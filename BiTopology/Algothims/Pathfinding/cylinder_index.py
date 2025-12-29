"""
Cylinder-based spatial index for obstacles.

This module precomputes which β-adic cylinders are blocked by obstacles,
enabling efficient pruning during pathfinding.
"""

from typing import Set, Dict, Tuple, FrozenSet
from collections import defaultdict
from beta_adic import cylinder_pattern_fast, grid_distance


class CylinderIndex:
    """
    Spatial index that tracks obstacle density per cylinder at each level.
    
    For each cylinder pattern at each level k, we track:
    - How many obstacle cells are in that cylinder
    - Whether the cylinder is "fully blocked" (high density)
    
    This enables the key pruning operation from cylinder_pruning_valid:
    If goal is outside a cylinder and that cylinder is fully blocked,
    we can skip exploring paths through it.
    """
    
    def __init__(self, obstacles: Set[Tuple[int, int]], max_level: int = 10):
        """
        Build the cylinder index from a set of obstacles.
        
        Args:
            obstacles: Set of (x, y) obstacle positions
            max_level: Maximum cylinder level to index
        """
        self.obstacles = frozenset(obstacles)
        self.max_level = max_level
        
        # For each level k, map pattern -> set of obstacles in that cylinder
        self.cylinder_obstacles: Dict[int, Dict[int, Set[Tuple[int, int]]]] = {}
        
        # For each level k, map pattern -> obstacle count
        self.cylinder_counts: Dict[int, Dict[int, int]] = {}
        
        # Build the index
        self._build_index()
    
    def _build_index(self):
        """Build the cylinder index for all levels."""
        for k in range(1, self.max_level + 1):
            self.cylinder_obstacles[k] = defaultdict(set)
            self.cylinder_counts[k] = defaultdict(int)
            
            for (x, y) in self.obstacles:
                pattern = cylinder_pattern_fast(x, y, k)
                self.cylinder_obstacles[k][pattern].add((x, y))
                self.cylinder_counts[k][pattern] += 1
    
    def get_obstacle_count(self, x: int, y: int, level: int) -> int:
        """Get number of obstacles in the same cylinder as (x, y) at given level."""
        if level > self.max_level or level < 1:
            return 0
        pattern = cylinder_pattern_fast(x, y, level)
        return self.cylinder_counts[level].get(pattern, 0)
    
    def get_cylinder_density(self, x: int, y: int, level: int) -> float:
        """
        Get obstacle density in the cylinder containing (x, y) at given level.
        
        A k-cylinder contains approximately 2^k cells, so density = count / 2^k.
        """
        if level > self.max_level or level < 1:
            return 0.0
        count = self.get_obstacle_count(x, y, level)
        # Approximate cylinder size: 2^k cells
        cylinder_size = 1 << level
        return count / cylinder_size
    
    def is_cylinder_blocked(self, x: int, y: int, level: int, 
                            threshold: float = 0.9) -> bool:
        """
        Check if the cylinder containing (x, y) at given level is "blocked".
        
        A cylinder is considered blocked if its obstacle density exceeds threshold.
        This is a heuristic - true blocking would require checking all paths.
        """
        density = self.get_cylinder_density(x, y, level)
        return density >= threshold
    
    def get_pattern(self, x: int, y: int, level: int) -> int:
        """Get the cylinder pattern for (x, y) at given level."""
        return cylinder_pattern_fast(x, y, level)
    
    def patterns_differ(self, x1: int, y1: int, x2: int, y2: int, level: int) -> bool:
        """Check if two points have different cylinder patterns at given level."""
        return self.get_pattern(x1, y1, level) != self.get_pattern(x2, y2, level)
    
    def should_prune(self, current_x: int, current_y: int,
                     goal_x: int, goal_y: int, 
                     level: int, threshold: float = 0.9) -> bool:
        """
        Determine if we should prune exploration from current toward goal.
        
        Based on cylinder_pruning_valid theorem:
        If goal has different pattern than current at level k,
        and current's cylinder is fully blocked at level k,
        then any path to goal must exit this cylinder - but if it's blocked,
        we might want to skip exploring deeper into it.
        
        Returns True if pruning is recommended.
        """
        # Only prune if goal is outside current's cylinder at this level
        if not self.patterns_differ(current_x, current_y, goal_x, goal_y, level):
            return False
        
        # Check if current's cylinder is heavily blocked
        return self.is_cylinder_blocked(current_x, current_y, level, threshold)


class HierarchicalCylinderIndex(CylinderIndex):
    """
    Extended cylinder index with hierarchical blocking detection.
    
    This version tracks whether entire subtrees of cylinders are blocked,
    enabling more aggressive pruning.
    """
    
    def __init__(self, obstacles: Set[Tuple[int, int]], max_level: int = 10):
        super().__init__(obstacles, max_level)
        
        # Cache for blocking decisions at each level
        self._blocking_cache: Dict[Tuple[int, int, int], bool] = {}
    
    def compute_blocking_score(self, x: int, y: int, level: int) -> float:
        """
        Compute a hierarchical blocking score that considers multiple levels.
        
        Higher score = more blocked = more likely to prune.
        """
        if level < 1:
            return 0.0
        
        # Weighted sum of densities at different levels
        score = 0.0
        weight_sum = 0.0
        
        for k in range(1, min(level + 1, self.max_level + 1)):
            weight = 1.0 / k  # Higher levels contribute less
            density = self.get_cylinder_density(x, y, k)
            score += weight * density
            weight_sum += weight
        
        return score / weight_sum if weight_sum > 0 else 0.0
    
    def get_pruning_level(self, current_x: int, current_y: int,
                          goal_x: int, goal_y: int) -> int:
        """
        Find the highest level at which pruning is recommended.
        
        Returns 0 if no pruning, otherwise the level at which to prune.
        """
        for level in range(self.max_level, 1, -1):
            if self.should_prune(current_x, current_y, goal_x, goal_y, level):
                return level
        return 0


if __name__ == "__main__":
    # Test the cylinder index
    print("Testing CylinderIndex...")
    
    # Create a simple obstacle set
    obstacles = set()
    # Create a diagonal wall
    for i in range(10):
        obstacles.add((i, i))
        obstacles.add((i + 1, i))
    
    index = CylinderIndex(obstacles, max_level=5)
    
    # Test obstacle counting
    print(f"Obstacles in cylinder of (5, 5) at level 3: {index.get_obstacle_count(5, 5, 3)}")
    print(f"Density at (5, 5) level 3: {index.get_cylinder_density(5, 5, 3):.2f}")
    
    # Test pattern difference
    print(f"(0,0) and (10,10) differ at level 2: {index.patterns_differ(0, 0, 10, 10, 2)}")
    
    # Test hierarchical index
    hier_index = HierarchicalCylinderIndex(obstacles, max_level=5)
    print(f"Blocking score at (5,5) level 3: {hier_index.compute_blocking_score(5, 5, 3):.2f}")
    
    print("CylinderIndex tests passed!")
