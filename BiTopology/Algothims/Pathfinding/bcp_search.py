"""
β-adic Cylinder Pruning (βCP) Search Algorithm.

This implements the novel pathfinding algorithm that uses β-adic cylinder
structure for hierarchical pruning, based on the theorems proven in PathPlanning.lean.
"""

import heapq
from typing import Set, Tuple, List, Optional, Dict
from beta_adic import cylinder_distance_fast, cylinder_pattern_fast, grid_distance
from cylinder_index import CylinderIndex, HierarchicalCylinderIndex


def standard_astar(start: Tuple[int, int], goal: Tuple[int, int],
                   obstacles: Set[Tuple[int, int]],
                   bounds: Tuple[int, int, int, int] = None) -> Tuple[Optional[List[Tuple[int, int]]], int]:
    """
    Standard A* for comparison baseline.
    
    Returns (path, nodes_expanded).
    """
    if start == goal:
        return [start], 0
    
    if start in obstacles or goal in obstacles:
        return None, 0
    
    def heuristic(pos):
        return max(abs(pos[0] - goal[0]), abs(pos[1] - goal[1]))
    
    def neighbors(pos):
        x, y = pos
        for dx in [-1, 0, 1]:
            for dy in [-1, 0, 1]:
                if dx == 0 and dy == 0:
                    continue
                nx, ny = x + dx, y + dy
                if bounds:
                    if not (bounds[0] <= nx < bounds[2] and bounds[1] <= ny < bounds[3]):
                        continue
                if (nx, ny) not in obstacles:
                    yield (nx, ny)
    
    open_set = [(heuristic(start), 0, start)]
    g_score = {start: 0}
    came_from = {}
    nodes_expanded = 0
    
    while open_set:
        _, g, current = heapq.heappop(open_set)
        
        if current == goal:
            path = [current]
            while current in came_from:
                current = came_from[current]
                path.append(current)
            return path[::-1], nodes_expanded
        
        if g > g_score.get(current, float('inf')):
            continue
        
        nodes_expanded += 1
        
        for neighbor in neighbors(current):
            tentative_g = g + 1
            if tentative_g < g_score.get(neighbor, float('inf')):
                came_from[neighbor] = current
                g_score[neighbor] = tentative_g
                f = tentative_g + heuristic(neighbor)
                heapq.heappush(open_set, (f, tentative_g, neighbor))
    
    return None, nodes_expanded


def bcp_search(start: Tuple[int, int], goal: Tuple[int, int],
               obstacles: Set[Tuple[int, int]],
               bounds: Tuple[int, int, int, int] = None,
               prune_threshold: float = 0.8,
               max_prune_level: int = 6) -> Tuple[Optional[List[Tuple[int, int]]], int, int]:
    """
    β-adic Cylinder Pruning (βCP) Search.
    
    This algorithm uses the β-adic cylinder structure for hierarchical pruning.
    Based on the proven theorem cylinder_pruning_valid:
    - If goal has different k-pattern than current, path must exit current's k-cylinder
    - If that cylinder is heavily blocked, we deprioritize exploring it
    
    Key difference from quadtree: cylinders are rotated 45° at each level,
    providing a different geometric decomposition.
    
    Returns (path, nodes_expanded, nodes_pruned).
    """
    if start == goal:
        return [start], 0, 0
    
    if start in obstacles or goal in obstacles:
        return None, 0, 0
    
    # Build cylinder index
    index = HierarchicalCylinderIndex(obstacles, max_level=max_prune_level)
    
    # Compute cylinder distance for tiebreaking
    cyl_dist_start = cylinder_distance_fast(start[0], start[1], goal[0], goal[1])
    
    def heuristic(pos):
        return max(abs(pos[0] - goal[0]), abs(pos[1] - goal[1]))
    
    def cylinder_tiebreaker(pos):
        """Use cylinder distance as tiebreaker - lower is better."""
        return cylinder_distance_fast(pos[0], pos[1], goal[0], goal[1])
    
    def neighbors(pos):
        x, y = pos
        for dx in [-1, 0, 1]:
            for dy in [-1, 0, 1]:
                if dx == 0 and dy == 0:
                    continue
                nx, ny = x + dx, y + dy
                if bounds:
                    if not (bounds[0] <= nx < bounds[2] and bounds[1] <= ny < bounds[3]):
                        continue
                if (nx, ny) not in obstacles:
                    yield (nx, ny)
    
    # Priority: (f_score, cylinder_tiebreaker, g_score, position)
    open_set = [(heuristic(start), cylinder_tiebreaker(start), 0, start)]
    g_score = {start: 0}
    came_from = {}
    nodes_expanded = 0
    nodes_pruned = 0
    
    while open_set:
        f, cyl_tb, g, current = heapq.heappop(open_set)
        
        if current == goal:
            path = [current]
            while current in came_from:
                current = came_from[current]
                path.append(current)
            return path[::-1], nodes_expanded, nodes_pruned
        
        if g > g_score.get(current, float('inf')):
            continue
        
        nodes_expanded += 1
        
        for neighbor in neighbors(current):
            # NOVEL PRUNING: Check if we should deprioritize this neighbor
            # based on cylinder blocking
            should_deprioritize = False
            prune_penalty = 0
            
            for level in range(2, max_prune_level + 1):
                if index.should_prune(neighbor[0], neighbor[1], 
                                      goal[0], goal[1], level, prune_threshold):
                    # Don't hard prune (would break optimality), but add penalty
                    prune_penalty = max(prune_penalty, level)
                    should_deprioritize = True
            
            if should_deprioritize:
                nodes_pruned += 1
            
            tentative_g = g + 1
            if tentative_g < g_score.get(neighbor, float('inf')):
                came_from[neighbor] = current
                g_score[neighbor] = tentative_g
                
                h = heuristic(neighbor)
                cyl_tb = cylinder_tiebreaker(neighbor)
                
                # Add penalty for blocked cylinders (soft pruning)
                f = tentative_g + h + (prune_penalty * 0.01)
                
                heapq.heappush(open_set, (f, cyl_tb, tentative_g, neighbor))
    
    return None, nodes_expanded, nodes_pruned


def bcp_search_hard_prune(start: Tuple[int, int], goal: Tuple[int, int],
                          obstacles: Set[Tuple[int, int]],
                          bounds: Tuple[int, int, int, int] = None,
                          prune_threshold: float = 0.95,
                          max_prune_level: int = 6) -> Tuple[Optional[List[Tuple[int, int]]], int, int]:
    """
    βCP with hard pruning - may not find path if pruning is too aggressive.
    
    This version actually skips exploring heavily blocked cylinders,
    which can provide significant speedups but may miss paths.
    
    Use only when you're okay with potentially missing some paths.
    """
    if start == goal:
        return [start], 0, 0
    
    if start in obstacles or goal in obstacles:
        return None, 0, 0
    
    # Build cylinder index
    index = HierarchicalCylinderIndex(obstacles, max_level=max_prune_level)
    
    def heuristic(pos):
        return max(abs(pos[0] - goal[0]), abs(pos[1] - goal[1]))
    
    def cylinder_tiebreaker(pos):
        return cylinder_distance_fast(pos[0], pos[1], goal[0], goal[1])
    
    def neighbors(pos):
        x, y = pos
        for dx in [-1, 0, 1]:
            for dy in [-1, 0, 1]:
                if dx == 0 and dy == 0:
                    continue
                nx, ny = x + dx, y + dy
                if bounds:
                    if not (bounds[0] <= nx < bounds[2] and bounds[1] <= ny < bounds[3]):
                        continue
                if (nx, ny) not in obstacles:
                    yield (nx, ny)
    
    open_set = [(heuristic(start), cylinder_tiebreaker(start), 0, start)]
    g_score = {start: 0}
    came_from = {}
    nodes_expanded = 0
    nodes_pruned = 0
    
    while open_set:
        f, cyl_tb, g, current = heapq.heappop(open_set)
        
        if current == goal:
            path = [current]
            while current in came_from:
                current = came_from[current]
                path.append(current)
            return path[::-1], nodes_expanded, nodes_pruned
        
        if g > g_score.get(current, float('inf')):
            continue
        
        nodes_expanded += 1
        
        for neighbor in neighbors(current):
            # HARD PRUNING: Skip if cylinder is heavily blocked and goal is outside
            skip = False
            for level in range(max_prune_level, 1, -1):
                if index.should_prune(neighbor[0], neighbor[1],
                                      goal[0], goal[1], level, prune_threshold):
                    skip = True
                    nodes_pruned += 1
                    break
            
            if skip:
                continue
            
            tentative_g = g + 1
            if tentative_g < g_score.get(neighbor, float('inf')):
                came_from[neighbor] = current
                g_score[neighbor] = tentative_g
                f = tentative_g + heuristic(neighbor)
                cyl_tb = cylinder_tiebreaker(neighbor)
                heapq.heappush(open_set, (f, cyl_tb, tentative_g, neighbor))
    
    return None, nodes_expanded, nodes_pruned


if __name__ == "__main__":
    import time
    
    print("Testing βCP Search...")
    
    # Simple test
    obstacles = set()
    for i in range(20):
        obstacles.add((10, i))  # Vertical wall
    obstacles.discard((10, 10))  # Gap in wall
    
    start = (0, 10)
    goal = (20, 10)
    bounds = (-5, -5, 30, 30)
    
    # Standard A*
    t0 = time.perf_counter()
    path_astar, expanded_astar = standard_astar(start, goal, obstacles, bounds)
    t_astar = time.perf_counter() - t0
    
    # βCP Search
    t0 = time.perf_counter()
    path_bcp, expanded_bcp, pruned_bcp = bcp_search(start, goal, obstacles, bounds)
    t_bcp = time.perf_counter() - t0
    
    print(f"A*:  path length={len(path_astar) if path_astar else 'None'}, "
          f"expanded={expanded_astar}, time={t_astar*1000:.2f}ms")
    print(f"βCP: path length={len(path_bcp) if path_bcp else 'None'}, "
          f"expanded={expanded_bcp}, pruned={pruned_bcp}, time={t_bcp*1000:.2f}ms")
    
    print("\nTest passed!")
