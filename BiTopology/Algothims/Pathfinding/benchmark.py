"""
Benchmark comparing βCP (β-adic Cylinder Pruning) against standard A*.

This tests whether the novel algorithm provides actual speedups.
"""

import random
import time
from typing import Set, Tuple, List, Dict
from bcp_search import standard_astar, bcp_search, bcp_search_hard_prune


def generate_random_obstacles(width: int, height: int, density: float,
                              seed: int = None) -> Set[Tuple[int, int]]:
    """Generate random obstacles with given density."""
    if seed is not None:
        random.seed(seed)
    
    obstacles = set()
    for x in range(width):
        for y in range(height):
            if random.random() < density:
                obstacles.add((x, y))
    return obstacles


def generate_diagonal_obstacles(width: int, height: int, 
                                num_walls: int = 5) -> Set[Tuple[int, int]]:
    """Generate diagonal walls - should favor βCP's rotated geometry."""
    obstacles = set()
    
    for _ in range(num_walls):
        # Random diagonal line
        start_x = random.randint(0, width - 1)
        start_y = random.randint(0, height - 1)
        length = random.randint(5, min(width, height) // 2)
        direction = random.choice([(1, 1), (1, -1), (-1, 1), (-1, -1)])
        
        for i in range(length):
            x = start_x + i * direction[0]
            y = start_y + i * direction[1]
            if 0 <= x < width and 0 <= y < height:
                obstacles.add((x, y))
                # Make walls thicker
                for dx in [-1, 0, 1]:
                    for dy in [-1, 0, 1]:
                        nx, ny = x + dx, y + dy
                        if 0 <= nx < width and 0 <= ny < height:
                            obstacles.add((nx, ny))
    
    return obstacles


def generate_clustered_obstacles(width: int, height: int,
                                 num_clusters: int = 10,
                                 cluster_size: int = 5) -> Set[Tuple[int, int]]:
    """Generate clustered obstacles - tests cylinder blocking."""
    obstacles = set()
    
    for _ in range(num_clusters):
        cx = random.randint(cluster_size, width - cluster_size)
        cy = random.randint(cluster_size, height - cluster_size)
        
        for _ in range(cluster_size * cluster_size // 2):
            dx = random.randint(-cluster_size, cluster_size)
            dy = random.randint(-cluster_size, cluster_size)
            x, y = cx + dx, cy + dy
            if 0 <= x < width and 0 <= y < height:
                obstacles.add((x, y))
    
    return obstacles


def generate_maze(width: int, height: int) -> Set[Tuple[int, int]]:
    """Generate a simple maze using recursive division."""
    obstacles = set()
    
    def divide(x1, y1, x2, y2, horizontal: bool):
        if x2 - x1 < 4 or y2 - y1 < 4:
            return
        
        if horizontal:
            y = random.randint(y1 + 2, y2 - 2)
            gap = random.randint(x1, x2)
            for x in range(x1, x2 + 1):
                if x != gap:
                    obstacles.add((x, y))
            divide(x1, y1, x2, y - 1, not horizontal)
            divide(x1, y + 1, x2, y2, not horizontal)
        else:
            x = random.randint(x1 + 2, x2 - 2)
            gap = random.randint(y1, y2)
            for y in range(y1, y2 + 1):
                if y != gap:
                    obstacles.add((x, y))
            divide(x1, y1, x - 1, y2, not horizontal)
            divide(x + 1, y1, x2, y2, not horizontal)
    
    divide(0, 0, width - 1, height - 1, True)
    return obstacles


def run_benchmark(name: str, obstacles: Set[Tuple[int, int]], 
                  start: Tuple[int, int], goal: Tuple[int, int],
                  bounds: Tuple[int, int, int, int],
                  num_runs: int = 5) -> Dict:
    """Run benchmark comparing A* and βCP."""
    
    results = {
        'name': name,
        'obstacle_count': len(obstacles),
        'astar': {'times': [], 'expanded': [], 'path_len': None},
        'bcp': {'times': [], 'expanded': [], 'pruned': [], 'path_len': None},
        'bcp_hard': {'times': [], 'expanded': [], 'pruned': [], 'path_len': None},
    }
    
    for _ in range(num_runs):
        # A*
        t0 = time.perf_counter()
        path, expanded = standard_astar(start, goal, obstacles, bounds)
        t = time.perf_counter() - t0
        results['astar']['times'].append(t)
        results['astar']['expanded'].append(expanded)
        if path:
            results['astar']['path_len'] = len(path)
        
        # βCP (soft pruning)
        t0 = time.perf_counter()
        path, expanded, pruned = bcp_search(start, goal, obstacles, bounds)
        t = time.perf_counter() - t0
        results['bcp']['times'].append(t)
        results['bcp']['expanded'].append(expanded)
        results['bcp']['pruned'].append(pruned)
        if path:
            results['bcp']['path_len'] = len(path)
        
        # βCP (hard pruning)
        t0 = time.perf_counter()
        path, expanded, pruned = bcp_search_hard_prune(start, goal, obstacles, bounds)
        t = time.perf_counter() - t0
        results['bcp_hard']['times'].append(t)
        results['bcp_hard']['expanded'].append(expanded)
        results['bcp_hard']['pruned'].append(pruned)
        if path:
            results['bcp_hard']['path_len'] = len(path)
    
    return results


def print_results(results: Dict):
    """Pretty print benchmark results."""
    print(f"\n{'='*60}")
    print(f"Benchmark: {results['name']}")
    print(f"Obstacles: {results['obstacle_count']}")
    print(f"{'='*60}")
    
    def avg(lst):
        return sum(lst) / len(lst) if lst else 0
    
    astar = results['astar']
    bcp = results['bcp']
    bcp_hard = results['bcp_hard']
    
    print(f"\n{'Algorithm':<15} {'Time (ms)':<12} {'Expanded':<12} {'Pruned':<10} {'Path Len':<10}")
    print("-" * 60)
    
    print(f"{'A*':<15} {avg(astar['times'])*1000:>10.2f} {avg(astar['expanded']):>10.0f} "
          f"{'N/A':>10} {astar['path_len'] or 'N/A':>10}")
    
    print(f"{'βCP (soft)':<15} {avg(bcp['times'])*1000:>10.2f} {avg(bcp['expanded']):>10.0f} "
          f"{avg(bcp['pruned']):>10.0f} {bcp['path_len'] or 'N/A':>10}")
    
    print(f"{'βCP (hard)':<15} {avg(bcp_hard['times'])*1000:>10.2f} {avg(bcp_hard['expanded']):>10.0f} "
          f"{avg(bcp_hard['pruned']):>10.0f} {bcp_hard['path_len'] or 'N/A':>10}")
    
    # Speedup analysis
    if avg(astar['times']) > 0:
        speedup_soft = avg(astar['times']) / avg(bcp['times']) if avg(bcp['times']) > 0 else 0
        speedup_hard = avg(astar['times']) / avg(bcp_hard['times']) if avg(bcp_hard['times']) > 0 else 0
        
        print(f"\nSpeedup (soft): {speedup_soft:.2f}x")
        print(f"Speedup (hard): {speedup_hard:.2f}x")
        
        if avg(astar['expanded']) > 0:
            node_ratio_soft = avg(bcp['expanded']) / avg(astar['expanded'])
            node_ratio_hard = avg(bcp_hard['expanded']) / avg(astar['expanded'])
            print(f"Node ratio (soft): {node_ratio_soft:.2f} (1.0 = same as A*)")
            print(f"Node ratio (hard): {node_ratio_hard:.2f}")


def main():
    print("=" * 60)
    print("β-adic Cylinder Pruning (βCP) Benchmark")
    print("=" * 60)
    
    random.seed(42)
    
    # Test configurations
    sizes = [50, 100, 200]
    
    for size in sizes:
        bounds = (0, 0, size, size)
        start = (5, 5)
        goal = (size - 5, size - 5)
        
        # Test 1: Random obstacles
        print(f"\n\n{'#'*60}")
        print(f"Grid Size: {size}x{size}")
        print(f"{'#'*60}")
        
        for density in [0.1, 0.2, 0.3]:
            obstacles = generate_random_obstacles(size, size, density, seed=42)
            obstacles.discard(start)
            obstacles.discard(goal)
            
            results = run_benchmark(
                f"Random {density*100:.0f}% density",
                obstacles, start, goal, bounds
            )
            print_results(results)
        
        # Test 2: Diagonal obstacles (should favor βCP)
        obstacles = generate_diagonal_obstacles(size, size, num_walls=size//10)
        obstacles.discard(start)
        obstacles.discard(goal)
        
        results = run_benchmark(
            "Diagonal walls",
            obstacles, start, goal, bounds
        )
        print_results(results)
        
        # Test 3: Clustered obstacles
        obstacles = generate_clustered_obstacles(size, size, 
                                                  num_clusters=size//5,
                                                  cluster_size=size//10)
        obstacles.discard(start)
        obstacles.discard(goal)
        
        results = run_benchmark(
            "Clustered obstacles",
            obstacles, start, goal, bounds
        )
        print_results(results)
        
        # Test 4: Maze
        obstacles = generate_maze(size, size)
        obstacles.discard(start)
        obstacles.discard(goal)
        
        results = run_benchmark(
            "Maze",
            obstacles, start, goal, bounds
        )
        print_results(results)
    
    print("\n" + "=" * 60)
    print("Benchmark complete!")
    print("=" * 60)


if __name__ == "__main__":
    main()
