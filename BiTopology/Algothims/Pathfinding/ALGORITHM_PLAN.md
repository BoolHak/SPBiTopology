# β-adic Cylinder Pathfinding (βCP) - Algorithm Plan

## The Core Question: What Can Actually Provide Speedups?

Based on the proven theorems in `PathPlanning.lean`, we need to identify what operations 
the β-adic structure enables that are NOT possible with existing approaches.

## What Existing Approaches Do

| Approach | Hierarchy Structure | Pruning Mechanism |
|----------|---------------------|-------------------|
| **HPA*** | Arbitrary rectangular clusters | Precomputed inter-cluster paths |
| **Quadtree** | Power-of-2 axis-aligned squares | Skip fully blocked quadrants |
| **Morton/Z-order** | Bit-interleaved spatial index | Locality-preserving search order |

## What β-adic Cylinders Provide (Proven Theorems)

### Theorem 1: `neighbors_different_k_pattern` (k ≥ 2)
```
For k ≥ 2, distinct grid neighbors CANNOT share the same k-cylinder pattern.
```
**Implication**: The cylinder hierarchy is FINER than the grid at depth ≥ 2.

### Theorem 2: `path_crosses_k_cylinder_for_k_ge_2`
```
For k ≥ 2 and z ≠ w, any path from z to w must cross k-cylinder boundaries.
```
**Implication**: Cylinder distance provides a LOWER BOUND on path crossings.

### Theorem 3: `cylinder_pruning_valid`
```
If goal has different k-pattern than z, any path to goal MUST exit z's k-cylinder.
```
**Implication**: If z's entire k-cylinder is blocked and goal is outside, PRUNE.

### Theorem 4: `βQuot_preserves_neighbor_structure`
```
Grid neighbors in original space have quotients within gridDistance ≤ 2.
```
**Implication**: Solving at quotient level preserves connectivity (with bounded error).

## The Novel Algorithm: β-adic Cylinder Pruning (βCP)

### Key Insight
The β-adic cylinders have a DIFFERENT geometry than quadtrees:
- Each level is rotated 45° (due to β = -1+i having argument 3π/4)
- Cylinder boundaries do NOT align with coordinate axes
- This creates a "spiral" decomposition that may cut obstacles differently

### Where Speedups Can Come From

1. **Obstacle-Cylinder Intersection**: A cylinder may be fully blocked even when 
   no axis-aligned quadrant is. The rotated geometry can detect blockages earlier.

2. **Lower Bound Tightening**: cylinderDistance provides additional lower bound 
   information that can improve A* priority ordering.

3. **Hierarchical Pruning**: For large blocked regions, entire cylinder subtrees 
   can be pruned without exploring individual cells.

### The Algorithm

```
function βCP_Search(start, goal, obstacles):
    # Step 1: Compute cylinder distance (first differing digit level)
    k = cylinderDistance(start, goal)
    
    # Step 2: Build cylinder-obstacle index
    # For each level 1..k, compute which cylinder patterns are blocked
    blocked_cylinders = precompute_blocked_cylinders(obstacles, k)
    
    # Step 3: A* with cylinder-aware pruning
    open_set = PriorityQueue()
    open_set.add(start, priority = h(start, goal))
    
    while open_set not empty:
        current = open_set.pop()
        
        if current == goal:
            return reconstruct_path()
        
        for neighbor in grid_neighbors(current):
            # NOVEL PRUNING: Check if neighbor's cylinder is fully blocked
            # and goal is outside that cylinder
            for level in range(2, k+1):
                neighbor_pattern = cylinderPattern(neighbor, level)
                goal_pattern = cylinderPattern(goal, level)
                
                if neighbor_pattern != goal_pattern:
                    # Goal is outside neighbor's level-cylinder
                    if is_fully_blocked(neighbor_pattern, level, blocked_cylinders):
                        # PRUNE: No path through this cylinder can reach goal
                        skip neighbor
                        break
            
            # Standard A* update with cylinder-distance tiebreaker
            g_new = g[current] + 1
            if g_new < g[neighbor]:
                g[neighbor] = g_new
                # Use cylinder distance as tiebreaker (novel heuristic component)
                f = g_new + h(neighbor, goal) + ε * cylinderDistance(neighbor, goal)
                open_set.add(neighbor, f)
    
    return NO_PATH
```

### What Makes This Different From Existing Approaches

| Aspect | Quadtree | HPA* | βCP (Ours) |
|--------|----------|------|------------|
| Geometry | Axis-aligned | Arbitrary rectangles | 45°-rotated hierarchy |
| Hierarchy basis | Powers of 2 | Manual clustering | Number-theoretic (β^k) |
| Pruning condition | Quadrant blocked | Cluster blocked | Cylinder blocked |
| Theoretical foundation | Geometric | Heuristic | Formally proven in Lean |

### Expected Speedup Scenarios

1. **Diagonal obstacles**: Cylinders may fully contain diagonal walls that 
   quadrants would split across multiple regions.

2. **Spiral/rotated mazes**: The 45° rotation may align better with certain 
   obstacle patterns.

3. **Dense obstacle regions**: Hierarchical cylinder pruning can skip large 
   blocked regions.

### Potential Weaknesses

1. **Overhead**: Computing β-adic codes and cylinder membership has cost.
2. **Axis-aligned obstacles**: Quadtrees may be better for Manhattan-style mazes.
3. **Sparse obstacles**: Pruning gains are minimal when few cylinders are fully blocked.

## Implementation Plan

1. **`beta_adic.py`**: Core β-adic operations (digit, βQuot, cylinderPattern)
2. **`cylinder_index.py`**: Precompute blocked cylinders from obstacle set
3. **`bcp_search.py`**: The βCP algorithm with cylinder pruning
4. **`benchmark.py`**: Compare against standard A* on various maze types

## Metrics to Measure

- Nodes expanded (primary measure of search efficiency)
- Wall-clock time
- Pruning effectiveness (how many nodes skipped via cylinder pruning)
- Path quality (should be optimal since we only prune provably unreachable nodes)

## Hypothesis

βCP will show speedups on:
- Mazes with diagonal/rotated obstacle patterns
- Large open areas with scattered obstacles
- Scenarios where cylinder-level blocking occurs

βCP may be slower on:
- Axis-aligned grid mazes (quadtrees better aligned)
- Very sparse obstacles (pruning overhead > benefit)

---

# BENCHMARK RESULTS (Actual)

## Summary: βCP is SLOWER than A*

| Metric | A* | βCP (soft) | βCP (hard) |
|--------|-----|------------|------------|
| Speedup | 1.0x | **0.03-0.04x** | 0.2-0.9x |
| Nodes explored | baseline | 0.87-0.99x | fails to find path |

## Root Cause Analysis

### Why βCP is Slower

1. **Index Building Overhead**: Building the cylinder index for all levels is O(obstacles × levels)
2. **Per-Neighbor Overhead**: Computing cylinder patterns for every neighbor at every level
3. **Minimal Pruning Benefit**: Cylinders rarely become "fully blocked" enough to prune
4. **The Fundamental Issue**: By `neighbors_different_k_pattern`, for k ≥ 2, neighbors are 
   ALWAYS in different cylinders. This means cylinder-based pruning can only work at k=1!

### The Mathematical Limitation

The proven theorem `neighbors_different_k_pattern` shows:
```
For k ≥ 2, distinct grid neighbors CANNOT share k-cylinder patterns.
```

This means:
- At depth k ≥ 2, EVERY move crosses a cylinder boundary
- Cylinder "blocking" at k ≥ 2 doesn't help because ALL paths cross boundaries
- Only k=1 cylinders (which are very coarse) can contain paths

## What Could Provide Actual Speedups

### Option A: Precomputation (like HPA*)
- Precompute paths BETWEEN cylinders (not within)
- Trade memory for query speed
- This is what HPA* does with clusters

### Option B: Different Use Case
- **Path COMPRESSION**: Represent optimal paths compactly using cylinder structure
- **Lower Bound COMPUTATION**: Use cylinderDistance for admissible heuristic bounds
- **Obstacle INDEXING**: Use β-adic codes as spatial hash (like Morton codes)

### Option C: Quotient-Space Search
- Solve at quotient level (coarser grid), then refine
- But: `βQuot_preserves_neighbor_structure` only guarantees distance ≤ 2, 
  so quotient solutions may need significant refinement

## Conclusion

The β-adic cylinder structure provides **theoretical value** (proven lower bounds, 
path compression) but does NOT provide **search speedups** in the naive implementation.

The key insight from the theorems:
- Cylinder structure is about PATH PROPERTIES, not search guidance
- Neighbors are too fine-grained relative to cylinders for k ≥ 2
- The theoretical contribution is the FORMAL VERIFICATION, not algorithm speedup

## Honest Assessment

**Is the algorithm novel?** Yes - the formal verification in Lean is novel.

**Does it provide speedups?** No - the overhead exceeds the pruning benefit.

**What is the actual contribution?** 
1. Formally verified theorems about path-cylinder relationships
2. A new way to UNDERSTAND grid paths through number theory
3. Potential for path compression (not search speedup)
