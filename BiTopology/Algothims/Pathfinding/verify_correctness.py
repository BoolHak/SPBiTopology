"""
Verification script to ensure Python implementation matches Lean definitions.

Tests the β-adic operations against known correct values and properties
proven in PathPlanning.lean.
"""

from beta_adic import (
    digit, beta_quot, nth_digit, cylinder_pattern, 
    cylinder_distance, cylinder_pattern_fast, cylinder_distance_fast,
    grid_distance, grid_neighbors
)
from bcp_search import standard_astar, bcp_search


def test_digit():
    """
    Verify digit function matches Lean definition:
    digit z = (z.re % 2 ≠ z.im % 2)
    """
    print("Testing digit()...")
    
    test_cases = [
        # (z, expected_digit)
        (complex(0, 0), False),   # 0 % 2 == 0 % 2
        (complex(1, 0), True),    # 1 % 2 != 0 % 2
        (complex(0, 1), True),    # 0 % 2 != 1 % 2
        (complex(1, 1), False),   # 1 % 2 == 1 % 2
        (complex(2, 0), False),   # 2 % 2 == 0 % 2
        (complex(2, 1), True),    # 2 % 2 != 1 % 2
        (complex(3, 2), True),    # 3 % 2 != 2 % 2
        (complex(4, 4), False),   # 4 % 2 == 4 % 2
        (complex(-1, 0), True),   # -1 % 2 != 0 % 2
        (complex(-2, -2), False), # -2 % 2 == -2 % 2
    ]
    
    for z, expected in test_cases:
        result = digit(z)
        assert result == expected, f"digit({z}) = {result}, expected {expected}"
    
    print("  ✓ All digit tests passed")


def test_beta_quot():
    """
    Verify βQuot matches Lean definition and satisfies:
    z = digit(z) + β * βQuot(z)
    
    where β = -1 + i
    """
    print("Testing beta_quot()...")
    
    beta = complex(-1, 1)
    
    # Test the fundamental recurrence for many values
    test_values = [
        complex(0, 0),
        complex(1, 0),
        complex(0, 1),
        complex(1, 1),
        complex(2, 3),
        complex(-5, 7),
        complex(10, -10),
        complex(100, 50),
        complex(-37, -42),
    ]
    
    for z in test_values:
        q = beta_quot(z)
        d = 1 if digit(z) else 0
        reconstructed = d + beta * q
        
        # Check reconstruction (should match exactly for integers)
        assert int(reconstructed.real) == int(z.real), \
            f"βQuot failed for {z}: reconstructed.re = {reconstructed.real}, expected {z.real}"
        assert int(reconstructed.imag) == int(z.imag), \
            f"βQuot failed for {z}: reconstructed.im = {reconstructed.imag}, expected {z.imag}"
    
    print("  ✓ All beta_quot tests passed (fundamental recurrence verified)")


def test_cylinder_pattern():
    """
    Verify cylinder_pattern returns correct k-digit patterns.
    """
    print("Testing cylinder_pattern()...")
    
    # Test that pattern length matches k
    z = complex(5, 3)
    for k in range(6):
        pattern = cylinder_pattern(z, k)
        assert len(pattern) == k, f"Pattern length mismatch: {len(pattern)} != {k}"
    
    # Test that same point has same pattern
    z1 = complex(10, 20)
    z2 = complex(10, 20)
    for k in range(1, 5):
        assert cylinder_pattern(z1, k) == cylinder_pattern(z2, k), \
            f"Same point should have same pattern at k={k}"
    
    # Test pattern consistency: pattern[i] should equal nth_digit(z, i)
    z = complex(17, -8)
    for k in range(1, 8):
        pattern = cylinder_pattern(z, k)
        for i in range(k):
            assert pattern[i] == nth_digit(z, i), \
                f"Pattern[{i}] != nth_digit at k={k}"
    
    print("  ✓ All cylinder_pattern tests passed")


def test_cylinder_distance():
    """
    Verify cylinder_distance returns first differing digit position.
    """
    print("Testing cylinder_distance()...")
    
    # Same point should have distance 0
    z = complex(5, 5)
    assert cylinder_distance(z, z) == 0, "Same point should have distance 0"
    
    # Different points should have positive distance
    test_pairs = [
        (complex(0, 0), complex(1, 0)),
        (complex(0, 0), complex(0, 1)),
        (complex(0, 0), complex(10, 10)),
        (complex(5, 5), complex(100, 100)),
    ]
    
    for z, w in test_pairs:
        dist = cylinder_distance(z, w)
        assert dist > 0, f"Different points should have dist > 0: {z}, {w}"
        
        # Verify: patterns match up to dist-1, differ at dist-1
        for i in range(dist - 1):
            assert nth_digit(z, i) == nth_digit(w, i), \
                f"Digits should match before cylinder_distance: i={i}"
        assert nth_digit(z, dist - 1) != nth_digit(w, dist - 1), \
            f"Digits should differ at cylinder_distance-1"
    
    print("  ✓ All cylinder_distance tests passed")


def test_fast_versions():
    """
    Verify fast (integer) versions match standard versions.
    """
    print("Testing fast versions...")
    
    test_points = [
        (0, 0), (1, 0), (0, 1), (1, 1),
        (5, 3), (10, -7), (-15, 20), (100, 100),
    ]
    
    for x, y in test_points:
        z = complex(x, y)
        for k in range(1, 6):
            # Convert standard pattern to int for comparison
            std_pattern = cylinder_pattern(z, k)
            std_int = sum(d << i for i, d in enumerate(std_pattern))
            fast_int = cylinder_pattern_fast(x, y, k)
            
            assert std_int == fast_int, \
                f"Pattern mismatch at ({x}, {y}), k={k}: std={std_int}, fast={fast_int}"
    
    # Test cylinder_distance_fast
    test_pairs = [
        ((0, 0), (1, 0)),
        ((5, 5), (10, 10)),
        ((0, 0), (100, 100)),
    ]
    
    for (x1, y1), (x2, y2) in test_pairs:
        std = cylinder_distance(complex(x1, y1), complex(x2, y2))
        fast = cylinder_distance_fast(x1, y1, x2, y2)
        assert std == fast, f"Distance mismatch: std={std}, fast={fast}"
    
    print("  ✓ All fast version tests passed")


def test_grid_operations():
    """
    Verify grid distance and neighbors are correct.
    """
    print("Testing grid operations...")
    
    # Grid distance = Chebyshev distance
    test_cases = [
        (complex(0, 0), complex(0, 0), 0),
        (complex(0, 0), complex(1, 0), 1),
        (complex(0, 0), complex(1, 1), 1),
        (complex(0, 0), complex(5, 3), 5),
        (complex(0, 0), complex(3, 5), 5),
        (complex(-5, -5), complex(5, 5), 10),
    ]
    
    for z, w, expected in test_cases:
        result = grid_distance(z, w)
        assert result == expected, f"grid_distance({z}, {w}) = {result}, expected {expected}"
    
    # Grid neighbors should be 8 distinct points at distance 1
    z = complex(5, 5)
    neighbors = grid_neighbors(z)
    assert len(neighbors) == 8, f"Should have 8 neighbors, got {len(neighbors)}"
    
    for n in neighbors:
        assert grid_distance(z, n) == 1, f"Neighbor {n} should be at distance 1 from {z}"
    
    print("  ✓ All grid operation tests passed")


def test_astar_correctness():
    """
    Verify A* finds optimal paths.
    """
    print("Testing A* correctness...")
    
    # Simple test without obstacles
    start = (0, 0)
    goal = (10, 10)
    obstacles = set()
    bounds = (-5, -5, 20, 20)
    
    path, expanded = standard_astar(start, goal, obstacles, bounds)
    
    assert path is not None, "A* should find a path"
    assert path[0] == start, "Path should start at start"
    assert path[-1] == goal, "Path should end at goal"
    
    # Path length should be optimal (Chebyshev distance + 1)
    expected_length = max(abs(goal[0] - start[0]), abs(goal[1] - start[1])) + 1
    assert len(path) == expected_length, \
        f"Path length {len(path)} != expected {expected_length}"
    
    # Test with obstacle
    obstacles = {(5, 5)}
    path2, _ = standard_astar(start, goal, obstacles, bounds)
    assert path2 is not None, "Should find path around obstacle"
    
    print("  ✓ All A* correctness tests passed")


def test_bcp_correctness():
    """
    Verify βCP finds correct paths (same as A*).
    """
    print("Testing βCP correctness...")
    
    test_cases = [
        # (start, goal, obstacles)
        ((0, 0), (10, 10), set()),
        ((0, 0), (10, 10), {(5, 5)}),
        ((5, 5), (15, 15), {(10, 10), (10, 11), (11, 10)}),
    ]
    
    bounds = (-5, -5, 25, 25)
    
    for start, goal, obstacles in test_cases:
        path_astar, _ = standard_astar(start, goal, obstacles, bounds)
        path_bcp, _, _ = bcp_search(start, goal, obstacles, bounds)
        
        # Both should find paths
        if path_astar is not None:
            assert path_bcp is not None, f"βCP should find path when A* does"
            
            # Paths should have same length (both optimal)
            assert len(path_bcp) == len(path_astar), \
                f"βCP path length {len(path_bcp)} != A* length {len(path_astar)}"
            
            # Verify path validity
            assert path_bcp[0] == start, "βCP path should start at start"
            assert path_bcp[-1] == goal, "βCP path should end at goal"
            
            # Verify consecutive points are neighbors
            for i in range(len(path_bcp) - 1):
                p1, p2 = path_bcp[i], path_bcp[i + 1]
                dist = max(abs(p1[0] - p2[0]), abs(p1[1] - p2[1]))
                assert dist == 1, f"Consecutive points should be neighbors"
    
    print("  ✓ All βCP correctness tests passed")


def test_theorem_neighbors_different_k_pattern():
    """
    Verify the proven theorem: for k ≥ 2, distinct neighbors have different k-patterns.
    
    This is Theorem `neighbors_different_k_pattern` in PathPlanning.lean.
    """
    print("Testing theorem: neighbors_different_k_pattern...")
    
    # Test many points and their neighbors
    test_points = [
        (0, 0), (1, 1), (5, 3), (-10, 7), (100, 50),
    ]
    
    for x, y in test_points:
        z = complex(x, y)
        neighbors = grid_neighbors(z)
        
        for n in neighbors:
            # For k >= 2, neighbors should have DIFFERENT k-patterns
            for k in range(2, 6):
                pattern_z = cylinder_pattern(z, k)
                pattern_n = cylinder_pattern(n, k)
                
                assert pattern_z != pattern_n, \
                    f"Theorem violation: {z} and {n} share {k}-pattern {pattern_z}"
    
    print("  ✓ Theorem neighbors_different_k_pattern verified")


def test_theorem_quotient_preserves_neighbor():
    """
    Verify the proven theorem: βQuot of neighbors have gridDistance ≤ 2.
    
    This is Theorem `βQuot_preserves_neighbor_structure` in PathPlanning.lean.
    """
    print("Testing theorem: βQuot_preserves_neighbor_structure...")
    
    test_points = [
        (0, 0), (1, 1), (5, 3), (-10, 7), (100, 50), (-37, -42),
    ]
    
    for x, y in test_points:
        z = complex(x, y)
        qz = beta_quot(z)
        
        for n in grid_neighbors(z):
            qn = beta_quot(n)
            dist = grid_distance(qz, qn)
            
            assert dist <= 2, \
                f"Theorem violation: βQuot({z}) and βQuot({n}) have dist {dist} > 2"
    
    print("  ✓ Theorem βQuot_preserves_neighbor_structure verified")


def main():
    print("=" * 60)
    print("Verification of β-adic Implementation")
    print("=" * 60)
    print()
    
    # Core β-adic operations
    test_digit()
    test_beta_quot()
    test_cylinder_pattern()
    test_cylinder_distance()
    test_fast_versions()
    test_grid_operations()
    
    # Algorithm correctness
    test_astar_correctness()
    test_bcp_correctness()
    
    # Theorem verification
    test_theorem_neighbors_different_k_pattern()
    test_theorem_quotient_preserves_neighbor()
    
    print()
    print("=" * 60)
    print("ALL TESTS PASSED ✓")
    print("=" * 60)
    print()
    print("The implementation correctly matches the Lean definitions.")


if __name__ == "__main__":
    main()
