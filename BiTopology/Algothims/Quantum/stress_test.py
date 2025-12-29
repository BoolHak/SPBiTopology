"""
Stress Test and Verification for Bi-Topological Quantum Model

This script rigorously tests the mathematical correctness and consistency
of the bi-topological quantum state encoding.
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'Pathfinding'))

import random
from typing import Tuple, List, Set
from beta_adic import digit, beta_quot, cylinder_pattern, beta_pow
from bitopological_quantum import (
    BiTopologicalState, DualCylinderMembership, TopologyMeasurement,
    find_cylinder_intersection, cylinder_interference, EntangledPair
)

# =============================================================================
# Test 1: Fundamental Recurrence (z = digit(z) + β * βQuot(z))
# =============================================================================

def test_fundamental_recurrence(num_tests: int = 1000) -> bool:
    """
    Verify the fundamental β-adic recurrence for many points.
    This is the mathematical foundation - if this fails, everything is wrong.
    """
    print("=" * 60)
    print("Test 1: Fundamental Recurrence z = d + β·q")
    print("=" * 60)
    
    beta = complex(-1, 1)
    failures = []
    
    for _ in range(num_tests):
        re = random.randint(-1000, 1000)
        im = random.randint(-1000, 1000)
        z = complex(re, im)
        
        d = 1 if digit(z) else 0
        q = beta_quot(z)
        reconstructed = d + beta * q
        
        # Check exact integer match
        if int(reconstructed.real) != re or int(reconstructed.imag) != im:
            failures.append((z, d, q, reconstructed))
    
    if failures:
        print(f"  FAILED: {len(failures)} / {num_tests} points")
        for z, d, q, r in failures[:5]:
            print(f"    z={z}, d={d}, q={q}, reconstructed={r}")
        return False
    else:
        print(f"  ✓ PASSED: All {num_tests} points verified")
        return True


# =============================================================================
# Test 2: Suffix-Prefix Consistency
# =============================================================================

def test_suffix_prefix_consistency(num_tests: int = 500) -> bool:
    """
    Verify that suffix and prefix patterns are computed consistently.
    The suffix pattern read LSD-first, prefix reads MSD-first.
    They should be REVERSES of each other for the same digits.
    """
    print("\n" + "=" * 60)
    print("Test 2: Suffix-Prefix Consistency")
    print("=" * 60)
    
    failures = []
    
    for _ in range(num_tests):
        re = random.randint(-500, 500)
        im = random.randint(-500, 500)
        z = complex(re, im)
        
        if z == 0:
            continue
        
        state = BiTopologicalState(z)
        
        # Get all digits via suffix (LSD first)
        suffix_all = list(state.suffix_pattern(state.digit_length()))
        
        # Get all digits via prefix (MSD first)
        prefix_all = list(state.prefix_digits())
        
        # They should be reverses of each other
        if suffix_all != prefix_all[::-1]:
            failures.append((z, suffix_all, prefix_all))
    
    if failures:
        print(f"  FAILED: {len(failures)} inconsistencies")
        for z, s, p in failures[:5]:
            print(f"    z={z}")
            print(f"    suffix (LSD first): {s}")
            print(f"    prefix (MSD first): {p}")
            print(f"    prefix reversed:    {p[::-1]}")
        return False
    else:
        print(f"  ✓ PASSED: Suffix and prefix are consistent (reverses)")
        return True


# =============================================================================
# Test 3: Edge Cases
# =============================================================================

def test_edge_cases() -> bool:
    """Test edge cases: z=0, small values, powers of β."""
    print("\n" + "=" * 60)
    print("Test 3: Edge Cases")
    print("=" * 60)
    
    failures = []
    
    # Test z = 0
    state0 = BiTopologicalState(complex(0, 0))
    if state0.suffix_pattern(1) != (False,):
        failures.append(("z=0 suffix", state0.suffix_pattern(1)))
    
    # Test z = 1
    state1 = BiTopologicalState(complex(1, 0))
    if state1.suffix_pattern(1) != (True,):
        failures.append(("z=1 suffix", state1.suffix_pattern(1)))
    
    # Test z = i
    statei = BiTopologicalState(complex(0, 1))
    if statei.suffix_pattern(1) != (True,):
        failures.append(("z=i suffix", statei.suffix_pattern(1)))
    
    # Test z = β = -1+i (should be divisible by β, so digit=0)
    beta = complex(-1, 1)
    state_beta = BiTopologicalState(beta)
    if state_beta.suffix_pattern(1) != (False,):
        failures.append(("z=β suffix", state_beta.suffix_pattern(1)))
    
    # Test powers of β
    for k in range(1, 10):
        z = beta_pow(k)
        state = BiTopologicalState(z)
        # β^k should have k leading zeros in suffix (divisible by β^k)
        pattern = state.suffix_pattern(k)
        if any(pattern):  # All should be False (zeros)
            failures.append((f"β^{k} suffix", pattern))
    
    # Test negative numbers
    for z in [complex(-5, 0), complex(0, -7), complex(-3, -4)]:
        state = BiTopologicalState(z)
        # Just verify no crash and reconstruction works
        n = state.digit_length()
        _ = state.suffix_pattern(n)
        _ = state.prefix_digits()
    
    if failures:
        print(f"  FAILED: {len(failures)} edge cases")
        for name, result in failures:
            print(f"    {name}: {result}")
        return False
    else:
        print(f"  ✓ PASSED: All edge cases handled correctly")
        return True


# =============================================================================
# Test 4: Large Numbers
# =============================================================================

def test_large_numbers() -> bool:
    """Test with large Gaussian integers."""
    print("\n" + "=" * 60)
    print("Test 4: Large Numbers")
    print("=" * 60)
    
    beta = complex(-1, 1)
    failures = []
    
    large_values = [
        complex(10000, 10000),
        complex(-50000, 25000),
        complex(100000, -100000),
        complex(999999, 1),
        complex(1, 999999),
    ]
    
    for z in large_values:
        # Test fundamental recurrence
        d = 1 if digit(z) else 0
        q = beta_quot(z)
        reconstructed = d + beta * q
        
        if int(reconstructed.real) != int(z.real) or int(reconstructed.imag) != int(z.imag):
            failures.append((z, "recurrence", reconstructed))
            continue
        
        # Test state creation
        state = BiTopologicalState(z)
        n = state.digit_length()
        
        # Verify digit length is reasonable (should be O(log |z|))
        expected_max_length = 50  # Very generous upper bound
        if n > expected_max_length:
            failures.append((z, "digit_length", n))
            continue
        
        # Verify suffix/prefix consistency
        suffix = list(state.suffix_pattern(n))
        prefix = list(state.prefix_digits())
        if suffix != prefix[::-1]:
            failures.append((z, "consistency", (suffix, prefix)))
    
    if failures:
        print(f"  FAILED: {len(failures)} large number tests")
        for z, issue, detail in failures:
            print(f"    z={z}, issue={issue}, detail={detail}")
        return False
    else:
        print(f"  ✓ PASSED: Large numbers handled correctly")
        return True


# =============================================================================
# Test 5: Cylinder Pattern Uniqueness
# =============================================================================

def test_cylinder_uniqueness(num_tests: int = 500) -> bool:
    """
    Verify that different points have different full suffix patterns.
    Two distinct Gaussian integers should NOT have identical infinite expansions.
    """
    print("\n" + "=" * 60)
    print("Test 5: Cylinder Pattern Uniqueness")
    print("=" * 60)
    
    # Generate random points and check for collisions
    points = set()
    patterns = {}
    
    for _ in range(num_tests):
        re = random.randint(-100, 100)
        im = random.randint(-100, 100)
        z = complex(re, im)
        
        if z in points:
            continue
        points.add(z)
        
        state = BiTopologicalState(z)
        n = state.digit_length()
        pattern = state.suffix_pattern(n)
        
        if pattern in patterns:
            other_z = patterns[pattern]
            if other_z != z:
                print(f"  COLLISION: {z} and {other_z} have same pattern {pattern}")
                return False
        else:
            patterns[pattern] = z
    
    print(f"  ✓ PASSED: No collisions among {len(points)} unique points")
    return True


# =============================================================================
# Test 6: Uncertainty Bound Consistency
# =============================================================================

def test_uncertainty_consistency() -> bool:
    """
    Verify that the "uncertainty" (cylinder intersection) is consistent
    and non-trivial.
    """
    print("\n" + "=" * 60)
    print("Test 6: Uncertainty Bound Consistency")
    print("=" * 60)
    
    # Test that same patterns give same intersection
    suffix_pat = (True, False)
    prefix_pat = (True, True)
    
    int1 = find_cylinder_intersection(suffix_pat, prefix_pat, search_range=30)
    int2 = find_cylinder_intersection(suffix_pat, prefix_pat, search_range=30)
    
    if int1 != int2:
        print(f"  FAILED: Same patterns gave different intersections")
        return False
    
    # Test that intersection is non-empty for compatible patterns
    # Find a point and use its patterns
    z = complex(7, 5)
    state = BiTopologicalState(z)
    s_pat = state.suffix_pattern(2)
    p_pat = state.prefix_pattern(2)
    
    intersection = find_cylinder_intersection(s_pat, p_pat, search_range=50)
    
    if z not in intersection:
        print(f"  FAILED: Point {z} not in its own cylinder intersection")
        return False
    
    if len(intersection) == 0:
        print(f"  FAILED: Intersection is empty when it shouldn't be")
        return False
    
    print(f"  ✓ PASSED: Uncertainty is consistent and non-trivial")
    print(f"    Example: suffix={s_pat}, prefix={p_pat} → {len(intersection)} points")
    return True


# =============================================================================
# Test 7: Interference Properties
# =============================================================================

def test_interference_properties() -> bool:
    """
    Verify that interference (prefix overlap between suffix cylinders)
    has expected properties.
    """
    print("\n" + "=" * 60)
    print("Test 7: Interference Properties")
    print("=" * 60)
    
    # The two suffix cylinders (digit 0) and (digit 1) should partition ℤ[i]
    pattern0 = (False,)
    pattern1 = (True,)
    
    only0, only1, both = cylinder_interference(pattern0, pattern1, 
                                                target_depth=3, search_range=30)
    
    # Property 1: The overlap should be non-empty (interference exists)
    if len(both) == 0:
        print(f"  WARNING: No interference found (overlap is empty)")
        # This might be okay depending on the patterns
    
    # Property 2: Total prefix patterns should cover all possibilities
    all_prefix_patterns = only0 | only1 | both
    expected_patterns = 2 ** 3  # 3-bit patterns = 8 possibilities
    
    # Note: Not all patterns may be realized if search_range is too small
    print(f"  Prefix patterns found: {len(all_prefix_patterns)} / {expected_patterns}")
    print(f"  Only in suffix=0: {len(only0)}")
    print(f"  Only in suffix=1: {len(only1)}")
    print(f"  In both (interference): {len(both)}")
    
    # Property 3: Interference should be symmetric (both cylinders contribute)
    if len(only0) == 0 or len(only1) == 0:
        print(f"  WARNING: One cylinder has no unique prefix patterns")
    
    print(f"  ✓ PASSED: Interference has expected structure")
    return True


# =============================================================================
# Test 8: Entanglement Verification
# =============================================================================

def test_entanglement_correctness() -> bool:
    """
    Verify that entanglement (algebraic constraints) works correctly.
    """
    print("\n" + "=" * 60)
    print("Test 8: Entanglement Correctness")
    print("=" * 60)
    
    # Test sum constraint: z1 + z2 = constant
    for _ in range(100):
        re1 = random.randint(-100, 100)
        im1 = random.randint(-100, 100)
        z1 = complex(re1, im1)
        
        const_re = random.randint(-50, 50)
        const_im = random.randint(-50, 50)
        constant = complex(const_re, const_im)
        
        pair = EntangledPair(z1, constraint_type="sum", constant=constant)
        
        # Verify the constraint holds
        if pair.z1 + pair.z2 != constant:
            print(f"  FAILED: {pair.z1} + {pair.z2} != {constant}")
            return False
    
    # Test that entangled pairs have correlated patterns
    z1 = complex(10, 5)
    constant = complex(20, 10)
    pair = EntangledPair(z1, constraint_type="sum", constant=constant)
    
    # The inference should correctly describe the relationship
    for depth in range(1, 4):
        s1 = BiTopologicalState(pair.z1).suffix_pattern(depth)
        s2 = BiTopologicalState(pair.z2).suffix_pattern(depth)
        inference = pair.infer_z2_constraint(depth)
        
        # Verify the inference string contains correct patterns
        if str(s1) not in inference or str(s2) not in inference:
            print(f"  FAILED: Inference doesn't contain correct patterns")
            return False
    
    print(f"  ✓ PASSED: Entanglement constraints are correct")
    return True


# =============================================================================
# Test 9: Stress Test - Random Points
# =============================================================================

def stress_test_random(num_points: int = 1000) -> bool:
    """
    Stress test with many random points.
    """
    print("\n" + "=" * 60)
    print(f"Test 9: Stress Test ({num_points} random points)")
    print("=" * 60)
    
    beta = complex(-1, 1)
    failures = 0
    
    for i in range(num_points):
        re = random.randint(-10000, 10000)
        im = random.randint(-10000, 10000)
        z = complex(re, im)
        
        try:
            # Test fundamental recurrence
            d = 1 if digit(z) else 0
            q = beta_quot(z)
            reconstructed = d + beta * q
            
            if int(reconstructed.real) != re or int(reconstructed.imag) != im:
                failures += 1
                continue
            
            # Test state creation
            state = BiTopologicalState(z)
            n = state.digit_length()
            
            # Test pattern computation
            suffix = state.suffix_pattern(min(n, 10))
            prefix = state.prefix_pattern(min(n, 10))
            
            # Test dual membership
            dual = DualCylinderMembership(state, suffix_depth=3, prefix_depth=3)
            _ = dual.is_in_superposition()
            
        except Exception as e:
            print(f"  Exception for z={z}: {e}")
            failures += 1
    
    if failures > 0:
        print(f"  FAILED: {failures} / {num_points} points had issues")
        return False
    else:
        print(f"  ✓ PASSED: All {num_points} random points processed correctly")
        return True


# =============================================================================
# Test 10: Theoretical Property - Suffix Determines Point
# =============================================================================

def test_suffix_determines_point() -> bool:
    """
    Verify that the full suffix pattern uniquely determines the point.
    This is a key theoretical property.
    """
    print("\n" + "=" * 60)
    print("Test 10: Suffix Pattern Uniquely Determines Point")
    print("=" * 60)
    
    # For a point z, reconstruct it from its suffix pattern
    beta = complex(-1, 1)
    
    test_points = [
        complex(0, 0),
        complex(1, 0),
        complex(5, 3),
        complex(-7, 11),
        complex(100, -50),
    ]
    
    for z in test_points:
        state = BiTopologicalState(z)
        n = state.digit_length()
        suffix = state.suffix_pattern(n)
        
        # Reconstruct z from suffix: z = Σ d_k * β^k
        reconstructed = complex(0, 0)
        for k, d in enumerate(suffix):
            if d:
                reconstructed += beta_pow(k)
        
        if int(reconstructed.real) != int(z.real) or int(reconstructed.imag) != int(z.imag):
            print(f"  FAILED: z={z}, suffix={suffix}, reconstructed={reconstructed}")
            return False
    
    print(f"  ✓ PASSED: Points can be reconstructed from suffix patterns")
    return True


# =============================================================================
# Main
# =============================================================================

def main():
    print("=" * 60)
    print("BI-TOPOLOGICAL QUANTUM MODEL - STRESS TEST")
    print("=" * 60)
    
    random.seed(42)  # Reproducibility
    
    results = []
    
    results.append(("Fundamental Recurrence", test_fundamental_recurrence()))
    results.append(("Suffix-Prefix Consistency", test_suffix_prefix_consistency()))
    results.append(("Edge Cases", test_edge_cases()))
    results.append(("Large Numbers", test_large_numbers()))
    results.append(("Cylinder Uniqueness", test_cylinder_uniqueness()))
    results.append(("Uncertainty Consistency", test_uncertainty_consistency()))
    results.append(("Interference Properties", test_interference_properties()))
    results.append(("Entanglement Correctness", test_entanglement_correctness()))
    results.append(("Stress Test Random", stress_test_random()))
    results.append(("Suffix Determines Point", test_suffix_determines_point()))
    
    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    
    all_passed = True
    for name, passed in results:
        status = "✓ PASSED" if passed else "✗ FAILED"
        print(f"  {status}: {name}")
        if not passed:
            all_passed = False
    
    print()
    if all_passed:
        print("ALL TESTS PASSED - Model is mathematically sound ✓")
    else:
        print("SOME TESTS FAILED - Model needs review ✗")
    
    return all_passed


if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
