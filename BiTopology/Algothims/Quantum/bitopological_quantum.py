"""
Bi-Topological Quantum States - Implementation

This module implements quantum-like phenomena using the bi-topological structure
on Gaussian integers WITHOUT probability. Probability emerges from the discontinuity
between the two topologies, but here we work at the pre-probabilistic level.

Key concepts:
- States are Gaussian integers z ∈ ℤ[i]
- Suffix topology captures local (LSD) structure
- Prefix topology captures global (MSD) structure
- "Superposition" = dual cylinder membership
- "Measurement" = topology selection
- "Uncertainty" = cylinder intersection bounds
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'Pathfinding'))

from typing import Tuple, Set, List, Optional, FrozenSet
from dataclasses import dataclass
from beta_adic import (
    digit, beta_quot, cylinder_pattern, cylinder_distance,
    grid_distance, beta_pow
)


# =============================================================================
# Core: Bi-Topological State
# =============================================================================

@dataclass(frozen=True)
class BiTopologicalState:
    """
    A quantum-like state represented as a Gaussian integer with dual characterizations.
    
    The state is DEFINITE (no probability) but has TWO incompatible descriptions:
    - Suffix pattern: determined by LSD digits
    - Prefix pattern: determined by MSD digits
    """
    z: complex  # The Gaussian integer (definite point)
    
    def suffix_pattern(self, k: int) -> Tuple[bool, ...]:
        """Get the k-digit suffix (LSD) pattern."""
        return cylinder_pattern(self.z, k)
    
    def prefix_digits(self) -> List[bool]:
        """
        Get the MSD-first digit sequence.
        This is computed by collecting all digits then reversing.
        """
        if self.z == 0:
            return [False]
        
        digits = []
        current = self.z
        while current != 0:
            digits.append(digit(current))
            current = beta_quot(current)
        
        return digits[::-1]  # Reverse to get MSD first
    
    def prefix_pattern(self, m: int) -> Tuple[bool, ...]:
        """Get the first m MSD digits."""
        all_digits = self.prefix_digits()
        return tuple(all_digits[:min(m, len(all_digits))])
    
    def digit_length(self) -> int:
        """The number of digits in the β-adic representation."""
        return len(self.prefix_digits())


# =============================================================================
# Superposition: Dual Cylinder Membership
# =============================================================================

@dataclass
class DualCylinderMembership:
    """
    Represents the "superposition" of a state - its membership in both
    suffix and prefix cylinders.
    
    This is NOT probability - it's the dual characterization of a definite point.
    """
    state: BiTopologicalState
    suffix_depth: int
    prefix_depth: int
    
    @property
    def suffix_cylinder(self) -> Tuple[bool, ...]:
        return self.state.suffix_pattern(self.suffix_depth)
    
    @property
    def prefix_cylinder(self) -> Tuple[bool, ...]:
        return self.state.prefix_pattern(self.prefix_depth)
    
    def is_in_superposition(self) -> bool:
        """
        A state is in "superposition" if its suffix and prefix patterns
        at the given depths are incompatible characterizations.
        
        Here "incompatible" means: knowing one doesn't determine the other.
        """
        # For non-trivial states, suffix and prefix are always incompatible
        # because they read digits in opposite orders
        return self.suffix_depth > 0 and self.prefix_depth > 0


# =============================================================================
# Measurement: Topology Selection
# =============================================================================

class TopologyMeasurement:
    """
    Measurement in the bi-topological framework.
    
    Unlike quantum mechanics, there's no "collapse" - measurement is simply
    choosing which topology to use for observation.
    """
    
    @staticmethod
    def measure_suffix(state: BiTopologicalState, depth: int) -> Tuple[bool, ...]:
        """
        Measure in the suffix basis at given depth.
        Returns the suffix cylinder the state belongs to.
        """
        return state.suffix_pattern(depth)
    
    @staticmethod
    def measure_prefix(state: BiTopologicalState, depth: int) -> Tuple[bool, ...]:
        """
        Measure in the prefix basis at given depth.
        Returns the prefix cylinder the state belongs to.
        """
        return state.prefix_pattern(depth)
    
    @staticmethod
    def full_measurement(state: BiTopologicalState) -> Tuple[Tuple[bool, ...], Tuple[bool, ...]]:
        """
        Complete measurement: return both suffix and prefix characterizations.
        
        This is allowed! Unlike QM, we CAN know both - they're just different
        representations of the same definite state.
        """
        suffix = tuple(state.suffix_pattern(state.digit_length()))
        prefix = tuple(state.prefix_digits())
        return (suffix, prefix)


# =============================================================================
# Uncertainty: Cylinder Intersection Bounds
# =============================================================================

def find_cylinder_intersection(suffix_pattern: Tuple[bool, ...],
                                prefix_pattern: Tuple[bool, ...],
                                search_range: int = 1000) -> Set[complex]:
    """
    Find all Gaussian integers matching both suffix and prefix patterns.
    
    This is the "uncertainty" computation: how many states are compatible
    with given suffix AND prefix constraints?
    
    The SIZE of this set is the "uncertainty" - analogous to Δx·Δp.
    """
    k = len(suffix_pattern)
    m = len(prefix_pattern)
    
    compatible = set()
    
    # Search in a bounded region
    for re in range(-search_range, search_range + 1):
        for im in range(-search_range, search_range + 1):
            z = complex(re, im)
            state = BiTopologicalState(z)
            
            # Check suffix match
            if state.suffix_pattern(k) != suffix_pattern:
                continue
            
            # Check prefix match
            if state.prefix_pattern(m) != prefix_pattern:
                continue
            
            compatible.add(z)
    
    return compatible


def uncertainty_bound(suffix_depth: int, prefix_depth: int, 
                      sample_size: int = 100) -> float:
    """
    Empirically estimate the uncertainty bound.
    
    For random suffix/prefix patterns at given depths, compute the average
    size of the intersection. This is the "topological uncertainty".
    """
    import random
    
    total_intersection_size = 0
    valid_samples = 0
    
    for _ in range(sample_size):
        # Random patterns
        suffix_pattern = tuple(random.choice([True, False]) for _ in range(suffix_depth))
        prefix_pattern = tuple(random.choice([True, False]) for _ in range(prefix_depth))
        
        intersection = find_cylinder_intersection(suffix_pattern, prefix_pattern, 
                                                   search_range=50)
        
        if intersection:  # Only count non-empty intersections
            total_intersection_size += len(intersection)
            valid_samples += 1
    
    if valid_samples == 0:
        return 0.0
    
    return total_intersection_size / valid_samples


# =============================================================================
# Interference: Cylinder Overlap Structure
# =============================================================================

def cylinder_interference(pattern1: Tuple[bool, ...], 
                          pattern2: Tuple[bool, ...],
                          target_topology: str = "prefix",
                          target_depth: int = 3,
                          search_range: int = 100) -> Tuple[Set[Tuple], Set[Tuple], Set[Tuple]]:
    """
    Compute the "interference" between two suffix cylinders when viewed
    in the prefix topology.
    
    Returns:
    - only_in_1: prefix patterns only in cylinder 1
    - only_in_2: prefix patterns only in cylinder 2
    - in_both: prefix patterns in both (constructive interference)
    """
    k = len(pattern1)
    assert len(pattern2) == k, "Patterns must have same depth"
    
    # Find all points in each suffix cylinder
    points1 = set()
    points2 = set()
    
    for re in range(-search_range, search_range + 1):
        for im in range(-search_range, search_range + 1):
            z = complex(re, im)
            state = BiTopologicalState(z)
            suffix = state.suffix_pattern(k)
            
            if suffix == pattern1:
                points1.add(z)
            if suffix == pattern2:
                points2.add(z)
    
    # Project to prefix patterns
    def to_prefix(points: Set[complex]) -> Set[Tuple[bool, ...]]:
        result = set()
        for z in points:
            state = BiTopologicalState(z)
            result.add(state.prefix_pattern(target_depth))
        return result
    
    prefix1 = to_prefix(points1)
    prefix2 = to_prefix(points2)
    
    only_in_1 = prefix1 - prefix2
    only_in_2 = prefix2 - prefix1
    in_both = prefix1 & prefix2
    
    return only_in_1, only_in_2, in_both


# =============================================================================
# Entanglement: Algebraic Constraints
# =============================================================================

@dataclass
class EntangledPair:
    """
    Two Gaussian integers with an algebraic constraint that creates
    "entanglement" - knowing one constrains knowledge of the other.
    """
    z1: complex
    z2: complex
    constraint: str  # Description of the constraint
    
    def __init__(self, z1: complex, constraint_type: str = "sum", constant: complex = 0):
        self.z1 = z1
        
        if constraint_type == "sum":
            # z1 + z2 = constant
            self.z2 = constant - z1
            self.constraint = f"z1 + z2 = {constant}"
        elif constraint_type == "product":
            # z1 * z2 = constant (if divisible)
            if z1 != 0 and constant.real % z1.real == 0 and constant.imag % z1.imag == 0:
                self.z2 = constant / z1
            else:
                self.z2 = complex(0, 0)
            self.constraint = f"z1 * z2 = {constant}"
        elif constraint_type == "difference":
            # z1 - z2 = constant
            self.z2 = z1 - constant
            self.constraint = f"z1 - z2 = {constant}"
    
    def measure_z1_suffix(self, depth: int) -> Tuple[bool, ...]:
        """Measure z1 in suffix basis."""
        return BiTopologicalState(self.z1).suffix_pattern(depth)
    
    def infer_z2_constraint(self, depth: int) -> str:
        """
        Given z1's suffix pattern, what do we know about z2?
        
        This is "entanglement" - measuring z1 tells us something about z2.
        """
        z1_suffix = self.measure_z1_suffix(depth)
        z2_suffix = BiTopologicalState(self.z2).suffix_pattern(depth)
        
        # The constraint is: their patterns must satisfy the algebraic relation
        return f"z1 suffix = {z1_suffix} implies z2 suffix = {z2_suffix}"


# =============================================================================
# Testing
# =============================================================================

def test_superposition():
    """Test the superposition concept."""
    print("=" * 60)
    print("Testing Bi-Topological Superposition")
    print("=" * 60)
    
    z = complex(13, 7)
    state = BiTopologicalState(z)
    
    print(f"\nState: z = {z}")
    print(f"Digit length: {state.digit_length()}")
    print(f"Suffix pattern (k=4): {state.suffix_pattern(4)}")
    print(f"Prefix pattern (m=4): {state.prefix_pattern(4)}")
    
    dual = DualCylinderMembership(state, suffix_depth=4, prefix_depth=4)
    print(f"\nIn superposition? {dual.is_in_superposition()}")
    print(f"Suffix cylinder: {dual.suffix_cylinder}")
    print(f"Prefix cylinder: {dual.prefix_cylinder}")
    
    print("\n✓ Superposition test complete")


def test_measurement():
    """Test the measurement concept."""
    print("\n" + "=" * 60)
    print("Testing Bi-Topological Measurement")
    print("=" * 60)
    
    z = complex(5, 3)
    state = BiTopologicalState(z)
    
    print(f"\nState: z = {z}")
    
    for depth in range(1, 5):
        suffix = TopologyMeasurement.measure_suffix(state, depth)
        prefix = TopologyMeasurement.measure_prefix(state, depth)
        print(f"Depth {depth}: suffix={suffix}, prefix={prefix}")
    
    full_s, full_p = TopologyMeasurement.full_measurement(state)
    print(f"\nFull measurement:")
    print(f"  Suffix (LSD first): {full_s}")
    print(f"  Prefix (MSD first): {full_p}")
    
    print("\n✓ Measurement test complete")


def test_uncertainty():
    """Test the uncertainty principle."""
    print("\n" + "=" * 60)
    print("Testing Bi-Topological Uncertainty")
    print("=" * 60)
    
    print("\nFinding intersection of suffix and prefix cylinders...")
    
    # Example: suffix pattern (True, False) and prefix pattern (True, True)
    suffix_pat = (True, False)
    prefix_pat = (True, True)
    
    intersection = find_cylinder_intersection(suffix_pat, prefix_pat, search_range=50)
    print(f"Suffix pattern: {suffix_pat}")
    print(f"Prefix pattern: {prefix_pat}")
    print(f"Intersection size: {len(intersection)}")
    if len(intersection) <= 10:
        print(f"Points: {intersection}")
    
    print("\n✓ Uncertainty test complete")


def test_interference():
    """Test the interference concept."""
    print("\n" + "=" * 60)
    print("Testing Bi-Topological Interference")
    print("=" * 60)
    
    pattern1 = (True,)   # Suffix starts with 1
    pattern2 = (False,)  # Suffix starts with 0
    
    only1, only2, both = cylinder_interference(pattern1, pattern2, 
                                                target_depth=3, search_range=30)
    
    print(f"\nSuffix cylinder 1: pattern = {pattern1}")
    print(f"Suffix cylinder 2: pattern = {pattern2}")
    print(f"\nPrefix patterns (depth 3) in only cylinder 1: {len(only1)}")
    print(f"Prefix patterns (depth 3) in only cylinder 2: {len(only2)}")
    print(f"Prefix patterns (depth 3) in BOTH (interference): {len(both)}")
    
    if both:
        print(f"Interfering patterns: {both}")
    
    print("\n✓ Interference test complete")


def test_entanglement():
    """Test the entanglement concept."""
    print("\n" + "=" * 60)
    print("Testing Bi-Topological Entanglement")
    print("=" * 60)
    
    # Create an entangled pair with sum constraint
    z1 = complex(7, 3)
    constant = complex(10, 10)
    pair = EntangledPair(z1, constraint_type="sum", constant=constant)
    
    print(f"\nEntangled pair with constraint: {pair.constraint}")
    print(f"z1 = {pair.z1}")
    print(f"z2 = {pair.z2}")
    
    for depth in range(1, 4):
        inference = pair.infer_z2_constraint(depth)
        print(f"Depth {depth}: {inference}")
    
    print("\n✓ Entanglement test complete")


def main():
    print("=" * 60)
    print("BI-TOPOLOGICAL QUANTUM STATES")
    print("(Without Probability)")
    print("=" * 60)
    
    test_superposition()
    test_measurement()
    test_uncertainty()
    test_interference()
    test_entanglement()
    
    print("\n" + "=" * 60)
    print("ALL TESTS COMPLETE")
    print("=" * 60)


if __name__ == "__main__":
    main()
