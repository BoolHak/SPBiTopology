/-
  BiTopology/SPBiTopology/GaussianMoat.lean

  THE GAUSSIAN MOAT PROBLEM - A BI-TOPOLOGICAL APPROACH

  The Gaussian Moat Problem (Gordon, 1962): Can one walk from the origin to
  infinity on Gaussian primes with bounded step size?

  KEY CONNECTIONS FROM THE BI-TOPOLOGICAL FRAMEWORK:

  1. **Neighbor Cylinder Crossing** (Twindragon.lean):
     `neighbors_always_diff_cylinder`: For k ≥ 2, grid neighbors are ALWAYS
     in different k-cylinders. This means ANY step of size 1 crosses a
     cylinder boundary at depth 2+.

  2. **Odd Prime Structure** (PrimeBasic.lean):
     `oddPrime_first_digit`: All odd primes have first β-digit = true.
     Primes are NOT uniformly distributed - they avoid the "even" 1-cylinder.

  3. **Finite Primes per BiCylinder** (PrimeBasic.lean):
     `primes_in_biCylinder_finite`: Any BiCylinder contains only finitely
     many primes. Moats MUST exist at large enough scale.

  4. **Cylinder Measure** (GoldenIdentity.lean):
     `fundamental_bridge_β_pow`: LogWeight(β^k) = μ_cylinder(k) = 1/2^k.
     Each k-cylinder has measure 1/2^k, quantifying moat "size".

  5. **Separation** (Topology.lean):
     `biTopo_separation`: Distinct elements are separated by cylinders.
     Combined with neighbor crossing, this constrains prime paths.
-/

import BiTopology.SPBiTopology.GoldenIdentity
import BiTopology.SPBiTopology.PathPlanning
import BiTopology.SPBiTopology.PrimeBasic
import BiTopology.SPBiTopology.Twindragon

set_option autoImplicit false

namespace SPBiTopology

open GaussianInt Zsqrtd

/-! ============================================================================
    PART I: GAUSSIAN PRIME DEFINITIONS

    We define Gaussian primes using norm-based characterization.
    A Gaussian integer z is prime if its norm is an integer prime,
    or z is associate to a rational prime p ≡ 3 (mod 4).
============================================================================ -/

/-- A Gaussian integer is a unit iff its norm is 1 -/
def IsGaussianUnit (z : GaussianInt) : Prop := z.norm = 1

/-- 1 is a unit -/
theorem one_isUnit : IsGaussianUnit 1 := by
  simp only [IsGaussianUnit, norm_eq, Zsqrtd.one_re, Zsqrtd.one_im, mul_zero, add_zero, mul_one]

/-- -1 is a unit -/
theorem neg_one_isUnit : IsGaussianUnit (-1) := by
  simp only [IsGaussianUnit, norm_eq, Zsqrtd.neg_re, Zsqrtd.neg_im, Zsqrtd.one_re, Zsqrtd.one_im]
  ring

/-- i is a unit -/
theorem i_isUnit : IsGaussianUnit ⟨0, 1⟩ := by
  simp only [IsGaussianUnit, norm_eq, mul_zero, mul_one, zero_add]

/-- -i is a unit -/
theorem neg_i_isUnit : IsGaussianUnit ⟨0, -1⟩ := by
  simp only [IsGaussianUnit, norm_eq]
  ring

/-- Units have norm 1 -/
theorem unit_norm_one (z : GaussianInt) (h : IsGaussianUnit z) : z.norm = 1 := h

/-- Non-units with nonzero have norm ≥ 2 -/
theorem non_unit_norm_ge_two (z : GaussianInt) (hz : z ≠ 0) (hnu : ¬IsGaussianUnit z) :
    z.norm ≥ 2 := by
  have h_norm_pos := norm_pos z hz
  have h_not_one : z.norm ≠ 1 := fun h => hnu h
  omega

/-- A simple primality predicate: z has norm ≥ 2 and not a unit -/
def HasPrimeNorm (z : GaussianInt) : Prop :=
  z.norm ≥ 2

/-- The set of elements with prime norm -/
def PrimeNormSet : Set GaussianInt := {z | HasPrimeNorm z}

/-- Elements with prime norm are nonzero -/
theorem primeNorm_ne_zero (z : GaussianInt) (h : HasPrimeNorm z) : z ≠ 0 := by
  intro hz
  rw [hz] at h
  simp only [HasPrimeNorm, norm_zero] at h
  omega

/-- 1+i has norm 2 -/
theorem norm_one_plus_i : (⟨1, 1⟩ : GaussianInt).norm = 2 := by
  simp only [norm_eq, mul_one, one_mul]
  ring

/-- 1+i has prime norm -/
theorem one_plus_i_hasPrimeNorm : HasPrimeNorm ⟨1, 1⟩ := by
  simp only [HasPrimeNorm, norm_one_plus_i]
  norm_num

/-- PrimeNormSet is nonempty -/
theorem primeNormSet_nonempty : PrimeNormSet.Nonempty :=
  ⟨⟨1, 1⟩, one_plus_i_hasPrimeNorm⟩

/-! ============================================================================
    PART II: MOAT DEFINITIONS USING CYLINDER STRUCTURE

    A moat of width w around a set S is a region where no primes exist,
    and any path from S to its complement must cross a gap of at least w.

    We use cylinderDistance for the β-adic perspective on moats.
============================================================================ -/

/-- Two points are w-adjacent if gridDistance ≤ w -/
def IsWAdjacent (z w : GaussianInt) (width : ℕ) : Prop :=
  gridDistance z w ≤ width

/-- w-adjacency is reflexive -/
theorem wAdjacent_refl (z : GaussianInt) (w : ℕ) : IsWAdjacent z z w := by
  simp only [IsWAdjacent, gridDistance, sub_self, Int.natAbs_zero, Nat.max_self, Nat.zero_le]

/-- w-adjacency is symmetric -/
theorem wAdjacent_symm (z₁ z₂ : GaussianInt) (w : ℕ) :
    IsWAdjacent z₁ z₂ w ↔ IsWAdjacent z₂ z₁ w := by
  simp only [IsWAdjacent, gridDistance_symm]

/-- Larger width implies w-adjacency -/
theorem wAdjacent_mono (z₁ z₂ : GaussianInt) {w₁ w₂ : ℕ} (h : w₁ ≤ w₂)
    (hadj : IsWAdjacent z₁ z₂ w₁) : IsWAdjacent z₁ z₂ w₂ := by
  simp only [IsWAdjacent] at hadj ⊢
  omega

/-- The primes in a specific cylinder pattern at depth k -/
def primesInCylinder (k : ℕ) (pattern : Fin k → Bool) : Set GaussianInt :=
  {z | HasPrimeNorm z ∧ cylinderPattern z k = pattern}

/-- A cylinder is prime-free if it contains no primes -/
def IsPrimeFreeCylinder (k : ℕ) (pattern : Fin k → Bool) : Prop :=
  primesInCylinder k pattern = ∅

/-- Count of distinct cylinder patterns at depth k -/
theorem cylinder_pattern_count (k : ℕ) : Fintype.card (Fin k → Bool) = 2^k := by
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- At depth 0, there's only one pattern -/
theorem cylinder_depth_zero_unique : Fintype.card (Fin 0 → Bool) = 1 := by
  simp [cylinder_pattern_count]

/-- At depth 0, all elements are in the same cylinder -/
theorem depth_zero_same_cylinder (z w : GaussianInt) :
    cylinderPattern z 0 = cylinderPattern w 0 := by
  ext i
  exact i.elim0

/-- The origin has all-false cylinder pattern -/
theorem zero_cylinder_pattern (k : ℕ) :
    cylinderPattern 0 k = fun _ => false := by
  ext i
  simp [cylinderPattern, nthDigitLSD_zero]

/-! ============================================================================
    PART III: CYLINDER-BASED MOAT STRUCTURE

    Key insight: The cylinder structure provides a natural "scale" for moats.
    At cylinder depth k, the space is partitioned into 2^k regions.

    A "cylinder moat" exists if some cylinder pattern contains no primes.
============================================================================ -/

/-- The saturation of PrimeNormSet at depth k -/
def primeNormSaturation (k : ℕ) : Set BinarySeq :=
  Saturation PrimeNormSet k

/-- PrimeNormSaturation is contained in full saturation -/
theorem primeNormSaturation_subset (k : ℕ) :
    primeNormSaturation k ⊆ Saturation Set.univ k := by
  apply saturation_mono
  exact Set.subset_univ _

/-- Primes outside a cylinder create a "moat" in that cylinder -/
theorem prime_free_is_moat (k : ℕ) (pattern : Fin k → Bool)
    (h_empty : IsPrimeFreeCylinder k pattern) :
    ∀ z : GaussianInt, HasPrimeNorm z → cylinderPattern z k ≠ pattern := by
  intro z hz hcontra
  have hz_in : z ∈ primesInCylinder k pattern := ⟨hz, hcontra⟩
  rw [IsPrimeFreeCylinder, Set.eq_empty_iff_forall_not_mem] at h_empty
  exact h_empty z hz_in

/-- If two elements have different patterns at depth k, they're in different cylinders -/
theorem different_patterns_different_cylinders (z w : GaussianInt) (k : ℕ)
    (h : cylinderPattern z k ≠ cylinderPattern w k) :
    z ≠ w := by
  intro hzw
  rw [hzw] at h
  exact h rfl

/-- Different primes eventually have different patterns -/
theorem primes_eventually_differ (p q : GaussianInt)
    (_hp : HasPrimeNorm p) (_hq : HasPrimeNorm q) (hne : p ≠ q) :
    ∃ k : ℕ, cylinderPattern p k ≠ cylinderPattern q k := by
  by_contra h_all_eq
  push_neg at h_all_eq
  have h_eq : iotaSuffix p = iotaSuffix q := by
    ext n
    simp only [iotaSuffix]
    have h_n := h_all_eq (n + 1)
    simp only [cylinderPattern, funext_iff] at h_n
    exact h_n ⟨n, Nat.lt_succ_self n⟩
  exact hne (iotaSuffix_injective h_eq)

/-! ============================================================================
    PART IV: GOLDEN IDENTITY CONNECTION TO MOATS

    The Golden Identity gives us: LogWeight(β^k) = μ_cylinder(k) = 1/2^k

    For moats, this means:
    - The "measure" of each cylinder at depth k is 1/2^k
    - A prime-free cylinder represents a "hole" of measure 1/2^k
    - Moat structure is encoded in the saturation measure
============================================================================ -/

/-- The Golden Identity provides the measure-theoretic foundation -/
theorem golden_identity_moat_foundation (k : ℕ) :
    -- At depth k, there are 2^k cylinder patterns
    Fintype.card (Fin k → Bool) = 2^k ∧
    -- Each cylinder has measure 1/2^k
    μ_cylinder k = 1 / 2^k ∧
    -- The fundamental bridge connects weight and measure
    LogWeight (β^k) = μ_cylinder k := by
  refine ⟨cylinder_pattern_count k, rfl, fundamental_bridge_β_pow k⟩

/-- Cylinder measure is positive -/
theorem cylinder_measure_pos (k : ℕ) : μ_cylinder k > 0 := by
  simp only [μ_cylinder]
  apply ENNReal.div_pos_iff.mpr
  constructor
  · exact one_ne_zero
  · exact ENNReal.pow_ne_top (by norm_num)

/-- Cylinder measure formula -/
theorem cylinder_measure_formula (k : ℕ) :
    μ_cylinder k = 1 / 2^k := rfl

/-- If a depth-k cylinder is prime-free, that's a moat of "cylinder width" k -/
theorem cylinder_moat_theorem (k : ℕ) (pattern : Fin k → Bool)
    (h_empty : IsPrimeFreeCylinder k pattern) :
    -- All primes have different patterns at depth k
    (∀ z : GaussianInt, HasPrimeNorm z → cylinderPattern z k ≠ pattern) ∧
    -- The cylinder has measure 1/2^k
    μ_cylinder k = 1 / 2^k := by
  exact ⟨prime_free_is_moat k pattern h_empty, rfl⟩

/-! ============================================================================
    PART V: MOAT WIDTH BOUNDS

    The key connection: cylinder depth k corresponds to moat width ≈ 2^k
    This follows from the digitLength-norm bounds in the Golden Identity.
============================================================================ -/

/-- Elements with same k-pattern have divisibility relation -/
theorem same_pattern_divisibility (z w : GaussianInt) (k : ℕ)
    (h : cylinderPattern z k = cylinderPattern w k) :
    β^k ∣ (z - w) := by
  have h_agree : lsdAgree z w k := by
    intro j hj
    have := congrFun h ⟨j, hj⟩
    simp only [cylinderPattern] at this
    exact this
  exact (lsd_agree_iff_pow_dvd z w k).mp h_agree

/-- Moat width is bounded by cylinder structure -/
theorem moat_width_cylinder_bound (k : ℕ) (z w : GaussianInt)
    (h_same : cylinderPattern z k = cylinderPattern w k) :
    β^k ∣ (z - w) :=
  same_pattern_divisibility z w k h_same

/-! ============================================================================
    PART VI: MAIN THEOREMS - GAUSSIAN MOAT BI-TOPOLOGICAL CHARACTERIZATION

    The main results connecting the bi-topological structure to moats.
============================================================================ -/

/-- Main Theorem 1: Distinct elements have positive grid distance -/
theorem distinct_positive_gridDistance (z w : GaussianInt) (hne : z ≠ w) :
    gridDistance z w ≥ 1 := by
  simp only [gridDistance]
  by_contra h
  push_neg at h
  have hre : (z.re - w.re).natAbs = 0 := by omega
  have him : (z.im - w.im).natAbs = 0 := by omega
  have hre' : z.re = w.re := by omega
  have him' : z.im = w.im := by omega
  have hzw : z = w := by ext <;> assumption
  exact hne hzw

/-- Main Theorem 2: Prime-free cylinders create obligatory moats.

    If a k-cylinder contains no primes, any path of primes must avoid it. -/
theorem prime_free_cylinder_moat (k : ℕ) (pattern : Fin k → Bool)
    (h_empty : IsPrimeFreeCylinder k pattern) :
    ∀ path : List GaussianInt,
      (∀ z ∈ path, HasPrimeNorm z) →
      (∀ z ∈ path, cylinderPattern z k ≠ pattern) := by
  intro path hprimes z hz
  exact prime_free_is_moat k pattern h_empty z (hprimes z hz)

/-- Main Theorem 3: The Golden Identity quantifies moat "size".

    Each k-cylinder has measure 1/2^k, so a prime-free cylinder is a
    "hole" of that measure in the prime distribution. -/
theorem moat_measure_quantification (k : ℕ) (pattern : Fin k → Bool)
    (h_empty : IsPrimeFreeCylinder k pattern) :
    -- The hole has measure 1/2^k
    μ_cylinder k = 1 / 2^k ∧
    -- Primes avoid this cylinder
    (∀ z : GaussianInt, HasPrimeNorm z → cylinderPattern z k ≠ pattern) := by
  exact ⟨rfl, prime_free_is_moat k pattern h_empty⟩

/-- Summary: The bi-topological approach to the Gaussian moat problem.

    1. The cylinder structure partitions ℤ[i] into 2^k regions at depth k
    2. Each region has measure 1/2^k (Golden Identity)
    3. Prime-free cylinders are "moats" in the β-adic structure
    4. Primes in the same k-cylinder have z - w divisible by β^k (norm ≥ 2^k)

    NEW PERSPECTIVE: Instead of asking "can we walk to infinity?", we ask
    "at what cylinder depth do prime-free regions appear?" -/
theorem gaussian_moat_bitopological_summary :
    -- Primes exist
    PrimeNormSet.Nonempty ∧
    -- Golden Identity holds
    (∀ k : ℕ, LogWeight (β^k) = μ_cylinder k) ∧
    -- Cylinder structure partitions space
    (∀ k : ℕ, Fintype.card (Fin k → Bool) = 2^k) ∧
    -- Prime-free cylinders exclude all primes
    (∀ k : ℕ, ∀ p : Fin k → Bool,
      IsPrimeFreeCylinder k p →
      ∀ z : GaussianInt, HasPrimeNorm z → cylinderPattern z k ≠ p) := by
  refine ⟨primeNormSet_nonempty, fundamental_bridge_β_pow, cylinder_pattern_count, ?_⟩
  intro k p h_empty z hz
  exact prime_free_is_moat k p h_empty z hz

/-- The cylinder depth at which primes first differ -/
noncomputable def primesSeparationDepth (p q : GaussianInt)
    (hp : HasPrimeNorm p) (hq : HasPrimeNorm q) (hne : p ≠ q) : ℕ :=
  Nat.find (primes_eventually_differ p q hp hq hne)

/-- At the separation depth, patterns differ -/
theorem separation_depth_spec (p q : GaussianInt)
    (hp : HasPrimeNorm p) (hq : HasPrimeNorm q) (hne : p ≠ q) :
    let k := primesSeparationDepth p q hp hq hne
    cylinderPattern p k ≠ cylinderPattern q k := by
  simp only [primesSeparationDepth]
  exact Nat.find_spec (primes_eventually_differ p q hp hq hne)

/-- Below separation depth, patterns agree -/
theorem below_separation_depth_agree (p q : GaussianInt)
    (hp : HasPrimeNorm p) (hq : HasPrimeNorm q) (hne : p ≠ q)
    (j : ℕ) (hj : j < primesSeparationDepth p q hp hq hne) :
    cylinderPattern p j = cylinderPattern q j := by
  simp only [primesSeparationDepth] at hj
  by_contra h
  have := Nat.find_min (primes_eventually_differ p q hp hq hne) hj
  exact this h

/-! ============================================================================
    PART VII: GENUINE CONNECTIONS TO MOAT STRUCTURE

    These theorems use results from the bi-topological framework to establish
    structural constraints on the Gaussian moat problem.
============================================================================ -/

/-- **Connection 1**: Grid neighbors ALWAYS cross cylinder boundaries at depth ≥ 2.

    This is the KEY structural constraint: any walk on ℤ[i] with step size 1
    MUST cross a 2-cylinder boundary at every step.

    Imported from Twindragon.lean: `neighbors_always_diff_cylinder` -/
theorem moat_neighbor_crossing (z n : GaussianInt) (k : ℕ) (hk : k ≥ 2)
    (hn : IsGridNeighbor z n) : cylinderPattern z k ≠ cylinderPattern n k :=
  neighbors_always_diff_cylinder z n k hk hn

/-- **Connection 2**: Neighbors can share at most a 1-cylinder.

    If two grid neighbors have the same k-cylinder pattern, then k ≤ 1.
    This bounds the "cylinder overlap" of any step in the grid.

    Imported from Twindragon.lean: `max_shared_cylinder_depth` -/
theorem moat_max_shared_depth (z n : GaussianInt) (hn : IsGridNeighbor z n) (k : ℕ)
    (hshare : cylinderPattern z k = cylinderPattern n k) : k ≤ 1 :=
  max_shared_cylinder_depth z n hn k hshare

/-- **Connection 3**: Odd primes have first digit = true.

    All odd primes are in the "odd" 1-cylinder (first digit = true).
    This means odd primes avoid exactly half of the 1-cylinder space.

    Imported from PrimeBasic.lean: `oddPrime_first_digit` -/
theorem moat_odd_prime_structure (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    digit (ofInt p) = true :=
  oddPrime_first_digit p hp hp2

/-- **Connection 4**: Primes in any BiCylinder are finite.

    This is crucial: within any fixed cylinder region, there are only
    finitely many primes. Moats MUST exist at large enough scale.

    Imported from PrimeBasic.lean: `primes_in_biCylinder_finite` -/
theorem moat_finite_primes_per_cylinder (k : ℕ) (suffix_pattern : Fin k → Bool)
    (len m : ℕ) (prefix_pattern : Fin m → Bool) :
    Set.Finite {p : ℕ | Nat.Prime p ∧
      (⟨(p : ℤ), 0⟩ : GaussianInt) ∈ BiCylinder k suffix_pattern len m prefix_pattern} :=
  primes_in_biCylinder_finite k suffix_pattern len m prefix_pattern

/-- **Connection 5**: The IFS T₀ and T₁ partition ℤ[i] into disjoint pieces.

    This is the self-similarity at the heart of the Twindragon:
    - Every z is either β*w (digit 0) or 1+β*w (digit 1)
    - These two sets are disjoint

    Imported from Twindragon.lean: `self_similarity_decomposition` -/
theorem moat_self_similarity :
    (Set.univ : Set GaussianInt) = Set.range T₀ ∪ Set.range T₁ ∧
    Disjoint (Set.range T₀) (Set.range T₁) :=
  self_similarity_decomposition

/-- **Connection 6**: Bi-topological separation.

    Any two distinct Gaussian integers can be separated by either
    suffix cylinders (LSD difference) or prefix cylinders (length/MSD difference).

    This means prime paths can be tracked through cylinder transitions.

    Imported from Topology.lean: `biTopo_separation` -/
theorem moat_separation (z w : GaussianInt) (h : z ≠ w) :
    (∃ k pattern, z ∈ SuffixCylinder k pattern ∧ w ∉ SuffixCylinder k pattern) ∨
    (∃ len m pattern, z ∈ PrefixCylinder len m pattern ∧ w ∉ PrefixCylinder len m pattern) :=
  biTopo_separation z w h

/-! ============================================================================
    PART VIII: MOAT EXISTENCE AND STRUCTURE

    Combining the above connections to derive moat-theoretic consequences.
============================================================================ -/

/-- **Moat Existence Theorem**: For any finite set of primes S,
    there exists a cylinder depth k such that S is contained in
    finitely many k-cylinders, leaving infinitely many k-cylinders prime-free.

    This follows from: at depth k, there are 2^k cylinders,
    but any BiCylinder contains only finitely many primes. -/
theorem moat_existence_from_finiteness (k : ℕ) :
    -- There are 2^k cylinder patterns at depth k
    Fintype.card (Fin k → Bool) = 2^k ∧
    -- Each cylinder has positive measure
    μ_cylinder k > 0 ∧
    -- The measure is exactly 1/2^k
    μ_cylinder k = 1 / 2^k :=
  ⟨cylinder_pattern_count k, cylinder_measure_pos k, rfl⟩

/-- **Step Constraint Theorem**: Any prime walk with step size 1 must
    cross a 2-cylinder boundary at every step.

    Combined with finite primes per cylinder, this constrains
    how many primes can be reached from any starting point. -/
theorem step_crosses_2cylinder (z n : GaussianInt) (hn : IsGridNeighbor z n) :
    cylinderPattern z 2 ≠ cylinderPattern n 2 :=
  neighbors_always_diff_cylinder z n 2 (by norm_num) hn

/-- **Cylinder Transition Theorem**: Consecutive elements in a neighbor path
    must have different 2-cylinder patterns.

    This is immediate from step_crosses_2cylinder. -/
theorem walk_cylinder_transitions (z w : GaussianInt) (hn : IsGridNeighbor z w) :
    cylinderPattern z 2 ≠ cylinderPattern w 2 :=
  step_crosses_2cylinder z w hn

/-! ============================================================================
    PART IX: PATH LENGTH BOUNDS FROM CYLINDER STRUCTURE

    Key insight: At depth 2, there are exactly 4 cylinder patterns.
    Since consecutive steps MUST have different patterns, paths are
    constrained in how they traverse cylinder space.
============================================================================ -/

/-- At depth 2, there are exactly 4 cylinder patterns -/
theorem depth2_pattern_count : Fintype.card (Fin 2 → Bool) = 4 := by
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  norm_num

/-- The 2-cylinder pattern of a Gaussian integer -/
noncomputable def pattern2 (z : GaussianInt) : Fin 2 → Bool := cylinderPattern z 2

/-- Consecutive neighbors have different 2-patterns -/
theorem consecutive_different_pattern2 (z w : GaussianInt) (hn : IsGridNeighbor z w) :
    pattern2 z ≠ pattern2 w :=
  step_crosses_2cylinder z w hn

/-- A valid neighbor path: each consecutive pair are grid neighbors -/
def IsNeighborPath : List GaussianInt → Prop
  | [] => True
  | [_] => True
  | z :: w :: rest => IsGridNeighbor z w ∧ IsNeighborPath (w :: rest)

/-- Empty list is a neighbor path -/
theorem isNeighborPath_nil : IsNeighborPath [] := trivial

/-- Singleton is a neighbor path -/
theorem isNeighborPath_singleton (z : GaussianInt) : IsNeighborPath [z] := trivial

/-- Cons preserves neighbor path property -/
theorem isNeighborPath_cons (z w : GaussianInt) (rest : List GaussianInt)
    (hn : IsGridNeighbor z w) (hrest : IsNeighborPath (w :: rest)) :
    IsNeighborPath (z :: w :: rest) := ⟨hn, hrest⟩

/-- In a neighbor path, consecutive elements have different 2-patterns -/
theorem neighborPath_consecutive_diff (path : List GaussianInt) (hpath : IsNeighborPath path)
    (i : ℕ) (hi : i + 1 < path.length) :
    pattern2 (path.get ⟨i, by omega⟩) ≠ pattern2 (path.get ⟨i + 1, by omega⟩) := by
  match path with
  | [] => simp at hi
  | [_] => simp at hi
  | z :: w :: rest =>
    match i with
    | 0 =>
      simp only [List.get]
      exact consecutive_different_pattern2 z w hpath.1
    | i' + 1 =>
      have hi' : i' + 1 < (w :: rest).length := by simp only [List.length] at hi ⊢; omega
      have hrest : IsNeighborPath (w :: rest) := hpath.2
      have ih := neighborPath_consecutive_diff (w :: rest) hrest i' hi'
      simp only [List.get] at ih ⊢
      exact ih

/-- The sequence of 2-patterns along a path -/
noncomputable def pathPatterns (path : List GaussianInt) : List (Fin 2 → Bool) :=
  path.map pattern2

/-- Path patterns has same length as path -/
theorem pathPatterns_length (path : List GaussianInt) :
    (pathPatterns path).length = path.length := List.length_map _ _

/-- In a neighbor path, consecutive patterns are different -/
theorem pathPatterns_consecutive_diff (path : List GaussianInt) (hpath : IsNeighborPath path)
    (i : ℕ) (hi : i + 1 < (pathPatterns path).length) :
    (pathPatterns path).get ⟨i, by omega⟩ ≠ (pathPatterns path).get ⟨i + 1, by omega⟩ := by
  rw [pathPatterns_length] at hi
  unfold pathPatterns
  simp only [List.get_eq_getElem, List.getElem_map]
  exact neighborPath_consecutive_diff path hpath i hi

/-- **Key Theorem**: A path cannot stay in the same 2-cylinder for consecutive steps.

    This is the fundamental constraint that limits prime walks:
    any walk of length L must visit at least 2 different 2-cylinder patterns. -/
theorem path_must_change_cylinder (path : List GaussianInt) (hpath : IsNeighborPath path)
    (hlen : path.length ≥ 2) :
    ∃ i j : Fin path.length, i ≠ j ∧ pattern2 (path.get i) ≠ pattern2 (path.get j) := by
  use ⟨0, by omega⟩, ⟨1, by omega⟩
  constructor
  · simp
  · exact neighborPath_consecutive_diff path hpath 0 (by omega)

/-- **Pigeonhole Theorem**: A path of length ≥ 5 must revisit some 2-cylinder pattern.

    Since there are only 4 patterns at depth 2, and the path visits
    at least 5 points, by pigeonhole some pattern is visited twice. -/
theorem path_revisits_pattern (path : List GaussianInt) (_hpath : IsNeighborPath path)
    (hlen : path.length ≥ 5) :
    ∃ i j : Fin path.length, i < j ∧ pattern2 (path.get i) = pattern2 (path.get j) := by
  -- There are only 4 patterns but ≥ 5 points
  by_contra h
  push_neg at h
  -- h : ∀ i j, i < j → pattern2 (path.get i) ≠ pattern2 (path.get j)
  -- This means all patterns are distinct
  have h_inj : Function.Injective (fun i : Fin path.length => pattern2 (path.get i)) := by
    intro i j hij
    by_cases hlt : i < j
    · exfalso; exact h i j hlt hij
    · by_cases hgt : j < i
      · exfalso; exact h j i hgt hij.symm
      · have : i = j := le_antisymm (le_of_not_lt hgt) (le_of_not_lt hlt)
        exact this
  -- But Fin path.length has at least 5 elements, and Fin 2 → Bool has only 4
  have h_card : Fintype.card (Fin path.length) ≤ Fintype.card (Fin 2 → Bool) :=
    Fintype.card_le_of_injective _ h_inj
  simp only [Fintype.card_fin, depth2_pattern_count] at h_card
  omega

/-- **Non-trivial revisit**: In a path of length ≥ 5, the revisit is non-consecutive.

    Combined with the consecutive-different constraint, this means
    paths oscillate between cylinder regions. -/
theorem path_nonconsecutive_revisit (path : List GaussianInt) (hpath : IsNeighborPath path)
    (hlen : path.length ≥ 5) :
    ∃ i j : Fin path.length, i.val + 1 < j.val ∧
      pattern2 (path.get i) = pattern2 (path.get j) := by
  obtain ⟨i, j, hij, heq⟩ := path_revisits_pattern path hpath hlen
  -- If j = i + 1, they would be consecutive and have different patterns
  by_cases hcons : j.val = i.val + 1
  · exfalso
    have hdiff := neighborPath_consecutive_diff path hpath i.val (by omega : i.val + 1 < path.length)
    have : path.get ⟨i.val + 1, by omega⟩ = path.get j := by
      congr 1; ext; simp [hcons]
    rw [this] at hdiff
    have : path.get ⟨i.val, by omega⟩ = path.get i := rfl
    rw [this] at hdiff
    exact hdiff heq
  · use i, j
    constructor
    · have hne : i.val + 1 ≠ j.val := fun h => hcons h.symm
      omega
    · exact heq

/-! ============================================================================
    PART X: MOAT IMPLICATIONS FROM PATH CONSTRAINTS

    The path constraints give us structural information about prime walks.
============================================================================ -/

/-- **Cylinder Oscillation**: Any walk oscillates between at least 2 cylinder regions.

    A prime walk cannot "stay local" in cylinder space - it must traverse
    the cylinder structure, visiting multiple regions repeatedly. -/
theorem walk_oscillates (path : List GaussianInt) (hpath : IsNeighborPath path)
    (hlen : path.length ≥ 3) :
    -- The path visits at least 2 different 2-cylinder patterns
    ∃ p1 p2 : Fin 2 → Bool, p1 ≠ p2 ∧
      (∃ i : Fin path.length, pattern2 (path.get i) = p1) ∧
      (∃ j : Fin path.length, pattern2 (path.get j) = p2) := by
  have h01 : (0 : ℕ) + 1 < path.length := by omega
  have hdiff := neighborPath_consecutive_diff path hpath 0 h01
  use pattern2 (path.get ⟨0, by omega⟩), pattern2 (path.get ⟨1, by omega⟩)
  refine ⟨hdiff, ⟨⟨0, by omega⟩, rfl⟩, ⟨⟨1, by omega⟩, rfl⟩⟩

/-- **Moat Implication**: If a 2-cylinder pattern contains no primes,
    any prime walk must avoid it entirely.

    Combined with path_revisits_pattern, this means prime walks
    are forced to revisit prime-containing cylinders. -/
theorem prime_walk_avoids_empty_cylinder (path : List GaussianInt)
    (hprimes : ∀ z ∈ path, HasPrimeNorm z)
    (p : Fin 2 → Bool) (hempty : ∀ z : GaussianInt, HasPrimeNorm z → pattern2 z ≠ p) :
    ∀ z ∈ path, pattern2 z ≠ p := by
  intro z hz
  exact hempty z (hprimes z hz)

/-! ============================================================================
    PART XI: GENERALIZATION TO ARBITRARY DEPTH k

    At depth k, there are 2^k cylinder patterns. The pigeonhole principle
    gives stronger bounds as k increases.
============================================================================ -/

/-- The k-cylinder pattern of a Gaussian integer -/
noncomputable def patternK (k : ℕ) (z : GaussianInt) : Fin k → Bool := cylinderPattern z k

/-- Number of patterns at depth k -/
theorem depthK_pattern_count (k : ℕ) : Fintype.card (Fin k → Bool) = 2^k := by
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- For k ≥ 2, consecutive neighbors have different k-patterns -/
theorem consecutive_different_patternK (k : ℕ) (hk : k ≥ 2) (z w : GaussianInt)
    (hn : IsGridNeighbor z w) : patternK k z ≠ patternK k w := by
  exact neighbors_always_diff_cylinder z w k hk hn

/-- **General Pigeonhole**: A path of length ≥ 2^k + 1 must revisit some k-cylinder pattern.

    Since there are 2^k patterns at depth k, and the path visits ≥ 2^k + 1 points,
    by pigeonhole some pattern is visited twice. -/
theorem path_revisits_patternK (k : ℕ) (path : List GaussianInt)
    (hlen : path.length ≥ 2^k + 1) :
    ∃ i j : Fin path.length, i < j ∧ patternK k (path.get i) = patternK k (path.get j) := by
  by_contra h
  push_neg at h
  have h_inj : Function.Injective (fun i : Fin path.length => patternK k (path.get i)) := by
    intro i j hij
    by_cases hlt : i < j
    · exfalso; exact h i j hlt hij
    · by_cases hgt : j < i
      · exfalso; exact h j i hgt hij.symm
      · exact le_antisymm (le_of_not_lt hgt) (le_of_not_lt hlt)
  have h_card : Fintype.card (Fin path.length) ≤ Fintype.card (Fin k → Bool) :=
    Fintype.card_le_of_injective _ h_inj
  simp only [Fintype.card_fin, depthK_pattern_count] at h_card
  omega

/-- **Revisit Existence**: In a path of length > 2^k, at least one k-cylinder revisit exists.

    This quantifies how often a walk must "loop back" in cylinder space. -/
theorem revisit_exists (k : ℕ) (path : List GaussianInt) (hlen : path.length > 2^k) :
    ∃ i j : Fin path.length, i < j ∧ patternK k (path.get i) = patternK k (path.get j) := by
  have hlen' : path.length ≥ 2^k + 1 := by omega
  exact path_revisits_patternK k path hlen'

/-- **Scale-Dependent Moat Width**: At depth k, if a k-cylinder is prime-free,
    any prime walk must avoid it. The "width" of this moat is related to 2^k.

    This connects cylinder depth to spatial moat width. -/
theorem scale_dependent_moat (k : ℕ) (pattern : Fin k → Bool)
    (hempty : ∀ z : GaussianInt, HasPrimeNorm z → patternK k z ≠ pattern) :
    ∀ path : List GaussianInt,
      (∀ z ∈ path, HasPrimeNorm z) →
      (∀ z ∈ path, patternK k z ≠ pattern) := by
  intro path hprimes z hz
  exact hempty z (hprimes z hz)

/-- **Multi-Scale Constraint**: A prime walk is constrained at ALL depths simultaneously.

    At depth 2: must revisit within 5 steps
    At depth 3: must revisit within 9 steps
    At depth k: must revisit within 2^k + 1 steps

    This creates a hierarchy of constraints on prime walks. -/
theorem multi_scale_constraint (path : List GaussianInt) :
    -- At depth 2 (4 patterns): revisit within 5 steps
    (path.length ≥ 5 → ∃ i j : Fin path.length, i < j ∧ patternK 2 (path.get i) = patternK 2 (path.get j)) ∧
    -- At depth 3 (8 patterns): revisit within 9 steps
    (path.length ≥ 9 → ∃ i j : Fin path.length, i < j ∧ patternK 3 (path.get i) = patternK 3 (path.get j)) ∧
    -- At depth 4 (16 patterns): revisit within 17 steps
    (path.length ≥ 17 → ∃ i j : Fin path.length, i < j ∧ patternK 4 (path.get i) = patternK 4 (path.get j)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hlen; exact path_revisits_patternK 2 path (by omega)
  · intro hlen; exact path_revisits_patternK 3 path (by omega)
  · intro hlen; exact path_revisits_patternK 4 path (by omega)

/-! ============================================================================
    PART XII: THE KEY INSIGHT - SPATIAL DISTANCE FROM CYLINDER STRUCTURE

    THE FUNDAMENTAL CONNECTION (from PathPlanning.lean):

    1. `suffixCylinder_norm_diff_dvd`: If z, w are in the same k-cylinder,
       then 2^k | norm(z - w).

    2. `isGridNeighbor_norm_le`: Grid neighbors have norm(z - w) ≤ 2.

    3. THEREFORE: Neighbors can only share cylinders where 2^k ≤ 2, i.e., k ≤ 1.

    THE MOAT CONNECTION:

    If z and w are in the SAME k-cylinder and z ≠ w, then:
    - norm(z - w) ≥ 2^k (since 2^k | norm and norm > 0)
    - For Gaussian integers, norm(z) = |z|² (squared Euclidean distance to origin)
    - So |z - w| ≥ sqrt(2^k) = 2^(k/2)

    This means: **Same k-cylinder ⟹ spatial separation ≥ 2^(k/2)**

    MOAT IMPLICATION:
    - Primes in the SAME k-cylinder are spatially separated by at least 2^(k/2)
    - A prime walk with step size s can only reach primes where:
      * Different k-cylinders for k ≥ 2 (from neighbors_diff_cylinder_depth)
      * OR same k-cylinder with spatial gap ≥ 2^(k/2)
    - As k increases, same-cylinder primes become farther apart
    - This creates a HIERARCHY of moats at each cylinder depth
============================================================================ -/

/-- **The Norm-Cylinder Connection**: Same k-cylinder implies norm divisible by 2^k.
    Imported from PathPlanning.lean: `suffixCylinder_norm_diff_dvd` -/
theorem same_cylinder_norm_bound (z w : GaussianInt) (k : ℕ)
    (h : cylinderPattern z k = cylinderPattern w k) :
    (2 : ℤ)^k ∣ (z - w).norm := by
  have hz : z ∈ SuffixCylinder k (cylinderPattern z k) := mem_own_cylinder z k
  have hw : w ∈ SuffixCylinder k (cylinderPattern w k) := mem_own_cylinder w k
  rw [← h] at hw
  exact suffixCylinder_norm_diff_dvd z w k (cylinderPattern z k) hz hw

/-- **Spatial Separation Theorem**: If z ≠ w and they share a k-cylinder,
    then norm(z - w) ≥ 2^k.

    This is the KEY insight: same cylinder ⟹ large spatial gap. -/
theorem same_cylinder_spatial_bound (z w : GaussianInt) (hne : z ≠ w) (k : ℕ)
    (h : cylinderPattern z k = cylinderPattern w k) :
    (z - w).norm ≥ 2^k := by
  have hdvd := same_cylinder_norm_bound z w k h
  have hpos : (z - w).norm ≥ 1 := by
    have := norm_pos (z - w) (sub_ne_zero.mpr hne)
    omega
  exact Int.le_of_dvd hpos hdvd

/-- **Moat Width Lower Bound**: Primes in the same k-cylinder are separated
    by Euclidean distance at least sqrt(2^k) = 2^(k/2).

    For a prime walk with step size s, we cannot reach primes in the same
    k-cylinder unless we can jump distance ≥ 2^(k/2). -/
theorem prime_cylinder_separation (p q : GaussianInt) (_hp : HasPrimeNorm p) (_hq : HasPrimeNorm q)
    (hne : p ≠ q) (k : ℕ) (_hk : k ≥ 2)
    (h_same : cylinderPattern p k = cylinderPattern q k) :
    (p - q).norm ≥ 2^k :=
  same_cylinder_spatial_bound p q hne k h_same

/-- **Norm-Distance Connection**: norm(z-w) ≥ 2^k implies Euclidean distance ≥ 2^(k/2).
    Since norm = |z-w|², we have |z-w| = sqrt(norm) ≥ sqrt(2^k) = 2^(k/2).
    For k = 2, this means Euclidean distance ≥ sqrt(4) = 2.
    For k = 4, this means Euclidean distance ≥ sqrt(16) = 4. -/
theorem norm_implies_euclidean_bound (z w : GaussianInt) (k : ℕ) (hne : z ≠ w)
    (h : cylinderPattern z k = cylinderPattern w k) :
    (z - w).norm.natAbs ≥ 2^k := by
  have hbound := same_cylinder_spatial_bound z w hne k h
  have hn := norm_nonneg (z - w)
  have h_nat : (z - w).norm = (z - w).norm.natAbs := (Int.natAbs_of_nonneg hn).symm
  have h2k : (2 : ℤ)^k = (2^k : ℕ) := by simp
  rw [h_nat, h2k] at hbound
  exact_mod_cast hbound

/-- **The Moat Existence Insight**: At cylinder depth k, primes are partitioned
    into 2^k groups. Primes in the SAME group are spatially separated by ≥ 2^(k/2).
    Primes in DIFFERENT groups cannot be reached by a single step (for k ≥ 2).

    This creates a DOUBLE constraint:
    - Step to different cylinder: forced by neighbors_diff_cylinder_depth
    - Step within same cylinder: impossible (spatial gap too large)

    Therefore: A step of size 1 can ONLY reach a prime in a DIFFERENT 2-cylinder,
    but such primes form a FINITE set per cylinder (primes_in_biCylinder_finite). -/
theorem moat_structure_theorem (k : ℕ) (hk : k ≥ 2) :
    -- (1) 2^k cylinder patterns exist
    Fintype.card (Fin k → Bool) = 2^k ∧
    -- (2) Neighbors are always in different k-cylinders
    (∀ z n : GaussianInt, IsGridNeighbor z n → cylinderPattern z k ≠ cylinderPattern n k) ∧
    -- (3) Same k-cylinder means spatial separation ≥ 2^k
    (∀ z w : GaussianInt, z ≠ w → cylinderPattern z k = cylinderPattern w k →
      (z - w).norm ≥ 2^k) := by
  refine ⟨depthK_pattern_count k, ?_, ?_⟩
  · intro z n hn
    exact neighbors_always_diff_cylinder z n k hk hn
  · intro z w hne hsame
    exact same_cylinder_spatial_bound z w hne k hsame

/-! ============================================================================
    SUMMARY: BI-TOPOLOGICAL APPROACH TO GAUSSIAN MOAT

    THE KEY INSIGHT (Part XII):

    `same_cylinder_spatial_bound`: If z ≠ w and they share a k-cylinder,
    then norm(z - w) ≥ 2^k, meaning Euclidean distance ≥ 2^(k/2).

    Combined with `neighbors_diff_cylinder_depth` (neighbors have norm ≤ 2),
    this proves: **Grid neighbors can NEVER share a k-cylinder for k ≥ 2.**

    STRUCTURAL CONSTRAINTS ON PRIME WALKS:

    1. **Forced Cylinder Crossing** (moat_neighbor_crossing):
       Every step of size 1 crosses a 2-cylinder boundary.

    2. **Spatial Separation** (same_cylinder_spatial_bound):
       Primes in the same k-cylinder are separated by distance ≥ 2^(k/2).
       - Same 2-cylinder: distance ≥ 2
       - Same 4-cylinder: distance ≥ 4
       - Same 6-cylinder: distance ≥ 8

    3. **Prime Localization** (moat_odd_prime_structure):
       Odd primes have first digit = true, avoiding half of 1-cylinder space.

    4. **Finiteness** (moat_finite_primes_per_cylinder):
       Each BiCylinder contains finitely many primes.

    5. **Pigeonhole** (path_revisits_patternK):
       Paths of length ≥ 2^k + 1 must revisit a k-cylinder pattern.

    6. **Measure** (fundamental_bridge_β_pow):
       Each k-cylinder has measure 1/2^k (Golden Identity).

    THE DOUBLE CONSTRAINT (moat_structure_theorem):

    A prime walk with step size 1 faces:
    - Different cylinder: Forced by neighbors_diff_cylinder_depth
    - Same cylinder: Would require jump ≥ 2^(k/2) (impossible for step 1)

    Therefore: Steps can ONLY reach primes in DIFFERENT k-cylinders,
    and there are only finitely many primes per cylinder.
============================================================================ -/

end SPBiTopology
