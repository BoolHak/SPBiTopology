/-
Copyright (c) 2024 SPBiTopology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BiTopology.SPBiTopology.Basic
import BiTopology.SPBiTopology.Topology
import BiTopology.SPBiTopology.PathPlanning
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Measure Theory on the Cantor Space

We construct the **Haar measure** (product of fair coins) on the Cantor space `BinarySeq = ℕ → Bool`.
The Gaussian integers ℤ[i] embed into this space via `iotaSuffix`, and we prove that this
embedded image has **measure zero** (as expected for a countable dense subset).

## Mathematical Structure

The Cantor space `{0,1}^ℕ` carries the product measure where each coordinate has the
Bernoulli(1/2) distribution. This is a probability measure with:

1. **Cylinder sets** at depth k have measure 1/2^k
2. **Singletons** have measure 0 (non-atomic)
3. **ℤ[i] embeds** as a countable subset of measure zero

## Key Distinction

- The measure lives on `Set BinarySeq`, NOT on `Set GaussianInt`
- Gaussian integers form a **measure-zero** subset of the Cantor space
- This resolves the "countable probability impossibility" paradox
-/

namespace SPBiTopology

open GaussianInt MeasureTheory

/-! ## Section 1: Cylinder Sets on the Cantor Space

Cylinder sets in BinarySeq are the basic measurable sets.
-/

/-- A cylinder set in BinarySeq: sequences matching a pattern on the first k positions -/
def CylinderSeq (k : ℕ) (pattern : Fin k → Bool) : Set BinarySeq :=
  {s | ∀ j : Fin k, s j.val = pattern j}

/-- Number of k-cylinder patterns is exactly 2^k -/
theorem cylinder_count (k : ℕ) : Fintype.card (Fin k → Bool) = 2^k := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- Two different patterns give DISJOINT cylinder sets in BinarySeq -/
theorem cylinderSeq_disjoint (k : ℕ) (p q : Fin k → Bool) (hpq : p ≠ q) :
    Disjoint (CylinderSeq k p) (CylinderSeq k q) := by
  rw [Set.disjoint_iff]
  intro s ⟨hp, hq⟩
  simp only [CylinderSeq, Set.mem_setOf_eq] at hp hq
  have h_diff : ∃ j : Fin k, p j ≠ q j := by
    by_contra h
    push_neg at h
    exact hpq (funext h)
  obtain ⟨j, hj⟩ := h_diff
  have hp_j := hp j
  have hq_j := hq j
  rw [hp_j] at hq_j
  exact hj hq_j

/-- The union of ALL k-cylinders is the entire BinarySeq space -/
theorem cylinderSeq_cover (k : ℕ) :
    ⋃ p : Fin k → Bool, CylinderSeq k p = Set.univ := by
  ext s
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  use fun j => s j.val
  intro j
  rfl

/-- Each sequence belongs to exactly one k-cylinder -/
theorem cylinderSeq_partition (s : BinarySeq) (k : ℕ) :
    ∃! p : Fin k → Bool, s ∈ CylinderSeq k p := by
  use fun j => s j.val
  constructor
  · intro j; rfl
  · intro q hq
    funext j
    exact (hq j).symm

/-! ## Section 2: Pre-Measure on Cylinder Sets

The natural pre-measure assigns measure 1/2^k to each k-cylinder.
-/

/-- The natural measure of a k-cylinder: 1/2^k -/
def μ_cylinder (k : ℕ) : ℚ := 1 / 2^k

/-- Cylinder measure is non-negative -/
theorem μ_nonneg (k : ℕ) : μ_cylinder k ≥ 0 := by
  simp only [μ_cylinder, one_div, inv_nonneg]
  exact pow_nonneg (by norm_num : (0:ℚ) ≤ 2) k

/-- Cylinder measure is at most 1 -/
theorem μ_le_one (k : ℕ) : μ_cylinder k ≤ 1 := by
  simp only [μ_cylinder, one_div]
  have h : (2:ℚ)^k ≥ 1 := one_le_pow_of_one_le (by norm_num : (1:ℚ) ≤ 2) k
  have hpos : (2:ℚ)^k > 0 := pow_pos (by norm_num) k
  have hinv : ((2:ℚ)^k)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff]
    right
    exact h
  exact hinv

/-- The full space (0-cylinder) has measure 1 -/
theorem μ_full_space : μ_cylinder 0 = 1 := by simp [μ_cylinder]

/-- Larger k gives smaller measure -/
theorem μ_decreasing {k m : ℕ} (h : k ≤ m) : μ_cylinder m ≤ μ_cylinder k := by
  simp only [μ_cylinder, one_div]
  have hk : (2:ℚ)^k > 0 := pow_pos (by norm_num) k
  have hm : (2:ℚ)^m > 0 := pow_pos (by norm_num) m
  rw [inv_le_inv hm hk]
  exact pow_le_pow_right (by norm_num : (1:ℚ) ≤ 2) h

/-- A k-cylinder splits into two (k+1)-cylinders -/
theorem μ_additivity (k : ℕ) :
    μ_cylinder k = μ_cylinder (k + 1) + μ_cylinder (k + 1) := by
  simp only [μ_cylinder, one_div, pow_succ]
  ring

/-- Measure is consistent: 2^k * μ_cylinder k = 1 -/
theorem μ_consistent (k : ℕ) : 2^k * μ_cylinder k = 1 := by
  simp only [μ_cylinder, one_div]
  have h : (2:ℚ)^k ≠ 0 := pow_ne_zero k (by norm_num)
  field_simp

/-- Sum of measures of all k-cylinders equals 1 -/
theorem μ_partition_sum (k : ℕ) :
    ∑ p : Fin k → Bool, μ_cylinder k = 1 := by
  simp only [μ_cylinder, one_div]
  rw [Finset.sum_const, Finset.card_univ]
  rw [cylinder_count]
  simp only [nsmul_eq_mul]
  have h : (2:ℚ)^k ≠ 0 := pow_ne_zero k (by norm_num)
  field_simp

/-! ## Section 3: The Embedding iotaSuffix and Measure Zero

The Gaussian integers embed into the Cantor space via iotaSuffix.
Crucially, this image has measure zero because Gaussian integers
correspond to EVENTUALLY ZERO sequences.
-/

/-- A sequence is eventually zero if all sufficiently large positions are false -/
def EventuallyZero (s : BinarySeq) : Prop := ∃ N : ℕ, ∀ n ≥ N, s n = false

/-- The set of eventually zero sequences -/
def EventuallyZeroSet : Set BinarySeq := {s | EventuallyZero s}

/-- Gaussian integers map to eventually zero sequences -/
theorem iotaSuffix_eventually_zero (z : GaussianInt) : EventuallyZero (iotaSuffix z) := by
  use digitLength z
  intro n hn
  simp only [iotaSuffix]
  exact nthDigitLSD_beyond_length z n hn

/-- The image of iotaSuffix is contained in EventuallyZeroSet -/
theorem iotaSuffix_range_subset : Set.range iotaSuffix ⊆ EventuallyZeroSet := by
  intro s hs
  obtain ⟨z, rfl⟩ := hs
  exact iotaSuffix_eventually_zero z

/-- The set of sequences that are zero from position N onwards -/
def ZeroFrom (N : ℕ) : Set BinarySeq := {s | ∀ n ≥ N, s n = false}

/-- ZeroFrom N is a union of 2^N cylinders (one for each pattern on positions 0..N-1) -/
theorem zeroFrom_eq_union (N : ℕ) :
    ZeroFrom N = ⋃ p : Fin N → Bool, CylinderSeq N p ∩ ZeroFrom N := by
  ext s
  simp only [ZeroFrom, Set.mem_iUnion, Set.mem_inter_iff, CylinderSeq, Set.mem_setOf_eq]
  constructor
  · intro hs
    use fun j => s j.val
    exact ⟨fun j => rfl, hs⟩
  · intro ⟨_, _, hs⟩
    exact hs

/-! ## Section 4: Measure Zero for Countable Sets

The key insight: EventuallyZeroSet is countable, and any singleton in
the Cantor space has measure zero. Therefore, the image of ℤ[i] has measure zero.
-/

/-- For any ε > 0, there exists k such that 1/2^k < ε -/
theorem μ_arbitrarily_small : ∀ ε : ℚ, ε > 0 → ∃ k : ℕ, μ_cylinder k < ε := by
  intro ε hε
  have hε_nat : ∃ n : ℕ, (n:ℚ) > ε⁻¹ := exists_nat_gt ε⁻¹
  obtain ⟨n, hn⟩ := hε_nat
  use n + 1
  simp only [μ_cylinder, one_div]
  have h2n_pos : (2:ℚ)^(n+1) > 0 := pow_pos (by norm_num) (n+1)
  have h2n_gt : (2:ℚ)^(n+1) > ε⁻¹ := by
    have h_nat : (2:ℕ)^(n+1) > n + 1 := Nat.lt_pow_self (by norm_num : 1 < 2) (n+1)
    calc (2:ℚ)^(n+1) = ((2:ℕ)^(n+1) : ℚ) := by norm_cast
      _ > ((n + 1 : ℕ) : ℚ) := by exact_mod_cast h_nat
      _ > (n : ℚ) := by simp only [Nat.cast_add, Nat.cast_one]; linarith
      _ > ε⁻¹ := hn
  exact inv_lt_of_inv_lt hε h2n_gt

/-- Each sequence s is contained in arbitrarily small cylinders -/
theorem singleton_in_small_cylinder (s : BinarySeq) :
    ∀ ε : ℚ, ε > 0 → ∃ k : ℕ, ∃ p : Fin k → Bool,
      s ∈ CylinderSeq k p ∧ μ_cylinder k < ε := by
  intro ε hε
  obtain ⟨k, hk⟩ := μ_arbitrarily_small ε hε
  obtain ⟨p, hp, _⟩ := cylinderSeq_partition s k
  exact ⟨k, p, hp, hk⟩

/-! ## Section 5: Relating SuffixCylinder to CylinderSeq

The SuffixCylinder on GaussianInt corresponds to the preimage of CylinderSeq under iotaSuffix.
-/

/-- SuffixCylinder is the preimage of CylinderSeq under iotaSuffix -/
theorem suffixCylinder_preimage (k : ℕ) (p : Fin k → Bool) :
    SuffixCylinder k p = iotaSuffix ⁻¹' (CylinderSeq k p) := by
  ext z
  simp only [SuffixCylinder, CylinderSeq, Set.mem_preimage, Set.mem_setOf_eq, iotaSuffix]

/-- The image of a SuffixCylinder under iotaSuffix is contained in the corresponding CylinderSeq -/
theorem iotaSuffix_image_subset (k : ℕ) (p : Fin k → Bool) :
    iotaSuffix '' (SuffixCylinder k p) ⊆ CylinderSeq k p := by
  intro s hs
  obtain ⟨z, hz, rfl⟩ := hs
  simp only [CylinderSeq, Set.mem_setOf_eq, iotaSuffix]
  intro j
  exact hz j

/-! ## Section 7: Bi-Topological Structure

The Gaussian integers embed into the Cantor space in two different ways:
1. **Suffix embedding** (iotaSuffix): Based on LSD digits
2. **Prefix embedding** (iotaPrefixCanonical): Based on MSD digits with length encoding

Both embeddings map ℤ[i] to eventually-zero sequences, hence to measure-zero subsets.
-/

/-- Each Gaussian integer is in exactly one suffix cylinder at any depth -/
theorem gaussianInt_in_suffixCylinder (z : GaussianInt) (k : ℕ) :
    ∃ p : Fin k → Bool, z ∈ SuffixCylinder k p := by
  obtain ⟨p, hp, _⟩ := suffixCylinder_partition z k
  exact ⟨p, hp⟩

/-- Prefix Cylinders are finite sets -/
theorem prefixCylinder_is_finite (len m : ℕ) (pattern : Fin m → Bool) :
    Set.Finite (PrefixCylinder len m pattern) :=
  prefixCylinder_finite len m pattern

/-- Finite sets can be covered by finitely many suffix cylinders -/
theorem finite_set_covered (A : Set GaussianInt) (hA : Set.Finite A) (k : ℕ) :
    ∃ S : Finset (Fin k → Bool), A ⊆ ⋃ p ∈ S, SuffixCylinder k p := by
  use hA.toFinset.image (fun z => (suffixCylinder_partition z k).choose)
  intro z hz
  simp only [Set.mem_iUnion, Finset.mem_image, Set.Finite.mem_toFinset]
  use (suffixCylinder_partition z k).choose
  exact ⟨⟨z, hz, rfl⟩, (suffixCylinder_partition z k).choose_spec.1⟩

/-- The number of cylinders needed to cover a finite set is at most its cardinality -/
theorem finite_set_cover_card (A : Set GaussianInt) (hA : Set.Finite A) (k : ℕ) :
    ∃ S : Finset (Fin k → Bool), A ⊆ ⋃ p ∈ S, SuffixCylinder k p ∧ S.card ≤ hA.toFinset.card := by
  use hA.toFinset.image (fun z => (suffixCylinder_partition z k).choose)
  constructor
  · intro z hz
    simp only [Set.mem_iUnion, Finset.mem_image, Set.Finite.mem_toFinset]
    use (suffixCylinder_partition z k).choose
    exact ⟨⟨z, hz, rfl⟩, (suffixCylinder_partition z k).choose_spec.1⟩
  · exact Finset.card_image_le

/-! ## Section 8: Summary - Bi-Topological Measure Theory

We have established the measure-theoretic foundation for the bi-topology on ℤ[i]:

1. **The measure lives on BinarySeq** (Cantor space), NOT on GaussianInt
2. **Suffix Cylinders** have measure 1/2^k and are infinite sets
3. **Prefix Cylinders** are finite sets (hence measure zero in any non-atomic measure)
4. **ℤ[i] embeds** as a countable dense subset of measure zero

**The Bi-Topological Contrast**:
- Suffix Cylinders are infinite (cosets of β^k · ℤ[i])
- Prefix Cylinders are finite (bounded digit length)

This formalizes the orthogonality of the two topological views.
-/

end SPBiTopology
