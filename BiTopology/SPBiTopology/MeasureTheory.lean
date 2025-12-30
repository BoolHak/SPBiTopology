/-
Copyright (c) 2024 SPBiTopology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BiTopology.SPBiTopology.Basic
import BiTopology.SPBiTopology.Topology
import BiTopology.SPBiTopology.PathPlanning
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Measure.Count

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

open GaussianInt MeasureTheory ENNReal Set Filter

/-- The MeasurableSpace on BinarySeq = ℕ → Bool is the product σ-algebra.
    Lean synthesizes this via `MeasurableSpace.pi`. We verify it explicitly here. -/
example : MeasurableSpace BinarySeq := inferInstance

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

/-- The natural measure of a k-cylinder: 1/2^k using ENNReal for Mathlib compatibility -/
noncomputable def μ_cylinder (k : ℕ) : ℝ≥0∞ := (1 : ℝ≥0∞) / 2^k

/-- Cylinder measure is at most 1 -/
theorem μ_le_one (k : ℕ) : μ_cylinder k ≤ 1 := by
  simp only [μ_cylinder]
  have h : (1 : ℝ≥0∞) ≤ 2^k := one_le_pow_of_one_le' (by norm_num : (1 : ℝ≥0∞) ≤ 2) k
  exact ENNReal.div_le_of_le_mul (by simp [h])

/-- The full space (0-cylinder) has measure 1 -/
theorem μ_full_space : μ_cylinder 0 = 1 := by simp [μ_cylinder]

/-- Larger k gives smaller measure -/
theorem μ_decreasing {k m : ℕ} (h : k ≤ m) : μ_cylinder m ≤ μ_cylinder k := by
  simp only [μ_cylinder]
  apply ENNReal.div_le_div_left
  exact pow_le_pow_right (by norm_num : (1 : ℝ≥0∞) ≤ 2) h

/-- A k-cylinder splits into two (k+1)-cylinders -/
theorem μ_additivity (k : ℕ) :
    μ_cylinder k = μ_cylinder (k + 1) + μ_cylinder (k + 1) := by
  unfold μ_cylinder
  have h2k_ne : (2 : ℝ≥0∞)^k ≠ 0 := pow_ne_zero k (by norm_num)
  have h2k_top : (2 : ℝ≥0∞)^k ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  have h2_ne : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  rw [pow_succ, mul_comm, ENNReal.div_add_div_same]
  rw [show (1 : ℝ≥0∞) + 1 = 2 by norm_num]
  rw [ENNReal.div_eq_div_iff (mul_ne_zero h2_ne h2k_ne) (ENNReal.mul_ne_top h2_top h2k_top)
      h2k_ne h2k_top]
  ring

/-- Measure is consistent: 2^k * μ_cylinder k = 1 -/
theorem μ_consistent (k : ℕ) : (2 : ℝ≥0∞)^k * μ_cylinder k = 1 := by
  simp only [μ_cylinder]
  have h2k : (2 : ℝ≥0∞)^k ≠ 0 := pow_ne_zero k (by norm_num)
  have h2k_top : (2 : ℝ≥0∞)^k ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  rw [mul_comm, ENNReal.div_mul_cancel h2k h2k_top]

/-- Sum of measures of all k-cylinders equals 1 -/
theorem μ_partition_sum (k : ℕ) :
    ∑ _p : Fin k → Bool, μ_cylinder k = 1 := by
  rw [Finset.sum_const, Finset.card_univ, cylinder_count, nsmul_eq_mul]
  convert μ_consistent k using 1
  unfold μ_cylinder
  simp only [Nat.cast_pow, Nat.cast_ofNat]

/-! ## Section 2b: Formal Measure Theory

We establish the measure-theoretic properties rigorously:
1. Prove CylinderSeq sets are measurable in the product σ-algebra
2. Define the Bernoulli(1/2) measure on Bool
3. Prove singletons are intersections of nested cylinders with measure → 0
4. PROVE (not assume) that singletons have measure 0 in any consistent measure
-/

/-- CylinderSeq k p is measurable in the product σ-algebra on ℕ → Bool.
    It is the preimage of a singleton under the restriction to Fin k. -/
theorem cylinderSeq_measurableSet (k : ℕ) (p : Fin k → Bool) :
    MeasurableSet (CylinderSeq k p) := by
  -- CylinderSeq k p = {s | ∀ j : Fin k, s j.val = p j}
  -- This is the preimage of {p} under the projection to Fin k → Bool
  have h_eq : CylinderSeq k p = (fun s : BinarySeq => fun j : Fin k => s j.val) ⁻¹' {p} := by
    ext s
    simp only [CylinderSeq, mem_preimage, mem_singleton_iff, mem_setOf_eq]
    constructor
    · intro h; ext j; exact h j
    · intro h j; exact congrFun h j
  rw [h_eq]
  apply MeasurableSet.preimage
  · exact MeasurableSet.singleton p
  · exact measurable_pi_lambda _ (fun j => measurable_pi_apply j.val)

/-- The fair coin measure on Bool: P(true) = P(false) = 1/2 -/
noncomputable def bernoulliHalf : Measure Bool :=
  (1/2 : ℝ≥0∞) • Measure.dirac true + (1/2 : ℝ≥0∞) • Measure.dirac false

/-- bernoulliHalf is a probability measure -/
theorem bernoulliHalf_isProbability : bernoulliHalf Set.univ = 1 := by
  simp only [bernoulliHalf, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
  rw [show (1 : ℝ≥0∞) / 2 + 1 / 2 = 1 by
    rw [ENNReal.div_add_div_same, show (1 : ℝ≥0∞) + 1 = 2 by norm_num, ENNReal.div_self]
    · norm_num
    · exact ENNReal.two_ne_top]

/-- **Key Lemma**: A singleton {s} is the intersection of all cylinders containing s.
    {s} = ⋂ k, CylinderSeq k (s|_k) -/
theorem singleton_eq_iInter_cylinders (s : BinarySeq) :
    {s} = ⋂ k : ℕ, CylinderSeq k (fun j => s j.val) := by
  ext t
  simp only [mem_singleton_iff, mem_iInter, CylinderSeq, mem_setOf_eq]
  constructor
  · intro h; rw [h]; intro k j; rfl
  · intro h
    ext n
    -- For any n, t n = s n because t ∈ CylinderSeq (n+1) (s|_{n+1})
    have := h (n + 1) ⟨n, Nat.lt_succ_self n⟩
    simp only [Fin.val_mk] at this
    exact this

/-- **Critical Theorem**: Stated here, proved in Section 7 after μ_arbitrarily_small.
    In any measure μ where μ(CylinderSeq k p) = μ_cylinder k, singletons have measure 0. -/
theorem singleton_measure_zero_of_cylinder_measure
    (μ : Measure BinarySeq)
    (h_cylinder : ∀ k p, μ (CylinderSeq k p) = μ_cylinder k)
    (s : BinarySeq) : μ {s} = 0 := by
  -- μ({s}) ≤ μ(CylinderSeq k (s|_k)) = μ_cylinder k for all k
  have h_bound : ∀ k, μ {s} ≤ μ_cylinder k := by
    intro k
    calc μ {s}
      ≤ μ (CylinderSeq k (fun j => s j.val)) := by
          apply measure_mono
          intro t ht
          simp only [mem_singleton_iff] at ht
          rw [ht]
          intro j; rfl
      _ = μ_cylinder k := h_cylinder k _
  -- Since μ_cylinder k = 1/2^k → 0, for any ε > 0 we can find k with μ_cylinder k < ε
  -- So μ {s} ≤ μ_cylinder k < ε for all ε > 0, hence μ {s} = 0
  apply le_antisymm _ (zero_le _)
  by_contra h_ne
  push_neg at h_ne
  have h_pos : 0 < μ {s} := h_ne
  -- Get k such that μ_cylinder k < μ {s}
  have h2k_ne : ∀ k, (2 : ℝ≥0∞)^k ≠ 0 := fun k => pow_ne_zero k (by norm_num)
  have h2k_top : ∀ k, (2 : ℝ≥0∞)^k ≠ ⊤ := fun k => ENNReal.pow_ne_top (by norm_num)
  -- Use Archimedean property: ∃ k, μ {s}⁻¹ < 2^k
  have h_ne_top : μ {s} ≠ ⊤ := by
    intro h_top
    have := h_bound 0
    simp only [h_top, μ_cylinder, pow_zero, div_one] at this
    exact ENNReal.top_ne_one (le_antisymm this le_top)
  obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt (ENNReal.inv_ne_top.mpr h_pos.ne')
  -- Prove k ≤ 2^k separately to avoid context pollution in induction
  have h_nat_le_pow : ∀ n : ℕ, (n : ℝ≥0∞) ≤ 2^n := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      calc ((m + 1 : ℕ) : ℝ≥0∞) = m + 1 := by norm_cast
        _ ≤ 2^m + 1 := add_le_add_right ih 1
        _ ≤ 2^m + 2^m := add_le_add_left (one_le_pow_of_one_le' (by norm_num : (1 : ℝ≥0∞) ≤ 2) m) _
        _ = 2^(m + 1) := by rw [← two_mul, pow_succ]; ring
  have h_k_le_2k : (k : ℝ≥0∞) ≤ 2^k := h_nat_le_pow k
  have h_inv_lt : (μ {s})⁻¹ < (2 : ℝ≥0∞)^k := lt_of_lt_of_le hk h_k_le_2k
  -- This means μ_cylinder k < μ {s}
  have h_cyl_lt : μ_cylinder k < μ {s} := by
    simp only [μ_cylinder]
    rw [ENNReal.div_lt_iff (Or.inl (h2k_ne k)) (Or.inl (h2k_top k))]
    calc 1 = (μ {s}) * (μ {s})⁻¹ := (ENNReal.mul_inv_cancel h_pos.ne' h_ne_top).symm
      _ < (μ {s}) * 2^k := ENNReal.mul_lt_mul_left h_pos.ne' h_ne_top |>.mpr h_inv_lt
  -- But h_bound says μ {s} ≤ μ_cylinder k, contradiction
  exact not_lt.mpr (h_bound k) h_cyl_lt

/-- **Corollary**: Any measure consistent with cylinder measures is non-atomic (NoAtoms). -/
theorem noAtoms_of_cylinder_measure
    (μ : Measure BinarySeq)
    (h_cylinder : ∀ k p, μ (CylinderSeq k p) = μ_cylinder k) : NoAtoms μ :=
  ⟨fun s => singleton_measure_zero_of_cylinder_measure μ h_cylinder s⟩

/-- Singletons in BinarySeq are measurable in the product σ-algebra -/
theorem singleton_measurableSet (s : BinarySeq) : MeasurableSet ({s} : Set BinarySeq) := by
  rw [singleton_eq_iInter_cylinders s]
  apply MeasurableSet.iInter
  intro k
  exact cylinderSeq_measurableSet k _

/-! ### The Cantor Measure (Product of Fair Coins)

The **Cantor measure** μ_cantor on BinarySeq = ℕ → Bool is the infinite product of
Bernoulli(1/2) measures. By the Kolmogorov extension theorem, there exists a unique
probability measure satisfying μ_cantor(CylinderSeq k p) = 1/2^k.

**Note on Mathlib Version**: The full construction via `Measure.infinitePi` requires
Mathlib features not available in v4.12.0. We assert existence (Kolmogorov) and prove
all properties hold for the chosen measure.
-/

/-- Specification: A measure is a "Cantor measure" if it assigns 1/2^k to each k-cylinder -/
def IsCantorMeasure (μ : Measure BinarySeq) : Prop :=
  ∀ k p, μ (CylinderSeq k p) = μ_cylinder k

/-- **Kolmogorov Extension Theorem**: The infinite product of Bernoulli(1/2) measures exists.

This is a standard result in measure theory: given a consistent family of finite-dimensional
distributions (here: uniform on {0,1}^k for each k), there exists a unique probability measure
on the infinite product space extending them.

**Implementation Note**: The constructive proof requires `Measure.infinitePi` from
`Mathlib.Probability.ProductMeasure`, which is not available in Mathlib v4.12.0.
When upgrading Mathlib, replace this axiom with:
```
noncomputable def μ_cantor : Measure BinarySeq :=
  Measure.infinitePi (fun _ : ℕ => bernoulliHalf)
```
and prove `IsCantorMeasure μ_cantor` using `Measure.infinitePi_pi_apply`.

The axiom is sound: it asserts a well-known existence result, not a novel claim. -/
axiom cantor_measure_exists : ∃ μ : Measure BinarySeq, IsCantorMeasure μ

/-- The canonical Cantor measure on BinarySeq -/
noncomputable def μ_cantor : Measure BinarySeq := Classical.choose cantor_measure_exists

/-- μ_cantor satisfies the cylinder measure property -/
theorem μ_cantor_cylinder : IsCantorMeasure μ_cantor :=
  Classical.choose_spec cantor_measure_exists

/-- μ_cantor is non-atomic (singletons have measure 0) -/
instance μ_cantor_noAtoms : NoAtoms μ_cantor :=
  noAtoms_of_cylinder_measure μ_cantor μ_cantor_cylinder

/-- μ_cantor gives measure 1/2^k to each cylinder -/
theorem μ_cantor_cylinder_eq (k : ℕ) (p : Fin k → Bool) :
    μ_cantor (CylinderSeq k p) = μ_cylinder k :=
  μ_cantor_cylinder k p

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

/-! ## Section 4: Relating SuffixCylinder to CylinderSeq

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

/-! ## Section 6: Bi-Topological Structure

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

/-! ## Section 7: Countable Subadditivity and Measure Zero

We prove that the EventuallyZeroSet has measure zero by showing:
1. ZeroFrom N has at most 2^N elements (one for each pattern on positions [0, N-1])
2. EventuallyZeroSet = ⋃ N, ZeroFrom N is a countable union
3. Each element of ZeroFrom N is in exactly one N-cylinder
-/

/-- ZeroFrom N is exactly the set of sequences that are zero from position N onwards -/
theorem zeroFrom_mem_iff (N : ℕ) (s : BinarySeq) :
    s ∈ ZeroFrom N ↔ ∀ n ≥ N, s n = false := Iff.rfl

/-- EventuallyZeroSet is the countable union of ZeroFrom N -/
theorem eventuallyZeroSet_eq_iUnion :
    EventuallyZeroSet = ⋃ N : ℕ, ZeroFrom N := by
  ext s
  simp only [EventuallyZeroSet, EventuallyZero, ZeroFrom, Set.mem_setOf_eq, Set.mem_iUnion]

/-- Each CylinderSeq N p ∩ ZeroFrom N contains at most one sequence -/
theorem cylinderSeq_inter_zeroFrom_subsingleton (N : ℕ) (p : Fin N → Bool) :
    Set.Subsingleton (CylinderSeq N p ∩ ZeroFrom N) := by
  intro s hs t ht
  funext n
  by_cases hn : n < N
  · have hs_cyl : s ∈ CylinderSeq N p := hs.1
    have ht_cyl : t ∈ CylinderSeq N p := ht.1
    have hs_n := hs_cyl ⟨n, hn⟩
    have ht_n := ht_cyl ⟨n, hn⟩
    simp only [CylinderSeq, Set.mem_setOf_eq] at hs_n ht_n
    rw [hs_n, ht_n]
  · have hs_zero : s ∈ ZeroFrom N := hs.2
    have ht_zero : t ∈ ZeroFrom N := ht.2
    simp only [ZeroFrom, Set.mem_setOf_eq] at hs_zero ht_zero
    have hn' : n ≥ N := Nat.not_lt.mp hn
    rw [hs_zero n hn', ht_zero n hn']

/-- ZeroFrom N is a finite set with at most 2^N elements -/
theorem zeroFrom_finite (N : ℕ) : Set.Finite (ZeroFrom N) := by
  have h_sub : ZeroFrom N ⊆ ⋃ p : Fin N → Bool, (CylinderSeq N p ∩ ZeroFrom N) := by
    intro s hs
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun j => s j.val, fun _ => rfl, hs⟩
  apply Set.Finite.subset _ h_sub
  apply Set.finite_iUnion
  intro p
  exact Set.Subsingleton.finite (cylinderSeq_inter_zeroFrom_subsingleton N p)

/-- ZeroFrom N is covered by cylinders of depth N -/
theorem zeroFrom_cylinder_cover (N : ℕ) :
    ZeroFrom N ⊆ ⋃ p : Fin N → Bool, CylinderSeq N p := by
  intro s _
  simp only [Set.mem_iUnion]
  use fun j => s j.val
  intro j
  rfl

/-- Each element of ZeroFrom N belongs to a unique cylinder -/
theorem zeroFrom_unique_cylinder (N : ℕ) (s : BinarySeq) (_hs : s ∈ ZeroFrom N) :
    ∃! p : Fin N → Bool, s ∈ CylinderSeq N p := by
  use fun j => s j.val
  constructor
  · intro j; rfl
  · intro q hq
    funext j
    exact (hq j).symm
/-- **Main Result**: EventuallyZeroSet is countable.
    Since EventuallyZeroSet = ⋃ N, ZeroFrom N and each ZeroFrom N is finite,
    EventuallyZeroSet is a countable union of finite sets, hence countable. -/
theorem eventuallyZeroSet_countable : Set.Countable EventuallyZeroSet := by
  rw [eventuallyZeroSet_eq_iUnion]
  apply Set.countable_iUnion
  intro N
  exact (zeroFrom_finite N).countable

/-- **Set-Theoretic Measure Zero**: EventuallyZeroSet has measure zero in any
    measure consistent with cylinder measures.

    This is the rigorous proof:
    1. We PROVE (not assume) that consistent measures are NoAtoms via `noAtoms_of_cylinder_measure`
    2. EventuallyZeroSet is countable (proven above)
    3. By Mathlib's `Set.Countable.measure_zero`: countable + NoAtoms → measure zero -/
theorem eventuallyZeroSet_measure_zero
    (μ : Measure BinarySeq)
    (h_cylinder : ∀ k p, μ (CylinderSeq k p) = μ_cylinder k) :
    μ EventuallyZeroSet = 0 := by
  have h_noatoms : NoAtoms μ := noAtoms_of_cylinder_measure μ h_cylinder
  exact eventuallyZeroSet_countable.measure_zero μ

/-- Version with NoAtoms typeclass (for convenience when instance is available) -/
theorem eventuallyZeroSet_measure_zero' (μ : Measure BinarySeq) [NoAtoms μ] :
    μ EventuallyZeroSet = 0 :=
  eventuallyZeroSet_countable.measure_zero μ

/-- **Main Application**: The image of Gaussian integers under iotaSuffix has measure zero
    in any consistent product measure. -/
theorem gaussianInt_image_measure_zero
    (μ : Measure BinarySeq)
    (h_cylinder : ∀ k p, μ (CylinderSeq k p) = μ_cylinder k) :
    μ (Set.range iotaSuffix) = 0 := by
  apply le_antisymm _ (zero_le _)
  calc μ (Set.range iotaSuffix)
    ≤ μ EventuallyZeroSet := measure_mono iotaSuffix_range_subset
    _ = 0 := eventuallyZeroSet_measure_zero μ h_cylinder

theorem gaussianInt_image_subset_eventuallyZero :
    Set.range iotaSuffix ⊆ EventuallyZeroSet :=
  iotaSuffix_range_subset

/-! ### Concrete Results for μ_cantor

These are the "ground truth" theorems using the concrete Cantor measure.
No hypothetical measures - these are actual equalities.
-/

/-- **Concrete**: EventuallyZeroSet has measure zero in μ_cantor -/
theorem eventuallyZeroSet_μ_cantor : μ_cantor EventuallyZeroSet = 0 :=
  eventuallyZeroSet_measure_zero μ_cantor μ_cantor_cylinder

/-- **Concrete**: The image of ℤ[i] has measure zero in μ_cantor -/
theorem gaussianInt_image_μ_cantor : μ_cantor (Set.range iotaSuffix) = 0 :=
  gaussianInt_image_measure_zero μ_cantor μ_cantor_cylinder

/-- **Concrete**: Singletons have measure zero in μ_cantor -/
theorem singleton_μ_cantor (s : BinarySeq) : μ_cantor {s} = 0 :=
  singleton_measure_zero_of_cylinder_measure μ_cantor μ_cantor_cylinder s

/-! ## Section 7: Summary - Bi-Topological Measure Theory

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
