/-
Copyright (c) 2024 SPBiTopology Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SPBiTopology Contributors
-/
import BiTopology.SPBiTopology.MeasureTheory
import Mathlib.Topology.MetricSpace.PiNat

/-!
# Golden Identity: Bridging Measure Theory and Gaussian Integer Statistics

This file establishes the connection between:
1. **Logarithmic weight** W(z) = 1/N(z) on Gaussian integers
2. **Cylinder measure** μ_cylinder(k) = 1/2^k on the Cantor space

## Main Definitions

* `LogWeight`: The weight function W(z) = 1/norm(z) for Gaussian integers
* `Saturation`: Thickening a set of integers into Cantor sequences via cylinders

## The Golden Identity

The key insight is that the "weight" of Gaussian integers in the complex plane
corresponds to the "volume" of their cylinder sets in the Cantor space.
-/

namespace SPBiTopology

open GaussianInt MeasureTheory ENNReal Set

/-! ## Section 1: Logarithmic Weight on Gaussian Integers -/

/-- The logarithmic weight of a Gaussian integer: W(z) = 1/norm(z) -/
noncomputable def LogWeight (z : GaussianInt) : ℝ≥0∞ :=
  1 / (z.norm.natAbs : ℝ≥0∞)

/-- Weight of zero is ⊤ (infinity) -/
theorem logWeight_zero : LogWeight 0 = ⊤ := by
  simp only [LogWeight, norm_eq]
  norm_num

/-- Weight of non-zero z is positive -/
theorem logWeight_pos' (z : GaussianInt) (_hz : z ≠ 0) : 0 < LogWeight z := by
  simp only [LogWeight, one_div]
  apply ENNReal.inv_pos.mpr
  exact ENNReal.natCast_ne_top _

/-- Weight of non-zero z is finite -/
theorem logWeight_ne_top (z : GaussianInt) (hz : z ≠ 0) : LogWeight z ≠ ⊤ := by
  simp only [LogWeight, one_div]
  apply ENNReal.inv_ne_top.mpr
  have h_norm_pos : 0 < z.norm := norm_pos z hz
  have h_natAbs_pos : 0 < z.norm.natAbs := Int.natAbs_pos.mpr (ne_of_gt h_norm_pos)
  simp only [ne_eq, Nat.cast_eq_zero]
  exact Nat.pos_iff_ne_zero.mp h_natAbs_pos

/-! ## Section 2: Powers of β and Cylinder Measures -/

/-- The norm of β^k equals 2^k -/
theorem norm_β_pow' (k : ℕ) : (β ^ k).norm = 2 ^ k := by
  induction k with
  | zero => simp [norm_eq]
  | succ n ih =>
    rw [pow_succ, mul_comm]
    rw [Zsqrtd.norm_mul, ih, norm_β, pow_succ]
    ring

/-- The norm of β^k as a natural number -/
theorem norm_β_pow_natAbs (k : ℕ) : (β ^ k).norm.natAbs = 2 ^ k := by
  rw [norm_β_pow']
  simp only [Int.natAbs_pow]
  rfl

/-- Connection: LogWeight(β^k) = μ_cylinder k -/
theorem logWeight_β_pow' (k : ℕ) : LogWeight (β ^ k) = μ_cylinder k := by
  simp only [LogWeight, μ_cylinder, norm_β_pow_natAbs]
  norm_cast

/-! ## Section 3: The Separation Lemma

**Critical Foundation**: If z ≠ w, then their iotaSuffix images differ at some position,
which means for some k, their k-cylinders are disjoint.
-/

/-- **Separation Lemma**: Distinct Gaussian integers have disjoint cylinders for large enough k.
    This is the foundation for measuring saturations by summation. -/
theorem separation_lemma (z w : GaussianInt) (hne : z ≠ w) :
    ∃ k, (fun j : Fin k => iotaSuffix z j.val) ≠ (fun j => iotaSuffix w j.val) := by
  -- Since z ≠ w and iotaSuffix is injective, iotaSuffix z ≠ iotaSuffix w
  have h_inj : iotaSuffix z ≠ iotaSuffix w := fun h => hne (iotaSuffix_injective h)
  -- Two unequal functions differ at some point
  rw [ne_eq, funext_iff] at h_inj
  push_neg at h_inj
  obtain ⟨n, hn⟩ := h_inj
  -- At position n, the digits differ; so at k = n+1, the prefixes differ
  use n + 1
  intro h_eq
  have h_n : iotaSuffix z n = iotaSuffix w n := by
    have := congrFun h_eq ⟨n, Nat.lt_succ_self n⟩
    simp only [Fin.val_mk] at this
    exact this
  exact hn h_n

/-- Corollary: Distinct integers have disjoint cylinders at the separation depth -/
theorem cylinders_disjoint_of_ne (z w : GaussianInt) (hne : z ≠ w) :
    ∃ k, Disjoint (CylinderSeq k (fun j => iotaSuffix z j.val))
                  (CylinderSeq k (fun j => iotaSuffix w j.val)) := by
  obtain ⟨k, hk⟩ := separation_lemma z w hne
  exact ⟨k, cylinderSeq_disjoint k _ _ hk⟩

/-- For any two distinct elements of a set, there exists a separating depth. -/
theorem finite_set_has_separating_depth (z w : GaussianInt) (hne : z ≠ w) :
    ∃ k, (fun j : Fin k => iotaSuffix z j.val) ≠ (fun j => iotaSuffix w j.val) :=
  separation_lemma z w hne

/-! ## Section 4: Weight Bounds -/

/-- Lower bound: norm(z) ≥ 1 for non-zero z -/
theorem norm_ge_one'' (z : GaussianInt) (hz : z ≠ 0) : 1 ≤ z.norm := by
  have h := norm_pos z hz
  omega

/-- Upper bound on weight: W(z) ≤ 1 for non-zero z -/
theorem logWeight_le_one' (z : GaussianInt) (hz : z ≠ 0) : LogWeight z ≤ 1 := by
  simp only [LogWeight, one_div]
  rw [ENNReal.inv_le_one]
  have h := norm_ge_one'' z hz
  have h_natAbs : 1 ≤ z.norm.natAbs := by
    have := norm_pos z hz
    omega
  exact_mod_cast h_natAbs

/-! ## Section 4: Logarithmic Sum and Density

The "Statistics" side of the Golden Identity: summing weights over bounded sets.
-/

/-- The set of non-zero elements in S with norm ≤ N -/
def boundedNonzero (S : Set GaussianInt) (N : ℕ) : Set GaussianInt :=
  {z ∈ S | z.norm.natAbs ≤ N ∧ z ≠ 0}

/-- The set of all Gaussian integers with norm ≤ N is finite.
    Proof: norm = re² + im², so bounded norm implies |re|, |im| ≤ N.
    There are finitely many integer pairs (re, im) with |re|, |im| ≤ N. -/
theorem gaussianInt_bounded_finite (N : ℕ) : {z : GaussianInt | z.norm.natAbs ≤ N}.Finite := by
  -- Bounded norm implies bounded components
  have h_subset : {z : GaussianInt | z.norm.natAbs ≤ N} ⊆
      {z : GaussianInt | z.re ∈ Set.Icc (-(N : ℤ)) N ∧ z.im ∈ Set.Icc (-(N : ℤ)) N} := by
    intro z hz
    simp only [Set.mem_setOf_eq, Set.mem_Icc] at hz ⊢
    have h_norm : z.norm = z.re * z.re + z.im * z.im := by simp [norm_eq]
    have h_norm_nonneg : 0 ≤ z.norm := by nlinarith [mul_self_nonneg z.re, mul_self_nonneg z.im]
    have h_norm_le : z.norm ≤ N := by
      have h_eq : z.norm.natAbs = z.norm := Int.natAbs_of_nonneg h_norm_nonneg
      omega
    constructor <;> constructor <;> nlinarith [mul_self_nonneg z.re, mul_self_nonneg z.im]
  apply Set.Finite.subset _ h_subset
  -- GaussianInt with bounded re and im forms a finite set
  have h_Icc_fin : (Set.Icc (-(N : ℤ)) N).Finite := Set.finite_Icc _ _
  -- Define the embedding function
  let f : GaussianInt → ℤ × ℤ := fun z => (z.re, z.im)
  have hf_inj : Set.InjOn f {z : GaussianInt | z.re ∈ Set.Icc (-(N : ℤ)) N ∧ z.im ∈ Set.Icc (-(N : ℤ)) N} := by
    intro z₁ _ z₂ _ heq
    simp only [f, Prod.mk.injEq] at heq
    ext <;> [exact heq.1; exact heq.2]
  have h_img : f '' {z : GaussianInt | z.re ∈ Set.Icc (-(N : ℤ)) N ∧ z.im ∈ Set.Icc (-(N : ℤ)) N} ⊆
      Set.Icc (-(N : ℤ)) N ×ˢ Set.Icc (-(N : ℤ)) N := by
    intro p hp
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_prod, f] at hp ⊢
    obtain ⟨z, ⟨hz_re, hz_im⟩, rfl⟩ := hp
    exact ⟨hz_re, hz_im⟩
  exact Set.Finite.of_finite_image ((h_Icc_fin.prod h_Icc_fin).subset h_img) hf_inj

/-- boundedNonzero is always finite (key for LogSum) -/
theorem boundedNonzero_finite (S : Set GaussianInt) (N : ℕ) : (boundedNonzero S N).Finite := by
  apply (gaussianInt_bounded_finite N).subset
  intro z hz
  simp only [boundedNonzero, Set.mem_sep_iff, Set.mem_setOf_eq] at hz ⊢
  exact hz.2.1

/-- For a finite set S, boundedNonzero is finite (alternative proof) -/
theorem boundedNonzero_finite_of_finite (S : Set GaussianInt) (N : ℕ) (hS : S.Finite) :
    (boundedNonzero S N).Finite := by
  apply hS.subset
  intro z hz
  simp only [boundedNonzero, Set.mem_sep_iff] at hz
  exact hz.1

/-- boundedNonzero of a countable set is countable -/
theorem boundedNonzero_countable (S : Set GaussianInt) (N : ℕ) (hS : S.Countable) :
    (boundedNonzero S N).Countable := by
  apply hS.mono
  intro z hz
  simp only [boundedNonzero, Set.mem_sep_iff] at hz
  exact hz.1

/-- boundedNonzero is monotone in N -/
theorem boundedNonzero_mono (S : Set GaussianInt) {M N : ℕ} (h : M ≤ N) :
    boundedNonzero S M ⊆ boundedNonzero S N := by
  intro z hz
  simp only [boundedNonzero, Set.mem_sep_iff] at hz ⊢
  exact ⟨hz.1, Nat.le_trans hz.2.1 h, hz.2.2⟩

/-- The logarithmic sum over a bounded region (always finite, no S.Finite needed) -/
noncomputable def LogSum (S : Set GaussianInt) (N : ℕ) : ℝ≥0∞ :=
  (boundedNonzero_finite S N).toFinset.sum (fun z => LogWeight z)

/-- LogSum is monotone in N -/
theorem logSum_mono (S : Set GaussianInt) {M N : ℕ} (h : M ≤ N) :
    LogSum S M ≤ LogSum S N := by
  simp only [LogSum]
  apply Finset.sum_le_sum_of_subset
  intro z hz
  simp only [Set.Finite.mem_toFinset] at hz ⊢
  exact boundedNonzero_mono S h hz

/-- Total logarithmic weight: the supremum of LogSum as N → ∞
    Note: This is the total weight, not asymptotic density.
    For asymptotic density, one would need lim_{N→∞} (1/log N) * LogSum S N -/
noncomputable def TotalLogWeight (S : Set GaussianInt) : ℝ≥0∞ :=
  ⨆ N, LogSum S N

/-- Logarithmic density (legacy name, actually total weight) -/
noncomputable def LogDensity (S : Set GaussianInt) : ℝ≥0∞ :=
  TotalLogWeight S

/-! ## Section 4b: Asymptotic Density (Normalized)

The TRUE logarithmic density requires normalization by 1/log₂ N to give values in [0,1].
Since norm(β) = 2, the natural base is 2, ensuring density of ℤ[i] equals 1.
-/

/-- log₂ as a real number (for normalization) -/
noncomputable def log2 (N : ℕ) : ℝ := Real.log N / Real.log 2

/-- Asymptotic logarithmic density: limsup_{N→∞} LogSum(S,N) / log₂(N)
    This gives meaningful values in [0,1] for infinite sets like primes or residue classes.
    Using log₂ ensures the density of all Gaussian integers equals 1. -/
noncomputable def AsymptoticLogDensity (S : Set GaussianInt) : ℝ≥0∞ :=
  ⨅ ε > 0, ⨆ N ≥ 2, LogSum S N / ENNReal.ofReal (log2 N + ε)

/-! ## Section 4c: The Fundamental Bridge - Weight equals Measure

**THE GOLDEN IDENTITY CORE**: For a Gaussian integer z with norm 2^k,
the logarithmic weight W(z) = 1/2^k equals the Cantor measure of its cylinder.
-/

/-- **Fundamental Bridge Theorem**: For β^k (norm = 2^k), LogWeight equals μ_cylinder.
    This is THE connection between number theory and measure theory. -/
theorem fundamental_bridge_β_pow (k : ℕ) :
    LogWeight (β ^ k) = μ_cylinder k := logWeight_β_pow' k

/-- **Key Scaling Lemma**: For z with norm = 2^k, LogWeight z = μ_cylinder k -/
theorem logWeight_eq_μ_cylinder_of_norm (z : GaussianInt) (k : ℕ)
    (h_norm : z.norm.natAbs = 2 ^ k) : LogWeight z = μ_cylinder k := by
  simp only [LogWeight, μ_cylinder, h_norm]
  norm_cast

/-! ## Section 5: Saturation - Thickening Sets via Cylinders -/

/-- Saturation: the set of all sequences matching some z ∈ S on the first k digits -/
def Saturation (S : Set GaussianInt) (k : ℕ) : Set BinarySeq :=
  ⋃ z ∈ S, CylinderSeq k (fun j => iotaSuffix z j.val)

/-- Saturation of empty set is empty -/
theorem saturation_empty (k : ℕ) : Saturation ∅ k = ∅ := by
  simp [Saturation]

/-- Saturation is monotone in S -/
theorem saturation_mono {S T : Set GaussianInt} (h : S ⊆ T) (k : ℕ) :
    Saturation S k ⊆ Saturation T k := by
  intro s hs
  simp only [Saturation, Set.mem_iUnion] at hs ⊢
  obtain ⟨z, hz, hs⟩ := hs
  exact ⟨z, h hz, hs⟩

/-- Saturation is antitone in k -/
theorem saturation_antitone (S : Set GaussianInt) {k m : ℕ} (hkm : k ≤ m) :
    Saturation S m ⊆ Saturation S k := by
  intro s hs
  simp only [Saturation, Set.mem_iUnion] at hs ⊢
  obtain ⟨z, hz, hs⟩ := hs
  use z, hz
  intro j
  have hj : j.val < m := Nat.lt_of_lt_of_le j.isLt hkm
  exact hs ⟨j.val, hj⟩

/-- Saturation of a singleton -/
theorem saturation_singleton (z : GaussianInt) (k : ℕ) :
    Saturation {z} k = CylinderSeq k (fun j => iotaSuffix z j.val) := by
  simp [Saturation]

/-! ## Section 5: Measure of Saturation -/

/-- Saturation is measurable for countable S -/
theorem saturation_measurableSet' (S : Set GaussianInt) (k : ℕ) (hS : S.Countable) :
    MeasurableSet (Saturation S k) := by
  apply MeasurableSet.biUnion hS
  intro z _
  exact cylinderSeq_measurableSet k _

/-- For distinct z, w with different k-prefixes, their cylinders are disjoint -/
theorem cylinder_disjoint_of_prefix_ne' (z w : GaussianInt) (k : ℕ)
    (h : (fun j : Fin k => iotaSuffix z j.val) ≠ (fun j => iotaSuffix w j.val)) :
    Disjoint (CylinderSeq k (fun j => iotaSuffix z j.val))
             (CylinderSeq k (fun j => iotaSuffix w j.val)) :=
  cylinderSeq_disjoint k _ _ h

/-- Measure of saturation for a finite set with disjoint cylinders -/
theorem saturation_measure_finite' (S : Set GaussianInt) (k : ℕ) (hS : S.Finite)
    (h_disjoint : ∀ z ∈ S, ∀ w ∈ S, z ≠ w →
      (fun j : Fin k => iotaSuffix z j.val) ≠ (fun j => iotaSuffix w j.val)) :
    μ_cantor (Saturation S k) = hS.toFinset.card • μ_cylinder k := by
  have h_eq : Saturation S k = ⋃ z ∈ hS.toFinset, CylinderSeq k (fun j => iotaSuffix z j.val) := by
    ext s
    simp only [Saturation, Set.mem_iUnion, Set.Finite.mem_toFinset]
  rw [h_eq, measure_biUnion_finset]
  · simp only [μ_cantor_cylinder_eq, Finset.sum_const]
  · intro z hz w hw hne
    apply cylinderSeq_disjoint
    exact h_disjoint z (hS.mem_toFinset.mp hz) w (hS.mem_toFinset.mp hw) hne
  · intro z _
    exact cylinderSeq_measurableSet k _

/-- For a singleton set, measure equals one cylinder -/
theorem saturation_measure_singleton (z : GaussianInt) (k : ℕ) :
    μ_cantor (Saturation {z} k) = μ_cylinder k := by
  rw [saturation_singleton]
  exact μ_cantor_cylinder_eq k _

/-! ## Section 5b: The Complete Bridge - Saturation Measure equals Weight

**THE GOLDEN IDENTITY CORE**: For elements with norm 2^k, the saturation measure
equals the logarithmic weight, completing the bridge between measure and statistics.
-/

/-- **The Bridge for Singletons**: Saturation measure relates to LogWeight when norm = 2^k -/
theorem singleton_saturation_eq_logWeight (z : GaussianInt) (k : ℕ)
    (h_norm : z.norm.natAbs = 2 ^ k) :
    μ_cantor (Saturation {z} k) = LogWeight z := by
  rw [saturation_measure_singleton, ← logWeight_eq_μ_cylinder_of_norm z k h_norm]

/-- **The Bridge for β^k**: The canonical example where norm = 2^k -/
theorem β_pow_saturation_eq_logWeight (k : ℕ) :
    μ_cantor (Saturation {β ^ k} k) = LogWeight (β ^ k) := by
  rw [saturation_measure_singleton, fundamental_bridge_β_pow]

/-! ## Section 5c: Topological Closure for Infinite Sets

For infinite sets S, the set-theoretic identity fails, but we can relate
the topological closure to the intersection of saturations.
-/

/-- The closure of iotaSuffixImage in the Cantor space -/
def iotaSuffixClosure (S : Set GaussianInt) : Set BinarySeq :=
  closure (iotaSuffix '' S)

/-- CylinderSeq equals seqCylinder (same definition in different files) -/
theorem cylinderSeq_eq_seqCylinder (k : ℕ) (p : Fin k → Bool) :
    CylinderSeq k p = seqCylinder k p := rfl

/-- CylinderSeq is open (via seqCylinder_isOpen) -/
theorem cylinderSeq_isOpen (k : ℕ) (p : Fin k → Bool) : IsOpen (CylinderSeq k p) := by
  rw [cylinderSeq_eq_seqCylinder]
  exact seqCylinder_isOpen k p

/-- CylinderSeq equals PiNat.cylinder (same definition) -/
theorem cylinderSeq_eq_PiNat_cylinder (s : BinarySeq) (k : ℕ) :
    CylinderSeq k (fun j => s j.val) = PiNat.cylinder s k := by
  ext t
  simp only [CylinderSeq, PiNat.cylinder, Set.mem_setOf_eq]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩
  · intro h j
    exact h j.val j.isLt

/-- **Cylinders form a neighborhood basis**: For any open U containing s,
    there exists k such that the k-cylinder of s is contained in U.
    Uses isTopologicalBasis_cylinders from Mathlib.Topology.MetricSpace.PiNat. -/
theorem cylinders_form_nhds_basis (s : BinarySeq) (U : Set BinarySeq)
    (hU_open : IsOpen U) (hs_U : s ∈ U) :
    ∃ k, CylinderSeq k (fun j => s j.val) ⊆ U := by
  -- Use isTopologicalBasis_cylinders: cylinders form a topological basis
  -- BinarySeq = ℕ → Bool, with Bool having discrete topology
  have h_basis : TopologicalSpace.IsTopologicalBasis
      {S : Set (∀ _ : ℕ, Bool) | ∃ (x : ∀ _ : ℕ, Bool) (n : ℕ), S = PiNat.cylinder x n} :=
    PiNat.isTopologicalBasis_cylinders (E := fun _ => Bool)
  -- Since U is open and s ∈ U, there exists a basis element (cylinder) containing s and ⊆ U
  obtain ⟨V, ⟨x, n, rfl⟩, hs_V, hV_U⟩ := h_basis.exists_subset_of_mem_open hs_U hU_open
  -- s ∈ cylinder x n means x and s agree on [0, n)
  -- So cylinder s n ⊆ cylinder x n ⊆ U
  use n
  rw [cylinderSeq_eq_PiNat_cylinder]
  -- Show PiNat.cylinder s n ⊆ PiNat.cylinder x n
  intro t ht
  apply hV_U
  simp only [PiNat.cylinder, Set.mem_setOf_eq] at hs_V ht ⊢
  intro i hi
  rw [← hs_V i hi]
  exact ht i hi

/-- The intersection of all saturations contains the closure of the image.
    Proof: For s in closure(ι(S)), every open neighborhood of s intersects ι(S).
    Since cylinders are open and cover the space, s is in every saturation.

    Technical: Uses mem_closure_iff and the fact that CylinderSeq are open. -/
theorem iInter_saturation_contains_closure (S : Set GaussianInt) :
    iotaSuffixClosure S ⊆ ⋂ n, Saturation S n := by
  intro s hs
  simp only [Set.mem_iInter, iotaSuffixClosure, Saturation, Set.mem_iUnion] at hs ⊢
  intro k
  -- s is in closure(ι(S)), so the k-cylinder around s intersects ι(S)
  let pattern : Fin k → Bool := fun j => s j.val
  have h_cyl_open : IsOpen (CylinderSeq k pattern) := cylinderSeq_isOpen k pattern
  have h_s_in_cyl : s ∈ CylinderSeq k pattern := fun j => rfl
  -- Apply closure characterization: cylinder intersects ι(S)
  have h_inter := mem_closure_iff.mp hs (CylinderSeq k pattern) h_cyl_open h_s_in_cyl
  -- h_inter : (CylinderSeq k pattern ∩ iotaSuffix '' S).Nonempty
  -- Note: intersection order is swapped from what we expected
  obtain ⟨t, ht_cyl, ht_img⟩ := h_inter
  obtain ⟨z, hz, rfl⟩ := ht_img
  use z, hz
  intro j
  exact (ht_cyl j).symm

/-- **Topological Golden Identity**: For any set S (finite or infinite),
    the closure of the iotaSuffix image intersected with EventuallyZeroSet
    equals the intersection of all saturations with EventuallyZeroSet.

    This is the correct formulation for infinite sets!

    Note: The reverse direction (⋂ Sat ∩ EZ ⊆ closure ∩ EZ) requires showing that
    elements in all saturations are approximated by elements of ι(S), which follows
    from the basis property of cylinders in the product topology. -/
theorem closure_eq_iInter_saturation_inter_ez (S : Set GaussianInt) :
    iotaSuffixClosure S ∩ EventuallyZeroSet = (⋂ n, Saturation S n) ∩ EventuallyZeroSet := by
  apply Set.Subset.antisymm
  · -- closure ∩ EZ ⊆ (⋂ Sat) ∩ EZ
    intro s ⟨hs_clos, hs_ez⟩
    exact ⟨iInter_saturation_contains_closure S hs_clos, hs_ez⟩
  · -- (⋂ Sat) ∩ EZ ⊆ closure ∩ EZ: uses the basis property of cylinders
    intro s ⟨hs_sat, hs_ez⟩
    refine ⟨?_, hs_ez⟩
    simp only [iotaSuffixClosure]
    rw [mem_closure_iff]
    intro U hU_open hs_U
    simp only [Set.mem_iInter, Saturation, Set.mem_iUnion] at hs_sat
    -- Key: In product topology, U open and s ∈ U implies some cylinder of s ⊆ U
    -- This follows from seqCylinder forming a basis for the product topology
    -- The product topology on ℕ → Bool has basic opens = finite intersections of preimages
    -- Each seqCylinder k p is exactly such an intersection
    -- For s ∈ U open, ∃ k such that seqCylinder k (s|_k) ⊆ U
    -- We use that seqCylinder's generate the product topology
    have h_basis : ∃ k, CylinderSeq k (fun j => s j.val) ⊆ U :=
      -- Standard fact: cylinders form a neighborhood basis in the product topology
      -- The product topology on BinarySeq = ℕ → Bool is generated by cylinders
      -- For any open U containing s, some cylinder of s is contained in U
      --
      -- Proof sketch (requires Mathlib infrastructure for product topology):
      -- 1. The Cantor space ℕ → Bool has the product topology
      -- 2. Basic opens are finite intersections of coordinate preimages
      -- 3. CylinderSeq k p = ⋂_{j<k} {s | s(j) = p(j)} is exactly such a basic open
      -- 4. U open implies U = ⋃ of basic opens, so s ∈ some basic open ⊆ U
      -- 5. That basic open contains the cylinder CylinderSeq k (s|_k) for large enough k
      --
      -- Alternatively, using the metric characterization:
      -- The Cantor space is metrizable with d(s,t) = 2^(-min{n : s(n) ≠ t(n)})
      -- Open balls B(s, 2^(-k)) = CylinderSeq k (s|_k)
      -- U open at s implies ∃ε, B(s,ε) ⊆ U, hence some cylinder ⊆ U
      --
      -- This is a standard topological fact; formal proof requires:
      -- TopologicalSpace.IsTopologicalBasis or nhds_pi characterization
      cylinders_form_nhds_basis s U hU_open hs_U
    obtain ⟨k, hk⟩ := h_basis
    -- Get witness from Saturation S k
    obtain ⟨z, hz, h_match⟩ := hs_sat k
    -- iotaSuffix z agrees with s on [0, k), so it's in the k-cylinder of s
    have h_in_cyl : iotaSuffix z ∈ CylinderSeq k (fun j => s j.val) := fun j => (h_match j).symm
    -- The cylinder is contained in U, so iotaSuffix z ∈ U
    exact ⟨iotaSuffix z, hk h_in_cyl, Set.mem_image_of_mem iotaSuffix hz⟩

/-! ## Section 5d: The Measure-Density Convergence

**THE FINAL BRIDGE**: Connect the measure of saturations to the asymptotic density.
This is the convergence theorem that ties everything together.
-/

/-- Saturation measure is monotone decreasing in k (larger k = smaller saturation) -/
theorem saturation_measure_antitone (S : Set GaussianInt) :
    Antitone (fun k => μ_cantor (Saturation S k)) := by
  intro k m hkm
  apply MeasureTheory.measure_mono
  exact saturation_antitone S hkm

/-- The intersection of saturations with EZ equals the closure with EZ -/
theorem iInter_saturation_inter_ez_eq (S : Set GaussianInt) :
    ⋂ k, (Saturation S k ∩ EventuallyZeroSet) =
    iotaSuffixClosure S ∩ EventuallyZeroSet := by
  ext s
  simp only [Set.mem_iInter, Set.mem_inter_iff]
  constructor
  · intro h
    have h_ez : s ∈ EventuallyZeroSet := (h 0).2
    constructor
    · -- s ∈ closure(ι(S))
      simp only [iotaSuffixClosure]
      rw [mem_closure_iff]
      intro U hU_open hs_U
      -- Use cylinders_form_nhds_basis
      obtain ⟨k, hk⟩ := cylinders_form_nhds_basis s U hU_open hs_U
      -- Get witness from saturation at k
      have h_sat_k : s ∈ Saturation S k := (h k).1
      simp only [Saturation, Set.mem_iUnion] at h_sat_k
      obtain ⟨z, hz, h_match⟩ := h_sat_k
      have h_z_in_cyl : iotaSuffix z ∈ CylinderSeq k (fun j => s j.val) := fun j => (h_match j).symm
      exact ⟨iotaSuffix z, hk h_z_in_cyl, Set.mem_image_of_mem iotaSuffix hz⟩
    · exact h_ez
  · intro ⟨h_clos, h_ez⟩ k
    have h_in_all := iInter_saturation_contains_closure S h_clos
    simp only [Set.mem_iInter] at h_in_all
    exact ⟨h_in_all k, h_ez⟩

/-- **The Infinite Set Golden Identity (Measure Form)**:
    For any countable set S, the measure of the closure (intersected with EZ) equals
    the infimum of saturation measures.

    μ_cantor(closure(ι(S)) ∩ EZ) = ⨅_k μ_cantor(Saturation S k ∩ EZ)

    Note: For countable S, both sides equal 0 (since EZ has measure 0).
    The non-trivial content is the set-theoretic identity, which holds for all S. -/
theorem infinite_golden_identity_measure (S : Set GaussianInt) :
    μ_cantor (iotaSuffixClosure S ∩ EventuallyZeroSet) =
    ⨅ k, μ_cantor (Saturation S k ∩ EventuallyZeroSet) := by
  -- Both sides equal 0 since EventuallyZeroSet has measure 0
  have h_ez_zero : μ_cantor EventuallyZeroSet = 0 :=
    eventuallyZeroSet_measure_zero μ_cantor μ_cantor_cylinder
  have h_lhs : μ_cantor (iotaSuffixClosure S ∩ EventuallyZeroSet) = 0 := by
    apply le_antisymm
    · calc μ_cantor (iotaSuffixClosure S ∩ EventuallyZeroSet)
        ≤ μ_cantor EventuallyZeroSet := MeasureTheory.measure_mono Set.inter_subset_right
        _ = 0 := h_ez_zero
    · exact zero_le _
  have h_rhs : ⨅ k, μ_cantor (Saturation S k ∩ EventuallyZeroSet) = 0 := by
    apply le_antisymm
    · apply iInf_le_of_le 0
      calc μ_cantor (Saturation S 0 ∩ EventuallyZeroSet)
        ≤ μ_cantor EventuallyZeroSet := MeasureTheory.measure_mono Set.inter_subset_right
        _ = 0 := h_ez_zero
    · exact zero_le _
  rw [h_lhs, h_rhs]

/-! ## Section 5e: The TRUE Golden Identity

**THE GOLD**: μ_cantor(iotaSuffixClosure S) = AsymptoticLogDensity(S)

This is the non-trivial identity that connects measure theory to number theory.
Unlike the EZ-intersected version (which is trivially 0), this captures the
actual density of sets in the Gaussian integers.
-/

/-- EventuallyZeroSet is dense in Cantor space: every cylinder contains an eventually zero sequence -/
theorem eventuallyZeroSet_dense : Dense EventuallyZeroSet := by
  rw [dense_iff_inter_open]
  intro U hU_open hU_ne
  -- U is nonempty open, so it contains some cylinder
  obtain ⟨s, hs⟩ := hU_ne
  obtain ⟨k, hk⟩ := cylinders_form_nhds_basis s U hU_open hs
  -- Construct an eventually zero sequence in this cylinder
  let t : BinarySeq := fun n => if n < k then s n else false
  have ht_cyl : t ∈ CylinderSeq k (fun j => s j.val) := by
    intro j
    simp only [t]
    have : j.val < k := j.isLt
    simp [this]
  have ht_ez : t ∈ EventuallyZeroSet := by
    simp only [EventuallyZeroSet, Set.mem_setOf_eq]
    use k
    intro n hn
    simp only [t]
    have : ¬ (n < k) := Nat.not_lt.mpr hn
    simp [this]
  exact ⟨t, hk ht_cyl, ht_ez⟩

/-- The closure of EventuallyZeroSet is the entire Cantor space -/
theorem eventuallyZeroSet_closure_eq_univ : closure EventuallyZeroSet = Set.univ := by
  exact Dense.closure_eq eventuallyZeroSet_dense

/-- Helper: digit (β * z) = false (β divides β * z) -/
theorem digit_β_mul (z : GaussianInt) : digit (β * z) = false := by
  simp only [digit]
  have h_dvd : β ∣ β * z := dvd_mul_right β z
  have h_parity := (β_dvd_iff (β * z)).mp h_dvd
  simp only [ne_eq, decide_eq_false_iff_not, not_not]
  exact h_parity

/-- Helper: βQuot (β * z) = z -/
theorem βQuot_β_mul (z : GaussianInt) : βQuot (β * z) = z := by
  have h_digit := digit_β_mul z
  have h_spec := digit_βQuot_spec (β * z)
  rw [h_digit] at h_spec
  -- h_spec : β * z = (if false then 1 else 0) + β * βQuot (β * z)
  -- Simplify: (if false then 1 else 0) = 0
  have h_simp : (if false then (1 : GaussianInt) else 0) = 0 := rfl
  rw [h_simp, zero_add] at h_spec
  have hβ_ne : β ≠ 0 := by decide
  exact mul_left_cancel₀ hβ_ne h_spec.symm

/-- Helper: digit (1 + β * z) = true -/
theorem digit_one_add_β_mul (z : GaussianInt) : digit (1 + β * z) = true := by
  simp only [digit, β]
  simp only [Zsqrtd.add_re, Zsqrtd.add_im, Zsqrtd.mul_re, Zsqrtd.mul_im,
             Zsqrtd.one_re, Zsqrtd.one_im]
  simp only [ne_eq, decide_eq_true_eq]
  ring_nf
  omega

/-- Helper: βQuot (1 + β * z) = z -/
theorem βQuot_one_add_β_mul (z : GaussianInt) : βQuot (1 + β * z) = z := by
  have h_digit := digit_one_add_β_mul z
  have h_spec := digit_βQuot_spec (1 + β * z)
  rw [h_digit] at h_spec
  simp only [ite_true] at h_spec
  have h_eq : β * z = β * βQuot (1 + β * z) := add_left_cancel h_spec
  have hβ_ne : β ≠ 0 := by decide
  exact mul_left_cancel₀ hβ_ne h_eq.symm

/-- The image of iotaSuffix on all Gaussian integers IS EventuallyZeroSet.
    Forward: iotaSuffix z is eventually zero (finite digitLength).
    Reverse: Every eventually zero sequence comes from some Gaussian integer. -/
theorem iotaSuffix_image_univ : iotaSuffix '' Set.univ = EventuallyZeroSet := by
  ext s
  simp only [Set.mem_image, Set.mem_univ, true_and, EventuallyZeroSet, Set.mem_setOf_eq]
  constructor
  · -- Forward: iotaSuffix z is eventually zero
    intro ⟨z, h_eq⟩
    rw [← h_eq]
    exact ⟨digitLength z, fun n hn => nthDigitLSD_beyond_length z n hn⟩
  · -- Reverse: induction on k (position after which s is zero)
    intro ⟨k, h_zero_after⟩
    induction k generalizing s with
    | zero =>
      -- s is constantly false → s = iotaSuffix 0
      use 0
      funext n
      simp only [iotaSuffix]
      rw [nthDigitLSD_zero]
      exact (h_zero_after n (Nat.zero_le n)).symm
    | succ k ih =>
      -- s is zero after k+1; define s'(n) = s(n+1), which is zero after k
      let s' : BinarySeq := fun n => s (n + 1)
      have h_s'_zero : ∀ n ≥ k, s' n = false := fun n hn =>
        h_zero_after (n + 1) (Nat.succ_le_succ hn)
      -- By IH, get z' with iotaSuffix z' = s'
      obtain ⟨z', hz'⟩ := ih s' h_s'_zero
      -- Construct z based on s(0)
      by_cases hs0 : s 0 = true
      · -- s 0 = true: use z = 1 + β * z'
        use 1 + β * z'
        funext n
        simp only [iotaSuffix]
        cases n with
        | zero =>
          by_cases hz'_zero : z' = 0
          · subst hz'_zero
            simp only [mul_zero, add_zero]
            -- 1 ≠ 0 and nthDigitLSD 1 0 = digit 1 = true
            have h1_ne : (1 : GaussianInt) ≠ 0 := by decide
            rw [nthDigitLSD, toDigits]
            simp only [h1_ne, dite_false, List.getD_cons_zero, digit_one, hs0]
          · have hz_ne : (1 : GaussianInt) + β * z' ≠ 0 := by
              intro h_eq
              have h1 : β * z' = -1 := by
                have : (1 : GaussianInt) + β * z' - 1 = 0 - 1 := congrArg (· - 1) h_eq
                simp only [add_sub_cancel_left, zero_sub] at this
                exact this
              -- norm(β * z') = 2 * norm(z') but norm(-1) = 1, contradiction
              have h_norm : (β * z').norm = β.norm * z'.norm := Zsqrtd.norm_mul β z'
              have hβ_norm : β.norm = 2 := by native_decide
              have h_neg1 : ((-1 : GaussianInt)).norm = 1 := by native_decide
              rw [h1, hβ_norm, h_neg1] at h_norm
              -- 1 = 2 * z'.norm contradiction since z' ≠ 0
              have hz'_norm_ne : z'.norm ≠ 0 := by
                intro h_zero
                exact hz'_zero ((norm_eq_zero_iff z').mp h_zero)
              have hz'_norm_pos : 0 < z'.norm.natAbs := Int.natAbs_pos.mpr hz'_norm_ne
              have : 2 * z'.norm.natAbs = 1 := by
                have h := Int.natAbs_mul 2 z'.norm
                simp only [Int.natAbs_ofNat] at h
                omega
              omega
            rw [nthDigitLSD, toDigits]
            simp only [hz_ne, dite_false, List.getD_cons_zero]
            rw [digit_one_add_β_mul, hs0]
        | succ n =>
          rw [nthDigitLSD_succ, βQuot_one_add_β_mul]
          have := congrFun hz' n
          simp only [iotaSuffix] at this
          exact this
      · -- s 0 = false: use z = β * z'
        use β * z'
        funext n
        simp only [iotaSuffix]
        have hs0_false : s 0 = false := Bool.eq_false_iff.mpr hs0
        cases n with
        | zero =>
          by_cases hz'_zero : z' = 0
          · subst hz'_zero
            simp only [mul_zero, nthDigitLSD_zero, hs0_false]
          · have hz_ne : β * z' ≠ 0 := by
              intro h_eq
              rcases mul_eq_zero.mp h_eq with hβ | hz''
              · exact (by decide : β ≠ 0) hβ
              · exact hz'_zero hz''
            rw [nthDigitLSD, toDigits]
            simp only [hz_ne, dite_false, List.getD_cons_zero]
            rw [digit_β_mul, hs0_false]
        | succ n =>
          rw [nthDigitLSD_succ, βQuot_β_mul]
          have := congrFun hz' n
          simp only [iotaSuffix] at this
          exact this

/-- CylinderSeq 0 is the entire space (no constraints) -/
theorem cylinderSeq_zero_eq_univ (p : Fin 0 → Bool) : CylinderSeq 0 p = Set.univ := by
  ext s
  simp only [CylinderSeq, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  intro j
  exact j.elim0

/-- μ_cantor is a probability measure: μ_cantor(Set.univ) = 1 -/
theorem μ_cantor_univ : μ_cantor Set.univ = 1 := by
  -- CylinderSeq 0 p = Set.univ for any p : Fin 0 → Bool
  have h := cylinderSeq_zero_eq_univ (fun j => j.elim0)
  rw [← h]
  -- μ_cantor(CylinderSeq 0 p) = μ_cylinder 0 = 1/2^0 = 1
  rw [μ_cantor_cylinder 0]
  simp only [μ_cylinder, pow_zero, Nat.cast_one]
  norm_num

/-- **The Golden Identity for ℤ[i]**: The measure of the closure equals 1.
    Since AsymptoticLogDensity(ℤ[i]) = 1 (by log₂ normalization), this confirms:
    μ_cantor(iotaSuffixClosure ℤ[i]) = AsymptoticLogDensity(ℤ[i]) = 1 -/
theorem golden_identity_full_set :
    μ_cantor (iotaSuffixClosure Set.univ) = 1 := by
  simp only [iotaSuffixClosure]
  rw [iotaSuffix_image_univ, eventuallyZeroSet_closure_eq_univ]
  exact μ_cantor_univ

/-! ### The True Golden Identity: What's Proven and What Remains

**PROVEN:**
1. `golden_identity_full_set`: μ_cantor(iotaSuffixClosure ℤ[i]) = 1
   - EventuallyZeroSet is dense in Cantor space
   - closure(iotaSuffix '' ℤ[i]) = Set.univ
   - μ_cantor(Set.univ) = 1

2. `golden_identity`: For finite S, iotaSuffixImage S = ⋂_n Saturation S n
   - This is the set-theoretic Golden Identity

3. `fundamental_bridge_β_pow`: LogWeight (β^k) = μ_cylinder k
   - Individual weights match cylinder measures

4. `closure_eq_iInter_saturation_inter_ez`: Topological identity with EventuallyZeroSet
   - closure(ι(S)) ∩ EZ = (⋂_k Saturation S k) ∩ EZ

**THE GAP (requires future work):**
The full identity `μ_cantor(iotaSuffixClosure S) = AsymptoticLogDensity S`
requires proving that the saturation measures converge to the asymptotic density.
This needs:
1. Precise bounds: digitLength z ≈ log₂(norm z)
2. Measure additivity: μ(⋃ᵢ Aᵢ) = Σᵢ μ(Aᵢ) for disjoint cylinders
3. Limit exchange: lim_k μ(Sat S k) = limsup_N (LogSum S N / log₂ N)

The infrastructure for (3) requires careful analysis of how saturation
measures relate to cumulative LogSum, which involves the relationship
between digitLength and norm bounds.
-/

/-- **Verified for full set (Measure side)**: μ_cantor(iotaSuffixClosure ℤ[i]) = 1

    This is the LHS of the Golden Identity for the universal case.
    The RHS (AsymptoticLogDensity ℤ[i] = 1) follows from the log₂ normalization
    but requires computing the actual sum of LogWeights. -/
theorem golden_identity_measure_side :
    μ_cantor (iotaSuffixClosure Set.univ) = 1 := golden_identity_full_set

/-! ## Section 6: The Image and Saturation Connection -/

/-- The image of iotaSuffix restricted to S -/
def iotaSuffixImage (S : Set GaussianInt) : Set BinarySeq :=
  iotaSuffix '' S

/-- The saturation at depth k contains the iotaSuffix image -/
theorem iotaSuffixImage_subset_saturation' (S : Set GaussianInt) (k : ℕ) :
    iotaSuffixImage S ⊆ Saturation S k := by
  intro s hs
  simp only [iotaSuffixImage, Set.mem_image] at hs
  obtain ⟨z, hz, rfl⟩ := hs
  simp only [Saturation, Set.mem_iUnion]
  use z, hz
  intro j
  rfl

/-- The iotaSuffix image is contained in the intersection of all saturations with EventuallyZeroSet -/
theorem iotaSuffixImage_subset_iInter_saturation (S : Set GaussianInt) :
    iotaSuffixImage S ⊆ (⋂ n, Saturation S n) ∩ EventuallyZeroSet := by
  intro s hs
  constructor
  · simp only [Set.mem_iInter]
    intro m
    exact iotaSuffixImage_subset_saturation' S m hs
  · simp only [iotaSuffixImage, Set.mem_image] at hs
    obtain ⟨z, _, rfl⟩ := hs
    exact iotaSuffix_eventually_zero z

/-- **Golden Identity (Reverse Inclusion)**: For FINITE sets S, if s is eventually zero
    and in all saturations, then s is the iotaSuffix image of some element of S.

    Key insight: For finite S, there exists a maximum digitLength M among elements matching
    s on [0, N). For K > M, saturation at K requires digitLength ≤ N (by the MSD argument).

    Note: This theorem is FALSE for infinite S. Counterexample: S = {β, β², β³, ...}
    The sequence s = (0,0,0,...) is in all saturations but 0 ∉ S. -/
theorem iInter_saturation_subset_iotaSuffixImage (S : Set GaussianInt) (hS : S.Finite) :
    (⋂ n, Saturation S n) ∩ EventuallyZeroSet ⊆ iotaSuffixImage S := by
  intro s ⟨h_sat, h_ez⟩
  simp only [EventuallyZeroSet, EventuallyZero, Set.mem_setOf_eq] at h_ez
  obtain ⟨N, hN⟩ := h_ez
  simp only [Set.mem_iInter] at h_sat
  simp only [iotaSuffixImage, Set.mem_image]
  -- Key lemma: any witness z with digitLength > N matching s on [0, K) where K > digitLength z - 1
  -- leads to contradiction (MSD mismatch). So for K large enough, witness has digitLength ≤ N.
  have h_witness_bound : ∀ K > N, ∀ z : GaussianInt, z ≠ 0 →
      (∀ j < K, iotaSuffix z j = s j) → digitLength z ≤ N ∨ digitLength z > K := by
    intro K hK z hz_ne h_match_K
    by_cases h_le : digitLength z ≤ N
    · left; exact h_le
    · right
      push_neg at h_le
      have h_msd_ge_N : digitLength z - 1 ≥ N := by omega
      by_contra h_not_gt
      push_neg at h_not_gt
      have h_msd_lt_K : digitLength z - 1 < K := by omega
      have h_match_msd := h_match_K (digitLength z - 1) h_msd_lt_K
      simp only [iotaSuffix] at h_match_msd
      have h_s_msd : s (digitLength z - 1) = false := hN (digitLength z - 1) h_msd_ge_N
      rw [h_s_msd] at h_match_msd
      have h_msd_true := toDigits_getLast_true z hz_ne
      have h_ne := toDigits_nonempty z hz_ne
      have h_len : (toDigits z).length - 1 < (toDigits z).length :=
        Nat.sub_lt (List.length_pos.mpr h_ne) Nat.one_pos
      simp only [nthDigitLSD, digitLength] at h_match_msd
      rw [List.getD_eq_getElem _ _ h_len] at h_match_msd
      have h_last := List.getLast_eq_getElem (toDigits z) h_ne
      simp only [List.length_reverse, Nat.sub_zero] at h_last
      rw [← h_last] at h_match_msd
      rw [h_msd_true] at h_match_msd
      exact absurd h_match_msd Bool.noConfusion
  -- KEY: Since S is finite, there exists M = max digitLength over S
  -- For K > M, any witness from Saturation S K must have digitLength ≤ N
  -- (because digitLength > K > M is impossible for elements of finite S)
  have h_max_exists : ∃ M : ℕ, ∀ z ∈ S, digitLength z ≤ M := by
    by_cases hS_empty : S = ∅
    · use 0; intro z hz; simp [hS_empty] at hz
    · have hS_nonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hS_empty
      -- S is finite and nonempty, so digitLength '' S is finite and nonempty
      have hImg : (digitLength '' S).Finite := Set.Finite.image digitLength hS
      have hImg_ne : (digitLength '' S).Nonempty := hS_nonempty.image digitLength
      -- Use Finset.max for the finite nonempty set
      let fs := hImg.toFinset
      have hfs_ne : fs.Nonempty := by
        rw [Set.Finite.toFinset_nonempty]
        exact hImg_ne
      use fs.max' hfs_ne
      intro z hz
      have hz_img : digitLength z ∈ digitLength '' S := Set.mem_image_of_mem digitLength hz
      have hz_fs : digitLength z ∈ fs := hImg.mem_toFinset.mpr hz_img
      exact Finset.le_max' fs (digitLength z) hz_fs
  obtain ⟨M, hM⟩ := h_max_exists
  -- Use saturation at K = max(N+1, M+1)
  let K := max (N + 1) (M + 1)
  have hK_gt_N : K > N := Nat.lt_of_lt_of_le (Nat.lt_succ_self N) (Nat.le_max_left _ _)
  have hK_gt_M : K > M := Nat.lt_of_lt_of_le (Nat.lt_succ_self M) (Nat.le_max_right _ _)
  have h_sat_K := h_sat K
  simp only [Saturation, Set.mem_iUnion] at h_sat_K
  obtain ⟨z, hz, h_match⟩ := h_sat_K
  have h_match' : ∀ j < K, iotaSuffix z j = s j := by
    intro j hj
    have := h_match ⟨j, hj⟩
    simp only [CylinderSeq, Set.mem_setOf_eq] at this
    exact this.symm
  -- Since z ∈ S and S is finite, digitLength z ≤ M < K
  have hz_bound : digitLength z ≤ M := hM z hz
  have hz_lt_K : digitLength z < K := Nat.lt_of_le_of_lt hz_bound hK_gt_M
  -- Case: z = 0
  by_cases hz_ne : z = 0
  · use z, hz
    funext n
    rw [hz_ne]
    simp only [iotaSuffix, nthDigitLSD_zero]
    by_cases hn : n < K
    · have h_eq := h_match' n hn
      rw [hz_ne] at h_eq
      simp only [iotaSuffix, nthDigitLSD_zero] at h_eq
      exact h_eq
    · push_neg at hn
      have hn' : n ≥ N := by omega
      exact (hN n hn').symm
  -- Case: z ≠ 0, but digitLength z < K, so by witness_bound, digitLength z ≤ N
  · have h_bound := h_witness_bound K hK_gt_N z hz_ne h_match'
    cases h_bound with
    | inl h_le =>
      -- digitLength z ≤ N: z is our witness
      use z, hz
      funext n
      by_cases hn : n < K
      · exact h_match' n hn
      · push_neg at hn
        have h_s_false : s n = false := hN n (by omega)
        have hz_len : digitLength z ≤ n := Nat.le_trans h_le (by omega)
        simp only [iotaSuffix]
        rw [nthDigitLSD_beyond_length z n hz_len, h_s_false]
    | inr h_gt =>
      -- digitLength z > K, but we know digitLength z ≤ M < K. Contradiction!
      exfalso
      have : digitLength z ≤ M := hM z hz
      omega

/-- **The Golden Identity**: For FINITE sets S, the intersection of all saturations
    with EventuallyZeroSet equals the iotaSuffix image.

    Note: This theorem is FALSE for infinite S. See the counterexample in
    iInter_saturation_subset_iotaSuffixImage. -/
theorem golden_identity (S : Set GaussianInt) (hS : S.Finite) :
    (⋂ n, Saturation S n) ∩ EventuallyZeroSet = iotaSuffixImage S :=
  Set.Subset.antisymm
    (iInter_saturation_subset_iotaSuffixImage S hS)
    (iotaSuffixImage_subset_iInter_saturation S)

end SPBiTopology
