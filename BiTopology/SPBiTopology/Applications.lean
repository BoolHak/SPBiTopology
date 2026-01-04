/-
  BiTopology/SPBiTopology/Applications.lean

  APPLICATIONS OF THE ℤ[i] ↔ ℕ BRIDGE

  This file contains results connecting the β-adic structure to number theory.

  PROVEN RESULTS:
  1. β-adic Norm Properties: N(β) = 2, N(βᵏ) = 2ᵏ, norm is multiplicative
  2. β-divisibility implies 2-divisibility: βᵏ | z ⟹ 2ᵏ | N(z)
  3. Conjugate Properties: N(z̄) = N(z), z·z̄ = N(z)
  4. Multiplicative Closure: Sums of two squares are closed under multiplication
  5. Cylinder-Representation Decomposition: NormFiber partitions over cylinders
  6. β-divisibility Filter: βʲ | z ⟹ cylinder only contributes when 2ʲ | n
-/

import BiTopology.SPBiTopology.Bridge

set_option autoImplicit false

namespace SPBiTopology

open GaussianInt Zsqrtd Classical

/-! ============================================================================
    PART I: β-ADIC NORM INTERACTION

    The fundamental relationship: N(β) = 2.
    This means: if βᵏ | z, then 2ᵏ | N(z).
    Note: Cylinder membership alone does NOT constrain N(z) mod powers of 2.
    The constraint requires explicit β-divisibility.
============================================================================ -/

/-- The norm of β = 1 + i is 2 -/
theorem beta_norm : gaussianNorm β = 2 := by
  unfold gaussianNorm β
  simp only [Zsqrtd.norm]
  native_decide

/-- β² = 2i, so N(β²) = 4 -/
theorem beta_sq_norm : gaussianNorm (β * β) = 4 := by
  unfold gaussianNorm β
  have h : (⟨1, 1⟩ : GaussianInt) * ⟨1, 1⟩ = ⟨0, 2⟩ := by ext <;> decide
  simp only [h, Zsqrtd.norm]
  native_decide

/-- The norm is multiplicative -/
theorem gaussianNorm_mul (z w : GaussianInt) :
    gaussianNorm (z * w) = gaussianNorm z * gaussianNorm w := by
  unfold gaussianNorm
  have hmul : (z * w).norm = z.norm * w.norm := Zsqrtd.norm_mul z w
  rw [hmul, Int.natAbs_mul]

/-- Powers of β have norm 2^k -/
theorem beta_pow_norm (k : ℕ) : gaussianNorm (β ^ k) = 2 ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero]
    unfold gaussianNorm
    simp only [Zsqrtd.norm, one_re, one_im]
    native_decide
  | succ n ih =>
    rw [pow_succ, gaussianNorm_mul, ih, beta_norm, pow_succ]

/-- If z is divisible by β^k, then N(z) is divisible by 2^k.
    This is the key connection: β-adic valuation controls 2-adic valuation of norm. -/
theorem norm_divisibility_from_beta (z : GaussianInt) (k : ℕ) (w : GaussianInt)
    (h : z = β ^ k * w) : 2 ^ k ∣ gaussianNorm z := by
  rw [h, gaussianNorm_mul, beta_pow_norm]
  exact Nat.dvd_mul_right (2 ^ k) (gaussianNorm w)

/-! ============================================================================
    PART II: CONJUGATE PROPERTIES

    The conjugate operation preserves norm and z·z̄ = N(z).
============================================================================ -/

/-- The conjugate of a Gaussian integer has the same norm -/
theorem star_norm (z : GaussianInt) : gaussianNorm (star z) = gaussianNorm z := by
  unfold gaussianNorm
  simp only [Zsqrtd.norm, star_re, star_im]
  congr 1
  ring

/-- Product of element and its conjugate equals the norm embedded in ℤ[i] -/
theorem mul_star_eq_norm (z : GaussianInt) :
    z * star z = ⟨(gaussianNorm z : ℤ), 0⟩ := by
  ext
  · simp only [Zsqrtd.mul_re, star_re, star_im]
    unfold gaussianNorm
    have hnorm : z.norm = z.re^2 + z.im^2 := gaussianInt_norm_eq z
    have hnn : 0 ≤ z.norm := gaussianInt_norm_nonneg z
    have hcast : (z.norm.natAbs : ℤ) = z.norm := Int.natAbs_of_nonneg hnn
    rw [hcast, hnorm]
    ring
  · simp only [Zsqrtd.mul_im, star_re, star_im]
    ring

/-! ============================================================================
    PART III: MULTIPLICATIVE CLOSURE

    Sums of two squares are closed under multiplication (Brahmagupta-Fibonacci).
============================================================================ -/

/-- Zero is a sum of two squares (0 = 0² + 0²) -/
theorem zero_sum_two_squares : IsSumOfTwoSquares 0 := by
  unfold IsSumOfTwoSquares
  use 0, 0
  ring

/-- One is a sum of two squares (1 = 1² + 0²) -/
theorem one_sum_two_squares : IsSumOfTwoSquares 1 := by
  unfold IsSumOfTwoSquares
  use 1, 0
  ring

/-- Two is a sum of two squares (2 = 1² + 1²) -/
theorem two_sum_two_squares : IsSumOfTwoSquares 2 := by
  unfold IsSumOfTwoSquares
  use 1, 1
  ring

/-- Sums of two squares are closed under multiplication (Brahmagupta-Fibonacci identity) -/
theorem sum_two_sq_mul (m n : ℕ) (hm : IsSumOfTwoSquares m) (hn : IsSumOfTwoSquares n) :
    IsSumOfTwoSquares (m * n) := by
  obtain ⟨a, b, hab⟩ := hm
  obtain ⟨c, d, hcd⟩ := hn
  unfold IsSumOfTwoSquares
  use a * c - b * d, a * d + b * c
  calc (a * c - b * d)^2 + (a * d + b * c)^2
      = (a^2 + b^2) * (c^2 + d^2) := by ring
    _ = (m : ℤ) * (n : ℤ) := by rw [hab, hcd]
    _ = ((m * n : ℕ) : ℤ) := by push_cast; ring

/-- Squares are sums of two squares (n² = n² + 0²) -/
theorem sq_sum_two_squares (n : ℕ) : IsSumOfTwoSquares (n^2) := by
  unfold IsSumOfTwoSquares
  use n, 0
  simp only [sq, Int.ofNat_mul]
  ring

/-- Every power of 2 is a sum of two squares -/
theorem pow_two_sum_two_squares (k : ℕ) : IsSumOfTwoSquares (2^k) := by
  induction k with
  | zero => exact one_sum_two_squares
  | succ n ih =>
    rw [pow_succ, Nat.mul_comm]
    exact sum_two_sq_mul 2 (2^n) two_sum_two_squares ih

/-! ============================================================================
    PART IV: CYLINDER-REPRESENTATION CONNECTION

    The cylinder decomposition partitions NormFiber(n).
    Each representation z with N(z) = n belongs to exactly one cylinder.
============================================================================ -/

/-- Elements in CylinderNormFiber are in the corresponding CylinderArc -/
theorem cylinder_norm_fiber_in_arc (k : ℕ) (p : Fin k → Bool) (n : ℕ)
    (z : GaussianInt) (hz : z ∈ CylinderNormFiber k p n) :
    z ∈ CylinderArc k p := by
  unfold CylinderNormFiber at hz
  simp only [Set.mem_setOf_eq] at hz
  exact hz.1

/-- Elements in CylinderNormFiber have the specified norm -/
theorem cylinder_norm_fiber_has_norm (k : ℕ) (p : Fin k → Bool) (n : ℕ)
    (z : GaussianInt) (hz : z ∈ CylinderNormFiber k p n) :
    gaussianNorm z = n := by
  unfold CylinderNormFiber at hz
  simp only [Set.mem_setOf_eq] at hz
  exact hz.2

/-- Every element of NormFiber(n) is in some CylinderNormFiber -/
theorem norm_fiber_covered_by_cylinders (k : ℕ) (n : ℕ) (z : GaussianInt)
    (hz : z ∈ NormFiber n) :
    ∃ p : Fin k → Bool, z ∈ CylinderNormFiber k p n := by
  use cylinderPattern z k
  unfold CylinderNormFiber CylinderArc
  simp only [Set.mem_setOf_eq]
  constructor
  · intro i; rfl
  · unfold NormFiber at hz
    simp only [Set.mem_setOf_eq] at hz
    exact hz

/-- The cylinder decomposition partitions NormFiber (from Bridge.lean) -/
theorem cylinder_decomposition_of_norm_fiber (k : ℕ) (n : ℕ) :
    NormFiber n = ⋃ (p : Fin k → Bool), CylinderNormFiber k p n :=
  cylinder_partitions_norm_fiber k n

/-- Each z belongs to exactly one cylinder pattern at depth k -/
theorem unique_cylinder_membership (k : ℕ) (z : GaussianInt) :
    ∃! p : Fin k → Bool, z ∈ CylinderArc k p :=
  cylinder_arcs_partition k z

/-! ============================================================================
    PART V: CYLINDER COUNTING STRUCTURE

    Each element of NormFiber(n) belongs to exactly one cylinder.
    This provides a partition for counting representations.
============================================================================ -/

/-- NormFiber(0) contains only 0 -/
theorem norm_fiber_zero : NormFiber 0 = {0} := by
  ext z
  simp only [NormFiber, Set.mem_setOf_eq, Set.mem_singleton_iff]
  unfold gaussianNorm
  constructor
  · intro hz
    have hnorm := gaussianInt_norm_eq z
    have hzero : z.norm = 0 := by
      have : z.norm.natAbs = 0 := hz
      exact Int.natAbs_eq_zero.mp this
    rw [hnorm] at hzero
    have hre : z.re = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    have him : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    ext <;> simp [hre, him]
  · intro hz
    rw [hz]
    simp [Zsqrtd.norm]

/-- Helper: if a² ≤ n then |a| ≤ n for integers -/
private theorem natAbs_le_of_sq_le {a : ℤ} {n : ℕ} (hn : n > 0) (h : a^2 ≤ n) : a.natAbs ≤ n := by
  have hcast : (a.natAbs : ℤ)^2 = a^2 := Int.natAbs_pow_two a
  -- a.natAbs² ≤ n as naturals
  have h1 : a.natAbs^2 ≤ n := by
    have hle : (a.natAbs : ℤ)^2 ≤ (n : ℤ) := by rw [hcast]; exact_mod_cast h
    exact Int.ofNat_le.mp (by simp only [Nat.cast_pow]; exact hle)
  -- If a.natAbs > n, then a.natAbs ≥ n+1, so a.natAbs² ≥ (n+1)² > n
  by_contra hgt
  push_neg at hgt
  have hge : a.natAbs ≥ n + 1 := hgt
  have hsq : a.natAbs^2 ≥ (n + 1)^2 := Nat.pow_le_pow_left hge 2
  have : (n + 1)^2 > n := by nlinarith
  omega

/-- Helper: natAbs bound implies interval membership -/
private theorem natAbs_le_iff_mem_Icc {a : ℤ} {n : ℕ} (h : a.natAbs ≤ n) :
    -(n : ℤ) ≤ a ∧ a ≤ (n : ℤ) := by
  have hle : |a| ≤ (n : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h
  exact abs_le.mp hle

/-- NormFiber(n) is finite for n > 0: there are finitely many (a,b) with a² + b² = n -/
theorem norm_fiber_finite (n : ℕ) (hn : n > 0) : (NormFiber n).Finite := by
  unfold NormFiber
  -- The set {z : N(z) = n} is a subset of [-n,n] × [-n,n] which is finite
  let S := (Finset.Icc (-n : ℤ) n ×ˢ Finset.Icc (-n : ℤ) n).image
    (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : GaussianInt))
  apply Set.Finite.subset (Finset.finite_toSet S)
  intro z hz
  simp only [Set.mem_setOf_eq] at hz
  -- Extract bounds from norm = n
  unfold gaussianNorm at hz
  have hnorm := gaussianInt_norm_eq z
  have hnn := gaussianInt_norm_nonneg z
  have hcast : z.norm = (n : ℤ) := by rw [← Int.natAbs_of_nonneg hnn, hz]
  have hre_sq : z.re^2 ≤ (n : ℤ) := by rw [← hcast, hnorm]; nlinarith [sq_nonneg z.im]
  have him_sq : z.im^2 ≤ (n : ℤ) := by rw [← hcast, hnorm]; nlinarith [sq_nonneg z.re]
  have hre_bound : z.re.natAbs ≤ n := natAbs_le_of_sq_le hn (by exact_mod_cast hre_sq)
  have him_bound : z.im.natAbs ≤ n := natAbs_le_of_sq_le hn (by exact_mod_cast him_sq)
  -- Get -n ≤ z.re ≤ n and -n ≤ z.im ≤ n
  have hre := natAbs_le_iff_mem_Icc hre_bound
  have him := natAbs_le_iff_mem_Icc him_bound
  -- Show z ∈ S
  rw [Finset.coe_image, Set.mem_image]
  refine ⟨(z.re, z.im), ?_, rfl⟩
  simp only [Finset.coe_product, Finset.coe_Icc, Set.mem_prod, Set.mem_Icc]
  exact ⟨hre, him⟩

/-- CylinderNormFiber is finite for n > 0 (subset of finite NormFiber) -/
theorem cylinder_norm_fiber_finite (k : ℕ) (p : Fin k → Bool) (n : ℕ) (hn : n > 0) :
    (CylinderNormFiber k p n).Finite := by
  apply Set.Finite.subset (norm_fiber_finite n hn)
  intro z hz
  unfold CylinderNormFiber at hz
  unfold NormFiber
  simp only [Set.mem_setOf_eq] at hz ⊢
  exact hz.2

/-- The cylinder contribution to representations: count in a specific cylinder -/
noncomputable def cylinderContribution (k : ℕ) (p : Fin k → Bool) (n : ℕ) : ℕ :=
  if hn : n > 0 then (cylinder_norm_fiber_finite k p n hn).toFinset.card else 0

/-- Each Gaussian integer with norm n belongs to exactly one cylinder -/
theorem unique_cylinder_for_norm (k : ℕ) (n : ℕ) (z : GaussianInt) (hz : gaussianNorm z = n) :
    ∃! p : Fin k → Bool, z ∈ CylinderNormFiber k p n := by
  have huniq := cylinder_arcs_partition k z
  obtain ⟨p, hp, hunique⟩ := huniq
  use p
  constructor
  · unfold CylinderNormFiber
    simp only [Set.mem_setOf_eq]
    exact ⟨hp, hz⟩
  · intro q hq
    unfold CylinderNormFiber at hq
    simp only [Set.mem_setOf_eq] at hq
    exact hunique q hq.1

/-! ============================================================================
    PART VI: β-DIVISIBILITY AND CYLINDER CONTRIBUTIONS

    Connection between Parts I-III and IV-V:
    If all elements in a cylinder are divisible by β^j, then the cylinder
    only contributes to norms divisible by 2^j.
============================================================================ -/

/-- If z ∈ CylinderNormFiber and βʲ | z, then 2ʲ | n -/
theorem cylinder_beta_div_implies_norm_div (k j : ℕ) (p : Fin k → Bool) (n : ℕ)
    (z : GaussianInt) (hz : z ∈ CylinderNormFiber k p n)
    (w : GaussianInt) (hdiv : z = β ^ j * w) : 2 ^ j ∣ n := by
  have hnorm := cylinder_norm_fiber_has_norm k p n z hz
  rw [← hnorm]
  exact norm_divisibility_from_beta z j w hdiv

/-- Contrapositive: if 2ʲ ∤ n, then no element divisible by βʲ is in CylinderNormFiber -/
theorem no_beta_div_in_cylinder_if_norm_not_div (k j : ℕ) (p : Fin k → Bool) (n : ℕ)
    (hndiv : ¬(2 ^ j ∣ n)) (z : GaussianInt) (hz : z ∈ CylinderNormFiber k p n) :
    ¬∃ w : GaussianInt, z = β ^ j * w := by
  intro ⟨w, hw⟩
  exact hndiv (cylinder_beta_div_implies_norm_div k j p n z hz w hw)

end SPBiTopology
