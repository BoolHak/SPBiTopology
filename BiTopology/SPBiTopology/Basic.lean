/-
  BiTopology/SPBiTopology/Basic.lean

  FOUNDATION: Canonical β-adic Representation of Gaussian Integers

-/

import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Data.List.Basic

set_option autoImplicit false

namespace SPBiTopology

abbrev GaussianInt := Zsqrtd (-1)

/-- The base β = -1 + i -/
def β : GaussianInt := ⟨-1, 1⟩

/-- Norm of β is 2 -/
theorem norm_β : β.norm = 2 := by native_decide

/-- β divides z iff z.re ≡ z.im (mod 2) -/
theorem β_dvd_iff (z : GaussianInt) : β ∣ z ↔ z.re % 2 = z.im % 2 := by
  constructor
  · intro ⟨q, hq⟩
    have hre : z.re = -q.re - q.im := by
      have := congrArg Zsqrtd.re hq
      simp only [β, Zsqrtd.mul_re] at this; linarith
    have him : z.im = q.re - q.im := by
      have := congrArg Zsqrtd.im hq
      simp only [β, Zsqrtd.mul_im] at this; linarith
    omega
  · intro h
    have hdiff_eq : z.im - z.re = 2 * ((z.im - z.re) / 2) := by
      have := Int.emod_add_ediv (z.im - z.re) 2; omega
    have hsum_eq : z.re + z.im = 2 * ((z.re + z.im) / 2) := by
      have := Int.emod_add_ediv (z.re + z.im) 2; omega
    use ⟨(z.im - z.re) / 2, -((z.re + z.im) / 2)⟩
    ext
    · simp only [β, Zsqrtd.mul_re]; linarith
    · simp only [β, Zsqrtd.mul_im]; linarith

/-- The digit of z: false (0) if β | z, else true (1) -/
def digit (z : GaussianInt) : Bool := z.re % 2 ≠ z.im % 2

theorem digit_zero : digit (0 : GaussianInt) = false := by
  simp [digit]

theorem digit_false_iff (z : GaussianInt) : digit z = false ↔ β ∣ z := by
  simp only [digit, ne_eq, decide_eq_false_iff_not, not_not, β_dvd_iff]

theorem digit_true_iff (z : GaussianInt) : digit z = true ↔ ¬(β ∣ z) := by
  simp only [digit, ne_eq, decide_eq_true_eq, β_dvd_iff]

/-- Helper to compute β-quotient -/
def βQuotAux (z : GaussianInt) : GaussianInt :=
  ⟨(z.im - z.re) / 2, -((z.re + z.im) / 2)⟩

/-- When z.re % 2 = z.im % 2, we have β * βQuotAux z = z -/
theorem β_mul_βQuotAux (z : GaussianInt) (h : z.re % 2 = z.im % 2) :
    β * βQuotAux z = z := by
  have hdiff_eq : z.im - z.re = 2 * ((z.im - z.re) / 2) := by
    have := Int.emod_add_ediv (z.im - z.re) 2; omega
  have hsum_eq : z.re + z.im = 2 * ((z.re + z.im) / 2) := by
    have := Int.emod_add_ediv (z.re + z.im) 2; omega
  ext
  · simp only [β, βQuotAux, Zsqrtd.mul_re]; linarith
  · simp only [β, βQuotAux, Zsqrtd.mul_im]; linarith

/-- (z-1).re % 2 = z.im % 2 when z.re % 2 ≠ z.im % 2 -/
theorem sub_one_fixes_parity (z : GaussianInt) (h : z.re % 2 ≠ z.im % 2) :
    (z.re - 1) % 2 = z.im % 2 := by omega

/-- The quotient function: βQuot z such that z = digit(z) + β * βQuot(z) -/
def βQuot (z : GaussianInt) : GaussianInt :=
  if digit z then βQuotAux ⟨z.re - 1, z.im⟩ else βQuotAux z

theorem βQuot_zero : βQuot (0 : GaussianInt) = 0 := by
  ext <;> simp [βQuot, βQuotAux, digit_zero]

/-- β * z is always divisible by β -/
theorem digit_β_mul (z : GaussianInt) : digit (β * z) = false := by
  rw [digit_false_iff]
  exact dvd_mul_right β z

/-- βQuot (β * z) = z -/
theorem βQuot_β_mul (z : GaussianInt) : βQuot (β * z) = z := by
  have hd : digit (β * z) = false := digit_β_mul z
  simp only [βQuot, hd, ↑reduceIte]
  have h_parity : (β * z).re % 2 = (β * z).im % 2 := by
    have := (digit_false_iff (β * z)).mp hd
    rw [β_dvd_iff] at this
    exact this
  have h_eq := β_mul_βQuotAux (β * z) h_parity
  have h_inj : β * βQuotAux (β * z) = β * z := h_eq
  have hβ_ne : β ≠ 0 := by decide
  exact mul_left_cancel₀ hβ_ne h_inj

/-- 1 + β * z is never divisible by β (for any z) -/
theorem digit_one_add_β_mul (z : GaussianInt) : digit (1 + β * z) = true := by
  rw [digit_true_iff]
  intro ⟨w, hw⟩
  have h1 : (1 : GaussianInt).re % 2 ≠ (1 : GaussianInt).im % 2 := by decide
  have hdvd : β ∣ (1 : GaussianInt) := by
    have hsub : (1 : GaussianInt) = (1 + β * z) - β * z := by ring
    rw [hsub]
    have h1 : β ∣ (1 + β * z) := ⟨w, hw⟩
    have h2 : β ∣ β * z := dvd_mul_right β z
    exact dvd_sub h1 h2
  rw [β_dvd_iff] at hdvd
  exact h1 hdvd

/-- βQuot (1 + β * z) = z -/
theorem βQuot_one_add_β_mul (z : GaussianInt) : βQuot (1 + β * z) = z := by
  have hd : digit (1 + β * z) = true := digit_one_add_β_mul z
  simp only [βQuot, hd, ↑reduceIte]
  have h_parity : (β * z).re % 2 = (β * z).im % 2 := by
    have := (digit_false_iff (β * z)).mp (digit_β_mul z)
    rw [β_dvd_iff] at this
    exact this
  have h_eq := β_mul_βQuotAux (β * z) h_parity
  have hβQuotAux_eq : βQuotAux (β * z) = z := by
    have h_inj : β * βQuotAux (β * z) = β * z := h_eq
    have hβ_ne : β ≠ 0 := by decide
    exact mul_left_cancel₀ hβ_ne h_inj
  have h_arg_eq : (⟨(1 + β * z).re - 1, (1 + β * z).im⟩ : GaussianInt) = β * z := by
    ext
    · simp only [Zsqrtd.add_re, Zsqrtd.one_re, Zsqrtd.mul_re, β]; ring
    · simp only [Zsqrtd.add_im, Zsqrtd.one_im, Zsqrtd.mul_im, β]; ring
  rw [h_arg_eq, hβQuotAux_eq]

/-- The fundamental recurrence: z = digit z + β * βQuot z -/
theorem digit_βQuot_spec (z : GaussianInt) :
    z = (if digit z then 1 else 0) + β * βQuot z := by
  by_cases hd : digit z
  · -- Case: digit z = true, so z.re % 2 ≠ z.im % 2
    simp only [hd, ↓reduceIte, βQuot]
    have hparity : z.re % 2 ≠ z.im % 2 := by
      simp only [digit, ne_eq, decide_eq_true_eq] at hd; exact hd
    have h_fixed := sub_one_fixes_parity z hparity
    have hmul := β_mul_βQuotAux ⟨z.re - 1, z.im⟩ h_fixed
    ext
    · have := congrArg Zsqrtd.re hmul
      simp only [Zsqrtd.add_re, Zsqrtd.one_re] at this ⊢; linarith
    · have := congrArg Zsqrtd.im hmul
      simp only [Zsqrtd.add_im, Zsqrtd.one_im] at this ⊢; linarith
  · -- Case: digit z = false, so z.re % 2 = z.im % 2
    simp only [hd, ↓reduceIte, Bool.false_eq_true, βQuot]
    have hparity : z.re % 2 = z.im % 2 := by
      simp only [digit, ne_eq, decide_eq_false_iff_not, not_not] at hd
      simpa using hd
    have hmul := β_mul_βQuotAux z hparity
    ext
    · have := congrArg Zsqrtd.re hmul
      simp only [Zsqrtd.add_re, Zsqrtd.zero_re, zero_add]; exact this.symm
    · have := congrArg Zsqrtd.im hmul
      simp only [Zsqrtd.add_im, Zsqrtd.zero_im, zero_add]; exact this.symm

/-! ## Norm Properties for Termination -/

/-- The norm of a Gaussian integer is re² + im² -/
theorem norm_eq (z : GaussianInt) : z.norm = z.re * z.re + z.im * z.im := by
  simp only [Zsqrtd.norm]
  ring

/-- Norm is non-negative for Gaussian integers -/
theorem norm_nonneg (z : GaussianInt) : 0 ≤ z.norm := by
  rw [norm_eq]
  nlinarith [sq_nonneg z.re, sq_nonneg z.im]

/-- Norm is zero iff z = 0 -/
theorem norm_eq_zero_iff (z : GaussianInt) : z.norm = 0 ↔ z = 0 := by
  constructor
  · intro h
    rw [norm_eq] at h
    have hre : z.re = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    have him : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    ext <;> simp [hre, him]
  · intro h
    simp [h, norm_eq]

/-- Norm is positive for non-zero z -/
theorem norm_pos (z : GaussianInt) (hz : z ≠ 0) : 0 < z.norm := by
  have h := norm_nonneg z
  cases' h.lt_or_eq with hlt heq
  · exact hlt
  · exfalso; exact hz ((norm_eq_zero_iff z).mp heq.symm)

/-- The norm of βQuotAux in terms of z -/
theorem norm_βQuotAux (z : GaussianInt) (h : z.re % 2 = z.im % 2) :
    (βQuotAux z).norm = z.norm / 2 := by
  -- β * βQuotAux z = z, so norm(β) * norm(βQuotAux z) = norm(z)
  -- 2 * norm(βQuotAux z) = norm(z)
  have hmul := β_mul_βQuotAux z h
  have hnorm : (β * βQuotAux z).norm = z.norm := by rw [hmul]
  rw [Zsqrtd.norm_mul] at hnorm
  simp only [norm_β] at hnorm
  omega

/-- For even-parity z ≠ 0, norm strictly decreases -/
theorem norm_βQuotAux_lt (z : GaussianInt) (hz : z ≠ 0) (hp : z.re % 2 = z.im % 2) :
    (βQuotAux z).norm < z.norm := by
  have hnorm := norm_βQuotAux z hp
  have hz_pos : 0 < z.norm := norm_pos z hz
  omega

/-! ## Termination Measure

The norm-based measure doesn't work directly because norm can temporarily increase
for small values (e.g., z = -1 has norm 1 but βQuot(-1) = 1+i has norm 2).

We use a hybrid measure:
- For a finite set of "exceptional" small values, we assign explicit ranks
  that form a strictly decreasing chain under βQuot.
- For all other values, we use 2 * norm + digit_bit, which strictly decreases.

The exceptional chain is: 1-i → -1 → 1+i → -i → i → 1 → 0
Plus the special cases -2±i where norm equality occurs.
-/

/-- Base measure: 2 * norm + parity adjustment -/
noncomputable def baseMeasure (z : GaussianInt) : ℕ :=
  2 * z.norm.natAbs + (if digit z then 1 else 0)

/-- Termination measure with explicit overrides for exceptional small values.
    The exceptional set covers the chain: 1-i → -1 → 1+i → -i → i → 1 → 0
    and -2±i (which have norm 5 but map to values with same or higher norm). -/
noncomputable def terminationMeasure (z : GaussianInt) : ℕ :=
  if z = 0 then 0
  else if z = (1 : GaussianInt) then 1
  else if z = ⟨0, 1⟩ then 2        -- i
  else if z = ⟨0, -1⟩ then 3       -- -i
  else if z = ⟨1, 1⟩ then 4        -- 1+i
  else if z = ⟨-1, 0⟩ then 5       -- -1
  else if z = ⟨1, -1⟩ then 6       -- 1-i
  else if z = ⟨-2, 1⟩ then 12      -- -2+i
  else if z = ⟨-2, -1⟩ then 12     -- -2-i
  else baseMeasure z

-- Computational lemmas for βQuot on exceptional values
private lemma βQuot_one : βQuot (1 : GaussianInt) = 0 := by
  simp only [βQuot, digit, βQuotAux]; native_decide

private lemma βQuot_i : βQuot (⟨0, 1⟩ : GaussianInt) = (1 : GaussianInt) := by
  simp only [βQuot, digit, βQuotAux]; native_decide

private lemma βQuot_neg_i : βQuot (⟨0, -1⟩ : GaussianInt) = ⟨0, 1⟩ := by
  simp only [βQuot, digit, βQuotAux]; native_decide

private lemma βQuot_one_plus_i : βQuot (⟨1, 1⟩ : GaussianInt) = ⟨0, -1⟩ := by
  simp only [βQuot, digit, βQuotAux]; native_decide

private lemma βQuot_neg_one : βQuot (⟨-1, 0⟩ : GaussianInt) = ⟨1, 1⟩ := by
  simp only [βQuot, digit, βQuotAux]; native_decide

private lemma βQuot_one_minus_i : βQuot (⟨1, -1⟩ : GaussianInt) = ⟨-1, 0⟩ := by
  simp only [βQuot, digit, βQuotAux]; native_decide

private lemma βQuot_neg2_plus_i : βQuot (⟨-2, 1⟩ : GaussianInt) = ⟨2, 1⟩ := by
  simp only [βQuot, digit, βQuotAux]; native_decide

-- For -2-i: First prove digit separately, then the βQuot computation works
private lemma digit_neg2_minus_i :
    digit (⟨-2, -1⟩ : GaussianInt) = true := by
  -- This is purely computation of Int.emod; it *does* reduce.
  native_decide

private lemma βQuot_neg2_minus_i : βQuot (⟨-2, -1⟩ : GaussianInt) = ⟨1, 2⟩ := by
  have hd : digit (⟨-2, -1⟩ : GaussianInt) = true := digit_neg2_minus_i
  -- Now the `if` is gone, and it's just arithmetic
  -- βQuot = βQuotAux ⟨-3, -1⟩ = ⟨(-1-(-3))/2, -((-3+(-1))/2)⟩ = ⟨1,2⟩
  ext <;> simp [βQuot, hd, βQuotAux]

-- Measure values for the targets of exceptional βQuot
private lemma terminationMeasure_2_1 : terminationMeasure (⟨2, 1⟩ : GaussianInt) = 11 := by
  simp only [terminationMeasure, baseMeasure, digit, norm_eq]; native_decide

private lemma terminationMeasure_1_2 : terminationMeasure (⟨1, 2⟩ : GaussianInt) = 11 := by
  simp only [terminationMeasure, baseMeasure, digit, norm_eq]; native_decide

-- Helper: terminationMeasure is bounded by baseMeasure for non-exceptional z
-- For exceptional z (norm ≤ 5), terminationMeasure ≤ 12
-- For non-exceptional z, terminationMeasure = baseMeasure
private lemma terminationMeasure_le_baseMeasure_add
    (z : GaussianInt) (hz : z ≠ 0) :
    terminationMeasure z ≤ baseMeasure z + 12 := by
  unfold terminationMeasure baseMeasure
  by_cases h1 : z = (1 : GaussianInt); · subst h1; native_decide
  by_cases hi : z = ⟨0, 1⟩; · subst hi; native_decide
  by_cases hni : z = ⟨0, -1⟩; · subst hni; native_decide
  by_cases hpi : z = ⟨1, 1⟩; · subst hpi; native_decide
  by_cases hn1 : z = ⟨-1, 0⟩; · subst hn1; native_decide
  by_cases hmi : z = ⟨1, -1⟩; · subst hmi; native_decide
  by_cases hn2p : z = ⟨-2, 1⟩; · subst hn2p; native_decide
  by_cases hn2m : z = ⟨-2, -1⟩; · subst hn2m; native_decide
  simp [hz, h1, hi, hni, hpi, hn1, hmi, hn2p, hn2m]

-- Helper lemmas for parity and digits
lemma digit_of_even_parity (z : GaussianInt) (h : z.re % 2 = z.im % 2) : digit z = false := by
  simp only [digit, ne_eq]
  rw [decide_eq_false_iff_not]
  exact fun hne => hne h

lemma digit_of_odd_parity (z : GaussianInt) (h : z.re % 2 ≠ z.im % 2) : digit z = true := by
  simp [digit]
  by_contra hc
  simp [hc] at h

lemma βQuot_eq_βQuotAux_of_even (z : GaussianInt) (h : z.re % 2 = z.im % 2) :
    βQuot z = βQuotAux z := by
  simp [βQuot, digit_of_even_parity z h]

lemma βQuot_eq_βQuotAux_of_odd (z : GaussianInt) (h : z.re % 2 ≠ z.im % 2) :
    βQuot z = βQuotAux ⟨z.re - 1, z.im⟩ := by
  simp [βQuot, digit_of_odd_parity z h]

lemma βQuotAux_norm_eq_half_norm_sub_one (z : GaussianInt) (h : z.re % 2 ≠ z.im % 2) :
    (βQuotAux ⟨z.re - 1, z.im⟩).norm = (⟨z.re - 1, z.im⟩ : GaussianInt).norm / 2 := by
  apply norm_βQuotAux
  apply sub_one_fixes_parity z h

/-- Predicate for values treated exceptionally in terminationMeasure -/
def isExceptional (z : GaussianInt) : Prop :=
  z = 0 ∨ z = 1 ∨ z = ⟨0, 1⟩ ∨ z = ⟨0, -1⟩ ∨ z = ⟨1, 1⟩ ∨
  z = ⟨-1, 0⟩ ∨ z = ⟨1, -1⟩ ∨ z = ⟨-2, 1⟩ ∨ z = ⟨-2, -1⟩

lemma not_isExceptional_iff (z : GaussianInt) :
    ¬ isExceptional z ↔
    z ≠ 0 ∧ z ≠ 1 ∧ z ≠ ⟨0, 1⟩ ∧ z ≠ ⟨0, -1⟩ ∧ z ≠ ⟨1, 1⟩ ∧
    z ≠ ⟨-1, 0⟩ ∧ z ≠ ⟨1, -1⟩ ∧ z ≠ ⟨-2, 1⟩ ∧ z ≠ ⟨-2, -1⟩ := by
  unfold isExceptional
  push_neg
  rfl

-- Helper: for non-exceptional z, terminationMeasure = baseMeasure
private lemma terminationMeasure_eq_baseMeasure
    (z : GaussianInt)
    (h_not_exc : ¬ isExceptional z) :
    terminationMeasure z = baseMeasure z := by
  rw [not_isExceptional_iff] at h_not_exc
  simp [terminationMeasure, baseMeasure, h_not_exc.1, h_not_exc.2.1, h_not_exc.2.2.1,
        h_not_exc.2.2.2.1, h_not_exc.2.2.2.2.1, h_not_exc.2.2.2.2.2.1,
        h_not_exc.2.2.2.2.2.2.1, h_not_exc.2.2.2.2.2.2.2.1, h_not_exc.2.2.2.2.2.2.2.2]

-- Helper: baseMeasure decreases for non-exceptional z
-- The proof is complex due to case analysis on parity and exceptional values.
-- Key insight: norm(βQuot z) < norm z for non-exceptional z.
private lemma baseMeasure_decrease_aux (z : GaussianInt)
    (h_not_exc : ¬ isExceptional z) :
    baseMeasure (βQuot z) < baseMeasure z := by
  have h_ne : z ≠ 0 := fun h => h_not_exc (Or.inl h)
  unfold baseMeasure
  -- Split by parity
  by_cases hp : z.re % 2 = z.im % 2
  · -- Even parity: digit z = false, βQuot z = βQuotAux z
    have hd : digit z = false := digit_of_even_parity z hp
    rw [βQuot_eq_βQuotAux_of_even z hp]
    simp only [hd, ite_false, add_zero]
    -- norm(βQuotAux z) < norm z
    have h_norm_lt : (βQuotAux z).norm < z.norm := norm_βQuotAux_lt z h_ne hp
    -- Convert to natAbs using norm non-negativity
    have h1 : 0 ≤ (βQuotAux z).norm := norm_nonneg _
    have h2 : 0 ≤ z.norm := norm_nonneg _
    have h_norm_nat : (βQuotAux z).norm.natAbs < z.norm.natAbs := by
      have h2_pos : 0 < z.norm := norm_pos z h_ne
      omega
    -- 2 * norm' + d' < 2 * norm where d' ≤ 1
    have d_le : (if digit (βQuotAux z) then 1 else 0) ≤ 1 := by split <;> simp
    omega
  · -- Odd parity: digit z = true, βQuot z = βQuotAux ⟨z.re - 1, z.im⟩
    have hd : digit z = true := digit_of_odd_parity z hp
    simp only [hd, ite_true]
    rw [βQuot_eq_βQuotAux_of_odd z hp]
    -- Need to show norm(βQuotAux ⟨z.re-1, z.im⟩) < norm z
    -- First, ⟨z.re-1, z.im⟩ has even parity (sub_one_fixes_parity)
    have hp' : (z.re - 1) % 2 = z.im % 2 := sub_one_fixes_parity z hp
    -- norm(βQuotAux w) = norm(w) / 2 for even parity w
    have h_norm_half : (βQuotAux ⟨z.re - 1, z.im⟩).norm = (⟨z.re - 1, z.im⟩ : GaussianInt).norm / 2 :=
      norm_βQuotAux ⟨z.re - 1, z.im⟩ hp'
    -- norm(⟨z.re-1, z.im⟩) = (z.re-1)² + z.im² = z.re² - 2*z.re + 1 + z.im²
    -- norm(z) = z.re² + z.im²
    -- So norm(⟨z.re-1, z.im⟩) = norm(z) - 2*z.re + 1
    have h_norm_sub : (⟨z.re - 1, z.im⟩ : GaussianInt).norm = z.norm - 2 * z.re + 1 := by
      simp only [norm_eq]; ring
    -- (z.re + 1)² + z.im² > 2 holds for all non-exceptional odd-parity z
    have h_ineq : (z.re + 1)^2 + z.im^2 > 2 := by
      by_contra h_contra
      push_neg at h_contra
      -- (z.re + 1)² ≤ 2 means z.re ∈ {-2, -1, 0}
      -- z.im² ≤ 2 means z.im ∈ {-1, 0, 1}
      have hre_bound : (z.re + 1)^2 ≤ 2 := by nlinarith [sq_nonneg z.im]
      have him_bound : z.im^2 ≤ 2 := by nlinarith [sq_nonneg (z.re + 1)]
      -- From x² ≤ 2, we get -1 ≤ x ≤ 1 (for integers)
      -- From (x+1)² ≤ 2, we get -2 ≤ x ≤ 0
      have hre_lo : -2 ≤ z.re := by nlinarith [sq_nonneg (z.re + 1), sq_nonneg (z.re + 2)]
      have hre_hi : z.re ≤ 0 := by nlinarith [sq_nonneg (z.re + 1), sq_nonneg z.re]
      have him_lo : -1 ≤ z.im := by nlinarith [sq_nonneg z.im, sq_nonneg (z.im + 1)]
      have him_hi : z.im ≤ 1 := by nlinarith [sq_nonneg z.im, sq_nonneg (z.im - 1)]
      -- Now we can enumerate: z.re ∈ {-2, -1, 0}, z.im ∈ {-1, 0, 1}
      have hre : z.re = -2 ∨ z.re = -1 ∨ z.re = 0 := by omega
      have him : z.im = -1 ∨ z.im = 0 ∨ z.im = 1 := by omega
      -- Check all 9 cases
      rcases hre with hre | hre | hre <;> rcases him with him | him | him
      -- z = ⟨-2, -1⟩: exceptional
      · have hz : z = ⟨-2, -1⟩ := by ext <;> simp [hre, him]
        exact h_not_exc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hz))))))))
      -- z = ⟨-2, 0⟩: even parity, contradicts hp
      · have hz : z = ⟨-2, 0⟩ := by ext <;> simp [hre, him]
        rw [hz] at hp; simp at hp
      -- z = ⟨-2, 1⟩: exceptional
      · have hz : z = ⟨-2, 1⟩ := by ext <;> simp [hre, him]
        exact h_not_exc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hz))))))))
      -- z = ⟨-1, -1⟩: even parity, contradicts hp
      · have hz : z = ⟨-1, -1⟩ := by ext <;> simp [hre, him]
        rw [hz] at hp; simp at hp
      -- z = ⟨-1, 0⟩: exceptional
      · have hz : z = ⟨-1, 0⟩ := by ext <;> simp [hre, him]
        exact h_not_exc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hz))))))
      -- z = ⟨-1, 1⟩: even parity, contradicts hp
      · have hz : z = ⟨-1, 1⟩ := by ext <;> simp [hre, him]
        rw [hz] at hp; simp at hp
      -- z = ⟨0, -1⟩: exceptional
      · have hz : z = ⟨0, -1⟩ := by ext <;> simp [hre, him]
        exact h_not_exc (Or.inr (Or.inr (Or.inr (Or.inl hz))))
      -- z = ⟨0, 0⟩ = 0: exceptional
      · have hz : z = 0 := by ext <;> simp [hre, him]
        exact h_not_exc (Or.inl hz)
      -- z = ⟨0, 1⟩: exceptional
      · have hz : z = ⟨0, 1⟩ := by ext <;> simp [hre, him]
        exact h_not_exc (Or.inr (Or.inr (Or.inl hz)))
    -- Now we can show norm decreases
    have h_norm_pos : 0 < z.norm := norm_pos z h_ne
    -- h_ineq says (z.re + 1)² + z.im² > 2
    -- Expanding: z.re² + 2*z.re + 1 + z.im² > 2
    -- So: z.re² + z.im² + 2*z.re > 1
    -- And: z.re² + z.im² - 2*z.re + 1 = (z.re² + z.im²) - 2*z.re + 1
    --      = norm(z) - 2*z.re + 1
    -- We need this > 0, i.e., norm(z) > 2*z.re - 1
    -- From h_ineq: norm(z) + 2*z.re + 1 > 2, so norm(z) > 1 - 2*z.re
    have h_norm_sub_pos : 0 < (⟨z.re - 1, z.im⟩ : GaussianInt).norm := by
      simp only [norm_eq]
      -- Need: (z.re - 1) * (z.re - 1) + z.im * z.im > 0
      -- This is true unless z.re = 1 and z.im = 0, i.e., z = 1
      -- But z = 1 is exceptional, contradicting h_not_exc
      have h_ne_one : z ≠ 1 := fun h => h_not_exc (Or.inr (Or.inl h))
      have h_sq1 : (z.re - 1) * (z.re - 1) ≥ 0 := mul_self_nonneg _
      have h_sq2 : z.im * z.im ≥ 0 := mul_self_nonneg _
      have h_sum_nonneg : (z.re - 1) * (z.re - 1) + z.im * z.im ≥ 0 := by linarith
      cases' h_sum_nonneg.lt_or_eq with hlt heq
      · exact hlt
      · exfalso
        have hre : z.re - 1 = 0 := by nlinarith
        have him : z.im = 0 := by nlinarith
        have : z = 1 := by ext <;> simp [hre, him]; omega
        exact h_ne_one this
    have h_norm_reduce : (βQuotAux ⟨z.re - 1, z.im⟩).norm < z.norm := by
      rw [h_norm_half, h_norm_sub]
      -- Need: (norm(z) - 2*z.re + 1) / 2 < norm(z)
      -- i.e., norm(z) - 2*z.re + 1 < 2 * norm(z)
      -- i.e., 1 - 2*z.re < norm(z)
      have h_expand : (z.re + 1)^2 + z.im^2 = z.norm + 2*z.re + 1 := by
        simp only [norm_eq]; ring
      have h_lt : z.norm - 2*z.re + 1 < z.norm * 2 := by linarith
      have h_two_pos : (0 : ℤ) < 2 := by norm_num
      exact Int.ediv_lt_of_lt_mul h_two_pos h_lt
    -- Convert to natAbs
    have h1 : 0 ≤ (βQuotAux ⟨z.re - 1, z.im⟩).norm := norm_nonneg _
    have h2 : 0 ≤ z.norm := norm_nonneg _
    have h_norm_nat : (βQuotAux ⟨z.re - 1, z.im⟩).norm.natAbs < z.norm.natAbs := by
      have h2_pos : 0 < z.norm := h_norm_pos
      omega
    -- 2 * norm' + d' < 2 * norm + 1
    have d_le : (if digit (βQuotAux ⟨z.re - 1, z.im⟩) then 1 else 0) ≤ 1 := by split <;> simp
    omega

-- Helper: handle transition into exceptional set
private lemma terminationMeasure_decrease_exceptional_target (z : GaussianInt)
    (h_not_exc : ¬ isExceptional z)
    (h_target : isExceptional (βQuot z)) :
    terminationMeasure (βQuot z) < baseMeasure z := by
  -- Each exceptional target value has a small terminationMeasure (≤ 12).
  -- For non-exceptional z, baseMeasure z ≥ 2 * norm z ≥ some minimum.
  have h_ne : z ≠ 0 := fun h => h_not_exc (Or.inl h)
  have h_norm_pos : 0 < z.norm := norm_pos z h_ne
  have h_base_ge_2 : baseMeasure z ≥ 2 := by
    unfold baseMeasure
    have : z.norm.natAbs ≥ 1 := by omega
    omega
  -- Key insight: if βQuot z is exceptional, then z = d + β * (βQuot z)
  -- where d = digit z ∈ {0, 1}. So z is determined by βQuot z and digit z.
  -- For most targets, terminationMeasure ≤ 6 < baseMeasure z (since baseMeasure ≥ 2 and norm ≥ 1 gives baseMeasure ≥ 2)
  -- But we need baseMeasure > terminationMeasure, so we need more careful analysis.
  -- Actually, for target 0: terminationMeasure = 0 < 2 ≤ baseMeasure z ✓
  -- For targets with terminationMeasure ≤ 6: need baseMeasure z > 6, i.e., norm ≥ 3
  -- For targets -2±i with terminationMeasure = 12: need baseMeasure z > 12, i.e., norm ≥ 6
  -- We handle each case by computing z explicitly from digit_βQuot_spec
  unfold isExceptional at h_target
  rcases h_target with h | h | h | h | h | h | h | h | h
  -- Target = 0: terminationMeasure 0 = 0
  -- βQuot z = 0 means z = d + β*0 = d, so z ∈ {0, 1}
  -- But z = 0 and z = 1 are both exceptional, contradicting h_not_exc
  · have h_z_form := digit_βQuot_spec z
    rw [h] at h_z_form
    simp only [mul_zero, add_zero] at h_z_form
    by_cases hd : digit z
    · simp only [hd, ite_true] at h_z_form
      -- z = 1, which is exceptional
      exact absurd (Or.inr (Or.inl h_z_form)) h_not_exc
    · simp only [hd, ite_false] at h_z_form
      -- z = 0, which is exceptional
      exact absurd (Or.inl h_z_form) h_not_exc
  -- Target = 1: terminationMeasure 1 = 1
  -- z = d + β*1 = d + (-1+i), so z ∈ {-1+i, i}
  -- But i is exceptional, so z = -1+i (if digit z = false, but then z = -1+i which has norm 2)
  -- Actually z = i is exceptional, contradicting h_not_exc
  · have h_z_form := digit_βQuot_spec z
    rw [h] at h_z_form
    simp only [β] at h_z_form
    by_cases hd : digit z
    · simp only [hd, ite_true] at h_z_form
      -- z = 1 + (-1+i)*1 = 1 + (-1+i) = i, which is exceptional
      have hz : z = ⟨0, 1⟩ := by
        have : z = 1 + ⟨-1, 1⟩ * 1 := h_z_form
        simp only [mul_one, Zsqrtd.add_def] at this
        ext <;> simp [this]
      exact absurd (Or.inr (Or.inr (Or.inl hz))) h_not_exc
    · simp only [hd, ite_false] at h_z_form
      -- z = 0 + (-1+i)*1 = -1+i, norm = 2, baseMeasure = 4 or 5
      have hz : z = ⟨-1, 1⟩ := by
        have : z = 0 + ⟨-1, 1⟩ * 1 := h_z_form
        simp only [mul_one, zero_add] at this
        exact this
      rw [hz]; simp only [h, terminationMeasure, baseMeasure, digit]; native_decide
  -- Target = i: terminationMeasure i = 2
  -- z = d + β*i = d + (-1+i)*i = d + (-i-1) = d - 1 - i
  · have h_z_form := digit_βQuot_spec z
    rw [h] at h_z_form
    simp only [β] at h_z_form
    by_cases hd : digit z
    · simp only [hd, ite_true] at h_z_form
      -- z = 1 + (-1+i)*i = 1 + (-i-1) = -i, which is exceptional
      have hz : z = ⟨0, -1⟩ := by simp [h_z_form]; ring_nf; rfl
      exact absurd (Or.inr (Or.inr (Or.inr (Or.inl hz)))) h_not_exc
    · simp only [hd, ite_false] at h_z_form
      -- z = (-1+i)*i = -i-1 = -1-i, norm = 2
      have hz : z = ⟨-1, -1⟩ := by simp [h_z_form]; ring_nf; rfl
      rw [hz]; simp only [h, terminationMeasure, baseMeasure, digit]; native_decide
  -- Target = -i: terminationMeasure (-i) = 3
  · have h_z_form := digit_βQuot_spec z
    rw [h] at h_z_form
    simp only [β] at h_z_form
    by_cases hd : digit z
    · simp only [hd, ite_true] at h_z_form
      -- z = 1 + (-1+i)*(-i) = 1 + (i+1) = 2+i, norm = 5
      have hz : z = ⟨2, 1⟩ := by simp [h_z_form]; ring_nf; rfl
      rw [hz]; simp only [h, terminationMeasure, baseMeasure, digit]; native_decide
    · simp only [hd, ite_false] at h_z_form
      -- z = (-1+i)*(-i) = i+1 = 1+i, which is exceptional
      have hz : z = ⟨1, 1⟩ := by simp [h_z_form]; ring_nf; rfl
      exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hz))))) h_not_exc
  -- Target = 1+i: terminationMeasure (1+i) = 4
  · have h_z_form := digit_βQuot_spec z
    rw [h] at h_z_form
    simp only [β] at h_z_form
    by_cases hd : digit z
    · simp only [hd, ite_true] at h_z_form
      -- z = 1 + (-1+i)*(1+i) = 1 + (-1-i+i-1) = 1 + (-2) = -1, which is exceptional
      have hz : z = ⟨-1, 0⟩ := by simp [h_z_form]; ring_nf; rfl
      exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hz)))))) h_not_exc
    · simp only [hd, ite_false] at h_z_form
      -- z = (-1+i)*(1+i) = -1-i+i-1 = -2, norm = 4
      have hz : z = ⟨-2, 0⟩ := by simp [h_z_form]; ring_nf; rfl
      rw [hz]; simp only [h, terminationMeasure, baseMeasure, digit]; native_decide
  -- Target = -1: terminationMeasure (-1) = 5
  · have h_z_form := digit_βQuot_spec z
    rw [h] at h_z_form
    simp only [β] at h_z_form
    by_cases hd : digit z
    · simp only [hd, ite_true] at h_z_form
      -- z = 1 + (-1+i)*(-1) = 1 + (1-i) = 2-i, norm = 5
      have hz : z = ⟨2, -1⟩ := by simp [h_z_form]; ring_nf; rfl
      rw [hz]; simp only [h, terminationMeasure, baseMeasure, digit]; native_decide
    · simp only [hd, ite_false] at h_z_form
      -- z = (-1+i)*(-1) = 1-i, which is exceptional
      have hz : z = ⟨1, -1⟩ := by simp [h_z_form]; ring_nf; rfl
      exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hz))))))) h_not_exc
  -- Target = 1-i: terminationMeasure (1-i) = 6
  · have h_z_form := digit_βQuot_spec z
    rw [h] at h_z_form
    simp only [β] at h_z_form
    by_cases hd : digit z
    · simp only [hd, ite_true] at h_z_form
      -- z = 1 + (-1+i)*(1-i) = 1 + (-1+i+i+1) = 1 + 2i = 1+2i, norm = 5
      have hz : z = ⟨1, 2⟩ := by simp [h_z_form]; ring_nf; rfl
      rw [hz]; simp only [h, terminationMeasure, baseMeasure, digit]; native_decide
    · simp only [hd, ite_false] at h_z_form
      -- z = (-1+i)*(1-i) = -1+i+i+1 = 2i, norm = 4
      have hz : z = ⟨0, 2⟩ := by simp [h_z_form]; ring_nf; rfl
      rw [hz]; simp only [h, terminationMeasure, baseMeasure, digit]; native_decide
  -- Target = -2+i: terminationMeasure (-2+i) = 12
  · have h_z_form := digit_βQuot_spec z
    rw [h] at h_z_form
    simp only [β] at h_z_form
    by_cases hd : digit z
    · simp only [hd, ite_true] at h_z_form
      -- z = 1 + (-1+i)*(-2+i) = 1 + (2-i-2i-1) = 1 + (1-3i) = 2-3i, norm = 13
      have hz : z = ⟨2, -3⟩ := by simp [h_z_form]; ring_nf; rfl
      rw [hz]; simp only [h, terminationMeasure, baseMeasure, digit]; native_decide
    · simp only [hd, ite_false] at h_z_form
      -- z = (-1+i)*(-2+i) = 2-i-2i-1 = 1-3i, norm = 10
      have hz : z = ⟨1, -3⟩ := by simp [h_z_form]; ring_nf; rfl
      rw [hz]; simp only [h, terminationMeasure, baseMeasure, digit]; native_decide
  -- Target = -2-i: terminationMeasure (-2-i) = 12
  · have h_z_form := digit_βQuot_spec z
    rw [h] at h_z_form
    simp only [β] at h_z_form
    by_cases hd : digit z
    · simp only [hd, ite_true] at h_z_form
      -- z = 1 + (-1+i)*(-2-i) = 1 + (2+i-2i+1) = 1 + (3-i) = 4-i, norm = 17
      have hz : z = ⟨4, -1⟩ := by simp [h_z_form]; ring_nf; rfl
      rw [hz]; simp only [h, terminationMeasure, baseMeasure, digit]; native_decide
    · simp only [hd, ite_false] at h_z_form
      -- z = (-1+i)*(-2-i) = 2+i-2i+1 = 3-i, norm = 10
      have hz : z = ⟨3, -1⟩ := by simp [h_z_form]; ring_nf; rfl
      rw [hz]; simp only [h, terminationMeasure, baseMeasure, digit]; native_decide

/-- The termination measure strictly decreases.
    Proof strategy: Handle exceptional cases by direct computation,
    then for general cases use norm inequalities. -/
theorem terminationMeasure_decrease (z : GaussianInt) (hz : z ≠ 0) :
    terminationMeasure (βQuot z) < terminationMeasure z := by
  -- Handle exceptional z cases by direct computation
  by_cases h_exc : isExceptional z
  · rcases h_exc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · contradiction -- z=0
    all_goals { simp only [terminationMeasure, baseMeasure, βQuot, βQuotAux, digit, norm_eq]; native_decide }

  -- Case: z is non-exceptional
  · rw [terminationMeasure_eq_baseMeasure z h_exc]
    -- Check if target is exceptional
    by_cases h_target : isExceptional (βQuot z)
    · -- Transition to exceptional set
      apply terminationMeasure_decrease_exceptional_target z h_exc h_target
    · -- Target is also non-exceptional
      rw [terminationMeasure_eq_baseMeasure (βQuot z) h_target]
      apply baseMeasure_decrease_aux z h_exc

/-! ## Canonical Representation -/

/-- Compute the canonical digit representation (LSD first) -/
noncomputable def toDigits (z : GaussianInt) : List Bool :=
  if hz : z = 0 then []
  else digit z :: toDigits (βQuot z)
termination_by terminationMeasure z
decreasing_by exact terminationMeasure_decrease z hz

/-- Evaluate a digit list back to GaussianInt -/
def evalDigits : List Bool → GaussianInt
  | [] => 0
  | d :: ds => (if d then 1 else 0) + β * evalDigits ds

/-- Zero has empty representation -/
theorem toDigits_zero : toDigits 0 = [] := by simp [toDigits]

/-- Correctness: evalDigits (toDigits z) = z -/
theorem evalDigits_toDigits (z : GaussianInt) : evalDigits (toDigits z) = z := by
  unfold toDigits
  split
  · rename_i h; simp only [h, evalDigits]
  · rename_i hz
    simp only [evalDigits]
    have ih := evalDigits_toDigits (βQuot z)
    rw [ih]
    exact (digit_βQuot_spec z).symm
termination_by terminationMeasure z
decreasing_by exact terminationMeasure_decrease z (by assumption)

/-! ## Digit Length and Access -/

/-- The digit length of z: number of digits in canonical representation -/
noncomputable def digitLength (z : GaussianInt) : ℕ := (toDigits z).length

/-- Zero has digit length 0 -/
theorem digitLength_zero : digitLength 0 = 0 := by simp [digitLength, toDigits_zero]

/-- Nonzero z has positive digit length -/
theorem digitLength_pos (z : GaussianInt) (hz : z ≠ 0) : 0 < digitLength z := by
  unfold digitLength toDigits
  simp only [hz, ↓reduceDIte, List.length_cons]
  omega

/-- toDigits of nonzero z is nonempty -/
theorem toDigits_nonempty (z : GaussianInt) (hz : z ≠ 0) : toDigits z ≠ [] := by
  intro h
  have : evalDigits (toDigits z) = 0 := by simp [h, evalDigits]
  rw [evalDigits_toDigits] at this
  exact hz this

/-- toDigits z = [] iff z = 0 -/
theorem toDigits_eq_nil_iff (z : GaussianInt) : toDigits z = [] ↔ z = 0 := by
  constructor
  · intro h
    by_contra hz
    exact toDigits_nonempty z hz h
  · intro h; rw [h, toDigits_zero]

/-- Get the n-th digit from LSD (0-indexed). Returns false beyond representation. -/
noncomputable def nthDigitLSD (z : GaussianInt) (n : ℕ) : Bool :=
  (toDigits z).getD n false

 theorem nthDigitLSD_zero (n : ℕ) : nthDigitLSD (0 : GaussianInt) n = false := by
  simp [nthDigitLSD, toDigits]

/-- The 0th LSD digit equals digit z for non-zero z -/
theorem nthDigitLSD_zero_eq (z : GaussianInt) (hz : z ≠ 0) :
    nthDigitLSD z 0 = digit z := by
  unfold nthDigitLSD toDigits
  simp only [hz, ↓reduceDIte, List.getD_cons_zero]

 /-- The 0th LSD digit is `false` for zero and `digit z` otherwise. -/
 theorem nthDigitLSD_zero_eq_if (z : GaussianInt) :
     nthDigitLSD z 0 = (if z = 0 then false else digit z) := by
   by_cases hz : z = 0
   · subst hz
     simp [nthDigitLSD, toDigits]
   · unfold nthDigitLSD toDigits
     simp [hz]

/-- Get the n-th digit from MSD (0-indexed). Returns false beyond representation. -/
noncomputable def nthDigitMSD (z : GaussianInt) (n : ℕ) : Bool :=
  let ds := toDigits z
  if h : n < ds.length then ds.reverse.get ⟨n, by simp [h]⟩ else false

/-! ## Key Properties for Topology -/

/-- The first k LSD digits of z -/
noncomputable def lsdPrefix (z : GaussianInt) (k : ℕ) : List Bool :=
  (toDigits z).take k

/-- The first m MSD digits of z -/
noncomputable def msdPrefix (z : GaussianInt) (m : ℕ) : List Bool :=
  (toDigits z).reverse.take m

/-- Two elements agree on first k LSD digits -/
def lsdAgree (z w : GaussianInt) (k : ℕ) : Prop :=
  ∀ n < k, nthDigitLSD z n = nthDigitLSD w n

/-- Two elements agree on first m MSD digits -/
def msdAgree (z w : GaussianInt) (m : ℕ) : Prop :=
  digitLength z = digitLength w ∧ ∀ n < m, nthDigitMSD z n = nthDigitMSD w n

/-- Helper: if first digits agree, difference is divisible by β -/
 theorem digit_agree_imp_β_dvd (z w : GaussianInt) (h : digit z = digit w) :
    β ∣ (z - w) := by
  rw [β_dvd_iff]
  simp only [Zsqrtd.sub_re, Zsqrtd.sub_im]
  simp only [digit, ne_eq, decide_eq_decide] at h
  omega

 /-- Helper: if β divides the difference, then the first digits agree -/
 theorem β_dvd_sub_imp_digit_eq (z w : GaussianInt) (hβ : β ∣ (z - w)) :
     digit z = digit w := by
   have hparity : (z - w).re % 2 = (z - w).im % 2 := (β_dvd_iff (z - w)).1 hβ
   simp only [digit, ne_eq, decide_eq_decide, Zsqrtd.sub_re, Zsqrtd.sub_im] at hparity ⊢
   omega

/-- Helper: z - w = β * (βQuot z - βQuot w) when digits agree -/
theorem βQuot_sub (z w : GaussianInt) (hd : digit z = digit w) :
    z - w = β * (βQuot z - βQuot w) := by
  have hz := digit_βQuot_spec z
  have hw := digit_βQuot_spec w
  have hdiff : (if digit z then (1 : GaussianInt) else 0) - (if digit w then 1 else 0) = 0 := by
    simp only [hd, sub_self]
  calc z - w
    = ((if digit z then 1 else 0) + β * βQuot z) - ((if digit w then 1 else 0) + β * βQuot w) := by
        conv_lhs => rw [hz, hw]
    _ = ((if digit z then 1 else 0) - (if digit w then 1 else 0)) + β * (βQuot z - βQuot w) := by ring
    _ = 0 + β * (βQuot z - βQuot w) := by rw [hdiff]
    _ = β * (βQuot z - βQuot w) := by ring

 /-- Helper: nthDigitLSD shifts with βQuot -/
 theorem nthDigitLSD_succ (z : GaussianInt) (n : ℕ) :
    nthDigitLSD z (n + 1) = nthDigitLSD (βQuot z) n := by
  by_cases hz : z = 0
  · subst hz
    simp [nthDigitLSD_zero, βQuot_zero]
  · simp only [nthDigitLSD]
    conv_lhs => rw [toDigits]; simp only [hz, ↓reduceDIte]
    simp only [List.getD_cons_succ]

/-- LSD agreement ↔ β^k divisibility (KEY THEOREM for suffix topology) -/
theorem lsd_agree_iff_pow_dvd (z w : GaussianInt) (k : ℕ) :
    lsdAgree z w k ↔ β^k ∣ (z - w) := by
  induction k generalizing z w with
  | zero =>
    simp only [lsdAgree, Nat.not_lt_zero, IsEmpty.forall_iff, forall_const, pow_zero, one_dvd,
               iff_true]
  | succ k ih =>
    constructor
    · -- lsdAgree z w (k+1) → β^(k+1) | (z - w)
      intro h
      by_cases hz : z = 0
      · subst hz
        by_cases hw : w = 0
        · simp only [hw, sub_self]; exact dvd_zero _
        · have hd0 : nthDigitLSD (0 : GaussianInt) 0 = nthDigitLSD w 0 :=
            h 0 (Nat.zero_lt_succ k)
          have hw_digit : digit w = false := by
            -- nthDigitLSD 0 0 = false
            have : nthDigitLSD (0 : GaussianInt) 0 = false := nthDigitLSD_zero 0
            have hw0 : nthDigitLSD w 0 = false := by simpa [this] using hd0
            simpa [nthDigitLSD_zero_eq w hw] using hw0
          have hw_eq : w = β * βQuot w := by
            simpa [hw_digit] using (digit_βQuot_spec w)
          have hrest : lsdAgree (0 : GaussianInt) (βQuot w) k := by
            intro n hn
            have hagree := h (n + 1) (Nat.succ_lt_succ hn)
            have h0 : nthDigitLSD (0 : GaussianInt) (n + 1) = false := nthDigitLSD_zero (n + 1)
            have hw_n1 : nthDigitLSD w (n + 1) = false := by
              simpa [h0] using hagree.symm
            have hw_shift : nthDigitLSD w (n + 1) = nthDigitLSD (βQuot w) n := by
              simpa using (nthDigitLSD_succ w n)
            have hβq : nthDigitLSD (βQuot w) n = false := by
              simpa [hw_shift] using hw_n1
            simp [nthDigitLSD_zero n, hβq]
          have hdiv : β^k ∣ ((0 : GaussianInt) - βQuot w) := (ih (0 : GaussianInt) (βQuot w)).1 hrest
          have hdiv' : β^(k+1) ∣ (-(w : GaussianInt)) := by
            -- rewrite -w using hw_eq
            have : β^(k+1) ∣ β * (-(βQuot w)) := by
              have hm : β * (β^k) ∣ β * ((0 : GaussianInt) - βQuot w) := mul_dvd_mul_left β hdiv
              simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg, add_assoc] using hm
            have hwneg : (-(w : GaussianInt)) = β * (-(βQuot w)) := by
              -- from w = β * βQuot w
              calc
                (-(w : GaussianInt)) = - (β * βQuot w) := by
                  exact congrArg Neg.neg hw_eq
                _ = β * (-(βQuot w)) := by
                  ring
            simpa [hwneg] using this
          simpa [sub_eq_add_neg] using hdiv'
      · by_cases hw : w = 0
        · subst hw
          have hd0 : nthDigitLSD z 0 = nthDigitLSD (0 : GaussianInt) 0 :=
            h 0 (Nat.zero_lt_succ k)
          have hz_digit : digit z = false := by
            have : nthDigitLSD (0 : GaussianInt) 0 = false := nthDigitLSD_zero 0
            have hz0 : nthDigitLSD z 0 = false := by simpa [this] using hd0
            simpa [nthDigitLSD_zero_eq z hz] using hz0
          have hz_eq : z = β * βQuot z := by
            simpa [hz_digit] using (digit_βQuot_spec z)
          have hrest : lsdAgree (βQuot z) (0 : GaussianInt) k := by
            intro n hn
            have := h (n + 1) (Nat.succ_lt_succ hn)
            have h0 : nthDigitLSD (0 : GaussianInt) (n + 1) = false := nthDigitLSD_zero (n + 1)
            have hz_n1 : nthDigitLSD z (n + 1) = false := by
              -- from agreement with 0
              have : nthDigitLSD z (n + 1) = nthDigitLSD (0 : GaussianInt) (n + 1) := this
              simpa [h0] using this
            have hz' : nthDigitLSD (βQuot z) n = false := by
              have hzshift : nthDigitLSD z (n + 1) = nthDigitLSD (βQuot z) n := by
                simpa using (nthDigitLSD_succ z n)
              simpa [hzshift] using hz_n1
            simpa [nthDigitLSD_zero n, hz']
          have hdiv : β^k ∣ (βQuot z - (0 : GaussianInt)) :=
            (ih (βQuot z) (0 : GaussianInt)).1 hrest
          have : β^(k+1) ∣ z := by
            have hm : β * (β^k) ∣ β * (βQuot z) := mul_dvd_mul_left β (by simpa using hdiv)
            have hm1 : β^k * β ∣ β * (βQuot z) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using hm
            have hm' : β^(k+1) ∣ β * (βQuot z) := by
              simpa [pow_succ] using hm1
            -- rewrite the goal using hz_eq and finish (avoid simp recursion)
            rw [hz_eq]
            exact hm'
          simpa [sub_eq_add_neg] using this
        · -- Main case: both nonzero
          have hd0 : nthDigitLSD z 0 = nthDigitLSD w 0 := h 0 (Nat.zero_lt_succ k)
          simp only [nthDigitLSD] at hd0
          conv at hd0 => lhs; rw [toDigits]; simp only [hz, ↓reduceDIte]
          conv at hd0 => rhs; rw [toDigits]; simp only [hw, ↓reduceDIte]
          simp only [List.getD_cons_zero] at hd0
          -- First digits agree
          have hd : digit z = digit w := hd0
          -- Use βQuot_sub
          rw [βQuot_sub z w hd, pow_succ, mul_comm]
          apply mul_dvd_mul_left
          -- Apply IH
          rw [← ih]
          intro n hn
          have := h (n + 1) (Nat.succ_lt_succ hn)
          rw [nthDigitLSD_succ z n, nthDigitLSD_succ w n] at this
          exact this
    · -- β^(k+1) | (z - w) → lsdAgree z w (k+1)
      intro h
      intro n hn
      -- β^(k+1) | (z - w) implies β | (z - w)
      have hβ : β ∣ (z - w) := dvd_trans (dvd_pow_self β (Nat.succ_ne_zero k)) h
      have hd : digit z = digit w := β_dvd_sub_imp_digit_eq z w hβ
      cases n with
      | zero =>
        by_cases hz : z = 0
        · subst hz
          have hw0 : digit w = false := by
            -- digit 0 = digit w
            simpa [digit_zero] using hd.symm
          by_cases hw : w = 0
          · subst hw
            simp [nthDigitLSD, toDigits]
          · -- w ≠ 0
            simp [nthDigitLSD_zero, nthDigitLSD_zero_eq w hw, hw0]
        · by_cases hw : w = 0
          · subst hw
            have hz0 : digit z = false := by
              simpa [digit_zero] using hd
            simp [nthDigitLSD_zero, nthDigitLSD_zero_eq z hz, hz0]
          · -- both nonzero
            simp [nthDigitLSD_zero_eq z hz, nthDigitLSD_zero_eq w hw, hd]
      | succ n =>
        have hn' : n < k := Nat.lt_of_succ_lt_succ hn
        rw [nthDigitLSD_succ z n, nthDigitLSD_succ w n]
        have hβ0 : (β : GaussianInt) ≠ 0 := by
          intro h0
          have : (-1 : ℤ) = 0 := by
            simpa [β] using congrArg Zsqrtd.re h0
          linarith
        have hdiv : β^k ∣ (βQuot z - βQuot w) := by
          have h' : β * (β^k) ∣ β * (βQuot z - βQuot w) := by
            simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm, βQuot_sub z w hd] using h
          exact (mul_dvd_mul_iff_left hβ0).1 h'
        have hagree : lsdAgree (βQuot z) (βQuot w) k := (ih (βQuot z) (βQuot w)).2 hdiv
        exact hagree n hn'

/-- Bridge lemma: nthDigitMSD is getD on reversed list -/
theorem nthDigitMSD_eq_getD_reverse (z : GaussianInt) (n : ℕ) :
    nthDigitMSD z n = (toDigits z).reverse.getD n false := by
  simp only [nthDigitMSD, List.getD_eq_getElem?_getD]
  split_ifs with h
  · have h' : n < (toDigits z).reverse.length := by simp [h]
    simp only [List.getElem?_eq_getElem h', Option.getD_some, List.get_eq_getElem]
  · have h' : (toDigits z).reverse.length ≤ n := by simp; omega
    simp only [List.getElem?_eq_none h', Option.getD_none]

/-- MSD agreement ↔ prefix equality (KEY THEOREM for prefix topology) -/
theorem msd_agree_of_same_length (z w : GaussianInt) (m : ℕ)
    (hlen : digitLength z = digitLength w) :
    msdAgree z w m ↔ msdPrefix z m = msdPrefix w m := by
  simp only [msdAgree, msdPrefix]
  have hlen' : (toDigits z).reverse.length = (toDigits w).reverse.length := by
    simp only [List.length_reverse]; exact hlen
  constructor
  · -- Forward: pointwise agreement → prefix equality
    intro ⟨_, h⟩
    apply List.ext_getElem?
    intro n
    simp only [List.getElem?_take]
    split_ifs with hn_m
    · specialize h n hn_m
      rw [nthDigitMSD_eq_getD_reverse, nthDigitMSD_eq_getD_reverse] at h
      simp only [List.getD_eq_getElem?_getD] at h
      by_cases hn_len : n < (toDigits z).reverse.length
      · have hn_len_w : n < (toDigits w).reverse.length := hlen' ▸ hn_len
        simp only [List.getElem?_eq_getElem hn_len, List.getElem?_eq_getElem hn_len_w,
                   Option.getD_some] at h ⊢
        exact congrArg some h
      · have hn_len_w : ¬ n < (toDigits w).reverse.length := by
          simp only [hlen'] at hn_len; exact hn_len
        simp only [List.getElem?_eq_none (Nat.not_lt.mp hn_len),
                   List.getElem?_eq_none (Nat.not_lt.mp hn_len_w)]
    · rfl
  · -- Backward: prefix equality → pointwise agreement
    intro h
    refine ⟨hlen, fun n hn => ?_⟩
    rw [nthDigitMSD_eq_getD_reverse, nthDigitMSD_eq_getD_reverse]
    simp only [List.getD_eq_getElem?_getD]
    have h' := congrArg (·[n]?) h
    simp only [List.getElem?_take, hn, ↓reduceIte] at h'
    by_cases hn_len : n < (toDigits z).reverse.length
    · have hn_len_w : n < (toDigits w).reverse.length := hlen' ▸ hn_len
      simp only [List.getElem?_eq_getElem hn_len, List.getElem?_eq_getElem hn_len_w] at h' ⊢
      simp only [Option.some.injEq] at h'
      simp only [Option.getD_some, h']
    · have hn_len_w : ¬ n < (toDigits w).reverse.length := by
        simp only [hlen'] at hn_len; exact hn_len
      simp only [List.getElem?_eq_none (Nat.not_lt.mp hn_len),
                 List.getElem?_eq_none (Nat.not_lt.mp hn_len_w), Option.getD_none]

/-! ## Leading Digit Property -/

/-- If βQuot z = 0 and z ≠ 0, then digit z = true.
    This is because z = (if digit z then 1 else 0) + β * 0 = (if digit z then 1 else 0).
    If digit z = false, then z = 0, contradiction. -/
theorem digit_true_of_βQuot_zero (z : GaussianInt) (hz : z ≠ 0) (hq : βQuot z = 0) :
    digit z = true := by
  have hspec := digit_βQuot_spec z
  rw [hq, mul_zero, add_zero] at hspec
  by_cases hd : digit z
  · exact hd
  · simp only [hd, ↓reduceIte] at hspec
    exact absurd hspec hz

/-- Helper: toDigits structure for nonzero z -/
theorem toDigits_cons (z : GaussianInt) (hz : z ≠ 0) :
    toDigits z = digit z :: toDigits (βQuot z) := by
  conv_lhs => unfold toDigits
  simp only [hz, ↓reduceDIte]

/-- Helper lemma: getLast of a cons with nonempty tail -/
private lemma getLast_cons_of_ne_nil {α : Type*} (a : α) (l : List α) (hl : l ≠ []) :
    (a :: l).getLast (List.cons_ne_nil a l) = l.getLast hl := by
  exact List.getLast_cons hl

/-- Helper: getLast' that doesn't require proof in type -/
private def getLast' (l : List Bool) : Bool :=
  match l with
  | [] => false
  | [a] => a
  | _ :: t => getLast' t

private theorem getLast'_eq_getLast (l : List Bool) (hl : l ≠ []) :
    getLast' l = l.getLast hl := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a t ih =>
    cases t with
    | nil => simp only [getLast', List.getLast_singleton]
    | cons b t' =>
      simp only [getLast', List.getLast_cons (List.cons_ne_nil b t')]
      exact ih (List.cons_ne_nil b t')

/-- The last element of toDigits z (the leading/MSD digit) is true for z ≠ 0.
    Proof by strong induction on terminationMeasure. -/
theorem toDigits_getLast_true (z : GaussianInt) (hz : z ≠ 0) :
    (toDigits z).getLast (toDigits_nonempty z hz) = true := by
  rw [← getLast'_eq_getLast]
  -- Strong induction: prove getLast' (toDigits w) = true for all nonzero w
  suffices h : ∀ n w, terminationMeasure w = n → w ≠ 0 → getLast' (toDigits w) = true by
    exact h (terminationMeasure z) z rfl hz
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hw_meas hw_ne
    by_cases hq : βQuot w = 0
    · -- βQuot w = 0, so toDigits w = [digit w]
      have h_struct : toDigits w = [digit w] := by
        rw [toDigits_cons w hw_ne, hq, toDigits_zero]
      simp only [h_struct, getLast']
      exact digit_true_of_βQuot_zero w hw_ne hq
    · -- βQuot w ≠ 0, recurse
      have h_nonempty : toDigits (βQuot w) ≠ [] := toDigits_nonempty (βQuot w) hq
      have h_struct : toDigits w = digit w :: toDigits (βQuot w) := toDigits_cons w hw_ne
      have h_dec : terminationMeasure (βQuot w) < terminationMeasure w :=
        terminationMeasure_decrease w hw_ne
      have h_dec' : terminationMeasure (βQuot w) < n := by omega
      have ih_βQuot := ih (terminationMeasure (βQuot w)) h_dec' (βQuot w) rfl hq
      rw [h_struct]
      -- getLast' (a :: t) = getLast' t when t ≠ []
      cases ht : toDigits (βQuot w) with
      | nil => exact absurd ht h_nonempty
      | cons b t' =>
        simp only [getLast']
        rw [ht] at ih_βQuot
        exact ih_βQuot

/-- The MSD (index 0 from most significant end) of nonzero z is true -/
theorem nthDigitMSD_zero_true (z : GaussianInt) (hz : z ≠ 0) :
    nthDigitMSD z 0 = true := by
  simp only [nthDigitMSD]
  have h_len : digitLength z > 0 := digitLength_pos z hz
  have h_lt : 0 < (toDigits z).length := h_len
  simp only [h_lt, ↓reduceDIte]
  have h_ne : toDigits z ≠ [] := toDigits_nonempty z hz
  have h_lt_rev : 0 < (toDigits z).reverse.length := by
    simp only [List.length_reverse]; exact h_lt
  -- (toDigits z).reverse.get ⟨0, _⟩ = (toDigits z).getLast _
  have h_rev : (toDigits z).reverse.get ⟨0, h_lt_rev⟩ = (toDigits z).getLast h_ne := by
    rw [List.get_eq_getElem, List.getElem_reverse]
    simp only [List.length_reverse, Nat.sub_zero, Nat.sub_self]
    exact (List.getLast_eq_getElem (toDigits z) h_ne).symm
  rw [h_rev]
  exact toDigits_getLast_true z hz

/-! ## Digit Pattern Theorems -/

/-- The digit at position n is false for all n ≥ digitLength z -/
theorem nthDigitLSD_beyond_length (z : GaussianInt) (n : ℕ) (hn : digitLength z ≤ n) :
    nthDigitLSD z n = false := by
  simp only [nthDigitLSD, digitLength]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · simp
  · exact hn

/-- Two elements with same toDigits are equal -/
theorem eq_of_toDigits_eq (z w : GaussianInt) (h : toDigits z = toDigits w) : z = w := by
  have hz := evalDigits_toDigits z
  have hw := evalDigits_toDigits w
  rw [h] at hz
  exact hz.symm.trans hw

/-- toDigits is injective -/
theorem toDigits_injective : Function.Injective toDigits := eq_of_toDigits_eq

/-- For a canonical digit list (non-empty with last element true), toDigits inverts evalDigits.
    This is the converse of evalDigits_toDigits for canonical lists. -/
theorem toDigits_evalDigits_of_canonical (ds : List Bool) (hds : ds ≠ [])
    (hlast : ds.getLast hds = true) : toDigits (evalDigits ds) = ds := by
  induction ds with
  | nil => exact absurd rfl hds
  | cons d ds' ih =>
    simp only [evalDigits]
    by_cases hds' : ds' = []
    · subst hds'
      simp only [evalDigits, mul_zero, add_zero]
      cases hd : d with
      | false =>
        subst hd
        simp only [List.getLast_singleton] at hlast
        exact absurd hlast (by decide)
      | true =>
        subst hd
        simp only [ite_true]
        have h1_ne : (1 : GaussianInt) ≠ 0 := by decide
        rw [toDigits]
        simp only [h1_ne, ↑reduceDIte]
        have h_digit_1 : digit (1 : GaussianInt) = true := by native_decide
        have h_βQuot_1 : βQuot (1 : GaussianInt) = 0 := by native_decide
        rw [h_digit_1, h_βQuot_1, toDigits_zero]
    · have hds'_ne : ds' ≠ [] := hds'
      have hlast' : ds'.getLast hds'_ne = true := by
        have h := hlast
        simp only [List.getLast_cons hds'_ne] at h
        exact h
      have ih_result := ih hds'_ne hlast'
      have heval_ne : evalDigits ds' ≠ 0 := by
        intro h_eq
        have : toDigits (evalDigits ds') = [] := by rw [h_eq, toDigits_zero]
        rw [ih_result] at this
        exact hds'_ne this
      have hne : (if d then 1 else 0) + β * evalDigits ds' ≠ 0 := by
        intro h_eq
        cases hd : d with
        | false =>
          subst hd
          have hf : (false = true) = False := by decide
          simp only [hf, ite_false, zero_add] at h_eq
          have hβ_ne : β ≠ 0 := by decide
          have := mul_eq_zero.mp h_eq
          cases this with
          | inl h => exact hβ_ne h
          | inr h => exact heval_ne h
        | true =>
          subst hd
          simp only [ite_true] at h_eq
          have h1_ne : (1 : GaussianInt) ≠ 0 := by decide
          have h1_add : (1 : GaussianInt) = (1 + β * evalDigits ds') - β * evalDigits ds' := by ring
          rw [h_eq] at h1_add
          simp only [zero_sub] at h1_add
          have h1_neg : -1 = β * evalDigits ds' := by
            have : -(β * evalDigits ds') = (1 : GaussianInt) := h1_add.symm
            rw [← neg_neg (β * evalDigits ds'), this]
          have hβ_dvd : β ∣ -1 := ⟨evalDigits ds', h1_neg⟩
          rw [β_dvd_iff] at hβ_dvd
          simp only [Zsqrtd.neg_re, Zsqrtd.one_re, Zsqrtd.neg_im, Zsqrtd.one_im, neg_zero] at hβ_dvd
          norm_num at hβ_dvd
      rw [toDigits]
      simp only [hne, ↑reduceDIte]
      have h_digit_eq : digit ((if d then 1 else 0) + β * evalDigits ds') = d := by
        cases hd : d with
        | false =>
          subst hd
          have hf : (false = true) = False := by decide
          simp only [hf, ite_false, zero_add]
          exact digit_β_mul (evalDigits ds')
        | true =>
          subst hd
          simp only [ite_true]
          exact digit_one_add_β_mul (evalDigits ds')
      have h_βQuot_eq : βQuot ((if d then 1 else 0) + β * evalDigits ds') = evalDigits ds' := by
        cases hd : d with
        | false =>
          subst hd
          have hf : (false = true) = False := by decide
          simp only [hf, ite_false, zero_add]
          exact βQuot_β_mul (evalDigits ds')
        | true =>
          subst hd
          simp only [ite_true]
          exact βQuot_one_add_β_mul (evalDigits ds')
      rw [h_digit_eq, h_βQuot_eq, ih_result]

/-! ## BREAKTHROUGH: Algebraic-Topological Correspondence -/

/-- The digit function determines parity: digit z = true iff z has "odd" parity
    (meaning re % 2 ≠ im % 2) -/
theorem digit_parity_characterization (z : GaussianInt) :
    digit z = true ↔ z.re % 2 ≠ z.im % 2 := by
  simp only [digit, ne_eq, decide_eq_true_eq]

/-- βQuot preserves a "twisted parity" structure -/
theorem βQuot_parity_relation (z : GaussianInt) :
    (βQuot z).re % 2 = (βQuot z).im % 2 ↔ digit (βQuot z) = false := by
  rw [digit_false_iff, β_dvd_iff]

/-- Norm is multiplicative for β -/
theorem norm_mul_β (z : GaussianInt) : (β * z).norm = 2 * z.norm := by
  rw [Zsqrtd.norm_mul, norm_β]

/-- digitLength is bounded below by log of norm (weak form) -/
theorem digitLength_ge_one_of_norm_ge_two (z : GaussianInt) (h : z.norm ≥ 2) :
    digitLength z ≥ 1 := by
  by_contra hc
  push_neg at hc
  have : digitLength z = 0 := Nat.lt_one_iff.mp hc
  have hz : z = 0 := by
    by_contra hne
    have := digitLength_pos z hne
    omega
  subst hz
  simp only [norm_eq, Zsqrtd.zero_re, Zsqrtd.zero_im, mul_zero, add_zero] at h
  omega

/-- Helper: digitLength of nonzero z equals 1 + digitLength of βQuot z -/
theorem digitLength_succ (z : GaussianInt) (hz : z ≠ 0) :
    digitLength z = 1 + digitLength (βQuot z) := by
  simp only [digitLength]
  conv_lhs => rw [toDigits]; simp only [hz, ↓reduceDIte]
  simp only [List.length_cons]
  ring

/-- Key structural property: digitLength is bounded by terminationMeasure.
    Proof by strong induction on terminationMeasure. -/
theorem digitLength_le_terminationMeasure (z : GaussianInt) :
    digitLength z ≤ terminationMeasure z := by
  -- We prove the stronger statement by strong induction on n = terminationMeasure z
  suffices h : ∀ n z, terminationMeasure z = n → digitLength z ≤ n by
    exact h (terminationMeasure z) z rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z hz_meas
    by_cases hz : z = 0
    · -- Base case: z = 0
      subst hz
      simp only [digitLength_zero]
      exact Nat.zero_le n
    · -- Inductive case: z ≠ 0
      -- digitLength z = 1 + digitLength (βQuot z)
      rw [digitLength_succ z hz]
      -- terminationMeasure (βQuot z) < terminationMeasure z = n
      have h_dec : terminationMeasure (βQuot z) < n := by
        have := terminationMeasure_decrease z hz
        omega
      -- By IH: digitLength (βQuot z) ≤ terminationMeasure (βQuot z)
      have h_ih : digitLength (βQuot z) ≤ terminationMeasure (βQuot z) :=
        ih (terminationMeasure (βQuot z)) h_dec (βQuot z) rfl
      -- Need: 1 + digitLength (βQuot z) ≤ n
      -- Since terminationMeasure (βQuot z) < n,
      -- we have 1 + terminationMeasure (βQuot z) ≤ n
      omega

/-! ## BREAKTHROUGH: β-adic Valuation -/

/-- β is nonzero -/
theorem β_ne_zero : (β : GaussianInt) ≠ 0 := by
  intro h
  have : (-1 : ℤ) = 0 := congrArg Zsqrtd.re h
  omega

/-- The β-adic valuation: count of leading false digits.
    Defined recursively: if digit z = true, val = 0; else val = 1 + val(βQuot z) -/
noncomputable def βVal (z : GaussianInt) : ℕ :=
  if hz : z = 0 then 0
  else if digit z then 0
  else 1 + βVal (βQuot z)
termination_by terminationMeasure z
decreasing_by exact terminationMeasure_decrease z hz

/-- βVal of 0 is 0 -/
theorem βVal_zero : βVal 0 = 0 := by
  unfold βVal
  simp

/-- If first digit is true, βVal is 0 -/
theorem βVal_zero_of_digit_true (z : GaussianInt) (hz : z ≠ 0) (hd : digit z = true) :
    βVal z = 0 := by
  unfold βVal
  simp [hz, hd]

/-- If first digit is false (and z ≠ 0), βVal > 0 -/
theorem βVal_pos_of_digit_false (z : GaussianInt) (hz : z ≠ 0) (hd : digit z = false) :
    0 < βVal z := by
  have : βVal z = 1 + βVal (βQuot z) := by
    conv_lhs => unfold βVal
    simp only [hz, hd, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]
  omega

/-- βVal of β * z equals 1 + βVal z (for z ≠ 0) -/
theorem βVal_mul_β (z : GaussianInt) (hz : z ≠ 0) :
    βVal (β * z) = 1 + βVal z := by
  have hβz_ne : β * z ≠ 0 := mul_ne_zero β_ne_zero hz
  have h_digit : digit (β * z) = false := by
    rw [digit_false_iff]; exact dvd_mul_right β z
  have h_βQuot : βQuot (β * z) = z := by
    have hspec := digit_βQuot_spec (β * z)
    simp only [h_digit, Bool.false_eq_true, ↓reduceIte, zero_add] at hspec
    exact mul_left_cancel₀ β_ne_zero hspec.symm
  conv_lhs => unfold βVal
  simp only [hβz_ne, h_digit, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte, h_βQuot]

/-- βVal of β^k * z equals k + βVal z (for z ≠ 0) -/
theorem βVal_pow_mul (z : GaussianInt) (hz : z ≠ 0) (k : ℕ) :
    βVal (β^k * z) = k + βVal z := by
  induction k with
  | zero => simp only [pow_zero, one_mul, Nat.zero_add]
  | succ k ih =>
    have hβkz_ne : β^k * z ≠ 0 := mul_ne_zero (pow_ne_zero k β_ne_zero) hz
    calc βVal (β^(k+1) * z)
        = βVal (β * (β^k * z)) := by ring_nf
      _ = 1 + βVal (β^k * z) := βVal_mul_β (β^k * z) hβkz_ne
      _ = 1 + (k + βVal z) := by rw [ih]
      _ = (k + 1) + βVal z := by ring

/-- βVal characterization: β^(βVal z) | z -/
theorem βVal_dvd (z : GaussianInt) : β^(βVal z) ∣ z := by
  by_cases hz : z = 0
  · simp [hz]
  · -- Strong induction on βVal z
    generalize hv : βVal z = v at *
    induction v generalizing z with
    | zero =>
      simp only [pow_zero, one_dvd]
    | succ n ih =>
      -- βVal z = n + 1 means digit z = false
      have h_digit : digit z = false := by
        by_contra hd
        push_neg at hd
        have := βVal_zero_of_digit_true z hz (eq_true_of_ne_false hd)
        omega
      -- z = β * βQuot z
      have hz_eq : z = β * βQuot z := by
        have hspec := digit_βQuot_spec z
        simp only [h_digit, Bool.false_eq_true, ↓reduceIte, zero_add] at hspec
        exact hspec
      -- βVal (βQuot z) = n
      have h_βQuot_ne : βQuot z ≠ 0 := by
        intro hq
        rw [hq, mul_zero] at hz_eq
        exact hz hz_eq
      have h_val_βQuot : βVal (βQuot z) = n := by
        have := βVal_mul_β (βQuot z) h_βQuot_ne
        rw [← hz_eq] at this
        omega
      -- By IH: β^n | βQuot z
      have ih_app := ih (βQuot z) h_βQuot_ne h_val_βQuot
      -- So β^(n+1) | β * βQuot z = z
      rw [hz_eq, pow_succ, mul_comm]
      exact mul_dvd_mul_left β ih_app

/-! ## BREAKTHROUGH: Digit-Norm Duality -/

/-- digitLength z ≥ 1 for nonzero z (restatement) -/
theorem digitLength_ge_one (z : GaussianInt) (hz : z ≠ 0) : digitLength z ≥ 1 := by
  have := digitLength_pos z hz
  omega

/-- The first k digits being false implies β^k | z -/
theorem first_k_false_imp_dvd (z : GaussianInt) (k : ℕ)
    (h : ∀ i < k, nthDigitLSD z i = false) : β^k ∣ z := by
  have h_agree : lsdAgree z 0 k := fun n hn => by rw [h n hn, nthDigitLSD_zero]
  rw [lsd_agree_iff_pow_dvd] at h_agree
  simpa using h_agree

/-- β^k | z implies the first k digits are false -/
theorem dvd_imp_first_k_false (z : GaussianInt) (k : ℕ) (h : β^k ∣ z) :
    ∀ i < k, nthDigitLSD z i = false := by
  intro i hi
  have h' : β^k ∣ z - 0 := by simpa using h
  have h_agree : lsdAgree z 0 k := (lsd_agree_iff_pow_dvd z 0 k).mpr h'
  have := h_agree i hi
  rw [nthDigitLSD_zero] at this
  exact this

/-- Characterization: β^k | z ↔ first k digits are all false -/
theorem pow_dvd_iff_first_k_false (z : GaussianInt) (k : ℕ) :
    β^k ∣ z ↔ ∀ i < k, nthDigitLSD z i = false := by
  constructor
  · exact dvd_imp_first_k_false z k
  · exact first_k_false_imp_dvd z k

/-! ## BREAKTHROUGH: Additive Structure -/

/-- Addition preserves cylinder membership modulo: if z₁, z₂ ∈ same cylinder,
    then z₁ + c, z₂ + c are in same cylinder -/
theorem add_preserves_lsdAgree (z w c : GaussianInt) (k : ℕ) (h : lsdAgree z w k) :
    lsdAgree (z + c) (w + c) k := by
  rw [lsd_agree_iff_pow_dvd] at h ⊢
  have : (z + c) - (w + c) = z - w := by ring
  rw [this]
  exact h

/-- Negation preserves lsdAgree with 0 -/
theorem neg_lsdAgree_zero (z : GaussianInt) (k : ℕ) (h : lsdAgree z 0 k) :
    lsdAgree (-z) 0 k := by
  rw [lsd_agree_iff_pow_dvd] at h ⊢
  simp only [sub_zero] at h ⊢
  exact dvd_neg.mpr h

/-! ## BREAKTHROUGH: βVal Maximality -/

/-- If digit z = true (z ≠ 0), then β does NOT divide z -/
theorem not_β_dvd_of_digit_true (z : GaussianInt) (hd : digit z = true) : ¬(β ∣ z) := by
  exact (digit_true_iff z).mp hd

/-- βVal is maximal: β^(βVal z + 1) does NOT divide z (for nonzero z with digit true) -/
theorem βVal_maximal_aux (z : GaussianInt) (hz : z ≠ 0) (hd : digit z = true) :
    ¬(β^(βVal z + 1) ∣ z) := by
  have hval : βVal z = 0 := βVal_zero_of_digit_true z hz hd
  rw [hval]
  simp only [Nat.zero_add, pow_one]
  exact not_β_dvd_of_digit_true z hd

/-- βVal is exactly the maximum k such that β^k | z (for nonzero z) -/
theorem βVal_is_max (z : GaussianInt) (hz : z ≠ 0) :
    β^(βVal z) ∣ z ∧ ¬(β^(βVal z + 1) ∣ z) := by
  constructor
  · exact βVal_dvd z
  · -- Prove ¬(β^(βVal z + 1) ∣ z)
    -- Key: z = β^(βVal z) * u where u has digit true (not divisible by β)
    generalize hv : βVal z = v
    induction v generalizing z with
    | zero =>
      -- βVal z = 0 means digit z = true
      have hd : digit z = true := by
        by_contra hd_false
        push_neg at hd_false
        have := βVal_pos_of_digit_false z hz (eq_false_of_ne_true hd_false)
        omega
      simp only [Nat.zero_add, pow_one]
      exact not_β_dvd_of_digit_true z hd
    | succ n ih =>
      -- βVal z = n + 1 means digit z = false, so z = β * βQuot z
      have hd : digit z = false := by
        by_contra hd_true
        push_neg at hd_true
        have := βVal_zero_of_digit_true z hz (eq_true_of_ne_false hd_true)
        omega
      have hz_eq : z = β * βQuot z := by
        have hspec := digit_βQuot_spec z
        simp only [hd, Bool.false_eq_true, ↓reduceIte, zero_add] at hspec
        exact hspec
      have hq_ne : βQuot z ≠ 0 := by
        intro hq
        rw [hq, mul_zero] at hz_eq
        exact hz hz_eq
      have hq_val : βVal (βQuot z) = n := by
        have := βVal_mul_β (βQuot z) hq_ne
        rw [← hz_eq] at this
        omega
      -- By IH: ¬(β^(n+1) ∣ βQuot z)
      have ih_app := ih (βQuot z) hq_ne hq_val
      -- Need: ¬(β^(n+2) ∣ z)
      intro hdiv
      -- β^(n+2) ∣ z = β * βQuot z means β^(n+2) ∣ β * βQuot z
      -- So β^(n+1) ∣ βQuot z (canceling one β)
      have hdiv' : β^(n+1) ∣ βQuot z := by
        rw [hz_eq, pow_succ, pow_succ] at hdiv
        have : β * β^n * β ∣ β * βQuot z := by
          convert hdiv using 1; ring
        have hβne : (β : GaussianInt) ≠ 0 := β_ne_zero
        exact (mul_dvd_mul_iff_left hβne).mp (by convert hdiv using 1; ring)
      exact ih_app hdiv'

/-- Alternative characterization: βVal z = k iff β^k | z and β^(k+1) ∤ z -/
theorem βVal_iff (z : GaussianInt) (hz : z ≠ 0) (k : ℕ) :
    βVal z = k ↔ β^k ∣ z ∧ ¬(β^(k+1) ∣ z) := by
  constructor
  · intro hk
    rw [← hk]
    exact βVal_is_max z hz
  · intro ⟨hdiv, hndiv⟩
    -- βVal z is the unique such k
    have hmax := βVal_is_max z hz
    by_contra hne
    cases' Nat.lt_or_gt_of_ne hne with hlt hgt
    · -- βVal z < k: then β^(βVal z + 1) | β^k | z, contradiction with hmax.2
      have h_le : βVal z + 1 ≤ k := hlt
      have h_dvd_trans : β^(βVal z + 1) ∣ β^k := pow_dvd_pow β h_le
      have : β^(βVal z + 1) ∣ z := dvd_trans h_dvd_trans hdiv
      exact hmax.2 this
    · -- βVal z > k: then β^(k+1) | β^(βVal z) | z, contradiction with hndiv
      have h_le : k + 1 ≤ βVal z := hgt
      have h_dvd_trans : β^(k+1) ∣ β^(βVal z) := pow_dvd_pow β h_le
      have : β^(k+1) ∣ z := dvd_trans h_dvd_trans hmax.1
      exact hndiv this

/-! ## BREAKTHROUGH: Multiplication Structure -/

/-- βVal of a product is at least the sum of βVals -/
theorem βVal_mul_ge (z w : GaussianInt) (hz : z ≠ 0) (hw : w ≠ 0) :
    βVal (z * w) ≥ βVal z + βVal w := by
  have hzw_ne : z * w ≠ 0 := mul_ne_zero hz hw
  -- β^(βVal z) | z and β^(βVal w) | w
  -- So β^(βVal z + βVal w) | z * w
  have hdiv_z := βVal_dvd z
  have hdiv_w := βVal_dvd w
  have hdiv_prod : β^(βVal z + βVal w) ∣ z * w := by
    rw [pow_add]
    exact mul_dvd_mul hdiv_z hdiv_w
  -- Since βVal is maximal, βVal (z * w) ≥ βVal z + βVal w
  by_contra hlt
  push_neg at hlt
  have hmax := βVal_is_max (z * w) hzw_ne
  -- β^(βVal(z*w) + 1) ∤ z*w, but β^(βVal z + βVal w) | z*w
  -- If βVal(z*w) + 1 ≤ βVal z + βVal w, then β^(βVal(z*w)+1) | z*w, contradiction
  have h_pow_dvd : β^(βVal (z * w) + 1) ∣ β^(βVal z + βVal w) := pow_dvd_pow β (by omega)
  have : β^(βVal (z * w) + 1) ∣ z * w := dvd_trans h_pow_dvd hdiv_prod
  exact hmax.2 this

/-! ## Summary

### Fully Proven (no sorry):
1. `β = -1 + i` with `norm_β : β.norm = 2`
2. `β_dvd_iff`: β | z ↔ z.re % 2 = z.im % 2
3. `digit`, `digit_false_iff`, `digit_true_iff`: Digit function
4. `βQuotAux`, `β_mul_βQuotAux`: Quotient helper
5. `βQuot`, `digit_βQuot_spec`: Fundamental recurrence z = d + β * q
6. `norm_eq`, `norm_nonneg`, `norm_pos`, `norm_eq_zero_iff`: Norm properties
7. `norm_βQuotAux`, `norm_βQuotAux_lt`: Norm decrease for even parity
8. `baseMeasure`, `terminationMeasure`: Hybrid termination measure definition
9. `toDigits`, `evalDigits`, `evalDigits_toDigits`: Canonical representation
10. `digitLength`, `nthDigitLSD`, `nthDigitMSD`: Digit access
11. `lsdPrefix`, `msdPrefix`, `lsdAgree`, `msdAgree`: Topology primitives
12. `digit_agree_imp_β_dvd`, `β_dvd_sub_imp_digit_eq`: Digit agreement ↔ β divisibility
13. `lsd_agree_iff_pow_dvd`: LSD agreement ↔ β^k divisibility
14. `msd_agree_of_same_length`: MSD agreement ↔ prefix equality (when lengths match)

### Foundation for Topology:
The proven results provide the basis for defining:
- **Suffix topology**: neighborhoods based on LSD agreement (β^k divisibility)
- **Prefix topology**: neighborhoods based on MSD agreement (digit length + prefix)
-/

end SPBiTopology
