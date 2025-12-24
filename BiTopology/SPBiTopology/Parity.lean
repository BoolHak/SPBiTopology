/-
  BiTopology/SPBiTopology/Parity.lean

  PARITY AND DIVISIBILITY FOR INTEGERS IN BI-TOPOLOGY

  Core results about even/odd integers and their digit structure.
  These are fundamental and reusable across many applications.
-/

import BiTopology.SPBiTopology.Basic
import BiTopology.SPBiTopology.Topology

set_option autoImplicit false

namespace SPBiTopology

open Zsqrtd

/-! ## Section 1: Integer Embedding -/

/-- Real integers: embedding ℤ → ℤ[i] -/
def ofInt (n : ℤ) : GaussianInt := ⟨n, 0⟩

/-- ofInt preserves addition -/
theorem ofInt_add (a b : ℤ) : ofInt (a + b) = ofInt a + ofInt b := by
  simp only [ofInt, Zsqrtd.ext_iff, Zsqrtd.add_re, Zsqrtd.add_im]
  simp

/-- ofInt preserves subtraction -/
theorem ofInt_sub (a b : ℤ) : ofInt (a - b) = ofInt a - ofInt b := by
  simp only [ofInt, Zsqrtd.ext_iff, Zsqrtd.sub_re, Zsqrtd.sub_im]
  simp

/-- ofInt preserves negation -/
theorem ofInt_neg (a : ℤ) : ofInt (-a) = -ofInt a := by
  simp only [ofInt, Zsqrtd.ext_iff, Zsqrtd.neg_re, Zsqrtd.neg_im]
  simp

/-! ## Section 2: β-Divisibility for Integers -/

/-- For integers, β divides n iff n is even -/
theorem β_dvd_int_iff (n : ℤ) : β ∣ (⟨n, 0⟩ : GaussianInt) ↔ 2 ∣ n := by
  rw [β_dvd_iff]
  simp only [Zsqrtd.re, Zsqrtd.im, Int.emod_zero]
  constructor
  · intro h; exact Int.dvd_of_emod_eq_zero h
  · intro ⟨k, hk⟩
    simp only [hk, Int.mul_emod_right, Int.zero_emod]

/-- For real integers, β divides iff even (using ofInt) -/
theorem β_dvd_ofInt_iff (n : ℤ) : β ∣ ofInt n ↔ 2 ∣ n := by
  rw [β_dvd_iff]
  simp only [ofInt]
  constructor
  · intro h; use n / 2; omega
  · intro ⟨k, hk⟩; subst hk; simp

/-! ## Section 3: Digit Characterization of Parity -/

/-- The first digit of an integer n is true iff n is odd -/
theorem digit_int_odd (n : ℤ) : digit (⟨n, 0⟩ : GaussianInt) = true ↔ ¬ 2 ∣ n := by
  rw [digit_true_iff, β_dvd_int_iff]

/-- The first digit of an integer n is false iff n is even -/
theorem digit_int_even (n : ℤ) : digit (⟨n, 0⟩ : GaussianInt) = false ↔ 2 ∣ n := by
  rw [digit_false_iff, β_dvd_int_iff]

/-- Even integers have first digit = false (divisible by β) -/
theorem even_first_digit_false (n : ℤ) (hn : 2 ∣ n) :
    digit (ofInt n) = false := by
  rw [digit_false_iff, β_dvd_ofInt_iff]
  exact hn

/-- Odd integers have first digit = true (not divisible by β) -/
theorem odd_first_digit_true (n : ℤ) (hn : ¬ 2 ∣ n) :
    digit (ofInt n) = true := by
  simp only [ofInt, digit, ne_eq, decide_eq_true_eq]
  intro h
  apply hn
  use n / 2
  omega

/-! ## Section 4: Sum of Parities -/

/-- Sum of two odd integers is even -/
theorem sum_odd_is_even (a b : ℤ) (ha : ¬ 2 ∣ a) (hb : ¬ 2 ∣ b) :
    2 ∣ (a + b) := by
  have ha' : a % 2 = 1 := by omega
  have hb' : b % 2 = 1 := by omega
  use (a + b) / 2
  omega

/-- Sum of two odd real integers has first digit = false -/
theorem sum_odd_first_digit_false (a b : ℤ) (ha : ¬ 2 ∣ a) (hb : ¬ 2 ∣ b) :
    digit (ofInt a + ofInt b) = false := by
  have h : ofInt a + ofInt b = ofInt (a + b) := by
    simp only [ofInt, Zsqrtd.ext_iff, Zsqrtd.add_re, Zsqrtd.add_im]
    simp
  rw [h]
  exact even_first_digit_false (a + b) (sum_odd_is_even a b ha hb)

/-- Sum of two even integers is even -/
theorem sum_even_is_even (a b : ℤ) (ha : 2 ∣ a) (hb : 2 ∣ b) :
    2 ∣ (a + b) := by
  obtain ⟨ka, hka⟩ := ha
  obtain ⟨kb, hkb⟩ := hb
  use ka + kb
  omega

/-! ## Section 5: Complement Parity -/

/-- For even n and odd m, (n-m) is also odd -/
theorem complement_odd_of_odd (n m : ℕ) (heven : 2 ∣ n) (hodd : ¬ 2 ∣ m) (hm : m < n) :
    ¬ 2 ∣ (n - m) := by
  intro hdiv
  obtain ⟨k, hk⟩ := heven
  obtain ⟨j, hj⟩ := hdiv
  have hm_dvd : 2 ∣ m := by
    use k - j
    omega
  exact hodd hm_dvd

/-- For even n and even m, (n-m) is also even -/
theorem complement_even_of_even (n m : ℕ) (hn : 2 ∣ n) (hm : 2 ∣ m) :
    2 ∣ (n - m) := by
  obtain ⟨kn, hkn⟩ := hn
  obtain ⟨km, hkm⟩ := hm
  use kn - km
  omega

/-! ## Section 6: LSD Agreement for Integers -/

/-- Two integers agree on first k LSD digits iff their difference is divisible by β^k -/
theorem int_lsdAgree_iff_pow_dvd (m n : ℤ) (k : ℕ) :
    lsdAgree (⟨m, 0⟩ : GaussianInt) ⟨n, 0⟩ k ↔ β^k ∣ (⟨m - n, 0⟩ : GaussianInt) := by
  have h : (⟨m, 0⟩ : GaussianInt) - ⟨n, 0⟩ = ⟨m - n, 0⟩ := by ext <;> simp
  rw [lsd_agree_iff_pow_dvd, h]

/-- lsdAgree is reflexive -/
theorem lsdAgree_refl (z : GaussianInt) (k : ℕ) : lsdAgree z z k := by
  intro i _
  rfl

/-! ## Section 7: Summary

### Core Parity Results:
1. `β_dvd_int_iff`, `β_dvd_ofInt_iff`: β-divisibility = 2-divisibility
2. `even_first_digit_false`, `odd_first_digit_true`: Digit characterization
3. `sum_odd_is_even`: Odd + odd = even
4. `complement_odd_of_odd`: Even - odd = odd
5. `int_lsdAgree_iff_pow_dvd`: LSD agreement = β^k divisibility

These are fundamental building blocks for any bi-topological analysis.
-/

end SPBiTopology
