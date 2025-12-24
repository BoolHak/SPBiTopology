/-
  BiTopology/SPBiTopology/SuffixCylinders.lean

  SUFFIX CYLINDER CHARACTERIZATIONS

  Defines odd and even suffix cylinders and proves their characterizations
  in terms of parity. These are reusable for any parity-based analysis.
-/

import BiTopology.SPBiTopology.Parity

set_option autoImplicit false

namespace SPBiTopology

open Zsqrtd

/-! ## Section 1: Odd and Even Suffix Cylinders -/

/-- The suffix cylinder for odd integers (first digit = true) -/
def oddSuffixCylinder : Set GaussianInt :=
  SuffixCylinder 1 (fun _ => true)

/-- The suffix cylinder for even integers (first digit = false) -/
def evenSuffixCylinder : Set GaussianInt :=
  SuffixCylinder 1 (fun _ => false)

/-! ## Section 2: Membership Characterizations -/

/-- Membership in oddSuffixCylinder means first digit is true -/
theorem mem_oddSuffixCylinder_iff_digit (z : GaussianInt) :
    z ∈ oddSuffixCylinder ↔ (z = 0 → False) ∧ digit z = true := by
  simp only [oddSuffixCylinder, SuffixCylinder, Set.mem_setOf_eq]
  constructor
  · intro h
    have h0 := h ⟨0, Nat.zero_lt_one⟩
    simp only [Fin.val_zero] at h0
    constructor
    · intro hz
      rw [hz, nthDigitLSD_zero] at h0
      exact Bool.false_ne_true h0
    · by_cases hz : z = 0
      · rw [hz, nthDigitLSD_zero] at h0; exact absurd h0 Bool.false_ne_true
      · rw [nthDigitLSD_zero_eq z hz] at h0; exact h0
  · intro ⟨hz, hd⟩ j
    have hne : z ≠ 0 := fun h => hz h
    cases' j with j hj
    cases j with
    | zero => rw [nthDigitLSD_zero_eq z hne]; exact hd
    | succ j => exact absurd hj (by omega)

/-- For nonzero integers: in oddSuffixCylinder iff odd -/
theorem mem_oddSuffixCylinder_int (n : ℤ) (hn : n ≠ 0) :
    ofInt n ∈ oddSuffixCylinder ↔ ¬ 2 ∣ n := by
  rw [mem_oddSuffixCylinder_iff_digit]
  have hne : ofInt n ≠ 0 := by
    intro h
    have : (ofInt n).re = 0 := congrArg Zsqrtd.re h
    simp only [ofInt, Zsqrtd.zero_re] at this
    exact hn this
  constructor
  · intro ⟨_, hd⟩
    simp only [ofInt, digit, ne_eq, decide_eq_true_eq] at hd
    intro ⟨k, hk⟩
    have : n % 2 = 0 := by omega
    omega
  · intro hodd
    refine ⟨fun h => hne h, ?_⟩
    simp only [ofInt, digit, ne_eq, decide_eq_true_eq]
    omega

/-- Membership in evenSuffixCylinder means first digit is false -/
theorem mem_evenSuffixCylinder_iff_digit (z : GaussianInt) :
    z ∈ evenSuffixCylinder ↔ z = 0 ∨ digit z = false := by
  simp only [evenSuffixCylinder, SuffixCylinder, Set.mem_setOf_eq]
  constructor
  · intro h
    have h0 := h ⟨0, Nat.zero_lt_one⟩
    simp only [Fin.val_zero] at h0
    by_cases hz : z = 0
    · left; exact hz
    · right; rw [nthDigitLSD_zero_eq z hz] at h0; exact h0
  · intro h j
    cases' j with j hj
    cases j with
    | zero =>
      rcases h with hz | hd
      · rw [hz, nthDigitLSD_zero]
      · by_cases hz : z = 0
        · rw [hz, nthDigitLSD_zero]
        · rw [nthDigitLSD_zero_eq z hz]; exact hd
    | succ j => exact absurd hj (by omega)

/-- For integers: in evenSuffixCylinder iff even -/
theorem mem_evenSuffixCylinder_int (n : ℤ) :
    ofInt n ∈ evenSuffixCylinder ↔ 2 ∣ n := by
  rw [mem_evenSuffixCylinder_iff_digit]
  constructor
  · intro h
    rcases h with hz | hd
    · simp only [ofInt, Zsqrtd.ext_iff] at hz
      have : n = 0 := hz.1
      subst this; exact ⟨0, rfl⟩
    · simp only [ofInt, digit, ne_eq, decide_eq_false_iff_not, not_not] at hd
      use n / 2; omega
  · intro ⟨k, hk⟩
    by_cases hn : n = 0
    · left; simp only [ofInt, hn]; rfl
    · right
      simp only [ofInt, digit, ne_eq, decide_eq_false_iff_not, not_not]
      omega

/-! ## Section 3: Cylinder Membership for Primes -/

/-- Odd primes are in the odd suffix cylinder -/
theorem oddPrime_in_oddSuffixCylinder (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    ofInt p ∈ oddSuffixCylinder := by
  rw [mem_oddSuffixCylinder_int]
  · intro ⟨k, hk⟩
    have : 2 ∣ p := by use k.natAbs; cases' Int.natAbs_eq k with h h <;> omega
    rcases hp.eq_one_or_self_of_dvd 2 this with h | h
    · omega
    · exact hp2 h.symm
  · have := hp.pos; omega

/-- Even integers are in the even suffix cylinder -/
theorem even_in_evenSuffixCylinder (n : ℕ) (heven : 2 ∣ n) :
    ofInt n ∈ evenSuffixCylinder := by
  rw [mem_evenSuffixCylinder_int]
  exact_mod_cast heven

/-! ## Section 4: Cylinder Complement Properties -/

/-- The odd and even cylinders partition nonzero elements -/
theorem cylinder_partition (z : GaussianInt) (hz : z ≠ 0) :
    z ∈ oddSuffixCylinder ∨ z ∈ evenSuffixCylinder := by
  by_cases hd : digit z = true
  · left; rw [mem_oddSuffixCylinder_iff_digit]; exact ⟨fun h => hz h, hd⟩
  · right; rw [mem_evenSuffixCylinder_iff_digit]
    right
    cases hd' : digit z
    · rfl
    · exact absurd hd' hd

/-- No nonzero element is in both cylinders -/
theorem cylinder_disjoint (z : GaussianInt) (hz : z ≠ 0) :
    ¬(z ∈ oddSuffixCylinder ∧ z ∈ evenSuffixCylinder) := by
  intro ⟨hodd, heven⟩
  rw [mem_oddSuffixCylinder_iff_digit] at hodd
  rw [mem_evenSuffixCylinder_iff_digit] at heven
  rcases heven with heq | hd
  · exact hz heq
  · rw [hodd.2] at hd; exact Bool.noConfusion hd

/-! ## Section 5: Summary

### Suffix Cylinder Results:
1. `oddSuffixCylinder` / `evenSuffixCylinder`: Defined as depth-1 cylinders
2. `mem_oddSuffixCylinder_int`: n ∈ oddCylinder ↔ n is odd (for n ≠ 0)
3. `mem_evenSuffixCylinder_int`: n ∈ evenCylinder ↔ n is even
4. `oddPrime_in_oddSuffixCylinder`: Odd primes are in odd cylinder
5. `cylinder_partition`, `cylinder_disjoint`: Cylinders partition nonzero elements

These characterizations are fundamental for any parity-based analysis in bi-topology.
-/

end SPBiTopology
