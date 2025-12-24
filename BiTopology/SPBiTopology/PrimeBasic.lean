/-
  BiTopology/SPBiTopology/PrimeBasic.lean

  BASIC PRIME PROPERTIES IN BI-TOPOLOGY

  Core results about primes in the bi-topological framework:
  - First digit structure
  - Mod 4 structure
  - BiCylinder finiteness for primes
-/

import BiTopology.SPBiTopology.SuffixCylinders
import Mathlib.Data.Nat.Prime.Basic

set_option autoImplicit false

namespace SPBiTopology

open Zsqrtd

/-! ## Section 1: Prime First Digit Structure -/

/-- The bi-topological signature of a natural number -/
noncomputable def biTopoSignature (n : ℕ) (k : ℕ) : Fin k → Bool :=
  fun j => nthDigitLSD (⟨n, 0⟩ : GaussianInt) j.val

/-- Odd primes have first digit true (using nthDigitLSD) -/
theorem odd_prime_first_digit (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    nthDigitLSD (⟨(p : ℤ), 0⟩ : GaussianInt) 0 = true := by
  have hp_odd : ¬ 2 ∣ (p : ℤ) := by
    intro ⟨k, hk⟩
    have : 2 ∣ p := ⟨k.natAbs, by cases' Int.natAbs_eq k with h h <;> omega⟩
    rcases hp.eq_one_or_self_of_dvd 2 this with h | h
    · omega
    · exact hp2 h.symm
  by_cases hz : (⟨(p : ℤ), 0⟩ : GaussianInt) = 0
  · simp only [Zsqrtd.ext_iff] at hz
    have hp_pos : 0 < p := hp.pos
    have : (p : ℤ) = 0 := hz.1
    omega
  · rw [nthDigitLSD_zero_eq _ hz, digit_int_odd]
    exact hp_odd

/-- Odd primes have first digit = true (using digit) -/
theorem oddPrime_first_digit (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    digit (ofInt p) = true := by
  have hodd : ¬ 2 ∣ (p : ℤ) := by
    intro ⟨k, hk⟩
    have : 2 ∣ p := by use k.natAbs; cases' Int.natAbs_eq k with h h <;> omega
    rcases hp.eq_one_or_self_of_dvd 2 this with h | h
    · omega
    · exact hp2 h.symm
  exact odd_first_digit_true p hodd

/-- Even integers have first digit = false -/
theorem even_first_digit (n : ℕ) (heven : 2 ∣ n) :
    digit (ofInt n) = false := by
  have heven' : 2 ∣ (n : ℤ) := by exact_mod_cast heven
  exact even_first_digit_false n heven'

/-! ## Section 2: Prime Mod 4 Structure -/

/-- Odd primes are ≡ 1 or 3 (mod 4) -/
theorem odd_prime_mod4 (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    p % 4 = 1 ∨ p % 4 = 3 := by
  have hp_odd : ¬ 2 ∣ p := by
    intro hdiv
    rcases hp.eq_one_or_self_of_dvd 2 hdiv with h | h
    · omega
    · exact hp2 h.symm
  have hp_mod2 : p % 2 = 1 := by omega
  omega

/-- Two odd numbers sum to a number ≡ 2 (mod 4) iff they're both ≡ 1 or both ≡ 3 (mod 4) -/
theorem sum_mod4_structure (a b : ℕ) (ha : a % 2 = 1) (hb : b % 2 = 1) :
    (a + b) % 4 = 2 ↔ (a % 4 = 1 ∧ b % 4 = 1) ∨ (a % 4 = 3 ∧ b % 4 = 3) := by
  constructor
  · intro h
    have ha4 : a % 4 = 1 ∨ a % 4 = 3 := by omega
    have hb4 : b % 4 = 1 ∨ b % 4 = 3 := by omega
    rcases ha4 with ha4 | ha4 <;> rcases hb4 with hb4 | hb4 <;> omega
  · intro h
    rcases h with ⟨ha4, hb4⟩ | ⟨ha4, hb4⟩ <;> omega

/-! ## Section 3: Prime Pair Mod 4 Compatibility -/

/-- If p, q are odd primes with p + q = n (even),
    then either both ≡ 1 (mod 4) or both ≡ 3 (mod 4) when n ≡ 2 (mod 4) -/
theorem prime_pair_mod4 (n p q : ℕ) (hn : 2 ∣ n) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hsum : p + q = n) (hn4 : n % 4 = 2) :
    (p % 4 = 1 ∧ q % 4 = 1) ∨ (p % 4 = 3 ∧ q % 4 = 3) := by
  have hp_not2 : ¬ 2 ∣ p := by
    intro hdiv
    rcases hp.eq_one_or_self_of_dvd 2 hdiv with h | h
    · omega
    · exact hp2 h.symm
  have hq_not2 : ¬ 2 ∣ q := by
    intro hdiv
    rcases hq.eq_one_or_self_of_dvd 2 hdiv with h | h
    · omega
    · exact hq2 h.symm
  have hp_odd : p % 2 = 1 := by omega
  have hq_odd : q % 2 = 1 := by omega
  have hpq4 : (p + q) % 4 = 2 := by rw [hsum]; exact hn4
  exact (sum_mod4_structure p q hp_odd hq_odd).mp hpq4

/-! ## Section 4: Prime Pair Bi-Topological Compatibility -/

/-- Prime pairs have compatible bi-topological structure -/
theorem prime_pair_biTopo_compatible (n p q : ℕ) (hn : 2 ∣ n)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hsum : p + q = n) :
    nthDigitLSD (⟨(p : ℤ), 0⟩ : GaussianInt) 0 = true ∧
    nthDigitLSD (⟨(q : ℤ), 0⟩ : GaussianInt) 0 = true ∧
    nthDigitLSD (⟨(n : ℤ), 0⟩ : GaussianInt) 0 = false := by
  refine ⟨odd_prime_first_digit p hp hp2, odd_prime_first_digit q hq hq2, ?_⟩
  have hn_pos : 0 < n := by have := hp.pos; omega
  have hz : (⟨(n : ℤ), 0⟩ : GaussianInt) ≠ 0 := by
    simp only [ne_eq, Zsqrtd.ext_iff, not_and]
    intro h; have : (n : ℤ) = 0 := h; omega
  rw [nthDigitLSD_zero_eq _ hz, digit_int_even]
  exact_mod_cast hn

/-! ## Section 5: Prime in BiCylinder Finiteness -/

/-- Primes in a given BiCylinder form a finite set -/
theorem primes_in_biCylinder_finite (k : ℕ) (suffix_pattern : Fin k → Bool)
    (len m : ℕ) (prefix_pattern : Fin m → Bool) :
    Set.Finite {p : ℕ | Nat.Prime p ∧
      (⟨(p : ℤ), 0⟩ : GaussianInt) ∈ BiCylinder k suffix_pattern len m prefix_pattern} := by
  have h := biCylinder_finite k suffix_pattern len m prefix_pattern
  let f : ℕ → GaussianInt := fun p => ⟨(p : ℤ), 0⟩
  have h_img_finite : Set.Finite (f '' {p : ℕ | Nat.Prime p ∧
      (⟨(p : ℤ), 0⟩ : GaussianInt) ∈ BiCylinder k suffix_pattern len m prefix_pattern}) := by
    apply Set.Finite.subset h
    intro z hz
    simp only [Set.mem_image, Set.mem_setOf_eq, f] at hz
    obtain ⟨p, ⟨_, hp_mem⟩, hp_eq⟩ := hz
    rw [← hp_eq]
    exact hp_mem
  have h_inj : Set.InjOn f {p : ℕ | Nat.Prime p ∧
      (⟨(p : ℤ), 0⟩ : GaussianInt) ∈ BiCylinder k suffix_pattern len m prefix_pattern} := by
    intro p1 _ p2 _ heq
    simp only [f, Zsqrtd.ext_iff] at heq
    exact Int.ofNat.inj heq.1
  exact Set.Finite.of_finite_image h_img_finite h_inj

/-! ## Section 6: Summary

### Prime Results in Bi-Topology:
1. `odd_prime_first_digit`: Odd primes have first digit = true
2. `odd_prime_mod4`: Odd primes are ≡ 1 or 3 (mod 4)
3. `prime_pair_mod4`: Prime pairs have compatible mod 4 structure
4. `prime_pair_biTopo_compatible`: Full digit compatibility
5. `primes_in_biCylinder_finite`: Finite primes in any BiCylinder

These results form the foundation for prime distribution analysis.
-/

end SPBiTopology
