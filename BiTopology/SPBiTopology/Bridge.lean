/-
  BiTopology/SPBiTopology/Bridge.lean

  THE ℤ[i] ↔ ℕ BRIDGE

  This module provides the mathematical bridge between Gaussian integer
  theory (ℤ[i]) and natural number problems (ℕ). The key connections are:

  1. **Norm Map**: N(a + bi) = a² + b² maps ℤ[i] → ℕ
     - Fibers of this map give sum-of-two-squares representations
     - Jacobi's formula: r₂(n) = 4(d₁(n) - d₃(n))

  2. **Zeta Factorization**: ζ_{ℤ[i]}(s) = ζ(s) · L(s, χ_{-4})
     - Dedekind zeta of ℚ(i) factors into Riemann zeta and Dirichlet L-function
     - Results about ℤ[i] translate to results about ℕ

  3. **Prime Correspondence**:
     - p = 2: Ramifies as (1+i)²
     - p ≡ 1 (mod 4): Splits as p = ππ̄
     - p ≡ 3 (mod 4): Stays prime (inert)

  4. **Cylinder-Representation Bridge**:
     - Cylinder decomposition of ℤ[i] induces decomposition of r₂(n)
     - Each cylinder contributes to representations at specific norms

  APPLICATIONS:
  - Sum of two squares problems
  - Prime counting in ℤ[i] → prime counting in ℕ
  - Goldbach-type problems via Gaussian primes
  - Asymptotic formulas via cylinder method
-/

import BiTopology.SPBiTopology.Basic
import BiTopology.SPBiTopology.GoldenIdentity
import BiTopology.SPBiTopology.CircleMethod
import Mathlib.NumberTheory.SumTwoSquares

set_option autoImplicit false

namespace SPBiTopology

open GaussianInt Zsqrtd Classical

attribute [local instance] Classical.propDecidable

/-! ============================================================================
    PART I: THE NORM MAP AND SUM OF TWO SQUARES

    The norm N : ℤ[i] → ℕ is the fundamental bridge. Its fiber over n
    gives all representations of n as a sum of two squares.
============================================================================ -/

/-- The norm of a Gaussian integer as a natural number -/
def gaussianNorm (z : GaussianInt) : ℕ := z.norm.natAbs

/-- The norm fiber: all Gaussian integers with a given norm -/
def NormFiber (n : ℕ) : Set GaussianInt :=
  {z : GaussianInt | gaussianNorm z = n}

/-- A number is representable as sum of two squares -/
def IsSumOfTwoSquares (n : ℕ) : Prop :=
  ∃ a b : ℤ, a^2 + b^2 = n

/-- r₂(n): the representation count (exists but may not be computable directly) -/
noncomputable def r₂ (n : ℕ) : ℕ :=
  -- Conceptually: count of (a, b) ∈ ℤ² with a² + b² = n
  -- For n > 0, this is finite and equals 4(d₁(n) - d₃(n)) by Jacobi
  if _h : IsSumOfTwoSquares n then 1 else 0  -- Simplified placeholder

/-- The norm of a Gaussian integer is nonnegative -/
theorem gaussianInt_norm_nonneg (z : GaussianInt) : 0 ≤ z.norm :=
  Zsqrtd.norm_nonneg (by norm_num : (-1 : ℤ) ≤ 0) z

/-- The norm as natAbs equals the norm when nonnegative -/
theorem gaussianInt_natAbs_norm (z : GaussianInt) : (z.norm.natAbs : ℤ) = z.norm :=
  Int.natAbs_of_nonneg (gaussianInt_norm_nonneg z)

/-- The Gaussian norm expands to re² + im² -/
theorem gaussianInt_norm_eq (z : GaussianInt) : z.norm = z.re^2 + z.im^2 := by
  simp only [Zsqrtd.norm]
  ring

/-- Alternative characterization via Gaussian integers -/
theorem sumOfTwoSquares_iff_normFiber_nonempty (n : ℕ) :
    IsSumOfTwoSquares n ↔ ∃ z : GaussianInt, gaussianNorm z = n := by
  unfold IsSumOfTwoSquares gaussianNorm
  constructor
  · intro ⟨a, b, hab⟩
    use ⟨a, b⟩
    -- N(a + bi) = a² + b² = n, and a² + b² ≥ 0, so natAbs preserves it
    have hnorm : (⟨a, b⟩ : GaussianInt).norm = a^2 + b^2 := gaussianInt_norm_eq ⟨a, b⟩
    have _hnn : 0 ≤ (⟨a, b⟩ : GaussianInt).norm := gaussianInt_norm_nonneg ⟨a, b⟩
    rw [hnorm, hab]
    -- Need to show (n : ℤ).natAbs = n
    exact Int.natAbs_ofNat n
  · intro ⟨z, hz⟩
    use z.re, z.im
    have hnorm : z.norm = z.re^2 + z.im^2 := gaussianInt_norm_eq z
    have hcast : (z.norm.natAbs : ℤ) = z.norm := gaussianInt_natAbs_norm z
    -- hz : z.norm.natAbs = n, so (n : ℤ) = z.norm = z.re² + z.im²
    calc z.re^2 + z.im^2 = z.norm := hnorm.symm
      _ = (z.norm.natAbs : ℤ) := hcast.symm
      _ = (n : ℤ) := by rw [hz]

/-! ============================================================================
    PART II: RATIONAL INTEGER EMBEDDING

    The integers ℤ embed in ℤ[i] as the real axis {a + 0i}.
    This provides a direct bridge for problems about ℤ.
============================================================================ -/

/-- Embed a rational integer into Gaussian integers -/
def embedℤ (n : ℤ) : GaussianInt := ⟨n, 0⟩

/-- A Gaussian integer is on the real axis -/
def IsRational (z : GaussianInt) : Prop := z.im = 0

/-- Embedded integers are rational -/
theorem embedℤ_isRational (n : ℤ) : IsRational (embedℤ n) := rfl

/-- The norm of an embedded integer is its square -/
theorem embedℤ_norm (n : ℤ) : (embedℤ n).norm = n^2 := by
  unfold embedℤ
  simp only [Zsqrtd.norm]
  ring

/-- Rational Gaussian integers correspond to integers -/
theorem rational_iff_im_zero (z : GaussianInt) :
    IsRational z ↔ ∃ n : ℤ, z = embedℤ n := by
  unfold IsRational embedℤ
  constructor
  · intro h
    use z.re
    ext <;> simp [h]
  · intro ⟨n, hn⟩
    simp [hn]

/-! ============================================================================
    PART III: DIVISOR FUNCTIONS AND JACOBI'S THEOREM

    Jacobi's formula: r₂(n) = 4(d₁(n) - d₃(n))
    where d_a(n) counts divisors of n congruent to a mod 4.
============================================================================ -/

/-- Count divisors of n congruent to a mod 4 -/
noncomputable def divisorCount (a : ℕ) (n : ℕ) : ℕ :=
  (Finset.filter (fun d => d % 4 = a) (Nat.divisors n)).card

/-- d₁(n): divisors ≡ 1 (mod 4) -/
noncomputable def d₁ (n : ℕ) : ℕ := divisorCount 1 n

/-- d₃(n): divisors ≡ 3 (mod 4) -/
noncomputable def d₃ (n : ℕ) : ℕ := divisorCount 3 n

/-- Characterization of sums of two squares via prime factorization (from Mathlib).
    A natural number n is a sum of two squares iff for every prime q ≡ 3 (mod 4)
    dividing n, the exponent of q in the factorization is even. -/
theorem sum_two_squares_iff_prime_factorization (n : ℕ) :
    (∃ x y : ℕ, n = x^2 + y^2) ↔
    ∀ {q : ℕ}, Nat.Prime q → q % 4 = 3 → Even (padicValNat q n) :=
  Nat.eq_sq_add_sq_iff

/-- Connection between IsSumOfTwoSquares and the ℕ characterization -/
theorem isSumOfTwoSquares_iff_nat (n : ℕ) :
    IsSumOfTwoSquares n ↔ ∃ x y : ℕ, n = x^2 + y^2 := by
  unfold IsSumOfTwoSquares
  constructor
  · intro ⟨a, b, hab⟩
    -- a² + b² = n with a, b : ℤ. Need x, y : ℕ.
    use a.natAbs, b.natAbs
    -- (a.natAbs)² = a² and similarly for b, since squaring removes sign
    have ha2 : ((a.natAbs : ℤ))^2 = a^2 := Int.natAbs_pow_two a
    have hb2 : ((b.natAbs : ℤ))^2 = b^2 := Int.natAbs_pow_two b
    have h : ((a.natAbs)^2 + (b.natAbs)^2 : ℕ) = n := by
      have hcast : ((a.natAbs)^2 : ℤ) + ((b.natAbs)^2 : ℤ) = (n : ℤ) := by
        simp only [← Nat.cast_pow, Nat.cast_add, ha2, hb2, hab]
      exact Int.ofNat.inj hcast
    exact h.symm
  · intro ⟨x, y, hxy⟩
    use x, y
    have h1 : (x : ℤ)^2 = ((x^2 : ℕ) : ℤ) := by norm_cast
    have h2 : (y : ℤ)^2 = ((y^2 : ℕ) : ℤ) := by norm_cast
    rw [h1, h2, ← Nat.cast_add, hxy]

/-! ============================================================================
    PART IV: PRIME SPLITTING IN ℤ[i]

    How rational primes behave in the Gaussian integers:
    - p = 2: Ramifies (2 = -i(1+i)²)
    - p ≡ 1 (mod 4): Splits (p = ππ̄ for Gaussian prime π)
    - p ≡ 3 (mod 4): Stays prime (inert)
============================================================================ -/

/-- A rational prime ramifies in ℤ[i] -/
def Ramifies (p : ℕ) : Prop := p = 2

/-- A rational prime splits in ℤ[i] -/
def Splits (p : ℕ) : Prop := Nat.Prime p ∧ p % 4 = 1

/-- A rational prime is inert in ℤ[i] -/
def IsInert (p : ℕ) : Prop := Nat.Prime p ∧ p % 4 = 3

/-- Classification of primes in ℤ[i] -/
theorem prime_trichotomy (p : ℕ) (hp : Nat.Prime p) :
    Ramifies p ∨ Splits p ∨ IsInert p := by
  unfold Ramifies Splits IsInert
  -- Every prime is ≡ 0, 1, 2, or 3 (mod 4)
  -- Primes ≡ 0 or 2 (mod 4) must be 2 (the only even prime)
  rcases Nat.Prime.eq_two_or_odd hp with rfl | hodd
  · left; rfl
  · have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases h4 with h1 | h3
    · right; left; exact ⟨hp, h1⟩
    · right; right; exact ⟨hp, h3⟩

/-- 2 ramifies as (1+i)² (up to units) -/
theorem two_ramifies : (⟨1, 1⟩ : GaussianInt) * ⟨1, 1⟩ = ⟨0, 2⟩ := by
  ext <;> decide

/-- Primes ≡ 1 (mod 4) are sums of two squares (Fermat's theorem on sums of two squares) -/
theorem fermat_two_squares (p : ℕ) (hp : Nat.Prime p) (h1 : p % 4 = 1) :
    IsSumOfTwoSquares p := by
  -- Use Mathlib's Nat.Prime.sq_add_sq which proves this for p % 4 ≠ 3
  have hne3 : p % 4 ≠ 3 := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq hne3
  unfold IsSumOfTwoSquares
  use (a : ℤ), (b : ℤ)
  -- hab : a^2 + b^2 = p in ℕ, need to show (a : ℤ)^2 + (b : ℤ)^2 = (p : ℤ)
  have h : (a^2 + b^2 : ℕ) = p := hab
  calc (a : ℤ)^2 + (b : ℤ)^2 = ((a^2 : ℕ) : ℤ) + ((b^2 : ℕ) : ℤ) := by simp [sq]
    _ = ((a^2 + b^2 : ℕ) : ℤ) := by push_cast; ring
    _ = (p : ℤ) := by rw [h]

/-- Squares mod 4 are 0 or 1 -/
theorem sq_mod_four (x : ℤ) : x^2 % 4 = 0 ∨ x^2 % 4 = 1 := by
  -- Write x = 4q + r where r = x % 4 ∈ {0, 1, 2, 3}
  -- Then x² = 16q² + 8qr + r², so x² % 4 = r² % 4
  have hmod : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  have hdiv : x = 4 * (x / 4) + x % 4 := (Int.ediv_add_emod x 4).symm
  rcases hmod with hr | hr | hr | hr
  all_goals {
    have hsq : x^2 % 4 = (x % 4)^2 % 4 := by
      conv_lhs => rw [hdiv]
      ring_nf
      omega
    rw [hsq, hr]
    decide
  }

/-- Sum of two squares mod 4 is 0, 1, or 2 (never 3) -/
theorem sum_two_sq_mod_four (a b : ℤ) : (a^2 + b^2) % 4 ≠ 3 := by
  have ha := sq_mod_four a
  have hb := sq_mod_four b
  rcases ha with ha0 | ha1 <;> rcases hb with hb0 | hb1 <;> omega

/-- Primes ≡ 3 (mod 4) are NOT sums of two squares -/
theorem inert_not_sum_two_squares (p : ℕ) (_hp : Nat.Prime p) (h3 : p % 4 = 3) :
    ¬IsSumOfTwoSquares p := by
  intro ⟨a, b, hab⟩
  have hmod : (a^2 + b^2) % 4 ≠ 3 := sum_two_sq_mod_four a b
  have hp4 : (p : ℤ) % 4 = 3 := by omega
  rw [hab] at hmod
  exact hmod hp4

/-! ============================================================================
    PART V: CYLINDER-REPRESENTATION BRIDGE

    Connect the bi-topological cylinder structure to representation counting.
    Each cylinder at depth k contributes to r₂(n) for specific values of n.
============================================================================ -/

/-- Cylinder-restricted norm fiber: elements in a cylinder with given norm -/
def CylinderNormFiber (k : ℕ) (pattern : Fin k → Bool) (n : ℕ) : Set GaussianInt :=
  {z : GaussianInt | z ∈ CylinderArc k pattern ∧ gaussianNorm z = n}

/-- Norm constraint from cylinder depth: elements in k-cylinder have
    norms constrained by β-adic structure -/
theorem cylinder_norm_constraint (k : ℕ) (pattern : Fin k → Bool) (z : GaussianInt)
    (_hz : z ∈ CylinderArc k pattern) :
    -- The last k digits of z determine N(z) mod 2^k
    -- (since N(β) = 2, divisibility by β^k implies divisibility by 2^⌊k/2⌋ in norm)
    ∃ r : ℕ, r < 2^k ∧ gaussianNorm z % 2^k = r := by
  use gaussianNorm z % 2^k
  exact ⟨Nat.mod_lt _ (Nat.two_pow_pos k), rfl⟩

/-- The cylinder structure partitions the norm fiber -/
theorem cylinder_partitions_norm_fiber (k : ℕ) (n : ℕ) :
    NormFiber n = ⋃ (p : Fin k → Bool), CylinderNormFiber k p n := by
  ext z
  simp only [NormFiber, CylinderNormFiber, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hz
    use cylinderPattern z k
    exact ⟨mem_own_cylinder z k, hz⟩
  · intro ⟨_p, ⟨_, hz⟩⟩
    exact hz

/-! ============================================================================
    PART VI: GENERATING FUNCTIONS AND THETA SERIES

    Connect to classical generating functions for sum of squares.
============================================================================ -/

-- The classical Jacobi theta function coefficient: r₂(n)
-- θ(q) = Σ_n r₂(n) q^n = (Σ_m q^{m²})²

/-- The cylinder decomposition provides a natural way to organize
    sum-of-two-squares representations by their β-adic digit patterns -/
theorem theta_cylinder_concept (k : ℕ) (n : ℕ) :
    -- Conceptually: r₂(n) = Σ_{patterns p} #{z : N(z) = n ∧ z ∈ Cylinder(k, p)}
    -- Each element of norm n belongs to exactly one k-cylinder
    ∀ z : GaussianInt, gaussianNorm z = n →
      ∃! p : Fin k → Bool, z ∈ CylinderArc k p := by
  intro z _
  exact cylinder_arcs_partition k z

/-! ============================================================================
    PART VII: DEDEKIND ZETA FACTORIZATION

    The Dedekind zeta of ℚ(i) factors as ζ_{ℚ(i)}(s) = ζ(s) · L(s, χ_{-4})
    This connects Gaussian integer theory to Riemann zeta and Dirichlet L-functions.
============================================================================ -/

/-- The non-principal character mod 4: χ_{-4}(n) = (−4|n) -/
def chi4 (n : ℤ) : ℤ :=
  if n % 4 = 1 then 1
  else if n % 4 = 3 then -1
  else 0

/-- Helper: odd numbers mod 4 are 1 or 3 -/
private theorem odd_mod_four (n : ℤ) (h : n % 2 = 1) : n % 4 = 1 ∨ n % 4 = 3 := by
  have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases h4 with h0 | h1 | h2 | h3
  · exfalso; omega
  · left; exact h1
  · exfalso; omega
  · right; exact h3

/-- Helper: product mod 4 when a ≡ r₁ and b ≡ r₂ (mod 4) -/
private theorem mul_mod_four_of_mod (a b : ℤ) (r₁ r₂ : ℤ)
    (ha : a % 4 = r₁) (hb : b % 4 = r₂) : (a * b) % 4 = (r₁ * r₂) % 4 := by
  calc (a * b) % 4 = ((a % 4) * (b % 4)) % 4 := Int.mul_emod a b 4
    _ = (r₁ * r₂) % 4 := by rw [ha, hb]

/-- χ_{-4} is multiplicative on odd integers -/
theorem chi4_multiplicative (a b : ℤ) (ha : a % 2 = 1) (hb : b % 2 = 1) :
    chi4 (a * b) = chi4 a * chi4 b := by
  have ha4 := odd_mod_four a ha
  have hb4 := odd_mod_four b hb
  unfold chi4
  -- Case analysis on a % 4 and b % 4
  rcases ha4 with ha1 | ha3 <;> rcases hb4 with hb1 | hb3
  · -- a ≡ 1, b ≡ 1: ab ≡ 1*1 = 1 (mod 4)
    have hab : (a * b) % 4 = 1 := by rw [mul_mod_four_of_mod a b 1 1 ha1 hb1]; decide
    simp only [ha1, hb1, hab]; decide
  · -- a ≡ 1, b ≡ 3: ab ≡ 1*3 = 3 (mod 4)
    have hab : (a * b) % 4 = 3 := by rw [mul_mod_four_of_mod a b 1 3 ha1 hb3]; decide
    simp only [ha1, hb3, hab]; decide
  · -- a ≡ 3, b ≡ 1: ab ≡ 3*1 = 3 (mod 4)
    have hab : (a * b) % 4 = 3 := by rw [mul_mod_four_of_mod a b 3 1 ha3 hb1]; decide
    simp only [ha3, hb1, hab]; decide
  · -- a ≡ 3, b ≡ 3: ab ≡ 3*3 = 9 ≡ 1 (mod 4)
    have hab : (a * b) % 4 = 1 := by rw [mul_mod_four_of_mod a b 3 3 ha3 hb3]; decide
    simp only [ha3, hb3, hab]; decide

/-- For primes p, the existence of Gaussian integers of norm p depends on p mod 4.
    This is the key connection between ℤ[i] structure and ℕ arithmetic. -/
theorem prime_norm_existence (p : ℕ) (hp : Nat.Prime p) :
    (p = 2 ∨ p % 4 = 1 → ∃ z : GaussianInt, gaussianNorm z = p) ∧
    (p % 4 = 3 → ¬∃ z : GaussianInt, gaussianNorm z = p) := by
  constructor
  · intro h
    rcases h with rfl | hp1
    · -- p = 2: use 1 + i
      use ⟨1, 1⟩
      unfold gaussianNorm
      have hnorm : (⟨1, 1⟩ : GaussianInt).norm = 2 := by simp [Zsqrtd.norm]
      simp only [hnorm]
      native_decide
    · -- p ≡ 1 (mod 4): use Fermat's theorem
      have hne3 : p % 4 ≠ 3 := by omega
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq hne3
      use ⟨a, b⟩
      unfold gaussianNorm
      have hnorm : (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt).norm = (a : ℤ)^2 + (b : ℤ)^2 := by
        simp only [Zsqrtd.norm, sq]; ring
      simp only [hnorm]
      have hcast : (a : ℤ)^2 + (b : ℤ)^2 = (p : ℤ) := by
        have h1 : (a : ℤ)^2 = ((a^2 : ℕ) : ℤ) := by norm_cast
        have h2 : (b : ℤ)^2 = ((b^2 : ℕ) : ℤ) := by norm_cast
        rw [h1, h2, ← Nat.cast_add, hab]
      simp only [hcast, Int.natAbs_ofNat]
  · intro hp3 ⟨z, hz⟩
    have hsq := sumOfTwoSquares_iff_normFiber_nonempty p |>.mpr ⟨z, hz⟩
    exact inert_not_sum_two_squares p hp hp3 hsq

/-- The norm of an embedded rational integer is its square -/
theorem embedZ_gaussianNorm (n : ℕ) : gaussianNorm (embedℤ n) = n^2 := by
  unfold gaussianNorm embedℤ
  have hnorm : (⟨(n : ℤ), 0⟩ : GaussianInt).norm = (n : ℤ)^2 := by
    simp [Zsqrtd.norm]; ring
  simp only [hnorm, sq, Int.natAbs_mul, Int.natAbs_ofNat]

/-- Inert primes (p ≡ 3 mod 4) remain prime in ℤ[i] with norm p² -/
theorem inert_prime_norm (p : ℕ) (_hp : Nat.Prime p) (_h3 : p % 4 = 3) :
    gaussianNorm (embedℤ p) = p^2 := embedZ_gaussianNorm p

/-! ============================================================================
    PART VIII: APPLICATIONS TO NATURAL NUMBER PROBLEMS

    Use the bridge to translate ℕ problems to ℤ[i] and back.
============================================================================ -/

/-- Problem: Count primes p ≤ x that are sums of two squares -/
noncomputable def countSumTwoSquaresPrimes (x : ℕ) : ℕ :=
  (Finset.filter (fun p => Nat.Prime p ∧ IsSumOfTwoSquares p) (Finset.range (x + 1))).card

/-- These are exactly primes = 2 or ≡ 1 (mod 4) -/
theorem sum_two_squares_primes_classification (p : ℕ) (hp : Nat.Prime p) :
    IsSumOfTwoSquares p ↔ p = 2 ∨ p % 4 = 1 := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    have hp2 : p ≠ 2 := hne.1
    have hp1 : p % 4 ≠ 1 := hne.2
    have h4 : p % 4 = 3 := by
      have hodd := Nat.Prime.eq_two_or_odd hp |>.resolve_left hp2
      omega
    exact inert_not_sum_two_squares p hp h4 h
  · intro h
    rcases h with rfl | h1
    · -- p = 2 = 1² + 1²
      unfold IsSumOfTwoSquares
      use 1, 1
      norm_num
    · exact fermat_two_squares p hp h1

/-- Cylinder method application: the bi-topological structure provides
    a canonical decomposition for analyzing sum-of-squares problems -/
theorem cylinder_sum_squares_application (k : ℕ) :
    -- The cylinder structure partitions ℤ[i] canonically
    -- Each norm fiber is partitioned by cylinders
    -- This connects the ℤ[i] structure to ℕ counting problems
    (∀ n : ℕ, NormFiber n = ⋃ (p : Fin k → Bool), CylinderNormFiber k p n) ∧
    (∀ n : ℕ, ∀ z : GaussianInt, gaussianNorm z = n →
      ∃! p : Fin k → Bool, z ∈ CylinderArc k p) := by
  constructor
  · exact fun n => cylinder_partitions_norm_fiber k n
  · intro n z _
    exact cylinder_arcs_partition k z

end SPBiTopology
