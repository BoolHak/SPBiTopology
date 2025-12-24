/-
  BiTopology/SPBiTopology/Topology.lean

  TOPOLOGICAL STRUCTURE: Suffix and Prefix Topologies on Gaussian Integers

  This file defines:
  1. The suffix embedding (LSD-first, for β-adic topology)
  2. The prefix embedding (MSD-first, using canonical representation)
  3. Both induced topologies
  4. Key properties: T0, cylinders, clopenness

  Based on the canonical representation from Basic.lean.
-/

import BiTopology.SPBiTopology.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Separation

set_option autoImplicit false

namespace SPBiTopology

open Zsqrtd

/-! ## Sequence Spaces -/

/-- Infinite binary sequences (Cantor space) -/
abbrev BinarySeq := ℕ → Bool

/-- The product topology on binary sequences -/
instance : TopologicalSpace BinarySeq := Pi.topologicalSpace

/-- Binary sequences form a compact space (Tychonoff) -/
instance : CompactSpace BinarySeq := inferInstance

/-- Binary sequences form a Hausdorff space -/
instance : T2Space BinarySeq := inferInstance

/-- Binary sequences form a totally disconnected space -/
instance : TotallyDisconnectedSpace BinarySeq := inferInstance

/-! ## The Suffix Embedding (LSD-first, β-adic) -/

/-- The suffix embedding: z ↦ (n-th LSD digit)
    This captures the β-adic structure where position n is the coefficient of β^n -/
noncomputable def iotaSuffix (z : GaussianInt) : BinarySeq :=
  fun n => nthDigitLSD z n

/-- The suffix topology on ℤ[i] induced by the suffix embedding -/
def tau_suffix : TopologicalSpace GaussianInt :=
  TopologicalSpace.induced iotaSuffix inferInstance

/-! ## The Prefix Embedding (MSD-first, Canonical) -/

/-- Encode a natural number in binary (LSB first) -/
def natToBinary (n : ℕ) : ℕ → Bool :=
  fun k => n.testBit k

/-- The canonical prefix embedding: z ↦ (interleaved length and digits)
    Position 2k encodes bit k of digitLength z
    Position 2k+1 encodes nthDigitMSD z k
    This ensures injectivity by encoding the length. -/
noncomputable def iotaPrefixCanonical (z : GaussianInt) : BinarySeq :=
  fun n =>
    if n % 2 = 0 then
      -- Even positions: encode the digit length
      natToBinary (digitLength z) (n / 2)
    else
      -- Odd positions: encode the MSD digits
      nthDigitMSD z (n / 2)

/-- The canonical prefix topology on ℤ[i] -/
def tau_prefix : TopologicalSpace GaussianInt :=
  TopologicalSpace.induced iotaPrefixCanonical inferInstance

/-! ## Suffix Cylinders -/

/-- A suffix cylinder: elements with prescribed first k LSD digits -/
def SuffixCylinder (k : ℕ) (pattern : Fin k → Bool) : Set GaussianInt :=
  {z | ∀ j : Fin k, nthDigitLSD z j.val = pattern j}

/-- Suffix cylinder membership is equivalent to lsdAgree with any element having that pattern -/
theorem mem_suffixCylinder_iff (z : GaussianInt) (k : ℕ) (pattern : Fin k → Bool) :
    z ∈ SuffixCylinder k pattern ↔ ∀ j : Fin k, nthDigitLSD z j.val = pattern j := by
  rfl

/-- Suffix cylinders are characterized by β^k divisibility -/
theorem suffixCylinder_eq_coset (k : ℕ) (pattern : Fin k → Bool) (w : GaussianInt)
    (hw : w ∈ SuffixCylinder k pattern) :
    SuffixCylinder k pattern = {z | lsdAgree z w k} := by
  ext z
  simp only [Set.mem_setOf_eq, SuffixCylinder, lsdAgree]
  constructor
  · intro hz j hj
    have hz' := hz ⟨j, hj⟩
    have hw' := hw ⟨j, hj⟩
    simp only at hz' hw'
    rw [hz', hw']
  · intro hz j
    have hw' := hw j
    have hz' := hz j.val j.isLt
    simp only at hw' hz'
    rw [← hw', hz']

/-! ## Suffix Cylinder Topology -/

/-- The cylinder set in BinarySeq constraining first k coordinates -/
def seqCylinder (k : ℕ) (pattern : Fin k → Bool) : Set BinarySeq :=
  {s | ∀ j : Fin k, s j.val = pattern j}

/-- seqCylinder is open in the product topology -/
theorem seqCylinder_isOpen (k : ℕ) (pattern : Fin k → Bool) :
    IsOpen (seqCylinder k pattern) := by
  have h_eq : seqCylinder k pattern =
      ⋂ j : Fin k, (fun s => s j.val) ⁻¹' {pattern j} := by
    ext s
    simp only [seqCylinder, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage,
               Set.mem_singleton_iff]
  rw [h_eq]
  apply isOpen_iInter_of_finite
  intro j
  exact (continuous_apply j.val).isOpen_preimage _ (isOpen_discrete _)

/-- seqCylinder is closed in the product topology -/
theorem seqCylinder_isClosed (k : ℕ) (pattern : Fin k → Bool) :
    IsClosed (seqCylinder k pattern) := by
  have h_eq : seqCylinder k pattern =
      ⋂ j : Fin k, (fun s => s j.val) ⁻¹' {pattern j} := by
    ext s
    simp only [seqCylinder, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage,
               Set.mem_singleton_iff]
  rw [h_eq]
  apply isClosed_iInter
  intro j
  apply IsClosed.preimage (continuous_apply j.val)
  exact isClosed_discrete _

/-- seqCylinder is clopen in the product topology -/
theorem seqCylinder_isClopen (k : ℕ) (pattern : Fin k → Bool) :
    IsClopen (seqCylinder k pattern) :=
  ⟨seqCylinder_isClosed k pattern, seqCylinder_isOpen k pattern⟩

/-- SuffixCylinder equals the preimage of seqCylinder under iotaSuffix -/
theorem suffixCylinder_eq_preimage (k : ℕ) (pattern : Fin k → Bool) :
    SuffixCylinder k pattern = iotaSuffix ⁻¹' (seqCylinder k pattern) := by
  ext z
  simp only [SuffixCylinder, seqCylinder, Set.mem_setOf_eq, Set.mem_preimage, iotaSuffix]

/-- Suffix cylinders are open in tau_suffix -/
theorem suffixCylinder_isOpen (k : ℕ) (pattern : Fin k → Bool) :
    @IsOpen GaussianInt tau_suffix (SuffixCylinder k pattern) := by
  rw [tau_suffix, suffixCylinder_eq_preimage]
  exact isOpen_induced (seqCylinder_isOpen k pattern)

/-- Suffix cylinders are closed in tau_suffix -/
theorem suffixCylinder_isClosed (k : ℕ) (pattern : Fin k → Bool) :
    @IsClosed GaussianInt tau_suffix (SuffixCylinder k pattern) := by
  rw [tau_suffix, suffixCylinder_eq_preimage, isClosed_induced_iff]
  exact ⟨seqCylinder k pattern, seqCylinder_isClosed k pattern, rfl⟩

/-- Suffix cylinders are clopen in tau_suffix -/
theorem suffixCylinder_isClopen (k : ℕ) (pattern : Fin k → Bool) :
    @IsClopen GaussianInt tau_suffix (SuffixCylinder k pattern) :=
  ⟨suffixCylinder_isClosed k pattern, suffixCylinder_isOpen k pattern⟩

/-! ## Prefix Cylinders -/

/-- A prefix cylinder: elements with prescribed first m MSD digits AND matching digit length -/
def PrefixCylinder (len : ℕ) (m : ℕ) (pattern : Fin m → Bool) : Set GaussianInt :=
  {z | digitLength z = len ∧ ∀ j : Fin m, nthDigitMSD z j.val = pattern j}

/-- Prefix cylinder membership -/
theorem mem_prefixCylinder_iff (z : GaussianInt) (len m : ℕ) (pattern : Fin m → Bool) :
    z ∈ PrefixCylinder len m pattern ↔
    digitLength z = len ∧ ∀ j : Fin m, nthDigitMSD z j.val = pattern j := by
  rfl

/-! ## Bi-Cylinders -/

/-- A bi-cylinder: constrained on both suffix and prefix -/
def BiCylinder (k : ℕ) (suffix_pattern : Fin k → Bool)
    (len m : ℕ) (prefix_pattern : Fin m → Bool) : Set GaussianInt :=
  SuffixCylinder k suffix_pattern ∩ PrefixCylinder len m prefix_pattern

/-! ## Resonant Cylinders (The "Cyclic-Scale" Novelty) -/

/-- A resonant prefix cylinder: elements matching a pattern and a length *modulo 2^m*.
    This formalizes the "Cyclic-Scale" property: standard prefix topology would require exact length,
    but the 2-adic length encoding implies that lengths differing by 2^m are topologically close. -/
def ResonantPrefixCylinder (len_mod : ℕ) (m : ℕ) (pattern : Fin m → Bool) : Set GaussianInt :=
  {z | digitLength z % 2^m = len_mod % 2^m ∧ ∀ j : Fin m, nthDigitMSD z j.val = pattern j}

/-- Helper: Agreement on first m bits of length is equivalent to modulo 2^m equality -/
theorem length_agree_iff_mod_eq (n len_mod m : ℕ) :
    (∀ k < m, natToBinary n k = natToBinary len_mod k) ↔ n % 2^m = len_mod % 2^m := by
  unfold natToBinary
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hk : k < m
    · simp only [hk, decide_True, Bool.true_and]
      exact h k hk
    · simp only [hk, decide_False, Bool.false_and]
  · intro h k hk
    have h_eq : (n % 2^m).testBit k = (len_mod % 2^m).testBit k := by rw [h]
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow] at h_eq
    simp only [hk, decide_True, Bool.true_and] at h_eq
    exact h_eq

/-- Resonant cylinders are open in the prefix topology.
    This is the key theorem formalizing the "Cyclic-Scale" property. -/
theorem isOpen_resonantPrefixCylinder (len_mod : ℕ) (m : ℕ) (pattern : Fin m → Bool) :
    tau_prefix.IsOpen (ResonantPrefixCylinder len_mod m pattern) := by
  -- The cylinder in sequence space constraining first 2m positions
  set C : Set BinarySeq := {s | ∀ i : Fin (2 * m), s i.val =
    if i.val % 2 = 0 then natToBinary len_mod (i.val / 2)
    else pattern ⟨i.val / 2, by have := i.isLt; omega⟩} with hC_def

  -- C is open: finite intersection of preimages of singletons
  have h_open_C : IsOpen C := by
    rw [hC_def]
    have h_eq : {s : BinarySeq | ∀ i : Fin (2 * m), s i.val =
        if i.val % 2 = 0 then natToBinary len_mod (i.val / 2)
        else pattern ⟨i.val / 2, by have := i.isLt; omega⟩} =
      ⋂ i : Fin (2 * m), (fun s => s i.val) ⁻¹'
        {if i.val % 2 = 0 then natToBinary len_mod (i.val / 2)
         else pattern ⟨i.val / 2, by have := i.isLt; omega⟩} := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    rw [h_eq]
    apply isOpen_iInter_of_finite
    intro i
    exact (continuous_apply i.val).isOpen_preimage _ (isOpen_discrete _)

  -- ResonantPrefixCylinder = iotaPrefixCanonical ⁻¹' C
  have h_preimage : ResonantPrefixCylinder len_mod m pattern = iotaPrefixCanonical ⁻¹' C := by
    rw [hC_def]
    ext z
    simp only [ResonantPrefixCylinder, Set.mem_preimage, Set.mem_setOf_eq, iotaPrefixCanonical]
    constructor
    · intro ⟨hlen, hpat⟩ i
      by_cases h_even : i.val % 2 = 0
      · -- Even: length bit
        simp only [h_even, ↓reduceIte]
        have hk : i.val / 2 < m := by have := i.isLt; omega
        have hlen' := (length_agree_iff_mod_eq (digitLength z) len_mod m).mpr hlen
        exact hlen' (i.val / 2) hk
      · -- Odd: digit
        have h_odd : i.val % 2 ≠ 0 := h_even
        simp only [h_odd, ↓reduceIte]
        have hk : i.val / 2 < m := by have := i.isLt; omega
        exact hpat ⟨i.val / 2, hk⟩
    · intro h
      constructor
      · -- Length modulo
        rw [← length_agree_iff_mod_eq]
        intro k hk
        have h_spec := h ⟨2 * k, by omega⟩
        have h_mod : (2 * k) % 2 = 0 := Nat.mul_mod_right 2 k
        have h_div : (2 * k) / 2 = k := Nat.mul_div_cancel_left k (by omega : 0 < 2)
        simp only [h_mod, ↓reduceIte, h_div] at h_spec
        exact h_spec
      · -- Pattern
        intro j
        have h_spec := h ⟨2 * j.val + 1, by omega⟩
        have h_mod : (2 * j.val + 1) % 2 ≠ 0 := by omega
        have h_div : (2 * j.val + 1) / 2 = j.val := by omega
        simp only [h_mod, ↓reduceIte, h_div] at h_spec
        convert h_spec using 1

  -- Conclude
  rw [tau_prefix, h_preimage]
  exact isOpen_induced h_open_C

/-! ## Injectivity of Embeddings -/

/-- norm(β^k) = 2^k -/
theorem norm_β_pow (k : ℕ) : (β^k).norm = 2^k := by
  induction k with
  | zero => simp only [pow_zero, Zsqrtd.norm_one]
  | succ k ih =>
    rw [pow_succ, Zsqrtd.norm_mul, ih, norm_β, pow_succ]

/-- If β^k | d for all k, then d = 0 -/
theorem dvd_all_pow_imp_zero (d : GaussianInt) (h : ∀ k, β^k ∣ d) : d = 0 := by
  by_contra hne
  have h_norm_pos : 0 < d.norm := norm_pos d hne
  -- Find k such that 2^k > |norm(d)|
  have h_bound : ∃ k, 2^k > d.norm.natAbs := by
    use d.norm.natAbs + 1
    have h1 : d.norm.natAbs + 1 < 2^(d.norm.natAbs + 1) := Nat.lt_two_pow (d.norm.natAbs + 1)
    omega
  obtain ⟨k, hk⟩ := h_bound
  -- But β^k | d means d = β^k * q for some q
  obtain ⟨q, hq⟩ := h k
  -- norm(d) = norm(β^k) * norm(q) = 2^k * norm(q)
  have h_norm_eq : d.norm = (β^k).norm * q.norm := by
    rw [← Zsqrtd.norm_mul, ← hq]
  rw [norm_β_pow] at h_norm_eq
  -- If q ≠ 0, then norm(q) ≥ 1, so norm(d) ≥ 2^k, contradiction
  -- If q = 0, then d = 0, contradiction
  by_cases hq0 : q = 0
  · rw [hq0, mul_zero] at hq; exact hne hq
  · have hq_norm_pos : 0 < q.norm := norm_pos q hq0
    have hq_norm_ge : q.norm ≥ 1 := by omega
    have h2k_pos : (2 : ℤ)^k > 0 := by positivity
    have h_norm_ge : d.norm ≥ 2^k := by nlinarith
    have h_natabs_ge : d.norm.natAbs ≥ 2^k := by
      have h_nonneg := norm_nonneg d
      have h_norm_int : d.norm = d.norm.natAbs := (Int.natAbs_of_nonneg h_nonneg).symm
      rw [h_norm_int] at h_norm_ge
      exact_mod_cast h_norm_ge
    omega

/-- The suffix embedding is injective (T0 property for tau_suffix) -/
theorem iotaSuffix_injective : Function.Injective iotaSuffix := by
  intro z w h
  -- If iotaSuffix z = iotaSuffix w, then all LSD digits agree
  have h_agree : ∀ n, nthDigitLSD z n = nthDigitLSD w n := fun n => congrFun h n
  -- This means lsdAgree z w k for all k
  have h_all : ∀ k, lsdAgree z w k := fun k n _ => h_agree n
  -- By lsd_agree_iff_pow_dvd, β^k | (z - w) for all k
  have h_dvd : ∀ k, β^k ∣ (z - w) := fun k => (lsd_agree_iff_pow_dvd z w k).mp (h_all k)
  -- The only element divisible by all powers of β is 0
  have h_zero : z - w = 0 := dvd_all_pow_imp_zero (z - w) h_dvd
  exact sub_eq_zero.mp h_zero

/-- The canonical prefix embedding is injective (T0 property for tau_prefix) -/
theorem iotaPrefixCanonical_injective : Function.Injective iotaPrefixCanonical := by
  intro z w h
  -- iotaPrefixCanonical encodes both length and digits
  -- Even positions encode digitLength, odd positions encode nthDigitMSD
  have h_all : ∀ n, iotaPrefixCanonical z n = iotaPrefixCanonical w n := fun n => congrFun h n
  -- Step 1: Extract that lengths are equal (from even positions)
  have h_len_bits : ∀ k, natToBinary (digitLength z) k = natToBinary (digitLength w) k := by
    intro k
    have h2k := h_all (2 * k)
    simp only [iotaPrefixCanonical, natToBinary] at h2k
    have hmod : (2 * k) % 2 = 0 := Nat.mul_mod_right 2 k
    have hdiv : (2 * k) / 2 = k := Nat.mul_div_cancel_left k (by omega : 0 < 2)
    simp only [hmod, ↓reduceIte, hdiv] at h2k
    exact h2k
  have h_len : digitLength z = digitLength w := by
    -- Two natural numbers with the same binary representation are equal
    have h_eq : ∀ k, (digitLength z).testBit k = (digitLength w).testBit k := h_len_bits
    exact Nat.eq_of_testBit_eq h_eq
  -- Step 2: Extract that MSD digits are equal (from odd positions)
  have h_msd : ∀ k, nthDigitMSD z k = nthDigitMSD w k := by
    intro k
    have h2k1 := h_all (2 * k + 1)
    simp only [iotaPrefixCanonical] at h2k1
    have hmod : (2 * k + 1) % 2 = 1 := by omega
    have hdiv : (2 * k + 1) / 2 = k := by omega
    simp only [hmod, hdiv] at h2k1
    simp only [Nat.one_ne_zero, ↓reduceIte] at h2k1
    exact h2k1
  -- Step 3: Show reversed lists are equal
  have h_rev : (toDigits z).reverse = (toDigits w).reverse := by
    apply List.ext_getElem
    · simp only [List.length_reverse, digitLength] at h_len ⊢; exact h_len
    · intro n hn _
      simp only [List.length_reverse] at hn
      have h_msd_n := h_msd n
      simp only [nthDigitMSD] at h_msd_n
      simp only [hn, ↓reduceDIte] at h_msd_n
      have hw_bound : n < (toDigits w).length := by
        simp only [digitLength] at h_len; omega
      simp only [hw_bound, ↓reduceDIte] at h_msd_n
      exact h_msd_n
  -- Step 4: Reversed lists equal implies original lists equal
  have h_repr : toDigits z = toDigits w := List.reverse_injective h_rev
  -- Step 5: Equal representations means equal values
  have hz := evalDigits_toDigits z
  rw [h_repr, evalDigits_toDigits] at hz
  exact hz.symm

/-! ## Dynamics: The Shift Map z ↦ βz -/

/-- Multiplication by β shifts LSD digits: the n-th digit of βz is 0 for n=0,
    and the (n-1)-th digit of z for n > 0. -/
theorem nthDigitLSD_mul_β (z : GaussianInt) (n : ℕ) :
    nthDigitLSD (β * z) n = if n = 0 then false else nthDigitLSD z (n - 1) := by
  by_cases hz : z = 0
  · subst hz
    simp only [mul_zero, nthDigitLSD_zero, ite_self]
  · by_cases hn : n = 0
    · -- n = 0: digit of βz is 0 (since β | βz)
      subst hn
      simp only [↓reduceIte]
      have hβz_ne : β * z ≠ 0 := by
        intro h
        exact hz (mul_eq_zero.mp h |>.resolve_left β_ne_zero)
      rw [nthDigitLSD_zero_eq (β * z) hβz_ne]
      rw [digit_false_iff]
      exact dvd_mul_right β z
    · -- n > 0: shift property
      simp only [hn, ↓reduceIte]
      -- βz = 0 + β * z, so βQuot(βz) = z (when digit = false)
      have hβz_digit : digit (β * z) = false := by
        rw [digit_false_iff]; exact dvd_mul_right β z
      have hβz_spec := digit_βQuot_spec (β * z)
      simp only [hβz_digit, Bool.false_eq_true, ↓reduceIte, zero_add] at hβz_spec
      -- βQuot(βz) = z
      have hβQuot_eq : βQuot (β * z) = z := mul_left_cancel₀ β_ne_zero hβz_spec.symm
      -- Use nthDigitLSD_succ
      have h_succ : n = (n - 1) + 1 := by omega
      conv_lhs => rw [h_succ, nthDigitLSD_succ (β * z) (n - 1), hβQuot_eq]

/-- The suffix embedding intertwines multiplication by β with a right shift -/
theorem iotaSuffix_mul_β (z : GaussianInt) :
    iotaSuffix (β * z) = fun n => if n = 0 then false else iotaSuffix z (n - 1) := by
  funext n
  simp only [iotaSuffix, nthDigitLSD_mul_β]

/-- Multiplication by β is continuous in the suffix topology.
    This is the KEY dynamical property: the β-adic topology supports the shift dynamics. -/
theorem continuous_mul_β_suffix : @Continuous GaussianInt GaussianInt tau_suffix tau_suffix (β * ·) := by
  -- We show that the composition iotaSuffix ∘ (β * ·) is continuous
  -- iotaSuffix (β * z) = shift(iotaSuffix z) where shift prepends false
  letI : TopologicalSpace GaussianInt := tau_suffix
  rw [tau_suffix, continuous_induced_rng]
  -- Need: iotaSuffix ∘ (β * ·) : GaussianInt → BinarySeq is continuous
  -- where GaussianInt has the induced topology from iotaSuffix
  -- This reduces to showing the shift map on BinarySeq is continuous
  have h_eq : iotaSuffix ∘ (β * ·) = (fun s n => if n = 0 then false else s (n - 1)) ∘ iotaSuffix := by
    funext z
    simp only [Function.comp_apply, iotaSuffix_mul_β]
  rw [h_eq]
  apply Continuous.comp
  · -- The right-shift map on BinarySeq is continuous
    apply continuous_pi
    intro n
    by_cases hn : n = 0
    · simp only [hn, ↓reduceIte]
      exact continuous_const
    · simp only [hn, ↓reduceIte]
      exact continuous_apply (n - 1)
  · -- iotaSuffix with induced topology is continuous (by definition)
    exact continuous_induced_dom

/-- LSD agreement is preserved by adding a constant.
    Key insight: if z and w agree on first k digits, then z - w is divisible by β^k,
    hence (z + c) - (w + c) = z - w is also divisible by β^k. -/
theorem lsdAgree_add (z w c : GaussianInt) (k : ℕ) (h : lsdAgree z w k) :
    lsdAgree (z + c) (w + c) k := by
  rw [lsd_agree_iff_pow_dvd] at h ⊢
  have hsub : (z + c) - (w + c) = z - w := by ring
  rw [hsub]
  exact h

/-- The n-th LSD digit of z + c depends only on the first n+1 digits of z.
    This is the key lemma for continuity of addition. -/
theorem nthDigitLSD_add_of_lsdAgree (z w c : GaussianInt) (n : ℕ)
    (h : lsdAgree z w (n + 1)) :
    nthDigitLSD (z + c) n = nthDigitLSD (w + c) n := by
  have h' := lsdAgree_add z w c (n + 1) h
  rw [lsdAgree] at h'
  exact h' n (Nat.lt_succ_self n)

/-- Addition of any constant is continuous in the suffix topology.
    The key insight: z ↦ nthDigitLSD (z + c) n depends only on the first n+1 digits of z.

    The proof uses that a function to a discrete space from an induced topology is continuous
    iff preimages of points are open. Since nthDigitLSD (z + c) n is determined by the first
    n+1 digits of z (by lsdAgree_add), preimages are unions of cylinders, hence open. -/
theorem continuous_add_suffix (c : GaussianInt) :
    @Continuous GaussianInt GaussianInt tau_suffix tau_suffix (· + c) := by
  letI := tau_suffix
  rw [continuous_induced_rng]
  apply continuous_pi
  intro n
  -- Goal: (fun z => nthDigitLSD (z + c) n) is continuous from induced topology to Bool

  -- A function to Bool (discrete) is continuous iff preimages of singletons are open.
  -- In the induced topology, a set is open iff it's a preimage of an open set.
  -- By nthDigitLSD_add_of_lsdAgree, our function is constant on suffix cylinders of depth n+1.
  -- Hence preimages are unions of cylinders, which are open.

  -- We prove this using the characterization: continuous iff preimages of opens are open
  rw [continuous_def]
  intro U _hU
  -- Need: preimage of U is open in induced topology
  rw [isOpen_induced_iff]
  -- Construct the open set V in BinarySeq
  -- V = {s | for any z with iotaSuffix z agreeing with s on [0,n], nthDigitLSD (z+c) n ∈ U}
  -- This is open because it depends only on coords 0..n
  use {s : BinarySeq | ∀ z : GaussianInt, (∀ i < n + 1, s i = nthDigitLSD z i) →
                                          nthDigitLSD (z + c) n ∈ U}
  constructor
  · -- V is open in BinarySeq (product topology)
    -- V depends only on the first n+1 coordinates
    -- Define the projection to first n+1 coords
    let proj : BinarySeq → (Fin (n + 1) → Bool) := fun s i => s i.val
    have hproj : Continuous proj := continuous_pi (fun i => continuous_apply i.val)
    -- V is a preimage under proj of some set in Fin (n+1) → Bool
    have hV : {s : BinarySeq | ∀ z : GaussianInt, (∀ i < n + 1, s i = nthDigitLSD z i) →
                                nthDigitLSD (z + c) n ∈ U} =
              proj ⁻¹' {p : Fin (n + 1) → Bool | ∀ z : GaussianInt,
                        (∀ i : Fin (n + 1), p i = nthDigitLSD z i.val) → nthDigitLSD (z + c) n ∈ U} := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_preimage, proj]
      constructor
      · intro h z hz
        apply h z
        intro i hi
        exact hz ⟨i, hi⟩
      · intro h z hz
        apply h z
        intro i
        exact hz i.val i.isLt
    rw [hV]
    apply hproj.isOpen_preimage
    exact isOpen_discrete _
  · -- Preimage equality
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Function.comp_apply, iotaSuffix]
    constructor
    · -- mp: from the universal statement, deduce for z itself
      intro hz
      exact hz z (fun _ _ => rfl)
    · -- mpr: from nthDigitLSD (z + c) n ∈ U, prove for all z' agreeing on first n+1 digits
      intro hz z' hz'
      have h_agree : lsdAgree z z' (n + 1) := fun i hi => hz' i hi
      rw [← nthDigitLSD_add_of_lsdAgree z z' c n h_agree]
      exact hz

/-- Addition of 1 is continuous in the suffix topology. -/
theorem continuous_add_one_suffix : @Continuous GaussianInt GaussianInt tau_suffix tau_suffix (· + 1) :=
  continuous_add_suffix 1

/-! ## Prefix Topology: Continuity of Shift

The key asymmetry: multiplication by β is a contraction in tau_suffix
but an expansion in tau_prefix.

In the standard prefix topology (without resonance), multiplication by β
would be discontinuous because it changes the digit length.
However, `tau_prefix` (induced by `iotaPrefixCanonical`) includes
2-adic length information, making the map z ↦ βz continuous. -/

/-- Multiplication by β increases digit length by 1 for nonzero z -/
theorem digitLength_mul_β (z : GaussianInt) (hz : z ≠ 0) :
    digitLength (β * z) = digitLength z + 1 := by
  have hβz_ne : β * z ≠ 0 := by
    intro h
    exact hz (mul_eq_zero.mp h |>.resolve_left β_ne_zero)
  have hβz_digit : digit (β * z) = false := by
    rw [digit_false_iff]; exact dvd_mul_right β z
  -- toDigits(βz) = false :: toDigits(z) when digit(βz) = false
  simp only [digitLength]
  conv_lhs => rw [toDigits]; simp only [hβz_ne, ↓reduceDIte]
  simp only [List.length_cons]
  -- βQuot(βz) = z
  have hβQuot_eq : βQuot (β * z) = z := by
    have hβz_spec := digit_βQuot_spec (β * z)
    simp only [hβz_digit, Bool.false_eq_true, ↓reduceIte, zero_add] at hβz_spec
    exact mul_left_cancel₀ β_ne_zero hβz_spec.symm
  rw [hβQuot_eq]


/-! ### Continuity of Multiplication by β in Prefix Topology

The theorem that multiplication by β is continuous in `tau_prefix` follows
from the "local determination" of the canonical embedding.
The n-th coordinate of `iotaPrefixCanonical (β * z)` depends only on
finitely many coordinates of `iotaPrefixCanonical z`.

The key helper lemmas needed are:
1. `nthDigitMSD_mul_β`: For k < digitLength z, nthDigitMSD (β * z) k = nthDigitMSD z k
2. `nthDigitMSD_mul_β_last`: nthDigitMSD (β * z) (digitLength z) = false

These follow from the structure of β-adic multiplication: toDigits (β * z) = false :: toDigits z,
so the MSD representation shifts appropriately. -/

/-! ## Helper lemmas for specific elements -/

/-- digit of 1 is true -/
theorem digit_one : digit (1 : GaussianInt) = true := by
  rw [digit_true_iff]; intro h
  have := β_dvd_iff 1 |>.mp h
  simp only [Zsqrtd.one_re, Zsqrtd.one_im] at this
  omega

/-- βQuot of 1 is 0 -/
theorem βQuot_one : βQuot (1 : GaussianInt) = 0 := by
  have hspec := digit_βQuot_spec 1
  simp only [digit_one, ↓reduceIte] at hspec
  -- hspec : 1 = 1 + β * βQuot 1, so β * βQuot 1 = 0
  have h : β * βQuot 1 = 0 := by
    have heq : (1 : GaussianInt) = 1 + β * βQuot 1 := hspec
    calc β * βQuot 1 = (1 + β * βQuot 1) - 1 := by ring
      _ = 1 - 1 := by rw [← heq]
      _ = 0 := by ring
  exact (mul_eq_zero.mp h).resolve_left β_ne_zero

/-- toDigits of 1 is [true] -/
theorem toDigits_one : toDigits (1 : GaussianInt) = [true] := by
  conv_lhs => rw [toDigits]
  simp only [one_ne_zero, ↓reduceDIte, digit_one, Bool.true_eq_false, ↓reduceIte,
             βQuot_one, toDigits, ↓reduceDIte]

/-- digitLength of 1 is 1 -/
theorem one_digitLength : digitLength (1 : GaussianInt) = 1 := by
  simp only [digitLength, toDigits_one, List.length_singleton]

/-- nthDigitLSD of 1 at position 0 is true -/
theorem one_nthDigitLSD_zero : nthDigitLSD (1 : GaussianInt) 0 = true := by
  rw [nthDigitLSD_zero_eq 1 one_ne_zero, digit_one]

/-- nthDigitLSD of 1 at position n+1 is false -/
theorem one_nthDigitLSD_succ (n : ℕ) : nthDigitLSD (1 : GaussianInt) (n + 1) = false := by
  simp only [nthDigitLSD, toDigits_one, List.getD_cons_succ, List.getD_nil]

/-! ## T0 Properties -/

/-- tau_suffix is T0 (follows from injective embedding into T2 space) -/
theorem tau_suffix_t0 : @T0Space GaussianInt tau_suffix := by
  -- T0 means: for distinct points, there exists an open set containing one but not the other
  -- Equivalently: inseparable points are equal
  rw [@t0Space_iff_inseparable _ tau_suffix]
  intro z w h_insep
  -- iotaSuffix is injective, so it suffices to show iotaSuffix z = iotaSuffix w
  apply iotaSuffix_injective
  -- In the induced topology, inseparable points have inseparable images
  -- Since BinarySeq is T2 (hence T0), inseparable images are equal
  letI : TopologicalSpace GaussianInt := tau_suffix
  have h_ind : Inducing iotaSuffix := inducing_induced iotaSuffix
  -- Inducing.inseparable_iff: Inseparable x y ↔ Inseparable (f x) (f y)
  have h_insep_img : Inseparable (iotaSuffix z) (iotaSuffix w) := h_ind.inseparable_iff.mpr h_insep
  exact h_insep_img.eq

/-! ## Phase 2: BiCylinder Characterization -/

/-- Elements with fixed digitLength form a finite set.
    Key insight: digitLength n means z = evalDigits (toDigits z) with |toDigits z| = n,
    so z is one of at most 2^n possibilities. -/
theorem prefixCylinder_finite (len m : ℕ) (pattern : Fin m → Bool) :
    Set.Finite (PrefixCylinder len m pattern) := by
  -- PrefixCylinder ⊆ {z | digitLength z = len}
  have h_sub : PrefixCylinder len m pattern ⊆ {z | digitLength z = len} := by
    intro z hz
    simp only [PrefixCylinder, Set.mem_setOf_eq] at hz
    exact hz.1
  -- It suffices to show {z | digitLength z = len} is finite
  apply Set.Finite.subset _ h_sub
  -- Elements with digitLength len are images of lists of length len under evalDigits
  have h_sub2 : {z : GaussianInt | digitLength z = len} ⊆
                evalDigits '' {ds : List Bool | ds.length = len} := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    simp only [Set.mem_image, Set.mem_setOf_eq]
    exact ⟨toDigits z, hz, evalDigits_toDigits z⟩
  apply Set.Finite.subset _ h_sub2
  apply Set.Finite.image
  -- Lists of fixed length form a finite set
  -- {ds : List Bool | ds.length = len} ⊆ range of List.ofFn
  have h_sub3 : {ds : List Bool | ds.length = len} ⊆
                Set.range (List.ofFn : (Fin len → Bool) → List Bool) := by
    intro ds hds
    simp only [Set.mem_setOf_eq] at hds
    simp only [Set.mem_range]
    refine ⟨fun i => ds.get ⟨i.val, by rw [hds]; exact i.isLt⟩, ?_⟩
    apply List.ext_getElem
    · simp only [List.length_ofFn, hds]
    · intro i h1 h2
      simp only [List.getElem_ofFn, List.get_eq_getElem]
  apply Set.Finite.subset (Set.finite_range _) h_sub3

/-- BiCylinders are finite -/
theorem biCylinder_finite (k : ℕ) (suffix_pattern : Fin k → Bool)
    (len m : ℕ) (prefix_pattern : Fin m → Bool) :
    Set.Finite (BiCylinder k suffix_pattern len m prefix_pattern) := by
  -- BiCylinder = SuffixCylinder ∩ PrefixCylinder
  -- PrefixCylinder is finite, so the intersection is finite
  simp only [BiCylinder]
  apply Set.Finite.subset (prefixCylinder_finite len m prefix_pattern)
  exact Set.inter_subset_right

/-- BiCylinders are proper subsets of SuffixCylinders (when nonempty with constraints) -/
theorem biCylinder_subset_suffix (k : ℕ) (suffix_pattern : Fin k → Bool)
    (len m : ℕ) (prefix_pattern : Fin m → Bool) :
    BiCylinder k suffix_pattern len m prefix_pattern ⊆ SuffixCylinder k suffix_pattern := by
  simp only [BiCylinder]
  exact Set.inter_subset_left

/-- BiCylinders are proper subsets of PrefixCylinders -/
theorem biCylinder_subset_prefix (k : ℕ) (suffix_pattern : Fin k → Bool)
    (len m : ℕ) (prefix_pattern : Fin m → Bool) :
    BiCylinder k suffix_pattern len m prefix_pattern ⊆ PrefixCylinder len m prefix_pattern := by
  simp only [BiCylinder]
  exact Set.inter_subset_right

/-! ## Phase 3: Orbit Distribution Across Scales -/

/-- digitLength grows without bound under iteration -/
theorem digitLength_pow_mul (z : GaussianInt) (hz : z ≠ 0) (n : ℕ) :
    digitLength (β^n * z) = digitLength z + n := by
  induction n with
  | zero => simp only [pow_zero, one_mul, Nat.add_zero]
  | succ n ih =>
    have hβnz_ne : β^n * z ≠ 0 := mul_ne_zero (pow_ne_zero n β_ne_zero) hz
    calc digitLength (β^(n+1) * z)
        = digitLength (β * (β^n * z)) := by ring_nf
      _ = digitLength (β^n * z) + 1 := digitLength_mul_β (β^n * z) hβnz_ne
      _ = (digitLength z + n) + 1 := by rw [ih]
      _ = digitLength z + (n + 1) := by ring

/-- Orbit escapes every fixed PrefixCylinder (digitLength grows unboundedly) -/
theorem orbit_prefix_escape (z : GaussianInt) (hz : z ≠ 0) (len m : ℕ)
    (pattern : Fin m → Bool) :
    ∃ n : ℕ, (β^n * z) ∉ PrefixCylinder len m pattern := by
  -- Choose n such that digitLength z + n > len
  use len - digitLength z + 1
  intro h_in
  simp only [PrefixCylinder, Set.mem_setOf_eq] at h_in
  have h_len := h_in.1
  rw [digitLength_pow_mul z hz] at h_len
  omega

/-- LSD of β * z at position 0 is false (since β | β*z) -/
theorem nthDigitLSD_mul_β_zero (z : GaussianInt) :
    nthDigitLSD (β * z) 0 = false := by
  by_cases hz : β * z = 0
  · rw [hz, nthDigitLSD_zero]
  · rw [nthDigitLSD_zero_eq (β * z) hz]
    rw [digit_false_iff]
    exact dvd_mul_right β z

/-- LSD of β * z at position n+1 equals LSD of z at position n -/
theorem nthDigitLSD_mul_β_succ (z : GaussianInt) (hz : z ≠ 0) (n : ℕ) :
    nthDigitLSD (β * z) (n + 1) = nthDigitLSD z n := by
  simp only [nthDigitLSD]
  have h_digit : digit (β * z) = false := by
    rw [digit_false_iff]; exact dvd_mul_right β z
  have h_βQuot : βQuot (β * z) = z := by
    have hspec := digit_βQuot_spec (β * z)
    simp only [h_digit, Bool.false_eq_true, ↓reduceIte, zero_add] at hspec
    exact mul_left_cancel₀ β_ne_zero hspec.symm
  have hβz_ne : β * z ≠ 0 := mul_ne_zero β_ne_zero hz
  conv_lhs => rw [toDigits]
  simp only [hβz_ne, ↓reduceDIte, h_digit, Bool.false_eq_true, ↓reduceIte, h_βQuot,
             List.getD_cons_succ]

/-- LSD of β^n * z at position k equals LSD of z at position k-n (for k ≥ n) -/
theorem nthDigitLSD_pow_mul (z : GaussianInt) (hz : z ≠ 0) (n k : ℕ) (hk : n ≤ k) :
    nthDigitLSD (β^n * z) k = nthDigitLSD z (k - n) := by
  induction n generalizing k with
  | zero => simp only [pow_zero, one_mul, Nat.sub_zero]
  | succ n ih =>
    have hβnz_ne : β^n * z ≠ 0 := mul_ne_zero (pow_ne_zero n β_ne_zero) hz
    have h_eq : β^(n+1) * z = β * (β^n * z) := by ring
    cases k with
    | zero => omega
    | succ k =>
      rw [h_eq, nthDigitLSD_mul_β_succ (β^n * z) hβnz_ne k]
      have hk' : n ≤ k := by omega
      rw [ih k hk']
      congr 1
      omega

/-- LSD of β^n * z at positions < n are all false -/
theorem nthDigitLSD_pow_mul_lt (z : GaussianInt) (hz : z ≠ 0) (n k : ℕ) (hk : k < n) :
    nthDigitLSD (β^n * z) k = false := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    have hβnz_ne : β^n * z ≠ 0 := mul_ne_zero (pow_ne_zero n β_ne_zero) hz
    have h_eq : β^(n+1) * z = β * (β^n * z) := by ring
    cases k with
    | zero => rw [h_eq]; exact nthDigitLSD_mul_β_zero (β^n * z)
    | succ k =>
      rw [h_eq, nthDigitLSD_mul_β_succ (β^n * z) hβnz_ne k]
      have hk' : k < n := by omega
      exact ih k hk'

/-- Orbit eventually agrees with 0 on first k LSD digits -/
theorem orbit_suffix_density (z : GaussianInt) (k : ℕ) :
    ∃ n : ℕ, lsdAgree (β^n * z) 0 k := by
  by_cases hz : z = 0
  · use 0
    simp only [hz, mul_zero, lsdAgree]
    intro i _
    trivial
  · use k
    intro i hi
    rw [nthDigitLSD_pow_mul_lt z hz k i hi, nthDigitLSD_zero]

/-- The bi-topological orbit signature: captures LSD pattern, digitLength, and MSD pattern -/
noncomputable def orbitSignature (z : GaussianInt) (n k m : ℕ) :
    (Fin k → Bool) × ℕ × (Fin m → Bool) :=
  (fun j => nthDigitLSD (β^n * z) j.val,
   digitLength (β^n * z),
   fun j => nthDigitMSD (β^n * z) j.val)

/-! ## Phase 4: Resonant Self-Similarity -/

/-- Resonant equivalence: elements with same digitLength mod 2^m and matching first m MSD digits -/
def resonantEquiv (m : ℕ) (z w : GaussianInt) : Prop :=
  digitLength z % 2^m = digitLength w % 2^m ∧
  ∀ j < m, nthDigitMSD z j = nthDigitMSD w j

/-- resonantEquiv is reflexive -/
theorem resonantEquiv_refl (m : ℕ) (z : GaussianInt) : resonantEquiv m z z := by
  simp only [resonantEquiv, and_self, implies_true]

/-- resonantEquiv is symmetric -/
theorem resonantEquiv_symm (m : ℕ) (z w : GaussianInt) :
    resonantEquiv m z w → resonantEquiv m w z := by
  intro ⟨hlen, hdigits⟩
  exact ⟨hlen.symm, fun j hj => (hdigits j hj).symm⟩

/-- resonantEquiv is transitive -/
theorem resonantEquiv_trans (m : ℕ) (x y z : GaussianInt) :
    resonantEquiv m x y → resonantEquiv m y z → resonantEquiv m x z := by
  intro ⟨hlen_xy, hdigits_xy⟩ ⟨hlen_yz, hdigits_yz⟩
  constructor
  · exact hlen_xy.trans hlen_yz
  · intro j hj
    exact (hdigits_xy j hj).trans (hdigits_yz j hj)

/-- resonantEquiv is an equivalence relation -/
theorem resonantEquiv_equivalence (m : ℕ) : Equivalence (resonantEquiv m) :=
  ⟨resonantEquiv_refl m, fun h => resonantEquiv_symm m _ _ h, fun h1 h2 => resonantEquiv_trans m _ _ _ h1 h2⟩

/-- digitLength mod 2^m is periodic with period 2^m under β multiplication -/
theorem digitLength_mod_periodic (z : GaussianInt) (hz : z ≠ 0) (m n : ℕ) :
    digitLength (β^(n + 2^m) * z) % 2^m = digitLength (β^n * z) % 2^m := by
  rw [digitLength_pow_mul z hz (n + 2^m)]
  rw [digitLength_pow_mul z hz n]
  have h : (digitLength z + (n + 2^m)) % 2^m = (digitLength z + n) % 2^m := by
    conv_lhs => rw [← Nat.add_assoc]
    rw [Nat.add_mod, Nat.mod_self, Nat.add_zero]
    exact Nat.mod_mod_of_dvd _ (dvd_refl _)
  exact h

/-- Orbit has period 2^m in resonant length classes -/
theorem orbit_resonant_period (z : GaussianInt) (hz : z ≠ 0) (m : ℕ) :
    ∀ n : ℕ, digitLength (β^(n + 2^m) * z) % 2^m = digitLength (β^n * z) % 2^m :=
  fun n => digitLength_mod_periodic z hz m n

/-- Elements in same ResonantPrefixCylinder share τ_prefix neighborhoods -/
theorem resonant_neighborhood_shared (z w : GaussianInt) (m : ℕ) (pattern : Fin m → Bool)
    (hz : z ∈ ResonantPrefixCylinder (digitLength z % 2^m) m pattern)
    (hw : resonantEquiv m z w) :
    w ∈ ResonantPrefixCylinder (digitLength z % 2^m) m pattern := by
  simp only [ResonantPrefixCylinder, Set.mem_setOf_eq] at hz ⊢
  obtain ⟨hlen_z, hpat_z⟩ := hz
  obtain ⟨hlen_eq, hdigits_eq⟩ := hw
  constructor
  · rw [← hlen_eq]; exact hlen_z
  · intro j
    rw [← hdigits_eq j.val j.isLt]
    exact hpat_z j

/-- The resonant structure creates a "renormalization" map:
    β^(2^m) preserves resonant class structure -/
theorem resonant_renormalization (z : GaussianInt) (hz : z ≠ 0) (m : ℕ) :
    digitLength (β^(2^m) * z) % 2^m = digitLength z % 2^m := by
  rw [digitLength_pow_mul z hz (2^m)]
  simp only [Nat.add_mod_right]

/-! ## Phase 5: Bi-Topological Complexity Measure -/

/-- Bi-topological complexity: count distinct orbit signatures visited up to step n.
    This captures how the orbit explores the joint (suffix, prefix) space. -/
noncomputable def biTopologicalComplexity (z : GaussianInt) (n k m : ℕ) : ℕ :=
  Finset.card (Finset.image (orbitSignature z · k m) (Finset.range n))

/-- The orbit signature of 0 is constant (0 is a fixed point) -/
theorem orbitSignature_zero (n k m : ℕ) :
    orbitSignature 0 n k m = orbitSignature 0 0 k m := by
  simp only [orbitSignature, mul_zero]

/-- 0 has complexity 1 for n > 0 (only one signature) -/
theorem biTopologicalComplexity_zero (n k m : ℕ) (hn : 0 < n) :
    biTopologicalComplexity 0 n k m = 1 := by
  simp only [biTopologicalComplexity]
  have h_image : Finset.image (orbitSignature 0 · k m) (Finset.range n) =
                 {orbitSignature 0 0 k m} := by
    ext sig
    simp only [Finset.mem_image, Finset.mem_singleton, Finset.mem_range]
    constructor
    · intro ⟨i, _, hi_eq⟩
      rw [← hi_eq, orbitSignature_zero]
    · intro hsig
      use 0
      exact ⟨hn, hsig.symm⟩
  rw [h_image, Finset.card_singleton]

/-- For nonzero z, the suffix part of orbit signature becomes constant after k steps -/
theorem orbitSignature_suffix_stabilizes (z : GaussianInt) (hz : z ≠ 0) (k m n : ℕ) (hn : k ≤ n) :
    (orbitSignature z n k m).1 = fun _ => false := by
  simp only [orbitSignature]
  ext j
  exact nthDigitLSD_pow_mul_lt z hz n j.val (Nat.lt_of_lt_of_le j.isLt hn)

/-- For nonzero z, digitLength grows linearly -/
theorem orbitSignature_length_grows (z : GaussianInt) (hz : z ≠ 0) (n k m : ℕ) :
    (orbitSignature z n k m).2.1 = digitLength z + n := by
  simp only [orbitSignature]
  exact digitLength_pow_mul z hz n

/-- The prefix part of the signature (digitLength) distinguishes different orbit steps -/
theorem orbitSignature_length_injective (z : GaussianInt) (hz : z ≠ 0) (k m : ℕ) :
    ∀ n₁ n₂ : ℕ, (orbitSignature z n₁ k m).2.1 = (orbitSignature z n₂ k m).2.1 → n₁ = n₂ := by
  intro n₁ n₂ h
  simp only [orbitSignature, digitLength_pow_mul z hz] at h
  omega

/-- Complexity of nonzero z equals n (each step has distinct digitLength) -/
theorem biTopologicalComplexity_eq (z : GaussianInt) (hz : z ≠ 0) (n k m : ℕ) :
    biTopologicalComplexity z n k m = n := by
  simp only [biTopologicalComplexity]
  rw [Finset.card_image_of_injective]
  · exact Finset.card_range n
  · intro i j hij
    have h := orbitSignature_length_injective z hz k m i j
    apply h
    simp only [hij]

/-- Summary: 0 has constant complexity, nonzero z has linear complexity growth -/
theorem complexity_dichotomy (z : GaussianInt) (n k m : ℕ) (hn : 0 < n) :
    (z = 0 → biTopologicalComplexity z n k m = 1) ∧
    (z ≠ 0 → biTopologicalComplexity z n k m = n) := by
  constructor
  · intro hz; rw [hz]; exact biTopologicalComplexity_zero n k m hn
  · intro hz; exact biTopologicalComplexity_eq z hz n k m

/-! ## Phase 6: Orbit Density and Topological Structure -/

/-- The orbit of any nonzero z eventually enters every suffix cylinder containing 0.
    This shows the orbit "approaches" 0 in the suffix topology. -/
theorem orbit_enters_zero_cylinder (z : GaussianInt) (hz : z ≠ 0) (k : ℕ)
    (pattern : Fin k → Bool) (h0 : (0 : GaussianInt) ∈ SuffixCylinder k pattern) :
    ∃ n : ℕ, β^n * z ∈ SuffixCylinder k pattern := by
  -- 0 ∈ SuffixCylinder k pattern means pattern j = false for all j
  have h_pattern : ∀ j : Fin k, pattern j = false := by
    intro j
    have h0j := h0 j
    simp only [nthDigitLSD_zero] at h0j
    exact h0j.symm
  -- β^k * z has first k digits all false
  use k
  intro j
  rw [h_pattern j]
  exact nthDigitLSD_pow_mul_lt z hz k j.val j.isLt

/-- The zero cylinder (all first k digits false) contains the orbit tail -/
theorem orbit_in_zero_cylinder (z : GaussianInt) (hz : z ≠ 0) (k : ℕ) :
    ∀ n ≥ k, β^n * z ∈ SuffixCylinder k (fun _ => false) := by
  intro n hn
  intro j
  simp only
  have hj_lt_n : j.val < n := Nat.lt_of_lt_of_le j.isLt hn
  exact nthDigitLSD_pow_mul_lt z hz n j.val hj_lt_n

/-- The suffix cylinder containing 0 with depth k is exactly the set of elements
    divisible by β^k -/
theorem zero_cylinder_eq_multiples (k : ℕ) :
    SuffixCylinder k (fun _ => false) = {z | β^k ∣ z} := by
  ext z
  simp only [SuffixCylinder, Set.mem_setOf_eq]
  constructor
  · intro h
    have h_agree : lsdAgree z 0 k := by
      intro i hi
      have := h ⟨i, hi⟩
      simp only at this
      rw [this, nthDigitLSD_zero]
    rw [lsd_agree_iff_pow_dvd] at h_agree
    simpa using h_agree
  · intro ⟨q, hq⟩
    intro j
    have h_agree : lsdAgree z 0 k := by
      rw [lsd_agree_iff_pow_dvd]
      simp only [sub_zero]
      exact ⟨q, hq⟩
    have := h_agree j.val j.isLt
    rw [nthDigitLSD_zero] at this
    exact this

/-- Characterization: z ∈ SuffixCylinder k pattern iff z ≡ w (mod β^k) for any w with that pattern -/
theorem suffixCylinder_mod_characterization (k : ℕ) (pattern : Fin k → Bool)
    (w : GaussianInt) (hw : w ∈ SuffixCylinder k pattern) :
    ∀ z, z ∈ SuffixCylinder k pattern ↔ β^k ∣ (z - w) := by
  intro z
  have h_coset := suffixCylinder_eq_coset k pattern w hw
  rw [h_coset]
  simp only [Set.mem_setOf_eq]
  exact lsd_agree_iff_pow_dvd z w k

/-- The intersection of all suffix cylinders containing 0 is exactly {0} -/
theorem zero_intersection :
    ⋂ k, SuffixCylinder k (fun _ => false) = {(0 : GaussianInt)} := by
  ext z
  simp only [Set.mem_iInter, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hz
    -- z ≠ 0, so digitLength z > 0
    have h_len := digitLength_pos z hz
    -- z ∈ SuffixCylinder (digitLength z) (fun _ => false)
    have h_cyl := h (digitLength z)
    -- But the (digitLength z - 1)-th digit of z should be true (MSD)
    -- Actually, let's use a simpler argument
    -- z is divisible by β^k for all k, so z = 0
    have h_dvd : ∀ k, β^k ∣ z := by
      intro k
      have hk := h k
      rw [zero_cylinder_eq_multiples] at hk
      exact hk
    exact hz (dvd_all_pow_imp_zero z h_dvd)
  · intro hz
    subst hz
    intro k j
    exact nthDigitLSD_zero j.val

/-- The shift map on BinarySeq: prepend false -/
def shiftRight : BinarySeq → BinarySeq :=
  fun s n => if n = 0 then false else s (n - 1)

/-- shiftRight is continuous -/
theorem shiftRight_continuous : Continuous shiftRight := by
  apply continuous_pi
  intro n
  by_cases hn : n = 0
  · simp only [shiftRight, hn, ↓reduceIte]
    exact continuous_const
  · simp only [shiftRight, hn, ↓reduceIte]
    exact continuous_apply (n - 1)

/-- The suffix embedding intertwines β-multiplication with shiftRight -/
theorem iotaSuffix_shift_commutes (z : GaussianInt) :
    iotaSuffix (β * z) = shiftRight (iotaSuffix z) := by
  funext n
  simp only [iotaSuffix, shiftRight, nthDigitLSD_mul_β]

/-- tau_suffix makes (ℤ[i], β * ·) a topological dynamical system -/
theorem tau_suffix_dynamical_system :
    @Continuous GaussianInt GaussianInt tau_suffix tau_suffix (β * ·) ∧
    Function.Injective iotaSuffix := by
  exact ⟨continuous_mul_β_suffix, iotaSuffix_injective⟩

/-! ## Phase 7: Bi-Topological Separation -/

/-- Two distinct elements can be separated by either suffix or prefix cylinders -/
theorem biTopo_separation (z w : GaussianInt) (h : z ≠ w) :
    (∃ k pattern, z ∈ SuffixCylinder k pattern ∧ w ∉ SuffixCylinder k pattern) ∨
    (∃ len m pattern, z ∈ PrefixCylinder len m pattern ∧ w ∉ PrefixCylinder len m pattern) := by
  -- If digitLength differs, use prefix separation
  by_cases h_len : digitLength z = digitLength w
  · -- Same length: must differ in some digit
    -- Use suffix separation at the first differing LSD position
    left
    have h_repr : toDigits z ≠ toDigits w := by
      intro h_eq
      exact h (eq_of_toDigits_eq z w h_eq)
    -- Find first differing position
    have h_diff : ∃ n, nthDigitLSD z n ≠ nthDigitLSD w n := by
      by_contra h_all
      push_neg at h_all
      have : toDigits z = toDigits w := by
        apply List.ext_getElem
        · simp only [digitLength] at h_len; exact h_len
        · intro i hi _
          simp only [nthDigitLSD, List.getD_eq_getElem?_getD] at h_all
          have hi' : i < (toDigits w).length := by simp only [digitLength] at h_len; omega
          have hz := h_all i
          simp only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi',
                     Option.getD_some] at hz
          exact hz
      exact h_repr this
    obtain ⟨n, hn⟩ := h_diff
    use n + 1, fun j => nthDigitLSD z j.val
    constructor
    · intro j; rfl
    · intro hw
      have := hw ⟨n, Nat.lt_succ_self n⟩
      simp only at this
      exact hn this.symm
  · -- Different lengths: use prefix separation
    right
    use digitLength z, 0, (Fin.elim0 : Fin 0 → Bool)
    constructor
    · -- z ∈ PrefixCylinder (digitLength z) 0 Fin.elim0
      rw [mem_prefixCylinder_iff]
      exact ⟨rfl, fun j => j.elim0⟩
    · -- w ∉ PrefixCylinder (digitLength z) 0 Fin.elim0
      rw [mem_prefixCylinder_iff]
      intro ⟨h_eq, _⟩
      exact h_len h_eq.symm

/-! ## Summary

### Defined:
1. `iotaSuffix`: LSD-first embedding (injective)
2. `iotaPrefixCanonical`: MSD-first embedding using canonical representation
3. `tau_suffix`: Suffix topology (induced by iotaSuffix)
4. `tau_prefix`: Prefix topology (induced by iotaPrefixCanonical)
5. `SuffixCylinder`, `PrefixCylinder`, `BiCylinder`: Cylinder sets
6. `ResonantPrefixCylinder`: Cylinders respecting 2-adic length resonance

### Proven:
1. `iotaSuffix_injective`: Suffix embedding is injective
2. `iotaPrefixCanonical_injective`: Prefix embedding is injective
3. `tau_suffix_t0`: Suffix topology is T0
4. `toDigits_getLast_true`: Leading digit of nonzero z is true
5. `suffixCylinder_isClopen`: Suffix cylinders are clopen
6. `isOpen_resonantPrefixCylinder`: Resonant prefix cylinders are open
7. `biCylinder_finite`: BiCylinders are finite
8. `continuous_mul_β_suffix`: Multiplication by β is continuous in suffix topology
9. `continuous_add_suffix`: Addition is continuous in suffix topology

### Dynamical Systems:
The suffix topology `tau_suffix` makes (ℤ[i], β·) a topological dynamical system.
The prefix topology `tau_prefix` captures the "global" structure required for search.
-/

end SPBiTopology
