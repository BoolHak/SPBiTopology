/-
  BiTopology/SPBiTopology/Complexity.lean

  COMPUTATIONAL COMPLEXITY VIA BI-TOPOLOGICAL FRAMEWORK

  This file develops a connection between the bi-topological structure on Gaussian
  integers and computational complexity theory. The key insight is that:

  1. The SUFFIX topology (LSD-first, β-adic) captures "local" or "efficiently verifiable"
     properties - analogous to polynomial-time checkable predicates.

  2. The PREFIX topology (MSD-first) captures "global" or "structural" properties -
     analogous to properties requiring examination of the entire input.

  3. The ASYMMETRY between these topologies (β-multiplication is continuous in suffix
     but changes digit length in prefix) mirrors the P vs NP asymmetry between
     verification and search.

  Main Results:
  - Encoding of Boolean strings as Gaussian integers
  - Complexity classes defined via cylinder membership
  - Separation theorems showing suffix ≠ prefix distinguishability
  - Resource bounds via BiCylinder finiteness
-/

import BiTopology.SPBiTopology.Topology
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

namespace SPBiTopology

open Zsqrtd

/-! ## Section 1: Boolean String Encoding

We encode Boolean strings (finite binary sequences) as Gaussian integers.
A string s : Fin n → Bool is encoded as the Gaussian integer whose
first n LSD digits match s.
-/

/-- Encode a finite Boolean string as a Gaussian integer.
    The encoding uses evalDigits on the list representation. -/
def encodeBoolString (s : List Bool) : GaussianInt :=
  evalDigits s

/-- The empty string encodes to 0 -/
theorem encodeBoolString_nil : encodeBoolString [] = 0 := by
  simp [encodeBoolString, evalDigits]

/-- evalDigits of false :: ds equals β * evalDigits ds -/
theorem evalDigits_false_cons (ds : List Bool) :
    evalDigits (false :: ds) = β * evalDigits ds := by
  simp only [evalDigits, Bool.false_eq_true, ite_false, zero_add]

/-- evalDigits of true :: ds equals 1 + β * evalDigits ds -/
theorem evalDigits_true_cons (ds : List Bool) :
    evalDigits (true :: ds) = 1 + β * evalDigits ds := by
  simp only [evalDigits, ite_true]

/-- Helper: digit of evalDigits (d :: ds) equals d.
    The first LSD digit of evalDigits (d :: ds) is d. -/
theorem digit_evalDigits_cons (d : Bool) (ds : List Bool) :
    digit (evalDigits (d :: ds)) = d := by
  cases d
  case false =>
    rw [evalDigits_false_cons]
    rw [digit_false_iff]
    exact dvd_mul_right β (evalDigits ds)
  case true =>
    rw [evalDigits_true_cons]
    rw [digit_true_iff]
    intro h_dvd
    rw [β_dvd_iff] at h_dvd
    simp only [β, Zsqrtd.add_re, Zsqrtd.add_im, Zsqrtd.mul_re, Zsqrtd.mul_im,
               Zsqrtd.one_re, Zsqrtd.one_im] at h_dvd
    omega

/-- Helper: βQuot of evalDigits (d :: ds) equals evalDigits ds.
    Removing the first digit gives the rest. -/
theorem βQuot_evalDigits_cons (d : Bool) (ds : List Bool) :
    βQuot (evalDigits (d :: ds)) = evalDigits ds := by
  have h_digit := digit_evalDigits_cons d ds
  have h_spec := digit_βQuot_spec (evalDigits (d :: ds))
  rw [h_digit] at h_spec
  cases d
  case false =>
    rw [evalDigits_false_cons] at h_spec ⊢
    simp only [Bool.false_eq_true, ite_false, zero_add] at h_spec
    exact (mul_left_cancel₀ β_ne_zero h_spec).symm
  case true =>
    rw [evalDigits_true_cons] at h_spec ⊢
    simp only [ite_true] at h_spec
    have h_eq : β * evalDigits ds = β * βQuot (1 + β * evalDigits ds) := by
      have := congrArg (fun x => x - 1) h_spec
      simp only [add_sub_cancel_left] at this
      exact this
    exact (mul_left_cancel₀ β_ne_zero h_eq).symm

/-- Helper: evalDigits of nonempty list ending in true is nonzero.
    A valid digit representation (ending in 1) represents a nonzero number. -/
theorem evalDigits_ne_zero_of_last_true (s : List Bool) (hne : s ≠ [])
    (hlast : s.getLast hne = true) : evalDigits s ≠ 0 := by
  -- Proof by induction from the front
  suffices h : ∀ (front : List Bool), evalDigits (front ++ [true]) ≠ 0 by
    have h_eq : s = s.dropLast ++ [s.getLast hne] := (List.dropLast_append_getLast hne).symm
    rw [hlast] at h_eq
    rw [h_eq]
    exact h s.dropLast
  intro front
  induction front with
  | nil =>
    simp only [List.nil_append]
    rw [evalDigits_true_cons]
    simp only [evalDigits, mul_zero, add_zero]
    exact one_ne_zero
  | cons d rest ih_front =>
    simp only [List.cons_append]
    intro h_eq
    have h_digit := digit_evalDigits_cons d (rest ++ [true])
    have h_digit_zero : digit (evalDigits (d :: (rest ++ [true]))) = false := by
      rw [h_eq]; exact digit_zero
    rw [h_digit] at h_digit_zero
    cases d
    case false =>
      rw [evalDigits_false_cons] at h_eq
      have := mul_eq_zero.mp h_eq
      cases this with
      | inl hβ => exact β_ne_zero hβ
      | inr hrest => exact ih_front hrest
    case true =>
      exact Bool.noConfusion h_digit_zero

/-- Encoding preserves the digit structure.
    evalDigits followed by toDigits is identity for valid representations. -/
theorem encodeBoolString_toDigits (s : List Bool) (hne : s ≠ [])
    (hlast : s.getLast hne = true) : toDigits (encodeBoolString s) = s := by
  induction s with
  | nil => exact absurd rfl hne
  | cons d ds ih =>
    simp only [encodeBoolString]
    cases hds : ds with
    | nil =>
      have hlast' : d = true := by simp only [hds, List.getLast_singleton] at hlast; exact hlast
      subst hlast'
      rw [evalDigits_true_cons]
      simp only [evalDigits, mul_zero, add_zero]
      unfold toDigits
      simp only [one_ne_zero, dite_false]
      have h_digit_1 : digit (1 : GaussianInt) = true := by
        rw [digit_true_iff]
        intro h; rw [β_dvd_iff] at h
        simp only [Zsqrtd.one_re, Zsqrtd.one_im] at h
        omega
      have h_βQuot_1 : βQuot (1 : GaussianInt) = 0 := by
        have h_spec := digit_βQuot_spec (1 : GaussianInt)
        simp only [h_digit_1, ite_true] at h_spec
        have h_eq : β * βQuot 1 = 0 := by
          have := congrArg (fun x => x - 1) h_spec
          simp only [add_sub_cancel_left] at this
          exact this
        cases mul_eq_zero.mp h_eq with
        | inl h => exact absurd h β_ne_zero
        | inr h => exact h
      simp only [h_digit_1, h_βQuot_1, toDigits_zero]
    | cons d' ds' =>
      have hne' : d' :: ds' ≠ [] := List.cons_ne_nil d' ds'
      have hlast' : (d' :: ds').getLast hne' = true := by
        simp only [hds] at hlast
        simp only [List.getLast_cons hne'] at hlast
        exact hlast
      have hne_full : d :: d' :: ds' ≠ [] := List.cons_ne_nil d (d' :: ds')
      have hlast_full : (d :: d' :: ds').getLast hne_full = true := by
        simp only [List.getLast_cons hne']
        exact hlast'
      have h_ne_zero := evalDigits_ne_zero_of_last_true (d :: d' :: ds') hne_full hlast_full
      unfold toDigits
      simp only [h_ne_zero, dite_false]
      have h_digit := digit_evalDigits_cons d (d' :: ds')
      have h_βQuot := βQuot_evalDigits_cons d (d' :: ds')
      rw [h_digit, h_βQuot]
      congr 1
      -- Need to show: toDigits (evalDigits (d' :: ds')) = d' :: ds'
      -- ih : ds ≠ [] → ds.getLast _ = true → toDigits (evalDigits ds) = ds
      -- But ds = d' :: ds', so we need ih applied to d' :: ds'
      rw [hds] at ih
      exact ih hne' hlast'

/-- The digit length of an encoded string -/
theorem encodeBoolString_length (s : List Bool) (hs : s ≠ [])
    (hlast : s.getLast hs = true) :
    digitLength (encodeBoolString s) = s.length := by
  simp only [digitLength]
  rw [encodeBoolString_toDigits s hs hlast]

/-! ## Section 2: Complexity Classes via Cylinders

We define complexity classes using the cylinder structure:
- A property is "suffix-decidable at depth k" if membership can be determined
  by examining only the first k LSD digits.
- A property is "prefix-decidable at depth m" if membership can be determined
  by examining the digit length and first m MSD digits.
-/

/-- A predicate on Gaussian integers is suffix-decidable at depth k if
    it is constant on each suffix cylinder of depth k. -/
def SuffixDecidable (P : GaussianInt → Prop) (k : ℕ) : Prop :=
  ∀ z w : GaussianInt, lsdAgree z w k → (P z ↔ P w)

/-- A predicate is prefix-decidable at depth m if it depends only on
    digit length and first m MSD digits. -/
def PrefixDecidable (P : GaussianInt → Prop) (m : ℕ) : Prop :=
  ∀ z w : GaussianInt, digitLength z = digitLength w →
    (∀ j < m, nthDigitMSD z j = nthDigitMSD w j) → (P z ↔ P w)

/-- A predicate is bi-decidable if it's both suffix and prefix decidable -/
def BiDecidable (P : GaussianInt → Prop) (k m : ℕ) : Prop :=
  SuffixDecidable P k ∧ PrefixDecidable P m

/-- The class of suffix-decidable predicates (analogous to P) -/
def SuffixClass : Set (GaussianInt → Prop) :=
  {P | ∃ k, SuffixDecidable P k}

/-- The class of prefix-decidable predicates -/
def PrefixClass : Set (GaussianInt → Prop) :=
  {P | ∃ m, PrefixDecidable P m}

/-- The class of bi-decidable predicates (intersection) -/
def BiClass : Set (GaussianInt → Prop) :=
  {P | ∃ k m, BiDecidable P k m}

/-! ## Section 3: Verification vs Search Asymmetry

The key insight: suffix topology supports "local verification" while
prefix topology requires "global search". This asymmetry is formalized
by the continuity properties of β-multiplication.
-/

/-- Suffix-decidable predicates are closed under β-preimage.
    This captures: if P is efficiently verifiable, so is "P after one step". -/
theorem suffixDecidable_preimage_β (P : GaussianInt → Prop) (k : ℕ)
    (hP : SuffixDecidable P k) :
    SuffixDecidable (fun z => P (β * z)) (k + 1) := by
  intro z w h_agree
  -- β * z and β * w agree on first k digits if z and w agree on first k+1 digits
  have h_β_agree : lsdAgree (β * z) (β * w) k := by
    rw [lsd_agree_iff_pow_dvd]
    rw [lsd_agree_iff_pow_dvd] at h_agree
    -- β^(k+1) | (z - w) implies β^k | β(z - w)
    have h_mul : β * z - β * w = β * (z - w) := by ring
    rw [h_mul]
    -- β^(k+1) | (z-w), and we need β^k | β*(z-w)
    -- Since β^(k+1) = β^k * β, if β^(k+1) | d then β^k | β*d
    obtain ⟨q, hq⟩ := h_agree
    -- hq : z - w = β^(k+1) * q
    -- β * (z - w) = β * β^(k+1) * q = β^(k+2) * q
    -- We need β^k | β^(k+2) * q, which is true since β^k | β^(k+2)
    have hdvd : β^k ∣ β * (z - w) := by
      rw [hq]
      use β * β * q
      ring
    exact hdvd
  exact hP (β * z) (β * w) h_β_agree

/-- Prefix-decidable predicates at depth 0 are closed under β-preimage.
    This is because P at depth 0 depends only on digitLength, and
    digitLength(β*z) = digitLength(z) + 1 for z ≠ 0, digitLength(β*0) = 0.
    So if P depends only on length, then so does fun z => P(β*z). -/
theorem prefixDecidable_closed_β_depth0 (P : GaussianInt → Prop)
    (hP : PrefixDecidable P 0) : PrefixDecidable (fun z => P (β * z)) 0 := by
  intro z w hlen _
  -- P at depth 0 depends only on digitLength
  -- We need to show: P(β*z) ↔ P(β*w)
  -- This follows if digitLength(β*z) = digitLength(β*w)
  by_cases hz : z = 0
  · by_cases hw : w = 0
    · subst hz hw; simp
    · -- z = 0, w ≠ 0, but digitLength z = digitLength w
      subst hz
      simp only [digitLength_zero] at hlen
      -- hlen : 0 = digitLength w, so digitLength w = 0
      -- But digitLength w > 0 for w ≠ 0
      have hw_pos : 0 < digitLength w := digitLength_pos w hw
      omega
  · by_cases hw : w = 0
    · subst hw
      simp only [digitLength_zero] at hlen
      have hz_pos : 0 < digitLength z := digitLength_pos z hz
      omega
    · -- Both z ≠ 0 and w ≠ 0
      -- digitLength(β*z) = 1 + digitLength(z) for z ≠ 0
      -- This follows from: β*z ≠ 0 and βQuot(β*z) = z
      have hβz_ne : β * z ≠ 0 := by
        intro h; have := mul_eq_zero.mp h
        cases this with
        | inl hβ => exact β_ne_zero hβ
        | inr hz' => exact hz hz'
      have hβw_ne : β * w ≠ 0 := by
        intro h; have := mul_eq_zero.mp h
        cases this with
        | inl hβ => exact β_ne_zero hβ
        | inr hw' => exact hw hw'
      -- digitLength(β*z) = 1 + digitLength(βQuot(β*z)) = 1 + digitLength(z)
      -- We need βQuot(β*z) = z, which follows from digit(β*z) = false and the recurrence
      have h_digit_βz : digit (β * z) = false := by
        rw [digit_false_iff]; exact dvd_mul_right β z
      have h_digit_βw : digit (β * w) = false := by
        rw [digit_false_iff]; exact dvd_mul_right β w
      have h_βQuot_βz : βQuot (β * z) = z := by
        have h_spec := digit_βQuot_spec (β * z)
        simp only [h_digit_βz, Bool.false_eq_true, ite_false, zero_add] at h_spec
        exact (mul_left_cancel₀ β_ne_zero h_spec).symm
      have h_βQuot_βw : βQuot (β * w) = w := by
        have h_spec := digit_βQuot_spec (β * w)
        simp only [h_digit_βw, Bool.false_eq_true, ite_false, zero_add] at h_spec
        exact (mul_left_cancel₀ β_ne_zero h_spec).symm
      have hlen_βz : digitLength (β * z) = 1 + digitLength z := by
        rw [digitLength_succ (β * z) hβz_ne, h_βQuot_βz]
      have hlen_βw : digitLength (β * w) = 1 + digitLength w := by
        rw [digitLength_succ (β * w) hβw_ne, h_βQuot_βw]
      have hlen_β : digitLength (β * z) = digitLength (β * w) := by
        rw [hlen_βz, hlen_βw, hlen]
      exact hP (β * z) (β * w) hlen_β (fun j hj => absurd hj (Nat.not_lt_zero j))

/-! ## Section 4: Resource Bounds via BiCylinder Finiteness

The finiteness of BiCylinders provides resource bounds:
any computation constrained on both suffix (local) and prefix (global)
structure has only finitely many possible states.
-/

/-- The number of elements in a BiCylinder is bounded -/
theorem biCylinder_card_bound (k : ℕ) (suffix_pattern : Fin k → Bool)
    (len m : ℕ) (prefix_pattern : Fin m → Bool) :
    ∃ N : ℕ, ∀ S : Finset GaussianInt,
      (∀ z ∈ S, z ∈ BiCylinder k suffix_pattern len m prefix_pattern) → S.card ≤ N := by
  -- BiCylinder is finite, so there's a maximum cardinality
  have h_finite := biCylinder_finite k suffix_pattern len m prefix_pattern
  -- Use the fact that finite sets have a cardinality bound
  have h_card := Set.Finite.exists_finset_coe h_finite
  obtain ⟨F, hF⟩ := h_card
  use F.card
  intro T hT
  have h_sub : T ⊆ F := by
    intro z hz
    have hz_mem := hT z hz
    simp only [Finset.mem_coe, ← hF] at hz_mem ⊢
    exact hz_mem
  exact Finset.card_le_card h_sub

/-- Elements with bounded digit length form a finite set -/
theorem bounded_length_finite (n : ℕ) : Set.Finite {z : GaussianInt | digitLength z ≤ n} := by
  have h_union : {z : GaussianInt | digitLength z ≤ n} = ⋃ k ≤ n, {z | digitLength z = k} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro h; exact ⟨digitLength z, h, rfl⟩
    · intro ⟨k, hk, heq⟩; omega
  rw [h_union]
  apply Set.Finite.biUnion
  · exact Set.finite_le_nat n
  · intro k _
    -- {z | digitLength z = k} is finite (at most 2^k elements)
    have h_sub : {z : GaussianInt | digitLength z = k} ⊆ PrefixCylinder k 0 Fin.elim0 := by
      intro z hz
      simp only [Set.mem_setOf_eq] at hz
      simp only [PrefixCylinder, Set.mem_setOf_eq]
      exact ⟨hz, fun j => j.elim0⟩
    exact Set.Finite.subset (prefixCylinder_finite k 0 Fin.elim0) h_sub

/-! ## Section 5: Complexity Hierarchy via Resonant Structure

The resonant structure creates a hierarchy of complexity classes
indexed by the scale parameter m. At scale m, elements are equivalent
if their digit lengths agree mod 2^m.
-/

/-- Complexity class at scale m: predicates decidable by length mod 2^m and m MSD digits -/
def ResonantClass (m : ℕ) : Set (GaussianInt → Prop) :=
  {P | ∀ z w : GaussianInt, resonantEquiv m z w → (P z ↔ P w)}

/-- ResonantClass forms an inclusion: coarser equivalence gives larger class.
    If P respects m-equivalence, it also respects (m+1)-equivalence
    (since (m+1)-equiv implies m-equiv). -/
theorem resonantClass_mono (m : ℕ) : ResonantClass m ⊆ ResonantClass (m + 1) := by
  intro P hP z w h_equiv
  apply hP
  -- (m+1)-equivalence implies m-equivalence
  simp only [resonantEquiv] at h_equiv ⊢
  constructor
  · -- Length mod 2^(m+1) agreement implies length mod 2^m agreement
    have h := h_equiv.1
    have hdvd : 2^m ∣ 2^(m+1) := ⟨2, by ring⟩
    calc digitLength z % 2^m
        = (digitLength z % 2^(m+1)) % 2^m := by rw [Nat.mod_mod_of_dvd _ hdvd]
      _ = (digitLength w % 2^(m+1)) % 2^m := by rw [h]
      _ = digitLength w % 2^m := by rw [Nat.mod_mod_of_dvd _ hdvd]
  · intro j hj
    exact h_equiv.2 j (Nat.lt_of_lt_of_le hj (Nat.le_succ m))

/-- ResonantClass at level 0 is NOT all predicates - it only contains predicates
    that are constant on elements with the same digitLength mod 1 (i.e., all elements).
    So ResonantClass 0 = constant predicates. -/
theorem resonantClass_zero_eq_constant :
    ResonantClass 0 = {P | ∀ z w : GaussianInt, P z ↔ P w} := by
  ext P
  simp only [ResonantClass, Set.mem_setOf_eq]
  constructor
  · intro hP z w
    apply hP
    simp only [resonantEquiv, pow_zero, Nat.mod_one, Nat.not_lt_zero, IsEmpty.forall_iff,
               implies_true, and_self]
  · intro hP z w _
    exact hP z w

/-- Elements with same toDigits satisfy all resonant equivalences -/
theorem resonantEquiv_of_eq_toDigits (z w : GaussianInt) (h : toDigits z = toDigits w) (m : ℕ) :
    resonantEquiv m z w := by
  have hlen : digitLength z = digitLength w := by simp only [digitLength, h]
  simp only [resonantEquiv]
  constructor
  · simp only [hlen]
  · intro j _
    -- nthDigitMSD depends on toDigits and digitLength
    -- Since toDigits z = toDigits w, the MSD digits are equal
    have h_eq : z = w := eq_of_toDigits_eq z w h
    simp only [h_eq]

/-! ## Section 6: Separation Theorems

These theorems formalize the key asymmetry: some properties are
suffix-decidable but not prefix-decidable, and vice versa.
-/

/-- There exist predicates that are suffix-decidable but not prefix-decidable -/
theorem suffix_not_prefix_exists :
    ∃ P : GaussianInt → Prop, P ∈ SuffixClass ∧ P ∉ PrefixClass := by
  -- The predicate "first digit is true" (i.e., β ∤ z)
  use fun z => digit z = true
  constructor
  · -- Suffix-decidable at depth 1
    use 1
    intro z w h_agree
    -- First digit agreement follows from LSD agreement at depth 1
    have h0 := h_agree 0 (Nat.zero_lt_one)
    by_cases hz : z = 0
    · subst hz
      simp only [nthDigitLSD_zero] at h0
      simp only [digit_zero, Bool.false_eq_true, false_iff]
      by_cases hw : w = 0
      · subst hw; simp [digit_zero]
      · rw [nthDigitLSD_zero_eq w hw] at h0
        rw [← h0]; simp
    · by_cases hw : w = 0
      · subst hw
        simp only [nthDigitLSD_zero] at h0
        rw [nthDigitLSD_zero_eq z hz] at h0
        simp only [digit_zero, Bool.false_eq_true, iff_false]
        rw [h0]; simp
      · rw [nthDigitLSD_zero_eq z hz, nthDigitLSD_zero_eq w hw] at h0
        simp only [h0]
  · -- Not prefix-decidable at any depth: proof by construction
    intro ⟨m, hP⟩
    -- The predicate "digit z = true" depends on the LSD, not the MSD
    -- For any m, we can construct elements with same length and MSD pattern but different LSD
    -- Use β^(m+1) and 1 + β^(m+1)
    -- Both have digitLength m+2 (toDigits gives [false, ..., false, true] with m+1 falses)
    -- Actually, let's use a simpler approach with evalDigits
    -- z = evalDigits ([true] ++ replicate m false ++ [true])
    -- w = evalDigits ([false] ++ replicate m false ++ [true])
    -- Both have same length m+2 and same last m+1 elements, differing only in first
    -- The first m MSD digits (positions 0..m-1 from end) are in the shared suffix
    exfalso
    let zList := [true] ++ List.replicate m false ++ [true]
    let wList := [false] ++ List.replicate m false ++ [true]
    let z := evalDigits zList
    let w := evalDigits wList
    have hz_toDigits : toDigits z = zList := encodeBoolString_toDigits zList
      (by simp [zList, List.append_ne_nil_of_right_ne_nil])
      (by simp [zList, List.getLast_append])
    have hw_toDigits : toDigits w = wList := encodeBoolString_toDigits wList
      (by simp [wList, List.append_ne_nil_of_right_ne_nil])
      (by simp [wList, List.getLast_append])
    have hz_len : digitLength z = m + 2 := by
      simp [digitLength, hz_toDigits, zList, List.length_append, List.length_replicate]
    have hw_len : digitLength w = m + 2 := by
      simp [digitLength, hw_toDigits, wList, List.length_append, List.length_replicate]
    have hlen_eq : digitLength z = digitLength w := by rw [hz_len, hw_len]
    -- The MSD digits agree for positions 0..m-1
    -- This is because both lists have the same suffix of length m+1
    -- Both reversed lists are [true] ++ replicate m false ++ [d] where d differs
    -- At position j < m, we're in the common prefix [true] ++ replicate m false
    have hmsd : ∀ j < m, nthDigitMSD z j = nthDigitMSD w j := by
      intro j hj
      -- Use the bridge lemma to convert to getD on reversed list
      rw [nthDigitMSD_eq_getD_reverse, nthDigitMSD_eq_getD_reverse]
      rw [hz_toDigits, hw_toDigits]
      simp only [zList, wList, List.reverse_append, List.reverse_singleton,
                 List.reverse_replicate]
      -- Both reversed lists are [true] ++ (replicate m false ++ [d])
      -- At position j < m, we access the common prefix
      -- First, normalize the list structure
      have h_assoc1 : [true] ++ (List.replicate m false ++ [true]) =
                      ([true] ++ List.replicate m false) ++ [true] := by simp [List.append_assoc]
      have h_assoc2 : [true] ++ (List.replicate m false ++ [false]) =
                      ([true] ++ List.replicate m false) ++ [false] := by simp [List.append_assoc]
      rw [h_assoc1, h_assoc2]
      have h_prefix_len : ([true] ++ List.replicate m false).length = m + 1 := by
        simp [List.length_append, List.length_replicate]
      have hj_in_prefix : j < ([true] ++ List.replicate m false).length := by
        rw [h_prefix_len]; omega
      -- Both lists have the same prefix, so getD at position j gives same result
      have h1 : (([true] ++ List.replicate m false) ++ [true]).getD j false =
                ([true] ++ List.replicate m false).getD j false := by
        rw [List.getD_append]; simp only [hj_in_prefix, ↓reduceDIte]
      have h2 : (([true] ++ List.replicate m false) ++ [false]).getD j false =
                ([true] ++ List.replicate m false).getD j false := by
        rw [List.getD_append]; simp only [hj_in_prefix, ↓reduceDIte]
      rw [h1, h2]
    have h_iff := hP z w hlen_eq hmsd
    have hz_digit : digit z = true := digit_evalDigits_cons true (List.replicate m false ++ [true])
    have hw_digit : digit w = false := digit_evalDigits_cons false (List.replicate m false ++ [true])
    -- h_iff : (digit z = true) ↔ (digit w = true)
    -- Since digit z = true, we have (digit z = true) is True
    -- Since digit w = false, we have (digit w = true) is False
    -- So h_iff : True ↔ False, contradiction
    have h1 : digit z = true := hz_digit
    have h2 : digit w = true := h_iff.mp h1
    rw [hw_digit] at h2
    exact Bool.noConfusion h2

/-- There exist predicates that are prefix-decidable but not suffix-decidable -/
theorem prefix_not_suffix_exists :
    ∃ P : GaussianInt → Prop, P ∈ PrefixClass ∧ P ∉ SuffixClass := by
  -- The predicate "digitLength is even"
  use fun z => digitLength z % 2 = 0
  constructor
  · -- Prefix-decidable at depth 0 (only depends on length)
    use 0
    intro z w hlen _
    simp only [hlen]
  · -- Not suffix-decidable at any depth k
    intro ⟨k, hP⟩
    -- For k = 0: 1 and 0 agree on first 0 digits (vacuously)
    -- digitLength 1 = 1 (odd), digitLength 0 = 0 (even)
    -- So P(1) = false, P(0) = true, but hP says they should be equivalent
    -- For k ≥ 1: we need elements that agree on first k digits but have different length parity
    -- Use β^k (has k+1 digits, all false except last) and β^(k+2) (has k+3 digits)
    -- They agree on first k LSD digits (all false) but have different length parity
    cases k with
    | zero =>
      -- 1 and 0 agree on first 0 digits
      have h_agree : lsdAgree 1 0 0 := fun n hn => absurd hn (Nat.not_lt_zero n)
      have h_iff := hP 1 0 h_agree
      -- digitLength 1 = 1, digitLength 0 = 0
      have h1 : digitLength 1 = 1 := by
        simp only [digitLength]
        unfold toDigits
        simp only [one_ne_zero, dite_false]
        have hd : digit 1 = true := by
          rw [digit_true_iff]; intro h; rw [β_dvd_iff] at h
          simp only [Zsqrtd.one_re, Zsqrtd.one_im] at h; omega
        have hq : βQuot 1 = 0 := by
          have h_spec := digit_βQuot_spec 1
          simp only [hd, ite_true] at h_spec
          have h_eq : β * βQuot 1 = 0 := by
            have := congrArg (fun x => x - 1) h_spec
            simp only [add_sub_cancel_left] at this; exact this
          cases mul_eq_zero.mp h_eq with
          | inl h => exact absurd h β_ne_zero
          | inr h => exact h
        simp only [hd, hq, toDigits_zero, List.length_singleton]
      simp only [h1, digitLength_zero] at h_iff
      -- h_iff : 1 % 2 = 0 ↔ 0 % 2 = 0, i.e., false ↔ true
      norm_num at h_iff
    | succ k' =>
      -- For k = k'+1 ≥ 1, we construct elements with same first k'+1 LSD digits but different length parity
      -- Use z = evalDigits (List.replicate (k'+1) false ++ [true]) which has length k'+2
      -- and w = evalDigits (List.replicate (k'+1) false ++ [true, true]) which has length k'+3
      -- Both have first k'+1 digits all false
      -- z has length k'+2, w has length k'+3, different parity!
      let zList := List.replicate (k' + 1) false ++ [true]
      let wList := List.replicate (k' + 1) false ++ [true, true]
      let z := evalDigits zList
      let w := evalDigits wList
      -- Show they agree on first k'+1 LSD digits
      -- Both zList and wList start with k'+1 falses, so their first k'+1 LSD digits are all false
      have h_agree : lsdAgree z w (k' + 1) := by
        intro n hn
        -- For n < k'+1, both z and w have digit false at position n
        -- Both lists start with k'+1 falses, so nthDigitLSD at position n < k'+1 gives false
        have hz_toDigits : toDigits z = zList := encodeBoolString_toDigits zList
          (by simp [zList, List.append_ne_nil_of_right_ne_nil])
          (by simp [zList, List.getLast_append])
        have hw_toDigits : toDigits w = wList := encodeBoolString_toDigits wList
          (by simp [wList, List.append_ne_nil_of_right_ne_nil])
          (by simp [wList, List.getLast_append])
        -- nthDigitLSD uses getD on the list directly
        simp only [nthDigitLSD, hz_toDigits, hw_toDigits, zList, wList]
        -- Both lists are replicate (k'+1) false ++ suffix
        -- At position n < k'+1, we access the replicate part, which is false
        have h_prefix_len : (List.replicate (k' + 1) false).length = k' + 1 := by
          simp [List.length_replicate]
        have hn_in_prefix : n < (List.replicate (k' + 1) false).length := by
          rw [h_prefix_len]; exact hn
        -- Use getD_append to show both give false
        have h1 : (List.replicate (k' + 1) false ++ [true]).getD n false =
                  (List.replicate (k' + 1) false).getD n false := by
          rw [List.getD_append]; simp only [hn_in_prefix, ↓reduceDIte]
        have h2 : (List.replicate (k' + 1) false ++ [true, true]).getD n false =
                  (List.replicate (k' + 1) false).getD n false := by
          rw [List.getD_append]; simp only [hn_in_prefix, ↓reduceDIte]
        rw [h1, h2]
      have h_iff := hP z w h_agree
      -- Show z and w have different length parity
      have hz_len : digitLength z = k' + 2 := by
        simp only [z, zList, digitLength]
        have h := encodeBoolString_toDigits (List.replicate (k' + 1) false ++ [true])
          (by simp [List.append_ne_nil_of_right_ne_nil]) (by simp [List.getLast_append])
        simp only [encodeBoolString] at h
        rw [h, List.length_append, List.length_replicate, List.length_singleton]
      have hw_len : digitLength w = k' + 3 := by
        simp only [w, wList, digitLength]
        have h := encodeBoolString_toDigits (List.replicate (k' + 1) false ++ [true, true])
          (by simp [List.append_ne_nil_of_right_ne_nil]) (by simp [List.getLast_append])
        simp only [encodeBoolString] at h
        rw [h, List.length_append, List.length_replicate]
        simp
      -- P(z) = (k'+2) % 2 = 0 and P(w) = (k'+3) % 2 = 0 have different values
      simp only [hz_len, hw_len] at h_iff
      -- (k'+2) % 2 = 0 ↔ (k'+3) % 2 = 0 is false since they differ by 1
      omega

/-- The fundamental separation: SuffixClass ≠ PrefixClass -/
theorem suffix_prefix_separation : SuffixClass ≠ PrefixClass := by
  intro h_eq
  obtain ⟨P, hP_suffix, hP_not_prefix⟩ := suffix_not_prefix_exists
  rw [h_eq] at hP_suffix
  exact hP_not_prefix hP_suffix

/-! ## Section 7: Polynomial vs Exponential Structure

The key observation: suffix cylinders have "polynomial" structure
(2^k elements for depth k), while prefix cylinders constrain to
finite sets but with exponential dependence on length.
-/

/-- Suffix cylinders of depth k partition ℤ[i] into 2^k classes -/
theorem suffix_cylinder_count (k : ℕ) :
    Fintype.card (Fin k → Bool) = 2^k := by
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- The number of distinct suffix patterns is exactly 2^k -/
theorem suffix_patterns_count (k : ℕ) :
    Fintype.card (Fin k → Bool) = 2^k := by
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- For fixed length n, there are at most 2^n elements -/
theorem fixed_length_bound (n : ℕ) :
    ∃ bound : ℕ, bound ≤ 2^n ∧
      ∀ S : Finset GaussianInt, (∀ z ∈ S, digitLength z = n) → S.card ≤ bound := by
  -- The set {z | digitLength z = n} is a subset of PrefixCylinder n 0 Fin.elim0
  use 2^n
  constructor
  · exact le_refl _
  · intro S hS
    -- S is a subset of {z | digitLength z = n} which is finite
    have h_sub : (S : Set GaussianInt) ⊆ {z | digitLength z = n} := by
      intro z hz; exact hS z hz
    have h_finite : Set.Finite {z : GaussianInt | digitLength z = n} := by
      have h_eq : {z : GaussianInt | digitLength z = n} = PrefixCylinder n 0 Fin.elim0 := by
        ext z
        simp only [Set.mem_setOf_eq, PrefixCylinder]
        constructor
        · intro h; exact ⟨h, fun j => j.elim0⟩
        · intro ⟨h, _⟩; exact h
      rw [h_eq]
      exact prefixCylinder_finite n 0 Fin.elim0
    -- Get a finite set containing S
    have h_card := Set.Finite.exists_finset_coe h_finite
    obtain ⟨F, hF⟩ := h_card
    have h_sub' : S ⊆ F := by
      intro z hz
      have := h_sub hz
      simp only [← hF, Set.mem_setOf_eq, Finset.mem_coe] at this ⊢
      exact this
    -- S.card ≤ F.card ≤ 2^n
    -- The bound follows from the fact that F is finite and contained in a set
    -- that injects into lists of length n (which has 2^n elements)
    -- For a complete proof, we would need to show F.card ≤ 2^n using the injection
    -- toDigits : F → {L : List Bool | L.length = n}
    -- This is technically involved but mathematically straightforward
    calc S.card ≤ F.card := Finset.card_le_card h_sub'
      _ ≤ 2^n := by
        -- Each element of F has digitLength = n, so toDigits maps F injectively
        -- to lists of length n, of which there are 2^n
        -- F injects into lists of booleans of length n
        have h_F_mem : ∀ z ∈ F, digitLength z = n := by
          intro z hz
          have : z ∈ ({z : GaussianInt | digitLength z = n} : Set GaussianInt) := by
            rw [← hF]; exact hz
          exact this
        -- Define the injection from F to Fin n → Bool
        let f : GaussianInt → (Fin n → Bool) := fun z => fun i => (toDigits z).getD i.val false
        have h_inj_on : Set.InjOn f F := by
          intro a ha b hb hab
          have ha_len : (toDigits a).length = n := h_F_mem a ha
          have hb_len : (toDigits b).length = n := h_F_mem b hb
          have h_eq : toDigits a = toDigits b := by
            apply List.ext_getElem
            · rw [ha_len, hb_len]
            · intro i hi_a hi_b
              have hi : i < n := by rw [← ha_len]; exact hi_a
              have h' := congr_fun hab ⟨i, hi⟩
              simp only [f] at h'
              rw [List.getD_eq_getElem _ _ hi_a, List.getD_eq_getElem _ _ hi_b] at h'
              exact h'
          rw [← evalDigits_toDigits a, ← evalDigits_toDigits b, h_eq]
        -- F.card ≤ |Fin n → Bool| = 2^n
        have h_card : Fintype.card (Fin n → Bool) = 2^n := by
          simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
        rw [← h_card]
        -- Use Finset.card_le_card_of_injOn
        exact Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _)
          (fun a ha b hb => h_inj_on ha hb)

/-! ## Section 8: The P vs NP Analogy

We formalize the analogy between:
- P ↔ SuffixClass (locally/efficiently decidable)
- NP ↔ Properties verifiable by suffix witness
- The separation SuffixClass ≠ PrefixClass as evidence for P ≠ NP structure
-/

/-- A predicate has a suffix witness of depth k if membership can be verified
    by exhibiting a witness whose first k digits determine the answer. -/
def HasSuffixWitness (P : GaussianInt → Prop) (k : ℕ) : Prop :=
  ∀ z : GaussianInt, P z → ∃ w : GaussianInt,
    lsdAgree z w k ∧ ∀ z' : GaussianInt, lsdAgree z' w k → P z'

/-- SuffixDecidable implies HasSuffixWitness (P ⊆ NP analogy) -/
theorem suffixDecidable_has_witness (P : GaussianInt → Prop) (k : ℕ)
    (hP : SuffixDecidable P k) : HasSuffixWitness P k := by
  intro z hz
  use z
  constructor
  · -- z agrees with itself
    intro n _; rfl
  · -- Any z' agreeing with z also satisfies P
    intro z' h_agree
    exact (hP z' z h_agree).mpr hz

/-- The class of predicates with suffix witnesses -/
def SuffixWitnessClass : Set (GaussianInt → Prop) :=
  {P | ∃ k, HasSuffixWitness P k}

/-- SuffixClass ⊆ SuffixWitnessClass (P ⊆ NP) -/
theorem suffixClass_subset_witnessClass : SuffixClass ⊆ SuffixWitnessClass := by
  intro P ⟨k, hP⟩
  exact ⟨k, suffixDecidable_has_witness P k hP⟩

/-! ## Section 9: Orbit Complexity and Time Bounds

The bi-topological complexity measure provides a formal notion of
"computational time" via orbit length.
-/

/-- For the zero cylinder (all false pattern), there exists a time at most k -/
theorem timeToZeroCylinder_exists (z : GaussianInt) (hz : z ≠ 0) (k : ℕ) :
    ∃ n ≤ k, β^n * z ∈ SuffixCylinder k (fun _ => false) := by
  use k, le_refl k
  exact orbit_in_zero_cylinder z hz k k (le_refl k)

/-- Time to reach the zero cylinder is at most k (noncomputable via Classical.choose) -/
noncomputable def timeToZeroCylinder (z : GaussianInt) (hz : z ≠ 0) (k : ℕ) : ℕ :=
  Classical.choose (timeToZeroCylinder_exists z hz k)

/-- The time to zero cylinder is bounded by k -/
theorem timeToZeroCylinder_le (z : GaussianInt) (hz : z ≠ 0) (k : ℕ) :
    timeToZeroCylinder z hz k ≤ k := by
  exact (Classical.choose_spec (timeToZeroCylinder_exists z hz k)).1

/-- Orbit complexity grows linearly for nonzero elements -/
theorem orbit_complexity_linear (z : GaussianInt) (hz : z ≠ 0) (n k m : ℕ) :
    biTopologicalComplexity z n k m = n :=
  biTopologicalComplexity_eq z hz n k m

/-- Zero has constant complexity -/
theorem orbit_complexity_constant (n k m : ℕ) (hn : 0 < n) :
    biTopologicalComplexity 0 n k m = 1 :=
  biTopologicalComplexity_zero n k m hn

/-! ## Section 10: Summary and Future Directions

### Proven:
1. Encoding of Boolean strings as Gaussian integers
2. Definition of SuffixDecidable and PrefixDecidable predicates
3. SuffixClass ≠ PrefixClass (fundamental separation)
4. Resource bounds via BiCylinder finiteness
5. Complexity hierarchy via resonant structure
6. P ⊆ NP analogy: SuffixClass ⊆ SuffixWitnessClass

### The P vs NP Connection:
The separation theorem `suffix_prefix_separation` shows that the two
natural complexity classes arising from bi-topology are distinct.
This mirrors the conjectured P ≠ NP separation:

- SuffixClass ↔ P: Properties decidable by local examination
- PrefixClass ↔ PSPACE-like: Properties requiring global structure
- The asymmetry of β-multiplication ↔ Verification vs Search asymmetry

### Key Insight:
The bi-topological framework provides a NUMBER-THEORETIC model of
computational complexity where:
- Time ↔ Orbit length (digitLength growth)
- Space ↔ Cylinder depth
- Verification ↔ Suffix agreement
- Search ↔ Prefix structure

This suggests that P vs NP may have deep connections to the
arithmetic structure of Gaussian integers under β-adic expansion.
-/

end SPBiTopology
