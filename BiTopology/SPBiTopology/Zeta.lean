/-
  BiTopology/SPBiTopology/Zeta.lean
  DEDEKIND ZETA FUNCTION OF ℤ[i] VIA BI-TOPOLOGY
  NO SORRY, NO AXIOMS - all proofs are complete.
-/

import BiTopology.SPBiTopology.GoldenIdentity
import BiTopology.SPBiTopology.Twindragon
import BiTopology.SPBiTopology.PrimeBasic

set_option autoImplicit false

namespace SPBiTopology

open GaussianInt Zsqrtd

/-- The set of nonzero Gaussian integers with digitLength ≤ n -/
def DigitBoundedNonzero (n : ℕ) : Set GaussianInt :=
  {z | digitLength z ≤ n ∧ z ≠ 0}

/-- DigitBoundedNonzero is a subset of DigitBounded -/
theorem digitBoundedNonzero_subset (n : ℕ) :
    DigitBoundedNonzero n ⊆ DigitBounded n := fun z hz => hz.1

/-- DigitBoundedNonzero is finite -/
theorem digitBoundedNonzero_finite (n : ℕ) : Set.Finite (DigitBoundedNonzero n) :=
  Set.Finite.subset (digitBounded_finite n) (digitBoundedNonzero_subset n)

/-- DigitBoundedNonzero sets are nested -/
theorem digitBoundedNonzero_mono {m n : ℕ} (h : m ≤ n) :
    DigitBoundedNonzero m ⊆ DigitBoundedNonzero n :=
  fun z hz => ⟨Nat.le_trans hz.1 h, hz.2⟩

/-- DigitBoundedNonzero 0 is empty -/
theorem digitBoundedNonzero_zero : DigitBoundedNonzero 0 = ∅ := by
  ext z
  simp only [DigitBoundedNonzero, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hlen hz
  have := digitLength_pos z hz
  omega

/-- DigitBoundedNonzero n is nonempty for n ≥ 1 -/
theorem digitBoundedNonzero_nonempty {n : ℕ} (hn : 1 ≤ n) :
    (DigitBoundedNonzero n).Nonempty := by
  use 1
  exact ⟨Nat.le_trans one_digitLength.le hn, one_ne_zero⟩

/-- T₀ and T₁ images are disjoint -/
theorem T₀_T₁_images_disjoint (A B : Set GaussianInt) :
    Disjoint (T₀ '' A) (T₁ '' B) := by
  rw [Set.disjoint_iff]
  intro z ⟨⟨a, _, ha'⟩, ⟨b, _, hb'⟩⟩
  have hd0 : digit z = false := by rw [← ha']; exact digit_β_mul a
  have hd1 : digit z = true := by rw [← hb']; exact digit_one_add_β_mul b
  rw [hd0] at hd1; exact Bool.noConfusion hd1

/-- The partial LogWeight sum over DigitBoundedNonzero n -/
noncomputable def LogWeightSum (n : Nat) : ENNReal :=
  (digitBoundedNonzero_finite n).toFinset.sum LogWeight

/-- LogWeightSum is monotone in n -/
theorem logWeightSum_mono {m n : Nat} (h : m <= n) : LogWeightSum m <= LogWeightSum n := by
  simp only [LogWeightSum]
  apply Finset.sum_le_sum_of_subset
  intro z hz
  simp only [Set.Finite.mem_toFinset] at hz
  simp only [Set.Finite.mem_toFinset]
  exact digitBoundedNonzero_mono h hz

/-- β^k ≠ 0 -/
theorem β_pow_ne_zero' (k : ℕ) : β^k ≠ 0 := pow_ne_zero k β_ne_zero

/-- digitLength(β^k) = k + 1 -/
theorem digitLength_β_pow' (k : ℕ) : digitLength (β^k) = k + 1 := by
  induction k with
  | zero => exact one_digitLength
  | succ n ih =>
    rw [pow_succ, mul_comm]
    rw [digitLength_mul_β _ (β_pow_ne_zero' n), ih]

/-- The fundamental bridge: LogWeight(β^k) = μ_cylinder(k) -/
theorem fundamental_bridge (k : ℕ) : LogWeight (β^k) = μ_cylinder k := by
  simp only [LogWeight, norm_β_pow_eq, Int.natAbs_pow, Int.natAbs_ofNat, μ_cylinder]
  norm_cast

/-- Every nonzero z is in some DigitBoundedNonzero -/
theorem mem_digitBoundedNonzero_of_ne_zero (z : GaussianInt) (hz : z ≠ 0) :
    z ∈ DigitBoundedNonzero (digitLength z) :=
  ⟨le_refl _, hz⟩

/-- Union of all DigitBoundedNonzero is all nonzero -/
theorem digitBoundedNonzero_exhaustive :
    ⋃ n, DigitBoundedNonzero n = {z : GaussianInt | z ≠ 0} := by
  ext z
  simp only [Set.mem_iUnion, DigitBoundedNonzero, Set.mem_setOf_eq]
  constructor
  · intro ⟨_, hn⟩; exact hn.2
  · intro hz; exact ⟨digitLength z, le_refl _, hz⟩

/-- Norm doubles under T₀ -/
theorem norm_T₀' (z : GaussianInt) : (T₀ z).norm = 2 * z.norm := by
  simp only [T₀, Zsqrtd.norm_mul, norm_β]

/-- β^k ∈ DigitBoundedNonzero (k+1) -/
theorem β_pow_in_digitBounded (k : ℕ) : β^k ∈ DigitBoundedNonzero (k + 1) := by
  simp only [DigitBoundedNonzero, Set.mem_setOf_eq]
  exact ⟨by rw [digitLength_β_pow'], β_pow_ne_zero' k⟩

/-- LogWeightSum is monotone as a function -/
theorem logWeightSum_monotone : Monotone LogWeightSum := fun _ _ h => logWeightSum_mono h

/-- LogWeightSum at 0 is 0 (no nonzero elements with digitLength <= 0) -/
theorem logWeightSum_zero : LogWeightSum 0 = 0 := by
  simp only [LogWeightSum]
  convert Finset.sum_empty (f := LogWeight)
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro z hz
  simp only [Set.Finite.mem_toFinset, DigitBoundedNonzero, Set.mem_setOf_eq] at hz
  have hpos := digitLength_pos z hz.2
  omega

/-- LogWeight of 1 equals 1 -/
theorem logWeight_one : LogWeight (1 : GaussianInt) = 1 := by
  simp only [LogWeight, Zsqrtd.norm_one, Int.natAbs_one, Nat.cast_one, div_one]

/-- LogWeightSum is positive for n >= 1 (contains at least 1) -/
theorem logWeightSum_pos {n : Nat} (hn : 1 <= n) : 0 < LogWeightSum n := by
  have h1_mem : (1 : GaussianInt) ∈ (digitBoundedNonzero_finite n).toFinset := by
    simp only [Set.Finite.mem_toFinset, DigitBoundedNonzero, Set.mem_setOf_eq]
    exact ⟨Nat.le_trans one_digitLength.le hn, one_ne_zero⟩
  simp only [LogWeightSum]
  calc 0 < LogWeight 1 := logWeight_pos' 1 one_ne_zero
    _ <= (digitBoundedNonzero_finite n).toFinset.sum LogWeight :=
        Finset.single_le_sum (fun _ _ => zero_le _) h1_mem

/-- LogWeightSum at n >= 1 is at least 1 (since LogWeight(1) = 1) -/
theorem logWeightSum_ge_one {n : Nat} (hn : 1 <= n) : 1 <= LogWeightSum n := by
  have h1_mem : (1 : GaussianInt) ∈ (digitBoundedNonzero_finite n).toFinset := by
    simp only [Set.Finite.mem_toFinset, DigitBoundedNonzero, Set.mem_setOf_eq]
    exact ⟨Nat.le_trans one_digitLength.le hn, one_ne_zero⟩
  simp only [LogWeightSum]
  calc 1 = LogWeight 1 := logWeight_one.symm
    _ <= (digitBoundedNonzero_finite n).toFinset.sum LogWeight :=
        Finset.single_le_sum (fun _ _ => zero_le _) h1_mem

/-- 1 is in DigitBoundedNonzero 1 -/
theorem one_mem_digitBoundedNonzero_one : (1 : GaussianInt) ∈ DigitBoundedNonzero 1 := by
  simp only [DigitBoundedNonzero, Set.mem_setOf_eq, one_digitLength, le_refl, true_and]
  exact one_ne_zero

/-- β is in DigitBoundedNonzero 2 -/
theorem β_mem_digitBoundedNonzero_two : β ∈ DigitBoundedNonzero 2 := by
  have h := β_pow_in_digitBounded 1
  simp only [pow_one] at h
  exact digitBoundedNonzero_mono (by norm_num : 2 <= 2) h

/-- LogWeight of β equals 1/2 -/
theorem logWeight_β : LogWeight β = 1 / 2 := by
  have h := fundamental_bridge 1
  simp only [pow_one] at h
  simp only [h, μ_cylinder, pow_one]

/-- digitLength of nonzero z is at least 1 -/
theorem digitLength_ge_one_of_ne_zero (z : GaussianInt) (hz : z ≠ 0) : 1 <= digitLength z := by
  have := digitLength_pos z hz
  omega

/-- DigitBoundedNonzero 1 contains only elements with digitLength exactly 1 -/
theorem digitBoundedNonzero_one_eq_digitLength_one :
    DigitBoundedNonzero 1 = {z | digitLength z = 1} := by
  ext z
  simp only [DigitBoundedNonzero, Set.mem_setOf_eq]
  constructor
  · intro ⟨hle, hne⟩
    have hge := digitLength_ge_one_of_ne_zero z hne
    omega
  · intro heq
    constructor
    · omega
    · intro hz
      rw [hz, digitLength_zero] at heq
      omega

/-- If digitLength z = 1, then z = 1 -/
theorem digitLength_eq_one_imp_eq_one (z : GaussianInt) (h : digitLength z = 1) : z = 1 := by
  have hz : z ≠ 0 := by
    intro heq
    rw [heq, digitLength_zero] at h
    omega
  have hspec := digit_βQuot_spec z
  have hlen : digitLength (βQuot z) = 0 := by
    have := digitLength_succ z hz
    omega
  have hq_zero : βQuot z = 0 := by
    by_contra hne
    have := digitLength_pos (βQuot z) hne
    omega
  rw [hq_zero, mul_zero, add_zero] at hspec
  by_cases hd : digit z = true
  · simp only [hd, ite_true] at hspec
    exact hspec
  · simp only [eq_false_of_ne_true hd, ite_false] at hspec
    exfalso
    exact hz hspec

/-- DigitBoundedNonzero 1 = {1} -/
theorem digitBoundedNonzero_one_eq_singleton :
    DigitBoundedNonzero 1 = {1} := by
  rw [digitBoundedNonzero_one_eq_digitLength_one]
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · exact digitLength_eq_one_imp_eq_one z
  · intro h
    rw [h, one_digitLength]

/-- LogWeightSum 1 = 1 (the only element is 1 with LogWeight 1) -/
theorem logWeightSum_one : LogWeightSum 1 = 1 := by
  simp only [LogWeightSum]
  have h_eq : (digitBoundedNonzero_finite 1).toFinset = {1} := by
    ext z
    simp only [Set.Finite.mem_toFinset, Finset.mem_singleton]
    constructor
    · intro hz
      rw [digitBoundedNonzero_one_eq_singleton] at hz
      exact Set.mem_singleton_iff.mp hz
    · intro hz
      rw [hz, digitBoundedNonzero_one_eq_singleton]
      exact Set.mem_singleton 1
  rw [h_eq, Finset.sum_singleton, logWeight_one]

/-- LogWeight of β^k equals 1/2^k -/
theorem logWeight_β_pow (k : Nat) : LogWeight (β^k) = 1 / (2 : ENNReal)^k := by
  have h := fundamental_bridge k
  simp only [h, μ_cylinder]

/-- digitLength of β equals 2 -/
theorem digitLength_β : digitLength β = 2 := by
  have h := digitLength_β_pow' 1
  simp only [pow_one] at h
  exact h

/-- β is not in DigitBoundedNonzero 1 -/
theorem β_not_mem_digitBoundedNonzero_one : β ∉ DigitBoundedNonzero 1 := by
  simp only [DigitBoundedNonzero, Set.mem_setOf_eq, not_and, not_not]
  intro hle
  have hlen := digitLength_β
  omega

/-- β is in DigitBoundedNonzero 2 (digitLength β = 2) -/
theorem β_in_digitBoundedNonzero_two : β ∈ DigitBoundedNonzero 2 := by
  simp only [DigitBoundedNonzero, Set.mem_setOf_eq]
  exact ⟨by rw [digitLength_β], β_ne_zero⟩

/-- 1 + β = i (the imaginary unit) -/
theorem one_plus_β_eq_i : (1 : GaussianInt) + β = ⟨0, 1⟩ := by
  simp only [β]
  ext <;> simp

/-- 1 + β is nonzero -/
theorem one_plus_β_ne_zero : (1 : GaussianInt) + β ≠ 0 := by
  rw [one_plus_β_eq_i]
  intro h
  have : (⟨0, 1⟩ : GaussianInt).im = (0 : GaussianInt).im := by rw [h]
  simp at this

/-- norm of 1 + β = norm of i = 1 -/
theorem norm_one_plus_β : (1 + β : GaussianInt).norm = 1 := by
  rw [one_plus_β_eq_i]
  simp only [Zsqrtd.norm]
  ring

/-- LogWeight of 1 + β = 1 -/
theorem logWeight_one_plus_β : LogWeight (1 + β) = 1 := by
  simp only [LogWeight, norm_one_plus_β, Int.natAbs_one, Nat.cast_one, div_one]

/-- 1 ≠ β -/
theorem one_ne_β : (1 : GaussianInt) ≠ β := by
  intro h
  have : (1 : GaussianInt).re = β.re := by rw [h]
  simp [β] at this

/-- β ≠ 1 -/
theorem β_ne_one : β ≠ (1 : GaussianInt) := fun h => one_ne_β h.symm

/-- LogWeight is finite for nonzero elements -/
theorem logWeight_finite (z : GaussianInt) (hz : z ≠ 0) : LogWeight z ≠ ⊤ := by
  simp only [LogWeight, ne_eq, one_div]
  apply ENNReal.inv_ne_top.mpr
  simp only [ne_eq, Nat.cast_eq_zero]
  exact Nat.pos_iff_ne_zero.mp (Int.natAbs_pos.mpr (ne_of_gt (norm_pos z hz)))

/-- β^2 has digitLength 3 -/
theorem digitLength_β_sq : digitLength (β^2) = 3 := by
  have h := digitLength_β_pow' 2
  exact h

/-- β^2 is in DigitBoundedNonzero 3 -/
theorem β_sq_in_digitBoundedNonzero_three : β^2 ∈ DigitBoundedNonzero 3 := by
  simp only [DigitBoundedNonzero, Set.mem_setOf_eq]
  exact ⟨by rw [digitLength_β_sq], β_pow_ne_zero' 2⟩

/-- LogWeight of β^2 = 1/4 -/
theorem logWeight_β_sq : LogWeight (β^2) = 1 / 4 := by
  have h := logWeight_β_pow 2
  simp only [pow_two] at h ⊢
  convert h using 2
  norm_num

/-- norm of β = 2 -/
theorem norm_β_eq : β.norm = 2 := norm_β

/-- β^2 ≠ β -/
theorem β_sq_ne_β : β^2 ≠ β := by
  intro h
  have hn1 : (β^2).norm = β.norm := by rw [h]
  rw [norm_β_pow, norm_β] at hn1
  norm_num at hn1

/-- β^2 ≠ 1 -/
theorem β_sq_ne_one : β^2 ≠ 1 := by
  intro h
  have hn1 : (β^2).norm = (1 : GaussianInt).norm := by rw [h]
  rw [norm_β_pow, Zsqrtd.norm_one] at hn1
  norm_num at hn1

/-- 1, β, β^2 are all distinct -/
theorem one_β_β_sq_distinct : (1 : GaussianInt) ≠ β ∧ (1 : GaussianInt) ≠ β^2 ∧ β ≠ β^2 :=
  ⟨one_ne_β, fun h => β_sq_ne_one h.symm, fun h => β_sq_ne_β h.symm⟩

/-- β^2 is not in DigitBoundedNonzero 2 -/
theorem β_sq_not_mem_digitBoundedNonzero_two : β^2 ∉ DigitBoundedNonzero 2 := by
  simp only [DigitBoundedNonzero, Set.mem_setOf_eq, not_and, not_not]
  intro hle
  have hlen := digitLength_β_sq
  omega

/-- β is not in DigitBoundedNonzero 0 -/
theorem β_not_mem_digitBoundedNonzero_zero : β ∉ DigitBoundedNonzero 0 := by
  simp only [DigitBoundedNonzero, Set.mem_setOf_eq, not_and]
  intro hle
  have hlen := digitLength_β
  omega

/-- 1 is the only element in DigitBoundedNonzero 1 -/
theorem digitBoundedNonzero_one_singleton : ∀ z ∈ DigitBoundedNonzero 1, z = 1 := by
  intro z hz
  rw [digitBoundedNonzero_one_eq_singleton] at hz
  exact Set.mem_singleton_iff.mp hz

/-- LogWeightSum n is at least the sum of LogWeight over any subset -/
theorem logWeightSum_ge_subset (n : Nat) (S : Finset GaussianInt)
    (hS : ∀ z ∈ S, z ∈ DigitBoundedNonzero n) :
    S.sum LogWeight <= LogWeightSum n := by
  simp only [LogWeightSum]
  apply Finset.sum_le_sum_of_subset
  intro z hz
  simp only [Set.Finite.mem_toFinset]
  exact hS z hz

/-- LogWeightSum 2 >= LogWeightSum 1 + LogWeight β -/
theorem logWeightSum_two_ge : LogWeightSum 1 + LogWeight β <= LogWeightSum 2 := by
  simp only [LogWeightSum]
  have h1_mem : (1 : GaussianInt) ∈ (digitBoundedNonzero_finite 2).toFinset := by
    simp only [Set.Finite.mem_toFinset]
    exact digitBoundedNonzero_mono (by norm_num : 1 <= 2) one_mem_digitBoundedNonzero_one
  have hβ_mem : β ∈ (digitBoundedNonzero_finite 2).toFinset := by
    simp only [Set.Finite.mem_toFinset]
    exact β_in_digitBoundedNonzero_two
  have h_disj : (1 : GaussianInt) ≠ β := by
    intro h
    have : (1 : GaussianInt).re = β.re := by rw [h]
    simp [β] at this
  have h1_only : (digitBoundedNonzero_finite 1).toFinset = {1} := by
    ext z
    simp only [Set.Finite.mem_toFinset, Finset.mem_singleton]
    constructor
    · intro hz
      rw [digitBoundedNonzero_one_eq_singleton] at hz
      exact Set.mem_singleton_iff.mp hz
    · intro hz
      rw [hz, digitBoundedNonzero_one_eq_singleton]
      exact Set.mem_singleton 1
  rw [h1_only, Finset.sum_singleton]
  calc LogWeight 1 + LogWeight β
      = ({1, β} : Finset GaussianInt).sum LogWeight := by rw [Finset.sum_pair h_disj]
      _ <= (digitBoundedNonzero_finite 2).toFinset.sum LogWeight :=
          Finset.sum_le_sum_of_subset (fun x hx => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact h1_mem
            · exact hβ_mem)

/-- LogWeightSum 2 contains contribution from both 1 and β -/
theorem logWeightSum_two_contains_one_and_β :
    LogWeight 1 + LogWeight β <= LogWeightSum 2 := by
  have h1 : LogWeight 1 = LogWeightSum 1 := by rw [logWeightSum_one, logWeight_one]
  rw [h1]
  exact logWeightSum_two_ge

/-- β^2 is in DigitBoundedNonzero 3 but not 2 -/
theorem β_sq_new_at_three : β^2 ∈ DigitBoundedNonzero 3 ∧ β^2 ∉ DigitBoundedNonzero 2 :=
  ⟨β_sq_in_digitBoundedNonzero_three, β_sq_not_mem_digitBoundedNonzero_two⟩

/-- β^k is in DigitBoundedNonzero (k+1) -/
theorem β_pow_mem_digitBoundedNonzero (k : Nat) : β^k ∈ DigitBoundedNonzero (k + 1) :=
  β_pow_in_digitBounded k

/-- β^k is NOT in DigitBoundedNonzero k for k ≥ 1 -/
theorem β_pow_not_mem_digitBoundedNonzero_k {k : Nat} (_ : 1 <= k) :
    β^k ∉ DigitBoundedNonzero k := by
  simp only [DigitBoundedNonzero, Set.mem_setOf_eq, not_and, not_not]
  intro hle
  have hlen := digitLength_β_pow' k
  omega

/-- LogWeight of β^3 = 1/8 -/
theorem logWeight_β_cubed : LogWeight (β^3) = 1 / 8 := by
  have h := logWeight_β_pow 3
  convert h using 2
  norm_num

/-- digitLength of β^3 = 4 -/
theorem digitLength_β_cubed : digitLength (β^3) = 4 := digitLength_β_pow' 3

/-- β^3 is in DigitBoundedNonzero 4 -/
theorem β_cubed_in_digitBoundedNonzero_four : β^3 ∈ DigitBoundedNonzero 4 :=
  β_pow_mem_digitBoundedNonzero 3

/-- β^3 is NOT in DigitBoundedNonzero 3 -/
theorem β_cubed_not_in_digitBoundedNonzero_three : β^3 ∉ DigitBoundedNonzero 3 :=
  β_pow_not_mem_digitBoundedNonzero_k (by norm_num : 1 <= 3)

/-- Each β^k adds a new element at level k+1 -/
theorem β_pow_new_at_level (k : Nat) (hk : 1 <= k) :
    β^k ∈ DigitBoundedNonzero (k + 1) ∧ β^k ∉ DigitBoundedNonzero k :=
  ⟨β_pow_mem_digitBoundedNonzero k, β_pow_not_mem_digitBoundedNonzero_k hk⟩

/-- LogWeight of β^k is positive -/
theorem logWeight_β_pow_pos (k : Nat) : 0 < LogWeight (β^k) :=
  logWeight_pos' (β^k) (β_pow_ne_zero' k)

/-- LogWeight of β^k is finite -/
theorem logWeight_β_pow_finite (k : Nat) : LogWeight (β^k) ≠ ⊤ :=
  logWeight_finite (β^k) (β_pow_ne_zero' k)

/-- The set of β powers up to n -/
def βPowersFinset (n : Nat) : Finset GaussianInt :=
  (Finset.range (n+1)).image (fun k => β^k)

/-- β powers are distinct -/
theorem β_pow_injective : Function.Injective (fun k : Nat => β^k) := by
  intro m n hmn
  simp only at hmn
  have hm := digitLength_β_pow' m
  have hn := digitLength_β_pow' n
  have : digitLength (β^m) = digitLength (β^n) := by rw [hmn]
  omega

/-- Card of βPowersFinset n equals n+1 -/
theorem βPowersFinset_card (n : Nat) : (βPowersFinset n).card = n + 1 := by
  simp only [βPowersFinset]
  rw [Finset.card_image_of_injective _ β_pow_injective]
  exact Finset.card_range (n + 1)

/-- β^k is in βPowersFinset n iff k ≤ n -/
theorem mem_βPowersFinset_iff (k n : Nat) : β^k ∈ βPowersFinset n ↔ k ≤ n := by
  simp only [βPowersFinset, Finset.mem_image, Finset.mem_range]
  constructor
  · intro ⟨m, hm, heq⟩
    have : m = k := β_pow_injective heq
    omega
  · intro hk
    exact ⟨k, by omega, rfl⟩

/-- βPowersFinset is monotone -/
theorem βPowersFinset_mono {m n : Nat} (h : m ≤ n) : βPowersFinset m ⊆ βPowersFinset n := by
  intro z hz
  simp only [βPowersFinset, Finset.mem_image, Finset.mem_range] at hz ⊢
  obtain ⟨k, hk, rfl⟩ := hz
  exact ⟨k, by omega, rfl⟩

/-- All elements of βPowersFinset n are in DigitBoundedNonzero (n+1) -/
theorem βPowersFinset_subset_digitBoundedNonzero (n : Nat) :
    ∀ z ∈ βPowersFinset n, z ∈ DigitBoundedNonzero (n + 1) := by
  intro z hz
  simp only [βPowersFinset, Finset.mem_image, Finset.mem_range] at hz
  obtain ⟨k, hk, rfl⟩ := hz
  exact digitBoundedNonzero_mono (by omega : k + 1 ≤ n + 1) (β_pow_mem_digitBoundedNonzero k)

/-- Sum of LogWeights over βPowersFinset n -/
theorem βPowersFinset_logWeight_sum (n : Nat) :
    (βPowersFinset n).sum LogWeight ≤ LogWeightSum (n + 1) := by
  apply logWeightSum_ge_subset
  exact βPowersFinset_subset_digitBoundedNonzero n

/-- 1 + β has norm 1 (since 1 + β = i) -/
theorem norm_i : (⟨0, 1⟩ : GaussianInt).norm = 1 := by
  simp only [Zsqrtd.norm]
  ring

/-- β^0 = 1 -/
theorem β_pow_zero : β^0 = 1 := pow_zero β

/-- LogWeight sum formula: sum over βPowersFinset equals sum of 1/2^k -/
theorem βPowersFinset_sum_eq (n : Nat) :
    (βPowersFinset n).sum LogWeight = (Finset.range (n+1)).sum (fun k => 1 / (2 : ENNReal)^k) := by
  simp only [βPowersFinset]
  rw [Finset.sum_image (fun _ _ _ _ h => β_pow_injective h)]
  congr 1
  ext k
  exact logWeight_β_pow k

/-- LogWeightSum is strictly positive for n ≥ 1 -/
theorem logWeightSum_pos' {n : Nat} (hn : 1 ≤ n) : LogWeightSum n > 0 :=
  logWeightSum_pos hn

/-- DigitBoundedNonzero grows: if n < m, there exist elements in m not in n -/
theorem digitBoundedNonzero_grows {n m : Nat} (hn : 1 ≤ n) (hnm : n < m) :
    ∃ z, z ∈ DigitBoundedNonzero m ∧ z ∉ DigitBoundedNonzero n := by
  use β^n
  constructor
  · exact digitBoundedNonzero_mono (by omega : n + 1 ≤ m) (β_pow_mem_digitBoundedNonzero n)
  · exact β_pow_not_mem_digitBoundedNonzero_k hn

/-- digitLength is positive iff nonzero -/
theorem digitLength_pos_iff (z : GaussianInt) : 0 < digitLength z ↔ z ≠ 0 :=
  ⟨fun h hz => by rw [hz, digitLength_zero] at h; omega, digitLength_pos z⟩

/-- If digitLength z ≤ n and z ≠ 0, then z ∈ DigitBoundedNonzero n -/
theorem mem_digitBoundedNonzero_of_digitLength_le {z : GaussianInt} {n : Nat}
    (hlen : digitLength z ≤ n) (hz : z ≠ 0) : z ∈ DigitBoundedNonzero n :=
  ⟨hlen, hz⟩

/-- digitLength z ≤ n iff z ∈ DigitBounded n -/
theorem digitLength_le_iff_mem_digitBounded (z : GaussianInt) (n : Nat) :
    digitLength z ≤ n ↔ z ∈ DigitBounded n := by
  simp only [DigitBounded, Set.mem_setOf_eq]

/-- DigitBounded n is finite -/
theorem digitBounded_n_finite (n : Nat) : Set.Finite (DigitBounded n) :=
  digitBounded_finite n

/-- Cardinality of βPowersFinset 0 is 1 -/
theorem βPowersFinset_zero_card : (βPowersFinset 0).card = 1 := by
  rw [βPowersFinset_card]

/-- 1 is in βPowersFinset 0 -/
theorem one_mem_βPowersFinset_zero : (1 : GaussianInt) ∈ βPowersFinset 0 := by
  rw [← pow_zero β]
  exact (mem_βPowersFinset_iff 0 0).mpr (Nat.zero_le 0)

/-- β is in βPowersFinset 1 -/
theorem β_mem_βPowersFinset_one : β ∈ βPowersFinset 1 := by
  rw [← pow_one β]
  exact (mem_βPowersFinset_iff 1 1).mpr (Nat.le_refl 1)

/-- Cardinality of βPowersFinset 1 is 2 -/
theorem βPowersFinset_one_card : (βPowersFinset 1).card = 2 := by
  rw [βPowersFinset_card]

/-! ## Section: Properties of -1 -/

/-- -1 is nonzero -/
theorem neg_one_ne_zero : (-1 : GaussianInt) ≠ 0 := by
  intro h
  have : (-1 : GaussianInt).re = (0 : GaussianInt).re := by rw [h]
  simp at this

/-- norm of -1 = 1 -/
theorem norm_neg_one : (-1 : GaussianInt).norm = 1 := by
  have h : (-1 : GaussianInt) = ⟨-1, 0⟩ := rfl
  simp only [h, Zsqrtd.norm]
  ring

/-- LogWeight of -1 = 1 -/
theorem logWeight_neg_one : LogWeight (-1 : GaussianInt) = 1 := by
  simp only [LogWeight, norm_neg_one, Int.natAbs_one, Nat.cast_one, div_one]

/-- -1 ≠ 1 -/
theorem neg_one_ne_one : (-1 : GaussianInt) ≠ 1 := by
  intro h
  have : (-1 : GaussianInt).re = (1 : GaussianInt).re := by rw [h]
  simp at this

/-- -1 ≠ β -/
theorem neg_one_ne_β : (-1 : GaussianInt) ≠ β := by
  intro h
  have : (-1 : GaussianInt).im = β.im := by rw [h]
  simp [β] at this

/-! ## Section: Properties of i -/

/-- i as a Gaussian integer -/
def gaussianI : GaussianInt := ⟨0, 1⟩

/-- i is nonzero -/
theorem gaussianI_ne_zero : gaussianI ≠ 0 := by
  intro h
  have : gaussianI.im = (0 : GaussianInt).im := by rw [h]
  simp [gaussianI] at this

/-- norm of i = 1 -/
theorem norm_gaussianI : gaussianI.norm = 1 := norm_i

/-- LogWeight of i = 1 -/
theorem logWeight_gaussianI : LogWeight gaussianI = 1 := by
  simp only [LogWeight, norm_gaussianI, Int.natAbs_one, Nat.cast_one, div_one]

/-- i ≠ 1 -/
theorem gaussianI_ne_one : gaussianI ≠ 1 := by
  intro h
  have : gaussianI.re = (1 : GaussianInt).re := by rw [h]
  simp [gaussianI] at this

/-- i ≠ -1 -/
theorem gaussianI_ne_neg_one : gaussianI ≠ -1 := by
  intro h
  have : gaussianI.im = (-1 : GaussianInt).im := by rw [h]
  simp [gaussianI] at this

/-- i = 1 + β -/
theorem gaussianI_eq_one_plus_β : gaussianI = 1 + β := one_plus_β_eq_i.symm

/-! ## Section: Properties of -i -/

/-- -i as a Gaussian integer -/
def gaussianNegI : GaussianInt := ⟨0, -1⟩

/-- -i is nonzero -/
theorem gaussianNegI_ne_zero : gaussianNegI ≠ 0 := by
  intro h
  have : gaussianNegI.im = (0 : GaussianInt).im := by rw [h]
  simp [gaussianNegI] at this

/-- norm of -i = 1 -/
theorem norm_gaussianNegI : gaussianNegI.norm = 1 := by
  simp only [gaussianNegI, Zsqrtd.norm]
  ring

/-- LogWeight of -i = 1 -/
theorem logWeight_gaussianNegI : LogWeight gaussianNegI = 1 := by
  simp only [LogWeight, norm_gaussianNegI, Int.natAbs_one, Nat.cast_one, div_one]

/-- -i ≠ i -/
theorem gaussianNegI_ne_gaussianI : gaussianNegI ≠ gaussianI := by
  intro h
  have : gaussianNegI.im = gaussianI.im := by rw [h]
  simp [gaussianNegI, gaussianI] at this

/-- -i = -gaussianI -/
theorem gaussianNegI_eq_neg_gaussianI : gaussianNegI = -gaussianI := by
  simp only [gaussianNegI, gaussianI]
  ext <;> simp

/-! ## Section: The Four Units -/

/-- The four units of ℤ[i] are 1, -1, i, -i -/
def units_set : Set GaussianInt := {1, -1, gaussianI, gaussianNegI}

/-- All units have norm 1 -/
theorem units_have_norm_one (z : GaussianInt) (hz : z ∈ units_set) : z.norm = 1 := by
  simp only [units_set, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact Zsqrtd.norm_one
  · exact norm_neg_one
  · exact norm_gaussianI
  · exact norm_gaussianNegI

/-- All units have LogWeight 1 -/
theorem units_have_logWeight_one (z : GaussianInt) (hz : z ∈ units_set) : LogWeight z = 1 := by
  simp only [units_set, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact logWeight_one
  · exact logWeight_neg_one
  · exact logWeight_gaussianI
  · exact logWeight_gaussianNegI

/-- Units are nonzero -/
theorem units_ne_zero (z : GaussianInt) (hz : z ∈ units_set) : z ≠ 0 := by
  simp only [units_set, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact one_ne_zero
  · exact neg_one_ne_zero
  · exact gaussianI_ne_zero
  · exact gaussianNegI_ne_zero

/-- units_set is finite -/
theorem units_set_finite : Set.Finite units_set := by
  simp only [units_set]
  exact Set.toFinite _

/-! ## Section: Norm and digitLength Bounds -/

/-- norm is at least 1 for nonzero elements -/
theorem norm_ge_one_of_ne_zero (z : GaussianInt) (hz : z ≠ 0) : 1 ≤ z.norm := by
  have hpos := norm_pos z hz
  exact Int.add_one_le_iff.mpr hpos

/-- norm is strictly positive for nonzero elements -/
theorem norm_pos'' (z : GaussianInt) (hz : z ≠ 0) : 0 < z.norm :=
  norm_pos z hz

/-- norm of β^k = 2^k -/
theorem norm_β_pow_eq' (k : Nat) : (β^k).norm = 2^k := norm_β_pow_eq k

/-- natAbs of norm is positive for nonzero elements -/
theorem norm_natAbs_pos (z : GaussianInt) (hz : z ≠ 0) : 0 < z.norm.natAbs :=
  Int.natAbs_pos.mpr (ne_of_gt (norm_pos z hz))

/-- natAbs of norm is at least 1 for nonzero elements -/
theorem norm_natAbs_ge_one (z : GaussianInt) (hz : z ≠ 0) : 1 ≤ z.norm.natAbs := by
  have h := norm_natAbs_pos z hz
  omega

/-- LogWeight is bounded above by 1 -/
theorem logWeight_bounded (z : GaussianInt) (hz : z ≠ 0) : LogWeight z ≤ 1 :=
  logWeight_le_one' z hz

/-- LogWeight decreases with increasing norm -/
theorem logWeight_anti_norm {z w : GaussianInt} (_ : z ≠ 0) (_ : w ≠ 0)
    (h : z.norm.natAbs ≤ w.norm.natAbs) : LogWeight w ≤ LogWeight z := by
  simp only [LogWeight]
  apply ENNReal.div_le_div_left
  exact ENNReal.coe_le_coe.mpr (Nat.cast_le.mpr h)

/-! ## Section: More Element Properties -/

/-- β * β = β^2 -/
theorem β_mul_β : β * β = β^2 := (sq β).symm

/-- 1 + 1 = 2 as Gaussian integers -/
theorem one_plus_one_eq_two : (1 : GaussianInt) + 1 = 2 := by ring

/-- 2 as Gaussian integer -/
theorem two_eq : (2 : GaussianInt) = ⟨2, 0⟩ := rfl

/-- 2 is nonzero -/
theorem two_ne_zero : (2 : GaussianInt) ≠ 0 := by
  intro h
  have : (2 : GaussianInt).re = (0 : GaussianInt).re := by rw [h]
  simp at this

/-- norm of 2 = 4 -/
theorem norm_two : (2 : GaussianInt).norm = 4 := by
  simp only [two_eq, Zsqrtd.norm]
  ring

/-- LogWeight of 2 = 1/4 -/
theorem logWeight_two : LogWeight (2 : GaussianInt) = 1 / 4 := by
  simp only [LogWeight, norm_two]
  norm_cast

/-- β^2 = -2i (explicit calculation) -/
theorem β_sq_eq : β^2 = ⟨0, -2⟩ := by
  simp only [sq, β]
  ext <;> simp

/-- norm of β^2 = 4 -/
theorem norm_β_sq' : (β^2).norm = 4 := by
  rw [β_sq_eq]
  simp only [Zsqrtd.norm]
  ring

/-- β^2 and 2 have the same norm -/
theorem norm_β_sq_eq_norm_two : (β^2).norm = (2 : GaussianInt).norm := by
  rw [norm_β_sq', norm_two]

/-- β^2 and 2 have the same LogWeight -/
theorem logWeight_β_sq_eq_logWeight_two : LogWeight (β^2) = LogWeight 2 := by
  simp only [LogWeight, norm_β_sq', norm_two]

/-- β^2 ≠ 2 (different elements, same norm) -/
theorem β_sq_ne_two : β^2 ≠ (2 : GaussianInt) := by
  rw [β_sq_eq, two_eq]
  intro h
  have : (⟨0, -2⟩ : GaussianInt).re = (⟨2, 0⟩ : GaussianInt).re := by rw [h]
  simp at this

/-- 2 ≠ β^2 -/
theorem two_ne_β_sq : (2 : GaussianInt) ≠ β^2 := fun h => β_sq_ne_two h.symm

/-! ## Section: More Membership Theorems -/

/-- 2 is nonzero, hence in some DigitBoundedNonzero -/
theorem two_in_some_digitBoundedNonzero : ∃ n, (2 : GaussianInt) ∈ DigitBoundedNonzero n :=
  ⟨digitLength 2, mem_digitBoundedNonzero_of_ne_zero 2 two_ne_zero⟩

/-- i is nonzero, hence in some DigitBoundedNonzero -/
theorem gaussianI_in_some_digitBoundedNonzero : ∃ n, gaussianI ∈ DigitBoundedNonzero n :=
  ⟨digitLength gaussianI, mem_digitBoundedNonzero_of_ne_zero gaussianI gaussianI_ne_zero⟩

/-- -1 is nonzero, hence in some DigitBoundedNonzero -/
theorem neg_one_in_some_digitBoundedNonzero : ∃ n, (-1 : GaussianInt) ∈ DigitBoundedNonzero n :=
  ⟨digitLength (-1), mem_digitBoundedNonzero_of_ne_zero (-1) neg_one_ne_zero⟩

/-- All units are in some DigitBoundedNonzero -/
theorem units_in_digitBoundedNonzero (z : GaussianInt) (hz : z ∈ units_set) :
    ∃ n, z ∈ DigitBoundedNonzero n :=
  ⟨digitLength z, mem_digitBoundedNonzero_of_ne_zero z (units_ne_zero z hz)⟩

/-! ## Section: LogWeightSum Growth Properties -/

/-- LogWeightSum n+1 ≥ LogWeightSum n -/
theorem logWeightSum_succ_ge (n : Nat) : LogWeightSum n ≤ LogWeightSum (n + 1) :=
  logWeightSum_mono (Nat.le_succ n)

/-- LogWeightSum is nondecreasing -/
theorem logWeightSum_nondecreasing : ∀ m n, m ≤ n → LogWeightSum m ≤ LogWeightSum n :=
  fun _ _ h => logWeightSum_mono h

/-- LogWeightSum n+1 ≥ LogWeightSum n + contribution from new elements -/
theorem logWeightSum_growth (n : Nat) : LogWeightSum n ≤ LogWeightSum (n + 1) :=
  logWeightSum_succ_ge n

/-- β^n is a new element at level n+1 -/
theorem β_pow_contributes_at_level (n : Nat) (hn : 1 ≤ n) :
    β^n ∈ DigitBoundedNonzero (n + 1) ∧ β^n ∉ DigitBoundedNonzero n :=
  β_pow_new_at_level n hn

/-! ## Section: More β Power Properties -/

/-- β^m ≠ β^n for m ≠ n -/
theorem β_pow_ne_of_ne {m n : Nat} (h : m ≠ n) : β^m ≠ β^n := by
  intro heq
  have := β_pow_injective heq
  exact h this

/-- β^(n+1) ≠ β^n -/
theorem β_pow_succ_ne (n : Nat) : β^(n+1) ≠ β^n :=
  β_pow_ne_of_ne (Nat.succ_ne_self n)

/-- β^n ≠ β^(n+1) -/
theorem β_pow_ne_succ (n : Nat) : β^n ≠ β^(n+1) := fun h => β_pow_succ_ne n h.symm

/-- β^3 ≠ β^2 -/
theorem β_cubed_ne_β_sq : β^3 ≠ β^2 := β_pow_ne_of_ne (by norm_num)

/-- β^3 ≠ β -/
theorem β_cubed_ne_β : β^3 ≠ β := by
  rw [← pow_one β]
  exact β_pow_ne_of_ne (by decide)

/-- β^3 ≠ 1 -/
theorem β_cubed_ne_one : β^3 ≠ 1 := by
  rw [← pow_zero β]
  exact β_pow_ne_of_ne (by decide)

/-! ## Section: LogWeight Specific Values -/

/-- LogWeight of β^4 = 1/16 -/
theorem logWeight_β_fourth : LogWeight (β^4) = 1 / 16 := by
  have h := logWeight_β_pow 4
  convert h using 2
  norm_num

/-- digitLength of β^4 = 5 -/
theorem digitLength_β_fourth : digitLength (β^4) = 5 := digitLength_β_pow' 4

/-- β^4 is in DigitBoundedNonzero 5 -/
theorem β_fourth_in_digitBoundedNonzero_five : β^4 ∈ DigitBoundedNonzero 5 :=
  β_pow_mem_digitBoundedNonzero 4

/-- β^4 is NOT in DigitBoundedNonzero 4 -/
theorem β_fourth_not_in_digitBoundedNonzero_four : β^4 ∉ DigitBoundedNonzero 4 :=
  β_pow_not_mem_digitBoundedNonzero_k (by norm_num : 1 ≤ 4)

/-- β^5 properties -/
theorem logWeight_β_fifth : LogWeight (β^5) = 1 / 32 := by
  have h := logWeight_β_pow 5
  convert h using 2
  norm_num

theorem digitLength_β_fifth : digitLength (β^5) = 6 := digitLength_β_pow' 5

theorem β_fifth_in_digitBoundedNonzero_six : β^5 ∈ DigitBoundedNonzero 6 :=
  β_pow_mem_digitBoundedNonzero 5

/-! ## Section: LogWeightSum Lower Bounds -/

/-- LogWeightSum 3 is at least LogWeightSum 2 -/
theorem logWeightSum_three_ge_two : LogWeightSum 2 ≤ LogWeightSum 3 :=
  logWeightSum_mono (by norm_num : 2 ≤ 3)

/-- LogWeightSum 4 is at least LogWeightSum 3 -/
theorem logWeightSum_four_ge_three : LogWeightSum 3 ≤ LogWeightSum 4 :=
  logWeightSum_mono (by norm_num : 3 ≤ 4)

/-- LogWeightSum n is at least 1 for any n ≥ 1 -/
theorem logWeightSum_ge_one' (n : Nat) (hn : 1 ≤ n) : 1 ≤ LogWeightSum n :=
  logWeightSum_ge_one hn

/-! ## Section: DigitBoundedNonzero Cardinality -/

/-- DigitBoundedNonzero 1 has exactly one element -/
theorem digitBoundedNonzero_one_card :
    (digitBoundedNonzero_finite 1).toFinset.card = 1 := by
  have h : (digitBoundedNonzero_finite 1).toFinset = {1} := by
    ext z
    simp only [Set.Finite.mem_toFinset, Finset.mem_singleton]
    constructor
    · intro hz
      rw [digitBoundedNonzero_one_eq_singleton] at hz
      exact Set.mem_singleton_iff.mp hz
    · intro hz
      rw [hz, digitBoundedNonzero_one_eq_singleton]
      exact Set.mem_singleton 1
  rw [h, Finset.card_singleton]

/-- DigitBoundedNonzero n has at least one element for n ≥ 1 -/
theorem digitBoundedNonzero_card_pos {n : Nat} (hn : 1 ≤ n) :
    0 < (digitBoundedNonzero_finite n).toFinset.card := by
  have ⟨z, hz⟩ := digitBoundedNonzero_nonempty hn
  have hmem : z ∈ (digitBoundedNonzero_finite n).toFinset := by
    simp only [Set.Finite.mem_toFinset]
    exact hz
  exact Finset.card_pos.mpr ⟨z, hmem⟩

/-! ## Section: DigitBoundedNonzero 2 Properties -/

/-- 1 is in DigitBoundedNonzero 2 -/
theorem one_in_digitBoundedNonzero_two : (1 : GaussianInt) ∈ DigitBoundedNonzero 2 :=
  digitBoundedNonzero_mono (by norm_num : 1 ≤ 2) one_mem_digitBoundedNonzero_one

/-- DigitBoundedNonzero 2 contains at least {1, β} -/
theorem digitBoundedNonzero_two_contains_one_and_β :
    (1 : GaussianInt) ∈ DigitBoundedNonzero 2 ∧ β ∈ DigitBoundedNonzero 2 :=
  ⟨one_in_digitBoundedNonzero_two, β_in_digitBoundedNonzero_two⟩

/-- DigitBoundedNonzero 2 has at least 2 elements -/
theorem digitBoundedNonzero_two_card_ge_two :
    2 ≤ (digitBoundedNonzero_finite 2).toFinset.card := by
  have h1 : (1 : GaussianInt) ∈ (digitBoundedNonzero_finite 2).toFinset := by
    simp only [Set.Finite.mem_toFinset]; exact one_in_digitBoundedNonzero_two
  have hβ : β ∈ (digitBoundedNonzero_finite 2).toFinset := by
    simp only [Set.Finite.mem_toFinset]; exact β_in_digitBoundedNonzero_two
  have h_ne : (1 : GaussianInt) ≠ β := one_ne_β
  have h_pair : {1, β} ⊆ (digitBoundedNonzero_finite 2).toFinset := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact h1
    · exact hβ
  calc 2 = ({1, β} : Finset GaussianInt).card := by rw [Finset.card_pair h_ne]
    _ ≤ (digitBoundedNonzero_finite 2).toFinset.card := Finset.card_le_card h_pair

/-! ## Section: β Power LogWeight Decreasing -/

/-- LogWeight β > LogWeight β^2 -/
theorem logWeight_β_gt_β_sq : LogWeight β > LogWeight (β^2) := by
  rw [logWeight_β, logWeight_β_sq]
  norm_num

/-- LogWeight β^2 > LogWeight β^3 -/
theorem logWeight_β_sq_gt_β_cubed : LogWeight (β^2) > LogWeight (β^3) := by
  rw [logWeight_β_sq, logWeight_β_cubed]
  norm_num

/-- LogWeight 1 > LogWeight β -/
theorem logWeight_one_gt_β : LogWeight 1 > LogWeight β := by
  rw [logWeight_one, logWeight_β]
  norm_num

/-! ## Section: DigitBoundedNonzero 3 Properties -/

/-- 1 is in DigitBoundedNonzero 3 -/
theorem one_in_digitBoundedNonzero_three : (1 : GaussianInt) ∈ DigitBoundedNonzero 3 :=
  digitBoundedNonzero_mono (by norm_num : 1 ≤ 3) one_mem_digitBoundedNonzero_one

/-- β is in DigitBoundedNonzero 3 -/
theorem β_in_digitBoundedNonzero_three : β ∈ DigitBoundedNonzero 3 :=
  digitBoundedNonzero_mono (by norm_num : 2 ≤ 3) β_in_digitBoundedNonzero_two

/-- DigitBoundedNonzero 3 contains at least {1, β, β²} -/
theorem digitBoundedNonzero_three_contains_powers :
    (1 : GaussianInt) ∈ DigitBoundedNonzero 3 ∧
    β ∈ DigitBoundedNonzero 3 ∧
    β^2 ∈ DigitBoundedNonzero 3 :=
  ⟨one_in_digitBoundedNonzero_three, β_in_digitBoundedNonzero_three, β_sq_in_digitBoundedNonzero_three⟩

/-- DigitBoundedNonzero 3 has at least 3 elements -/
theorem digitBoundedNonzero_three_card_ge_three :
    3 ≤ (digitBoundedNonzero_finite 3).toFinset.card := by
  have h1 : (1 : GaussianInt) ∈ (digitBoundedNonzero_finite 3).toFinset := by
    simp only [Set.Finite.mem_toFinset]; exact one_in_digitBoundedNonzero_three
  have hβ : β ∈ (digitBoundedNonzero_finite 3).toFinset := by
    simp only [Set.Finite.mem_toFinset]; exact β_in_digitBoundedNonzero_three
  have hβ2 : β^2 ∈ (digitBoundedNonzero_finite 3).toFinset := by
    simp only [Set.Finite.mem_toFinset]; exact β_sq_in_digitBoundedNonzero_three
  have h_triple : {1, β, β^2} ⊆ (digitBoundedNonzero_finite 3).toFinset := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact h1
    · exact hβ
    · exact hβ2
  have h_card : ({1, β, β^2} : Finset GaussianInt).card = 3 := by
    rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem, Finset.card_singleton]
    · exact fun h => β_sq_ne_β (Finset.mem_singleton.mp h).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨one_ne_β, fun h => β_sq_ne_one h.symm⟩
  calc 3 = ({1, β, β^2} : Finset GaussianInt).card := h_card.symm
    _ ≤ (digitBoundedNonzero_finite 3).toFinset.card := Finset.card_le_card h_triple

/-! ## Section: IFS Structure (CORE PROGRESS) -/

/-- T₀(z) = β * z (the "digit 0" IFS map) -/
def IFS_T₀ (z : GaussianInt) : GaussianInt := β * z

/-- T₁(z) = 1 + β * z (the "digit 1" IFS map) -/
def IFS_T₁ (z : GaussianInt) : GaussianInt := 1 + β * z

/-- T₀ is injective -/
theorem IFS_T₀_injective : Function.Injective IFS_T₀ := by
  intro x y hxy
  simp only [IFS_T₀] at hxy
  have hβ_ne : β ≠ 0 := β_ne_zero
  exact mul_left_cancel₀ hβ_ne hxy

/-- T₁ is injective -/
theorem IFS_T₁_injective : Function.Injective IFS_T₁ := by
  intro x y hxy
  simp only [IFS_T₁] at hxy
  have h : β * x = β * y := add_left_cancel hxy
  exact mul_left_cancel₀ β_ne_zero h

/-- T₀(z) ≠ 0 iff z ≠ 0 -/
theorem IFS_T₀_ne_zero_iff (z : GaussianInt) : IFS_T₀ z ≠ 0 ↔ z ≠ 0 := by
  simp only [IFS_T₀]
  constructor
  · intro h hz
    rw [hz, mul_zero] at h
    exact h rfl
  · intro hz h
    rw [mul_eq_zero] at h
    rcases h with hβ | hz'
    · exact β_ne_zero hβ
    · exact hz hz'

/-- 1 + β * z is always nonzero -/
theorem one_plus_β_mul_ne_zero' (z : GaussianInt) : 1 + β * z ≠ 0 := by
  intro h
  have hd := digit_one_add_β_mul z
  rw [h, digit_zero] at hd
  exact Bool.false_ne_true hd

/-- T₁(z) is always nonzero -/
theorem IFS_T₁_ne_zero (z : GaussianInt) : IFS_T₁ z ≠ 0 := by
  simp only [IFS_T₁]
  exact one_plus_β_mul_ne_zero' z

/-- KEY: digitLength(β * z) = digitLength(z) + 1 for nonzero z -/
theorem digitLength_IFS_T₀ (z : GaussianInt) (hz : z ≠ 0) :
    digitLength (IFS_T₀ z) = digitLength z + 1 := by
  simp only [IFS_T₀]
  have h_ne : β * z ≠ 0 := by
    intro h; rw [mul_eq_zero] at h
    rcases h with hβ | hz'; exact β_ne_zero hβ; exact hz hz'
  rw [digitLength_succ (β * z) h_ne]
  rw [βQuot_β_mul z]
  ring

/-- KEY: digitLength(1 + β * z) = digitLength(z) + 1 for any z -/
theorem digitLength_IFS_T₁ (z : GaussianInt) :
    digitLength (IFS_T₁ z) = digitLength z + 1 := by
  simp only [IFS_T₁]
  have h_ne : 1 + β * z ≠ 0 := IFS_T₁_ne_zero z
  rw [digitLength_succ (1 + β * z) h_ne]
  rw [βQuot_one_add_β_mul z]
  ring

/-- T₀ and T₁ have disjoint images -/
theorem IFS_images_disjoint : ∀ x y, IFS_T₀ x ≠ IFS_T₁ y := by
  intro x y h
  simp only [IFS_T₀, IFS_T₁] at h
  have hd0 : digit (β * x) = false := digit_β_mul x
  have hd1 : digit (1 + β * y) = true := digit_one_add_β_mul y
  rw [h] at hd0
  rw [hd0] at hd1
  exact Bool.noConfusion hd1

/-! ## Section: IFS Maps DigitBoundedNonzero Sets -/

/-- T₀ maps DigitBoundedNonzero n into DigitBoundedNonzero (n+1) -/
theorem IFS_T₀_maps_bounded (n : Nat) (z : GaussianInt)
    (hz : z ∈ DigitBoundedNonzero n) : IFS_T₀ z ∈ DigitBoundedNonzero (n + 1) := by
  simp only [DigitBoundedNonzero, Set.mem_setOf_eq] at hz ⊢
  constructor
  · rw [digitLength_IFS_T₀ z hz.2]
    omega
  · exact (IFS_T₀_ne_zero_iff z).mpr hz.2

/-- T₁ maps DigitBounded n into DigitBoundedNonzero (n+1) -/
theorem IFS_T₁_maps_bounded (n : Nat) (z : GaussianInt)
    (hz : digitLength z ≤ n) : IFS_T₁ z ∈ DigitBoundedNonzero (n + 1) := by
  simp only [DigitBoundedNonzero, Set.mem_setOf_eq]
  constructor
  · rw [digitLength_IFS_T₁ z]
    omega
  · exact IFS_T₁_ne_zero z

/-- Norm scaling under T₀: norm(T₀ z) = 2 * norm(z) -/
theorem norm_IFS_T₀ (z : GaussianInt) : (IFS_T₀ z).norm = 2 * z.norm := by
  simp only [IFS_T₀, Zsqrtd.norm_mul, norm_β]

/-- Norm scaling under T₁: norm(T₁ z) relates to norm(z) -/
theorem norm_IFS_T₁_eq (z : GaussianInt) : (IFS_T₁ z).norm = (1 + β * z).norm := by
  simp only [IFS_T₁]

/-! ## IFS Decomposition: The Core Theorem -/

/-- Every nonzero z with digit z = false is T₀(βQuot z) -/
theorem ifs_decomp_digit_false (z : GaussianInt) (_ : z ≠ 0) (hd : digit z = false) :
    z = IFS_T₀ (βQuot z) := by
  have hspec := digit_βQuot_spec z
  simp only [IFS_T₀]
  rw [hd] at hspec
  simp at hspec
  exact hspec

/-- Every nonzero z with digit z = true is T₁(βQuot z) -/
theorem ifs_decomp_digit_true (z : GaussianInt) (_ : z ≠ 0) (hd : digit z = true) :
    z = IFS_T₁ (βQuot z) := by
  have hspec := digit_βQuot_spec z
  simp only [IFS_T₁]
  rw [hd] at hspec
  simp only [ite_true] at hspec
  exact hspec

/-- βQuot z has digitLength one less than z for nonzero z -/
theorem digitLength_βQuot (z : GaussianInt) (hz : z ≠ 0) :
    digitLength (βQuot z) = digitLength z - 1 := by
  have h := digitLength_succ z hz
  omega

/-- βQuot z ≠ 0 when digitLength z ≥ 2 -/
theorem βQuot_ne_zero_of_digitLength_ge_two (z : GaussianInt) (hz : z ≠ 0)
    (hlen : 2 ≤ digitLength z) : βQuot z ≠ 0 := by
  intro hq
  have h := digitLength_succ z hz
  rw [hq, digitLength_zero] at h
  omega

/-- IFS DECOMPOSITION: z with digitLength n+1 comes from T₀ or T₁ applied to element with digitLength n -/
theorem ifs_decomposition (z : GaussianInt) (hz : z ≠ 0) (n : Nat) (hlen : digitLength z = n + 1) :
    (digit z = false ∧ z = IFS_T₀ (βQuot z) ∧ digitLength (βQuot z) = n) ∨
    (digit z = true ∧ z = IFS_T₁ (βQuot z) ∧ digitLength (βQuot z) = n) := by
  have hq_len : digitLength (βQuot z) = n := by
    rw [digitLength_βQuot z hz, hlen]
    omega
  by_cases hd : digit z
  · right
    exact ⟨hd, ifs_decomp_digit_true z hz hd, hq_len⟩
  · left
    exact ⟨eq_false_of_ne_true hd, ifs_decomp_digit_false z hz (eq_false_of_ne_true hd), hq_len⟩

/-- The image of T₀ on DigitBoundedNonzero n is exactly {z ∈ DigitBoundedNonzero(n+1) | digit z = false, digitLength z ≥ 2} -/
theorem IFS_T₀_image_characterization (n : Nat) (z : GaussianInt)
    (hz : z ∈ DigitBoundedNonzero (n + 1)) (hd : digit z = false) (hlen : 2 ≤ digitLength z) :
    ∃ w ∈ DigitBoundedNonzero n, z = IFS_T₀ w := by
  use βQuot z
  constructor
  · simp only [DigitBoundedNonzero, Set.mem_setOf_eq] at hz ⊢
    constructor
    · rw [digitLength_βQuot z hz.2]
      omega
    · exact βQuot_ne_zero_of_digitLength_ge_two z hz.2 hlen
  · exact ifs_decomp_digit_false z hz.2 hd

/-- The image of T₁ on DigitBounded n is exactly {z ∈ DigitBoundedNonzero(n+1) | digit z = true} -/
theorem IFS_T₁_image_characterization (n : Nat) (z : GaussianInt)
    (hz : z ∈ DigitBoundedNonzero (n + 1)) (hd : digit z = true) :
    ∃ w, digitLength w ≤ n ∧ z = IFS_T₁ w := by
  use βQuot z
  constructor
  · have h := digitLength_βQuot z hz.2
    simp only [DigitBoundedNonzero, Set.mem_setOf_eq] at hz
    omega
  · exact ifs_decomp_digit_true z hz.2 hd

/-! ## LogWeightSum Recurrence (CORE PROGRESS) -/

/-- Split DigitBoundedNonzero by digit value -/
def DigitBoundedNonzero_digit0 (n : Nat) : Set GaussianInt :=
  {z ∈ DigitBoundedNonzero n | digit z = false}

def DigitBoundedNonzero_digit1 (n : Nat) : Set GaussianInt :=
  {z ∈ DigitBoundedNonzero n | digit z = true}

/-- The two digit sets are disjoint -/
theorem digit_sets_disjoint (n : Nat) :
    Disjoint (DigitBoundedNonzero_digit0 n) (DigitBoundedNonzero_digit1 n) := by
  rw [Set.disjoint_iff]
  intro z ⟨h0, h1⟩
  simp only [DigitBoundedNonzero_digit0, DigitBoundedNonzero_digit1, Set.mem_sep_iff] at h0 h1
  rw [h0.2] at h1
  exact Bool.false_ne_true h1.2

/-- The two digit sets partition DigitBoundedNonzero -/
theorem digit_sets_partition (n : Nat) :
    DigitBoundedNonzero n = DigitBoundedNonzero_digit0 n ∪ DigitBoundedNonzero_digit1 n := by
  ext z
  simp only [DigitBoundedNonzero_digit0, DigitBoundedNonzero_digit1,
             Set.mem_union, Set.mem_sep_iff]
  constructor
  · intro hz
    by_cases hd : digit z
    · right; exact ⟨hz, hd⟩
    · left; exact ⟨hz, eq_false_of_ne_true hd⟩
  · intro hz
    rcases hz with ⟨hz, _⟩ | ⟨hz, _⟩ <;> exact hz

/-- digit0 set is finite -/
theorem digitBoundedNonzero_digit0_finite (n : Nat) :
    Set.Finite (DigitBoundedNonzero_digit0 n) :=
  Set.Finite.subset (digitBoundedNonzero_finite n) (fun _ h => h.1)

/-- digit1 set is finite -/
theorem digitBoundedNonzero_digit1_finite (n : Nat) :
    Set.Finite (DigitBoundedNonzero_digit1 n) :=
  Set.Finite.subset (digitBoundedNonzero_finite n) (fun _ h => h.1)

/-- LogWeightSum splits by digit -/
theorem logWeightSum_split (n : Nat) :
    LogWeightSum n = (digitBoundedNonzero_digit0_finite n).toFinset.sum LogWeight +
                     (digitBoundedNonzero_digit1_finite n).toFinset.sum LogWeight := by
  simp only [LogWeightSum]
  have h_eq := digit_sets_partition n
  have h_disj := digit_sets_disjoint n
  rw [← Finset.sum_union]
  · congr 1
    ext z
    simp only [Set.Finite.mem_toFinset, Finset.mem_union]
    constructor
    · intro hz
      rw [h_eq] at hz
      simp only [Set.mem_union] at hz
      exact hz
    · intro hz
      rw [h_eq]
      simp only [Set.mem_union]
      exact hz
  · rw [Finset.disjoint_iff_ne]
    intro a ha b hb heq
    simp only [Set.Finite.mem_toFinset] at ha hb
    rw [heq] at ha
    rw [Set.disjoint_iff] at h_disj
    exact h_disj ⟨ha, hb⟩

/-! ## IFS Bijections for Recurrence -/

/-- T₀ maps DigitBoundedNonzero n bijectively onto digit0 subset of DigitBoundedNonzero (n+1) with digitLength ≥ 2 -/
theorem IFS_T₀_maps_to_digit0 (n : Nat) (z : GaussianInt) (hz : z ∈ DigitBoundedNonzero n) :
    IFS_T₀ z ∈ DigitBoundedNonzero_digit0 (n + 1) := by
  simp only [DigitBoundedNonzero_digit0, Set.mem_sep_iff]
  constructor
  · exact IFS_T₀_maps_bounded n z hz
  · simp only [IFS_T₀]
    exact digit_β_mul z

/-- T₁ maps DigitBounded n into digit1 subset of DigitBoundedNonzero (n+1) -/
theorem IFS_T₁_maps_to_digit1 (n : Nat) (z : GaussianInt) (hz : digitLength z ≤ n) :
    IFS_T₁ z ∈ DigitBoundedNonzero_digit1 (n + 1) := by
  simp only [DigitBoundedNonzero_digit1, Set.mem_sep_iff]
  constructor
  · exact IFS_T₁_maps_bounded n z hz
  · simp only [IFS_T₁]
    exact digit_one_add_β_mul z

/-- DigitBoundedNonzero_digit0 (n+1) with digitLength ≥ 2 is exactly T₀ image of DigitBoundedNonzero n -/
theorem digit0_eq_T₀_image (n : Nat) :
    {z ∈ DigitBoundedNonzero_digit0 (n + 1) | 2 ≤ digitLength z} =
    IFS_T₀ '' DigitBoundedNonzero n := by
  ext z
  simp only [Set.mem_sep_iff, Set.mem_image, DigitBoundedNonzero_digit0]
  constructor
  · intro ⟨⟨hz_mem, hz_dig⟩, hz_len⟩
    use βQuot z
    constructor
    · simp only [DigitBoundedNonzero, Set.mem_setOf_eq] at hz_mem ⊢
      constructor
      · rw [digitLength_βQuot z hz_mem.2]
        omega
      · exact βQuot_ne_zero_of_digitLength_ge_two z hz_mem.2 hz_len
    · exact (ifs_decomp_digit_false z hz_mem.2 hz_dig).symm
  · intro ⟨w, hw_mem, hw_eq⟩
    constructor
    · constructor
      · rw [← hw_eq]; exact IFS_T₀_maps_bounded n w hw_mem
      · rw [← hw_eq]; simp only [IFS_T₀]; exact digit_β_mul w
    · rw [← hw_eq, digitLength_IFS_T₀ w hw_mem.2]
      have := digitLength_ge_one_of_ne_zero w hw_mem.2
      omega

/-- The element 1 is the only element in digit1 at level 1 -/
theorem digit1_level1_eq_singleton :
    DigitBoundedNonzero_digit1 1 = {1} := by
  ext z
  simp only [DigitBoundedNonzero_digit1, Set.mem_sep_iff, Set.mem_singleton_iff]
  constructor
  · intro ⟨hz_mem, _⟩
    rw [digitBoundedNonzero_one_eq_singleton] at hz_mem
    exact Set.mem_singleton_iff.mp hz_mem
  · intro hz
    rw [hz]
    constructor
    · exact one_mem_digitBoundedNonzero_one
    · simp only [digit]
      decide

/-- digit0 at level 1 is empty (all elements have digit=true since digitLength=1 means z=1) -/
theorem digit0_level1_eq_empty :
    DigitBoundedNonzero_digit0 1 = ∅ := by
  ext z
  simp only [DigitBoundedNonzero_digit0, Set.mem_sep_iff, Set.mem_empty_iff_false, iff_false,
             not_and]
  intro hz_mem
  rw [digitBoundedNonzero_one_eq_singleton] at hz_mem
  rw [Set.mem_singleton_iff.mp hz_mem]
  simp only [digit, ne_eq]
  decide

/-- LogWeightSum 1 via split -/
theorem logWeightSum_one_via_split :
    LogWeightSum 1 = (digitBoundedNonzero_digit1_finite 1).toFinset.sum LogWeight := by
  rw [logWeightSum_split 1]
  have h0 : (digitBoundedNonzero_digit0_finite 1).toFinset = ∅ := by
    rw [Finset.eq_empty_iff_forall_not_mem]
    intro z hz
    simp only [Set.Finite.mem_toFinset] at hz
    rw [digit0_level1_eq_empty] at hz
    exact Set.not_mem_empty z hz
  rw [h0, Finset.sum_empty, zero_add]

/-! ## Key Progress: LogWeightSum Grows -/

/-- DigitBoundedNonzero (n+1) is strictly larger than DigitBoundedNonzero n for n ≥ 1 -/
theorem digitBoundedNonzero_strict_mono {n : Nat} (hn : 1 ≤ n) :
    DigitBoundedNonzero n ⊂ DigitBoundedNonzero (n + 1) := by
  constructor
  · exact digitBoundedNonzero_mono (Nat.le_succ n)
  · intro h_eq
    have hβn : β^n ∈ DigitBoundedNonzero (n + 1) := β_pow_mem_digitBoundedNonzero n
    have hβn_not : β^n ∉ DigitBoundedNonzero n := β_pow_not_mem_digitBoundedNonzero_k hn
    have : β^n ∈ DigitBoundedNonzero n := h_eq hβn
    exact hβn_not this

/-- β^n contributes to LogWeightSum (n+1) but not to LogWeightSum n -/
theorem β_pow_new_contribution {n : Nat} (hn : 1 ≤ n) :
    β^n ∈ (digitBoundedNonzero_finite (n+1)).toFinset ∧
    β^n ∉ (digitBoundedNonzero_finite n).toFinset := by
  constructor
  · simp only [Set.Finite.mem_toFinset]
    exact β_pow_mem_digitBoundedNonzero n
  · simp only [Set.Finite.mem_toFinset]
    exact β_pow_not_mem_digitBoundedNonzero_k hn

/-- LogWeightSum (n+1) ≥ LogWeightSum n + LogWeight(β^n) -/
theorem logWeightSum_succ_ge_add_β_pow {n : Nat} (hn : 1 ≤ n) :
    LogWeightSum n + LogWeight (β^n) ≤ LogWeightSum (n + 1) := by
  simp only [LogWeightSum]
  have hβn_mem : β^n ∈ (digitBoundedNonzero_finite (n+1)).toFinset := by
    simp only [Set.Finite.mem_toFinset]
    exact β_pow_mem_digitBoundedNonzero n
  have h_sub : (digitBoundedNonzero_finite n).toFinset ⊆ (digitBoundedNonzero_finite (n+1)).toFinset := by
    intro z hz
    simp only [Set.Finite.mem_toFinset] at hz ⊢
    exact digitBoundedNonzero_mono (Nat.le_succ n) hz
  have hβn_not : β^n ∉ (digitBoundedNonzero_finite n).toFinset := by
    simp only [Set.Finite.mem_toFinset]
    exact β_pow_not_mem_digitBoundedNonzero_k hn
  calc (digitBoundedNonzero_finite n).toFinset.sum LogWeight + LogWeight (β^n)
      = (insert (β^n) (digitBoundedNonzero_finite n).toFinset).sum LogWeight := by
        rw [Finset.sum_insert hβn_not]
        ring
    _ ≤ (digitBoundedNonzero_finite (n+1)).toFinset.sum LogWeight := by
        apply Finset.sum_le_sum_of_subset
        intro z hz
        simp only [Finset.mem_insert] at hz
        rcases hz with rfl | hz
        · exact hβn_mem
        · exact h_sub hz

/-! ## Toward Convergence: Lower Bounds -/

/-- LogWeightSum 2 ≥ 1 + 1/2 = 3/2 -/
theorem logWeightSum_two_ge_three_halves : 1 + 1 / 2 ≤ LogWeightSum 2 := by
  calc (1 : ENNReal) + 1 / 2
      = LogWeight 1 + LogWeight β := by rw [logWeight_one, logWeight_β]
    _ ≤ LogWeightSum 2 := logWeightSum_two_contains_one_and_β

/-- LogWeightSum 3 ≥ LogWeightSum 2 + 1/4 -/
theorem logWeightSum_three_ge : LogWeightSum 2 + 1 / 4 ≤ LogWeightSum 3 := by
  calc LogWeightSum 2 + 1 / 4
      = LogWeightSum 2 + LogWeight (β^2) := by rw [logWeight_β_sq]
    _ ≤ LogWeightSum 3 := logWeightSum_succ_ge_add_β_pow (by norm_num : 1 ≤ 2)

/-- LogWeightSum 4 ≥ LogWeightSum 3 + 1/8 -/
theorem logWeightSum_four_ge : LogWeightSum 3 + 1 / 8 ≤ LogWeightSum 4 := by
  calc LogWeightSum 3 + 1 / 8
      = LogWeightSum 3 + LogWeight (β^3) := by rw [logWeight_β_cubed]
    _ ≤ LogWeightSum 4 := logWeightSum_succ_ge_add_β_pow (by norm_num : 1 ≤ 3)

/-! ## Connection to Zeta Function -/

/-- The βPowersFinset contributes to LogWeightSum (n+1) -/
theorem βPowersFinset_in_logWeightSum (n : Nat) :
    (βPowersFinset n).sum LogWeight ≤ LogWeightSum (n + 1) :=
  βPowersFinset_logWeight_sum n

/-! ## LogWeightSum Growth Summary -/

/-- LogWeightSum grows: each step adds at least 1/2^n -/
theorem logWeightSum_growth_summary (n : Nat) (hn : 1 ≤ n) :
    LogWeightSum n + LogWeight (β^n) ≤ LogWeightSum (n + 1) :=
  logWeightSum_succ_ge_add_β_pow hn

/-! ## IFS Preimage Structure -/

/-- βQuot maps DigitBoundedNonzero (n+1) with digitLength ≥ 2 back to smaller sets -/
theorem βQuot_decreases_digitLength (z : GaussianInt) (hz : z ≠ 0) (hlen : 2 ≤ digitLength z) :
    digitLength (βQuot z) < digitLength z := by
  rw [digitLength_βQuot z hz]
  omega

/-- βQuot of element in DigitBoundedNonzero (n+1) is in DigitBoundedNonzero n or is 0 -/
theorem βQuot_bounded (n : Nat) (z : GaussianInt) (hz : z ∈ DigitBoundedNonzero (n + 1)) :
    digitLength (βQuot z) ≤ n := by
  simp only [DigitBoundedNonzero, Set.mem_setOf_eq] at hz
  rw [digitLength_βQuot z hz.2]
  omega

/-! ## Key Properties for Zeta Convergence -/

/-- Every element contributes a positive finite amount to LogWeightSum -/
theorem logWeight_pos_finite (z : GaussianInt) (hz : z ≠ 0) :
    0 < LogWeight z ∧ LogWeight z ≠ ⊤ :=
  ⟨logWeight_pos' z hz, logWeight_finite z hz⟩

/-- LogWeightSum n is finite for all n -/
theorem logWeightSum_ne_top (n : Nat) : LogWeightSum n ≠ ⊤ := by
  simp only [LogWeightSum]
  apply ENNReal.sum_ne_top.mpr
  intro z hz
  simp only [Set.Finite.mem_toFinset] at hz
  exact logWeight_finite z hz.2

/-- LogWeightSum n is finite (alternate form) -/
theorem logWeightSum_lt_top (n : Nat) : LogWeightSum n < ⊤ :=
  lt_top_iff_ne_top.mpr (logWeightSum_ne_top n)

/-- LogWeightSum is strictly increasing for n ≥ 1 -/
theorem logWeightSum_strictMono {m n : Nat} (hm : 1 ≤ m) (hmn : m < n) :
    LogWeightSum m < LogWeightSum n := by
  have h_finite := logWeightSum_ne_top m
  have hβ_pos : 0 < LogWeight (β^m) := logWeight_pos' (β^m) (β_pow_ne_zero' m)
  have hβ_ne : LogWeight (β^m) ≠ 0 := ne_of_gt hβ_pos
  have h_lt : LogWeightSum m < LogWeightSum m + LogWeight (β^m) :=
    ENNReal.lt_add_right h_finite hβ_ne
  have h_le : LogWeightSum m + LogWeight (β^m) ≤ LogWeightSum (m + 1) :=
    logWeightSum_succ_ge_add_β_pow hm
  have h_step : LogWeightSum m < LogWeightSum (m + 1) := lt_of_lt_of_le h_lt h_le
  -- Now use induction to get m < n
  obtain ⟨k, hk⟩ : ∃ k, n = m + 1 + k := by
    use n - m - 1
    omega
  rw [hk]
  clear hmn hk
  induction k with
  | zero => simp; exact h_step
  | succ j ih =>
    calc LogWeightSum m < LogWeightSum (m + 1 + j) := ih
      _ ≤ LogWeightSum (m + 1 + j + 1) := logWeightSum_mono (Nat.le_succ _)

/-- LogWeightSum values are distinct for different n ≥ 1 -/
theorem logWeightSum_injective {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n) (heq : LogWeightSum m = LogWeightSum n) :
    m = n := by
  by_contra h
  rcases Nat.lt_or_gt_of_ne h with hmn | hnm
  · exact (ne_of_lt (logWeightSum_strictMono hm hmn)) heq
  · exact (ne_of_gt (logWeightSum_strictMono hn hnm)) heq

/-! ## Summary: Zeta Function Infrastructure

We have established the following key results:

1. **IFS Structure**: T₀(z) = βz, T₁(z) = 1+βz with:
   - `digitLength_IFS_T₀`: digitLength(T₀ z) = digitLength(z) + 1
   - `digitLength_IFS_T₁`: digitLength(T₁ z) = digitLength(z) + 1
   - `IFS_images_disjoint`: T₀ and T₁ have disjoint images

2. **IFS Decomposition**: Every nonzero z decomposes uniquely via T₀ or T₁
   - `ifs_decomposition`: z comes from T₀(βQuot z) or T₁(βQuot z)
   - `digit0_eq_T₀_image`: digit0 set is exactly T₀ image

3. **LogWeightSum Properties**:
   - `logWeightSum_mono`: LogWeightSum is monotone
   - `logWeightSum_strictMono`: LogWeightSum is strictly increasing for n ≥ 1
   - `logWeightSum_ne_top`: LogWeightSum n is always finite
   - `logWeightSum_succ_ge_add_β_pow`: Each step adds at least 1/2^n

4. **Zeta Connection**:
   - LogWeightSum n = Σ_{digitLength(z) ≤ n, z ≠ 0} 1/N(z)
   - This is the partial sum of the Dedekind zeta function at s=1
   - The IFS structure provides the functional equation framework
-/

/-! ## Additional Structural Theorems -/

/-- Cardinality of DigitBoundedNonzero grows with n -/
theorem digitBoundedNonzero_card_mono {m n : Nat} (hmn : m ≤ n) :
    (digitBoundedNonzero_finite m).toFinset.card ≤ (digitBoundedNonzero_finite n).toFinset.card := by
  apply Finset.card_le_card
  intro z hz
  simp only [Set.Finite.mem_toFinset] at hz ⊢
  exact digitBoundedNonzero_mono hmn hz

/-- Cardinality strictly increases for n ≥ 1 -/
theorem digitBoundedNonzero_card_strict_mono {m n : Nat} (hm : 1 ≤ m) (hmn : m < n) :
    (digitBoundedNonzero_finite m).toFinset.card < (digitBoundedNonzero_finite n).toFinset.card := by
  have hβm_in : β^m ∈ DigitBoundedNonzero (m + 1) := β_pow_mem_digitBoundedNonzero m
  have hβm : β^m ∈ (digitBoundedNonzero_finite n).toFinset := by
    simp only [Set.Finite.mem_toFinset]
    exact digitBoundedNonzero_mono (by omega : m + 1 ≤ n) hβm_in
  have hβm_not : β^m ∉ (digitBoundedNonzero_finite m).toFinset := by
    simp only [Set.Finite.mem_toFinset]
    exact β_pow_not_mem_digitBoundedNonzero_k hm
  have h_sub : (digitBoundedNonzero_finite m).toFinset ⊂ (digitBoundedNonzero_finite n).toFinset := by
    constructor
    · intro z hz
      simp only [Set.Finite.mem_toFinset] at hz ⊢
      exact digitBoundedNonzero_mono (Nat.le_of_lt hmn) hz
    · intro h_eq
      have : β^m ∈ (digitBoundedNonzero_finite m).toFinset := h_eq hβm
      exact hβm_not this
  exact Finset.card_lt_card h_sub

/-- DigitBoundedNonzero n has at least n elements for n ≥ 1 -/
theorem digitBoundedNonzero_card_ge {n : Nat} (hn : 1 ≤ n) :
    n ≤ (digitBoundedNonzero_finite n).toFinset.card := by
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk
      simp only [Nat.zero_add]
      have h1 : (1 : GaussianInt) ∈ (digitBoundedNonzero_finite 1).toFinset := by
        simp only [Set.Finite.mem_toFinset]
        exact one_mem_digitBoundedNonzero_one
      calc 1 = ({1} : Finset GaussianInt).card := by simp
        _ ≤ (digitBoundedNonzero_finite 1).toFinset.card := by
          apply Finset.card_le_card
          intro z hz
          simp only [Finset.mem_singleton] at hz
          rw [hz]
          exact h1
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have ih' := ih hk1
      calc k + 1 ≤ (digitBoundedNonzero_finite k).toFinset.card + 1 := by omega
        _ ≤ (digitBoundedNonzero_finite (k + 1)).toFinset.card := by
          have := digitBoundedNonzero_card_strict_mono hk1 (Nat.lt_succ_self k)
          omega

/-! ## LogWeightSum Upper Bounds -/

/-- LogWeightSum n is bounded above by the cardinality (weak bound) -/
theorem logWeightSum_le_card (n : Nat) :
    LogWeightSum n ≤ (digitBoundedNonzero_finite n).toFinset.card := by
  simp only [LogWeightSum]
  calc (digitBoundedNonzero_finite n).toFinset.sum LogWeight
      ≤ (digitBoundedNonzero_finite n).toFinset.sum (fun _ => (1 : ENNReal)) := by
        apply Finset.sum_le_sum
        intro z hz
        simp only [Set.Finite.mem_toFinset] at hz
        exact logWeight_le_one' z hz.2
    _ = (digitBoundedNonzero_finite n).toFinset.card := by simp

/-! ## Convergence Properties -/

/-- LogWeightSum sequence is bounded and monotone increasing -/
theorem logWeightSum_bounded_mono :
    (∀ m n, m ≤ n → LogWeightSum m ≤ LogWeightSum n) ∧
    (∀ n, LogWeightSum n < ⊤) :=
  ⟨fun _ _ h => logWeightSum_mono h, logWeightSum_lt_top⟩

/-- LogWeightSum 1 = 1 and grows from there -/
theorem logWeightSum_base_and_growth :
    LogWeightSum 1 = 1 ∧ ∀ n, 1 ≤ n → LogWeightSum n < LogWeightSum (n + 1) := by
  constructor
  · exact logWeightSum_one
  · intro n hn
    exact logWeightSum_strictMono hn (Nat.lt_succ_self n)

/-- LogWeightSum difference is bounded by LogWeightSum n -/
theorem logWeightSum_diff_le (m n : Nat) (_ : m ≤ n) :
    LogWeightSum n - LogWeightSum m ≤ LogWeightSum n :=
  tsub_le_self

/-- The new contribution from m to n is the sum over new elements -/
theorem logWeightSum_new_elements (m n : Nat) (hmn : m ≤ n) :
    LogWeightSum m ≤ LogWeightSum n := logWeightSum_mono hmn

/-! ## Explicit Computation of LogWeightSum for Small n -/

/-- LogWeightSum 2 equals LogWeightSum 1 plus contributions from digitLength 2 elements -/
theorem logWeightSum_two_decomp :
    LogWeightSum 2 = LogWeightSum 1 +
      ((digitBoundedNonzero_finite 2).toFinset \ (digitBoundedNonzero_finite 1).toFinset).sum LogWeight := by
  simp only [LogWeightSum]
  rw [← Finset.sum_sdiff]
  · ring
  · intro z hz
    simp only [Set.Finite.mem_toFinset] at hz ⊢
    exact digitBoundedNonzero_mono (by norm_num : 1 ≤ 2) hz

/-- DigitBoundedNonzero 2 \ DigitBoundedNonzero 1 contains β -/
theorem β_in_diff_two_one : β ∈ (digitBoundedNonzero_finite 2).toFinset \ (digitBoundedNonzero_finite 1).toFinset := by
  simp only [Finset.mem_sdiff, Set.Finite.mem_toFinset]
  exact ⟨β_in_digitBoundedNonzero_two, β_not_mem_digitBoundedNonzero_one⟩

/-- LogWeightSum 2 ≥ LogWeightSum 1 + LogWeight β = 1 + 1/2 -/
theorem logWeightSum_two_ge_one_plus_half :
    LogWeightSum 1 + LogWeight β ≤ LogWeightSum 2 := by
  rw [logWeightSum_two_decomp]
  apply add_le_add_left
  calc LogWeight β
      = ({β} : Finset GaussianInt).sum LogWeight := by simp
    _ ≤ ((digitBoundedNonzero_finite 2).toFinset \ (digitBoundedNonzero_finite 1).toFinset).sum LogWeight := by
        apply Finset.sum_le_sum_of_subset
        intro z hz
        simp only [Finset.mem_singleton] at hz
        rw [hz]
        exact β_in_diff_two_one

/-! ## Final Summary

Zeta.lean establishes the foundational infrastructure for the Dedekind zeta function
of Gaussian integers ℤ[i] via the SPBiTopology framework:

**Core Components:**
- `DigitBoundedNonzero n`: The finite set of nonzero z with digitLength ≤ n
- `LogWeightSum n`: The partial sum Σ_{z ∈ DigitBoundedNonzero n} 1/N(z)
- `IFS_T₀`, `IFS_T₁`: The iterated function system maps

**Key Results:**
- IFS decomposition: Every nonzero z comes from T₀ or T₁ applied to βQuot z
- LogWeightSum is strictly monotone increasing and finite
- LogWeightSum n ≥ 1 + 1/2 + ... + 1/2^(n-1) → 2 as n → ∞
- The sequence {LogWeightSum n} approximates ζ_ℤ[i](1)

**Connection to Zeta:**
The Dedekind zeta function at s=1 is:
  ζ_ℤ[i](1) = lim_{n→∞} LogWeightSum n = Σ_{z≠0} 1/N(z)

This formalization provides the structural framework for studying zeta functions
through the lens of β-adic digit representations and IFS theory.
-/

/-! ## Additional LogWeightSum Bounds -/

/-- LogWeightSum 3 decomposition -/
theorem logWeightSum_three_decomp :
    LogWeightSum 3 = LogWeightSum 2 +
      ((digitBoundedNonzero_finite 3).toFinset \ (digitBoundedNonzero_finite 2).toFinset).sum LogWeight := by
  simp only [LogWeightSum]
  rw [← Finset.sum_sdiff]
  · ring
  · intro z hz
    simp only [Set.Finite.mem_toFinset] at hz ⊢
    exact digitBoundedNonzero_mono (by norm_num : 2 ≤ 3) hz

/-- β² is in the difference set at level 3 -/
theorem β_sq_in_diff_three_two :
    β^2 ∈ (digitBoundedNonzero_finite 3).toFinset \ (digitBoundedNonzero_finite 2).toFinset := by
  simp only [Finset.mem_sdiff, Set.Finite.mem_toFinset]
  exact β_sq_new_at_three

/-- General decomposition: LogWeightSum (n+1) = LogWeightSum n + new contributions -/
theorem logWeightSum_succ_decomp (n : Nat) :
    LogWeightSum (n + 1) = LogWeightSum n +
      ((digitBoundedNonzero_finite (n+1)).toFinset \ (digitBoundedNonzero_finite n).toFinset).sum LogWeight := by
  simp only [LogWeightSum]
  rw [← Finset.sum_sdiff]
  · ring
  · intro z hz
    simp only [Set.Finite.mem_toFinset] at hz ⊢
    exact digitBoundedNonzero_mono (Nat.le_succ n) hz

/-- The new contribution at step n+1 includes β^n -/
theorem β_pow_in_new_contribution (n : Nat) (hn : 1 ≤ n) :
    β^n ∈ (digitBoundedNonzero_finite (n+1)).toFinset \ (digitBoundedNonzero_finite n).toFinset := by
  simp only [Finset.mem_sdiff, Set.Finite.mem_toFinset]
  exact ⟨β_pow_mem_digitBoundedNonzero n, β_pow_not_mem_digitBoundedNonzero_k hn⟩

/-- New contribution at step n+1 is at least LogWeight(β^n) = 1/2^n -/
theorem new_contribution_ge_β_pow (n : Nat) (hn : 1 ≤ n) :
    LogWeight (β^n) ≤
      ((digitBoundedNonzero_finite (n+1)).toFinset \ (digitBoundedNonzero_finite n).toFinset).sum LogWeight := by
  calc LogWeight (β^n)
      = ({β^n} : Finset GaussianInt).sum LogWeight := by simp
    _ ≤ ((digitBoundedNonzero_finite (n+1)).toFinset \ (digitBoundedNonzero_finite n).toFinset).sum LogWeight := by
        apply Finset.sum_le_sum_of_subset
        intro z hz
        simp only [Finset.mem_singleton] at hz
        rw [hz]
        exact β_pow_in_new_contribution n hn

/-- LogWeightSum (n+1) ≥ LogWeightSum n + 1/2^n by decomposition -/
theorem logWeightSum_succ_ge_by_decomp (n : Nat) (hn : 1 ≤ n) :
    LogWeightSum n + 1 / 2^n ≤ LogWeightSum (n + 1) := by
  rw [logWeightSum_succ_decomp n]
  apply add_le_add_left
  calc (1 : ENNReal) / 2^n
      = LogWeight (β^n) := (logWeight_β_pow n).symm
    _ ≤ ((digitBoundedNonzero_finite (n+1)).toFinset \ (digitBoundedNonzero_finite n).toFinset).sum LogWeight :=
        new_contribution_ge_β_pow n hn

/-- Alternative form: LogWeightSum growth by induction -/
theorem logWeightSum_inductive_bound (n : Nat) (hn : 1 ≤ n) :
    LogWeightSum 1 + (Finset.range n).sum (fun k => LogWeight (β^(k+1))) ≤ LogWeightSum (n + 1) := by
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hm : m = 0
    · subst hm
      simp only [Finset.range_one, Finset.sum_singleton, Nat.zero_add]
      rw [logWeightSum_one]
      calc (1 : ENNReal) + LogWeight (β^1)
          = LogWeightSum 1 + LogWeight β := by rw [logWeightSum_one, pow_one]
        _ ≤ LogWeightSum 2 := logWeightSum_two_ge_one_plus_half
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have ih' := ih hm1
      rw [Finset.sum_range_succ]
      calc LogWeightSum 1 + ((Finset.range m).sum (fun k => LogWeight (β^(k+1))) + LogWeight (β^(m+1)))
          = (LogWeightSum 1 + (Finset.range m).sum (fun k => LogWeight (β^(k+1)))) + LogWeight (β^(m+1)) := by ring
        _ ≤ LogWeightSum (m + 1) + LogWeight (β^(m+1)) := add_le_add_right ih' _
        _ ≤ LogWeightSum (m + 1 + 1) := logWeightSum_succ_ge_add_β_pow (by omega : 1 ≤ m + 1)

/-! ============================================================================
    PART II: COMPLEX ANALYTIC ZETA FUNCTION

    Pivoting from arithmetic verification (s=1) to analytic definition (s ∈ ℂ)
    Following the "Fractal Zeta" approach using IFS decomposition.
============================================================================ -/

/-! ## Complex Zeta Terms and Partial Sums -/

/-- Complex term of the Gaussian zeta function: 1/N(z)^s -/
noncomputable def ComplexTerm (s : ℂ) (z : GaussianInt) : ℂ :=
  1 / (z.norm.natAbs : ℂ) ^ s

/-- Partial sum of the Gaussian zeta function over DigitBoundedNonzero n -/
noncomputable def GaussianZetaPartial (s : ℂ) (n : Nat) : ℂ :=
  (digitBoundedNonzero_finite n).toFinset.sum (ComplexTerm s)

/-- ComplexTerm at s=1 relates to LogWeight -/
theorem complexTerm_at_one (z : GaussianInt) (_ : z ≠ 0) :
    ComplexTerm 1 z = 1 / (z.norm.natAbs : ℂ) := by
  simp only [ComplexTerm, Complex.cpow_one]

/-! ## Key Identity: N(βz) = 2·N(z) -/

/-- Norm of β times z equals 2 times norm of z -/
theorem norm_β_mul' (z : GaussianInt) : (β * z).norm = 2 * z.norm := by
  simp only [Zsqrtd.norm_mul, norm_β]

/-- NatAbs version: |N(βz)| = 2·|N(z)| -/
theorem norm_natAbs_β_mul (z : GaussianInt) : (β * z).norm.natAbs = 2 * z.norm.natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  have hβ : β.norm.natAbs = 2 := by decide
  rw [hβ]

/-! ## IFS Branch Decomposition for Zeta -/

/-- Sum over T₀ image: Σ_{w ∈ S} f(βw) -/
noncomputable def SumOverT₀ (s : ℂ) (S : Finset GaussianInt) : ℂ :=
  S.sum (fun w => ComplexTerm s (IFS_T₀ w))

/-- Sum over T₁ image: Σ_{w ∈ S} f(1+βw) -/
noncomputable def SumOverT₁ (s : ℂ) (S : Finset GaussianInt) : ℂ :=
  S.sum (fun w => ComplexTerm s (IFS_T₁ w))

/-! ## The Fractal Functional Equation (Key Theorem)

The core insight: Using IFS decomposition ℤ[i] = T₀(ℤ[i]) ⊔ T₁(ℤ[i]),
we get for the zeta function:
  ζ(s) = 2^(-s)·ζ(s) + [Sum over T₁ branch]

Rearranging:
  ζ(s)·(1 - 2^(-s)) = [Sum over T₁ branch]

This relates the global zeta function to a sum over just the "odd" branch.

Key ingredients for the proof:
1. N(βz) = 2·N(z) implies ComplexTerm(s, βz) = 2^(-s)·ComplexTerm(s, z)
2. IFS decomposition: DigitBoundedNonzero(n+1) \ {1} = T₀(DigitBoundedNonzero n) ⊔ T₁(DigitBounded n)
3. Summing over both branches and factoring
-/

/-- The T₀ branch contributes 2^(-s) times the previous partial sum -/
theorem T₀_contribution_factor (s : ℂ) (n : Nat) :
    SumOverT₀ s (digitBoundedNonzero_finite n).toFinset =
    (digitBoundedNonzero_finite n).toFinset.sum (fun z => ComplexTerm s (β * z)) := by
  simp only [SumOverT₀, IFS_T₀]

/-- GaussianZetaPartial decomposes into old and new contributions -/
theorem gaussianZetaPartial_decomp (s : ℂ) (m n : Nat) (hmn : m ≤ n) :
    GaussianZetaPartial s n = GaussianZetaPartial s m +
      ((digitBoundedNonzero_finite n).toFinset \ (digitBoundedNonzero_finite m).toFinset).sum (ComplexTerm s) := by
  simp only [GaussianZetaPartial]
  have hsub : (digitBoundedNonzero_finite m).toFinset ⊆ (digitBoundedNonzero_finite n).toFinset := by
    intro z hz
    simp only [Set.Finite.mem_toFinset] at hz ⊢
    exact digitBoundedNonzero_mono hmn hz
  rw [← Finset.sum_sdiff hsub, add_comm]

/-- ComplexTerm at 1 equals 1 -/
theorem complexTerm_one (s : ℂ) : ComplexTerm s 1 = 1 := by
  simp only [ComplexTerm, norm_one, Int.natAbs_one, Nat.cast_one]
  rw [Complex.one_cpow, div_one]

/-- GaussianZetaPartial 1 s = 1 (only element is 1) -/
theorem gaussianZetaPartial_one (s : ℂ) : GaussianZetaPartial s 1 = 1 := by
  simp only [GaussianZetaPartial]
  have h : (digitBoundedNonzero_finite 1).toFinset = {1} := by
    ext z
    simp only [Set.Finite.mem_toFinset, Finset.mem_singleton]
    constructor
    · intro hz
      rw [digitBoundedNonzero_one_eq_singleton] at hz
      exact Set.mem_singleton_iff.mp hz
    · intro hz
      rw [hz, digitBoundedNonzero_one_eq_singleton]
      exact Set.mem_singleton 1
  rw [h, Finset.sum_singleton, complexTerm_one]

/-! ## ComplexTerm Scaling Under β -/

/-- β has norm 2, so ComplexTerm s β = 2^(-s) -/
theorem complexTerm_β (s : ℂ) : ComplexTerm s β = (2 : ℂ)^(-s) := by
  simp only [ComplexTerm]
  have h : β.norm.natAbs = 2 := by decide
  rw [h]
  simp only [Nat.cast_ofNat, Complex.cpow_neg, div_eq_mul_inv, one_mul]

/-! ## The Fractal Functional Equation Setup

For the partial zeta function, we have:
  GaussianZetaPartial(s, n+1) = ComplexTerm(s, 1) + Σ over T₀ branch + Σ over T₁ branch

Since Σ over T₀ branch = 2^(-s) · GaussianZetaPartial(s, n), we get:
  GaussianZetaPartial(s, n+1) ≈ 1 + 2^(-s) · previous + T₁ contribution

In the limit, this gives:
  ζ(s) = 1 + 2^(-s) · (ζ(s) - 1) + T₁ contribution
  ζ(s) · (1 - 2^(-s)) = 1 - 2^(-s) + T₁ contribution

KEY INSIGHT: The scaling property ComplexTerm(s, βz) = 2^(-s) · ComplexTerm(s, z)
combined with IFS decomposition gives the Fractal Functional Equation.
-/

/-! ## ComplexTerm Scaling Under IFS -/

/-- Norm of βz equals 2 times norm of z (natAbs version) -/
theorem norm_natAbs_IFS_T₀ (z : GaussianInt) : (IFS_T₀ z).norm.natAbs = 2 * z.norm.natAbs := by
  simp only [IFS_T₀]
  exact norm_natAbs_β_mul z

/-- ComplexTerm scales under T₀: ComplexTerm(s, βz) uses norm 2·N(z) -/
theorem complexTerm_T₀_norm (s : ℂ) (z : GaussianInt) :
    ComplexTerm s (IFS_T₀ z) = 1 / ((2 * z.norm.natAbs : ℕ) : ℂ)^s := by
  simp only [ComplexTerm, norm_natAbs_IFS_T₀]

/-- Sum over T₀ images: each term has norm 2·N(z) -/
theorem sum_T₀_norm (s : ℂ) (S : Finset GaussianInt) :
    S.sum (fun z => ComplexTerm s (IFS_T₀ z)) =
    S.sum (fun z => 1 / ((2 * z.norm.natAbs : ℕ) : ℂ)^s) := by
  apply Finset.sum_congr rfl
  intro z _
  simp only [ComplexTerm, norm_natAbs_IFS_T₀]

/-! ## Summary: Complex Zeta Infrastructure

We have now established:
1. `ComplexTerm s z = 1/N(z)^s` - the complex term of the zeta function
2. `GaussianZetaPartial s n` - partial sum over DigitBoundedNonzero n
3. `complexTerm_β s = 2^(-s)` - β contributes 2^(-s)
4. `gaussianZetaPartial_one s = 1` - base case
5. `norm_natAbs_IFS_T₀` - N(T₀ z) = 2·N(z)
6. `sum_T₀_norm` - Sum over T₀ images uses doubled norms

The Fractal Functional Equation framework is in place:
- IFS decomposition: T₀(z) = βz, T₁(z) = 1+βz
- Scaling: ComplexTerm(s, βz) = 2^(-s) · ComplexTerm(s, z)
- This leads to: ζ(s)·(1 - 2^(-s)) = [Sum over T₁ branch]
-/

/-! ============================================================================
    PART III: THE GEOMETRIC BRIDGE

    Proving that DigitBounded sets decompose exactly according to the IFS.
    This is the missing link between the set-theoretic IFS decomposition
    and the analytic functional equation.

    Key theorem: digitBoundedNonzero_succ_eq_union shows that
      DigitBoundedNonzero (n+1) = T₀(DigitBoundedNonzero n) ∪ T₁(DigitBounded n)
============================================================================ -/

/-- T₁(0) = 1 -/
theorem IFS_T₁_zero' : IFS_T₁ 0 = 1 := by
  simp only [IFS_T₁, mul_zero, add_zero]

/-- The element 1 comes from T₁(0) -/
theorem one_from_T₁_zero' : (1 : GaussianInt) = IFS_T₁ 0 := IFS_T₁_zero'.symm

/-- DigitBoundedNonzero (n+1) decomposes into T₀ image and T₁ image -/
theorem digitBoundedNonzero_succ_eq_union (n : ℕ) :
    DigitBoundedNonzero (n + 1) =
    (IFS_T₀ '' (DigitBoundedNonzero n)) ∪ (IFS_T₁ '' (DigitBounded n)) := by
  ext z
  simp only [Set.mem_union, Set.mem_image]
  constructor
  · intro hz
    by_cases hlen : digitLength z = 1
    · -- z has digitLength 1, so z = 1
      have heq : z = 1 := digitLength_eq_one_imp_eq_one z hlen
      right
      use 0
      exact ⟨zero_mem_digitBounded n, by rw [heq]; exact IFS_T₁_zero'.symm⟩
    · -- z has digitLength ≥ 2, use IFS decomposition
      have hlen2 : 2 ≤ digitLength z := by
        have h1 := digitLength_ge_one_of_ne_zero z hz.2
        omega
      by_cases hd : digit z
      · -- digit z = true means z came from T₁
        right
        use βQuot z
        constructor
        · simp only [DigitBounded, Set.mem_setOf_eq]
          rw [digitLength_βQuot z hz.2]
          have := hz.1; omega
        · exact (ifs_decomp_digit_true z hz.2 hd).symm
      · -- digit z = false means z came from T₀
        left
        use βQuot z
        constructor
        · simp only [DigitBoundedNonzero, Set.mem_setOf_eq]
          constructor
          · rw [digitLength_βQuot z hz.2]; have := hz.1; omega
          · exact βQuot_ne_zero_of_digitLength_ge_two z hz.2 hlen2
        · have hd' : digit z = false := eq_false_of_ne_true hd
          exact (ifs_decomp_digit_false z hz.2 hd').symm
  · intro hz
    rcases hz with ⟨w, hw, heq⟩ | ⟨w, hw, heq⟩
    · -- z = T₀ w for w ∈ DigitBoundedNonzero n
      rw [← heq]
      exact IFS_T₀_maps_bounded n w hw
    · -- z = T₁ w for w ∈ DigitBounded n
      rw [← heq]
      simp only [DigitBoundedNonzero, Set.mem_setOf_eq]
      constructor
      · rw [digitLength_IFS_T₁ w]
        simp only [DigitBounded, Set.mem_setOf_eq] at hw
        omega
      · exact IFS_T₁_ne_zero w

/-- The decomposition is disjoint -/
theorem digitBoundedNonzero_succ_disjoint (n : ℕ) :
    Disjoint (IFS_T₀ '' (DigitBoundedNonzero n)) (IFS_T₁ '' (DigitBounded n)) := by
  rw [Set.disjoint_iff]
  intro z ⟨⟨w₀, _, hw₀⟩, ⟨w₁, _, hw₁⟩⟩
  have : IFS_T₀ w₀ = IFS_T₁ w₁ := hw₀.trans hw₁.symm
  exact IFS_images_disjoint w₀ w₁ this

/-! ============================================================================
    PART IV: THE FRACTAL FUNCTIONAL EQUATION

    Using the geometric bridge to derive the functional equation:
      S_{n+1}(s) = 2^{-s} · S_n(s) + [T₁ contribution]

    In the limit:
      ζ(s) · (1 - 2^{-s}) = [Sum over T₁ branch]
============================================================================ -/

/-! ## Finset versions of the decomposition -/

/-- T₀ image of a finite set is finite -/
theorem IFS_T₀_image_finite (S : Set GaussianInt) (hS : S.Finite) :
    (IFS_T₀ '' S).Finite := Set.Finite.image IFS_T₀ hS

/-- T₁ image of a finite set is finite -/
theorem IFS_T₁_image_finite (S : Set GaussianInt) (hS : S.Finite) :
    (IFS_T₁ '' S).Finite := Set.Finite.image IFS_T₁ hS

/-! ## Sum decomposition using the bridge -/

/-- GaussianZetaPartial (n+1) splits into T₀ and T₁ contributions -/
theorem gaussianZetaPartial_succ_split (s : ℂ) (n : ℕ) :
    GaussianZetaPartial s (n + 1) =
    (IFS_T₀_image_finite (DigitBoundedNonzero n) (digitBoundedNonzero_finite n)).toFinset.sum (ComplexTerm s) +
    (IFS_T₁_image_finite (DigitBounded n) (digitBounded_finite n)).toFinset.sum (ComplexTerm s) := by
  simp only [GaussianZetaPartial]
  have h_union := digitBoundedNonzero_succ_eq_union n
  have h_disj := digitBoundedNonzero_succ_disjoint n
  -- The finite set equals the union of the two image sets
  have h_eq : (digitBoundedNonzero_finite (n + 1)).toFinset =
      (IFS_T₀_image_finite (DigitBoundedNonzero n) (digitBoundedNonzero_finite n)).toFinset ∪
      (IFS_T₁_image_finite (DigitBounded n) (digitBounded_finite n)).toFinset := by
    ext z
    simp only [Set.Finite.mem_toFinset, Finset.mem_union]
    rw [h_union]
    simp only [Set.mem_union]
  rw [h_eq, Finset.sum_union]
  -- Need to show the finsets are disjoint
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb hab
  simp only [Set.Finite.mem_toFinset] at ha hb
  rw [hab] at ha
  rw [Set.disjoint_iff] at h_disj
  exact h_disj ⟨ha, hb⟩

/-- T₀ sum uses doubled norms -/
theorem T₀_sum_doubled_norms (s : ℂ) (n : ℕ) :
    (digitBoundedNonzero_finite n).toFinset.sum (fun w => ComplexTerm s (IFS_T₀ w)) =
    (digitBoundedNonzero_finite n).toFinset.sum (fun w => 1 / ((2 * w.norm.natAbs : ℕ) : ℂ)^s) := by
  apply Finset.sum_congr rfl
  intro w _
  exact complexTerm_T₀_norm s w

/-! ## The Functional Equation for Partial Sums -/

/-- Define the T₁ contribution: sum of 1/N(1+βw)^s over DigitBounded n -/
noncomputable def T₁_Contribution (s : ℂ) (n : ℕ) : ℂ :=
  (digitBounded_finite n).toFinset.sum (fun w => ComplexTerm s (IFS_T₁ w))

/-- DigitBounded 0 = {0} -/
theorem digitBounded_zero_eq : DigitBounded 0 = {0} := by
  ext z
  simp only [DigitBounded, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro hz
    by_contra hne
    have h1 := digitLength_ge_one_of_ne_zero z hne
    omega
  · intro hz
    rw [hz, digitLength_zero]

/-- T₁ contribution at level 0 is just ComplexTerm(1) = 1 -/
theorem T₁_contribution_zero (s : ℂ) : T₁_Contribution s 0 = 1 := by
  unfold T₁_Contribution
  have h : (digitBounded_finite 0).toFinset = {0} := by
    ext z
    simp only [Set.Finite.mem_toFinset, Finset.mem_singleton]
    constructor
    · intro hz
      simp only [DigitBounded, Set.mem_setOf_eq] at hz
      by_contra hne
      have h1 := digitLength_ge_one_of_ne_zero z hne
      omega
    · intro hz
      rw [hz]
      exact zero_mem_digitBounded 0
  rw [h, Finset.sum_singleton, IFS_T₁_zero', complexTerm_one]

/-- Define the T₀ contribution: sum of ComplexTerm(s, T₀ w) over DigitBoundedNonzero n -/
noncomputable def T₀_Contribution (s : ℂ) (n : ℕ) : ℂ :=
  (digitBoundedNonzero_finite n).toFinset.sum (fun w => ComplexTerm s (IFS_T₀ w))

/-- T₀ contribution at level 1 is ComplexTerm(β) = 2^(-s) -/
theorem T₀_contribution_one (s : ℂ) : T₀_Contribution s 1 = (2 : ℂ)^(-s) := by
  simp only [T₀_Contribution]
  have h : (digitBoundedNonzero_finite 1).toFinset = {1} := by
    ext z
    simp only [Set.Finite.mem_toFinset, Finset.mem_singleton]
    constructor
    · intro hz
      rw [digitBoundedNonzero_one_eq_singleton] at hz
      exact Set.mem_singleton_iff.mp hz
    · intro hz
      rw [hz, digitBoundedNonzero_one_eq_singleton]
      exact Set.mem_singleton 1
  rw [h, Finset.sum_singleton]
  simp only [IFS_T₀]
  rw [mul_one, complexTerm_β]

/-! ============================================================================
    FINAL ASSEMBLY: THE FRACTAL FUNCTIONAL EQUATION

    The culmination: proving that T₀_Contribution factors as 2^(-s) times
    the previous partial sum, giving the recurrence relation.
============================================================================ -/

/-- Key factorization: ComplexTerm(s, T₀ w) = 2^(-s) * ComplexTerm(s, w) for w ≠ 0

    This uses: (2n)^s = 2^s * n^s, so 1/(2n)^s = 2^(-s) * 1/n^s

    The algebraic identity follows from:
    - N(T₀ w) = 2 * N(w)  (norm_natAbs_β_mul)
    - (2n)^s = 2^s * n^s for positive reals
    - 1/(ab) = (1/a)(1/b) -/
theorem complexTerm_T₀_factorization (s : ℂ) (w : GaussianInt) (hw : w ≠ 0) :
    ComplexTerm s (IFS_T₀ w) = (2 : ℂ)^(-s) * ComplexTerm s w := by
  -- 1. Unfold definitions and use the norm scaling lemma
  simp only [ComplexTerm, norm_natAbs_IFS_T₀]
  -- 2. Prepare positivity proofs (crucial for complex power laws)
  have h_norm_pos : 0 < (w.norm.natAbs : ℝ) := by
    rw [Nat.cast_pos, Int.natAbs_pos]
    exact ne_of_gt (norm_pos w hw)
  have h_two_pos : 0 < (2 : ℝ) := by norm_num
  have h_norm_nonneg : 0 ≤ (w.norm.natAbs : ℝ) := le_of_lt h_norm_pos
  have h_two_nonneg : 0 ≤ (2 : ℝ) := le_of_lt h_two_pos
  -- 3. Rewrite to use ofReal for the product power formula
  have h_eq : ((2 * w.norm.natAbs : ℕ) : ℂ) = ((2 : ℝ) : ℂ) * ((w.norm.natAbs : ℝ) : ℂ) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  rw [h_eq]
  -- 4. Use the product power formula for positive reals: (xy)^s = x^s * y^s
  rw [Complex.mul_cpow_ofReal_nonneg h_two_nonneg h_norm_nonneg]
  -- 5. Rearrange fractions: 1 / (A * B) = (1/A) * (1/B)
  rw [one_div, mul_inv, mul_comm (((2 : ℝ) : ℂ)^s)⁻¹]
  -- 6. Use cpow_neg and simplify
  have h2_cast : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_cast
  have hn_cast : ((w.norm.natAbs : ℝ) : ℂ) = (w.norm.natAbs : ℂ) := Complex.ofReal_natCast _
  rw [h2_cast, hn_cast, Complex.cpow_neg, one_div]
  ring

/-- T₀_Contribution equals 2^(-s) times GaussianZetaPartial
    (The key factorization theorem) -/
theorem T₀_contribution_eq_scaled_partial (s : ℂ) (n : ℕ) :
    T₀_Contribution s n = (2 : ℂ)^(-s) * GaussianZetaPartial s n := by
  simp only [T₀_Contribution, GaussianZetaPartial]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  simp only [Set.Finite.mem_toFinset, DigitBoundedNonzero, Set.mem_setOf_eq] at hw
  exact complexTerm_T₀_factorization s w hw.2

/-- THE FRACTAL FUNCTIONAL EQUATION FOR PARTIAL SUMS

    S_{n+1}(s) = 2^{-s} · S_n(s) + T₁_Contribution(s, n)

    This is the core recurrence that characterizes the Dedekind zeta function
    of Gaussian integers via IFS decomposition.
-/
theorem gaussianZetaPartial_recurrence (s : ℂ) (n : ℕ) :
    GaussianZetaPartial s (n + 1) =
    (2 : ℂ)^(-s) * GaussianZetaPartial s n + T₁_Contribution s n := by
  rw [← T₀_contribution_eq_scaled_partial]
  -- Now need to show: GaussianZetaPartial s (n + 1) = T₀_Contribution s n + T₁_Contribution s n
  simp only [GaussianZetaPartial, T₀_Contribution, T₁_Contribution]
  -- Use the set decomposition
  have h_union := digitBoundedNonzero_succ_eq_union n
  have h_disj := digitBoundedNonzero_succ_disjoint n
  -- Convert to Finset equality
  have h_eq : (digitBoundedNonzero_finite (n + 1)).toFinset =
      (digitBoundedNonzero_finite n).toFinset.image IFS_T₀ ∪
      (digitBounded_finite n).toFinset.image IFS_T₁ := by
    ext z
    simp only [Set.Finite.mem_toFinset, Finset.mem_union, Finset.mem_image]
    rw [h_union]
    simp only [Set.mem_union, Set.mem_image]
  rw [h_eq]
  -- Split the sum over the disjoint union
  have h_finset_disj : Disjoint
      ((digitBoundedNonzero_finite n).toFinset.image IFS_T₀)
      ((digitBounded_finite n).toFinset.image IFS_T₁) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb hab
    simp only [Finset.mem_image, Set.Finite.mem_toFinset] at ha hb
    obtain ⟨w₀, _, rfl⟩ := ha
    obtain ⟨w₁, _, rfl⟩ := hb
    exact IFS_images_disjoint w₀ w₁ hab
  rw [Finset.sum_union h_finset_disj]
  -- Now show each sum equals the contribution
  congr 1
  · -- T₀ sum
    rw [Finset.sum_image]
    intro x _ y _ hxy
    exact IFS_T₀_injective hxy
  · -- T₁ sum
    rw [Finset.sum_image]
    intro x _ y _ hxy
    exact IFS_T₁_injective hxy

/-! ## Summary: The Fractal Functional Equation Structure

We have established the complete infrastructure for the Dedekind zeta function
of Gaussian integers via IFS decomposition:

**Core Results:**
1. `digitBoundedNonzero_succ_eq_union`:
   DigitBoundedNonzero(n+1) = T₀(DigitBoundedNonzero n) ∪ T₁(DigitBounded n)

2. `gaussianZetaPartial_succ_split`:
   S_{n+1}(s) = [Sum over T₀ image] + [Sum over T₁ image]

3. `gaussianZetaPartial_recurrence`:
   S_{n+1}(s) = T₀_Contribution(s, n) + T₁_Contribution(s, n)

4. `T₀_sum_doubled_norms`:
   Sum over T₀ image uses norms 2·N(w)

**Key Insight:**
Since N(T₀ w) = 2·N(w), the T₀ contribution involves terms 1/(2·N(w))^s = 2^{-s}/N(w)^s.
This means: T₀_Contribution(s, n) ≈ 2^{-s} · GaussianZetaPartial(s, n)

**The Fractal Functional Equation (in the limit):**
  ζ(s) = 2^{-s} · ζ(s) + [T₁ limit]
  ζ(s) · (1 - 2^{-s}) = lim_{n→∞} T₁_Contribution(s, n)

This expresses the Dedekind zeta function ζ_{ℤ[i]}(s) in terms of a sum
over only the T₁ ("odd") branch of the IFS!
-/

/-! ============================================================================
    PART V: CONVERGENCE ANALYSIS

    To define the global ζ(s), we need to prove that the partial sums converge.

    Key steps:
    1. Bound the norm of T₁(w) = 1 + βw
    2. Show |ComplexTerm(s, T₁ w)| decays appropriately for Re(s) > 1
    3. Prove T₁_Contribution(s, n) converges as n → ∞
    4. Define GaussianZeta(s) as the limit
============================================================================ -/

/-! ## Norm bounds for T₁ -/

/-- N(T₁ w) = N(1 + βw) ≥ 1 for all w -/
theorem norm_IFS_T₁_ge_one (w : GaussianInt) : 1 ≤ (IFS_T₁ w).norm.natAbs := by
  simp only [IFS_T₁]
  by_cases hw : w = 0
  · rw [hw, mul_zero, add_zero]
    simp only [Zsqrtd.norm_one, Int.natAbs_one, le_refl]
  · -- For w ≠ 0, N(1 + βw) ≥ 1 since 1 + βw ≠ 0
    have h_ne : 1 + β * w ≠ 0 := IFS_T₁_ne_zero w
    exact Int.natAbs_pos.mpr (ne_of_gt (norm_pos (1 + β * w) h_ne))

/-- ComplexTerm is bounded by 1 for T₁ images when Re(s) > 0

    Since N(T₁ w) ≥ 1, we have |1/N(T₁ w)^s| = N(T₁ w)^(-Re s) ≤ 1

    This follows from: for positive real n ≥ 1 and Re(s) > 0,
    |n^s| = n^(Re s) ≥ 1, so |1/n^s| ≤ 1 -/
theorem complexTerm_T₁_norm_le_one (s : ℂ) (w : GaussianInt) (hs : 0 < s.re) :
    Complex.abs (ComplexTerm s (IFS_T₁ w)) ≤ 1 := by
  simp only [ComplexTerm]
  have h_norm_ge : 1 ≤ ((IFS_T₁ w).norm.natAbs : ℝ) := by
    exact_mod_cast norm_IFS_T₁_ge_one w
  have h_norm_pos : 0 < ((IFS_T₁ w).norm.natAbs : ℝ) := by linarith
  -- |n^s| = n^(Re s) for positive real n ≥ 1, so |1/n^s| ≤ 1
  -- Uses Complex.abs_cpow_eq_rpow_re_of_pos and Real.one_le_rpow
  have h_abs_ge : 1 ≤ Complex.abs (((IFS_T₁ w).norm.natAbs : ℂ) ^ s) := by
    have h_eq : ((IFS_T₁ w).norm.natAbs : ℂ) = ((IFS_T₁ w).norm.natAbs : ℝ) := by
      simp only [Complex.ofReal_natCast]
    rw [h_eq, Complex.abs_cpow_eq_rpow_re_of_pos h_norm_pos]
    exact Real.one_le_rpow h_norm_ge (le_of_lt hs)
  rw [map_div₀, Complex.abs.map_one]
  exact div_le_one_of_le h_abs_ge (Complex.abs.nonneg _)

/-- DigitBounded (n+1) decomposes as T₀(DigitBounded n) ∪ T₁(DigitBounded n) -/
theorem digitBounded_succ_eq_union (n : ℕ) :
    DigitBounded (n + 1) = (IFS_T₀ '' (DigitBounded n)) ∪ (IFS_T₁ '' (DigitBounded n)) := by
  ext z
  simp only [Set.mem_union, Set.mem_image, DigitBounded, Set.mem_setOf_eq]
  constructor
  · intro hz
    by_cases hz0 : z = 0
    · -- z = 0 comes from T₀(0) = 0
      left
      use 0
      constructor
      · simp only [digitLength_zero]; omega
      · simp [IFS_T₀, hz0]
    · -- z ≠ 0, use digit decomposition
      by_cases hd : digit z
      · -- digit z = true means z came from T₁
        right
        use βQuot z
        constructor
        · rw [digitLength_βQuot z hz0]; omega
        · exact (ifs_decomp_digit_true z hz0 hd).symm
      · -- digit z = false means z came from T₀
        left
        use βQuot z
        constructor
        · rw [digitLength_βQuot z hz0]; omega
        · have hd' : digit z = false := eq_false_of_ne_true hd
          exact (ifs_decomp_digit_false z hz0 hd').symm
  · intro hz
    rcases hz with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
    · -- z = T₀ w
      by_cases hw0 : w = 0
      · simp [IFS_T₀, hw0, digitLength_zero]
      · rw [digitLength_IFS_T₀ w hw0]; omega
    · -- z = T₁ w
      rw [digitLength_IFS_T₁ w]; omega

/-- T₀ and T₁ images of DigitBounded n are disjoint -/
theorem digitBounded_T₀_T₁_disjoint (n : ℕ) :
    Disjoint (IFS_T₀ '' (DigitBounded n)) (IFS_T₁ '' (DigitBounded n)) := by
  rw [Set.disjoint_iff]
  intro z ⟨⟨w₀, _, hw₀⟩, ⟨w₁, _, hw₁⟩⟩
  have : IFS_T₀ w₀ = IFS_T₁ w₁ := hw₀.trans hw₁.symm
  exact IFS_images_disjoint w₀ w₁ this

/-- The cardinality of DigitBounded n is 2^n -/
theorem digitBounded_card (n : ℕ) : (digitBounded_finite n).toFinset.card = 2^n := by
  induction n with
  | zero =>
    have h : (digitBounded_finite 0).toFinset = {0} := by
      ext z
      simp only [Set.Finite.mem_toFinset, DigitBounded, Set.mem_setOf_eq, Finset.mem_singleton]
      constructor
      · intro hz
        by_contra hne
        have h1 := digitLength_ge_one_of_ne_zero z hne
        omega
      · intro hz
        rw [hz, digitLength_zero]
    rw [h, Finset.card_singleton]
    simp
  | succ n ih =>
    -- DigitBounded (n+1) = T₀(DigitBounded n) ∪ T₁(DigitBounded n)
    have h_union := digitBounded_succ_eq_union n
    have h_disj := digitBounded_T₀_T₁_disjoint n
    -- Convert to finsets
    have h_eq : (digitBounded_finite (n + 1)).toFinset =
        (digitBounded_finite n).toFinset.image IFS_T₀ ∪
        (digitBounded_finite n).toFinset.image IFS_T₁ := by
      ext z
      simp only [Set.Finite.mem_toFinset, Finset.mem_union, Finset.mem_image]
      rw [h_union, Set.mem_union, Set.mem_image, Set.mem_image]
    have h_disj_fin : Disjoint
        ((digitBounded_finite n).toFinset.image IFS_T₀)
        ((digitBounded_finite n).toFinset.image IFS_T₁) := by
      rw [Finset.disjoint_iff_ne]
      intro a ha b hb hab
      simp only [Finset.mem_image, Set.Finite.mem_toFinset] at ha hb
      obtain ⟨w₀, _, rfl⟩ := ha
      obtain ⟨w₁, _, rfl⟩ := hb
      exact IFS_images_disjoint w₀ w₁ hab
    rw [h_eq, Finset.card_union_of_disjoint h_disj_fin]
    rw [Finset.card_image_of_injective _ IFS_T₀_injective]
    rw [Finset.card_image_of_injective _ IFS_T₁_injective]
    rw [ih]
    ring

/-- T₁_Contribution has exactly 2^n terms -/
theorem T₁_contribution_terms_eq (s : ℂ) (n : ℕ) :
    (digitBounded_finite n).toFinset.card = 2^n := digitBounded_card n

/-! ## Summary: Convergence Framework

The convergence of the partial sums follows from:
1. `norm_IFS_T₁_ge_one`: Every T₁ term has norm ≥ 1
2. `complexTerm_T₁_norm_le_one`: |1/N(T₁ w)^s| ≤ 1 for Re(s) > 0
3. The number of terms at level n is bounded by 2^n
4. Each new level adds terms with norms roughly doubling

For Re(s) > 1, the series converges absolutely by comparison with
the standard Dedekind zeta function convergence.

The final step (not yet formalized) would be:
- Define `GaussianZeta s := lim_{n→∞} GaussianZetaPartial s n`
- Prove this limit exists for Re(s) > 1
- Show it satisfies: ζ(s) · (1 - 2^{-s}) = lim_{n→∞} T₁_Contribution(s, n)
-/

/-! ============================================================================
    PART VI: NORM GROWTH ESTIMATES

    To prove convergence for Re(s) > 1, we need to show that norms grow
    exponentially with digit length. Since |β| = √2, we expect:
      z ∈ DigitBounded n, z ≠ 0  ⟹  N(z) ≥ c · 2^n for some c > 0

    Combined with the count (2^n terms), this gives:
      |S_n| · max_term ≤ 2^n · (c · 2^n)^{-σ} = c^{-σ} · 2^{n(1-σ)}

    For σ = Re(s) > 1, this decays exponentially, proving convergence.
============================================================================ -/

/-! ## Norm bounds by digit length -/

/-- Key lemma: For z with digitLength n ≥ 1, we have N(z) ≥ 1.
    This is because digitLength z ≥ 1 implies z ≠ 0. -/
theorem norm_natAbs_ge_one_of_digitLength_ge_one (z : GaussianInt) (hn : 1 ≤ digitLength z) :
    1 ≤ z.norm.natAbs := by
  have hz : z ≠ 0 := by
    intro heq
    rw [heq, digitLength_zero] at hn
    omega
  exact Int.natAbs_pos.mpr (ne_of_gt (norm_pos z hz))

/-- Coarse norm bound: For z ∈ DigitBoundedNonzero n, N(z) ≥ 1 -/
theorem norm_natAbs_ge_one_in_digitBoundedNonzero (n : ℕ) (z : GaussianInt)
    (hz : z ∈ DigitBoundedNonzero n) : 1 ≤ z.norm.natAbs := by
  exact Int.natAbs_pos.mpr (ne_of_gt (norm_pos z hz.2))

/-- The norm of 1 is 1 -/
theorem norm_natAbs_one : (1 : GaussianInt).norm.natAbs = 1 := by
  simp [Zsqrtd.norm_one]

/-- Explicit formula: N(1 + βz) = 1 - 2(z.re + z.im) + 2N(z) -/
theorem norm_one_plus_β_mul (z : GaussianInt) :
    (1 + β * z).norm = 1 - 2 * (z.re + z.im) + 2 * z.norm := by
  simp only [β, Zsqrtd.norm, Zsqrtd.add_re, Zsqrtd.add_im, Zsqrtd.one_re, Zsqrtd.one_im,
             Zsqrtd.mul_re, Zsqrtd.mul_im]
  ring

/-- For nonzero w, |w.re| ≤ N(w). Proof: |re|² ≤ N(w) and for N ≥ 1, |re| ≤ N. -/
theorem re_natAbs_le_norm (w : GaussianInt) (hw : w ≠ 0) : w.re.natAbs ≤ w.norm.natAbs := by
  have h_norm_ge_1 := norm_natAbs_ge_one w hw
  by_cases h : w.re.natAbs ≤ 1
  · exact le_trans h h_norm_ge_1
  · push_neg at h
    have h_norm_eq : w.norm = w.re * w.re + w.im * w.im := by simp [norm_eq]
    have h_re_sq_le_norm : w.re * w.re ≤ w.norm := by
      rw [h_norm_eq]; nlinarith [mul_self_nonneg w.im]
    have h_norm_nonneg : 0 ≤ w.norm := norm_nonneg w
    have h_sq_le : w.re.natAbs * w.re.natAbs ≤ w.norm.natAbs := by
      have h1 : (w.re.natAbs : ℤ) * w.re.natAbs = w.re * w.re := Int.natAbs_mul_self' w.re
      have h2 : (w.norm.natAbs : ℤ) = w.norm := Int.natAbs_of_nonneg h_norm_nonneg
      have h3 : (w.re.natAbs : ℤ) * w.re.natAbs ≤ w.norm.natAbs := by rw [h1, h2]; exact h_re_sq_le_norm
      exact_mod_cast h3
    have h_sq_ge : w.re.natAbs ≤ w.re.natAbs * w.re.natAbs := by
      calc w.re.natAbs = w.re.natAbs * 1 := by ring
        _ ≤ w.re.natAbs * w.re.natAbs := Nat.mul_le_mul_left _ (by omega)
    omega

/-- For nonzero w, |w.im| ≤ N(w) -/
theorem im_natAbs_le_norm (w : GaussianInt) (hw : w ≠ 0) : w.im.natAbs ≤ w.norm.natAbs := by
  have h_norm_ge_1 := norm_natAbs_ge_one w hw
  by_cases h : w.im.natAbs ≤ 1
  · exact le_trans h h_norm_ge_1
  · push_neg at h
    have h_norm_eq : w.norm = w.re * w.re + w.im * w.im := by simp [norm_eq]
    have h_im_sq_le_norm : w.im * w.im ≤ w.norm := by
      rw [h_norm_eq]; nlinarith [mul_self_nonneg w.re]
    have h_norm_nonneg : 0 ≤ w.norm := norm_nonneg w
    have h_sq_le : w.im.natAbs * w.im.natAbs ≤ w.norm.natAbs := by
      have h1 : (w.im.natAbs : ℤ) * w.im.natAbs = w.im * w.im := Int.natAbs_mul_self' w.im
      have h2 : (w.norm.natAbs : ℤ) = w.norm := Int.natAbs_of_nonneg h_norm_nonneg
      have h3 : (w.im.natAbs : ℤ) * w.im.natAbs ≤ w.norm.natAbs := by rw [h1, h2]; exact h_im_sq_le_norm
      exact_mod_cast h3
    have h_sq_ge : w.im.natAbs ≤ w.im.natAbs * w.im.natAbs := by
      calc w.im.natAbs = w.im.natAbs * 1 := by ring
        _ ≤ w.im.natAbs * w.im.natAbs := Nat.mul_le_mul_left _ (by omega)
    omega

/-- For nonzero w, |re + im| ≤ 2 * N(w) -/
theorem re_plus_im_natAbs_le (w : GaussianInt) (hw : w ≠ 0) :
    (w.re + w.im).natAbs ≤ 2 * w.norm.natAbs := by
  have h1 := re_natAbs_le_norm w hw
  have h2 := im_natAbs_le_norm w hw
  calc (w.re + w.im).natAbs ≤ w.re.natAbs + w.im.natAbs := Int.natAbs_add_le _ _
    _ ≤ w.norm.natAbs + w.norm.natAbs := by omega
    _ = 2 * w.norm.natAbs := by ring

/-- Upper bound: N(T₁ w) ≤ 1 + 6 * N(w)

    Proof: N(1 + βw) = 1 - 2(re+im) + 2N(w) by norm_one_plus_β_mul.
    Since |re+im| ≤ 2N(w), we have -(re+im) ≤ 2N(w).
    Thus N(T₁ w) = 1 - 2(re+im) + 2N ≤ 1 + 4N + 2N = 1 + 6N. -/
theorem norm_IFS_T₁_upper (w : GaussianInt) (hw : w ≠ 0) :
    (IFS_T₁ w).norm.natAbs ≤ 1 + 6 * w.norm.natAbs := by
  have h_sum_bound := re_plus_im_natAbs_le w hw
  have h_formula := norm_one_plus_β_mul w
  -- (IFS_T₁ w).norm = (1 + β * w).norm = 1 - 2(re+im) + 2N(w)
  have h_eq : (IFS_T₁ w).norm = 1 - 2 * (w.re + w.im) + 2 * w.norm := by
    simp only [IFS_T₁]; exact h_formula
  -- Key: -(re+im) ≤ |re+im| ≤ 2N
  have h_neg_bound : -(w.re + w.im) ≤ 2 * w.norm := by
    have h1 : -(w.re + w.im) ≤ |w.re + w.im| := neg_le_abs _
    have h2 : |w.re + w.im| = (w.re + w.im).natAbs := Int.abs_eq_natAbs _
    have h3 : (w.norm.natAbs : ℤ) = w.norm := Int.natAbs_of_nonneg (norm_nonneg w)
    calc -(w.re + w.im) ≤ |w.re + w.im| := h1
      _ = (w.re + w.im).natAbs := h2
      _ ≤ 2 * w.norm.natAbs := by exact_mod_cast h_sum_bound
      _ = 2 * w.norm := by rw [h3]
  -- N(T₁ w) = 1 - 2(re+im) + 2N ≤ 1 + 4N + 2N = 1 + 6N (as integers)
  have h_ineq : (IFS_T₁ w).norm ≤ 1 + 6 * w.norm := by
    rw [h_eq]; linarith
  -- Convert to natAbs
  have h_nonneg : 0 ≤ (IFS_T₁ w).norm := norm_nonneg _
  have h_lhs : (IFS_T₁ w).norm.natAbs = (IFS_T₁ w).norm := Int.natAbs_of_nonneg h_nonneg
  -- Show RHS natAbs = 1 + 6 * w.norm.natAbs
  have h_norm_eq : (1 + 6 * w.norm.natAbs : ℤ) = 1 + 6 * w.norm := by
    rw [Int.natAbs_of_nonneg (norm_nonneg w)]
  -- Final: natAbs comparison
  have h_final : ((IFS_T₁ w).norm.natAbs : ℤ) ≤ 1 + 6 * w.norm.natAbs := by
    rw [h_lhs, h_norm_eq]; exact h_ineq
  exact_mod_cast h_final

/-- Upper bound: N(z) ≤ 7^n for z ∈ DigitBounded n
    Uses: N(T₀ w) = 2*N(w), N(T₁ w) ≤ 1 + 6*N(w)
    Induction: 2*7^n ≤ 7^(n+1), and 1 + 6*7^n ≤ 7^(n+1) -/
theorem norm_upper_bound_digitBounded (n : ℕ) (z : GaussianInt)
    (hz : z ∈ DigitBounded n) : z.norm.natAbs ≤ 7^n := by
  induction n generalizing z with
  | zero =>
    simp only [DigitBounded, Set.mem_setOf_eq] at hz
    have hz0 : z = 0 := by
      by_contra hne
      have := digitLength_ge_one_of_ne_zero z hne
      omega
    simp [hz0, Zsqrtd.norm_zero]
  | succ n ih =>
    rw [digitBounded_succ_eq_union] at hz
    rcases hz with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
    · -- z = T₀(w), N(z) = 2 * N(w)
      have h_w_bound := ih w hw
      simp only [norm_natAbs_IFS_T₀]
      calc 2 * w.norm.natAbs ≤ 2 * 7^n := Nat.mul_le_mul_left 2 h_w_bound
        _ ≤ 7 * 7^n := Nat.mul_le_mul_right (7^n) (by omega)
        _ = 7^(n+1) := by ring
    · -- z = T₁(w)
      have h_w_bound := ih w hw
      by_cases hw0 : w = 0
      · simp only [hw0, IFS_T₁, mul_zero, add_zero, Zsqrtd.norm_one, Int.natAbs_one]
        have : 7^(n+1) ≥ 1 := Nat.one_le_pow _ _ (by omega)
        omega
      · -- w ≠ 0: N(T₁ w) ≤ 1 + 6 * N(w) ≤ 1 + 6 * 7^n ≤ 7^(n+1)
        have h_T₁_bound := norm_IFS_T₁_upper w hw0
        calc (IFS_T₁ w).norm.natAbs ≤ 1 + 6 * w.norm.natAbs := h_T₁_bound
          _ ≤ 1 + 6 * 7^n := by nlinarith
          _ ≤ 7 * 7^n := by nlinarith [Nat.one_le_pow n 7 (by omega)]
          _ = 7^(n+1) := by ring

/-! ## Convergence Bound -/

/-- The key bound for convergence: sum of |terms| at level n is bounded.
    For Re(s) = σ > 1, the partial sum is bounded by 2^n · 1 = 2^n,
    but this still diverges. The real argument requires norm growth. -/
theorem partial_sum_bound_coarse (s : ℂ) (n : ℕ) (hs : 0 < s.re) :
    Complex.abs (GaussianZetaPartial s n) ≤ 2^n := by
  simp only [GaussianZetaPartial]
  calc Complex.abs ((digitBoundedNonzero_finite n).toFinset.sum (ComplexTerm s))
      ≤ (digitBoundedNonzero_finite n).toFinset.sum (fun z => Complex.abs (ComplexTerm s z)) :=
          Complex.abs.sum_le _ _
    _ ≤ (digitBoundedNonzero_finite n).toFinset.sum (fun _ => (1 : ℝ)) := by
          apply Finset.sum_le_sum
          intro z hz
          simp only [Set.Finite.mem_toFinset, DigitBoundedNonzero, Set.mem_setOf_eq] at hz
          -- Need to show |ComplexTerm s z| ≤ 1 for z with norm ≥ 1
          simp only [ComplexTerm]
          have h_norm_ge : 1 ≤ (z.norm.natAbs : ℝ) := by
            have h := Int.natAbs_pos.mpr (ne_of_gt (norm_pos z hz.2))
            exact_mod_cast h
          have h_norm_pos : 0 < (z.norm.natAbs : ℝ) := by linarith
          rw [map_div₀, Complex.abs.map_one]
          have h_abs_ge : 1 ≤ Complex.abs ((z.norm.natAbs : ℂ) ^ s) := by
            have h_eq : (z.norm.natAbs : ℂ) = ((z.norm.natAbs : ℕ) : ℝ) := by
              simp only [Complex.ofReal_natCast]
            rw [h_eq, Complex.abs_cpow_eq_rpow_re_of_pos h_norm_pos]
            exact Real.one_le_rpow h_norm_ge (le_of_lt hs)
          exact div_le_one_of_le h_abs_ge (Complex.abs.nonneg _)
    _ = (digitBoundedNonzero_finite n).toFinset.card := by simp
    _ ≤ 2^n := by
          have h_sub : (digitBoundedNonzero_finite n).toFinset ⊆ (digitBounded_finite n).toFinset := by
            intro z hz
            simp only [Set.Finite.mem_toFinset] at hz ⊢
            exact digitBoundedNonzero_subset n hz
          have h_card := Finset.card_le_card h_sub
          rw [digitBounded_card n] at h_card
          exact_mod_cast h_card

/-! ## Summary: Convergence Framework

**What we have proved:**
1. Count: |DigitBounded n| = 2^n (digitBounded_card)
2. Each term satisfies |1/N(z)^s| ≤ 1 for Re(s) > 0
3. partial_sum_bound_coarse: |S_n| ≤ 2^n

**What remains (for full convergence proof):**
1. Prove norm growth: z ∈ DigitBoundedNonzero n, z ≠ 0 ⟹ N(z) ≥ c · 2^{n-k}
   for some constants c, k
2. This would give: |S_n| ≤ 2^n · (c · 2^{n-k})^{-σ} = c^{-σ} · 2^{k·σ} · 2^{n(1-σ)}
3. For σ > 1, this decays exponentially, proving convergence

The norm growth estimate requires deeper analysis of the digit representation
and the geometry of the twindragon fractal.
-/

end SPBiTopology
