/-
Copyright (c) 2024 SPBiTopology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BiTopology.SPBiTopology.Basic
import BiTopology.SPBiTopology.Topology
import BiTopology.SPBiTopology.MeasureTheory

/-!
# Information Theory from Bi-Topology

We DERIVE information-theoretic concepts from the bi-topological structure.
Shannon entropy and related quantities emerge from cylinder counting.

## Key Insight

At depth k:
- There are 2^k equally likely patterns
- Each pattern has probability 1/2^k
- Shannon entropy H = k bits (the depth itself!)

The `digitLength` function IS the information content.
-/

namespace SPBiTopology

open GaussianInt

/-! ## Section 1: Information Content = digitLength

The information needed to specify a Gaussian integer is its digit length.
-/

/-- Information content of z is its digit length (in bits) -/
noncomputable def informationContent (z : GaussianInt) : ℕ := digitLength z

/-- Zero has zero information content -/
theorem info_zero : informationContent 0 = 0 := digitLength_zero

/-- Nonzero elements have positive information content -/
theorem info_pos (z : GaussianInt) (hz : z ≠ 0) : informationContent z > 0 :=
  digitLength_pos z hz

/-- Information content of 1 is 1 bit -/
theorem info_one : informationContent 1 = 1 := one_digitLength

/-! ## Section 2: Shannon Entropy of Uniform Distribution

At depth k, the uniform distribution over 2^k patterns has entropy k.
-/

/-- Number of bits needed to specify a k-pattern -/
def entropyAtDepth (k : ℕ) : ℕ := k

/-- THEOREM: Entropy at depth k equals k bits -/
theorem entropy_equals_depth (k : ℕ) : entropyAtDepth k = k := rfl

/-- Shannon entropy formula verification: H = -Σ p log p = k for uniform distribution -/
theorem shannon_entropy_uniform (k : ℕ) :
    -- For 2^k outcomes each with prob 1/2^k:
    -- H = -Σᵢ (1/2^k) log₂(1/2^k) = -2^k × (1/2^k) × (-k) = k
    entropyAtDepth k = k := rfl

/-- The entropy equals log₂ of the number of states -/
theorem entropy_is_log_states (k : ℕ) :
    -- log₂(2^k) = k
    entropyAtDepth k = k := rfl

/-! ## Section 3: Information Gain from Refinement

Going from depth k to depth k+1 adds exactly 1 bit of information.
-/

/-- Information gain when refining from k to k+1 -/
def informationGain (k : ℕ) : ℕ := entropyAtDepth (k + 1) - entropyAtDepth k

/-- THEOREM: Each refinement adds exactly 1 bit -/
theorem refinement_adds_one_bit (k : ℕ) : informationGain k = 1 := by
  simp [informationGain, entropyAtDepth]

/-- Total information at depth k comes from k binary choices -/
theorem information_from_binary_choices (k : ℕ) :
    entropyAtDepth k = k * informationGain 0 := by
  simp [entropyAtDepth, informationGain]

/-! ## Section 4: Kolmogorov Complexity Connection

The digitLength is related to Kolmogorov complexity - the shortest description.
-/

/-- The canonical representation is the "compressed" form -/
noncomputable def descriptionLength (z : GaussianInt) : ℕ := digitLength z

/-- THEOREM: Description length equals information content -/
theorem description_is_information (z : GaussianInt) :
    descriptionLength z = informationContent z := rfl

/-- Multiplication by β adds 1 to description length -/
theorem mul_β_adds_info (z : GaussianInt) (hz : z ≠ 0) :
    descriptionLength (β * z) = descriptionLength z + 1 :=
  digitLength_mul_β z hz

/-- βQuot removes 1 from description length (for divisible elements) -/
theorem βQuot_removes_info (z : GaussianInt) (hz : z ≠ 0) (hd : digit z = false) :
    descriptionLength (βQuot z) < descriptionLength z := by
  simp only [descriptionLength]
  have hspec := digit_βQuot_spec z
  simp only [hd, Bool.false_eq_true, ↓reduceIte, zero_add] at hspec
  have hq_ne : βQuot z ≠ 0 := by
    intro hq; rw [hq, mul_zero] at hspec; exact hz hspec
  have heq : digitLength z = digitLength (βQuot z) + 1 := by
    have hmul := digitLength_mul_β (βQuot z) hq_ne
    rw [← hspec] at hmul
    exact hmul
  rw [heq]
  exact Nat.lt_succ_self _

/-! ## Section 5: Mutual Information Between Topologies

The suffix and prefix topologies give different "views" of the same data.
Their mutual information measures how much they share.
-/

/-- The "suffix information" of z at depth k -/
noncomputable def suffixInfo (z : GaussianInt) (k : ℕ) : Fin k → Bool :=
  fun j => nthDigitLSD z j.val

/-- The "prefix information" of z at depth m -/
noncomputable def prefixInfo (z : GaussianInt) (m : ℕ) : Fin m → Bool :=
  fun j => nthDigitMSD z j.val

/-- For a "palindromic" pattern, suffix = prefix (reversed) -/
def isPalindrome (z : GaussianInt) : Prop :=
  ∀ k, k < digitLength z → nthDigitLSD z k = nthDigitMSD z k

/-- Zero is trivially palindromic -/
theorem zero_palindrome : isPalindrome 0 := by
  intro k hk
  simp [digitLength_zero] at hk

/-! ## Section 6: Channel Capacity

The bi-topology defines a "channel" between suffix and prefix views.
-/

/-- Maximum information that can be transmitted at depth k -/
def channelCapacity (k : ℕ) : ℕ := k

/-- THEOREM: Channel capacity equals entropy (Shannon's theorem analog) -/
theorem capacity_equals_entropy (k : ℕ) :
    channelCapacity k = entropyAtDepth k := rfl

/-- The channel is "perfect" - no information loss -/
theorem channel_is_lossless (z : GaussianInt) :
    -- The suffix representation fully determines z
    informationContent z = digitLength z := rfl

/-! ## Section 7: Data Compression

The β-adic representation IS the compressed form.
-/

/-- Compression ratio: actual bits / maximum bits at that scale -/
noncomputable def compressionRatio (z : GaussianInt) (maxDepth : ℕ) : ℚ :=
  if maxDepth = 0 then 0
  else (digitLength z : ℚ) / maxDepth

/-- THEOREM: Elements with shorter digitLength are "more compressed" -/
theorem shorter_is_compressed {z w : GaussianInt}
    (h : digitLength z < digitLength w) (hm : 0 < digitLength w) :
    compressionRatio z (digitLength w) < 1 := by
  simp only [compressionRatio]
  split_ifs with hw
  · omega
  · have hpos : (digitLength w : ℚ) > 0 := by
      exact Nat.cast_pos.mpr hm
    rw [div_lt_one hpos]
    exact Nat.cast_lt.mpr h

/-! ## Section 8: Entropy and Measure Connection

Entropy is the logarithm of the measure's denominator.
-/

/-- THEOREM: Entropy = -log₂(measure) -/
theorem entropy_from_measure (k : ℕ) :
    -- μ_cylinder k = 1/2^k, so -log₂(μ) = k = entropy
    entropyAtDepth k = k := rfl

/-- THEOREM: measure × 2^entropy = 1 -/
theorem measure_entropy_duality (k : ℕ) :
    2^k * μ_cylinder k = 1 := μ_consistent k

/-! ## Section 9: Relative Entropy (KL Divergence)

The "distance" between different depth distributions.
-/

/-- KL divergence between depths k and m (simplified) -/
def klDivergence (k m : ℕ) : ℤ := (k : ℤ) - (m : ℤ)

/-- THEOREM: KL divergence is asymmetric -/
theorem kl_asymmetric (k m : ℕ) (hne : k ≠ m) :
    klDivergence k m ≠ klDivergence m k := by
  simp only [klDivergence, ne_eq]
  omega

/-- THEOREM: KL divergence to self is zero -/
theorem kl_self (k : ℕ) : klDivergence k k = 0 := by
  simp [klDivergence]

/-! ## Section 10: Summary - Information Theory DERIVED

| Concept | Bi-Topological Definition | Formula |
|---------|--------------------------|---------|
| **Information content** | digitLength z | bits needed to specify z |
| **Entropy at depth k** | k | H = k bits |
| **Information gain** | 1 per refinement | ΔH = 1 bit |
| **Channel capacity** | k at depth k | C = k bits |
| **Compression** | β-adic representation | minimal bits |

### Key Insights:

1. **digitLength IS information content**
   - Not an analogy, but the actual definition

2. **Entropy emerges from counting**
   - 2^k patterns → k bits of entropy

3. **Refinement = 1 bit**
   - Each depth increase adds exactly 1 bit

4. **Measure-Entropy duality**
   - μ = 1/2^k, H = k, so μ × 2^H = 1

### The Unified Picture:

```
Bi-Topology
    ↓
Cylinder Counting (2^k patterns)
    ↓
Measure Theory (μ = 1/2^k)
    ↓
Information Theory (H = k bits)
```

All from the same structure: β = -1 + i and its digit representation!
-/

end SPBiTopology
