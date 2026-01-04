/-
  BiTopology/SPBiTopology/QuantumBiTopology.lean

  QUANTUM MECHANICS FROM BI-TOPOLOGY - FRESH START

  GOAL: Build quantum mechanics from first principles using bi-topology.
  METHOD: No speculation. Each claim must be a proven theorem or a clearly
          labeled physical interpretation.

  PHYSICAL INTERPRETATION (clearly marked, not proven):
  - Space: ℤ[i] lattice (2D discrete space)
  - Time: digitLength (number of β-digits)
  - State: cylinder pattern (which cylinder a point belongs to)
  - Evolution: βQuot (coarse-graining = forward time)

  MATHEMATICAL FACTS (proven):
  - Every z ∈ ℤ[i] has unique β-adic expansion
  - Cylinder at depth k has measure 1/2^k
  - βQuot decreases digitLength by 1 (for non-fixed points)

  ACHIEVABLE GOALS:
  1. Define quantum state as cylinder membership
  2. Prove states form a complete orthonormal basis
  3. Define time evolution via βQuot
  4. Prove unitarity analog (measure preservation)
  5. Define position/momentum from suffix/prefix
  6. Prove uncertainty relation from topology discontinuity
-/

import BiTopology.SPBiTopology.Basic
import BiTopology.SPBiTopology.Topology
import BiTopology.SPBiTopology.MeasureTheory
import BiTopology.SPBiTopology.PhysicsFoundations

set_option autoImplicit false

namespace SPBiTopology.Quantum

open GaussianInt Zsqrtd

/-! ============================================================================
    PART I: QUANTUM STATES AS CYLINDER PATTERNS

    A quantum state at depth k is a choice of k binary digits.
    There are exactly 2^k states at depth k.
============================================================================ -/

/-- A quantum state at depth k is a pattern of k binary digits -/
abbrev QuantumState (k : ℕ) := Fin k → Bool

/-- The number of quantum states at depth k is 2^k -/
theorem state_count (k : ℕ) : Fintype.card (QuantumState k) = 2^k := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- The zero state: all digits false -/
def zeroState (k : ℕ) : QuantumState k := fun _ => false

/-- The "all ones" state -/
def onesState (k : ℕ) : QuantumState k := fun _ => true

/-! ============================================================================
    PART II: STATES ARE ORTHONORMAL

    Different states correspond to disjoint cylinders.
    This is the orthogonality condition.
============================================================================ -/

/-- Two states are orthogonal if they differ at any position -/
def areOrthogonal (k : ℕ) (s t : QuantumState k) : Prop := s ≠ t

/-- THEOREM: Distinct states are orthogonal (trivially true by definition) -/
theorem distinct_states_orthogonal (k : ℕ) (s t : QuantumState k) (h : s ≠ t) :
    areOrthogonal k s t := h

/-- THEOREM: States partition the space (every z belongs to exactly one state) -/
theorem states_partition (k : ℕ) (z : GaussianInt) :
    ∃! s : QuantumState k, cylinderPattern z k = s := by
  use cylinderPattern z k
  simp only [and_self, forall_eq', implies_true]

/-- THEOREM: Each state has equal measure 1/2^k (equiprobable) -/
theorem state_measure (k : ℕ) (_s : QuantumState k) :
    μ_cylinder k = 1 / 2^k := rfl

/-- THEOREM: Total measure sums to 1 (normalization) -/
theorem total_measure_one (k : ℕ) :
    ∑ _s : QuantumState k, μ_cylinder k = 1 := by
  simp only [QuantumState]
  exact μ_partition_sum k

/-! ============================================================================
    PART III: TIME EVOLUTION VIA βQuot

    PHYSICAL INTERPRETATION: βQuot is the time evolution operator.
    Moving forward in time = coarse-graining = losing fine structure.

    This is like decoherence: fine details are lost over time.
============================================================================ -/

/-- The time evolution operator: βQuot moves us forward in time -/
noncomputable def timeStep : GaussianInt → GaussianInt := βQuot

/-- THEOREM: Time evolution decreases state complexity (for nonzero z) -/
theorem time_decreases_complexity (z : GaussianInt) (hz : z ≠ 0) :
    digitLength (timeStep z) < digitLength z := by
  simp only [timeStep]
  have h := digitLength_succ z hz
  omega

/-- THEOREM: Time evolution terminates at the vacuum (zero) -/
theorem time_reaches_vacuum (z : GaussianInt) :
    ∃ n : ℕ, (timeStep^[n]) z = 0 := by
  use digitLength z
  simp only [timeStep]
  exact orbit_length_eq_digitLength z

/-- The number of time steps to reach vacuum -/
noncomputable def timeToVacuum (z : GaussianInt) : ℕ := digitLength z

/-- THEOREM: timeToVacuum is exactly the number of steps needed -/
theorem timeToVacuum_spec (z : GaussianInt) :
    (timeStep^[timeToVacuum z]) z = 0 := by
  simp only [timeToVacuum, timeStep]
  exact orbit_length_eq_digitLength z

/-! ============================================================================
    PART IV: STATE TRANSITIONS

    Each time step, the state "forgets" one digit.
    The first digit is emitted as a "quantum" of information.
============================================================================ -/

/-- The information emitted at each time step -/
def emittedBit (z : GaussianInt) : Bool := digit z

/-- THEOREM: The emitted bit determines if we were in digit-0 or digit-1 sector -/
theorem emitted_bit_determines_sector (z : GaussianInt) :
    (emittedBit z = false ↔ β ∣ z) ∧ (emittedBit z = true ↔ ¬(β ∣ z)) := by
  constructor
  · exact digit_false_iff z
  · exact digit_true_iff z

/-- THEOREM: State reconstruction - we can recover z from emitted bit and βQuot z -/
theorem state_reconstruction (z : GaussianInt) :
    z = (if emittedBit z then 1 else 0) + β * timeStep z :=
  digit_βQuot_spec z

/-- The "history" of a state: all emitted bits -/
noncomputable def stateHistory (z : GaussianInt) : List Bool :=
  toDigits z

/-- THEOREM: History length equals time to vacuum -/
theorem history_length (z : GaussianInt) :
    (stateHistory z).length = timeToVacuum z := rfl

/-- THEOREM: History uniquely determines the state (injectivity) -/
theorem history_determines_state (z w : GaussianInt)
    (h : stateHistory z = stateHistory w) : z = w :=
  toDigits_injective h

/-! ============================================================================
    PART V: MEASUREMENT AND COLLAPSE

    PHYSICAL INTERPRETATION: "Measuring" at depth k means asking
    "which k-cylinder is z in?"

    The answer is the cylinder pattern - a deterministic function of z.
    No randomness yet - that comes from the measure on initial conditions.
============================================================================ -/

/-- A measurement at depth k returns the k-bit state -/
noncomputable def measure (k : ℕ) (z : GaussianInt) : QuantumState k :=
  cylinderPattern z k

/-- THEOREM: Measurement is deterministic (same z gives same result) -/
theorem measurement_deterministic (k : ℕ) (z : GaussianInt) :
    measure k z = measure k z := rfl

/-- THEOREM: Coarser measurement is determined by finer measurement -/
theorem coarse_from_fine (k m : ℕ) (hkm : k ≤ m) (z : GaussianInt) :
    measure k z = fun i => measure m z ⟨i.val, Nat.lt_of_lt_of_le i.isLt hkm⟩ := by
  funext i
  simp only [measure, cylinderPattern]

/-- THEOREM: Measurement after time step loses first bit -/
theorem measure_after_time (k : ℕ) (z : GaussianInt) :
    measure k (timeStep z) = fun i => nthDigitLSD z (i.val + 1) := by
  funext i
  simp only [measure, cylinderPattern, timeStep]
  exact (nthDigitLSD_succ z i.val).symm

/-! ============================================================================
    PART VI: SUMMARY - WHAT WE HAVE PROVEN

    PROVEN MATHEMATICAL FACTS:
    1. state_count: 2^k states at depth k
    2. states_partition: every z belongs to exactly one state
    3. state_measure: each state has measure 1/2^k
    4. total_measure_one: measures sum to 1
    5. time_decreases_complexity: evolution reduces state size
    6. time_reaches_vacuum: all states evolve to vacuum
    7. state_reconstruction: z = bit + β * βQuot(z)
    8. history_determines_state: history is complete information
    9. coarse_from_fine: coarse measurement from fine
    10. measure_after_time: time evolution shifts measurements

    PHYSICAL INTERPRETATION (NOT proven, but consistent):
    - States = cylinder patterns
    - Time = digitLength (discrete)
    - Evolution = βQuot (irreversible coarse-graining)
    - Measurement = reading cylinder pattern
    - Vacuum = the zero state

    NEXT STEPS (achievable goals):
    1. Define superposition via complex amplitudes on states
    2. Prove interference from amplitude phases
    3. Define complementary observables from suffix/prefix
    4. Prove uncertainty from topological discontinuity
============================================================================ -/

/-! ============================================================================
    PART VII: SUPERPOSITION - COMPLEX AMPLITUDES ON STATES

    A superposition assigns a complex amplitude to each basis state.
    This is the standard quantum mechanical structure.

    MATHEMATICAL FACT: The space of amplitudes is ℂ^(2^k) at depth k.
============================================================================ -/

/-- A superposition at depth k assigns a complex amplitude to each state -/
def Superposition (k : ℕ) := QuantumState k → ℂ

/-- The zero superposition (vacuum) -/
def zeroSuperposition (k : ℕ) : Superposition k := fun _ => 0

/-- A basis state: amplitude 1 at state s, 0 elsewhere -/
def basisState (k : ℕ) (s : QuantumState k) : Superposition k :=
  fun t => if t = s then 1 else 0

/-- Addition of superpositions -/
def addSuperposition (k : ℕ) (ψ φ : Superposition k) : Superposition k :=
  fun s => ψ s + φ s

/-- Scalar multiplication of superposition -/
def scaleSuperposition (k : ℕ) (c : ℂ) (ψ : Superposition k) : Superposition k :=
  fun s => c * ψ s

instance (k : ℕ) : Add (Superposition k) := ⟨addSuperposition k⟩
instance (k : ℕ) : SMul ℂ (Superposition k) := ⟨scaleSuperposition k⟩

/-- THEOREM: Basis state has amplitude 1 at its own state -/
theorem basisState_self (k : ℕ) (s : QuantumState k) :
    basisState k s s = 1 := by simp [basisState]

/-- THEOREM: Basis state has amplitude 0 at other states -/
theorem basisState_other (k : ℕ) (s t : QuantumState k) (h : s ≠ t) :
    basisState k s t = 0 := by simp [basisState, Ne.symm h]

/-! ============================================================================
    PART VIII: INNER PRODUCT AND NORMALIZATION

    The inner product ⟨ψ|φ⟩ = Σ_s ψ(s)* × φ(s)
    Norm squared: ‖ψ‖² = ⟨ψ|ψ⟩ = Σ_s |ψ(s)|²
============================================================================ -/

/-- Inner product of two superpositions -/
noncomputable def innerProduct (k : ℕ) (ψ φ : Superposition k) : ℂ :=
  ∑ s : QuantumState k, (starRingEnd ℂ (ψ s)) * (φ s)

/-- Norm squared of a superposition -/
noncomputable def normSq (k : ℕ) (ψ : Superposition k) : ℂ :=
  innerProduct k ψ ψ

/-- THEOREM: Inner product of basis states is Kronecker delta -/
theorem innerProduct_basis (k : ℕ) (s t : QuantumState k) :
    innerProduct k (basisState k s) (basisState k t) = if s = t then 1 else 0 := by
  simp only [innerProduct, basisState]
  by_cases hst : s = t
  · subst hst
    simp only [ite_true]
    have h : ∑ u : QuantumState k, (starRingEnd ℂ (if u = s then 1 else 0)) * (if u = s then 1 else 0)
           = ∑ u : QuantumState k, if u = s then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases hus : u = s <;> simp [hus]
    rw [h, Finset.sum_ite_eq' Finset.univ s (fun _ => (1 : ℂ))]
    simp
  · simp only [hst, ite_false]
    apply Finset.sum_eq_zero
    intro u _
    by_cases hus : u = s
    · by_cases hut : u = t
      · exfalso; exact hst (hus.symm.trans hut)
      · simp only [hus, ite_true, map_one, one_mul, hst, ite_false]
    · simp only [hus, ite_false, map_zero, zero_mul]

/-- THEOREM: Basis states are orthonormal -/
theorem basis_orthonormal (k : ℕ) (s t : QuantumState k) :
    innerProduct k (basisState k s) (basisState k t) = if s = t then 1 else 0 :=
  innerProduct_basis k s t

/-- THEOREM: Norm squared of basis state is 1 -/
theorem normSq_basis (k : ℕ) (s : QuantumState k) :
    normSq k (basisState k s) = 1 := by
  simp only [normSq, innerProduct_basis, if_true]

/-- THEOREM: Norm squared of zero superposition is 0 -/
theorem normSq_zero (k : ℕ) : normSq k (zeroSuperposition k) = 0 := by
  simp only [normSq, innerProduct, zeroSuperposition, map_zero, zero_mul,
             Finset.sum_const_zero]

/-! ============================================================================
    PART IX: SUPERPOSITION PRINCIPLE

    Any superposition can be written as a sum of basis states.
    ψ = Σ_s ψ(s) × |s⟩
============================================================================ -/

/-- THEOREM: Superposition decomposes into basis states -/
theorem superposition_decomposition (k : ℕ) (ψ : Superposition k) :
    ψ = fun t => ∑ s : QuantumState k, ψ s * (basisState k s t) := by
  funext t
  simp only [basisState]
  have h : ∑ s : QuantumState k, ψ s * (if t = s then 1 else 0)
         = ∑ s : QuantumState k, if s = t then ψ s else 0 := by
    apply Finset.sum_congr rfl
    intro s _
    by_cases hst : s = t
    · simp [hst]
    · have hts : t ≠ s := fun h => hst h.symm
      simp [hst, hts]
  rw [h, Finset.sum_ite_eq' Finset.univ t]
  simp

/-- THEOREM: Completeness - sum of projectors is identity
    Σ_s |s⟩⟨s| = I, meaning Σ_s (basisState s)(t) × conj((basisState s)(u)) = δ_{tu} -/
theorem completeness (k : ℕ) (t u : QuantumState k) :
    ∑ s : QuantumState k, (basisState k s t) * (starRingEnd ℂ (basisState k s u))
    = if t = u then 1 else 0 := by
  simp only [basisState]
  by_cases htu : t = u
  · subst htu
    have h : ∑ s : QuantumState k, (if t = s then 1 else 0) * (starRingEnd ℂ (if t = s then 1 else 0))
           = ∑ s : QuantumState k, if s = t then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      by_cases hst : s = t
      · simp [hst]
      · have hts : t ≠ s := fun h => hst h.symm
        simp [hst, hts]
    rw [h, Finset.sum_ite_eq' Finset.univ t]
    simp
  · simp only [htu, ite_false]
    apply Finset.sum_eq_zero
    intro s _
    by_cases hst : s = t
    · have hut : u ≠ t := fun h => htu h.symm
      have hut' : ¬(u = t) := hut
      simp only [hst, ite_true, one_mul, hut', ite_false, map_zero]
    · have hts : ¬(t = s) := fun h => hst h.symm
      simp only [hts, ite_false, zero_mul]

/-! ============================================================================
    PART X: PROBABILITY FROM AMPLITUDE

    Born rule: P(s) = |ψ(s)|²
    This is not derived - it's a physical postulate.
    But we can prove it's consistent with normalization.
============================================================================ -/

/-- Probability of measuring state s (Born rule - postulate) -/
noncomputable def probability (k : ℕ) (ψ : Superposition k) (s : QuantumState k) : ℝ :=
  Complex.normSq (ψ s)

/-- THEOREM: Probability is non-negative -/
theorem probability_nonneg (k : ℕ) (ψ : Superposition k) (s : QuantumState k) :
    0 ≤ probability k ψ s :=
  Complex.normSq_nonneg (ψ s)

/-- THEOREM: Probability of basis state at its own state is 1 -/
theorem probability_basis_self (k : ℕ) (s : QuantumState k) :
    probability k (basisState k s) s = 1 := by
  simp [probability, basisState, Complex.normSq_one]

/-- THEOREM: Probability of basis state at other state is 0 -/
theorem probability_basis_other (k : ℕ) (s t : QuantumState k) (h : s ≠ t) :
    probability k (basisState k s) t = 0 := by
  simp [probability, basisState, Ne.symm h]

/-- Total probability (should equal normSq for normalized states) -/
noncomputable def totalProbability (k : ℕ) (ψ : Superposition k) : ℝ :=
  ∑ s : QuantumState k, probability k ψ s

/-- THEOREM: Total probability of basis state is 1 -/
theorem totalProbability_basis (k : ℕ) (s : QuantumState k) :
    totalProbability k (basisState k s) = 1 := by
  simp only [totalProbability, probability, basisState]
  have h : ∑ t : QuantumState k, Complex.normSq (if t = s then 1 else 0)
         = ∑ t : QuantumState k, if t = s then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro t _
    by_cases hts : t = s <;> simp [hts, Complex.normSq_one, Complex.normSq_zero]
  rw [h, Finset.sum_ite_eq' Finset.univ s]
  simp

/-! ============================================================================
    PART XI: SUMMARY - QUANTUM MECHANICS FOUNDATION

    PROVEN MATHEMATICAL FACTS (Parts VII-X):
    1. basisState_self/other: Basis states are indicator functions
    2. basis_orthonormal: ⟨s|t⟩ = δ_{st}
    3. normSq_basis: ‖|s⟩‖² = 1
    4. superposition_decomposition: ψ = Σ ψ(s)|s⟩
    5. completeness: Σ |s⟩⟨s| = I
    6. probability_nonneg: P(s) ≥ 0
    7. totalProbability_basis: Σ P(s) = 1 for basis states

    PHYSICAL POSTULATES (clearly marked):
    - Born rule: P(s) = |ψ(s)|² (definition, not derived)
    - Normalization: ‖ψ‖² = 1 for physical states (convention)

    WHAT WE HAVE:
    - Complete orthonormal basis at each depth k
    - Superposition principle (linearity)
    - Probability interpretation (Born rule)
    - Completeness relation

    THIS IS STANDARD QUANTUM MECHANICS on a finite-dimensional Hilbert space ℂ^(2^k).
============================================================================ -/

/-! ============================================================================
    PART XII: INTERFERENCE - THE CORE QUANTUM PHENOMENON

    Interference arises from superposition of amplitudes.
    When two paths contribute to the same outcome, amplitudes ADD (not probabilities).
    This leads to constructive (amplitudes in phase) or destructive (out of phase) interference.

    MATHEMATICAL FACT: |a + b|² ≠ |a|² + |b|² in general.
    The cross terms 2·Re(a*b) are the interference terms.
============================================================================ -/

/-- Two-path superposition: equal amplitude on two states -/
noncomputable def twoPathSuperposition (k : ℕ) (s t : QuantumState k)
    (phase_s phase_t : ℂ) : Superposition k :=
  fun u => if u = s then phase_s else if u = t then phase_t else 0

/-- THEOREM: Two-path superposition is zero outside the two paths -/
theorem twoPath_outside (k : ℕ) (s t u : QuantumState k)
    (hs : u ≠ s) (ht : u ≠ t) (ps pt : ℂ) :
    twoPathSuperposition k s t ps pt u = 0 := by
  simp [twoPathSuperposition, hs, ht]

/-- THEOREM: Two-path superposition at first path -/
theorem twoPath_at_s (k : ℕ) (s t : QuantumState k) (ps pt : ℂ) :
    twoPathSuperposition k s t ps pt s = ps := by
  simp [twoPathSuperposition]

/-- THEOREM: Two-path superposition at second path (when s ≠ t) -/
theorem twoPath_at_t (k : ℕ) (s t : QuantumState k) (hst : s ≠ t) (ps pt : ℂ) :
    twoPathSuperposition k s t ps pt t = pt := by
  simp [twoPathSuperposition, hst.symm]

/-- Equal superposition: both amplitudes are 1/√2 -/
noncomputable def equalSuperposition (k : ℕ) (s t : QuantumState k) : Superposition k :=
  twoPathSuperposition k s t (1 / Real.sqrt 2) (1 / Real.sqrt 2)

/-- Opposite phase superposition: amplitudes are 1/√2 and -1/√2 -/
noncomputable def oppositeSuperposition (k : ℕ) (s t : QuantumState k) : Superposition k :=
  twoPathSuperposition k s t (1 / Real.sqrt 2) (-1 / Real.sqrt 2)

/-! ============================================================================
    PART XIII: INTERFERENCE FORMULA

    The key equation: |a + b|² = |a|² + |b|² + 2·Re(a*·b)

    The term 2·Re(a*·b) is the INTERFERENCE TERM.
    - When a and b have the same phase: interference is POSITIVE (constructive)
    - When a and b have opposite phase: interference is NEGATIVE (destructive)
============================================================================ -/

/-- THEOREM: Norm squared expansion with interference term
    Uses the identity: |a+b|² = |a|² + |b|² + 2·Re(āb) -/
theorem normSq_sum (a b : ℂ) :
    Complex.normSq (a + b) = Complex.normSq a + Complex.normSq b +
                             2 * (a * starRingEnd ℂ b).re :=
  Complex.normSq_add a b

/-- THEOREM: For real positive amplitudes, interference is constructive
    |a + b|² = (a+b)² > a² + b² = |a|² + |b|² when a,b > 0 -/
theorem interference_constructive (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a + b)^2 > a^2 + b^2 := by nlinarith

/-- THEOREM: For opposite sign real amplitudes, interference is destructive
    |a - b|² = (a-b)² < a² + b² = |a|² + |b|² when a,b > 0 -/
theorem interference_destructive (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a - b)^2 < a^2 + b^2 := by nlinarith

/-- THEOREM: Perfect destructive interference - equal and opposite cancel -/
theorem perfect_destructive (a : ℂ) :
    Complex.normSq (a + (-a)) = 0 := by
  simp [Complex.normSq_eq_zero]

/-- THEOREM: Perfect constructive interference - same amplitude doubles
    |2a|² = 4|a|² -/
theorem perfect_constructive (a : ℂ) :
    Complex.normSq (a + a) = 4 * Complex.normSq a := by
  have h : a + a = 2 * a := by ring
  rw [h, Complex.normSq_mul]
  simp only [Complex.normSq_ofNat]
  ring

/-! ============================================================================
    PART XIV: PROBABILITY WITH INTERFERENCE

    When measuring a superposition, the probability at each state
    includes interference effects from the amplitude sum.
============================================================================ -/

/-- Probability of outcome for a superposition (Born rule applied) -/
noncomputable def outcomeProb (k : ℕ) (ψ : Superposition k) (s : QuantumState k) : ℝ :=
  Complex.normSq (ψ s)

/-- THEOREM: Outcome probability equals amplitude squared -/
theorem outcomeProb_eq_normSq (k : ℕ) (ψ : Superposition k) (s : QuantumState k) :
    outcomeProb k ψ s = Complex.normSq (ψ s) := rfl

/-- THEOREM: Basis state has probability 1 at its position -/
theorem outcomeProb_basis_self (k : ℕ) (s : QuantumState k) :
    outcomeProb k (basisState k s) s = 1 := by
  simp [outcomeProb, basisState, Complex.normSq_one]

/-- THEOREM: Probability is non-negative -/
theorem outcomeProb_nonneg (k : ℕ) (ψ : Superposition k) (s : QuantumState k) :
    0 ≤ outcomeProb k ψ s :=
  Complex.normSq_nonneg _

/-! ============================================================================
    PART XV: SUMMARY - INTERFERENCE IS REAL MATHEMATICS

    PROVEN FACTS:
    1. normSq_sum: |a+b|² = |a|² + |b|² + 2·Re(a*b)
    2. interference_constructive: same-sign reals give |a+b|² > |a|² + |b|²
    3. interference_destructive: opposite-sign reals give |a+b|² < |a|² + |b|²
    4. perfect_destructive: a + (-a) = 0, so |a + (-a)|² = 0
    5. perfect_constructive: |a + a|² = 4|a|²

    WHAT THIS MEANS:
    - Amplitudes add, not probabilities
    - Phases matter: same phase → constructive, opposite → destructive
    - This is pure linear algebra, not speculation

    WHY THIS IS QUANTUM:
    In classical probability: P(A or B) = P(A) + P(B) for disjoint events
    In quantum mechanics: P = |ψ_A + ψ_B|² ≠ |ψ_A|² + |ψ_B|² in general

    The interference term 2·Re(ψ_A* ψ_B) is the quantum signature.
============================================================================ -/

end SPBiTopology.Quantum
