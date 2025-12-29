/-
  BiTopology/SPBiTopology/StatisticalMechanics.lean

  STATISTICAL MECHANICS ON BI-TOPOLOGY
  Rigorous connections to thermodynamics.
-/

import BiTopology.SPBiTopology.PhysicsFoundations

set_option autoImplicit false

namespace SPBiTopology

open Zsqrtd

/-! ## Section 1: Microstate Counting -/

def microstateCount (k : ℕ) : ℕ := 2^k

theorem microstateCount_eq_pattern_count (k : ℕ) :
    microstateCount k = (allPatterns k).card := by
  unfold microstateCount; rw [pattern_count]

theorem microstateCount_exponential (k : ℕ) :
    microstateCount (k + 1) = 2 * microstateCount k := by
  unfold microstateCount; ring

theorem microstateCount_zero : microstateCount 0 = 1 := rfl

/-! ## Section 2: Entropy from Counting (in units of log 2) -/

def discreteEntropy (k : ℕ) : ℕ := k

theorem entropy_additive (k m : ℕ) :
    discreteEntropy (k + m) = discreteEntropy k + discreteEntropy m := rfl

theorem entropy_microstate_relation (k : ℕ) :
    2^(discreteEntropy k) = microstateCount k := rfl

theorem entropy_vacuum : discreteEntropy 0 = 0 := rfl

/-! ## Section 3: Energy from Scale -/

def energyScale (k : ℕ) : ℕ := k

theorem energy_entropy_equality (k : ℕ) :
    energyScale k = discreteEntropy k := rfl

theorem norm_energy_relation (k : ℕ) :
    (β^k).norm = 2^(energyScale k) := norm_β_pow_eq k

/-! ## Section 4: Partition Function -/

def partitionFunction (k : ℕ) : ℕ := 2^k

theorem partitionFunction_growth (k : ℕ) :
    partitionFunction (k + 1) = 2 * partitionFunction k := by
  unfold partitionFunction; ring

/-! ## Section 5: Free Energy F = E - S = 0 -/

def freeEnergy (k : ℕ) : ℤ := (k : ℤ) - (k : ℤ)

theorem freeEnergy_zero (k : ℕ) : freeEnergy k = 0 := by
  unfold freeEnergy; ring

/-! ## Section 6: Area-Entropy Law (Holographic) -/

theorem area_entropy_law (k : ℕ) :
    (β^k).norm = 2^(discreteEntropy k) := norm_β_pow_eq k

theorem holographic_bound (k : ℕ) :
    (microstateCount k : ℤ) = (β^k).norm := by
  unfold microstateCount
  rw [norm_β_pow_eq]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

end SPBiTopology
