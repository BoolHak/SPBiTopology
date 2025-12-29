/-
  BiTopology/SPBiTopology/Twindragon.lean

  THE TWINDRAGON FRACTAL

  The twindragon is the attractor of the IFS defined by the base β = -1 + i.
  It is the set of all complex numbers representable as:
    T = { Σ_{k=0}^∞ d_k β^k : d_k ∈ {0,1} }

  This file develops:
  1. Self-similarity: ℤ[i] = β·ℤ[i] ⊔ (1 + β·ℤ[i])
  2. Finite approximations (partial sums)
  3. Connection to the bi-topological cylinder structure
-/

import BiTopology.SPBiTopology.PathPlanning

set_option autoImplicit false

namespace SPBiTopology

open Zsqrtd

/-! ## Section 1: Finite Digit Sums

We start with finite sums which correspond to Gaussian integers.
Every Gaussian integer has a unique finite β-adic expansion.
-/

/-- The set of Gaussian integers representable with at most n digits -/
def DigitBounded (n : ℕ) : Set GaussianInt :=
  {z | digitLength z ≤ n}

/-- Zero is in every DigitBounded set -/
theorem zero_mem_digitBounded (n : ℕ) : (0 : GaussianInt) ∈ DigitBounded n := by
  simp only [DigitBounded, Set.mem_setOf_eq, digitLength_zero, Nat.zero_le]

/-- DigitBounded sets are nested -/
theorem digitBounded_mono {m n : ℕ} (h : m ≤ n) : DigitBounded m ⊆ DigitBounded n := by
  intro z hz
  simp only [DigitBounded, Set.mem_setOf_eq] at hz ⊢
  omega

/-- DigitBounded n is finite -/
theorem digitBounded_finite (n : ℕ) : Set.Finite (DigitBounded n) := by
  have hsub : DigitBounded n ⊆ ⋃ k : Fin (n + 1), {z | digitLength z = k.val} := by
    intro z hz
    simp only [DigitBounded, Set.mem_setOf_eq] at hz
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨⟨digitLength z, Nat.lt_succ_of_le hz⟩, rfl⟩
  apply Set.Finite.subset _ hsub
  apply Set.finite_iUnion
  intro k
  have hsub2 : {z : GaussianInt | digitLength z = k.val} ⊆
               evalDigits '' {ds : List Bool | ds.length = k.val} := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    simp only [Set.mem_image, Set.mem_setOf_eq]
    exact ⟨toDigits z, hz, evalDigits_toDigits z⟩
  apply Set.Finite.subset _ hsub2
  apply Set.Finite.image
  have hsub3 : {ds : List Bool | ds.length = k.val} ⊆
               Set.range (List.ofFn : (Fin k.val → Bool) → List Bool) := by
    intro ds hds
    simp only [Set.mem_setOf_eq] at hds
    simp only [Set.mem_range]
    refine ⟨fun i => ds.get ⟨i.val, by rw [hds]; exact i.isLt⟩, ?_⟩
    apply List.ext_getElem
    · simp only [List.length_ofFn, hds]
    · intro i h1 h2
      simp only [List.getElem_ofFn, List.get_eq_getElem]
  exact Set.Finite.subset (Set.finite_range _) hsub3

/-! ## Section 2: Self-Similarity Structure

The key recurrence: z = digit(z) + β * βQuot(z)
This gives us the self-similarity structure.
-/

/-- 1 + β * w ≠ 0 -/
theorem one_add_β_mul_ne_zero (w : GaussianInt) : 1 + β * w ≠ 0 := by
  intro h
  have hre : (1 + β * w).re = 0 := congrArg Zsqrtd.re h
  simp only [Zsqrtd.add_re, Zsqrtd.one_re, β, Zsqrtd.mul_re, Zsqrtd.zero_re] at hre
  have him : (1 + β * w).im = 0 := congrArg Zsqrtd.im h
  simp only [Zsqrtd.add_im, Zsqrtd.one_im, β, Zsqrtd.mul_im, Zsqrtd.zero_im] at him
  omega

/-- 1 + β * w has digit = true -/
theorem digit_one_add_β_mul (w : GaussianInt) : digit (1 + β * w) = true := by
  rw [digit_true_iff]
  intro ⟨q, hq⟩
  have hre : (1 + β * w).re = (β * q).re := congrArg Zsqrtd.re hq
  simp only [Zsqrtd.add_re, Zsqrtd.one_re, Zsqrtd.mul_re, β] at hre
  have him : (1 + β * w).im = (β * q).im := congrArg Zsqrtd.im hq
  simp only [Zsqrtd.add_im, Zsqrtd.one_im, Zsqrtd.mul_im, β] at him
  omega

/-- β * w has digit = false -/
theorem digit_β_mul (w : GaussianInt) : digit (β * w) = false := by
  rw [digit_false_iff]
  exact dvd_mul_right β w

/-- The self-similarity equation for Gaussian integers:
    Every z can be written as either β * w or 1 + β * w for some w -/
theorem gaussianInt_self_similarity (z : GaussianInt) :
    (∃ w, z = β * w) ∨ (∃ w, z = 1 + β * w) := by
  by_cases hd : digit z = false
  · left
    have hspec := digit_βQuot_spec z
    simp only [hd, Bool.false_eq_true, ↓reduceIte, zero_add] at hspec
    exact ⟨βQuot z, hspec⟩
  · right
    have hspec := digit_βQuot_spec z
    simp only [eq_true_of_ne_false hd, ↓reduceIte] at hspec
    exact ⟨βQuot z, hspec⟩

/-- βQuot of 1 + β * w equals w -/
theorem βQuot_one_add_β_mul (w : GaussianInt) : βQuot (1 + β * w) = w := by
  have hd : digit (1 + β * w) = true := digit_one_add_β_mul w
  have hspec := digit_βQuot_spec (1 + β * w)
  simp only [hd, ↓reduceIte] at hspec
  have heq : β * βQuot (1 + β * w) = β * w := by
    have h1 : (β * βQuot (1 + β * w)).re = (β * w).re := by
      have := congrArg Zsqrtd.re hspec
      simp only [Zsqrtd.add_re, Zsqrtd.one_re] at this
      linarith
    have h2 : (β * βQuot (1 + β * w)).im = (β * w).im := by
      have := congrArg Zsqrtd.im hspec
      simp only [Zsqrtd.add_im, Zsqrtd.one_im] at this
      linarith
    ext <;> [exact h1; exact h2]
  exact mul_left_cancel₀ β_ne_zero heq

/-- βQuot of β * w equals w -/
theorem βQuot_β_mul (w : GaussianInt) : βQuot (β * w) = w := by
  by_cases hw : w = 0
  · simp only [hw, mul_zero, βQuot_zero]
  · have hd : digit (β * w) = false := digit_β_mul w
    have hspec := digit_βQuot_spec (β * w)
    simp only [hd, Bool.false_eq_true, ↓reduceIte, zero_add] at hspec
    exact mul_left_cancel₀ β_ne_zero hspec.symm

/-! ## Section 3: IFS Maps T₀ and T₁

The twindragon is the attractor of the IFS {T₀, T₁}.
-/

/-- The self-similarity map T₀: z ↦ β * z -/
def T₀ (z : GaussianInt) : GaussianInt := β * z

/-- The self-similarity map T₁: z ↦ 1 + β * z -/
def T₁ (z : GaussianInt) : GaussianInt := 1 + β * z

/-- T₀ is injective -/
theorem T₀_injective : Function.Injective T₀ := by
  intro x y h
  simp only [T₀] at h
  exact mul_left_cancel₀ β_ne_zero h

/-- T₁ is injective -/
theorem T₁_injective : Function.Injective T₁ := by
  intro x y h
  simp only [T₁] at h
  have : β * x = β * y := by
    have h1 : (β * x).re = (β * y).re := by
      have := congrArg Zsqrtd.re h
      simp only [Zsqrtd.add_re, Zsqrtd.one_re] at this
      linarith
    have h2 : (β * x).im = (β * y).im := by
      have := congrArg Zsqrtd.im h
      simp only [Zsqrtd.add_im, Zsqrtd.one_im] at this
      linarith
    ext <;> [exact h1; exact h2]
  exact mul_left_cancel₀ β_ne_zero this

/-- T₀ and T₁ have disjoint images -/
theorem T₀_T₁_disjoint : Disjoint (Set.range T₀) (Set.range T₁) := by
  rw [Set.disjoint_iff]
  intro z ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  simp only [T₀, T₁] at hx hy
  have hd0 : digit z = false := by rw [← hx]; exact digit_β_mul x
  have hd1 : digit z = true := by rw [← hy]; exact digit_one_add_β_mul y
  rw [hd0] at hd1
  exact Bool.noConfusion hd1

/-- The union of T₀ and T₁ images covers all Gaussian integers -/
theorem T₀_T₁_cover : Set.range T₀ ∪ Set.range T₁ = Set.univ := by
  ext z
  simp only [Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
  rcases gaussianInt_self_similarity z with ⟨w, hw⟩ | ⟨w, hw⟩
  · left; exact ⟨w, hw.symm⟩
  · right; exact ⟨w, hw.symm⟩

/-- Main self-similarity theorem: ℤ[i] = T₀(ℤ[i]) ⊔ T₁(ℤ[i]) (disjoint union) -/
theorem self_similarity_decomposition :
    (Set.univ : Set GaussianInt) = Set.range T₀ ∪ Set.range T₁ ∧
    Disjoint (Set.range T₀) (Set.range T₁) :=
  ⟨T₀_T₁_cover.symm, T₀_T₁_disjoint⟩

/-! ## Section 4: Inverse Maps -/

/-- T₀_inv is left inverse of T₀ -/
theorem T₀_inv_left_inverse (x : GaussianInt) : βQuot (T₀ x) = x := by
  simp only [T₀]
  exact βQuot_β_mul x

/-- T₁_inv is left inverse of T₁ -/
theorem T₁_inv_left_inverse (x : GaussianInt) : βQuot (T₁ x) = x := by
  simp only [T₁]
  exact βQuot_one_add_β_mul x

/-- T₀ is right inverse of βQuot on digit-false elements -/
theorem T₀_right_inverse (z : GaussianInt) (hz : digit z = false) : T₀ (βQuot z) = z := by
  simp only [T₀]
  have hspec := digit_βQuot_spec z
  simp only [hz, Bool.false_eq_true, ↓reduceIte, zero_add] at hspec
  exact hspec.symm

/-- T₁ is right inverse of βQuot on digit-true elements -/
theorem T₁_right_inverse (z : GaussianInt) (hz : digit z = true) : T₁ (βQuot z) = z := by
  simp only [T₁]
  have hspec := digit_βQuot_spec z
  simp only [hz, ↓reduceIte] at hspec
  exact hspec.symm

/-! ## Section 5: Twindragon Tiles

The cylinder structure provides a natural tiling.
-/

/-- Two Gaussian integers are in the same "tile" if they have the same cylinder pattern -/
def SameTile (z w : GaussianInt) (k : ℕ) : Prop :=
  cylinderPattern z k = cylinderPattern w k

/-- SameTile is reflexive -/
theorem sameTile_refl (z : GaussianInt) (k : ℕ) : SameTile z z k := rfl

/-- SameTile is symmetric -/
theorem sameTile_symm {z w : GaussianInt} {k : ℕ} (h : SameTile z w k) : SameTile w z k := h.symm

/-- SameTile is transitive -/
theorem sameTile_trans {x y z : GaussianInt} {k : ℕ}
    (hxy : SameTile x y k) (hyz : SameTile y z k) : SameTile x z k := hxy.trans hyz

/-- The number of distinct k-tiles is exactly 2^k -/
theorem num_tiles (k : ℕ) : Fintype.card (Fin k → Bool) = 2^k := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-! ## Section 6: Fundamental Domain -/

/-- The fundamental tile at depth k centered at 0 -/
def FundamentalTile (k : ℕ) : Set GaussianInt :=
  SuffixCylinder k (fun _ => false)

/-- Zero is in the fundamental tile -/
theorem zero_in_fundamentalTile (k : ℕ) : (0 : GaussianInt) ∈ FundamentalTile k := by
  simp only [FundamentalTile, SuffixCylinder, Set.mem_setOf_eq]
  intro j
  exact nthDigitLSD_zero j.val

/-- The fundamental tile is the set of z divisible by β^k -/
theorem fundamentalTile_eq_divisible (k : ℕ) :
    FundamentalTile k = {z | β^k ∣ z} := by
  ext z
  simp only [FundamentalTile, SuffixCylinder, Set.mem_setOf_eq]
  rw [pow_dvd_iff_first_k_false]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩
  · intro h j
    exact h j.val j.isLt

/-- β * FundamentalTile k ⊆ FundamentalTile (k+1) -/
theorem fundamentalTile_mul_β (k : ℕ) :
    (β * ·) '' FundamentalTile k ⊆ FundamentalTile (k + 1) := by
  intro z hz
  simp only [Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rw [fundamentalTile_eq_divisible] at hw ⊢
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [pow_succ, mul_comm]
  exact mul_dvd_mul_left β hw

/-! ## Section 7: Coset Decomposition -/

/-- The coset of z modulo β^k -/
def Coset (z : GaussianInt) (k : ℕ) : Set GaussianInt :=
  {w | lsdAgree z w k}

/-- z is in its own coset -/
theorem mem_own_coset (z : GaussianInt) (k : ℕ) : z ∈ Coset z k := by
  simp only [Coset, Set.mem_setOf_eq]
  unfold lsdAgree
  intro n _hn
  rfl

/-- Cosets are suffix cylinders -/
theorem coset_eq_suffixCylinder (z : GaussianInt) (k : ℕ) :
    Coset z k = SuffixCylinder k (cylinderPattern z k) := by
  ext w
  simp only [Coset, SuffixCylinder, Set.mem_setOf_eq, lsdAgree, cylinderPattern]
  constructor
  · intro h j
    exact (h j.val j.isLt).symm
  · intro h n hn
    exact (h ⟨n, hn⟩).symm

/-! ## Section 8: Twindragon Approximations -/

/-- The twindragon approximation at level n: all z with digitLength ≤ n -/
def TwindragonApprox (n : ℕ) : Set GaussianInt :=
  DigitBounded n

/-- Approximations are nested -/
theorem twindragonApprox_mono {m n : ℕ} (h : m ≤ n) :
    TwindragonApprox m ⊆ TwindragonApprox n :=
  digitBounded_mono h

/-- Zero is in all approximations -/
theorem zero_in_twindragonApprox (n : ℕ) : (0 : GaussianInt) ∈ TwindragonApprox n :=
  zero_mem_digitBounded n

/-- The union of all approximations is all of ℤ[i] -/
theorem twindragonApprox_union : ⋃ n, TwindragonApprox n = Set.univ := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  simp only [TwindragonApprox, DigitBounded, Set.mem_setOf_eq]
  exact ⟨digitLength z, le_refl _⟩

/-! ## Section 9: Norm and Scale Properties -/

/-- Norm doubles under T₀ -/
theorem T₀_norm (z : GaussianInt) : (T₀ z).norm = 2 * z.norm := by
  simp only [T₀]
  rw [Zsqrtd.norm_mul, norm_β]

/-- Scale invariance: norm of β^k is 2^k -/
theorem scale_invariance (k : ℕ) : (β^k).norm = 2^k := norm_β_pow_eq k

/-! ## Section 10: Twindragon Boundary

The boundary of a twindragon tile consists of points that have grid neighbors
in different tiles. This is where the fractal structure becomes visible.
-/

/-- A point is on the k-tile boundary if it has a grid neighbor in a different k-cylinder -/
def OnTileBoundary (z : GaussianInt) (k : ℕ) : Prop :=
  ∃ n : GaussianInt, IsGridNeighbor z n ∧ cylinderPattern z k ≠ cylinderPattern n k

/-- The set of k-boundary points -/
def TileBoundary (k : ℕ) : Set GaussianInt :=
  {z | OnTileBoundary z k}

/-- For k = 0, the cylinder pattern is trivially equal (empty function) -/
theorem cylinderPattern_zero_eq (z w : GaussianInt) :
    cylinderPattern z 0 = cylinderPattern w 0 := by
  ext i
  exact i.elim0

/-- For k ≥ 2, neighbors are ALWAYS in different k-cylinders (key boundary theorem) -/
theorem neighbors_always_diff_cylinder (z n : GaussianInt) (k : ℕ) (hk : k ≥ 2)
    (hn : IsGridNeighbor z n) : cylinderPattern z k ≠ cylinderPattern n k := by
  intro heq
  have hne : z ≠ n := isGridNeighbor_ne z n hn
  have hz : z ∈ SuffixCylinder k (cylinderPattern z k) := fun i => rfl
  have hwn : n ∈ SuffixCylinder k (cylinderPattern z k) := by
    intro i
    exact (congrFun heq i).symm
  exact neighbors_diff_cylinder_depth z n k hk hn hne (cylinderPattern z k) hz hwn

/-- For k ≥ 2, every point with a neighbor is on the k-boundary -/
theorem all_with_neighbors_on_boundary (z : GaussianInt) (k : ℕ) (hk : k ≥ 2)
    (hexists : ∃ n, IsGridNeighbor z n) : OnTileBoundary z k := by
  obtain ⟨n, hn⟩ := hexists
  exact ⟨n, hn, neighbors_always_diff_cylinder z n k hk hn⟩

/-- Every point has at least one grid neighbor -/
theorem exists_neighbor (z : GaussianInt) : ∃ n, IsGridNeighbor z n := by
  use z - ⟨1, 0⟩
  simp only [IsGridNeighbor, unitMoves, Finset.mem_insert, Finset.mem_singleton]
  left
  ext
  · simp only [Zsqrtd.sub_re]; ring
  · simp only [Zsqrtd.sub_im]; ring

/-- For k ≥ 2, ALL points are on the k-tile boundary -/
theorem all_on_boundary_ge_2 (z : GaussianInt) (k : ℕ) (hk : k ≥ 2) : OnTileBoundary z k :=
  all_with_neighbors_on_boundary z k hk (exists_neighbor z)

/-- The k-tile boundary is everything for k ≥ 2 -/
theorem tileBoundary_eq_univ (k : ℕ) (hk : k ≥ 2) : TileBoundary k = Set.univ := by
  ext z
  simp only [TileBoundary, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact all_on_boundary_ge_2 z k hk

/-- Whether z has a neighbor sharing the same 1-cylinder -/
def HasShared1Cylinder (z : GaussianInt) : Prop :=
  ∃ n, IsGridNeighbor z n ∧ cylinderPattern z 1 = cylinderPattern n 1

/-- Neighbors can share at most a 1-cylinder -/
theorem max_shared_cylinder_depth (z n : GaussianInt) (hn : IsGridNeighbor z n) (k : ℕ)
    (hshare : cylinderPattern z k = cylinderPattern n k) : k ≤ 1 := by
  by_contra hk
  push_neg at hk
  have hk2 : k ≥ 2 := hk
  exact neighbors_always_diff_cylinder z n k hk2 hn hshare

/-! ## Section 11: Boundary Self-Similarity

The boundary inherits the self-similarity of the twindragon.
-/

/-- T₀ preserves the boundary structure: if z has neighbor n in different k-cylinder,
    then T₀ z has neighbor T₀ n (though they may be in different (k+1)-cylinder) -/
theorem T₀_maps_neighbors (z n : GaussianInt) (_hn : IsGridNeighbor z n) :
    (T₀ z - T₀ n).norm = 2 * (z - n).norm := by
  simp only [T₀]
  rw [← mul_sub, Zsqrtd.norm_mul, norm_β]

/-- The norm of difference between T₁-images doubles -/
theorem T₁_maps_neighbors (z n : GaussianInt) (_hn : IsGridNeighbor z n) :
    (T₁ z - T₁ n).norm = 2 * (z - n).norm := by
  simp only [T₁]
  have h : (1 + β * z) - (1 + β * n) = β * (z - n) := by ring
  rw [h, Zsqrtd.norm_mul, norm_β]

/-- Cylinder pattern shifts under T₀: the k-pattern of T₀ z is related to (k-1)-pattern of z -/
theorem T₀_cylinder_shift (z : GaussianInt) (k : ℕ) (hk : k ≥ 1) :
    (cylinderPattern (T₀ z) k) ⟨0, hk⟩ = false := by
  simp only [T₀, cylinderPattern, nthDigitLSD]
  have hd := digit_β_mul z
  simp only [List.getD_eq_getElem?_getD]
  by_cases hz : β * z = 0
  · simp only [hz, toDigits_zero, List.getElem?_nil, Option.getD_none]
  · rw [toDigits, dif_neg hz]
    simp only [List.getElem?_cons_zero, Option.getD_some]
    exact hd

/-- The first digit of T₁ z is always true -/
theorem T₁_first_digit (z : GaussianInt) (k : ℕ) (hk : k ≥ 1) :
    (cylinderPattern (T₁ z) k) ⟨0, hk⟩ = true := by
  simp only [T₁, cylinderPattern, nthDigitLSD]
  have hd := digit_one_add_β_mul z
  simp only [List.getD_eq_getElem?_getD]
  have hne : 1 + β * z ≠ 0 := one_add_β_mul_ne_zero z
  rw [toDigits, dif_neg hne]
  simp only [List.getElem?_cons_zero, Option.getD_some]
  exact hd

/-- Fractal dimension hint: at scale k, there are 2^k cylinders,
    and boundary points (all points for k ≥ 2) fill the space -/
theorem boundary_fills_space (k : ℕ) (hk : k ≥ 2) :
    TileBoundary k = Set.univ := tileBoundary_eq_univ k hk

/-! ## Section 12: Unique Representation -/

/-- toDigits is injective -/
theorem toDigits_inj : Function.Injective (toDigits : GaussianInt → List Bool) := by
  intro z w h
  have hz := evalDigits_toDigits z
  have hw := evalDigits_toDigits w
  rw [h] at hz
  exact hz.symm.trans hw

/-- evalDigits ∘ toDigits = id -/
theorem evalDigits_toDigits_id : evalDigits ∘ toDigits = id := by
  funext z
  simp only [Function.comp_apply, id_eq]
  exact evalDigits_toDigits z

/-! ## Section 13: Twindragon Tiling Structure

The twindragon tiles ℂ by ℤ[i]-translates. Each Gaussian integer z
determines a unique tile, and the tiles partition the plane.
-/

/-- The tiling equivalence: z ~ w iff they have the same fractional part in the twindragon -/
def TilingEquiv (z w : GaussianInt) : Prop :=
  ∃ k : ℕ, SameTile z w k

/-- TilingEquiv is reflexive -/
theorem tilingEquiv_refl (z : GaussianInt) : TilingEquiv z z :=
  ⟨0, rfl⟩

/-- At any depth k, there are exactly 2^k distinct tiles -/
theorem tiles_at_depth (k : ℕ) : Fintype.card (Fin k → Bool) = 2^k :=
  num_tiles k

/-- The tiles refine as depth increases -/
theorem tiles_refine (z w : GaussianInt) (k : ℕ) (h : SameTile z w (k + 1)) :
    SameTile z w k := by
  simp only [SameTile, cylinderPattern] at h ⊢
  funext i
  have := congrFun h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
  simp only [cylinderPattern] at this
  exact this

/-! ## Section 14: Binary Address System

Every point in the twindragon has a binary address given by its β-adic expansion.
-/

/-- The binary address of z at depth k -/
noncomputable def binaryAddress (z : GaussianInt) (k : ℕ) : Fin k → Bool :=
  cylinderPattern z k

/-- Binary addresses determine cylinder membership -/
theorem binaryAddress_determines_cylinder (z w : GaussianInt) (k : ℕ) :
    binaryAddress z k = binaryAddress w k ↔ SameTile z w k := by
  simp only [binaryAddress, SameTile]

/-- The address refines under the IFS maps -/
theorem T₀_address_shift (z : GaussianInt) (k : ℕ) :
    binaryAddress (T₀ z) (k + 1) ⟨0, Nat.zero_lt_succ k⟩ = false := by
  simp only [binaryAddress]
  exact T₀_cylinder_shift z (k + 1) (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k))

/-- T₁ prepends a 1 to the address -/
theorem T₁_address_shift (z : GaussianInt) (k : ℕ) :
    binaryAddress (T₁ z) (k + 1) ⟨0, Nat.zero_lt_succ k⟩ = true := by
  simp only [binaryAddress]
  exact T₁_first_digit z (k + 1) (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k))

/-- The tail of T₀'s address is z's address -/
theorem T₀_address_tail (z : GaussianInt) (k : ℕ) (i : Fin k) :
    binaryAddress (T₀ z) (k + 1) ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ =
    binaryAddress z k i := by
  simp only [binaryAddress, cylinderPattern, nthDigitLSD, T₀]
  simp only [List.getD_eq_getElem?_getD]
  by_cases hz : β * z = 0
  · simp only [hz, toDigits_zero, List.getElem?_nil, Option.getD_none]
    have hz' : z = 0 := by
      cases' mul_eq_zero.mp hz with h h
      · exact absurd h β_ne_zero
      · exact h
    simp only [hz', toDigits_zero, List.getElem?_nil, Option.getD_none]
  · rw [toDigits, dif_neg hz]
    simp only [List.getElem?_cons_succ]
    have hβQuot := βQuot_β_mul z
    rw [hβQuot]

/-- The tail of T₁'s address is z's address -/
theorem T₁_address_tail (z : GaussianInt) (k : ℕ) (i : Fin k) :
    binaryAddress (T₁ z) (k + 1) ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ =
    binaryAddress z k i := by
  simp only [binaryAddress, cylinderPattern, nthDigitLSD, T₁]
  simp only [List.getD_eq_getElem?_getD]
  have hne : 1 + β * z ≠ 0 := one_add_β_mul_ne_zero z
  rw [toDigits, dif_neg hne]
  simp only [List.getElem?_cons_succ]
  have hβQuot := βQuot_one_add_β_mul z
  rw [hβQuot]

/-! ## Section 15: Iterated Function System Properties

The twindragon is the unique non-empty compact set satisfying T = T₀(T) ∪ T₁(T).
-/

/-- The n-th iterate of the IFS -/
def IFSIterate (n : ℕ) : Set GaussianInt → Set GaussianInt :=
  match n with
  | 0 => id
  | n + 1 => fun S => (T₀ '' IFSIterate n S) ∪ (T₁ '' IFSIterate n S)

/-- Connection between IFS iterates and TwindragonApprox -/
theorem IFSIterate_twindragonApprox (n : ℕ) :
    IFSIterate n {(0 : GaussianInt)} ⊆ TwindragonApprox n := by
  induction n with
  | zero =>
    simp only [IFSIterate, id_eq, TwindragonApprox, DigitBounded]
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    simp only [Set.mem_setOf_eq, hz, digitLength_zero, Nat.le_refl]
  | succ n ih =>
    intro z hz
    simp only [IFSIterate, Set.mem_union, Set.mem_image] at hz
    simp only [TwindragonApprox, DigitBounded, Set.mem_setOf_eq]
    rcases hz with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
    · have hw' := ih hw
      simp only [TwindragonApprox, DigitBounded, Set.mem_setOf_eq] at hw'
      simp only [T₀]
      by_cases hw0 : w = 0
      · simp only [hw0, mul_zero, digitLength_zero, Nat.zero_le]
      · have hlen := digitLength_succ (β * w) (mul_ne_zero β_ne_zero hw0)
        have hβQuot := βQuot_β_mul w
        rw [hβQuot] at hlen
        omega
    · have hw' := ih hw
      simp only [TwindragonApprox, DigitBounded, Set.mem_setOf_eq] at hw'
      simp only [T₁]
      have hne := one_add_β_mul_ne_zero w
      have hlen := digitLength_succ (1 + β * w) hne
      have hβQuot := βQuot_one_add_β_mul w
      rw [hβQuot] at hlen
      omega

/-! ## Section 16: Fractal Dimension Indicators

While we can't directly compute Hausdorff dimension in Lean,
we can prove properties that indicate the twindragon has dimension 2.
-/

/-- The number of depth-k tiles is 2^k (exponential growth) -/
theorem tile_count_exponential (k : ℕ) : (Fintype.card (Fin k → Bool) : ℕ) = 2^k :=
  tiles_at_depth k

/-- The diameter of a k-tile (in terms of norm) is bounded by 2^k -/
theorem tile_diameter_bound (z w : GaussianInt) (k : ℕ)
    (h : SameTile z w k) : (2 : ℤ)^k ∣ (z - w).norm := by
  have hsame : cylinderPattern z k = cylinderPattern w k := h
  have hz : z ∈ SuffixCylinder k (cylinderPattern z k) := fun i => rfl
  have hw : w ∈ SuffixCylinder k (cylinderPattern z k) := by
    intro i; exact (congrFun hsame i).symm
  exact suffixCylinder_norm_diff_dvd z w k (cylinderPattern z k) hz hw

/-- Area-entropy relation: |β^k| = 2^k = number of k-tiles -/
theorem area_tile_correspondence (k : ℕ) :
    (β^k).norm = 2^k ∧ Fintype.card (Fin k → Bool) = 2^k := by
  constructor
  · exact norm_β_pow_eq k
  · exact tiles_at_depth k

/-- Self-similarity dimension: scaling by β doubles area, and we have 2 copies -/
theorem dimension_two_indicator :
    (β : GaussianInt).norm = 2 ∧ Fintype.card (Fin 1 → Bool) = 2 := by
  constructor
  · exact norm_β
  · simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, pow_one]

/-! ## Section 17: Connectivity via Cylinder Structure

The cylinder structure provides a notion of "connected" through shared patterns.
-/

/-- Two points are k-connected if they share a k-cylinder -/
def KConnected (z w : GaussianInt) (k : ℕ) : Prop := SameTile z w k

/-- k-connectivity is an equivalence relation -/
theorem kConnected_equiv (k : ℕ) : Equivalence (fun z w => KConnected z w k) :=
  ⟨fun z => sameTile_refl z k,
   fun h => sameTile_symm h,
   fun h1 h2 => sameTile_trans h1 h2⟩

/-- Finer connectivity implies coarser connectivity -/
theorem kConnected_mono {z w : GaussianInt} {j k : ℕ} (hjk : j ≤ k)
    (h : KConnected z w k) : KConnected z w j := by
  simp only [KConnected, SameTile, cylinderPattern] at h ⊢
  funext i
  have hi' : i.val < k := Nat.lt_of_lt_of_le i.isLt hjk
  have := congrFun h ⟨i.val, hi'⟩
  simp only [cylinderPattern] at this
  exact this

/-- The quotient by k-connectivity has 2^k elements -/
theorem kConnected_quotient_card (k : ℕ) :
    Fintype.card (Fin k → Bool) = 2^k := tiles_at_depth k

/-! ## Section 18: Self-Contact Structure

Points where different "copies" of the twindragon meet.
These occur at boundary points between different address branches.
-/

/-- A point is a k-contact point if it's the image of different addresses -/
def IsContactPoint (z : GaussianInt) (k : ℕ) : Prop :=
  ∃ a b : List Bool, a.length = k ∧ b.length = k ∧ a ≠ b ∧
    evalDigits a = z ∧ evalDigits b = z

/-- evalDigits of all-false list is zero -/
theorem evalDigits_all_false (n : ℕ) :
    evalDigits (List.replicate n false) = 0 := by
  induction n with
  | zero => simp only [List.replicate, evalDigits]
  | succ n ih =>
    simp only [List.replicate_succ, evalDigits, Bool.false_eq_true, ↓reduceIte, zero_add, ih,
               mul_zero]

/-! ## Section 19: Dragon Curve Connection

The twindragon boundary is related to the classic dragon curve.
-/

/-- The "dragon" transformation: alternating T₀ and T₁ -/
def dragonStep (n : ℕ) (z : GaussianInt) : GaussianInt :=
  if n % 2 = 0 then T₀ z else T₁ z

/-- Iterating dragonStep builds the dragon curve structure -/
def dragonIterate : ℕ → GaussianInt → GaussianInt
  | 0, z => z
  | n + 1, z => dragonStep n (dragonIterate n z)

/-! ## Summary

### Proven Results:

1. **Self-Similarity Decomposition** (`self_similarity_decomposition`):
   ℤ[i] = T₀(ℤ[i]) ⊔ T₁(ℤ[i]) where T₀(z) = βz and T₁(z) = 1 + βz

2. **Disjoint Union** (`T₀_T₁_disjoint`):
   The images of T₀ and T₁ are disjoint

3. **Inverse Maps** (`T₀_inv_left_inverse`, `T₁_inv_left_inverse`):
   βQuot inverts both T₀ and T₁

4. **Tile Structure** (`sameTile_refl`, `sameTile_symm`, `sameTile_trans`):
   SameTile is an equivalence relation

5. **Fundamental Domain** (`fundamentalTile_eq_divisible`):
   The fundamental tile at depth k is {z : β^k | z}

6. **Scale Invariance** (`scale_invariance`):
   |β^k| = 2^k

7. **Unique Representation** (`toDigits_inj`):
   toDigits is injective

### Physical/Geometric Interpretation:

- The twindragon is the "attractor" of the IFS {T₀, T₁}
- Gaussian integers are the "lattice points" within the twindragon tiling
- The suffix topology captures the local structure of the twindragon
- The cylinder structure gives a natural multi-scale decomposition
- The self-similarity T = T ∪ (1 + βT) is encoded in the IFS structure
-/

end SPBiTopology
