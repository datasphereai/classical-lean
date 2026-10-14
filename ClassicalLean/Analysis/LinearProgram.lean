/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Linear programs: Farkas' lemma and strong duality

A *linear program* asks for the largest value of a linear function under linear inequalities.
Here the *primal* program is: maximise `c ⬝ᵥ x` subject to `A x ≤ b` and `x ≥ 0`; its *dual* is:
minimise `b ⬝ᵥ y` subject to `y A ≥ c` and `y ≥ 0` (all inequalities entry by entry, `A` a real
`m × n` matrix, `m` and `n` finite). The words used below mean exactly:

* *feasible*: a point is feasible when it meets the constraints (`PrimalFeasible A b x`,
  `DualFeasible A c y`); a program is feasible when it has a feasible point (`∃ x, …`);
* *bounded*: the set of values `{c ⬝ᵥ x | x feasible}` is bounded above (`BddAbove`), and for the
  dual `{b ⬝ᵥ y | y feasible}` is bounded below (`BddBelow`);
* *attained*: the set of values has a greatest (least) element (`IsGreatest`, `IsLeast`).

Results, order LEAN-23, item 47:

* `weak_duality` — every primal value is at most every dual value.
* `lp_strong_duality` — if both programs are feasible, there are feasible `x`, `y` with
  `c ⬝ᵥ x = b ⬝ᵥ y`; so (`isGreatest_primal_isLeast_dual`) both optima are attained and equal.
* `exists_dualFeasible` — a feasible primal that is bounded has a feasible dual;
  `exists_primalFeasible` is the mirror image. So (`isGreatest_primal_isLeast_dual_of_bddAbove`,
  the textbook form) a feasible, bounded primal has its optimum attained, equal to the dual
  optimum, also attained; `isGreatest_primal_isLeast_dual_of_bddBelow` starts from the dual.
* `farkas` — **Farkas' lemma**: for a linear map `L` between finite products of `ℝ`, `L x ≤ b` has
  a solution `x ≥ 0` exactly when every `y ≥ 0` with `y ⬝ᵥ L x ≥ 0` for all `x ≥ 0` has
  `y ⬝ᵥ b ≥ 0`.
* `isClosed_image_nonneg` — the image of the nonnegative orthant under such a linear map is
  closed; `exists_linearIndependent_of_nonneg` is Carathéodory's step for cones behind it.

The proof. *Closed image*: a nonnegative combination `∑ xⱼ vⱼ` of the columns `vⱼ` can be
rewritten with linearly independent columns only (if the columns in use are dependent, move along
a dependence until one coefficient reaches `0`); so the image is a finite union, over independent
sets of columns, of images of closed orthants under one-to-one linear maps, which are closed.
*Farkas*: if `b` is not in the closed convex cone `{L x + s | x ≥ 0, s ≥ 0}`, the Hahn–Banach
theorem separates it by a linear function, which must be `≤ 0` on the whole cone because the
cone is closed under positive scaling; its coefficients give `y`. *Strong duality*: Farkas'
lemma for the joint system `A x ≤ b`, `y A ≥ c`, `b ⬝ᵥ y ≤ c ⬝ᵥ x` in `(x, y)` (`dualitySystem`):
if it had no solution, the certificate `(u, v, t)` would either give, for `t > 0`, feasible
points `v/t`, `u/t` against weak duality, or, for `t = 0`, contradict the feasible points
assumed. *Bounded gives feasible*: Farkas' lemma for the dual constraints gives a direction `v ≥ 0`
with `A v ≤ 0` and `c ⬝ᵥ v > 0`, along which the primal value grows without bound.

## Hypotheses

Measured in order LEAN-23's checks (`checks.py`, exact rationals): on 200 random programs with
`m, n ≤ 3` made feasible on both sides, the primal maximum and the dual minimum, found by listing
vertices, are equal. The hypotheses are needed; each case below is an `example` at the end of this
file, checked by Lean (`A`, `b`, `c` of size `1`; review r47). For `lp_strong_duality`: without
primal feasibility, `A = (0)`, `b = (−1)`, `c = (0)` has a feasible dual and no feasible primal;
without dual feasibility, `A = (0)`, `b = (1)`, `c = (1)` has every `x ≥ 0` feasible and no dual
point. For `exists_dualFeasible`: primal feasibility is needed because the empty set is bounded
(`A = (0)`, `b = (−1)`, `c = (1)`: both programs infeasible); boundedness is needed
(`A = (0)`, `b = (1)`, `c = (1)`). For `weak_duality`, the signs in the definitions: without
`x ≥ 0`, `A = (1)`, `b = (1)`, `c = (−1)`, `x = −5`, `y = 0` give `c ⬝ᵥ x = 5 > 0 = b ⬝ᵥ y`;
without `y ≥ 0`, `A = (−1)`, `b = (1)`, `c = (0)`, `x = 0`, `y = −5` give `b ⬝ᵥ y = −5 < 0`.

Citations: Farkas 1902, "Theorie der einfachen Ungleichungen"; Gale, Kuhn and Tucker 1951,
"Linear programming and the theory of games". Neither was read for this file.

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-23, `grep -rniE` over Mathlib):
`linear program|strong duality|weak duality` 11 lines in 3 files: the TODO in
`Analysis/Convex/Cone/Basic.lean` (lines 35 to 37: define cone programs and linear programs and
prove weak, strong and LP duality) and `linarith`'s simplex oracle. `farkas` 14 lines in 4 files:
Farkas' lemma for a closed (proper) cone, `ProperCone.hyperplane_separation` and
`ProperCone.hyperplane_separation_of_notMem`, whose `K.map f` is the closure of the image; not
used, since here the cone's closedness is the point. No lemma states that a finitely generated
cone is closed: `IsClosed` in the cone folders concerns duals and proper cones, and the
Minkowski–Weyl theorem is named only in the docstring of `Geometry/Convex/Cone/DualFinite.lean`.
Main lemmas used: `geometric_hahn_banach_closed_point`, `LinearMap.isClosedEmbedding_of_injective`,
`linearIndependent_iff_injective_fintypeLinearCombination`, `Fintype.not_linearIndependent_iff`,
`LinearMap.pi_apply_eq_sum_univ`, `Set.Finite.isClosed_biUnion`, `dotProduct_mulVec`.
-/

open Matrix Finset

namespace ClassicalLean.LinearProgram

/-- **Carathéodory for cones.** A combination `∑ xⱼ vⱼ` with `x ≥ 0` and `x` zero off `s` is also
a combination `∑ yⱼ vⱼ` with `y ≥ 0` and `y` zero off some `t ⊆ s` whose vectors `vⱼ` are
linearly independent. -/
theorem exists_linearIndependent_of_nonneg {κ V : Type*} [Fintype κ]
    [AddCommGroup V] [Module ℝ V] (v : κ → V) (s : Finset κ) (x : κ → ℝ) (hx : 0 ≤ x)
    (hs : ∀ j ∉ s, x j = 0) :
    ∃ t ⊆ s, LinearIndependent ℝ (fun j : t ↦ v j) ∧
      ∃ y : κ → ℝ, 0 ≤ y ∧ (∀ j ∉ t, y j = 0) ∧ ∑ j, y j • v j = ∑ j, x j • v j := by
  classical
  induction s using Finset.strongInduction generalizing x with
  | H s ih =>
  by_cases hli : LinearIndependent ℝ (fun j : s ↦ v j)
  · exact ⟨s, subset_refl _, hli, x, hx, hs, rfl⟩
  obtain ⟨g, hg0, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hli
  set G : κ → ℝ := fun j ↦ if h : j ∈ s then g ⟨j, h⟩ else 0
  have hGs : ∀ j ∉ s, G j = 0 := fun j hj ↦ by simp [G, hj]
  have hG0 : ∑ j, G j • v j = 0 := by
    rw [← sum_subset (subset_univ s) (fun j _ hj ↦ by simp [hGs j hj]),
      ← sum_coe_sort s (fun j ↦ G j • v j)]
    simpa [G] using hg0
  -- a dependence with a positive entry
  obtain ⟨H, hH0, hHs, j₁, hj₁⟩ : ∃ H : κ → ℝ, ∑ j, H j • v j = 0 ∧ (∀ j ∉ s, H j = 0) ∧
      ∃ j, 0 < H j := by
    have hne : G i₀ ≠ 0 := by simpa [G] using hi₀
    rcases hne.lt_or_gt with h | h
    · refine ⟨-G, ?_, fun j hj ↦ by simp [hGs j hj], i₀, by simpa using h⟩
      simp only [Pi.neg_apply, neg_smul, sum_neg_distrib, hG0, neg_zero]
    · exact ⟨G, hG0, hGs, i₀, h⟩
  set P := univ.filter fun j ↦ 0 < H j
  obtain ⟨j₀, hj₀P, hmin⟩ := P.exists_min_image (fun j ↦ x j / H j) ⟨j₁, by simp [P, hj₁]⟩
  have hHj₀ : 0 < H j₀ := (mem_filter.mp hj₀P).2
  set τ := x j₀ / H j₀
  have hτ : 0 ≤ τ := div_nonneg (hx j₀) hHj₀.le
  set y : κ → ℝ := fun j ↦ x j - τ * H j
  have hy : 0 ≤ y := fun j ↦ by
    by_cases hj : 0 < H j
    · have h := hmin j (by simp [P, hj])
      rw [le_div_iff₀ hj] at h
      simp only [Pi.zero_apply, y]
      linarith
    · have h1 : τ * H j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hτ (not_lt.mp hj)
      have hxj : (0 : ℝ) ≤ x j := hx j
      simp only [Pi.zero_apply, y]
      linarith
  have hj₀s : j₀ ∈ s := by
    by_contra h
    exact hHj₀.ne' (hHs j₀ h)
  have hys : ∀ j ∉ s.erase j₀, y j = 0 := by
    intro j hj
    by_cases hjj : j = j₀
    · subst hjj
      simp only [y, τ]
      field_simp
      ring
    · have hjs : j ∉ s := fun h ↦ hj (mem_erase.mpr ⟨hjj, h⟩)
      simp [y, hs j hjs, hHs j hjs]
  have hsum : ∑ j, y j • v j = ∑ j, x j • v j := by
    simp only [y, sub_smul, sum_sub_distrib, mul_smul, ← smul_sum, hH0, smul_zero, sub_zero]
  obtain ⟨t, ht, hli', y', hy', hy's, hsum'⟩ := ih (s.erase j₀) (erase_ssubset hj₀s) y hy hys
  exact ⟨t, ht.trans (erase_subset _ _), hli', y', hy', hy's, hsum'.trans hsum⟩

variable {ι κ : Type*}

/-- The image of the nonnegative orthant under a linear map between finite products of `ℝ`
is closed. -/
theorem isClosed_image_nonneg [Finite ι] [Finite κ] (L : (κ → ℝ) →ₗ[ℝ] (ι → ℝ)) :
    IsClosed (L '' {x | 0 ≤ x}) := by
  classical
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  set v : κ → ι → ℝ := fun i ↦ L fun j ↦ if i = j then 1 else 0
  have hL (x : κ → ℝ) : L x = ∑ j, x j • v j := L.pi_apply_eq_sum_univ x
  have hconv (t : Finset κ) (x : κ → ℝ) (hx : ∀ j ∉ t, x j = 0) :
      ∑ j : t, x j • v j = ∑ j, x j • v j := by
    rw [sum_coe_sort t (fun j ↦ x j • v j)]
    exact sum_subset (subset_univ _) fun j _ hj ↦ by simp [hx j hj]
  set piece : Finset κ → Set (ι → ℝ) := fun t ↦
    Fintype.linearCombination ℝ (fun j : t ↦ v j) '' {y | 0 ≤ y}
  have heq : L '' {x | 0 ≤ x} =
      ⋃ t ∈ {t : Finset κ | LinearIndependent ℝ (fun j : t ↦ v j)}, piece t := by
    ext b
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop, piece]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨t, -, hli, y, hy, hyt, hsum⟩ :=
        exists_linearIndependent_of_nonneg v univ x hx (by simp)
      refine ⟨t, hli, fun j ↦ y j, fun j ↦ hy j, ?_⟩
      rw [Fintype.linearCombination_apply, hconv t y hyt, hsum, hL]
    · rintro ⟨t, -, y, hy, rfl⟩
      refine ⟨fun j ↦ if h : j ∈ t then y ⟨j, h⟩ else 0, fun j ↦ ?_, ?_⟩
      · by_cases h : j ∈ t
        · simpa [h] using hy ⟨j, h⟩
        · simp [h]
      · rw [hL, ← hconv t _ (fun j hj ↦ by simp [hj]), Fintype.linearCombination_apply]
        simp
  rw [heq]
  refine Set.Finite.isClosed_biUnion (Set.toFinite _) fun t ht ↦ ?_
  have hinj : LinearMap.ker (Fintype.linearCombination ℝ (fun j : t ↦ v j)) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (linearIndependent_iff_injective_fintypeLinearCombination.mp ht)
  exact (LinearMap.isClosedEmbedding_of_injective hinj).isClosedMap _
    (isClosed_le continuous_const continuous_id)

/-- A vector whose dot product with every `y ≥ 0` is `≥ 0` is itself `≥ 0`. -/
theorem nonneg_of_forall_dotProduct_nonneg [Fintype ι] {w : ι → ℝ}
    (h : ∀ y, 0 ≤ y → 0 ≤ w ⬝ᵥ y) : 0 ≤ w := fun i ↦ by
  classical
  simpa [dotProduct_single] using h (Pi.single i 1) (Pi.single_nonneg.mpr zero_le_one)

/-- **Farkas' lemma**, inequality form: `L x ≤ b` has a solution `x ≥ 0` exactly when every
`y ≥ 0` with `y ⬝ᵥ L x ≥ 0` for all `x ≥ 0` has `y ⬝ᵥ b ≥ 0`. -/
theorem farkas [Fintype ι] [Finite κ] (L : (κ → ℝ) →ₗ[ℝ] (ι → ℝ)) (b : ι → ℝ) :
    (∃ x, 0 ≤ x ∧ L x ≤ b) ↔ ∀ y, 0 ≤ y → (∀ x, 0 ≤ x → 0 ≤ y ⬝ᵥ L x) → 0 ≤ y ⬝ᵥ b := by
  classical
  constructor
  · rintro ⟨x, hx, hLx⟩ y hy hyL
    exact (hyL x hx).trans (dotProduct_le_dotProduct_of_nonneg_left hLx hy)
  intro h
  by_contra hno
  -- the cone `{L x + s | x ≥ 0, s ≥ 0}`, as the image of the orthant of `κ ⊕ ι`
  set M : ((κ ⊕ ι) → ℝ) →ₗ[ℝ] (ι → ℝ) :=
    L ∘ₗ LinearMap.funLeft ℝ ℝ Sum.inl + LinearMap.funLeft ℝ ℝ Sum.inr
  have hM (x : κ → ℝ) (s : ι → ℝ) : M (Sum.elim x s) = L x + s := by
    have h1 : LinearMap.funLeft ℝ ℝ Sum.inl (Sum.elim x s) = x := by
      ext j; simp [LinearMap.funLeft_apply]
    ext i; simp [M, h1, LinearMap.funLeft_apply]
  set C := M '' {z | 0 ≤ z}
  have hconv : Convex ℝ C := (convex_Ici (0 : (κ ⊕ ι) → ℝ)).linear_image M
  have hb : b ∉ C := by
    rintro ⟨z, hz, hMz⟩
    refine hno ⟨fun j ↦ z (Sum.inl j), fun j ↦ hz _, fun i ↦ ?_⟩
    have h1 := congrFun hMz i
    have h2 : (0 : ℝ) ≤ z (Sum.inr i) := hz _
    simp only [M, LinearMap.add_apply, LinearMap.comp_apply, Pi.add_apply,
      LinearMap.funLeft_apply] at h1
    have h3 : (L ∘ₗ LinearMap.funLeft ℝ ℝ Sum.inl) z = L fun j ↦ z (Sum.inl j) := rfl
    rw [LinearMap.comp_apply] at h3
    rw [h3] at h1
    linarith
  obtain ⟨f, u, hfC, hub⟩ := geometric_hahn_banach_closed_point hconv (isClosed_image_nonneg M) hb
  have hu : 0 < u := by simpa using hfC 0 ⟨0, Set.mem_ofPred.mpr le_rfl, map_zero M⟩
  have hcone (c : ι → ℝ) (hc : c ∈ C) : f c ≤ 0 := by
    by_contra hpos
    push Not at hpos
    obtain ⟨z, hz, rfl⟩ := hc
    have := hfC _ ⟨(u / f (M z)) • z,
      Set.mem_ofPred.mpr (smul_nonneg (div_nonneg hu.le hpos.le) hz), rfl⟩
    rw [map_smul, map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at this
    exact lt_irrefl _ this
  set y : ι → ℝ := fun i ↦ -f fun j ↦ if i = j then 1 else 0
  have hf (w : ι → ℝ) : f w = -(y ⬝ᵥ w) := by
    have := (f : (ι → ℝ) →ₗ[ℝ] ℝ).pi_apply_eq_sum_univ w
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    simp [this, y, dotProduct, mul_comm]
  have hy : 0 ≤ y := fun i ↦ by
    have := hcone (fun j ↦ if i = j then 1 else 0) ⟨Sum.elim 0 fun j ↦ if i = j then 1 else 0,
      fun s ↦ by cases s <;> simp; split_ifs <;> norm_num, by rw [hM]; simp⟩
    simp only [y, Pi.zero_apply]
    linarith
  have hyL (x : κ → ℝ) (hx : 0 ≤ x) : 0 ≤ y ⬝ᵥ L x := by
    have := hcone (L x) ⟨Sum.elim x 0, fun s ↦ by cases s with
      | inl j => exact hx j
      | inr i => simp, by rw [hM, add_zero]⟩
    rw [hf] at this
    linarith
  have := h y hy hyL
  rw [hf] at hub
  linarith

variable {m n : Type*} [Fintype m] [Fintype n]

/-- `x` is feasible for the primal program: maximise `c ⬝ᵥ x` subject to `A x ≤ b` and `x ≥ 0`. -/
def PrimalFeasible (A : Matrix m n ℝ) (b : m → ℝ) (x : n → ℝ) : Prop :=
  0 ≤ x ∧ A *ᵥ x ≤ b

/-- `y` is feasible for the dual program: minimise `b ⬝ᵥ y` subject to `y A ≥ c` and `y ≥ 0`. -/
def DualFeasible (A : Matrix m n ℝ) (c : n → ℝ) (y : m → ℝ) : Prop :=
  0 ≤ y ∧ c ≤ y ᵥ* A

/-- **Weak duality.** Every primal value is at most every dual value. -/
theorem weak_duality {A : Matrix m n ℝ} {b : m → ℝ} {c : n → ℝ} {x : n → ℝ} {y : m → ℝ}
    (hx : PrimalFeasible A b x) (hy : DualFeasible A c y) : c ⬝ᵥ x ≤ b ⬝ᵥ y :=
  calc c ⬝ᵥ x ≤ y ᵥ* A ⬝ᵥ x := dotProduct_le_dotProduct_of_nonneg_right hy.2 hx.1
    _ = y ⬝ᵥ A *ᵥ x := (dotProduct_mulVec y A x).symm
    _ ≤ y ⬝ᵥ b := dotProduct_le_dotProduct_of_nonneg_left hx.2 hy.1
    _ = b ⬝ᵥ y := dotProduct_comm _ _

/-- The system behind strong duality, in `z = (x, y)`: the rows `A x`, `−y A` and
`b ⬝ᵥ y − c ⬝ᵥ x`. -/
def dualitySystem (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) :
    ((n ⊕ m) → ℝ) →ₗ[ℝ] (((m ⊕ n) ⊕ Unit) → ℝ) where
  toFun z := Sum.elim (Sum.elim (A *ᵥ fun j ↦ z (Sum.inl j)) (-((fun i ↦ z (Sum.inr i)) ᵥ* A)))
    fun _ ↦ b ⬝ᵥ (fun i ↦ z (Sum.inr i)) - c ⬝ᵥ fun j ↦ z (Sum.inl j)
  map_add' z w := by
    have h1 : (fun j ↦ (z + w) (Sum.inl j)) = (fun j ↦ z (Sum.inl j)) + fun j ↦ w (Sum.inl j) :=
      rfl
    have h2 : (fun i ↦ (z + w) (Sum.inr i)) = (fun i ↦ z (Sum.inr i)) + fun i ↦ w (Sum.inr i) :=
      rfl
    rw [h1, h2]
    ext ((i | j) | u) <;> simp [mulVec_add, add_vecMul, dotProduct_add] <;> ring
  map_smul' r z := by
    have h1 : (fun j ↦ (r • z) (Sum.inl j)) = r • fun j ↦ z (Sum.inl j) := rfl
    have h2 : (fun i ↦ (r • z) (Sum.inr i)) = r • fun i ↦ z (Sum.inr i) := rfl
    rw [h1, h2]
    ext ((i | j) | u) <;> simp [mulVec_smul, smul_vecMul, dotProduct_smul]
    ring

/-- **Strong duality.** If both programs are feasible, there are feasible `x` and `y` with
`c ⬝ᵥ x = b ⬝ᵥ y`; by weak duality both are optimal. -/
theorem lp_strong_duality {A : Matrix m n ℝ} {b : m → ℝ} {c : n → ℝ}
    (hP : ∃ x, PrimalFeasible A b x) (hD : ∃ y, DualFeasible A c y) :
    ∃ x y, PrimalFeasible A b x ∧ DualFeasible A c y ∧ c ⬝ᵥ x = b ⬝ᵥ y := by
  classical
  obtain ⟨x₀, hx₀⟩ := hP
  obtain ⟨y₀, hy₀⟩ := hD
  by_cases hz : ∃ z, 0 ≤ z ∧ dualitySystem A b c z ≤ Sum.elim (Sum.elim b (-c)) 0
  · obtain ⟨z, hz0, hzL⟩ := hz
    have hx : PrimalFeasible A b fun j ↦ z (Sum.inl j) :=
      ⟨fun j ↦ hz0 _, fun i ↦ by simpa [dualitySystem] using hzL (Sum.inl (Sum.inl i))⟩
    have hy : DualFeasible A c fun i ↦ z (Sum.inr i) := by
      refine ⟨fun i ↦ hz0 _, fun j ↦ ?_⟩
      have := hzL (Sum.inl (Sum.inr j))
      simp [dualitySystem] at this
      linarith
    have hobj := hzL (Sum.inr ())
    simp [dualitySystem] at hobj
    exact ⟨_, _, hx, hy, le_antisymm (weak_duality hx hy) (by linarith)⟩
  exfalso
  have hf := (farkas (dualitySystem A b c) (Sum.elim (Sum.elim b (-c)) 0)).not.mp hz
  push Not at hf
  obtain ⟨w, hw0, hwL, hwb⟩ := hf
  set u : m → ℝ := fun i ↦ w (Sum.inl (Sum.inl i))
  set v : n → ℝ := fun j ↦ w (Sum.inl (Sum.inr j))
  set t := w (Sum.inr ())
  have hu : 0 ≤ u := fun i ↦ hw0 _
  have hv : 0 ≤ v := fun j ↦ hw0 _
  have ht : 0 ≤ t := hw0 _
  have hwz (x : n → ℝ) (y : m → ℝ) : w ⬝ᵥ dualitySystem A b c (Sum.elim x y) =
      u ⬝ᵥ A *ᵥ x - v ⬝ᵥ y ᵥ* A + t * (b ⬝ᵥ y - c ⬝ᵥ x) := by
    simp [dualitySystem, dotProduct, Fintype.sum_sum_type, u, v, t, Finset.sum_neg_distrib]
    ring
  have hwb' : w ⬝ᵥ Sum.elim (Sum.elim b (-c)) 0 = u ⬝ᵥ b - v ⬝ᵥ c := by
    simp [dotProduct, Fintype.sum_sum_type, u, v, Finset.sum_neg_distrib, mul_comm]
    ring
  rw [hwb'] at hwb
  -- from `z = (x, 0)`: `u A ≥ t c`; from `z = (0, y)`: `A v ≤ t b`
  have hI : 0 ≤ u ᵥ* A - t • c := nonneg_of_forall_dotProduct_nonneg fun x hx ↦ by
    have := hwL (Sum.elim x 0) (fun s ↦ by cases s with
      | inl j => exact hx j
      | inr i => simp)
    rw [hwz, dotProduct_mulVec] at this
    simp only [zero_vecMul, dotProduct_zero, sub_zero, zero_sub] at this
    simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    linarith
  have hII : 0 ≤ t • b - A *ᵥ v := nonneg_of_forall_dotProduct_nonneg fun y hy ↦ by
    have := hwL (Sum.elim 0 y) (fun s ↦ by cases s with
      | inl j => simp
      | inr i => exact hy i)
    rw [hwz, dotProduct_comm v, ← dotProduct_mulVec, dotProduct_comm b y] at this
    simp only [mulVec_zero, dotProduct_zero, sub_zero, zero_sub] at this
    simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm (A *ᵥ v) y,
      dotProduct_comm b y]
    linarith
  rcases ht.lt_or_eq with htpos | ht0
  · -- `t > 0`: `v / t` and `u / t` are feasible, and weak duality fails for them
    have hx : PrimalFeasible A b (t⁻¹ • v) := by
      refine ⟨smul_nonneg (inv_nonneg.mpr ht) hv, fun i ↦ ?_⟩
      have := hII i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, inv_mul_le_iff₀ htpos]
      linarith
    have hy : DualFeasible A c (t⁻¹ • u) := by
      refine ⟨smul_nonneg (inv_nonneg.mpr ht) hu, fun j ↦ ?_⟩
      have := hI j
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      rw [smul_vecMul, Pi.smul_apply, smul_eq_mul, le_inv_mul_iff₀ htpos]
      linarith
    have h := weak_duality hx hy
    rw [dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h
    have h' := le_of_mul_le_mul_left h (inv_pos.mpr htpos)
    rw [dotProduct_comm u b, dotProduct_comm v c] at hwb
    linarith
  · -- `t = 0`: `u A ≥ 0` and `A v ≤ 0`, so `u ⬝ᵥ b ≥ 0 ≥ v ⬝ᵥ c`
    rw [← ht0, zero_smul, sub_zero] at hI
    rw [← ht0, zero_smul, zero_sub] at hII
    have h1 : 0 ≤ u ⬝ᵥ b :=
      calc (0 : ℝ) ≤ u ᵥ* A ⬝ᵥ x₀ := dotProduct_nonneg_of_nonneg hI hx₀.1
        _ = u ⬝ᵥ A *ᵥ x₀ := (dotProduct_mulVec u A x₀).symm
        _ ≤ u ⬝ᵥ b := dotProduct_le_dotProduct_of_nonneg_left hx₀.2 hu
    have h2 : v ⬝ᵥ c ≤ 0 :=
      calc v ⬝ᵥ c ≤ v ⬝ᵥ y₀ ᵥ* A := dotProduct_le_dotProduct_of_nonneg_left hy₀.2 hv
        _ = y₀ ⬝ᵥ A *ᵥ v := by rw [dotProduct_comm, ← dotProduct_mulVec]
        _ ≤ 0 := by
          have := dotProduct_nonneg_of_nonneg hy₀.1 hII
          rw [dotProduct_neg] at this
          linarith
    linarith

/-- Both optima are attained and equal: when both programs are feasible, some value `v` is the
greatest primal value and the least dual value. -/
theorem isGreatest_primal_isLeast_dual {A : Matrix m n ℝ} {b : m → ℝ} {c : n → ℝ}
    (hP : ∃ x, PrimalFeasible A b x) (hD : ∃ y, DualFeasible A c y) :
    ∃ v, IsGreatest ((c ⬝ᵥ ·) '' {x | PrimalFeasible A b x}) v ∧
      IsLeast ((b ⬝ᵥ ·) '' {y | DualFeasible A c y}) v := by
  obtain ⟨x, y, hx, hy, hxy⟩ := lp_strong_duality hP hD
  refine ⟨c ⬝ᵥ x, ⟨⟨x, hx, rfl⟩, ?_⟩, ⟨⟨y, hy, hxy.symm⟩, ?_⟩⟩
  · rintro _ ⟨x', hx', rfl⟩
    rw [hxy]
    exact weak_duality hx' hy
  · rintro _ ⟨y', hy', rfl⟩
    exact weak_duality hx hy'

/-- A feasible primal whose values are bounded above has a feasible dual. -/
theorem exists_dualFeasible {A : Matrix m n ℝ} {b : m → ℝ} {c : n → ℝ}
    (hP : ∃ x, PrimalFeasible A b x)
    (hB : BddAbove ((c ⬝ᵥ ·) '' {x | PrimalFeasible A b x})) : ∃ y, DualFeasible A c y := by
  classical
  by_contra hno
  obtain ⟨x₀, hx₀⟩ := hP
  obtain ⟨M, hM⟩ := hB
  have hf : ¬∃ y, 0 ≤ y ∧ (-A.vecMulLinear) y ≤ -c := by
    rintro ⟨y, hy, hyc⟩
    refine hno ⟨y, hy, fun j ↦ ?_⟩
    have := hyc j
    simp at this
    linarith
  have := (farkas (-A.vecMulLinear) (-c)).not.mp hf
  push Not at this
  obtain ⟨v, hv, hvL, hvc⟩ := this
  -- `A v ≤ 0` and `c ⬝ᵥ v > 0`: moving along `v` stays feasible and raises the value forever
  have hAv : 0 ≤ -(A *ᵥ v) := nonneg_of_forall_dotProduct_nonneg fun y hy ↦ by
    have := hvL y hy
    simp only [LinearMap.neg_apply, Matrix.vecMulLinear_apply, dotProduct_neg] at this
    rw [dotProduct_comm v, ← dotProduct_mulVec] at this
    rwa [neg_dotProduct, dotProduct_comm]
  have hcv : 0 < c ⬝ᵥ v := by
    rw [dotProduct_neg, dotProduct_comm] at hvc
    linarith
  have hMx : c ⬝ᵥ x₀ ≤ M := hM ⟨x₀, hx₀, rfl⟩
  set s := (M - c ⬝ᵥ x₀) / (c ⬝ᵥ v) + 1
  have hs : 0 ≤ s := by positivity
  have hfeas : PrimalFeasible A b (x₀ + s • v) := by
    refine ⟨add_nonneg hx₀.1 (smul_nonneg hs hv), fun i ↦ ?_⟩
    have h1 := hx₀.2 i
    have h2 := hAv i
    simp only [Pi.neg_apply, Pi.zero_apply] at h2
    simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith
  have := hM ⟨_, hfeas, rfl⟩
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at this
  have : s * (c ⬝ᵥ v) = M - c ⬝ᵥ x₀ + c ⬝ᵥ v := by
    simp only [s]
    field_simp
  linarith

/-- A feasible dual whose values are bounded below has a feasible primal. -/
theorem exists_primalFeasible {A : Matrix m n ℝ} {b : m → ℝ} {c : n → ℝ}
    (hD : ∃ y, DualFeasible A c y)
    (hB : BddBelow ((b ⬝ᵥ ·) '' {y | DualFeasible A c y})) : ∃ x, PrimalFeasible A b x := by
  classical
  by_contra hno
  obtain ⟨y₀, hy₀⟩ := hD
  obtain ⟨M, hM⟩ := hB
  have hf : ¬∃ x, 0 ≤ x ∧ A.mulVecLin x ≤ b := by
    rintro ⟨x, hx, hxb⟩
    exact hno ⟨x, hx, hxb⟩
  have := (farkas A.mulVecLin b).not.mp hf
  push Not at this
  obtain ⟨u, hu, huL, hub⟩ := this
  -- `u A ≥ 0` and `b ⬝ᵥ u < 0`: moving along `u` stays feasible and lowers the value forever
  have huA : 0 ≤ u ᵥ* A := nonneg_of_forall_dotProduct_nonneg fun x hx ↦ by
    have := huL x hx
    rwa [Matrix.mulVecLin_apply, dotProduct_mulVec] at this
  have hbu : b ⬝ᵥ u < 0 := by rwa [dotProduct_comm]
  have hMy : M ≤ b ⬝ᵥ y₀ := hM ⟨y₀, hy₀, rfl⟩
  set s := (b ⬝ᵥ y₀ - M) / -(b ⬝ᵥ u) + 1
  have hs : 0 ≤ s := by
    have : 0 < -(b ⬝ᵥ u) := by linarith
    positivity
  have hfeas : DualFeasible A c (y₀ + s • u) := by
    refine ⟨add_nonneg hy₀.1 (smul_nonneg hs hu), fun j ↦ ?_⟩
    have h1 := hy₀.2 j
    have h2 := huA j
    simp only [Pi.zero_apply] at h2
    simp only [add_vecMul, smul_vecMul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith
  have := hM ⟨_, hfeas, rfl⟩
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at this
  have : s * (b ⬝ᵥ u) = -(b ⬝ᵥ y₀ - M) + b ⬝ᵥ u := by
    have : b ⬝ᵥ u ≠ 0 := hbu.ne
    simp only [s]
    field_simp
  linarith

/-- **Strong duality, textbook form.** A feasible primal whose values are bounded above has its
optimum attained, and it equals the dual optimum, also attained. -/
theorem isGreatest_primal_isLeast_dual_of_bddAbove {A : Matrix m n ℝ} {b : m → ℝ} {c : n → ℝ}
    (hP : ∃ x, PrimalFeasible A b x)
    (hB : BddAbove ((c ⬝ᵥ ·) '' {x | PrimalFeasible A b x})) :
    ∃ v, IsGreatest ((c ⬝ᵥ ·) '' {x | PrimalFeasible A b x}) v ∧
      IsLeast ((b ⬝ᵥ ·) '' {y | DualFeasible A c y}) v :=
  isGreatest_primal_isLeast_dual hP (exists_dualFeasible hP hB)

/-- The same from the dual side: a feasible dual whose values are bounded below. -/
theorem isGreatest_primal_isLeast_dual_of_bddBelow {A : Matrix m n ℝ} {b : m → ℝ} {c : n → ℝ}
    (hD : ∃ y, DualFeasible A c y)
    (hB : BddBelow ((b ⬝ᵥ ·) '' {y | DualFeasible A c y})) :
    ∃ v, IsGreatest ((c ⬝ᵥ ·) '' {x | PrimalFeasible A b x}) v ∧
      IsLeast ((b ⬝ᵥ ·) '' {y | DualFeasible A c y}) v :=
  isGreatest_primal_isLeast_dual (exists_primalFeasible hD hB) hD

/-! ### The hypotheses are needed (checked by Lean; review r47 wrote the first four) -/

/-- `lp_strong_duality` without primal feasibility: `A = (0)`, `b = (−1)`, `c = (0)`. -/
example : (∃ y, DualFeasible (0 : Matrix Unit Unit ℝ) 0 y) ∧
    ¬∃ x y, PrimalFeasible (0 : Matrix Unit Unit ℝ) (fun _ ↦ -1) x ∧
      DualFeasible (0 : Matrix Unit Unit ℝ) 0 y ∧
        (0 : Unit → ℝ) ⬝ᵥ x = (fun _ ↦ (-1 : ℝ)) ⬝ᵥ y := by
  refine ⟨⟨0, le_rfl, by simp⟩, ?_⟩
  rintro ⟨x, y, ⟨-, hx⟩, -⟩
  have := hx ()
  simp at this
  linarith

/-- `lp_strong_duality` without dual feasibility: `A = (0)`, `b = (1)`, `c = (1)`. -/
example : (∃ x, PrimalFeasible (0 : Matrix Unit Unit ℝ) 1 x) ∧
    ¬∃ x y, PrimalFeasible (0 : Matrix Unit Unit ℝ) 1 x ∧
      DualFeasible (0 : Matrix Unit Unit ℝ) 1 y ∧ (1 : Unit → ℝ) ⬝ᵥ x = 1 ⬝ᵥ y := by
  refine ⟨⟨0, le_rfl, fun _ ↦ by simp⟩, ?_⟩
  rintro ⟨x, y, -, ⟨-, hy⟩, -⟩
  have := hy ()
  simp at this
  linarith

/-- `exists_dualFeasible` without primal feasibility: the empty set of values is bounded above,
and there is no dual point (`A = (0)`, `b = (−1)`, `c = (1)`). -/
example : BddAbove (((1 : Unit → ℝ) ⬝ᵥ ·) ''
      {x | PrimalFeasible (0 : Matrix Unit Unit ℝ) (fun _ ↦ -1) x}) ∧
    ¬∃ y, DualFeasible (0 : Matrix Unit Unit ℝ) 1 y := by
  constructor
  · refine ⟨0, ?_⟩
    rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
    have := hx ()
    simp at this
    linarith
  · rintro ⟨y, -, hy⟩
    have := hy ()
    simp at this
    linarith

/-- `exists_dualFeasible` without boundedness: `A = (0)`, `b = (1)`, `c = (1)`. -/
example : (∃ x, PrimalFeasible (0 : Matrix Unit Unit ℝ) 1 x) ∧
    ¬∃ y, DualFeasible (0 : Matrix Unit Unit ℝ) 1 y :=
  ⟨⟨0, le_rfl, fun _ ↦ by simp⟩, by
    rintro ⟨y, -, hy⟩
    have := hy ()
    simp at this
    linarith⟩

/-- `weak_duality` without `x ≥ 0` in `PrimalFeasible`: `A = (1)`, `b = (1)`, `c = (−1)`,
`x = −5`, `y = 0`. -/
example : (1 : Matrix Unit Unit ℝ) *ᵥ (fun _ : Unit ↦ (-5 : ℝ)) ≤ 1 ∧
    DualFeasible (1 : Matrix Unit Unit ℝ) (fun _ ↦ -1) 0 ∧
    (1 : Unit → ℝ) ⬝ᵥ (0 : Unit → ℝ) < (fun _ : Unit ↦ (-1 : ℝ)) ⬝ᵥ (fun _ : Unit ↦ (-5 : ℝ)) := by
  refine ⟨fun _ ↦ by simp [mulVec, dotProduct]; norm_num, ⟨le_rfl, fun _ ↦ by simp⟩,
    by simp [dotProduct]⟩

/-- `weak_duality` without `y ≥ 0` in `DualFeasible`: `A = (−1)`, `b = (1)`, `c = (0)`, `x = 0`,
`y = −5`. -/
example : PrimalFeasible (-1 : Matrix Unit Unit ℝ) 1 0 ∧
    (0 : Unit → ℝ) ≤ (fun _ : Unit ↦ (-5 : ℝ)) ᵥ* (-1 : Matrix Unit Unit ℝ) ∧
    (1 : Unit → ℝ) ⬝ᵥ (fun _ : Unit ↦ (-5 : ℝ)) < (0 : Unit → ℝ) ⬝ᵥ (0 : Unit → ℝ) := by
  refine ⟨⟨le_rfl, fun _ ↦ by simp⟩, fun _ ↦ by simp [vecMul, dotProduct], by simp [dotProduct]⟩

end ClassicalLean.LinearProgram

open Matrix in
/-- The hypotheses of `lp_strong_duality` hold together: for the program with two variables and
two constraints, `A` with rows `(1, 1)` and `(1, −1)`, `b = (2, 1)`, `c = (1, 1)`, the point
`x = (1/2, 1/2)` is primal feasible (`x ≥ 0`, `A x = (1, 0) ≤ b`) and `y = (1, 0)` is dual feasible
(`y ≥ 0`, `y A = (1, 1) ≥ c`). -/
example := ClassicalLean.LinearProgram.lp_strong_duality (m := Fin 2) (n := Fin 2)
  (A := !![1, 1; 1, -1]) (b := ![2, 1]) (c := ![1, 1])
  ⟨![1 / 2, 1 / 2], fun i ↦ by fin_cases i <;> norm_num,
    fun i ↦ by fin_cases i <;> norm_num [mulVec, dotProduct, Fin.sum_univ_two]⟩
  ⟨![1, 0], fun i ↦ by fin_cases i <;> norm_num,
    fun j ↦ by fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_two]⟩
