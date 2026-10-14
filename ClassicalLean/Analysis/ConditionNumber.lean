/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# The condition number bounds the relative error of a linear solve

If `A x = b` and `A x' = b'`, the relative change in the solution is at most the condition number
`‖A‖ ‖A⁻¹‖` times the relative change in the right-hand side:
`‖x' − x‖ / ‖x‖ ≤ ‖A‖ ‖A⁻¹‖ · ‖b' − b‖ / ‖b‖`.

* `norm_sub_div_le_cond` — for a continuous linear map `A` between normed spaces with a continuous
  left inverse `B` (`B (A x) = x`), with `‖A‖ ‖B‖` in place of the condition number.
* `norm_sub_div_le_cond_of_mulVec` — for an invertible square matrix over `ℝ` or `ℂ`, with
  Mathlib's `ℓ∞` operator norm on matrices (the largest absolute row sum) and the largest absolute
  entry on vectors.

`norm_sub_div_le_cond` is the order's name (`cond` for the condition number, not Lean's Boolean
`cond`); `norm_sub_div_le_cond_of_mulVec` is an added name for the matrix form.

Only the right-hand side is perturbed here; the textbook statements that also perturb `A` are not
stated. The idea is standard (for example Trefethen and Bau, Numerical Linear Algebra, Lecture 12;
cited for the idea, no theorem number checked).

Lean divides by `0` to get `0`: when `x = 0`, the left side is `0` and the bound holds trivially;
when `x ≠ 0`, `b ≠ 0` too, because `B b = x`.

## Hypotheses

Measured in order LEAN-20's checks (check C29, exact rationals): 396 invertible real matrices of
size up to `4` (a few with `x = 0`) and 299 tall matrices with the left inverse `(Aᵀ A)⁻¹ Aᵀ`.
Each hypothesis fails when dropped alone (computed in the checks, and in Lean in review r29):

* `B` a left inverse of `A`: `A = 1`, `B = 0` (size 1), `x = 1`, `x' = 2`: `1 > 0`.
* `A` invertible, in the matrix form: `A = 0` (size 1), whose Lean inverse is `0`; `x = 1`,
  `x' = 2`, `b = b' = 0`: `1 > 0`.
* `A x = b`: `A = 1`, `x = 1`, `b = 5`, `x' = b' = 2`: `1 > 3/5`.
* `A x' = b'`: `A = 1`, `x = b = 1`, `x' = 2`, `b' = 1`: `1 > 0`.

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-20, `grep -rniE` over Mathlib):
`condition.?number|condNum|cond_number` 0. Used: `ContinuousLinearMap.le_opNorm` and
`Matrix.linfty_opNorm_eq_opNorm`.
-/

open Matrix

namespace ClassicalLean.Analysis

/-- The arithmetic shared by both forms: from `dx ≤ nB db` and `nb ≤ nA nx`, with `nb ≠ 0`
whenever `nx ≠ 0`, `dx / nx ≤ nA nB (db / nb)`. -/
private theorem div_le_mul_mul_div {dx db nx nb nA nB : ℝ} (hdb : 0 ≤ db)
    (hnx : 0 ≤ nx) (hnb : 0 ≤ nb) (hnB : 0 ≤ nB) (h1 : dx ≤ nB * db) (h2 : nb ≤ nA * nx)
    (h3 : nx ≠ 0 → nb ≠ 0) : dx / nx ≤ nA * nB * (db / nb) := by
  rcases hnx.eq_or_lt with hx | hx
  · rw [← hx, div_zero]
    rcases hnb.eq_or_lt with hb | hb
    · rw [← hb, div_zero, mul_zero]
    · have hA : 0 ≤ nA := by
        by_contra hA
        push Not at hA
        nlinarith
      positivity
  · have hb : 0 < nb := lt_of_le_of_ne hnb (Ne.symm (h3 hx.ne'))
    rw [div_le_iff₀ hx]
    set r := db / nb
    have hr : 0 ≤ r := div_nonneg hdb hnb
    have hdb' : db = r * nb := by simp only [r]; field_simp
    rw [hdb'] at h1
    have : nB * r * nb ≤ nB * r * (nA * nx) := mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith

/-- **The condition number bound, for linear maps.** If `A` is a continuous linear map with a
continuous left inverse `B`, `A x = b` and `A x' = b'`, then
`‖x' − x‖ / ‖x‖ ≤ ‖A‖ ‖B‖ (‖b' − b‖ / ‖b‖)`: `x' − x = B (b' − b)` and `‖b‖ ≤ ‖A‖ ‖x‖`. -/
theorem norm_sub_div_le_cond {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (A : E →L[𝕜] F) (B : F →L[𝕜] E) (hBA : ∀ x, B (A x) = x) {x x' : E} {b b' : F}
    (hb : A x = b) (hb' : A x' = b') :
    ‖x' - x‖ / ‖x‖ ≤ ‖A‖ * ‖B‖ * (‖b' - b‖ / ‖b‖) := by
  have h1 : ‖x' - x‖ ≤ ‖B‖ * ‖b' - b‖ := by
    have : x' - x = B (b' - b) := by rw [map_sub, ← hb, ← hb', hBA, hBA]
    rw [this]
    exact B.le_opNorm _
  have h2 : ‖b‖ ≤ ‖A‖ * ‖x‖ := hb ▸ A.le_opNorm x
  refine div_le_mul_mul_div (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) h1 h2 fun hx hb0 ↦ hx ?_
  rw [norm_eq_zero] at hb0 ⊢
  rw [← hBA x, hb, hb0, map_zero]

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace in
/-- **The condition number bound, for matrices.** For an invertible square matrix `A` over `ℝ` or
`ℂ`, `A x = b` and `A x' = b'`: `‖x' − x‖ / ‖x‖ ≤ ‖A‖ ‖A⁻¹‖ (‖b' − b‖ / ‖b‖)`, with the `ℓ∞`
operator norm on matrices (largest absolute row sum) and the largest absolute entry on vectors.
Mathlib's `Matrix.linfty_opNorm_eq_opNorm` turns it into the linear-map form (review r29). -/
theorem norm_sub_div_le_cond_of_mulVec {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    [DecidableEq n] {A : Matrix n n 𝕜} (hA : IsUnit A.det) {x x' b b' : n → 𝕜}
    (hb : A *ᵥ x = b) (hb' : A *ᵥ x' = b') :
    ‖x' - x‖ / ‖x‖ ≤ ‖A‖ * ‖A⁻¹‖ * (‖b' - b‖ / ‖b‖) := by
  rw [Matrix.linfty_opNorm_eq_opNorm A, Matrix.linfty_opNorm_eq_opNorm A⁻¹]
  exact norm_sub_div_le_cond _ _
    (fun y ↦ by simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA]) hb hb'

end ClassicalLean.Analysis

/-- The hypotheses of `norm_sub_div_le_cond` hold together: on the plane `ℝ × ℝ`, `A = 2 • id`,
whose inverse `B = (1/2) • id` undoes it, and the points `x = (1, 0)`, `x' = (1, 1)` with images
`b = A x = (2, 0)` and `b' = A x' = (2, 2)`. -/
example := ClassicalLean.Analysis.norm_sub_div_le_cond (𝕜 := ℝ) (E := ℝ × ℝ) (F := ℝ × ℝ)
  (A := (2 : ℝ) • ContinuousLinearMap.id ℝ (ℝ × ℝ))
  (B := (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (ℝ × ℝ))
  (fun x ↦ by simp [smul_smul]) (x := (1, 0)) (x' := (1, 1)) (b := (2, 0)) (b' := (2, 2))
  (by simp) (by simp)
