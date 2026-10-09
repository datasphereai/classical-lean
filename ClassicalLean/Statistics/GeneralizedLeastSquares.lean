/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Statistics.GaussMarkov

/-!
# Generalised least squares and Aitken's theorem

In the linear model `y = X β + ε` whose noise has covariance `σ² V` (not `σ² · 1`, as in
`Statistics/GaussMarkov`), a linear unbiased estimator `β̂ = C y` (`C * X = 1`) has covariance
`σ² · C V Cᵀ`. **Aitken's theorem** (1935) says the best one is generalised least squares,
`glsMatrix V X = (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹`, whose covariance factor is `(Xᵀ V⁻¹ X)⁻¹`. As in
`GaussMarkov`, everything is matrix algebra over `ℝ`; the covariance reading is the standard
one, not a theorem of this file.

* `glsMatrix V X` — the matrix `(Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹`; `glsMatrix_one`: at `V = 1` it is
  `leastSquares X`, with no hypothesis.
* `glsMatrix_mul_self` — it is unbiased, `glsMatrix V X * X = 1`, when `V` is positive definite
  and `Xᵀ X` is invertible.
* `glsMatrix_mul_mul_transpose` — its covariance factor is `(Xᵀ V⁻¹ X)⁻¹`, for every `V` and `X`:
  when `V` is invertible this is `A⁻¹ Aᵀ (Aᵀ)⁻¹` with `A = Xᵀ V⁻¹ X`, and when `V` or `A` is
  singular both sides are `0` under Mathlib's `⁻¹`.
* `posSemidef_mul_mul_transpose_sub_inv` — **Aitken's theorem**: for `V` positive semidefinite
  and every `C` with `C * X = 1`, `C V Cᵀ - (Xᵀ V⁻¹ X)⁻¹` is positive semidefinite. It is
  `D V Dᵀ` with `D = C - glsMatrix V X`, as `GaussMarkov`'s `self_mul_transpose_sub_inv_eq` is at
  `V = 1`. When `V` is singular, Mathlib's `V⁻¹ = 0` makes the subtracted matrix `0`, and the
  statement says only that `C V Cᵀ` is positive semidefinite, which is true.

## Hypotheses

Measured in order LEAN-18's checks (check C16, exact rationals): `glsMatrix 1 X = leastSquares X`
on 300 random `X`; unbiasedness on 217 cases; the covariance factor on 300 cases with `V`
singular, not symmetric or not definite; Aitken's theorem on 217 cases with `V` positive
semidefinite, singular ones included. Each hypothesis fails when dropped alone:

* Aitken, `V` positive semidefinite: `V = diag(1, -1)`, `X = (1, 1)ᵀ`, `C = (0, 1)` gives
  `Xᵀ V⁻¹ X = 0`, so the matrix is `C V Cᵀ = -1`.
* Aitken, `C * X = 1`: `V = X = 1`, `C = 0` gives `-1`.
* Unbiasedness, `V` positive definite: `V = 0` gives `glsMatrix V X = 0`; and an invertible `V`
  that is not definite is not enough, `V = diag(1, -1)`, `X = (1, 1)ᵀ` gives `0` too.
* Unbiasedness, `Xᵀ X` invertible: `X = 0`, `V = 1` gives `0`.

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-18, `grep -rniE` over Mathlib):
`aitken|generali[sz]ed least|weighted least|gls` 5 hits, none about least squares (the group
`GL`, a tactic's goal list); `best linear unbiased|BLUE|gauss.?markov` 9 hits, all the word
"blue". Mathlib has positive definite and semidefinite matrices (`Matrix.PosDef.inv`,
`Matrix.PosDef.conjTranspose_mul_mul_same`, `Matrix.PosSemidef.mul_mul_conjTranspose_same`,
`Matrix.PosDef.isUnit`), which this file uses.
-/

namespace ClassicalLean.Statistics

open Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The generalised least-squares matrix `(Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` for a design `X` and a noise
covariance `V`. When `V` or `Xᵀ V⁻¹ X` is singular, Mathlib's `⁻¹` is `0`, and so is this matrix. -/
noncomputable def glsMatrix (V : Matrix ι ι ℝ) (X : Matrix ι κ ℝ) : Matrix κ ι ℝ :=
  (Xᵀ * V⁻¹ * X)⁻¹ * Xᵀ * V⁻¹

/-- At `V = 1` generalised least squares is least squares. No hypothesis. -/
theorem glsMatrix_one (X : Matrix ι κ ℝ) : glsMatrix 1 X = leastSquares X := by
  simp [glsMatrix, leastSquares]

/-- **Generalised least squares is unbiased** when `V` is positive definite and `Xᵀ X` is
invertible: then `Xᵀ V⁻¹ X` is positive definite, so invertible. -/
theorem glsMatrix_mul_self {V : Matrix ι ι ℝ} (hV : V.PosDef) {X : Matrix ι κ ℝ}
    (hX : IsUnit (Xᵀ * X).det) : glsMatrix V X * X = 1 := by
  have hinj : Function.Injective X.mulVec := by
    intro u w h
    have h' : (Xᵀ * X) *ᵥ u = (Xᵀ * X) *ᵥ w := by rw [← mulVec_mulVec, h, mulVec_mulVec]
    exact mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr hX) h'
  have hA : (Xᵀ * V⁻¹ * X).PosDef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hV.inv.conjTranspose_mul_mul_same hinj
  calc glsMatrix V X * X = (Xᵀ * V⁻¹ * X)⁻¹ * (Xᵀ * V⁻¹ * X) := by
        simp only [glsMatrix, Matrix.mul_assoc]
    _ = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hA.isUnit)

/-- **The covariance factor of generalised least squares** is `(Xᵀ V⁻¹ X)⁻¹`, for every `V` and
`X`. When `V` or `Xᵀ V⁻¹ X` is singular, both sides are `0`. -/
theorem glsMatrix_mul_mul_transpose (V : Matrix ι ι ℝ) (X : Matrix ι κ ℝ) :
    glsMatrix V X * V * (glsMatrix V X)ᵀ = (Xᵀ * V⁻¹ * X)⁻¹ := by
  set A := Xᵀ * V⁻¹ * X with hA
  by_cases hV : IsUnit V.det
  · have hAt : Aᵀ = Xᵀ * V⁻¹ᵀ * X := by
      rw [hA, transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_assoc]
    have key : glsMatrix V X * V * (glsMatrix V X)ᵀ = A⁻¹ * (Aᵀ * A⁻¹ᵀ) := by
      rw [glsMatrix, ← hA, transpose_mul, transpose_mul, transpose_transpose, hAt]
      simp only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left V _ hV]
    rw [key]
    by_cases hdet : IsUnit A.det
    · rw [transpose_nonsing_inv, mul_nonsing_inv _ (by rwa [det_transpose]), Matrix.mul_one]
    · rw [nonsing_inv_apply_not_isUnit _ hdet, Matrix.zero_mul]
  · have hV0 : V⁻¹ = 0 := nonsing_inv_apply_not_isUnit _ hV
    have hA0 : A⁻¹ = 0 := by rw [hA, hV0, Matrix.mul_zero, Matrix.zero_mul, Matrix.inv_zero]
    rw [glsMatrix, ← hA, hA0]
    simp

/-- **Aitken's theorem.** For a noise covariance `V` that is positive semidefinite and any linear
unbiased estimator `C` (`C * X = 1`), `C V Cᵀ - (Xᵀ V⁻¹ X)⁻¹` is positive semidefinite: no linear
unbiased estimator has a smaller covariance than generalised least squares. When `V` is positive
definite, `glsMatrix V X` is itself unbiased (`glsMatrix_mul_self`); when `V` is singular,
Mathlib's `V⁻¹ = 0` and this says only that `C V Cᵀ` is positive semidefinite. -/
theorem posSemidef_mul_mul_transpose_sub_inv {V : Matrix ι ι ℝ} (hV : V.PosSemidef)
    {X : Matrix ι κ ℝ} {C : Matrix κ ι ℝ} (hC : C * X = 1) :
    (C * V * Cᵀ - (Xᵀ * V⁻¹ * X)⁻¹).PosSemidef := by
  set A := Xᵀ * V⁻¹ * X with hA
  have hpsd : ∀ D : Matrix κ ι ℝ, (D * V * Dᵀ).PosSemidef := fun D ↦ by
    simpa [conjTranspose_eq_transpose_of_trivial] using hV.mul_mul_conjTranspose_same D
  by_cases hVu : IsUnit V.det
  · have hVt : Vᵀ = V := by
      simpa [conjTranspose_eq_transpose_of_trivial] using hV.1.eq
    have hVit : V⁻¹ᵀ = V⁻¹ := by rw [transpose_nonsing_inv, hVt]
    have hAt : Aᵀ = A := by
      rw [hA, transpose_mul, transpose_mul, transpose_transpose, hVit, Matrix.mul_assoc]
    have hAit : A⁻¹ᵀ = A⁻¹ := by rw [transpose_nonsing_inv, hAt]
    set G := glsMatrix V X with hG
    have hGt : Gᵀ = V⁻¹ * X * A⁻¹ := by
      rw [hG, glsMatrix, ← hA, transpose_mul, transpose_mul, transpose_transpose, hVit, hAit,
        Matrix.mul_assoc]
    have hGG : G * V * Gᵀ = A⁻¹ := glsMatrix_mul_mul_transpose V X
    have hCG : C * V * Gᵀ = A⁻¹ := by
      rw [hGt]
      simp only [Matrix.mul_assoc]
      rw [mul_nonsing_inv_cancel_left V _ hVu, ← Matrix.mul_assoc, hC, Matrix.one_mul]
    have hGC : G * V * Cᵀ = A⁻¹ := by
      have := congrArg Matrix.transpose hCG
      rw [transpose_mul, transpose_mul, transpose_transpose, hVt, hAit, ← Matrix.mul_assoc] at this
      exact this
    have key : C * V * Cᵀ - A⁻¹ = (C - G) * V * (C - G)ᵀ := by
      simp only [transpose_sub, Matrix.sub_mul, Matrix.mul_sub, hCG, hGC, hGG]
      abel
    rw [key]
    exact hpsd _
  · have hV0 : V⁻¹ = 0 := nonsing_inv_apply_not_isUnit _ hVu
    have hA0 : A⁻¹ = 0 := by rw [hA, hV0, Matrix.mul_zero, Matrix.zero_mul, Matrix.inv_zero]
    rw [hA0, sub_zero]
    exact hpsd C

end ClassicalLean.Statistics
