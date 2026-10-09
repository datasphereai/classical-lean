/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Statistics.GaussMarkov
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The Frisch–Waugh–Lovell theorem

For a design matrix `X = [X₁ X₂]` (as `Matrix.fromCols`) over `ℝ` with invertible Gram matrix, the
least-squares coefficients on `X₂` equal those from regressing the `X₁`-residuals of `y` on the
`X₁`-residuals of `X₂`. Write `M₁ = residualMaker X₁ = 1 - X₁ (X₁ᵀ X₁)⁻¹ X₁ᵀ` for the residual maker
(the statistics "annihilator" matrix), over the library's `leastSquares` (`Statistics/GaussMarkov`).

## Main results

* `transpose_residualMaker`, `residualMaker_mul_self`: `M₁` is symmetric and idempotent (no
  hypothesis).
* `residualMaker_mul_eq_zero`: `M₁ X₁ = 0` when `X₁ᵀ X₁` is invertible.
* `trace_residualMaker`, `rank_residualMaker`: when `X₁ᵀ X₁` is invertible, `M₁` has trace and rank
  `n − p`, for `n` rows and `p` columns of `X₁` (order LEAN-17). Both need the invertibility: at
  `X₁ = [[0]]`, `M₁ = 1` has trace and rank `1`, not `0` (order LEAN-17's checks, line C1). The
  rank's `n − p` is a subtraction in `ℕ`; it does not truncate, because the hypothesis forces
  `p ≤ n`.
* `isUnit_det_transpose_mul_self_left`, `isUnit_det_transpose_mul_self_residualMaker`: if `Xᵀ X` is
  invertible, so are `X₁ᵀ X₁` and `(M₁ X₂)ᵀ (M₁ X₂)`.
* `toRows₂_leastSquares_fromCols`: the matrix form — the `X₂`-rows of `leastSquares [X₁ X₂]` are
  `leastSquares (M₁ X₂)`.
* `leastSquares_fromCols_mulVec_inr`, `leastSquares_fromCols_mulVec_inr'`: the `X₂`-coefficients of
  the regression of `y` on `[X₁ X₂]` are those of `M₁ y` on `M₁ X₂` (and of `y` on `M₁ X₂`).
* `residual_eq_residualMaker_sub`: the residuals agree.
* `not_forall_leastSquares_fromCols_mulVec_inr`: the invertibility hypothesis cannot be dropped.

## The proof

From the normal equations the library has (`leastSquares_mul_self`,
`transpose_mulVec_sub_mulVec_leastSquares`). Splitting `Xᵀ X β = Xᵀ y` into blocks
(`transpose_fromCols`, `fromRows_mul_fromCols`, `fromBlocks_mulVec`) gives, for the `inr` block,
`(M₁ X₂)ᵀ (M₁ X₂) β₂ = (M₁ X₂)ᵀ (M₁ y)`, whose Gram matrix is a unit by the Schur complement
(`det_fromBlocks₁₁`); cancelling it gives the theorem. `M₁` symmetric is `transpose_nonsing_inv`;
idempotent is by cases on `IsUnit (X₁ᵀ X₁).det`.
The trace is `n − trace (leastSquares X₁ * X₁) = n − p`, by `trace_mul_comm` and
`leastSquares_mul_self`; the rank equals the trace because `M₁` is idempotent (Mathlib's
`LinearMap.IsProj.trace`, through `LinearMap.isProj_range_iff_isIdempotentElem`).

## A remark, not proved here (order G-10 §0 row 9)

In all 109 of 2000 random exact trials where `Xᵀ X` is singular but `X₁ᵀ X₁` is a unit, both
sides of the `inr` identity were `0`, so `leastSquares_fromCols_mulVec_inr` plausibly holds under
the weaker `IsUnit (X₁ᵀ X₁).det` alone, by a rank argument. This is **[inferred, not proved]** and
is left for a later order.

## Searches (Mathlib v4.34.0, order G-10 §0 row 12)

`frisch`/`waugh`/`lovell`/partial regression have 0 hits; `least squares` 0; there is no
residual-maker or annihilator matrix in Mathlib. The block-matrix and Schur-complement lemmas used
are present (`ColumnRowPartitioned`, `SchurComplement`, `NonsingularInverse`). Prior art: none; the
route is derived here from the normal equations the library already has.
Searched again for order LEAN-17 (its plan, section 5): `degrees of freedom`, `residual.*variance`,
`unbiased.*variance` 0 hits; `IsIdempotentElem.*(rank|trace)` gives rank-one idempotents and
`IsIdempotentElem.trace_eq_zero_iff` only, so Mathlib has no "rank equals trace" for an idempotent
matrix.
-/

namespace ClassicalLean.Statistics

open Matrix

variable {ι κ₁ κ₂ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ₁] [Fintype κ₂] [DecidableEq κ₁]
  [DecidableEq κ₂]

/-- The residual maker of `X₁`: `M₁ = 1 − X₁ (X₁ᵀ X₁)⁻¹ X₁ᵀ`, which sends `y` to its residual after
regressing on `X₁`. -/
noncomputable def residualMaker (X₁ : Matrix ι κ₁ ℝ) : Matrix ι ι ℝ :=
  1 - X₁ * leastSquares X₁

/-- `M₁` is symmetric. -/
theorem transpose_residualMaker (X₁ : Matrix ι κ₁ ℝ) :
    (residualMaker X₁)ᵀ = residualMaker X₁ := by
  unfold residualMaker leastSquares
  simp only [transpose_sub, transpose_one, Matrix.transpose_mul, transpose_transpose,
    Matrix.transpose_nonsing_inv, Matrix.mul_assoc]

/-- `M₁` is idempotent. -/
theorem residualMaker_mul_self (X₁ : Matrix ι κ₁ ℝ) :
    residualMaker X₁ * residualMaker X₁ = residualMaker X₁ := by
  by_cases h : IsUnit (X₁ᵀ * X₁).det
  · unfold residualMaker
    have hls : leastSquares X₁ * X₁ = 1 := leastSquares_mul_self h
    have hAA : X₁ * leastSquares X₁ * (X₁ * leastSquares X₁) = X₁ * leastSquares X₁ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (leastSquares X₁) X₁, hls, Matrix.one_mul]
    have expand : (1 - X₁ * leastSquares X₁) * (1 - X₁ * leastSquares X₁)
        = 1 - X₁ * leastSquares X₁ - X₁ * leastSquares X₁
          + X₁ * leastSquares X₁ * (X₁ * leastSquares X₁) := by noncomm_ring
    rw [expand, hAA]; abel
  · unfold residualMaker
    rw [leastSquares_eq_zero_of_not_isUnit_det h, Matrix.mul_zero, sub_zero, Matrix.one_mul]

/-- `M₁ X₁ = 0`: the residual maker annihilates its own regressors. -/
theorem residualMaker_mul_eq_zero {X₁ : Matrix ι κ₁ ℝ} (h : IsUnit (X₁ᵀ * X₁).det) :
    residualMaker X₁ * X₁ = 0 := by
  unfold residualMaker
  have hls : leastSquares X₁ * X₁ = 1 := leastSquares_mul_self h
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hls, Matrix.mul_one, sub_self]

/-- **The trace of the residual maker** is `n − p`: `n` observations less `p` parameters, when
`X₁ᵀ X₁` is invertible. -/
theorem trace_residualMaker {X₁ : Matrix ι κ₁ ℝ} (h : IsUnit (X₁ᵀ * X₁).det) :
    (residualMaker X₁).trace = Fintype.card ι - Fintype.card κ₁ := by
  rw [residualMaker, trace_sub, trace_one, trace_mul_comm, leastSquares_mul_self h, trace_one]

/-- **The rank of the residual maker** is `n − p` when `X₁ᵀ X₁` is invertible: `M₁` is idempotent,
so its rank is its trace (Mathlib's `LinearMap.IsProj.trace`). -/
theorem rank_residualMaker {X₁ : Matrix ι κ₁ ℝ} (h : IsUnit (X₁ᵀ * X₁).det) :
    (residualMaker X₁).rank = Fintype.card ι - Fintype.card κ₁ := by
  set M := residualMaker X₁
  have hid : IsIdempotentElem M.mulVecLin := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, residualMaker_mul_self]
  have htr : ((M.rank : ℕ) : ℝ) = Fintype.card ι - Fintype.card κ₁ := by
    rw [← trace_residualMaker h, Matrix.rank,
      ← ((LinearMap.isProj_range_iff_isIdempotentElem _).mpr hid).trace]
    exact Matrix.trace_toLin'_eq M
  have hle : Fintype.card κ₁ ≤ Fintype.card ι := by
    have : (0 : ℝ) ≤ Fintype.card ι - Fintype.card κ₁ := htr ▸ Nat.cast_nonneg _
    exact_mod_cast sub_nonneg.mp this
  have : ((M.rank : ℕ) : ℝ) = ((Fintype.card ι - Fintype.card κ₁ : ℕ) : ℝ) := by
    rw [htr, Nat.cast_sub hle]
  exact_mod_cast this

omit [DecidableEq ι] in
/-- If `[X₁ X₂]` has invertible Gram matrix, so has `X₁`. -/
theorem isUnit_det_transpose_mul_self_left {X₁ : Matrix ι κ₁ ℝ} {X₂ : Matrix ι κ₂ ℝ}
    (h : IsUnit ((fromCols X₁ X₂)ᵀ * fromCols X₁ X₂).det) : IsUnit (X₁ᵀ * X₁).det := by
  have hGinj : Function.Injective ((fromCols X₁ X₂)ᵀ * fromCols X₁ X₂).mulVec :=
    mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr h)
  have hXinj : Function.Injective (fromCols X₁ X₂).mulVec := by
    intro u v huv
    apply hGinj
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, huv]
  have hX1inj : Function.Injective X₁.mulVec := by
    intro u v huv
    have hsum : (fromCols X₁ X₂) *ᵥ (Sum.elim u 0) = (fromCols X₁ X₂) *ᵥ (Sum.elim v 0) := by
      rw [fromCols_mulVec_sumElim, fromCols_mulVec_sumElim, huv]
    have he := hXinj hsum
    funext j; simpa using congr_fun he (Sum.inl j)
  have hpd : (X₁ᵀ * X₁).PosDef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using PosDef.conjTranspose_mul_self X₁ hX1inj
  exact (isUnit_iff_isUnit_det _).mp hpd.isUnit

set_option linter.style.haveILetI false in
/-- If `[X₁ X₂]` has invertible Gram matrix, so has `M₁ X₂`. -/
theorem isUnit_det_transpose_mul_self_residualMaker {X₁ : Matrix ι κ₁ ℝ} {X₂ : Matrix ι κ₂ ℝ}
    (h : IsUnit ((fromCols X₁ X₂)ᵀ * fromCols X₁ X₂).det) :
    IsUnit ((residualMaker X₁ * X₂)ᵀ * (residualMaker X₁ * X₂)).det := by
  have hX1 : IsUnit (X₁ᵀ * X₁).det := isUnit_det_transpose_mul_self_left h
  letI : Invertible (X₁ᵀ * X₁) := invertibleOfIsUnitDet _ hX1
  have hM1M1 : (residualMaker X₁)ᵀ * residualMaker X₁ = residualMaker X₁ := by
    rw [transpose_residualMaker, residualMaker_mul_self]
  have hSchur : (residualMaker X₁ * X₂)ᵀ * (residualMaker X₁ * X₂)
      = X₂ᵀ * X₂ - X₂ᵀ * X₁ * ⅟(X₁ᵀ * X₁) * (X₁ᵀ * X₂) := by
    have h1 : (residualMaker X₁ * X₂)ᵀ * (residualMaker X₁ * X₂)
        = X₂ᵀ * (residualMaker X₁ * X₂) := by
      rw [Matrix.transpose_mul, Matrix.mul_assoc,
        ← Matrix.mul_assoc (residualMaker X₁)ᵀ (residualMaker X₁) X₂, hM1M1]
    rw [h1]
    unfold residualMaker
    rw [leastSquares, invOf_eq_nonsing_inv, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub]
    congr 1
    simp only [Matrix.mul_assoc]
  have hblock : (fromCols X₁ X₂)ᵀ * fromCols X₁ X₂
      = fromBlocks (X₁ᵀ * X₁) (X₁ᵀ * X₂) (X₂ᵀ * X₁) (X₂ᵀ * X₂) := by
    rw [transpose_fromCols, fromRows_mul_fromCols]
  have hdet : ((fromCols X₁ X₂)ᵀ * fromCols X₁ X₂).det
      = (X₁ᵀ * X₁).det * ((residualMaker X₁ * X₂)ᵀ * (residualMaker X₁ * X₂)).det := by
    rw [hblock, det_fromBlocks₁₁, ← hSchur]
  rw [hdet] at h
  exact (IsUnit.mul_iff.mp h).2

/-- **The Frisch–Waugh–Lovell theorem**: the `X₂`-coefficients of the regression of `y` on
`[X₁ X₂]` are those of the regression of `M₁ y` on `M₁ X₂`. -/
theorem leastSquares_fromCols_mulVec_inr {X₁ : Matrix ι κ₁ ℝ} {X₂ : Matrix ι κ₂ ℝ}
    (h : IsUnit ((fromCols X₁ X₂)ᵀ * fromCols X₁ X₂).det) (y : ι → ℝ) :
    (leastSquares (fromCols X₁ X₂) *ᵥ y) ∘ Sum.inr
      = leastSquares (residualMaker X₁ * X₂) *ᵥ (residualMaker X₁ *ᵥ y) := by
  have hX1 : IsUnit (X₁ᵀ * X₁).det := isUnit_det_transpose_mul_self_left h
  have hMX2 : IsUnit ((residualMaker X₁ * X₂)ᵀ * (residualMaker X₁ * X₂)).det :=
    isUnit_det_transpose_mul_self_residualMaker h
  set β := leastSquares (fromCols X₁ X₂) *ᵥ y with hβ
  have hnorm : (fromCols X₁ X₂)ᵀ *ᵥ (y - fromCols X₁ X₂ *ᵥ β) = 0 :=
    transpose_mulVec_sub_mulVec_leastSquares h y
  set r := y - fromCols X₁ X₂ *ᵥ β with hrdef
  have hblock : (fromCols X₁ X₂)ᵀ *ᵥ r = Sum.elim (X₁ᵀ *ᵥ r) (X₂ᵀ *ᵥ r) := by
    rw [transpose_fromCols, fromRows_mulVec]
  rw [hblock] at hnorm
  have hr1 : X₁ᵀ *ᵥ r = 0 := by
    funext j; have := congr_fun hnorm (Sum.inl j); simpa using this
  have hr2 : X₂ᵀ *ᵥ r = 0 := by
    funext j; have := congr_fun hnorm (Sum.inr j); simpa using this
  have hL1r : leastSquares X₁ *ᵥ r = 0 := by
    rw [leastSquares, ← Matrix.mulVec_mulVec, hr1, Matrix.mulVec_zero]
  have hM1r : residualMaker X₁ *ᵥ r = r := by
    rw [residualMaker, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hL1r,
      Matrix.mulVec_zero, sub_zero]
  have hXβ : fromCols X₁ X₂ *ᵥ β = X₁ *ᵥ (β ∘ Sum.inl) + X₂ *ᵥ (β ∘ Sum.inr) := by
    conv_lhs => rw [← Sum.elim_comp_inl_inr β]
    rw [fromCols_mulVec_sumElim]
  have hnormM : ((residualMaker X₁ * X₂)ᵀ * (residualMaker X₁ * X₂)) *ᵥ (β ∘ Sum.inr)
      = (residualMaker X₁ * X₂)ᵀ *ᵥ (residualMaker X₁ *ᵥ y) := by
    have hS3 : residualMaker X₁ * X₁ = 0 := residualMaker_mul_eq_zero hX1
    have key : residualMaker X₁ *ᵥ (X₂ *ᵥ (β ∘ Sum.inr)) = residualMaker X₁ *ᵥ y - r := by
      have hbig : X₂ *ᵥ (β ∘ Sum.inr) = y - r - X₁ *ᵥ (β ∘ Sum.inl) := by
        rw [hrdef, hXβ]; abel
      rw [hbig, Matrix.mulVec_sub, Matrix.mulVec_sub, hM1r, Matrix.mulVec_mulVec, hS3,
        Matrix.zero_mulVec, sub_zero]
    have hr0 : (residualMaker X₁ * X₂)ᵀ *ᵥ r = 0 := by
      rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec, transpose_residualMaker, hM1r, hr2]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, key, Matrix.mulVec_sub, hr0, sub_zero]
  have hsol : ((residualMaker X₁ * X₂)ᵀ * (residualMaker X₁ * X₂)) *ᵥ
      (leastSquares (residualMaker X₁ * X₂) *ᵥ (residualMaker X₁ *ᵥ y))
      = (residualMaker X₁ * X₂)ᵀ *ᵥ (residualMaker X₁ *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, leastSquares, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hMX2, Matrix.one_mul]
  have hinj : Function.Injective
      ((residualMaker X₁ * X₂)ᵀ * (residualMaker X₁ * X₂)).mulVec :=
    mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr hMX2)
  exact hinj (hnormM.trans hsol.symm)

/-- The same with `y` not residualised (`M₁` is symmetric and idempotent). -/
theorem leastSquares_fromCols_mulVec_inr' {X₁ : Matrix ι κ₁ ℝ} {X₂ : Matrix ι κ₂ ℝ}
    (h : IsUnit ((fromCols X₁ X₂)ᵀ * fromCols X₁ X₂).det) (y : ι → ℝ) :
    (leastSquares (fromCols X₁ X₂) *ᵥ y) ∘ Sum.inr
      = leastSquares (residualMaker X₁ * X₂) *ᵥ y := by
  have hM1M1 : (residualMaker X₁)ᵀ * residualMaker X₁ = residualMaker X₁ := by
    rw [transpose_residualMaker, residualMaker_mul_self]
  have hTabs : (residualMaker X₁ * X₂)ᵀ * residualMaker X₁ = (residualMaker X₁ * X₂)ᵀ := by
    conv_lhs => rw [Matrix.transpose_mul, Matrix.mul_assoc, hM1M1]
    conv_rhs => rw [Matrix.transpose_mul, transpose_residualMaker]
  have habsorb : leastSquares (residualMaker X₁ * X₂) * residualMaker X₁
      = leastSquares (residualMaker X₁ * X₂) := by
    conv_lhs => rw [leastSquares, Matrix.mul_assoc, hTabs]
    rw [leastSquares]
  rw [leastSquares_fromCols_mulVec_inr h y, Matrix.mulVec_mulVec, habsorb]

/-- The residuals agree: `y − X β̂ = M₁ y − (M₁ X₂) β̂₂`. -/
theorem residual_eq_residualMaker_sub {X₁ : Matrix ι κ₁ ℝ} {X₂ : Matrix ι κ₂ ℝ}
    (h : IsUnit ((fromCols X₁ X₂)ᵀ * fromCols X₁ X₂).det) (y : ι → ℝ) :
    y - fromCols X₁ X₂ *ᵥ (leastSquares (fromCols X₁ X₂) *ᵥ y)
      = residualMaker X₁ *ᵥ y
        - (residualMaker X₁ * X₂) *ᵥ
            (leastSquares (residualMaker X₁ * X₂) *ᵥ (residualMaker X₁ *ᵥ y)) := by
  have hX1 : IsUnit (X₁ᵀ * X₁).det := isUnit_det_transpose_mul_self_left h
  rw [← leastSquares_fromCols_mulVec_inr h y]
  set β := leastSquares (fromCols X₁ X₂) *ᵥ y with hβ
  have hnorm : (fromCols X₁ X₂)ᵀ *ᵥ (y - fromCols X₁ X₂ *ᵥ β) = 0 :=
    transpose_mulVec_sub_mulVec_leastSquares h y
  set r := y - fromCols X₁ X₂ *ᵥ β with hrdef
  have hblock : (fromCols X₁ X₂)ᵀ *ᵥ r = Sum.elim (X₁ᵀ *ᵥ r) (X₂ᵀ *ᵥ r) := by
    rw [transpose_fromCols, fromRows_mulVec]
  rw [hblock] at hnorm
  have hr1 : X₁ᵀ *ᵥ r = 0 := by
    funext j; have := congr_fun hnorm (Sum.inl j); simpa using this
  have hL1r : leastSquares X₁ *ᵥ r = 0 := by
    rw [leastSquares, ← Matrix.mulVec_mulVec, hr1, Matrix.mulVec_zero]
  have hM1r : residualMaker X₁ *ᵥ r = r := by
    rw [residualMaker, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hL1r,
      Matrix.mulVec_zero, sub_zero]
  have hXβ : fromCols X₁ X₂ *ᵥ β = X₁ *ᵥ (β ∘ Sum.inl) + X₂ *ᵥ (β ∘ Sum.inr) := by
    conv_lhs => rw [← Sum.elim_comp_inl_inr β]
    rw [fromCols_mulVec_sumElim]
  have hS3 : residualMaker X₁ * X₁ = 0 := residualMaker_mul_eq_zero hX1
  have key : residualMaker X₁ *ᵥ (X₂ *ᵥ (β ∘ Sum.inr)) = residualMaker X₁ *ᵥ y - r := by
    have hbig : X₂ *ᵥ (β ∘ Sum.inr) = y - r - X₁ *ᵥ (β ∘ Sum.inl) := by
      rw [hrdef, hXβ]; abel
    rw [hbig, Matrix.mulVec_sub, Matrix.mulVec_sub, hM1r, Matrix.mulVec_mulVec, hS3,
      Matrix.zero_mulVec, sub_zero]
  rw [← Matrix.mulVec_mulVec, key]; abel

/-- **The Frisch–Waugh–Lovell theorem, matrix form**: the `X₂`-rows of the least-squares matrix
of `[X₁ X₂]` are the least-squares matrix of `M₁ X₂`. -/
theorem toRows₂_leastSquares_fromCols {X₁ : Matrix ι κ₁ ℝ} {X₂ : Matrix ι κ₂ ℝ}
    (h : IsUnit ((fromCols X₁ X₂)ᵀ * fromCols X₁ X₂).det) :
    (leastSquares (fromCols X₁ X₂)).toRows₂ = leastSquares (residualMaker X₁ * X₂) := by
  ext i j
  have key := congr_fun (leastSquares_fromCols_mulVec_inr' h (Pi.single j 1)) i
  rw [Matrix.toRows₂_apply]
  simpa using key

/-- The invertibility hypothesis `h` cannot be dropped: at `X₁ = 0`, `X₂ = (1, 1)`, `y = (1, 3)`,
both Gram matrices `Xᵀ X` and `X₁ᵀ X₁` are singular, the left side is `0` and the right side is
`2`. (This does not show `IsUnit (X₁ᵀ X₁).det` alone cannot be dropped — see the remark above.) -/
theorem not_forall_leastSquares_fromCols_mulVec_inr :
    ¬ ∀ (X₁ : Matrix (Fin 2) (Fin 1) ℝ) (X₂ : Matrix (Fin 2) (Fin 1) ℝ) (y : Fin 2 → ℝ),
      (leastSquares (fromCols X₁ X₂) *ᵥ y) ∘ Sum.inr
        = leastSquares (residualMaker X₁ * X₂) *ᵥ (residualMaker X₁ *ᵥ y) := by
  intro H
  have hM0 : residualMaker (0 : Matrix (Fin 2) (Fin 1) ℝ) = 1 := by
    rw [residualMaker, Matrix.zero_mul, sub_zero]
  have hsing : leastSquares (fromCols (0 : Matrix (Fin 2) (Fin 1) ℝ) (!![1; 1])) = 0 := by
    apply leastSquares_eq_zero_of_not_isUnit_det
    rw [isUnit_iff_ne_zero, not_not]
    apply Matrix.det_eq_zero_of_row_eq_zero (Sum.inl 0)
    intro j
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.fromCols_apply_inl]
  have hkey := congr_fun (H 0 !![1; 1] ![1, 3]) 0
  rw [hsing, hM0, Matrix.one_mul, Matrix.one_mulVec, leastSquares_ones_two] at hkey
  simp [Matrix.zero_mulVec, mulVec, dotProduct] at hkey
  norm_num at hkey

end ClassicalLean.Statistics
