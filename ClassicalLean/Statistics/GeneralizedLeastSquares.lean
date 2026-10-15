/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Statistics.GaussMarkov
import ClassicalLean.Analysis.MinimumQuadraticForm
import ClassicalLean.Algebra.Kantorovich

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

**A common mean** (order LEAN-27, item 81). When the design `X` is a column of ones (one unknown,
the common mean; `κ` has one element), generalised least squares is the least-variance weighting
of `Analysis/MinimumQuadraticForm`: `glsMatrix_ones_eq_minWeights` says its row
`(1ᵀ V⁻¹ 1)⁻¹ 1ᵀ V⁻¹` is `minWeights V = V⁻¹ 1 / (1ᵀ V⁻¹ 1)`, and
`inv_transpose_mul_ones_eq` and `glsMatrix_ones_mul_mul_transpose` give its variance factor
`1 / (1ᵀ V⁻¹ 1)`. The shared object is the positive definite quadratic form `wᵀ V w`: Aitken's
theorem here and `inv_onesInvOnes_le_quadForm` there say the same thing for this design (a
reading, not stated as a Lean theorem). The
row's identity needs only `Vᵀ = V`, not the plan's "positive definite", so it is stated with that
(wider than the plan's row); exact cases in order LEAN-27's `checks.py`: without symmetry,
`V = [[2, 1], [0, 1]]` gives the row `(1/2, 1/2)` against `minWeights V = (0, 1)`; for a singular
symmetric `V`, Mathlib's `V⁻¹ = 0` makes both sides `0` (and so does `1ᵀ V⁻¹ 1 = 0`, as for
`V = diag(1, −1)`, under `0⁻¹ = 0`). The variance factor needs only that `κ` has one element
(`[Unique κ]`, the one column), and all three theorems need it (cold review r81): with two
columns of ones (`κ = Fin 2`, `V = 1`), `Xᵀ V⁻¹ X` is the singular all-`2` matrix, so Lean's
inverse and the GLS row are `0`, against `minWeights 1 = (1/2, 1/2)` and a variance factor `1/2`.
This file now imports `Analysis/MinimumQuadraticForm` (which imports only Mathlib,
so no cycle).

**What ordinary least squares loses, for a common mean** (order LEAN-30, item 98 of
MATH-PLAN-library-2). With noise covariance `σ² V`, the plain average of `n` observations has
variance `σ² (1ᵀ V 1) / n²` and generalised least squares has `σ² / (1ᵀ V⁻¹ 1)` (above); their ratio
is `(1ᵀ V 1)(1ᵀ V⁻¹ 1) / n²` (the variance reading is the standard one, not a theorem of this file).
`onesQuad_mul_onesInvOnes_le` bounds it: when `m ≤ V ≤ M` in the Loewner order (`V − m I` and
`M I − V` positive semidefinite) and `0 < m`, the ratio is at most `(m + M)² / (4 m M)`, Bloomfield
and Watson's efficiency bound in this case (P. Bloomfield and G. S. Watson, "The inefficiency of
least squares", Biometrika 62 (1975)). It is the Kantorovich inequality
(`ClassicalLean.Algebra.Kantorovich.dotProduct_mulVec_mul_inv_le`, imported here; that module
imports only Mathlib, so no cycle) at the vector of ones, with `1 ⬝ 1 = n`. The bound is reached at
`V = diag(m, M)`, `n = 2`, the equal mix of the two eigenvectors (order LEAN-30's check
`98.equal`). Each hypothesis is needed (order LEAN-30's exact checks, lane `lean/LEAN-30-checks.py`,
each case keeping the other hypotheses):

* `0 < m` (`98.drop.hm`): `V = (1)`, `m = 0`, `M = 1`: the left side is `1`, the bound Lean's
  `1 / 0 = 0`.
* `V − m I ≥ 0` (`98.drop.hmV`): `V = diag(1, 4)`, `m = 2`, `M = 4`: `25/16` against `9/8`.
* `M I − V ≥ 0` (`98.drop.hVM`): `V = diag(1, 4)`, `m = 1`, `M = 2`: `25/16` against `9/8`.
* at least one index (`98.drop.nonempty`): with none, the left side is Lean's `0 / 0 = 0`, while
  `m = 1`, `M = −2` meet both Loewner hypotheses (a matrix with no entries is positive
  semidefinite) and the bound is `−1/8`.

The junk value `x / 0 = 0` decides two rows, in the bound (`0 < m`) and on the left (no index).
Also measured exactly: 200 cases `V = H D H` (`98.random`). The plan's search
(`MATH-PLAN-library-2-checks.py`, line `row.X16`: `bloomfield`), in order LEAN-30's run of it
before this module changed, found 0 lines in pinned Mathlib, in Mathlib master at `2da3ab0a` and in
the library. The hypotheses hold together: the witness at the end of this file.

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

open Matrix ClassicalLean.Analysis.MinimumQuadraticForm

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

/-! ### A common mean (order LEAN-27, item 81) -/

omit [Fintype κ] [DecidableEq κ] in
/-- For `X` a matrix of ones with any column set `κ`, every entry of `Xᵀ V⁻¹ X` is `1ᵀ V⁻¹ 1`
(the `1 × 1` matrix `1ᵀ V⁻¹ 1` when `κ` has one element). -/
theorem transpose_mul_ones_eq (V : Matrix ι ι ℝ) :
    (of fun _ _ ↦ (1 : ℝ) : Matrix ι κ ℝ)ᵀ * V⁻¹ * (of fun _ _ ↦ (1 : ℝ) : Matrix ι κ ℝ) =
      of fun _ _ ↦ onesInvOnes V := by
  ext a b
  simp only [mul_apply, transpose_apply, of_apply, one_mul, mul_one, onesInvOnes, dotProduct,
    Pi.one_apply, mulVec]
  rw [Finset.sum_comm]

/-- **The variance factor for a common mean** (order LEAN-27, item 81): for `X` a column of ones,
`(Xᵀ V⁻¹ X)⁻¹ = 1 / (1ᵀ V⁻¹ 1)`, for every `V` (both sides are `0` when `V` is singular). -/
theorem inv_transpose_mul_ones_eq [Unique κ] (V : Matrix ι ι ℝ) :
    ((of fun _ _ ↦ (1 : ℝ) : Matrix ι κ ℝ)ᵀ * V⁻¹ * (of fun _ _ ↦ (1 : ℝ) : Matrix ι κ ℝ))⁻¹ =
      (of fun _ _ ↦ (onesInvOnes V)⁻¹ : Matrix κ κ ℝ) := by
  rw [transpose_mul_ones_eq, inv_def, adjugate_subsingleton, det_unique]
  ext a b
  simp [Subsingleton.elim a b, Ring.inverse_eq_inv']

/-- **Generalised least squares for a common mean is the least-variance weighting** (order
LEAN-27, item 81): for a symmetric `V` and `X` a column of ones, the row of `glsMatrix V X`,
`(1ᵀ V⁻¹ 1)⁻¹ 1ᵀ V⁻¹`, is `minWeights V = V⁻¹ 1 / (1ᵀ V⁻¹ 1)`. -/
theorem glsMatrix_ones_eq_minWeights [Unique κ] {V : Matrix ι ι ℝ} (hV : Vᵀ = V) (c : κ) :
    glsMatrix V (of fun _ _ ↦ (1 : ℝ) : Matrix ι κ ℝ) c = minWeights V := by
  have hVi : V⁻¹ᵀ = V⁻¹ := by rw [transpose_nonsing_inv, hV]
  rw [glsMatrix, inv_transpose_mul_ones_eq]
  ext j
  simp only [minWeights, mul_apply, of_apply, transpose_apply, Pi.smul_apply,
    smul_eq_mul, mulVec, dotProduct, mul_one, Finset.univ_unique, Finset.sum_singleton,
    ← Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Pi.one_apply, mul_one, ← hVi, transpose_apply, hVi]

/-- The covariance factor of generalised least squares for a common mean is `1 / (1ᵀ V⁻¹ 1)`,
for every `V`: `glsMatrix_mul_mul_transpose` with `inv_transpose_mul_ones_eq`. -/
theorem glsMatrix_ones_mul_mul_transpose [Unique κ] (V : Matrix ι ι ℝ) :
    glsMatrix V (of fun _ _ ↦ (1 : ℝ) : Matrix ι κ ℝ) * V *
        (glsMatrix V (of fun _ _ ↦ (1 : ℝ) : Matrix ι κ ℝ))ᵀ =
      (of fun _ _ ↦ (onesInvOnes V)⁻¹ : Matrix κ κ ℝ) := by
  rw [glsMatrix_mul_mul_transpose, inv_transpose_mul_ones_eq]

/-! ### What ordinary least squares loses, for a common mean (order LEAN-30, item 98) -/

/-- **Bloomfield and Watson's bound for a common mean** (order LEAN-30, item 98 of
MATH-PLAN-library-2). When `m ≤ V ≤ M` in the Loewner order and `0 < m`, the ratio
`(1ᵀ V 1)(1ᵀ V⁻¹ 1) / n²` (read as the variance of the plain average over that of generalised
least squares; a reading, not a theorem) is at most `(m + M)² / (4 m M)`: the Kantorovich
inequality at the vector of ones. -/
theorem onesQuad_mul_onesInvOnes_le [Nonempty ι] {V : Matrix ι ι ℝ} {m M : ℝ} (hm : 0 < m)
    (hmV : (V - m • 1).PosSemidef) (hVM : (M • 1 - V).PosSemidef) :
    (1 ⬝ᵥ (V *ᵥ 1)) * onesInvOnes V / (Fintype.card ι : ℝ) ^ 2 ≤ (m + M) ^ 2 / (4 * m * M) := by
  have h := ClassicalLean.Algebra.Kantorovich.dotProduct_mulVec_mul_inv_le hm hmV hVM 1
  rw [one_dotProduct_one] at h
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ (by positivity)]
  exact h

/-- The hypothesis of `glsMatrix_ones_eq_minWeights` can be met: `V = 1` on `ℝ²`. -/
example : glsMatrix (1 : Matrix (Fin 2) (Fin 2) ℝ) (of fun _ _ ↦ (1 : ℝ) : Matrix (Fin 2) Unit ℝ)
    () = minWeights 1 :=
  glsMatrix_ones_eq_minWeights (transpose_one) ()

end ClassicalLean.Statistics

open Matrix in
/-- The hypotheses of `posSemidef_mul_mul_transpose_sub_inv` hold together: the noise covariance
`V = diag (1, 2, 3)`, positive definite, so invertible and positive semidefinite; the design `X`,
whose columns are the first two unit vectors of `ℝ³`; and `C` with rows `(1, 0, 1)` and
`(0, 1, 0)`, a left inverse of `X` (the third row of `X` is zero) that is not the GLS matrix, so
the difference in the conclusion is `diag (3, 0)`, not `0`. -/
example := ClassicalLean.Statistics.posSemidef_mul_mul_transpose_sub_inv (ι := Fin 3) (κ := Fin 2)
  (V := diagonal ![1, 2, 3]) (posSemidef_diagonal_iff.mpr fun i ↦ by fin_cases i <;> norm_num)
  (X := !![1, 0; 0, 1; 0, 0]) (C := !![1, 0, 1; 0, 1, 0])
  (by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three])

open Matrix in
/-- The hypotheses of `onesQuad_mul_onesInvOnes_le` hold together: `V = [[2, 1], [1, 3]]`, `m = 1`,
`M = 4`. `V − I = [[1, 1], [1, 2]] = Bᵀ B` with `B = [[1, 1], [0, 1]]`, and
`4 I − V = [[2, −1], [−1, 1]] = Cᵀ C` with `C = [[1, −1], [1, 0]]`, so both are positive
semidefinite. The vector of ones is not an eigenvector of `V` (by hand: `V *ᵥ 1 = (3, 4)`), and the
left side, `21/20`, lies strictly between `1` and the bound `25/16` (order LEAN-30's check
`98.witness`): ordinary least squares loses something here, though less than the bound allows. -/
example := ClassicalLean.Statistics.onesQuad_mul_onesInvOnes_le (ι := Fin 2)
  (V := !![2, 1; 1, 3]) (m := 1) (M := 4) one_pos
  (by
    rw [show (!![2, 1; 1, 3] : Matrix (Fin 2) (Fin 2) ℝ) - (1 : ℝ) • 1 =
        (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)ᴴ * !![1, 1; 0, 1] by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [conjTranspose_eq_transpose_of_trivial, mul_apply, Fin.sum_univ_two, one_fin_two] <;>
        norm_num]
    exact posSemidef_conjTranspose_mul_self _)
  (by
    rw [show (4 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - !![2, 1; 1, 3] =
        (!![1, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)ᴴ * !![1, -1; 1, 0] by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [conjTranspose_eq_transpose_of_trivial, mul_apply, Fin.sum_univ_two, one_fin_two] <;>
        norm_num]
    exact posSemidef_conjTranspose_mul_self _)
