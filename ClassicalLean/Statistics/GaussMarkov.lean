/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The Gauss–Markov theorem

In the linear model `y = X β + ε`, with design matrix `X`, a *linear estimator* of `β` is
`β̂ = C y` for a matrix `C`. It is unbiased exactly when `C * X = 1`
(`unbiased_iff_mul_eq_one`). The **Gauss–Markov theorem** says that among linear unbiased
estimators, least squares, `C = (Xᵀ X)⁻¹ Xᵀ`, has the smallest covariance: when the noise has
mean `0` and covariance `σ² • 1`, the covariance of `C y` is `σ² • C Cᵀ` and that of least
squares is `σ² • (Xᵀ X)⁻¹`, and

    C Cᵀ - (Xᵀ X)⁻¹  is positive semidefinite  (posSemidef_self_mul_transpose_sub_inv),

with equality exactly at least squares (`self_mul_transpose_eq_inv_iff`). Everything here is
stated as matrix algebra over `ℝ`: no probability measure is involved, and the covariance
reading above is the standard one, not a theorem of this file.

## Main results

* `leastSquares X = (Xᵀ X)⁻¹ Xᵀ`, the least-squares matrix, and its facts:
  `leastSquares_mul_self` (it is unbiased when `Xᵀ X` is invertible),
  `leastSquares_mul_transpose` (its variance factor is `(Xᵀ X)⁻¹`, with no hypothesis),
  `transpose_mulVec_sub_mulVec_leastSquares` (the normal equations) and
  `residual_dotProduct_le` (least squares: no `X β` has a smaller sum of squared residuals).
* `isUnit_det_transpose_mul_self_of_mul_eq_one` and
  `exists_mul_eq_one_iff_isUnit_det_transpose_mul_self`: an unbiased linear estimator exists
  exactly when `Xᵀ X` is invertible.
* The theorem: `self_mul_transpose_sub_inv_eq` (`C Cᵀ - (Xᵀ X)⁻¹ = D Dᵀ` with
  `D = C - leastSquares X`), `posSemidef_self_mul_transpose_sub_inv`, the equality case
  `self_mul_transpose_eq_inv_iff`, the variance reading `dotProduct_inv_mulVec_le` and the
  Loewner form `inv_le_self_mul_transpose` (under `open scoped MatrixOrder`).
* The hypotheses of the normal equations, of the least-squares theorem and of the variance
  reading (and so of the Gauss–Markov theorem and its Loewner form) cannot be dropped: each
  statement without its hypothesis has a counterexample,
  `not_forall_transpose_mulVec_sub_mulVec_leastSquares`, `not_forall_residual_dotProduct_le`,
  `not_forall_dotProduct_inv_mulVec_le`.
* A worked example, two observations of one mean (`X = !![1; 1]`): least squares is the sample
  mean (`leastSquares_ones_two`), and the first observation alone is unbiased with twice the
  variance, so the inequality can be strict (`exists_mul_eq_one_dotProduct_inv_mulVec_lt`). That
  theorem is also the witness that the hypothesis class `C * X = 1` is inhabited.
* One more observation (recursive least squares, order LEAN-22): `leastSquares_append_row` and
  `inv_transpose_mul_appendRow`, below.

## One more observation: recursive least squares

Order LEAN-22 (item 40 of the plan) adds what happens when one more observation arrives: a row
`x` of the design with response `y'`. The new design is `appendRow X x` (the rows of `X`, then
`x`), and with `P = (Xᵀ X)⁻¹` and the old estimate `β = leastSquares X *ᵥ y`:

* `transpose_mul_appendRow`: the new `Xᵀ X` is `Xᵀ X + x xᵀ`;
* `inv_transpose_mul_appendRow`: its inverse is `P − P x xᵀ P / (1 + xᵀ P x)`. This is Mathlib's
  Woodbury identity (`Matrix.add_mul_mul_inv_eq_sub`) with a `1 × 1` middle matrix, read for one
  new row;
* `leastSquares_append_row`: the new estimate is `β + P x (y' − xᵀ β) / (1 + xᵀ P x)`: the old
  estimate, moved along `P x` in proportion to how far the new response is from its prediction
  `xᵀ β`. No new matrix has to be inverted;
* `one_add_dotProduct_inv_mulVec_pos`: the divisor `1 + xᵀ P x` is positive, for every `X`, and
  `isUnit_det_transpose_mul_appendRow`: an invertible `Xᵀ X` stays invertible.

The estimate update is proved from the normal equations: the new `Xᵀ X` times the proposed
estimate is the new `Xᵀ y`. Measured in order LEAN-22's checks (check C40, exact arithmetic): both
updates equal a direct computation on 300 random integer designs with `Xᵀ X` invertible. `Xᵀ X`
invertible is needed (for the estimate also in Lean: `not_forall_leastSquares_append_row`):
with one observation and one parameter, `X = (0)`, `x = 1`, `y = 0`, `y' = 1`, the new estimate is
`1`, while the formula, with Mathlib's junk inverse `0`, gives `0`; the same case breaks the
inverse update, and with `x = 0` the new matrix stays singular. The positivity of `1 + xᵀ P x`
needs no hypothesis, because `P` is positive semidefinite even when it is the junk `0` (Mathlib's
`Matrix.PosSemidef.inv`). Mathlib's matrix determinant lemma
(`Matrix.det_add_replicateCol_mul_replicateRow`) gives the invertibility.

## Junk values, enumerated first

Mathlib's matrix inverse is `0` on a singular matrix (`Matrix.nonsing_inv_apply_not_isUnit`).
So `leastSquares X = 0` when `Xᵀ X` is singular (`leastSquares_eq_zero_of_not_isUnit_det`); there
it does not in general satisfy the normal equations or the least-squares property (the
`not_forall_` counterexamples), which is why those carry `IsUnit (Xᵀ X).det`. The hypothesis
`C * X = 1` of the main theorem cannot meet the junk value, because it forces `Xᵀ X` to be
invertible: if `Xᵀ X v = 0` then `X v` has zero length, so `X v = 0` and `v = C X v = 0`.
`leastSquares_mul_transpose` is the one public statement that holds on the junk value too, as
`0 = 0`. The hypothesis is empty when there are fewer observations than parameters (the rank of
`C * X` is then at most the number of observations, below that of `1`), and trivial when there
are no parameters.

## Mathlib at v4.34.0

Searched before this file was written, `grep -rniE '<pattern>' Mathlib --include=*.lean`: no
Gauss–Markov theorem, and nothing named least squares, "unbiased" or regression (the 26 hits of
`gauss.?markov|best linear unbiased|unbiased|least.?squares|leastSquares|regression` are all
the word "regression": tactic-analysis options, a linter set, four definitions and two
comments); no Moore–Penrose
inverse; no `(Xᵀ * X)⁻¹` shape. Mathlib has least-squares minimisation in geometric form
(`Submodule.starProjection_minimal`), positive semidefiniteness (`Matrix.PosSemidef`) and the
Loewner order (`Analysis/Matrix/Order.lean`), which this file uses. The full search, with
counts, is `ROADMAP.md` §2.9.
-/

namespace ClassicalLean.Statistics

open Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- The least-squares matrix `(Xᵀ X)⁻¹ Xᵀ` of a design matrix `X`. When `Xᵀ X` is invertible,
the least-squares estimate from observations `y` is `leastSquares X *ᵥ y`. When `Xᵀ X` is
singular, Mathlib's `⁻¹` is `0`, and so is this matrix, which is then not in general a
least-squares solution (`not_forall_residual_dotProduct_le`). -/
noncomputable def leastSquares (X : Matrix ι κ ℝ) : Matrix κ ι ℝ :=
  (Xᵀ * X)⁻¹ * Xᵀ

/-- `C` recovers every parameter from noiseless data, `C (X β) = β`, exactly when `C * X = 1`.
With zero-mean noise `E[C y] = C X β`, so this is unbiasedness of `β̂ = C y`; stated as matrix
algebra. -/
theorem unbiased_iff_mul_eq_one {X : Matrix ι κ ℝ} {C : Matrix κ ι ℝ} :
    (∀ β, C *ᵥ (X *ᵥ β) = β) ↔ C * X = 1 := by
  refine ⟨fun h => ext_iff_mulVec.mpr fun v => ?_, fun h β => ?_⟩
  · rw [← mulVec_mulVec, h, one_mulVec]
  · rw [mulVec_mulVec, h, one_mulVec]

/-- An unbiased linear estimator exists only if `Xᵀ X` is invertible. -/
theorem isUnit_det_transpose_mul_self_of_mul_eq_one {X : Matrix ι κ ℝ} {C : Matrix κ ι ℝ}
    (hC : C * X = 1) : IsUnit (Xᵀ * X).det := by
  have hinj : Function.Injective X.mulVec := fun u v huv => by
    simpa [mulVec_mulVec, hC] using congrArg (C *ᵥ ·) huv
  have hpd : (Xᵀ * X).PosDef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using PosDef.conjTranspose_mul_self X hinj
  exact (isUnit_iff_isUnit_det _).mp hpd.isUnit

/-- The junk value: when `Xᵀ X` is singular, Mathlib's `⁻¹` is `0`
(`Matrix.nonsing_inv_apply_not_isUnit`), and so is `leastSquares X`. -/
theorem leastSquares_eq_zero_of_not_isUnit_det {X : Matrix ι κ ℝ}
    (h : ¬ IsUnit (Xᵀ * X).det) : leastSquares X = 0 := by
  rw [leastSquares, nonsing_inv_apply_not_isUnit _ h, Matrix.zero_mul]

/-- When `Xᵀ X` is invertible (full column rank), the least-squares matrix is unbiased. -/
theorem leastSquares_mul_self {X : Matrix ι κ ℝ} (hX : IsUnit (Xᵀ * X).det) :
    leastSquares X * X = 1 := by
  rw [leastSquares, Matrix.mul_assoc, nonsing_inv_mul _ hX]

/-- A linear unbiased estimator exists exactly when `Xᵀ X` is invertible. -/
theorem exists_mul_eq_one_iff_isUnit_det_transpose_mul_self {X : Matrix ι κ ℝ} :
    (∃ C : Matrix κ ι ℝ, C * X = 1) ↔ IsUnit (Xᵀ * X).det :=
  ⟨fun ⟨_, hC⟩ => isUnit_det_transpose_mul_self_of_mul_eq_one hC,
    fun hX => ⟨leastSquares X, leastSquares_mul_self hX⟩⟩

/-- `(Xᵀ X)⁻¹` is symmetric. -/
private theorem transpose_inv_transpose_mul_self (X : Matrix ι κ ℝ) :
    ((Xᵀ * X)⁻¹)ᵀ = (Xᵀ * X)⁻¹ := by
  rw [transpose_nonsing_inv, transpose_mul, transpose_transpose]

/-- The variance factor of least squares is `(Xᵀ X)⁻¹`. No hypothesis: when `Xᵀ X` is singular,
Mathlib's inverse is `0`, so `leastSquares X = 0` and both sides are `0`. -/
theorem leastSquares_mul_transpose (X : Matrix ι κ ℝ) :
    leastSquares X * (leastSquares X)ᵀ = (Xᵀ * X)⁻¹ := by
  by_cases h : IsUnit (Xᵀ * X).det
  · rw [leastSquares, transpose_mul, transpose_transpose, transpose_inv_transpose_mul_self,
      Matrix.mul_assoc, ← Matrix.mul_assoc Xᵀ, ← Matrix.mul_assoc, nonsing_inv_mul _ h,
      Matrix.one_mul]
  · simp [leastSquares, nonsing_inv_apply_not_isUnit _ h]

/-- When `Xᵀ X` is invertible, the normal equations `Xᵀ X β̂ = Xᵀ y` hold for
`β̂ = leastSquares X *ᵥ y`, in residual form: the residual `y - X β̂` is orthogonal to every column
of `X`. -/
theorem transpose_mulVec_sub_mulVec_leastSquares {X : Matrix ι κ ℝ} (hX : IsUnit (Xᵀ * X).det)
    (y : ι → ℝ) : Xᵀ *ᵥ (y - X *ᵥ (leastSquares X *ᵥ y)) = 0 := by
  simp only [mulVec_sub, mulVec_mulVec, leastSquares, ← Matrix.mul_assoc, mul_nonsing_inv _ hX,
    Matrix.one_mul, sub_self]

/-- **Least squares**: when `Xᵀ X` is invertible, no `X β` is closer to `y`, in the sum of
squares, than `X β̂` with `β̂ = leastSquares X *ᵥ y`. -/
theorem residual_dotProduct_le {X : Matrix ι κ ℝ} (hX : IsUnit (Xᵀ * X).det) (y : ι → ℝ)
    (β : κ → ℝ) :
    (y - X *ᵥ (leastSquares X *ᵥ y)) ⬝ᵥ (y - X *ᵥ (leastSquares X *ᵥ y)) ≤
      (y - X *ᵥ β) ⬝ᵥ (y - X *ᵥ β) := by
  have h0 := transpose_mulVec_sub_mulVec_leastSquares hX y
  have hsplit : y - X *ᵥ β =
      (y - X *ᵥ (leastSquares X *ᵥ y)) + X *ᵥ (leastSquares X *ᵥ y - β) := by
    rw [mulVec_sub]; abel
  rw [hsplit]
  generalize y - X *ᵥ (leastSquares X *ᵥ y) = r at h0 ⊢
  generalize leastSquares X *ᵥ y - β = d
  have horth : r ⬝ᵥ (X *ᵥ d) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, h0, zero_dotProduct]
  have hnn : 0 ≤ (X *ᵥ d) ⬝ᵥ (X *ᵥ d) := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rw [add_dotProduct, dotProduct_add, dotProduct_add, horth, dotProduct_comm (X *ᵥ d) r, horth]
  linarith

/-- The excess variance factor of an unbiased `C` over least squares is `D Dᵀ`, where
`D = C - leastSquares X`. -/
theorem self_mul_transpose_sub_inv_eq {X : Matrix ι κ ℝ} {C : Matrix κ ι ℝ} (hC : C * X = 1) :
    C * Cᵀ - (Xᵀ * X)⁻¹ = (C - leastSquares X) * (C - leastSquares X)ᵀ := by
  have hCM : C * (leastSquares X)ᵀ = (Xᵀ * X)⁻¹ := by
    rw [leastSquares, transpose_mul, transpose_transpose, transpose_inv_transpose_mul_self,
      ← Matrix.mul_assoc, hC, Matrix.one_mul]
  have hMC : leastSquares X * Cᵀ = (Xᵀ * X)⁻¹ := by
    have := congrArg transpose hCM
    rwa [transpose_mul, transpose_transpose, transpose_inv_transpose_mul_self] at this
  rw [transpose_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, hCM, hMC,
    leastSquares_mul_transpose]
  abel

/-- **The Gauss–Markov theorem**, matrix form: for every linear unbiased estimator `C`
(`C * X = 1`), `C Cᵀ - (Xᵀ X)⁻¹` is positive semidefinite. In the linear model `y = X β + ε` with
`E ε = 0` and `Cov ε = σ² • 1`, `σ² • C Cᵀ` and `σ² • (Xᵀ X)⁻¹` are the covariance matrices of
`C y` and of the least-squares estimate, so least squares is the best linear unbiased estimator.
Stated as matrix algebra; no probability measure is involved. -/
theorem posSemidef_self_mul_transpose_sub_inv {X : Matrix ι κ ℝ} {C : Matrix κ ι ℝ}
    (hC : C * X = 1) : (C * Cᵀ - (Xᵀ * X)⁻¹).PosSemidef := by
  rw [self_mul_transpose_sub_inv_eq hC]
  simpa [conjTranspose_eq_transpose_of_trivial] using
    posSemidef_self_mul_conjTranspose (C - leastSquares X)

/-- The equality case: least squares is the only unbiased estimator attaining the bound. -/
theorem self_mul_transpose_eq_inv_iff {X : Matrix ι κ ℝ} {C : Matrix κ ι ℝ} (hC : C * X = 1) :
    C * Cᵀ = (Xᵀ * X)⁻¹ ↔ C = leastSquares X := by
  rw [← sub_eq_zero, self_mul_transpose_sub_inv_eq hC, ← conjTranspose_eq_transpose_of_trivial,
    self_mul_conjTranspose_eq_zero, sub_eq_zero]

/-- The variance reading (matrix algebra; with noise covariance `σ² • 1`, the two sides times
`σ²` are the variances of `a ⬝ᵥ β̂` for least squares and for `C`). -/
theorem dotProduct_inv_mulVec_le {X : Matrix ι κ ℝ} {C : Matrix κ ι ℝ} (hC : C * X = 1)
    (a : κ → ℝ) : a ⬝ᵥ ((Xᵀ * X)⁻¹ *ᵥ a) ≤ a ⬝ᵥ ((C * Cᵀ) *ᵥ a) := by
  have h := (posSemidef_self_mul_transpose_sub_inv hC).dotProduct_mulVec_nonneg a
  simpa [sub_mulVec, dotProduct_sub, sub_nonneg] using h

open scoped MatrixOrder in
/-- The Loewner form of the Gauss–Markov theorem: `posSemidef_self_mul_transpose_sub_inv` read
through `Matrix.le_iff`. -/
theorem inv_le_self_mul_transpose {X : Matrix ι κ ℝ} {C : Matrix κ ι ℝ} (hC : C * X = 1) :
    (Xᵀ * X)⁻¹ ≤ C * Cᵀ :=
  Matrix.le_iff.mpr (posSemidef_self_mul_transpose_sub_inv hC)

/-- The singular design `!![1, 1; 1, 1]`: `Xᵀ X = !![2, 2; 2, 2]` has determinant `0`, so
`leastSquares` takes its junk value `0`. -/
private theorem leastSquares_ones_two_two :
    leastSquares (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
  apply leastSquares_eq_zero_of_not_isUnit_det
  rw [isUnit_iff_ne_zero, not_not, det_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The normal equations need their hypothesis: at `X = !![1, 1; 1, 1]`, `y = ![1, 0]`,
`leastSquares X = 0` (the junk value) and the left side is `Xᵀ *ᵥ y = ![1, 1]`. This is a fact
about the definition, which rests on Mathlib's junk inverse: this rank-deficient design still has
least-squares solutions, such as `![1/2, 0]`, and they satisfy the normal equations. -/
theorem not_forall_transpose_mulVec_sub_mulVec_leastSquares :
    ¬ ∀ (X : Matrix (Fin 2) (Fin 2) ℝ) (y : Fin 2 → ℝ),
      Xᵀ *ᵥ (y - X *ᵥ (leastSquares X *ᵥ y)) = 0 := by
  intro h
  have := congrFun (h !![1, 1; 1, 1] ![1, 0]) 0
  rw [leastSquares_ones_two_two] at this
  simp [mulVec, dotProduct, Fin.sum_univ_two] at this

/-- The least-squares minimality needs its hypothesis: at `X = !![1, 1; 1, 1]`, `y = ![1, 0]`,
`leastSquares X = 0` gives residual sum of squares `1`, while `β = ![1/2, 0]` gives `1/2`. -/
theorem not_forall_residual_dotProduct_le :
    ¬ ∀ (X : Matrix (Fin 2) (Fin 2) ℝ) (y : Fin 2 → ℝ) (β : Fin 2 → ℝ),
      (y - X *ᵥ (leastSquares X *ᵥ y)) ⬝ᵥ (y - X *ᵥ (leastSquares X *ᵥ y)) ≤
        (y - X *ᵥ β) ⬝ᵥ (y - X *ᵥ β) := by
  intro h
  have := h !![1, 1; 1, 1] ![1, 0] ![1 / 2, 0]
  rw [leastSquares_ones_two_two] at this
  simp [dotProduct, Fin.sum_univ_two] at this
  norm_num at this

/-- `Xᵀ X = !![2]` for two observations of one mean, so its inverse is `!![1 / 2]`. -/
private theorem inv_transpose_mul_self_ones_two :
    ((!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ * (!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ))⁻¹ =
      !![1 / 2] := by
  apply inv_eq_left_inv
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  norm_num

/-- The variance reading, and so the Gauss–Markov theorem and its Loewner form, need the
hypothesis `C * X = 1`, even where `Xᵀ X` is invertible: at `X = !![1; 1]`, the biased `C = 0`
and `a = ![1]` give `1/2 ≤ 0`. -/
theorem not_forall_dotProduct_inv_mulVec_le :
    ¬ ∀ (X : Matrix (Fin 2) (Fin 1) ℝ) (C : Matrix (Fin 1) (Fin 2) ℝ) (a : Fin 1 → ℝ),
      IsUnit (Xᵀ * X).det → a ⬝ᵥ ((Xᵀ * X)⁻¹ *ᵥ a) ≤ a ⬝ᵥ ((C * Cᵀ) *ᵥ a) := by
  intro h
  have hdet : IsUnit
      ((!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ * (!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ)).det := by
    rw [isUnit_iff_ne_zero, det_fin_one]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have := h !![1; 1] 0 ![1] hdet
  rw [inv_transpose_mul_self_ones_two] at this
  simp [mulVec, dotProduct] at this
  norm_num at this

/-- Two observations of one mean, `X = !![1; 1]`: least squares is the sample mean. -/
theorem leastSquares_ones_two :
    leastSquares (!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ) = !![1 / 2, 1 / 2] := by
  rw [leastSquares, inv_transpose_mul_self_ones_two]
  ext i j
  fin_cases i; fin_cases j <;> simp [Matrix.mul_apply]

/-- The hypothesis `C * X = 1` is satisfiable and the variance inequality can be strict: two
observations of one mean, `X = !![1; 1]`, the first observation alone, `C = !![1, 0]`, and
`a = ![1]` give variance factors `1 / 2` for least squares against `1` for `C`. -/
theorem exists_mul_eq_one_dotProduct_inv_mulVec_lt :
    ∃ (X : Matrix (Fin 2) (Fin 1) ℝ) (C : Matrix (Fin 1) (Fin 2) ℝ) (a : Fin 1 → ℝ),
      C * X = 1 ∧ a ⬝ᵥ ((Xᵀ * X)⁻¹ *ᵥ a) < a ⬝ᵥ ((C * Cᵀ) *ᵥ a) := by
  refine ⟨!![1; 1], !![1, 0], ![1], ?_, ?_⟩
  · ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [inv_transpose_mul_self_ones_two]
    simp [mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two]
    norm_num

/-- The first observation alone is unbiased. -/
example : (!![1, 0] : Matrix (Fin 1) (Fin 2) ℝ) * (!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ) = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-! ### One more observation (order LEAN-22, item 40) -/

/-- The design `X` with one more row `x` below its rows. -/
def appendRow (X : Matrix ι κ ℝ) (x : κ → ℝ) : Matrix (ι ⊕ Unit) κ ℝ :=
  fromRows X (replicateRow Unit x)

omit [Fintype κ] [DecidableEq κ] in
/-- One more row `x` adds `x xᵀ` to `Xᵀ X`. -/
theorem transpose_mul_appendRow (X : Matrix ι κ ℝ) (x : κ → ℝ) :
    (appendRow X x)ᵀ * appendRow X x = Xᵀ * X + vecMulVec x x := by
  rw [appendRow, transpose_fromRows, fromCols_mul_fromRows, transpose_replicateRow,
    vecMulVec_eq Unit]

omit [Fintype κ] [DecidableEq κ] in
/-- One more observation `(x, y')` adds `y' x` to `Xᵀ y`. -/
theorem transpose_mulVec_appendRow (X : Matrix ι κ ℝ) (x : κ → ℝ) (y : ι → ℝ) (y' : ℝ) :
    (appendRow X x)ᵀ *ᵥ Sum.elim y (fun _ ↦ y') = Xᵀ *ᵥ y + y' • x := by
  rw [appendRow, transpose_fromRows, fromCols_mulVec_sumElim, transpose_replicateRow]
  ext k
  simp [mulVec, dotProduct, mul_comm]

/-- `1 + xᵀ (Xᵀ X)⁻¹ x > 0` for every `X` and `x`: `(Xᵀ X)⁻¹` is positive semidefinite, also when
it is Mathlib's junk value `0`. -/
theorem one_add_dotProduct_inv_mulVec_pos (X : Matrix ι κ ℝ) (x : κ → ℝ) :
    0 < 1 + x ⬝ᵥ ((Xᵀ * X)⁻¹ *ᵥ x) := by
  have h : (Xᵀ * X).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self X
  have := h.inv.dotProduct_mulVec_nonneg x
  simp only [star_trivial] at this
  linarith

omit [DecidableEq κ] in
/-- The `1 × 1` matrix `xᵀ P x`. -/
private theorem replicateRow_mul_mul_replicateCol (P : Matrix κ κ ℝ) (x : κ → ℝ) :
    replicateRow Unit x * P * replicateCol Unit x = of fun _ _ ↦ x ⬝ᵥ (P *ᵥ x) := by
  rw [Matrix.mul_assoc, ← replicateCol_mulVec, replicateRow_mul_replicateCol]

/-- If `Xᵀ X` is invertible, so is `Xᵀ X` after one more row: by the matrix determinant lemma
its determinant is `det (Xᵀ X) * (1 + xᵀ (Xᵀ X)⁻¹ x)`. -/
theorem isUnit_det_transpose_mul_appendRow {X : Matrix ι κ ℝ} (hX : IsUnit (Xᵀ * X).det)
    (x : κ → ℝ) : IsUnit ((appendRow X x)ᵀ * appendRow X x).det := by
  rw [transpose_mul_appendRow, vecMulVec_eq Unit, det_add_replicateCol_mul_replicateRow hX,
    det_unique (1 + _), replicateRow_mul_mul_replicateCol]
  exact hX.mul (isUnit_iff_ne_zero.mpr (one_add_dotProduct_inv_mulVec_pos X x).ne')

/-- **The inverse after one more row** (Sherman–Morrison form): with `P = (Xᵀ X)⁻¹`,
`(X'ᵀ X')⁻¹ = P − P x xᵀ P / (1 + xᵀ P x)`. It is Mathlib's Woodbury identity
`Matrix.add_mul_mul_inv_eq_sub` with a `1 × 1` middle matrix. -/
theorem inv_transpose_mul_appendRow {X : Matrix ι κ ℝ} (hX : IsUnit (Xᵀ * X).det) (x : κ → ℝ) :
    ((appendRow X x)ᵀ * appendRow X x)⁻¹ = (Xᵀ * X)⁻¹ -
      (1 + x ⬝ᵥ ((Xᵀ * X)⁻¹ *ᵥ x))⁻¹ • vecMulVec ((Xᵀ * X)⁻¹ *ᵥ x) (x ᵥ* (Xᵀ * X)⁻¹) := by
  set A := Xᵀ * X
  have hd := (one_add_dotProduct_inv_mulVec_pos X x).ne'
  have hAC : IsUnit ((1 : Matrix Unit Unit ℝ)⁻¹ +
      replicateRow Unit x * A⁻¹ * replicateCol Unit x) := by
    rw [inv_one, replicateRow_mul_mul_replicateCol, isUnit_iff_isUnit_det, det_unique]
    exact isUnit_iff_ne_zero.mpr hd
  have hW := add_mul_mul_inv_eq_sub A (replicateCol Unit x) 1 (replicateRow Unit x)
    ((isUnit_iff_isUnit_det A).mpr hX) isUnit_one hAC
  rw [Matrix.mul_one, ← vecMulVec_eq Unit] at hW
  rw [transpose_mul_appendRow, hW, inv_one, replicateRow_mul_mul_replicateCol,
    inv_subsingleton (1 + of _)]
  have hdiag : (diagonal fun i : Unit ↦
      Ring.inverse ((1 + of fun _ _ ↦ x ⬝ᵥ (A⁻¹ *ᵥ x) : Matrix Unit Unit ℝ) i i)) =
      (1 + x ⬝ᵥ (A⁻¹ *ᵥ x))⁻¹ • (1 : Matrix Unit Unit ℝ) := by
    rw [smul_one_eq_diagonal]
    congr 1
    funext i
    simp [Ring.inverse_eq_inv']
  rw [hdiag]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [Matrix.mul_assoc A⁻¹, ← vecMulVec_eq Unit, mul_vecMulVec, vecMulVec_mul]

/-- **Recursive least squares.** When `Xᵀ X` is invertible, one more observation `(x, y')`
changes the least-squares estimate `β = leastSquares X *ᵥ y` to
`β + P x (y' − xᵀ β) / (1 + xᵀ P x)`, with `P = (Xᵀ X)⁻¹`. -/
theorem leastSquares_append_row {X : Matrix ι κ ℝ} (hX : IsUnit (Xᵀ * X).det) (x : κ → ℝ)
    (y : ι → ℝ) (y' : ℝ) :
    leastSquares (appendRow X x) *ᵥ Sum.elim y (fun _ ↦ y') =
      leastSquares X *ᵥ y + ((y' - x ⬝ᵥ (leastSquares X *ᵥ y)) /
        (1 + x ⬝ᵥ ((Xᵀ * X)⁻¹ *ᵥ x))) • ((Xᵀ * X)⁻¹ *ᵥ x) := by
  set A := Xᵀ * X with hA
  set β := leastSquares X *ᵥ y
  set c := (y' - x ⬝ᵥ β) / (1 + x ⬝ᵥ (A⁻¹ *ᵥ x))
  have hc : c * (1 + x ⬝ᵥ (A⁻¹ *ᵥ x)) = y' - x ⬝ᵥ β :=
    div_mul_cancel₀ _ (one_add_dotProduct_inv_mulVec_pos X x).ne'
  have hAβ : A *ᵥ β = Xᵀ *ᵥ y := by
    simp only [β, leastSquares, ← hA, mulVec_mulVec, ← Matrix.mul_assoc, mul_nonsing_inv _ hX,
      Matrix.one_mul]
  have hAP : A *ᵥ (A⁻¹ *ᵥ x) = x := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hX, one_mulVec]
  have key : ((appendRow X x)ᵀ * appendRow X x) *ᵥ (β + c • (A⁻¹ *ᵥ x)) =
      (appendRow X x)ᵀ *ᵥ Sum.elim y (fun _ ↦ y') := by
    rw [transpose_mul_appendRow, transpose_mulVec_appendRow, add_mulVec, mulVec_add, mulVec_add,
      mulVec_smul, mulVec_smul, vecMulVec_mulVec, vecMulVec_mulVec, hAβ, hAP]
    simp only [op_smul_eq_smul]
    linear_combination (norm := module) hc • x
  rw [leastSquares, ← mulVec_mulVec, ← key, mulVec_mulVec,
    nonsing_inv_mul _ (isUnit_det_transpose_mul_appendRow hX x), one_mulVec]

/-- The hypothesis of `leastSquares_append_row` is needed: with one observation and one parameter,
`X = (0)`, `x = 1`, `y = 0` and `y' = 1`, the new estimate is `1`, while the formula, with
Mathlib's junk inverse `0`, gives `0` (review r40 of order LEAN-22). -/
theorem not_forall_leastSquares_append_row :
    ¬ ∀ (X : Matrix (Fin 1) (Fin 1) ℝ) (x : Fin 1 → ℝ) (y : Fin 1 → ℝ) (y' : ℝ),
      leastSquares (appendRow X x) *ᵥ Sum.elim y (fun _ ↦ y') =
        leastSquares X *ᵥ y + ((y' - x ⬝ᵥ (leastSquares X *ᵥ y)) /
          (1 + x ⬝ᵥ ((Xᵀ * X)⁻¹ *ᵥ x))) • ((Xᵀ * X)⁻¹ *ᵥ x) := by
  intro h
  have h1 := congrFun (h 0 (fun _ ↦ 1) 0 1) 0
  have hz : leastSquares (0 : Matrix (Fin 1) (Fin 1) ℝ) = 0 := by
    apply leastSquares_eq_zero_of_not_isUnit_det; simp
  have hA : (appendRow (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ ↦ 1))ᵀ *
      appendRow (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ ↦ 1) = 1 := by
    rw [transpose_mul_appendRow]; ext i j; fin_cases i; fin_cases j; simp [vecMulVec]
  rw [hz] at h1
  simp only [leastSquares, hA, inv_one, Matrix.one_mul] at h1
  simp only [mulVec, dotProduct, appendRow, fromRows, replicateRow, Fin.isValue, transpose_apply,
    of_apply, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Sum.elim_inl,
    Pi.zero_apply, mul_zero, Finset.sum_const_zero, PUnit.default_eq_unit, Sum.elim_inr, mul_one,
    Finset.sum_singleton, zero_add, mulVec_zero, Matrix.zero_apply, sub_zero, transpose_zero,
    inv_subsingleton, isUnit_iff_ne_zero, ne_eq, not_true_eq_false, not_false_eq_true,
    Ring.inverse_non_unit, diagonal_zero, add_zero, one_ne_zero, div_self, zero_mulVec, smul_zero,
    Pi.add_apply] at h1
  exact one_ne_zero (show (1 : ℝ) = 0 from h1)

end ClassicalLean.Statistics

open Matrix in
/-- The hypotheses of `leastSquares_append_row` hold together: the `3 × 2` design with rows
`(1, 0)`, `(1, 1)` and `(0, 1)` has Gram matrix with rows `(2, 1)` and `(1, 2)`, whose determinant
`3` is a unit; the new row `x = (1, 1)`, the old responses `y = (1, 2, 3)` and the new one `y' = 4`.
-/
example := ClassicalLean.Statistics.leastSquares_append_row (ι := Fin 3) (κ := Fin 2)
  (X := !![1, 0; 1, 1; 0, 1])
  (by norm_num [isUnit_iff_ne_zero, det_fin_two, mul_apply, Fin.sum_univ_three]) (x := ![1, 1])
  (y := ![1, 2, 3]) (y' := 4)
