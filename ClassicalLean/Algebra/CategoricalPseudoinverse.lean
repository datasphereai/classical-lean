/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Algebra.Pseudoinverse
import ClassicalLean.Simplex.SecondOrder

/-!
# The pseudoinverse of a categorical covariance

Bridge 172 of `MATH-PLAN-library-2-bridges-2.md` (order CLOUD-MATH-7), joining
`ClassicalLean.Algebra.Pseudoinverse` and `ClassicalLean.Simplex.SecondOrder`.

* `pinv_categoricalCov` — for a strictly positive probability vector `p` on `n = card ι` points
  and `P = 1 - (1/n) 1 1ᵀ`, the projection onto the vectors summing to `0`,
  `pinv (categoricalCov p) = P * diagonal (1/p) * P` and
  `categoricalCov p * pinv (categoricalCov p) = P`. On tangent vectors this is the Fisher–Rao
  form; `Simplex.SecondOrder` states the inverse only in a two-coordinate chart
  (`fisherRaoChart_mul_categoricalCov`).

The proof. Write `C = categoricalCov p = D - p pᵀ` with `D = diagonal p`, and
`X = P D⁻¹ P`. `C 1 = 0` (`categoricalCov_mulVec_one`) and the symmetry of `C` give
`C P = P C = C`; `C D⁻¹ = 1 - p 1ᵀ` and `1ᵀ P = 0` give `C X = P`, and `X C = P` by symmetry;
then `C X C = P C = C` and `X C X = P X = X`, and `P` is symmetric, so `pinv_unique` applies.

The statement was written by order LEAN-38 (a reading order) and elaborated there stated without
a proof; this module proves it word for word.
-/

open Matrix
open ClassicalLean.Algebra.Pseudoinverse ClassicalLean.Simplex

namespace ClassicalLean.Algebra.CategoricalPseudoinverse

/-- **The pseudoinverse of a categorical covariance is the Fisher–Rao form on the tangent space.**
For a strictly positive probability vector `p` on `n = card ι` points, write
`P = 1 - (1/n) 1 1ᵀ` (the projection onto vectors summing to `0`). Then
`pinv (categoricalCov p) = P * diagonal (1/p) * P`, and
`categoricalCov p * pinv (categoricalCov p) = P`.
(A consequence, not stated here: for tangent vectors `u`, `v`, sums `0`, `P u = u`, so
`u ⬝ᵥ (pinv (categoricalCov p) *ᵥ v) = ∑ i, u i * v i / p i`, the Fisher–Rao form.)
Bridge 172 of `MATH-PLAN-library-2-bridges-2.md`. -/
theorem pinv_categoricalCov {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → ℝ}
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1) :
    pinv (categoricalCov p) =
        (1 - (Fintype.card ι : ℝ)⁻¹ • Matrix.of fun _ _ ↦ (1 : ℝ)) *
          Matrix.diagonal (fun i ↦ (p i)⁻¹) *
          (1 - (Fintype.card ι : ℝ)⁻¹ • Matrix.of fun _ _ ↦ (1 : ℝ)) ∧
      categoricalCov p * pinv (categoricalCov p) =
        1 - (Fintype.card ι : ℝ)⁻¹ • Matrix.of fun _ _ ↦ (1 : ℝ) := by
  set J : Matrix ι ι ℝ := Matrix.of fun _ _ ↦ (1 : ℝ) with hJ_def
  set P : Matrix ι ι ℝ := 1 - (Fintype.card ι : ℝ)⁻¹ • J with hP_def
  set D' : Matrix ι ι ℝ := Matrix.diagonal (fun i ↦ (p i)⁻¹) with hD'_def
  set Dp : Matrix ι ι ℝ := Matrix.diagonal p with hDp_def
  set C := categoricalCov p with hC_def
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hp1
  have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- `C = Dp - Dp J Dp`
  have hC : C = Dp - Dp * J * Dp := by
    ext i j
    simp [C, Dp, J, categoricalCov, Matrix.vecMulVec_apply, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
  have hJJ : J * J = (Fintype.card ι : ℝ) • J := by
    ext i j
    simp [J, Matrix.mul_apply]
  have hJP : J * P = 0 := by
    rw [hP_def, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, hJJ, smul_smul,
      inv_mul_cancel₀ hn, one_smul, sub_self]
  have hPJ : P * J = 0 := by
    rw [hP_def, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, hJJ, smul_smul,
      inv_mul_cancel₀ hn, one_smul, sub_self]
  have hPP : P * P = P := by
    conv_lhs => rw [hP_def]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, hJP, smul_zero, sub_zero]
  -- `C 1 = 0` gives `C J = 0`, and `C` is symmetric, so `J C = 0`
  have hCJ : C * J = 0 := by
    ext i j
    have := congrFun (categoricalCov_mulVec_one hp1) i
    simpa [J, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hJt : Jᵀ = J := by
    ext i j
    simp [J]
  have hCt : Cᵀ = C := by
    ext i j
    simp only [C, Matrix.transpose_apply, categoricalCov_apply]
    by_cases h : i = j
    · subst h; rfl
    · simp [h, Ne.symm h, mul_comm]
  have hJC : J * C = 0 := by
    rw [← hJt, ← hCt, ← Matrix.transpose_mul, hCJ, Matrix.transpose_zero]
  have hCP : C * P = C := by
    rw [hP_def, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, hCJ, smul_zero, sub_zero]
  have hPC : P * C = C := by
    rw [hP_def, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, hJC, smul_zero, sub_zero]
  -- `D⁻¹` inverts `D`
  have hD'Dp : D' * Dp = 1 := by
    rw [hD'_def, hDp_def, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext fun i ↦ inv_mul_cancel₀ (hp i).ne')
  have hDpD' : Dp * D' = 1 := by
    rw [hD'_def, hDp_def, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext fun i ↦ mul_inv_cancel₀ (hp i).ne')
  have hCD : C * D' = 1 - Dp * J := by
    rw [hC, Matrix.sub_mul, hDpD', Matrix.mul_assoc (Dp * J), hDpD', Matrix.mul_one]
  have hDC : D' * C = 1 - J * Dp := by
    rw [hC, Matrix.mul_sub, hD'Dp, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hD'Dp,
      Matrix.one_mul]
  -- the four Penrose equations for `X = P D⁻¹ P`
  have hCX : C * (P * D' * P) = P := by
    calc C * (P * D' * P) = C * P * D' * P := by simp only [Matrix.mul_assoc]
      _ = P := by
        rw [hCP, hCD, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hJP, Matrix.mul_zero,
          sub_zero]
  have hXC : P * D' * P * C = P := by
    calc P * D' * P * C = P * (D' * (P * C)) := by simp only [Matrix.mul_assoc]
      _ = P := by
        rw [hPC, hDC, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPJ, Matrix.zero_mul,
          sub_zero]
  have hPt : Pᵀ = P := by
    rw [hP_def, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hJt]
  have hX : P * D' * P = pinv C := by
    refine pinv_unique ?_ ?_ ?_ ?_
    · rw [hCX, hPC]
    · rw [hXC]
      simp only [← Matrix.mul_assoc]
      rw [hPP]
    · rw [hCX, hPt]
    · rw [hXC, hPt]
  exact ⟨hX.symm, by rw [← hX, hCX]⟩

end ClassicalLean.Algebra.CategoricalPseudoinverse

/-- The hypotheses of `pinv_categoricalCov` hold together: on `ι = Fin 3`, the probability vector
`p = (1/2, 1/3, 1/6)` is strictly positive and sums to `1`; it is not uniform, so
`diagonal (1/p) = diag (2, 3, 6)` is not a multiple of `1` and the projection `P` matters. -/
example := ClassicalLean.Algebra.CategoricalPseudoinverse.pinv_categoricalCov (ι := Fin 3)
    (p := ![1 / 2, 1 / 3, 1 / 6])
    (fun i ↦ by fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_three])
