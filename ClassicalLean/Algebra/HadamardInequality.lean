/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalities

/-!
# Hadamard's inequality

* `det_le_prod_diag` — a positive semidefinite real matrix has determinant at most the product of
  its diagonal entries: `det A ≤ ∏ i, A i i`.
* `sq_det_le_prod_sum_sq` — so any real square matrix has `(det M)² ≤ ∏ i, ∑ j, (M i j)²`: the
  squared volume of the slanted box (parallelepiped) spanned by the rows is at most the product of
  the rows' squared lengths. It follows from the first with `A = M Mᵀ`.

Citation: Hadamard 1893, "Résolution d'une question relative aux déterminants".

The proof: if `det A = 0` the bound holds because the diagonal of a positive semidefinite matrix
is at least `0`. Otherwise `A` is positive definite, its diagonal entries are positive, and
`B = D A D`, with `D` diagonal and `D i i = 1 / √(A i i)`, is positive semidefinite with every
diagonal entry `1`. Its eigenvalues are at least `0` and add up to its trace, the number of rows
`n`, so by the arithmetic–geometric mean inequality their product, `det B`, is at most `1`; and
`det A = det B · ∏ i, A i i`.

## Hypotheses

Measured in order LEAN-21's checks (check C37, exact rationals): `det A ≤ ∏ A i i` for 300 random
`A = B Bᵀ` with `B` integer, singular ones included; the row form for 300 random integer `M`.
Positive semidefinite is needed: `A = −[[2, 1, 0], [1, 2, 0], [0, 0, 1]]` has `det A = −3`, above
`∏ A i i = −4`; and a symmetric matrix with diagonal at least `0` is not enough:
`[[0, 1, 1], [1, 0, 1], [1, 1, 0]]` has `det = 2 > 0` (review r37). (For `2 × 2` symmetric matrices
the bound holds without it, since `a d − b² ≤ a d`.)

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-21, `grep -rniE` over Mathlib):
`hadamard.?s? inequality|det_le_prod|prod_diag|det.*le.*prod.*diag` 1 line (`Finset.prod_diag`,
unrelated); `det_le|le_det` in LinearAlgebra 3 lines, `Matrix.det_le`, a bound from bounded
entries; `det.*≤.*∏` 0. Mathlib's files on "Hadamard" (`grep -rli`) treat the entrywise product
(`LinearAlgebra/Matrix/Hadamard`, the Schur product theorem in `Analysis/Matrix/Order`), Hadamard
matrices (`LinearAlgebra/Matrix/HadamardMatrix`, whose `IsHadamard.det_mul_star_det` is the case
of equality in the row form) and the three-lines theorem (`Analysis/Complex/Hadamard`); none
proves this inequality. Used:
`PosSemidef.posDef_iff_det_ne_zero`, `PosDef.diag_pos`, `PosSemidef.mul_mul_conjTranspose_same`,
`IsHermitian.det_eq_prod_eigenvalues`, `IsHermitian.trace_eq_sum_eigenvalues`,
`PosSemidef.eigenvalues_nonneg`, `Real.geom_mean_le_arith_mean`. The plan's row names the LDL
decomposition; it is not used.
-/

open Finset Matrix

namespace ClassicalLean

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The arithmetic–geometric mean inequality in the form used here: numbers `z i ≥ 0` that add up
to the number of indices have product at most `1`. -/
private theorem prod_le_one_of_sum_eq_card [Nonempty n] {z : n → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hs : ∑ i, z i = Fintype.card n) : ∏ i, z i ≤ 1 := by
  have hc : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have h := Real.geom_mean_le_arith_mean univ (fun _ ↦ (1 : ℝ)) z (fun _ _ ↦ zero_le_one)
    (by simpa using hc) (fun i _ ↦ hz i)
  simp only [Real.rpow_one, sum_const, card_univ, nsmul_eq_mul, mul_one, one_mul, hs,
    div_self hc.ne'] at h
  by_contra hlt
  push Not at hlt
  have := Real.one_lt_rpow hlt (inv_pos.mpr hc)
  linarith

/-- **Hadamard's inequality.** A positive semidefinite real matrix has determinant at most the
product of its diagonal entries. -/
theorem det_le_prod_diag {A : Matrix n n ℝ} (hA : A.PosSemidef) : A.det ≤ ∏ i, A i i := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp
  by_cases hdet : A.det = 0
  · rw [hdet]; exact prod_nonneg fun i _ ↦ hA.diag_nonneg
  have hPD : A.PosDef := hA.posDef_iff_det_ne_zero.mpr hdet
  have hpos : ∀ i, 0 < A i i := fun i ↦ hPD.diag_pos
  set d : n → ℝ := fun i ↦ (Real.sqrt (A i i))⁻¹ with hd
  have hd2 : ∀ i, d i * d i = (A i i)⁻¹ := fun i ↦ by
    rw [hd, ← mul_inv, Real.mul_self_sqrt (hpos i).le]
  have hDt : (diagonal d)ᴴ = diagonal d := by simp
  set B := diagonal d * A * (diagonal d)ᴴ with hBdef
  have hB : B.PosSemidef := hA.mul_mul_conjTranspose_same (diagonal d)
  have hBij : ∀ i j, B i j = d i * A i j * d j := fun i j ↦ by
    rw [hBdef, hDt, mul_diagonal, diagonal_mul]
  have hBii : ∀ i, B i i = 1 := fun i ↦ by
    rw [hBij, mul_right_comm, hd2, inv_mul_cancel₀ (hpos i).ne']
  have hprod : 0 < ∏ i, A i i := prod_pos fun i _ ↦ hpos i
  have hdetB : B.det = A.det * (∏ i, A i i)⁻¹ := by
    have hdd : (∏ i, d i) * (∏ i, d i) = (∏ i, A i i)⁻¹ := by
      rw [← prod_mul_distrib, ← prod_inv_distrib]
      exact prod_congr rfl fun i _ ↦ hd2 i
    rw [hBdef, det_mul, det_mul, hDt, det_diagonal, ← hdd]
    ring
  have hBle : B.det ≤ 1 := by
    rw [hB.isHermitian.det_eq_prod_eigenvalues]
    have htr := hB.isHermitian.trace_eq_sum_eigenvalues
    have htrB : B.trace = Fintype.card n := by
      simp [trace, Matrix.diag, hBii]
    rw [htrB] at htr
    simp only [RCLike.ofReal_real_eq_id, id] at htr
    simp only [RCLike.ofReal_real_eq_id, id]
    exact prod_le_one_of_sum_eq_card (fun i ↦ hB.eigenvalues_nonneg i) htr.symm
  rw [hdetB] at hBle
  have := mul_le_mul_of_nonneg_right hBle hprod.le
  rwa [inv_mul_cancel_right₀ hprod.ne', one_mul] at this

/-- **Hadamard's inequality for rows.** For any real square matrix,
`(det M)² ≤ ∏ i, ∑ j, (M i j)²`. -/
theorem sq_det_le_prod_sum_sq (M : Matrix n n ℝ) : M.det ^ 2 ≤ ∏ i, ∑ j, M i j ^ 2 := by
  have h := det_le_prod_diag (posSemidef_self_mul_conjTranspose M)
  rw [det_mul, det_conjTranspose] at h
  simpa [sq, mul_apply] using h

end ClassicalLean
