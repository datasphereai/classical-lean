/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
# The Kantorovich inequality

For a real matrix `A` with `m ≤ A ≤ M` in the Loewner order (`A − m I` and `M I − A` positive
semidefinite, which makes `A` symmetric) and `0 < m`, every vector `x` has
`(xᵀ A x)(xᵀ A⁻¹ x) ≤ ((m + M)² / (4 m M)) ‖x‖⁴` (Kantorovich 1948). It bounds how far apart the
quadratic forms of `A` and `A⁻¹` can pull, and so how slowly steepest descent can go on `xᵀ A x`.

* `dotProduct_mulVec_mul_inv_le` — the inequality, with `‖x‖⁴` written `(x ⬝ x)²`.
* `dotProduct_mulVec_mul_inv_add_eq` — an identity for any two eigenpairs of an invertible `A`
  (`A u = m u`, `A v = M v`) of equal length (`u ⬝ u = v ⬝ v`; the vectors may be `0`): at
  `x = u + v` the two sides are equal. With `u ≠ 0` and `m`, `M` the Loewner bounds of the
  inequality (and eigenvalues of `A`), it shows the bound is reached, by an equal mix of
  eigenvectors for `m` and `M`, as the plan's row says. The proof shows that neither `u ⬝ v = 0`
  nor unit length is needed (both sides are `((m + M)² / (m M)) (s + p)²` with `s = u ⬝ u`,
  `p = u ⬝ v`); the exact case of order LEAN-27's checks, a non-symmetric `A` with `u ⬝ v = 3/5`,
  only illustrates it. With no sign condition the identity also holds for eigenvalues of
  opposite signs (both sides are then `≤ 0`). If `m M = 0`, invertibility forces the eigenvector
  for `0` to be `0`, so `u = v = 0` and both sides are `0` (cold review r82, round 2).
* `dotProduct_mulVec_eq_sum` — the tool: for an orthonormal basis of eigenvectors `bᵢ` of `B` with
  eigenvalues `μᵢ`, `x ⬝ B x = ∑ μᵢ (bᵢ ⬝ x)²` (no symmetry hypothesis, cold review r82).

The proof: in Mathlib's eigenvector basis of `A` (`Matrix.IsHermitian.eigenvectorBasis`), with
`cᵢ = bᵢ ⬝ x`, the three numbers are `xᵀ A x = ∑ λᵢ cᵢ²`, `xᵀ A⁻¹ x = ∑ cᵢ² / λᵢ` and
`x ⬝ x = ∑ cᵢ²`, and every `λᵢ` lies in `[m, M]` (the two Loewner hypotheses at `bᵢ`). From
`(λ − m)(M − λ) ≥ 0`, `λ + m M / λ ≤ m + M`; summed,
`xᵀ A x + m M · xᵀ A⁻¹ x ≤ (m + M) x ⬝ x`, and `4 m M a b ≤ (a + m M b)²` finishes.

## Hypotheses

Exact cases in order LEAN-27's `checks.py` (fractions, Lean's conventions; output `chk2.out`,
ALL OK). Each drops one hypothesis and keeps the rest:

* `0 < m`: `A = 1`, `M = 1`, `x = (1)`; at `m = 0` the bound is Lean's `x / 0 = 0` and the left
  side is `1`; at `m = −1` the bound is `0 / (−4) = 0`.
* `A − m I ≥ 0`: `A = diag(1/4, 1)`, `m = M = 1`, `x = (1, 1)`: `25/4 > 4`.
* `M I − A ≥ 0`: `A = diag(1, 4)`, `m = M = 1`, `x = (1, 1)`: `25/4 > 4`.
* Sanity: `A = diag(1, 4)`, `m = 1`, `M = 4`: `x = (1, 1)` gives equality (`25/4`), `x = (2, 1)`
  gives `34 < 625/16`.

For the equality (`dotProduct_mulVec_mul_inv_add_eq`):

* `A` invertible: `A = diag(1, 2, 0)`, `u = e₀`, `v = e₁`, `m = 1`, `M = 2`: Lean's `A⁻¹ = 0`
  gives `0`, against `9/2`.
* `A u = m u`: `A = diag(1, 2)`, `u = e₀`, `v = e₁`, `M = 2`, with `m = 5`: `9/2` against `49/10`;
  and `A v = M v`: the same with `m = 1` and `M = 5`: `9/2` against `36/5`.
* `u ⬝ u = v ⬝ v`: `A = diag(1, 2)`, `u = 2 e₀`, `v = e₁`, `m = 1`, `M = 2`: `27` against `225/8`.

For the tool (`dotProduct_mulVec_eq_sum`): without `B bᵢ = μᵢ bᵢ`, `B = diag(1, 2)`, the standard
basis, `μ = 0`, `x = (1, 1)` give `3` against `0`.

The two Loewner hypotheses are Mathlib's `m • 1 ≤ A` and `A ≤ M • 1` under `open scoped
MatrixOrder` (`Matrix.le_iff` is `Iff.rfl`; checked by cold review r82). The proof derives, and
does not export, `Aᵀ = A`, every eigenvalue in `[m, M]` and `A` invertible; a later item that
needs them (item 111, steepest descent) can state them as lemmas.

Symmetry of `A` is not a separate hypothesis of the inequality: it comes with the positive
semidefinite `A − m I` (Mathlib's `PosSemidef` includes `IsHermitian`). Positive definiteness of
`A` follows from `A − m I ≥ 0` and `0 < m`, and is not assumed either.

## Mathlib at v4.34.0

Searched before this file was written (MATH-PLAN-library-2, row 82, re-run in order LEAN-27):
`kantorovich` 0 lines in pinned Mathlib, in Mathlib master and in the library. Used:
`Matrix.IsHermitian.eigenvectorBasis`, `mulVec_eigenvectorBasis`, `det_eq_prod_eigenvalues`,
`OrthonormalBasis.sum_repr'`, `PosSemidef.dotProduct_mulVec_nonneg`.
-/

open Matrix

namespace ClassicalLean.Algebra.Kantorovich

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The quadratic form of `B` in an orthonormal basis of its eigenvectors:
`x ⬝ B x = ∑ μᵢ (bᵢ ⬝ x)²`. No symmetry hypothesis: a real matrix with an orthonormal basis of
eigenvectors is symmetric anyway (proof from cold review r82, which found `Bᵀ = B` unneeded). -/
theorem dotProduct_mulVec_eq_sum {B : Matrix n n ℝ}
    (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)) {μ : n → ℝ}
    (hμ : ∀ i, B *ᵥ ⇑(b i) = μ i • ⇑(b i)) (x : n → ℝ) :
    x ⬝ᵥ (B *ᵥ x) = ∑ i, μ i * (⇑(b i) ⬝ᵥ x) ^ 2 := by
  have h := b.sum_repr' (WithLp.toLp 2 x)
  have h2 : ∑ i, (⇑(b i) ⬝ᵥ x) • ⇑(b i) = x := by
    have := congrArg (fun y : EuclideanSpace ℝ n ↦ (⇑y : n → ℝ)) h
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using this
  have hBx : B *ᵥ x = ∑ i, ((⇑(b i) ⬝ᵥ x) * μ i) • ⇑(b i) := by
    conv_lhs => rw [← h2]
    rw [mulVec_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mulVec_smul, hμ, smul_smul]
  rw [hBx, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [dotProduct_smul, smul_eq_mul, dotProduct_comm x]
  ring

/-- **The Kantorovich inequality.** For `m ≤ A ≤ M` in the Loewner order and `0 < m`:
`(xᵀ A x)(xᵀ A⁻¹ x) ≤ ((m + M)² / (4 m M)) (x ⬝ x)²`. -/
theorem dotProduct_mulVec_mul_inv_le {A : Matrix n n ℝ} {m M : ℝ} (hm : 0 < m)
    (hmA : (A - m • 1).PosSemidef) (hAM : (M • 1 - A).PosSemidef) (x : n → ℝ) :
    (x ⬝ᵥ (A *ᵥ x)) * (x ⬝ᵥ (A⁻¹ *ᵥ x)) ≤ (m + M) ^ 2 / (4 * m * M) * (x ⬝ᵥ x) ^ 2 := by
  have hAT : Aᵀ = A := by
    have h := hmA.1
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_smul,
      transpose_one, sub_left_inj] at h
    exact h
  have hAh : A.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hAT]
  set b := hAh.eigenvectorBasis
  set lam := hAh.eigenvalues
  have hb : ∀ i, A *ᵥ ⇑(b i) = lam i • ⇑(b i) := hAh.mulVec_eigenvectorBasis
  have hbb : ∀ i, ⇑(b i) ⬝ᵥ ⇑(b i) = 1 := fun i ↦ by
    have h := (orthonormal_iff_ite.mp b.orthonormal) i i
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, ↓reduceIte] using h
  have hlo : ∀ i, m ≤ lam i := fun i ↦ by
    have := hmA.dotProduct_mulVec_nonneg (⇑(b i))
    simpa [sub_mulVec, hb, smul_mulVec, hbb, dotProduct_sub] using this
  have hhi : ∀ i, lam i ≤ M := fun i ↦ by
    have := hAM.dotProduct_mulVec_nonneg (⇑(b i))
    simpa [sub_mulVec, hb, smul_mulVec, hbb, dotProduct_sub] using this
  have hpos : ∀ i, 0 < lam i := fun i ↦ hm.trans_le (hlo i)
  have hdet : IsUnit A.det := by
    rw [hAh.det_eq_prod_eigenvalues]
    exact (Finset.prod_ne_zero_iff.mpr fun i _ ↦ by
      simpa using (hpos i).ne').isUnit
  have hbinv : ∀ i, A⁻¹ *ᵥ ⇑(b i) = (lam i)⁻¹ • ⇑(b i) := fun i ↦ by
    have h1 : ⇑(b i) = (lam i)⁻¹ • (A *ᵥ ⇑(b i)) := by
      rw [hb, smul_smul, inv_mul_cancel₀ (hpos i).ne', one_smul]
    conv_lhs => rw [h1]
    rw [mulVec_smul, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
  have ha := dotProduct_mulVec_eq_sum b hb x
  have hbi := dotProduct_mulVec_eq_sum b hbinv x
  have hs := dotProduct_mulVec_eq_sum b (B := 1) (μ := fun _ ↦ 1)
    (fun i ↦ by rw [one_mulVec, one_smul]) x
  rw [one_mulVec] at hs
  set c := fun i ↦ ⇑(b i) ⬝ᵥ x
  -- each eigenvalue in `[m, M]` gives `λ + m M / λ ≤ m + M`
  have hsum : x ⬝ᵥ (A *ᵥ x) + m * M * (x ⬝ᵥ (A⁻¹ *ᵥ x)) ≤ (m + M) * (x ⬝ᵥ x) := by
    rw [ha, hbi, hs, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have hk : lam i + m * M * (lam i)⁻¹ ≤ m + M := by
      rw [← sub_nonneg]
      have hl := (hpos i).ne'
      have : m + M - (lam i + m * M * (lam i)⁻¹) = (lam i - m) * (M - lam i) / lam i := by
        field_simp
        ring
      rw [this]
      exact div_nonneg (mul_nonneg (sub_nonneg.2 (hlo i)) (sub_nonneg.2 (hhi i))) (hpos i).le
    have hc := sq_nonneg (⇑(b i) ⬝ᵥ x)
    nlinarith [mul_le_mul_of_nonneg_right hk hc]
  have ha0 : 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
    rw [ha]
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hpos i).le (sq_nonneg _)
  have hb0 : 0 ≤ x ⬝ᵥ (A⁻¹ *ᵥ x) := by
    rw [hbi]
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (inv_nonneg.2 (hpos i).le) (sq_nonneg _)
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i⟩⟩
  · simp [dotProduct, Finset.univ_eq_empty]
  have hM : 0 < M := (hpos i).trans_le (hhi i)
  have hmM : 0 < 4 * m * M := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hmM]
  set a := x ⬝ᵥ (A *ᵥ x)
  set q := x ⬝ᵥ (A⁻¹ *ᵥ x)
  set s := x ⬝ᵥ x
  have h2 : (a + m * M * q) ^ 2 ≤ ((m + M) * s) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsum 2
  nlinarith [sq_nonneg (a - m * M * q)]

/-- **The Kantorovich bound is reached** at an equal mix of eigenvectors: for `A` invertible,
`A u = m u`, `A v = M v` and `u ⬝ u = v ⬝ v`, the vector `u + v` gives equality. -/
theorem dotProduct_mulVec_mul_inv_add_eq {A : Matrix n n ℝ} (hA : IsUnit A.det) {m M : ℝ}
    {u v : n → ℝ} (hu : A *ᵥ u = m • u) (hv : A *ᵥ v = M • v) (huv : u ⬝ᵥ u = v ⬝ᵥ v) :
    ((u + v) ⬝ᵥ (A *ᵥ (u + v))) * ((u + v) ⬝ᵥ (A⁻¹ *ᵥ (u + v))) =
      (m + M) ^ 2 / (4 * m * M) * ((u + v) ⬝ᵥ (u + v)) ^ 2 := by
  have hinv : ∀ {w : n → ℝ} {t : ℝ}, A *ᵥ w = t • w → w ≠ 0 →
      t ≠ 0 ∧ A⁻¹ *ᵥ w = t⁻¹ • w := by
    intro w t hw hw0
    have hback : A⁻¹ *ᵥ (A *ᵥ w) = w := by rw [mulVec_mulVec, nonsing_inv_mul _ hA, one_mulVec]
    have ht : t ≠ 0 := by
      rintro rfl
      rw [hw, zero_smul, mulVec_zero] at hback
      exact hw0 hback.symm
    refine ⟨ht, ?_⟩
    rw [hw, mulVec_smul] at hback
    conv_rhs => rw [← hback]
    rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
  rcases eq_or_ne u 0 with rfl | hu0
  · have hv0 : v = 0 := dotProduct_self_eq_zero.mp (by rw [← huv]; simp)
    simp [hv0]
  have hv0 : v ≠ 0 := fun h ↦ hu0 (dotProduct_self_eq_zero.mp (by rw [huv, h]; simp))
  obtain ⟨hm, hiu⟩ := hinv hu hu0
  obtain ⟨hM, hiv⟩ := hinv hv hv0
  have hvu : v ⬝ᵥ u = u ⬝ᵥ v := dotProduct_comm v u
  simp only [mulVec_add, hu, hv, hiu, hiv, add_dotProduct, dotProduct_add, dotProduct_smul,
    smul_eq_mul, hvu, ← huv]
  field_simp
  ring

/-- The hypotheses of `dotProduct_mulVec_mul_inv_le` hold together: `A = 1`, `m = 1`, `M = 2`. -/
example : ∃ (A : Matrix (Fin 2) (Fin 2) ℝ) (m M : ℝ),
    0 < m ∧ (A - m • 1).PosSemidef ∧ (M • 1 - A).PosSemidef :=
  ⟨1, 1, 2, one_pos, by simpa using PosSemidef.zero, by
    rw [show (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - 1 = 1 by
      rw [two_smul, add_sub_cancel_right]]
    exact PosSemidef.one⟩

/-- The hypotheses of `dotProduct_mulVec_mul_inv_add_eq` hold together: `A = diag(1, 2)` with
its two unit eigenvectors. -/
example : ∃ (A : Matrix (Fin 2) (Fin 2) ℝ) (m M : ℝ) (u v : Fin 2 → ℝ),
    IsUnit A.det ∧ A *ᵥ u = m • u ∧ A *ᵥ v = M • v ∧ u ⬝ᵥ u = v ⬝ᵥ v := by
  refine ⟨diagonal ![1, 2], 1, 2, Pi.single 0 1, Pi.single 1 1, ?_, ?_, ?_, ?_⟩
  · simp [det_diagonal, Fin.prod_univ_two]
  · ext j; fin_cases j <;> simp [mulVec_diagonal]
  · ext j; fin_cases j <;> simp [mulVec_diagonal]
  · simp

end ClassicalLean.Algebra.Kantorovich
