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
* `quadForm_steepestStep_le` — item 111 of MATH-PLAN-library-2 (order LEAN-33): steepest descent
  with exact line search on `f(y) = yᵀ A y / 2` shrinks `f` by at least `((M − m)/(M + m))²` in one
  step, from the inequality above at `g = A x`. The proof is the draft `d111-r1-s2` (written by
  Claude Opus 5.5 through the Anthropic Batch API, the lane's API-CREDIT-1 work), adapted by order
  LEAN-33's session: inside this namespace, and its `field_simp <;> ring`, whose `ring` never ran,
  is `field_simp`.

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

/-- **Steepest descent with exact line search** (item 111 of MATH-PLAN-library-2; the draft
`d111-r1-s2`, written by Claude Opus 5.5 through the Anthropic Batch API, the lane's API-CREDIT-1
work, adapted by order LEAN-33's session). For `m ≤ A ≤ M` in the Loewner order and `0 < m`, one
step `x ↦ x − α g`, `g = A x`, `α = (g ⬝ g)/(g ⬝ A g)`, shrinks `f(y) = yᵀ A y / 2` to at most
`((M − m)/(M + m))²` times its value. At `g = 0` Lean's `0 / 0 = 0` makes the step not move, and
both sides are `0`. -/
theorem quadForm_steepestStep_le {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} {m M : ℝ} (hm : 0 < m)
    (hmA : (A - m • 1).PosSemidef) (hAM : (M • 1 - A).PosSemidef) (x : n → ℝ) :
    (x - ((A *ᵥ x) ⬝ᵥ (A *ᵥ x) / ((A *ᵥ x) ⬝ᵥ (A *ᵥ (A *ᵥ x)))) • (A *ᵥ x)) ⬝ᵥ
        (A *ᵥ (x - ((A *ᵥ x) ⬝ᵥ (A *ᵥ x) / ((A *ᵥ x) ⬝ᵥ (A *ᵥ (A *ᵥ x)))) • (A *ᵥ x))) / 2
      ≤ ((M - m) / (M + m)) ^ 2 * (x ⬝ᵥ (A *ᵥ x) / 2) := by
  have hAT : Aᵀ = A := by
    have h := hmA.1
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_smul,
      transpose_one, sub_left_inj] at h
    exact h
  have hAh : A.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hAT]
  set e := hAh.eigenvectorBasis
  set lam := hAh.eigenvalues
  have he : ∀ i, A *ᵥ ⇑(e i) = lam i • ⇑(e i) := hAh.mulVec_eigenvectorBasis
  have hee : ∀ i, ⇑(e i) ⬝ᵥ ⇑(e i) = 1 := fun i ↦ by
    have h := (orthonormal_iff_ite.mp e.orthonormal) i i
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, ↓reduceIte] using h
  have hlo : ∀ i, m ≤ lam i := fun i ↦ by
    have := hmA.dotProduct_mulVec_nonneg (⇑(e i))
    simpa [sub_mulVec, he, smul_mulVec, hee, dotProduct_sub] using this
  have hpos : ∀ i, 0 < lam i := fun i ↦ hm.trans_le (hlo i)
  have hdet : IsUnit A.det := by
    rw [hAh.det_eq_prod_eigenvalues]
    exact (Finset.prod_ne_zero_iff.mpr fun i _ ↦ by
      simpa using (hpos i).ne').isUnit
  set g := A *ᵥ x with hg
  rcases eq_or_ne g 0 with h0 | h0
  · have h0' : A *ᵥ x = 0 := by rw [← hg]; exact h0
    simp [h0, h0']
  have hv : x ᵥ* A = g := by rw [hg, ← vecMul_transpose, hAT]
  have h1 : x ⬝ᵥ (A *ᵥ g) = g ⬝ᵥ g := by rw [dotProduct_mulVec, hv]
  have h2 : g ⬝ᵥ (A⁻¹ *ᵥ g) = x ⬝ᵥ g := by
    rw [hg, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec, dotProduct_comm]
  have hK := dotProduct_mulVec_mul_inv_le hm hmA hAM g
  rw [h2] at hK
  have ha : 0 < g ⬝ᵥ g := by
    refine lt_of_le_of_ne ?_ (fun h ↦ h0 (dotProduct_self_eq_zero.mp h.symm))
    unfold dotProduct
    exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  have hmb : m * (g ⬝ᵥ g) ≤ g ⬝ᵥ (A *ᵥ g) := by
    have := hmA.dotProduct_mulVec_nonneg g
    simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec,
      dotProduct_smul, smul_eq_mul] at this
    linarith
  have hbM : g ⬝ᵥ (A *ᵥ g) ≤ M * (g ⬝ᵥ g) := by
    have := hAM.dotProduct_mulVec_nonneg g
    simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec,
      dotProduct_smul, smul_eq_mul] at this
    linarith
  have hb : 0 < g ⬝ᵥ (A *ᵥ g) := lt_of_lt_of_le (mul_pos hm ha) hmb
  have hb0 : g ⬝ᵥ (A *ᵥ g) ≠ 0 := hb.ne'
  have hmM : m ≤ M := by nlinarith
  have hMp : 0 < M := by linarith
  have hm0 : m ≠ 0 := hm.ne'
  have hM0 : M ≠ 0 := hMp.ne'
  have hs1 : M + m ≠ 0 := by linarith
  have hs2 : m + M ≠ 0 := by linarith
  have hy : (x - (g ⬝ᵥ g / (g ⬝ᵥ (A *ᵥ g))) • g) ⬝ᵥ
      (A *ᵥ (x - (g ⬝ᵥ g / (g ⬝ᵥ (A *ᵥ g))) • g)) =
      x ⬝ᵥ g - (g ⬝ᵥ g) ^ 2 / (g ⬝ᵥ (A *ᵥ g)) := by
    simp only [mulVec_sub, mulVec_smul, ← hg, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, h1]
    field_simp
    ring
  have hr : ((M - m) / (M + m)) ^ 2 = 1 - 4 * m * M / (m + M) ^ 2 := by
    field_simp
    ring
  have hkpos : 0 ≤ 4 * m * M / (m + M) ^ 2 := by positivity
  have hk : 4 * m * M / (m + M) ^ 2 * (x ⬝ᵥ g) * (g ⬝ᵥ (A *ᵥ g)) ≤ (g ⬝ᵥ g) ^ 2 := by
    calc 4 * m * M / (m + M) ^ 2 * (x ⬝ᵥ g) * (g ⬝ᵥ (A *ᵥ g))
        = 4 * m * M / (m + M) ^ 2 * ((g ⬝ᵥ (A *ᵥ g)) * (x ⬝ᵥ g)) := by ring
      _ ≤ 4 * m * M / (m + M) ^ 2 * ((m + M) ^ 2 / (4 * m * M) * (g ⬝ᵥ g) ^ 2) :=
          mul_le_mul_of_nonneg_left hK hkpos
      _ = (g ⬝ᵥ g) ^ 2 := by field_simp
  rw [hy, hr]
  have h3 : 4 * m * M / (m + M) ^ 2 * (x ⬝ᵥ g) ≤ (g ⬝ᵥ g) ^ 2 / (g ⬝ᵥ (A *ᵥ g)) := by
    rw [le_div_iff₀ hb]
    linarith [hk]
  nlinarith [h3]

end ClassicalLean.Algebra.Kantorovich

/-- The hypotheses of `quadForm_steepestStep_le` hold together: `A = diag(1, 2)` on `Fin 2`, with
the Loewner bounds `m = 1 < M = 2` (`A − I = diag(0, 1)` and `2 I − A = diag(1, 0)` are positive
semidefinite), and the start `x = (1, 1)`: `A x = (1, 2) ≠ 0`, so the step moves, and `x` is not
an eigenvector of `A`, so the step does not land on `0` (the left side is `1/9`, the right side
`1/6`). -/
example := ClassicalLean.Algebra.Kantorovich.quadForm_steepestStep_le (n := Fin 2)
  (A := diagonal ![1, 2]) (m := 1) (M := 2) one_pos
  (by
    rw [show (diagonal ![1, 2] : Matrix (Fin 2) (Fin 2) ℝ) - (1 : ℝ) • 1 = diagonal ![0, 1] by
      ext i j; fin_cases i <;> fin_cases j <;> norm_num]
    exact posSemidef_diagonal_iff.mpr fun i ↦ by fin_cases i <;> norm_num)
  (by
    rw [show (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - diagonal ![1, 2] = diagonal ![1, 0] by
      ext i j; fin_cases i <;> fin_cases j <;> norm_num]
    exact posSemidef_diagonal_iff.mpr fun i ↦ by fin_cases i <;> norm_num)
  (x := ![1, 1])

open Matrix in
/-- The hypotheses of `dotProduct_mulVec_mul_inv_le` hold together: `A = [[2, 1], [1, 3]]`, `m = 1`,
`M = 4`, `x = (1, 2)`. `A − I = [[1, 1], [1, 2]] = Bᵀ B` with `B = [[1, 1], [0, 1]]`, and
`4 I − A = [[2, −1], [−1, 1]] = Cᵀ C` with `C = [[1, −1], [1, 0]]`, so both are positive
semidefinite; the eigenvalues of `A`, `(5 ± √5) / 2`, lie strictly inside `[1, 4]` (not `A = 1`,
where `A − m I = 0`), and `x` is not an eigenvector (`A x = (4, 7)`). -/
example := ClassicalLean.Algebra.Kantorovich.dotProduct_mulVec_mul_inv_le (n := Fin 2)
  (A := !![2, 1; 1, 3]) (m := 1) (M := 4) one_pos
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
  (x := ![1, 2])

open Matrix in
/-- The hypotheses of `dotProduct_mulVec_mul_inv_add_eq` hold together: `A = [[2, 1], [1, 2]]`
(determinant `3`), `u = (1, −1)` with `A u = u` (`m = 1`) and `v = (1, 1)` with `A v = 3 v`
(`M = 3`), `u ⬝ u = v ⬝ v = 2`: two different eigenvalues, and eigenvectors that are not on the
axes (not a diagonal matrix with its unit vectors). -/
example := ClassicalLean.Algebra.Kantorovich.dotProduct_mulVec_mul_inv_add_eq (n := Fin 2)
  (A := !![2, 1; 1, 2]) (isUnit_iff_ne_zero.mpr (by rw [det_fin_two_of]; norm_num))
  (m := 1) (M := 3) (u := ![1, -1]) (v := ![1, 1])
  (by ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num)
  (by ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num)
  (by simp [dotProduct, Fin.sum_univ_two])
