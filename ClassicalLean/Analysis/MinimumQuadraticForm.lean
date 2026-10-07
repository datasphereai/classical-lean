/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The least value of a positive definite quadratic form on weights summing to one

For a real positive definite matrix `S` (for example a covariance matrix), let
`c = 1ᵀ S⁻¹ 1` and `w* = S⁻¹ 1 / c`.

* `zero_lt_onesInvOnes`: `c > 0`.
* `sum_minWeights`: the weights `w*` sum to `1`.
* `quadForm_eq`: for every `w` with `∑ w = 1`, `wᵀ S w = (w - w*)ᵀ S (w - w*) + 1 / c`.
* `inv_onesInvOnes_le_quadForm`, `quadForm_minWeights`: so `1 / c` is the least value of `wᵀ S w`
  over weights summing to `1`, reached at `w*`, and (`quadForm_eq_inv_iff`) only there.

When `S` is the covariance matrix of several assets, `wᵀ S w` is the variance of the mix with
weights `w`, so `w*` is the mix with the smallest variance and `1 / c` is that variance.

## What Mathlib provides

`Matrix.PosDef`, `PosDef.inv` (the inverse is positive definite), `PosDef.isUnit`,
`PosDef.dotProduct_mulVec_pos`, `Matrix.mul_nonsing_inv`. The library's `Simplex.SecondOrder` and
`Statistics.GaussMarkov` work with positive semidefinite matrices but not with this constrained
minimum, so they are not imported.
-/

open Matrix

namespace ClassicalLean.Analysis.MinimumQuadraticForm

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `c = 1ᵀ S⁻¹ 1`. -/
noncomputable def onesInvOnes (S : Matrix n n ℝ) : ℝ := 1 ⬝ᵥ (S⁻¹ *ᵥ 1)

/-- The weights `w* = S⁻¹ 1 / (1ᵀ S⁻¹ 1)`. -/
noncomputable def minWeights (S : Matrix n n ℝ) : n → ℝ := (onesInvOnes S)⁻¹ • (S⁻¹ *ᵥ 1)

omit [DecidableEq n] in
/-- A real positive definite matrix gives the same value on `(v, w)` and `(w, v)`. -/
theorem dotProduct_mulVec_comm {S : Matrix n n ℝ} (hS : S.PosDef) (v w : n → ℝ) :
    v ⬝ᵥ (S *ᵥ w) = w ⬝ᵥ (S *ᵥ v) := by
  have hT : Sᵀ = S := by
    have := hS.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  rw [dotProduct_mulVec, ← hT, vecMul_transpose, hT, dotProduct_comm]

/-- **`c` is positive.** For positive definite `S` on a nonempty index set, `1ᵀ S⁻¹ 1 > 0`. -/
theorem zero_lt_onesInvOnes [Nonempty n] {S : Matrix n n ℝ} (hS : S.PosDef) :
    0 < onesInvOnes S := by
  have h1 : (1 : n → ℝ) ≠ 0 := fun h ↦ by
    simpa using congr_fun h (Classical.arbitrary n)
  simpa [onesInvOnes] using hS.inv.dotProduct_mulVec_pos h1

theorem mulVec_minWeights {S : Matrix n n ℝ} (hS : S.PosDef) :
    S *ᵥ minWeights S = (onesInvOnes S)⁻¹ • (1 : n → ℝ) := by
  rw [minWeights, mulVec_smul, mulVec_mulVec,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det S).mp hS.isUnit), one_mulVec]

/-- **The weights `w*` sum to `1`.** -/
theorem sum_minWeights [Nonempty n] {S : Matrix n n ℝ} (hS : S.PosDef) :
    ∑ i, minWeights S i = 1 := by
  rw [← one_dotProduct, minWeights, dotProduct_smul, smul_eq_mul, ← onesInvOnes,
    inv_mul_cancel₀ (zero_lt_onesInvOnes hS).ne']

/-- **The splitting identity.** For positive definite `S` and weights `w` summing to `1`:
`wᵀ S w = (w - w*)ᵀ S (w - w*) + 1 / c`. -/
theorem quadForm_eq [Nonempty n] {S : Matrix n n ℝ} (hS : S.PosDef) {w : n → ℝ}
    (hw : ∑ i, w i = 1) :
    w ⬝ᵥ (S *ᵥ w) =
      (w - minWeights S) ⬝ᵥ (S *ᵥ (w - minWeights S)) + (onesInvOnes S)⁻¹ := by
  have hc := (zero_lt_onesInvOnes hS).ne'
  have h1 : w ⬝ᵥ (S *ᵥ minWeights S) = (onesInvOnes S)⁻¹ := by
    rw [mulVec_minWeights hS, dotProduct_smul, dotProduct_one, hw, smul_eq_mul, mul_one]
  have h2 : minWeights S ⬝ᵥ (S *ᵥ w) = (onesInvOnes S)⁻¹ := by
    rw [dotProduct_mulVec_comm hS, h1]
  have h3 : minWeights S ⬝ᵥ (S *ᵥ minWeights S) = (onesInvOnes S)⁻¹ := by
    rw [mulVec_minWeights hS, dotProduct_smul, dotProduct_one, sum_minWeights hS, smul_eq_mul,
      mul_one]
  rw [mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, h1, h2, h3]
  ring

/-- **The weights `w*` reach `1 / c`.** `w*ᵀ S w* = 1 / (1ᵀ S⁻¹ 1)`. -/
theorem quadForm_minWeights [Nonempty n] {S : Matrix n n ℝ} (hS : S.PosDef) :
    minWeights S ⬝ᵥ (S *ᵥ minWeights S) = (onesInvOnes S)⁻¹ := by
  rw [quadForm_eq hS (sum_minWeights hS), sub_self, mulVec_zero, dotProduct_zero, zero_add]

/-- **The least variance of a mix.** For positive definite `S` and weights `w` summing to `1`:
`1 / (1ᵀ S⁻¹ 1) ≤ wᵀ S w`. For a trader: with covariance matrix `S`, no mix of the assets (weights
summing to 1, short positions allowed) has variance below `1 / (1ᵀ S⁻¹ 1)`. -/
theorem inv_onesInvOnes_le_quadForm [Nonempty n] {S : Matrix n n ℝ} (hS : S.PosDef)
    {w : n → ℝ} (hw : ∑ i, w i = 1) : (onesInvOnes S)⁻¹ ≤ w ⬝ᵥ (S *ᵥ w) := by
  rw [quadForm_eq hS hw, le_add_iff_nonneg_left]
  rcases eq_or_ne (w - minWeights S) 0 with h | h
  · simp [h]
  · simpa using (hS.dotProduct_mulVec_pos h).le

/-- **Only `w*` has the least variance.** For positive definite `S` and weights `w` summing to
`1`: `wᵀ S w = 1 / (1ᵀ S⁻¹ 1)` exactly when `w = S⁻¹ 1 / (1ᵀ S⁻¹ 1)`. For a trader: the
smallest-variance mix is unique, and it is `S⁻¹ 1` scaled to sum to 1. -/
theorem quadForm_eq_inv_iff [Nonempty n] {S : Matrix n n ℝ} (hS : S.PosDef) {w : n → ℝ}
    (hw : ∑ i, w i = 1) : w ⬝ᵥ (S *ᵥ w) = (onesInvOnes S)⁻¹ ↔ w = minWeights S := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ quadForm_minWeights hS⟩
  rw [quadForm_eq hS hw, add_eq_right] at h
  by_contra hne
  have := hS.dotProduct_mulVec_pos (sub_ne_zero.mpr hne)
  simp only [star_trivial] at this
  linarith

end ClassicalLean.Analysis.MinimumQuadraticForm
