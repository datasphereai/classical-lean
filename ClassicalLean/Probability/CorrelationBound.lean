/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Analysis.Gruss
import ClassicalLean.Probability.LinearPrediction

/-!
# The covariance's Cauchy–Schwarz inequality, and the correlation in `[−1, 1]`

On a probability space, for `X` and `Y` with finite second moments (`MemLp X 2 μ`,
`MemLp Y 2 μ`):

* `covariance_sq_le_variance_mul` — `cov[X, Y]² ≤ Var X · Var Y`;
* `abs_correlation_le_one` — the library's correlation
  `correlation X Y μ = cov[X, Y] / √(Var X · Var Y)` (`ClassicalLean.Probability.LinearPrediction`)
  has absolute value at most `1`. When `Var X · Var Y = 0` the root is `0` and Lean's `x / 0 = 0`
  makes the correlation `0`.

Bridge row 155 of MATH-PLAN-library-2's bridges file (order CLOUD-MATH-5), stated and proved by the
Claude Code cloud session of that order from the row's sketch; no draft. The measure is a
probability measure, as the row says.

The proof. For every `t`, `0 ≤ Var[t X + Y] = Var X · t² + 2 cov[X, Y] · t + Var Y`, a quadratic in
`t` that is never negative, so its discriminant `(2 cov)² − 4 Var X · Var Y` is at most `0`
(Mathlib's `discrim_le_zero`). This is the step inside the proof of `abs_covariance_le_mul_div_four`
(`ClassicalLean.Analysis.Gruss`), copied here; that module is not changed. The second theorem takes
square roots: `|cov[X, Y]| ≤ √(Var X · Var Y)`.
-/

open MeasureTheory ProbabilityTheory
open ClassicalLean.Probability.LinearPrediction

namespace ClassicalLean.Probability.CorrelationBound

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [hμ : IsProbabilityMeasure μ]
  {X Y : Ω → ℝ}

/-- **The covariance's Cauchy–Schwarz inequality.** On a probability space, for `X` and `Y` in
`L²`, `cov[X, Y]² ≤ Var X · Var Y`. -/
theorem covariance_sq_le_variance_mul (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    cov[X, Y; μ] ^ 2 ≤ variance X μ * variance Y μ := by
  -- the variance of `t X + Y` is never negative: a quadratic in `t` with no two real roots
  have hquad : ∀ t : ℝ, 0 ≤ Var[X; μ] * (t * t) + 2 * cov[X, Y; μ] * t + Var[Y; μ] := by
    intro t
    calc 0 ≤ Var[t • X + Y; μ] := variance_nonneg _ _
      _ = Var[X; μ] * (t * t) + 2 * cov[X, Y; μ] * t + Var[Y; μ] := by
          rw [variance_add (hX.const_smul t) hY, variance_smul, covariance_smul_left]
          ring
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  nlinarith [hdisc]

/-- **The correlation lies in `[−1, 1]`.** On a probability space, for `X` and `Y` in `L²`,
`|correlation X Y μ| ≤ 1` (when `Var X · Var Y = 0`, Lean's `x / 0 = 0` makes it `0`). -/
theorem abs_correlation_le_one (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    |correlation X Y μ| ≤ 1 := by
  rw [correlation, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_one_of_le₀ (Real.abs_le_sqrt (covariance_sq_le_variance_mul hX hY))
    (Real.sqrt_nonneg _)

end ClassicalLean.Probability.CorrelationBound

open scoped NNReal in
/-- The hypotheses of `covariance_sq_le_variance_mul` hold together: two fair coin flips, the
uniform probability `μ = (1/4) · count` on the four sequences `Ω = Fin 2 → Bool` (a probability
measure: its total mass is `4⁻¹ · 4 = 1`, proved in the block, since Lean does not find the
instance); `X = ±1` by the first flip and `Y = X + Z`, with `Z = ±1` by the second; both are in
`L²` (a finite space). What moves: neither is constant, they are neither independent nor
proportional, and `cov[X, Y] = Var X = 1`, `Var Y = 2`, so the inequality reads `1 ≤ 2`, strict. -/
example := ClassicalLean.Probability.CorrelationBound.covariance_sq_le_variance_mul
  (Ω := Fin 2 → Bool) (μ := (4⁻¹ : ℝ≥0) • Measure.count)
  (hμ := ⟨by
    simp only [Measure.smul_apply, Measure.count_univ, ENat.card_eq_coe_fintype_card,
      Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Nat.reducePow, Nat.cast_ofNat, ENat.toENNReal_ofNat, ENNReal.smul_def, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_inv, ENNReal.coe_ofNat, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩)
  (X := fun ω ↦ if ω 0 then 1 else -1)
  (Y := fun ω ↦ (if ω 0 then 1 else -1) + (if ω 1 then 1 else -1))
  MemLp.of_discrete MemLp.of_discrete

open scoped NNReal in
/-- The hypotheses of `abs_correlation_le_one` hold together: the same two fair coin flips, `X = ±1`
by the first flip and `Y = X + Z` with `Z = ±1` by the second, both in `L²`. What moves: with
`cov[X, Y] = 1`, `Var X = 1` and `Var Y = 2`, the correlation is `1/√2`, strictly inside
`(−1, 1)`; the root `√2` is not `0`, so Lean's `x / 0 = 0` plays no part. -/
example := ClassicalLean.Probability.CorrelationBound.abs_correlation_le_one
  (Ω := Fin 2 → Bool) (μ := (4⁻¹ : ℝ≥0) • Measure.count)
  (hμ := ⟨by
    simp only [Measure.smul_apply, Measure.count_univ, ENat.card_eq_coe_fintype_card,
      Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Nat.reducePow, Nat.cast_ofNat, ENat.toENNReal_ofNat, ENNReal.smul_def, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_inv, ENNReal.coe_ofNat, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩)
  (X := fun ω ↦ if ω 0 then 1 else -1)
  (Y := fun ω ↦ (if ω 0 then 1 else -1) + (if ω 1 then 1 else -1))
  MemLp.of_discrete MemLp.of_discrete
