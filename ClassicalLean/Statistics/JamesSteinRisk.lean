/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Statistics.JamesStein
import ClassicalLean.Probability.ChiSquared

/-!
# The risk of the James–Stein estimator at the origin

Under `normalVec d 0`, the normal law with mean `0` and identity covariance in dimension `d`
(`ClassicalLean.Statistics.normalVec`, the product of `d` laws `gaussianReal 0 1`), the squared
length `sqNorm x = ∑ i, x i ^ 2` has the chi-squared law with `d` degrees of freedom, the gamma law
of shape `d / 2` and rate `1 / 2`. From this:

* `integral_inv_sqNorm_zero` — the inverse moment: for `d ≥ 3`,
  `∫ x, (sqNorm x)⁻¹ ∂normalVec d 0 = 1 / (d − 2)`.
* `integral_sqNorm_jamesStein_zero` — the James–Stein estimator `(1 − (d − 2)/‖x‖²) x` has mean
  squared error `2` at the origin, in every dimension `d ≥ 3`:
  `∫ x, sqNorm (jamesStein x) ∂normalVec d 0 = 2`, against the mean squared error `d` of `x`
  itself (`integral_sqNorm_sub`).

Bridge row 161 of MATH-PLAN-library-2's bridges file (order CLOUD-MATH-4), stated and proved by the
Claude Code cloud session of that order from the row's sketch; no draft. The mean `θ = 0` is the
zero vector of `Fin d → ℝ`, and the risk `∫ x, sqNorm (jamesStein x - θ) ∂normalVec d θ` at
`θ = 0` is written without the `- 0`. The dimension `d` is a natural number, cast to `ℝ` in
`1 / ((d : ℝ) - 2)`.

The proof. The coordinates `x ↦ x i` are independent under the product measure (`iIndepFun_pi`),
each with the law `gaussianReal 0 1` (`measurePreserving_eval`), so the library's chi-squared law
(`ClassicalLean.Probability.ChiSquared.hasLaw_sum_sq_gaussian`) gives `sqNorm` the law
`gammaMeasure (d / 2) (1 / 2)`. Its inverse moment is an integral against Mathlib's gamma density,
`r ^ a / Γ(a) · ∫₀^∞ t ^ (a − 2) e^(−r t) dt = r ^ a / Γ(a) · Γ(a − 1) / r ^ (a − 1)`
(`Real.integral_rpow_mul_exp_neg_mul_Ioi`), which is `r / (a − 1)` by `Γ(a) = (a − 1) Γ(a − 1)`
(`Real.Gamma_add_one`); at `a = d / 2`, `r = 1 / 2` it is `1 / (d − 2)`, finite since `a > 1`. The
library's risk identity `integral_sqNorm_jamesStein_sub_eq` at `θ = 0` then gives
`d − (d − 2)² / (d − 2) = 2`.
-/

open MeasureTheory ProbabilityTheory Set
open ClassicalLean.Statistics ClassicalLean.Probability.ChiSquared

namespace ClassicalLean.Statistics.JamesSteinRisk

/-- **The inverse moment of the chi-squared law.** For `X` normal with mean `0` and identity
covariance in dimension `d ≥ 3`, `E[1/‖X‖²] = 1/(d − 2)`. -/
theorem integral_inv_sqNorm_zero {d : ℕ} (hd : 3 ≤ d) :
    ∫ x, (sqNorm x)⁻¹ ∂normalVec d 0 = 1 / ((d : ℝ) - 2) := by
  have hd0 : 0 < d := by omega
  have hlaw : HasLaw (fun x : Fin d → ℝ => ∑ i, x i ^ 2) (gammaMeasure ((d : ℝ) / 2) (1 / 2))
      (normalVec d 0) := by
    unfold normalVec
    exact hasLaw_sum_sq_gaussian hd0 (X := fun (i : Fin d) (x : Fin d → ℝ) => x i)
      (fun i => measurable_pi_apply i) (iIndepFun_pi fun _ => aemeasurable_id)
      fun i => ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
  have h1 : ∫ x, (sqNorm x)⁻¹ ∂normalVec d 0 =
      ∫ y, y⁻¹ ∂gammaMeasure ((d : ℝ) / 2) (1 / 2) :=
    hlaw.integral_comp (f := fun y : ℝ => y⁻¹) measurable_inv.aestronglyMeasurable
  set a : ℝ := (d : ℝ) / 2 with ha_def
  set r : ℝ := 1 / 2 with hr_def
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have ha1 : 0 < a - 1 := by rw [ha_def]; linarith
  have ha0 : 0 < a := by linarith
  have hr0 : 0 < r := by norm_num [hr_def]
  have hmeas : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  rw [h1, gammaMeasure, integral_withDensity_eq_integral_toReal_smul hmeas
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha0 hr0 _), smul_eq_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0) fun y hy => by
    rw [mem_Ioi, not_lt] at hy
    rcases hy.lt_or_eq with hy | hy
    · simp [gammaPDFReal, not_le.mpr hy]
    · simp [hy]]
  have hcongr : ∀ y ∈ Ioi (0 : ℝ), gammaPDFReal a r y * y⁻¹ =
      r ^ a / Real.Gamma a * (y ^ (a - 1 - 1) * Real.exp (-(r * y))) := fun y hy => by
    rw [mem_Ioi] at hy
    rw [gammaPDFReal, Real.rpow_sub_one hy.ne' (a - 1)]
    simp only [hy.le, ↓reduceIte]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi ha1 hr0]
  have hG : Real.Gamma a = (a - 1) * Real.Gamma (a - 1) := by
    rw [← Real.Gamma_add_one ha1.ne', sub_add_cancel]
  have hG1 : 0 < Real.Gamma (a - 1) := Real.Gamma_pos_of_pos ha1
  have hra : r ^ a = r ^ (a - 1) * r := by
    rw [← Real.rpow_add_one hr0.ne', sub_add_cancel]
  have hinv : (1 / r) ^ (a - 1) = (r ^ (a - 1))⁻¹ := by
    rw [one_div, Real.inv_rpow hr0.le]
  have hpos : 0 < r ^ (a - 1) := Real.rpow_pos_of_pos hr0 _
  rw [hG, hra, hinv]
  field_simp
  have hd2 : (d : ℝ) - 2 ≠ 0 := by linarith
  rw [ha_def, hr_def]
  field_simp

/-- **The James–Stein risk at the origin is `2`.** For `X` normal with mean `0` and identity
covariance in dimension `d ≥ 3`, the James–Stein estimator `(1 − (d − 2)/‖X‖²) X` has mean
squared error `E ‖JS(X)‖² = 2`, in every such dimension, against the mean squared error `d` of `X`
itself. -/
theorem integral_sqNorm_jamesStein_zero {d : ℕ} (hd : 3 ≤ d) :
    ∫ x, sqNorm (jamesStein x) ∂normalVec d 0 = 2 := by
  have h := integral_sqNorm_jamesStein_sub_eq hd (0 : Fin d → ℝ)
  simp only [sub_zero] at h
  have hd2 : (d : ℝ) - 2 ≠ 0 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [h, integral_inv_sqNorm_zero hd]
  field_simp
  ring

end ClassicalLean.Statistics.JamesSteinRisk

/-- The hypotheses of `integral_inv_sqNorm_zero` hold together: dimension `d = 4`, above the
least dimension `3` the theorem allows, so `d − 2 = 2` is away from the boundary `d = 2` where the
inverse moment is infinite, and the value is `1/2`. -/
example := ClassicalLean.Statistics.JamesSteinRisk.integral_inv_sqNorm_zero (d := 4) (by norm_num)

/-- The hypotheses of `integral_sqNorm_jamesStein_zero` hold together: dimension `d = 4`, above the
least dimension `3` the theorem allows, so `d − 2 = 2` is away from the boundary `d = 2` where the
estimator is `X` itself; the risk `2` is then below the risk `4` of `X`. -/
example := ClassicalLean.Statistics.JamesSteinRisk.integral_sqNorm_jamesStein_zero (d := 4)
  (by norm_num)
