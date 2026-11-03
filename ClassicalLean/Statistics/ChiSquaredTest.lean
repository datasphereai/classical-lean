/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Probability.ChiSquared
import ClassicalLean.Statistics.NeymanPearson

/-!
# The chi-squared test of a normal variance is uniformly most powerful

Bridge 169 of `MATH-PLAN-library-2-bridges-2.md` (order CLOUD-MATH-7), joining
`ClassicalLean.Probability.ChiSquared` and `ClassicalLean.Statistics.NeymanPearson`.

* `isUniformlyMostPowerful_sum_sq_gaussian` — for `k ≥ 1` independent `N(0, v)` draws (density
  `∏ i, gaussianPDFReal 0 v (x i)` against Lebesgue measure on `Fin k → ℝ`, `v > 0`) and every
  `c`, the test rejecting when `∑ i, x i ^ 2 > c` is uniformly most powerful for `v ≤ v₀` against
  `v > v₀` at the level `α = P(χ²ₖ > c / v₀)`, the chi-squared law being Mathlib's
  `gammaMeasure (k / 2) (1 / 2)`.

The proof. The density of the `k` draws is `(2πv)^(−k/2) exp(−S/(2v))` with `S = ∑ i, x i ^ 2`,
so for `v < v'` the ratio of the densities is `(v/v')^(k/2) exp(S (1/v − 1/v')/2)`, a
nondecreasing function of `S` (`HasMonotoneLikelihoodRatio`). Karlin–Rubin
(`isUniformlyMostPowerful_of_monotoneLikelihoodRatio`, `γ = 0`) makes the threshold test uniformly
most powerful at its size under `v₀`. That size is `P_{v₀}(S > c)` (`integral_thresholdTest`):
under `v₀` the draws are the product of `k` laws `N(0, v₀)`, the coordinates `x i / √v₀` are
independent standard normals, and `hasLaw_sum_sq_gaussian` gives `S / v₀` the law
`gammaMeasure (k/2) (1/2)`.

The statement was written by order LEAN-38 (a reading order) and elaborated there stated without
a proof; this module proves it word for word.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ClassicalLean.Statistics.ChiSquaredTest

/-- **The chi-squared test of a normal variance is uniformly most powerful.** For `k ≥ 1`
independent `N(0, v)` draws (density `∏ i, gaussianPDFReal 0 v (x i)` against Lebesgue measure on
`Fin k → ℝ`), the test that rejects when `∑ i, x i ^ 2 > c` is uniformly most powerful for
`v ≤ v₀` against `v > v₀` at the level `α = P(χ²ₖ > c / v₀)`, the chi-squared law being Mathlib's
`gammaMeasure (k / 2) (1 / 2)`. Bridge 169 of `MATH-PLAN-library-2-bridges-2.md`. -/
theorem isUniformlyMostPowerful_sum_sq_gaussian {k : ℕ} (hk : 0 < k)
    (v₀ : Set.Ioi (0 : ℝ≥0)) (c : ℝ) :
    ClassicalLean.Statistics.IsUniformlyMostPowerful (volume : Measure (Fin k → ℝ))
      (fun (v : Set.Ioi (0 : ℝ≥0)) (x : Fin k → ℝ) ↦ ∏ i, gaussianPDFReal 0 v.1 (x i)) v₀
      ((gammaMeasure ((k : ℝ) / 2) (1 / 2)).real (Set.Ioi (c / (v₀.1 : ℝ))))
      (ClassicalLean.Statistics.thresholdTest (fun x ↦ ∑ i, x i ^ 2) c 0) := by
  have hSm : Measurable (fun x : Fin k → ℝ ↦ ∑ i, x i ^ 2) := by fun_prop
  have hFm : ∀ v : ℝ≥0, Measurable (fun x : Fin k → ℝ ↦ ∏ i, gaussianPDFReal 0 v (x i)) :=
    fun v ↦ Finset.measurable_prod _ fun i _ ↦
      (measurable_gaussianPDFReal 0 v).comp (measurable_pi_apply i)
  have hf0 : ∀ v : ℝ≥0, 0 ≤ (fun x : Fin k → ℝ ↦ ∏ i, gaussianPDFReal 0 v (x i)) :=
    fun v x ↦ Finset.prod_nonneg fun i _ ↦ gaussianPDFReal_nonneg 0 v (x i)
  have hint : ∀ v : ℝ≥0, Integrable (fun x : Fin k → ℝ ↦ ∏ i, gaussianPDFReal 0 v (x i)) := by
    intro v
    rw [MeasureTheory.volume_pi]
    exact Integrable.fintype_prod fun _ ↦ integrable_gaussianPDFReal 0 v
  have hf1 : ∀ v : Set.Ioi (0 : ℝ≥0), ∫ x : Fin k → ℝ, ∏ i, gaussianPDFReal 0 v.1 (x i) = 1 := by
    intro v
    rw [MeasureTheory.volume_pi, integral_fintype_prod_eq_prod]
    simp [integral_gaussianPDFReal_eq_one 0 (ne_of_gt v.2)]
  -- the monotone likelihood ratio in `S = ∑ i, x i ^ 2`
  have hmlr : ClassicalLean.Statistics.HasMonotoneLikelihoodRatio
      (fun (v : Set.Ioi (0 : ℝ≥0)) (x : Fin k → ℝ) ↦ ∏ i, gaussianPDFReal 0 v.1 (x i))
      (fun x ↦ ∑ i, x i ^ 2) := by
    intro v v' hlt
    have hv0 : (0 : ℝ) < v.1 := v.2
    have hv0' : (0 : ℝ) < v'.1 := v'.2
    have hlt' : (v.1 : ℝ) < v'.1 := hlt
    set a := √(2 * Real.pi * v.1) / √(2 * Real.pi * v'.1) with ha
    set d := (2 * (v.1 : ℝ))⁻¹ - (2 * (v'.1 : ℝ))⁻¹ with hd
    have ha0 : 0 < a :=
      div_pos (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr (by positivity))
    have hd0 : 0 ≤ d := by
      rw [hd, sub_nonneg]
      exact inv_anti₀ (by positivity) (by linarith)
    have hcoord : ∀ y : ℝ, gaussianPDFReal 0 v'.1 y =
        a * Real.exp (y ^ 2 * d) * gaussianPDFReal 0 v.1 y := by
      intro y
      simp only [gaussianPDFReal_def, sub_zero, ha, hd]
      have h1 : √(2 * Real.pi * v.1) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
      have h2 : √(2 * Real.pi * v'.1) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
      have hexp : Real.exp (y ^ 2 * ((2 * (v.1 : ℝ))⁻¹ - (2 * (v'.1 : ℝ))⁻¹)) *
          Real.exp (-y ^ 2 / (2 * v.1)) = Real.exp (-y ^ 2 / (2 * v'.1)) := by
        rw [← Real.exp_add]
        congr 1
        field_simp
        ring
      have hconst : √(2 * Real.pi * v.1) / √(2 * Real.pi * v'.1) * (√(2 * Real.pi * v.1))⁻¹ =
          (√(2 * Real.pi * v'.1))⁻¹ := by
        field_simp
      rw [← hexp, ← hconst]
      ring
    refine ⟨fun t ↦ a ^ k * Real.exp (t * d), fun s t hst ↦ ?_, fun t ↦ by positivity,
      fun x ↦ ?_⟩
    · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hst hd0))
        (by positivity)
    · simp only [hcoord, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, ← Real.exp_sum, Finset.sum_mul]
  have key := ClassicalLean.Statistics.isUniformlyMostPowerful_of_monotoneLikelihoodRatio hSm
    (fun v ↦ hint v.1) (fun v ↦ hf0 v.1) hf1 hmlr v₀ c (γ := 0) ⟨le_rfl, zero_le_one⟩
  -- the size: under `v₀` the draws have the law of `k` independent `N(0, v₀)`
  set P := Measure.pi (fun _ : Fin k ↦ gaussianReal 0 v₀.1) with hP
  have hv : v₀.1 ≠ 0 := ne_of_gt v₀.2
  have hdens : (volume : Measure (Fin k → ℝ)).withDensity
      (fun x ↦ ENNReal.ofReal (∏ i, gaussianPDFReal 0 v₀.1 (x i))) = P := by
    symm
    refine Measure.pi_eq fun s hs ↦ ?_
    rw [withDensity_apply _ (MeasurableSet.univ_pi hs), MeasureTheory.volume_pi,
      Measure.restrict_pi_pi, ← ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg
        (fun i _ ↦ setIntegral_nonneg (hs i) fun y _ ↦ gaussianPDFReal_nonneg 0 v₀.1 y)]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [gaussianReal_apply 0 hv, ofReal_integral_eq_lintegral_ofReal
        (integrable_gaussianPDFReal 0 v₀.1).integrableOn
        (ae_of_all _ fun y ↦ gaussianPDFReal_nonneg 0 v₀.1 y)]
      rfl
    · exact Integrable.fintype_prod fun i ↦ (integrable_gaussianPDFReal 0 v₀.1).integrableOn
    · exact ae_of_all _ fun x ↦ Finset.prod_nonneg fun i _ ↦ gaussianPDFReal_nonneg 0 v₀.1 (x i)
  -- the size as an integral against `P` (the step of NeymanPearson's private
  -- `integral_mul_eq_integral_withDensity`, copied)
  have hmul : ∫ x : Fin k → ℝ, ClassicalLean.Statistics.thresholdTest (fun x ↦ ∑ i, x i ^ 2) c 0 x *
        ∏ i, gaussianPDFReal 0 v₀.1 (x i) =
      ∫ x : Fin k → ℝ, ClassicalLean.Statistics.thresholdTest (fun x ↦ ∑ i, x i ^ 2) c 0 x ∂P := by
    rw [← hdens, show (fun x : Fin k → ℝ ↦ ENNReal.ofReal (∏ i, gaussianPDFReal 0 v₀.1 (x i))) =
        fun x ↦ (((Real.toNNReal ∘ fun x ↦ ∏ i, gaussianPDFReal 0 v₀.1 (x i)) x : ℝ≥0) : ENNReal)
        from rfl, integral_withDensity_eq_integral_smul (measurable_real_toNNReal.comp (hFm _))]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [Function.comp_apply, NNReal.smul_def, smul_eq_mul,
      Real.coe_toNNReal _ (hf0 v₀.1 x)]
    ring
  -- `S / v₀` is a sum of `k` squared standard normals under `P`
  have hv0 : (0 : ℝ) < v₀.1 := v₀.2
  set r := (√(v₀.1 : ℝ))⁻¹ with hr
  have hr2 : r ^ 2 * (v₀.1 : ℝ) = 1 := by
    rw [hr, inv_pow, Real.sq_sqrt hv0.le, inv_mul_cancel₀ hv0.ne']
  have hlaw : HasLaw (fun x : Fin k → ℝ ↦ ∑ i, (r * x i) ^ 2)
      (gammaMeasure ((k : ℝ) / 2) (1 / 2)) P := by
    refine ClassicalLean.Probability.ChiSquared.hasLaw_sum_sq_gaussian hk
      (X := fun i (x : Fin k → ℝ) ↦ r * x i) (fun i ↦ by fun_prop) ?_ (fun i ↦ ?_)
    · exact iIndepFun_pi (X := fun _ t ↦ r * t) fun i ↦ (measurable_const_mul r).aemeasurable
    · refine ⟨(show Measurable (fun x : Fin k → ℝ ↦ r * x i) by fun_prop).aemeasurable, ?_⟩
      have h1 : (fun x : Fin k → ℝ ↦ r * x i) = (fun t ↦ r * t) ∘ Function.eval i := rfl
      rw [h1, ← Measure.map_map (measurable_const_mul r) (measurable_pi_apply i),
        (measurePreserving_eval (fun _ : Fin k ↦ gaussianReal 0 v₀.1) i).map_eq,
        gaussianReal_map_const_mul, mul_zero]
      congr 1
      ext
      simp [hr2]
  have hset : {x : Fin k → ℝ | c < ∑ i, x i ^ 2} =
      (fun x : Fin k → ℝ ↦ ∑ i, (r * x i) ^ 2) ⁻¹' Set.Ioi (c / (v₀.1 : ℝ)) := by
    ext x
    have hS : ∑ i, (r * x i) ^ 2 = (∑ i, x i ^ 2) / v₀.1 := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [mul_pow, show r ^ 2 = (v₀.1 : ℝ)⁻¹ by rw [hr, inv_pow, Real.sq_sqrt hv0.le],
        mul_comm]
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioi, hS]
    exact (div_lt_div_iff_of_pos_right hv0).symm
  have hYm : Measurable (fun x : Fin k → ℝ ↦ ∑ i, (r * x i) ^ 2) := by fun_prop
  have hsize :
      ∫ x : Fin k → ℝ, ClassicalLean.Statistics.thresholdTest (fun x ↦ ∑ i, x i ^ 2) c 0 x *
        ∏ i, gaussianPDFReal 0 v₀.1 (x i) =
      (gammaMeasure ((k : ℝ) / 2) (1 / 2)).real (Set.Ioi (c / (v₀.1 : ℝ))) := by
    rw [hmul, ClassicalLean.Statistics.integral_thresholdTest hSm c 0, zero_mul, add_zero,
      hset, ← hlaw.map_eq, map_measureReal_apply hYm measurableSet_Ioi]
  rw [hsize] at key
  exact key

end ClassicalLean.Statistics.ChiSquaredTest

/-- The hypotheses of `isUniformlyMostPowerful_sum_sq_gaussian` hold together: `k = 2` draws
(the theorem asks only `0 < k`; two draws keep the statistic a real sum), the null variance
`v₀ = 1` and the threshold `c = 3`. The densities move with the variance `v`: at `x = 0` the product
density is `1 / (2πv)`, so `1 / (2π)` at `v = 1` and `1 / (4π)` at `v = 2`. The level is
`P(χ²₂ > 3) = e^(-3/2) ≈ 0.223`, strictly between `0` and `1`, since `gammaMeasure 1 (1/2)` has
density `e^(-x/2) / 2` on `x ≥ 0`. -/
example := ClassicalLean.Statistics.ChiSquaredTest.isUniformlyMostPowerful_sum_sq_gaussian
    (k := 2) (by norm_num) (v₀ := ⟨1, by simp⟩) (c := 3)
