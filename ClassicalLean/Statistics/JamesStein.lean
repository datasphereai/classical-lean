/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.MeanInequalities

/-!
# Stein's lemma and the James–Stein estimator

* `integral_sub_mul_eq_integral_deriv` — **Stein's lemma** (Gaussian integration by parts): for
  `Z` normal with mean `μ` and variance `1` (Mathlib's `gaussianReal μ 1`) and `g` differentiable
  everywhere with derivative `g'`, `E[(Z − μ) g(Z)] = E[g'(Z)]`, when `g`, `g'` and `(x − μ) g`
  are integrable under `N(μ, 1)`. Proved by Mathlib's integration by parts on the line against the
  density `φ`, whose derivative is `−(x − μ) φ` (`hasDerivAt_gaussianPDFReal`). The plan's row
  names `integral_mul_deriv_eq_deriv_mul`; the variant used is
  `integral_mul_deriv_eq_deriv_mul_of_integrable`, on the whole line.
* `normalVec d θ` — **the normal law with mean `θ` and identity covariance in dimension `d`**,
  built from `gaussianReal`: `Measure.pi fun i ↦ gaussianReal (θ i) 1` on `Fin d → ℝ`, `d`
  independent coordinates `N(θ i, 1)`. (Mathlib's `multivariateGaussian` on `EuclideanSpace` is
  another construction; it is not used.) `sqNorm x = ∑ x i ^ 2` is the squared Euclidean length,
  written out because the norm of `Fin d → ℝ` is the largest coordinate.
* `jamesStein x = (1 − (d − 2)/‖x‖²) x`.
* `integral_sqNorm_sub` — `E ‖X − θ‖² = d`, the mean squared error of `X` itself.
* `integrable_inv_sqNorm` — for `d ≥ 3`, `E[1/‖X‖²] < ∞`: by the arithmetic–geometric mean
  inequality on three coordinates, `1/‖x‖² ≤ (1/3) ∏_{k < 3} |x k|^(−2/3)`, and `|t|^(−2/3)` is
  integrable under `N(μ, 1)` because `−2/3 > −1` (`integrable_sq_rpow_gaussianReal`).
* `integral_coord_stein` — Stein's identity in one coordinate for `g(x) = x i / ‖x‖²`, by Fubini
  (`measurePreserving_piFinSuccAbove`, `integral_prod_symm`) and Stein's lemma on almost every
  slice (`integral_slice`).
* `integral_sqNorm_jamesStein_sub_eq` — the exact risk:
  `E ‖JS(X) − θ‖² = d − (d − 2)² E[1/‖X‖²]` for `d ≥ 3`.
* `integral_norm_sq_jamesStein_lt` — order LEAN-24, item 59, **the James–Stein theorem**: for
  `d ≥ 3` and every `θ`, the squared error of `JS(X)` is integrable and its mean is strictly less
  than `d`, the mean squared error of `X`.
* `integral_sqNorm_jamesStein_sub_lt_integral_sqNorm_sub` — the same, stated against
  `E ‖X − θ‖²` directly.
* `jamesStein_eq_self_two`, `integral_sqNorm_jamesStein_sub_two` — **`d ≥ 3` is needed for this
  estimator**: for `d = 2` it is `X` itself (`d − 2 = 0`) and its risk is exactly `2 = d`.

## Hypotheses

Measured in order LEAN-24's checks (`checks.py`, lines J1 to J3). `d ≥ 3` is needed: `d = 2` is
proved above (risk exactly `d`); for `d = 1` the estimator is `x + 1/x`, whose squared error has
infinite mean (worked by hand: `1/x²` is not integrable near `0` against a density bounded below
there). Lean's integral of a non-integrable function is `0`, so for `d = 1` the bare inequality
"risk `< d`" would read `0 < 1` and hold for a wrong reason; this is why integrability is part
of the conclusion. For `d = 2`, `E[1/‖X‖²]` is itself infinite for every `θ` (by hand: the
density of `X` is bounded below near `0`, and `1/‖x‖²` is not integrable near `0` in the plane;
review r59). A seeded simulation (FLOAT, 100,000 draws each)
gives risk `1.997`, `2.009`, `2.000` at `θ = 0` for `d = 3, 5, 10` (the exact value there is `2`,
since `E[1/‖X‖²] = 1/(d − 2)`), and `4.798` for `d = 5`, `9.937` for `d = 10` with every
coordinate of `θ` equal to `3` and `10`. In Stein's lemma, the integrability of `g` and of
`(x − μ) g` is assumed because Mathlib's integration by parts asks for it; the textbook form
needs only `E |g'(Z)| < ∞` for absolutely continuous `g` (review r59, from the reviewer's
knowledge; not proved here). The only use here has `g` bounded.

## What is cited

For works not read here, author, title and year only: C. Stein, "Inadmissibility of the Usual
Estimator for the Mean of a Multivariate Normal Distribution", 1956; W. James and C. Stein,
"Estimation with Quadratic Loss", 1961; C. Stein, "Estimation of the Mean of a Multivariate Normal
Distribution", 1981.

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-24): "james.?stein|stein.?s lemma|gaussian
integration by parts|shrinkage" has one hit, Eisenstein's lemma. Used: `gaussianReal`,
`gaussianPDFReal`, `integral_gaussianReal_eq_integral_smul`,
`integral_mul_deriv_eq_deriv_mul_of_integrable`, `variance_fun_id_gaussianReal`,
`memLp_id_gaussianReal`, `Integrable.fintype_prod`, `integrable_comp_eval`, `integral_comp_eval`,
`measurePreserving_piFinSuccAbove`, `integral_prod_symm`,
`intervalIntegral.intervalIntegrable_rpow'`, `Real.geom_mean_le_arith_mean3_weighted`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ClassicalLean.Statistics

/-- Integrability under the normal law `N(μ, 1)` is integrability of `φ · g` on the line, with
`φ` its density. -/
theorem integrable_gaussianReal_iff {μ : ℝ} {g : ℝ → ℝ} :
    Integrable g (gaussianReal μ 1) ↔ Integrable (fun x ↦ gaussianPDFReal μ 1 x * g x) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF, smul_eq_mul]

/-- The density of `N(μ, 1)` has derivative `−(x − μ) φ(x)`. -/
theorem hasDerivAt_gaussianPDFReal (μ x : ℝ) :
    HasDerivAt (gaussianPDFReal μ 1) (-(x - μ) * gaussianPDFReal μ 1 x) x := by
  have h : HasDerivAt (fun x ↦ -(x - μ) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) (-(x - μ)) x := by
    have h0 : HasDerivAt (fun y : ℝ ↦ y - μ) 1 x := (hasDerivAt_id x).sub_const μ
    convert ((h0.mul h0).neg).div_const (2 * ((1 : ℝ≥0) : ℝ)) using 1
    · funext y; simp only [NNReal.coe_one, Pi.neg_apply, Pi.mul_apply]; ring
    · simp only [NNReal.coe_one]; ring
  have := (h.exp).const_mul (Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹
  convert this using 1
  · ext y; rw [gaussianPDFReal_def]
  · rw [gaussianPDFReal_def]; ring

/-- **Stein's lemma** (Gaussian integration by parts). For `Z` normal with mean `μ` and variance
`1`, and `g` differentiable with derivative `g'`, `E[(Z − μ) g(Z)] = E[g'(Z)]`, provided `g`, `g'`
and `(x − μ) g` are integrable under `N(μ, 1)`. -/
theorem integral_sub_mul_eq_integral_deriv {μ : ℝ} {g g' : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hgi : Integrable g (gaussianReal μ 1))
    (hg' : Integrable g' (gaussianReal μ 1))
    (hgx : Integrable (fun x ↦ (x - μ) * g x) (gaussianReal μ 1)) :
    ∫ x, (x - μ) * g x ∂gaussianReal μ 1 = ∫ x, g' x ∂gaussianReal μ 1 := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  rw [integrable_gaussianReal_iff] at hgi hg' hgx
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := g) (u' := g')
    (v := gaussianPDFReal μ 1) (v' := fun x ↦ -(x - μ) * gaussianPDFReal μ 1 x)
    (fun x _ ↦ hg x) (fun x _ ↦ hasDerivAt_gaussianPDFReal μ x)
    (by convert hgx.neg using 1; ext x; simp only [Pi.mul_apply, Pi.neg_apply]; ring)
    (by convert hg' using 1; ext x; simp only [Pi.mul_apply]; ring)
    (by convert hgi using 1; ext x; simp only [Pi.mul_apply]; ring)
  simp only [smul_eq_mul]
  have e1 : ∫ x, gaussianPDFReal μ 1 x * ((x - μ) * g x) =
      -∫ x, g x * (-(x - μ) * gaussianPDFReal μ 1 x) := by
    rw [← integral_neg]; congr 1; ext x; ring
  have e2 : ∫ x, gaussianPDFReal μ 1 x * g' x = ∫ x, g' x * gaussianPDFReal μ 1 x := by
    congr 1; ext x; ring
  rw [e1, e2, key, neg_neg]

/-- The density of `N(μ, 1)` is at most `1` (its peak is `1/√(2π)`). -/
theorem gaussianPDFReal_le_one (μ x : ℝ) : gaussianPDFReal μ 1 x ≤ 1 := by
  rw [gaussianPDFReal_def]
  have h1 : 1 ≤ Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)) := by
    rw [NNReal.coe_one, mul_one, Real.one_le_sqrt]
    linarith [Real.two_le_pi]
  have h2 : Real.exp (-(x - μ) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    apply div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _))
    simp
  calc _ ≤ (Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 (Real.sqrt_nonneg _))
    _ ≤ 1 := by rw [mul_one]; exact inv_le_one_of_one_le₀ h1

/-- `(t²)^(−1/3) = |t|^(−2/3)` is integrable on `[−1, 1]`, since `−2/3 > −1`. -/
theorem integrableOn_sq_rpow :
    IntegrableOn (fun t : ℝ ↦ (t ^ 2) ^ (-(1 / 3 : ℝ))) (Icc (-1) 1) := by
  have h01 : IntervalIntegrable (fun t : ℝ ↦ (t ^ 2) ^ (-(1 / 3 : ℝ))) volume 0 1 := by
    have h := intervalIntegral.intervalIntegrable_rpow' (r := -(2 / 3 : ℝ)) (by norm_num)
      (a := 0) (b := 1)
    rw [intervalIntegrable_iff] at h ⊢
    refine h.congr_fun (fun t ht ↦ ?_) measurableSet_uIoc
    rw [uIoc_of_le zero_le_one] at ht
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.1.le]
    norm_num
  have heven : (fun t : ℝ ↦ ((-t) ^ 2) ^ (-(1 / 3 : ℝ))) =
      fun t ↦ (t ^ 2) ^ (-(1 / 3 : ℝ)) := by
    ext t; rw [neg_sq]
  have hm10 : IntervalIntegrable (fun t : ℝ ↦ (t ^ 2) ^ (-(1 / 3 : ℝ))) volume (-1) 0 := by
    rw [IntervalIntegrable.iff_comp_neg, heven, neg_neg, neg_zero]
    exact h01.symm
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).1 (hm10.trans h01)

/-- `t ↦ (t²)^(−1/3)` is measurable. -/
theorem measurable_sq_rpow : Measurable fun t : ℝ ↦ (t ^ 2) ^ (-(1 / 3 : ℝ)) :=
  (measurable_id.pow_const 2).pow_const _

/-- Under `N(μ, 1)`, `|Z|^(−2/3)` is integrable: near `0` by `integrableOn_sq_rpow` (the density
is at most `1`), and away from `0` it is at most `1`. -/
theorem integrable_sq_rpow_gaussianReal (μ : ℝ) :
    Integrable (fun t : ℝ ↦ (t ^ 2) ^ (-(1 / 3 : ℝ))) (gaussianReal μ 1) := by
  rw [integrable_gaussianReal_iff]
  have hbd : Integrable (fun t ↦ (Icc (-1 : ℝ) 1).indicator
      (fun t : ℝ ↦ (t ^ 2) ^ (-(1 / 3 : ℝ))) t + gaussianPDFReal μ 1 t) :=
    (integrableOn_sq_rpow.integrable_indicator measurableSet_Icc).add
      (integrable_gaussianPDFReal μ 1)
  refine hbd.mono' ((measurable_gaussianPDFReal μ 1).mul measurable_sq_rpow).aestronglyMeasurable
    (ae_of_all _ fun t ↦ ?_)
  have hp0 := gaussianPDFReal_nonneg μ 1 t
  have hp1 := gaussianPDFReal_le_one μ t
  have hh0 : 0 ≤ (t ^ 2) ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg (sq_nonneg t) _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp0 hh0)]
  by_cases ht : t ∈ Icc (-1 : ℝ) 1
  · rw [indicator_of_mem ht]
    nlinarith
  · rw [indicator_of_notMem ht, zero_add]
    have h1 : 1 ≤ t ^ 2 := by
      simp only [mem_Icc, not_and_or, not_le] at ht
      rcases ht with h | h <;> nlinarith
    have : (t ^ 2) ^ (-(1 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num)
    nlinarith

/-! ### The normal law in dimension `d` -/

/-- **The normal law with mean `θ` and identity covariance in dimension `d`**, built from
Mathlib's `gaussianReal`: the product of the `d` laws `N(θ i, 1)` on `Fin d → ℝ` (independent
coordinates, each of variance `1`). -/
noncomputable def normalVec (d : ℕ) (θ : Fin d → ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi fun i ↦ gaussianReal (θ i) 1

instance isProbabilityMeasure_normalVec (d : ℕ) (θ : Fin d → ℝ) :
    IsProbabilityMeasure (normalVec d θ) := by
  unfold normalVec; infer_instance

/-- The squared length `∑ x i ^ 2` (written out: the norm of `Fin d → ℝ` is the largest
coordinate, not the Euclidean length). -/
def sqNorm {d : ℕ} (x : Fin d → ℝ) : ℝ := ∑ i, x i ^ 2

theorem sqNorm_nonneg {d : ℕ} (x : Fin d → ℝ) : 0 ≤ sqNorm x :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- Under `normalVec`, each coordinate is `0` with chance `0`. -/
theorem ae_ne_zero_normalVec {d : ℕ} (θ : Fin d → ℝ) (i : Fin d) :
    ∀ᵐ x ∂normalVec d θ, x i ≠ 0 := by
  have := nullSingletonClass_gaussianReal (μ := θ i) (v := 1) one_ne_zero
  have h : normalVec d θ {x | x i = 0} = 0 := by
    rw [show {x : Fin d → ℝ | x i = 0} = Function.eval i ⁻¹' {0} from rfl, normalVec,
      (measurePreserving_eval (fun i ↦ gaussianReal (θ i) 1) i).measure_preimage
        (measurableSet_singleton (0 : ℝ)).nullMeasurableSet]
    exact measure_singleton _
  rw [ae_iff]
  simpa using h

/-- **`E[1/‖X‖²]` is finite in dimension `d ≥ 3`.** By the arithmetic–geometric mean inequality on
three coordinates, `1/‖x‖² ≤ (1/3) ∏_{k<3} |x k|^(−2/3)`, a product of functions of separate
coordinates, each integrable under `N(θ k, 1)` (`integrable_sq_rpow_gaussianReal`). -/
theorem integrable_inv_sqNorm {d : ℕ} (hd : 3 ≤ d) (θ : Fin d → ℝ) :
    Integrable (fun x ↦ (sqNorm x)⁻¹) (normalVec d θ) := by
  classical
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  set i2 : Fin d := ⟨2, by omega⟩
  set T : Finset (Fin d) := {i0, i1, i2} with hT
  set h : ℝ → ℝ := fun t ↦ (t ^ 2) ^ (-(1 / 3 : ℝ)) with hh
  have hB : Integrable (fun x : Fin d → ℝ ↦ 3⁻¹ * ∏ i, (if i ∈ T then h (x i) else 1))
      (normalVec d θ) := by
    refine Integrable.const_mul ?_ _
    refine Integrable.fintype_prod (f := fun i t ↦ if i ∈ T then h t else 1) fun i ↦ ?_
    by_cases hi : i ∈ T
    · simp only [hi, ↓reduceIte]; exact integrable_sq_rpow_gaussianReal _
    · simp only [hi, ↓reduceIte]; exact integrable_const _
  have hmeas : Measurable fun x : Fin d → ℝ ↦ (sqNorm x)⁻¹ := by unfold sqNorm; fun_prop
  refine hB.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_ne_zero_normalVec θ i0, ae_ne_zero_normalVec θ i1,
    ae_ne_zero_normalVec θ i2] with x h0 h1 h2
  have hne01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have hne02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have hne12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  have hprod : ∏ i, (if i ∈ T then h (x i) else 1) = h (x i0) * h (x i1) * h (x i2) := by
    rw [Finset.prod_ite_mem, Finset.univ_inter, hT, Finset.prod_insert (by simp [hne01, hne02]),
      Finset.prod_insert (by simp [hne12]), Finset.prod_singleton, mul_assoc]
  rw [hprod, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (sqNorm_nonneg x))]
  set p0 := x i0 ^ 2
  set p1 := x i1 ^ 2
  set p2 := x i2 ^ 2
  have hp0 : 0 < p0 := by positivity
  have hp1 : 0 < p1 := by positivity
  have hp2 : 0 < p2 := by positivity
  have hS : p0 + p1 + p2 ≤ sqNorm x := by
    have := Finset.sum_le_univ_sum_of_nonneg (s := T) (f := fun i ↦ x i ^ 2)
      (fun i ↦ sq_nonneg _)
    rwa [hT, Finset.sum_insert (by simp [hne01, hne02]), Finset.sum_insert (by simp [hne12]),
      Finset.sum_singleton, ← add_assoc] at this
  have hG := Real.geom_mean_le_arith_mean3_weighted (w₁ := 1 / 3) (w₂ := 1 / 3) (w₃ := 1 / 3)
    (by norm_num) (by norm_num) (by norm_num) hp0.le hp1.le hp2.le (by norm_num)
  have hGpos : 0 < p0 ^ (1 / 3 : ℝ) * p1 ^ (1 / 3 : ℝ) * p2 ^ (1 / 3 : ℝ) := by positivity
  calc (sqNorm x)⁻¹ ≤ (3 * (p0 ^ (1 / 3 : ℝ) * p1 ^ (1 / 3 : ℝ) * p2 ^ (1 / 3 : ℝ)))⁻¹ :=
        inv_anti₀ (by positivity) (by linarith)
    _ = 3⁻¹ * (h (x i0) * h (x i1) * h (x i2)) := by
        simp only [hh, Real.rpow_neg (sq_nonneg _), mul_inv]
        ring

/-- Stein's lemma on one slice: for `r > 0`, `E[(Z − μ) Z/(Z² + r)] = E[(r − Z²)/(Z² + r)²]`
under `N(μ, 1)`. -/
theorem integral_slice (μ : ℝ) {r : ℝ} (hr : 0 < r) :
    ∫ t, (t - μ) * (t / (t ^ 2 + r)) ∂gaussianReal μ 1 =
      ∫ t, (r - t ^ 2) / (t ^ 2 + r) ^ 2 ∂gaussianReal μ 1 := by
  have hpos : ∀ t : ℝ, 0 < t ^ 2 + r := fun t ↦ by positivity
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun t ↦ t / (t ^ 2 + r)) ((r - t ^ 2) / (t ^ 2 + r) ^ 2) t := by
    intro t
    have h2 : HasDerivAt (fun t : ℝ ↦ t ^ 2 + r) (2 * t) t := by
      simpa using ((hasDerivAt_id t).pow 2).add_const r
    convert (hasDerivAt_id t).div h2 (hpos t).ne' using 1
    · funext x; simp only [Pi.div_apply, id]
    · simp only [id]; ring
  have hgm : Measurable fun t : ℝ ↦ t / (t ^ 2 + r) := by fun_prop
  have hg'm : Measurable fun t : ℝ ↦ (r - t ^ 2) / (t ^ 2 + r) ^ 2 := by fun_prop
  have hgb : ∀ t : ℝ, ‖t / (t ^ 2 + r)‖ ≤ 1 + 1 / r := by
    intro t
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hpos t), div_le_iff₀ (hpos t)]
    have h1 : |t| ≤ 1 + t ^ 2 := by
      rcases le_total |t| 1 with h | h
      · nlinarith [sq_nonneg t]
      · nlinarith [sq_abs t]
    have h2 : 1 + t ^ 2 ≤ (1 + 1 / r) * (t ^ 2 + r) := by
      rw [add_mul, one_mul, div_mul_eq_mul_div, one_mul, add_div, div_self hr.ne']
      have : 0 ≤ t ^ 2 / r := div_nonneg (sq_nonneg t) hr.le
      linarith
    linarith
  have hg'b : ∀ t : ℝ, ‖(r - t ^ 2) / (t ^ 2 + r) ^ 2‖ ≤ 1 / r := by
    intro t
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos (hpos t) 2), div_le_div_iff₀
      (pow_pos (hpos t) 2) hr, one_mul]
    have : |r - t ^ 2| ≤ t ^ 2 + r := abs_le.2 ⟨by nlinarith [sq_nonneg t], by nlinarith⟩
    nlinarith [sq_nonneg t]
  have hgi : Integrable (fun t ↦ t / (t ^ 2 + r)) (gaussianReal μ 1) :=
    Integrable.of_bound hgm.aestronglyMeasurable _ (ae_of_all _ hgb)
  have hg'i : Integrable (fun t ↦ (r - t ^ 2) / (t ^ 2 + r) ^ 2) (gaussianReal μ 1) :=
    Integrable.of_bound hg'm.aestronglyMeasurable _ (ae_of_all _ hg'b)
  have hid : Integrable (fun t : ℝ ↦ t - μ) (gaussianReal μ 1) :=
    ((memLp_id_gaussianReal 1).integrable le_rfl).sub (integrable_const μ)
  have hgx : Integrable (fun t ↦ (t - μ) * (t / (t ^ 2 + r))) (gaussianReal μ 1) := by
    have := hid.bdd_mul (c := 1 + 1 / r) hgm.aestronglyMeasurable (ae_of_all _ hgb)
    exact this.congr (ae_of_all _ fun t ↦ mul_comm _ _)
  exact integral_sub_mul_eq_integral_deriv hderiv hgi hg'i hgx

/-- The squared length after inserting the coordinate `t` at place `i`. -/
theorem sqNorm_insertNth {n : ℕ} (i : Fin (n + 1)) (t : ℝ) (y : Fin n → ℝ) :
    sqNorm (Fin.insertNth i t y) = t ^ 2 + sqNorm y := by
  simp only [sqNorm]
  rw [Fin.sum_univ_succAbove _ i, Fin.insertNth_apply_same]
  simp only [Fin.insertNth_apply_succAbove]

/-- **Stein's identity in one coordinate**, for `g(x) = x i / ‖x‖²`: under `normalVec (n + 1) θ`
with `n ≥ 1`, `E[(X i − θ i) X i / ‖X‖²] = E[(‖X‖² − 2 X i²) / ‖X‖⁴]`, given that both sides are
integrable. Fubini splits off coordinate `i`; for almost every value `y` of the other coordinates
`‖y‖² > 0`, and `integral_slice` applies. -/
theorem integral_coord_stein {n : ℕ} (hn : 1 ≤ n) (θ : Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (h1 : Integrable (fun x ↦ (x i - θ i) * (x i / sqNorm x)) (normalVec (n + 1) θ))
    (h2 : Integrable (fun x ↦ (sqNorm x - 2 * x i ^ 2) / sqNorm x ^ 2) (normalVec (n + 1) θ)) :
    ∫ x, (x i - θ i) * (x i / sqNorm x) ∂normalVec (n + 1) θ =
      ∫ x, (sqNorm x - 2 * x i ^ 2) / sqNorm x ^ 2 ∂normalVec (n + 1) θ := by
  set μs : Fin (n + 1) → Measure ℝ := fun j ↦ gaussianReal (θ j) 1 with hμs
  have hmp := (measurePreserving_piFinSuccAbove μs i).symm
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i with he
  have happ : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.insertNth i p.1 p.2 := fun p ↦ rfl
  have hrest : ∀ᵐ y ∂(Measure.pi fun j ↦ μs (i.succAbove j)), 0 < sqNorm y := by
    filter_upwards [ae_ne_zero_normalVec (fun j ↦ θ (i.succAbove j)) ⟨0, by omega⟩] with y hy
    have : 0 < y ⟨0, by omega⟩ ^ 2 := by positivity
    exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun j ↦ y j ^ 2)
      (fun j _ ↦ sq_nonneg _) (Finset.mem_univ _))
  rw [normalVec, ← hmp.integral_comp', ← hmp.integral_comp']
  rw [normalVec, ← hmp.integrable_comp_emb e.symm.measurableEmbedding] at h1 h2
  have i1 := integral_prod_symm _ h1
  have i2 := integral_prod_symm _ h2
  simp only [Function.comp_apply] at i1 i2
  rw [i1, i2]
  refine integral_congr_ae ?_
  filter_upwards [hrest] with y hy
  have := integral_slice (θ i) hy
  simp only [happ, Fin.insertNth_apply_same, sqNorm_insertNth]
  rw [this]
  congr 1; ext t; ring

/-- `E[(Z − μ)²] = 1` under `N(μ, 1)`. -/
theorem integral_sub_sq_gaussianReal (μ : ℝ) : ∫ t, (t - μ) ^ 2 ∂gaussianReal μ 1 = 1 := by
  have h := variance_fun_id_gaussianReal (μ := μ) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at h
  exact_mod_cast h

/-- `(Z − μ)²` is integrable under `N(μ, 1)`. -/
theorem integrable_sub_sq_gaussianReal (μ : ℝ) :
    Integrable (fun t : ℝ ↦ (t - μ) ^ 2) (gaussianReal μ 1) := by
  have h : MemLp (fun t : ℝ ↦ t - μ) 2 (gaussianReal μ 1) :=
    (memLp_id_gaussianReal 2).sub (memLp_const μ)
  exact h.integrable_sq

/-- The mean squared error of `X` itself: `E ‖X − θ‖² = d`. -/
theorem integral_sqNorm_sub (d : ℕ) (θ : Fin d → ℝ) :
    ∫ x, sqNorm (x - θ) ∂normalVec d θ = d := by
  simp only [sqNorm, Pi.sub_apply, normalVec]
  rw [integral_finsetSum Finset.univ (f := fun i (x : Fin d → ℝ) ↦ (x i - θ i) ^ 2)
    fun i _ ↦ integrable_comp_eval (X := fun _ ↦ ℝ) (μ := fun i ↦ gaussianReal (θ i) 1) (i := i)
      (f := fun t : ℝ ↦ (t - θ i) ^ 2) (integrable_sub_sq_gaussianReal (θ i))]
  rw [Finset.sum_congr rfl fun i _ ↦ (integral_comp_eval (X := fun _ ↦ ℝ)
    (μ := fun i ↦ gaussianReal (θ i) 1) (i := i) (f := fun t : ℝ ↦ (t - θ i) ^ 2)
    (by fun_prop)).trans (integral_sub_sq_gaussianReal (θ i))]
  simp

/-- **The James–Stein estimator** `(1 − (d − 2)/‖x‖²) x` (at `x = 0` Lean's `x / 0 = 0` makes it
`0`, a point of chance `0`). -/
noncomputable def jamesStein {d : ℕ} (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i ↦ (1 - ((d : ℝ) - 2) / sqNorm x) * x i

/-- One squared coordinate is at most the squared length. -/
theorem sq_le_sqNorm {d : ℕ} (x : Fin d → ℝ) (i : Fin d) : x i ^ 2 ≤ sqNorm x :=
  Finset.single_le_sum (f := fun j ↦ x j ^ 2) (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ i)

/-- The squared length is measurable. -/
theorem measurable_sqNorm (d : ℕ) : Measurable fun x : Fin d → ℝ ↦ sqNorm x := by
  unfold sqNorm; fun_prop

/-- The pointwise bound behind the integrability of `(x i − θ i) x i / ‖x‖²`. -/
private theorem abs_mul_div_le {a b S : ℝ} (hb : b ^ 2 ≤ S) :
    |a * (b / S)| ≤ a ^ 2 + S⁻¹ := by
  rcases (le_trans (sq_nonneg b) hb).lt_or_eq with hS | hS
  · have h1 : (|a| * |b|) ^ 2 ≤ a ^ 2 * S := by
      rw [mul_pow, sq_abs, sq_abs]; exact mul_le_mul_of_nonneg_left hb (sq_nonneg a)
    have key : |a| * |b| ≤ a ^ 2 * S + 1 := by
      nlinarith [sq_nonneg (|a| * |b| - 1), abs_nonneg a, abs_nonneg b]
    calc |a * (b / S)| = |a| * |b| / S := by rw [abs_mul, abs_div, abs_of_pos hS, mul_div_assoc]
      _ ≤ (a ^ 2 * S + 1) / S := div_le_div_of_nonneg_right key hS.le
      _ = a ^ 2 + S⁻¹ := by field_simp
  · rw [← hS, div_zero, mul_zero, abs_zero, inv_zero, add_zero]; exact sq_nonneg a

private theorem abs_sub_div_sq_le {b S : ℝ} (hb : b ^ 2 ≤ S) :
    |(S - 2 * b ^ 2) / S ^ 2| ≤ S⁻¹ := by
  rcases (le_trans (sq_nonneg b) hb).lt_or_eq with hS | hS
  · have h : |S - 2 * b ^ 2| ≤ S :=
      abs_le.2 ⟨by nlinarith [sq_nonneg b], by nlinarith [sq_nonneg b]⟩
    calc |(S - 2 * b ^ 2) / S ^ 2| = |S - 2 * b ^ 2| / S ^ 2 := by
          rw [abs_div, abs_of_pos (pow_pos hS 2)]
      _ ≤ S / S ^ 2 := div_le_div_of_nonneg_right h (pow_pos hS 2).le
      _ = S⁻¹ := by field_simp
  · rw [← hS]; simp

private theorem jamesStein_risk_aux {d : ℕ} (hd : 3 ≤ d) (θ : Fin d → ℝ) :
    Integrable (fun x ↦ sqNorm (jamesStein x - θ)) (normalVec d θ) ∧
    ∫ x, sqNorm (jamesStein x - θ) ∂normalVec d θ =
      d - ((d : ℝ) - 2) ^ 2 * ∫ x, (sqNorm x)⁻¹ ∂normalVec d θ := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  set c : ℝ := ((n + 1 : ℕ) : ℝ) - 2 with hc
  have hinv := integrable_inv_sqNorm hd θ
  have hA : ∀ i, Integrable (fun x : Fin (n + 1) → ℝ ↦ (x i - θ i) ^ 2) (normalVec (n + 1) θ) :=
    fun i ↦ integrable_comp_eval (X := fun _ ↦ ℝ) (μ := fun i ↦ gaussianReal (θ i) 1) (i := i)
      (f := fun t : ℝ ↦ (t - θ i) ^ 2) (integrable_sub_sq_gaussianReal (θ i))
  have hB : ∀ i, Integrable (fun x ↦ (x i - θ i) * (x i / sqNorm x)) (normalVec (n + 1) θ) := by
    intro i
    refine ((hA i).add hinv).mono' ?_ (ae_of_all _ fun x ↦ ?_)
    · exact (((measurable_pi_apply i).sub measurable_const).mul
        ((measurable_pi_apply i).div (measurable_sqNorm _))).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact abs_mul_div_le (sq_le_sqNorm x i)
  have hC : ∀ i, Integrable (fun x ↦ (sqNorm x - 2 * x i ^ 2) / sqNorm x ^ 2)
      (normalVec (n + 1) θ) := by
    intro i
    refine hinv.mono' ?_ (ae_of_all _ fun x ↦ ?_)
    · exact (((measurable_sqNorm _).sub (measurable_const.mul
        ((measurable_pi_apply i).pow_const 2))).div
          ((measurable_sqNorm _).pow_const 2)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact abs_sub_div_sq_le (sq_le_sqNorm x i)
  -- the pointwise expansion
  have hexp : ∀ x : Fin (n + 1) → ℝ, sqNorm (jamesStein x - θ) =
      sqNorm (x - θ) - 2 * c * ∑ i, (x i - θ i) * (x i / sqNorm x) + c ^ 2 * (sqNorm x)⁻¹ := by
    intro x
    have hsq : ∑ i, (x i / sqNorm x) ^ 2 = (sqNorm x)⁻¹ := by
      simp only [div_pow, ← Finset.sum_div]
      change sqNorm x / sqNorm x ^ 2 = (sqNorm x)⁻¹
      rcases eq_or_ne (sqNorm x) 0 with h0 | h0
      · simp [h0]
      · field_simp
    simp only [sqNorm, jamesStein, Pi.sub_apply] at hsq ⊢
    have e : ∀ i, ((1 - c / ∑ j, x j ^ 2) * x i - θ i) ^ 2 = (x i - θ i) ^ 2 -
        2 * c * ((x i - θ i) * (x i / ∑ j, x j ^ 2)) + c ^ 2 * (x i / ∑ j, x j ^ 2) ^ 2 := by
      intro i; ring
    rw [Finset.sum_congr rfl fun i _ ↦ e i, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hsq]
  have hsumC : ∀ x : Fin (n + 1) → ℝ,
      ∑ i, (sqNorm x - 2 * x i ^ 2) / sqNorm x ^ 2 = c * (sqNorm x)⁻¹ := by
    intro x
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Finset.mul_sum, nsmul_eq_mul]
    change (((n + 1 : ℕ) : ℝ) * sqNorm x - 2 * sqNorm x) / sqNorm x ^ 2 = c * (sqNorm x)⁻¹
    rcases eq_or_ne (sqNorm x) 0 with h0 | h0
    · simp [h0]
    · rw [hc]; field_simp
  have hsum_int : Integrable (fun x ↦ ∑ i, (x i - θ i) * (x i / sqNorm x))
      (normalVec (n + 1) θ) := integrable_finsetSum _ fun i _ ↦ hB i
  have hsq_int : Integrable (fun x ↦ sqNorm (x - θ)) (normalVec (n + 1) θ) := by
    simp only [sqNorm, Pi.sub_apply]; exact integrable_finsetSum _ fun i _ ↦ hA i
  have hsig : ∫ x, ∑ i, (x i - θ i) * (x i / sqNorm x) ∂normalVec (n + 1) θ =
      c * ∫ x, (sqNorm x)⁻¹ ∂normalVec (n + 1) θ := by
    rw [integral_finsetSum _ fun i _ ↦ hB i,
      Finset.sum_congr rfl fun i _ ↦ integral_coord_stein (by omega) θ i (hB i) (hC i),
      ← integral_finsetSum _ fun i _ ↦ hC i]
    simp_rw [hsumC]
    exact integral_const_mul c _
  have hfun : (fun x ↦ sqNorm (jamesStein x - θ)) = fun x ↦ sqNorm (x - θ) -
      2 * c * ∑ i, (x i - θ i) * (x i / sqNorm x) + c ^ 2 * (sqNorm x)⁻¹ := funext hexp
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact (hsq_int.sub (hsum_int.const_mul _)).add (hinv.const_mul _)
  · have h1 : Integrable (fun x ↦ sqNorm (x - θ) -
        2 * c * ∑ i, (x i - θ i) * (x i / sqNorm x)) (normalVec (n + 1) θ) :=
      hsq_int.sub (hsum_int.const_mul _)
    have h2 : Integrable (fun x ↦ c ^ 2 * (sqNorm x)⁻¹) (normalVec (n + 1) θ) :=
      hinv.const_mul _
    rw [hfun, integral_add h1 h2, integral_sub (f := fun x ↦ sqNorm (x - θ))
      (g := fun x ↦ 2 * c * ∑ i, (x i - θ i) * (x i / sqNorm x)) hsq_int
      (hsum_int.const_mul _), integral_const_mul, integral_const_mul, hsig, integral_sqNorm_sub]
    ring

/-- **The risk of the James–Stein estimator**, exactly: for `d ≥ 3`,
`E ‖JS(X) − θ‖² = d − (d − 2)² E[1/‖X‖²]`. -/
theorem integral_sqNorm_jamesStein_sub_eq {d : ℕ} (hd : 3 ≤ d) (θ : Fin d → ℝ) :
    ∫ x, sqNorm (jamesStein x - θ) ∂normalVec d θ =
      d - ((d : ℝ) - 2) ^ 2 * ∫ x, (sqNorm x)⁻¹ ∂normalVec d θ :=
  (jamesStein_risk_aux hd θ).2

/-- `E[1/‖X‖²] > 0`. -/
theorem integral_inv_sqNorm_pos {d : ℕ} (hd : 3 ≤ d) (θ : Fin d → ℝ) :
    0 < ∫ x, (sqNorm x)⁻¹ ∂normalVec d θ := by
  have hnn : 0 ≤ ∫ x, (sqNorm x)⁻¹ ∂normalVec d θ :=
    integral_nonneg fun x ↦ inv_nonneg.2 (sqNorm_nonneg x)
  refine lt_of_le_of_ne hnn fun h ↦ ?_
  have h0 := (integral_eq_zero_iff_of_nonneg (fun x ↦ inv_nonneg.2 (sqNorm_nonneg x))
    (integrable_inv_sqNorm hd θ)).1 h.symm
  obtain ⟨x, hx0, hx1⟩ := (h0.and (ae_ne_zero_normalVec θ ⟨0, by omega⟩)).exists
  have : 0 < sqNorm x := lt_of_lt_of_le (by positivity) (sq_le_sqNorm x ⟨0, by omega⟩)
  exact (inv_pos.2 this).ne' hx0

/-- **The James–Stein theorem.** For `X` normal with mean `θ` and identity covariance in dimension
`d ≥ 3` (`normalVec`), the estimator `(1 − (d − 2)/‖X‖²) X` has integrable squared error, and its
mean squared error is strictly below `d`, the mean squared error of `X` itself
(`integral_sqNorm_sub`), for every `θ`. Integrability is part of the conclusion because Lean's
integral of a non-integrable function is `0`, which would make the inequality hold for a wrong
reason. -/
theorem integral_norm_sq_jamesStein_lt {d : ℕ} (hd : 3 ≤ d) (θ : Fin d → ℝ) :
    Integrable (fun x ↦ sqNorm (jamesStein x - θ)) (normalVec d θ) ∧
      ∫ x, sqNorm (jamesStein x - θ) ∂normalVec d θ < d := by
  refine ⟨(jamesStein_risk_aux hd θ).1, ?_⟩
  rw [integral_sqNorm_jamesStein_sub_eq hd θ]
  have hc : 0 < ((d : ℝ) - 2) ^ 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have := integral_inv_sqNorm_pos hd θ
  nlinarith

/-- **James–Stein, as a comparison of two risks**: for `d ≥ 3` the mean squared error of
`JS(X)` is strictly below that of `X`, for every `θ`. -/
theorem integral_sqNorm_jamesStein_sub_lt_integral_sqNorm_sub {d : ℕ} (hd : 3 ≤ d)
    (θ : Fin d → ℝ) :
    ∫ x, sqNorm (jamesStein x - θ) ∂normalVec d θ < ∫ x, sqNorm (x - θ) ∂normalVec d θ := by
  rw [integral_sqNorm_sub]; exact (integral_norm_sq_jamesStein_lt hd θ).2

/-- **`d ≥ 3` is needed for this estimator: `d = 2`.** In dimension `2` the James–Stein estimator
is `X` itself (`d − 2 = 0`), so its mean squared error is exactly `2 = d`, not less. (Whether
some other estimator beats `X` in dimension `1` or `2` is not addressed here.) -/
theorem jamesStein_eq_self_two (x : Fin 2 → ℝ) : jamesStein x = x := by
  ext i; simp [jamesStein]

/-- The risk in dimension `2` is exactly `2`. -/
theorem integral_sqNorm_jamesStein_sub_two (θ : Fin 2 → ℝ) :
    ∫ x, sqNorm (jamesStein x - θ) ∂normalVec 2 θ = 2 := by
  simp_rw [jamesStein_eq_self_two]
  rw [integral_sqNorm_sub]; norm_num

end ClassicalLean.Statistics

/-- The hypotheses of `integral_norm_sq_jamesStein_lt` hold together: dimension `d = 3`, the least
for which `3 ≤ d`; the mean `θ = (1, 1, 1)`. -/
example := ClassicalLean.Statistics.integral_norm_sq_jamesStein_lt (d := 3) (by norm_num)
  (θ := fun _ ↦ 1)
