/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.ComplexMGF

/-!
# The chi-squared law

* `hasLaw_sum_sq_gaussian` — order CLOUD-MATH-2, item 151 of MATH-PLAN-library-2: for `k ≥ 1`
  independent real random variables `X i` on a probability space, each with the standard normal
  law `gaussianReal 0 1`, the sum of squares `∑ i, X i ^ 2` has the gamma law
  `gammaMeasure (k / 2) (1 / 2)`, shape `k / 2` and rate `1 / 2`: the chi-squared law with `k`
  degrees of freedom.

The proof is by characteristic functions (`Measure.ext_of_charFun`). The gamma law's complex
moment generating function is `r ^ a * (1 / (r - z)) ^ a` on the half-plane `re z < r`
(`complexMGF_gammaMeasure_aux`): both sides are analytic there and agree at the real points
`s < r`, where the integral is Mathlib's real gamma integral (`mgf_gammaMeasure_aux`). At
`z = t * I` this is the gamma law's characteristic function (`charFun_gammaMeasure_aux`). The
square of a standard normal has the characteristic function of `gammaMeasure (1 / 2) (1 / 2)`, by
the complex Gaussian integral (`charFun_sq_gaussian_aux`). Independence makes the characteristic
function of the sum the product of the `k` factors (`integral_exp_add_of_indep_aux`, by induction
over the summands), and `(r ^ (1 / 2) * (1 / (r - t * I)) ^ (1 / 2)) ^ k` is
`r ^ (k / 2) * (1 / (r - t * I)) ^ (k / 2)` at `r = 1 / 2`.

The proof is the draft `d151-r9-s1` (written by a Claude Code session on DSMain, order CC-151,
from an API draft), adapted by the Claude Code cloud session that landed it (order CLOUD-MATH-2):
the namespace, targeted imports and docstrings, and the draft's private lemma that the gamma law
is a probability measure replaced by Mathlib's
`ProbabilityTheory.isProbabilityMeasure_gammaMeasure`.
The witness at the end of the file, for `k = 3` coordinates of the product of standard normal laws
(`Measure.pi`, which is why the file imports `Mathlib.MeasureTheory.Constructions.Pi`), starts from
claude-ai's satisfiability check of 2026-10-13 (`d151-r9-s1-sat.lean`).
-/

open MeasureTheory ProbabilityTheory
open scoped Real Topology

namespace ClassicalLean.Probability.ChiSquared

/-- For a positive real `p`, complex powers split over the product `p * z`. -/
private lemma cpow_ofReal_mul_aux {p : ℝ} (hp : 0 < p) {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    ((p : ℂ) * z) ^ w = (p : ℂ) ^ w * z ^ w := by
  sorry

/-- Characteristic function of an image measure as an expectation. -/
private lemma charFun_map_eq_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {f : Ω → ℝ}
    (hf : Measurable f) (t : ℝ) :
    charFun (P.map f) t = ∫ ω, Complex.exp ((t : ℂ) * (f ω : ℂ) * Complex.I) ∂P := by
  sorry

/-- Independence factorises the expectation of `exp(it(A+B))`. -/
private lemma integral_exp_add_of_indep_aux {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A B : Ω → ℝ} (hA : Measurable A) (hB : Measurable B)
    (h : IndepFun A B P) (t : ℝ) :
    ∫ ω, Complex.exp ((t : ℂ) * ((A ω + B ω : ℝ) : ℂ) * Complex.I) ∂P
      = (∫ ω, Complex.exp ((t : ℂ) * (A ω : ℂ) * Complex.I) ∂P)
        * ∫ ω, Complex.exp ((t : ℂ) * (B ω : ℂ) * Complex.I) ∂P := by
  sorry

/-- The mgf of the gamma law at a real point `s` below the rate. The integral has the real
rate `r - s`, so Mathlib's real gamma integral applies. -/
private lemma mgf_gammaMeasure_aux {a r : ℝ} (ha : 0 < a) (hr : 0 < r) {s : ℝ} (hs : s < r) :
    mgf id (gammaMeasure a r) s = r ^ a * (1 / (r - s)) ^ a := by
  sorry

/-- Every real point below the rate lies in the gamma law's `integrableExpSet`. -/
private lemma Iio_subset_integrableExpSet_gamma_aux {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Set.Iio r ⊆ integrableExpSet id (gammaMeasure a r) := by
  sorry

/-- The complex mgf of the gamma law at a real point below the rate. -/
private lemma complexMGF_gammaMeasure_ofReal_aux {a r : ℝ} (ha : 0 < a) (hr : 0 < r) {s : ℝ}
    (hs : s < r) :
    complexMGF id (gammaMeasure a r) s = (r : ℂ) ^ (a : ℂ) * (1 / ((r : ℂ) - s)) ^ (a : ℂ) := by
  sorry

-- The route of this proof is the one of Mathlib's `ProbabilityTheory.eqOn_complexMGF_of_mgf'`
-- (`Mathlib/Probability/Moments/ComplexMGF.lean`): the identity theorem
-- `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` on a preconnected set, from agreement at
-- the real points near a real base point, moved from `ℝ` to `ℂ` by
-- `Filter.frequently_iff_seq_forall`, `tendsto_nhdsWithin_iff` and `Filter.tendsto_ofReal_iff`.
-- That lemma compares the complex mgfs of two measures with the same mgf; here one side is an
-- explicit function, so it does not apply as stated.
/-- The complex mgf of the gamma law on the half-plane `re z < r`. Both sides are analytic
there and agree at the real points, so they agree on the whole half-plane. -/
private lemma complexMGF_gammaMeasure_aux {a r : ℝ} (ha : 0 < a) (hr : 0 < r) {z : ℂ}
    (hz : z.re < r) :
    complexMGF id (gammaMeasure a r) z = (r : ℂ) ^ (a : ℂ) * (1 / ((r : ℂ) - z)) ^ (a : ℂ) := by
  sorry

/-- Characteristic function of the gamma law. -/
private lemma charFun_gammaMeasure_aux {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (t : ℝ) :
    charFun (gammaMeasure a r) t
      = (r : ℂ) ^ (a : ℂ) * (1 / ((r : ℂ) - (t : ℂ) * Complex.I)) ^ (a : ℂ) := by
  sorry

/-- Algebraic identity relating the Gaussian integral to the gamma formula. -/
private lemma sq_gauss_alg_aux (b : ℂ) (hb : b ≠ 0) :
    (((Real.sqrt (2 * π))⁻¹ : ℝ) : ℂ) * ((π : ℂ) / b) ^ (1 / 2 : ℂ)
      = ((1 / 2 : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ) * (1 / b) ^ ((1 / 2 : ℝ) : ℂ) := by
  sorry

/-- The square of a standard normal has the gamma law with shape and rate `1/2`
(at the level of characteristic functions). -/
private lemma charFun_sq_gaussian_aux (t : ℝ) :
    charFun ((gaussianReal 0 1).map (fun x : ℝ => x ^ 2)) t
      = charFun (gammaMeasure (1 / 2) (1 / 2)) t := by
  sorry

/-- Expectation of `exp(itY²)` for a standard normal `Y`. -/
private lemma integral_sq_eq_aux {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → ℝ} (hY : Measurable Y) (hlaw : HasLaw Y (gaussianReal 0 1) P) (t : ℝ) :
    ∫ ω, Complex.exp ((t : ℂ) * ((Y ω ^ 2 : ℝ) : ℂ) * Complex.I) ∂P
      = charFun (gammaMeasure (1 / 2) (1 / 2)) t := by
  sorry

/-- **The chi-squared law** (item 151 of MATH-PLAN-library-2): the sum of squares of `k ≥ 1`
independent standard normal random variables has the gamma law with shape `k/2` and rate
`1/2`. -/
theorem hasLaw_sum_sq_gaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {k : ℕ} (hk : 0 < k) {X : Fin k → Ω → ℝ}
    (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) :
    HasLaw (fun ω => ∑ i, X i ω ^ 2) (gammaMeasure ((k : ℝ) / 2) (1 / 2)) P := by
  sorry

end ClassicalLean.Probability.ChiSquared

set_option pp.fullNames true
#check @ClassicalLean.Probability.ChiSquared.hasLaw_sum_sq_gaussian
