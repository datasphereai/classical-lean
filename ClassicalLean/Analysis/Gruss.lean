/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Grüss's inequality

Grüss's inequality (G. Grüss, 1935): if `X` takes values in `[m, M]` and `Y` in `[n, N]`, their
covariance is at most `(M − m)(N − n)/4` in size; for functions on `[a, b]`, the average of `f g`
is within `(M − m)(N − n)/4` of the product of the averages of `f` and `g`. Order LEAN-29, item 92
of MATH-PLAN-library-2.

* `abs_covariance_le_mul_div_four` — for random variables on a probability space:
  `|cov[X, Y]| ≤ (M − m)(N − n)/4`, with `X` and `Y` almost everywhere measurable and almost
  everywhere in `[m, M]` and `[n, N]`.
* `abs_average_mul_sub_le` — for interval-integrable `f` and `g` on `[a, b]`, `a < b`, with values
  in `[m, M]` and `[n, N]` there:
  `|avg (f g) − avg f · avg g| ≤ (M − m)(N − n)/4`, each average `(b − a)⁻¹ ∫ₐᵇ`.

**The route.** For every real `t`, the variance of `t X + Y` is not negative:
`t² Var X + 2 t cov[X, Y] + Var Y ≥ 0`. A quadratic in `t` that is never negative has
discriminant at most `0` (Mathlib's `discrim_le_zero`), so `cov[X, Y]² ≤ Var X · Var Y`: the
Cauchy–Schwarz inequality for the covariance, by the standard discriminant argument, written out
here (Mathlib v4.34.0 has no such bound for `covariance`, below). Popoviciu's inequality, Mathlib's
`variance_le_sq_of_bounded`, bounds `Var X ≤ ((M − m)/2)²` and `Var Y ≤ ((N − n)/2)²`. The order
derived route (b), `2 |u v| ≤ t u² + v² / t` with a chosen `t`; this discriminant form of it is the
variant the order's approved plan names (no square roots, and no case split on `M = m` or
`N = n`). The second theorem is the first for the uniform probability on `[a, b]`,
`volume[|Icc a b] = (volume (Icc a b))⁻¹ • volume.restrict (Icc a b)`, where the covariance is
`E[f g] − E f · E g` (`covariance_eq_sub`) and each mean is an average (`integral_smul_measure`).
Every interval integral in the statement is bracketed: `∫ x in a..b, f x * g x - …` without
brackets would read as one integral of the whole difference.

## Hypotheses, and Lean's junk values

Each hypothesis is needed, except that the two measurability hypotheses of the first theorem are
needed only together (below) (order LEAN-29's exact checks, lane `lean/LEAN-29-checks.py`, by the
label of each line; or by hand, as said). For `abs_covariance_le_mul_div_four`:

* a probability measure (`92.drop.prob`): one point, `X = Y = 1`. With mass `0` the bound
  hypotheses hold for any bounds, so `m = 1`, `M = 0`, `n = 0`, `N = 1` are allowed: covariance `0`
  against `−1/4`. With masses `1/2` and `2` and all four bounds `1`: Lean's covariance is
  `c (1 − c)²`, `1/8` and `2`, against `0`.
* the bounds on `X` (`92.drop.bnd`): `X = Y` fair on `{−1, 1}`, `X`'s bounds claimed `m = M = 0`,
  `Y`'s `n = −1`, `N = 1`: covariance `1` against `0`; the bounds on `Y` likewise, the roles
  swapped.
* measurability, the two together (`92.drop.meas`, by hand): `Bool` with only `∅` and the whole
  space measurable, the point mass at `true`, `X` equal to `1` at `true` and `2` at `false`,
  `Y = 2 / X`, both within `[1, 2]`. Neither is almost everywhere measurable, so Lean's integrals of
  `X` and `Y` are `0` (the integral of a function that is not almost everywhere measurable), while
  `X Y = 2` is measurable: Lean's covariance is `2`, against `1/4`. With only one of the two dropped
  there is no such case (cold review 1 of the order, by hand): if `X (Y − E Y)` is not integrable,
  Lean's covariance is `0`, within the bound; otherwise let `X'` be `X` where `Y ≠ E Y` and `m`
  elsewhere; `X'` is almost everywhere measurable, lies in `[m, M]`, and
  `cov[X', Y] = ∫ X (Y − E Y) = cov[X, Y]`, so the theorem for `X'` gives the bound. So the two
  hypotheses are needed together.

For `abs_average_mul_sub_le`:

* `a < b` (`92.drop.hab`): `a = 1`, `b = 0`: the interval `[1, 0]` is empty, so the bound
  hypotheses hold for any bounds; `f = g = 0`, `m = 1`, `M = 0`, `n = 0`, `N = 1`: left side `0`
  against `−1/4`. At `a = b` the statement still holds: every interval integral over `[a, a]` is
  `0`, so the left side is `0` whatever `0⁻¹` is, and the bound is at least `0` (the hypotheses at
  `x = a` give `m ≤ M` and `n ≤ N`).
* the bounds on `f` (`92.drop.fbnd`): `f = g = x` on `[0, 1]`, `f`'s bounds claimed `m = M = 0`,
  `g`'s `n = 0`, `N = 1`: left side `1/3 − 1/4 = 1/12` against `0`; the bounds on `g` likewise.
* integrability of `f`, alone (`92.drop.fmeas`, by hand): on `[0, 1]`, `f = 1 + 1_V` with `V` a
  subset of `(1/2, 1]` that is not Lebesgue measurable, and `g = 1_[0, 1/2]`. Lean's integral of
  `f` is `0`, of `f g = g` it is `1/2`, and of `g` it is `1/2`: left side `1/2` against
  `(2 − 1)(1 − 0)/4 = 1/4`. The integrability of `g` likewise, the roles swapped.

Also measured exactly (the same checks): the first bound on 200 finite laws (`92.prob`), equality
for a fair two-point law on `{m, M}` with `X = Y` (`92.equal`), and the second on 200 step
functions and on `f = g = x` over `[0, 1]` (`92.fun`). The hypotheses of each theorem hold
together: the two `example`s at the end of this file.

## Mathlib at v4.34.0

For order LEAN-29 (row C2 of MATH-PLAN-library-2, run by the plan's check script
`MATH-PLAN-library-2-checks.py`, lines `row.C2`, at 2026-10-15 02:19 UTC, before this module was
written): `gr[üu]ss` and `abs_covariance_le|covariance_le_sqrt|covariance.*sqrt.*variance` each
gave 0 lines in pinned Mathlib, 0 in Mathlib master at `2da3ab0a`, and 0 in the library; the
library's matches now are this module's own text. The main Mathlib results used:
`variance_le_sq_of_bounded`, `variance_add`, `variance_smul`, `covariance_smul_left`,
`discrim_le_zero`, `covariance_eq_sub`, `memLp_of_bounded`, `cond_isProbabilityMeasure_of_finite`,
`ae_cond_of_forall_mem`, `integral_smul_measure`, `integral_Icc_eq_integral_Ioc`.
-/

open MeasureTheory ProbabilityTheory

namespace ClassicalLean.Analysis

/-- **Grüss's inequality for random variables** (order LEAN-29, item 92 of MATH-PLAN-library-2).
On a probability space, if `X` lies in `[m, M]` and `Y` in `[n, N]` almost everywhere, and both
are almost everywhere measurable, then `|cov[X, Y]| ≤ (M − m)(N − n)/4`. The variance of `t X + Y`
is not negative for any `t`, so `cov[X, Y]² ≤ Var X · Var Y`, and Popoviciu's inequality bounds
both variances. -/
theorem abs_covariance_le_mul_div_four {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y : Ω → ℝ} {m M n N : ℝ}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hXb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc m M) (hYb : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc n N) :
    |cov[X, Y; μ]| ≤ (M - m) * (N - n) / 4 := by
  have hX2 : MemLp X 2 μ := memLp_of_bounded hXb hX.aestronglyMeasurable 2
  have hY2 : MemLp Y 2 μ := memLp_of_bounded hYb hY.aestronglyMeasurable 2
  -- the variance of `t X + Y` is never negative: a quadratic in `t` with no two real roots
  have hquad : ∀ t : ℝ, 0 ≤ Var[X; μ] * (t * t) + 2 * cov[X, Y; μ] * t + Var[Y; μ] := by
    intro t
    calc 0 ≤ Var[t • X + Y; μ] := variance_nonneg _ _
      _ = Var[X; μ] * (t * t) + 2 * cov[X, Y; μ] * t + Var[Y; μ] := by
          rw [variance_add (hX2.const_smul t) hY2, variance_smul, covariance_smul_left]
          ring
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  -- Popoviciu's inequality on both
  have hVX := variance_le_sq_of_bounded hXb hX
  have hVY := variance_le_sq_of_bounded hYb hY
  -- the bounds hold somewhere, so `m ≤ M` and `n ≤ N`
  obtain ⟨ω, hω⟩ := hXb.exists
  obtain ⟨ω', hω'⟩ := hYb.exists
  have hmM : 0 ≤ M - m := sub_nonneg.mpr (hω.1.trans hω.2)
  have hnN : 0 ≤ N - n := sub_nonneg.mpr (hω'.1.trans hω'.2)
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  calc cov[X, Y; μ] ^ 2 ≤ Var[X; μ] * Var[Y; μ] := by nlinarith [hdisc]
    _ ≤ ((M - m) / 2) ^ 2 * ((N - n) / 2) ^ 2 :=
        mul_le_mul hVX hVY (variance_nonneg _ _) (sq_nonneg _)
    _ = ((M - m) * (N - n) / 4) ^ 2 := by ring

/-- **Grüss's inequality for averages on an interval** (order LEAN-29, item 92 of
MATH-PLAN-library-2). For `a < b` and functions `f` and `g`, interval-integrable on `[a, b]`, with
`f` in `[m, M]` and `g` in `[n, N]` on `[a, b]`, the average of `f g` over `[a, b]` is within
`(M − m)(N − n)/4` of the product of the averages of `f` and `g`. This is
`abs_covariance_le_mul_div_four` for the uniform probability on `[a, b]`. -/
theorem abs_average_mul_sub_le {f g : ℝ → ℝ} {a b m M n N : ℝ} (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (hfb : ∀ x ∈ Set.Icc a b, f x ∈ Set.Icc m M) (hgb : ∀ x ∈ Set.Icc a b, g x ∈ Set.Icc n N) :
    |(b - a)⁻¹ * (∫ x in a..b, f x * g x) -
        ((b - a)⁻¹ * (∫ x in a..b, f x)) * ((b - a)⁻¹ * (∫ x in a..b, g x))| ≤
      (M - m) * (N - n) / 4 := by
  -- the uniform probability on `[a, b]`
  set μ : Measure ℝ := (volume : Measure ℝ)[|Set.Icc a b] with hμ
  have hvol : volume (Set.Icc a b) = ENNReal.ofReal (b - a) := Real.volume_Icc
  have hv0 : volume (Set.Icc a b) ≠ 0 := by
    rw [hvol]
    exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hab)
  have hvt : volume (Set.Icc a b) ≠ ⊤ := by
    rw [hvol]
    exact ENNReal.ofReal_ne_top
  have : IsProbabilityMeasure μ := cond_isProbabilityMeasure_of_finite hv0 hvt
  have hμdef : μ = (volume (Set.Icc a b))⁻¹ • volume.restrict (Set.Icc a b) := rfl
  -- `f` and `g` on the interval
  have hfI : IntegrableOn f (Set.Icc a b) :=
    (integrableOn_Icc_iff_integrableOn_Ioc).mpr ((intervalIntegrable_iff_integrableOn_Ioc_of_le
      hab.le).mp hf)
  have hgI : IntegrableOn g (Set.Icc a b) :=
    (integrableOn_Icc_iff_integrableOn_Ioc).mpr ((intervalIntegrable_iff_integrableOn_Ioc_of_le
      hab.le).mp hg)
  have hfm : AEMeasurable f μ := hμdef ▸ hfI.aemeasurable.smul_measure _
  have hgm : AEMeasurable g μ := hμdef ▸ hgI.aemeasurable.smul_measure _
  have hfb' : ∀ᵐ x ∂μ, f x ∈ Set.Icc m M := ae_cond_of_forall_mem measurableSet_Icc hfb
  have hgb' : ∀ᵐ x ∂μ, g x ∈ Set.Icc n N := ae_cond_of_forall_mem measurableSet_Icc hgb
  have key := abs_covariance_le_mul_div_four hfm hgm hfb' hgb'
  rw [covariance_eq_sub (memLp_of_bounded hfb' hfm.aestronglyMeasurable 2)
    (memLp_of_bounded hgb' hgm.aestronglyMeasurable 2)] at key
  -- an integral against `μ` is an average over `[a, b]`
  have hint (φ : ℝ → ℝ) : ∫ x, φ x ∂μ = (b - a)⁻¹ * ∫ x in a..b, φ x := by
    rw [hμdef, integral_smul_measure, ENNReal.toReal_inv, hvol,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le), intervalIntegral.integral_of_le hab.le,
      ← integral_Icc_eq_integral_Ioc, smul_eq_mul]
  rw [hint, hint, hint] at key
  simpa only [Pi.mul_apply] using key

end ClassicalLean.Analysis

/-- The hypotheses of `abs_covariance_le_mul_div_four` hold together: a fair coin (the uniform
probability on the two points of `Bool`), `X` the indicator of `true` and `Y` the indicator of
`false`, neither constant, each measurable and within `[0, 1]`. -/
example := ClassicalLean.Analysis.abs_covariance_le_mul_div_four (Ω := Bool)
  (μ := ProbabilityTheory.uniformOn Set.univ)
  (X := fun ω ↦ if ω then 1 else 0) (Y := fun ω ↦ if ω then 0 else 1)
  (m := 0) (M := 1) (n := 0) (N := 1)
  (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable
  (MeasureTheory.ae_of_all _ fun ω ↦ by cases ω <;> simp)
  (MeasureTheory.ae_of_all _ fun ω ↦ by cases ω <;> simp)

/-- The hypotheses of `abs_average_mul_sub_le` hold together: `f = g = x` on `[0, 1]`, an interval
of positive length, both continuous and not constant, each within `[0, 1]` there. -/
example := ClassicalLean.Analysis.abs_average_mul_sub_le (f := fun x ↦ x) (g := fun x ↦ x)
  (a := 0) (b := 1) (m := 0) (M := 1) (n := 0) (N := 1) (by norm_num)
  (continuous_id.intervalIntegrable 0 1) (continuous_id.intervalIntegrable 0 1)
  (fun _ hx ↦ hx) (fun _ hx ↦ hx)
