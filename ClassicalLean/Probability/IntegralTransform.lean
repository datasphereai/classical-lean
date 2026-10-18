/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The probability integral transform

A real random variable `X` on a probability space, and `F = cdf (μ.map X)`, Mathlib's distribution
function of `X`, `F x = P(X ≤ x)`.

* `measureReal_cdf_le_le` — order LEAN-32, item 106: `P(F(X) ≤ u) ≤ u` for every `u ≥ 0`. So the
  p-value `F(X)` of a test that rejects for small values of `X` is valid: under the hypothesis, it
  is at most `u` with chance at most `u`.
* `measureReal_cdf_le_eq_of_continuous` — when `F` is continuous, `P(F(X) ≤ u) = u` for every
  `u ∈ [0, 1]`: `F(X)` is uniform on `[0, 1]`.

The proof of the bound. `F` is monotone, so `S = {x | F x ≤ u}` is a ray: empty (chance `0`), all
of `ℝ` (then `1 ≤ u`, since `F → 1`), `(−∞, a]` with `F a ≤ u`, or `(−∞, a)` with
`F (a⁻) ≤ u`, where `a` is the supremum of `S` and `F (a⁻)` the left limit; the chance of `X`
lying in the ray is at most `F a` or `F (a⁻)`. For the equality, Mathlib's intermediate value
theorem (`intermediate_value_univ`) finds `a` with `F a = u` when `0 < u < 1`, and
`{X ≤ a} ⊆ {F(X) ≤ u}`; the cases `u = 0` and `u = 1` are direct.

## Hypotheses

Each needed hypothesis has a case (order LEAN-32's checks, exact fractions, on discrete laws):
`0 ≤ u`, at `u = −1/2` the left side is `0` (`F ≥ 0`), above `u` (line `106.u_neg`; for `u < 0`
the bound would ask a chance to be negative); continuity of `F`, for a fair coin on `{0, 1}` and
`u = 1/4` the left side is `0`, not `1/4` (`106.eq_cont`); `u ≤ 1`, at `u = 3/2` the left side is
`1`, not `3/2` (`106.eq_le1`). Not shown needed: the measurability of `X` and the probability
measure. Both are what makes `F` the distribution function of `X` and the left side a chance;
Lean's `μ.map X` for an `X` that is not almost everywhere measurable is a junk value, which this
file does not use. The bound holds on 49 values of `u` in `[0, 2]` for five discrete laws, where
`F` jumps (`106.le`).

The witness of the equality uses the standard normal law `gaussianReal 0 1` with `X` the identity:
Mathlib knows it is a probability measure and that it puts no mass on a point
(`nullSingletonClass_gaussianReal`), so its distribution function has no jump. The order suggested
the uniform law on `[0, 1]`, `volume.restrict (Set.Icc 0 1)`. It is a probability measure (its
mass is `volume (Set.Icc 0 1) = 1`, Mathlib's `Real.volume_Icc`), but no instance under this
module's imports says so, and the witness's standing form, the theorem applied by named
arguments, has no slot for one: the instance argument has no name. Supplying it by an `@`
application or a `haveI` would leave that form. (Mathlib gives the unit interval, as its own type,
a probability measure by an instance in `Mathlib.MeasureTheory.Constructions.UnitInterval`, read
in its source, by hand; that module is outside the library's imports.) Where the law is uniform
on `[0, 1]`, `F x = x` there and `P(F(X) ≤ u) = u` (by hand, line `106.eq_uniform`).

## Mathlib at v4.34.0

Searched for order LEAN-32 (the plan's check `row.B5`, `probability integral transform`): 0 hits
in Mathlib at this pin and at master `2da3ab0a`, 0 in the library. Used: `cdf`, `cdf_eq_real`,
`measure_cdf`, `tendsto_cdf_atBot`, `tendsto_cdf_atTop`, `StieltjesFunction.measure_Iio`,
`Monotone.tendsto_leftLim`, `intermediate_value_univ`, `map_measureReal_apply`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace ClassicalLean.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The probability integral transform, the bound** (order LEAN-32, item 106): for a real random
variable `X` with distribution function `F`, `P(F(X) ≤ u) ≤ u` for every `u ≥ 0`. -/
theorem measureReal_cdf_le_le [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | cdf (μ.map X) (X ω) ≤ u} ≤ u := by
  set ν := μ.map X with hν
  set F := cdf ν with hFdef
  set S := {x : ℝ | F x ≤ u} with hS
  have hSm : MeasurableSet S := measurableSet_le F.mono.measurable measurable_const
  have hpre : μ.real {ω | F (X ω) ≤ u} = ν.real S := by
    rw [hν, map_measureReal_apply hX hSm]
    rfl
  rw [hpre]
  have hlow : ∀ x y, x ≤ y → y ∈ S → x ∈ S := fun x y hxy hy ↦ (F.mono hxy).trans hy
  by_cases hne : S.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, measureReal_empty]
    exact hu
  by_cases hbdd : BddAbove S
  swap
  · have hall : ∀ x, F x ≤ u := fun x ↦ by
      obtain ⟨y, hy, hxy⟩ := not_bddAbove_iff.1 hbdd x
      exact hlow x y hxy.le hy
    exact measureReal_le_one.trans (le_of_tendsto' (tendsto_cdf_atTop ν) hall)
  by_cases ha : sSup S ∈ S
  · have hsub : S ⊆ Set.Iic (sSup S) := fun x hx ↦ le_csSup hbdd hx
    calc ν.real S ≤ ν.real (Set.Iic (sSup S)) := measureReal_mono hsub
      _ = F (sSup S) := (cdf_eq_real ν _).symm
      _ ≤ u := ha
  · have hsub : S ⊆ Set.Iio (sSup S) := fun x hx ↦
      lt_of_le_of_ne (le_csSup hbdd hx) fun h ↦ ha (h ▸ hx)
    have hleft : Function.leftLim F (sSup S) ≤ u := by
      refine le_of_tendsto (F.mono.tendsto_leftLim (sSup S)) ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      obtain ⟨s, hs, hys⟩ := exists_lt_of_lt_csSup hne hy
      exact hlow y s hys.le hs
    have hIio : ν.real (Set.Iio (sSup S)) = Function.leftLim F (sSup S) := by
      rw [measureReal_def, ← measure_cdf (μ := ν), ← hFdef, F.measure_Iio (tendsto_cdf_atBot ν),
        sub_zero, ENNReal.toReal_ofReal]
      exact (cdf_nonneg _ _).trans (F.mono.le_leftLim (sub_one_lt (sSup S)))
    calc ν.real S ≤ ν.real (Set.Iio (sSup S)) := measureReal_mono hsub
      _ = Function.leftLim F (sSup S) := hIio
      _ ≤ u := hleft

/-- **The probability integral transform** (order LEAN-32, item 106): when the distribution
function `F` of `X` is continuous, `F(X)` is uniform on `[0, 1]`: `P(F(X) ≤ u) = u` for
`0 ≤ u ≤ 1`. -/
theorem measureReal_cdf_le_eq_of_continuous [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (hF : Continuous (cdf (μ.map X))) {u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) :
    μ.real {ω | cdf (μ.map X) (X ω) ≤ u} = u := by
  refine le_antisymm (measureReal_cdf_le_le hX hu0) ?_
  rcases hu0.eq_or_lt with h0 | h0
  · rw [← h0]
    exact measureReal_nonneg
  rcases hu1.eq_or_lt with h1 | h1
  · have huniv : {ω | cdf (μ.map X) (X ω) ≤ u} = Set.univ :=
      Set.eq_univ_of_forall fun ω ↦ h1 ▸ cdf_le_one _ _
    rw [huniv, probReal_univ, h1]
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atBot (μ.map X)).eventually (gt_mem_nhds h0)).exists
  obtain ⟨c, hc⟩ := ((tendsto_cdf_atTop (μ.map X)).eventually (lt_mem_nhds h1)).exists
  obtain ⟨a, ha⟩ := intermediate_value_univ b c hF ⟨hb.le, hc.le⟩
  have hsub : X ⁻¹' Set.Iic a ⊆ {ω | cdf (μ.map X) (X ω) ≤ u} := fun ω hω ↦
    ha ▸ (cdf (μ.map X)).mono hω
  calc u = cdf (μ.map X) a := ha.symm
    _ = (μ.map X).real (Set.Iic a) := cdf_eq_real _ a
    _ = μ.real (X ⁻¹' Set.Iic a) := map_measureReal_apply hX measurableSet_Iic
    _ ≤ μ.real {ω | cdf (μ.map X) (X ω) ≤ u} := measureReal_mono hsub

end ClassicalLean.Probability

/-- The hypotheses of `measureReal_cdf_le_le` hold together: `X` the identity under the standard
normal law `gaussianReal 0 1`, and `u = 1/2`. -/
example := ClassicalLean.Probability.measureReal_cdf_le_le (Ω := ℝ)
  (μ := ProbabilityTheory.gaussianReal 0 1) (X := id) measurable_id (u := 1 / 2) (by norm_num)

/-- The hypotheses of `measureReal_cdf_le_eq_of_continuous` hold together: `X` the identity under
the standard normal law `gaussianReal 0 1`, whose distribution function is continuous because the
law puts no mass on a point (`nullSingletonClass_gaussianReal`), and `u = 1/2`. -/
example := ClassicalLean.Probability.measureReal_cdf_le_eq_of_continuous (Ω := ℝ)
  (μ := gaussianReal 0 1) (X := id) measurable_id
  (by
    rw [Measure.map_id]
    have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    refine continuous_iff_continuousAt.2 fun a ↦ ?_
    rw [(cdf (gaussianReal 0 1)).mono.continuousAt_iff_leftLim_eq_rightLim,
      StieltjesFunction.rightLim_eq]
    have h := (cdf (gaussianReal 0 1)).measure_singleton a
    rw [measure_cdf, MeasureTheory.measure_singleton] at h
    linarith [ENNReal.ofReal_eq_zero.1 h.symm,
      (cdf (gaussianReal 0 1)).mono.leftLim_le (le_refl a)])
  (u := 1 / 2) (by norm_num) (by norm_num)
