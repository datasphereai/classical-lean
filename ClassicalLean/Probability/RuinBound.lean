/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Probability.MaximalInequality
import Mathlib.Probability.Independence.Basic

/-!
# The chance of falling to half, from the two-outcome condition alone

`MaximalInequality.measureReal_exists_le_half_of_iIndepFun` bounds the chance of falling to half
by `2 ^ (-θ)` when each step factor `F i` has `E[F i ^ (-θ)] ≤ 1`. For a step that multiplies by
`1 + b x` on a win (chance `p`) and by `1 - x` otherwise, that mean is
`p (1 + b x) ^ (-θ) + (1 - p) (1 - x) ^ (-θ)`, and `ruinConditionOK p b x θ` decides exactly
whether it is at most `1`. This file joins the two:

* `integral_twoPointFactor_rpow`: the mean of a two-valued factor raised to a power;
* `measureReal_exists_le_half_of_ruinConditionOK`: with independent win events of chance `p`,
  rationals `p b x` with `0 < 1 - x`, `0 < 1 + b x`, a whole number `θ`, and
  `ruinConditionOK p b x θ = true`, the chance of falling to half within `N` steps is at most
  `2 ^ (-θ)`;
* `measureReal_exists_le_half_of_ruinConditionOK_ever`: the same with no limit on the number of
  steps, by continuity of the measure from below (`tendsto_measure_iUnion_atTop`);
* `measureReal_iUnion_le_of_monotone`: that limit step for any increasing sequence of sets.

Each hypothesis is needed. With `p = 9/20`, `b = 1`, `x = 3/10`, `θ = 2` the condition fails and
the exact chance of halving within 400 steps is `1.0` against `2 ^ (-2)`. With `x = 1` the
condition passes in Lean (`1 / 0 = 0`) though one loss takes the value to `0`. Dropping
independence: if every step copies the first, the chance of halving is at least `1 - p`.
-/

open MeasureTheory Filter Finset ProbabilityTheory
open ClassicalLean.Probability.MaximalInequality

namespace ClassicalLean.Probability.RuinBound

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

open scoped Classical in
/-- The step factor that is `u` on the event `W i` and `v` off it. -/
noncomputable def twoPointFactor (W : ℕ → Set Ω) (u v : ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  if ω ∈ W i then u else v

lemma twoPointFactor_eq_indicator (W : ℕ → Set Ω) (u v : ℝ) (i : ℕ) :
    twoPointFactor W u v i = fun ω ↦ v + (u - v) * (W i).indicator (fun _ ↦ (1 : ℝ)) ω := by
  funext ω
  by_cases h : ω ∈ W i <;> simp [twoPointFactor, h]

lemma twoPointFactor_rpow (W : ℕ → Set Ω) {u v : ℝ} (r : ℝ) (i : ℕ) :
    (fun ω ↦ twoPointFactor W u v i ω ^ r) = twoPointFactor W (u ^ r) (v ^ r) i := by
  funext ω
  by_cases h : ω ∈ W i <;> simp [twoPointFactor, h]

/-- **The mean of a two-valued factor raised to a power.** If the factor is `u` on an event of
chance `μ.real (W i)` and `v` off it, the mean of its `r`-th power is
`μ.real (W i) · u ^ r + (1 - μ.real (W i)) · v ^ r`. -/
theorem integral_twoPointFactor_rpow [IsProbabilityMeasure μ] {W : ℕ → Set Ω}
    (hW : ∀ i, MeasurableSet (W i)) (u v r : ℝ) (i : ℕ) :
    ∫ ω, twoPointFactor W u v i ω ^ r ∂μ =
      μ.real (W i) * u ^ r + (1 - μ.real (W i)) * v ^ r := by
  rw [twoPointFactor_rpow, twoPointFactor_eq_indicator]
  rw [integral_add (integrable_const _)
    ((integrable_const (1 : ℝ)).indicator (hW i) |>.const_mul _), integral_const,
    integral_const_mul, integral_indicator_const _ (hW i)]
  simp only [probReal_univ, smul_eq_mul, one_mul, mul_one]
  ring

/-- **Continuity from below, for a bound.** If an increasing sequence of sets has chance at most
`c` at every stage, its union has chance at most `c`. -/
theorem measureReal_iUnion_le_of_monotone [IsFiniteMeasure μ] {A : ℕ → Set Ω} (hA : Monotone A)
    {c : ℝ} (hc : ∀ N, μ.real (A N) ≤ c) : μ.real (⋃ N, A N) ≤ c := by
  have hc0 : 0 ≤ c := (measureReal_nonneg).trans (hc 0)
  have hlim := tendsto_measure_iUnion_atTop (μ := μ) hA
  have hle : μ (⋃ N, A N) ≤ ENNReal.ofReal c :=
    le_of_tendsto' hlim fun N ↦ by
      simp only [Function.comp_apply]
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ (A N))]
      exact ENNReal.ofReal_le_ofReal (hc N)
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rwa [ENNReal.toReal_ofReal hc0] at this

/-- The step factors built from independent events are independent. -/
lemma iIndepFun_twoPointFactor {W : ℕ → Set Ω} (hind : iIndepSet W μ) (u v : ℝ) :
    iIndepFun (twoPointFactor W u v) μ := by
  have h := hind.iIndepFun_indicator (β := ℝ) (m := Real.measurableSpace)
  have hcomp := h.comp (fun _ y ↦ v + (u - v) * y) (fun _ ↦ by fun_prop)
  convert hcomp using 1
  funext i
  rw [twoPointFactor_eq_indicator]
  rfl

variable [IsProbabilityMeasure μ]

/-- **The chance of falling to half, from the exact check.** Let the win events `W i` be
independent, measurable, each of chance `p`. Stake the fraction `x` each step: a win multiplies
the value by `1 + b x` and a loss by `1 - x`, with `p b x` rational, `0 < 1 - x` and
`0 < 1 + b x`. If `ruinConditionOK p b x θ` holds for a whole number `θ`, the chance that the
value falls to half its start within `N` steps is at most `2 ^ (-θ)`. -/
theorem measureReal_exists_le_half_of_ruinConditionOK {W : ℕ → Set Ω}
    (hW : ∀ i, MeasurableSet (W i)) (hind : iIndepSet W μ) {p b x : ℚ}
    (hp : ∀ i, μ.real (W i) = p) (hv : 0 < 1 - x) (hu : 0 < 1 + b * x) {θ : ℕ}
    (hok : ruinConditionOK p b x θ = true) {w₀ : ℝ} (hw₀ : 0 < w₀) (N : ℕ) :
    μ.real {ω | ∃ n ≤ N, w₀ * ∏ i ∈ range n,
        twoPointFactor W (1 + b * x) (1 - x) (i + 1) ω ≤ w₀ / 2} ≤ (2 : ℝ) ^ (-(θ : ℝ)) := by
  rcases Nat.eq_zero_or_pos θ with rfl | hθ
  · simp
  have hu' : (0 : ℝ) < 1 + (b : ℝ) * x := by exact_mod_cast hu
  have hv' : (0 : ℝ) < 1 - (x : ℝ) := by exact_mod_cast hv
  have hcond := (ruinConditionOK_iff θ hu hv).mp hok
  refine measureReal_exists_le_half_of_iIndepFun (lo := min (1 + (b : ℝ) * x) (1 - x))
    (hi := max (1 + (b : ℝ) * x) (1 - x)) (fun i ↦ ?_) (iIndepFun_twoPointFactor hind _ _)
    (lt_min hu' hv') (fun i ω ↦ ?_) (by exact_mod_cast hθ) (fun i ↦ ?_) hw₀ N
  · rw [twoPointFactor_eq_indicator]
    exact (((stronglyMeasurable_const.indicator (hW i)).const_mul _).const_add _)
  · by_cases h : ω ∈ W i <;> simp [twoPointFactor, h]
  · rw [integral_twoPointFactor_rpow hW, hp]
    linarith

/-- **The chance of ever falling to half.** Under the hypotheses of
`measureReal_exists_le_half_of_ruinConditionOK`, the chance that the value falls to half its
start at some step, with no limit on the number of steps, is at most `2 ^ (-θ)`. -/
theorem measureReal_exists_le_half_of_ruinConditionOK_ever {W : ℕ → Set Ω}
    (hW : ∀ i, MeasurableSet (W i)) (hind : iIndepSet W μ) {p b x : ℚ}
    (hp : ∀ i, μ.real (W i) = p) (hv : 0 < 1 - x) (hu : 0 < 1 + b * x) {θ : ℕ}
    (hok : ruinConditionOK p b x θ = true) {w₀ : ℝ} (hw₀ : 0 < w₀) :
    μ.real {ω | ∃ n, w₀ * ∏ i ∈ range n,
        twoPointFactor W (1 + b * x) (1 - x) (i + 1) ω ≤ w₀ / 2} ≤ (2 : ℝ) ^ (-(θ : ℝ)) := by
  have hmono : Monotone fun N ↦ {ω | ∃ n ≤ N, w₀ * ∏ i ∈ range n,
      twoPointFactor W (1 + b * x) (1 - x) (i + 1) ω ≤ w₀ / 2} := by
    intro N M hNM ω ⟨n, hn, h⟩
    exact ⟨n, hn.trans hNM, h⟩
  have hU : {ω | ∃ n, w₀ * ∏ i ∈ range n,
      twoPointFactor W (1 + b * x) (1 - x) (i + 1) ω ≤ w₀ / 2} =
      ⋃ N, {ω | ∃ n ≤ N, w₀ * ∏ i ∈ range n,
        twoPointFactor W (1 + b * x) (1 - x) (i + 1) ω ≤ w₀ / 2} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨fun ⟨n, h⟩ ↦ ⟨n, n, le_rfl, h⟩, fun ⟨_, n, _, h⟩ ↦ ⟨n, h⟩⟩
  rw [hU]
  exact measureReal_iUnion_le_of_monotone hmono fun N ↦
    measureReal_exists_le_half_of_ruinConditionOK hW hind hp hv hu hok hw₀ N

end ClassicalLean.Probability.RuinBound
