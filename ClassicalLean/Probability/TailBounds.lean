/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Statistics.RaoBlackwell

/-!
# Two tail bounds: Cantelli's inequality and the Paley–Zygmund inequality

On a probability space:

* `measureReal_sub_integral_ge_le` — **Cantelli's inequality** (the one-sided Chebyshev
  inequality): for `X` square-integrable with variance `σ²` and `t > 0`,
  `P(X − E X ≥ t) ≤ σ² / (σ² + t²)`. It is sharp (not proved here; equality for two-point laws
  is checked in exact arithmetic in order LEAN-20's checks).
* `measureReal_gt_ge` — **the Paley–Zygmund inequality**: for `0 ≤ θ ≤ 1`,
  `P(X > θ E X) ≥ (1 − θ)² (E X)² / E[X²]`, assuming only `E X ≥ 0` (review r27's weakening; no
  sign, measurability or integrability is assumed of `X`). A lower bound on a tail from the first
  two moments.
* `measureReal_gt_ge_of_nonneg` — the usual form, for `X ≥ 0` almost everywhere.

Cited: Cantelli's inequality as in F. P. Cantelli, "Sui confini della probabilità", Atti del
Congresso Internazionale dei Matematici, Bologna 1928 (printed 1932); Paley and Zygmund (1932), in
the modern form above. Checked for this order by web search against secondary sources only: the
statements match the standard modern forms; neither original was read, and the 1932 papers state
the Paley–Zygmund bound for functions in a form not checked here.

## Hypotheses

Measured in order LEAN-20's checks (checks C27 and C28, exact rationals), each on 2000 finite
distributions. Each hypothesis fails when dropped alone:

* Cantelli, `0 < t`: for `X = 0`, at `t = 0` the chance is `1` and Lean's `0 / 0` is `0`; at
  `t = −1` the chance is `1` and the bound `0`.
* Cantelli, probability measure: one point of mass `1/2` with `X = 1` and `t = 1/2`. Lean's
  integral is `1/2`, its variance `∫ (X − 1/2)² = 1/8`, so the bound is `1/3`, but the measure of
  the event is `1/2`.
* Cantelli, `X` square-integrable (worked by hand): with `P(X = 2ᵏ) = (3/4) 4^(−k)`, `E X = 3/2`
  but `E X² = ∞`, so Lean's variance is `0` and the bound `0`, while `P(X − E X ≥ 1) ≥ 1/16`.
* Paley–Zygmund, `θ ≤ 1`: `X = 1`, `θ = 2`: bound `1`, chance `0`. `0 ≤ θ`: `X = 1`, `θ = −1`:
  bound `4`, chance `1`. `0 ≤ E X` (and so `0 ≤ X`): `X = −1`, `θ = 0`: bound `1`, chance `0`.
* Paley–Zygmund, probability measure: one point of mass `2`, `X = 1`, `θ = 1/2`: Lean's `E X = 2`,
  `E X² = 2`, bound `1/2`, but `{1 < 1}` is empty.

Paley–Zygmund needs no integrability: if `X` or `X²` is not integrable, Lean's `E X` or `E[X²]`
is `0` and so is the bound.

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-20, `grep -rniE` over Mathlib): `cantelli` 41
lines in 7 files, all Borel–Cantelli; `one.?sided (chebyshev|tchebych)` 0; `paley|zygmund` 0.
Used: Mathlib's Markov inequality in the form `mul_meas_ge_le_integral_of_nonneg` (Mathlib's
Chebyshev inequality, `meas_ge_le_variance_div_sq`, also rests on Markov's inequality, through
`mul_meas_ge_le_pow_eLpNorm`), and order LEAN-19's `integral_sub_sq_eq_variance_add_sq`. The
Paley–Zygmund proof does not use Mathlib's Cauchy–Schwarz for integrals, which the plan's row
names: it bounds `2 X 1_A ≤ l X² + 1_A / l` and optimises over `l`, which gives the same bound.
The name `measureReal_gt_ge` is the order's.
-/

open MeasureTheory ProbabilityTheory

namespace ClassicalLean.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Cantelli's inequality.** For `X` square-integrable on a probability space and `t > 0`,
`P(X − E X ≥ t) ≤ Var X / (Var X + t²)`. Shift by `u = Var X / t` and apply Markov's inequality to
`(X − E X + u)²`, whose mean is `Var X + u²`. -/
theorem measureReal_sub_integral_ge_le {X : Ω → ℝ} (hX : MemLp X 2 μ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ X ω - ∫ x, X x ∂μ} ≤ Var[X; μ] / (Var[X; μ] + t ^ 2) := by
  set m := ∫ x, X x ∂μ
  set V := Var[X; μ]
  have hV : 0 ≤ V := variance_nonneg X μ
  set u := V / t
  have hu : 0 ≤ u := div_nonneg hV ht.le
  have htu : 0 < t + u := by positivity
  have hint : Integrable (fun ω ↦ (X ω - (m - u)) ^ 2) μ :=
    (hX.sub (memLp_const (m - u))).integrable_sq
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω ↦ sq_nonneg _) hint
    ((t + u) ^ 2)
  rw [ClassicalLean.Statistics.integral_sub_sq_eq_variance_add_sq hX (m - u)] at hmarkov
  have hmu : (m - (m - u)) ^ 2 = u ^ 2 := by ring
  rw [hmu] at hmarkov
  have hsub : {ω | t ≤ X ω - m} ⊆ {ω | (t + u) ^ 2 ≤ (X ω - (m - u)) ^ 2} := by
    intro ω hω
    have h1 : t ≤ X ω - m := hω
    have h2 : t + u ≤ X ω - (m - u) := by linarith
    exact pow_le_pow_left₀ htu.le h2 2
  have htu2 : 0 < (t + u) ^ 2 := by positivity
  calc μ.real {ω | t ≤ X ω - m} ≤ μ.real {ω | (t + u) ^ 2 ≤ (X ω - (m - u)) ^ 2} :=
        measureReal_mono hsub
    _ ≤ (V + u ^ 2) / (t + u) ^ 2 := by
        rw [le_div_iff₀ htu2]
        linarith
    _ = V / (V + t ^ 2) := by
        have hVt : 0 < V + t ^ 2 := by positivity
        simp only [u]
        field_simp
        ring

/-- **The Paley–Zygmund inequality.** On a probability space, for `0 ≤ θ ≤ 1` and any `X` with
`E X ≥ 0`: `P(X > θ E X) ≥ (1 − θ)² (E X)² / E[X²]`. Nothing else is assumed of `X`: if `X` or
`X²` is not integrable, Lean's `E X` or `E[X²]` is `0` and the bound is `0`. Otherwise, on the
event `A = {X > θ E X}` write `X ≤ θ E X + X 1_A`, and bound `2 X 1_A ≤ l X² + 1_A / l` for every
`l > 0`; `l = (1 − θ) E X / E[X²]` gives the result. Review r27 found that `E X ≥ 0` suffices and
gave this proof. -/
theorem measureReal_gt_ge {X : Ω → ℝ} (hm0 : 0 ≤ ∫ ω, X ω ∂μ) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) :
    (1 - θ) ^ 2 * (∫ ω, X ω ∂μ) ^ 2 / ∫ ω, X ω ^ 2 ∂μ
      ≤ μ.real {ω | θ * ∫ x, X x ∂μ < X ω} := by
  set m := ∫ ω, X ω ∂μ
  set A := {ω | θ * m < X ω}
  set s := ∫ ω, X ω ^ 2 ∂μ
  have hA0 : 0 ≤ μ.real A := measureReal_nonneg
  by_cases h1 : Integrable X μ
  swap
  · rw [show m = 0 from integral_undef h1]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div]
    exact hA0
  by_cases h2 : Integrable (fun ω ↦ X ω ^ 2) μ
  swap
  · rw [show s = 0 from integral_undef h2, div_zero]
    exact hA0
  have hXm : AEStronglyMeasurable X μ := h1.aestronglyMeasurable
  have hs0 : 0 ≤ s := integral_nonneg fun ω ↦ sq_nonneg _
  by_cases hs : s = 0
  · rw [hs, div_zero]
    exact hA0
  have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
  have hAnull : NullMeasurableSet A μ := nullMeasurableSet_lt aemeasurable_const hXm.aemeasurable
  have hind : Integrable (A.indicator fun _ ↦ (1 : ℝ)) μ := (integrable_const 1).indicator₀ hAnull
  have hindint : ∫ ω, A.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ = μ.real A := by
    rw [integral_indicator₀ hAnull, setIntegral_const, smul_eq_mul, mul_one]
  set c := (1 - θ) * m
  have hc0 : 0 ≤ c := mul_nonneg (by linarith) hm0
  have key : ∀ l : ℝ, 0 < l → 2 * c ≤ l * s + μ.real A / l := by
    intro l hl
    have hpt : ∀ ω,
        2 * X ω ≤ 2 * (θ * m) + l * X ω ^ 2 + A.indicator (fun _ ↦ (1 : ℝ)) ω / l := by
      intro ω
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω]
        have h1 : 2 * X ω ≤ l * X ω ^ 2 + 1 / l := by
          rw [← sub_nonneg]
          have : l * X ω ^ 2 + 1 / l - 2 * X ω = (l * X ω - 1) ^ 2 / l := by
            field_simp
            ring
          rw [this]
          positivity
        nlinarith [mul_nonneg hθ0 hm0]
      · rw [Set.indicator_of_notMem hω, zero_div, add_zero]
        have h1 : X ω ≤ θ * m := not_lt.mp hω
        nlinarith [sq_nonneg (X ω), hl.le]
    have hint : ∫ ω, 2 * X ω ∂μ
        ≤ ∫ ω, (2 * (θ * m) + l * X ω ^ 2 + A.indicator (fun _ ↦ (1 : ℝ)) ω / l) ∂μ :=
      integral_mono (h1.const_mul 2)
        (((integrable_const _).add (h2.const_mul l)).add (hind.div_const l)) hpt
    rw [integral_const_mul,
      integral_add (f := fun ω ↦ 2 * (θ * m) + l * X ω ^ 2)
        (g := fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω / l)
        ((integrable_const _).add (h2.const_mul l)) (hind.div_const l),
      integral_add (f := fun _ ↦ 2 * (θ * m)) (g := fun ω ↦ l * X ω ^ 2)
        (integrable_const _) (h2.const_mul l), integral_const,
      integral_const_mul, integral_div, hindint] at hint
    simp only [probReal_univ, smul_eq_mul, one_mul] at hint
    simp only [c]
    linarith
  have hcs : c ^ 2 ≤ s * μ.real A := by
    rcases hc0.eq_or_lt with hc | hc
    · rw [← hc]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
    · have h := key (c / s) (div_pos hc hspos)
      have h' : c / s * s = c := div_mul_cancel₀ c hs
      rw [h', div_div_eq_mul_div] at h
      have h3 : c ≤ μ.real A * s / c := by linarith
      rw [le_div_iff₀ hc] at h3
      nlinarith
  rw [div_le_iff₀ hspos]
  have : (1 - θ) ^ 2 * m ^ 2 = c ^ 2 := by simp only [c]; ring
  rw [this]
  linarith

/-- **The Paley–Zygmund inequality, the usual form**: for `X ≥ 0` almost everywhere and
`0 ≤ θ ≤ 1`, `P(X > θ E X) ≥ (1 − θ)² (E X)² / E[X²]`. -/
theorem measureReal_gt_ge_of_nonneg {X : Ω → ℝ} (hX0 : 0 ≤ᵐ[μ] X) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) :
    (1 - θ) ^ 2 * (∫ ω, X ω ∂μ) ^ 2 / ∫ ω, X ω ^ 2 ∂μ
      ≤ μ.real {ω | θ * ∫ x, X x ∂μ < X ω} :=
  measureReal_gt_ge (integral_nonneg_of_ae hX0) hθ0 hθ1

end ClassicalLean.Probability
