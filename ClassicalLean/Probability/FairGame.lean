/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.ConditionalExpectation

/-!
# No stopping rule beats a fair game

If `f n` is a martingale (each step's expected change is `0` given everything up to that step),
then for any stopping rule `τ` that never waits past a fixed time `N`, the expected value at the
moment of stopping equals the expected value at the start (`integral_stoppedValue_eq`). Deciding
*when* to stop, using only what has happened so far, cannot turn a fair game into a favourable one.

## Wald's identity for a bounded stopping time

Order LEAN-21 (item 35 of the plan) adds Wald's identity: for running sums `S n` with `S 0 = 0`,
whose every step has mean `m` given the past, and a stopping rule `τ` that never waits past `N`,
`E[S τ] = m E[τ]` (`integral_stoppedValue_eq_mul`). The usual form, with independent steps of mean
`m`, follows (`integral_stoppedValue_sum_eq`). Citation: Wald 1944, "On cumulative sums of random
variables". Only stopping times bounded by a fixed `N` are covered here, and the steps need not be
independent or identically distributed, only of mean `m` given the past. `E[τ]` is written
`∫ ω, ((τ ω).untopA : ℝ) ∂μ`, the mean of the stopping time's value.

Measured in order LEAN-21's checks (check C35, exact enumeration): four step laws (means `0`,
`1/2`, `1/4`, `7/5`) with bounded stopping rules. Each hypothesis below is needed: drop it alone
and the conclusion fails at the case given (worked out by hand; the check script records the
arithmetic):

* each step of mean `m` given the past: `X₀ = ±1` fair, `X₁ = X₀`, `τ = 2` if `X₀ = 1` else `1`,
  `m = 0`: `E[S τ] = 1/2`.
* `S 0 = 0`: `S n = 1 +` a fair `±1` walk, `τ = 1`, `m = 0`: `E[S τ] = 1`.
* `τ` a stopping time: fair `±1` steps, `τ = 1` if `X₁ = −1` else `2` (it looks ahead): `1/2 ≠ 0`.
* `τ ≤ N`: a fair walk stopped when it first reaches `1`; `S τ = 1` almost surely, so
  `E[S τ] = 1`, while `m = 0` gives `m E[τ] = 0`.

Not claimed needed: that `S` is adapted, and in the independent form that `X n` is known by time
`n + 1` (both serve the proof, which builds a martingale); and `S 0 = 0` only fixes the start,
since `E[S τ] = E[S 0] + m E[τ]` follows in the same way (review r35).

## What Mathlib provides

The optional stopping theorem in its monotone form,
`MeasureTheory.Submartingale.expected_stoppedValue_mono`: for a submartingale and bounded stopping
times `τ ≤ π`, `E[f_τ] ≤ E[f_π]`. This module applies it to the martingale and to its negative,
with the constant stopping time `0`, to get equality. For Wald's identity:
`martingale_of_condExp_sub_eq_zero_nat`, `condExp_indep_eq`, `integrable_stoppedValue`. Searched
before item 35 was written (order LEAN-21, `grep -rniE` over Mathlib): `wald` matches only inside
an author's name ("Turnwald"); `stoppedValue.*integral|integral.*stoppedValue` 1 line, optional
stopping.
-/

open MeasureTheory ProbabilityTheory Finset

namespace ClassicalLean.Probability.FairGame

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}
  [SigmaFiniteFiltration μ 𝒢]

/-- **No stopping rule beats a fair game.** For a real martingale `f` and a stopping time `τ` with
`τ ≤ N` everywhere, `E[f_τ] = E[f_0]`. -/
theorem integral_stoppedValue_eq {f : ℕ → Ω → ℝ} (hf : Martingale f 𝒢 μ) {τ : Ω → WithTop ℕ}
    (hτ : IsStoppingTime 𝒢 τ) {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    ∫ ω, stoppedValue f τ ω ∂μ = ∫ ω, f 0 ω ∂μ := by
  have h0 := isStoppingTime_const 𝒢 (0 : ℕ)
  have hle : ∀ ω, ((0 : ℕ) : WithTop ℕ) ≤ τ ω := fun ω ↦ by
    cases τ ω with
    | top => exact le_top
    | coe n => exact WithTop.coe_le_coe.mpr (Nat.zero_le n)
  have up := hf.submartingale.expected_stoppedValue_mono h0 hτ (fun ω ↦ hle ω) hbdd
  have dn := hf.neg.submartingale.expected_stoppedValue_mono h0 hτ (fun ω ↦ hle ω) hbdd
  rw [stoppedValue_const] at up dn
  have hneg : stoppedValue (-f) τ = fun ω ↦ -stoppedValue f τ ω := by
    funext ω; simp [stoppedValue]
  rw [hneg, integral_neg] at dn
  have h2 : ∫ ω, (-f) 0 ω ∂μ = -∫ ω, f 0 ω ∂μ := by
    simp only [Pi.neg_apply]; exact integral_neg _
  rw [h2] at dn
  linarith

omit [SigmaFiniteFiltration μ 𝒢] in
/-- **Wald's identity for a bounded stopping time.** On a finite measure, let `S` be adapted and
integrable with `S 0 = 0`, and let every step `S (n + 1) − S n` have conditional mean `m` given
the past `𝒢 n`. For a stopping time `τ ≤ N`, `E[S τ] = m E[τ]`. -/
theorem integral_stoppedValue_eq_mul [IsFiniteMeasure μ] {S : ℕ → Ω → ℝ} {m : ℝ}
    (hadp : StronglyAdapted 𝒢 S) (hint : ∀ n, Integrable (S n) μ) (h0 : ∀ ω, S 0 ω = 0)
    (hstep : ∀ n, μ[S (n + 1) - S n | 𝒢 n] =ᵐ[μ] fun _ ↦ m) {τ : Ω → WithTop ℕ}
    (hτ : IsStoppingTime 𝒢 τ) {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    ∫ ω, stoppedValue S τ ω ∂μ = m * ∫ ω, ((τ ω).untopA : ℝ) ∂μ := by
  let D : ℕ → Ω → ℝ := fun n _ ↦ n * m
  have hD : ∀ n, Integrable (D n) μ := fun n ↦ integrable_const _
  have hmart : Martingale (S - D) 𝒢 μ := by
    refine martingale_of_condExp_sub_eq_zero_nat
      (fun n ↦ (hadp n).sub stronglyMeasurable_const) (fun n ↦ (hint n).sub (hD n)) fun n ↦ ?_
    have e : (S - D) (n + 1) - (S - D) n = (S (n + 1) - S n) - fun _ ↦ m := by
      funext ω; simp only [Pi.sub_apply, D]; push_cast; ring
    rw [e]
    filter_upwards [condExp_sub ((hint _).sub (hint _)) (integrable_const m) (𝒢 n), hstep n]
      with ω h1 h2
    rw [h1, condExp_const (𝒢.le n), Pi.sub_apply, h2, sub_self]
    rfl
  have h := ClassicalLean.Probability.FairGame.integral_stoppedValue_eq hmart hτ hbdd
  have hsplit : stoppedValue (S - D) τ = fun ω ↦ stoppedValue S τ ω - stoppedValue D τ ω := rfl
  rw [hsplit, integral_sub (integrable_stoppedValue ℕ hτ hint hbdd)
    (integrable_stoppedValue ℕ hτ hD hbdd)] at h
  have hS0 : ∫ ω, (S - D) 0 ω ∂μ = 0 := by simp [D, h0]
  rw [hS0, sub_eq_zero] at h
  rw [h, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by
    simp only [stoppedValue, D]; ring)

omit [SigmaFiniteFiltration μ 𝒢] in
/-- **Wald's identity, independent steps.** On a probability space, let each step `X n` be known
by time `n + 1`, integrable with mean `m`, and independent of the past `𝒢 n`. For a stopping time
`τ ≤ N`, the sum of the first `τ` steps has mean `m E[τ]`. -/
theorem integral_stoppedValue_sum_eq [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {m : ℝ}
    (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n)) (hint : ∀ n, Integrable (X n) μ)
    (hmean : ∀ n, ∫ ω, X n ω ∂μ = m)
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime 𝒢 τ) {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    ∫ ω, stoppedValue (fun n ω ↦ ∑ i ∈ range n, X i ω) τ ω ∂μ =
      m * ∫ ω, ((τ ω).untopA : ℝ) ∂μ := by
  refine integral_stoppedValue_eq_mul (fun n ↦ ?_) (fun n ↦ integrable_finsetSum _ fun i _ ↦ hint i)
    (fun ω ↦ by simp) (fun n ↦ ?_) hτ hbdd
  · exact Finset.stronglyMeasurable_fun_sum _ fun i hi ↦
      (hX i).mono (𝒢.mono (Nat.succ_le_of_lt (mem_range.mp hi)))
  · have e : (fun ω ↦ ∑ i ∈ range (n + 1), X i ω) - (fun ω ↦ ∑ i ∈ range n, X i ω) = X n := by
      funext ω; simp [sum_range_succ]
    rw [e]
    have hXm : Measurable (X n) := (hX n).measurable.mono (𝒢.le (n + 1)) le_rfl
    have := condExp_indep_eq hXm.comap_le (𝒢.le n)
      (comap_measurable (X n)).stronglyMeasurable (hind n)
    rwa [hmean n] at this

end ClassicalLean.Probability.FairGame
