/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.Moments.Covariance

/-!
# The autocovariance of a moving average

A moving average of order `q` built from noise `e`:
`X t = θ₀ e (t + q) + θ₁ e (t + q − 1) + ⋯ + θ_q e t` (`movingAverage`), where the noise is white:
`cov(e s, e t)` is `v` when `s = t` and `0` otherwise. (The indices run forward from `t` so that no
subtraction in `ℕ` is cut off at `0`; it is the usual `X t = ∑ⱼ θⱼ e (t − j)` shifted by `q`.)

* `covariance_movingAverage` — `cov(X (t + k), X t) = v · ∑_{j < q + 1 − k} θⱼ θ_{j+k}`, the same
  for every `t`: the autocovariance depends only on the lag `k`. (The means are not constrained,
  so this alone does not make the process stationary.)
* `covariance_movingAverage_eq_zero_of_lt` — the autocovariance is `0` beyond lag `q`.

This is the standard formula (with `θ₀ = 1` it is found in time-series textbooks, for example
Brockwell and Davis's; no theorem number is cited, none was checked).

## Hypotheses

Measured in order LEAN-20's checks (check C26, exact rationals): 200 cases with `q` from `0` to
`4`, random `θ`, `v`, `t` and `k`. Each hypothesis fails when dropped alone (the first two cases
computed in the checks, the third worked by hand in review r26):

* white noise: with `q = 0`, `θ₀ = 1` and `e t = Z t + Z (t + 1)` for uncorrelated `Z` of variance
  `1`, `cov(X 1, X 0) = 1`, but the formula gives `0`.
* `q < k`, for the zero: at `k = q = 1`, `θ = (1, 1)`, `v = 1` the autocovariance is `1`.
* the noise square-integrable: on `ℕ` with `μ {n} = 2^(−n−1)`, let `Y n = 2ⁿ`, `W n = (−1)ⁿ`,
  `e 0 = −Y`, `e 1 = Y + W`, `e t = 0` after; `q = 1`, `θ = (1, 1)`, `v = 0`. None of the products
  is integrable, so Lean's covariances of the noise are all `0` and the white-noise hypothesis
  holds with `v = 0`; but `X 0 = e 1 + e 0 = W` has variance `8/9`, not `0`.

The finite measure is assumed because Mathlib's covariance algebra assumes it; not tested.

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-20, `grep -rniE` over Mathlib):
`moving.?average` 0; `autocovarian` 0. Used: Mathlib's covariance of finite sums
(`covariance_fun_sum_fun_sum'`).
-/

open MeasureTheory ProbabilityTheory Finset

namespace ClassicalLean.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- A moving average of order `q` with weights `θ₀, …, θ_q` of the noise `e`:
`X t = ∑_{j ≤ q} θⱼ e (t + q − j)`. -/
noncomputable def movingAverage (q : ℕ) (θ : ℕ → ℝ) (e : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ range (q + 1), θ j * e (t + q - j) ω

variable [IsFiniteMeasure μ]

/-- **The autocovariance of a moving average.** For white noise of variance `v` (square-integrable,
`cov(e s, e t) = v` if `s = t` and `0` otherwise), `cov(X (t + k), X t) = v · ∑_{j < q + 1 − k}
θⱼ θ_{j+k}` for every `t` and `k`. Expand both sums; a pair of noise terms is correlated only when
it is the same term, which happens for the weights `θ_{j+k}` and `θⱼ`. -/
theorem covariance_movingAverage {q : ℕ} {θ : ℕ → ℝ} {e : ℕ → Ω → ℝ} {v : ℝ}
    (he : ∀ t, MemLp (e t) 2 μ) (hcov : ∀ s t, cov[e s, e t; μ] = if s = t then v else 0)
    (t k : ℕ) :
    cov[movingAverage q θ e (t + k), movingAverage q θ e t; μ]
      = v * ∑ j ∈ range (q + 1 - k), θ j * θ (j + k) := by
  have hterm : ∀ s j, MemLp (fun ω ↦ θ j * e (s + q - j) ω) 2 μ := fun s j ↦ (he _).const_mul _
  unfold movingAverage
  rw [covariance_fun_sum_fun_sum' (X := fun j ω ↦ θ j * e (t + k + q - j) ω)
    (Y := fun l ω ↦ θ l * e (t + q - l) ω) (fun j _ ↦ hterm _ j) (fun l _ ↦ hterm _ l)]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right, hcov]
  rw [Finset.sum_comm]
  have hinner : ∀ l ∈ range (q + 1),
      ∑ j ∈ range (q + 1), θ j * (θ l * if t + k + q - j = t + q - l then v else 0)
        = if l + k ∈ range (q + 1) then θ (l + k) * (θ l * v) else 0 := by
    intro l hl
    rw [← Finset.sum_ite_eq' (range (q + 1)) (l + k) fun j ↦ θ j * (θ l * v)]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hl' := Finset.mem_range.mp hl
    have hj' := Finset.mem_range.mp hj
    split_ifs with h1 h2 h2
    · rfl
    · omega
    · omega
    · simp
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter, Finset.mul_sum]
  have hfilter : (range (q + 1)).filter (fun l ↦ l + k ∈ range (q + 1)) = range (q + 1 - k) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilter]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  ring

/-- **A moving average of order `q` is uncorrelated beyond lag `q`.** Under the hypotheses of
`covariance_movingAverage`, `cov(X (t + k), X t) = 0` for `k > q`: the sum is empty. -/
theorem covariance_movingAverage_eq_zero_of_lt {q : ℕ} {θ : ℕ → ℝ} {e : ℕ → Ω → ℝ} {v : ℝ}
    (he : ∀ t, MemLp (e t) 2 μ) (hcov : ∀ s t, cov[e s, e t; μ] = if s = t then v else 0)
    (t : ℕ) {k : ℕ} (hk : q < k) :
    cov[movingAverage q θ e (t + k), movingAverage q θ e t; μ] = 0 := by
  rw [covariance_movingAverage he hcov, Nat.sub_eq_zero_of_le (by omega), Finset.range_zero,
    Finset.sum_empty, mul_zero]

end ClassicalLean.Probability
