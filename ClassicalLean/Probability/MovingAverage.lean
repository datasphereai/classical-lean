/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.Moments.Covariance
import ClassicalLean.Probability.EffectiveSampleSize

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
* `sum_covariance_mul_cexp_eq` — order LEAN-31, item 101 of MATH-PLAN-library-2: **the spectral
  density, finite form**: `∑_{|k| ≤ q} γ (|k|) e^(−i k φ) = v |∑ⱼ θⱼ e^(i j φ)|²` at every
  frequency `φ`, with `γ (|k|)` the autocovariance at lag `|k|`. The right side is
  `v · (∑ⱼ θⱼ e^(i j φ)) · (∑ₗ θₗ e^(−i l φ))`; its double sum, grouped by the lag `l − j`, is the
  left side.
* `zero_le_sum_covariance_mul_cos` — the same item: **so it is never negative**, in real form,
  `∑_{|k| ≤ q} γ (|k|) cos (k φ) ≥ 0`, the real part of the identity; `v = cov(e 0, e 0) ≥ 0`, so
  no sign of `v` is assumed.
* `variance_sum_movingAverage` — item 115 of MATH-PLAN-library-2 (order LEAN-35): **the long-run
  variance of a moving average.** For white noise of variance `v` and `n > q`,
  `Var(X 0 + ⋯ + X (n − 1)) = n v (∑ θ)² − 2 ∑_{k ≤ q} k γ(k)` with `γ(k) = cov(X k, X 0)`, so
  `n · Var(mean) → v (∑ θ)²`; through `EffectiveSampleSize`'s variance of a sum of
  covariance-stationary terms, which this module now imports. The proof is the draft `d115-r2-s1`
  (written by Claude Opus 5.5 through the Anthropic Batch API, the lane's API-CREDIT-1 work),
  adapted by order LEAN-35's session: inside this namespace, the theorem's own
  `[IsFiniteMeasure μ]` left to this module's `variable` line, `open Filter Topology in` on the
  theorem in place of the draft's file-level `open`, its docstring rewritten (the item, the credit,
  the hypotheses in words), a `show` that changed the goal written as `change`, and a `ring` that
  never ran removed. Its hypotheses were not drop-tested by this order (the section below has no
  line for it). Its witness is at the end of the file.

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

The finite measure is assumed because Mathlib's covariance algebra assumes it; not tested (the
same for both item 101 theorems).

Item 101 (order LEAN-31's exact checks, lane `lean/LEAN-31-checks.py`, exact fractions; checks
`101.identity`, 200 random cases, `101.model`, 60 cases of Walsh white noise, and `101.nonneg`,
200 cases with `v ≥ 0`). With any one hypothesis dropped, each theorem fails:

* white noise, for both (`101.drop.hcov`): `e t = Z t + Z (t + 1)` for the Walsh noise `Z`,
  correlated at lag `1`, `q = 1`, `θ = (1, 1)`: `γ 0 = 6`, `γ 1 = 4`, so at `φ = π` the real sum is
  `6 − 8 = −2 < 0`, and no `v` matches (`6 = 2 v` and `4 = v`).
* the noise square-integrable, for the identity (by hand): the case above (`q = 1`,
  `θ = (1, 1)`, `v = 0`), at `t = 0`: the left side is `8/9` at every `φ`, the right side `0`
  (at `t ≥ 1` both sides are `0`). It does not break the corollary, as `0 ≤ 8/9`.
* the noise square-integrable, for the corollary (by hand; the line `101 (he, corollary)` of the
  checks): `W` a fair sign and `Y` independent of it with `P(Y = 2ⁿ) = 2⁻ⁿ`, not integrable;
  `e 0 = Y`, `e 1 = W − Y`, `e 2 = 9 W + Y`, `e t = Y` after. Every noise and every product of two
  has a part in `Y` or `Y²` that is not integrable, so every noise mean and covariance is Lean's
  `0` and white noise holds with `v = 0`; with `q = 1`, `θ = (1, 1)`, `t = 0`: `X 0 = W`,
  `X 1 = 10 W`, and the real sum at `φ = π` is `1 + 20 cos π = −19 < 0`.

Junk value in both square-integrability cases: the integral of a function that is not integrable
is `0` (in the corollary's, twice: the means and the covariances).

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-20, `grep -rniE` over Mathlib):
`moving.?average` 0; `autocovarian` 0. Used: Mathlib's covariance of finite sums
(`covariance_fun_sum_fun_sum'`). Order LEAN-31: the plan's search `spectral density|spectralDensity`
(`MATH-PLAN-library-2-checks.py`, line `row.L9`), before item 101 was written, found 0 lines in
pinned Mathlib, in Mathlib master at `2da3ab0a` and in the library. Used for item 101:
`Complex.mul_conj`, `Complex.exp_conj`, `Finset.sum_fiberwise_of_maps_to`, `Finset.sum_nbij'`.
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

/-- Regrouping a double sum over `j, l < q + 1` by the lag `l − j ∈ [−q, q]`: the lag `k` collects
the products `θ a θ (a + |k|)` for `a < q + 1 − |k|`. -/
private lemma sum_Icc_mul_cexp_eq_sum_sum (q : ℕ) (θ : ℕ → ℝ) (φ : ℝ) :
    ∑ k ∈ Icc (-(q : ℤ)) q,
        ((∑ a ∈ range (q + 1 - k.natAbs), θ a * θ (a + k.natAbs) : ℝ) : ℂ) *
          Complex.exp (-((k : ℂ) * φ * Complex.I))
      = ∑ j ∈ range (q + 1), ∑ l ∈ range (q + 1),
          (θ j : ℂ) * θ l * Complex.exp (((j : ℂ) - l) * φ * Complex.I) := by
  classical
  rw [← Finset.sum_product (f := fun p : ℕ × ℕ ↦
    (θ p.1 : ℂ) * θ p.2 * Complex.exp (((p.1 : ℂ) - p.2) * φ * Complex.I))]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ ↦ (p.2 : ℤ) - p.1)
    (t := Icc (-(q : ℤ)) q) (fun p hp ↦ by
      simp only [Finset.mem_product, Finset.mem_range] at hp
      simp only [Finset.mem_Icc]
      omega)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hexp : ∀ p ∈ (range (q + 1) ×ˢ range (q + 1)).filter (fun p : ℕ × ℕ ↦ (p.2 : ℤ) - p.1 = k),
      (θ p.1 : ℂ) * θ p.2 * Complex.exp (((p.1 : ℂ) - p.2) * φ * Complex.I)
        = (θ p.1 : ℂ) * θ p.2 * Complex.exp (-((k : ℂ) * φ * Complex.I)) := fun p hp ↦ by
    have hk : (p.2 : ℤ) - p.1 = k := (Finset.mem_filter.mp hp).2
    have hkc : (k : ℂ) = (p.2 : ℂ) - p.1 := by
      rw [← hk]
      push_cast
      ring
    rw [hkc]
    congr 2
    ring
  rw [Finset.sum_congr rfl hexp, ← Finset.sum_mul]
  congr 1
  push_cast
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [Int.natAbs_natCast]
    refine Finset.sum_nbij' (fun a ↦ (a, a + n)) (fun p ↦ p.1) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ha ⊢
      omega
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
      omega
    · intro a _
      rfl
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      exact Prod.ext rfl (by simp only; omega)
    · intro a _
      rfl
  · rw [Int.natAbs_neg, Int.natAbs_natCast]
    refine Finset.sum_nbij' (fun a ↦ (a + n, a)) (fun p ↦ p.2) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ha ⊢
      omega
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
      omega
    · intro a _
      rfl
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      exact Prod.ext (by simp only; omega) rfl
    · intro a _
      simp only
      ring

/-- **The spectral density of a moving average, finite form** (order LEAN-31, item 101 of
MATH-PLAN-library-2). For white noise of variance `v`, the autocovariances `γ k` of the moving
average satisfy `∑_{|k| ≤ q} γ (|k|) e^(−i k φ) = v |∑ⱼ θⱼ e^(i j φ)|²` at every frequency `φ`
(with `γ (|k|)` written `cov[X (t + |k|), X t]`, the same for every `t`). -/
theorem sum_covariance_mul_cexp_eq {q : ℕ} {θ : ℕ → ℝ} {e : ℕ → Ω → ℝ} {v : ℝ}
    (he : ∀ t, MemLp (e t) 2 μ) (hcov : ∀ s t, cov[e s, e t; μ] = if s = t then v else 0)
    (t : ℕ) (φ : ℝ) :
    ∑ k ∈ Icc (-(q : ℤ)) q,
        (cov[movingAverage q θ e (t + k.natAbs), movingAverage q θ e t; μ] : ℂ) *
          Complex.exp (-((k : ℂ) * φ * Complex.I))
      = v * Complex.normSq
          (∑ j ∈ range (q + 1), (θ j : ℂ) * Complex.exp ((j : ℂ) * φ * Complex.I)) := by
  simp_rw [covariance_movingAverage he hcov, Complex.ofReal_mul, mul_assoc (v : ℂ),
    ← Finset.mul_sum]
  rw [sum_Icc_mul_cexp_eq_sum_sum, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_natCast,
    Complex.conj_I]
  rw [show ((j : ℂ) - l) * φ * Complex.I = j * φ * Complex.I + l * φ * (-Complex.I) by ring,
    Complex.exp_add]
  ring

/-- **The spectral density of a moving average is never negative** (order LEAN-31, item 101 of
MATH-PLAN-library-2, the plan's "so it is never negative", in real form): for white noise,
`∑_{|k| ≤ q} γ (|k|) cos (k φ) ≥ 0` at every frequency `φ`. It is the real part of
`sum_covariance_mul_cexp_eq`, and `v = cov[e 0, e 0] ≥ 0`, so no `0 ≤ v` is assumed. -/
theorem zero_le_sum_covariance_mul_cos {q : ℕ} {θ : ℕ → ℝ} {e : ℕ → Ω → ℝ} {v : ℝ}
    (he : ∀ t, MemLp (e t) 2 μ) (hcov : ∀ s t, cov[e s, e t; μ] = if s = t then v else 0)
    (t : ℕ) (φ : ℝ) :
    0 ≤ ∑ k ∈ Icc (-(q : ℤ)) q,
      cov[movingAverage q θ e (t + k.natAbs), movingAverage q θ e t; μ] * Real.cos (k * φ) := by
  have hv : 0 ≤ v := by
    have h : cov[e 0, e 0; μ] = v := by simpa using hcov 0 0
    rw [← h]
    unfold covariance
    exact integral_nonneg fun ω ↦ mul_self_nonneg _
  have h := congrArg Complex.re (sum_covariance_mul_cexp_eq (q := q) (θ := θ) he hcov t φ)
  rw [Complex.re_sum] at h
  have hl : ∀ k ∈ Icc (-(q : ℤ)) q,
      ((cov[movingAverage q θ e (t + k.natAbs), movingAverage q θ e t; μ] : ℂ) *
          Complex.exp (-((k : ℂ) * φ * Complex.I))).re =
        cov[movingAverage q θ e (t + k.natAbs), movingAverage q θ e t; μ] * Real.cos (k * φ) :=
    fun k _ ↦ by
      rw [Complex.re_ofReal_mul,
        show -((k : ℂ) * φ * Complex.I) = ((-(k * φ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  rw [Finset.sum_congr rfl hl, ← Complex.ofReal_mul, Complex.ofReal_re] at h
  rw [h]
  exact mul_nonneg hv (Complex.normSq_nonneg _)

/-- The autocovariance at lag `k` of a moving average of order `q`, weights `θ`, noise variance
`v`. -/
private noncomputable def maCov (q : ℕ) (θ : ℕ → ℝ) (v : ℝ) (k : ℕ) : ℝ :=
  v * ∑ j ∈ range (q + 1 - k), θ j * θ (j + k)

/-- The square of a sum, grouped by lag:
`(∑_{j<m} θⱼ)² = 2 ∑_{k<m} ∑_{j<m−k} θⱼ θ_{j+k} − ∑_{j<m} θⱼ²`. -/
private lemma sq_sum_eq (θ : ℕ → ℝ) (m : ℕ) :
    (∑ j ∈ range m, θ j) ^ 2 =
      2 * ∑ k ∈ range m, ∑ j ∈ range (m - k), θ j * θ (j + k) - ∑ j ∈ range m, θ j * θ j := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hc : ∀ k ∈ range (m + 1), ∑ j ∈ range (m + 1 - k), θ j * θ (j + k) =
        ∑ j ∈ range (m - k), θ j * θ (j + k) + θ (m - k) * θ m := by
      intro k hk
      have hk' := mem_range.mp hk
      rw [show m + 1 - k = m - k + 1 by omega, sum_range_succ, show m - k + k = m by omega]
    have hrefl : ∑ k ∈ range (m + 1), θ (m - k) = ∑ k ∈ range (m + 1), θ k := by
      have := sum_range_reflect θ (m + 1)
      simpa only [Nat.add_sub_cancel] using this
    have h3 : ∑ k ∈ range (m + 1), ∑ j ∈ range (m + 1 - k), θ j * θ (j + k) =
        ∑ k ∈ range m, ∑ j ∈ range (m - k), θ j * θ (j + k) +
          (∑ j ∈ range (m + 1), θ j) * θ m := by
      rw [sum_congr rfl hc, sum_add_distrib,
        sum_range_succ (fun k ↦ ∑ j ∈ range (m - k), θ j * θ (j + k)) m, Nat.sub_self,
        range_zero, sum_empty, add_zero, ← sum_mul, hrefl]
    have h1 : ∑ j ∈ range (m + 1), θ j = ∑ j ∈ range m, θ j + θ m := sum_range_succ _ _
    have h2 : ∑ j ∈ range (m + 1), θ j * θ j = ∑ j ∈ range m, θ j * θ j + θ m * θ m :=
      sum_range_succ _ _
    rw [h3, h2, h1]
    linear_combination ih

open Filter Topology in
/-- **The long-run variance of a moving average** (item 115 of MATH-PLAN-library-2; the draft
`d115-r2-s1`, written by Claude Opus 5.5 through the Anthropic Batch API, the lane's API-CREDIT-1
work, adapted by order LEAN-35's session). For white noise of variance `v` (each `e t`
square-integrable, `cov(e s, e t) = v` if `s = t` and `0` otherwise) under a finite measure `μ`,
and the moving average `X = movingAverage q θ e` of order `q` with weights `θ`, for every `n > q`,
`Var(X 0 + ⋯ + X (n − 1)) = n v (∑_{j ≤ q} θ j)² − 2 ∑_{k ≤ q} k γ(k)` with
`γ(k) = cov(X k, X 0)`, the autocovariance at lag `k` (`covariance_movingAverage`); and
consequently `n · Var(mean of X 0, …, X (n − 1)) → v (∑_{j ≤ q} θ j)²`. The proof uses
`EffectiveSampleSize`'s variance of a sum of covariance-stationary terms. -/
theorem variance_sum_movingAverage {q : ℕ} {θ : ℕ → ℝ}
    {e : ℕ → Ω → ℝ} {v : ℝ}
    (he : ∀ t, MemLp (e t) 2 μ) (hcov : ∀ s t, cov[e s, e t; μ] = if s = t then v else 0) :
    (∀ n : ℕ, q < n →
      Var[fun ω ↦ ∑ t ∈ range n, movingAverage q θ e t ω; μ] =
        n * v * (∑ j ∈ range (q + 1), θ j) ^ 2 -
          2 * ∑ k ∈ range (q + 1),
            (k : ℝ) * cov[movingAverage q θ e k, movingAverage q θ e 0; μ]) ∧
    Tendsto (fun n : ℕ ↦
        (n : ℝ) * Var[fun ω ↦ (∑ t ∈ range n, movingAverage q θ e t ω) / (n : ℝ); μ])
      atTop (𝓝 (v * (∑ j ∈ range (q + 1), θ j) ^ 2)) := by
  have hγ : ∀ k : ℕ, cov[movingAverage q θ e k, movingAverage q θ e 0; μ] = maCov q θ v k := by
    intro k
    rw [maCov]
    simpa only [zero_add] using covariance_movingAverage (θ := θ) he hcov 0 k
  have hmain : ∀ n : ℕ, q < n →
      Var[fun ω ↦ ∑ t ∈ range n, movingAverage q θ e t ω; μ] =
        n * v * (∑ j ∈ range (q + 1), θ j) ^ 2 -
          2 * ∑ k ∈ range (q + 1),
            (k : ℝ) * cov[movingAverage q θ e k, movingAverage q θ e 0; μ] := by
    intro n hn
    have hX : ∀ i < n, MemLp (movingAverage q θ e i) 2 μ := fun i _ ↦ by
      change MemLp (fun ω ↦ ∑ j ∈ range (q + 1), θ j * e (i + q - j) ω) 2 μ
      exact memLp_finsetSum (range (q + 1)) (f := fun j ω ↦ θ j * e (i + q - j) ω)
        fun j _ ↦ (he _).const_mul _
    have hcovX : ∀ i < n, ∀ j < n, cov[movingAverage q θ e i, movingAverage q θ e j; μ] =
        maCov q θ v (max i j - min i j) := by
      intro i _ j _
      rcases le_total i j with h | h
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
        rw [maCov, max_eq_right h, min_eq_left h, Nat.add_sub_cancel_left, covariance_comm,
          covariance_movingAverage he hcov]
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
        rw [maCov, max_eq_left h, min_eq_right h, Nat.add_sub_cancel_left,
          covariance_movingAverage he hcov]
    have hV := EffectiveSampleSize.variance_sum_range_eq_of_stationary (μ := μ)
      (X := movingAverage q θ e) (k := n) (γ := maCov q θ v) hX hcovX
    have k1 := EffectiveSampleSize.sum_sum_lag_eq (maCov q θ v) n
    have k2 := EffectiveSampleSize.sum_sum_lag_eq_range (maCov q θ v) n
    have hzero : ∀ k, q + 1 ≤ k → maCov q θ v k = 0 := by
      intro k hk
      rw [maCov, Nat.sub_eq_zero_of_le hk, range_zero, sum_empty, mul_zero]
    have hR : ∑ j ∈ range n, ((n : ℝ) - j) * maCov q θ v j =
        ∑ j ∈ range (q + 1), ((n : ℝ) - j) * maCov q θ v j := by
      symm
      refine sum_subset (fun x hx ↦ ?_) (fun x _ hx' ↦ ?_)
      · rw [mem_range] at hx ⊢
        omega
      · rw [mem_range] at hx'
        rw [hzero x (by omega), mul_zero]
    have hsplit : ∑ j ∈ range (q + 1), ((n : ℝ) - j) * maCov q θ v j =
        (n : ℝ) * ∑ j ∈ range (q + 1), maCov q θ v j -
          ∑ j ∈ range (q + 1), (j : ℝ) * maCov q θ v j := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun j _ ↦ by ring
    have hsq := sq_sum_eq θ (q + 1)
    have hC : ∑ k ∈ range (q + 1), maCov q θ v k =
        v * ∑ k ∈ range (q + 1), ∑ j ∈ range (q + 1 - k), θ j * θ (j + k) := by
      rw [mul_sum]
      rfl
    have hc0 : maCov q θ v 0 = v * ∑ j ∈ range (q + 1), θ j * θ j := by
      rw [maCov]
      simp
    have hW : ∑ k ∈ range (q + 1),
          (k : ℝ) * cov[movingAverage q θ e k, movingAverage q θ e 0; μ] =
        ∑ k ∈ range (q + 1), (k : ℝ) * maCov q θ v k :=
      sum_congr rfl fun k _ ↦ by rw [hγ k]
    linear_combination hV + 2 * hW - k1 + k2 + 2 * hR + 2 * hsplit + 2 * (n : ℝ) * hC
      - (n : ℝ) * v * hsq - (n : ℝ) * hc0
  refine ⟨hmain, ?_⟩
  have hmean : ∀ n : ℕ,
      Var[fun ω ↦ (∑ t ∈ range n, movingAverage q θ e t ω) / (n : ℝ); μ] =
        Var[fun ω ↦ ∑ t ∈ range n, movingAverage q θ e t ω; μ] / (n : ℝ) ^ 2 := by
    intro n
    simp_rw [div_eq_mul_inv]
    rw [variance_mul_const]
    ring
  have hlim : Tendsto (fun n : ℕ ↦ v * (∑ j ∈ range (q + 1), θ j) ^ 2 -
      2 * (∑ k ∈ range (q + 1),
        (k : ℝ) * cov[movingAverage q θ e k, movingAverage q θ e 0; μ]) / (n : ℝ))
      atTop (𝓝 (v * (∑ j ∈ range (q + 1), θ j) ^ 2)) := by
    have := (tendsto_const_nhds (x := v * (∑ j ∈ range (q + 1), θ j) ^ 2)).sub
      (tendsto_const_div_atTop_nhds_zero_nat (2 * (∑ k ∈ range (q + 1),
        (k : ℝ) * cov[movingAverage q θ e k, movingAverage q θ e 0; μ])))
    simpa only [sub_zero] using this
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop q] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [hmean, hmain n hn]
  field_simp

end ClassicalLean.Probability

open MeasureTheory ProbabilityTheory in
open scoped ENNReal in
/-- The hypotheses of `covariance_movingAverage` hold together: the points `n = 0, 1, 2, …` with
chance `2^-(n+1)` (Lean's finite-measure instance comes from conditioning on the whole space, which
changes nothing, as the chances sum to `1`); the noise `e t = √(2^t) · h t`, where `h t n` is `1` at
`n = t`, `-1` for `n > t` and `0` below `t`; each `e t` is bounded, so in `L²`, has mean `0` (the
point `t` and the points above it carry the same chance), variance `v = 1`, and is uncorrelated
with every other (for `s < t`, `h s` is `-1` wherever `h t` is not `0`); `q = 2`, the weights
`θ j = j + 1`, the times `t = 3` and lag `k = 1`. -/
example := ClassicalLean.Probability.covariance_movingAverage
  (μ := (Measure.sum fun n : ℕ ↦ ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) • Measure.dirac n)[|Set.univ])
  (q := 2) (θ := fun j ↦ (j : ℝ) + 1)
  (e := fun t n ↦ Real.sqrt (2 ^ t) * if n = t then 1 else if t < n then -1 else 0) (v := 1)
  (fun t ↦ MemLp.of_bound (measurable_of_countable _).aestronglyMeasurable (Real.sqrt (2 ^ t))
    (ae_of_all _ fun n ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (by split_ifs <;> norm_num)))
  (by
    obtain ⟨M, hM⟩ : ∃ M : Measure ℕ,
        M = Measure.sum fun n : ℕ ↦ ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) • Measure.dirac n := ⟨_, rfl⟩
    obtain ⟨h, hh⟩ : ∃ h : ℕ → ℕ → ℝ,
        h = fun t n ↦ if n = t then 1 else if t < n then -1 else 0 := ⟨_, rfl⟩
    have M_single : ∀ m : ℕ, M {m} = (2⁻¹ : ℝ≥0∞) ^ (m + 1) := by
      intro m
      rw [hM, Measure.sum_apply _ (measurableSet_singleton m)]
      simp only [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton m),
        smul_eq_mul]
      rw [tsum_eq_single m]
      · simp
      · intro n hn; simp [Set.indicator, hn]
    have cond_eq : M[|Set.univ] = M := by
      have M_univ : M Set.univ = 1 := by
        rw [hM, Measure.sum_apply _ MeasurableSet.univ]
        simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, pow_succ]
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
          ENNReal.mul_inv_cancel (by simp) (by simp)]
      rw [ProbabilityTheory.cond, Measure.restrict_univ, M_univ, inv_one, one_smul]
    have integral_eq : ∀ f : ℕ → ℝ, Integrable f M →
        ∫ n, f n ∂M = ∑' n, ((2 : ℝ)⁻¹) ^ (n + 1) * f n := by
      intro f hf
      rw [integral_countable hf]
      congr 1; ext n
      rw [measureReal_def, M_single]; simp
    have bdd : ∀ (f : ℕ → ℝ) (C : ℝ), (∀ n, |f n| ≤ C) → Integrable f M := by
      intro f C hC
      rw [← cond_eq]
      exact Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable C
        (ae_of_all _ fun n ↦ by simpa using hC n)
    have summ_tail : ∀ t : ℕ, Summable fun n : ℕ ↦ if t + 1 ≤ n then (2 : ℝ)⁻¹ ^ n else 0 :=
      fun t ↦ (summable_geometric_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
        ).of_nonneg_of_le
        (fun n ↦ by split_ifs <;> positivity)
        (fun n ↦ by split_ifs <;> first | exact le_rfl | positivity)
    have sum_h : ∀ t : ℕ, ∑' n, (2 : ℝ)⁻¹ ^ (n + 1) * h t n = 0 := by
      intro t
      have r : ∀ n, (2 : ℝ)⁻¹ ^ (n + 1) * h t n = (if n = t then (2 : ℝ)⁻¹ ^ (t + 1) else 0) -
          2⁻¹ * (if t + 1 ≤ n then (2 : ℝ)⁻¹ ^ n else 0) := by
        intro n; rw [hh]; dsimp only
        split_ifs <;> subst_vars <;> first | (exfalso; omega) | ring1
      simp_rw [r]
      rw [Summable.tsum_sub (hasSum_ite_eq t _).summable ((summ_tail t).mul_left _), tsum_ite_eq,
        tsum_mul_left, tsum_geometric_inv_two_ge]
      ring
    have sum_h_sq : ∀ t : ℕ, ∑' n, (2 : ℝ)⁻¹ ^ (n + 1) * (h t n * h t n) = (2 : ℝ)⁻¹ ^ t := by
      intro t
      have r : ∀ n, (2 : ℝ)⁻¹ ^ (n + 1) * (h t n * h t n) =
          (if n = t then (2 : ℝ)⁻¹ ^ (t + 1) else 0) +
            2⁻¹ * (if t + 1 ≤ n then (2 : ℝ)⁻¹ ^ n else 0) := by
        intro n; rw [hh]; dsimp only
        split_ifs <;> subst_vars <;> first | (exfalso; omega) | ring1
      simp_rw [r]
      rw [Summable.tsum_add (hasSum_ite_eq t _).summable ((summ_tail t).mul_left _), tsum_ite_eq,
        tsum_mul_left, tsum_geometric_inv_two_ge]
      ring
    have h_mul_lt : ∀ {s t : ℕ}, s < t → ∀ n, h s n * h t n = - h t n := by
      intro s t hst n; rw [hh]; dsimp only
      split_ifs <;> first | (exfalso; omega) | norm_num
    have h_abs : ∀ t n, |h t n| ≤ 1 := by
      intro t n; rw [hh]; dsimp only; split_ifs <;> norm_num
    have key : ∀ s t, cov[fun n ↦ Real.sqrt (2 ^ s) * h s n, fun n ↦ Real.sqrt (2 ^ t) * h t n;
        M[|Set.univ]] = if s = t then 1 else 0 := by
      intro s t
      have mean : ∀ t, ∫ n, Real.sqrt (2 ^ t) * h t n ∂M = 0 := by
        intro t
        rw [integral_eq _ (bdd _ (Real.sqrt (2 ^ t)) fun n ↦ by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (h_abs t n))]
        simp_rw [mul_left_comm _ (Real.sqrt _)]
        rw [tsum_mul_left, sum_h, mul_zero]
      rw [covariance, cond_eq]
      rw [mean, mean]
      simp only [sub_zero]
      rw [integral_eq _ (bdd _ (Real.sqrt (2 ^ s) * Real.sqrt (2 ^ t)) fun n ↦ by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
          abs_of_nonneg (Real.sqrt_nonneg _)]
        have := h_abs s n; have := h_abs t n
        have := Real.sqrt_nonneg (2 ^ s); have := Real.sqrt_nonneg (2 ^ t)
        calc _ = Real.sqrt (2 ^ s) * Real.sqrt (2 ^ t) * (|h s n| * |h t n|) := by ring
          _ ≤ Real.sqrt (2 ^ s) * Real.sqrt (2 ^ t) * (1 * 1) := by gcongr
          _ = _ := by ring)]
      have r : ∀ n,
          (2 : ℝ)⁻¹ ^ (n + 1) * (Real.sqrt (2 ^ s) * h s n * (Real.sqrt (2 ^ t) * h t n)) =
          Real.sqrt (2 ^ s) * Real.sqrt (2 ^ t) * ((2 : ℝ)⁻¹ ^ (n + 1) * (h s n * h t n)) := by
        intro n; ring
      simp_rw [r]
      rw [tsum_mul_left]
      rcases lt_trichotomy s t with hst | rfl | hst
      · simp_rw [h_mul_lt hst, mul_neg]
        rw [tsum_neg, sum_h, neg_zero, mul_zero]
        simp [hst.ne]
      · rw [sum_h_sq, ← Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by positivity),
          ← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow]
        simp
      · simp_rw [mul_comm (h s _), h_mul_lt hst, mul_neg]
        rw [tsum_neg, sum_h, neg_zero, mul_zero]
        simp [hst.ne']
    subst hM hh
    exact key)
  (t := 3) (k := 1)

open MeasureTheory ProbabilityTheory in
open scoped ENNReal in
/-- The hypotheses of `sum_covariance_mul_cexp_eq` hold together: the points `n = 0, 1, 2, …` with
chance `2^-(n+1)` (Lean's finite-measure instance comes from conditioning on the whole space, which
changes nothing, as the chances sum to `1`); the noise `e t = √(2^t) · h t`, where `h t n` is `1` at
`n = t`, `-1` for `n > t` and `0` below `t`; each `e t` is bounded, so in `L²`, has mean `0`,
variance `v = 1`, and is uncorrelated with every other; `q = 2`, the weights `θ j = j + 1`, the
time `t = 3` and the frequency `φ = 1` (the same model as `covariance_movingAverage`'s witness). -/
example := ClassicalLean.Probability.sum_covariance_mul_cexp_eq
  (μ := (Measure.sum fun n : ℕ ↦ ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) • Measure.dirac n)[|Set.univ])
  (q := 2) (θ := fun j ↦ (j : ℝ) + 1)
  (e := fun t n ↦ Real.sqrt (2 ^ t) * if n = t then 1 else if t < n then -1 else 0) (v := 1)
  (fun t ↦ MemLp.of_bound (measurable_of_countable _).aestronglyMeasurable (Real.sqrt (2 ^ t))
    (ae_of_all _ fun n ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (by split_ifs <;> norm_num)))
  (by
    obtain ⟨M, hM⟩ : ∃ M : Measure ℕ,
        M = Measure.sum fun n : ℕ ↦ ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) • Measure.dirac n := ⟨_, rfl⟩
    obtain ⟨h, hh⟩ : ∃ h : ℕ → ℕ → ℝ,
        h = fun t n ↦ if n = t then 1 else if t < n then -1 else 0 := ⟨_, rfl⟩
    have M_single : ∀ m : ℕ, M {m} = (2⁻¹ : ℝ≥0∞) ^ (m + 1) := by
      intro m
      rw [hM, Measure.sum_apply _ (measurableSet_singleton m)]
      simp only [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton m),
        smul_eq_mul]
      rw [tsum_eq_single m]
      · simp
      · intro n hn; simp [Set.indicator, hn]
    have cond_eq : M[|Set.univ] = M := by
      have M_univ : M Set.univ = 1 := by
        rw [hM, Measure.sum_apply _ MeasurableSet.univ]
        simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, pow_succ]
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
          ENNReal.mul_inv_cancel (by simp) (by simp)]
      rw [ProbabilityTheory.cond, Measure.restrict_univ, M_univ, inv_one, one_smul]
    have integral_eq : ∀ f : ℕ → ℝ, Integrable f M →
        ∫ n, f n ∂M = ∑' n, ((2 : ℝ)⁻¹) ^ (n + 1) * f n := by
      intro f hf
      rw [integral_countable hf]
      congr 1; ext n
      rw [measureReal_def, M_single]; simp
    have bdd : ∀ (f : ℕ → ℝ) (C : ℝ), (∀ n, |f n| ≤ C) → Integrable f M := by
      intro f C hC
      rw [← cond_eq]
      exact Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable C
        (ae_of_all _ fun n ↦ by simpa using hC n)
    have summ_tail : ∀ t : ℕ, Summable fun n : ℕ ↦ if t + 1 ≤ n then (2 : ℝ)⁻¹ ^ n else 0 :=
      fun t ↦ (summable_geometric_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
        ).of_nonneg_of_le
        (fun n ↦ by split_ifs <;> positivity)
        (fun n ↦ by split_ifs <;> first | exact le_rfl | positivity)
    have sum_h : ∀ t : ℕ, ∑' n, (2 : ℝ)⁻¹ ^ (n + 1) * h t n = 0 := by
      intro t
      have r : ∀ n, (2 : ℝ)⁻¹ ^ (n + 1) * h t n = (if n = t then (2 : ℝ)⁻¹ ^ (t + 1) else 0) -
          2⁻¹ * (if t + 1 ≤ n then (2 : ℝ)⁻¹ ^ n else 0) := by
        intro n; rw [hh]; dsimp only
        split_ifs <;> subst_vars <;> first | (exfalso; omega) | ring1
      simp_rw [r]
      rw [Summable.tsum_sub (hasSum_ite_eq t _).summable ((summ_tail t).mul_left _), tsum_ite_eq,
        tsum_mul_left, tsum_geometric_inv_two_ge]
      ring
    have sum_h_sq : ∀ t : ℕ, ∑' n, (2 : ℝ)⁻¹ ^ (n + 1) * (h t n * h t n) = (2 : ℝ)⁻¹ ^ t := by
      intro t
      have r : ∀ n, (2 : ℝ)⁻¹ ^ (n + 1) * (h t n * h t n) =
          (if n = t then (2 : ℝ)⁻¹ ^ (t + 1) else 0) +
            2⁻¹ * (if t + 1 ≤ n then (2 : ℝ)⁻¹ ^ n else 0) := by
        intro n; rw [hh]; dsimp only
        split_ifs <;> subst_vars <;> first | (exfalso; omega) | ring1
      simp_rw [r]
      rw [Summable.tsum_add (hasSum_ite_eq t _).summable ((summ_tail t).mul_left _), tsum_ite_eq,
        tsum_mul_left, tsum_geometric_inv_two_ge]
      ring
    have h_mul_lt : ∀ {s t : ℕ}, s < t → ∀ n, h s n * h t n = - h t n := by
      intro s t hst n; rw [hh]; dsimp only
      split_ifs <;> first | (exfalso; omega) | norm_num
    have h_abs : ∀ t n, |h t n| ≤ 1 := by
      intro t n; rw [hh]; dsimp only; split_ifs <;> norm_num
    have key : ∀ s t, cov[fun n ↦ Real.sqrt (2 ^ s) * h s n, fun n ↦ Real.sqrt (2 ^ t) * h t n;
        M[|Set.univ]] = if s = t then 1 else 0 := by
      intro s t
      have mean : ∀ t, ∫ n, Real.sqrt (2 ^ t) * h t n ∂M = 0 := by
        intro t
        rw [integral_eq _ (bdd _ (Real.sqrt (2 ^ t)) fun n ↦ by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (h_abs t n))]
        simp_rw [mul_left_comm _ (Real.sqrt _)]
        rw [tsum_mul_left, sum_h, mul_zero]
      rw [covariance, cond_eq]
      rw [mean, mean]
      simp only [sub_zero]
      rw [integral_eq _ (bdd _ (Real.sqrt (2 ^ s) * Real.sqrt (2 ^ t)) fun n ↦ by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
          abs_of_nonneg (Real.sqrt_nonneg _)]
        have := h_abs s n; have := h_abs t n
        have := Real.sqrt_nonneg (2 ^ s); have := Real.sqrt_nonneg (2 ^ t)
        calc _ = Real.sqrt (2 ^ s) * Real.sqrt (2 ^ t) * (|h s n| * |h t n|) := by ring
          _ ≤ Real.sqrt (2 ^ s) * Real.sqrt (2 ^ t) * (1 * 1) := by gcongr
          _ = _ := by ring)]
      have r : ∀ n,
          (2 : ℝ)⁻¹ ^ (n + 1) * (Real.sqrt (2 ^ s) * h s n * (Real.sqrt (2 ^ t) * h t n)) =
          Real.sqrt (2 ^ s) * Real.sqrt (2 ^ t) * ((2 : ℝ)⁻¹ ^ (n + 1) * (h s n * h t n)) := by
        intro n; ring
      simp_rw [r]
      rw [tsum_mul_left]
      rcases lt_trichotomy s t with hst | rfl | hst
      · simp_rw [h_mul_lt hst, mul_neg]
        rw [tsum_neg, sum_h, neg_zero, mul_zero]
        simp [hst.ne]
      · rw [sum_h_sq, ← Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by positivity),
          ← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow]
        simp
      · simp_rw [mul_comm (h s _), h_mul_lt hst, mul_neg]
        rw [tsum_neg, sum_h, neg_zero, mul_zero]
        simp [hst.ne']
    subst hM hh
    exact key)
  (t := 3) (φ := 1)

open MeasureTheory ProbabilityTheory in
open scoped ENNReal in
/-- The hypotheses of `zero_le_sum_covariance_mul_cos` hold together: the points `n = 0, 1, 2, …`
with chance `2^-(n+1)` (Lean's finite-measure instance comes from conditioning on the whole space,
which changes nothing, as the chances sum to `1`); the noise `e t = √(2^t) · h t`, where `h t n` is
`1` at `n = t`, `-1` for `n > t` and `0` below `t`; each `e t` is bounded, so in `L²`, has mean `0`,
variance `v = 1`, and is uncorrelated with every other; `q = 2`, the weights `θ j = j + 1`, the time
`t = 3` and the frequency `φ = 1` (the same model as `covariance_movingAverage`'s witness). -/
example := ClassicalLean.Probability.zero_le_sum_covariance_mul_cos
  (μ := (Measure.sum fun n : ℕ ↦ ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) • Measure.dirac n)[|Set.univ])
  (q := 2) (θ := fun j ↦ (j : ℝ) + 1)
  (e := fun t n ↦ Real.sqrt (2 ^ t) * if n = t then 1 else if t < n then -1 else 0) (v := 1)
  (fun t ↦ MemLp.of_bound (measurable_of_countable _).aestronglyMeasurable (Real.sqrt (2 ^ t))
    (ae_of_all _ fun n ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (by split_ifs <;> norm_num)))
  (by
    obtain ⟨M, hM⟩ : ∃ M : Measure ℕ,
        M = Measure.sum fun n : ℕ ↦ ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) • Measure.dirac n := ⟨_, rfl⟩
    obtain ⟨h, hh⟩ : ∃ h : ℕ → ℕ → ℝ,
        h = fun t n ↦ if n = t then 1 else if t < n then -1 else 0 := ⟨_, rfl⟩
    have M_single : ∀ m : ℕ, M {m} = (2⁻¹ : ℝ≥0∞) ^ (m + 1) := by
      intro m
      rw [hM, Measure.sum_apply _ (measurableSet_singleton m)]
      simp only [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton m),
        smul_eq_mul]
      rw [tsum_eq_single m]
      · simp
      · intro n hn; simp [Set.indicator, hn]
    have cond_eq : M[|Set.univ] = M := by
      have M_univ : M Set.univ = 1 := by
        rw [hM, Measure.sum_apply _ MeasurableSet.univ]
        simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, pow_succ]
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
          ENNReal.mul_inv_cancel (by simp) (by simp)]
      rw [ProbabilityTheory.cond, Measure.restrict_univ, M_univ, inv_one, one_smul]
    have integral_eq : ∀ f : ℕ → ℝ, Integrable f M →
        ∫ n, f n ∂M = ∑' n, ((2 : ℝ)⁻¹) ^ (n + 1) * f n := by
      intro f hf
      rw [integral_countable hf]
      congr 1; ext n
      rw [measureReal_def, M_single]; simp
    have bdd : ∀ (f : ℕ → ℝ) (C : ℝ), (∀ n, |f n| ≤ C) → Integrable f M := by
      intro f C hC
      rw [← cond_eq]
      exact Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable C
        (ae_of_all _ fun n ↦ by simpa using hC n)
    have summ_tail : ∀ t : ℕ, Summable fun n : ℕ ↦ if t + 1 ≤ n then (2 : ℝ)⁻¹ ^ n else 0 :=
      fun t ↦ (summable_geometric_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
        ).of_nonneg_of_le
        (fun n ↦ by split_ifs <;> positivity)
        (fun n ↦ by split_ifs <;> first | exact le_rfl | positivity)
    have sum_h : ∀ t : ℕ, ∑' n, (2 : ℝ)⁻¹ ^ (n + 1) * h t n = 0 := by
      intro t
      have r : ∀ n, (2 : ℝ)⁻¹ ^ (n + 1) * h t n = (if n = t then (2 : ℝ)⁻¹ ^ (t + 1) else 0) -
          2⁻¹ * (if t + 1 ≤ n then (2 : ℝ)⁻¹ ^ n else 0) := by
        intro n; rw [hh]; dsimp only
        split_ifs <;> subst_vars <;> first | (exfalso; omega) | ring1
      simp_rw [r]
      rw [Summable.tsum_sub (hasSum_ite_eq t _).summable ((summ_tail t).mul_left _), tsum_ite_eq,
        tsum_mul_left, tsum_geometric_inv_two_ge]
      ring
    have sum_h_sq : ∀ t : ℕ, ∑' n, (2 : ℝ)⁻¹ ^ (n + 1) * (h t n * h t n) = (2 : ℝ)⁻¹ ^ t := by
      intro t
      have r : ∀ n, (2 : ℝ)⁻¹ ^ (n + 1) * (h t n * h t n) =
          (if n = t then (2 : ℝ)⁻¹ ^ (t + 1) else 0) +
            2⁻¹ * (if t + 1 ≤ n then (2 : ℝ)⁻¹ ^ n else 0) := by
        intro n; rw [hh]; dsimp only
        split_ifs <;> subst_vars <;> first | (exfalso; omega) | ring1
      simp_rw [r]
      rw [Summable.tsum_add (hasSum_ite_eq t _).summable ((summ_tail t).mul_left _), tsum_ite_eq,
        tsum_mul_left, tsum_geometric_inv_two_ge]
      ring
    have h_mul_lt : ∀ {s t : ℕ}, s < t → ∀ n, h s n * h t n = - h t n := by
      intro s t hst n; rw [hh]; dsimp only
      split_ifs <;> first | (exfalso; omega) | norm_num
    have h_abs : ∀ t n, |h t n| ≤ 1 := by
      intro t n; rw [hh]; dsimp only; split_ifs <;> norm_num
    have key : ∀ s t, cov[fun n ↦ Real.sqrt (2 ^ s) * h s n, fun n ↦ Real.sqrt (2 ^ t) * h t n;
        M[|Set.univ]] = if s = t then 1 else 0 := by
      intro s t
      have mean : ∀ t, ∫ n, Real.sqrt (2 ^ t) * h t n ∂M = 0 := by
        intro t
        rw [integral_eq _ (bdd _ (Real.sqrt (2 ^ t)) fun n ↦ by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (h_abs t n))]
        simp_rw [mul_left_comm _ (Real.sqrt _)]
        rw [tsum_mul_left, sum_h, mul_zero]
      rw [covariance, cond_eq]
      rw [mean, mean]
      simp only [sub_zero]
      rw [integral_eq _ (bdd _ (Real.sqrt (2 ^ s) * Real.sqrt (2 ^ t)) fun n ↦ by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
          abs_of_nonneg (Real.sqrt_nonneg _)]
        have := h_abs s n; have := h_abs t n
        have := Real.sqrt_nonneg (2 ^ s); have := Real.sqrt_nonneg (2 ^ t)
        calc _ = Real.sqrt (2 ^ s) * Real.sqrt (2 ^ t) * (|h s n| * |h t n|) := by ring
          _ ≤ Real.sqrt (2 ^ s) * Real.sqrt (2 ^ t) * (1 * 1) := by gcongr
          _ = _ := by ring)]
      have r : ∀ n,
          (2 : ℝ)⁻¹ ^ (n + 1) * (Real.sqrt (2 ^ s) * h s n * (Real.sqrt (2 ^ t) * h t n)) =
          Real.sqrt (2 ^ s) * Real.sqrt (2 ^ t) * ((2 : ℝ)⁻¹ ^ (n + 1) * (h s n * h t n)) := by
        intro n; ring
      simp_rw [r]
      rw [tsum_mul_left]
      rcases lt_trichotomy s t with hst | rfl | hst
      · simp_rw [h_mul_lt hst, mul_neg]
        rw [tsum_neg, sum_h, neg_zero, mul_zero]
        simp [hst.ne]
      · rw [sum_h_sq, ← Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by positivity),
          ← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow]
        simp
      · simp_rw [mul_comm (h s _), h_mul_lt hst, mul_neg]
        rw [tsum_neg, sum_h, neg_zero, mul_zero]
        simp [hst.ne']
    subst hM hh
    exact key)
  (t := 3) (φ := 1)

open MeasureTheory ProbabilityTheory in
open scoped ENNReal in
/-- The hypotheses of `variance_sum_movingAverage` hold together: the points `n = 0, 1, 2, …` with
chance `2^-(n+1)` (Lean's finite-measure instance comes from conditioning on the whole space, which
changes nothing, as the chances sum to `1`); the noise `e t = √(2^t) · h t`, where `h t n` is `1` at
`n = t`, `-1` for `n > t` and `0` below `t`; each `e t` is bounded, so in `L²`, has mean `0`,
variance `v = 1`, and is uncorrelated with every other; the order `q = 2` and the weights
`θ j = j + 1` (the same model as `covariance_movingAverage`'s witness). -/
example := ClassicalLean.Probability.variance_sum_movingAverage
  (μ := (Measure.sum fun n : ℕ ↦ ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) • Measure.dirac n)[|Set.univ])
  (q := 2) (θ := fun j ↦ (j : ℝ) + 1)
  (e := fun t n ↦ Real.sqrt (2 ^ t) * if n = t then 1 else if t < n then -1 else 0) (v := 1)
  (fun t ↦ MemLp.of_bound (measurable_of_countable _).aestronglyMeasurable (Real.sqrt (2 ^ t))
    (ae_of_all _ fun n ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (by split_ifs <;> norm_num)))
  (by
    obtain ⟨M, hM⟩ : ∃ M : Measure ℕ,
        M = Measure.sum fun n : ℕ ↦ ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) • Measure.dirac n := ⟨_, rfl⟩
    obtain ⟨h, hh⟩ : ∃ h : ℕ → ℕ → ℝ,
        h = fun t n ↦ if n = t then 1 else if t < n then -1 else 0 := ⟨_, rfl⟩
    have M_single : ∀ m : ℕ, M {m} = (2⁻¹ : ℝ≥0∞) ^ (m + 1) := by
      intro m
      rw [hM, Measure.sum_apply _ (measurableSet_singleton m)]
      simp only [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton m),
        smul_eq_mul]
      rw [tsum_eq_single m]
      · simp
      · intro n hn; simp [Set.indicator, hn]
    have cond_eq : M[|Set.univ] = M := by
      have M_univ : M Set.univ = 1 := by
        rw [hM, Measure.sum_apply _ MeasurableSet.univ]
        simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, pow_succ]
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
          ENNReal.mul_inv_cancel (by simp) (by simp)]
      rw [ProbabilityTheory.cond, Measure.restrict_univ, M_univ, inv_one, one_smul]
    have integral_eq : ∀ f : ℕ → ℝ, Integrable f M →
        ∫ n, f n ∂M = ∑' n, ((2 : ℝ)⁻¹) ^ (n + 1) * f n := by
      intro f hf
      rw [integral_countable hf]
      congr 1; ext n
      rw [measureReal_def, M_single]; simp
    have bdd : ∀ (f : ℕ → ℝ) (C : ℝ), (∀ n, |f n| ≤ C) → Integrable f M := by
      intro f C hC
      rw [← cond_eq]
      exact Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable C
        (ae_of_all _ fun n ↦ by simpa using hC n)
    have summ_tail : ∀ t : ℕ, Summable fun n : ℕ ↦ if t + 1 ≤ n then (2 : ℝ)⁻¹ ^ n else 0 :=
      fun t ↦ (summable_geometric_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
        ).of_nonneg_of_le
        (fun n ↦ by split_ifs <;> positivity)
        (fun n ↦ by split_ifs <;> first | exact le_rfl | positivity)
    have sum_h : ∀ t : ℕ, ∑' n, (2 : ℝ)⁻¹ ^ (n + 1) * h t n = 0 := by
      intro t
      have r : ∀ n, (2 : ℝ)⁻¹ ^ (n + 1) * h t n = (if n = t then (2 : ℝ)⁻¹ ^ (t + 1) else 0) -
          2⁻¹ * (if t + 1 ≤ n then (2 : ℝ)⁻¹ ^ n else 0) := by
        intro n; rw [hh]; dsimp only
        split_ifs <;> subst_vars <;> first | (exfalso; omega) | ring1
      simp_rw [r]
      rw [Summable.tsum_sub (hasSum_ite_eq t _).summable ((summ_tail t).mul_left _), tsum_ite_eq,
        tsum_mul_left, tsum_geometric_inv_two_ge]
      ring
    have sum_h_sq : ∀ t : ℕ, ∑' n, (2 : ℝ)⁻¹ ^ (n + 1) * (h t n * h t n) = (2 : ℝ)⁻¹ ^ t := by
      intro t
      have r : ∀ n, (2 : ℝ)⁻¹ ^ (n + 1) * (h t n * h t n) =
          (if n = t then (2 : ℝ)⁻¹ ^ (t + 1) else 0) +
            2⁻¹ * (if t + 1 ≤ n then (2 : ℝ)⁻¹ ^ n else 0) := by
        intro n; rw [hh]; dsimp only
        split_ifs <;> subst_vars <;> first | (exfalso; omega) | ring1
      simp_rw [r]
      rw [Summable.tsum_add (hasSum_ite_eq t _).summable ((summ_tail t).mul_left _), tsum_ite_eq,
        tsum_mul_left, tsum_geometric_inv_two_ge]
      ring
    have h_mul_lt : ∀ {s t : ℕ}, s < t → ∀ n, h s n * h t n = - h t n := by
      intro s t hst n; rw [hh]; dsimp only
      split_ifs <;> first | (exfalso; omega) | norm_num
    have h_abs : ∀ t n, |h t n| ≤ 1 := by
      intro t n; rw [hh]; dsimp only; split_ifs <;> norm_num
    have key : ∀ s t, cov[fun n ↦ Real.sqrt (2 ^ s) * h s n, fun n ↦ Real.sqrt (2 ^ t) * h t n;
        M[|Set.univ]] = if s = t then 1 else 0 := by
      intro s t
      have mean : ∀ t, ∫ n, Real.sqrt (2 ^ t) * h t n ∂M = 0 := by
        intro t
        rw [integral_eq _ (bdd _ (Real.sqrt (2 ^ t)) fun n ↦ by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (h_abs t n))]
        simp_rw [mul_left_comm _ (Real.sqrt _)]
        rw [tsum_mul_left, sum_h, mul_zero]
      rw [covariance, cond_eq]
      rw [mean, mean]
      simp only [sub_zero]
      rw [integral_eq _ (bdd _ (Real.sqrt (2 ^ s) * Real.sqrt (2 ^ t)) fun n ↦ by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
          abs_of_nonneg (Real.sqrt_nonneg _)]
        have := h_abs s n; have := h_abs t n
        have := Real.sqrt_nonneg (2 ^ s); have := Real.sqrt_nonneg (2 ^ t)
        calc _ = Real.sqrt (2 ^ s) * Real.sqrt (2 ^ t) * (|h s n| * |h t n|) := by ring
          _ ≤ Real.sqrt (2 ^ s) * Real.sqrt (2 ^ t) * (1 * 1) := by gcongr
          _ = _ := by ring)]
      have r : ∀ n,
          (2 : ℝ)⁻¹ ^ (n + 1) * (Real.sqrt (2 ^ s) * h s n * (Real.sqrt (2 ^ t) * h t n)) =
          Real.sqrt (2 ^ s) * Real.sqrt (2 ^ t) * ((2 : ℝ)⁻¹ ^ (n + 1) * (h s n * h t n)) := by
        intro n; ring
      simp_rw [r]
      rw [tsum_mul_left]
      rcases lt_trichotomy s t with hst | rfl | hst
      · simp_rw [h_mul_lt hst, mul_neg]
        rw [tsum_neg, sum_h, neg_zero, mul_zero]
        simp [hst.ne]
      · rw [sum_h_sq, ← Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by positivity),
          ← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow]
        simp
      · simp_rw [mul_comm (h s _), h_mul_lt hst, mul_neg]
        rw [tsum_neg, sum_h, neg_zero, mul_zero]
        simp [hst.ne']
    subst hM hh
    exact key)
