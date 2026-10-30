/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Analysis.EulerMethod
import ClassicalLean.Analysis.Simpson

/-!
# Richardson extrapolation of Heun's method is Simpson's rule

For an equation `y' = g(t)` whose right side does not depend on `y`, Heun's method
(`heunIterate`, `ClassicalLean.Analysis.EulerMethod`) is the composite trapezoidal rule, and
Richardson's extrapolation of two runs, `(4 u₂ₙ − uₙ)/3`, is composite Simpson's rule (`simpson`,
`ClassicalLean.Analysis.Simpson`). With `heunIterate (fun t _ ↦ g t) a h y₀ n` the `n`-th iterate of
Heun's method for `y' = g(t)` with step `h` from `(a, y₀)`:

* `heunIterate_add_eq_trapezoidal` — with `N` steps of `h = (b − a)/N`, the iterate is
  `y₀ + trapezoidal_integral g N a b` (Mathlib's composite trapezoidal rule), for every `N`;
* `richardson_heunIterate_eq_simpson` — `(4 u − v)/3 = y₀ + simpson g N a b`, where `u` is the run
  with `2N` steps of `(b − a)/(2N)` and `v` the run with `N` steps of `(b − a)/N`, for every `N`;
* `abs_sub_richardson_heunIterate_le` — under `simpson_error_le`'s hypotheses on `g` (four
  derivatives on `[a, b]`, `|g⁗| ≤ M`, `N ≥ 1`), the extrapolated value is within
  `(b − a) ((b − a)/(2N))⁴ M / 180` of `y₀ + ∫ₐᵇ g`.

Bridge row 166 of MATH-PLAN-library-2's bridges file (order CLOUD-MATH-5), stated and proved by the
Claude Code cloud session of that order from the row's sketch; no draft. Choices: the row's error is
against `y b`, the solution's value at `b`; for `y' = g` with `y a = y₀` that value is `y₀ + ∫ₐᵇ g`,
so the third theorem is stated with the integral and no solution `y` appears. The `2N` run's step is
written `(b - a) / (2 * (N : ℝ))`, Simpson's step and the one in `simpson_error_le`'s bound. At
`N = 0` the first two theorems hold with both sides `y₀`, since Lean's `(b − a)/0 = 0` makes the
step, `trapezoidal_integral` and `simpson` all `0`.

The proof. Each step of Heun's method for `y' = g(t)` adds `h/2 (g (a + k h) + g (a + k h + h))`, so
after `N` steps the iterate is `y₀` plus `h/2` times the sum of `g` at consecutive nodes, which is
`h` times `(g a + g b)/2` plus the values of `g` at the inner nodes, the composite trapezoid. Then
Simpson's rule is `(4 T₂ₙ − Tₙ)/3` (`simpson_eq_trapezoidal`), and its error bound is
`simpson_error_le`.
-/

open Set Finset

namespace ClassicalLean.Analysis.HeunRichardson

/-- Heun's method for `y' = g(t)`, any step `h`: after `n` steps from `(a, y₀)` the iterate is
`y₀ + h/2 · ∑_{k < n} (g (a + k h) + g (a + k h + h))`. -/
theorem heunIterate_eq_add_sum (g : ℝ → ℝ) (a h y₀ : ℝ) (n : ℕ) :
    heunIterate (fun t _ ↦ g t) a h y₀ n =
      y₀ + h / 2 * ∑ k ∈ range n, (g (a + k * h) + g (a + k * h + h)) := by
  induction n with
  | zero => simp [heunIterate]
  | succ n ih => rw [heunIterate, ih, sum_range_succ]; ring

/-- **Heun's method for `y' = g(t)` is the trapezoidal rule.** With `N` steps of
`h = (b − a)/N` from `(a, y₀)`, Heun's iterate is `y₀ + trapezoidal_integral g N a b`, for every
`N` (at `N = 0` both sides are `y₀`). -/
theorem heunIterate_add_eq_trapezoidal (g : ℝ → ℝ) (a b y₀ : ℝ) (N : ℕ) :
    heunIterate (fun t _ ↦ g t) a ((b - a) / N) y₀ N = y₀ + trapezoidal_integral g N a b := by
  rw [heunIterate_eq_add_sum]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [trapezoidal_integral]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  set h := (b - a) / ((n + 1 : ℕ) : ℝ) with hh
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  -- every node is `a + j h`
  have hnode : ∀ k : ℕ, a + (k + 1 : ℝ) * (b - a) / ((n + 1 : ℕ) : ℝ) = a + k * h + h := by
    intro k; rw [hh]; field_simp; ring
  have hb : a + (n : ℝ) * h + h = b := by rw [hh]; push_cast; field_simp; ring
  rw [trapezoidal_integral, ← hh, Nat.add_sub_cancel, sum_add_distrib,
    sum_range_succ (fun k : ℕ ↦ g (a + k * h + h)), sum_range_succ' (fun k : ℕ ↦ g (a + k * h)), hb]
  simp only [hnode]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero]
  have hk : ∀ k : ℕ, a + ((k : ℝ) + 1) * h = a + k * h + h := fun k ↦ by ring
  simp only [hk]
  ring

/-- **Richardson extrapolation of Heun's method is Simpson's rule.** For `y' = g(t)` from
`(a, y₀)`, with the run of `2N` steps of `(b − a)/(2N)` and the run of `N` steps of `(b − a)/N`,
`(4 u₂ₙ − uₙ)/3 = y₀ + simpson g N a b`, for every `N`. -/
theorem richardson_heunIterate_eq_simpson (g : ℝ → ℝ) (a b y₀ : ℝ) (N : ℕ) :
    (4 * heunIterate (fun t _ ↦ g t) a ((b - a) / (2 * (N : ℝ))) y₀ (2 * N) -
        heunIterate (fun t _ ↦ g t) a ((b - a) / N) y₀ N) / 3 = y₀ + simpson g N a b := by
  have h2 := heunIterate_add_eq_trapezoidal g a b y₀ (2 * N)
  push_cast at h2
  rw [h2, heunIterate_add_eq_trapezoidal, simpson_eq_trapezoidal]
  ring

/-- **The error of Richardson-extrapolated Heun for `y' = g(t)`.** If `g` is four times
differentiable within `[a, b]` (derivatives `g₁, …, g₄`, one-sided at the ends), `|g⁗| ≤ M` there
and `N ≥ 1`, then `(4 u₂ₙ − uₙ)/3` is within `(b − a) ((b − a)/(2N))⁴ M / 180` of `y₀ + ∫ₐᵇ g`,
which is `y b` for the solution `y` of `y' = g` with `y a = y₀` (stated with the integral, so no
solution `y` appears). -/
theorem abs_sub_richardson_heunIterate_le {g g₁ g₂ g₃ g₄ : ℝ → ℝ} {a b M y₀ : ℝ} (hab : a ≤ b)
    {N : ℕ} (hN : 0 < N)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt g (g₁ x) (Icc a b) x)
    (hf₁ : ∀ x ∈ Icc a b, HasDerivWithinAt g₁ (g₂ x) (Icc a b) x)
    (hf₂ : ∀ x ∈ Icc a b, HasDerivWithinAt g₂ (g₃ x) (Icc a b) x)
    (hf₃ : ∀ x ∈ Icc a b, HasDerivWithinAt g₃ (g₄ x) (Icc a b) x)
    (hM : ∀ x ∈ Icc a b, |g₄ x| ≤ M) :
    |(y₀ + ∫ x in a..b, g x) -
        (4 * heunIterate (fun t _ ↦ g t) a ((b - a) / (2 * (N : ℝ))) y₀ (2 * N) -
          heunIterate (fun t _ ↦ g t) a ((b - a) / N) y₀ N) / 3| ≤
      (b - a) * ((b - a) / (2 * N)) ^ 4 * M / 180 := by
  rw [richardson_heunIterate_eq_simpson, add_sub_add_left_eq_sub]
  exact simpson_error_le hab hN hf hf₁ hf₂ hf₃ hM

end ClassicalLean.Analysis.HeunRichardson

/-- The hypotheses of `abs_sub_richardson_heunIterate_le` hold together (the model of
`simpson_error_le`'s witness): on `[0, 1]` (`0 ≤ 1`, not a point), from `y₀ = 1`, with `N = 2` (the
runs take 4 and 2 steps, Simpson's rule two panel pairs), `g x = x ^ 4` and its derivatives
`4 x ^ 3`, `12 x ^ 2`, `24 x` and `24`, each the derivative of the one before on the interval, and
`|g⁗| = 24 ≤ M = 24`. What moves: both Heun runs move at every step, the run of 2 steps by
`1/64` and `17/64` (to `41/32`), the run of 4 steps by `1/2048`, `17/2048`, `97/2048` and `337/2048`
(to `625/512`); the fourth derivative is not `0`, so Simpson's rule is not exact here, and the bound
`(1/4) ^ 4 · 24 / 180 = 1/1920` is positive (the error, `1/1920`, attains it). -/
example := ClassicalLean.Analysis.HeunRichardson.abs_sub_richardson_heunIterate_le
  (g := fun x ↦ x ^ 4) (g₁ := fun x ↦ 4 * x ^ 3) (g₂ := fun x ↦ 12 * x ^ 2) (g₃ := fun x ↦ 24 * x)
  (g₄ := fun _ ↦ 24) (a := 0) (b := 1) (M := 24) (y₀ := 1) (by norm_num) (N := 2) (by norm_num)
  (fun x _ ↦ by simpa using (hasDerivAt_pow 4 x).hasDerivWithinAt)
  (fun x _ ↦ by
    have := ((hasDerivAt_pow 3 x).const_mul 4).hasDerivWithinAt (s := Icc 0 1)
    convert this using 1; ring)
  (fun x _ ↦ by
    have := ((hasDerivAt_pow 2 x).const_mul 12).hasDerivWithinAt (s := Icc 0 1)
    convert this using 1; ring)
  (fun x _ ↦ by simpa using ((hasDerivAt_id x).const_mul 24).hasDerivWithinAt)
  (fun x _ ↦ by norm_num)
