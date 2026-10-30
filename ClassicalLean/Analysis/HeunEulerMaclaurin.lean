/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Analysis.EulerMethod
import ClassicalLean.Analysis.EulerMaclaurin

/-!
# The exact global error of Heun's method at unit steps

For an equation `y' = g(t)` whose right side does not depend on `y`, Heun's method
(`heunIterate`, `ClassicalLean.Analysis.EulerMethod`) with step `1` from an integer `a` is the
trapezoid sum on the integer nodes, and Euler–Maclaurin to second order (`sum_eq_integral_add_two`,
`ClassicalLean.Analysis.EulerMaclaurin`) gives its error exactly:

* `heunIterate_one_eq_add_sum_sub` — for integers `a ≤ b`, after `b − a` steps of `1` from
  `(a, y₀)` the iterate is `y₀ + ∑_{k=a}^{b} g k − (g a + g b)/2`;
* `sub_heunIterate_eq_eulerMaclaurin` — under `sum_eq_integral_add_two`'s hypotheses on `g` (there
  named `f f' f''`), `y₀ + ∫ₐᵇ g` minus the iterate is
  `−(g' b − g' a)/12 + ∫ₐᵇ B₂(fract t)/2 · g''`, with `B₂` Mathlib's `bernoulliFun 2`.

Bridge row 167 of MATH-PLAN-library-2's bridges file (order CLOUD-MATH-5), stated and proved by the
Claude Code cloud session of that order from the row's sketch; no draft. Choices: the row's error
is `y b` minus the iterate, with `y b` the solution's value at `b`; for `y' = g` with `y a = y₀`
that value is `y₀ + ∫ₐᵇ g`, so the second theorem is stated with the integral and no solution `y`
appears. The number of steps `b − a` is the natural number `(b - a).toNat`, as `heunIterate` counts
steps in `ℕ`; the start is the cast `(a : ℝ)`, and the sum runs over `Finset.Icc a b` in `ℤ`, as in
`sum_eq_integral_add_two`. Only unit steps: the library's Euler–Maclaurin is stated on integer
nodes. The hypothesis `a ≤ b` of the first theorem is needed: for `a > b` no step is taken and the
iterate is `y₀`, while the right side is `y₀ − (g a + g b)/2`.

The proof. Each step of Heun's method for `y' = g(t)` with step `1` from the node `a + k` adds
`(g (a + k) + g (a + k + 1))/2`; by induction on the number of steps, `n` steps give
`y₀ + ∑_{k=a}^{a+n} g k − (g a + g (a + n))/2`. Then `sum_eq_integral_add_two` replaces the sum.
-/

open Set MeasureTheory

namespace ClassicalLean.Analysis.HeunEulerMaclaurin

/-- **Heun's method at unit steps for `y' = g(t)` is the trapezoid sum.** For integers `a ≤ b`,
`b − a` steps of `1` from `(a, y₀)` give `y₀ + ∑_{k=a}^{b} g k − (g a + g b)/2`. -/
theorem heunIterate_one_eq_add_sum_sub {g : ℝ → ℝ} {a b : ℤ} {y₀ : ℝ} (hab : a ≤ b) :
    heunIterate (fun t _ ↦ g t) (a : ℝ) 1 y₀ (b - a).toNat =
      y₀ + ∑ k ∈ Finset.Icc a b, g k - (g a + g b) / 2 := by
  obtain ⟨n, rfl⟩ := Int.le.dest hab
  clear hab
  rw [show (a + n - a).toNat = n by simp]
  induction n with
  | zero =>
    simp only [heunIterate, Nat.cast_zero, add_zero, Finset.Icc_self, Finset.sum_singleton]
    ring
  | succ n ih =>
    have hI : Finset.Icc a (a + ((n + 1 : ℕ) : ℤ)) = insert (a + n + 1) (Finset.Icc a (a + n)) := by
      rw [Finset.insert_Icc_right_eq_Icc_add_one (by omega)]
      push_cast
      ring_nf
    have hnot : a + n + 1 ∉ Finset.Icc a (a + n) := by
      rw [Finset.mem_Icc]
      omega
    rw [heunIterate, ih, hI, Finset.sum_insert hnot]
    push_cast
    simp only [mul_one, add_assoc]
    ring

/-- **The exact global error of Heun's method at unit steps.** For integers `a ≤ b`, `g`
continuous on `[a, b]` with derivative `g'` inside, `g'` continuous on `[a, b]` with derivative
`g''` inside, and `g''` integrable, `b − a` steps of `1` from `(a, y₀)` for `y' = g(t)` fall short
of `y₀ + ∫ₐᵇ g` (which is `y b` for the solution with `y a = y₀`; stated with the integral, so no
solution `y` appears) by exactly `−(g' b − g' a)/12 + ∫ₐᵇ B₂(fract t)/2 · g''`, with
`B₂ = bernoulliFun 2`. -/
theorem sub_heunIterate_eq_eulerMaclaurin {g g' g'' : ℝ → ℝ} {a b : ℤ} {y₀ : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn g (Icc (a : ℝ) b))
    (hf' : ∀ t ∈ Ioo (a : ℝ) b, HasDerivAt g (g' t) t)
    (hf'c : ContinuousOn g' (Icc (a : ℝ) b))
    (hf'' : ∀ t ∈ Ioo (a : ℝ) b, HasDerivAt g' (g'' t) t)
    (hint : IntervalIntegrable g'' volume (a : ℝ) b) :
    (y₀ + ∫ t in (a : ℝ)..b, g t) - heunIterate (fun t _ ↦ g t) (a : ℝ) 1 y₀ (b - a).toNat =
      -(g' b - g' a) / 12 + ∫ t in (a : ℝ)..b, bernoulliFun 2 (Int.fract t) / 2 * g'' t := by
  rw [heunIterate_one_eq_add_sum_sub hab, sum_eq_integral_add_two hab hf hf' hf'c hf'' hint]
  ring

end ClassicalLean.Analysis.HeunEulerMaclaurin

/-- The hypotheses of `heunIterate_one_eq_add_sum_sub` hold together: the integers `a = 0` and
`b = 3` (`0 ≤ 3`, three steps), `g x = x ^ 2` and `y₀ = 1`. What moves: the iterate moves at every
step, by `1/2`, `5/2` and `13/2`, to `21/2 = 1 + 14 − 9/2`. -/
example := ClassicalLean.Analysis.HeunEulerMaclaurin.heunIterate_one_eq_add_sum_sub
  (g := fun x ↦ x ^ 2) (a := 0) (b := 3) (y₀ := 1) (by norm_num)

/-- The hypotheses of `sub_heunIterate_eq_eulerMaclaurin` hold together (the model of
`sum_eq_integral_add_two`'s witness): the integers `a = 0` and `b = 2` (`0 ≤ 2`, two steps), from
`y₀ = 1`, `g x = x ^ 4`, continuous, with derivative `g' x = 4 x ^ 3` at every point, which is
continuous with derivative `g'' x = 12 x ^ 2`, continuous, so integrable on `[0, 2]`. What moves:
the iterate moves at both steps, by `1/2` and `17/2`, to `10`; `g''` is not linear, so the remainder
`∫ B₂(fract t)/2 · g''` is not `0`: it is `1/30` on each unit interval, `1/15` in all (a cubic would
make it `0`, since `∫₀¹ B₂ = ∫₀¹ s B₂(s) ds = 0`). -/
example := ClassicalLean.Analysis.HeunEulerMaclaurin.sub_heunIterate_eq_eulerMaclaurin
  (g := fun x ↦ x ^ 4) (g' := fun x ↦ 4 * x ^ 3) (g'' := fun x ↦ 12 * x ^ 2) (a := 0) (b := 2)
  (y₀ := 1) (by norm_num)
  (continuous_pow 4).continuousOn
  (fun t _ ↦ by simpa using hasDerivAt_pow 4 t)
  (continuous_const.mul (continuous_pow 3)).continuousOn
  (fun t _ ↦ by convert (hasDerivAt_pow 3 t).const_mul (4 : ℝ) using 1; norm_num; ring)
  ((continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _)
