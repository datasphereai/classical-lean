/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Analysis.GradientDescent

/-!
# The global error of Euler's method

For the equation `y' = f (t, y)`, Euler's method with step `h` from `(t₀, y₀)` takes
`u₀ = y₀` and `u_{k+1} = u_k + h f (t₀ + k h, u_k)` (`eulerIterate`).

* `abs_sub_sub_mul_le_of_lipschitzWith` — the local error: if `y' = F` and `F` is
  `M`-Lipschitz, then `|y (t + h) − y t − h F t| ≤ (M/2) h²`, from order LEAN-19's descent lemma
  (`le_add_inner_gradient_add_sq`) applied to `y` and to `−y`.
* `abs_sub_eulerIterate_le` — the global error: if `y` solves `y' = f (t, y)` with
  `t ↦ f (t, y t)` `M`-Lipschitz (so `|y''| ≤ M` where `y''` exists), `f (t, ·)` is `L`-Lipschitz
  with `L > 0`, `h ≥ 0`, and Euler's method starts at `y t₀`, then after `k` steps
  `|y (t₀ + k h) − u_k| ≤ (h M / (2 L)) (exp (L k h) − 1)`.

This matches the bound in numerical-analysis textbooks; checked for this order by web search,
it is Theorem 5.9 of Burden and Faires, Numerical Analysis, as numbered in lecture notes that
follow the book (the book itself and its edition were not checked). The book assumes `|y''| ≤ M`;
here the weaker hypothesis that `y'` is `M`-Lipschitz is used. The hypotheses are assumed at every
time, not only on the interval the method covers.

## Hypotheses

Measured in order LEAN-20's checks (check C31): 300 exact cases of `y' = 2 t + c (y − t²)` with
solution `y = t²` (`M = 2`), compared with a rational lower bound of `exp`, and 200 float cases
with solution `sin`. Each hypothesis fails when dropped alone:

* `0 < L`: with `L = 0` Lean's `h M / 0` is `0`, but for `f = 2 t`, `y = t²`, `h = 1/4`, one step
  from `0` misses by `1/16`. This is no restriction: an `L`-Lipschitz map is `L'`-Lipschitz for
  every `L' ≥ L`, so an `f` that does not depend on `y` is covered with any `L > 0`.
* `0 ≤ h`: `f = 2 t`, `y = t²`, `M = 2`, `L = 1`, `h = −1`, one step from `0`: error `1`, bound
  `1 − exp (−1) ≤ 2/3`. Needed only because the bound is written with `h`: review r31 proved, in
  a scratch file, the same bound with `|h|` for every `h`; it is not added here.
* `y'` `M`-Lipschitz: `f = 2 t` with `M = 0` claimed: error `1/16`, bound `0`.
* `y` solves the equation: `y = 0` with `f = 1`: error `1/4` after one step of `1/4`, bound `0`.
* `f (t, ·)` `L`-Lipschitz (floats): `f = 2 t + 5 (y − t²)` claimed `1`-Lipschitz, `h = 1/4`,
  eight steps from `0`: the error exceeds the bound.

For the local error `abs_sub_sub_mul_le_of_lipschitzWith` (review r31's cases, computed in the
checks): without `y' = F`, `y = 0` and `F = 1` give `1 > 0` at `t = 0`, `h = 1`; without the
Lipschitz bound, `y = t³`, `F = 3 t²` with `M = 0` claimed give `1 > 0`.

The plan's row names the theorem `abs_sub_eulerStep_le`; it bounds `k` steps, so it is named
`abs_sub_eulerIterate_le` here.

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-20, `grep -rniE` over Mathlib):
`euler.?s? method|explicit euler|forward euler` 0. The plan's row names Mathlib's
`discrete_gronwall` and `taylor_mean_remainder_lagrange`; the proof here uses neither: the local
error comes from order LEAN-19's descent lemma, and the recursion `e_{k+1} ≤ (1 + h L) e_k + M h²/2`
is solved by induction, with `1 + h L ≤ exp (h L)`. `discrete_gronwall` would give only
`k (M h²/2) exp (L k h)`, a weaker bound (review r31).
-/

open scoped NNReal

namespace ClassicalLean.Analysis

/-- `k` steps of Euler's method for `y' = f (t, y)` with step `h` from `(t₀, y₀)`:
`u₀ = y₀`, `u_{k+1} = u_k + h f (t₀ + k h, u_k)`. -/
noncomputable def eulerIterate (f : ℝ → ℝ → ℝ) (t₀ h y₀ : ℝ) : ℕ → ℝ
  | 0 => y₀
  | k + 1 => eulerIterate f t₀ h y₀ k + h * f (t₀ + k * h) (eulerIterate f t₀ h y₀ k)

/-- **The local error of one Euler step.** If `y' = F` and `F` is `M`-Lipschitz, then
`|y (t + h) − y t − h F t| ≤ (M/2) h²` for every `t` and `h`. Order LEAN-19's descent lemma bounds
`y (t + h)` above by `y t + h F t + (M/2) h²`, and the same lemma for `−y` bounds it below. -/
theorem abs_sub_sub_mul_le_of_lipschitzWith {y F : ℝ → ℝ} {M : ℝ≥0}
    (hy : ∀ t, HasDerivAt y (F t) t) (hM : LipschitzWith M F) (t h : ℝ) :
    |y (t + h) - y t - h * F t| ≤ M / 2 * h ^ 2 := by
  have h1 := le_add_inner_gradient_add_sq (fun x ↦ (hy x).hasGradientAt') hM t (t + h)
  have hM' : LipschitzWith M fun x ↦ -F x :=
    LipschitzWith.of_dist_le_mul fun a b ↦ by rw [dist_neg_neg]; exact hM.dist_le_mul a b
  have h2 := le_add_inner_gradient_add_sq (f := fun s ↦ -y s)
    (fun x ↦ (hy x).neg.hasGradientAt') hM' t (t + h)
  simp only [add_sub_cancel_left, Real.norm_eq_abs, sq_abs, RCLike.inner_apply,
    conj_trivial] at h1 h2
  rw [abs_le]
  constructor <;> nlinarith

/-- **The global error of Euler's method.** If `y` solves `y' = f (t, y)` at every time, with
`t ↦ f (t, y t)` `M`-Lipschitz and every `f (t, ·)` `L`-Lipschitz for some `L > 0`, and the
method starts at `y t₀` with step `h ≥ 0`, then after `k` steps
`|y (t₀ + k h) − u_k| ≤ (h M / (2 L)) (exp (L k h) − 1)`. The errors `e_k` satisfy
`e_{k+1} ≤ (1 + h L) e_k + (M/2) h²`, so `e_k ≤ (h M / (2 L)) ((1 + h L)^k − 1)`, and
`1 + h L ≤ exp (h L)`. -/
theorem abs_sub_eulerIterate_le {f : ℝ → ℝ → ℝ} {y : ℝ → ℝ} {t₀ h : ℝ} {L M : ℝ≥0}
    (hy : ∀ t, HasDerivAt y (f t (y t)) t) (hM : LipschitzWith M fun t ↦ f t (y t))
    (hL : ∀ t, LipschitzWith L (f t)) (hL0 : 0 < L) (hh : 0 ≤ h) (k : ℕ) :
    |y (t₀ + k * h) - eulerIterate f t₀ h (y t₀) k|
      ≤ h * M / (2 * L) * (Real.exp (L * (k * h)) - 1) := by
  have hL0' : (0 : ℝ) < L := hL0
  have hM0 : (0 : ℝ) ≤ M := M.2
  set c : ℝ := h * M / (2 * L)
  have hc : 0 ≤ c := by positivity
  -- the recursion, solved
  have hrec : ∀ k : ℕ, |y (t₀ + k * h) - eulerIterate f t₀ h (y t₀) k|
      ≤ c * ((1 + h * L) ^ k - 1) := by
    intro k
    induction k with
    | zero => simp [eulerIterate]
    | succ k ih =>
      set u := eulerIterate f t₀ h (y t₀) k
      set t := t₀ + k * h
      have ht : t₀ + ((k + 1 : ℕ) : ℝ) * h = t + h := by push_cast; ring
      have hloc := abs_sub_sub_mul_le_of_lipschitzWith hy hM t h
      have hlip : |f t (y t) - f t u| ≤ L * |y t - u| := by
        have := (hL t).dist_le_mul (y t) u
        rwa [Real.dist_eq, Real.dist_eq] at this
      have hsplit : y (t + h) - (u + h * f t u)
          = (y (t + h) - y t - h * f t (y t)) + (y t - u) + h * (f t (y t) - f t u) := by ring
      change |y (t₀ + ((k + 1 : ℕ) : ℝ) * h) - (u + h * f t u)| ≤ _
      rw [ht, hsplit]
      have habs : |h * (f t (y t) - f t u)| ≤ h * (L * |y t - u|) := by
        rw [abs_mul, abs_of_nonneg hh]
        exact mul_le_mul_of_nonneg_left hlip hh
      calc |(y (t + h) - y t - h * f t (y t)) + (y t - u) + h * (f t (y t) - f t u)|
          ≤ |y (t + h) - y t - h * f t (y t)| + |y t - u| + |h * (f t (y t) - f t u)| :=
            abs_add_three _ _ _
        _ ≤ M / 2 * h ^ 2 + |y t - u| + h * (L * |y t - u|) := by gcongr
        _ = (1 + h * L) * |y t - u| + M / 2 * h ^ 2 := by ring
        _ ≤ (1 + h * L) * (c * ((1 + h * L) ^ k - 1)) + M / 2 * h ^ 2 := by
            gcongr
        _ = c * ((1 + h * L) ^ (k + 1) - 1) := by
            simp only [c]
            field_simp
            ring
  refine (hrec k).trans (mul_le_mul_of_nonneg_left ?_ hc)
  have hexp : (1 + h * L) ^ k ≤ Real.exp (L * (k * h)) := by
    have h1 : 1 + h * L ≤ Real.exp (h * L) := by linarith [Real.add_one_le_exp (h * L)]
    calc (1 + h * L) ^ k ≤ Real.exp (h * L) ^ k :=
          pow_le_pow_left₀ (by positivity) h1 k
      _ = Real.exp (L * (k * h)) := by rw [← Real.exp_nat_mul]; ring_nf
  linarith

end ClassicalLean.Analysis
