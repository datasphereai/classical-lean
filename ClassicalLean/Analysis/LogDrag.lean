/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The cost of fluctuation for products of growth factors

* `sum_mul_log_le_log_sum_mul` (Jensen): for weights `w i ≥ 0` summing to `1` and factors
  `x i > 0`, `∑ w i log (x i) ≤ log (∑ w i x i)`: the average of the logs is at most the log of
  the average. `mean_log_one_add_nonpos`: if returns `r i` average to `0`, the average of
  `log (1 + r i)` is at most `0`.
* `log_one_add_bounds`: for `|r| ≤ R < 1`,
  `r - r ^ 2 (1 / 2 + R / (1 - R)) ≤ log (1 + r) ≤ r - r ^ 2 (1 / 2 - R / (1 - R))`.
* `mean_log_one_add_le`, `le_mean_log_one_add`: averaged over returns bounded by `R`, the shortfall
  of the average log growth below the average return lies between `(1/2 - R/(1-R))` and
  `(1/2 + R/(1-R))` times the average of `r ^ 2`. With average return `0` this is the drag:
  roughly half the mean square return.

## What Mathlib provides

Jensen's inequality (`ConcaveOn.le_map_sum`) with the concavity of `log`
(`strictConcaveOn_log_Ioi`), and the log series with an exact remainder
(`Real.abs_log_sub_add_sum_range_le`).
-/

open Real Finset

namespace ClassicalLean.Analysis.LogDrag

/-- **Jensen for logarithms.** The weighted average of the logs of positive factors is at most the
log of their weighted average. For a trader: compounding never beats the average factor, so
swings cost growth. -/
theorem sum_mul_log_le_log_sum_mul {ι : Type*} (s : Finset ι) {w x : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1) (hx : ∀ i ∈ s, 0 < x i) :
    ∑ i ∈ s, w i * log (x i) ≤ log (∑ i ∈ s, w i * x i) := by
  have := strictConcaveOn_log_Ioi.concaveOn.le_map_sum hw hw1 (fun i hi ↦ Set.mem_Ioi.mpr (hx i hi))
  simpa [smul_eq_mul] using this

/-- **Zero average return means non-positive average log growth.** If returns `r i > -1` average
to `0` over `n > 0` steps, the average of `log (1 + r i)` is at most `0`. For a trader: a strategy
whose returns average zero loses money when compounded. -/
theorem mean_log_one_add_nonpos {n : ℕ} (hn : 0 < n) {r : ℕ → ℝ} (hr : ∀ i ∈ range n, -1 < r i)
    (hmean : ∑ i ∈ range n, r i = 0) : ∑ i ∈ range n, log (1 + r i) ≤ 0 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h := sum_mul_log_le_log_sum_mul (range n) (w := fun _ ↦ 1 / (n : ℝ)) (x := fun i ↦ 1 + r i)
    (fun _ _ ↦ by positivity) (by rw [sum_const, card_range, nsmul_eq_mul]; field_simp)
    (fun i hi ↦ by linarith [hr i hi])
  have hs : ∑ i ∈ range n, 1 / (n : ℝ) * (1 + r i) = 1 := by
    rw [← mul_sum, sum_add_distrib, hmean, sum_const, card_range, nsmul_eq_mul]; field_simp; simp
  rw [hs, log_one, ← mul_sum] at h
  have : 0 < 1 / (n : ℝ) := by positivity
  nlinarith

/-- **Two-sided bound on `log (1 + r)`.** For `|r| ≤ R < 1`:
`r - r ^ 2 (1/2 + R/(1-R)) ≤ log (1 + r) ≤ r - r ^ 2 (1/2 - R/(1-R))`. For a trader: the log
growth of a single return is the return minus about half its square, with a stated error. -/
theorem log_one_add_bounds {r R : ℝ} (hR : R < 1) (hr : |r| ≤ R) :
    r - r ^ 2 * (1 / 2 + R / (1 - R)) ≤ log (1 + r) ∧
      log (1 + r) ≤ r - r ^ 2 * (1 / 2 - R / (1 - R)) := by
  have hr1 : |(-r)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hr1 2
  simp only [sum_range_succ, sum_range_zero, zero_add, pow_one, Nat.cast_zero, Nat.cast_one,
    sub_neg_eq_add, abs_neg] at h
  have hR0 : 0 ≤ R := (abs_nonneg r).trans hr
  have h1R : 0 < 1 - R := by linarith
  have h1r : 0 < 1 - |r| := by linarith
  -- |r| ^ 3 / (1 - |r|) ≤ r ^ 2 * (R / (1 - R))
  have hcube : |r| ^ 3 / (1 - |r|) ≤ r ^ 2 * (R / (1 - R)) := by
    have hsq : |r| ^ 2 = r ^ 2 := sq_abs r
    rw [div_le_iff₀ h1r]
    have : |r| ^ 3 = |r| * r ^ 2 := by rw [← hsq]; ring
    rw [this]
    have hfrac : R / (1 - R) * (1 - |r|) ≥ R := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ h1R]; nlinarith [abs_nonneg r]
    nlinarith [sq_nonneg r, abs_nonneg r, mul_le_mul_of_nonneg_left hfrac (sq_nonneg r)]
  have hb := (abs_le.mp (h.trans hcube))
  constructor <;> nlinarith [hb.1, hb.2]

/-- **Average log growth, upper bound.** For returns with `|r i| ≤ R < 1`, the average of
`log (1 + r i)` is at most the average return minus `(1/2 - R/(1-R))` times the average square.
For a trader: with average return `0`, swings of size `σ` cost at least about `σ ^ 2 / 2` per step. -/
theorem mean_log_one_add_le {n : ℕ} {r : ℕ → ℝ} {R : ℝ} (hR : R < 1)
    (hr : ∀ i ∈ range n, |r i| ≤ R) :
    ∑ i ∈ range n, log (1 + r i) ≤
      ∑ i ∈ range n, r i - (1 / 2 - R / (1 - R)) * ∑ i ∈ range n, r i ^ 2 := by
  rw [mul_sum, ← sum_sub_distrib]
  exact sum_le_sum fun i hi ↦ by
    have := (log_one_add_bounds hR (hr i hi)).2; nlinarith

/-- **Average log growth, lower bound.** For returns with `|r i| ≤ R < 1`, the average of
`log (1 + r i)` is at least the average return minus `(1/2 + R/(1-R))` times the average square.
For a trader: the drag from swings is at most about half the mean square return, plus a small
correction `R / (1 - R)`. -/
theorem le_mean_log_one_add {n : ℕ} {r : ℕ → ℝ} {R : ℝ} (hR : R < 1)
    (hr : ∀ i ∈ range n, |r i| ≤ R) :
    ∑ i ∈ range n, r i - (1 / 2 + R / (1 - R)) * ∑ i ∈ range n, r i ^ 2 ≤
      ∑ i ∈ range n, log (1 + r i) := by
  rw [mul_sum, ← sum_sub_distrib]
  exact sum_le_sum fun i hi ↦ by
    have := (log_one_add_bounds hR (hr i hi)).1; nlinarith

end ClassicalLean.Analysis.LogDrag
