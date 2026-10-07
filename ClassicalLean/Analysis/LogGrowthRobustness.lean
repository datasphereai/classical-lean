/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Analysis.LogGrowthRate
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# What a wrong fraction costs, and why a fraction of the optimum is used

Continuing `ClassicalLean.Analysis.LogGrowthRate`, with `0 < p < 1`, `0 < b`,
`g x = logGrowth p b x` and `x* = optimalFraction p b`:

* **Any other fraction is strictly worse** (`logGrowth_lt_optimalFraction`): `g x < g x*` for every
  `x ≠ x*` in `[0, 1)`. In particular a fraction computed from a wrong estimate `q ≠ p` of `p` loses
  growth (`logGrowth_lt_of_estimate_ne`).
* **Far above the optimum, growth is negative** (`logGrowth_neg_of_lt`): `g x < 0` whenever
  `0 < x < 1` and `x > 2 b x* / (1 - p)`. This holds for every payout `b`. The stronger "negative
  already at twice the optimum" is *not* claimed: an exact check found it true for every case tried
  with `b ≤ 1`, and false for many cases with `b > 1` (for example `b = 2`, `p = 0.459`).
* **Half the optimal fraction keeps at least half the optimal growth** (`half_logGrowth_le`):
  `g x* / 2 ≤ g (x* / 2)`, by concavity of the logarithm. This, with the first two items, is the
  usual reason for betting a fraction of the optimum when `p` is only estimated.
* **Gains combine by multiplying** (`log_prod_growth`, which is Mathlib's `Real.log_prod`): the log
  of total growth over several steps is the sum of the per-step logs. **A rise of `r` followed by a
  fall of `r` loses** (`one_add_mul_one_sub_lt_one`): `(1 + r) (1 - r) < 1` for `r ≠ 0`.

The bound `log (1 - x) ≤ -x - x ^ 2 / 2` used for the second item comes from Mathlib's series
`Real.hasSum_pow_div_log_of_abs_lt_one`.
-/

open Real Finset

namespace ClassicalLean.Analysis.LogGrowthRobustness

open ClassicalLean.Analysis.LogGrowthRate

variable {p b : ℝ}

private theorem one_sub_optimalFraction_pos (hp1 : p < 1) (hb : 0 < b) :
    0 < (1 - p) * (1 + b) / b := by
  apply div_pos _ hb; nlinarith

private theorem weighted_sum (hp0 : 0 < p) (hp1 : p < 1) (hb : 0 < b) (x : ℝ) :
    p * ((1 + b * x) / (p * (1 + b)) - 1) +
        (1 - p) * ((1 - x) / ((1 - p) * (1 + b) / b) - 1) = 0 := by
  have : p ≠ 0 := hp0.ne'
  have : (1 - p) ≠ 0 := by linarith
  have : (1 + b) ≠ 0 := by linarith
  field_simp
  ring

/-- **Any fraction other than the optimum is strictly worse.** -/
theorem logGrowth_lt_optimalFraction (hp0 : 0 < p) (hp1 : p < 1) (hb : 0 < b) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) (hne : x ≠ optimalFraction p b) :
    logGrowth p b x < logGrowth p b (optimalFraction p b) := by
  have hu : 0 < 1 + b * x := by nlinarith
  have hv : 0 < 1 - x := by linarith
  have hU : 0 < p * (1 + b) := by positivity
  have hV := one_sub_optimalFraction_pos hp1 hb
  have hratio : (1 + b * x) / (p * (1 + b)) ≠ 1 := by
    intro h
    rw [div_eq_one_iff_eq hU.ne', ← one_add_mul_optimalFraction hb] at h
    exact hne (mul_left_cancel₀ hb.ne' (by linarith))
  have l1 := Real.log_lt_sub_one_of_pos (div_pos hu hU) hratio
  have l2 := Real.log_le_sub_one_of_pos (div_pos hv hV)
  rw [Real.log_div hu.ne' hU.ne'] at l1
  rw [Real.log_div hv.ne' hV.ne'] at l2
  have hsum := weighted_sum hp0 hp1 hb x
  unfold logGrowth
  rw [one_add_mul_optimalFraction hb, one_sub_optimalFraction hb]
  nlinarith [mul_lt_mul_of_pos_left l1 hp0,
    mul_le_mul_of_nonneg_left l2 (by linarith : 0 ≤ 1 - p)]

theorem optimalFraction_injective (hb : 0 < b) {q : ℝ}
    (h : optimalFraction q b = optimalFraction p b) : q = p := by
  unfold optimalFraction at h
  field_simp at h
  nlinarith

/-- **A wrong estimate costs growth.** If the fraction is computed from an estimate `q ≠ p` and lies
in `[0, 1)`, the growth under the true `p` is strictly below the optimum. -/
theorem logGrowth_lt_of_estimate_ne (hp0 : 0 < p) (hp1 : p < 1) (hb : 0 < b) {q : ℝ} (hq : q ≠ p)
    (hx0 : 0 ≤ optimalFraction q b) (hx1 : optimalFraction q b < 1) :
    logGrowth p b (optimalFraction q b) < logGrowth p b (optimalFraction p b) :=
  logGrowth_lt_optimalFraction hp0 hp1 hb hx0 hx1 fun h ↦ hq (optimalFraction_injective hb h)

/-- `log (1 - x) ≤ -x - x ^ 2 / 2` for `0 ≤ x < 1`, from the series of `-log (1 - x)`. -/
theorem log_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) : log (1 - x) ≤ -x - x ^ 2 / 2 := by
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x := x) (by rw [abs_of_nonneg hx0]; exact hx1)
  have h2 := sum_le_hasSum (range 2) (fun i _ ↦ by positivity) hs
  simp [sum_range_succ] at h2
  linarith

/-- **Far enough above the optimum, growth is negative**, for every payout: `g x < 0` when
`0 < x < 1` and `x > 2 b x* / (1 - p)`. -/
theorem logGrowth_neg_of_lt (hp0 : 0 < p) (hp1 : p < 1) (hb : 0 < b) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 1) (h : 2 * b * optimalFraction p b / (1 - p) < x) : logGrowth p b x < 0 := by
  have hu : 0 < 1 + b * x := by nlinarith
  have l1 := Real.log_le_sub_one_of_pos hu
  have l2 := log_one_sub_le hx0.le hx1
  have hq : 0 < 1 - p := by linarith
  have hbx : b * optimalFraction p b = p * b - (1 - p) := by
    unfold optimalFraction; field_simp
  rw [div_lt_iff₀ hq, mul_assoc, hbx] at h
  unfold logGrowth
  nlinarith [mul_le_mul_of_nonneg_left l1 hp0.le, mul_le_mul_of_nonneg_left l2 hq.le,
    mul_pos hx0 hq]

/-- **Half the optimal fraction keeps at least half the optimal growth**:
`g x* / 2 ≤ g (x* / 2)`. -/
theorem half_logGrowth_le (hp0 : 0 < p) (hp1 : p < 1) (hb : 0 < b) :
    logGrowth p b (optimalFraction p b) / 2 ≤ logGrowth p b (optimalFraction p b / 2) := by
  have hU : 0 < 1 + b * optimalFraction p b := by
    rw [one_add_mul_optimalFraction hb]; positivity
  have hV : 0 < 1 - optimalFraction p b := by
    rw [one_sub_optimalFraction hb]; exact one_sub_optimalFraction_pos hp1 hb
  have conc := strictConcaveOn_log_Ioi.concaveOn
  have c1 := conc.2 (Set.mem_Ioi.mpr one_pos) (Set.mem_Ioi.mpr hU)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have c2 := conc.2 (Set.mem_Ioi.mpr one_pos) (Set.mem_Ioi.mpr hV)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at c1 c2
  have e1 : 1 / 2 * 1 + 1 / 2 * (1 + b * optimalFraction p b) =
      1 + b * (optimalFraction p b / 2) := by
    ring
  have e2 : 1 / 2 * 1 + 1 / 2 * (1 - optimalFraction p b) = 1 - optimalFraction p b / 2 := by ring
  rw [e1] at c1
  rw [e2] at c2
  unfold logGrowth
  nlinarith [mul_le_mul_of_nonneg_left c1 hp0.le,
    mul_le_mul_of_nonneg_left c2 (by linarith : 0 ≤ 1 - p)]

/-- **Gains combine by multiplying**: the log of the total growth factor is the sum of the logs of
the per-step factors. This is Mathlib's `Real.log_prod`, restated for positive factors. -/
theorem log_prod_growth {ι : Type*} (s : Finset ι) {f : ι → ℝ} (hf : ∀ i ∈ s, 0 < f i) :
    log (∏ i ∈ s, f i) = ∑ i ∈ s, log (f i) :=
  Real.log_prod fun i hi ↦ (hf i hi).ne'

/-- **A rise of `r` followed by a fall of `r` loses**: `(1 + r) (1 - r) < 1` for `r ≠ 0`. -/
theorem one_add_mul_one_sub_lt_one {r : ℝ} (hr : r ≠ 0) : (1 + r) * (1 - r) < 1 := by
  nlinarith [sq_pos_of_ne_zero hr]

/-- The same in log form: `log (1 + r) + log (1 - r) < 0` for `0 < |r| < 1`. -/
theorem log_one_add_add_log_one_sub_neg {r : ℝ} (hr : r ≠ 0) (hr1 : |r| < 1) :
    log (1 + r) + log (1 - r) < 0 := by
  have h1 : 0 < 1 + r := by linarith [neg_abs_le r]
  have h2 : 0 < 1 - r := by linarith [le_abs_self r]
  rw [← Real.log_mul h1.ne' h2.ne']
  exact Real.log_neg (by positivity) (one_add_mul_one_sub_lt_one hr)

end ClassicalLean.Analysis.LogGrowthRobustness
