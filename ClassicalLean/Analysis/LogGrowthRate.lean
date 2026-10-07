/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Proportional deductions and the log-optimal fraction

Three pieces of elementary arithmetic about repeated proportional changes.

* **Two proportional deductions.** Exchange an amount `W` at rate `a`, losing a fraction `f`, then
  exchange back at rate `c`, losing `f` again: the result is
  `afterTwoDeductions f a c W = W / a * (1 - f) * c * (1 - f)`, and it exceeds `W` exactly when
  `a < c * (1 - f) ^ 2` (`lt_afterTwoDeductions_iff`, for `0 < W` and `0 < a`; no condition on
  `f` is needed for the equivalence).
* **The log-optimal fraction.** For `0 < p < 1` and `0 < b`, the function
  `logGrowth p b x = p * log (1 + b * x) + (1 - p) * log (1 - x)` is the expected logarithm of the
  factor by which a quantity changes when a fraction `x` of it gains `b` times itself with
  probability `p` and is lost otherwise. On `0 ≤ x < 1` it is largest at
  `optimalFraction p b = p - (1 - p) / b` whenever that lies in the interval
  (`logGrowth_le_optimalFraction`, `optimalFraction_mem_Ico`), and some `x` in the interval makes
  it positive exactly when `1 - p < p * b` (`exists_logGrowth_pos_iff`). This is the classical
  result of J. L. Kelly (1956), often called the Kelly criterion.
* **Repeated decrease.** Removing the fraction `x` of what is left, `n` times, leaves
  `W * (1 - x) ^ n` (`repeatedDecrease_eq`).

The definitions are stated over an arbitrary field, so that they compute exactly on `ℚ` (`#eval`);
the inequalities are stated over `ℝ`.

## Method

The two inequalities about `logGrowth` come from `Real.log_le_sub_one_of_pos` (`log y ≤ y - 1`)
and its strict form, applied to the ratios `(1 + b x) / (1 + b x*)` and `(1 - x) / (1 - x*)`. At
`x* = p - (1 - p) / b` one has `1 + b x* = p (1 + b)` and `1 - x* = (1 - p) (1 + b) / b`, and the
weighted sum of the two ratios is then exactly `1`, which is what makes `x*` the maximiser.

## What Mathlib provides

Searched at Mathlib v4.34.0: no statement of these three results under any name (`Kelly` occurs
only in category-theory citations; no break-even lemma). Mathlib supplies the ingredients:
`Real.log_le_sub_one_of_pos`, `Real.log_lt_sub_one_of_pos`, `Real.log_div`, `Real.log_one`.
-/

namespace ClassicalLean.Analysis.LogGrowthRate

section Field

variable {K : Type*} [Field K]

/-- Exchange `W` at rate `a` losing the fraction `f`, then back at rate `c` losing `f` again. -/
def afterTwoDeductions (f a c W : K) : K := W / a * (1 - f) * c * (1 - f)

/-- The log-optimal fraction `p - (1 - p) / b`. -/
def optimalFraction (p b : K) : K := p - (1 - p) / b

/-- Remove the fraction `x` of what is left, `n` times, starting from `W`. -/
def repeatedDecrease (W x : K) : ℕ → K
  | 0 => W
  | n + 1 => repeatedDecrease W x n - x * repeatedDecrease W x n

/-- **Repeated decrease.** After `n` removals of the fraction `x`, `W * (1 - x) ^ n` is left. -/
theorem repeatedDecrease_eq (W x : K) (n : ℕ) : repeatedDecrease W x n = W * (1 - x) ^ n := by
  induction n with
  | zero => simp [repeatedDecrease]
  | succ n ih => rw [repeatedDecrease, ih, pow_succ]; ring

end Field

example : afterTwoDeductions (6 / 1000 : ℚ) 100 102 1000 = 12597459 / 12500 := by
  norm_num [afterTwoDeductions]

example : optimalFraction (55 / 100 : ℚ) 1 = 1 / 10 := by norm_num [optimalFraction]

example : repeatedDecrease (1000 : ℚ) (1 / 10) 5 = 59049 / 100 := by
  norm_num [repeatedDecrease]

/-- **Two proportional deductions.** The round trip gains exactly when `a < c * (1 - f) ^ 2`. -/
theorem lt_afterTwoDeductions_iff {f a c W : ℝ} (hW : 0 < W) (ha : 0 < a) :
    W < afterTwoDeductions f a c W ↔ a < c * (1 - f) ^ 2 := by
  have h : afterTwoDeductions f a c W = W * (c * (1 - f) ^ 2) / a := by
    unfold afterTwoDeductions; field_simp
  rw [h, lt_div_iff₀ ha]
  constructor
  · intro h1; nlinarith
  · intro h1; nlinarith

/-- The expected logarithm of the growth factor when the fraction `x` gains `b` times itself with
probability `p` and is lost otherwise. -/
noncomputable def logGrowth (p b x : ℝ) : ℝ :=
  p * Real.log (1 + b * x) + (1 - p) * Real.log (1 - x)

theorem logGrowth_zero (p b : ℝ) : logGrowth p b 0 = 0 := by simp [logGrowth]

section Optimal

variable {p b : ℝ}

theorem one_add_mul_optimalFraction (hb : 0 < b) :
    1 + b * optimalFraction p b = p * (1 + b) := by
  unfold optimalFraction; field_simp; ring

theorem one_sub_optimalFraction (hb : 0 < b) :
    1 - optimalFraction p b = (1 - p) * (1 + b) / b := by
  unfold optimalFraction; field_simp; ring

theorem optimalFraction_lt_one (hp1 : p < 1) (hb : 0 < b) : optimalFraction p b < 1 := by
  have h := one_sub_optimalFraction (p := p) hb
  have : 0 < (1 - p) * (1 + b) / b := by
    apply div_pos _ hb; nlinarith
  linarith

theorem optimalFraction_nonneg_iff (hb : 0 < b) :
    0 ≤ optimalFraction p b ↔ 1 - p ≤ p * b := by
  unfold optimalFraction
  rw [sub_nonneg, div_le_iff₀ hb]

theorem optimalFraction_pos_iff (hb : 0 < b) :
    0 < optimalFraction p b ↔ 1 - p < p * b := by
  unfold optimalFraction
  rw [sub_pos, div_lt_iff₀ hb]

/-- The log-optimal fraction lies in `[0, 1)` when `1 - p ≤ p * b`. -/
theorem optimalFraction_mem_Ico (hp1 : p < 1) (hb : 0 < b) (h : 1 - p ≤ p * b) :
    optimalFraction p b ∈ Set.Ico 0 1 :=
  ⟨(optimalFraction_nonneg_iff hb).mpr h, optimalFraction_lt_one hp1 hb⟩

/-- The bound behind both main inequalities: for `x` with `1 + b x > 0` and `1 - x > 0`,
`logGrowth p b x - logGrowth p b x*` is at most the weighted sum of `ratio - 1`, which is `0`. -/
private theorem logGrowth_sub_le (hp0 : 0 < p) (hp1 : p < 1) (hb : 0 < b) {x : ℝ}
    (hu : 0 < 1 + b * x) (hv : 0 < 1 - x) :
    logGrowth p b x - logGrowth p b (optimalFraction p b) ≤
      p * ((1 + b * x) / (p * (1 + b)) - 1) +
        (1 - p) * ((1 - x) / ((1 - p) * (1 + b) / b) - 1) := by
  have hU : 0 < p * (1 + b) := by positivity
  have hV : 0 < (1 - p) * (1 + b) / b := by
    apply div_pos _ hb; nlinarith
  have l1 := Real.log_le_sub_one_of_pos (div_pos hu hU)
  have l2 := Real.log_le_sub_one_of_pos (div_pos hv hV)
  rw [Real.log_div hu.ne' hU.ne'] at l1
  rw [Real.log_div hv.ne' hV.ne'] at l2
  unfold logGrowth
  rw [one_add_mul_optimalFraction hb, one_sub_optimalFraction hb]
  nlinarith [mul_le_mul_of_nonneg_left l1 hp0.le,
    mul_le_mul_of_nonneg_left l2 (by linarith : 0 ≤ 1 - p)]

private theorem weighted_ratio_sum (hp0 : 0 < p) (hp1 : p < 1) (hb : 0 < b) (x : ℝ) :
    p * ((1 + b * x) / (p * (1 + b)) - 1) +
        (1 - p) * ((1 - x) / ((1 - p) * (1 + b) / b) - 1) = 0 := by
  have : (1 - p) ≠ 0 := by linarith
  have : (1 + b) ≠ 0 := by linarith
  field_simp
  ring

/-- **The log-optimal fraction is a maximiser.** For `0 < p < 1`, `0 < b` and every `x` with
`0 ≤ x < 1`, `logGrowth p b x ≤ logGrowth p b (p - (1 - p) / b)`. (The bound holds for every such
`x` whether or not `x*` itself lies in `[0, 1)`; `optimalFraction_mem_Ico` says when it does.) -/
theorem logGrowth_le_optimalFraction (hp0 : 0 < p) (hp1 : p < 1) (hb : 0 < b) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    logGrowth p b x ≤ logGrowth p b (optimalFraction p b) := by
  have hu : 0 < 1 + b * x := by nlinarith
  have hv : 0 < 1 - x := by linarith
  have := logGrowth_sub_le hp0 hp1 hb hu hv
  rw [weighted_ratio_sum hp0 hp1 hb x] at this
  linarith

/-- When `1 - p < p * b` the largest value is positive: `0 < logGrowth p b x*`. -/
theorem logGrowth_optimalFraction_pos (hp0 : 0 < p) (hp1 : p < 1) (hb : 0 < b)
    (h : 1 - p < p * b) : 0 < logGrowth p b (optimalFraction p b) := by
  have hU : 0 < p * (1 + b) := by positivity
  have hV : 0 < (1 - p) * (1 + b) / b := by
    apply div_pos _ hb; nlinarith
  -- strict `log y < y - 1` at `y = 1 / (p (1 + b))`, which is not `1` because `p b ≠ 1 - p`
  have hne : 1 / (p * (1 + b)) ≠ 1 := by
    intro h1
    rw [div_eq_one_iff_eq hU.ne'] at h1
    linarith
  have l1 := Real.log_lt_sub_one_of_pos (div_pos one_pos hU) hne
  have l2 := Real.log_le_sub_one_of_pos (div_pos one_pos hV)
  rw [Real.log_div one_ne_zero hU.ne'] at l1
  rw [Real.log_div one_ne_zero hV.ne'] at l2
  have hsum := weighted_ratio_sum hp0 hp1 hb 0
  simp only [mul_zero, add_zero, sub_zero] at hsum
  unfold logGrowth
  rw [one_add_mul_optimalFraction hb, one_sub_optimalFraction hb]
  simp only [Real.log_one, zero_sub] at l1 l2
  nlinarith [mul_lt_mul_of_pos_left l1 hp0, mul_le_mul_of_nonneg_left l2 (by linarith : 0 ≤ 1 - p)]

/-- **Some fraction in `[0, 1)` has positive log growth exactly when `1 - p < p * b`.** -/
theorem exists_logGrowth_pos_iff (hp0 : 0 < p) (hp1 : p < 1) (hb : 0 < b) :
    (∃ x, 0 ≤ x ∧ x < 1 ∧ 0 < logGrowth p b x) ↔ 1 - p < p * b := by
  constructor
  · rintro ⟨x, hx0, hx1, hpos⟩
    by_contra hle
    push Not at hle
    have hu : 0 < 1 + b * x := by nlinarith
    have hv : 0 < 1 - x := by linarith
    have l1 := Real.log_le_sub_one_of_pos hu
    have l2 := Real.log_le_sub_one_of_pos hv
    unfold logGrowth at hpos
    nlinarith [mul_le_mul_of_nonneg_left l1 hp0.le,
      mul_le_mul_of_nonneg_left l2 (by linarith : 0 ≤ 1 - p),
      mul_nonneg hx0 (by linarith : 0 ≤ 1 - p - p * b)]
  · intro h
    exact ⟨optimalFraction p b, ((optimalFraction_pos_iff hb).mpr h).le,
      optimalFraction_lt_one hp1 hb, logGrowth_optimalFraction_pos hp0 hp1 hb h⟩

end Optimal

end ClassicalLean.Analysis.LogGrowthRate
