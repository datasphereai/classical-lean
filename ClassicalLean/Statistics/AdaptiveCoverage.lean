/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Adaptive coverage on any sequence

A forecaster gives, each round, an interval meant to miss the outcome a share `α` of the time.
Round `t` uses a working level `a t` in place of `α`: an interval built to miss with chance
`a t`. After the round, `err t` records the miss (`1`) or the hit (`0`), and the level moves by
`a (t + 1) = a t + γ (α − err t)`: up after a hit, down after a miss. A level at most `0` asks
for an interval that never misses, the whole line, so the round is a hit; a level at least `1`
asks for an interval that always misses, the empty one, so the round is a miss. Order LEAN-26,
item 67 of the plan.

* `abs_mean_err_sub_le`: for `α ∈ [0, 1]`, `γ > 0`, any starting level `a₁` and any `T ≥ 1`,
  the share of misses over the first `T` rounds is within `(max a₁ (1 − a₁) + γ) / (γ T)` of
  `α`.
* `alphaSeq_mem_Icc`: the level stays in `[min a₁ (−γ), max a₁ (1 + γ)]`.
* `alphaSeq_eq`: the level after `T` rounds is `a₁ + γ (T α − ∑_{t < T} err t)` (a telescoping
  sum), which turns the band on the level into the bound on the share of misses.

**What "any sequence" means.** `err : ℕ → ℝ` is any function at all, subject only to the rules of
`IsMissSeq`: every `err t` lies in `[0, 1]`; `err t = 0` whenever `a t ≤ 0`; `err t = 1` whenever
`a t ≥ 1`. Nothing else is assumed: no probability, no independence, no model of the outcomes.
The misses may be chosen by an adversary who sees everything, including the levels, since every
such choice is one function `err`. The levels `a t = alphaSeq α γ a₁ err t` are computed from
`err` by the update above.

The plan asks for `α ∈ (0, 1)`, `err t ∈ {0, 1}` and `a₁ ∈ [0, 1]`; the theorem allows more:
`α` may also be `0` or `1`, `err t` may be anywhere in `[0, 1]` when `0 < a t < 1` (a randomized
interval's chance of missing, say), and the starting level may be any real number. Each
remaining hypothesis is needed (order LEAN-26's checks, lines A1 to A9, exact):

* `γ > 0`: with `γ = 0` the level never moves; `α = 1/10`, `a₁ = 1/2`, `T = 10` and a miss
  every round give `|1 − 1/10| = 9/10` against Lean's `x / 0 = 0`.
* `α ≤ 1`: `α = 2`, `γ = 1`, `a₁ = 0`, `T = 10` gives `11/10 > 1/5`.
* `0 ≤ α`: `α = −1`, `γ = 1`, `a₁ = 1`, `T = 10` gives `11/10 > 1/5`.
* `err t ∈ [0, 1]`: `α = 1/2`, `γ = 1/10`, `a₁ = 1/2`, one round with `err = −10` gives
  `21/2 > 6`; with `err = 10`, `19/2 > 6`.
* the forced hit at `a t ≤ 0`: a miss every round, `α = γ = 1/10`, `a₁ = 1/2`, `T = 100`, gives
  `9/10 > 3/50`.
* the forced miss at `a t ≥ 1`: a hit every round, `α = 9/10`, `γ = 1/10`, `a₁ = 1/2`,
  `T = 100`, gives `9/10 > 3/50`.
* `T ≥ 1`: with `T = 0` and `α = 1/10` the share of misses is Lean's `0 / 0 = 0`, and
  `|0 − 1/10| = 1/10` against Lean's `x / 0 = 0`.

3000 further runs (`α ∈ [0, 1]`, `γ > 0`, starting levels from `−3` to `5`, misses chosen at
random, by a rule that chases `α`, or by a fixed pattern) all met the bound (line A1).

## What Mathlib provides

`Finset.sum_range_succ` and ordered-field arithmetic. Mathlib v4.34.0 has no adaptive
coverage or conformal prediction: `conformal predict|adaptive conformal` gives no hits (order
LEAN-26's search).
-/

open Finset

namespace ClassicalLean.Statistics.AdaptiveCoverage

/-- The level after `t` rounds: `a 0 = a₁`, `a (t + 1) = a t + γ (α − err t)`. -/
def alphaSeq (α γ a₁ : ℝ) (err : ℕ → ℝ) : ℕ → ℝ
  | 0 => a₁
  | t + 1 => alphaSeq α γ a₁ err t + γ * (α - err t)

/-- The rules on the miss sequence: each `err t` lies in `[0, 1]`, it is `0` (a hit) when the
level is at most `0` (the interval is the whole line), and `1` (a miss) when the level is at least
`1` (the interval is empty). -/
structure IsMissSeq (α γ a₁ : ℝ) (err : ℕ → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ err t
  le_one : ∀ t, err t ≤ 1
  eq_zero : ∀ t, alphaSeq α γ a₁ err t ≤ 0 → err t = 0
  eq_one : ∀ t, 1 ≤ alphaSeq α γ a₁ err t → err t = 1

/-- **The level telescopes.** After `T` rounds the level is `a₁ + γ (T α − ∑_{t < T} err t)`. -/
theorem alphaSeq_eq (α γ a₁ : ℝ) (err : ℕ → ℝ) (T : ℕ) :
    alphaSeq α γ a₁ err T = a₁ + γ * (T * α - ∑ t ∈ range T, err t) := by
  induction T with
  | zero => simp [alphaSeq]
  | succ T ih => rw [alphaSeq, ih, sum_range_succ]; push_cast; ring

/-- **The level stays in a band**: `min a₁ (−γ) ≤ a t ≤ max a₁ (1 + γ)` for every round `t`. -/
theorem alphaSeq_mem_Icc {α γ a₁ : ℝ} {err : ℕ → ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hγ : 0 ≤ γ)
    (h : IsMissSeq α γ a₁ err) (t : ℕ) :
    alphaSeq α γ a₁ err t ∈ Set.Icc (min a₁ (-γ)) (max a₁ (1 + γ)) := by
  rw [Set.mem_Icc]
  induction t with
  | zero => exact ⟨min_le_left _ _, le_max_left _ _⟩
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hlo : min a₁ (-γ) ≤ -γ := min_le_right _ _
    have hhi : 1 + γ ≤ max a₁ (1 + γ) := le_max_right _ _
    rw [alphaSeq]
    set a := alphaSeq α γ a₁ err t
    have e0 := h.nonneg t; have e1 := h.le_one t
    rcases le_or_gt a 0 with ha | ha
    · rw [h.eq_zero t ha]
      constructor <;> nlinarith [mul_nonneg hγ hα0, mul_le_mul_of_nonneg_left hα1 hγ]
    rcases le_or_gt 1 a with hb | hb
    · rw [h.eq_one t hb]
      constructor <;> nlinarith [mul_nonneg hγ (sub_nonneg.mpr hα1)]
    constructor <;> nlinarith [mul_nonneg hγ e0, mul_nonneg hγ (sub_nonneg.mpr e1),
      mul_nonneg hγ hα0, mul_nonneg hγ (sub_nonneg.mpr hα1)]

/-- **Adaptive coverage on any sequence.** For every miss sequence that follows the rules, the share
of misses over the first `T ≥ 1` rounds is within `(max a₁ (1 − a₁) + γ) / (γ T)` of `α`. -/
theorem abs_mean_err_sub_le {α γ a₁ : ℝ} {err : ℕ → ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hγ : 0 < γ)
    (h : IsMissSeq α γ a₁ err) {T : ℕ} (hT : 0 < T) :
    |(∑ t ∈ range T, err t) / T - α| ≤ (max a₁ (1 - a₁) + γ) / (γ * T) := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  obtain ⟨h1, h2⟩ := alphaSeq_mem_Icc hα0 hα1 hγ.le h T
  have heq := alphaSeq_eq α γ a₁ err T
  set D := alphaSeq α γ a₁ err T - a₁ with hD
  have hmean : (∑ t ∈ range T, err t) / T - α = -D / (γ * T) := by
    field_simp; rw [hD, heq]; ring
  have hM : 1 / 2 ≤ max a₁ (1 - a₁) := by
    rcases le_total a₁ (1 / 2) with h | h
    · exact le_max_of_le_right (by linarith)
    · exact le_max_of_le_left h
  have hDu : D ≤ max a₁ (1 - a₁) + γ := by
    rcases le_total a₁ (1 + γ) with h | h
    · rw [max_eq_right h] at h2; linarith [le_max_right a₁ (1 - a₁)]
    · rw [max_eq_left h] at h2; linarith
  have hDl : -D ≤ max a₁ (1 - a₁) + γ := by
    rcases le_total a₁ (-γ) with h | h
    · rw [min_eq_left h] at h1; linarith
    · rw [min_eq_right h] at h1; linarith [le_max_left a₁ (1 - a₁)]
  rw [hmean, abs_div, abs_of_pos (mul_pos hγ hT'), abs_neg]
  exact div_le_div_of_nonneg_right (abs_le.mpr ⟨by linarith, hDu⟩) (mul_pos hγ hT').le

end ClassicalLean.Statistics.AdaptiveCoverage

open ClassicalLean.Statistics.AdaptiveCoverage in
/-- The hypotheses of `abs_mean_err_sub_le` hold together: the target miss rate `α = 1/2` in
`[0, 1]`, the step `γ = 2 > 0`, the first level `a₁ = 0`, and the misses `err t = 0` on even
rounds and `1` on odd ones; the level then alternates between `0` and `1`, so on even rounds it is
at most `0` and the rule that the round must then be a hit applies, and on odd rounds it is at
least `1` and the rule that the round must then be a miss applies; `T = 4` rounds. (The model is
the group 11 reviewer's.) -/
example := ClassicalLean.Statistics.AdaptiveCoverage.abs_mean_err_sub_le (α := 1 / 2) (γ := 2)
  (a₁ := 0) (err := fun t ↦ if t % 2 = 0 then 0 else 1) (by norm_num) (by norm_num)
  (by norm_num)
  (by
    have key : ∀ t, alphaSeq (1 / 2) 2 0 (fun t ↦ if t % 2 = 0 then 0 else 1) t =
        if t % 2 = 0 then 0 else 1 := by
      intro t
      induction t with
      | zero => simp [alphaSeq]
      | succ t ih =>
        rw [alphaSeq, ih]
        rcases Nat.mod_two_eq_zero_or_one t with h | h
        · simp [h, Nat.succ_mod_two_eq_one_iff.mpr h]
        · simp [h, Nat.succ_mod_two_eq_zero_iff.mpr h]; norm_num
    refine ⟨fun t ↦ by split_ifs <;> norm_num, fun t ↦ by split_ifs <;> norm_num,
      fun t ht ↦ ?_, fun t ht ↦ ?_⟩
    · rw [key] at ht
      split_ifs at ht with h
      · simp [h]
      · linarith
    · rw [key] at ht
      split_ifs at ht with h
      · linarith
      · simp [h])
  (T := 4) (by norm_num)
