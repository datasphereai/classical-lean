/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Analysis.GeneralGrowth
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.BigOperators.Field

/-!
# The best fraction for a finite list of returns: it exists, and where it lies

Finitely many returns `r i` with chances `q i > 0`. The worst return is `-a < 0`, the best is at
most `b`, the mean is `m = ∑ q i r i` and the second moment is `s₂ = ∑ q i r i ^ 2`. The expected
log growth `growth s q r x = ∑ q i log (1 + x r i)` is considered on `[0, 1/a)`, where every
`1 + x r i` is positive.

* `existsUnique_isMaxOn_growth`: on `[0, 1/a)` the growth has exactly one maximiser `x*`, whatever
  the sign of the mean (for `m ≤ 0` it is `0`).
* `div_le_of_isMaxOn_growth`: if `m ≥ 0`, then `m / (s₂ + a m) ≤ x*`.
* `le_div_of_isMaxOn_growth`: if `m ≥ 0` and `s₂ > b m`, then `x* ≤ m / (s₂ - b m)`.

In words the bounds are `(m/s₂) / (1 + a m/s₂)` and `(m/s₂) / (1 - b m/s₂)`. They are close to
`m/s₂` only when `a m/s₂` and `b m/s₂` are small, not merely when the returns are small: returns
`+e` and `-e` with chances `0.6` and `0.4` give `0.833` and `1.25` times `m/s₂` for every `e`.

The route: the slope `growthSlope x = ∑ q i r i / (1 + x r i)` satisfies
`growth y ≤ growth x + (y - x) · growthSlope x` (from `log t ≤ t - 1`), so a point of slope `0` is
a maximiser. The slope is `m ≥ 0` at `0` and at most `0` at `x₁ = (1 - a w / P) / a < 1/a`, where
`w` is the chance of the worst return and `P` the sum of `q i · max (r i) 0` over the other
outcomes; `intermediate_value_Icc'` gives a zero in between. Uniqueness is
`GeneralGrowth.eq_of_isMaxOn_growth`.

The point `1/a` itself is left out: there `1 + x r i = 0` for the worst return, and Lean's
`log 0 = 0` would make it look better than `x*` (returns `-1` and `+1` with chances `0.01` and
`0.99`: Lean's growth at `x = 1` is `0.686`, against `0.637` at `x* = 0.98`).

Each hypothesis is needed. Without `q i > 0`, a worst return of chance `0` leaves the growth
rising towards `1/a` with no maximiser (returns `-1` and `1/10` with chances `0` and `1`).
Without a negative return the growth keeps rising (return `1/10` or `0` with chance `1/2` each:
`0.048`, `0.35`, `1.20` at `x = 1, 10, 100`). Without `m ≥ 0` the bounds fail: returns `1/2` and
`-1/2` with chances `2/5` and `3/5` give `m = -1/10`, `x* = 0`, upper bound `-1/3`; returns
`-1, -1/2, 1/10` with chances `1/10, 4/5, 1/10` give a lower bound `70/27`, above `1/a = 1`.
Without `s₂ > b m` the upper bound fails too: returns `1/2, 1, -1/100` with chances
`989/1000, 1/1000, 1/100` have `s₂ < b m`, and the bound is negative.
-/

open Real Finset Set
open ClassicalLean.Analysis.GeneralGrowth

namespace ClassicalLean.Analysis.GrowthMaximiser

variable {ι : Type*} (s : Finset ι) (q r : ι → ℝ)

/-- The slope of the growth: `∑ q i r i / (1 + x r i)`. -/
noncomputable def growthSlope (x : ℝ) : ℝ := ∑ i ∈ s, q i * r i / (1 + x * r i)

variable {s q r}

/-- **The tangent line lies above the growth.** Where every `1 + x r i` and `1 + y r i` is
positive, `growth y ≤ growth x + (y - x) · growthSlope x`. -/
theorem growth_le_add_slope (hq : ∀ i ∈ s, 0 ≤ q i) {x y : ℝ} (hx : ∀ i ∈ s, 0 < 1 + x * r i)
    (hy : ∀ i ∈ s, 0 < 1 + y * r i) :
    growth s q r y ≤ growth s q r x + (y - x) * growthSlope s q r x := by
  unfold growth growthSlope
  rw [mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun i hi ↦ ?_
  have hxi := hx i hi
  have hlog := Real.log_le_sub_one_of_pos (div_pos (hy i hi) hxi)
  rw [Real.log_div (hy i hi).ne' hxi.ne'] at hlog
  have e : (1 + y * r i) / (1 + x * r i) - 1 = (y - x) * r i / (1 + x * r i) := by
    rw [div_sub_one hxi.ne']; congr 1; ring
  rw [e] at hlog
  have := mul_le_mul_of_nonneg_left hlog (hq i hi)
  have e2 : (y - x) * (q i * r i / (1 + x * r i)) = q i * ((y - x) * r i / (1 + x * r i)) := by
    ring
  rw [e2]; nlinarith

/-- A point of slope `0` maximises the growth on any set where every `1 + y r i` is positive. -/
theorem isMaxOn_of_growthSlope_eq_zero (hq : ∀ i ∈ s, 0 ≤ q i) {D : Set ℝ}
    (hdom : ∀ y ∈ D, ∀ i ∈ s, 0 < 1 + y * r i) {x : ℝ} (hx : x ∈ D)
    (h0 : growthSlope s q r x = 0) : IsMaxOn (growth s q r) D x := fun y hy ↦ by
  have := growth_le_add_slope hq (hdom x hx) (hdom y hy)
  rw [h0, mul_zero, add_zero] at this
  exact this

section Bracket

variable {a : ℝ} (ha : 0 < a) (hlow : ∀ i ∈ s, -a ≤ r i)
include ha hlow

omit hlow in
lemma one_sub_mul_pos {x : ℝ} (hx : x ∈ Ico 0 (1 / a)) : 0 < 1 - x * a := by
  have := (lt_div_iff₀ ha).mp hx.2; linarith

lemma dom_of_mem_Ico {x : ℝ} (hx : x ∈ Ico 0 (1 / a)) : ∀ i ∈ s, 0 < 1 + x * r i := fun i hi ↦ by
  have h1 := one_sub_mul_pos ha hx
  have : -(x * a) ≤ x * r i := by nlinarith [hlow i hi, hx.1]
  linarith

/-- The slope from below: `m - x s₂ / (1 - x a) ≤ growthSlope x` on `[0, 1/a)`. -/
lemma sub_le_growthSlope (hq : ∀ i ∈ s, 0 ≤ q i) {x : ℝ} (hx : x ∈ Ico 0 (1 / a)) :
    ∑ i ∈ s, q i * r i - x * (∑ i ∈ s, q i * r i ^ 2) / (1 - x * a) ≤ growthSlope s q r x := by
  have h1 := one_sub_mul_pos ha hx
  rw [mul_sum, Finset.sum_div, ← sum_sub_distrib]
  refine sum_le_sum fun i hi ↦ ?_
  have hd := dom_of_mem_Ico ha hlow hx i hi
  have hge : 1 - x * a ≤ 1 + x * r i := by nlinarith [hlow i hi, hx.1]
  have e : q i * r i / (1 + x * r i) = q i * r i - x * (q i * r i ^ 2) / (1 + x * r i) := by
    rw [eq_sub_iff_add_eq, ← add_div, div_eq_iff hd.ne']; ring
  rw [e]
  have hnum : 0 ≤ x * (q i * r i ^ 2) := mul_nonneg hx.1 (mul_nonneg (hq i hi) (sq_nonneg _))
  have := div_le_div_of_nonneg_left hnum h1 hge
  linarith

/-- The slope from above: `growthSlope x ≤ m - x s₂ / (1 + x b)` on `[0, 1/a)` when every
return is at most `b`. -/
lemma growthSlope_le_sub (hq : ∀ i ∈ s, 0 ≤ q i) {b : ℝ} (hup : ∀ i ∈ s, r i ≤ b) {x : ℝ}
    (hx : x ∈ Ico 0 (1 / a)) :
    growthSlope s q r x ≤ ∑ i ∈ s, q i * r i - x * (∑ i ∈ s, q i * r i ^ 2) / (1 + x * b) := by
  rw [mul_sum, Finset.sum_div, ← sum_sub_distrib]
  refine sum_le_sum fun i hi ↦ ?_
  have hd := dom_of_mem_Ico ha hlow hx i hi
  have hle : 1 + x * r i ≤ 1 + x * b := by nlinarith [hup i hi, hx.1]
  have e : q i * r i / (1 + x * r i) = q i * r i - x * (q i * r i ^ 2) / (1 + x * r i) := by
    rw [eq_sub_iff_add_eq, ← add_div, div_eq_iff hd.ne']; ring
  rw [e]
  have hnum : 0 ≤ x * (q i * r i ^ 2) := mul_nonneg hx.1 (mul_nonneg (hq i hi) (sq_nonneg _))
  have := div_le_div_of_nonneg_left hnum hd hle
  linarith

variable {j : ι} (hj : j ∈ s) (hja : r j = -a)
include hj hja

/-- The slope from above by the worst return alone:
`growthSlope x ≤ P - a w / (1 - x a)`, with `w = q j` and `P = ∑_{i ≠ j} q i · max (r i) 0`. -/
lemma growthSlope_le_pos_sub [DecidableEq ι] (hq : ∀ i ∈ s, 0 ≤ q i) {x : ℝ}
    (hx : x ∈ Ico 0 (1 / a)) :
    growthSlope s q r x ≤ ∑ i ∈ s.erase j, q i * max (r i) 0 - a * q j / (1 - x * a) := by
  have h1 := one_sub_mul_pos ha hx
  unfold growthSlope
  rw [← add_sum_erase s _ hj, hja]
  have hterm : ∑ i ∈ s.erase j, q i * r i / (1 + x * r i) ≤
      ∑ i ∈ s.erase j, q i * max (r i) 0 := by
    refine sum_le_sum fun i hi ↦ ?_
    have hi' := mem_of_mem_erase hi
    have hd := dom_of_mem_Ico ha hlow hx i hi'
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (hq i hi')
    rcases le_or_gt 0 (r i) with hr | hr
    · rw [max_eq_left hr, div_le_iff₀ hd]; nlinarith [mul_nonneg (mul_nonneg hx.1 hr) hr]
    · rw [max_eq_right hr.le]; exact (div_neg_of_neg_of_pos hr hd).le
  have e : q j * -a / (1 + x * -a) = -(a * q j / (1 - x * a)) := by
    rw [show 1 + x * -a = 1 - x * a by ring]; ring
  rw [e]; linarith

omit ha hlow in
/-- The mean is at most `P - a w`. -/
lemma mean_le_pos_sub [DecidableEq ι] (hq : ∀ i ∈ s, 0 ≤ q i) :
    ∑ i ∈ s, q i * r i ≤ ∑ i ∈ s.erase j, q i * max (r i) 0 - a * q j := by
  rw [← add_sum_erase s _ hj, hja]
  have : ∑ i ∈ s.erase j, q i * r i ≤ ∑ i ∈ s.erase j, q i * max (r i) 0 :=
    sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left (le_max_left _ _) (hq i (mem_of_mem_erase hi))
  linarith

omit hj hja in
lemma continuousOn_growthSlope {x₁ : ℝ} (hx₁ : x₁ < 1 / a) :
    ContinuousOn (growthSlope s q r) (Icc 0 x₁) := by
  change ContinuousOn (fun x ↦ ∑ i ∈ s, q i * r i / (1 + x * r i)) _
  refine continuousOn_finsetSum _ fun i hi ↦ ?_
  refine ContinuousOn.div continuousOn_const (by fun_prop) fun x hx ↦ ?_
  exact (dom_of_mem_Ico ha hlow ⟨hx.1, hx.2.trans_lt hx₁⟩ i hi).ne'

omit ha hlow hj hja in
lemma growthSlope_zero : growthSlope s q r 0 = ∑ i ∈ s, q i * r i := by
  simp [growthSlope]

/-- With a nonnegative mean, the slope has a zero in `[0, 1/a)`. -/
lemma exists_growthSlope_eq_zero (hq : ∀ i ∈ s, 0 < q i) (hm : 0 ≤ ∑ i ∈ s, q i * r i) :
    ∃ x ∈ Ico 0 (1 / a), growthSlope s q r x = 0 := by
  classical
  have hq0 : ∀ i ∈ s, 0 ≤ q i := fun i hi ↦ (hq i hi).le
  set P := ∑ i ∈ s.erase j, q i * max (r i) 0 with hPdef
  set w := q j with hwdef
  have hw : 0 < w := hq j hj
  have hmean := mean_le_pos_sub hj hja hq0
  have hP : a * w ≤ P := by linarith
  have hPpos : 0 < P := lt_of_lt_of_le (mul_pos ha hw) hP
  have hfrac : a * w / P ≤ 1 := (div_le_one hPpos).mpr hP
  have hfrac0 : 0 < a * w / P := div_pos (mul_pos ha hw) hPpos
  set x₁ := (1 - a * w / P) / a with hx₁def
  have hx₁0 : 0 ≤ x₁ := div_nonneg (by linarith) ha.le
  have hx₁lt : x₁ < 1 / a := div_lt_div_of_pos_right (by linarith) ha
  have h1 : 1 - x₁ * a = a * w / P := by rw [hx₁def, div_mul_cancel₀ _ ha.ne']; ring
  have hslope1 : growthSlope s q r x₁ ≤ 0 := by
    have := growthSlope_le_pos_sub ha hlow hj hja hq0 ⟨hx₁0, hx₁lt⟩
    have e : a * q j / (a * w / P) = P := by
      rw [div_div_eq_mul_div]; exact mul_div_cancel_left₀ P (mul_pos ha hw).ne'
    rw [h1, e] at this
    linarith
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc' hx₁0 (continuousOn_growthSlope ha hlow hx₁lt)
    ⟨hslope1, (growthSlope_zero (s := s) (q := q) (r := r)).symm ▸ hm⟩
  exact ⟨x, ⟨hx.1, hx.2.trans_lt hx₁lt⟩, hx0⟩

/-- **Exactly one best fraction.** With chances `q i > 0`, worst return `-a < 0` (attained at
`j`), the growth `∑ q i log (1 + x r i)` has exactly one maximiser on `[0, 1/a)`. -/
theorem existsUnique_isMaxOn_growth (hq : ∀ i ∈ s, 0 < q i) :
    ∃! x, x ∈ Ico 0 (1 / a) ∧ IsMaxOn (growth s q r) (Ico 0 (1 / a)) x := by
  have hq0 : ∀ i ∈ s, 0 ≤ q i := fun i hi ↦ (hq i hi).le
  have hdom : ∀ y ∈ Ico 0 (1 / a), ∀ i ∈ s, 0 < 1 + y * r i := fun y hy ↦ dom_of_mem_Ico ha hlow hy
  have hnz : ∃ i ∈ s, 0 < q i ∧ r i ≠ 0 :=
    ⟨j, hj, hq j hj, by rw [hja]; exact neg_ne_zero.mpr ha.ne'⟩
  have h0mem : (0 : ℝ) ∈ Ico 0 (1 / a) := ⟨le_rfl, by positivity⟩
  obtain ⟨x, hx, hmax⟩ : ∃ x ∈ Ico 0 (1 / a), IsMaxOn (growth s q r) (Ico 0 (1 / a)) x := by
    rcases le_or_gt 0 (∑ i ∈ s, q i * r i) with hm | hm
    · obtain ⟨x, hx, h0⟩ := exists_growthSlope_eq_zero ha hlow hj hja hq hm
      exact ⟨x, hx, isMaxOn_of_growthSlope_eq_zero hq0 hdom hx h0⟩
    · refine ⟨0, h0mem, fun y hy ↦ ?_⟩
      have := growth_le_add_slope hq0 (hdom 0 h0mem) (hdom y hy)
      rw [growthSlope_zero] at this
      have hneg : (y - 0) * ∑ i ∈ s, q i * r i ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith [hy.1]) hm.le
      change growth s q r y ≤ growth s q r 0
      linarith
  exact ⟨x, ⟨hx, hmax⟩, fun y ⟨hy, hymax⟩ ↦
    eq_of_isMaxOn_growth s q r hq0 (convex_Ico _ _) hdom hnz hy hx hymax hmax⟩

/-- A maximiser on `[0, 1/a)` has slope `0` when the mean is nonnegative. -/
lemma growthSlope_eq_zero_of_isMaxOn (hq : ∀ i ∈ s, 0 < q i) (hm : 0 ≤ ∑ i ∈ s, q i * r i)
    {x : ℝ} (hx : x ∈ Ico 0 (1 / a)) (hmax : IsMaxOn (growth s q r) (Ico 0 (1 / a)) x) :
    growthSlope s q r x = 0 := by
  have hq0 : ∀ i ∈ s, 0 ≤ q i := fun i hi ↦ (hq i hi).le
  have hdom : ∀ y ∈ Ico 0 (1 / a), ∀ i ∈ s, 0 < 1 + y * r i := fun y hy ↦ dom_of_mem_Ico ha hlow hy
  have hnz : ∃ i ∈ s, 0 < q i ∧ r i ≠ 0 :=
    ⟨j, hj, hq j hj, by rw [hja]; exact neg_ne_zero.mpr ha.ne'⟩
  obtain ⟨x₀, hx₀, h0⟩ := exists_growthSlope_eq_zero ha hlow hj hja hq hm
  rw [eq_of_isMaxOn_growth s q r hq0 (convex_Ico _ _) hdom hnz hx hx₀ hmax
    (isMaxOn_of_growthSlope_eq_zero hq0 hdom hx₀ h0)]
  exact h0

omit ha hlow hja in
lemma secondMoment_pos (hq : ∀ i ∈ s, 0 < q i) (hrj : r j ≠ 0) :
    0 < ∑ i ∈ s, q i * r i ^ 2 :=
  lt_of_lt_of_le (mul_pos (hq j hj) (pow_pos (abs_pos.mpr hrj) 2 |>.trans_eq (sq_abs _)))
    (single_le_sum (f := fun i ↦ q i * r i ^ 2)
      (fun i hi ↦ mul_nonneg (hq i hi).le (sq_nonneg _)) hj)

/-- **The best fraction from below.** With a nonnegative mean `m` and second moment `s₂`, the
maximiser on `[0, 1/a)` is at least `m / (s₂ + a m)`. -/
theorem div_le_of_isMaxOn_growth (hq : ∀ i ∈ s, 0 < q i) (hm : 0 ≤ ∑ i ∈ s, q i * r i) {x : ℝ}
    (hx : x ∈ Ico 0 (1 / a)) (hmax : IsMaxOn (growth s q r) (Ico 0 (1 / a)) x) :
    (∑ i ∈ s, q i * r i) / (∑ i ∈ s, q i * r i ^ 2 + a * ∑ i ∈ s, q i * r i) ≤ x := by
  have hq0 : ∀ i ∈ s, 0 ≤ q i := fun i hi ↦ (hq i hi).le
  have h0 := growthSlope_eq_zero_of_isMaxOn ha hlow hj hja hq hm hx hmax
  have hb := sub_le_growthSlope ha hlow hq0 hx
  rw [h0] at hb
  have h1 := one_sub_mul_pos ha hx
  have hs2 := secondMoment_pos (r := r) hj hq (by rw [hja]; exact neg_ne_zero.mpr ha.ne')
  have hden : 0 < ∑ i ∈ s, q i * r i ^ 2 + a * ∑ i ∈ s, q i * r i := by positivity
  have hk : (∑ i ∈ s, q i * r i) * (1 - x * a) ≤ x * ∑ i ∈ s, q i * r i ^ 2 :=
    (le_div_iff₀ h1).mp (by linarith)
  rw [div_le_iff₀ hden]
  nlinarith

/-- **The best fraction from above.** With a nonnegative mean `m`, every return at most `b`, and
`s₂ > b m`, the maximiser on `[0, 1/a)` is at most `m / (s₂ - b m)`. -/
theorem le_div_of_isMaxOn_growth (hq : ∀ i ∈ s, 0 < q i) (hm : 0 ≤ ∑ i ∈ s, q i * r i) {b : ℝ}
    (hup : ∀ i ∈ s, r i ≤ b) (hsb : b * ∑ i ∈ s, q i * r i < ∑ i ∈ s, q i * r i ^ 2) {x : ℝ}
    (hx : x ∈ Ico 0 (1 / a)) (hmax : IsMaxOn (growth s q r) (Ico 0 (1 / a)) x) :
    x ≤ (∑ i ∈ s, q i * r i) / (∑ i ∈ s, q i * r i ^ 2 - b * ∑ i ∈ s, q i * r i) := by
  have hq0 : ∀ i ∈ s, 0 ≤ q i := fun i hi ↦ (hq i hi).le
  have h0 := growthSlope_eq_zero_of_isMaxOn ha hlow hj hja hq hm hx hmax
  have hd := dom_of_mem_Ico ha hlow hx j hj
  have hb1 : 0 < 1 + x * b := by nlinarith [hup j hj, hx.1]
  have hb := growthSlope_le_sub ha hlow hq0 hup hx
  rw [h0] at hb
  have hk : x * ∑ i ∈ s, q i * r i ^ 2 ≤ (∑ i ∈ s, q i * r i) * (1 + x * b) :=
    (div_le_iff₀ hb1).mp (by linarith)
  rw [le_div_iff₀ (by linarith)]
  nlinarith

end Bracket

end ClassicalLean.Analysis.GrowthMaximiser
