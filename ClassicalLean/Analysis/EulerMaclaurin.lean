/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.ZetaValues

/-!
# Euler–Maclaurin, first order

A sum `f a + f (a + 1) + ⋯ + f b` over the integers from `a` to `b` is close to `∫ₐᵇ f`; the
Euler–Maclaurin formula says how close. To first order the correction is the trapezoid's
`(f a + f b)/2` plus an integral of `f'` against the *sawtooth* `t ↦ fract t − 1/2` (`fract t` is
`t` minus the largest integer at most `t`).

* `sawtooth`, `sawtooth_eq_periodizedBernoulli` — the sawtooth is Mathlib's `periodizedBernoulli 1`,
  the first Bernoulli polynomial `x − 1/2` made periodic, at every point.
* `sum_eq_integral_add` — order LEAN-23, item 49: for integers `a ≤ b` (negative ones too), `f`
  continuous on `[a, b]` with derivative `f'` at every inner point and `f'` integrable,
  `∑_{k=a}^{b} f k = ∫ₐᵇ f + (f a + f b)/2 + ∫ₐᵇ sawtooth · f'`.
* `abs_sum_sub_integral_le` — so the sum differs from `∫ₐᵇ f + (f a + f b)/2` by at most
  `(∫ₐᵇ |f'|)/2`, since `|sawtooth| ≤ 1/2`.
* `integral_sawtooth_mul_unit` — the step: on `[k, k + 1]` the sawtooth is `t − k − 1/2` except
  at `k + 1`, and one integration by parts gives
  `∫ₖᵏ⁺¹ sawtooth · f' = (f k + f (k + 1))/2 − ∫ₖᵏ⁺¹ f`.
  The formula follows by induction on `b`, one unit interval at a time.

## Hypotheses

Measured in order LEAN-23's checks (`checks.py`, exact rationals): the formula on 300 random
polynomials of degree at most 5 with integer `a ≤ b` in `[−8, 14]`, and `t²` on `[0, 1]`
(remainder `1/6`) and on `[−1, 1]` (`2 = 2/3 + 1 + 1/3`); the bound on the same 300 (with `∫ |f'|`
by a midpoint rule, floating point). Dropping a hypothesis: with `a > b` the sum over the empty
range is `0`, and `f = 1`, `a = 2`, `b = 0` gives right side `−1` (only `b = a − 1` escapes);
for `f = 1` on `[0, 1/2]` the sum over the integers there is `1`, the formula `3/2`; without
continuity at an end, `f = 0` on `[0, 1)` with `f 1 = 1` and `f' = 0` gives `1` against `1/2`;
if `f'` is not `f`'s derivative inside, `f = t²` on `[0, 1]` with `f' = 0` gives `1` against
`5/6` (review r49). The derivative hypothesis is sufficient, not minimal: the formula also holds
for `f` with corners, such as `|t − 1/2|`, which this statement does not cover. Integrability of
`f'` is needed because Lean's integral of a non-integrable function is `0`: for `t² sin(1/t²)`
on `[0, 1]` (`f'` not integrable near `0`) the left side is `sin 1 ≈ 0.8415` and the right side
with Lean's `0` is `≈ 0.6396` (floating point).

Citations: Euler 1738, "Methodus generalis summandi progressiones"; Maclaurin 1742, "A Treatise
of Fluxions". Neither was read for this file.

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-23, `grep -rniE` over Mathlib, case ignored):
`euler.?maclaurin` 0 lines; `sum_eq_integral|periodi[sz]ed` 9 lines in 1 file
(`NumberTheory/ZetaValues.lean`: the periodised Bernoulli functions and their Fourier
coefficients, no summation formula); `sawtooth` 0. Related and not used: Abel's summation formula
(`sum_mul_eq_sub_sub_integral_mul`, `NumberTheory/AbelSummation.lean`), which sums over natural
numbers (`0 ≤ a`) with `DifferentiableAt` on `Icc a b` and `deriv f`; the trapezoidal rule's
error bound (`MeasureTheory/Integral/IntervalIntegral/TrapezoidalRule.lean`); sum–integral
comparisons for monotone functions (`Analysis/SumIntegralComparisons.lean`) (review r49). Main
lemmas used:
`integral_mul_deriv_eq_deriv_mul_of_hasDerivAt`, `integral_congr_Ioo_of_le`,
`integral_add_adjacent_intervals`, `Integrable.bdd_mul`, `AddCircle.liftIco_coe_apply`,
`bernoulliFun_one`, `Finset.insert_Icc_right_eq_Icc_add_one`, `Int.leInduction`.
-/

open Set Finset intervalIntegral MeasureTheory

namespace ClassicalLean

/-- The sawtooth `t ↦ fract t − 1/2`: the first Bernoulli polynomial `x − 1/2` on `[0, 1)`,
repeated with period `1`. It jumps from `1/2` to `−1/2` at each integer. -/
noncomputable def sawtooth (t : ℝ) : ℝ := Int.fract t - 1 / 2

/-- The sawtooth is Mathlib's periodised Bernoulli function of order `1`, at every point. -/
theorem sawtooth_eq_periodizedBernoulli (t : ℝ) :
    sawtooth t = periodizedBernoulli 1 (t : UnitAddCircle) := by
  have h : ((t : ℝ) : UnitAddCircle) = ((Int.fract t : ℝ) : UnitAddCircle) := by
    rw [← Int.floor_add_fract t, AddCircle.coe_add]
    simp [Int.floor_add_fract]
  rw [h, periodizedBernoulli, AddCircle.liftIco_coe_apply
    (by simp [Int.fract_nonneg, Int.fract_lt_one]), bernoulliFun_one, sawtooth]

/-- The sawtooth lies in `[−1/2, 1/2]`. -/
theorem abs_sawtooth_le (t : ℝ) : |sawtooth t| ≤ 1 / 2 := by
  rw [sawtooth, abs_le]
  constructor <;> linarith [Int.fract_nonneg t, Int.fract_lt_one t]

/-- The sawtooth is measurable. -/
theorem measurable_sawtooth : Measurable sawtooth :=
  (measurable_fract (R := ℝ)).sub_const _

/-- The sawtooth times an integrable function is integrable. -/
theorem intervalIntegrable_sawtooth_mul {g : ℝ → ℝ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun t ↦ sawtooth t * g t) volume a b :=
  ⟨hg.1.bdd_mul measurable_sawtooth.aestronglyMeasurable (ae_of_all _ abs_sawtooth_le),
    hg.2.bdd_mul measurable_sawtooth.aestronglyMeasurable (ae_of_all _ abs_sawtooth_le)⟩

/-- One unit interval: `∫ₖᵏ⁺¹ sawtooth · f' = (f k + f (k + 1))/2 − ∫ₖᵏ⁺¹ f`, by parts. -/
theorem integral_sawtooth_mul_unit {f f' : ℝ → ℝ} (k : ℤ)
    (hf : ContinuousOn f (Icc (k : ℝ) (k + 1)))
    (hf' : ∀ t ∈ Ioo (k : ℝ) (k + 1), HasDerivAt f (f' t) t)
    (hint : IntervalIntegrable f' volume (k : ℝ) (k + 1)) :
    ∫ t in (k : ℝ)..(k + 1), sawtooth t * f' t =
      (f k + f (k + 1)) / 2 - ∫ t in (k : ℝ)..(k + 1), f t := by
  have hkk : (k : ℝ) ≤ k + 1 := by linarith
  rw [integral_congr_Ioo_of_le hkk (g := fun t ↦ (t - k - 1 / 2) * f' t)]
  · rw [integral_mul_deriv_eq_deriv_mul_of_hasDerivAt (u' := fun _ ↦ 1) (by fun_prop)
      (by rwa [uIcc_of_le hkk]) (fun x _ ↦ ((hasDerivAt_id' x).sub_const _).sub_const _)
      (by rwa [min_eq_left hkk, max_eq_right hkk]) intervalIntegrable_const hint]
    simp only [one_mul]
    ring
  · intro t ht
    simp only [sawtooth, Int.fract, Int.floor_eq_iff.mpr ⟨ht.1.le, ht.2⟩]

/-- **Euler–Maclaurin, first order.** For integers `a ≤ b` and `f` continuous on `[a, b]` with
derivative `f'` inside and `f'` integrable,
`∑_{k=a}^{b} f k = ∫ₐᵇ f + (f a + f b)/2 + ∫ₐᵇ sawtooth · f'`. -/
theorem sum_eq_integral_add {f f' : ℝ → ℝ} {a b : ℤ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc (a : ℝ) b))
    (hf' : ∀ t ∈ Ioo (a : ℝ) b, HasDerivAt f (f' t) t)
    (hint : IntervalIntegrable f' volume (a : ℝ) b) :
    ∑ k ∈ Finset.Icc a b, f k =
      (∫ t in (a : ℝ)..b, f t) + (f a + f b) / 2 + ∫ t in (a : ℝ)..b, sawtooth t * f' t := by
  induction b, hab using Int.leInduction with
  | base => simp
  | succ b hab ih =>
    push_cast at hf hf' hint ⊢
    have hb : (a : ℝ) ≤ b := by exact_mod_cast hab
    have hb1 : (b : ℝ) ≤ b + 1 := by linarith
    have hsub : Icc (a : ℝ) b ⊆ Icc (a : ℝ) (b + 1) := Icc_subset_Icc le_rfl hb1
    have hsub' : Icc (b : ℝ) (b + 1) ⊆ Icc (a : ℝ) (b + 1) := Icc_subset_Icc hb le_rfl
    have hI₁ : IntervalIntegrable f' volume (a : ℝ) b :=
      hint.mono_set (by rw [uIcc_of_le hb, uIcc_of_le (hb.trans hb1)]; exact hsub)
    have hI₂ : IntervalIntegrable f' volume (b : ℝ) (b + 1) :=
      hint.mono_set (by rw [uIcc_of_le hb1, uIcc_of_le (hb.trans hb1)]; exact hsub')
    have ih' := ih (hf.mono hsub) (fun t ht ↦ hf' t ⟨ht.1, ht.2.trans (by linarith)⟩) hI₁
    have hu := integral_sawtooth_mul_unit b (hf.mono hsub')
      (fun t ht ↦ hf' t ⟨hb.trans_lt ht.1, ht.2⟩) hI₂
    rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), sum_insert (by simp), ih',
      ← integral_add_adjacent_intervals (b := (b : ℝ))
        ((hf.mono hsub).intervalIntegrable_of_Icc hb)
        ((hf.mono hsub').intervalIntegrable_of_Icc hb1),
      ← integral_add_adjacent_intervals (b := (b : ℝ)) (intervalIntegrable_sawtooth_mul hI₁)
        (intervalIntegrable_sawtooth_mul hI₂), hu]
    push_cast
    ring

/-- The remainder is at most half of `∫ₐᵇ |f'|`, since `|sawtooth| ≤ 1/2`. -/
theorem abs_sum_sub_integral_le {f f' : ℝ → ℝ} {a b : ℤ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc (a : ℝ) b))
    (hf' : ∀ t ∈ Ioo (a : ℝ) b, HasDerivAt f (f' t) t)
    (hint : IntervalIntegrable f' volume (a : ℝ) b) :
    |∑ k ∈ Finset.Icc a b, f k - (∫ t in (a : ℝ)..b, f t) - (f a + f b) / 2| ≤
      (∫ t in (a : ℝ)..b, |f' t|) / 2 := by
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  rw [sum_eq_integral_add hab hf hf' hint, show ∀ x y z : ℝ, x + y + z - x - y = z by
    intros; ring, ← intervalIntegral.integral_div]
  refine (abs_integral_le_integral_abs hab').trans
    (integral_mono_on hab' (intervalIntegrable_sawtooth_mul hint).abs (hint.abs.div_const 2)
      fun t _ ↦ ?_)
  rw [abs_mul]
  calc |sawtooth t| * |f' t| ≤ 1 / 2 * |f' t| := by
        gcongr; exact abs_sawtooth_le t
    _ = |f' t| / 2 := by ring

end ClassicalLean

open Set in
/-- The hypotheses of `sum_eq_integral_add` hold together: the integers from `a = 0` to `b = 3`
(`0 ≤ 3`, four points), `f x = x ^ 2`, continuous, with derivative `f' x = 2 x` at every point,
which is continuous, so integrable on `[0, 3]`. -/
example := ClassicalLean.sum_eq_integral_add (f := fun x ↦ x ^ 2) (f' := fun x ↦ 2 * x)
  (a := 0) (b := 3) (by norm_num) (continuous_pow 2).continuousOn
  (fun t _ ↦ by simpa using hasDerivAt_pow 2 t)
  ((continuous_const.mul continuous_id).intervalIntegrable _ _)
