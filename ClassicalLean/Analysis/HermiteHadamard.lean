/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule


/-!
# The Hermite–Hadamard inequality, and the trapezoidal rule for a convex function

For `f` convex and continuous on `[a, b]` with `a < b`, the average of `f` over `[a, b]` lies
between its value at the midpoint and the average of its two end values:

    f ((a + b) / 2) ≤ (1 / (b - a)) ∫ f ≤ (f a + f b) / 2.

* `convexOn_midpoint_le_average` — the left half. It is Jensen's inequality for the uniform
  measure on `[a, b]`, Mathlib's `ConvexOn.map_set_average_le` with the identity function, whose
  average over `[a, b]` is the midpoint; it is derived from Mathlib's theorem here, not proved
  again.
* `integral_le_mul_add_div_two_of_convexOn` — the right half multiplied out,
  `∫ f ≤ (b - a) (f a + f b) / 2`, for `a ≤ b` (so `a = b` is allowed). Convexity gives
  `f x + f (a + b - x) ≤ f a + f b` on `[a, b]`, and the two terms on the left have the same
  integral.
* `average_le_convexOn_endpoints` — the right half as an average, for `a < b`.
* `integral_le_trapezoidal_integral` — so the trapezoidal rule never under-estimates the integral
  of a convex function: for `a ≤ b` and `N > 0` trapezoids, `∫ f ≤ trapezoidal_integral f N a b`
  (Mathlib's definition). Each trapezoid is the right half on its own piece, summed with
  Mathlib's `sum_trapezoidal_integral_adjacent_intervals` and `sum_integral_adjacent_intervals`.

## Hypotheses

Measured in order LEAN-18's checks (check C12 and C13, exact rationals): both halves hold on 3000
convex cases (quadratics and `|x - c|`), and the trapezoidal bound on the same cases, with one
`N` drawn from `1` to `12` for each. Each hypothesis below fails when dropped alone:

* `a < b`: at `a = b = 0` the average is `0`, so `f = 1` breaks the left half and `f = -1` the
  right. For the multiplied form and the trapezoidal rule, `a ≤ b`: at `a = 1`, `b = 0`, `f = x²`
  the integral `-1/3` is above `-1/2`, which is both `(b - a) (f a + f b) / 2` and the
  one-trapezoid value.
* convexity: `f = -x²` on `[0, 1]` gives `-1/4 > -1/3` on the left, `-1/3 > -1/2` on the right,
  and `-1/3 > -1/2` for one trapezoid.
* `0 < N`: Mathlib's `trapezoidal_integral f 0 a b` is `0` (division by `0`), below `∫ 1 = 1` on
  `[0, 1]`.

Continuity is not shown needed, and is believed removable (not proved here): a convex function
on `[a, b]` is continuous inside it and bounded, so integrable, and the inequalities should stay
true for one that jumps up at an end point; the checks tried only continuous functions. It is
used here for integrability and because Mathlib's Jensen inequality asks for it.

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-18, `grep -rniE` over Mathlib):
`hermite.?hadamard` 0; `ConvexOn.*trapezoid|trapezoid.*ConvexOn|convex.*trapezoid` 0; the shapes
`(f a + f b) / 2` and `(a + b) / 2` next to an integral, 1 hit, the definition of
`trapezoidal_integral`. Mathlib has Jensen's inequality (`Analysis/Convex/Integral.lean`) and the
trapezoidal rule's error bound from the second derivative (`trapezoidal_error_le`,
`MeasureTheory/Integral/IntervalIntegral/TrapezoidalRule.lean`), not its sign for convex `f`.
-/

open MeasureTheory Set intervalIntegral Finset
open scoped Interval

namespace ClassicalLean.Analysis

/-- **Hermite–Hadamard, left half.** For `f` convex and continuous on `[a, b]` with `a < b`, the
value at the midpoint is at most the average of `f` over `[a, b]`. Jensen's inequality for the
uniform measure on `[a, b]`, Mathlib's `ConvexOn.map_set_average_le`, applied to the identity. -/
theorem convexOn_midpoint_le_average {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ConvexOn ℝ (Icc a b) f) (hfc : ContinuousOn f (Icc a b)) :
    f ((a + b) / 2) ≤ (b - a)⁻¹ * ∫ x in a..b, f x := by
  have hI : Ι a b = Ioc a b := uIoc_of_le hab.le
  have hJ := hf.map_set_average_le (μ := volume) (t := Ι a b) (f := id) hfc isClosed_Icc
    (by rw [hI, Real.volume_Ioc]; simpa using hab)
    (by rw [hI, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (ae_restrict_of_forall_mem measurableSet_uIoc fun x hx ↦ by
      rw [hI] at hx; exact Ioc_subset_Icc_self hx)
    (by rw [hI]; exact (continuous_id.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
    (by rw [hI]; exact (hfc.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
  have hmid : (⨍ x in a..b, id x) = (a + b) / 2 := by
    rw [interval_average_eq]
    simp only [id, integral_id, smul_eq_mul]
    field_simp [(sub_pos.mpr hab).ne']
    ring
  rw [hmid, interval_average_eq, smul_eq_mul] at hJ
  exact hJ

/-- **Hermite–Hadamard, right half, multiplied out.** For `f` convex and continuous on `[a, b]`
with `a ≤ b`, `∫ f ≤ (b - a) (f a + f b) / 2`: the integral is at most that of the chord. -/
theorem integral_le_mul_add_div_two_of_convexOn {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ConvexOn ℝ (Icc a b) f) (hfc : ContinuousOn f (Icc a b)) :
    ∫ x in a..b, f x ≤ (b - a) * ((f a + f b) / 2) := by
  have hfi : IntervalIntegrable f volume a b := hfc.intervalIntegrable_of_Icc hab
  have hgi : IntervalIntegrable (fun x ↦ f (a + b - x)) volume a b := by
    have := hfi.comp_sub_left (a + b)
    simpa using this.symm
  -- `f x + f (a + b - x) ≤ f a + f b` on `[a, b]`
  have hpair : ∀ x ∈ Icc a b, f x + f (a + b - x) ≤ f a + f b := by
    intro x hx
    rcases hab.eq_or_lt with rfl | hlt
    · have : x = a := le_antisymm hx.2 hx.1
      subst this; simp
    have hba : 0 < b - a := sub_pos.mpr hlt
    set t := (x - a) / (b - a)
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hx.1) hba.le
    have ht1 : t ≤ 1 := (div_le_one hba).mpr (by linarith [hx.2])
    have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
    have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
    have h1 := hf.2 ha hb (sub_nonneg.mpr ht1) ht0 (by ring)
    have h2 := hf.2 ha hb ht0 (sub_nonneg.mpr ht1) (by ring)
    have e1 : (1 - t) • a + t • b = x := by
      simp only [smul_eq_mul, t]; field_simp; ring
    have e2 : t • a + (1 - t) • b = a + b - x := by
      simp only [smul_eq_mul, t]; field_simp; ring
    rw [e1] at h1
    rw [e2] at h2
    simp only [smul_eq_mul] at h1 h2
    linarith
  have hsym : ∫ x in a..b, f (a + b - x) = ∫ x in a..b, f x := by
    rw [integral_comp_sub_left]; congr 1 <;> ring
  have hmono := integral_mono_on hab (hfi.add hgi) intervalIntegrable_const hpair
  rw [integral_add hfi hgi, hsym, intervalIntegral.integral_const, smul_eq_mul] at hmono
  linarith

/-- **Hermite–Hadamard, right half.** For `f` convex and continuous on `[a, b]` with `a < b`, the
average of `f` over `[a, b]` is at most the average of its two end values. -/
theorem average_le_convexOn_endpoints {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ConvexOn ℝ (Icc a b) f) (hfc : ContinuousOn f (Icc a b)) :
    (b - a)⁻¹ * ∫ x in a..b, f x ≤ (f a + f b) / 2 := by
  have hba : 0 < b - a := sub_pos.mpr hab
  rw [inv_mul_le_iff₀ hba]
  exact integral_le_mul_add_div_two_of_convexOn hab.le hf hfc

/-- **The trapezoidal rule over-estimates a convex integral.** For `f` convex and continuous on
`[a, b]` with `a ≤ b`, and any number `N > 0` of trapezoids of equal width, the integral of `f` is
at most Mathlib's `trapezoidal_integral f N a b`. -/
theorem integral_le_trapezoidal_integral {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ConvexOn ℝ (Icc a b) f) (hfc : ContinuousOn f (Icc a b)) {N : ℕ} (hN : 0 < N) :
    ∫ x in a..b, f x ≤ trapezoidal_integral f N a b := by
  set h := (b - a) / N with hh
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hh0 : 0 ≤ h := div_nonneg (sub_nonneg.mpr hab) hN'.le
  have hb : a + N * h = b := by rw [hh]; field_simp; ring
  -- the points `a + k h`, `k ≤ N`, lie in `[a, b]`
  have hmem : ∀ k : ℕ, k ≤ N → a + k * h ∈ Icc a b := fun k hk ↦ by
    refine ⟨le_add_of_nonneg_right (mul_nonneg k.cast_nonneg hh0), ?_⟩
    rw [← hb]
    have := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk : (k : ℝ) ≤ N) hh0
    linarith
  have hsub : ∀ k < N, Icc (a + k * h) (a + (k + 1) * h) ⊆ Icc a b := fun k hk ↦ by
    have h1 := hmem k hk.le
    have h2 := hmem (k + 1) hk
    push_cast at h2
    exact Icc_subset_Icc h1.1 h2.2
  have hle : ∀ k : ℕ, a + k * h ≤ a + (k + 1) * h := fun k ↦ by nlinarith
  have hint : ∀ k < N, IntervalIntegrable f volume (a + k * h) (a + (k + 1 : ℕ) * h) := by
    intro k hk
    push_cast
    exact (hfc.mono (hsub k hk)).intervalIntegrable_of_Icc (hle k)
  have hsumI := sum_integral_adjacent_intervals (a := fun k : ℕ ↦ a + k * h) hint
  have hsumT := sum_trapezoidal_integral_adjacent_intervals (f := f) (a := a) (h := h) hN
  simp only [Nat.cast_zero, zero_mul, add_zero] at hsumI
  rw [hb] at hsumI hsumT
  rw [← hsumI, ← hsumT]
  refine Finset.sum_le_sum fun k hk ↦ ?_
  have hk := Finset.mem_range.mp hk
  rw [trapezoidal_integral_one]
  push_cast
  have := integral_le_mul_add_div_two_of_convexOn (hle k) (hf.subset (hsub k hk) (convex_Icc _ _))
    (hfc.mono (hsub k hk))
  linarith

end ClassicalLean.Analysis
