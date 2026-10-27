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
* `convexOn_midpoint_mul_integral_le`, `integral_mul_le_endpoints` — order LEAN-36, item 127,
  **Fejér's inequality**: for `f` convex and continuous on `[a, b]` with `a ≤ b`, and a weight
  `g ≥ 0` integrable on `[a, b]` and symmetric about the midpoint,
  `f ((a + b) / 2) ∫ g ≤ ∫ f g ≤ ((f a + f b) / 2) ∫ g`, the two halves stated apart. With `g = 1`
  they are the module's two halves of Hermite–Hadamard, multiplied out. Against the plan's row
  (FAITHFUL): `a ≤ b`, the weight asked to be nonnegative and symmetric only on `[a, b]`, `g`
  integrable on `[a, b]` (the row's `∫ g` presumes it), and `f` continuous on `[a, b]` added, as
  this module's own theorems ask (not shown needed: see Hypotheses). The proofs are the draft
  `d127-r1-s2` (written by Claude Opus 5.5 through the Anthropic Batch API, the lane's API-CREDIT-1
  work), placed by order LEAN-36's session inside this namespace, the draft's import line, module
  docstring and `open` lines left out (this module's `open` lines cover them), its two docstrings
  rewritten; its proofs unchanged. The session did not drop-test their hypotheses; order LEAN-36's
  review (a) did, outside the library: `a ≤ b`, convexity, `g ≥ 0` and the symmetry each fail when
  dropped (in Lean); the integrability of `g` judged needed and the continuity of `f` judged
  removable, not checked in Lean. The two witnesses are claude-ai's (lane
  `lean/LEAN-36/data/witnesses.txt`, section HermiteHadamard), with the theorems called by their
  full names.

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

/-- For `f` convex on `[a, b]`, `f x + f (a + b - x) ≤ f a + f b` on `[a, b]`. -/
private lemma fejer_pair_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ConvexOn ℝ (Icc a b) f) :
    ∀ x ∈ Icc a b, f x + f (a + b - x) ≤ f a + f b := by
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

/-- The product `f g` is integrable on `[a, b]`. -/
private lemma fejer_integrable {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfc : ContinuousOn f (Icc a b)) (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun x => f x * g x) volume a b :=
  hg.continuousOn_mul (by rwa [uIcc_of_le hab])

/-- The reflected product `x ↦ f (a + b - x) g (a + b - x)` is integrable on `[a, b]`. -/
private lemma fejer_integrable_refl {f g : ℝ → ℝ} {a b : ℝ}
    (hfg : IntervalIntegrable (fun x => f x * g x) volume a b) :
    IntervalIntegrable (fun x => f (a + b - x) * g (a + b - x)) volume a b := by
  have := hfg.comp_sub_left (a + b)
  simpa using this.symm

/-- Reflection about the midpoint preserves the integral of `f g`. -/
private lemma fejer_integral_refl (f g : ℝ → ℝ) (a b : ℝ) :
    ∫ x in a..b, f (a + b - x) * g (a + b - x) = ∫ x in a..b, f x * g x := by
  have h : ∫ x in a..b, f (a + b - x) * g (a + b - x)
      = ∫ x in (a + b) - b..(a + b) - a, f x * g x :=
    intervalIntegral.integral_comp_sub_left (fun x => f x * g x) (a + b)
  rw [show a + b - b = a by ring, show a + b - a = b by ring] at h
  exact h

/-- **Fejér's inequality, left half** (item 127 of MATH-PLAN-library-2; the draft `d127-r1-s2`,
written by Claude Opus 5.5 through the Anthropic Batch API, the lane's API-CREDIT-1 work, adapted
by order LEAN-36's session). For `f` convex and continuous on `[a, b]` with `a ≤ b`, and a weight
`g ≥ 0` integrable on `[a, b]` and symmetric about the midpoint (`g (a + b - x) = g x` on
`[a, b]`), `f ((a + b) / 2) ∫ g ≤ ∫ f g`. With `g = 1` it is the left half of Hermite–Hadamard
(`convexOn_midpoint_le_average`, multiplied out). Convexity at the midpoint, applied to `x` and
`a + b - x`, integrated against `g`, whose reflection leaves `∫ f g` unchanged. -/
theorem convexOn_midpoint_mul_integral_le {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ConvexOn ℝ (Icc a b) f) (hfc : ContinuousOn f (Icc a b))
    (hg : IntervalIntegrable g volume a b) (hg0 : ∀ x ∈ Icc a b, 0 ≤ g x)
    (hgs : ∀ x ∈ Icc a b, g (a + b - x) = g x) :
    f ((a + b) / 2) * ∫ x in a..b, g x ≤ ∫ x in a..b, f x * g x := by
  have hfg := fejer_integrable hab hfc hg
  have hfg' := fejer_integrable_refl hfg
  have hI := fejer_integral_refl f g a b
  have hpt : ∀ x ∈ Icc a b, f ((a + b) / 2) * g x
      ≤ (1 / 2) * (f x * g x + f (a + b - x) * g (a + b - x)) := by
    intro x hx
    have hy : a + b - x ∈ Icc a b := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have h := hf.2 hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    have e : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (a + b - x) = (a + b) / 2 := by
      simp only [smul_eq_mul]; ring
    rw [e] at h
    simp only [smul_eq_mul] at h
    rw [hgs x hx]
    have hm := mul_le_mul_of_nonneg_right h (hg0 x hx)
    exact hm.trans_eq (by ring)
  have hmono : ∫ x in a..b, f ((a + b) / 2) * g x
      ≤ ∫ x in a..b, (1 / 2) * (f x * g x + f (a + b - x) * g (a + b - x)) :=
    intervalIntegral.integral_mono_on hab (hg.const_mul _) ((hfg.add hfg').const_mul _) hpt
  have e1 : ∫ x in a..b, f ((a + b) / 2) * g x = f ((a + b) / 2) * ∫ x in a..b, g x := by
    rw [intervalIntegral.integral_const_mul]
  have e2 : ∫ x in a..b, (1 / 2) * (f x * g x + f (a + b - x) * g (a + b - x))
      = (1 / 2) * ((∫ x in a..b, f x * g x) + ∫ x in a..b, f (a + b - x) * g (a + b - x)) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hfg hfg']
  rw [e1, e2, hI] at hmono
  linarith

/-- **Fejér's inequality, right half** (item 127 of MATH-PLAN-library-2; the draft `d127-r1-s2`,
written by Claude Opus 5.5 through the Anthropic Batch API, the lane's API-CREDIT-1 work, adapted
by order LEAN-36's session). For `f` convex and continuous on `[a, b]` with `a ≤ b`, and a weight
`g ≥ 0` integrable on `[a, b]` and symmetric about the midpoint (`g (a + b - x) = g x` on
`[a, b]`), `∫ f g ≤ ((f a + f b) / 2) ∫ g`. With `g = 1` it is
`integral_le_mul_add_div_two_of_convexOn`. Convexity gives `f x + f (a + b - x) ≤ f a + f b` on
`[a, b]`, integrated against `g`, whose reflection leaves `∫ f g` unchanged. -/
theorem integral_mul_le_endpoints {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ConvexOn ℝ (Icc a b) f) (hfc : ContinuousOn f (Icc a b))
    (hg : IntervalIntegrable g volume a b) (hg0 : ∀ x ∈ Icc a b, 0 ≤ g x)
    (hgs : ∀ x ∈ Icc a b, g (a + b - x) = g x) :
    ∫ x in a..b, f x * g x ≤ (f a + f b) / 2 * ∫ x in a..b, g x := by
  have hfg := fejer_integrable hab hfc hg
  have hfg' := fejer_integrable_refl hfg
  have hI := fejer_integral_refl f g a b
  have hpt : ∀ x ∈ Icc a b,
      f x * g x + f (a + b - x) * g (a + b - x) ≤ (f a + f b) * g x := by
    intro x hx
    rw [hgs x hx]
    have hm := mul_le_mul_of_nonneg_right (fejer_pair_le hab hf x hx) (hg0 x hx)
    rw [← add_mul]
    exact hm
  have hmono : ∫ x in a..b, (f x * g x + f (a + b - x) * g (a + b - x))
      ≤ ∫ x in a..b, (f a + f b) * g x :=
    intervalIntegral.integral_mono_on hab (hfg.add hfg') (hg.const_mul _) hpt
  rw [intervalIntegral.integral_add hfg hfg', hI, intervalIntegral.integral_const_mul] at hmono
  have e : (f a + f b) / 2 * ∫ x in a..b, g x = ((f a + f b) * ∫ x in a..b, g x) / 2 := by
    ring
  rw [e]
  linarith

end ClassicalLean.Analysis

open Set in
/-- The hypotheses of `convexOn_midpoint_le_average` hold together: on `[0, 1]`, with `0 < 1`, the
function `x ↦ x ^ 2` is convex (an even power) and continuous. -/
example := ClassicalLean.Analysis.convexOn_midpoint_le_average (f := fun x ↦ x ^ 2) (a := 0)
  (b := 1) (by norm_num) ((Even.convexOn_pow even_two).subset (subset_univ _) (convex_Icc 0 1))
  (continuous_pow 2).continuousOn

open Set in
/-- The hypotheses of `average_le_convexOn_endpoints` hold together: on `[0, 1]`, with `0 < 1`, the
function `x ↦ x ^ 2` is convex (an even power) and continuous. -/
example := ClassicalLean.Analysis.average_le_convexOn_endpoints (f := fun x ↦ x ^ 2) (a := 0)
  (b := 1) (by norm_num) ((Even.convexOn_pow even_two).subset (subset_univ _) (convex_Icc 0 1))
  (continuous_pow 2).continuousOn

open Set in
/-- The hypotheses of `integral_le_trapezoidal_integral` hold together: on `[0, 1]`, with
`0 ≤ 1` and not an equality, the function `x ↦ x ^ 2` is convex (an even power) and continuous,
and the rule takes `N = 2` steps. -/
example := ClassicalLean.Analysis.integral_le_trapezoidal_integral (f := fun x ↦ x ^ 2) (a := 0)
  (b := 1) (by norm_num) ((Even.convexOn_pow even_two).subset (subset_univ _) (convex_Icc 0 1))
  (continuous_pow 2).continuousOn (N := 2) (by norm_num)

open Set in
/-- The hypotheses of `convexOn_midpoint_mul_integral_le` hold together: on `[0, 1]`, with
`0 ≤ 1`, the function `x ↦ x ^ 2` is convex (an even power) and continuous, and the weight
`g x = x (1 − x)` is continuous, so integrable, nonnegative on `[0, 1]` and symmetric about `1/2`;
the inequality is strict here (`1/24 < 1/20`). -/
example := ClassicalLean.Analysis.convexOn_midpoint_mul_integral_le (f := fun x ↦ x ^ 2)
  (g := fun x ↦ x * (1 - x)) (a := 0) (b := 1) (by norm_num)
  ((Even.convexOn_pow even_two).subset (subset_univ _) (convex_Icc 0 1))
  (continuous_pow 2).continuousOn
  ((continuous_id.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _)
  (fun x hx ↦ mul_nonneg hx.1 (by linarith [hx.2]))
  (fun x _ ↦ by ring)

open Set in
/-- The hypotheses of `integral_mul_le_endpoints` hold together: on `[0, 1]`, with `0 ≤ 1`, the
function `x ↦ x ^ 2` is convex (an even power) and continuous, and the weight `g x = x (1 − x)` is
continuous, so integrable, nonnegative on `[0, 1]` and symmetric about `1/2`; the inequality is
strict here (`1/20 < 1/12`). -/
example := ClassicalLean.Analysis.integral_mul_le_endpoints (f := fun x ↦ x ^ 2)
  (g := fun x ↦ x * (1 - x)) (a := 0) (b := 1) (by norm_num)
  ((Even.convexOn_pow even_two).subset (subset_univ _) (convex_Icc 0 1))
  (continuous_pow 2).continuousOn
  ((continuous_id.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _)
  (fun x hx ↦ mul_nonneg hx.1 (by linarith [hx.2]))
  (fun x _ ↦ by ring)
