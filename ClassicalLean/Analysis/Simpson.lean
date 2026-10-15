/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule

/-!
# Simpson's rule: its error bound, and Richardson's identity

Simpson's rule estimates `∫ₐᵇ f` by cutting `[a, b]` into `2N` equal steps of width
`h = (b − a)/(2N)` and, on each pair of steps (a *panel* `[c − h, c + h]`), replacing `f` by the
parabola through its three values: the panel contributes `h/3 · (f(c − h) + 4 f(c) + f(c + h))`.

* `simpson f N a b` — the composite rule, as above (Lean's `x / 0 = 0` makes it `0` for `N = 0`).
* `simpson_error_le` — order LEAN-23, item 48: if `f` is four times differentiable within
  `[a, b]` (one-sided at the ends; the derivatives `f₁, …, f₄` are given as functions) and
  `|f⁗| ≤ M` there, then `|∫ₐᵇ f − simpson f N a b| ≤ (b − a) h⁴ M / 180` for `a ≤ b`, `N ≥ 1`.
* `simpson_error_le_of_contDiffOn` — the same for `f` of class `C⁴` on `[a, b]`, with `M` a bound
  on `iteratedDerivWithin 4 f (Icc a b)`.
* `simpson_eq_integral_of_cubic` — the rule is exact on cubics, for every `a`, `b`, `N ≥ 1`.
* `simpson_error_pow_four`, `abs_simpson_error_pow_four_eq_bound` — the bound is attained: `x⁴`
  on `[0, 1]` with `N = 1` has error exactly `−1/120`, and its size equals the bound for `M = 24`.
* `simpson_eq_trapezoidal` — order LEAN-29, item 93: **Richardson extrapolation, exactly**:
  `simpson f N a b = (4 T(2N) − T(N))/3` with `T` Mathlib's trapezoidal rule, for every `f`, `a`,
  `b` and `N` (at `N = 0` both sides are Lean's `0`).

The proof, one panel at a time: with `F' = f`, the panel's error at half-width `t`,
`g(t) = F(c + t) − F(c − t) − t/3 · (f(c − t) + 4 f(c) + f(c + t))`, has
`g(0) = g'(0) = g''(0) = 0` and `g'''(t) = −t/3 · (f'''(c + t) − f'''(c − t))`. The mean value
theorem on `f'''` gives `|g'''(t)| ≤ (2/3) M t²`, and integrating three times gives
`|g(h)| ≤ M h⁵ / 90`. The `N` panels add up to `N M h⁵/90 = (b − a) h⁴ M / 180`.

## Hypotheses

Measured in order LEAN-23's checks (`checks.py`, exact rationals): the error equals the bound
for `x⁴` with `N = 1, …, 5` on three intervals; the rule is exact on 300 random cubics; the bound
holds on 300 random quintics. Dropping a hypothesis: `N = 0` makes the rule and the bound `0`
while `f = 1` on `[0, 1]` has error `1`; with `a > b`, `x⁴` on `[1, 0]` has error of size `1/120`
against the bound `−1/120` (only the bound's signed form `(b − a) · …` needs `a ≤ b`: the rule
itself changes sign when `a` and `b` are swapped, as the integral does; review r48); without the
derivatives, `|x|` on `[−1, 1]` (fourth derivative `0`
away from `0`, so `M = 0`) has error `1/3`. The proof uses `f₄` and `M` only through
`|f₃ x − f₃ y| ≤ M |x − y|` on `[a, b]` (the mean value theorem), so a Lipschitz `f₃` would do;
the statement keeps the textbook form, which already allows a discontinuous `f₄` (review r48).

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-23): `simpson` has 9 hits in 4 files, all an
author's name. Mathlib has the trapezoidal rule and its error bound
(`MeasureTheory/Integral/IntervalIntegral/TrapezoidalRule.lean`); its integration step (from a
bound on `φ'` to a bound on `φ`, by `image_norm_le_of_norm_deriv_right_le_deriv_boundary`) is
adapted here, starting from `0`, as `abs_le_of_abs_deriv_le`. The plan's row names Taylor's
theorem; it is not used. Also used: `integral_hasDerivWithinAt_right`,
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`, `integral_eq_sub_of_hasDerivAt`.

For order LEAN-29 (item 93, row F4 of MATH-PLAN-library-2, run by its check script at
2026-10-15 02:19 UTC, before `simpson_eq_trapezoidal` was written): `richardson|extrapolat` gave 0
lines in pinned Mathlib, 0 in Mathlib master at `2da3ab0a`, and 0 in the library; the library's
matches now are this module's own text. `simpson_eq_trapezoidal` uses Mathlib's
`trapezoidal_integral` only through its definition.
-/

open Set Finset intervalIntegral

namespace ClassicalLean

/-- Composite Simpson's rule with `N` pairs of panels on `[a, b]`: with step
`h = (b − a)/(2N)` and nodes `xⱼ = a + j h`, it is `h/3 · ∑ₖ (x₂ₖ + 4 x₂ₖ₊₁ + x₂ₖ₊₂)` evaluated by
`f`. For `N = 0` Lean's `x / 0 = 0` makes it `0`. -/
noncomputable def simpson (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) : ℝ :=
  (b - a) / (2 * N) / 3 * ∑ k ∈ range N,
    (f (a + 2 * k * ((b - a) / (2 * N))) + 4 * f (a + (2 * k + 1) * ((b - a) / (2 * N))) +
      f (a + (2 * k + 2) * ((b - a) / (2 * N))))

/-- `G b − G a` as a sum over the `N` panel pairs `[a + 2k h, a + (2k + 2) h]`. -/
private theorem sub_eq_sum_panels (G : ℝ → ℝ) {N : ℕ} (hN : 0 < N) (a b : ℝ) :
    G b - G a = ∑ k ∈ range N,
      (G (a + (2 * k + 2) * ((b - a) / (2 * N))) - G (a + 2 * k * ((b - a) / (2 * N)))) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have := Finset.sum_range_sub (fun k : ℕ ↦ G (a + 2 * k * ((b - a) / (2 * N)))) N
  have e1 : a + 2 * (N : ℝ) * ((b - a) / (2 * N)) = b := by field_simp; ring
  simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero, e1] at this
  rw [← this]
  refine sum_congr rfl fun k _ ↦ ?_
  push_cast
  ring_nf

/-- If `φ 0 = 0` and `|φ' t| ≤ C tᵏ` on `[0, h]`, then `|φ t| ≤ C tᵏ⁺¹/(k + 1)` there. -/
private theorem abs_le_of_abs_deriv_le {φ φ' : ℝ → ℝ} {h C : ℝ} {k : ℕ}
    (hφ : ∀ t ∈ Icc 0 h, HasDerivWithinAt φ (φ' t) (Icc 0 h) t) (h0 : φ 0 = 0)
    (hb : ∀ t ∈ Icc 0 h, |φ' t| ≤ C * t ^ k) :
    ∀ t ∈ Icc 0 h, |φ t| ≤ C / (k + 1) * t ^ (k + 1) := by
  intro t ht
  have hB (x : ℝ) : HasDerivAt (fun y ↦ C / (k + 1) * y ^ (k + 1)) (C * x ^ k) x := by
    convert! (hasDerivAt_const x (C / (k + 1))).mul ((hasDerivAt_id x).pow (k + 1)) using 1
    simp [field]
  simpa [Real.norm_eq_abs, h0] using image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun x hx ↦ (hφ x hx).continuousWithinAt)
    (fun x hx ↦ by grind [Icc_mem_nhdsGE_of_mem, HasDerivWithinAt.mono_of_mem_nhdsWithin])
    (by simp [h0]) hB (fun x hx ↦ hb x (Ico_subset_Icc_self hx)) ht

/-- One panel `[c − h, c + h]` inside `[a, b]`, with `F' = f` and `f` four times differentiable
within `[a, b]`, `|f⁗| ≤ M`: Simpson's error on the panel is at most `M h⁵/90`. -/
private theorem abs_panel_le {F f f₁ f₂ f₃ f₄ : ℝ → ℝ} {a b c h M : ℝ} (hh : 0 ≤ h)
    (hsub : Icc (c - h) (c + h) ⊆ Icc a b)
    (hF : ∀ x ∈ Icc a b, HasDerivWithinAt F (f x) (Icc a b) x)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f₁ x) (Icc a b) x)
    (hf₁ : ∀ x ∈ Icc a b, HasDerivWithinAt f₁ (f₂ x) (Icc a b) x)
    (hf₂ : ∀ x ∈ Icc a b, HasDerivWithinAt f₂ (f₃ x) (Icc a b) x)
    (hf₃ : ∀ x ∈ Icc a b, HasDerivWithinAt f₃ (f₄ x) (Icc a b) x)
    (hM : ∀ x ∈ Icc a b, |f₄ x| ≤ M) :
    |F (c + h) - F (c - h) - h / 3 * (f (c - h) + 4 * f c + f (c + h))| ≤ M / 90 * h ^ 5 := by
  have hmp : MapsTo (fun t ↦ c + t) (Icc 0 h) (Icc a b) := fun t ht ↦
    hsub ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmm : MapsTo (fun t ↦ c - t) (Icc 0 h) (Icc a b) := fun t ht ↦
    hsub ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hid (t : ℝ) : HasDerivWithinAt (fun x : ℝ ↦ x) 1 (Icc 0 h) t := hasDerivWithinAt_id t _
  have hp {G G' : ℝ → ℝ} (hG : ∀ x ∈ Icc a b, HasDerivWithinAt G (G' x) (Icc a b) x) (t : ℝ)
      (ht : t ∈ Icc 0 h) :
      HasDerivWithinAt (fun t ↦ G (c + t)) (G' (c + t)) (Icc 0 h) t := by
    exact ((hG _ (hmp ht)).comp t ((hid t).const_add c) hmp).congr_deriv (by ring)
  have hm {G G' : ℝ → ℝ} (hG : ∀ x ∈ Icc a b, HasDerivWithinAt G (G' x) (Icc a b) x) (t : ℝ)
      (ht : t ∈ Icc 0 h) :
      HasDerivWithinAt (fun t ↦ G (c - t)) (-G' (c - t)) (Icc 0 h) t := by
    exact ((hG _ (hmm ht)).comp t ((hid t).const_sub c) hmm).congr_deriv (by ring)
  -- the error as a function of the half-width `t`, and its first three derivatives
  set g : ℝ → ℝ := fun t ↦ F (c + t) - F (c - t) - t / 3 * (f (c - t) + 4 * f c + f (c + t))
  set g₁ : ℝ → ℝ := fun t ↦
    2 / 3 * (f (c + t) + f (c - t)) - 4 / 3 * f c - t / 3 * (f₁ (c + t) - f₁ (c - t))
  set g₂ : ℝ → ℝ := fun t ↦
    1 / 3 * (f₁ (c + t) - f₁ (c - t)) - t / 3 * (f₂ (c + t) + f₂ (c - t))
  set g₃ : ℝ → ℝ := fun t ↦ -(t / 3 * (f₃ (c + t) - f₃ (c - t)))
  have hg : ∀ t ∈ Icc 0 h, HasDerivWithinAt g (g₁ t) (Icc 0 h) t := by
    intro t ht
    have := ((hp hF t ht).sub (hm hF t ht)).sub (((hid t).div_const 3).mul
      (((hm hf t ht).add_const (4 * f c)).add (hp hf t ht)))
    convert this using 1
    simp only [g₁, Pi.add_apply]; ring
  have hg₁ : ∀ t ∈ Icc 0 h, HasDerivWithinAt g₁ (g₂ t) (Icc 0 h) t := by
    intro t ht
    have := ((((hp hf t ht).add (hm hf t ht)).const_mul (2 / 3)).sub_const (4 / 3 * f c)).sub
      (((hid t).div_const 3).mul ((hp hf₁ t ht).sub (hm hf₁ t ht)))
    convert this using 1
    simp only [g₂, Pi.sub_apply]; ring
  have hg₂ : ∀ t ∈ Icc 0 h, HasDerivWithinAt g₂ (g₃ t) (Icc 0 h) t := by
    intro t ht
    have := (((hp hf₁ t ht).sub (hm hf₁ t ht)).const_mul (1 / 3)).sub
      (((hid t).div_const 3).mul ((hp hf₂ t ht).add (hm hf₂ t ht)))
    convert this using 1
    simp only [g₃, Pi.add_apply]; ring
  -- the mean value theorem on `f₃` bounds `g₃`
  have hb₃ : ∀ t ∈ Icc 0 h, |g₃ t| ≤ 2 / 3 * M * t ^ 2 := by
    intro t ht
    have hmvt := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hf₃
      (fun x hx ↦ by simpa [Real.norm_eq_abs] using hM x hx) (hmm ht) (hmp ht)
    simp only [Real.norm_eq_abs] at hmvt
    rw [show c + t - (c - t) = 2 * t by ring,
      abs_of_nonneg (show (0 : ℝ) ≤ 2 * t by linarith [ht.1])] at hmvt
    simp only [g₃, abs_neg, abs_mul, abs_div, abs_of_nonneg ht.1,
      abs_of_pos (show (0 : ℝ) < 3 by norm_num)]
    calc t / 3 * |f₃ (c + t) - f₃ (c - t)| ≤ t / 3 * (M * (2 * t)) := by
          gcongr; linarith [ht.1]
      _ = 2 / 3 * M * t ^ 2 := by ring
  have h₂ := abs_le_of_abs_deriv_le hg₂ (by simp [g₂]) hb₃
  have h₁ := abs_le_of_abs_deriv_le hg₁ (by simp only [g₁]; ring_nf) h₂
  have h₀ := abs_le_of_abs_deriv_le hg (by simp [g]) h₁
  exact (h₀ h ⟨hh, le_rfl⟩).trans_eq (by push_cast; ring)

/-- **Simpson's rule error bound.** If `f` is four times differentiable within `[a, b]`
(derivatives `f₁, …, f₄`, one-sided at the ends) and `|f⁗| ≤ M` there, composite Simpson with
`N ≥ 1` pairs of panels, step `h = (b − a)/(2N)`, is within `(b − a) h⁴ M / 180` of `∫ f`. -/
theorem simpson_error_le {f f₁ f₂ f₃ f₄ : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b) {N : ℕ} (hN : 0 < N)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f₁ x) (Icc a b) x)
    (hf₁ : ∀ x ∈ Icc a b, HasDerivWithinAt f₁ (f₂ x) (Icc a b) x)
    (hf₂ : ∀ x ∈ Icc a b, HasDerivWithinAt f₂ (f₃ x) (Icc a b) x)
    (hf₃ : ∀ x ∈ Icc a b, HasDerivWithinAt f₃ (f₄ x) (Icc a b) x)
    (hM : ∀ x ∈ Icc a b, |f₄ x| ≤ M) :
    |(∫ x in a..b, f x) - simpson f N a b| ≤ (b - a) * ((b - a) / (2 * N)) ^ 4 * M / 180 := by
  have hcont : ContinuousOn f (Icc a b) := fun x hx ↦ (hf x hx).continuousWithinAt
  set F : ℝ → ℝ := fun x ↦ ∫ t in a..x, f t
  have hF : ∀ x ∈ Icc a b, HasDerivWithinAt F (f x) (Icc a b) x := by
    intro y hy
    have := Fact.mk hy
    exact integral_hasDerivWithinAt_right
      ((hcont.mono (Icc_subset_Icc le_rfl hy.2)).intervalIntegrable_of_Icc hy.1)
      (hcont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc y)
      (hcont.continuousWithinAt hy)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set h := (b - a) / (2 * N) with hh_def
  have hh : 0 ≤ h := div_nonneg (sub_nonneg.mpr hab) (by positivity)
  have hint : (∫ x in a..b, f x) = F b - F a := by simp [F]
  rw [hint, sub_eq_sum_panels F hN a b, simpson, mul_sum, ← sum_sub_distrib]
  calc |∑ k ∈ range N, (F (a + (2 * k + 2) * h) - F (a + 2 * k * h) -
          h / 3 * (f (a + 2 * k * h) + 4 * f (a + (2 * k + 1) * h) + f (a + (2 * k + 2) * h)))|
      ≤ ∑ k ∈ range N, |F (a + (2 * k + 2) * h) - F (a + 2 * k * h) -
          h / 3 * (f (a + 2 * k * h) + 4 * f (a + (2 * k + 1) * h) + f (a + (2 * k + 2) * h))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ range N, M / 90 * h ^ 5 := by
        refine sum_le_sum fun k hk ↦ ?_
        have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast mem_range.mp hk
        have hc := abs_panel_le (c := a + (2 * k + 1) * h) hh ?_ hF hf hf₁ hf₂ hf₃ hM
        · convert hc using 4 <;> ring_nf
        · intro x hx
          refine ⟨?_, ?_⟩
          · nlinarith [hx.1, (k.cast_nonneg : (0 : ℝ) ≤ k)]
          · have : a + (2 * k + 2) * h ≤ b := by
              have : (2 * k + 2) * h ≤ 2 * N * h := by nlinarith
              have h2 : 2 * N * h = b - a := by rw [hh_def]; field_simp
              linarith
            nlinarith [hx.2]
    _ = (b - a) * h ^ 4 * M / 180 := by
        rw [sum_const, card_range, nsmul_eq_mul]
        have h2 : 2 * N * h = b - a := by rw [hh_def]; field_simp
        rw [← h2]; ring

/-- Simpson's error bound for `f` of class `C⁴` on `[a, b]`, with the bound on the fourth
derivative within `[a, b]`. -/
theorem simpson_error_le_of_contDiffOn {f : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b) {N : ℕ}
    (hN : 0 < N) (hf : ContDiffOn ℝ 4 f (Icc a b))
    (hM : ∀ x ∈ Icc a b, |iteratedDerivWithin 4 f (Icc a b) x| ≤ M) :
    |(∫ x in a..b, f x) - simpson f N a b| ≤ (b - a) * ((b - a) / (2 * N)) ^ 4 * M / 180 := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp [simpson]
  have hd (k : ℕ) (hk : k < 4) : ∀ x ∈ Icc a b,
      HasDerivWithinAt (iteratedDerivWithin k f (Icc a b))
        (iteratedDerivWithin (k + 1) f (Icc a b) x) (Icc a b) x := by
    intro x hx
    rw [iteratedDerivWithin_succ]
    exact ((hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hk)
      (uniqueDiffOn_Icc hlt)) x hx).hasDerivWithinAt
  have h0 := hd 0 (by norm_num)
  simp only [iteratedDerivWithin_zero] at h0
  exact simpson_error_le hab hN h0 (hd 1 (by norm_num)) (hd 2 (by norm_num))
    (hd 3 (by norm_num)) hM

/-- **Simpson's rule is exact on cubics**, for every `a`, `b` and `N ≥ 1`. -/
theorem simpson_eq_integral_of_cubic (c₀ c₁ c₂ c₃ a b : ℝ) {N : ℕ} (hN : 0 < N) :
    simpson (fun x ↦ c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3) N a b =
      ∫ x in a..b, c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 := by
  set G : ℝ → ℝ := fun x ↦ c₀ * x + c₁ * x ^ 2 / 2 + c₂ * x ^ 3 / 3 + c₃ * x ^ 4 / 4
  have hG : ∀ x, HasDerivAt G (c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3) x := by
    intro x
    have := ((((hasDerivAt_id' x).const_mul c₀).add (((hasDerivAt_pow 2 x).const_mul c₁).div_const
      2)).add (((hasDerivAt_pow 3 x).const_mul c₂).div_const 3)).add
      (((hasDerivAt_pow 4 x).const_mul c₃).div_const 4)
    convert this using 1
    push_cast; ring
  rw [integral_eq_sub_of_hasDerivAt (fun x _ ↦ hG x)
      (Continuous.intervalIntegrable (by fun_prop) _ _), sub_eq_sum_panels G hN,
    simpson, mul_sum]
  refine sum_congr rfl fun k _ ↦ ?_
  simp only [G]
  ring

/-- The bound is attained: for `x⁴` on `[0, 1]` with one pair of panels, `f⁗ = 24`, the bound
is `1 · (1/2)⁴ · 24/180 = 1/120`, and the error is exactly `1/5 − 5/24 = −1/120`. -/
theorem simpson_error_pow_four :
    (∫ x in (0 : ℝ)..1, x ^ 4) - simpson (· ^ 4) 1 0 1 = -1 / 120 := by
  simp only [integral_pow, simpson]
  norm_num

/-- The bound of `simpson_error_le` for `x⁴` on `[0, 1]`, `N = 1`, `M = 24` is reached. -/
theorem abs_simpson_error_pow_four_eq_bound :
    |(∫ x in (0 : ℝ)..1, x ^ 4) - simpson (· ^ 4) 1 0 1| =
      (1 - 0) * ((1 - 0) / (2 * (1 : ℕ))) ^ 4 * 24 / 180 := by
  rw [simpson_error_pow_four]
  norm_num

/-- **Richardson extrapolation, exactly** (order LEAN-29, item 93 of MATH-PLAN-library-2). The
library's composite Simpson rule with `N` panels, each two steps wide, is `(4 T(2N) − T(N))/3`,
where `T(m)` is Mathlib's trapezoidal rule with `m` steps (`trapezoidal_integral`). So Simpson's
rule is the Richardson extrapolation of the trapezoidal rule: for smooth `f`, the trapezoidal rule
with step `H` has error `c H² + O(H⁴)` (Euler–Maclaurin; not proved here); `T(N)` has step
`(b − a)/N` and `T(2N)` half of it, so `(4 T(2N) − T(N))/3` cancels the `H²` term. The identity
holds for every `f`, `a` and `b` (`a > b` and `a = b` included); at `N = 0` both sides are Lean's
`0`, since `(b − a) / 0 = 0` in both definitions. With `h = (b − a)/(2N)` and nodes `a + j h`,
`T(2N)` uses every node, `T(N)` the even ones, and `4 T(2N) − T(N)` weights the ends `h`, the odd
nodes `4 h` and the even inner nodes `2 h`, which is `3` times Simpson's rule. -/
theorem simpson_eq_trapezoidal (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) :
    simpson f N a b =
      (4 * trapezoidal_integral f (2 * N) a b - trapezoidal_integral f N a b) / 3 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [simpson, trapezoidal_integral]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  set h := (b - a) / (2 * ((n + 1 : ℕ) : ℝ)) with hh
  set g : ℕ → ℝ := fun j ↦ f (a + j * h) with hg
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  -- every node is `a + j h`
  have node (j : ℕ) (x : ℝ) (hx : x = a + j * h) : f x = g j := by rw [hx]
  have ha : f a = g 0 := node 0 a (by simp)
  have hb : f b = g (2 * (n + 1)) := node _ b (by rw [hh]; push_cast; field_simp; ring)
  -- the two sums
  have odd_even : ∀ m : ℕ, ∑ k ∈ range (2 * m + 1), g (k + 1) =
      ∑ k ∈ range (m + 1), g (2 * k + 1) + ∑ k ∈ range m, g (2 * k + 2) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
        sum_range_succ (fun k ↦ g (2 * k + 1)) (m + 1), sum_range_succ (fun k ↦ g (2 * k + 2)) m]
      ring_nf
  have panels : ∀ m : ℕ, ∑ k ∈ range (m + 1), (g (2 * k) + 4 * g (2 * k + 1) + g (2 * k + 2)) =
      g 0 + g (2 * (m + 1)) + 4 * ∑ k ∈ range (m + 1), g (2 * k + 1) +
        2 * ∑ k ∈ range m, g (2 * k + 2) := by
    intro m
    induction m with
    | zero => simp; ring
    | succ m ih =>
      rw [sum_range_succ, ih, sum_range_succ (fun k ↦ g (2 * k + 1)) (m + 1),
        sum_range_succ (fun k ↦ g (2 * k + 2)) m]
      ring_nf
  -- unfold the two rules into `g`
  have hS : simpson f (n + 1) a b =
      h / 3 * ∑ k ∈ range (n + 1), (g (2 * k) + 4 * g (2 * k + 1) + g (2 * k + 2)) := by
    rw [simpson, ← hh]
    refine congrArg (h / 3 * ·) (sum_congr rfl fun k _ ↦ ?_)
    rw [node (2 * k) _ (by push_cast; ring), node (2 * k + 1) _ (by push_cast; ring),
      node (2 * k + 2) _ (by push_cast; ring)]
  have hT2 : trapezoidal_integral f (2 * (n + 1)) a b =
      h * ((g 0 + g (2 * (n + 1))) / 2 + ∑ k ∈ range (2 * n + 1), g (k + 1)) := by
    rw [trapezoidal_integral, ha, hb, show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
    congr 1
    · rw [hh]; push_cast; ring
    · refine congrArg (_ + ·) (sum_congr rfl fun k _ ↦ node (k + 1) _ ?_)
      rw [hh]; push_cast; field_simp
  have hT1 : trapezoidal_integral f (n + 1) a b =
      2 * h * ((g 0 + g (2 * (n + 1))) / 2 + ∑ k ∈ range n, g (2 * k + 2)) := by
    rw [trapezoidal_integral, ha, hb, show n + 1 - 1 = n by omega]
    congr 1
    · rw [hh]; field_simp
    · refine congrArg (_ + ·) (sum_congr rfl fun k _ ↦ node (2 * k + 2) _ ?_)
      rw [hh]; push_cast; field_simp
  rw [hS, hT2, hT1, panels, odd_even]
  ring

end ClassicalLean

open Set in
/-- The hypotheses of `simpson_error_le` hold together: on `[0, 1]` (`0 ≤ 1`, not a point), with
`N = 2` panel pairs (four panels of width `1/4`), `f x = x ^ 4` and its derivatives `4 x ^ 3`,
`12 x ^ 2`, `24 x` and `24`, each the
derivative of the one before on the interval, and `|f⁗| = 24 ≤ M = 24`. -/
example := ClassicalLean.simpson_error_le (f := fun x ↦ x ^ 4) (f₁ := fun x ↦ 4 * x ^ 3)
  (f₂ := fun x ↦ 12 * x ^ 2) (f₃ := fun x ↦ 24 * x) (f₄ := fun _ ↦ 24) (a := 0) (b := 1)
  (M := 24) (by norm_num) (N := 2) (by norm_num)
  (fun x _ ↦ by simpa using (hasDerivAt_pow 4 x).hasDerivWithinAt)
  (fun x _ ↦ by
    have := ((hasDerivAt_pow 3 x).const_mul 4).hasDerivWithinAt (s := Icc 0 1)
    convert this using 1; ring)
  (fun x _ ↦ by
    have := ((hasDerivAt_pow 2 x).const_mul 12).hasDerivWithinAt (s := Icc 0 1)
    convert this using 1; ring)
  (fun x _ ↦ by simpa using ((hasDerivAt_id x).const_mul 24).hasDerivWithinAt)
  (fun x _ ↦ by norm_num)
