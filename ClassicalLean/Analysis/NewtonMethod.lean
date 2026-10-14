/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Newton's method converges quadratically near a simple root

To find a root `r` of `f`, Newton's method replaces a guess `x` by the root of the tangent line at
`x`: `newtonStep f f' x = x − f x / f' x`, with `f'` the derivative.

* `abs_sub_sub_mul_le_half_mul_sq` — on an interval where `f` has derivative `f'` and `f'` is
  `M`-Lipschitz, `f` stays within `(M/2) (y − x)²` of its tangent line at `x`.
* `abs_newtonStep_sub_le` — if also `f r = 0` and `|f' x| ≥ m > 0`, one step from `x` lands within
  `(M / (2 m)) (x − r)²` of `r`: the new error is at most a constant times the old error squared.
* `abs_newtonIterate_sub_le` — on `[r − δ, r + δ]`, with `|f'| ≥ m > 0` there and
  `(M / (2 m)) δ ≤ 1`, every iterate from a start `x₀` in that interval stays in it, and with
  `K = M / (2 m)`, `K |x_k − r| ≤ (K |x₀ − r|) ^ (2 ^ k)`: the number of correct digits roughly
  doubles each step.
* `tendsto_newtonIterate` — if `(M / (2 m)) δ < 1`, the iterates converge to `r`.

When `M = 0` the second part of `abs_newtonIterate_sub_le` says nothing (both sides are `0`); then
`abs_newtonStep_sub_le` shows that one step lands on `r`. Derivatives are two-sided
(`HasDerivAt`), also at the ends of the interval, so `f` must be differentiable a little beyond it.

The textbook form assumes `|f''| ≤ M`; here `f'` is only assumed `M`-Lipschitz, which follows from
it. "Simple root" is the hypothesis `|f'| ≥ m > 0` near `r`. The constant `M / (2 m)` is derived in
this module from the tangent-line bound; no book is cited for it.

## Hypotheses

Measured in order LEAN-21's checks (check C33, exact rationals): `f = x² − 4` on `[1, 3]` and
`f = x³ − 8` on `[5/3, 7/3]`, one step at 101 and 61 points, the iterates from 21 starts each.
Each hypothesis is needed: drop it alone and the conclusion fails at (one step, `f = x² − 4`
unless stated; the cases for `s` convex, `f'` the derivative and `r ∈ s` were found by review r33):

* `f r = 0`: `r = 19/10`, `x = r`: `|N r − r| = 39/380 > 0`.
* `m ≤ |f' x|`: `x = 1`, `m = 3`, `M = 2`: `1/2 > 1/3`.
* `f'` `M`-Lipschitz: `x = 1`, `M = 0`, `m = 2`: `1/2 > 0`.
* `0 < m`: `m = 0`, where Lean reads `M / 0` as `0`: `1/2 > 0`.
* `x ∈ s` (by hand): `f = x² − 4` on `[1, 3]`, extended smoothly with `f 10 = 1000`, `f' 10 = 1`,
  `m = 1`, `M = 2`: `992 > 64`.
* `r ∈ s`: `s = {1}`, `x = 1`, `M = 0`, `m = 2`: `1/2 > 0`.
* `s` convex (by hand): `s = {1, 2}`, `r = 2`, a smooth `f` with `f 1 = −3`, `f 2 = 0` and
  `f' = 1` at both points, `M = 0`, `m = 1`, `x = 1`: `|N 1 − 2| = 2 > 0`.
* `f'` the derivative: `f' = 1` everywhere, `M = 0`, `m = 1`, `x = 1`: `2 > 0`.
* for the iterates, `(M / (2 m)) δ ≤ 1`: `δ = 3/2` (so `m = 1`), `x₀ = 1/2`: the first step lands
  at distance `9/4 > 3/2`.
* `|x₀ − r| ≤ δ`: `δ = 1`, `x₀ = 1/10`: the first step lands at distance `361/20`.
* the strict `(M / (2 m)) δ < 1`, for convergence (review r33): `f t = 3 t − t |t|`,
  `f' t = 3 − 2 |t|`, `r = 0`, `δ = 1`, `m = 1`, `M = 2`, so the product is `1`: from `x₀ = 1` the
  iterates are `1, −1, 1, −1, …`.

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-21, `grep -rniE` over Mathlib):
`newton.?s? method|newtonMap|newtonStep|newton.?raphson` 37 lines in 4 files: `Polynomial.newtonMap`
(Dynamics/Newton, the iteration for a polynomial over a ring, with a nilpotent value, not
convergence over the reals), Henselian rings, `Nat.nthRoot`, and the Jordan–Chevalley
decomposition; `quadratic(ally)? conver|order of convergence` 0. Used:
`antitoneOn_of_hasDerivWithinAt_nonpos`, `Convex.add_smul_sub_mem`. The plan's row names Taylor's
theorem with the Lagrange remainder (`taylor_mean_remainder_lagrange`); it is not used, because it
needs a second derivative.
-/

open Filter Topology Set

namespace ClassicalLean.Analysis

/-- One step of Newton's method for `f` with derivative `f'`: the root of the tangent line at
`x`. -/
noncomputable def newtonStep (f f' : ℝ → ℝ) (x : ℝ) : ℝ := x - f x / f' x

/-- Both sides of the tangent-line bound at once: for `|σ| ≤ 1`,
`σ (f y − f x − f' x (y − x)) ≤ (M/2) (y − x)²`. -/
private theorem mul_sub_sub_mul_le {f f' : ℝ → ℝ} {s : Set ℝ} {M x y σ : ℝ} (hσ : |σ| ≤ 1)
    (hs : Convex ℝ s) (hd : ∀ t ∈ s, HasDerivAt f (f' t) t)
    (hL : ∀ t ∈ s, ∀ u ∈ s, |f' t - f' u| ≤ M * |t - u|) (hx : x ∈ s) (hy : y ∈ s) :
    σ * (f y - f x - f' x * (y - x)) ≤ M / 2 * (y - x) ^ 2 := by
  set d := y - x with hd_def
  have hp : ∀ u ∈ Icc (0 : ℝ) 1, x + u * d ∈ s := fun u hu ↦ by
    simpa [smul_eq_mul] using hs.add_smul_sub_mem hx hy hu
  let G : ℝ → ℝ := fun u ↦ σ * (f (x + u * d) - f x - u * (f' x * d)) - M / 2 * u ^ 2 * d ^ 2
  have hG : ∀ u ∈ Icc (0 : ℝ) 1,
      HasDerivAt G (σ * (f' (x + u * d) * d - f' x * d) - M * u * d ^ 2) u := by
    intro u hu
    have h1 : HasDerivAt (fun u ↦ x + u * d) d u := by
      simpa using ((hasDerivAt_id u).mul_const d).const_add x
    have h2 : HasDerivAt (fun u ↦ f (x + u * d)) (f' (x + u * d) * d) u :=
      (hd _ (hp u hu)).comp u h1
    have h3 := ((h2.sub_const (f x)).sub ((hasDerivAt_id u).mul_const (f' x * d))).const_mul σ
    have h4 := ((hasDerivAt_pow 2 u).const_mul (M / 2)).mul_const (d ^ 2)
    convert h3.sub h4 using 1
    · funext v
      simp only [G, Pi.sub_apply, id]
    · ring
  have hanti : AntitoneOn G (Icc 0 1) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      (fun u hu ↦ (hG u hu).continuousAt.continuousWithinAt)
      (fun u hu ↦ (hG u (interior_subset hu)).hasDerivWithinAt) fun u hu ↦ ?_
    have hu' := interior_subset hu
    have hu0 : 0 ≤ u := hu'.1
    have hb := hL _ (hp u hu') x hx
    rw [add_sub_cancel_left, abs_mul, abs_of_nonneg hu0] at hb
    have e1 : σ * (f' (x + u * d) * d - f' x * d) ≤ |σ| * (|f' (x + u * d) - f' x| * |d|) := by
      rw [← abs_mul, ← mul_sub_right_distrib, ← abs_mul]
      exact le_abs_self _
    have hd2 : |d| * |d| = d ^ 2 := by rw [← abs_mul, ← sq, abs_sq]
    have e2 : |σ| * (|f' (x + u * d) - f' x| * |d|) ≤ |f' (x + u * d) - f' x| * |d| :=
      mul_le_of_le_one_left (by positivity) hσ
    have e3 : |f' (x + u * d) - f' x| * |d| ≤ M * (u * |d|) * |d| :=
      mul_le_mul_of_nonneg_right hb (abs_nonneg d)
    have e4 : M * (u * |d|) * |d| = M * u * d ^ 2 := by rw [← hd2]; ring
    linarith
  have h01 := hanti (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_le_one
  simp only [G, one_mul, zero_mul, add_zero, sub_self, mul_zero, one_pow, zero_pow two_ne_zero]
    at h01
  rw [hd_def, add_sub_cancel] at h01
  linarith

/-- **The tangent-line bound.** On a convex set `s` where `f` has derivative `f'` and `f'` is
`M`-Lipschitz, `|f y − f x − f' x (y − x)| ≤ (M/2) (y − x)²` for `x, y ∈ s`. -/
theorem abs_sub_sub_mul_le_half_mul_sq {f f' : ℝ → ℝ} {s : Set ℝ} {M x y : ℝ}
    (hs : Convex ℝ s) (hd : ∀ t ∈ s, HasDerivAt f (f' t) t)
    (hL : ∀ t ∈ s, ∀ u ∈ s, |f' t - f' u| ≤ M * |t - u|) (hx : x ∈ s) (hy : y ∈ s) :
    |f y - f x - f' x * (y - x)| ≤ M / 2 * (y - x) ^ 2 := by
  have h1 := mul_sub_sub_mul_le (σ := 1) (by simp) hs hd hL hx hy
  have h2 := mul_sub_sub_mul_le (σ := -1) (by simp) hs hd hL hx hy
  rw [abs_le]
  constructor <;> linarith

/-- **One Newton step squares the error, up to a constant.** On a convex set `s` containing `x`
and a root `r` of `f`, where `f` has derivative `f'` and `f'` is `M`-Lipschitz, if
`|f' x| ≥ m > 0` then `|newtonStep f f' x − r| ≤ (M / (2 m)) (x − r)²`. -/
theorem abs_newtonStep_sub_le {f f' : ℝ → ℝ} {s : Set ℝ} {M m x r : ℝ} (hs : Convex ℝ s)
    (hd : ∀ t ∈ s, HasDerivAt f (f' t) t) (hL : ∀ t ∈ s, ∀ u ∈ s, |f' t - f' u| ≤ M * |t - u|)
    (hx : x ∈ s) (hr : r ∈ s) (hfr : f r = 0) (hm : 0 < m) (hmx : m ≤ |f' x|) :
    |newtonStep f f' x - r| ≤ M / (2 * m) * (x - r) ^ 2 := by
  have hpos : 0 < |f' x| := hm.trans_le hmx
  have hfx : f' x ≠ 0 := abs_pos.mp hpos
  have e : newtonStep f f' x - r = (f r - f x - f' x * (r - x)) / f' x := by
    rw [newtonStep, hfr]
    field_simp
    ring
  have hT := abs_sub_sub_mul_le_half_mul_sq hs hd hL hx hr
  rw [e, abs_div]
  calc |f r - f x - f' x * (r - x)| / |f' x|
      ≤ |f r - f x - f' x * (r - x)| / m := div_le_div_of_nonneg_left (abs_nonneg _) hm hmx
    _ ≤ M / 2 * (r - x) ^ 2 / m := div_le_div_of_nonneg_right hT hm.le
    _ = M / (2 * m) * (x - r) ^ 2 := by field_simp; ring

/-- **Newton's method converges quadratically near a simple root.** Let `f r = 0`, and on
`[r − δ, r + δ]` let `f` have derivative `f'`, `f'` be `M`-Lipschitz and `|f'| ≥ m > 0`. With
`K = M / (2 m)` and `K δ ≤ 1`, from any `x₀` with `|x₀ − r| ≤ δ` the `k`-th iterate stays within
`δ` of `r`, and `K |x_k − r| ≤ (K |x₀ − r|) ^ (2 ^ k)`. -/
theorem abs_newtonIterate_sub_le {f f' : ℝ → ℝ} {M m r δ x₀ : ℝ}
    (hd : ∀ t ∈ Icc (r - δ) (r + δ), HasDerivAt f (f' t) t)
    (hL : ∀ t ∈ Icc (r - δ) (r + δ), ∀ u ∈ Icc (r - δ) (r + δ), |f' t - f' u| ≤ M * |t - u|)
    (hfr : f r = 0) (hm : 0 < m) (hm' : ∀ t ∈ Icc (r - δ) (r + δ), m ≤ |f' t|)
    (hMδ : M / (2 * m) * δ ≤ 1) (hx₀ : |x₀ - r| ≤ δ) (k : ℕ) :
    |(newtonStep f f')^[k] x₀ - r| ≤ δ ∧
      M / (2 * m) * |(newtonStep f f')^[k] x₀ - r| ≤ (M / (2 * m) * |x₀ - r|) ^ (2 ^ k) := by
  set K := M / (2 * m)
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hx₀
  have hmem : ∀ x, |x - r| ≤ δ → x ∈ Icc (r - δ) (r + δ) := fun x hx ↦ by
    rw [abs_le] at hx; constructor <;> linarith
  have hr : r ∈ Icc (r - δ) (r + δ) := hmem r (by simpa using hδ)
  induction k with
  | zero => simpa using hx₀
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    set x := (newtonStep f f')^[k] x₀
    have hstep := abs_newtonStep_sub_le (convex_Icc _ _) hd hL (hmem x ih1) hr hfr hm
      (hm' x (hmem x ih1))
    rw [Function.iterate_succ_apply']
    set e := |x - r|
    have he : 0 ≤ e := abs_nonneg _
    have hsq : (x - r) ^ 2 = e * e := by rw [← sq_abs, sq]
    rw [hsq] at hstep
    rcases le_or_gt 0 K with hK | hK
    · refine ⟨?_, ?_⟩
      · have : K * e ≤ 1 := (mul_le_mul_of_nonneg_left ih1 hK).trans hMδ
        nlinarith
      · rw [pow_succ, pow_mul, sq]
        calc K * |newtonStep f f' x - r| ≤ K * (K * (e * e)) := mul_le_mul_of_nonneg_left hstep hK
          _ = (K * e) * (K * e) := by ring
          _ ≤ (K * |x₀ - r|) ^ 2 ^ k * (K * |x₀ - r|) ^ 2 ^ k :=
            mul_le_mul ih2 ih2 (mul_nonneg hK he) ((mul_nonneg hK he).trans ih2)
    · have h0 : |newtonStep f f' x - r| ≤ 0 := hstep.trans (by nlinarith)
      have h0' : |newtonStep f f' x - r| = 0 := le_antisymm h0 (abs_nonneg _)
      refine ⟨by rw [h0']; exact hδ, ?_⟩
      rw [h0', mul_zero, pow_succ, pow_mul]
      positivity

/-- **Newton's iterates converge to the root.** Under the hypotheses of
`abs_newtonIterate_sub_le` with the strict `(M / (2 m)) δ < 1`, the iterates from any `x₀` with
`|x₀ − r| ≤ δ` converge to `r`. (The proof bounds their distance to `r` by `q ^ k δ` with
`q = max ((M / (2 m)) δ) 0`; that bound is not stated separately.) -/
theorem tendsto_newtonIterate {f f' : ℝ → ℝ} {M m r δ x₀ : ℝ}
    (hd : ∀ t ∈ Icc (r - δ) (r + δ), HasDerivAt f (f' t) t)
    (hL : ∀ t ∈ Icc (r - δ) (r + δ), ∀ u ∈ Icc (r - δ) (r + δ), |f' t - f' u| ≤ M * |t - u|)
    (hfr : f r = 0) (hm : 0 < m) (hm' : ∀ t ∈ Icc (r - δ) (r + δ), m ≤ |f' t|)
    (hMδ : M / (2 * m) * δ < 1) (hx₀ : |x₀ - r| ≤ δ) :
    Tendsto (fun k ↦ (newtonStep f f')^[k] x₀) atTop (𝓝 r) := by
  set K := M / (2 * m)
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hx₀
  have hmem : ∀ x, |x - r| ≤ δ → x ∈ Icc (r - δ) (r + δ) := fun x hx ↦ by
    rw [abs_le] at hx; constructor <;> linarith
  have hr : r ∈ Icc (r - δ) (r + δ) := hmem r (by simpa using hδ)
  set q := max (K * δ) 0
  have hq0 : 0 ≤ q := le_max_right _ _
  have hq1 : q < 1 := max_lt hMδ zero_lt_one
  have hbound : ∀ k, |(newtonStep f f')^[k] x₀ - r| ≤ q ^ k * δ := by
    intro k
    induction k with
    | zero => simpa using hx₀
    | succ k ih =>
      set x := (newtonStep f f')^[k] x₀
      have hin := (abs_newtonIterate_sub_le hd hL hfr hm hm' hMδ.le hx₀ k).1
      have hstep := abs_newtonStep_sub_le (convex_Icc _ _) hd hL (hmem x hin) hr hfr hm
        (hm' x (hmem x hin))
      rw [Function.iterate_succ_apply']
      set e := |x - r|
      have he : 0 ≤ e := abs_nonneg _
      have hsq : (x - r) ^ 2 = e * e := by rw [← sq_abs, sq]
      rw [hsq] at hstep
      have hKq : K * (e * e) ≤ q * e := by
        rcases le_or_gt 0 K with hK | hK
        · calc K * (e * e) = (K * e) * e := by ring
            _ ≤ (K * δ) * e := mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hin hK) he
            _ ≤ q * e := mul_le_mul_of_nonneg_right (le_max_left _ _) he
        · nlinarith [mul_nonneg hq0 he]
      calc |newtonStep f f' x - r| ≤ q * e := hstep.trans hKq
        _ ≤ q * (q ^ k * δ) := mul_le_mul_of_nonneg_left ih hq0
        _ = q ^ (k + 1) * δ := by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ (Real.norm_eq_abs _).trans_le (hbound k)) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const δ

end ClassicalLean.Analysis

open Set in
/-- The hypotheses of `abs_newtonStep_sub_le` hold together: `f t = t ^ 2 − 2` with derivative
`f' t = 2 t` on the convex set `[1, 2]`, where `|f' t − f' u| = 2 |t − u|` (`M = 2`); the start
`x = 2` and the root `r = √2` lie in it, `f r = 0`, and `|f' x| = 4 ≥ m = 2 > 0`. -/
example := ClassicalLean.Analysis.abs_newtonStep_sub_le (f := fun t ↦ t ^ 2 - 2)
  (f' := fun t ↦ 2 * t) (s := Icc 1 2) (M := 2) (m := 2) (x := 2) (r := Real.sqrt 2)
  (convex_Icc 1 2)
  (fun t _ ↦ by simpa using (hasDerivAt_pow 2 t).sub_const 2)
  (fun t _ u _ ↦ by rw [← mul_sub, abs_mul]; norm_num)
  (by norm_num)
  ⟨by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num,
    by rw [Real.sqrt_le_left (by norm_num)]; norm_num⟩
  (by simp) (by norm_num) (by norm_num)
