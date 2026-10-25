/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import ClassicalLean.Probability.FirstOrderRecursion

/-!
# The error variance of the scalar Kalman filter

A quantity `x` moves by `x ↦ a x + w`, where the noise `w` has variance `q`, and is observed as
`z = h x + v`, where the noise `v` has variance `r`. The Kalman filter's error variance before
each observation, `P`, then moves by one step of the Riccati recursion

    riccatiStep a h q r P = a² r P / (h² P + r) + q

(the observation shrinks `P` to `P r / (h² P + r)`; the next move multiplies by `a²` and adds `q`).
That reading as a filter is the standard one and is not proved here: this file is about the
recursion of real numbers. Citation: Kalman 1960, "A New Approach to Linear Filtering and
Prediction Problems".

Order LEAN-22 (item 42 of the plan) proves that the recursion settles, from every start `P ≥ 0`,
at the positive root of its Riccati equation `h² P² − (q h² + a² r − r) P − q r = 0`:

* `riccatiRoot a h q r`, that root, written with a square root; `riccatiRoot_pos`,
  `riccati_equation_riccatiRoot` (it solves the equation) and `riccatiStep_riccatiRoot` (it is a
  fixed point);
* `riccatiRate a h q r = a² r / (h² R + r)`, where `R` is the root, written `c` below;
  `abs_riccatiStep_sub_le`: one step multiplies the distance to the root by at most `c`;
  `riccatiRate_lt_one`: `c < 1`, since `R (1 − c) = q > 0`;
* `abs_riccatiStep_iterate_sub_le`: after `n` steps the distance is at most `cⁿ |P − R|`;
* `tendsto_riccatiStep`: the iterates converge to `R`; `eq_riccatiRoot_of_riccatiStep_eq`: `R` is
  the only fixed point at or above `0`.

Order LEAN-35 (item 114 of MATH-PLAN-library-2) adds:

* `riccatiRoot_eq_steady` — **the steady Kalman filter of a local level.** For `a = h = 1`, with
  the steady gain `K = R / (R + r)`, the root is `R = (q + K² r) / (1 − (1 − K)²)`: the steady
  value of a first-order variance recursion with coefficient `1 − K`
  (`FirstOrderRecursion.eq_steady_iff`, which this module now imports). Only this equation is
  proved, not the filter itself. The proof is the draft `d114-r1-s2` (written by Claude Opus 5.5
  through the Anthropic Batch API, the lane's API-CREDIT-1 work), adapted by order LEAN-35's
  session: moved inside this namespace (the draft's `open ClassicalLean.Probability` dropped), and
  its docstring rewritten (the item, the credit, every letter defined, the filter marked as a
  reading); the proof is unchanged. Its witness is at the end of the file.

## When the iteration really converges

The theorems assume `q > 0`, `r ≥ 0`, `h ≠ 0` and a start `P ≥ 0`, and need nothing of `a`.
Measured in order LEAN-22's checks (check C42, exact arithmetic): on 104 parameter sets whose
square root is rational (44 of them with `r > 0`; at `r = 0` each step is the constant `q`), the
root is positive, solves the equation and is fixed, `c < 1`, and `|P_n − R| ≤ cⁿ |P_0 − R|` for 12
steps from 4 starts. Each assumption is needed; drop it alone and the conclusion fails at the case
given:

* `q > 0`: `q = 0`, `a = 2`, `h = 1`, `r = 1`, `P = 0`: the iterates stay at `0`, the formula's
  root is `3`. With no noise in the motion, a variance of `0` stays `0`. Only the start `P = 0`
  needs `q > 0`: with `q = 0` and `P > 0` the iterates still reach the formula's root (float
  check, 2000 random cases with `|a² − 1| ≥ 0.2`; observed in review r42, not proved here).
* `r ≥ 0`: `a = 0`, `h = 1`, `q = 1`, `r = −2`, `P = 0`: the iterates are `1`, the root `2`.
  (Seeded float search in the checks, `a, h ∈ [−3, 3]`, `q ∈ [0.01, 3]`, `r ∈ [−3, −0.01]`,
  `P ∈ [0, 5]`, 400 steps: 14,531 of 20,000 cases fail.)
* `h ≠ 0`: `h = 0`, `a = 1`, `q = 1`, `r = 1`, `P = 0`: each step adds `1`, so the iterates
  `0, 1, 2, …` grow without bound (Lean's root is `(…) / 0 = 0`). With no observation and
  `r ≠ 0` the recursion is `P ↦ a² P + q`.
* `P ≥ 0`: `a = 1`, `h = 1`, `r = 1`, `q = 9/4`: `P = −3/4` is a fixed point, and the root is `3`;
  the same case shows that uniqueness needs `P ≥ 0`.

Not needed: `r > 0`. At `r = 0` (an exact observation) each step gives `q` and the root is `q`,
so the theorems hold there too and are stated with `r ≥ 0`.

## What Mathlib provides

No Kalman filter and no Riccati equation: `kalman|riccati` has 0 hits in Mathlib v4.34.0 (order
LEAN-22's search). Used: `Real.sqrt`, `Real.lt_sqrt_of_sq_lt`,
`tendsto_pow_atTop_nhds_zero_of_lt_one`. The proof is a contraction estimate, not the
monotone-limit argument named in the plan's row.
-/

open Filter Topology

namespace ClassicalLean.Probability

/-- One step of the scalar Riccati recursion: `a² r P / (h² P + r) + q`. -/
noncomputable def riccatiStep (a h q r P : ℝ) : ℝ := a ^ 2 * r * P / (h ^ 2 * P + r) + q

/-- The positive root of `h² P² − (q h² + a² r − r) P − q r = 0`, by the quadratic formula. -/
noncomputable def riccatiRoot (a h q r : ℝ) : ℝ :=
  (q * h ^ 2 + a ^ 2 * r - r + √((q * h ^ 2 + a ^ 2 * r - r) ^ 2 + 4 * h ^ 2 * q * r)) /
    (2 * h ^ 2)

/-- The contraction factor `a² r / (h² R + r)` at the root `R`. -/
noncomputable def riccatiRate (a h q r : ℝ) : ℝ := a ^ 2 * r / (h ^ 2 * riccatiRoot a h q r + r)

/-- `riccatiRoot` solves the Riccati equation `h² R² − (q h² + a² r − r) R − q r = 0`. -/
theorem riccati_equation_riccatiRoot {a h q r : ℝ} (hh : h ≠ 0) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    h ^ 2 * riccatiRoot a h q r ^ 2 - (q * h ^ 2 + a ^ 2 * r - r) * riccatiRoot a h q r - q * r
      = 0 := by
  set B := q * h ^ 2 + a ^ 2 * r - r
  have hD : 0 ≤ B ^ 2 + 4 * h ^ 2 * q * r := by positivity
  set s := √(B ^ 2 + 4 * h ^ 2 * q * r)
  have hs : s ^ 2 = B ^ 2 + 4 * h ^ 2 * q * r := Real.sq_sqrt hD
  have hh2 : 0 < h ^ 2 := by positivity
  set R := riccatiRoot a h q r
  have hR : 2 * h ^ 2 * R = B + s := by
    change 2 * h ^ 2 * ((B + s) / (2 * h ^ 2)) = B + s
    field_simp
  have h4 : 4 * h ^ 2 * (h ^ 2 * R ^ 2 - B * R - q * r) = 0 := by
    linear_combination (2 * h ^ 2 * R + s - B) * hR + hs
  rcases mul_eq_zero.mp h4 with h0 | h0
  · exact absurd h0 (by positivity)
  · exact h0

/-- The root is positive when `q > 0`, `r ≥ 0` and `h ≠ 0`. -/
theorem riccatiRoot_pos {a h q r : ℝ} (hq : 0 < q) (hr : 0 ≤ r) (hh : h ≠ 0) :
    0 < riccatiRoot a h q r := by
  have hh2 : 0 < h ^ 2 := by positivity
  unfold riccatiRoot
  refine div_pos ?_ (by positivity)
  set B := q * h ^ 2 + a ^ 2 * r - r
  rcases le_or_gt B 0 with hB | hB
  · have hr' : 0 < r := by
      rcases hr.eq_or_lt with h0 | h0
      · subst h0
        simp only [B, mul_zero, sub_zero, add_zero] at hB
        nlinarith [mul_pos hq hh2]
      · exact h0
    have : -B < √(B ^ 2 + 4 * h ^ 2 * q * r) :=
      Real.lt_sqrt_of_sq_lt (by nlinarith [mul_pos (mul_pos hh2 hq) hr'])
    linarith
  · have := Real.sqrt_nonneg (B ^ 2 + 4 * h ^ 2 * q * r)
    linarith

/-- The root is a fixed point of the recursion. -/
theorem riccatiStep_riccatiRoot {a h q r : ℝ} (hq : 0 < q) (hr : 0 ≤ r) (hh : h ≠ 0) :
    riccatiStep a h q r (riccatiRoot a h q r) = riccatiRoot a h q r := by
  have hR := riccatiRoot_pos (a := a) hq hr hh
  have hE := riccati_equation_riccatiRoot (a := a) hh hq.le hr
  have hden : 0 < h ^ 2 * riccatiRoot a h q r + r := by positivity
  unfold riccatiStep
  rw [div_add' _ _ _ hden.ne', div_eq_iff hden.ne']
  linear_combination -hE

/-- From `P ≥ 0`, one step lands above `0`. -/
theorem riccatiStep_pos {a h q r P : ℝ} (hq : 0 < q) (hr : 0 ≤ r) (hP : 0 ≤ P) :
    0 < riccatiStep a h q r P := by
  unfold riccatiStep
  have : 0 ≤ a ^ 2 * r * P / (h ^ 2 * P + r) := by positivity
  linarith

/-- The contraction factor is at least `0`. -/
theorem riccatiRate_nonneg {a h q r : ℝ} (hq : 0 < q) (hr : 0 ≤ r) (hh : h ≠ 0) :
    0 ≤ riccatiRate a h q r := by
  have := riccatiRoot_pos (a := a) hq hr hh
  unfold riccatiRate
  positivity

/-- The contraction factor `c = a² r / (h² R + r)` is below `1`: the fixed point gives
`R (1 − c) = q > 0`. -/
theorem riccatiRate_lt_one {a h q r : ℝ} (hq : 0 < q) (hr : 0 ≤ r) (hh : h ≠ 0) :
    riccatiRate a h q r < 1 := by
  unfold riccatiRate
  have hR := riccatiRoot_pos (a := a) hq hr hh
  have hfix := riccatiStep_riccatiRoot (a := a) hq hr hh
  unfold riccatiStep at hfix
  rw [mul_div_right_comm] at hfix
  by_contra hc
  push Not at hc
  nlinarith

/-- One step from `P ≥ 0` multiplies the distance to the root by at most
`c = a² r / (h² R + r)`. -/
theorem abs_riccatiStep_sub_le {a h q r P : ℝ} (hq : 0 < q) (hr : 0 ≤ r) (hh : h ≠ 0)
    (hP : 0 ≤ P) :
    |riccatiStep a h q r P - riccatiRoot a h q r| ≤
      riccatiRate a h q r * |P - riccatiRoot a h q r| := by
  unfold riccatiRate
  set R := riccatiRoot a h q r
  have hR : 0 < R := riccatiRoot_pos hq hr hh
  have hfix : riccatiStep a h q r R = R := riccatiStep_riccatiRoot hq hr hh
  rcases hr.eq_or_lt with h0 | hr'
  · subst h0
    have h1 : riccatiStep a h q 0 P = q := by simp [riccatiStep]
    have h2 : R = q := by rw [← hfix]; simp [riccatiStep]
    rw [h1, h2, sub_self, abs_zero]
    simp
  · have hdP : 0 < h ^ 2 * P + r := by positivity
    have hdR : 0 < h ^ 2 * R + r := by positivity
    have e : riccatiStep a h q r P - R =
        a ^ 2 * r / (h ^ 2 * R + r) * (r / (h ^ 2 * P + r)) * (P - R) := by
      rw [show riccatiStep a h q r P - R = riccatiStep a h q r P - riccatiStep a h q r R by
        rw [hfix]]
      unfold riccatiStep
      field_simp
      ring
    rw [e, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ a ^ 2 * r / (h ^ 2 * R + r)),
      abs_of_nonneg (by positivity : 0 ≤ r / (h ^ 2 * P + r))]
    have hle : r / (h ^ 2 * P + r) ≤ 1 := by
      rw [div_le_one hdP]; nlinarith [sq_nonneg h]
    have h3 : 0 ≤ a ^ 2 * r / (h ^ 2 * R + r) := by positivity
    calc a ^ 2 * r / (h ^ 2 * R + r) * (r / (h ^ 2 * P + r)) * |P - R|
        ≤ a ^ 2 * r / (h ^ 2 * R + r) * 1 * |P - R| := by gcongr
      _ = _ := by ring

/-- After `n` steps from `P ≥ 0`, the distance to the root is at most `cⁿ |P − R|`. -/
theorem abs_riccatiStep_iterate_sub_le {a h q r P : ℝ} (hq : 0 < q) (hr : 0 ≤ r) (hh : h ≠ 0)
    (hP : 0 ≤ P) (n : ℕ) :
    |(riccatiStep a h q r)^[n] P - riccatiRoot a h q r| ≤
      riccatiRate a h q r ^ n * |P - riccatiRoot a h q r| := by
  induction n generalizing P with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have hP' := (riccatiStep_pos (a := a) (h := h) hq hr hP).le
    calc _ ≤ _ := ih hP'
      _ ≤ riccatiRate a h q r ^ n * (riccatiRate a h q r * |P - riccatiRoot a h q r|) := by
          have := riccatiRate_nonneg (a := a) hq hr hh
          gcongr
          exact abs_riccatiStep_sub_le hq hr hh hP
      _ = _ := by ring

/-- **The Riccati recursion settles.** From every start `P ≥ 0`, the iterates of the Riccati
recursion converge to the positive root of the Riccati equation. -/
theorem tendsto_riccatiStep {a h q r P : ℝ} (hq : 0 < q) (hr : 0 ≤ r) (hh : h ≠ 0) (hP : 0 ≤ P) :
    Tendsto (fun n ↦ (riccatiStep a h q r)^[n] P) atTop (𝓝 (riccatiRoot a h q r)) := by
  have hc0 := riccatiRate_nonneg (a := a) hq hr hh
  have hc1 := riccatiRate_lt_one (a := a) hq hr hh
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ abs_riccatiStep_iterate_sub_le hq hr hh hP n)
    ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const |P - riccatiRoot a h q r|

/-- The root is the only fixed point at or above `0`. -/
theorem eq_riccatiRoot_of_riccatiStep_eq {a h q r P : ℝ} (hq : 0 < q) (hr : 0 ≤ r) (hh : h ≠ 0)
    (hP : 0 ≤ P) (hfix : riccatiStep a h q r P = P) : P = riccatiRoot a h q r := by
  have h1 := abs_riccatiStep_sub_le (a := a) hq hr hh hP
  rw [hfix] at h1
  have hc1 := riccatiRate_lt_one (a := a) hq hr hh
  have h2 := abs_nonneg (P - riccatiRoot a h q r)
  have : |P - riccatiRoot a h q r| = 0 := by nlinarith
  linarith [abs_eq_zero.mp this]

/-- **The steady Kalman filter of a local level** (item 114 of MATH-PLAN-library-2; the draft
`d114-r1-s2`, written by Claude Opus 5.5 through the Anthropic Batch API, the lane's API-CREDIT-1
work, adapted by order LEAN-35's session). Take the state factor `a = 1` and the observation gain
`h = 1` (the first two arguments of `riccatiRoot`), motion noise of variance `q > 0` and
observation noise of variance `r ≥ 0`; let `P = riccatiRoot 1 1 q r` (read as the filter's steady
error variance) and `K = P / (P + r)` (read as its steady gain). Then
`P = (q + K² r) / (1 − (1 − K)²)`: by `FirstOrderRecursion.eq_steady_iff`, `P` is the steady value
`s² / (1 − c²)` of the first-order recursion `V ↦ c² V + s²` of a variance `V`, with coefficient
`c = 1 − K` and `s² = q + K² r`. Read as the filter, that is the recursion of the error
`e ↦ (1 − K) e + w − K v`, where `w` is the motion's noise and `v` the observation's,
uncorrelated; that reading, and the filter itself (exponential smoothing with constant `K`), are
not stated or proved here: only the equation is. -/
theorem riccatiRoot_eq_steady {q r : ℝ} (hq : 0 < q) (hr : 0 ≤ r) :
    riccatiRoot 1 1 q r =
      (q + (riccatiRoot 1 1 q r / (riccatiRoot 1 1 q r + r)) ^ 2 * r) /
        (1 - (1 - riccatiRoot 1 1 q r / (riccatiRoot 1 1 q r + r)) ^ 2) := by
  have hP := riccatiRoot_pos (a := 1) (h := 1) hq hr one_ne_zero
  have hE := riccati_equation_riccatiRoot (a := 1) (h := 1) one_ne_zero hq.le hr
  generalize riccatiRoot 1 1 q r = P at hP hE ⊢
  have hD : 0 < P + r := by linarith
  generalize hK' : P / (P + r) = K
  have hK : K * (P + r) = P := by rw [← hK', div_mul_cancel₀ _ hD.ne']
  have hK0 : 0 < K := by rw [← hK']; exact div_pos hP hD
  have hK1 : K ≤ 1 := by rw [← hK', div_le_one hD]; linarith
  have ha : (1 - K) ^ 2 ≠ 1 := by
    have : (1 - K) ^ 2 < 1 := by
      nlinarith [mul_pos hK0 (by linarith : (0:ℝ) < 2 - K)]
    exact this.ne
  have hs : √(q + K ^ 2 * r) ^ 2 = q + K ^ 2 * r :=
    Real.sq_sqrt (add_nonneg hq.le (mul_nonneg (sq_nonneg K) hr))
  have key : (P - (1 - K) ^ 2 * P - (q + K ^ 2 * r)) * (P + r) ^ 2 = 0 := by
    linear_combination
      (P * (2 * (P + r) - K * (P + r) - P) - r * (K * (P + r) + P)) * hK + (P + r) * hE
  have hfix : P = (1 - K) ^ 2 * P + √(q + K ^ 2 * r) ^ 2 := by
    rcases mul_eq_zero.mp key with h0 | h0
    · rw [hs]; linarith
    · exact absurd h0 (pow_ne_zero 2 hD.ne')
  have := (FirstOrderRecursion.eq_steady_iff ha P).mp hfix
  rwa [hs] at this

end ClassicalLean.Probability

/-- The hypotheses of `tendsto_riccatiStep` hold together: state factor `a = 1/2`, observation
gain `h = 1 ≠ 0`, process noise `q = 1 > 0`, observation noise `r = 1 ≥ 0` (not `0`), and the
starting error variance `P = 1 ≥ 0` (not `0`). -/
example := ClassicalLean.Probability.tendsto_riccatiStep (a := 1 / 2) (h := 1) (q := 1) (r := 1)
  (P := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The hypotheses of `riccatiRoot_eq_steady` hold together: motion noise of variance `q = 1 > 0`
and observation noise of variance `r = 1 ≥ 0`, away from the boundary `r = 0`. -/
example := ClassicalLean.Probability.riccatiRoot_eq_steady (q := 1) (r := 1) (by norm_num)
  (by norm_num)
