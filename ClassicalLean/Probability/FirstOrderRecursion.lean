/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The first-order recursion `x (t + 1) = a x t + e t`

Each step keeps the share `a` of the last value and adds fresh noise `e t`, independent of the
past value, with mean `0` and variance `s²`.

* `variance_mul_add`: for independent `X` and `E`, `Var[a X + E] = a² Var X + Var E`.
* `variance_succ`: so the variances satisfy `v (t + 1) = a² v t + s²`; `integral_eq_pow`: the
  means satisfy `E[x t] = a ^ t E[x 0]`.
* For that recursion of numbers, with `|a| < 1`: `eq_steady_iff` (`s² / (1 - a²)` is its only
  fixed point), `sub_steady_eq` (the distance to it shrinks by `a²` each step) and
  `tendsto_steady` (every start converges to it).
* `tendsto_atTop_of_one_le_abs`: for `|a| ≥ 1` and `s² > 0`, the variance grows without bound, so
  there is no steady state.
* `rpow_halfLife`, `rpow_add_halfLife_mul`: for `0 < a < 1`, a gap `a ^ t g` halves every
  `log (1/2) / log a` steps; `abs_le_abs_pow_mul`: for `|a| ≥ 1` it never shrinks.

## What Mathlib provides

`ProbabilityTheory.IndepFun.variance_add`, `variance_const_mul`, `IndepFun.comp`,
`tendsto_pow_atTop_nhds_zero_of_lt_one`, `Real.rpow_def_of_pos`. Mathlib has no autoregressive
process; independence of each step's noise from the current value is a hypothesis here.
-/

open MeasureTheory ProbabilityTheory Filter Topology Real

namespace ClassicalLean.Probability.FirstOrderRecursion

section Variance

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **One step of the variance.** For independent `X` and `E` with finite variances:
`Var[a X + E] = a² Var X + Var E`. For a trader: keeping the share `a` of yesterday's deviation and
adding independent noise gives a swing of `a²` times yesterday's plus the noise's own. -/
theorem variance_mul_add {X E : Ω → ℝ} (hX : MemLp X 2 μ) (hE : MemLp E 2 μ)
    (h : IndepFun X E μ) (a : ℝ) :
    variance (fun ω ↦ a * X ω + E ω) μ = a ^ 2 * variance X μ + variance E μ := by
  have hind : IndepFun (fun ω ↦ a * X ω) E μ :=
    h.comp (φ := fun x ↦ a * x) (ψ := id) (measurable_const_mul a) measurable_id
  rw [show (fun ω ↦ a * X ω + E ω) = (fun ω ↦ a * X ω) + E from rfl,
    hind.variance_add (hX.const_mul a) hE, variance_const_mul]

/-- The values of the recursion have finite variance when the start and the noise do. -/
theorem memLp_two {x e : ℕ → Ω → ℝ} {a : ℝ} (hx : ∀ t ω, x (t + 1) ω = a * x t ω + e t ω)
    (hx0 : MemLp (x 0) 2 μ) (he : ∀ t, MemLp (e t) 2 μ) : ∀ t, MemLp (x t) 2 μ := by
  intro t
  induction t with
  | zero => exact hx0
  | succ t ih =>
    rw [show x (t + 1) = fun ω ↦ a * x t ω + e t ω from funext (hx t)]
    exact (ih.const_mul a).add (he t)

/-- **The variance recursion.** If `x (t + 1) = a x t + e t`, the start and the noise have finite
variance, each `e t` is independent of `x t`, and `Var[e t] = s²`, then
`Var[x (t + 1)] = a² Var[x t] + s²`. -/
theorem variance_succ {x e : ℕ → Ω → ℝ} {a s : ℝ} (hx : ∀ t ω, x (t + 1) ω = a * x t ω + e t ω)
    (hx0 : MemLp (x 0) 2 μ) (he : ∀ t, MemLp (e t) 2 μ) (hind : ∀ t, IndepFun (x t) (e t) μ)
    (hvar : ∀ t, variance (e t) μ = s ^ 2) (t : ℕ) :
    variance (x (t + 1)) μ = a ^ 2 * variance (x t) μ + s ^ 2 := by
  rw [show x (t + 1) = fun ω ↦ a * x t ω + e t ω from funext (hx t),
    variance_mul_add (memLp_two hx hx0 he t) (he t) (hind t), hvar]

/-- **The mean decays geometrically.** If `x (t + 1) = a x t + e t` with integrable start and noise
of mean `0`, then `E[x t] = a ^ t E[x 0]`. For a trader: the expected gap from the long-run mean
shrinks by the factor `a` each step. -/
theorem integral_eq_pow {x e : ℕ → Ω → ℝ} {a : ℝ} (hx : ∀ t ω, x (t + 1) ω = a * x t ω + e t ω)
    (hx0 : Integrable (x 0) μ) (he : ∀ t, Integrable (e t) μ) (hmean : ∀ t, ∫ ω, e t ω ∂μ = 0)
    (t : ℕ) : ∫ ω, x t ω ∂μ = a ^ t * ∫ ω, x 0 ω ∂μ := by
  have hint : ∀ t, Integrable (x t) μ := by
    intro t
    induction t with
    | zero => exact hx0
    | succ t ih =>
      rw [show x (t + 1) = fun ω ↦ a * x t ω + e t ω from funext (hx t)]
      exact (ih.const_mul a).add (he t)
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show x (t + 1) = fun ω ↦ a * x t ω + e t ω from funext (hx t),
      integral_add ((hint t).const_mul a) (he t), integral_const_mul, hmean, ih]
    ring

end Variance

section Numbers

variable {v : ℕ → ℝ} {a s : ℝ}

/-- **The only steady state.** For `a² ≠ 1`, `q = a² q + s²` exactly when `q = s² / (1 - a²)`. -/
theorem eq_steady_iff (ha : a ^ 2 ≠ 1) (q : ℝ) : q = a ^ 2 * q + s ^ 2 ↔ q = s ^ 2 / (1 - a ^ 2) := by
  have h : 1 - a ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  rw [eq_div_iff h]
  constructor <;> intro h' <;> linarith

/-- **Distance to the steady state.** If `v (t + 1) = a² v t + s²` and `a² ≠ 1`, then
`v t - s² / (1 - a²) = (a²) ^ t (v 0 - s² / (1 - a²))`. -/
theorem sub_steady_eq (hv : ∀ t, v (t + 1) = a ^ 2 * v t + s ^ 2) (ha : a ^ 2 ≠ 1) (t : ℕ) :
    v t - s ^ 2 / (1 - a ^ 2) = (a ^ 2) ^ t * (v 0 - s ^ 2 / (1 - a ^ 2)) := by
  have h : 1 - a ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hv, pow_succ]
    have hq : s ^ 2 / (1 - a ^ 2) = a ^ 2 * (s ^ 2 / (1 - a ^ 2)) + s ^ 2 :=
      (eq_steady_iff ha _).mpr rfl
    calc a ^ 2 * v t + s ^ 2 - s ^ 2 / (1 - a ^ 2)
        = a ^ 2 * (v t - s ^ 2 / (1 - a ^ 2)) := by linarith
      _ = _ := by rw [ih]; ring

/-- **The steady-state variance.** If `v (t + 1) = a² v t + s²` and `|a| < 1`, then `v t` tends to
`s² / (1 - a²)` from any start. For a trader: a mean-reverting quantity with step noise `s` settles
to a spread of `s² / (1 - a²)`, whatever its first value. -/
theorem tendsto_steady (hv : ∀ t, v (t + 1) = a ^ 2 * v t + s ^ 2) (ha : |a| < 1) :
    Tendsto v atTop (𝓝 (s ^ 2 / (1 - a ^ 2))) := by
  have ha2 : a ^ 2 < 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg a]
  have hlim : Tendsto (fun t ↦ (a ^ 2) ^ t * (v 0 - s ^ 2 / (1 - a ^ 2)) + s ^ 2 / (1 - a ^ 2))
      atTop (𝓝 (0 * (v 0 - s ^ 2 / (1 - a ^ 2)) + s ^ 2 / (1 - a ^ 2))) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg a) ha2).mul_const _).add_const _
  rw [zero_mul, zero_add] at hlim
  refine hlim.congr fun t ↦ ?_
  rw [← sub_steady_eq hv ha2.ne]; ring

/-- **No steady state when `|a| ≥ 1`.** If `v (t + 1) = a² v t + s²` with `|a| ≥ 1`, `s ≠ 0` and
`v 0 ≥ 0`, then `v t ≥ v 0 + t s²`, so `v t` grows without bound. For a trader: a quantity that
does not pull back towards its mean (`|a| ≥ 1`) has an ever-growing spread. -/
theorem tendsto_atTop_of_one_le_abs (hv : ∀ t, v (t + 1) = a ^ 2 * v t + s ^ 2) (ha : 1 ≤ |a|)
    (hs : s ≠ 0) (h0 : 0 ≤ v 0) : Tendsto v atTop atTop := by
  have ha2 : 1 ≤ a ^ 2 := by rw [← sq_abs]; nlinarith
  have hs2 : 0 < s ^ 2 := by positivity
  have key : ∀ t : ℕ, v 0 + t * s ^ 2 ≤ v t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hvt : 0 ≤ v t := by nlinarith [ih, (Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
      rw [hv]; push_cast; nlinarith
  refine tendsto_atTop_mono key ?_
  exact tendsto_atTop_add_const_left _ _
    (tendsto_natCast_atTop_atTop.atTop_mul_const hs2)

end Numbers

section HalfLife

/-- The number of steps over which `a ^ t` halves: `log (1/2) / log a`. -/
noncomputable def halfLife (a : ℝ) : ℝ := log (1 / 2) / log a

/-- **The half-life is positive** for `0 < a < 1`. -/
theorem halfLife_pos {a : ℝ} (h0 : 0 < a) (h1 : a < 1) : 0 < halfLife a :=
  div_pos_of_neg_of_neg (log_neg (by norm_num) (by norm_num)) (log_neg h0 h1)

/-- **`a` to the power of the half-life is `1/2`.** For `0 < a < 1`:
`a ^ (log (1/2) / log a) = 1/2`. -/
theorem rpow_halfLife {a : ℝ} (h0 : 0 < a) (h1 : a < 1) : a ^ halfLife a = 1 / 2 := by
  rw [rpow_def_of_pos h0, halfLife, mul_div_cancel₀ _ (log_neg h0 h1).ne, exp_log (by norm_num)]

/-- **A gap halves every half-life.** For `0 < a < 1`, any time `t ≥ 0` and any gap `g`:
`a ^ (t + log (1/2) / log a) g = (1/2) a ^ t g`. For a trader: under mean reversion with factor
`a`, a deviation from the mean is expected to halve every `log (1/2) / log a` steps, from any
moment (about 6.6 steps for `a = 0.9`). -/
theorem rpow_add_halfLife_mul {a : ℝ} (h0 : 0 < a) (h1 : a < 1) (t g : ℝ) :
    a ^ (t + halfLife a) * g = 1 / 2 * (a ^ t * g) := by
  rw [rpow_add h0, rpow_halfLife h0 h1]; ring

/-- **Without `|a| < 1` a gap never shrinks.** For `|a| ≥ 1`: `|g| ≤ |a ^ t g|` for every step
count `t`. For a trader: with `|a| ≥ 1` there is no pull back to the mean and no half-life. -/
theorem abs_le_abs_pow_mul {a : ℝ} (ha : 1 ≤ |a|) (g : ℝ) (t : ℕ) : |g| ≤ |a ^ t * g| := by
  rw [abs_mul, abs_pow]
  exact le_mul_of_one_le_left (abs_nonneg g) (one_le_pow₀ ha)

end HalfLife

end ClassicalLean.Probability.FirstOrderRecursion
