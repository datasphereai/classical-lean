/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The descent lemma, gradient descent (also under PL, and projected), and KKT for convex problems

Throughout, `f` is a real function on a real Hilbert space `E` (a complete inner product space,
which Mathlib's `HasGradientAt` asks for). "The gradient is `L`-Lipschitz" is
`LipschitzWith L f'` for a function `f'` with `HasGradientAt f (f' x) x` at every `x`; a gradient
step of length `1 / L` is `x - (1 / L) • f' x`.

* `le_add_inner_gradient_add_sq` — the descent lemma: with an `L`-Lipschitz gradient,
  `f y ≤ f x + ⟪f' x, y - x⟫ + (L / 2) ‖y - x‖²`; and `le_sub_of_gradientStep`, so one step of
  length `1 / L` lowers `f` by at least `‖f' x‖² / (2 L)`.
* `add_inner_gradient_le` — a convex function lies above its tangent planes,
  `f x + ⟪f', y - x⟫ ≤ f y`, on any convex set and with the gradient needed only at `x`.
* `sub_le_sq_sub_sq_of_gradientStep`, `mul_sub_le_of_gradientStep`, `sub_le_of_gradientStep` —
  gradient descent at rate `1 / k` for convex `f`, derived here (compare the step-`1 / L` case
  of Nesterov 2004, Theorem 2.1.14, which gives `2 L ‖x 0 - x*‖² / (k + 4)`):
  `f (x k) - f z ≤ L ‖x 0 - z‖² / (2 k)` for every point `z`.
* `add_inner_gradient_add_sq_le` — the tangent-plane inequality for an `m`-strongly convex `f`
  (Mathlib's `StrongConvexOn`), with `(m / 2) ‖y - x‖²` added; and `dist_gradientStep_le`, so
  gradient descent reaches the minimiser at the geometric rate
  `dist (x k) xs ² ≤ (1 - m / L) ^ k · dist (x 0) xs ²`.
* `isMinOn_of_kkt` — the Karush–Kuhn–Tucker conditions (stationarity, multipliers at least `0`,
  complementary slackness) make a point a minimiser of a convex problem with convex inequality
  constraints. Mathlib lists the KKT theorem as a TODO (`Analysis/Calculus/LagrangeMultipliers`);
  this is the sufficiency half for convex problems, not the necessity half, which needs a
  constraint qualification such as Slater's condition.
* `sub_le_pow_mul_of_polyakLojasiewicz` — item 112 of MATH-PLAN-library-2 (order LEAN-33):
  **linear convergence of gradient descent under the Polyak–Łojasiewicz inequality.** If
  `‖∇f x‖² / 2 ≥ μ (f x − f*)` for every `x`, `f*` is a lower bound of `f`, and the gradient is
  `L`-Lipschitz, then gradient descent with step `1 / L` satisfies
  `f (x k) − f* ≤ (1 − μ / L) ^ k (f (x 0) − f*)`, with nothing asked of `μ` or `L`. The proof is
  the draft `d112-r1-s2` (written by Claude Opus 5.5 through the Anthropic Batch API, the lane's
  API-CREDIT-1 work), adapted by order LEAN-33's session: inside this namespace.
* `sub_le_of_projGradientStep` — item 134 (order LEAN-33): **projected gradient descent on a convex
  set.** Each iterate is a nearest point of `K` to the plain gradient step, and the rate `1 / k` of
  unconstrained gradient descent persists: `f (x k) - f z ≤ L ‖x 0 - z‖² / (2 k)` for `z ∈ K`; with
  the private one-step lemma `projStep_aux`. Wider than the plan's row, which asks for a closed
  convex set: closedness is never used, since each step's nearest-point property is a hypothesis
  (closedness is what makes such points exist). The proof is the draft `d134-r1-s1` (as above),
  adapted by order LEAN-33's session: inside this namespace with the module's `variable` line, and
  its unused `IsClosed K` removed.

The proofs go through one variable: along the segment from `x` to `y`, `t ↦ f (x + t (y - x))`
has derivative `⟪f' (x + t (y - x)), y - x⟫` (`hasDerivAt_comp_add_smul_sub`) and is convex when
`f` is (`convexOn_comp_add_smul_sub`); Mathlib's `ConvexOn.le_slope_of_hasDerivAt` and
`antitoneOn_of_hasDerivWithinAt_nonpos` do the rest.

## Hypotheses

These checks are order LEAN-19's and cover the results above `sub_le_pow_mul_of_polyakLojasiewicz`;
items 112 and 134 (order LEAN-33) were not measured this way (their hypotheses are discussed in
their docstrings).

Measured in order LEAN-19's checks (checks C17 to C20, exact rationals): the statements hold on
quadratics in one to three variables (convex, strongly convex, and for the descent lemma also
not convex), for `k` up to 8 steps, and the KKT statement on 347 random convex problems in one
variable. Each hypothesis below fails when dropped alone, the others kept:

* The descent lemma: the Lipschitz gradient (`f = x⁴`, `L = 1`, `x = 0`, `y = 1`: `1 > 1/2`) and
  the gradient (`f = x²` with `f' = 0`, `L = 0`: `1 > 0`). For one step, the gradient
  (`f = x²/2` with `f' = -x`, `L = 1`, `x = 1`: `2 > 0`) and the Lipschitz constant (`f = x²` with
  `L = 1`, `x = 1`: `1 > -1`).
* The tangent plane: convexity (`f = -x²`, `x = 0`, `y = 1`), `x ∈ s` and `y ∈ s` (`f = x³`,
  convex on `[0, 1]`, at `x = -1` or `y = -1`), and the gradient (`f = x²` with `f' = 1` at `0`,
  `y = 1/2`: `1/2 > 1/4`). For the strongly convex form: strong convexity (`f = x²` read with
  `m = 4`, `x = 0`, `y = 1`: `2 > 1`), `x ∈ s` and `y ∈ s` (`f = x³`, `m = 0`) and the gradient
  (as above).
* One step against any point (`sub_le_sq_sub_sq_of_gradientStep`): `0 < L` (`f = x`, `L = 0`,
  `x = 0`, `z = -1`: `1 > 0`), convexity (`f = -x²/2`, `L = 1`, `x = 1`, `z = 10`: `48 > 17/2`),
  the gradient (`f = x²/2` with `f' = 0`, `x = 1`, `z = 0`: `1/2 > 0`) and the Lipschitz constant
  (`f = x²` with `L = 1`, `x = 1`, `z = 0`: `1 > 0`).
* The rate `1 / k`: `0 < L` (`f = x`, `L = 0`, so Lean's step `0⁻¹` does not move, `x 0 = 0`,
  `z = -1`: `1 > 0`), convexity (`f = -x²/2`, `L = 1`, `x 0 = 1`, `z = 10`: `48 > 81/2`), the
  step rule, the gradient and the Lipschitz constant (each with an exact case in the checks).
* The geometric rate: `0 ≤ m` (`f = -x²/2`, which is `(-1)`-strongly convex, `L = 1`,
  `x 0 = 1`: `4 > 2`), strong convexity (`f = 0` read with `m = 1/2`: `1 > 1/2`), the gradient,
  the Lipschitz constant, the step rule, and `f' xs = 0` (`f = x²/2`, `xs = 1`: `1 > 0`).
* KKT: convexity of `f` (`f = -x²`) and of the constraints (`f = x`, `g = -x² - 2x`, `xbar = 0`,
  `w = 1/2`: the point `-3` satisfies the constraint and `f (-3) = -3 < 0`), `w ≥ 0`, complementary
  slackness, both gradients and stationarity (each `f = x` with one constraint or none, and the
  point `-1`).

Not needed, and so not assumed: `0 < L` for one step and for the geometric rate (at `L = 0` the
step does not move and both statements hold); feasibility of `xbar` for KKT.

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-19, `grep -rniE` over Mathlib): `descent lemma`,
`gradient descent`, `lipschitz gradient` 0 (2 unrelated hits); a Lipschitz gradient in any
statement 0; `ConvexOn` beside `fderiv`, `gradient` or `inner` 0; a convergence rate 0;
`karush|kuhn|tucker|KKT` only the TODO and authors' names. Mathlib has the one-variable slope and
derivative lemmas for convex functions (`Analysis/Convex/Deriv.lean`), `StrongConvexOn`
(`Analysis/Convex/Strong.lean`), and, for one variable without constraints, that a convex
function with right derivative `0` at an interior point is minimal there
(`ConvexOn.isMinOn_of_rightDeriv_eq_zero`).
-/

open Finset
open scoped RealInnerProductSpace NNReal

namespace ClassicalLean.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The derivative along a segment: if `f` has gradient `f'` at `x + t (y - x)`, then
`t ↦ f (x + t (y - x))` has derivative `⟪f', y - x⟫` at `t`. A helper for the theorems below. -/
theorem hasDerivAt_comp_add_smul_sub {f : E → ℝ} {f' x y : E} {t : ℝ}
    (hf : HasGradientAt f f' (x + t • (y - x))) :
    HasDerivAt (fun t : ℝ ↦ f (x + t • (y - x))) ⟪f', y - x⟫ t := by
  have hl : HasDerivAt (fun t : ℝ ↦ x + t • (y - x)) (y - x) t := by
    simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
  have h := (hasGradientAt_iff_hasFDerivAt.mp hf).comp_hasDerivAt t hl
  exact h.congr_deriv (by simp [InnerProductSpace.toDual_apply_apply])

omit [CompleteSpace E] in
/-- A convex function stays convex along a segment: if `f` is convex on `s` and `x, y ∈ s`, then
`t ↦ f (x + t (y - x))` is convex on `[0, 1]`. A helper for the theorems below. -/
theorem convexOn_comp_add_smul_sub {f : E → ℝ} {x y : E} {s : Set E} (hf : ConvexOn ℝ s f)
    (hx : x ∈ s) (hy : y ∈ s) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t : ℝ ↦ f (x + t • (y - x))) := by
  have hseg : Set.Icc (0 : ℝ) 1 ⊆ (AffineMap.lineMap (k := ℝ) x y) ⁻¹' s := fun t ht ↦
    hf.1.lineMap_mem hx hy ⟨ht.1, ht.2⟩
  have hφ := (hf.comp_affineMap (AffineMap.lineMap (k := ℝ) x y)).subset hseg (convex_Icc 0 1)
  have heq : (f ∘ AffineMap.lineMap (k := ℝ) x y) = fun t : ℝ ↦ f (x + t • (y - x)) := by
    funext t; simp [AffineMap.lineMap_apply_module', add_comm]
  rwa [heq] at hφ

/-- **A convex function lies above its tangent planes.** If `f` is convex on `s`, `x` and `y` are
in `s`, and `f` has gradient `f'` at `x`, then `f x + ⟪f', y - x⟫ ≤ f y`. The gradient is needed
only at `x`. -/
theorem add_inner_gradient_le {f : E → ℝ} {f' x y : E} {s : Set E} (hf : ConvexOn ℝ s f)
    (hx : x ∈ s) (hy : y ∈ s) (hf' : HasGradientAt f f' x) :
    f x + ⟪f', y - x⟫ ≤ f y := by
  have hd : HasDerivAt (fun t : ℝ ↦ f (x + t • (y - x))) ⟪f', y - x⟫ 0 :=
    hasDerivAt_comp_add_smul_sub (by simpa using hf')
  have := (convexOn_comp_add_smul_sub hf hx hy).le_slope_of_hasDerivAt (by simp) (by simp)
    (by norm_num : (0 : ℝ) < 1) hd
  simp [slope_def_field] at this
  linarith

/-- **The descent lemma.** If `f` has gradient `f' x` at every `x` and the gradient is
`L`-Lipschitz, then `f` lies below the parabola that touches it at `x`:
`f y ≤ f x + ⟪f' x, y - x⟫ + (L / 2) ‖y - x‖²`. No convexity is needed. -/
theorem le_add_inner_gradient_add_sq {f : E → ℝ} {f' : E → E} {L : ℝ≥0}
    (hf : ∀ x, HasGradientAt f (f' x) x) (hL : LipschitzWith L f') (x y : E) :
    f y ≤ f x + ⟪f' x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  let g : ℝ → ℝ := fun t ↦ f (x + t • (y - x)) - t * ⟪f' x, y - x⟫ - L / 2 * t ^ 2 * ‖y - x‖ ^ 2
  let g' : ℝ → ℝ := fun t ↦ ⟪f' (x + t • (y - x)), y - x⟫ - ⟪f' x, y - x⟫ - L * t * ‖y - x‖ ^ 2
  have hg : ∀ t, HasDerivAt g (g' t) t := by
    intro t
    have h1 := hasDerivAt_comp_add_smul_sub (hf (x + t • (y - x)))
    have h2 := ((hasDerivAt_id t).mul_const ⟪f' x, y - x⟫)
    have h3 := (((hasDerivAt_id t).pow 2).const_mul (L / 2 : ℝ)).mul_const (‖y - x‖ ^ 2)
    convert (h1.sub h2).sub h3 using 1
    · funext s; simp only [g, Pi.sub_apply, Pi.pow_apply, id]
    · simp only [g', id]; ring
  have hanti : AntitoneOn g (Set.Icc 0 1) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      (fun t _ ↦ (hg t).continuousAt.continuousWithinAt) (fun t _ ↦ (hg t).hasDerivWithinAt) ?_
    intro t ht
    rw [interior_Icc] at ht
    have hlip := hL.dist_le_mul (x + t • (y - x)) x
    rw [dist_eq_norm, dist_eq_norm] at hlip
    have hsub : x + t • (y - x) - x = t • (y - x) := by abel
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1] at hlip
    have hcs : ⟪f' (x + t • (y - x)) - f' x, y - x⟫ ≤
        ‖f' (x + t • (y - x)) - f' x‖ * ‖y - x‖ := real_inner_le_norm _ _
    rw [inner_sub_left] at hcs
    have : ‖f' (x + t • (y - x)) - f' x‖ * ‖y - x‖ ≤ L * (t * ‖y - x‖) * ‖y - x‖ :=
      mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
    simp only [g']
    nlinarith
  have := hanti (by simp : (0 : ℝ) ∈ Set.Icc 0 1) (by simp : (1 : ℝ) ∈ Set.Icc 0 1) zero_le_one
  simp [g] at this
  linarith

/-- **One gradient step lowers `f`.** Under the descent lemma's hypotheses, the step of length
`1 / L` against the gradient lowers `f` by at least `‖f' x‖² / (2 L)`. Nothing is asked of `L`:
at `L = 0` the gradient is constant, Lean reads `0⁻¹` as `0`, the step does not move, and both
sides are `f x`. -/
theorem le_sub_of_gradientStep {f : E → ℝ} {f' : E → E} {L : ℝ≥0}
    (hf : ∀ x, HasGradientAt f (f' x) x) (hL : LipschitzWith L f') (x : E) :
    f (x - (L : ℝ)⁻¹ • f' x) ≤ f x - ‖f' x‖ ^ 2 / (2 * L) := by
  have h := le_add_inner_gradient_add_sq hf hL x (x - (L : ℝ)⁻¹ • f' x)
  rw [sub_sub_cancel_left, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_inv, NNReal.abs_eq] at h
  rcases eq_or_ne (L : ℝ) 0 with hL0 | hL0
  · rw [hL0] at h ⊢; simp
  · have : (L : ℝ) / 2 * ((L : ℝ)⁻¹ * ‖f' x‖) ^ 2 = ‖f' x‖ ^ 2 / (2 * L) := by
      field_simp
    have h2 : (L : ℝ)⁻¹ * ‖f' x‖ ^ 2 = 2 * (‖f' x‖ ^ 2 / (2 * L)) := by field_simp
    linarith

/-- **One gradient step against any point.** For convex `f` with `L`-Lipschitz gradient, `L > 0`,
and any point `z`, after one step `x' = x - (1 / L) f' x`:
`f x' - f z ≤ (L / 2) (‖x - z‖² - ‖x' - z‖²)`. Summed over the steps, the right side telescopes.
-/
theorem sub_le_sq_sub_sq_of_gradientStep {f : E → ℝ} {f' : E → E} {L : ℝ≥0}
    (hconv : ConvexOn ℝ Set.univ f) (hf : ∀ x, HasGradientAt f (f' x) x) (hL : LipschitzWith L f')
    (hL0 : 0 < L) (x z : E) :
    f (x - (L : ℝ)⁻¹ • f' x) - f z ≤
      L / 2 * (‖x - z‖ ^ 2 - ‖x - (L : ℝ)⁻¹ • f' x - z‖ ^ 2) := by
  have h1 := le_sub_of_gradientStep hf hL x
  have h2 := add_inner_gradient_le hconv (Set.mem_univ x) (Set.mem_univ z) (hf x)
  have hL0' : (L : ℝ) ≠ 0 := by positivity
  have hn : ‖x - (L : ℝ)⁻¹ • f' x - z‖ ^ 2 =
      ‖x - z‖ ^ 2 - 2 * (L : ℝ)⁻¹ * ⟪f' x, x - z⟫ + (L : ℝ)⁻¹ ^ 2 * ‖f' x‖ ^ 2 := by
    rw [show x - (L : ℝ)⁻¹ • f' x - z = (x - z) - (L : ℝ)⁻¹ • f' x by abel, norm_sub_sq_real,
      inner_smul_right, norm_smul, Real.norm_eq_abs, abs_inv, NNReal.abs_eq, real_inner_comm]
    ring
  rw [hn]
  have hi : ⟪f' x, z - x⟫ = -⟪f' x, x - z⟫ := by rw [← inner_neg_right, neg_sub]
  rw [hi] at h2
  have : (L : ℝ) / 2 * (2 * (L : ℝ)⁻¹ * ⟪f' x, x - z⟫ - (L : ℝ)⁻¹ ^ 2 * ‖f' x‖ ^ 2) =
      ⟪f' x, x - z⟫ - ‖f' x‖ ^ 2 / (2 * L) := by field_simp
  linarith

/-- **Gradient descent at rate `1 / k`, multiplied out.** For convex `f` with `L`-Lipschitz
gradient, `L > 0`, the iterates `x (k + 1) = x k - (1 / L) f' (x k)` satisfy
`k (f (x k) - f z) ≤ (L / 2) ‖x 0 - z‖²` for every point `z` and every `k`, `k = 0` included. -/
theorem mul_sub_le_of_gradientStep {f : E → ℝ} {f' : E → E} {L : ℝ≥0}
    (hconv : ConvexOn ℝ Set.univ f) (hf : ∀ x, HasGradientAt f (f' x) x) (hL : LipschitzWith L f')
    (hL0 : 0 < L) {x : ℕ → E} (hx : ∀ k, x (k + 1) = x k - (L : ℝ)⁻¹ • f' (x k)) (z : E) (k : ℕ) :
    k * (f (x k) - f z) ≤ L / 2 * ‖x 0 - z‖ ^ 2 := by
  have key : ∀ k : ℕ, k * (f (x k) - f z) + L / 2 * ‖x k - z‖ ^ 2 ≤ L / 2 * ‖x 0 - z‖ ^ 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hstep := sub_le_sq_sub_sq_of_gradientStep hconv hf hL hL0 (x k) z
      have hdec := le_sub_of_gradientStep hf hL (x k)
      rw [← hx] at hstep hdec
      have hnn : 0 ≤ ‖f' (x k)‖ ^ 2 / (2 * L) := by positivity
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have := mul_le_mul_of_nonneg_left (show f (x (k + 1)) - f z ≤ f (x k) - f z by linarith) hk
      push_cast
      nlinarith
  have := key k
  have : 0 ≤ (L : ℝ) / 2 * ‖x k - z‖ ^ 2 := by positivity
  linarith

/-- **Gradient descent at rate `1 / k`**, with step `1 / L` (derived here; the step-`1 / L` case
of Nesterov 2004, Theorem 2.1.14, gives `2 L ‖x 0 - x*‖² / (k + 4)` instead).
For convex `f` with `L`-Lipschitz gradient, `L > 0`, after `k > 0` steps of length `1 / L`:
`f (x k) - f z ≤ L ‖x 0 - z‖² / (2 k)`, for every point `z`; with `z` a minimiser, this bounds
how far `f (x k)` is above the least value. -/
theorem sub_le_of_gradientStep {f : E → ℝ} {f' : E → E} {L : ℝ≥0}
    (hconv : ConvexOn ℝ Set.univ f) (hf : ∀ x, HasGradientAt f (f' x) x) (hL : LipschitzWith L f')
    (hL0 : 0 < L) {x : ℕ → E} (hx : ∀ k, x (k + 1) = x k - (L : ℝ)⁻¹ • f' (x k)) (z : E) {k : ℕ}
    (hk : 0 < k) :
    f (x k) - f z ≤ L * ‖x 0 - z‖ ^ 2 / (2 * k) := by
  have h := mul_sub_le_of_gradientStep hconv hf hL hL0 hx z k
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- **A strongly convex function lies above its tangent planes by a parabola.** If `f` is
`m`-strongly convex on `s` (Mathlib's `StrongConvexOn`), `x, y ∈ s` and `f` has gradient `f'` at
`x`, then `f x + ⟪f', y - x⟫ + (m / 2) ‖y - x‖² ≤ f y`. Proved from the tangent-plane theorem
applied to the convex function `f - (m / 2) ‖·‖²` (Mathlib's `strongConvexOn_iff_convex`). -/
theorem add_inner_gradient_add_sq_le {f : E → ℝ} {f' x y : E} {s : Set E} {m : ℝ}
    (hf : StrongConvexOn s m f) (hx : x ∈ s) (hy : y ∈ s) (hf' : HasGradientAt f f' x) :
    f x + ⟪f', y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  have hc := (strongConvexOn_iff_convex.mp hf)
  have hq : HasFDerivAt (fun z : E ↦ ‖z‖ ^ 2) (2 • (innerSL ℝ x)) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hg : HasGradientAt (fun z ↦ f z - m / 2 * ‖z‖ ^ 2) (f' - m • x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have := (hasGradientAt_iff_hasFDerivAt.mp hf').sub (hq.const_mul (m / 2))
    convert this using 1
    ext v
    simp [InnerProductSpace.toDual_apply_apply]
    ring
  have h := add_inner_gradient_le hc hx hy hg
  rw [inner_sub_left, real_inner_smul_left] at h
  have hn : ‖y - x‖ ^ 2 = ‖y‖ ^ 2 - 2 * ⟪y, x⟫ + ‖x‖ ^ 2 := norm_sub_sq_real y x
  have hi : ⟪x, y - x⟫ = ⟪y, x⟫ - ‖x‖ ^ 2 := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm]
  rw [hi] at h
  rw [hn]
  linarith

/-- **Gradient descent converges geometrically for a strongly convex function.** If `f` is
`m`-strongly convex with `m ≥ 0`, its gradient is `L`-Lipschitz, and `xs` is a point where the
gradient is `0` (so the minimiser), the iterates `x (k + 1) = x k - (1 / L) f' (x k)` satisfy
`dist (x k) xs ² ≤ (1 - m / L) ^ k · dist (x 0) xs ²`. Nothing is asked of `L`: at `L = 0` the
gradient is `0` everywhere and the iterates do not move. -/
theorem dist_gradientStep_le {f : E → ℝ} {f' : E → E} {L : ℝ≥0} {m : ℝ} (hm : 0 ≤ m)
    (hconv : StrongConvexOn Set.univ m f) (hf : ∀ x, HasGradientAt f (f' x) x)
    (hL : LipschitzWith L f') {x : ℕ → E}
    (hx : ∀ k, x (k + 1) = x k - (L : ℝ)⁻¹ • f' (x k)) {xs : E} (hxs : f' xs = 0) (k : ℕ) :
    dist (x k) xs ^ 2 ≤ (1 - m / L) ^ k * dist (x 0) xs ^ 2 := by
  set c : ℝ := 1 - m / L
  simp only [dist_eq_norm]
  -- one step: `‖x (k+1) - xs‖² ≤ c ‖x k - xs‖²`
  have step : ∀ k, ‖x (k + 1) - xs‖ ^ 2 ≤ c * ‖x k - xs‖ ^ 2 := by
    intro k
    rcases eq_or_ne (L : ℝ) 0 with hL0 | hL0
    · have hconst : f' (x k) = 0 := by
        have := hL.dist_le_mul (x k) xs
        rw [show (L : ℝ) = 0 from hL0, zero_mul, hxs] at this
        exact dist_le_zero.mp this
      rw [hx k, hconst, smul_zero, sub_zero]
      simp [c, hL0]
    · set g := f' (x k)
      have hL0' : (0 : ℝ) < L := lt_of_le_of_ne (NNReal.coe_nonneg L) (Ne.symm hL0)
      have hn : ‖x (k + 1) - xs‖ ^ 2 =
          ‖x k - xs‖ ^ 2 - 2 * (L : ℝ)⁻¹ * ⟪g, x k - xs⟫ + (L : ℝ)⁻¹ ^ 2 * ‖g‖ ^ 2 := by
        rw [hx k, show x k - (L : ℝ)⁻¹ • g - xs = (x k - xs) - (L : ℝ)⁻¹ • g by abel,
          norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_inv,
          NNReal.abs_eq, real_inner_comm]
        ring
      -- strong convexity at `x k`, towards `xs`
      have h1 := add_inner_gradient_add_sq_le hconv (Set.mem_univ (x k)) (Set.mem_univ xs)
        (hf (x k))
      have hi : ⟪g, xs - x k⟫ = -⟪g, x k - xs⟫ := by rw [← inner_neg_right, neg_sub]
      rw [hi, norm_sub_rev] at h1
      -- `xs` is a minimiser
      have h2 := add_inner_gradient_add_sq_le hconv (Set.mem_univ xs) (Set.mem_univ (x (k + 1)))
        (hxs ▸ hf xs)
      rw [inner_zero_left] at h2
      have h2' : f xs ≤ f (x (k + 1)) := by nlinarith [sq_nonneg ‖x (k + 1) - xs‖]
      -- one step decreases `f`
      have h3 := le_sub_of_gradientStep hf hL (x k)
      rw [← hx k] at h3
      have hg2 : ‖g‖ ^ 2 ≤ 2 * L * (f (x k) - f xs) := by
        have : ‖g‖ ^ 2 / (2 * L) ≤ f (x k) - f xs := by linarith
        rwa [div_le_iff₀ (by positivity), mul_comm] at this
      rw [hn]
      have hcL : c * ‖x k - xs‖ ^ 2 = ‖x k - xs‖ ^ 2 - (L : ℝ)⁻¹ * m * ‖x k - xs‖ ^ 2 := by
        simp only [c]; field_simp
      rw [hcL]
      have hinv : (L : ℝ)⁻¹ ^ 2 * ‖g‖ ^ 2 ≤ (L : ℝ)⁻¹ ^ 2 * (2 * L * (f (x k) - f xs)) :=
        mul_le_mul_of_nonneg_left hg2 (by positivity)
      have hLL : (L : ℝ)⁻¹ ^ 2 * (2 * L * (f (x k) - f xs)) = 2 * (L : ℝ)⁻¹ * (f (x k) - f xs) := by
        field_simp
      have hmul : 2 * (L : ℝ)⁻¹ * (f (x k) - f xs + m / 2 * ‖x k - xs‖ ^ 2) ≤
          2 * (L : ℝ)⁻¹ * ⟪g, x k - xs⟫ :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      nlinarith
  -- iterate
  rcases le_or_gt 0 c with hc | hc
  · induction k with
    | zero => simp
    | succ k ih =>
      calc ‖x (k + 1) - xs‖ ^ 2 ≤ c * ‖x k - xs‖ ^ 2 := step k
        _ ≤ c * (c ^ k * ‖x 0 - xs‖ ^ 2) := mul_le_mul_of_nonneg_left ih hc
        _ = c ^ (k + 1) * ‖x 0 - xs‖ ^ 2 := by ring
  · -- `c < 0` forces every distance to be `0`
    have hz : ∀ k, ‖x k - xs‖ ^ 2 = 0 := by
      have h0 : ‖x 0 - xs‖ ^ 2 = 0 := by
        have := step 0
        nlinarith [sq_nonneg ‖x 1 - xs‖, sq_nonneg ‖x 0 - xs‖]
      intro k
      induction k with
      | zero => exact h0
      | succ k ih =>
        have := step k
        rw [ih, mul_zero] at this
        exact le_antisymm this (sq_nonneg _)
    rw [hz k, hz 0, mul_zero]

/-- **The KKT conditions are sufficient for a convex problem.** Minimise a convex `f` over the
points `x` with `g i x ≤ 0` for every `i`, each `g i` convex. If at `xbar` the gradients are `a`
(of `f`) and `b i` (of `g i`), and there are multipliers `w i ≥ 0` with `w i · g i xbar = 0`
(complementary slackness) and `a + ∑ w i b i = 0` (stationarity), then no point satisfying the
constraints has a smaller value of `f` than `xbar`. Feasibility of `xbar` is not needed for that
inequality; when `xbar` also satisfies the constraints, it is a minimiser of the problem. -/
theorem isMinOn_of_kkt {ι : Type*} [Fintype ι] {f : E → ℝ} {g : ι → E → ℝ} {xbar a : E}
    {b : ι → E} {w : ι → ℝ} (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hfa : HasGradientAt f a xbar) (hgb : ∀ i, HasGradientAt (g i) (b i) xbar)
    (hw : ∀ i, 0 ≤ w i) (hslack : ∀ i, w i * g i xbar = 0) (hstat : a + ∑ i, w i • b i = 0) :
    IsMinOn f {x | ∀ i, g i x ≤ 0} xbar := by
  intro y hy
  have hy : ∀ i, g i y ≤ 0 := hy
  have h0 := add_inner_gradient_le hf (Set.mem_univ xbar) (Set.mem_univ y) hfa
  have ha : a = -∑ i, w i • b i := eq_neg_of_add_eq_zero_left hstat
  rw [ha, inner_neg_left, sum_inner] at h0
  simp only [real_inner_smul_left] at h0
  have hi : ∀ i, w i * ⟪b i, y - xbar⟫ ≤ w i * g i y - w i * g i xbar := by
    intro i
    have := add_inner_gradient_le (hg i) (Set.mem_univ xbar) (Set.mem_univ y) (hgb i)
    have := mul_le_mul_of_nonneg_left (show ⟪b i, y - xbar⟫ ≤ g i y - g i xbar by linarith) (hw i)
    linarith
  have hs : ∑ i, w i * ⟪b i, y - xbar⟫ ≤ 0 := by
    calc ∑ i, w i * ⟪b i, y - xbar⟫ ≤ ∑ i, (w i * g i y - w i * g i xbar) :=
          sum_le_sum fun i _ ↦ hi i
      _ = ∑ i, w i * g i y := by simp [hslack]
      _ ≤ 0 := sum_nonpos fun i _ ↦ mul_nonpos_of_nonneg_of_nonpos (hw i) (hy i)
  change f xbar ≤ f y
  linarith

/-- **Polyak–Łojasiewicz** (item 112 of MATH-PLAN-library-2; the draft `d112-r1-s2`, written by
Claude Opus 5.5 through the Anthropic Batch API, the lane's API-CREDIT-1 work, adapted by order
LEAN-33's session). If the gradient `f'` of `f` is `L`-Lipschitz, `f* ≤ f` everywhere, and
`μ (f x − f*) ≤ ‖f' x‖² / 2` for every `x`, then the iterates
`x (k + 1) = x k − (1 / L) f' (x k)` satisfy `f (x k) − f* ≤ (1 − μ / L) ^ k (f (x 0) − f*)`.
Wider than the plan's row: `f*` is any lower bound of `f`, not only its least value, and nothing is
asked of `μ` or `L` (when `1 − μ / L < 0` the lower bound forces `f (x k) = f*` for every `k`; at
`L = 0` Lean's `0⁻¹ = 0` makes the step not move). -/
theorem sub_le_pow_mul_of_polyakLojasiewicz {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {f : E → ℝ} {f' : E → E} {L : ℝ≥0} {μ fstar : ℝ}
    (hf : ∀ x, HasGradientAt f (f' x) x) (hL : LipschitzWith L f')
    (hfs : ∀ x, fstar ≤ f x) (hPL : ∀ x, μ * (f x - fstar) ≤ ‖f' x‖ ^ 2 / 2)
    {x : ℕ → E} (hx : ∀ k, x (k + 1) = x k - (L : ℝ)⁻¹ • f' (x k)) (k : ℕ) :
    f (x k) - fstar ≤ (1 - μ / L) ^ k * (f (x 0) - fstar) := by
  have step : ∀ k, f (x (k + 1)) - fstar ≤ (1 - μ / L) * (f (x k) - fstar) := by
    intro k
    have h3 := le_sub_of_gradientStep hf hL (x k)
    rw [← hx k] at h3
    rcases eq_or_ne (L : ℝ) 0 with hL0 | hL0
    · rw [hL0, mul_zero, div_zero, sub_zero] at h3
      rw [hL0, div_zero, sub_zero, one_mul]
      linarith
    · have hLpos : (0 : ℝ) < L := lt_of_le_of_ne (NNReal.coe_nonneg L) (Ne.symm hL0)
      have hmul : (L : ℝ)⁻¹ * (μ * (f (x k) - fstar)) ≤ (L : ℝ)⁻¹ * (‖f' (x k)‖ ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (hPL (x k)) (inv_nonneg.mpr hLpos.le)
      have e1 : (1 - μ / L) * (f (x k) - fstar) =
          (f (x k) - fstar) - (L : ℝ)⁻¹ * (μ * (f (x k) - fstar)) := by ring
      have e2 : ‖f' (x k)‖ ^ 2 / (2 * L) = (L : ℝ)⁻¹ * (‖f' (x k)‖ ^ 2 / 2) := by ring
      rw [e1]
      linarith
  rcases le_or_gt 0 (1 - μ / L) with hc | hc
  · induction k with
    | zero => simp
    | succ k ih =>
      calc f (x (k + 1)) - fstar ≤ (1 - μ / L) * (f (x k) - fstar) := step k
        _ ≤ (1 - μ / L) * ((1 - μ / L) ^ k * (f (x 0) - fstar)) :=
          mul_le_mul_of_nonneg_left ih hc
        _ = (1 - μ / L) ^ (k + 1) * (f (x 0) - fstar) := by ring
  · have hz : ∀ k, f (x k) - fstar = 0 := by
      have h0 : f (x 0) - fstar = 0 := by
        have h := step 0
        have h1 := hfs (x 1)
        have h0' := hfs (x 0)
        refine le_antisymm ?_ (by linarith)
        nlinarith
      intro k
      induction k with
      | zero => exact h0
      | succ k ih =>
        have h := step k
        rw [ih, mul_zero] at h
        have h1 := hfs (x (k + 1))
        linarith
    rw [hz k, hz 0, mul_zero]

/-- One projected gradient step against any point `z` of `K`. -/
private lemma projStep_aux {f : E → ℝ} {f' : E → E} {L : ℝ≥0} {K : Set E}
    (hK : Convex ℝ K) (hconv : ConvexOn ℝ K f) (hf : ∀ x, HasGradientAt f (f' x) x)
    (hL : LipschitzWith L f') (hL0 : 0 < L) {x p z : E} (hx : x ∈ K) (hz : z ∈ K) (hp : p ∈ K)
    (hproj : ‖x - (L : ℝ)⁻¹ • f' x - p‖ = ⨅ w : K, ‖x - (L : ℝ)⁻¹ • f' x - w‖) :
    f p - f z ≤ L / 2 * (‖x - z‖ ^ 2 - ‖p - z‖ ^ 2) := by
  have h1 := le_add_inner_gradient_add_sq hf hL x p
  have h2 := add_inner_gradient_le hconv hx hz (hf x)
  have h3 := (norm_eq_iInf_iff_real_inner_le_zero hK hp).mp hproj z hz
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL0
  have e3 : ⟪x - (L : ℝ)⁻¹ • f' x - p, z - p⟫ =
      ⟪x - p, z - p⟫ - (L : ℝ)⁻¹ * ⟪f' x, z - p⟫ := by
    rw [show x - (L : ℝ)⁻¹ • f' x - p = (x - p) - (L : ℝ)⁻¹ • f' x by abel,
      inner_sub_left, real_inner_smul_left]
  rw [e3] at h3
  have h4 : (L : ℝ) * ⟪x - p, z - p⟫ ≤ ⟪f' x, z - p⟫ := by
    have e : (L : ℝ) * ((L : ℝ)⁻¹ * ⟪f' x, z - p⟫) = ⟪f' x, z - p⟫ := by
      rw [← mul_assoc, mul_inv_cancel₀ hL'.ne', one_mul]
    have := mul_le_mul_of_nonneg_left h3 hL'.le
    rw [mul_sub, e, mul_zero] at this
    linarith
  have hg : ⟪f' x, z - p⟫ = ⟪f' x, z - x⟫ - ⟪f' x, p - x⟫ := by
    rw [← inner_sub_right]; congr 1; abel
  have hn : ‖x - z‖ ^ 2 = ‖x - p‖ ^ 2 - 2 * ⟪x - p, z - p⟫ + ‖z - p‖ ^ 2 := by
    rw [show x - z = (x - p) - (z - p) by abel]
    exact norm_sub_sq_real _ _
  rw [norm_sub_rev p x] at h1
  rw [norm_sub_rev p z, hn]
  linarith

/-- **Projected gradient descent at rate `1 / k`** (item 134 of MATH-PLAN-library-2; the draft
`d134-r1-s1`, written by Claude Opus 5.5 through the Anthropic Batch API, the lane's API-CREDIT-1
work, adapted by order LEAN-33's session). Let `K` be a convex set, `f` convex on `K` with
`L`-Lipschitz gradient, `L > 0`, and let each iterate `x (k + 1)` be a nearest point of `K` to
`x k - (1 / L) f' (x k)`, starting from `x 0 ∈ K`. Then for every `z ∈ K` and `k > 0`,
`f (x k) - f z ≤ L ‖x 0 - z‖² / (2 k)`. Wider than the plan's row (GENERALIZED): the row asks for a
closed convex set, but the proof takes the nearest-point property of each step as the hypothesis
`hx`, so closedness is never used; closedness is what makes such nearest points exist in a Hilbert
space (Mathlib's `exists_norm_eq_iInf_of_complete_convex`), so for a closed nonempty `K` the
hypothesis can always be met. The draft's unused `IsClosed K` is removed (claude-ai's ruling in
order LEAN-33, accepted by Dustin on 2026-10-20). Also wider than item 18
(`sub_le_of_gradientStep`): `f` need be convex on `K` only. `hK` follows from `hconv` (its first
part); it is kept as drafted. -/
theorem sub_le_of_projGradientStep {f : E → ℝ} {f' : E → E} {L : ℝ≥0} {K : Set E}
    (hK : Convex ℝ K) (hconv : ConvexOn ℝ K f)
    (hf : ∀ x, HasGradientAt f (f' x) x) (hL : LipschitzWith L f') (hL0 : 0 < L)
    {x : ℕ → E} (hx0 : x 0 ∈ K) (hxK : ∀ k, x (k + 1) ∈ K)
    (hx : ∀ k, ‖x k - (L : ℝ)⁻¹ • f' (x k) - x (k + 1)‖ =
      ⨅ w : K, ‖x k - (L : ℝ)⁻¹ • f' (x k) - w‖)
    {z : E} (hz : z ∈ K) {k : ℕ} (hk : 0 < k) :
    f (x k) - f z ≤ L * ‖x 0 - z‖ ^ 2 / (2 * k) := by
  have hmem : ∀ k, x k ∈ K := fun k => by
    cases k with
    | zero => exact hx0
    | succ k => exact hxK k
  have step : ∀ k w, w ∈ K →
      f (x (k + 1)) - f w ≤ L / 2 * (‖x k - w‖ ^ 2 - ‖x (k + 1) - w‖ ^ 2) :=
    fun k w hw => projStep_aux hK hconv hf hL hL0 (hmem k) hw (hxK k) (hx k)
  have key : ∀ k : ℕ, k * (f (x k) - f z) + L / 2 * ‖x k - z‖ ^ 2 ≤
      L / 2 * ‖x 0 - z‖ ^ 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := step k z hz
      have hdec := step k (x k) (hmem k)
      simp only [sub_self, norm_zero] at hdec
      have hdec' : f (x (k + 1)) ≤ f (x k) := by
        have : 0 ≤ (L : ℝ) / 2 * ‖x (k + 1) - x k‖ ^ 2 := by positivity
        linarith
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have := mul_le_mul_of_nonneg_left
        (show f (x (k + 1)) - f z ≤ f (x k) - f z by linarith) hk0
      push_cast
      nlinarith
  have h := key k
  have hpos : 0 ≤ (L : ℝ) / 2 * ‖x k - z‖ ^ 2 := by positivity
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [le_div_iff₀ (by positivity)]
  nlinarith

end ClassicalLean.Analysis

/-- The hypotheses of `le_add_inner_gradient_add_sq` hold together: on `ℝ`, `f x = x ^ 2 / 2` has
gradient `f' x = x` at every point, and `f'` is Lipschitz with constant `L = 2` (it is with `1`,
so with any larger constant); `x = 1`, `y = 3`. -/
example := ClassicalLean.Analysis.le_add_inner_gradient_add_sq (E := ℝ) (f := fun y ↦ y ^ 2 / 2)
  (f' := fun y ↦ y) (L := 2)
  (fun x ↦ by simpa using ((hasDerivAt_pow 2 x).div_const 2).hasGradientAt)
  (LipschitzWith.id.weaken (by norm_num)) (x := 1) (y := 3)

/-- The hypotheses of `add_inner_gradient_le` hold together: on `ℝ`, `f x = x ^ 2 / 2` is convex
on the whole line (strongly convex with `m = 1`, since `f x − x ^ 2 / 2 = 0`), the points `x = 1`
and `y = 3` lie in it, and `f` has gradient `1` at `x = 1`. -/
example := ClassicalLean.Analysis.add_inner_gradient_le (E := ℝ) (f := fun y ↦ y ^ 2 / 2)
  (f' := 1) (x := 1) (y := 3) (s := Set.univ)
  ((show StrongConvexOn Set.univ 1 (fun y : ℝ ↦ y ^ 2 / 2) by
    rw [strongConvexOn_iff_convex]
    convert convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set ℝ)) using 1
    ext x; simp; ring).convexOn fun r ↦ by positivity)
  (Set.mem_univ _) (Set.mem_univ _)
  (by simpa using ((hasDerivAt_pow 2 (1 : ℝ)).div_const 2).hasGradientAt)

/-- The hypotheses of `sub_le_of_gradientStep` hold together: on `ℝ`, `f x = x ^ 2 / 2` is convex
(strongly convex with `m = 1`), has gradient `f' x = x`, and `f'` is Lipschitz with `L = 2 > 0`;
the steps `x k = (1/2) ^ k` are gradient steps of size `1/L`, `x (k + 1) = x k − x k / 2`; the
point `z = 0` and the step `k = 3 > 0`. -/
example := ClassicalLean.Analysis.sub_le_of_gradientStep (E := ℝ) (f := fun y ↦ y ^ 2 / 2)
  (f' := fun y ↦ y) (L := 2)
  ((show StrongConvexOn Set.univ 1 (fun y : ℝ ↦ y ^ 2 / 2) by
    rw [strongConvexOn_iff_convex]
    convert convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set ℝ)) using 1
    ext x; simp; ring).convexOn fun r ↦ by positivity)
  (fun x ↦ by simpa using ((hasDerivAt_pow 2 x).div_const 2).hasGradientAt)
  (LipschitzWith.id.weaken (by norm_num)) (by norm_num) (x := fun k ↦ (1 / 2) ^ k)
  (fun k ↦ by simp [pow_succ]; ring) (z := 0) (k := 3) (by norm_num)

/-- The hypotheses of `dist_gradientStep_le` hold together: on `ℝ`, `f x = x ^ 2 / 2` is strongly
convex with `m = 1 ≥ 0` (`f x − x ^ 2 / 2 = 0` is convex), has gradient `f' x = x`, and `f'` is
Lipschitz with `L = 2`, so `1 − m / L = 1/2` is not `0`; the steps `x k = (1/2) ^ k` are gradient
steps of size `1/L`; the minimiser `xs = 0` has `f' xs = 0`; `k = 3`. -/
example := ClassicalLean.Analysis.dist_gradientStep_le (E := ℝ) (f := fun y ↦ y ^ 2 / 2)
  (f' := fun y ↦ y) (L := 2) (m := 1) zero_le_one
  (by
    rw [strongConvexOn_iff_convex]
    convert convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set ℝ)) using 1
    ext x; simp; ring)
  (fun x ↦ by simpa using ((hasDerivAt_pow 2 x).div_const 2).hasGradientAt)
  (LipschitzWith.id.weaken (by norm_num)) (x := fun k ↦ (1 / 2) ^ k)
  (fun k ↦ by simp [pow_succ]; ring) (xs := 0) rfl (k := 3)

/-- The hypotheses of `isMinOn_of_kkt` hold together: on `ℝ`, minimise `f x = x ^ 2 / 2` (convex)
under two constraints, `g 0 x = 1 − x ≤ 0` (active at `xbar = 1`, multiplier `w 0 = 1`) and
`g 1 x = x − 5 ≤ 0` (slack at `xbar`, multiplier `w 1 = 0`), both affine, so convex; the
gradients at `xbar = 1` are `a = 1`, `b 0 = −1`, `b 1 = 1`; the multipliers are nonnegative,
`w i * g i xbar = 0` for each, and `a + w 0 * b 0 + w 1 * b 1 = 0`. -/
example := ClassicalLean.Analysis.isMinOn_of_kkt (E := ℝ) (ι := Fin 2) (f := fun y ↦ y ^ 2 / 2)
  (g := ![fun x ↦ 1 - x, fun x ↦ x - 5]) (xbar := 1) (a := 1) (b := ![-1, 1]) (w := ![1, 0])
  ((show StrongConvexOn Set.univ 1 (fun y : ℝ ↦ y ^ 2 / 2) by
    rw [strongConvexOn_iff_convex]
    convert convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set ℝ)) using 1
    ext x; simp; ring).convexOn fun r ↦ by positivity)
  (fun i ↦ by
    fin_cases i
    · exact (convexOn_const (1 : ℝ) convex_univ).sub (concaveOn_id convex_univ)
    · exact (convexOn_id convex_univ).sub (concaveOn_const (5 : ℝ) convex_univ))
  (by simpa using ((hasDerivAt_pow 2 (1 : ℝ)).div_const 2).hasGradientAt)
  (fun i ↦ by
    fin_cases i
    · simpa using ((hasDerivAt_id (1 : ℝ)).const_sub 1).hasGradientAt
    · simpa using ((hasDerivAt_id (1 : ℝ)).sub_const 5).hasGradientAt)
  (fun i ↦ by fin_cases i <;> norm_num) (fun i ↦ by fin_cases i <;> norm_num)
  (by simp [Fin.sum_univ_two])

/-- The hypotheses of `sub_le_pow_mul_of_polyakLojasiewicz` hold together: on `ℝ`,
`f x = x ^ 2 / 2` has gradient `f' x = x`, which is Lipschitz with `L = 2`; `f* = 0` is a lower
bound of `f`; the Polyak–Łojasiewicz inequality holds with `μ = 1`, as `‖x‖² / 2 = f x`; the steps
`x k = (1/2) ^ k` are gradient steps of size `1 / L`, so the factor `1 − μ / L = 1/2` is neither
`0` nor `1` and every iterate is nonzero; `k = 3`. -/
example := ClassicalLean.Analysis.sub_le_pow_mul_of_polyakLojasiewicz (E := ℝ)
  (f := fun y ↦ y ^ 2 / 2) (f' := fun y ↦ y) (L := 2) (μ := 1) (fstar := 0)
  (fun x ↦ by simpa using ((hasDerivAt_pow 2 x).div_const 2).hasGradientAt)
  (LipschitzWith.id.weaken (by norm_num)) (fun x ↦ by positivity)
  (fun x ↦ by simp [Real.norm_eq_abs, sq_abs]) (x := fun k ↦ (1 / 2) ^ k)
  (fun k ↦ by simp [pow_succ]; ring) (k := 3)

/-- The hypotheses of `sub_le_of_projGradientStep` hold together: on `ℝ`, `f x = x ^ 2 / 2`
(convex, gradient `f' x = x`, Lipschitz with `L = 2 > 0`) on the convex set `K = [1/4, 1]`; the
iterates `1, 1/2, 1/4, 1/4, …` start in `K`, and each is the nearest point of `K` to the plain
gradient step `x k / 2` (from `x 2` on the plain step `1/8` leaves `K` and the projection moves it
back to `1/4`); `z = 1/2 ∈ K` and `k = 3`. -/
example := ClassicalLean.Analysis.sub_le_of_projGradientStep (E := ℝ)
  (f := fun y ↦ y ^ 2 / 2) (f' := fun y ↦ y) (L := 2) (K := Set.Icc (1 / 4) 1)
  (convex_Icc _ _)
  (((show StrongConvexOn Set.univ 1 (fun y : ℝ ↦ y ^ 2 / 2) by
    rw [strongConvexOn_iff_convex]
    convert convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set ℝ)) using 1
    ext x; simp; ring).convexOn fun r ↦ by positivity).subset (Set.subset_univ _) (convex_Icc _ _))
  (fun x ↦ by simpa using ((hasDerivAt_pow 2 x).div_const 2).hasGradientAt)
  (LipschitzWith.id.weaken (by norm_num)) (by norm_num)
  (x := fun k ↦ if k = 0 then 1 else if k = 1 then 1 / 2 else 1 / 4)
  (by norm_num) (fun k ↦ by rcases k with _ | _ | k <;> norm_num)
  (fun k ↦ by
    rw [norm_eq_iInf_iff_real_inner_le_zero (convex_Icc _ _)
      (by rcases k with _ | _ | k <;> norm_num)]
    intro w hw
    rcases k with _ | _ | k <;> simp at hw ⊢ <;> nlinarith [hw.1, hw.2])
  (z := 1 / 2) (by norm_num) (k := 3) (by norm_num)
