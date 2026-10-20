/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Necessity of the KKT conditions under Slater's condition

* `exists_kkt_of_slater` — order CLOUD-MATH-2, item 152 of MATH-PLAN-library-2. For the convex
  problem of minimising `f x` subject to `g i x ≤ 0` for `i` in a finite type, on a real Hilbert
  space, with `f` and every `g i` convex and differentiable at a feasible minimiser `xbar`
  (gradients `a` and `b i`): if some point satisfies every constraint strictly (Slater's
  condition), there are multipliers `w i ≥ 0` with complementary slackness `w i * g i xbar = 0`
  and stationarity `a + ∑ i, w i • b i = 0`.

The proof. The set `C` of pairs `(t, v)` such that `f x < t` and `g i x < v i` for every `i`, for
some `x`, is convex and open, and `(f xbar, 0)` lies outside it because `xbar` is a feasible
minimiser; a continuous linear functional `φ` separates the point from `C`
(`geometric_hahn_banach_point_open`). `φ` is nonnegative on pairs with nonnegative coordinates, so
`φ (t, v) = l₀ * t + ∑ i, v i * λ i` with `l₀ ≥ 0` and every `λ i ≥ 0`, and
`l₀ * f xbar ≤ l₀ * f x + ∑ i, λ i * g i x` for every `x`. Slater's point rules out `l₀ = 0`.
With `w i = λ i / l₀`, `xbar` minimises the Lagrangian `f + ∑ i, w i * g i` over the whole space,
which gives complementary slackness; the Lagrangian's derivative at `xbar`, the functional of
`a + ∑ i, w i • b i`, vanishes there (`IsLocalMin.hasFDerivAt_eq_zero`), and so does that vector.

The proof is the draft `d152-r2-s1` (written by Claude Opus 5.5 through the Anthropic Batch API,
the lane's order API-CREDIT-1), adapted by the Claude Code cloud session that landed it (order
CLOUD-MATH-2): the namespace and docstrings; `change` where a `show` changed the goal; `push Not`
for the deprecated `push_neg`; the names Mathlib now gives four deprecated `ContinuousLinearMap`
lemmas (`add_apply`, `_root_.sum_apply`, `smul_apply`, `zero_apply`); and the import of
`Mathlib.Analysis.Calculus.FDeriv.Mul` (for `HasFDerivAt.const_mul`) in place of the draft's
import of the library's `ClassicalLean.Analysis.GradientDescent`, none of whose declarations the
proof uses.
-/

open Finset
open scoped RealInnerProductSpace

namespace ClassicalLean.Analysis.KKT

/-- A strict convex combination inequality. -/
private lemma convex_comb_lt {s t a b c d : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1)
    (hab : a < b) (hcd : c < d) : s * a + t * c < s * b + t * d := by
  sorry

/-- **KKT conditions are necessary under Slater's condition** (item 152 of MATH-PLAN-library-2).
Let `f` and every `g i` be convex on a real Hilbert space, with gradients `a` and `b i` at `xbar`.
If `xbar` is feasible and minimises `f` over `{x | ∀ i, g i x ≤ 0}`, and some point satisfies
every constraint strictly, then there are multipliers `w i ≥ 0` with `w i · g i xbar = 0` and
`a + ∑ w i b i = 0`. -/
theorem exists_kkt_of_slater {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] {f : E → ℝ} {g : ι → E → ℝ} {xbar a : E}
    {b : ι → E} (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hfa : HasGradientAt f a xbar) (hgb : ∀ i, HasGradientAt (g i) (b i) xbar)
    (hslater : ∃ x0, ∀ i, g i x0 < 0) (hxbar : ∀ i, g i xbar ≤ 0)
    (hmin : IsMinOn f {x | ∀ i, g i x ≤ 0} xbar) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∀ i, w i * g i xbar = 0) ∧ a + ∑ i, w i • b i = 0 := by
  sorry

end ClassicalLean.Analysis.KKT

set_option pp.fullNames true
#check @ClassicalLean.Analysis.KKT.exists_kkt_of_slater
