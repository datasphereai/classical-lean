/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The subgradient method

A function `f : E → ℝ` on a real inner product space `E`, and points `x n` with, at each of them,
a subgradient `g n`: `f (x n) + ⟪g n, y - x n⟫_ℝ ≤ f y` for every `y`. The subgradient method steps
against the subgradient with a fixed step `η > 0`: `x (n + 1) = x n - η • g n`.

* `min_sub_le_of_subgradient` — order CLOUD-MATH-3, item 113 of MATH-PLAN-library-2. If
  `‖g n‖ ≤ G` for every `n`, then for every point `z` and every `T ≥ 1` the least of the first `T`
  values `f (x 0), …, f (x (T - 1))` (`Finset.inf'` over `Finset.range T`) is at most `f z` plus
  `(‖x 0 - z‖ ^ 2 + η ^ 2 * G ^ 2 * T) / (2 * η * T)`.

Wider than the plan's row, by this session's reading (the draft's last review, as the order's
table gives it: GENERALIZED): the row speaks of a convex `f`; the theorem asks no convexity, only
the subgradient inequality at the points `x n` themselves, which every subgradient of a convex `f`
satisfies.

The proof. The subgradient inequality at `y = z` and the expansion of
`‖x (n + 1) - z‖ ^ 2 = ‖(x n - z) - η • g n‖ ^ 2` give
`2 * η * (f (x n) - f z) ≤ ‖x n - z‖ ^ 2 - ‖x (n + 1) - z‖ ^ 2 + η ^ 2 * G ^ 2`. Summed over
`n < T`, the right side telescopes to at most `‖x 0 - z‖ ^ 2 + T * (η ^ 2 * G ^ 2)`, and the least
value is at most every term of the sum on the left.

The proof is the draft `d113-r1-s1` (written by Claude Opus 5.5 through the Anthropic Batch API,
the lane's API-CREDIT-1 work), adapted by the Claude Code cloud session that landed it (order
CLOUD-MATH-3): the namespace, the targeted import and the docstrings; its proof needed no other
change. The witness at the end of the file, `f y = y ^ 2 / 2` on the real line with the step
`η = 1 / 2`, is new: the item had no witness start.
-/

open scoped InnerProductSpace
open Finset

namespace ClassicalLean.Analysis.SubgradientMethod

