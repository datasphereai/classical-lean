/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.Distributions.Bernoulli

/-!
# Order statistics

`orderStat v k` is the entry at position `k`, counting from `0`, of the real tuple `v : Fin n → ℝ`
sorted increasingly (`Tuple.sort`); so `orderStat v ⟨k - 1, _⟩` is the `k`-th smallest entry.

* `measureReal_orderStat_le` — order CLOUD-MATH-3, item 126 of MATH-PLAN-library-2. For `n`
  independent measurable real random variables `X i` on a probability space with a common value
  `F = P(X i ≤ x)` at a point `x`, and `1 ≤ k ≤ n`, the `k`-th smallest of them is at most `x` with
  probability `∑ j ∈ Finset.Icc k n, n.choose j * F ^ j * (1 - F) ^ (n - j)`.

The proof. The `k`-th smallest entry is at most `x` exactly when at least `k` entries are
(`orderStat_le_iff`), so the event is the disjoint union, over the sets `S` of at least `k`
indices, of the events `E S` that the entries at most `x` are exactly those with index in `S`. By
independence `E S` has probability `F ^ S.card * (1 - F) ^ (n - S.card)` (`prod_ite_mem_eq`), and
grouping the sets `S` by size gives the binomial sum (`sum_filter_card`).

The proof is the draft `d126-r2-s2` (written by Claude Opus 5.5 through the Anthropic Batch API,
the lane's API-CREDIT-1 work), adapted by the Claude Code cloud session that landed it (order
CLOUD-MATH-3): the namespace, the targeted import and docstrings; `push Not` for the deprecated
`push_neg`; `ite_eq_left` and `ite_eq_right` for the deprecated `if_pos` and `if_neg`;
`Set.mem_ofPred_eq` for the deprecated `Set.mem_setOf_eq`; and `change` where a `show` changed the
goal. The witness at the end of the file, three independent fair coins with values `1` and `0`
(the coordinates of `Measure.pi` of three copies of Mathlib's `bernoulliMeasure`) at `x = 1 / 2`,
so `F = 1 / 2`, and `k = 2`, is claude-ai's start for the order (`w126-tail.lean`), with the
theorem called by its full name; it is why the file imports
`Mathlib.Probability.Distributions.Bernoulli`, which also brings in every module the proof uses.
-/

open MeasureTheory ProbabilityTheory Finset

namespace ClassicalLean.Probability.OrderStatistics

