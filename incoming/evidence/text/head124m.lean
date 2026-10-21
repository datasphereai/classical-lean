/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Moments.Basic

/-!
# Bernstein's inequality

* `measureReal_sum_ge_le_bernstein` — order CLOUD-MATH-3, item 124 of MATH-PLAN-library-2. Let
  `X i`, for `i : ι`, be independent measurable real random variables on a probability space, and
  `s` a finite set of indices. If each `X i` with `i ∈ s` is integrable with an integrable square,
  has mean `0` and is almost surely at most `b`, where `b ≥ 0`, and `∑ i ∈ s, E[X i ^ 2] ≤ v`, then
  for every `t ≥ 0` the chance that `t ≤ ∑ i ∈ s, X i` is at most
  `exp (-t ^ 2 / (2 * (v + b * t / 3)))`.

The proof is Chernoff's method. For `0 ≤ l` with `l * b < 3`, the bound
`exp y ≤ 1 + y + y ^ 2 / (2 * (1 - c / 3))` for `y ≤ c`, where `0 ≤ c < 3` (`exp_le_bernstein`,
from one calculus lemma for `y ≤ 0` and one for `y ≥ 0`), bounds each moment generating function:
since the mean is `0`, `E[exp (l * X i)] ≤ 1 + κ * E[X i ^ 2] ≤ exp (κ * E[X i ^ 2])` with
`κ = l ^ 2 / (2 * (1 - l * b / 3))`. Independence multiplies them (`iIndepFun.mgf_sum`), and
Markov's inequality for `exp (l * ∑ i ∈ s, X i)` (`measure_ge_le_exp_mul_mgf`) gives a chance at
most `exp (-l * t + κ * v)`. The choice `l = t / (v + b * t / 3)` when `v > 0`, and
`l = t / (2 * (v + b * t / 3))` when `v = 0`, makes the exponent
`-t ^ 2 / (2 * (v + b * t / 3))`; at `t = 0`, or when `v + b * t / 3 ≤ 0`, the choice `l = 0`
gives the chance at most `1`, and the target exponent is then `0` or nonnegative.

The proof is the draft `d124-r4-s2` (written by Claude Opus 5.5 through the Anthropic Batch API,
the lane's API-CREDIT-1 work), adapted by the Claude Code cloud session that landed it (order
CLOUD-MATH-3): the namespace, targeted imports and docstrings; every `first` chain cut to the
branch that fires; `change` where a `show` changed the goal; and `push Not` for the deprecated
`push_neg`. The witness at the end of the file, two independent fair `±1` coins (the coordinates
of `Measure.pi` of two copies of Mathlib's `bernoulliMeasure`) with `b = 1`, `v = 2` and `t = 1`,
is claude-ai's start for the order (`w124-tail.lean`), with the theorem called by its full name;
it is why the file imports `Mathlib.Probability.Distributions.Bernoulli`.
-/

open MeasureTheory ProbabilityTheory

namespace ClassicalLean.Probability.BernsteinInequality

