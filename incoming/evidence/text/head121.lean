/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Efron–Stein inequality on a finite product space

Coordinates `x i ∈ Ω i`, for `i : Fin n`, each `Ω i` a finite type with a probability vector
`p i : Ω i → ℝ` (`0 ≤ p i a` and `∑ a, p i a = 1`), drawn independently: the point `x` has
weight `∏ i, p i (x i)`. The definitions, for a function `f` of the point:

* `wmean r h` and `wvar r h` — the mean `∑ a, r a * h a` and the variance
  `∑ a, r a * (h a - wmean r h) ^ 2` of `h` under the weights `r`;
* `weight p x` — the product weight `∏ i, p i (x i)` of the point `x`;
* `expect p f` and `variance p f` — the mean and the variance of `f` under the product law
  (`wmean` and `wvar` with the weights `weight p`);
* `coordVar p i f x` — the variance of `f` in coordinate `i` alone, the other coordinates held at
  those of `x`: `wvar (p i) (fun a => f (Function.update x i a))`.

The results, order CLOUD-MATH-3, item 121 of MATH-PLAN-library-2:

* `variance_le_sum_variance_coord` — the Efron–Stein inequality,
  `variance p f ≤ ∑ i, expect p (coordVar p i f)`, that is `Var f ≤ ∑ᵢ E[Varᵢ f]`;
* `variance_le_sum_sq_div_four` — bounded differences: if changing coordinate `i` alone moves `f`
  by at most `c i`, then `variance p f ≤ ∑ i, c i ^ 2 / 4`.

The proof is by induction on `n`, splitting off coordinate `0`. The law of total variance
(`variance_split`) writes `variance p f` as the mean, over the other coordinates, of the variance
in coordinate `0`, plus the variance of the average over coordinate `0` (`marg`). The first term is
the mean of `coordVar p 0 f` (`expect_coordVar_zero`); the induction hypothesis bounds the second,
and since the variance of an average is at most the average of the variances (`wvar_mix_le`), each
of its coordinate terms is at most the matching term for `f` (`coord_succ_le`). Bounded
differences then follow from the weighted Popoviciu inequality: values in a band of width `c` have
variance at most `c ^ 2 / 4` (`wvar_le_of_bdd`).

The proof is the draft `d121-r3-s1` (written by Claude Opus 5.5 through the Anthropic Batch API,
the lane's API-CREDIT-1 work), adapted by the Claude Code cloud session that landed it (order
CLOUD-MATH-3): the draft's namespace `EfronStein` became this module's, the two main theorems moved
inside it and their references to `EfronStein.…` lost the prefix; targeted imports, docstrings, and
`change` where a `show` changed the goal.
-/

universe u

namespace ClassicalLean.Probability.EfronStein

