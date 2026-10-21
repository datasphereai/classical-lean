/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.InformationTheory.MutualInformation
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# The capacity of the binary symmetric channel

The binary symmetric channel with crossover probability `ε` receives an input `a : Fin 2` as the
output `b = a` with probability `1 - ε`, and as the other symbol with probability `ε`. An input law
`p : Fin 2 → ℝ` gives input and output the joint law `p a * (if a = b then 1 - ε else ε)`; its
mutual information is the library's `mutualInfo` (`InformationTheory/MutualInformation`), the
relative entropy of the joint law to the product of its marginals, with the natural logarithm.
`Real.binEntropy ε` is the binary entropy `h(ε) = -ε log ε - (1 - ε) log (1 - ε)`.

The results, order CLOUD-MATH-3, item 130 of MATH-PLAN-library-2:

* `mutualInfo_bsc_le` — for every `ε ∈ [0, 1]` and every input law `p`, the mutual information is
  at most `log 2 - h(ε)`;
* `mutualInfo_bsc_half` — at the uniform input, `p a = 1 / 2`, it equals `log 2 - h(ε)`.

Together: the capacity of the channel, the largest mutual information over input laws, is
`log 2 - h(ε)`, and the uniform input reaches it.

The proof. For a nonnegative joint law the mutual information is the sum of the entropies of the
two marginals minus the entropy of the joint law
(`mutualInfo_eq_shannonEntropy_add_shannonEntropy_sub_shannonEntropy`). Here the entropy of the
joint law is the input's entropy plus `h(ε)`, from `x y log (x y) = y (x log x) + x (y log y)`
(`mul_mul_log_mul`), so the mutual information is the output's entropy minus `h(ε)`
(`mutualInfo_bscJoint`). The output's entropy is at most `log 2` (`shannonEntropy_le_log_card`),
and at the uniform input the output law is uniform (`bscJoint_output_half`), with entropy `log 2`.

The proof is the draft `d130-r1-s1` (written by Claude Opus 5.5 through the Anthropic Batch API,
the lane's API-CREDIT-1 work), adapted by the Claude Code cloud session that landed it (order
CLOUD-MATH-3): the namespace, which the private `bscJoint` and its lemmas moved into with the main
theorems; docstrings; `change` where a `show` changed the goal; and `ite_eq_left` and
`ite_eq_right` for the deprecated `if_pos` and `if_neg`. Its two imports were already targeted.
The two witnesses at the end of the file, at `ε = 1 / 4`, are new: the item had no witness start.
-/

open ClassicalLean.Simplex

namespace ClassicalLean.InformationTheory.ChannelCapacity

