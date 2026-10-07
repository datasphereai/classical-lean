# Round 35 — trusting an estimate, what a wrong one costs, fair games, log returns (order LEAN-7)

Session: Claude Code `session_01KyYusMNSHJap88c9A6s6K2` on DSMain, as dustin, executing order
`LEAN-7` (`records/orders/20261007T203600Z__claude-ai__order-lean7-trust-estimates.md`), on branch
`paper-crypto-2`, which sits on `paper-crypto` (`812a3c4`, round 34), in the worktree
`~/lean/classical-lean-paper-crypto`. Lean and Mathlib v4.34.0. Nothing was pushed.

Modules added, with the new top-level directory `Probability/`:

* `ClassicalLean/Probability/SampleMean.lean` — item 1.
  - `measureReal_abs_sampleMean_sub_ge_le`: for independent `X i` in `[0, 1]` with common mean
    `p`, `P(|mean of n − p| ≥ e) ≤ 2 exp(−2 n e²)`.
  - `sampleSizeOK` / `minSampleSize`: a computable test on rationals, with
    `two_mul_exp_neg_le_of_sampleSizeOK` and
    `measureReal_abs_sampleMean_sub_ge_le_of_sampleSizeOK`. It rests on `(1 + y/k)^k ≤ exp y`.
  - Mathlib already had Hoeffding's lemma (`hasSubgaussianMGF_of_mem_Icc`) and the one-sided
    inequality (`HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun`); this module uses both.
* `ClassicalLean/Analysis/LogGrowthRobustness.lean` — items 2 and 4.
  - `logGrowth_lt_optimalFraction` and `logGrowth_lt_of_estimate_ne`: a fraction other than the
    optimum, or one from a wrong estimate, is strictly worse.
  - `logGrowth_neg_of_lt`: growth is negative above `2 b x*/(1 − p)`, for every payout.
  - `half_logGrowth_le`: half the optimal fraction keeps at least half the optimal growth.
  - `log_prod_growth`: Mathlib's `Real.log_prod`, restated.
  - `one_add_mul_one_sub_lt_one` and `log_one_add_add_log_one_sub_neg`: up r then down r loses.
  - No "twice the optimum" claim: an exact check found it false for many payouts above 1.
* `ClassicalLean/Probability/FairGame.lean` — item 3. `integral_stoppedValue_eq`: for a real
  martingale and a stopping time bounded by `N`, `E[f_τ] = E[f_0]`. It is built on Mathlib's
  `Submartingale.expected_stoppedValue_mono`, applied to the martingale and to its negative.

`ClassicalLean.lean` gains three import lines.

Before any statement was written, each was checked with exact numbers:
- 100 exact binomial tails against `2 exp(−2 n e²)`;
- 7928 cases of the sample-size test;
- 21,364, 1,591 and 64 cases for item 2;
- exact expectations of a ±1 walk stopped at +1 or at step N, all 0.

There were 0 failures. The least `n` for `e = 0.1`, `δ = 0.05`, `k = 64` is 190: Python's exact
search and Lean's `#eval minSampleSize (1/10) (1/20) 64 1000 = some 190` agree.

Per-module theorem-constant counts (`env.getModuleFor?`, the axiom gate's predicate):
`Probability/SampleMean` **21**, `Analysis/LogGrowthRobustness` **18**, `Probability/FairGame`
**1**. The total is 1729, against 1689 on `paper-crypto`.

`#print axioms`: every new public theorem gives `[propext, Classical.choice, Quot.sound]`.
`lake build`: 0 warnings, after seven lines over 100 characters were split.
