# Round 39 — the rest of the trading math (order LEAN-11)

Session: Claude Code `session_013Qr4CQrBpWChEJzEPW8Ewo` on DSMain, as dustin, executing order `LEAN-11`
(`records/orders/20261007T231500Z__claude-ai__order-lean11-trading-math-3.md`), on branch `paper-crypto-6`
(on `origin/master` = `c571611`, which holds `paper-crypto-5`), worktree `~/lean/classical-lean-paper-crypto`.
Lean and Mathlib v4.34.0. Nothing was pushed. Records were written before the modules (`9775d80`).

Modules added. Two counts per module: theorems written (what a reader counts) and theorem constants
under the axiom gate's predicate (which adds Lean's generated constants):

* `ClassicalLean/Probability/RuinBound.lean` (7 written, 9 constants), item 1: the mean of a
  two-valued factor's power; the 2^(-theta) chance of halving from `ruinConditionOK` alone, for
  independent win events, within N steps and with no limit (`tendsto_measure_iUnion_atTop`).
  theta > 0 was dropped: at theta = 0 the bound is 1.
* `ClassicalLean/Analysis/GrowthMaximiser.lean` (16 written, 17 constants), item 2: exactly one
  maximiser of the growth on [0, 1/a) for any finite returns with a negative worst return;
  m/(s2 + a m) <= x* and, when s2 > b m, x* <= m/(s2 - b m).
* `ClassicalLean/Probability/LikelihoodScore.lean` (12 written, 16 constants), item 3: the score
  (q/p0)^wins ((1-q)/(1-p0))^losses is a nonnegative supermartingale from 1 when the win chance
  given the past is at most p0 <= q <= 1; it reaches 1/alpha with chance at most alpha, within N
  outcomes and with no limit. q must be fixed in advance.
* `ClassicalLean/Probability/CovarianceDirections.lean` (12 written, 17 constants), item 4:
  Var(sum w X) = w'Sw; S positive semidefinite (linked to Mathlib's `covarianceBilin`); S positive
  definite exactly when no nonzero mix is almost surely constant; over unit weights in
  `EuclideanSpace`, the largest and least variances are eigenvalues reached at eigenvectors
  (Mathlib's `hasEigenvector_of_isMaxOn`, `hasEigenvector_of_isMinOn`).
* `ClassicalLean/Probability/TwoStateChain.lean` (7 written, 15 constants), item 5: the matrix is
  in Mathlib's `rowStochastic`; the one steady distribution for s + t > 0; the n-step formula;
  forgetting for s + t < 2; mean spell 1/s.
* `ClassicalLean/Probability/LinearPrediction.lean` (11 written, 28 constants), item 6: the one best
  coefficient Cov/Var X and the leftover Var Y (1 - rho^2); each value of the first-order recursion
  is independent of every later noise, derived from joint independence; corr(x t, x (t+k)) = a^k.
* `ClassicalLean/InformationTheory/SignalGrowth.lean` (7 written, 9 constants), item 7: best growth
  with a signal minus best growth without it is the library's `mutualInfo`, for any positive
  payouts, all wealth staked, stakes positive where the chance is.
* `ClassicalLean/Analysis/RoundingError.lean` (8 written, 24 constants), item 8: gamma n bounds for
  n rounding factors, a product of n + 1 numbers and a left-to-right sum of n + 1 numbers.

Totals: 80 theorems written, 135 constants; the axiom gate counts 2001, against 1866 on
`paper-crypto-5`. `#print axioms` on all 80 gives `[propext, Classical.choice, Quot.sound]`.
`lake build` 0 warnings. Each statement was checked with exact numbers first, and each hypothesis
was shown to fail when dropped (Python exact checks for all eight; Lean refutations for items 2,
3, 5, 7 and 8, and Lean checks of the condition values for item 1, each with a planted control
that fails; item 4 and item 6 by exact computation only). Details are in the LEAN-11 report.
