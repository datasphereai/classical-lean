# Round 38 — more of the math behind the trading (order LEAN-10)

Session: Claude Code `session_01Q4k3npejYw5xFw391cgtiu` on DSMain, as dustin, executing order `LEAN-10`
(`records/orders/20261007T221000Z__claude-ai__order-lean10-trading-math-2.md`), on branch `paper-crypto-5`
(on `paper-crypto-4` = `origin/master` `933d7b7`), worktree `~/lean/classical-lean-paper-crypto`.
Lean and Mathlib v4.34.0. Nothing was pushed. Records were written before the modules (`7201ef6`).

Modules added. Two counts per module: theorems written (what a reader counts) and theorem constants
under the axiom gate's predicate (which adds Lean's generated `_simp_`, `eq_1`, `_proof_` constants):

* `ClassicalLean/Probability/RelativeEntropyGrowth.lean` (9 written, 16 constants), item B1:
  - `growth p p o - growth p b o = sum p log(p/b)` (`growth_sub_growth_eq`);
  - that sum is Mathlib's `InformationTheory.klDiv` for measures on a finite set
    (`toReal_klDiv_eq_sum`, `growth_sub_growth_eq_toReal_klDiv`);
  - Gibbs, finite form; splitting by the true chances is best, and only it
    (`growth_le_growth_self`, `growth_eq_growth_self_iff`); payouts 1/r give D(p||r) - D(p||b).
* `ClassicalLean/Analysis/MinimumQuadraticForm.lean` (8 written, 11 constants), item B2:
  for positive definite S, `w* = S^-1 1 / (1'S^-1 1)` sums to 1, `w'Sw = (w-w*)'S(w-w*) + 1/c`,
  so `1/c` is the least value on weights summing to 1, reached only at `w*`.
* `ClassicalLean/Probability/FirstOrderRecursion.lean` (12 written, 14 constants), item B3:
  `Var[aX + E] = a^2 Var X + Var E` for independent X, E; the variance recursion; `E[x t] = a^t E[x 0]`;
  steady state `s^2/(1-a^2)`, its uniqueness and convergence for |a| < 1; unbounded growth for
  |a| >= 1; half-life `log(1/2)/log a` for 0 < a < 1; no shrinking at all for |a| >= 1.
* `ClassicalLean/Probability/StepUpProcedure.lean` (22 written, 53 constants), item B4:
  the Benjamini-Hochberg procedure; exactly `numRej` tests are rejected; a rejected p-value can be
  set to 0 without changing the count, and conversely; the expected share of false finds is at
  most `|H| q / m` for independent p-values with `P(p <= t) <= t` for the true nulls
  (`integral_falseShare_le`). The independence of one p-value from the others' count comes from
  Mathlib's `iIndepFun.indepFun_finset`; it is not a hypothesis.

Totals: 51 theorems written, 94 constants; the axiom gate counts 1866, against 1772 on
`paper-crypto-4`. `#print axioms` on all 51 gives `[propext, Classical.choice, Quot.sound]`.
`lake build` 0 warnings; axiom, vacuity, check_sorry, banned_vocab and check_records gates PASS.
Every statement was checked with exact numbers first, and each hypothesis was shown to fail when
dropped (Python enumeration for all four; Lean refutations for B1, B2 and B3). Details are in
the LEAN-10 report.
