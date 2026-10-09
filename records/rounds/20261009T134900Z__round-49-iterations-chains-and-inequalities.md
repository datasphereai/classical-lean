# Round 49 — Jacobi iteration, Newton's method, finite chains, Wald's identity, Fano's and Hadamard's inequalities, the binomial variance, and Mathlib's relative entropy on a finite set (order LEAN-21)

Session: Claude Code `session_019DbYoaqCsdYF7tW4YCkR4P` on DSMain, as dustin, executing order
`LEAN-21` (`records/orders/20261009T134800Z__claude-code__order-lean21-iterations-chains-and-inequalities.md`), batch 5 of the plan
`/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md` (sha256
a3006a18bb59a1228f69b5426beb12bb9ec9f9e79ba61c2bcf91563a14665216), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `paper-crypto-16`, made from `origin/master` =
`59a4749`. Lean and Mathlib v4.34.0. Nothing pushed. Evidence: `~/lean/lean21-checks/` (outside the
repository), `evidence.log` (time, label, rc, prediction, command per run).

First part written before any module change, so that gate 6 finds the new modules' paths before
their commits; completed after the work, below.

Modules this round plans to change or add (as the claim row):

* `ClassicalLean/Analysis/JacobiIteration.lean` — new module, item 32; added to `ClassicalLean.lean`.
* `ClassicalLean/Analysis/NewtonMethod.lean` — new module, item 33; added to `ClassicalLean.lean`.
* `ClassicalLean/Probability/FiniteChain.lean` — new module, item 34; added to `ClassicalLean.lean`.
* `ClassicalLean/Probability/FairGame.lean` — item 35 (Wald's identity).
* `ClassicalLean/InformationTheory/Fano.lean` — new module, item 36; added to `ClassicalLean.lean`.
* `ClassicalLean/Algebra/HadamardInequality.lean` — new module, item 37; added to `ClassicalLean.lean`.
* `ClassicalLean/Probability/BinomialVariance.lean` — new module, item 38 (Mathlib's `proof_wanted`); added to `ClassicalLean.lean`.
* `ClassicalLean/Probability/RelativeEntropyGrowth.lean` — item 39.

Mathlib re-checked before the records were written (`~/lean/lean21-checks/search.out`,
`search2.out`): none of the eight items is in Mathlib v4.34.0, so none is dropped. Item 38 is a
`proof_wanted` there (`Wanted/Probability/Distributions/Binomial.lean`, line 20), proved here with
its statement unchanged. Statements elaborated with `sorry` before this fragment: `st2.out`, rc 0,
24 `sorry` warnings, nothing else (`st1` had 5 lint warnings besides; fixed).
