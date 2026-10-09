# Round 45 — the residual variance, two-outcome Pinsker, a Chernoff bound from the score, an AR(1) average, data processing for mutual information, and source coding (order LEAN-17)

Session: Claude Code `session_019VHs1gNRScdbNoDT2HAccf` on DSMain, as dustin, executing order
`LEAN-17` (`records/orders/20261009T091024Z__claude-code__order-lean17-residual-variance-and-coding.md`), batch 1 of the plan
`/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md` (sha256
b24f5cc872ef2aa3506bddfdf6b88cb0b9aa570598d2af43647f43319d0387b2), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `paper-crypto-12`, made from `origin/master` =
`65e10e5`. Lean and Mathlib v4.34.0. Nothing pushed. Evidence: `~/lean/lean17-checks/` (outside the
repository), `evidence.log` (time, label, rc, prediction, command per run).

First part written before any module change, so that gate 6 finds the new modules' paths before
their commits; completed after the work, below.

Modules this round plans to change or add (as the claim row):

* `ClassicalLean/Statistics/FrischWaughLovell.lean` — item 1.
* `ClassicalLean/Probability/CovarianceDirections.lean` — item 2.
* `ClassicalLean/Statistics/ResidualVariance.lean` — new module, item 3; added to `ClassicalLean.lean`.
* `ClassicalLean/InformationTheory/Entropy.lean` — item 4.
* `ClassicalLean/Probability/LikelihoodScore.lean` — item 5.
* `ClassicalLean/Probability/EffectiveSampleSize.lean` — item 6.
* `ClassicalLean/InformationTheory/MutualInformation.lean` — item 7.
* `ClassicalLean/InformationTheory/SourceCoding.lean` — new module, item 8; added to `ClassicalLean.lean`.
