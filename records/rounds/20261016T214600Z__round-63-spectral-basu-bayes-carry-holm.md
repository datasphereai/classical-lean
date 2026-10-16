# Round 63 — the spectral density of a moving average, bounded completeness and Basu, Bayes equals minimax with infinite losses, three carried generalisations, Holm's step-down procedure (order LEAN-31)

Session: Claude Code `session_011sA11abhwhEtt7xhgzBBKC` on DSMain, as dustin, executing order
`LEAN-31` (`records/orders/20261016T214500Z__claude-ai__order-lean31-spectral-basu-bayes-carry-holm.md`),
batch 5 (items 101 to 105) of the plan `/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library-2.md`
(sha256 6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166), and its job 0 (the
Bloomfield and Watson credit, LEAN-30's thread 6), in the worktree `~/lean/classical-lean-paper-crypto`
on branch `lean-31`, made from `49c4c9833f4f49610ef710aa69531cb84490b6e1` (order LEAN-30's last
commit). Lean and Mathlib v4.34.0. Nothing pushed. Evidence: `~/lean/lean31-checks/` (outside the
repository), `evidence.log` (UTC time, label, rc, prediction, command per run). Plan: lane
`lean/LEAN-31-PLAN.md` (sha256 b3b5ca1d8751a8998e4a293b801eafb95897609757bec48a8d990bb0eeecb5d0),
approved by Dustin on 2026-10-16, with its job 0 proposal (both credits get the full, checked
reference). Dustin's ruling of 2026-10-16, with the approval: whole-library runs go under a 24G memory
cap, not the order's 12G (DSMain measured at 62.2 GiB; `~/CLAUDE.md` records it); still one at a time.

**Order LEAN-30's push.** Both remotes are at `49c4c9833f4f49610ef710aa69531cb84490b6e1`,
re-measured by `git ls-remote origin master` and `git ls-remote github master` before this fragment
was written (evidence label `lsremote`). Pushed by Dustin, 2026-10-16 13:16 EDT (store row
20261016-010). LEAN-30's INDEX State cell and CLAIMS row gain that clause, and nothing else in them
changes.

First part written before any Lean file changed; completed after the work, below.

## Files this round changes

Module files, each spelled in full:

* item 101: `ClassicalLean/Probability/MovingAverage.lean` (extended; no new import);
* item 102: `ClassicalLean/Statistics/Sufficiency.lean` (extended);
* item 103: `ClassicalLean/Analysis/FiniteGame.lean` (extended);
* item 104: `ClassicalLean/Statistics/ResidualVariance.lean`, `ClassicalLean/Probability/LikelihoodScore.lean` and `ClassicalLean/Probability/EffectiveSampleSize.lean` (extended; the last gains the imports
  `Mathlib.Probability.HasLawExists` and `Mathlib.Probability.Distributions.Gaussian.Real`);
* item 105: `ClassicalLean/Probability/StepDownProcedure.lean` (new; imports `Mathlib.MeasureTheory.Measure.Real`), and its import line in
  `ClassicalLean.lean`;
* job 0: `ClassicalLean/Statistics/GeneralizedLeastSquares.lean` (docstring and comment lines only).

Also, as the order allows: `tools/vacuity_reviewed.txt` (only if a helper is listed under job 2's
2c), `records/` (this fragment, `records/orders/INDEX.md`, `records/CLAIMS.md`, `records/README.md`'s
one sentence, the order's copy, and the new bridge baseline `records/bridges/LEAN-31/`), `HANDOFF.md`
and `ROADMAP.md` (job 3).

Records files written by this session's commands, not by the evidence helper (HANDOFF.md rule 32):
the order's copy (by `cp` from the lane inside `ev.sh --nolean`, label `order-copy`, its sha256 then
printed equal to the order's, 9a0df0902bab8de2d80bb2a59c872bb39b74b6657dbf1129466e5e7cfebc1242), this
fragment, the INDEX and CLAIMS rows and the README sentence (by `scripts/records_first.py`).

The vacuity gate is used as LEAN-30 left it. The standing rules of round 58 apply, and so does the
bridge search's standing rule of round 55. Counts at `49c4c98` are order LEAN-30's measured values
(4176 jobs, 3345 theorem constants, 128 modules; bridge baseline `records/bridges/LEAN-30/`).

## Completed after the work
