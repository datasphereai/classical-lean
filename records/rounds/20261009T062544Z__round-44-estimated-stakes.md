# Round 44 — the stake when the edge is only estimated, a count from the spread, what a signal is worth with cash, and a mixture of fixed stakes (order LEAN-16)

Session: Claude Code `session_01CAgquuMxBPCgwwHySSAPvP` on DSMain, as dustin, executing order
`LEAN-16` (`records/orders/20261009T061600Z__claude-ai__order-lean16-estimated-stakes.md`), in the
worktree `~/lean/classical-lean-paper-crypto` on branch `paper-crypto-11`, made from `origin/master` =
`3f910db`. Lean and Mathlib v4.34.0. Nothing pushed. Evidence: `~/lean/lean16-checks/` (outside the
repository), `evidence.log` (time, label, rc, prediction, command per run).

First part, written before any module change, so that gate 6 finds the new module's path before the
module's commit (LEAN-15-CLOSE.md, trap 5). Completed after the work with commit hashes, counts and
gate results.

Modules this round plans to change or add (as the claim row):

* `ClassicalLean/Analysis/GeneralGrowth.lean` — item 1.
* `ClassicalLean/Analysis/LogGrowthRobustness.lean` — item 2.
* `ClassicalLean/Probability/EdgeGrowth.lean` — items 3 and 4.
* `ClassicalLean/InformationTheory/SignalGrowth.lean` — item 5.
* `ClassicalLean/Analysis/UniversalMixture.lean` — new module, item 6; added to `ClassicalLean.lean`.
* `ClassicalLean/Probability/EffectiveSampleSize.lean` — item 7.
* `ROADMAP.md` §1 (the online-learning bridge) and §1.16 (the combinatorics bridge, proved).
