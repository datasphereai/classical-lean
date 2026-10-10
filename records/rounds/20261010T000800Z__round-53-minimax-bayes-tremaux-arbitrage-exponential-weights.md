# Round 53 — von Neumann's minimax theorem, Bayes equals minimax, Trémaux's rule, no gain around a cycle with Bellman–Ford, and the game's value by exponential weights (order LEAN-25)

Session: Claude Code `session_01Y8vMKHokSopC3taexkCYny` on DSMain, as dustin, executing order
`LEAN-25` (`records/orders/20261010T000700Z__claude-code__order-lean25-minimax-bayes-tremaux-arbitrage-exponential-weights.md`),
batch 9 of the plan `/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md` (sha256
c73957af6a9f2d19aacfd3acfc1d42d9a2a124fabefae62bbfee026090422898), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `paper-crypto-20`, made from `origin/master` =
`ed64909` (equal to `git ls-remote github master`). Lean and Mathlib v4.34.0. Nothing pushed.
Evidence: `~/lean/lean25-checks/` (outside the repository), `evidence.log` (time, label, rc,
prediction, command per run).

First part written before any module change, so that gate 6 finds the new modules' paths before
their commits; completed after the work, below. Item numbers are the plan's.

Modules this round plans to add or change (as the claim row):

* `ClassicalLean/Analysis/FiniteGame.lean` — new module, items 62, 63 and 66; added to `ClassicalLean.lean`.
* `ClassicalLean/Combinatorics/Tremaux.lean` — new module, item 64; added to `ClassicalLean.lean`.
* `ClassicalLean/Combinatorics/ArbitrageCycle.lean` — new module, item 65; added to `ClassicalLean.lean`.

Mathlib re-checked before the records were written (`~/lean/lean25-checks/search.out`): none of
the five items is in Mathlib v4.34.0, so none is dropped or reduced. The plan written before any
Lean or records work: `~/lean/lean25-checks/plan.md`.
