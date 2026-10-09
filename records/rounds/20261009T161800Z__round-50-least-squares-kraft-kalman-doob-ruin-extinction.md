# Round 50 — recursive least squares, the converse of Kraft's inequality, the scalar Kalman filter's error variance, Doob's L² inequality, gambler's ruin, and Galton–Watson extinction (order LEAN-22)

Session: Claude Code `session_015uyBADuYuNNAwLUWbUvxWF` on DSMain, as dustin, executing order
`LEAN-22` (`records/orders/20261009T161700Z__claude-code__order-lean22-least-squares-kraft-kalman-doob-ruin-extinction.md`),
batch 6 of the plan `/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md` (sha256
5c2381ba371a3b810dbc39302c724ff7d2279fca9d9870d354f269ae6f048fc0), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `paper-crypto-17`, made from `origin/master` =
`5c25955`. Lean and Mathlib v4.34.0. Nothing pushed. Evidence: `~/lean/lean22-checks/` (outside the
repository), `evidence.log` (time, label, rc, prediction, command per run).

First part written before any module change, so that gate 6 finds the new modules' paths before
their commits; completed after the work, below. Item numbers are the plan's: item 42 is the Kalman
filter's variance, item 45 Galton–Watson extinction.

Modules this round plans to change or add (as the claim row):

* `ClassicalLean/Statistics/GaussMarkov.lean` — item 40 (recursive least squares).
* `ClassicalLean/InformationTheory/SourceCoding.lean` — item 41 (the converse of Kraft's inequality).
* `ClassicalLean/Probability/KalmanVariance.lean` — new module, item 42; added to `ClassicalLean.lean`.
* `ClassicalLean/Probability/MaximalInequality.lean` — item 43 (Doob's `L²` inequality).
* `ClassicalLean/Probability/GamblersRuin.lean` — new module, item 44; added to `ClassicalLean.lean`.
* `ClassicalLean/Probability/Extinction.lean` — new module, item 45; added to `ClassicalLean.lean`.
* `ClassicalLean/InformationTheory/Channel.lean` — module docstring only: the `klDiv` bridge is
  proved (order LEAN-21, item 39), no longer future work. `HANDOFF.md` §3 likewise.

Mathlib re-checked before the records were written (`~/lean/lean22-checks/search.out`,
`search2.out`): none of the six items is in Mathlib v4.34.0, so none is dropped. Statements
elaborated with `sorry` before this fragment: `st2.out`, rc 0, 24 `sorry` warnings, nothing else
(`st1` had 3 lint warnings besides; fixed). The exact checks behind the needed-hypothesis table:
`checks.py`, `chk1.out`, ALL OK.
