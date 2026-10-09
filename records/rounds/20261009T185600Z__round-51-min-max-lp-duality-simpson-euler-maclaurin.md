# Round 51 — Courant–Fischer min–max and Weyl's inequality, strong duality for linear programs, Simpson's rule error bound, and Euler–Maclaurin to first order (order LEAN-23)

Session: Claude Code `session_01Sygvo6Yn77Tbb7i6N4k4a1` on DSMain, as dustin, executing order
`LEAN-23` (`records/orders/20261009T185500Z__claude-code__order-lean23-min-max-lp-duality-simpson-euler-maclaurin.md`),
batch 7 of the plan `/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md` (sha256
5c2381ba371a3b810dbc39302c724ff7d2279fca9d9870d354f269ae6f048fc0), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `paper-crypto-18`, made from `origin/master` =
`607f185`. Lean and Mathlib v4.34.0. Nothing pushed. Evidence: `~/lean/lean23-checks/` (outside the
repository), `evidence.log` (time, label, rc, prediction, command per run).

First part written before any module change, so that gate 6 finds the new modules' paths before
their commits; completed after the work, below. Item numbers are the plan's.

Modules this round plans to add (as the claim row):

* `ClassicalLean/Analysis/Simpson.lean` — new module, item 48; added to `ClassicalLean.lean`.
* `ClassicalLean/Analysis/EulerMaclaurin.lean` — new module, item 49; added to `ClassicalLean.lean`.
* `ClassicalLean/Algebra/MinMax.lean` — new module, item 46; added to `ClassicalLean.lean`.
* `ClassicalLean/Analysis/LinearProgram.lean` — new module, item 47; added to `ClassicalLean.lean`.

Mathlib re-checked before the records were written (`~/lean/lean23-checks/search.out`): none of
the four items is in Mathlib v4.34.0, so none is dropped or reduced. Statements elaborated with
`sorry` before this fragment, in scratch files outside the repository (`stmt/`): `st1-*.out`, rc 0,
23 `sorry` warnings (24 predicted: I counted 8 theorems in the linear-program file, which has 7)
and 2 lint warnings (`Fintype` where `Finite` suffices); after the fix `st2-*.out`, rc 0, 23 `sorry`
warnings, nothing else. The checks behind the needed-hypothesis table: `checks.py`, `chk1.out`,
ALL OK (34 lines).
