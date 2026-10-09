# Round 46 — the chain rule for entropy, Pinsker's inequality, the Hessian of log-sum-exp, Hermite–Hadamard and the trapezoidal rule, rounding in inner products and Horner's rule, and generalised least squares (order LEAN-18)

Session: Claude Code `session_014tMro6KYq7f532WnRJZyjY` on DSMain, as dustin, executing order
`LEAN-18` (`records/orders/20261009T100800Z__claude-code__order-lean18-chain-rule-pinsker-and-gls.md`), batch 2 of the plan
`/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md` (sha256
b9b64503909bc9d42ab562b9aa83474e86fa5661be6c14b5b3add5badf8d1789), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `paper-crypto-13`, made from `origin/master` =
`197910f`. Lean and Mathlib v4.34.0. Nothing pushed. Evidence: `~/lean/lean18-checks/` (outside the
repository), `evidence.log` (time, label, rc, prediction, command per run).

First part written before any module change, so that gate 6 finds the new modules' paths before
their commits; completed after the work, below.

Modules this round plans to change or add (as the claim row):

* `ClassicalLean/InformationTheory/MutualInformation.lean` — item 9.
* `ClassicalLean/InformationTheory/Channel.lean` — item 10.
* `ClassicalLean/Simplex/SecondOrder.lean` — item 11.
* `ClassicalLean/Analysis/HermiteHadamard.lean` — new module, items 12 and 13; added to `ClassicalLean.lean`.
* `ClassicalLean/Analysis/RoundingError.lean` — items 14 and 15.
* `ClassicalLean/Statistics/GeneralizedLeastSquares.lean` — new module, item 16; added to `ClassicalLean.lean`.

Mathlib re-checked before the records were written (`~/lean/lean18-checks/search.txt`): none of
items 9 to 16 is in Mathlib v4.34.0; item 12's left half is to come from Mathlib's
`ConvexOn.map_set_average_le`.
