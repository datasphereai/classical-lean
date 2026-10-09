# Round 47 — the descent lemma and gradient descent, KKT sufficiency, exponential weights, Rao–Blackwell, and Kolmogorov's maximal inequality (order LEAN-19)

Session: Claude Code `session_016HZA2rbHQv4Gvdu2sAUW2u` on DSMain, as dustin, executing order
`LEAN-19` (`records/orders/20261009T110600Z__claude-code__order-lean19-gradient-descent-and-maximal.md`), batch 3 of the plan
`/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md` (sha256
b9b64503909bc9d42ab562b9aa83474e86fa5661be6c14b5b3add5badf8d1789), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `paper-crypto-14`, made from `origin/master` =
`eb2a150`. Lean and Mathlib v4.34.0. Nothing pushed. Evidence: `~/lean/lean19-checks/` (outside the
repository), `evidence.log` (time, label, rc, prediction, command per run).

First part written before any module change, so that gate 6 finds the new modules' paths before
their commits; completed after the work, below.

Modules this round plans to change or add (as the claim row):

* `ClassicalLean/Analysis/GradientDescent.lean` — new module, items 17 to 20; added to `ClassicalLean.lean`.
* `ClassicalLean/Analysis/ExponentialWeights.lean` — new module, item 21; added to `ClassicalLean.lean`.
* `ClassicalLean/Statistics/RaoBlackwell.lean` — new module, item 22; added to `ClassicalLean.lean`.
* `ClassicalLean/Probability/MaximalInequality.lean` — item 23.
* `ROADMAP.md` — §1.14, pattern P2 (its own commit).

Mathlib re-checked before the records were written (`~/lean/lean19-checks/search.txt`): none of
items 17 to 23 is in Mathlib v4.34.0, so none is dropped. Item 22 is to come from Mathlib's
`integral_condVar_add_variance_condExp` and item 23 from Mathlib's `maximal_ineq`; what this round
adds for item 23 is that the square of a square-integrable martingale is a submartingale.
