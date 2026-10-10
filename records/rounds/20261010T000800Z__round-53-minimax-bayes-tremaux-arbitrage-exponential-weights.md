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

## Completed after the work

All five items of batch 9 are done (62 to 66), with the plan's numbering, built in the suggested
order 62, 63, 66, then 64, then 65. Citations of works nobody here read are author, title and year
only: von Neumann 1928; Sion 1958; Wald 1950; Freund and Schapire 1999; Bellman 1958; Ford 1956.
Read and cited with pages: Lucas, Récréations mathématiques, tome I, 2nd ed., Gauthier-Villars et
fils, 1891, pp. 47–51 (Trémaux's rule), in the Internet Archive scan `p1rcrationsm00lucauoft`.

Commits on `paper-crypto-20` (made from `origin/master` = `ed64909`; nothing pushed):

* `dbab349` records before the work (this fragment's first part).
* `e6abbd4` `ClassicalLean/Analysis/FiniteGame.lean`, items 62, 63 and 66 (new module).
* `13b6659` `ClassicalLean/Combinatorics/Tremaux.lean`, item 64 (new module).
* `2489db4` `ClassicalLean/Combinatorics/ArbitrageCycle.lean`, item 65 (new module).
* `a1a3a67` two hypotheses restated (`Tremaux.anc_mem`, `noGainCycle_of_short`) after
  VacuityGate's case 3 flagged them; neither followed by applying its hypothesis, and neither
  says anything different now. The gate is unchanged.

Item 66 follows the ruling sent during the order: a statement about explicit averaged strategies,
proved without item 62 (checked by review r62, which walked every constant the proofs use), so it
is a second proof of item 62's equality for payoffs in `[0, 1]`. Item 63 uses Mathlib's
`bayesRisk` and `minimaxRisk` unchanged; it needs at least one action, and a finite (not
necessarily Markov) kernel. Item 64's rule is Lucas's; rule 2's return is made inside one step.

Gates at `a1a3a67`: build 4160 jobs, 0 warnings; AxiomGate 3052; VacuityGate, check_sorry,
banned_vocab_scan, check_records PASS on 116. The theorem count was predicted blind: Method B 3052
(hit), Method A 3015 (miss by 37, outside its range 2988 to 3048). By kind, Method A against
measured: hand-written 107 / 107; equation lemmas 24 / 23 (`step`, `tremaux` got none,
`closedSimplex.eq_1` appeared in FiniteGame); matcher equations 0 / 8; `eq_def` 0 / 4; structure
helpers 3 / 3; `Inv` projections 8 / 8; `_proof_` 0 / 35 (inside theorems, mostly from `omega`: 27 in Tremaux,
5 in ArbitrageCycle; `step._proof_1`; `ruleKernel._proof_1`, `_2`); `_simp_` 18 / 4 (no
`field_simp` helper at all); `congr_simp` 1 / 5; `walkSum._sparseCasesOn_1.else_eq` 0 / 1.
Names in `~/lean/lean25-checks/census/new_*.names`.

Gate 7 (`~/lean/recheck/run-recheck.sh a1a3a67 ~/lean/classical-lean-paper-crypto`): ALL PASSED;
4160 jobs; leanchecker 116 modules, 0 failed; nanoda 90,190 declarations, no errors, only
propext, Classical.choice and Quot.sound; 3052 theorems from the export; the planted wrong proof
rejected and named. The export leaves out 17 `_unsafe_rec` compiler helpers, 3 of them new
(`Tremaux.run`, `walkSum`, `walkProd`). Cold reviews r62, r64, r65: PASS WITH FINDINGS, no BLOCKER
or MAJOR; findings applied except r62 F5 (the affine reduction of item 66 to every matrix) and
r65 F6 (Lean examples for the item 65 counterexamples, which are exact in `checks.py`). Not
reached: nothing in batch 9. Batch 10 not started.
