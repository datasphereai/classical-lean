# Round 83 — merge of order CLOUD-MATH-7 into master, after MERGE-5 (order MERGE-6)

Session: Claude Code `session_01HgueTaJ6yK9xLKWCkuwEmo` on DSMain, as dustin, executing order
`MERGE-6` (`records/orders/20261101T230315Z__claude-ai__order-merge6-cloud-math-7.md`, written by
claude-ai, copied verbatim; lane `lean/MERGE-6/order.md`, sha256
`12a5db681386c6eace322d4b265d6a68958f75b349d724e141d9301b69c7d4e4`), to the lighter procedure (store
row 20261026-063), in the worktree `~/lean/classical-lean-paper-crypto` on branch `merge-6`, from
`d723fbfd171cf9c018ddc0160446984ef1daffee` (MERGE-5's last commit, master on both remotes).
Evidence: `~/lean/merge6-checks/` (outside the repository); every count below is read from a saved
output there, cited by its file name.

This round lands order CLOUD-MATH-7 (round 82, written in a cloud session on GitHub branch
`cloud-math-7`, `70677d783d5e2cee31778472dbf6640c279db4d0`) by one merge. It re-proves and edits
nothing in a module.

## Modules this round brings in (unchanged by the merge; round 82 names them too)

From `cloud-math-7` (round 82):

* bridge 170: `ClassicalLean/Algebra/HatMatrixRank.lean`
* bridge 172: `ClassicalLean/Algebra/CategoricalPseudoinverse.lean`
* bridge 168: `ClassicalLean/Analysis/KKTMultipliers.lean`
* bridge 169: `ClassicalLean/Statistics/ChiSquaredTest.lean`
* bridge 171: `ClassicalLean/Analysis/EigenvalueSubgradient.lean`

and `ClassicalLean.lean`: their five import lines, in that order.

Theorem-constant counts per module: round 82's census table, 2, 2, 1, 11 and 1 (total 17), in the
order above; this round measures nothing per module, since no module changes here.

## Order MERGE-5's push

By records/README.md rule 2, this round's first commit inserts into MERGE-5's INDEX row (immediately
before its commits cell) and its CLAIMS row (before the final ` |`) the text `; pushed by Dustin:
master d723fbf on both remotes, CI run 41336003462 green`. "Green" is measured: `gh run view
41336003462 -R datasphereai/classical-lean --json status,conclusion,headSha` gave `completed`,
`success`, headSha `d723fbfd171cf9c018ddc0160446984ef1daffee` on 2026-11-02 at 20:24 EST
(`step1.out`).

## Setup (measured in this session, 2026-11-02 EST)

* Step 1 (`step1.out`, by `step1.sh`): the launch variable `1`; both fetches rc 0; both remotes'
  master `d723fbf…`; `github/cloud-math-7` `70677d7…`, 9 commits on `d723fbf`; porcelain empty;
  HANDOFF.md, ROADMAP.md and records/rules.toml sha256 as the order names; the two `incoming/`
  files' sizes and sha256 as the order names; one MERGE-5 header in HANDOFF.md; CI run 41359365177
  `completed success` on `70677d7…` and CI run 41336003462 `completed success` on `d723fbf…`.
* Step 2: `TypeDumpPI.lean`, `g8_typediff.py` and `run.sh` copied from `~/lean/merge5-checks/`, each
  sha256 as the order names, and `run.sh`'s `D=` line changed (`step2_runsh_check.out`, by
  `step2_runsh_check.sh`: PASS); at `d723fbf` the build had 4206 jobs (`build.out`) and the type
  dump 4436 records, thm 3914, def 522, elided 0 (`td-before-check.out`).
* The order copy: the permission rules on DSMain refuse `cp` out of the lane, so it was written from
  the connector's reply; its sha256 is the lane file's and `cmp` against the lane file returned 0.
  Its timestamp is the lane file's mtime (`ds_stat`), as MERGE-5's was.
* The RF rows: MERGE-5's push note and this order's two rows were written by
  `~/lean/merge6-checks/rf_rows.py` and checked by `rf_check.py` against `d723fbf`'s files
  (`rf-check.out`), with a planted fault in each file failing as it should
  (`rf-check-control.out`, by `plant.py`).

## Tree state

No whole-library gate runs before G; the gates of this round run on the clean tree at G, the last
commit outside `records/`, and are quoted in this round's second part. The check at this first
commit is check_records on the staged tree, which does not yet hold the five modules.

First part written before the merge; commit hashes are added after the commits exist, below.

## Second part (written at close, 2026-11-03)

### The merge and its resolution (step 4)

* Check (e) (`e.out`, by `check_e.py`): from `d723fbf` to `70677d7…`, `records/orders/INDEX.md` gains
  exactly two lines after its last line (`82a83,84`, the LEAN-38 and CLOUD-MATH-7 rows) and
  `records/CLAIMS.md` exactly one (`74a75`, the CLOUD-MATH-7 row).
* `git merge --no-ff --no-commit 70677d7…` (`merge.out`): rc 1, CONFLICT in exactly those two files.
* `resolve.py` wrote each as RF's file without its last line, then the cloud's added lines in their
  order, then RF's last line (`resolve.out`: INDEX 85 lines, CLAIMS 76). `resolve_check.py`
  (`resolve-check.out`): (a), (b), (c) and (d) OK on both files; with a planted fault in a copy of each
  (one character changed, the last two lines swapped, a line dropped) it fails as it should, rc 1 six
  times (`resolve-check-control.out`, by `plant.py`).
* The staged list (`merge-staged.out`) was the order's twelve entries: the five modules (A),
  `ClassicalLean.lean` (M), the two `incoming/` files (A), the cloud order copy and round 82 (A), the
  two resolved files (M).

### CLOUD-MATH-7's two files (step 5)

`lean/CLOUD-MATH-7/` held only `order.md` and an empty `data/` before the copy. Through the drop
folder and `ds_copy_in`, then `ds_move` of the report: lane `lean/CLOUD-MATH-7/report.md` sha256
`ec813553023152612fa897311000b7540590921573eb6d57edc1d71da560590c` (11769 bytes) and
`lean/CLOUD-MATH-7/data/cloud-review-1.md`
`bd224a76f199f46f02c37bfeb11b471a30c0ccc4fb3ce6506656169af494cc60` (10333 bytes), each by `ds_hash`
equal to the order's hash (`drop-sha.out`). Then `incoming/` removed (`rm-incoming.out`: two
deletions).

### Documents (step 6)

HANDOFF.md section 1 gained the LEAN-38, CLOUD-MATH-7 and MERGE-6 paragraph after MERGE-5's, and
ROADMAP.md section 1.34 after 1.33 (`docs_insert.py`, `docs-insert.out`: HANDOFF 40 lines after
line 655, ROADMAP 22 lines before `## 2.`); drift PASS no drift before the commit (`pre-G-drift.out`)
and at G (`G-drift.out`).

### The gates at G (`e8398c2`), clean tree, expected beside measured

Expected results: `expected.txt`, sha256
`dcb6e79ede6faa067d198ae07a64fcdf28c6210b91e024fd2d2026bd248c7c32`, written before the gates ran.
Each gate ran through `run.sh` (sha256 `aa9286da…`) under the 12 GB cap (`runs.log`), one at a time,
by `gates.sh` (`gates.log`, rc 0).

| gate | expected | measured |
|---|---|---|
| `G-build` | 4211 jobs, 0 warnings | 4211 jobs, 0 `warning:` lines |
| `G-axiom` | PASS 3931 | PASS 3931, 0 scoped exceptions |
| `G-sorry` | PASS 158 | PASS 158 |
| `G-records` | PASS 158, 1 exemption | PASS 158, 1 exemption (`Simplex/Hessian.lean`) |
| `G-vacuity` | PASS, 1 reviewed helper | PASS, 1 reviewed helper, 0 VACUOUS-PENDING, 0 rule-5 run-outs |
| `G-vacuity-tests` | 89 tests, 47 flagged, 0 mismatches | the same (output sha256 `7463c448…`, equal to MERGE-5's reference) |
| `G-banned` | PASS, 158 files and the root | PASS, 158 files and the root, 0 hits |
| `G-witness-all` | PASS, OK 212, copy-error 0 | `WITNESSGATE PASS modules=158`, OK=212, copy-error=0, TYPED=205, LISTED=1, time=1795.6s |
| `G-witness-tests` | 119 cases, 0 mismatches | the same |
| `G-modcount` | MODULES 5747 | MODULES 5747 |
| `G-typediff` | removed 0, added 17, changed 0, proof-only 0 | `DIFF removed=0 added=17 changed=0 proof_only=0`; `td-after.jsonl` 4453 records, thm 3931, def 522, elided 0 (`G-tdcheck.out`) |
| `G-gate7` | ALL PASSED, 158 modules, 3931, the planted fault named | `ALL PASSED for e8398c2…`, `SUMMARY modules=158 failed=0`, 3931 theorems, the planted fault `ClassicalLean.Analysis.LogDrag.mean_log_one_add_le` named |

The 17 added constants are the five modules' 17 theorem constants (round 82's census: 2, 2, 1, 11, 1)
and no definitions (`listnew.out`); every ADDED line names one of the five modules.

### The bridge search and the report tool

* `G-bridges` (rc 1): 3352 pairs, 964 shape candidates, N = 157; against `records/bridges/MERGE-5/`
  (commit `23a3227`), 219 new keys (158 pairs, 61 shapes) and 76 gone pairs. Every new key names one
  of the five new modules (`bridge-read.out`, by `bridge_read.py`; `newpairs.txt`, `newshapes.txt`).
* The 76 gone pairs (`gone-check.out`, by `gone_check.py`): each shared only constants now used by
  more than 10 modules, so the search's df bound drops them; there are 7 such constants
  (`Finset.prod_const`, `Inner.inner`, `Measurable.aemeasurable`, `div_eq_mul_inv`, `inv_pow`,
  `starRingEnd`, `zero_le_one`), and none of them is in any MERGE-6 row. RESULT PASS. No existing
  module changed, so no import path between two old modules changed.
* How the new keys were read (`inherit-check.out`, by `inherit_check.py`): 75 of the 158 new pairs
  share only constants that a module the new module imports already shared with the same partner in
  the MERGE-5 baseline; 58 of the 61 new shapes repeat a shape of an imported module; the three left
  (`covariance` and `stochastic matrix` CategoricalPseudoinverse x Simplex.SecondOrder, `eigenvalues`
  Algebra.MinMax x EigenvalueSubgradient) are import-related, so not bridges by definition. The 83
  other pairs (`residue-pairs.txt`) were read one by one (`bridge-reading.md`). The largest,
  EigenvalueSubgradient x CovarianceDirections (15 constants) and x PrincipalComponents (10), share
  Mathlib's spectral theorem; CovarianceDirections imports Algebra.MinMax, which EigenvalueSubgradient
  imports too. A theorem joining them would be bridge 171 applied to covariance maps, with
  `exists_isMaxOn_variance_mix` renaming the largest eigenvalue; that is a substitution, and the
  covariance of a mixture is not affine in the weights, so it was not appended (the closest
  candidate). ChiSquaredTest x JamesSteinRisk (11), JamesStein (10) and Sufficiency (9) share the
  product-of-normals machinery; ChiSquaredTest and JamesSteinRisk both import
  Probability.ChiSquared and use `hasLaw_sum_sq_gaussian` the same way. The rest share matrix
  algebra, inner-product algebra, product measures, measurability and finite-set lemmas. No theorem
  needing both sides was found; no row appended to the bridges file. This was a read of the shared
  constants, imports and module headers, not a proof attempt. The baseline is
  `records/bridges/MERGE-6/` (its `COMMIT` is G).
* `G-uninformative` (rc 0, once): 30 lines hold `CLOSES` anywhere; none names a theorem of the five
  modules (`closes-new.txt` empty, by `closes_new.py`, which searches the whole line). A planted
  `B CLOSES` line naming `isUniformlyMostPowerful_sum_sq_gaussian` in a copy is found
  (`closes-new-control.out`). 4 lines name a new theorem: 3 `A OPEN`, 1 `A DEPENDENT`
  (`uninformative-new.txt`).

### Misses

* The first `ListNew.lean` run (step 7) came before the five modules were built: rc 1, no output
  used (`listnew-attempt1-nobuild.out`). A build (`pre-G-build`, 4211 jobs) then the run again, as
  MERGE-5 did.
* The `sed` that adapted `closes_new.py` from MERGE-5's also changed its docstring's "MERGE-4's
  trap 3"; seen and put back before the script was used.
* Data files (`msg-*.txt`, `expected.txt`, and the scripts `gates.sh`, `push-review.sh`,
  `imports_check.sh`, `ListNew.lean`) were written by shell heredocs; each was run from disk. No
  script ran from standard input.
* The report tool ran while `records/bridges/MERGE-6/` was already copied into the worktree,
  untracked; `grep` of `tools/UninformativeReport.lean` for `readFile`, `IO.FS` and `records` has
  no hit, so the tool does not read that folder.

### Commits

`27b1130` (records first), `bf49304` (the merge, parents `27b1130` and `70677d7`), `24517ed`
(`incoming/` removed), `e8398c2` (documents, G) and this records commit (with the bridge baseline).
Nothing pushed; the push is Dustin's after claude-ai's push review.
