# Round 81 — merge of orders CLOUD-MATH-5 and CLOUD-MATH-6 into master, after MERGE-4 (order MERGE-5)

Session: Claude Code `session_01HgueTXXQb4tMTTEcj9aiW4` on DSMain, as dustin, executing order
`MERGE-5` (`records/orders/20261030T225632Z__claude-ai__order-merge5-cloud-math-5-6.md`, written by
claude-ai, copied verbatim; lane `lean/MERGE-5/order.md`, sha256
`6fc1ae7d27917f52a3a44c25ee8b506d758465ee3dc23980094c9de8ee0f39c3`), to the lighter procedure (store
row 20261026-063), in the worktree `~/lean/classical-lean-paper-crypto` on branch `merge-5`, from
`8631a8d3c4316d85c78df697436b0245fa24cf1b` (MERGE-4's last commit, master on both remotes).
Evidence: `~/lean/merge5-checks/` (outside the repository); every count below is read from a saved
output there, cited by its file name.

This round lands order CLOUD-MATH-5 (round 79, written in a cloud session on GitHub branch
`cloud-math-5`, `d36e20a55c633b371e6aacd2bb144f7d913b734f`) and order CLOUD-MATH-6 (round 80, GitHub
branch `cloud-math-6`, `19cbbe7fa310f87628a3dadb25ad80a0fb7ce628`) by two merges, one after the other.
It re-proves and edits nothing in a module.

## Modules this round brings in (unchanged by the merges; rounds 79 and 80 name them too)

From `cloud-math-5` (round 79):

* bridge 158: `ClassicalLean/Probability/HolmInsideStepUp.lean`
* bridge 155: `ClassicalLean/Probability/CorrelationBound.lean`
* bridge 164: `ClassicalLean/Statistics/PinskerTest.lean`
* bridge 166: `ClassicalLean/Analysis/HeunRichardson.lean`
* bridge 167: `ClassicalLean/Analysis/HeunEulerMaclaurin.lean`

From `cloud-math-6` (round 80):

* bridge 157: `ClassicalLean/Probability/UrnVille.lean`
* bridge 154: `ClassicalLean/Probability/RuinConditional.lean`
* bridge 156: `ClassicalLean/Probability/RuinDivisibility.lean`
* bridge 165: `ClassicalLean/Probability/RuinChain.lean`
* bridge 159: `ClassicalLean/Probability/KolmogorovSmirnov.lean`

and `ClassicalLean.lean`: their ten import lines, CLOUD-MATH-5's five first.

Theorem-constant counts per module: rounds 79 and 80's census tables, 6, 2, 1, 5 and 4 (total 18) for
CLOUD-MATH-5 and 9, 1, 3, 34 and 5 (total 52) for CLOUD-MATH-6, in the order above; this round
measures nothing per module, since no module changes here.

## Order MERGE-4's push

By records/README.md rule 2, this round's first commit inserts into MERGE-4's INDEX row (immediately
before its commits cell) and its CLAIMS row (before the final ` |`) the text `; pushed by Dustin:
master 8631a8d on both remotes, CI run 41122857984 green`. "Green" is measured: `gh run view
41122857984 -R datasphereai/classical-lean --json status,conclusion,headSha` gave `completed`,
`success`, headSha `8631a8d3c4316d85c78df697436b0245fa24cf1b` on 2026-10-30 at about 19:50 EDT
(`step1-check.out`).

## Setup (measured in this session, 2026-10-30)

* Step 1 (`step1-check.out`, by `step1.sh`): the launch variable `1`; both fetches rc 0; both remotes'
  master `8631a8d…`; `github/cloud-math-5` `d36e20a…` and `github/cloud-math-6` `19cbbe7…`; porcelain
  empty; HANDOFF.md, ROADMAP.md and records/rules.toml sha256 as the order names; the four `incoming/`
  files' sizes and sha256 as the order names; one MERGE-4 header in HANDOFF.md; CI run 41122857984
  `completed success` on `8631a8d…` and CI run 41139926284 `completed success` on `19cbbe7…`.
* Step 2: `TypeDumpPI.lean` and `g8_typediff.py` copied from `~/lean/merge4-checks/`, each sha256 as
  the order names (`step2-scripts-sha.out`); at `8631a8d` the build had 4196 jobs (`before-build.out`)
  and the type dump 4363 records, thm 3844, def 519, elided 0 (`td-before-check.out`).
* The order copy: the permission rules on DSMain refuse `cp` out of the lane, so it was written from
  the connector's reply; its sha256 is the lane file's and `cmp` against the lane file returned 0.
* The RF rows: MERGE-4's push note and this order's two rows were written by
  `~/lean/merge5-checks/rf_rows.py` and checked by `rf_check.py` against `8631a8d`'s files
  (`rf-check.out`: both OK), with a planted fault in each file failing as it should
  (`rf-check-control.out`, by `plant.py`).

## Tree state

No whole-library gate runs before G; the gates of this round run on the clean tree at G, the last
commit outside `records/`, and are quoted in this round's second part. The check at this first
commit is check_records on the staged tree, which does not yet hold the ten modules.

First part written before the merges; commit hashes are added after the commits exist, below.

## Second part (written at close, 2026-10-30)

### The first merge and its resolution (step 4)

* Check (e) (`e5.out`, by `check_e.py`): from `8631a8d` to `d36e20a…`, each of
  `records/orders/INDEX.md` and `records/CLAIMS.md` gains exactly one line after its last line
  (`79a80`, `71a72`), the CLOUD-MATH-5 row.
* `git merge --no-ff --no-commit d36e20a…` (`merge1.out`): rc 1, CONFLICT in exactly those two files.
* `resolve.py` wrote each as RF's file without its last line, then the cloud's last line, then RF's
  last line (`resolve1.out`: INDEX 81 lines, CLAIMS 73). `resolve_check.py` (`resolve-check1.out`):
  (a), (b), (c) and (d) OK on both files; with a planted fault in each (last two lines swapped; one
  character changed) it fails as it should (`resolve-check1-control.out`, by `plant.py`).
* The staged list (`merge1-staged.out`) was the order's twelve entries: the five modules (A),
  `ClassicalLean.lean` (M), the two `incoming/` files (A), the cloud order copy and round 79 (A), the
  two resolved files (M).

### CLOUD-MATH-5's two files (step 5)

`lean/CLOUD-MATH-5/` held no `report.md` and its `data/` was empty before the copy. Through the drop
folder and `ds_copy_in`, then `ds_move` of the report: lane `lean/CLOUD-MATH-5/report.md` sha256
`a24d4fbaf8186bb860928423384c8c2259ede624bdef16a54a94bfe0eee527f8` (11915 bytes) and
`lean/CLOUD-MATH-5/data/cloud-review-1.md`
`b89a78be6dbcc54aa5ba6d7e5f41e34841fed124a3b7815dc8d49cf082c91d9e` (23135 bytes), each by `ds_hash`
equal to the order's hash (`drop5-sha.out`). Then `incoming/` removed (`rm-incoming5.out`: two
deletions).

### The second merge and its resolutions (step 6)

* Check (e) (`e6.out`): from `8631a8d` to `19cbbe7…`, INDEX `79a80` and CLAIMS `71a72`, the
  CLOUD-MATH-6 row only.
* `git merge --no-ff --no-commit 19cbbe7…` (`merge2.out`): rc 1, CONFLICT in `ClassicalLean.lean`,
  `records/CLAIMS.md` and `records/orders/INDEX.md`.
* The two records files resolved as in step 4 (`resolve2.out`: INDEX 82 lines, CLAIMS 74).
  `ClassicalLean.lean` resolved by `resolve_root.py`: the first branch's five import lines, then the
  second's five, after `ClassicalLean.Statistics.JamesSteinRisk` (184 lines). `resolve_check.py` and
  `root_check.py` (`resolve-check2.out`): OK on all three; the root's only hunk against `8631a8d` is
  `@@ -149,0 +150,10 @@`, 153 imports. Four planted faults (a dropped line, two rows swapped, an extra
  root line, the two import blocks swapped) each fail as they should (`resolve-check2-control.out`).
* The staged list (`merge2-staged.out`) was the order's twelve entries for CLOUD-MATH-6.

### CLOUD-MATH-6's two files (step 7)

As step 5: lane `lean/CLOUD-MATH-6/report.md` sha256
`2f311d02983d70ad4c1f2c1cf9392724f29013a63827158c3e3c290946cda326` (9854 bytes) and
`lean/CLOUD-MATH-6/data/cloud-review-1.md`
`06e44e8e2ba2688d7f94b6a94c02b1add93ff518e39a0c10d1679bc08b2e89fd` (11681 bytes), each by `ds_hash`
equal to the order's hash (`drop6-sha.out`). Then `incoming/` removed (`rm-incoming6.out`: two
deletions).

### Documents (step 8)

HANDOFF.md section 1 gained the CLOUD-MATH-5, CLOUD-MATH-6 and MERGE-5 paragraph after MERGE-4's, and
ROADMAP.md section 1.33 after 1.32 (`docs_insert.py`, `docs-insert.out`); drift PASS no drift before
the commit (`pre-G-drift.out`) and at G (`G-drift.out`).

### The gates at G (`23a3227`), clean tree, expected beside measured

Expected results: `expected.txt`, sha256
`3b7180fe65d99a9f887f2b845106aabf293184c5ef5347005de1bf2aac88ecc1`, written before the gates ran.
Each gate ran through `run.sh` under the 12 GB cap (`runs.log`), one at a time, by `gates.sh`.

| gate | expected | measured |
|---|---|---|
| `G-build` | 4206 jobs, 0 warnings | 4206 jobs, 0 `warning:` lines |
| `G-axiom` | PASS 3914 | PASS 3914, 0 scoped exceptions |
| `G-sorry` | PASS 153 | PASS 153 |
| `G-records` | PASS 153, 1 exemption | PASS 153, 1 exemption |
| `G-vacuity` | PASS, 1 reviewed helper | PASS, 1 reviewed helper, 0 VACUOUS-PENDING, 0 rule-5 run-outs |
| `G-vacuity-tests` | 89 tests, 47 flagged, 0 mismatches | the same |
| `G-banned` | PASS, 153 files and the root | PASS, 153 files and the root, 0 hits |
| `G-witness-all` | PASS, OK 208, copy-error 0 | `WITNESSGATE PASS modules=153`, OK=208, copy-error=0, TYPED=205, LISTED=1, time=1768.5s |
| `G-witness-tests` | 119 cases, 0 mismatches | the same |
| `G-modcount` | MODULES 5742 | MODULES 5742 |
| `G-typediff` | removed 0, added 73, changed 0, proof-only 0 | `DIFF removed=0 added=73 changed=0 proof_only=0`; `td-after.jsonl` 4436 records, thm 3914, def 522, elided 0 (`G-tdcheck.out`) |
| `G-gate7` | ALL PASSED, 153 modules, 3914, the planted fault named | `ALL PASSED for 23a3227…`, `SUMMARY modules=153 failed=0`, 3914 theorems, the planted fault `ClassicalLean.Analysis.LogDrag.mean_log_one_add_le` named |

The 73 added constants are the ten modules' 70 theorem constants (18 + 52, rounds 79 and 80) and
three definitions (`listnew.out`): `RuinChain.ruinChain` and two compiler-made match helpers of
`UrnVille`.

### The bridge search and the report tool

* `G-bridges` (rc 1): 3270 pairs, 903 shape candidates, N = 152; against `records/bridges/MERGE-4/` (commit `7841158`), 332 new keys (265 pairs,
  67 shapes) and 95 gone pairs. Every new key names one of the ten new modules (`bridge-read.out`, by
  `bridge_read.py`; `newpairs.txt`, `newshapes.txt`).
* The 95 gone pairs (`gone-check.out`, by `gone_check.py`): each shared only constants now used by
  more than 10 modules, so the search's df bound drops them; there are 8 such constants
  (`Finset.sum_ite_eq'`, `MeasureTheory.Measure.map`, `MeasureTheory.MeasureSpace.volume`,
  `Nat.cast_sub`, `Set.preimage`, `Set.range`, `iSup`, `mul_sub`), and none of them is in any
  MERGE-5 row. No existing module changed, so no import path between two old modules changed.
* How the new keys were read (`inherit-check.out`, by `inherit_check.py`): 95 of the 265 new pairs
  share only constants that a module the new module imports already shared with the same partner in
  the MERGE-4 baseline; 66
  of the 67 new shapes repeat a shape of an imported module (CorrelationBound's `covariance` from
  Gruss, RuinDivisibility's `linear recurrence` from LucasApparition, PinskerTest's `relative
  entropy` and `stochastic matrix` from NeymanPearson and Channel, RuinChain's four `stopping time`
  rows, all import-related); the one left, `stochastic matrix` Channel x PinskerTest, is
  import-related (PinskerTest imports Channel), so not a bridge by definition. The 170 other pairs
  (`residue-pairs.txt`) were read by their constants not so covered: 133 have one, the largest
  seven; they are casts (`Int.cast_*`), order and absolute-value facts (`LinearOrder`, `abs_one`,
  `zero_le_one`), `ENNReal.ofReal` conversions, measurability plumbing and finite-sum lemmas. The
  largest pair, KolmogorovSmirnov x NeymanPearson (19 constants, the distribution function `cdf` and
  its limits), has 17 of them already shared by GlivenkoCantelli, which KolmogorovSmirnov imports,
  with NeymanPearson; the other two are `LinearOrder` and `zero_le_one`. The
  one pair with shared martingale content, GamblersRuin x UrnVille (`MeasureTheory.Martingale`,
  `Martingale.supermartingale`, `Monotone.measure_iUnion`), comes from a common parent: both import
  `Probability.MaximalInequality` and apply it to their own martingale. No theorem needing both
  sides was found; no row appended to the bridges file. This was a read of the shared constants and
  of the import graph, not a proof attempt. The baseline is `records/bridges/MERGE-5/` (its
  `COMMIT` is G).
* `G-uninformative` (rc 0, once): 30 lines hold `CLOSES` anywhere (8 self-tests, 16 `B CLOSES`, 6
  summaries); none names a theorem of the ten modules (`closes-new.txt` empty, by `closes_new.py`,
  which searches the whole line). 16 lines name a new theorem, all `A OPEN`
  (`uninformative-new.txt`).

### Misses

* One shell command held a stray empty `python3 -I -` (Python read from standard input, which was
  empty); it ran nothing and wrote nothing. MERGE-4 had the same miss.
* The first run of `gates.sh` called `run.sh` directly, and `run.sh` has no execute bit:
  `Permission denied`, no gate ran (`gates-attempt1-norun.log`). `gates.sh` was changed to call
  `bash run.sh`, the stale outputs removed, and the whole run started again.
* The `sed` that adapted `rf_check.py` from MERGE-4's also changed its MERGE-4 row test on line 22;
  seen and put back before the script was used.
* Three data files (`index-row.md`, `claims-row.md`, `expected.txt`) were written by shell
  heredocs. They are data, not scripts; no script ran from standard input.

### Commits

`9804fbc` (records first), `5337361` (first merge, parents `9804fbc` and `d36e20a`), `1928b2a`
(`incoming/` removed), `a448431` (second merge, parents `1928b2a` and `19cbbe7`), `370ff97`
(`incoming/` removed), `23a3227` (documents, G) and this records commit (with the bridge baseline).
Nothing pushed; the push is Dustin's after claude-ai's push review.
