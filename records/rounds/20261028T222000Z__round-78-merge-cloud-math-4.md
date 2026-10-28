# Round 78 — merge of order CLOUD-MATH-4 into master, after LEAN-37 (order MERGE-4)

Session: Claude Code `session_01HgueTX15wcrz5PQyuToqtP` on DSMain, as dustin, executing order
`MERGE-4` (`records/orders/20261028T220740Z__claude-ai__order-merge4-cloud-math-4.md`, written by
claude-ai, copied verbatim; lane `lean/MERGE-4/order.md`, sha256
`5b87ced4659a8f9444f20806aff90f1e0583ec01a8888a84f3f3983c4b677f96`), to the lighter procedure (store
row 20261026-063), in the worktree `~/lean/classical-lean-paper-crypto` on branch `merge-4`, from
`3b62d24f740d6f649ce5a9c98a04a8b51edd28d7` (LEAN-37's last commit, master on both remotes).
Evidence: `~/lean/merge4-checks/` (outside the repository); every count below is read from a saved
output there, cited by its file name.

This round lands order CLOUD-MATH-4 (round 77, written in a cloud session on GitHub branch
`cloud-math-4`, `91d98e790d38b0118ac66a4ee444ac7267b083bb`) by one merge. It re-proves and edits
nothing in a module.

## Modules this round brings in (unchanged by the merge; round 77 names them too)

* bridge 160: `ClassicalLean/InformationTheory/HuffmanEntropy.lean`
* bridge 162: `ClassicalLean/Probability/PrincipalComponents.lean`
* bridge 161: `ClassicalLean/Statistics/JamesSteinRisk.lean`
* `ClassicalLean.lean`: their three import lines.

Theorem-constant counts per module: round 77's census (its table), 3, 4 and 10 for 160, 162 and
161, total 17; this round measures nothing per module, since no module changes here.

## Order LEAN-37's push

By records/README.md rule 2, this round's first commit inserts into LEAN-37's INDEX row (immediately
before its commits cell) and its CLAIMS row (before the final ` |`) the text `; pushed by Dustin:
master 3b62d24 on both remotes, CI run 40776387516 green`. "Green" is measured: `gh run view
40776387516 -R datasphereai/classical-lean --json conclusion,status` printed
`{"conclusion":"success","status":"completed"}` on 2026-10-28 at about 18:18 EDT.

## Setup (measured in this session, 2026-10-28)

* Step 1 (`step1-check.out`): the launch variable `1`; both fetches rc 0; both remotes' master
  `3b62d24…`; `github/cloud-math-4` `91d98e7…`; porcelain empty; HANDOFF.md, ROADMAP.md and
  records/rules.toml sha256 as the order names; the two `incoming/` files' sha256 as the order names.
* Step 2: `TypeDumpPI.lean` and `g8_typediff.py` written from the lane connector's replies, each
  sha256 as the order names (`step2-scripts-sha.out`); at `3b62d24` the build had 4193 jobs
  (`before-build.out`) and the type dump 4346 records, thm 3827, def 519, elided 0
  (`td-before-check.out`).
* The order copy: the permission rules on DSMain refuse `cp` out of the lane, so it was written from
  the connector's reply; its sha256 is the lane file's and `cmp` against the lane file returned 0.
* The RF rows: LEAN-37's push note and this order's two rows were written by
  `~/lean/merge4-checks/rf_rows.py` and checked by `rf_check.py` against `3b62d24`'s files
  (`rf-check.out`: both OK), with a planted fault in each file failing as it should
  (`rf-check-control.out`).

## Tree state

No whole-library gate runs before G; the gates of this round run on the clean tree at G, the last
commit outside `records/`, and are quoted in this round's second part. The check at this first
commit is check_records on the staged tree, which does not yet hold the three modules.

First part written before the merge; commit hashes are added after the commits exist, below.

## Completed after the work

### The merge and its two resolutions

* Check (e) (`step4-merge.out`): from `67d05bf` to `91d98e7`, each of `records/orders/INDEX.md` and
  `records/CLAIMS.md` gains exactly one line after its last line (`76a77`, `68a69`), the
  CLOUD-MATH-4 row.
* `git merge --no-ff --no-commit 91d98e7…`: rc 1, CONFLICT in exactly those two files.
* `resolve.py` wrote each as RF's file without its last line, then `91d98e7`'s last line, then RF's
  last line (`resolve.out`: INDEX 79 lines, CLAIMS 71). `resolve_check.py` (`resolve-check.out`):
  checks (e), (a), (b), (c) and (d) OK on both files; with a planted fault in each file (last two
  lines swapped; no CLOUD-MATH-4 row) it fails as it should (`resolve-check-control.out`).
* The staged list against RF (`merge-staged-vs-rf.out`) was exactly the order's list: the three
  modules (A), `ClassicalLean.lean` (M), the two `incoming/` files (A), the cloud order copy and
  round 77 (A), the two resolved files (M). Against `3b62d24` (`merge-staged.out`) it also holds
  RF's own two files, this order's copy and this fragment (A), which the order's list does not
  name; they are RF's, as `git diff --name-status 3b62d24 a34e1cb` shows in the same file.

### The cloud session's two files

`lean/CLOUD-MATH-4/` held no `report.md` and its `data/` was empty before the copy. Through the drop
folder and `ds_copy_in`, then `ds_move` of the report: lane `lean/CLOUD-MATH-4/report.md` sha256
`ffb88c36e6d7fea8090cd47ef24e214c344f92dfaaa30a4315967661af4191ac` (9758 bytes) and
`lean/CLOUD-MATH-4/data/cloud-review-1.md`
`b423184f4f46b1d4eb763b0790497d5154d00ebf67dc98a3a07f365a75a47779` (15947 bytes), each by `ds_hash`
equal to the order's hash. Then `incoming/` removed (`rm-incoming.out`: two deletions).

### Documents

HANDOFF.md section 1 gained the CLOUD-MATH-4 and MERGE-4 paragraph after LEAN-37's, and ROADMAP.md
section 1.32 after 1.31; drift PASS no drift (`G-drift.out`).

### The gates at G (`7841158`), clean tree, expected beside measured

Expected results: `expected.txt`, sha256
`b4873f7cc8f86cebacf6ea6f67b773278cb318a5c7da03be96b615dc341ec796`, written before the gates ran.
Each gate ran through `run.sh` under the 12 GB cap (`runs.log`).

| gate | expected | measured |
|---|---|---|
| `G-build` | 4196 jobs, 0 warnings | 4196 jobs, 0 `warning:` lines |
| `G-axiom` | PASS 3844 | PASS 3844, 0 scoped exceptions |
| `G-sorry` | PASS 143 | PASS 143 |
| `G-records` | PASS 143, 1 exemption | PASS 143, 1 exemption |
| `G-vacuity` | PASS, 1 reviewed helper | PASS, 1 reviewed helper, 0 VACUOUS-PENDING |
| `G-vacuity-tests` | 89 tests, 47 flagged, 0 mismatches | the same |
| `G-banned` | PASS, 143 files and the root | PASS, 143 files and the root, 0 hits |
| `G-witness-all` | PASS, OK 195, copy-error 0 | `WITNESSGATE PASS modules=143`, OK=195, copy-error=0, TYPED=205, LISTED=1, time=1708.5s |
| `G-witness-tests` | 119 cases, 0 mismatches | the same |
| `G-modcount` | MODULES 5732 | MODULES 5732 |
| `G-typediff` | removed 0, added 17, changed 0, proof-only 0 | `DIFF removed=0 added=17 changed=0 proof_only=0`; `td-after.jsonl` 4363 records, thm 3844, def 519, elided 0 |
| `G-gate7` | ALL PASSED, 143 modules, 3844, the planted fault named | `ALL PASSED for 7841158…`, `SUMMARY modules=143 failed=0`, 3844 theorems, the planted fault `ClassicalLean.Analysis.LogDrag.mean_log_one_add_le` named |

The 17 added constants are the three modules' 17 theorem constants and no definition
(`listnew.out`), round 77's census.

### The bridge search and the report tool

* `G-bridges` (rc 1): 3100 pairs, 836 shape candidates, N = 142; against `records/bridges/LEAN-37/`
  117 new keys (69 pairs, 48 shapes) and 8 gone pairs. Every new key names one of the three new
  modules (`newpairs.txt`, `newshapes.txt`). How they were read: each new pair's shared constants
  were read; the largest are general plumbing (orthonormal bases and inner products with
  Kantorovich, 8; the product measure with ScoreLookahead and Sufficiency, 7 and 6), and the rest
  share one to three general lemmas. The new shapes repeat, for the new modules, the shapes of the
  modules they import, already ruled on in `MATH-PLAN-library-2-bridges-2.md`: `binary strings` of
  HuffmanEntropy with CompressionTest and others (CompressionTest's scores hold for every code that
  passes Kraft's test, so a Huffman code adds nothing); `eigenvalues` of PrincipalComponents with
  the list ruled for `Analysis.PowerMethod`; `covariance` of PrincipalComponents and JamesSteinRisk
  with the list ruled for `Analysis.Gruss` (CramerRao's and GaussMarkov's covariances are finite
  weighted sums). No theorem needing both sides was found; no row appended. This was a read of the
  shared constants and of the earlier rulings, not a proof attempt. The baseline is
  `records/bridges/MERGE-4/`.
* `G-uninformative`: 22 `CLOSES` lines, none naming a theorem of the three modules
  (`closes-new.txt` empty); the six new theorems appear, four `A OPEN` and two `A DEPENDENT`
  (`uninformative-new.txt`).

### Misses

* In the RF control step, one shell command held a stray empty `python3 -I -` (Python read from
  standard input, which was empty); it ran nothing and wrote nothing.
* The order's step 4 list of staged files leaves out RF's two files; read as a wording gap, not a
  stop, as said above.

### Commits

`a34e1cb` (records first), `0cbd6c0` (the merge, parents `a34e1cb` and `91d98e7`), `3172ca1`
(`incoming/` removed), `7841158` (documents, G) and this records commit (with the bridge
baseline). Nothing pushed; the push is Dustin's after claude-ai's push review.
