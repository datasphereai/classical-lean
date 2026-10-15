# MERGE-1 order: CI and the five cloud modules into master, with gate 7

For a plain Claude Code session on DSMain, as dustin, in tmux `cc`. Written by claude-ai on
2026-10-15. Board: OPEN-WORK-20261011-r2.md, step 3 (the cloud sessions' merge).

## What is already true (measured by claude-ai, 2026-10-15 10:39 to 11:20 EDT, on DSMain over ssh from helios)

- `master` on both remotes (`/data/git/classical-lean.git` and GitHub) is
  `92a314c49fec6af16aefabcfd37cd6dbcb32d832`, LEAN-29's last commit. LEAN-29's gates at 0ff0d44
  (lean/LEAN-29-report.md, 89ebe004): build 4171 jobs, AxiomGate PASS 3246, check_sorry PASS 123,
  check_records PASS 123, VacuityGate PASS (1 reviewed helper), gate 7 ALL PASSED (4171 jobs, 123
  modules). Its bridge baseline is `records/bridges/LEAN-29/`; its two real bridges are rows 155
  and 156 of `MATH-PLAN-library-2-bridges-2.md` (f0aa214a).
- GitHub branch `cloud-ci` = `ed0bccbbe2a9090114f7d9bc5b8b188216d7b117`: one file,
  `.github/workflows/ci.yml` (CI: lean-action build plus AxiomGate, check_sorry, VacuityGate on
  every push to `master` and `cloud-*`). Its runs on GitHub: green on the clean tree, red on a
  planted `sorry` (CLOUD-1-CI-result.md).
- GitHub branch `cloud-math-1` = `d7756afae16c6e00424589d8a020315f24eb95be`, which contains
  `cloud-ci`: order CLOUD-MATH-1 (CLOUD-MATH-1-order.md, ae1295f3), five new modules
  `ClassicalLean/InformationTheory/HanInequality.lean`, `ClassicalLean/Analysis/FrankWolfe.lean`,
  `ClassicalLean/Analysis/StatePrices.lean`, `ClassicalLean/Probability/PolyaUrn.lean`,
  `ClassicalLean/Probability/Reflection.lean` (items 131, 135, 136, 137, 139), their five import
  lines, records (order copy, INDEX row, CLAIMS row, round 60), and `incoming/` (REPORT.md,
  PREDICTIONS.md, reviews/, 15 files). At its tip, alone: build 4175 jobs, AxiomGate PASS 3317,
  check_sorry 127, VacuityGate PASS; CI green (run 38676986252). claude-ai's check of it:
  CLOUD-MATH-1-result.md (5cd4c868).
- A trial merge of `cloud-math-1` into `92a314c` (in claude-ai's scratch clone, aborted, nothing
  pushed) conflicted in exactly three files, each only on lines both sides added at the same place:
  `ClassicalLean.lean` (LEAN-29's Gruss import against the five cloud imports),
  `records/CLAIMS.md` and `records/orders/INDEX.md` (one new row each side). Nothing else
  conflicted.
- The merge base of `92a314c` and `cloud-math-1` is `20303cd`. LEAN-29 changed the `.lean` files
  ConvexConjugate, EulerMethod, Gruss (new), Simpson, PrimitiveDivisor, GamblersRuin, LongestRun and
  `ClassicalLean.lean`. None of these is in the import closure of the five cloud modules (a script
  over the tree at `92a314c` walked the closure of their library imports, 10 modules, and found no
  overlap), so neither side's work can change the other's proofs or counts: the basis of rule 3.
- At `92a314c`: round 59 is LEAN-29's (`records/rounds/…round-59-…`), round 60 the cloud's;
  `tools/vacuity_reviewed.txt` holds 1 entry; remote `github` in the worktree has the default fetch
  refspec `+refs/heads/*:refs/remotes/github/*`.
- tools/check_records.py checks only that every module under `ClassicalLean/` is named in some
  records file (its docstring); naming a path that does not exist yet does not fail it.
- The worktree `~/lean/classical-lean-paper-crypto` is on `lean-29` at `92a314c`, clean. The main
  clone `~/lean/classical-lean` (the nightly's) is at `20303cd` and pulls at 03:30.

## Goal

`master` gains CI and the five modules, with LEAN-29's work intact, every gate passing on the
merged tree, gate 7 included, and the documents saying what changed. Dustin pushes after
claude-ai checks the push-review file.

## Scope

- **Branch.** `merge-1` from `92a314c` in `~/lean/classical-lean-paper-crypto`, made after Dustin
  approves your plan. Nothing pushed. No sudo.
- **You may change:** the three conflicted files, by rule 2 only (for `ClassicalLean.lean` that is
  the only change you make to a `.lean` file); `incoming/` (removed, after its copy to the lane);
  `records/`; `HANDOFF.md` and `ROADMAP.md` (job 3). What the merge itself brings in (five modules,
  `ci.yml`) is not a change by you.
- **You may not change** any other `.lean` file, anything under `tools/`, or `.github/`. A gate failing on
  the merged tree is a stop: report it, change nothing to make it pass.
- **Off limits:** the main clone's working tree and its `master`; `~/trading`; `~/lean/recheck`
  (`run-recheck.sh` is run, as gate 7, not edited); Dustin's `~/.config/classical-lean/banned-terms`;
  the GitHub branches (no push, no delete).
- **The night window and the memory cap,** exactly as LEAN-29's order says them
  (lean/LEAN-29-order.md, Scope): nothing that loads the library may run at 02:00 to 05:45 EDT or
  in the 15 minutes before 00:00; every whole-library run under
  `systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0`; never two at once; check
  `crontab -l` and both `systemctl list-timers` lists before you start; put `~/.elan/bin` on `PATH`.
- **Your plan** goes to `lean/MERGE-1-PLAN.md` (then -PLAN-2, never overwriting). Report its sha256.

## Check, then read

All lane paths in this order are under `/opt/datasphere/lane/inbox/threads/staging/` (ds_* tools: root `lane`, path `inbox/threads/staging/…`).
Check these sha256s first; if any differs, stop and say which:
- this order, `lean/MERGE-1-order.md`: the value in Dustin's prompt;
- `lean/LEAN-29-order.md` `e878aca2d617e65af38de731ec7223ae6c0125cf47f8b9d2f45affb26c0b3151`;
- `lean/LEAN-29-report.md` `89ebe00492ded3c6a01fe07fb5f0623dbaa19e4ae8da443c7005cc9c348b167f`;
- `CLOUD-MATH-1-order.md` `ae1295f372835e70a20f448d829254ab725b90556c68256ff1483b506e88365e`;
- `CLOUD-MATH-1-result.md` `5cd4c868c9c9f56bff9166cd6a252d0cc2572b2c4cc08d85cb1feda6346e4c81`;
- `CLOUD-1-CI-result.md` `f4daab995f6beffb6faa01c5687df051934ff5abf6142318c0d112a2085810e8`;
- `MATH-PLAN-library-2-bridges-2.md` `f0aa214a6d747e6c5a95979cd329fbca85e046a303089e3e70d8aa8c20320119`.
Then read them, and in the repository `records/README.md` and `HANDOFF.md` §1, §4 and §6.

## Rules

1. **Nothing is re-proved or edited in a module.** The five modules arrive as the cloud session
   left them; LEAN-29's as LEAN-29 left them. This order merges, measures and documents.
2. **Conflicts.** Expected: exactly the three files above. Resolve each by keeping every added line
   of both sides, in time order: in `ClassicalLean.lean` the Gruss import first, then the five
   cloud imports in the cloud's order; in `CLAIMS.md` and `INDEX.md` the rows in the order they
   were opened (LEAN-29, then CLOUD-MATH-1, then MERGE-1). After resolving, `git diff 92a314c` must
   show for these three files only added lines. A conflict in any other file, or a resolution that
   needs a removed line, is a stop.
3. **Predicted by claude-ai before this order was written**, from measured numbers, and resting on
   the measured fact that neither side imports the other's changed modules (above): the merged
   tree builds `4176` jobs (LEAN-29's 4171 + 5; the cloud's tip built 4175 from 20303cd's 4170,
   measured on 20303cd by the nightly and in CI, so its five modules added no Mathlib file) with 0
   warnings (both tips: LEAN-29's report and the cloud's report); AxiomGate PASS `3335` (3246 +
   89; the cloud's 3317 minus 20303cd's 3228, both measured: CI log and the 2026-10-15 nightly);
   check_sorry PASS `128`; check_records PASS `128`; VacuityGate PASS with 1 reviewed helper (the
   list holds 1 entry at 92a314c and the cloud added none), no new flag, no UNCHECKED, 0
   VACUOUS-PENDING; gate 7 ALL PASSED, 4176 jobs, 128 modules 0 failed, 3335, three standard
   axioms, planted fault named. Check them and add your own in a prediction file before any run
   (rule 4).
4. **Predict, then measure,** as LEAN-29 did: an evidence folder `~/lean/merge1-checks/` with
   `evidence.log` (time, label, rc, prediction, command); every prediction file hashed into the log
   before its run; hashes in records and the report by script, never typed.
5. **The merged tree is the one that counts.** Every gate runs on the clean tree of the last commit
   that touches anything outside `records/` (the commit that closes job 3; call it G and record
   its hash); later commits touch only `records/`, and check_records runs again at the final HEAD.

## Setup (after approval)

1. `git fetch origin && git fetch github cloud-math-1 cloud-ci` in the worktree. `origin/master`
   and `git ls-remote github master` must both be `92a314c…`, `github/cloud-math-1` `d7756af…`,
   `github/cloud-ci` `ed0bccb…`, `git merge-base --is-ancestor github/cloud-ci github/cloud-math-1`
   exit 0, `git merge-base 92a314c github/cloud-math-1` `20303cd…`, and `git status --porcelain`
   empty. If not, stop.
2. Make the evidence folder `~/lean/merge1-checks/` with `evidence.log`, and write the prediction
   file for every run below before the first one (rule 4). Then `git switch -c merge-1 92a314c`.
3. **Records first**, one commit, no `.lean` file: this order's copy as
   `records/orders/<UTC>__claude-ai__order-merge1-ci-and-cloud-math-1.md`; its INDEX row
   (`| MERGE-1 |`); a CLAIMS row; round 61's fragment
   `records/rounds/<UTC>__round-61-merge-ci-and-cloud-math-1.md`, naming the five module paths in
   full (they are already named in round 60) and saying the round lands CI and order CLOUD-MATH-1.
   check_records then: PASS 123 (it does not check that a named path exists).

## The work

### Job 1: the merge

`git merge --no-ff github/cloud-math-1` with message "Merge CI and order CLOUD-MATH-1 (items 131,
135, 136, 137, 139) into master (order MERGE-1)". Resolve by rule 2; your own MERGE-1 rows from
setup step 3 now also sit in CLAIMS and INDEX and keep their place at the bottom. Before
committing: `git diff --name-status 92a314c` lists only the five new modules,
`ClassicalLean.lean`, `.github/workflows/ci.yml`, `incoming/…`, and `records/…`; save that
output to the evidence folder.

### Job 2: incoming/ to the lane, then out of the tree

Copy through `ds_write_staging`, each post_sha256 compared with your own sha256sum:
`incoming/REPORT.md` to `lean/CLOUD-MATH-1-REPORT.md`; `incoming/PREDICTIONS.md` to
`lean/CLOUD-MATH-1-PREDICTIONS.md`; the 13 files of `incoming/reviews/` into one file
`lean/CLOUD-MATH-1-reviews.md`, each under a heading line giving its path, its byte length and its
sha256, then its bytes unchanged (build it by script; split it back by the lengths and check every
part hashes to its original). If any review file is not valid UTF-8, stop and say which. Then
`git rm -r incoming` in its own commit, naming the three lane files and their hashes in the message.

### Job 3: documents

- `HANDOFF.md` §1: a dated MERGE-1 paragraph with the counts; the five modules in its module lists
  where it lists modules.
- `HANDOFF.md` §4: a dated paragraph on CI: `.github/workflows/ci.yml` builds the library with
  `leanprover/lean-action` (pinned v1.6.2) and runs AxiomGate, check_sorry and VacuityGate on
  every push to `master` and to any `cloud-*` branch; it is not gate 7 (the independent recheck
  reached about 28 GB of memory uncapped and runs only on DSMain, under a 12 GB cap); a newer push cancels an older run on the same branch;
  about 11 minutes a run; GitHub's free plan gives 2,000 minutes a month for private repositories.
  Cite CLOUD-1-CI-result.md for its planted-fault test.
- `HANDOFF.md` §6: a dated line: cloud sessions push only their own `cloud-*` branches to GitHub
  (orders CLOUD-1 and CLOUD-MATH-1); `master` still moves only from DSMain, after claude-ai's check
  and on Dustin's push.
- `ROADMAP.md`: after LEAN-29's batch 3 section, a section for items 131, 135, 136, 137 and 139,
  landed from below the plan's cut by order CLOUD-MATH-1 in a cloud session and merged by MERGE-1.

### Job 4: the end checks, in this order

Commit jobs 1 to 3; the last of those commits is G (rule 5). The gates run first, before anything
else loads the library.

- **4a. The gates**, on the clean tree at G, each predicted first (rule 3): build; AxiomGate;
  VacuityGate (and its tests unchanged: 89, 47 flagged, 3 UNCHECKED as expected, 0 mismatches);
  check_sorry; check_records; gate 7 under the cap
  (`systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0 ~/lean/recheck/run-recheck.sh <G> ~/lean/classical-lean-paper-crypto`).
  Also, not a gate: confirm `.github/workflows/ci.yml`'s sha256 is
  `0d7508432a867a9f44caca6b498e9d33b0b42230a73f240c74734070ff00283e`, the file whose runs
  CLOUD-1-CI-result.md records. A gate that fails is a stop: report it; 4b and 4c do not run.
- **4b. The bridge search:** `tools/bridge_search.py --diff records/bridges/LEAN-29/` under the cap,
  at G, only after 4a passed; rc 1 means candidates to review. Report NEW and GONE keys, pairs and
  shapes. Check each NEW import-unrelated pair and each NEW shape by hand for a theorem whose proof
  needs both sides; a real one gets an item number from 157 on and is appended to
  `MATH-PLAN-library-2-bridges-2.md` through `ds_patch_staging` (its current sha256 as
  `expect_sha256`), in the file's section 7 columns. Say for each whether it is load-bearing for a
  scheduled row (items 96 to 110). Write the new baseline to `records/bridges/MERGE-1/`; its commit
  touches only `records/`.
- **4c. The report tool**, under the cap, at G: a report, not a gate. List every `CLOSES` line that
  names a theorem of the five modules; none is expected for a main theorem.
- **4d. check_records again at the final HEAD**, after every records-only commit, predicted PASS 128.
- **4e. Report** `lean/MERGE-1-report.md` through ds_write_staging, laid out like LEAN-29's: in
  short; setup; the merge and its conflict resolution (the three diffs); the lane copies; documents;
  G's hash; predicted beside measured for every gate and count; the bridge diff and baseline;
  4c's `CLOSES` lines that name a theorem of the five modules (or "none");
  commits; misses; the push command as one line, not run:
  `cd ~/lean/classical-lean-paper-crypto && git push origin merge-1:master && git push github merge-1:master`.
  Say in the report that the GitHub push starts the first CI run on `master`.
- **4f. Push-review file** `lean/MERGE-1-push-review.txt` through ds_write_staging, by one script,
  each command followed by its full output: `git rev-parse HEAD`, `git status --porcelain`,
  `git ls-remote origin master`, `git ls-remote github master`,
  `git merge-base --is-ancestor 92a314c HEAD` with its exit code,
  `git merge-base --is-ancestor d7756afae16c6e00424589d8a020315f24eb95be HEAD` with its exit code,
  `git rev-list --count 92a314c..HEAD`, `git log --name-status --format='== %h %cI %s' 92a314c..HEAD`
  (files under `records/bridges/` as counts only), `git diff 92a314c HEAD -- ClassicalLean.lean
  records/CLAIMS.md records/orders/INDEX.md`, `git diff --name-only <G> HEAD` (only `records/`),
  and 4d's check_records output. Report its sha256. Then stop. claude-ai reviews it before Dustin
  pushes.

## Done means

- Branch `merge-1` from `92a314c`, clean tree, nothing pushed; its first commit is the records
  commit; then the merge (conflicts resolved by rule 2, only added lines in the three files); then
  the `incoming/` removal; then documents; then records-only commits.
- The three lane copies of `incoming/` exist with hashes equal to yours and to the originals.
- Every gate as predicted on the merged tree at G, or each miss reported; gate 7 ALL PASSED at G;
  after G only `records/` changed, and check_records passes at the final HEAD.
- The bridge diff reported, real bridges (if any) appended from row 157, the new baseline committed.
- Job 3's documents changed and named.
- 4c's report-tool run reported, with its `CLOSES` lines for the five modules.
- The report and push-review file in `lean/`, hashes matching yours.

Then report in a few plain sentences: what merged, the gate results beside the predictions, any
new bridge, the two files' hashes and the push command. Dustin reads your replies carefully and is
still learning to read code: plain words, and define a technical term the first time you use it.
When you need a decision from him, ask in one line with your recommended answer first.

## Not in this order

- Any change to a `.lean` file beyond rule 2's import lines in `ClassicalLean.lean`, or to `tools/` or `.github/` (what the merge brings in excepted).
- Deleting the GitHub branches `cloud-ci` and `cloud-math-1` (Dustin's call, later).
- Items 96 to 110 (LEAN-30 to LEAN-32) and the second cloud batch (items 147, 150 to 153).

## Revisions

- r1, cold review 1 (fresh subagent): 0 BLOCKER, 3 MAJOR, 9 MINOR; all applied. The gates now run
  first (4a) at a named commit G, and bridge rows reach the lane only after they pass; check_records
  runs again at the final HEAD and its output goes in the push-review file; every lane file has its
  full path. Measured for the minors: the merge base is 20303cd; LEAN-29's changed modules are not
  in the cloud modules' import closure; remote `github` has the default fetch refspec; rounds 59 and
  60 are taken, so this is 61; check_records does not check that a named path exists. Also: each
  prediction's source named; the scope's `.lean` wording; G named for gate 7; the evidence folder
  made before the first run; byte lengths in the reviews file; "28 GB of memory uncapped"; the
  cloud tip's ancestry and `git diff --name-only G HEAD` in the push-review file.
- r2, confirming pass (fresh subagent, 4 calls): all r1 fixes present, 0 BLOCKER, 0 MAJOR, 3 MINOR, applied: "Not in this order" now matches the scope; the lane-path line covers the plan path too; 4c's CLOSES lines have a place in the report and in Done-means. The header's measurement window widened to 11:20 EDT, when the r1 facts were measured.
