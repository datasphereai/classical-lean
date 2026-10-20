# MERGE-2 order: the five CLOUD-MATH-2 modules into master, with gate 7

For a plain Claude Code session on DSMain, as dustin, in tmux `cc`. Written by claude-ai on
2026-10-20. Plan: lean/CLOUD-LANDING-PLAN-1.md (the shape) and lean/CLOUD-LANDING-PLAN-2.md (the
money re-plan). Cold-reviewed twice by one fresh subagent: pass 1 FAIL (2 BLOCKER, 4 MAJOR, 11 MINOR, all applied); pass 2 PASS WITH FINDINGS (every pass-1 finding fixed, 0 BLOCKER, 0 MAJOR, 7 new MINOR, all applied; not re-reviewed). See Revisions.

## What is already true (measured by claude-ai on 2026-10-20, from 17:31 to 18:40 EDT, on DSMain over ssh from helios)

- `master` on both remotes (`/data/git/classical-lean.git` and GitHub) is
  `9c0639c5878d09db83b1334ec35b705add9a8cb7`, RULES-1's last commit (`git ls-remote`).
- GitHub branch `cloud-math-2` = `284dd5f3defb4e4326c24e20c81ebc1786a0b156`: order CLOUD-MATH-2
  (lane `lean/CLOUD-MATH-2-order.md`, 76aad8c5), eight commits on `4d99afd`, which is `9c0639c` plus
  claude-ai's one commit adding `incoming/` (its message has no `Evidence:` line). Five new
  modules `ClassicalLean/Analysis/PowerMethod.lean`, `ClassicalLean/Algebra/Pseudoinverse.lean`,
  `ClassicalLean/Probability/ChiSquared.lean`, `ClassicalLean/Analysis/KKT.lean`,
  `ClassicalLean/InformationTheory/Huffman.lean` (items 147, 150, 151, 152, 153 of
  MATH-PLAN-library-2), their five import lines, records (order copy, INDEX row, CLAIMS row, round
  66; and RULES-1's push added to RULES-1's INDEX and CLAIMS rows, records/README.md rule 2, so that
  is done), and `incoming/`: 619 files at the tip (`git ls-tree -r --name-only 284dd5f incoming`):
  REPORT.md, PREDICTIONS.md, README.md, `reviews/` 11, `tools/` 14, `evidence/` 591; 5.9 MB.
  `git show 284dd5f:incoming/tools/SHA256SUMS | sha256sum` is `0d9c12ff1c9a33ba2c07fb96d5934185ed12e8d648b13931bd8ea6848412b422`.
  CI on its last commit, run 39497980258: green, every step. claude-ai's check of it, gates rerun
  on DSMain in its own clone, every value as predicted: lane `lean/CLOUD-MATH-2-result.md` (4921c2ed).
- At the cloud tip, measured by claude-ai on DSMain: `lake build` 4188 jobs, 0 warnings; AxiomGate
  PASS 3458; check_sorry PASS 135; VacuityGate PASS, 1 reviewed helper, 0 VACUOUS-PENDING;
  check_records PASS 135 (96 records files searched); `compile_rules.py drift` PASS;
  `banned_vocab_scan.py ClassicalLean` PASS, 135 files and `ClassicalLean.lean`, 0 hits.
- Two trial merges in claude-ai's scratch clone (nothing pushed; git 2.43.0):
  (a) `git merge --no-ff github/cloud-math-2` on a branch at `9c0639c`: rc 0, no conflict;
  `git diff --name-only 9c0639c HEAD` outside `incoming/` lists exactly `ClassicalLean.lean`, the
  five modules, `records/CLAIMS.md`, `records/orders/INDEX.md`, the CLOUD-MATH-2 order copy and
  round 66's fragment.
  (b) the same after a stand-in records-first commit that appends one row to the bottom of
  `records/orders/INDEX.md` and one to `records/CLAIMS.md` (as this order's Setup step 4 does):
  `git merge --no-ff --no-commit` rc 1, CONFLICT in exactly `records/CLAIMS.md` and
  `records/orders/INDEX.md`, one hunk each. In each hunk, ours is RULES-1's old row and the
  stand-in row; theirs is RULES-1's row with its push and CLOUD-MATH-2's row. Nothing else
  conflicted. This is the case this order meets.
- The 11 review files are valid UTF-8 (`iconv`).
- The worktree `~/lean/classical-lean-paper-crypto` is on branch `rules-1` at `9c0639c`, clean
  (`git status --porcelain` empty). Its remotes: `origin` the bare repo, `github` GitHub. No branch
  `merge-2` exists. The main clone `~/lean/classical-lean` (the nightly's) is on `master` at
  `9c0639c`.
- At `9c0639c`: round 65 is RULES-1's, and round 66 (on the branch) CLOUD-MATH-2's, so this order's
  round is 67; the latest bridge baseline is `records/bridges/LEAN-32/` (COMMIT, pairs.tsv,
  shapes.tsv); `tools/vacuity_reviewed.txt` holds 1 entry; HANDOFF.md section 1's last dated
  paragraph is LEAN-32's (line 318); ROADMAP.md's last section is 1.24 (LEAN-32, line 721);
  HANDOFF.md section 6's dated MERGE-1 line about cloud sessions (line 1047) names "orders CLOUD-1
  and CLOUD-MATH-1".
- The lane: the bridges file is now `lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md`
  (sha256 f8363b7ab545fddf7d9f37240ed311687d5914e601e9daf7470865ce11216b4f; it moved there in the
  lane's layout move); its last row is 159, so new rows start at 160. No folder
  `lean/CLOUD-MATH-2/` exists, so this order's lane copies are flat files under `lean/`, as
  MERGE-1's were.
- Timers and cron on DSMain, read 2026-10-20 (`systemctl --user list-timers`, `crontab -l`):
  memory-index at midnight; restic nightly, ds-hygiene, the daily verify, lean-nightly and the
  backup bundle between 2 and 4 in the morning; the store sync before 6; w29-tracker and
  w29-sysmap every few minutes (they load no Lean).
- `~/lean/lean32-checks/scripts/` holds LEAN-32's helpers (sha256): `ev.sh`
  `ee1d209eaaef0a743b79cd7cc44561e266e74cd6702bd3b943d7f218d9d10efc`, `hl.sh`
  `09a418f2c2593450a22497c64753e81e4542574fa00deb3b8b2f267193564054`, `rootrun.sh`
  `4d739a45d5a49d1c041dd0f239264ddbab15dfd5c3b431c24706da90dae10131`, `evcite.py`
  `11565ca5adc96a067c3b9110a3c2cd0c5cb87a86c90958dc1f59b2140745eedf`, `citecheck.py`
  `7e3e38f7dd8b2ce97b3da5250feac31be410a99f840272324b18b021503bc366`.
  `ev.sh`, `hl.sh` and `rootrun.sh` each name `D=/home/dustin/lean/lean32-checks` on one line;
  `ev.sh` and `rootrun.sh` also name the worktree `~/lean/classical-lean-paper-crypto`, the same
  worktree this order uses. `evcite.py` names the path twice, in its docstring and in its `LOG = `
  default; `citecheck.py` names no path (it takes the log as an argument).
- How LEAN-32 ran its gates and tools (its `~/lean/lean32-checks/evidence.log`): build, AxiomGate,
  VacuityGate and the vacuity tests through `ev.sh --cap … nice -n 19 …` (labels `g1-build`,
  `g2-axiom`, `g3-vacuity`, `g3-tests`); check_sorry and check_records through plain `ev.sh`; gate 7
  as `ev.sh --cap g7 … ~/lean/recheck/run-recheck.sh <G> ~/lean/classical-lean-paper-crypto`; the
  bridge search and the report tool through `rootrun.sh` (labels `bridges`, `report-after`); the
  banned scan as `python3 -I tools/banned_vocab_scan.py ClassicalLean`; each commit through `ev.sh`
  as `git commit -F <message file>` with a label starting `commit-`, then a `COMMIT <hash>` line.
  LEAN-32's vacuity tests gave 89 verdicts, 47 flagged, 3 UNCHECKED as expected, 0 mismatches;
  its report tool's output is `~/lean/lean32-checks/report-after.out`. RULES-1 changed, under
  `tools/`, only `build_registry.py`, `compile_rules.py` and their two tests
  (`git diff --name-only a6d5c0f 9c0639c -- tools`), so `bridge_search.py` and
  `UninformativeReport.lean` are LEAN-32's. The repository's only lakefile is `lakefile.toml`
  (`git ls-tree --name-only 9c0639c`). None of `lean/CLOUD-MATH-2-REPORT.md`,
  `lean/CLOUD-MATH-2-PREDICTIONS.md`, `lean/CLOUD-MATH-2-reviews.md`, `lean/MERGE-2-report.md`
  exists in the lane (`ds_hash`).

## Goal

`master` gains the five CLOUD-MATH-2 modules, every gate passing on the merged tree, gate 7
included, the banned-vocabulary scan run, the bridge search and the report tool run, the cloud
session's report, predictions and reviews copied to the lane, `incoming/` out of the tree (its
evidence and toolkit kept in git history), and the documents saying what changed. Dustin pushes
after claude-ai checks the push-review file.

## Scope

- **Branch.** `merge-2` from `9c0639c` in `~/lean/classical-lean-paper-crypto`, made after Dustin
  approves your plan. Nothing pushed. No sudo.
- **You may change in the repository:** `records/CLAIMS.md` and `records/orders/INDEX.md` by rule 2
  only, and the rest of `records/`; `incoming/` (removed, after its copy to the lane); `HANDOFF.md`
  and `ROADMAP.md` (job 3). What the merge itself brings in is not a change by you.
- **You may write in the lane:** `lean/MERGE-2-PLAN.md` (then -PLAN-2, never overwriting), the three
  copies of job 2, rows from 160 in the bridges file (job 4b), `lean/MERGE-2-report.md` and
  `lean/MERGE-2-push-review.txt`. Nothing else in the lane.
- **You may not change** any `.lean` file, anything under `tools/`, `.github/` or
  `records/rules.toml`. A gate failing on the merged tree is a stop: report it, change nothing to
  make it pass.
- **Off limits:** the main clone `~/lean/classical-lean` and its `master`; `~/break-it-5`;
  `~/trading`; `~/lean/recheck` (`run-recheck.sh` is run, as gate 7, not edited); Dustin's
  `~/.config/classical-lean/banned-terms` (the scanner reads it; you never print or copy it); the
  GitHub branches (no push, no delete); `/tmp/claude-ai-cm2/` (claude-ai's scratch).
- **The night window and the memory cap,** as LEAN-32's `ev.sh` enforces them: the window is the
  one in that script's header, which this order adopts unchanged (rule 36: name the window, do not
  copy its times). Start gate 7 only when it can finish before the midnight timer (it took about 21
  minutes in MERGE-1). Every whole-library run under `ev.sh --cap` or `rootrun.sh` (each puts its runs in the 12 GB
  scope); never two Lean
  runs at once; read `crontab -l` and `systemctl --user list-timers` before you start; `~/.elan/bin`
  on `PATH`.

## Check, then read

All lane paths are under `/opt/datasphere/lane/inbox/threads/staging/` (ds_* tools: root `lane`,
path `inbox/threads/staging/…`). Check these sha256s first; if any differs, stop and say which:
- this order, `lean/MERGE-2-order.md`: the value in Dustin's prompt;
- `lean/CLOUD-MATH-2-order.md` `76aad8c5ec6db0465247446b55fad48e86d925406f96f327d41b63425a3fd53f`;
- `lean/CLOUD-MATH-2-result.md` `4921c2eda9f2f698de0f39e64745b493abfd7ba21d6ad6f9348dd39f89497b59`;
- `lean/MERGE-1-order.md` `062c0fa0e085085cfc5752a2c03ef7e7f210c0cefaeb6286d234bb79165f5af2` (the
  pattern this order follows);
- `lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md`
  `f8363b7ab545fddf7d9f37240ed311687d5914e601e9daf7470865ce11216b4f`.
Then read them; in the repository `records/README.md` and `HANDOFF.md` sections 1, 4 and 6 (all 21
rules); on branch `cloud-math-2`, `incoming/REPORT.md`; and LEAN-32's `evidence.log` lines for the
labels named above.

## Rules

1. **Nothing is re-proved or edited in a module.** The five modules arrive as the cloud session
   left them. This order merges, measures and documents.
2. **The merge and its two conflicts.** `git merge --no-ff --no-commit github/cloud-math-2` after
   the records-first commit. Expected, as measured in trial (b): CONFLICT in exactly
   `records/CLAIMS.md` and `records/orders/INDEX.md`, one hunk each. Resolve both by one script, run as `ev.sh --nolean resolve …` (a script file in the evidence
   folder, bash where it needs `<(…)`): take the branch's version of the file (`git show 284dd5f:<file>`) and append this order's own
   MERGE-2 row from the records-first commit after it. So RULES-1's row keeps the push the branch
   added, CLOUD-MATH-2's row follows, and MERGE-2's row is last. Check by a second script, `ev.sh --nolean resolve-check …`, that
   `diff <(git show 284dd5f:<file>) <file>` shows only the MERGE-2 row added at the end. Any other
   conflict, or any other difference, is a stop. RULES-1's push is already recorded on the branch
   (records/README.md rule 2), so the records-first commit does not touch RULES-1's rows.
3. **HANDOFF section 6's rules** apply as for any DSMain order. The ones this order acts on: 17
   (every output saved with its sha256), 18 (records follow the clock), 22 (quotes in round 67's
   fragment checked by script, with a planted misquote), 23 (every evidence command through
   `ev.sh`, which refuses without a prediction; refusals logged `NOT RUN`), 36 (dated clock times),
   38 (`rootrun.sh` for the bridge search and the report tool), 39 (commits staged by path,
   messages written after their gates, each ending with the `Evidence:` line `evcite.py` writes,
   `citecheck.py` at the end). Rules 12 and 26 apply if you start any subagent. Rules 14, 20, 27
   (but see rule 4), 31 and 37 have nothing to act on: no `.lean` file changes here, and no
   declaration is drafted here. The five modules' declarations were reviewed cold by CLOUD-MATH-2:
   11 reviews, in `incoming/reviews/`.
4. **Predicted by claude-ai before this order was written**, from the cloud tip's measured gates;
   the merge adds no `.lean` change beyond the cloud tip's, which 4g measures. The merged tree
   builds `4188` jobs with 0 warnings. AxiomGate PASS `3458`. check_sorry PASS `135`. check_records
   PASS `135`. VacuityGate PASS with 1 reviewed helper, no new flag, no UNCHECKED, 0 VACUOUS-PENDING;
   its tests 89 verdicts, 47 flagged, 3 UNCHECKED as expected, 0 mismatches. `compile_rules.py
   drift` PASS. `banned_vocab_scan.py ClassicalLean` PASS, 135 files and the root file, 0 hits.
   Gate 7 ALL PASSED: 4188 jobs, 135 modules 0 failed, 3458, the three standard axioms, the planted
   fault named. Check them, and add your own in a prediction file before any run: the bridge
   search's and the report tool's numbers, by hand from LEAN-32's runs (say they are hand
   predictions, as MERGE-1's were), and the records-file count.
5. **Predict, then measure,** as LEAN-32 did: an evidence folder `~/lean/merge2-checks/` with
   `evidence.log`; every prediction file hashed into the log (`hl.sh`) before its run; hashes in
   records and the report by script, never typed. Git, hash and resolve commands, which load no
   Lean, run as `ev.sh --nolean …`, so the night window does not refuse them. Every commit runs
   through `ev.sh --nolean` as `git commit -F <message file>`, with a label starting `commit-`;
   after it you append the line `COMMIT <hash>` to `evidence.log`. Between the `evcite.py` run that
   writes a message's `Evidence:` line and that commit's `COMMIT` line, the only evidence line is
   the `commit-…` line (citecheck reports any other).
6. **The merged tree is the one that counts.** Every gate runs on the clean tree of the last commit
   that touches anything outside `records/` (the commit that closes job 3; call it G and record its
   hash). Later commits touch only `records/`, and check_records runs again at the final HEAD.

## Setup (after approval)

1. The helpers first. Make `~/lean/merge2-checks/scripts/`, check the five files' hashes above, and
   copy them with one script that changes only:
   - in `ev.sh`, `hl.sh` and `rootrun.sh`, the one line `D=/home/dustin/lean/lean32-checks` to
     `D=/home/dustin/lean/merge2-checks`, refusing unless each file has exactly one such line;
   - in `evcite.py`, only the one line beginning `LOG = `, its default path to
     `/home/dustin/lean/merge2-checks/evidence.log` (the docstring stays; refuse unless exactly one
     such line);
   - `citecheck.py` byte for byte (its sha256 must stay the full value above).
   The script compares all 64 characters of each source hash first and refuses on any difference.
   The script then logs the five new sha256s with `hl.sh`. Then write `pred-setup.md` (the
   predictions for steps 2 and 3) and hash it with `hl.sh` before step 2's first run.
2. Test the helpers before first use (rules 23, 38, 39), each logged and predicted:
   - `ev.sh` with an empty prediction is refused, exit 97, and logs `NOT RUN`.
   - `ROOTRUN_BUILD=false rootrun.sh t-rootrun-false "<pred>" touch ~/lean/merge2-checks/ran`: exit
     95, logged `NOT RUN`, and the file `ran` does not appear.
   - before the real-build test, `ev.sh --nolean pre-real "<pred>" bash -c 'git status --porcelain; git rev-parse HEAD'`
     (predicted: no status line, and `9c0639c5878d09db83b1334ec35b705add9a8cb7`); a dirty tree or
     another head is a stop. Then `rootrun.sh t-rootrun-real "<pred>" true`, with the real root
     build at `9c0639c`, outside the night window: the `t-rootrun-real-build` line comes before the `t-rootrun-real`
     line in `evidence.log`, and both carry the same head.
   - citecheck on a scratch copy of `evidence.log`, in this order: append two planted lines in the
     log's format with labels `p-one` and `p-two`; run `evcite.py <copy>` and save its line; append
     `COMMIT ffffff0`; then `citecheck.py <copy> --message <file> ffffff0` with a message ending in
     that line prints `OK ffffff0`, exit 0, and with the same line minus `, p-two` prints exactly
     `DIFF ffffff0: label left out: p-two`, exit 1. The real log is not touched.
3. Then the remaining repository checks, through `ev.sh --nolean setup1 …`: `git fetch origin && git fetch
   github cloud-math-2` in the worktree; `origin/master` and `git ls-remote github master` both
   `9c0639c…`; `github/cloud-math-2` `284dd5f…`; `git merge-base --is-ancestor 9c0639c
   github/cloud-math-2` exit 0; `git status --porcelain` empty. If not, stop.
4. Write the prediction file for every later run (rule 4), hash it, then
   `git switch -c merge-2 9c0639c`.
5. **Records first**, one commit, no `.lean` file: this order's copy as
   `records/orders/<UTC>__claude-ai__order-merge2-cloud-math-2.md`; its INDEX row (`| MERGE-2 |`)
   at the bottom; a CLAIMS row at the bottom; round 67's fragment
   `records/rounds/<UTC>__round-67-merge-cloud-math-2.md`, naming the five module paths in full
   (round 66 names them too) and saying the round lands order CLOUD-MATH-2. Do not touch RULES-1's
   rows (rule 2). check_records then: PASS 130 (the five modules are not in this tree yet).

## The work

### Job 1: the merge

`git merge --no-ff --no-commit github/cloud-math-2`, through `ev.sh --nolean` (predicted rc 1, the two
conflicts of rule 2). Resolve by rule 2's script and stage the two files by path. Then, before
committing: `ev.sh --nolean name-status "<pred>" git diff --cached --name-status 9c0639c` lists
only the five new modules, `ClassicalLean.lean`, `incoming/…` and `records/…` (incoming/ as a
count, 619). Then write the message to a file: "Merge order CLOUD-MATH-2 (items 147, 150, 151,
152, 153) into master (order MERGE-2)", the two conflicts and their resolution, and its
`Evidence:` line, generated last. Commit with `ev.sh --nolean commit-merge … git commit -F <file>`, then
append `COMMIT <hash>`.

### Job 2: the cloud session's report, predictions and reviews to the lane, then incoming/ out of the tree

Copy through `ds_write_staging`, each post_sha256 compared with your own sha256sum; if a target
path already exists in the lane, stop and report (never overwrite). A large file
may go up in pieces, with the running sha256 checked after each, as MERGE-1 did.
`incoming/REPORT.md` to `lean/CLOUD-MATH-2-REPORT.md`; `incoming/PREDICTIONS.md` to
`lean/CLOUD-MATH-2-PREDICTIONS.md`; the 11 files of `incoming/reviews/` into one file
`lean/CLOUD-MATH-2-reviews.md`, each under a heading line giving its path, its byte length and its
sha256, then its bytes unchanged (build it by script; split it back by the lengths and check every
part hashes to its original). `incoming/README.md`, `incoming/tools/` and `incoming/evidence/`
are not copied: they stay in git history, reachable from master through the merge's second parent
`284dd5f` once pushed (`git show 284dd5f:incoming/README.md`; `git archive 284dd5f incoming/tools`;
`incoming/tools/SHA256SUMS` hashes to 0d9c12ff…, the toolkit a later cloud order may reuse). Then
`git rm -r incoming` through `ev.sh --nolean` in its own commit; its message names the three lane files and their hashes
and gives those two commands and that hash.

### Job 3: documents

- `HANDOFF.md` section 1: after LEAN-32's paragraph, a dated paragraph for order CLOUD-MATH-2
  (round 66) and its merge by MERGE-2 (round 67), in MERGE-1's form: the five modules by name and
  item, one line each; that the cloud session's report, predictions and reviews went to the lane
  and `incoming/` left the tree, its toolkit and evidence in history at `284dd5f` (the two commands
  of job 2); the counts predicted by rule 4, to be re-measured by this order's gates on the clean
  tree: **135 modules, 3458 theorem constants (3379 + 79, round 66's censuses), `lake build` 4188
  jobs, 0 warnings**.
- `HANDOFF.md` section 6: **no change at all.** `tools/compile_rules.py drift` checks not only the
  generated block between `<!-- rules:begin` and `<!-- rules:end -->` but also section 6's text
  outside it, against `meta.outside_sha256` in `records/rules.toml`
  (`f39a512b6b1d3a56f15d03c8e420584993d1ef0b38700aae3bedc909e78c9fac`), so any edit anywhere in
  section 6 fails the drift gate and CI's Rules gate unless the registry changes, which this order
  may not do. The dated MERGE-1 line there already states the rule for every `cloud-*` branch;
  CLOUD-MATH-2's own push of its branch is recorded in section 1's paragraph above.
- `ROADMAP.md`: after section 1.24, a section 1.25 for items 147, 150, 151, 152 and 153, landed from
  below the plan's cut by order CLOUD-MATH-2 in a cloud session and merged by MERGE-2, in section
  1.21's form.

### Job 4: the end checks, in this order

Commit jobs 1 to 3; the last of those commits is G (rule 6). The gates run first, before anything
else loads the library.

- **4a. The gates**, on the clean tree at G, each through `ev.sh` with its prediction (rule 4), in
  LEAN-32's forms: `ev.sh --cap g1-build … nice -n 19 lake build`; `ev.sh --cap g2-axiom … nice -n 19
  lake env lean tools/AxiomGate.lean`; `ev.sh --cap g3-vacuity … nice -n 19 lake env lean
  tools/VacuityGate.lean`; `ev.sh --cap g3-tests … nice -n 19 python3 -I tools/run_vacuity_tests.py`;
  `ev.sh g4-sorry … python3 -I tools/check_sorry.py`; `ev.sh g5-records … python3 -I
  tools/check_records.py`; `ev.sh g6-drift … python3 tools/compile_rules.py drift records/rules.toml
  HANDOFF.md`; `ev.sh g6-banned … python3 -I tools/banned_vocab_scan.py ClassicalLean`; and gate 7,
  `ev.sh --cap g7 … ~/lean/recheck/run-recheck.sh <G> ~/lean/classical-lean-paper-crypto`. A gate
  that fails is a stop: report it; 4b and 4c do not run.
- **4b. The bridge search,** through `rootrun.sh` (rule 38), at G, only after 4a passed:
  `rootrun.sh bridges … python3 -I tools/bridge_search.py --diff records/bridges/LEAN-32/ --out ~/lean/merge2-checks/bridges/MERGE-2`;
  rc 1 means candidates to review. Report NEW and GONE keys, pairs and shapes. Check each NEW
  import-unrelated pair and each NEW shape by hand for a theorem whose proof needs both sides; a
  real one gets an item number from 160 on and is appended to
  `lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md` through `ds_patch_staging` (its
  sha256 above as `expect_sha256`), in the file's columns. Write the new baseline to
  `records/bridges/MERGE-2/`; its commit touches only `records/`.
- **4c. The report tool,** through `rootrun.sh`, at G, once: `rootrun.sh report … nice -n 19 lake env
  lean tools/UninformativeReport.lean`; a report, not a gate. Predict its counts from
  `~/lean/lean32-checks/report-after.out` (RULES-1 changed no `.lean` file, so only the five modules
  can add to them). List every `CLOSES` line that names a theorem of the five modules; none is
  expected for a main theorem.
- **4d. check_records again at the final HEAD**, after every records-only commit, predicted PASS 135.
- **4e. citecheck**, two runs, both through `ev.sh`:
  - this order's own commits, `git rev-list --first-parent 9c0639c..HEAD`, each by
    `citecheck.py ~/lean/merge2-checks/evidence.log --message <its message file> <hash>`
    (`git log -1 --format=%B <hash>` to a file), by one loop: every one `OK`, rc 0;
  - the repository run `citecheck.py ~/lean/merge2-checks/evidence.log ~/lean/classical-lean-paper-crypto 9c0639c`,
    for the record. Predicted rc 1: this order's own commits `OK`; the 8 CLOUD-MATH-2 commits each a
    line beginning `DIFF <hash>: no COMMIT marker for <hash> in the log` (label differences may
    follow on the same line, since their ranges are compared against this log; their `Evidence:` lines cite the cloud
    session's log, checked by its End check 2 and, for 284dd5f, by claude-ai:
    lean/CLOUD-MATH-2-result.md); `4d99afd` `NO-EVIDENCE` (claude-ai's incoming/ commit, which has
    no `Evidence:` line and was checked by no one's citecheck; its content is checked by
    lean/CLOUD-MATH-2-order.md's rests-on lines).
- **4f. Report** `lean/MERGE-2-report.md` through ds_write_staging, laid out like MERGE-1's: in
  short; setup and the helper tests; the merge and its two resolved conflicts (the two diffs);
  the lane copies; documents; G's hash; predicted beside measured for every gate and count; the
  bridge diff and baseline; 4c's `CLOSES` lines that name a theorem of the five modules (or "none");
  commits; 4e's output; misses; the push command as one line, not run:
  `cd ~/lean/classical-lean-paper-crypto && git push origin merge-2:master && git push github merge-2:master`.
  Say in the report that the GitHub push starts a CI run on `master`.
- **4g. Push-review file** `lean/MERGE-2-push-review.txt` through ds_write_staging, by one script,
  each command followed by its full output: `git rev-parse HEAD`, `git status --porcelain`,
  `git ls-remote origin master`, `git ls-remote github master`,
  `git merge-base --is-ancestor 9c0639c HEAD` with its exit code,
  `git merge-base --is-ancestor 284dd5f3defb4e4326c24e20c81ebc1786a0b156 HEAD` with its exit code,
  the merge commit's `git log -1 --format='%H %P'`,
  `git rev-list --count 9c0639c..HEAD` (predicted: this order's own commits plus 9),
  `git log --first-parent --name-status --format='== %h %cI %s' 9c0639c..HEAD` (files under
  `incoming/` and `records/bridges/` as counts only),
  `git diff 9c0639c HEAD -- ClassicalLean.lean records/CLAIMS.md records/orders/INDEX.md`,
  `git diff --name-only 284dd5f <G> -- ClassicalLean ClassicalLean.lean tools .github ':(glob)lakefile*' lake-manifest.json lean-toolchain`
  (predicted empty), `git ls-tree --name-only <G> | grep -c '^lakefile'` (predicted 1), `git diff --name-only <G> HEAD` (only `records/`), 4d's check_records output
  and 4e's two outputs. Report its sha256. Then stop. claude-ai reviews it before Dustin pushes.

## Done means

- Branch `merge-2` from `9c0639c`, clean tree, nothing pushed; its first commit is the records
  commit; then the merge (its two conflicts resolved by rule 2); then the `incoming/` removal; then
  documents; then records-only commits.
- The helpers copied, their five sha256s logged, and their four tests logged before first use.
- The three lane copies exist with hashes equal to yours and to the originals.
- Every gate as predicted on the merged tree at G, or each miss reported; gate 7 ALL PASSED at G;
  after G only `records/` changed, and check_records passes at the final HEAD.
- The bridge diff reported, real bridges (if any) appended from row 160, the new baseline committed.
- Job 3's documents changed and named (section 1 and ROADMAP only; section 6 untouched); the
  drift check passes.
- 4c's report-tool run reported, with its `CLOSES` lines for the five modules.
- 4e's two outputs in the report; every commit of this order `OK`.
- The report and push-review file in `lean/`, hashes matching yours.

Then report in a few plain sentences: what merged, the gate results beside the predictions, any
new bridge, the two files' hashes and the push command. Dustin reads your replies carefully and is
still learning to read code: plain words, and define a technical term the first time you use it.
When you need a decision from him, ask in one line with your recommended answer first.

## Not in this order

- Any change to a `.lean` file, to `tools/`, `.github/` or `records/rules.toml`.
- Deleting the GitHub branches `cloud-ci`, `cloud-math-1` and `cloud-math-2` (Dustin's call, later).
- CLOUD-MATH-3 and LEAN-33 to LEAN-37 (lean/CLOUD-LANDING-PLAN-2.md).

## Revisions

- r1, cold review pass 1 (fresh subagent, read list in /tmp/claude-ai-cm2/review2/ on helios and four lane files, 13 calls, read-only): FAIL, 2 BLOCKER, 4 MAJOR, 11 MINOR, all applied.
  - BLOCKER: the merge conflicts after the records-first commit (claude-ai's first trial merge had no records-first commit, so it missed this; re-measured as trial (b): exactly `records/CLAIMS.md` and `records/orders/INDEX.md`, one hunk each); rule 2 now resolves them by script, checked against the branch's files. The helper-copy script would have refused `evcite.py` (no `D=` line) and `citecheck.py` (no path at all); the copy rules are now per file.
  - MAJOR: the merge runs with `--no-commit`, so its message is written after its checks (rule 39); citecheck is two runs, own commits by `--message` (all OK) and the repository run predicted rc 1 with the 8 cloud commits and `4d99afd` named; rule 38's real-build test added; the push-review file gains the three-file diff, the merge's parents and a predicted-empty diff of the `.lean`, tools, CI and lake paths.
  - MINOR: helpers set up before the setup checks; the citecheck test on a scratch log copy; the incoming/ inventory corrected (evidence has 591 files, not 436: claude-ai had counted one level); how to get the toolkit and evidence back from history; flat lane names (no CLOUD-MATH-2 folder); LEAN-32's exact gate forms; one report-tool run; rule 31's wording; incoming/ as counts in the push review; the lane writes in Scope; bridge and report predictions labelled hand predictions; gate 7 not started where it would run into the midnight timer.
- r2, cold review pass 2 (the same reviewer, 2 calls): every pass-1 finding FIXED (M4 and one minor with small residues), 0 BLOCKER, 0 MAJOR, 7 new MINOR, all applied: a prediction file for the setup runs; the tree checked clean just before the real-build rootrun test; nothing logged between the `evcite.py` run and its commit's `COMMIT` line; the lakefile path as a glob, with the lakefile count (measured: only `lakefile.toml`); git, hash and resolve commands as `ev.sh --nolean`; the conflict resolution and its check run through the helper; full helper sha256s, and lane targets never overwritten (measured: none exists). Measured for the reviewer's open questions: RULES-1 changed neither `bridge_search.py` nor `UninformativeReport.lean`.
- r3, claude-ai, after pass 2, settling the item neither pass could check: `compile_rules.py drift` does read section 6 outside the generated block (it compares that text's sha256 with `meta.outside_sha256` in `records/rules.toml`, lines 286 to 304 and 473 of the tool), so job 3's planned section 6 line would have failed the drift gate and CI's Rules gate. The line is removed; section 6 is not touched (store row 20261020-001). The phrase "just before it" in Setup 2 now reads "before the real-build test".
- Not re-reviewed: the r2 and r3 edits.
