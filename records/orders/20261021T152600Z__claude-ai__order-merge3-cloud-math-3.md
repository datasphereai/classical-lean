# MERGE-3 order: the five CLOUD-MATH-3 modules into master, after LEAN-33, with gate 7

For a plain Claude Code session on DSMain, as dustin, in tmux `cc`. Written by claude-ai on
2026-10-20 and 2026-10-21 under lean/CLOUD-LANDING-PLAN-2.md ruling 3 ("the second to finish merges
after the first": LEAN-33 reached master first, so this order merges `cloud-math-3` onto it) and
lean/CLOUD-MATH-3-order.md's section "After the session". The shape is MERGE-2's
(lean/MERGE-2-order.md), which ran clean. Lane files named `lean/...` are under
/opt/datasphere/lane/inbox/threads/staging/lean/ (ds_* tools: root `lane`, path
`inbox/threads/staging/lean/...`). This order is `lean/MERGE-3/order.md`.

**New lane files go through `ds_file`** (project `lean`), and land at these paths only: your plan,
job `MERGE-3`, kind `plan` → `lean/MERGE-3/plan.md` (a second becomes `plan-r2.md`, never
overwriting); the report, job `MERGE-3`, kind `report` → `lean/MERGE-3/report.md`; the push-review
file, job `MERGE-3`, subdir `data`, name `MERGE-3-push-review.txt` →
`lean/MERGE-3/data/MERGE-3-push-review.txt`; job 2's three copies →
`lean/CLOUD-MATH-3/report.md`, `lean/CLOUD-MATH-3/data/PREDICTIONS.md` and
`lean/CLOUD-MATH-3/data/reviews.md`. Compare each reply's `post_sha256` with your own, and its `path`
with the one named here (a different path means the file existed: stop and report). **Appends go
through `ds_write_staging`** in mode `append`, each with `expect_sha256` the file's current sha256:
the later pieces of `reviews.md` (job 2), and at most one section of the bridges file (job 4b).
**Track the order's steps with the task tools** (lane `lean/NOTE-20261015-task-list-rule.md`).

Review: two cold passes by one fresh reviewer (a subagent of claude-ai's, reads only). Pass 1: PASS
WITH FINDINGS, 0 BLOCKER, 4 MAJOR, 12 MINOR, all fixed (r1). Pass 2: PASS WITH FINDINGS, 0 BLOCKER,
0 MAJOR, 10 MINOR, all fixed (r2). Both reports saved verbatim in the lane:
`lean/MERGE-3/data/rv1-pass1.txt` (`816bf62b5a81d945e67ddffd1a0be7f1738179c9ce4c74fa1683ff9a5be437fb`)
and `lean/MERGE-3/data/rv1-pass2.txt`
(`1ad7e2bdd5ae5855ca4ce930b9f8d65db65db68099da0a8db44bacd176a31a17`).

## What is already true (measured by claude-ai on DSMain over ssh from helios, from 2026-10-20 23:15 EDT into 2026-10-21; later facts carry their own dates)

- **Master.** Both remotes (`/data/git/classical-lean.git` and GitHub) are at
  `aba2d92ba76989f3afe9324cb3b8b3b126095089`, LEAN-33's last commit, pushed by Dustin (the bare
  repo's master ref written 2026-10-20 23:28:52 EDT; `git ls-remote` of both read 2026-10-20 23:29
  EDT). Its CI run 39538801023 (event push, branch `master`, head `aba2d92`): success, completed
  2026-10-21T03:47:34Z (`gh run view` on DSMain, read 2026-10-20 23:57 EDT). claude-ai's
  push review of LEAN-33 (store row 20261020-025): its gates rerun in a fresh clone at `aba2d92`,
  build 4188 jobs, 0 warnings, AxiomGate PASS 3468, check_sorry and check_records PASS 135 (100
  records files), VacuityGate PASS with 1 reviewed helper, drift PASS, banned scan PASS, 0 hits.
- **GitHub branch `cloud-math-3`** = `8c5fa226384c977b16301047f8a20ae306ea1ab6`: order CLOUD-MATH-3
  (lane `lean/CLOUD-MATH-3-order.md`, dfe8e5a9), eight commits on `313e9a7`, which is `04e4a38` plus
  claude-ai's one commit adding `incoming/` (its message has no `Evidence:` line). Against
  `04e4a38`, `git diff --name-only 04e4a38 8c5fa22 -- ClassicalLean ClassicalLean.lean` prints
  exactly:
  ```
  ClassicalLean.lean
  ClassicalLean/Analysis/SubgradientMethod.lean
  ClassicalLean/InformationTheory/ChannelCapacity.lean
  ClassicalLean/Probability/BernsteinInequality.lean
  ClassicalLean/Probability/EfronStein.lean
  ClassicalLean/Probability/OrderStatistics.lean
  ```
  (items 113, 130, 124, 121 and 126 of MATH-PLAN-library-2, in that order; `ClassicalLean.lean`
  gains exactly their five import lines, one hunk `@@ -141,0 +142,5 @@`). Also on the branch:
  records (the order's copy, INDEX and CLAIMS rows, round 68; and MERGE-2's push added to MERGE-2's
  INDEX and CLAIMS rows, records/README.md rule 2, so that is done), and `incoming/`: 614 files at
  the tip (REPORT.md, PREDICTIONS.md, README.md; `evidence/` 575, `reviews/` 8, `tools/` 14,
  `cm2-scripts/` 14). `git show 8c5fa22:incoming/tools/SHA256SUMS | sha256sum` is
  `7d5d50395635a37ff68376488fd68a823c603981bc0592abf746c16335169059`. CI on its last commit, run
  39533795172: success. No existing module, nothing under `tools/`, `.github/`, the lake files,
  HANDOFF.md, ROADMAP.md or records/rules.toml changes on the branch. claude-ai's check of it, gates
  rerun at the tip in its own clone, every value as predicted but one citecheck line: lane
  `lean/CLOUD-MATH-3/notes.md` (cc86957e).
- **The cloud session's last commit cannot be citechecked from the repository.** `8c5fa22`'s
  `Evidence:` line cites lines 882 to 922 of its log, but the log it committed in
  `incoming/evidence/evidence.log` has 914 lines (the copy into `incoming/` was one of that commit's
  own runs), so seven of its labels and its COMMIT marker exist only in the cloud container's log,
  now gone (store row 20261020-026). The other seven cloud commits citecheck `OK` against that log.
- **LEAN-33's seven changed modules**, which the branch does not have: `git diff --name-only 04e4a38
  aba2d92 -- ClassicalLean ClassicalLean.lean` prints exactly
  ```
  ClassicalLean/Algebra/Kantorovich.lean
  ClassicalLean/Analysis/ConvexConjugate.lean
  ClassicalLean/Analysis/ExponentialWeights.lean
  ClassicalLean/Analysis/GradientDescent.lean
  ClassicalLean/Probability/EffectiveSampleSize.lean
  ClassicalLean/Probability/GlivenkoCantelli.lean
  ClassicalLean/Probability/LikelihoodScore.lean
  ```
  So the merged tree's `.lean` files are the cloud tip's plus these seven: trial (b)'s tree below.
- **Trial merges in claude-ai's scratch clone** `/tmp/claude-ai-m3/trial` (nothing pushed; git
  2.43.0; `trial-m3.sh` 6de07b7e, output `trial-m3.out`
  `9d05ca0b15be46eb84fec2f0eb690d28e8c84f399a30c75f3d8ed1b94750dbd0`, every prediction of
  `pred-trial.txt` hit; that file was written before the run (`stat`: helios's copy last modified
  2026-10-20 23:30:43 EDT, DSMain's 2026-10-20 23:31:12 EDT; the run's first line
  2026-10-20T23:31:13-04:00), but its header's clock time was a guess, store row 20261020-027):
  (a) `git merge --no-ff --no-commit 8c5fa22` on a branch at `aba2d92`: rc 1, CONFLICT in exactly
  `records/CLAIMS.md` and `records/orders/INDEX.md`, one hunk each. Both sides add rows after
  MERGE-2's row, and `cloud-math-3` also edits MERGE-2's row with its push.
  (b) the same after a stand-in records-first commit (LEAN-33's INDEX and CLAIMS rows edited in place
  with a note, a MERGE-3 row appended at the bottom of each, a stand-in order copy and a stand-in
  round-70 fragment): rc 1, the same two files, one hunk each. Resolved by a script as rule 2 says
  (the branch's file, then the stand-in commit's last two lines). Measured diffs, branch file to
  result: `69a70,71` (INDEX) and `61a62,63` (CLAIMS), the two lines added at the end; stand-in file
  to result: `68c68,69` (INDEX) and `60c60,61` (CLAIMS), MERGE-2's row changed (its push) and
  CLOUD-MATH-3's row added after it, before LEAN-33's. Then `git diff --cached --name-status
  aba2d92` listed `ClassicalLean.lean`, the five modules, `incoming/` (614 files),
  `records/CLAIMS.md`, `records/orders/INDEX.md`, CLOUD-MATH-3's order copy and round 68, and the
  two stand-in files; nothing else. On the trial merge commit `e8511f4` (packages from claude-ai's
  clone at `04e4a38`): `lake build` 4193 jobs, 0 warnings; AxiomGate PASS 3527 (3468 + 59);
  check_sorry PASS 140; VacuityGate PASS, 1 reviewed helper, 0 VACUOUS-PENDING; check_records PASS
  140 (104 records files); `compile_rules.py drift` PASS; `banned_vocab_scan.py ClassicalLean` PASS,
  140 files and the root, 0 hits. This is the case this order meets.
  (c) the bridge search and the report tool at `e8511f4`, through a fresh root build (`trial-tools.sh`
  39ddbc40, predictions `pred-tools.txt` 4704ede0 hashed by the script's first line before any run;
  output `trial-tools.out` `ad71f1d6507b292b1193cf29709465967469e48442b3a9319ba3fbe23316edcf`, run
  2026-10-20 23:51:23 to 23:52:11 EDT): `bridge_search.py --diff records/bridges/LEAN-33/`: rc 1;
  "3029 pairs, 758 shape candidates, N = 139"; against LEAN-33's baseline 209 new pairs, 23 new
  shapes, 77 gone pairs, no gone shape; every NEW key names one of the five new modules and no GONE
  key does (the gone count was predicted 5 to 60, a miss: store row 20261020-028). The report tool:
  rc 0; written theorems 1961 (LEAN-33's 1925 + 36): A 1164 (OPEN 1120, DEPENDENT 44), B 797
  (CLOSES simp 15, CLOSES positivity 1, OPEN 781), C 36, 0 recursive; self-test 0 mismatches; no
  `CLOSES` line outside the self-test names a constant of the five modules. `git status --porcelain`
  empty after both.
- **The worktree** `~/lean/classical-lean-paper-crypto` is on branch `lean-33` at `aba2d92`, clean;
  remotes `origin` the bare repo and `github` GitHub; no branch `merge-3`. The main clone
  `~/lean/classical-lean` (the nightly's) is on `master` at `9c0639c`; its nightly fast-forwards it.
- **Records at `aba2d92`:** round 69 is LEAN-33's and round 68 (on the branch) CLOUD-MATH-3's, so
  this order's round is 70; 100 records files (orders and rounds); `records/CLAIMS.md` has 61 lines
  and `records/orders/INDEX.md` 69, each ending with LEAN-33's row (the branch's two files have 61
  and 69 lines too, each ending with CLOUD-MATH-3's row); the latest bridge baseline is
  `records/bridges/LEAN-33/` (COMMIT, pairs.tsv, shapes.tsv; its COMMIT names `9461986`);
  `tools/vacuity_reviewed.txt` holds 1 entry, unchanged on both branches; `records/rules.toml` line
  10 holds `outside_sha256 = "f39a512b6b1d3a56f15d03c8e420584993d1ef0b38700aae3bedc909e78c9fac"`.
- **HANDOFF.md and ROADMAP.md at `aba2d92`** (`grep -n` and `awk` in claude-ai's `facts-m3.out` and
  `facts2-m3.out`, 2026-10-20 23:57 and 2026-10-21 00:13 EDT): HANDOFF's section 1's last paragraph is
  LEAN-33's, whose first line begins
  ```
  **Dated 2026-10-21 UTC (order LEAN-33, round 69; branch `lean-33`, DSMain):**
  ```
  then a `---` line and `## 2. What I claimed, and what I actually checked`; section 0 comes
  before section 1, section 4 is `## 4. The gates, and their known limits`, section 6 `## 6. Working agreement`.
  ROADMAP's last subsection of section 1 is `### 1.26 Five items from below the plan's cut, and five witness rows
  (order LEAN-33, round 69)`, followed by `## 2. Categories to add`.
- **LEAN-33's push is this order's to record** (records/README.md rule 2: "the next order's records
  commit appends the push of the order before it to that order's INDEX row and CLAIMS row"), in the
  form CLOUD-MATH-3's records commit `65c8797` gave MERGE-2's rows: in the INDEX row, at the end of
  the state cell, before the commits cell; in the CLAIMS row, before the final ` |`. LEAN-33's INDEX
  row holds this text once, at the end of its state cell:
  ```
  no real bridge (baseline `records/bridges/LEAN-33/`)
  ```
  followed directly by a space, `|`, a space and its commits cell, which begins with the hash
  `ce41eef` in backticks. Its CLAIMS row holds this text once:
  ```
  after claude-ai's push review
  ```
  followed only by a space, `|` and the line end.
- **The helpers** in `~/lean/lean33-checks/scripts/` (sha256): `ev.sh`
  `7360900c631d67cb26d3ade5d42b4bc9c331995efff6be2cf62031ad83f9a256`, `hl.sh`
  `e7c00591f753511c52dfdbb886fe4d5e6de855a1a4190d8b11035f5f14ddb990`, `rootrun.sh`
  `f787d5bdbe7f3756b73ebc6cfdbdaebf98c8075af6e497214c25c56444426ba8` (each with exactly one line
  `D=/home/dustin/lean/lean33-checks`), `evcite.py`
  `f42d6814d14d44ae1140aa3f5b0b59d6d16bcdf82614507cdd3eb7dc8f0b010a` (the path on two lines, its
  docstring's line 3 and its `LOG = ` line 13), `citecheck.py`
  `7e3e38f7dd8b2ce97b3da5250feac31be410a99f840272324b18b021503bc366` (no path). `ev.sh`'s header
  names order LEAN-31's night window (Lean runs refused in the small hours).
- **How LEAN-33 ran its gates** (its `~/lean/lean33-checks/evidence.log`): `g1-build`, `g2-axiom`,
  `g3-vacuity`, `g3-tests` under the cap with `nice -n 19`; `g4-sorry`, `g5-records`, `g6-drift`,
  `g6-banned` plain; `g7` as `~/lean/recheck/run-recheck.sh <G> ~/lean/classical-lean-paper-crypto`
  under the cap, about 23 minutes (2026-10-20 from 22:40 to 23:03 EDT); `bridges` and `report`
  through `rootrun.sh`. Its vacuity tests: 89 verdicts, 47 flagged, 3 UNCHECKED as expected, 0
  mismatches. MERGE-2's bridge search, for a merge of five new modules: 290 new pairs, 58 new
  shapes, 47 gone, its section in the bridges file below.
- **The lane:** the bridges file `lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md` is
  `7cec75c22d572b7bfce8bd24e2cea6d53a34394d2478c9da770d4ac6d5e6d68e`, 148 lines, last row 162, so new
  rows start at 163; LEAN-33 found no bridge and wrote nothing to it. Each search that found a bridge
  added one section: MERGE-2's is lines 134 to 148 (a heading naming the order, baseline and commit;
  the rows; "Checked and not bridges", with how the pairs were checked and why the gone pairs went;
  a closing line). `lean/CLOUD-MATH-3/` holds `notes.md` and `data/cut-evidence.txt` only (`ds_list`,
  2026-10-21 00:00 EDT). At this order's filing, `lean/MERGE-3/` holds only this order and, under
  `data/`, claude-ai's two saved review reports of it (`rv1-pass1.txt`, `rv1-pass2.txt`). The
  upload route of job 2 was tried on the first: `ds_file` made it from one piece, and three
  `ds_write_staging` appends with the running `expect_sha256` completed it, each reply's
  `post_sha256` the expected prefix hash (claude-ai; `stat` of the lane file: born 2026-10-21
  00:14:45 EDT, last written 2026-10-21 00:15:37 EDT, sha256 `816bf62b…` as sent).
- **Timers on DSMain** (read 2026-10-20 23:31 EDT): w29-tracker and w29-sysmap every few minutes
  (they load no Lean); memory-index at midnight; restic, ds-hygiene, the daily verify, lean-nightly
  and the backup bundle between 2 and 4 in the morning; the store sync before 6.

## Goal

`master` gains the five CLOUD-MATH-3 modules on top of LEAN-33, every gate passing on the merged
tree, gate 7 included, the banned-vocabulary scan, the bridge search and the report tool run, the
cloud session's report, predictions and reviews copied to the lane, `incoming/` out of the tree (its
evidence and toolkit kept in git history), LEAN-33's push recorded, and the documents saying what
changed. Dustin pushes after claude-ai checks the push-review file.

## Scope

- **Branch.** `merge-3` from `aba2d92` in `~/lean/classical-lean-paper-crypto`, made after Dustin
  approves your plan. Nothing pushed. No sudo.
- **You may change in the repository:** `records/CLAIMS.md` and `records/orders/INDEX.md` by rule 2
  only, and the rest of `records/`; `incoming/` (removed, after its copies to the lane); `HANDOFF.md`
  section 1 and `ROADMAP.md` section 1 (job 3). What the merge itself brings in is not a change by
  you.
- **You may write in the lane:** your plan; job 2's three copies; in the bridges file, one appended
  section if job 4b finds a real bridge, and nothing if it finds none; your report and the
  push-review file. Nothing else.
- **You may not change** any `.lean` file, anything under `tools/`, `.github/` or
  `records/rules.toml`, or anything in `HANDOFF.md` outside section 1 (section 6's drift check
  hashes the text outside the generated block too). A gate failing on the merged tree is a stop:
  report it, change nothing to make it pass.
- **Off limits:** the main clone `~/lean/classical-lean` and its `master`; `~/break-it-5`;
  `~/trading`; `~/lean/recheck` (`run-recheck.sh` is run as gate 7, not edited); every earlier
  order's folder under `~/lean/` (read only; `~/lean/lean33-checks/` is the source of your helpers);
  Dustin's `~/.config/classical-lean/banned-terms` (the scanner reads it; never print or copy it);
  the GitHub branches (no push, no delete); `/data/api-credit/`, `~/api-credit/` and `/tmp/claude-ai-*/`
  (claude-ai's).
- **The night window and the memory cap,** as `ev.sh` enforces them (its header names the window;
  rule 36: name the window, do not copy its times). Before each whole-library run, log `pgrep -ax
  lean` through `ev.sh --nolean` (rc 1 when none runs; `pgrep -a lean` also matches a Samba process,
  as LEAN-33 found) and wait while a Lean process runs. Start gate 7 (about 23 minutes in LEAN-33)
  only when it cannot overlap the midnight memory-index run or the night window. If `ev.sh` refuses
  a run for the night window, it is logged `NOT RUN`: stop there and tell Dustin in one line; he
  resumes the session after the window, and you run it again under a new label. Every whole-library
  run under `ev.sh --cap` or `rootrun.sh`; never two Lean runs at once; read `crontab -l` and
  `systemctl --user list-timers` before you start; `~/.elan/bin` on `PATH`. claude-ai starts no Lean
  run on DSMain while this session runs.

## Check, then read

Check these sha256s first; if any differs, stop and say which:
- this order, `lean/MERGE-3/order.md`: the value in Dustin's prompt;
- `lean/MERGE-2-order.md` `81894b5bc85a6ee6858f7a1d8b065ee17ff5034f21df9ef68803cded13e4251a` (the
  pattern this order follows) and `lean/MERGE-2-report.md`
  `e6e4c2aaffce6d9e68dd3354c024c01a922e6ccc443a8589d3d94248ce5ba41e` (the report's layout, and its
  `docs-check` and `records2` checks);
- `lean/CLOUD-LANDING-PLAN-2.md` `26da22cef5604286b2b4b8fdfed4ec9fd70fb5c8520cb5dbfcd7b5c8411051a5`
  (rulings 3 and 5);
- `lean/CLOUD-MATH-3-order.md` `dfe8e5a96158f915e30cf856620410daa9ed28bdfa8d66eccb9b73e946a44dd7`;
- `lean/CLOUD-MATH-3/notes.md` `cc86957ebb0fdfeab5e81630472c9046a098a4ac89225ef02372024a0440f99d`;
- `lean/LEAN-33/report.md` `11c7482a69fea652d39ad0cb91c5a3cd0fe3b71c3f853649a6c94446f2187b5b`;
- `lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md`: the value above;
- on branch `cloud-math-3`, `git show 8c5fa22:incoming/REPORT.md | sha256sum`
  `331788bbf4e6a8c4d725fdb9574f18da0e05d4daac9d0b1b1dc0464b5a4d7580`, and the files of job 2's table;
- the five helpers above.
Then read them; in the repository `records/README.md` and `HANDOFF.md` sections 1, 4 and 6 (all 21
rules); on branch `cloud-math-3`, `incoming/REPORT.md`; and LEAN-33's `evidence.log` lines for the
labels named above.

## Rules

1. **Nothing is re-proved or edited in a module.** The five modules arrive as the cloud session left
   them. This order merges, measures and documents.
2. **The merge and its two conflicts.** `git merge --no-ff --no-commit github/cloud-math-3` after the
   records-first commit (RF below). Expected, as measured in trial (b): CONFLICT in exactly
   `records/CLAIMS.md` and `records/orders/INDEX.md`, one hunk each. Three scripts, each taking the
   commits it reads (`aba2d92`, `8c5fa22`, RF) and the file as arguments and refusing without them
   (rule 28), each run as `ev.sh --nolean <label> …` (script files in the evidence folder, bash where
   they need `<(…)`):
   - `resolve-pre`, run twice: on the staged files before RF's commit (reading `git show :<file>` in
     place of RF), and on RF after its commit, before the merge. For each file, `diff <(git show
     aba2d92:<file>) <(…)` must be exactly one hunk, `61c61,62` (CLAIMS) or `69c69,70` (INDEX):
     aba2d92's last line removed; added, a first line and a second line. The first must contain the
     push note of Setup 5 exactly once, equal aba2d92's last line once the note is removed, and have
     right after the note the measured text that followed its anchor (a space, `|`, a space and the
     backticked `ce41eef` in INDEX; a space, `|` and nothing more in CLAIMS); the second is this
     order's MERGE-3 row. Anything else is a stop.
   - `resolve`: for each file, write `git show 8c5fa22:<file>` followed by `git show RF:<file> | tail
     -2` (LEAN-33's row with its push, then the MERGE-3 row). So MERGE-2's row keeps the push the
     branch added, CLOUD-MATH-3's row follows it, then LEAN-33's, and MERGE-3's is last.
   - `resolve-check`: for each file, rebuild that expected file from the two `git show` outputs and
     compare it with the resolved file by `cmp`; then save both diffs whole and compare each, by
     `cmp`, with expected text the script builds from `git show` outputs:
     `diff <(git show 8c5fa22:<file>) <file>` is `61a62,63` (CLAIMS) or `69a70,71` (INDEX), then
     RF's last two lines, each prefixed `> `; `diff <(git show RF:<file>) <file>` is `60c60,61`
     (CLAIMS) or `68c68,69` (INDEX), then RF's MERGE-2 row prefixed `< `, a line `---`, then
     8c5fa22's MERGE-2 row and its CLOUD-MATH-3 row, each prefixed `> `.
   Any other conflict, or any difference, is a stop.
3. **HANDOFF section 6's 21 rules**, each named. Acted on here:
   - 1: the resolution is checked by whole-file and whole-diff comparison and by the measured text
     around the push note, not by counts; each scripted check has a negative control; the gates run
     on the merged tree, not the trial's.
   - 10: module paths compared exactly as `git diff --name-only` prints them, in full as above;
     citecheck labels matched exactly.
   - 17: every output saved with its sha256.
   - 18: when a step runs out of this order's sequence or overlaps another, round 70's fragment says
     so at that step, with dated times. Foreseeable here: a stop for the night window and its resume
     (Scope), and a stop and resume of job 2's upload. The rows after resolution run in clock order:
     MERGE-2, CLOUD-MATH-3 (`2026-10-21 00:21` UTC), LEAN-33 (`2026-10-21 01:25` UTC), then MERGE-3.
   - 20: warnings count only from `g1-build`'s `lake build`.
   - 22: round 70's quotes checked by script, with a planted misquote, before each of its two
     commits (RF and 4d's closing commit).
   - 23: every evidence command through `ev.sh`, which refuses without a prediction, refusals logged
     `NOT RUN`; every write, hash and edit of an evidence or records file through the helper, or
     listed in the plan and the fragment before the commit that carries it (Setup 1's copy script,
     which runs before `ev.sh` exists in the new folder, is listed in the plan). A commit is made
     only when its checks exited 0: before RF, `resolve-pre` on the staged files, check_records on
     the staged tree, and rule 22's and 36's checks; before the merge commit, `resolve-check` and the
     name-status check; before the `incoming/` removal, job 2's lane hashes equal to yours and `git
     diff --cached --name-status` showing exactly 614 deletions, all under `incoming/`, and nothing
     else; before G, the drift check and the docs check of job 3; before 4d's two commits,
     check_records, and for the baseline the `cmp` of its three files, for the closing commit rule
     22's and 36's checks.
   - 27: every count Lean generates in rule 4 was measured on trial (b)'s merge commit, whose
     `.lean` files and `tools/` are G's; hand numbers are not used.
   - 28: every script this order has you write (the push-note script, `resolve-pre`, `resolve`,
     `resolve-check`, the reviews builder and splitter, the docs check and the push-review script)
     takes its commits, paths and hashes as arguments and refuses to run without them.
   - 36: dated clock times; a scripted check, as MERGE-2's `records2`, that no line of round 70's
     fragment holds a time without its date (the pattern of rule 36), before each of its two
     commits, with a negative control: a scratch copy with one planted undated time is refused.
   - 38: `rootrun.sh` for the bridge search and the report tool.
   - 39: commits staged by path, messages written after their gates, each ending with the
     `Evidence:` line `evcite.py` writes, `citecheck.py` at the end.
   Only if you start a subagent: 12 and 26. Nothing to act on (no `.lean` file changes; no
   declaration is drafted, probed or proved; no cell, research note or tool pattern is written): 2,
   3, 14, 15, 19, 31 and 37. The five modules' declarations were reviewed cold by CLOUD-MATH-3: eight
   reviews, in `incoming/reviews/`.
4. **Predicted by claude-ai, measured on trial (b)'s merge commit `e8511f4`** (rule 27; its `.lean`
   files and `tools/` are G's): build 4193 jobs, 0 warnings; AxiomGate PASS 3527; check_sorry PASS
   140; check_records PASS 140 with 104 records files at G and at the final HEAD, and PASS 135 with
   102 at RF (the five modules are not in RF's tree); VacuityGate PASS with 1 reviewed helper, no new
   flag, no UNCHECKED, 0 VACUOUS-PENDING; `compile_rules.py drift` PASS; `banned_vocab_scan.py
   ClassicalLean` PASS, 140 files and the root file, 0 hits; the bridge search against
   `records/bridges/LEAN-33/`: rc 1, "3029 pairs, 758 shape candidates, N = 139", 209 new pairs, 23
   new shapes, 77 gone pairs, no gone shape, every NEW key naming one of the five modules and no GONE
   key naming one; the report tool: rc 0, written theorems 1961, A 1164 (OPEN 1120, DEPENDENT 44), B
   797 (CLOSES simp 15, CLOSES positivity 1, OPEN 781), C 36, 0 recursive, self-test 0 mismatches, no
   `CLOSES` line outside the self-test naming a constant of the five modules. Not run on the trial: the
   vacuity tests, as LEAN-33's at `aba2d92` (nothing under `tools/` changes): 89 verdicts, 47
   flagged, 3 UNCHECKED as expected, 0 mismatches; gate 7 ALL PASSED, with the trial's counts: 4193
   jobs, 140 modules 0 failed, 3527, the three standard axioms, the planted fault named. Check them,
   and add your own in a prediction file before any run (the records-file count and the two files'
   line counts at each records commit, the diffs of rule 2).
5. **Predict, then measure,** as LEAN-33 did: an evidence folder `~/lean/merge3-checks/` with
   `evidence.log`; every prediction file hashed into the log (`hl.sh`) before its run; hashes in
   records and the report by script, never typed. Git, hash and resolve commands, which load no Lean,
   run as `ev.sh --nolean …`. Every commit runs through `ev.sh --nolean` as `git commit -F <message
   file>`, with a label starting `commit-`; after it you append the line `COMMIT <hash>` to
   `evidence.log`. Between the `evcite.py` run that writes a message's `Evidence:` line and that
   commit's `COMMIT` line, the only evidence line is the `commit-…` line (citecheck reports any
   other).
6. **The merged tree is the one that counts.** Every gate, the bridge search and the report tool run
   on the clean tree of the last commit that touches anything outside `records/` (the commit that
   closes job 3; call it G and record its hash), with HEAD at G. Later commits touch only `records/`,
   and check_records runs again at the final HEAD.
7. **Master does not move under you.** If `origin/master` or GitHub's `master` is not `aba2d92` at
   setup or when you write the push-review file, stop and report. Never rebase; the one merge is
   rule 2's.

## Setup (after approval)

1. The helpers first. Make `~/lean/merge3-checks/scripts/`, check the five files' hashes above
   (all 64 characters), and copy them with one script (listed in your plan; it takes the source and
   target folders as arguments) that changes only:
   - in `ev.sh`, `hl.sh` and `rootrun.sh`, the one line `D=/home/dustin/lean/lean33-checks` to
     `D=/home/dustin/lean/merge3-checks`, refusing unless each file has exactly one such line;
   - in `evcite.py`, the path `/home/dustin/lean/lean33-checks/` to `/home/dustin/lean/merge3-checks/`
     on its two lines (the docstring's and the `LOG = ` line), refusing unless exactly two lines name
     it;
   - `citecheck.py` byte for byte (its sha256 must stay the full value above).
   Then log the five new sha256s with `hl.sh`, write `pred-setup.md` (the predictions for steps 2 and
   3) and hash it with `hl.sh` before step 2's first run.
2. Test the helpers before first use (rules 23, 38, 39), each logged and predicted; a test that does
   not behave as predicted is a stop:
   - `ev.sh` with an empty prediction is refused, exit 97, and logs `NOT RUN`.
   - `ROOTRUN_BUILD=false rootrun.sh t-rootrun-false "<pred>" touch ~/lean/merge3-checks/ran`: exit
     95, logged `NOT RUN`, and the file `ran` does not appear.
   - before the real-build test, `ev.sh --nolean pre-real "<pred>" bash -c 'git status --porcelain; git
     rev-parse HEAD'` (predicted: no status line, and `aba2d92ba76989f3afe9324cb3b8b3b126095089`); a
     dirty tree or another head is a stop. Then `rootrun.sh t-rootrun-real "<pred>" true`, with the
     real root build at `aba2d92`, outside the night window: the `t-rootrun-real-build` line comes
     before the `t-rootrun-real` line in `evidence.log`, and both carry the same head.
   - citecheck on scratch copies of `evidence.log` (the real log is not touched): on one copy, append
     two planted lines in the log's format with labels `p-one` and `p-two`; run `evcite.py <copy>`
     and save its line; append `COMMIT ffffff0`; then `citecheck.py <copy> --message <file> ffffff0`
     with a message ending in that line prints `OK ffffff0`, exit 0, and with the same line minus
     `, p-two` prints exactly `DIFF ffffff0: label left out: p-two`, exit 1. On a second copy, the
     same two planted lines and `evcite.py` run, then a line labelled `commit-p`, then `COMMIT
     ffffff1`: the message ending in its `evcite.py` line prints `OK ffffff1`, exit 0 (rule 5's one
     allowed line).
3. Then the repository checks, through `ev.sh --nolean setup1 …`: `git fetch origin && git fetch
   github cloud-math-3` in the worktree; `origin/master` and `git ls-remote github master` both
   `aba2d92…`; `github/cloud-math-3` `8c5fa22…`; `git merge-base --is-ancestor 04e4a38
   github/cloud-math-3` exit 0; `git status --porcelain` empty. If not, stop.
4. Write the prediction file for every later run (rule 4), hash it, then
   `git switch -c merge-3 aba2d92`.
5. **Records first (RF),** one commit, no `.lean` file:
   - this order's copy as `records/orders/<UTC>__claude-ai__order-merge3-cloud-math-3.md`;
   - LEAN-33's push, by inserting this exact text
     ```
     ; pushed by Dustin: DSMain's master ref written 2026-10-20 23:28:52 EDT, GitHub master equal (`aba2d92`)
     ```
     into LEAN-33's INDEX row and CLAIMS row, each right after its anchor given above (so the INDEX
     note ends the state cell, before its commits cell, and the CLAIMS note comes before the final
     ` |`), by a script that takes the two files, `aba2d92` and the note as arguments, and does this
     before anything is appended: it takes LEAN-33's row as the file's last line, refusing unless
     that line equals `aba2d92`'s last line and starts `| LEAN-33 |` (INDEX) or holds ``executing
     order `LEAN-33` `` (CLAIMS); refuses unless the anchor occurs exactly once in that row and is
     followed by exactly the measured text given above; inserts the note there; nothing else in
     either row changes;
   - then this order's INDEX row (`| MERGE-3 |`) and CLAIMS row, each as the new last line of its
     file;
   - round 70's fragment `records/rounds/<UTC>__round-70-merge-cloud-math-3.md`, naming the five
     module paths in full (round 68 names them too) and saying the round lands order CLOUD-MATH-3.
   Do not touch MERGE-2's rows (the branch carries their push). Before the commit: `resolve-pre` on
   the staged files (rule 2); check_records on the staged tree, PASS 135, 102 records files; rule
   22's quote check of round 70's fragment, and its planted-misquote control; rule 36's date check of
   the fragment, and its planted control.

## The work

### Job 1: the merge

`resolve-pre` on RF first (its second run, rule 2). Then `git merge --no-ff --no-commit github/cloud-math-3`, through
`ev.sh --nolean` (predicted rc 1, the two conflicts of rule 2). Resolve by `resolve`, check by
`resolve-check`, and stage the two files by path. Then, before committing: `ev.sh --nolean
name-status "<pred>" git diff --cached --name-status aba2d92` lists only `ClassicalLean.lean`, the
five new modules (paths as above), 614 paths under `incoming/`, `records/CLAIMS.md`,
`records/orders/INDEX.md`, CLOUD-MATH-3's order copy and round 68's fragment, and this order's own
two records files (its order copy and round 70). Then write the message to a file: "Merge order
CLOUD-MATH-3 (items 113, 121, 124, 126, 130) into master (order MERGE-3)", the two conflicts and
their resolution, and its `Evidence:` line, generated last. Commit with `ev.sh --nolean commit-merge
… git commit -F <file>`, then append `COMMIT <hash>`.

### Job 2: the cloud session's report, predictions and reviews to the lane, then incoming/ out of the tree

The sources, at `8c5fa22` (claude-ai, `git show 8c5fa22:<path> | wc -c` and `| sha256sum`; none of
the ten holds a backslash: `grep -c` in `facts-m3.out` and `facts2-m3.out`):

| path | bytes | sha256 |
|---|---|---|
| `incoming/REPORT.md` | 14132 | `331788bbf4e6a8c4d725fdb9574f18da0e05d4daac9d0b1b1dc0464b5a4d7580` |
| `incoming/PREDICTIONS.md` | 3126 | `489f3b3cf4e408a48393d577ca055ce6fc2d6a9fff81a26de4898be6e9320b72` |
| `incoming/reviews/rv1-statements.md` | 18445 | `6261731d78c743c5c0e153e2c782dafe1fc9dd7d1e7e07fa9d37dfa3b7970189` |
| `incoming/reviews/rv1c-confirm.md` | 6349 | `3dfd03bbefe552be8255a1f1406665b6d264a8eb5f989047a247528b6cdeeab6` |
| `incoming/reviews/rv2-113.md` | 10280 | `917a71953376ec3b4c0c82d035db2776c34eaaa9f1ac5a909724e44b09cad161` |
| `incoming/reviews/rv2-121.md` | 11217 | `f5e709b8eea61d8f0483b93a68424bad98034fb64d9fdddff6ee301943833be8` |
| `incoming/reviews/rv2-124.md` | 13255 | `94aba9efc49a484e27a252cd90036da5871b02a01d17c0ba2799e8122c4638f8` |
| `incoming/reviews/rv2-126.md` | 10940 | `e677a363153973422b596347bbd5be19f1e2183fbffc52a4a9debdeddf5f2ffb` |
| `incoming/reviews/rv2-130.md` | 13345 | `188f4b17d5bfff18d6a433e0f4394a55f456358a482fb1395ba4c21f0d73f0e8` |
| `incoming/reviews/rv2c-124.md` | 8875 | `083764952957c9526835224e21ac0dbfb523539da3fa2fc2aec5c22334d1f61b` |

Check each against the table first. Then:
- `incoming/REPORT.md` through `ds_file`, job `CLOUD-MATH-3`, kind `report` → `lean/CLOUD-MATH-3/report.md`;
- `incoming/PREDICTIONS.md` through `ds_file`, job `CLOUD-MATH-3`, subdir `data`, name
  `PREDICTIONS.md` → `lean/CLOUD-MATH-3/data/PREDICTIONS.md`;
- the eight reviews (92,706 bytes) into one file `reviews.md`, built by a script: each under a
  heading line giving its path, its byte length and its sha256, then its bytes unchanged; split it
  back by the lengths with a second script and check every part against the table before sending.
  It goes up in pieces of at most about 20,000 bytes, each cut at a line end (MERGE-2 sent its
  126,344-byte file in 7 pieces, the running sha256 checked after each): the first through
  `ds_file`, job `CLOUD-MATH-3`, subdir `data`, name `reviews.md` →
  `lean/CLOUD-MATH-3/data/reviews.md`; each later one through `ds_write_staging`, path
  `inbox/threads/staging/lean/CLOUD-MATH-3/data/reviews.md`, mode `append`, `expect_sha256` the
  sha256 of the pieces sent so far (your own prefix file's hash, which must equal the last reply's
  `post_sha256`). At the end the lane file's sha256 equals your built file's. A refusal or a
  mismatch is a stop: report the lane file's sha256 and which prefix of your pieces it equals (or
  that it equals none). On resume (rule 18), append from that prefix to the same file, never into
  a second one; a lane file that equals no prefix is a stop for Dustin.
`incoming/README.md`, `incoming/tools/`, `incoming/cm2-scripts/` and `incoming/evidence/` are not
copied: they stay in git history, reachable from master through the merge's second parent `8c5fa22`
once pushed (`git show 8c5fa22:incoming/README.md`; `git archive 8c5fa22 incoming/tools`;
`incoming/tools/SHA256SUMS` hashes to 7d5d5039…). Then `git rm -r incoming` through `ev.sh
--nolean` in its own commit; its message names the three lane files and their hashes and gives
those two commands and that hash.

### Job 3: documents

- `HANDOFF.md` section 1: after LEAN-33's paragraph (its first line given above) and before the
  `---` line above `## 2.`, a dated paragraph for order CLOUD-MATH-3
  (round 68) and its merge by MERGE-3 (round 70), in MERGE-2's form: the five modules by name and
  item, one line each (113 GENERALIZED: no convexity asked, as round 68 says); that the cloud
  session's report, predictions and reviews went to the lane and `incoming/` left the tree, its
  toolkit and evidence in history at `8c5fa22` (the two commands of job 2); that the last cloud
  commit's `Evidence:` line cannot be citechecked from the committed log (one sentence, as the facts
  above give it); the counts of rule 4, to be re-measured by this order's gates on the clean tree:
  **140 modules, 3527 theorem constants (3468 + 59, round 68's censuses), `lake build` 4193 jobs, 0
  warnings**.
- `HANDOFF.md` outside section 1: **no change at all** (the drift check reads section 6's text
  outside the generated block against `meta.outside_sha256` in `records/rules.toml`).
- `ROADMAP.md`: after section 1.26 and before `## 2. Categories to add`, a section 1.27 for items
  113, 121, 124, 126 and 130, landed from below the plan's cut by order CLOUD-MATH-3 in a cloud
  session and merged by MERGE-3, in section 1.25's form.
- Before the documents commit, a docs check as MERGE-2's `docs-check` (lean/MERGE-2-report.md,
  section Documents; a script taking the two files and `aba2d92` as arguments): `git diff -U0
  aba2d92 -- HANDOFF.md ROADMAP.md` adds lines only; HANDOFF's one hunk starts before the line of
  `## 2.` and after LEAN-33's paragraph; ROADMAP's one hunk lies between 1.26's heading and `## 2.`;
  no added line over 100 characters except the 1.27 heading (as 1.25's); and the drift check.
- Commit jobs 2 and 3 separately; the documents commit is G (rule 6).

### Job 4: the end checks, in this order

The gates run first, before anything else loads the library; HEAD stays at G until 4d.

- **4a. The gates**, on the clean tree at G, each through `ev.sh` with its prediction (rule 4), in
  LEAN-33's forms: `ev.sh --cap g1-build … nice -n 19 lake build`; `ev.sh --cap g2-axiom … nice -n 19
  lake env lean tools/AxiomGate.lean`; `ev.sh --cap g3-vacuity … nice -n 19 lake env lean
  tools/VacuityGate.lean`; `ev.sh --cap g3-tests … nice -n 19 python3 -I tools/run_vacuity_tests.py`;
  `ev.sh g4-sorry … python3 -I tools/check_sorry.py`; `ev.sh g5-records … python3 -I
  tools/check_records.py`; `ev.sh g6-drift … python3 tools/compile_rules.py drift records/rules.toml
  HANDOFF.md`; `ev.sh g6-banned … python3 -I tools/banned_vocab_scan.py ClassicalLean`; and gate 7,
  `ev.sh --cap g7 … ~/lean/recheck/run-recheck.sh <G> ~/lean/classical-lean-paper-crypto`. A gate that
  fails is a stop: 4b to 4e and 4g do not run, but 4f's report is still written (what failed, each
  gate predicted beside measured, what did not run).
- **4b. The bridge search,** through `rootrun.sh` (rule 38), at G, only after 4a passed:
  `rootrun.sh bridges … python3 -I tools/bridge_search.py --diff records/bridges/LEAN-33/ --out ~/lean/merge3-checks/bridges/MERGE-3`
  (outside the tree); rc 1 means candidates to review. Report NEW and GONE keys, pairs and shapes,
  against rule 4's numbers. Check each NEW import-unrelated pair and each NEW shape for a theorem
  whose proof needs both sides, and explain the gone pairs by script as MERGE-2 did (the constants
  each shared, and what pushed them past the document-frequency cut). Say exactly how the pairs were
  checked: which were read statement by statement, and how the rest were judged.
  lean/CLOUD-LANDING-PLAN-2.md ruling 5 has LEAN-38 read pair by pair "the new pairs of MERGE-2's
  search that were not read closely"; claude-ai's ruling (2026-10-21, Dustin may veto; store row
  20261021-001): LEAN-38 reads the new pairs of this order's search that were not read closely in the
  same way, so the record must say which those are.
  - If a real bridge is found: one section appended to the bridges file (path
    `inbox/threads/staging/lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md`, mode
    `append`), in one `ds_write_staging` call with `expect_sha256` `7cec75c2…` in full as above if
    it is at most about 20,000 bytes, or else in pieces cut at line ends, the first with that
    `expect_sha256` and each later one with the running hash, as in job 2. The section is in the form of
    MERGE-2's (the file's lines 134 to 148): its heading naming this order, `records/bridges/MERGE-3/`,
    `LEAN-33/` and G; the rows, numbered from 163, in the file's columns; "Checked and not bridges",
    with how the pairs were checked and why the gone pairs went; the closing line. If a write is
    refused, stop and report the file's sha256 and which prefix of your section it equals.
  - If none is found: nothing is written to the bridges file (as LEAN-33); the method goes in your
    report only.
- **4c. The report tool,** through `rootrun.sh`, at G (HEAD still G, before the baseline commit),
  once: `rootrun.sh report … nice -n 19 lake env lean tools/UninformativeReport.lean`; a report, not
  a gate. Its counts as rule 4 gives them. List every `CLOSES` line that names a constant of the five
  modules; none is expected.
- **4d. The baseline and the records.** First the new baseline: copy `~/lean/merge3-checks/bridges/MERGE-3/`
  (COMMIT, pairs.tsv, shapes.tsv) to `records/bridges/MERGE-3/`, check each by `cmp`, one commit
  touching only `records/`. Then close the records: round 70's follow-up edit with the commit hashes
  and the measured counts, its quotes checked by script with the planted control (rule 22) and its
  dates checked (rule 36); the CLAIMS row closed and the INDEX row's state set; one records-only
  commit. Then check_records again at the final HEAD, predicted PASS 140, 104 records files.
- **4e. citecheck**, two runs, both through `ev.sh`:
  - this order's own commits, `git rev-list --first-parent aba2d92..HEAD` (six: RF, the merge, the
    `incoming/` removal, G, the baseline, the closing commit), each by
    `citecheck.py ~/lean/merge3-checks/evidence.log --message <its message file> <hash>`
    (`git log -1 --format=%B <hash>` to a file), by one loop: every one `OK`, rc 0;
  - the repository run `citecheck.py ~/lean/merge3-checks/evidence.log ~/lean/classical-lean-paper-crypto aba2d92`,
    for the record. Predicted rc 1: this order's own commits `OK`; the 8 CLOUD-MATH-3 commits each a
    line beginning `DIFF <hash>: no COMMIT marker for <hash> in the log` (label differences may
    follow on the same line, since their ranges are compared against this log; their `Evidence:`
    lines cite the cloud session's log, checked by its End check 2 for the first seven and by
    claude-ai for all eight: lean/CLOUD-MATH-3/notes.md); `313e9a7` `NO-EVIDENCE` (claude-ai's
    incoming/ commit, checked by lean/CLOUD-MATH-3-order.md's rests-on lines).
- **4f. Report** through `ds_file` (job `MERGE-3`, kind `report` → `lean/MERGE-3/report.md`), laid
  out like MERGE-2's (lean/MERGE-2-report.md): in short; setup and the helper tests; the merge and
  its two resolved conflicts (the two diffs); the lane copies; LEAN-33's push recorded; documents;
  G's hash; predicted beside measured for every gate and count; the bridge diff and how it was
  checked; 4c's `CLOSES` lines that name a constant of the five modules (or "none"); commits; 4e's
  output; misses; the push command as one line, not run:
  `cd ~/lean/classical-lean-paper-crypto && git push origin merge-3:master && git push github merge-3:master`.
  Say in the report that the GitHub push starts a CI run on `master`.
- **4g. Push-review file** through `ds_file` (job `MERGE-3`, subdir `data`, name
  `MERGE-3-push-review.txt` → `lean/MERGE-3/data/MERGE-3-push-review.txt`), by one script taking G's
  hash as an argument, each command followed by its full output and, where given, compared with its
  prediction:
  - `git rev-parse HEAD`; `git status --porcelain` (empty); `git ls-remote origin master` and `git
    ls-remote github master` (both still `aba2d92`, rule 7);
  - `git merge-base --is-ancestor aba2d92 HEAD` and `git merge-base --is-ancestor
    8c5fa226384c977b16301047f8a20ae306ea1ab6 HEAD`, each with its exit code (0);
  - the merge commit's `git log -1 --format='%H %P'` (parents RF and
    `8c5fa226384c977b16301047f8a20ae306ea1ab6`); `git rev-list --count aba2d92..HEAD` (15: this
    order's six commits and the branch's nine, `313e9a7` and the eight cloud commits);
  - `git log --first-parent --name-status --format='== %h %cI %s' aba2d92..HEAD` (files under
    `incoming/` and `records/bridges/` as counts only);
  - `git diff -U0 aba2d92 HEAD -- ClassicalLean.lean records/CLAIMS.md records/orders/INDEX.md`
    (predicted: `ClassicalLean.lean` five lines added, the five imports, none removed; CLAIMS one
    hunk `@@ -60,2 +60,4 @@` and INDEX one hunk `@@ -68,2 +68,4 @@`, each replacing MERGE-2's and
    LEAN-33's rows with four: MERGE-2's with its push, CLOUD-MATH-3's, LEAN-33's with its push,
    MERGE-3's);
  - `git diff --name-only 8c5fa22 <G> -- ClassicalLean ClassicalLean.lean tools .github
    records/rules.toml ':(glob)lakefile*' lake-manifest.json lean-toolchain` (predicted: exactly the
    seven LEAN-33 paths above);
  - `git diff --name-only aba2d92 <G> --` with the same paths (predicted: exactly
    `ClassicalLean.lean` and the five new module paths above);
  - the docs check of job 3 again, at G (HANDOFF changed only between LEAN-33's paragraph and `## 2.`,
    so sections 0 and 2 to 6 are untouched; ROADMAP only between 1.26 and `## 2.`);
  - `git ls-tree --name-only <G> | grep -c '^lakefile'` (1); `git diff --name-only <G> HEAD` (only
    under `records/`: the baseline's three files, round 70, CLAIMS and INDEX);
  - 4d's final check_records output (PASS 140, 104 records files) and 4e's two outputs.
  Report its sha256. Then stop. claude-ai reviews it before Dustin pushes.

## Done means

- Branch `merge-3` from `aba2d92`, clean tree, nothing pushed; its first commit is RF (with LEAN-33's
  push); then the merge (its two conflicts resolved by rule 2); then the `incoming/` removal; then
  documents (G); then the baseline and the closing commit, records only.
- The helpers copied, their five sha256s logged, and their tests logged before first use.
- The three lane copies exist at the paths named, with hashes equal to yours and to the originals.
- Every gate as predicted on the merged tree at G, or each miss reported; gate 7 ALL PASSED at G;
  after G only `records/` changed, and check_records passes at the final HEAD.
- The bridge diff reported with how it was checked; real bridges (if any) in one appended section
  from row 163; the new baseline committed.
- Job 3's documents changed and named (HANDOFF section 1 and ROADMAP section 1.27 only; HANDOFF
  outside section 1 untouched); the drift check passes.
- 4c's report-tool run reported, with its `CLOSES` lines for the five modules.
- 4e's two outputs in the report; every commit of this order `OK`.
- The report and push-review file in `lean/MERGE-3/`, hashes matching yours.

Then report in a few plain sentences: what merged, the gate results beside the predictions, any new
bridge, the two files' hashes and the push command. Dustin reads your replies carefully and is still
learning to read code: plain words, and define a technical term the first time you use it. When you
need a decision from him, ask in one line with your recommended answer first.

## Not in this order

- Any change to a `.lean` file, to `tools/`, `.github/` or `records/rules.toml`.
- Deleting the GitHub branches `cloud-ci`, `cloud-math-1`, `cloud-math-2` and `cloud-math-3` (Dustin's
  call, later).
- LEAN-34 (batch 4 and VACUITY-3 row 70; its draft is lane `lean/LEAN-34/data/order-draft-r3.md`,
  cut by claude-ai after this order is pushed) and LEAN-35 to LEAN-37.

## Revisions

- r1, review pass 1 (one fresh reviewer; 0 BLOCKER, 4 MAJOR, 12 MINOR; its report saved verbatim,
  sha256 `816bf62b5a81d945e67ddffd1a0be7f1738179c9ce4c74fa1683ff9a5be437fb`): MAJOR: LEAN-33's push
  note now has exact anchors, both endings stated correctly, and a script that refuses unless each
  anchor occurs once; the reviews copy has a route for its 92,706 bytes (the first piece through
  `ds_file`, the rest appended with the running hash); the bridges file gets at most one appended
  section in MERGE-2's form, allowed in Scope, and nothing when no bridge is found; the trial's
  "predictions written first" is backed by the file's mtime and its wrong header time is logged
  (store row 20261020-027). MINOR: rule 4's false sentence replaced by the measured seven-module
  list; `trial-m3.out`'s finished hash; the HANDOFF and ROADMAP places given by text and measured;
  rule 2's checks made whole-file and whole-diff by script, with the measured diff headers; all 21
  rules of section 6 named; the bridge and report numbers measured on the trial merge (rule 27;
  one prediction missed, store row 20261020-028); every landing path named; 4c before the baseline
  commit; the push-review predictions (rev-list 15, the parents, the `-U0` hunks, `ClassicalLean.lean`
  and `records/rules.toml` in the pathspecs, the docs check); ruling 5's file, MERGE-2's report and
  the cloud report's hash added to the checks; the third citecheck test; the night-window refusal,
  the midnight timer and a dated clock line.
- r2, review pass 2 (the same reviewer; 0 BLOCKER, 0 MAJOR, 10 MINOR; saved verbatim, sha256
  `1ad7e2bdd5ae5855ca4ce930b9f8d65db65db68099da0a8db44bacd176a31a17`): the push-note script finds
  LEAN-33's row as the last line and checks its start, inserts before anything is appended, and
  asserts the measured text after the anchor; `resolve-pre` checks the note's placement
  independently and runs on the staged files before RF's commit as well as after; the scripts take
  `aba2d92` and `8c5fa22` as arguments; the reviews upload says how to report and resume a stop,
  and its route was tried by claude-ai on this order's own review file; the bridges section may go
  in pieces; the backslash count, the prediction file's `stat` and the ROADMAP heading are now cited
  from saved outputs; rule 18 stated as it reads, rule 36 given a negative control; the `incoming/`
  removal commit's checks named; ruling 5 quoted exactly, with claude-ai's extension as a vetoable
  ruling (store row 20261021-001); a gate failure still gets its report; dated and UTC-labelled
  times.
