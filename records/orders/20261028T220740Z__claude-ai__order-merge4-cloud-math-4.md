# MERGE-4 order: cloud-math-4 (CLOUD-MATH-4's three bridges) into master

For a plain Claude Code session on DSMain, as dustin, in tmux `cc`. Written by claude-ai on 2026-10-28 in
Project LEAN, to the lighter procedure (store row 20261026-063). One cold pass on helios
(`~/merge4-review-1/out1/review.md`, PASS WITH FINDINGS: F1 MAJOR, F2 to F12 MINOR, all applied here).

**When to start.** After the LEAN-37 session has written its close note and the worktree is clean, and
outside the night window that `~/lean/vacuity4-checks/scripts/ev.sh`'s header names (no Lean run from 01:45
to 05:45). Do not start a Lean run that is not expected to end before 01:45 by the times below (the witness gate
about 28 minutes, gate 7 about 22); if the window comes, stop at a clean point, say so, and go on when
Dustin says to.
About 2 hours; the two long gates take about 50 minutes (the whole-library witness gate 27.4 minutes at
LEAN-37's G, gate 7 about 22).

**Launch check.** This session was started with `CLAUDE_CODE_DISABLE_AUTO_MEMORY=1`. Print it first; if it is
not `1`, stop and say so.

## Goal

Merge GitHub's branch `cloud-math-4` (three new modules from order CLOUD-MATH-4, all three bridges landed and
checked) into master on branch `merge-4`, with its two record conflicts resolved by script, the cloud
session's report and review copied to the lane and `incoming/` taken out of the tree, every library-wide gate
the cloud could not run run here, HANDOFF and ROADMAP entries, records, and a push-review file. Dustin pushes
after claude-ai checks that file.

## What is already true (measured by claude-ai, 2026-10-28, 17:44 to 18:05 EDT)

- Master is `3b62d24f740d6f649ce5a9c98a04a8b51edd28d7` on both remotes (LEAN-37, pushed by Dustin; the bare repo's
  ref written 17:59:13 EDT; store row 20261028-006); its CI run is 40776387516. The worktree
  `~/lean/classical-lean-paper-crypto` is on branch `lean-37` at `3b62d24`, porcelain empty.
- GitHub's `cloud-math-4` is `91d98e790d38b0118ac66a4ee444ac7267b083bb`, 7 commits on `67d05bf` (LEAN-37's base), its
  CI run 40770205149 green. Against `67d05bf` it adds `ClassicalLean/InformationTheory/HuffmanEntropy.lean`,
  `ClassicalLean/Probability/PrincipalComponents.lean`, `ClassicalLean/Statistics/JamesSteinRisk.lean`, three
  import lines at the end of `ClassicalLean.lean`'s import block, its order copy
  `records/orders/20261028T201746Z__claude-ai__order-cloudmath4-huffman-entropy-principal-components-james-stein-risk.md`,
  round 77 `records/rounds/20261028T201747Z__round-77-huffman-entropy-principal-components-james-stein-risk.md`,
  one row at the bottom of each of `records/orders/INDEX.md` and `records/CLAIMS.md` and no other change to
  either (`git diff -U0 67d05bf 91d98e7`: `@@ -68,0 +69 @@` in CLAIMS, `@@ -76,0 +77 @@` in INDEX, one added line
  each, the CLOUD-MATH-4 rows), and `incoming/` with
  exactly two files: `incoming/REPORT.md` (9758 bytes, sha256
  `ffb88c36e6d7fea8090cd47ef24e214c344f92dfaaa30a4315967661af4191ac`) and `incoming/reviews/review-1.md` (15947,
  `b423184f4f46b1d4eb763b0790497d5154d00ebf67dc98a3a07f365a75a47779`). It removes no line under `ClassicalLean/`.
- claude-ai's rerun on a fresh clone of `cloud-math-4` (store row 20261028-005): build 4196 jobs, 0 warnings;
  AxiomGate PASS 3683; check_sorry and check_records PASS 143; VacuityGate PASS, 1 reviewed helper; witness
  gate on the three modules OK 6, copy-error 0; drift PASS.
- claude-ai's trial merge of `cloud-math-4` onto `lean-37` at `3b62d24` (`git merge --no-ff --no-commit`): rc 1,
  CONFLICT in exactly `records/CLAIMS.md` and `records/orders/INDEX.md`, one hunk each; everything else merged
  cleanly (the three modules, `ClassicalLean.lean`, the two records files of the cloud order, `incoming/`).
- At `3b62d24` (LEAN-37's push-review file and claude-ai's review-1, row 20261028-004): build 4193 jobs, 0
  warnings; AxiomGate 3827 (gate 7's count); type dump 4346 records (4163 + 183); whole-library witness gate
  OK 189, copy-error 0, 1642.9 s; gate 7 ALL PASSED; root closure 5729 modules. `HANDOFF.md` sha256
  `fe3740b698d837382e89f3e54440b2126ae5828a9675d9b56aca318610d7b827` (1495 lines; section 1's last dated paragraph
  LEAN-37's, line 540); `ROADMAP.md` `3c160ce17bdc00480157d60acab742c9a09248b537a1b01c7bccc57b922acec9` (last section
  1.31, line 949); `records/rules.toml` `2b5fb47dc4751d93171969649f9dc4f7b7e1233cdbc36bb06713c20e23bb0359`. The last
  round on master is 76; the cloud brings 77; this order's is 78. The last rows of INDEX and CLAIMS on master
  are LEAN-37's. The bridge baseline is `records/bridges/LEAN-37/`; the bridges file ends at row 167.

## Scope

- Branch `merge-4` from `3b62d24`. Nothing pushed. No sudo. Never rebase; the merge is one `--no-ff` merge
  commit.
- You may change: what the merge brings; `records/` (the two resolved files, this order's copy, round 78,
  LEAN-37's push on its rows, the new bridge baseline); `incoming/` (removed); `HANDOFF.md` section 1 (one
  dated paragraph after LEAN-37's); `ROADMAP.md` (a section 1.32 after 1.31, in its form); the bridges file
  (a real bridge only, from row 168). No existing module changes. Needing to change anything else is a stop.
- Your files: `~/lean/merge4-checks/`. Lane writes through the connector: the report (`ds_file`, project
  `lean`, job `MERGE-4`, kind `report`), the push-review file (subdir `data`, name `MERGE-4-push-review.txt`),
  and the two cloud copies (step 5). A file over a few kilobytes goes byte for byte through DSMain's drop
  folder: copy it to `/opt/datasphere/drop/<name>`, then `ds_copy_in` with its sha256 (it lands in
  `<job>/data/<name>`), as LEAN-37's session did.
- Off limits as in every order: `~/lean/classical-lean`, every earlier order's folder (read only),
  `~/api-credit/` and `/tmp/claude-ai-*` (read only), `/data/api-credit/`, Dustin's
  `~/.config/classical-lean/banned-terms` (never print or copy it), every GitHub branch (fetch only).
- Lean runs: one at a time, under the 12 GB cap, `~/.elan/bin` on `PATH`, `pgrep -ax lean` empty before each.

## The work

1. **Check.** Launch variable; `git fetch origin`; `git fetch github cloud-math-4`; `git ls-remote origin
   master` and `git ls-remote github master` both `3b62d24…`; `git rev-parse github/cloud-math-4` is
   `91d98e790d38b0118ac66a4ee444ac7267b083bb`; porcelain empty; HANDOFF, ROADMAP and rules.toml sha256 as above;
   `git show 91d98e7:incoming/REPORT.md | sha256sum` and the same for the review, as above. If anything
   differs, stop.
2. **Before** (on a clean `3b62d24`): copy lane `lean/LEAN-33/scripts/TypeDumpPI.lean` (sha256
   `1fcb69f41ddbd35f84862521d2ead5946a0bd52caf5f60b6d10e966cfd9776ff`) and lane `lean/LEAN-33/scripts/g8-typediff.py`
   (`371eda9a2e5065abaa8f36bac9872d0f15e7bade72a248d5f0f88f20b4eacb71`, as `g8_typediff.py`) from the lane
   through the connector into `~/lean/merge4-checks/`, checking each hash; `lake build`; `lake env lean
   ~/lean/merge4-checks/TypeDumpPI.lean > ~/lean/merge4-checks/td-before.out`, its lines starting `{` in
   `~/lean/merge4-checks/td-before.jsonl`; `python3 -I ~/lean/merge4-checks/g8_typediff.py check
   ~/lean/merge4-checks/td-before.jsonl`: 4346 records. Every file of this order lives in `~/lean/merge4-checks/`,
   never in the worktree.
3. **Records first** (RF). First `git switch -c merge-4 3b62d24`, and check `git rev-parse HEAD` and `git branch
   --show-current`. Then one commit, no `.lean` file: this order's copy in `records/orders/`; its
   INDEX row and CLAIMS row at the bottom (`| MERGE-4 |`, in MERGE-3's rows' form); round 78's fragment
   naming the three modules by full path; and LEAN-37's push recorded in LEAN-37's two rows as VACUITY-5's was. The note is
   `; pushed by Dustin: master 3b62d24 on both remotes, CI run 40776387516 <result>`, `<result>` being `green`
   for `gh run view 40776387516 -R datasphereai/classical-lean --json conclusion` = `success`, `in progress` for
   an empty conclusion; `failure` or `cancelled` is a stop. In INDEX it goes immediately before the text
   `` | `2123af1` (records)`` (once in LEAN-37's row, measured); in CLAIMS it replaces the final ` |` of LEAN-37's
   row, right after `not pushed, the push is Dustin's after claude-ai's push review` (once, measured). Check by
   script before the commit: each row changed only by that insertion, the note once, everything else in both
   files equal to `3b62d24`'s apart from the two new MERGE-4 rows at the bottom. check_records PASS.
4. **The merge.** First check (e): for each of the two files, `diff <(git show 67d05bf:<file>) <(git show
   91d98e790d38b0118ac66a4ee444ac7267b083bb:<file>)` is exactly one added line after the last line, which starts `| CLOUD-MATH-4 |`
   (INDEX) or holds ``executing order `CLOUD-MATH-4` `` (CLAIMS); anything else is a stop. Then `git merge
   --no-ff --no-commit 91d98e790d38b0118ac66a4ee444ac7267b083bb`. Expected: rc 1, CONFLICT
   in exactly `records/CLAIMS.md` and `records/orders/INDEX.md`. Resolve each by one script that takes the
   commits it reads as arguments: the resolved file is RF's version with its last line removed, then
   `91d98e7`'s last line (CLOUD-MATH-4's row), then RF's last line (MERGE-4's row). Check by a second script:
   (a) the resolved file has exactly one more line than RF's; (b) deleting the CLOUD-MATH-4 row from it gives
   RF's file byte for byte, and the deleted line equals `git show 91d98e7:<file> | tail -1` byte for byte; (c) its last three lines are LEAN-37's row (with the push), CLOUD-MATH-4's row and
   MERGE-4's row, in that order; (d) the lines above LEAN-37's row equal the lines above LEAN-37's row in
   `3b62d24`'s file. Any other conflict, or any check that fails, is a stop. Before the commit, `git diff --cached --name-status
   3b62d24` lists exactly: the three modules (A), `ClassicalLean.lean` (M), the two `incoming/` files (A), the
   cloud's order copy and round 77 (A), and the two resolved files (M); anything else is a stop. Commit the merge with the message "Merge cloud-math-4 (CLOUD-MATH-4's bridges 160, 161,
   162) into master (order MERGE-4)", naming the two resolved files.
5. **The cloud session's two files to the lane, then `incoming/` out.** First `ds_list lean/CLOUD-MATH-4/`: if
   `report.md`, `data/cloud-report.md` or `data/cloud-review-1.md` already exists, stop. Copy both byte for byte
   through the drop folder:
   `incoming/REPORT.md` as `/opt/datasphere/drop/cloud-report.md` and `incoming/reviews/review-1.md` as
   `/opt/datasphere/drop/cloud-review-1.md`, then `ds_copy_in` each (project `lean`, job `CLOUD-MATH-4`, with
   its sha256; they land in `lean/CLOUD-MATH-4/data/`), then `ds_move` `lean/CLOUD-MATH-4/data/cloud-report.md`
   to `lean/CLOUD-MATH-4/report.md`; check each lane copy with `ds_hash` against the hashes above; a reply whose path differs from the one named is a stop. Then
   `git rm -r incoming`, `git diff --cached --name-status` showing exactly those two deletions; commit.
6. **Documents.** HANDOFF section 1: a dated paragraph after LEAN-37's for CLOUD-MATH-4 and MERGE-4 (the three
   bridges by name, module and row, each module's theorem-constant count from round 77, the counts expected
   at G as predictions "to be re-measured by its gates"); ROADMAP section 1.32 for the three bridges, in
   1.31's form. One commit: this is G. Then `python3 tools/compile_rules.py drift records/rules.toml
   HANDOFF.md` (PASS).
7. **Expected results,** one file in `~/lean/merge4-checks/` written before step 8, its sha256 in the report:
   build 4196 jobs, 0 warnings; AxiomGate PASS 3844 (3827 + 3683 − 3666); check_sorry and check_records PASS
   143; VacuityGate PASS, its reviewed-helper count as at `3b62d24` (both branches added none);
   `run_vacuity_tests.py` as in `~/lean/lean37-checks/G-vacuity-tests.out`; banned scan PASS over 143 files and the root; whole-library witness
   gate PASS, OK 195 (189 + 6), copy-error 0; `witness_gate_tests.py` as in `~/lean/lean37-checks/G-witness-tests.out`;
   root closure 5732 modules (`~/lean/lean37-checks/G-modcount.out`'s count plus 3; the three modules import
   only library modules already in the closure: put `grep '^import'` of the three files in this file); type dump `removed=0 changed=0 proof_only=0`, `added=` the cloud modules' `thm` and `def`
   constants (count them from a file importing the three modules, as LEAN-37's step 5 did); gate 7 ALL PASSED,
   143 modules, 3844 theorems, its planted fault named; drift PASS.
8. **Gates at G,** each beside its expected result, cited from its saved output: `lake build`; `lake env lean
   tools/AxiomGate.lean`; `python3 -I tools/check_sorry.py`; `python3 -I tools/check_records.py`; `lake env lean
   tools/VacuityGate.lean`; `python3 -I tools/run_vacuity_tests.py`; `python3 -I tools/banned_vocab_scan.py
   ClassicalLean`; `python3 -I tools/witness_gate.py` (whole library) and `python3 -I tools/witness_gate_tests.py`;
   the module count; the type dump into `~/lean/merge4-checks/td-after.jsonl` and `g8_typediff.py diff` of the two `td-*.jsonl` there
   (a `REMOVED`, `CHANGED` or `PROOF-ONLY` line is a stop: the merge adds modules only); gate 7 last,
   `/home/dustin/lean/recheck/run-recheck.sh <G full hash> /home/dustin/lean/classical-lean-paper-crypto` under
   the 12 GB cap. Then the bridge search, `python3 -I tools/bridge_search.py --diff records/bridges/LEAN-37/
   --out ~/lean/merge4-checks/bridges/MERGE-4` (rc 1 means candidates): read each NEW import-unrelated pair and
   NEW shape that involves one of the three new modules for a theorem whose proof needs both sides; a real
   one is appended to the bridges file from row 168 (`ds_write_staging`, append, `expect_sha256` its hash when
   you read it); say how the pairs were read; write the baseline to `records/bridges/MERGE-4/`. Then the report
   tool, `lake env lean tools/UninformativeReport.lean`, once; list its `CLOSES` lines that name a theorem of the
   three new modules (a report, not a gate).
9. **Records.** Round 78 completed with the commit hashes and the counts from the saved outputs; CLAIMS closed;
   INDEX set; one records-only commit; check_records PASS at the final HEAD.
10. **Report** (`ds_file`, kind `report`): the merge and its two resolutions (the check script's output); the
    two lane copies and their hashes; each gate's expected and observed result, cited by file; the bridge diff
    and how it was read; the `CLOSES` lines for the three modules (or "none"); misses; the push command as one
    line, not run:
    `cd ~/lean/classical-lean-paper-crypto && git push origin merge-4:master && git push github merge-4:master`.
11. **Push-review file** (subdir `data`, name `MERGE-4-push-review.txt`), by one script, each command with its
    full output: `git rev-parse HEAD`; `git status --porcelain`; both remotes' master (still `3b62d24`); `git
    log --first-parent --name-status --format='== %h %cI %s' 3b62d24..HEAD` (files under `records/bridges/` as a
    count); `git log -1 --format='%H %P' <merge commit>` (parents RF and `91d98e790d38b0118ac66a4ee444ac7267b083bb`); `git merge-base --is-ancestor
    91d98e790d38b0118ac66a4ee444ac7267b083bb HEAD` with its exit code (0); `git diff --name-only 91d98e7 <G> -- ClassicalLean ClassicalLean.lean
    tools .github records/rules.toml ':(glob)lakefile*' lake-manifest.json lean-toolchain` (exactly LEAN-37's five
    modules); `git diff -U0 3b62d24 HEAD -- records/CLAIMS.md records/orders/INDEX.md` (LEAN-37's row changed by the
    push note, the CLOUD-MATH-4 and MERGE-4 rows added); `git diff --name-status
    3b62d24 <G>` (expected: the three modules A, `ClassicalLean.lean` M, `HANDOFF.md` M, `ROADMAP.md` M, and
    under `records/` only); `git diff -U0 3b62d24 <G> -- ClassicalLean.lean ClassicalLean | grep '^-' | grep -v
    '^---' || true` (nothing); `git diff -U0 3b62d24 <G> -- ClassicalLean.lean` (exactly three `+import` lines);
    `git ls-tree -r <G> incoming | wc -l` (0); the type-dump `DIFF` line; the whole-library `WITNESSGATE` line
    with its time; gate 7's summary lines; the `reduceBool`-family and `(config *:=` greps over
    `ClassicalLean/` (nothing); `grep -rnwE 'native_decide|implemented_by|admit|sorry|axiom|set_option'` on the
    three new modules (no hit outside a comment or docstring; each hit quoted and read); `git diff --name-only <G> HEAD` (only `records/`). Then stop: claude-ai
    reviews it before Dustin pushes.

## Done means

Branch `merge-4` from `3b62d24`, clean, nothing pushed: RF, the merge commit (second parent `91d98e7`), the
`incoming/` removal, the documents commit (G), records-only commits after it; the two conflicts resolved and
checked by script; the two cloud files in the lane with matching hashes; every gate of step 8 as expected or
each miss reported; the report and the push-review file in `lean/MERGE-4/`, hashes matching yours. Then tell
Dustin in a few plain sentences what was merged and checked, defining any technical term the first time, and
give the two files' hashes and the push command.

## Not in this order

LEAN-38 (the pair-by-pair reads), TWINS-1, GATE-2, the follow-ups list; any push; deleting the `cloud-math-4`
branch (Dustin's call, after the push).
