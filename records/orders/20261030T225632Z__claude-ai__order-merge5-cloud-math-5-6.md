# MERGE-5 order: cloud-math-5 and cloud-math-6 (ten bridges) into master

For a plain Claude Code session on DSMain, as dustin, in tmux `cc`. Written by claude-ai on 2026-10-30 in
Project LEAN, to the lighter procedure (store row 20261026-063), on MERGE-4's pattern (its order `5b87ced4`,
its report `f4f74625`, its close `2e3d97ac`, claude-ai's review `54dceaa1`). One cold pass on helios
(`~/merge5-review-1/out1/review.md` 6f701419: PASS WITH FINDINGS, F1 and F2 MAJOR, F3 to F10 MINOR, all applied here;
F3 was an artifact of claude-ai's measuring script, two greps numbering lines from different starts, settled by
`facts2.out`: HANDOFF holds one MERGE-4 header).

**When to start.** Now, outside the night window that `~/lean/vacuity4-checks/scripts/ev.sh`'s header names
(no Lean run from 01:45 to 05:45). Do not start a Lean run that is not expected to end before 01:45 by the
times below; if the window comes, stop at a clean point, say so, and go on when Dustin says to.
About 2.5 hours; the two long gates take about 55 minutes (MERGE-4's whole-library witness gate 1708.5 s over
143 modules, gate 7 1412 s; ten more modules here).

**Launch check.** This session was started with `CLAUDE_CODE_DISABLE_AUTO_MEMORY=1`. Print it first; if it is
not `1`, stop and say so.

## Goal

Merge GitHub's branches `cloud-math-5` and `cloud-math-6` (five new modules each, orders CLOUD-MATH-5 and
CLOUD-MATH-6, all ten bridges landed) into master on branch `merge-5`, one after the other, with every
conflict resolved by script, each cloud session's report and review copied to the lane and `incoming/` taken
out of the tree after each merge, every library-wide gate the cloud could not run run here, HANDOFF and
ROADMAP entries, records, and a push-review file. Dustin pushes after claude-ai checks that file.

## What is already true (measured by claude-ai, 2026-10-30, 18:47 to 18:56 EDT, on DSMain over ssh from helios; the scripts and outputs are on helios in /home/dustin/merge5-draft/: check.out a309fc3b, facts.out ee1baf4b, facts2.out a896138b)

- Master is `8631a8d3c4316d85c78df697436b0245fa24cf1b` on both remotes (MERGE-4, pushed by Dustin 2026-10-30
  16:23:50 EDT; store rows 20261030-002, -007); its CI run 41122857984: `completed`, `success`, headSha `8631a8d…`
  (`gh run view`, facts2.out; step 1 reads it again). The worktree
  `~/lean/classical-lean-paper-crypto` is on branch `merge-4` at `8631a8d`, porcelain empty.
- GitHub's `cloud-math-5` is `d36e20a55c633b371e6aacd2bb144f7d913b734f`, 9 commits on `8631a8d`; CI run
  41137467872 success. Against `8631a8d` it adds `ClassicalLean/Probability/HolmInsideStepUp.lean`,
  `ClassicalLean/Probability/CorrelationBound.lean`, `ClassicalLean/Statistics/PinskerTest.lean`,
  `ClassicalLean/Analysis/HeunRichardson.lean`, `ClassicalLean/Analysis/HeunEulerMaclaurin.lean`, five import
  lines at the end of `ClassicalLean.lean`'s import block (in that order), its order copy
  `records/orders/20261030T211529Z__claude-ai__order-cloudmath5-holm-correlation-pinsker-heun-richardson-euler-maclaurin.md`,
  round 79 `records/rounds/20261030T211530Z__round-79-holm-correlation-pinsker-heun-richardson-euler-maclaurin.md`,
  one row at the bottom of each of `records/orders/INDEX.md` and `records/CLAIMS.md` and no other change to
  either (`diff`: `79a80` in INDEX, `71a72` in CLAIMS, the CLOUD-MATH-5 rows), and `incoming/` with exactly
  `incoming/REPORT.md` (11915 bytes, sha256 `a24d4fbaf8186bb860928423384c8c2259ede624bdef16a54a94bfe0eee527f8`) and
  `incoming/reviews/review-1.md` (23135, `b89a78be6dbcc54aa5ba6d7e5f41e34841fed124a3b7815dc8d49cf082c91d9e`).
  Nothing under `tools/`, `.github/`, the lake files or `lean-toolchain`.
- GitHub's `cloud-math-6` is `19cbbe7fa310f87628a3dadb25ad80a0fb7ce628`, 9 commits on `8631a8d`; its CI run
  41139926284 was in progress at 18:47 EDT (step 1 reads it). Against `8631a8d` it adds
  `ClassicalLean/Probability/UrnVille.lean`, `ClassicalLean/Probability/RuinConditional.lean`,
  `ClassicalLean/Probability/RuinDivisibility.lean`, `ClassicalLean/Probability/RuinChain.lean`,
  `ClassicalLean/Probability/KolmogorovSmirnov.lean`, five import lines at the end of the import block (in that
  order), its order copy
  `records/orders/20261030T212345Z__claude-ai__order-cloudmath6-urn-ville-ruin-conditional-divisibility-chain-kolmogorov-smirnov.md`,
  round 80 `records/rounds/20261030T212346Z__round-80-urn-ville-ruin-conditional-divisibility-chain-kolmogorov-smirnov.md`,
  one row at the bottom of INDEX and of CLAIMS (`79a80`, `71a72`, the CLOUD-MATH-6 rows), and `incoming/` with
  exactly `incoming/REPORT.md` (9854, `2f311d02983d70ad4c1f2c1cf9392724f29013a63827158c3e3c290946cda326`) and
  `incoming/reviews/review-1.md` (11681, `06e44e8e2ba2688d7f94b6a94c02b1add93ff518e39a0c10d1679bc08b2e89fd`).
  Nothing under `tools/`, `.github/`, the lake files or `lean-toolchain`.
- The ten modules import only library modules (each its table's two; 20 import lines, 17 distinct modules),
  and each of the 17 is an `import` line of `ClassicalLean.lean` at `8631a8d` (facts2.out). That file has 174
  lines, 143 imports, the last at line 149.
  The banned-identifier greps on all ten files: nothing.
- claude-ai's trial merge onto `8631a8d` (a scratch worktree, removed): `cloud-math-5` merged with no
  conflict; then `cloud-math-6` gave CONFLICT in `ClassicalLean.lean` (the import block's tail: five lines
  each), `records/orders/INDEX.md`, `records/CLAIMS.md` (one row each) and, because both add them,
  `incoming/REPORT.md` and `incoming/reviews/review-1.md`. This order removes `incoming/` between the two
  merges, so `cloud-math-6`'s `incoming/` comes in as a plain addition.
- The cloud sessions' own end checks (their reports, read from Dustin's screenshots 18:46 EDT): each build
  4201 jobs (4196 + 5), 0 warnings; AxiomGate 3862 (3844 + 18, CLOUD-MATH-5) and 3896 (3844 + 52,
  CLOUD-MATH-6); check_sorry and check_records PASS 148 each; VacuityGate PASS; witness gate on its five
  modules OK 7 (CLOUD-MATH-5) and OK 6 (CLOUD-MATH-6); drift PASS.
- At `8631a8d` (its library code is MERGE-4's G `7841158`; MERGE-4's files in `~/lean/merge4-checks/`): build
  4196 jobs; AxiomGate 3844; type dump 4363 records (`CHECK records=4363 thm=3844 def=519`); whole-library
  witness gate OK 195, copy-error 0, 1708.5 s; `run_vacuity_tests.py` 89 tests, 47 flagged, 0 mismatches;
  `witness_gate_tests.py` 119 cases, 0 mismatches; gate 7 ALL PASSED, 1412 s; root closure 5732 modules;
  VacuityGate 1 reviewed helper. `HANDOFF.md` sha256
  `543f27e861f64ba87c35aa06fdc884812116587f4d98288d3588bdddc03db00a` (1521 lines; section 1's last dated
  paragraph MERGE-4's, line 573, the only `**Dated 2026-10-28 UTC (orders CLOUD-MATH-4` header in the file); `ROADMAP.md` `d967919b849ac6b5015a1235194b5bf29a3931dc6189efbf8173363818ac9ac6`
  (last section 1.32, line 978); `records/rules.toml` `2b5fb47dc4751d93171969649f9dc4f7b7e1233cdbc36bb06713c20e23bb0359`.
  The last round on master is 78; the clouds bring 79 and 80; this order's is 81. The last rows of INDEX and
  CLAIMS on master are MERGE-4's. The bridge baseline is `records/bridges/MERGE-4/`; the bridges file ends at
  row 167.
- Lane folders `lean/CLOUD-MATH-5/` and `lean/CLOUD-MATH-6/` hold `order.md` and an empty `data/`; no
  `report.md`.

## Scope

- Branch `merge-5` from `8631a8d`. Nothing pushed. No sudo. Never rebase; each merge is one `--no-ff` merge
  commit.
- You may change: what the two merges bring; `records/` (the resolved files, this order's copy, round 81,
  MERGE-4's push on its rows, the new bridge baseline); `incoming/` (removed, twice); `ClassicalLean.lean`
  only as step 6's resolution; `HANDOFF.md` section 1 (one dated paragraph after MERGE-4's); `ROADMAP.md` (a
  section 1.33 after 1.32, in its form); the bridges file (a real bridge only, from row 168). No existing module
  changes. Needing to change anything else is a stop.
- Your files: `~/lean/merge5-checks/`. Lane writes through the connector: the report (`ds_file`, project
  `lean`, job `MERGE-5`, kind `report`), the push-review file (subdir `data`, name `MERGE-5-push-review.txt`),
  and the four cloud copies (steps 5 and 7). A file over a few kilobytes goes byte for byte through DSMain's
  drop folder: copy it to `/opt/datasphere/drop/<name>`, then `ds_copy_in` with its sha256 (it lands in
  `<job>/data/<name>`). Copying out of the lane with `cp` is denied; write a lane file you need from the
  connector's reply and check it by hash (MERGE-4's trap 1). Lane paths through the connector are
  `inbox/threads/staging/lean/…` (MERGE-4's trap 2).
- Off limits as in every order: `~/lean/classical-lean`, every earlier order's folder (read only),
  `~/api-credit/` and `/tmp/claude-ai-*` (read only), `/data/api-credit/`, Dustin's
  `~/.config/classical-lean/banned-terms` (never print or copy it), every GitHub branch (fetch only).
- Lean runs: one at a time, under the 12 GB cap, `~/.elan/bin` on `PATH`, `pgrep -ax lean` empty before each.
- Every script you write is a file in `~/lean/merge5-checks/`, run with `python3 -I <file>` or `bash <file>`;
  never a heredoc or standard input (MERGE-4's misses 1 and 2). The library's own tools and
  `run-recheck.sh` run from where they are.

## The work

1. **Check.** Launch variable; `git fetch origin`; `git fetch github cloud-math-5 cloud-math-6`;
   `git ls-remote origin master` and `git ls-remote github master` both `8631a8d…`; `git rev-parse
   github/cloud-math-5` is `d36e20a55c633b371e6aacd2bb144f7d913b734f` and `git rev-parse github/cloud-math-6` is
   `19cbbe7fa310f87628a3dadb25ad80a0fb7ce628`; porcelain empty; HANDOFF, ROADMAP and rules.toml sha256 as above;
   the four `incoming/` files' sizes and sha256 by `git show <commit>:<path>`, as above;
   `git show 8631a8d:HANDOFF.md | grep -c '^\*\*Dated 2026-10-28 UTC (orders CLOUD-MATH-4'` is `1`;
   `gh run view 41122857984 -R datasphereai/classical-lean --json status,conclusion,headSha` is `completed`,
   `success`, headSha `8631a8d3c4316d85c78df697436b0245fa24cf1b`; `gh run view 41139926284 -R datasphereai/classical-lean --json
   status,conclusion,headSha` has headSha `19cbbe7fa310f87628a3dadb25ad80a0fb7ce628` and, once `status` is
   `completed` (wait up to 20 minutes while it is not, then read again), `conclusion` `success`; anything else
   is a stop. If anything differs, stop.
2. **Before** (on a clean `8631a8d`): copy `~/lean/merge4-checks/TypeDumpPI.lean` (sha256
   `1fcb69f41ddbd35f84862521d2ead5946a0bd52caf5f60b6d10e966cfd9776ff`) and `~/lean/merge4-checks/g8_typediff.py`
   (`371eda9a2e5065abaa8f36bac9872d0f15e7bade72a248d5f0f88f20b4eacb71`; both equal to lane
   `inbox/threads/staging/lean/LEAN-33/scripts/TypeDumpPI.lean` and `…/g8-typediff.py`, facts2.out) into
   `~/lean/merge5-checks/` with `cp`, checking each hash; `lake build` (4196 jobs); `lake env lean
   ~/lean/merge5-checks/TypeDumpPI.lean > ~/lean/merge5-checks/td-before.out`, its lines starting `{` in
   `~/lean/merge5-checks/td-before.jsonl`; `python3 -I ~/lean/merge5-checks/g8_typediff.py check
   ~/lean/merge5-checks/td-before.jsonl`: 4363 records.
3. **Records first** (RF). `git switch -c merge-5 8631a8d`; check `git rev-parse HEAD` and `git branch
   --show-current`. One commit, no `.lean` file: this order's copy in `records/orders/`; its INDEX row and
   CLAIMS row at the bottom (`| MERGE-5 |`, in MERGE-4's rows' form); round 81's fragment naming the ten
   modules by full path; and MERGE-4's push recorded in MERGE-4's two rows. The note is
   `; pushed by Dustin: master 8631a8d on both remotes, CI run 41122857984 green`. In INDEX it goes
   immediately before the text `` | `a34e1cb` (records)`` (once in the whole file, measured). In CLAIMS it goes
   immediately before the final ` |` of MERGE-4's row: anchor on the line ending `not pushed, the push is
   Dustin's after claude-ai's push review |` (that phrase occurs 9 times in the file, but with ` |` at the end
   of a line only once, in MERGE-4's row, measured); the row keeps its closing ` |`, as LEAN-37's did. Check by script before the commit: each row changed only by that
   insertion, the note once, everything else in both files equal to `8631a8d`'s apart from the two new MERGE-5
   rows at the bottom. check_records PASS.
4. **First merge: `cloud-math-5`.** Check (e): for each of INDEX and CLAIMS, `diff <(git show
   8631a8d:<file>) <(git show d36e20a55c633b371e6aacd2bb144f7d913b734f:<file>)` is exactly one added line after
   the last line, which starts `| CLOUD-MATH-5 |` (INDEX) or holds ``executing order `CLOUD-MATH-5` `` (CLAIMS);
   anything else is a stop. Then `git merge --no-ff --no-commit d36e20a55c633b371e6aacd2bb144f7d913b734f`.
   Expected: rc 1, CONFLICT in exactly `records/CLAIMS.md` and `records/orders/INDEX.md` (RF's rows against
   the cloud's). Resolve each by one script, `resolve.py <file> <ours-commit> <theirs-commit>`: the resolved
   file is ours (RF) with its last line removed, then theirs' last line, then ours' last line. Check by a
   second script, `resolve_check.py`: (a) one more line than ours; (b) deleting theirs' row gives ours byte for
   byte, and the deleted line equals `git show <theirs>:<file> | tail -1` byte for byte; (c) its last three
   lines are MERGE-4's row (with the push), CLOUD-MATH-5's row and MERGE-5's row; (d) the lines above MERGE-4's
   row equal those in `8631a8d`'s file. Its control: a planted fault in a copy of each resolved file must fail.
   Then `git diff --cached --name-status` against RF lists exactly: the five modules (A), `ClassicalLean.lean`
   (M), the two `incoming/` files (A), the cloud's order copy and round 79 (A), and the two resolved files (M);
   anything else is a stop. Commit: "Merge cloud-math-5 (CLOUD-MATH-5's bridges 155, 158, 164, 166, 167) into
   master (order MERGE-5)", naming the two resolved files.
5. **CLOUD-MATH-5's two files to the lane, then `incoming/` out.** First `ds_list
   inbox/threads/staging/lean/CLOUD-MATH-5/`: if `report.md`, `data/cloud-report.md` or `data/cloud-review-1.md`
   exists, stop. Copy `incoming/REPORT.md` as `/opt/datasphere/drop/cloud-report.md` and
   `incoming/reviews/review-1.md` as `/opt/datasphere/drop/cloud-review-1.md`, `ds_copy_in` each (project
   `lean`, job `CLOUD-MATH-5`, its sha256), then `ds_move` `…/CLOUD-MATH-5/data/cloud-report.md` to
   `…/CLOUD-MATH-5/report.md`; check each lane copy with `ds_hash` against the hashes above; a reply whose
   path differs from the one named is a stop. Then `git rm -r incoming`, `git diff --cached --name-status`
   showing exactly those two deletions; commit.
6. **Second merge: `cloud-math-6`.** Check (e) as in step 4 for `19cbbe7fa310f87628a3dadb25ad80a0fb7ce628`
   (the CLOUD-MATH-6 rows). Then `git merge --no-ff --no-commit 19cbbe7fa310f87628a3dadb25ad80a0fb7ce628`.
   Expected: rc 1, CONFLICT in exactly `ClassicalLean.lean`, `records/CLAIMS.md` and `records/orders/INDEX.md`;
   `incoming/` comes in as two additions. INDEX and CLAIMS: `resolve.py` with ours = HEAD; `resolve_check.py`
   with (c) as the last four lines MERGE-4's, CLOUD-MATH-5's, CLOUD-MATH-6's and MERGE-5's rows and (b) against
   HEAD's file. `ClassicalLean.lean`: by a script, `resolve_root.py`, the resolved file is HEAD's with
   `19cbbe7`'s five added import lines (`git diff -U0 8631a8d 19cbbe7 -- ClassicalLean.lean`, the `+import`
   lines, in their order) inserted right after HEAD's last `import` line; checked by a second script: the resolved file is, byte for byte, `8631a8d`'s lines 1 to 149, then
   CLOUD-MATH-5's five import lines, then CLOUD-MATH-6's five, then `8631a8d`'s lines 150 to 174 (so `git diff
   -U0 8631a8d` is the one hunk `@@ -149,0 +150,10 @@`), and holds no conflict marker; lines are matched as
   `^import `. Its control: a planted fault must fail. Then
   `git diff --cached --name-status` against HEAD lists exactly: the five modules (A), `ClassicalLean.lean`
   (M), the two `incoming/` files (A), the cloud's order copy and round 80 (A), and the two records files (M);
   anything else is a stop. Commit: "Merge cloud-math-6 (CLOUD-MATH-6's bridges 154, 156, 157, 159, 165) into
   master (order MERGE-5)", naming the three resolved files.
7. **CLOUD-MATH-6's two files to the lane, then `incoming/` out,** as step 5 with job `CLOUD-MATH-6` and its
   hashes.
8. **Documents.** HANDOFF section 1: one dated paragraph after MERGE-4's for CLOUD-MATH-5, CLOUD-MATH-6 and
   MERGE-5 (the ten bridges by name, module and row; each module's theorem-constant count from rounds 79 and
   80; the counts expected at G as predictions "to be re-measured by its gates"); ROADMAP section 1.33 for the
   ten bridges, in 1.32's form. One commit: this is G. Then `python3 -I tools/compile_rules.py drift
   records/rules.toml HANDOFF.md` (PASS).
9. **Expected results,** one file `~/lean/merge5-checks/expected.txt`, written before step 10, its sha256 in
   the report: build 4206 jobs (4196 + 10), 0 warnings; AxiomGate PASS 3914 (3844 + 18 + 52); check_sorry and
   check_records PASS 153; VacuityGate PASS, 1 reviewed helper (neither branch changed `tools/`);
   `run_vacuity_tests.py` as in `~/lean/merge4-checks/G-vacuity-tests.out`; banned scan PASS over 153 files and
   the root; whole-library witness gate PASS, OK 208 (195 + 7 + 6), copy-error 0; `witness_gate_tests.py` as in
   `~/lean/merge4-checks/G-witness-tests.out`; root closure 5742 modules (`~/lean/merge4-checks/G-modcount.out`'s
   5732 plus 10; put `grep '^import'` of the ten files in this file); type dump `removed=0 changed=0
   proof_only=0`, `added=` the ten modules' `thm` and `def` constants (count them from a file importing the ten
   modules, as MERGE-4 did), of which the `thm` records must be 70 (18 + 52, the clouds' AxiomGate counts;
   at MERGE-4 the dump's `thm` equalled AxiomGate's count), any other value a miss to report; gate 7 ALL PASSED, 153 modules, 3914 theorems, its planted fault named; drift PASS.
10. **Gates at G,** each beside its expected result, cited from its saved output: `lake build`; `lake env lean
    tools/AxiomGate.lean`; `python3 -I tools/check_sorry.py`; `python3 -I tools/check_records.py`; `lake env lean
    tools/VacuityGate.lean`; `python3 -I tools/run_vacuity_tests.py`; `python3 -I tools/banned_vocab_scan.py
    ClassicalLean`; `python3 -I tools/witness_gate.py` (whole library) and `python3 -I tools/witness_gate_tests.py`;
    the module count; the type dump into `~/lean/merge5-checks/td-after.jsonl` and `g8_typediff.py diff` of the two
    `td-*.jsonl` there (a `REMOVED`, `CHANGED` or `PROOF-ONLY` line is a stop: the merges add modules only); gate 7
    last, `/home/dustin/lean/recheck/run-recheck.sh <G full hash> /home/dustin/lean/classical-lean-paper-crypto`
    under the 12 GB cap. Then the bridge search, `python3 -I tools/bridge_search.py --diff records/bridges/MERGE-4/
    --out ~/lean/merge5-checks/bridges/MERGE-5` (rc 1 means candidates): read each NEW import-unrelated pair and
    NEW shape that involves one of the ten new modules for a theorem whose proof needs both sides; a real one
    is appended to the bridges file from row 168 (`ds_write_staging`, append, `expect_sha256` its hash when you
    read it); say how the pairs were read, by a saved script; write the baseline to `records/bridges/MERGE-5/`.
    Then the report tool, `lake env lean tools/UninformativeReport.lean`, once; list its `CLOSES` lines that name
    a theorem of the ten new modules (the lines are not at the start of a line: MERGE-4's trap 3), a report, not
    a gate.
11. **Records.** Round 81 completed with the commit hashes and the counts from the saved outputs; CLAIMS
    closed; INDEX set; one records-only commit; check_records PASS at the final HEAD.
12. **Report** (`ds_file`, kind `report`): the two merges and their resolutions (the check scripts' outputs
    and their controls); the four lane copies and their hashes; each gate's expected and observed result, cited
    by file; the bridge diff and how it was read; the `CLOSES` lines for the ten modules (or "none"); misses;
    the push command as one line, not run:
    `cd ~/lean/classical-lean-paper-crypto && git push origin merge-5:master && git push github merge-5:master`.
13. **Push-review file** (subdir `data`, name `MERGE-5-push-review.txt`), by one script, each command with its
    full output: `git rev-parse HEAD`; `git status --porcelain`; both remotes' master (still `8631a8d`); `git
    log --first-parent --name-status --format='== %h %cI %s' 8631a8d..HEAD` (files under `records/bridges/` as a
    count); `git log -1 --format='%H %P'` of each merge commit (parents: RF and `d36e20a…`; the step 5 commit and
    `19cbbe7…`); `git merge-base --is-ancestor` of `d36e20a…` and of `19cbbe7…` against HEAD with exit codes (0);
    `git diff --name-only <commit> <G> -- ClassicalLean tools .github records/rules.toml ':(glob)lakefile*'
    lake-manifest.json lean-toolchain` for each cloud commit (exactly the other branch's five modules);
    `git diff -U0 8631a8d HEAD -- records/CLAIMS.md records/orders/INDEX.md` (MERGE-4's row changed by the push
    note; the CLOUD-MATH-5, CLOUD-MATH-6 and MERGE-5 rows added); `git diff --name-status 8631a8d <G>` (expected:
    the ten modules A, `ClassicalLean.lean` M, `HANDOFF.md` M, `ROADMAP.md` M, and under `records/` only);
    `git diff -U0 8631a8d <G> -- ClassicalLean.lean ClassicalLean | grep '^-' | grep -v '^---' || true`
    (nothing); `git diff -U0 8631a8d <G> -- ClassicalLean.lean` (exactly ten `+import` lines);
    `git ls-tree -r <G> incoming | wc -l` (0); the type-dump `DIFF` line; the whole-library `WITNESSGATE` line
    with its time; gate 7's summary lines; the `reduceBool`-family and `(config *:=` greps over
    `ClassicalLean/` (nothing); `grep -rnwE 'native_decide|implemented_by|admit|sorry|axiom|set_option'` on the
    ten new modules (no hit outside a comment or docstring; each hit quoted and read); `git diff --name-only <G>
    HEAD` (only `records/`). Then stop: claude-ai reviews it before Dustin pushes.

## Done means

Branch `merge-5` from `8631a8d`, clean, nothing pushed: RF, the first merge commit (second parent `d36e20a`),
its `incoming/` removal, the second merge commit (second parent `19cbbe7`), its `incoming/` removal, the
documents commit (G), records-only commits after it; every conflict resolved and checked by script with a
failing control; the four cloud files in the lane with matching hashes; every gate of step 10 as expected or
each miss reported; the report and the push-review file in `lean/MERGE-5/`, hashes matching yours. Then tell
Dustin in a few plain sentences what was merged and checked, defining any technical term the first time, and
give the two files' hashes and the push command.

## Not in this order

LEAN-38 (the pair-by-pair reads), TWINS-1, GATE-2, the follow-ups list; any push; deleting the `cloud-math-4`,
`cloud-math-5` or `cloud-math-6` branches (Dustin's call, after the push).
