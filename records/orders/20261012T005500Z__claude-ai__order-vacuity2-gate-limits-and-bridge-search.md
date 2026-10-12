<!-- Written on 2026-10-11 by claude-ai; copied verbatim on 2026-10-12 (UTC) by Claude Code session_011EbLXaTFXVhmDqos8VbGfe on DSMain from /opt/datasphere/lane/inbox/threads/staging/VACUITY-2-order.md (sha256 cf32f88b53c297d0953807f639a52e1bf4d19b08109e0951635ce70e84ff100f, checked by sha256sum before this copy; equal to the hash in Dustin's prompt), as Dustin ordered in chat. Written before any tool or gate file changed, per records/README.md rule 2. -->

# VACUITY-2 order: close the vacuity gate's open limits (items 72 to 78)

Written 2026-10-11 by claude-ai for a plain Claude Code session on DSMain, as dustin, from step 1
of OPEN-WORK-20261011-r2.md (sha256 9a45f744...). Every lane file named here is in
/opt/datasphere/lane/inbox/threads/staging/. Reports and plans go to the lane through
ds_write_staging, since the lane is read-only on disk for you.

Review: one cold review by a fresh subagent that had not seen it written, PASS WITH FINDINGS
(0 BLOCKER, 5 MAJOR, 10 MINOR), every finding applied; a second pass by the same reviewer is
recorded at the end ("Revisions"). Not reviewed, because they live only on DSMain: the repo files
(`tools/VacuityGate.lean`, the test runner, `check_records`, `banned_vocab_scan.py`) and
`run-recheck.sh`. Where this order rests on one of them, check it before relying on it.

## Goal

Make `tools/VacuityGate.lean` close the gaps VACUITY-1 left open, as items 72 to 78 of
MATH-PLAN-library-2.md state them, before any new module is written: LEAN-27 onward is checked
against the gate this order leaves. Also put in place Dustin's two additions of 2026-10-11 18:06
EDT (decision A of the board), which every later order inherits.

The vacuity gate is the check that fails a theorem whose statement proves nothing beyond its own
hypotheses (a *vacuous* theorem). A *flag* is its verdict that a theorem is vacuous. The gate
today has two tests: the *fixed test*, which builds a proof term for each flag, and the *old case
3*, which matches shapes and builds none.

## Scope

- Branch `vacuity-2`, made from `d2cba27`. Nothing pushed. No sudo.
- Files you may change: `tools/VacuityGate.lean`, `tools/VacuityGateTests.lean`,
  `tools/run_vacuity_tests.py`, `tools/vacuity_reviewed.txt`, `tools/vacuity_reviewed_tests.txt`,
  a new `tools/bridge_search.py`, `records/` (the order copy, INDEX, CLAIMS, the round fragment,
  a new `records/bridges/` folder), and any repo document that lists what the gate checks or its
  limits (work step 9). Before adding `records/bridges/`, read `tools/check_records.py` and make
  sure it accepts files there; if it would not, say so and put the baseline where it does.
- No file under `ClassicalLean/` changes. If a gate change seems to need one, stop and report.
- Nothing under `~/trading` or `~/lean/recheck` is edited (`run-recheck.sh` is run, as gate 7).
- `~/.config/classical-lean/banned-terms` is Dustin's file: never edit it, and never copy its
  patterns into a record, a lane file or a commit.
- The night window. `lean-nightly.timer` and `datasphere-backup.sh` both start at 03:30 on this
  30 GiB box. First run `systemctl --user list-timers`, `systemctl list-timers --all` and
  `crontab -l`, and note every job that fires between 03:00 and 06:00. Then start nothing that loads the library (`lake build`, any
  `lake env lean`, the test runner, the plan's check script, `bridge_search.py`, gate 7) between
  03:15 and 04:30 EDT, or within 30 minutes before any other timer you found there.
- Memory. Every run that loads the whole library (the gate on the library, the plan's checks with
  `--lean`, `bridge_search.py`, gate 7) runs under
  `systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0 <command>`, the cap RECHECK-1
  used. A run killed by that cap is a stop: report it.
- If you make a plan, write it to the lane as VACUITY-2-PLAN.md (then -PLAN-2, never overwriting)
  and report its sha256.

## Check, then read

Check these sha256s first; if any differs, stop and say which:
- this order: the value in Dustin's prompt;
- MATH-PLAN-library-2.md `6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166`;
- MATH-PLAN-library-2-checks.py `92eedbc6598361a06a50bdf3a1b4fa1698c1d1d7a3dfe783cc79dd9c1c38307e`;
- MATH-PLAN-library-2-checks.out `9b4e4cf12e86178dbef44f319f27c3ce439bdc8aed45d573625065be56f98c7a`;
- VACUITY-1-report.md `db4d8e72debaa707dd0d5b7a355f945b20879803ef3ee93ff2644e2cbdea22a5`;
- LEAN-16-order.md `d494728c561a922b1227587395f9650f33dd3182791620e7a0d0fb6469f3120e`.

Then read: MATH-PLAN-library-2.md section 5 (the "Order VACUITY-2" table and the paragraph after
it), section 8 (the per-batch method), section 9 (VACUITY-2's steps) and section 2's paragraph
"Connections, by a mechanical search"; VACUITY-1-report.md in full; the "Known traps" section of
LEAN-16-order.md; MATH-PLAN-library-2-checks.py lines 167 to 196 (`LEAN_USED`), 285 to 370
(`run_lean`, `bridge_pairs`, `import_graph`, `SHAPES`, `shape_modules`), around line 588
(`setup.worktree`), and 706 to 797 of its `main` (sections 3, 4 and 4b). In the repo:
`tools/VacuityGate.lean`, `tools/VacuityGateTests.lean`, `tools/run_vacuity_tests.py`, both
`tools/vacuity_reviewed*.txt`, `tools/check_records.py`. Nothing more is needed.

## Setup

1. `cd ~/lean/classical-lean-paper-crypto && git fetch origin`. origin/master and
   `git ls-remote github master` must both be `d2cba27`, and `git status` clean. If not, stop and
   report. Then `git switch -c vacuity-2 d2cba27`.
2. Evidence folder `~/lean/vacuity2-checks/`, with `evidence.log` kept as VACUITY-1 kept its own
   (time, label, rc, prediction, command). Every prediction file is hashed when written, before
   the run it predicts, and the hash goes into `evidence.log`.
3. First build, predicted rc 0, 4166 jobs, 0 warnings: `nice -n 19 lake build`.
4. Baseline of the plan's checks. Run MATH-PLAN-library-2-checks.py with `--lean` as the plan's
   section 2 shows (a Mathlib master clone at `2da3ab0a`, which also holds `5ed2965256`; reuse
   one already on DSMain if it is at that commit). Predicted: last line "232 of 232 checks hit".
   Save the output as `checks-before.out` and compare it with the lane's
   MATH-PLAN-library-2-checks.out; report any line that differs.
5. Time and memory of today's gate on the library: run `lake env lean tools/VacuityGate.lean`
   under the memory cap and `/usr/bin/time -v`, predicted PASS in about 3 minutes (VACUITY-1's
   figure). Record wall time and peak memory (maximum resident set size). If `/usr/bin/time` is
   missing, say so and record wall time with `date +%s` before and after; installing it needs
   root and is not part of this order.

## The work

1. **Records first** (plan section 8, step 2): one commit, no `.lean` file: this order's copy, its
   INDEX row, a CLAIMS row, and a round fragment that names no module (no `ClassicalLean/` file
   changes).

2. **The bridge search as a tool** (decision A, second addition; made here so every later order
   can re-run it). A *bridge* is a theorem whose proof must use two library modules that do not
   import each other, through an object they share. Write `tools/bridge_search.py`:
   - It copies, not imports, from MATH-PLAN-library-2-checks.py the `LEAN_USED` source,
     `run_lean`, `bridge_pairs`, `import_graph`, `SHAPES` and `shape_modules`, unchanged.
   - `bridge_pairs` returns only the score and the two modules of each pair. Add one function that
     recomputes, for each pair, the set of shared kept constants with the same filters
     `bridge_pairs` uses (the skip pattern, the kind split, df at most 10), and assert that its
     score for every pair equals `bridge_pairs`' score.
   - It writes two files: every import-unrelated pair that shares a kept constant (rank, score,
     module x, module y, the number of shared kept constants, the constants), and every shape
     candidate (shape, module x, module y, related or unrelated), plus a `COMMIT` file holding
     the commit it ran on.
   - `--diff OLD_DIR` compares by key only: a pair is keyed by (x, y) and a shape candidate by
     (shape, x, y), never by the whole row, since scores and ranks move for every pair whenever
     a module is added. It prints every key present now and absent from OLD_DIR, and every key
     gone, and exits 0 when there are none and 1 when there are some. Exit 1 means "candidates to
     review", not a failed gate.
   - Check it with an instrument you did not write: its pair count, its top 30 and the four ranks
     and scores that `checks-before.out` prints must be equal (2337 pairs; GlivenkoCantelli x
     NeymanPearson first at 188.7; GamblersRuin x MaximalInequality second at 121.8; FiniteGame x
     LinearProgram 17th at 66.1; MinMax x CovarianceDirections 36th at 51.4).
   - Exercise both exit codes: `--diff` against the baseline itself, predicted rc 0; and against a
     scratch copy of the baseline with one pair line deleted, predicted rc 1 naming that pair.
   - Commit the files as the baseline `records/bridges/VACUITY-1/` (the tree as VACUITY-1 left it;
     its `COMMIT` file says `d2cba27`). Every later baseline is named by its order the same way.

3. **Tests before the gate changes** (plan section 9, step 2). Add to `tools/VacuityGateTests.lean`:
   `vac_and_hyp`, `vac_iff_hyp`, `vac_irreducible`, `vac_deep_unfold`, `vac_false_hyp`,
   `real_exfalso_helper` (a deliberate "from a contradiction, anything" helper, on the test list),
   `vac_meta_helper._proof_1` (made by `addDecl`, used by nothing), and one more for item 75:
   `vac_macro_scoped`, a theorem made by a local hygienic macro, so its name carries macro scopes.
   Check in the runner that it reads the expectation from the name with the scopes erased, and
   that a theorem made by `addDecl` survives its scratch join; fix the runner if not. Rename
   `lim_and_hyp` to a `vac_` name not already taken (item 72), and `lim_false` too if you predict
   rule 5 will flag it. Write each test's predicted verdict under today's gate in a prediction
   file, hash it, run today's gate on the tests, and commit the measured table before any gate
   change, as VACUITY-1 did.

4. **Items 72 to 77**, one commit each with its tests (item 74 may share item 72's commit, as the
   plan allows). Each plan row is done as the plan states it; the notes below add to the rows and
   replace nothing, except item 77's budget, which departs from the row as its note says. Before each run, write the predicted verdicts and the predicted library result
   in `evidence.log`; after each commit, run the whole test set and the library, timed and under
   the memory cap as in setup 5.
   - Item 74: remove the dead counter and strike the "more than 4 unfoldings" limit from the
     gate's own stated limits (the docstring of `isVacuousType`). VACUITY-1-report.md is a lane
     record and is not edited; this order's report carries the new limits table.
   - Item 75: the gate change is the plan's: test theorems with macro scopes, and skip a `_proof_`
     helper with no source position only when some declaration uses it. Predict, for each of the
     three helpers used by nothing (`abs_le_of_abs_deriv_le._proof_1_8`, `_9`, `_10`), whether it
     is flagged; one that is goes on `tools/vacuity_reviewed.txt` as HELPER with its reason.
   - Item 76: every flag that comes with a proof term (the fixed test's and rule 5's) is also
     checked by the kernel. A term the kernel rejects is printed as its own verdict
     (KERNEL-REJECTED) and fails the gate, since it would mean `Meta.check` accepted a bad term.
     Predicted: none, in the tests or the library. Old case 3 builds no term, so its flags carry
     the label "old case 3 only" where no other test fired.
   - Item 77, rule 5: the plan's row says "under the per-theorem budget"; this order departs from
     it. Rule 5 runs with its own heartbeat count, as each of the two existing tests does, of at
     most 400000 heartbeats per theorem (the gate's budget before VACUITY-1), the closing tactics
     tried in the plan's order inside that count, so a slow rule 5 can never starve the fixed test
     into UNCHECKED. The 2000000 budget is unchanged; the separate count adds at most 400000 of
     work per theorem. claude-ai told Dustin so in one line on 2026-10-11, his veto open; if he
     vetoes, this order is revised before it runs. Do not change either number during the run
     without asking him in one line (LEAN-16's known trap). A theorem whose rule-5 search runs out
     is printed on its own line with its name, and the count of such theorems is added after the
     gate's existing summary text, keeping its prefix exactly ("vacuity gate PASS" or its FAIL
     form), so the nightly status shows it. Read `~/bin/lean-nightly.sh` first to see how it reads
     the gate's result, and keep it reading the same way. A run-out does not fail the gate on that
     ground alone: rule 5 is an incomplete search, and running out tells no more than finding
     nothing; Dustin's ruling that a slow theorem is never passed silently is met by the printed
     line and count. The fixed test's UNCHECKED behaviour stays as it is. Predict the number of
     rule-5 flags and of rule-5 run-outs in the library before the run, and report both with
     names. Look at each flag by hand: a deliberate one goes on the list as HELPER, any other as
     VACUOUS-PENDING with its reason (VACUITY-1's class b).
   - If the final library run takes more than 15 minutes or more than 10 GB at peak, stop before
     item 78 and report: the gate runs nightly on the same box as the backup.

5. **Item 78, the cold review of the gate as left**, before the last commit. One fresh
   general-purpose subagent, no persistent memory, its own folder `~/lean/vacuity2-checks/reviews/`,
   about 40 tool calls. Read list: the gate's diff from `d2cba27`, `tools/VacuityGateTests.lean`,
   your measured tables, VACUITY-1-report.md's limits table and cold review section, and the 24
   probe theorems of VACUITY-1's reviewer (`R1Tests.lean` under `~/lean/vacuity1-checks/reviews/`;
   if not there, `find ~/lean -name R1Tests.lean`). It may run `tools/run_vacuity_tests.py` on test
   files of its own; it runs no library gate, build, census or count, and edits nothing in the
   repository. Hash `~/.claude/agent-memory/` before and after. Its job: a real theorem the gate
   flags; a vacuous one the three tests all pass; a flag with a proof term that is not
   kernel-checked; a skip that hides a written theorem; a stated limit that is wrong; a Done-means
   line below not met. Check each finding against the source before acting; apply it or answer it
   in the report. A fix re-runs the test set and the library.

6. **Banned vocabulary** (decision A, first addition, a standing rule from this order on).
   `banned_vocab_scan.py` is measured to read only `ClassicalLean/` and `ClassicalLean.lean`
   (board, 2026-10-11 18:20 EDT); confirm that from its source. This order changes neither, so
   here it is predicted PASS, 120 files, 0 hits. The rule for every later order: if a batch needs
   a banned term for its mathematics, report the hit (file, line, and the term the mathematics
   needs) and stop; Dustin narrows that one pattern in his own file, and the exception is recorded
   in that batch's records. Write this rule into the round fragment so LEAN-27 finds it in the
   repo.

7. **The bridge search at the end** (decision A, second addition, a standing rule from this order
   on). Run `tools/bridge_search.py --diff records/bridges/VACUITY-1/` on the tree as left.
   Predicted: rc 0, no new or gone key, since no module changed. This report names the current
   baseline, `records/bridges/VACUITY-1/`, and every later report names its own current baseline
   whether or not it changed. The rule for every later order,
   also written into the round fragment:
   - re-run it against the baseline the last report names;
   - check each new import-unrelated pair by hand for a theorem whose proof needs both sides;
     import-related pairs and shape candidates are listed in the report, not reviewed;
   - a real bridge gets an item number from 154 on, ranked after item 153, the columns of the
     plan's section 7 table with its cost and its "Shared object:" line, and its own Mathlib grep
     (plan section 8, step 3 needs a search behind every row);
   - it goes into the lane file MATH-PLAN-library-2-bridges.md (the first time), then
     -bridges-2.md and on, each a whole new file carrying all earlier rows, never an overwrite;
     every later order's read list names the newest one;
   - a found bridge never enters the batch that found it; the cut is re-drawn only at a batch
     boundary, and only if a new bridge is load-bearing for a scheduled row;
   - when modules were added, commit a new baseline `records/bridges/<ORDER>/` and name it in the
     report.
   The cold-reviewed plan file itself is not edited, so its hash keeps meaning what the board and
   its review say. Decision A's words were "added to the plan's ranked list below the cut"; the
   bridges file is that list's continuation, and Dustin may veto the choice.

8. **The plan's checks after.** The script exits 1 when any check misses, so rc 1 is expected
   here. Before re-running it, write down, and hash, the multiset of (label, claim) pairs you
   expect to miss now (labels repeat, such as `bridges.rank`). The predictable ones:
   `setup.worktree` (it wants HEAD at `d2cba27`); `gate.maxUnfolds` (item 74); `gate.macro` and
   `gate.helper` (item 75); `gate.metacheck` (item 76); `gate.test.lim_and_hyp`;
   `gate.test.lim_false` if renamed; `gate.list` if the library list gained an entry;
   `gate.heartbeats` if that line changed; and any other you can name with its reason. Then run
   it. The measured multiset must equal the predicted one. The report lists them, so that LEAN-27's
   "every row line must hit" reads as every row line, with these known to differ.

9. **Documents.** If HANDOFF.md, ROADMAP.md, records/README.md or any other repo document lists
   what the gate checks or its limits, bring it in line with the gate as left. Name each file
   changed, or say none needed it.

10. **Gates, on the clean tree, predicted first** (plan section 8, step 9): `nice -n 19 lake build`
    (rc 0, 4166 jobs, 0 warnings); AxiomGate (PASS, 3158); VacuityGate as left (PASS; predict the
    number of HELPER and VACUOUS-PENDING entries and of rule-5 run-outs); check_sorry (PASS, 120);
    banned_vocab_scan (PASS, 120 files, 0 hits); check_records (PASS, 120); and gate 7, under the
    memory cap (leanchecker has reached about 28 GB uncapped):
    `systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0 ~/lean/recheck/run-recheck.sh <commit> ~/lean/classical-lean-paper-crypto`
    (predicted ALL PASSED, 4166 jobs, 120 modules 0 failed, three standard axioms, 3158, planted
    fault named). Constants, modules and jobs unchanged: 3158, 120, 4166.

11. **Report** VACUITY-2-report.md through ds_write_staging, post_sha256 compared with your own
    sha256sum. Its sections, as VACUITY-1's: in short; setup; the route taken; the test table
    (predicted and measured, under today's gate and under the gate as left, with which test or
    rule fired); the library (flags, list entries with reasons, rule-5 run-outs with names); time
    and peak memory before and after; the cold review and its findings; every limit VACUITY-1
    stated, with its status now; the bridge tool's check, both exit-code runs and the end diff;
    the plan's checks before and after, with the predicted and measured misses; the documents
    changed; the gates table; commits; misses and not reached; and the push command as one line,
    not run:
    `cd ~/lean/classical-lean-paper-crypto && git push origin vacuity-2:master && git push github vacuity-2:master`.
    Then stop.

## Done means

- Branch `vacuity-2` from `d2cba27`, clean tree, nothing pushed, no `ClassicalLean/` file changed;
  the records-first commit holds no `.lean` file.
- Every prediction file is hashed in `evidence.log` before the run it predicts.
- Every new and renamed `vac_` test is flagged, `real_exfalso_helper` comes out LISTED, and every
  VACUITY-1 test keeps its verdict, or each change is explained.
- Every fixed-test and rule-5 flag is kernel-checked; old-case-3-only flags are labelled so; no
  KERNEL-REJECTED anywhere.
- The gate's stated limits are exactly these, each said plainly in its docstring and the report:
  true but uninformative statements; contradictions rule 5's tactics do not find; a closed premise
  `decide` cannot finish (fails closed, as UNCHECKED); chained hypotheses and premises not closed
  by `rfl` or `decide`, outside a plain `∀`; a `_proof_` helper with no source position that some
  declaration uses; plus any the cold review adds. The "more than 4 unfoldings" limit is gone.
- Rule 5 runs within 400000 heartbeats per theorem; its run-outs are counted in the gate's summary
  line and named in the report.
- The cold review's findings are applied or answered.
- The bridge tool reproduces the checks' bridge numbers, its score assertion holds, both exit codes
  were exercised as predicted, and the end diff is empty.
- The round fragment carries the two standing rules (steps 6 and 7).
- The plan's checks: 232 of 232 before; afterwards, the misses equal the predicted multiset.
- Step 9 names each document changed, or says none.
- Every gate as predicted, or the miss reported; gate 7 ALL PASSED for the last commit.
- The library gate's time and peak memory, before and after, are in the report.
- The report is in the lane and its hash matches yours.

Then report in a few plain sentences: the commits, the verdicts, the limits left, the change in
time and memory, the report's hash, and the push command. Dustin reads your replies carefully and
is still learning to read code: use plain words and define a technical term the first time you
use it. When you need a decision from him, ask in one line with your recommended answer first.

## Revisions

- r1 (cold review 1, PASS WITH FINDINGS, all applied): the limits that stay are listed exactly
  (three more than the draft said); the kernel check covers flags with a proof term, not old case
  3; `bridge_search.py` gets one added function for the shared constants, with a score assertion,
  and diffs by key; the expected misses of the plan's checks are named, including
  `setup.worktree`, and compared as a multiset, with rc 1 expected; rule 5's budget is fixed at
  400000 with the no-change line; Done-means lines added for records-first, hashed predictions,
  the round fragment and documents; both `--diff` exit codes exercised; baselines named by order;
  the night window and the memory cap cover every run that loads the library; read range 706 to
  797; import-related pairs listed, not reviewed; found bridges numbered from 154 with their own
  Mathlib grep, in versioned bridges files.
- r2 (second pass by the same reviewer, PASS WITH FINDINGS, 0 MAJOR, 5 MINOR, all applied): item
  77's budget named as a departure from the plan row and as an added count, with Dustin told;
  the gate's summary prefix kept for the nightly script; timers checked system-wide and in cron;
  every report names its current baseline; the memory stop at 10 GB, below the 12G cap.
