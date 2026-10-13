<!-- Written on 2026-10-11 by claude-ai (revised r3 on 2026-10-12); copied verbatim on 2026-10-13 (UTC) by Claude Code session_014kHVkG96PnyF2Mo91rghpR on DSMain from /opt/datasphere/lane/inbox/threads/staging/LEAN-27-order.md (sha256 de8f6f000c9d4d0901c620f114988db9ed6bb83ff2c049d1b105c5626ce7d465, checked by sha256sum before this copy; equal to the hash in Dustin's prompt), as Dustin ordered in chat. Written before any Lean file changed, per records/README.md rule 2. -->

# LEAN-27 order: batch 1 of the library's second plan (items 79 to 83), and one gate fix

Written 2026-10-11 by claude-ai for a plain Claude Code session on DSMain, as dustin, from step 1
of OPEN-WORK-20261011-r2.md, after VACUITY-2 was pushed (origin/master and github master both
`92f8ae5`, measured by `git ls-remote` at about 23:05 EDT). Every lane file named here is in
/opt/datasphere/lane/inbox/threads/staging/. Reports and plans go to the lane through
ds_write_staging, since the lane is read-only on disk for you.

Review: one cold review by a fresh subagent that had not seen it written, PASS WITH FINDINGS
(0 BLOCKER, 3 MAJOR, 8 MINOR), every finding applied; a confirming pass by the same reviewer
(1 MAJOR, 5 MINOR, all applied) is recorded under "Revisions". Facts measured on DSMain by claude-ai at about 23:10 EDT and relied on here:
`lean-toolchain` is `leanprover/lean4:v4.34.0`; that toolchain's `Lean/Meta/Basic.lean` has a
`Meta.Config` field `iota : Bool := true` and `withConfig`; VACUITY-2's Mathlib clone
`~/lean/vacuity2-checks/mm` is at `2da3ab0a`; `tools/bridge_search.py --diff` prints NEW and GONE
keys and exits 1 when there is either; the runner's test list is
`tools/vacuity_reviewed_tests.txt` (VACUITY-2's commit `d2503ba` changed it).

## Goal

Prove items 79 to 83 of MATH-PLAN-library-2.md (batch 1) in classical-lean, as that plan states
them, under the gate VACUITY-2 left, by the plan's per-batch method (its section 8). Before the
mathematics, fix one small flaw found in the gate after VACUITY-2's reviews (job 0). Dustin pushes
after claude-ai checks the result.

The five rows, in one line each (the plan's section 5, "Batch 1", is the source; read it there):
- 79: the convex conjugate, valued in the extended reals, with Fenchel–Young, antitonicity and
  `f** ≤ f`; new module `ClassicalLean.Analysis.ConvexConjugate`.
- 80: the variance of a sum for a covariance-stationary series (the variance-ratio identity);
  in `ClassicalLean.Probability.EffectiveSampleSize`.
- 81: generalised least squares for a common mean is the library's least-variance weighting
  (`glsMatrix` of a column of ones against `minWeights`); in
  `ClassicalLean.Statistics.GeneralizedLeastSquares`, which gains an import of
  `ClassicalLean.Analysis.MinimumQuadraticForm` (measured: it imports only
  `ClassicalLean.Statistics.GaussMarkov` today). Check the new import makes no cycle.
- 82: the Kantorovich inequality; new module `ClassicalLean.Algebra.Kantorovich`.
- 83: Ky Fan's maximum principle; in `ClassicalLean.Algebra.MinMax`.

No result from below the plan's cut is pulled into this batch (Dustin did not ask for one;
LEAN-27-order-inputs.md item 2).

## Scope

- Branch `lean-27`, made from `92f8ae5` in `~/lean/classical-lean-paper-crypto`. Nothing pushed.
  No sudo.
- You may change: the five modules above (two new, three extended), `ClassicalLean.lean` (two
  import lines), `tools/VacuityGate.lean` (job 0, `unfoldNamed` only),
  `tools/VacuityGateTests.lean` and `tools/vacuity_reviewed_tests.txt` (job 0),
  `tools/vacuity_reviewed.txt` (job 0 if an entry goes stale, and rule 2c), `records/`, and
  `HANDOFF.md` and `ROADMAP.md` where they list modules, counts or the gate's limits. Nothing else.
- Nothing under `~/trading` or `~/lean/recheck` is edited. `~/.config/classical-lean/banned-terms`
  is Dustin's: never edit it, never copy its patterns anywhere.
- The night window, as VACUITY-2 measured it: start nothing that loads the library and could still
  be running at 02:30 EDT, and nothing between 02:30 and 05:45 EDT (cron 03:00 `daily_verify.sh`, cron 03:30
  `datasphere-backup.sh`, user timer 03:30 `lean-nightly`, cron 05:40 `ds-backup sync.sh`). Gate 7
  takes about 23 minutes. Check `crontab -l` and both `systemctl list-timers` lists again first.
- The memory cap: every run that loads the whole library (the gate, the plan's checks with
  `--lean`, `tools/bridge_search.py`, gate 7, a full build) runs under
  `systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0 <command>`; a run the cap kills
  is a stop.
- If you make a plan, write it to the lane as LEAN-27-PLAN.md (then -PLAN-2, never overwriting)
  and report its sha256.

## Check, then read

Check these sha256s first; if any differs, stop and say which:
- this order: the value in Dustin's prompt;
- MATH-PLAN-library-2.md `6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166`;
- MATH-PLAN-library-2-checks.py `92eedbc6598361a06a50bdf3a1b4fa1698c1d1d7a3dfe783cc79dd9c1c38307e`;
- VACUITY-2-report.md `e373acdc0aac3672af21f3b79280dd296bbef73109fff5397926679251bf0fe0`;
- LEAN-27-order-inputs.md `564d3b742e69189149d076e1fec3c435d6dd67dc567cedd8242b756280a87549`;
- LEAN-26-report.md `ce34f78d815b66673131ad01ac3cbb5b6047592f47e8f234fe7c4c8811fd8243`;
- LEAN-16-order.md `d494728c561a922b1227587395f9650f33dd3182791620e7a0d0fb6469f3120e`.

Then read: MATH-PLAN-library-2.md section 5's "Batch 1" table and the paragraph "The rule, exactly
as applied", section 6's rows 79 to 83, section 7's table header (its columns), section 8 (the
per-batch method) in full; LEAN-27-order-inputs.md in full; VACUITY-2-report.md sections "In
short", "The library", "Every limit VACUITY-1 stated", "The bridge tool" and "The plan's checks,
before and after"; LEAN-26-report.md's layout (the report's model); the "Known traps" section of
LEAN-16-order.md. In the repo: `HANDOFF.md`, `records/README.md`, round 55's fragment (it carries
the standing rule on the bridge search; its banned-vocabulary rule is withdrawn, see Revisions r3), the three existing modules'
sources, and `tools/VacuityGate.lean`'s `unfoldNamed` and `gluedProof`. If
MATH-PLAN-library-2-bridges.md exists in the lane, read the newest of its versions (none exists at
the time of writing).

## Setup

1. `git fetch origin`. origin/master and `git ls-remote github master` must both be `92f8ae5` and
   `git status` clean. If not, stop and report. Then `git switch -c lean-27 92f8ae5`.
2. Evidence folder `~/lean/lean27-checks/` with `evidence.log` (time, label, rc, prediction,
   command). Every prediction file is hashed into the log before the run it predicts. Hashes go
   into records and the report by script, never typed; every compile-fix run through `el.sh` is
   logged (section 8, step 10).
3. **Records first** (section 8, step 2), as the first commit on `lean-27`, with no `.lean` file:
   this order's copy, its INDEX row, a CLAIMS row, and the round fragment naming every new
   module's path (check_records reads fragments) and job 0.
4. First build, predicted rc 0, 4166 jobs, 0 warnings. AxiomGate at `92f8ae5`, predicted PASS,
   3158: the base for the blind constant prediction.
5. The plan's checks (section 8, step 3): run MATH-PLAN-library-2-checks.py with `--lean`, using
   `~/lean/vacuity2-checks/mm` if it is still at `2da3ab0a`, else a fresh clone into
   `~/lean/lean27-checks/mm` as the plan's section 2 shows. Predicted: 224 of 232, the misses
   exactly VACUITY-2's eight (`setup.worktree`, `gate.maxUnfolds`, `gate.macro`, `gate.helper`,
   `gate.metacheck`, `gate.test.lim_and_hyp`, `gate.test.lim_false`, `gate.list`), and every line
   of rows 79 to 83 a hit. A row line that misses means Mathlib or the library has that row by
   now: drop the row and say so.

## The work

### Job 0: the gate fix

From LEAN-27-order-inputs.md item 4 (claude-ai's review of `d2503ba`, measured on DSMain at about
22:50 EDT). `unfoldNamed` calls `whnfCore`, which still reduces a `match`, so a part computed by
pattern matching is read as `True`: `real_hyp_and_small2` below is flagged, against Dustin's ruling
that computed parts pass. The flaw errs on the strict side.

1. Add these to the test file, inside its namespace, where `V` and `P` are already variables
   (claude-ai's probe; its scratch copy on DSMain may be gone, so they are written out here):

   ```
   theorem vac_univ_mem : (5 : ℕ) ∈ (Set.univ : Set ℕ) := trivial

   def Small2 : ℕ → Prop
     | 0 => True
     | _ + 1 => False

   theorem real_hyp_and_small2 (a : V) (h : P a) : P a ∧ Small2 0 := ⟨h, trivial⟩
   ```

   Predict the new verdict count by Method A, counting the equation lemmas Lean generates for
   `Small2` and their expected verdicts (VACUITY-2 missed `Small.eq_1` the same way); add a line to
   the test list for any generated name that must be LISTED. Predict and measure under the gate as
   it is (`vac_univ_mem` and `real_hyp_and_small2` both FLAG, as claude-ai measured). Commit the
   tests and their measured table: one commit.
2. Change only `unfoldNamed`'s call to `whnfCore` so it reduces no matchers or recursors: run it
   under `withConfig (fun c => { c with iota := false })`, or under whatever `Meta.Config` field of
   the toolchain in `lean-toolchain` controls matcher reduction; read the toolchain's own source
   to confirm, and do not write a reduction of your own. One commit.
3. Predicted after: `real_hyp_and_small2` PASS, `vac_univ_mem` FLAG, every earlier test's verdict
   unchanged, the library gate PASS with the same 1 HELPER, 0 VACUOUS-PENDING, 0 rule-5 flags,
   0 run-outs, no STALE entry.
4. **Stop rule.** If no config field stops matcher reduction in `whnfCore`, or any prediction in
   step 3 misses, revert the fix commit, keep the tests commit with its measured table, leave the
   gate as VACUITY-2 left it (strict, never lax), report it, and go on with jobs 1 to 4.
5. A confirming review of the fix: one fresh general-purpose subagent, no persistent memory, its
   own folder, about 15 tool calls; its read list is the fix diff, `unfoldNamed` whole, the
   toolchain file that defines the config field, and the measured table. It runs no library gate,
   build, census or count and edits nothing in the repository; hash `~/.claude/agent-memory/`
   before and after (section 8, step 8). Apply or answer its findings; a fix gets a second
   confirming pass on its own diff; after two rounds, apply step 4's stop rule (revert the fix,
   keep the tests, report) and go on with jobs 1 to 4.

### Jobs 1 to 4: items 79 to 83, by the plan's section 8

Section 8's steps 4 to 11 apply as written, with the additions below; the one change to them is
that the vacuity gate run in step 9 is the gate as job 0 leaves it.

**Job 1, predictions** (section 8, step 4). The first build's job count by the import-closure
method; the theorem-constant count blind, Method A from source then Method B by a census of
scratch copies, the file re-hashed before the first gate. Also predict the bridge diff before its
run (job 4b): item 81's import makes `Analysis.MinimumQuadraticForm` and
`Statistics.GeneralizedLeastSquares` import-related, so that pair, and pairs that become related
through it, show as GONE; the two new modules add NEW pairs.

**Job 2, statements, hypotheses and reviews** (section 8, steps 5 to 8), with these from the
record:
- 2a. Every new main theorem with a hypothesis gets a satisfiability example in its module, an
  `example` meeting all its hypotheses at once (section 8, step 6; decision 4).
- 2b. Lean's junk values named in every dropped-hypothesis row where they decide the case. For
  item 79 there are two reasons in the plan's row: `f` is real-valued because Mathlib's
  `⊥ + ⊤ = ⊥` would break Fenchel–Young for a function that could be `⊥`; and the conjugate is
  valued in `EReal` so no junk value is needed, since a real-valued supremum of an unbounded family
  is `0`.
- 2c. A vacuity flag on a short helper lemma that only restates a definition is not a stop: remove
  the lemma if a Mathlib lemma or `simp` already does its job, or list it in
  `tools/vacuity_reviewed.txt` as HELPER with a one-line reason. Every new entry is named in the
  report, and the module's cold reviewer checks each reason against the statement. A flag on a
  main theorem, or any VACUOUS-PENDING entry, is a stop (inputs item 1).
- 2d. Every review ends with a confirming pass on the fix diff only (the same reviewer by
  SendMessage, or a fresh one with that diff as its whole read list, about 15 calls); at most two
  fix-and-confirm rounds, then stop and report (inputs item 5).
- 2e. A narrower statement than the plan's is said plainly in the module docstring, the report's
  item line and the hypothesis table (section 8, step 7). A row whose plan statement turns out
  false is reported with its counterexample and narrowed, never dropped silently.

**Job 3, documents.** `HANDOFF.md` and `ROADMAP.md` updated for the new modules and counts, and
`HANDOFF.md` §4's gate text updated for job 0 if job 0 landed.

**Job 4, the end checks, in this order:**
- 4a. None. The banned-vocabulary check is retired (Revisions r3): do not run
  `tools/banned_vocab_scan.py`, and treat round 55's banned-vocabulary rule as withdrawn.
- 4b. The bridge search (round 55's standing rule): run
  `tools/bridge_search.py --diff records/bridges/VACUITY-1/` under the memory cap; rc 1 here means
  candidates to review, not a failure. Report NEW and GONE keys against the job 1 prediction. Check
  each NEW import-unrelated pair by hand for a theorem whose proof needs both sides; a real one gets
  an item number from 154 on, ranked after item 153, and goes into the lane file
  MATH-PLAN-library-2-bridges.md (later versions -bridges-2.md, -bridges-3.md, each a whole new
  file carrying all earlier rows), with the plan's section 7 columns, its "Shared object:" line
  and its own Mathlib grep. It never enters this batch. Say for each whether it is load-bearing for
  a scheduled row (items 84 to 110); only that would re-draw the cut, at a batch boundary. Write
  the new baseline to `records/bridges/LEAN-27/`. Commit jobs 1 to 3 first and run this on that
  clean commit, so the baseline's `COMMIT` file names the tree that was searched; the baseline's
  own commit then touches only `records/`.
- 4c. Commit everything above. Then the gates (section 8, step 9) on the clean tree, predicted
  first: build (0 warnings), AxiomGate, VacuityGate, check_sorry, check_records,
  and gate 7 under the memory cap
  (`systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0 ~/lean/recheck/run-recheck.sh <commit> ~/lean/classical-lean-paper-crypto`).
  After the gates, only commits that touch nothing outside `records/` are allowed (INDEX and
  CLAIMS states, the round fragment's part 2).
- 4d. **Report** LEAN-27-report.md through ds_write_staging, post_sha256 compared with your own
  sha256sum, laid out like LEAN-26-report.md and VACUITY-2-report.md: in short; setup; job 0 with
  its tests, library run and review (or the stop rule's outcome); each item with its statements,
  hypothesis table, satisfiability example, review and any narrowing; predicted beside measured for
  jobs, constants and every gate; list entries with reasons; the bridge diff and the current
  baseline (`records/bridges/LEAN-27/`); documents changed; commits; misses and not reached; and
  the push command as one line, not run:
  `cd ~/lean/classical-lean-paper-crypto && git push origin lean-27:master && git push github lean-27:master`.
  Then stop. claude-ai reviews every commit after the last confirming pass before Dustin pushes.

## Done means

- Branch `lean-27` from `92f8ae5`, clean tree, nothing pushed; its first commit is the records
  commit and holds no `.lean` file; every prediction hashed in `evidence.log` before its run;
  hashes in records written by script; `el.sh` runs logged.
- Job 0: either landed (`real_hyp_and_small2` PASS, `vac_univ_mem` FLAG, every earlier test
  unchanged, the library gate PASS, its confirming review's findings applied or answered), or
  reverted by the stop rule with the reason reported; in both cases the tests commit stands.
- Items 79 to 83 proved with no `sorry` and no new axiom, as the plan states them, or each
  narrowing said plainly in the three places with its reason; any dropped row named with the
  Mathlib or library line that has it.
- Every new main theorem with a hypothesis has a satisfiability example; every hypothesis has a
  dropped-hypothesis row, with Lean's junk values where they decide the case.
- Each new or extended module had its cold review after its statements were final, ending with a
  confirming pass; any statement changed after its review had a statement-equivalence review.
- Every new vacuity-list entry is named in the report with its reason and its reviewer's check;
  no VACUOUS-PENDING entry.
- The job count and the constant count predicted (blind, before any census) beside measured.
- Job 3's documents changed and named.
- All six gates as predicted, or each miss reported; gate 7 ALL PASSED on the last commit that
  touches anything outside `records/`, and later commits touch only `records/`.
- The bridge diff run and reported against its prediction; the new baseline committed and named.
- The report is in the lane and its hash matches yours.

Then report in a few plain sentences: what was proved, any narrowing, job 0's outcome, the gate
results, the new list entries, the report's hash and the push command. Dustin reads your replies
carefully and is still learning to read code: use plain words and define a technical term the
first time you use it. When you need a decision from him, ask in one line with your recommended
answer first.

## Revisions

- r1 (cold review 1, PASS WITH FINDINGS, 0 BLOCKER, 3 MAJOR, 8 MINOR, all applied): records-first
  moved to setup, as the first commit; documents and the bridge search moved before the gates, and
  only records-only commits after them, with Done-means worded as VACUITY-2's; job 0 gets a stop
  rule (revert the fix, keep the tests, gate stays strict) and its switch named from the measured
  toolchain source; job 0's test count predicted with generated lemmas, its two commits named, its
  review's read list and conditions stated; scope widened to the test list and HANDOFF.md §4;
  item 79's two junk-value reasons separated; numbering made consistent; the bridges-file naming,
  the load-bearing question, the clone fallback, the night window's 23-minute margin, the
  AxiomGate base, and Done-means for documents and section 8 step 10 added; no below-cut result
  pulled in.
- r2 (confirming pass by the same reviewer: every r1 finding fixed; new 1 MAJOR, 5 MINOR, all
  applied): the night window reads "nothing between 02:30 and 05:45"; the scope cites rule 2c;
  job 0's review loop ends in its stop rule and the order goes on; the bridge search runs on a
  clean commit so its baseline names the searched tree; the test list's filename is stated as
  measured; this section records the pass.
- r3 (2026-10-12, claude-ai, from Dustin's ruling of 19:42 EDT, store row 20261012-005): the
  banned-vocabulary check is retired. Job 4a no longer runs it, the gate list in 4c and Done-means
  drop it (six gates, not seven), and the read list notes round 55's rule as withdrawn. A single
  release check for the old coined names replaces it; it is built for the public release, not here.
