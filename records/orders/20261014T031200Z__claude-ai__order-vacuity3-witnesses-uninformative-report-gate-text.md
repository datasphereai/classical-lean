# VACUITY-3 order: the gate's two reports (items 89 and 90), and the gate's stale text

Written 2026-10-13 by claude-ai for a plain Claude Code session on DSMain, as dustin, from step 1
of OPEN-WORK-20261011-r2.md: VACUITY-3 comes after LEAN-28, whose last commit `bf9922b` is GitHub
master. Lane files named here without a folder are in /opt/datasphere/lane/inbox/threads/staging/;
files named `lean/...` are in its subfolder /opt/datasphere/lane/inbox/threads/staging/lean/ (read
`lean/README.md`). Your plan, the report and the push-review file go to `lean/` through
ds_write_staging, since the lane is read-only on disk for you.

Review: two passes by one fresh cold reviewer that had not seen it written, reading the order and its sources on helios, read-only. Pass 1: PASS WITH FINDINGS (0 BLOCKER, 9 MAJOR, 18 MINOR; 22 calls). Pass 2: PASS WITH FINDINGS (0 BLOCKER, 1 MAJOR, 11 MINOR; 8 calls), confirming pass 1's findings fixed. Every finding of both passes applied ("Revisions"); the second pass's fixes have not had a third review. Not reviewed: the appendix scripts' sha256 (the reviewer had no hashing tool; the assembler checks them), the 50 modules' own `open` and `variable` lines, and anything that needs the server to run.

Facts measured on DSMain by claude-ai on 2026-10-13 from 20:38 to 21:30 EDT (DSMain's `date`),
read-only, in `~/lean/classical-lean-paper-crypto` on `lean-28` at `bf9922b` (`git status
--porcelain` empty after every run), and relied on here. The scripts are in Appendix A with their
sha256; their outputs were saved in `/tmp/claude-ai-vacuity3/` on DSMain.

- **The repository.** GitHub master and `/data/git/classical-lean.git` master are both `bf9922b`;
  GitHub has no other branch. `git diff --stat c58db94 bf9922b` shows only three files under
  `records/` (CLAIMS, INDEX and LEAN-28's records), so the gate numbers round 57 measured at
  `c58db94` hold for `bf9922b`. The main clone `~/lean/classical-lean` has `master` at `deb08cb`,
  17 commits behind origin/master, a clean tree, 26 other local branches each fully inside
  origin/master (`git branch --no-merged origin/master` prints nothing), and no stash. It is the
  nightly's clone: `~/.config/lean-nightly/config` sets `CLONE_DIR=/home/dustin/lean/classical-lean`,
  and `~/bin/lean-nightly.sh` runs `git pull --ff-only` there at 03:30, so its master catches up at
  the next nightly run. This order does not touch it.
- **The gates at `bf9922b`**, from round 57's fragment (measured by the LEAN-28 session at
  `c58db94`): build 4170 jobs, 0 warnings; AxiomGate PASS 3228; VacuityGate PASS, 1 reviewed
  helper, 0 VACUOUS-PENDING, rule 5 ran out on 0 theorems, no UNCHECKED (2:51.62, 5050648 KB); the
  gate's tests 88, 47 flagged, 0 mismatches; check_sorry PASS 122; check_records PASS 122; gate 7
  ALL PASSED, 4170 jobs, 122 modules 0 failed, 90615 declarations, three standard axioms, 3228,
  planted fault named (about 20 minutes, about 4.75 GB). The bridge baseline is
  `records/bridges/LEAN-28/`, taken at `1032cd3`; round 57 says it should describe `c58db94` too,
  "reasoned, not measured".
- **The gate's files** at `bf9922b`: `tools/VacuityGate.lean`, last changed by `5344c16`, so
  HANDOFF.md §4's line numbers "at `5344c16`" still hold; hashes in "Check, then read".
- **Item 89's targets.**
  - The plan-2 check `r1.backfill` counts 86 names in the first plan's Lean-names column. Its
    cell split (at every unescaped `|`) cuts 8 rows (9, 10, 14, 15, 22, 23, 36, 48) inside a
    backticked formula that holds `|` or `‖`. A split that keeps backtick spans whole (A3) gives
    95 names over the 71 rows.
  - 88 of the 95 resolve to exactly one library constant (A4). The other 7 were renamed by their
    orders. By name and module, inferred and not yet confirmed from the records:
    `abs_sub_eulerStep_le` → `abs_sub_eulerIterate_le`; `sum_two_pow_neg_len_div_le_one` →
    `sum_inv_two_pow_length_le_one`; `measureReal_len_le_sub_le` → `measureReal_len_add_le_le`;
    `norm_vecMul_pow_sub_le` → `sum_abs_vecMul_pow_sub_le`; `isSufficient_sum_bernoulli` →
    `isSufficient_numHeads`; `isComplete_sum_bernoulli` → `isComplete_numHeads`;
    `sampleMean_isMinVariance` → `variance_sampleMean_le` and `eq_sampleMean_of_variance_eq`.
  - Of the 96 library names, 4 are definitions (`condEntropy`, `glsMatrix`, `IsComplete`,
    `IsSufficient`) and 92 are theorems; 83 of the theorems have at least one hypothesis as
    written (a binder, not an instance, whose type is a proposition; `forallTelescope`) and 9
    have none. An instance binder that is a proposition (`[Fact p.Prime]`) is not counted as a
    hypothesis, here or in job 1. The 83 sit in 50 module files and cover 67 of the 71 items
    (items 11, 38, 53 and 62 have no theorem with a hypothesis).
  - The column does not name every main theorem. Item 44's row promises the mean duration of the
    walk, which the library proves as `GamblersRuin.integral_exitTime_eq` (it has a hypothesis);
    the column names only `measureReal_hit_eq`. Such theorems are not in this order.
  - The table, one row per theorem, is `lean/VACUITY-3-targets.tsv` (A5's output). Columns: item,
    plan name, library name, number of hypotheses, module file, and whether an `example` in that
    file (with the docstring above it) already names the theorem. Three are named in an example:
    `lp_strong_duality`, `measureReal_exists_run_le`, `measureReal_no_run_le`. Whether those
    examples meet rules 2 and 3 is not checked. Three files hold rows of two different items far
    apart in the table: `InformationTheory/SourceCoding` (items 8 and 41),
    `Probability/MaximalInequality` (23 and 43) and `Probability/CovarianceDirections` (2 and 70).
  - Re-run in a fresh folder with the names sorted under `LC_ALL=C` (setup 6's pipeline):
    `names89b.txt` sha256 `23f3cbded00bac5cd0a0d67b0ba6906862daa713450c1e13a83975ffc518e158`,
    A4's output `de6f8ba9b251bce95180526fd690391441700cf9851fa9ae48d9467f7020d5bf` (96 HIT lines),
    and A5's table byte for byte the lane table.
  - Rule 2's witness form works: A6 holds three witnesses (items 34, 37 and 28) that apply the
    theorem, each a self-contained block (`open … in`, docstring, `example`). It elaborates with
    HANDOFF.md §6 rule 20's four flags, rc 0 and no message (3.06 s, 3288404 KB).
- **Item 90's prototype**, A1 (not the tool job 1 asks for), at `bf9922b`: rc 0, 39.51 s, 4096216 KB
  peak, output sha256 `d0e06627c39478137e7121d2b2aa2f5088bb282c8707d642d3bb0d225ab82a5f`.
  - 1785 written theorems in the library (1790 with A1's 5 planted ones, which came out as
    predicted).
  - 1027 have at least one hypothesis as written. With the hypotheses cleared, none closes by
    `simp`, `norm_num` or `positivity` (988 OPEN); 39 are DEPENDENT (the conclusion or another
    binder needs a hypothesis, so it cannot be cleared); 0 TIMEOUT at 200000 heartbeats each. A1
    labels every exception TIMEOUT, so this 0 also says no exception occurred.
  - 758 have no hypothesis. 49 of them close (48 by `simp`, 1 by `positivity`). 12 of those close
    only through themselves: 10 whose proof names the theorem (A1's USES-ITSELF), and
    `Stack.admits_cons` and `Stack.admits_nil`, whose proof names the theorem's own `._simp_1`
    lemma (found by the cold review). The rest are value lemmas such as `lucas_zero`.
  - The plan's census (`forallTelescopeReducing`, at `d2cba27`) counted 1068 written theorems
    with a hypothesis. The two counts differ by method (unfolding definitions adds binders) and
    by the library's growth since then; that is inferred, not measured.
- **The recursive all-`True` predicate** that HANDOFF.md §4 leaves "for a later gate order"
  (`NatT2 | 0 => True | n + 1 => NatT2 n`): by A2's test, which reads a definition's own value,
  the library has 33 Prop-valued definitions under `ClassicalLean` and none is recursive; A2 finds
  its own planted `NatT2`. A2 would miss recursion compiled into a helper without a declaration
  range (well-founded recursion on two arguments goes through `._unary`).
- **The night jobs** (`crontab -l` and `systemctl --user list-timers --all`, 20:58 EDT): user timer
  00:00 `memory-index`, cron 02:20 `~/restic-kingston/nightly.sh` (new since LEAN-28), cron 03:00
  `daily_verify.sh`, cron 03:30 `datasphere-backup.sh`, user timer 03:30 `lean-nightly`, cron 05:40
  `ds-backup sync.sh`. There are also jobs every 5 and every 15 minutes, and two user timers that
  run every few minutes. What `memory-index` does was not measured.

## Goal

Do items 89 and 90 of MATH-PLAN-library-2.md (section 5, "Order VACUITY-3"), and the fixes to
the gate's own text and its test runner that HANDOFF.md §4 leaves "for a later gate order". (The
LEAN-28 order said the gate's next fixes are VACUITY-3's.) Nothing in the library's mathematics
changes: no theorem, definition, proof, import or module. Only `example`s are added.

- **Item 89**, satisfiability witnesses. Each theorem with a hypothesis that the first plan's
  Lean-names column names for items 1 to 71, with the 7 renames, gets an `example` that meets all
  its hypotheses at once. That is 83 theorems, listed in the targets table.
- **Item 90**, a report. A tool in `tools/` lists every written theorem whose conclusion closes
  with no hypotheses by `simp`, `norm_num` or `positivity`, for a human to read. It is a report,
  not a check. Its output is this order's evidence and goes into the report.
- **The gate's stale text and the runner**: the seven points of job 2. No verdict changes.

## Scope

- **Branch.** `vacuity-3` from `bf9922b` in `~/lean/classical-lean-paper-crypto`, made after
  Dustin approves your plan. Nothing pushed. No sudo.
- **You may change:**
  - the module files named in the targets table, by appending `example`s with their docstrings
    (rules 1 and 2) and nothing else;
  - `tools/VacuityGate.lean`, docstrings and comments only;
  - `tools/run_vacuity_tests.py`;
  - a new `tools/UninformativeReport.lean`;
  - `records/`;
  - `HANDOFF.md` §4, and §1 where it lists the tools;
  - `ROADMAP.md`, only where it lists what the gate checks.
- **You may not change** anything else under `ClassicalLean/` or `tools/`. `ClassicalLean.lean`
  does not change. Neither `tools/vacuity_reviewed.txt` nor `tools/vacuity_reviewed_tests.txt`
  changes: needing an entry there is a stop. `tools/VacuityGateTests.lean` does not change.
- **Off limits:** the main clone's working tree `~/lean/classical-lean` and its `master` branch
  (the nightly's clone; see the facts). The worktree shares the main clone's `.git`, so `git
  fetch`, your branch and your commits are written there; that is expected. Also off limits:
  anything under `~/trading` or `~/lean/recheck`. `~/.config/classical-lean/banned-terms` is
  Dustin's: never edit it, and never copy its patterns anywhere.
- **The night window.**
  - Start nothing that loads the library and could still be running at 02:00 EDT.
  - Start nothing that loads the library between 02:00 and 05:45 EDT (the night jobs above; gate
    7 takes about 20 minutes).
  - Do not start a whole-library run in the 15 minutes before the 00:00 `memory-index` timer.
  - Check `crontab -l` and both `systemctl list-timers` lists again before you start.
  - Reading, hash checks and records commits may run inside the window.
- **The memory cap.**
  - Every run that loads the whole library goes under
    `systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0 <command>`. That means a full
    build, the gate, a whole-library census, the plan's checks with `--lean`, the report tool,
    `tools/bridge_search.py` and gate 7.
  - A run the cap kills is a stop.
  - Never run two whole-library runs at once, a reviewer's included: while a reviewer runs the
    report tool, you start none, and the reviewer starts none while one of yours runs.
- **Your plan** goes to `lean/VACUITY-3-PLAN.md` (then -PLAN-2, never overwriting). Report its
  sha256.

## Check, then read

Check these sha256s first; if any differs, stop and say which:
- this order, `lean/VACUITY-3-order.md`: the value in Dustin's prompt;
- `lean/VACUITY-3-targets.tsv` `ffaa9192c81773cc0fba854f12c76fa811cc218a2b913494609848e4e3a36381`;
- MATH-PLAN-library-2.md `6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166`;
- MATH-PLAN-library.md `d7fdc14cd4e64068617783e6cb8626abc15371793a7d17f8c91de93003717d84`;
- MATH-PLAN-library-2-checks.py `92eedbc6598361a06a50bdf3a1b4fa1698c1d1d7a3dfe783cc79dd9c1c38307e`;
- `lean/LEAN-28-order.md` `65e13493df7cd07962fe559f79419a6f05f09c1505b9217e8e0f211ffcd2c8e6`;
- `lean/LEAN-28-report.md` `9e10dcf0a3a4d6ca7957204074cd3cec53b1a22cbfc6a89a730316b345a93ccb`;
- VACUITY-2-report.md `e373acdc0aac3672af21f3b79280dd296bbef73109fff5397926679251bf0fe0`;
- LEAN-16-order.md `d494728c561a922b1227587395f9650f33dd3182791620e7a0d0fb6469f3120e`;
- in the repository at `bf9922b`: `tools/VacuityGate.lean`
  `d5fd492090f2f4db7b5b085b3b4ea7828eaf4d6bfb7470c7f56ec13b8416010b`,
  `tools/run_vacuity_tests.py` `86c713ecc5056506f971e0e1270f788f4608f6b6e7ac7f3fd23b8668f2242416`,
  `tools/VacuityGateTests.lean` `5f88d6ab5fedeb77b2b67ddfd6c2c345f3282ed338d2da9d56562f125a1af4a7`,
  `tools/vacuity_reviewed.txt` `b5d168d4474375cbba3d5fd29948da316109b4323fa768af433b71df29fa8bde`.

Then read:
- **In the lane:**
  - MATH-PLAN-library-2.md: section 5's "Order VACUITY-3" table and its paragraph "Where Track G
    goes", and section 8 in full;
  - MATH-PLAN-library.md section 4, the 71 rows;
  - LEAN-28-order.md's sections "Scope", "Setup", "Job 2" and "Job 4". This order follows them
    where it does not say otherwise;
  - LEAN-28-report.md in full, the report's model;
  - VACUITY-2-report.md's limits table, the gate report's model;
  - the "Known traps" section of LEAN-16-order.md;
  - `lean/README.md`.
- **In the repository:** HANDOFF.md §4 and §6 (rules 17 and 20 apply here: every reviewer's
  output is saved verbatim with its sha256, and scratch files are elaborated with the lakefile's
  options), records/README.md, round 57's fragment, `tools/VacuityGate.lean`,
  `tools/run_vacuity_tests.py` and `tools/VacuityGateTests.lean`.

Which steps of the plan's section 8 apply: steps 1 (base), 2 (records first), 4's hashed
predictions, 8 (reviews, with `~/.claude/agent-memory/` hashed before and after each), 9 (gates;
the banned-vocabulary scan is retired, as in LEAN-28), 10 and 11. Step 3 applies only as setup 5's
run of the checks. Steps 5 to 7 are for new statements and do not apply.

## Rules for this order

1. **No mathematics changes.**
   - In `ClassicalLean/`, the only change is a block appended at the end of a module file, after
     its last line (after its last `end`), made of witness blocks. A witness block is, in this
     order: an optional `open … in` line, the docstring, the `example`. Appending after the last
     `end` keeps every `section` `variable` out of scope.
   - No theorem, definition, proof, import, attribute, `open`, `variable` or namespace line
     changes.
   - The machine checks, each by script and logged, for every changed module:
     - `git diff --numstat bf9922b -- <file>` shows 0 deleted lines, and the diff is one hunk at
       the end of the file (check `tail -c1` first: a file without a final newline shows its last
       line as changed, an expected one-line change);
     - every witness's body begins with its row's full library name;
     - the added lines contain none of `sorry`, `admit`, `native_decide`, `implemented_by`,
       `axiom`, `set_option` (grep, predicted empty);
     - no name bound by any `variable` line of the file occurs as a whole word in the added
       lines, except as the key of a named argument (`(n := …)`, as in A6's first witness, whose
       module binds `n`); every hit is checked by hand and logged, since a namespace still open
       at the end of a file keeps its variables in scope;
     - the witness blocks equal their scratch file's, byte for byte (an empty diff).
   - And once for the whole library: a per-module count of theorem constants (records/README.md
     rule 1's `env.getModuleFor?` count) before the first witness group and after the last, equal
     for every module, and AxiomGate at 3228. LEAN-28's
     `~/lean/lean28-checks/census/census-all-tail.lean` may serve; read it first, copy it into
     the evidence folder and log its sha256 before you use it.
2. **The witness form.**
   - A witness is an `example` that applies the theorem itself at concrete arguments, with a
     proof of each hypothesis: `example := Full.name (x := …) h₁ h₂ …`. Every argument the witness
     chooses (a type, a number, a matrix, a measure, a function) is given by name, `(x := …)`;
     arguments Lean fills in from those (an instance, a measurable-space structure fixed by the
     measure's type) may be left to Lean.
   - Applying the theorem makes Lean check that the hypotheses met are the theorem's own. The
     examples LEAN-27 and LEAN-28 wrote restate the hypotheses as an `∃`, which can drift from the
     theorem, so that form is not used here. Those examples stay as they are.
   - The docstring reads: "The hypotheses of `name` hold together: <the witness, in words>."
   - A witness block relies on no `open` of its scratch file: it carries its own `open … in`
     line, before its docstring (a docstring before `open … in` does not parse). A scratch file
     holds, after its import, only the module's own top-level `open` lines (those outside every
     namespace and section, which are still in force after the module's last `end`), then the
     blocks. A witness then elaborates in its scratch file in the scope it will have in the
     module.
   - No `sorry`, `admit`, `native_decide`, `implemented_by` or `axiom`, and no `set_option`.
   - A6's three witness blocks meet rules 2 and 3 (A6's third version, after both reviews) and
     may be used as they are.
   - This rule is claude-ai's ruling, with Dustin's veto open. Job 4 files it as a standing rule.
3. **Not degenerate.** No hypothesis may be met only:
   - because a type or a set is empty, a size or a count is 0, a measure is the zero measure, an
     interval is a single point, or a sum ranges over nothing;
   - through one of Lean's junk values: `x / 0 = 0`, `log 0 = 0`, `ℕ` subtraction stopping at
     `0`, `⨆` of an unbounded family being `0`, the integral of a non-integrable function being
     `0`, the inverse of a singular matrix being `0`, conditional expectation with respect to a
     σ-algebra that is not smaller being `0`;
   - at a boundary where a constant of the theorem itself vanishes (A6's first draft took
     `δ = 1/2` on `Fin 2`, where `existsUnique_vecMul_eq_self`'s `1 - card n * δ` is `0`).

   Where a theorem is about a family or a matrix of size `n`, take `n ≥ 2`, unless the theorem
   fixes `n`. A point mass or a one-point space is allowed only when the docstring says why each
   hypothesis is still met for a reason of its own (A6's third witness shows how). Each group's
   reviewer checks this, witness by witness.
4. **Hypotheses that cannot all hold.**
   - A rule-4 finding says a library theorem's hypotheses contradict each other, which is what
     item 89 exists to find. It stands only with a scratch `example` that derives `False` from
     the hypotheses (elaborated with the four flags, rc 0, logged). Then:
     - stop work on that theorem;
     - put the scratch file and your reasoning in the report as a finding;
     - tell Dustin in one line, and go on with the others;
     - do not change the theorem in this order.
   - Without such a proof, the row is NOT WITNESSED, with the suspicion stated.
   - A theorem still without a witness after about 30 minutes of attempts is NOT WITNESSED.
   - Every NOT WITNESSED row names its scratch file and the `evidence.log` lines of its first and
     last attempts.
   - Never weaken, restate or add a hypothesis to a theorem to get a witness.
5. **The report tool reports.** Nothing its library output shows fails anything. Only its own
   self-test and its own count check (job 1, point 7) can fail it, with rc 1.
6. **Gate text changes change no verdict.**
   - The library gate's output is the same before and after, line for line apart from times.
   - The tests' output format changes (job 2, point 7), so for the tests compare by script the
     (name, verdict) pairs and the counts on the summary line: equal before and after.
7. **A question to Dustin holds only its own outcome open** (LEAN-28's rule 2). Don't apply your
   own answer before he replies; the work the question doesn't touch goes on.

## Before approval (read-only in the repository)

1. `git fetch origin` in the worktree. origin/master and `git ls-remote github master` must both be
   `bf9922b` (`bf9922be881cbdcbe3cd29bea8132326b3cb43c0`), and `git status --porcelain` must be
   empty. If not, stop and report.
2. Check the hashes above and read the read list.
3. Check the night jobs and the free memory (`free -g`).
4. Write your plan to `lean/VACUITY-3-PLAN.md`: the jobs in order, with every prediction you can
   already make, and the size of job 3's witness groups. Then stop and wait for Dustin's
   approval.

## Setup (after approval)

1. **Branch.** `git switch -c vacuity-3 bf9922b`.
2. **Evidence folder** `~/lean/vacuity3-checks/`, with `evidence.log` (time, label, rc,
   prediction, command).
   - Every prediction file is hashed into the log before the run it predicts.
   - Hashes go into records and the report by script, never typed.
   - Every compile-fix run through `el.sh` is logged.
   - Every file reused from LEAN-28's folder (`census-all-tail.lean`, `pred-checks.md`) is copied
     in first, with its sha256 logged.
3. **Records first.** The first commit on `vacuity-3`, with no `.lean` file:
   - this order's copy as
     `records/orders/<UTC>__claude-ai__order-vacuity3-witnesses-uninformative-report-gate-text.md`;
   - its INDEX row;
   - a CLAIMS row;
   - round 58's fragment, which names in full every module file of the targets table, plus
     `tools/VacuityGate.lean`, `tools/run_vacuity_tests.py` and the new
     `tools/UninformativeReport.lean`, and says that no module is new.
4. **The before runs, at the records commit**, predicted from round 57:
   - build rc 0, 4170 jobs, 0 warnings;
   - AxiomGate PASS 3228;
   - VacuityGate PASS (1 reviewed helper, 0 VACUOUS-PENDING, rule 5 ran out on 0, no UNCHECKED),
     its output saved as `gate-before.out` for rule 6;
   - the gate's tests: 88, 47 flagged, 0 mismatches, the output saved as `tests-before.out`;
   - the whole-library per-module count of rule 1, saved as `census-before.out`.
5. **The plan's checks**, with `--lean`, using `~/lean/vacuity2-checks/mm`.
   - First write the predicted misses, line by line. Start from LEAN-28's `pred-checks.md` and
     its report's 30 misses at `c5c004b`, then add every line LEAN-28's commits moved, each named
     with its reason.
   - Give the predicted values of the three lines behind this order's rows: `census.hyp1`,
     `census.written` and `r1.backfill`. The last still hits, because its own split gives 86
     (see the facts above).
   - A miss never drops item 89 or item 90: their rows are not Mathlib searches.
6. **The targets, re-measured.**
   - Extract Appendix A's A3, A4 and A5 byte for byte into `~/lean/vacuity3-checks/targets/` and
     check their sha256.
   - Run A3 with that folder as the current folder. Then, in that folder, make `plan1-names.txt`
     with `cut -f2 plan1-names.tsv | tr ' ' '\n' | sed '/^$/d' | LC_ALL=C sort -u`, and make
     `names89b.txt` as `plan1-names.txt` followed by the 8 inferred names in the order the facts
     list them. Predicted sha256 of `names89b.txt`: `23f3cbde…` (in full in the facts).
   - Run A4 from the repository root, under the cap, with `V3DIR` set to that folder (pass it to
     the scope with `systemd-run --setenv=V3DIR=…`), its output saved as `resolve89b.out` in that
     folder. Predicted sha256: `de6f8ba9…`.
   - Run A5 from the repository root, with that folder as its argument. Predicted: its table is
     equal byte for byte to `lean/VACUITY-3-targets.tsv`.
   - Then confirm each of the 7 inferred names from the records: `grep -rn` the old plan name in
     `records/rounds/` and `records/orders/`, and say where a record names its library name, or
     that none does.
   - A mapping the records contradict is fixed in the evidence copy of the table. Write the fixed
     table to the lane as `lean/VACUITY-3-targets-2.tsv` through ds_write_staging, compare its
     post_sha256, and work from it from then on. The report says so.

## The work

The jobs run in this order. If the session must stop during job 3, jobs 4 and 5 still run, on
what is committed.

### Job 1, item 90: `tools/UninformativeReport.lean`

- **Goal:** the report the plan's item 90 describes. Any later order can re-run it with
  `lake env lean tools/UninformativeReport.lean` from the repository root.
- **What it does.** A1 is a prototype you may start from; the tool must meet this list, not A1.
  1. **Scope.** It scans every written theorem under the namespace `ClassicalLean`: a `.thmInfo`
     constant with a declaration range, with private names read through `privateToUserName`. It
     goes in name order and takes binders as written (`forallTelescope`, no unfolding). An
     instance binder that is a proposition is not a hypothesis; the tool's docstring says so as a
     limit.
  2. **Section A**, theorems with at least one hypothesis (a binder, not an instance, whose type
     is a proposition):
     - The hypotheses are cleared from the goal. A theorem whose conclusion or another binder
       needs one is DEPENDENT.
     - Otherwise `simp`, `norm_num` and `positivity` are tried in that order, each from a saved
       state. The line is `CLOSES <tactic>`, `OPEN`, `TIMEOUT` or `ERROR`.
     - Each theorem's whole try has its own heartbeat count of 200000, as in A1. Do not change
       that number during the run without asking Dustin in one line (LEAN-16's known trap).
     - TIMEOUT is only for running out of heartbeats (`Exception.isMaxHeartbeat`, defined in
       Lean's `Lean/CoreM.lean` at line 669 of v4.34.0's sources). Any other exception is
       `ERROR <name>: <the message's first line>`. A theorem that runs out is never a pass.
     - A CLOSES whose proof term contains `sorryAx` or an unassigned metavariable is an ERROR.
  3. **Section B**, theorems with no hypothesis: the same three tactics. The theorems that close
     are listed; the others are only counted.
  4. **Self-use.**
     - Both `simp` and `norm_num` run with the theorem itself removed from the simp set, through
       the simp-set API so that private names work too. Remove it only when it is a simp lemma
       (or with a removal that does not fail on a name the set lacks): an erase that throws on a
       theorem without the attribute would make most of section A an ERROR.
     - Every CLOSES line names the library constants its proof term uses.
     - A line says USES-ITSELF when the proof's constants, unfiltered, include the theorem or any
       constant that has the theorem's name as a strict prefix (`<name>._simp_1`, `<name>.eq_1`).
  5. **Section C**, the gap in HANDOFF.md §4: every Prop-valued definition under `ClassicalLean`
     whose value names a `brecOn`, a recursor `rec` or `WellFounded.fix` (A2's test), following
     one level into constants that have no declaration range (such as `._unary`). These are
     listed for a human, since the gate does not read a recursive all-`True` predicate as `True`.
  6. **A self-test, run first,** on planted theorems and definitions in a namespace of the tool's
     own, outside `ClassicalLean`. At least:
     - A1's five planted theorems (one closing by each tactic, one OPEN, one DEPENDENT);
     - a second DEPENDENT case, where a later binder that is not a proposition has a type that
       mentions a hypothesis, while the conclusion does not;
     - a TIMEOUT case: a goal that needs more than the small budget the self-test gives it (that
       budget is the self-test's, not the library's; it must be at least 1, since a
       `maxHeartbeats` of 0 means no limit);
     - a `@[simp]` value lemma of a definition that only its own simp lemma unfolds, predicted
       OPEN once it is removed from the simp set, for both `simp` and `norm_num`;
     - A2's `NatT2`, and a Prop-valued definition by well-founded recursion on two arguments, both
       predicted in section C.

     Each expected verdict is written in the file. A mismatch is an error, so the run's rc is 1.
     Planted names never appear in the library's sections or counts.
  7. **Output:** one line per listed theorem, then `SUMMARY` lines with every category, zeros
     included. The tool checks that section A's and section B's counts add up to the number of
     written theorems, and raises an error if they do not. The run's wall time and peak memory
     are taken outside it, with `/usr/bin/time -v`.
- **Predicted**, from the facts above (A1 and A2 at `bf9922b`; no library theorem changes in this
  order). Write your own numbers in the prediction file before the first run.
  - The self-test passes, rc 0.
  - Section A: 1027 theorems: 0 CLOSES, 988 OPEN, 39 DEPENDENT, 0 TIMEOUT, 0 ERROR.
  - Section B: 758 theorems, between 37 and 49 of them close. The 12 that closed only through
    themselves may now stay open; say which.
  - Section C: 0.
  - About 40 s and about 4.1 GB.
- **Cold review** of the tool before it is final.
  - A fresh general-purpose subagent with its own scratch folder.
  - Read list: this job's text, the tool, its output and A1.
  - About 40 tool calls. It may run the tool once under the cap (rule on whole-library runs in
    Scope), and may add planted cases in a scratch copy.
  - Then a confirming pass on the fix diff: at most two fix-and-confirm rounds, as LEAN-28's 2d.
- **Done means:**
  - the tool is committed with its self-test;
  - its last run is job 5's (5b);
  - the report quotes, from that run: the `SUMMARY` lines, every CLOSES, DEPENDENT, TIMEOUT and
    ERROR line of section A, every CLOSES line of section B, and all of section C.
- **Undo:** `git rm tools/UninformativeReport.lean` in a new commit.

### Job 2, the gate's own text and its test runner

These are the points HANDOFF.md §4 lists from the confirming review of `5344c16`. Line numbers
are in `tools/VacuityGate.lean` at `d5fd4920`, the same as at `5344c16`. They move as you edit:
find each place by its text, or edit from the bottom of the file up.

1. **Lines 328 and 407 to 408.** `gluedProof`'s docstring and `vacuousProof`'s limits list say
   that computed facts are "never flagged". In fact a structural recursion such as `Small3` is
   read as `True` through smart unfolding and is flagged (test `real_hyp_and_small3`, listed).
   Say so.
2. **Line 384.** The heading "As order VACUITY-2 leaves it": give the limits as they stand after
   LEAN-27's job 0.
3. **Lines 470 and 652 to 653.** The docstrings of `KernelCheck.rejected` and
   `Verdict.kernelRejected` name `Meta.check` as the cause. Say that the kernel refused a term the
   elaborator had accepted, and keep the resource-limit case (`notChecked`, lines 472 to 474)
   separate.
4. **Line 650.** `Verdict.unchecked` says only "did not finish within the heartbeat budget". Read
   `judge` (its docstring at lines 656 to 666, its code at 667 to 708) and name every path that gives UNCHECKED: running out of
   heartbeats, an all-`True` reading the kernel could not confirm (`unconfirmedMsg`, line 318),
   and any other exception from the fixed test that `judge` turns into UNCHECKED.
5. **Lines 280 to 281 and 308 to 311.** `unfoldNamed`'s docstring and `confirmTrue`'s docstring
   both say "yes for a structure outside `Prop` (eta)". That claims too much: `Fin 2`'s all-`True`
   match is not confirmed, and fails closed. Say what is confirmed.
6. **Lines 656 to 666.** `judge`'s docstring should say that "old case 3 only (fixed test
   UNCHECKED: …)" can label an empty theorem.
7. **`tools/run_vacuity_tests.py`.** The runner joins the gate's code into a scratch file and
   prints its own verdict lines (line 93: `UNCHECKED <name>: <message>`). It checks the UNCHECKED
   verdict but not its message, and its verdict column (line 186) is 7 wide, narrower than
   UNCHECKED and KERNEL-REJECTED.
   - For each `vac_unchecked_` test, compare the message on its UNCHECKED line with a literal
     kept in the runner, the gate's `unconfirmedMsg` today ("every case is True; kernel could not
     confirm the proof"). A difference is a MISMATCH.
   - Widen the column to fit every verdict.
   - Fail-test it: run with `--gate` on a scratch copy of the gate, kept in the evidence folder
     (outside the repository, so the tree stays clean), whose `unconfirmedMsg` is changed.
     Predicted: rc 1, with 2 MISMATCH lines. Log it.

- **Guards.**
  - The runner tells gate versions apart by searching the gate's text, comments included (lines
    122 to 140 and line 40). So before and after the edits, count with `grep -c` each of
    `def judge`, `if n.hasMacroScopes then continue`, `def usedHelpers`, `kernelRejected` and
    `def rule5`, and count the two-line `set_option maxHeartbeats N in` / `run_cmd` pair with the
    runner's own line-40 regex, in Python. Predicted equal.
  - After job 2, run `grep -n "never flagged\|structure outside\|structure type outside"
    tools/VacuityGate.lean`, and after job 4 the same on `HANDOFF.md`, each with its expected
    output written first. Every line left must say the corrected thing.
- **Predicted.**
  - The tests give the same 88 verdicts as `tests-before.out` (47 flagged, 2 UNCHECKED, now with
    their messages checked), 0 mismatches, compared as rule 6 says.
  - The library gate's output equals `gate-before.out` line for line, apart from times.
- **Cold review** of the diff: a fresh subagent, about 20 calls, then a confirming pass.
- **Done means:** one commit for the gate text and one for the runner, with the tests, the
  fail-test, the version-detection counts, the gate file's grep and the library as predicted
  (HANDOFF.md's grep is job 4's).
- **Undo:** revert both commits.

### Job 3, item 89: the witnesses

- **Goal:** every theorem of the targets table has a witness by rules 2 and 3, or is reported
  under rule 4, or is NOT REACHED (below).
- **Groups.** Work in table order, in groups of at most 8 witnesses. Do not edit a file in a later
  group until the confirming pass of an earlier group that touched the same file has closed
  (three files hold rows far apart; see the facts).
- **Each group, in this order:**
  1. **Scratch first.** For each of its modules, write the group's witness blocks in a scratch
     file in the evidence folder that imports only that module, laid out as rule 2 says.
     Elaborate it with rule 20's four flags:
     `lake env lean -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3 <file>`.
     The result must be rc 0 and no message. Log every run.
  2. **Into the module.** Append the witnesses to the end of the file, byte for byte from the
     scratch file (rule 1). Then build: rc 0, 4170 jobs, 0 warnings. Run rule 1's per-module
     checks. check_sorry PASS.
  3. **One commit** for the group, naming its modules and theorems.
  4. **Cold review of the group.**
     - A fresh general-purpose subagent, with its own scratch folder.
     - Its read list is a packet you build by script: for each row, the theorem's statement as it
       stands in its module, beside the witness and its docstring; plus rules 2 to 4 of this
       order.
     - About 40 calls. Tell it that other work goes on meanwhile, and to run no census, count or
       gate. It may elaborate at most two small files, each under
       `systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=0`.
     - It checks, witness by witness: the example applies the named theorem (not a restatement,
       not another theorem); every argument the witness chooses is given by name (rule 2); no
       witness uses a name from a `variable` line; rule 3 holds, junk values and boundaries
       included; the docstring says what the witness is.
     - Then a confirming pass on the fix diff. At most two fix-and-confirm rounds; a witness still
       not clean after two is removed and reported NOT WITNESSED.
     - A fix goes through steps 1 and 2 again (the scratch file first, then the byte-for-byte
       copy and rule 1's checks), never as an edit in the module alone.
- **The three theorems an example already names** (see the facts): if that example applies the
  theorem and meets rule 3, keep it, name it in the report and add nothing. Otherwise add a
  witness.
- **The time cap.** Job 3 stops after about 8 hours of work, at a group boundary. Rows not reached
  by then are NOT REACHED, and a later order picks them up. Stop at a group boundary too if the
  night window, the session's context or Dustin requires it; commit the group that is done.
  Stop early enough that jobs 4 and 5 still fit: about 2 hours, gate 7's 20 minutes included,
  before the night window or the end of the session's context.
- **Predicted:** 83 witnesses, or fewer with each missing one named. Constants stay at 3228 and
  build jobs at 4170. Before the first group, write your own predicted counts of NOT WITNESSED
  and NOT REACHED.
- **Done means:**
  - every row of the table is one of: WITNESSED (the example's module and line), KEPT (an
    existing example), NOT WITNESSED (its scratch file and log lines), NOT REACHED, or a rule-4
    finding;
  - rule 1's checks logged for every changed module, and the whole-library count after the last
    group (`census-after.out`) equal to `census-before.out`;
  - every group's review closed with a confirming pass.
- **Undo:** revert the group commits.

### Job 4, documents

- **HANDOFF.md §4, the VacuityGate paragraph:**
  - strike the list "Stale text left for a later gate order" and the runner points job 2 fixed;
  - correct its own two stale sentences, which say computed facts are "never flagged" and that
    `confirmTrue` says yes "for a structure outside `Prop` (eta)";
  - keep the `NatT2` gap as a stated limit, with the measured count (section C: none under
    `ClassicalLean`, by the tool's test);
  - add a short paragraph on the report tool: what it lists, that it is a report, its limits,
    how to run it;
  - add a short paragraph on witnesses: rules 2 and 3, where the witnesses are, and the rows not
    done;
  - update §1 if it lists the tools.
- **Round 58's fragment** carries two standing rules: from VACUITY-3 on, a satisfiability example
  applies the theorem itself (rule 2 of this order), not an `∃` restatement; and every later gate
  order re-runs the report tool.
- **ROADMAP.md** only where it lists what the gate checks. Name each file changed.

### Job 5, the end checks, in this order

- **5a. The bridge search.** Run `tools/bridge_search.py --diff records/bridges/LEAN-28/` under
  the cap, on a clean commit after jobs 1 to 4.
  - Predicted: rc 0, no new key and no gone key, because `example`s add no constants, so the
    search sees what LEAN-28 left.
  - This also measures round 57's "reasoned, not measured" line about `c58db94`.
  - If rc 1, report the keys. Make a new baseline only if keys changed.
- **5b. The report tool's last run** on that commit, with job 1's predicted numbers.
- **5c. The six gates** (build, AxiomGate, VacuityGate, check_sorry, check_records, gate 7), plus
  the gate's tests, on the clean tree, predicted first:
  - build rc 0, 4170 jobs, 0 warnings;
  - AxiomGate PASS 3228;
  - VacuityGate's output equal to `gate-before.out` (rule 6);
  - the gate's tests: 88, 47 flagged, 0 mismatches;
  - check_sorry PASS 122;
  - check_records PASS 122;
  - gate 7 under the cap: ALL PASSED, 4170 jobs, 122 modules 0 failed, 90615 declarations, three
    standard axioms, 3228, planted fault named.

  After the gates, the only commits allowed are ones that touch nothing outside `records/`.
- **5d. The report**, `lean/VACUITY-3-report.md`, written through ds_write_staging. Compare its
  post_sha256 with your own sha256sum. Lay it out like LEAN-28-report.md:
  - in short;
  - setup;
  - job 1: the spec met point by point, the self-test, the output lines its Done-means names, and
    the numbers predicted beside measured;
  - job 2: the edits, the guards, the fail-test, and the tests and library before and after;
  - job 3: a table of item, theorem, and the witness's module and line (or KEPT, NOT WITNESSED,
    NOT REACHED, or a rule-4 finding), and the reviews;
  - documents; the plan's checks; the bridge diff;
  - predicted beside measured for everything;
  - commits; misses and not reached;
  - the push command as one line, not run:
    `cd ~/lean/classical-lean-paper-crypto && git push origin vacuity-3:master && git push github vacuity-3:master`.
- **5e. The push-review file**, `lean/VACUITY-3-push-review.txt`, built as LEAN-28's job 4d but
  from `bf9922b`. One script writes it, each command followed by its full output:
  - `git rev-parse HEAD`;
  - `git status --porcelain`;
  - `git ls-remote origin master`;
  - `git ls-remote github master`;
  - `git merge-base --is-ancestor bf9922b HEAD`, with its exit code;
  - `git rev-list --count bf9922b..HEAD`;
  - `git log --name-only --format='== %h %cI %s' bf9922b..HEAD`;
  - `git show` of every commit after the last confirming review, and of every commit that touches
    a module, or one of the three `tools/` files, after that file's last confirming pass; files
    under `records/bridges/` as `--stat` only.

  Report its sha256. Then stop. claude-ai reviews it before Dustin pushes.

## Done means

- **Branch and records.** Branch `vacuity-3` from `bf9922b`, clean tree, nothing pushed. Its first
  commit is the records commit and holds no `.lean` file. Every prediction is hashed in
  `evidence.log` before its run; hashes in records are written by script; `el.sh` runs are
  logged; every reviewer's output is saved verbatim with its sha256 (HANDOFF.md §6 rule 17).
- **The targets** were re-measured equal to the lane table, or each difference is named and the
  fixed table is in the lane. Each of the 7 inferred names is confirmed or corrected from the
  records.
- **Job 1:** the report tool committed with its self-test; its last run's lines quoted in the
  report.
- **Job 2:** the seven points done; the guards as predicted (HANDOFF.md's grep after job 4); the
  fail-test as predicted; the test verdicts and the library output unchanged (rule 6).
- **Job 3:** every target accounted for (WITNESSED, KEPT, NOT WITNESSED, NOT REACHED, or a rule-4
  finding); rule 1's checks logged; the whole-library counts equal; every group's review closed
  with a confirming pass.
- **Job 4:** the documents changed and named; round 58 carries the two standing rules.
- **The gates:** all six and the tests as predicted, or each miss reported. Gate 7 ALL PASSED on
  the last commit that touches anything outside `records/`, and later commits touch only
  `records/`.
- **The bridge diff** run and reported against its prediction.
- **The lane files:** the report and the push-review file are in `lean/`, and their hashes match
  yours.

Then report in a few plain sentences: the witnesses made and missing, any rule-4 finding, the
report tool's numbers, the gate results, the two files' hashes and the push command. Dustin reads
your replies carefully and is still learning to read code: use plain words, and define a
technical term the first time you use it. When you need a decision from him, ask in one line with
your recommended answer first.

## Not in this order

- **Main theorems the first plan's column does not name**, such as item 44's
  `integral_exitTime_eq`. A later order can collect them from the round fragments.
- **Converting LEAN-27's and LEAN-28's `∃` examples** to rule 2's form. They stay as they are; a
  later order may convert them.
- **Witnesses for lemmas, helpers or plan-2 theorems.** Items 72 on are covered by the per-batch
  rule, from LEAN-27 on.
- **Catching a recursive all-`True` predicate in the gate.** It needs induction and its own
  ruling; the report's section C lists any such predicate.
- **The main clone and its 26 merged local branches.** The nightly fast-forwards its master;
  deleting the old branches is Dustin's decision.
- **LEAN-29**, and the API drafts of items 91 to 110.

## Revisions

- r1 (cold review pass 1, PASS WITH FINDINGS, 0 BLOCKER, 9 MAJOR, 18 MINOR; claude-ai checked each
  against the sources, and all held; all applied):
  - Job 2 (the witnesses) is now job 3, in groups of at most 8 with a commit, a review packet and
    a confirming pass each, an 8-hour cap with NOT REACHED, and jobs 4 and 5 run after any stop;
    the gate text is now job 2.
  - Witnesses go after the file's last line, out of every section; rule 1's checks are by script
    (diff, variable names, byte-for-byte move, banned words) plus one whole-library count before
    and after, instead of a census per module.
  - Rule 3 names Lean's junk values and the boundary case; A6's first witness moved off
    `δ = 1/2` (where the theorem's constant is 0), and its third says why each hypothesis holds
    (A6 re-run: rc 0, no message).
  - The Goal says what the table covers, and item 44's `integral_exitTime_eq` is named as a main
    theorem the column leaves out.
  - Job 1: self-removal from `norm_num` too; USES-ITSELF by name prefix (12, not 10: the review
    found `Stack.admits_cons` and `Stack.admits_nil`); TIMEOUT only by `isMaxHeartbeat`, other
    exceptions ERROR; planted TIMEOUT, a second DEPENDENT and a two-argument recursion; every count
    printed, and A plus B checked.
  - Rule 4 needs a Lean proof of `False` for a finding, and a NOT WITNESSED row names its attempts.
  - Job 2's line numbers corrected (281 is `unfoldNamed`'s docstring, `confirmTrue`'s is 308 to
    311; 470, 652 to 653, 656 to 666) and HANDOFF's two stale sentences added; the runner's message
    check compares with a literal and is fail-tested; guards for the runner's version detection and
    a grep for the stale phrases.
  - The main clone's fast-forward is dropped: the nightly's config sets
    `CLONE_DIR=/home/dustin/lean/classical-lean`, and the nightly pulls it at 03:30 (the draft had
    inferred the opposite; store row 20261013-022).
  - Smaller: rule 6 compares the tests by (name, verdict); `names89b.txt` and A4's output re-measured
    under `LC_ALL=C` (table unchanged); section C's wording and its blind spot; the three files in
    two batches; `open … in` allowed; plan section 8's applicable steps, agent-memory hashing and
    HANDOFF rule 17; ROADMAP in scope; the push-review file's `records/bridges/` and `tools/`
    rules; a fixed table goes to the lane as `-targets-2.tsv`; reused LEAN-28 files hashed first;
    the instance-binder limit; `bf9922b` adds only records to `c58db94` (measured); the 1068
    against 1027 comparison marked inferred; a reviewer's whole-library run counts against the
    one-at-a-time rule; the 00:00 timer listed.
- r2 (cold review pass 2 by the same reviewer, PASS WITH FINDINGS, 0 BLOCKER, 1 MAJOR, 11 MINOR;
  it confirmed all 9 majors and 17 of the 18 minors of pass 1 fixed, one partly; all applied):
  - A6's witnesses are self-contained blocks (`open … in`, then the docstring, then the
    `example`), the third names `Ω`, and rule 2 says which arguments must be named and how a
    scratch file is laid out (A6's third version: rc 0, no message, 3.06 s).
  - Rule 5 names the count check; the simp-set removal must not fail on a non-simp theorem; the
    self-test's TIMEOUT budget is at least 1; any `variable` line's names are grepped; the final
    newline case; the two-line pattern counted by the runner's own regex; the gate file's grep
    after job 2 and HANDOFF.md's after job 4; edits found by text, not line number; the fail-test's
    gate copy outside the repository; a fix after review goes through the scratch file again;
    "off limits" means the main clone's working tree and `master`, not the shared `.git`; job 3
    stops early enough for jobs 4 and 5; the `memory-index` timer's part said.

## Appendix A: the measurement files

claude-ai ran these on DSMain from `~/lean/classical-lean-paper-crypto` at `bf9922b`, with the files in `/tmp/claude-ai-vacuity3/`. Each file is the text between its fence lines, exactly, ending with a newline; extract it and check its sha256 before you run it.

### A1: `/tmp/claude-ai-vacuity3/Report90Probe.lean`, item 90's prototype, with five planted theorems

sha256 `f53afbb73a41887719a977b0475f377085af88f183be4c2ca4482394b927186d`; its output `report90probe3.out` had sha256 `d0e06627c39478137e7121d2b2aa2f5088bb282c8707d642d3bb0d225ab82a5f`.

```lean
import ClassicalLean
/-! VACUITY-3 probe for item 90 (claude-ai, 2026-10-13), read-only, a prototype and not the tool
the order asks for. For every written theorem under `ClassicalLean` (a declaration range, so no
`_proof_` helper or equation lemma) with at least one hypothesis (a non-instance binder whose type
is a proposition, binders taken as written with `forallTelescope`), it clears the hypotheses and
tries to close the conclusion with `simp`, `norm_num`, `positivity`, in that order, each in a
saved state, the theorem's whole try under its own heartbeat budget (`budget` below).
One line per theorem with a hypothesis:
  `CLOSES <tactic> <name> uses=[library constants in the proof]` (`USES-ITSELF` if the proof
  term names the theorem), `OPEN <name>`, `DEPENDENT <name>` (the conclusion or another binder
  needs a hypothesis, so it cannot be cleared), `TIMEOUT <name>`.
Then `SUMMARY` lines with the counts.
Predicted before running: rc 0; about 1068 theorems with a hypothesis (the plan's census at
`d2cba27`; more now); CLOSES on a few dozen at most; wall time under 15 minutes. -/
/-- Planted cases (predicted: the first three CLOSES by simp, norm_num and positivity in turn;
`notClosed` OPEN; `dep` DEPENDENT). -/
theorem ClassicalLean.Probe90.bySimp (x : ℕ) (h : x = 5) : x + 0 = x := by simp
theorem ClassicalLean.Probe90.byNormNum (x : ℕ) (h : x = 5) : (2 : ℝ) + 2 = 4 := by norm_num
theorem ClassicalLean.Probe90.byPositivity (x : ℝ) (h : 0 < x) : 0 ≤ x ^ 2 := by positivity
theorem ClassicalLean.Probe90.notClosed (x : ℝ) (h : 0 < x) : 0 < x := h
theorem ClassicalLean.Probe90.dep (n : ℕ) (h : 0 < n) : (⟨0, h⟩ : Fin n).val = 0 := rfl

open Lean Meta Elab Term Tactic Command

def budget : Nat := 200000

def tacs : TermElabM (Array (String × TSyntax `tactic)) := do
  return #[("simp", ← `(tactic| simp)), ("norm_num", ← `(tactic| norm_num)),
    ("positivity", ← `(tactic| positivity))]

def tryClose (dbg : Bool) (g : MVarId) (tac : TSyntax `tactic) : TermElabM (Option (Array Name)) := do
  let s ← saveState
  try
    let gs ← Tactic.run g (evalTactic tac)
    if gs.isEmpty then
      let pf ← instantiateMVars (mkMVar g)
      let used := pf.getUsedConstants.filter fun c => (`ClassicalLean).isPrefixOf (privateToUserName c)
      s.restore
      return some used
    if dbg then IO.println s!"DEBUG {tac}: {gs.length} goals left"
    s.restore
    return none
  catch e =>
    if dbg then IO.println s!"DEBUG {tac}: {← e.toMessageData.toString}"
    s.restore
    if e.isRuntime then throw e
    return none

def analyze (n : Name) (ty : Expr) : TermElabM String := do
  forallTelescope ty fun xs body => do
    let mut hyps : Array FVarId := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isInstImplicit then continue
      if ← isProp d.type then hyps := hyps.push x.fvarId!
    let pre := if hyps.isEmpty then "NOHYP-" else ""
    if hyps.any (fun h => body.containsFVar h) then return "DEPENDENT"
    let g ← mkFreshExprMVar body
    let gid ← g.mvarId!.tryClearMany hyps
    let lctx := (← gid.getDecl).lctx
    if hyps.any (fun h => lctx.contains h) then return "DEPENDENT"
    let dbg := (`ClassicalLean.Probe90).isPrefixOf n
    for (nm, tac) in ← tacs do
      if let some used ← tryClose dbg gid tac then
        let self := if used.contains n then " USES-ITSELF" else ""
        let us := ", ".intercalate (used.toList.map fun c => (privateToUserName c).toString)
        return s!"{pre}CLOSES {nm}{self} uses=[{us}]"
    return s!"{pre}OPEN"

elab "#report90probe" : command => do
  let env ← getEnv
  let mut cands : Array (Name × Expr) := #[]
  for (n, ci) in env.constants.toList do
    let .thmInfo ti := ci | continue
    unless (`ClassicalLean).isPrefixOf (privateToUserName n) do continue
    if (← findDeclarationRanges? n).isNone then continue
    cands := cands.push (n, ti.type)
  cands := cands.qsort fun a b => (privateToUserName a.1).toString < (privateToUserName b.1).toString
  let mut counts : Std.HashMap String Nat := {}
  for (n, ty) in cands do
    let r ← try
        withScope (fun s => { s with opts := maxHeartbeats.set s.opts budget }) <|
          liftTermElabM (analyze n ty)
      catch _ => pure "TIMEOUT"
    let key := (r.splitOn " ").head!
    counts := counts.insert key (counts.getD key 0 + 1)
    unless key == "NOHYP-OPEN" do
      let detail := " ".intercalate ((r.splitOn " ").drop 1)
      IO.println s!"{key} {privateToUserName n} {detail}"
  IO.println s!"SUMMARY written theorems {cands.size}"
  for (k, v) in counts.toList do
    IO.println s!"SUMMARY {k} {v}"

set_option maxHeartbeats 2000000 in
#report90probe
```

### A2: `/tmp/claude-ai-vacuity3/RecProp.lean`, Prop-valued and recursive definitions, with a planted `NatT2`

sha256 `e5686ab0e81d110084d68e86233d6ca4db364c1808836b44578e3c0e8bbcaf65`; its output `recprop.out` had sha256 `9e7c42d3ff14fd367e0c9bce11a946ea47389b810345d0c7cc724b727d6d628b`.

```lean
import ClassicalLean
/-! VACUITY-3 measurement (claude-ai, 2026-10-13), read-only: the library's definitions whose
type ends in `Prop` (after `forallTelescopeReducing`), and which of them are recursive (their
value names a `brecOn`, a recursor `rec`, or `WellFounded.fix`). This bears on the gap the
confirming review of `5344c16` left for a later gate order (`NatT2 | 0 => True | n + 1 =>
NatT2 n`). Predicted before running: rc 0; some dozens of Prop-valued definitions; zero to a few
recursive ones. -/
/-- Planted, the review's shape: predicted to be the one recursive definition found. -/
def ClassicalLean.ProbeRec.NatT2 : ℕ → Prop
  | 0 => True
  | n + 1 => NatT2 n

open Lean Meta

def recProp : MetaM Unit := do
  let env ← getEnv
  let mut props := 0
  let mut recs : Array Name := #[]
  for (n, ci) in env.constants.toList do
    let u := privateToUserName n
    unless (`ClassicalLean).isPrefixOf u do continue
    let .defnInfo di := ci | continue
    if (← findDeclarationRanges? n).isNone then continue
    let isPropValued ← forallTelescopeReducing di.type fun _ b => return b.isProp
    unless isPropValued do continue
    props := props + 1
    let cs := di.value.getUsedConstants
    if cs.any (fun c => c.isStr && (c.getString! == "brecOn" || c.getString! == "rec")) ||
        cs.contains ``WellFounded.fix then
      recs := recs.push u
  IO.println s!"PROPDEFS {props}"
  IO.println s!"RECURSIVE {recs.size} {recs.toList}"

#eval recProp
```

### A3: `/tmp/claude-ai-vacuity3/plan1_names.py`, the first plan's rows and Lean names, two parses

sha256 `be531e13eadfc12fe89571da5ac44dd02faa8774efdba78f88e8bb536874efed`; its output `plan1-names.tsv` had sha256 `c3cbda30b2abdfc0c749e1d31e69e85268967a3966abc14e339b0593b80a17a0`.

```python
"""VACUITY-3 measurement (claude-ai, 2026-10-13): the first plan's 71 rows and the names in their
Lean-names column. Two parses: (a) exactly as MATH-PLAN-library-2-checks.py's r1.backfill check
(split on every unescaped `|`), and (b) a cell split that ignores `|` inside backticks, which some
rows' formulas contain (`‖·‖`, `|x|`). Writes plan1-names.tsv from parse (b): item, names, module."""
import re

LANE = "/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md"
lp = open(LANE, encoding="utf-8").read().split("## 4. The ranked list", 1)[1].split("## 5.", 1)[0]
NAME = r"`([A-Za-z][A-Za-z0-9_.']*)`"


def cells_b(line):
    out, cur, code, i = [], "", False, 0
    while i < len(line):
        ch = line[i]
        if ch == "\\" and i + 1 < len(line) and line[i + 1] == "|":
            cur += "|"; i += 2; continue
        if ch == "`":
            code = not code
        if ch == "|" and not code:
            out.append(cur.strip()); cur = ""
        else:
            cur += ch
        i += 1
    out.append(cur.strip())
    return out[1:-1]


rows_a, names_a, rows = 0, set(), []
for line in lp.splitlines():
    cc = [x.strip() for x in re.split(r"(?<!\\)\|", line)[1:-1]]
    if len(cc) >= 7 and re.match(r"^\d+$", cc[0]):
        rows_a += 1
        names_a |= set(re.findall(NAME, cc[3]))
    cb = cells_b(line)
    if len(cb) >= 7 and re.match(r"^\d+$", cb[0]):
        rows.append((int(cb[0]), re.findall(NAME, cb[3]), cb[4]))
names_b = {n for _, ns, _ in rows for n in ns}
print("parse a (the check's): rows", rows_a, "distinct names", len(names_a))
print("parse b (backticks kept whole): rows", len(rows), "distinct names", len(names_b))
print("only in a:", sorted(names_a - names_b))
print("only in b:", sorted(names_b - names_a))
with open("plan1-names.tsv", "w", encoding="utf-8") as f:
    for i, ns, mod in sorted(rows):
        f.write(f"{i}\t{' '.join(ns)}\t{mod}\n")
```

### A4: `/tmp/claude-ai-vacuity3/Resolve89b.lean`, resolve the names against the library

sha256 `72495ed50244a517c92c91732aebe34b978258e39c48b4cceb9fb5e7800ebb49`; its output `resolve89b.out` had sha256 `de6f8ba9b251bce95180526fd690391441700cf9851fa9ae48d9467f7020d5bf`.

```lean
import ClassicalLean
/-! VACUITY-3 measurement (claude-ai, 2026-10-13), read-only: resolve each name of the first plan's
Lean-names column (names89b.txt in the folder `$V3DIR`, default /tmp/claude-ai-vacuity3, one per line) against the library, by suffix under the
namespace `ClassicalLean` (private names through `privateToUserName`, as the census does).
Prints one line per match: `HIT <plan name> <full name> <kind> <hyps>` where `hyps` counts the
non-instance binders whose type is a proposition, binders as written (`forallTelescope`; the
second run, names89b.txt: the plan's names and the 8 names inferred for the 7 renamed ones), and `MISS <plan name>` when nothing matches.
Predicted before running: rc 0; most names hit once; a few miss (renamed by their orders). -/
open Lean Meta

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"

def resolve89 : MetaM Unit := do
  let dir := (← IO.getEnv "V3DIR").getD "/tmp/claude-ai-vacuity3"
  let ls ← IO.FS.lines (dir ++ "/names89b.txt")
  let wanted : Std.HashSet String := ls.foldl (fun s l => if l.trimAscii.toString.isEmpty then s else s.insert l.trimAscii.toString) {}
  let env ← getEnv
  let mut hits : Std.HashMap String (Array String) := {}
  for (n, ci) in env.constants.toList do
    let u := privateToUserName n
    unless (`ClassicalLean).isPrefixOf u do continue
    if n.isInternal && !(n != u) then continue
    -- every dotted suffix of the user name, e.g. `IsSufficient.raoBlackwell` and `raoBlackwell`
    let comps := u.components.map (·.toString)
    let k := comps.length
    for i in [0:k] do
      let s := ".".intercalate (comps.drop i)
      if wanted.contains s then
        let hyps ← forallTelescope ci.type fun xs _ => do
          let mut c := 0
          for x in xs do
            let d ← x.fvarId!.getDecl
            if d.binderInfo.isInstImplicit then continue
            if ← isProp d.type then c := c + 1
          return c
        let line := s!"{u} {kindOf ci} {hyps}{if n != u then " private" else ""}"
        hits := hits.insert s ((hits.getD s #[]).push line)
  for l in ls do
    let p := l.trimAscii.toString
    if p.isEmpty then continue
    match hits.get? p with
    | some arr => for h in arr do IO.println s!"HIT {p} {h}"
    | none => IO.println s!"MISS {p}"

set_option maxHeartbeats 4000000 in
#eval resolve89
```

### A5: `/tmp/claude-ai-vacuity3/targets89.py`, item 89's target table

sha256 `415ad9ff4623c66c009e0ea77a21b656a4bcc7e10459d94dda232889dde7d683`; its output `targets89.tsv` had sha256 `ffaa9192c81773cc0fba854f12c76fa811cc218a2b913494609848e4e3a36381`.

```python
"""VACUITY-3 (claude-ai, 2026-10-13): item 89's target table, from resolve89b.out (Resolve89b.lean's
output at bf9922b) and plan1-names.tsv (the first plan's rows, parse b). One row per library
theorem with at least one hypothesis as written: plan item(s), plan name, library name, the
number of hypotheses, its module file (text search, as examples89.py), and whether an `example`
in that file (with the docstring above it) already names it. Run from the repository root:
python3 -I targets89.py <folder holding resolve89b.out and plan1-names.tsv> > targets89.tsv"""
import re
import sys
from pathlib import Path

d = Path(sys.argv[1])
RENAMED = {  # plan name -> library names, inferred from names and modules; VACUITY-3's J1 confirms
    "abs_sub_eulerStep_le": ["abs_sub_eulerIterate_le"],
    "sum_two_pow_neg_len_div_le_one": ["sum_inv_two_pow_length_le_one"],
    "measureReal_len_le_sub_le": ["measureReal_len_add_le_le"],
    "norm_vecMul_pow_sub_le": ["sum_abs_vecMul_pow_sub_le"],
    "isSufficient_sum_bernoulli": ["isSufficient_numHeads"],
    "isComplete_sum_bernoulli": ["isComplete_numHeads"],
    "sampleMean_isMinVariance": ["variance_sampleMean_le", "eq_sampleMean_of_variance_eq"],
}
items = {}
for line in (d / "plan1-names.tsv").read_text(encoding="utf-8").splitlines():
    it, names, _ = line.split("\t")
    for n in names.split():
        items.setdefault(n, []).append(it)
hits = {}
for line in (d / "resolve89b.out").read_text(encoding="utf-8").splitlines():
    p = line.split()
    if p and p[0] == "HIT" and p[3] == "theorem":
        hits[p[1]] = (p[2], int(p[4]))
rows = []
for plan, its in items.items():
    for lib in RENAMED.get(plan, [plan]):
        if lib in hits and hits[lib][1] >= 1:
            rows.append((min(int(i) for i in its), ",".join(its), plan, hits[lib][0], hits[lib][1]))
src = {f: f.read_text(encoding="utf-8") for f in sorted(Path("ClassicalLean").rglob("*.lean"))}


def examples(text):
    lines, out, i = text.splitlines(), [], 0
    while i < len(lines):
        if lines[i].startswith("example"):
            j = i + 1
            while j < len(lines) and (lines[j] == "" or lines[j][0] in " \t"):
                j += 1
            k = i
            if i > 0 and lines[i - 1].rstrip().endswith("-/"):
                k = i - 1
                while k > 0 and not lines[k].lstrip().startswith("/--"):
                    k -= 1
            out.append("\n".join(lines[k:j]))
            i = j
        else:
            i += 1
    return out


print("item\tplan name\tlibrary name\thypotheses\tmodule file\tan example names it")
for _, its, plan, full, h in sorted(rows):
    last = full.split(".")[-1]
    pat = re.compile(r"^(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+(?:[\w.']*\.)?"
                     + re.escape(last) + r"(?=[\s:({\[])", re.M)
    fs = [f for f, s in src.items() if pat.search(s)]
    f = fs[0] if len(fs) == 1 else None
    named = f is not None and any(re.search(r"(?<![\w.']){}(?![\w'])".format(re.escape(last)), e)
                                  for e in examples(src[f]))
    print(f"{its}\t{plan}\t{full}\t{h}\t{f.as_posix() if f else 'AMBIGUOUS ' + str(len(fs))}\t{'yes' if named else 'no'}")
```

### A6: `/tmp/claude-ai-vacuity3/Witness89Probe.lean`, three witnesses in rule 2's form

sha256 `807f9e4c60a6248b64afd7fa85e49cdca9f8c46c7d0827c722e886ccc8ff30f3`.

```lean
import ClassicalLean.Probability.FiniteChain
import ClassicalLean.Algebra.HadamardInequality
import ClassicalLean.Probability.TailBounds
/-! VACUITY-3 probe for item 89 (claude-ai, 2026-10-13), read-only: the witness form the order
proposes, an `example` that applies the theorem itself at concrete arguments and proves each
hypothesis, so Lean checks that the hypotheses met are the theorem's own. Three theorems of items
34, 37 and 28. Third version, after the order's two cold reviews: the first witness is off the
boundary `δ = 1/2` (where the theorem's own constant `1 - card n * δ` is `0`); the third says why
each hypothesis holds; each block carries its own `open … in`, relies on no `open` of this file,
and names every argument it chooses. Predicted before running: rc 0, no error, no warning. -/

open Matrix in
/-- The hypotheses of `existsUnique_vecMul_eq_self` hold together: the `2 × 2` matrix with rows
`(3/4, 1/4)` and `(1/4, 3/4)`, each row summing to `1`, every entry at least `δ = 1/4 > 0`; the
theorem's constant `1 - 2 δ` is `1/2`, not `0`. -/
example := ClassicalLean.Probability.existsUnique_vecMul_eq_self (n := Fin 2)
  (P := !![3 / 4, 1 / 4; 1 / 4, 3 / 4]) (δ := 1 / 4)
  (fun i => by fin_cases i <;> norm_num [Fin.sum_univ_two])
  (by norm_num)
  (fun i j => by fin_cases i <;> fin_cases j <;> norm_num)

open Matrix in
/-- The hypotheses of `det_le_prod_diag` hold together: the `2 × 2` identity matrix is positive
semidefinite. -/
example := ClassicalLean.det_le_prod_diag (n := Fin 2) (A := (1 : Matrix (Fin 2) (Fin 2) ℝ))
  PosSemidef.one

open MeasureTheory in
/-- The hypotheses of `measureReal_gt_ge` hold together: on `Bool` with the point mass at
`true` (a probability measure), `X = 1` has mean `1 ≥ 0` because `X` is positive, not because
the measure is trivial, and `θ = 1/2` lies in `[0, 1]`. -/
example := ClassicalLean.Probability.measureReal_gt_ge (Ω := Bool) (μ := Measure.dirac true)
  (X := fun _ : Bool => (1 : ℝ)) (by simp) (θ := 1 / 2) (by norm_num) (by norm_num)
```
