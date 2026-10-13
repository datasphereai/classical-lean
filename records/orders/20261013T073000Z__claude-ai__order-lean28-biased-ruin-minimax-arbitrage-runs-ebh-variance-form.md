<!-- Written on 2026-10-13 by claude-ai; copied verbatim on 2026-10-13 (UTC) by Claude Code session_01CJNTgEfU5v3FmgQzLoqchA on DSMain from /opt/datasphere/lane/inbox/threads/staging/lean/LEAN-28-order.md (sha256 65e13493df7cd07962fe559f79419a6f05f09c1505b9217e8e0f211ffcd2c8e6, computed by script before this copy; equal to the hash in Dustin's prompt), as Dustin ordered in chat. Written before any Lean file changed, per records/README.md rule 2. -->

# LEAN-28 order: batch 2 of the library's second plan (items 84 to 88), and item 80's product form

Written 2026-10-13 by claude-ai for a plain Claude Code session on DSMain, as dustin, after
LEAN-27's push review (store rows 20261013-005 and 20261013-010). Lane files named here without a
folder are in /opt/datasphere/lane/inbox/threads/staging/; files named `lean/...` are in its new
subfolder /opt/datasphere/lane/inbox/threads/staging/lean/ (read `lean/README.md`). Plans, the
report and the push-review file go to `lean/` through ds_write_staging, since the lane is
read-only on disk for you.

Review: two passes by one fresh cold reviewer that had not seen it written. Pass 1: PASS WITH
FINDINGS (0 BLOCKER, 3 MAJOR, 12 MINOR). Pass 2: PASS WITH FINDINGS (0 BLOCKER, 0 MAJOR, 6 MINOR).
Every finding applied ("Revisions"). Not reviewed: anything that needs Lean to elaborate (no Lean
ran while the order was written, because of the night window).

Facts measured on DSMain by claude-ai on 2026-10-13 from 02:43 EDT (the first run's `date`), read-only, on
`lean-27` at `deb08cb` (the commit Dustin is to push), and relied on here:
- `lean-toolchain` is `leanprover/lean4:v4.34.0`; `~/lean/vacuity2-checks/mm` is at `2da3ab0a`.
- LEAN-27's last gates (at `ff68a8a`; `deb08cb` changes only `records/`): 4168 jobs, 0 warnings,
  AxiomGate PASS 3197, 122 modules, check_records PASS 122 (re-run by claude-ai at `deb08cb`: PASS,
  76 files searched, 1 exemption).
- MATH-PLAN-library-2-checks.py (sha256 below), run by claude-ai **without** `--lean` (the night
  window): 194 of 209 hit. The 15 misses: `setup.modules` (122), `setup.worktree` (`deb08cb`),
  `row.A2`, `row.A3`, `row.H6`, `row.X2` (LEAN-27's items 83, 82, 79, 81, now in the library),
  `row.F6` and `row.X15` (only LEAN-27 docstrings naming items 111 and 117:
  `ClassicalLean.Algebra.Kantorovich` lines 17 and 65, `ClassicalLean.Analysis.ConvexConjugate`
  line 57), and VACUITY-2's seven `gate.*` lines (`maxUnfolds`, `macro`, `helper`, `metacheck`,
  `test.lim_and_hyp`, `test.lim_false`, `list`). Every line of rows 84 to 88 hit: `row.X3` (both
  searches), `X3.X4.ruin`, `X3.ville`, `row.L2`, `trackL.L4`, `trackL.L15`, `trackL.L18`.
- Every module this order touches exists: `ClassicalLean.Probability.GamblersRuin` (581 lines;
  imports `ClassicalLean.Probability.FairGame` and two Mathlib files),
  `ClassicalLean.Probability.MaximalInequality` (imports Mathlib only),
  `ClassicalLean.Analysis.FiniteGame`, `ClassicalLean.Combinatorics.ArbitrageCycle` (0 `example`s),
  `ClassicalLean.Probability.LongestRun`, `ClassicalLean.InformationTheory.CompressionTest`
  (imported only by `ClassicalLean.lean`), `ClassicalLean.Probability.EValueStepUp` (imports
  Mathlib only), `ClassicalLean.Probability.EffectiveSampleSize`. So neither new import (item 84,
  item 88) can make a cycle, and no new module is made.
- Item 80b's route, by text search of the pinned Mathlib (`.lake/packages/mathlib`), not yet
  elaborated: `ProbabilityTheory.ae_eq_integral_of_variance_eq_zero`
  (`Mathlib/Probability/Moments/Variance.lean:162`, `[IsFiniteMeasure μ]`, `MemLp X 2 μ`),
  `ProbabilityTheory.covariance_self` (`Mathlib/Probability/Moments/Variance.lean:197`, `AEMeasurable X μ`),
  `ProbabilityTheory.evariance_eq_zero_iff` (`Mathlib/Probability/Moments/Variance.lean:181`). `covariance_const_left`
  (`Mathlib/Probability/Moments/Covariance.lean:81`) needs a probability measure, and
  EffectiveSampleSize's measure is only finite (its `variable` line 120), so it does not apply.

## Goal

Prove items 84 to 88 of MATH-PLAN-library-2.md (batch 2) in classical-lean, as that plan states
them, under the vacuity gate as LEAN-27 left it, by the plan's per-batch method (its section 8).
Add **item 80b**: the plan's product form of item 80, which LEAN-27 left unstated (LEAN-27's
records say so since `deb08cb`). Dustin pushes after claude-ai checks the result.

The six rows, one line each (the plan's section 5, "Batch 2", is the source for 84 to 88):
- 80b: `Var (X 0 + ⋯ + X (k − 1)) = k γ 0 (1 + 2 ∑_{1 ≤ j < k} (1 − j/k) ρ j)`, `ρ j = γ j / γ 0`,
  under the hypotheses of `variance_sum_eq_of_stationary` only; in
  `ClassicalLean.Probability.EffectiveSampleSize`. Section "Item 80b" below.
- 84: the biased `±1` walk (up with chance `p`, `0 < p < 1`, `p ≠ 1/2`, `q = 1 − p`, `r = q/p`): it
  leaves `(−b, a)` with chance 1, reaches `a` first with chance `(r^b − 1)/(r^(a+b) − 1)`, and when
  `p < q` Ville's inequality bounds the chance of ever reaching `a` by `(p/q)^a`; in `ClassicalLean.Probability.GamblersRuin`, which gains an import of
  `ClassicalLean.Probability.MaximalInequality`.
- 85: item 66's second proof of the minimax equality, extended from payoffs in `[0, 1]` to every
  real matrix by an affine change; in `ClassicalLean.Analysis.FiniteGame`.
- 86: item 65's exact counterexamples A1 to A3 as Lean `example`s; in
  `ClassicalLean.Combinatorics.ArbitrageCycle`.
- 87: `measureReal_no_run_le` without its measurability hypothesis, or the module says why it
  stays; in `ClassicalLean.Probability.LongestRun`.
- 88: compression scores, each against its own null law fixed in advance, fed to e-BH keep the
  expected false share at most `q`; in
  `ClassicalLean.InformationTheory.CompressionTest`, which gains an import of
  `ClassicalLean.Probability.EValueStepUp`.

No result from below the plan's cut is pulled in.

## Scope

- Branch `lean-28` from the commit Dustin pushed (`deb08cb`) in `~/lean/classical-lean-paper-crypto`.
  Nothing pushed. No sudo.
- You may change: the six modules above (none new), `ClassicalLean.lean` only if a module's import
  line must change there (none expected), `tools/vacuity_reviewed.txt` (job 2's 2c), `records/`, and
  `HANDOFF.md` and `ROADMAP.md` where they list modules, counts or results. Nothing in `tools/`
  otherwise: the gate is not changed in this order (its next fixes are order VACUITY-3's).
- Nothing under `~/trading` or `~/lean/recheck` is edited. `~/.config/classical-lean/banned-terms`
  is Dustin's: never edit it, never copy its patterns anywhere.
- The night window: start nothing that loads the library and could still be running at 02:30 EDT,
  and nothing between 02:30 and 05:45 EDT (cron 03:00 `daily_verify.sh`, cron 03:30
  `datasphere-backup.sh`, user timer 03:30 `lean-nightly`, cron 05:40 `ds-backup sync.sh`). Gate 7
  takes about 20 minutes. Check `crontab -l` and both `systemctl list-timers` lists again first.
  Reading, hash checks and the records-first commit may run inside the window.
- The memory cap: every run that loads the whole library (the gate, the plan's checks with
  `--lean`, `tools/bridge_search.py`, gate 7, a full build) runs under
  `systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0 <command>`; a run the cap kills
  is a stop. Never run two whole-library runs at once (`free -g` on DSMain, measured by claude-ai:
  62 GiB total, shared with the nightly jobs and any reviewer's probe).
- If you make a plan, write it to the lane as `lean/LEAN-28-PLAN.md` (then -PLAN-2, never
  overwriting) and report its sha256.

## Check, then read

Check these sha256s first; if any differs, stop and say which:
- this order, `lean/LEAN-28-order.md`: the value in Dustin's prompt;
- `lean/LEAN-28-check80b.py` `e22807bc6b50368749b4e00f24aae2e4932f2684fd2894d5ce8c131aded21e48`;
- MATH-PLAN-library-2.md `6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166`;
- MATH-PLAN-library-2-checks.py `92eedbc6598361a06a50bdf3a1b4fa1698c1d1d7a3dfe783cc79dd9c1c38307e`;
- LEAN-27-report.md `7a74cc2afdd80bf8003cb91b0f045fc090b7714acbc6634234540fcb9f5b4ffb`;
- LEAN-27-order.md `de8f6f000c9d4d0901c620f114988db9ed6bb83ff2c049d1b105c5626ce7d465`;
- LEAN-25-report.md `ab738eae5ac8b714d795f6a342bfb840fa4df414f37e814299e1cf4d202a6b0e`;
- LEAN-26-report.md `ce34f78d815b66673131ad01ac3cbb5b6047592f47e8f234fe7c4c8811fd8243`;
- LEAN-16-order.md `d494728c561a922b1227587395f9650f33dd3182791620e7a0d0fb6469f3120e`.

Then read: MATH-PLAN-library-2.md section 5's "Batch 2" table, section 6's rows 84 to 88, section
7's table header, section 8 in full; LEAN-27-order.md's sections "Scope", "Setup" and "Job 4" (this
order follows them where it does not say otherwise); LEAN-27-report.md in full (the report's model,
and its misses are rule 3's sources); LEAN-25-report.md's item 65 rows (lines 133 to 137; the
counterexamples A1 to A3 are lines 133 to 135); LEAN-26-report.md's sections on items 68 and 69; the "Known traps"
section of LEAN-16-order.md; `lean/README.md`. In the repo: `HANDOFF.md` (§4's gate text as
LEAN-27 left it), `records/README.md`, round 56's fragment, and the six modules' sources.

## Rules for this order

1. **The gate as LEAN-27 left it.** A theorem with verdict UNCHECKED fails the gate; for a main
   theorem it is a stop; on a helper the helper is rewritten or removed; it is never a list entry. A known gap stays until VACUITY-3: a predicate whose
   every case is `True` or a call to itself on a smaller argument (the shape
   `NatT2 | 0 => True | n + 1 => NatT2 n`) passes silently. Each module's cold reviewer checks that
   no main theorem's conclusion is such a predicate and says so in its verdict.
2. **A question to Dustin holds only its own outcome open.** If you ask him something, do not apply
   your own answer before he replies; the work it does not touch goes on (LEAN-27 applied its own
   answer to the NatT question first, and his ruling reversed it).
3. **Method A carries LEAN-27's lessons:** about one `_simp_` per term that `field_simp` closes
   inside a lemma it rewrites (7 from one call in LEAN-27), a `congr_simp` when a simp set rewrites
   under a definition from another module, and the old import closure counted with every module
   the last order added (LEAN-27 missed LEAN-26's four).
4. **Narrowing is said the same way everywhere.** Before the last records commit, the INDEX row,
   the round fragment's completed section and the report's "In short" each name every narrowing of
   this order, or each says "none". Check it on the report's draft, before the grep output goes in:
   `grep -n -i narrow <round 57 fragment> <report draft>` and
   `grep -n -i narrow records/orders/INDEX.md | grep 'LEAN-28'`; paste the output into the report.
   Round 57's line saying LEAN-27's item 80 narrowing is closed (rule 5) is expected and is not a
   LEAN-28 narrowing. (LEAN-27's INDEX row said "none narrower" and round 56 said "nothing
   narrower than the plan's rows" beside a report that named one, and the push waited for a fix.)
   INDEX rows start `| LEAN-NN |` (LEAN-27's, measured), so the filter finds this order's row.
5. **Item 80b closes LEAN-27's narrowing.** When it lands, EffectiveSampleSize's docstring
   (lines 89 to 91 at `deb08cb`) names `variance_sum_eq_mul_one_add` as the plan's product form with
   no extra hypothesis, and round 57's fragment says LEAN-27's item 80 narrowing is closed. LEAN-27's
   INDEX row and round 56 stay as they are.

## Setup

1. `git fetch origin`. origin/master and `git ls-remote github master` must both be `deb08cb`
   (`deb08cb656ef9ceaeeb74c8c7ffd226491fb9c0b`) and `git status` clean. If not, stop and report.
   Then `git switch -c lean-28 deb08cb`.
2. Evidence folder `~/lean/lean28-checks/` with `evidence.log` (time, label, rc, prediction,
   command). Every prediction file is hashed into the log before the run it predicts. Hashes go
   into records and the report by script, never typed; every compile-fix run through `el.sh` is
   logged.
3. **Records first**, the first commit on `lean-28`, no `.lean` file: this order's copy as
   `records/orders/<UTC>__claude-ai__order-lean28-biased-ruin-minimax-arbitrage-runs-ebh-variance-form.md`,
   its INDEX row, a CLAIMS row, and round 57's fragment naming the six modules and item 80b.
4. First build, at the records commit: predicted rc 0, 4168 jobs, 0 warnings (no module changed
   since `ff68a8a`). AxiomGate there, predicted PASS 3197: the base for the blind constant
   prediction. Job 1 predicts the build after the two new import edges by the import-closure method
   (inferred 4168 again: both imported modules and their Mathlib imports are already built).
5. The plan's checks (section 8, step 3) with `--lean`, using `~/lean/vacuity2-checks/mm` (at
   `2da3ab0a`). Predict "N of 232" before the run, line by line: the 15 misses claude-ai measured
   without `--lean` (header; `row.F6` and `row.X15` are only docstring mentions); and of the 23
   `--lean` lines (the script's lines 722 to 764, values pinned at `92f8ae5`), every one LEAN-27
   moved: `census.theorems` (3158, now 3197), `census.written`, `hyp1` to `hyp3`, `helpers` and
   `census.derived` (work each out from LEAN-27's 22 hand-written theorems and 4 `_proof_` helpers;
   the census counts hypotheses after unfolding definitions in the type, so `⊆` adds a binder), `used.lines`
   (56744), `bridges.modules` (119; `records/bridges/LEAN-27/pairs.tsv`'s header says N = 121) and
   `bridges.pairs` (2337; that header says 2422). Mark the four `bridges.rank` lines,
   `bridges.named` and `bridges.minquad` "may miss": scores move with module frequencies
   (`GamblersRuin × MaximalInequality` scores 120.0 in that file, against the script's 121.8).
   Every line of rows 84 to 88 must hit. Only a miss on a row 84 to 88 line means Mathlib or the
   library has that row by now: drop that row and say so. A `setup.*`, `gate.*`, `census.*`,
   `used.*` or `bridges.*` miss never drops a row.
6. Run `lean/LEAN-28-check80b.py` with `python3 -I`: predicted ALL OK, rc 0 (claude-ai's run:
   six HIT lines, output sha256 `437c69f95e5309d0d1f0c668cf2c399fb0738d04e69d88dbd99f1e57a257e346`).

## The work

Item 80b goes through jobs 1 to 4 with items 84 to 88: it is in job 1's blind prediction, its
statement goes through job 2's scratch file with `sorry`, its rows and EffectiveSampleSize's cold
review are job 2's, and its documents are job 3's. The section below adds only its statement,
route, rows and stop rule.

### Item 80b: the product form

The statement, beside `variance_sum_div_eq`, with exactly the hypotheses of
`variance_sum_eq_of_stationary`:

```
theorem variance_sum_eq_mul_one_add {k : ℕ} {X : Fin k → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ)
    {γ : ℕ → ℝ} (hcov : ∀ i j : Fin k, cov[X i, X j; μ] = γ (max (i : ℕ) j - min (i : ℕ) j)) :
    Var[fun ω ↦ ∑ i, X i ω; μ] =
      k * γ 0 * (1 + 2 * ∑ j ∈ Ico 1 k, (1 - (j : ℝ) / k) * (γ j / γ 0))
```

The route, from `variance_sum_eq_of_stationary`, in three cases:
- `k = 0`: both sides are `0`.
- `γ 0 ≠ 0` (and `k ≥ 1`): algebra, as in `variance_sum_div_eq`'s proof.
- `γ 0 = 0`: then every `γ j` with `1 ≤ j < k` is `0`, so both sides are `0`. Why: by `hcov` at
  `(0, 0)` and `covariance_self`, `Var (X 0) = γ 0 = 0`; by `ae_eq_integral_of_variance_eq_zero`,
  `X 0` equals its integral almost everywhere; so `cov (X 0, X j)`, the integral of
  `(X 0 − μ[X 0]) (X j − μ[X j])`, is `0`; and `hcov` at `(0, j)` makes it `γ j`.
  `lean/LEAN-28-check80b.py` checks with exact fractions that the identity alone fails here
  (first cell `k = 2`, `γ = (0, 1)`: product `0`, sum `2`), so this step is needed.

Elaborate every Mathlib name above with `#check @name`, and run `#print ProbabilityTheory.covariance`
(the route needs it to be the integral of the centred product), before relying on them.
Dropped-hypothesis rows: `hX` and `hcov`, with LEAN-27's cases (left side `1` against `0`, and `4`
against `0`). The script's P5 and P6 machine-check only the product form's `0`; their left sides
are written in, and `hX`'s case rests on LEAN-27's by-hand row (Lean's junk value `0` for the
covariance of a function outside `L²`). Satisfiability: the module's existing `example` already meets both hypotheses at
once; extend its docstring to name `variance_sum_eq_mul_one_add`. **Stop rule:** if the `γ 0 = 0`
case does not close with Mathlib's lemmas, leave the product form unstated, rewrite docstring
lines 89 to 91 to say plainly that it is narrower and why, report it, and go on.

### Items 84 to 88, by the plan's section 8

Section 8's steps 4 to 11 apply as written, with the additions below. The vacuity gate in step 9
is the gate as LEAN-27 left it; the gates are six: build, AxiomGate, VacuityGate, check_sorry,
check_records, gate 7 (the banned-vocabulary scan is retired).

**Job 1, predictions** (section 8, step 4): the job count, and the theorem-constant count blind
(Method A from source, then Method B by a census of scratch copies, the file re-hashed before the
first gate), both with rule 3. Also the bridge diff before its run (job 4a): item 84's import makes
`GamblersRuin × MaximalInequality` import-related, so that pair (rank 2 in
`records/bridges/LEAN-27/pairs.tsv`) and pairs related through it show as GONE;
`CompressionTest × EValueStepUp` is not in that file, so item 88's import removes no listed pair.
Count, as LEAN-27 did not, new pairs from the six extended modules' new constants and pairs gone
because shared constants crossed the document-frequency cut (LEAN-27's misses: 113 and 27).

**Job 2, statements, hypotheses and reviews** (section 8, steps 5 to 8), with:
- 2a. Every new main theorem with a hypothesis gets a satisfiability example in its module.
- 2b. Lean's junk values named in every dropped-hypothesis row where they decide the case. The
  plan names one: item 84 at `p = 0`, where Lean's values would give `1` for a chance that is `0`.
  Item 84's `p ≠ 1/2` is another: there `r = 1` and the formula is `0/0 = 0` in Lean, while the
  fair walk's chance is `b/(a+b)`. One is inferred, not measured: in item 85 a constant matrix
  (`M = m`) makes `(A − m)/(M − m)` divide by `0`, so `A` becomes the zero matrix; mapping back
  by `m + (M − m) v` may still give `m`, so check whether the case decides anything before
  giving it a hypothesis and a row.
- 2c. A vacuity flag on a short helper that only restates a definition is not a stop: remove it if
  Mathlib or `simp` already does its job, or list it in `tools/vacuity_reviewed.txt` as HELPER with
  a one-line reason checked by the module's cold reviewer. A flag or UNCHECKED on a main theorem,
  or any VACUOUS-PENDING entry, is a stop.
- 2d. Every review ends with a confirming pass on the fix diff only (the same reviewer by
  SendMessage, or a fresh one with that diff as its whole read list, about 15 calls); at most two
  fix-and-confirm rounds. If a module is still not clean after two, its item is reported as not
  closed, that item's changes are reverted before job 3, and the other items go on. A change to a
  module after its confirming pass gets its own confirming pass on that diff. A reviewer may elaborate at most two small Lean files, each
  under `systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=0`.
- 2e. A narrower statement than the plan's is said plainly in the module docstring, the report's
  item line and the hypothesis table, and rule 4 holds. A row whose plan statement turns out
  false is reported with its counterexample and narrowed, never dropped silently.
- 2f. Item 86: the three examples use ArbitrageCycle's own definitions for (a), (b) and (c), and A3
  uses its round function `bellmanFord w k j` (it takes weights, as A3 is given;
  `bellmanFord_stable_iff` is the statement A3 bears on). A1 and A2 give only off-diagonal rates,
  so choose diagonal rates that keep the stated side true (a self-loop is a cycle too) and say
  which; A3 gives `0` on the diagonal.
- 2g. Item 87: if the measurability hypothesis goes, the old statement must still follow from the
  new one, every use of the old theorem must still compile, and `measurableSet_allLost`'s own
  hypothesis is judged on its own; if it stays, the module docstring says why in one sentence.

**Job 3, documents.** `HANDOFF.md` and `ROADMAP.md` updated for the new results and counts.

**Job 4, the end checks, in this order:**
- 4a. The bridge search: `tools/bridge_search.py --diff records/bridges/LEAN-27/` under the memory
  cap, on a clean commit of jobs 1 to 3; rc 1 means candidates to review. Report NEW and GONE keys
  against job 1's prediction; check each NEW import-unrelated pair by hand for a theorem whose
  proof needs both sides; a real one gets an item number from 154 on and goes into the lane file
  MATH-PLAN-library-2-bridges.md (a later version is a whole new file, -bridges-2.md), with the
  plan's section 7 columns; it never enters this batch. Say for each real bridge whether it is
  load-bearing for a scheduled row (items 89 to 110); only that re-draws the cut, at a batch
  boundary. Write the new baseline to
  `records/bridges/LEAN-28/`; its commit touches only `records/`.
- 4b. Commit everything above. Then the six gates on the clean tree, predicted first, gate 7 under
  the memory cap
  (`systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0 ~/lean/recheck/run-recheck.sh <commit> ~/lean/classical-lean-paper-crypto`).
  After the gates, only commits that touch nothing outside `records/` are allowed.
- 4c. **Report** `lean/LEAN-28-report.md` through ds_write_staging, post_sha256 compared with your
  own sha256sum, laid out like LEAN-27-report.md: in short; setup; each item with its statements,
  hypothesis table, satisfiability example, review and any narrowing; rule 4's grep output;
  predicted beside measured for jobs, constants and every gate; list entries with reasons; the
  bridge diff and the baseline; documents changed; commits; misses and not reached; the push
  command as one line, not run:
  `cd ~/lean/classical-lean-paper-crypto && git push origin lean-28:master && git push github lean-28:master`.
- 4d. **Push-review file** `lean/LEAN-28-push-review.txt` through ds_write_staging, written by one
  script from the repository as it is after the last commit, each command followed by its full
  output: `git rev-parse HEAD`, `git status --porcelain`, `git ls-remote origin master`,
  `git ls-remote github master`, `git merge-base --is-ancestor deb08cb HEAD` with its exit code,
  `git rev-list --count deb08cb..HEAD`, `git log --name-only --format='== %h %cI %s' deb08cb..HEAD`,
  and `git show` of every commit after the last confirming review, and of every commit that touches
  a module after that module's own last confirming pass (files under `records/bridges/` as
  `--stat` only). Report its sha256. Then stop. claude-ai reviews it before Dustin pushes.

## Done means

- Branch `lean-28` from `deb08cb`, clean tree, nothing pushed; its first commit is the records
  commit and holds no `.lean` file; every prediction hashed in `evidence.log` before its run;
  hashes in records written by script; `el.sh` runs logged.
- Item 80b proved as stated, with its rows, the docstring change of rule 5 and round 57's line
  closing LEAN-27's narrowing, or stopped by its stop rule with the narrowing said plainly.
- Items 84 to 88 proved with no `sorry` and no new axiom, as the plan states them, or each
  narrowing said plainly with its reason; any dropped row named with the line that has it; any
  item not closed after two review rounds reported, its changes reverted.
- Every new main theorem with a hypothesis has a satisfiability example; every hypothesis has a
  dropped-hypothesis row, with Lean's junk values where they decide the case.
- Each changed module had its cold review after its statements were final, ending with a
  confirming pass, and each review answered rule 1's check; any statement changed after its review
  had a statement-equivalence review.
- Every new vacuity-list entry is named in the report with its reason and its reviewer's check; no
  VACUOUS-PENDING entry and no UNCHECKED verdict in the library.
- The job count and the constant count predicted (blind, before any census) beside measured.
- Job 3's documents changed and named; rule 4's three files agree and the grep is in the report.
- All six gates as predicted, or each miss reported; gate 7 ALL PASSED on the last commit that
  touches anything outside `records/`, and later commits touch only `records/`.
- The bridge diff run and reported against its prediction; the new baseline committed and named.
- The report and the push-review file are in `lean/` and their hashes match yours.

Then report in a few plain sentences: what was proved, any narrowing, the gate results, the new
list entries, the two files' hashes and the push command. Dustin reads your replies carefully and
is still learning to read code: use plain words and define a technical term the first time you use
it. When you need a decision from him, ask in one line with your recommended answer first.

## Revisions

- r1 (cold review 1, PASS WITH FINDINGS, 0 BLOCKER, 3 MAJOR, 12 MINOR; all applied except the
  pre-flight items, done after pass 2, and the load-bearing question, added in r2): the
  push-review file shows every commit after the last confirming review (it had shown only those
  after the last gate 7 run); item 80b placed inside jobs 1 to 4; setup 5 predicts "N of 232" with
  every `--lean` line LEAN-27 moved named, and says which misses never drop a row; item 84's
  `p ≠ 1/2` case added as a junk-value row, item 85's case marked as inferred and to be checked;
  2f names `bellmanFord` and A3's diagonal; LEAN-25 line range corrected; rule 4's quote, filter
  and order of steps fixed; setup 4 gives its numbers; job 1's bridge prediction uses the measured
  baseline (only `GamblersRuin × MaximalInequality` is in it) and LEAN-27's two bridge misses;
  P5 and P6 described as checking the right side only; `#print ProbabilityTheory.covariance` added;
  2d gets LEAN-27's fallback reviewer, an item-level stop and the reviewer's 6G limit; no two
  whole-library runs at once; UNCHECKED on a helper; the plan's hypotheses kept in the summaries;
  Done-means names round 57's closing line.
- r2 (confirming pass by the same reviewer, PASS WITH FINDINGS, 0 BLOCKER, 0 MAJOR, 6 MINOR, all
  applied; 13 of pass 1's 15 confirmed fixed, one partly, one deferred by design): `census.derived`
  and the census's unfolding named in setup 5; an item not closed after two rounds has its changes
  reverted, in 2d and Done-means; a change after a module's confirming pass gets its own pass and
  shows in the push-review file; job 4a asks whether a real bridge is load-bearing for items 89 to
  110; rule 4 names both of LEAN-27's quotes and the INDEX row's measured format; r1 reworded.
  Then the pre-flight: this order and `lean/LEAN-28-check80b.py` placed in the lane with their
  hashes compared, `lean/README.md` given a line for check scripts, and the review line filled.
