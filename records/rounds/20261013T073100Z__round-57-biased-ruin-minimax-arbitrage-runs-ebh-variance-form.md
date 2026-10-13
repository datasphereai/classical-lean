# Round 57 — the biased walk, minimax for every matrix, arbitrage counterexamples, runs, e-BH for compression scores, the variance product form (order LEAN-28)

Session: Claude Code `session_01CJNTgEfU5v3FmgQzLoqchA` on DSMain, as dustin, executing order
`LEAN-28` (`records/orders/20261013T073000Z__claude-ai__order-lean28-biased-ruin-minimax-arbitrage-runs-ebh-variance-form.md`),
batch 2 (items 84 to 88) of the plan `/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library-2.md`
(sha256 6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166), and item 80b (the product form of item 80, which
LEAN-27 left unstated), in the worktree `~/lean/classical-lean-paper-crypto` on branch `lean-28`, made
from `origin/master` = `deb08cb` (equal to `git ls-remote github master`). Lean and Mathlib v4.34.0.
Nothing pushed. Evidence: `~/lean/lean28-checks/` (outside the repository), `evidence.log` (time,
label, rc, prediction, command per run).

First part written before any Lean file changed; completed after the work, below.

## Modules this round changes (no new module)

* item 84: `ClassicalLean/Probability/GamblersRuin.lean` (extended; gains an import of
  `ClassicalLean.Probability.MaximalInequality`);
* item 85: `ClassicalLean/Analysis/FiniteGame.lean` (extended);
* item 86: `ClassicalLean/Combinatorics/ArbitrageCycle.lean` (extended: three `example`s);
* item 87: `ClassicalLean/Probability/LongestRun.lean` (the measurability hypothesis of
  `measureReal_no_run_le`: dropped, or the module says why it stays);
* item 88: `ClassicalLean/InformationTheory/CompressionTest.lean` (extended; gains an import of
  `ClassicalLean.Probability.EValueStepUp`);
* item 80b: `ClassicalLean/Probability/EffectiveSampleSize.lean` (extended: the product form
  `variance_sum_eq_mul_one_add`, with the hypotheses of `variance_sum_eq_of_stationary` only);
* `ClassicalLean.lean`: no change expected (no new module).

The vacuity gate is used as LEAN-27 left it (no change to `tools/` except a possible
`tools/vacuity_reviewed.txt` entry). Standing rule 2 of round 55 (the bridge search) applies.

## Completed after the work

Items 84 to 88 of MATH-PLAN-library-2 and item 80b are proved, no `sorry`, no new axiom. Narrowing:
none (nothing narrower than the plan's rows). Wider, each said in its module docstring: item 84's
`ae_exitTime_ne_top_of_biased` asks nothing of `p`; item 85 asks for no `Nonempty`; item 87's
measurability hypothesis is only for the trials `i < n`; item 88 adds the sharper `q · |H| / m`.
Item 88 is stated under a probability measure, the plan's expected share; a first draft for any
finite measure was false (through Lean's point-mass law of a string that is not measurable) and was
not committed. LEAN-27's item 80 narrowing (the product form not stated in Lean) is closed:
`variance_sum_eq_mul_one_add` in `Probability/EffectiveSampleSize`, with no extra hypothesis.

Commits on `lean-28` (from `deb08cb`; nothing pushed):

* `c5c004b` records before the work (this fragment's first part).
* `325c526` the six modules (items 84 to 88 and 80b); no new module, `ClassicalLean.lean` unchanged.
* Cold reviews' fixes, each closed by a confirming pass: `f328482`, `92dfa7b` (EffectiveSampleSize,
  r80b, two rounds); `6a1b65b`, `96f5cf7` (CompressionTest, r88, two rounds); `8b268ee`, `8cf6be5`
  (GamblersRuin, r84, two rounds); `d0e6b8e` (FiniteGame, r85); `3f4df2f` (ArbitrageCycle, r86);
  `e81ab8a` (LongestRun, r87: a satisfiability example, and `measurableSet_allLost` asks only for
  its block's trials).
* `1032cd3` HANDOFF.md and ROADMAP.md; `8ae25e2` the bridge baseline `records/bridges/LEAN-28/`.

Per-module theorem constants (census of scratch copies, the axiom gate's `.thmInfo` predicate under
`ClassicalLean`): GamblersRuin 51 → 68; FiniteGame 55 → 56; ArbitrageCycle 47 → 47; LongestRun
37 → 38 (one helper renumbered); CompressionTest 15 → 18; EffectiveSampleSize 63 → 72.

Whole-library numbers on the **clean** tree at `8ae25e2`: build 4170 jobs (two Mathlib modules
more, from `Mathlib.Probability.HasLawExists`), 0 warnings; AxiomGate PASS 3228 (3197 + 31);
VacuityGate PASS, 1 reviewed helper, 0 VACUOUS-PENDING, rule 5 ran out on 0 theorems, no UNCHECKED,
no new list entry (2:51.62, 5050648 KB); the gate's tests 88, 47 flagged, 0 mismatches; check_sorry
PASS 122; check_records PASS 122. Gate 7 at `1032cd3`, the last commit touching anything outside `records/`: ALL PASSED, 4170 jobs, 122 modules 0 failed, 90615 declarations no errors, three standard axioms, 3228, planted fault named (20:06.74, 4750424 KB); `8ae25e2` adds only `records/bridges/LEAN-28/` to `1032cd3`.

Bridge search (standing rule 2) against `records/bridges/LEAN-27/` at `1032cd3`: rc 1, 17 new (13
pairs, 4 shapes), 42 gone; `GamblersRuin × MaximalInequality` gone (now import-related). One new
bridge, row 154 (`GamblersRuin × LikelihoodScore`: item 84's Ville bound under only a conditional
up-chance at most `p`), in the lane's `MATH-PLAN-library-2-bridges.md`; not load-bearing for items
89 to 110, so the cut is not re-drawn. **Current baseline: `records/bridges/LEAN-28/`.**
Report: lane `lean/LEAN-28-report.md`.

### After Dustin's ruling on "checked in Lean" (2026-10-13)

Ruling: a claim in the library must be checkable from the library. Three docstrings of this order
(EffectiveSampleSize, cold review r80b; GamblersRuin, r84; LongestRun, r87) said a case was "checked
in Lean" while the check was a reviewer's scratch file outside the repository. Each check is now an
`example` at the end of its module (four examples), and each docstring names its example.
EffectiveSampleSize's older line on order LEAN-16's identity now says the check was review r6's own
scratch file, outside the library. No theorem, definition, proof or import changed; no named
constant added (census of each module before and after: the same constants, name for name).
Commits `b0b4f5e` and `c58db94`; confirming pass rx: PASS WITH FINDINGS 0/0/2 on `b0b4f5e`, fixed
in `c58db94`, then PASS.

Gates re-run on the clean tree at `c58db94`, all as predicted (`pred-gates2.md`, hashed first):
build 4170 jobs, 0 warnings; AxiomGate PASS 3228; VacuityGate PASS, output identical to the
first run (1 reviewed helper, 0 VACUOUS-PENDING, no UNCHECKED, no new list entry), its tests 88, 47
flagged, 0 mismatches; check_sorry PASS 122; check_records PASS 122; gate 7 at `c58db94`: ALL
PASSED, 4170 jobs, 122 modules 0 failed, 90615 declarations no errors (the same as at `1032cd3`),
three standard axioms, 3228, planted fault named (20:00.86, 4752100 KB).
`c58db94` is now the last commit touching anything outside `records/`. The bridge search was not
re-run: the change adds no declaration and changes no proof (the axiom gate's 3228 and gate 7's
declaration count are unchanged), so the baseline `records/bridges/LEAN-28/`, taken at `1032cd3`,
should describe `c58db94` too. That is reasoned, not measured.
