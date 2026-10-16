# Round 63 — the spectral density of a moving average, bounded completeness and Basu, Bayes equals minimax with infinite losses, three carried generalisations, Holm's step-down procedure (order LEAN-31)

Session: Claude Code `session_011sA11abhwhEtt7xhgzBBKC` on DSMain, as dustin, executing order
`LEAN-31` (`records/orders/20261016T214500Z__claude-ai__order-lean31-spectral-basu-bayes-carry-holm.md`),
batch 5 (items 101 to 105) of the plan `/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library-2.md`
(sha256 6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166), and its job 0 (the
Bloomfield and Watson credit, LEAN-30's thread 6), in the worktree `~/lean/classical-lean-paper-crypto`
on branch `lean-31`, made from `49c4c9833f4f49610ef710aa69531cb84490b6e1` (order LEAN-30's last
commit). Lean and Mathlib v4.34.0. Nothing pushed. Evidence: `~/lean/lean31-checks/` (outside the
repository), `evidence.log` (UTC time, label, rc, prediction, command per run). Plan: lane
`lean/LEAN-31-PLAN.md` (sha256 b3b5ca1d8751a8998e4a293b801eafb95897609757bec48a8d990bb0eeecb5d0),
approved by Dustin on 2026-10-16, with its job 0 proposal (both credits get the full, checked
reference). Dustin's ruling of 2026-10-16, with the approval: whole-library runs go under a 24G memory
cap, not the order's 12G (DSMain measured at 62.2 GiB; `~/CLAUDE.md` records it); still one at a time.

**Order LEAN-30's push.** Both remotes are at `49c4c9833f4f49610ef710aa69531cb84490b6e1`,
re-measured by `git ls-remote origin master` and `git ls-remote github master` before this fragment
was written (evidence label `lsremote`). Pushed by Dustin, 2026-10-16 13:16 EDT (store row
20261016-010). LEAN-30's INDEX State cell and CLAIMS row gain that clause, and nothing else in them
changes.

First part written before any Lean file changed; completed after the work, below.

## Files this round changes

Module files, each spelled in full:

* item 101: `ClassicalLean/Probability/MovingAverage.lean` (extended; no new import);
* item 102: `ClassicalLean/Statistics/Sufficiency.lean` (extended);
* item 103: `ClassicalLean/Analysis/FiniteGame.lean` (extended);
* item 104: `ClassicalLean/Statistics/ResidualVariance.lean`, `ClassicalLean/Probability/LikelihoodScore.lean` and `ClassicalLean/Probability/EffectiveSampleSize.lean` (extended; the last gains the imports
  `Mathlib.Probability.HasLawExists` and `Mathlib.Probability.Distributions.Gaussian.Real`);
* item 105: `ClassicalLean/Probability/StepDownProcedure.lean` (new; imports `Mathlib.MeasureTheory.Measure.Real`), and its import line in
  `ClassicalLean.lean`;
* job 0: `ClassicalLean/Statistics/GeneralizedLeastSquares.lean` (docstring and comment lines only).

Also, as the order allows: `tools/vacuity_reviewed.txt` (only if a helper is listed under job 2's
2c), `records/` (this fragment, `records/orders/INDEX.md`, `records/CLAIMS.md`, `records/README.md`'s
one sentence, the order's copy, and the new bridge baseline `records/bridges/LEAN-31/`), `HANDOFF.md`
and `ROADMAP.md` (job 3).

Records files written by this session's commands, not by the evidence helper (HANDOFF.md rule 32):
the order's copy (by `cp` from the lane inside `ev.sh --nolean`, label `order-copy`, its sha256 then
printed equal to the order's, 9a0df0902bab8de2d80bb2a59c872bb39b74b6657dbf1129466e5e7cfebc1242), this
fragment, the INDEX and CLAIMS rows and the README sentence (by `scripts/records_first.py`).

The vacuity gate is used as LEAN-30 left it. The standing rules of round 58 apply, and so does the
bridge search's standing rule of round 55. Counts at `49c4c98` are order LEAN-30's measured values
(4176 jobs, 3345 theorem constants, 128 modules; bridge baseline `records/bridges/LEAN-30/`).

## Completed after the work

**Narrowing: none.** **Wider than the plan's reading, two conditions** (the order's Goal;
claude-ai's ruling, Dustin's veto open): item 105 for any finite measure, not only a probability
measure; item 104's Chernoff bound with no `p₀ < 1`. Item 104's `q ≤ 1` and `0 < p₀` are kept
though not needed. Item 101's real-form corollary and item 102's implication
`IsComplete.isBoundedlyComplete` are additions, not widenings.

**Done.** Items 101 to 105 and job 0, every new main theorem with a witness in rule 2's form (nine;
item 104's r6 witness is rule 2's first try, `Measure.infinitePi`, so no exception was used),
every module reviewed cold and closed by a confirming pass:

* `ClassicalLean/Probability/MovingAverage.lean` (item 101): `sum_covariance_mul_cexp_eq`,
  `zero_le_sum_covariance_mul_cos`, private `sum_Icc_mul_cexp_eq_sum_sum`; commits `a6dbd5d`,
  `c645868`; reviews r101 (0/0/5), r101c (0/0/1, records only).
* `ClassicalLean/Statistics/Sufficiency.lean` (item 102): `IsBoundedlyComplete`,
  `IsComplete.isBoundedlyComplete`, `indep_of_isSufficient_of_isBoundedlyComplete_of_isAncillary`;
  commits `d7ecc39`, `222e526`; reviews r102 (0/0/3), r102c PASS.
* `ClassicalLean/Analysis/FiniteGame.lean` (item 103): `iSup_bayesRisk_eq_minimaxRisk_of_finite'`
  and three private lemmas, from `d3103-r1-s1.lean`; commits `82549ee`, `f4a61bb`; reviews r103
  (0/0/4), r103c PASS.
* `ClassicalLean/Statistics/ResidualVariance.lean`, `ClassicalLean/Probability/LikelihoodScore.lean`,
  `ClassicalLean/Probability/EffectiveSampleSize.lean` (item 104): the three primed theorems from
  `d3204-r4-s1.lean`; commits `593fca1`, `943ec0b`, `36610d2`; reviews r104 (0/0/5), r104c
  (0/0/1), r104c2 PASS.
* `ClassicalLean/Probability/StepDownProcedure.lean` (item 105, new, and its import line in
  `ClassicalLean.lean`): `holmRejected`, `measureReal_exists_holmRejected_true_le`; it imports
  `Mathlib.MeasureTheory.Measure.Real` and, for its witness, `Mathlib.Probability.UniformOn`, a
  module already in the closure (A1, `a1-final`); commits `f075da6`, `6231f3c`; reviews r105
  (0/0/5), r105c PASS.
* `ClassicalLean/Statistics/GeneralizedLeastSquares.lean` (job 0): docstrings only; commit
  `219dc39`; reviews j0 (0/0/1), j0c PASS.
* Documents: `HANDOFF.md` (§1, rules 36 and 37), `ROADMAP.md` (§1.23); commits `0bcf200`,
  `6763859`; reviews d3 (0/0/4), d3c (0/0/1, records only).

**Theorem constants, per module** (census of each module's source, `.thmInfo` under
`ClassicalLean`, before at `49c4c98` and after): MovingAverage 8 → 24, Sufficiency 55 → 58,
FiniteGame 56 → 60, ResidualVariance 3 → 4, LikelihoodScore 19 → 20, EffectiveSampleSize 72 → 73,
StepDownProcedure 0 → 1: 27 added, 3372 in all (labels `census_B_*`).

**Records follow the clock** (HANDOFF.md rule 18): items were landed and reviewed in the order
103, 104, 105, 102, 101, with reviews running while the next item was drafted; each module's own
fixes came after its own review. Job 1's Method A was written after the five items' module builds
and before any census or gate. The first bridge search and report tool runs (labels `bridges`,
`report-after`) read a stale `ClassicalLean` build and are void; both were rerun after a full
build (`build-pre4a`): `bridges2`, `report-after2`. Dustin's cap ruling of 2026-10-16 (24G, in the
first part above) was reversed by him the same evening: the order's 12G stands (`cap-ruling-2`);
four early runs (`build0`, `axiom0`, `report-before`, `checks0`) ran under 24G, peak 4.5 GB.

**Bridge search** (job 4a, `bridges2`, at `6763859`): N = 128, 89 new pairs, 11 new shapes, 75
gone pairs; one real bridge, row 158 (Holm's rejections inside Benjamini and Hochberg's), filed in
the lane's `lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md`, not in this batch; new
baseline `records/bridges/LEAN-31/` (commit `b420ff3`).

**End checks** (job 4, on the clean tree at `b420ff3`): build 4177 jobs, 0 warnings (`g1-build`);
AxiomGate PASS 3372 (`g2-axiom`); VacuityGate PASS, 1 reviewed helper, 0 VACUOUS-PENDING, 0
run-outs, no UNCHECKED (`g3-vacuity`), its tests 89 / 47 flagged / 3 UNCHECKED as expected / 0
mismatches (`g3-tests`); check_sorry PASS 129 (`g4-sorry`); check_records PASS 129 (`g5-records`);
gate 7 ALL PASSED for `b420ff3` (4177 jobs, 129 modules 0 failed, 91072 declarations with no errors, propext/Classical.choice/Quot.sound, 3372, planted fault `LogDrag.mean_log_one_add_le` named; `g7`); banned_vocab_scan PASS, 0 hits (`banned-scan`, not a gate). The report tool
(`report-after2`): 1861 written; A 1081 (0 close, 1042 open, 39 dependent); B 780 (16 close);
C 36, 0 recursive; no CLOSES line names a theorem of this order.
