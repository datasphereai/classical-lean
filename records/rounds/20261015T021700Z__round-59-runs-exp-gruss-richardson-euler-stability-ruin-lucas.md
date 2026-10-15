# Round 59 — no run of losses below an exponential, Grüss's inequality, Richardson's identity for Simpson's rule, Euler stability, the ruin chance as Lucas numbers (order LEAN-29)

Session: Claude Code `session_01SprMWhWWPFRjpDo2LjJXrf` on DSMain, as dustin, executing order
`LEAN-29` (`records/orders/20261015T021600Z__claude-ai__order-lean29-runs-exp-gruss-richardson-euler-stability-ruin-lucas.md`),
batch 3 (items 91 to 95) of the plan `/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library-2.md`
(sha256 6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166), and its job 0 (two older
docstring lines, store row 20261013-017, item 2), in the worktree `~/lean/classical-lean-paper-crypto`
on branch `lean-29`, made from `origin/master` = `20303cd` (equal to `git ls-remote github master`).
Lean and Mathlib v4.34.0. Nothing pushed. Evidence: `~/lean/lean29-checks/` (outside the
repository), `evidence.log` (UTC time, label, rc, prediction, command per run). Plan: lane
`lean/LEAN-29-PLAN.md` (sha256 051a18a57e4c8d95d76a81228b5e2ca9b9d3148f59a23b5d7232b19dc13fd832),
approved by Dustin on 2026-10-15 (UTC; 2026-10-14 about 22:12 EDT).

First part written before any Lean file changed; completed after the work, below.

## Files this round changes

Module files, each spelled in full:

* item 91: `ClassicalLean/Probability/LongestRun.lean` (extended; gains an import of
  `Mathlib.Analysis.Complex.Exponential`);
* item 92: the new module `ClassicalLean/Analysis/Gruss.lean` (`ClassicalLean.Analysis.Gruss`);
* item 93: `ClassicalLean/Analysis/Simpson.lean` (extended; gains an import of
  `Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule`);
* item 94: `ClassicalLean/Analysis/EulerMethod.lean` (extended);
* item 95: `ClassicalLean/Probability/GamblersRuin.lean` (extended; gains an import of
  `ClassicalLean.NumberTheory.LucasSequence`);
* job 0: `ClassicalLean/Analysis/ConvexConjugate.lean` and
  `ClassicalLean/NumberTheory/PrimitiveDivisor.lean` (docstring lines and `example`s appended after
  the last line; no theorem, definition or proof changes);
* `ClassicalLean.lean`: one import line, for the new module.

Also, as the order allows: `tools/vacuity_reviewed.txt` (only if a helper is listed under job 2's
2c), `records/` (this fragment, `records/orders/INDEX.md`, `records/CLAIMS.md`, the order's copy,
and the new bridge baseline `records/bridges/LEAN-29/`), `HANDOFF.md` and `ROADMAP.md` (job 3).

Records files written by this session's commands, not by the evidence helper (HANDOFF.md rule 32):
the order's copy (by `cp` from the lane, its sha256 then checked equal to the order's,
`e878aca2d617e65af38de731ec7223ae6c0125cf47f8b9d2f45affb26c0b3151`, by `ev.sh --nolean`), this
fragment, the INDEX row and the CLAIMS row (by the editor tools).

The vacuity gate is used as VACUITY-3 left it. The two standing rules of round 58 apply (witnesses
apply the theorem itself; the report tool is re-run and its summary lines reported), and so does
the bridge search's standing rule of round 55.

## Completed after the work

Items 91 to 95 of MATH-PLAN-library-2 are proved, no `sorry`, no new axiom, and job 0 is done.
**Narrowing: none.** **Wider:** item 95's `measureReal_hit_eq_lucasU` asks no `p ≠ 1/2`, so it is
wider than item 84's `measureReal_hit_eq_of_biased` (at `p = 1/2` its formula is the fair walk's
`b / (a + b)`); the order planned this widening. Item 95's `p = 1/2` case closed on its first
elaboration (`i95-1`, 2026-10-15T02:38:06Z), inside the order's 30-minute stop rule; no `p ≠ 1/2` was
added.

Commits on `lean-29` (from `20303cd`; nothing pushed), with each module's cold review and
confirming passes (BLOCKER/MAJOR/MINOR; files under `~/lean/lean29-checks/reviews/`, sha256 of
each `review.md` by script):

* job 0, `ClassicalLean/Analysis/ConvexConjugate.lean` and
  `ClassicalLean/NumberTheory/PrimitiveDivisor.lean`: cc3a802; review j0 PASS WITH FINDINGS
  0/0/4 (bdb0b4466068d1e7aaf61d28a3f6629ad230bc769009ff4148264a627d92d6b9); fix 0c3943b; confirming pass j0c PASS WITH FINDINGS 0/0/2
  (3d5ce5cc9b1783bb6dabdb510eaeb4e3d72edb8ac006b4ebcc4729ef90ecbe7b); fix ea3a8e0; confirming pass j0c2 PASS
  (4450c97ad03790063e8c1b7b12a2f60394340244e0c0684cc9cfac22f1119196). Census of both modules before and after each step equal, name for
  name (5 and 10 theorem constants; 6 and 11 constants). j0's finding 1 (four older passages of
  PrimitiveDivisor that cite elaborations not kept in the library) is outside job 0's two lines and
  is left for a later order.
* item 93, `ClassicalLean/Analysis/Simpson.lean`, `simpson_eq_trapezoidal` (no hypothesis, no
  witness): 56437cf; r93 PASS WITH FINDINGS 0/1/1 (a732ba17ffe6b63b2962b19e92354f6901ffb09e83265371264fdda7e738c8df); fix
  2b69223; r93c PASS (c109815b83539578aa901e6e4f7869b829dec5db9e249a9bcf20531094b7f183).
* item 94, `ClassicalLean/Analysis/EulerMethod.lean`, `tendsto_implicitEuler`,
  `tendsto_explicitEuler_iff`, two witnesses: 2ab8b9b; r94 PASS WITH FINDINGS 0/0/4
  (0ee57fab6e219a4ce725248b945c100d0d3514ba19a5762085f7d2ca16af879c); fix 01fb1ec; r94c PASS (c03da1b21c540ff878edf6ea65e2636a48a65c4c9b51e70f43e922956783e112).
* item 91, `ClassicalLean/Probability/LongestRun.lean`, `measureReal_no_run_le_exp`, witness
  `n = 2`, `r = 1`: 65ccb6c; r91 PASS WITH FINDINGS 0/0/1 (cdc66cb9fabec9f44bfa186a42118eb4209ffe89fe210d8ea377972876288bd6); fix
  cfdd9ac; r91c PASS WITH FINDINGS 0/0/1 (0d35cc1c966cf7c617bfabe2617d447066d480e14ad802f1f54829e10fa3b208); fix 82310b3; r91c2
  PASS (a66d187bf79d4cdd0508829d7e4a61354533416268c6d8c2eb678ed98eaf09f5).
* item 95, `ClassicalLean/Probability/GamblersRuin.lean` (now importing
  `ClassicalLean.NumberTheory.LucasSequence`), `measureReal_hit_eq_lucasU`, witness on `Fin 3`
  coins at `p = 1/3`: 8188a0d; r95 PASS WITH FINDINGS 0/0/2 (90912a8ee05d7e8eb71d1b7ea4cd452ec8a61b1c514d746360a58c5b1b78aec0); fix
  7e8b115; r95c PASS (741d68cd4b5a0d3aefb1e092f614b56734e63d9344b465535c1da1d7175936c7).
* item 92, the new module `ClassicalLean/Analysis/Gruss.lean` and one import line in
  `ClassicalLean.lean`, `abs_covariance_le_mul_div_four`, `abs_average_mul_sub_le`, two
  witnesses: 2bba7b6; r92 PASS WITH FINDINGS 0/0/4 (c6c3996d0a83708d03b80c412b06bec0d3d2ccd306b3ce98aa061d3ab2e59779); fix
  54c3624; r92c PASS WITH FINDINGS 0/0/2 (8076d031d7b845bfb8a6e752514837b5b79fef817fa9052ab1f8fffb2002a165), both findings on the
  fix commit's message, none on the module, so the module closed there (answered below).
* documents (job 3): 7ca9f6d; the bridge baseline `records/bridges/LEAN-29/` (job 4a,
  records only): 0ff0d44.

Every new witness is in round 58's form, with VACUITY-3 ruling 3's two rule-3 cases, each checked
by its module's reviewer. Every reviewer answered rule 1: no new conclusion is a recursive
all-`True` predicate. `~/.claude/agent-memory/` hashed before the first review and after the last:
equal. Dustin's ruling 1 of this order (lane `lean/LEAN-29-ruling-1.md`, sha256
25f70cd1dab65d1ff2c95c6090d5faa0caa074cf458037468c5911c3410aac92) arrived with every item
already closed inside rule 7's two rounds; no "third fix, docstrings only" was needed.

**Theorem constants, per module** (census of each module's source with order LEAN-28's census
tail, `.thmInfo` under `ClassicalLean`, labels `census_B_*`): LongestRun 38 → 40, Simpson 30 →
41, EulerMethod 14 → 16, GamblersRuin 68 → 69, Gruss 2, ConvexConjugate 5 → 5, PrimitiveDivisor
10 → 10: 3228 + 18 = 3246. Predicted blind by Method A at 3243 (a miss of 3: Simpson's four
`field_simp` calls made 7 `_simp_` helpers where 4 were estimated) and by Method B at 3246 (hit),
in `pred/prediction.txt` (74111d5808142c9e79841368b45eb03fa830f549f4483928d28ded3d1fb49d30).

**Records follow the clock** (HANDOFF.md rule 18):

* item 92's names. The commit message of 2bba7b6 says the names beyond A3 were probed first.
  In fact the probe `p92-1` (2026-10-15T02:43:50Z, rc 1) failed on three names
  (`ProbabilityTheory.variance_def'`, `MeasureTheory.ae_smul_measure`,
  `MeasureTheory.integrableOn_Icc_iff_integrableOn_Ioc`); the root-level
  `integrableOn_Icc_iff_integrableOn_Ioc` and `ProbabilityTheory.ae_cond_of_forall_mem` (used in
  place of the unknown `ae_smul_measure`) were then found by grep of Mathlib's sources, not probed
  by a `#check`; the first draft `i92-1` (2026-10-15T02:45:10Z, rc 1) failed only on the
  first of them (a lemma with an automatic argument needs brackets before `.mpr`), and `i92-2`
  (2026-10-15T02:45:23Z, rc 0) is the run that confirms both. Reviews r92 (finding 4) and r92c
  (findings A and B) found this.
* `pred/pred-gates.md` says it was written "about 23:01 EDT"; it was written about 22:58 EDT and
  hashed at 2026-10-15T02:58:17Z, before any of the runs it predicts.

**End checks** (job 4, on the clean tree):

* 4a, the bridge search at 54c3624 against `records/bridges/LEAN-28/`, under the 12G cap: rc 1;
  2437 pairs, 564 shape candidates, N = 122; 91 new (62 pairs, 29 shapes), 18 gone (pairs).
  Predicted (`pred-bridges.out`, beb867ef91810d4792cb750346cb452a0b3b0fbf13fcd01d87248c9411cc0199): the 29 new shapes exactly, 0 shapes gone,
  0 pairs gone by import; about 77 new pairs as a lower bound (a miss: 62, 52 of them predicted)
  and about 15 gone by the document-frequency cut (18, the 15 among them). Two real bridges, rows
  155 and 156, in the lane's new file `MATH-PLAN-library-2-bridges-2.md` (sha256
  f0aa214a6d747e6c5a95979cd329fbca85e046a303089e3e70d8aa8c20320119), neither load-bearing for items 96 to 110.
* 4b, the report tool at 54c3624, under the cap: rc 0, self-test 0 mismatches; 1792 written
  theorems; section A 1033 (0 close, 994 open, 39 dependent); section B 759 (16 close: 15 by
  `simp`, 1 by `positivity`; 743 open); section C 33 Prop-valued, 0 recursive; no `CLOSES` line
  names a theorem of this order. All as predicted.
* 4c, the six gates at 0ff0d44 (predicted in `pred/pred-gates.md`, 59ccad7129311ff555162ddc219d217cce565865482ae69b090ea0a092e5c223):
  build rc 0, 4171 jobs, 0 warnings; AxiomGate PASS 3246; VacuityGate PASS (1 reviewed helper,
  0 VACUOUS-PENDING, 0 run-outs, no UNCHECKED, no new flag), its tests 89 / 47 flagged / 3
  UNCHECKED as expected / 0 mismatches; check_sorry PASS 123; check_records PASS 123; gate 7
  (`~/lean/recheck/run-recheck.sh 0ff0d44 ~/lean/classical-lean-paper-crypto`, under the cap,
  rc 0): ALL PASSED for 0ff0d44, 4171 jobs, 123 modules 0 failed, 90647 declarations
  with no errors, the three standard axioms, 3246 theorems under `ClassicalLean`, the planted fault
  named (`LogDrag.mean_log_one_add_le`); 20:29.60, 4751320 KB. Every gate as predicted. Commits
  after the gates touch only `records/`.

No refused call (`NOT RUN`) in `evidence.log`; no Lean run in the night window.
