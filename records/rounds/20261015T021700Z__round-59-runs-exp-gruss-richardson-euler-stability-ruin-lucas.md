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
