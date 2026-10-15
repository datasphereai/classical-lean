# Round 62 — Hadamard for a covariance matrix, relative entropy along a chain, Bloomfield–Watson for a common mean, the plug-in compression score, Perron–Frobenius for a primitive chain (order LEAN-30)

Session: Claude Code `session_0148mpze7NidhsLJoJvBQsng` on DSMain, as dustin, executing order
`LEAN-30` (`records/orders/20261015T172700Z__claude-ai__order-lean30-hadamard-cov-chain-entropy-bloomfield-plugin-perron.md`),
batch 4 (items 96 to 100) of the plan `/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library-2.md`
(sha256 6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166), and its job 0 (five older
docstring lines, LEAN-29's review j0 finding 1 and review r92c's note), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `lean-30`, made from `origin/master` = MERGE =
`132e9d82a8e74944be325650fee9ba4134be76de` (order MERGE-1's pushed merge; equal to
`git ls-remote github master`). Lean and Mathlib v4.34.0. Nothing pushed. Evidence:
`~/lean/lean30-checks/` (outside the repository), `evidence.log` (UTC time, label, rc, prediction,
command per run). Plan: lane `lean/LEAN-30-PLAN.md` (sha256
f53f9e646bac6a412ca8b212b3704b73436bcf96996297025b1b51b16a0476c8), approved by Dustin on 2026-10-15
with three additions (claude-ai's ruling, store row 20261015-019). The lane file
`MATH-PLAN-library-2-bridges-2.md` is read at `0dea55c0…` (MERGE-1's row 157 appended), not the
order's `f0aa214a…`, by the ruling of store row 20261015-017.

First part written before any Lean file changed; completed after the work, below.

## Files this round changes

Module files, each spelled in full:

* item 96: `ClassicalLean/Probability/CovarianceDirections.lean` (extended; gains an import of
  `ClassicalLean.Algebra.HadamardInequality`);
* items 97 and 100: `ClassicalLean/Probability/FiniteChain.lean` (extended);
* item 98: `ClassicalLean/Statistics/GeneralizedLeastSquares.lean` (extended; gains an import of
  `ClassicalLean.Algebra.Kantorovich`);
* item 99: `ClassicalLean/InformationTheory/CompressionTest.lean` (extended; gains an import of
  `ClassicalLean.InformationTheory.Entropy` only if item 99 takes route (b));
* job 0: `ClassicalLean/NumberTheory/PrimitiveDivisor.lean` and `ClassicalLean/Analysis/Gruss.lean`
  (docstring and comment lines, and in PrimitiveDivisor at most one `example` appended after the
  last line; no theorem, definition, proof or existing `example` changes).

No new module; `ClassicalLean.lean` does not change. Also, as the order allows:
`tools/vacuity_reviewed.txt` (only if a helper is listed under job 2's 2c), `records/` (this
fragment, `records/orders/INDEX.md`, `records/CLAIMS.md`, the order's copy, and the new bridge
baseline `records/bridges/LEAN-30/`), `HANDOFF.md` and `ROADMAP.md` (job 3).

Records files written by this session's commands, not by the evidence helper (HANDOFF.md rule 32):
the order's copy (by `cp` from the lane inside `ev.sh --nolean`, label `order-copy`, its sha256
then checked equal to the order's,
`2452e0c6c9635f19b364e16ff315b9f0337450713b9ce8ad4578bb524b94a85d`), this fragment, the INDEX row
and the CLAIMS row (by the editor tools).

The vacuity gate is used as LEAN-29 left it. The standing rules of round 58 apply (witnesses apply
the theorem itself; the report tool is re-run and its summary lines reported), and so does the
bridge search's standing rule of round 55. Counts after MERGE are order MERGE-1's measured values
(4176 jobs, 3335 theorem constants, 128 modules; bridge baseline `records/bridges/MERGE-1/`), as the
order asks.
