# Round 64 — the probability integral transform, the Kolmogorov–Smirnov test's consistency, a Lyapunov bound, the asymptotic equipartition property, data processing for f-divergences (order LEAN-32)

Session: Claude Code `session_01Lqdistr7WXJn72iiS3PC1m` on DSMain, as dustin, executing order
`LEAN-32` (`records/orders/20261018T193500Z__claude-ai__order-lean32-pit-ks-lyapunov-aep-fdiv.md`),
batch 6 (items 106 to 110, the last batch above the plan's cut) of the plan
`/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library-2.md`
(sha256 6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `lean-32`, made from
`8071e74a04761d1ea0bbaac3fcabd7b1e1b6eb31` (order LEAN-31's last commit). Lean and Mathlib v4.34.0.
Nothing pushed. Evidence: `~/lean/lean32-checks/` (outside the repository), `evidence.log` (UTC
time, label, rc, prediction, command, output sha256 per run; `COMMIT <hash>` marker lines). Plan:
lane `lean/LEAN-32/plan.md` (sha256 176fc6fce08d324e62fc1d8d6fd536cfb4fb0331deab019e9951feff400033db),
approved by Dustin on 2026-10-18. The memory cap is the order's 12G.

**Order LEAN-31's push.** Both remotes are at `8071e74a04761d1ea0bbaac3fcabd7b1e1b6eb31`,
re-measured by `git ls-remote origin master` and `git ls-remote github master` before this fragment
was written (evidence label `lsremote`). Pushed by Dustin, 2026-10-16 19:39 EDT (lane
`lean/LEAN-31-CLOSE.md`, section 1, the reflogs). LEAN-31's INDEX State cell and CLAIMS row gain
that clause, and nothing else in them changes.

First part written before any Lean file changed; completed after the work, below.

## Files this round changes

Module files, each spelled in full:

* item 106: `ClassicalLean/Probability/IntegralTransform.lean` (new; imports `Mathlib.Probability.CDF` and
  `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`), and its import line in `ClassicalLean.lean`;
* item 107: `ClassicalLean/Probability/GlivenkoCantelli.lean` (extended; gains the import `Mathlib.Probability.HasLawExists`
  for its witnesses);
* item 108: `ClassicalLean/Analysis/LinearODE.lean` (extended);
* item 109: `ClassicalLean/InformationTheory/MethodOfTypes.lean` (extended; gains the imports
  `Mathlib.Probability.StrongLaw` and `Mathlib.Probability.HasLawExists`);
* item 110: `ClassicalLean/InformationTheory/Channel.lean` (extended).

Also, as the order allows: `tools/vacuity_reviewed.txt` (only if a helper is listed under job 2's
2c), `records/` (this fragment, `records/orders/INDEX.md`, `records/CLAIMS.md`, the order's copy,
and the new bridge baseline `records/bridges/LEAN-32/`), `HANDOFF.md` and `ROADMAP.md` (job 3).

Records files written by this session's commands, not by the evidence helper (HANDOFF.md rule 32):
the order's copy (by `cp` from the lane inside `ev.sh --nolean`, label `order-copy`, its sha256 then
printed equal to the order's, 923648ae5ea7952fc2982b8491932731a5a6a0f8f865477215b67cc90c355e8d), this
fragment, and the INDEX and CLAIMS rows (by `scripts/records_first.py`).

The vacuity gate is used as LEAN-31 left it. The standing rules of round 58 apply, and so does the
bridge search's standing rule of round 55. Counts at `8071e74` are order LEAN-31's measured values
(4177 jobs, 3372 theorem constants, 129 modules; bridge baseline `records/bridges/LEAN-31/`).

## Completed after the work
