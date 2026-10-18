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

**Narrowing: none.** **Wider than the plan's reading, five conditions** (the order's Goal; claude-ai's ruling, Dustin's veto open): item 107 for any measure `ν₀`, and its first theorem with no "`F` differs from `F₀`" hypothesis; item 108 with no positive definiteness and no symmetry of `P`; item 109's law hypothesis; item 109 with pairwise independence only; item 110 with `q ≥ 0` and the support condition. Item 107's second theorem is an addition, not a widening.

**Done.** Items 106 to 110, every new main theorem with a witness in rule 2's form (seven; rule 2's
first try closed for items 107 and 109, `Measure.infinitePi`, so no fallback; item 106's equality
witnessed with the standard normal law, not the uniform law, for the reason its module gives), every
module reviewed cold and closed by a confirming pass:

* `ClassicalLean/InformationTheory/Channel.lean` (item 110): `sum_mul_comp_div_vecMul_le`; commits
  `14fa18f`, `204b767`; reviews r110 (0/0/2), r110c PASS.
* `ClassicalLean/Analysis/LinearODE.lean` (item 108): `quadForm_le_exp_mul`; commits `7df8665`,
  `aed6060`; reviews r108 (0/0/3), r108c PASS.
* `ClassicalLean/Probability/IntegralTransform.lean` (item 106, new, and its import line in
  `ClassicalLean.lean`): `measureReal_cdf_le_le`, `measureReal_cdf_le_eq_of_continuous`; it imports
  `Mathlib.Probability.CDF`, `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` and, for its witness,
  `Mathlib.Probability.Distributions.Gaussian.Real`, already in the closure (`a1-final3`); commits
  `ca4aa9e`, `379fec4`, `f821e6a`, `469910f` (the order's rule 7 third fix, docstrings only, with a
  code-only comparison and its negative control); reviews r106 (0/0/2), r106c (0/0/2), r106c2
  (0/0/1), r106c3 PASS.
* `ClassicalLean/Probability/GlivenkoCantelli.lean` (item 107): `eventually_lt_sup_abs_empiricalCDF_sub`,
  `eventually_lt_sup_abs_empiricalCDF_sub_of_tendsto`; it imports `Mathlib.Probability.HasLawExists`;
  commits `688905c`, `92ee811`; reviews r107 (0/0/4), r107c (0/0/1, records only).
* `ClassicalLean/InformationTheory/MethodOfTypes.lean` (item 109): `tendsto_neg_log_div_shannonEntropy`;
  it imports `Mathlib.Probability.StrongLaw` and `Mathlib.Probability.HasLawExists`; commits
  `0b652f5`, `160b865`; reviews r109 (0/0/2), r109c (0/0/1, records only).
* Documents: `HANDOFF.md` (§1, rules 38 and 39), `ROADMAP.md` (§1.24); commits `071528a`, `41cf780`;
  reviews d3 (0/0/4), d3c PASS.

**Theorem constants, per module** (census of each module's source, `.thmInfo` under
`ClassicalLean`, before at `8071e74` and after; labels `census_B_*`): Channel 5 → 6, LinearODE
2 → 3, MethodOfTypes 21 → 22, GlivenkoCantelli 16 → 18, IntegralTransform 0 → 2: 7 added, 3379 in
all; Method A, blind, said 3379 (range 3379 to 3383).

**Records follow the clock** (HANDOFF.md rule 18): items were landed and reviewed in the order 110,
108, 106, 107, 109, with each review running while the next item was drafted; each module's own fixes
came after its own review. Job 1's Method A and Method B ran after the five modules' builds and before
any gate. The bridge prediction's base used table is LEAN-31's kept one for the Lean tree of
`8071e74` (`used-8071e74-bridges2.tsv`), not a new dump at the records commit.

**Bridge search** (job 4a, `bridges`, through `rootrun.sh` at `071528a`): N = 129, 79 new pairs, 23
new shapes, 15 gone pairs, as predicted; one real bridge, row 159 (the Kolmogorov–Smirnov statistic
is distribution-free, GlivenkoCantelli × IntegralTransform), filed in the lane's
`lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md`, not in this batch; new baseline
`records/bridges/LEAN-32/` (commit `1c770ac`).

**End checks** (job 4, on the clean tree at `1c770ac`): build 4178 jobs, 0 warnings (`g1-build`);
AxiomGate PASS 3379 (`g2-axiom`); VacuityGate PASS, 1 reviewed helper, 0 VACUOUS-PENDING, 0 run-outs,
no UNCHECKED (`g3-vacuity`), its tests 89 / 47 flagged / 3 UNCHECKED as expected / 0 mismatches
(`g3-tests`); check_sorry PASS 130 (`g4-sorry`); check_records PASS 130 (`g5-records`); gate 7:
ALL PASSED for `1c770ac` (4178 jobs, 130 modules 0 failed, 91094 declarations with no errors, propext/Classical.choice/Quot.sound, 3379, planted fault `LogDrag.mean_log_one_add_le` named; 21 min 41 s, 4756968 KB) (`g7`); banned_vocab_scan PASS, 0 hits (`banned-scan`, not a gate). The report tool
(`report-after`, through `rootrun.sh`): 1868 written; A 1088 (0 close, 1049 open, 39 dependent);
B 780 (16 close); C 36, 0 recursive; no CLOSES line names a theorem of this order.
