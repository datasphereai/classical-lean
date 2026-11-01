# Round 82 — the hat matrix's rank, the categorical covariance's pseudoinverse, one KKT multiplier for every minimiser, the chi-squared test, the largest eigenvalue by subgradients (order CLOUD-MATH-7)

Session: Claude Code cloud session `session_01HgueTXEfmRyGHEx4eHzyN9`
(https://claude.ai/code/session_01HgueTXEfmRyGHEx4eHzyN9), executing order `CLOUD-MATH-7`
(`records/orders/20261101T214207Z__claude-ai__order-cloudmath7-hat-rank-categorical-pinv-kkt-multipliers-chi-squared-test-eigenvalue-subgradient.md`),
bridge rows 170, 172, 168, 169 and 171 of `MATH-PLAN-library-2-bridges-2.md`, in a cloud container's
clone of GitHub `datasphereai/classical-lean` on branch `cloud-math-7`, from
`d723fbfd171cf9c018ddc0160446984ef1daffee` (checked equal to `origin/cloud-math-7` before any
change, `branch_start.txt`). `git ls-remote origin master` at the start:
`d723fbfd171cf9c018ddc0160446984ef1daffee` (`master_start.txt`). Lean and Mathlib v4.34.0
(`lake exe cache get`, 8908 files).

**No drafts.** The five statements were written by order LEAN-38 (a reading order) and given in
the order word for word; each bridge is proved by this session from its row's sketch, and no proof
comes from an earlier draft.

Evidence: `$HOME/cm7/` (outside the repository); every count below is read from a saved output
there, cited by its file name (rule 9).

First part written before any Lean file changed; completed after the work, below.

## Modules this round adds (five new modules)

* bridge 170: `ClassicalLean/Algebra/HatMatrixRank.lean` (`ClassicalLean.Algebra.HatMatrixRank`),
  importing `ClassicalLean.Algebra.Pseudoinverse` and `ClassicalLean.Statistics.Cochran`;
* bridge 172: `ClassicalLean/Algebra/CategoricalPseudoinverse.lean`
  (`ClassicalLean.Algebra.CategoricalPseudoinverse`), importing
  `ClassicalLean.Algebra.Pseudoinverse` and `ClassicalLean.Simplex.SecondOrder`;
* bridge 168: `ClassicalLean/Analysis/KKTMultipliers.lean` (`ClassicalLean.Analysis.KKTMultipliers`),
  importing `ClassicalLean.Analysis.GradientDescent` and `ClassicalLean.Analysis.KKT`;
* bridge 169: `ClassicalLean/Statistics/ChiSquaredTest.lean`
  (`ClassicalLean.Statistics.ChiSquaredTest`), importing `ClassicalLean.Probability.ChiSquared` and
  `ClassicalLean.Statistics.NeymanPearson`;
* bridge 171: `ClassicalLean/Analysis/EigenvalueSubgradient.lean`
  (`ClassicalLean.Analysis.EigenvalueSubgradient`), importing `ClassicalLean.Algebra.MinMax` and
  `ClassicalLean.Analysis.SubgradientMethod`;
* `ClassicalLean.lean`: five import lines, at the end of its import block, in landing order, each
  added by its module's landing commit.

No existing module changes. `tools/vacuity_reviewed.txt` changes only if a helper is listed (the
order's rule 4). Nothing else under `tools/` changes. `records/orders/INDEX.md` also gets order
LEAN-38's row (a reading order with no repository change), directly above this order's row, as the
order's Setup 5 asks.

## Starting counts (measured in this session, before any new module, clean tree at `d723fbf`)

* `lake build`: exit 0, `Build completed successfully (4206 jobs).`, 0 lines with `warning:`
  (`setup3_lake_build.txt`).
* `lake env lean tools/AxiomGate.lean`: `axiom gate PASS — 3914 theorem constant(s) under
  [ClassicalLean] …; 0 scoped exceptions` (`setup3_axiom.txt`).
* `python3 -I tools/check_sorry.py`: PASS, 153 files (`setup3_sorry.txt`).
* `python3 -I tools/check_records.py`: PASS, 153 modules, 1 named exemption (`setup3_records.txt`).
* `lake env lean tools/VacuityGate.lean`: PASS, 1 reviewed helper, 0 VACUOUS-PENDING, rule 5 out of
  heartbeats on 0 theorems (`setup3_vacuity.txt`).
* sha256 of each output: `setup_sha256.txt`.
