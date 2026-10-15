# Round 60 — Han's inequality, Frank–Wolfe on the simplex, state prices, Pólya's urn, the reflection principle (order CLOUD-MATH-1)

Session: Claude Code cloud session `session_01HV9mMLe9qSe13nN9hMyEBJ`
(https://claude.ai/code/session_01HV9mMLe9qSe13nN9hMyEBJ), executing order `CLOUD-MATH-1`
(`records/orders/20261015T023648Z__claude-ai__order-cloudmath1-han-frank-wolfe-state-prices-polya-reflection.md`),
items 131, 135, 136, 137 and 139 of MATH-PLAN-library-2 (rows below its cut), in a cloud container's
clone of GitHub `datasphereai/classical-lean` on branch `cloud-math-1`, from
`e2fac6da5992ea3e7d3f55ba31420e44039d7b42` (checked equal to `origin/cloud-math-1` before any
change). `git ls-remote origin master` at the start: `20303cd4eb902e15b2d4994ea6aa2263f5146264`.
Lean and Mathlib v4.34.0 (`lake exe cache get`). The proofs come from the five drafts in
`incoming/` (sha256s checked equal to `incoming/README.md` before any change); this round lands
them, it does not re-prove them. Round 59 is another session's and is not on this branch.

First part written before any Lean file changed; completed after the work, below.

## Modules this round adds (five new modules)

* item 131: `ClassicalLean/InformationTheory/HanInequality.lean`
  (`ClassicalLean.InformationTheory.HanInequality`), from `incoming/d131-r1-s1.lean`;
* item 135: `ClassicalLean/Analysis/FrankWolfe.lean` (`ClassicalLean.Analysis.FrankWolfe`), from
  `incoming/d135-r1-s2.lean`;
* item 136: `ClassicalLean/Analysis/StatePrices.lean` (`ClassicalLean.Analysis.StatePrices`), from
  `incoming/d136-r3-s2.lean`;
* item 137: `ClassicalLean/Probability/PolyaUrn.lean` (`ClassicalLean.Probability.PolyaUrn`), from
  `incoming/d137-r2-s1.lean`;
* item 139: `ClassicalLean/Probability/Reflection.lean` (`ClassicalLean.Probability.Reflection`),
  from `incoming/d139-r2-s1.lean`;
* `ClassicalLean.lean`: five import lines, at the end of its import block, in landing order.

No existing module changes. `tools/vacuity_reviewed.txt` changes only if a helper is listed (the
order's rule 3). Nothing else under `tools/` changes.

## Starting counts (measured in this session, before any new module)

* `lake build` at `e2fac6d`: rc 0, `Build completed successfully (4170 jobs).`, 0 lines with
  `warning:`.
* `lake env lean tools/AxiomGate.lean` at `e2fac6d`: rc 0, `axiom gate PASS — 3228 theorem
  constant(s) under [ClassicalLean], every one depending only on a subset of [propext,
  Classical.choice, Quot.sound]; 0 scoped exceptions`.
* 122 `.lean` files under `ClassicalLean/`.
