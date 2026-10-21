# Round 68 — the subgradient method, the Efron–Stein inequality, the capacity of the binary symmetric channel, Bernstein's inequality, order statistics (order CLOUD-MATH-3)

Session: Claude Code cloud session `session_01RDwAvLsB97mZBZzuHMzYsR`
(https://claude.ai/code/session_01RDwAvLsB97mZBZzuHMzYsR), executing order `CLOUD-MATH-3`
(`records/orders/20261021T002100Z__claude-ai__order-cloudmath3-subgradient-efron-stein-bernstein-order-statistics-bsc.md`),
items 113, 121, 130, 124 and 126 of MATH-PLAN-library-2 (rows below its cut), in a cloud container's
clone of GitHub `datasphereai/classical-lean` on branch `cloud-math-3`, from
`313e9a7009d025ebeddd84dd804a65ae605be672` (checked equal to `origin/cloud-math-3` before any
change). `git ls-remote origin master` at the start: `04e4a3842055026616256cf549ded9bf4bcfdd96`
(label `lsremote-start`). Lean and Mathlib v4.34.0 (`lake exe cache get`, 8908 files). The proofs
come from the five drafts in `incoming/` (the seven `.lean` files' sha256s, the five drafts and the
two witness starts, checked equal to `incoming/README.md`, and `sha256sum -c SHA256SUMS` passed in
`incoming/tools/` and `incoming/cm2-scripts/`, before any change); this round lands them, it does
not re-prove them. Evidence: `~/cm3-evidence/` (outside the repository), `evidence.log` (UTC time,
label, rc, prediction, command, output sha256 per run; `COMMIT <hash>` marker lines), copied to
`incoming/evidence/` at the end.

**The tool tests, run twice (rule 18).** The order's test command was first run while this
fragment's order copy already stood, untracked, in `records/orders/` (its mtime
2026-10-21T00:22:20Z, before the test). That run gave 40 `OK` lines and one `BAD`,
`repo-still-clean` (the test's last check, that the tree is clean after the tests): `git status
--porcelain` named only that file. Its output is kept (`ctools-test-dirty-tree.out`, label
`tools-test-dirty-tree`, sha256 `655061a5…`). The file was moved out of the tree, the test run
again on the clean tree: 41 `OK`, `BAD=0` (label `tools-test`, output sha256
`3fc1b6ebabad26085aca2e48e5d356e703eba48cfcc011dc7671f973b47cc700`, the value
`incoming/README.md` gives for DSMain's run), and the file put back after the starting counts.

**Order MERGE-2's push.** MERGE-2's INDEX State cell and CLAIMS row gain the clause the order
gives, "; pushed by Dustin: DSMain's master ref written 2026-10-20 19:18:05 EDT, GitHub master
equal (`04e4a38`)", measured by claude-ai on DSMain, not by this session (which cannot reach
DSMain); what this session measured is `git ls-remote origin master` above, GitHub's master at
`04e4a38…`. Nothing else in those rows changes. Round 68 was free on `origin/master` at the start
(`git ls-tree`, label `round68-free`: 0 files named `round-68`).

First part written before any Lean file changed; completed after the work, below.

## Modules this round adds (five new modules)

* item 113: `ClassicalLean/Analysis/SubgradientMethod.lean` (`ClassicalLean.Analysis.SubgradientMethod`),
  from `incoming/d113-r1-s1.lean`;
* item 121: `ClassicalLean/Probability/EfronStein.lean` (`ClassicalLean.Probability.EfronStein`),
  from `incoming/d121-r3-s1.lean`;
* item 130: `ClassicalLean/InformationTheory/ChannelCapacity.lean`
  (`ClassicalLean.InformationTheory.ChannelCapacity`), from `incoming/d130-r1-s1.lean`;
* item 124: `ClassicalLean/Probability/BernsteinInequality.lean`
  (`ClassicalLean.Probability.BernsteinInequality`), from `incoming/d124-r4-s2.lean`, its witness
  from `incoming/witness-starts/w124-tail.lean`;
* item 126: `ClassicalLean/Probability/OrderStatistics.lean` (`ClassicalLean.Probability.OrderStatistics`),
  from `incoming/d126-r2-s2.lean`, its witness from `incoming/witness-starts/w126-tail.lean`;
* `ClassicalLean.lean`: five import lines, at the end of its import block, in landing order.

No existing module changes. `tools/vacuity_reviewed.txt` changes only if a helper is listed (the
order's rule 3). Nothing else under `tools/` changes.

## Starting counts (measured in this session, before any new module, clean tree at `313e9a7`)

* `lake build`: rc 0, `Build completed successfully (4188 jobs).`, 0 lines with `warning:` (labels
  `start-build`, `start-build-warn`).
* `lake env lean tools/AxiomGate.lean`: rc 0, `axiom gate PASS — 3458 theorem constant(s) under
  [ClassicalLean], every one depending only on a subset of [propext, Classical.choice, Quot.sound];
  0 scoped exceptions` (label `start-axiom`).
* The base closure (rule 38's first use, `rootrun.sh`, label `closure-base`): the root build at
  `313e9a7` rc 0, 4188 jobs, 0 warnings, then `$EVD/closure-base.lean` (the order's four lines)
  rc 0, 5724 `MOD` lines (the whole import closure of `ClassicalLean`, Lean's own modules
  included; label `closure-base-count`), 136 of them `ClassicalLean` (the 135 modules and the root;
  label `closure-base-kinds`, whose logged prediction, 136 plus the root, was one too many). In
  `evidence.log` the `closure-base-build` line (line 14) comes before the `closure-base` line
  (line 15) and both name head `313e9a7009d025ebeddd84dd804a65ae605be672` (label `rule38-order`):
  rule 38's test with the real build.

## Proof changes and warning fixes, by item (written as each item lands)

## Steps out of the order's sequence (rule 18)

## Completed after the work
