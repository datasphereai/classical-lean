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

## Job 1 (before any proof entered a module)

* Probes (rule 37): one probe file per draft, written by script from a discovery run of the draft
  with the Goal list's cuts (`cut-<item>`, `disc2-<item>`, `mkprobes2-<item>`), each rc 0
  (`probes-113`, `probes-121`, `probes-130`, `probes-124`, `probes-126`: 28, 49, 23, 120 and 101
  names), and one for the original drafts' deprecated and dead-branch names (`probes-orig2`). One
  name does not resolve at this Mathlib: `Finset.measurable_sum'` (`probes-orig`, rc 1), used only
  in the dead first branch of 124's `hSmeas` chain, which the Goal list's cut removes. Two tokens
  added to `$EVD/allowlist.txt`, each with its reason: `_ℝ` (the notation `⟪x, y⟫_ℝ`) and
  `pp.fullNames` (the option of the type comparison's scratch files).
* Statement files (`$EVD/stmt/`), built by script from each draft (`mkstmt.py`: every statement
  and `def` body the draft's text, each proof `sorry`), each rc 0 with only `sorry` warnings
  (`stmt-<item>`), hashed (`stmt-files`). Targeted imports found by script (`locate-<item>`), each
  set tested on the whole cut draft, witness start included (`imports-113`, `imports4-121`,
  `imports-130`, `imports-124`, `imports-126`, rc 0).
* The type comparison (`typecmp3.py`, adapted from CLOUD-MATH-2's `typecmp.py`): every main
  theorem's and public definition's type the same as the draft's up to the namespace prefix, 20 of
  20 (`typecmp2-113`, `typecmp2-121`, `typecmp2-130`, `typecmp2-124`, `typecmp2-126`), and the
  bodies of the eight definitions too (`printcmp-121`, `printcmp-130`, `printcmp-126`); each kind's
  planted control reported `DIFF`, rc 1 (`typecmp2-planted`, `printcmp-planted`). No name of 130
  needed `ClassicalLean.Simplex.` in full.
* The statement review `rv1-statements`: FINDINGS 1 (MINOR), the docstring of 121's private
  `wvar_mix_le`; the fix, the docstring alone (`diff-121-fix`), confirmed by a fresh reviewer,
  `rv1c-confirm`: CONFIRMED.

## Proof changes and warning fixes, by item (written as each item lands)

Each module is assembled by `$EVD/scripts/assemble.py` (CLOUD-MATH-2's) from its statement file
and its draft's proof lines; the spec `$EVD/spec/a<item>.json` names every edit to a draft line,
and the assembler printed each one. Line numbers below are the draft's.

* **113** (`d113-r1-s1.lean`). No warning to fix, at 9c0639c (the Goal list) or here; the proof is
  the draft's lines 17 to 54 with no edit (`assemble-113`). The module's `lake build`: 0 warning
  lines (`build-113`, `build-113-warn`). Its witness is new (the item had no witness start): the
  function `y ^ 2 / 2` on the real line, the step `1 / 2`, `G = 1`, `z = 0`, `T = 3`. Its review,
  `rv2-113`: CLEAN, so no confirming pass.
* **121** (`d121-r3-s1.lean`). Lines 81, 93, 207, 220, 228 and 241: `show` became `change` (each
  changed the goal). The draft's namespace `EfronStein` is the module's
  `ClassicalLean.Probability.EfronStein`: its `end` (line 259) moved after the two main theorems,
  `open EfronStein` (line 261) is gone, and the prefix `EfronStein.` is dropped in the statements
  (lines 267 and 277, job 1) and the proofs (lines 268, 278, 280, 281, 282, 285, 287 and 289;
  `assemble2-121`, 14 edits). The private `wvar_mix_le`'s docstring (line 69) is job 1's fix.
  `Mathlib.Tactic.FinCases` is a seventh import, for the witnesses' `fin_cases` (without it
  `m121-a` rc 1, unknown tactic; with it `m121-b` rc 0). The module's `lake build`: 0 warning
  lines (`build-121`, `build-121-warn`). Its two witnesses are new (the item had no witness
  start): two coordinates in `Fin 2` with the weights `(1/4, 3/4)` and `(1/2, 1/2)`,
  `f = x 0 + 2 * x 1`, and `c = (1, 2)`. Its review, `rv2-121`: CLEAN, so no confirming pass.
* **130** (`d130-r1-s1.lean`). Lines 23, 25, 27, 29, 35, 97 and 117: `show` became `change` (each
  changed the goal). Lines 24 and 30: the deprecated `if_pos` became `ite_eq_left`; lines 26 and
  28: `if_neg` became `ite_eq_right` (`assemble-130`, 11 edits). The private `bscJoint` and its
  five lemmas are inside `ClassicalLean.InformationTheory.ChannelCapacity` with the two main
  theorems; `open ClassicalLean.Simplex` stays above the namespace; no name needed
  `ClassicalLean.Simplex.` in full (job 1's type comparison). Its two imports are the draft's. The
  module's `lake build`: 0 warning lines (`build-130`, `build-130-warn`). Its two witnesses are
  new (the item had no witness start): `ε = 1 / 4`, and for `mutualInfo_bsc_le` the input
  `(1 / 3, 2 / 3)`. Its review, `rv2-130`: CLEAN, so no confirming pass.
* **124** (`d124-r4-s2.lean`). Every `first` chain cut to the branch that fires (`assemble-124`, 26
  edits): lines 12 to 14 to line 13 (line 14 never ran); lines 144 to 148 to line 145; lines 162
  to 164 to line 163; lines 176 to 178 to line 177; lines 197 to 199 to line 198 (each later
  branch never ran); lines 224 to 226 to `field_simp` and `ring` on two lines (line 226 never
  ran); and lines 157 to 160, in `hSmeas`, to `fun_prop`, its third branch: its first branch names
  `Finset.measurable_sum'`, which does not exist at this Mathlib (`probes-orig`), and the review's
  fire test found the second a type mismatch. Line 131: `show` became `change`. Line 194: the
  deprecated `push_neg` became `push Not`. The draft had no docstring; the module has one for the
  main theorem and one for each of its five private lemmas (job 1). The module's `lake build`: 0
  warning lines (`build-124`, `build-124-warn`; after the fix, `build2-124`, `build2-124-warn`). Its
  witness is claude-ai's start with the theorem called by its full name (`wdiff-124`). Its
  review, `rv2-124`, had one MINOR finding: the module docstring named the start by its path in
  `incoming/`, which the merge removes; fixed in that docstring sentence only (`fixdiff-124`),
  re-elaborated (`m124-module2`) and rebuilt, and confirmed by a fresh reviewer (`rv2c-124`). The
  same sentence of item 126's module docstring was fixed the same way before its review
  (`mkstmt-126m`).
* **126** (`d126-r2-s2.lean`). Lines 43 and 49: the deprecated `push_neg` became `push Not`.
  Lines 59, 114, 121, 126 and 152: `if_pos` became `ite_eq_left`; lines 63, 116, 122, 127 and 154:
  `if_neg` became `ite_eq_right`. Lines 96 and 133: `Set.mem_setOf_eq` became `Set.mem_ofPred_eq`.
  Lines 98 and 158: `show` became `change` (each changed the goal) (`assemble2-126`, 16 edits).
  Its one import, `Mathlib.Probability.Distributions.Bernoulli`, is the witness's, and covers every
  module the proof uses (`imports-126`). The module's `lake build`: 0 warning lines (`build-126`,
  `build-126-warn`). Its witness is claude-ai's start with the theorem called by its full name
  (`wdiff-126`). Its review, `rv2-126`: CLEAN, so no confirming pass.

## Steps out of the order's sequence (rule 18)

* Job 2 began while job 1's confirming pass ran: `rv1c-confirm` ran from its brief,
  2026-10-21T01:09:44Z (`brief-rv1c`), to its report, hashed at 2026-10-21T01:14:17Z
  (`review-rv1c`); between them items 113 and 121 were assembled and elaborated in the evidence
  folder, not in the tree (`assemble-113` at 2026-10-21T01:11:54Z to `m121-a` at
  2026-10-21T01:14:12Z). The statement review's report was in at 2026-10-21T01:08:47Z
  (`review-rv1`), before any proof was assembled. `status-before-rv1c` and `status-after-rv1c`
  are equal (both empty).
* While item 113's review `rv2-113` ran (its brief 2026-10-21T01:16:02Z, its report hashed
  2026-10-21T01:23:08Z), items 130, 124 and 126 were assembled and their witnesses elaborated in
  the evidence folder, not in the tree (`w130-start` at 2026-10-21T01:17:33Z to `w126-end` at
  2026-10-21T01:18:45Z). `status-before-rv2-113` and `status-after-rv2-113` are equal.
* While item 124's confirming pass `rv2c-124` ran (its brief 2026-10-21T02:01:34Z, its report
  hashed 2026-10-21T02:06:56Z), item 126's module docstring was fixed and the module reassembled
  and elaborated in the evidence folder, not in the tree (`mkstmt-126m` at 2026-10-21T02:02:54Z
  to `m126-b` at 2026-10-21T02:03:02Z). `status-before-rv2c-124` and `status-after-rv2c-124`
  are equal.

## Completed after the work
