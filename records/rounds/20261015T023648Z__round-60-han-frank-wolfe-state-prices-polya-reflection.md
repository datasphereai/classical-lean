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

## Completed after the work

All five items are closed; no narrowing; no item undone. Every statement of the drafts is kept as
it was; the only new statement is the order's third theorem of item 137. Report:
`incoming/REPORT.md`.

**Commits** (branch `cloud-math-1`, each pushed with `git push origin cloud-math-1`):

* `1a56f31` — records first (the order, its INDEX row, the CLAIMS row, this fragment's first
  part);
* `3aa32f8` — item 139, `ClassicalLean/Probability/Reflection.lean`;
* `82b24d2` — item 136, `ClassicalLean/Analysis/StatePrices.lean`;
* `5da88e9` — item 131, `ClassicalLean/InformationTheory/HanInequality.lean`;
* `82ac344` — item 137, `ClassicalLean/Probability/PolyaUrn.lean`;
* `cc65251` — item 135, `ClassicalLean/Analysis/FrankWolfe.lean` (with its review's docstring fix);
* `6a007c6` — `incoming/PREDICTIONS.md`, and `incoming/README.md` removed (no draft left);
* the commit that carries this section — `incoming/REPORT.md`, the CLAIMS row closed, the INDEX
  row's state (its own hash cannot be written in it).

Each landing commit removed its draft from `incoming/`, added the module's import line at the end
of `ClassicalLean.lean`'s import block (landing order: Reflection, StatePrices, HanInequality,
PolyaUrn, FrankWolfe) and its review files under `incoming/reviews/`.

**The modules and their theorem-constant counts.** Measured as records/README.md rule 1 says
(`env.getModuleFor?` under the axiom gate's `.thmInfo` predicate, user names under
`ClassicalLean`, private ones included), on the clean tree at `6a007c6` (a census file importing
`ClassicalLean`, run after the predictions were committed and after End check 1; its total, 3317,
equals the axiom gate's):

| module | item | theorem constants |
|---|---|---|
| `ClassicalLean/Probability/Reflection.lean` | 139 | 40 (18 written, 14 `omega` and 5 `_simp_` auxiliaries, 3 `eq_1`) |
| `ClassicalLean/Analysis/StatePrices.lean` | 136 | 4 (2 written, `sysMap._proof_1`, `_proof_2`) |
| `ClassicalLean/InformationTheory/HanInequality.lean` | 131 | 18 (12 written, 3 `omega`, 2 `_simp_`, `marg.eq_1`) |
| `ClassicalLean/Probability/PolyaUrn.lean` | 137 | 14 (11 written, 2 `omega`, `urnShare.eq_1`) |
| `ClassicalLean/Analysis/FrankWolfe.lean` | 135 | 13 (4 written, 1 `omega`, 7 `_simp_` from `field_simp`, 1 `_abel_`) |
| **five modules** | | **89** |

**Main theorems** (each docstring names its item of MATH-PLAN-library-2):

* 131: `ClassicalLean.InformationTheory.HanInequality.mul_shannonEntropy_le_sum` — FAITHFUL;
* 135: `ClassicalLean.Analysis.FrankWolfe.sub_le_of_frankWolfe` — FAITHFUL;
  `ClassicalLean.Analysis.FrankWolfe.fw_general` (public now, as the order's table asks) —
  GENERALIZED (any convex set of squared diameter at most `D`);
* 136: `ClassicalLean.Analysis.StatePrices.exists_pos_statePrices_iff` — FAITHFUL (no hypothesis,
  so no witness);
* 137: `ClassicalLean.Probability.PolyaUrn.martingale_urnShare`, `…ae_tendsto_urnShare` —
  FAITHFUL; `…ae_mem_Icc_of_tendsto_urnShare` (new: any almost sure limit of the share lies in
  `[0, 1]` almost surely, assuming only that the draws are `0` or `1`) — GENERALIZED;
* 139: `ClassicalLean.Probability.Reflection.measureReal_max_ge_eq` — FAITHFUL; `import Mathlib`
  replaced by `import Mathlib.Probability.UniformOn`.

**Witnesses** (rule 4; `example`s after each module's last line; start and end times by `date`):
139 at 02:39:50Z, done 02:40:04Z (`n = 4`, `a = 2`); 131 at 02:42:10Z, done 02:43:02Z (two binary
coordinates, `3/8` where they agree, `1/8` where they differ); 135 at 02:44:25Z, done 02:47:40Z
(both theorems: `‖y‖²` on the two-coordinate simplex, the real Frank–Wolfe iterates, alternating
vertices); 137 at 02:49:14Z, done 03:01:29Z (all three theorems: a Pólya urn with `r = b = 1` on
`ℕ → Bool` built by `Kernel.traj`, Mathlib's Ionescu–Tulcea construction; the third takes its
limit from `ae_tendsto_urnShare` by `Classical.choose`). All within 30 minutes. PolyaUrn imports
`Mathlib.Probability.Kernel.IonescuTulcea.Traj` for its witnesses only.

**Reviews** (`incoming/reviews/`, each reviewer a fresh subagent, its hand-back saved verbatim by
script from its transcript): 139 PASS; 136 PASS; 131 PASS; 137 PASS; 135 PASS WITH FINDINGS
(0/0/1: two docstrings said the simplex's squared diameter is exactly `2`, false for fewer than two
coordinates), fixed in docstrings only with the reviewer's wording, confirmed by a fresh reviewer
(CONFIRMED, no new finding). One fix-and-confirm round in all. Each brief is saved beside its
review. Every reviewer checked that no main theorem's conclusion is a recursive predicate that is
`True` everywhere: none is.

**Vacuity list:** no entry added; `tools/vacuity_reviewed.txt` unchanged.

**End check 1** (clean tree at `6a007c6`, 03:22:06Z to 03:31:22Z, the predictions committed
first; no fix or undo followed, so it ran once):

| gate | predicted | measured |
|---|---|---|
| `lake build` | rc 0, 4175 jobs, 0 warnings | rc 0, `Build completed successfully (4175 jobs).`, 0 `warning:` lines |
| `lake env lean tools/AxiomGate.lean` | PASS 3302 (3228 + 74; range 74 to 82) | PASS 3317 (3228 + 89), 0 scoped exceptions — **miss, +15** |
| `python3 -I tools/check_sorry.py` | PASS 127 | PASS 127 |
| `lake env lean tools/VacuityGate.lean` | PASS, 1 reviewed helper, 0 VACUOUS-PENDING, rule 5 ran out on 0 | the same (534 s) |
| `python3 -I tools/check_records.py` | PASS 127, 82 files, 1 exemption | the same |

**The miss.** The blind count (by hand, model calibrated on toy files) had 74 new theorem
constants; there are 89. Per module: Reflection 35 against 40 (5 `_simp_1_k` auxiliaries in
`card_eq` from its `simp only`/`simp at` calls, not modelled), HanInequality 16 against 18 (2
`_simp_1_1`, not modelled), FrankWolfe 5 against 13 (7 `_simp_1_k` from the one `field_simp` call
in `fw_general`, which the model put at 0 from the toy calibration, and 1 `_abel_1_1` from `abel` in
`fw_step`, not modelled), StatePrices 4 and PolyaUrn 14 exact. The `omega` (20), `eq_1` (5) and
`_proof_` (2) parts of the model were right. Not corrected: the prediction stays as committed.

CI (`.github/workflows/ci.yml`: build, axiom gate, check_sorry, vacuity gate): success on
`1a56f31`, `5da88e9` and `6a007c6`; the runs on `82b24d2` (pushed together with `3aa32f8`),
`82ac344` and `cc65251` were cancelled by the next push, as the workflow's `concurrency` setting
does. The run on the last commit is read after its push; its result is in the session's final
message.

`git ls-remote origin master` at the start and at the end: `20303cd4eb902e15b2d4994ea6aa2263f5146264`.
