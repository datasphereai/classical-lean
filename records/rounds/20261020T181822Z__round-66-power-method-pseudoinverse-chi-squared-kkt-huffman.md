# Round 66 — the power method, the Moore–Penrose pseudoinverse, the chi-squared law, KKT under Slater's condition, Huffman's code (order CLOUD-MATH-2)

Session: Claude Code cloud session `session_019tga5LT3iStpcstjGMLwLU`
(https://claude.ai/code/session_019tga5LT3iStpcstjGMLwLU), executing order `CLOUD-MATH-2`
(`records/orders/20261020T181822Z__claude-ai__order-cloudmath2-power-method-pseudoinverse-chi-squared-kkt-huffman.md`),
items 147, 150, 151, 152 and 153 of MATH-PLAN-library-2 (rows below its cut), in a cloud container's
clone of GitHub `datasphereai/classical-lean` on branch `cloud-math-2`, from
`4d99afd873730fa5f1231c6d6c68f57f2601c4a0` (checked equal to `origin/cloud-math-2` before any
change). `git ls-remote origin master` at the start: `9c0639c5878d09db83b1334ec35b705add9a8cb7`.
Lean and Mathlib v4.34.0 (`lake exe cache get`, 8908 files). The proofs come from the five drafts in
`incoming/` (the seven `.lean` files' sha256s checked equal to `incoming/README.md`, and
`sha256sum -c SHA256SUMS` in `incoming/tools` passed, before any change); this round lands them, it
does not re-prove them. Evidence: `~/cm2-evidence/` (outside the repository), `evidence.log` (UTC
time, label, rc, prediction, command, output sha256 per run; `COMMIT <hash>` marker lines), copied to
`incoming/evidence/` at the end. The cloud toolkit's 41 planted-fault tests passed before first use
(41 OK, `BAD=0`; label `tools-test`, output sha256
`3fc1b6ebabad26085aca2e48e5d356e703eba48cfcc011dc7671f973b47cc700`, the value `incoming/README.md`
gives for DSMain's run).

**Order RULES-1's push.** RULES-1's INDEX State cell and CLAIMS row gain the clause the order gives,
"; pushed by Dustin: DSMain's master ref written 2026-10-19 20:07:42 EDT, GitHub master equal
(`9c0639c`)", measured by claude-ai on DSMain, not by this session (which cannot reach DSMain); what
this session measured is `git ls-remote origin master` above, GitHub's master at `9c0639c…`.
Nothing else in those rows changes.

First part written before any Lean file changed; completed after the work, below.

## Modules this round adds (five new modules)

* item 147: `ClassicalLean/Analysis/PowerMethod.lean` (`ClassicalLean.Analysis.PowerMethod`), from
  `incoming/d147-r1-s2.lean`, its witness from `incoming/d147-r1-s2-witness.lean`;
* item 150: `ClassicalLean/Algebra/Pseudoinverse.lean` (`ClassicalLean.Algebra.Pseudoinverse`), from
  `incoming/d150-r1-s2.lean`;
* item 151: `ClassicalLean/Probability/ChiSquared.lean` (`ClassicalLean.Probability.ChiSquared`),
  from `incoming/d151-r9-s1.lean`, its witness from `incoming/d151-r9-s1-sat.lean`;
* item 152: `ClassicalLean/Analysis/KKT.lean` (`ClassicalLean.Analysis.KKT`), from
  `incoming/d152-r2-s1.lean`;
* item 153: `ClassicalLean/InformationTheory/Huffman.lean` (`ClassicalLean.InformationTheory.Huffman`),
  from `incoming/d153-r1-s2.lean`;
* `ClassicalLean.lean`: five import lines, at the end of its import block, in landing order.

No existing module changes. `tools/vacuity_reviewed.txt` changes only if a helper is listed (the
order's rule 3). Nothing else under `tools/` changes.

## Starting counts (measured in this session, before any new module, clean tree at `4d99afd`)

* `lake build`: rc 0, `Build completed successfully (4178 jobs).`, 0 lines with `warning:` (labels
  `start-build`, `start-build-warn`).
* `lake env lean tools/AxiomGate.lean`: rc 0, `axiom gate PASS — 3379 theorem constant(s) under
  [ClassicalLean], every one depending only on a subset of [propext, Classical.choice, Quot.sound];
  0 scoped exceptions` (label `start-axiom`).
* The base closure (rule 38's first use, `rootrun.sh`, label `closure-base`): the root build at
  `4d99afd` rc 0, 4178 jobs, 0 warnings, then `$EVD/closure-base.lean` (the order's four lines)
  rc 0, 5714 `MOD` lines (the whole import closure of `ClassicalLean`, Lean's own modules
  included). In `evidence.log` the `closure-base-build` line (line 11) comes before the
  `closure-base` line (line 12) and both name head `4d99afd873730fa5f1231c6d6c68f57f2601c4a0`
  (label `rule38-order`): rule 38's test with the real build.

## Proof changes and warning fixes, by item (written as each item lands)

The Goal list asks that every warning fix be listed here. Each module is assembled by
`~/cm2-evidence/scripts/assemble.py` from its reviewed statement file (job 1) and its draft's proof
lines; the spec `~/cm2-evidence/spec/s<item>.json` names every edit to a draft line, and the
assembler printed each one. Line numbers below are the draft's. Statements are untouched: job 1's
type comparison found every main theorem and definition the same as the draft's.

* **147** (`d147-r1-s2.lean`). Lines 12 and 22: `show` became `change` (the `show` changed the
  goal). Line 98: `try ring` deleted; `field_simp` closes that goal, and without the line the
  module elaborates with no message (label `m147-a`). Lines 127 to 129: the `first` chain cut to
  `simp`; its first branch was `simpa using hT.apply_eigenvectorBasis hn i`, which the linter asked
  to be `simp`, and plain `simp` closes the goal; its second branch never ran. The module's
  `lake build`: 0 warning lines (`build-147-4`). Its review, `rv2-147`, had two MINOR docstring
  findings, fixed in docstrings only and confirmed by a fresh reviewer (`rv2c-147`).
* **150** (`d150-r1-s2.lean`). The linter's warning that `exists_symm_ginv`, `exists_penrose` and
  `penrose_unique` do not use the section's `[DecidableEq n]` in their types: the section's
  `variable` line no longer carries it before `pinv` (a second `variable [DecidableEq n]` comes
  after `pinv`); `classical` is the new first line of the proofs of `exists_symm_ginv` (before
  line 23) and `exists_penrose` (before line 89); and `pinv` binds `[DecidableEq n]` itself, which
  keeps its type, and every main theorem's, equal to the draft's (job 1's type comparison, and
  review `rv1-statements`'s fire test `rv1-fire-instdrop`). First tried in the statement file and
  dropped: `omit [DecidableEq n] in` on the three helpers took the instance off `pinv`'s type and
  left the main theorems with an unused instance (`stmt-Pseudoinverse`, 2026-10-20T18:38Z), and a
  binder on `pinv` beside the section's instance overlapped it (`stmt2-Pseudoinverse`,
  2026-10-20T18:40Z). `pinv_spec`'s proof stays the draft's term (line 142). The module's
  `lake build`: 0 warning lines (`build-150-2`). Its review, `rv2-150`, had one MINOR docstring
  finding, fixed in the docstring only and confirmed by a fresh reviewer (`rv2c-150`). Its two
  witnesses (`pinv_unique` on `!![1, 2; 0, 0]`, rank one; `pinv_eq_leastSquares` on a three-by-two
  matrix of full column rank) are new: the item had no witness start.
* **151** (`d151-r9-s1.lean`). No warning to fix, at 9c0639c (the Goal list) or here. The private
  `isProb_gamma_aux` (lines 54 to 58, its docstring included) is gone, and its one use (line 245)
  now calls Mathlib's `ProbabilityTheory.isProbabilityMeasure_gammaMeasure`; a comment at
  `complexMGF_gammaMeasure_aux` says that its route is the one of Mathlib's
  `ProbabilityTheory.eqOn_complexMGF_of_mgf'`, and why that lemma does not apply as stated.
  `import Mathlib` is replaced by thirteen Mathlib modules, each declaring a name the file uses.
  The module's `lake build`: 0 warning lines (`build-151`). Its witness takes `k = 3`, from
  claude-ai's satisfiability check `d151-r9-s1-sat.lean`. Its review, `rv2-151`: CLEAN, so no
  confirming pass.
* **152** (`d152-r2-s1.lean`). Lines 72, 73, 131, 132 and 202: `show` became `change` (each changed
  the goal). Lines 78, 121 and 175: the deprecated `push_neg` became `push Not`. Lines 208 to 210:
  the deprecated `ContinuousLinearMap.add_apply`, `sum_apply`, `smul_apply` and `zero_apply` became
  the names the warnings give, `add_apply`, `_root_.sum_apply` (the module opens `Finset`),
  `smul_apply` and `zero_apply`. Imports: the draft's import of the library's
  `ClassicalLean.Analysis.GradientDescent`, none of whose declarations the proof uses, became
  `Mathlib.Analysis.Calculus.FDeriv.Mul`, the file of `HasFDerivAt.const_mul`, which the proof had
  taken through it (without it `imports-152` rc 1; with it `imports-152b` rc 0). The module's
  `lake build`: 0 warning lines (`build-152-2`). Its witness is new (the item had no witness
  start): minimise `x * x` on the real line subject to `1 - x ≤ 0` and `x - 2 ≤ 0`. Its review,
  `rv2-152`, had one MINOR finding in the module docstring's proof sketch, fixed in the docstring
  only and confirmed by a fresh reviewer (`rv2c-152`).
* **153** (`d153-r1-s2.lean`). Every declaration is now in `ClassicalLean.InformationTheory.Huffman`
  (the draft had the helpers in `ClassicalLean.Huffman` and `huffman_optimal` outside any
  namespace), and the helpers' `variable {ι : Type*} [DecidableEq ι]` line is in a section closed
  before `huffman_optimal`, whose binders stay the draft's. In `huffman_optimal`'s proof (lines 398,
  400, 409, 412, 413 and 415) the full names `ClassicalLean.Huffman.huffAux_kraft`,
  `…huffmanLength`, `…huffAux_opt` and `…huffAux` became their names in the new namespace (its
  statement's, job 1). The warning that `exists_pair` does not use `[DecidableEq ι]` in its type:
  `omit [DecidableEq ι] in` before `exists_pair`, with `classical` as the new first line of its
  proof (before line 22), and before `pick_spec`, whose type then has no use for it either; so the
  private `pick` no longer takes the instance, which the Goal list allows for a private helper
  (job 1's type comparison: `pick` alone differs; review `rv1-statements`'s fire test: the draft's
  `pick` and this one are equal by `rfl`). Lines 68 and 72: the deprecated `dif_pos` and `dif_neg`
  became `dite_eq_left` and `dite_eq_right`. Line 240: the deprecated `push_neg` became
  `push Not`. `pick_spec` and `sum_erase_split` keep the draft's term proofs (lines 38 and 110).
  The module's `lake build`: 0 warning lines (`build-153-2`). Its witness is new (the item had no
  witness start): three symbols with the weights `(1/2, 1/4, 1/4)` and the alphabet `Bool`. Its
  review, `rv2-153`, had two MINOR docstring findings, fixed in docstrings only and confirmed by a
  fresh reviewer (`rv2c-153`).

## Steps out of the order's sequence (rule 18)

* Job 2 began while job 1's confirming pass ran: review `rv1c-confirm`, on the fix of a Huffman
  docstring line, ran from its brief, 2026-10-20T19:06:55Z (`brief-rv1c`), to its report,
  2026-10-20T19:13:33Z (`review-rv1c`), and item 147's module was assembled and placed in the tree
  between 2026-10-20T19:08:38Z (`mod147-a`) and 2026-10-20T19:09:15Z (`m147-module`). The
  statement review's report (`rv1-statements`) was in at 2026-10-20T19:06:09Z (`review-rv1`),
  before any proof entered a module. The tree
  change was this session's, during a running review: `status-before-rv1c` and
  `status-after-rv1c` differ by item 147's two files, which the reviewer did not write.
* Items 150 to 153 were assembled and elaborated in the evidence folder, not in the tree, while
  item 147's review `rv2-147` ran (its brief 2026-10-20T19:09:55Z, its report
  2026-10-20T19:22:26Z; `mod150-a` at 2026-10-20T19:10:41Z to `m153-a` at 2026-10-20T19:16:01Z).
  Each entered the tree only after the item before it was committed, and never while a reviewer
  ran (every later review's `status-before-*` and `status-after-*` are equal).

## Completed after the work

All five items are closed; no narrowing; no item undone; no entry added to
`tools/vacuity_reviewed.txt`. Report: `incoming/REPORT.md`; reviews: `incoming/reviews/`;
evidence: `incoming/evidence/` (one file over 1 MB left out, named in the report).

**Commits** (branch `cloud-math-2`, each pushed with `git push origin cloud-math-2`):

* `1663442` — records first (the order's copy, its INDEX row, the CLAIMS row, this fragment's first
  part, RULES-1's push in its two rows);
* `f58d3ba` — item 147, `ClassicalLean/Analysis/PowerMethod.lean` (with job 1);
* `f2c4785` — item 150, `ClassicalLean/Algebra/Pseudoinverse.lean`;
* `bcc7619` — item 151, `ClassicalLean/Probability/ChiSquared.lean`;
* `7b7a471` — item 152, `ClassicalLean/Analysis/KKT.lean`;
* `f224ec9` — item 153, `ClassicalLean/InformationTheory/Huffman.lean`;
* `2f21991` — `incoming/PREDICTIONS.md`;
* the commit that carries this section — the report, the reviews, the evidence, the CLAIMS row
  closed and the INDEX row's state (its own hash cannot be written in it).

Each landing commit added its module's import line at the end of `ClassicalLean.lean`'s import
block (landing order: PowerMethod, Pseudoinverse, ChiSquared, KKT, Huffman) and removed its draft,
and its witness start where it had one, from `incoming/`.

**The modules and their theorem-constant counts**, from `census.sh` on each final module file
(rule 27: the axiom gate's predicate, user names under `ClassicalLean`, private ones and
auxiliaries included); their total, 79, plus the base's 3379 is the axiom gate's 3458 below:

| module | item | theorem constants |
|---|---|---|
| `ClassicalLean/Analysis/PowerMethod.lean` | 147 | 14 (5 written, 7 `_simp` and 2 `_abel` auxiliaries) |
| `ClassicalLean/Algebra/Pseudoinverse.lean` | 150 | 10 (8 written, `pinv.congr_simp`, 1 `_abel`) |
| `ClassicalLean/Probability/ChiSquared.lean` | 151 | 12 (12 written) |
| `ClassicalLean/Analysis/KKT.lean` | 152 | 2 (2 written) |
| `ClassicalLean/InformationTheory/Huffman.lean` | 153 | 41 (23 written, 8 `_proof_`, 4 `congr_simp`, 6 equation lemmas) |
| **five modules** | | **79** |

**Main theorems and their verdicts** (each docstring names its item of MATH-PLAN-library-2):
147 `tendsto_powerIterate` GENERALIZED; 150 `pinv` (definition), `pinv_spec`, `pinv_unique`,
`pinv_residual_dotProduct_le`, `pinv_eq_leastSquares` FAITHFUL; 151 `hasLaw_sum_sq_gaussian`
FAITHFUL; 152 `exists_kkt_of_slater` FAITHFUL; 153 `huffmanLength` (definition) FAITHFUL,
`huffman_optimal` GENERALIZED. Each under its module's namespace.

**Witnesses** (rule 4; six, after each module's last line; epoch seconds from `date +%s` through
`ev.sh`): 147 from 1792523234 to 1792523335; 150 (two) from 1792523425 to 1792523459; 151 from
1792523478 to 1792523502; 152 from 1792523608 to 1792523729; 153 from 1792523743 to 1792523766.
All within 1800 seconds.

**Reviews** (`incoming/reviews/`, each by a fresh subagent; each report returned only its sha256,
checked equal by `hl.sh` before it was opened; each brief built by script from `HANDOFF.md`,
`briefcheck.py` PASS, hashed before it was sent): job 1's statement review `rv1-statements`,
FINDINGS 1 (MINOR), confirmed `rv1c-confirm`; `rv2-147` FINDINGS 2 (MINOR), confirmed `rv2c-147`;
`rv2-150` FINDINGS 1 (MINOR), confirmed `rv2c-150`; `rv2-151` CLEAN; `rv2-152` FINDINGS 1
(MINOR), confirmed `rv2c-152`; `rv2-153` FINDINGS 2 (MINOR), confirmed `rv2c-153`. Every finding
was a docstring; one fix-and-confirm round each. Every reviewer checked that no main theorem's
conclusion is a recursive predicate that is `True` everywhere: none is.

**End check 1** (the clean tree at `2f21991`, the predictions committed first; no fix or undo
followed, so it ran once):

| command | predicted | measured |
|---|---|---|
| `lake build` | rc 0, 4188 jobs, 0 warnings | rc 0, `Build completed successfully (4188 jobs).`, 0 `warning:` lines (`ec1-build`, `ec1-build-warn`) |
| `lake env lean tools/AxiomGate.lean` | PASS 3458 | PASS 3458, 0 scoped exceptions (`ec1-axiom`) |
| `python3 -I tools/check_sorry.py` | PASS 135 | PASS 135 (`ec1-sorry`) |
| `lake env lean tools/VacuityGate.lean` | PASS, 1 reviewed helper, 0 VACUOUS-PENDING, rule 5 out on 0 | the same (`ec1-vacuity`) |
| `python3 -I tools/check_records.py` | PASS 135, 1 exemption | the same (`ec1-records`) |
| `python3 tools/compile_rules.py drift records/rules.toml HANDOFF.md` | `PASS no drift` | `PASS no drift` (`ec1-drift`) |

**End check 2** (`citecheck.py` over every commit after `4d99afd`): `OK` for all seven,
`1663442`, `f58d3ba`, `f2c4785`, `bcc7619`, `7b7a471`, `f224ec9` and `2f21991` (`citecheck`).

`git ls-remote origin master` at the start and at the end (`lsremote-start`, `lsremote-end`):
`9c0639c5878d09db83b1334ec35b705add9a8cb7`. CI: success on `4d99afd`, `1663442`, `f58d3ba` and
`7b7a471`; the runs on `f2c4785`, `bcc7619` and `f224ec9` were cancelled by the next push, as the
workflow's `concurrency` setting does; the run on `2f21991` was in progress when this was written
(`ci-list-end`); the run on the last commit is read after its push, and its result is in the
session's final message.
