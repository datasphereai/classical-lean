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
  2026-10-20T19:22:26Z; `mod150-a` at 2026-10-20T19:10:41Z to `m153-a` at 2026-10-20T19:16:01Z). Each enters the tree only after the item before it is committed, and not while a
  reviewer runs.
