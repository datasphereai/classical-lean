# Round 20 — statistics: the Gauss–Markov theorem

Session: Claude Code `session_01BJXvpG7w5sbVN7yDWgdFwE` on helios, executing order `G-5`
(`records/orders/20260923T172503Z__claude-ai__order-g5-licence-gauss-markov.md`), job J3.
Lean and Mathlib v4.34.0. The library's first statistics module and its second area with no
number theory in it (`ROADMAP.md` §2.9, §3 item 3).

Commit: **`4eecf40`** (added in a follow-up edit, records/README.md Rule 1). The module, its
import line, this fragment, `ROADMAP.md` §2.9 and `HANDOFF.md` §3 land in one commit, so that
gate 6 passes at every commit; gate 6 was shown red on the new file first (below).

Evidence, outside the repository: `~/work/_bump-evidence/g5/j3/` (statement drafts, proof
workspace, junk-cell script and output, build logs, dumps) and `~/work/_bump-evidence/g5/
evidence.log` (every line a command and its rc).

## Modules

Added:

* `ClassicalLean/Statistics/GaussMarkov.lean` — 296 lines, the licence header, one module
  docstring, one definition, 18 theorems and 3 private theorems, one `example`.

Changed: `ClassicalLean.lean` gained `import ClassicalLean.Statistics.GaussMarkov`, its only
change. Every other module is untouched. Top-level directories under `ClassicalLean/`: 9 → 10.

## The search, before anything was written

Recorded in `ROADMAP.md` §2.9 with its commands. At Mathlib v4.34.0: the order's first search
(`gauss.?markov|best linear unbiased|unbiased|least.?squares|leastSquares|regression`) gives 26
lines in 5 files, every one the word "regression" — tactic-analysis options and definitions, and
two comments about performance regressions (the order said "every one … in a tactic-analysis
option or comment"; two are ordinary comments, and some hits are definitions, so "nothing named
regression" is literally false and right about statistics); `pseudo.?inverse|moore.?penrose`
3 lines in 2 files, no Moore–Penrose inverse; `PosSemidef.*⁻¹` 3 lines in 1 file, `PosSemidef.inv`
and the two Schur-complement lemmas, whose full names are `Matrix.PosDef.fromBlocks₁₁` and
`Matrix.PosDef.fromBlocks₂₂`; a shape search for `(Xᵀ * X)⁻¹`, 0. Each of the four over this
library: 0. `docs/1000.yaml` Q428134: title only, no formalisation. Predicted from the order and
measured: 26/5, 3/2, 3/1 all held.

Rule 2 (`HANDOFF.md` §6), definitions read before stating: `Matrix.PosSemidef`
(`LinearAlgebra/Matrix/PosDef.lean:60`) quantifies over `n →₀ R`, with the vector form
`posSemidef_iff_dotProduct_mulVec` (:298); the Loewner order is `Matrix.instPreOrder`,
`le A B := (B - A).PosSemidef`, scoped to `MatrixOrder` and stated for `RCLike 𝕜` under
`open scoped ComplexOrder` (`Analysis/Matrix/Order.lean:48-58`). At `𝕜 = ℝ` the order on `ℝ`
inside it is `RCLike.toPartialOrder`, a class field that `Real.instRCLike`
(`Analysis/RCLike/Basic.lean:786`) leaves to instance search, so it is `ℝ`'s usual order and the
Loewner form means what it says; `Matrix.le_iff.mpr` then proves it from the positive
semidefinite form with no conversion, which is the check in Lean.

## Junk cells, enumerated first (rule 3)

Constructed exact-zero cases and random trials, in exact rational arithmetic with Mathlib's
inverse modelled as `0` on a singular matrix: `~/work/_bump-evidence/g5/j3/junk_cells_gm.py`,
seed 20260923, output `junk_cells_gm.out`.

* Constructed: the singular design `!![1, 1; 1, 1]` (`det (Xᵀ X) = 0`, the inverse and
  `leastSquares` are `0`; the normal equations at `y = ![1, 0]` give `![1, 1]`; the residual sum
  of squares is `1` against `1/2` at `β = ![1/2, 0]`); `X = !![1; 1]` with the biased `C = 0`
  (`1/2 ≤ 0` fails); the worked example; `C` equal to least squares exactly (`D = 0`); `n < k`
  and `n = 0` (the hypothesis is empty); `k = 0` (everything trivially true).
* Random: 4000 designs, of five kinds (full rank, rank-deficient with a copied column, `n < k`,
  `n = 0`, `k = 0`); 1555 with an unbiased `C`, 2445 without. Every statement held in 1555 of
  1555 under its hypothesis; without it, each one-sided statement failed in some trials (S2 and
  S3 1717, the normal equations 784, the decomposition 728, the minimality 88, positive
  semidefiniteness 64, the variance reading 20, the equality case 4) — except
  `leastSquares * leastSquaresᵀ = (Xᵀ X)⁻¹`, which failed in 0 of 2445: on the junk value both
  sides are `0`. That finding, and the first cold review, dropped its hypothesis.
* The first run exited 1 with 20 "failures" of the variance reading under the hypothesis. It was
  the harness, not the statement: the test for the hypothesis-free `iff` used
  `name.startswith("S1")`, which also matched "S10". Fixed to `"S1 "`; the first output is kept
  as `junk_cells_gm.run1-harness-bug.out`, and the run quoted above is the second.

The reading in the order — `C * X = 1` forces `Xᵀ X` invertible, so no junk inverse can make the
main theorem hold emptily — is a theorem here, not an assumption:
`isUnit_det_transpose_mul_self_of_mul_eq_one`, through injectivity of `X.mulVec` and
`Matrix.PosDef.conjTranspose_mul_self`.

## Statements, and the reviews before proving

Every statement was drafted with `sorry` outside the repository and type-checked with
`lake env lean` before review. **That check did not apply the lakefile's linters** — the second
reviewer found it: `lake env` passes no `[leanOptions]`. The linters ran for the first time at the
module's `lake build` (below), where they found two long lines.

**First cold review**, two fresh reviewers, over revision 1 (18 statements). The meaning lens:
"All 18 statements are true as typed, and none is vacuous. None needs rejecting. … OVERALL:
APPROVE-WITH-FIXES." The Lean/Mathlib lens: "OVERALL: APPROVE-WITH-FIXES". Fixes adopted: the
`leastSquares`-only statements take `IsUnit (Xᵀ * X).det` instead of a phantom `C`; the variance
factor drops its hypothesis; a general junk-value lemma replaces a literal one; the strict worked
example becomes an `∃` statement (a `let` in the statement hid its conclusion from VacuityGate);
general index types `ι κ`; `self_…` names after Mathlib's `self_mul_conjTranspose`; docstrings
that say exactly what the statements say; a new equivalence, an unbiased linear estimator exists
iff `Xᵀ X` is invertible.

**Second cold review**, one fresh reviewer, over revision 2: "All 18 theorems and the `example`
are true as typed and none is rejected. Two changes are required: a docstring on the `def`, and
one rename (#5). … OVERALL: APPROVE-WITH-FIXES." Adopted verbatim: the definition's docstring,
the rename to `exists_mul_eq_one_iff_isUnit_det_transpose_mul_self`, and its optional
strengthening of `not_forall_dotProduct_inv_mulVec_le` with `IsUnit (Xᵀ * X).det →`, which makes
"the failure is bias, not the junk inverse" machine-checked.

**Not reviewed before proving:** three private helper theorems written while proving —
`transpose_inv_transpose_mul_self` (`(Xᵀ X)⁻¹` is symmetric), `leastSquares_ones_two_two` (the
junk value at `!![1, 1; 1, 1]`) and `inv_transpose_mul_self_ones_two` (`(Xᵀ X)⁻¹ = !![1 / 2]` at
`!![1; 1]`). They are reviewed with every other shipped statement after proving, below.

Two reviewers broke their read-only instruction, and said so: the first round's Lean reviewer
wrote a scratch file into this session's scratchpad, outside the repository; the second round's
reviewer, loading the scanner with `importlib`, created `tools/__pycache__/`, which `.gitignore`
covers — parked outside the repository at `~/work/_parked/g5-reviewer-tools-pycache`, not deleted.

## What the module states

`namespace ClassicalLean.Statistics`, over `ℝ`, `X : Matrix ι κ ℝ`, `[Fintype ι] [Fintype κ]
[DecidableEq κ]`. Definition `leastSquares X := (Xᵀ * X)⁻¹ * Xᵀ`. Theorems:
`unbiased_iff_mul_eq_one`, `isUnit_det_transpose_mul_self_of_mul_eq_one`,
`leastSquares_eq_zero_of_not_isUnit_det`, `leastSquares_mul_self`,
`exists_mul_eq_one_iff_isUnit_det_transpose_mul_self`, `leastSquares_mul_transpose`,
`transpose_mulVec_sub_mulVec_leastSquares` (the normal equations), `residual_dotProduct_le`
(least squares), `self_mul_transpose_sub_inv_eq`, **`posSemidef_self_mul_transpose_sub_inv` (the
Gauss–Markov theorem)**, `self_mul_transpose_eq_inv_iff`, `dotProduct_inv_mulVec_le`,
`inv_le_self_mul_transpose` (Loewner form; `posSemidef_self_mul_transpose_sub_inv` read through
`Matrix.le_iff`, which is `Iff.rfl` — the ordering form, not new content), the three
counterexamples `not_forall_transpose_mulVec_sub_mulVec_leastSquares`,
`not_forall_residual_dotProduct_le`, `not_forall_dotProduct_inv_mulVec_le`, and the worked
example `leastSquares_ones_two` and `exists_mul_eq_one_dotProduct_inv_mulVec_lt` — the witness
`HANDOFF.md` §3 asks for, that the hypothesis `C * X = 1` is inhabited, and through the
equivalence above so is `IsUnit (Xᵀ X).det`.

## Building it

The proofs were written in `~/work/_bump-evidence/g5/j3/Proofs.lean` with `lake env lean`; the
module is that file's body, byte for byte, under a new head (header, imports, module docstring):
the body's sha256 was compared after each assembly. The module was never built before its root
import line existed (the header linter reads the root at compile time). Builds, from the
repository root:

1. `lake build`: rc 0, **2 warnings**, the long-line linter at lines 241 (104 characters) and 255
   (111) — predicted from a length count before the build.
2. After wrapping both: rc 0, 1 warning — the second wrap left line 257 at 103 characters.
3. After a second wrap: **rc 0, 0 warnings, "Build completed successfully (3793 jobs)"** — 3719 +
   74, the 73 Mathlib modules the closure count predicted and the module.
4. After the post-proof review's docstring fixes (below): rc 0, 0 warnings, 3793 jobs. The first
   reassembly after those fixes left two lines at 145 and 103 characters (an edit had ended
   mid-line); a length count caught it before the build, and the paragraph was rewrapped.

Header fire test on the new module (the second reviewer of order G-5's plan asked for it): its
Authors line deleted, `lake build` gave exactly one warning,
``GaussMarkov.lean:4:0: * `-/`:`` / `Copyright too short!`; restored (`cmp` rc 0), 0 warnings.

## Gates

* Gate 6 red first: with the module and its import line in place and this fragment not yet
  written, `check_records.py` rc 1, "45 module(s) under ClassicalLean, 1 with no records entry …
  UNRECORDED ClassicalLean/Statistics/GaussMarkov.lean". The filed order names the module only as
  `ClassicalLean/Statistics/GaussMarkov` and `GaussMarkov`, which the gate does not count, so the
  file kept its name.
* AxiomGate rc 0: 1098 theorem constants, every new one within `propext`, `Classical.choice`,
  `Quot.sound`; the same two scoped exceptions, no new one. VacuityGate rc 0. check_sorry and
  banned_vocab_scan PASS over 45 files, 0 hits.
* `import_closure.py`: closure 3895 → 3969 (Mathlib 3401 → 3474);
  `Mathlib.Probability.Kernel.Invariance` False before and after; controls
  `Mathlib.Analysis.Matrix.Order` and `Mathlib.Algebra.Order.Star.Real` False before, True after,
  the first through `ClassicalLean.Statistics.GaussMarkov`.
* Type dump against J2's Done-means dump: `removed=0 added=29 changed=0` — 27 theorems and 2
  definitions (`leastSquares`, and `…exists_mul_eq_one_iff_isUnit_det_transpose_mul_self.match_1_1`
  from the anonymous-constructor pattern), all under `ClassicalLean.Statistics`. No existing
  theorem type or definition changed.

## Per-module theorem-constant count

`~/work/_bump-evidence/ModuleThmCount.lean`: total 1098, equal to AxiomGate's; private 138; 45
modules. `ClassicalLean/Statistics/GaussMarkov.lean`: **27** — 18 public theorems, 3 private, and
6 generated: `leastSquares.eq_1`, `leastSquares.congr_simp`, two `_simp_` and two `_abel_`
auxiliaries. Filtered list (`ListTheorems.lean`) 724 → 746: the 21 named theorems and
`leastSquares.congr_simp`; raw 1071 → 1098. Predicted: filtered 745 or 746.

## Consumers (round 16's sense)

`leastSquares` has **no consumer outside its own file**, and this is why: the module is new and
nothing but the root imports `ClassicalLean.Statistics` (`grep` over `ClassicalLean/`). Inside the
file it is what the normal equations, the least-squares theorem, the decomposition and the
equality case are about, and `posSemidef_self_mul_transpose_sub_inv` and the variance reading are
proved through it without naming it. Its first outside consumer would be generalised least
squares or Cochran's theorem (`HANDOFF.md` §3, `ROADMAP.md` §2.9).

## Not done

The order's optional second module, the variance reading through
`ProbabilityTheory.covarianceBilin`, was not started; `HANDOFF.md` §3 lists it. Nothing was left
unproved.

## The review after proving

A fresh reviewer, read-only, over every shipped declaration of the module as first built
(sha256 `d67dddd6…`): "None of the flags touches a theorem statement. All 23 declarations (20
theorems, the def and the example) are true as typed. … OVERALL: SOUND-WITH-FLAGS." It diffed
every statement against revision 2 and found only the requested fixes, plus the three private
helpers, which it reviewed and passed ("`transpose_inv_transpose_mul_self` is SOUND …
`leastSquares_ones_two_two` is SOUND … `inv_transpose_mul_self_ones_two` is SOUND"; it confirmed
the `1 / 2` is division in `ℝ` from the type dump). It read the proofs: no `sorry`, `admit`,
`native_decide`, `axiom` or `set_option`; the junk value is used only in
`leastSquares_mul_transpose`'s singular branch, as its docstring says; each `not_forall_` proof
specialises at the named witness and closes on the intended arithmetic contradiction.

Its flags, all in prose, and what was done:

* **F1** — the module docstring said the junk value "satisfies neither the normal equations nor
  the least-squares property"; false at `X = 0`. Now "does not in general satisfy".
* **F2** — "Each hypothesis is shown necessary" overclaimed: `leastSquares_mul_self`, the
  decomposition and the equality case have no counterexample. Narrowed, in the module docstring
  and in `ROADMAP.md` §2.9, to the three statements that have one; the reviewer's hand-computed
  witnesses for the other three are recorded in §2.9, not stated in Lean.
* **F3** — "the one statement that holds on the junk value too" is now "the one public
  statement"; the private symmetry lemma holds there too.
* **F4** — the breakdown of the 26 "regression" hits, corrected in the module docstring and in
  §2.9: 16 lines of `linter.tacticAnalysis.regressions.*` options, 4 of
  `linter.nightlyRegressionSet`, four `*Regressions` definitions, two comments.
* **F5** — `ROADMAP.md` §2.9, which the module docstring cites, is committed with the module.

The fixes touch the module's docstring only: the body, from `namespace ClassicalLean.Statistics`
to the end, has the same sha256 (`6de75634…`) in the proof workspace, in the module the reviewer
read and in the module as committed. The reviewer also reported "another session was editing
`ROADMAP.md` and `HANDOFF.md`" during its review; that was this session writing these records.

## Addendum — the Close's check of every Done-means (2026-09-23)

Order G-5's Close, step 3: a fresh subagent, read-only, checked every Done-means of J1, J2 and
J3 and the Close's first step against `git diff d9ed3b6^..master` at `3c2fdb0` (11 commits, 57
files). It ran the three text gates itself (each rc 0), recomputed the `LICENSE` hash and the 45
headers (46 with the new module), re-diffed the before and after name lists and type dumps, and
cited this session's logged runs for the Lean gates, which it may not run. Its verdict:
"**VERDICT: CLOSE**" — every checkable Done-means met.

What it found that no Done-means covers, and what was done:

* The landed vocabulary exception is stricter than the order's literal regex — this session's
  ruling, recorded in round 19 and `HANDOFF.md` §6; it asked that the final report list it with
  the three decisions made on Dustin's delegation. Listed there.
* **An error of this session's, logged here (R8):** four lines of
  `~/work/_bump-evidence/g5/evidence.log` carry placeholder values in the rc position —
  "TypeDump rc=9; typediff rc=9" and "rc=na", written by the step-3 helper when a build failed
  and the dump therefore did not run, and "rc ok" for a run whose rc was seen but not logged.
  `g5_typediff.py` can only exit 0, 1 or 125, so none of those is a measured code; a run that did
  not happen shared the channel of runs that did. Each is on an intermediate state later
  superseded by a logged run, and nothing depends on it. The log was not rewritten; a dated
  correction line is appended to it. Four further lines log a command without an rc.
* Two passages still say `Helix` "already sets" the option (`LucasSequenceGeneratingFunction`'s
  docstring, `HANDOFF.md` §1); both sit above the dated lines that supersede them.
* `RETIRED.md` got a six-line dated paragraph where the order said "one dated line"; cosmetic.
* The three private helpers were not cold-reviewed before proving (disclosed above; passed after).
* "Staged by path" is inferred from each commit's file list, which carries no stray path; git
  does not record how a file was staged.
