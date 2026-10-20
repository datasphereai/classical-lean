# Review rv1-statements: order CLOUD-MATH-2, job 1, statement review

Reviewer: a fresh subagent that had not seen the session's work. Brief `/root/cm2-evidence/briefs/rv1-statements.md`, sha256 `ae14621010ed4ab2d9df1278d348658ce8622fa34294a9641091428712fb7b0c`, checked before reading. Worked in `/root/cm2-review-1` on 2026-10-20 from 18:45 to 19:07 UTC. Nothing was written in the repository: `git status --porcelain` was empty at the start and at the end. In `/root/cm2-evidence` I wrote only this file and the `rv1-*.out` outputs that `el.sh` writes itself.

Files reviewed, with sha256s as read: `PowerMethod.lean` `bc713ac1…c1c0`, `Pseudoinverse.lean` `4e19dcb9…6ef8`, `ChiSquared.lean` `4e82f4a9…0f03`, `KKT.lean` `5165927c…6df5`, `Huffman.lean` `8671eee9…aae`. They match the `stmt-files` lines of `evidence.log`. Each draft's sha256 matches `incoming/README.md`.

## What I ran (redone, not taken on trust)

- `rv1-stmt-<Module>`, five runs: each statement file, copied into my folder and elaborated with `el.sh`. All five gave rc 0, and every warning was `declaration uses 'sorry'`.
- `hdrcmp.py` (my script). It compares the statement text of every declaration, draft against statement file, after stripping comments: theorems up to their top-level `:=`, and definitions with their whole body. Every text is identical except for three things, all expected:
  - `pinv` binds `[DecidableEq n]` itself;
  - `huffman_optimal` now reads `huffmanLength`, where the draft had `ClassicalLean.Huffman.huffmanLength`;
  - `isProb_gamma_aux` is in the draft only (the Goal list removes it).
- `rv1-types-d<item>` and `rv1-types-s<item>`, ten runs, compared with a copy of `typecmp.py`. Each ran `#check @` with `pp.fullNames` on every declaration the two files share, private helpers included, not only the main theorems. Results:
  - 147: 5/5 SAME.
  - 151: all 12 declarations SAME. The script reports 10/10 because the two helpers that have no implicit argument print without `@` and are compared inside the message before them.
  - 152: 2/2 SAME.
  - 150: 6/9 SAME. The only differences: `exists_symm_ginv`, `exists_penrose` and `penrose_unique` lost an unused `[DecidableEq n]`.
  - 153: 25/28 SAME. The only differences: `exists_pair`, `pick` and `pick_spec` lost an unused `[DecidableEq ι]`.
  - Every main theorem, `pinv`, `huffmanLength`, `huffAux`, `mergeLen` and `mergeW` is SAME.
- `rv1-fire-instdrop`, a fire test that dropping the instance changed no value. It sets the draft's text beside the statement file's text. Both `@draft.pick ι inst w s h = stmt.pick w s h` and `@draft.pinv … inst A = @stmt.pinv … inst A` close by `rfl` (rc 0). `rv1-fire-instdrop-control` is its negative control: one conjunct is removed from the statement side's `exists_pair`, and the `rfl` then fails (rc 1, a type mismatch at the `rfl`).
- `rv1-ns-<Module>`, five runs: each statement file plus a `run_cmd` that lists every constant the file adds (`env.constants.map₂`). Every constant lies under its module's namespace, auto-generated ones included (`huffAux.match_1`, `._sunfold`, `._f`), and private ones carry the namespace after `_private.…0.`. The counts are 5, 9, 12, 2 and 31.
- Imports:
  - `closure.py` (my script) computes each import's place in the import graph.
  - `rv1-imp-<file>-x<k>`, 28 runs, removes one import at a time from the full text. For 147, 151 and 152 the full text is the session's `imports/i147b.lean`, `i151.lean` and `i152b.lean` (draft proofs, plus the witness start for 147 and the satisfiability example for 151); for 150 it is the draft itself (`rv1-imp-150-base`, rc 0).
  - `rv1-imp-<file>-min`, three runs, checks the minimal import sets together.
- Drafts: `rv1-types-d*` (each draft's full text with `#check` lines appended) elaborated with rc 0, no `sorry`, no error. No draft contains `axiom`, `sorry`, `admit`, `native_decide` or `implemented_by`. So every helper statement the drafts prove is true (check 6). The statement files' helpers have the same types, apart from the unused instances dropped above, which only widens them.
- Docstring names were checked against the Mathlib and library sources at this checkout:
  - Mathlib: `eigenvalues_antitone` ("ordered largest first"), `isProbabilityMeasure_gammaMeasure` (`{a r : ℝ} (ha : 0 < a) (hr : 0 < r)`), the proof of `eqOn_complexMGF_of_mgf'` (`Mathlib/Probability/Moments/ComplexMGF.lean`, lines 270–295), `IsPrefixFree.finsetSum_one_div_card_pow_length_le_one` (in Mathlib's `InformationTheory/Coding/Kraft.lean`), `geometric_hahn_banach_point_open`, `IsLocalMin.hasFDerivAt_eq_zero` and `HasFDerivAt.const_mul` (in `FDeriv/Mul.lean`).
  - Deprecations: the four `ContinuousLinearMap` aliases point to `_root_.add_apply`, `_root_.sum_apply`, `_root_.smul_apply` and `_root_.zero_apply`; `dif_pos` and `dif_neg` warn "Use `dite_eq_left`" and "Use `dite_eq_right`".
  - Library: `ClassicalLean.Statistics.leastSquares X = (Xᵀ * X)⁻¹ * Xᵀ`, and `ClassicalLean.Simplex.exists_isPrefixFree_length_eq`.

## Each main theorem and definition against its plan row

**Item 147, `ClassicalLean.Analysis.PowerMethod`**
- `tendsto_powerIterate`: **GENERALIZED**. It is stated for a symmetric linear map of any finite-dimensional real inner product space; a symmetric matrix is the case `Matrix.toEuclideanLin A` on `EuclideanSpace ℝ (Fin n)`. The index `i₀` of the strictly dominant eigenvalue can be any index. The theorem gives the row's rate `(|λ₁|/|λ₀|)^k` as an explicit bound and also the convergence of the rescaled iterates to `u`. Its one hypothesis the row does not name, `⟪u, x⟫ ≠ 0`, is one without which the row's claim fails.

**Item 150, `ClassicalLean.Algebra.Pseudoinverse`**
- `pinv` (definition): **FAITHFUL**. It is a matrix chosen to satisfy the four Penrose equations, so by `pinv_unique` it is the Moore–Penrose pseudoinverse. Its explicit `[DecidableEq n]` gives the draft's type, and the fire test above shows the draft's value.
- `pinv_spec`: **FAITHFUL**. It gives the four equations.
- `pinv_unique`: **FAITHFUL**. Uniqueness: every solution of the four equations is `pinv A`.
- `pinv_residual_dotProduct_le`: **FAITHFUL**. Least squares for every design, a rank-deficient one included: no `β` has a smaller residual sum of squares than `pinv A *ᵥ y`.
- `pinv_eq_leastSquares`: **FAITHFUL**. It adds to the row: for full column rank, `pinv A` is the library's `(Aᵀ A)⁻¹ Aᵀ`.

**Item 151, `ClassicalLean.Probability.ChiSquared`**
- `hasLaw_sum_sq_gaussian`: **FAITHFUL**. `k ≥ 1` measurable, mutually independent (`iIndepFun`) variables with law `gaussianReal 0 1` have the sum of squares with law `gammaMeasure (k/2) (1/2)`. The only extra hypotheses are `k ≥ 1`, which the row's `k` degrees of freedom imply, and measurability, which is what a random variable is.

**Item 152, `ClassicalLean.Analysis.KKT`**
- `exists_kkt_of_slater`: **FAITHFUL**. The problem is convex: `f` and every `g i` are convex on the whole space and differentiable at `xbar`. There are finitely many inequality constraints and a Slater point, and `xbar` is a feasible minimiser. The conclusion gives multipliers `w i ≥ 0` with complementary slackness and stationarity. It is stated on a real Hilbert space.

**Item 153, `ClassicalLean.InformationTheory.Huffman`**
- `huffmanLength` (definition): **FAITHFUL**. It is binary Huffman: each step merges a lightest and a next-lightest symbol (`pick`) into one of the summed weight (`mergeW`), and both merged symbols get the merged symbol's length plus one (`mergeLen`). `Fintype.card ι` steps of the recursion are enough.
- `huffman_optimal`: **GENERALIZED**. Optimality over every injective prefix-free code over a two-letter alphabet, as the row asks. It also gives an injective prefix-free code with Huffman's lengths, and it allows nonnegative weights that need not sum to 1.

The other checks:
- Check 2: each main theorem and definition matches the draft apart from the Goal list's changes and the namespace (see above).
- Check 3: the Goal list's statement-level changes are all made: namespaces; no `import Mathlib`; a module docstring listing each module's results; every main theorem and `pinv`/`huffmanLength` naming its item; for 147, the iterates described and the name kept; for 150, the unused instances removed from the three helpers; for 151, `isProb_gamma_aux` removed, plus the comment on `eqOn_complexMGF_of_mgf'`, whose route I compared with Mathlib's proof and found right; for 153, `huffman_optimal` moved into the namespace with its reference rewritten and its binders kept clear of the closed section.
- Check 4: every declaration is in its namespace.
- Check 7: no main theorem's conclusion is a recursive predicate.

## Findings

1. **MINOR**: `/root/cm2-evidence/stmt/Huffman.lean`, lines 17–18 (module docstring, the `huffmanLength` item). It says "(`Fintype.card ι` steps, each merging the two lightest" and goes on "symbols, which `pick` chooses)". The Lean does not support "each": `huffmanLength p = huffAux (Fintype.card ι) p Finset.univ`, and each step merges and recurses on `s.erase (pick w s h).2` only while `2 ≤ s.card`. The last step, reached with one symbol left (`huffAux 1 w s` with `s.card = 1`), takes the `else` branch and merges nothing. So `Fintype.card ι` steps make `Fintype.card ι - 1` merges. Possible wording: "(`Fintype.card ι` steps of the recursion; each step with at least two symbols left merges the two lightest, which `pick` chooses)".

## Notes for the session (not counted as findings)

- **Imports, check 5.** No file imports `Mathlib`. Every import of the five files is the defining module of some name the file uses: the draft's proofs, the 147 witness start, or the 151 satisfiability example (checked against `loc147*.out` and `loc151*.out`, and by grep for the rest). By that reading every import is needed, and that is the library's own practice: by the same graph computation, 78 of its 130 modules, with 169 of their 438 import lines, also import something another import implies.
  - By the stricter reading, "cannot be removed", 18 lines are not needed. Removing any one of them alone leaves the full text compiling (rc 0), as the graph predicts:
    - 147: `InnerProductSpace.Spectrum`, `SpecificLimits.Basic`, `Normed.Lp.Matrix` and `LinearAlgebra.Trace`.
    - 150: `Charpoly.Basic`, `Polynomial.Div` and `Polynomial.Inductions`, all implied by the library's `GaussMarkov`.
    - 151: all except `Probability.Distributions.Gamma` and `Probability.Distributions.Gaussian.Real`.
    - 152 and 153: none.
  - The minimal sets, which compile together (`rv1-imp-*-min`), are:
    - 147: {`InnerProductSpace.Trace`, `Matrix.Hermitian`, `Archimedean.Real.Hom`};
    - 150: {`ClassicalLean.Statistics.GaussMarkov`};
    - 151: {`Distributions.Gamma`, `Distributions.Gaussian.Real`}.
  - With the minimal sets, two passages would need rewording: PowerMethod.lean lines 50–52 ("it is why the file imports [...]") and ChiSquared.lean lines 46–48 ("which is why the file imports [...]"). I did not count this, because the Goal list defines "targeted" as "no `import Mathlib`", and under the stricter reading Pseudoinverse would depend on the import list of another library module.
- **Witness sentences.** PowerMethod.lean line 34 and lines 48–52, and ChiSquared.lean lines 46–48, describe the witness at the end of the file (the matrix `!![2, 0; 0, 1]`; `k = 3` with `Measure.pi`). The statement files do not contain these witnesses yet, because they come in job 2. Each module's review should check those sentences against the witness that lands.

VERDICT: FINDINGS 1
