<!-- The order's text, as given in the prompt of Claude Code cloud session session_01HgueTamcgmkdp3A6C5qVW8 (https://claude.ai/code/session_01HgueTamcgmkdp3A6C5qVW8), copied on 2026-10-28 (UTC) by that session before any Lean file changed, per records/README.md rule 2. Its file name gives claude-ai as the source, as the order's own Setup step 5 names it. -->

# Order CLOUD-MATH-4: three bridges as three new modules

## Goal

Prove three results that join two existing modules each, and land each as a new module on branch
`cloud-math-4`, under the library's gates, with witnesses, one cold review and records. Nothing here is
drafted: you write the statements in Lean from the descriptions below, have them reviewed, then prove them.
The rows are in landing order, cheapest first.

| bridge | the result | new module (namespace = module name) | imports | main theorems (names to keep) |
|---|---|---|---|---|
| 160 | Huffman's mean length is within one bit of the entropy. For `p : ι → ℝ` on a finite type with `∑ p = 1`: `shannonEntropy p / Real.log 2 ≤ ∑ i, p i * huffmanLength p i` when every `p i ≥ 0`, and `∑ i, p i * huffmanLength p i < shannonEntropy p / Real.log 2 + 1` when every `p i > 0`. Proof: take the alphabet `Bool` (`Fintype.card Bool = 2`). The lower side is `shannonEntropy_le_sum_mul_length_of_isPrefixFree` applied to the code `huffman_optimal` gives, divided by `log 2 > 0`. The upper side is `huffman_optimal`'s optimality against the code of `exists_isPrefixFree_sum_mul_length_lt`. | `ClassicalLean.InformationTheory.HuffmanEntropy` | `ClassicalLean.InformationTheory.Huffman` (which imports SourceCoding) | `le_sum_mul_huffmanLength`, `sum_mul_huffmanLength_lt` |
| 162 | Principal components by power iteration. For `X : ι → Ω → ℝ` with each `X i` in `L²` of a finite measure `μ`, write `T = covLin X μ` (symmetric: from `isSelfAdjoint_covOp` through the continuous-linear-map lemma that turns `IsSelfAdjoint` into `IsSymmetric`, built inside the statement, not taken as a hypothesis), `hn : Module.finrank ℝ (EuclideanSpace ℝ ι) = n`, `λ = hT.eigenvalues hn` (Mathlib's order, largest first: `eigenvalues_antitone`), `u = hT.eigenvectorBasis hn ⟨0, _⟩`. **Theorem 1** (`tendsto_powerIterate_covLin`), with `2 ≤ n`, `λ ⟨1, _⟩ < λ ⟨0, _⟩` and `⟪u, x⟫ ≠ 0` as its only hypotheses beyond `hX`: both conclusions of `tendsto_powerIterate` (the `∃ C` rate bound with ratio `λ 1 / λ 0` and the limit `u`), absolute values gone. The dominance `|λ i| ≤ λ 1` for `i ≠ 0` is derived, not assumed: every eigenvalue is at least `0` (for an eigenvector `v`, `c ‖v‖² = (covOp X μ).reApplyInnerSelf v = variance (mix X v) μ ≥ 0`, by `reApplyInnerSelf_covOp` at CovarianceDirections line 262 and `variance_nonneg`), and `eigenvalues_antitone`. **Theorem 2** (your name), with only `hX` and `0 < n`: `variance (mix X (WithLp.ofLp u)) μ = λ ⟨0, _⟩ ∧ ∀ w, ‖w‖ = 1 → variance (mix X (WithLp.ofLp w)) μ ≤ λ ⟨0, _⟩`. The equality is `variance_mix_eq_of_hasEigenvector`; the bound needs the top eigenvalue to dominate every Rayleigh quotient, which MinMax's `sum_eigenvalues_eq_iSup` at `k = 1` gives (MinMax is imported by CovarianceDirections), or an expansion of `w` in `eigenvectorBasis`; `exists_isMaxOn_variance_mix` alone does not give it. | `ClassicalLean.Probability.PrincipalComponents` | `ClassicalLean.Probability.CovarianceDirections`, `ClassicalLean.Analysis.PowerMethod` | `tendsto_powerIterate_covLin`, and theorem 2 (your name) |
| 161 | The James–Stein estimator's risk at the origin is `2` in every dimension `d ≥ 3`: `∫ x, sqNorm (jamesStein x) ∂normalVec d 0 = 2`, against the risk `d` of `x` itself. Proof: under `normalVec d 0` the coordinates are independent standard normals, so `hasLaw_sum_sq_gaussian` gives `sqNorm` the law `gammaMeasure (d/2) (1/2)`; its inverse moment is `(1/2)/(d/2 − 1) = 1/(d − 2)` (Mathlib's gamma density, `Real.integral_rpow_mul_exp_neg_mul_Ioi` and `Real.Gamma_add_one`); then `integral_sqNorm_jamesStein_sub_eq` at `θ = 0` gives `d − (d − 2)²/(d − 2) = 2`. State the inverse moment as a theorem of its own too: `∫ x, (sqNorm x)⁻¹ ∂normalVec d 0 = 1 / (d − 2)` for `3 ≤ d`. | `ClassicalLean.Statistics.JamesSteinRisk` | `ClassicalLean.Statistics.JamesStein`, `ClassicalLean.Probability.ChiSquared` | `integral_sqNorm_jamesStein_zero`, and the inverse moment (your name) |

Each bridge's row in the bridges file is quoted under "The bridge rows" at the end of this order. The
statement you write must say what its row says; where Lean makes you choose (an index set, how the
eigenvalue order is stated, a cast), choose the form closest to the row and to the theorems it rests on,
and say what you chose in the docstring. Hypotheses are what the proof needs and no more.

## Branch rules (hard)

These override any branch this session was assigned; do not push an assigned `claude/*` branch.
- Work only on `cloud-math-4`. First confirm `origin/cloud-math-4` is `67d05bfbd0efa80f0de679813b54500ae8c69122`
  and note `git ls-remote origin master` (you report it again at the end). If the branch is missing or
  differs, stop and report.
- Push only with `git push origin cloud-math-4`. Never push `master` or `main`, never force-push, never reset
  a pushed commit, open no pull request, merge nothing on GitHub. Every undo is a new commit.

## Scope

You may: add the three module files under `ClassicalLean/`; add their three import lines at the end of the
import block of `ClassicalLean.lean`; add HELPER lines to `tools/vacuity_reviewed.txt` (rule 4); write
`records/` (rule 6); add `incoming/REPORT.md` and `incoming/reviews/`.
You may not change any existing module, any other file under `tools/`, `HANDOFF.md`, `ROADMAP.md`,
`records/rules.toml`, the lake files, `lean-toolchain` or `.github/`; nor any existing row of
`records/orders/INDEX.md` or `records/CLAIMS.md` (VACUITY-5's push is recorded by LEAN-37, on its own
branch). Needing to is a stop: report it.

## Read first (in the repository)

`records/README.md`; `HANDOFF.md` sections 0, 4 (the gates, "Satisfiability witnesses" with its dated
cases) and 5 (naming); the six modules named above, at least their docstrings and the statements listed;
`ClassicalLean/Analysis/PowerMethod.lean`'s witness (it proves concrete eigenvalue facts for a symmetric
map: the pattern for 162's); `ClassicalLean/Probability/LongestRun.lean`'s first witness (a uniform measure
on `Fin 2 → Bool` with independence by `iIndepSet_iff_meas_biInter`); CLOUD-MATH-3's order copy under
`records/orders/`, its INDEX and CLAIMS rows and round 68, as the pattern for your records.

## Setup

1. Network: `curl -sSI https://cache.mathlib.org/ | head -3`. A connection error, or a 403 from the
   session's proxy, is a stop: report the output and do not build Mathlib from source.
2. Install the toolchain from `lean-toolchain` (elan, from GitHub) and run `lake exe cache get`. A refused
   download is a stop.
3. Starting gates, before any new file exists: `lake build` (predicted 4193 jobs, 0 warnings; run it in the
   background if it may pass a 10-minute limit; if the VM kills it for memory, retry once with
   `LEAN_NUM_THREADS=2 lake build`, then stop), `lake env lean tools/AxiomGate.lean` (PASS 3666),
   `python3 -I tools/check_sorry.py` and `python3 -I tools/check_records.py` (PASS 140), and
   `lake env lean tools/VacuityGate.lean` (PASS; note its reviewed-helper count, the baseline for End check 1). Save every output
   in `$HOME/cm4/` with its sha256. A different value is a stop.
4. Probe every name the order cites, and every other name you will use, with `#check @Name` lines in one
   scratch file per new module, in `$HOME/cm4/` (never under `ClassicalLean/`, where check_sorry and
   check_records would read it), that imports exactly that module's imports, run with `lake env lean` from the
   repository root. Among them: `LinearMap.IsSymmetric.eigenvalues_antitone`, `hasEigenvalue_eigenvalues`,
   `reApplyInnerSelf_covOp`, `variance_nonneg`, MinMax's `sum_eigenvalues_eq_iSup`, the lemma turning a
   continuous linear map's `IsSelfAdjoint` into `IsSymmetric`, and the instance
   `(inferInstance : IsFiniteMeasure ((4⁻¹ : ℝ≥0∞) • Measure.count : Measure (Fin 2 → Bool)))` (if it fails,
   162's witness uses `(4⁻¹ : ℝ≥0) • Measure.count` instead). A name
   that is unknown is not used until you find what it is called; say so in the report.
5. Records first, one commit, no `.lean` file: this order's text from "# Order CLOUD-MATH-4" to the end as
   `records/orders/<UTC>__claude-ai__order-cloudmath4-huffman-entropy-principal-components-james-stein-risk.md`;
   its INDEX row at the bottom (`| CLOUD-MATH-4 |`, in CLOUD-MATH-3's row's form); a CLAIMS row at the bottom
   naming this session and the three module paths; round 77's fragment
   `records/rounds/<UTC>__round-77-huffman-entropy-principal-components-james-stein-risk.md` naming the three
   module files by full path. Push.

## Rules of this order

1. **Statements first, then one cold review, then proofs.** For each bridge, write its module with every
   statement final and every proof `sorry`, its witnesses complete (a witness proves the hypotheses, not the
   theorem, so it can be finished now), its docstrings and its namespace. Elaborate each with `lake env lean`
   (only `sorry` warnings). Then one cold review of all three (rule 5). Proofs come after its verdict. A
   statement a proof later forces you to change is a narrowing: rule 7.
2. **Namespaces and imports.** Every declaration, private ones included, sits inside its module's namespace
   (the axiom gate checks only constants under `ClassicalLean`). Imports are the table's, targeted; no
   `import Mathlib`, no Mathlib import line the proofs do not need. An `open` line that reaches another
   module's names (`ClassicalLean.Simplex` for `shannonEntropy`, `ClassicalLean.InformationTheory.Huffman`,
   `ClassicalLean.Statistics`, and so on) sits after the imports and before the namespace.
3. **Witnesses** in HANDOFF section 4's form: for each main theorem with a hypothesis, one `example` after the
   module's last line that applies the theorem itself, `example := Full.name (x := …) h₁ h₂ …`, every chosen
   argument by name and every binder before the colon supplied, optional `open … in` lines of their own and
   no other `open` than the module's top-level ones, the docstring "The hypotheses of `name` hold together:
   …" saying what moves, one inline block with no helper declaration, none of `sorry`, `admit`,
   `native_decide`, `implemented_by`, `axiom`, `set_option`, nor `(config :=` or any `reduceBool`-family
   name. Not degenerate (rule 3 of HANDOFF section 4 and its dated cases: no empty, zero or single-point
   case, no junk value, no boundary where a constant vanishes, families and matrices of size at least 2
   unless the theorem fixes it). Models to start from, each to be checked like any witness:
   - 160, both theorems: `ι = Fin 3`, `p = ![1/2, 1/3, 1/6]` (positive, summing to `1`, not uniform and not
     a power of `1/2` in every entry, so neither inequality is an equality).
   - 162: `ι = Fin 2`, `Ω = Fin 2 → Bool` with `μ = (4⁻¹ : ℝ≥0∞) • Measure.count`, `X 0 ω = if ω 0 then 2 else
     -2`, `X 1 ω = if ω 1 then 1 else -1`: means `0`, variances `4` and `1`, covariance `0`, so the covariance
     map is `diag(4, 1)`, eigenvalues `4 > 1 > 0`; `x = (1, 1)`. What moves: the second eigenvalue is not `0`,
     so the iterates never reach `u` in finitely many steps and the rate `1/4` is not `0`. If Mathlib's order
     of the eigenvalues makes `i₀`, `i₁` hard to pin, follow PowerMethod's witness.
   - 161: `d = 4` (the theorems fix `d ≥ 3`; `d − 2 = 2` keeps away from the boundary).
   - A theorem with no hypothesis gets none (HANDOFF: "for a theorem with hypotheses").
4. **Vacuity gate.** A flag or an UNCHECKED verdict on a main theorem makes its bridge not closed. On a
   helper: rewrite it, remove it if Mathlib or `simp` already does its job, or list it in
   `tools/vacuity_reviewed.txt` as HELPER with a one-line reason the cold review checks.
5. **One cold review,** by one fresh subagent that has not seen your work, after rule 1's statement stage:
   give it the three modules as they stand (statements, witnesses, docstrings, helpers' statements), the
   three bridge rows below, HANDOFF section 4's "Satisfiability witnesses" paragraph with its dated cases, and
   the statements of the theorems each bridge rests on, copied from their modules by a script, not retyped.
   It checks each statement against its row (FAITHFUL, GENERALIZED or WEAKER; WEAKER is a finding), that no
   hypothesis is missing or extra, each witness against rule 3 (doing the arithmetic), namespaces and
   imports. Its report goes to `incoming/reviews/review-1.md`. Fix what it finds; a second pass, on the fixes
   only, only if a fix changes a statement or a witness's arguments.
6. **Records.** As `records/README.md` says, including its rule 1's per-module theorem-constant count and its
   statement of which tree each count was measured on. Round 77's fragment names the three module files in full, says
   each bridge was proved by this session (no draft) from the row's sketch, gives each module's commit hash
   in a follow-up edit once it exists (never predicted), and lists every witness and what moves in it. Close
   your CLAIMS row and set your INDEX row's state at the end.
7. **Not closed.** A bridge whose proofs do not build after two hours of work on it (log `date` when you
   start it), or whose statement had to be narrowed in a way its row does not allow, is not closed: its
   module, import line and vacuity entries removed by a new commit, and round 77, the CLAIMS row and the
   report saying which and why. The others go on. A narrowing that keeps the row's meaning (a hypothesis
   the proof needs and the row left implicit) is said plainly in the docstring and the report.
8. **Push often:** after the records commit and after each bridge lands, so nothing is lost if the session
   stops. Each push starts a CI run; an older run on the branch is cancelled, which is fine.
9. **A count is what its output says.** Every count in round 77 and the report is read from a saved output in
   `$HOME/cm4/` and cited by its file name.

## The work, per bridge (in the table's order)

Proofs in place of the `sorry`s; `lake build ClassicalLean.<Area>.<Module>`, 0 errors, 0 warnings;
`python3 -I tools/witness_gate.py <Area>/<Module>.lean` (the path relative to `ClassicalLean/`), every block
OK, `copy-error=0`; then the module's import line added to `ClassicalLean.lean` (only now, so that no pushed
commit imports a module not yet committed), `lake build` of the root (the vacuity gate imports
`ClassicalLean`, and `lake env lean` does not rebuild it), and `lake env lean tools/VacuityGate.lean` (rule
4), its lines for the new theorems quoted in round 77; one commit staged by path (the module, its import line
and, if rule 4 added one, its `tools/vacuity_reviewed.txt` line); push.

## End checks, in this order

1. Before running them, write `$HOME/cm4/expected.txt` with the expected result of each, and its sha256:
   `lake build` (4193 plus the new modules plus any Mathlib module a new import line brings that is
   not already in the closure, counted by a scratch file printing `env.header.moduleNames` before and after,
   0 warnings), AxiomGate (3666 plus each new module's theorem-constant count, measured as
   `records/README.md` rule 1 says: `env.getModuleFor?` under the axiom gate's `.thmInfo` predicate, not a
   name count from the source), check_sorry and check_records (140 plus the modules landed), VacuityGate PASS with its
   reviewed-helper count (Setup 3's plus any HELPER line added), `python3 -I tools/witness_gate.py` on the three new modules (OK equal to the
   witnesses written, `copy-error=0`), `python3 tools/compile_rules.py drift records/rules.toml HANDOFF.md`
   PASS (neither file changes). Then run each and save its output.
2. Not run here (they run on DSMain at the merge, MERGE-4): gate 7, the banned-vocabulary scan (its term
   list is kept only on DSMain), the whole-library witness gate, the bridge search and the report tool.
3. `grep -rnwE 'reduceBool|reduceNat|ofReduceBool|ofReduceNat|trustCompiler|native|native_decide|implemented_by|admit|sorry|plausible|slim_check|evalExpr|evalConst'`
   and `grep -rn '(config *:='` on the three new files: nothing. `git diff --name-only 67d05bf HEAD`: only the
   three modules, `ClassicalLean.lean`, `records/`, `incoming/` and, if a helper was listed,
   `tools/vacuity_reviewed.txt`. `git diff 67d05bf HEAD -- ClassicalLean.lean`: only the added import lines.
4. Records: round 77 completed with the commit hashes and the counts from the saved outputs; CLAIMS closed;
   INDEX set; check_records PASS; push.
5. `incoming/REPORT.md` (and push it): each bridge's final statements, verdict, witnesses and what moves;
   every probe that found a name unknown; the review and its fixes; each end check's expected and observed
   value, cited by file; anything not closed or narrowed; `git ls-remote origin master` at the start and the
   end; the branch's last commit. Then tell Dustin in a few plain sentences what was proved, define any
   technical term the first time, and give the last commit's hash.

## Done means

Branch `cloud-math-4` from `67d05bf`, pushed, with: the records commit; one commit per bridge landed, each
module building with 0 warnings, no `sorry`, no new axiom; every witness OK in the witness gate and passed by
the review; the review in `incoming/reviews/`; every end check as expected or each miss reported; records
closed; `incoming/REPORT.md`. Or a bridge reported not closed under rule 7 and undone. Nothing on `master`.

## After the session (claude-ai)

claude-ai checks the branch against `67d05bf` (files, imports, no existing module changed), reruns the
gates in its own clone, and writes MERGE-4 for DSMain after LEAN-37 is pushed: the merge, then the gates that
did not run here (gate 7, the banned scan, the whole-library witness gate, the bridge search, the report
tool), and HANDOFF's and ROADMAP's entries.

## Not in this order

LEAN-38's pair-by-pair reads of MERGE-2's and MERGE-3's searches (plan 2 ruling 5's second half, which stays
on DSMain); TWINS-1; GATE-2; HANDOFF and ROADMAP entries (MERGE-4); anything on `master`.

## The bridge rows

(Quoted from `lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md`, a lane file this session cannot
read, rows 160 to 162, as filed by order MERGE-2's bridge search.)

| # | area | the result | Lean names | module | rests on | cost |
|---|---|---|---|---|---|---|
| 160 | 5, bridge | Huffman's mean length lies within one bit of the entropy: for weights `p i > 0` summing to `1`, `H(p) / log 2 ≤ ∑ i, p i * huffmanLength p i < H(p) / log 2 + 1`. The lower side is Shannon's bound for the binary Huffman code that item 153's `huffman_optimal` builds (`shannonEntropy_le_sum_mul_length_of_isPrefixFree`); the upper side compares that code, by `huffman_optimal`, with the Shannon code of `exists_isPrefixFree_sum_mul_length_lt` (alphabet `Bool`, so `2 ≤ Fintype.card α`). Shared object: injective prefix-free codes and their mean length. Found as the new shape keys `Kraft-type sum` and `binary strings: InformationTheory.Huffman × InformationTheory.SourceCoding` (import-related: Huffman imports SourceCoding, for `exists_isPrefixFree_length_eq` only); checked by reading both statements, not elaborated. Not load-bearing for any scheduled row. | `sum_mul_huffmanLength_lt`, `le_sum_mul_huffmanLength` (proposed) | ClassicalLean.InformationTheory.Huffman | item 153 (`huffman_optimal`, `huffmanLength`), library `exists_isPrefixFree_sum_mul_length_lt`, `shannonEntropy_le_sum_mul_length_of_isPrefixFree` | S |
| 161 | L, bridge | The James–Stein estimator's risk at the origin is `2`, for every `d ≥ 3`: `∫ x, sqNorm (jamesStein x) ∂normalVec d 0 = 2`. Under `normalVec d 0` (the product of `d` laws `gaussianReal 0 1`) the coordinates are independent standard normals, so by item 151's `hasLaw_sum_sq_gaussian` `sqNorm` has the law `gammaMeasure (d/2) (1/2)`; its inverse moment is `(1/2)/(d/2 − 1) = 1/(d − 2)` (from Mathlib's gamma integral and `Γ(a) = (a − 1) Γ(a − 1)`, a step neither module has), and the library's risk identity `integral_sqNorm_jamesStein_sub_eq` gives `d − (d − 2)² / (d − 2) = 2`, against the risk `d` of `X` itself. Shared object: the law of `‖X‖²` for a standard normal vector. Found as the new pair `Probability.ChiSquared × Statistics.JamesStein` (import-unrelated, score 66.2, rank 23); checked by reading both modules (`normalVec` is `Measure.pi fun i ↦ gaussianReal (θ i) 1`; item 151's witness builds its family the same way), not elaborated. Not load-bearing for any scheduled row. | `integral_sqNorm_jamesStein_zero` (proposed) | ClassicalLean.Statistics.JamesStein, importing Probability.ChiSquared | item 151 (`hasLaw_sum_sq_gaussian`), library `integral_sqNorm_jamesStein_sub_eq`, Mathlib `gammaPDFReal`, `Real.integral_rpow_mul_exp_neg_mul_Ioi`, `Real.Gamma_add_one` | M |
| 162 | 6, bridge | Principal components by power iteration: for square-integrable `X i` under a finite measure, when the largest eigenvalue `λ₀` of the covariance operator `covLin X μ` is strictly larger than the next (`λ₁ < λ₀`, Mathlib's order) and the start `x` has a nonzero component along its eigenvector `u`, the rescaled iterates `(covLin X μ) ^ k x` tend to `u`, at rate `(λ₁/λ₀)^k`, and `u` is a direction of largest variance: `variance (mix X u) μ = λ₀`, the maximum over unit `w`. Item 147's `tendsto_powerIterate` gives the convergence (the operator is symmetric, `isSelfAdjoint_covOp`, and positive semidefinite, so every eigenvalue is at least `0` and `|λ i| ≤ λ₁` for `i ≠ 0`); `variance_mix_eq_of_hasEigenvector` and `exists_isMaxOn_variance_mix` give the variance. Shared object: the eigenvectors of a covariance matrix. Found as the new shape key `eigenvalues: Analysis.PowerMethod × Probability.CovarianceDirections` (import-unrelated), also a new pair (score 23.5); checked by reading both statements, not elaborated. Not load-bearing for any scheduled row. | `tendsto_powerIterate_covLin` (proposed) | ClassicalLean.Probability.CovarianceDirections, importing Analysis.PowerMethod | item 147 (`tendsto_powerIterate`), item 96's module (`exists_isMaxOn_variance_mix`, `variance_mix_eq_of_hasEigenvector`, `posSemidef_covMatrix`) | S |
