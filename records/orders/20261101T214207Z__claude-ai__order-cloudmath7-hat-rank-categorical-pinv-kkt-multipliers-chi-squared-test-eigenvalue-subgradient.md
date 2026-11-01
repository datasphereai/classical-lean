# Order CLOUD-MATH-7: five bridges as five new modules

## Goal

Prove five results that join two existing modules each, and land each as a new module on branch
`cloud-math-7`, under the library's gates, with witnesses, one cold review and records. The five
statements are given: each was written and elaborated with `sorry` by order LEAN-38 (a reading order on
DSMain, no repository change) and re-elaborated by claude-ai (rc 0, only the `sorry` warning). You prove
them. The rows are in landing order, cheapest first. Each row's text in the bridges file is quoted under
"The bridge rows" at the end; each statement is quoted under "The statements" below.

| bridge | the result | new module (namespace = module name) | imports | main theorems (names to keep) |
|---|---|---|---|---|
| 170 | The hat matrix of any design has rank and trace equal to the design's rank, rank-deficient designs included; the residual maker has rank `m − rank A`. Proof: `H = A * pinv A` is idempotent by `pinv_spec` (`A pinv A A = A`); `rank_eq_trace_of_isIdempotentElem` gives `rank H = trace H`; `A = H A` and `H = A (pinv A)` bound the rank both ways (`Matrix.rank_mul_le_left`, `rank_mul_le_right`); `sum_rank_eq_iff` (or rank of a complementary idempotent) gives `rank (1 − H) = m − rank A`. Cochran's `rank_mul_leastSquares` is the full-rank case. | `ClassicalLean.Algebra.HatMatrixRank` | `ClassicalLean.Algebra.Pseudoinverse`, `ClassicalLean.Statistics.Cochran` | `rank_mul_pinv_eq` |
| 172 | The pseudoinverse of a categorical covariance is the Fisher–Rao form on the tangent space: for `p > 0` summing to `1`, `pinv (categoricalCov p) = P * diagonal (1/p) * P` with `P = 1 − (1/n) 1 1ᵀ`, and `categoricalCov p * pinv (categoricalCov p) = P`. Proof: `pinv_unique` with `X = P D⁻¹ P` and `Σ = categoricalCov p = D − p pᵀ`: `Σ 1 = 0` (`categoricalCov_mulVec_one`), so `Σ P = Σ`; `Σ D⁻¹ = 1 − p 1ᵀ` and `1ᵀ P = 0`, so `Σ X = P`, symmetric; `X Σ = (Σ X)ᵀ = P`; `X Σ X = P X = X`; `Σ X Σ = P Σ = Σ`. | `ClassicalLean.Algebra.CategoricalPseudoinverse` | `ClassicalLean.Algebra.Pseudoinverse`, `ClassicalLean.Simplex.SecondOrder` | `pinv_categoricalCov` |
| 168 | Under Slater's condition one multiplier vector serves every minimiser: the minimisers of a convex, differentiable problem are exactly the feasible points where that `w` meets complementary slackness and stationarity. Proof: `exists_kkt_of_slater` (KKT) gives `w ≥ 0` at `xbar`; the Lagrangian `L = f + ∑ w i • g i` is convex and its gradient vanishes at `xbar`, so `L` is minimised everywhere at the value `f xbar` (`add_inner_gradient_le`, GradientDescent); a feasible minimiser `y` has `L y ≤ f y = f xbar`, so `y` minimises `L` too: its gradient vanishes there and `∑ w i * g i y = 0` with each term `≤ 0`, so each is `0`. The converse is `isMinOn_of_kkt` (GradientDescent). | `ClassicalLean.Analysis.KKTMultipliers` | `ClassicalLean.Analysis.GradientDescent`, `ClassicalLean.Analysis.KKT` | `exists_multipliers_isMinOn_iff` |
| 169 | The chi-squared test of a normal variance is uniformly most powerful for `v ≤ v₀` against `v > v₀`, at the level `P(χ²ₖ > c/v₀)`. Proof: the product density of `k` draws `N(0, v)` is `(2πv)^(−k/2) exp(−S/(2v))` with `S = ∑ x i ²`, so the family has a monotone likelihood ratio in `S`; `isUniformlyMostPowerful_of_monotoneLikelihoodRatio` (NeymanPearson) makes `thresholdTest S c 0` uniformly most powerful at its size under `v₀`; that size is `P_{v₀}(S > c)`, and under `v₀`, `S / v₀` is a sum of `k` squared standard normals, whose law is `gammaMeasure (k/2) (1/2)` by `hasLaw_sum_sq_gaussian` (ChiSquared). | `ClassicalLean.Statistics.ChiSquaredTest` | `ClassicalLean.Probability.ChiSquared`, `ClassicalLean.Statistics.NeymanPearson` | `isUniformlyMostPowerful_sum_sq_gaussian` |
| 171 | Minimising the largest eigenvalue of an affine family of symmetric maps by the subgradient method, at the rate of `min_sub_le_of_subgradient`. Proof: for `T x = A₀ + ∑ i, x i • A i` and `u` the unit top eigenvector of `T x` (`eigenvectorBasis` at index `0`; index `0` is the largest by `eigenvalues_antitone`), `λ₀(T z) ≥ ⟪T z u, u⟫ = λ₀(T x) + ∑ i, (z i − x i) ⟪A i u, u⟫` (MinMax's Courant–Fischer, or the top eigenvalue's Rayleigh bound), so `g x = (⟪A i u, u⟫)ᵢ` is a subgradient of `x ↦ λ₀(T x)`; then `min_sub_le_of_subgradient` (SubgradientMethod) gives the bound. | `ClassicalLean.Analysis.EigenvalueSubgradient` | `ClassicalLean.Algebra.MinMax`, `ClassicalLean.Analysis.SubgradientMethod` | `min_sub_le_of_subgradient_eigenvalues` |

The statements below are the ones to prove, word for word, inside each module's namespace (with the `open`
lines they need after the imports, as rule 2 says; you may drop a namespace prefix an `open` makes
redundant). Change a statement only if it is false or does not elaborate in the module; any change is
a narrowing under rule 7 unless it only generalises (fewer hypotheses, or a wider type), and is said in the
docstring and the report. Each docstring keeps the scratch file's text, says the bridge's row, and drops the
"LEAN-38 scratch" header. Add no definition or notation that a main statement unfolds through.

## The statements

(From order LEAN-38's scratch files `~/lean/lean38-checks/b168.lean` to `b172.lean` on DSMain,
copied by script; each file's sha256 is given. Names are written in full; inside your module you may
shorten them after an `open` line.)

### Row 170 (b170.lean, sha256 `9b8a265241706e8c921499a873b79d069c08bfec90988024092589062b05bc96`)

Imports and opens of the scratch file: `import ClassicalLean.Algebra.Pseudoinverse`; `import ClassicalLean.Statistics.Cochran`; `open Matrix`

```lean
/-- **The hat matrix of any design has rank and trace equal to the design's rank.** For every real
`m × n` matrix `A`, rank-deficient included, `H = A * pinv A` is a symmetric idempotent with
`rank H = trace H = rank A`, and the residual maker `1 - H` has rank `m - rank A`: the residual
degrees of freedom. `Statistics.Cochran`'s `rank_mul_leastSquares` is the full-rank case. -/
theorem rank_mul_pinv_eq {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) :
    (A * ClassicalLean.Algebra.Pseudoinverse.pinv A).rank = A.rank ∧
      (A * ClassicalLean.Algebra.Pseudoinverse.pinv A).trace = (A.rank : ℝ) ∧
      (1 - A * ClassicalLean.Algebra.Pseudoinverse.pinv A).rank = Fintype.card m - A.rank := by
  sorry
```

### Row 172 (b172.lean, sha256 `903d989b47a4933f9849cc1b1a94e9048824756983756bbebcd8e3dce1b138f9`)

Imports and opens of the scratch file: `import ClassicalLean.Algebra.Pseudoinverse`; `import ClassicalLean.Simplex.SecondOrder`; `open Matrix`; `open ClassicalLean.Algebra.Pseudoinverse ClassicalLean.Simplex`

```lean
/-- **The pseudoinverse of a categorical covariance is the Fisher–Rao form on the tangent space.**
For a strictly positive probability vector `p` on `n = card ι` points, write
`P = 1 - (1/n) 1 1ᵀ` (the projection onto vectors summing to `0`). Then
`pinv (categoricalCov p) = P * diagonal (1/p) * P`, and `categoricalCov p * pinv (categoricalCov p) = P`.
(A consequence, not stated here: for tangent vectors `u`, `v`, sums `0`, `P u = u`, so
`u ⬝ᵥ (pinv (categoricalCov p) *ᵥ v) = ∑ i, u i * v i / p i`, the Fisher–Rao form.) -/
theorem pinv_categoricalCov {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → ℝ}
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1) :
    pinv (categoricalCov p) =
        (1 - (Fintype.card ι : ℝ)⁻¹ • Matrix.of fun _ _ ↦ (1 : ℝ)) *
          Matrix.diagonal (fun i ↦ (p i)⁻¹) *
          (1 - (Fintype.card ι : ℝ)⁻¹ • Matrix.of fun _ _ ↦ (1 : ℝ)) ∧
      categoricalCov p * pinv (categoricalCov p) =
        1 - (Fintype.card ι : ℝ)⁻¹ • Matrix.of fun _ _ ↦ (1 : ℝ) := by
  sorry
```

### Row 168 (b168.lean, sha256 `035283a19f16b3d90c4b8137c51a4df9d6211739cb90bc4db553f24f7144204c`)

Imports and opens of the scratch file: `import ClassicalLean.Analysis.GradientDescent`; `import ClassicalLean.Analysis.KKT`; `open scoped RealInnerProductSpace`

```lean
/-- Under Slater's condition one multiplier vector serves every minimiser: there is `w ≥ 0` such
that the minimisers of a convex, differentiable problem are exactly the feasible points where `w`
satisfies complementary slackness and stationarity. -/
theorem exists_multipliers_isMinOn_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] {f : E → ℝ} {g : ι → E → ℝ} {f' : E → E}
    {g' : ι → E → E} {xbar : E} (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hf' : ∀ x, HasGradientAt f (f' x) x) (hg' : ∀ i x, HasGradientAt (g i) (g' i x) x)
    (hslater : ∃ x0, ∀ i, g i x0 < 0) (hxbar : ∀ i, g i xbar ≤ 0)
    (hmin : IsMinOn f {x | ∀ i, g i x ≤ 0} xbar) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ ∀ y : E,
      ((∀ i, g i y ≤ 0) ∧ IsMinOn f {x | ∀ i, g i x ≤ 0} y) ↔
        ((∀ i, g i y ≤ 0) ∧ (∀ i, w i * g i y = 0) ∧ f' y + ∑ i, w i • g' i y = 0) := by
  sorry
```

### Row 169 (b169.lean, sha256 `4f9f973e93f879f1a457402087a7274408a3d714dbd3002ed99c3671e92db8f1`)

Imports and opens of the scratch file: `import ClassicalLean.Probability.ChiSquared`; `import ClassicalLean.Statistics.NeymanPearson`; `open MeasureTheory ProbabilityTheory`; `open scoped NNReal`

```lean
/-- **The chi-squared test of a normal variance is uniformly most powerful.** For `k ≥ 1`
independent `N(0, v)` draws (density `∏ i, gaussianPDFReal 0 v (x i)` against Lebesgue measure on
`Fin k → ℝ`), the test that rejects when `∑ i, x i ^ 2 > c` is uniformly most powerful for
`v ≤ v₀` against `v > v₀` at the level `α = P(χ²ₖ > c / v₀)`, the chi-squared law being Mathlib's
`gammaMeasure (k / 2) (1 / 2)`. -/
theorem isUniformlyMostPowerful_sum_sq_gaussian {k : ℕ} (hk : 0 < k)
    (v₀ : Set.Ioi (0 : ℝ≥0)) (c : ℝ) :
    ClassicalLean.Statistics.IsUniformlyMostPowerful (volume : Measure (Fin k → ℝ))
      (fun (v : Set.Ioi (0 : ℝ≥0)) (x : Fin k → ℝ) ↦ ∏ i, gaussianPDFReal 0 v.1 (x i)) v₀
      ((gammaMeasure ((k : ℝ) / 2) (1 / 2)).real (Set.Ioi (c / (v₀.1 : ℝ))))
      (ClassicalLean.Statistics.thresholdTest (fun x ↦ ∑ i, x i ^ 2) c 0) := by
  sorry
```

### Row 171 (b171.lean, sha256 `a234a461f42f25fc7fbdc3ab0122bded6ab1e92e46486ff9407729248a88d228`)

Imports and opens of the scratch file: `import ClassicalLean.Algebra.MinMax`; `import ClassicalLean.Analysis.SubgradientMethod`; `open scoped InnerProductSpace`

```lean
/-- **Minimising the largest eigenvalue by the subgradient method.** For symmetric maps
`A₀, A 0, …, A (m - 1)` of a real inner product space `F` of dimension `n + 1`, let
`f x = λ₀(A₀ + ∑ i, x i • A i)`, the largest eigenvalue. With `u x` the unit eigenvector of that
eigenvalue (Mathlib's `eigenvectorBasis` at index `0`), the vector `g x = (⟪A i (u x), u x⟫)ᵢ` is
a subgradient of `f` at `x` (Courant–Fischer: `λ₀(T y) ≥ ⟪T y u, u⟫` for unit `u`), so the
subgradient method `x (k + 1) = x k - η g (x k)`, with `‖g‖ ≤ G`, has the rate of
`min_sub_le_of_subgradient`. -/
theorem min_sub_le_of_subgradient_eigenvalues {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {n m : ℕ} (hn : Module.finrank ℝ F = n + 1)
    (A₀ : F →ₗ[ℝ] F) (A : Fin m → F →ₗ[ℝ] F)
    (hT : ∀ x : EuclideanSpace ℝ (Fin m), (A₀ + ∑ i, WithLp.ofLp x i • A i).IsSymmetric)
    (x : ℕ → EuclideanSpace ℝ (Fin m)) (z : EuclideanSpace ℝ (Fin m)) (η G : ℝ) (T : ℕ)
    (hη : 0 < η) (hTpos : 0 < T)
    (hg : ∀ k, ‖WithLp.toLp 2 (fun i ↦ ⟪A i ((hT (x k)).eigenvectorBasis hn 0),
        (hT (x k)).eigenvectorBasis hn 0⟫_ℝ)‖ ≤ G)
    (hstep : ∀ k, x (k + 1) = x k - η • WithLp.toLp 2 (fun i ↦
        ⟪A i ((hT (x k)).eigenvectorBasis hn 0), (hT (x k)).eigenvectorBasis hn 0⟫_ℝ)) :
    (Finset.range T).inf' ⟨0, Finset.mem_range.mpr hTpos⟩
        (fun k ↦ (hT (x k)).eigenvalues hn 0) - (hT z).eigenvalues hn 0 ≤
      (‖x 0 - z‖ ^ 2 + η ^ 2 * G ^ 2 * T) / (2 * η * T) := by
  sorry
```

## Branch rules (hard)

These override any branch this session was assigned; do not push an assigned `claude/*` branch.
- Work only on `cloud-math-7`. First `git fetch origin cloud-math-7` and
  `git switch -c cloud-math-7 --track origin/cloud-math-7` (a fresh clone may hold only another branch), then confirm `origin/cloud-math-7` is `d723fbfd171cf9c018ddc0160446984ef1daffee`
  and note `git ls-remote origin master` (you report it again at the end). If the branch is missing or
  differs, stop and report.
- Push only with `git push origin cloud-math-7`. Never push `master` or `main`, never force-push, never reset
  a pushed commit, open no pull request, merge nothing on GitHub. Every undo is a new commit.

## Scope

You may: add the five module files under `ClassicalLean/`; add their five import lines at the end of the
import block of `ClassicalLean.lean`; add HELPER lines to `tools/vacuity_reviewed.txt` (rule 4); write
`records/` (rule 6); add `incoming/REPORT.md` and `incoming/reviews/`.
You may not change any existing module (Pseudoinverse, KKT and the rest stay as they are, even where a
lemma you need is private there: copy the step into your module), any other file under `tools/`,
`HANDOFF.md`, `ROADMAP.md`, `records/rules.toml`, the lake files, `lean-toolchain` or `.github/`; nor any
existing row of `records/orders/INDEX.md` or `records/CLAIMS.md` (adding LEAN-38's INDEX row, Setup 5, is allowed). Needing to is a stop: report it.

## Read first (in the repository)

`records/README.md`; `HANDOFF.md` sections 0, 4 (the gates, "Satisfiability witnesses" with its dated
cases) and 5 (naming); the nine modules named in the table (Pseudoinverse, Cochran, SecondOrder, GradientDescent, KKT,
ChiSquared, NeymanPearson, MinMax, SubgradientMethod), and FisherRao, which SecondOrder imports, at least
their docstrings and the statements the proofs use; the library witnesses named under rule 3 (the patterns
for yours); CLOUD-MATH-4's order copy under
`records/orders/`, its INDEX and CLAIMS rows and round 77, as the pattern for your records.

## Setup

1. Network: `curl -sSI https://cache.mathlib.org/ | head -3`, for the report only. A connection error, or a
   403 whose body or headers name the session's proxy, is a stop: report the output and do not build Mathlib
   from source. A 403 or 404 from the cache server itself is not a stop; Setup 2's `lake exe cache get` is
   the test.
2. Install the toolchain from `lean-toolchain` (elan, from GitHub) and run `lake exe cache get`. A refused
   download is a stop.
3. Starting gates, before any new file exists: `lake build` (predicted 4206 jobs, 0 warnings; run it in the
   background if it may pass a 10-minute limit; if the VM kills it for memory, retry once with
   `LEAN_NUM_THREADS=2 lake build`, then stop), `lake env lean tools/AxiomGate.lean` (PASS 3914),
   `python3 -I tools/check_sorry.py` and `python3 -I tools/check_records.py` (PASS 153), and
   `lake env lean tools/VacuityGate.lean` (PASS, 1 reviewed helper). Save every output in `$HOME/cm7/` with
   its sha256. A different value is a stop.
4. Probe every name the order cites, and every other name you will use, with `#check @Name` lines in one
   scratch file per new module, in `$HOME/cm7/` (never under `ClassicalLean/`, where check_sorry and
   check_records would read it), that imports exactly that module's imports, run with `lake env lean` from the
   repository root. Among them: every name in the table's proofs, and `IsLocalMin.hasFDerivAt_eq_zero`,
   `hasGradientAt_iff_hasFDerivAt`, `ClassicalLean.Statistics.integral_thresholdTest`,
   `ClassicalLean.Statistics.HasMonotoneLikelihoodRatio`, `ClassicalLean.MinMax.le_eigenvalues_mul_of_mem`,
   `ClassicalLean.Probability.ChiSquared.hasLaw_sum_sq_gaussian`, `Matrix.rank_mul_le_left`, `Matrix.rank_mul_le_right`, `Matrix.trace`,
   `ClassicalLean.Simplex.categoricalCov_mulVec_one`, `LinearMap.IsSymmetric.eigenvalues_antitone`,
   `LinearMap.IsSymmetric.eigenvectorBasis`, `ConvexOn.add`, `HasGradientAt.add`, `gaussianPDFReal`,
   `ProbabilityTheory.gammaMeasure`. A name that is unknown is not used until
   you find what it is called; say so in the report.
5. Records first, one commit, no `.lean` file: this order's text from "# Order CLOUD-MATH-7" to the end as
   `records/orders/<UTC>__claude-ai__order-cloudmath7-hat-rank-categorical-pinv-kkt-multipliers-chi-squared-test-eigenvalue-subgradient.md`;
   its INDEX row at the bottom (`| CLOUD-MATH-7 |`, in CLOUD-MATH-4's row's form); a CLAIMS row at the bottom
   naming this session and the five module paths; round 82's fragment
   `records/rounds/<UTC>__round-82-hat-rank-categorical-pinv-kkt-multipliers-chi-squared-test-eigenvalue-subgradient.md` naming the five
   module files by full path. `records/README.md` rule 2 (the next order appends the previous order's push
   to its INDEX and CLAIMS rows) does not apply here: MERGE-5's push is appended to its rows by MERGE-6 on
   DSMain; do not change those rows. In the same commit, add one more INDEX row, directly above your own,
   for order LEAN-38, which changed nothing in the repository and so has no row yet. Its text is the one
   line inside this block, exactly:
   ```
   | LEAN-38 | Reading order: the pair-by-pair reads of the NEW pairs of MERGE-2's and MERGE-3's bridge searches that were judged only by their shared constants (284 and 169 pairs), with a stop after 40 pairs in a row without a bridge | lane `lean/LEAN-38/order.md` (39e5bafa…; a reading order, not copied to `records/orders/`) | **done** 2026-11-01, no repository change; 223 pairs read (171 and 52); five bridges found, rows 168 to 172 of `MATH-PLAN-library-2-bridges-2.md`, stated and elaborated with `sorry`, ordered proved by order CLOUD-MATH-7 (see its row); report lane `lean/LEAN-38/report.md` (36b021d5…), claude-ai's review `lean/LEAN-38/review-1.md` (aa70054c…) | none |
   ```
   It is the only row of another order you add. Push.

## Rules of this order

1. **Statements first, then one cold review, then proofs.** For each bridge, write its module with every
   statement final and every proof `sorry`, its witnesses complete (a witness proves the hypotheses, not the
   theorem, so it can be finished now), its docstrings and its namespace. Elaborate each with `lake env lean`
   (only `sorry` warnings). Then one cold review of all five (rule 5). Proofs come after its verdict. A
   statement a proof later forces you to change is a narrowing: rule 7.
2. **Namespaces and imports.** Every declaration, private ones included, sits inside its module's namespace
   (the axiom gate checks only constants under `ClassicalLean`). Imports are the table's, targeted; no
   `import Mathlib`, no Mathlib import line the proofs do not need. An `open` line that reaches another
   module's names (`ClassicalLean.Probability.StepDownProcedure`, `ClassicalLean.Probability.StepUpProcedure`,
   `ClassicalLean.Probability.LinearPrediction`, `ClassicalLean.Simplex`, `ClassicalLean.Statistics`,
   `ClassicalLean.Analysis`, `ClassicalLean`, and so on) sits after the imports and before the namespace.
3. **Witnesses** in HANDOFF section 4's form: for each main theorem with a hypothesis, one `example` after the
   module's last line that applies the theorem itself, `example := Full.name (x := …) h₁ h₂ …`, every chosen
   argument by name and every binder before the colon supplied, optional `open … in` lines of their own and
   no other `open` than the module's top-level ones, the docstring "The hypotheses of `name` hold together:
   …" saying what moves, one inline block with no helper declaration, none of `sorry`, `admit`,
   `native_decide`, `implemented_by`, `axiom`, `set_option`, nor `(config :=` or any `reduceBool`-family
   name. No docstring of your modules uses the words `sorry`, `native` or `plausible` either (End check
   3's grep reads docstrings too): say "stated without a proof" for LEAN-38's scratch files. Not degenerate (rule 3 of HANDOFF section 4 and its dated cases: no empty, zero or single-point
   case, no junk value, no boundary where a constant vanishes, families and matrices of size at least 2
   unless the theorem fixes it). A theorem with no hypothesis gets none (HANDOFF: "for a theorem with
   hypotheses"): 170 has none. Models to start from, each to be checked like any witness:
   - 172: `ι = Fin 3`, `p = ![1/2, 1/3, 1/6]`: positive, summing to `1`, not uniform, so `diagonal (1/p)` is not a
     multiple of `1` and the projection `P` matters. Pseudoinverse's witness of `pinv_unique` (line 242) is the
     pattern for a matrix witness (SecondOrder's typed `example` blocks at lines 402 to 431 are not in witness
     form; do not copy their shape).
   - 168: `E = ℝ`, `ι = Fin 2`, `f y = (y − 2) ^ 2 / 2` (gradient `y − 2`), `g 0 y = y − 1` (gradient `1`),
     `g 1 y = −y − 5` (gradient `−1`), Slater point `x₀ = 0`, `xbar = 1`: the constraint `g 0` is active at the
     minimiser and its multiplier is `1`, not `0`; `g 1` is slack. GradientDescent's witness of
     `isMinOn_of_kkt` (line 595) and KKT's of `exists_kkt_of_slater` (line 254) are the patterns.
   - 169: `k = 2` (the theorem fixes only `0 < k`; two draws keep the sum a real sum), `v₀ = ⟨1, _⟩`, `c = 3`.
   - 171: `F = EuclideanSpace ℝ (Fin 2)`, `n = 1`, `m = 2` (a family of two maps, as rule 3 asks),
     `A₀ = diag(1, 0)`, `A 0 = diag(1, −1)`, `A 1 = diag(0, 1)` (as linear maps; `T x = diag(1 + x₀, −x₀ + x₁)`,
     symmetric for every `x`), `η = 1/2`, `G = 2` (for unit `u` with `b = u₁²`, `g = (1 − 2b, b)` and
     `‖g‖² = (1 − 2b)² + b² ≤ 2`), `T = 3`, `z = 0`, and the iterates `x` defined inline by recursion from
     `x 0 = toLp 2 ![3/4, 0]` through `hstep` (a `Nat.rec` inside the example, no helper declaration; `hstep`
     then holds by `rfl`, and `hg` holds for every unit vector, so no eigenvector is computed in Lean). Inside
     the horizon the top eigenvalue is never tied: `T (x 0) = diag(7/4, −3/4)`, `x 1 = (1/4, 0)` with
     `diag(5/4, −1/4)`, `x 2 = (−1/4, 0)` with `diag(3/4, 1/4)`, `x 3 = (−3/4, 0)`; each step uses `u = e₀`,
     `g = (1, 0)`, and moves. The witness's docstring lists these iterates. MinMax's witnesses (from line 484)
     and SubgradientMethod's (line 103) are the patterns. If the recursion cannot be stated inline, say so in
     the report and state `x` in closed form for the steps up to `T`, checked against `hstep`.
4. **Vacuity gate.** A flag or an UNCHECKED verdict on a main theorem makes its bridge not closed. On a
   helper: rewrite it, remove it if Mathlib or `simp` already does its job, or list it in
   `tools/vacuity_reviewed.txt` as HELPER with a one-line reason the cold review checks.
5. **One cold review,** by one fresh subagent that has not seen your work, after rule 1's statement stage:
   give it the five modules as they stand (statements, witnesses, docstrings, helpers' statements), the
   five bridge rows below, HANDOFF section 4's "Satisfiability witnesses" paragraph with its dated cases, and
   the statements of the theorems each bridge rests on, copied from their modules by a script, not retyped.
   It checks each statement against its row (FAITHFUL, GENERALIZED or WEAKER; WEAKER is a finding), that no
   hypothesis is missing or extra, each witness against rule 3 (doing the arithmetic), namespaces and
   imports. Its report goes to `incoming/reviews/review-1.md`. Fix what it finds; a second pass, on the fixes
   only, only if a fix changes a statement or a witness's arguments.
6. **Records.** As `records/README.md` says, including its rule 1's per-module theorem-constant count and its
   statement of which tree each count was measured on. Round 82's fragment names the five module files in
   full, says each bridge was proved by this session (no draft) from the row's sketch, gives each module's
   commit hash in a follow-up edit once it exists (never predicted), and lists every witness and what moves in
   it. Close your CLAIMS row and set your INDEX row's state at the end.
7. **Not closed.** A bridge whose proofs do not build after two hours of work on it (log `date` when you
   start it), or whose statement had to be narrowed in a way its row does not allow, is not closed: its
   module, import line and vacuity entries removed by a new commit, and round 82, the CLAIMS row and the
   report saying which and why. The others go on. A narrowing that keeps the row's meaning (a hypothesis
   the proof needs and the row left implicit) is said plainly in the docstring and the report.
8. **Push often:** after the records commit and after each bridge lands, so nothing is lost if the session
   stops. Each push starts a CI run; an older run on the branch is cancelled, which is fine.
9. **A count is what its output says.** Every count in round 82 and the report is read from a saved output in
   `$HOME/cm7/` and cited by its file name.

## The work, per bridge (in the table's order)

Proofs in place of the `sorry`s; `lake build ClassicalLean.<Area>.<Module>`, 0 errors, 0 warnings;
`python3 -I tools/witness_gate.py <Area>/<Module>.lean` (the path relative to `ClassicalLean/`), every block
OK, `copy-error=0`; then the module's import line added to `ClassicalLean.lean` (only now, so that no pushed
commit imports a module not yet committed), `lake build` of the root (the vacuity gate imports
`ClassicalLean`, and `lake env lean` does not rebuild it), and `lake env lean tools/VacuityGate.lean` (rule
4), its lines for the new theorems quoted in round 82; one commit staged by path (the module, its import line
and, if rule 4 added one, its `tools/vacuity_reviewed.txt` line); push.

## End checks, in this order

1. Before running them, write `$HOME/cm7/expected.txt` with the expected result of each, and its sha256:
   `lake build` (4206 plus the new modules plus any Mathlib module a new import line brings that is
   not already in the closure, counted by a scratch file printing `env.header.moduleNames` before and after,
   0 warnings), AxiomGate (3914 plus each new module's theorem-constant count, measured as
   `records/README.md` rule 1 says: `env.getModuleFor?` under the axiom gate's `.thmInfo` predicate, not a
   name count from the source), check_sorry and check_records (153 plus the modules landed), VacuityGate PASS
   with its reviewed-helper count (Setup 3's plus any HELPER line added), `python3 -I tools/witness_gate.py`
   on the five new modules (OK equal to the witnesses written, `copy-error=0`),
   `python3 tools/compile_rules.py drift records/rules.toml HANDOFF.md` PASS (neither file changes). Then run
   each and save its output.
2. Not run here (they run on DSMain at the merge, MERGE-6): gate 7, the banned-vocabulary scan (its term
   list is kept only on DSMain), the whole-library witness gate, the bridge search and the report tool.
3. `grep -rnwE 'reduceBool|reduceNat|ofReduceBool|ofReduceNat|trustCompiler|native|native_decide|implemented_by|admit|sorry|plausible|slim_check|evalExpr|evalConst'`
   and `grep -rn '(config *:='` on the five new files: nothing. `git diff --name-only d723fbf HEAD`: only the
   five modules, `ClassicalLean.lean`, `records/`, `incoming/` and, if a helper was listed,
   `tools/vacuity_reviewed.txt`.    `git diff d723fbf HEAD -- ClassicalLean.lean`: only the added import lines.
   `git diff --name-status d723fbf HEAD -- records/`: only `A` lines (this order's copy, round 82) and `M`
   for `records/orders/INDEX.md` and `records/CLAIMS.md`. `git diff -U0 d723fbf HEAD -- records/orders/INDEX.md
   records/CLAIMS.md`: only `+` lines, at the end of each file.
4. Records: round 82 completed with the commit hashes and the counts from the saved outputs; CLAIMS closed;
   INDEX set; check_records PASS; push.
5. `incoming/REPORT.md` (and push it): each bridge's final statements, verdict, witnesses and what moves;
   every probe that found a name unknown; the review and its fixes; each end check's expected and observed
   value, cited by file; anything not closed or narrowed; `git ls-remote origin master` at the start and the
   end; the branch's last commit. Then tell Dustin in a few plain sentences what was proved, define any
   technical term the first time, and give the last commit's hash.

## Done means

Branch `cloud-math-7` from `d723fbf`, pushed, with: the records commit; one commit per bridge landed, each
module building with 0 warnings, no `sorry`, no new axiom; every witness OK in the witness gate and passed by
the review; the review in `incoming/reviews/`; every end check as expected or each miss reported; records
closed; `incoming/REPORT.md`. Or a bridge reported not closed under rule 7 and undone. Nothing on `master`.

## After the session (claude-ai)

claude-ai checks the branch against `d723fbf` (files, imports, no existing module changed), reruns the
gates in its own clone, and writes MERGE-6 for DSMain: the merge, then the gates that did not run here
(gate 7, the banned scan, the whole-library witness gate, the bridge search, the report tool), and
HANDOFF's and ROADMAP's entries.

## Not in this order

The skimmed pairs of the later bridge searches (LEAN-39); LEAN-38's pair-by-pair reads; TWINS-1; GATE-2; HANDOFF and
ROADMAP entries (MERGE-5); anything on `master`.

## The bridge rows

(Quoted from `lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md`, a lane file this session cannot
read, rows 170, 172, 168, 169 and 171 in landing order, copied by script; the header row is the file's.)

| # | area | the result | Lean names | module | rests on | cost |
|---|---|---|---|---|---|---|
| 170 | 1, bridge | The hat matrix of any design has rank and trace equal to the design's rank: for every real `m × n` matrix `A`, rank-deficient included, `H = A * pinv A` has `rank H = rank A` and `trace H = rank A`, and the residual maker `1 − H` has rank `m − rank A`, the residual degrees of freedom. `pinv_spec` makes `H` idempotent (`H H = (A X A) X = A X`); `A = H A` and `rank (A X) ≤ rank A` give `rank H = rank A`; `rank_eq_trace_of_isIdempotentElem` gives the trace; `H + (1 − H) = 1` with both idempotent gives, by `sum_rank_eq_iff`, `rank H + rank (1 − H) = m`. `rank_mul_leastSquares` (Cochran's module) is the full-column-rank case, through `pinv_eq_leastSquares`; the any-design case is not a generalisation needing a new proof (the bridges files' exclusion), since it composes the four named results above. Shared object: the hat matrix, as a Moore–Penrose product and as an idempotent of Cochran's theorem. Found by order LEAN-38's pair-by-pair read of MERGE-2's search: `merge2-unread.tsv` order 27, score 17.0 (`Algebra.Pseudoinverse × Statistics.Cochran`); checked by reading both statements and elaborating the statement with `sorry` (`~/lean/lean38-checks/b170.lean`, rc 0, only the `sorry` warning), not proved. Not load-bearing for any scheduled row (none is scheduled). | `rank_mul_pinv_eq` (proposed) | a new module importing Algebra.Pseudoinverse and Statistics.Cochran | item 150 (`pinv`, `pinv_spec`), library `rank_eq_trace_of_isIdempotentElem`, `sum_rank_eq_iff`; Mathlib `Matrix.rank_mul_le_left` | S |
| 172 | 1, bridge | The pseudoinverse of a categorical covariance is the Fisher–Rao form on the tangent space: for a strictly positive probability vector `p` on `n` points and `P = 1 − (1/n) 1 1ᵀ`, `pinv (categoricalCov p) = P * diagonal (1/p) * P` and `categoricalCov p * pinv (categoricalCov p) = P`. With `C = diagonal p − p pᵀ` and `X = P D⁻¹ P`: `C 1 = 0` (`categoricalCov_mulVec_one`) gives `C P = P C = C`; `C D⁻¹ C = (1 − p 1ᵀ) C = C` and `X C X = P (D⁻¹ − 1 1ᵀ) P = X`, since `1ᵀ D = pᵀ`, `1ᵀ p = 1` and `P 1 = 0`; `C X = P` and `X C = P` are symmetric; so `pinv_unique` applies. For tangent vectors `u`, `v` (sums `0`, so `P u = u`), `u ⬝ᵥ (pinv C *ᵥ v) = ∑ u i v i / p i`, the Fisher–Rao form (`fisherRao_categoricalCov_mulVec` is the same fact read the other way). `Simplex.SecondOrder` states the inverse only in a two-coordinate chart (`fisherRaoChart_mul_categoricalCov`). Shared object: the covariance of a one-hot draw, singular because its rows sum to `0`. Found by order LEAN-38's pair-by-pair read of MERGE-2's search, in the reading the cold check reopened: `merge2-unread.tsv` order 131, score 5.7 (`Algebra.Pseudoinverse × Simplex.SecondOrder`); checked by reading both statements, the four Penrose equations worked by hand, and elaborating the statement with `sorry` (`~/lean/lean38-checks/b172.lean`, rc 0, only the `sorry` warning), not proved. Not load-bearing for any scheduled row (none is scheduled). | `pinv_categoricalCov` (proposed) | a new module importing Algebra.Pseudoinverse and Simplex.SecondOrder | item 150 (`pinv_unique`), library `categoricalCov`, `categoricalCov_apply`, `categoricalCov_mulVec_one`, `fisherRao_categoricalCov_mulVec` | S |
| 168 | 7, bridge | One multiplier vector serves every minimiser: for a convex problem on a real Hilbert space (minimise `f x` subject to `g i x ≤ 0`, `f` and every `g i` convex with gradients `f' x`, `g' i x` everywhere) with a Slater point and a feasible minimiser `xbar`, there is `w ≥ 0` such that, for every `y`, `y` is a feasible minimiser exactly when `y` is feasible, `w i * g i y = 0` for every `i`, and `f' y + ∑ i, w i • g' i y = 0`. `exists_kkt_of_slater` gives `w` at `xbar`; then the Lagrangian `f + ∑ i, w i * g i` is convex with gradient `0` at `xbar`, so by `add_inner_gradient_le` it is at least `f xbar` everywhere; at a feasible minimiser `y` (`f y = f xbar`) this forces `∑ i, w i * g i y ≥ 0` with every term `≤ 0`, so each is `0`, `y` minimises the Lagrangian, and its gradient vanishes (`IsLocalMin.hasFDerivAt_eq_zero`); `isMinOn_of_kkt` gives the converse. Shared object: the convex program's KKT conditions, necessary in `Analysis.KKT`, sufficient in `Analysis.GradientDescent`. Found by order LEAN-38's pair-by-pair read of MERGE-2's search: `merge2-unread.tsv` order 1, score 73.0 (`Analysis.GradientDescent × Analysis.KKT`); checked by reading both statements and elaborating the statement with `sorry` (`~/lean/lean38-checks/b168.lean`, rc 0, only the `sorry` warning), not proved. Not load-bearing for any scheduled row (none is scheduled). | `exists_multipliers_isMinOn_iff` (proposed) | a new module importing Analysis.GradientDescent and Analysis.KKT | library `exists_kkt_of_slater`, `isMinOn_of_kkt`, `add_inner_gradient_le`; Mathlib `IsLocalMin.hasFDerivAt_eq_zero`, `hasGradientAt_iff_hasFDerivAt` | S |
| 169 | 2, bridge | The chi-squared test of a normal variance is uniformly most powerful: for `k ≥ 1` independent `N(0, v)` draws (density `∏ i, gaussianPDFReal 0 v (x i)` against Lebesgue measure on `Fin k → ℝ`, `v > 0`) and every `c`, the test rejecting when `∑ i, x i ^ 2 > c` is uniformly most powerful for `v ≤ v₀` against `v > v₀` at level `α = P(χ²ₖ > c / v₀)`, the chi-squared law being `gammaMeasure (k/2) (1/2)`. The density ratio `f v' / f v = (v/v')^(k/2) exp(S (1/v − 1/v')/2)` is a nondecreasing function of `S = ∑ x i ^ 2` for `v < v'` (`HasMonotoneLikelihoodRatio`), so Karlin–Rubin (`isUniformlyMostPowerful_of_monotoneLikelihoodRatio`, `γ = 0`) makes the threshold test UMP at its size under `v₀`; that size is `P_{v₀}(S > c)` (`integral_thresholdTest`), and `hasLaw_sum_sq_gaussian` at `x i / √v₀` gives `S / v₀` the law `gammaMeasure (k/2) (1/2)`. Shared object: the sum of squares of normal draws, the sufficient statistic of the test and the chi-squared variable. Found by order LEAN-38's pair-by-pair read of MERGE-2's search: `merge2-unread.tsv` order 15, score 26.0 (`Probability.ChiSquared × Statistics.NeymanPearson`); checked by reading both statements and elaborating the statement with `sorry` (`~/lean/lean38-checks/b169.lean`, rc 0, only the `sorry` warning), not proved. Not load-bearing for any scheduled row (none is scheduled). | `isUniformlyMostPowerful_sum_sq_gaussian` (proposed) | a new module importing Probability.ChiSquared and Statistics.NeymanPearson | item 151 (`hasLaw_sum_sq_gaussian`), library `isUniformlyMostPowerful_of_monotoneLikelihoodRatio`, `thresholdTest`, `integral_thresholdTest`; Mathlib `gaussianPDFReal`, `integral_gaussianPDFReal_eq_one`, `gammaMeasure` | M |
| 171 | 7, bridge | Minimising the largest eigenvalue by the subgradient method: for symmetric maps `A₀, A 0, …, A (m − 1)` of a real inner product space of dimension `n + 1` and `f x = λ₀(A₀ + ∑ i, x i • A i)` on `EuclideanSpace ℝ (Fin m)`, the vector `g x = (⟪A i u, u⟫)ᵢ`, `u` the unit eigenvector of `λ₀` (Mathlib's `eigenvectorBasis` at index `0`), is a subgradient of `f` at `x`, so the iterates `x (k + 1) = x k − η g (x k)` with `‖g‖ ≤ G` satisfy `min_{k < T} f (x k) − f z ≤ (‖x 0 − z‖² + η² G² T)/(2 η T)` for every `z`. Courant–Fischer's bound `re ⟪T y u, u⟫ ≤ λ₀(T y) ‖u‖²` (`le_eigenvalues_mul_of_mem` at `k = 0`, whose span is the whole space) and `T x u = λ₀(T x) u` give `f y ≥ ⟪T y u, u⟫ = f x + ⟪g x, y − x⟫`, the hypothesis `hsub` of `min_sub_le_of_subgradient`. Shared object: the largest eigenvalue as a convex, nonsmooth function of the matrix. Found by order LEAN-38's pair-by-pair read of MERGE-3's search: `merge3-unread.tsv` order 12, score 8.6 (`Algebra.MinMax × Analysis.SubgradientMethod`); checked by reading both statements and elaborating the statement with `sorry` (`~/lean/lean38-checks/b171.lean`, rc 0, only the `sorry` warning), not proved. Not load-bearing for any scheduled row (none is scheduled). | `min_sub_le_of_subgradient_eigenvalues` (proposed) | a new module importing Algebra.MinMax and Analysis.SubgradientMethod | item 113 (`min_sub_le_of_subgradient`), library `le_eigenvalues_mul_of_mem`; Mathlib `LinearMap.IsSymmetric.apply_eigenvectorBasis`, `eigenvalues_antitone` | S |
