<!-- The order's text, as given in the prompt of Claude Code cloud session session_01HgueTYMESHnLVKHDy4XkAM (https://claude.ai/code/session_01HgueTYMESHnLVKHDy4XkAM), copied on 2026-10-30 (UTC) by that session before any Lean file changed, per records/README.md rule 2. Its file name gives claude-ai as the source, as the order's own Setup step 5 names it. -->

# Order CLOUD-MATH-5: five bridges as five new modules

## Goal

Prove five results that join two existing modules each, and land each as a new module on branch
`cloud-math-5`, under the library's gates, with witnesses, one cold review and records. Nothing here is
drafted: you write the statements in Lean from the descriptions below, have them reviewed, then prove them.
The rows are in landing order, cheapest first. Each row's text in the bridges file is quoted under "The
bridge rows" at the end.

| bridge | the result | new module (namespace = module name) | imports | main theorems (names to keep) |
|---|---|---|---|---|
| 158 | Holm's rejections lie inside Benjamini and Hochberg's at the same level. For `[Fintype ι]`, `q ≥ 0`, `x : ι → ℝ` and `i : ι` with `holmRejected q x i`: `x i ≤ q * numRej q x / Fintype.card ι`, so the step-up procedure rejects `i` too (its rejections are the `i` with `x i ≤ q · numRej q x / m`). Proof (the row's): with `k` the number of `j` with `x j ≤ x i` (that is `countLE x (x i)`), `1 ≤ k ≤ m`; each such `x j` is at most `q / c_j` with `c_j ≥ m − k + 1`, and `k (m − k + 1) ≥ m`, so `x j ≤ q k / m`; so `k ≤ countLE x (q k / m)`, `le_numRej` gives `k ≤ numRej q x`, and `x i ≤ q k / m ≤ q · numRej q x / m` by `thr_mono`. Ties are covered by the definitions. | `ClassicalLean.Probability.HolmInsideStepUp` | `ClassicalLean.Probability.StepDownProcedure`, `ClassicalLean.Probability.StepUpProcedure` | `le_mul_numRej_div_of_holmRejected` |
| 155 | The covariance's Cauchy–Schwarz inequality, and the correlation in `[−1, 1]`. On a probability space (`[IsProbabilityMeasure μ]`, as the row says; do not widen it to a finite measure), for `X Y : Ω → ℝ` with `MemLp X 2 μ` and `MemLp Y 2 μ`: `cov[X, Y; μ] ^ 2 ≤ variance X μ * variance Y μ`; and `|ClassicalLean.Probability.LinearPrediction.correlation X Y μ| ≤ 1` (the full name, or the short one after an `open` line) (when the root is `0`, Lean's `x / 0 = 0` gives `0`). Proof: `Var[t X + Y] ≥ 0` for every `t` is the quadratic `Var X · t² + 2 cov · t + Var Y ≥ 0`, and `discrim_le_zero` gives the first, exactly as inside the proof of `abs_covariance_le_mul_div_four` (Gruss line 103; copy that step, do not change Gruss); the second follows by taking square roots. | `ClassicalLean.Probability.CorrelationBound` | `ClassicalLean.Analysis.Gruss`, `ClassicalLean.Probability.LinearPrediction` | `covariance_sq_le_variance_mul`, `abs_correlation_le_one` |
| 164 | A Pinsker bound for tests. With exactly the binders and hypotheses of `size_add_one_sub_power_ge` (`[Fintype ι] [MeasurableSpace ι]`, `p₀ p₁ φ : ι → ℝ`, `hp₀ hp₀1 hp₁ hp₁1`, `hsupp : ∀ i, p₀ i = 0 → p₁ i = 0`, `hφ : IsTest φ`): `1 - Real.sqrt (relEntropy p₁ p₀ / 2) ≤ ∑ i, φ i * p₀ i + (1 - ∑ i, φ i * p₁ i)`. Proof: size plus missed detection is `1 − ∑ φ i (p₁ i − p₀ i) ≥ 1 − ∑_{p₁ > p₀} (p₁ i − p₀ i) = 1 − ½ ∑ |p₁ i − p₀ i|` (both sums are `1`), and `sq_sum_abs_sub_le_two_mul_relEntropy` at `p = p₁`, `q = p₀` (its `hpq` is `hsupp`) bounds the half-sum by `√(D/2)`. The companion of item 144's Bretagnolle–Huber bound; state no comparison of the two. | `ClassicalLean.Statistics.PinskerTest` | `ClassicalLean.Statistics.NeymanPearson`, `ClassicalLean.InformationTheory.Channel` | `size_add_one_sub_power_ge_pinsker` |
| 166 | Richardson extrapolation of Heun's method is Simpson's rule, for `y' = g(t)`. Below, `heun g a h y₀ n` is prose shorthand for `heunIterate (fun t _ ↦ g t) a h y₀ n` only: the statements write `heunIterate (fun t _ ↦ g t) …` in full, and the module adds no definition or notation for it. **Theorem 1**, every `N`, no hypothesis: `heunIterate (fun t _ ↦ g t) a ((b - a) / N) y₀ N = y₀ + trapezoidal_integral g N a b` (each step adds `h/2 (g (a + k h) + g (a + k h + h))`; at `N = 0` both sides are `y₀`, since `(b − a)/0 = 0`). **Theorem 2**, every `N`: `(4 * heun g a ((b - a) / (2 * (N : ℝ))) y₀ (2 * N) - heun g a ((b - a) / N) y₀ N) / 3 = y₀ + simpson g N a b`, the `2N` run's step written `(b - a) / (2 * (N : ℝ))` (simpson's step and the one in `simpson_error_le`'s bound; `push_cast` turns theorem 1's `(b - a) / ↑(2 * N)` into it), by theorem 1 twice and `simpson_eq_trapezoidal`. **Theorem 3** (your name), with `simpson_error_le`'s hypotheses on `g` (`hab`, `0 < N`, `hf hf₁ hf₂ hf₃`, `hM`): the extrapolated value of theorem 2 is within `(b - a) * ((b - a) / (2 * N)) ^ 4 * M / 180` of `y₀ + ∫ x in a..b, g x`. The row says "of `y b`"; for `y' = g` with `y a = y₀` that is `y₀ + ∫ₐᵇ g`, so state it with the integral, no solution `y` in the statement, and say so in the docstring. | `ClassicalLean.Analysis.HeunRichardson` | `ClassicalLean.Analysis.EulerMethod`, `ClassicalLean.Analysis.Simpson` | `heunIterate_add_eq_trapezoidal`, `richardson_heunIterate_eq_simpson`, and theorem 3 (your name) |
| 167 | The exact global error of Heun's method at unit steps, for `y' = g(t)`. **Theorem 1** (your name), for integers `a ≤ b`: `heunIterate (fun t _ ↦ g t) (a : ℝ) 1 y₀ (b - a).toNat = y₀ + ∑ k ∈ Finset.Icc a b, g k - (g a + g b) / 2` (induction on the number of steps). **Theorem 2**, with `sum_eq_integral_add_two`'s hypotheses on `g` (`hab hf hf' hf'c hf'' hint`, there named `f f' f''`): `(y₀ + ∫ t in (a : ℝ)..b, g t) - heunIterate (fun t _ ↦ g t) (a : ℝ) 1 y₀ (b - a).toNat = -(g' b - g' a) / 12 + ∫ t in (a : ℝ)..b, bernoulliFun 2 (Int.fract t) / 2 * g'' t`, by theorem 1 and `sum_eq_integral_add_two`. As in 166, `y b` of the row is `y₀ + ∫ₐᵇ g`; say so in the docstring. Only unit steps: the library's Euler–Maclaurin is stated on integer nodes. | `ClassicalLean.Analysis.HeunEulerMaclaurin` | `ClassicalLean.Analysis.EulerMethod`, `ClassicalLean.Analysis.EulerMaclaurin` | theorem 1 (your name), `sub_heunIterate_eq_eulerMaclaurin` |

The statement you write must say what its row says; where Lean makes you choose (an index set, a cast, the
form of a step size), choose the form closest to the row and to the theorems it rests on, and say what you
chose in the docstring. Hypotheses are what the proof needs and no more.

## Branch rules (hard)

These override any branch this session was assigned; do not push an assigned `claude/*` branch.
- Work only on `cloud-math-5`. First confirm `origin/cloud-math-5` is `8631a8d3c4316d85c78df697436b0245fa24cf1b`
  and note `git ls-remote origin master` (you report it again at the end). If the branch is missing or
  differs, stop and report.
- Push only with `git push origin cloud-math-5`. Never push `master` or `main`, never force-push, never reset
  a pushed commit, open no pull request, merge nothing on GitHub. Every undo is a new commit.

## Scope

You may: add the five module files under `ClassicalLean/`; add their five import lines at the end of the
import block of `ClassicalLean.lean`; add HELPER lines to `tools/vacuity_reviewed.txt` (rule 4); write
`records/` (rule 6); add `incoming/REPORT.md` and `incoming/reviews/`.
You may not change any existing module (Gruss, StepUpProcedure and the rest stay as they are, even where a
lemma you need is private there: copy the step into your module), any other file under `tools/`,
`HANDOFF.md`, `ROADMAP.md`, `records/rules.toml`, the lake files, `lean-toolchain` or `.github/`; nor any
existing row of `records/orders/INDEX.md` or `records/CLAIMS.md`. Needing to is a stop: report it.

## Read first (in the repository)

`records/README.md`; `HANDOFF.md` sections 0, 4 (the gates, "Satisfiability witnesses" with its dated
cases) and 5 (naming); the ten modules named in the table, at least their docstrings and the statements
listed; NeymanPearson's witness of `size_add_one_sub_power_ge` and PrincipalComponents' witnesses (the
patterns for 164's and 155's); CLOUD-MATH-4's order copy under `records/orders/`, its INDEX and CLAIMS rows
and round 77, as the pattern for your records.

## Setup

1. Network: `curl -sSI https://cache.mathlib.org/ | head -3`, for the report only. A connection error, or a
   403 whose body or headers name the session's proxy, is a stop: report the output and do not build Mathlib
   from source. A 403 or 404 from the cache server itself is not a stop; Setup 2's `lake exe cache get` is
   the test.
2. Install the toolchain from `lean-toolchain` (elan, from GitHub) and run `lake exe cache get`. A refused
   download is a stop.
3. Starting gates, before any new file exists: `lake build` (predicted 4196 jobs, 0 warnings; run it in the
   background if it may pass a 10-minute limit; if the VM kills it for memory, retry once with
   `LEAN_NUM_THREADS=2 lake build`, then stop), `lake env lean tools/AxiomGate.lean` (PASS 3844),
   `python3 -I tools/check_sorry.py` and `python3 -I tools/check_records.py` (PASS 143), and
   `lake env lean tools/VacuityGate.lean` (PASS, 1 reviewed helper). Save every output in `$HOME/cm5/` with
   its sha256. A different value is a stop.
4. Probe every name the order cites, and every other name you will use, with `#check @Name` lines in one
   scratch file per new module, in `$HOME/cm5/` (never under `ClassicalLean/`, where check_sorry and
   check_records would read it), that imports exactly that module's imports, run with `lake env lean` from the
   repository root. Among them: `discrim_le_zero`, `variance_add`, `variance_smul`, `covariance_smul_left`,
   `trapezoidal_integral`, `bernoulliFun`, `ClassicalLean.Probability.StepUpProcedure.le_numRej`,
   `ClassicalLean.Probability.StepUpProcedure.thr_mono`, `ClassicalLean.Simplex.sq_sum_abs_sub_le_two_mul_relEntropy`,
   `ClassicalLean.Statistics.IsTest`, `ClassicalLean.Analysis.heunIterate`, `ClassicalLean.simpson`,
   `ClassicalLean.simpson_eq_trapezoidal`, `ClassicalLean.simpson_error_le`,
   `ClassicalLean.sum_eq_integral_add_two`; and for 155's witness, whether
   `IsProbabilityMeasure ((4⁻¹ : ℝ≥0) • Measure.count : Measure (Fin 2 → Bool))` is found as an instance (if
   not, the witness supplies it as a named argument, proved inline). A name that is unknown is not used until
   you find what it is called; say so in the report.
5. Records first, one commit, no `.lean` file: this order's text from "# Order CLOUD-MATH-5" to the end as
   `records/orders/<UTC>__claude-ai__order-cloudmath5-holm-correlation-pinsker-heun-richardson-euler-maclaurin.md`;
   its INDEX row at the bottom (`| CLOUD-MATH-5 |`, in CLOUD-MATH-4's row's form); a CLAIMS row at the bottom
   naming this session and the five module paths; round 79's fragment
   `records/rounds/<UTC>__round-79-holm-correlation-pinsker-heun-richardson-euler-maclaurin.md` naming the five
   module files by full path. `records/README.md` rule 2 (the next order appends the previous order's push
   to its INDEX and CLAIMS rows) does not apply here: MERGE-4's push is appended to its rows by MERGE-5 on
   DSMain; do not change those rows. Push.

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
   name. Not degenerate (rule 3 of HANDOFF section 4 and its dated cases: no empty, zero or single-point
   case, no junk value, no boundary where a constant vanishes, families and matrices of size at least 2
   unless the theorem fixes it). A theorem with no hypothesis gets none (HANDOFF: "for a theorem with
   hypotheses"): 166's theorems 1 and 2 have none. Models to start from, each to be checked like any witness:
   - 158: `ι = Fin 3`, `x = ![1/100, 1/50, 9/10]`, `q = 1/10`, `i = 1`. Holm rejects `i = 1`, which is not the
     smallest p-value, so both of Holm's steps are used: `j = 0` needs `1/100 ≤ (1/10)/3`, `j = 1` needs
     `1/50 ≤ (1/10)/2`; `x 2` is not at most `x 1`. Then `numRej = 2` (`2 ≤ countLE x (2/30)`, but
     `3 > countLE x (3/30) = 2`), and the conclusion `1/50 ≤ 2/30` is strict. The cards are computed by
     `Finset.card_filter` and `Fin.sum_univ_three`, not by `decide`.
   - 155, both theorems: `Ω = Fin 2 → Bool`, `μ = (4⁻¹ : ℝ≥0) • Measure.count`, `X ω = if ω 0 then 1 else -1`,
     `Y ω = X ω + (if ω 1 then 1 else -1)`: `cov[X, Y] = 1`, `Var X = 1`, `Var Y = 2`, so `1 < 2` and the
     correlation `1/√2` lies strictly inside `(−1, 1)`. Neither variable is constant and they are neither
     independent nor proportional.
   - 164: NeymanPearson's model for `size_add_one_sub_power_ge` (`ι = Fin 3`, `p₀ = ![1/2, 1/2, 0]`,
     `p₁ = ![1/4, 3/4, 0]`, `φ = ![0, 1, 0]`): the laws differ, so `D > 0`, the test is not constant, and the
     third cell exercises `hsupp`.
   - 166, theorem 3: `g x = x ^ 4` on `[0, 1]`, `N = 2` (both runs take at least 2 steps, Simpson two panel
     pairs), derivatives `4 x ^ 3`, `12 x ^ 2`, `24 x`, `24`, `M = 24`: the fourth derivative is not `0`, so
     Simpson's rule is not exact and the bound `(1/4) ^ 4 * 24 / 180` is positive.
   - 167, theorem 1: `a = 0`, `b = 3`, `g x = x ^ 2`, `y₀ = 1`: three steps, and the iterate moves at each
     (increments `1/2`, `5/2`, `13/2`). Theorem 2: `g x = x ^ 4` on `[0, 2]`, `g' x = 4 x ^ 3`,
     `g'' x = 12 x ^ 2`: `g''` is not linear, so the remainder `∫ B₂(fract t)/2 · g''` is not `0` (it is
     `1/30` on each unit interval, `1/15` in all). A cubic would make it `0` (`∫₀¹ B₂ = ∫₀¹ s B₂(s) ds = 0`),
     as EulerMaclaurin's own witness notes.
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
   statement of which tree each count was measured on. Round 79's fragment names the five module files in
   full, says each bridge was proved by this session (no draft) from the row's sketch, gives each module's
   commit hash in a follow-up edit once it exists (never predicted), and lists every witness and what moves in
   it. Close your CLAIMS row and set your INDEX row's state at the end.
7. **Not closed.** A bridge whose proofs do not build after two hours of work on it (log `date` when you
   start it), or whose statement had to be narrowed in a way its row does not allow, is not closed: its
   module, import line and vacuity entries removed by a new commit, and round 79, the CLAIMS row and the
   report saying which and why. The others go on. A narrowing that keeps the row's meaning (a hypothesis
   the proof needs and the row left implicit) is said plainly in the docstring and the report.
8. **Push often:** after the records commit and after each bridge lands, so nothing is lost if the session
   stops. Each push starts a CI run; an older run on the branch is cancelled, which is fine.
9. **A count is what its output says.** Every count in round 79 and the report is read from a saved output in
   `$HOME/cm5/` and cited by its file name.

## The work, per bridge (in the table's order)

Proofs in place of the `sorry`s; `lake build ClassicalLean.<Area>.<Module>`, 0 errors, 0 warnings;
`python3 -I tools/witness_gate.py <Area>/<Module>.lean` (the path relative to `ClassicalLean/`), every block
OK, `copy-error=0`; then the module's import line added to `ClassicalLean.lean` (only now, so that no pushed
commit imports a module not yet committed), `lake build` of the root (the vacuity gate imports
`ClassicalLean`, and `lake env lean` does not rebuild it), and `lake env lean tools/VacuityGate.lean` (rule
4), its lines for the new theorems quoted in round 79; one commit staged by path (the module, its import line
and, if rule 4 added one, its `tools/vacuity_reviewed.txt` line); push.

## End checks, in this order

1. Before running them, write `$HOME/cm5/expected.txt` with the expected result of each, and its sha256:
   `lake build` (4196 plus the new modules plus any Mathlib module a new import line brings that is
   not already in the closure, counted by a scratch file printing `env.header.moduleNames` before and after,
   0 warnings), AxiomGate (3844 plus each new module's theorem-constant count, measured as
   `records/README.md` rule 1 says: `env.getModuleFor?` under the axiom gate's `.thmInfo` predicate, not a
   name count from the source), check_sorry and check_records (143 plus the modules landed), VacuityGate PASS
   with its reviewed-helper count (Setup 3's plus any HELPER line added), `python3 -I tools/witness_gate.py`
   on the five new modules (OK equal to the witnesses written, `copy-error=0`),
   `python3 tools/compile_rules.py drift records/rules.toml HANDOFF.md` PASS (neither file changes). Then run
   each and save its output.
2. Not run here (they run on DSMain at the merge, MERGE-5): gate 7, the banned-vocabulary scan (its term
   list is kept only on DSMain), the whole-library witness gate, the bridge search and the report tool.
3. `grep -rnwE 'reduceBool|reduceNat|ofReduceBool|ofReduceNat|trustCompiler|native|native_decide|implemented_by|admit|sorry|plausible|slim_check|evalExpr|evalConst'`
   and `grep -rn '(config *:='` on the five new files: nothing. `git diff --name-only 8631a8d HEAD`: only the
   five modules, `ClassicalLean.lean`, `records/`, `incoming/` and, if a helper was listed,
   `tools/vacuity_reviewed.txt`. `git diff 8631a8d HEAD -- ClassicalLean.lean`: only the added import lines.
   `git diff --name-status 8631a8d HEAD -- records/`: only `A` lines (this order's copy, round 79) and `M`
   for `records/orders/INDEX.md` and `records/CLAIMS.md`. `git diff -U0 8631a8d HEAD -- records/orders/INDEX.md
   records/CLAIMS.md`: only `+` lines, at the end of each file.
4. Records: round 79 completed with the commit hashes and the counts from the saved outputs; CLAIMS closed;
   INDEX set; check_records PASS; push.
5. `incoming/REPORT.md` (and push it): each bridge's final statements, verdict, witnesses and what moves;
   every probe that found a name unknown; the review and its fixes; each end check's expected and observed
   value, cited by file; anything not closed or narrowed; `git ls-remote origin master` at the start and the
   end; the branch's last commit. Then tell Dustin in a few plain sentences what was proved, define any
   technical term the first time, and give the last commit's hash.

## Done means

Branch `cloud-math-5` from `8631a8d`, pushed, with: the records commit; one commit per bridge landed, each
module building with 0 warnings, no `sorry`, no new axiom; every witness OK in the witness gate and passed by
the review; the review in `incoming/reviews/`; every end check as expected or each miss reported; records
closed; `incoming/REPORT.md`. Or a bridge reported not closed under rule 7 and undone. Nothing on `master`.

## After the session (claude-ai)

claude-ai checks the branch against `8631a8d` (files, imports, no existing module changed), reruns the
gates in its own clone, and writes MERGE-5 for DSMain: the merge, then the gates that did not run here
(gate 7, the banned scan, the whole-library witness gate, the bridge search, the report tool), and
HANDOFF's and ROADMAP's entries.

## Not in this order

Bridges 154, 156, 157, 159 and 165 (CLOUD-MATH-6); LEAN-38's pair-by-pair reads; TWINS-1; GATE-2; HANDOFF and
ROADMAP entries (MERGE-5); anything on `master`.

## The bridge rows

(Quoted from `lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md`, a lane file this session cannot
read, rows 155, 158, 164, 166 and 167, copied by script; the header row is the file's.)

| # | area | the result | Lean names | module | rests on | cost |
|---|---|---|---|---|---|---|
| 155 | 10, bridge | The covariance's Cauchy–Schwarz inequality as a theorem: for `X`, `Y` in `L²` on a probability space, `cov[X, Y]² ≤ Var X · Var Y`, and so the library's `correlation X Y μ = cov[X, Y] / √(Var X · Var Y)` lies in `[−1, 1]` (when the root is `0`, Lean's `x / 0 = 0` gives `0`). Shared object: the quadratic `t ↦ Var(t X + Y) ≥ 0`. `Analysis.Gruss` proves the inequality as a step inside `abs_covariance_le_mul_div_four` (its discriminant), and `Probability.LinearPrediction`'s `variance_sub_mul_eq` makes the leftover `Var Y − Cov² / Var X` a variance, so never negative: the same inequality at `Var X > 0`. The two modules do not import each other. Found as the new shape key `covariance: Analysis.Gruss × Probability.LinearPrediction` (import-unrelated), also a new pair sharing `ProbabilityTheory.covariance`; checked by reading both modules, not elaborated. Not load-bearing for items 96 to 110 (item 96 bounds the determinant of a covariance matrix by Hadamard's inequality, not by this), so the cut is not re-drawn. | `covariance_sq_le_variance_mul`, `abs_correlation_le_one` | ClassicalLean.Analysis.Gruss (the first); ClassicalLean.Probability.LinearPrediction, importing Analysis.Gruss (the second) | Mathlib `discrim_le_zero`, `variance_add`, `variance_smul`, `covariance_smul_left`; library `correlation` | S |
| 158 | 2, bridge | Holm's rejections lie inside Benjamini and Hochberg's at the same level: for `q ≥ 0`, if Holm's step-down procedure rejects hypothesis `i` (`holmRejected q x i`), then `x i ≤ q · numRej q x / m`, so the step-up procedure rejects it too. With `k` the number of p-values at most `x i`, every such `x j` is at most `q / c_j`, where `c_j ≥ m − k + 1` counts the p-values at least `x j`, and `k (m − k + 1) ≥ m` for `1 ≤ k ≤ m`, so `x j ≤ q k / m`; hence at least `k` p-values are at most `q k / m`, `numRej q x ≥ k` and `x i ≤ q k / m ≤ q · numRej q x / m`. Ties are covered (the library's definitions count them). Shared object: the p-value counts `countLE` and the step thresholds. Not found by the search: `StepDownProcedure` shares no kept constant with any module, so no pair of it appears; the order named the pair, and it was checked by hand and by an exact check (order LEAN-31's `bridges/check158.py`, line `B158.subset`: 143010 cases, m up to 4 over `{0, 1/8, …, 1}`, `q` in `{0, 1/10, 1/4, 1/2, 1}`, 29741 Holm rejections, none outside), not elaborated. Not load-bearing for items 106 to 110 (item 106 gives valid p-values to both procedures but needs neither inclusion), so the cut is not re-drawn. | `le_mul_numRej_div_of_holmRejected` | ClassicalLean.Probability.StepDownProcedure, importing Probability.StepUpProcedure | library `holmRejected`, `numRej`, `le_numRej`, `countLE`, `countLE_mono` | S |
| 164 | 10, bridge | A Pinsker bound for tests: on a finite set, for probability vectors `p₀` (null) and `p₁` (alternative) with `p₁ i = 0` wherever `p₀ i = 0`, every test `φ` has size plus missed-detection chance at least `1 − √(D(p₁ ‖ p₀)/2)`. Size plus missed detection is `1 − ∑ φ i (p₁ i − p₀ i) ≥ 1 − ∑_{p₁ > p₀} (p₁ i − p₀ i) = 1 − ½ ∑ |p₁ i − p₀ i|` (the sums of `p₀` and `p₁` are both `1`), and Pinsker's inequality in the library's form, `(∑ |p − q|)² ≤ 2 D(p ‖ q)` (`sq_sum_abs_sub_le_two_mul_relEntropy` at `p = p₁`, `q = p₀`), bounds the half-sum by `√(D/2)`. The companion of item 144's Bretagnolle–Huber bound `exp(−D)/2`: the Pinsker bound is the stronger one for small `D`, Bretagnolle–Huber for large `D`. Shared object: the relative entropy of the two hypotheses, inside the testing bound and inside Pinsker's inequality. Found as the new shape key `relative entropy: InformationTheory.Channel × Statistics.NeymanPearson` (import-unrelated: neither imports the other); checked by reading both statements, not elaborated. Not load-bearing for any scheduled row. | `size_add_one_sub_power_ge_pinsker` (proposed) | ClassicalLean.Statistics.NeymanPearson, importing InformationTheory.Channel (or a new module importing both) | item 144's setting (`IsTest`), library `sq_sum_abs_sub_le_two_mul_relEntropy` (`InformationTheory/Channel`) | S |
| 166 | 4, bridge | Richardson extrapolation of Heun's method is Simpson's rule: for an equation `y' = g(t)` whose right side does not depend on `y`, Heun's method from `(a, y₀)` with `N ≥ 1` steps of `h = (b − a)/N` gives `u_N = y₀ + T_N`, `T_N` Mathlib's `trapezoidal_integral g N a b` (each step adds `h/2 (g(t_k) + g(t_k + h))`, and the sum of these is the composite trapezoid), so `(4 u'_{2N} − u_N)/3 = y₀ + simpson g N a b`, `u'` the run with `2N` steps of `h/2`, by Simpson's `simpson_eq_trapezoidal` (`simpson g N a b = (4 T_{2N} − T_N)/3`). With `simpson_error_le`, for `y₀ = y a` and `|g⁗| ≤ M` on `[a, b]`, the extrapolated value is within `(b − a) (h/2)⁴ M/180` of `y b`, against Heun's `h²` bound. Shared object: the composite trapezoidal rule, inside Heun's method and inside Richardson's identity. Found as the new pair `Analysis.EulerMethod x Analysis.Simpson` (import-unrelated; score 24.9, the highest new pair, sharing eight derivative and convexity lemmas); checked by reading both statements and `heunIterate`'s definition against Mathlib's `trapezoidal_integral` (`MeasureTheory/Integral/IntervalIntegral/TrapezoidalRule.lean`, line 41), the identity worked by hand, not elaborated. Not load-bearing for any scheduled row. | `heunIterate_add_eq_trapezoidal`, `richardson_heunIterate_eq_simpson` (proposed) | a new module importing Analysis.EulerMethod and Analysis.Simpson | item 146 (`heunIterate`), library `simpson_eq_trapezoidal`, Mathlib `trapezoidal_integral` | S |
| 167 | 4, bridge | The exact global error of Heun's method at unit steps, for `y' = g(t)`: from an integer start `a` with `h = 1`, after `b − a` steps (`b ≥ a` an integer), `u_{b−a} = y(a) + ∑_{k=a}^{b} g k − (g a + g b)/2`, so item 128 gives `y(b) − u_{b−a} = −(g' b − g' a)/12 + ∫ₐᵇ B₂(fract t)/2 · g''`, under item 128's hypotheses on `g`. Shared object: the trapezoid sum `∑ g k − (g a + g b)/2`, Heun's method's output and the left side of Euler–Maclaurin. Found as the new pair `Analysis.EulerMaclaurin x Analysis.EulerMethod` (import-unrelated; score 15.6, sharing five derivative lemmas); checked by reading `sum_eq_integral_add_two` and `heunIterate` (at `b = a` both sides are `0`), worked by hand, not elaborated. Only unit steps: the library's Euler–Maclaurin is stated on integer nodes. Not load-bearing for any scheduled row. | `sub_heunIterate_eq_eulerMaclaurin` (proposed) | a new module importing Analysis.EulerMaclaurin and Analysis.EulerMethod | items 128 (`sum_eq_integral_add_two`) and 146 (`heunIterate`) | S |
