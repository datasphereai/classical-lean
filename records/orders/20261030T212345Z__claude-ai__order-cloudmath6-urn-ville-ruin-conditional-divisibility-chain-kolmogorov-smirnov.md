<!-- The order's text, as given in the prompt of Claude Code cloud session session_01HgueTbGvJvmksxSgWGMRPt (https://claude.ai/code/session_01HgueTbGvJvmksxSgWGMRPt), copied on 2026-10-30 (UTC) by that session before any Lean file changed, per records/README.md rule 2. Its file name gives claude-ai as the source, as the order's own Setup step 5 names it. -->

# Order CLOUD-MATH-6: five bridges as five new modules

## Goal

Prove five results that join two existing modules each, and land each as a new module on branch
`cloud-math-6`, under the library's gates, with witnesses, one cold review and records. Nothing here is
drafted: you write the statements in Lean from the descriptions below, have them reviewed, then prove them.
The rows are in landing order, cheapest first. Each row's text in the bridges file is quoted under "The
bridge rows" at the end.

| bridge | the result | new module (namespace = module name) | imports | main theorems (names to keep) |
|---|---|---|---|---|
| 157 | Pólya's urn rarely runs far up. With `martingale_urnShare`'s binders and hypotheses (`[IsProbabilityMeasure μ]`, `ℱ`, `r b`, `0 < r + b`, `X`, `hX01`, `hX_meas`, `hX_cond`) and `{c : ℝ} (hc : 0 < c)`: `μ.real {ω | ∃ n, c ≤ urnShare r b X n ω} ≤ (r : ℝ) / (((r : ℝ) + b) * c)`. Proof: the share is a martingale (`martingale_urnShare`), so a supermartingale; it is at least `0` at every point (every draw is `0` or `1`); its start is the constant `r / (r + b)`; Ville's inequality (`measureReal_exists_le_of_supermartingale`) bounds each horizon `N`, and the union over `N` gives "ever", as GamblersRuin lines 977 to 991 do (`Monotone.measure_iUnion`; LikelihoodScore's `measureReal_iUnion_le_of_monotone` comes from RuinBound, which this module does not import). PolyaUrn's bound and measurability lemmas (`urnRed_bounds`, `urnShare_mem_Icc`, `urnRed_stronglyMeasurable`) are `private`, and PolyaUrn's witness of `martingale_urnShare` calls two of them, so state in this module, inside its namespace, your own lemmas for `urnShare r b X n ω ∈ Set.Icc 0 1` (when every draw is `0` or `1`) and for `StronglyMeasurable[ℱ n] (urnRed r X n)`; the proof and the witness both use them, and they go through rule 4's vacuity gate like any helper. Do not touch PolyaUrn. | `ClassicalLean.Probability.UrnVille` | `ClassicalLean.Probability.PolyaUrn`, `ClassicalLean.Probability.MaximalInequality` | `measureReal_exists_urnShare_ge_le` |
| 154 | Item 84's Ville bound under a weaker hypothesis. With `[IsProbabilityMeasure μ]`, `𝒢 : Filtration ℕ m0`, `X : ℕ → Ω → ℝ`, `hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n)` (each step known by time `n + 1`), `hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1`, `hcond : ∀ n, μ[fun ω ↦ (X n ω + 1) / 2 | 𝒢 n] ≤ᵐ[μ] fun _ ↦ p` (the conditional chance of `+1` given the past is at most `p`), `hp0 : 0 < p`, `hp : p ≤ 1 / 2`, `a : ℕ`: `μ.real {ω | ∃ n, (a : ℝ) ≤ walk X n ω} ≤ (p / (1 - p)) ^ a`. No independence and no exact law. Proof: the wins `W (n + 1) = (X n + 1) / 2` (and `W 0 = 0`) are strongly adapted with values in `{0, 1}`; LikelihoodScore's score with `p₀ = p`, `q = 1 − p` is `((1 − p)/p) ^ (wins − losses) = r ^ walk`, `r = (1 − p)/p ≥ 1` (`score_eq_pow`; `p ≤ 1/2` gives `p₀ ≤ q`); reaching `a` makes the score at least `r ^ a`, and `measureReal_exists_le_score_ever` at `α = (p / (1 − p)) ^ a` gives the bound. Item 84's `measureReal_exists_ge_le_of_biased` is the case of independent steps of one law; do not restate it. | `ClassicalLean.Probability.RuinConditional` | `ClassicalLean.Probability.GamblersRuin`, `ClassicalLean.Probability.LikelihoodScore` | `measureReal_exists_ge_le_of_condProb` |
| 156 | Probability meets the divisibility of Lucas numbers. With `measureReal_hit_eq_lucasU`'s binders and hypotheses `hX hind hpm`, a whole number `r` with `hr : 0 < r`, `hp : ∀ n, μ.real {ω | X n ω = 1} = 1 / ((r : ℝ) + 1)` (so `p = 1/(r + 1)`: `1/2, 1/3, 1/4, …`), `a b : ℕ` and `hb : 0 < b`: `(∃ m : ℕ, 0 < m ∧ μ.real {ω | ∃ n, walk X n ω = a ∧ ∀ k ≤ n, -(b : ℝ) < walk X k ω} = 1 / m) ↔ b ∣ a`. Proof: at this `p`, `(1 − p)/p = r`, so item 95's chance is `U b / U (a + b)` with `U = lucasU (1 + r) r`; by `map_lucasU` (the cast `ℤ → ℝ`) work with the integer sequence; `U 0 = 0`, `U (n + 1) = U n + r ^ n` (from the recurrence), so `U` is positive and strictly increasing from `n = 1`; `IsCoprime (1 + r) r`, so `lucasU_gcd` gives `gcd (U m, U n) = U (gcd m n)`; then the chance is `1/m` exactly when `U b ∣ U (a + b)`, exactly when `U (gcd b (a + b)) = U b`, exactly when `gcd b (a + b) = b`, that is `b ∣ a`. | `ClassicalLean.Probability.RuinDivisibility` | `ClassicalLean.Probability.GamblersRuin`, `ClassicalLean.NumberTheory.LucasApparition` | `measureReal_hit_eq_inv_iff_dvd` |
| 165 | Gambler's ruin by first-step analysis. Define in the module (a `def` with a docstring is allowed here) the chain `ruinChain a b : Matrix (Fin (a + b + 1)) (Fin (a + b + 1)) ℝ` on the positions `−b, …, a` (index `i` is position `i − b`): from an inside index it moves one down or one up with chance `1/2` each; the two end indices `0` and `a + b` stay where they are. With `A` the two ends (as a `Finset`), and the fair-walk hypotheses of `integral_exitTime_eq` (`hX hind hpm hmean`, `[IsProbabilityMeasure μ]`): **theorem 1** (`integral_exitTime_eq_meanHitting`): for every `g : Fin (a + b + 1) → ℝ` with `g = 0` on `A` and `g i = 1 + ∑ j, ruinChain a b i j * g j` off `A`, `∫ ω, ((exitTime X a b ω).untopA : ℝ) ∂μ = g ⟨b, _⟩`, the start (position `0`); **theorem 2** (your name): that system has exactly one solution, `g i = (a + b − i) · i` in index terms (position `x`: `(a − x)(x + b)`). Proof: the chain has rows summing to `1`, entries at least `0`, and both ends reachable from every inside index (walk down `i` steps: `(P ^ i) i 0 ≥ (1/2) ^ i > 0`), so `meanHitting_eq` gives exactly one solution; `(a + b − i) i` is one (check the ends and the inside equation); at the start it is `a b`, which is `integral_exitTime_eq`. Both theorems are stated for all `a b : ℕ`, with no positivity hypothesis: if `a = 0` or `b = 0` the start is an end and both sides are `0`, and at `a + b ≤ 1` every index is an end, so `hreach` is vacuous. Theorem 1's docstring says that, with theorem 2 (a solution exists) and `meanHitting_eq` (every solution is the series `h`), it gives `∫ = h ⟨b, _⟩`, the row's form; the cold review classifies the two theorems together. | `ClassicalLean.Probability.RuinChain` | `ClassicalLean.Probability.GamblersRuin`, `ClassicalLean.Probability.FiniteChain` | `ruinChain`, `integral_exitTime_eq_meanHitting`, theorem 2 (your name) |
| 159 | The Kolmogorov–Smirnov statistic is distribution-free. With `[IsProbabilityMeasure μ]`, `X : ℕ → Ω → ℝ`, `hX : ∀ i, Measurable (X i)`, `hlaw : ∀ i, μ.map (X i) = μ.map (X 0)` (identically distributed) and `hF : Continuous F`, `F = cdf (μ.map (X 0))`: **theorem 1** (`sup_abs_empiricalCDF_sub_eq_of_continuous`): `∀ᵐ ω ∂μ, ∀ n, (⨆ x : ℝ, |empiricalCDF X n ω x - F x|) = ⨆ u : Set.Icc (0 : ℝ) 1, |empiricalCDF (fun i ω ↦ F (X i ω)) n ω u - u|`; **theorem 2** (your name): each `F (X i)` is uniform on `[0, 1]`, `μ.real {ω | F (X i ω) ≤ u} = u` for `0 ≤ u ≤ 1` (item 106 at `X i`, with `hlaw`). The row also assumes pairwise independence; theorem 1 does not need it, so leave it out and call the result GENERALIZED. Proof: almost surely, for every `i` and every `x`, `X i ω ≤ x ↔ F (X i ω) ≤ F x` (`≤ → ≤` is `F`'s monotonicity; the converse fails only when `X i ω` lies in a stretch `(s, t]` where `F` is flat, and the union of those stretches has `μ.map (X 0)`-measure `0`: a countable union of intervals of measure `F t − F s = 0`); so `empiricalCDF X n ω x = empiricalCDF (F ∘ X) n ω (F x)` for every `x`; `F` is continuous with limits `0` and `1`, so its range contains `(0, 1)` and lies in `[0, 1]`; at `n = 0` both sides are `1` (the empirical function is `0`; `⨆ x, F x = 1` by `tendsto_cdf_atTop`, and `⨆ u, u = 1`); for `n ≥ 1`, at `u = 0` and `u = 1` the right side's term is `0` almost surely (`P(F (X i) ≤ 0) = 0` by theorem 2, and `F ≤ 1`). Both suprema are of sets bounded by `1`; prove `BddAbove` where `⨆` needs it. The docstrings state the pathwise identity and the uniform marginals only: the row's "the law of the statistic is the same for every continuous `F`" needs the draws mutually independent (`iIndepFun`) as well as identically distributed, so name it there as a consequence under those hypotheses, not as something proved here. | `ClassicalLean.Probability.KolmogorovSmirnov` | `ClassicalLean.Probability.GlivenkoCantelli`, `ClassicalLean.Probability.IntegralTransform` | `sup_abs_empiricalCDF_sub_eq_of_continuous`, theorem 2 (your name) |

The statement you write must say what its row says; where Lean makes you choose (an index set, a cast, how
an interval or a supremum is written), choose the form closest to the row and to the theorems it rests on,
and say what you chose in the docstring. Hypotheses are what the proof needs and no more. Beyond 165's
`ruinChain`, add no definition or notation that a main statement unfolds through.

## Branch rules (hard)

These override any branch this session was assigned; do not push an assigned `claude/*` branch.
- Work only on `cloud-math-6`. First `git fetch origin cloud-math-6` and
  `git switch -c cloud-math-6 --track origin/cloud-math-6` (a fresh clone may hold only another branch), then confirm `origin/cloud-math-6` is `8631a8d3c4316d85c78df697436b0245fa24cf1b`
  and note `git ls-remote origin master` (you report it again at the end). If the branch is missing or
  differs, stop and report.
- Push only with `git push origin cloud-math-6`. Never push `master` or `main`, never force-push, never reset
  a pushed commit, open no pull request, merge nothing on GitHub. Every undo is a new commit.

## Scope

You may: add the five module files under `ClassicalLean/`; add their five import lines at the end of the
import block of `ClassicalLean.lean`; add HELPER lines to `tools/vacuity_reviewed.txt` (rule 4); write
`records/` (rule 6); add `incoming/REPORT.md` and `incoming/reviews/`.
You may not change any existing module (PolyaUrn, GamblersRuin and the rest stay as they are, even where a
lemma you need is private there: copy the step into your module), any other file under `tools/`,
`HANDOFF.md`, `ROADMAP.md`, `records/rules.toml`, the lake files, `lean-toolchain` or `.github/`; nor any
existing row of `records/orders/INDEX.md` or `records/CLAIMS.md`. Needing to is a stop: report it.

## Read first (in the repository)

`records/README.md`; `HANDOFF.md` sections 0, 4 (the gates, "Satisfiability witnesses" with its dated
cases) and 5 (naming); the eight modules named in the table, at least their docstrings and the statements
listed; the library witnesses named under rule 3 (the patterns for yours); CLOUD-MATH-4's order copy under
`records/orders/`, its INDEX and CLAIMS rows and round 77, as the pattern for your records.

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
   `lake env lean tools/VacuityGate.lean` (PASS, 1 reviewed helper). Save every output in `$HOME/cm6/` with
   its sha256. A different value is a stop.
4. Probe every name the order cites, and every other name you will use, with `#check @Name` lines in one
   scratch file per new module, in `$HOME/cm6/` (never under `ClassicalLean/`, where check_sorry and
   check_records would read it), that imports exactly that module's imports, run with `lake env lean` from the
   repository root. Among them: `ClassicalLean.Probability.GamblersRuin.walk`, `…exitTime`,
   `…integral_exitTime_eq`, `…measureReal_exists_ge_le_of_biased`, `…measureReal_hit_eq_lucasU`,
   `ClassicalLean.Probability.LikelihoodScore.score`, `…score_eq_pow`, `…measureReal_exists_le_score_ever`,
   `ClassicalLean.lucasU`, `ClassicalLean.map_lucasU`, `ClassicalLean.lucasU_gcd`,
   `ClassicalLean.Probability.PolyaUrn.urnShare`, `…martingale_urnShare`,
   `ClassicalLean.Probability.MaximalInequality.measureReal_exists_le_of_supermartingale` (and whether
   `SigmaFiniteFiltration μ 𝒢` is found as an instance for a probability measure),
   `ClassicalLean.Probability.empiricalCDF`, `ClassicalLean.Probability.measureReal_cdf_le_eq_of_continuous`,
   `ClassicalLean.Probability.meanHitting_eq`, `ProbabilityTheory.cdf`, `condExp_indep_eq` (or whatever
   turns a conditional expectation of an independent variable into its mean, for 154's witness),
   `gaussianReal_map_neg`. A name that is unknown is not used until
   you find what it is called; say so in the report.
5. Records first, one commit, no `.lean` file: this order's text from "# Order CLOUD-MATH-6" to the end as
   `records/orders/<UTC>__claude-ai__order-cloudmath6-urn-ville-ruin-conditional-divisibility-chain-kolmogorov-smirnov.md`;
   its INDEX row at the bottom (`| CLOUD-MATH-6 |`, in CLOUD-MATH-4's row's form); a CLAIMS row at the bottom
   naming this session and the five module paths; round 80's fragment
   `records/rounds/<UTC>__round-80-urn-ville-ruin-conditional-divisibility-chain-kolmogorov-smirnov.md` naming the five
   module files by full path. `records/README.md` rule 2 (the next order appends the previous order's push
   to its INDEX and CLAIMS rows) does not apply here: MERGE-4's push is appended to its rows by MERGE-5 on
   DSMain; do not change those rows (nor any row CLOUD-MATH-5 adds on its own branch). Push.

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
   hypotheses"); `ruinChain` is a definition, not a theorem. Models to start from, each to be checked like
   any witness; build the random processes as the library's own witnesses do, not from scratch:
   - 157: PolyaUrn's witness of `martingale_urnShare` (line 238), with `r = b = 1` and `c = 3/4`: the start
     share is `1/2 < c`, so the event is not sure, and the bound `1 / (2 · 3/4) = 2/3` is below `1`.
   - 154: GamblersRuin's witness of `measureReal_exists_ge_le_of_biased` (line 1232: `Ω = ℕ → Fin 3`, the
     step `+1` when the coin shows `0`, chance `1/3`), with `p = 1/3` and `a = 2`; `hcond` holds with
     equality there, because the step is independent of the past (prove it through the conditional
     expectation of an independent variable). `p = 1/3 < 1/2`, so the bound `(1/2) ^ 2 = 1/4` is below `1`.
   - 156: GamblersRuin's witness of `measureReal_hit_eq_lucasU` (line 1133, the same coins), with `r = 2`
     (`p = 1/3`), `a = 4`, `b = 2`: `b > 1` and `a > b`, so neither side of the `↔` is a boundary case.
   - 165, theorem 1: GamblersRuin's witness of `measureReal_hit_eq` (line 1105: `Ω = ℕ → Bool`, fair
     `±1` steps) for `hX hind hpm`, with `hmean` from the fair coins, `a = 2`, `b = 3` (six positions, four
     inside), and `g i = (5 − i) · i` (`0, 4, 6, 6, 4, 0`), checked at each of the six indices by `fin_cases`.
     Theorem 2, if it has hypotheses: the same `a`, `b`.
   - 159, both theorems: `Ω = ℝ`, `μ = gaussianReal 0 1`, `X i ω = if Even i then ω else -ω`: the draws are
     not all the same function, each has the standard normal law (`gaussianReal_map_neg`), and `F = Φ` is
     continuous (IntegralTransform's witness, line 147, proves it for `X := id`); for theorem 2, `i = 1`
     (`X 1 = −ω`, whose law goes through `gaussianReal_map_neg`, so `hlaw 1` is not `rfl`) and `u = 1/2` (not an
     end of `[0, 1]`).
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
   statement of which tree each count was measured on. Round 80's fragment names the five module files in
   full, says each bridge was proved by this session (no draft) from the row's sketch, gives each module's
   commit hash in a follow-up edit once it exists (never predicted), and lists every witness and what moves in
   it. Close your CLAIMS row and set your INDEX row's state at the end.
7. **Not closed.** A bridge whose proofs do not build after two hours of work on it (log `date` when you
   start it), or whose statement had to be narrowed in a way its row does not allow, is not closed: its
   module, import line and vacuity entries removed by a new commit, and round 80, the CLAIMS row and the
   report saying which and why. The others go on. A narrowing that keeps the row's meaning (a hypothesis
   the proof needs and the row left implicit) is said plainly in the docstring and the report.
8. **Push often:** after the records commit and after each bridge lands, so nothing is lost if the session
   stops. Each push starts a CI run; an older run on the branch is cancelled, which is fine.
9. **A count is what its output says.** Every count in round 80 and the report is read from a saved output in
   `$HOME/cm6/` and cited by its file name.

## The work, per bridge (in the table's order)

Proofs in place of the `sorry`s; `lake build ClassicalLean.<Area>.<Module>`, 0 errors, 0 warnings;
`python3 -I tools/witness_gate.py <Area>/<Module>.lean` (the path relative to `ClassicalLean/`), every block
OK, `copy-error=0`; then the module's import line added to `ClassicalLean.lean` (only now, so that no pushed
commit imports a module not yet committed), `lake build` of the root (the vacuity gate imports
`ClassicalLean`, and `lake env lean` does not rebuild it), and `lake env lean tools/VacuityGate.lean` (rule
4), its lines for the new theorems quoted in round 80; one commit staged by path (the module, its import line
and, if rule 4 added one, its `tools/vacuity_reviewed.txt` line); push.

## End checks, in this order

1. Before running them, write `$HOME/cm6/expected.txt` with the expected result of each, and its sha256:
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
   `tools/vacuity_reviewed.txt`.    `git diff 8631a8d HEAD -- ClassicalLean.lean`: only the added import lines.
   `git diff --name-status 8631a8d HEAD -- records/`: only `A` lines (this order's copy, round 80) and `M`
   for `records/orders/INDEX.md` and `records/CLAIMS.md`. `git diff -U0 8631a8d HEAD -- records/orders/INDEX.md
   records/CLAIMS.md`: only `+` lines, at the end of each file.
4. Records: round 80 completed with the commit hashes and the counts from the saved outputs; CLAIMS closed;
   INDEX set; check_records PASS; push.
5. `incoming/REPORT.md` (and push it): each bridge's final statements, verdict, witnesses and what moves;
   every probe that found a name unknown; the review and its fixes; each end check's expected and observed
   value, cited by file; anything not closed or narrowed; `git ls-remote origin master` at the start and the
   end; the branch's last commit. Then tell Dustin in a few plain sentences what was proved, define any
   technical term the first time, and give the last commit's hash.

## Done means

Branch `cloud-math-6` from `8631a8d`, pushed, with: the records commit; one commit per bridge landed, each
module building with 0 warnings, no `sorry`, no new axiom; every witness OK in the witness gate and passed by
the review; the review in `incoming/reviews/`; every end check as expected or each miss reported; records
closed; `incoming/REPORT.md`. Or a bridge reported not closed under rule 7 and undone. Nothing on `master`.

## After the session (claude-ai)

claude-ai checks the branch against `8631a8d` (files, imports, no existing module changed), reruns the
gates in its own clone, and writes MERGE-5 for DSMain, merging this branch and `cloud-math-5` together: the merges, then the gates that did not run here
(gate 7, the banned scan, the whole-library witness gate, the bridge search, the report tool), and
HANDOFF's and ROADMAP's entries.

## Not in this order

Bridges 155, 158, 164, 166 and 167 (CLOUD-MATH-5, on its own branch); LEAN-38's pair-by-pair reads; TWINS-1; GATE-2; HANDOFF and
ROADMAP entries (MERGE-5); anything on `master`.

## The bridge rows

(Quoted from `lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md`, a lane file this session cannot
read, rows 157, 154, 156, 165 and 159 in landing order, copied by script; the header row is the file's.)

| # | area | the result | Lean names | module | rests on | cost |
|---|---|---|---|---|---|---|
| 157 | 10, bridge | Pólya's urn rarely runs far up: with `r` red and `b` blue balls (`r + b > 0`) and draws that are each `0` or `1`, the chance that the red share ever reaches `c > 0` is at most `r / ((r + b) c)` (for `c ≤ r / (r + b)` the bound is at least `1` and says nothing). The share is a nonnegative martingale (item 137's `martingale_urnShare`; nonnegative at every point because every draw is `0` or `1`) whose start is the constant `r / (r + b)`, so `measureReal_exists_le_of_supermartingale` (Ville's inequality for a nonnegative supermartingale, up to each `N`) gives the bound up to `N`, and the union over `N` gives "ever", as `measureReal_exists_le_score_ever` does for the likelihood score. Shared object: a nonnegative martingale and Ville's inequality. Found as the new shape key `supermartingale: Probability.MaximalInequality × Probability.PolyaUrn` (import-unrelated), also a new pair (rank 69, 13 shared constants); checked by reading both statements (Ville's inequality asks a supermartingale, nonnegative everywhere, `c > 0` and a finite measure; the urn theorem gives a martingale under a probability measure), not elaborated. Not load-bearing for items 96 to 110 (none of them is about martingales or urns), so the cut is not re-drawn. | `measureReal_exists_urnShare_ge_le` | ClassicalLean.Probability.PolyaUrn, importing Probability.MaximalInequality | library `martingale_urnShare`, `measureReal_exists_le_of_supermartingale` | S |
| 154 | 10, bridge | Item 84's Ville bound under a weaker hypothesis: for `±1` steps `X n`, each known by time `n + 1`, whose conditional chance of `+1` given the past is at most `p`, `0 < p ≤ 1/2` (no independence and no exact law), the chance that the walk ever reaches `a` is at most `(p/(1 − p))^a`. The library's likelihood score with `p₀ = p`, `q = 1 − p` on the wins `W (n + 1) = (X n + 1)/2` is exactly `r^(walk n)`, `r = (1 − p)/p` (`score_eq_pow`), so `measureReal_exists_le_score_ever` at `α = r^(−a)` gives it; item 84's `measureReal_exists_ge_le_of_biased` is the case of independent steps of one law. Shared object: the nonnegative supermartingale `r^(walk n)` and Ville's inequality. Found as the new shape key `supermartingale: GamblersRuin × LikelihoodScore` (import-unrelated); checked by reading both modules' statements (indexing of `score` and `walk` matched), not elaborated. Not load-bearing for items 89 to 110: item 95 rests on item 84's hit formula, not on this bound, so the cut is not re-drawn. | `measureReal_exists_ge_le_of_condProb` | ClassicalLean.Probability.GamblersRuin (imports Probability.LikelihoodScore) | library `walk`, `score_eq_pow`, `measureReal_exists_le_score_ever` | S |
| 156 | 10, bridge | Probability meets the divisibility of Lucas numbers: when the up-chance is `p = 1/(r + 1)` with `r` a positive whole number (`p = 1/2, 1/3, 1/4, …`), the chance that the `±1` walk reaches `a` before `−b` (`b ≥ 1`) is the reciprocal of a whole number exactly when `b` divides `a`. By item 95 the chance is `U b / U (a + b)` with `U = lucasU (1 + r) r`; `1 + r` and `r` are coprime, so `gcd (U m, U n) = U (gcd m n)` (`lucasU_gcd`, `NumberTheory.LucasApparition`); `U` is increasing from `n = 1`, so `U b ∣ U (a + b)` exactly when `b ∣ a + b`, that is `b ∣ a`. At `p = 1/2` it is `b / (a + b)`. Shared object: the Lucas sequence `lucasU (1 + r) r`. Found as the new shape key `linear recurrence: NumberTheory.LucasApparition × Probability.GamblersRuin` (import-unrelated); checked by hand and by an exact check (order LEAN-29's `bridges/check156.py`, line `B156.unit`: 288 cells, `r` in 1..4, `a` in 0..8, `b` in 1..8; line `B156.gcd`), not elaborated. Not load-bearing for items 96 to 110, so the cut is not re-drawn. | `measureReal_hit_eq_inv_iff_dvd` | ClassicalLean.Probability.GamblersRuin, importing NumberTheory.LucasApparition | library `measureReal_hit_eq_lucasU` (item 95), `lucasU_gcd`, `lucasU_dvd_lucasU_of_dvd` | S |
| 165 | 8, bridge | Gambler's ruin by first-step analysis: for the fair `±1` walk started at `0` and stopped on leaving `(−b, a)`, its chain on the `a + b + 1` positions `−b, …, a` (move up or down with chance `1/2` each inside, stay at the two ends) with the target `A = {−b, a}` meets `meanHitting_eq`'s hypotheses (rows sum to `1`, entries at least `0`, both ends reachable from every inside position), and the mean hitting time `h` that theorem gives at the start position equals the walk's mean exit time: `∫ ω, ((exitTime X a b ω).untopA : ℝ) ∂μ = h 0 = a b`. Item 148's uniqueness gives `h x = (a − x)(x + b)` (that function solves `g = 0` at the ends and `g x = 1 + (g (x − 1) + g (x + 1))/2` inside), and GamblersRuin's `integral_exitTime_eq` gives the same `a b` for the process, so the two halves meet at the start. Shared object: the mean time to reach the ends of an interval, as an expectation of a stopping time and as the solution of a linear system. Found as the new shape key `stopping time: Probability.FiniteChain × Probability.GamblersRuin` (import-unrelated: neither imports the other); checked by reading both statements (`integral_exitTime_eq` asks the fair-walk hypotheses `hX`, `hind`, `hpm`, `hmean` and any `a b : ℕ`; `meanHitting_eq` asks `hP`, `hP0`, `hreach` on a `Fintype`), not elaborated. Not load-bearing for any scheduled row. | `integral_exitTime_eq_meanHitting` (proposed) | ClassicalLean.Probability.GamblersRuin, importing Probability.FiniteChain (or a new module importing both) | item 148 (`meanHitting_eq`), library `integral_exitTime_eq` | S |
| 159 | 2, bridge | The Kolmogorov–Smirnov statistic is distribution-free: for pairwise independent, identically distributed real draws `X i` whose distribution function `F` is continuous, almost surely `sup over x of |F_n(x) − F(x)| = sup over u ∈ [0, 1] of |G_n(u) − u|` for every `n`, where `G_n` is the empirical distribution function of `U i = F(X i)`; by item 106 the `U i` are uniform on `[0, 1]`, so the law of the statistic is the same for every continuous `F`, and one table of critical values serves every such test. Shared objects: `cdf`, `empiricalCDF` and the transform `F(X)`. `X i ≤ x` gives `F(X i) ≤ F(x)`, and the converse fails only where `F` is flat on `[x, X i]`, which has chance `0` (by hand). | `sup_abs_empiricalCDF_sub_eq_of_continuous` (proposed) | `Probability.GlivenkoCantelli` × `Probability.IntegralTransform` | item 106 (`measureReal_cdf_le_eq_of_continuous`), item 60 (`empiricalCDF`) | S–M |
