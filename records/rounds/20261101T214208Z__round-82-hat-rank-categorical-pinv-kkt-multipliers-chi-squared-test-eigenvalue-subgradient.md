# Round 82 — the hat matrix's rank, the categorical covariance's pseudoinverse, one KKT multiplier for every minimiser, the chi-squared test, the largest eigenvalue by subgradients (order CLOUD-MATH-7)

Session: Claude Code cloud session `session_01HgueTXEfmRyGHEx4eHzyN9`
(https://claude.ai/code/session_01HgueTXEfmRyGHEx4eHzyN9), executing order `CLOUD-MATH-7`
(`records/orders/20261101T214207Z__claude-ai__order-cloudmath7-hat-rank-categorical-pinv-kkt-multipliers-chi-squared-test-eigenvalue-subgradient.md`),
bridge rows 170, 172, 168, 169 and 171 of `MATH-PLAN-library-2-bridges-2.md`, in a cloud container's
clone of GitHub `datasphereai/classical-lean` on branch `cloud-math-7`, from
`d723fbfd171cf9c018ddc0160446984ef1daffee` (checked equal to `origin/cloud-math-7` before any
change, `branch_start.txt`). `git ls-remote origin master` at the start:
`d723fbfd171cf9c018ddc0160446984ef1daffee` (`master_start.txt`). Lean and Mathlib v4.34.0
(`lake exe cache get`, 8908 files).

**No drafts.** The five statements were written by order LEAN-38 (a reading order) and given in
the order word for word; each bridge is proved by this session from its row's sketch, and no proof
comes from an earlier draft.

Evidence: `$HOME/cm7/` (outside the repository); every count below is read from a saved output
there, cited by its file name (rule 9).

First part written before any Lean file changed; completed after the work, below.

## Modules this round adds (five new modules)

* bridge 170: `ClassicalLean/Algebra/HatMatrixRank.lean` (`ClassicalLean.Algebra.HatMatrixRank`),
  importing `ClassicalLean.Algebra.Pseudoinverse` and `ClassicalLean.Statistics.Cochran`;
* bridge 172: `ClassicalLean/Algebra/CategoricalPseudoinverse.lean`
  (`ClassicalLean.Algebra.CategoricalPseudoinverse`), importing
  `ClassicalLean.Algebra.Pseudoinverse` and `ClassicalLean.Simplex.SecondOrder`;
* bridge 168: `ClassicalLean/Analysis/KKTMultipliers.lean` (`ClassicalLean.Analysis.KKTMultipliers`),
  importing `ClassicalLean.Analysis.GradientDescent` and `ClassicalLean.Analysis.KKT`;
* bridge 169: `ClassicalLean/Statistics/ChiSquaredTest.lean`
  (`ClassicalLean.Statistics.ChiSquaredTest`), importing `ClassicalLean.Probability.ChiSquared` and
  `ClassicalLean.Statistics.NeymanPearson`;
* bridge 171: `ClassicalLean/Analysis/EigenvalueSubgradient.lean`
  (`ClassicalLean.Analysis.EigenvalueSubgradient`), importing `ClassicalLean.Algebra.MinMax` and
  `ClassicalLean.Analysis.SubgradientMethod`;
* `ClassicalLean.lean`: five import lines, at the end of its import block, in landing order, each
  added by its module's landing commit.

No existing module changes. `tools/vacuity_reviewed.txt` changes only if a helper is listed (the
order's rule 4). Nothing else under `tools/` changes. `records/orders/INDEX.md` also gets order
LEAN-38's row (a reading order with no repository change), directly above this order's row, as the
order's Setup 5 asks.

## Starting counts (measured in this session, before any new module, clean tree at `d723fbf`)

* `lake build`: exit 0, `Build completed successfully (4206 jobs).`, 0 lines with `warning:`
  (`setup3_lake_build.txt`).
* `lake env lean tools/AxiomGate.lean`: `axiom gate PASS — 3914 theorem constant(s) under
  [ClassicalLean] …; 0 scoped exceptions` (`setup3_axiom.txt`).
* `python3 -I tools/check_sorry.py`: PASS, 153 files (`setup3_sorry.txt`).
* `python3 -I tools/check_records.py`: PASS, 153 modules, 1 named exemption (`setup3_records.txt`).
* `lake env lean tools/VacuityGate.lean`: PASS, 1 reviewed helper, 0 VACUOUS-PENDING, rule 5 out of
  heartbeats on 0 theorems (`setup3_vacuity.txt`).
* sha256 of each output: `setup_sha256.txt`.

**A slip, said plainly.** While the starting `lake build` ran, and before the other starting gates,
the draft of `ClassicalLean/Algebra/HatMatrixRank.lean` was written into the tree for about a
minute, then moved out to `$HOME/cm7/drafts/` (21:31 UTC). It was imported by nothing, so the build
could not read it, and check_sorry, check_records, the axiom gate and the vacuity gate all ran after
it was gone. The setup counts above are the clean tree's.

## Probes (Setup 4)

One file per new module, importing exactly its imports (`$HOME/cm7/probes/probe170.lean`,
`probe172.lean`, `probe168.lean`, `probe169.lean`, `probe171.lean`, outputs `probe*.out`), and a
second round for the names the proofs needed (`probe168b`, `probe169b`, `probe171b`, `probe172b`).
Every name the order cites is known **except `HasGradientAt.add`**, which Mathlib does not have
(its `HasGradientAt` lemmas are `unique`, `differentiableAt`, `hasDerivAt`, … in
`Analysis/Calculus/Gradient/Basic.lean`). Bridge 168 builds the Lagrangian's derivative with
`hasGradientAt_iff_hasFDerivAt`, `HasFDerivAt.add`, `HasFDerivAt.sum` and `HasFDerivAt.const_mul`,
as `exists_kkt_of_slater`'s proof does. Names of this session's own that were unknown as first
written, and what was used instead: `HasGradientAt.sum`, `HasGradientAt.const_smul` (the
`HasFDerivAt` forms); `Matrix.transpose_diagonal` (`Matrix.diagonal_transpose`, not needed in the
end); `MeasureTheory.lintegral_fintype_prod_eq_prod` (none; the product's measure of a box goes
through the Bochner integral, `integral_fintype_prod_eq_prod` and
`ofReal_integral_eq_lintegral_ofReal`); `MeasureTheory.integral_withDensity_eq_integral_toReal_smul`
(it is in the root namespace); `MeasureTheory.Measure.volume_pi` (`MeasureTheory.volume_pi`);
`Set.indicator_pi`, `Finset.prod_indicator`, `Measure.IsProbabilityMeasure` (not needed);
`Matrix.isHermitian_iff_isSymmetric` (in Mathlib, outside these imports; not needed);
`Matrix.toEuclideanLin_apply`, `Matrix.piLp_equiv_toEuclideanLin` (unfold `Matrix.toEuclideanLin`
instead); `OrthonormalBasis.span_eq`, `Basis.span_eq` (`Module.Basis.span_eq` with
`OrthonormalBasis.coe_toBasis`); `LinearMap.coeFn_sum` (`LinearMap.sum_apply`).

## Statement stage and its cold review (rule 1, rule 5)

The five modules were written with every statement final, every proof `sorry` and every witness
complete. Each was elaborated with `lake env lean` with only the `sorry` warning
(`stmt_HatMatrixRank.out`, `stmt_CategoricalPseudoinverse.out`, `stmt_KKTMultipliers.out`,
`stmt_ChiSquaredTest.out`, `stmt_EigenvalueSubgradient.out`). One docstring line of 172 copied from
LEAN-38's scratch text was over 100 characters; it was re-wrapped with no word changed. The witness
gate was run on the four witnessed modules as a form check: each block was read as a witness of its
theorem, BROKEN only through `sorryAx`.

The brief was built by script (`$HOME/cm7/review/mkbrief.py`). It copies the order's goal, table,
statements, rules 2 and 3 and bridge rows from the order's copy, HANDOFF.md's "Satisfiability
witnesses" paragraph, the statements the bridges rest on (cut from their modules), the probes'
outputs, the five modules and their elaboration outputs. Its first version cut `pinv`'s docstring
at a blank line and picked two docstring lines as code. The script was fixed to track comment
blocks, and the brief rebuilt before it was sent: `brief.md`, sha256
`79d5ce7767182373318c97b124858ec2d504488dfae4182a6569cb45349aef6e`.

One fresh subagent reviewed it: `incoming/reviews/review-1.md` (sha256
`bd224a76f199f46f02c37bfeb11b471a30c0ccc4fb3ce6506656169af494cc60`), **FINDINGS 2, both MINOR**:

1. 171's witness docstring gave `u = e₀` and `g = (1, 0)` only at `x 0`. It now says this at each
   of `x 0`, `x 1`, `x 2`, and that each step moves the iterate by `(-1/2, 0)`.
2. 169's witness docstring did not say what moves, and gave no number for the level. It now says
   the densities move with `v` (`1 / (2πv)` at `x = 0`) and the level is
   `P(χ²₂ > 3) = e^(-3/2) ≈ 0.223`.

Neither fix changed a statement or a witness's arguments, so there was no second pass (rule 5).
Verdicts: all five main theorems **FAITHFUL**, word for word the order's; all four witnesses PASS.
No theorem is WEAKER.

## Proofs, by bridge (start times: `start170.txt`, `start172.txt`, `start168.txt`, `start169.txt`, `start171.txt`)

Each bridge was proved by this session from its row's sketch; no draft was used.

* **170** (from 22:02:11 UTC, landed 22:08): `pinv_spec` gives `A X A = A`, so `H = A X` is
  idempotent. `Matrix.rank_mul_le_left` bounds `rank H ≤ rank A` and, through `A = H A`,
  `rank A ≤ rank H`. `rank_eq_trace_of_isIdempotentElem` gives the trace. `sum_rank_eq_iff` on the
  pair `H`, `1 - H`, both idempotent (`IsIdempotentElem.one_sub`), gives
  `rank H + rank (1 - H) = card m`. The first linted build had 0 warnings (`build170.txt`).
* **172** (from 22:08:50, landed 22:15): matrix algebra with `J = 1 1ᵀ`, `Dp = diagonal p` and
  `C = Dp - Dp J Dp`. `categoricalCov_mulVec_one` gives `C J = 0`, and the symmetry of `C` gives
  `J C = 0`. Then `C P = P C = C`, `C D⁻¹ = 1 - Dp J`, `D⁻¹ C = 1 - J Dp` and `J P = P J = 0`, so
  `C X = P` and `X C = P` for `X = P D⁻¹ P`. With `P² = P` and `Pᵀ = P`, `pinv_unique` gives
  `X = pinv C`. The first `lake env lean` had two deprecation warnings (`if_neg`), seen in the
  terminal and not saved; that step became `simp`. The linted build then had 0 warnings
  (`build172.txt`).
* **168** (from 22:15:53, landed 22:23): `exists_kkt_of_slater` gives `w`. Tangent planes
  (`add_inner_gradient_le` for `f` and each `g i` at `xbar`), complementary slackness and
  stationarity at `xbar` give `f xbar ≤ f z + ∑ i, w i * g i z` for every `z`. At a feasible
  minimiser `y` (`f y = f xbar`), the sum is `0` with each term `≤ 0`
  (`Finset.sum_eq_zero_iff_of_nonpos`). Then `y` minimises the Lagrangian on `univ`, so it is a
  local minimum, and `IsLocalMin.hasFDerivAt_eq_zero` with `inner_self_eq_zero` gives stationarity.
  The converse is `isMinOn_of_kkt`. The first `lake env lean` had four deprecation warnings
  (`ContinuousLinearMap.add_apply` and three like it), seen in the terminal and not saved; they
  became the root names. The linted build then had 0 warnings (`build168.txt`).
* **169** (from 22:23:16, landed 22:34): there are three steps.
  * For `v < v'`, `gaussianPDFReal 0 v' y = a · exp (y² d) · gaussianPDFReal 0 v y`, with
    `a = √(2πv)/√(2πv') > 0` and `d = 1/(2v) − 1/(2v') ≥ 0`. So the product's ratio is
    `g S = a ^ k · exp (S d)`, nondecreasing and nonnegative. Karlin–Rubin (`γ = 0`) then applies;
    its integrability and normalisation come from `Integrable.fintype_prod` and
    `integral_fintype_prod_eq_prod` with `integral_gaussianPDFReal_eq_one`.
  * The density measure is `Measure.pi` of `k` laws `N(0, v₀)`. This uses `Measure.pi_eq` on boxes,
    `restrict_pi_pi`, `integral_fintype_prod_eq_prod`, `ofReal_integral_eq_lintegral_ofReal` and
    `gaussianReal_apply`. NeymanPearson's private `integral_mul_eq_integral_withDensity` step is
    copied inline, so the size is `∫ φ dP = P(S > c)` (`integral_thresholdTest`).
  * `hasLaw_sum_sq_gaussian` at `X i x = x i / √v₀` gives the chi-squared tail. The `X i` are
    independent by `iIndepFun_pi`, and have law `N(0, 1)` by `measurePreserving_eval` and
    `gaussianReal_map_const_mul`.

  The first linted build had 1 warning, a line of 101 characters (`build169_first.txt`). It was
  re-wrapped, and the re-run had 0 warnings (`build169.txt`).
* **171** (from 22:34:39, landed 22:41): `min_sub_le_of_subgradient` with
  `f y = λ₀(T y)` and `g k` the order's vector; its `hsub` is proved here.
  `le_eigenvalues_mul_of_mem` at index `0` applies to the unit `u` because `Finset.Ici 0` is
  `univ` and the span of the whole basis is `⊤`. `apply_eigenvectorBasis` gives
  `⟪T (x k) u, u⟫ = λ₀(T (x k))`. The quadratic form is affine in the parameter. The first
  `lake env lean` had two errors (an unknown lemma name and a trivial `ℝ → ℝ` cast). Both were
  fixed before the linted build, which had 0 warnings (`build171.txt`).

No proof forced a statement to change: **no narrowing** (rule 7). Every bridge closed well inside its
two hours. No helper declaration was added to any module (every step is a `have`), no helper was
flagged, and `tools/vacuity_reviewed.txt` is unchanged.

## Per bridge: the gates before each landing commit

| bridge | module build | witness gate | root build | vacuity gate |
|---|---|---|---|---|
| 170 | 0 warnings (`build170.txt`) | PASS, no block (no hypothesis), copy-error=0 (`witness170.txt`) | 4207 jobs, 0 warnings (`rootbuild170.txt`) | PASS, 1 reviewed helper (`vacuity170.txt`) |
| 172 | 0 warnings (`build172.txt`) | PASS, OK=1, copy-error=0 (`witness172.txt`) | 4208 jobs, 0 warnings (`rootbuild172.txt`) | PASS, 1 reviewed helper (`vacuity172.txt`) |
| 168 | 0 warnings (`build168.txt`) | PASS, OK=1, copy-error=0 (`witness168.txt`) | 4209 jobs, 0 warnings (`rootbuild168.txt`) | PASS, 1 reviewed helper (`vacuity168.txt`) |
| 169 | 0 warnings (`build169.txt`) | PASS, OK=1, copy-error=0 (`witness169.txt`) | 4210 jobs, 0 warnings (`rootbuild169.txt`) | PASS, 1 reviewed helper (`vacuity169.txt`) |
| 171 | 0 warnings (`build171.txt`) | PASS, OK=1, copy-error=0 (`witness171.txt`) | 4211 jobs, 0 warnings (`rootbuild171.txt`) | PASS, 1 reviewed helper (`vacuity171.txt`) |

The vacuity gate prints a line for a theorem only when it flags one, so its lines for the new
theorems are none. Its whole output each time is the summary line `vacuity gate PASS — no vacuous
theorems in [ClassicalLean] (1 reviewed helpers and 0 VACUOUS-PENDING on tools/vacuity_reviewed.txt);
rule 5 ran out of its 400000 heartbeats on 0 theorems`.

## Witnesses (four, each after its module's last line; all OK in the witness gate)

* `rank_mul_pinv_eq` (170): no hypothesis, so no witness (the order's rule 3).
* `pinv_categoricalCov` (172): `ι = Fin 3`, `p = (1/2, 1/3, 1/6)`, positive and summing to `1`.
  What moves: `p` is not uniform, so `diagonal (1/p) = diag (2, 3, 6)` is not a multiple of `1` and
  the projection `P` matters.
* `exists_multipliers_isMinOn_iff` (168): on `ℝ`, `ι = Fin 2`, `f y = (y − 2)² / 2`,
  `g 0 y = y − 1`, `g 1 y = −y − 5`, gradients `y − 2`, `1`, `−1`; Slater point `0` (`−1`, `−5`);
  `xbar = 1`. What moves: the unconstrained minimiser `2` is infeasible, so the constraint `g 0` is
  active at `xbar` with multiplier `1`, not `0`, while `g 1` is slack (`−6`).
* `isUniformlyMostPowerful_sum_sq_gaussian` (169): `k = 2`, `v₀ = 1`, `c = 3`. What moves: the
  densities change with `v` (`1 / (2πv)` at `x = 0`), and the level
  `P(χ²₂ > 3) = e^(-3/2) ≈ 0.223` is strictly between `0` and `1`.
* `min_sub_le_of_subgradient_eigenvalues` (171):
  * the setting: `F = EuclideanSpace ℝ (Fin 2)`, `n = 1`, `m = 2`, `A₀ = diag(1, 0)`,
    `A 0 = diag(1, −1)`, `A 1 = diag(0, 1)`, so `T x = diag(1 + x 0, −x 0 + x 1)`; `η = 1/2`,
    `G = 2` (`‖g‖² ≤ 2` for every unit `u`), `T = 3`, `z = 0`;
  * the iterates are defined inline by `Nat.rec` from `x 0 = (3/4, 0)`, so `hstep` holds by `rfl`
    (no closed form was needed);
  * what moves: the iterates `(3/4, 0)`, `(1/4, 0)`, `(−1/4, 0)`, `(−3/4, 0)` give
    `diag(7/4, −3/4)`, `diag(5/4, −1/4)`, `diag(3/4, 1/4)`, with top eigenvector `e₀` and
    `g = (1, 0)` at each step, every step moving, and no tie inside the horizon.

## The modules and their theorem-constant counts

Measured with `$HOME/cm7/count/census.lean`: the axiom gate's predicate (user name under
`ClassicalLean`, no macro scopes, `.thmInfo`), restricted to the constants that `env.getModuleFor?`
places in the module. Measured on the tree at `715f99b`, with all five modules landed and the tree
clean (`count/census_all.txt`).

| module | bridge | theorem constants |
|---|---|---|
| `ClassicalLean/Algebra/HatMatrixRank.lean` | 170 | 2: 1 written, 1 `_proof_` |
| `ClassicalLean/Algebra/CategoricalPseudoinverse.lean` | 172 | 2: 1 written, 1 `_simp_` |
| `ClassicalLean/Analysis/KKTMultipliers.lean` | 168 | 1: 1 written |
| `ClassicalLean/Statistics/ChiSquaredTest.lean` | 169 | 11: 1 written, 10 `_simp_` |
| `ClassicalLean/Analysis/EigenvalueSubgradient.lean` | 171 | 1: 1 written |
| **five modules** | | **17** |

3914 + 17 = 3931, the axiom gate's count below. The import closure went from 6546 to 6551 modules
(`ClassicalLean` from 154 to 159, Mathlib 3779 both times; `count/closure_base.txt`,
`count/closure_after.txt`, counted from `env.header.moduleNames`, Lean's core included), so no new
Mathlib module, and the build has 4206 + 5 = 4211 jobs.

## End check 1 (clean tree at `715f99b`, predictions first: `expected.txt`, sha256 `fd9956b3…`)

| command | expected | measured |
|---|---|---|
| `lake build` | 4211 jobs, 0 warnings | `Build completed successfully (4211 jobs).`, 0 `warning:` lines (`ec1_build.txt`) |
| `lake env lean tools/AxiomGate.lean` | PASS 3931 | PASS 3931, 0 scoped exceptions (`ec1_axiom.txt`) |
| `python3 -I tools/check_sorry.py` | PASS 158 | PASS 158 (`ec1_sorry.txt`) |
| `python3 -I tools/check_records.py` | PASS 158, 1 exemption | the same (`ec1_records.txt`) |
| `lake env lean tools/VacuityGate.lean` | PASS, 1 reviewed helper | the same, 0 VACUOUS-PENDING, rule 5 out on 0 (`ec1_vacuity.txt`) |
| `python3 -I tools/witness_gate.py` on the five modules | PASS, OK=4, copy-error=0 | PASS, modules=5, OK=4, PARTIAL=0, WRONG-NAME=0, BROKEN=0, copy-error=0 (`ec1_witness.txt`) |
| `python3 tools/compile_rules.py drift records/rules.toml HANDOFF.md` | PASS no drift | `PASS no drift` (`ec1_drift.txt`) |

**End check 2** (not run here; they run on DSMain at MERGE-6): gate 7, the banned-vocabulary scan,
the whole-library witness gate, the bridge search and the report tool.

**End check 3** (`ec3.txt`):
* Both greps on the five new files find nothing (rc 1).
* `git diff --name-only d723fbf HEAD` lists only the five modules, `ClassicalLean.lean`,
  `records/` and `incoming/reviews/review-1.md`.
* In `ClassicalLean.lean` the diff is only the five added import lines.
* `records/` has only `A` (this order's copy, round 82) and `M` (INDEX, CLAIMS).
* INDEX and CLAIMS have only `+` lines, at their ends.

Every output's sha256 is in `end_sha256.txt`.

## Commits (branch `cloud-math-7`, each pushed with `git push origin cloud-math-7`)

* `159e1b0` — records first: the order's copy, LEAN-38's and this order's INDEX rows, the CLAIMS
  row and this fragment's first part.
* `24c0ef5` — `incoming/reviews/review-1.md`.
* `c7bc0fd` — bridge 170, `ClassicalLean/Algebra/HatMatrixRank.lean`, and its import line.
* `3541793` — bridge 172, `ClassicalLean/Algebra/CategoricalPseudoinverse.lean`, and its import
  line.
* `e6d979c` — bridge 168, `ClassicalLean/Analysis/KKTMultipliers.lean`, and its import line.
* `26f32ce` — bridge 169, `ClassicalLean/Statistics/ChiSquaredTest.lean`, and its import line.
* `715f99b` — bridge 171, `ClassicalLean/Analysis/EigenvalueSubgradient.lean`, and its import
  line.
* The commit that carries this section: the CLAIMS row closed and the INDEX row's state. A commit
  cannot cite its own hash.
* Then `incoming/REPORT.md`.

All five bridges are closed: none narrowed, none undone. `master` was not touched.
