# Report: order CLOUD-MATH-7, five bridges as five new modules

Claude Code cloud session `session_01HgueTXEfmRyGHEx4eHzyN9`
(https://claude.ai/code/session_01HgueTXEfmRyGHEx4eHzyN9), branch `cloud-math-7`, from
`d723fbfd171cf9c018ddc0160446984ef1daffee`. The full record is round 82
(`records/rounds/20261101T214208Z__round-82-hat-rank-categorical-pinv-kkt-multipliers-chi-squared-test-eigenvalue-subgradient.md`).
Every count below is read from a saved output in `$HOME/cm7/` of the cloud container, cited by its
file name.

## Outcome

All five bridges are **closed**: 170, 172, 168, 169 and 171, each in its own new module, each
statement the order's word for word, each proof by this session from the row's sketch (no draft).
None was narrowed, none undone. No helper declaration was added, and `tools/vacuity_reviewed.txt`
is unchanged. `master` was not touched.

* `git ls-remote origin master` at the start: `d723fbfd171cf9c018ddc0160446984ef1daffee`
  (`master_start.txt`).
* At the end: `d723fbfd171cf9c018ddc0160446984ef1daffee` (`master_end.txt`).

Network (Setup 1, `setup1_curl.txt`): `HTTP/1.1 200 Connection Established`, then `HTTP/2 404` from
the cache server itself. That is not a stop: `lake exe cache get` downloaded and decompressed 8908
files.

## Final statements (extracted from the modules by script)

### Bridge 170: `ClassicalLean/Algebra/HatMatrixRank.lean`, `ClassicalLean.Algebra.HatMatrixRank.rank_mul_pinv_eq`

```lean
theorem rank_mul_pinv_eq {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) :
    (A * ClassicalLean.Algebra.Pseudoinverse.pinv A).rank = A.rank ∧
      (A * ClassicalLean.Algebra.Pseudoinverse.pinv A).trace = (A.rank : ℝ) ∧
      (1 - A * ClassicalLean.Algebra.Pseudoinverse.pinv A).rank = Fintype.card m - A.rank := by …
```

### Bridge 172: `ClassicalLean/Algebra/CategoricalPseudoinverse.lean`, `ClassicalLean.Algebra.CategoricalPseudoinverse.pinv_categoricalCov`

```lean
theorem pinv_categoricalCov {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → ℝ}
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1) :
    pinv (categoricalCov p) =
        (1 - (Fintype.card ι : ℝ)⁻¹ • Matrix.of fun _ _ ↦ (1 : ℝ)) *
          Matrix.diagonal (fun i ↦ (p i)⁻¹) *
          (1 - (Fintype.card ι : ℝ)⁻¹ • Matrix.of fun _ _ ↦ (1 : ℝ)) ∧
      categoricalCov p * pinv (categoricalCov p) =
        1 - (Fintype.card ι : ℝ)⁻¹ • Matrix.of fun _ _ ↦ (1 : ℝ) := by …
```

### Bridge 168: `ClassicalLean/Analysis/KKTMultipliers.lean`, `ClassicalLean.Analysis.KKTMultipliers.exists_multipliers_isMinOn_iff`

```lean
theorem exists_multipliers_isMinOn_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] {f : E → ℝ} {g : ι → E → ℝ} {f' : E → E}
    {g' : ι → E → E} {xbar : E} (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hf' : ∀ x, HasGradientAt f (f' x) x) (hg' : ∀ i x, HasGradientAt (g i) (g' i x) x)
    (hslater : ∃ x0, ∀ i, g i x0 < 0) (hxbar : ∀ i, g i xbar ≤ 0)
    (hmin : IsMinOn f {x | ∀ i, g i x ≤ 0} xbar) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ ∀ y : E,
      ((∀ i, g i y ≤ 0) ∧ IsMinOn f {x | ∀ i, g i x ≤ 0} y) ↔
        ((∀ i, g i y ≤ 0) ∧ (∀ i, w i * g i y = 0) ∧ f' y + ∑ i, w i • g' i y = 0) := by …
```

### Bridge 169: `ClassicalLean/Statistics/ChiSquaredTest.lean`, `ClassicalLean.Statistics.ChiSquaredTest.isUniformlyMostPowerful_sum_sq_gaussian`

```lean
theorem isUniformlyMostPowerful_sum_sq_gaussian {k : ℕ} (hk : 0 < k)
    (v₀ : Set.Ioi (0 : ℝ≥0)) (c : ℝ) :
    ClassicalLean.Statistics.IsUniformlyMostPowerful (volume : Measure (Fin k → ℝ))
      (fun (v : Set.Ioi (0 : ℝ≥0)) (x : Fin k → ℝ) ↦ ∏ i, gaussianPDFReal 0 v.1 (x i)) v₀
      ((gammaMeasure ((k : ℝ) / 2) (1 / 2)).real (Set.Ioi (c / (v₀.1 : ℝ))))
      (ClassicalLean.Statistics.thresholdTest (fun x ↦ ∑ i, x i ^ 2) c 0) := by …
```

### Bridge 171: `ClassicalLean/Analysis/EigenvalueSubgradient.lean`, `ClassicalLean.Analysis.EigenvalueSubgradient.min_sub_le_of_subgradient_eigenvalues`

```lean
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
      (‖x 0 - z‖ ^ 2 + η ^ 2 * G ^ 2 * T) / (2 * η * T) := by …
```

## Verdicts (cold review, `incoming/reviews/review-1.md`) and witnesses

| bridge | main theorem | verdict | witness | what moves |
|---|---|---|---|---|
| 170 | `rank_mul_pinv_eq` | FAITHFUL | none (no hypothesis) | — |
| 172 | `pinv_categoricalCov` | FAITHFUL | `ι = Fin 3`, `p = (1/2, 1/3, 1/6)`; OK | `p` is not uniform, so `diagonal (1/p) = diag (2, 3, 6)` is not a multiple of `1` and `P` matters |
| 168 | `exists_multipliers_isMinOn_iff` | FAITHFUL | `E = ℝ`, `f y = (y − 2)²/2`, `g 0 y = y − 1`, `g 1 y = −y − 5`, Slater point `0`, `xbar = 1`; OK | the active constraint's multiplier is `1`, not `0` (the unconstrained minimiser `2` is infeasible); `g 1` is slack |
| 169 | `isUniformlyMostPowerful_sum_sq_gaussian` | FAITHFUL | `k = 2`, `v₀ = 1`, `c = 3`; OK | the densities change with `v` (`1/(2πv)` at `x = 0`); the level `e^(−3/2) ≈ 0.223` is strictly inside `(0, 1)` |
| 171 | `min_sub_le_of_subgradient_eigenvalues` | FAITHFUL | plane, `A₀ = diag(1,0)`, `A 0 = diag(1,−1)`, `A 1 = diag(0,1)`, `η = 1/2`, `G = 2`, `T = 3`, `z = 0`, iterates by an inline `Nat.rec` from `(3/4, 0)`; OK | iterates `(3/4,0)`, `(1/4,0)`, `(−1/4,0)`, `(−3/4,0)`, top eigenvector `e₀` and `g = (1,0)` at each step, never tied |

The recursion of 171 could be stated inline: `hstep` holds by `rfl`, and no closed form was needed.
`hg` is proved for every unit vector, so no eigenvector is computed.

## The cold review and its fixes

One fresh subagent reviewed a brief built by script (`review/brief.md`, sha256 `79d5ce77…`). The
brief's first version mis-cut `pinv`'s docstring and two docstring lines; it was fixed and rebuilt
before sending. Result: **FINDINGS 2, both MINOR**. Every statement is FAITHFUL and every witness
PASS.

1. 171's witness docstring now states `u = e₀`, `g = (1, 0)` and the move `(−1/2, 0)` at each step.
2. 169's witness docstring now says what moves and gives the level `e^(−3/2) ≈ 0.223`.

Neither fix changed a statement or a witness's arguments, so there was no second pass. The review
was committed as `24c0ef5` before any proof was written. The fixes landed in the modules' commits.

## Probes: names found unknown

* **`HasGradientAt.add`, named by the order, is not in Mathlib.** Bridge 168 builds the
  Lagrangian's derivative with `hasGradientAt_iff_hasFDerivAt`, `HasFDerivAt.add`,
  `HasFDerivAt.sum` and `HasFDerivAt.const_mul`. Every other name the order cites is known
  (`probe170.out` … `probe171.out`).
* The session's own names that were unknown, and what was used instead:
  * `HasGradientAt.sum`, `HasGradientAt.const_smul`: the `HasFDerivAt` forms.
  * `Matrix.transpose_diagonal`: it is `Matrix.diagonal_transpose`.
  * `MeasureTheory.lintegral_fintype_prod_eq_prod`: none; the Bochner `integral_fintype_prod_eq_prod`
    was used.
  * `MeasureTheory.integral_withDensity_eq_integral_toReal_smul`: the root name.
  * `MeasureTheory.Measure.volume_pi`: it is `MeasureTheory.volume_pi`.
  * `Set.indicator_pi`, `Finset.prod_indicator`, `Measure.IsProbabilityMeasure`: not needed.
  * `Matrix.isHermitian_iff_isSymmetric`: outside the imports, not needed.
  * `Matrix.toEuclideanLin_apply`, `Matrix.piLp_equiv_toEuclideanLin`: `Matrix.toEuclideanLin`
    was unfolded instead.
  * `OrthonormalBasis.span_eq`, `Basis.span_eq`: `Module.Basis.span_eq`.
  * `LinearMap.coeFn_sum`: `LinearMap.sum_apply`.

  See round 82.

## Starting gates (Setup 3, clean tree at `d723fbf`)

* `lake build`: 4206 jobs, 0 warnings (`setup3_lake_build.txt`).
* AxiomGate: PASS 3914 (`setup3_axiom.txt`).
* check_sorry: PASS 153 (`setup3_sorry.txt`).
* check_records: PASS 153 (`setup3_records.txt`).
* VacuityGate: PASS, 1 reviewed helper (`setup3_vacuity.txt`).

All as predicted.

One slip: the draft of `HatMatrixRank.lean` sat in the tree for about a minute while the starting
build ran. It was imported by nothing, and it was moved out before the other gates ran. Round 82
says so.

## End checks

**End check 1**, clean tree at `715f99b`, predictions written first (`expected.txt`, sha256
`fd9956b3…`):

| command | expected | observed |
|---|---|---|
| `lake build` | 4211 jobs, 0 warnings | 4211 jobs, 0 warnings (`ec1_build.txt`) |
| AxiomGate | PASS 3931 (3914 + 17) | PASS 3931 (`ec1_axiom.txt`) |
| check_sorry | PASS 158 | PASS 158 (`ec1_sorry.txt`) |
| check_records | PASS 158 | PASS 158 (`ec1_records.txt`) |
| VacuityGate | PASS, 1 reviewed helper | PASS, 1 reviewed helper (`ec1_vacuity.txt`) |
| witness gate, five modules | OK=4, copy-error=0 | OK=4, copy-error=0, no other verdict (`ec1_witness.txt`) |
| rules drift | PASS | PASS no drift (`ec1_drift.txt`) |

The theorem-constant census (`count/census_all.txt`) gives 2 (HatMatrixRank), 2
(CategoricalPseudoinverse), 1 (KKTMultipliers), 11 (ChiSquaredTest) and 1 (EigenvalueSubgradient),
17 in all. The closure went from 6546 to 6551 modules (`count/closure_base.txt`,
`count/closure_after.txt`): +5 `ClassicalLean`, Mathlib unchanged.

**End check 2** was not run here: gate 7, the banned-vocabulary scan, the whole-library witness
gate, the bridge search and the report tool run on DSMain at MERGE-6.

**End check 3** (`ec3.txt`):
* The forbidden-word grep and the `(config :=` grep on the five files find nothing.
* The diff from `d723fbf` touches only the five modules, `ClassicalLean.lean` (five import lines),
  `records/` and `incoming/`.
* `records/` has only the `A` and `M` lines expected.
* INDEX and CLAIMS have only `+` lines, at their ends.

**End check 4**: round 82 completed, CLAIMS closed, INDEX set, check_records PASS 158
(`ec4_records.txt`), pushed as `09ab276`.

## Not closed or narrowed

Nothing. Every bridge was closed well inside its two hours (start times `start*.txt`). Each first
build's warnings were fixed without changing a statement:
* 172: two `if_neg` deprecations;
* 168: four `ContinuousLinearMap.*_apply` deprecations;
* 169: one 101-character line (`build169_first.txt`).

The 172 and 168 warnings were seen in `lake env lean` runs whose output was not saved; this is a
miss under rule 9, said in round 82.

## Commits on `cloud-math-7`

| commit | content |
|---|---|
| `159e1b0` | records first |
| `24c0ef5` | the review |
| `c7bc0fd` | bridge 170 |
| `3541793` | bridge 172 |
| `e6d979c` | bridge 168 |
| `26f32ce` | bridge 169 |
| `715f99b` | bridge 171 |
| `09ab276` | records closed |

Then the commit carrying this report, which is the branch's last commit. A commit cannot cite its
own hash; it is given in the session's closing message.
