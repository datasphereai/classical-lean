# Order CLOUD-MATH-6 — report

Claude Code cloud session `session_01HgueTbGvJvmksxSgWGMRPt`
(https://claude.ai/code/session_01HgueTbGvJvmksxSgWGMRPt), branch `cloud-math-6` from `8631a8d`.
Every count below is read from a saved output in `$HOME/cm6/` (in the session's container, outside
the repository), cited by file name; round 80
(`records/rounds/20261030T212346Z__round-80-urn-ville-ruin-conditional-divisibility-chain-kolmogorov-smirnov.md`)
has the full record.

* `git ls-remote origin master` at the start: `8631a8d3c4316d85c78df697436b0245fa24cf1b`
  (`start-git.txt`); at the end: the same (`end-master.txt`). `master` was not touched; no pull
  request was opened.
* Last commit before this report: `8df765b` (records). This report is the commit after it.

All five bridges are **closed**: none narrowed, none undone.

## The bridges

### 157 — `ClassicalLean/Probability/UrnVille.lean` (`1861efb`)

```lean
theorem measureReal_exists_urnShare_ge_le {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (r b : ℕ) (hrb : 0 < r + b)
    (X : ℕ → Ω → ℝ) (hX01 : ∀ n ω, X n ω = 0 ∨ X n ω = 1)
    (hX_meas : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hX_cond : ∀ n, μ[X n | ℱ n] =ᵐ[μ] urnShare r b X n) {c : ℝ} (hc : 0 < c) :
    μ.real {ω | ∃ n, c ≤ urnShare r b X n ω} ≤ (r : ℝ) / (((r : ℝ) + b) * c)
```

Helpers (PolyaUrn's are private): `urnShare_mem_Icc` (`urnShare r b X n ω ∈ Set.Icc 0 1` when every
draw is `0` or `1`) and `urnRed_stronglyMeasurable` (`∀ n, StronglyMeasurable[ℱ n] (urnRed r X n)`).
Verdict: FAITHFUL. Witness: PolyaUrn's urn, `r = b = 1`, `c = 3/4`; moves: every draw random, the
share moves at every step, start `1/2 < 3/4`, bound `2/3 < 1`.

### 154 — `ClassicalLean/Probability/RuinConditional.lean` (`3c72bbe`)

```lean
theorem measureReal_exists_ge_le_of_condProb {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {𝒢 : Filtration ℕ m0} {X : ℕ → Ω → ℝ}
    (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n)) (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1)
    {p : ℝ} (hcond : ∀ n, μ[fun ω ↦ (X n ω + 1) / 2 | 𝒢 n] ≤ᵐ[μ] fun _ ↦ p)
    (hp0 : 0 < p) (hp : p ≤ 1 / 2) (a : ℕ) :
    μ.real {ω | ∃ n, (a : ℝ) ≤ walk X n ω} ≤ (p / (1 - p)) ^ a
```

Verdict: FAITHFUL. Witness: GamblersRuin's biased walk on `ℕ → Fin 3`, `p = 1/3`, `a = 2`; `hcond`
with equality through `condExp_indep_eq`; moves: every step `±1`, bound `1/4 < 1`.

### 156 — `ClassicalLean/Probability/RuinDivisibility.lean` (`f1fb5ad`)

```lean
theorem measureReal_hit_eq_inv_iff_dvd {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {𝒢 : Filtration ℕ m0} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ)
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) {r : ℕ} (hr : 0 < r)
    (hp : ∀ n, μ.real {ω | X n ω = 1} = 1 / ((r : ℝ) + 1)) (a b : ℕ) (hb : 0 < b) :
    (∃ m : ℕ, 0 < m ∧
        μ.real {ω | ∃ n, walk X n ω = a ∧ ∀ k ≤ n, -(b : ℝ) < walk X k ω} = 1 / m) ↔
      b ∣ a
```

Verdict: FAITHFUL. Witness: the same coins, `r = 2`, `a = 4`, `b = 2`; moves: `b > 1`, `a > b`,
chance `U 2 / U 6 = 3/63 = 1/21`.

### 165 — `ClassicalLean/Probability/RuinChain.lean` (`3fefc24`)

`ruinChain a b : Matrix (Fin (a + b + 1)) (Fin (a + b + 1)) ℝ` (a `noncomputable def`: stay at the
ends `0` and `a + b`, `1/2` down and `1/2` up inside), and, with `A = {0, Fin.last (a + b)}`:

```lean
theorem ruinChain_meanHitting_iff (a b : ℕ) (g : Fin (a + b + 1) → ℝ) :
    ((∀ i ∈ ({0, Fin.last (a + b)} : Finset (Fin (a + b + 1))), g i = 0) ∧
        ∀ i ∉ ({0, Fin.last (a + b)} : Finset (Fin (a + b + 1))),
          g i = 1 + ∑ j, ruinChain a b i j * g j) ↔
      g = fun i : Fin (a + b + 1) ↦ ((a : ℝ) + b - ((i : ℕ) : ℝ)) * ((i : ℕ) : ℝ)

theorem integral_exitTime_eq_meanHitting {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {𝒢 : Filtration ℕ m0} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ)
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) (hmean : ∀ n, ∫ ω, X n ω ∂μ = 0) (a b : ℕ)
    (g : Fin (a + b + 1) → ℝ)
    (hgA : ∀ i ∈ ({0, Fin.last (a + b)} : Finset (Fin (a + b + 1))), g i = 0)
    (hg : ∀ i ∉ ({0, Fin.last (a + b)} : Finset (Fin (a + b + 1))),
      g i = 1 + ∑ j, ruinChain a b i j * g j) :
    ∫ ω, ((exitTime X a b ω).untopA : ℝ) ∂μ = g ⟨b, by omega⟩
```

Helpers added by the review's fix: `sum_ruinChain`, `ruinChain_nonneg`, `exists_pow_ruinChain_pos`
(`meanHitting_eq`'s three hypotheses for the chain). Verdict (the two theorems together): FAITHFUL.
Witness (theorem 1): the fair walk on `ℕ → Bool`, `a = 2`, `b = 3`, `g = 0, 4, 6, 6, 4, 0`; moves:
every step `±1`, start index inside, `g 3 = 6 = a b`. Theorem 2 has no hypothesis, so no witness.

### 159 — `ClassicalLean/Probability/KolmogorovSmirnov.lean` (`2fd47ac`)

```lean
theorem measureReal_cdf_le_eq_of_map_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} (i : ℕ) (hX : Measurable (X i))
    (hlaw : μ.map (X i) = μ.map (X 0)) (hF : Continuous (cdf (μ.map (X 0)))) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    μ.real {ω | cdf (μ.map (X 0)) (X i ω) ≤ u} = u

theorem sup_abs_empiricalCDF_sub_eq_of_continuous {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, μ.map (X i) = μ.map (X 0)) (hF : Continuous (cdf (μ.map (X 0)))) :
    ∀ᵐ ω ∂μ, ∀ n, (⨆ x : ℝ, |empiricalCDF X n ω x - cdf (μ.map (X 0)) x|) =
      ⨆ u : Set.Icc (0 : ℝ) 1,
        |empiricalCDF (fun i ω ↦ cdf (μ.map (X 0)) (X i ω)) n ω u - u|
```

Verdicts: theorem 1 GENERALIZED (no pairwise independence, as the order asks); theorem 2 FAITHFUL
(its hypotheses at the one index `i`). The docstrings name "the law of the statistic does not depend
on `F`" as a consequence under mutual independence, not proved here. Witnesses: `Ω = ℝ`, standard
normal, `X i ω = ±ω` by parity; moves: `X (i + 1) ≠ X i` off `{0}`; theorem 2 at `i = 1` (`hlaw`
through `gaussianReal_map_neg`) and `u = 1/2`.

## Probes that found a name unknown (Setup 4, `probes/`)

* `ProbabilityTheory.condExp_indep_eq` → root `condExp_indep_eq` (`probe154.out`).
* `Finset.filter_card_add_filter_neg_card_eq_card` → `Finset.card_filter_add_card_filter_not`
  (`probe_extra154.out`; not used).
* `MeasureTheory.StronglyMeasurable.div_const` → not in Mathlib; `Measurable.div_const` used
  (`probe_extra154.out`).
* `MeasureTheory.measureReal_diff` → deprecated; `measureReal_sdiff` used (`probe_extra159.out`).
* During the proofs: `isProbabilityMeasure_map` / `Measure.isProbabilityMeasure_map` unknown; the
  pushforward's probability is an instance, so no name is needed.

Every name the order cites otherwise exists, and `SigmaFiniteFiltration μ 𝒢` is found as an
instance for a probability measure (`probe157.out`).

## The review and its fixes

One fresh subagent, brief built by script (`review/mkbrief.py`, `brief.md` sha256 `23a0c2a1…`),
report `incoming/reviews/review-1.md` (sha256 `06e44e8e…`): **FINDINGS 1, MINOR**. Bridge 165's
theorem 1 docstring leaned on a proof (that the chain meets `meanHitting_eq`'s hypotheses).
Fixed by stating them as `sum_ruinChain`, `ruinChain_nonneg` and `exists_pow_ruinChain_pos`,
used in theorem 2's proof and cited in the docstrings. No statement or witness argument changed, so
there was no second pass; the three helpers were not seen by the reviewer and passed the vacuity gate.

## End checks (clean tree at `2fd47ac`; predictions `expected.txt`, sha256 `b49850ac…`)

| check | expected | observed |
|---|---|---|
| `lake build` | 4201 jobs, 0 warnings | 4201 jobs, 0 warnings (`ec1_build.txt`) |
| AxiomGate | PASS 3896 (3844 + 52, `count/census.txt`) | PASS 3896 (`ec1_axiom.txt`) |
| check_sorry | PASS 148 | PASS 148 (`ec1_sorry.txt`) |
| check_records | PASS 148 | PASS 148 (`ec1_records.txt`; again after the records commit, `ec4_records.txt`) |
| VacuityGate | PASS, 1 reviewed helper | PASS, 1 reviewed helper (`ec1_vacuity.txt`) |
| witness gate, five modules | OK=6, copy-error=0 | OK=6, copy-error=0 (`ec1_witness.txt`) |
| rules drift | PASS | PASS no drift (`ec1_drift.txt`) |
| greps for forbidden words, `(config :=` | nothing | nothing (`ec3.txt`) |
| `git diff` against `8631a8d` | only the allowed paths, import lines, `+` lines | as expected (`ec3.txt`) |

The closure of the root's imports went from 5731 to 5736 modules, all five new ones in ClassicalLean
(`count/closure_base.txt`, `count/closure_after.txt`), so no new Mathlib module. Per-module theorem
constants: UrnVille 9, RuinConditional 1, RuinDivisibility 3, RuinChain 34, KolmogorovSmirnov 5.

Not run here (MERGE-5 on DSMain): gate 7, the banned-vocabulary scan, the whole-library witness
gate, the bridge search, the report tool.

## Misses

* Rule 9: each bridge's first linted build was overwritten by its clean re-run, so only the re-runs
  are saved; the first runs' warning counts (2, 0, 0, 0 and 1, all style, in docstrings or a
  proof line) were read from the terminal.
* Bridge 157's first root build failed: the import line had been appended after the root file's
  closing comment instead of at the end of its import block. It was corrected before any commit.

Nothing was narrowed and nothing is not closed.
