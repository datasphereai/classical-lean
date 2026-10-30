# Report — order CLOUD-MATH-5 (five bridges as five new modules)

Claude Code cloud session `session_01HgueTYMESHnLVKHDy4XkAM`
(https://claude.ai/code/session_01HgueTYMESHnLVKHDy4XkAM), branch `cloud-math-5` of GitHub
`datasphereai/classical-lean`, from `8631a8d3c4316d85c78df697436b0245fa24cf1b`. Every count below
is read from a saved output in `$HOME/cm5/` (outside the repository) and cited by file name. The
full record is round 79,
`records/rounds/20261030T211530Z__round-79-holm-correlation-pinsker-heun-richardson-euler-maclaurin.md`.

## Summary

All five bridges are closed: 158, 155, 164, 166 and 167, each a new module, statements and proofs
by this session from the rows' sketches (no drafts). Nothing narrowed, nothing undone, no helper
listed in `tools/vacuity_reviewed.txt`. One cold review, PASS WITH FINDINGS (7, all MINOR), every
finding fixed, no second pass needed. Every End check 1 command as expected.

## `master`, start and end

* `git ls-remote origin master` at the start: `8631a8d3c4316d85c78df697436b0245fa24cf1b`
  (`start-refs.txt`); `origin/cloud-math-5` was the same commit, as the order requires.
* at the end: `8631a8d3c4316d85c78df697436b0245fa24cf1b` (`end-master.txt`). `master` was not
  touched; no pull request was opened, nothing merged, nothing force-pushed.

## Setup

* `curl -sSI https://cache.mathlib.org/ | head -3`: `HTTP/1.1 200 Connection Established` (the
  proxy's tunnel), then `HTTP/2 404` from the cache server itself, not a stop (`curl-cache.txt`).
  `lake exe cache get` downloaded and decompressed 8908 files (`cache-get.txt`). Toolchain
  `leanprover/lean4:v4.34.0` installed by elan from GitHub.
* Starting gates at `8631a8d`, each as the order predicted: build 4196 jobs, 0 warnings
  (`start-lake-build.txt`); AxiomGate PASS 3844 (`start-axiom.txt`); check_sorry PASS 143
  (`start-sorry.txt`); check_records PASS 143, 1 exemption (`start-records.txt`); VacuityGate PASS,
  1 reviewed helper (`start-vacuity.txt`); hashes in `start_sha256.txt`.

## Probes: names not found as written (Setup 4)

Every name the order cites was found (`probes/probe158.out` … `probe167.out`). Not found:

* `Finset.filter_card_add_filter_neg_card_eq_card` (a name this session would have used): unknown
  at v4.34.0; Mathlib's name is `Finset.card_filter_add_card_filter_not` (`probes/probe158b.out`).
  Used under that name.
* the instance `IsProbabilityMeasure ((4⁻¹ : ℝ≥0) • Measure.count : Measure (Fin 2 → Bool))`: not
  synthesized (`probes/probe155.out`). The theorems of 155 name their instance binder `hμ`, and
  both witnesses supply `(hμ := ⟨…⟩)`, proved in the block (`probes/probe155c.out`).

## The final statements

#### Bridge 158: `ClassicalLean/Probability/HolmInsideStepUp.lean`

```lean
theorem le_mul_numRej_div_of_holmRejected {ι : Type*} [Fintype ι] {q : ℝ} (hq : 0 ≤ q)
    {x : ι → ℝ} {i : ι} (h : holmRejected q x i) :
    x i ≤ q * numRej q x / Fintype.card ι
```

#### Bridge 155: `ClassicalLean/Probability/CorrelationBound.lean`

```lean
variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [hμ : IsProbabilityMeasure μ]
  {X Y : Ω → ℝ}
theorem covariance_sq_le_variance_mul (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    cov[X, Y; μ] ^ 2 ≤ variance X μ * variance Y μ
theorem abs_correlation_le_one (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    |correlation X Y μ| ≤ 1
```

#### Bridge 164: `ClassicalLean/Statistics/PinskerTest.lean`

```lean
theorem size_add_one_sub_power_ge_pinsker {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    {p₀ p₁ φ : ι → ℝ} (hp₀ : ∀ i, 0 ≤ p₀ i) (hp₀1 : ∑ i, p₀ i = 1)
    (hp₁ : ∀ i, 0 ≤ p₁ i) (hp₁1 : ∑ i, p₁ i = 1) (hsupp : ∀ i, p₀ i = 0 → p₁ i = 0)
    (hφ : IsTest φ) :
    1 - Real.sqrt (relEntropy p₁ p₀ / 2) ≤ ∑ i, φ i * p₀ i + (1 - ∑ i, φ i * p₁ i)
```

#### Bridge 166: `ClassicalLean/Analysis/HeunRichardson.lean`

```lean
theorem heunIterate_eq_add_sum (g : ℝ → ℝ) (a h y₀ : ℝ) (n : ℕ) :
    heunIterate (fun t _ ↦ g t) a h y₀ n =
      y₀ + h / 2 * ∑ k ∈ range n, (g (a + k * h) + g (a + k * h + h))
theorem heunIterate_add_eq_trapezoidal (g : ℝ → ℝ) (a b y₀ : ℝ) (N : ℕ) :
    heunIterate (fun t _ ↦ g t) a ((b - a) / N) y₀ N = y₀ + trapezoidal_integral g N a b
theorem richardson_heunIterate_eq_simpson (g : ℝ → ℝ) (a b y₀ : ℝ) (N : ℕ) :
    (4 * heunIterate (fun t _ ↦ g t) a ((b - a) / (2 * (N : ℝ))) y₀ (2 * N) -
        heunIterate (fun t _ ↦ g t) a ((b - a) / N) y₀ N) / 3 = y₀ + simpson g N a b
theorem abs_sub_richardson_heunIterate_le {g g₁ g₂ g₃ g₄ : ℝ → ℝ} {a b M y₀ : ℝ} (hab : a ≤ b)
    {N : ℕ} (hN : 0 < N)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt g (g₁ x) (Icc a b) x)
    (hf₁ : ∀ x ∈ Icc a b, HasDerivWithinAt g₁ (g₂ x) (Icc a b) x)
    (hf₂ : ∀ x ∈ Icc a b, HasDerivWithinAt g₂ (g₃ x) (Icc a b) x)
    (hf₃ : ∀ x ∈ Icc a b, HasDerivWithinAt g₃ (g₄ x) (Icc a b) x)
    (hM : ∀ x ∈ Icc a b, |g₄ x| ≤ M) :
    |(y₀ + ∫ x in a..b, g x) -
        (4 * heunIterate (fun t _ ↦ g t) a ((b - a) / (2 * (N : ℝ))) y₀ (2 * N) -
          heunIterate (fun t _ ↦ g t) a ((b - a) / N) y₀ N) / 3| ≤
      (b - a) * ((b - a) / (2 * N)) ^ 4 * M / 180
```

#### Bridge 167: `ClassicalLean/Analysis/HeunEulerMaclaurin.lean`

```lean
theorem heunIterate_one_eq_add_sum_sub {g : ℝ → ℝ} {a b : ℤ} {y₀ : ℝ} (hab : a ≤ b) :
    heunIterate (fun t _ ↦ g t) (a : ℝ) 1 y₀ (b - a).toNat =
      y₀ + ∑ k ∈ Finset.Icc a b, g k - (g a + g b) / 2
theorem sub_heunIterate_eq_eulerMaclaurin {g g' g'' : ℝ → ℝ} {a b : ℤ} {y₀ : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn g (Icc (a : ℝ) b))
    (hf' : ∀ t ∈ Ioo (a : ℝ) b, HasDerivAt g (g' t) t)
    (hf'c : ContinuousOn g' (Icc (a : ℝ) b))
    (hf'' : ∀ t ∈ Ioo (a : ℝ) b, HasDerivAt g' (g'' t) t)
    (hint : IntervalIntegrable g'' volume (a : ℝ) b) :
    (y₀ + ∫ t in (a : ℝ)..b, g t) - heunIterate (fun t _ ↦ g t) (a : ℝ) 1 y₀ (b - a).toNat =
      -(g' b - g' a) / 12 + ∫ t in (a : ℝ)..b, bernoulliFun 2 (Int.fract t) / 2 * g'' t
```

`heunIterate_eq_add_sum` (166) is a helper, used for theorem 1; it has no hypothesis, so no witness
and no vacuity entry (the gate did not flag it).

## Verdicts (review-1) and choices

| bridge | theorem | verdict |
|---|---|---|
| 158 | `le_mul_numRej_div_of_holmRejected` | FAITHFUL |
| 155 | `covariance_sq_le_variance_mul`, `abs_correlation_le_one` | FAITHFUL (probability measure, not widened) |
| 164 | `size_add_one_sub_power_ge_pinsker` | FAITHFUL (binders and hypotheses exactly those of `size_add_one_sub_power_ge`) |
| 166 | `heunIterate_add_eq_trapezoidal`, `richardson_heunIterate_eq_simpson` | FAITHFUL to the table; GENERALIZED against the row (every `N`, the row's `N ≥ 1` dropped, as the table asks) |
| 166 | `abs_sub_richardson_heunIterate_le` | FAITHFUL |
| 167 | `heunIterate_one_eq_add_sum_sub`, `sub_heunIterate_eq_eulerMaclaurin` | FAITHFUL |

Choices said in the docstrings: 158 writes the step-up rejection as StepUpProcedure does
(`q * numRej q x / Fintype.card ι`); 155's correlation is `0` when the root is `0` (Lean's
`x / 0 = 0`); 166 and 167 state the row's `y b` as `y₀ + ∫ₐᵇ g` with no solution `y`; 166 writes the
`2N` run's step `(b - a) / (2 * (N : ℝ))`; 167 counts steps as `(b - a).toNat`, starts at the cast
`(a : ℝ)` and sums over `Finset.Icc a b` in `ℤ`, and its `a ≤ b` is needed (for `a > b` the
iterate is `y₀` but the right side is `y₀ − (g a + g b)/2`). No narrowing.

## Witnesses (seven; all OK in the witness gate, all passed by the review)

| theorem | witness | what moves |
|---|---|---|
| `le_mul_numRej_div_of_holmRejected` | `Fin 3`, `x = (1/100, 1/50, 9/10)`, `q = 1/10`, `i = 1` | Holm rejects a p-value that is not the smallest, using both steps; `numRej = 2`; the conclusion `1/50 ≤ 2/30` is strict |
| `covariance_sq_le_variance_mul` | two fair coins, `μ = (4⁻¹ : ℝ≥0) • count`, `X = ±1`, `Y = X ± 1` | `cov = Var X = 1`, `Var Y = 2`: `1 ≤ 2` strict; neither constant, neither independent nor proportional |
| `abs_correlation_le_one` | the same | correlation `1/√2`, strictly inside `(−1, 1)`, nonzero root |
| `size_add_one_sub_power_ge_pinsker` | `Fin 3`, `p₀ = (1/2, 1/2, 0)`, `p₁ = (1/4, 3/4, 0)`, `φ = (0, 1, 0)` | `D ≈ 0.131 > 0`, bound `≈ 0.744 < 3/4`; test not constant; third cell exercises `hsupp` |
| `abs_sub_richardson_heunIterate_le` | `x ^ 4` on `[0, 1]`, `N = 2`, `M = 24`, `y₀ = 1` | both runs move at every step; `g⁗ ≠ 0`; bound `1/1920 > 0` (attained) |
| `heunIterate_one_eq_add_sum_sub` | `a = 0`, `b = 3`, `x ^ 2`, `y₀ = 1` | increments `1/2`, `5/2`, `13/2`, to `21/2` |
| `sub_heunIterate_eq_eulerMaclaurin` | `x ^ 4` on `[0, 2]`, `y₀ = 1` | increments `1/2`, `17/2`; remainder `1/15 ≠ 0` |

## The review and its fixes

`incoming/reviews/review-1.md` (one fresh subagent; brief built by script, `review/brief.md`, sha256
`cc678ae580087b33d7049b9f2c69a262886f2419ea5b6eada346bebb1bf45572`): PASS WITH FINDINGS (7), all
MINOR. (1) six docstring lines over 100 characters, re-wrapped with no word changed; (2)
`linter.flexible` in CorrelationBound's two `hμ` proofs, now `simp only`; (3) a garbled sum in
HeunRichardson's helper docstring; (4) misplaced backticks in HeunRichardson's proof sketch; (5) and
(6) the witness docstrings of HeunRichardson and of HeunEulerMaclaurin's theorem 2 now say the
iterates move; (7) a stray line break in a CorrelationBound docstring. No fix changed a statement or
a witness's arguments, so no second pass.

## End checks

End check 1, on the clean tree at `90898da`, predictions written first (`expected.txt`, sha256
`ad7ca6ae0d41d34f602a9df564eb9ad49ae41ae58fe37269694be53e3c51ab4d`):

| command | expected | observed |
|---|---|---|
| `lake build` | 4201 jobs, 0 warnings | 4201 jobs, 0 `warning:` lines (`ec1_build.txt`) |
| AxiomGate | PASS 3862 (3844 + 18) | PASS 3862, 0 scoped exceptions (`ec1_axiom.txt`) |
| check_sorry | PASS 148 | PASS 148 (`ec1_sorry.txt`) |
| check_records | PASS 148, 1 exemption | the same (`ec1_records.txt`) |
| VacuityGate | PASS, 1 reviewed helper | the same (`ec1_vacuity.txt`) |
| witness gate, five modules | PASS, OK=7, copy-error=0 | the same, every other verdict 0 (`ec1_witness.txt`) |
| rules drift | PASS no drift | PASS no drift (`ec1_drift.txt`) |

The 18 theorem constants: HolmInsideStepUp 6, CorrelationBound 2, PinskerTest 1, HeunRichardson 5,
HeunEulerMaclaurin 4 (`count/census.txt`, `env.getModuleFor?` under the axiom gate's predicate).
Import closure 5732 → 5737, the five new modules only, no new Mathlib module
(`count/closure_base.txt`, `count/closure_after.txt`).

End check 2: not run here (gate 7, the banned-vocabulary scan, the whole-library witness gate, the
bridge search and the report tool run on DSMain at MERGE-5).

End check 3 (`ec3.txt`): both greps find nothing; `git diff --name-only 8631a8d HEAD` lists only the
five modules, `ClassicalLean.lean`, `records/` and `incoming/`; `ClassicalLean.lean` gains only the
five import lines; `records/` has only `A` (order copy, round 79) and `M` (INDEX, CLAIMS), each `M`
one `+` line at the end of its file.

End check 4: round 79 completed, CLAIMS row closed, INDEX row set, check_records PASS 148
(`ec4_records.txt`), pushed as `e8a35fb`.

## Commits on `cloud-math-5`

`1eb5209` records first; `266dd79` review; `1a9e0cc` bridge 158; `3d2f4cc` bridge 155; `c1762fd`
bridge 164; `6c18194` bridge 166; `90898da` bridge 167; `e8a35fb` round 79 completed, CLAIMS
closed, INDEX set; then the commit that adds this report, which is the branch's last commit (a
commit cannot cite its own hash; `git log -1 origin/cloud-math-5` gives it).

## Not closed or narrowed

None.
