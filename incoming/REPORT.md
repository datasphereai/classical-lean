# Report: order CLOUD-MATH-4 (three bridges as three new modules)

Claude Code cloud session `session_01HgueTamcgmkdp3A6C5qVW8`
(https://claude.ai/code/session_01HgueTamcgmkdp3A6C5qVW8). Branch `cloud-math-4`, from
`67d05bfbd0efa80f0de679813b54500ae8c69122` (`origin/cloud-math-4` was checked equal to it before any
change). Records: `records/rounds/20261028T201747Z__round-77-huffman-entropy-principal-components-james-stein-risk.md`.
Evidence: `$HOME/cm4/` in the session's container (outside the repository); the files named below are
there, and their sha256s are in `setup_sha256.txt` and `end_sha256.txt`.

## Outcome

All three bridges are closed: none narrowed, none undone. Each was stated and proved by this session
from its row's sketch; there were no drafts.

| bridge | module | commit |
|---|---|---|
| 160 | `ClassicalLean/InformationTheory/HuffmanEntropy.lean` | `87de121` |
| 162 | `ClassicalLean/Probability/PrincipalComponents.lean` | `51b2ed9` |
| 161 | `ClassicalLean/Statistics/JamesSteinRisk.lean` | `f1d30dd` |

Other commits: `068ffe3` (records first), `5c76118` (the review), `a065e72` (round 77 completed,
CLAIMS closed, INDEX set), and this report's own commit, which is the branch's last.

`git ls-remote origin master`: `67d05bfbd0efa80f0de679813b54500ae8c69122` at the start
(`master_start.txt`) and at the end (`master_end.txt`). Nothing was pushed to `master`, no pull
request was opened, and no force-push was made.

## Final statements (copied from the modules by script)

```lean
theorem le_sum_mul_huffmanLength {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    shannonEntropy p / Real.log 2 ≤ ∑ i, p i * (huffmanLength p i : ℝ) := by
```

```lean
theorem sum_mul_huffmanLength_lt {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → ℝ}
    (hp0 : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1) :
    ∑ i, p i * (huffmanLength p i : ℝ) < shannonEntropy p / Real.log 2 + 1 := by
```

```lean
theorem tendsto_powerIterate_covLin {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ] {X : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) {n : ℕ} (hn : Module.finrank ℝ (EuclideanSpace ℝ ι) = n)
    (h2 : 2 ≤ n)
    (hgap : (isSymmetric_covLin (X := X) (μ := μ)).eigenvalues hn ⟨1, h2⟩ <
      (isSymmetric_covLin (X := X) (μ := μ)).eigenvalues hn ⟨0, by omega⟩)
    (x : EuclideanSpace ℝ ι)
    (hx : inner ℝ ((isSymmetric_covLin (X := X) (μ := μ)).eigenvectorBasis hn ⟨0, by omega⟩) x
      ≠ 0) :
    (∃ C : ℝ, ∀ k : ℕ,
      ‖(inner ℝ ((isSymmetric_covLin (X := X) (μ := μ)).eigenvectorBasis hn ⟨0, by omega⟩)
            ((covLin X μ ^ k) x))⁻¹ • (covLin X μ ^ k) x
          - (isSymmetric_covLin (X := X) (μ := μ)).eigenvectorBasis hn ⟨0, by omega⟩‖
        ≤ C * ((isSymmetric_covLin (X := X) (μ := μ)).eigenvalues hn ⟨1, h2⟩ /
          (isSymmetric_covLin (X := X) (μ := μ)).eigenvalues hn ⟨0, by omega⟩) ^ k) ∧
    Tendsto (fun k : ℕ =>
        (inner ℝ ((isSymmetric_covLin (X := X) (μ := μ)).eigenvectorBasis hn ⟨0, by omega⟩)
          ((covLin X μ ^ k) x))⁻¹ • (covLin X μ ^ k) x) atTop
      (𝓝 ((isSymmetric_covLin (X := X) (μ := μ)).eigenvectorBasis hn ⟨0, by omega⟩)) := by
```

```lean
theorem variance_mix_eigenvectorBasis_eq_and_le {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ] {X : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) {n : ℕ} (hn : Module.finrank ℝ (EuclideanSpace ℝ ι) = n)
    (h0 : 0 < n) :
    variance (mix X (WithLp.ofLp
        ((isSymmetric_covLin (X := X) (μ := μ)).eigenvectorBasis hn ⟨0, h0⟩))) μ =
        (isSymmetric_covLin (X := X) (μ := μ)).eigenvalues hn ⟨0, h0⟩ ∧
      ∀ w : EuclideanSpace ℝ ι, ‖w‖ = 1 →
        variance (mix X (WithLp.ofLp w)) μ ≤
          (isSymmetric_covLin (X := X) (μ := μ)).eigenvalues hn ⟨0, h0⟩ := by
```

```lean
theorem integral_inv_sqNorm_zero {d : ℕ} (hd : 3 ≤ d) :
    ∫ x, (sqNorm x)⁻¹ ∂normalVec d 0 = 1 / ((d : ℝ) - 2) := by
```

```lean
theorem integral_sqNorm_jamesStein_zero {d : ℕ} (hd : 3 ≤ d) :
    ∫ x, sqNorm (jamesStein x) ∂normalVec d 0 = 2 := by
```

## Verdicts (review-1)

* `le_sum_mul_huffmanLength`: FAITHFUL to the order's table. GENERALIZED against its row: the row
  asks `p i > 0`, and the order's table asks only `p i ≥ 0` for this side.
* `sum_mul_huffmanLength_lt`: FAITHFUL.
* `tendsto_powerIterate_covLin`: FAITHFUL.
* `variance_mix_eigenvectorBasis_eq_and_le`: FAITHFUL.
* `integral_inv_sqNorm_zero`: FAITHFUL.
* `integral_sqNorm_jamesStein_zero`: FAITHFUL.

Choices Lean forced, each stated in its docstring:

* the lengths are cast `ℕ → ℝ`;
* 162's symmetry is the library's `isSymmetric_covLin`, which is `(isSelfAdjoint_covOp …).isSymmetric`, built inside the statement;
* the dimension is `n` with `hn`, and the indices are `⟨0, _⟩` and `⟨1, _⟩` in Mathlib's largest-first order, with `2 ≤ n` and `0 < n` as the hypotheses that let them be written;
* 161's mean is `θ = 0`, with the `- 0` dropped, and `d` is cast in `1 / ((d : ℝ) - 2)`.

## Witnesses (six; all OK in the witness gate and PASS in the review)

* **160, both theorems.**
  * Setup: `ι = Fin 3`, `p = (1/2, 1/3, 1/6)`.
  * What moves: both bounds are strict. The entropy is ≈ 1.459 bits, Huffman's mean length is 3/2, and one bit more is ≈ 2.459.
* **162, `tendsto_powerIterate_covLin`.**
  * Setup: two fair coins, `μ = (1/4 : ℝ≥0) • count` on `Fin 2 → Bool`, `X = (±2, ±1)`. The covariance map is `diag(4, 1)`, computed inside the block, and `x = (1, 1)`.
  * What moves: `λ₁ = 1 ≠ 0`, so the iterates never reach `u`, and the rate 1/4 is not 0.
* **162, `variance_mix_eigenvectorBasis_eq_and_le`.**
  * Setup: the same data, with `n = 2`.
  * What moves: the variances 4 and 1 are distinct, so the largest is a strict maximum.
* **161, both theorems.**
  * Setup: `d = 4`.
  * What moves: this is away from the least dimension 3 and from the boundary `d = 2`. The inverse moment is 1/2, and the risk is 2 against `X`'s 4.

## Probes that found a name unknown (Setup 4; `probe160.out`, `probe161.out`, `probe162.out`, then `probe161b.out`, `probe162b.out`)

* `MeasureTheory.integral_withDensity_eq_integral_toReal_smul` (and `…_smul`): the lemma is in the root namespace, as `integral_withDensity_eq_integral_toReal_smul`.
* `ContinuousLinearMap.IsSelfAdjoint.isSymmetric`: the name is `IsSelfAdjoint.isSymmetric`.
* `Equiv.piFinTwo`: the names are `finTwoArrowEquiv` and `piFinTwoEquiv`.
* The instance `IsFiniteMeasure ((4⁻¹ : ℝ≥0∞) • Measure.count : Measure (Fin 2 → Bool))` fails to synthesize. `(4⁻¹ : ℝ≥0) • Measure.count` works, so 162's witnesses use it, as the order allows.

No unknown name was used.

## The review and its fixes

There was one cold review, `incoming/reviews/review-1.md`, by a fresh subagent. It was given a brief built by script, `$HOME/cm4/review/brief.md`, with sha256 `1767e9bd…`. Its result was FINDINGS 2, both MINOR:

1. A HuffmanEntropy docstring credited the `p i ≥ 0` widening to the session's reading. The order's table asks for it, and the sentence now says so.
2. PrincipalComponents' top-level `open scoped NNReal` served only the witnesses. It is now an `open scoped NNReal in` line above each witness.

Neither fix changed a statement or a witness's arguments, so there was no second pass.

Changes after the review, all for the linter:

* The tactic steps inside 162's witness blocks: `show` became `change`, and a non-terminal `simp` became the `simp only` list that `simp?` gave.
* Long docstring lines in all three modules were re-wrapped.

No witness argument changed, no docstring's words changed, and the witness gate passes on the final files.

## End checks

End check 1 ran on the clean tree at `f1d30dd`. The predictions were written first, in `expected.txt` (sha256 `6f6621db…`).

| check | expected | observed |
|---|---|---|
| `lake build` | 4196 jobs (4193 + 3 modules; closure 5729 → 5732, so no new Mathlib module), 0 warnings | 4196 jobs, 0 warnings (`ec1_build.txt`) |
| AxiomGate | PASS 3683 (3666 + 3 + 4 + 10, `census_*.txt`) | PASS 3683 (`ec1_axiom.txt`) |
| check_sorry | PASS 143 | PASS 143 (`ec1_sorry.txt`) |
| check_records | PASS 143 | PASS 143, 1 exemption (`ec1_records.txt`; again after the records commit, `ec4_records.txt`) |
| VacuityGate | PASS, 1 reviewed helper (no HELPER line added) | PASS, 1 reviewed helper (`ec1_vacuity.txt`) |
| witness gate, three modules | OK=6, copy-error=0 | OK=6, copy-error=0, PASS (`ec1_witness.txt`) |
| rules drift | PASS | PASS no drift (`ec1_drift.txt`) |

* **End check 2.** Not run here; these checks run on DSMain at MERGE-4: gate 7, the banned-vocabulary scan, the whole-library witness gate, the bridge search and the report tool.
* **End check 3** (`ec3.txt`). Both forbidden-word greps found nothing. `git diff --name-only 67d05bf HEAD` lists only the three modules, `ClassicalLean.lean`, `records/` and `incoming/`. In `ClassicalLean.lean`, the diff is only the three added import lines.
* **End check 4.** Round 77 is completed with the commit hashes and counts, CLAIMS is closed, INDEX is set, and check_records passes (`a065e72`).

## Not closed, narrowed, or missed

* Not closed: none.
* Narrowed: none.
* One miss (rule 9): each bridge's first linted build wrote its output to the same file as its clean re-run, so the first runs' warning counts (4, 13 and 1, all from line length, `show`/`simp` style or a docstring) are not in a saved output.
