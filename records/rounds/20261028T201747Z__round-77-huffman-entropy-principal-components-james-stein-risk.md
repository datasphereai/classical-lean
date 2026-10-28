# Round 77 — Huffman's code within one bit of the entropy, principal components by power iteration, the James–Stein risk at the origin (order CLOUD-MATH-4)

Session: Claude Code cloud session `session_01HgueTamcgmkdp3A6C5qVW8`
(https://claude.ai/code/session_01HgueTamcgmkdp3A6C5qVW8), executing order `CLOUD-MATH-4`
(`records/orders/20261028T201746Z__claude-ai__order-cloudmath4-huffman-entropy-principal-components-james-stein-risk.md`),
bridge rows 160, 162 and 161 of `MATH-PLAN-library-2-bridges-2.md`, in a cloud container's clone of
GitHub `datasphereai/classical-lean` on branch `cloud-math-4`, from
`67d05bfbd0efa80f0de679813b54500ae8c69122` (checked equal to `origin/cloud-math-4` before any
change). `git ls-remote origin master` at the start: `67d05bfbd0efa80f0de679813b54500ae8c69122`
(`$HOME/cm4/master_start.txt`). Lean and Mathlib v4.34.0 (`lake exe cache get`, 8908 files).

**No drafts.** Each of the three bridges is stated and proved by this session from its row's sketch
in the order; no proof comes from an earlier draft.

Evidence: `$HOME/cm4/` (outside the repository); every count below is read from a saved output
there, cited by its file name (rule 9).

First part written before any Lean file changed; completed after the work, below.

## Modules this round adds (three new modules)

* bridge 160: `ClassicalLean/InformationTheory/HuffmanEntropy.lean`
  (`ClassicalLean.InformationTheory.HuffmanEntropy`), importing
  `ClassicalLean.InformationTheory.Huffman`;
* bridge 162: `ClassicalLean/Probability/PrincipalComponents.lean`
  (`ClassicalLean.Probability.PrincipalComponents`), importing
  `ClassicalLean.Probability.CovarianceDirections` and `ClassicalLean.Analysis.PowerMethod`;
* bridge 161: `ClassicalLean/Statistics/JamesSteinRisk.lean`
  (`ClassicalLean.Statistics.JamesSteinRisk`), importing `ClassicalLean.Statistics.JamesStein` and
  `ClassicalLean.Probability.ChiSquared`;
* `ClassicalLean.lean`: three import lines, at the end of its import block, in landing order, each
  added by its module's landing commit.

No existing module changes. `tools/vacuity_reviewed.txt` changes only if a helper is listed (the
order's rule 4). Nothing else under `tools/` changes.

## Starting counts (measured in this session, before any new module, clean tree at `67d05bf`)

* `lake build`: exit 0, `Build completed successfully (4193 jobs).`, 0 lines with `warning:`
  (`setup3_build.txt`).
* `lake env lean tools/AxiomGate.lean`: `axiom gate PASS — 3666 theorem constant(s) under
  [ClassicalLean] …; 0 scoped exceptions` (`setup3_axiom.txt`).
* `python3 -I tools/check_sorry.py`: PASS, 140 files (`setup3_sorry.txt`).
* `python3 -I tools/check_records.py`: PASS, 140 modules, 1 named exemption (`setup3_records.txt`).
* `lake env lean tools/VacuityGate.lean`: PASS, 1 reviewed helper, 0 VACUOUS-PENDING, rule 5 out of
  heartbeats on 0 theorems (`setup3_vacuity.txt`).
* sha256 of each output: `setup_sha256.txt`.

## Probes (Setup 4)

One file per new module, importing exactly its imports (`$HOME/cm4/probes/probe160.lean`,
`probe162.lean`, `probe161.lean`; outputs `probe160.out`, `probe162.out`, `probe161.out`). Four
names were unknown as written and were found under other names (`probe161b.out`, `probe162b.out`):

* `MeasureTheory.integral_withDensity_eq_integral_toReal_smul` (and the `_smul` form): the lemma is
  in the root namespace, `integral_withDensity_eq_integral_toReal_smul`.
* `ContinuousLinearMap.IsSelfAdjoint.isSymmetric`: the lemma is `IsSelfAdjoint.isSymmetric`
  (`(isSelfAdjoint_covOp …).isSymmetric`, which is CovarianceDirections' `isSymmetric_covLin`).
* `Equiv.piFinTwo`: Mathlib's names are `finTwoArrowEquiv` and `piFinTwoEquiv`.
* the instance `IsFiniteMeasure ((4⁻¹ : ℝ≥0∞) • Measure.count : Measure (Fin 2 → Bool))` does not
  synthesize; `(4⁻¹ : ℝ≥0) • Measure.count` does, so bridge 162's witness uses it, as the order
  allows.

## Statement stage and its cold review (rule 1, rule 5)

The three modules were written with every statement final, every proof `sorry` and every witness
complete, and each was elaborated with `lake env lean` with only `sorry` warnings (`stmt160.out`,
`stmt162.out`, `stmt161.out`). The brief for the review was built by script
(`$HOME/cm4/review/mkbrief.py`, which copies the order's table, rule 3 and bridge rows, HANDOFF.md's
"Satisfiability witnesses" paragraph, the statements the bridges rest on and the three modules;
`brief.md`, sha256 `1767e9bd96f1ec68fefc6f709a4af0832e923f64823f95179f91c683aa014539`). Its first
version cut definition bodies at `:=` and swept stray lines into the context extracts; the script
was fixed and the brief rebuilt before it was sent. One fresh subagent reviewed it:
`incoming/reviews/review-1.md` (sha256
`b423184f4f46b1d4eb763b0790497d5154d00ebf67dc98a3a07f365a75a47779`), **FINDINGS 2, both MINOR**:

1. HuffmanEntropy's module docstring credited the lower side's `p i ≥ 0` to "this session's
   reading"; the order's table asks for it. Fixed in that sentence.
2. PrincipalComponents' top-level `open scoped NNReal` served only the witnesses; it is now an
   `open scoped NNReal in` line above each witness's docstring.

Neither fix changed a statement or a witness's arguments, so no second pass (rule 5). Verdicts:
`le_sum_mul_huffmanLength` FAITHFUL to the order's table, GENERALIZED against its row (`p i ≥ 0`);
`sum_mul_huffmanLength_lt`, `tendsto_powerIterate_covLin`,
`variance_mix_eigenvectorBasis_eq_and_le`, `integral_inv_sqNorm_zero` and
`integral_sqNorm_jamesStein_zero` FAITHFUL. No theorem WEAKER; all six witnesses PASS.

## Proofs, by bridge (start times: `start160.txt`, `start162.txt`, `start161.txt`)

* **160** (from 2026-10-28 20:35:41 UTC): the lower side is `huffman_optimal (α := Bool)`'s code
  through `shannonEntropy_le_sum_mul_length_of_isPrefixFree`, divided by `log 2 > 0`; the upper side
  is its optimality against `exists_isPrefixFree_sum_mul_length_lt`'s code. The first build had
  four long-line warnings, all in docstrings; the lines were re-wrapped with no word changed, and
  the module then built with 0 warnings (`build160.txt`).
* **162** (from 20:44:07 UTC): every eigenvalue is a variance (`hasEigenvector_eigenvectorBasis`,
  `variance_mix_eq_of_hasEigenvector`, `variance_nonneg`), so `|λ i| = λ i` and the dominance
  follows from `eigenvalues_antitone`; `tendsto_powerIterate` at `⟨0, _⟩`, `⟨1, _⟩` then gives the
  first theorem. The second is `variance_mix_eq_of_hasEigenvector` at `u` and
  `ClassicalLean.MinMax.sum_re_inner_le_sum_eigenvalues` at `k = 1`. The first linted build had 13
  warnings, all in the witnesses' tactic steps and one docstring line: two `show` that changed the
  goal became `change`, and the non-terminal `simp … at e0 e1` (twice) became the `simp only` list
  that `simp?` gave. The witnesses' arguments and docstrings did not change. Then 0 warnings
  (`build162.txt`).
* **161** (from 20:53:54 UTC): the coordinates of `normalVec d 0` are independent standard normals
  (`iIndepFun_pi`, `measurePreserving_eval`), so `hasLaw_sum_sq_gaussian` gives `sqNorm` the law
  `gammaMeasure (d / 2) (1 / 2)`. `HasLaw.integral_comp` and
  `integral_withDensity_eq_integral_toReal_smul` turn the inverse moment into an integral against
  `gammaPDFReal` over `Ioi 0`. Then `Real.integral_rpow_mul_exp_neg_mul_Ioi` and
  `Real.Gamma_add_one` give `r / (a − 1) = 1 / (d − 2)`, and `integral_sqNorm_jamesStein_sub_eq` at
  `θ = 0` gives `2`. One long proof line was re-wrapped; then 0 warnings (`build161.txt`).

**Miss (rule 9):** each bridge's first linted build wrote to the same file as its re-run
(`build160.txt`, `build162.txt`, `build161.txt`), so the warning counts of the first runs (4, 13 and
1, read from the terminal at the time) are not in a saved output. Only the clean re-runs are saved.

No proof forced a statement to change: no narrowing (rule 7). Every bridge closed well inside its
two hours. No helper was flagged, so `tools/vacuity_reviewed.txt` is unchanged.

## Per bridge: the gates before each landing commit

| bridge | module build | witness gate | root build | vacuity gate |
|---|---|---|---|---|
| 160 | 0 warnings (`build160.txt`) | PASS, OK=2, copy-error=0 (`witness160.txt`) | 4194 jobs, 0 warnings (`rootbuild160.txt`) | PASS, 1 reviewed helper (`vacuity160.txt`) |
| 162 | 0 warnings (`build162.txt`) | PASS, OK=2, copy-error=0 (`witness162.txt`) | 4195 jobs, 0 warnings (`rootbuild162.txt`) | PASS, 1 reviewed helper (`vacuity162.txt`) |
| 161 | 0 warnings (`build161.txt`) | PASS, OK=2, copy-error=0 (`witness161.txt`) | 4196 jobs, 0 warnings (`rootbuild161.txt`) | PASS, 1 reviewed helper (`vacuity161.txt`) |

The vacuity gate prints a line for a theorem only when it flags one, so for the new theorems its
lines are none: its whole output each time is the summary line `vacuity gate PASS — no vacuous
theorems in [ClassicalLean] (1 reviewed helpers and 0 VACUOUS-PENDING on
tools/vacuity_reviewed.txt); rule 5 ran out of its 400000 heartbeats on 0 theorems`.

## Witnesses (six, each after its module's last line; all OK in the witness gate)

* `le_sum_mul_huffmanLength` and `sum_mul_huffmanLength_lt`: `ι = Fin 3`,
  `p = (1/2, 1/3, 1/6)`, positive, summing to `1`, not uniform and not all powers of `1/2`. What
  moves: both inequalities are strict. The entropy is about `1.459` bits, Huffman's lengths
  `(1, 2, 2)` have mean `3/2`, and one bit above the entropy is about `2.459`.
* `tendsto_powerIterate_covLin`: two fair coins, `μ = (1/4 : ℝ≥0) • count` on `Fin 2 → Bool`,
  `X 0 = ±2` and `X 1 = ±1` by the two flips, so the covariance map is `diag(4, 1)` (computed in the
  block). `n = 2`, `x = (1, 1)`. `hgap` is proved by showing that two equal eigenvalues would put
  both orthonormal eigenvectors on one axis. `hx` is proved by showing that any eigenvector of
  `diag(4, 1)` lies on an axis. What moves: `λ₁ = 1 ≠ 0`, so the iterates never reach `u` and the
  rate `1/4` is not `0`.
* `variance_mix_eigenvectorBasis_eq_and_le`: the same `X` and `μ`, `n = 2`. What moves: the two
  variances `4` and `1` are distinct, so the largest is a strict maximum.
* `integral_inv_sqNorm_zero` and `integral_sqNorm_jamesStein_zero`: `d = 4`, away from the
  theorems' least dimension `3` and from the boundary `d = 2`. The values are `1/2`, and the risk
  `2` against the risk `4` of `X`.

## The modules and their theorem-constant counts

Measured with `$HOME/cm4/count/census_<module>.lean`: the axiom gate's predicate (user name under
`ClassicalLean`, no macro scopes, `.thmInfo`), restricted to the constants that `env.getModuleFor?`
places in the module. Measured on the tree at `f1d30dd`, with all three modules landed and the tree
clean.

| module | bridge | theorem constants |
|---|---|---|
| `ClassicalLean/InformationTheory/HuffmanEntropy.lean` | 160 | 3: 2 written, plus `ClassicalLean.InformationTheory.Huffman.huffmanLength.congr_simp`, generated in this module (`census_HuffmanEntropy.txt`) |
| `ClassicalLean/Probability/PrincipalComponents.lean` | 162 | 4: 2 written, 2 `_proof_` (`census_PrincipalComponents.txt`) |
| `ClassicalLean/Statistics/JamesSteinRisk.lean` | 161 | 10: 2 written, 1 `_proof_`, 7 `_simp_` (`census_JamesSteinRisk.txt`) |
| **three modules** | | **17** |

3666 + 17 = 3683, the axiom gate's count below. The import closure went from 5729 to 5732 modules
(`ClassicalLean` from 141 to 144; `closure_base.txt`, `closure_after.txt`), so no new Mathlib
module, and the build has 4193 + 3 = 4196 jobs.

## End check 1 (clean tree at `f1d30dd`, predictions first: `expected.txt`, sha256 `6f6621db…`)

| command | expected | measured |
|---|---|---|
| `lake build` | 4196 jobs, 0 warnings | `Build completed successfully (4196 jobs).`, 0 `warning:` lines (`ec1_build.txt`) |
| `lake env lean tools/AxiomGate.lean` | PASS 3683 | PASS 3683, 0 scoped exceptions (`ec1_axiom.txt`) |
| `python3 -I tools/check_sorry.py` | PASS 143 | PASS 143 (`ec1_sorry.txt`) |
| `python3 -I tools/check_records.py` | PASS 143, 1 exemption | the same (`ec1_records.txt`) |
| `lake env lean tools/VacuityGate.lean` | PASS, 1 reviewed helper | the same, 0 VACUOUS-PENDING, rule 5 out on 0 (`ec1_vacuity.txt`) |
| `python3 -I tools/witness_gate.py` on the three modules | PASS, OK=6, copy-error=0 | the same (`ec1_witness.txt`) |
| `python3 tools/compile_rules.py drift records/rules.toml HANDOFF.md` | PASS no drift | `PASS no drift` (`ec1_drift.txt`) |

**End check 2** (not run here; they run on DSMain at MERGE-4): gate 7, the banned-vocabulary scan,
the whole-library witness gate, the bridge search and the report tool.

**End check 3** (`ec3.txt`): both greps on the three new files find nothing (rc 1). The output of
`git diff --name-only 67d05bf HEAD` lists only the three modules, `ClassicalLean.lean`, `records/`
and `incoming/reviews/review-1.md`. In `ClassicalLean.lean` the diff is only the three added import
lines. Every output's sha256 is in `end_sha256.txt`.

## Commits (branch `cloud-math-4`, each pushed with `git push origin cloud-math-4`)

* `068ffe3` — records first: the order's copy, its INDEX row, the CLAIMS row and this fragment's
  first part.
* `87de121` — bridge 160, `ClassicalLean/InformationTheory/HuffmanEntropy.lean`, and its import
  line.
* `5c76118` — `incoming/reviews/review-1.md`.
* `51b2ed9` — bridge 162, `ClassicalLean/Probability/PrincipalComponents.lean`, and its import
  line.
* `f1d30dd` — bridge 161, `ClassicalLean/Statistics/JamesSteinRisk.lean`, and its import line.
* The commit that carries this section: the CLAIMS row closed and the INDEX row's state. A commit
  cannot cite its own hash.
* Then `incoming/REPORT.md`.

All three bridges are closed: none narrowed, none undone. `master` was not touched.
