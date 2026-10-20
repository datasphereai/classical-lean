# Report of order CLOUD-MATH-2

Written on 2026-10-20 by Claude Code cloud session `session_019tga5LT3iStpcstjGMLwLU`
(https://claude.ai/code/session_019tga5LT3iStpcstjGMLwLU), on branch `cloud-math-2` of GitHub
`datasphereai/classical-lean`, from `4d99afd873730fa5f1231c6d6c68f57f2601c4a0`. Records: round 66,
`records/rounds/20261020T181822Z__round-66-power-method-pseudoinverse-chi-squared-kkt-huffman.md`.
Reviews: `incoming/reviews/`. Evidence: `incoming/evidence/` (the session's `~/cm2-evidence/`;
`evidence.log` there is the log as it stood when it was copied).

## In short

All five items landed as five new modules, one commit each; none narrowed, none undone; every main
theorem with a hypothesis has a witness; every module had a cold review, and each review with
findings ended with a fresh reviewer's confirming pass. Every finding, in all seven reviews, was
MINOR and in a docstring (six reviews, five confirming passes). End check 1's six commands all came out as predicted, so it ran once;
End check 2 (`citecheck.py`) is `OK` for every commit. `master` was not touched:
`git ls-remote origin master` gave `9c0639c5878d09db83b1334ec35b705add9a8cb7` at the start and at
the end (`lsremote-start`, `lsremote-end`). No pull request was opened (the order forbids it).

| item | module | commit | verdict of the main theorems against the plan row |
|---|---|---|---|
| 147 | `ClassicalLean/Analysis/PowerMethod.lean` | `f58d3ba` | `tendsto_powerIterate` GENERALIZED |
| 150 | `ClassicalLean/Algebra/Pseudoinverse.lean` | `f2c4785` | `pinv`, `pinv_spec`, `pinv_unique`, `pinv_residual_dotProduct_le`, `pinv_eq_leastSquares` FAITHFUL |
| 151 | `ClassicalLean/Probability/ChiSquared.lean` | `bcc7619` | `hasLaw_sum_sq_gaussian` FAITHFUL |
| 152 | `ClassicalLean/Analysis/KKT.lean` | `7b7a471` | `exists_kkt_of_slater` FAITHFUL |
| 153 | `ClassicalLean/InformationTheory/Huffman.lean` | `f224ec9` | `huffmanLength` FAITHFUL, `huffman_optimal` GENERALIZED |

GENERALIZED means wider than the plan's row, never weaker: 147 holds for any symmetric linear map
of a finite-dimensional real inner product space (a symmetric matrix is the case
`Matrix.toEuclideanLin A`) and any dominant index; 153 also builds the optimal code and allows
nonnegative weights that need not sum to 1. Both are the drafts' statements, unchanged.

## The final statements

As they stand in the committed modules (each inside its module's namespace, which is the module's
name), printed by `~/cm2-evidence/scripts/stmts.py` (label `report-stmts`):

```lean
theorem tendsto_powerIterate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (i₀ i₁ : Fin n)
    (hgap : |hT.eigenvalues hn i₁| < |hT.eigenvalues hn i₀|)
    (hdom : ∀ i, i ≠ i₀ → |hT.eigenvalues hn i| ≤ |hT.eigenvalues hn i₁|)
    (x : E) (hx : inner ℝ (hT.eigenvectorBasis hn i₀) x ≠ 0) :
    (∃ C : ℝ, ∀ k : ℕ,
      ‖(inner ℝ (hT.eigenvectorBasis hn i₀) ((T ^ k) x))⁻¹ • (T ^ k) x
          - hT.eigenvectorBasis hn i₀‖
        ≤ C * (|hT.eigenvalues hn i₁| / |hT.eigenvalues hn i₀|) ^ k) ∧
    Tendsto (fun k : ℕ =>
        (inner ℝ (hT.eigenvectorBasis hn i₀) ((T ^ k) x))⁻¹ • (T ^ k) x) atTop
      (𝓝 (hT.eigenvectorBasis hn i₀))

noncomputable def pinv [DecidableEq n] (A : Matrix m n ℝ) : Matrix n m ℝ :=
  Classical.choose (exists_penrose A)

theorem pinv_spec (A : Matrix m n ℝ) :
    A * pinv A * A = A ∧ pinv A * A * pinv A = pinv A ∧
      (A * pinv A)ᵀ = A * pinv A ∧ (pinv A * A)ᵀ = pinv A * A

theorem pinv_unique {A : Matrix m n ℝ} {X : Matrix n m ℝ}
    (h1 : A * X * A = A) (h2 : X * A * X = X) (h3 : (A * X)ᵀ = A * X)
    (h4 : (X * A)ᵀ = X * A) : X = pinv A

theorem pinv_residual_dotProduct_le (A : Matrix m n ℝ) (y : m → ℝ) (β : n → ℝ) :
    (y - A *ᵥ (pinv A *ᵥ y)) ⬝ᵥ (y - A *ᵥ (pinv A *ᵥ y)) ≤
      (y - A *ᵥ β) ⬝ᵥ (y - A *ᵥ β)

theorem pinv_eq_leastSquares {A : Matrix m n ℝ} (hA : IsUnit (Aᵀ * A).det) :
    pinv A = ClassicalLean.Statistics.leastSquares A

theorem hasLaw_sum_sq_gaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {k : ℕ} (hk : 0 < k) {X : Fin k → Ω → ℝ}
    (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) :
    HasLaw (fun ω => ∑ i, X i ω ^ 2) (gammaMeasure ((k : ℝ) / 2) (1 / 2)) P

theorem exists_kkt_of_slater {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] {f : E → ℝ} {g : ι → E → ℝ} {xbar a : E}
    {b : ι → E} (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hfa : HasGradientAt f a xbar) (hgb : ∀ i, HasGradientAt (g i) (b i) xbar)
    (hslater : ∃ x0, ∀ i, g i x0 < 0) (hxbar : ∀ i, g i xbar ≤ 0)
    (hmin : IsMinOn f {x | ∀ i, g i x ≤ 0} xbar) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∀ i, w i * g i xbar = 0) ∧ a + ∑ i, w i • b i = 0

noncomputable def huffmanLength [Fintype ι] (p : ι → ℝ) : ι → ℕ :=
  huffAux (Fintype.card ι) p Finset.univ

theorem huffman_optimal {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (hα : Fintype.card α = 2) {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) :
    ∃ c : ι → List α, Function.Injective c ∧ InformationTheory.IsPrefixFree (Set.range c) ∧
      (∀ i, (c i).length = huffmanLength p i) ∧
      ∀ c' : ι → List α, Function.Injective c' →
        InformationTheory.IsPrefixFree (Set.range c') →
          ∑ i, p i * ((c i).length : ℝ) ≤ ∑ i, p i * ((c' i).length : ℝ)
```

## What changed against the drafts

Statements: nothing but the move into the namespaces, by job 1's type comparison with
`pp.fullNames` (every main theorem and definition SAME; the private `pick` of 153 alone differs, by
an instance its value never depended on). Proofs: the Goal list's changes only, every one made,
each listed in round 66 (section "Proof changes and warning fixes, by item"). Two choices there
the order did not spell out:

- **150, `[DecidableEq n]`.** The Goal list's `omit … in` on the three private helpers would also
  have taken the instance off the public `pinv` (a definition takes only the section instances its
  body uses) and so changed every main theorem's type. Instead, by the Goal list's other option
  ("bind it where it is used"), the section's `variable` line gives `[DecidableEq n]` only after
  `pinv`, and `pinv` binds it itself. Every main theorem's type is the draft's.
- **152, imports.** The draft imported the library's `ClassicalLean.Analysis.GradientDescent`, using
  none of its declarations, for one Mathlib lemma it brings in (`HasFDerivAt.const_mul`); the
  module imports that lemma's Mathlib file, `Mathlib.Analysis.Calculus.FDeriv.Mul`, instead.

`import Mathlib` (147 and 151) became targeted imports, each declaring a name the file uses; both
module reviewers note, and do not count, that several of them are also implied by the others, as
in much of the library. Every module's `lake build` gave 0 warnings.

## Witnesses (rule 4)

Six, after each module's last line, each `example := Full.name (…)` with every chosen argument by
name and rule 4's docstring; times in epoch seconds (`date +%s` through `ev.sh`), all far within
1800 seconds:

| item | theorem | the case | start | end |
|---|---|---|---|---|
| 147 | `tendsto_powerIterate` | the diagonal matrix `!![2, 0; 0, 1]` on the Euclidean plane, `i₀ = 0`, `i₁ = 1`, from `(1, 1)` (claude-ai's start) | 1792523234 | 1792523335 |
| 150 | `pinv_unique` | `A = !![1, 2; 0, 0]` (rank one, not symmetric), `X = !![1/5, 0; 2/5, 0]` | 1792523425 | 1792523459 |
| 150 | `pinv_eq_leastSquares` | `A = !![1, 0; 0, 1; 1, 1]`, full column rank, `det (Aᵀ A) = 3` | 1792523425 | 1792523459 |
| 151 | `hasLaw_sum_sq_gaussian` | `k = 3` coordinates of the product of three standard normal laws (from claude-ai's check) | 1792523478 | 1792523502 |
| 152 | `exists_kkt_of_slater` | minimise `x * x` on the real line subject to `1 - x ≤ 0` and `x - 2 ≤ 0`; `xbar = 1`, Slater point `3/2` | 1792523608 | 1792523729 |
| 153 | `huffman_optimal` | three symbols, weights `(1/2, 1/4, 1/4)`, alphabet `Bool` | 1792523743 | 1792523766 |

## Reviews

Each by a fresh subagent that had not seen the work; each brief built by
`~/cm2-evidence/scripts/mkbrief.py` from `HANDOFF.md` (quoting rules 12, 14, 17, 18, 19, 20, 22,
23, 26 and 31 whole), checked by `briefcheck.py` and hashed before it was sent; each reviewer
returned only its report's sha256, checked equal by `hl.sh` before the report was opened (all
equal); the repository's `git status --porcelain` before and after each review compared (equal
for all but `rv1c-confirm`, below).

| review | on | verdict | findings | confirming pass |
|---|---|---|---|---|
| `rv1-statements` | job 1, the five statement files | FINDINGS 1 | MINOR: a Huffman docstring said every step merges | `rv1c-confirm`: CONFIRMED |
| `rv2-147` | module 147 | FINDINGS 2 | MINOR: "every other eigenvalue" read by value, not by index; the credit's list of changes omitted `simpa` to `simp` | `rv2c-147`: CONFIRMED |
| `rv2-150` | module 150 | FINDINGS 1 | MINOR: the credit's account of the instance change ("the three private helpers") | `rv2c-150`: CONFIRMED |
| `rv2-151` | module 151 | CLEAN | none | not needed |
| `rv2-152` | module 152 | FINDINGS 1 | MINOR: the proof sketch's order (slackness first, then the Lagrangian's minimum) | `rv2c-152`: CONFIRMED |
| `rv2-153` | module 153 | FINDINGS 2 | MINOR: `pick` used the instance only inside a proof; `merge_step`'s docstring described the proof's choice, not the statement | `rv2c-153`: CONFIRMED |

One fix-and-confirm round per review; every fix was in docstrings only, each re-elaborated (and, for a
module, rebuilt with 0 warnings) before its confirming pass. The credit wording "the lane's API-CREDIT-1 work"
(that of `incoming/README.md`) replaced "the lane's order API-CREDIT-1" in four modules, from a note
of `rv2-147`; each module review or confirming pass saw it.

## Gates, predicted beside measured

Predictions: `incoming/PREDICTIONS.md`, committed as `2f21991` before End check 1 (rule 27's
methods: the censuses, and the import closure of a scratch file importing only the five modules,
10 modules more than the base closure). End check 1 on the clean tree at `2f21991`:

| command | predicted | measured |
|---|---|---|
| `lake build` | rc 0, 4188 jobs, 0 warnings | rc 0, 4188 jobs, 0 `warning:` lines (`ec1-build`, `ec1-build-warn`) |
| `lake env lean tools/AxiomGate.lean` | PASS 3458 (3379 + 79) | PASS 3458, 0 scoped exceptions (`ec1-axiom`) |
| `python3 -I tools/check_sorry.py` | PASS 135 | PASS 135 (`ec1-sorry`) |
| `lake env lean tools/VacuityGate.lean` | PASS, 1 reviewed helper, 0 VACUOUS-PENDING, rule 5 out on 0 | the same (`ec1-vacuity`) |
| `python3 -I tools/check_records.py` | PASS 135, 1 exemption | the same (`ec1-records`) |
| `python3 tools/compile_rules.py drift records/rules.toml HANDOFF.md` | `PASS no drift` | `PASS no drift` (`ec1-drift`) |

No miss. The censuses (14, 10, 12, 2, 41) are measurements; the hand estimates logged before them
were 14, 10, 15, 6 and 30, and were not used.

During job 2 the vacuity gate ran, per module, as a copy of `tools/VacuityGate.lean` whose only
change is its import line (`import ClassicalLean` became `import ClassicalLean.Simplex.Ordered`,
the module of the one reviewed helper, and the new module), because the root module is not rebuilt
between job 2 and End check 1 (rule 27); the copy passed on the base as a control (`vac-control`).
The real gate ran in End check 1.

## The vacuity list

No entry added to `tools/vacuity_reviewed.txt`; no helper flagged.

## The commits

`1663442` records first; `f58d3ba` item 147 (with job 1); `f2c4785` item 150; `bcc7619` item 151;
`7b7a471` item 152; `f224ec9` item 153; `2f21991` the predictions; and the commit that carries
this report, the reviews, the evidence and the closed records, the last. Each message ends with
its `Evidence:` line from `evcite.py`, followed by the two attribution trailers (the DSMain
practice of `9c0639c`).

## End check 2

`$T/ev.sh citecheck "OK for every commit" python3 -I $T/citecheck.py $EVD/evidence.log $REPO 4d99afd` (label `citecheck`), its output
verbatim:

```
OK 1663442
OK f58d3ba
OK f2c4785
OK bcc7619
OK 7b7a471
OK f224ec9
OK 2f21991
```

The last commit comes after this check; claude-ai checks it at the merge.

## Evidence left out of `incoming/evidence/`

Files over 1 MB (label `big-files`; size in bytes, sha256, path):

```
1411913 24b9b05bc2ada321ae6ce946924a42e702a6108c30d01d28a81c92c17da0dfc2 /root/cm2-evidence/rv2-151-graph.out
```

It is a review's import-graph dump (`rv2-151-graph`), kept in the session's folder.

## Misses, refusals and anything not closed

Nothing is not closed. The misses, as the session recorded them when they happened
(`~/cm2-evidence/misses.txt`):

```
MISS-1 2026-10-20 probecheck check on the five drafts run once outside ev.sh after the probes run (not cited)
MISS-2 2026-10-20 typecmp-153's logged prediction said 7 of 8 SAME; the file has 7 messages, 6 SAME, pick DIFF as predicted
MISS-3 2026-10-20 rule 12: the repository tree changed during review rv1c (status empty before at 19:07Z; the session added ClassicalLean/Analysis/PowerMethod.lean and its import line at 19:08:55Z-19:09:03Z, logged m147-module, build-147); the reviewer wrote nothing and says so; from here the tree is not touched while a reviewer runs
MISS-4 2026-10-20 a line-length check of PowerMethod.lean ran as inline python outside ev.sh (not cited); two fix edits had first made lines over 100 characters, caught by el.sh m147-module-2 and m147-module-3 (1 warning each) before the final text
MISS-5 2026-10-20 quotes-r66-b listed a quote not in the fragment (manifest error, rc 1); corrected manifest quotes-r66-c rc 0
```

Calls refused by a tool, a `grep` of `evidence.log` (`notrun-count`: 7):

```
2026-10-20T18:30:31Z	types-draft-147	cmd=refused by rule 37 (probecheck rc 4): el.sh /root/cm2-evidence/types/draft-147.lean :: NOT CLEARED: set_option
2026-10-20T18:30:31Z	types-draft-150	cmd=refused by rule 37 (probecheck rc 4): el.sh /root/cm2-evidence/types/draft-150.lean :: NOT CLEARED: set_option
2026-10-20T18:30:31Z	types-draft-151	cmd=refused by rule 37 (probecheck rc 4): el.sh /root/cm2-evidence/types/draft-151.lean :: NOT CLEARED: set_option
2026-10-20T18:30:32Z	types-draft-152	cmd=refused by rule 37 (probecheck rc 4): el.sh /root/cm2-evidence/types/draft-152.lean :: NOT CLEARED: set_option
2026-10-20T18:30:32Z	types-draft-153	cmd=refused by rule 37 (probecheck rc 4): el.sh /root/cm2-evidence/types/draft-153.lean :: NOT CLEARED: set_option
2026-10-20T19:29:31Z	rv2c-147-simple	cmd=refused by rule 37 (probecheck rc 4): el.sh /root/cm2-review-4/simple.lean :: NOT CLEARED: sub_mul zero_smul
2026-10-20T20:07:40Z	rv2-151-var-no-hind	cmd=refused by rule 37 (probecheck rc 4): el.sh /root/cm2-review-7/var/no-hind.lean :: NOT CLEARED: hind.comp
```

The first five were this session's, before `set_option` was allowlisted with its reason; the last
two were reviewers' runs, each replaced by a run that passed the check. Notes from the reviewers,
not counted as findings: `rv2-147` noted that with `n = 2` the witness's `hdom` constrains nothing
past `i₁` (rule 4 accepts a 2-by-2 matrix); `rv2c-152` noted that `rv2-152`'s report gives an end
time later than the time its file was written; the module reviews of 147, 150 and 151 noted that
some imports are implied by others.

## CI

`.github/workflows/ci.yml` (build, axiom gate, check_sorry, vacuity gate, rules gate): success on
`4d99afd`, `1663442`, `f58d3ba` and `7b7a471`; cancelled on `f2c4785`, `bcc7619` and `f224ec9` by
the next push; on `2f21991`, in progress when this was written (`ci-list-end`). The run on the
last commit is read after its push; its result is in the session's final message.
