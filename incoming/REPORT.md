# Report — order CLOUD-MATH-1 (round 60)

Claude Code cloud session `session_01HV9mMLe9qSe13nN9hMyEBJ`, branch `cloud-math-1` on GitHub
`datasphereai/classical-lean`, from `e2fac6da5992ea3e7d3f55ba31420e44039d7b42`. Order:
`records/orders/20261015T023648Z__claude-ai__order-cloudmath1-han-frank-wolfe-state-prices-polya-reflection.md`.
Round: `records/rounds/20261015T023648Z__round-60-han-frank-wolfe-state-prices-polya-reflection.md`.

## In short

- All five items landed as five new modules, each under the library's gates, with witnesses, a
  cold review and records: Han's inequality (131), Frank–Wolfe on the simplex (135), state prices
  (136), Pólya's urn (137), the reflection principle (139).
- No narrowing. No item undone. Every draft statement is kept as it was, moved into its module's
  namespace. Two statements are wider than the plan's rows (GENERALIZED): `fw_general` (any convex
  set of squared diameter at most `D`) and the new `ae_mem_Icc_of_tendsto_urnShare` (any almost sure
  limit of the share, assuming only 0/1 draws).
- Every main theorem with a hypothesis has a witness, each done within 30 minutes of its start.
- Reviews: four PASS with no finding. Item 135 had one MINOR docstring finding. It was fixed and
  then confirmed by a fresh reviewer.
- End check 1 on the clean tree: all five gates passed. Four matched their predictions exactly.
  One missed: the axiom gate counted 3317 theorem constants against a predicted 3302 (+15, outside
  the stated range of 74 to 82 new). The causes were tactic auxiliaries the hand model left out
  (below).
- No entry was added to `tools/vacuity_reviewed.txt`. `master` was untouched:
  `git ls-remote origin master` gave `20303cd4eb902e15b2d4994ea6aa2263f5146264` at the start and at
  the end.

## Setup

- `curl -sSI https://cache.mathlib.org/` answered `HTTP/2 404` from cache.mathlib.org itself,
  through the proxy's `200 Connection Established`. That is a pass.
- `origin/cloud-math-1` was `e2fac6d…`, and the five drafts' sha256s matched `incoming/README.md`.
- elan installed Lean v4.34.0. `lake exe cache get` downloaded 8908 files.
- The setup `lake build` gave rc 0, 4170 jobs, 0 warnings. AxiomGate gave PASS 3228. There were 122
  modules. These are the order's starting counts, confirmed before any new module existed.

## The items

The statements are quoted from the modules. Each docstring names its item ("item N of
MATH-PLAN-library-2"). Each module docstring lists its results.

### 131 — Han's inequality, `ClassicalLean/InformationTheory/HanInequality.lean`

```lean
theorem mul_shannonEntropy_le_sum {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    [DecidableEq α] {P : (ι → α) → ℝ} (hP0 : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1) :
    ((Fintype.card ι : ℝ) - 1) * shannonEntropy P
      ≤ ∑ i, shannonEntropy (fun y : {j // j ≠ i} → α =>
          ∑ x, if (fun j : {j // j ≠ i} => x j.1) = y then P x else 0)
```

- **Narrowing:** none.
- **Witness:** two coordinates with two values each. The law puts `3/8` on each family where the
  coordinates agree and `1/8` on each where they differ.
- **Review** (`incoming/reviews/131-review-r1.md`): PASS, FAITHFUL, no findings. The reviewer
  checked in Lean that `hP1` is needed, and by hand that `hP0` is needed.

### 135 — Frank–Wolfe on the simplex, `ClassicalLean/Analysis/FrankWolfe.lean`

```lean
theorem fw_general {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {f' : E → E} {L : ℝ≥0} {K : Set E} {D : ℝ}
    (hK : Convex ℝ K) (hconv : ConvexOn ℝ K f) (hf : ∀ x, HasGradientAt f (f' x) x)
    (hL : LipschitzWith L f') (hD : ∀ a ∈ K, ∀ b ∈ K, ‖a - b‖ ^ 2 ≤ D)
    {x s : ℕ → E} (hx0 : x 0 ∈ K) (hs : ∀ k, s k ∈ K)
    (hmin : ∀ k, ∀ y ∈ K, ⟪f' (x k), s k⟫ ≤ ⟪f' (x k), y⟫)
    (hx : ∀ k : ℕ, x (k + 1) = x k + (2 / ((k : ℝ) + 2)) • (s k - x k))
    {z : E} (hz : z ∈ K) (k : ℕ) :
    f (x (k + 1)) - f z ≤ 2 * (L : ℝ) * D / ((k : ℝ) + 3)

theorem sub_le_of_frankWolfe {ι : Type*} [Fintype ι] {f : EuclideanSpace ℝ ι → ℝ}
    {f' : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {L : ℝ≥0}
    (hconv : ConvexOn ℝ {y : EuclideanSpace ℝ ι | WithLp.ofLp y ∈ closedSimplex ι} f)
    (hf : ∀ y, HasGradientAt f (f' y) y) (hL : LipschitzWith L f')
    {x s : ℕ → EuclideanSpace ℝ ι} (hx0 : WithLp.ofLp (x 0) ∈ closedSimplex ι)
    (hs : ∀ k, WithLp.ofLp (s k) ∈ closedSimplex ι)
    (hmin : ∀ k, ∀ y : EuclideanSpace ℝ ι, WithLp.ofLp y ∈ closedSimplex ι →
      ⟪f' (x k), s k⟫ ≤ ⟪f' (x k), y⟫)
    (hx : ∀ k : ℕ, x (k + 1) = x k + (2 / ((k : ℝ) + 2)) • (s k - x k))
    {z : EuclideanSpace ℝ ι} (hz : WithLp.ofLp z ∈ closedSimplex ι) {k : ℕ} (hk : 0 < k) :
    f (x k) - f z ≤ 4 * L / (k + 2)
```

- **Changes:** `fw_general` was private in the draft. It is public now under the same name, as
  the order's table asks.
- **Narrowing:** none.
- **Witnesses** (both theorems):
  - `f y = ‖y‖²` on the two-coordinate simplex, with gradient `2 y` and `L = 2`.
  - The real Frank–Wolfe iterates of `f` from the vertex `(0, 1)`. Their linear-minimisation
    points alternate between the two vertices, with closed forms `k/(2(k+1))` (even `k`) and
    `(k+1)/(2k)` (odd `k`), so the iterates approach `(1/2, 1/2)` from both sides.
  - `z = (1/2, 1/2)`, `k = 3`. For `fw_general`, `K` is the simplex and `D = 2`.
- **Review** (`135-review-r1.md`): PASS WITH FINDINGS (0 blocker, 0 major, 1 minor).
  `sub_le_of_frankWolfe` is FAITHFUL and `fw_general` is GENERALIZED. The reviewer checked by
  exact arithmetic that the witness iterates are the method's own iterates for `k < 40`.
- **The finding:** two docstrings said the simplex's squared diameter is exactly `2`, which is
  false for fewer than two coordinates.
- **Fix:** docstrings only, with the reviewer's wording (`135-fix-r1.diff`).
- **Confirming pass** by a fresh reviewer (`135-confirm-r1.md`): CONFIRMED, finding 1 fixed, no
  new finding.

### 136 — State prices, `ClassicalLean/Analysis/StatePrices.lean`

```lean
theorem exists_pos_statePrices_iff {m n : Type*} [Fintype m] [Fintype n]
    (D : Matrix m n ℝ) (π : n → ℝ) :
    (¬∃ θ : n → ℝ, π ⬝ᵥ θ ≤ 0 ∧ 0 ≤ D *ᵥ θ ∧ (π ⬝ᵥ θ < 0 ∨ ∃ i, 0 < (D *ᵥ θ) i)) ↔
      ∃ ψ : m → ℝ, (∀ i, 0 < ψ i) ∧ Dᵀ *ᵥ ψ = π
```

- **Narrowing:** none.
- **Witness:** none needed. The theorem has no hypothesis: `D` and `π` are data. The reviewer
  agreed.
- **Review** (`136-review-r1.md`): PASS, FAITHFUL, no findings. The reviewer showed in Lean that
  both sides take both truth values on 2×2 data.

### 137 — Pólya's urn, `ClassicalLean/Probability/PolyaUrn.lean`

```lean
theorem martingale_urnShare {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (r b : ℕ) (hrb : 0 < r + b)
    (X : ℕ → Ω → ℝ) (hX01 : ∀ n ω, X n ω = 0 ∨ X n ω = 1)
    (hX_meas : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hX_cond : ∀ n, μ[X n | ℱ n] =ᵐ[μ] urnShare r b X n) :
    Martingale (urnShare r b X) ℱ μ

theorem ae_tendsto_urnShare {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (r b : ℕ) (hrb : 0 < r + b)
    (X : ℕ → Ω → ℝ) (hX01 : ∀ n ω, X n ω = 0 ∨ X n ω = 1)
    (hX_meas : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hX_cond : ∀ n, μ[X n | ℱ n] =ᵐ[μ] urnShare r b X n) :
    ∃ L : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n => urnShare r b X n ω) atTop (𝓝 (L ω))

theorem ae_mem_Icc_of_tendsto_urnShare {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    (r b : ℕ) (X : ℕ → Ω → ℝ) (hX01 : ∀ n ω, X n ω = 0 ∨ X n ω = 1) {L : Ω → ℝ}
    (hL : ∀ᵐ ω ∂μ, Tendsto (fun n => urnShare r b X n ω) atTop (𝓝 (L ω))) :
    ∀ᵐ ω ∂μ, L ω ∈ Set.Icc 0 1
```

- **The third theorem** is the order's new one. Any almost-sure limit of the share lies in
  `[0, 1]`, assuming only that every draw is `0` or `1`. Together with `ae_tendsto_urnShare` it
  says that the urn's limit lies in `[0, 1]` almost surely.
- **Narrowing:** none.
- **Witnesses** (all three theorems):
  - A real Pólya urn with `r = b = 1` on the path space `ℕ → Bool`, built with Mathlib's
    Ionescu–Tulcea construction `Kernel.traj`.
  - The kernel draws red with the current share, computed from the history. That share lies
    strictly between `0` and `1`.
  - The filtration is `piLE`. The conditional mean comes from `Kernel.condExp_traj`.
  - The third witness takes its `L` from `ae_tendsto_urnShare` by `Classical.choose`.
  - The module imports `Mathlib.Probability.Kernel.IonescuTulcea.Traj` for the witnesses only. That
    file is already in the library's import closure.
- **Review** (`137-review-r1.md`): PASS, no findings. The two draft theorems are FAITHFUL and the
  new one is GENERALIZED. The reviewer checked in Lean that the kernel depends on the history and
  that the shares are bounded away from `0` and `1`.
- **Observations, not findings:** `hrb` could be dropped; rule 1 keeps it.

### 139 — The reflection principle, `ClassicalLean/Probability/Reflection.lean`

```lean
theorem measureReal_max_ge_eq (n : ℕ) (a : ℤ) (ha : 1 ≤ a) :
    (uniformOn (Set.univ : Set (Fin n → Bool))).real
        {ω | a ≤ (Finset.range (n + 1)).sup' ⟨0, by simp⟩ (walk n ω)} =
      (uniformOn (Set.univ : Set (Fin n → Bool))).real
          {ω | a ≤ walk n ω n} +
        (uniformOn (Set.univ : Set (Fin n → Bool))).real
          {ω | a < walk n ω n}
```

- **Imports:** `import Mathlib` was replaced by `import Mathlib.Probability.UniformOn`.
- **Narrowing:** none.
- **Witness:** `n = 4`, `a = 2`.
- **Review** (`139-review-r1.md`): PASS, FAITHFUL, no findings. The reviewer checked in Lean that
  `1 ≤ a` is needed: it fails at `a = −1`.

### Changes to proofs, all items

These are the only proof changes. They came from Lean's warnings. A `lake build` gives 0 warnings
for each module.
- Deprecated names were renamed: `if_pos` to `ite_eq_left`, `if_neg` to `ite_eq_right`,
  `dif_pos` to `dite_eq_left`, `push_neg` to `push Not`, and `Set.mem_setOf_eq` (in a witness) to
  `Set.mem_ofPred_eq`.
- `show` became `change` where it changed the goal.
- Dead `first | … | …` alternatives were removed.
- The private helper `marg_via_equiv` takes `[Finite Z]` and no `[DecidableEq W]`, as the linter
  asked.

## Predicted beside measured (End check 1)

The predictions are in `incoming/PREDICTIONS.md`, committed in `6a007c6` before the gates ran. The
gates ran on the clean tree at `6a007c6` from 03:22:06Z to 03:31:22Z. Nothing needed fixing or
undoing, so End check 1 ran once.

| gate | predicted | measured |
|---|---|---|
| `lake build` | rc 0, 4175 jobs, 0 warnings | rc 0, `Build completed successfully (4175 jobs).`, 0 `warning:` lines |
| `lake env lean tools/AxiomGate.lean` | PASS, 3302 theorem constants (3228 + 74; range 74 to 82) | PASS, 3317 (3228 + 89), 0 scoped exceptions — **miss, +15** |
| `python3 -I tools/check_sorry.py` | PASS, 127 files | `check_sorry PASS — 127 file(s) under ClassicalLean, …` |
| `lake env lean tools/VacuityGate.lean` | PASS, 1 reviewed helper, 0 VACUOUS-PENDING, rule 5 ran out on 0 | the same line (534 s) |
| `python3 -I tools/check_records.py` | PASS, 127 modules, 82 files searched, 1 exemption | the same |

**Per-module theorem constants.** These are measured as `records/README.md` rule 1 says, after the
predictions. The census total, 3317, equals the axiom gate's count.

| module | predicted | measured | where the difference is |
|---|---|---|---|
| `Probability/Reflection` | 35 | 40 | 5 `card_eq._simp_1_k` from its `simp only`/`simp at` calls |
| `Analysis/StatePrices` | 4 | 4 | — |
| `InformationTheory/HanInequality` | 16 | 18 | `ssa_sum._simp_1_1`, `mul_shannonEntropy_le_sum._simp_1_1` |
| `Probability/PolyaUrn` | 14 | 14 | — |
| `Analysis/FrankWolfe` | 5 | 13 | 7 `fw_general._simp_1_k` from one `field_simp`; `fw_step._abel_1_1` from `abel` |
| **total** | 74 | 89 | +15 |

**Why the count missed.** The blind model came from a calibration on toy files outside the library.
- It got right: the `omega` auxiliaries (20), the `eq_1` lemmas (5) and the `_proof_` lemmas of a
  definition (2).
- It left out: `_simp_` auxiliaries from `simp only` with Mathlib lemmas that simp must first
  restate (7 in Reflection and HanInequality).
- It put `field_simp`'s auxiliaries at 0 because the toy `field_simp` made none. This one made 7.
- It did not know that `abel` makes an auxiliary.

**Two predictions were not fully blind.** The reviews of items 136 and 131 had shown some of their
modules' constants before `PREDICTIONS.md` was written; the file says so. Both of those modules'
predictions came from the model and were not changed to fit what the reviews showed.

## Vacuity-list entries

None. The vacuity gate passed during the work and at End check 1 with no helper flagged, so
`tools/vacuity_reviewed.txt` is unchanged.

## Commits

| commit | what |
|---|---|
| `1a56f31` | records first: the order, its INDEX row, the CLAIMS row, round 60's first part |
| `3aa32f8` | item 139 landed (module, import line, draft removed, review) |
| `82b24d2` | item 136 landed |
| `5da88e9` | item 131 landed |
| `82ac344` | item 137 landed |
| `cc65251` | item 135 landed, with its review's docstring fix and confirming pass |
| `6a007c6` | `incoming/PREDICTIONS.md`; `incoming/README.md` removed (no draft left) |
| this commit | this report; round 60 completed; the CLAIMS row closed; the INDEX row's state |

- Every push was `git push origin cloud-math-1`. No force-push, no reset, no pull request, no
  merge. Nothing outside the order's scope changed.
- **CI** (the workflow runs build, axiom gate, check_sorry and vacuity gate): success on
  `1a56f31`, `5da88e9` and `6a007c6` (the tree End check 1 ran on). `3aa32f8` and `82b24d2` went
  up in one push, so only `82b24d2` had a run. That run, and the runs on `82ac344` and `cc65251`,
  were cancelled because a later push came before they finished, as the workflow's `concurrency`
  setting does. The run on this last commit is read to the end after the push; its result is in
  the session's final message, since this file cannot hold it.

## Misses, and anything not closed

- **Not closed:** nothing. All five items closed.
- **The one miss:** the axiom gate's count, 3317 against a predicted 3302, explained above. It is
  not corrected: the prediction stays as committed.
- **Witness times** (from `date`):
  - 139: 02:39:50Z to 02:40:04Z.
  - 131: 02:42:10Z to 02:43:02Z.
  - 135: 02:44:25Z to 02:47:40Z.
  - 137: 02:49:14Z to 03:01:29Z.
  
  All were inside 30 minutes.
- **Review fix rounds:** one, on item 135. The limit is two.
