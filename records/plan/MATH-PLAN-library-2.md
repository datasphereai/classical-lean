# MATH-PLAN-library-2: the library's next plan, items 72 onward, ranked, in batches

Written 2026-10-11 by Claude Code on DSMain (a plain session, as dustin), for Dustin, from order
MATH-PLAN-library-2-order.md (sha256 d4bc6a1bd6b516dad5a78041066d4c30aeae535aa6f8ab42606883c341cd0ecc,
checked before reading). Read and search only: the worktree `~/lean/classical-lean-paper-crypto`
stayed at `d2cba27` with 0 dirty paths, nothing was built, committed or pushed. Every module is
named in dotted form. Every number below is checked by MATH-PLAN-library-2-checks.py (section 2).

## Context

The 71-item plan (MATH-PLAN-library.md) is done: LEAN-17 to LEAN-26 and VACUITY-1 are pushed,
origin/master and github master are both `d2cba27` (measured by `git fetch origin` and
`git ls-remote github master` at 07:29 UTC). The library has 120 modules, 3158 theorem constants
and builds in 4166 jobs (VACUITY-1-report.md). Dustin asked on 2026-10-09 for new results across
ten areas, with "connections" (results that tie two separate parts of the library together) counted
as worth as much as the obvious additions; on 2026-10-11 he ruled that fixing the vacuity gate's
open limits belongs in this plan. The vacuity gate (`tools/VacuityGate.lean`) is the check that
fails a theorem whose statement proves nothing beyond its own hypotheses (a *vacuous* theorem).

Two Mathlib versions were searched: the pinned one, v4.34.0 at `5ed2965256`
(lake-manifest.json; the same as the last plan), and Mathlib master at `2da3ab0a20` (git ls-remote,
2026-10-11 07:29 UTC), which builds with Lean v4.35.0-rc4, a release candidate.

Read for this plan: ROADMAP.md, HANDOFF.md, records/README.md, all 120 module docstrings (collected
by a script), MATH-PLAN-library.md in full, MATH-PLAN-library-HANDOFF.md, the known traps of
LEAN-16-order.md, the "Not reached" sections and statement notes of LEAN-17-report.md to
LEAN-26-report.md, and VACUITY-1-report.md in full. The handoff names the order's first version
(be033e28…); the version carried out here is the revised one (d4bc6a1b…).

Words used throughout. A **row** is one proposed result. A row is **load-bearing** when another row
of this plan rests on it. A **bridge** is a theorem whose proof must use two library modules that
do not depend on each other, through an object they share. **Track L** collects what the 71-item
plan narrowed or left open; **Track G** collects the gate's open limits. **Cost**, as in the last
plan: S = one to three short theorems; M = three to six theorems or one hard proof; L = an order on
its own.

## 1. Predicted beside found

The predictions were written into a separate file before the first Mathlib search:
MATH-PLAN-library-2-prediction.txt, written through ds_write_staging at 07:33:07 UTC,
post_sha256 **a3d7046cd6b57cb0650377d753c50688b691ca2ab7997eed540685b4e0e1206e**, equal to my own
sha256sum before the write and of the lane file after it. The first Mathlib read of this session
came after that (the Wanted/ comparison, below). The file fixes the counting rule used here: a row
is an item in the ranked list, batched or below the cut; a Track L row counts only under Track L;
a bridge counts under area 10; other rows under the first area they name.

| area | predicted | found | why it differs |
|---|---|---|---|
| 1 Linear algebra | 4 | 3 | two candidates are already in Mathlib (section 3) |
| 2 Probability and statistics | 5 | 6 | |
| 3 Calculus | 2 | 3 | |
| 4 Differential equations | 3 | 3 | hit |
| 5 Information theory | 4 | 5 | |
| 6 Numerical analysis and matrices | 4 | 6 | the Kantorovich inequality opened two rows here |
| 7 Convex optimization | 4 | 6 | Mathlib has no convex conjugate and no first-order method beyond what the library proved |
| 8 Stochastic processes | 4 | 4 | hit |
| 9 Time series | 3 | 2 | spectral density went to Track L, and two time-series ideas became bridges |
| 10 Connections (bridges) | 12 | 16 | the mechanical search found more pairs than I expected |
| Track L rows | 10 | 19 | the reports' "Not reached" lists held more small open points than the 17 I counted |
| Track G rows | 6 | 9 | I expected 6 of the 8 named gaps closed; 7 are handled by items 72 to 78 (the unfolding "limit" turned out not to be a limit at all, item 74), and the witnesses and the uninformative-statement report add 2 (items 89, 90) |
| total rows | 61 | 82 | |
| Track G limits kept as stated limits | 2 | 1 | the unfolding limit is not real (review r1, item 74), so only "true but uninformative" stays |

Two of twelve row counts hit (areas 4 and 8). As in the last plan I under-predicted overall (61
against 82), most in Track L and area 10.

## 2. How the search was done

**One script is the search.** MATH-PLAN-library-2-checks.py (sha256 in section 10) runs every
search in this plan and checks every number; its output MATH-PLAN-library-2-checks.out shows
**all hits**. Both files are in the lane next to this plan. To re-run it on DSMain:

```
mkdir mm && cd mm && git init -q && git remote add origin https://github.com/leanprover-community/mathlib4
git fetch -q --depth 1 origin 2da3ab0a20dc0c66f56a557e37df39f7d36cb953 && git checkout -q FETCH_HEAD
git fetch -q --depth 1 origin 5ed2965256430c3649e86755f9576b54eca72435
python3 -I MATH-PLAN-library-2-checks.py --repo ~/lean/classical-lean-paper-crypto --master mm --lean
```

The script refuses to run if the master clone is not at `2da3ab0a`. With `--lean` it also runs two
Lean files through `lake env lean` (about two minutes, nothing is built); without it, those two
sections are skipped.

**Each row's search** (ROADMAP §0: the mathematics, not only the name) is
`grep -rniE --include=*.lean '<pattern>'` over pinned `Mathlib/`, master `Mathlib/` and the
library's `ClassicalLean/`, giving lines / files. Section 6 lists every pattern with its three
counts and what any Mathlib hit is. Each name a row says it rests on was checked to exist as a
declaration in pinned Mathlib or the library (script section 2c; 122 names).

**The rows' formulas.** Where a row states a formula or a bound, the script checks it on exact
cases (Python fractions) or, marked FLOAT, on floating-point cases (sections 5 to 5d of its
output). Not checked numerically: rows that state no number (definitions, existence, consistency,
Lean examples), and three textbook bounds whose constants the proving order will fix (items 133,
146 and 147: Higham's Theorem 8.5, Heun's order two, the power method's ratio).

**Wanted/ and docs/1000.yaml.** Pinned Wanted/ has 34 `proof_wanted` in 18 files; master has 33 in
17: nothing new, one removed (`recENNReal_neg_coe_ennreal`, outside the plan). docs/1000.yaml has
1179 entries in both; the one entry that differs is Q1052678 (Baire category theorem), outside the
plan. So, since the pinned Mathlib is the one the last plan read, there is nothing new on Mathlib's
own lists. Unformalised 1000.yaml titles read for ideas: "Fundamental theorem of arbitrage-free
pricing" (Q5508973, item 136), "Max flow min cut" and "Menger" (not now, section 7),
"Perron–Frobenius" (Q1564541, items 100 and later), "Wold's theorem" (not now).

**Connections, by a mechanical search in two parts**, both inside the script:

1. *Shared constants.* A Lean file (UsedConsts, in the script) lists, for every library module, the
   constants its declarations use. The script keeps the Mathlib constants that are not instances,
   structure projections or tactic internals, and for every pair of modules with no import path
   between them adds up log(N / df) over the rare constants they share (df = how many modules use
   it, at most 10; N = 119 modules use a kept constant). 2337 such pairs share at least one. Top of
   the list: GlivenkoCantelli × NeymanPearson (188.7, they share `cdf` and `StieltjesFunction`),
   GamblersRuin × MaximalInequality (121.8, stopping times; item 84), FiniteGame × LinearProgram
   (rank 17, item 141), MinimumQuadraticForm × GaussMarkov (positive definite quadratic forms; item
   81), MinMax × CovarianceDirections (rank 36, eigenvalues of a covariance matrix; item 142).
2. *Shared shapes.* Regular expressions for the shapes the order names (a first-order recursion
   `x (t+1) = a x t + e t`, a linear recurrence, a supermartingale, a Kraft-type sum, a quadratic
   form, a covariance, relative entropy, log-sum-exp, a stochastic matrix, a generating function, a
   stopping time, a linear program, eigenvalues, binary strings), each listing the modules whose
   source matches. Pairs that match one shape and have no import path between them are bridge
   candidates: KalmanVariance and FirstOrderRecursion (recursion; item 114), Extinction and
   AlgebraicGeneratingFunction (generating function; item 149), MovingAverage and
   EffectiveSampleSize (covariance; item 115), LinearProgram and ArbitrageCycle (linear program;
   item 145), ExponentialWeights and Entropy (log-sum-exp; item 116), HadamardInequality and
   CovarianceDirections (eigenvalues; item 96), GamblersRuin and MaximalInequality (stopping time).

Each bridge proposed was then checked by hand for a theorem whose proof needs both sides. Two pairs
from memory were confirmed by the script's exact checks: the gambler's ruin chance is a ratio of Lucas
numbers (item 95), and strings with no run of two losses are counted by Fibonacci numbers, of three
by the library's tribonacci numbers (item 143).

**Track G** was searched in `tools/VacuityGate.lean`, `tools/VacuityGateTests.lean` and
`tools/vacuity_reviewed.txt` (script section 3) and by a Lean census of the library's theorems
(HypCensus, in the script): 3158 theorem constants, 1748 written in a file (with a source
position), 1068 of those with at least one hypothesis that is a proposition, 637 with two or more,
400 with three or more; no theorem with macro scopes; 589 helper lemmas named `_proof_` with no
source position, of which 582 are used by their parent declaration, 4 by recursion internals or a
sibling helper, and 3 by nothing at all (`abs_le_of_abs_deriv_le._proof_1_8`, `_9`, `_10`); and
three definitions Lean marks irreducible, `motzkin`, `nacciAugmented` and `euclidSteps` (all
defined by well-founded recursion, which Lean makes irreducible by default; VACUITY-1's reviewer
grepped for the attribute and found none, which is also true; all three take values in `ℕ` or `ℤ`).

## 3. Not candidates: Mathlib or the library has them

- **The Loewner order reverses inverses** (if `A ≤ B` for positive definite matrices, then
  `B⁻¹ ≤ A⁻¹`): Mathlib proves it for a wide class of algebras that includes square matrices,
  `CStarAlgebra.inv_le_inv` (Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean:352),
  with matrices given that structure by a scoped instance (Analysis/CStarAlgebra/Matrix.lean:301).
  The matrix form is a helper for whoever needs it, not a row.
- **Sylvester's law of inertia**: LinearAlgebra/QuadraticForm/Real.lean.
- **Popoviciu's inequality on variances** (`Var X ≤ ((b − a)/2)²` for `X ∈ [a, b]`):
  `ProbabilityTheory.variance_le_sq_of_bounded`, Probability/Moments/Variance.lean:497. Item 92
  rests on it.
- **Detailed balance gives an invariant law**: `ProbabilityTheory.Kernel.IsReversible` and the lemma
  after it, Probability/Kernel/Invariance.lean.
- **Doob's decomposition** (1000.yaml has no `decl`, but Mathlib has it): `martingalePart`,
  Probability/Martingale/Centering.lean. **Martingale convergence**:
  `Submartingale.ae_tendsto_limitProcess`. **Cramér–Wold**: Probability/CramerWold.lean.
- **Loomis–Whitney, finite form** (`|S|^(n−1) ≤ ∏ᵢ |S projected away from coordinate i|`): Mathlib's
  grid-lines lemma (Analysis/FunctionalSpaces/SobolevInequality.lean) gives it with counting
  measures, so an entropy proof of it would be a second proof of a Mathlib corollary. Dropped as a
  row; Han's inequality, its entropy half, stays (item 131).
- **Chebyshev's sum inequality**: Algebra/Order/Chebyshev.lean.
- In the library already: entropy subadditivity (`shannonEntropy_le_shannonEntropy_add_shannonEntropy`),
  the uniform law has the most entropy (`shannonEntropy_le_log_card`), Shannon's source coding
  bound (item 8), the minimax theorem (item 62), Glivenko–Cantelli (item 60), and the Gibbs
  variational principle in the direction "log-sum-exp is the largest Gibbs objective"
  (`isMaxOn_gibbsObjective`; item 117 is the other direction).

## 4. In newer Mathlib

**None.** For every row the master count equals the pinned count (section 6; the script checks each
one). Between the pin and master, `Mathlib/` changed in 6474 files (55913 lines added, 44612
removed), none of it on a row of this plan.

What a bump would cost, from the last one (round 17, `records/rounds/20260923T164057Z__round-17-toolchain-v4.34.0.md`):
six toolchain steps from v4.29 to v4.34.0, 23 proof sites changed (6 at v4.29.1, 17 at v4.31.0),
warnings fixed at every step, at 3719 jobs and 44 modules. The library is now 4166 jobs and 120
modules, and master is a release candidate (v4.35.0-rc4), not a release. Nothing here would come
free with a bump, so no bump is proposed (decision 5).

## 5. The ranked list, in batches, with Track G placed

**The rule, exactly as applied** (the script computes it and checks this list against it):
1. load-bearing first: a row that another row of this plan rests on. The last plan's second
   reading, "used by an existing module", selects nothing here, because a theorem not yet written
   has no users;
2. absent from Mathlib: every row is (rows Mathlib has are in section 3), so this step orders
   nothing;
3. cheaper first: S, then S–M, then M, then M–L, then L;
4. ties, in this order: more dependent rows first; Track L before area rows (it finishes work
   already started, as ROADMAP's Tier 1 does); lower area number; then the order rows are listed in
   the script.

**Where Track G goes, by the order's rule.** Items 72 to 78 change what later batches are checked
against, so they come first, as order VACUITY-2, before LEAN-27: no new module is written under a
gate this plan already knows how to strengthen. Items 89 and 90 add no check that new modules
depend on (new main theorems get their satisfiability examples from LEAN-27 on, by the per-batch
method in section 8), so they may sit anywhere; they are order VACUITY-3, after LEAN-28, so the
first two math batches are not delayed.

**The cut.** Six math batches of five rows (30 rows) are batched; 43 math rows are below the cut,
ranked, in section 7. With the nine gate items numbered in place, the six batches end at item 110,
not 101 (decision 2).

### Order VACUITY-2: the gate, before any new module (items 72 to 78)

A *flag* is the gate's verdict that a theorem is vacuous. The *fixed test* and the *old case 3* are
the two tests VACUITY-1 left in the gate (a theorem is flagged when either fires).

| # | the gap, and the fix in one sentence | where | rests on | cost |
|---|---|---|---|---|
| 72 | `∧` and `↔` hypotheses are not opened: the fixed test opens a hypothesis `∀ x, P x ∧ Q x` into its two halves (`.1`, `.2`) and `∀ x, P x ↔ Q x` into its two directions (`.mp`, `.mpr`), so the test `lim_and_hyp` (renamed `vac_…`) and review r1's probes `vac_and_hyp` and `vac_iff_hyp` are flagged. | tools/VacuityGate.lean, tools/VacuityGateTests.lean | VACUITY-1's `openLevels`, `finish` | S–M |
| 73 | Irreducible definitions are not unfolded: the fixed test unfolds with all transparency (`withTransparency .all`), so a hypothesis stated through an irreducible definition is opened; test `vac_irreducible` is flagged. The library has three irreducible definitions (`motzkin`, `nacciAugmented`, `euclidSteps`), each a recursion Lean made irreducible by default; all three take values in `ℕ` or `ℤ`, not propositions, so this changes nothing for today's library and guards later modules. | tools/VacuityGate.lean | Lean's `whnf` | S |
| 74 | "More than 4 unfoldings before one binder" is not a real limit (review r1): one `whnf` call already unfolds every nested definition down to the binder, so the counter in `openLevels` never passes 1 (check `r1.unfold`: six nested definitions, one call). Fix: remove the dead counter, strike the limit from the gate's docstring and VACUITY-1's limits list, and add the test `vac_deep_unfold` as a guard. Changes no verdict. | tools/VacuityGate.lean, tests | `maxUnfolds`, `openLevels` | S |
| 75 | Theorems added by meta code, or with macro scopes, are skipped: test theorems with macro scopes (the library has 0, so nothing new to review); skip a `_proof_` helper with no source position only when some declaration uses it. Measured: 589 helpers, 586 used, 3 used by nothing; those 3 (`abs_le_of_abs_deriv_le._proof_1_8`, `_9`, `_10`) would then be tested, and if flagged go on the reviewed list as HELPER with that reason. | tools/VacuityGate.lean | `isTacticHelper`, `scan` | S–M |
| 76 | A flag is checked by `Meta.check`, not by the kernel: the proof term behind each fixed-test flag is also added to a throwaway copy of the environment (`addDecl` inside `withoutModifyingEnv`), so Lean's kernel checks it before the flag stands. | tools/VacuityGate.lean | `finish` | S |
| 77 | A contradictory hypothesis passes (`lim_false`): a new rule 5 tries to prove `False` from a written theorem's hypotheses with a short fixed list of closing tactics (`contradiction`, `linarith`, `omega`, `norm_num`, `decide`) under the per-theorem budget; a proof found, kernel-checked, flags "contradictory hypotheses". Scope measured: 1068 written theorems have a hypothesis, 637 have two or more. A deliberate "from a contradiction, anything" helper goes on the reviewed list. Stated limit that remains: contradictions those tactics do not find. | tools/VacuityGate.lean, tests | rule 5 is new | M |
| 78 | The union never had a cold review (its review came before ruling R3): one cold review of the whole gate as VACUITY-2 leaves it, old case 3, fixed test and rule 5, with the test set and `u-r1.out`'s probe theorems, in its own folder, before VACUITY-2's last commit. | review only | VACUITY-1's tests | S |

Seven items, all small. The order's rule of four to six items is for the math batches ("batches …
as orders LEAN-27 onward"); gate orders hold what the order's placement rule puts in them, so
VACUITY-2 has seven and VACUITY-3 two. If Dustin prefers, item 78 can run as VACUITY-2's ordinary
closing review and item 74 inside item 72's commit.

### Batch 1: order LEAN-27 (items 79 to 83)

| # | area | the result, in one sentence | Lean names | module | rests on | cost |
|---|---|---|---|---|---|---|
| 79 | 7 | The convex conjugate `f* y = sup over x of (y ⬝ x − f x)`, for a real-valued `f` on `ι → ℝ`, valued in the extended reals so no junk value is needed (a function that could be `⊥` would break Fenchel–Young, since Mathlib's `⊥ + ⊤ = ⊥`): Fenchel–Young `y ⬝ x ≤ f x + f* y`, `f ≤ g` gives `g* ≤ f*`, and `f** ≤ f`. Load-bearing for item 117. | `convexConjugate`, `dotProduct_le_add_convexConjugate`, `convexConjugate_anti`, `convexConjugate_convexConjugate_le` | new ClassicalLean.Analysis.ConvexConjugate | Mathlib `EReal`, `le_iSup`, `iSup_le` | S |
| 80 | 9 | For a covariance-stationary series (`cov(X i, X j) = γ \|i − j\|`), `Var(X 0 + ⋯ + X (k − 1)) = k γ 0 + 2 ∑_{1 ≤ j < k} (k − j) γ j`, which is `k γ 0 (1 + 2 ∑ (1 − j/k) ρ j)`: the variance-ratio identity. Load-bearing for item 115. | `variance_sum_eq_of_stationary`, `variance_sum_div_eq` | ClassicalLean.Probability.EffectiveSampleSize | library `variance_average` | S |
| 81 | 10, bridge | Generalised least squares for a common mean (design `X` = a column of ones, noise covariance `V` positive definite) is the library's least-variance weighting: its row `(1ᵀ V⁻¹ 1)⁻¹ 1ᵀ V⁻¹` equals `minWeights V`, and its variance factor is `1/(1ᵀ V⁻¹ 1)`. Shared object: a positive definite quadratic form. Load-bearing for item 98. | `glsMatrix_ones_eq_minWeights`, `inv_transpose_mul_ones_eq` | ClassicalLean.Statistics.GeneralizedLeastSquares (imports Analysis.MinimumQuadraticForm) | library `glsMatrix`, `minWeights`, `onesInvOnes`, `sum_minWeights` | S |
| 82 | 1 | The Kantorovich inequality: for a symmetric positive definite matrix `A` with `m ≤ A ≤ M` (Loewner order, `0 < m`), `(xᵀ A x)(xᵀ A⁻¹ x) ≤ ((m + M)²/(4 m M)) \|x\|⁴`, with equality at an equal mix of eigenvectors for `m` and `M` when `m` and `M` are eigenvalues of `A`. Load-bearing for items 98 and 111. | `dotProduct_mulVec_mul_inv_le` | new ClassicalLean.Algebra.Kantorovich | Mathlib `Matrix.IsHermitian.spectral_theorem`, `Matrix.PosDef`, `Matrix.PosSemidef` | S–M |
| 83 | 1 | Ky Fan's maximum principle: for a symmetric map on a finite-dimensional inner product space, for `k ≤ n`, the sum of its `k` largest eigenvalues is the largest value of `∑ᵢ re ⟪T uᵢ, uᵢ⟫` over orthonormal families `u₀, …, u_{k−1}`. Load-bearing for item 142. | `sum_eigenvalues_eq_iSup` | ClassicalLean.Algebra.MinMax | library `eigenvalues_eq_iSup_iInf`; Mathlib `LinearMap.IsSymmetric.eigenvectorBasis`, `LinearMap.IsSymmetric.eigenvalues_antitone` | M |

### Batch 2: order LEAN-28 (items 84 to 88)

| # | area | the result | Lean names | module | rests on | cost |
|---|---|---|---|---|---|---|
| 84 | 10, bridge | The biased `±1` walk (up with chance `p`, `0 < p < 1`, `p ≠ 1/2`, `r = q/p`; at `p = 0` Lean's junk values would give 1 where the chance is 0): it leaves `(−b, a)` with chance 1 and reaches `a` before `−b` with chance `(r^b − 1)/(r^(a+b) − 1)`; and when `p < q`, Ville's inequality on the martingale `r^(S n)` gives `P(the walk ever reaches a) ≤ (p/q)^a`. Shared object: a stopping time and a nonnegative martingale. Load-bearing for item 95. | `ae_exitTime_ne_top_of_biased`, `measureReal_hit_eq_of_biased`, `measureReal_exists_ge_le_of_biased` | ClassicalLean.Probability.GamblersRuin (imports Probability.MaximalInequality) | library `exitTime`, `measureReal_exists_le_of_supermartingale`; Mathlib `MeasureTheory.Martingale`, `MeasureTheory.stoppedValue` | M |
| 85 | L | Item 66's second proof of the minimax theorem, extended from payoffs in `[0, 1]` to every real matrix by the affine change `A ↦ (A − m)/(M − m)` (item 66 left it unproved, FiniteGame's docstring says so). The equality itself is already `minimax_eq_of_matrix` (item 62, by Sion); this row is a second proof, not a new statement. | `minimax_eq_of_exponentialWeights_of_affine` | ClassicalLean.Analysis.FiniteGame | library `minimax_eq_of_exponentialWeights`, `payoff` | S |
| 86 | L | Item 65's exact counterexamples A1 to A3 of LEAN-25's table as Lean `example`s: rates with a zero entry break (a) ⇔ (c), negative rates break (a) ⇔ (b), and `n − 2` Bellman–Ford rounds do not settle. | three `example`s | ClassicalLean.Combinatorics.ArbitrageCycle | library `NoGainCycle`, `HasPrices`, `noGainCycle_iff_noNegativeCycle` | S |
| 87 | L | Item 69's open point: prove `measureReal_no_run_le` without its hypothesis that each `A i` is measurable, or say in the module why it stays. | `measureReal_no_run_le` (restated) | ClassicalLean.Probability.LongestRun | library `measureReal_no_run_le`, `runEvent`; Mathlib `ProbabilityTheory.iIndepSet` | S |
| 88 | L | The Lean lemma item 68 did not make: compression scores, each against its own null law fixed in advance, fed to e-BH keep the expected false share at most `q`. | `integral_eFalseShare_score_le` | ClassicalLean.InformationTheory.CompressionTest (imports Probability.EValueStepUp) | library `integral_score_le_one`, `integral_eFalseShare_le` | S |

### Order VACUITY-3: the gate's reports (items 89 and 90)

| # | the gap, and the fix | where | cost |
|---|---|---|---|
| 89 | A contradictory hypothesis that rule 5 does not find (item 77): satisfiability *witnesses*, an `example` per theorem that meets all its hypotheses at once. Weighed: a witness for every written theorem with a hypothesis would be 1068 examples, too many to be worth it; most are lemmas whose hypotheses are met by the main theorem that uses them. So: from LEAN-27 on, every new **main** theorem with a hypothesis gets one (section 8, rule 6); VACUITY-3 backfills the main theorems of items 1 to 71, as `example`s in their modules. Cost measured from the last plan: its Lean-names column names 86 declarations for the 71 items (some are definitions, and the reports renamed or added some), so about 90 examples, against 1068 for every written theorem (check `r1.backfill`). | the modules of items 1 to 71 | L |
| 90 | True but uninformative statements stay a **stated limit** (being uninformative is not a property of the statement's form). A report narrows it: list each written theorem whose conclusion closes with no hypotheses by `simp`, `norm_num` or `positivity`, for a human to read. A report, not a check. | a script under tools/, its output in the order's evidence | M |

### Batch 3: order LEAN-29 (items 91 to 95)

| # | area | the result | Lean names | module | rests on | cost |
|---|---|---|---|---|---|---|
| 91 | L | Item 69's `log₂ n` reading, lower side, in Lean: in `n` independent trials that each lose with chance `q`, no run of `r` losses has chance at most `exp(−⌊n/r⌋ q^r)`; so for fair trials a run of `r` losses is all but certain once `n/r` is large compared with `2^r`. | `measureReal_no_run_le_exp` | ClassicalLean.Probability.LongestRun | library `measureReal_no_run_le`; Mathlib `Real.one_sub_le_exp_neg` | S |
| 92 | 3 | Grüss's inequality: for `X ∈ [m, M]` and `Y ∈ [n, N]` on a probability space, `\|Cov(X, Y)\| ≤ (M − m)(N − n)/4`; for functions on `[a, b]`, the average of `f g` is within `(M − m)(N − n)/4` of the product of the averages. | `abs_covariance_le_mul_div_four`, `abs_average_mul_sub_le` | new ClassicalLean.Analysis.Gruss | Mathlib `ProbabilityTheory.variance_le_sq_of_bounded` (Popoviciu), `ProbabilityTheory.covariance`, `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg` | S |
| 93 | 6 | Richardson extrapolation, exactly: the library's composite Simpson rule with `N` panels is `(4 T(2N) − T(N))/3`, `T(m)` Mathlib's trapezoidal rule with `m` steps (true for `N = 0` too, where both sides are Lean's `0`). | `simpson_eq_trapezoidal` | ClassicalLean.Analysis.Simpson | library `simpson`; Mathlib `trapezoidal_integral` | S |
| 94 | 6 | Stability for `y' = −λ y`, `λ > 0`, step `h > 0`: implicit Euler `u (k+1) = u k / (1 + h λ)` decays to `0` for every `h`; explicit Euler, from a nonzero start, decays exactly when `h λ < 2`. | `tendsto_implicitEuler`, `tendsto_explicitEuler_iff` | ClassicalLean.Analysis.EulerMethod | Mathlib `tendsto_pow_atTop_nhds_zero_iff` (the explicit factor `1 − hλ` can be negative) | S |
| 95 | 10, bridge | The gambler's ruin chance of item 84 is a ratio of Lucas numbers: `(r^b − 1)/(r^(a+b) − 1) = U b / U (a + b)` with `U = lucasU (1 + r) r`, the Lucas sequence whose characteristic roots are `1` and `r`. Shared object: the recurrence `h x = p h (x + 1) + q h (x − 1)`. | `measureReal_hit_eq_lucasU` | ClassicalLean.Probability.GamblersRuin (imports NumberTheory.LucasSequence) | item 84; library `lucasU`, `lucasU_add_two` | S |

### Batch 4: order LEAN-30 (items 96 to 100)

| # | area | the result | Lean names | module | rests on | cost |
|---|---|---|---|---|---|---|
| 96 | 10, bridge | Hadamard's inequality applied to a covariance matrix: `det (covMatrix X) ≤ ∏ᵢ Var(X i)` (the "generalised variance" is at most the product of the variances). Shared object: a positive semidefinite matrix. | `det_covMatrix_le_prod_variance` | ClassicalLean.Probability.CovarianceDirections (imports Algebra.HadamardInequality) | library `posSemidef_covMatrix`, `det_le_prod_diag`, `covMatrix`; Mathlib `ProbabilityTheory.covariance_self` | S |
| 97 | 10, bridge (import-related) | Relative entropy to the stationary law never increases along a chain: if `π P = π` and `μ i = 0` wherever `π i = 0`, then `D(μ P ‖ π) ≤ D(μ ‖ π)` (without that condition it is false under Lean's `x/0 = 0`: `π = (1, 0)`, `μ = (1/e, 1 − 1/e)` gives `0 ≤ −0.368`, review r1). A *stationary* law is one a step of the chain leaves unchanged. Shared object: a stochastic matrix as a channel. FiniteChain already imports Channel, so this link is not hidden. | `relEntropy_vecMul_le_of_stationary` | ClassicalLean.Probability.FiniteChain | library `relEntropy_vecMul_le` | S |
| 98 | 10, bridge | How much ordinary least squares loses against generalised least squares for a common mean: `(1ᵀ V 1)(1ᵀ V⁻¹ 1)/n² ≤ (m + M)²/(4 m M)` when the noise covariance `V` has `m ≤ V ≤ M` (Bloomfield and Watson's bound in this case). Shared object: the positive definite quadratic forms of `V` and `V⁻¹`. | `onesQuad_mul_onesInvOnes_le` | ClassicalLean.Statistics.GeneralizedLeastSquares (imports Algebra.Kantorovich) | items 81 and 82 | S |
| 99 | L | Item 68's plug-in argument in Lean: putting the estimated win rate `k/n` into the product Bernoulli null law, with a fixed code, gives a score at most every fixed-rate score, because `p̂^k (1 − p̂)^(n−k) ≥ p^k (1 − p)^(n−k)`; so its false-alarm rate stays at most `α` under every Bernoulli law. | `score_plugIn_le`, `measureReal_score_plugIn_ge_le` | ClassicalLean.InformationTheory.CompressionTest | library `measureReal_score_bernProd_ge_le`, `bernProd`, `relEntropy_nonneg` | S–M |
| 100 | L | Perron–Frobenius for a primitive chain (some power `P^k` has every entry at least `δ > 0`, though `P` may have zeros): one stationary law, approached at rate `(1 − n δ)^⌊t/k⌋`. Mathlib already defines primitive matrices, `Matrix.IsPrimitive` (Irreducible/Defs.lean, definitions only); the row states its hypothesis with it where it fits. | `existsUnique_vecMul_eq_self_of_pow`, `sum_abs_vecMul_pow_sub_le_of_pow` | ClassicalLean.Probability.FiniteChain | library `existsUnique_vecMul_eq_self`, `sum_abs_vecMul_pow_sub_le`; Mathlib `Matrix.IsPrimitive` | S–M |

### Batch 5: order LEAN-31 (items 101 to 105)

| # | area | the result | Lean names | module | rests on | cost |
|---|---|---|---|---|---|---|
| 101 | L | The spectral density of a moving average, finite form: `∑_{\|k\| ≤ q} γ(\|k\|) e^(−i k ω) = v \|∑ⱼ θⱼ e^(i j ω)\|²`, so it is never negative. | `sum_covariance_mul_cexp_eq` | ClassicalLean.Probability.MovingAverage | library `covariance_movingAverage`, `covariance_movingAverage_eq_zero_of_lt`; Mathlib `Complex.normSq` | S–M |
| 102 | L | Basu's theorem with bounded completeness (only bounded functions of `m` with mean 0 must vanish), the usual and weaker hypothesis (item 58 assumed full completeness). | `IsBoundedlyComplete`, `indep_of_isSufficient_of_isBoundedlyComplete_of_isAncillary` | ClassicalLean.Statistics.Sufficiency | library `indep_of_isSufficient_of_isComplete_of_isAncillary`, `IsComplete`, `IsAncillary` | S–M |
| 103 | L | Item 63's open point: prove `iSup_bayesRisk_eq_minimaxRisk_of_finite` without `hℓ` (every loss finite), or give the case that needs it. | the theorem, restated | ClassicalLean.Analysis.FiniteGame | library `iSup_bayesRisk_eq_minimaxRisk_of_finite` | S–M |
| 104 | L | The optional generalisations LEAN-17's reviews proved: item 3 without the probability-measure assumption (r3), item 5 at `q = 1` (r5), item 6 without the probability-measure instance, which independence gives (r6). | `integral_residual_sq`, `measureReal_sum_ge_le_exp_neg_relEntropy`, `variance_average_le_of_steady` (restated) | Statistics.ResidualVariance, Probability.LikelihoodScore, Probability.EffectiveSampleSize | those three theorems | S–M |
| 105 | 2 | Holm's step-down procedure: if every true null's p-value is valid (`P(p ≤ u) ≤ u`), the chance of rejecting any true null is at most `q`, under any dependence. | `holmRejected`, `measureReal_exists_holmRejected_true_le` | new ClassicalLean.Probability.StepDownProcedure | Mathlib `MeasureTheory.measure_biUnion_finset_le` | S–M |

### Batch 6: order LEAN-32 (items 106 to 110)

| # | area | the result | Lean names | module | rests on | cost |
|---|---|---|---|---|---|---|
| 106 | 2 | The probability integral transform: with `F` the distribution function of `X`, `P(F(X) ≤ u) ≤ u` for every `u ≥ 0` (for `u < 0` the left side is `0`), with equality for `u ∈ [0, 1]` when `F` is continuous; so a threshold test's p-value is valid. | `measureReal_cdf_le_le`, `measureReal_cdf_le_eq_of_continuous` | new ClassicalLean.Probability.IntegralTransform | Mathlib `ProbabilityTheory.cdf` | S–M |
| 107 | 2 | The Kolmogorov–Smirnov test is consistent: if the true distribution function `F` differs from `F₀` somewhere, then almost surely `sup \|F_n − F₀\|` eventually exceeds every `c < sup \|F − F₀\|`, so a test with thresholds `c_n → 0` rejects eventually. | `eventually_lt_sup_abs_empiricalCDF_sub` | ClassicalLean.Probability.GlivenkoCantelli | library `tendsto_sup_abs_empiricalCDF_sub`, `empiricalCDF` | S–M |
| 108 | 4 | A Lyapunov function for `x' = A x`: if `P` is positive definite and `Aᵀ P + P A + 2 c P` is negative semidefinite, then `x(t)ᵀ P x(t) ≤ e^(−2 c t) x(0)ᵀ P x(0)` for `t ≥ 0`. | `quadForm_le_exp_mul` | ClassicalLean.Analysis.LinearODE | library `eq_exp_smul_mulVec`, `hasDerivAt_exp_smul_mulVec`; Mathlib `antitoneOn_of_deriv_nonpos` | S–M |
| 109 | 5 | The asymptotic equipartition property: for independent draws with law `p` on a finite alphabet, `−(1/n) ∑ log p(X i) → H(p)` almost surely. | `tendsto_neg_log_div_shannonEntropy` | ClassicalLean.InformationTheory.MethodOfTypes | library `vecMeasure`, `shannonEntropy`; Mathlib `ProbabilityTheory.strong_law_ae` | S–M |
| 110 | 5 | Data processing for every f-divergence on finite sets: for `f` convex on `[0, ∞)`, a channel `W` and `q > 0`, `∑ⱼ (qW)ⱼ f((pW)ⱼ/(qW)ⱼ) ≤ ∑ᵢ qᵢ f(pᵢ/qᵢ)`; relative entropy is the case `f x = x log x`. | `sum_mul_comp_div_vecMul_le` | ClassicalLean.InformationTheory.Channel | Mathlib `ConvexOn.map_sum_le`; library `relEntropy_vecMul_le` (the special case) | S–M |

### Track L: every leftover of the 71-item plan, and what became of it

| leftover | where it was left | decision |
|---|---|---|
| full textbook Karlin–Rubin (support growing with θ) | item 56, ruling of 2026-10-09 | row, item 118 |
| item 66's second proof beyond payoffs in `[0, 1]` | LEAN-25 "Not reached" | row, item 85 (affine change); item 141 gives a third proof by linear programming |
| item 68's plug-in argument in Lean | LEAN-26, ruling of 2026-10-10 | row, item 99 |
| item 65's exact counterexamples as Lean examples | LEAN-25 table, A1 to A3 | row, item 86 |
| LEAN-17's dropped hypotheses as Lean witnesses | handoff §4; 29 table rows, 25 with a case | row, item 119 |
| LEAN-18's dropped hypotheses as Lean witnesses | handoff §4; 27 table rows, 23 with a case | row, item 120 |
| Moore–Penrose pseudoinverse | last plan §6 | row, item 150 |
| Perron–Frobenius | last plan §6 | primitive chains, item 100; the nonnegative irreducible case not now (section 7) |
| chi-squared laws and Cochran's theorem for laws | last plan §6 | row, item 151 (the chi-squared law); Cochran for laws not now |
| spectral density, Wold, Ljung–Box | last plan §6 | finite spectral density of a moving average, item 101; Wold and Ljung–Box not now |
| stochastic differential equations, Ornstein–Uhlenbeck | last plan §6 | not now: Mathlib still has no stochastic integral (0 hits, pinned and master) |
| KKT with Slater's condition | last plan §6 | row, item 152 |
| Efron–Stein | last plan §6 | row, item 121 |
| the lower half of Sanov's theorem | LEAN-24 "Not reached" | row, item 122 |
| Basu with bounded completeness | LEAN-24, review r58 | row, item 102 |
| does item 69's second theorem need measurability? | LEAN-26 "Not reached" | row, item 87 |
| does item 63 need finite losses? | LEAN-25 "Not reached" | row, item 103 |
| item 3 for any measure, item 5 at `q = 1`, item 6 without the instance | LEAN-17 "Not reached" | row, item 104 |
| a Lean lemma joining item 68's score to e-BH | LEAN-26 "Not reached" | row, item 88 |
| the lower side of item 69's `log₂ n` reading | LEAN-26 "Not reached" | row, item 91 |
| item 65's (a) ⇔ (b) for `r ≥ 0` and infinitely many assets (by hand only) | LEAN-25 "Not reached" | not now (section 7) |
| exact numbers of item 69 and item 68's 3/5 example in Lean (checks.py only) | LEAN-26 "Not reached" | not now (section 7) |
| full Marchenko–Pastur law | LEAN-26 | not now (section 7) |
| RaoBlackwell's docstring pointing to `IsSufficient.raoBlackwell`; item 18's citation in the old plan; item 22's name | LEAN-19, LEAN-20 notes | not rows: text edits for the next order that touches those files |

## 6. The search behind each row

`grep -rniE --include=*.lean '<pattern>'`; counts are lines / files in pinned Mathlib, then master,
then lines in the library. A Mathlib count above 0 is followed by what the hits are. "Gate" rows
cite the script's check labels (its section 3 and the census in section 4), which re-run them.

| # | row | pattern(s) | pinned | master | library | what the Mathlib hits are |
|---|---|---|---|---|---|---|
| 72 | G1 | checks `gate.test.lim_and_hyp`; VACUITY-1-report's limits table | — | — | — | — |
| 73 | G2 | checks `census.irreducible`, `r1.irreducible_values` | — | — | 3 definitions | — |
| 74 | G3 | checks `gate.maxUnfolds`, `r1.unfold` | — | — | — | — |
| 75 | G4 | checks `gate.macro`, `gate.helper`, `census.macroscopes`, `census.helpers`, `census.helpers_not_used_by_parent`, `census.helpers_used_by_nothing` | — | — | 0; 589; 7; 3 | — |
| 76 | G5 | check `gate.metacheck`; VACUITY-1-report "Not reached" | — | — | — | — |
| 77 | G6 | checks `gate.test.lim_false`, `census.hyp1`, `census.hyp2` | — | — | 1068; 637 | — |
| 78 | G7 | VACUITY-1-report "Cold review" (before ruling R3) | — | — | — | — |
| 79 | H6 | `convexConjugate\|convex conjugate\|fenchel\|legendre.?(transform\|fenchel)` | 0/0 | 0/0 | 2 | (library: LogSumExp's search note and SecondOrder's prose) |
| 80 | T2 | `variance ratio` | 0/0 | 0/0 | 0 | — |
| 81 | X2 | `generali[sz]ed least\|aitken\|glsMatrix` | 0/0 | 0/0 | 36 | — |
| 82 | A3 | `kantorovich` | 0/0 | 0/0 | 0 | — |
| 83 | A2 | `ky fan\|kyFan` | 0/0 | 0/0 | 0 | — |
| 84 | X3 | `gambler\|ruin`; `biased.*walk\|asymmetric.*walk` | 2/2; 0/0 | the same | 33; 0 | an author (Bruin) and a word in Algebra/Quandle.lean |
| 85 | L2 | `affine.*(payoff\|game)\|payoff.*affine` | 0/0 | 0/0 | 1 | (library: FiniteGame's docstring, "not proved here") |
| 86 | L4 | check `trackL.L4`: no `example` in ArbitrageCycle.lean | — | — | 0 | — |
| 87 | L15 | check `trackL.L15`: `(hA : ∀ i, MeasurableSet (A i))` in LongestRun.lean | — | — | 2 | — |
| 88 | L18 | check `trackL.L18`: CompressionTest does not import EValueStepUp | — | — | — | — |
| 89 | G8 | checks `census.hyp1`, `census.written`, `r1.backfill` | — | — | 1068; 1748; 86 names | — |
| 90 | G9 | VACUITY-1-report limits table; HANDOFF.md §4 (VacuityGate's stated blind spot) | — | — | — | — |
| 91 | L19 | check `trackL.L19`: no theorem with `exp` in LongestRun.lean | — | — | 0 | — |
| 92 | C2 | `gr[üu]ss`; `abs_covariance_le\|covariance_le_sqrt\|covariance.*sqrt.*variance` | 0/0; 0/0 | the same | 0; 0 | — |
| 93 | F4 | `richardson\|extrapolat` | 0/0 | 0/0 | 0 | — |
| 94 | F5 | `implicit euler\|backward euler\|a-stable\|a-stability` | 0/0 | 0/0 | 0 | — |
| 95 | X4 | `lucas.*(ruin\|walk)\|ruin.*lucas` | 0/0 | 0/0 | 0 | — |
| 96 | X6 | `det.*covMatrix\|covMatrix.*det\|generali[sz]ed variance` | 0/0 | 0/0 | 0 | — |
| 97 | X8 | `h-theorem\|entropy production` | 0/0 | 0/0 | 0 | — |
| 98 | X16 | `bloomfield` | 0/0 | 0/0 | 0 | — |
| 99 | L3 | `maximum.likelihood\|plug-in estimate` | 0/0 | 0/0 | 1 | — |
| 100 | L7 | `perron`; `stationary distribution\|invariant distribution`; check `r1.isPrimitive` | 6/6; 0/0; 1/1 | the same | 1; 5 | the Perron integral (BoxIntegral) and its citations; `structure IsPrimitive` (definitions only, found by review r1) |
| 101 | L9 | `spectral density\|spectralDensity` | 0/0 | 0/0 | 0 | — |
| 102 | L14 | `boundedly complete\|bounded completeness` | 0/0 | 0/0 | 1 | — |
| 103 | L16 | check `trackL.L16`: `(hℓ : ∀ θ y, ℓ θ y ≠ ∞)` in FiniteGame.lean | — | — | 2 | — |
| 104 | L17 | check `trackL.L17`: the three theorems and their hypotheses `[IsProbabilityMeasure μ]`, `(hq1 : q < 1)` | — | — | — | — |
| 105 | B3 | `\bholm\b\|bonferroni\|familywise error\|family.wise error\|step.?down (procedure\|test)` | 0/0 | 0/0 | 0 | — |
| 106 | B5 | `probability integral transform` | 0/0 | 0/0 | 0 | — |
| 107 | B6 | `kolmogorov.?smirnov\|smirnov` | 0/0 | 0/0 | 1 | — |
| 108 | D2 | `lyapunov` | 0/0 | 0/0 | 0 | — |
| 109 | E4 | `asymptotic equipartition\|typical set\|shannon.?mcmillan` | 0/0 | 0/0 | 0 | — |
| 110 | E6 | `f-divergence\|fDivergence\|csisz` | 3/2 | 3/2 | 0 | KL docstrings: "the Kullback–Leibler divergence is an f-divergence for `klFun`"; no general f-divergence and no data processing for one |
| 111 | F6 | `steepest descent\|exact line search` | 0/0 | 0/0 | 0 | — |
| 112 | H1 | `polyak\|[lł]ojasiewicz` | 0/0 | 0/0 | 0 | — |
| 113 | H3 | `subgradient\|subdifferential` | 0/0 | 0/0 | 0 | — |
| 114 | X10 | `kalman\|exponential smoothing` | 0/0 | 0/0 | 4 | — |
| 115 | X11 | `long.?run variance` | 0/0 | 0/0 | 1 | — |
| 116 | X12 | `mirror descent\|multiplicative weights\|exponential weights` | 0/0 | 0/0 | 10 | — |
| 117 | X15 | `logSumExp\|softmax` | 0/0 | 0/0 | 390 | — |
| 118 | L1 | `karlin\|rubin\|monotone likelihood` | 1/1 | 1/1 | 13 | "Rubin's theorem" on group actions |
| 119 | L5a | check `L5.lean17` | — | — | — | — |
| 120 | L5b | check `L5.lean18` | — | — | — | — |
| 121 | L12 | `efron` | 0/0 | 0/0 | 0 | — |
| 122 | L13 | `sanov` | 0/0 | 0/0 | 5 | — |
| 123 | A1 | `interlac\|poincar[eé] separation` | 0/0 | 0/0 | 0 | — |
| 124 | B1 | `bernstein.?s? (inequality\|bound)\|bennett` | 0/0 | 0/0 | 0 | — |
| 125 | B2 | `h[aá]jek` | 0/0 | 0/0 | 0 | — |
| 126 | B4 | `order statistic\|orderStatistic\|kth.?smallest` | 0/0 | 0/0 | 0 | — |
| 127 | C1 | `fej[eé]r` | 0/0 | 0/0 | 0 | — |
| 128 | C3 | `euler.?maclaurin`; `periodizedBernoulli 2\|bernoulliFun 2` | 0/0; 1/1 | the same | 3; 0 | `bernoulliFun_two` (`B₂(x) = x² − x + 1/6`), which the row rests on |
| 129 | D1 | `variation of (constants\|parameters)\|duhamel` | 0/0 | 0/0 | 0 | — |
| 130 | E1 | `channel capacity\|binary symmetric` | 0/0 | 0/0 | 0 | — |
| 131 | E2 | `han.?s inequality\|shearer` | 0/0 | 0/0 | 0 | — |
| 132 | F1 | `gauss.?seidel` | 0/0 | 0/0 | 0 | — |
| 133 | F3 | `forward substitution\|back.?substitution\|triangular solve\|backward (error\|stab)` | 0/0 | 0/0 | 0 | — |
| 134 | H2 | `projected gradient` | 0/0 | 0/0 | 0 | — |
| 135 | H4 | `frank.?wolfe\|conditional gradient` | 0/0 | 0/0 | 0 | — |
| 136 | H5 | `state price\|asset pricing\|stiemke`; `arbitrage` | 0/0; 0/0 | the same | 0; 1 | — |
| 137 | K1 | `p[óo]lya.?s? urn\|\burn\b` | 0/0 | 0/0 | 0 | — |
| 138 | K2 | `wald` | 1/1 | 1/1 | 11 | an author (Turnwald) in Dickson.lean |
| 139 | K3 | `reflection principle` | 1/1 | 1/1 | 0 | the reflection formula of Bernoulli polynomials (ZetaValues.lean:134) |
| 140 | T1 | `durbin\|partial autocorrelation` | 0/0 | 0/0 | 0 | — |
| 141 | X1 | `minimax.*(linear program\|duality)\|linear program.*minimax` | 0/0 | 0/0 | 0 | — |
| 142 | X5 | `principal component\|\bPCA\b` | 0/0 | 0/0 | 0 | — |
| 143 | X7 | `no two consecutive\|run.*fib\|fib.*run` | 0/0 | 0/0 | 1 | (library: a sentence in GoldenRatio.Characterisations, not about runs) |
| 144 | X13 | `bretagnolle\|\bhuber\b` | 0/0 | 0/0 | 0 | — |
| 145 | X14 | `negative cycle\|bellman` | 0/0 | 0/0 | 83 | — |
| 146 | D3 | `heun.?s method\|runge.?kutta` | 0/0 | 0/0 | 0 | — |
| 147 | F2 | `power (method\|iteration)` | 0/0 | 0/0 | 0 | — |
| 148 | K4 | `expected hitting\|mean hitting\|first.?step analysis\|mean first passage` | 0/0 | 0/0 | 0 | — |
| 149 | X9 | `total progeny\|galton\|branching process` | 0/0 | 0/0 | 5 | — |
| 150 | L6 | `pseudo.?inverse\|moorePenrose\|penrose` | 35/5 | 35/5 | 1 | NonsingularInverse.lean:22 "pseudoinverses which we do not consider"; a `DivInvMonoid` docstring; Penrose diagrams in a widget |
| 151 | L8 | `chi.?squared\|chiSquared` | 0/0 | 0/0 | 2 | — (Mathlib has the gamma law, `gammaPDF`, which the row rests on) |
| 152 | L11 | `\bslater\|karush\|kuhn.?tucker` | 2/2 | 2/2 | 3 | the TODO "Formalize Karush-Kuhn-Tucker theorem" (LagrangeMultipliers.lean:24) and a link in LocalExtr/Basic.lean |
| 153 | E5 | `huffman` | 0/0 | 0/0 | 0 | — |

## 7. Not now, and why

### Ranked below the cut (items 111 to 153, in rank order)

Same columns as section 5; "rests on" names the library or Mathlib facts, each checked to exist.

| # | area | the result | Lean names | module | rests on | cost |
|---|---|---|---|---|---|---|
| 111 | 6 | Steepest descent with exact line search on `xᵀ A x / 2` shrinks it by at least `((M − m)/(M + m))²` each step. | `quadForm_steepestStep_le` | ClassicalLean.Algebra.Kantorovich | item 82 | S–M |
| 112 | 7 | Polyak–Łojasiewicz: if `‖∇f‖²/2 ≥ μ (f − f*)` and the gradient is `L`-Lipschitz, gradient descent with step `1/L` has `f(x_k) − f* ≤ (1 − μ/L)^k (f(x_0) − f*)`. | `sub_le_pow_mul_of_polyakLojasiewicz` | ClassicalLean.Analysis.GradientDescent | library `le_sub_of_gradientStep` | S–M |
| 113 | 7 | The subgradient method: for convex `f` with subgradients of norm at most `G` and step `η`, the best of the first `T` points is within `(‖x₀ − z‖² + η² G² T)/(2 η T)` of `f z`. | `min_sub_le_of_subgradient` | new ClassicalLean.Analysis.SubgradientMethod | Mathlib `norm_sub_sq_real` | S–M |
| 114 | 10, bridge | The steady Kalman filter for a local level (`a = h = 1`) is exponential smoothing with constant `K = P*/(P* + r)`, `P* = riccatiRoot`; its error is a first-order recursion with coefficient `1 − K` whose steady variance `(q + K² r)/(1 − (1 − K)²)` equals `P*`. Shared object: the first-order recursion `e (t+1) = a e t + noise`. | `riccatiRoot_eq_steady` | ClassicalLean.Probability.KalmanVariance (imports Probability.FirstOrderRecursion) | library `riccatiRoot`, `riccati_equation_riccatiRoot`, `eq_steady_iff` | S–M |
| 115 | 10, bridge | The long-run variance of a moving average: for `n > q`, `Var(X 0 + ⋯ + X (n − 1)) = n v (∑ θ)² − 2 ∑_{k ≤ q} k γ(k)`, so `n Var(mean) → v (∑ θ)²`. Shared object: the variance of a sum of correlated quantities. | `variance_sum_movingAverage` | ClassicalLean.Probability.MovingAverage (imports Probability.EffectiveSampleSize) | item 80; library `covariance_movingAverage` | S–M |
| 116 | 10, bridge | Exponential weights is mirror descent: `softmax(log x − η ℓ)` is the one minimiser over the simplex of `η ⟨ℓ, y⟩ + D(y ‖ x)`. Shared object: softmax and relative entropy. | `isMinOn_inner_add_relEntropy_softmax` | ClassicalLean.Analysis.ExponentialWeights (imports InformationTheory.Entropy) | library `relEntropy_softmax`, `gibbsObjective_le` | S–M |
| 117 | 10, bridge (import-related) | The other direction of the Gibbs principle: the convex conjugate of log-sum-exp at `p` in the open simplex is `∑ p i log p i` (minus the entropy). The library already proves log-sum-exp is the largest Gibbs objective; Entropy imports LogSumExp, so this link is not hidden. Shared object: the Gibbs objective. | `convexConjugate_logSumExp` | ClassicalLean.Analysis.ConvexConjugate | item 79; library `isMaxOn_gibbsObjective`, `gibbsObjective_softmax` | S–M |
| 118 | L | Karlin–Rubin in the textbook form: monotone likelihood ratio with the ratio allowed to be `+∞` where `f θ = 0`, which takes in uniform laws on `[0, θ]`. | `HasMonotoneLikelihoodRatio'`, `isUniformlyMostPowerful_of_monotoneLikelihoodRatio'` | ClassicalLean.Statistics.NeymanPearson | library `power_le_of_likelihoodRatioTest`, `isUniformlyMostPowerful_of_monotoneLikelihoodRatio` | M |
| 119 | L | LEAN-17's 25 dropped-hypothesis cases as Lean `example`s in their modules. | `example`s | the modules of items 1 to 8 | LEAN-17's table | M |
| 120 | L | LEAN-18's 23 dropped-hypothesis cases as Lean `example`s. | `example`s | the modules of items 9 to 16 | LEAN-18's table | M |
| 121 | L | Efron–Stein for independent coordinates on finite sets: `Var f ≤ ∑ᵢ E[Varᵢ f]`; so with bounded differences `cᵢ`, `Var f ≤ ∑ cᵢ²/4`. | `variance_le_sum_variance_coord`, `variance_le_sum_sq_div_four` | new ClassicalLean.Probability.EfronStein | Mathlib `ProbabilityTheory.variance_le_sq_of_bounded` (Popoviciu); finite sums | M |
| 122 | L | The lower half of Sanov's theorem: a type `q` has chance at least `(n + 1)^(−K) exp(−n D(q ‖ p))`. | `le_measureReal_empirical_eq` | ClassicalLean.InformationTheory.MethodOfTypes | library `measureReal_empirical_eq_le`, `draws`; Mathlib `Nat.multinomial` | M |
| 123 | 1 | Cauchy interlacing: compressing a symmetric map to a subspace of dimension `m` gives eigenvalues with `λ_k(T) ≥ λ_k(T_V) ≥ λ_{k+n−m}(T)`. | `eigenvalues_compression_le`, `le_eigenvalues_compression` | ClassicalLean.Algebra.MinMax | library `eigenvalues_eq_iSup_iInf` | M |
| 124 | 2 | Bernstein's inequality: independent `X i` with mean 0, `X i ≤ b` and `∑ E[X i²] ≤ v` have `P(∑ X i ≥ t) ≤ exp(−t²/(2(v + b t/3)))`. | `measureReal_sum_ge_le_bernstein` | new ClassicalLean.Probability.BernsteinInequality | Mathlib `ProbabilityTheory.measure_ge_le_exp_mul_mgf`, `ProbabilityTheory.iIndepFun.mgf_sum` | M |
| 125 | 2 | The Hájek–Rényi inequality: for a square-integrable martingale and weights `c₁ ≥ c₂ ≥ ⋯ > 0`, `P(max c_k \|S_k\| ≥ ε) ≤ ε⁻² ∑ c_k² E[ξ_k²]`. | `measureReal_exists_mul_abs_ge_le` | ClassicalLean.Probability.MaximalInequality | library `measureReal_exists_abs_ge_le` (Kolmogorov's inequality) | M |
| 126 | 2 | Order statistics: for independent draws with `P(X i ≤ x) = F`, the `k`-th smallest is at most `x` with chance `∑_{j ≥ k} C(n, j) F^j (1 − F)^(n−j)`. | `measureReal_orderStat_le` | new ClassicalLean.Probability.OrderStatistics | Mathlib `ProbabilityTheory.iIndepSet` | M |
| 127 | 3 | Fejér's inequality: for convex `f` and a weight `g ≥ 0` symmetric about the midpoint, `f((a + b)/2) ∫ g ≤ ∫ f g ≤ ((f a + f b)/2) ∫ g`. | `convexOn_midpoint_mul_integral_le`, `integral_mul_le_endpoints` | ClassicalLean.Analysis.HermiteHadamard | library `convexOn_midpoint_le_average` | M |
| 128 | 3 | Euler–Maclaurin to second order, with the remainder `∫ B₂(fract t)/2 · f''`. | `sum_eq_integral_add_two` | ClassicalLean.Analysis.EulerMaclaurin | library `sum_eq_integral_add`; Mathlib `bernoulliFun_two`, `periodizedBernoulli` | M |
| 129 | 4 | Variation of constants: the one solution of `x' = A x + f(t)` is `exp(t A) x₀ + ∫₀ᵗ exp((t − s) A) f(s) ds`. | `eq_exp_smul_mulVec_add_integral` | ClassicalLean.Analysis.LinearODE | library `eq_exp_smul_mulVec`; Mathlib `intervalIntegral.integral_hasDerivAt_right` | M |
| 130 | 5 | The binary symmetric channel with crossover `ε` has capacity `log 2 − h(ε)`, reached by the uniform input. | `mutualInfo_bsc_le`, `mutualInfo_bsc_half` | new ClassicalLean.InformationTheory.ChannelCapacity | library `mutualInfo_eq_shannonEntropy_add_shannonEntropy_sub_shannonEntropy`, `shannonEntropy_le_log_card`; Mathlib `Real.binEntropy` | M |
| 131 | 5 | Han's inequality: for a joint law of `n` coordinates, `(n − 1) H(X) ≤ ∑ᵢ H(X without coordinate i)`. | `mul_shannonEntropy_le_sum` | new ClassicalLean.InformationTheory.HanInequality | library `shannonEntropy_eq_add_condEntropy`, `shannonEntropy_le_shannonEntropy_add_shannonEntropy` | M |
| 132 | 6 | Gauss–Seidel for a strictly diagonally dominant matrix: each sweep shrinks the error by at least the Jacobi factor `ρ`. | `norm_gaussSeidelIterate_sub_le` | ClassicalLean.Analysis.JacobiIteration | library `norm_jacobiStep_sub_le` | M |
| 133 | 6 | Forward substitution is backward stable: the computed solution of a lower-triangular `L x = b` solves `(L + ΔL) x = b` with `\|ΔL\| ≤ γ_n \|L\|` entry by entry (Higham 2002, Theorem 8.5). | `exists_forwardSubstComputed_eq` | ClassicalLean.Analysis.RoundingError | library `abs_prod_one_add_sub_one_le`, `gamma` | M |
| 134 | 7 | Projected gradient descent on a closed convex set has item 18's rate `L ‖x₀ − z‖²/(2k)`. | `sub_le_of_projGradientStep` | ClassicalLean.Analysis.GradientDescent | Mathlib `exists_norm_eq_iInf_of_complete_convex`, `norm_eq_iInf_iff_real_inner_le_zero`; library `le_add_inner_gradient_add_sq` | M |
| 135 | 7 | Frank–Wolfe on the simplex: for convex `f` with `L`-Lipschitz gradient, step `2/(k + 2)` gives `f(x_k) − f* ≤ 4L/(k + 2)` (the simplex has squared diameter 2). | `sub_le_of_frankWolfe` | new ClassicalLean.Analysis.FrankWolfe | library `le_add_inner_gradient_add_sq`, `closedSimplex` | M |
| 136 | 7 | One-period asset pricing, finite form (1000.yaml Q5508973): with payoff matrix `D` (states by assets) and prices `π`, no portfolio costs at most nothing, never pays less than nothing, and either costs less than nothing or sometimes pays more, exactly when there are strictly positive state prices `ψ` with `Dᵀ ψ = π`. | `exists_pos_statePrices_iff` | new ClassicalLean.Analysis.StatePrices | library `farkas` | M |
| 137 | 8 | Pólya's urn: the share of red balls is a martingale and converges almost surely. | `martingale_urnShare`, `ae_tendsto_urnShare` | new ClassicalLean.Probability.PolyaUrn | Mathlib `Submartingale.ae_tendsto_limitProcess` | M |
| 138 | 8 | Wald's second identity: for independent steps of mean 0 and variance `σ²` and a bounded stopping time, `E[S_τ²] = σ² E[τ]`. The library already has the fair `±1` case (`integral_stoppedValue_walk_sq`, GamblersRuin.lean:194); this row is the general step law. | `integral_stoppedValue_sq_eq` | ClassicalLean.Probability.FairGame | library `integral_stoppedValue_eq`; Mathlib `MeasureTheory.Martingale` | M |
| 139 | 8 | The reflection principle for the fair `±1` walk: `P(max_{k ≤ n} S_k ≥ a) = P(S_n ≥ a) + P(S_n > a)` for `a ≥ 1`. | `measureReal_max_ge_eq` | new ClassicalLean.Probability.Reflection | Mathlib `Finset.card_bij` | M |
| 140 | 9 | The Durbin–Levinson recursion solves the order-`k` prediction equations from the order-`(k − 1)` solution, with error variance `v_k = v_{k−1}(1 − φ_kk²) > 0`. | `durbinLevinson_spec` | ClassicalLean.Probability.YuleWalker | library `covariance_eq_sum`; Mathlib `Matrix.PosDef` | M |
| 141 | 10, bridge | A third proof of the minimax theorem, for every matrix, from linear-program duality; the statement is already `minimax_eq_of_matrix`, so this is a new proof only. Shared object: the payoff matrix as a constraint matrix. | `minimax_eq_of_lp` | ClassicalLean.Analysis.FiniteGame (imports Analysis.LinearProgram) | library `lp_strong_duality`, `payoff` | M |
| 142 | 10, bridge | Principal components: for orthonormal weight vectors `w₁, …, w_k`, the variances of the mixes add up to at most the sum of the `k` largest eigenvalues of the covariance matrix, with equality at its eigenvectors. Shared object: the eigenvalues of a positive semidefinite matrix. | `sum_variance_mix_le_sum_eigenvalues` | ClassicalLean.Probability.CovarianceDirections (imports Algebra.MinMax) | item 83; library `variance_mix`, `posSemidef_covMatrix` | M |
| 143 | 10, bridge | Runs and Fibonacci: in `n` fair independent trials, no two losses in a row has chance `fib(n + 2)/2^n`, and no three has chance `tribonacci(n + 3)/2^n`. Shared object: strings counted by a linear recurrence. | `measureReal_no_run_two_eq`, `measureReal_no_run_three_eq` | ClassicalLean.Probability.LongestRun (imports NumberTheory.Tribonacci) | library `runEvent`, `tribonacci`; Mathlib `Nat.fib` | M |
| 144 | 10, bridge | The Bretagnolle–Huber bound: on a finite set, every test has size plus missed-detection chance at least `exp(−D(p₁ ‖ p₀))/2`. Shared object: the likelihood ratio, inside both the test and the relative entropy. | `size_add_one_sub_power_ge` | ClassicalLean.Statistics.NeymanPearson (imports InformationTheory.Entropy) | library `relEntropy`, `IsTest` | M |
| 145 | 10, bridge | Item 65's (a) ⇔ (b), second proof by linear-program duality: prices exist exactly when the potential inequalities are feasible. Shared object: potentials (log prices) as dual variables. | `hasPrices_iff_of_lp` | ClassicalLean.Combinatorics.ArbitrageCycle (imports Analysis.LinearProgram) | library `farkas`, `NoGainCycle`, `HasPrices` | M |
| 146 | 4 | Heun's method (the explicit trapezoid) has global error of order `h²`. | `abs_sub_heunIterate_le` | ClassicalLean.Analysis.EulerMethod | library `abs_sub_eulerIterate_le` (its pattern) | M–L |
| 147 | 6 | The power method: for a symmetric matrix with `\|λ₀\| > \|λ₁\|`, the iterates' direction approaches the top eigenvector at rate `(\|λ₁\|/\|λ₀\|)^k`. | `tendsto_powerIterate` | new ClassicalLean.Analysis.PowerMethod | Mathlib `LinearMap.IsSymmetric.eigenvectorBasis` | M–L |
| 148 | 8 | Mean hitting times of a finite chain solve `h = 1 + Q h` off the target, `h = ∑_t Q^t 1`, the only solution. | `meanHitting_eq` | ClassicalLean.Probability.FiniteChain | library `sum_abs_vecMul_pow_sub_le` | M–L |
| 149 | 10, bridge | Total progeny and extinction: for an offspring law with `p 0 > 0`, the power series `T` with `T = X f(T)` (unique by the library's functional-equation theorem) sums to the extinction chance (the least fixed point of `f` in `[0, 1]`); for `f s = (1 + s²)/2` its coefficients are `C_n / 2^(2n+1)` (Catalan numbers) and they sum to 1. Shared object: the generating function and its least fixed point. | `progeny_eval_one_eq_extinctionChance` | ClassicalLean.Probability.Extinction (imports Combinatorics.AlgebraicGeneratingFunction) | library `extinctionChance`, `pgf`, `eq_of_eq_C_add_X_mul`; Mathlib `catalan` | M–L |
| 150 | L | The Moore–Penrose pseudoinverse: its four equations, uniqueness, and least squares with a rank-deficient design. | `pinv`, `pinv_spec`, `pinv_unique` | new ClassicalLean.Algebra.Pseudoinverse | library `leastSquares` | L |
| 151 | L | The chi-squared law: the sum of squares of `k` independent standard normals has the gamma law with shape `k/2` and rate `1/2`. | `hasLaw_sum_sq_gaussian` | new ClassicalLean.Probability.ChiSquared | Mathlib `ProbabilityTheory.gammaPDF`, `ProbabilityTheory.gaussianReal` | L |
| 152 | L | KKT conditions are necessary under Slater's condition (a strictly feasible point exists), for convex differentiable problems. | `exists_kkt_of_slater` | new ClassicalLean.Analysis.KKT | library `isMinOn_of_kkt`; Mathlib `geometric_hahn_banach_point_open` | L |
| 153 | 5 | Huffman's code has the least mean length among prefix-free codes. | `huffman_optimal` | new ClassicalLean.InformationTheory.Huffman | library `exists_isPrefixFree_length_eq` | L |

### Not rows, with the reason

- Wold's decomposition and the Ljung–Box test: need the Hilbert space of a stationary process and
  chi-squared limits; Mathlib has neither (`\bwold\b` has 3 hits in 1 file, all Cramér–Wold;
  `ljung` 0; pinned and master the same).
- Stochastic differential equations and Ornstein–Uhlenbeck: Mathlib has no stochastic integral
  (`stochastic integral|itoIntegral` 0, pinned and master).
- Cochran's theorem for laws: after item 151, an order of its own.
- Perron–Frobenius for nonnegative irreducible matrices (not primitive): Mathlib has the definitions
  only; after item 100.
- Max-flow min-cut and Menger (ROADMAP §2.10): an order on its own (L), better after items 141 and
  145 have shown how linear-program duality is used.
- Item 65's (a) ⇔ (b) for `r ≥ 0` and infinitely many assets: by hand only, no use in the library.
- Lean computation of item 69's 5.99 and 0.544 and item 68's 3/5 numbers: checked exactly in
  Python already; a Lean copy adds no new fact.
- The full Marchenko–Pastur law: very large; item 70 carries its practical warning.
- A finite Loomis–Whitney by entropy: Mathlib's grid-lines lemma gives it (section 3).

## 8. The per-batch method (each later order, LEAN-27 onward and VACUITY-2, VACUITY-3)

These carry the lessons of LEAN-22 to LEAN-26 and VACUITY-1.

1. **Base.** `git fetch origin`; origin/master and github master must equal the last pushed commit;
   a new branch from it; nothing in `~/trading`, nothing in `~/lean/recheck` edited; no sudo; no
   push.
2. **Records first**, one commit, no `.lean` file: the order copy, its INDEX row, a CLAIMS row, the
   round fragment naming every new module's path (check_records reads fragments, not CLAIMS).
3. **Re-check each row against Mathlib** by its line in MATH-PLAN-library-2-checks.py (re-run it;
   every row line must hit) before writing anything; a row Mathlib has by then is dropped and said.
4. **Predictions written before they are measured, each hashed when written:** the first build's
   job count is the last count plus the new modules plus the Mathlib modules the new imports pull
   in (list the import closure from the old import list and from it plus the new files' Mathlib
   imports, before any new module is loaded; LEAN-26: 4160 + 4 + 2 = 4166, a hit). The theorem
   constant count is predicted **blind**: `prediction.txt` is written before any census, vacuity
   probe or gate runs on a new module. Part 1 by Method A, from the source alone: hand-written
   theorems, `.eq_N` lemmas of each definition, one `.eq_def` per definition unfolded by `unfold`,
   matcher equations for definitions by pattern matching (LEAN-26 missed 2 of these), structure
   fields, about one `_proof_` per `omega` call (LEAN-25's rate held in LEAN-26), and about one
   `_simp_` per membership or reversed (`←`) lemma inside `simp only [...]` (LEAN-26's miss of 24).
   Part 2 by Method B, a census of scratch copies, appended and the file hashed again before the
   first gate.
5. **Statements first**, with `sorry`, in a scratch file; rc 0 and one `sorry` warning per
   statement; then the statements are final before any review.
6. **Every hypothesis gets a dropped-hypothesis row**, exact where possible, with **Lean's junk
   values** named wherever they decide the case: `x / 0 = 0`, `log 0 = 0`, `log x = log |x|`, the
   inverse of a singular matrix is `0`, `ℕ` subtraction stops at `0`, `⨆` of an unbounded family is
   `0`, the integral of a non-integrable function is `0`, conditional expectation with respect to a
   σ-algebra that is not smaller is `0` (item 50's MAJOR). **Every new main theorem with a
   hypothesis also gets a satisfiability example** in its module, an `example` that meets all its
   hypotheses at once (item 89's rule, from LEAN-27 on).
7. **A narrower statement is said plainly** wherever it appears: the module docstring, the report's
   item line and the hypothesis table (the Karlin–Rubin precedent of LEAN-24).
8. **Reviews.** A module's cold review only after its statements are final: a fresh general-purpose
   subagent with no persistent memory, its own scratch folder, a read list, told that other work
   goes on meanwhile and to run no census, probe, count or gate; `~/.claude/agent-memory/` hashed
   before and after. Any statement that changes after its review gets a statement-equivalence
   review (old statement proved from the new one in Lean, as LEAN-25 and LEAN-26 did).
9. **Gates, on the clean tree, predicted first:** `nice -n 19 lake build` (0 warnings), AxiomGate,
   VacuityGate (as VACUITY-2 leaves it), check_sorry, banned_vocab_scan, check_records, and gate 7,
   `~/lean/recheck/run-recheck.sh <commit> ~/lean/classical-lean-paper-crypto`.
10. **Check scripts set their exit code** (LEAN-26's A5 and A6 sat on the bound and only reading the
    output caught it); hashes go into the records by script, never typed (LEAN-17 to LEAN-23 each
    caught a typed hash); compile-fix runs through `el.sh` are logged too (LEAN-26 did not).
11. **Report** through ds_write_staging with post_sha256 compared; the push command as one line, not
    run; then stop.

LEAN-16's known traps all still apply (`push Not`, `integral_finsetSum`, `omit … in` before the
docstring, the `git add` hook and asterisks, `λ` not a name, the on-box lane door).

## 9. How the first batch would run, after approval

The first order is **VACUITY-2** (items 72 to 78), then **LEAN-27** (items 79 to 83).

VACUITY-2, on branch `vacuity-2` from `d2cba27` (or whatever master is then):
1. Records first (order copy, INDEX, CLAIMS, a round fragment that names no module, since no
   `ClassicalLean/` file changes).
2. Tests before the gate changes: add `vac_and_hyp`, `vac_iff_hyp`, `vac_irreducible`,
   `vac_deep_unfold` (six nested definitions before a binder; already flagged today, kept as a guard for item 74), `vac_false_hyp` (rule 5),
   `real_exfalso_helper` (a deliberate one, listed), `vac_meta_helper._proof_1` (made by `addDecl`,
   used by nothing), with predictions hashed; run the old gate on them and commit the measured
   table, as VACUITY-1 did.
3. Items 72 to 77, one commit each, each with its tests; after each, the whole test set and the
   library run (`lake env lean tools/VacuityGate.lean`), timed; the three unused helpers (item 75)
   and any rule-5 flag in the library looked at by hand before any list entry.
4. Item 78, the cold review of the final gate, before the last commit; findings applied or
   answered in the report.
5. Gates: the six gates and gate 7; constants, modules and jobs unchanged (3158, 120, 4166)
   unless a library theorem had to change.
6. Report VACUITY-2-report.md through ds_write_staging; push command as one line; stop.

LEAN-27 then follows section 8 for items 79 to 83: two new modules
(ClassicalLean.Analysis.ConvexConjugate and ClassicalLean.Algebra.Kantorovich), three extended
(Probability.EffectiveSampleSize, Statistics.GeneralizedLeastSquares, Algebra.MinMax).

## 10. The check script, its output, and these files

- MATH-PLAN-library-2-checks.py, sha256 **92eedbc6598361a06a50bdf3a1b4fa1698c1d1d7a3dfe783cc79dd9c1c38307e**
- MATH-PLAN-library-2-checks.out, sha256 **9b4e4cf12e86178dbef44f319f27c3ce439bdc8aed45d573625065be56f98c7a**: its last line reads "232 of 232 checks hit"; run on DSMain with `--lean`
- MATH-PLAN-library-2-prediction.txt, sha256 a3d7046cd6b57cb0650377d753c50688b691ca2ab7997eed540685b4e0e1206e

## 11. The cold review of this plan

One fresh general-purpose subagent, no persistent memory, its own folder
(`scratchpad/plan2/review1/`), with the read list the order gives (the order, this plan as first written,
sha256 f793584d…8d4e, the check script and output, the prediction file, the last plan's sections 3 and 6),
and about 60 tool calls (it used 39). It re-ran the check script (225 of 225 hit, output byte-identical
to the lane copy), re-ran by its own greps the search behind every Track G item and every row of
batches 1 and 2, and sampled 19 later rows (93, 97, 101, 106, 109, 113, 121, 123, 124, 126, 129, 131,
137, 138, 139, 143, 150, 151, 152), chosen as rows whose search was mostly a proper name, or whose topic
Mathlib might hold under another name, plus three the library might already have. It found no row that
Mathlib or the library already has as stated. Report `review1/r1-report.md`, sha256
e0f136a808d0dbf05c3fb0a5d1d6d14fa76f8973f1223f78c1ea94ccca33d0cc. The sha256 of the 58 files under
`~/.claude/agent-memory/` was the same before and after. Verdict: **PASS WITH FINDINGS**, 2 MAJOR,
9 MINOR. I checked each against the sources before acting; all held. Each is now a check in the
script (section 2f and the `r1.unfold` line of section 4), which grew from 225 to 232 checks.

| # | finding | done |
|---|---|---|
| 1 | MAJOR, item 74: the 4-unfolding limit is not real; one `whnf` opens all nested definitions | confirmed by re-running its probe (now check `r1.unfold`); item 74 restated as removing the dead counter and the false limit, with a guard test; section 1 corrected |
| 2 | MAJOR, item 106: `P(F(X) ≤ u) ≤ u` is false for `u < 0` | fixed: "for every `u ≥ 0`"; check `B5.pit` widened to `u ∈ [0, 2]` |
| 3 | item 97 is false without `π i = 0 → μ i = 0`, under Lean's `x/0 = 0` | fixed: the hypothesis added (it is the one `relEntropy_vecMul_le` carries, check `r1.dpi_support`) |
| 4 | item 94 rests on a lemma that needs `r ≥ 0` | fixed: `tendsto_pow_atTop_nhds_zero_iff`; the script's name list updated |
| 5 | items 79, 82, 83, 84 leave out a hypothesis | fixed: `f` real-valued (79); `m`, `M` eigenvalues for equality (82); `k ≤ n` (83); `0 < p < 1` (84) |
| 6 | items 85 and 141 restate `minimax_eq_of_matrix` | fixed: both now say they are new proofs only (check `r1.minimax`) |
| 7 | item 138's `±1` case is in the library; item 100 misses `Matrix.IsPrimitive` | fixed: both named (checks `r1.wald_pm1`, `r1.isPrimitive`); costs unchanged, since the general law and the convergence are still new |
| 8 | VACUITY-2 (7 items) and VACUITY-3 (2) are outside four to six | answered: that rule is for the math batches, LEAN-27 onward; gate orders hold what the placement rule puts in them; the merge option is stated under VACUITY-2 |
| 9 | eleven bridges do not name their shared object | fixed: every bridge row now says "Shared object:" |
| 10 | item 89 gives no cost | fixed: about 90 examples, measured from the last plan's 86 named declarations (check `r1.backfill`) |
| 11 | item 73 changes nothing today | fixed: said so in item 73 (check `r1.irreducible_values`); it stays, as a guard |

No row moved, so the ranking, the batches, the item numbers and the counts are unchanged.

## 12. Decisions that are Dustin's

1. Gate first: VACUITY-2 (items 72 to 78) runs before LEAN-27, by the order's rule. Recommended: yes.
2. The cut: six math batches of five (30 rows), ending at item 110 because the nine gate items take
   numbers too; 43 rows below it, ranked. Recommended: keep it; you may resize it.
3. The tie-break this plan adds to the order's rule (more dependents, then Track L before area
   rows, then area number). Recommended: keep it.
4. Satisfiability examples: required for every new main theorem from LEAN-27 on; backfilled only for
   the main theorems of items 1 to 71 (VACUITY-3), not for all 1068 written theorems with a
   hypothesis. Recommended: yes.
5. No Mathlib bump now: nothing in this plan is in newer Mathlib, and master is a release
   candidate. Recommended: no bump; look again when v4.35.0 is released.
6. The hidden-link bridges below the cut (items 141 to 145 and 149: minimax by linear programs,
   principal components, runs and Fibonacci, Bretagnolle–Huber, prices by duality, Catalan
   progeny) stay where the rule puts them. Recommended: keep the rule; if you want them sooner, say
   which, and they replace the last rows of batch 6.

If you approve without a note, I take the recommended answer to each.
