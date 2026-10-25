# LEAN-35 order: batch 5 of the API-credit drafts (items 114, 115, 125, 138 and 148)

For a plain Claude Code session on DSMain, as dustin, in tmux `cc`. Written by claude-ai on
2026-10-21 under lean/CLOUD-LANDING-PLAN-2.md ruling 2 (batches 3 to 7 land on DSMain as LEAN-33 to
LEAN-37; LEAN-35 is batch 5, with no VACUITY-3 row), staged at Dustin's request of 2026-10-21 15:53
EDT while no order's session ran on DSMain. It was written from file facts read at master `02ac649`
and from claude-ai's Lean runs there (LEAN-34's cut of the five drafts, and the probes below); every fact about the
master this order starts from, `f5411f4` (LEAN-34's, pushed by Dustin on 2026-10-21), was measured at
the cut, on 2026-10-21 from 21:09:52 to 21:24:06 EDT (section "Measured at the cut", filled by
script). The draft is `lean/LEAN-35/data/order-draft.md` (r2), with `fix-r3.py` and `fix-r4.py` beside
it (r3 and r4); this file, the cut, is `lean/LEAN-35/order.md`, made from r4 by `fill-cut35.py`,
`fix-cut-r1.py` and `fix-cut-r2.py` (kept with the cut's outputs in `~/api-credit/l35/cut/` on DSMain;
its two review reports are `lean/LEAN-35/data/rv-cut-pass1.txt` and `rv-cut-pass2.txt`). Lane files named `lean/...` are under
/opt/datasphere/lane/inbox/threads/staging/lean/ (ds_* tools: root `lane`, path
`inbox/threads/staging/lean/...`). Its inputs are `lean/LEAN-35/data/` and LEAN-33's two type-dump
scripts in `lean/LEAN-33/scripts/`.

**New lane files go through `ds_file`** (project `lean`, job `LEAN-35`): your plan is kind `plan`
(it lands as `lean/LEAN-35/plan.md`; a second becomes `plan-r2.md`, never overwriting), the report
kind `report`, the push-review file subdir `data`, name `LEAN-35-push-review.txt`. Compare each
reply's `post_sha256` with your own. Appending to the bridges file (job 5b) is `ds_write_staging`
in append mode with `expect_sha256`. **Track the order's steps with the task tools** (lane
`lean/NOTE-20261015-task-list-rule.md`).

Review: the draft, on 2026-10-21, by a fresh subagent (pass 1: FAIL, 1 BLOCKER, 2 MAJOR, 9 MINOR,
all applied, r1) and a confirming pass by another (all 12 fixed, 7 new MINOR, applied, r2; r2 not
reviewed again); r3 added rules 11 to 13 after LEAN-34's run, and r4 changed rule 11 and 5f. The cut
(its values, filled by `fill-cut35.py`, and rules 11 to 13) was cold-reviewed on 2026-10-21 by a fresh
subagent: pass 1 PASS WITH FINDINGS, 0 BLOCKER, 1 MAJOR (the copied `commit.sh` named LEAN-34's
session), 10 MINOR, applied by `fix-cut-r1.py`; a confirming pass by the same reviewer, CONFIRMED WITH
FINDINGS, 9 fixed, 2 held for the final fill and done there, 5 new MINOR, applied by `fix-cut-r2.py`,
which was not reviewed again. Not reviewed: any Lean
beyond the drafts' compile and claude-ai's probes (the placements in the modules and the import lines
alone were measured at the cut; the witness hints were not elaborated); MERGE-2's order, `records/README.md` and the helpers' code.

## What is already true

### Measured by claude-ai on 2026-10-21 from 16:00:35 to 16:50:35 EDT, at `02ac649`

On DSMain over ssh from helios, in claude-ai's clones of master
`02ac649b17f66e39327022462ee4d3d9a73b62d4` (MERGE-3's last commit, pushed by Dustin; store row
20261021-012): file reads in `/tmp/claude-ai-m3/push/repo` (`gather1.sh` at 16:00:35 EDT,
`gather2.sh` at 16:02:11 EDT, `gather3.sh` at 16:28:59 EDT; no Lean process), claude-ai's Lean probes
(`probe1.sh` and probe 2, from 16:49:56 to 16:50:35 EDT on 2026-10-21, each prediction written first,
in `~/api-credit/cl-02ac649`), and the five drafts
compiled in `~/api-credit/cl-02ac649` by LEAN-34's cut (`cut-l34.sh`, 16:05:56 to 16:06:29 EDT, its
lines `f4-d114-r1-s2` to `score-d1148-r1-s1` in `lean/LEAN-34/data/cut-facts.txt`, sha256
`0d7ef8d48aac219d34436942b0c9ee5c6486cf45344078531c133a4ee545baa9`). The five outputs are kept in
`~/api-credit/l35/` on DSMain: `gather1.out`
`a2a1c703c5dd1c4902e89d977fab14bbcdc070d9562740d047bac3d857522b6a`, `gather2.out`
`a75c13c3be343aa31e5be646160c674c2533ea1f276352a3d54c1a8baf451b84`, `gather3.out`
`4cacdfa9a0b4df9aeed8d8f4a8dd9cfedae1bdd771776aab6f9ef73438c9aa21`, `probe1.out`
`aa481daa83adb9cf2d75827af269ea90acbca45410d07f1986a734383305c849`, `probe2.out`
`7eac87502f0352e1c0c2dad7e77d0e044f7a1d5d073e0fe1580601ed789f1d8f` (the predictions `pred-probe1.txt` and
`pred-probe2.txt` and the script `probe1.sh` beside them; probe 2 ran from one command line; the probe
files and their outputs in `~/api-credit/l35/probe/`); the cut keeps the five, joined in that order, as
`~/api-credit/l35/facts.txt` on DSMain, not copied to the lane (read only for you, Scope; sha256 `0a9e7c93ba419245432c07ba6519c0ca4665aad1ed2674c547d1642efdd3f0c0`;
each part under a header line with its own sha256; `gather2.out` holds 4 invalid UTF-8 sequences, from a
`cut -c` that split a character, shown there as U+FFFD).

- **The five drafts** (in `/data/api-credit/20261019/carry/`, read-only, whose `SHA256SUMS` is
  a2f5e552; the same bytes in `~/api-credit/drafts/`, `cmp`). Each imports its home module (d114
  also `ClassicalLean.Probability.FirstOrderRecursion`; d115 also
  `ClassicalLean.Probability.EffectiveSampleSize` and `Mathlib.Analysis.SpecificLimits.Basic`) and
  declares at the root namespace. None holds `sorry`, `admit`, `native_decide`, `implemented_by`,
  `axiom` or `set_option` (grep). At `02ac649` each compiles with rule 20's four flags, rc 0, and
  the API-credit pipeline's scorer (`#print axioms` lines appended) gives every named theorem only
  `propext`, `Classical.choice` and `Quot.sound` (cut-facts.txt).

  | item | draft | sha256 | home module | its declarations | last review (work/api-credit/API-CREDIT-1/API-CREDIT-1.md, lean/API-CREDIT-CARRY-1.md) |
  |---|---|---|---|---|---|
  | 114 | d114-r1-s2 | `738ef6e34c08e1ec1a70ad45f3f3af128e5bf52cc0a2e1294ce9487634d50d1c` | Probability.KalmanVariance | the theorem `riccatiRoot_eq_steady`; `open ClassicalLean.Probability` (line 4) | round 1's cold review (line 59): carry s2; its optional strengthening "state the error recursion" |
  | 115 | d115-r2-s1 | `7d3cb62e762745679e6dc5b2b9b3edf8f20ea5ed68f66036664dcc47a468444c` | Probability.MovingAverage | the private def `maCov`, the private lemma `sq_sum_eq`, the theorem `variance_sum_movingAverage`; a `variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}` line (line 8); `open MeasureTheory ProbabilityTheory Finset Filter Topology` and `open ClassicalLean.Probability` (lines 5 and 6) | review r5 (line 120): FAITHFUL; carry r2-s1 |
  | 125 | d125-r3-s2 | `5104b69e740b730a5960e0914c22602156de8b8f4c3f87b32e8ffb9ce825db86` | Probability.MaximalInequality | the private def `hajekW`, the private lemmas `hajekW_zero` and `hajekW_succ`, the theorem `measureReal_exists_mul_abs_ge_le`; `open MeasureTheory Filter Finset` and `open scoped NNReal` (lines 3 and 4) | round 1's cold review (line 59): GENERALIZED; carry s2 |
  | 138 | d138-r1-s1 | `e7e9c4ee91e112bcc74fae9c47792002e4ba6c3ab95ae1f93eefa54443c4ede8` | Probability.FairGame | the theorem `integral_stoppedValue_sq_eq`; `open MeasureTheory ProbabilityTheory Finset` (line 3) | review r6 (line 142): GENERALIZED; carry s1 |
  | 148 | d1148-r1-s1 | `0099e0f7f961ececeb3c55f4acf155ffc92957fb78983ff40bd2468def1145cb` | Probability.FiniteChain | the private `one_sub_mul_le_pow_aux`, the theorems `meanHitting_eq` and `meanHitting_eq_of_le`; a module docstring (lines 3 to 12); `open Finset Filter Topology Matrix` (line 14) | the amendment of d148-r2-s1, which review r6 found WEAKER (line 142, its major at line 144); review r7 (lines 172 to 175): FAITHFUL, carry d1148-r1-s1 |

  With the four flags at `02ac649` (cut-facts.txt): d114 no warning; d115 a `show` linter line
  (line 68), and "this tactic is never executed" with the unused-tactic linter at line 135 (a
  `ring` that does nothing); d125 one `show` line (127); d138 the deprecated
  `MeasureTheory.memLp_finset_sum` (line 21) and one `show` line (45); d1148 nine `show` lines.
- **Their plan rows** (MATH-PLAN-library-2.md, at the lane root's `inbox/threads/staging/`, not in
  the `lean/MATH-PLAN-library-2/` folder, which holds the bridges file; section 7, lines 423, 424,
  434, 447 and 457; gather3.out): 114 (bridge, home importing Probability.FirstOrderRecursion) the steady Kalman filter
  for a local level (`a = h = 1`) is exponential smoothing with constant `K = P*/(P* + r)`,
  `P* = riccatiRoot`, and its error is a first-order recursion with coefficient `1 − K` whose steady
  variance `(q + K² r)/(1 − (1 − K)²)` equals `P*`; 115 (bridge, home importing
  Probability.EffectiveSampleSize) for `n > q`, `Var(X 0 + ⋯ + X (n − 1)) = n v (∑ θ)² − 2 ∑_{k ≤ q}
  k γ(k)`, so `n Var(mean) → v (∑ θ)²`; 125 the Hájek–Rényi inequality, for a square-integrable
  martingale and weights `c₁ ≥ c₂ ≥ ⋯ > 0`, `P(max c_k |S_k| ≥ ε) ≤ ε⁻² ∑ c_k² E[ξ_k²]`; 138 Wald's
  second identity, for independent steps of mean 0 and variance `σ²` and a bounded stopping time,
  `E[S_τ²] = σ² E[τ]`, "the general step law" beside the library's fair `±1` case
  `integral_stoppedValue_walk_sq` (the row says GamblersRuin.lean:194; it is at line 304 at
  `02ac649`, gather2.out); 148 mean hitting times of a finite chain solve `h = 1 + Q h` off the
  target, `h = ∑_t Q^t 1`, the only solution.
- **The drafts' statements** (gather3.out), for the plan-fit check:
  - 114: `riccatiRoot 1 1 q r = (q + K² r)/(1 − (1 − K)²)` with `K = riccatiRoot 1 1 q r /
    (riccatiRoot 1 1 q r + r)` written out, under `hq : 0 < q` and `hr : 0 ≤ r`; the row's filter and
    its error recursion are in the draft's docstring (lines 6 to 8, with `w` and `v` undefined there),
    not in the statement. Round 1's review counts it FAITHFUL (line 59: every item states the
    planned theorem, GENERALIZED only for 113, 123 s1 and 125).
  - 115: `[IsFiniteMeasure μ]`, white noise as `he : ∀ t, MemLp (e t) 2 μ` and `hcov : ∀ s t,
    cov[e s, e t; μ] = if s = t then v else 0`; two clauses: for every `n > q` the variance of the
    sum of `movingAverage q θ e t` over `t < n` is `n v (∑_{j ≤ q} θ j)² − 2 ∑_{k ≤ q} k
    cov[movingAverage q θ e k, movingAverage q θ e 0; μ]`, and `n · Var(sum / n)` tends to
    `v (∑_{j ≤ q} θ j)²`.
  - 125: `[IsFiniteMeasure μ]`, a filtration `𝒢`, `hS : Martingale S 𝒢 μ`, `hS2 : ∀ n, MemLp (S n) 2
    μ`, `hc : ∀ k, 0 < c k`, `hanti : Antitone c`, `hε : 0 < ε`, `n : ℕ`; the chance (`μ.real`) that
    `ε ≤ c k * |S k ω|` for some `k ≤ n` is at most `(c 0² E[S 0²] + ∑_{k < n} c (k + 1)²
    E[(S (k + 1) − S k)²]) / ε²`, so `ξ 0 = S 0`.
  - 138: `[IsProbabilityMeasure μ]`, steps `X n` known at time `n + 1` (`hX`), square integrable
    (`hL2`), of mean 0 (`hmean`) and second moment `σ²` (`hvar`), each independent of `𝒢 n`
    (`hind`); `hτ : IsStoppingTime 𝒢 τ` with `hbdd : ∀ ω, τ ω ≤ N`; the conclusion
    `E[(stoppedValue (fun n ω ↦ ∑ i ∈ range n, X i ω) τ)²] = σ² E[(τ ω).untopA]`.
  - 148: `meanHitting_eq`: `hP : ∀ i, ∑ j, P i j = 1`, `hP0 : ∀ i j, 0 ≤ P i j`, `hreach : ∀ i ∉ A,
    ∃ t, ∃ a ∈ A, 0 < (P ^ t) i a`; with `Q` the chain killed on entering `A`, `u` the indicator of
    the complement of `A` and `h i = ∑' t, (Q ^ t *ᵥ u) i` (three `let`s in the statement): every
    series is summable, and `g` solves `g = 0` on `A`, `g i = 1 + ∑ j, P i j * g j` off `A` exactly
    when `g = h`. `meanHitting_eq_of_le` (the old WEAKER statement, kept as a corollary): `hP`,
    `hδ0 : 0 < δ`, `hδ : ∀ i j, δ ≤ P i j`, `hA : A.Nonempty`, the same conclusion.
- **The reviews' minor findings for these drafts** (API-CREDIT-1.md lines 59, 120, 148 and 174), and
  what this order does with each: every draft at the root namespace goes into its module's namespace
  (taken); 114's optional "state the error recursion" (not taken: it needs a definition of the filter
  and its error recursion, which the library does not have; the Goal list says how the docstring
  speaks of them); 115 r5's "compile each placed module
  once to catch cycles and name clashes" (taken: job 2), and its list of the import lines the drafts
  add, "115: EffectiveSampleSize" (taken: Goal list); 148 r6's "a docstring" (it has them) and r7's
  "the corollary's docstring says 'if nonempty' though `hA` assumes it" (taken: Goal list); r7's "the
  plan's names column lacks the names the amendments added" (`meanHitting_eq_of_le` is named in round
  72's fragment and the report).
- **Names.** No name the drafts declare occurs anywhere under `ClassicalLean/` (`grep -w`,
  gather2.out). The library names they use exist where expected: `riccatiRoot` (KalmanVariance line
  78), `riccati_equation_riccatiRoot` (86), `riccatiRoot_pos` (105), FirstOrderRecursion's
  `eq_steady_iff` (its line 101); `movingAverage` (MovingAverage 88), `covariance_movingAverage` (97);
  EffectiveSampleSize's `sum_sum_lag_eq_range` (its line 474), `sum_sum_lag_eq` (496) and
  `variance_sum_range_eq_of_stationary` (568), which d115 calls as `EffectiveSampleSize.…` (its lines
  81 to 84; probe1.out);
  `submartingale_sq` (MaximalInequality 300), `measureReal_exists_abs_ge_le` (321);
  `integral_stoppedValue_eq` (FairGame 65), `integral_stoppedValue_eq_mul` (88); `sum_abs_vecMul_pow_sub_le`
  (FiniteChain 232), which the row names and the amended draft does not use.
- **Imports, by a text parse of every `import` line** (gather2.out; a parse, not Lean; the cut
  confirms with Lean): KalmanVariance imports only Mathlib (lines 7 and 8), and FirstOrderRecursion
  imports only Mathlib, so `import ClassicalLean.Probability.FirstOrderRecursion` in KalmanVariance
  makes no cycle; FirstOrderRecursion is not yet in KalmanVariance's closure, and is in the root's.
  EffectiveSampleSize's closure does not hold MovingAverage, so `import
  ClassicalLean.Probability.EffectiveSampleSize` in MovingAverage makes no cycle; EffectiveSampleSize
  is not yet in MovingAverage's closure (MovingAverage's only import is
  `Mathlib.Probability.Moments.Covariance`, its line 7), and is in the root's; d115 calls three of its theorems (above), so MovingAverage needs that
  import line (claude-ai's first reading, that d115 used nothing of it, was wrong: store row
  20261021-017). `Mathlib.Analysis.SpecificLimits.Basic` is already in MovingAverage's closure, so
  d115's line 3 is not needed. d125, d138 and d1148 import only their home modules. Importers:
  KalmanVariance, MovingAverage and FiniteChain only the root file; MaximalInequality
  Probability.GamblersRuin, Probability.RuinBound and the root; FairGame Probability.GamblersRuin and
  the root.
- **The five home modules at `02ac649`** (sha256; namespace; where its block ends; what follows),
  none touched by LEAN-34:
  - `ClassicalLean/Probability/KalmanVariance.lean` `0fa0e58cecc22b8ae6b0e4a5d6185a2513a51ea9fd2014f7dac838e392d30ccc`, 239 lines; `open Filter Topology` (line 70); `namespace ClassicalLean.Probability` (line 72) to its `end` at line 233; no `variable` line; one witness after the block (its example at line 238, of `tendsto_riccatiStep` at `a := 1 / 2`, `h := 1`, `q := 1`, `r := 1`).
  - `ClassicalLean/Probability/MovingAverage.lean` `330a719b8c6240c121aea15334901cff2c2e4cca12c702c90ebb8bf329f69b73`, 612 lines; `open MeasureTheory ProbabilityTheory Finset` (line 80); `namespace ClassicalLean.Probability` (line 82) to its `end` at line 254; `variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}` (line 84, the same as d115's line 8) and `variable [IsFiniteMeasure μ]` (line 91) for the rest of the block; three witnesses after it (lines 256 to 612), each behind `open MeasureTheory ProbabilityTheory in` and `open scoped ENNReal in`, the first of `covariance_movingAverage` (its example at line 265).
  - `ClassicalLean/Probability/MaximalInequality.lean` `4700cdfcd13eba73a05c2e6997773365efb893e0251f1de703acaed2f18be70c`, 605 lines; `open MeasureTheory Filter Finset` (line 96, d125's line 3); `namespace ClassicalLean.Probability.MaximalInequality` (line 98) to its `end` at line 526; `variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]` and `{𝒢 : Filtration ℕ m0} [SigmaFiniteFiltration μ 𝒢]` (lines 100 and 101); `section Independent` (193 to 288, with its own probability-measure `variable` line), `section Kolmogorov` (290 to 344, with `open ProbabilityTheory` and `open scoped NNReal`, `submartingale_sq` and `measureReal_exists_abs_ge_le`), `section DoobL2` (346 to 524); two witnesses after the block (lines 528 to 605, on `Ω := Fin 2`).
  - `ClassicalLean/Probability/FairGame.lean` `aff5c323c52169a7c2338eb1a32668e4dec11dd8be2772581817e37901249d78`, 178 lines; `open MeasureTheory ProbabilityTheory Finset` (line 56, d138's line 3); `namespace ClassicalLean.Probability.FairGame` (line 58) to its `end` at line 138; `variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}` and `[SigmaFiniteFiltration μ 𝒢]` (lines 60 and 61); one witness after the block (lines 140 to 178, on `Ω := Fin 2`).
  - `ClassicalLean/Probability/FiniteChain.lean` `d183f2943908287fb21ecdd21f7413eacfa7fa8fb6a1741e1a477f5e4793a2bb`, 465 lines; `open Finset Filter Topology Matrix` (line 167, d1148's line 14); `namespace ClassicalLean.Probability` (line 169) to its `end` at line 408; `variable {n : Type*} [Fintype n]` (line 171); five witnesses after the block (lines 410 to 465, each behind `open Matrix in`, on `n := Fin 2`).

  KalmanVariance, MovingAverage and FiniteChain share the namespace `ClassicalLean.Probability`, so
  a new name in one must not exist in the others (the cut's name check is under that namespace).
- **claude-ai's probes in Lean** (probe1.out, probe2.out; scratch files importing a home module,
  elaborated in `~/api-credit/cl-02ac649`; their predictions written first, and probe 1's on 138
  missed, store row 20261021-018): from FairGame alone none of `MeasureTheory.Measure.infinitePi`,
  `ProbabilityTheory.iIndepFun_infinitePi` and `ProbabilityTheory.iIndepFun.indep_comap_natural_of_lt`
  is reachable (three "Unknown" errors); with `import Mathlib.Probability.ProductMeasure` and `import
  Mathlib.Probability.BorelCantelli` the second is still unknown (it is in
  `Mathlib/Probability/Independence/InfinitePi.lean`, line 125); with `import
  Mathlib.Probability.Independence.InfinitePi` and `import Mathlib.Probability.BorelCantelli` all three
  are (rc 0). GamblersRuin's witness of `measureReal_hit_eq` (its lines 1135 to 1160) uses all three,
  and GamblersRuin reaches them through MaximalInequality (which imports BorelCantelli) and its other
  imports, so both modules are in the root's closure. No finite space can carry 138's witness: `hX`
  and `hind` make the steps `X 0, X 1, …` independent, and `hvar` with `σ ≠ 0` makes each one
  nonconstant (with `σ = 0` the witness is degenerate, rule 3). And in a file importing FiniteChain,
  Mathlib's Bernoulli inequality `one_add_mul_le_pow` (`-2 ≤ a → 1 + n * a ≤ (1 + a) ^ n`) at `a := −x`
  proves 148's helper statement `1 − m * x ≤ (1 − x) ^ m` in two lines (rc 0).
- **Witness hints, worked by claude-ai** (`lean/LEAN-35/data/hints.py`, sha256
  `e9dcd9655a0c2c462544da1e82da7cb53069b0e3a4326233ad21a67669f03896`, and its output
  `lean/LEAN-35/data/hints.out`, `9ed205547d8a8802d0e2b07d1e150319d1b22dd120d690485417aac72aa9b948`;
  exact arithmetic except 114's square root and 148's `Fin 2` series, shown as a 400-term partial sum in
  floating point, whose limit 4 is a geometric sum; not elaborated in Lean; check them):
  - 114: `q = r = 1`: `P* = (1 + √5)/2`, `K = P*/(P* + 1)`, and `(q + K² r)/(1 − (1 − K)²) = P*`. With
    `r = 0`, `K = 1` and the error recursion's coefficient `1 − K` is `0`: avoid it.
  - 115: `q = 2`, `θ j = j + 1` (weights `1, 2, 3`), `v = 1`, the noise of the module's first
    witness (its lines 256 to 375): `γ = (14, 8, 3)`, the variance of the sum of `n` terms
    `36 n − 28` for `n > 2` both ways (checked for `n = 3` to `7`), and `n Var(mean) → 36 =
    v (∑ θ)²`.
  - 125: `Ω = Fin 2` with the uniform law, as the module's witnesses; `S 0 = 0` and `S n = (1, −1)`
    for every `n ≥ 1`, as the module's Kolmogorov witness (its line 535), a martingale for the
    filtration that knows nothing at time 0 and everything after;
    `c k = 1/(k + 1)` (positive and antitone), `ε = 1/2`, `n = 2`: left side 1, right side 1.
  - 138: coin sequences `ℕ → Bool` with independent fair coins, the coins' filtration, `X n = ±1`
    read from coin `n + 1`, `σ = 1`, `τ = 1` when coin 1 is true and `2` otherwise (an event of the
    coins known at time 1), `N = 2`: `E[S_τ²] = 3/2 = σ² E[τ]`, built as GamblersRuin's witness of
    `measureReal_hit_eq` builds its space, with FairGame's two new Mathlib import lines (Goal list).
  - 148: `n = Fin 3`, `P = !![0, 1, 0; 0, 0, 1; 0, 0, 1]`, `A = {2}`: `h = (2, 1, 0)` solves the
    system, and state 0 reaches `A` only in two steps (so `hreach` is not met in one step); the
    corollary on `Fin 2`, `P = !![3/4, 1/4; 1/4, 3/4]`, `δ = 1/4`, `A = {1}`: `h 0 = 4 = 1 + (3/4) · 4 +
    (1/4) · 0`.
- **The type dump (rule 14):** LEAN-33's lane copies of rule 14's pair, `lean/LEAN-33/scripts/TypeDumpPI.lean`
  (`1fcb69f41ddbd35f84862521d2ead5946a0bd52caf5f60b6d10e966cfd9776ff`) and
  `lean/LEAN-33/scripts/g8-typediff.py` (`371eda9a2e5065abaa8f36bac9872d0f15e7bade72a248d5f0f88f20b4eacb71`;
  copy it back as `g8_typediff.py`).
- **Timers on DSMain** (read on 2026-10-20 for LEAN-33): memory-index at midnight; restic,
  ds-hygiene, the daily verify, lean-nightly and the backup bundle between 2 and 4 in the morning;
  the store sync before 6; w29-tracker and w29-sysmap every few minutes (they load no Lean). Read
  them again before you start (Scope).

### Measured at the cut (claude-ai, on 2026-10-21 from 21:09:52 to 21:24:06 EDT, at `f5411f4`)

In claude-ai's own clone `~/api-credit/cl-f5411f4` of the master this order starts from, its own
build (begun from claude-ai's `02ac649` build directory; lake rebuilt 8 modules, the 6 LEAN-34
changed, `Statistics.ResidualVariance` and the root, as `build.out` shows); outputs in `/tmp/claude-ai-l35/cut/` on DSMain (kept in `~/api-credit/l35/cut/`, the
type dumps but one left out, since all four are byte for byte the same), gathered in
`lean/LEAN-35/data/cut-facts.txt` (sha256 `e76ee732d012027c1ca8da273500c39cffc9d0bdacc77e5b3dcc7e8277affa4e`): the file facts at
21:09:52 EDT (`gather-cut.sh`), the Lean runs from 21:13:56 to 21:24:06 EDT (`cut-l35.sh`), their
prediction `pred-cut.txt` written first. Every prediction held but two: the copy that keeps 148's helper
warned once more than predicted (below), and the probe with ProductMeasure alone gave two Unknown
errors, not one (as it did at `02ac649`); lake's 8 rebuilt modules were not predicted. No order's
session ran on DSMain then (LEAN-34's had ended; the trading session runs no Lean), and `pgrep -ax
lean` was empty before the runs.

- **Master.** Both remotes (`/data/git/classical-lean.git` and GitHub) at `f5411f4d37ea5becc011c803dccc79e9ca4dc9f6`, LEAN-34's
  last commit, pushed by Dustin (DSMain's bare master ref written 2026-10-21 20:51:51 EDT; store row
  20261021-049); its GitHub CI run 39702251944 (workflow CI) ended `success` (12m0s, started
  2026-10-22T00:51:54Z). At it: `lake build` 4193 jobs, 0 warnings; AxiomGate PASS 3574;
  VacuityGate PASS with 1 reviewed helper and 0 VACUOUS-PENDING; check_sorry PASS 140; check_records PASS 140 (106
  records files, 1 named exemption, `Simplex/Hessian.lean`); `compile_rules.py drift` PASS; rule 27's module count
  (`env.header.moduleNames.size` of a scratch file importing `ClassicalLean`) 5729 (it counts
  Mathlib's modules too).
- **Records at it:** the last round is 71 (LEAN-34,
  `records/rounds/20261021T222600Z__round-71-karlin-rubin-sanov-durbin-levinson-pca-bretagnolle-huber-bsc-cascade.md`),
  so this order's is 72; 106 records files. LEAN-34's push, for your records commit (records/README.md
  rule 2), is the text
  ``; pushed by Dustin: DSMain's master ref written 2026-10-21 20:51:51 EDT, GitHub master equal (`f5411f4`)``
  (from its `;` to its `)`) inserted at one anchor in each of two rows, both their files' last lines at
  `f5411f4` (cut-facts.txt): in `records/orders/INDEX.md` (72 lines) LEAN-34's row, right after
  ``one bridge found (row 164, lane `MATH-PLAN-library-2-bridges-2.md`)`` (once in the file); in
  `records/CLAIMS.md` (64 lines) LEAN-34's row, right after `after claude-ai's push review` (three
  times in the file, once in its last line, at that line's end). Do it by a script that finds each row
  as its file's last line and checks its start (INDEX: `| LEAN-34 |`; CLAIMS: `| 2026-10-21 22:25` and
  that the line contains ``executing order `LEAN-34` ``), refuses unless the anchor occurs once in that
  line, inserts before anything is appended, and asserts, before inserting, exactly this (a fenced
  block, so spaces count; `A1` is the INDEX anchor and `A2` the CLAIMS anchor above, `i` where each
  starts in its line, `line` the file's last line without its newline):

  ```
  INDEX:  after = line[i + len(A1):]; assert after.startswith(" | `6684c41` (records); ")
  CLAIMS: after = line[i + len(A2):]; assert after == " |"
  ```

  The latest bridge baseline is `records/bridges/LEAN-34/` (`COMMIT` names
  `105850104d0f9c7a6603ec72f901e3b7792b778f`, LEAN-34's G; `pairs.tsv` 3068 lines, `shapes.tsv` 772);
  `tools/vacuity_reviewed.txt` holds 1 entry, `ClassicalLean.Simplex.orderedSimplex_subset_closedSimplex`;
  ROADMAP.md's last section is 1.28 (line 839), so yours is 1.29.
- **The worktree** `~/lean/classical-lean-paper-crypto` is on branch `lean-34` at `f5411f4`,
  clean. Remotes: `origin` the bare repo, `github` GitHub.
- **The five home modules at `f5411f4`:** all five byte for byte as at `02ac649`, each sha256 equal
  (as predicted: LEAN-34 changed none of them); their importers as at `02ac649`: KalmanVariance,
  MovingAverage and FiniteChain only the root file; MaximalInequality Probability.GamblersRuin,
  Probability.RuinBound and the root; FairGame Probability.GamblersRuin and the root; GamblersRuin
  itself only the root.
- **The drafts at `f5411f4`:** the scorer (each draft with `#print axioms` lines appended,
  `-DmaxHeartbeats=400000`) rc 0 for all five, every named theorem depending only on `propext`,
  `Classical.choice` and `Quot.sound`; with the four flags rc 0 and the same warnings as at `02ac649`
  (above), no error. Names: a Lean `env.contains` check of every name the drafts declare, under its
  home namespace, under `ClassicalLean.Probability` where that differs and at the root: 29 checked,
  0 exist.
- **Lean checks of the Goal list,** each a scratch copy of the home module with the Goal list's
  changes and the drafts' proofs, elaborated with the four flags: KalmanVariance with 114 and its
  import line: rc 0, no warning; MovingAverage with 115 and its EffectiveSampleSize import line: rc 0, only the draft's
  three warning lines (its `show` line, and two for the `ring` that is never executed), now at the copy's lines
  314 and 381;
  MaximalInequality with 125 after `end DoobL2`: rc 0, only the draft's `show` line (the copy's line 648); FairGame with 138 and its two Mathlib import
  lines: rc 0, only the draft's `memLp_finset_sum` deprecation and `show` line (the copy's lines 156
  and 180); the witness on coin sequences is not in the cut's copy: it is yours (rule 5), from the hint
  and GamblersRuin's witness, and the probes below reach its three Mathlib names; FiniteChain with 148, its helper replaced by
  `one_add_mul_le_pow` at its one use (the draft's line 189 becomes three lines, `have hb : 1 - (N : ℝ) *
  ((1 - c) / (2 * N)) ≤ (1 - (1 - c) / (2 * N)) ^ N` by `one_add_mul_le_pow (a := -((1 - c) / (2 * N)))
  (by linarith) N` and `simpa [sub_eq_add_neg]`): rc 0, only the draft's nine `show` lines; a second
  copy that keeps the helper and gives it that two-line proof is rc 0 too, but warns that its `h0` is
  then unused, so the helper goes. No copy warned for an unused section variable or instance. The import lines alone, added in claude-ai's clone and then restored, one module
  at a time (KalmanVariance's; MovingAverage's; FairGame's two together): each build rc 0, 4193 jobs,
  rebuilding KalmanVariance and the root; MovingAverage and the root; FairGame, GamblersRuin and the
  root; each type dump against the base's `DIFF removed=0 added=0 changed=0 proof_only=0`, as
  predicted; after each restore porcelain 0 and the build rc 0 (the EffectiveSampleSize line brings its closure, LinearPrediction and RecurrenceGeneratingFunction among
  it, into a module inside `namespace ClassicalLean.Probability`, where a library name can capture an
  unqualified name in an existing proof, which the build and the dump would show). The probes above
  again at `f5411f4`: each output equal to its `02ac649` one once file paths are removed (from
  FairGame alone, three Unknown errors; with ProductMeasure, two; with ProductMeasure and BorelCantelli,
  one, `iIndepFun_infinitePi`; with Independence.InfinitePi alone, one,
  `iIndepFun.indep_comap_natural_of_lt`; with Independence.InfinitePi and BorelCantelli, rc 0; the
  Bernoulli probe rc 0).
- **The type dump at `f5411f4`:** 4058 records (3574 thm, 484 def), none dropped; `check`: elided 0, missing_fields 0; the dump against
  itself all zeros.
- **Helpers:** LEAN-34's, in `~/lean/lean34-checks/scripts/` and `~/lean/lean34-checks/census/`, with
  each file's sha256, the path lines Setup 1 changes and their counts: 27 scripts in `scripts/` and the
  two census tails `census/census-all-tail-lean28.lean` and `census/census-tail-lean28.lean` (the other
  entries in LEAN-34's `census/` are its outputs and sources, not helpers: do not copy them); their full
  sha256s in cut-facts.txt (its `gather-cut.out` section, "helpers (LEAN-34's)"); lines naming
  `lean34-checks`: `commit.sh` 1, `docs-insert.py` 1, `el.sh` 1, `evcite.py` 2, `ev.sh` 1, `hl.sh` 1,
  `mkcensus.sh` 1, `probecheck.py` 1 (its line 27, `D = '/home/dustin/lean/lean34-checks'`),
  `records2.py` 1, `rootrun.sh` 1, the other 17 none; one `BASE = ` line, `probecheck.py`'s line 29,
  `BASE = '02ac649'`; `commit.sh` line 16 carries LEAN-34's two attribution trailers (`Co-Authored-By: Claude
  Opus 5.5 <noreply@anthropic.com>` and `Claude-Session:
  https://claude.ai/code/session_01SYJof36hVcDcFdNyijRw19`; LEAN-34 changed its own copy as
  `adapt-commit-2`, its evidence.log line 42); `allowlist.txt` sha256
  `06f4de72c39476fd6819d0f0b14ed436000e8ba4c3f003860dee97443c84cb00`, 27 lines (LEAN-34 added three
  tokens, each with its reason in its report); no `seed.txt`. LEAN-34's `pushreview.sh` and
  `mkwitcheck.py` are in its `evidence/`, not `scripts/`; rule 13 takes the witness check from the lane.
- **LEAN-34's runs, the pattern for your gates:** the vacuity tests 89 tests, 47 flagged, 0 rule-5
  run-outs, 0 mismatches, rc 0 (`g3-tests.out` line 93); gate 7 ALL PASSED for `1058501` in 23:19.71
  wall clock, 1399.71 seconds (`g7.out` line 40; the planted fault
  `ClassicalLean.Analysis.LogDrag.mean_log_one_add_le` named at its line 33); the report tool's output
  `~/lean/lean34-checks/report.out` (sha256
  `ec5643b7f53d6d5f1bfca59215fa7f7f80609f8fc9af4450643fe81f27829d21`, 1260 lines): 1981 written
  theorems; A, with a hypothesis, 1180 (CLOSES 0, OPEN 1135, DEPENDENT 45); B, with none, 801 (CLOSES
  `simp` 15 and `positivity` 1, OPEN 785); C, Prop-valued definitions, 37 (0 recursive); self-test
  mismatches 0.
- **The bridges file** `lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md` is `08773508fcdddda22e1a13d6bc2d24882f2825563261226460bf27f80a6ada2f`;
  its last row is 164 (LEAN-34's, a Pinsker bound for tests), so new rows start at 165.
- **LEAN-34's order and report** (`lean/LEAN-34/order.md`, `b4869d7c17cfc1d92750b39c424019346770dfaf880680f074f8736fe66b02dd`; its report
  `lean/LEAN-34/report-r2.md`, `90f1bd8b3c78a8e86b0ee6172cc33b8cb3e76a40826e592e6de9178cdf6f76e8`, which
  replaced `report.md` after claude-ai's push review): what this order takes from them: rule 13, the
  witness check (from its cut-short witness), and rules 11 and 12 (from what went wrong while it ran);
  its `allowlist.txt` as it is; `pgrep -ax lean`; full paths in every `ev.sh` command (a run with
  relative paths changed nothing, one of its misses); every name probed before `el.sh` can refuse it
  (it probed seven only after a refused run); the report tool at G; and Setup 2's allowlist test
  predicting no new line on either `el.sh` run (LEAN-34's plan, store row 20261021-029).

## Goal

The five items proved in their home modules, each inside its module's namespace, with witnesses,
reviews and records; no existing declaration changed (the type dump shows it); every gate passing,
gate 7 included; the bridge search and the report tool run; HANDOFF.md and ROADMAP.md saying what
changed. Dustin pushes after claude-ai checks the push-review file.

The changes asked of each draft (from the measurements above):
- **Every item:** its declarations go inside its home module's namespace block, before that block's
  `end`, reusing the module's own `variable` line where it is the draft's (MovingAverage's line 84
  is d115's line 8: drop the draft's copy); a draft that binds its types in its own signature (125,
  138, 148) keeps them, and its binders shadow the module's `variable` lines, which then do not
  reach it (the cut's copies measured it, above); the draft's `open` lines the module lacks become
  `open … in` on the declarations that need them, and an `open` of the namespace itself is dropped;
  references the namespace makes ambiguous or wrong are written in full (job 1's type comparison
  for statements; `el.sh` on the module and the cut's copies for proofs); each main theorem's docstring names its item ("Item 114 of MATH-PLAN-library-2") and its
  draft; the module docstring lists the new results; a step whose effect is not determined is cut to
  what fires; a private helper whose statement Mathlib or the module already proves is replaced by
  that name (the module review asks it of each helper); every warning the four flags or `lake build`
  report is fixed in the proof only, except a warning that a section variable is unused, which is
  fixed by `omit … in` before the declaration's docstring, as is a warning that a section variable's
  instance is unused in the type (Mathlib's `linter.unusedDecidableInType` and
  `linter.unusedFintypeInType`); the same warning on a declaration's own binder is reported and the
  statement kept (rule 1). FairGame uses `omit … in` at lines 84 and 115;
  each fix listed in round 72.
- **114:** KalmanVariance gains `import ClassicalLean.Probability.FirstOrderRecursion` after its last
  import line (line 8); the theorem before `end` (line 233); the draft's `open
  ClassicalLean.Probability` dropped (the namespace); `FirstOrderRecursion.eq_steady_iff` resolves in
  the namespace as in the draft (job 1's type comparison and the cut's copy check it). Verdict:
  FAITHFUL to the row's equation (round 1's review); the row's filter and error-recursion clauses are
  not stated (Not in this order). The docstring says only what is proved: `P*` equals the steady
  value `(q + K² r)/(1 − (1 − K)²)` that FirstOrderRecursion's `eq_steady_iff` gives a first-order
  recursion of coefficient `1 − K` and noise variance `q + K² r`; it names the filter's error
  recursion as the reading, not as a proved fact, and defines every letter it uses (the draft's `w`
  and `v` are not defined). A module review that finds 114 WEAKER for those clauses is answered by
  that docstring and recorded in round 72, not by restating the theorem (rule 1); brief (a)
  says so.
- **115:** the private def and lemma and the theorem before `end` (line 254), after line 91; the
  theorem without its own `[IsFiniteMeasure μ]` binder, which line 91 supplies in the same place
  (first after `{Ω} {mΩ} {μ}`, as in the draft; job 1's type comparison checks it); `open Filter
  Topology in` on the theorem (the module opens neither); MovingAverage gains `import
  ClassicalLean.Probability.EffectiveSampleSize` after its last import line (line 7), as the plan
  row's module column says (d115 calls three of its theorems); the draft's
  `Mathlib.Analysis.SpecificLimits.Basic` line is not added (already in MovingAverage's closure).
- **125:** the private def, the two private lemmas and the theorem after `end DoobL2` (line 524) and
  before `end` (line 526), outside the three sections, keeping their own binders; `open scoped NNReal
  in` on the declarations that use `ℝ≥0` (the module opens it only inside section Kolmogorov), and no
  `open ProbabilityTheory` (the draft does not open it). Verdict GENERALIZED (round 1's review), said
  in the docstring with how; claude-ai's reading, for the plan-fit check and review (c) to confirm:
  no `S 0 = 0` (`ξ 0 = S 0`), any finite measure (`μ.real`), not only a probability, and the
  weights indexed from 0. Its importers GamblersRuin and RuinBound are rebuilt (job 2).
- **138:** the theorem before `end` (line 138), keeping its own binders; verdict GENERALIZED (review
  r6) said in the docstring with how; claude-ai's reading, for the plan-fit check and review (d) to
  confirm: each step independent only of the past `𝒢 n`, not a family independent from the start;
  any filtration in which step `n` is known at time `n + 1` (`τ` in `WithTop ℕ`, read with
  `untopA`, is Mathlib's typing of a stopping time, not a generalization). The docstring names GamblersRuin's fair `±1` case `integral_stoppedValue_walk_sq`, which stays
  as it is. For its witness FairGame gains `import Mathlib.Probability.Independence.InfinitePi` and
  `import Mathlib.Probability.BorelCantelli` after its last import line (line 8), for the witness only
  (claude-ai's probes above; GamblersRuin's closure, and so the root's, already holds both, so only
  FairGame's closure grows; the cut measured the two lines alone); claude-ai's ruling, which Dustin did
  not veto before the cut (store row 20261021-027). Its importer GamblersRuin is
  rebuilt.
- **148:** the private helper and the two theorems before `end` (line 408), keeping their own
  binders; the draft's module docstring (its lines 3 to 12) is not added: FiniteChain's module
  docstring lists the two theorems in one or two sentences of its own; `meanHitting_eq_of_le`'s
  docstring says the target is nonempty by `hA` (review r7's minor), not "if nonempty";
  `one_sub_mul_le_pow_aux` replaced by Mathlib's Bernoulli inequality `one_add_mul_le_pow` at
  `a := −x` at its one use, as the cut's copy did (rc 0; keeping the helper with that proof leaves its
  `h0` unused), said in round 72.

## Scope

- **Branch.** `lean-35` from `f5411f4` in `~/lean/classical-lean-paper-crypto`, made after Dustin
  approves your plan. Nothing pushed. No sudo.
- **You may change in the repository:** the five home modules above, and in them only: new
  declarations inside the namespace block (the Goal list); the four import lines named
  (KalmanVariance's, MovingAverage's and FairGame's two); the module docstrings' lists of results; witnesses after the last line
  (rule 5). Also `tools/vacuity_reviewed.txt` (rule 4 only), `records/`, and `HANDOFF.md` section 1
  and `ROADMAP.md` (job 4).
- **You may not change:** any other module, any existing declaration of the five (the type dump
  checks it), any other import line, `ClassicalLean.lean`, anything else under `tools/`, `.github/`,
  `records/rules.toml`, the lake files, `HANDOFF.md` sections 0 and 2 to 6 (section 6's drift check
  hashes the text outside the generated block too). Needing to is a stop: report it.
- **You may write in the lane:** the plan, the report and the push-review file through `ds_file`;
  rows from 165 in the bridges file (job 5b). Nothing else.
- **Off limits:** the main clone `~/lean/classical-lean` and its `master`; `~/break-it-5`;
  `~/trading`; `~/lean/recheck` (`run-recheck.sh` is run as gate 7, not edited); every earlier
  order's folder under `~/lean/` (read only; `~/lean/lean34-checks/` is the source of your helpers);
  Dustin's `~/.config/classical-lean/banned-terms` (the scanner reads it; never print or copy it);
  every GitHub branch (no push, no delete); `/data/api-credit/` (read only); `~/api-credit/` and
  `/tmp/claude-ai-*/` (claude-ai's; you may read `~/api-credit/l35/` only, never write there).
- **The night window and the memory cap,** as `ev.sh` enforces them (its header names the window;
  rule 36: name the window, do not copy its times). Before each whole-library run, log `pgrep -ax
  lean` through `ev.sh --nolean` (rc 1 when none runs) and wait while another Lean process runs;
  reviewers run no Lean while you do; claude-ai starts no Lean run on DSMain while this session
  runs, unless Dustin says so. Start gate 7 only when it can finish before the midnight timer (its
  duration in LEAN-34's run is in the cut's list). Every whole-library run under `ev.sh --cap` or
  `rootrun.sh`; never two Lean runs at once; read `crontab -l` and `systemctl --user list-timers`
  before you start; `~/.elan/bin` on `PATH`.

## Check, then read

Check these sha256s first; if any differs, stop and say which:
- this order, `lean/LEAN-35/order.md`: the value in Dustin's prompt;
- `~/api-credit/l35/facts.txt` on DSMain, `lean/LEAN-35/data/cut-facts.txt`, `lean/LEAN-35/data/hints.py`,
  `lean/LEAN-35/data/hints.out`, `lean/LEAN-33/scripts/TypeDumpPI.lean`,
  `lean/LEAN-33/scripts/g8-typediff.py`: the values above;
- `lean/LEAN-34/order.md` and `lean/LEAN-34/report-r2.md` (the pattern this order follows): the cut's
  values; `lean/LEAN-34/data/mkwitcheck.py` `fac60ab63a4708b36ef58f6274e8bea2aa79f8afbb0ed27e0324a3208669507a` (rule 13);
  `lean/LEAN-34/data/cut-facts.txt`
  `0d7ef8d48aac219d34436942b0c9ee5c6486cf45344078531c133a4ee545baa9` (the drafts' compile at `02ac649`);
- `lean/MERGE-2-order.md` `81894b5bc85a6ee6858f7a1d8b065ee17ff5034f21df9ef68803cded13e4251a` (setup,
  gates and push review on DSMain);
- `lean/CLOUD-LANDING-PLAN-2.md` `26da22cef5604286b2b4b8fdfed4ec9fd70fb5c8520cb5dbfcd7b5c8411051a5`;
- MATH-PLAN-library-2.md (lane `inbox/threads/staging/MATH-PLAN-library-2.md`)
  `6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166`;
- `work/api-credit/API-CREDIT-1/API-CREDIT-1.md` (lane root)
  `599276c28ba636a8aa56d304c9d81db370b67424f237b9e75941f79f8ad51f43`;
- `lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md`: `08773508fcdddda22e1a13d6bc2d24882f2825563261226460bf27f80a6ada2f`;
- the five carry files in `/data/api-credit/20261019/carry/`: the values above;
- the helpers and census tails (Setup 1); and the five modules at `f5411f4`, which must have the
  `02ac649` sha256s above (the cut: all five equal): a difference is a stop, since every line number
  this order gives in them is `02ac649`'s.

Then read: in the repository `records/README.md`, `HANDOFF.md` sections 1, 4 and 6 (all 21 rules),
the five home modules in full, GamblersRuin's `integral_stoppedValue_walk_sq` (line 304) and its
witness of `measureReal_hit_eq` (lines 1135 to 1160), the last round's fragment, and LEAN-34's INDEX
and CLAIMS rows (the pattern for yours); in the lane LEAN-34's order in full and its report,
MERGE-2's order's Setup and Job 4, CLOUD-LANDING-PLAN-2.md rulings 2 and 5, MATH-PLAN-library-2.md
section 7's rows 114, 115, 125, 138 and 148, API-CREDIT-1.md lines 59, 120, 142 to 148 and 171 to
175, and the bridges file's last section; the five carry files in full.

## Rules of this order

1. **Statements as drafted.** Each main theorem (`riccatiRoot_eq_steady`,
   `variance_sum_movingAverage`, `measureReal_exists_mul_abs_ge_le`, `integral_stoppedValue_sq_eq`,
   `meanHitting_eq` and `meanHitting_eq_of_le`) keeps its draft's statement, apart from the Goal
   list's changes and the move into its namespace. Never weaken, restate or add a hypothesis to make
   anything easier. A statement you find false is reported with its counterexample and narrowed,
   said plainly in its docstring, round 72 and the report; never dropped silently.
2. **Namespaces and imports.** Every new declaration, private ones included, sits inside its home
   module's namespace block; the axiom gate checks only constants under `ClassicalLean`. Only the
   four import lines named in the Goal list are added; no other import line anywhere changes.
3. **No existing declaration changes** (HANDOFF rule 14). A type dump of the whole library
   (`TypeDumpPI.lean`, through `rootrun.sh`, because it imports `ClassicalLean`) at the records
   commit and again at G (rule 7), compared by `g8_typediff.py diff`, read by its `DIFF` line (its
   exit code is 0 whenever nothing is CHANGED, even with REMOVED lines): predicted `removed=0
   changed=0 proof_only=0`, and `added=` the new constants (job 3). A `REMOVED` or `CHANGED` line is a
   stop. A `PROOF-ONLY` line is listed and explained as rule 14 says, and reported as a miss of this
   prediction: claude-ai measured the import lines alone at the cut (above). A difference between
   `added=` and job 3's list confined to auxiliary names is listed and explained, not a stop. A new
   warning in an existing declaration is a stop (Scope).
4. **The vacuity gate as the repository has it.** A flag or an UNCHECKED verdict on a main theorem
   makes that item not closed (rule 9). On a helper: rewrite it, remove it if Mathlib or `simp`
   already does its job, or list it in `tools/vacuity_reviewed.txt` as HELPER with a one-line reason
   its module's reviewer checks. A VACUOUS-PENDING entry makes the item not closed.
5. **Witnesses** in HANDOFF section 4's form (rule 2's form: `example := Full.name (x := …) h₁ h₂ …`,
   every chosen argument by name, optional `open … in` lines of their own and no other `open` than
   the module's top-level ones, the docstring "The hypotheses of `name` hold together: …", none of
   the six forbidden words, one inline block with no helper declarations; not degenerate as rule 3
   and VACUITY-3's ruling 3 say). Six blocks in all, one for each main theorem (148's two
   included), each after its module's last line, starting from the hints above. Log `date +%s`
   through `ev.sh` when you start each; one still missing 1800 seconds later makes its item not
   closed. 138's witness is on coin sequences, with FairGame's two Mathlib import lines (Goal
   list; Dustin did not veto them before the cut).
6. **Records.** As `records/README.md` says. The records-first commit: this order's copy, its INDEX
   row (`| LEAN-35 |`) and CLAIMS row at the bottom, the push of LEAN-34 appended to LEAN-34's
   INDEX and CLAIMS rows (records/README.md rule 2: the next order's records commit records the
   push, as the cut gives it above), and round 72's fragment naming the five module files by
   full path. Round 72's fragment gives each module's theorem-constant count from the census
   (rule 27) and gets its commit hashes in a follow-up edit once they exist, never predicted.
7. **Predict, then measure; the tree that counts.** As LEAN-34's rule 7: an evidence folder
   `~/lean/lean35-checks/` with `evidence.log`; every prediction file hashed into the log (`hl.sh`)
   before its run; hashes in records and the report by script, never typed; git, hash and records
   commands as `ev.sh --nolean`; every commit through `ev.sh --nolean` as `git commit -F <message
   file>` with a label starting `commit-`, then `COMMIT <hash>` appended to `evidence.log`; a helper
   you must run after generating a message's `Evidence:` line, and before its commit, takes a label
   starting `commit-`. Every gate runs on the clean tree of the last commit that touches anything
   outside `records/` (call it G); later commits touch only `records/`.
8. **Reviews.** Job 1's statement review, then five cold reviews once their text is final: (a)
   KalmanVariance (114), (b) MovingAverage (115), (c) MaximalInequality (125), (d) FairGame (138),
   (e) FiniteChain (148), each by a fresh subagent that has not seen your work, with a brief built
   by script as rule 26 says. Each brief caps its reviewer at 40 tool calls; at the cap it writes
   what it has and lists what it did not check, and anything listed as not checked gets a fresh
   reviewer for those parts only before the commit. A module review checks each statement against
   its plan row (FAITHFUL, GENERALIZED or WEAKER; WEAKER is a finding), every hypothesis used, each
   witness against rule 5, every new declaration in the namespace, the import lines, every private
   helper's statement and whether Mathlib or the module already has it, and no main theorem whose
   conclusion is a recursive predicate that is `True` everywhere. A review with findings ends with a
   confirming pass on the fix only, by a fresh reviewer. At most two fix-and-confirm rounds; an item
   not clean after two is not closed.
9. **Not closed.** An item not closed is undone by a new commit (never a reset): its declarations,
   witnesses, import lines, module-docstring entries and vacuity-list entries removed, and round 72, the CLAIMS row and
   the report saying which item and why. The others go on.
10. **Master does not move under you.** If `origin/master` or GitHub's `master` is not `f5411f4` at
    "Before approval" or when you write the push-review file, stop and report: claude-ai then writes
    the merge step. Never merge or rebase anything yourself.
11. **Nothing is added during the run.** The Goal list, the jobs and the checks are this order's,
    all of them. Nobody adds a job, a check or the wording of a result while you run, claude-ai
    included: a finding outside the Goal (a fault in an older module, a gap in a tool, an idea for
    the library) is written down with its evidence and goes to the report's list for a later order;
    it is not chased. A heads-up (a side note Claude Code shows on Dustin's screen, not in your
    conversation) reaches you only when Dustin passes it in with its "Chat in main session"
    option; each one that reaches you is answered in your next message and listed in the report
    with your answer, and you act on one only when it names a stop under these rules. claude-ai rules during the run only on a stop. (LEAN-34: three
    additions claude-ai sent while it ran grew a landing order into a tool build and a library-wide
    sweep that no review had planned; store rows 20261021-033, -034 and -041.)
12. **A count is what its output says.** Every count in round 72's fragment, the report and
    your replies is read from a saved output and cited by its path and line. No message sets a
    count or the words of a result in advance; if one does, the output wins and you say so. A check
    that did not give a verdict on everything is stated as how many it confirmed and which it did
    not, each with why, never as "N of N checked". (LEAN-34: claude-ai's message gave the sweep's
    headline, "145 of 145 checked", before the sweep ran; the check confirmed 137; store row
    20261021-042.)
13. **The witness check, on this order's witnesses only.** After each module's `lake build` in job
    2 and before its cold review, run LEAN-34's `mkwitcheck.py` (lane
    `lean/LEAN-34/data/mkwitcheck.py`, checked above; copied into `~/lean/lean35-checks/scripts/` by
    Setup 1's route, its sha256 logged) on the module as built, with EXPECTED predicted from the module at `f5411f4` plus this order's
    blocks: KalmanVariance 2, MovingAverage 4, MaximalInequality 3, FairGame 2, FiniteChain 7 (at
    `f5411f4` they hold 1, 3, 2, 1 and 5 lines starting `example :=`, and no typed example); a refusal
    is a miss: name the missing or extra block, and rerun with the count predicted again. Its generated file is elaborated with `lake env lean`
    through `ev.sh`, as LEAN-34's `witsweep.sh` did (the check reads constants, not linters), its
    prediction first: every witness of this order OK. Log the module's sha256 beside each run; a fix
    after the check that touches the module reruns it before the commit. The check has had one read
    by claude-ai and no cold review. Where it is blind (a witness that uses a private lemma gets
    BROKEN; an example inside the namespace makes the check file fail; a hypothesis behind a
    definition that reducible unfolding does not open passes as OK; a conclusion that itself begins
    with a hypothesis binder gives a false PARTIAL; the script's docstring and LEAN-34's report-r2,
    line 231, list them), the module's cold review reads that witness by hand and says so. A non-OK line on an older witness is listed in the report, not
    fixed. No library-wide run.

## HANDOFF's rules in this session

Every rule of `HANDOFF.md` section 6 applies. How, for this order:

| rule | here |
|---|---|
| 1, 2, 3, 10, 15, 18, 19, 22, 28 | as written. Rule 19: credit each proof to its draft (the API-credit pipeline's Claude Opus 5.5 through the Anthropic Batch API, lean/API-CREDIT-CARRY-1.md; 148's to the amendment round), adapted by this session. Rule 22: every quote in round 72's fragment is checked by a script with a planted misquote (the quote checker LEAN-34 used may be adapted). |
| 12 | Reviewers work in `~/lean/lean35-checks/reviews/<label>/`, outside the repository, with `PYTHONDONTWRITEBYTECODE=1`, copy any repository script before importing it; `git status --porcelain` unchanged after each review; the tree is not touched while a reviewer runs. |
| 14 | Rule 3 above: the type dump at the records commit and at G, by the lane pair, after its controls (Setup 5). |
| 17 | Each reviewer writes its report to a file and returns only its sha256; you hash the file with `hl.sh` and compare before you open it. |
| 20 | Scratch files and modules are elaborated by `el.sh` (it carries the four flags); linter results count only from `lake build`. Rule 13's generated check file is the one exception: `lake env lean` through `ev.sh`, no flags (it reads constants). |
| 23 | `ev.sh` and `hl.sh`, tested in Setup 2. Every write, hash and edit of an evidence or records file runs through them, or is listed in the plan and round 72's fragment before the commit that carries it (records files written with Write or Edit are hashed with `hl.sh` before their commit); a commit runs only when its gates exited 0 in the same run. |
| 26 | Every review brief is built by a script from `HANDOFF.md`, saved with its sha256 before it is sent, and quotes verbatim rules 14, 17, 18, 19, 20, 22, 23, 26 and 31, cut only with `[...]`; briefs (a) to (e) also quote HANDOFF section 4's "Satisfiability witnesses" paragraph verbatim. Use the brief builder LEAN-34 used (Setup 1), tested in Setup 2. |
| 27 | Theorem-constant counts, total and per module, from `mkcensus.sh` with the census tails on scratch copies of each final module, before any gate; the module count from `env.header.moduleNames` of a scratch file importing `ClassicalLean`, run through `rootrun.sh`, at the records commit and at G (predicted equal: no module is added, and the four import lines bring FirstOrderRecursion, EffectiveSampleSize and two Mathlib files, all already in the root's closure), and the build's job count (predicted 4193 at both). |
| 31 | Job 1's statement review is in before any landing; every new declaration, private helpers included, gets its module's cold review before its commit; a review fix that touches a proof line gets its delta check (re-elaborated with `el.sh` and the module rebuilt through `ev.sh`) before its commit. |
| 36 | Briefs and predictions carry a date beside every clock time; each brief gives the dated end of its own run; `briefcheck.py` passes every brief before it is sent. Witness time limits in epoch seconds. |
| 37 | `el.sh` refuses a run while a name is not probed: one probe file per draft and one for the witness blocks, `#check @Name` lines for every Mathlib and library name in the text as it will land, run with `EL_PROBE=1`. |
| 38 | `rootrun.sh` for the type dumps, the bridge search, the report tool and any census that imports `ClassicalLean`; tested before first use (Setup 2). The gates are not wrapped. |
| 39 | Stage by path. A commit message is written after its gates ran, says only what `evidence.log` shows, names in its first paragraph any linter or option switched off or on, and ends with the line `evcite.py` prints, generated last, followed only by the session's attribution trailers. Job 5e runs `citecheck.py`. |

## Before approval (read-only in the repository)

1. `git fetch origin` in the worktree. Then, each predicted and checked: `origin/master` and
   `git ls-remote github master` both `f5411f4d37ea5becc011c803dccc79e9ca4dc9f6`; `git status --porcelain` empty. If not, stop (rule
   10).
2. Check the hashes and read the read list.
3. Check `crontab -l`, `systemctl --user list-timers` and `free -g`.
4. Write your plan with `ds_file` (project `lean`, job `LEAN-35`, kind `plan`): the jobs in order,
   every prediction you can make now, the order of the items (a suggestion: 114 (35 lines), then 115 (135),
   125 (143), 148 (321), and 138 last, its witness resting on FairGame's two import lines), and the
   plan-fit check: for each item its plan
   row beside the draft's statement, every difference named (at least: 114's equation with `K`
   written out, FAITHFUL to the row's equation, the filter and its error recursion not stated, its
   `hq` and `hr`; 115's white
   noise as `he` and `hcov`, `γ(k)` as `cov[X k, X 0]`, and `[IsFiniteMeasure μ]`; 125's `hc` and
   `hanti` for the row's weights, `[IsFiniteMeasure μ]` with `μ.real` for the row's `P`, and
   `ξ 0 = S 0`; 138's `hX`, `hL2`, `hmean`, `hvar` and `hind` for the row's "independent steps", and
   `untopA`; 148's `hP0` and `hreach` for "a finite chain", `g = 0` on `A` with `P` in the
   equation and `u` for the row's `1`, and the corollary's `hδ0`, `hδ` and `hA`; and for 125 and 138
   how each is GENERALIZED). Then stop and wait for Dustin's approval.

## Setup (after approval)

1. **The helpers.** Make `~/lean/lean35-checks/scripts/` and `~/lean/lean35-checks/census/`. One
   script copies LEAN-34's helpers and census tails (the cut's list above, with their sha256s)
   after comparing all 64 characters of each source hash, and changes only the path lines the cut
   lists (each `lean34-checks` to `lean35-checks`) and `probecheck.py`'s one `BASE = ` line to
   `BASE = 'f5411f4'`, and `commit.sh`'s line 16, its two trailers (`Co-Authored-By: …` and
   `Claude-Session: …`, naming LEAN-34's `session_01SYJof36hVcDcFdNyijRw19`), to this session's own
   attribution lines, with full paths, each refused unless the
   file has exactly that many such lines. The same script copies the lane's
   `lean/LEAN-34/data/mkwitcheck.py` (its sha256 in the check list) into `~/lean/lean35-checks/scripts/`
   unchanged (it names no `lean34-checks` path). `records2.py`, `docs-insert.py`, `mk116.py`,
   `mkw78.py` and `swap78.py` are LEAN-33's one-off job scripts (round 69's file, LEAN-33's HANDOFF
   anchors, LikelihoodScore's lines): read them as patterns, never run them unchanged. LEAN-34's
   `allowlist.txt` is copied into `~/lean/lean35-checks/` byte for byte; its `seed.txt`, if any, is
   not (your own probes seed the check). You may add to `allowlist.txt` a tactic name `el.sh` refuses
   (a token that is not a constant), with a reason; `el.sh` logs the list's new hash. Copy the lane's
   two type-dump files into `~/lean/lean35-checks/inputs/` (`g8-typediff.py` as `g8_typediff.py`)
   and check their sha256. Log every new sha256 with `hl.sh`. Then write `pred-setup.md` and hash it.
2. **Tests before first use,** each logged and predicted, as LEAN-34's Setup 2: the empty-prediction
   refusal, exit 97; `ROOTRUN_BUILD=false rootrun.sh` refused, exit 95, the command not run; the
   real-build `rootrun.sh` test, its build line before its command line at the same head; the
   citecheck planted pair on a scratch copy of the log, plus a third case with a `commit-…` helper
   line between the `evcite.py` run and the `COMMIT` line, predicted `OK`; `el.sh` refusing a
   scratch file that uses an unprobed name (logged `NOT RUN`), then running it after its probe, and
   no new allowlist line on either run (Setup 1's `hl.sh` already logged the same hash: LEAN-33's
   report, line 49; store row 20261021-029); `briefcheck.py`
   refusing a planted brief line with a time and no date; the brief builder printing a brief that
   quotes the nine rules of rule 26 verbatim and passes `briefcheck.py`. A test that does not behave
   as predicted is a stop.
3. **Branch.** First, through `ev.sh --nolean setup1 …`: `git fetch origin`; `origin/master` and
   `git ls-remote github master` both `f5411f4…`; `git status --porcelain` empty (rule 10). Then
   `git switch -c lean-35 f5411f4d37ea5becc011c803dccc79e9ca4dc9f6`.
4. **Records first,** one commit, no `.lean` file (rule 6):
   `records/orders/<UTC>__claude-ai__order-lean35-kalman-moving-average-hajek-renyi-wald-hitting-times.md`,
   the INDEX and CLAIMS rows, LEAN-34's push, and round 72's fragment
   `records/rounds/<UTC>__round-72-kalman-moving-average-hajek-renyi-wald-hitting-times.md`.
   check_records then: PASS 140.
5. **Before runs at the records commit,** predicted from the facts: build rc 0, 4193 jobs, 0
   warnings; AxiomGate PASS 3574; rule 27's module count (a scratch file importing `ClassicalLean`,
   printing `env.header.moduleNames.size`, through `rootrun.sh` while HEAD is the records commit):
   5729; the type dump,
   `rootrun.sh td-before "<pred>" lake env lean ~/lean/lean35-checks/inputs/TypeDumpPI.lean`, whose
   `td-before.out` ends with `/usr/bin/time -v`'s report: keep its lines that start with `{` in
   `td-before.jsonl` by a script run through `ev.sh --nolean`, and check that every dropped line is
   time's report; then `g8_typediff.py check td-before.jsonl`: rc 0, 4058 records (3574 thm, 484 def), elided 0,
   missing_fields 0. Then the diff tool's controls on copies of `td-before.jsonl`, each predicted and
   read by its `DIFF` line: the file against itself, all zeros, rc 0; one record's `ppPI` edited,
   `changed=1`, rc 1; only its `pp` edited, `proof_only=1`, rc 0; one record deleted, `removed=1`, rc
   0 (the exit code does not catch it; the `DIFF` line does).

## The work

### Job 1: statements and their review

1. Probes (rule 37): one file per draft and one for the witness blocks; each new witness's names are
   probed before it is written.
2. For each draft, a scratch statement file outside the repository that imports its home module
   (and FirstOrderRecursion for 114, EffectiveSampleSize for 115, FairGame's two Mathlib files for
   138), repeats the module's top-level `open` lines, and holds
   `namespace <home namespace>`, the draft's declarations as they will land with every theorem's
   and lemma's proof `sorry` (defs keep their bodies), and `end`; the statement file for 115 keeps
   the draft's `variable` line and puts a copy of MovingAverage's line 91 just before its first
   declaration, since a module's `variable` lines do not reach a file that imports it (the files
   for 114, 125, 138 and 148 need none: 114 has no section variable, and the others bind their own
   types). So `el.sh` reads only the new text (it reads a scratch file whole), and the full names
   are the ones the module will have. Elaborate each with `el.sh`, predicted rc 0 with `sorry`
   warnings and any other warning you expect listed in job 1's prediction file, hashed before the
   run; an unlisted warning is a miss, checked again when the proof is in. Hash the statement files.
   Scratch files for work on a witness likewise import the module and hold only the block.
3. A mechanical check that the move changed no meaning: for each main theorem, its type printed
   with `set_option pp.fullNames true in #check @name` from the draft (a scratch copy with the line
   appended) and from the statement file, compared by a script (the type comparer LEAN-34 used may be
   adapted): only the namespace prefix may differ. Log the result.
4. One statement review of the five items' six main theorems, by one fresh subagent (each statement
   against its plan row and its draft, the Goal list's changes, the namespaces, the four import lines).
   Its verdict is in before job 2.

### Job 2: land, one commit per module

In the plan's order, per module: the declarations in place (the Goal list), the import lines if any,
the witnesses; `el.sh` on the module (rc 0); `lake build` of the module and of every module that
imports it (the cut's list; at `02ac649` MaximalInequality had GamblersRuin and RuinBound, FairGame
had GamblersRuin, the other three none but the root file) through `ev.sh` (0 errors, 0 warnings); `python3 -I tools/banned_vocab_scan.py
ClassicalLean`; the vacuity gate and the check scripts (a copy of the vacuity gate whose only change
is its import line may run on one module while the root is not rebuilt; the real gate runs in job
5a); the witness check on the module as built (rule 13); the module's cold review (rule 8) with
any fix and its confirming pass; one commit staged by
path, then its `COMMIT` line.

### Job 3: predictions

Once every module's text is final (after the reviews) and before job 5: a prediction file, hashed,
with the module count and job count (rule 27's measurements); the theorem constants by census (base
3574 plus the census of each final module's new constants, per module: `mkcensus.sh` on a copy of
each changed module at `f5411f4` and on its final copy, the new constants being the difference of
the two `.names` lists); the type dump's `added=` list, the difference of the two census-all lists
for the changed modules (the dump keeps only `thm` and `def` constants, so a name of another kind in
that difference is listed as an expected absence, and private names are compared by their
user-facing names, `privateToUserName`, because the census runs on copy files whose module name
differs) (rule 3); check_sorry and check_records PASS 140; the vacuity gate's verdicts and
reviewed-helper count, and its tests (89 tests, 47 flagged, 0 rule-5 run-outs, 0 mismatches); `banned_vocab_scan.py ClassicalLean` PASS,
140 files and the root file, 0 hits; gate 7 ALL PASSED, 4193 jobs, 140 modules 0
failed, 3574 plus the census count, the three standard axioms, the planted fault named; the drift
check PASS; the bridge search's and report tool's numbers by hand from LEAN-34's runs (say they are
hand predictions); the records-file count. Until then do not run the axiom gate on the changed
modules. A miss is reported, never fixed by changing what was measured.

### Job 4: documents

- `HANDOFF.md` section 1: after LEAN-34's paragraph, a dated LEAN-35 paragraph (round 72):
  the five items by name, module and item number, one line each, 125's and 138's GENERALIZED
  verdicts said, and 148's two theorems; the counts predicted by job 3, to be re-measured by job 5a.
  No other section of HANDOFF.md changes (section 6's drift check).
- `ROADMAP.md`: after section 1.28, a section 1.29 for items 114, 115, 125, 138 and 148,
  landed from below the plan's cut by order LEAN-35, in section 1.28's form.
- One fresh cold reviewer reads the documents commit's diff alone (about 15 calls); a review with
  findings ends with a confirming pass on the fix only (rule 8).

### Job 5: the end checks, in this order

- **5a. The gates,** on the clean tree at G, each through `ev.sh` with its prediction, in MERGE-2's
  forms (its job 4a): build, AxiomGate, VacuityGate, the vacuity tests, check_sorry, check_records,
  the drift check, `banned_vocab_scan.py ClassicalLean`, and gate 7. Then rule 27's module count at G
  through `rootrun.sh`, predicted equal to Setup 5's. Then the type dump at G through `rootrun.sh`
  as in Setup 5, its `{` lines kept in `td-after.jsonl` and the dropped lines checked,
  `g8_typediff.py check td-after.jsonl`, then `g8_typediff.py diff td-before.jsonl td-after.jsonl`
  (rule 3). A gate that fails is a stop: 5b and 5c do not run, but 5f's report is still written.
- **5b. The bridge search,** through `rootrun.sh`, at G:
  `python3 -I tools/bridge_search.py --diff records/bridges/LEAN-34/ --out ~/lean/lean35-checks/bridges/LEAN-35`;
  rc 1 means candidates to review. Report NEW and GONE pairs and shapes. Check each NEW
  import-unrelated pair and each NEW shape for a theorem whose proof needs both sides; a real one is
  appended to the bridges file from row 165, through `ds_write_staging` in append mode with
  `expect_sha256` its value above (if the write is refused, stop and report), in the file's columns.
  Say in the file and the report exactly how the pairs were checked: which were read statement by
  statement, and how the rest were judged (plan 2's ruling 5). The two new library import edges
  (KalmanVariance imports FirstOrderRecursion, MovingAverage imports EffectiveSampleSize) can make
  pairs the baseline listed as import-unrelated related: list each such GONE pair with that reason. Items 114 and 115 are the plan's own bridge rows, landed
  here; they are not new rows of the bridges file. Write the new baseline to
  `records/bridges/LEAN-35/`; its commit touches only `records/`.
- **5c. The report tool,** through `rootrun.sh`, at G, once; a report, not a gate; predicted by hand
  from LEAN-34's `report.out`. List every `CLOSES` line that names a theorem of this order.
- **5d. Close the records:** round 72's follow-up edit with the commit hashes and the measured
  counts, its quotes checked by script (rule 22); the CLAIMS row closed and the INDEX row's state set;
  one records-only commit. Then check_records again at the final HEAD, predicted PASS 140.
- **5e. citecheck:** every commit of this order, `git rev-list f5411f4..HEAD`, by
  `citecheck.py ~/lean/lean35-checks/evidence.log --message <its message file> <hash>` in one loop (the
  message from `git log -1 --format=%B <hash>`; each `OK`), and the repository run `citecheck.py
  ~/lean/lean35-checks/evidence.log ~/lean/classical-lean-paper-crypto f5411f4` (predicted rc 0,
  every commit `OK`).
- **5f. Report** with `ds_file` (kind `report`), laid out like LEAN-34's report: in short; setup and
  the helper tests; for each item its final statement, witnesses and review verdicts; the type-dump
  diff; predicted beside measured for every gate and count, each cited from its output (rule 12); the bridge diff and how it was checked;
  5c's `CLOSES` lines for this order (or "none"); the commits; 5e's output; each heads-up Dustin passed in and your
  answer to it (rule 11); the findings outside the Goal, each with its evidence, for a later order (rule
  11); misses and anything not closed; and the push command as one line, not run:
  `cd ~/lean/classical-lean-paper-crypto && git push origin lean-35:master && git push github lean-35:master`.
  Say that the GitHub push starts a CI run on `master`, and that Dustin runs it only after claude-ai
  has checked the push-review file.
- **5g. Push-review file** with `ds_file` (subdir `data`, name `LEAN-35-push-review.txt`), by one
  script, each command followed by its full output: `git rev-parse HEAD`, `git status --porcelain`,
  `git ls-remote origin master`, `git ls-remote github master` (both must still be `f5411f4`, rule
  10), `git merge-base --is-ancestor f5411f4 HEAD` with its exit code, `git rev-list --count
  f5411f4..HEAD`, `git log --name-status --format='== %h %cI %s' f5411f4..HEAD` (files under
  `records/bridges/` as a count), `git diff --stat f5411f4 HEAD`, `git diff --name-only f5411f4 <G>
  -- ClassicalLean.lean tools .github ':(glob)lakefile*' lake-manifest.json lean-toolchain
  records/rules.toml` (predicted: only `tools/vacuity_reviewed.txt`, if a helper was listed), `git
  diff --name-only f5411f4 <G> -- ClassicalLean` (predicted: exactly the five modules), `git diff
  -U0 f5411f4 <G> -- ClassicalLean | grep '^[-+]import'` (predicted: exactly the four import lines,
  each `+`), `git diff -U0 f5411f4 <G> -- ClassicalLean` piped to a script that lists every removed
  line (predicted: none outside the five module docstrings), the type-dump `DIFF` line, `git diff
  --name-only <G> HEAD` (only `records/`), 5d's output and 5e's two outputs. Report its sha256. Then
  stop: claude-ai reviews it before Dustin pushes.

## Done means

- Branch `lean-35` from `f5411f4`, clean tree, nothing pushed; its first commit is the records
  commit and holds no `.lean` file; then one commit per module; then documents; then records-only
  commits.
- The helpers copied, their sha256s logged, their tests run before first use as predicted.
- The five items proved with no `sorry` and no new axiom, as drafted with the Goal list's changes,
  or each narrowing said plainly, or reported not closed and undone by rule 9; 125 and 138
  GENERALIZED and said so.
- Six witnesses in rule 2's form, each checked by its review against rule 5, or an item undone by
  rule 9 and said so; each OK in the witness check before its commit (rule 13), or read by hand in
  its module review where the check is blind, and said so.
- The type-dump diff `removed=0 changed=0`, and `proof_only=0` or each PROOF-ONLY record listed and
  explained (rule 3); its `added=` list equal to the census's new constants, apart from differences
  listed and explained under rule 3 and job 3.
- Job 1's statement review and the five module reviews and the documents review saved and
  hash-checked, each ending in a confirming pass where it had findings.
- Every gate as predicted at G, or each miss reported; gate 7 ALL PASSED at G; after G only
  `records/` changed; check_records PASS at the final HEAD.
- The bridge diff reported with how it was checked; real bridges (if any) from row 165;
  the new baseline committed.
- Job 4's documents changed and named (only section 1 of HANDOFF.md; the drift check passes).
- 5e: every commit `OK`.
- The plan and the report in `lean/LEAN-35/`, the push-review file in `lean/LEAN-35/data/`, hashes
  matching yours.

Then report in a few plain sentences: what was proved, the GENERALIZED verdicts of 125 and 138, the
witnesses, the gate results beside the predictions, any new bridge, the two files' hashes and the
push command. Dustin reads your replies carefully and is still learning to read code: plain words,
and define a technical term the first time you use it. When you need a decision from him, ask in one
line with your recommended answer first.

## Not in this order

- VACUITY-3 rows 31 and 32 (YuleWalker's two theorems; LEAN-36 with batch 6).
- 114's filter (exponential smoothing with constant `K`) and its error recursion as theorems (the
  row's other two clauses; round 1's optional strengthening).
- Bridges 160 to 162 and the pair-by-pair reads of MERGE-2's and MERGE-3's searches (LEAN-38, plan
  2 ruling 5 and store row 20261021-001); the twin search (TWINS-1, ruling 6).
- Deleting GitHub branches; any push.

## Revisions

- r0, the draft (claude-ai, 2026-10-21, staged while LEAN-34 waits to run).
- r1, review pass 1 (one fresh subagent, 2026-10-21; FAIL, 1 BLOCKER, 2 MAJOR, 9 MINOR; its report
  saved verbatim, sha256 `c791a2bea5d4462bc4c90b8a35cd150131ded8eea1f4239f59ab3565af9c8df7`): BLOCKER: 115 needs
  MovingAverage's import of EffectiveSampleSize (d115 calls three of its theorems; claude-ai's
  reading was wrong, store row 20261021-017), so it is added and the ruling withdrawn. MAJOR: 138's
  witness space, probed by claude-ai in Lean (store row 20261021-018): FairGame gains two Mathlib
  import lines for it, a vetoable ruling; 114's verdict FAITHFUL to the row's equation and its
  docstring limited to what is proved. MINOR: 125 without `open ProbabilityTheory`; proofs' names
  checked by `el.sh`, not the type comparison; claude-ai's reading of how 125 and 138 are
  GENERALIZED; the hints' floating-point sum named; the items' order by length; MATH-PLAN's path;
  148's WEAKER line; 125's `S n` for every `n`; LEAN-34's cut-facts in the check list; 148's helper
  replaced by `one_add_mul_le_pow` (probed).
- r2, the confirming pass (a fresh subagent, 2026-10-21; CONFIRMED WITH FINDINGS: all 12 fixed, 7 new
  MINOR; saved verbatim, sha256 `801f3b2dde0ceb960531df3f57b0c4a96ad2b0fa576848ab976b5e30bf53399a`): stale text after the probes (the
  Lean runs, the time range, the five outputs, where the probe files are, "the import lines"); the
  closure sentence's subject; the veto on 138's import lines makes claude-ai revise the order before
  the cut; 114's two unstated clauses in "Not in this order"; the `omit` rule limited to section
  variables' instances, a declaration's own binder kept; 138's `WithTop ℕ` is not a generalization.
  For the cut's script: one placeholder for the probes replaced two older ones. Not reviewed
  again.
- r3 (claude-ai, 2026-10-21 after 20:33 EDT, at Dustin's question whether LEAN-34 was going off the
  rails): rules 11 to 13 from LEAN-34's run (store rows 20261021-033, -034, -041 to -043); the
  witness check in job 2, the check list, 5f and Done means. Reviewed with the cut.
- r4 (claude-ai, 2026-10-21 after 20:48 EDT): rule 11's heads-ups reach the session only when Dustin
  passes one in (r3 assumed the session sees them; it does not, store row 20261021-046); 5f to
  match. Reviewed with the cut.
- the cut (claude-ai, 2026-10-21, after LEAN-34 was pushed): the values measured at `f5411f4`
  (cut-facts.txt) filled into r4 by `fill-cut35.py` (sha256
  `582552e6ebc33ee74109c4b6f9bf364c844ee9854fd567bad33cff15c1c52da8`). Review pass 1 (a fresh subagent;
  PASS WITH FINDINGS, 0 BLOCKER, 1 MAJOR, 10 MINOR; saved verbatim, sha256
  `87b1e1f76426f17972917a95cfade8d14e52e8b4ec1f993243c6b119d7506803`): `commit.sh`'s LEAN-34 trailer
  (MAJOR); the hints not measured; the review line; rule 13's EXPECTED as a prediction, its blind
  spots, its sha256 log and its rerun after a fix; Setup 1 copies `mkwitcheck.py`; the rule 20 row's
  exception; 5f's later-order list; the 8 rebuilt modules; LEAN-34's `census/`; the lane files.
  Applied by `fix-cut-r1.py` (`29d4d89e5689de830ad48ebacc4f6d1b32ead1f3e360bf845d0666765bae5d4c`). Pass 2 (the
  same reviewer; CONFIRMED WITH FINDINGS: 9 fixed, 2 held for the final fill; saved verbatim, sha256
  `4abdbaf860ed26e1633eb8582fe8e591bd0c626cc73bab082ef71014830d2b79`): r4's wording; both of `commit.sh`'s
  trailers; LEAN-33's one-off scripts never run unchanged; the cut's outputs kept outside `/tmp`; a
  refusal of the witness check resolved by naming the block. Applied by `fix-cut-r2.py`, with
  `facts.txt` kept on DSMain (read only for the session) instead of the lane. Not reviewed again.
