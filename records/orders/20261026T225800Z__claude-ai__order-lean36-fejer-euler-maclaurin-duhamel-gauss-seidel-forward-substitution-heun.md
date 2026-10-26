# LEAN-36 order: batch 6 of the API-credit drafts (items 127, 128, 129, 132, 133 and 146)

For a plain Claude Code session on DSMain, as dustin, in tmux `cc`. Written by claude-ai on
2026-10-26 in Project LEAN, under lean/CLOUD-LANDING-PLAN-2.md ruling 2 (batches 3 to 7 land on DSMain
as LEAN-33 to LEAN-37; LEAN-36 is batch 6), after VACUITY-4 was pushed (master `354d835` on both
remotes, store row 20261026-048; its CI run #40 green, row 20261026-052). Every fact about the master
this order starts from was measured by claude-ai at `354d835` on 2026-10-26 from 16:13 to 17:10:53 EDT,
and again after cold reviews 1 to 3 from 17:24:52 to 18:00:00 EDT (section "What is already true"), so the draft is also the cut: if master moves before you start,
stop (rule 10). Lane files named `lean/...` are under /opt/datasphere/lane/inbox/threads/staging/lean/
(ds_* tools: root `lane`, path `inbox/threads/staging/lean/...`). Its inputs are `lean/LEAN-36/`
(`notes.md`, `data/witnesses.txt`, `scripts/witcheck.py`, `data/witcheck.out`) and LEAN-33's two
type-dump scripts in `lean/LEAN-33/scripts/`.

**New lane files go through `ds_file`** (project `lean`, job `LEAN-36`): your plan is kind `plan`
(it lands as `lean/LEAN-36/plan.md`; a second becomes `plan-r2.md`, never overwriting), the report
kind `report`, the push-review file subdir `data`, name `LEAN-36-push-review.txt`. Compare each
reply's `post_sha256` with your own. Appending to the bridges file (job 5b) is `ds_write_staging`
in append mode with `expect_sha256`. **Track the order's steps with the task tools** (lane
`lean/NOTE-20261015-task-list-rule.md`).

**Launch check.** This session was started with `CLAUDE_CODE_DISABLE_AUTO_MEMORY=1` (claude-ai's
ruling, store row 20261025-048: fresh subagents otherwise load Dustin's auto-memory index and the
reviews are not cold). Print the variable before anything else; if it is not `1`, stop and say so.

Review: cold pass 1 on helios (`~/lean36-review-1/out1/review.md`,
`cb07d3e5555e8ef479c927ea0fcee512662ba34dbd6763db9fbf322e003fab27`): PASS WITH FINDINGS, F1 to F20, all
applied in r1. Cold pass 2 (`~/lean36-review-2/out2/review.md`,
`8f9ed9b90304e27979d7363577225c432e421c8154bff69738677d11fbacfa53`): PASS WITH FINDINGS, F1 to F20
applied (F2 and F19 partly) and new findings G1 to G9, all applied in r2. Cold pass 3, on those
fixes only (`~/lean36-review-3/out1/review.md`,
`2c19bc0bb1cc8776cf46f57e230f53c1de473c650b57cc8886a5684e0d86299a`): PASS WITH FINDINGS, G1 to G9
applied (G4, G7 and G9 partly) and H1 to H6, all MINOR, applied in r3 (Revisions) with no further pass.

## What is already true

### Measured by claude-ai on 2026-10-26 from 16:13 to 18:00:00 EDT, at `354d835`

On DSMain over ssh from helios: file reads in the work tree `~/lean/classical-lean-paper-crypto`
(branch `vacuity-4` at `354d8358f247740acadc5b9b0fa25722fab4f584`, porcelain empty, no Lean process)
and claude-ai's Lean runs in its own clone `~/api-credit/cl-354d835` (master `354d835`, packages
copied from the work tree, library built once under the 12 GB cap: rc 0, 4193 jobs, 75 s). Every
prediction was written before its run: claude-ai wrote each on helios and copied it to DSMain with
the run's inputs, so DSMain's copy carries the copy time; the helios mtimes and sha256s are in
`gather/g18-helios.out` (`30449fc91153ab3972ce32c586b4c92cedcca819209f80a5a6133d305efc27e5`), each
file equal to its copy here (`gather/g18.out`,
`ab8342df94eddc64f968a0a469cc837752045f90e97444f86c1204d6c2e08c88`) and written before its run's
first log line (probe 2's first file 16:49:43 EDT, its four runs from 16:50:07 EDT;
that file had typed its own time as "about 17:15 EDT", which was wrong). Probe 4's log and, from probe 2's
r3 run on, probe 2's logs hash the prediction file first. Probe 5 had no prediction file. Misses of claude-ai's
predictions, each beside what was measured: probe 3's P5 said RoundingError's `gamma_mono` and
`abs_one_add_mul_prod_sub_one_le` exist, `p3/B.out` found neither (so the Goal keeps d133's own
lemmas); probe 2 r1's P2 said no warning at a witness block's line, two came (the line-length linter
on two docstring lines of claude-ai's), so its counts missed too (JacobiIteration 1 where 0,
RoundingError 8 where at most 7); probe 4's P1 said its first build rebuilds 7 modules, it
rebuilt 6. Outputs are kept in `~/api-credit/l36/` on DSMain (read only
for you, Scope), listed with their sha256 in `~/api-credit/l36/SHA256SUMS-all.txt`
(`2957a4a79f56a7a3d933c5d8048090e0459b6de763c9e080fb6a9d43a97500d6`): `compile/run.log` (the drafts'
compile), `probe1.out`, `p2out/` (the witness probe of draft r0, its fourth run) and `p2out-run1/` to
`p2out-run3/` (its three earlier runs: run 1's LinearODE build failed on a name in claude-ai's witness,
so its gate was not run; run 2's gate found no `lake` on `PATH`; run 3's builds had unused simp
arguments in a witness), `p2out-r1/`, `p2out-r2/` and `p2out-r3/` (the witness probe again after cold
reviews 1 and 2: r2 after two docstring lines were rewrapped, r3 after two docstrings said every step
moves; each run's modules are in `p2-r1/` to `p2-r3/`, written by `mkprobe-r1.py` from that run's
witness file, `witnesses-r2.lean.txt` for r2 and `witnesses-r3.lean.txt` for r3, and hashed in
`p2-r2.sha` and `p2-r3.sha`, which `mkprobe-r1.py`
(`4c74772cd48a4397420505ee36beed5089f22a31a2061d8b505aee5af34b0e8b`) run again on those two witness
files reproduces, `gather/g18-helios.out`; the probe script writes to `/tmp/claude-ai-lean36/p2out`, renamed and
copied here after each run), `p4out/` (EulerMethod's import line alone against the type dump),
`probe5a`/`probe5b` (the two replacements' names), `p3/` (closure, names, duplicates) and `gather/`
(`g17.out`, `g17-helios.out`, `g18.out` and `g18-helios.out` for cold reviews 2 and 3) (file facts; `g14-dups.out` read at 17:10:53 EDT for
the helpers' twins). Store rows 20261026-049, -051 and -053 to -058 record them.

- **The six drafts** (in `/data/api-credit/20261019/carry/`, read-only; each line OK against its
  `SHA256SUMS` at 16:13 EDT). Each imports its home module (d129 also
  `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`) and holds no `sorry`, `admit`,
  `native_decide`, `implemented_by`, `axiom`, `set_option`, attribute, `decide`, `mutual` or
  `(config :=` (grep). At `354d835` each elaborates rc 0, no error, no `sorry` (`compile/run.log`),
  and `#print axioms` gives every named theorem only `propext`, `Classical.choice` and `Quot.sound`.

  | item | draft | sha256 | home module | declarations | last review (lane `work/api-credit/API-CREDIT-1/API-CREDIT-1.md`) |
  |---|---|---|---|---|---|
  | 127 | d127-r1-s2 | `15954fb5b7dda53df5a81c0d473e7d34a0830936b9ad0e4f08665df9af28bc60` | Analysis.HermiteHadamard | private lemmas `fejer_pair_le`, `fejer_integrable`, `fejer_integrable_refl`, `fejer_integral_refl`; theorems `convexOn_midpoint_mul_integral_le`, `integral_mul_le_endpoints`; `open MeasureTheory Set` and `open scoped Interval` (lines 14, 15); root namespace | round 1's review (line 59): FAITHFUL; carry s2 |
  | 128 | d128-r1-s2 | `adf20df5b59da245f6e3d0147b63260e3d8d006b45fb7dd23b0daef90bceab2d` | Analysis.EulerMaclaurin | private lemmas `bernoulliFun_two_eq'`, `intervalIntegrable_B2_mul`, `unit_step`, `integral_sawtooth_mul_eq'`; theorem `sum_eq_integral_add_two`; `open Set Finset intervalIntegral MeasureTheory ClassicalLean` (line 10); root namespace | round 1 (line 59): FAITHFUL; carry s2 |
  | 129 | d129-r2-s1 | `53cf1a1a289ce4b179bd0e1fc46252f00912ccc362317e885d65851cc65592f2` | Analysis.LinearODE | `variable {n : Type*} [Fintype n] [DecidableEq n]` (line 14); private lemmas `exp_smul_mul_exp_smul`, `exists_clm_exp`; theorem `eq_exp_smul_mulVec_add_integral`; `open Matrix` (line 12); root namespace | round 1 (line 59): FAITHFUL; its "129 s1" is this file, round 2's first sample (lines 36 and 43; claude-ai's reading) |
  | 132 | d132-r1-s1 | `a6c68b6b51a0d5058c51d476bc2235cb8a6b1162a5fd8853f7e93137187f1df6` | Analysis.JacobiIteration | in `namespace ClassicalLean.Analysis` (lines 5 to 96) with `variable {m : ℕ}` (line 7): defs `gaussSeidelUpdate`, `gaussSeidelStep`, `gaussSeidelIterate`, private lemmas `gs_fold_bound`, `norm_gaussSeidelStep_sub_le'`; at the root, after `open ClassicalLean.Analysis in`, theorem `norm_gaussSeidelIterate_sub_le`; `open Finset Matrix` (line 3) | review r6 (line 142): GENERALIZED; minor (line 148): make the one-sweep lemma public |
  | 133 | d133-r1-s1 | `1231b7a5afc464086bae02baef5e029a07dfaa48bdfd05f772f31a3e89d41c79` | Analysis.RoundingError | defs `subComputed`, `forwardSubstComputed`, private def `deltaL`, private lemmas `subComputed_congr`, `forwardSubstComputed_eq_sub`, `subComputed_mul_prod`, `gamma_mono'`, `abs_one_add_mul_prod_sub_one_le'`, `one_add_ne_zero'`; theorem `exists_forwardSubstComputed_eq`; `open Finset ClassicalLean.Analysis.RoundingError` (line 3); root namespace | r6 (line 142): FAITHFUL; minor (line 148): "add `ΔL i j = 0` above the diagonal" |
  | 146 | d146-r3-s1 | `d07963a6aec5b6e3cfae5d4cce17fed407057c458d22f1400c69106221a7e76d` | Analysis.EulerMethod | in `namespace ClassicalLean.Analysis` (lines 15 to 23): def `heunIterate`; then `open ClassicalLean.Analysis` (line 25); private theorems `heun_abs_add`, `heun_abs_le_of_deriv`, `heun_trapezoid`; theorem `abs_sub_heunIterate_le`; `open scoped NNReal` (line 13) | r6 (line 142): FAITHFUL; carry r3-s1 (line 143) |

- **Their plan rows** (MATH-PLAN-library-2.md at the lane root's `inbox/threads/staging/`, sha256
  `6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166`; section 7, lines 436, 437, 438,
  441, 442 and 455): 127 Fejér's inequality, `f((a + b)/2) ∫ g ≤ ∫ f g ≤ ((f a + f b)/2) ∫ g` for
  convex `f` and a weight `g ≥ 0` symmetric about the midpoint (library `convexOn_midpoint_le_average`);
  128 Euler–Maclaurin to second order with the remainder `∫ B₂(fract t)/2 · f''` (library
  `sum_eq_integral_add`; Mathlib `bernoulliFun_two`, `periodizedBernoulli`); 129 variation of
  constants, `x t = exp(t A) x₀ + ∫₀ᵗ exp((t − s) A) f(s) ds` (library `eq_exp_smul_mulVec`); 132
  Gauss–Seidel for a strictly diagonally dominant matrix shrinks the error by at least the Jacobi
  factor `ρ` each sweep (library `norm_jacobiStep_sub_le`); 133 forward substitution is backward
  stable, `(L + ΔL) x = b` with `|ΔL| ≤ γ_n |L|` entry by entry (Higham 2002, Theorem 8.5; library
  `abs_prod_one_add_sub_one_le`, `gamma`); 146 Heun's method has global error of order `h²` (library
  `abs_sub_eulerIterate_le`, its pattern).
- **The drafts' main statements** (read from the files; `lean/LEAN-36/notes.md` lists them): 127's two
  theorems take `hab : a ≤ b`, `hf : ConvexOn ℝ (Icc a b) f`, `hfc : ContinuousOn f (Icc a b)`,
  `hg : IntervalIntegrable g volume a b`, `hg0 : ∀ x ∈ Icc a b, 0 ≤ g x` and
  `hgs : ∀ x ∈ Icc a b, g (a + b - x) = g x`; 128 takes integers `a ≤ b`, `f` continuous on `[a, b]`
  with derivative `f'` on the open interval, `f'` continuous with derivative `f''` there, `f''`
  interval-integrable, and states `∑ k ∈ Icc a b, f k = ∫ f + (f a + f b)/2 + (f' b − f' a)/12 −
  ∫ bernoulliFun 2 (Int.fract t) / 2 * f'' t`; 129 takes `hf : Continuous f`, `hx : ∀ t, HasDerivAt x
  (A *ᵥ x t + f t) t` and `t`; 132 takes `hdiag`, `hrow : ∀ i, ∑ j ∈ univ.erase i, |A i j| ≤ ρ * |A i i|`,
  `hρ1 : ρ ≤ 1`, `hy : A *ᵥ y = b` and `k`, and bounds `‖gaussSeidelIterate A b x₀ k − y‖` by
  `ρ ^ k * ‖x₀ − y‖`; 133 takes `hl`, roundings `ε`, `δ`, `ρ` at most `u`, `h : n * u < 1`, and gives
  `∃ ΔL` with `|ΔL i j| ≤ gamma u n * |l i j|` for `j ≤ i < n` and the rows of `(L + ΔL) x = b`; 146
  takes `hy`, `hG` (the derivative `G` of `t ↦ f t (y t)`), `hM`, `hK`, `hL`, `hL0 : 0 < L`, `hh : 0 ≤ h`
  and `k`, and bounds the error by `h² (K + 3 L M) / (12 L) · (exp (L k h) − 1)`.
- **Names.** In a file importing `ClassicalLean` at `354d835` (`p3/B.out`), none of the drafts' 35
  declared names exists under `ClassicalLean.Analysis`, `ClassicalLean`,
  `ClassicalLean.Analysis.RoundingError` or the root; no line of the six modules has `private`, with or
  without attributes before it (`gather/g18.out`), and no declaration line in them names one of the 35 (`gather/g17.out`,
  `411c3db661143a5574736f477008cb67a75df75f77d4751be2c0bd434cd86eef`). Of the helpers' likely twins: Mathlib's
  `bernoulliFun_two` exists (`Mathlib/NumberTheory/ZetaValues.lean` line 63, `bernoulliFun 2 x = x ^ 2 -
  x + 6⁻¹`; d128's `bernoulliFun_two_eq'` states it with `1 / 6` and proves it by a `first` block whose
  unused branches give EulerMaclaurin's three warnings below); `abs_add_le` exists (d146's
  `heun_abs_add` states `|x + y| ≤ |x| + |y|`); RoundingError has `gamma`, `gamma_nonneg`,
  `self_le_gamma`, `abs_one_add_mul_sub_one_le` and `abs_prod_one_add_sub_one_le` (its lines 58 to 211)
  and no monotonicity lemma for `gamma` (d133's `gamma_mono'`).
- **Imports and closure** (`p3/`): d129 elaborates rc 0 without its FundThmCalculus line (`p3/A.out`), so
  LinearODE needs no import line. A file importing `ClassicalLean` has 5729 modules, and both
  `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus` and
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds` are among them (`p3/B.out`): an import line of
  either in a library module adds nothing to the root's closure. `probe1.lean`
  (`8a2117f4213bae327c2ae29aa962ab49096891ee9ac7bb4d87e7a3e83dc325a8`) has one import line, `import
  ClassicalLean.Analysis.EulerMethod`; its ten "Unknown" lines name eight distinct constants
  (`probe1.out`): `Real.hasDerivAt_sin`, `Real.hasDerivAt_cos`, `Real.lipschitzWith_sin`,
  `Real.lipschitzWith_cos`, `Even.convexOn_pow`, `Continuous.intervalIntegrable`,
  `ClassicalLean.Analysis.hasDerivAt_exp_smul_mulVec` and `bernoulliFun_two`. The last four are names
  other modules' witnesses use, known there (the witness probe); the four trigonometric ones are outside
  EulerMethod's closure. The two replacements the Goal list names are known in their modules:
  `bernoulliFun_two` (`∀ x : ℝ, bernoulliFun 2 x = x ^ 2 - x + 6⁻¹`) in a file importing EulerMaclaurin,
  `abs_add_le` (`|a + b| ≤ |a| + |b|` in a lattice-ordered group) in one importing EulerMethod
  (`probe5a.out`, `probe5b.out`, written 17:39:34 and 17:39:37 EDT by their mtimes, `gather/g17.out`;
  a check with no prediction file). `Real.lipschitzWith_sin` and `Real.lipschitzWith_cos` are in
  `Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean` (lines 273 and 276). Each of the six
  modules is imported by the root file `ClassicalLean.lean` only (grep of `import` lines).
  EulerMethod with only the line `import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds` added
  (`p4out/`, probe 4): `lake build` rc 0, 4193 jobs, 0 warnings, rebuilding EulerMethod and the root
  only; the type dump before and after, 4088 records each, `DIFF removed=0 added=0 changed=0
  proof_only=0` (the two dump outputs are byte-identical); the module restored and rebuilt after.
- **The six home modules at `354d835`** (sha256; namespace; where its block ends; what follows):
  - `ClassicalLean/Analysis/HermiteHadamard.lean` `b3cdb1b987433cf120f55413e468e87acd4c0fdd9ae165a5f24be71a82cf79f8`, 199 lines; `open MeasureTheory Set intervalIntegral Finset` and `open scoped Interval` (lines 65, 66); `namespace ClassicalLean.Analysis` (line 68) to its `end` at line 177; no `variable` line; three witnesses after the block (examples at lines 182, 189, 197, each behind `open Set in`).
  - `ClassicalLean/Analysis/EulerMaclaurin.lean` `18a9cc286f8e33261ab99bba16ac7d5d883ee2a183394a76b179c0ec7dbcdfd3`, 176 lines; `open Set Finset intervalIntegral MeasureTheory` (line 66); `namespace ClassicalLean` (line 68) to its `end` at line 167; no `variable` line; one witness (example at line 173).
  - `ClassicalLean/Analysis/LinearODE.lean` `d609383af0c163625fe0484e48e43bbe002a0db733624f2aa6efbae20043b927`, 169 lines; `open Matrix` (line 66); `namespace ClassicalLean.Analysis` (line 68) to its `end` at line 148; `variable {n : Type*} [Fintype n] [DecidableEq n]` (line 70, the same as d129's line 14); `omit [DecidableEq n] in` at line 101; two witnesses (examples at lines 154, 163, each behind `open Matrix in`).
  - `ClassicalLean/Analysis/JacobiIteration.lean` `fa86ff1870052f238933e1686c2807ede028fd59ac3eaace4cfda0a39c8e42a4`, 175 lines; `open Finset Filter Topology Matrix` (line 58); `namespace ClassicalLean.Analysis` (line 60) to its `end` at line 165; `variable {n : Type*} [Fintype n] [DecidableEq n]` (line 62); one witness (example at line 171, behind `open Finset Matrix in`).
  - `ClassicalLean/Analysis/RoundingError.lean` `210ec06875968651d7980f2ad24e44e394a0ea235a939f69b96fbe45e3c3adcb`, 293 lines; `open Finset` (line 53); `namespace ClassicalLean.Analysis.RoundingError` (line 55) to its `end` at line 279; no `variable` line; two witnesses (examples at lines 284, 291).
  - `ClassicalLean/Analysis/EulerMethod.lean` `ae34a15e39b9bbb7a43721aae8e26b7b7ae4c2fb8633abd10e3de13beaf585ee`, 255 lines; one import, `ClassicalLean.Analysis.GradientDescent` (line 7); `open scoped NNReal` (line 102, d146's line 13); `namespace ClassicalLean.Analysis` (line 104) to its `end` at line 231, with `open Filter Topology in` at lines 183 and 201; three witnesses (examples at lines 237, 248, 254).

  HermiteHadamard, LinearODE, JacobiIteration and EulerMethod share the namespace
  `ClassicalLean.Analysis`, so a new name in one must not exist in the others (the name check
  above covers it).
- **The witness probe** (`p2out-r3/`, run after cold review 2; draft r0's run is `p2out/`, store row
  20261026-053, r1's `p2out-r2/`, row -054): each draft appended to its module in claude-ai's clone, with claude-ai's witness blocks
  (`lean/LEAN-36/data/witnesses.txt`, sha256
  `2bc14e815ecf3ceb8f2bbe34268aa2831ca7884ed7015fe6f683e838dc719d17`; the same bytes as the run's
  file), the one-sweep lemma public as `norm_gaussSeidelStep_sub_le`, the import line
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds` in EulerMethod and no other import line
  (LinearODE without d129's FundThmCalculus line; draft r0's run carried it): `lake build` of each
  module rc 0, no error; the witness gate, from the clone's root, in the form
  `python3 -I tools/witness_gate.py Analysis/HermiteHadamard.lean Analysis/EulerMaclaurin.lean
  Analysis/LinearODE.lean Analysis/JacobiIteration.lean Analysis/RoundingError.lean
  Analysis/EulerMethod.lean` (`~/api-credit/l36/probe2-r3.sh`,
  `baa545ba34ff6f99c23184562bec70c8b00644701678cf92558bf772f9e55f62`), rc 0 in 82 s,
  `WITNESSGATE PASS modules=6 elaborated=6 OK=20 … BROKEN=0 … copy-error=0` (`p2out-r3/gate.out`,
  `0e780fc29463ea250d163fae0bc03ecf1713a5a81e6f2ecdcc02efbba4a856a4`): the twelve older blocks and the
  eight new ones OK, each new one with every binder before the colon supplied (`k = n`: 127's two 10
  and 10, 128 11, 129 9, 132 11, the one-sweep lemma 10, 133 12, 146 16). Warnings of that build,
  counted on lines starting `warning:`, none in a witness block, all in the drafts' text:
  HermiteHadamard 0, EulerMaclaurin 3 (the `first` block of `bernoulliFun_two_eq'`), LinearODE 19
  (unused tactics, never-executed tactics, `show` lines), JacobiIteration 0, RoundingError 7 (the
  unreferenced name `h` in `if h : j < i` in the body of the def `forwardSubstComputed`, and six
  deprecated `if_pos`/`if_neg` in proofs), EulerMethod 10 (unused simp arguments, never-executed
  tactics). Draft r0 said RoundingError 8: its counter matched any line containing `warning`. The
  probe's run 1 after review 1 (`p2out-r1/`) also warned on one docstring line of claude-ai's in each
  of JacobiIteration and RoundingError (over 100 characters); they were rewrapped for run 2. The
  witness blocks name the drafts' theorems at the root, where the probe put them; in this order they
  land in namespaces, so the witnesses use the full names (rule 5). Their arithmetic, exact
  (`lean/LEAN-36/scripts/witcheck.py`, `b76e4491c9149223dd8f1b9ff679e4469c613cc1b75f0c5641761bba27c2fa74`;
  its output `lean/LEAN-36/data/witcheck.out`,
  `df9993f572743c4ea297c7d56e7ef9b1004b768add04263c56b40ef720eb1987`): 127's two sides are strict on the
  witness (`1/24 < 1/20 < 1/12`); 128's remainder is `0` for a cubic `f` and `1/30` per period for
  `f = x⁴` (so the witness uses `x⁴`); 129's curve solves the equation (residual `[0, 0]`, by sympy's
  matrix exponential); 132's Gauss–Seidel sweeps move, `(3/2, 15/8)`, `(33/32, 255/128)`,
  `(513/512, 4095/2048)` (the first is the one-sweep witness's); 133's `n u = 1/5 < 1`; each of 146's
  three Heun steps moves, `u₁ ≈ 0.09976`, `u₂ ≈ 0.19854`, `u₃ ≈ 0.29535` from `u₀ = 0`. For 146 the witness takes `y = sin` with
  `f t y = cos t + (y − sin t)`, so `G = −sin` is not constant and `hK` is used with `K = 1 > 0`: with
  `G` constant, `K = 0` would do and the bound's `K` term would test nothing. (Draft r0 said a constant
  `G` makes Heun's method exact. That was false, review 1's F1: `f t y = t + (y − t²/2)` with
  `y = t²/2` has `G = 1`, and one step from `(0, 0)` misses `y h` by `h³/4`.)
- **The type dump (rule 14):** LEAN-33's lane copies of rule 14's pair,
  `lean/LEAN-33/scripts/TypeDumpPI.lean` (`1fcb69f41ddbd35f84862521d2ead5946a0bd52caf5f60b6d10e966cfd9776ff`) and
  `lean/LEAN-33/scripts/g8-typediff.py` (`371eda9a2e5065abaa8f36bac9872d0f15e7bade72a248d5f0f88f20b4eacb71`;
  copy it as `g8_typediff.py`), the same bytes as `~/lean/vacuity4-checks/inputs/`.
- **Master and the gates at it.** Both remotes (`/data/git/classical-lean.git` and GitHub) at
  `354d8358f247740acadc5b9b0fa25722fab4f584`, VACUITY-4's last commit, pushed by Dustin (DSMain's bare
  master ref written 2026-10-26 16:09:29 EDT; claude-ai's `ls-remote` of both at 16:11 EDT); its
  GitHub CI run #40 `success`, 16m 34s. The library tree at `354d835` equals G' `7ebda52`'s and G
  `6951c86`'s (tree hash `369469c2c5a8bd1bdbe16f0532099874fcafd96c`), where VACUITY-4 measured, in
  `~/lean/vacuity4-checks/` (at G `6951c86` unless said otherwise; `git diff --name-only` gives
  `HANDOFF.md`, `tools/WitnessListing.lean` and `tools/witness_gate.py` from G to G' `7ebda52`, and
  three files under `records/`, not `records/rules.toml`, from G' to `354d835`, whose `rules.toml` is
  the same at all three, `gather/g17.out`; VACUITY-4 ruling 6 section 2 item 3 planned G'): build 4193 jobs (`j6-build.out`); AxiomGate PASS 3602 (`j6-axiom.out`);
  VacuityGate PASS, 1 reviewed helper, 0 VACUOUS-PENDING, 0 run-outs (`j6-vacuity.out`); the vacuity
  tests 89 tests, 47 flagged, 0 rule-5 run-outs, 0 mismatches (`j6-vactests.out`); check_sorry PASS
  140 (`j6-sorry.out`); check_records PASS 140, 110 files searched, 1 named exemption (`j6-records-final.out`,
  at `354d835`; `g2-records.out` counts 112 records files); the drift check PASS at G' (`gp-drift.out`,
  `a7b4dcf48d844b8b793b64a8c5f2984867a991969fa67f45fe0b51fe636bfa27`, "PASS no drift"; HANDOFF.md and
  `records/rules.toml` are the same at G' and `354d835`, `gather/g17.out`); `banned_vocab_scan.py` PASS, 140 files and the
  root file, 0 hits (`j6-banned.out`); rule 27's module count 5729 (`j6-modcount.out`); the type dump
  4088 records (3602 thm, 486 def), elided 0, missing_fields 0 (`j6-td-check.out`); gate 7 ALL PASSED
  for `6951c86`, 140 modules 0 failed, the planted fault named, 23:22.52 (`j6-gate7.out`); the witness
  gate at G' `WITNESSGATE PASS modules=140 … OK=171 … copy-error=0`, 26:48.84 (`gp-witness.out`) and its
  tests 119 cases, 0 mismatches (`gp-witness-tests.out`).
- **Records at it:** the last round is 73 (VACUITY-4,
  `records/rounds/20261026T024200Z__round-73-witness-gate-older-witnesses-gate-leftovers.md`), so this
  order's is 74; check_records searches 110 files (112 records files by `g2-records.out`'s count). VACUITY-4's push, for your records commit (records/README.md rule
  2), is the text
  ``; pushed by Dustin: DSMain's master ref written 2026-10-26 16:09:29 EDT, GitHub master equal (`354d835`)``
  (from its `;` to its `)`) inserted at one anchor in each of two rows, both their files' last lines at
  `354d835`: in `records/orders/INDEX.md` (74 lines) VACUITY-4's row, right after `rulings 2 to 6`
  (once in the file); in `records/CLAIMS.md` (66 lines) VACUITY-4's row, right after `after claude-ai's
  push review` (five times in the file, once in its last line, at that line's end). Do it by a script
  that finds each row as its file's last line and checks its start (INDEX: `| VACUITY-4 |`; CLAIMS:
  `| 2026-10-26 02:41` and that the line contains ``executing order `VACUITY-4` ``), refuses unless the
  anchor occurs once in that line, inserts before anything is appended, and asserts, before
  inserting, exactly this (a fenced block, so spaces count; `A1` is the INDEX anchor and `A2` the
  CLAIMS anchor above, `i` where each starts in its line, `line` the file's last line without its
  newline):

  ```
  INDEX:  after = line[i + len(A1):]; assert after.startswith(" | `661a181` (records); ")
  CLAIMS: after = line[i + len(A2):]; assert after == " |"
  ```

  The latest bridge baseline is `records/bridges/LEAN-35/` (`COMMIT` names
  `d21fd222a432a1d2de6802347fbcd4fdd5978dbb`, LEAN-35's G; `pairs.tsv` 3024 lines, `shapes.tsv` 775;
  VACUITY-4 ran no bridge search and changed only `example` blocks and prose);
  `tools/vacuity_reviewed.txt` holds 1 entry, `ClassicalLean.Simplex.orderedSimplex_subset_closedSimplex`;
  `tools/witness_reviewed.txt` holds 1 entry, PrimitiveDivisor's name-resolution check; ROADMAP.md's
  last section is 1.29 (line 879), so yours is 1.30. `records/rules.toml`
  `2b5fb47dc4751d93171969649f9dc4f7b7e1233cdbc36bb06713c20e23bb0359`, 39 rules (HANDOFF section 6's
  generated block); HANDOFF.md 1409 lines, sha256
  `6c40032d09e2a05e17df37bdeb678bcb8480f7aa3c4ad89e0eec1b73337b98ff`.
- **The worktree** `~/lean/classical-lean-paper-crypto` is on branch `vacuity-4` at `354d835`, clean.
  Remotes: `origin` the bare repo, `github` GitHub.
- **Helpers:** VACUITY-4's, in `~/lean/vacuity4-checks/scripts/` (28 files) and the two census tails
  `~/lean/vacuity4-checks/census/census-all-tail-lean28.lean`
  (`83de4147767d603ef129cc674f0b7a2d97531072108762618b2ca01aeb06baa8`) and
  `census-tail-lean28.lean` (`2c950fc9d39cfea54562aae80bac14a36f2cbef9e9ec5150143ca6437eb56d6b`); the
  other entries of its `census/` are its outputs, not helpers. Their sha256s are in
  `~/api-credit/l36/gather/g12-helpers.out` (read at 17:02:05 EDT). Lines naming `vacuity4-checks`:
  `commit.sh` 1, `docs-insert.py` 1, `el.sh` 1, `evcite.py` 2, `ev.sh` 1, `hl.sh` 1, `mkcensus.sh` 1,
  `probecheck.py` 1, `records2.py` 1, `rootrun.sh` 1, the other 18 none; one `BASE = ` line,
  `probecheck.py` line 29, `BASE = 'ac62f50'`; `commit.sh` line 16 carries VACUITY-4's two attribution
  trailers (`Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>` and `Claude-Session:
  https://claude.ai/code/session_01CaiSGfxRa9So88se5LzGkG`); `allowlist.txt` (`~/lean/vacuity4-checks/`)
  sha256 `a4ebb5b5a35d2f3145ec951e4a053236016bbfa1cad76e73e1cbcaa249dfe738`, 38 lines.
  `mkwitcheck.py` is among the scripts; this order does not run it (rule 13: the witness gate
  supersedes it).
- **Timers on DSMain** (read 17:02:22 EDT): crontab restic 02:20, the daily verify 03:00, the backup
  bundle 03:30, the store sync 05:40; user timers memory-index at midnight, ds-hygiene about 02:51,
  lean-nightly 03:30, launchpadlib-cache-clean 21:53, w29-tracker and w29-sysmap every few minutes
  (they load no Lean). 16 cores, 62 GB of memory. Read them again before you start (Scope).

## Goal

The six items proved in their home modules, each inside its module's namespace, with witnesses
that pass the witness gate, reviews and records; no existing declaration changed (the type dump
shows it); every gate passing, gate 7 and the witness gate included; the bridge search and the
report tool run; HANDOFF.md and ROADMAP.md saying what changed. Dustin pushes after claude-ai checks
the push-review file.

The changes asked of each draft (from the measurements above):
- **Every item:** its declarations go inside its home module's namespace block, before that block's
  `end`, reusing the module's own `variable` line where it is the draft's (LinearODE's line 70 is
  d129's line 14: drop the draft's copy); a draft's own namespace lines are dropped where the module's
  block already is that namespace (132 and 146 open `ClassicalLean.Analysis` themselves); the draft's
  `open` lines the module lacks become `open … in` on the declarations that need them, and an `open` of
  the namespace itself is dropped; references the namespace makes ambiguous or wrong are written in
  full (job 1's type comparison for statements; `el.sh` on the module for proofs); each main theorem's
  docstring names its item ("Item 127 of MATH-PLAN-library-2") and its draft; the module docstring lists
  the new results; a step whose effect is not determined is cut to what fires; a private helper whose
  statement Mathlib or the module already proves is replaced by that name (the module review asks it of
  each helper; the two known replacements are named below, 128's `bernoulliFun_two_eq'` and 146's
  `heun_abs_add`, and 133's `gamma_mono'` is kept); every warning `lake build` reports is fixed in
  the proof only, except the one the probe saw outside a proof, the unreferenced `h` of `if h : j < i`
  in the body of 133's def `forwardSubstComputed`, which is written `_h` there (the def's term is
  unchanged; if its termination proof then fails, keep `h` and report the warning as a miss), and except a warning that a section variable is unused, which is fixed by `omit … in`
  before the declaration's docstring (LinearODE line 101 is the pattern), as is a warning that a
  section variable's instance is unused in the type; the same warning on a declaration's own binder is
  reported and the statement kept (rule 1). Each fix is listed in round 74.
- **127:** the four private lemmas and the two theorems before `end` (line 177); the module's opens
  cover the draft's (`MeasureTheory`, `Set`, `Interval`). Verdict FAITHFUL (round 1).
- **128:** three private lemmas (`bernoulliFun_two_eq'` replaced, below) and the theorem before `end`
  (line 167), in `namespace
  ClassicalLean`; the draft's `open … ClassicalLean` dropped (the namespace); `bernoulliFun_two_eq'`
  replaced by Mathlib's `bernoulliFun_two` at its uses (`6⁻¹` for `1 / 6` where a step needs it), which
  removes the module's three measured warnings. Verdict FAITHFUL.
- **129:** the two private lemmas and the theorem before `end` (line 148), after line 70's `variable`;
  no import line (measured: d129 needs none, `p3/A.out`, and LinearODE with d129 and its witness builds
  and passes the witness gate without one, `p2out-r3/`). Verdict FAITHFUL. For the plan-fit check: the
  row's "the one solution of `x' = A x + f(t)` is …" is stated as the form of every solution; that the
  formula is a solution (round 1's optional existence half, API-CREDIT-1 line 59) is not in the draft
  and not taken (Not in this order).
- **132:** the three defs, the private `gs_fold_bound`, the one-sweep lemma and the theorem before
  `end` (line 165); the draft's `variable {m : ℕ}` kept in a `section` of its own around the defs and
  lemmas that use it (the module's `variable` line binds `n`, not `m`), or `{m : ℕ}` written into each
  signature: say which in the plan; the one-sweep lemma `norm_gaussSeidelStep_sub_le'` made public as
  `norm_gaussSeidelStep_sub_le` (review r6's minor; check first that the name is free under the
  namespace; measured: no name containing `gaussSeidel` in the library at `354d835`, grep, and
  JacobiIteration builds with it, `p2out-r3/`), its statement unchanged, with a witness of its own
  (the eighth block: one sweep from `x = 0` moves to `(3/2, 15/8)`). Verdict GENERALIZED (review r6); claude-ai's reading, for the
  plan-fit check and its review to confirm: `ρ ≤ 1` (weak diagonal dominance, with `ρ = 1` allowed and
  the bound then only `≤`) where the row says strictly dominant, and any start `x₀`.
- **133:** the defs, the private def and the six private lemmas and the theorem before `end` (line
  279), in `namespace ClassicalLean.Analysis.RoundingError`; the draft's `open … RoundingError` dropped;
  `gamma_mono'` kept unless the module review finds it proved elsewhere (RoundingError has no
  monotonicity lemma for `gamma`); `abs_one_add_mul_prod_sub_one_le'` compared by the review with the
  module's `abs_prod_one_add_sub_one_le`, `abs_one_add_mul_sub_one_le` and `abs_mul_prod_sub_le` (a
  product with an extra factor, like it; `g14-dups.out` line 103). Review r6's minor "add
  `ΔL i j = 0` above the diagonal" is not taken: it changes the drafted statement (rule 1); it is listed
  in Not in this order. Verdict FAITHFUL.
- **146:** `heunIterate`, two private theorems (`heun_abs_add` replaced, below) and the theorem before
  `end` (line 231); the
  draft's own `namespace`/`end` and `open ClassicalLean.Analysis` dropped; `heun_abs_add` replaced by
  Mathlib's `abs_add_le` at its uses. For its witness EulerMethod gains
  `import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds` after its last import line (line 7):
  the witness needs `Real.hasDerivAt_sin`, `Real.hasDerivAt_cos`, `Real.lipschitzWith_sin` and
  `Real.lipschitzWith_cos`, none in EulerMethod's closure, and the line adds nothing to the root's
  closure, and alone it changes no constant of the library in the type dump (both measured above,
  probe 4); claude-ai's ruling, Dustin's veto open (store row 20261026-053). EulerMethod
  is imported only by the root file. Verdict FAITHFUL.

## Scope

- **Branch.** `lean-36` from `354d835` in `~/lean/classical-lean-paper-crypto`, made after Dustin
  approves your plan. Nothing pushed. No sudo.
- **You may change in the repository:** the six home modules above, and in them only: new
  declarations inside the namespace block (the Goal list), the one import line named (EulerMethod's),
  the module docstrings' lists of results, witnesses after the last line (rule 5). Also
  `tools/vacuity_reviewed.txt` (rule 4 only), `records/`, and `HANDOFF.md` section 1 and `ROADMAP.md`
  (job 4).
- **You may not change:** any other module, any existing declaration of the six (the type dump checks
  it), any other import line, `ClassicalLean.lean`, anything else under `tools/` (the witness gate and
  its lists included: a needed change there is a stop), `.github/`, `records/rules.toml`, the lake
  files, `HANDOFF.md` sections 0 and 2 to 6 (section 6's drift check hashes the text outside the
  generated block too). Needing to is a stop: report it.
- **You may write in the lane:** the plan, the report and the push-review file through `ds_file`; rows
  from 166 in the bridges file (job 5b). Nothing else.
- **Off limits:** the main clone `~/lean/classical-lean` and its `master`; `~/break-it-5`; `~/trading`;
  `~/lean/recheck` (`run-recheck.sh` is run as gate 7, not edited); every earlier order's folder under
  `~/lean/` (read only; `~/lean/vacuity4-checks/` is the source of your helpers); Dustin's
  `~/.config/classical-lean/banned-terms` (the scanner reads it; never print or copy it); every GitHub
  branch (no push, no delete); `/data/api-credit/` (read only); `~/api-credit/` and `/tmp/claude-ai-*/`
  (claude-ai's; you may read `~/api-credit/l36/` only, never write there).
- **The night window and the memory cap,** as `ev.sh` enforces them (its header names the window;
  rule 36: name the window, do not copy its times). Before each whole-library run, log `pgrep -ax lean`
  through `ev.sh --nolean` (rc 1 when none runs) and wait while another Lean process runs; reviewers
  run no Lean while you do; claude-ai starts no Lean run on DSMain while this session runs, unless
  Dustin says so. Start gate 7 or the witness gate's whole-library run only when it can finish before
  the midnight timer (their durations at G are above: about 23 and 27 minutes). Every whole-library
  run under `ev.sh --cap` or `rootrun.sh`; never two Lean runs at once; read `crontab -l` and
  `systemctl --user list-timers` before you start; `~/.elan/bin` on `PATH` (the witness gate refuses
  to start without `lake` on it).

## Check, then read

Check these sha256s first; if any differs, stop and say which:
- this order, `lean/LEAN-36/order.md`: the value in Dustin's prompt;
- `~/api-credit/l36/SHA256SUMS-all.txt` on DSMain, `lean/LEAN-36/notes.md`,
  `lean/LEAN-36/data/witnesses.txt`, `lean/LEAN-36/scripts/witcheck.py`, `lean/LEAN-36/data/witcheck.out`,
  `lean/LEAN-33/scripts/TypeDumpPI.lean`, `lean/LEAN-33/scripts/g8-typediff.py`: the values above
  (notes.md: `394b6df8f0b055f5422b5990168f528ff5e4b4846c572a35348ad849059ec229`);
- `lean/LEAN-35/order.md` `037d2022b2669ba034100932761a1f3ed09d77aa39e6f89a0ec0a4c3520a54cc` and
  `lean/LEAN-35/report.md` `6c56b5353f9df4559c2cfcc2f9dae0efddcd2a92f528da0186a4516110e0fcbb` (the pattern
  this order follows), `lean/VACUITY-4/order.md`
  `68996aadffdc8660aa569344d1769453d4b035e49216a2fe8509d3b6936fd1b1`, `lean/VACUITY-4/report.md`
  `43166b8aeb524c298cdfe1496add3e47796d1cbba770c8200b8fdb41c8eb3047` and `lean/VACUITY-4/ruling-6.md`
  `2ec1d4ec41a2f86814fae5ecbcc2b1bf8a045d1fafa98be7f0c9e0c0bea43f90` (the witness gate and its limit);
- `lean/VACUITY-3-ruling-3.md` `aa0d17e403031b81d0e0803c3308002ed985b416d788980de0f61cc79e13a4f2`
  (rule 5 cites it) and the memory lesson `memory/lessons/data/2026-10-25-a-witness-must-move.md` (lane
  root) `0f3ae89cb9bb7dd064d5f2e654da2044713e824cc36a0fec1637a293d177eb42`;
- `lean/MERGE-2-order.md` `81894b5bc85a6ee6858f7a1d8b065ee17ff5034f21df9ef68803cded13e4251a` (setup,
  gates and push review on DSMain);
- `lean/CLOUD-LANDING-PLAN-2.md` `26da22cef5604286b2b4b8fdfed4ec9fd70fb5c8520cb5dbfcd7b5c8411051a5`;
- MATH-PLAN-library-2.md (lane `inbox/threads/staging/MATH-PLAN-library-2.md`)
  `6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166`;
- `work/api-credit/API-CREDIT-1/API-CREDIT-1.md` (lane root)
  `599276c28ba636a8aa56d304c9d81db370b67424f237b9e75941f79f8ad51f43`;
- `lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md`:
  `bc396a1a087b29b85de4f8eadae08c7c0fb00bf3cedcf4afa4e33f7d92eec571` (its last row is 165);
- the six carry files in `/data/api-credit/20261019/carry/`: the values above;
- the helpers and census tails (Setup 1); and the six modules at `354d835`: the sha256s above, since
  every line number this order gives in them is `354d835`'s.

Then read: in the repository `records/README.md`, `HANDOFF.md` sections 1, 4 (the witness gate's
entry and the "Satisfiability witnesses" paragraph with rule 3's case of the moving process) and 6
(all 39 rules), the six home modules in full, the last round's fragment, and VACUITY-4's INDEX and
CLAIMS rows (the pattern for yours); in the lane LEAN-35's order in full and its report, VACUITY-4's
report and ruling 6, VACUITY-3's ruling 3, MERGE-2's order's Setup and Job 4, CLOUD-LANDING-PLAN-2.md rulings 2 and 5,
MATH-PLAN-library-2.md section 7's rows 127, 128, 129, 132, 133 and 146, API-CREDIT-1.md lines 59 and
142 to 148, `lean/LEAN-36/notes.md` (written before the draft: where it differs from this order, for
example on the plan's name, d129's import line, the count of carry files or the run log's place, this
order holds), the witness file and the bridges file's last section; the six
carry files in full; the memory lesson `memory/lessons/data/2026-10-25-a-witness-must-move.md`.

## Rules of this order

1. **Statements as drafted.** Each main theorem (`convexOn_midpoint_mul_integral_le`,
   `integral_mul_le_endpoints`, `sum_eq_integral_add_two`, `eq_exp_smul_mulVec_add_integral`,
   `norm_gaussSeidelIterate_sub_le`, `exists_forwardSubstComputed_eq` and `abs_sub_heunIterate_le`), and the public one-sweep lemma
   `norm_gaussSeidelStep_sub_le`, keeps its draft's statement, apart from the Goal list's changes and the move into its namespace.
   Never weaken, restate or add a hypothesis to make anything easier. A statement you find false is
   reported with its counterexample and narrowed, said plainly in its docstring, round 74 and the
   report; never dropped silently.
2. **Namespaces and imports.** Every new declaration, private ones included, sits inside its home
   module's namespace block; the axiom gate checks only constants under `ClassicalLean`. Only the one
   import line named in the Goal list is added; no other import line anywhere changes.
3. **No existing declaration changes** (HANDOFF rule 14). A type dump of the whole library
   (`TypeDumpPI.lean`, through `rootrun.sh`, because it imports `ClassicalLean`) at the records commit
   and again at G (rule 7), compared by `g8_typediff.py diff`, read by its `DIFF` line (its exit code is
   0 whenever nothing is CHANGED, even with REMOVED lines): predicted `removed=0 changed=0
   proof_only=0`, and `added=` the new constants (job 3). EulerMethod's import line alone was measured
   (probe 4: all zeros); the drafts' text with it was not, so a `PROOF-ONLY` line in EulerMethod is a
   possible miss of this prediction. A `REMOVED` or `CHANGED` line is a stop. A
   `PROOF-ONLY` line is listed and explained as rule 14 says, and reported as a miss of this
   prediction. A difference between `added=` and job 3's list confined to auxiliary names is listed and
   explained, not a stop. A new warning in an existing declaration is a stop (Scope).
4. **The vacuity gate as the repository has it.** A flag or an UNCHECKED verdict on a main theorem,
   or on the public one-sweep lemma (for item 132), makes that item not closed (rule 9). On a helper: rewrite it, remove it if Mathlib or `simp` already
   does its job, or list it in `tools/vacuity_reviewed.txt` as HELPER with a one-line reason its
   module's reviewer checks. A VACUOUS-PENDING entry makes the item not closed.
5. **Witnesses** in HANDOFF section 4's form (rule 2's form: `example := Full.name (x := …) h₁ h₂ …`,
   every chosen argument by name and every binder before the colon supplied, optional `open … in` lines
   of their own and no other `open` than the module's top-level ones, the docstring "The hypotheses of
   `name` hold together: …", none of the six forbidden words, one inline block with no helper
   declarations; not degenerate as rule 3, its case of the moving process and VACUITY-3's ruling 3
   say). Eight blocks in all, one for each main theorem (127's two included) and one for the newly
   public one-sweep lemma `norm_gaussSeidelStep_sub_le`, each after its module's
   last line, starting from `lean/LEAN-36/data/witnesses.txt` with each head written as its full name
   (`ClassicalLean.Analysis.convexOn_midpoint_mul_integral_le`, `ClassicalLean.sum_eq_integral_add_two`,
   `ClassicalLean.Analysis.RoundingError.exists_forwardSubstComputed_eq`, and so on). What must move, and
   does in the given blocks: 127 a weight that is not zero and a convex `f` that is not affine (both
   inequalities strict); 128 an `f''` that is not linear (its remainder is then not zero); 129 a push
   `f` that is not zero; 132 iterates that change at every sweep before `k`, and for the one-sweep lemma
   a sweep that moves `x`; 133 roundings that are not zero; 146 a solution whose `G` is not constant,
   so that `K > 0` is used, and Heun iterates that change at each of the `k` steps. A block you change keeps these properties, and its
   docstring says how. Log `date +%s` through `ev.sh` when you start each; one still missing 1800
   seconds later makes its item not closed.
6. **Records.** As `records/README.md` says. The records-first commit: this order's copy, its INDEX
   row (`| LEAN-36 |`) and CLAIMS row at the bottom, the push of VACUITY-4 inserted in VACUITY-4's INDEX
   and CLAIMS rows (records/README.md rule 2, as the facts above give it), and round 74's fragment
   naming the six module files by full path. Round 74's fragment gives each module's theorem-constant
   count from the census (rule 27) and gets its commit hashes in a follow-up edit once they exist,
   never predicted.
7. **Predict, then measure; the tree that counts.** As LEAN-35's rule 7: an evidence folder
   `~/lean/lean36-checks/` with `evidence.log`; every prediction file hashed into the log (`hl.sh`)
   before its run; hashes in records and the report by script, never typed; git, hash and records
   commands as `ev.sh --nolean`; every commit through `ev.sh --nolean` as `git commit -F <message file>`
   with a label starting `commit-`, then `COMMIT <hash>` appended to `evidence.log`; a helper you must
   run after generating a message's `Evidence:` line, and before its commit, takes a label starting
   `commit-`. Every gate runs on the clean tree of the last commit that touches anything outside
   `records/` (call it G); later commits touch only `records/`. A clock time in any prediction or brief
   is read from a clock, never typed.
8. **Reviews.** Job 1's statement review, then six cold reviews once their text is final: (a)
   HermiteHadamard (127), (b) EulerMaclaurin (128), (c) LinearODE (129), (d) JacobiIteration (132), (e)
   RoundingError (133), (f) EulerMethod (146), each by a fresh subagent that has not seen your work, with
   a brief built by script as rule 26 says. Each brief caps its reviewer at 40 tool calls; at the cap it
   writes what it has and lists what it did not check, and anything listed as not checked gets a fresh
   reviewer for those parts only before the commit. A module review checks each statement against its
   plan row (FAITHFUL, GENERALIZED or WEAKER; WEAKER is a finding), every hypothesis used, each witness
   against rule 5 (what moves included), every new declaration in the namespace, the import line, every
   private helper's statement and whether Mathlib or the module already has it, and no main theorem
   whose conclusion is a recursive predicate that is `True` everywhere. A review with findings ends with
   a confirming pass on the fix only, by a fresh reviewer. At most two fix-and-confirm rounds; an item
   not clean after two is not closed. If a model's safeguards refuse a reviewer's brief, run that
   review on the Sonnet copy of the review route, as VACUITY-4 did, and say so in the report.
9. **Not closed.** An item not closed is undone by a new commit (never a reset): its declarations,
   witnesses, import line, module-docstring entries and vacuity-list entries removed, and round 74, the
   CLAIMS row and the report saying which item and why. The others go on.
10. **Master does not move under you.** If `origin/master` or GitHub's `master` is not `354d835` at
    "Before approval" or when you write the push-review file, stop and report: claude-ai then writes
    the merge step. Never merge or rebase anything yourself.
11. **Nothing is added during the run.** The Goal list, the jobs and the checks are this order's, all
    of them. Nobody adds a job, a check or the wording of a result while you run, claude-ai included: a
    finding outside the Goal (a fault in an older module, a gap in a tool, an idea for the library) is
    written down with its evidence and goes to the report's list for a later order; it is not chased. A
    heads-up (a side note Claude Code shows on Dustin's screen, not in your conversation) reaches you
    only when Dustin passes it in; each one that reaches you is answered in your next message and listed
    in the report with your answer, and you act on one only when it names a stop under these rules.
    claude-ai rules during the run only on a stop.
12. **A count is what its output says.** Every count in round 74's fragment, the report and your
    replies is read from a saved output and cited by its path and line. No message sets a count or the
    words of a result in advance; if one does, the output wins and you say so. A check that did not give
    a verdict on everything is stated as how many it confirmed and which it did not, each with why,
    never as "N of N checked".
13. **The witness gate, per module and then whole.** After each module's `lake build` in job 2 and
    before its cold review, run the witness gate on that module from the repository root through
    `ev.sh`, its prediction first, in the argument form claude-ai's probe ran (`probe2-r3.sh` above,
    six modules at once), with the one module, for example
    `python3 -I tools/witness_gate.py Analysis/JacobiIteration.lean` (claude-ai did not run the
    one-module form: its first run is job 2's, and a refusal of that form is a stop): every block of the module OK, `copy-error=0`,
    with OK counts HermiteHadamard 5, EulerMaclaurin 2, LinearODE 3, JacobiIteration 3, RoundingError 3,
    EulerMethod 4 (at `354d835` they hold 3, 1, 2, 1, 2 and 3 lines starting `example :=`, all OK in
    VACUITY-4's run); a non-OK line on a new block is a miss: name it, fix it, rerun with the count
    predicted again; a non-OK line on an older block is a stop (Scope): report it, do not edit it; a fix after the gate that touches the module reruns it before the commit. The gate's stated
    limits (HANDOFF section 4) hold: a process that stops moving inside the horizon is not seen by it,
    so the module's cold review reads each new witness for rule 5's "what must move"; and a module's own
    code run inside a tactic branch Lean discards is not seen (review a4c, VACUITY-4 ruling 6): no new
    text uses `(config :=`, `native`, `Lean.reduceBool` or the like (job 5g greps for them).
    `mkwitcheck.py` is not run. The whole-library run is job 5a's.

## HANDOFF's rules in this session

Every rule of `HANDOFF.md` section 6 applies. How, for this order:

| rule | here |
|---|---|
| 1, 2, 3, 10, 15, 18, 19, 22, 28 | as written. Rule 19: credit each proof to its draft (the API-credit pipeline's Claude Opus 5.5 through the Anthropic Batch API, lean/API-CREDIT-CARRY-1.md), adapted by this session; each witness to claude-ai's file, as adapted. Rule 22: every quote in round 74's fragment is checked by a script with a planted misquote (`quotecheck.py`). |
| 12 | Reviewers work in `~/lean/lean36-checks/reviews/<label>/`, outside the repository, with `PYTHONDONTWRITEBYTECODE=1`, copy any repository script before importing it; `git status --porcelain` unchanged after each review; the tree is not touched while a reviewer runs. |
| 14 | Rule 3 above: the type dump at the records commit and at G, by the lane pair, after its controls (Setup 5). |
| 17 | Each reviewer writes its report to a file and returns only its sha256; you hash the file with `hl.sh` and compare before you open it. |
| 20 | Scratch files and modules are elaborated by `el.sh` (it carries the four flags); linter results count only from `lake build`. The witness gate runs as the repository has it (rule 13). |
| 23 | `ev.sh` and `hl.sh`, tested in Setup 2. Every write, hash and edit of an evidence or records file runs through them, or is listed in the plan and round 74's fragment before the commit that carries it (records files written with Write or Edit are hashed with `hl.sh` before their commit); a commit runs only when its gates exited 0 in the same run. |
| 26 | Every review brief is built by a script from `HANDOFF.md`, saved with its sha256 before it is sent, and quotes verbatim rules 14, 17, 18, 19, 20, 22, 23, 26 and 31, cut only with `[...]`; briefs (a) to (f) also quote HANDOFF section 4's "Satisfiability witnesses" paragraph and its witness-gate entry verbatim. Use the brief builder VACUITY-4 used (Setup 1), tested in Setup 2. |
| 27 | Theorem-constant counts, total and per module, from `mkcensus.sh` with the census tails on scratch copies of each final module, before any gate; the module count from `env.header.moduleNames` of a scratch file importing `ClassicalLean`, run through `rootrun.sh`, at the records commit and at G (predicted 5729 at both: no module is added, and the one import line brings a Mathlib file already in the root's closure, measured above), and the build's job count (predicted 4193 at both). |
| 31 | Job 1's statement review is in before any landing; every new declaration, private helpers included, gets its module's cold review before its commit; a review fix that touches a proof line gets its delta check (re-elaborated with `el.sh` and the module rebuilt through `ev.sh`) before its commit. |
| 36 | Briefs and predictions carry a date beside every clock time; each brief gives the dated end of its own run; `briefcheck.py` passes every brief before it is sent. Witness time limits in epoch seconds. |
| 37 | `el.sh` refuses a run while a name is not probed: one probe file per draft and one per module for the witness blocks, `#check @Name` lines for every Mathlib and library name in the text as it will land, run with `EL_PROBE=1`, each probe file importing the module the text will land in (a name outside that module's closure is "Unknown" there: claude-ai's probe 1, importing EulerMethod alone, reported eight names unknown, four of them names other modules know, store row 20261026-053). |
| 38 | `rootrun.sh` for the type dumps, the bridge search, the report tool and any census that imports `ClassicalLean`; tested before first use (Setup 2). The gates are not wrapped. |
| 39 | Stage by path. A commit message is written after its gates ran, says only what `evidence.log` shows, names in its first paragraph any linter or option switched off or on, and ends with the line `evcite.py` prints, generated last, followed only by the session's attribution trailers. Job 5e runs `citecheck.py`. |

## Before approval (read-only in the repository)

1. `git fetch origin` in the worktree. Then, each predicted and checked: `origin/master` and
   `git ls-remote github master` both `354d8358f247740acadc5b9b0fa25722fab4f584`; `git status --porcelain`
   empty. If not, stop (rule 10).
2. Check the hashes and read the read list.
3. Check `crontab -l`, `systemctl --user list-timers` and `free -g`.
4. Write your plan with `ds_file` (project `lean`, job `LEAN-36`, kind `plan`): the jobs in order,
   every prediction you can make now, the order of the items (a suggestion, by the drafts' lengths:
   129 (100 lines), 128 (119), 132 (123), 127 (124), 133 (134), and 146 (183) last, its witness resting
   on EulerMethod's import line), 132's choice for its `variable {m : ℕ}`, and the plan-fit check: for
   each item its plan row beside the draft's statement, every difference named (at least: 127's
   `hab : a ≤ b` and `hfc`, `hg` and `hgs` restricted to `[a, b]`; 128's integers `a ≤ b`, the open
   interval for the derivatives and `hint`; 129's `hx` for every `t` and `t` arbitrary rather than `t ≥ 0`, and the row's "the one solution": the
   theorem gives the form of every solution, not that the formula is a solution (round 1's optional
   existence half, not taken);
   132's `hrow` with `ρ`, `hρ1 : ρ ≤ 1` for the row's strict dominance, and the norm; 133's `l`, `b`,
   `ε`, `δ`, `ρ` as functions on `ℕ`, `hl`, the bounds `≤ u`, `h : n * u < 1`, and the conclusion for
   `j ≤ i < n` only; 146's `hG`, `hK`, `hM`, `hL`, `hL0`, `hh` and the constant `(K + 3 L M)/(12 L)`;
   and for 132 how it is GENERALIZED). Then stop and wait for Dustin's approval.

## Setup (after approval)

1. **The helpers.** Make `~/lean/lean36-checks/scripts/` and `~/lean/lean36-checks/census/`. One
   script copies VACUITY-4's 28 helpers and two census tails (the list above, with their sha256s from
   `g12-helpers.out`) after comparing all 64 characters of each source hash, and changes only the path
   lines listed above (each `vacuity4-checks` to `lean36-checks`), `probecheck.py`'s one `BASE = ` line
   to `BASE = '354d835'`, and `commit.sh`'s line 16, its two trailers (naming VACUITY-4's
   `session_01CaiSGfxRa9So88se5LzGkG`), to this session's own attribution lines, with full paths, each
   refused unless the file has exactly that many such lines. `records2.py`, `docs-insert.py`, `mk116.py`,
   `mkw78.py`, `swap78.py`, `mkland.py`, `mkdiscover.py`, `mkprobe1.py` and `filltask.py` are earlier
   orders' one-off job scripts: read them as patterns, never run them unchanged. VACUITY-4's
   `allowlist.txt` is copied into `~/lean/lean36-checks/` byte for byte; you may add to it a tactic name
   `el.sh` refuses (a token that is not a constant), with a reason; `el.sh` logs the list's new hash. Copy
   the lane's two type-dump files into `~/lean/lean36-checks/inputs/` (`g8-typediff.py` as
   `g8_typediff.py`) and check their sha256. Log every new sha256 with `hl.sh`. Then write
   `pred-setup.md` and hash it.
2. **Tests before first use,** each logged and predicted, as LEAN-35's Setup 2: the empty-prediction
   refusal, exit 97; `ROOTRUN_BUILD=false rootrun.sh` refused, exit 95, the command not run; the
   real-build `rootrun.sh` test, its build line before its command line at the same head; the citecheck
   planted pair on a scratch copy of the log, plus a third case with a `commit-…` helper line between
   the `evcite.py` run and the `COMMIT` line, predicted `OK`; `el.sh` refusing a scratch file that uses
   an unprobed name (logged `NOT RUN`), then running it after its probe, and no new allowlist line on
   either run; `briefcheck.py` refusing a planted brief line with a time and no date; the brief builder
   printing a brief that quotes the nine rules of rule 26 verbatim and passes `briefcheck.py`. A test that
   does not behave as predicted is a stop.
3. **Branch.** First, through `ev.sh --nolean setup1 …`: `git fetch origin`; `origin/master` and
   `git ls-remote github master` both `354d835…`; `git status --porcelain` empty (rule 10). Then
   `git switch -c lean-36 354d8358f247740acadc5b9b0fa25722fab4f584`.
4. **Records first,** one commit, no `.lean` file (rule 6):
   `records/orders/<UTC>__claude-ai__order-lean36-fejer-euler-maclaurin-duhamel-gauss-seidel-forward-substitution-heun.md`,
   the INDEX and CLAIMS rows, VACUITY-4's push, and round 74's fragment
   `records/rounds/<UTC>__round-74-fejer-euler-maclaurin-duhamel-gauss-seidel-forward-substitution-heun.md`.
   check_records then: PASS 140.
5. **Before runs at the records commit,** predicted from the facts: build rc 0, 4193 jobs, 0 warnings;
   AxiomGate PASS 3602; rule 27's module count (a scratch file importing `ClassicalLean`, printing
   `env.header.moduleNames.size`, through `rootrun.sh` while HEAD is the records commit): 5729; the type
   dump, `rootrun.sh td-before "<pred>" lake env lean ~/lean/lean36-checks/inputs/TypeDumpPI.lean`, whose
   `td-before.out` ends with `/usr/bin/time -v`'s report: keep its lines that start with `{` in
   `td-before.jsonl` by a script run through `ev.sh --nolean`, and check that every dropped line is
   time's report; then `g8_typediff.py check td-before.jsonl`: rc 0, 4088 records (3602 thm, 486 def),
   elided 0, missing_fields 0. Then the diff tool's controls on copies of `td-before.jsonl`, each
   predicted and read by its `DIFF` line: the file against itself, all zeros, rc 0; one record's `ppPI`
   edited, `changed=1`, rc 1; only its `pp` edited, `proof_only=1`, rc 0; one record deleted,
   `removed=1`, rc 0 (the exit code does not catch it; the `DIFF` line does).

## The work

### Job 1: statements and their review

1. Probes (rule 37): one file per draft and one per module for the witness blocks, each importing its
   home module (EulerMethod's with its new import line); each new witness's names are probed before it
   is written.
2. For each draft, a scratch statement file outside the repository that imports its home module (and
   the Trigonometric.Bounds line for 146), repeats the module's top-level `open` lines, and holds
   `namespace <home namespace>`, the draft's declarations as they will land with every theorem's and
   lemma's proof `sorry` (defs keep their bodies), and `end`; the statement file for 129 puts a copy of
   LinearODE's line 70 just before its first declaration, since a module's `variable` lines do not reach
   a file that imports it. Elaborate each with `el.sh`, predicted rc 0 with `sorry` warnings and any
   other warning you expect listed in job 1's prediction file, hashed before the run; an unlisted
   warning is a miss, checked again when the proof is in. Hash the statement files.
3. A mechanical check that the move changed no meaning: for each main theorem and the one-sweep lemma (mapping
   `norm_gaussSeidelStep_sub_le'` to `norm_gaussSeidelStep_sub_le`), its type printed with
   `set_option pp.fullNames true in #check @name` from the draft (a scratch copy with the line appended)
   and from the statement file, compared by a script (`typecmp.py` may be adapted): only the namespace
   prefixes of the theorem and of the constants moved with it may differ (133's `subComputed` and
   `forwardSubstComputed`, 132's three defs, 146's `heunIterate`): the script maps those names first,
   then compares. Log the result.
4. One statement review of the six items' seven main theorems and the public one-sweep lemma, by one
   fresh subagent (each statement
   against its plan row and its draft, the Goal list's changes, the namespaces, the import line). Its
   verdict is in before job 2.

### Job 2: land, one commit per module

In the plan's order, per module: the declarations in place (the Goal list), the import line if any,
the witnesses; `el.sh` on the module (rc 0); `lake build` of the module (its only importer is the root
file) through `ev.sh` (0 errors, 0 warnings); `python3 -I tools/banned_vocab_scan.py ClassicalLean`;
the vacuity gate and the check scripts (a copy of the vacuity gate whose only change is its import line
may run on one module while the root is not rebuilt; the real gate runs in job 5a); the witness gate
on the module (rule 13); the module's cold review (rule 8) with any fix and its confirming pass; one
commit staged by path, then its `COMMIT` line.

### Job 3: predictions

Once every module's text is final (after the reviews) and before job 5: a prediction file, hashed, with
the module count and job count (rule 27's measurements); the theorem constants by census (base 3602
plus the census of each final module's new constants, per module: `mkcensus.sh` on a copy of each
changed module at `354d835` and on its final copy, the new constants being the difference of the two
`.names` lists); the type dump's `added=` list, the difference of the two census-all lists for the
changed modules (the dump keeps only `thm` and `def` constants, so a name of another kind in that
difference is listed as an expected absence, and private names are compared by their user-facing
names, `privateToUserName`, because the census runs on copy files whose module name differs) (rule 3);
check_sorry and check_records PASS 140; the vacuity gate's verdicts and reviewed-helper count, and its
tests (89 tests, 47 flagged, 0 rule-5 run-outs, 0 mismatches); `banned_vocab_scan.py ClassicalLean`
PASS, 140 files and the root file, 0 hits; gate 7 ALL PASSED, 4193 jobs, 140 modules 0 failed, 3602
plus the census count, the three standard axioms, the planted fault named; the witness gate on the
whole library PASS with OK 179 (171 plus this order's eight), copy-error 0, LISTED 1, TYPED 205, and
its tests 119 cases, 0 mismatches; the drift check PASS; the bridge search's numbers by hand
from `records/bridges/LEAN-35/`, and the report tool's from VACUITY-4's
`~/lean/vacuity4-checks/j6-report.out`
(`d788fb9f69ddea6bf0dcb576f9403108e3270250368024b492c231aff0923fc6`, `SUMMARY written theorems 1990`,
the run at this library tree; say they are hand predictions); check_records's count of files searched,
112 after this order (110 plus its order file and round 74's fragment). Until then do not
run the axiom gate on the changed modules. A miss is reported, never fixed by changing what was
measured.

### Job 4: documents

- `HANDOFF.md` section 1: after VACUITY-4's paragraph, a dated LEAN-36 paragraph (round 74): the six
  items by name, module and item number, one line each, 132's GENERALIZED verdict said; the counts
  predicted by job 3, to be re-measured by job 5a. No other section of HANDOFF.md changes (section 6's
  drift check).
- `ROADMAP.md`: after section 1.29, a section 1.30 for items 127, 128, 129, 132, 133 and 146, landed
  from below the plan's cut by order LEAN-36, in section 1.29's form.
- One fresh cold reviewer reads the documents commit's diff alone (about 15 calls); a review with
  findings ends with a confirming pass on the fix only (rule 8).

### Job 5: the end checks, in this order

- **5a. The gates,** on the clean tree at G, each through `ev.sh` with its prediction, in MERGE-2's forms
  (its job 4a): build, AxiomGate, VacuityGate, the vacuity tests, check_sorry, check_records, the drift
  check, `banned_vocab_scan.py ClassicalLean`, gate 7, and the witness gate on the whole library
  (`python3 -I tools/witness_gate.py`, about 27 minutes) and its tests
  (`python3 -I tools/witness_gate_tests.py`). Then rule 27's module count at G through `rootrun.sh`,
  predicted equal to Setup 5's. Then the type dump at G through `rootrun.sh` as in Setup 5, its `{` lines
  kept in `td-after.jsonl` and the dropped lines checked, `g8_typediff.py check td-after.jsonl`, then
  `g8_typediff.py diff td-before.jsonl td-after.jsonl` (rule 3). A gate that fails is a stop: 5b and 5c
  do not run, but 5f's report is still written.
- **5b. The bridge search,** through `rootrun.sh`, at G:
  `python3 -I tools/bridge_search.py --diff records/bridges/LEAN-35/ --out ~/lean/lean36-checks/bridges/LEAN-36`;
  rc 1 means candidates to review. Report NEW and GONE pairs and shapes. Check each NEW
  import-unrelated pair and each NEW shape for a theorem whose proof needs both sides; a real one is
  appended to the bridges file from row 166, through `ds_write_staging` in append mode with
  `expect_sha256` its value above (if the write is refused, stop and report), in the file's columns. Say
  in the file and the report exactly how the pairs were checked: which were read statement by
  statement, and how the rest were judged (plan 2's ruling 5). EulerMethod's new Mathlib import adds no
  library import edge. Write the new baseline to `records/bridges/LEAN-36/`; its commit touches only
  `records/`.
- **5c. The report tool,** through `rootrun.sh`, at G, once; a report, not a gate; predicted by hand from
  VACUITY-4's `j6-report.out`. List every `CLOSES` line that names a theorem of this order.
- **5d. Close the records:** round 74's follow-up edit with the commit hashes and the measured counts,
  its quotes checked by script (rule 22); the CLAIMS row closed and the INDEX row's state set; one
  records-only commit. Then check_records again at the final HEAD, predicted PASS 140.
- **5e. citecheck:** every commit of this order, `git rev-list 354d835..HEAD`, by
  `citecheck.py ~/lean/lean36-checks/evidence.log --message <its message file> <hash>` in one loop (the
  message from `git log -1 --format=%B <hash>`; each `OK`), and the repository run `citecheck.py
  ~/lean/lean36-checks/evidence.log ~/lean/classical-lean-paper-crypto 354d835` (predicted rc 0, every
  commit `OK`).
- **5f. Report** with `ds_file` (kind `report`), laid out like LEAN-35's report: in short; setup and the
  helper tests; for each item its final statement, witnesses and review verdicts; the type-dump diff;
  predicted beside measured for every gate and count, each cited from its output (rule 12); the bridge
  diff and how it was checked; 5c's `CLOSES` lines for this order (or "none"); the commits; 5e's output;
  each heads-up Dustin passed in and your answer to it (rule 11); the findings outside the Goal, each
  with its evidence, for a later order (rule 11); misses and anything not closed; and the push command
  as one line, not run:
  `cd ~/lean/classical-lean-paper-crypto && git push origin lean-36:master && git push github lean-36:master`.
  Say that the GitHub push starts a CI run on `master`, and that Dustin runs it only after claude-ai has
  checked the push-review file.
- **5g. Push-review file** with `ds_file` (subdir `data`, name `LEAN-36-push-review.txt`), by one
  script, each command followed by its full output: `git rev-parse HEAD`, `git status --porcelain`,
  `git ls-remote origin master`, `git ls-remote github master` (both must still be `354d835`, rule 10),
  `git merge-base --is-ancestor 354d835 HEAD` with its exit code, `git rev-list --count 354d835..HEAD`,
  `git log --name-status --format='== %h %cI %s' 354d835..HEAD` (files under `records/bridges/` as a
  count), `git diff --stat 354d835 HEAD`, `git diff --name-only 354d835 <G> -- ClassicalLean.lean tools
  .github ':(glob)lakefile*' lake-manifest.json lean-toolchain records/rules.toml` (predicted: only
  `tools/vacuity_reviewed.txt`, if a helper was listed), `git diff --name-only 354d835 <G> --
  ClassicalLean` (predicted: exactly the six modules), `git diff -U0 354d835 <G> -- ClassicalLean | grep
  '^[-+]import'` (predicted: exactly EulerMethod's one line, `+`), `git diff -U0 354d835 <G> --
  ClassicalLean` piped to a script that lists every removed line (predicted: none outside the six
  module docstrings), the type-dump `DIFF` line, the whole-library `WITNESSGATE` line at G with its
  time, ruling 6's two greps at HEAD (`grep -rnwE
  'reduceBool|reduceNat|ofReduceBool|ofReduceNat|trustCompiler|native|plausible|slim_check|evalExpr|evalConst'
  ClassicalLean/` and `grep -rn '(config *:=' ClassicalLean/`, each predicted to find nothing), `git
  diff --name-only <G> HEAD` (only `records/`), 5d's output and 5e's two outputs. Report its sha256. Then
  stop: claude-ai reviews it before Dustin pushes.

## Done means

- Branch `lean-36` from `354d835`, clean tree, nothing pushed; its first commit is the records commit
  and holds no `.lean` file; then one commit per module; then documents; then records-only commits.
- The launch variable printed `1`; the helpers copied, their sha256s logged, their tests run before
  first use as predicted.
- The six items proved with no `sorry` and no new axiom, as drafted with the Goal list's changes, or
  each narrowing said plainly, or reported not closed and undone by rule 9; 132 GENERALIZED and said so.
- Eight witnesses in rule 2's form, each checked by its review against rule 5 (what must move
  included), each OK in the witness gate before its commit (rule 13), and all OK in the whole-library
  run at G; or an item undone by rule 9 and said so.
- The type-dump diff `removed=0 changed=0`, and `proof_only=0` or each PROOF-ONLY record listed and
  explained (rule 3); its `added=` list equal to the census's new constants, apart from differences
  listed and explained under rule 3 and job 3.
- Job 1's statement review, the six module reviews and the documents review saved and hash-checked,
  each ending in a confirming pass where it had findings.
- Every gate as predicted at G, or each miss reported; gate 7 ALL PASSED and the witness gate PASS at
  G; after G only `records/` changed; check_records PASS at the final HEAD.
- The bridge diff reported with how it was checked; real bridges (if any) from row 166; the new
  baseline committed.
- Job 4's documents changed and named (only section 1 of HANDOFF.md; the drift check passes).
- 5e: every commit `OK`.
- The plan and the report in `lean/LEAN-36/`, the push-review file in `lean/LEAN-36/data/`, hashes
  matching yours.

Then report in a few plain sentences: what was proved, 132's GENERALIZED verdict, the witnesses and
what moves in each, the gate results beside the predictions, any new bridge, the two files' hashes
and the push command. Dustin reads your replies carefully and is still learning to read code: plain
words, and define a technical term the first time you use it. When you need a decision from him, ask
in one line with your recommended answer first.

## Not in this order

- VACUITY-3's "rows 31, 32" (`d3003-r1-s1`): YuleWalker's `covariance_eq_sum` and
  `isSolution_autocovariance`, witnessed from d3003's AR(2) model in their own order, VACUITY-5, after
  this one (store rows 20261026-049, -050; the targets file's items 31 and 32 were witnessed on
  2026-10-14).
- 129's existence half (round 1's optional strengthening, API-CREDIT-1 line 59): that
  `exp (t A) x₀ + ∫₀ᵗ exp ((t − s) A) f(s) ds` solves the equation.
- 133's "`ΔL i j = 0` above the diagonal" (review r6's minor): a stronger statement, for a later order.
- GATE-2 (VACUITY-4 ruling 6 section 4): the witness gate's fail-closed inner check and its speed.
- Bridges 160 to 162 and the pair-by-pair reads of MERGE-2's and MERGE-3's searches (LEAN-38, plan 2
  ruling 5); the twin search (TWINS-1, ruling 6).
- Deleting GitHub branches; any push.

## Revisions

- r0, the draft (claude-ai, 2026-10-26, after VACUITY-4's push; every fact measured at `354d835`).
- r1 (claude-ai, 2026-10-26), cold review 1's F1 to F20 applied: 146's false claim about a constant
  `G` corrected in the witness file and here, and `witcheck.py` checks 129's curve and 146's first step
  (F1); probe 2's typed time corrected, its runs named (F2); the witness probe run again (`p2out-r2/`)
  with LinearODE as it lands, without an import line (F3); an older block's non-OK line a stop (F4);
  129's existence half named in the plan-fit check and Not in this order (F5); 133's witness `l`
  lower-triangular (F6); warnings counted on `warning:` lines, the def body's `h` (F7);
  `abs_mul_prod_sub_le` among 133's twins (F8); the helper counts (F9); job 1's type comparison maps
  moved constants (F10); three more hashes to check (F11); rule 37's row (F12); Done means for an undone
  item (F13); the hand predictions' sources (F14); check_records's counts (F15); probe 1's eight names
  and import (F16); the witness gate's argument form (F17); an eighth witness, for the public one-sweep
  lemma (F18); which gate results are at G, G' and `354d835` (F19); EulerMethod's import line measured
  alone against the type dump, probe 4 (F20).
- r2 (claude-ai, 2026-10-26), cold review 2's G1 to G9 applied: the prediction files' helios times
  from `stat` and the misses of claude-ai's predictions listed (G1, G8); each of 146's three steps
  shown to move by `witcheck.py`, 132's and 146's docstrings say every step moves, rule 5 asks it, and
  the witness probe run again (`p2out-r3/`) (G2); the files changed after G and G' from `git diff`
  (G3); how the probe runs' inputs and outputs were kept (G4); the modules' private names checked (G5);
  the one-sweep lemma in rules 1 and 4 (G6); the measurement window and probe 5's times (G7); notes.md
  older than the order, and rule 13's one-module form unmeasured (G9).
- r3 (claude-ai, 2026-10-26), cold review 3's H1 to H6 applied: the prediction files' sha256s tied to
  their copies, and which logs hash them first (H1); the probe modules reproduced from the witness
  files (H2); notes.md's differences as examples (H3); the window's end from a saved output (H4); the
  private-name grep with attributes (H5); job 1's type check covers the one-sweep lemma (H6).
