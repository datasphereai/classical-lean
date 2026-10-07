# Round 21 — the credit line, and the information-geometry connections

Session: Claude Code `session_014ohH81ESXFBMFPQyLxkgnq` on helios, executing order `G-6`
(`records/orders/20260923T233012Z__claude-ai__order-g6-connections-zsigmondy.md`), job J2.
Lean and Mathlib v4.34.0 throughout.

Commits: J1's records `42cceb4`; J2 step 1 `f0c14ca`, this fragment's first commit (its hash
added in the step-3 edit, records/README.md Rule 1); step 3 `c434743`; step 4 `3c734c3`; steps
5–7 in one records commit, its hash added in a follow-up edit. The order has step 3 create this fragment; it starts
at step 1 instead, so that the commit which changes every module carries its own round entry
(Rule 4). Until step 3 it names no new module file, so gate 6's FAIL checks at steps 3 and 4
are unaffected (order §1).

Evidence, outside the repository: `~/work/_bump-evidence/g6/evidence.log` (every line a command,
its prediction where one was made, and its rc), the before evidence
`~/work/_bump-evidence/g6-before/` (taken at `42cceb4` on a clean tree; byte-identical to order
G-5's final `g5/j3/final/` list and type dump, `cmp` rc 0 for both), per-step logs and dumps
under `~/work/_bump-evidence/g6/`.

## Step 1 — the credit line

Changed, line 4 of the licence header only (`Authors: Dustin [surname]` becomes
`Authors: Dustin [surname], Claude (Anthropic)`), at Dustin's wish of 2026-09-23; the copyright
line still names him alone:

* `ClassicalLean/Algebra/CompanionMatrix.lean`
* `ClassicalLean/Combinatorics/AlgebraicGeneratingFunction.lean`
* `ClassicalLean/Combinatorics/RecurrenceGeneratingFunction.lean`
* `ClassicalLean/Geometry/Helix.lean`
* `ClassicalLean/Geometry/Hopf.lean`
* `ClassicalLean/Geometry/S3Quaternion.lean`
* `ClassicalLean/Geometry/SU2SO3.lean`
* `ClassicalLean/Geometry/Spectral3x3.lean`
* `ClassicalLean/GoldenRatio/Characterisations.lean`
* `ClassicalLean/InformationTheory/Channel.lean`
* `ClassicalLean/InformationTheory/Entropy.lean`
* `ClassicalLean/InformationTheory/MutualInformation.lean`
* `ClassicalLean/Logic/PredicateStack.lean`
* `ClassicalLean/NumberTheory/Catalan.lean`
* `ClassicalLean/NumberTheory/CompositumDiscriminant.lean`
* `ClassicalLean/NumberTheory/FactorialPart.lean`
* `ClassicalLean/NumberTheory/Jacobsthal.lean`
* `ClassicalLean/NumberTheory/Lucas.lean`
* `ClassicalLean/NumberTheory/LucasApparition.lean`
* `ClassicalLean/NumberTheory/LucasCompanion.lean`
* `ClassicalLean/NumberTheory/LucasSequence.lean`
* `ClassicalLean/NumberTheory/LucasSequenceCases.lean`
* `ClassicalLean/NumberTheory/LucasSequenceGeneratingFunction.lean`
* `ClassicalLean/NumberTheory/Mersenne.lean`
* `ClassicalLean/NumberTheory/MersenneFactorialPart.lean`
* `ClassicalLean/NumberTheory/MersenneOrder.lean`
* `ClassicalLean/NumberTheory/NacciTrace.lean`
* `ClassicalLean/NumberTheory/Pell.lean`
* `ClassicalLean/NumberTheory/PowerSumCases.lean`
* `ClassicalLean/NumberTheory/PrimitiveDivisor.lean`
* `ClassicalLean/NumberTheory/Tribonacci.lean`
* `ClassicalLean/Order/Superadditive.lean`
* `ClassicalLean/Order/Tolerance.lean`
* `ClassicalLean/Simplex/Basic.lean`
* `ClassicalLean/Simplex/CrossEntropy.lean`
* `ClassicalLean/Simplex/DesignConstants.lean`
* `ClassicalLean/Simplex/FisherRao.lean`
* `ClassicalLean/Simplex/Gibbs.lean`
* `ClassicalLean/Simplex/Hessian.lean`
* `ClassicalLean/Simplex/Involution.lean`
* `ClassicalLean/Simplex/LogSumExp.lean`
* `ClassicalLean/Simplex/Ordered.lean`
* `ClassicalLean/Simplex/Symmetry.lean`
* `ClassicalLean/Simplex/Temperature.lean`
* `ClassicalLean/Statistics/GaussMarkov.lean`
* `ClassicalLean.lean` — line 4 as above, and one paragraph at the end of its module docstring:
  "The Authors line credits Claude (Anthropic) alongside the copyright holder; how the library was
  written and ported is recorded in `PROVENANCE.md` and `records/`." Written as its own paragraph
  in two lines, because on one line it is 161 characters and the long-line linter (100) would
  warn. `grep -c [surname] ClassicalLean.lean` is 2, lines 2 and 4, as before.

Also changed: `tools/banned_vocab_scan.py` (the `[surname]` exception's second alternative becomes
`Authors: Dustin [surname], Claude \(Anthropic\)`, keeping `(?-i:…)` and `[0-9]`, with the order's
comment line above it; +2 −1 lines); `RETIRED.md` (one dated paragraph in its note on names);
`HANDOFF.md` §4, §5 and §6 (one dated line each).

The replacement was a script (`g6/replace_authors.py`) that asserts 46 exact matches of line 4
before writing and reads 46 new lines back after; `git diff --numstat` then showed 46 rows of
`1 1` and nothing else.

### The exception, fail-tested (order §1 rule 8: under the scanner's own compile flags)

The order of operations matters: the Catalan tests isolate one file only once the other 44
modules carry the new line, so the 46 lines changed first, the scanner second.

| Run | Scanner | Tree | Predicted | Measured |
|---|---|---|---|---|
| fire | old exception | new Authors line in all 46 files | FAIL, 45 hits, all at line 4 | rc 1, 45 hits, 45 at `.lean:4` |
| full | new exception | the same | PASS, 0 hits | rc 0, 0 hits, 45 files |
| 1 | new | `NumberTheory/Catalan.lean` as landed | PASS | rc 0, 0 hits |
| 2 | new | Catalan line 4 := the old Authors line | FAIL, 1 hit at :4 | rc 1, 1 hit at `Catalan.lean:4` |
| 3 | new | Catalan line 4 := the new line in lower case | FAIL, 1 hit at :4 | rc 1, 1 hit at `Catalan.lean:4` |
| 4 | new | Catalan line 4 := the new line followed by `, X` | FAIL, 1 hit at :4 | rc 1, 1 hit at `Catalan.lean:4` |
| 5 | new | a scratch last line `-- the <eponym> theorem` | FAIL, 1 hit there | rc 1, 1 hit at `Catalan.lean:118` |

Catalan was saved outside the repository first and restored after every run, `cmp` rc 0 each
time (`g6/catalan_tests.sh`, output `g6/catalan-tests.out`).

### Gates, and the type dump

On the step-1 tree before commit (the uncommitted changes were exactly this commit's paths; this
fragment was written after the gates and does not change a `.lean` file): `lake build` rc 0,
0 warnings, 46 modules rebuilt, from the repository root with the header linter on — so Mathlib's
Authors-line checks accept the new line; AxiomGate PASS, 1098; VacuityGate PASS; check_sorry PASS;
banned_vocab_scan PASS, 0 hits; check_records PASS, 45 modules, 11 files.

Type dump against J1's before evidence: `DIFF removed=0 added=0 changed=0`, read from the summary
line, not the exit code (`g5_typediff.py` exits 0 whenever nothing CHANGED, even if records were
removed or added; its line 82). The raw list, the filtered list and the type dump are each
byte-identical to the before evidence (`cmp` rc 0): 1098 raw, 746 filtered, 138 private. No
theorem constant was added, removed or changed, so step 1's per-module counts are J1's.

## Step 2 — searches and junk cells, before steps 3 and 4

**Mathlib v4.34.0 searches**, run from `.lake/packages/mathlib` with `/usr/bin/grep -rniE
'<pattern>' Mathlib --include=*.lean | wc -l` (the tool shell's `grep` is a wrapper; full list in
`g6/j2/mathlib-searches.txt`): `softmax` 0; `cram[eé]r.?rao` 0; `fisher.?info|fisherInformation`
0; `fisher.?rao|fisherRao|bhattacharyya` 1 (`MeasureTheory/Measure/Tight.lean:4`, an author's
name); `vecMulVec` 141; `PosSemidef.*diagonal` 10; `hasDerivAt.*exp.*div` 2 (both unrelated);
`PosSemidef.*⁻¹` 3 (`PosSemidef.inv` and the two Schur-complement criteria); `sigmoid` 120;
`covMatrix|covarianceMatrix|covariance_matrix` 23 (Brownian motion); `information.?inequality` 0;
`majoriz` 68 (Mathlib's two TODOs, `Analysis/Convex/Birkhoff.lean:29` and
`Analysis/InnerProductSpace/Spectrum.lean:47`, plus an unrelated asymptotics predicate).
The shape search added to the order's list, `sigmoid`, matters: Mathlib has the two-class softmax
as `Real.sigmoid` with `hasDerivAt_sigmoid` (`Analysis/SpecialFunctions/Sigmoid.lean:63`,
`:138`), so "Mathlib has no softmax" is true by name only.

**Junk cells**, with exact rational arithmetic, random trials plus constructed cases. The research
scripts were copied into `~/work/_bump-evidence/g6/j2/junk/` and re-run by this session (every
output reproduced the research agents' reports): the two chart identities, 11733 and 19555 cases,
0 failures, zero cells included; the chart inverse, 3911 cases, 0 failures where `lam`, `kap` and
`eta` are nonzero (any sign), failing at every zero cell; the tangent inverse, 4000 cases, failing
at a zero coordinate (`p = [0, 1/2, 1/2]`, `u = [1, -1, 0]`) and when `∑ u ≠ 0`; semidefiniteness,
0 negative forms under `0 ≤ p` and `∑ p ≤ 1`, with counterexamples when either is dropped; the
softmax Jacobian and the Hessian of `logSumExp`, symbolic at three coordinates. For step 4: 3000
trials, `h` satisfiable in 1942, and a singular `E[S Sᵀ]` in none of them — the order's question
"can the hypotheses of step 4 hold with a singular `E[S Sᵀ]`?" is answered no, and
`isUnit_det_secondMoment` proves it; a negative weight breaks the inequality (`p = ![1, -1]`); a
zero weight breaks the equality case (`p = ![0, 1/4, 9/4]`).

## Step 3 — `ClassicalLean/Simplex/SecondOrder.lean`

New module `ClassicalLean/Simplex/SecondOrder.lean`, sha256 `c4797c7a…39c7` as landed, one import
line in `ClassicalLean.lean` (between `Simplex.Ordered` and `Simplex.Symmetry`). Imports
`ClassicalLean.Simplex.FisherRao` and `Mathlib.Algebra.Order.Star.Real` (for `StarOrderedRing ℝ`,
which the library already reached through `Statistics/GaussMarkov`, so the library's import
closure gains only this module: 3969 → 3970 modules, Mathlib 3474 → 3474; the cache gap
`Mathlib.Probability.Kernel.Invariance` is still not reached; positive control
`ClassicalLean.Simplex.SecondOrder` reached, rc 0).

Declarations: `fisherRaoChart`, `fisherRao_eq_fisherRaoChart`, `hessian_eq_smul_fisherRaoChart_add`,
`fisherRaoChart_posDef`, an `example` proving `hessian_posDef` as barrier plus `T` times a
positive definite metric (it does not cite `hessian_posDef`), `hasDerivAt_softmax`,
`categoricalCov`, `categoricalCov_apply`, `categoricalCov_fin_two`,
`hasDerivAt_softmax_categoricalCov`, `categoricalCov_posSemidef`, `categoricalCov_mulVec_one`,
`categoricalCov_mulVec_div`, `fisherRao_categoricalCov_mulVec`, `fisherRaoChart_mul_categoricalCov`,
and four `example`s (the order's closed- and open-simplex forms, the softmax instance, and the
literal chart matrix with positive coordinates). No private declaration.

**Consumers** (order Done-means 4): the module uses `hessian` (`Simplex/Hessian`), `fisherRao`
(`Simplex/FisherRao`) and `softmax` (`Simplex/LogSumExp`), none of which cited the others before.

**Where the statements differ from the order's text** (each approved in the plan, each implying the
order's version, which an `example` recovers): semidefiniteness under `0 ≤ p` and `∑ p ≤ 1`
(order: `∑ p = 1`); the tangent inverse under `p i ≠ 0` (order: `p ∈ openSimplex`); the chart
inverse under nonzero coordinates (order: positive); `fisherRaoChart_posDef` added, because the
order's `example` needs it; `fisherRao_categoricalCov_mulVec` added on the statement review's
finding that P2 had no statement against `fisherRao` itself.

**Gate 6, shown red first.** With the file and its import line in place and no record naming it:
`check_records.py` rc 1, `check_records FAIL — 46 module(s) under ClassicalLean, 1 with no records
entry`, the one line `UNRECORDED  ClassicalLean/Simplex/SecondOrder.lean`. This fragment then
names it.

**Gates on the landed bytes** (before this section was written; the tree differed from the
commit only by this fragment): `lake build` rc 0, 0 warnings, 2 modules built; AxiomGate PASS,
1134 (1098 + 36); VacuityGate PASS; check_sorry PASS, 46 files; banned_vocab_scan PASS, 0 hits.
Type dump against J1's before evidence: `DIFF removed=0 added=38 changed=0` (36 theorem constants
and the two definitions); filtered list +13 −0 (the twelve theorems and
`categoricalCov.congr_simp`). Per-module count (`ModuleThmCount.lean`): `ClassicalLean.Simplex.
SecondOrder` 36, total 1134, equal to AxiomGate. The other 23 raw constants are `.eq_1` equation
lemmas and `_simp_1_N` auxiliaries that `field_simp` generates; AxiomGate checks them all.

**Reviews.** Before proving, a cold reviewer checked the statement list (verdict PASS, five minor
findings: P2 had no statement against `fisherRao`; the `example` must not cite `hessian_posDef`;
two names; docstrings). Rulings: `fisherRao_categoricalCov_mulVec` added with its softmax
instance; `fisherRao_chart` renamed `fisherRao_eq_fisherRaoChart` (one underscore from the
definition) and `hasDerivAt_softmax_eq_categoricalCov` renamed `hasDerivAt_softmax_categoricalCov`;
the `_posDef` suffix kept, by the library's `hessian_posDef`. After proving, a second cold
reviewer read every declaration, verdict PASS:

> All 19 declarations (2 defs, 12 theorems, 5 examples; no private helper) hold under their
> hypotheses: exact rational and sympy checks using Lean's 0⁻¹ = 0 found 0 failures, and every
> counterexample in the module docstring and all 8 Mathlib search counts reproduce exactly. The
> routes are the ones the order names: the hessian_posDef example goes through
> hessian_eq_smul_fisherRaoChart_add and fisherRaoChart_posDef and never cites hessian_posDef;
> the module uses hessian, fisherRao and softmax. The weakened hypotheses of
> categoricalCov_posSemidef are sharp (both necessary), and the chart inverse fails at all 132
> zero cells swept.

Its eight minor findings were docstring wording (applied: "three parts", "bilinear form", the
softmax example's headline now states only what the statement says and marks the Hessian of
`logSumExp` as a reading, a process reference removed, the covariance search counts added) and
one naming point, `categoricalCov_mulVec_one` stated with `(fun _ => 1)` rather than `1`, kept as
the order writes it. It also noted that the only compile evidence at review time was for a
combined scratch file; the build evidence above is `lake build` on the landed bytes.

## Step 4 — `ClassicalLean/Statistics/CramerRao.lean`

New module `ClassicalLean/Statistics/CramerRao.lean`, sha256 `1787e217…60a9` as landed, one import
line in `ClassicalLean.lean` (before `Statistics.GaussMarkov`). Imports
`ClassicalLean.Simplex.SecondOrder` and `ClassicalLean.Statistics.GaussMarkov`; the library's
import closure gains only this module (3970 → 3971, Mathlib 3474 unchanged; the cache gap still
not reached; positive control `ClassicalLean.Statistics.CramerRao` reached, rc 0).

Declarations: `weightedMean`, `weightedCov`, `secondMoment` (weights not divided by their sum),
the private `of_mul_sqrt_mul_transpose` (for `p ≥ 0`, scaling columns by `√p` turns a matrix
product into `p`-weighted sums), `isUnit_det_secondMoment`, **the information inequality**
`posSemidef_weightedCov_sub_inv_secondMoment`, the equality case
`weightedCov_eq_inv_secondMoment_iff`; the categorical family `categoricalScore`,
`categoricalOneHot`, an `example` that its weights sum to `1`, `weightedMean_categoricalScore`
(`E S = 0`), `secondMoment_categoricalScore` (its Fisher information is `fisherRaoChart`),
`weightedMean_categoricalOneHot` (unbiased), `weightedCov_categoricalOneHot`,
`crossMoment_categoricalOneHot_categoricalScore` (it satisfies the hypothesis),
`weightedCov_categoricalOneHot_eq_inv_secondMoment` (it attains the bound), and an `example`
applying the general theorem to it.

**Consumers** (order Done-means 4): `posSemidef_weightedCov_sub_inv_secondMoment` is
`Statistics/GaussMarkov`'s `posSemidef_self_mul_transpose_sub_inv` at `C = (T - E T) diag √p`,
`X = diag √p Sᵀ` — its first consumer outside its own file; `isUnit_det_secondMoment` uses
`isUnit_det_transpose_mul_self_of_mul_eq_one`; the equality case uses
`self_mul_transpose_eq_inv_iff` and unfolds `leastSquares`, so `leastSquares` also has its first
outside consumer (`HANDOFF.md` §3 said generalised least squares or Cochran would be first; step
6 corrects it). The categorical instance uses `fisherRaoChart` and the chart identity
`fisherRaoChart_mul_categoricalCov`, through `Matrix.inv_eq_right_inv`.

**Where the statements differ from the order's text:** `∑ p = 1` and `E S = 0` are not
hypotheses (the order's own instruction; the docstring gives the probabilistic reading, and the
categorical family proves both); no `[DecidableEq Ω]` (the statements do not use it, and
`linter.unusedDecidableInType` is on); `T - E T` and `diagonal (√p)` written as `Matrix.of` with
`√(p ω)` (the order's notation does not typecheck); the one-hot estimator is the `2 × 3` matrix
`!![1, 0, 0; 0, 1, 0]`; the two categorical identities that hold at `0⁻¹ = 0` carry no
hypothesis, and the others need `lam`, `kap`, `eta` nonzero rather than positive.

**Correction to order G-6 §0 row 7 (the order is filed and not edited).** Its gloss on the
`cram[eé]r.?rao` search, "only Cramer's rule", is incomplete: Mathlib v4.34.0 also has the
Cramér–Wold theorem, `Probability/CramerWold.lean`. The count of `0` for `cram[eé]r.?rao` stands.
The post-proof reviewer caught the gloss copied into the module docstring; the docstring now
names both.

**Gate 6, shown red first.** With the file and its import line in place and no record naming it:
`check_records.py` rc 1, `check_records FAIL — 47 module(s) under ClassicalLean, 1 with no records
entry`, the one line `UNRECORDED  ClassicalLean/Statistics/CramerRao.lean`.

**Gates on the landed bytes:** `lake build` rc 0, 0 warnings, 2 modules built; AxiomGate PASS,
1149 (1134 + 15); VacuityGate PASS; check_sorry PASS, 47 files; banned_vocab_scan PASS, 0 hits.
Type dump against J1's before evidence: `DIFF removed=0 added=58 changed=0` (steps 3 and 4
together; 20 of them this step, 15 theorem constants and five definitions); filtered list +10 for
this step. Per-module count: `ClassicalLean.Statistics.CramerRao` 15 (nine theorems, the private
helper, five `.eq_1` lemmas), total 1149, equal to AxiomGate.

**Reviews.** Before proving, a cold reviewer checked the statements (verdict FLAG: one major
finding, that the categorical instance did not prove `∑ p = 1`, and five minor ones on names,
docstrings, and the final `example`'s route). Rulings: the weights-sum-to-`1` `example` added;
`weightedMean_categoricalOneHot` (unbiasedness proper) added and the cross-moment lemma renamed
from `chartOneHot_unbiased`; `chartScore` / `chartOneHot` renamed `categoricalScore` /
`categoricalOneHot`; docstrings state that the weights are unnormalised and give the
probabilistic reading; the `not_forall_` counterexamples were not added (their witnesses are in
the module docstring). After proving, a second cold reviewer read every declaration including the
private helper, verdict FLAG:

> Every statement is true under its hypotheses, and every hypothesis is needed; this was checked
> with exact arithmetic under Mathlib's junk inverse. Both docstring counterexamples reproduce:
> p=![1,-1] gives E[SSᵀ]=0 and Cov T=-1, and p=![0,1/4,9/4] gives Cov T=4/5=(E[SSᵀ])⁻¹ with
> 11≠4. The routes are the ones the order asks for: the inequality comes from
> posSemidef_self_mul_transpose_sub_inv, the equality case from self_mul_transpose_eq_inv_iff
> with leastSquares unfolded, and attainment from fisherRaoChart and
> fisherRaoChart_mul_categoricalCov. Nothing is circular, and the vocabulary scan passes; the
> scanner was first shown to fail on a planted term. One blocker, in the docstring only:
> '(Mathlib has Cramer's rule only)' is false, because Mathlib v4.34.0 also has the Cramér–Wold
> theorem (Probability/CramerWold.lean).

The blocker was fixed, then the file rebuilt (the gates above are on the fixed bytes). Minor
findings applied: the attainment identity's behaviour at zero cells stated (it fails on the
edges, and holds at the vertices only through the junk inverse); the family's saturation stated
(the instance shows attainment, not strictness); the trial count reworded; the helper's docstring
says `p ≥ 0`; the Schur-complement route (`Matrix.PosDef.fromBlocks₁₁`/`₂₂`) named as the
alternative; an agent's name removed from the source; the attainment theorem renamed
`weightedCov_categoricalOneHot_eq_inv_secondMoment`. Not applied: factoring the repeated `hCX`
blocks into helpers (it would add declarations for no change in content).

## Steps 5 and 6 — the records of the patterns, and the rules

`ROADMAP.md` §1.14 (new): one entry per pattern of order G-6 §0 rows 4–6 and 9, each with its
hypotheses, P1–P3 labelled "proved, round 21" and P4–P7 "measured by claude-ai 2026-09-23, not
proved"; one dated line in §1.5 on P4 (it would join `Geometry/S3Quaternion` to
`Simplex/FisherRao`, not the corner to the number-theory half §1.5 asks for). `HANDOFF.md` §3:
P6 (the law of apparition) and P7 (majorization, with Mathlib's
`Analysis/Convex/Birkhoff.lean:29–30` TODO) added as candidates; the two sentences that expected
generalised least squares or Cochran to give `leastSquares` its first outside consumer are
corrected. `HANDOFF.md` §6: the eight rules of order G-6 §1 become rules 8–15, each with its
source, and the lead-in names both orders (0923: 1–7; G-5: 8–15); rule 14 gains the lesson of this
round (read `g5_typediff.py`'s `DIFF` line, not its exit code). One dated line records the push
J1 found missing: `classical-lean` to `202394a` at 2026-09-13T06:42:22Z, from the `dsmain/master`
reflog, and states that whether it was on Dustin's yes is not recorded.

## J2's Done-means, item by item

1. The six gates on a clean tree: in the follow-up edit below.
2. Step 1: 46 files carry the new Authors line; the five exception tests are in `f0c14ca`'s
   commit message; the type dump against J1's evidence showed nothing removed, added or changed.
3. Steps 3 and 4: every new theorem is within the kernel trio (AxiomGate PASS at 1134 and 1149);
   both reviews, before and after proving, are quoted above for each module; the type dump
   against J1's evidence shows only additions (`removed=0 added=58 changed=0` after step 4).
4. Consumers: `Statistics/CramerRao` uses `posSemidef_self_mul_transpose_sub_inv`; the
   categorical instance uses `fisherRaoChart` and the chart identity
   `fisherRaoChart_mul_categoricalCov`; `Simplex/SecondOrder` uses `hessian`, `fisherRao` and
   `softmax`.
5. This fragment carries the searches (step 2), the junk cells (step 2), the per-module counts
   (SecondOrder 36, CramerRao 15) and the import-closure results (3969 → 3970 → 3971, Mathlib
   3474 unchanged, the cache gap unreached, positive controls reached).

Filtered theorem list over J2: 746 → 769 (+23); raw 1098 → 1149 (+51).

**Added in the follow-up edit (Rule 1): steps 5–7's records commit is `66b6cea`.** J2's
Done-means 1, on a clean tree at `66b6cea` (`git status --porcelain` empty): `lake build` rc 0,
0 warnings, nothing built; AxiomGate PASS, 1149; VacuityGate PASS; check_sorry PASS, 47 files;
banned_vocab_scan PASS, 0 hits across 31 retired and 8 provenance terms; check_records PASS, 47
modules, 12 files; each rc 0. Every gate figure quoted in this fragment was taken on a tree whose
only uncommitted changes were the commit's own paths, and this one on a clean tree.

## Addendum, dated 2026-09-24 UTC (order G-6 Close check) — the statement reviews, quoted

The Close check (round 22) found J2's Done-means 3 **not met as written**: the post-proof reviews
are quoted above, but the two statement reviews before proving were paraphrased, and no reviewer
output had been kept as evidence. All review outputs are now saved, byte for byte as the workflow
returned them, in `~/work/_bump-evidence/g6/reviews/` (`j2-statement-review-w2iy3pc35.json`,
sha256 `adb7eaaa…`; `j2-proof-review-wopc046tp.json`, `45d1137f…`). The statement reviews,
quoted:

> [secondorder] verdict PASS. […] fisherRao_chart: TRUE for every input, junk values included.
> Exact check: 4000 cases with 0 failures, including lam=0, kap=0, eta=0, lam=kap=0 and negative
> values. Symbolic check: it is a polynomial identity when lam⁻¹, kap⁻¹ and eta⁻¹ are replaced by
> independent symbols, so every value Lean's inverse can take is covered. […]
> categoricalCov_posSemidef: TRUE under 0 ≤ p and ∑ p ≤ 1. Exact check: 1500 cases at sizes 1 to 4
> with zeros included; the matrix is symmetric and every principal minor is ≥ 0.

> [cramerrao] verdict FLAG. […] The order has the categorical instance prove both probabilistic
> readings, sum p = 1 and E S = 0. Only E S = 0 is stated (weightedMean_chartScore). Nothing states
> sum_ω ![lam, kap, 1 - lam - kap] ω = 1.

**Timing, stated because the sections above did not.** The statement reviews were dispatched
before any proof was written, but proving ran while they worked: `g6/j2/SecondOrderWork.lean`
compiled sorry-free at 21:00 EDT and the Cramér–Rao proofs at 21:02–21:03, and the reviews
returned at 21:04–21:05 (file times, as the Close check measured them). Their rulings — renames,
added declarations — were applied to the proved text afterwards. Four declarations were added on
those rulings and so were reviewed only after proving: `fisherRao_categoricalCov_mulVec`,
`weightedMean_categoricalOneHot`, and the two `example`s (the softmax instance and the weights
summing to `1`); the private `of_mul_sqrt_mul_transpose` likewise. All of them were in the
post-proof reviews quoted above, before their commits (order §1 rule 6's letter holds; the plan's
"before proving" held for dispatch, not for the verdict).

**Evidence-log gaps** (the Close check's findings): `evidence.log` has no line for the
`ModuleThmCount.lean` runs of steps 3 and 4 (their outputs are `g6/module-thm-count-j2.3.txt` and
`-j2.4.txt`), for the re-runs of the junk-cell scripts (their `.out` files are in `g6/j2/junk/`),
or an rc for the Mathlib searches (`g6/j2/mathlib-searches.txt`); three lines carry no rc. No
line records a placeholder rc. The follow-up commit `beb2cbc` was committed without a gate-6 run
on its own tree; the Close check's re-run on it passes (47 modules, 12 files).
