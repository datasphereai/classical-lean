# Handoff

For a session picking this up cold. Read `ROADMAP.md` for the subject areas to add next and
the patterns connecting the ones already here; this file is about **what to do next in the
small and how to be sure it is true**.

---

## 0. The one rule that matters

**Measure the thing you are claiming, not something near it.**

This project has produced the same failure nine times, and every instance was a *correct*
measurement of the wrong object:

| claim | what was measured | what was claimed |
|---|---|---|
| "49 restored Lean files on [retired name]" | a number copied from an older record | the state of a filesystem |
| "0 warnings" (five porters, independently) | `lake env lean`, which does **not** apply the lakefile's linters | that the modules were warning-free |
| "the cleanest untouched material found" | `sorry`/`native_decide` counts | that the *content* was good — two of seven files were mostly tautologies |
| "no bound on `discr K1` is proved anywhere" | a reading of the intent | the file proves two bounds |
| "Mathlib has no general Lucas sequence" | `grep 'Lucas sequence\|lucasSeq\|LucasSequence'` — a search for the **name** | that the object was absent; it is there as `Polynomial.dickson` |
| "Mathlib has no `Finset.sum` version of `add_mulVec`" | `grep 'Finset.sum_mulVec'` — a search in the **wrong namespace** | that the lemma was absent; it is `Matrix.sum_mulVec`, `Data/Matrix/Basic.lean:943` |
| "Mathlib has no rank of apparition" (ROADMAP §2.1) | `grep -rni 'apparition'` → 0 — a search for the **name** | that the theorem was absent; Mathlib proves it at `(P,Q) = (2a,1)` as `Pell.y_dvd_iff`, `NumberTheory/PellMatiyasevic.lean:412` |
| "this module contributes N theorem constants" (rounds 7–9, archived history) | a census filtered with `!isInternal` on the **raw** name, which skips every `private` declaration | a share commensurable with `AxiomGate`'s aggregate; it under-counted 17 vs 26, 18 vs 27, 6 vs 10. The gate's own source documents the trap |
| "nothing instantiates `Superadditive` / `Tolerance`" (ROADMAP §1.12) | `grep` for the name **excluding the defining file** — i.e. uses by *other* modules | that the definitions had no instance at all; both ship one in-file, `example : Superadditive id` and `natTolerance`, the latter documented as "witnessing that the definition is inhabited" |

Each was written in good faith by someone who had actually run a command. Before you write a
number in a docstring or a commit message, ask which of the two things you measured.

Corollaries that are already load-bearing here:

- **Warnings only exist at the `lake build` layer.** `lake env lean <file>` is silent on the
  Mathlib linter set. Always `lake build <ModuleName>` and `grep -c 'warning:'`.
- **A gate that has never failed is not known to work.** Every gate in `tools/` was shown red on
  a deliberately broken input before being trusted green. If you add or change one, do the same
  and put both runs in the commit message.
- **A clean proof footprint is not a claim about content.** `0 sorry, 0 native_decide` and
  "vacuous" are compatible; that is what `tools/VacuityGate.lean` is for, and even it has
  stated limits (see §4).

---

## 1. Current state, and how to re-measure it

```
cd ~/work/classical-lean
lake build                                  # rc 0, and grep -c 'warning:' must be 0
lake env lean tools/AxiomGate.lean          # every theorem within the kernel trio
lake env lean tools/VacuityGate.lean        # no theorem asserts nothing
python3 tools/check_sorry.py ClassicalLean  # no sorry / admit / native_decide / bare axiom
python3 tools/banned_vocab_scan.py ClassicalLean
python3 tools/check_records.py             # every shipped module is named in the records
lake env lean tools/UninformativeReport.lean  # a report, not a gate (§4; order VACUITY-3)
```

As of this handoff (2026-09-25 UTC, order G-10's close, the six commands run on a clean tree at
`fad33c5`, Lean and Mathlib v4.34.0): **52 modules in 10 top-level directories, 1595 theorem
constants, one axiom, no `sorry`, no `native_decide`, 0 warnings with the header linter on**;
gate 5 scans the 52 modules and `ClassicalLean.lean` (round 23, step V); gate 6 searches 25
records files. Do not trust that paragraph — it is a snapshot. Run the six commands. (Order
G-9's close had 50 modules and 1487 at `1e63d5b`; G-10 added `NumberTheory/Wolstenholme` with 91
theorem constants, round 29, and `Statistics/FrischWaughLovell` with 17, round 30. Order
G-8's close had 49 modules and 1434 at `552c38a`; G-9 added `NumberTheory/EuclidSteps` with 33
theorem constants, 17 of them `omega`'s auxiliaries, round 27, and 20 in
`NumberTheory/LucasApparition`, 10 of them auxiliaries, round 28 (73 → 93). Order
G-7's close had 48 modules and 1283 at `91bd2df`; G-8 added `NumberTheory/ZsigmondyPowSubPow`
with 131 theorem constants, and 151 in all, auxiliaries included, rounds 25 and 26: Zsigmondy
82 → 88, LucasApparition 66 → 73, AlgebraicGeneratingFunction 27 → 34. Order G-6's close had
1225 at `020f1ef`; G-7 added no module and 58 theorem constants, auxiliaries
included: round 23's bridges (Hopf 14 → 16, S3Quaternion 11 → 13, SecondOrder 36 → 46,
Zsigmondy 76 → 82, Characterisations 35 → 37, Helix 28 → 26, DesignConstants 58 → 56) and round
24's law of apparition (LucasApparition 26 → 66). Order G-5's close had 45 modules and 1098 at
`7cac0f6`; G-6 added
`Simplex/SecondOrder` with 36 constants and `Statistics/CramerRao` with 15, round 21, and
`NumberTheory/Zsigmondy` with 76, round 22; every module's Authors line now credits Claude
(Anthropic), round 21.)

**Dated 2026-10-07 (order LEAN-3, round 31; branch `prove-disc-biquadratic`, DSMain):** the six
commands on that branch: 53 modules, **1662 theorem constants, no axiom** (`0 scoped exceptions`), no
`sorry`, no `native_decide`, 0 warnings. `NumberTheory/BiquadraticDiscriminant` is new (53 constants).
On `master` the paragraph above still holds until the branch is pushed.

**Toolchain: `leanprover/lean4:v4.34.0`, Mathlib `5ed2965256` (tag v4.34.0)**, from order 0923's J3
(round 17), which moved the library from `v4.29.0-rc2` / `8f07524533` through v4.29.1, v4.30.0,
v4.31.0, v4.32.2, v4.33.1 and v4.34.0. No theorem statement changed in meaning: Mathlib deprecated
`stdSimplex`, the library's `closedSimplex` has its definition word for word (equal by `rfl`), and
`stdSimplex ℝ X` became `closedSimplex X` in eleven theorems, renamed `*_stdSimplex →
*_closedSimplex`, and in six declarations that kept their names — `orderedSimplex`,
`mem_orderedSimplex`, `existsUnique_mem_orderedSimplex`, `exists_mem_orderedSimplex_and_eq`,
`exists_mem_orderedSimplex_logSumExp_eq`, and an `example` in `Simplex/Involution`. No `backward.*`
option was added. One linter is off, and
a reviewer should know it: `set_option linter.defProp false in` on `isLocalId` (a `def` on
purpose; see its docstring).
**Dated 2026-09-23 (order G-5, round 19):** the header linter is on since round 19. Until then a
second linter was off, `weak.linter.style.header = false` for the whole library in
`lakefile.toml`, because it demands a Mathlib copyright block and the licence was Dustin's
decision. He chose Apache-2.0 on 2026-09-23; `LICENSE` is Mathlib's copy byte for byte, every
module and `ClassicalLean.lean` carry the header naming him, and the setting and its comment are
gone from `lakefile.toml`. Two limits of Mathlib's linter, read in its source
(`Mathlib/Tactic/Linter/Header.lean`): it never checks the library root file itself, and it finds
that root by a path relative to where `lake build` was started, so run the build from the
repository root or the copyright checks are silently skipped.
Mathlib v4.34.0's cache lacks `Mathlib.Probability.Kernel.Invariance`, which this library does not
import; the build check that stood in for `lake build --no-build Mathlib` at that step is in round
17.

**Undoing the toolchain move (dated 2026-09-23):** `git -C ~/work/classical-lean reset --keep
7ad841e` plus the parked `~/work/_parked/classical-lean.lake-v4.29.0-rc2` (moved back as `.lake`)
restore `v4.29.0-rc2` with round 18 kept. Order 0923's own undo line names `PRE`, `a18ab6a`, which
predates the rebase and would also drop round 18 and the records commits before it.

**Mathlib claims in this repository were measured at `8f07524533`** unless their text names
v4.34.0 (dated 2026-09-23). Re-measured at v4.34.0 on that date and still true: "no companion
matrix" (`Algebra/CompanionMatrix.lean`), the cross-entropy search (`Simplex/CrossEntropy.lean`), the
logsumexp and softmax searches (`Simplex/LogSumExp.lean`), `Dickson.lean`'s content
(`NumberTheory/LucasSequence.lean`; 277 lines now, the same 18 theorems), the conductor–discriminant
search (`NumberTheory/CompositumDiscriminant.lean`), "Mathlib has no Lucas numbers" (§2a below; the
same four `*lucas*` files), the `native_decide` axiom naming (`tools/AxiomGate.lean`, §4), and the
three `InformationTheory/` modules. Not re-measured, so still claims at `8f07524533`:
`NumberTheory/LucasApparition.lean` ("Mathlib has nothing of the shape"), the table in §0, §2 item 4,
and the rows of `ROADMAP.md` §2 — re-run a row's command before acting on it.

**Before you write anything, read `records/README.md`.** Two sessions worked this tree at once
on 2026-09-07/08 and two shipped modules landed with no round entry, because each session
correctly declined to edit the shared round file while the other held it. Rounds are now written as
fragments under `records/rounds/`, orders as files under `records/orders/`, and gate 6
(`tools/check_records.py`) fails if a module under `ClassicalLean/` is named in none of them.
Claim your modules in `records/CLAIMS.md` first.

The one axiom is `disc_biquadratic_23` (`|discr ℚ(√2,√3)| = 2304`) in
`NumberTheory/CompositumDiscriminant.lean`, registered in `AxiomGate.scopedExceptions` and
carrying exactly two theorems. **Discharging it is real work worth doing** — the module header
records the Mathlib search that failed to close it, and Mathlib moves.
**Dated 2026-10-07 (order LEAN-3, round 31; branch `prove-disc-biquadratic` on DSMain, not yet
on `master`):** discharged. `disc_biquadratic_23` is a theorem with the same statement, proved
through the ring of integers: `NumberTheory/BiquadraticDiscriminant.lean` shows `ℤ[θ] = 𝓞` for
`θ = (√2 + √6)/2 − 1` (minpoly `X⁴ + 4X³ + 2X² − 4X − 2`, Eisenstein at 2; the prime 3 by a trace
argument) and `discr = 2304`. `AxiomGate.scopedExceptions` is empty. The search findings below were
right about what Mathlib lacks; they were wrong that it was needed. The remaining paragraphs of
this section are history.

**Update, 2026-09-08 — the cyclotomic route is measured, and it does not close the axiom.**
Reported by the G-4 session and recorded here because it existed only in a chat transcript;
**not re-measured while writing this note**, so treat the arithmetic as attributed rather than
checked.  The Mathlib pin has not moved (`.lake` still at `8f07524533`), so "Mathlib moves" does
not yet apply.  **(2026-09-23: the pin has since moved to v4.34.0, round 17; the G-4 searches were
re-run there and the axiom stands — see the G-4 order.)**  An independent search adding `conductor.discriminant`,
`discr.*tower|relativeDiscr`, `ringOfIntegers.*(quadratic|biquad)` and `index.*discr` returned
nothing beyond what the module already cites.

The sharper finding: `natAbs_discr_sq_dvd_of_tower` and `discr_cyclo24 = 5308416` already exist
axiom-free, so realising `K1` inside the 24th cyclotomic field would give `|discr K1|` dividing
2304.  Against the best lower bound this Mathlib has (`abs_discr_ge'`), that still leaves **ten**
surviving divisors of 2304 in the best case — totally real, r2 = 0, bound 113.78 — and 14 at
r2 = 2, versus 25 under the `abs_discr_gt_two` the module actually uses.  So the cyclotomic
embedding cannot force 2304 even if it were built.  The §6 argument worked because 125 = 5^3
leaves one square-divisor candidate.  Closing this needs the conductor-discriminant formula or the
ring of integers of a biquadratic field, neither of which is in this Mathlib.

Incidental: the module uses only `abs_discr_gt_two`, and `abs_discr_ge'` is strictly sharper, but
exploiting it needs `nrComplexPlaces K1 = 0` and `IsTotallyReal` appears nowhere in the module.

Available and not started: proving `(discr K1).natAbs` divides 2304 axiom-free, via the two square
roots as Gauss sums in the 24th cyclotomic field plus the existing tower lemma — roughly 100 lines
into a 1000-line module, the same shape as §6.  It narrows the axiom's content from one value to
ten candidates; **it does not discharge it.**

Build note: `.lake/` is gitignored and this project was built **offline**, by copying a
prebuilt Mathlib from another checkout on this machine. A fresh build elsewhere needs
`lake exe cache get`, which needs network.
**Since 2026-09-23 (round 17)** the tree is built at v4.34.0 by `lake exe cache get`, in the
`toolchain-bump` worktree, whose `.lake` order 0923's landing step moves into this tree; that step
parks the `v4.29.0-rc2` `.lake` — the offline-copy build described above — at
`~/work/_parked/classical-lean.lake-v4.29.0-rc2`.
One module of Mathlib's v4.34.0 cache is missing (`Mathlib.Probability.Kernel.Invariance`); this
library does not import it, so nothing is compiled — but `lake build --no-build Mathlib` exits 3
at this pin, and is not the check to use (round 17).

Second build note, and it will cost you an hour if you meet it cold: **`ring` closes no goal in
`PowerSeries R` under this toolchain** — not even `X * X = X ^ 2` — and `rw [sub_mul]` will not
match `1 - f`. It is not a `ring` bug. **Measured**: under `pp.explicit` with
`pp.fullNames`, `1` and `*` elaborate through `MvPowerSeries.instOne`/`instMul` while `-` goes
through `PowerSeries.instAddGroup` and `0` through `PowerSeries.instZero`; Mathlib declares both
families, each `by dsimp only [PowerSeries]; infer_instance`
(`RingTheory/PowerSeries/Basic.lean` lines 87 and 111). **Inferred**: that a lemma stated for one
family therefore fails to match a goal built from the other. The fix is one line, `set_option backward.isDefEq.respectTransparency false`,
which Mathlib itself sets before `PowerSeries.catalanSeries_sq_mul_X_add_one` and which
`Geometry/Helix.lean` already sets for matrix goals. `abel`, `sub_eq_add_neg` and `coeff`-level
`simp` work without it.
**Measured 2026-09-23 (order 0923, J3):** at Lean and Mathlib **v4.34.0** `ring` closes
`X * X = X ^ 2` and `(1 - X) * (1 + X) = 1 - X ^ 2` in `PowerSeries R` with **no** option, with
`backward.isDefEq.respectTransparency.types false`, and with `respectTransparency false` alike;
at `v4.29.0-rc2` the same file fails without the option (`~/work/_bump-evidence/RingPowerSeries.lean`,
kept). At this library's toolchain since round 17, v4.34.0, the note therefore no longer applies;
the ten modules' `backward.isDefEq.respectTransparency false` lines stay until the next order
removes them.
**Dated 2026-09-23 (order G-5, round 19):** all fifteen went — the nine file-level settings
(`CompanionMatrix`, `AlgebraicGeneratingFunction`, `RecurrenceGeneratingFunction`, `Helix`,
`Hopf`, `S3Quaternion`, `SU2SO3`, `LucasSequenceGeneratingFunction`, `PowerSumCases`) and the
six scoped ones in `CompositumDiscriminant`. Each was removed alone and followed by a full
`lake build` (rc 0, 0 warnings) and a dump of every theorem type and definition, compared with
the dump taken before (no change). Two modules needed small proof edits, all of one kind: a
rewrite with a `Finset.sum` lemma no longer matched the sum's instance argument syntactically,
and `erw` does — one `example` in `LucasSequenceGeneratingFunction`, two proofs in
`PowerSumCases`. The re-run of `RingPowerSeries.lean` (rc 0, no output) is in
`~/work/_bump-evidence/ring-v4.34.0-g5.txt`.

**Dated 2026-10-13 UTC (order LEAN-27, round 56; branch `lean-27`, DSMain):** batch 1 of
MATH-PLAN-library-2, items 79 to 83: two new modules, `Analysis/ConvexConjugate` (the convex
conjugate valued in `EReal`, Fenchel–Young, antitonicity, `f** ≤ f`) and `Algebra/Kantorovich`
(the Kantorovich inequality under Loewner bounds, and the equal mix of eigenvectors that reaches
it), and three extended: `Probability/EffectiveSampleSize` (the variance of a sum for a
covariance-stationary series, and the variance-ratio identity), `Statistics/GeneralizedLeastSquares`
(generalised least squares for a common mean is `minWeights`; it now imports
`Analysis/MinimumQuadraticForm`) and `Algebra/MinMax` (Ky Fan's maximum principle). Counts on this
order's working tree, re-measured by its gates on the clean tree (round 56's fragment):
**122 modules, 3197 theorem constants (3158 + 39), `lake build` 4168 jobs, 0 warnings**. Job 0
changed the vacuity gate's `unfoldNamed` (§4).

**Dated 2026-10-13 UTC (order LEAN-28, round 57; branch `lean-28`, DSMain):** batch 2 of
MATH-PLAN-library-2, items 84 to 88, and item 80b; no new module, six extended:
`Probability/GamblersRuin` (the biased `±1` walk: it leaves `(−b, a)` with chance `1` for every up
chance `p`, reaches `a` first with chance `(r^b − 1)/(r^(a+b) − 1)`, `r = (1 − p)/p`, and for
`p < 1 − p` ever reaches `a` with chance at most `(p/(1 − p))^a`, by Ville's inequality; it now
imports `Probability/MaximalInequality` and Mathlib's `Probability/HasLawExists`),
`Analysis/FiniteGame` (the minimax equality by exponential weights for every real matrix, by an
affine change of payoffs, without Sion's theorem), `Combinatorics/ArbitrageCycle` (item 65's
counterexamples A1 to A3 as Lean `example`s), `Probability/LongestRun` (the measurability
hypothesis of `measureReal_no_run_le` stays, now only for the trials that count, with a Lean
`example` of why), `InformationTheory/CompressionTest` (compression scores fed to e-BH keep the
expected false share at most `q`, under a probability measure, which is needed; it now imports
`Probability/EValueStepUp`) and `Probability/EffectiveSampleSize` (item 80's product form,
`variance_sum_eq_mul_one_add`, with no extra hypothesis). Counts on this order's working tree,
re-measured by its gates on the clean tree (round 57's fragment): **122 modules, 3228 theorem
constants (3197 + 31), `lake build` 4170 jobs, 0 warnings** (two Mathlib modules more, from
`HasLawExists`).

**Dated 2026-10-15 UTC (order LEAN-29, round 59; branch `lean-29`, DSMain):** batch 3 of
MATH-PLAN-library-2, items 91 to 95, and job 0; one new module, `Analysis/Gruss` (Grüss's
inequality for bounded random variables and for averages on `[a, b]`, with the covariance's
Cauchy–Schwarz inequality by the discriminant argument), and four extended:
`Probability/LongestRun` (no run of `r` losses has chance at most `exp (−⌊n / r⌋ q^r)`; it now
imports Mathlib's `Analysis/Complex/Exponential`), `Analysis/Simpson` (Simpson's rule is
`(4 T(2N) − T(N))/3` with Mathlib's trapezoidal rule, exactly; it now imports Mathlib's
`TrapezoidalRule`), `Analysis/EulerMethod` (for `y' = −c y`: implicit Euler decays for every step,
explicit Euler exactly when `h c < 2`) and `Probability/GamblersRuin` (the ruin chance is
`U b / U (a + b)` with `U = lucasU (1 + r) r`, the fair walk included, so wider than item 84; it
now imports `NumberTheory/LucasSequence`). Narrowing: none. Job 0 moved order LEAN-27's junk-value
checks into `Analysis/ConvexConjugate` as `example`s and stated the `0 < a` form of
`exists_isPrimitiveDivisor_of_forall_prime_dvd` as an `example` in `NumberTheory/PrimitiveDivisor`.
Counts measured by this order's development runs, to be re-measured by its gates on the clean tree
(round 59's fragment): **123 modules, 3246 theorem constants (3228 + 18), `lake build` 4171 jobs,
0 warnings** (no Mathlib module more).

**Dated 2026-10-15 UTC (order MERGE-1, round 61; branch `merge-1`, DSMain):** one merge lands CI
(`.github/workflows/ci.yml`, §4) and order CLOUD-MATH-1 (round 60, written in a cloud session on
the GitHub branch `cloud-math-1`) on top of LEAN-29. Five new modules, each unchanged by the
merge: `InformationTheory/HanInequality` (item 131, Han's inequality,
`(n − 1) H(X) ≤ ∑ᵢ H(X without coordinate i)`), `Analysis/FrankWolfe` (item 135, Frank–Wolfe on
the closed simplex, `f (x k) − f z ≤ 4 L / (k + 2)`, and `fw_general` for any convex set of squared
diameter at most `D`), `Analysis/StatePrices` (item 136, no arbitrage exactly when strictly
positive state prices exist, finite form), `Probability/PolyaUrn` (item 137, Pólya's urn: the red
share is a martingale, converges almost surely, and any almost-sure limit lies in `[0, 1]`) and
`Probability/Reflection` (item 139, the reflection principle for the fair `±1` walk). The merge
conflicted only on lines both sides added (`ClassicalLean.lean`, `records/CLAIMS.md`,
`records/orders/INDEX.md`) and kept every one of them; `incoming/` (the cloud session's report,
predictions and reviews) went to the lane and left the tree. This section names no other list of
modules, so the five are named here. Counts predicted from both sides' measured gates, to be
re-measured by this order's gates on the clean tree (round 61's fragment): **128 modules, 3335
theorem constants (3246 + 89, round 60's per-module table), `lake build` 4176 jobs, 0 warnings**
(no Mathlib module more).

**Dated 2026-10-15 UTC (order LEAN-30, round 62; branch `lean-30`, DSMain):** batch 4 of
MATH-PLAN-library-2, items 96 to 100, and job 0; no new module, four extended:
`Probability/CovarianceDirections` (item 96, Hadamard's inequality for a covariance matrix,
`det S ≤ ∏ Var`, for any finite measure; it now imports `Algebra/HadamardInequality`),
`Statistics/GeneralizedLeastSquares` (item 98, the Kantorovich inequality at the vector of ones,
`(1ᵀ V 1)(1ᵀ V⁻¹ 1)/n² ≤ (m + M)²/(4 m M)`, read as Bloomfield and Watson's bound on ordinary
against generalised least squares for a common mean; it now imports `Algebra/Kantorovich`),
`Probability/FiniteChain` (item 97, relative entropy to a stationary vector never increases along
the chain, `π` need not be a law; item 100,
Perron–Frobenius for a primitive chain, one stationary law with no `P ≥ 0` and no `k > 0`, and the
rate `(1 − n δ) ^ (t / k)` with no `k > 0`) and `InformationTheory/CompressionTest` (item 99, the
plug-in score is at most every fixed-rate score where the fixed rate gives the string positive
mass, and its false-alarm rate stays at most `α` under every Bernoulli law; no new import).
Narrowing: none. Job 0 reworded five older docstring lines of `NumberTheory/PrimitiveDivisor` and
`Analysis/Gruss` (and appended one `example` to PrimitiveDivisor). Counts, all to be re-measured by
its gates on the clean tree (round 62's fragment): **3345 theorem constants**, 3335 from the base
axiom gate plus 10 from the censuses of the changed modules; **128 modules** and **`lake build`
4176 jobs** carried over from the base (no module and no Mathlib module added, by the import
closure); 0 warnings in the changed modules' own builds.

**Dated 2026-10-16 UTC (order LEAN-31, round 63; branch `lean-31`, DSMain):** batch 5 of
MATH-PLAN-library-2, items 101 to 105, and job 0; one new module, six extended:
`Probability/MovingAverage` (item 101, the spectral density of a moving average, finite form,
`∑_{|k| ≤ q} γ(|k|) e^(−i k φ) = v |∑ⱼ θⱼ e^(i j φ)|²`, and its real form `≥ 0`),
`Statistics/Sufficiency` (item 102, bounded completeness, that completeness gives it, and Basu's
theorem with it), `Analysis/FiniteGame` (item 103, Bayes equals minimax with losses in `[0, ∞]`,
item 63's open point, from the carried draft `d3103-r1-s1.lean`), `Statistics/ResidualVariance`,
`Probability/LikelihoodScore` and `Probability/EffectiveSampleSize` (item 104, LEAN-17's reviews r3,
r5 and r6 as primed theorems from the carried draft `d3204-r4-s1.lean`; EffectiveSampleSize now
imports `Mathlib.Probability.HasLawExists` and `Mathlib.Probability.Distributions.Gaussian.Real`),
and the new `Probability/StepDownProcedure` (item 105, Holm's step-down procedure, for any finite
measure; it imports `Mathlib.MeasureTheory.Measure.Real` and `Mathlib.Probability.UniformOn`).
Narrowing: none. Wider than the plan's reading, two conditions: item 105 for any finite measure;
item 104's Chernoff bound with no `p₀ < 1`; item 104's `q ≤ 1` and `0 < p₀` are kept though not
needed. Job 0: the Bloomfield and Watson credit is complete and marked as checked against the
journal's contents page. Counts, all to be re-measured by its gates on the clean tree (round 63's
fragment): **3372 theorem constants**, 3345 from the base axiom gate plus 27 from the censuses of
the changed modules (Method B); **129 modules** (128 under `ClassicalLean/` at `49c4c98` plus
`StepDownProcedure`; the Lean count of the base closure, which also counts the root module, gives
129 at the base); **`lake build` 4177 jobs**, predicted from the import closure, which is **4160**
modules at `49c4c98` and 4161 after (order LEAN-31's revised closure script; order LEAN-30's script
read import lines inside comments and printed 9037). Also new: rules 36 and 37 below (dated times;
`el.sh` refuses names not probed).

**Dated 2026-10-18 UTC (order LEAN-32, round 64; branch `lean-32`, DSMain):** batch 6 of
MATH-PLAN-library-2, items 106 to 110, the last batch above the plan's cut; one new module, four
extended: `Probability/IntegralTransform` (item 106, new: the probability integral transform,
`P(F(X) ≤ u) ≤ u` for `u ≥ 0`, with equality on `[0, 1]` when `F` is continuous; it imports
`Mathlib.Probability.CDF`, `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` and, for its witness,
`Mathlib.Probability.Distributions.Gaussian.Real`), `Probability/GlivenkoCantelli` (item 107, the
Kolmogorov–Smirnov test is consistent, and its test with thresholds `c n → 0` rejects eventually
when `F` differs from `cdf ν₀`; it now imports `Mathlib.Probability.HasLawExists`),
`Analysis/LinearODE` (item 108, a Lyapunov bound for `x' = A x`), `InformationTheory/MethodOfTypes`
(item 109, the asymptotic equipartition property; it now imports `Mathlib.Probability.StrongLaw` and
`Mathlib.Probability.HasLawExists`) and `InformationTheory/Channel` (item 110, data processing for
every f-divergence). Narrowing: none. Wider than the plan's reading, five conditions: item 107 for
any measure `ν₀`, and its first theorem with no "`F` differs from `F₀`" hypothesis; item 108 with no
positive definiteness and no symmetry of `P`; item 109's law hypothesis; item 109 with pairwise
independence only; item 110 with `q ≥ 0` and the support condition. Item 107's second theorem is an
addition. Counts, all to be re-measured by its gates on the clean tree (round 64's fragment): **3379
theorem constants**, 3372 from the base axiom gate plus 7 from the censuses of the changed modules
(Method B, equal to Method A); **130 modules**; **`lake build` 4178 jobs**, predicted from the
import closure (4161 → 4162 modules) and seen by the root build inside `rootrun.sh` (label
`used-head-build`). Also new: rules 38 and 39 below (a fresh root build before any tool that imports
`ClassicalLean`; run citations in commit messages written by script).

**Dated 2026-10-20 UTC (order MERGE-2, round 67; branch `merge-2`, DSMain):** one merge lands order
CLOUD-MATH-2 (round 66, written in a cloud session on the GitHub branch `cloud-math-2`, `284dd5f`)
on top of RULES-1. Five new modules, items 147, 150, 151, 152 and 153 of MATH-PLAN-library-2 (below
its cut), each unchanged by the merge: `Analysis/PowerMethod` (item 147, the power method: for a
symmetric linear map with a strictly dominant eigenvalue, the rescaled iterates tend to its
eigenvector at rate `(|λ₁|/|λ₀|)^k`, `tendsto_powerIterate`), `Algebra/Pseudoinverse` (item 150,
the Moore–Penrose pseudoinverse `pinv`: its four equations, uniqueness, least squares for every
design, and `(Aᵀ A)⁻¹ Aᵀ` at full column rank), `Probability/ChiSquared` (item 151, the sum of
squares of `k ≥ 1` independent standard normals has the gamma law with shape `k/2` and rate `1/2`,
`hasLaw_sum_sq_gaussian`), `Analysis/KKT` (item 152, the KKT conditions are necessary under
Slater's condition for convex differentiable problems, `exists_kkt_of_slater`) and
`InformationTheory/Huffman` (item 153, Huffman's code has the least mean length among prefix-free
binary codes, `huffman_optimal`, with `huffmanLength`). The merge conflicted only in
`records/CLAIMS.md` and `records/orders/INDEX.md`, resolved by taking the branch's file and
appending MERGE-2's row. The cloud session's report, predictions and reviews
went to the lane (`lean/CLOUD-MATH-2-REPORT.md`, `lean/CLOUD-MATH-2-PREDICTIONS.md`,
`lean/CLOUD-MATH-2-reviews.md`) and `incoming/` left the tree; its toolkit and evidence stay in
history at `284dd5f` (`git show 284dd5f:incoming/README.md`, `git archive 284dd5f incoming/tools`).
This section names no other list of modules, so the five are named here. Counts predicted from the
cloud tip's measured gates, to be re-measured by this order's gates on the clean tree (round 67's
fragment): **135 modules, 3458 theorem constants (3379 + 79, round 66's censuses), `lake build` 4188
jobs, 0 warnings** (five Mathlib modules more, round 66's import closure).

**Dated 2026-10-21 UTC (order LEAN-33, round 69; branch `lean-33`, DSMain):** five items from below
MATH-PLAN-library-2's cut, from the API-credit drafts, each in its home module, and five VACUITY-3
witness rows; no new module, seven extended:

- item 111, `Algebra/Kantorovich`: steepest descent with exact line search shrinks `xᵀ A x / 2` in
  one step to at most `((M − m)/(M + m))²` times its value (`quadForm_steepestStep_le`);
- item 112, `Analysis/GradientDescent`: the Polyak–Łojasiewicz rate `(1 − μ/L)^k`
  (`sub_le_pow_mul_of_polyakLojasiewicz`), wider than its plan row: `f*` is any lower bound and
  nothing is asked of `μ` or `L`;
- item 134, `Analysis/GradientDescent`: projected gradient descent at rate `1/k`
  (`sub_le_of_projGradientStep`), wider than its plan row: the set need not be closed, since each
  step's nearest-point property is a hypothesis;
- item 116, `Analysis/ExponentialWeights`: exponential weights is mirror descent, over
  `closedSimplex ι` (`isMinOn_inner_add_relEntropy_softmax`); the module now imports
  `InformationTheory/Entropy`;
- item 117, `Analysis/ConvexConjugate`: the conjugate of log-sum-exp on the open simplex is
  `∑ p i log p i` (`convexConjugate_logSumExp`); the module now imports `Simplex/LogSumExp`;
- VACUITY-3 rows 7 and 8 re-witnessed with two genuine rounds (`Probability/LikelihoodScore`),
  rows 9 and 10 (`Probability/EffectiveSampleSize`) and row 67 (`Probability/GlivenkoCantelli`)
  witnessed.

Narrowing: none. Counts predicted by this order's
job 3, to be re-measured by its gates on the clean tree (round 69's fragment): **135 modules, 3468
theorem constants (3458 + 10, the censuses of the changed modules), `lake build` 4188 jobs, 0
warnings** (no module added, by the import closure).

**Dated 2026-10-21 UTC (order MERGE-3, round 70; branch `merge-3`, DSMain):** one merge lands order
CLOUD-MATH-3 (round 68, written in a cloud session on the GitHub branch `cloud-math-3`, `8c5fa22`)
on top of LEAN-33. Five new modules, items 113, 121, 124, 126 and 130 of MATH-PLAN-library-2 (below
its cut), each unchanged by the merge: `Analysis/SubgradientMethod` (item 113, the subgradient
method: the best of the first `T` iterates is within `(‖x₀ − z‖² + η² G² T)/(2 η T)` of `f z`,
`min_sub_le_of_subgradient`, GENERALIZED: no convexity is asked, only the subgradient inequality at
the iterates), `Probability/EfronStein` (item 121, the Efron–Stein inequality for independent
coordinates on finite sets, `Var f ≤ ∑ᵢ E[Varᵢ f]`, `variance_le_sum_variance_coord`, and with
bounded differences `Var f ≤ ∑ cᵢ²/4`, `variance_le_sum_sq_div_four`),
`Probability/BernsteinInequality` (item 124, Bernstein's inequality
`P(∑ Xᵢ ≥ t) ≤ exp(−t²/(2(v + b t/3)))`, `measureReal_sum_ge_le_bernstein`),
`Probability/OrderStatistics` (item 126, the chance that the `k`-th smallest of `n` independent
draws is at most `x` is `∑_{j ≥ k} C(n, j) F^j (1 − F)^(n−j)`, `measureReal_orderStat_le`, with
`orderStat`) and `InformationTheory/ChannelCapacity` (item 130, the binary symmetric channel with
crossover `ε` has capacity `log 2 − h(ε)`, reached by the uniform input, `mutualInfo_bsc_le` and
`mutualInfo_bsc_half`). The merge conflicted only in `records/CLAIMS.md` and
`records/orders/INDEX.md`, resolved by taking the branch's file and appending the last two lines of
this order's records-first commit. The cloud session's report, predictions and reviews went to the
lane (`lean/CLOUD-MATH-3/report.md`, `lean/CLOUD-MATH-3/data/PREDICTIONS.md`,
`lean/CLOUD-MATH-3/data/reviews.md`) and `incoming/` left the tree; its toolkit and evidence stay in
history at `8c5fa22` (`git show 8c5fa22:incoming/README.md`, `git archive 8c5fa22 incoming/tools`).
The cloud session's last commit, `8c5fa22`, cannot be citechecked from the committed log: its
`Evidence:` line cites lines 882 to 922, but the log it copied into `incoming/evidence/` has 914
lines. Counts predicted from the trial merge's measured gates, to be re-measured by this order's
gates on the clean tree (round 70's fragment): **140 modules, 3527 theorem constants (3468 + 59,
round 68's censuses), `lake build` 4193 jobs, 0 warnings**.

**Dated 2026-10-21 UTC (order LEAN-34, round 71; branch `lean-34`, DSMain):** five items from below
MATH-PLAN-library-2's cut, from the API-credit drafts, each in its home module; VACUITY-3 row 70
re-witnessed; and bridge row 163 proved (statements by claude-ai, proofs by the session); no new
module, five extended and FiniteGame's row-70 witness replaced:

- item 118, `Statistics/NeymanPearson`: the Karlin–Rubin theorem in the textbook form, the
  likelihood ratio allowed to be `+∞` (`HasMonotoneLikelihoodRatio'`,
  `isUniformlyMostPowerful_of_monotoneLikelihoodRatio'`), for a threshold test of positive size;
- item 144, `Statistics/NeymanPearson`: the Bretagnolle–Huber bound
  (`size_add_one_sub_power_ge`); the module now imports `InformationTheory/Entropy`;
- item 122, `InformationTheory/MethodOfTypes`: Sanov's theorem, lower half, for one type class
  (`le_measureReal_empirical_eq`), GENERALIZED: `p ≥ 0` only;
- item 140, `Probability/YuleWalker`: the Durbin–Levinson recursion (`durbinLevinson_spec`);
- item 142, `Probability/CovarianceDirections`: principal components
  (`sum_variance_mix_le_sum_eigenvalues`), GENERALIZED: any finite measure; the module now imports
  `Algebra/MinMax`;
- VACUITY-3 row 70 (`Analysis/FiniteGame`) re-witnessed with the kernel `P θ = dirac 0 + dirac θ`;
- bridge row 163, `InformationTheory/ChannelCapacity`: binary symmetric channels in series
  (`mutualInfo_bsc_pow_le`, `mutualInfo_bsc_pow_half`, `tendsto_capacity_bsc_pow`); the module now
  imports `Probability/TwoStateChain`.

Narrowing: none. Counts predicted by this order's job 3, to be re-measured by its gates on the clean
tree (round 71's fragment): **140 modules, 3574 theorem constants (3527 + 47, the censuses of the
changed modules), `lake build` 4193 jobs, 0 warnings** (no module added).

**Dated 2026-10-25 UTC (order LEAN-35, round 72; branch `lean-35`, DSMain):** five items from below
MATH-PLAN-library-2's cut, from the API-credit drafts, each in its home module; no new module, five
extended:

- item 114, `Probability/KalmanVariance`: the steady Kalman filter of a local level, the Riccati
  root `P` equals the steady value `(q + K² r)/(1 − (1 − K)²)` of a first-order recursion with
  coefficient `1 − K`, `K = P/(P + r)` (`riccatiRoot_eq_steady`); the module now imports
  `Probability/FirstOrderRecursion`;
- item 115, `Probability/MovingAverage`: the long-run variance of a moving average,
  `Var(X 0 + ⋯ + X (n − 1)) = n v (∑ θ)² − 2 ∑_{k ≤ q} k γ(k)` for `n > q`, and
  `n Var(mean) → v (∑ θ)²` (`variance_sum_movingAverage`); the module now imports
  `Probability/EffectiveSampleSize`;
- item 125, `Probability/MaximalInequality`: the Hájek–Rényi inequality
  (`measureReal_exists_mul_abs_ge_le`), GENERALIZED: any finite measure, and no `S 0 = 0`;
- item 138, `Probability/FairGame`: Wald's second identity `E[S_τ²] = σ² E[τ]` for a bounded
  stopping time (`integral_stoppedValue_sq_eq`), GENERALIZED: each step independent only of the
  past, any filtration in which step `n` is known at time `n + 1`; the module now imports Mathlib's
  `Probability/Independence/InfinitePi` and `Probability/BorelCantelli`, for its witness;
- item 148, `Probability/FiniteChain`: mean hitting times of a finite chain, `h = ∑ₜ Q^t u` (`Q`
  the chain killed on the target, `u` the indicator off it) is the only `g` with `g = 1 + P g` off
  the target and `g = 0` on it (`meanHitting_eq`), and the corollary for a chain whose every entry
  is at least `δ > 0`, with a nonempty target (`meanHitting_eq_of_le`).

Narrowing: none. Counts predicted by this order's job 3, to be re-measured by its gates on the clean
tree (round 72's fragment): **140 modules, 3602 theorem constants (3574 + 28, the censuses of the
changed modules), `lake build` 4193 jobs, 0 warnings** (no module added).

**Dated 2026-10-26 UTC (order VACUITY-4, round 73; branch `vacuity-4`, DSMain):** the witness gate,
the older witnesses brought to rule 2, and two gate leftovers; no theorem added or changed.

- The witness gate, `tools/witness_gate.py`, with its listing driver `tools/WitnessListing.lean`,
  its tests `tools/witness_gate_tests.py` and 119 fixtures under `tools/witness-fixtures/` (§4), after
  five rounds of cold review, a confirming pass of the last fixes (review a4c, whose finding is
  stated as a limit in §4) and rulings 1 to 6 of the order; its listing file
  `tools/witness_reviewed.txt` holds one entry, PrimitiveDivisor's line 423 (a name-resolution
  check, `LISTED`).
- Witnesses: 23 new rule-2 witnesses in ten modules (Superadditive 5, Spectral3x3 1,
  ConvexConjugate 1, GeneralizedLeastSquares 1, Kantorovich 2, MinMax 2, CompressionTest 2,
  EffectiveSampleSize 4, GamblersRuin 3, MaximalInequality 2); MinMax's line 443 moved after the
  module's last line and rewritten (`sum_eigenvalues_eq_iSup`); 15 blocks removed: the thirteen
  typed examples that claimed a witness, and MaximalInequality's two frozen witnesses, re-witnessed
  at one step (Goal item 4's case, dated below in §4); the sweep's three re-witnesses (below) replace
  their blocks one for one and are in neither count. Each group had a cold review (b) and a
  confirming pass; several values are the reviewers'.
- The process sweep (Goal item 5): 44 witnesses read by three fresh reviewers; three re-witnessed
  (GradientDescent `sub_le_of_projGradientStep` and YuleWalker `durbinLevinson_spec`, frozen;
  FairGame `integral_stoppedValue_sum_eq`, degenerate under rule 3); no `LISTED-FAULT`.
- The leftovers: the vacuity gate's FAIL text names case 5 and says what UNCHECKED and
  KERNEL-REJECTED mean; the report tool's whole-library command has a finite outer budget.

Narrowing: none. Counts predicted by this order's job 6, to be re-measured by its gates on the clean
tree (round 73's fragment): **140 modules, 3602 theorem constants, `lake build` 4193 jobs, 0
warnings**; the witness gate `WITNESSGATE PASS` with 171 `OK`, 1 `LISTED`, 205 `TYPED`.

**Dated 2026-10-27 UTC (order LEAN-36, round 74; branch `lean-36`, DSMain):** six items from below
MATH-PLAN-library-2's cut, from the API-credit drafts, each in its home module; no new module, six
extended:

- item 127, `Analysis/HermiteHadamard`: Fejér's inequality,
  `f ((a + b)/2) ∫ g ≤ ∫ f g ≤ ((f a + f b)/2) ∫ g` for `f` convex and continuous on `[a, b]` and a
  weight `g ≥ 0`, integrable and symmetric about the midpoint (`convexOn_midpoint_mul_integral_le`,
  `integral_mul_le_endpoints`);
- item 128, `Analysis/EulerMaclaurin`: Euler–Maclaurin to second order, for integers `a ≤ b`, `f`
  and `f'` continuous on `[a, b]` with derivatives `f'`, `f''` inside and `f''` integrable,
  `∑_{k=a}^{b} f k = ∫ₐᵇ f + (f a + f b)/2 + (f' b − f' a)/12 − ∫ₐᵇ B₂(fract t)/2 · f''`
  (`sum_eq_integral_add_two`);
- item 129, `Analysis/LinearODE`: variation of constants, every solution of `x' = A x + f(t)` with
  `f` continuous is `x t = exp (t A) x(0) + ∫₀ᵗ exp ((t − s) A) f(s) ds`
  (`eq_exp_smul_mulVec_add_integral`);
- item 132, `Analysis/JacobiIteration`: Gauss–Seidel, under the hypotheses of
  `norm_jacobiStep_sub_le` and `ρ ≤ 1`, one sweep multiplies the error by at most `ρ`
  (`norm_gaussSeidelStep_sub_le`) and `k` sweeps by at most `ρ ^ k`
  (`norm_gaussSeidelIterate_sub_le`), GENERALIZED: `ρ = 1` (weak dominance) is allowed;
- item 133, `Analysis/RoundingError`: forward substitution is backward stable, with a nonzero
  diagonal, every rounding at most `u` and `n u < 1`, the computed solution of a lower-triangular
  `L x = b` solves `(L + ΔL) x = b` with `|ΔL i j| ≤ γ n · |L i j|` for
  `j ≤ i < n` (`exists_forwardSubstComputed_eq`);
- item 146, `Analysis/EulerMethod`: Heun's method (`heunIterate`, iterates `u_k` from `y t₀`) has
  global error of order `h²`, under the hypotheses of `abs_sub_eulerIterate_le` and a `K`-Lipschitz
  derivative of `t ↦ f (t, y t)`,
  `|y (t₀ + k h) − u_k| ≤ h² (K + 3 L M)/(12 L) · (exp (L k h) − 1)` (`abs_sub_heunIterate_le`); the
  module now imports Mathlib's `Analysis/SpecialFunctions/Trigonometric/Bounds`, for its witness.

Narrowing: none. Counts predicted by this order's job 3, to be re-measured by its gates on the clean
tree (round 74's fragment): **140 modules, 3666 theorem constants (3602 + 64, the censuses of the
changed modules), `lake build` 4193 jobs, 0 warnings** (no module added); the witness gate
`WITNESSGATE PASS` with 179 `OK` (171 + this order's 8), 1 `LISTED`, 205 `TYPED`.

**Dated 2026-10-27 UTC (order VACUITY-5, round 75; branch `vacuity-5`, DSMain):** three rule-2
witnesses in `Probability/YuleWalker`, one each for `covariance_eq_sum`, `isSolution_autocovariance`
and `exists_poly_mk_autocovariance_eq` (VACUITY-3 rows 31 and 32, and the third theorem), on one
covariance-stationary autoregression of order 2 driven by independent Gaussian noises on `ℕ → ℝ`
(`Measure.infinitePi`); dated in §4. No declaration added or changed. The module now imports
Mathlib's `Probability/Distributions/Gaussian/Real` and `Probability/Independence/InfinitePi`, both
already in the root's import closure. Counts measured by this order's gates on the clean tree at G
(round 75's fragment): **140 modules, 3666 theorem constants (unchanged), `lake build` 4193 jobs, 0
warnings**; the type dump unchanged (removed 0, added 0, changed 0, proof-only 0); the witness gate
`WITNESSGATE PASS` with 182 `OK` (179 + 3), 1 `LISTED`, 205 `TYPED`.

**Dated 2026-10-28 UTC (order LEAN-37, round 76; branch `lean-37`, DSMain):** five items from below
MATH-PLAN-library-2's cut, from the API-credit drafts, each in its home module; no new module, five
extended:

- item 123, `Algebra/MinMax`: Cauchy interlacing. For symmetric `T` on `E` (dimension `n`), a
  subspace `V` of dimension `m` and a symmetric `A` on `V` with `⟪A x, y⟫ = ⟪T x, y⟫` on `V` (the
  compression of `T`), `λ_k(A) ≤ λ_i(T)` when `i ≤ k` (`eigenvalues_compression_le`) and
  `λ_j(T) ≤ λ_k(A)` when `k + n ≤ j + m` (`le_eigenvalues_compression`);
- item 141, `Analysis/FiniteGame` (which now imports `Analysis/LinearProgram`): the minimax theorem
  for every real matrix, from linear-program duality (`minimax_eq_of_lp`); GENERALIZED against
  `minimax_eq_of_matrix`: no `Nonempty ι` or `Nonempty κ`, an empty side settled by Lean's `0` for
  an empty `⨅` or `⨆` in `ℝ`;
- item 143, `Probability/LongestRun` (which now imports `NumberTheory/Tribonacci`): in `n` fair
  independent trials the chance of no run of two losses is `fib (n + 2) / 2^n`
  (`measureReal_no_run_two_eq`) and of no run of three `tribonacci (n + 3) / 2^n`
  (`measureReal_no_run_three_eq`);
- item 145, `Combinatorics/ArbitrageCycle` (which now imports `Analysis/LinearProgram`): prices
  exist exactly when no cycle gains, a second proof of item 65's (a) ⇔ (b), by Farkas' lemma
  (`hasPrices_iff_of_lp`);
- item 149, `Probability/Extinction` (which now imports `Combinatorics/AlgebraicGeneratingFunction`
  and Mathlib's `RingTheory/PowerSeries/Trunc`): the total-progeny series `T = X · f(T)` has exactly
  one power-series solution (`existsUnique_progeny`), its coefficients sum to `extinctionChance p`
  for `p ≥ 0` summing to `1` (`progeny_eval_one_eq_extinctionChance`), and for `f s = (1 + s²)/2`
  they are the Catalan numbers over powers of `2` and sum to `1` (`coeff_progeny_catalan`);
  GENERALIZED against the plan's row: no `p 0 > 0` (with `p 0 = 0` both sides are `0`), and the
  uniqueness is a theorem of its own.

Narrowing: none. Counts predicted by this order's step 5, to be re-measured by its gates on the
clean tree (round 76's fragment): **140 modules, 3827 theorem constants (3666 + 161, the new theorem
constants of the five modules), `lake build` 4193 jobs, 0 warnings** (no module added); the type
dump `added=183`, `removed=0 changed=0`; the witness gate `WITNESSGATE PASS` with 189 `OK` (182 +
this order's 7), 1 `LISTED`, 205 `TYPED`.

**Dated 2026-10-28 UTC (orders CLOUD-MATH-4, round 77, cloud branch `cloud-math-4`; and MERGE-4,
round 78, branch `merge-4`, DSMain):** three bridges of `MATH-PLAN-library-2-bridges-2.md` as three
new modules, stated and proved in a cloud session (no drafts) and merged onto LEAN-37 by one merge
commit; no existing module changed:

- bridge 160, `InformationTheory/HuffmanEntropy` (new, imports `InformationTheory/Huffman`):
  Huffman's mean length is within one bit of the entropy, `H(p)/log 2 ≤ ∑ p i · ℓ i` for `p ≥ 0`
  summing to `1` (`le_sum_mul_huffmanLength`) and `∑ p i · ℓ i < H(p)/log 2 + 1` for `p > 0`
  (`sum_mul_huffmanLength_lt`); 3 theorem constants (round 77's census);
- bridge 162, `Probability/PrincipalComponents` (new, imports `Probability/CovarianceDirections`
  and `Analysis/PowerMethod`): principal components by power iteration. With a gap between the top
  two eigenvalues of the covariance map, the normalized iterates converge to the top eigenvector at
  rate `(λ₁/λ₀)^k` (`tendsto_powerIterate_covLin`), and that eigenvector is the direction of largest
  variance, the variance there being `λ₀` (`variance_mix_eigenvectorBasis_eq_and_le`); 4 theorem
  constants;
- bridge 161, `Statistics/JamesSteinRisk` (new, imports `Statistics/JamesStein` and
  `Probability/ChiSquared`): for `d ≥ 3` and a standard normal vector at the origin,
  `E[1/‖X‖²] = 1/(d − 2)` (`integral_inv_sqNorm_zero`) and the James–Stein estimator's risk is `2`
  (`integral_sqNorm_jamesStein_zero`); 10 theorem constants.

Narrowing: none. Counts predicted by order MERGE-4's step 7, to be re-measured by its gates on the
clean tree (round 78's fragment): **143 modules, 3844 theorem constants (3827 + 17), `lake build`
4196 jobs, 0 warnings**; the root's import closure 5732 modules (5729 + 3); the type dump
`added=17`, `removed=0 changed=0 proof_only=0`; the witness gate `WITNESSGATE PASS` with 195 `OK`
(189 + the cloud order's 6), copy-error 0.

---

## 2. What I claimed, and what I actually checked

The previous session proposed five additions. **Two of the underlying observations were verified
by grep; three were not.** Treat the unverified ones as hypotheses to test, and be willing to
conclude "not worth it" — one earlier candidate (`[retired name]`) was correctly declined after
measurement showed it was three Mathlib one-liners.

| # | claim | status | how to check |
|---|---|---|---|
| 1 | The library has **no Binet formula for `lucas`** | ~~measured~~ — **done**, see below | — |
| 2 | `Simplex/Gibbs` and `FisherRao` never reference `orderedSimplex` | **measured** — grep returns nothing | — |
| 3 | Four modules independently build a 2×2 companion matrix and reprove trace/det/charpoly | **measured — false as stated**, and the real duplication was elsewhere; see §2c | — |
| 4 | Lucas numbers have a rank-of-apparition theory mirroring `MersenneOrder` | **measured to be worth doing**, and larger than "one citation" — Mathlib has no `apparition` and no `Zsigmondy` at all. Scoped as `ROADMAP.md` §2.1 | — |
| 5 | Tree C's E₈ literal facts are worth an `Examples/` module | **NOT measured** | they are `native_decide` in the source; check whether `decide` closes them at these sizes before promising anything |

### 2a. The Binet connection — done

**This item is closed.** `NumberTheory/Lucas.lean` now proves

    lucas_isSol_fibRec  : Real.fibRec.IsSolution (fun n => (lucas n : ℝ))
    coe_lucas_eq  (n)   : (lucas n : ℝ) = φ ^ n + ψ ^ n
    coe_lucas_two_mul   : (lucas (2 * n) : ℝ) = (φ ^ 2) ^ n + (ψ ^ 2) ^ n

and a new module `NumberTheory/LucasCompanion.lean` joins the three formerly disjoint modules
with `companionMatrix_pow_trace : (M ^ n).trace = (lucas (2 * n) : ℝ)`, plus the determinant,
the characteristic polynomial `x ^ 2 - L (2n) * x + 1` of `M ^ n`, the eigenvalue reading, and
the orbit statement. Round 3, in the archived history,
records the Mathlib search and the gate results.

Two things a next session should know rather than rediscover:

- **Mathlib has no Lucas numbers.** The four files matching `*lucas*` are the Lucas–Lehmer test,
  the Lucas primality test, the Gauss–Lucas theorem and Lucas' congruence on binomials. The
  search is written out in the docstring of `coe_lucas_eq` (and in round 3, archived history).
- **"The orbit of that matrix" needs a seed as well as an action.** Both conventions work, on
  different vectors: `Matrix.vecMul` advances the consecutive pair `(L (2n), L (2n + 2))`, and
  `Matrix.mulVec` advances the signed pair `(L (2n), -L (2n + 2))`. Both are shipped. Carrying
  the unsigned pair to the column action is what fails, and that is a spot check at `n = 0`.
  An earlier draft of this file recorded the column action as simply wrong; it is not, and the
  claim was withdrawn before the follow-up commit.

What is **not** done, and is the obvious continuation: `lucas_sq_sub_five_mul_fib_sq` and
`lucas_two_mul` are now one-liners from Binet, and were deliberately left on their inductive
proofs. Whether to re-prove them is a judgement call about which proof a reader wants; the
docstrings do not yet cross-reference Binet.

### 2b. The symmetry the library proves but never uses

`Simplex/Ordered.existsUnique_mem_orderedSimplex` says the sorted simplex is a fundamental
domain for coordinate permutation. `Simplex/Gibbs.freeEnergy T i₀ x = -log (x i₀) + T * ∑ x i *
log (x i)` — the entropy term is permutation-invariant, the barrier term is not.

That asymmetry is the interesting content, not an obstacle: state that the entropy is invariant,
that the barrier picks a coordinate, and that a permutation-invariant statement need only be
proved on the ordered simplex. Right now the reduction exists and nothing uses it.

### 2c. Item 3, measured — and what the duplication actually was

**The claim was false as stated.** `grep -c '!!\[' ` over the four named modules:
`GoldenRatio/Characterisations.lean` 4, `Geometry/Helix.lean` 5, `NumberTheory/Jacobsthal.lean`
**0**, `NumberTheory/Pell.lean` **0**. Two modules build a 2×2 companion matrix, not four;
Jacobsthal and Pell build no matrix at all. (`Simplex/Hessian.lean` has one, unrelated — it is
the Hessian of a free energy.)

The duplication was real but was **not** in the matrices. It was in the *identities*, and it
was worse than the claim: `lucas_mul_fib` and `jacobsthal_mul_jacobsthalCompanion` are the same
theorem; `lucas_sq_sub_five_mul_fib_sq` and `pellHalfCompanion_sq_sub_two_mul_sq` are the same
theorem; four separate closed forms are one theorem at four pairs of roots. That is what
`NumberTheory/LucasSequence.lean` now proves once, and `LucasSequenceCases.lean` records the
identifications. `ROADMAP.md` §1.1 is the summary.

The lesson is the file's own §0 read the other way round: the previous session inferred a shared
object *from declaration names*, guessed the wrong object, and happened to be pointing at a real
duplication anyway. Reading names found something; it did not find what it named.

---

## 3. Expanding into new mathematics

The standing goal is a library that spans mathematics, not just the salvage from one corpus.
Everything above is finishing the salvage. **New material is welcome and wanted.**

When adding a new area:

- **Check Mathlib first, and say what you searched.** The rule this project has converged on: a
  claim that "Mathlib does not have X" must rest on a search you actually ran and record the
  terms. Three modules were declined on these grounds and one axiom survives *because* the
  search is documented and reproducible.
- **Research is in scope.** If a domain needs background — a definition convention, which of
  several equivalent formulations is standard, what the standard name for a result is — go and
  find out rather than guessing. Getting the *name* right is part of the deliverable (§5).
- **Prefer results with a statement someone would want to cite.** The corpus this library came
  from was full of true statements nobody could use. `Order/Superadditive.lean` is the shape to
  aim for: a definition, five theorems, and a worked witness that the hypothesis class is
  inhabited so nothing is vacuously about an empty class. (Corrected 2026-09-23, order G-5
  round 19: this said "four"; the module declares five theorems, eight theorem constants with
  its three `_proof_1_1` auxiliaries — round 16, finding 5.)
- **A module earns its place if it shortens something or states something new.** `[retired name]` was
  declined because porting it would have added names, not results. That is a valid outcome and
  should be recorded in a fragment under `records/rounds/` with the reason.

Directions that would extend the library's reach rather than deepen one corner — pick by what
you can do well, not by this list's order:

- **Order/lattice theory** — `Order/` has two isolated modules (`Superadditive`, `Tolerance`).
  `Tolerance` is a pseudometric with the codomain abstracted; the obvious next step is a
  triangle inequality and the resulting equivalence relation, which the module explicitly does
  *not* assume.
- **Combinatorics** — the sequence modules (`Pell`, `Jacobsthal`, `Tribonacci`, `Catalan`,
  `NacciTrace`) are all linear recurrences. Generating functions, or the general theory of
  integer linear recurrences, would unify them the way `FactorialPart` unified the factorisation.
- **Number theory** — `MersenneOrder` is the deepest thing here. Rank of apparition, cyclotomic
  polynomials and Zsigmondy (done for `aⁿ − 1`, round 22; spelling corrected 2026-09-24) are
  the natural continuations, and the compositum-discriminant
  module is a doorway into algebraic number theory.
- **Anything genuinely new.** Analysis, topology, category theory, probability — the library has
  none of these and no reason not to.

**Next in information theory, from order 0923 (2026-09-23).** `InformationTheory/` exists now
(`ROADMAP.md` §2.8). No statement was left unproved in round 18. What comes next, in order:

- **The bridge to Mathlib's `klDiv`** — done (dated 2026-10-09, order LEAN-21, item 39 of the
  library plan; this entry corrected in order LEAN-22):
  `(InformationTheory.klDiv μ_p μ_q).toReal = relEntropy p q + ∑ i, q i - ∑ i, p i` for `p, q ≥ 0`
  with `q i = 0 → p i = 0`, where `μ_p` is the finite measure with weights `p`
  (`ClassicalLean.Probability.RelativeEntropyGrowth.toReal_klDiv_vecMeasure`). Mathlib's `klDiv`
  carries the mass term `ν.real univ - μ.real univ`, so the version without it is false off equal
  totals (`p = (1)`, `q = (2)`), and without support `klDiv = ∞`. With the bridge, the library's
  data-processing inequality follows again from Mathlib's `klDiv_comp_right_le`
  (`relEntropy_vecMul_le_of_klDiv`), since a channel preserves both totals.
- **Conditional entropy and the chain rule** `H(X, Y) = H(X) + H(Y | X)`.
- **Data processing for mutual information** along a Markov chain `X → Y → Z` — which would also
  give `mutualInfo` its first user outside its own module.

**Dated 2026-09-23 (order G-5, round 19) — the list above is declined for now.** Conditional
entropy, the chain rule, Markov data processing, Pinsker and Fano exist, in random-variable
form, in an Apache-2.0 library this one does not depend on (`github.com/FujiHaruka/
information-theory`; `ROADMAP.md` §2.8 has claude-ai's measurements). The finite-vector forms
would still be new here, so this is a ranking decision on the prior-art ground Dustin asked
claude-ai to apply, not a finding that they add nothing; his veto is open. The three finite
modules stay as they are; `mutualInfo` keeps no consumer (round 19 says why); the `klDiv`
bridge stays listed as the first step if the finite layer is ever offered to Mathlib. (Dated
2026-10-09, order LEAN-22: the bridge is now proved, order LEAN-21; the chain rule, Pinsker and
Fano were proved in orders LEAN-18 and LEAN-21, under MATH-PLAN-library's decision 1, which
recommended lifting the decline above.)

**Next after the toolchain move (order 0923, round 17), smaller items first:**

- Swap `InformationTheory/Channel.lean`'s private `vecMul_eq_sum` for Mathlib's
  `Matrix.vecMul_apply_eq_sum` (`Data/Matrix/Mul.lean:726`, present at v4.34.0, absent at the old
  pin). **Done 2026-09-23 (order G-5, round 19):** the statements were identical, so each of the
  five uses now names `Matrix.vecMul_apply_eq_sum` in full (Mathlib's different
  `Matrix.vecMul_eq_sum`, `v ᵥ* M = ∑ i, v i • M i`, makes the bare name a trap) and the
  private theorem is gone: raw 1072 → 1071, filtered 725 → 724, no other type changed.
- Remove the ten modules' `backward.isDefEq.respectTransparency false` lines where they are no
  longer needed: `ring` works in `PowerSeries R` without them at v4.34.0 (§1). **Done
  2026-09-23 (order G-5, round 19):** all fifteen settings removed (§1). Left for later, one
  line: `finrank_K1_eq`'s `set_option maxHeartbeats 400000 in` is no longer needed at v4.34.0
  (`#count_heartbeats` 91057, under the default 200000; the module comment has the figures).
- `linter.style.header` is off library-wide until Dustin chooses a licence for the copyright
  block it asks for. **Superseded 2026-09-23 (order G-5, round 19):** he chose Apache-2.0; the
  linter is on and every module carries the header (§1).
- `mem_closedSimplex` is an `Iff.rfl` unfolding with no user yet, kept on `mem_openSimplex`'s
  precedent; Dustin's call whether it stays. **Settled 2026-09-23 (order G-5 §2):** it stays, by
  `mem_openSimplex`'s precedent — claude-ai's decision on his delegation, his veto open (§6).

**Statistics, from order G-5 (2026-09-23).** `Statistics/GaussMarkov.lean` exists now
(`ROADMAP.md` §2.9). No statement was left unproved in round 20. Not started, and listed here as
the order asks:

- **The variance reading with `ProbabilityTheory.covarianceBilin`** — order G-5's optional second
  module. It would restate `dotProduct_inv_mulVec_le` as a statement about the variance of
  `a ⬝ᵥ β̂` for a random noise vector with covariance `σ² • 1`, through Mathlib's measure-theoretic
  covariance; it adds 126 modules to the import closure and does not reach
  `Mathlib.Probability.Kernel.Invariance` (the order's reviewer's count, reproduced read-only).
  Read `covarianceBilin`'s definition before stating anything (§6 rule 2).
- **Generalised least squares** (`Cov ε = σ² • V`), and **Cochran's theorem**; both build on
  `leastSquares`, which has no consumer outside its own module until one of them lands.
  **Corrected 2026-09-24 UTC (order G-6, round 21):** `leastSquares` has its first outside
  consumer already: `Statistics/CramerRao`'s equality case `weightedCov_eq_inv_secondMoment_iff`
  unfolds it (through `self_mul_transpose_eq_inv_iff`).

**What next — re-ranked at order G-10's close (2026-09-25 UTC).** G-9's ranking below is kept as
written; its fourth item is done (round 29: Wolstenholme's theorem, so the library proves Q1724049's
statement) and its third item's first half is done (round 30: the Frisch–Waugh–Lovell theorem). In
order:

1. **Carmichael's theorem** (Q3889376): `F_n` has a primitive prime divisor exactly for
   `n ∉ {1, 2, 6, 12}`. Now measured cell by cell (order G-10 §0 row 16): the elementary shape — the
   Fibonacci cyclotomic numbers `c_n = ∏_{d ∣ n} F_d ^ μ(n/d)` by Möbius inversion, the key lemma
   that a prime `p ∤ n` dividing `c_n` is primitive for `F_n`, the `3 · 2^k` anomaly at `p = 2`
   (cells to `n = 150`), the Binet size bound (measured `15 ≤ n ≤ 400`, to be proved in general),
   and the finite check `n ≤ 14`. Proposed as order G-11's work once its Lean-side needs are
   measured (Mathlib's Möbius inversion for products, a Binet lower bound on `Nat.fib`, the rank of
   apparition and `α(p) ≤ p + 1` from round 24, and `decide` on `F_n` for `n ≤ 14`) — one order's
   J2 and J3 together, with a new module.
2. **Majorization** (P7; Mathlib's own TODO, `Analysis/Convex/Birkhoff.lean:29–30`), which no cycle
   has measured. Offering it to Mathlib would be Dustin's decision.
3. **Cochran's theorem** (Q599876), the second half of the third item, over J3's
   `Statistics/FrischWaughLovell` module and `GaussMarkov`'s `leastSquares`.
4. **Max-flow min-cut, then Menger** (Q608294, Q928813; `ROADMAP.md` §2.10), with
   `Applied/Integrity` folded in.
5. **Mathlib's wanted list** (§2.12).

Also open, not ranked: the two islands (`NumberTheory/CompositumDiscriminant`, `Order/Tolerance`;
`ROADMAP.md` §1.15), the other pairs of order G-10 §0 row 6, the `ExpChar` form, a `lucasV` analogue
of the rank of apparition, and order G-10 §0 row 9's weaker Frisch–Waugh–Lovell hypothesis (`IsUnit
(X₁ᵀ X₁).det` alone; measured, not proved — this order did not take it).

**What next — re-ranked at order G-9's close (2026-09-25 UTC).** G-8's ranking below is kept as
written. Its fourth item is done (round 27: Lamé's theorem, so the library proves Q230848's
statement), and so are two of its open items (round 28: `V_{p^k} = P ^ (p ^ k)` in characteristic
`p`, with `V (p n)`, `U (p n)`, `U (p ^ k)` and the `dickson` form; round 27: `land.sh` under
`LC_ALL=C`). In order:

1. **Carmichael's theorem** (Q3889376): `F_n` has a primitive prime divisor exactly for
   `n ∉ {1, 2, 6, 12}`. Order G-8 §0 row 13 measured what the cyclotomic route needs (a lower bound
   on the Fibonacci cyclotomic numbers that the triangle inequality does not give; no `Φₙ(−X)`
   identity or reversal lemma in Mathlib; round 22's key lemma fails at `n = 6, 12`; `p = 2` and
   `p = 5` apart). The elementary route (Yabuta 2001, through the rank of apparition and the bound
   `α(p) ≤ p + 1`, which round 24 has) is measured cell by cell by claude-ai before any order
   proposes the theorem (order G-9 §0 row 16).
2. **Majorization** (P7; Mathlib's own TODO, `Analysis/Convex/Birkhoff.lean:29–30`). Offering it
   to Mathlib would be Dustin's decision.
3. **The Frisch–Waugh–Lovell theorem, then Cochran's theorem** (Q1059151, Q599876), as matrix
   algebra over round 20's `leastSquares`. **First half done 2026-09-25 UTC (order G-10, J3, round
   30):** the Frisch–Waugh–Lovell theorem, `Statistics/FrischWaughLovell.lean` (`residualMaker` the
   annihilator `M₁`, (S1)–(S5), the vector and matrix forms (F1)–(F4), and the witness that the
   invertibility hypothesis cannot be dropped), over `GaussMarkov`'s `leastSquares` (`GaussMarkov`
   now `usedBy=2`). Cochran's theorem, the second half, is not in this order and stays ranked.
4. **Wolstenholme's theorem** (Q1724049): `C(2p − 1, p − 1) ≡ 1 (mod p³)` for primes `p ≥ 5`;
   Mathlib has no harmonic sum modulo a prime (order G-9 §0 row 12: the one hit is a docstring,
   and `NumberTheory/Harmonic/` is real-analytic), so the route through `H_{p−1} ≡ 0 (mod p²)` is
   all new. (Corrected 2026-09-25 UTC, order G-9's Close check, round 28 addendum item 13:
   `NumberTheory/Harmonic/` is not real-analytic — it defines the rational `harmonic`
   (`Harmonic/Defs.lean:23`) and proves `padicValRat_two_harmonic` and `harmonic_not_int`
   (`Harmonic/Int.lean:30, 52`); it has no congruence modulo a prime, so the congruence is new and
   can start from Mathlib's `harmonic`.) **Done 2026-09-25 UTC (order G-10, J2, round 29):**
   `NumberTheory/Wolstenholme.lean`, both classical forms (`choose_two_mul_sub_one_modEq_one`,
   `two_le_padicValRat_harmonic`) and the central and Catalan corollaries, for every prime `p ≥ 5`;
   the library now proves Q1724049's statement, the first congruence modulo a prime power here, and
   the island `Catalan` gets its first user.
5. **Max-flow min-cut, then Menger** (Q608294, Q928813; `ROADMAP.md` §2.10), with
   `Applied/Integrity` folded in.
6. **Mathlib's wanted list** (§2.12).

Also open, not ranked: the three islands (`NumberTheory/Catalan`,
`NumberTheory/CompositumDiscriminant`, `Order/Tolerance`; `ROADMAP.md` §1.15; retiring a module is
Dustin's decision); the other pairs of `pairs.py` (91 at `1e63d5b`: pairs of modules with no edge
between them that share a rare constant, `S3Quaternion ~ SU2SO3` first); the `ExpChar` form of the
characteristic-`p` results; and a `lucasV` analogue of the rank of apparition.

**What next — re-ranked at order G-8's close (2026-09-24 UTC).** G-7's ranking below is kept as
written. Its first item is done (round 25: Zsigmondy's theorem for `aⁿ − bⁿ` with the sum clause,
so the library proves `docs/1000.yaml`'s Q8074796 in full), and so are two of its open items
(round 26: `V_p = P ^ p` in characteristic `p`; round 25: the type dump up to proof irrelevance).
In order:

1. **Carmichael's theorem** (Q3889376): `F_n` has a primitive prime divisor exactly for
   `n ∉ {1, 2, 6, 12}` (checked from the definition for `n ≤ 400`). Order G-8 §0 row 13 measured
   what it needs: the Fibonacci cyclotomic numbers `c_n = ∏_{d ∣ n} F_d ^ μ(n / d)` with a lower
   bound (`c_n ≥ 0.618 · φ ^ φ(n)` held for `3 ≤ n ≤ 300`; the triangle inequality gives only
   `c_n ≥ 1`); round 22's key lemma does not carry over (`c_6 = 4` and `c_12 = 6` exceed
   `P(n) = 3`, and `2` divides both `n` and `c_n`); Mathlib has no identity for `Φₙ(−X)` and no
   reversal lemma; `p = 2` and `p = 5` need their own treatment. Round 25's
   `exists_prime_lucasApparition_add_mul_eq_iff` is the case of integer roots; Fibonacci's roots
   are conjugate quadratic irrationals.
2. **Majorization** (P7; Mathlib's own TODO, `Analysis/Convex/Birkhoff.lean:29–30`). Offering it
   to Mathlib would be Dustin's decision.
3. **The Frisch–Waugh–Lovell theorem, then Cochran's theorem** (Q1059151, Q599876), as matrix
   algebra over round 20's `leastSquares`.
4. **Lamé's theorem** (Q230848), the Euclidean algorithm's step bound, through the Fibonacci
   numbers the library already has.
5. **Wolstenholme's theorem** (Q1724049, new; order G-8 §0 row 15): `C(2p − 1, p − 1) ≡ 1
   (mod p³)` for primes `p ≥ 5`; title only in `docs/1000.yaml`, and `wolstenholme` has 0 hits in
   Mathlib; claude-ai's cells hold for the primes `5 ≤ p < 400` and for no composite `n < 2000`.
6. **Max-flow min-cut, then Menger** (Q608294, Q928813; `ROADMAP.md` §2.10), with
   `Applied/Integrity` folded in.
7. **Mathlib's wanted list** (§2.12).

Also open, not ranked: the three remaining islands (`NumberTheory/Catalan`,
`NumberTheory/CompositumDiscriminant`, `Order/Tolerance`; `ROADMAP.md` §1.15; retiring a module is
Dustin's decision) and the other pairs of order G-8 §0 row 6 (`pairs.py`: 87 pairs of modules with
no edge between them that share a rare constant, at `87653a4`); `V_{p^k} = P ^ (p ^ k)` and the
`ExpChar` form (the dated paragraph under G-7's ranking); a `lucasV` analogue of the rank of
apparition; and running `land.sh`'s path comparison under `LC_ALL=C` (round 26's Close).

**Dated 2026-09-25 UTC (order G-9, rounds 27 and 28):** item 4 above is done: Lamé's theorem, in
the new module `NumberTheory/EuclidSteps` (`ROADMAP.md` §2.13) — the step count of the Euclidean
algorithm, the Fibonacci bounds with their attaining pairs, and at most five steps per decimal digit
of the second argument, so the library proves the statement of `docs/1000.yaml`'s Q230848 (listing
it there is Dustin's decision). Two of the open items are done: `V_{p^k} = P ^ (p ^ k)` in
characteristic `p` (`lucasV_prime_pow_eq_pow`), with `V (p n) = V n ^ p`, `U (p n)`, `U (p ^ k)`, the
`dickson` form at prime powers and the characteristic-2 identities (round 28; `ROADMAP.md` §2.1);
and `land.sh`'s path comparison, which now runs under `LC_ALL=C` and reads `comm`'s exit status
(round 27). Still open: the `ExpChar` form, and a `lucasV` analogue of the rank of apparition.

**What next — re-ranked at order G-7's close (2026-09-24 UTC).** G-6's ranking below is kept as
written; its first item is done (round 24: the law of apparition, the bound `α(p) ∣ p − (D/p)`
for odd `p ∤ Q`, and the Fibonacci case), and round 23 bridged two of the six islands. In order:

1. **Zsigmondy's theorem for `aⁿ − bⁿ`**, coprime `a > b > 0` (`ROADMAP.md` §2.5): it completes
   `docs/1000.yaml`'s Q8074796, whose statement is for `aⁿ − bⁿ`; the library proves `b = 1`
   (round 22). Both prior-art proofs state the two-variable form; their route is the one round
   22 used, and it is credited, not adapted.
2. **Carmichael's theorem** (Q3889376): every Fibonacci number beyond `F₁₂` has a primitive prime
   divisor. In reach now that the law of apparition is proved (round 24), with round 22's
   primitive-divisor machinery.
3. **Majorization** (P7; Mathlib's own TODO, `Analysis/Convex/Birkhoff.lean:29–30`). Offering it
   to Mathlib would be Dustin's decision.
4. **The Frisch–Waugh–Lovell theorem, then Cochran's theorem** (Q1059151, Q599876), as matrix
   algebra over round 20's `leastSquares`.
5. **Lamé's theorem** (Q230848), the Euclidean algorithm's step bound, through the Fibonacci
   numbers the library already has.
6. **Max-flow min-cut, then Menger** (Q608294, Q928813; `ROADMAP.md` §2.10), with
   `Applied/Integrity` folded in.
7. **Mathlib's wanted list** (§2.12).

Also open, not ranked: the four remaining islands (`ROADMAP.md` §1.15; recorded, not bridged;
retiring a module is Dustin's decision); `lucasV P Q p = P ^ p` in any ring of characteristic
`p`, which would extend Mathlib's `dickson_one_one_charP` from `Q = 1` to every `Q` (the J3
statement review's suggestion, round 24); and a tooling item from round 23's step 4 —
`g5_typediff.py` reports a record as changed when only a `Prop`-valued instance argument's proof
term moved (an import widened instance search), so it cannot tell a changed statement from a
definitionally equal one; comparing such arguments up to proof irrelevance would resolve it.

**Dated 2026-09-24 UTC (order G-8, rounds 25 and 26):** item 1 above is done: Zsigmondy's theorem
for `aⁿ − bⁿ`, with the sum clause and the ranks of apparition in `U(a + b, ab)`, in the new module
`NumberTheory/ZsigmondyPowSubPow` (`ROADMAP.md` §2.5). Two of the open items are done:
`lucasV P Q p = P ^ p` in any commutative ring of prime characteristic `p` (`lucasV_prime_eq_pow`,
with `dickson_one_eq_X_pow_of_charP`, `dickson 1 a p = X ^ p` for every `a`), and the tooling item
(`TypeDumpPI.lean` with `g8_typediff.py`, rule 25). Offering the `dickson` form to Mathlib is
Dustin's decision. For that offer, the J3 statement review recorded that Mathlib puts the `ExpChar`
form of such results first (`add_pow_expChar`, `Algebra/CharP/Lemmas.lean:162`, with the `CharP`
form derived from it at `:176`; 100 lines with an `[ExpChar …]` binder against 26 with `CharP` and
a `Fact`-prime), so a Mathlib reviewer is likely to ask for it; the library's binders are
`dickson_one_one_charP`'s. Open, and not required by order G-8: `V_{p^k} = P ^ (p ^ k)` in
characteristic `p` (the statement review's cell D), whose route needs a composition law Mathlib has
only at `a = 1` (`dickson_one_one_mul`, `Dickson.lean:183`) or the iterated Frobenius in the matrix
ring. Three islands remain (`ROADMAP.md` §1.15): `AlgebraicGeneratingFunction` now uses
`RecurrenceGeneratingFunction`.

**What next — re-ranked at order G-6's close (2026-09-24 UTC).** Order G-5's ranking below is
kept as written; its first item is done (round 22: Zsigmondy for `aⁿ − 1`, base `2` included,
with no new analytic inequality), and G-6's patterns add two candidates (`ROADMAP.md` §1.14). In
order:

1. **The law of apparition** `α(p) ∣ p − (D/p)` for a Lucas sequence (P6): it continues
   `NumberTheory/LucasApparition` and `MersenneOrder`, which record the general bound as not
   proved, and it uses the same `orderOf`-in-`ZMod p` machinery Zsigmondy just exercised.
2. **Majorization** (P7): Mathlib's own TODO, `Analysis/Convex/Birkhoff.lean:29–30`; the library
   has the pieces (`InformationTheory/Channel`, `Simplex/Ordered`, `Simplex/Symmetry`). Offering
   it to Mathlib would be Dustin's decision.
3. **Max-flow min-cut, then Menger** (`ROADMAP.md` §2.10), with `Applied/Integrity` folded in
   (§2.11).
4. **More statistics** (§2.9): the Frisch–Waugh–Lovell theorem (`docs/1000.yaml` Q1059151, title
   only, no formalisation recorded, checked 2026-09-24), generalised least squares, and Cochran's
   theorem as matrix algebra.
5. **Mathlib's wanted list** (§2.12).

Also open and not ranked: Zsigmondy's two-variable form `aⁿ − bⁿ` for coprime `a > b > 0`
(`ROADMAP.md` §2.5, dated 2026-09-24), which both prior-art proofs state.
**Dated 2026-09-24 UTC (order G-7, J2 step 7):** two more, `docs/1000.yaml` entries with no
formalisation recorded (order G-7 §0 row 12, claude-ai's measurement at Mathlib v4.34.0):
**Carmichael's theorem** (Q3889376; it needs the law of apparition, order G-7 J3) and
**Lamé's theorem** (Q230848). The Frisch–Waugh–Lovell theorem is already item 4 above.

**What next — claude-ai's ranking in order G-5's Close, checked against what G-5 found
(2026-09-23).** Each item has a `ROADMAP.md` §2 row with its searches and counts, re-run at
v4.34.0 by this session. The ranking holds, with two changes of scope:

1. **Zsigmondy's theorem** (`ROADMAP.md` §2.5, dated update) — **first, scoped to `aⁿ − 1`**: an
   `iff` with the exact exceptional set, stated with `PrimitiveDivisor`'s `IsPrimitiveDivisor`,
   proved here. The code `docs/1000.yaml` could not find is found and is not in Mathlib:
   Bakšys's Lean 3 branch (2022, unmerged) and a Lean 4 port, mathlib4 #28895, closed unmerged
   on 2026-09-18 and never built green. The recorded blocker is stronger than needed: only
   base `a = 2` needs a new cyclotomic inequality.
2. **Max-flow min-cut, then Menger** (§2.10) — second, as ranked. 0 Mathlib hits; Mathlib has
   the cut side of edge-Menger for `SimpleGraph` (`IsEdgeReachable`), which Menger can be
   stated against. Its hard step is a path-shortening lemma for a relation on a finite type,
   which Mathlib lacks.
3. **More statistics** (§2.9, dated update) — generalised least squares first (every ingredient
   is in Mathlib; it gives `leastSquares` its first outside consumer), then Cochran's theorem
   as matrix algebra; the distributional Cochran needs a chi-squared law Mathlib lacks.
   (Corrected 2026-09-24 UTC, order G-6: the first outside consumer of `leastSquares` is
   `Statistics/CramerRao`, round 21.)
4. **`Applied/Integrity`** (§2.11) — **fold into item 2**: its one real lemma, decidable
   transitive closure of a finite relation, is item 2's path-shortening lemma; the append-only
   half is `List.foldl_append`.
5. **Mathlib's wanted list** (§2.12) — fifth: `Order.height_of_linearOrder`,
   `Order.coheight_of_linearOrder` and `ProbabilityTheory.variance_of_hasLaw_binomial` are in
   reach; the research also found a wanted statement that reads as false
   (`condVar_of_hasLaw_binomial`). Offering anything to Mathlib is Dustin's decision.

**Two more candidates, dated 2026-09-24 UTC (order G-6, J2 step 5)** — measured by claude-ai on
2026-09-23 and not proved; `ROADMAP.md` §1.14 has the measurements:

- **The law of apparition** `α(p) ∣ p − (D/p)` for a Lucas sequence (P6): 684 checks over nine
  pairs `(P, Q)`, primes below 400 not dividing `2QD`, 0 failures. `LucasApparition` records
  that the general bound is not proved; its split case `(3, 2)` is Fermat's little theorem in
  `MersenneOrder`.
- **Majorization** (P7): Mathlib's own TODO, `Analysis/Convex/Birkhoff.lean:29–30` — `x` is
  majorized by `y` if and only if `M *ᵥ y = x` for a doubly stochastic `M`. The library already
  has entropy under doubly stochastic matrices (`InformationTheory/Channel`), the sorted simplex
  (`Simplex/Ordered`) and permutation invariance (`Simplex/Symmetry`). Offering the result to
  Mathlib would be Dustin's decision.

---

## 4. The gates, and their known limits

Seven gates, in `tools/`. Each was fail-tested; if you change one, fail-test it again.

- **`AxiomGate.lean`** — enumerates every theorem constant under `ClassicalLean` and requires its
  kernel dependencies to be a subset of `{propext, Classical.choice, Quot.sound}`, plus named
  `scopedExceptions`. Written as an **allowlist** on purpose: `native_decide` emits a
  *per-declaration* axiom on v4.29 (`<thm>._native.native_decide.ax_1_1`), not the
  `Lean.ofReduceBool` older Lean used, so a denylist of known axiom names would miss it. Still so
  at v4.34.0: round 17's gate probe produced `probe_native._native.native_decide.ax_1_1`.
- **`VacuityGate.lean`** — flags a theorem when any of three tests fires, and says which
  (order VACUITY-2): the **fixed test** (conclusion is `True`; is `∃ y, y = e` with `e`
  independent of `y`; or follows from one hypothesis by applying it, opened through `⊆`, named and
  `@[irreducible]` definitions, `∧` halves and `↔` directions, with that hypothesis's premises met
  by the other hypotheses; or is an `∧`, an `↔` or another Prop structure every part of which is
  `True` or closed by one hypothesis, Dustin's ruling of 2026-10-11); the **old case 3** (the conclusion of a `∀` hypothesis matches,
  premises ignored; labelled `old case 3 only` when nothing else fired); and **rule 5**
  (`contradiction`, `linarith`, `omega`, `norm_num`, `decide` prove `False` from the written
  hypotheses, 400000 heartbeats per theorem; running out is counted on the summary line, not a
  failure). Every flag of the fixed test and rule 5 stands for a proof term checked by the kernel
  (`kernelCheck`; not every one passes `Meta.check` first); a kernel rejection, a term the
  elaborator had accepted, is KERNEL-REJECTED and fails the gate. Flagged theorems may
  pass through `tools/vacuity_reviewed.txt` (name and statement hash). Tests:
  `tools/VacuityGateTests.lean`, run by `tools/run_vacuity_tests.py`. **Stated limits** (the
  docstring of `isVacuousType`, after the cold review of VACUITY-2): a true-but-contentless
  statement such as `[retired name]` for `psi` valued in `ℕ` is *not* caught, because being
  uninformative is not a syntactic property (that exact shape was found in the wild presented as
  a named law; only review catches it); contradictions rule 5's tactics do not find, or with no
  hypothesis that is a proposition; a closed premise `decide` cannot finish makes the theorem
  UNCHECKED (fails closed) unless the old case 3 flags it; chained hypotheses and premises not
  closed by `rfl` or `decide` are caught only in a plain `∀`; a `_proof_` helper with no source
  position that some declaration uses is skipped; a conclusion glued from hypotheses is caught
  only as an `∧`, `↔` or Prop structure whose parts are each `True` or one hypothesis (a part
  needing `rfl`, `decide` or computation passes, except a definition by structural recursion
  applied to a literal or a constructor, which smart unfolding reduces and which is then read as
  `True` and flagged, `real_hyp_and_small3`, listed; a part under a binder is not opened; `∨`
  and `∃` are not caught); rule 5 reads the statement as written (`p → False` and `¬ p` are read
  differently; `∀ x ∈ [], F x` written out is flagged and listed, the same inside
  a definition is not); theorems are selected by the namespace `ClassicalLean`, not by module (5
  generated equation lemmas fall outside). Flagged on purpose: lemmas that are a projection, the
  identity or a pairing of hypotheses once definitions and instances are unfolded
  (`S ∩ T ⊆ S`, the shape of `Prod.mk_le_mk`); they stay through a list entry.
  **Dated 2026-10-13 UTC (order LEAN-27, job 0, with Dustin's rulings of 2026-10-12 and
  2026-10-13):** what counts as "computing" when a part is read as `True`. `unfoldNamed` runs
  `whnfCore` with `iota := false`, so a `match` or recursor is not reduced there. A `match` it
  leaves stuck is opened branch by branch (`matchMatcherApp?`, each alternative's parameters bound
  by `lambdaBoundedTelescope`); if every branch unfolds to `True`, the match is read as `True`,
  otherwise it stays stuck. So `P a ∧ Small2 0` passes (one branch `True`, one `False`:
  computing), and `∀ x, PairT x` with `PairT (_, _) := True` is flagged (one branch, `True`:
  nothing computed). Where the `True` reading is used, `confirmTrue` (`isDefEq` at `.all`) asks
  whether `True.intro` proves it, measured, not a general rule: yes for a match on a constructor,
  and for a match on a variable of a structure whose patterns are only the constructor with
  variable fields, which eta reduces (`PairT`); no for a variable of `ℕ`, `Bool` or another
  inductive without eta (`NatT`), and no for `Fin 2`, whose literal patterns split the natural
  number inside (`vac_unchecked_fin_true`, order VACUITY-3's ruling 1, below). Then a hypothesis
  that closes the part is tried (`vac_hyp_and_nat_true`, flagged), and failing that the theorem
  is **UNCHECKED**,
  "every case is True; kernel could not confirm the proof", which fails the gate and is never a
  pass (`vac_unchecked_nat_true`, `vac_unchecked_hyp_and_nat_true`; the runner expects UNCHECKED
  for names starting `vac_unchecked_`); a part with content still makes the glue fail first
  (`real_nat_true_and_work` passes). Measured limits, each with a test: a definition by structural
  recursion (`Small3`) is still read as `True` through `unfoldDefinition?`'s smart unfolding,
  which runs with `iota` on (strict side; `real_hyp_and_small3`, listed); a chain of all-`True`
  matches on constructors or literals costs about `kᵈ` calls, bounded by the heartbeat budget
  (worst case UNCHECKED).
  **Dated 2026-10-14 UTC (order VACUITY-3, job 2):** the gate's own stale text that the confirming
  review of `5344c16` found is corrected in `tools/VacuityGate.lean` (docstrings and comments
  only, no verdict changes): the two sentences on computed facts, the heading of the limits list,
  `KernelCheck.rejected` and `Verdict.kernelRejected` (the kernel refused a term the elaborator
  had accepted), `Verdict.unchecked` (every path that gives it), `unfoldNamed` and `confirmTrue`
  (what is confirmed, as above), and `judge` ("old case 3 only (fixed test UNCHECKED: …)" can label
  an empty theorem). The runner now compares each `vac_unchecked_` test's message with a literal
  kept in it, the gate's `unconfirmedMsg` (a different message is a MISMATCH; fail-tested), and
  its verdict column fits every verdict; it reads the message from its own verdict line, which
  prints the message `judge` returns. A new test, `vac_unchecked_fin_true` (the `Fin 2` case), was
  added by Dustin's ruling 1 of order VACUITY-3 (lane `lean/VACUITY-3-ruling-1.md`, sha256
  `f825cd36215ab62de3977030617e3c1bd580056c4a5361b9bca942b977ca4860`). **The tests are now 89
  verdicts, 47 flagged, 3 UNCHECKED as expected, 0 mismatches.**
  **Stated limit, kept:** a **recursive** all-`True` predicate (`NatT2 | 0 => True | n + 1 =>
  NatT2 n`) is not read as `True`, so `∀ n, NatT2 n` passes silently (a gap older than LEAN-27;
  catching it means induction, which needs its own ruling). Measured at order VACUITY-3 by the
  report tool's section C (below): 33 Prop-valued definitions under `ClassicalLean`, **0 of them
  recursive**, so no theorem of the library can fall into this gap today.
  **Left for a later gate order** (cold review of VACUITY-3's job 2, finding 5(c), older than that
  job): the gate's FAIL text lists the cases but omits case 5 (a glued conclusion), and does not
  say what UNCHECKED or KERNEL-REJECTED mean, so a FAIL caused by an UNCHECKED theorem explains
  nothing to the reader. **Done (dated 2026-10-26 UTC, order VACUITY-4, Goal item 7):** the FAIL
  text now names case 5 and says in one sentence each what UNCHECKED and KERNEL-REJECTED mean (the
  vacuity tests' 89 verdicts and the gate's code, outside comments and strings, unchanged); and the
  report tool's whole-library command, which had no outer budget, has `maxHeartbeats 2000000`, as
  the vacuity gate has (its summary lines unchanged).
- **`UninformativeReport.lean`** (order VACUITY-3, item 90) — **a report, not a gate and not a
  check**: nothing it lists fails anything; only its own self-test and count check give rc 1. It
  narrows the gate's first stated limit (a true statement that carries no information) for a
  human reader. Section A: every written theorem under `ClassicalLean` with a hypothesis whose
  conclusion closes with the hypotheses cleared, by `simp`, `norm_num` or `positivity`
  (`DEPENDENT` when the conclusion needs a hypothesis). Section B: the theorems with no hypothesis
  that close the same way. Each `CLOSES` line names the library constants its proof uses, and says
  `USES-ITSELF` when the proof uses the theorem; the theorem itself is erased from the simp set
  first. Section C: Prop-valued definitions defined by recursion (the `NatT2` gap above). Run from
  the repository root: `lake env lean tools/UninformativeReport.lean` (about 40 s, 4.2 GB). At
  order VACUITY-3: 1785 written theorems; A 1027 (0 close, 988 open, 39 dependent); B 758 (16
  close: 15 by `simp`, 1 by `positivity`); C 33 Prop-valued, 0 recursive. A `CLOSES` line is a
  statement for a human to read, not a finding (a value lemma that `simp` closes is still a useful
  theorem). Limits, in its docstring: binders are read as written; a proposition in an instance
  binder stays in the context; only three tactics are tried; `USES-ITSELF` cannot see an `rfl`
  simp lemma (21 such value lemmas in section B close only because they were erased from the
  simp set first); section C reads one level below a definition. **Standing rule (round 58):**
  every later gate order re-runs it and reports its summary lines.
- **Satisfiability witnesses** (order VACUITY-3, item 89). For a theorem with hypotheses, a
  witness is an `example` at the end of the theorem's module that applies the theorem itself at
  concrete arguments, with a proof of each hypothesis, so that Lean checks that the theorem's own
  hypotheses can all hold at once. The form (rule 2): `example := Full.name (x := …) h₁ h₂ …`,
  every chosen argument given by name, optional `open … in` lines of their own (it relies on no
  other `open` than its module's top-level ones), the docstring "The hypotheses of `name` hold
  together: …", and no `sorry`, `native_decide` or `set_option`. **Standing rule (round 58):** a
  satisfiability example applies the theorem itself, not an `∃` restatement. Not degenerate
  (rule 3): no hypothesis is met only because something is empty, zero, a single point or a sum
  over nothing, through one of Lean's junk values, or at a boundary where a constant of the
  theorem vanishes; families and matrices have size at least 2 unless the theorem fixes it. The
  83 targets (items 1 to 71) are the rows of the lane's `lean/VACUITY-3-targets.tsv`; each witness
  sits after its module's last line, and each group of at most 8 rows had a cold review and a
  confirming pass. **Not witnessed, 5 rows:** `variance_average_eq_of_steady` and
  `variance_average_le_of_steady` (`Probability/EffectiveSampleSize`) and
  `tendsto_sup_abs_empiricalCDF_sub` (`Probability/GlivenkoCantelli`) need an infinite family of
  independent random variables, which nothing in their modules' imports builds
  (`Measure.infinitePi` is outside them; a countable product of Bernoulli laws on `Finset ℕ`, or
  binary digits under Lebesgue measure, would do, as a longer proof); `covariance_eq_sum` and
  `isSolution_autocovariance` (`Probability/YuleWalker`) need a stationary process with noise,
  which a finite space cannot carry: a stationary AR(1) model on `ℕ` with weights `2^-(n+1)` meets
  every hypothesis of both (checked outside the library), but rule 3 asks for an AR(2) model, and
  written without helper declarations each witness would run to about 350 lines. Left for a
  ruling.
  **Dated 2026-10-15 UTC (order LEAN-29, rule 2; claude-ai's ruling, Dustin's veto open):** order
  VACUITY-3's ruling 3 (lane `lean/VACUITY-3-ruling-3.md`) gave rule 3 two more cases, and order
  LEAN-29 files them here in place of the next gate order, because it is the first order to write
  witnesses under them: no hypothesis may be met only because a function is identically `0` past
  some point, and no kernel or observation may fail to depend on the parameter it is about. Rule
  2's form stays one inline block with no helper declarations (ruling 3, item 2), and its
  forbidden words are `sorry`, `admit`, `native_decide`, `implemented_by`, `axiom` and
  `set_option`. The next gate order keeps only their use on the older rows 7, 8 and 70. Order
  LEAN-29's six witnesses (items 91, 92 twice, 94 twice and 95) were written and reviewed under
  them.
  **Dated 2026-10-15 UTC (order LEAN-30, job 3):** "an optional `open … in` line of its own"
  above now reads "optional `open … in` lines of their own", as claude-ai's push review of order
  LEAN-29 asked (lane `lean/LEAN-29-ruling-2.md`, note 2): order VACUITY-3's witnesses in
  `49bcd41` and LEAN-29's item 91 witness stand behind two such lines and passed their reviews.
  Order LEAN-30's seven witnesses (items 96, 97, 98, 99 twice and 100 twice) were written before
  this change, under the earlier wording (item 99's confirming pass returned just after it); each
  has at most one `open … in` line, so it meets both.
  **Dated 2026-10-21 UTC (order LEAN-33):** rows 9 and 10 (`variance_average_eq_of_steady`,
  `variance_average_le_of_steady`) and row 67 (`tendsto_sup_abs_empiricalCDF_sub`), listed above as
  not witnessed, are now witnessed, with Mathlib's `Measure.infinitePi`, which their modules'
  imports reach since orders LEAN-31 and LEAN-32: a steady first-order recursion driven by
  independent Gaussian noises on `ℕ → ℝ` (rows 9 and 10) and fair coins on `ℕ → Bool` (row 67); so
  2 rows remain not witnessed, the two of `Probability/YuleWalker`. Rows 7 and 8 are re-witnessed
  with two genuine fair coins and `N = 2` (order VACUITY-3's ruling 1), and their blocks no longer
  use the older rows' exception for the six forbidden words.
  **Dated 2026-10-21 UTC (order LEAN-34):** row 70 (`iSup_bayesRisk_eq_minimaxRisk_of_finite`) is
  re-witnessed by this order with a kernel that depends on the parameter, `P θ = dirac 0 + dirac θ`
  (finite, not Markov), as VACUITY-3's ruling 1 asked; the hand-worked value is removed from its
  docstring. With LEAN-33's rows 7 and 8, no row uses the older rows' forbidden-word exception any
  more.
  **Dated 2026-10-26 UTC (order VACUITY-4): rule 3's case of the moving process.** A witness of a
  theorem about a process `X` up to a time `n` (the process the conclusion is about; for a stopped
  process, the underlying process and the stopping time together) makes `X` move at every step before
  `n`: for each `k < n`, `X (k + 1) ≠ X k` with positive probability, or, for a deterministic
  sequence, `X (k + 1) ≠ X k`; and `n ≥ 1` (at least one step). For a stopped process, `τ ≥ n` has
  positive probability. Where the theorem's hypotheses force `X` to stop or to pause (an absorbing
  state, a bounded stopping time, a sequence they make constant from some point), the witness stops or
  pauses it no earlier than they force, and its docstring says so. For a theorem with no horizon (a
  limit, or a statement for every `n`), a witness whose process is constant from some time on is
  degenerate unless the hypotheses force it.
  **Dated 2026-10-27 UTC (order VACUITY-5):** the two YuleWalker rows listed above as not
  witnessed, `covariance_eq_sum` and `isSolution_autocovariance`, and the third theorem of the
  group, `exists_poly_mk_autocovariance_eq`, are now witnessed by VACUITY-5, with Mathlib's
  `Measure.infinitePi`: an autoregression of order 2 (`a = (1/2, 1/4)`) driven by independent
  Gaussian noises of variances `48/25, 16/15, 1, 1, …`, covariance-stationary from time `0`
  (`γ 0, γ 1, γ 2 = 48/25, 32/25, 28/25`), moving at every time; each witness is one inline block of
  about 250 lines, with no helper declaration. By this section's count, no row of the 83 remains
  not witnessed.
- **`witness_gate.py`** (order VACUITY-4) — reads every `example` block of the library in place.
  A witness-form block (`example :=` at column 0) with the docstring "The hypotheses of `NAME` hold
  together" is turned, in a copy outside the repository, into a definition where it stood, and a
  check inserted after the imports reports what Lean knows of it: `BROKEN` (an error in it, or an
  axiom outside the kernel trio, so `sorry` and `native_decide` are caught), `WRONG-NAME` (its head
  is not the theorem `NAME` names, or not a theorem of the module), `PARTIAL` (a proposition binder
  is left, the value is a function, or the theorem is applied to fewer arguments than its binders
  before the colon, as Lean counts them), else `OK`, whose line prints the head and both counts.
  Other blocks: `NO-DOCSTRING`, `TYPED-CLAIM` (a typed example whose docstring claims a witness;
  fails), `TYPED`, `NOT-A-BLOCK`, `UNREAD` (fails), `LISTED` and `LISTED-FAULT` (entries of
  `tools/witness_reviewed.txt`, matched by the block's hash and a fingerprint of what Lean reports,
  so a changed block or theorem goes stale); `COPY-ERROR` for a module whose copy or listing does
  not match the build, or that the driver refuses (fails), and three failures counted apart,
  `STALE-LISTING`, `RANGE-MISMATCH` and `DOC-MISMATCH`. A listing driver, `tools/WitnessListing.lean`, runs
  Lean's frontend over every module: it lists the `example` keywords Lean parses (the gate's own
  list must agree), reads `run_cmd`'s scope at each block, counts each theorem's binders, and checks
  every command before Lean elaborates it (command kinds and attributes by allowlists taken from the
  library's census of 2026-10-26, kinds that run code by a list found by asking Lean, and the
  `native` configuration item), then refuses the constants it added that use Lean's own machinery;
  a module that needs a kind or attribute off the lists needs a ruling first. Run
  `python3 -I tools/witness_gate.py` from the repository root (whole library about 27 minutes on
  DSMain, one Lean process at a time); its tests are
  `python3 -I tools/witness_gate_tests.py` (119 fixtures). **Stated limits** (its docstring has them
  all): a hypothesis hidden behind a definition that reducible unfolding does not open passes as
  `OK`; a theorem whose conclusion itself opens with a hypothesis binder gives a false `PARTIAL`
  (listed with its reason); a process that stops moving inside the horizon is not seen (the case
  above is met by review); a theorem whose hypotheses are bundled in a data argument passes when the
  witness supplies nothing real inside it; a default of `optParam` or `autoParam` counts as
  supplied; typed examples are read, not elaborated; the code that Lean's and Mathlib's own
  elaborators run, options included, is not the module's and is not checked; and (review a4c,
  ruling 6 of order VACUITY-4) a module's own pure code can be compiled and run during
  elaboration, inside a tactic branch the elaborator then discards (for example a
  `(config := ...)` value or `Lean.reduceBool` under `first`), and the gate does not see it. A
  witness that rests on such a run is still caught, by the checked copy's axiom check. Whether
  such a run can do IO was tried once and not reproduced; it is not excluded. **Standing rule:** it
  and its tests run as job 5a's gates in this order and every later one.
- **`check_sorry.py`** — text-level, so it sees modules nobody wired into the aggregator. Scoped
  to `ClassicalLean/`; skips `.lake/` and `tools/`, and the reason is written in the file
  (it does not parse string literals, and the gates quote the words they detect).
- **`banned_vocab_scan.py`** — 31 retired terms plus 8 provenance patterns, over code *and*
  prose. An audit-marker allowlist let the old retirement list name what it retired
  without tripping.
  **Dated 2026-09-23 (order G-5, round 19):** its first live `EXCEPTIONS` entry permits the
  retired corpus's eponym on exactly two lines, the licence header's copyright line and its
  Authors line (case-exact, whole line, ASCII year `20[0-9][0-9]`), and nowhere else. Fail-tested
  before it landed: without it the header gives 2 hits; with it a scratch line, an Authors line
  with trailing text and a lowercase Authors line each still fail, and the header alone passes.
  The runs are in the commit that added it.
  **Dated 2026-09-24 UTC (order G-6, J2 step 1):** the Authors alternative is now
  `Authors: Dustin [surname], Claude \(Anthropic\)`, still case-exact and whole-line. Fail-tested in
  place on `NumberTheory/Catalan.lean` before it landed: the new header passes; the old Authors
  line, the new line in lower case, the new line followed by `, X`, and a scratch line naming the
  eponym each fail with one hit. The runs are in the commit that changed it.
  **Dated 2026-09-24 UTC (order G-7, J2 step V, approved by Dustin):** the audit-marker
  allowlist is removed (the scanner reads only `.lean` files, so it never saw the retirement list;
  inside its scope it only hid lines, four at removal, none with a banned term);
  `ClassicalLean.lean` is scanned too; an `EXCEPTIONS` entry forgives only its own term and
  only a hit inside its context (`finditer`, span containment); `(r"[retired term]",
  r"unconscious statistician")` is a second entry. Fail-tested before and after, ten tests,
  both runs in the commit that changed it (round 23).
- **`compile_rules.py`** (order RULES-1) — the rules gate: it validates the rule registry
  `records/rules.toml` against the registry at the base commit (no rule number disappears, a changed
  rule needs a change note, the budget of self-applied rules does not rise without Dustin's row),
  and checks that §6's generated block equals what the registry generates (`drift`). CI runs both
  as its rules gate.
- **`check_records.py`** — every `.lean` module under `ClassicalLean/` must be named in
  the old round archive (read only if present), in a fragment under `records/rounds/`,
  or in an order under `records/orders/`. A **tree** check rather than a `git log` audit, deliberately: a commit
  cannot cite its own hash, so a history audit cannot be run by the commit that needs it, while
  module paths are known before the commit is made. **Stated limit:** it checks that a module is
  *named*, not that what the record says about it is true — a wrong round entry passes. It exists
  because the other five gates check axioms, vacuity, holes and vocabulary, and none of them can
  see a records gap; on 2026-09-07/08 two concurrent sessions shipped `Simplex/Symmetry.lean` and
  `Simplex/Temperature.lean` with no round entry and every gate stayed green. One named
  exemption, `Simplex/Hessian.lean`, carrying its evidence in the script.

**Both Lean gates test `privateToUserName`.** A `private theorem` is stored as
`_private.<Module>.0.<name>`, which no namespace-prefix test matches — before that fix, every
private declaration in the library was exempt from the axiom gate (89 of 625 constants at the
time). If you write a new gate that filters by namespace, this is the trap.

**CI (dated 2026-10-15 UTC, order MERGE-1).** `.github/workflows/ci.yml` (sha256
`0d7508432a867a9f44caca6b498e9d33b0b42230a73f240c74734070ff00283e`, from order CLOUD-1) runs on
GitHub on every push to `master` and to any `cloud-*` branch. It builds the library with
`leanprover/lean-action` (pinned v1.6.2, with Mathlib's cache) and then runs the axiom gate,
`check_sorry.py` and the vacuity gate. It does not run `check_records.py`, `banned_vocab_scan.py`
or the report tool, and it is not gate 7: the independent recheck reached about 28 GB of memory
uncapped and runs only on DSMain, under a 12 GB cap. A newer push cancels an older run on the same
branch (`concurrency`, `cancel-in-progress: true`). A run takes about 11 minutes; GitHub's free
plan gives 2,000 minutes a month for private repositories. Its planted-fault test (a `sorry`
theorem on a scratch branch, `cloud-ci-fault`: the axiom gate and `check_sorry` failed, the clean
tree passed) is lane `CLOUD-1-CI-result.md`.

**The witness gate is not in CI (dated 2026-10-26 UTC, order VACUITY-4, Goal item 6).** Its
whole-library time at HEAD after the order's leftover commits, on DSMain (16 cores), one Lean process
at a time under the 12 GB cap, was 27 minutes, above the 20 minutes Goal item 6 sets (the gate's
output does not split the time; the session judges that most of it is the listing driver, which
checks every command of all 140 modules). Ruling 5 of the order keeps
the limit and leaves speed to a later order (GATE-SPEED); until then claude-ai's push review of
every Lean order reads the session's whole-library `WITNESSGATE` result at G. `ci.yml` is unchanged
by this order (sha256 `2dc680ea9b745963f72fd49835ae433286a56564bf643aeccf90b220f03b8182` at
`ac62f50` and at HEAD; the hash in the MERGE-1 paragraph above predates order RULES-1's change of
the file); the gate's time on GitHub's runner is not measured.

**Research actions step 4 (dated 2026-10-26 UTC, order VACUITY-4, Goal item 8).** The re-check
outside the build is gate 7 since order RECHECK-1 (leanchecker per module, then nanoda on a
`lean4export` export, with a planted fault), measured at `d21fd22`. `lake comparator` and `lake
check` exist from Lean v4.35.0 on (the standalone Comparator, now superseded, needs a newer
toolchain at its latest commit), not at v4.34.0. So they wait for the order that moves the
toolchain to v4.35.0 or later, which then decides how comparator checks AI-drafted statements
against their approved statements (the plan's purpose), and whether `lake check --paranoid`, with
the toolchain's bundled nanoda and `--from-export`, replaces gate 7's hand-built steps.

---

## 5. Naming

**Dated 2026-10-07 (order LEAN-5):** the term list is no longer in the repository. The scanner
reads it from `~/.config/classical-lean/banned-terms` (JSON, mode 0600) and exits 2 if it is
missing. The old round archive (rounds 1–14 and 10a) and the retirement list are removed, and
retired words quoted in this file and the
records are replaced by `[surname]`, `[retired term]` and `[retired name]`; see `records/README.md`.
Both survive only in the full history, archived outside this repository; where this file cites
an early round, that is where it is.

**Results are named for what they are about.** No eponyms, no project nouns, no acronyms from
the source corpus. `orderedSimplex`, `freeEnergy`, `factorialPart`, `CompositumDiscriminant` —
not the names the sources used. `banned_vocab_scan.py` enforces this on every build and the
shipped library has zero hits.
**Dated 2026-09-23 (order G-5, round 19):** the only permitted occurrences of the retired
corpus's eponym in `ClassicalLean/`, outside audit-marked lines, are the two licence-header
lines naming the copyright holder (Apache-2.0, Dustin's choice of 2026-09-23); the scanner
permits exactly those and fails on any other. "On every build" is loose: the scanner is gate 5
of the six manual commands in §1, not part of `lake build`.
**Dated 2026-09-24 UTC (order G-6, J2 step 1):** the two permitted lines are the copyright line,
which names Dustin alone, and the Authors line, which now credits Claude as a co-author:
`Authors: Dustin [surname], Claude (Anthropic)`.
**Dated 2026-09-24 UTC (order G-7, J2 step V):** "outside audit-marked lines" no longer
applies — the allowlist is removed — and the scan covers `ClassicalLean.lean` as well.

Where such a name appeared in the old round archive or the retirement list it was a **quoted source
identifier being retired** — the record of a removal, not a use — and the list said so at the top.
Keep
that distinction. If you add a term to the retired list, add it to the scanner too; the list is
the record.

For new material, use the standard name from the literature. If you are unsure what a result is
conventionally called, find out — "the theorem is right but nobody can find it" is a real
failure mode, and it is the one this library was built in reaction to.

---

## 6. Working agreement

- **Local commits only.** Neither repository has a remote and neither should acquire one without
  being asked. `~/work/classical-lean` is the library; `~/Cowork/lean-rebuild` is the evidence,
  pinned from the round archive at a commit hash so the link survives a move.
  **Corrected 2026-09-23:** both repositories now have one remote, `dsmain`
  (`dsmain:/data/git/classical-lean.git` and `dsmain:/data/git/lean-rebuild.git`, through the
  `dsmain` ssh alias). First pushes, read from each repository's `dsmain` reflog: `lean-rebuild`
  2026-09-08T23:27:12Z, `classical-lean` 2026-09-09T19:41:09Z. What still holds: commit locally;
  push to `dsmain` only when Dustin says yes; never push to GitHub and never add another remote.
  Pushes so far, each on his yes and fast-forward only: on 2026-09-23, `lean-rebuild` to `b84de8f`
  and `classical-lean` to `7ad841e`.
  **Dated 2026-09-23 (order G-5, round 19):** one later push is missing from that list:
  `classical-lean` to `025b729`, fast-forward, at 13:12:36 -0400 — the `dsmain/master` reflog
  (`update by push`) and `~/work/_bump-evidence/push.log` (`rc=0 push :: 7ad841e..025b729`). It
  came one second after order 0923's last records commit, which therefore could not list it.
  Whether it was on his yes is not recorded in this repository.
  **Dated 2026-09-23 (order G-5, after its close):** `classical-lean` to `59fa0d9`, on Dustin's
  yes to the Close's push question, fast-forward from `025b729`, at 17:04:46 -0400 — the
  `dsmain/master` reflog (`update by push`) and `~/work/_bump-evidence/push.log`
  (`rc=0 push … 025b729..59fa0d9 master -> master`; `ls-remote` afterwards `59fa0d9…`). This line
  is committed after that push, so `master` is one commit ahead of DSMain until the next push.
  **Dated 2026-09-24 UTC (order G-6, J1):** one earlier push is also missing from this list:
  `classical-lean` to `202394a`, fast-forward from `38a1252`, at 2026-09-13T06:42:22Z
  (02:42:22 -0400) — the `dsmain/master` reflog (`update by push`) and order 0923's §0 row 2. It
  predates `~/work/_bump-evidence/push.log`, whose first line is the later `202394a..7ad841e`.
  Whether it was on Dustin's yes is not recorded in this repository.
  **Dated 2026-09-24 UTC (order G-7, J2 step 7):** `classical-lean` to `cca6f8a`, on Dustin's
  yes to order G-6's push question, fast-forward from `59fa0d9`, at 2026-09-24T02:05:15Z
  (22:05:15 -0400 on 2026-09-23) — the `dsmain/master` reflog (`update by push`) and
  `~/work/_bump-evidence/push.log` (`rc=0 push [G-6, Dustin's yes 2026-09-24] ::
  59fa0d9..cca6f8a master -> master`; `ls-remote` afterwards `cca6f8a…`). push.log's date is the
  UTC date.
  **Dated 2026-09-24 UTC (order G-8, records):** `classical-lean` to `87683e3`, on Dustin's yes
  to order G-7's push question, fast-forward from `cca6f8a`, at 2026-09-24T17:43:46Z (13:43:46
  -0400) — the `dsmain/master` reflog (`update by push`) and `~/work/_bump-evidence/push.log`
  (`rc=0 push [G-7, Dustin's yes 2026-09-24] :: [...] cca6f8a..87683e3 master -> master`;
  `ls-remote` afterwards `87683e3…`).
  **Dated 2026-09-25 UTC (order G-9, records):** `classical-lean` to `196a87d`, on Dustin's yes
  to order G-8's push question, fast-forward from `87683e3`, at 2026-09-24T23:25:19Z (19:25:19
  -0400) — the `dsmain/master` reflog (`update by push`) and `~/work/_bump-evidence/push.log`
  (`rc=0 push [G-8, Dustin's yes 2026-09-24] :: To dsmain:/data/git/classical-lean.git
  87683e3..196a87d master -> master`; `ls-remote` afterwards `196a87d…`).
  **Dated 2026-09-25 UTC (order G-10, records):** `classical-lean` to `432aa26`, on Dustin's yes to
  order G-9's push question, fast-forward from `196a87d`, at 2026-09-25T04:29:35Z — the
  `dsmain/master` reflog (`update by push`) and `~/work/_bump-evidence/push.log`
  (`rc=0 push [G-9, Dustin's yes 2026-09-25] :: To dsmain:/data/git/classical-lean.git
  196a87d..432aa26 master -> master`; `ls-remote` afterwards `432aa26…`); recorded now by G-9's
  Close step 4 (order G-10 §0 row 1). This order's own push, if Dustin says yes at the close, the
  next order records.
  **Dated 2026-10-07 (order LEAN-4):** `classical-lean` to `299cc09`, by Dustin from his terminal on
  DSMain, fast-forward from `ea592cf`: `ea592cf..299cc09  prove-disc-biquadratic -> master` for
  `To /data/git/classical-lean.git`. The order gives the time as 15:32 EDT (his terminal). Measured
  on DSMain: the clone's `origin/master` reflog shows `update by push` at 2026-10-07 15:31:38 -0400,
  and `git ls-remote origin master` gives `299cc09…`. This push landed order LEAN-3 (round 31).
  **Dated 2026-10-07 (order LEAN-5):** `classical-lean` to `2e79a0c`, by Dustin from DSMain,
  fast-forward from `299cc09` (`package-nightly` → `master`), landing order LEAN-4 (round 32). Measured
  on DSMain: the clone's `origin/master` reflog shows `update by push` at 2026-10-07 16:04:34 -0400,
  and `git ls-remote origin master` gives `2e79a0c…`.
  **Dated 2026-10-15 UTC (order MERGE-1):** the repository also has the remote `github`
  (`datasphereai/classical-lean`). Cloud sessions push only their own `cloud-*` branches to it
  (orders CLOUD-1 and CLOUD-MATH-1; CLOUD-MATH-1 overrode "never push to GitHub" for its branch);
  `master`, on both remotes, still moves only from DSMain, after claude-ai's check and on Dustin's
  push.
- **Rules learned in the runs of order 0923 (rules 1–7), order G-5 (rules 8–15), order G-6
  (rules 16–19), order G-7 (rules 20–25), order G-8 (rules 26–30), order G-9 (rules 31–34),
  order LEAN-29 (rule 35), order LEAN-30 (rules 36 and 37) and order LEAN-32 (rules 38 and 39).**
  Rules 1–7
  are dated 2026-09-23; source: order G-5 §1, which cites round 17's dated amendment, Findings 1
  and 3 and "Options and linters", round 18's Findings 1 and 2 and closing addendum, and order
  0923's final report. Rules 8–15 are dated 2026-09-24 UTC; source: order G-6 §1, which cites the
  round named with each. Rules 16–19 are dated 2026-09-24 UTC; source: order G-7 §1, which cites
  its §0 row 13, rounds 21 and 22 and order G-6's Close check (lead-in dated 2026-09-24 UTC,
  order G-7, J2 step 7). Rules 20–25 are dated 2026-09-24 UTC; source: order G-8 §1, which cites
  its §0 rows 16–18, round 24 and round 24's addendum (lead-in extended 2026-09-24 UTC, order
  G-8). Rules 26–30 are dated 2026-09-24 UTC; source: order G-9 §1, which cites its §0 rows 14
  and 15, round 25's timeline and round 26's addendum (lead-in extended 2026-09-25 UTC, order G-9,
  records; the rules' text is order G-9's, with "§0 row" qualified as order G-9's). Rules 31–34 are
  dated 2026-09-25 UTC; source: order G-10 §1, which cites order G-9's run (its §0 rows 14 and 15,
  round 27, and round 28's addendum items 11, 17, 20 and 23); lead-in extended 2026-09-25 UTC,
  order G-10, records. Rule 35 is dated 2026-10-15 UTC; source: order LEAN-30's rule 8, which
  cites order LEAN-29's `2bba7b6` and `54c3624` and its reviews r92 (finding 4) and r92c (findings
  A and B); see also claude-ai's push review of LEAN-29 (lane `lean/LEAN-29-ruling-2.md`, note 1);
  lead-in extended 2026-10-15 UTC, order LEAN-30, job 3. Rules 36 and 37 are dated 2026-10-16
  UTC; source: order LEAN-31's rules 9 and 10, which cite order LEAN-30's close, threads 2 and 3;
  lead-in extended 2026-10-16 UTC, order LEAN-31, job 3. Rules 38 and 39 are dated 2026-10-18 UTC;
  source: order LEAN-32's rules 12 and 13, which cite order LEAN-31's `misses.md` item 23 (rule 38)
  and order LEAN-31's close, section 3.4, and `misses.md` items 10 to 14, 17 and 20 (rule 39);
  lead-in extended 2026-10-18 UTC, order LEAN-32, job 3.
  The next order
  cites these instead of repeating them:
<!-- rules:begin (generated by compile_rules.py from the rule registry; edit the registry, not this block) -->
  Rules to apply yourself (21 of a budget of 21, set by RULES-1 2026-10-19: lowered to the self-applied count under row 20261018-010):
  1. *Check the invariant, not a proxy* — §0 applied to a gate: the cache check tested all of Mathlib, and so it stopped the toolchain move over a module this library never imports.
  2. *Read a Mathlib definition before stating anything about it.* The `klDiv` bridge was written from the name; the definition carries a mass term.
  3. *Junk cells need random trials plus constructed exact-zero cases.* Random search missed a measure-zero failure.
  10. *Test harnesses match identifiers exactly, never by prefix.* Suspect the harness first when a result surprises (round 20: `S1` matched `S10`).
  12. *Reviewers work in a scratch directory outside the repository*, with `PYTHONDONTWRITEBYTECODE=1`, copy a repository script before importing it, and are followed by a `git status` check (round 20: two reviewers wrote outside their brief).
  14. *Before-and-after evidence is a type dump, read by its `DIFF` line and judged up to proof irrelevance.* (absorbs rule 25) Before-and-after evidence is `TypeDump.lean` with `g5_typediff.py`, not name lists alone (round 19). Read its `DIFF removed= added= changed=` line, not its exit code, which is 0 whenever nothing changed even if records were removed or added (order G-6, round 21). **Amended 2026-09-24 UTC (order G-8, rule 25, now part of this rule):** the pair is now `~/work/_bump-evidence/TypeDumpPI.lean` with `g8_typediff.py`, which print today's fields and the same forms with every proof replaced by one placeholder; their `DIFF` line adds `proof_only=`. They passed their controls in order G-8's J1 (round 25). `TypeDump.lean` and `g5_typediff.py` are kept, unchanged. Type-dump Done-means are judged up to proof irrelevance: a record whose raw form differs only inside proof terms is `PROOF-ONLY`: listed, explained, and not counted as changed (round 24's addendum, item 1; order G-8 §2's ruling). Without a tool that has passed its controls, such a record is settled by a Lean file with a fire test, as round 23 did (`DefeqCheck.lean`).
  15. *A pattern written for a tool is tested under that tool's own compile flags* (round 19: claude-ai's exception, compiled with `re.I`, also admitted lowercase variants).
  17. *Every reviewer and checker output is saved verbatim, with its sha256, in the order's evidence directory when it returns.* (absorbs rule 33) Fragments quote from the saved file. A workflow returns each report's text with its sha256, and the saving command compares the two before the report is read; where reviews are dispatched outside a workflow, the same holds by extracting each agent's returned text from its hand-back and hashing the saved file against it. Sources: order G-6's Close check: the statement reviews were paraphrased and their outputs not kept (rule 17); nothing in orders G-5 to G-9 had checked that a saved review was the text its agent returned, until G-9's addendum compared all twelve against the harness's journal, round 28's addendum item 23 (rule 33).
  18. *Records follow the clock.* When a step runs out of the order's sequence, or overlaps another (a search re-run after the proof, step commits cut from a finished module, proving while a review runs), the fragment says so at that step, with times (order G-7 §0 row 13; rounds 21 and 22).
  19. *Research notes name the source of every proof route they propose*: derived here, a textbook with its reference, or a prior-art file, so that the module docstring's credit can be exact (round 22: the base-2 route was the prior art's).
  20. *`lake env lean` checks types only: scratch proofs are elaborated with the lakefile's options, and linter results count only from `lake build`.* (absorbs rule 11) Linter results count only from `lake build`, run from the repository root: `[leanOptions]` apply only there, and the header linter finds the root by a relative path. Scratch proofs are elaborated with the lakefile's options: `lake env lean -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3 <file>`. Plain `lake env lean` applies none of `[leanOptions]`, so a proof checked only that way can land with linter warnings. Sources: rounds 19 and 20 (rule 11); round 24: four `flexible` warnings at order G-7's first J3 build, and order G-8 §0 row 17 (rule 20).
  22. *Every quote in a fragment, block or inline, is checked by a script against its saved source before the fragment is committed* (absorbs rule 34), with a negative control (for inline quotes, a planted misquote), and every omission inside a quote is marked `[...]`. An inline quote is a phrase in quotation marks or backticks attributed to a document; it is checked by script against its source, as block quotes are. Sources: round 24's addendum, items 3 and 4, and `g7/close/quotecheck.py` (rule 22); `inlinecheck.py`, and round 28's addendum items 11 and 23: three inline quotes cut or paraphrased their sources and the block-quote check never saw them (rule 34).
  23. *Evidence commands run through one helper, and the evidence log holds only what was measured.* (absorbs rules 5, 8, 30, 32) The helper takes the prediction as an argument, refuses to run without one, and logs the command with its own `$?`; every evidence-log line carries its command and its rc. An evidence log records only a measured rc, taken from the command's own `$?`: a run that did not happen is logged `NOT RUN`, never a placeholder, and a refused call is logged `NOT RUN` in the next helper call, with the refused command's label and the guard's message, so that the final report's count of refusals is a `grep` of `evidence.log` and not a recollection. Every write, hash and edit of an evidence or records file runs through the helper, or is listed in the plan and the fragment before the commit that carries it. A commit runs only when its gates exited 0 in the same run. Sources: round 24's addendum, items 7, 8 and 9, and order G-8's `ev.sh` and `land.sh`, round 25 (rule 23); rule 5; round 20, the Close check's addendum (rule 8); order G-9 §0 row 15: the report said "nothing stopped" and "the only refusals were my own tools" over one guard refusal the log never saw (rule 30); order G-9 ran five such commands outside the helper, round 28's addendum item 20 (rule 32).
  26. *Every brief is built by script from `HANDOFF.md` and saved with its sha256 before it is sent; every reader, research and review brief quotes the rules it will be checked against* (absorbs rule 24), at least rules 16 to 25 as numbered on 2026-10-18 (where one of them has since been merged, the rule that absorbed it). Briefs are built as order G-8's Close-check brief was (`close-brief-make`); a brief that claims to quote a rule verbatim quotes it verbatim, cuts marked `[...]`. Sources: round 24's addendum, item 6 (rule 24); round 26's addendum, item 16: the J3 post-proof brief shortened rules 16–25 without marking the cuts, and the J2 briefs were never saved (rule 26).
  27. *A count that Lean generates is predicted by a Lean measurement of the scratch file, not by hand.* Theorem constants: a census of the elaborated scratch file's environment under the axiom gate's `.thmInfo` predicate, restricted to the declarations being landed, auxiliaries included; import closures: `env.header.moduleNames` of a file importing the module alone (order G-8: 1421 against a hand prediction of 1326–1345, 16 modules against 5–8; order G-9 §0 row 14). A hand prediction may accompany the measurement; it does not replace it.
  28. *A workflow or script that consumes inputs takes them as arguments and refuses to run without them.* Order G-8's critic script ignored its arguments; re-invoked by mistake it would have re-run four critics over the old draft and overwritten their saved reports (round 25's timeline, 20:29:42Z; order G-9 §0 row 14).
  31. *A job's work runs in order: no statement is drafted before the job's last search and cell has run, a statement review's verdict is in before any proof of those statements, and every new declaration is reviewed cold before its commit.* (absorbs rules 13, 16, 21, 29) No statement of a job is drafted until the job's last search and cell has run, the ones a plan critic adds included; a statement drafted in a plan is drafted, so a job's recorded searches and junk cells come before any of its statements is drafted, the plan's drafts included. A cell a review adds after a draft is run and logged, and the draft re-hashed and re-elaborated after it (rule 18); J1 item 12 checks it by mtime against the log. A statement review's verdict is in before any proof of those statements is written: research, other jobs' drafting, and gate runs may overlap a review; proofs of the statements under review may not. Every new declaration, private helpers included, is reviewed cold before its commit. A review fix that touches a proof line gets its delta check before the landing, as the review's condition asked. Sources: order G-9's J1 ran cells and reads after the first drafts, round 28's addendum item 17, a MAJOR finding (rule 31); round 24's addendum, item 2 (rule 21); order G-6's run: J2's and J3's statement reviews returned after their proofs were written, J2's compiled, and §0 row 13 of order G-7, rounds 21 and 22 (rule 16); round 20: three helpers were reviewed only after proving (rule 13); round 26's addendum, item 18: `hp.out` to `(Fact.out : p.Prime)` landed without its delta check, and the gates and the type dump then held, which is luck, not a check (rule 29).
  36. *Every clock time carries its date, and time windows use epoch seconds or `find -newer`.* (absorbs rule 9) A clock time in a brief, a prediction or a record carries its ISO date on the same line (for example `2026-10-16T01:45 EDT`, or `2026-10-16 01:45 EDT`), or the text names no clock; a brief names the night window of its order's Scope rather than copying its daily times, and gives the dated end of its own run. The brief builder refuses a brief with a line that holds a time, matched by `(?<![\d:])\d{1,2}:\d{2}(?!\d)`, and no date `\d{4}-\d{2}-\d{2}` on that line; an order copied verbatim into `records/orders/` is exempt. Time windows use epoch seconds, or `find -newer <reference file>`, never a formatted UTC time without its `Z`. Sources: order LEAN-30's brief builder wrote "none after 01:45 EDT" with no date, and four item reviewers read it on 2026-10-15 at 13:53 EDT as already past and ran no Lean: LEAN-30's close, thread 2 (rule 36); order G-5's session page, as claude-ai read it, not recorded in round 20 (rule 9).
  37. *A name is probed before the text that uses it, and `el.sh` enforces it.* Before it runs Lean, `el.sh` reads the text (a scratch draft whole; a library module only on its lines changed against the order's base commit), with comments, docstrings and string literals removed, takes the identifiers that contain `.` or `_`, and refuses the run, logged `NOT RUN` with the tokens, while one is not cleared: by a successful `#check` probe of it or of a dot-prefix of it, or of a full name that ends in `.` and it (a name under `open`); by a first component that the text declares or binds (a hypothesis or a local); or by the hashed allowlist of tactic names. The order's own statement probes seed it. Refusing too much is safe: a probe clears it (order LEAN-30 used names in drafts before their `#check` probes again, its review r98's MAJOR and others: LEAN-30's close, thread 3).
  38. *A tool that imports `ClassicalLean` runs only on a fresh root build.* The bridge search, the report tool, the plan's checks with `--lean`, a census that imports the root, and any other tool that imports `ClassicalLean` run through a wrapper (order LEAN-32's `rootrun.sh`) that first runs `lake build` at the current HEAD under the memory cap, logs its rc, its job count and `git rev-parse HEAD`, and refuses the command, logged `NOT RUN`, unless that build's rc is 0. The gates are not wrapped; they run after gate 1's build. Tested before first use: with the build replaced by `false` the command is refused and not run; with the real build the build line comes before the command line, at the same HEAD (order LEAN-31's first bridge search and report tool run read a `ClassicalLean.olean` built before its new module existed, so both saw 128 modules and were void: its `misses.md` item 23).
  39. *A commit is staged by path; its message is written after its gates have run, says only what the evidence log shows, and, when it cites runs, ends with a run citation written by script.* (absorbs rules 4, 6, 7, 35) Stage every commit by path, branch commits included. Write a commit message only after its gates have run. Any linter or option switched off or on goes in the first paragraph of the commit message, and in §1. A commit message says only what the evidence log shows: a commit message that cites a run names its evidence label and claims only what that run's output shows, and every Mathlib or library name a proof uses that the order's own probes do not cover gets a logged `#check` probe before the first draft that uses it. Run citations in commit messages are written by script. After each commit a marker line `COMMIT <hash>` goes into `evidence.log`; a commit message that cites runs ends with one line written by a script (order LEAN-32's `evcite.py`), `Evidence: evidence.log lines N to M: <every label in those lines>`, covering every line since the last marker; and a checker (its `citecheck.py`) compares each commit's `Evidence:` line with the log and reports every difference, its output at the end of the push-review file (order LEAN-32, job 4e). Tested before first use: a message whose label list leaves one label out is reported; the generated line passes. Sources: order LEAN-31's commit messages named lists of runs that were not the whole list, its close, section 3.4, and `misses.md` items 10 to 14, 17 and 20 (rule 39); order LEAN-29's `2bba7b6` said item 92's names "were probed first (el.sh p92-1)", when that probe had failed on three names and two of the names used were never probed by `#check`, review r92, finding 4, and the fix commit `54c3624` restated it with a quotation cut without a mark and left out the run that confirmed the names, review r92c, findings A and B (rule 35); rules 4, 6 and 7.
- **Rules a tool enforces** (0; the tool refuses the act, so there is nothing to remember):
- **The full text** of every rule, the enforced, merged and retired ones included, is in the rule registry (merged: 4 into 39, 5 into 23, 6 into 39, 7 into 39, 8 into 23, 9 into 36, 11 into 20, 13 into 31, 16 into 31, 21 into 31, 24 into 26, 25 into 14, 29 into 31, 30 into 23, 32 into 23, 33 into 17, 34 into 22, 35 into 39).
<!-- rules:end -->
- **Standing answers** (dated 2026-09-23; source: order G-5 §2):
  - A Mathlib cache gap outside this library's import closure: use the import-closure check plus
    the `.olean` sha256 manifest taken before and after `lake build` (ruled for order 0923's J3).
  - A deprecation whose replacement changes what a statement says: give the library its own
    object with the identical definition, check it equal by `rfl` in a scratch file, switch to it
    (same ruling; `closedSimplex`, round 17).
  - The licence is **Apache-2.0**, chosen by Dustin; the copyright and Authors lines name him
    (`LICENSE`, the header on every module, §1).
  - The retired corpus's eponym stays banned. One anchored exception in
    `tools/banned_vocab_scan.py` permits exactly the two licence lines; as landed it is
    case-exact with an ASCII year, `(?-i:^(Copyright \(c\) 20[0-9][0-9] Dustin [surname]\. All
    rights reserved\.|Authors: Dustin [surname])$)`, stricter than the order's `\d` form because the
    scanner compiles exceptions case-insensitively (the executing session's ruling; round 19).
    **Dated 2026-09-24 UTC (order G-6, J2 step 1):** at Dustin's wish of 2026-09-23 the Authors
    line credits Claude as a co-author, `Authors: Dustin [surname], Claude (Anthropic)`, on every
    module and `ClassicalLean.lean`; the copyright line stays his alone. The exception's second
    alternative is now `Authors: Dustin [surname], Claude \(Anthropic\)`, in the same `(?-i:…)`
    form; the old Authors line fails the gate.
    **Dated 2026-09-24 UTC (order G-7, J2 step V):** the exception now forgives only a
    `[surname]` hit lying inside one of those two whole lines, and `ClassicalLean.lean` is
    scanned too, so its two licence lines are checked by the same entry.
  - `mem_closedSimplex` stays, by `mem_openSimplex`'s precedent (claude-ai's decision on Dustin's
    delegation; his veto is open).
  - The parked `v4.29.0-rc2` build (`~/work/_parked/classical-lean.lake-v4.29.0-rc2`) stays
    parked; only Dustin deletes it.
  - Anything that needs Dustin: ask in one line, recommended answer first, and keep working on
    what does not depend on it. Publishing, and offering anything to Mathlib, are his decisions,
    like pushing.
  - **Dated 2026-09-24 UTC (order G-7 §1, measured in order G-6's run):** the local guard
    blocks a heredoc commit message that contains `*` and refuses inline `python3 -c` and
    chained in-place edits: write every commit message to a
    file and commit with `git commit -F <file>`; write scripts to files in the evidence
    directory and run them.
  - **Dated 2026-09-24 UTC (order G-8 §1 and J1):** the guard also refuses any Bash call that
    contains `python3 -` reading from stdin: run scripts as `python3 <file>`. helios's `BASH_ENV`
    (`~/.bash_env`) switches `pipefail` on in every non-interactive bash, so a pipeline's rc
    depends on the calling shell; the evidence helper sets `pipefail` itself. A plain
    `git status` takes `index.lock` for an optional refresh and moves `.git`'s mtime; a read-only
    status runs as `GIT_OPTIONAL_LOCKS=0 git status` (round 25).
  - **Dated 2026-09-25 UTC (order G-9 §1, J1 and J3):** helios's `ls` prints local time (EDT); read
    evidence times with `TZ=UTC` (`TZ=UTC ls --time-style=full-iso`), as `evidence.log`'s are UTC.
    `sort` and `comm` on helios are the Rust coreutils, and under a UTF-8 locale `sort` collates by
    the locale while `comm` compares bytes: run any `sort`/`comm` comparison under `LC_ALL=C`
    (`land.sh` exports it since order G-9's J1; round 28 records a comparison that did not).
  - **Dated 2026-09-24 UTC (order G-8 §2):** order G-7's J2 Done-means 3 is ruled. The two
    records `hasDerivAt_softmax` and `hasDerivAt_softmax_categoricalCov` changed only inside a
    `Prop`-valued instance argument, and their statements did not change: claude-ai, as order
    G-7's author, confirmed its executor's ruling (order G-8 §0 row 18; re-run in J1,
    `DefeqCheck.lean` rc 0 and its fire test rc 1). Dustin's veto stays open. Under rule 25 such
    records are `PROOF-ONLY`.
  - **Dated 2026-09-25 UTC (order G-10, J2 records; source order G-9 §0 row 14):** the Edit tool
    refuses a file that has not been read in the session ("File has not been read yet"). Read a file
    before editing it, and never run a measurement of a file in the same call as its edit.
  - **Dated 2026-09-25 UTC (order G-10, §2):** on the two-commit close, the Close commit sets the
    `INDEX.md` row's State to "Close check pending" alone; the Close-check addendum's commit is what
    closes the row.
- **Keep the records true.** A source theorem that is neither shipped nor explicitly dropped is
  silence, not a decision. Per-declaration drop reasons live in the module header that inherited
  the source file; record file- and block-level decisions in the round fragment under
  `records/rounds/` and point at them.
- **Report what you measured.** If a step was skipped, say so. If a claim is a reading rather
  than a measurement, label it — §2 of this file does that, and the labels are the useful part.
