# Round 58 — satisfiability witnesses for items 1 to 71, the uninformative-statement report, the gate's stale text (order VACUITY-3)

Session: Claude Code `session_01AbBRjKg16k8xxtNMe2yBYd` on DSMain, as dustin, executing order `VACUITY-3`
(`records/orders/20261014T031200Z__claude-ai__order-vacuity3-witnesses-uninformative-report-gate-text.md`), items 89 and 90
of the plan `/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library-2.md`
(sha256 6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166), and the gate's text
fixes HANDOFF.md §4 left for a later gate order, in the worktree `~/lean/classical-lean-paper-crypto`
on branch `vacuity-3`, made from `origin/master` = `bf9922b` (equal to `git ls-remote github master`).
Lean and Mathlib v4.34.0. Nothing pushed. Evidence: `~/lean/vacuity3-checks/` (outside the
repository), `evidence.log` (time, label, rc, prediction, command per run). Plan: lane
`lean/VACUITY-3-PLAN.md` (sha256 013fb6c178012ce86fef815f3cb58d4bd2b58db6786f912a953d3a761b9e26bb),
approved by Dustin on 2026-10-14 (UTC).

First part written before any Lean file changed; completed after the work, below.

## Files this round changes (no new module)

No module is new, and `ClassicalLean.lean` does not change. No theorem, definition, proof, import,
attribute, `open`, `variable` or namespace line changes: the only change in a module is a block of
`example`s (satisfiability witnesses, item 89) appended after its last line. The module files of
the order's targets table (lane `lean/VACUITY-3-targets.tsv`), in table order, each of which may
gain witnesses:

* `ClassicalLean/Statistics/FrischWaughLovell.lean`;
* `ClassicalLean/Probability/CovarianceDirections.lean`;
* `ClassicalLean/Statistics/ResidualVariance.lean`;
* `ClassicalLean/InformationTheory/Entropy.lean`;
* `ClassicalLean/Probability/LikelihoodScore.lean`;
* `ClassicalLean/Probability/EffectiveSampleSize.lean`;
* `ClassicalLean/InformationTheory/MutualInformation.lean`;
* `ClassicalLean/InformationTheory/SourceCoding.lean`;
* `ClassicalLean/InformationTheory/Channel.lean`;
* `ClassicalLean/Analysis/HermiteHadamard.lean`;
* `ClassicalLean/Analysis/RoundingError.lean`;
* `ClassicalLean/Statistics/GeneralizedLeastSquares.lean`;
* `ClassicalLean/Analysis/GradientDescent.lean`;
* `ClassicalLean/Analysis/ExponentialWeights.lean`;
* `ClassicalLean/Statistics/RaoBlackwell.lean`;
* `ClassicalLean/Probability/MaximalInequality.lean`;
* `ClassicalLean/Statistics/Cochran.lean`;
* `ClassicalLean/Probability/YuleWalker.lean`;
* `ClassicalLean/Probability/MovingAverage.lean`;
* `ClassicalLean/Probability/TailBounds.lean`;
* `ClassicalLean/Analysis/ConditionNumber.lean`;
* `ClassicalLean/Analysis/LinearODE.lean`;
* `ClassicalLean/Analysis/EulerMethod.lean`;
* `ClassicalLean/Analysis/JacobiIteration.lean`;
* `ClassicalLean/Analysis/NewtonMethod.lean`;
* `ClassicalLean/Probability/FiniteChain.lean`;
* `ClassicalLean/Probability/FairGame.lean`;
* `ClassicalLean/InformationTheory/Fano.lean`;
* `ClassicalLean/Algebra/HadamardInequality.lean`;
* `ClassicalLean/Probability/RelativeEntropyGrowth.lean`;
* `ClassicalLean/Statistics/GaussMarkov.lean`;
* `ClassicalLean/Probability/KalmanVariance.lean`;
* `ClassicalLean/Probability/GamblersRuin.lean`;
* `ClassicalLean/Probability/Extinction.lean`;
* `ClassicalLean/Algebra/MinMax.lean`;
* `ClassicalLean/Analysis/LinearProgram.lean`;
* `ClassicalLean/Analysis/Simpson.lean`;
* `ClassicalLean/Analysis/EulerMaclaurin.lean`;
* `ClassicalLean/Statistics/Sufficiency.lean`;
* `ClassicalLean/Statistics/NeymanPearson.lean`;
* `ClassicalLean/InformationTheory/MethodOfTypes.lean`;
* `ClassicalLean/Statistics/JamesStein.lean`;
* `ClassicalLean/Probability/GlivenkoCantelli.lean`;
* `ClassicalLean/Analysis/FiniteGame.lean`;
* `ClassicalLean/Combinatorics/Tremaux.lean`;
* `ClassicalLean/Combinatorics/ArbitrageCycle.lean`;
* `ClassicalLean/Statistics/AdaptiveCoverage.lean`;
* `ClassicalLean/InformationTheory/CompressionTest.lean`;
* `ClassicalLean/Probability/LongestRun.lean`;
* `ClassicalLean/Probability/InspectionParadox.lean`;

Tools:

* `tools/VacuityGate.lean` (docstrings and comments only; no verdict changes);
* `tools/run_vacuity_tests.py` (checks the UNCHECKED message; a wider verdict column);
* the new `tools/UninformativeReport.lean` (item 90: a report, not a check).

Documents: `HANDOFF.md` §4 (and §1's tool list), `ROADMAP.md` only where it lists what the gate
checks. `tools/vacuity_reviewed.txt`, `tools/vacuity_reviewed_tests.txt` and
`tools/VacuityGateTests.lean` do not change.

## Completed after the work

Items 89 and 90 of MATH-PLAN-library-2 and the gate's stale text are done, with no change to any
theorem, definition, proof, import, attribute, `open`, `variable` or namespace line. One change to
the first part above: Dustin's ruling 1 of this order (lane `lean/VACUITY-3-ruling-1.md`, sha256
`f825cd36215ab62de3977030617e3c1bd580056c4a5361b9bca942b977ca4860`) added one test,
`vac_unchecked_fin_true` with its predicate `FinT`, to `tools/VacuityGateTests.lean`, which the
first part said would not change. The tests are now 89 verdicts, 47 flagged, 3 UNCHECKED as
expected, 0 mismatches; the runner's fail-test (a gate copy with another `unconfirmedMsg`) gives
rc 1 with 3 MISMATCH lines.

**Item 90, `tools/UninformativeReport.lean`** (job 1): commits `2433a9a`; `4e07844` (cold review
r90, one MAJOR: a theorem's try could leak state into the next; `judge` now saves and restores the
command state; self-test 19 checks); `d5176be` and `d722bfc` (docstring points of the confirming
passes; `d722bfc`, the third, had no confirming pass of its own). Run at `d722bfc` (`job1-dev5`,
its library lines equal to the first run's, `job1-run1`, 36.43 s, 4148484 KB): rc 0, self-test
PASS; 1785 written theorems; section A 1027 (0 close, 988 open, 39 dependent, 0 timeout, 0
error); section B 758 (15 close by `simp`, 1 by `positivity`, 742 open); section C 33 Prop-valued
definitions, 0 recursive. Predicted about 37 `CLOSES` in section B; 16 measured: the other 21 are
`rfl` simp value lemmas that closed only through their own simp entry, which the tool now erases
first (the cold review confirmed). Section C: no recursive Prop-valued definition under
`ClassicalLean`.

**The gate's text** (job 2): commits `5c0dc7b` (the seven points in `tools/VacuityGate.lean`, and
ruling 1's test), `c2b17db` (the runner), `aaca9e2` (cold review r2gate, six MINOR), `22865ab`
(its confirming pass; then PASS). Code equal to `bf9922b` outside comments and docstrings; the
runner's version-detection counts equal; the library gate's output equal to the run before, apart
from times. Not done, for a later gate order (r2gate finding 5(c), older than this order): the
gate's FAIL text omits case 5 and does not say what UNCHECKED or KERNEL-REJECTED mean.

**Item 89, the witnesses** (job 3): 78 of the 83 rows of lane `lean/VACUITY-3-targets.tsv`
witnessed, in 47 modules; each witness an `example` after its module's last line, in rule 2's
form. Twelve groups, each with a cold review and a confirming pass:
* group 1 `2f59473`, fix `cb80ce5`; group 2 `bde3f20`; group 3 `c8260d4`, fix `42d2e54`; group 4
  `ba9e75e`, fix `83724b3`; group 5 `c66abe1`, fixes `ceaac20` and `e4227df` (two rounds, the
  order's limit); group 6 `7332b8f`, fix `81b6d73`; group 7 `61946ff`, fix `79eccc5`; group 8
  `04a3e8b`, fix `3fc2b9c`; group 9 `5d36c01`, fix `9202502`; group 10 `7434918`, fix `7bcee33`;
  group 11 `49bcd41`, fix `d222421`; group 12 `b9c2292`, fix `39874de`.
* Not witnessed, 5 rows: `variance_average_eq_of_steady`, `variance_average_le_of_steady`
  (EffectiveSampleSize) and `tendsto_sup_abs_empiricalCDF_sub` (GlivenkoCantelli): an infinite
  independent family is needed, and nothing in the modules' imports builds one
  (`Measure.infinitePi` is outside them; a countable Bernoulli product on `Finset ℕ`, or binary
  digits under Lebesgue measure, would do as a longer proof). `covariance_eq_sum` and
  `isSolution_autocovariance` (YuleWalker): a stationary process with noise is needed; an AR(1)
  model on `ℕ` with weights `2^-(n+1)` meets every hypothesis of both, checked outside the library
  (`~/lean/vacuity3-checks/witness/g5late/yw-parts.lean`, run `g5late-yw-4`); rule 3 asks for an
  AR(2) model (a coefficient family of size at least 2), not built; without helper declarations
  each witness would be about 350 lines. Left for Dustin's ruling.
* Five witnesses are reviewers' models, credited in their docstrings or commit messages: rows 46
  and 47 (group 7), row 65 (group 9, Basu's theorem), rows 77 and 78 (group 11).
* Census of theorem constants after the work (`census-after`, at `49bcd41`): equal to the census
  before, module for module, TOTAL 3228 in 122 modules (witnesses are `example`s and add no
  constant); AxiomGate PASS 3228 at the same commit.

**Documents** (job 4), the commit after `d222421`: `HANDOFF.md` §4 (the stale list struck; the two
stale sentences corrected; the `NatT2` limit kept with section C's count; paragraphs on the report
tool and the witnesses, with the rows not done; the new test counts, citing ruling 1; the FAIL
text left for a later gate order) and §1 (the report tool's command). `ROADMAP.md`: no change; it
does not list what the gate checks. This fragment, `records/orders/INDEX.md` and
`records/CLAIMS.md`.

### Standing rules from this round

1. From order VACUITY-3 on, a satisfiability example applies the theorem itself (rule 2 of the
   order: `example := Full.name (x := …) h₁ …`, every chosen argument by name), not an `∃`
   restatement of its hypotheses. (claude-ai's ruling, with Dustin's veto open.)
2. Every later gate order re-runs `tools/UninformativeReport.lean` and reports its summary lines.

### End checks (job 5)

Filled in after the gates, in a commit that touches nothing outside `records/`.

### Lapses, logged in `evidence.log`

* Two development runs of the report tool (`job1-dev1`, `job1-dev2`) loaded the whole library
  without the 12G memory cap.
* Group 8's fix: a `sed` with an empty line number overwrote the scratch file after the first
  append; the commit `3fc2b9c` was made from the right module text, and the scratch file was
  rebuilt from the commit and re-checked (rule 1 PASS).
* Group 9's fix diff was first saved from the wrong parent (it held groups 7's and 8's fixes); it
  was redone from the right parent before the confirming pass.
* The reason given for rows 9 and 10 was corrected twice after reviews (`g2-correction`,
  `g2-correction-2`), and the reason for rows 31 and 32 once (group 5's second pass: AR(2)).
