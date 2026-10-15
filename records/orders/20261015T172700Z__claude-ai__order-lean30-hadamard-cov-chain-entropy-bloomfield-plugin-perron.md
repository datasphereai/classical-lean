# LEAN-30 order: batch 4 of the library's second plan (items 96 to 100), and five old docstring lines

Written 2026-10-15 by claude-ai for a plain Claude Code session on DSMain, as dustin, from step 1
of OPEN-WORK-20261011-r2.md: LEAN-30 comes after LEAN-29, whose last commit `92a314c` Dustin
pushed to both remotes (measured 2026-10-15 10:41 EDT), **and after order MERGE-1** (lane
`lean/MERGE-1-order.md`, sha256 `062c0fa0e085085cfc5752a2c03ef7e7f210c0cefaeb6286d234bb79165f5af2`),
which merges CI and the five cloud modules of order CLOUD-MATH-1 into master in the same worktree
(store row 20261015-010, Dustin's ruling of 11:25 EDT). LEAN-30 branches from master only after
Dustin has pushed MERGE-1's merge; call that commit **MERGE** (a name for its hash; `M` elsewhere is item 98's bound). Lane files named here without a folder are
in /opt/datasphere/lane/inbox/threads/staging/; files named `lean/...` are in its subfolder
/opt/datasphere/lane/inbox/threads/staging/lean/ (read `lean/README.md`). Your plan, the report and
the push-review file go to `lean/` through ds_write_staging, since the lane is read-only on disk
for you.

**Track the order's steps with the task tools (TaskCreate, TaskUpdate), as Dustin's standing rule
asks** (lane `lean/NOTE-20261015-task-list-rule.md`): lay the jobs out as tasks at the start, mark
each `in_progress` when you start it and `completed` when it is done.

Review: Two passes by one fresh cold reviewer that had not seen it written, reading the order, its
check script and Appendix A in the cloud, and claude-ai's quoted DSMain outputs. Pass 1: PASS WITH
FINDINGS (0 BLOCKER, 3 MAJOR, 13 MINOR; 16 calls); every finding applied (r1). Pass 2, the same
reviewer: PASS WITH FINDINGS (0 BLOCKER, 2 MAJOR, 4 MINOR, all new), confirming the 16 findings of
pass 1 fixed (the first partly, pending the DSMain run, now made); the six new findings applied
(r2), which have not had a third review. Not reviewed: the statements' fit to
MATH-PLAN-library-2.md, which the reviewer did not have (claude-ai read section 5's rows 96 to 100;
your plan checks it again, rule 16), and anything that needs Lean beyond the scratch files' own
elaboration.
Revision r3 (rebasing on MERGE-1) had one short confirming pass of its own (r3).

It rests on: LEAN-29's report and claude-ai's push review of it (lane `lean/LEAN-29-ruling-2.md`,
store row 20261015-001). The ruling's four notes, and what this order does with each:
1. the faults in the commit message of `54c3624` (review r92c, findings A and B: a quotation cut
   without a mark, and i92-2's time and result left out): commit messages stay as written, and
   round 59 states the clock. Together with `2bba7b6`'s message, which said item 92's names were
   probed first when they were not (review r92, finding 4), it becomes new rule 8, filed as
   HANDOFF.md §6 rule 35 in job 3;
2. two `open … in` lines before a witness, against rule 2's "an optional `open … in` line": rule 2
   below says "lines", and job 3 changes HANDOFF.md §4 to match;
3. no statement review before the proofs: HANDOFF.md §6 rule 16 asks for one ("A statement
   review's verdict is in before any proof of those statements is written"). This order's two cold
   reviews of A2 to A5 checked each statement's truth under Lean's conventions, each hypothesis's
   need and the Lean form, but not the fit to the plan (the reviewer did not have
   MATH-PLAN-library-2.md). claude-ai read section 5's rows 96 to 100 against them while writing;
   your plan (before approval, step 4) checks the fit again, row by row, and Dustin's approval of
   the plan closes rule 16 for these statements (2d below). Any statement the session changes gets
   a statement-equivalence review before its proof;
4. the four older PrimitiveDivisor passages and the double bracket in Gruss's lead sentence: job 0.

**Facts at `92a314c`, and what MERGE-1 changes.** The facts below were measured at `92a314c`,
before MERGE-1. MERGE-1 changes, by its own order: five new modules
(`ClassicalLean/InformationTheory/HanInequality.lean`, `ClassicalLean/Analysis/FrankWolfe.lean`,
`ClassicalLean/Analysis/StatePrices.lean`, `ClassicalLean/Probability/PolyaUrn.lean`,
`ClassicalLean/Probability/Reflection.lean`), `ClassicalLean.lean` (their imports),
`.github/workflows/ci.yml`, `records/`, `HANDOFF.md` and `ROADMAP.md`; no other `.lean` file. So
none of this order's homes changes (Before approval, step 1 checks it), and these counts move to
MERGE-1's predicted values (its rule 3): build 4176 jobs, AxiomGate 3335, check_sorry and
check_records 128, gate 7 with 128 modules; round 61 is MERGE-1's, so this order's is **round 62**;
the bridge baseline becomes `records/bridges/MERGE-1/`. Where this order says 4171, 3246, 123 or
`records/bridges/LEAN-29/` for a run after MERGE, use MERGE-1's measured values from its report
(lane `lean/MERGE-1-report.md`) instead, and say so in your plan.

Facts measured on DSMain by claude-ai on 2026-10-15 from 10:41 to 11:00 EDT (DSMain's `date`),
read-only, in `~/lean/classical-lean-paper-crypto` on branch `lean-29` at `92a314c` (`git status
--porcelain` empty after every run). Outputs saved in `/tmp/claude-ai-lean30/` on DSMain; the
scratch files and the closure script are in Appendix A with their sha256.

- **The repository.** `git ls-remote origin master` and `git ls-remote github master` both give
  `92a314c49fec6af16aefabcfd37cd6dbcb32d832`, and so does `origin/master` after `git fetch`.
  `lean-toolchain` is `leanprover/lean4:v4.34.0`; the pinned Mathlib is
  `5ed2965256430c3649e86755f9576b54eca72435` (unchanged since LEAN-29). 123 modules under
  `ClassicalLean/`, 41640 lines (40959 at `20303cd`).
- **The gates at `92a314c`**, from LEAN-29's report (gates at `0ff0d44`; `92a314c` changes only
  `records/`, checked by claude-ai's push review): build 4171 jobs, 0 warnings; AxiomGate PASS
  3246; VacuityGate PASS (1 reviewed helper, 0 VACUOUS-PENDING, 0 rule-5 run-outs, no UNCHECKED);
  the gate's tests 89 verdicts, 47 flagged, 3 UNCHECKED as expected, 0 mismatches; check_sorry
  PASS 123; check_records PASS 123; gate 7 ALL PASSED, 4171 jobs, 123 modules 0 failed, 90647
  declarations, three standard axioms, 3246, planted fault named. The report tool: 1792 written
  theorems; section A 1033 (0 close, 994 open, 39 dependent); section B 759 (16 close: 15 by
  `simp`, 1 by `positivity`; 743 open); section C 33 Prop-valued definitions, 0 recursive.
- **The plan's checks** (MATH-PLAN-library-2-checks.py, `--lean`, `--master
  ~/lean/vacuity2-checks/mm`, under the 12G cap, 10:46 to 10:48 EDT, 2:15 wall, 4374948 KB peak;
  `checks-lean.out`, sha256 `d450430ae1c152ba62938b3d99ff27bd56230ce8258d5e2f9e8d8f439b60d09d`,
  prediction `pred-plan-checks.txt` hashed before the run): **186 of 232** hit. The 46 misses, by
  label: `setup.modules` (123), `setup.worktree` (`92a314c`), `row.A2`, `row.A3`, `row.C2` (both
  searches), `row.C3`, `row.F4`, `row.F5`, `row.F6`, `row.H6`, `row.K2`, `row.X2`, `row.X3` (both
  searches), `row.X4`, `row.X12`, `row.X14`, `row.X15`, `trackL.L2`, `trackL.L4`, `trackL.L15`,
  `trackL.L18`, `trackL.L19`, the seven `gate.*` lines (`maxUnfolds`, `macro`, `helper`,
  `metacheck`, `test.lim_and_hyp`, `test.lim_false`, `list`), and 15 `--lean` lines:
  `census.theorems` 3246, `census.written` 1792, `census.hyp1` 1100, `census.hyp2` 664,
  `census.hyp3` 421, `census.helpers` 600, `census.derived` (593, 4, 597), `used.lines` 58599,
  `bridges.modules` 122, `bridges.pairs` 2437, `bridges.named`, and the four `bridges.rank` lines.
  Against LEAN-29's run (192 of 232, 40 misses): 7 new misses, LEAN-29's own work landing
  (`row.C2` twice, `row.F4`, `row.F5`, `row.X4`, `trackL.L19`, as LEAN-29's job 1 expected) and
  `row.C3` (`euler.?maclaurin`, library 3 → 4); and 1 new hit, `bridges.minquad`, one of LEAN-29's
  16 `--lean` misses. 40 + 7 − 1 = 46.
  - **Every line of rows 96 to 100 hits:** `row.X6`, `row.X8`, `row.X16`, `row.L3`, `row.L7` (both
    searches), and the exact lines `X6.det_cov`, `X8.chain_kl` (FLOAT), `X16.efficiency`,
    `L3.plugin`, `L7.primitive`. So neither Mathlib (pinned or master `2da3ab0a`) nor the library
    has any of the five rows.
- **The homes.** At `92a314c` (sha256 in "Check, then read"):
  - `ClassicalLean.Probability.CovarianceDirections` (538 lines, namespace
    `ClassicalLean.Probability.CovarianceDirections`): `covMatrix X μ i j = cov[X i, X j; μ]`
    (line 99); `posSemidef_covMatrix [Finite ι] [IsFiniteMeasure μ] (hX : ∀ i, MemLp (X i) 2 μ)`
    (line 137). It imports only Mathlib. `ClassicalLean.Statistics.ResidualVariance` and the root
    import it.
  - `ClassicalLean.Algebra.HadamardInequality` (126 lines, namespace `ClassicalLean`):
    `det_le_prod_diag {A : Matrix n n ℝ} (hA : A.PosSemidef) : A.det ≤ ∏ i, A i i`, with
    `[Fintype n] [DecidableEq n]`. It imports only Mathlib.
  - `ClassicalLean.Probability.FiniteChain` (228 lines, namespace `ClassicalLean.Probability`):
    `sum_abs_vecMul_le` (one step shrinks `∑ |d|` by `1 − n δ` when `∑ d = 0`, `d` of any sign),
    `sum_abs_vecMul_pow_le`, `sum_abs_vecMul_pow_sub_le`, `existsUnique_vecMul_eq_self`
    (every entry at least `δ > 0`), and the private `sum_pow_apply_eq_one` (the rows of `P ^ t` sum
    to `1`). It imports `ClassicalLean.InformationTheory.Channel`, which has
    `relEntropy_vecMul_le` (the data-processing inequality, hypotheses `p, q ≥ 0`,
    `q i = 0 → p i = 0`, `W ≥ 0`, rows of `W` summing to `1`); `relEntropy p q = ∑ i, p i *
    Real.log (p i / q i)` is in namespace `ClassicalLean.Simplex` (InformationTheory/Entropy, line
    74). Mathlib's `Matrix.IsPrimitive` (`LinearAlgebra/Matrix/Irreducible/Defs.lean`, line 88:
    `nonneg` and `exists_pos_pow : ∃ k > 0, ∀ i j, 0 < (A ^ k) i j`) is **not** visible through
    FiniteChain's imports (A3's first draft: "Unknown constant").
  - `ClassicalLean.Statistics.GeneralizedLeastSquares` (227 lines, namespace
    `ClassicalLean.Statistics`, `open ClassicalLean.Analysis.MinimumQuadraticForm`):
    `onesInvOnes S = 1 ⬝ᵥ (S⁻¹ *ᵥ 1)` comes from MinimumQuadraticForm. Only the root imports it.
  - `ClassicalLean.Algebra.Kantorovich` (227 lines, namespace
    `ClassicalLean.Algebra.Kantorovich`): `dotProduct_mulVec_mul_inv_le (hm : 0 < m)
    (hmA : (A - m • 1).PosSemidef) (hAM : (M • 1 - A).PosSemidef) (x)`:
    `(x ⬝ᵥ (A *ᵥ x)) * (x ⬝ᵥ (A⁻¹ *ᵥ x)) ≤ (m + M) ^ 2 / (4 * m * M) * (x ⬝ᵥ x) ^ 2`. It imports
    only Mathlib.
  - `ClassicalLean.InformationTheory.CompressionTest` (374 lines, namespace
    `ClassicalLean.InformationTheory.CompressionTest`): `score c p₀ x = 2⁻¹ ^ (c x).length /
    p₀.real {x}`, `bernProd n p` (`p : unitInterval`), `bernProd_real_singleton`,
    `measureReal_score_bernProd_ge_le`. Its docstring's paragraph "Estimating `p` from the same
    trades" gives item 68's plug-in argument and says "This argument is by hand, not proved in
    Lean". The library's `relEntropy_nonneg` is **not** visible through its imports (probe
    `P99.lean`: "Unknown identifier"); `Real.geom_mean_le_arith_mean2_weighted` is.
- **Imports, measured.** The two new import lines (CovarianceDirections gains
  `import ClassicalLean.Algebra.HadamardInequality`; GeneralizedLeastSquares gains
  `import ClassicalLean.Algebra.Kantorovich`) add no module to the closure: A1 (`closure.py`, the
  same file as LEAN-29's A1) gives 9032 before and after, and 9032 also with item 99's optional
  third line (CompressionTest gaining `import ClassicalLean.InformationTheory.Entropy`), "added
  modules 0" each time (`closure.out`). No new module. **Inferred: the build after the work is
  4171 jobs on `92a314c`, so MERGE-1's 4176 on MERGE** (the five cloud modules do not import these
  homes, MERGE-1's facts).
- **The statements elaborate.** The four scratch files A2 to A5 hold every statement of this order
  with `sorry` (A3 holds items 97 and 100, both in FiniteChain), item 99's definition `winRate` in
  full, and a `#check @name` probe for every public name the routes and witnesses below cite (not
  the module's private `sum_pow_apply_eq_one`, which a scratch file cannot see). The probe
  `P99.lean` (A6) shows `relEntropy_nonneg` is not visible through CompressionTest. Each was elaborated
  from the worktree root with HANDOFF.md §6 rule 20's four flags under the 12G cap (`el.sh`,
  summary in `elab.out`): first drafts at 10:49 EDT (A3's probed `Matrix.IsPrimitive`, not
  visible; A4's probed `Matrix.dotProduct_one`, which is `dotProduct_one` in the root namespace);
  final files, with five probes added after cold review 1, at 11:12:44 to 11:12:53 EDT: rc 0 for
  all four; the only messages are `declaration uses sorry`, 1, 3, 1 and 2 of them (one per
  theorem); 2.7 to 3.0 s, at most 3282780 KB; every probe printed.
- **The exact checks**, `lean/LEAN-30-checks.py` (standard library, `python3 -I`, exact fractions
  under Lean's conventions, floating point only for item 97's logarithms, marked FLOAT; predictions
  in its docstring before each run). Revision 1: 36 of 36, 4 BY HAND, as predicted. Revision 2,
  after cold review 1 (the drop lines also check the other hypotheses; two witness lines added):
  **38 of 38 checks hit, 4 BY HAND lines, rc 0**, as predicted; output sha256 `1ff937bade285f225176771c5bbe63746789394b63356e77d118cc7a3c2ba310` in the
  cloud sandbox (Python 3.13), and the same on DSMain from the lane copy (Python 3.12.3, 11:19 EDT, `checks30-dsmain.out`).
- **Five older docstring lines.** LEAN-29's review j0, finding 1 (lane report, "Found and left"):
  four passages of `ClassicalLean/NumberTheory/PrimitiveDivisor.lean` (406 lines) say a check ran
  that no `example` in the library shows: line 98 ("`#check` resolves both against the import
  block below, rc 0"), line 265 ("dropping it fails with exactly that instance error"), lines 346
  to 348 ("elaborating this file's import block followed by `#check
  @Nat.exists_prime_gt_modEq_one` fails with `Unknown constant ...`") and lines 348 to 350 ("The
  statement below was separately checked to be Mathlib's, by elaborating ... in a file that does
  import that module"). And `ClassicalLean/Analysis/Gruss.lean` lines 41 to 43 have two brackets
  in a row, "needed only together (below) (order LEAN-29's exact checks, ...", where the second
  reads as the source of "needed only together", which was shown by hand (LEAN-29's review r92c,
  a note).
- **The bridge baseline** `records/bridges/LEAN-29/` (`COMMIT` `54c3624`): `pairs.tsv`, 2437
  import-unrelated pairs over N = 122 modules, and `shapes.tsv`, 564 shape candidates (LEAN-29's
  report; the file has 566 lines). The two new
  import edges make two listed pairs import-related: rank 127,
  `Algebra.HadamardInequality × Probability.CovarianceDirections` (score 29.7, 10 shared), and rank
  129, `Algebra.Kantorovich × Statistics.GeneralizedLeastSquares` (29.5, 9 shared); and two shape
  lines that say "unrelated": `eigenvalues` (HadamardInequality × CovarianceDirections, line 513)
  and `quadratic form` (Kantorovich × GeneralizedLeastSquares, line 177). ResidualVariance, which
  imports CovarianceDirections, has no listed pair with HadamardInequality (grep). LEAN-29 found
  two real bridges (rows 155 and 156, lane `MATH-PLAN-library-2-bridges-2.md`), neither
  load-bearing for items 96 to 110.
- **The night jobs and memory** (`crontab -l`, `systemctl --user list-timers`, `free -g`, 10:41
  EDT): user timer 00:00 `memory-index`; cron 02:20 `~/restic-kingston/nightly.sh`; cron 03:00
  `daily_verify.sh`; cron 03:30 `datasphere-backup.sh`; user timer 03:30 `lean-nightly`; cron 05:40
  `ds-backup sync.sh`; also a cron every 15 minutes and two user timers that run every few minutes
  (`w29-tracker`, `w29-sysmap`). 62 GiB total, 55 available.
- **LEAN-29's numbers**, for the order table: filed `b7eddf0` 2026-10-15T02:15:33Z, closed
  `92a314c` 03:33:29Z (1 h 18 min); 18 commits; 123 modules (one new); 41640 lines under
  `ClassicalLean/` (+681); 3246 theorem constants (+18); six gates as predicted; one ruling
  (ruling 1, not needed) and Dustin's push.

## Goal

1. **Items 96 to 100** of MATH-PLAN-library-2.md (section 5, "Batch 4"), proved in classical-lean
   under the vacuity gate as LEAN-29 left it, by the plan's per-batch method (its section 8), with
   the statements below. Planned wider than the plan's reading (claude-ai's rulings, Dustin's veto
   open), five conditions in all: item 96 for any finite measure, not only a probability measure;
   item 97 with no `π ≥ 0` and no `∑ π = 1`; item 100's uniqueness with no `P ≥ 0` and no `k > 0`
   (both of `Matrix.IsPrimitive`'s conditions but the positive power), and its rate with no
   `k > 0`. Nothing is meant to be narrower.
2. **Job 0, five older docstring lines** above: each claim is made checkable from the library or
   says plainly what ran and that no file was kept.

Dustin pushes after claude-ai checks the result.

The statements, as elaborated in A2 to A5 (the plan's section 5 table is the source for the
mathematics; the Lean form is this order's). No new module.

- **96**, in `ClassicalLean.Probability.CovarianceDirections`, which gains
  `import ClassicalLean.Algebra.HadamardInequality`: Hadamard's inequality for a covariance matrix,
  the "generalised variance" is at most the product of the variances.

  ```
  theorem det_covMatrix_le_prod_variance [DecidableEq ι] [IsFiniteMeasure μ]
      (hX : ∀ i, MemLp (X i) 2 μ) :
      (covMatrix X μ).det ≤ ∏ i, variance (X i) μ
  ```

  **Wider than a probability-space reading:** any finite measure, as `posSemidef_covMatrix` asks.

- **97**, in `ClassicalLean.Probability.FiniteChain`: relative entropy to a stationary vector never
  increases along the chain.

  ```
  theorem relEntropy_vecMul_le_of_stationary {P : Matrix n n ℝ} {μ π : n → ℝ}
      (hP0 : ∀ i j, 0 ≤ P i j) (hP : ∀ i, ∑ j, P i j = 1) (hμ : ∀ i, 0 ≤ μ i)
      (hμπ : ∀ i, π i = 0 → μ i = 0) (hπ : π ᵥ* P = π) :
      ClassicalLean.Simplex.relEntropy (μ ᵥ* P) π ≤ ClassicalLean.Simplex.relEntropy μ π
  ```

  **Wider than the plan's reading** (claude-ai's ruling, Dustin's veto open): `π` need not be a law;
  no `π ≥ 0` and no total `1`. A stationary `π` of any sign gives the stationary `|π|`, and Lean's
  `relEntropy p q` depends on `q` only through `|q|` (check `97.signs` and its BY HAND line).

- **98**, in `ClassicalLean.Statistics.GeneralizedLeastSquares`, which gains
  `import ClassicalLean.Algebra.Kantorovich`: how much ordinary least squares loses against
  generalised least squares for a common mean, Bloomfield and Watson's bound in this case.

  ```
  theorem onesQuad_mul_onesInvOnes_le [Nonempty ι] {V : Matrix ι ι ℝ} {m M : ℝ} (hm : 0 < m)
      (hmV : (V - m • 1).PosSemidef) (hVM : (M • 1 - V).PosSemidef) :
      (1 ⬝ᵥ (V *ᵥ 1)) * onesInvOnes V / (Fintype.card ι : ℝ) ^ 2 ≤ (m + M) ^ 2 / (4 * m * M)
  ```

  `[Nonempty ι]` is needed: with no index Lean's left side is `0 / 0 = 0` while `M` may be negative
  (`98.drop.nonempty`).

- **99**, in `ClassicalLean.InformationTheory.CompressionTest`: item 68's plug-in argument in
  Lean. The definition is complete as A5 elaborates it (its two bounds proved there):

  ```
  noncomputable def winRate (x : Fin n → Bool) : unitInterval :=
    ⟨((univ.filter fun i ↦ x i = true).card : ℝ) / n, by positivity,
      div_le_one_of_le₀ (by exact_mod_cast (card_filter_le _ _).trans (by simp)) (by positivity)⟩

  theorem score_plugIn_le (c : (Fin n → Bool) → List Bool) (p : unitInterval) (x : Fin n → Bool)
      (hx : (bernProd n p).real {x} ≠ 0) :
      score c (bernProd n (winRate x)) x ≤ score c (bernProd n p) x

  theorem measureReal_score_plugIn_ge_le {c : (Fin n → Bool) → List Bool}
      (hc : Function.Injective c) (hpf : InformationTheory.IsPrefixFree (Set.range c))
      (p : unitInterval) {α : ℝ} (hα : 0 < α) :
      (bernProd n p).real {x | 1 / α ≤ score c (bernProd n (winRate x)) x} ≤ α
  ```

  `hx` is not a narrowing: the plan's sentence "a score at most every fixed-rate score" is false
  under Lean's junk value `2^(−L) / 0 = 0` when the fixed rate gives the string mass `0`
  (`99.drop.hx`), and the second theorem needs no such hypothesis (those strings have mass `0`
  under `bernProd n p`). The plan's names are kept; the plug-in score is written out, with no
  second definition.

- **100**, in `ClassicalLean.Probability.FiniteChain`: Perron–Frobenius for a primitive chain (some
  power of `P` has every entry positive, though `P` may have zeros).

  ```
  theorem existsUnique_vecMul_eq_self_of_pow [DecidableEq n] [Nonempty n] {P : Matrix n n ℝ}
      {k : ℕ} (hP : ∀ i, ∑ j, P i j = 1) (hpos : ∀ i j, 0 < (P ^ k) i j) :
      ∃! π : n → ℝ, ((∀ i, 0 ≤ π i) ∧ ∑ i, π i = 1) ∧ π ᵥ* P = π

  theorem sum_abs_vecMul_pow_sub_le_of_pow [DecidableEq n] {P : Matrix n n ℝ} {k : ℕ} {δ : ℝ}
      (hP0 : ∀ i j, 0 ≤ P i j) (hP : ∀ i, ∑ j, P i j = 1) (hδ : ∀ i j, δ ≤ (P ^ k) i j)
      {μ π : n → ℝ} (hμ : ∑ i, μ i = ∑ i, π i) (hπ : π ᵥ* P = π) (t : ℕ) :
      ∑ j, |(μ ᵥ* P ^ t) j - π j| ≤ (1 - Fintype.card n * δ) ^ (t / k) * ∑ j, |μ j - π j|
  ```

  **Wider than the plan's reading** (claude-ai's ruling, Dustin's veto open): the plan says "states
  its hypothesis with `Matrix.IsPrimitive` where it fits". It does not fit: `IsPrimitive` is not
  visible through FiniteChain's imports (facts), and it carries two conditions the uniqueness
  theorem does not need, `P ≥ 0` (`100.unique.neg`, and BY HAND) and `k > 0` (at `k = 0`, `P ^ 0 = 1`
  has every entry positive only with one state). Neither does the rate theorem need `k > 0`: Lean's
  `t / 0 = 0` makes the factor `1` (`100.k0`). The module docstring says that a primitive matrix
  in Mathlib's sense (`Matrix.IsPrimitive`) meets `hpos` through its field `exists_pos_pow`.

No result from below the plan's cut is pulled in.

## Scope

- **Branch.** `lean-30` from MERGE (master after MERGE-1's push) in
  `~/lean/classical-lean-paper-crypto`, made after Dustin approves your plan. Nothing pushed. No sudo.
- **You may change:**
  - the four modules named above (CovarianceDirections, FiniteChain, GeneralizedLeastSquares,
    CompressionTest; FiniteChain takes items 97 and 100), each gaining at most the one import line
    named for it (CompressionTest's only if you take item 99's route (b), and A1 says the module
    is in the closure);
  - for job 0, `ClassicalLean/NumberTheory/PrimitiveDivisor.lean` and
    `ClassicalLean/Analysis/Gruss.lean`: docstring and comment lines, and in PrimitiveDivisor at
    most one appended `example` (job 0); no theorem, definition, proof or existing `example`
    changes;
  - `tools/vacuity_reviewed.txt` (job 2's 2c only), `records/`, and `HANDOFF.md` and `ROADMAP.md`
    (job 3).
- **You may not change** anything else under `ClassicalLean/` or `tools/`, or `ClassicalLean.lean`
  (no new module). Needing to is a stop.
- **Off limits:** the main clone's working tree `~/lean/classical-lean` and its `master` (the
  nightly's clone). The worktree shares the main clone's `.git`, so `git fetch`, your branch and
  your commits are written there; that is expected. Also off limits: anything under `~/trading`
  or `~/lean/recheck` (`run-recheck.sh` is run, as gate 7, not edited).
  `~/.config/classical-lean/banned-terms` is Dustin's: never edit it, never copy its patterns.
- **The night window.**
  - Start nothing that loads the library and could still be running at 02:00 EDT.
  - Start nothing that loads the library between 02:00 and 05:45 EDT (the night jobs in the facts;
    gate 7 takes about 20 minutes).
  - Do not start a whole-library run in the 15 minutes before the 00:00 `memory-index` timer.
  - Check `crontab -l` and both `systemctl list-timers` lists again before you start.
  - Reading, hash checks and records commits may run inside the window.
  - If a step that loads Lean comes due inside the window, stop and tell Dustin in one line.
- **The memory cap.**
  - Every run that loads the whole library goes under
    `systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0 <command>`: a full build, the
    gate, a whole-library census, the plan's checks with `--lean`, the report tool,
    `tools/bridge_search.py` and gate 7.
  - A run the cap kills is a stop.
  - Never run two whole-library runs at once, a reviewer's included.
  - A non-interactive shell on DSMain may lack `~/.elan/bin` in `PATH` (measured over ssh: "Failed
    to find executable lake"); put it there or call `~/.elan/bin/lake`.
- **Your plan** goes to `lean/LEAN-30-PLAN.md` (then -PLAN-2, never overwriting). Report its
  sha256.

## Check, then read

Check these sha256s first; if any differs, stop and say which:
- this order, `lean/LEAN-30-order.md`: the value in Dustin's prompt;
- `lean/LEAN-30-checks.py` `6af2e0421ffd01df5a8ea28f094945b2173b5729356c3ac500e06fc3c02ddcf7`;
- MATH-PLAN-library-2.md `6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166`;
- MATH-PLAN-library-2-checks.py `92eedbc6598361a06a50bdf3a1b4fa1698c1d1d7a3dfe783cc79dd9c1c38307e`;
- MATH-PLAN-library-2-bridges-2.md `f0aa214a6d747e6c5a95979cd329fbca85e046a303089e3e70d8aa8c20320119`;
- `lean/LEAN-29-order.md` `e878aca2d617e65af38de731ec7223ae6c0125cf47f8b9d2f45affb26c0b3151`;
- `lean/LEAN-29-report.md` `89ebe00492ded3c6a01fe07fb5f0623dbaa19e4ae8da443c7005cc9c348b167f`;
- `lean/LEAN-29-ruling-2.md` `25423b160efdf912beb555be57ad53987f35e3ed9f02eb0583b5c05554cc065f`;
- `lean/VACUITY-3-ruling-3.md` `aa0d17e403031b81d0e0803c3308002ed985b416d788980de0f61cc79e13a4f2`;
- `lean/NOTE-20261015-task-list-rule.md`
  `76cfb510d0023c0c8cb2e843877417c387fe05b92f9ef5dfbe24dc18457194ef`;
- LEAN-16-order.md `d494728c561a922b1227587395f9650f33dd3182791620e7a0d0fb6469f3120e`;
- in the repository at MERGE (measured at `92a314c`; MERGE-1 changes none of these files):
  - `ClassicalLean/Probability/CovarianceDirections.lean`
    `8372fb3343dcc5048bbd3df77b6ead2edb3fbd45a3c8e8933c353f897d816c2b`;
  - `ClassicalLean/Algebra/HadamardInequality.lean`
    `131a4d76775987ed10158d9d87f4c2b39ff4359878dc8940007c394c341fa652`;
  - `ClassicalLean/Probability/FiniteChain.lean`
    `e48978582752d9f1b4a11f28062f42a3142ca39429b3be91433997f142073130`;
  - `ClassicalLean/InformationTheory/Channel.lean`
    `7d0fed1182b96be53f8f1249c44ed9fdc9781f0b969a652cda2dae0fb9bd8bf3`;
  - `ClassicalLean/Statistics/GeneralizedLeastSquares.lean`
    `47684627fc4046f517d3f46f92bfa5dce84fa81a493babe4ea6b71b43043acd6`;
  - `ClassicalLean/Algebra/Kantorovich.lean`
    `67e03d7994f2d89b441adb71f105b2406cf2525db0dad4c8b0ff33fc91964a52`;
  - `ClassicalLean/Analysis/MinimumQuadraticForm.lean`
    `94cc728e76e00b5a441ff66e02400ae9a7ddcbc0efca1375346de06189c26bdc`;
  - `ClassicalLean/InformationTheory/Entropy.lean`
    `06bfd59f71b5056ca8d44b0d8b3a70b1299b330d91d5f3272b6cbfe72938d29f`;
  - `ClassicalLean/InformationTheory/CompressionTest.lean`
    `2d6d8e35b1e4f40f0e9d3d0199afdaa0379591b1630e19121122f1962b6d0d16`;
  - `ClassicalLean/NumberTheory/PrimitiveDivisor.lean`
    `ce75ce40e7be06309cc02f6940d813c29b1fda002bb622cb6b8e7e3c9af95fbf`;
  - `ClassicalLean/Analysis/Gruss.lean`
    `a7ec5f04898296e8e579d9a8714b38794bf0ff8c5a7a5a75095ea7cbc9c73235`;
  - `tools/vacuity_reviewed.txt`
    `b5d168d4474375cbba3d5fd29948da316109b4323fa768af433b71df29fa8bde`.

Then read (also `HANDOFF.md` at MERGE, which MERGE-1 changed; its sha256 at `92a314c` was
`00fd5a465fa1e1ed3102deb732513e91d67d9def77f756a7aeada83f9de30d75`):
- **In the lane:**
  - `lean/MERGE-1-order.md` (sha256 above) and `lean/MERGE-1-report.md` (the counts after MERGE);
  - MATH-PLAN-library-2.md: section 5's "Batch 4" table, section 6's rows 96 to 100, section 7's
    table header, and section 8 in full;
  - LEAN-29-order.md's sections "Scope", "Rules for this order", "Setup", "Job 2" and "Job 4" (this
    order follows them where it does not say otherwise), and LEAN-29-report.md in full (the
    report's model);
  - LEAN-29-ruling-2.md (the four points this order answers);
  - VACUITY-3-ruling-3.md in full (the witness form and rule 3's two cases);
  - MATH-PLAN-library-2-bridges-2.md (rows 154 to 156);
  - the "Known traps" section of LEAN-16-order.md;
  - `lean/README.md`;
  - `lean/LEAN-30-checks.py`'s docstring (its predictions are this order's exact rows).
- **In the repository:** HANDOFF.md §4 and §6 (rules 17, 18, 20, 27 and 31 apply: reviewer outputs
  saved verbatim with their sha256; records follow the clock; scratch files elaborated with the
  lakefile's options; a count Lean generates predicted by a Lean measurement; no statement drafted
  before its searches and cells, which this order and its checks supply), records/README.md, round
  59's fragment, and the sources of the four homes, of HadamardInequality, Channel, Kantorovich,
  MinimumQuadraticForm, PrimitiveDivisor and Gruss.

Which steps of the plan's section 8 apply: all of them, with the gates of step 9 as LEAN-29 ran
them (six: build, AxiomGate, VacuityGate, check_sorry, check_records, gate 7).

## Rules for this order

1. **The gate as LEAN-29 left it** (HANDOFF.md §4, read as MERGE leaves it). A flag or an UNCHECKED verdict on a main
   theorem is a stop. On a helper: rewrite it, remove it if Mathlib or `simp` already does its job,
   or list it in `tools/vacuity_reviewed.txt` as HELPER with a one-line reason its module's cold
   reviewer checks (2c). A VACUOUS-PENDING entry is a stop. The known gap stays: a recursive
   all-`True` predicate (`NatT2`) passes silently; each module's cold reviewer checks that no main
   theorem's conclusion is such a predicate and says so, and the report tool's section C after the
   work still shows 0 recursive.
2. **Witnesses, in round 58's standing form, as HANDOFF.md §4 now files it** (with LEAN-29's
   dated paragraph): every new main theorem with a hypothesis gets an `example` after the module's
   last line that applies the theorem itself, `example := Full.name (x := …) h₁ h₂ …`, every
   chosen argument by name, optional `open … in` lines of their own, the docstring "The
   hypotheses of `name` hold together: …", no `sorry`, `admit`, `native_decide`,
   `implemented_by`, `axiom` or `set_option`, one inline block with no helper declarations; not
   degenerate (rule 3), with ruling 3's two cases: no hypothesis met only because a function is
   identically `0` past some point, and no kernel or observation that fails to depend on the
   parameter it is about. **Seven witnesses are owed:** 96, 97, 98, both of 99, both of 100.
3. **A claim in the library is checkable from the library** (store row 20261013-014). No
   docstring or comment in a module says a case was "checked in Lean", "elaborated" or "`#check`
   resolves" unless the check is an `example` in the module, with one exception, job 0's: a
   docstring may report a past run if it says plainly that it is a past run, names the commit that
   first wrote the claim (from `git log -S`) and says no file was kept. Records, commit messages
   and the report may cite a run, by its evidence label (rule 8). A dropped-hypothesis row's evidence is
   one of: an `example` in the module; a labelled line of `lean/LEAN-30-checks.py` or of your own
   checks script, named by label; or "by hand", said so.
4. **Narrowing and widening are said the same way everywhere.** Before the last records commit,
   the INDEX row, round 62's completed section and the report's "In short" each name every
   narrowing of this order, or say "none", and each names the five widenings of items 96, 97 and
   100 (Goal). Check it on the report's draft: `grep -n -i -E 'narrow|widen|wider' <round 62
   fragment> <report draft>` and `grep -n -i -E 'narrow|widen|wider' records/orders/INDEX.md |
   grep 'LEAN-30'`; paste the output into the report. INDEX rows start `| LEAN-NN |`.
5. **Method A carries LEAN-29's lesson:** Simpson's four `field_simp` calls made 7 `_simp_`
   helpers where 4 were estimated (LEAN-29's miss of 3), after LEAN-28's 8 for 2. Count each
   `field_simp` and `simp` that closes an equation as likely to make helpers, and give a range.
6. **A question to Dustin holds only its own outcome open.** Don't apply your own answer before he
   replies; the work it does not touch goes on.
7. **Stops inside an item.** A witness still missing after about 30 minutes of attempts, or a
   module not clean after two fix-and-confirm review rounds, makes that item not closed: its
   changes are reverted before job 3 and the other items go on. FiniteChain holds items 97 and 100
   under one review: if it is not clean after two rounds, revert the item whose lines the open
   findings touch, and both if they touch both or you cannot tell. A finding after the second round
   that needs a change only inside docstrings or comments is fixed, not reverted, as LEAN-29's
   ruling 1 sets out (a code-only comparison with a negative control, a rebuild with 0 warnings,
   one fresh reviewer on that diff alone, reported as "third fix, docstrings only"). Never weaken,
   restate or add a hypothesis to get a witness; the stop rules of items 97 and 100 below are the
   only planned restatements.
8. **A commit message says only what the evidence log shows** (new; filed as HANDOFF.md §6 rule
   35 in job 3). LEAN-29's `2bba7b6` said item 92's names "were probed first (el.sh p92-1)"; the
   probe had failed on three names and two of the names used were never probed by `#check`
   (LEAN-29's review r92, finding 4); and the fix commit `54c3624` restated it with a quotation
   cut without a mark and left out the run that confirmed the names (review r92c, findings A and
   B). So: every Mathlib or library
   name a proof uses that Appendix A does not probe gets a logged `#check` probe before the first
   draft that uses it, and a commit message that cites a run names its evidence label and claims
   only what that run's output shows.

## Before approval (read-only in the repository)

1. `git fetch origin` in the worktree. Then, each predicted and checked:
   - origin/master and `git ls-remote github master` are the same commit MERGE, and MERGE is the
     HEAD that `lean/MERGE-1-push-review.txt` records (and MERGE-1's report names as pushed);
   - `git merge-base --is-ancestor 92a314c49fec6af16aefabcfd37cd6dbcb32d832 MERGE` and
     `git merge-base --is-ancestor d7756afae16c6e00424589d8a020315f24eb95be MERGE` (MERGE-1's cloud
     tip, `cloud-math-1`) both exit 0;
   - `git diff --name-only 92a314c MERGE` (the whole tree) lists only MERGE-1's declared set: the
     five cloud modules (facts), `ClassicalLean.lean`, `.github/workflows/ci.yml`, files under
     `records/`, `HANDOFF.md` and `ROADMAP.md`;
   - `git show MERGE:lean-toolchain` is `leanprover/lean4:v4.34.0`, and the Mathlib `rev` in
     `git show MERGE:lake-manifest.json` is `5ed2965256430c3649e86755f9576b54eca72435`;
   - `git status --porcelain` is empty.
   If MERGE-1 is not pushed yet, or any check differs, stop and report. Report MERGE's full hash.
2. Check the hashes above and read the read list.
3. Check the night jobs and `free -g`.
4. Write your plan to `lean/LEAN-30-PLAN.md`: the jobs in order, every prediction you can already
   make, and the order of the items; and the plan-fit check (rule 16): for each of items 96 to 100,
   section 5's row of MATH-PLAN-library-2.md beside A2 to A5's statement, with every difference
   named (the five widenings, item 99's `hx` and `winRate`, item 100's form without
   `Matrix.IsPrimitive`) and anything else you find. Then stop and wait for Dustin's approval.

## Setup (after approval)

1. **Branch.** `git switch -c lean-30 <MERGE's full hash>`.
2. **Evidence folder** `~/lean/lean30-checks/`, with `evidence.log` (time, label, rc, prediction,
   command). Every prediction file is hashed into the log before the run it predicts; hashes go
   into records and the report by script, never typed; every compile-fix run through `el.sh` is
   logged; every refused or not-run call is logged `NOT RUN` (HANDOFF.md §6 rule 30). Extract
   Appendix A's six files byte for byte into `~/lean/lean30-checks/appendix/` and check their
   sha256 against the appendix.
3. **Records first.** The first commit on `lean-30`, with no `.lean` file:
   - this order's copy as
     `records/orders/<UTC>__claude-ai__order-lean30-hadamard-cov-chain-entropy-bloomfield-plugin-perron.md`;
   - its INDEX row and a CLAIMS row;
   - round 62's fragment, which names in full every module file this order changes.
   check_records then: PASS 128 (or MERGE-1's measured count).
4. **The before runs, at the records commit**, predicted from the facts:
   - build rc 0, 4176 jobs (MERGE-1's), 0 warnings;
   - AxiomGate PASS 3335 (MERGE-1's): the base for job 1's blind prediction;
   - the report tool, rc 0, with the counts of MERGE-1's report (its job 4c); at `92a314c` they
     were 1792 written; A 1033 (0 / 994 / 39); B 759 (16 close); C 33, 0 recursive; saved as
     `report-before.out` for job 4b.
5. **The plan's checks**, with `--lean`, using `~/lean/vacuity2-checks/mm` (at `2da3ab0a`).
   Predicted: every line of rows 96 to 100 a hit; the misses those of the facts at `92a314c`
   (copy the list into your prediction file line by line; `setup.worktree`'s measured value will be
   your records commit), changed only where MERGE-1's five modules move a count (`setup.modules`,
   the `census.*`, `used.*` and `bridges.*` lines, and any row line whose library search now finds
   a cloud module's words): write each such change into the prediction before the run. A miss on
   a row 96 to 100 line whose new library matches are all in the five cloud modules is such a
   predicted change, not a drop: grep those matches and show they do not prove the row. Only a miss on a row 96 to 100 line
   means Mathlib or the library has that row by now: drop that row and say so. A `setup.*`,
   `gate.*`, `census.*`, `used.*` or `bridges.*` miss never drops a row.
6. **The exact checks:** `python3 -I` on the lane's `lean/LEAN-30-checks.py`. Predicted: 38 of 38
   checks hit, 4 BY HAND lines, rc 0, output sha256 `1ff937bade285f225176771c5bbe63746789394b63356e77d118cc7a3c2ba310` (claude-ai's run on DSMain from the lane copy gave exactly that). A
   different output hash with 38 of 38 is reported, not a stop.
7. **The statements:** elaborate A2 to A5 from the worktree root with rule 20's four flags
   (`lake env lean -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false
   -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3`), and A6. Predicted: A2 to A5
   rc 0 each, and only `declaration uses sorry` warnings, 1, 3, 1, 2; A6 rc 1, "Unknown
   identifier" (unless item 99's route (b) import is already in place, which it is not at setup).

## The work

Job 0 comes first; it touches no statement of items 96 to 100. Items 96 to 100 then go through
jobs 1 to 4 together. A suggested order, easiest first: 96, 98, 97, 100, 99.

### Job 0: five older docstring lines (LEAN-29's review j0, finding 1; review r92c, a note)

- **PrimitiveDivisor.** For each of the four passages, find with `git log -S` the commit that
  first wrote it and say what you find (LEAN-29's facts found line 286's text first in `333b69a`,
  the library's initial commit of 2026-10-07). Then:
  - line 98 reports a successful `#check`: either state it as an `example` appended after the
    module's last line, if the names resolve against the module's own imports (for example
    `example := @Nat.emultiplicity_pow_sub_pow`), or reword it as a past run with no file kept;
  - line 265 reports a failing elaboration, which no `example` can show: reword it "by hand:
    `isRoot_cyclotomic_iff` asks `IsDomain (ZMod p)`, which Mathlib supplies from `Fact p.Prime`"
    if a logged `#check` of `isRoot_cyclotomic_iff` shows that signature, or as a past run;
  - lines 346 to 348 report a failing elaboration, and lines 348 to 350 a successful one in a file
    that imports a module this one does not: neither can be an `example` here; reword both as past
    runs with no file kept.
  The dated note at lines 81 to 88 says the paragraphs below it are "kept as written"; add one
  dated sentence there saying that order LEAN-30 reworded only these claims of what was checked.
- **Gruss, lines 41 to 43.** One bracket, so the source of "needed only together" is not
  misread: for example "... needed only together, below (order LEAN-29's exact checks, ...)".
- Neither module's theorems, definitions, proofs, existing `example`s or count of theorem
  constants changes; check that by a census of the two modules before and after (LEAN-28's
  `census3_*` method), predicted equal, and by a code-only comparison of each file (comments and
  docstrings stripped; an appended `example` set aside and named) before and after, predicted
  equal, with a negative control (a one-word code change must be detected).
- One fresh cold reviewer reads the diff of the two files only, with this section as its brief,
  about 15 calls; its confirming pass closes the job.

### Item 96, `ClassicalLean.Probability.CovarianceDirections`

- **Import:** add `import ClassicalLean.Algebra.HadamardInequality` (facts: in the closure, no
  cycle).
- **Route** (A2 probes every name): `det_le_prod_diag (posSemidef_covMatrix hX)`; each diagonal
  entry `covMatrix X μ i i = cov[X i, X i; μ]` (by definition) is `variance (X i) μ` by
  `covariance_self (hX i).aemeasurable`; `Finset.prod_congr`. `posSemidef_covMatrix` asks
  `[Finite ι]`, which `[Fintype ι]` gives. Place the theorem after `posSemidef_covMatrix`.
- **Rows:**
  - `hX`, by hand, with the determinant as exact algebra (`96.drop.L2` checks `2 c₁₂ c₁₃ c₂₃` at
    `c = 1`; the construction's covariances are generic positive numbers): three variables on
    `[0, 1]` with Lebesgue
    measure, each integrable but not square-integrable, whose pairwise covariances are integrable
    and positive (the BY HAND line builds them); Lean's `cov[X k, X k]` is `0` (the integral of a
    function that is not integrable) and so is `variance` (`evariance` is `∞`, and `∞.toReal = 0`),
    so the covariance matrix has zero diagonal and `det = 2 c₁₂ c₁₃ c₂₃ > 0 = ∏ Var`.
  - `IsFiniteMeasure`, by hand with an exact matrix (`96.drop.fin`): Lebesgue measure on `ℝ`,
    `X₁ = 1_[0,1]`, `X₂ = 1_[1,2]`, `X₃ = 1_[0,1] − 1_[2,3]`, `X₄ = 1_[1,2] − 1_[3,4]`, all in `L²`;
    `X₁` and `X₂` have mean `1`, so `(X − 1)²` is not integrable on `ℝ` and their covariances with
    themselves and each other are Lean's `0`, as are their variances; the matrix is
    `[[0,0,1,0],[0,0,0,1],[1,0,2,0],[0,1,0,2]]`, `det = 1 > 0 = ∏ Var`.
  - Junk values deciding both rows: the Bochner integral of a non-integrable function is `0`;
    `variance` is `(evariance …).toReal`, `0` at `∞`.
- **Exact cases:** `96.hadamard` (200 Gram matrices), `96.cov` (150 finite laws, masses `1/2`, `1`,
  `3`).
- **Witness:** at least two variables that are not proportional on a space of at least three
  points, so the covariance matrix is not singular; for example `ι = Fin 2`, `Ω = Fin 3` with
  `uniformOn Set.univ` (a probability measure, hence finite) or `Measure.count`, `X 0` and `X 1`
  the indicators of two different points. `MemLp` on a finite space: find the lemma and probe it.

### Item 98, `ClassicalLean.Statistics.GeneralizedLeastSquares`

- **Import:** add `import ClassicalLean.Algebra.Kantorovich` (facts).
- **Route** (A4): `ClassicalLean.Algebra.Kantorovich.dotProduct_mulVec_mul_inv_le hm hmV hVM 1`;
  `onesInvOnes V` is `1 ⬝ᵥ (V⁻¹ *ᵥ 1)` by definition; `one_dotProduct_one` (root namespace) gives
  `1 ⬝ᵥ 1 = Fintype.card ι`; `Fintype.card_pos` from `[Nonempty ι]`; `div_le_iff₀`.
- **Rows** (all exact): `hm`, `98.drop.hm` (`V = (1)`, `m = 0`, `M = 1`: left side `1` against
  Lean's `1 / 0 = 0`); `hmV`, `98.drop.hmV` (`V = diag(1, 4)`, `m = 2`, `M = 4`: `25/16` against
  `9/8`); `hVM`, `98.drop.hVM` (`V = diag(1, 4)`, `m = 1`, `M = 2`: `25/16` against `9/8`);
  `[Nonempty ι]`, `98.drop.nonempty` (no index, `m = 1`, `M = −2`: `0` against `−1/8`). Junk values:
  `x / 0 = 0` in the bound (row `hm`) and on the left (row `Nonempty`).
- **Exact cases:** `98.random` (200 `V = H D H`), `98.equal` (equality at `V = diag(m, M)`, `n = 2`,
  the plan's "equal mix" case).
- **Witness:** `ι = Fin 2`, `V = !![2, 1; 1, 3]`, `m = 1`, `M = 4` (cold review 1's choice,
  `98.witness`): `V − 1 = !![1, 1; 1, 2]` and `4 • 1 − V = !![2, -1; -1, 1]` are positive
  semidefinite (each has determinant `1` and positive diagonal), and the left side `21/20` lies
  strictly between `1` and the bound `25/16`, so ordinary least squares does lose something. (With
  `!![2, 1; 1, 2]` the vector of ones is an eigenvector and the left side is exactly `1`.) A
  diagonal `V` is allowed if the semidefinite proofs do not close within the 30 minutes, said in
  the docstring (`V = diag(m, M)` is the equality case, not a degenerate one).

### Item 97, `ClassicalLean.Probability.FiniteChain`

- **Route** (A3): put `q = |π|` (as a function, `fun i ↦ |π i|`).
  - `|π| ᵥ* P = |π|`: entrywise `|π| ᵥ* P ≥ |π ᵥ* P| = |π|` (`Finset.abs_sum_le_sum_abs`, `hP0`),
    and both sides have the same total (`ClassicalLean.Simplex.sum_vecMul_eq_sum hP`), so they are
    equal (`Finset.sum_eq_sum_iff_of_le`).
  - `relEntropy p π = relEntropy p |π|` for every `p`: termwise `Real.log (a / b) =
    Real.log (a / |b|)`, both being `Real.log (|a| / |b|)` (`Real.log_abs`, `abs_div`), and both
    `0` at `b = 0`.
  - Then `ClassicalLean.Simplex.relEntropy_vecMul_le` with `p = μ`, `q = |π|`, `W = P` (its
    `hpq` from `hμπ`, since `|π i| = 0 ↔ π i = 0`), and rewrite `|π| ᵥ* P = |π|`.
  - **Stop rule:** if the `|π|` step does not close within about 30 minutes, add
    `(hπ0 : ∀ i, 0 ≤ π i)`, which is the plan's reading, say so as a narrowing of this order's
    statement (not of the plan's), and go on.
- **Rows** (`LEAN-30-checks.py`, FLOAT, each gap at least `0.1`): `hP0`, `97.drop.hP0`
  (`P = [[3/2, −1/2], [−1/2, 3/2]]`, `π = (1/2, 1/2)`, `μ = (1, 0)`: `1.648` against `0.693`; junk:
  `Real.log` of a negative number is the log of its absolute value); `hP`, `97.drop.hP`
  (`P = [[1, 1], [0, 0]]`: `1.386` against `0.693`); `hμ`, `97.drop.hmu` (`μ = (−1, 0)`: `0` against
  `−0.693`; junk: `Real.log (−1) = 0`); `hμπ`, `97.drop.hmupi` (`P = [[1, 0], [1, 0]]`, `π = (1, 0)`,
  `μ = (1/2, 1/2)`: `0` against `−0.347`; junk: `x / 0 = 0` and `Real.log 0 = 0` make the term at
  `π i = 0` vanish; the plan's own case `μ = (1/e, 1 − 1/e)` fails the same way); `hπ`,
  `97.drop.hpi` (`π = (1/2, 1/2)` not stationary for `P = [[1, 0], [1, 0]]`: `0.693` against `0`).
  No `π ≥ 0`: `97.signs` and its BY HAND line.
- **Exact cases:** `97.random` (300 chains, FLOAT), `97.signs` (100, FLOAT).
- **Witness:** `P = !![1/2, 1/2; 1/4, 3/4]`, the stationary `π = ![1/3, 2/3]`, `μ = ![1, 0]` (not
  stationary, so the two sides differ).
- **Docstring:** name the plan's reading (the "H-theorem" for a finite chain: relative entropy to
  the stationary law never increases) as a reading.

### Item 100, `ClassicalLean.Probability.FiniteChain`

- **Route, uniqueness** (A3): put `Q = P ^ k`; its rows sum to `1` (the module's private
  `sum_pow_apply_eq_one`); `δ`, the least entry of `Q`, is `> 0` (`Finite.exists_min`, or
  `Finset.univ.inf'`); `existsUnique_vecMul_eq_self` for `Q` gives a law `π*` with
  `π* ᵥ* Q = π*`. Then `π* ᵥ* P` is also fixed by `Q` (`Q * P = P * Q`) and has total `1`, so
  `d = π* ᵥ* P − π*` has `∑ d = 0` and `d ᵥ* Q = d`; `sum_abs_vecMul_le` for `Q` (it allows `d` of
  any sign) gives `n δ ∑ |d| ≤ 0`, so `d = 0`. Any law `π` with `π ᵥ* P = π` has `π ᵥ* Q = π`,
  so it is `π*`. Nowhere is `P ≥ 0` used, and `k = 0` needs no case (with two or more states
  `hpos` is false at `k = 0`; with one, `P = 1`).
- **Route, rate** (A3): `t = k * (t / k) + t % k` (`Nat.div_add_mod`), so `P ^ t = (P ^ k) ^ (t / k)
  * P ^ (t % k)` (`pow_add`, `pow_mul`). Apply `sum_abs_vecMul_pow_sub_le` to `Q = P ^ k` (rows sum
  to `1`, entries at least `δ`, `π ᵥ* Q = π`) for the `(t / k)` steps first, then
  `sum_abs_vecMul_pow_le` with `δ = 0` for the remaining `t % k` steps of `P` applied to
  `μ ᵥ* Q ^ (t / k) − π` (its total is `0`), which gives factor `1`. In that order no sign of
  `1 − n δ` is needed. At `k = 0` the same formula holds (`t / 0 = 0`, `t % 0 = t`).
  - **Stop rule:** if uniqueness without `P ≥ 0` does not close within about 30 minutes, add
    `(hP0 : ∀ i j, 0 ≤ P i j)` to it, which is the plan's reading (`IsPrimitive`'s `nonneg`), say
    so as a narrowing of this order's statement, and go on.
- **Rows, uniqueness** (exact): `hP`, `100.drop.u.hP` (`P` all `1`, `k = 1`: no stationary vector
  of total `1`); `hpos`, `100.drop.u.hpos` (`P = 1`, two states: `(1, 0)` and `(0, 1)`);
  `[Nonempty n]`, `100.drop.u.nonempty`. No `P ≥ 0` (`100.unique.neg`, BY HAND), no `k > 0` (BY
  HAND, the same line).
- **Rows, rate** (exact): `hP0`, `100.drop.r.hP0` (`P = [[3/2, −1/2], [−1/2, 3/2]]`, `k = 2`,
  `δ = −3/2`, `t = 1`: `2` against `1`); `hP`, `100.drop.r.hP` (`P = 2 • 1`: `4` against `2`); `hδ`,
  `100.drop.r.hdelta` (`P = 1`, `δ = 1/2`: `2` against `0`); `hμ`, `100.drop.r.hmu`; `hπ`,
  `100.drop.r.hpi`. No `k > 0`: `100.k0` (junk `t / 0 = 0`).
- **Exact cases:** `100.unique` (200 chains with a zero entry), `100.unique.neg` (100 chains with a
  negative entry), `100.rate` (200 chains, `t ≤ 12`).
- **Witnesses:** `P = !![0, 1; 1/2, 1/2]` (a zero entry, so `existsUnique_vecMul_eq_self` does not
  apply), `k = 2` (`P ^ 2 = !![1/2, 1/2; 1/4, 3/4]`); for the rate also `δ = 1/4`, `μ = ![1, 0]`,
  `π = ![1/3, 2/3]`, `t = 5` (the plan's check `L7.primitive` is this chain).
- **Docstring:** the module's "Mathlib at v4.34.0" paragraph gains this order's search
  (`row.L7`) and the sentence that Mathlib's `Matrix.IsPrimitive` meets `hpos` through
  `exists_pos_pow` (named, not imported).

### Item 99, `ClassicalLean.InformationTheory.CompressionTest`

- **The definition** `winRate` exactly as above; put it and the two theorems after
  `measureReal_len_add_le_le`, before section `EBH`.
- **Route, `score_plugIn_le`** (A5): the heart is `p ^ k (1 − p) ^ (n − k) ≤ p̂ ^ k (1 − p̂) ^ (n − k)`
  for `p̂ = k / n` (`99.ml`), where `bernProd_real_singleton` and `Finset.prod_ite` turn the masses
  into these products (`k` wins, `n − k` losses). Two routes; use either and say which:
  - (a) weighted AM–GM, `Real.geom_mean_le_arith_mean2_weighted` (visible, A5) with weights `k/n`,
    `(n−k)/n` and points `p / p̂`, `(1 − p) / (1 − p̂)`, raised to the power `n`; the cases `p̂ = 0`
    and `p̂ = 1` (and `n = 0`) are direct, the plug-in mass being `1`;
  - (b) Gibbs's inequality, the library's `relEntropy_nonneg` on the two-point laws `(p̂, 1 − p̂)`
    and `(p, 1 − p)`, which needs `import ClassicalLean.InformationTheory.Entropy` in
    CompressionTest (in the closure, A1; not visible now, `P99.lean`): run A1 with it and say what
    the bridge prediction loses.
  Then the score: both have the same numerator `2⁻¹ ^ (c x).length`, and the fixed mass is
  positive (`hx`), so `div_le_div_of_nonneg_left`.
- **Route, `measureReal_score_plugIn_ge_le`:** the set `{x | 1 / α ≤ plug-in score}` lies inside
  `{x | 1 / α ≤ score c (bernProd n p) x} ∪ {x | (bernProd n p).real {x} = 0}`
  (`score_plugIn_le`); the first has chance at most `α` (`measureReal_score_bernProd_ge_le`); the
  second is a finite set of strings each of mass `0`, so mass `0`; `measureReal_union_le`,
  `measureReal_mono`.
- **Rows:** `score_plugIn_le`: `hx`, `99.drop.hx` (`n = 1`, `p = 0`, the string "win", length `1`:
  plug-in `1/2` against Lean's `2⁻¹ / 0 = 0`). `measureReal_score_plugIn_ge_le`: `hc`,
  `99.drop.hc` (every string of length `2` sent to `[]`, fair coin, `α = 1/4`: chance `1/2`);
  `hpf`, `99.drop.hpf` (`n = 3`, the injective words `[]`, `[0]`, `[1]` on the first three
  strings with both a win and a loss, Kraft sum `25/8`; fair coin, `α = 1/3`: chance `3/8`); `hα`,
  `99.drop.halpha` (`α = 0`: Lean's `1 / 0 = 0`, chance `1`). The check uses word lengths (only
  Kraft's inequality enters the proof); a row that names a code gives the words. Junk values: the
  plug-in rate at `n = 0` is Lean's `0 / 0 = 0` (one empty string, mass `1` under every rate, so it
  decides nothing; say so).
- **Exact cases:** `99.ml` (`n ≤ 10`), `99.score` (`n ≤ 6`), `99.rate` (`n ≤ 8`, every `p` of a
  grid with `0` and `1`, five levels `α`, two Kraft codes).
- **Witnesses:** `score_plugIn_le`: `n = 2`, `c = fun x ↦ [x 0, x 1]`, `p = ⟨1/3, …⟩`,
  `x = ![true, false]`: the fixed mass is `2/9 ≠ 0` (`bernProd_real_singleton`) and below the
  plug-in mass `1/4`, so the inequality is strict there (`99.witness`, cold review 1's choice). `measureReal_score_plugIn_ge_le`:
  `n = 2`, the same code, whose two hypotheses the module's witness of
  `sum_inv_two_pow_length_le_one` already proves, `p` a rate other than `1/2` and `0`, `1` (for
  example `⟨1/3, …⟩`), `α = 1/2`.
- **Docstring:** the paragraph "Estimating `p` from the same trades" names the two theorems where
  it now says "This argument is by hand, not proved in Lean"; the C8 and C9 checks it cites stay as
  they are.

### Job 1, predictions (section 8, step 4)

- **The job count:** inferred MERGE-1's 4176 (no new module; at `92a314c` the closure was
  9032 → 9032 with the new import lines, A1). Confirm by A1 at MERGE with the import lines as you
  finally write them, before any build.
- **The theorem constants, blind:** Method A from the source, then Method B by a census of scratch
  copies, both before any gate; base MERGE-1's 3335; rule 5. Job 0 adds none.
- **The bridge diff** before its run (job 4a): the two listed pairs that the new import edges make
  related (ranks 127 and 129 in LEAN-29's baseline; find them in `records/bridges/MERGE-1/`) and
  the two "unrelated" shape lines that become related (facts);
  if item 99 takes route (b), also CompressionTest's pairs with Entropy and the modules Entropy
  imports (measure with `grep` on `pairs.tsv` before the run); new pairs from the new constants;
  pairs gone because shared constants cross the document-frequency cut (LEAN-29: 18 such).
- **The plan's checks after the work** are not re-run as a gate. If you re-run them, expect the
  library counts of `row.X6`, `row.X8`, `row.X16`, `row.L3` and `row.L7` to turn into misses as
  the new docstrings use their words.

### Job 2, statements, hypotheses and reviews (section 8, steps 5 to 8)

Start from A2 to A5 (the statements are final there unless a review changes them). With:
- **2a.** Every new main theorem with a hypothesis gets its witness (rule 2), checked by its
  module's cold reviewer against rule 3 with ruling 3's two cases.
- **2b.** Lean's junk values named in every row where they decide the case (the rows above name
  them).
- **2c.** A vacuity flag on a short helper that only restates a definition is not a stop: remove
  it, or list it as HELPER (rule 1). A flag or UNCHECKED on a main theorem, or a VACUOUS-PENDING
  entry, is a stop.
- **2d.** Every review ends with a confirming pass on the fix diff only; at most two
  fix-and-confirm rounds (rule 7). A reviewer may elaborate at most two small Lean files, each
  under `systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=0`. A witness or a docstring
  that comes from a reviewer gets its confirming pass from a different, fresh reviewer (VACUITY-3's
  ruling 2). FiniteChain holds two items; one cold review covers both, after both are proved.
  HANDOFF.md §6 rule 16's statement review for this order's statements is its two cold reviews of
  A2 to A5 together with your plan's plan-fit check, closed by Dustin's approval; a statement you
  change gets a statement-equivalence review before its proof.
- **2e.** A narrower statement than this order's is said plainly in the module docstring, the
  report's item line and the hypothesis table, and rule 4 holds. A row whose statement turns out
  false is reported with its counterexample and narrowed, never dropped silently.
- **2f.** Each new theorem's docstring names the plan's item, and each module docstring's list of
  results gains the new theorems (and `winRate`).

### Job 3, documents

- `HANDOFF.md` (as MERGE-1 left it):
  - §1, a dated LEAN-30 paragraph with the counts;
  - §4's witness paragraph: "an optional `open … in` line of its own" becomes "optional `open …
    in` lines of their own", dated, citing lane `lean/LEAN-29-ruling-2.md` (note 2: VACUITY-3's
    `49bcd41` and LEAN-29's item 91 witness use two such lines, and passed their reviews);
  - §6, the next free rule number at MERGE (35 if MERGE-1 added no numbered rule; its §6 line is
    a dated line), from rule 8 above, with its source (LEAN-29's `2bba7b6`; reviews r92 and r92c);
    rule 8 here and the report use the number you file.
- `ROADMAP.md`: batch 4, after the last batch section at MERGE (MERGE-1's section for the cloud
  items follows LEAN-29's §1.20).
- One fresh cold reviewer reads the documents commit's diff alone (about 15 calls): every count
  against its gate or census output, the new rule 35 against rule 8 here, the §4 sentence against
  `lean/LEAN-29-ruling-2.md`; its confirming pass closes the job. (LEAN-29's documents commit
  `7ca9f6d` had no reviewer, ruling 2 noted.)

### Job 4, the end checks, in this order

- **4a. The bridge search:** `tools/bridge_search.py --diff records/bridges/MERGE-1/` under the
  cap, on a clean commit of jobs 0 to 3; rc 1 means candidates to review. Report NEW and GONE keys
  against job 1's prediction, pairs and shapes; check each NEW import-unrelated pair and each NEW
  shape by hand for a theorem whose proof needs both sides; a real one gets the next free item
  number (157, unless MERGE-1's bridge search used it) and goes into the lane's
  `MATH-PLAN-library-2-bridges-2.md` (ds_write_staging with its current sha256 as
  `expect_sha256`, appended after its last row, the plan's section 7 columns); it never
  enters this batch. Say for each whether it is load-bearing for a scheduled row (items 101 to
  110); only that re-draws the cut, at a batch boundary. Write the new baseline to
  `records/bridges/LEAN-30/`; its commit touches only `records/`.
- **4b. The report tool**, under the cap, on the same clean commit: a report, not a gate. Predicted
  from `report-before.out` and job 1: its written theorems plus the hand-written theorems this
  order adds; section C still 0 recursive. List every `CLOSES` line that names a theorem of this
  order, for Dustin to read; none is expected for a main theorem.
- **4c. Commit everything above. Then the six gates** on the clean tree, predicted first: build rc
  0, 4176 jobs (or job 1's corrected count), 0 warnings; AxiomGate PASS at job 1's count;
  VacuityGate PASS, no new flag (or job 2's listed helpers), 0 VACUOUS-PENDING, 0 run-outs, no
  UNCHECKED, and its tests unchanged (89, 47 flagged, 3 UNCHECKED as expected, 0 mismatches);
  check_sorry PASS 128; check_records PASS 128; gate 7 under the cap
  (`systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0 ~/lean/recheck/run-recheck.sh <commit> ~/lean/classical-lean-paper-crypto`):
  ALL PASSED, 4176 jobs, 128 modules 0 failed, the theorem count, three standard axioms, planted
  fault named. After the gates, only commits that touch nothing outside `records/` are allowed.
- **4d. Report** `lean/LEAN-30-report.md` through ds_write_staging, post_sha256 compared with your
  own sha256sum, laid out like LEAN-29-report.md: in short; setup; job 0; each item with its
  statements, hypothesis table, witness, review and any narrowing or widening; rule 4's grep
  output; predicted beside measured for jobs, constants, the report tool and every gate; list
  entries with reasons; the bridge diff and the baseline; documents changed; commits; misses and
  not reached; LEAN-29's row of numbers for the order table (facts) and this order's own row
  (filing commit to closing commit in UTC, commits, modules, lines under `ClassicalLean/`, theorem
  constants, Dustin's decisions); the push command as one line, not run:
  `cd ~/lean/classical-lean-paper-crypto && git push origin lean-30:master && git push github lean-30:master`.
- **4e. Push-review file** `lean/LEAN-30-push-review.txt` through ds_write_staging, written by one
  script from the repository as it is after the last commit, each command followed by its full
  output: `git rev-parse HEAD`, `git status --porcelain`, `git ls-remote origin master`,
  `git ls-remote github master`, `git merge-base --is-ancestor MERGE HEAD` with its exit code,
  `git rev-list --count MERGE..HEAD`, `git log --name-only --format='== %h %cI %s' MERGE..HEAD` (MERGE written
  out in full),
  and `git show` of every commit after the last confirming review, of every commit that touches a
  module after that module's own last confirming pass, and of every commit that touches
  `HANDOFF.md` or `ROADMAP.md` (files under `records/bridges/` as `--stat` only). Report its
  sha256. Then stop. claude-ai reviews it before Dustin pushes.

## Done means

- Branch `lean-30` from MERGE (master after MERGE-1's push), clean tree, nothing pushed; its first
  commit is the records
  commit and holds no `.lean` file; every prediction hashed in `evidence.log` before its run;
  hashes in records written by script; `el.sh` runs logged; the jobs tracked with the task tools.
- Job 0: PrimitiveDivisor's four passages reworded (or line 98 stated as an `example`) with the
  dated sentence added, and Gruss's lead sentence reworded; no existing code changed (census and
  code-only comparison, each with its prediction and the negative control); the job's review
  closed by a confirming pass.
- Items 96 to 100 proved with no `sorry` and no new axiom, as stated here, or each narrowing said
  plainly with its reason; the five widenings of items 96, 97 and 100 said in the module docstrings, the
  report, the INDEX row and round 62; any dropped row named with the line that has it; any item
  not closed after two review rounds reported, its changes reverted.
- Seven witnesses in rule 2's form, each checked by its module's reviewer against rule 3 with
  ruling 3's two cases; every hypothesis has a dropped-hypothesis row whose evidence is an
  `example`, a labelled check or "by hand" (rule 3), with Lean's junk values where they decide the
  case.
- Each changed module had its cold review after its statements were final, ending with a
  confirming pass, and each review answered rule 1's check; any statement changed after its review
  had a statement-equivalence review.
- Every reviewer's and checker's output saved verbatim with its sha256 in the evidence folder
  (HANDOFF.md §6 rule 17), and `~/.claude/agent-memory/` hashed before the first review and after
  the last.
- Every commit message that cites a run names its evidence label (rule 8).
- Every new vacuity-list entry named in the report with its reason and its reviewer's check; no
  VACUOUS-PENDING entry and no UNCHECKED verdict in the library.
- The job count and the constant count predicted (blind, before any census) beside measured.
- Job 3's documents changed and named, their review closed by a confirming pass; rule 4's three
  files agree and the grep is in the report.
- The report tool's run reported (4b).
- All six gates as predicted, or each miss reported; gate 7 ALL PASSED on the last commit that
  touches anything outside `records/`, and later commits touch only `records/`.
- The bridge diff run and reported against its prediction; the new baseline committed and named.
- The report and the push-review file are in `lean/` and their hashes match yours.

Then report in a few plain sentences: what was proved, any narrowing and the widenings, the gate
results, the new list entries, the two files' hashes and the push command. Dustin reads your
replies carefully and is still learning to read code: use plain words and define a technical term
the first time you use it. When you need a decision from him, ask in one line with your recommended
answer first.

## Not in this order

- Rows 7, 8 and 70's witnesses, the report tool's outer heartbeat budget, and the gate's FAIL text
  (case 5, the meaning of UNCHECKED and KERNEL-REJECTED): the next gate order (VACUITY-3's ruling
  3).
- Rows 9, 10, 67, 31 and 32 (the infinite independent family and the AR(2) process): the later
  order ruling 3 names.
- Items 101 to 110 (LEAN-31 and LEAN-32; LEAN-31 takes rows 103 and 104 from lane
  `lean/API-CREDIT-CARRY-1.md` rather than drafting them again, store row 20261015-010), and rows
  154 to 156 of the bridges files.
- MERGE-1's work: the merge, CI, the five cloud modules and their records.
- An `example` in PrimitiveDivisor for lines 265 and 346 to 350 (a failing elaboration, and a run
  that needs an import this module does not have, cannot be one).
- The main clone, `~/trading`, `~/lean/recheck`, Dustin's `banned-terms` file, and any push.

## Revisions

- r1 (cold review 1, PASS WITH FINDINGS, 0 BLOCKER, 3 MAJOR, 13 MINOR; all applied):
  - MAJOR: the DSMain output hash of the checks was a placeholder; it is now the measured value
    (placement) and Setup 6's prediction says whose run it is.
  - MAJOR: rule 3 forbade records and the report to say "elaborated", which the order itself asks
    them to report; the ban now covers module docstrings and comments, and records cite runs by
    evidence label.
  - MAJOR: the opening misstated ruling 2's four notes; they are now listed as the ruling has
    them, each with what this order does (note 3, the statement review, is answered under
    HANDOFF.md §6 rule 16 in "It rests on" and 2d).
  - MINOR: the plan's checks have 15 `--lean` misses, not 16, and `bridges.minquad` now hits
    (40 + 7 − 1 = 46); "four modules", not five; every widening listed (five conditions, item 96's
    finite measure included); rule 4's grep matches "widen"; "INDEX rows start" restored.
  - MINOR: the checks' drop lines now check the other hypotheses (positive semidefiniteness,
    injectivity and prefix-freeness on written-out words, the rate theorem's five hypotheses), and
    two witness lines were added: 38 of 38 (revision 2).
  - MINOR: five more names probed (A2 to A5 re-elaborated, rc 0) and the probe `P99.lean` added as
    A6; item 98's witness is now `!![2, 1; 1, 3]`, `m = 1`, `M = 4` (left side `21/20`, strictly
    inside the bound), item 99's first witness `p = 1/3` (strict).
  - MINOR: job 0 now separates successful from failing elaborations (line 98 may become an
    `example`), adds a dated sentence to the note "kept as written", and says Mathlib supplies
    `IsDomain (ZMod p)` from `Fact p.Prime`; item 96's `hX` row says its determinant check is
    algebra at `c = 1`; item 99's three ranges are given apart; FiniteChain's shared review says
    which item reverts; the documents commit gets a cold reviewer and is shown in the push-review
    file; Setup 7 spells out rule 20's flags; MinimumQuadraticForm and Entropy have full hashes;
    "564 shape candidates" is attributed to LEAN-29's report.
- r2 (cold review 2, PASS WITH FINDINGS, 0 BLOCKER, 2 MAJOR, 4 MINOR; all applied):
  - MAJOR: the cold reviews were credited as HANDOFF.md §6 rule 16's statement review, but the
    reviewer did not have the plan; "It rests on" now says what they covered, and the plan (Before
    approval, step 4) holds a plan-fit check, row by row, closed by Dustin's approval (2d).
  - MAJOR: rule 3 forbade the past-run wording that job 0 asks for; it now allows a docstring to
    report a past run that names the commit that first wrote the claim and says no file was kept.
  - MINOR: ruling 2's note 1 and rule 8 now cite review r92 for `2bba7b6` and review r92c for
    `54c3624`, and drop "the cause"; Done means names the five widenings and the documents review;
    the full sha256 of MinimumQuadraticForm and Entropy are quoted in claude-ai's evidence; a rate
    case of the checks whose other hypotheses fail now prints MISS instead of stopping (revision 3,
    the same output, `1ff937ba…`, in the cloud and on DSMain).
- r3 (claude-ai, after Dustin's ruling of 11:25 EDT, store rows 20261015-010 and -011): order MERGE-1 runs first in the same worktree, and LEAN-30 branches from master
  after Dustin pushes the merge (MERGE). Before approval now checks MERGE (both remotes, MERGE-1's
  push-review HEAD, both ancestors, a whole-tree diff limited to MERGE-1's declared files, the
  toolchain and the Mathlib pin); the counts after MERGE are MERGE-1's
  (4176 jobs, 3335, 128 modules), the round is 62, the bridge baseline `records/bridges/MERGE-1/`
  and the next bridge row the next free number; HANDOFF.md's hash moved to the read list, since
  MERGE-1 changes it. "Not in this order" says LEAN-31 takes rows 103 and 104 from lane
  `lean/API-CREDIT-CARRY-1.md`. A short confirming pass by the same reviewer (claude-ai had not
  given it MERGE-1's order, a miss; it read LEAN-30's summary of it): 0 BLOCKER, 1 MAJOR, 5 MINOR,
  all applied: the whole-tree diff, toolchain and pin checks; MERGE tied to MERGE-1's push-review
  file; job 3's rule number and ROADMAP place read at MERGE; a cloud module's words cannot drop a
  row; the commit is called MERGE, not M (item 98's bound).

## Appendix A: the measurement files

Each block below is the file byte for byte, between its fence lines; the file ends with a newline
after its last line. `closure.py` is run from the worktree root with `python3 -I` (the same file as
LEAN-29's A1); the `.lean` files are elaborated from the worktree root with rule 20's four flags. On
DSMain all six are in `/tmp/claude-ai-lean30/`.

### A1: `/tmp/claude-ai-lean30/closure.py`, the import closure (facts, "Imports"; LEAN-29's A1)

sha256 `10c080f1cfbbf470cfd5c5cda3745155e55a1a882b568af444b0a1984736df95`

```python
"""Import closure of the classical-lean library, for order LEAN-29's job prediction.

Run from the worktree root: python3 -I closure.py [Module.Name=Extra.Import,...] ...
Each argument adds imports to a module (simulating the order's new import lines); a module named
on the left that does not exist is a new module (its file is not read). Prints the size of the
closure of ClassicalLean.lean (the root) over modules found as source files in the repository or
in .lake/packages/*, core modules (Init, Std, Lean, Lake) excluded, and lists the modules the
additions bring in.
"""
import os, re, sys
ROOTS = ['.'] + sorted(os.path.join('.lake/packages', d) for d in os.listdir('.lake/packages'))
IMP = re.compile(r'^\s*(?:public\s+)?(?:private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z_][\w.]*)')
CORE = ('Init', 'Std', 'Lean', 'Lake')

def path_of(mod):
    rel = mod.replace('.', '/') + '.lean'
    for r in ROOTS:
        p = os.path.join(r, rel)
        if os.path.isfile(p):
            return p
    return None

def imports(mod, extra):
    out = list(extra.get(mod, []))
    p = path_of(mod)
    if p is not None:
        with open(p, encoding='utf-8') as fh:
            for line in fh:
                m = IMP.match(line)
                if m:
                    out.append(m.group(1))
    return out

def closure(start, extra):
    seen, stack, missing = set(), [start], set()
    while stack:
        m = stack.pop()
        if m in seen or m.split('.')[0] in CORE:
            continue
        if path_of(m) is None and m not in extra:
            missing.add(m)
            continue
        seen.add(m)
        stack.extend(imports(m, extra))
    return seen, missing

def parse(args):
    extra = {}
    for a in args:
        mod, imps = a.split('=', 1)
        extra.setdefault(mod, []).extend(x for x in imps.split(',') if x)
    return extra

if __name__ == '__main__':
    base, miss0 = closure('ClassicalLean', {})
    print('base closure', len(base), 'unresolved', sorted(miss0))
    if len(sys.argv) > 1:
        extra = parse(sys.argv[1:])
        new, miss1 = closure('ClassicalLean', extra)
        print('with additions', len(new), 'unresolved', sorted(miss1))
        print('added modules', len(new - base))
        for m in sorted(new - base):
            print('  +', m)
        for mod in extra:
            if path_of(mod) is not None:
                own0, _ = closure(mod, {})
                own1, _ = closure(mod, extra)
                print('module', mod, 'own closure', len(own0), '->', len(own1))
```

### A2: `/tmp/claude-ai-lean30/S96.lean`, item 96, statement and probes

sha256 `a3df11bd5a6f5683c133a0e374e5cf3f83640e58f58c34cc29fff1291e700e5b`

```lean
import ClassicalLean.Probability.CovarianceDirections
import ClassicalLean.Algebra.HadamardInequality

/-! Order LEAN-30, item 96: the statement with `sorry`, and the names its route cites.
`ClassicalLean.Probability.CovarianceDirections` gains the import of the library's Hadamard
module above (it imports only Mathlib, so there is no cycle). -/

open MeasureTheory ProbabilityTheory Matrix Finset

#check @ClassicalLean.det_le_prod_diag
#check @ClassicalLean.Probability.CovarianceDirections.covMatrix
#check @ClassicalLean.Probability.CovarianceDirections.posSemidef_covMatrix
#check @ProbabilityTheory.covariance_self
#check @MeasureTheory.MemLp.aemeasurable
#check @ProbabilityTheory.variance_nonneg
#check @Finset.prod_congr

namespace ClassicalLean.Probability.CovarianceDirections

variable {ι Ω : Type*} [Fintype ι] {m0 : MeasurableSpace Ω} {μ : Measure Ω} {X : ι → Ω → ℝ}

theorem det_covMatrix_le_prod_variance [DecidableEq ι] [IsFiniteMeasure μ]
    (hX : ∀ i, MemLp (X i) 2 μ) :
    (covMatrix X μ).det ≤ ∏ i, variance (X i) μ := by
  sorry

end ClassicalLean.Probability.CovarianceDirections
```

### A3: `/tmp/claude-ai-lean30/S97.lean`, items 97 and 100, statements and probes

sha256 `7a67d41c070d43465646d131d4031573e786d865b9fa17ef8fdd019e6f1c0dd6`

```lean
import ClassicalLean.Probability.FiniteChain

/-! Order LEAN-30, items 97 and 100: the statements with `sorry`, and the names their routes
cite. Both go in `ClassicalLean.Probability.FiniteChain`, which already imports the library's
`Channel` (and through it `relEntropy`). Mathlib's `Matrix.IsPrimitive` is not visible through
FiniteChain's imports (measured: Unknown constant), so item 100 states its hypothesis directly. -/

open Finset Matrix

#check @ClassicalLean.Simplex.relEntropy
#check @ClassicalLean.Simplex.relEntropy_vecMul_le
#check @ClassicalLean.Simplex.sum_vecMul_eq_sum
#check @ClassicalLean.Simplex.vecMul_nonneg
#check @Real.log_abs
#check @abs_div
#check @Finset.abs_sum_le_sum_abs
#check @Finset.sum_eq_sum_iff_of_le
#check @ClassicalLean.Probability.sum_abs_vecMul_le
#check @ClassicalLean.Probability.sum_abs_vecMul_pow_le
#check @ClassicalLean.Probability.sum_abs_vecMul_pow_sub_le
#check @ClassicalLean.Probability.existsUnique_vecMul_eq_self
#check @Finite.exists_min
#check @Finset.inf'
#check @Nat.div_add_mod
#check @pow_mul
#check @pow_add

namespace ClassicalLean.Probability

variable {n : Type*} [Fintype n]

theorem relEntropy_vecMul_le_of_stationary {P : Matrix n n ℝ} {μ π : n → ℝ}
    (hP0 : ∀ i j, 0 ≤ P i j) (hP : ∀ i, ∑ j, P i j = 1) (hμ : ∀ i, 0 ≤ μ i)
    (hμπ : ∀ i, π i = 0 → μ i = 0) (hπ : π ᵥ* P = π) :
    ClassicalLean.Simplex.relEntropy (μ ᵥ* P) π ≤ ClassicalLean.Simplex.relEntropy μ π := by
  sorry

theorem existsUnique_vecMul_eq_self_of_pow [DecidableEq n] [Nonempty n] {P : Matrix n n ℝ}
    {k : ℕ} (hP : ∀ i, ∑ j, P i j = 1) (hpos : ∀ i j, 0 < (P ^ k) i j) :
    ∃! π : n → ℝ, ((∀ i, 0 ≤ π i) ∧ ∑ i, π i = 1) ∧ π ᵥ* P = π := by
  sorry

theorem sum_abs_vecMul_pow_sub_le_of_pow [DecidableEq n] {P : Matrix n n ℝ} {k : ℕ} {δ : ℝ}
    (hP0 : ∀ i j, 0 ≤ P i j) (hP : ∀ i, ∑ j, P i j = 1) (hδ : ∀ i j, δ ≤ (P ^ k) i j)
    {μ π : n → ℝ} (hμ : ∑ i, μ i = ∑ i, π i) (hπ : π ᵥ* P = π) (t : ℕ) :
    ∑ j, |(μ ᵥ* P ^ t) j - π j| ≤ (1 - Fintype.card n * δ) ^ (t / k) * ∑ j, |μ j - π j| := by
  sorry

end ClassicalLean.Probability
```

### A4: `/tmp/claude-ai-lean30/S98.lean`, item 98, statement and probes

sha256 `47eabf3485cd20bd8c19f09a6d201abc14f862df2da16cb7028c7768514bb028`

```lean
import ClassicalLean.Statistics.GeneralizedLeastSquares
import ClassicalLean.Algebra.Kantorovich

/-! Order LEAN-30, item 98: the statement with `sorry`, and the names its route cites.
`ClassicalLean.Statistics.GeneralizedLeastSquares` gains the import of the library's Kantorovich
module above (it imports only Mathlib, so there is no cycle). -/

open Matrix

#check @ClassicalLean.Algebra.Kantorovich.dotProduct_mulVec_mul_inv_le
#check @ClassicalLean.Analysis.MinimumQuadraticForm.onesInvOnes
#check @dotProduct_one
#check @one_dotProduct_one
#check @Finset.card_univ
#check @Fintype.card_pos
#check @div_le_iff₀

namespace ClassicalLean.Statistics

open ClassicalLean.Analysis.MinimumQuadraticForm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem onesQuad_mul_onesInvOnes_le [Nonempty ι] {V : Matrix ι ι ℝ} {m M : ℝ} (hm : 0 < m)
    (hmV : (V - m • 1).PosSemidef) (hVM : (M • 1 - V).PosSemidef) :
    (1 ⬝ᵥ (V *ᵥ 1)) * onesInvOnes V / (Fintype.card ι : ℝ) ^ 2 ≤ (m + M) ^ 2 / (4 * m * M) := by
  sorry

end ClassicalLean.Statistics
```

### A5: `/tmp/claude-ai-lean30/S99.lean`, item 99, definition, statements and probes

sha256 `9a54c4fadb2ab9b5bdd32745a45863741285e9fdf63da6de5506473d67841d6b`

```lean
import ClassicalLean.InformationTheory.CompressionTest

/-! Order LEAN-30, item 99: the definition, the statements with `sorry`, and the names the route
cites. `winRate` is complete here (its two bounds are proved); only the two theorems use `sorry`. -/

open MeasureTheory Finset

#check @ClassicalLean.InformationTheory.CompressionTest.score
#check @ClassicalLean.InformationTheory.CompressionTest.bernProd
#check @ClassicalLean.InformationTheory.CompressionTest.bernProd_real_singleton
#check @ClassicalLean.InformationTheory.CompressionTest.bernProd_fairCoin_real_singleton
#check @ClassicalLean.InformationTheory.CompressionTest.measureReal_score_bernProd_ge_le
#check @Real.geom_mean_le_arith_mean2_weighted
#check @Finset.prod_ite
#check @Finset.prod_const
#check @MeasureTheory.measureReal_mono
#check @MeasureTheory.measureReal_union_le
#check @div_le_div_of_nonneg_left

namespace ClassicalLean.InformationTheory.CompressionTest

variable {n : ℕ}

/-- The share of wins in a string, `k / n` with `k` the number of wins (Lean's `0` at `n = 0`). -/
noncomputable def winRate (x : Fin n → Bool) : unitInterval :=
  ⟨((univ.filter fun i ↦ x i = true).card : ℝ) / n, by positivity,
    div_le_one_of_le₀ (by exact_mod_cast (card_filter_le _ _).trans (by simp)) (by positivity)⟩

theorem score_plugIn_le (c : (Fin n → Bool) → List Bool) (p : unitInterval) (x : Fin n → Bool)
    (hx : (bernProd n p).real {x} ≠ 0) :
    score c (bernProd n (winRate x)) x ≤ score c (bernProd n p) x := by
  sorry

theorem measureReal_score_plugIn_ge_le {c : (Fin n → Bool) → List Bool}
    (hc : Function.Injective c) (hpf : InformationTheory.IsPrefixFree (Set.range c))
    (p : unitInterval) {α : ℝ} (hα : 0 < α) :
    (bernProd n p).real {x | 1 / α ≤ score c (bernProd n (winRate x)) x} ≤ α := by
  sorry

end ClassicalLean.InformationTheory.CompressionTest
```

### A6: `/tmp/claude-ai-lean30/P99.lean`, the visibility probe for item 99's route (b); rc 1 expected

sha256 `3c32e497b674d00dcb57d8770a333c888738b4ee954ed2f280ffa796e897a498`

```lean
import ClassicalLean.InformationTheory.CompressionTest

/-! Probe, not part of the order: is the library's `relEntropy_nonneg` visible through
CompressionTest's imports? Predicted: no (Unknown identifier), since CompressionTest imports no
ClassicalLean module of the Entropy line. -/

#check @ClassicalLean.Simplex.relEntropy_nonneg
```
