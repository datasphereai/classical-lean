# Round 80 — Ville's inequality for Pólya's urn, the walk under a conditional up-chance, ruin and the divisibility of Lucas numbers, ruin by first-step analysis, the Kolmogorov–Smirnov statistic (order CLOUD-MATH-6)

Session: Claude Code cloud session `session_01HgueTbGvJvmksxSgWGMRPt`
(https://claude.ai/code/session_01HgueTbGvJvmksxSgWGMRPt), executing order `CLOUD-MATH-6`
(`records/orders/20261030T212345Z__claude-ai__order-cloudmath6-urn-ville-ruin-conditional-divisibility-chain-kolmogorov-smirnov.md`),
bridge rows 157, 154, 156, 165 and 159 of `MATH-PLAN-library-2-bridges-2.md`, in a cloud container's
clone of GitHub `datasphereai/classical-lean` on branch `cloud-math-6`, from
`8631a8d3c4316d85c78df697436b0245fa24cf1b` (checked equal to `origin/cloud-math-6` before any
change). `git ls-remote origin master` at the start: `8631a8d3c4316d85c78df697436b0245fa24cf1b`
(`$HOME/cm6/start-git.txt`). Lean and Mathlib v4.34.0 (`lake exe cache get`, 8908 files,
`$HOME/cm6/setup2-cache.txt`).

**No drafts.** Each of the five bridges is stated and proved by this session from its row's sketch
in the order; no proof comes from an earlier draft.

Evidence: `$HOME/cm6/` (outside the repository); every count below is read from a saved output
there, cited by its file name (rule 9).

First part written before any Lean file changed; completed after the work, below.

## Modules this round adds (five new modules)

* bridge 157: `ClassicalLean/Probability/UrnVille.lean` (`ClassicalLean.Probability.UrnVille`),
  importing `ClassicalLean.Probability.PolyaUrn` and `ClassicalLean.Probability.MaximalInequality`;
* bridge 154: `ClassicalLean/Probability/RuinConditional.lean`
  (`ClassicalLean.Probability.RuinConditional`), importing `ClassicalLean.Probability.GamblersRuin`
  and `ClassicalLean.Probability.LikelihoodScore`;
* bridge 156: `ClassicalLean/Probability/RuinDivisibility.lean`
  (`ClassicalLean.Probability.RuinDivisibility`), importing `ClassicalLean.Probability.GamblersRuin`
  and `ClassicalLean.NumberTheory.LucasApparition`;
* bridge 165: `ClassicalLean/Probability/RuinChain.lean` (`ClassicalLean.Probability.RuinChain`),
  importing `ClassicalLean.Probability.GamblersRuin` and `ClassicalLean.Probability.FiniteChain`;
* bridge 159: `ClassicalLean/Probability/KolmogorovSmirnov.lean`
  (`ClassicalLean.Probability.KolmogorovSmirnov`), importing
  `ClassicalLean.Probability.GlivenkoCantelli` and `ClassicalLean.Probability.IntegralTransform`;
* `ClassicalLean.lean`: five import lines, at the end of its import block, in landing order, each
  added by its module's landing commit.

No existing module changes. `tools/vacuity_reviewed.txt` changes only if a helper is listed (the
order's rule 4). Nothing else under `tools/` changes.

## Starting counts (measured in this session, before any new file, clean tree at `8631a8d`)

The record files of the records-first commit were stashed while these ran (`git stash push -u --
records/`), so the tree was the base tree.

* `lake build`: exit 0, `Build completed successfully (4196 jobs).`, 0 lines with `warning:`
  (`setup3-lake-build.txt`).
* `lake env lean tools/AxiomGate.lean`: `axiom gate PASS — 3844 theorem constant(s) under
  [ClassicalLean] …; 0 scoped exceptions` (`setup3-axiom.txt`).
* `python3 -I tools/check_sorry.py`: PASS, 143 files (`setup3-sorry.txt`).
* `python3 -I tools/check_records.py`: PASS, 143 modules, 1 named exemption (`setup3-records.txt`).
* `lake env lean tools/VacuityGate.lean`: PASS, 1 reviewed helper, 0 VACUOUS-PENDING, rule 5 out of
  heartbeats on 0 theorems (`setup3-vacuity.txt`).
* Setup 1: `curl -sSI https://cache.mathlib.org/` gave `HTTP/1.1 200 Connection Established` then
  `HTTP/2 404` from the cache server (`setup1-curl.txt`), not a stop; `lake exe cache get` then
  fetched and decompressed 8908 files (`setup2-cache.txt`).
* sha256 of each output: `setup_sha256.txt`.

## Probes (Setup 4)

One file per new module, importing exactly its imports (`$HOME/cm6/probes/probe157.lean`,
`probe154.lean`, `probe156.lean`, `probe165.lean`, `probe159.lean`, outputs `probe<n>.out`), and a
second round for the names the proofs use (`probe_extra<n>.lean`, `probe_extra<n>.out`). Every name
the order cites was found except one, and `SigmaFiniteFiltration μ 𝒢` is found as an instance for a
probability measure (`probe157.out`: the `example` elaborated). Unknown as written:

* `ProbabilityTheory.condExp_indep_eq` (`probe154.out`): the lemma is in the root namespace,
  `condExp_indep_eq`, which bridge 154's witness uses.
* `Finset.filter_card_add_filter_neg_card_eq_card` (`probe_extra154.out`): Mathlib has
  `Finset.card_filter_add_card_filter_not`; not used in the end.
* `MeasureTheory.StronglyMeasurable.div_const` (`probe_extra154.out`): not in Mathlib; the proof of
  154 uses `Measurable.div_const` and `.stronglyMeasurable`.
* `MeasureTheory.measureReal_diff` exists but is deprecated (`probe_extra159.out`); 159 uses
  `measureReal_sdiff`. During the proofs, `isProbabilityMeasure_map` and
  `Measure.isProbabilityMeasure_map` were unknown: the probability of a pushforward is an instance in
  Mathlib (`Measure.isProbabilityMeasure_map_iff` is the only named lemma), and the line was dropped.

## Statement stage and its cold review (rule 1, rule 5)

The five modules were written with every statement final, every proof `sorry` and every witness
complete, and each elaborated with `lake env lean` with only `sorry` warnings (`stmt/stmt157.out`,
`stmt154.out`, `stmt156.out`, `stmt165.out`, `stmt159.out`; the modules as reviewed are copied in
`stmt/`, hashes `stmt_sha256.txt`). The brief was built by script (`$HOME/cm6/review/mkbrief.py`,
which copies the order's table and rules 2 and 3, the five bridge rows, HANDOFF.md's "Satisfiability
witnesses" paragraph, the statements the bridges rest on, five library witnesses used as models, and
the five modules; `brief.md`, sha256
`23a0c2a104d196ff4deb46cd069a4c405c790ced0f4ff1f4af96daaa2160ba54`). Its first version cut
`map_lucasU` (no `:=` on its statement) and `meanHitting_eq` (a `:=` inside its `let`) at the wrong
line; the script was fixed and the brief rebuilt before it was sent. One fresh subagent reviewed it:
`incoming/reviews/review-1.md` (sha256
`06e44e8e2ba2688d7f94b6a94c02b1add93ff518e39a0c10d1679bc08b2e89fd`), **FINDINGS 1, MINOR**:

1. Bridge 165's theorem 1 docstring said `meanHitting_eq`'s hypotheses hold for `ruinChain` "as
   `ruinChain_meanHitting_iff`'s proof shows", a proof, not a statement. Fixed by the reviewer's
   option (a): three helpers with no hypotheses, `sum_ruinChain`, `ruinChain_nonneg` and
   `exists_pow_ruinChain_pos`, used by theorem 2's proof and cited in theorem 1's docstring and the
   module docstring (in bridge 165's landing commit).

The fix changed no statement and no witness's arguments, so no second pass (rule 5); the three
helpers were not seen by the review and passed the vacuity gate. Verdicts:
`measureReal_exists_urnShare_ge_le`, `measureReal_exists_ge_le_of_condProb`,
`measureReal_hit_eq_inv_iff_dvd`, `integral_exitTime_eq_meanHitting` with
`ruinChain_meanHitting_iff` (classified together) and `measureReal_cdf_le_eq_of_map_eq` FAITHFUL;
`sup_abs_empiricalCDF_sub_eq_of_continuous` GENERALIZED (no pairwise independence, as the order
says). No theorem WEAKER; all six witnesses PASS. The review noted, as not findings, that `hrb`
(157), `hp0` (154) and `hX` (159, theorem 2) are not needed for truth but are named by the order's
table, so they stay.

## Proofs, by bridge (start times: `start157.txt`, `start154.txt`, `start156.txt`, `start165.txt`, `start159.txt`)

Every bridge is proved by this session, from its row's sketch in the order; no draft.

* **157** (from 2026-10-30 21:49:02 UTC): the share is a martingale (`martingale_urnShare`), so a
  supermartingale, nonnegative by `urnShare_mem_Icc`, with `E[share 0] = r / (r + b)`; Ville's
  inequality per horizon and `Monotone.measure_iUnion` for "ever". The first linted build had 2
  long-line warnings in the module docstring; re-wrapped, then 0 (`build157.txt`).
* **154** (from 21:57:08 UTC): the wins `W n = if n = 0 then 0 else (X (n − 1) + 1) / 2`;
  `measureReal_exists_le_score_ever` at `p₀ = p`, `q = 1 − p`, `α = (p / (1 − p)) ^ a`; on reaching
  `a`, `score_eq_pow` gives `r ^ w (1/r) ^ l ≥ r ^ (a + l) (1/r) ^ l = r ^ a`, with `w − l` the walk.
  Four `<;>` lint warnings were removed before the linted build, which had 0 (`build154.txt`).
* **156** (from 22:05:12 UTC): `(1 − p)/p = r` at `p = 1/(r + 1)`; `map_lucasU` to the integer `U`;
  `U (n + 1) = U n + r ^ n`, so `U` strictly increasing with `U 0 = 0`; `lucasU_gcd` with
  `IsCoprime (1 + r) r`; `Int.gcd_eq_left` and injectivity give `gcd b (a + b) = b`. 0 warnings
  (`build156.txt`).
* **165** (from 22:13:05 UTC): the three helpers above, a private description of an inside row and a
  private one-term sum over `Fin`; `meanHitting_eq`'s uniqueness and the check that `(a + b − i) i`
  solves the equations; theorem 1 is `integral_exitTime_eq` and theorem 2 at index `b`. 0 warnings
  (`build165.txt`).
* **159** (from 22:22:35 UTC): theorem 2 is item 106 at `X i` rewritten by `hlaw`; theorem 1 as the
  module docstring says (the null sets `{F (X i) ≤ F q} \ {X i ≤ q}` for rational `q`, of measure
  `F q − F q`, and `{F (X i) ≤ 0}`). The first linted build had 1 long line in a proof; re-wrapped,
  then 0 (`build159.txt`).

**Miss (rule 9):** as in round 77, each first linted build wrote to the same file as its re-run, so
only the clean re-runs are saved; the counts of the first runs (2, 0, 0, 0 and 1) were read from the
terminal.

No proof forced a statement to change: no narrowing (rule 7). Each bridge closed in under ten
minutes of the session's clock. No helper was flagged, so `tools/vacuity_reviewed.txt` is unchanged.

## Per bridge: the gates before each landing commit

| bridge | module build | witness gate | root build | vacuity gate |
|---|---|---|---|---|
| 157 | 0 warnings (`build157.txt`) | PASS, OK=1, copy-error=0 (`witness157.txt`) | 4197 jobs, 0 warnings (`rootbuild157.txt`) | PASS, 1 reviewed helper (`vacuity157.txt`) |
| 154 | 0 warnings (`build154.txt`) | PASS, OK=1, copy-error=0 (`witness154.txt`) | 4198 jobs, 0 warnings (`rootbuild154.txt`) | PASS, 1 reviewed helper (`vacuity154.txt`) |
| 156 | 0 warnings (`build156.txt`) | PASS, OK=1, copy-error=0 (`witness156.txt`) | 4199 jobs, 0 warnings (`rootbuild156.txt`) | PASS, 1 reviewed helper (`vacuity156.txt`) |
| 165 | 0 warnings (`build165.txt`) | PASS, OK=1, copy-error=0 (`witness165.txt`) | 4200 jobs, 0 warnings (`rootbuild165.txt`) | PASS, 1 reviewed helper (`vacuity165.txt`) |
| 159 | 0 warnings (`build159.txt`) | PASS, OK=2, copy-error=0 (`witness159.txt`) | 4201 jobs, 0 warnings (`rootbuild159.txt`) | PASS, 1 reviewed helper (`vacuity159.txt`) |

Bridge 157's first root build failed because the import line had been appended after the root
file's closing comment block instead of at the end of its import block; it was moved before any
commit, and the root build above is the re-run. The vacuity gate prints a line for a theorem only
when it flags one, so for the new theorems its lines are none: its whole output each time is the
summary line `vacuity gate PASS — no vacuous theorems in [ClassicalLean] (1 reviewed helpers and 0
VACUOUS-PENDING on tools/vacuity_reviewed.txt); rule 5 ran out of its 400000 heartbeats on 0
theorems`.

## Witnesses (six, each after its module's last line; all OK in the witness gate)

* `measureReal_exists_urnShare_ge_le`: PolyaUrn's urn with `r = b = 1`, paths by `Kernel.traj` on
  `ℕ → Bool`, filtration `piLE`, `c = 3/4`. What moves: every draw is random (red with chance the
  current share, between `1/(n + 2)` and `(n + 1)/(n + 2)`), so the share moves at every step; the
  start share `1/2 < 3/4`, so the event is not sure, and the bound `1/(2 · 3/4) = 2/3 < 1`.
* `measureReal_exists_ge_le_of_condProb`: GamblersRuin's biased walk (`ℕ → Fin 3`, uniform coins,
  step `+1` when the coin shows `0`), `p = 1/3`, `a = 2`; `hcond` with equality through
  `condExp_indep_eq` (mean of `(X n + 1)/2` is `1/3`). What moves: every step is `±1`; the bound
  `(1/2)² = 1/4 < 1`, and `p < 1/2`.
* `measureReal_hit_eq_inv_iff_dvd`: the same coins, `r = 2` (`p = 1/3`), `a = 4`, `b = 2`. What
  moves: `b > 1`, `a > b`, and the chance is `U 2 / U 6 = 3/63 = 1/21` with `U n = 2 ^ n − 1`.
* `integral_exitTime_eq_meanHitting`: GamblersRuin's fair walk (`ℕ → Bool`, fair coins), `a = 2`,
  `b = 3` (six positions, four inside), `g i = (5 − i) i = 0, 4, 6, 6, 4, 0`, checked at each index.
  What moves: every step is `±1` with mean `0`; the start index `3` is inside, and `g 3 = 6 = a b`.
* `sup_abs_empiricalCDF_sub_eq_of_continuous`: `Ω = ℝ`, `μ = gaussianReal 0 1`,
  `X i ω = if Even i then ω else −ω`. What moves: `X (i + 1) ≠ X i` off the null set `{0}`; each law
  is standard normal (`gaussianReal_map_neg` for odd `i`); `Φ` continuous.
* `measureReal_cdf_le_eq_of_map_eq`: the same draws at `i = 1` (`X 1 = −ω`, `hlaw` through
  `gaussianReal_map_neg`, not `rfl`) and `u = 1/2`, not an end of `[0, 1]`.

`ruinChain_meanHitting_iff` and the helpers have no hypothesis, so no witness (HANDOFF section 4).

## The modules and their theorem-constant counts

Measured with `$HOME/cm6/count/census.lean`: the axiom gate's predicate (user name under
`ClassicalLean`, no macro scopes, `.thmInfo`), restricted to the constants that `env.getModuleFor?`
places in the module (`count/census.txt`). Measured on the tree at `2fd47ac`, with all five modules
landed and the tree clean.

| module | bridge | theorem constants |
|---|---|---|
| `ClassicalLean/Probability/UrnVille.lean` | 157 | 9: 3 written, 1 `_simp_`, and 5 equation lemmas of PolyaUrn's `urnRed` (`eq_1`, `eq_2`, `eq_def`, two of its `match_1`) generated in this module by `simp [urnRed]` |
| `ClassicalLean/Probability/RuinConditional.lean` | 154 | 1: 1 written |
| `ClassicalLean/Probability/RuinDivisibility.lean` | 156 | 3: 1 written, 2 `_proof_` |
| `ClassicalLean/Probability/RuinChain.lean` | 165 | 34: 7 written (2 of them private), `ruinChain.eq_1`, and 26 `_proof_` and `_simp_` |
| `ClassicalLean/Probability/KolmogorovSmirnov.lean` | 159 | 5: 2 written, 3 `_simp_` |
| **five modules** | | **52** |

3844 + 52 = 3896, the axiom gate's count below. The import closure of the root's imports went from
5731 to 5736 modules (`ClassicalLean` from 143 to 148; `count/closure_base.txt`,
`count/closure_after.txt`), so no new Mathlib module, and the build has 4196 + 5 = 4201 jobs.

## End check 1 (clean tree at `2fd47ac`, predictions first: `expected.txt`, sha256 `b49850ac…`)

| command | expected | measured |
|---|---|---|
| `lake build` | 4201 jobs, 0 warnings | `Build completed successfully (4201 jobs).`, 0 `warning:` lines (`ec1_build.txt`) |
| `lake env lean tools/AxiomGate.lean` | PASS 3896 | PASS 3896, 0 scoped exceptions (`ec1_axiom.txt`) |
| `python3 -I tools/check_sorry.py` | PASS 148 | PASS 148 (`ec1_sorry.txt`) |
| `python3 -I tools/check_records.py` | PASS 148, 1 exemption | the same (`ec1_records.txt`) |
| `lake env lean tools/VacuityGate.lean` | PASS, 1 reviewed helper | the same, 0 VACUOUS-PENDING, rule 5 out on 0 (`ec1_vacuity.txt`) |
| `python3 -I tools/witness_gate.py` on the five modules | PASS, OK=6, copy-error=0 | the same (`ec1_witness.txt`) |
| `python3 tools/compile_rules.py drift records/rules.toml HANDOFF.md` | PASS no drift | `PASS no drift` (`ec1_drift.txt`) |

**End check 2** (not run here; they run on DSMain at MERGE-5): gate 7, the banned-vocabulary scan,
the whole-library witness gate, the bridge search and the report tool.

**End check 3** (`ec3.txt`): both greps on the five new files find nothing (rc 1). The output of
`git diff --name-only 8631a8d HEAD` lists only the five modules, `ClassicalLean.lean`, `records/`
and `incoming/reviews/review-1.md`. In `ClassicalLean.lean` the diff is only the five added import
lines; under `records/` only `A` (this order's copy, this fragment) and `M` (`INDEX.md`,
`CLAIMS.md`), whose diffs are one `+` line each at the end of the file. Every output's sha256 is in
`end_sha256.txt`.

## Commits (branch `cloud-math-6`, each pushed with `git push origin cloud-math-6`)

* `8f0bfc1` — records first: the order's copy, its INDEX row, the CLAIMS row and this fragment's
  first part.
* `0d7f852` — `incoming/reviews/review-1.md`.
* `1861efb` — bridge 157, `ClassicalLean/Probability/UrnVille.lean`, and its import line.
* `3c72bbe` — bridge 154, `ClassicalLean/Probability/RuinConditional.lean`, and its import line.
* `f1fb5ad` — bridge 156, `ClassicalLean/Probability/RuinDivisibility.lean`, and its import line.
* `3fefc24` — bridge 165, `ClassicalLean/Probability/RuinChain.lean` (with the review's fix), and
  its import line.
* `2fd47ac` — bridge 159, `ClassicalLean/Probability/KolmogorovSmirnov.lean`, and its import line.
* The commit that carries this section: the CLAIMS row closed and the INDEX row's state. A commit
  cannot cite its own hash.
* Then `incoming/REPORT.md`.

All five bridges are closed: none narrowed, none undone. `master` was not touched.
