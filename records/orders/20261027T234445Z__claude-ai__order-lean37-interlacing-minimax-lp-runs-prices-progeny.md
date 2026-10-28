# LEAN-37 order: batch 7 of the API-credit drafts (items 123, 141, 143, 145 and 149)

For a plain Claude Code session on DSMain, as dustin, in tmux `cc`. Written by claude-ai on 2026-10-27 in
Project LEAN, to the lighter procedure (store row 20261026-063; VACUITY-5 was the first such order): Lean's
own check of every proof, the machine gates, one cold review of the statements and witnesses, and
claude-ai's push review. No plan-approval stop, no per-step prediction files, no evidence-log labels, no
citecheck, no per-module cold reviews.

Review: one cold pass on helios (`~/lean37-review-1/out1/review.md`,
`b8a48e73074197281cce8f11a7f5f8519cb4ccea20df41b9a146dbaacb1692ac`): PASS WITH FINDINGS (F1 to F5 MAJOR,
F6 to F10 MINOR), all applied here (revision r3). It confirmed every hash, line number, namespace, `variable`,
`section` and `include` line and `example :=` count it could see, and the witness arithmetic.

**When to start.** Outside the night window, which `~/lean/vacuity4-checks/scripts/ev.sh`'s header names
(no Lean run from 01:45 to 05:45 local time). If the window comes while you work, stop at a clean point
(no Lean running, the tree committed or the change only in your scratch folder), say so, and go on when
Dustin says to. Time inside a window does not count toward any time limit below. The whole run is about
4 to 6 hours; the two long gates alone take about 50 minutes (the whole-library witness gate about 27, gate
7 about 22, both measured in LEAN-36's and VACUITY-5's runs).

**Launch check.** This session was started with `CLAUDE_CODE_DISABLE_AUTO_MEMORY=1`. Print it first; if it
is not `1`, stop and say so (the cold review in step 6 must be cold).

## Goal

Five items of MATH-PLAN-library-2 that sit below the plan's cut land in their existing home modules, as
their API-credit drafts state them (plan 1's batch 7, `lean/CLOUD-LANDING-PLAN-1.md` line 49; plan 2's
ruling 2 sends it to DSMain as LEAN-37):

| item | draft (`/data/api-credit/20261019/carry/`) | theorems | home module | import lines added |
|---|---|---|---|---|
| 123 | `d123-r1-s1.lean` | `eigenvalues_compression_le`, `le_eigenvalues_compression` | `ClassicalLean/Algebra/MinMax.lean` | none |
| 141 | `d141-r2-s1.lean` | `minimax_eq_of_lp` | `ClassicalLean/Analysis/FiniteGame.lean` | `ClassicalLean.Analysis.LinearProgram` |
| 143 | `d143-r1-s1.lean` | `measureReal_no_run_two_eq`, `measureReal_no_run_three_eq` | `ClassicalLean/Probability/LongestRun.lean` | `ClassicalLean.NumberTheory.Tribonacci` |
| 145 | `d145-r1-s1.lean` | `hasPrices_iff_of_lp` | `ClassicalLean/Combinatorics/ArbitrageCycle.lean` | `ClassicalLean.Analysis.LinearProgram` |
| 149 | `d1149-r3-s1.lean` | `progeny_eval_one_eq_extinctionChance`, `existsUnique_progeny`, `coeff_progeny_catalan` | `ClassicalLean/Probability/Extinction.lean` | `ClassicalLean.Combinatorics.AlgebraicGeneratingFunction`, `Mathlib.RingTheory.PowerSeries.Trunc` |

Each draft's private helpers land with it, private, inside the module's namespace. Seven witnesses in rule
2's form (section "The witnesses"). No existing declaration changes. HANDOFF section 1 and ROADMAP gain one
entry each. Every gate passes. Dustin pushes after claude-ai checks the push-review file.

## What is already true (measured by claude-ai, 2026-10-27, 19:21 to 19:30 EDT)

- Master is `67d05bfbd0efa80f0de679813b54500ae8c69122` on both remotes (VACUITY-5, pushed by Dustin at 14:20:46
  EDT; CI run 40559114678 green, 19m 19s; store row 20261027-017). The worktree
  `~/lean/classical-lean-paper-crypto` is on branch `vacuity-5` at `67d05bf`, porcelain empty.
- The five modules at `67d05bf` (lines, sha256):
  - `Algebra/MinMax.lean` 503, `2a26e6b63bcc20e99dcef03811a7346dccad941563a6992a825b13e2867ece4f`. One import
    (line 7). `open Module LinearMap Submodule` and `open scoped InnerProductSpace` (104, 105);
    `namespace ClassicalLean.MinMax` (107) to `end` (426); `variable` lines 109 to 112 bind `𝕜 E`, their
    instances, `{n : ℕ} (hn : finrank 𝕜 E = n)`, `{S T}`, `(hS)` and `(hT)`. d123 rebinds `𝕜 E n hn T hT`
    in its own binders. 5 blocks starting `example :=`, after line 426. One importer:
    `Probability/CovarianceDirections.lean` (4 `example :=` blocks).
  - `Analysis/FiniteGame.lean` 997, `19158caea54e968ef92dcd0b7842623358718b04e609b031d9af730dca53c73f`. Imports
    lines 7 to 11. `open Finset Matrix`, `open ClassicalLean.Simplex` (131, 132); `namespace
    ClassicalLean.Analysis` (134) to `end` (968); `variable {ι κ : Type*} [Fintype ι] [Fintype κ]` (136);
    sections `Bayes` (638 to 794) and `BayesFinite` (796 to 966) with their own `variable` lines. 3 blocks
    `example :=`. No importer.
  - `Probability/LongestRun.lean` 579, `2a8f7432495a9c77b3e992933fe0a30701e27c13e56bd6dcc5bb0c895a050226`.
    Imports 7 to 9. `open MeasureTheory ProbabilityTheory Finset` (107); `namespace
    ClassicalLean.Probability.LongestRun` (109) to `end` (356); `variable {Ω : Type*} {m0 : MeasurableSpace
    Ω}` (111). 6 examples, 3 of them `example :=`. No importer.
  - `Combinatorics/ArbitrageCycle.lean` 539, `ed43b6ee873538021e31e73ccd61e4f463a42239fa83ad5f528d078621d04724`.
    Imports 7, 8. `open Finset` (93); `namespace ClassicalLean.Combinatorics` (95) to `end` (529); `variable
    {ι : Type*}` (97); sections `BellmanFord` (220 to 288), `Stable` (311 to 369), `Main` (373 to 432),
    each with `variable [Fintype ι]` (and `[Nonempty ι]` in the first two). 5 examples, 2 `example :=`. No
    importer.
  - `Probability/Extinction.lean` 326, `25cb1d0978b91382cf87e06f3ad3be4523e14a82149dbd9428e3417cff8795e7`.
    Imports 7 to 10. `open Filter Topology Set` (69); `namespace ClassicalLean.Probability.Extinction` (71)
    to `end` (308); `variable {p : ℕ → ℝ}` (73); **a `section` from line 82 to its `end` at 306 with
    `variable (hp0 : ∀ k, 0 ≤ p k) (hp : HasSum p 1)` and `include hp0 hp` (84, 85): a theorem landed
    inside it gains both hypotheses.** Item 149's theorems land after line 306 and before line 308. 1 block
    `example :=`. No importer.
- The five drafts (sha256 as in `SHA256SUMS` beside them, read only): d123 `a64ae9d7…`, 64 lines; d141
  `30ab3d21…`, 123; d143 `e1527924…`, 321; d145 `b39f262e…`, 248; d1149 `bbc7c235…`, 431. claude-ai's check
  (`/tmp/claude-ai-lean37/compile/run.log`; script and prediction on helios in `~/lean37-draft/`), each
  draft with its imports, as a file under `lake env lean -DmaxHeartbeats=400000` in claude-ai's clone at
  `67d05bf`: all five rc 0, 0 errors, no `sorry`, every theorem's axioms within `propext`,
  `Classical.choice`, `Quot.sound`. They do give warnings, which must be gone when they land (the build
  allows none):
  - d123: lines 34 and 61, `simpa using hx1` never executed (unused tactic), twice each.
  - d143: line 8, the private `lrPre` (a `MeasurableSpace`) is semireducible; the linter asks for it to be
    instance-reducible.
  - d145: line 64 `if_neg` deprecated (use `ite_eq_right`); line 146 `simp [cycleSum]` never executed.
  - d1149: `if_pos` and `if_neg` deprecated at lines 49, 79, 105, 119, 120, 134, 338, 393, 403, 412 (use
    `ite_eq_left` and `ite_eq_right`); line 216 `tendsto_finset_sum` deprecated (use `tendsto_finsetSum`).
  - d141: none.
  `lake env lean` does not pass `lakefile.toml`'s `[leanOptions]` (VACUITY-5's close, trap 3), so the module
  build may show more; it is the one that counts.
- Imports: no cycle (`LinearProgram`'s, `Tribonacci`'s and `AlgebraicGeneratingFunction`'s library imports,
  followed transitively, reach none of the home modules; a script over the import lines). A file importing
  `ClassicalLean` at `67d05bf` has 5729 modules, `Mathlib.RingTheory.PowerSeries.Trunc` and the three library
  modules among them (`/tmp/claude-ai-lean37/probe/closure.out`), so no import line of this order adds a
  module to the root's closure: predicted 5729 at G too.
- Names probed (`/tmp/claude-ai-lean37/probe/`, each file importing the home module and the draft's import
  lines): `finrank_euclideanSpace_fin`, `starProjection_isSymmetric`, `LinearMap.IsSymmetric.id`, `.add`,
  `.smul` (and `IsSymmetric.id.smul` closes `(3/2 : ℝ) • id` on a span, by `simp`), `finrank_span_singleton`,
  `EuclideanSpace.single`; `ClassicalLean.Probability.LongestRun.runEvent`, `ClassicalLean.tribonacci`
  (`tribonacci 6 = 7` and `Nat.fib 5 = 5` by `decide`), `iIndepSet_iff_meas_biInter`,
  `Measure.count_apply_finite`; `HasPrices`, `NoGainCycle`,
  `forall_cycle_prod_le_one_iff_exists_prices`; `minimax_eq_of_matrix`, `payoff`; `extinctionChance`,
  `ClassicalLean.IsLocal`, `catalan`. **`Measure.infinitePi` is unknown from LongestRun with Tribonacci**
  (`longestrun.out`, rc 1, that line only), so item 143's witnesses use a finite space.
- `HANDOFF.md` sha256 `aaa3a472be8cde92ea0d7166a680d22679c31de0453fee21da68ad6d7342d640`; its section 1's last
  dated paragraph is VACUITY-5's (line 529); section 4's is VACUITY-5's (line 1124). `records/rules.toml`
  `2b5fb47dc4751d93171969649f9dc4f7b7e1233cdbc36bb06713c20e23bb0359`. The last round is 75, so this order's
  is 76. `records/orders/INDEX.md` 76 lines and `records/CLAIMS.md` 68, each last line VACUITY-5's row.
  `ROADMAP.md`'s last section of this kind is 1.30 (LEAN-36, line 911). The bridge baseline is
  `records/bridges/LEAN-36/` (VACUITY-5 ran no search); the bridges file
  (`lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md`) ends at row 167.
- At VACUITY-5's G `cf1bde0` (same library code as `67d05bf`): build 4193 jobs, 0 warnings; AxiomGate PASS
  3666; type dump 4163 records; library witness gate OK 182, copy-error 0 (VACUITY-5's report). AxiomGate's
  count has equalled the type dump's `thm` records at each of the last orders (3666 thm of 4163).
- Gate 7 is `/home/dustin/lean/recheck/run-recheck.sh <G, full hash> /home/dustin/lean/classical-lean-paper-crypto`
  under the 12 GB cap, as LEAN-36 ran it (its `evidence.log` line 1252, `ALL PASSED`).

## Statements: how they land

1. **As drafted.** Each theorem in the Goal table keeps its draft's statement, moved into its module's
   namespace. Never weaken, restate or add a hypothesis. A statement you find false is reported with its
   counterexample and narrowed, said plainly in its docstring, round 76 and the report; never dropped
   silently.
2. **Placement.** All five drafts declare at the root and move into their module's namespace block, outside
   any `section` whose `variable` or `include` lines would reach the new declarations (Extinction: after
   line 306). d141's theorem is named `ClassicalLean.Analysis.minimax_eq_of_lp`: drop the prefix inside the
   namespace. d143's own `variable {Ω : Type*} {m0 : MeasurableSpace Ω}` line is the module's line 111 and is
   dropped. The drafts need `open` lines the modules lack (d145 `ClassicalLean.LinearProgram`, for `farkas`;
   d1149 `PowerSeries`; d143 `ClassicalLean`, for `tribonacci`): give them either as `open … in` prefixes on
   the new declarations, or in one new `section` per module holding only the new declarations, its own
   `open` lines and no `variable` or `include` line, placed after the module's existing sections. No
   top-level `open` line of a module changes.
3. **The type check that the move changed nothing.** For each of the nine theorems, its type printed with
   `set_option pp.fullNames true in #check @<name>`: from the draft, in step 2, on the clean `67d05bf` build
   (a scratch copy of the draft with the nine lines appended; once a module is landed a draft copy no longer
   elaborates beside it), and from the module as landed, after its build (a scratch file importing it).
   Compared by a script that first renames universe parameters in order of appearance (the modules'
   `variable … : Type*` lines shift their numbering): only the namespace prefix of the theorem itself may
   differ. Any other difference (a gained hypothesis, a binder turned
   explicit, a different `n`) is a stop for that item until fixed. Save both outputs and the script's
   verdict.
4. **Warnings.** Every warning above is fixed in the proof text only (the deprecated names replaced by the
   ones the warning gives, the never-executed tactics removed, `lrPre` made instance-reducible as the
   linter asks). A fix that would change a statement is a stop.
5. **Expected verdicts against the plan rows** (MATH-PLAN-library-2 lines 432, 450, 452, 454, 458): 123
   FAITHFUL (Cauchy interlacing in both directions, eigenvalues in decreasing order as Mathlib numbers
   them); 141 GENERALIZED (`minimax_eq_of_matrix` has `[Nonempty ι] [Nonempty κ]`, `finitegame.out`; d141 drops both
   and settles an empty side by ℝ's junk `iInf`/`iSup` = 0, a harmless but real extension); 143
   FAITHFUL; 145 FAITHFUL (`HasPrices r ↔ NoGainCycle r`, the module's item-65 (a) ⇔ (b), by duality); 149
   GENERALIZED: the row asks `p 0 > 0`, the draft's `progeny_eval_one_eq_extinctionChance` assumes only
   `0 ≤ p k` and `HasSum p 1` (with `p 0 = 0` both sides are `0`), and it adds `existsUnique_progeny`, the
   row's "unique by the library's functional-equation theorem". The cold review checks these.
6. **New imports and existing proofs.** An existing proof that a new import line breaks is a stop under the
   Scope, not something to edit. A `PROOF-ONLY` record in the type-dump diff (an existing proof term changed
   by a new simp lemma or instance) is listed and explained as HANDOFF rule 14 says, and reported as a miss of
   the prediction `proof_only=0`; it is not a stop. `REMOVED` and `CHANGED` are stops.
7. **Vacuity gate.** A flag or an UNCHECKED verdict on a theorem of the Goal table makes its item not
   closed. On a helper: rewrite it, remove it if Mathlib or `simp` already does its job, or list it in
   `tools/vacuity_reviewed.txt` as HELPER with a one-line reason the cold review checks.
8. **Not closed.** An item not closed is undone by a new commit (never a reset): its declarations,
   witnesses, import lines, docstring entries and vacuity-list entries removed, and round 76, the CLAIMS row
   and the report saying which item and why. The others go on. An item whose proofs or witnesses do not
   build after two hours of work on it is not closed.
9. **Master does not move under you.** If `origin/master` or GitHub's `master` is not `67d05bf` at step 1 or
   when you write the push-review file, stop and report. Never merge or rebase.
10. **Nothing is added during the run.** A finding outside the Goal goes to the report's list for a later
   order, with its evidence; it is not chased. A heads-up Dustin passes in is answered in your next message
   and listed in the report.
11. **A count is what its output says.** Every count in round 76, the report and your replies is read from
   a saved output and cited by its path.
12. **G is the last commit outside `records/`.** Any commit after the gates that touches anything outside
   `records/` (a fix, a HELPER line, an item undone) becomes the new G, and every gate of step 8 reruns on it.

## The witnesses (rule 2's form)

HANDOFF section 4's "Satisfiability witnesses" paragraph: a theorem with hypotheses gets one `example` after
its module's last line that applies the theorem itself, `example := Full.name (x := …) h₁ h₂ …`, every
chosen argument by name and every binder before the colon supplied, optional `open … in` lines of their own
and no other `open` than the module's top-level ones, the docstring "The hypotheses of `name` hold together:
…" saying what moves, one inline block with no helper declaration, none of rule 2's six words (`sorry`,
`admit`, `native_decide`, `implemented_by`, `axiom`, `set_option`), nor `(config :=` or any
`reduceBool`-family name. Not degenerate (rule 3 and its two dated cases). `minimax_eq_of_lp` and
`existsUnique_progeny` have no hypotheses, so they get none. Seven blocks; the module's existing blocks are
the patterns to follow.

- **123, both theorems.** On `E = EuclideanSpace ℝ (Fin 3)` (`n = 3`, `hn := finrank_euclideanSpace_fin`),
  `T = id + P₀ + P₀ + P₁` as MinMax's existing `sum_re_inner_le_sum_eigenvalues` witness builds it
  (eigenvalues `3`, `2`, `1`); `V = span {e₀ + e₁, e₂}` (`m = 2`, the two vectors independent); `A` the
  compression of `T` to `V`, the orthogonal projection onto `V` after `T` after `V`'s inclusion
  (`Submodule.orthogonalProjection` is deprecated at this Mathlib for `Submodule.orthogonalProjectionOnto`,
  `probe2/minmax2.out`; `Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left` and `_right` exist, probed from a file
  importing MinMax, `/tmp/claude-ai-lean37/probe3/proj.out`, rc 0), so `hAT` is the projection's
  inner-product lemma and `hA` follows from `hAT` and `hT`. `A`'s eigenvalues are `5/2` (on
  `(e₀ + e₁)/√2`) and `1` (on `e₂`). First theorem `k = 0`, `i = 0` (`5/2 < 3`); second `k = 0`, `j = 1`
  (`0 + 3 ≤ 1 + 2`, and `2 < 5/2`). Not `k = 1` on the lower side (`λ₂(T) = 1 = λ₁(A)`). What must move:
  `m = 2` (rule 3's size clause; with `m = 1` every map on a line is a scalar), `V` a proper subspace not
  spanned by eigenvectors of `T`, both inequalities strict.
- **143, both theorems.** On `Ω = Fin 4 → Bool` with `P = (16⁻¹ : ℝ≥0∞) • Measure.count`, `A i` flip `i`
  comes up `true` (a loss), for `i < 4`, as LongestRun's existing `measureReal_exists_run_le` witness does
  for two flips; `n = 4`; independence by `iIndepSet_iff_meas_biInter` over the subsets of `Fin 4`. What
  must move: four fair independent flips, so runs of two and of three losses each have at least two
  overlapping windows and are possible and not certain (chance of none `fib 6 / 16 = 1/2` and
  `tribonacci 7 / 16 = 13/16`; `fib 6 = 8` and `tribonacci 7 = 13` by `decide`,
  `/tmp/claude-ai-lean37/probe3/runs.lean`, rc 0, no output). If the independence proof over 16 subsets
  is not accepted after an hour of work, `Fin 3 → Bool` with `8⁻¹` (`5/8` and `7/8`) is allowed; its
  docstring then says the run of three has a single window, and the report says why.
- **145.** `ι = Fin 3`, `r i j = 1` on the diagonal and different positive rates off it, not all equal (for
  example `2` from `0` to `1`, `1/2` back, `1/2` elsewhere), `hr` by cases. What must move: rates not all
  equal. With `2` and `1/2` the cycle `0 → 1 → 0` has product exactly `1`, which forces `p₀ = 2 p₁`, and every
  other cycle has product below `1`; the docstring says so.
- **149, `progeny_eval_one_eq_extinctionChance`.** The offspring law of Extinction's existing witness
  (`1/4` none, `1/4` one, `1/2` two; mean `5/4`, extinction chance `1/2`, strictly between `0` and `1`), its
  `hp0` and `hp` as that block proves them, and `T := Classical.choose (existsUnique_progeny p).exists` with
  `hT` from `Classical.choose_spec`. What must move: `p 0 > 0` and `p` not a point mass, so the progeny
  series has infinitely many nonzero coefficients and sums to `1/2`, not `1` or `0`.
- **149, `coeff_progeny_catalan`.** `T := Classical.choose (existsUnique_progeny _).exists` for the law
  `fun k ↦ if k = 0 ∨ k = 2 then 1/2 else 0`, written exactly as in the theorem's hypothesis, `hT` from
  `choose_spec`. What moves: the odd coefficients are the Catalan numbers over powers of `2`, all positive.
  The cold review of this order ruled this form acceptable under rule 2: it applies the theorem itself, is
  one inline block with no helper and none of the forbidden words, and `existsUnique_progeny` does not rest
  on either theorem it witnesses.

Each block is written in a scratch copy first and elaborated with `lake env lean` until accepted with no
warning, then moved into the module. A witness whose docstring says something about how a method behaves
says it only with a script behind it (LEAN-36's lesson, store row 20261026-056).

## Scope

- Branch `lean-37` from `67d05bf` in `~/lean/classical-lean-paper-crypto`. Nothing pushed. No sudo.
- You may change: the five home modules (the declarations, the import lines above, the witness blocks, the
  module docstring's lists of results); `tools/vacuity_reviewed.txt` (HELPER lines only); `records/`;
  `HANDOFF.md` section 1 (one dated LEAN-37 paragraph after VACUITY-5's); `ROADMAP.md` (a section 1.31 after
  1.30, in 1.30's form). Nothing else; needing to is a stop. A new warning in an existing declaration is a
  stop.
- Your files: `~/lean/lean37-checks/`. Nothing untracked in the worktree.
- Lane writes, through the connector (`ds_file`, project `lean`, job `LEAN-37`): the report (kind
  `report`) and the push-review file (subdir `data`, name `LEAN-37-push-review.txt`); a real bridge as a new
  row of the bridges file from row 168 (`ds_write_staging`, append, `expect_sha256` its hash when you read
  it; a refused write is a stop). Read lane files through the connector, not a local path (VACUITY-5's
  miss 3).
- Off limits as in every order: `~/lean/classical-lean` and its `master`, every earlier order's folder (read
  only), `~/api-credit/` and `/tmp/claude-ai-*` (claude-ai's; read only), `/data/api-credit/` (read only),
  Dustin's `~/.config/classical-lean/banned-terms` (never print or copy it), every GitHub branch.
- Lean runs: one at a time, under the 12 GB cap (`systemd-run --user --scope -q -p MemoryMax=12G
  -p MemorySwapMax=0`), `~/.elan/bin` on `PATH`, `pgrep -ax lean` empty before each (not `pgrep -a lean`,
  which matches `smbd: cleanupd`), outside the window.

## The work

1. **Check.** Launch variable; `git fetch origin`; `git ls-remote origin master` and `git ls-remote github
   master` both `67d05bf…`; porcelain empty; the sha256s above (the five modules, the five drafts, HANDOFF,
   rules.toml); `pgrep -ax lean`. If anything differs, stop.
2. **Before.** Copy `lean/LEAN-33/scripts/TypeDumpPI.lean` (sha256
   `1fcb69f41ddbd35f84862521d2ead5946a0bd52caf5f60b6d10e966cfd9776ff`) and `g8-typediff.py`
   (`371eda9a2e5065abaa8f36bac9872d0f15e7bade72a248d5f0f88f20b4eacb71`, saved as `g8_typediff.py`) from the
   lane through the connector into `~/lean/lean37-checks/`, checking each hash. On a clean `67d05bf`, from
   the repository root: `lake build`, then `lake env lean ~/lean/lean37-checks/TypeDumpPI.lean >
   ~/lean/lean37-checks/td-before.out`, its lines starting `{` kept in `td-before.jsonl`, and
   `python3 -I ~/lean/lean37-checks/g8_typediff.py check td-before.jsonl`: 4163 records. Then the draft side of
   the type check (rule 3 of "Statements"), on this clean tree.
3. **Branch and records.** `git switch -c lean-37 67d05bf`. One records-first commit as `records/README.md`
   says, no `.lean` file: this order's copy in `records/orders/`, its INDEX and CLAIMS rows, round 76's
   fragment naming the five modules by full path, and VACUITY-5's push recorded in VACUITY-5's INDEX and
   CLAIMS rows the way LEAN-36's was (text: `; pushed by Dustin: master 67d05bf on both remotes, CI run
   40559114678 green`). check_records PASS.
4. **Land, one commit per module,** suggested order by draft length: MinMax (123), FiniteGame (141),
   ArbitrageCycle (145), LongestRun (143), Extinction (149). Per module: the declarations, `open` lines and import
   lines in place; the warnings fixed; the witnesses; `lake build ClassicalLean.<Area>.<Module>` and its
   importers (for MinMax, `lake build ClassicalLean.Algebra.MinMax ClassicalLean.Probability.CovarianceDirections`),
   0 errors, 0 warnings; then the type check (rule 3 of "Statements"); `python3 -I tools/witness_gate.py
   <Area>/<Module>.lean` (the path relative to `ClassicalLean/`, as VACUITY-5 ran
   `python3 -I tools/witness_gate.py Probability/YuleWalker.lean`), every block OK, `copy-error=0`, OK counts MinMax 7,
   FiniteGame 3, ArbitrageCycle 3, LongestRun 5, Extinction 3 (a non-OK line on an older block is a stop:
   report it, do not edit it); then the commit, staged by path.
   When all five are in: `lake build` (the root), then `lake env lean tools/VacuityGate.lean` and
   `python3 -I tools/run_vacuity_tests.py` (rule 7 of "Statements"), before step 6, so that any helper
   rewritten or listed as HELPER is in the review packet and in a module commit before G.
5. **Expected results.** Before step 7, one file in `~/lean/lean37-checks/` with the expected result of
   every gate, written from the counts the landed text gives: the type dump's `added=` (the new constants a
   file importing each landed module lists under `ClassicalLean`, compared with the same list at `67d05bf`),
   and AxiomGate's count as 3666 plus the new `thm` constants. Its sha256 in the report.
6. **One cold review** of the five items, by one fresh subagent that has not seen your work: give it the
   nine statements as landed with their plan rows (MATH-PLAN-library-2 lines 432, 450, 452, 454, 458), the
   type check's verdicts, the seven witness blocks, HANDOFF section 4's "Satisfiability witnesses" paragraph
   with its dated cases, this order's "The witnesses" section, and every private helper's statement, and any HELPER line with its reason. It
   gives each theorem FAITHFUL, GENERALIZED or WEAKER (WEAKER is a finding), checks each witness against
   rule 2's form and rule 3 (what must move does move), rules on 149's witness built on its own existence
   theorem, and says for each helper whether Mathlib or the module already has it. Fix what it finds (a fix
   to a module reruns that module's step 4 checks); a second pass, on the fixes only, only if a fix changes
   a statement or a witness's arguments.
7. **Documents,** before the gates: HANDOFF section 1's LEAN-37 paragraph (the five items by name, module
   and number, the GENERALIZED verdicts of 141 and 149, and step 5's counts given as predictions "to be
   re-measured by its gates", in LEAN-36's wording, HANDOFF line 524); ROADMAP section 1.31; one commit. This
   commit is G. Then `python3 tools/compile_rules.py drift records/rules.toml HANDOFF.md` on it (PASS,
   written in step 5's file first). The measured counts go only in round 76, so a count that differs from
   the prediction is a miss reported there, not a new commit.
8. **Gates on the clean tree at G** (the documents commit of step 7: the last commit that touches anything
   outside `records/`), each beside its expected result: `lake build` (4193 jobs, 0 errors, 0 warnings); `lake env lean tools/AxiomGate.lean`
   (PASS, the count from step 5); `python3 -I tools/check_sorry.py`; `python3 -I tools/check_records.py`;
   `lake env lean tools/VacuityGate.lean` and `python3 -I tools/run_vacuity_tests.py`;
   `python3 -I tools/banned_vocab_scan.py ClassicalLean`; the whole-library witness gate
   `python3 -I tools/witness_gate.py` (PASS, OK 189 = 182 + 7, copy-error 0, about 27 minutes) and
   `python3 -I tools/witness_gate_tests.py`; the module count of a file importing `ClassicalLean` (5729);
   the type dump again into `td-after.jsonl` and `g8_typediff.py diff td-before.jsonl td-after.jsonl` (read
   by its `DIFF` line: `removed=0 changed=0 proof_only=0`, `added=` step 5's list; a `REMOVED` or `CHANGED`
   line is a stop); gate 7 last (`ALL PASSED`, 140 modules, 0 failed, the three standard axioms, its planted
   fault named, about 22 minutes). Then the bridge search, `python3 -I tools/bridge_search.py --diff
   records/bridges/LEAN-36/ --out ~/lean/lean37-checks/bridges/LEAN-37` (rc 1 means candidates): read each
   NEW import-unrelated pair and NEW shape for a theorem whose proof needs both sides; append a real one from
   row 168; say how the pairs were read; write the new baseline to `records/bridges/LEAN-37/`. Then the
   report tool, `lake env lean tools/UninformativeReport.lean`, once, its `CLOSES` lines naming this order's
   theorems listed (a report, not a gate).
9. **Records.** Round 76's fragment completed with the commit hashes and the counts from the gates' output;
   the CLAIMS row closed and the INDEX row set; one records-only commit; check_records PASS at the final
   HEAD.
10. **Report** (`ds_file`, kind `report`): each item's final statement, verdict, witnesses and what moves;
   the type check's verdicts; the review and its fixes; each gate's expected and observed result, cited from
   its output; the bridge diff and how it was read; the `CLOSES` lines for this order (or "none"); findings
   outside the Goal; misses and anything not closed; the push command as one line, not run:
   `cd ~/lean/classical-lean-paper-crypto && git push origin lean-37:master && git push github lean-37:master`.
11. **Push-review file** (`ds_file`, subdir `data`, name `LEAN-37-push-review.txt`), by one script, each
   command with its full output: `git rev-parse HEAD`; `git status --porcelain`; `git ls-remote origin
   master` and `git ls-remote github master` (both still `67d05bf`); `git log --name-status --format='== %h
   %cI %s' 67d05bf..HEAD` (files under `records/bridges/` as a count); `git diff --name-only 67d05bf <G> --
   ClassicalLean.lean tools .github ':(glob)lakefile*' lake-manifest.json lean-toolchain records/rules.toml`
   (only `tools/vacuity_reviewed.txt`, if a helper was listed); `git diff --name-only 67d05bf <G> --
   ClassicalLean` (exactly the five modules); `git diff -U0 67d05bf <G> -- ClassicalLean | grep
   '^[-+]import'` (exactly the five `+` lines of the Goal table); `git diff -U0 67d05bf <G> -- ClassicalLean
   | grep '^-' | grep -v '^---' || true` (only lines of the five module docstrings); the type-dump `DIFF`
   line; the whole-library `WITNESSGATE` line with its time; gate 7's summary line; `grep -rnwE
   'reduceBool|reduceNat|ofReduceBool|ofReduceNat|trustCompiler|native|plausible|slim_check|evalExpr|evalConst'
   ClassicalLean/ || true` and `grep -rn '(config *:=' ClassicalLean/ || true` (each nothing); `git diff -U0 67d05bf <G> -- ClassicalLean | grep '^+open' || true` (only the `open` lines rule 2 of
   "Statements" allows, each named); `grep -nE 'set_option|implemented_by|\badmit\b|\bsorry\b|\baxiom\b'`
   on the five modules (only ArbitrageCycle line 45, prose: "Quotes that admit no prices"); `git diff
   --name-only <G> HEAD` (only `records/`). Then stop: claude-ai reviews it before Dustin pushes.

## Done means

Branch `lean-37` from `67d05bf`, clean, nothing pushed; the nine theorems in their modules with no `sorry`
and no new axiom, as drafted, each type check passed, or each narrowing or item not closed said plainly;
141 and 149 GENERALIZED and said so; seven witnesses, each OK in the witness gate and passed by the cold review; no existing declaration changed
(type dump `removed=0 changed=0`, and `proof_only=0` or each PROOF-ONLY record explained); every gate in step 8, gate 7 among them, and the drift check pass; the
documents and records committed; the report and the push-review file in the lane, their hashes matching
yours. Then tell Dustin in a few plain sentences what was proved and what moves in each witness, defining any
technical term the first time, and give the two files' hashes and the push command.

## Not in this order

LEAN-38 (bridges 160 to 162 and the pair-by-pair reads, plan 2 ruling 5); TWINS-1; GATE-2; the follow-ups
listed in START-HERE (MethodOfTypes' docstring, FiniteChain's title, GamblersRuin's unused import,
MaximalInequality's two-step witnesses); drop tests of witnesses; any push.
