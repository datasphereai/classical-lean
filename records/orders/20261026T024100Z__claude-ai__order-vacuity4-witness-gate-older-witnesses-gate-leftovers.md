# VACUITY-4 order: the witness gate, the older witnesses brought to rule 2, and the gate leftovers

For a plain Claude Code session on DSMain, as dustin, in tmux `cc`, started with
`CLAUDE_CODE_DISABLE_AUTO_MEMORY=1` in its environment (store rows 20261025-036, -043, -048). Written
by claude-ai in the claude.ai Project LEAN on 2026-10-25, under claude-ai's ruling of that day that
the gate order comes before LEAN-36 (store row 20261025-104, Dustin's veto open). This is the order
(r5: the cut, r3, with its two review passes applied as r4 and r5): the values the draft left for the
cut were measured on 2026-10-25 from 11:12 to 12:18 EDT at `ac62f50` ("Measured at the cut") and are
filled in. Lane files named `lean/...` are under
/opt/datasphere/lane/inbox/threads/staging/lean/ (ds_* tools: root `lane`, path
`inbox/threads/staging/lean/...`).

**New lane files go through `ds_file`** (project `lean`, job `VACUITY-4`): your plan is kind `plan`
(it lands as `lean/VACUITY-4/plan.md`), the report kind `report`, the push-review file subdir
`data`, name `VACUITY-4-push-review.txt`. Compare each reply's `post_sha256` with your own. **Track
the order's steps with the task tools** (lane `lean/NOTE-20261015-task-list-rule.md`).

Review: the draft r0, on 2026-10-25, by a fresh subagent (pass 1: PASS WITH FINDINGS, 0 BLOCKER, 11
MAJOR, 19 MINOR, all applied, r1) and a confirming pass by the same reviewer (NOT CONFIRMED: 26 of the
30 fixed, 4 partly; 1 new BLOCKER, brought in by r1's change to `WRONG-NAME`, and 13 new MINOR, all
applied, r2; r2 not reviewed again as a draft). Review of the cut (r3), by one fresh subagent with a read list, a text record of every DSMain output and a 40-call limit per pass: pass 1, PASS WITH FINDINGS (0 BLOCKER, 1 MAJOR, 14 MINOR; `rv-cut-pass1.md`, sha256 `1452355d4323e63091a53e4696c5a047530a00b7ffd6e8a38800b32c23abdaf3`), all applied, r4; pass 2 by the same reviewer, NOT CONFIRMED (14 of 15 FIXED, 1 PARTLY FIXED; 0 BLOCKER, 0 MAJOR, 9 new MINOR; `rv-cut-pass2.md`, sha256 `3ae47c89b769b554447cd1faa668128cf534581072a5ba682785cea28c1a3a5f`), all applied, r5; r5 not reviewed again. Not reviewed: how Lean itself attaches a docstring across comments and `set_option … in` (the reviewer and claude-ai worked from what they know of Lean's lexer; the reviewer had no toolchain); the DSMain outputs themselves (the reviewer read claude-ai's text record of them; claude-ai checked the order's hashes and the 46 sweep items against DSMain by script); the parts of the order unchanged since r2, beyond consistency checks; `HANDOFF.md`, `records/README.md` and the store rows the order cites.

## Why this order

Four threads that the record says belong to "the next gate order" and that no landing order may take
(a landing order's Scope forbids `tools/` and `.github/`):

1. **A witness cut short passes every gate** (store row 20261021-033). LEAN-34's cold review (c) found
   item 140's witness applied to only some of its arguments; Lean elaborated it, the build gave 0
   warnings and the vacuity gate passed. LEAN-34's session wrote a check for it, `mkwitcheck.py` (lane
   `lean/LEAN-34/data/mkwitcheck.py`, sha256
   `fac60ab63a4708b36ef58f6274e8bea2aa79f8afbb0ed27e0324a3208669507a`), which has had one read by
   claude-ai and no cold review. Run once over the library at `9ef33f0`
   (`~/lean/lean34-checks/witsweep-summary.md` on DSMain), it confirmed 137 of the 145 `example :=`
   blocks then present. It did not confirm 7, each for a blind spot of the check (Algebra/MinMax's 3
   got no verdict: one block sits inside the module's namespace and names its theorem without the
   prefix, so the separate check file did not elaborate; Analysis/FrankWolfe's 1 and
   Probability/PolyaUrn's 3 use private lemmas a separate file cannot name), and NumberTheory/
   PrimitiveDivisor's line 423 is a name-resolution check, not a witness (LEAN-34's report-r2, "The
   witness check"). LEAN-35 ran the same check on its own six witnesses only (its rule 13). Nothing
   checks the library's witnesses at every push.
2. **Witnesses in the older `∃` form.** HANDOFF.md §4's standing rule of round 58 says a
   satisfiability example applies the theorem itself, not an `∃` restatement. Thirteen typed
   `example`s carry a docstring that claims a witness ("hypotheses of", "hypothesis of", "hold
   together" or "can be met together"): ten in the older `∃` form or a typed restatement, found for
   the draft, and three with the singular "hypothesis of", found at the cut. Twelve name theorems,
   and one (Order/Superadditive) names "the results above". They are listed under "What is already
   true".
3. **A process that stops moving inside the horizon tests nothing.** LEAN-35's cold review (c) found
   item 125's first witness degenerate: its walk made one fair step and then stood still, inside the
   horizon `n = 2` (lane `lean/LEAN-35/report.md`, sha256
   `6c56b5353f9df4559c2cfcc2f9dae0efddcd2a92f528da0186a4516110e0fcbb`, "In short" and "Reviews"; it
   was replaced before its commit). The same report lists two older witnesses with the same fault,
   in Probability/MaximalInequality (of `measureReal_exists_abs_ge_le` and `integral_sup_sq_le`), and
   recommends a sweep of every witness for a process that stops changing inside the theorem's
   horizon. claude-ai's own approval of LEAN-35's plan had called that witness allowed after checking
   only its arithmetic (R8, store row 20261025-097).
4. **Gate leftovers.** Order VACUITY-3's ruling 3 (lane `lean/VACUITY-3-ruling-3.md`, sha256
   `aa0d17e403031b81d0e0803c3308002ed985b416d788980de0f61cc79e13a4f2`), item 3, and HANDOFF.md §4
   ("Left for a later gate order"): the report tool's whole-library command runs under
   `set_option maxHeartbeats 0 in` (no outer budget), and the vacuity gate's FAIL text lists the cases
   but omits case 5 (a glued conclusion) and does not say what UNCHECKED or KERNEL-REJECTED mean.

And one thread that this order **records** but does not build: the research actions' step 4 (lane
`server/RESEARCH-ACTIONS-1/plan.md`, lines 66 to 67: "add lean4checker (re-check outside the build) to
the gates, and comparator for AI-drafted statements, in the next Lean order").

**Three departures from claude-ai's ruling of 2026-10-25 (store row 20261025-104), each with its
reason, Dustin's veto open:**
- Row 104 (and row 20261021-033) say the check goes "into the vacuity gate". It becomes a gate of its
  own, `tools/witness_gate.py`: an `example` adds nothing to the environment, so `VacuityGate.lean`,
  which imports `ClassicalLean` and walks its constants, cannot see a witness; a check has to read
  each module's text and elaborate it again, which is what `mkwitcheck.py` already does.
- Row 104 asks for "a check for witnesses whose process stops changing". A process's increments are
  values the gate cannot compute in general, so the check is a rule (rule 3's new case, Goal item 4)
  met by review and a sweep (Goal item 5), not a machine check.
- Row 104 says the order "takes research actions step 4". Measured below: the re-check outside the
  build has been gate 7 since order RECHECK-1, and comparator exists as `lake comparator` only from
  Lean v4.35.0 on; so step 4 is recorded (Goal item 8), not built.

## What is already true

### Measured by claude-ai on 2026-10-25 for the draft, from 09:31:48 EDT, at `ac62f50`

On DSMain over ssh from helios, read-only, in `~/lean/classical-lean-paper-crypto` on branch
`lean-35` at `ac62f505db03edda95e7f7fa83a301a07ddda924` (LEAN-35's last commit; pushed by Dustin to both
remotes on 2026-10-25, store row 20261025-102; its CI run #39 green in 20m 8s, row 20261025-106), `git
status --porcelain` empty before and after every run. Outputs in `/tmp/claude-ai-gate1/` on DSMain:
`g1-tree.out`, `g2-ci.yml`, `g3-handoff-s4.md`, `g4-handoff-s6.md`, `census.out` (sha256
`f733c307bb88f1646a3072b76c722ad7acae59fde17ff77b8b4cea92110f8321`, from `census_examples.py`
`0fffdb7572a3e0b81ae8e81e02e0ff2c569899e1f47e7537baed1c3eabed5a3c`), `claims.out`
(`496e871f1ef92d6b84d8180585782d4612a7d06b1650babb2bb2acaede5ca89d`, from `typed_witness_claims.py`
`063ccb1428a057ee92c60915e8d6252c0aef525e61e9ece519e74129a8b2dfab`), and `draft-facts.txt`
(`686103c350c6d4ec185ba06b909e5d28eb92b920ee5a8143a74e96b8b8947d61`, 50649 bytes: the files this
section quotes, each part with its own sha256). Both scripts are Appendix A.

- **Toolchain.** `lean-toolchain` is `leanprover/lean4:v4.34.0`; the manifest pins Mathlib at
  `5ed2965256430c3649e86755f9576b54eca72435` (`v4.34.0`).
- **The gates in `tools/`** (`git ls-tree`): `AxiomGate.lean`, `VacuityGate.lean` (52000 bytes),
  `VacuityGateTests.lean`, `run_vacuity_tests.py`, `vacuity_reviewed.txt`,
  `vacuity_reviewed_tests.txt`, `UninformativeReport.lean`, `check_sorry.py`, `check_records.py`,
  `banned_vocab_scan.py`, `bridge_search.py`, `compile_rules.py`, `build_registry.py`, and their tests.
  CI (`.github/workflows/ci.yml`, sha256 at the cut
  `2dc680ea9b745963f72fd49835ae433286a56564bf643aeccf90b220f03b8182`) builds with
  `leanprover/lean-action` and then runs,
  each `if: ${{ !cancelled() && steps.lean.outcome == 'success' }}`, the axiom gate
  (`lake env lean tools/AxiomGate.lean`), `check_sorry` (`python3 -I tools/check_sorry.py`) and the
  vacuity gate (`lake env lean tools/VacuityGate.lean`), then the Rules gate; the job's
  `timeout-minutes` is 90. HANDOFF.md §4's CI paragraph (dated 2026-10-15, order MERGE-1) still names
  the workflow's sha256 from order CLOUD-1 (`0d750843…`); order RULES-1 added the Rules gate since.
  CI run #39 (`ac62f50`) took 20m 8s, #38 (`f5411f4`) 12m 0s (the Actions page, read in Dustin's
  Chrome on 2026-10-25).
- **The `example` lines** (`census.out`): 370 lines start `example` under `ClassicalLean/`: 151 start
  `example :=` (witness form, in 70 modules), 168 start `example :` (typed), 50 start with a binder
  (`example (`, `example {`, …), and 1 is a line of a module docstring that starts with the word
  `examples` (NumberTheory/Pell, line 58; Goal item 1's `UNREAD` pattern, which ends in `\b`, does
  not match it, so 369 lines match that pattern, all at column 0). 211 of them sit inside a namespace (49 binder, 161 typed, 1 witness form: Algebra/
  MinMax line 443). Two witness-form blocks have no docstring of the form "The hypotheses of
  `NAME` hold together": Algebra/MinMax line 443 (it applies `sum_eigenvalues_eq_iSup` to the identity
  on `ℝ²` with `k = 1`; its docstring says "Ky Fan applied on a concrete space") and NumberTheory/
  PrimitiveDivisor line 423 (`example := And.intro @Nat.emultiplicity_pow_sub_pow
  @Int.emultiplicity_pow_sub_pow`).
- **The typed examples that claim a witness**, 13: the 10 that `claims.out` found (a docstring with
  "hypotheses of", "can be met together" or "hold together") and 3 that the cut's wider scan found
  (`claim-scan-2.out`, the singular "hypothesis of"):

  | module, line | theorems its docstring names | a rule-2 witness of it in the module already |
  |---|---|---|
  | Algebra/Kantorovich 216 | `dotProduct_mulVec_mul_inv_le` | no |
  | Algebra/Kantorovich 225 | `dotProduct_mulVec_mul_inv_add_eq` | no |
  | Algebra/MinMax 427 (inside the namespace) | `sum_mul_le_sum_of_antitone` | no |
  | Algebra/MinMax 434 (inside the namespace) | `sum_re_inner_le_sum_eigenvalues`, `sum_eigenvalues_eq_iSup` | no (line 443 applies the second, without the docstring) |
  | Analysis/ConvexConjugate 126 (inside the namespace; the cut) | `convexConjugate_anti` | no (an `∃ f g, f ≤ g`) |
  | Geometry/Spectral3x3 175 (inside the namespace; the cut) | `gap_identity_of_offDiagCross_eq_zero` | no (the module has no witness-form block) |
  | InformationTheory/CompressionTest 462 | `integral_eFalseShare_score_le`, `integral_eFalseShare_score_le_mul_card_div` | no |
  | Order/Superadditive 116 | none by name ("the results above") | no (the module has no witness-form block; five theorems, each taking `hf`: the module table under "Measured at the cut") |
  | Probability/EffectiveSampleSize 583 | `variance_sum_eq_of_stationary`, `variance_sum_div_eq`, `variance_sum_eq_mul_one_add` | no |
  | Probability/EffectiveSampleSize 595 | `variance_sum_range_eq_of_stationary` | no |
  | Probability/GamblersRuin 1046 | `ae_exitTime_ne_top_of_biased`, `measureReal_hit_eq_of_biased`, `measureReal_exists_ge_le_of_biased` (and Mathlib's `ProbabilityTheory.exists_iid`, named as a tool) | no |
  | Probability/LongestRun 268 | `measureReal_no_run_le` | yes (a witness-form block with the docstring) |
  | Statistics/GeneralizedLeastSquares 261 (inside the namespace; the cut) | `glsMatrix_ones_eq_minWeights` | no (a typed application of the theorem) |

  Of the ten that `claims.out` found, `witsweep-summary.md` (LEAN-34's) lists nine by claude-ai's
  count, all but Superadditive's; claude-ai did not look there for the cut's three. Of the 18
  theorems the twelve claims name, only LongestRun's `measureReal_no_run_le` has a witness-form block
  anywhere in the library (`census2.out`, matched by NAME, at the cut). VACUITY-3's report put LongestRun's older `∃` example at line 209: it is the block
  now at 268. Its docstring ("The hypotheses of `measureReal_no_run_le` hold together (order LEAN-28,
  …") is at line 208 at `e81ab8a` (the commit that `git blame` gives for line 268, "LongestRun: cold
  review r87's five findings"), 209 at `b0b4f5e` and at `49bcd41` (VACUITY-3's group 11), 263, 264
  and 265 at LEAN-29's three commits, and 265 at `ac62f50` (`cut-facts-3.out`).
  The cut's wider scan (`claim_scan2.py`: typed and binder examples whose docstring has `hypothes`,
  `witness`, `satisf`, `assumptions of`, `consistent`, `vacuous`, `inhabited` or `nonempty`) found,
  besides the 13, five that claude-ai read and judged not to claim a witness: NumberTheory/
  LucasApparition 442 ("with no hypothesis on `N`": a statement), NumberTheory/PrimitiveDivisor 412
  (a stronger form of a theorem, proved in place), NumberTheory/Tribonacci 196 (trace sums that
  "satisfy" a recurrence), Probability/LongestRun 289 (why a hypothesis is kept: a counterexample
  without it) and Statistics/CramerRao 265 ("its hypotheses discharged": the theorem
  `posSemidef_weightedCov_sub_inv_secondMoment` applied at the categorical family with three
  hypotheses left as binders; a specialization, not a claim that the hypotheses hold together; that
  theorem has no rule-2 witness, and not every theorem has one; this order adds none). Later scans,
  after the cut's reviews (`claim_scan3.py`, then `claim_scan5.py`: blocks and docstrings as Lean
  reads them, whitespace collapsed, more wider words; `claim_scan5.py` uses the gate's four phrases and
  Goal item 1's docstring rule, and its output equals `claim_scan3.py`'s byte for byte), found the
  same 13 and one more wider hit, Probability/EffectiveSampleSize 610 ("Why … need the finite
  measure": a counterexample, not a claim); "can be met" occurs in 4 typed or binder docstrings, all
  among the 13. So the gate's `TYPED-CLAIM` phrases are four:
  "hypotheses of", "hypothesis of", "can be met", "hold together" (Goal item 1). The cut's first scan
  (`claim_scan.py`) also listed two binder examples of
  NumberTheory/PrimitiveDivisor (lines 363 and 401) with another block's docstring: each sits under a
  `/-! … -/` section comment, and the scan walked back past it. The second scan and
  `census_examples2.py` take a docstring only from a `/--` comment that ends just above; the census
  did not change (`census2.out` equals `census.out` byte for byte).
- **claude-ai's predictions for these two runs and their misses** (`pred-census.txt`, sha256
  `0324642adf8751c99930ad45a7ba300e6072ec2d4b258480d1a0c8bfcea47ce5`, and `pred-claims.txt`,
  `2908184687cbdb2926bd474d59fdda59d17bf1ae2f72d85300c18c0ce486ef04`, in claude-ai's scratchpad,
  hashed before the runs): the census's totals all held
  (370; 151, 168, 50, 1); "at least 3 witness-form blocks inside a namespace" missed (1: MinMax's other
  two are typed); "about 9 typed or binder examples with a witness docstring" missed against the
  census's narrower phrase (`census.out`, "== TYPED OR BINDER WITH A WITNESS DOCSTRING 4", the four
  whose docstring says "The hypotheses of `NAME` hold together") and the claims script's three phrases
  (10). At the cut, the predictions were `pred-cut-facts.txt`
  (`c088c0d43d7973f59ac71a007582bb0bee46009d369844f660a4fb48befa3876`), `pred-cut-3.txt` (a line added
  before each later run, each time hashed; last `cb789377954f903ba7a7b466dbc48566fffeeb76b19d5b9baad4276d6a87c9bc`),
  `pred-cut-4.txt` (`bf6626f8972bbd9940238f23d90a9e5ae6e43eea7378647615d0f4b3d2ed58ce`),
  `pred-cut-5.txt` (a line added before `claim_scan5.py`'s run; last
  `eff3fe4817afdffedbdc0e592d8d25a094da18974131dfbd068e787f6674f7d0`) and the docstrings of
  `claim_scan.py`, `claim_scan3.py`, `claim_scan4.py`, `claim_scan5.py` and `name_scope.py`, all
  written before their runs. Held: the masters, the options, the heartbeat lines, the records' and
  helpers' counts, LongestRun's one witness-form block of `measureReal_no_run_le` (457), the census's
  equality, the 369 lines, every prediction of `claim_scan3.py`, `claim_scan5.py` and `name_scope.py`,
  the records-only diff, the earlier push form, the dotted name's check, and the Rules gate's "not
  `tools/`". Missed: `pred-cut-4.txt`'s "compile_rules.py scans ClassicalLean/" (it opens only its
  arguments); `claim_scan4.py`'s DOC-DIFF 0 (8: a bug of its own, below); `claim_phrases.py` (an earlier
  helper, run by `cut_facts.sh`) printed 4 lines, not 0 to 3; `claim_scan.py`'s 11 claims (13: the
  ConvexConjugate and GeneralizedLeastSquares ones were not foreseen) and its "lines matching the
  `UNREAD` pattern equal the lines starting `example`" (369 against 370: Pell 58); the second scan's
  other hits (5, not 6: PrimitiveDivisor 363 also sits under a section comment); each copy's time (4
  to 7 seconds, not 1 to 4 minutes); and the sweep selection needed three tries (below). Not
  confirmed: "line 268's blame is a LEAN-28 commit": it is `e81ab8a`, whose subject names no order,
  though the docstring it wrote says "order LEAN-28".
- **MaximalInequality's two frozen witnesses** (read, lines 690 to 745): the witnesses of
  `measureReal_exists_abs_ge_le` (line 697) and `integral_sup_sq_le` (line 736) both use, under the
  uniform probability on `Fin 2` with the filtration that knows nothing at time `0` and everything
  from time `1`, the walk `S 0 = 0`, `S n = (1, −1)` for `n ≥ 1`, at `n = 2`; their docstrings say
  "one fair `±1` step, then still". Line 779 is LEAN-35's item 125 witness, review (c)'s replacement:
  two points, `S 0 = 1/2`, one fair step, `n = 1` (LEAN-35's report, "The items"). On two points with a
  filtration that knows everything from time `1`, every martingale is constant after time `1`
  (`E[S₂ | 𝓕₁] = S₂`). A martingale that moves at each of `n` steps needs at least `n + 1` points
  (each moving step has to split an atom of the filtration); `n` independent fair coins on `2^n`
  points, or a product of coins (as GamblersRuin's witness of `measureReal_hit_eq` builds its space),
  is the usual way (cold review pass 2, N1).
- **The re-check is already a gate.** Gate 7, `~/lean/recheck/run-recheck.sh` (sha256
  `ec932243f06e57946711cebfd23d5e6985a7a0fa02601e976ee12b713069a4a0`, 117 lines, order RECHECK-1, its
  logs in `~/lean/recheck/` dated 2026-10-09), runs the toolchain's `leanchecker` (`lake env
  leanchecker -v`, one module per process, each under a 12 GB scope: `leanchecker-each.sh`) and then
  exports every `ClassicalLean` constant with `lean4export` (tag `v4.34.0`) and checks the export with
  nanoda, an independent kernel, permitted axioms `propext`, `Classical.choice`, `Quot.sound`; then it
  plants one wrong proof in the export and passes only if nanoda rejects exactly that theorem.
  LEAN-35's gate 7 at `d21fd22`: ALL PASSED, `SUMMARY modules=140 failed=0` for leanchecker
  (`~/lean/recheck/run-d21fd22/leanchecker.txt`; both checked again at the cut). The v4.34.0 toolchain's `bin/` has `leanchecker`.
  So the research plan's "lean4checker (re-check outside the build)" has been in the gates since
  RECHECK-1, in a stronger form (a second kernel and a planted fault), though the plan's step 4,
  written later, did not note it; it runs on DSMain, not in CI (HANDOFF.md §4, "CI": 28 GB uncapped).
- **Comparator** (read by claude-ai on 2026-10-25): Comparator checks that a solution file proves the
  theorems a challenge file states, with only permitted axioms, building and exporting each in a
  sandbox (`landrun`) and replaying the solution through the kernel (its Reservoir page,
  reservoir.lean-lang.org/@leanprover/Comparator: latest 0.1.0, its latest commit built on Lean
  v4.36.0-rc1; it says Comparator was merged into Lean core in v4.35.0 as `lake comparator` and `lake
  check`). Lean v4.35.0's release notes (lean-lang.org/doc/reference/4.35.0/releases/v4.35.0/) list
  `lake check` (build, export, replay through the kernel; #14990), `lake comparator` (#14885, #15146),
  external checkers bundled with the toolchain (#15048, #15099, #15130, #15153; `leanchecker-paranoid`,
  #14884), `--paranoid`, which runs them besides Lean's own kernel (#15145), and checking an export made
  elsewhere (`--from-export`, #15050 and #15157). The library is on v4.34.0, where `lake comparator`
  and `lake check` do not exist.

### Measured at the cut (claude-ai, 2026-10-25, 11:12:29 to 12:17:40 EDT, at `ac62f50`)

The cut's first three scripts ran from 11:12:29 to 11:27:48; the checks for review pass 1
(`cut_facts4.sh`) from 11:56:59 to 11:57:04, with a few reads after; those for review pass 2
(`cut_facts5.sh` and `claim_scan5.py`) from 12:15:19 to 12:17:40.

On DSMain over ssh from helios, as dustin, in `~/lean/classical-lean-paper-crypto`, read-only: `git
status --porcelain` empty before and after every script; `pgrep -ax lean` rc 1 before every Lean run;
each Lean run alone, under `systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0
/usr/bin/time -v` (as `ev.sh --cap`), from the repository root, with `nice -n 19 lake env lean` and the
lakefile's four options as `-D` flags (as `el.sh`). Scripts and outputs are in `/tmp/claude-ai-gate1/`;
the scripts the order relies on are in Appendix A, byte for byte; `cut-manifest-r5.txt` there lists the
sha256 of every DSMain file the session must check (not every file this order mentions: LEAN-34's
`witsweep-summary.md`, gate 7's logs and the draft's `g1` to `g4` outputs are cited, not checked).

- **Master and tree.** `git ls-remote origin master` and `git ls-remote github master`: both
  `ac62f505db03edda95e7f7fa83a301a07ddda924`; HEAD the same, branch `lean-35`. After LEAN-35's G
  (`d21fd22`) come `8421cef` and `ac62f50`, both records only (`git diff --name-only d21fd22
  ac62f50`: six files, all under `records/`: `CLAIMS.md`, `bridges/LEAN-35/` `COMMIT`, `pairs.tsv` and
  `shapes.tsv`, `orders/INDEX.md`, and round 72's fragment). `lake build --no-build`: "All targets
  up-to-date (4193 jobs)", rc 0.
- **The lakefile's `[leanOptions]`** (`lakefile.toml`): `pp.unicode.fun = true`,
  `relaxedAutoImplicit = false`, `weak.linter.mathlibStandardSet = true`, `maxSynthPendingDepth = 3`
  (HANDOFF rule 20's four, nothing else).
- **The gates' counts at the master.** Not re-run at the cut: they are LEAN-35's at its G, as its
  session measured them (lane `lean/LEAN-35/report.md`, "Predicted beside measured" and "The report
  tool"), since only `records/` changed after G. Build 4193 jobs, 0 warnings; AxiomGate PASS 3602;
  VacuityGate PASS, 1 reviewed helper, 0 VACUOUS-PENDING; vacuity tests 89, 47 flagged, 0 run-outs, 0
  mismatches; check_sorry PASS 140; check_records PASS 140, 108 files; the drift check PASS; the
  banned scan PASS, 140 modules and the root file, 0 hits; module count 5729 (`ClassicalLean` 141);
  type dump 4088 records (3602 theorems, 486 definitions); gate 7 ALL PASSED in 24:02.49. The report
  tool: `SUMMARY written theorems 1990`; A 1186 with a hypothesis, 0 close; B 804, 16 close; C 37, 0
  recursive; self-test mismatches 0.
- **The heartbeat lines.** `tools/UninformativeReport.lean` line 360: `set_option maxHeartbeats 0 in`
  (line 359: "The budget of each theorem is set inside `judge`; this outer one only bounds the
  command."). Its per-theorem budget is `libraryBudget`, `200000` (line 137); its docstring (lines 42
  to 44) says that budget "is not to be changed without asking Dustin (order LEAN-16's known trap)".
  `tools/VacuityGate.lean` line 838: `set_option maxHeartbeats 2000000 in`. Each file has one `set_option
  maxHeartbeats` line.
- **The two scanners' scope.** `tools/check_sorry.py` line 73: `SKIP_DIRS = {".lake", ".git",
  "__pycache__", "node_modules", ".venv", "tools"}`. `tools/banned_vocab_scan.py` (lines 29 to 30, 94,
  103 to 104): `ClassicalLean/` and the root file `ClassicalLean.lean` beside it, default root
  `ClassicalLean`. The Rules gate (CI's step: `compile_rules.py check records/rules.toml --base …` and
  `compile_rules.py drift records/rules.toml HANDOFF.md`) opens only the registry, its base copy and
  `HANDOFF.md` (its four `open` calls, lines 90, 353, 385 and 477; no directory walk). So fixtures
  under `tools/` are outside all three.
- **The lines the gate reads.** 140 modules under `ClassicalLean/`, 50849 lines. 107 of them (42589
  lines) have a line matching the `UNREAD` pattern; 369 such lines, all at column 0: 151 witness form,
  168 typed, 50 binder. None is indented, attributed, `private` or `noncomputable`, and no comment or
  docstring line matches the pattern, so `NOT-A-BLOCK` is 0 at the master. 70 modules have a
  witness-form block (28513 lines); the largest are Statistics/Sufficiency (1407 lines) and
  Probability/GamblersRuin (1191).
- **The same, as Lean reads it** (`claim_scan5.py`, after review pass 2; `claim-scan-5.out`, sha256
  `49007ab53eee49315310f524850c10b0a0647cca409be9e12666d40f0678247f`, byte for byte equal to
  `claim_scan3.py`'s output after review pass 1): comments (nested), strings, char literals and raw
  strings masked; every `example` keyword outside them is a block wherever it stands; a docstring is
  the `/--` comment that Lean attaches, found as Goal item 1 says (across blank lines, `--` and plain
  `/- … -/` comments, attributes, modifiers and `open … in` and `set_option … in` prefixes; never past
  a `/-!` comment or code). Version 4 (`claim_scan4.py`, superseded) gave 8 false DOC-DIFF lines
  (Algebra/CompanionMatrix 294; NumberTheory/NacciTrace 252 to 271): it took a `]` that ends a block
  (`simp […]`) for the end of an attribute and jumped to the nearest `@[` above; version 5 matches the
  bracket (Goal item 2 has a fixture for it). Blocks 369, all at column 0 (no `open … in example` on one line, no docstring and
  `example` on one line); no comment or string line matches the `UNREAD` pattern; every docstring
  equals the line rule's; the witness-form blocks without a witness docstring are MinMax 443 and
  PrimitiveDivisor 423; claims 13, the same 13. So rule 3's predicted counts hold under both readings.
- **Names in scope after each module's last line** (`name_scope.py`'s Lean file, importing
  `ClassicalLean`; `name-scope.out`, sha256
  `1531c43fc396608a6cc3f88cf3b70cca6ff8a341a8c043727e933bb2e6ece255`): for the 24 theorems this order
  witnesses (17 of the 18 that the twelve claims name, all but LongestRun's `measureReal_no_run_le`,
  which has a witness; Superadditive's five; MaximalInequality's two frozen ones), each short name
  finds exactly one theorem in its module's namespaces, and only Superadditive's `map_zero` also
  reaches another constant from the root (Mathlib's `map_zero`); the other 23 reach nothing else
  through the root or the modules' top-level `open` lines. The dotted `Superadditive.map_zero`
  (`DottedName.lean`, `dotted-name.out`, sha256
  `4b670b1dc9587c59867564aff745ad5038dc62f8beb4b19a6de664e705c0474b`): no root `Superadditive` and no
  root `Superadditive.map_zero`; `ClassicalLean.Superadditive.map_zero` present and
  `ClassicalLean.Superadditive.Superadditive.map_zero` absent, so exactly one `N.NAME`.
- **One copy, timed.** Each of those two modules, copied byte for byte to `/tmp/claude-ai-gate1/time/`
  and elaborated: Sufficiency rc 0, 6.36 s wall, 3.39 GB peak; GamblersRuin rc 0, 4.07 s, 3.43 GB; no
  warning or error lines. Plain copies: no turned blocks, no checks. claude-ai's estimate for the
  gate on the whole library, one process at a time: 107 modules at 4 to 7 s each, about 7 to 13
  minutes on DSMain (`nproc` 16; `free -g` 62 GB total, 54 available). An estimate by line count
  only (elaboration time does not follow line count); Goal item 6 measures.
- **The modules this order changes, or lists:**

  | module | lines | sha256 | blocks read at the cut |
  |---|---|---|---|
  | Algebra/Kantorovich | 338 | `fa37d293787e72eb9637c65c206f96d2da71fccd1dbcc5fcfe9994e0fd9ec666` | `namespace` 87 to `end` 321; typed claims 216, 225; witness form 328 (another theorem) |
  | Algebra/MinMax | 470 | `c855ff6557b9b83bc352efcf717a102ddaffd3716c6697395b248caa940ad733` | `namespace ClassicalLean.MinMax` 107 to `end` 446; typed claims 427, 434; witness form 443 (no docstring), 453, 466 |
  | Analysis/ConvexConjugate | 206 | `328a2e81c265268356691d0c5e4bd4aa5d517b8a98e6572a563ed7d7b32e11eb` | namespace 73 to `end` 161; `convexConjugate_anti` 99; typed claim 126; typed 165 to 199 (7); witness form 203 |
  | Geometry/Spectral3x3 | 181 | `f4b74e15217a84767ac51d5ab502a573e80e8d7d65f00a1ac319c8452543b00d` | namespace 68 to `end` 181 (the last line); `gap_identity_of_offDiagCross_eq_zero` 145; typed 166, 169, 171, 178; typed claim 175; no witness-form block |
  | InformationTheory/CompressionTest | 530 | `fd343671229da7ed722ad1ec94d6632562b871ebd19980bb93f254c4c12132f1` | `namespace` 171 to `end` 476; typed claim 462; witness form 484, 500, 512, 524 (other theorems) |
  | Order/Superadditive | 122 | `3da8e5a50e2feec1f35fdda087b21e077e200a3fc481ea9eafc84b53e3a4249d` | five theorems (73, 81, 90, 100, 108) in `namespace Superadditive`, each taking the section's `hf : Superadditive f` (`include hf`); `unbounded` (100) and `pos_of_pos` (108) also take `0 < f 1`, and `pos_of_pos` `0 < n`; `end Superadditive` 112; typed claim 116; binder 120 (not a claim); `end ClassicalLean` 122 |
  | Probability/EffectiveSampleSize | 767 | `eb0343bd16a24cadbf2ab25fb713cd01435c363824d8700b4d430ba8b45c9529` | `namespace` 143 to `end` 662; typed claims 583, 595; typed 610; witness form 670, 706, 739 (other theorems; selected for the sweep) |
  | Probability/GamblersRuin | 1191 | `2f8f365e64714f71172704e4124bf8b440d5c53ff70e02de1b3298ffa6e1a5f4` | `namespace` 178 to `end` 1133; typed claim 1046; typed 1084; witness form 1141, 1169 (other theorems; selected) |
  | Probability/LongestRun | 598 | `d68a51c9ba64d99aaad21a4902d9cf651831230dd041bac90618536c31e3cf3e` | typed claim 268; typed 289, 330, 357 (why each hypothesis is kept: not claims); `namespace` 109 to `end` 375; witness form 383, 457, 532 (selected) |
  | Probability/MaximalInequality | 814 | `e461ec42f84fb4806d7ecf150313a620475392315877f404d272db05d96b397a` | `namespace` 112 to `end` 688; witness form 697, 736 (frozen), 779 (all three selected) |
  | Statistics/GeneralizedLeastSquares | 300 | `fdcaba282eb339fbc95f95213fe06f4bfa1e0ed33427d784f2a35813f377cae9` | `namespace ClassicalLean.Statistics` 107 to `end` 265; `glsMatrix_ones_eq_minWeights` 222; typed claim 261; witness form 273, 285 |
  | NumberTheory/PrimitiveDivisor (listed, not changed) | 423 | `93a70cec9325f45f4b6f526b5d78c2c30f347da27ed0ac4794be2ee7168e6b17` | `namespace ClassicalLean` 176 to `end` 407; binder 363 (under `/-! ### The real-work test`, line 329) and 401 (under `/-! ### Cross-item: the Mersenne slice`); binder 412; witness form 423 (no docstring) |

- **The sweep selection** (Job 3; `census_examples2.py`, then the Lean file `sweep_select4.py` writes,
  which imports `ClassicalLean`; rc 0, 3.83 s, 4.07 GB): every target constant present
  (`MeasureTheory.Filtration`, `Martingale`, `Submartingale`, `Supermartingale`, `IsStoppingTime`,
  `stoppedValue`, `stoppedProcess`, `hittingBtwn`, `hittingAfter`, `Nat.iterate`); 149 witness-form
  blocks with a docstring NAME; MISSING 0, AMBIGUOUS 0; SELECT 46, SKIP 103 (`sweep-select-4.out`).
  The 46, by module and the theorem each witness names (its line at the cut in brackets; Job 2's
  removals above a block move its line, so the theorem is the key):
  Analysis/EulerMethod `tendsto_implicitEuler` (248), `tendsto_explicitEuler_iff` (254);
  Analysis/ExponentialWeights `sum_inner_softmax_le` (254); Analysis/FrankWolfe `sub_le_of_frankWolfe`
  (180), `fw_general` (255); Analysis/GradientDescent `sub_le_of_gradientStep` (566),
  `dist_gradientStep_le` (580), `sub_le_pow_mul_of_polyakLojasiewicz` (618),
  `sub_le_of_projGradientStep` (630); Analysis/PowerMethod `tendsto_powerIterate` (206);
  Analysis/RoundingError `abs_dotComputed_sub_le` (284), `abs_hornerComputed_sub_le` (291);
  Analysis/SubgradientMethod `min_sub_le_of_subgradient` (103); InformationTheory/ChannelCapacity
  `tendsto_capacity_bsc_pow` (291); InformationTheory/MethodOfTypes
  `tendsto_neg_log_div_shannonEntropy` (611); Probability/EffectiveSampleSize
  `variance_average_le_of_steady'` (670), `variance_average_eq_of_steady` (706),
  `variance_average_le_of_steady` (739); Probability/Extinction `tendsto_iterate_zero` (313);
  Probability/FairGame `integral_stoppedValue_sum_eq` (233), `integral_stoppedValue_sq_eq` (274);
  Probability/GamblersRuin `measureReal_hit_eq` (1141), `measureReal_hit_eq_lucasU` (1169);
  Probability/GlivenkoCantelli `eventually_lt_sup_abs_empiricalCDF_sub` (413),
  `eventually_lt_sup_abs_empiricalCDF_sub_of_tendsto` (431), `tendsto_sup_abs_empiricalCDF_sub` (459);
  Probability/InspectionParadox `sum_sq_div_sum_ge_mean` (213); Probability/KalmanVariance
  `tendsto_riccatiStep` (291); Probability/LikelihoodScore `measureReal_sum_ge_le_exp_neg_relEntropy`
  (409), `measureReal_sum_ge_le_exp_neg_sq` (496), `measureReal_sum_ge_le_exp_neg_relEntropy'` (582);
  Probability/LongestRun `measureReal_exists_run_le` (383), `measureReal_no_run_le` (457),
  `measureReal_no_run_le_exp` (532); Probability/MaximalInequality `measureReal_exists_abs_ge_le`
  (697), `integral_sup_sq_le` (736), `measureReal_exists_mul_abs_ge_le` (779); Probability/MovingAverage
  `covariance_movingAverage` (412), `sum_covariance_mul_cexp_eq` (531),
  `zero_le_sum_covariance_mul_cos` (650), `variance_sum_movingAverage` (769); Probability/PolyaUrn
  `martingale_urnShare` (238), `ae_tendsto_urnShare` (315), `ae_mem_Icc_of_tendsto_urnShare` (386);
  Probability/YuleWalker `durbinLevinson_spec` (313); Statistics/AdaptiveCoverage
  `abs_mean_err_sub_le` (150). The script took three tries, each run read and the next written before it ran: version 2's
  Lean file did not elaborate (rc 1: its counter's `0` was read as `MessageData`); version 3 selected
  42 but printed `TARGET MeasureTheory.hitting ABSENT` (this Mathlib has `hittingBtwn` and
  `hittingAfter`) and skipped KalmanVariance's `tendsto_riccatiStep`, a limit of an iterated map;
  version 4 has the two hitting names, `Nat.iterate` and the limit along `ℕ`, and selects version 3's
  42 and four more (EulerMethod 254, PowerMethod 206, ChannelCapacity 291, KalmanVariance 291). A
  binder counts only when it is not a proof (a hypothesis `∀ n, …` does not).
- **LEAN-35's rows, for the push** (the last 200 bytes of each file). INDEX's last row (LEAN-35's) ends
  "`8421cef` (bridge baseline) and the records commit |". CLAIMS's last row (LEAN-35's) ends
  "**closed** 2026-10-25 — branch `lean-35` landed (items 114, 115, 125, 138 and 148), G `d21fd22`,
  every gate as predicted; not pushed, the push is Dustin's after claude-ai's push review |". Records:
  51 entries in `records/orders/`, 57 in `records/rounds/` (the last
  `20261025T101100Z__round-72-kalman-moving-average-hajek-renyi-wald-hitting-times.md`), INDEX 73
  lines, CLAIMS 65 lines.
- **LEAN-35's helpers** (`~/lean/lean35-checks/`): 28 files in `scripts/` (the 27 that LEAN-35 used,
  and `mkwitcheck.py`). `lean35-checks` is on one line each of `commit.sh`, `docs-insert.py`, `el.sh`,
  `ev.sh`, `hl.sh`, `mkcensus.sh`, `probecheck.py`, `records2.py` and `rootrun.sh`, and on two lines
  of `evcite.py`; `probecheck.py` line 29 is `BASE = 'f5411f4'`; `commit.sh` line 16 holds the two
  trailers (LEAN-35's session). `inputs/TypeDumpPI.lean` and `inputs/g8_typediff.py` equal the lane's
  two type-dump files. The time windows: `el.sh` refuses Lean from 01:45 to 05:45 local time; `ev.sh
  --cap` also from 01:15 to 01:45 and from 23:45 to 00:00; `rootrun.sh` from 01:15 to 05:45 and from
  23:45.
- **Gate 7 at the cut:** `run-recheck.sh`'s sha256 as above; `run-d21fd22/leanchecker.txt`: `SUMMARY
  modules=140 failed=0`.

**Files and their sha256 at the cut.** Lane files, under `/opt/datasphere/lane/inbox/threads/staging/`
(read with `ds_hash` while the cut ran, and again with `sha256sum` on DSMain once this order was
assembled: `order-hash-check-r5.txt`, all `OK`):

| file | sha256 |
|---|---|
| `lean/LEAN-34/data/mkwitcheck.py` | `fac60ab63a4708b36ef58f6274e8bea2aa79f8afbb0ed27e0324a3208669507a` |
| `lean/LEAN-34/report-r2.md` | `90f1bd8b3c78a8e86b0ee6172cc33b8cb3e76a40826e592e6de9178cdf6f76e8` |
| `lean/LEAN-35/order.md` | `037d2022b2669ba034100932761a1f3ed09d77aa39e6f89a0ec0a4c3520a54cc` |
| `lean/LEAN-35/report.md` | `6c56b5353f9df4559c2cfcc2f9dae0efddcd2a92f528da0186a4516110e0fcbb` |
| `lean/VACUITY-3-ruling-3.md` | `aa0d17e403031b81d0e0803c3308002ed985b416d788980de0f61cc79e13a4f2` |
| `lean/MERGE-2-order.md` | `81894b5bc85a6ee6858f7a1d8b065ee17ff5034f21df9ef68803cded13e4251a` |
| `lean/NOTE-20261015-task-list-rule.md` | `76cfb510d0023c0c8cb2e843877417c387fe05b92f9ef5dfbe24dc18457194ef` |
| `lean/LEAN-33/scripts/TypeDumpPI.lean` | `1fcb69f41ddbd35f84862521d2ead5946a0bd52caf5f60b6d10e966cfd9776ff` |
| `lean/LEAN-33/scripts/g8-typediff.py` | `371eda9a2e5065abaa8f36bac9872d0f15e7bade72a248d5f0f88f20b4eacb71` |
| `server/RESEARCH-ACTIONS-1/plan.md` | `1052940d41d685f4c66a4e9b30b30571f8e57f9fef6518a122619e18e230f9d5` |

DSMain: `/tmp/claude-ai-gate1/cut-manifest-r5.txt`, sha256
`1fe2650c3bd9c85ff99fbd4a87e8d9d49808ad088bc1038f172a5e4ee4998668`, 99 lines of `sha256sum` output with
absolute paths (the cut's first manifest, `cut-manifest.txt`, 83 lines,
`ba3ebc65ea02cca47632a429878dd98e489be4e0b7e18370751a96434f2d9ccd`, then the eight files of review
pass 1's checks, then the eight of review pass 2's): the twelve modules above, `ClassicalLean.lean`, the gates' files in `tools/`
(`AxiomGate.lean`, `VacuityGate.lean`, `VacuityGateTests.lean`, `UninformativeReport.lean`,
`run_vacuity_tests.py`, `vacuity_reviewed.txt`, `check_sorry.py`, `check_records.py`,
`banned_vocab_scan.py`), `.github/workflows/ci.yml`, `lakefile.toml`, `lake-manifest.json`,
`lean-toolchain`, `records/rules.toml`, `HANDOFF.md`, `records/README.md`, `~/lean/recheck/run-recheck.sh`,
LEAN-35's 28 scripts, its two census tails, `allowlist.txt` and its two inputs, and the cut's scripts
and outputs (`census.out`, `census2.out`, `claims.out`, `claim-scan-2.out`, `SweepSelect4.lean`,
`sweep-select-4.out`, `cut-facts-1.out` to `cut-facts-3.out`, `draft-facts.txt`, the two timing
outputs; then `claim_phrases.py`, `claim_scan3.py`, `name_scope.py`, `cut_facts4.sh`,
`claim-scan-3.out`, `NameScope.lean`, `name-scope.out`, `cut-facts-4.out`; then `claim_scan4.py`,
`claim_scan5.py`, `DottedName.lean`, `cut_facts5.sh`, `claim-scan-4.out`, `claim-scan-5.out`,
`dotted-name.out`, `cut-facts-5.out`). `sha256sum -c` on it when it was written: all `OK`.

## Goal

1. **The witness gate.** A new gate, `tools/witness_gate.py`, run as `python3 -I
   tools/witness_gate.py [--root DIR] [MODULE …]` (no module: every module under `ClassicalLean/`; a
   root other than the repository's: for its fixtures and planted faults). It reads each module **in
   place**: a scratch copy of the module's own text, outside the repository, with each `example :=`
   block turned into a named definition where it stands (inside its namespace, beside its module's
   private lemmas, under its `open … in` lines), elaborated with `lake env lean` from the repository
   root with the build's own options (the lakefile's `[leanOptions]`, read from the lakefile, not typed
   by hand), one Lean process at a time. Each turned block is checked right after its definition, in
   its own scope. Its verdicts, one per line of output:
   - for a block that starts `example :=` at column 0 and has a witness docstring ("The hypotheses of
     `NAME` hold together"):
     - `BROKEN`: the block raised an error, or the axioms of its definition, collected through every
       constant it uses (`Lean.collectAxioms`), are not a subset of `propext`, `Classical.choice`,
       `Quot.sound` (so a `sorryAx` anywhere below it, or `native_decide`'s axiom, is caught);
     - `WRONG-NAME`: the head constant `c` of the block's value is not the constant NAME names. If NAME
       resolves in the block's own scope (its namespaces and `open`s), `c` must be that constant. If it
       does not (the library's usual case: the docstring gives the short name and the block sits after
       the module's last `end`), `c` must be `N.NAME` for a namespace `N` that the module itself opens
       with a `namespace` line (nested namespaces joined), and exactly one such constant may exist;
     - `PARTIAL`: the definition's type, opened with `forallTelescopeReducing` at reducible
       transparency, has a binder anywhere in that telescope whose type is a proposition (instance and
       implicit binders included);
     - `OK`: none of these;
   - `NO-DOCSTRING`: a block that starts `example :=` at column 0 without a witness docstring;
   - `TYPED-CLAIM`: a typed or binder example whose docstring has one of the four phrases
     "hypotheses of", "hypothesis of", "can be met", "hold together" (case ignored, and matched after
     the docstring's runs of whitespace are collapsed to one space, so a phrase broken across lines
     counts; the cut's list, "What is already true");
   - `TYPED`: any other typed or binder example at column 0 (Lean has checked it against its stated
     type; not a witness; passes);
   - `NOT-A-BLOCK`: a line inside a comment, docstring or string that matches the `UNREAD` pattern
     below, leading spaces allowed (Lean's block comments nest; passes);
   - `UNREAD`: a line matching `^\s*(@\[.*\]\s*)?(private |noncomputable )*example\b` that is not one
     of the forms above (an indented, attributed, `private` or `noncomputable` example), and any
     `example` keyword outside comments and strings that does not start its line (`open … in example`
     on one line, or a docstring and `example` on one line); fails. Comments and strings are found as
     Lean's lexer finds them: block comments nest; `--` runs to the end of the line; char literals
     (`'"'`, `'\''`) and raw strings (`r"…"`, `r#"…"#`) are strings;
   - `LISTED`: a block with a matching entry in `tools/witness_reviewed.txt`; passes. An entry holds the
     module, the sha256 of the block's whole source (from its first `open … in` line or docstring line
     through the end of the command as Lean parses it), the verdict the block would otherwise get, and a
     one-line reason; one entry per block. Only `NO-DOCSTRING` and `PARTIAL` may be listed as blind spots
     of the check; a known fault may be listed only as Goal items 3 and 5 say, its reason starting
     `FAULT, later order:` (the verdict it would otherwise get may then be `OK`, for a frozen witness the
     gate cannot see), and is then printed `LISTED-FAULT` and counted apart; `BROKEN`, `UNREAD` and
     `COPY-ERROR` may never be listed. An entry whose hash matches no block, or whose block now gets a
     different verdict, fails (a stale listing);
   - `COPY-ERROR <module>`: the copy failed outside every turned block. The gate's Lean side reports
     every verdict with info lines and never raises an error, so a nonzero rc from `lake env lean`
     means the copy failed; an error whose position falls inside a turned block gives that block
     `BROKEN`, and `COPY-ERROR` is given only if errors also fall outside every block; fails.
   Every other verdict fails. The last line is one summary line, `WITNESSGATE PASS` or `WITNESSGATE
   FAIL`, with the counts by verdict (`LISTED-FAULT` apart), the number of modules read, and a
   cross-check: the number of lines it gave a verdict equals the number of lines matching the `UNREAD`
   pattern in the modules it read (under `--root`'s `ClassicalLean/` when given), plus the `UNREAD`
   keywords that do not start their line; and the number of `example` keywords outside comments and
   strings equals the number of verdicts other than `NOT-A-BLOCK`; `COPY-ERROR` and stale-listing
   lines are counted apart and are not in either. `--root DIR`: the gate reads
   `DIR/ClassicalLean/**` (or the named modules under it); Lean still runs from the repository root
   with the repository lakefile's options. The options are the package's `leanOptions`, from whichever
   lakefile the repository has (`lakefile.toml` at `ac62f50`); the plan says how the turned blocks
   avoid linter warnings the original `example`s did not raise (for example, the docstring kept on the
   turned definition). A block's docstring is the comment that Lean attaches to it: going back from
   the `example` keyword over whitespace (blank lines included), over `--` comments and plain
   `/- … -/` comments (Lean reads both as whitespace), over the modifiers `private`, `protected`,
   `noncomputable`, `unsafe`, `partial` and `nonrec`, over an attribute only when its `]` closes a
   bracket opened by `@[` (matched, outside comments and strings), and over whole `open … in` and
   `set_option … in` prefixes, the text just before must close a comment that opened with `/--` (read
   whole, nested comments included). A `/-!` comment or code there means no docstring, and the gate
   does not look past it (claude-ai's first scan did, "What is already true").
2. **Its tests** (`tools/witness_gate_tests.py` and fixture files under `tools/witness-fixtures/`,
   outside `ClassicalLean/` so they are not built or gated), each case with its expected verdict and
   a runner that reports MISMATCH: `OK`; `PARTIAL` (one hypothesis left out at the end); `PARTIAL` (cut
   short before a data argument that a later hypothesis depends on); `BROKEN` (one wrong hypothesis
   proof); `BROKEN` (a theorem of the module whose own proof fails in the copy, its witness otherwise
   well formed: `COPY-ERROR` too); `BROKEN` (a witness resting on a `native_decide` lemma); `WRONG-NAME`
   (including a theorem of the same last name in another namespace); `OK` for a witness after its
   module's namespace block whose docstring gives the short name and whose value gives the full name
   (the library's usual form); `OK` for a witness inside a namespace that names its theorem without the
   prefix; `OK` for a witness that uses a private lemma;
   `OK` for a witness under two `open … in` lines; `OK` for a witness whose docstring holds a nested
   comment; `NO-DOCSTRING`; `NO-DOCSTRING` for a witness-form block directly under a `/-! … -/`
   section comment, when a declaration above that comment has a docstring of the witness form;
   `TYPED-CLAIM` (one case for the singular "hypothesis of", one for a claim docstring followed by a
   blank line before its example, one for a phrase broken across two lines, one for a claim
   docstring followed by a `--` comment line before its example); `TYPED`; `TYPED` for a typed
   example that follows a block whose last token is `]` (`simp […]`; claude-ai's fourth scan took that
   `]` for an attribute's); `OK` for a witness that follows a `def` holding the char literal `'"'`;
   `UNREAD` for `open … in example` on one line, and for a docstring and witness on one line;
   `NOT-A-BLOCK`
   for a docstring line starting with the word `example`; `UNREAD` for an indented example; `LISTED` for
   a listed block; a stale listing (one character of the block changed) failing; a listing of a
   `BROKEN` block refused. Each failing case fails the gate run on its fixture (rc 1), each passing case
   passes (rc 0). `check_sorry.py` skips `tools/` and `banned_vocab_scan.py` is run on `ClassicalLean`
   (HANDOFF.md §4), and the Rules gate reads only the registry, its base copy and `HANDOFF.md` (the
   cut), so the fixtures' forbidden words (the `native_decide` case) are not seen by them; the plan
   confirms this by reading the three scripts, and the gate's docstring says so.
3. **The library passes it at G**, with these changes to modules, witnesses only (no declaration
   changes; the type dump checks it):
   - **The thirteen claiming typed examples:** for every theorem the table names that has no rule-2
     witness, a rule-2 witness written after its module's last line (HANDOFF.md §4's form, rule 3 with
     the case of Goal item 4); then the typed example is removed. LongestRun 268 is removed (its
     theorem has one). For Order/Superadditive 116, read its docstring and the module: name the
     theorems it means (the plan gives their number; claude-ai's reading at the cut: five, each with
     the hypothesis `hf`); each with a hypothesis gets a rule-2 witness, and the typed example is
     removed or, if it is something else than a witness, its docstring is reworded in place to stop
     claiming one (say which in the plan). The witness of `ClassicalLean.Superadditive.map_zero` gives
     `Superadditive.map_zero` (or the full name) in its docstring: the short `map_zero` resolves after
     the module's last line to Mathlib's root `map_zero` (the cut, "Names in scope"), which would give
     `WRONG-NAME`; the dotted name reaches exactly one `N.NAME` and nothing from the root (the cut).
     For every new witness, the plan checks, as `name_scope.py` did, that after the module's last line
     its docstring NAME reaches no constant through the root or a top-level `open` other than the
     theorem (a `#check @NAME` placed there gives "unknown identifier", the usual case, or names the
     theorem itself), and that exactly one `N.NAME` exists for the namespaces the module opens (rule
     37's probes).
   - **Values the old examples used** may be degenerate under rule 3: Spectral3x3's diagonal matrix
     makes `offDiagCross = 0` hold trivially; GeneralizedLeastSquares' `V = 1` is the case where the
     generalized estimator is the ordinary one; Superadditive's identity holds with equality
     throughout. The plan's first values avoid these, and review (b) judges.
   - **Algebra/MinMax line 443:** moved after the module's last line, outside the namespace, with the
     full name and the witness docstring; it is then `sum_eigenvalues_eq_iSup`'s rule-2 witness, so no
     second witness of that theorem is written. Its values (the identity on `ℝ²`, `k = 1`, every
     eigenvalue equal) may be found degenerate by review (b); then it is rewritten with values that
     are not.
   - **NumberTheory/PrimitiveDivisor line 423:** listed in `tools/witness_reviewed.txt` as a
     name-resolution check (verdict `NO-DOCSTRING`, reason said), not changed.
   - **Other faults the gate's first library run finds** (Job 1): up to 6 are fixed by a rule-2 rewrite
     in this order (the old block removed, the new one after the module's last line); any more get an
     entry whose reason starts `FAULT, later order:` (`LISTED-FAULT`), each listed in the report with its
     evidence. A false verdict where the check is blind (a theorem whose conclusion itself opens with a
     hypothesis binder gives a false `PARTIAL`) is listed with its reason; the gate's docstring names
     the other known limit (a hypothesis behind a definition that reducible unfolding does not open
     passes as `OK`).
4. **Rule 3 gains a case, and the frozen witnesses are fixed.** HANDOFF.md §4's "Satisfiability
   witnesses" gets this dated paragraph, word for word:
   "**Dated <date> UTC (order VACUITY-4): rule 3's case of the moving process.** A witness of a
   theorem about a process `X` up to a time `n` (the process the conclusion is about; for a stopped
   process, the underlying process and the stopping time together) makes `X` move at every step before
   `n`: for each `k < n`, `X (k + 1) ≠ X k` with positive probability, or, for a deterministic
   sequence, `X (k + 1) ≠ X k`; and `n ≥ 1` (at least one step). For a stopped process, `τ ≥ n` has
   positive probability. Where the theorem's hypotheses force `X` to stop or to pause (an absorbing
   state, a bounded stopping time, a sequence they make constant from some point), the witness stops or
   pauses it no earlier than they force, and its docstring says so. For a theorem with no horizon (a
   limit, or a statement for every `n`), a witness whose process is constant from some time on is
   degenerate unless the hypotheses force it."
   (`<date>` is the UTC date of Job 5's documents commit.) MaximalInequality's two frozen witnesses (lines 697 and 736) are re-witnessed under it (the old
   blocks removed, the new ones after the module's last line). Line 779 (LEAN-35's item 125, `n = 1`,
   its one step moving with positive probability) meets the case and is not changed.
5. **The process sweep.** Fresh reviewers, at most 15 witnesses each, read against Goal item 4's case
   and rule 3 every witness of a theorem that Job 3's Lean census selects (at the cut: 46 of 149,
   listed by theorem under "Measured at the cut"; those not rewritten in Job 2 are read, 44 at the cut
   without MaximalInequality's two, so three reviewers). A witness they find frozen is
   re-witnessed in this order, up to six beyond MaximalInequality's two; any more get a `LISTED-FAULT`
   entry and go to the report's list for a later order, each with the reviewer's evidence.
6. **The gate in CI and in the session gates.** The witness gate and its tests run as job 5a's gates
   in this order and in every later order (HANDOFF.md §4 says so). It is added to
   `.github/workflows/ci.yml` as one step after the vacuity gate, with the same `if:` condition, when
   its wall time for the whole library, one Lean process at a time on DSMain under the 12 GB cap,
   measured at HEAD after Job 4's two leftover commits (they change no module, so the library's text
   then equals the last commit of Jobs 2 and 3; the clean tree checked first), is at most 20 minutes;
   otherwise it is not added, and HANDOFF.md §4 and the report say why, with the measured time. The
   added step carries its own `timeout-minutes: 45`, so a slow runner fails that step without hiding
   the other gates, which have already run. The report gives DSMain's core count and says that the
   time on GitHub's runner is not measured until the first CI run after Dustin's push (a CI run is 12
   to 21 minutes today, against the job's 90-minute limit). The cut's estimate, not a measurement:
   about 7 to 13 minutes on DSMain ("Measured at the cut", "One copy, timed"). Job 6's 5a measures the gate's time again at G, predicted at most the
   first measurement plus 10%; a miss is reported, not fixed. Gate 7 (`run-recheck.sh`) is not changed.
7. **The two leftovers.** (a) `tools/UninformativeReport.lean`'s whole-library command gets a finite
   outer budget, `set_option maxHeartbeats 2000000 in` as `tools/VacuityGate.lean` has; if the report
   then fails on its budget, the smallest of `4000000`, `8000000`, `16000000` with which it runs is
   used and the report says so; if `16000000` also fails, stop. Its summary lines must equal Setup 5's
   run at the records commit. The per-theorem budget, `libraryBudget` (`200000`, line 137, which the
   tool's docstring says "is not to be changed without asking Dustin"), is not changed. (b) The vacuity gate's FAIL text names case 5 (a conclusion glued from
   hypotheses) and says in one sentence each what UNCHECKED and KERNEL-REJECTED mean; strings and
   comments only, no verdict changes: the vacuity tests give the same 89 verdicts (47 flagged, 3
   UNCHECKED as expected, 0 mismatches) before and after, and the gate's code with comments and the
   literal parts of strings removed (the `{…}` holes of `s!` and `m!` strings kept as code) is equal
   before and after, checked by a script with two controls on scratch copies: a one-token code change is
   detected; a change inside a string only is not.
8. **Research actions step 4, recorded.** HANDOFF.md §4 gets a dated paragraph: the re-check outside
   the build is gate 7 since order RECHECK-1 (leanchecker per module, then nanoda on a `lean4export`
   export, with a planted fault), measured at `d21fd22`; `lake comparator` and `lake check` exist from
   Lean v4.35.0 on (the standalone Comparator, now superseded, needs a newer toolchain at its latest
   commit), not at v4.34.0. So they wait for the order that moves the toolchain to v4.35.0 or later,
   which then decides how comparator checks AI-drafted statements against their approved statements
   (the plan's purpose), and whether `lake check --paranoid`, with the toolchain's bundled nanoda and
   `--from-export`, replaces gate 7's hand-built steps. No code for this item.

## Scope

- **Branch.** `vacuity-4` from `ac62f50` in `~/lean/classical-lean-paper-crypto`, made after
  Dustin approves your plan. Nothing pushed. No sudo.
- **You may add:** `tools/witness_gate.py`, `tools/witness_gate_tests.py`, `tools/witness-fixtures/`
  (Lean fixture files and the tests' expected verdicts), `tools/witness_reviewed.txt`.
- **You may change:** `tools/VacuityGate.lean` (strings and comments of the FAIL text only, Goal item
  7b); `tools/UninformativeReport.lean` (its one `set_option maxHeartbeats` line, Goal item 7a);
  `.github/workflows/ci.yml` (one step, Goal item 6); in the modules Goal items 3 to 5 name or that
  Job 1's first library run or Job 3's sweep adds, only `example` blocks, their docstrings and their
  `open … in` lines: added after the module's last line; moved there (MinMax 443); removed (the typed
  claims, and an old witness-form block that Goal item 3, 4 or 5 replaces with a new block after the
  last line); or, for a typed example that stays (rule 2's NOT WITNESSED, Superadditive), its docstring
  reworded in place; `HANDOFF.md` §1 and §4 (dated paragraphs; the CI paragraph's sha256 and steps; the
  gate count "Five gates"); `records/`.
- **You may not change:** any declaration (the type dump checks it: `removed=0 added=0 changed=0
  proof_only=0`), any import line, `ClassicalLean.lean`, any other file under `tools/`,
  `records/rules.toml`, the lake files, `lean-toolchain`, `HANDOFF.md` §0, §2, §3, §5 and §6 (§6's
  drift check), `ROADMAP.md`, `~/lean/recheck/` (gate 7 is run, not edited). Needing to is a stop:
  report it.
- **You may write in the lane:** the plan, the report and the push-review file through `ds_file`.
  Nothing else.
- **Off limits:** the main clone `~/lean/classical-lean` and its `master`; `~/break-it-5`; `~/trading`;
  every earlier order's folder under `~/lean/` (read only; `~/lean/lean35-checks/` is the source of
  your helpers); Dustin's `~/.config/classical-lean/banned-terms` (the scanner reads it; never print or
  copy it); every GitHub branch (no push, no delete); `/data/api-credit/` and `~/api-credit/` (not
  used); `/tmp/claude-ai-gate1/` (the cut's outputs, read only); every other `/tmp/claude-ai-*/` (not
  used).
- **The night window and the memory cap,** as `ev.sh` enforces them (name the window; do not copy its
  times; HANDOFF rule 36). Before each whole-library run, log `pgrep -ax lean` through `ev.sh
  --nolean` (rc 1 when none runs); never two Lean runs at once (the witness gate runs one Lean process
  at a time, and a whole-library run of it counts as one Lean run); reviewers run no Lean while you do;
  claude-ai starts no Lean run on DSMain while this session runs, unless Dustin says so. Start gate 7
  only when it can finish before the midnight timer (LEAN-35's run: 24:02.49, its report's table).

## Check, then read

Check these sha256s first; if any differs, stop and say which: this order (the value in Dustin's
prompt); the lane files in the table "Files and their sha256 at the cut" (`sha256sum` on
`/opt/datasphere/lane/inbox/threads/staging/...`, or `ds_hash`); `/tmp/claude-ai-gate1/cut-manifest-r5.txt`
(its sha256 just below that table), then every file it lists with `sha256sum -c
/tmp/claude-ai-gate1/cut-manifest-r5.txt` (99 lines, predicted all `OK`). If
`/tmp/claude-ai-gate1/` or a file it lists is missing, stop there and say so: claude-ai then measures
again, read-only, from Appendix A's scripts, which gives new outputs (the dated ones cannot be rebuilt
byte for byte), a new manifest and a revised order.

Then read: in the repository `records/README.md`, `HANDOFF.md` §1's last three dated paragraphs, §4 in
full and §6 (all rules), `tools/VacuityGate.lean`'s FAIL text and the docstring of `isVacuousType`,
`tools/run_vacuity_tests.py`, `tools/UninformativeReport.lean`'s whole-library command, the CI
workflow, the lakefile, every module this order changes in full, and the last round's fragment; in the
lane `lean/LEAN-34/data/mkwitcheck.py` (the pattern for the gate's Lean side), LEAN-34's report-r2
("The witness check"), LEAN-35's order (its rules, Setup, jobs 3 and 5, and Done means, which this
order follows) and report, `lean/MERGE-2-order.md`'s job 4a (the forms of the end gates),
`lean/VACUITY-3-ruling-3.md`, and `server/RESEARCH-ACTIONS-1/plan.md` lines 60 to 70.

## Rules of this order

1. **No declaration changes.** The type dump at the records commit and at G (HANDOFF rule 14,
   through `rootrun.sh`), read by its `DIFF` line: predicted `removed=0 added=0 changed=0
   proof_only=0`. An `example` adds no constant. Any other line is a stop.
2. **Witnesses** in HANDOFF.md §4's form (rule 2: `example := Full.name (x := …) h₁ h₂ …`, every chosen
   argument by name, optional `open … in` lines of their own and no other `open` than the module's
   top-level ones, the docstring "The hypotheses of `name` hold together: …", none of the six
   forbidden words, one inline block, no helper declarations, after the module's last line); not
   degenerate (rule 3, with VACUITY-3's ruling 3 and Goal item 4's case). Log `date +%s` through
   `ev.sh` when you start each; one still missing 1800 seconds later is not closed. A theorem whose
   witness cannot be written under these rules is NOT WITNESSED: it is listed in round 73 and the
   report with the reason, as VACUITY-3 listed its five rows, and its typed example stays, its
   docstring reworded in place to stop claiming a witness (so the gate reads it as `TYPED`). Credit:
   each witness to whoever wrote it (this session, or a reviewer whose tested witness is taken, as
   LEAN-35 took review (c)'s).
3. **The gate is fail-tested before its first library run** (HANDOFF §4: "Each was fail-tested; if
   you change one, fail-test it again"): Goal item 2's tests all as expected, review (a) clean, then the
   gate's first library run at the records commit, with `tools/witness_reviewed.txt` empty, predicted
   from the cut's lists: rc 1; 13 `TYPED-CLAIM`; 2 `NO-DOCSTRING` (MinMax 443, PrimitiveDivisor 423);
   205 `TYPED` (the 168 typed and 50 binder lines, less the 13); 0 `NOT-A-BLOCK`, 0 `UNREAD`, no
   `COPY-ERROR`; the other 149 witness-form blocks `OK` unless the gate finds a fault (the
   faults are Goal item 3's work list); both cross-checks 369 (369 lines matching the pattern plus 0
   keywords not starting their line; 369 keywords against 369 verdicts less 0 `NOT-A-BLOCK`). That run is evidence, not one of the Job 1 commit's gates; it is made with the gate's
   files untracked in `tools/`, `git status --porcelain` showing only them (logged before and after);
   its non-OK verdicts are the work list of Goal item 3, and nothing else is changed to make the gate
   pass. A change to the gate
   after review (a) reruns Goal item 2's tests and gets a confirming pass on the change before Job 1's
   commit (one of rule 7's two rounds); review (a) not clean after two rounds is a stop, since Jobs 2 to
   6 rest on the gate.
4. **The vacuity gate's verdicts do not move** (Goal item 7b): same test verdicts; code equal
   outside comments and strings.
5. **Records.** As `records/README.md` says. The records-first commit: this order's copy, its INDEX
   row (`| VACUITY-4 |`) and CLAIMS row at the bottom, LEAN-35's push appended to LEAN-35's INDEX and
   CLAIMS rows in the form the earlier rows use ("; pushed by Dustin: DSMain's master ref written
   2026-10-25 09:08:03 EDT, GitHub master equal (`ac62f50`)": appended to the last cell of LEAN-35's
   CLAIMS row, and to the outcome cell of its INDEX row, the cell before the commits cell, as
   LEAN-34's rows have it; the time is the mtime of `/data/git/classical-lean.git/refs/heads/master`,
   which holds `ac62f505db03edda95e7f7fa83a301a07ddda924`, both read on DSMain on 2026-10-25 after
   the cut's review pass 1; the two rows' endings
   are quoted under "Measured at the cut"),
   and round 73's fragment naming the modules known at Setup 4 (the ten modules of the thirteen
   claims: Kantorovich, MinMax, ConvexConjugate, Spectral3x3, CompressionTest, Superadditive,
   EffectiveSampleSize, GamblersRuin, LongestRun, GeneralizedLeastSquares; and MaximalInequality;
   PrimitiveDivisor named apart, as listed and not changed) and the new `tools/` files. A module
   that Job 1's first library run or Job 3's sweep adds is named in round 73's follow-up edit, with the
   run or review that added it; so are the commit hashes.
6. **Predict, then measure; the tree that counts.** As LEAN-35's rule 7, with
   `~/lean/vacuity4-checks/` as the evidence folder. Every gate runs on the clean tree of the last
   commit that touches anything outside `records/` (G); later commits touch only `records/`.
7. **Reviews,** each by a fresh subagent that has not seen your work, with a brief built by script
   (HANDOFF rule 26), capped at 40 tool calls (at the cap it writes what it has and lists what it did
   not check; a fresh reviewer then takes those parts only): (a) the witness gate, its tests and its
   fixtures, before its first library run: does each verdict mean what Goal item 1 says, can a witness
   cut short, wrongly named or broken pass, can a listing hide a changed block, does the copy elaborate
   as the build does; (b) the witness rewrites, in groups of at most eight blocks (as VACUITY-3 grouped
   its rows), each against rule 2, rule 3 and Goal item 4's case, every chosen value checked; (c) the
   process sweep (Goal item 5), at most 15 witnesses per reviewer; (d) the two leftovers' diffs and
   their checks; (e) the documents commit's diff. A review with findings ends with a confirming pass on
   the fix only, by a fresh reviewer; at most two fix-and-confirm rounds; an item not clean after two is
   not closed and is undone by a new commit, said in round 73 and the report.
8. **Master does not move under you.** As LEAN-35's rule 10, at `ac62f50`.
9. **Nothing is added during the run.** As LEAN-35's rule 11: a finding outside the Goal is written
   down with its evidence for the report's list, not chased; a heads-up Dustin passes in is answered
   in your next message and listed in the report; claude-ai rules during the run only on a stop.
10. **A count is what its output says.** As LEAN-35's rule 12. A check that did not give a verdict
    on everything is stated as how many it confirmed and which it did not, each with why.
11. **Cold reviews are cold.** Before Setup 1, `printenv CLAUDE_CODE_DISABLE_AUTO_MEMORY` through a
    plain Bash call, predicted `1`. If it prints anything else, stop and say so (store rows
    20261025-036, -043: without it a fresh subagent loads Dustin's auto-memory index).

## HANDOFF's rules in this session

Every rule of `HANDOFF.md` §6 applies. How, for this order (`vacuity4-checks` wherever LEAN-35 says
`lean35-checks`):

| rule | here |
|---|---|
| 1, 2, 3, 10, 15, 18, 22, 28, 36, 39 | as written, and as LEAN-35's table says |
| 12 | Reviewers work in `~/lean/vacuity4-checks/reviews/<label>/`, outside the repository, with `PYTHONDONTWRITEBYTECODE=1`, copy any repository script before importing it; `git status --porcelain` unchanged after each review; the tree is not touched while a reviewer runs. |
| 14 | Rule 1 above. |
| 17 | As LEAN-35's table. |
| 19 | Rule 2's credit line above. |
| 20 | Scratch files and modules are elaborated by `el.sh` (the four flags). The witness gate's generated copies and its fixtures are elaborated by the gate itself, with the build's options read from the lakefile (Goal item 1), not by `el.sh`. |
| 23 | As LEAN-35's table: `ev.sh` and `hl.sh`, tested in Setup 2. |
| 26 | Every review brief is built by script from `HANDOFF.md`, saved with its sha256 before it is sent, and quotes verbatim rules 14, 17, 18, 19, 20, 22, 23, 26 and 31, cut only with `[...]`; briefs (b) and (c) also quote HANDOFF §4's "Satisfiability witnesses" paragraph verbatim and Goal item 4's case verbatim from this order (HANDOFF.md gets it only in Job 5). |
| 27 | The census predicts no new constant; the module count and the build's job count equal at the records commit and at G (at the master, from LEAN-35's report at G `d21fd22`: 5729 modules, 4193 jobs). |
| 31 | Review (a) is in before the gate's first library run; each block's review (b) before its commit; review (c) before any re-witness it asks for; review (d) before each leftover's commit. |
| 37 | The probes cover each new witness's names before it is written; the gate's generated copies are not probed. |
| 38 | The witness gate is not wrapped (as the other gates); each of its runs at a commit comes after that commit's `lake build`. Job 3's census imports `ClassicalLean` and runs through `rootrun.sh`. |

## Before approval (read-only in the repository)

1. Rule 11's check.
2. `git fetch origin` in the worktree. Then, each predicted and checked: `origin/master` and `git
   ls-remote github master` both `ac62f505db03edda95e7f7fa83a301a07ddda924`; `git status --porcelain` empty. If not, stop (rule 8).
3. Check the hashes and read the read list.
4. Check `crontab -l`, `systemctl --user list-timers` and `free -g`, and `nproc`.
5. Write your plan with `ds_file` (project `lean`, job `VACUITY-4`, kind `plan`): the jobs in order;
   every prediction you can make now; the witness gate's design (how it finds blocks and tells a
   comment or docstring line from a block, how it builds the in-place copy and names each turned
   block, where each block's check runs, how it reads the lakefile's options, what it does with a
   module that has no `example :=` block, how its output is laid out), with the expected whole-library
   time from the cut's timing of one copy; for each claiming typed example, the theorems you will
   witness and your first idea of each witness's values; the Superadditive reading, with the number of
   theorems; and how you will meet Goal item 4's case in MaximalInequality's two witnesses. Then stop
   and wait for Dustin's approval.

## Setup (after approval)

1. **The helpers.** As LEAN-35's Setup 1, from `~/lean/lean35-checks/` into `~/lean/vacuity4-checks/`
   (the 27 scripts, the two census tails, `allowlist.txt`, after checking all 64 characters of each
   hash; each `lean35-checks` to `vacuity4-checks` on the lines the cut lists; `probecheck.py`'s
   `BASE` line (line 29, `BASE = 'f5411f4'`) to `'ac62f50'`; `commit.sh`'s two trailers (line 16)
   to this session's own attribution
   lines). The two type-dump files from the lane (`lean/LEAN-33/scripts/TypeDumpPI.lean` and
   `lean/LEAN-33/scripts/g8-typediff.py`, the second as `g8_typediff.py`) into
   `~/lean/vacuity4-checks/inputs/`, by the connector route, their sha256 checked against the cut's
   list. `mkwitcheck.py` is copied as a reference only; the gate replaces it. The cut's scripts that
   the session runs (`census_examples2.py`, `sweep_select4.py`, `claim_scan5.py`) are extracted from
   Appendix A byte for byte into `~/lean/vacuity4-checks/cut/`, each checked against Appendix A's
   sha256 and against its copy in `/tmp/claude-ai-gate1/`. Then `pred-setup.md`, hashed.
2. **Tests before first use,** as LEAN-35's Setup 2, each predicted and logged.
3. **Branch.** Through `ev.sh --nolean`: `git fetch origin`; both masters `ac62f505db03edda95e7f7fa83a301a07ddda924`;
   porcelain empty. Then `git switch -c vacuity-4 ac62f505db03edda95e7f7fa83a301a07ddda924`.
4. **Records first,** one commit, no `.lean` file and no `tools/` file (rule 5). check_records then:
   PASS 140.
5. **Before runs at the records commit,** predicted from the cut: build, AxiomGate, VacuityGate and
   its tests, check_sorry, check_records, the module count, the type dump with its four controls (as
   LEAN-35's Setup 5), the report tool through `rootrun.sh` (its summary lines: the baseline of Goal
   item 7a), and Job 3's selection: `census_examples2.py` (Appendix A) on the tree, then
   `sweep_select4.py` (Appendix A) on that output, and its Lean file through `rootrun.sh` with the
   four options (`el.sh`'s flags), predicted equal to the cut's: the census output's sha256
   `f733c307bb88f1646a3072b76c722ad7acae59fde17ff77b8b4cea92110f8321`, the Lean file's sha256
   `7044e5832b68568addc64e81ab344b34767f5f76ebf78bae42db2e79b83b95a8`, and the text of the 46 `SELECT`
   lines (from `SELECT` on; the file-position prefix of each info line differs); and `claim_scan5.py`
   on the tree, its output's sha256 predicted
   `49007ab53eee49315310f524850c10b0a0647cca409be9e12666d40f0678247f`.

## The work

### Job 1: the witness gate

Write `tools/witness_gate.py`, its tests and fixtures (Goal items 1 and 2); run the tests, each
predicted; review (a) with its confirming pass; then the gate's first library run at the records
commit (rule 3), predicted from the cut, its wall time logged. One commit for the gate, its tests and
fixtures, after review (a) is clean and the tests pass; its message cites the runs (HANDOFF rule 39).
The commit adds `tools/witness_reviewed.txt` empty or holding only PrimitiveDivisor's entry; later
entries come with the commits that need them.

### Job 2: the witnesses

In the plan's order, one commit per module: the new rule-2 witnesses after the module's last line, the
typed claims removed, old blocks replaced, MinMax 443 moved; `el.sh` on the module (rc 0); `lake
build` of the module and its importers through `ev.sh` (0 errors, 0 warnings); `banned_vocab_scan.py
ClassicalLean`; the witness gate on that module (every line `OK`, `TYPED`, `NOT-A-BLOCK`, `LISTED` or
`LISTED-FAULT`);
review (b) for the group the module's blocks are in, with any fix and its confirming pass; one commit
staged by path, then its `COMMIT` line. MaximalInequality's two re-witnesses (Goal item 4) are one of
these commits.

### Job 3: the process sweep

The selection is Setup 5's run (it imports `ClassicalLean`): every theorem that some witness-form
block's docstring names (NAME, or `N.NAME` for a namespace `N` the module opens, exactly one existing)
and whose type uses one of `MeasureTheory.Filtration`, `MeasureTheory.Martingale`,
`MeasureTheory.Submartingale`, `MeasureTheory.Supermartingale`, `MeasureTheory.IsStoppingTime`,
`MeasureTheory.stoppedValue`, `MeasureTheory.stoppedProcess`, `MeasureTheory.hittingBtwn`,
`MeasureTheory.hittingAfter`, `Nat.iterate`, or a constant whose name contains `exitTime` or
`hitTime`, or contains a limit along `ℕ` (`Filter.atTop` at `ℕ`), or binds a variable that is not a
proof and whose type is a function from `ℕ`. At the cut: 46. Then review (c) of those of the 46 not
rewritten in Job 2 (44 at the cut: MaximalInequality's two are Goal item 4's; fewer if Job 2 rewrote a
selected block from Job 1's work list), in groups of at most 15, each brief naming its blocks by module
and theorem, to be found at HEAD by docstring NAME; then Job 2's procedure for each frozen one (Goal
item 5's cap). A witness that Job 2 writes for a theorem the
selection would pick is read against Goal item 4's case by review (b).

### Job 4: the leftovers and CI

Goal item 7a (the report tool's budget, run through `rootrun.sh` after the change, summary lines equal
to Setup 5's) and 7b (the FAIL text, with the vacuity tests and the code comparison before and after),
with review (d); one commit each. Then Goal item 6: the gate's whole-library wall time, at HEAD after
those two commits (the clean tree checked first), decides the CI step; if added, one commit for `ci.yml`, and the step's command
run locally on a planted fault (a scratch copy of one module with one witness cut short, through
`--root`: the gate fails naming it) and on the clean tree (it passes). The CI run itself happens only
after Dustin's push.

### Job 5: documents

- `HANDOFF.md` §1: a dated VACUITY-4 paragraph (round 73): the gate, the witnesses written, moved,
  replaced and removed, the sweep's outcome, any `LISTED-FAULT`, the leftovers, and the counts predicted
  in Job 6's prediction file.
- `HANDOFF.md` §4: the gate's entry (what it reads, its verdicts, its listing file, its stated limits:
  a hypothesis behind a definition that reducible unfolding does not open; a conclusion that opens
  with a hypothesis binder; anything else review (a) finds), "Five gates" to the right count, Goal item
  4's paragraph word for word, Goal item 8's paragraph, the CI paragraph's steps and its new sha256 (or
  why the gate is not in CI), and a note under "Left for a later gate order" that the two leftovers
  are done.
- One fresh cold reviewer reads the documents commit's diff alone (review (e)).

### Job 6: predictions, then the end checks

A prediction file, hashed, once every text is final: as LEAN-35's job 3 (no new constants; the census
of each changed module equal before and after), plus the witness gate's counts by verdict at G and its
time, and its tests. Then LEAN-35's jobs 5a and 5c to 5g in its forms, with the witness gate and its
tests added to 5a's gates, no bridge search (5b; no constant changes, rule 1), and these differences in
5g: `git diff --name-only <master> <G> -- ClassicalLean.lean tools .github ':(glob)lakefile*'
lake-manifest.json lean-toolchain records/rules.toml` predicted to list exactly the new and changed
`tools/` files and `ci.yml` (if Job 4 added the step); `git diff --name-only <master> <G> --
ClassicalLean` exactly the modules Goal items 3 to 5 changed; no `import` line in the diff; a script
that lists every removed line of `ClassicalLean/` predicted to list only lines of removed, replaced or
moved `example` blocks and of reworded docstrings of typed examples that stay, each named in round 73;
the type-dump `DIFF` line. The report tool runs once at G with the new budget and its summary lines are
reported (HANDOFF §4's standing rule of round 58). The push command, not run:
`cd ~/lean/classical-lean-paper-crypto && git push origin vacuity-4:master && git push github vacuity-4:master`.

## Done means

- Branch `vacuity-4` from `ac62f50`, clean tree, nothing pushed; records commit first; then the
  gate; then one commit per module; then the leftovers and CI; then documents; then records-only
  commits.
- The witness gate and its tests in `tools/`, fail-tested as Goal item 2 says, review (a) clean.
- At G: `WITNESSGATE PASS`, every line matching the `UNREAD` pattern with one verdict, `LISTED`
  entries each with a reason, no stale listing; no `TYPED-CLAIM` and no `UNREAD` left; each
  `LISTED-FAULT` in the report with its evidence.
- Every theorem the thirteen claiming examples named has a rule-2 witness, or is NOT WITNESSED with its
  reason; MinMax 443 outside the namespace; MaximalInequality's two witnesses meet Goal item 4's case;
  the sweep done and its frozen witnesses re-witnessed within the cap, the rest `LISTED-FAULT`.
- The report tool has a finite outer budget and the same summary lines; the vacuity gate's FAIL text
  names case 5 and the meaning of UNCHECKED and KERNEL-REJECTED, with its verdicts and code unchanged.
- The CI step added, or its absence explained with the measured time.
- HANDOFF.md §1 and §4 changed as Job 5 says; the drift check passes.
- The type-dump diff all zeros; every gate as predicted at G or each miss reported; gate 7 ALL PASSED;
  after G only `records/` changed; check_records PASS at the final HEAD; citecheck every commit `OK`.
- The plan and the report in `lean/VACUITY-4/`, the push-review file in `lean/VACUITY-4/data/`, hashes
  matching yours.

Then report in a few plain sentences: what the gate checks and its verdict counts, the witnesses
written, moved, replaced and removed, the sweep's outcome, the gate results beside the predictions, the
two files' hashes and the push command. Dustin reads your replies carefully and is still learning to
read code: plain words, and define a technical term the first time you use it. When you need a
decision from him, ask in one line with your recommended answer first.

## Not in this order

- A machine check for a frozen process: a process's increments are values the gate cannot compute in
  general; rule 3's new case is met by review (Goal items 4 and 5).
- `lake comparator`, `lake check` and a move to Lean v4.35.0 or later (Goal item 8).
- VACUITY-3 rows 31 and 32 (YuleWalker; LEAN-36). LEAN-34's and LEAN-35's documentation follow-ups
  (MethodOfTypes' module docstring, NeymanPearson's list entry for `size_add_one_sub_power_ge`,
  FiniteChain's title and its sentence on zero entries) and drop tests of LEAN-35's five theorems:
  they change declarations' docstrings or need Lean scratch work outside this Goal; a later landing
  order takes them.
- The bridge search (no constant changes).
- Any push; deleting GitHub branches.

## Revisions

- r0, the draft (claude-ai, 2026-10-25, Project LEAN), sha256
  `e18b1793e25591492449829c34f69d11165aac44921a97ec3f2a156b5950e244`.
- r1, review pass 1 (one fresh subagent, 2026-10-25; PASS WITH FINDINGS, 0 BLOCKER, 11 MAJOR, 19
  MINOR; its report saved verbatim, `rv-draft-pass1.md`, sha256
  `262d7601a470d4c7e6fe8e90dfa293907cdf2736735aa8f4a092996fdd60e1c7`), all applied. MAJOR: the CI
  decision measured at the last commit of Jobs 2 and 3, not at G (M1); the Scope allows replacing old
  blocks and rewording a staying docstring (M2); round 73 names the modules known at Setup 4, the
  others in its follow-up (M3); a cap of 6 on faults found by the first library run, the rest
  `LISTED-FAULT` (M4); `PARTIAL` reads the whole telescope, as `mkwitcheck.py` did (M5); `BROKEN` by
  collected axioms, and `COPY-ERROR` for any error in the copy (M6); the copy uses the build's options,
  and rows for rules 20, 37 and 38 (M7); rule 3's new case reworded (M8); "`n ≥ 2`" dropped, since it
  would forbid LEAN-35's good item 125 witness (`n = 1`) and rule 3's size rule already gives `n ≥ 1`
  (M9); one Lean process at a time, the copy of the largest module timed at the cut, the CI time stated
  as unmeasured until the first CI run (M10); Setup 1 copies the two type-dump files (M11). MINOR: the
  CI paragraph's order; the plan's lines 66 to 67; 7 blind spots plus one non-witness; the source of
  "9" and claude-ai's two prediction misses; Comparator's wording and the plan's purpose for it; that
  the plan's step 4 did not note gate 7; the three departures from row 104 named; `WRONG-NAME` by
  resolution in scope; what a listing's hash covers and which verdicts may be listed; the cut to look
  for other claim phrases; `NOT-A-BLOCK` and `UNREAD`; the gate's command line and its first run as
  evidence; a gate change after review (a); Goal item 7's second control, its end of the ladder and its
  baseline; this order's own rows for HANDOFF rules 12, 19, 20, 26, 27, 31, 37 and 38; MERGE-2's job
  4a in the read list; at most 15 witnesses per sweep reviewer; the off-limits list written out; MinMax
  443 as `sum_eigenvalues_eq_iSup`'s witness and possibly degenerate, Superadditive's count, and
  LongestRun's line confirmed at the cut.
- r2, the confirming pass (the same reviewer, 2026-10-25; NOT CONFIRMED; its report saved verbatim,
  `rv-draft-pass2.md`, sha256 `27f93cee1654889f806a6bd2168c3a3c5c7f82fdad23518094d5a5afa5c3cd2f`): 26
  of pass 1's 30 FIXED, 4 PARTLY FIXED (M8, MINOR 4, 8, 11), none NOT FIXED. All its new findings
  applied. BLOCKER B1: `WRONG-NAME` as r1 worded it would fail nearly every library witness (the
  docstring gives the short name, the block sits after the namespace's `end`); now NAME is resolved in
  scope or, failing that, matched as `N.NAME` for exactly one namespace `N` the module opens, with a
  test for the library's usual form. MINOR: `n + 1` points, not `2^n` (N1; the reviewer's own pass-1
  error); the deterministic clause asks every step to move, unless the hypotheses force a pause, and
  `n ≥ 1` is stated in the case (N2, N3); `NOT-A-BLOCK` covers comment, docstring and string lines,
  leading spaces allowed, and the cross-check's scope and exclusions are said (N4); round 73 names the
  seven claim modules and MaximalInequality, PrimitiveDivisor apart (N5); `LISTED-FAULT` allowed by
  Goal items 3 and 5, and in Job 2's passing list (N6); the gate never raises, so a nonzero rc means
  the copy failed, and an error inside a block gives `BROKEN` (N7); the CI time measured at HEAD after
  Job 4's leftover commits (N8); the CI step's own `timeout-minutes: 45` (N9); the census line behind
  "4" (N10); `--root` defined, and the first library run with the gate's files untracked (N11); the
  package's `leanOptions` from whichever lakefile, and the turned blocks' linter warnings in the plan
  (N12); Job 3 selects the theorems the witnesses name (N13). Added: the fixtures' forbidden words are
  outside `check_sorry.py`'s and the banned scan's scope (the reviewer's "Not checked").

- r3, the cut (claude-ai, 2026-10-25, 11:12 to 11:28 EDT, at `ac62f50`; "Measured at the cut"). Filled
  in: the master and the branch base; the CI workflow's sha256; the lakefile's options; the gates'
  counts (LEAN-35's at G); the heartbeat lines, with Goal item 7a now saying that the per-theorem
  budget stays; the two scanners' scope; the lines the gate reads (369; `NOT-A-BLOCK` 0); one timed
  copy of each of the two largest witnessed modules, and the gate's time estimate (Goal item 6); each
  changed module's lines, blocks and sha256; the sweep selection, now run in Setup 5 with
  `sweep_select4.py` (46 of 149; Goal item 5 and Job 3 give the reviewers); the text LEAN-35's INDEX
  and CLAIMS rows get for its push (rule 5); the helpers' lines (Setup 1); the files to check
  (`cut-manifest.txt` and the lane table). Changed by what the cut found: three more claiming typed
  examples, with the singular "hypothesis of" (ConvexConjugate 126, Spectral3x3 175,
  GeneralizedLeastSquares 261), so 13 claims in 10 modules and four `TYPED-CLAIM` phrases (Why, What
  is already true, Goal items 1 to 3, rules 3 and 5, Done means); five other docstrings with a wider
  word, read and judged not to claim a witness; a docstring is only a `/--` comment just above (Goal
  item 1), with a fixture for a section comment (Goal item 2); Pell 58 starts with `examples`;
  LongestRun 268 is VACUITY-3's line 209; Superadditive read (five theorems); the date of Goal item
  4's paragraph is the documents commit's; rule 3's first library run predicted verdict by verdict.
  claude-ai's prediction misses at the cut are under "What is already true".
- r4, the cut's review pass 1 (a fresh subagent, 2026-10-25; PASS WITH FINDINGS, 0 BLOCKER, 1 MAJOR,
  14 MINOR; its report saved verbatim, `rv-cut-pass1.md`, sha256
  `1452355d4323e63091a53e4696c5a047530a00b7ffd6e8a38800b32c23abdaf3`), all applied, with four new
  measurements at `ac62f50` (`cut_facts4.sh`, 11:56:59 to 11:57:04 EDT; `pred-cut-4.txt` before it).
  MAJOR M1: the gate reads blocks and docstrings as Lean does (any `example` keyword outside comments
  and strings; the docstring Lean attaches, across blank lines; phrases after whitespace is
  collapsed), with a second cross-check and five fixtures (Goal items 1 and 2); `claim_scan3.py`
  measured that the library has none of the missed forms, so rule 3's counts stand, and Setup 5 runs
  it again. MINOR: the 46 keyed by theorem, and Job 3's reviewers find blocks by NAME (m1);
  Superadditive's `map_zero` must be named `Superadditive.map_zero`, measured by `name_scope.py`, and
  every new witness's NAME is probed in its scope (m2); the misses record corrected, with the
  prediction files' sha256 (m3); the Superadditive row (m4); the manifest pointer, the lane table's
  time, and a stop if `/tmp/claude-ai-gate1/` is gone (m5, m14); Setup 5's predicted sha256 of the
  census output, the Lean file and `claim_scan3.py`'s output, and Setup 1 extracting the cut's three
  scripts (m6); the manifest's scope stated and `claim_phrases.py` listed (m7); the records-only diff
  quoted (m8); the Rules gate's scope measured (m9); "can be met" as the fourth phrase (it occurs only
  in claims) and the wider words widened (m10); LEAN-35's push recorded in the earlier rows' form,
  with DSMain's master ref time (m11); possibly degenerate old values flagged (m12); two wording slips
  (m13); the time estimate called one by line count (m14).
- r5, the cut's review pass 2 (the same reviewer, 2026-10-25; NOT CONFIRMED: 14 of 15 FIXED, m2
  PARTLY FIXED; 0 BLOCKER, 0 MAJOR, 9 new MINOR; its report saved verbatim, `rv-cut-pass2.md`, sha256
  `3ae47c89b769b554447cd1faa668128cf534581072a5ba682785cea28c1a3a5f`), all applied, with new
  measurements at `ac62f50` (`cut_facts5.sh` and `claim_scan5.py`, 12:15:19 to 12:17:40 EDT;
  `pred-cut-5.txt` before them). m2's remainder and N2: the name probe says what to expect for the
  usual short name ("unknown identifier" after the module's last line, and exactly one `N.NAME`), and
  the dotted `Superadditive.map_zero` was measured. N1: the 24 names counted right. N3: the docstring
  rule goes over `--` and plain comments, `set_option … in` and all modifiers, as Lean does, and over
  an attribute only by bracket matching; `claim_scan5.py` measures it (the same output as
  `claim_scan3.py`'s; `claim_scan4.py`'s attribute bug found and recorded), with two fixtures. N4: char
  literals and raw strings lexed as strings, with a fixture. N5: the "can be met" sentence and the scan
  that uses the gate's phrases. N6: the header's revision and times, the section's times, the
  hash-check file. N7: both cross-checks predicted. N8: the missed predictions recorded. N9: five
  fixtures; what a rebuilt `/tmp/claude-ai-gate1/` would mean.

## Appendix A: claude-ai's scripts

### `census_examples.py` (the draft's census; output `census.out`)

sha256 `0fffdb7572a3e0b81ae8e81e02e0ff2c569899e1f47e7537baed1c3eabed5a3c`, 4554 bytes.

```python
"""Census of `example` blocks in ClassicalLean/, read-only (claude-ai, gate order draft, 2026-10-25).

usage: python3 -I census_examples.py REPO_ROOT

For every line that starts `example` in ClassicalLean/**/*.lean it prints one TSV line:
  module  line  kind  ns  doc_name  process  first_line
kind     : 'witness-form' (starts `example :=`), 'typed' (`example :`), 'binder' (`example (`,
           `example {`, `example [`, `example ⦃`), 'other'
ns       : the innermost open namespace at that line ('-' when none), tracked from
           `namespace X` / `section [X]` / `end [X]` lines at column 0
doc_name : NAME from "The hypotheses of `NAME` hold together" in the docstring just above
           (the `/-- ... -/` block ending on the line above, or above `open ... in` lines), else '-'
process  : 'yes' when the block (from its line to the next line not starting with a space) names
           Filtration, Martingale, Submartingale, Supermartingale, IsStoppingTime, stoppedValue,
           stoppedProcess or hitting; else 'no'
Then totals by kind, by ns ('-' vs inside), witness-form without a witness docstring, typed with a
witness docstring, and the process 'yes' list. Predictions are written beside the run, not here.
"""
import os
import re
import sys
from collections import Counter

root = sys.argv[1]
PROC = re.compile(r'Filtration|Martingale|Submartingale|Supermartingale|IsStoppingTime|stoppedValue|stoppedProcess|hitting')
DOC = re.compile(r'The hypotheses of `([^`]+)` hold together')
rows = []
for dp, dn, fn in os.walk(os.path.join(root, 'ClassicalLean')):
    dn.sort()
    for f in sorted(fn):
        if not f.endswith('.lean'):
            continue
        p = os.path.join(dp, f)
        mod = os.path.relpath(p, root)[:-5].replace(os.sep, '.')
        L = open(p, encoding='utf-8').read().split('\n')
        stack = []
        for i, l in enumerate(L):
            if l.startswith('namespace '):
                stack.append(('ns', l.split()[1]))
            elif l.startswith('section'):
                parts = l.split()
                stack.append(('sec', parts[1] if len(parts) > 1 else ''))
            elif l.startswith('end') and (l == 'end' or l.startswith('end ')):
                parts = l.split()
                name = parts[1] if len(parts) > 1 else ''
                for k in range(len(stack) - 1, -1, -1):
                    if stack[k][1] == name or (name == '' and stack[k][0] == 'sec'):
                        del stack[k:]
                        break
            if not l.startswith('example'):
                continue
            if l.startswith('example :='):
                kind = 'witness-form'
            elif l.startswith('example :'):
                kind = 'typed'
            elif re.match(r'example\s*[\(\{\[⦃]', l):
                kind = 'binder'
            else:
                kind = 'other'
            nss = [n for t, n in stack if t == 'ns']
            ns = nss[-1] if nss else '-'
            j = i - 1
            while j >= 0 and L[j].startswith('open ') and L[j].rstrip().endswith(' in'):
                j -= 1
            doc = ''
            if j >= 0 and L[j].rstrip().endswith('-/'):
                d = j
                while d >= 0 and not L[d].lstrip().startswith('/--'):
                    d -= 1
                doc = ' '.join(L[d:j + 1])
            m = DOC.search(doc)
            e = i + 1
            while e < len(L) and L[e].startswith(' '):
                e += 1
            body = '\n'.join(L[i:e])
            proc = 'yes' if PROC.search(body) else 'no'
            rows.append((mod, i + 1, kind, ns, m.group(1) if m else '-', proc, l[:70]))
for r in rows:
    print('\t'.join(str(x) for x in r))
print('== TOTAL', len(rows))
print('== BY KIND', dict(Counter(r[2] for r in rows)))
print('== INSIDE A NAMESPACE', sum(1 for r in rows if r[3] != '-'),
      dict(Counter(r[2] for r in rows if r[3] != '-')))
print('== WITNESS-FORM WITHOUT A WITNESS DOCSTRING', [(r[0], r[1]) for r in rows if r[2] == 'witness-form' and r[4] == '-'])
print('== TYPED OR BINDER WITH A WITNESS DOCSTRING', len([r for r in rows if r[2] != 'witness-form' and r[4] != '-']),
      [(r[0], r[1], r[4]) for r in rows if r[2] != 'witness-form' and r[4] != '-'])
print('== MODULES WITH A WITNESS-FORM BLOCK', len({r[0] for r in rows if r[2] == 'witness-form'}))
print('== PROCESS yes, witness docstring', len([r for r in rows if r[5] == 'yes' and r[4] != '-']))
for r in rows:
    if r[5] == 'yes' and r[4] != '-':
        print('PROC\t' + '\t'.join(str(x) for x in r[:5]))
```

### `typed_witness_claims.py` (the draft's claims scan; output `claims.out`)

sha256 `063ccb1428a057ee92c60915e8d6252c0aef525e61e9ece519e74129a8b2dfab`, 2199 bytes.

```python
"""List the typed or binder `example`s whose docstring claims a witness, read-only (claude-ai, 2026-10-25).

usage: python3 -I typed_witness_claims.py REPO_ROOT

A claim is a docstring (just above the block, or above its `open ... in` lines) that contains
'hypotheses of' or 'can be met together' or 'hold together'. For each such typed/binder example it
prints module, line, every backticked name in the docstring, and for each name whether the module
has a witness-form block whose docstring says "The hypotheses of `NAME` hold together".
"""
import os
import re
import sys

root = sys.argv[1]
CLAIM = re.compile(r'hypotheses of|can be met together|hold together')
NAMES = re.compile(r'`([A-Za-z_][\w.\']*)`')
WIT = re.compile(r'The hypotheses of `([^`]+)` hold together')


def doc_above(L, i):
    j = i - 1
    while j >= 0 and L[j].startswith('open ') and L[j].rstrip().endswith(' in'):
        j -= 1
    if j >= 0 and L[j].rstrip().endswith('-/'):
        d = j
        while d >= 0 and not L[d].lstrip().startswith('/--'):
            d -= 1
        return ' '.join(L[d:j + 1])
    return ''


n = 0
for dp, dn, fn in os.walk(os.path.join(root, 'ClassicalLean')):
    dn.sort()
    for f in sorted(fn):
        if not f.endswith('.lean'):
            continue
        p = os.path.join(dp, f)
        mod = os.path.relpath(p, root)[:-5].replace(os.sep, '.')
        L = open(p, encoding='utf-8').read().split('\n')
        witnessed = set()
        for i, l in enumerate(L):
            if l.startswith('example :='):
                m = WIT.search(doc_above(L, i))
                if m:
                    witnessed.add(m.group(1).split('.')[-1])
        for i, l in enumerate(L):
            if not l.startswith('example') or l.startswith('example :='):
                continue
            doc = doc_above(L, i)
            if not CLAIM.search(doc):
                continue
            n += 1
            names = [x for x in NAMES.findall(doc) if '_' in x or '.' in x]
            cov = ', '.join(f"{x}:{'has-rule2' if x.split('.')[-1] in witnessed else 'NO-rule2'}" for x in names)
            print(f'{mod}\t{i + 1}\t{cov}\t{doc[:110]}')
print('== CLAIMING TYPED/BINDER EXAMPLES', n)
```

### `cut_facts.sh` (the cut, part 1; output `cut-facts-1.out`)

sha256 `8045d1943c9700223550d493c9c436fc470cb95f677b01bcd6cde158e7516726`, 4194 bytes.

```bash
#!/usr/bin/env bash
# VACUITY-4 cut facts, read-only (claude-ai, 2026-10-25). Run on DSMain as dustin:
#   bash /tmp/claude-ai-gate1/cut_facts.sh > /tmp/claude-ai-gate1/cut-facts-1.out 2>&1
# Reads the repository at its HEAD, LEAN-35's helpers and the records; writes nothing outside
# /tmp/claude-ai-gate1/. Checks `git status --porcelain` before and after.
set -u
R=$HOME/lean/classical-lean-paper-crypto
C=$HOME/lean/lean35-checks
G=/tmp/claude-ai-gate1
export GIT_OPTIONAL_LOCKS=0 LC_ALL=C
cd "$R" || exit 2
echo "== start $(date '+%F %T %Z')"
echo "== porcelain-before $(git status --porcelain | wc -l)"
echo "== masters"; git ls-remote origin master; git ls-remote github master
echo "== head $(git rev-parse HEAD) branch $(git branch --show-current)"
echo "== ci.yml"; sha256sum .github/workflows/ci.yml
echo "== lakefile.toml [leanOptions] block"; sed -n '/^\[leanOptions\]/,/^\[[a-zA-Z]/p' lakefile.toml
M="ClassicalLean/Algebra/Kantorovich.lean ClassicalLean/Algebra/MinMax.lean ClassicalLean/InformationTheory/CompressionTest.lean ClassicalLean/Order/Superadditive.lean ClassicalLean/Probability/EffectiveSampleSize.lean ClassicalLean/Probability/GamblersRuin.lean ClassicalLean/Probability/LongestRun.lean ClassicalLean/Probability/MaximalInequality.lean ClassicalLean/NumberTheory/PrimitiveDivisor.lean"
T="tools/VacuityGate.lean tools/UninformativeReport.lean tools/run_vacuity_tests.py tools/check_sorry.py tools/banned_vocab_scan.py tools/vacuity_reviewed.txt"
echo "== modules and tools: sha256"; sha256sum $M $T
echo "== modules: lines"; wc -l $M
echo "== maxHeartbeats lines"; grep -n 'maxHeartbeats' tools/UninformativeReport.lean tools/VacuityGate.lean
echo "== check_sorry and banned scan: scope lines"; grep -n "tools\|ClassicalLean'\|\.lake" tools/check_sorry.py | head -8; grep -n "argv\|ClassicalLean" tools/banned_vocab_scan.py | head -8
echo "== LongestRun example lines"; grep -n '^example' ClassicalLean/Probability/LongestRun.lean
echo "== LongestRun 268 blame"; git blame -L 268,268 --porcelain ClassicalLean/Probability/LongestRun.lean | sed -n '1p;/^summary/p'
echo "== MaximalInequality example lines"; grep -n '^example' ClassicalLean/Probability/MaximalInequality.lean
echo "== MinMax namespace and example lines"; grep -n '^namespace\|^end\|^example' ClassicalLean/Algebra/MinMax.lean
echo "== Superadditive lines 100-125"; sed -n '100,125p' ClassicalLean/Order/Superadditive.lean
echo "== Superadditive theorems"; grep -n '^theorem\|^lemma' ClassicalLean/Order/Superadditive.lean
echo "== witnessed modules: lines, largest 5"; for f in $(grep -rl '^example :=' ClassicalLean --include='*.lean'); do echo "$(wc -l < "$f") $f"; done | sort -n | tail -5
echo "== witnessed modules: count $(grep -rl '^example :=' ClassicalLean --include='*.lean' | wc -l), lines in all $(cat $(grep -rl '^example :=' ClassicalLean --include='*.lean') | wc -l)"
echo "== records: INDEX last line (first 300 chars)"; tail -1 records/orders/INDEX.md | cut -c1-300
echo "== records: INDEX last line (last 200 bytes)"; tail -c 200 records/orders/INDEX.md; echo
echo "== records: CLAIMS last line (first 200 chars)"; tail -1 records/CLAIMS.md | cut -c1-200
echo "== records: CLAIMS last line (last 200 bytes)"; tail -c 200 records/CLAIMS.md; echo
echo "== records: counts orders $(ls records/orders | wc -l) rounds $(ls records/rounds | wc -l) INDEX lines $(wc -l < records/orders/INDEX.md) CLAIMS lines $(wc -l < records/CLAIMS.md)"
echo "== records: last two rounds"; ls records/rounds | tail -2
echo "== helpers: scripts $(ls $C/scripts | wc -l)"; sha256sum $C/scripts/* $C/census/* $C/allowlist.txt
echo "== helpers: lean35-checks lines"; grep -c 'lean35-checks' $C/scripts/* | grep -v ':0$'
echo "== helpers: probecheck BASE"; grep -n '^BASE' $C/scripts/probecheck.py
echo "== helpers: commit.sh trailers"; grep -n 'Co-Authored-By\|Claude-Session' $C/scripts/commit.sh
echo "== helpers: inputs"; sha256sum $C/inputs/* 2>&1
echo "== nproc $(nproc)"; free -g | head -2
echo "== pgrep lean"; pgrep -ax lean; echo "pgrep rc=$?"
echo "== claim phrases"; python3 -I $G/claim_phrases.py .
echo "== porcelain-after $(git status --porcelain | wc -l)"
echo "== end $(date '+%F %T %Z')"
```

### `cut_facts2.sh` (the cut, part 2 (runs `claim_scan.py`, version 1, superseded); output `cut-facts-2.out`)

sha256 `a7ba28f087d5ad311dec3899ca8167f826d0d328c1bdd9e19e59fb3d889728e1`, 2194 bytes.

```bash
#!/usr/bin/env bash
# VACUITY-4 cut facts, part 2, read-only (claude-ai, 2026-10-25). Run on DSMain as dustin:
#   bash /tmp/claude-ai-gate1/cut_facts2.sh > /tmp/claude-ai-gate1/cut-facts-2.out 2>&1
set -u
R=$HOME/lean/classical-lean-paper-crypto
C=$HOME/lean/lean35-checks
G=/tmp/claude-ai-gate1
export GIT_OPTIONAL_LOCKS=0 LC_ALL=C
cd "$R" || exit 2
echo "== start $(date '+%F %T %Z') head $(git rev-parse HEAD) porcelain-before $(git status --porcelain | wc -l)"
echo "== UninformativeReport 36-48"; sed -n '36,48p' tools/UninformativeReport.lean
echo "== UninformativeReport 130-142"; sed -n '130,142p' tools/UninformativeReport.lean
echo "== UninformativeReport 352-366"; sed -n '352,366p' tools/UninformativeReport.lean
echo "== VacuityGate 832-842"; sed -n '832,842p' tools/VacuityGate.lean
echo "== LongestRun 255-300"; sed -n '255,300p' ClassicalLean/Probability/LongestRun.lean
echo "== LongestRun 320-385"; sed -n '320,385p' ClassicalLean/Probability/LongestRun.lean
echo "== LongestRun log of e81ab8a"; git log -1 --format='%h %cI %s' e81ab8a; git log --format='%h %s' e81ab8a..HEAD -- ClassicalLean/Probability/LongestRun.lean
echo "== Spectral3x3 160-200"; sed -n '160,200p' ClassicalLean/Geometry/Spectral3x3.lean
echo "== Spectral3x3 example and namespace lines"; grep -n '^example\|^namespace\|^end\|gap_identity_of_offDiagCross_eq_zero' ClassicalLean/Geometry/Spectral3x3.lean; wc -l ClassicalLean/Geometry/Spectral3x3.lean; sha256sum ClassicalLean/Geometry/Spectral3x3.lean
echo "== PrimitiveDivisor 340-423"; sed -n '340,423p' ClassicalLean/NumberTheory/PrimitiveDivisor.lean
echo "== Tribonacci 190-200"; sed -n '190,200p' ClassicalLean/NumberTheory/Tribonacci.lean
echo "== Superadditive 1-72"; sed -n '1,72p' ClassicalLean/Order/Superadditive.lean
echo "== claim scan"; python3 -I $G/claim_scan.py .
echo "== el.sh"; cat $C/scripts/el.sh
echo "== ev.sh"; cat $C/scripts/ev.sh
echo "== rootrun.sh"; cat $C/scripts/rootrun.sh
echo "== olean of ClassicalLean"; ls -l --time-style=+%FT%T .lake/build/lib/lean/ClassicalLean.olean 2>&1
echo "== pgrep lean"; pgrep -ax lean; echo "pgrep rc=$?"
echo "== porcelain-after $(git status --porcelain | wc -l) end $(date '+%F %T %Z')"
```

### `cut_facts3.sh` (the cut, part 3 (runs `census_examples2.py`, `claim_scan2.py`, the timed copies and `sweep_select2.py`, superseded); output `cut-facts-3.out`)

sha256 `1b19d6fc708059fce72d149ffa1907c093a3ebfc6979ffa55edf55c2f86acf13`, 4920 bytes.

```bash
#!/usr/bin/env bash
# VACUITY-4 cut facts, part 3 (claude-ai, 2026-10-25). Run on DSMain as dustin:
#   bash /tmp/claude-ai-gate1/cut_facts3.sh > /tmp/claude-ai-gate1/cut-facts-3.out 2>&1
# Read-only in the repository (git status --porcelain checked before and after). Its Lean runs, one at
# a time, each under the 12 GB cap that ev.sh --cap uses, only when no `lean` process runs: `lake
# build --no-build` (a check that the build is current; it builds nothing), two copies of witnessed
# modules elaborated outside the repository with the lakefile's four leanOptions (timed), and the
# sweep selection (imports ClassicalLean). Writes only under /tmp/claude-ai-gate1/.
set -u
R=$HOME/lean/classical-lean-paper-crypto
G=/tmp/claude-ai-gate1
export GIT_OPTIONAL_LOCKS=0 LC_ALL=C PATH=$HOME/.elan/bin:$PATH
cd "$R" || exit 2
echo "== start $(date '+%F %T %Z') head $(git rev-parse HEAD) porcelain-before $(git status --porcelain | wc -l)"
echo "== Pell 55-60"; sed -n '55,60p' ClassicalLean/NumberTheory/Pell.lean
for f in Analysis/ConvexConjugate Statistics/GeneralizedLeastSquares Statistics/CramerRao; do
  echo "== $f: example, namespace and end lines"; grep -n '^example\|^namespace\|^end' ClassicalLean/$f.lean; wc -l ClassicalLean/$f.lean; sha256sum ClassicalLean/$f.lean
done
echo "== ConvexConjugate 118-135"; sed -n '118,135p' ClassicalLean/Analysis/ConvexConjugate.lean
echo "== GeneralizedLeastSquares 255-268"; sed -n '255,268p' ClassicalLean/Statistics/GeneralizedLeastSquares.lean
echo "== CramerRao 258-280"; sed -n '258,280p' ClassicalLean/Statistics/CramerRao.lean
echo "== census2"; python3 -I $G/census_examples2.py . > $G/census2.out; echo "rc=$?"; sha256sum $G/census2.out; grep '^==' $G/census2.out
echo "== census vs census2"; diff $G/census.out $G/census2.out && echo "census2 SAME as census"
echo "== census2 rows naming the three theorems, and CramerRao's rows"; grep -P '\t(convexConjugate_anti|glsMatrix_ones_eq_minWeights|gap_identity_of_offDiagCross_eq_zero)\t' $G/census2.out; grep -P '^ClassicalLean\.Statistics\.CramerRao\t' $G/census2.out
echo "== claim scan 2"; python3 -I $G/claim_scan2.py . > $G/claim-scan-2.out 2>&1; echo "rc=$?"; sha256sum $G/claim-scan-2.out; cat $G/claim-scan-2.out
echo "== LongestRun: the line of 268's docstring in each commit"
for c in e81ab8a^ e81ab8a b0b4f5e 49bcd41 65ccb6c cfdd9ac 82310b3 HEAD; do
  echo "$c $(git rev-parse --short $c) $(git show $c:ClassicalLean/Probability/LongestRun.lean | grep -n 'The hypotheses of `measureReal_no_run_le` hold together (order LEAN-28' | cut -d: -f1)"
done
echo "== modules: all $(find ClassicalLean -name '*.lean' | wc -l), lines $(cat $(find ClassicalLean -name '*.lean') | wc -l)"
U=$(grep -rlP '^\s*(@\[.*\]\s*)?(private |noncomputable )*example\b' ClassicalLean --include='*.lean')
echo "== modules with an UNREAD-pattern line: $(echo "$U" | wc -l), lines in them $(cat $U | wc -l)"
F="-Dpp.unicode.fun=true -DrelaxedAutoImplicit=false -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3"
CAP="systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 /usr/bin/time -v"
echo "== pgrep lean"; pgrep -ax lean; p=$?; echo "pgrep rc=$p"
if [ $p -ne 1 ]; then echo "== a lean process runs: the Lean part is not started"; else
  echo "== lake build --no-build ($(date '+%T'))"; $CAP lake build --no-build > $G/nobuild.out 2>&1; nb=$?; echo "rc=$nb"; grep -v '^\s' $G/nobuild.out | tail -3; grep -E 'Elapsed|Maximum resident' $G/nobuild.out
  mkdir -p $G/time
  for m in Statistics/Sufficiency Probability/GamblersRuin; do
    b=$(basename $m); cp ClassicalLean/$m.lean $G/time/$b.lean; sha256sum ClassicalLean/$m.lean $G/time/$b.lean
    echo "== time $b ($(date '+%T'))"; $CAP nice -n 19 lake env lean $F $G/time/$b.lean > $G/time-$b.out 2>&1; echo "rc=$?"
    grep -E 'Elapsed|Maximum resident|Exit status' $G/time-$b.out; echo "warning lines $(grep -c 'warning' $G/time-$b.out) error lines $(grep -c 'error' $G/time-$b.out)"; sha256sum $G/time-$b.out
  done
  if [ $nb -eq 0 ]; then
    echo "== sweep select ($(date '+%T'))"; python3 -I $G/sweep_select2.py . $G/census2.out $G/SweepSelect.lean; echo "gen rc=$?"; sha256sum $G/SweepSelect.lean
    $CAP nice -n 19 lake env lean $F $G/SweepSelect.lean > $G/sweep-select.out 2>&1; echo "rc=$?"; sha256sum $G/sweep-select.out
    grep -E 'Elapsed|Maximum resident|Exit status' $G/sweep-select.out
    echo "SELECT $(grep -c 'SELECT ClassicalLean' $G/sweep-select.out) SKIP $(grep -c 'SKIP ' $G/sweep-select.out) MISSING $(grep -c 'MISSING ' $G/sweep-select.out) AMBIGUOUS $(grep -c 'AMBIGUOUS ' $G/sweep-select.out)"
    grep -E 'TARGET|SWEEP-SELECT|SELECT ClassicalLean|MISSING|AMBIGUOUS|error' $G/sweep-select.out
  else echo "== the build is not current: the sweep select is not started"; fi
fi
echo "== pgrep lean after"; pgrep -ax lean; echo "pgrep rc=$?"
echo "== porcelain-after $(git status --porcelain | wc -l) end $(date '+%F %T %Z')"
```

### `census_examples2.py` (the census, version 2; output `census2.out`, equal to `census.out`)

sha256 `46a1ca0ba71a104aa9572542fefb24f3fc53e5e3f08f95f65b280479dc1e04b6`, 4907 bytes.

```python
"""Census of `example` blocks in ClassicalLean/, read-only (claude-ai, gate order draft, 2026-10-25).

Version 2 (the cut): the docstring is the comment ending on the line above only when that comment
opens with `/--`; a `/-!` or `/-` comment there means no docstring (version 1 walked back past it
to an earlier docstring: NumberTheory/PrimitiveDivisor line 401, found by claim_scan.py).

usage: python3 -I census_examples.py REPO_ROOT

For every line that starts `example` in ClassicalLean/**/*.lean it prints one TSV line:
  module  line  kind  ns  doc_name  process  first_line
kind     : 'witness-form' (starts `example :=`), 'typed' (`example :`), 'binder' (`example (`,
           `example {`, `example [`, `example ⦃`), 'other'
ns       : the innermost open namespace at that line ('-' when none), tracked from
           `namespace X` / `section [X]` / `end [X]` lines at column 0
doc_name : NAME from "The hypotheses of `NAME` hold together" in the docstring just above
           (the `/-- ... -/` block ending on the line above, or above `open ... in` lines), else '-'
process  : 'yes' when the block (from its line to the next line not starting with a space) names
           Filtration, Martingale, Submartingale, Supermartingale, IsStoppingTime, stoppedValue,
           stoppedProcess or hitting; else 'no'
Then totals by kind, by ns ('-' vs inside), witness-form without a witness docstring, typed with a
witness docstring, and the process 'yes' list. Predictions are written beside the run, not here.
"""
import os
import re
import sys
from collections import Counter

root = sys.argv[1]
PROC = re.compile(r'Filtration|Martingale|Submartingale|Supermartingale|IsStoppingTime|stoppedValue|stoppedProcess|hitting')
DOC = re.compile(r'The hypotheses of `([^`]+)` hold together')
rows = []
for dp, dn, fn in os.walk(os.path.join(root, 'ClassicalLean')):
    dn.sort()
    for f in sorted(fn):
        if not f.endswith('.lean'):
            continue
        p = os.path.join(dp, f)
        mod = os.path.relpath(p, root)[:-5].replace(os.sep, '.')
        L = open(p, encoding='utf-8').read().split('\n')
        stack = []
        for i, l in enumerate(L):
            if l.startswith('namespace '):
                stack.append(('ns', l.split()[1]))
            elif l.startswith('section'):
                parts = l.split()
                stack.append(('sec', parts[1] if len(parts) > 1 else ''))
            elif l.startswith('end') and (l == 'end' or l.startswith('end ')):
                parts = l.split()
                name = parts[1] if len(parts) > 1 else ''
                for k in range(len(stack) - 1, -1, -1):
                    if stack[k][1] == name or (name == '' and stack[k][0] == 'sec'):
                        del stack[k:]
                        break
            if not l.startswith('example'):
                continue
            if l.startswith('example :='):
                kind = 'witness-form'
            elif l.startswith('example :'):
                kind = 'typed'
            elif re.match(r'example\s*[\(\{\[⦃]', l):
                kind = 'binder'
            else:
                kind = 'other'
            nss = [n for t, n in stack if t == 'ns']
            ns = nss[-1] if nss else '-'
            j = i - 1
            while j >= 0 and L[j].startswith('open ') and L[j].rstrip().endswith(' in'):
                j -= 1
            doc = ''
            if j >= 0 and L[j].rstrip().endswith('-/'):
                d = j
                while d >= 0 and not L[d].lstrip().startswith('/-'):
                    d -= 1
                if d >= 0 and L[d].lstrip().startswith('/--'):
                    doc = ' '.join(L[d:j + 1])
            m = DOC.search(doc)
            e = i + 1
            while e < len(L) and L[e].startswith(' '):
                e += 1
            body = '\n'.join(L[i:e])
            proc = 'yes' if PROC.search(body) else 'no'
            rows.append((mod, i + 1, kind, ns, m.group(1) if m else '-', proc, l[:70]))
for r in rows:
    print('\t'.join(str(x) for x in r))
print('== TOTAL', len(rows))
print('== BY KIND', dict(Counter(r[2] for r in rows)))
print('== INSIDE A NAMESPACE', sum(1 for r in rows if r[3] != '-'),
      dict(Counter(r[2] for r in rows if r[3] != '-')))
print('== WITNESS-FORM WITHOUT A WITNESS DOCSTRING', [(r[0], r[1]) for r in rows if r[2] == 'witness-form' and r[4] == '-'])
print('== TYPED OR BINDER WITH A WITNESS DOCSTRING', len([r for r in rows if r[2] != 'witness-form' and r[4] != '-']),
      [(r[0], r[1], r[4]) for r in rows if r[2] != 'witness-form' and r[4] != '-'])
print('== MODULES WITH A WITNESS-FORM BLOCK', len({r[0] for r in rows if r[2] == 'witness-form'}))
print('== PROCESS yes, witness docstring', len([r for r in rows if r[5] == 'yes' and r[4] != '-']))
for r in rows:
    if r[5] == 'yes' and r[4] != '-':
        print('PROC\t' + '\t'.join(str(x) for x in r[:5]))
```

### `claim_scan2.py` (the wider claims scan, version 2; output `claim-scan-2.out`)

sha256 `f9a3a8f18c654456ba28eeac06fae872992321870cbc3c04e3ec966c39d092c7`, 3080 bytes.

```python
r"""Typed or binder examples (column 0, not `example :=`) by docstring claim words, widened list
(claude-ai, VACUITY-4 cut, 2026-10-25). Read-only.

Version 2: a raw docstring (no escape warning), and the docstring fixed as census_examples2.py fixes
it (a `/-!` or `/-` comment just above is not a docstring). Version 1's run: CLAIM 13, WIDE 7,
UNREAD-pattern lines 369 against 370 starting `example`.

usage: python3 -I claim_scan.py REPO_ROOT

PHRASE (the gate's TYPED-CLAIM list as the cut proposes it): 'hypotheses of', 'hypothesis of',
'can be met together', 'hold together'. WIDE: 'hypothes', 'witness', 'satisf', 'assumptions of',
'consistent', 'vacuous', 'inhabited', 'nonempty'. Prints CLAIM lines (a PHRASE matched), then WIDE
lines (a WIDE word, no PHRASE), each with module, line, the words and the docstring's first 160
characters; then the counts, and the UNREAD-pattern cross-check (lines matching
^\s*(@\[.*\]\s*)?(private |noncomputable )*example\b against lines starting `example`).

Predictions for version 2 (written before its run): CLAIM 13, as version 1; WIDE 6 (version 1's 7
without PrimitiveDivisor 401); UNREAD-pattern lines 369, lines starting `example` 370.
"""
import os
import re
import sys

root = sys.argv[1]
PHRASE = re.compile(r'hypotheses of|hypothesis of|can be met together|hold together', re.I)
WIDE = re.compile(r'hypothes|witness|satisf|assumptions of|consistent|vacuous|inhabited|nonempty', re.I)
UNREAD = re.compile(r'^\s*(@\[.*\]\s*)?(private |noncomputable )*example\b')


def doc_above(L, i):
    j = i - 1
    while j >= 0 and L[j].startswith('open ') and L[j].rstrip().endswith(' in'):
        j -= 1
    if j >= 0 and L[j].rstrip().endswith('-/'):
        d = j
        while d >= 0 and not L[d].lstrip().startswith('/-'):
            d -= 1
        if d >= 0 and L[d].lstrip().startswith('/--'):
            return ' '.join(L[d:j + 1])
    return ''


claim, wide = [], []
n_unread = n_col0 = 0
for dp, dn, fn in os.walk(os.path.join(root, 'ClassicalLean')):
    dn.sort()
    for f in sorted(fn):
        if not f.endswith('.lean'):
            continue
        p = os.path.join(dp, f)
        mod = os.path.relpath(p, root)[:-5].replace(os.sep, '.')
        L = open(p, encoding='utf-8').read().split('\n')
        for i, l in enumerate(L):
            if UNREAD.match(l):
                n_unread += 1
            if l.startswith('example'):
                n_col0 += 1
            if not l.startswith('example') or l.startswith('example :='):
                continue
            doc = doc_above(L, i)
            pm = sorted({m.group(0).lower() for m in PHRASE.finditer(doc)})
            wm = sorted({m.group(0).lower() for m in WIDE.finditer(doc)})
            row = f'{mod}\t{i + 1}\t{",".join(pm or wm)}\t{doc[:160]}'
            if pm:
                claim.append('CLAIM\t' + row)
            elif wm:
                wide.append('WIDE\t' + row)
print('\n'.join(claim))
print('\n'.join(wide))
print('== CLAIM', len(claim), 'WIDE', len(wide))
print('== UNREAD-pattern lines', n_unread, 'lines starting example', n_col0)
```

### `sweep_select4.py` (the sweep selection, version 4; its Lean file `SweepSelect4.lean`, output `sweep-select-4.out`)

sha256 `93815ff1fcdf393b26ba3dba81258c409cfc2a15292dc589174458bc57180258`, 4919 bytes.

```python
"""Write the Lean file that selects the process sweep's witnesses (claude-ai, VACUITY-4 cut, 2026-10-25).

usage: python3 -I sweep_select4.py REPO_ROOT CENSUS_OUT OUT.lean

Reads CENSUS_OUT (census_examples2.py's output) for every witness-form block with a docstring NAME.
For each, the candidates are NAME and N.NAME for every namespace N the module opens with a
`namespace` line (nested ones joined). Writes OUT.lean: `import ClassicalLean`, then a `run_cmd`
that, for each block, keeps the candidates that exist in the environment (`MISSING` or `AMBIGUOUS`
when not exactly one) and prints `SELECT` for the one theorem when its type (as stored, nothing
unfolded) uses one of the target constants or a constant whose name contains `exitTime` or
`hitTime` (`constants=`), or contains a limit along `ℕ` (`Filter.atTop` at `ℕ`: `natlimit=`), or
binds a variable that is not a proof and whose type is a function from `ℕ` (`natfn=`; the binders
as written, read with `forallTelescope`); `SKIP` otherwise. It also prints whether each target
exists. Refuses when OUT exists (exit 2).

History: version 1 (`sweep_select.py`) as drafted; version 2 counted only binders that are not
proofs (`isProp`); version 3 typed the counter `Nat` (version 2's file failed to elaborate, rc 1);
version 4, this one (the cut), replaces `MeasureTheory.hitting`, which this Mathlib does not have
(version 3's run: `TARGET MeasureTheory.hitting ABSENT`), by `hittingBtwn` and `hittingAfter`, adds
`Nat.iterate` and the limit along `ℕ` (version 3 skipped KalmanVariance's `tendsto_riccatiStep`),
and prints which constants matched.
"""
import os
import sys

root, census, out = sys.argv[1:4]
if os.path.exists(out):
    sys.exit(2)
rows = []
for line in open(census, encoding='utf-8'):
    f = line.rstrip('\n').split('\t')
    if len(f) == 7 and f[2] == 'witness-form' and f[4] != '-':
        rows.append((f[0], int(f[1]), f[4]))
ns_cache = {}


def namespaces(mod):
    if mod not in ns_cache:
        p = os.path.join(root, *mod.split('.')) + '.lean'
        stack, seen = [], []
        for l in open(p, encoding='utf-8').read().split('\n'):
            if l.startswith('namespace '):
                stack.append(l.split()[1])
                seen.append('.'.join(stack))
            elif l.startswith('end ') and stack and l.split()[1] == stack[-1]:
                stack.pop()
        ns_cache[mod] = sorted(set(seen))
    return ns_cache[mod]


TARGETS = ['MeasureTheory.Filtration', 'MeasureTheory.Martingale', 'MeasureTheory.Submartingale',
           'MeasureTheory.Supermartingale', 'MeasureTheory.IsStoppingTime', 'MeasureTheory.stoppedValue',
           'MeasureTheory.stoppedProcess', 'MeasureTheory.hittingBtwn', 'MeasureTheory.hittingAfter',
           'Nat.iterate']
items = []
for mod, ln, name in rows:
    cands = [name] + [f'{n}.{name}' for n in namespaces(mod)]
    items.append(f'("{mod}", {ln}, "{name}", [' + ', '.join(f'`{c}' for c in cands) + '])')
L = ['import ClassicalLean', '', 'open Lean Meta Elab Command in', 'run_cmd do', '  let env ← getEnv',
     '  let targets : List Name := [' + ', '.join(f'`{t}' for t in TARGETS) + ']',
     '  for t in targets do',
     '    logInfo m!"TARGET {t} {if env.contains t then "present" else "ABSENT"}"',
     '  let items : List (String × Nat × String × List Name) := [']
L += ['    ' + it + (',' if k < len(items) - 1 else '') for k, it in enumerate(items)]
L += ['  ]',
      '  let mut nsel : Nat := 0',
      '  for (m, ln, nm, cands) in items do',
      '    let found := cands.filter env.contains',
      '    match found with',
      '    | [c] =>',
      '      let some ci := env.find? c | pure ()',
      '      let used := ci.type.getUsedConstants',
      '      let viaC := used.filter fun u => targets.contains u ||',
      '        (u.toString.splitOn "exitTime").length > 1 || (u.toString.splitOn "hitTime").length > 1',
      '      let natLim := (ci.type.find? fun e =>',
      '        e.isAppOfArity ``Filter.atTop 2 && (e.getArg! 0).isConstOf ``Nat).isSome',
      '      let natFn ← liftTermElabM <| forallTelescope ci.type fun xs _ => do',
      '        let mut r := false',
      '        for x in xs do',
      '          let t ← inferType x',
      '          if t.isForall && t.bindingDomain!.isConstOf ``Nat && !(← isProp t) then r := true',
      '        return r',
      '      if !viaC.isEmpty || natLim || natFn then',
      '        nsel := nsel + 1',
      '        logInfo m!"SELECT {m} {ln} {c} constants={viaC.toList} natlimit={natLim} natfn={natFn}"',
      '      else logInfo m!"SKIP {m} {ln} {c}"',
      '    | [] => logInfo m!"MISSING {m} {ln} {nm}"',
      '    | _ => logInfo m!"AMBIGUOUS {m} {ln} {nm} {found}"',
      f'  logInfo m!"SWEEP-SELECT {{nsel}} of {len(items)} witness blocks with a docstring NAME"']
open(out, 'w', encoding='utf-8').write('\n'.join(L) + '\n')
print(out, len(items), 'blocks')
```

### `cut_facts4.sh` (review pass 1's checks; output `cut-facts-4.out`)

sha256 `9ae4be6d983c8f4d7bffe2368956a0e1caf2ebdddc5113ab7cc3797f55519c05`, 2297 bytes.

```bash
#!/usr/bin/env bash
# VACUITY-4 cut facts, part 4: review pass 1's checks (claude-ai, 2026-10-25). Run on DSMain as dustin:
#   bash /tmp/claude-ai-gate1/cut_facts4.sh > /tmp/claude-ai-gate1/cut-facts-4.out 2>&1
# Read-only in the repository; one Lean run (name_scope.py's file, importing ClassicalLean) under the
# 12 GB cap, only when no `lean` process runs and the build is current. Writes only under
# /tmp/claude-ai-gate1/.
set -u
R=$HOME/lean/classical-lean-paper-crypto
G=/tmp/claude-ai-gate1
export GIT_OPTIONAL_LOCKS=0 LC_ALL=C PATH=$HOME/.elan/bin:$PATH
cd "$R" || exit 2
echo "== start $(date '+%F %T %Z') head $(git rev-parse HEAD) porcelain-before $(git status --porcelain | wc -l)"
echo "== claim scan 3"; python3 -I $G/claim_scan3.py . > $G/claim-scan-3.out 2>&1; echo "rc=$?"; sha256sum $G/claim-scan-3.out; cat $G/claim-scan-3.out
echo "== git diff --name-only d21fd22 ac62f50"; git diff --name-only d21fd22 ac62f50; echo "outside records/: $(git diff --name-only d21fd22 ac62f50 | grep -vc '^records/')"
echo "== compile_rules.py: path lines"; grep -n "ClassicalLean\|rglob\|glob(\|os.walk\|tools\|rules.toml\|argv" tools/compile_rules.py | head -30
echo "== CLAIMS and INDEX: earlier pushes"; grep -o '.\{0,100\}[Pp]ushed .\{0,200\}' records/CLAIMS.md | tail -3; echo "--"; grep -o '.\{0,100\}[Pp]ushed .\{0,200\}' records/orders/INDEX.md | tail -3
echo "== claim_phrases.py"; sha256sum $G/claim_phrases.py
echo "== pgrep lean"; pgrep -ax lean; p=$?; echo "pgrep rc=$p"
if [ $p -eq 1 ]; then
  lake build --no-build > $G/nobuild-4.out 2>&1; nb=$?; echo "no-build rc=$nb $(tail -1 $G/nobuild-4.out)"
  if [ $nb -eq 0 ]; then
    python3 -I $G/name_scope.py . $G/NameScope.lean; echo "gen rc=$?"; sha256sum $G/NameScope.lean
    systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 /usr/bin/time -v nice -n 19 lake env lean -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3 $G/NameScope.lean > $G/name-scope.out 2>&1; echo "rc=$?"; sha256sum $G/name-scope.out
    grep -E 'Elapsed|Maximum resident|Exit status' $G/name-scope.out; grep -oE '(THEOREM|ALSO) .*' $G/name-scope.out; grep -c 'error' $G/name-scope.out
  fi
fi
echo "== porcelain-after $(git status --porcelain | wc -l) end $(date '+%F %T %Z')"
```

### `name_scope.py` (names in scope after each module's last line; its Lean file `NameScope.lean`, output `name-scope.out`)

sha256 `30a764888a49503beaebf90a139aafd274fb730b716322232c62891d8e42948b`, 4340 bytes.

```python
"""Write a Lean file that finds which short names of the theorems VACUITY-4 witnesses would resolve to
another constant after their module's last line (claude-ai, VACUITY-4 cut, review pass 1's m2,
2026-10-25). Read-only.

usage: python3 -I name_scope.py REPO_ROOT OUT.lean

For each (module, short name) below: the theorem is N.short for a namespace N that the module opens
with `namespace` lines (nested ones joined); the names the short form could also reach after the
module's last line are `short` itself (the root) and O.short for every namespace O that an `open`
line at column 0 opens outside every `namespace` and `section` (scoped, selective, hiding and
renaming forms skipped). The Lean file prints, for each, `THEOREM` with the existing candidates of
the first kind, and `ALSO` with the existing candidates of the second. Refuses when OUT exists.

Predictions (written before the run): every THEOREM line has exactly one name; ALSO is non-empty for
Superadditive's `map_zero` (Mathlib's root `map_zero`) and for 0 to 3 others.
"""
import os
import re
import sys

root, out = sys.argv[1:3]
if os.path.exists(out):
    sys.exit(2)
WORK = [('Algebra.Kantorovich', ['dotProduct_mulVec_mul_inv_le', 'dotProduct_mulVec_mul_inv_add_eq']),
        ('Algebra.MinMax', ['sum_mul_le_sum_of_antitone', 'sum_re_inner_le_sum_eigenvalues', 'sum_eigenvalues_eq_iSup']),
        ('Analysis.ConvexConjugate', ['convexConjugate_anti']),
        ('Geometry.Spectral3x3', ['gap_identity_of_offDiagCross_eq_zero']),
        ('InformationTheory.CompressionTest', ['integral_eFalseShare_score_le', 'integral_eFalseShare_score_le_mul_card_div']),
        ('Order.Superadditive', ['map_zero', 'monotone', 'linear_le', 'unbounded', 'pos_of_pos']),
        ('Probability.EffectiveSampleSize', ['variance_sum_eq_of_stationary', 'variance_sum_div_eq',
                                             'variance_sum_eq_mul_one_add', 'variance_sum_range_eq_of_stationary']),
        ('Probability.GamblersRuin', ['ae_exitTime_ne_top_of_biased', 'measureReal_hit_eq_of_biased',
                                      'measureReal_exists_ge_le_of_biased']),
        ('Probability.MaximalInequality', ['measureReal_exists_abs_ge_le', 'integral_sup_sq_le']),
        ('Statistics.GeneralizedLeastSquares', ['glsMatrix_ones_eq_minWeights'])]


def scan(mod):
    p = os.path.join(root, 'ClassicalLean', *mod.split('.')) + '.lean'
    stack, seen, opens = [], [], []
    for l in open(p, encoding='utf-8').read().split('\n'):
        if l.startswith('namespace '):
            stack.append(('ns', l.split()[1]))
            seen.append('.'.join(n for t, n in stack if t == 'ns'))
        elif l.startswith('section'):
            parts = l.split()
            stack.append(('sec', parts[1] if len(parts) > 1 else ''))
        elif l == 'end' or l.startswith('end '):
            parts = l.split()
            name = parts[1] if len(parts) > 1 else ''
            for k in range(len(stack) - 1, -1, -1):
                if stack[k][1] == name or (name == '' and stack[k][0] == 'sec'):
                    del stack[k:]
                    break
        elif l.startswith('open ') and not stack and not l.rstrip().endswith(' in'):
            ws = l.split()[1:]
            if ws and ws[0] != 'scoped':
                for w in ws:
                    if w in ('hiding', 'renaming') or w.startswith('('):
                        break
                    opens.append(w)
    return sorted(set(seen)), opens


items = []
for mod, shorts in WORK:
    nss, opens = scan(mod)
    for sh in shorts:
        thm = [f'{n}.{sh}' for n in nss]
        also = [sh] + [f'{o}.{sh}' for o in opens]
        items.append(f'("{mod}", "{sh}", [' + ', '.join(f'`{c}' for c in thm) + '], ['
                     + ', '.join(f'`{c}' for c in also) + '])')
L = ['import ClassicalLean', '', 'open Lean in', 'run_cmd do', '  let env ← getEnv',
     '  let items : List (String × String × List Name × List Name) := [']
L += ['    ' + it + (',' if k < len(items) - 1 else '') for k, it in enumerate(items)]
L += ['  ]',
      '  for (m, sh, thm, also) in items do',
      '    logInfo m!"THEOREM {m} {sh} {thm.filter env.contains}"',
      '    logInfo m!"ALSO {m} {sh} {also.filter env.contains}"']
open(out, 'w', encoding='utf-8').write('\n'.join(L) + '\n')
print(out, len(items), 'names')
```

### `cut_facts5.sh` (review pass 2's checks (runs `claim_scan4.py`, superseded, and `DottedName.lean`); output `cut-facts-5.out`)

sha256 `a1fc3a89428fc400006e22fc064d6de89c9346256fdfae907ab443aa9f549d61`, 1744 bytes.

```bash
#!/usr/bin/env bash
# VACUITY-4 cut facts, part 5: review pass 2's checks (claude-ai, 2026-10-25). Run on DSMain as dustin:
#   bash /tmp/claude-ai-gate1/cut_facts5.sh > /tmp/claude-ai-gate1/cut-facts-5.out 2>&1
# Read-only in the repository; one Lean run (DottedName.lean, importing ClassicalLean) under the 12 GB
# cap, only when no `lean` process runs and the build is current. Writes only under /tmp/claude-ai-gate1/.
set -u
R=$HOME/lean/classical-lean-paper-crypto
G=/tmp/claude-ai-gate1
export GIT_OPTIONAL_LOCKS=0 LC_ALL=C PATH=$HOME/.elan/bin:$PATH
cd "$R" || exit 2
echo "== start $(date '+%F %T %Z') head $(git rev-parse HEAD) porcelain-before $(git status --porcelain | wc -l)"
echo "== claim scan 4"; python3 -I $G/claim_scan4.py . > $G/claim-scan-4.out 2>&1; echo "rc=$?"; sha256sum $G/claim-scan-4.out; cat $G/claim-scan-4.out
echo "== claim scan 3 against 4 (CLAIM lines)"; diff <(grep '^CLAIM' $G/claim-scan-3.out) <(grep '^CLAIM' $G/claim-scan-4.out) && echo "CLAIM lines equal"
echo "== pgrep lean"; pgrep -ax lean; p=$?; echo "pgrep rc=$p"
if [ $p -eq 1 ]; then
  lake build --no-build > $G/nobuild-5.out 2>&1; nb=$?; echo "no-build rc=$nb $(tail -1 $G/nobuild-5.out)"
  if [ $nb -eq 0 ]; then
    sha256sum $G/DottedName.lean
    systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 /usr/bin/time -v nice -n 19 lake env lean -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3 $G/DottedName.lean > $G/dotted-name.out 2>&1; echo "rc=$?"; sha256sum $G/dotted-name.out
    grep -E 'Elapsed|Exit status' $G/dotted-name.out; grep -oE 'NAME .*' $G/dotted-name.out
  fi
fi
echo "== porcelain-after $(git status --porcelain | wc -l) end $(date '+%F %T %Z')"
```

### `DottedName.lean` (the dotted name's check; output `dotted-name.out`)

sha256 `9c81746d6a2dc06bc6bb163007f28c0ad1ac51fe7069912077c40f5f97b57ec3`, 491 bytes.

```lean
import ClassicalLean

-- VACUITY-4 cut, review pass 2 (claude-ai, 2026-10-25): does the dotted docstring name
-- `Superadditive.map_zero` reach only `ClassicalLean.Superadditive.map_zero` after the module's last line?
open Lean in
run_cmd do
  let env ← getEnv
  for n in [`Superadditive.map_zero, `Superadditive, `ClassicalLean.Superadditive.map_zero,
      `ClassicalLean.Superadditive.Superadditive.map_zero] do
    logInfo m!"NAME {n} {if env.contains n then "present" else "ABSENT"}"
```

### `claim_scan5.py` (blocks and claims as Lean reads them, version 5; output `claim-scan-5.out`, equal to `claim-scan-3.out`)

sha256 `f3ccb7f95adf149f3517bb4b548f5a3af2c07d8637e68af74476c5ca97bb1dfd`, 9351 bytes.

```python
r"""Blocks and claims as Lean reads them (claude-ai, VACUITY-4 cut, review passes 1 and 2, 2026-10-25).
Read-only.

usage: python3 -I claim_scan5.py REPO_ROOT

Version 5 of the claim scans. Version 4's run at `ac62f50` gave 8 false DOC-DIFF lines: going back
from a block, it took any `]` as the end of an attribute and jumped to the nearest earlier `@[` in
the file (CompanionMatrix 294 and NacciTrace 252 to 271 follow a block ending in `simp […]`); version
5 skips an attribute only when the `]` closes a bracket opened by `@[`, found by bracket matching
outside comments and strings. Version 4's changes over version 3 (claim_scan3.py) stand: char literals (`'"'`) and raw
strings (`r"…"`, `r#"…"#`) are masked as strings; going back from a block to its docstring also
skips `--` comments, plain `/- … -/` comments (Lean reads both as whitespace) and `set_option … in`
prefixes, and the modifiers `protected`, `unsafe`, `partial` and `nonrec`; CLAIM uses the gate's four
phrases ("hypotheses of", "hypothesis of", "can be met", "hold together"); the kind of a block is read
across line breaks.

For each module under ClassicalLean/, it marks comments (`--` to the end of the line; `/-` … `-/`,
nested) and strings (`"…"` with backslash escapes) outside comments. Every `example` keyword outside
them (no identifier character on either side) is a block, wherever it stands on its line. A block's
docstring is found as Lean attaches it: going back over whitespace (blank lines too), over
`private`, `noncomputable` and `@[…]` before the keyword, and over whole `open … in` prefixes, the
text just before must close a block comment that opened with `/--`. Phrases and words are matched
after the docstring's whitespace is collapsed to single spaces.

It prints, one per line: NOT-AT-COL0 (a block whose keyword is not at column 0, or has other code
before it on its line); COMMENT-MATCH (a line matching the UNREAD pattern whose `example` is inside
a comment or string); DOC-DIFF (a column-0 block whose docstring by this rule differs from the line
rule of claim_scan2.py); WITNESS-NO-DOC (a witness-form block with no docstring "The hypotheses of
`NAME` hold together"); CLAIM (a typed or binder block whose docstring has one of the four phrases);
MET (a docstring with "can be met"); WIDE (a wider word and no phrase); then the counts.

Predictions for version 5 (written before its run): the same as version 3's run at `ac62f50`:
blocks 369, all at column 0; NOT-AT-COL0 0; COMMENT-MATCH 0; DOC-DIFF 0; WITNESS-NO-DOC 2 (MinMax
443, PrimitiveDivisor 423); CLAIM 13, the same 13; MET 4; WIDE 6.
"""
import os
import re
import sys

root = sys.argv[1]
PHRASE = re.compile(r'hypotheses of|hypothesis of|can be met|hold together', re.I)
MET = re.compile(r'can be met', re.I)
WIDE = re.compile(r'hypothes|witness|satisf|assumption|consistent|vacuous|inhabited|nonempty|condition|'
                  r'premise|jointly|simultaneous|compatible|realiz|can be met', re.I)
WDOC = re.compile(r'The hypotheses of `([^`]+)` hold together')
UNREAD = re.compile(r'^\s*(@\[.*\]\s*)?(private |noncomputable )*example\b')
KW = re.compile(r"(?<![\w.'!?])example(?![\w'!?])")
CHAR = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^'\\\n])'")
RAW = re.compile(r'r(#*)"')


def ident(c):
    return c.isalnum() or c in "_'!?."


def mask(s):
    n = len(s)
    kind = bytearray(b' ' * n)
    spans = {}
    i = 0
    while i < n:
        if s.startswith('--', i):
            j = s.find('\n', i)
            j = n if j < 0 else j
            kind[i:j] = b'c' * (j - i)
            i = j
        elif s.startswith('/-', i):
            start, depth, isdoc = i, 0, s.startswith('/--', i)
            while i < n:
                if s.startswith('/-', i):
                    depth += 1
                    i += 2
                elif s.startswith('-/', i):
                    depth -= 1
                    i += 2
                    if depth == 0:
                        break
                else:
                    i += 1
            kind[start:i] = b'c' * (i - start)
            spans[i] = (start, isdoc)
        elif s[i] == "'" and (i == 0 or not ident(s[i - 1])) and CHAR.match(s, i):
            j = CHAR.match(s, i).end()
            kind[i:j] = b's' * (j - i)
            i = j
        elif s[i] == 'r' and (i == 0 or not ident(s[i - 1])) and RAW.match(s, i):
            m = RAW.match(s, i)
            close = '"' + m.group(1)
            j = s.find(close, m.end())
            j = n if j < 0 else j + len(close)
            kind[i:j] = b's' * (j - i)
            i = j
        elif s[i] == '"':
            start = i
            i += 1
            while i < n and s[i] != '"':
                i += 2 if s[i] == '\\' else 1
            i += 1
            kind[start:i] = b's' * (i - start)
        else:
            i += 1
    return kind, spans


def doc_lean(s, kind, spans, pos):
    j = pos
    while True:
        k = j
        while k > 0 and s[k - 1].isspace():
            k -= 1
        if k == 0:
            return ''
        before = s[s.rfind('\n', 0, k) + 1:k]
        m = re.search(r'(?:(?<![\w.])(?:private|protected|noncomputable|unsafe|partial|nonrec))$', before)
        if m and kind[k - 1] == 32:
            j = k - len(before) + m.start()
            continue
        if s[k - 1] == ']' and kind[k - 1] == 32:
            p, depth = k - 1, 0
            while p >= 0:
                if kind[p] == 32 and s[p] == ']':
                    depth += 1
                elif kind[p] == 32 and s[p] == '[':
                    depth -= 1
                    if depth == 0:
                        break
                p -= 1
            if p > 0 and s[p - 1] == '@':
                j = p - 1
                continue
            return ''
        m = re.search(r'(?<![\w.])(?:open|set_option)\b[^\n]*(?<![\w.])in$', before)
        if m and kind[k - 1] == 32:
            j = k - len(before) + m.start()
            continue
        if s[k - 2:k] == '-/' and k in spans:
            start, isdoc = spans[k]
            if isdoc:
                return s[start:k]
            if s.startswith('/-!', start):
                return ''
            j = start
            continue
        if kind[k - 1] == ord('c'):
            a = k - 1
            while a > 0 and kind[a - 1] == ord('c') and s[a - 1] != '\n':
                a -= 1
            j = a
            continue
        return ''


def doc_line(L, i):
    j = i - 1
    while j >= 0 and L[j].startswith('open ') and L[j].rstrip().endswith(' in'):
        j -= 1
    if j >= 0 and L[j].rstrip().endswith('-/'):
        d = j
        while d >= 0 and not L[d].lstrip().startswith('/-'):
            d -= 1
        if d >= 0 and L[d].lstrip().startswith('/--'):
            return ' '.join(L[d:j + 1])
    return ''


def squash(x):
    return re.sub(r'\s+', ' ', x)


out = {k: [] for k in ('NOT-AT-COL0', 'COMMENT-MATCH', 'DOC-DIFF', 'WITNESS-NO-DOC', 'CLAIM', 'MET', 'WIDE')}
nblocks = 0
for dp, dn, fn in os.walk(os.path.join(root, 'ClassicalLean')):
    dn.sort()
    for f in sorted(fn):
        if not f.endswith('.lean'):
            continue
        p = os.path.join(dp, f)
        mod = os.path.relpath(p, root)[:-5].replace(os.sep, '.')
        s = open(p, encoding='utf-8').read()
        L = s.split('\n')
        kind, spans = mask(s)
        starts = [0]
        for ln in L[:-1]:
            starts.append(starts[-1] + len(ln) + 1)
        for li, ln in enumerate(L):
            m = UNREAD.match(ln)
            if m:
                at = starts[li] + ln.index('example', m.start())
                if kind[at] != 32:
                    out['COMMENT-MATCH'].append(f'{mod}\t{li + 1}\t{ln[:100]}')
        for m in KW.finditer(s):
            if kind[m.start()] != 32:
                continue
            nblocks += 1
            li = s.count('\n', 0, m.start())
            col = m.start() - starts[li]
            line = L[li]
            if col != 0 and line[:col].strip() != '':
                out['NOT-AT-COL0'].append(f'{mod}\t{li + 1}\t{line[:100]}')
            elif col != 0:
                out['NOT-AT-COL0'].append(f'{mod}\t{li + 1}\t(indented)\t{line[:100]}')
            rest = s[m.end():m.end() + 200].lstrip()
            kindb = 'witness-form' if rest.startswith(':=') else 'typed' if rest.startswith(':') else 'binder'
            dl = squash(doc_lean(s, kind, spans, m.start()))
            if col == 0:
                dd = squash(doc_line(L, li))
                if dd.strip() != dl.strip():
                    out['DOC-DIFF'].append(f'{mod}\t{li + 1}\tline-rule={dd[:60]!r}\tlean-rule={dl[:60]!r}')
            if kindb == 'witness-form':
                if not WDOC.search(dl):
                    out['WITNESS-NO-DOC'].append(f'{mod}\t{li + 1}')
                continue
            if MET.search(dl):
                out['MET'].append(f'{mod}\t{li + 1}\t{dl[:120]}')
            if PHRASE.search(dl):
                out['CLAIM'].append(f'{mod}\t{li + 1}\t{dl[:120]}')
            elif WIDE.search(dl):
                w = sorted({x.group(0).lower() for x in WIDE.finditer(dl)})
                out['WIDE'].append(f'{mod}\t{li + 1}\t{",".join(w)}\t{dl[:140]}')
for k, v in out.items():
    for x in v:
        print(k + '\t' + x)
print('== BLOCKS', nblocks, ' '.join(f'{k} {len(v)}' for k, v in out.items()))
```

### Superseded, not reproduced

In `/tmp/claude-ai-gate1/` on DSMain, by sha256 only: `claim_phrases.py` (an earlier helper that
`cut_facts.sh` runs; four lines, superseded by the claim scans)
`91e6a997be59deb5de2ed943878df31ecda70042a1da8a870a02e4ecddd4f3de`; `claim_scan.py` (version 1: it took a section
comment's earlier docstring) `6e251f4a5b750c00103cef973081820b3639b1cdc10a6e87fb8a400ccd3d48bc`;
`sweep_select.py` (version 1, never run) `5a54b1aef4b9c2f8c562456db638ce451eed9f0ba289d5f8efb88856e72aa735`;
`sweep_select2.py` (its Lean file failed, rc 1)
`eca7698df6f13a94a800d6cf7412c52981175d97468122fa23f28177584f6b6a`; `claim_scan3.py` (version 3, run by
`cut_facts4.sh`; its output equals version 5's) `758da477e65eada41c0016d9cf29ced84befb355f272bf3b53a80ed8631ee044`;
`claim_scan4.py` (version 4, run by `cut_facts5.sh`; its attribute bug gave 8 false DOC-DIFF lines)
`d02cb61a3203e2cd8f32d38d77df139fed2f5558bb594506805d6c3d5bd89c58`; `sweep_select3.py` (42 selected,
`MeasureTheory.hitting` absent) `67c5efc0d7239b8110c4b8fc3f8e86e1f71358bf4171817cd8cf6e34aa152865`.
