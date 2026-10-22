# Round 71 — batch 4 of the API-credit drafts, VACUITY-3 row 70 and bridge row 163 (order LEAN-34)

Session: Claude Code `session_01SYJof36hVcDcFdNyijRw19` on DSMain, as dustin, executing order
`LEAN-34` (`records/orders/20261021T222500Z__claude-ai__order-lean34-karlin-rubin-sanov-durbin-levinson-pca-bretagnolle-huber-bsc-cascade.md`,
written by claude-ai, copied verbatim; lane `lean/LEAN-34/order.md`, sha256
`b4869d7c17cfc1d92750b39c424019346770dfaf880680f074f8736fe66b02dd`), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `lean-34`, made from `origin/master` = `02ac649`
(MERGE-3's last commit, equal to `git ls-remote github master`). Lean and Mathlib v4.34.0. Nothing
pushed. Evidence: `~/lean/lean34-checks/` (outside the repository), `evidence.log` (UTC time,
label, rc, prediction, command per run; `COMMIT <hash>` marker lines). Plan: lane
`lean/LEAN-34/plan.md` (sha256 `86e3d731a28f42c8d5df7ae3222aabb90dc277c929df959afb5bc73583c51dbe`),
approved by Dustin on 2026-10-21 (EDT evening); the first Setup 1 line of `evidence.log` is at
2026-10-21T22:18:57Z.

Dustin's decisions with the approval (saved as `~/lean/lean34-checks/pre/dustin-approval.md`):
(1) row 70: `lean/LEAN-34/data/w70.lean`'s block; (2) row 163: the last job, in its own commit;
(3) NeymanPearson's module docstring: one dated sentence is added after "(Dustin's ruling, order
LEAN-24)." in the section "The limit of item 56", dated with the UTC date of the commit that adds
it, saying item 118 proves the textbook form; nothing else in that paragraph changes, and the
documents review checks it. claude-ai's answers with the approval: the cut's hash of HANDOFF.md
section 4's "Satisfiability witnesses" paragraph was taken over lines 932 to 980 with one leading
space per line (reproduced here: label `handoff-para-hash`, `ecb72ac5…`, beside the raw lines'
`1ae9c230…`); no new allowlist line is predicted on either `el.sh` test run; item 118's `hsize`
counterexample, checked by claude-ai in exact arithmetic, goes to job 1's statement reviewer as a
claim to check.

First part written before the work; completed after it, below.

## Files this round changes

Module files (no module is added):

* items 118 and 144: `ClassicalLean/Statistics/NeymanPearson.lean` (new import line
  `import ClassicalLean.InformationTheory.Entropy`);
* item 122: `ClassicalLean/InformationTheory/MethodOfTypes.lean`;
* item 140: `ClassicalLean/Probability/YuleWalker.lean`;
* item 142: `ClassicalLean/Probability/CovarianceDirections.lean` (new import line
  `import ClassicalLean.Algebra.MinMax`);
* VACUITY-3 row 70: `ClassicalLean/Analysis/FiniteGame.lean`;
* bridge row 163: `ClassicalLean/InformationTheory/ChannelCapacity.lean` (new import line
  `import ClassicalLean.Probability.TwoStateChain`).

Also changed: `records/CLAIMS.md` and `records/orders/INDEX.md` (this order's rows appended at the
bottom, and MERGE-3's push recorded in MERGE-3's two rows), this fragment, the order's copy,
`HANDOFF.md` sections 1 and 4, `ROADMAP.md` (section 1.28), the new bridge baseline
`records/bridges/LEAN-34/`, and `tools/vacuity_reviewed.txt` only if a helper is listed. No other
`.lean` file, no other import line, nothing else under `tools/`, `.github/` or
`records/rules.toml`; `HANDOFF.md` section 6 untouched.

## Order MERGE-3's push

By records/README.md rule 2 ("the next order's records commit appends the push of the order before
it to that order's INDEX row and CLAIMS row"), this round's first commit inserts into MERGE-3's
INDEX row (after ``one bridge found (row 163, lane `MATH-PLAN-library-2-bridges-2.md`)``, before its
commits cell) and its CLAIMS row (before the final ` |`) the text ``; pushed by Dustin: DSMain's
master ref written 2026-10-21 15:42:20 EDT, GitHub master equal (`02ac649`)``, as the order's cut
measured it, by the script `evidence/pushnote.py` (MERGE-3's, adapted), which asserts the text
after each anchor before inserting and runs before anything is appended.

Records files written by this session's commands, not by the evidence helper (HANDOFF.md rule 23):
the order's copy (by `evidence/lanecopy.py`, which reads the lane file and checks the copy's
sha256, through `ev.sh --nolean`, label `records1`), this fragment, the INDEX row and the CLAIMS
row (written with the Write tool into the evidence folder, hashed by `hl.sh`, and copied or
appended by `records1.sh` through `ev.sh --nolean`, label `records1`).

## Completed after the work (2026-10-22 UTC)

### What landed (one commit per module, then row 70 and row 163)

| commit | what | review | confirming pass |
|---|---|---|---|
| `6684c41` | records first (this fragment's first part, the order's copy, the INDEX and CLAIMS rows, MERGE-3's push) | | |
| `26acca8` | item 140, `ClassicalLean/Probability/YuleWalker.lean`: `durbinLevinson_spec` (helper `pos_of_pred`), FAITHFUL | (c): FAIL, 1 BLOCKER (the landed witness was cut short, a partial application that still elaborated: the session's mistake) and 2 MINOR, fixed | (cc): CONFIRMED WITH FINDINGS (5 MINOR on the new witness check, answered by its version 2) |
| `06b7135` | items 118 and 144, `ClassicalLean/Statistics/NeymanPearson.lean`: `HasMonotoneLikelihoodRatio'`, `isUniformlyMostPowerful_of_monotoneLikelihoodRatio'` (helpers `isLRTest_thresholdTest'`, `thresholdTest_mul_eq_zero'`), `size_add_one_sub_power_ge`, both FAITHFUL; new import line `import ClassicalLean.InformationTheory.Entropy`; Dustin's dated sentence in the section on the limit of item 56, dated 2026-10-21 UTC (the commit's UTC date: 2026-10-21 23:06:12) | (a): PASS WITH FINDINGS, 4 MINOR: 1 fixed, 3 answered | (ac): CONFIRMED WITH FINDINGS (2 MINOR on these records) |
| `6461f95` | item 142, `ClassicalLean/Probability/CovarianceDirections.lean`: `isSymmetric_covLin`, `sum_variance_mix_le_sum_eigenvalues`, GENERALIZED (any finite measure); new import line `import ClassicalLean.Algebra.MinMax` | (d): PASS WITH FINDINGS, 4 MINOR: 3 fixed with their delta check, 1 on the brief | (dc): CONFIRMED |
| `1ce0c4d` | item 122, `ClassicalLean/InformationTheory/MethodOfTypes.lean`: `le_measureReal_empirical_eq` (def `cnt`, helpers `typeCount_cons`, `prod_eq_prod_pow_typeCount_nat`, `pow_mul_factorial_le`, `cnt_mul_prod_factorial`, `cnt_mul_le`, `pow_le_card_types`), GENERALIZED (`p ≥ 0` only) | (b): PASS WITH FINDINGS, 5 MINOR: 2 fixed, 3 outside the Scope (follow-ups) | (bc): CONFIRMED |
| `6c76665` | VACUITY-3 row 70, `ClassicalLean/Analysis/FiniteGame.lean`: old lines 970 to 979 replaced by `lean/LEAN-34/data/w70.lean`'s block, byte for byte | (e): PASS WITH FINDINGS, 1 optional MINOR, answered | (ec): CONFIRMED |
| `c83337c` | bridge row 163, `ClassicalLean/InformationTheory/ChannelCapacity.lean`: `mutualInfo_bsc_pow_le`, `mutualInfo_bsc_pow_half`, `tendsto_capacity_bsc_pow` (helpers `twoStateMatrix_pow_apply`, `crossover_pow_mem_Icc`), all FAITHFUL; new import line `import ClassicalLean.Probability.TwoStateChain` | (f): PASS WITH FINDINGS, 2 MINOR, fixed | (fc): CONFIRMED |
| `1058501` | documents: `HANDOFF.md` sections 1 and 4, `ROADMAP.md` section 1.28 (G) | documents review: PASS WITH FINDINGS, 3 MINOR, fixed; Dustin's sentence: PASS | (docsc): CONFIRMED WITH FINDINGS (1 optional note, a follow-up) |
| `9ef33f0` | records: the bridge baseline `records/bridges/LEAN-34/` | | |

Job 1's statement review: PASS WITH FINDINGS, 0 BLOCKER, 2 MAJOR (two of 122's helpers were
Mathlib's: `consEquiv'` is `Fin.consEquiv`, `prod_le_prod_nat` is `Finset.prod_le_prod`; both
dropped, the Mathlib names used), 4 MINOR, all answered; the claim that 118's `hsize` is needed was
confirmed in Lean by the reviewer. Its confirming pass: CONFIRMED WITH FINDINGS, one MINOR: the probe
`p-d122-r2` is a type check of the two Mathlib names, not a probe of the replacement (the reviewer's
own probe ran the replaced steps).

Credit (rule 19): items 118, 122, 140, 142 and 144: the drafts `d118-r1-s1`, `d122-r5-s1`,
`d140-r1-s2`, `d142-r1-s2`, `d144-r1-s1`, written by Claude Opus 5.5 through the Anthropic Batch
API (the lane's API-CREDIT-1 work), adapted by this session; row 70's block: claude-ai, after
VACUITY-3's fresh reviewer's suggested fix; row 163: statements by claude-ai, from the bridges
file's row, proofs by this session. Each proof change against its draft is in its commit message
and in the module docstring's entry.

Theorem-constant counts per module (census of the final module copies under the axiom gate's
`.thmInfo` predicate, rule 27; labels `census_<Module>_new_thm`), auxiliaries included:
`Statistics/NeymanPearson` 23 (+4), `InformationTheory/MethodOfTypes` 41 (+19),
`Probability/YuleWalker` 28 (+17), `Probability/CovarianceDirections` 45 (+2),
`Analysis/FiniteGame` 60 (+0), `InformationTheory/ChannelCapacity` 12 (+5); total +47.

### The gates, on the clean tree at G `1058501` (predicted in `pred/pred-main.md`, hashed first)

| run | predicted | measured |
|---|---|---|
| g1-build | rc 0, 4193 jobs, 0 warnings | rc 0, 4193 jobs, 0 warnings |
| g2-axiom | PASS 3574 | PASS 3574 |
| g3-vacuity | PASS, 1 reviewed helper, 0 VACUOUS-PENDING | the same |
| g3-tests | 89, 47 flagged, 0 mismatches | 89 tests, 47 flagged, 0 rule-5 run-outs, 0 mismatches |
| g4-sorry | PASS 140 | PASS 140 |
| g5-records | PASS 140, 106 files | PASS 140, 106 files |
| g6-drift | PASS | PASS |
| g6-banned | PASS, 140 + root, 0 hits | the same |
| g7 | ALL PASSED, 4193, 140 modules 0 failed, 3574, three axioms, planted fault named | ALL PASSED for `1058501`, 23:19.71 wall clock |
| g-modcount | MODULES 5729 | MODULES 5729 (ClassicalLean 141) |
| td-after | 4058 records (3574 thm, 484 def) | the same, elided 0, missing_fields 0 |
| td-diff | removed 0, added 49, changed 0, proof_only 0 | the same; the 49 ADDED names equal the census's (label `td-added-cmp`) |

The bridge search (at G, through `rootrun.sh`): rc 1; 66 new pairs, 12 new shapes, 29 gone pairs
against `records/bridges/MERGE-3/`; inside the hand prediction. One real bridge, appended to the
lane's bridges file as row 164 (a Pinsker bound for tests: `InformationTheory/Channel`'s Pinsker
inequality with item 144's setting); the file says how the other keys were checked. The report tool
(at `9ef33f0`, whose tree differs from G only in `records/`): 1981 written theorems; A 1180; B 801;
C 37, 0 recursive; self-test mismatches 0; no `CLOSES` line names a theorem of this order.

### The witness check (version 2 of `evidence/mkwitcheck.py`; lane `lean/LEAN-34/data/mkwitcheck.py`)

Before each module commit, every witness of the module was OK. Once over the library after the
gates (Dustin's instruction; evidence only): 145 of 145 `example :=` witnesses checked, in 70
modules; their verdicts: 137 OK, 4 BROKEN (FrankWolfe 1, PolyaUrn 3: their witnesses use the
modules' private lemmas, which a separate check file cannot name), 1 WRONG-NAME (PrimitiveDivisor
line 423, a name-resolution check, not a satisfiability witness), and Algebra/MinMax's 3 got no
verdict because its check file did not elaborate (its examples lie inside the namespace). All four
are blind spots of the check, not faults found in those modules. 219 typed examples were not read
by the script, 9 of them ∃-form witnesses, left for the gate order to decide.

### Misses, follow-ups and notes

- The cut witness of item 140 (review (c)'s BLOCKER), and my prediction of the line it would land
  after (295 for 296), which nothing compared.
- Setup 1: one `ev.sh` run with relative paths that changed nothing (`adapt-commit`, redone as
  `adapt-commit-2`); `commit.sh`'s session trailer changed to this session, beyond the listed
  path lines (logged).
- Probes found missing at elaboration and then run: `Equiv.left_inv` and `Equiv.right_inv`
  (`stmt-122` refused once); `LE.le.lt_or_eq`, `LE.le.lt_of_ne`, `LE.le.trans_eq`; `push_neg`,
  `_ℝ` and `all_goals` added to the allowlist with reasons; the w70 block's names (`Kernel.const`,
  `Kernel.id`) were not probed before its landing (`el-fg-1` refused, `NOT RUN`).
- Line-count predictions in labels that missed: 34 for 37 (`land-142-insert`), 14 for 11
  (`land-163-move`).
- Hand predictions that missed: the census (about 20 new theorem constants for 47, the
  auxiliaries); the report tool's B (+1 for +4) and C (36 for 37).
- Commands outside the evidence helper: one inline parse check of `mkwitcheck.py`; one run of
  `evidence/mk163.py` (its inputs and output then hashed, label `land-163-files`).
- Row 163's limit uses the direct route the order's cut lists (`tendsto_pow_atTop_nhds_zero_of_abs_lt_one`,
  `Real.binEntropy_continuous`, `Real.binEntropy_two_inv`), not `tendsto_vecMul_pow_apply_one`,
  which the Goal list and the bridges row's rests-on column name (review (f)'s note).
- Records notes from review (ac): the answer to review (a)'s finding 3 said the paragraph was
  untouched apart from the inserted sentence, when its line breaks also moved; and an `el.sh`
  output that holds only `rc=0` is how this record's phrase no message is measured.
- Follow-ups for a later order, outside this order's Scope: in
  `ClassicalLean/InformationTheory/MethodOfTypes.lean`'s module docstring, the title (upper bound
  only), the proof paragraph (upper bound only), the Hypotheses section (no line for item 122) and
  the Mathlib list (eight names the new proof uses); in
  `ClassicalLean/Statistics/NeymanPearson.lean`'s list entry for `size_add_one_sub_power_ge`, the
  hypothesis `hsupp`.
- A note for claude-ai: `w70.lean`'s docstring writes `2 · dirac 0` with a middle dot where Lean's
  scalar multiplication is `•`; the block was kept byte for byte.
