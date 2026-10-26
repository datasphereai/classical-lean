# Round 73 — the witness gate, the older witnesses brought to rule 2, and the gate leftovers (order VACUITY-4)

Session: Claude Code `session_01CaiSGfxRa9So88se5LzGkG` on DSMain, as dustin, executing order
`VACUITY-4` (`records/orders/20261026T024100Z__claude-ai__order-vacuity4-witness-gate-older-witnesses-gate-leftovers.md`,
written by claude-ai, copied verbatim; lane `lean/VACUITY-4/order.md`, sha256
`68996aadffdc8660aa569344d1769453d4b035e49216a2fe8509d3b6936fd1b1`), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `vacuity-4`, made from `origin/master` = `ac62f50`
(LEAN-35's last commit, equal to `git ls-remote github master`). Lean and Mathlib v4.34.0. Nothing
pushed. Evidence: `~/lean/vacuity4-checks/` (outside the repository), `evidence.log` (UTC time,
label, rc, prediction, command per run; `COMMIT <hash>` marker lines). Plan: lane
`lean/VACUITY-4/plan-r2.md` (sha256 `90fde810a569bd846bd1a90b81fb243585a59968daca6e1187c493aeb0cea1d3`;
it replaces `lean/VACUITY-4/plan.md`, sha256
`991bfd960eb8c45b03460b66cd48733c8909f3838cd0bcb44c445c9d5fc18d39`), approved by Dustin on
2026-10-25 (EDT evening) with claude-ai's five rulings (lane `lean/VACUITY-4/ruling-1.md`, sha256
`accee2804ff50f7e3c4ad4318fb6ad9ca8cb37a6ae01b70f0db49b9d83fab173`); both saved in
`~/lean/vacuity4-checks/pre/` (label `approval`); the first line of `evidence.log` is at
2026-10-26T02:38:01Z.

The rulings, in short: (1) the plan's lane reads outside the connector are accepted, and every later
lane read and copy goes through the connector; (2) the Scope widens for exactly the pointer sentences
plan r2 lists (and any a Job 3 witness would make false the same way), each pointing at a witness by
its theorem, never by its place; (3) MaximalInequality's two re-witnesses at one step (`n = 1`),
after the two theorems' statements are probed; (4) the gate compares its docstring reading with
Lean's (`DOC-MISMATCH`), and a fixture compares the two on each layout before review (a); (5) the
rest of the plan stands.

First part written before the work; completed after it, below.

## Files this round changes

Module files (no module is added; only `example` blocks, their docstrings and `open … in` lines,
and the sentences of ruling 2):

* `ClassicalLean/Order/Superadditive.lean` (the typed claim at line 116 replaced by five witnesses);
* `ClassicalLean/Geometry/Spectral3x3.lean` (the typed claim at line 175);
* `ClassicalLean/Analysis/ConvexConjugate.lean` (the typed claim at line 126);
* `ClassicalLean/Statistics/GeneralizedLeastSquares.lean` (the typed claim at line 261);
* `ClassicalLean/Algebra/Kantorovich.lean` (the typed claims at lines 216 and 225);
* `ClassicalLean/Algebra/MinMax.lean` (the typed claims at lines 427 and 434; the witness-form block
  at line 443 moved after the module's last line);
* `ClassicalLean/InformationTheory/CompressionTest.lean` (the typed claim at line 462);
* `ClassicalLean/Probability/LongestRun.lean` (the typed claim at line 268 removed; its theorem has a
  witness; ruling 2's sentences);
* `ClassicalLean/Probability/EffectiveSampleSize.lean` (the typed claims at lines 583 and 595;
  ruling 2's sentences);
* `ClassicalLean/Probability/GamblersRuin.lean` (the typed claim at line 1046; ruling 2's
  sentences);
* `ClassicalLean/Probability/MaximalInequality.lean` (the witnesses at lines 697 and 736 re-witnessed
  under rule 3's case of the moving process).

Listed, not changed: `ClassicalLean/NumberTheory/PrimitiveDivisor.lean` (its line 423, a
name-resolution check, listed in `tools/witness_reviewed.txt` as `NO-DOCSTRING`).

A module that the gate's first library run or the process sweep adds is named in the follow-up edit,
with the run or review that added it.

Also: the new `tools/witness_gate.py`, `tools/witness_gate_tests.py`, `tools/witness-fixtures/` and
`tools/witness_reviewed.txt`; `tools/UninformativeReport.lean` (its one `set_option maxHeartbeats`
line), `tools/VacuityGate.lean` (FAIL text strings and comments only), `.github/workflows/ci.yml`
(one step, if the gate's time allows); `HANDOFF.md` sections 1 and 4; `records/CLAIMS.md` and
`records/orders/INDEX.md` (this order's rows appended at the bottom, and LEAN-35's push recorded in
LEAN-35's two rows), this fragment and the order's copy. No declaration, no import line, no other
file under `tools/`, nothing in `records/rules.toml`, the lake files or `lean-toolchain`; `HANDOFF.md`
sections 0, 2, 3, 5 and 6 untouched.

## Order LEAN-35's push

By records/README.md rule 2 ("the next order's records commit appends the push of the order before
it to that order's INDEX row and CLAIMS row"), this round's first commit inserts into LEAN-35's
INDEX row (after ``one bridge found (row 165, lane `MATH-PLAN-library-2-bridges-2.md`)``, before its
commits cell) and its CLAIMS row (before the final ` |`) the text ``; pushed by Dustin: DSMain's
master ref written 2026-10-25 09:08:03 EDT, GitHub master equal (`ac62f50`)``, by the script
`evidence/pushnote.py` (LEAN-35's, adapted), which asserts the text after each anchor before
inserting and runs before anything is appended. The time is the mtime of
`/data/git/classical-lean.git/refs/heads/master`, which holds `ac62f505db03edda95e7f7fa83a301a07ddda924`,
read again by this session (label `pushref`).

Records files written by this session's commands, not by the evidence helper (HANDOFF.md rule 23):
the order's copy (written from the connector's reply by `evidence/replyextract.py`, its sha256
checked, and copied into the tree by `evidence/records1.sh` through `ev.sh --nolean`, label
`records1`), this fragment, the INDEX row and the CLAIMS row (written with the Write tool into the
evidence folder, hashed by `hl.sh`, and copied or appended by `records1.sh` through `ev.sh --nolean`,
label `records1`).

## Completed after the work (2026-10-26 UTC)

### What landed (one commit per module or leftover, then the documents)

| commit | what | review | confirming pass |
|---|---|---|---|
| `661a181` | records first (this fragment's first part, the order's copy, the INDEX and CLAIMS rows, LEAN-35's push) | | |
| `7515a48` | Job 1: `tools/witness_gate.py`, `tools/WitnessListing.lean` (the listing driver), `tools/witness_gate_tests.py`, `tools/witness-fixtures/` (117 cases), `tools/witness_reviewed.txt` (empty); committed locally before its last review, as ruling 4 section 4 directs | (a) five rounds and two confirming passes before it (below) | |
| `fa45254` | Job 1: review (a) round 5's four MINOR points fixed (the configuration item `native` refused before elaboration, `mutual` stated as refused, fixture c110's reason, the docstrings' account of the inner list); fixtures c118 and c119; 119 cases | (a) round 5: CONFIRMED WITH FINDINGS, no false `WITNESSGATE PASS` measured, 4 MINOR | (a4c), after a heads-up during Job 6: NOT CONFIRMED, A1 MAJOR (a module's own code can run in a tactic branch the elaborator discards, and the gate passes it), A2 MINOR; stopped; ruling 6 states it as a limit (`7ebda52`) |
| `b6af448` | `ClassicalLean/Order/Superadditive.lean`: five rule-2 witnesses (`f n = n * n`), the identity's typed claim removed | (b) group 1: CONFIRMED WITH FINDINGS, 2 MINOR | (b1c): CONFIRMED |
| `4e4e2bb` | `ClassicalLean/Geometry/Spectral3x3.lean`: a witness of `gap_identity_of_offDiagCross_eq_zero` | (b) group 1 | (b1c) |
| `b10a18f` | `ClassicalLean/Analysis/ConvexConjugate.lean`: a witness of `convexConjugate_anti`, with the strictly convex pair review (b) group 1's finding 1 gave | (b) group 1, finding 1 fixed | (b1c): CONFIRMED |
| `dd135c6` | `ClassicalLean/Statistics/GeneralizedLeastSquares.lean`: a witness of `glsMatrix_ones_eq_minWeights` | (b) group 1 | (b1c) |
| `91e997a` | `ClassicalLean/Algebra/Kantorovich.lean`: witnesses of the two Kantorovich theorems | (b) group 2: CONFIRMED WITH FINDINGS, 1 MAJOR, 3 MINOR | (b2c): CONFIRMED |
| `0fa3003` | `ClassicalLean/Algebra/MinMax.lean`: two witnesses; the block at line 443 moved after the module's last line and rewritten on `ℝ³` with `k = 2` (review (b) group 2's MAJOR finding 1 and MINOR finding 2) | (b) group 2 | (b2c): CONFIRMED |
| `f2862d2` | `ClassicalLean/InformationTheory/CompressionTest.lean`: witnesses of the two e-BH bounds, three tests and `H = {0, 1}` (review (b) group 2's optional finding 4, taken) | (b) group 2 | (b2c): CONFIRMED |
| `fc77bd2` | `ClassicalLean/Probability/LongestRun.lean`: the typed claim at line 268 removed (its theorem already had a witness); five sentences reworded in place (ruling 2 of `lean/VACUITY-4/ruling-1.md`) | (b) group 2: the removal and the five sentences passed | (b2c) |
| `a9da7eb` | `ClassicalLean/Probability/EffectiveSampleSize.lean`: four witnesses, two typed claims removed, two sentences reworded; the docstrings and one witness's `X` changed after review (b) group 3's finding 1 | (b) group 3: CONFIRMED WITH FINDINGS, 1 MINOR | (b3c): CONFIRMED |
| `4fecf7e` | `ClassicalLean/Probability/GamblersRuin.lean`: three witnesses of the biased-walk theorems, the typed claim at line 1046 removed, three sentences reworded | (b) group 3 | (b3c) |
| `cfc476a` | `ClassicalLean/Probability/MaximalInequality.lean`: the two frozen witnesses re-witnessed at `n = 1` (ruling 3 of `lean/VACUITY-4/ruling-1.md`) | (b) group 4: CONFIRMED WITH FINDINGS, 1 MAJOR (process), 1 MINOR (the minus signs, fixed) | (b4c): NOT CONFIRMED, 1 MINOR (a records line in `misses.md`, fixed); (b4c2): CONFIRMED |
| `f6721ec` | `tools/witness_reviewed.txt`: `ClassicalLean/NumberTheory/PrimitiveDivisor.lean` line 423 listed as `NO-DOCSTRING` (a name-resolution check), not changed | | |
| `0a96178` | Job 3: `ClassicalLean/Analysis/GradientDescent.lean`, `sub_le_of_projGradientStep` re-witnessed (review (c) group 1: FROZEN; the reviewer's tested values) | (b) group 5: CONFIRMED WITH FINDINGS, 1 MINOR (a double blank line, fixed) | (b5c): CONFIRMED |
| `e196c18` | Job 3: `ClassicalLean/Probability/FairGame.lean`, `integral_stoppedValue_sum_eq` re-witnessed (review (c) group 2: DEGENERATE under rule 3, not FROZEN; counted within the six) | (b) group 5 | (b5c) |
| `25ce6f6` | Job 3: `ClassicalLean/Probability/YuleWalker.lean`, `durbinLevinson_spec` re-witnessed (review (c) group 3: FROZEN and degenerate) | (b) group 5 | (b5c) |
| `df19856` | Job 4, Goal item 7a: `tools/UninformativeReport.lean`'s whole-library command gets a finite outer budget (`set_option maxHeartbeats 2000000 in`) and its comment | (d): NOT CONFIRMED, 2 MINOR (one per leftover, text only) | (d1c): CONFIRMED |
| `2a916fd` | Job 4, Goal item 7b: `tools/VacuityGate.lean`'s FAIL text names case 5 and says what UNCHECKED and KERNEL-REJECTED mean (strings and comments only; the code compared equal, `j4-codecmp-7b-2`) | (d) | (d1c) |
| `6951c86` | Job 5: `HANDOFF.md` section 1 (round 73) and section 4 (the witness gate, rule 3's case of the moving process dated 2026-10-26, the CI decision, research step 4) (G) | (e): NOT CONFIRMED, 2 MAJOR, 4 MINOR, all wording; five fixed, MINOR 5 answered | (e1c): CONFIRMED |
| `7ebda52` | ruling 6: the gate's texts state review a4c's limit; `tools/WitnessListing.lean`'s header docstring, `tools/witness_gate.py`'s module docstring, HANDOFF.md section 4's gate entry and section 1's round-73 line; comments and docstrings only (G') | none (ruling 6 section 2 item 4: no code changed; claude-ai reads the texts at the push review) | |

Review (a) of Job 1, before `7515a48`: round 1 PASS WITH FINDINGS (4 MAJOR, each with a probe);
its confirming passes (ac) and (ac2) NOT CONFIRMED; rounds 3 and 4 NOT CONFIRMED (round 4 measured
false `WITNESSGATE PASS` results through module code, the stop answered by ruling 4); round 5
(`reviews/a4/review.md`, run on the Sonnet copy after the Opus run was stopped by a safety
classifier, as ruling 4 section 4 allows) CONFIRMED WITH FINDINGS. Every review is saved in
`~/lean/vacuity4-checks/reviews/`, its sha256 logged when it came back (the `review-*` lines of
`evidence.log`); each brief
was checked by `briefverify.py` and `briefcheck.py` before it was sent.

The process sweep (Job 3, review (c), three groups): 44 witnesses read; 1 FROZEN in group 1, 0 in
group 2 with 1 DEGENERATE, 1 FROZEN and degenerate in group 3. Three re-witnessed, so three of
Goal item 5's six places are used. No module beyond these three was added by the sweep; the gate's
first library run (`wg-lib-1`) added none (its 13 `TYPED-CLAIM` and 2 `NO-DOCSTRING` blocks are the
listed ones).

The modules this round changed, 14 (`j6-changed-modules.txt`): the eleven of the first part, and
`ClassicalLean/Analysis/GradientDescent.lean`, `ClassicalLean/Probability/FairGame.lean` and
`ClassicalLean/Probability/YuleWalker.lean`, added by review (c). The sentences reworded in place,
under ruling 2 of `lean/VACUITY-4/ruling-1.md`: five in LongestRun (`fc77bd2`), two in
EffectiveSampleSize (`a9da7eb`), three in GamblersRuin (`4fecf7e`), each named in its commit
message; no other sentence of a module changed.

Census of each of the 14 modules (`mkcensus.sh` on its copy at `ac62f50` and at G): the theorem
constants and all constants equal before and after for every one (`j6/run-all.log` lines 1 to 43,
14 `CENSUS-EQUAL` lines). No declaration was added, removed or changed.

### The gates, on the clean tree at G `6951c86` (predicted in `pred/pred-job6.md`, hashed first)

| run | predicted | measured (output, line) |
|---|---|---|
| j6-status | porcelain empty at G | empty, HEAD `6951c86` (`j6-status.out`: the HEAD line only) |
| j6-build | rc 0, 4193 jobs, 0 warnings | rc 0, 4193 jobs, 0 warnings (`j6-build.out` 1) |
| j6-axiom | PASS 3602, 0 scoped exceptions | the same (`j6-axiom.out` 1) |
| j6-vacuity | PASS, 1 reviewed helper, 0 VACUOUS-PENDING, 0 run-outs | the same (`j6-vacuity.out` 1) |
| j6-vactests | 89 tests, 47 flagged, 0 run-outs, 0 mismatches, 3 UNCHECKED | the same (`j6-vactests.out` 93) |
| j6-sorry | PASS 140 | PASS 140 (`j6-sorry.out` 1) |
| j6-records | PASS 140, 110 files | PASS 140, 110 files, 1 exemption (`j6-records.out` 1) |
| j6-drift | PASS | PASS (`j6-drift.out` 1) |
| j6-banned | PASS, 140 + root, 0 hits | the same (`j6-banned.out` 1) |
| j6-gate7 | ALL PASSED for G, 140 modules 0 failed, three axioms, planted fault named, about 24 min | ALL PASSED for `6951c86` (`j6-gate7.out` 35), modules 140 failed 0 (line 10), planted fault named (line 33), 23:22.52 wall clock (line 40) |
| j6-witness | PASS: OK 171, LISTED 1, TYPED 205, others 0, 377/377, 140 modules, 72 elaborated; at most 27 min 03 s + 10% | the same (`j6-witness.out` 591), 26:53.46 wall clock (line 596), 5760320 kB (line 601) |
| j6-witness-tests | 119 cases, 0 mismatches | the same (`j6-witness-tests.out` 120) |
| j6-modcount | MODULES 5729 ClassicalLean 141 | the same (`j6-modcount.out` 1) |
| j6-td-check | 4088 records (3602 thm, 486 def), elided 0, missing 0 | the same (`j6-td-check.out` 1) |
| j6-td-diff | removed 0, added 0, changed 0, proof_only 0 | the same (`j6-td-diff.out` 1) |
| j6-report | the 22 SUMMARY lines equal Setup 5's | equal (`j6-report.out` SUMMARY lines against `j4/s5-summary.txt`: no difference) |

### G', after ruling 6 (predicted in `pred/pred-gprime.md`, hashed first)

G' = `7ebda52` changes only comments and docstrings of the two tools files, and HANDOFF.md:
`evidence/docsonly.py` gives `DOCSONLY PASS` (label `docsonly-gprime`: the three files only, every
changed tools line inside a comment or the module docstring, the `ClassicalLean` tree `369469c2`
equal to `6951c86`'s), after its control (`docsonly-control-4`, `7515a48` to `fa45254`: FAIL, 5
problems). Re-run at G', as ruling 6 directs:

| run | predicted | measured (output, line) |
|---|---|---|
| gp-status | porcelain empty, HEAD `7ebda52` | the same (`gp-status.out`: the HEAD line only) |
| gp-witness-tests | 119 cases, 0 mismatches | the same (`gp-witness-tests.out` 120) |
| gp-witness | PASS: OK 171, LISTED 1, TYPED 205, others 0, copy-error 0, 377/377, 140 modules, 72 elaborated; within 10% of 26:53.46 | the same (`gp-witness.out` 591), 26:48.84 wall clock (line 596), 5759080 kB (line 601) |

The drift check, whose input HANDOFF.md
changed, ran before the commit (`gp-drift`, PASS). Every other result above stands for G': its
inputs are byte-identical; gate 7 was not re-run.

Goal item 6: the gate's whole-library time at `2a916fd` (`j4-g6-gate`) was 27:03.48 wall clock,
5.76 GB, on DSMain's 16 cores (`nproc`): over 20 minutes, so `.github/workflows/ci.yml` is not
changed (ruling 5). The first library run (`wg-lib-1`, before Job 2) took 26:27.02. The gate's
output does not separate the listing driver's time from the copies' time; no timing code was added
(ruling 5).

### Rulings during the work

Ruling 2 (`lean/VACUITY-4/ruling-2.md`): the listing driver outside the module, the check defined
once, the binder rules, a last round of review (a). Ruling 3 (`lean/VACUITY-4/ruling-3.md`): Lean
counts `k` and `n`. Ruling 4 (`lean/VACUITY-4/ruling-4.md`): a module may not run its own code while
it elaborates (the census, the command-kind and attribute allowlists, the inner code list, the
constants refused); one local commit, the library run, then a cold review. Ruling 5
(`lean/VACUITY-4/ruling-5.md`): Goal item 6 stands as written; no speed work in this order; the
follow-up GATE-SPEED for a later order. Ruling 6 (`lean/VACUITY-4/ruling-6.md`, on the stop
after review a4c): state the limit, no gate code changed in this order; one docs-only commit, G';
re-run at G' only the witness gate's tests and its library run; GATE-SPEED becomes GATE-2, with the
fail-closed inner check. Each saved in `~/lean/vacuity4-checks/pre/`.

### Misses, follow-ups and notes

- Misses, each in `evidence/misses.md` (items 1 to 26). The larger ones: review (a)'s round 4
  measured false `WITNESSGATE PASS` results through module code that I had listed as a limit rather
  than tested (item 21); I predicted the axiom `native_decide` leaves from the ruling's text, not
  from Lean (item 22); two Lean probes ran while the suite ran (item 23); the MaximalInequality
  statements were probed in Lean after the module was written, not before (item 24, review (b)
  group 4's MAJOR finding; the substance held); `fa45254` fixed review (a) round 5's F1 for the
  forms it named, not the mechanism, and had no confirming pass until a heads-up Dustin passed in
  (item 26; review a4c, ruling 6).
- The allowlists are frozen to the library of 2026-10-26: a new command kind or attribute (for
  example `alias`) fails the gate with `COPY-ERROR` until a ruling
  adds it (a heads-up Dustin passed in; HANDOFF.md section 4: "a module that needs a kind or
  attribute off the lists needs a ruling first").
- MovingAverage's four witnesses (review (c) group 3, finding 2) meet the case of the moving process
  as worded (with positive probability); under a path-by-path reading each would be frozen. Left
  as they are under the wording; for claude-ai to rule on (a heads-up Dustin passed in).
- Follow-ups for a later order, outside this order's Scope (rule 11): GATE-2 (ruling 6 section 4:
  the fail-closed inner check, with review a4c's k4 and k6 as fixtures, and ruling 5's speed
  work); the
  MERGE-1 CI paragraph of HANDOFF.md section 4 is stale since RULES-1 (review (e)); the unused
  `Mathlib.Probability.HasLawExists` import of `ClassicalLean/Probability/GamblersRuin.lean`
  (review (b) group 3); the order's Goal item 3 says the short `map_zero` resolves after
  Superadditive's last line to Mathlib's root lemma, which the module's own imports do not reach
  (review (b) group 1, finding 2; the dotted name is right either way); AdaptiveCoverage's witness
  at `T = 4` gives a zero left side (review (c) group 3, finding 3, optional).

Every quote in this part was checked by `scripts/quotecheck.py` against its saved source before the
commit (label `j6-quotes-8`, 17 quotes, 0 problems), after a planted misquote was caught (label
`j6-quotes-planted-8`, rc 1). This part, the INDEX row and the CLAIMS row were written by
`evidence/records73.py` through `ev.sh --nolean` (label `records73`).
