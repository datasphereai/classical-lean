# Round 72 — batch 5 of the API-credit drafts (order LEAN-35)

Session: Claude Code `session_01JeFYgaV5tNaAbLVxH8HFHY` on DSMain, as dustin, executing order
`LEAN-35` (`records/orders/20261025T101000Z__claude-ai__order-lean35-kalman-moving-average-hajek-renyi-wald-hitting-times.md`,
written by claude-ai, copied verbatim; lane `lean/LEAN-35/order.md`, sha256
`037d2022b2669ba034100932761a1f3ed09d77aa39e6f89a0ec0a4c3520a54cc`), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `lean-35`, made from `origin/master` = `f5411f4`
(LEAN-34's last commit, equal to `git ls-remote github master`). Lean and Mathlib v4.34.0. Nothing
pushed. Evidence: `~/lean/lean35-checks/` (outside the repository), `evidence.log` (UTC time,
label, rc, prediction, command per run; `COMMIT <hash>` marker lines). Plan: lane
`lean/LEAN-35/plan.md` (sha256 `4d3d25ddae7b0e47bc95fb37c506da2a64f1f16a2cdbb417812265ff4f21307a`),
approved by Dustin on 2026-10-25 (EDT morning); the first line of `evidence.log` is at
2026-10-25T10:07:51Z.

Dustin's approval, saved word for word as `~/lean/lean35-checks/pre/dustin-approval.md` (label
`approval`), carries two rulings: (1) before Setup 1, `printenv CLAUDE_CODE_DISABLE_AUTO_MEMORY`,
predicted `1`, so that fresh reviewers do not load his auto-memory index; it printed `1`; (2) the
plan's one read of a lane file outside the connector is accepted, and every later lane read and
copy goes through the connector. The three lane files Setup 1 needed (the two type-dump files and
the witness check) and the order's copy were read through the connector and written from its
replies, each sha256 checked against the order's value (`evidence/copyhelpers.sh`).

First part written before the work; completed after it, below.

## Files this round changes

Module files (no module is added):

* item 114: `ClassicalLean/Probability/KalmanVariance.lean` (new import line
  `import ClassicalLean.Probability.FirstOrderRecursion`);
* item 115: `ClassicalLean/Probability/MovingAverage.lean` (new import line
  `import ClassicalLean.Probability.EffectiveSampleSize`);
* item 125: `ClassicalLean/Probability/MaximalInequality.lean`;
* item 148: `ClassicalLean/Probability/FiniteChain.lean`;
* item 138: `ClassicalLean/Probability/FairGame.lean` (new import lines
  `import Mathlib.Probability.Independence.InfinitePi` and `import Mathlib.Probability.BorelCantelli`,
  for its witness).

Also changed: `records/CLAIMS.md` and `records/orders/INDEX.md` (this order's rows appended at the
bottom, and LEAN-34's push recorded in LEAN-34's two rows), this fragment, the order's copy,
`HANDOFF.md` section 1, `ROADMAP.md` (section 1.29), the new bridge baseline
`records/bridges/LEAN-35/`, and `tools/vacuity_reviewed.txt` only if a helper is listed. No other
`.lean` file, no other import line, nothing else under `tools/`, `.github/` or
`records/rules.toml`; `HANDOFF.md` sections 0 and 2 to 6 untouched.

## Order LEAN-34's push

By records/README.md rule 2 ("the next order's records commit appends the push of the order before
it to that order's INDEX row and CLAIMS row"), this round's first commit inserts into LEAN-34's
INDEX row (after ``one bridge found (row 164, lane `MATH-PLAN-library-2-bridges-2.md`)``, before its
commits cell) and its CLAIMS row (before the final ` |`) the text ``; pushed by Dustin: DSMain's
master ref written 2026-10-21 20:51:51 EDT, GitHub master equal (`f5411f4`)``, as the order's cut
measured it, by the script `evidence/pushnote.py` (LEAN-34's, adapted), which asserts the text
after each anchor before inserting and runs before anything is appended.

Records files written by this session's commands, not by the evidence helper (HANDOFF.md rule 23):
the order's copy (written from the connector's reply, its sha256 checked, and copied into the tree
by `evidence/records1.sh` through `ev.sh --nolean`, label `records1`), this fragment, the INDEX row
and the CLAIMS row (written with the Write tool into the evidence folder, hashed by `hl.sh`, and
copied or appended by `records1.sh` through `ev.sh --nolean`, label `records1`).

## Completed after the work (2026-10-25 UTC)

### What landed (one commit per item, then the documents)

| commit | what | review | confirming pass |
|---|---|---|---|
| `47b4e08` | records first (this fragment's first part, the order's copy, the INDEX and CLAIMS rows, LEAN-34's push) | | |
| `ece8009` | item 114, `ClassicalLean/Probability/KalmanVariance.lean`: `riccatiRoot_eq_steady`, FAITHFUL to the row's equation (the row's filter and error-recursion clauses not stated, as its docstring says); new import line `import ClassicalLean.Probability.FirstOrderRecursion` | (a): PASS WITH FINDINGS, 4 MINOR: 1 answered by the docstring, 3 docstring fixes | (ac): CONFIRMED |
| `2292e73` | item 115, `ClassicalLean/Probability/MovingAverage.lean`: `variance_sum_movingAverage` (private `maCov`, `sq_sum_eq`), FAITHFUL; new import line `import ClassicalLean.Probability.EffectiveSampleSize` | (b): PASS WITH FINDINGS, 2 MINOR on the docstring entry, fixed | (bc): CONFIRMED WITH FINDINGS, 1 optional MINOR on the entry's wording, not taken |
| `cdc3e60` | item 114's docstring entry completed, as review (b) noted against `ece8009` (docstring only) | | (bc): the line FIXED |
| `11bcaea` | item 125, `ClassicalLean/Probability/MaximalInequality.lean`: `measureReal_exists_mul_abs_ge_le` (private `hajekW`, `hajekW_zero`, `hajekW_succ`), GENERALIZED (any finite measure; no `S 0 = 0`) | (c): PASS WITH FINDINGS, 1 MAJOR (the first witness, the module's Kolmogorov walk at `n = 2`, was frozen inside its horizon: replaced by the reviewer's tested witness) and 2 MINOR, fixed | (cc): CONFIRMED WITH FINDINGS, 1 MINOR on the records, answered by re-runs |
| `846e368` | item 148, `ClassicalLean/Probability/FiniteChain.lean`: `meanHitting_eq`, FAITHFUL, and `meanHitting_eq_of_le`, the draft's earlier statement kept as a corollary; the draft's private Bernoulli inequality replaced by Mathlib's `one_add_mul_le_pow` | (e): PASS WITH FINDINGS, 3 MINOR: the first witness replaced (its killed chain was nilpotent), the route added to the entry, an older module-docstring sentence outside the Scope left for a later order | (ec): CONFIRMED |
| `c1aec90` | item 138, `ClassicalLean/Probability/FairGame.lean`: `integral_stoppedValue_sq_eq`, GENERALIZED (each step independent only of the past; any filtration in which step `n` is known at time `n + 1`); new import lines `import Mathlib.Probability.Independence.InfinitePi` and `import Mathlib.Probability.BorelCantelli`, for the witness only | (d): PASS WITH FINDINGS, 2 MINOR on the docstring paragraph, fixed | (dc): CONFIRMED |
| `d21fd22` | documents: `HANDOFF.md` section 1, `ROADMAP.md` section 1.29 (G) | documents review: PASS WITH FINDINGS, 3 MINOR wording fixes | (docsc): CONFIRMED |
| `8421cef` | records: the bridge baseline `records/bridges/LEAN-35/` | | |

Job 1's statement review (reviews/stmt/review.md): PASS WITH FINDINGS, 0 BLOCKER, 0 MAJOR, 9 MINOR, all
fixed or answered in the statement files' docstrings; its confirming pass (reviews/stmtc/review.md):
CONFIRMED. Every review saved in `~/lean/lean35-checks/reviews/` and hash-checked against the sha256
its agent returned; the tree checked before and after each (labels `pre-*-status`, `post-*-status`).

Credit (rule 19): items 114, 115, 125 and 138: the drafts `d114-r1-s2`, `d115-r2-s1`, `d125-r3-s2`,
`d138-r1-s1`; item 148: the amended draft `d1148-r1-s1` (the amendment round); all written by Claude
Opus 5.5 through the Anthropic Batch API (the lane's API-CREDIT-1 work), adapted by this session. The
witnesses of items 125 and 148's `meanHitting_eq` were proposed by reviews (c) and (e). Each proof
change against its draft is in its commit message and in the module docstring's entry.

Theorem-constant counts per module (census of the final module copies under the axiom gate's
`.thmInfo` predicate, rule 27; `census_<Module>_new_thm.out` line 1, against
`census_<Module>_old_thm.out`; differences by `evidence/addednames.sh`, `census-added.out` line 6):
`Probability/KalmanVariance` 21 (+1), `Probability/MovingAverage` 39 (+15),
`Probability/MaximalInequality` 27 (+4), `Probability/FiniteChain` 22 (+7), `Probability/FairGame`
4 (+1); total +28 (the 9 named theorems, 2 equation lemmas, 10 `_proof_N` and 7 `_simp_N`
auxiliaries), and 2 new definitions.

### The gates, on the clean tree at G `d21fd22` (predicted in `pred/pred-main.md`, hashed first)

| run | predicted | measured (output, line) |
|---|---|---|
| g1-build | rc 0, 4193 jobs, 0 warnings | rc 0, 4193 jobs, 0 warnings (`g1-build.out` 6) |
| g2-axiom | PASS 3602 | PASS 3602 (`g2-axiom.out` 1) |
| g3-vacuity | PASS, 1 reviewed helper, 0 VACUOUS-PENDING | the same (`g3-vacuity.out` 1) |
| g3-tests | 89 tests, 47 flagged, 0 run-outs, 0 mismatches | the same (`g3-tests.out` 93) |
| g4-sorry | PASS 140 | PASS 140 (`g4-sorry.out` 1) |
| g5-records | PASS 140, 108 files | PASS 140, 108 files (`g5-records.out` 1) |
| g6-drift | PASS | PASS (`g6-drift.out` 1) |
| g6-banned | PASS, 140 + root, 0 hits | the same (`g6-banned.out` 1) |
| g7 | ALL PASSED, 4193, 140 modules 0 failed, 3602, three axioms, planted fault named | ALL PASSED for `d21fd22` (`g7.out` 35), 24:02.49 wall clock (line 40) |
| g-modcount | MODULES 5729 | MODULES 5729, ClassicalLean 141 (`g-modcount.out` 1) |
| td-after | 4088 records (3602 thm, 486 def) | the same, elided 0, missing_fields 0 (`td-after-check.out` 1) |
| td-diff | removed 0, added 30, changed 0, proof_only 0 | the same (`td-diff.out` 31); the 30 ADDED names equal the census's (`td-added-cmp.out` 2) |

The bridge search (at G, through `rootrun.sh`): rc 1; 30 new pairs, 3 new shapes, 74 gone pairs
against `records/bridges/LEAN-34/` (`bridges.out` 109); inside the hand prediction. One real bridge,
appended to the lane's bridges file as row 165 (the fair walk's mean exit time equals the mean
hitting time of its finite chain: GamblersRuin's `integral_exitTime_eq` with item 148's
`meanHitting_eq`); the file says how the other keys were checked. The report tool (at G): 1990
written theorems; A 1186; B 804; C 37, 0 recursive; self-test mismatches 0 (`report.out` 1222 to
1243); no `CLOSES` line names a theorem of this order.

### The witness check (`scripts/mkwitcheck.py`, LEAN-34's version 2)

Before each module commit, on the module as built: KalmanVariance 2 of 2 OK (`witcheck-kv-3`),
MovingAverage 4 of 4 (`witcheck-ma-2`), MaximalInequality 3 of 3 (`witcheck-mi-3`), FiniteChain 7 of
7 (`witcheck-fc-2`), FairGame 2 of 2 (`witcheck-fg-2`), each count as predicted by rule 13.

### Misses, follow-ups and notes

- Misses, each in `evidence/misses.md`: a clock time in one prediction header not read from a clock;
  three guessed line counts (34 for 37, 285 for 288, 45 for 46) and one count taken before a later
  edit (301 for 302); a predicted unused-section-variable warning that did not appear; the type
  comparison of item 115 needed two re-runs (a notation difference, then the checker's reading
  order); one name refused by `el.sh` (`w115-1`, the copied witness's names not yet probed); the
  vacuity copy's folder not made before its first run (`mkv-vac`, rc 1); two docstring edits that
  left lines over 100 characters, each corrected; a records claim made before its re-run (review
  (cc)); commands outside the evidence helper: two stray `python3 -I -` runs (one waited on stdin
  and was killed, one read `/dev/null`; neither read nor wrote anything) and two `replall.py` runs
  on a block file.
- Before approval, one lane file was read with `cat` rather than the connector; accepted by Dustin's
  ruling 2; every later lane read and write went through the connector.
- Follow-ups for a later order, outside this order's Scope (rule 11): the module's older witnesses
  of `measureReal_exists_abs_ge_le` and `integral_sup_sq_le` in
  `ClassicalLean/Probability/MaximalInequality.lean` use a walk frozen inside their horizon `n = 2`
  (review (c); a heads-up Dustin passed in, `evidence/headsups.md`); a sweep of earlier orders'
  witnesses for the same pattern is recommended for the next gate order. In
  `ClassicalLean/Probability/FiniteChain.lean`'s module docstring, the title and the sentence on
  `TwoStateChain` say the module asks every entry at least `δ`, false since item 100 and again with
  item 148 (review (e)). Item 148's hypotheses were not drop-tested; review (e) worked three cases by
  hand (not checked in Lean).
