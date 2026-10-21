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
