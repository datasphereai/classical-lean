# ORDER 0923 — bring the library current, close its open threads, start information theory

Written 2026-09-23T12:27:13Z by claude-ai (Cowork, linked to helios) for one Claude Code session on
helios; revised the same day after a cold review and two follow-up checks by a second agent that did
not write it.
Library: `~/work/classical-lean`. Evidence repository: `~/Cowork/lean-rebuild`.
**Source of truth:** this file and `records/orders/INDEX.md`.

Four jobs, J1 to J4, in order, then a close. Each has Goal / Scope / Done-means and a line saying
whether it can be undone. "Done" closes a job only when its Done-means holds; a STOP at a gate is a
report, not a close (`records/orders/INDEX.md`).

---

## 0. State measured by claude-ai on 2026-09-23 — predict J1 from this, then check it

claude-ai read staged copies of files through the helios link. **No Lean was run**: there is no Lean
toolchain on that surface. Tags: *measured* (with what), *recorded* (read from a record, not
re-measured), *web* (read from a web page or a public git server, not measured on helios).

| # | Fact | Value | Tag |
|---|---|---|---|
| 1 | `master` in `~/work/classical-lean` | `202394ad3305c89323406874543a7c4cc4821093`, "Record Tolerance as speculative; round 14 used the wrong bar", committed 2026-09-11T02:59:52Z | measured: `.git/refs/heads/master`, `.git/logs/HEAD` |
| 2 | Copy on DSMain | `/data/git/classical-lean.git` `master` = the same hash; last push from helios 2026-09-13T06:42:22Z | measured: that ref file through the `~/dsmain` mount; `.git/logs/refs/remotes/dsmain/master` |
| 3 | Remotes | one: `dsmain` → `dsmain:/data/git/classical-lean.git` (an ssh alias) | measured: `.git/config` |
| 4 | Toolchain | `leanprover/lean4:v4.29.0-rc2`; Mathlib rev `8f07524533b483cffcf3c5a50b9633c6af0defdc` (`inputRev` `v4.29.0-rc2`) | measured: `lean-toolchain`, `lake-manifest.json` |
| 5 | How it was built | offline, by copying a prebuilt Mathlib from another checkout; `.lake/packages` about 6.8 G. Order F-1R (`~/Cowork/lean-rebuild/design/FOUNDATION-DELTA.md`) **forbade `lake update`** | recorded: `.gitignore` lines 3–11, `HANDOFF.md` §1, `FOUNDATION-DELTA.md` (order F-1R) |
| 6 | Modules | 41 under `ClassicalLean/`, all 41 imported by `ClassicalLean.lean` | measured: file listing and an import parse |
| 7 | Text gates | `check_sorry.py` PASS; `banned_vocab_scan.py` PASS, 0 hits; `check_records.py` PASS, 41 modules, 1 exemption (`Simplex/Hessian.lean`), 3 files searched — 4 once this order sits in `records/orders/` | measured: the repo's own scripts on a copy in claude-ai's sandbox |
| 8 | Lean gates | `lake build` rc 0, 0 warnings; `AxiomGate` rc 0, 1037 theorem constants, the same 2 named exceptions; `VacuityGate` rc 0 | recorded: `PROVENANCE.md` round 15 table — not re-measured |
| 9 | `records/rounds/` | empty | measured: directory listing on helios |
| 10 | Two rule slips by round 15 (committed 2026-09-11T02:59Z) | it was written into `PROVENANCE.md` (heading at line 42) although `records/README.md` Rule 1 sends new rounds to `records/rounds/`; and it wrote no `records/CLAIMS.md` row (the last row is dated 2026-09-08), against Rule 3 | measured: read |
| 11 | Open order | G-4 — `INDEX.md`: "open, route revised" | measured: read |
| 12 | Audit named but not run | the consumer test for `Superadditive` and `PredicateStack` (round 15; commit message of row 1) | measured: read |
| 13 | Who imports them | `Order/Superadditive.lean` ← only `NumberTheory/Mersenne.lean` (`superadditive_mersenne`). `Logic/PredicateStack.lean` ← only `Simplex/Basic.lean` (`openSimplexStack`, `admits_openSimplexStack_iff`, and an `example` using `Stack.admits_of_append_right`). The aggregator imports both | measured: grep on the copy |
| 14 | `backward.isDefEq.respectTransparency false` | set in 10 modules: `Algebra/CompanionMatrix`, `Combinatorics/AlgebraicGeneratingFunction`, `Combinatorics/RecurrenceGeneratingFunction`, `Geometry/Helix`, `Geometry/Hopf`, `Geometry/S3Quaternion`, `Geometry/SU2SO3`, `NumberTheory/CompositumDiscriminant` (six scoped `set_option … in` lines), `NumberTheory/LucasSequenceGeneratingFunction`, `NumberTheory/PowerSumCases` | measured: grep on the copy |
| 15 | Shannon entropy already exists | `ClassicalLean.Simplex.shannonEntropy`, `Simplex/FisherRao.lean` line 418, `-∑ i, p i * Real.log (p i)`; used only inside that file | measured: grep on the copy |
| 16 | The Gibbs lemmas' domain | `sum_mul_log_div_nonneg` (`Simplex/Gibbs.lean:124`) and `sum_mul_log_div_pos_of_ne` (`:146`) need both vectors strictly positive; `neg_log_card_le_sum_mul_log` (`:177`) needs `x ∈ openSimplex ι` | measured: read |
| 17 | Stale text | "no remote" is stated in `HANDOFF.md` §6 (line 290), in `PROVENANCE.md` "Where the evidence lives" (lines 22–25) and in `~/Cowork/lean-rebuild/README.md` (lines 8–9). False: `lean-rebuild` first pushed to `dsmain` 2026-09-08T23:27:12Z, `classical-lean` 2026-09-09T19:41:09Z | measured: read, and both repositories' `dsmain` reflogs |
| 18 | Evidence repository | `~/Cowork/lean-rebuild` `master` = `efe35b76`; DSMain `/data/git/lean-rebuild.git` `master` = `3a48ceb5`. The two local-only commits (`fbdbfc34`, `efe35b76`, 2026-09-15) add `layer/`: a separate Lake project on Lean v4.33.1 that derives the lane's FRONT / HARNESS / BACK layers — lane work, not library work | measured: both ref files, `layer/lean-toolchain`, `layer/DsLayer/Basic.lean` |
| 19 | Duplicate file | `~/Cowork/lean-rebuild/20260907T225350Z__claude-ai__msc-index-and-lean-coverage-plan (copy 1).md` exists on helios (13011 B, mtime 2026-09-07T23:01:12Z) and is byte-identical to the same name without ` (copy 1)` (sha256 `ab83e613…`) | measured: helios directory listing; `sha256sum` and `cmp` on staged copies |
| 20 | Mathlib tags after the pin | stable: `v4.29.0`, `v4.29.1`, `v4.30.0`, `v4.31.0`, `v4.32.0`, `v4.32.1`, `v4.32.2`, `v4.33.0`, `v4.33.1`, `v4.34.0`; newest overall `v4.35.0-rc2`. Each tag's `lean-toolchain` names the same Lean version | web: `git ls-remote` and raw `lean-toolchain` files, from claude-ai's sandbox |
| 21 | Upstream Lean | newest stable release v4.34.0, published 2026-09-14 | web: the GitHub release page |
| 22 | Mathlib and G-4 | the quadratic-field discriminant work (mathlib4 PRs #43490, #43491, opened 2026-09-06) was still open, with merge conflicts, when checked on 2026-09-23. A toolchain move alone is not expected to close G-4 | web: the two PR pages |

---

## 1. Rules for this session

- **Dustin does not read code or files.** Everything he needs goes in your chat reply. When he must
  act, give the exact command, the box, and the output you expect.
- **Predict, then measure.** Before any command that prints a count, a hash or an rc, write the value
  you expect, or write "no prediction". Report predicted beside actual.
- **This repository's rules hold unchanged:** `HANDOFF.md` §0 (measure the thing you claim), §4 (a
  gate is trusted only after it has been seen failing), §5 (names describe the mathematics;
  `banned_vocab_scan.py` enforces it); `records/README.md` Rules 1 to 4 (claim first; a round writes a
  fragment under `records/rounds/`, never `PROVENANCE.md`; an order is a file).
- **What Dustin ruled, 2026-09-07:** the library is comprehensive; module names follow Mathlib
  convention; no MSC code in any path or directory name; rank work by import in-degree of this build;
  computing, number theory, combinatorics, information theory and data science take precedence;
  softmax normalization is a target; and he delegated the priority order to claude-ai's mathematical
  judgment. The tiers and the "log-sum-exp spine" of the 2026-09-07 build order are claude-ai's
  proposal made at his request, not his rulings. **2026-08-29:** no cosmological framing and no
  golden-ratio numerology.
- **Git.** Commit locally. Never push to GitHub and never add a remote. Push to the existing `dsmain`
  remote only after Dustin says yes in the chat. Stage files by path, never with `git add -A`.
- **Park, never delete** — `mv -n` into a `_parked/` folder **outside** the repository, so the tree
  stays clean. Two named exceptions: J3's gate probe, a scratch file this session creates, is deleted;
  and `git worktree remove` of the bump worktree once J3 has landed (committed content only; its
  `.lake` has been moved out first).
- **Shell state does not carry between tool calls; the working directory does.** Write any value a
  later step needs into a file under `~/work/_bump-evidence/`, and name the directory in every command
  (`git -C <dir>`, or `cd <dir> && …`).
- **Network and DSMain.** Reach DSMain with `ssh -o BatchMode=yes -o ConnectTimeout=15` (for git:
  `GIT_SSH_COMMAND='ssh -o BatchMode=yes -o ConnectTimeout=15'`). If it fails, record "unreachable"
  and carry on. Never touch the VPN, routes or ssh configuration.
- **A second party for everything you write.** Before anything lands that adds or changes a theorem
  statement, a fresh subagent that did not write it reviews the statements cold. `VacuityGate` cannot
  see a statement that is true but says nothing (`HANDOFF.md` §4); only review can.
- **Agents.** Builds are serial. Never two agents editing one file, or running `lake` in one worktree,
  at the same time.

---

## J1 — open and re-measure (read-only)

**Goal.** Know the state before touching it.

**Scope.** Read-only. Run what plan mode allows now; a command it blocks goes into the plan with its
prediction and marked "deferred".

**Measure, predicting each value from §0 first:**

1. `git -C ~/work/classical-lean status --short` — expect exactly one line, this file, untracked:
   `?? records/orders/20260923T122713Z__claude-ai__order-0923-pick-up.md`. claude-ai placed it there
   through the helios link. If it is absent, STOP and say so: an order is a file before it is work.
2. `git -C ~/work/classical-lean rev-parse master dsmain/master` and
   `GIT_SSH_COMMAND='ssh -o BatchMode=yes -o ConnectTimeout=15' git -C ~/work/classical-lean ls-remote dsmain master`
   — expect the full hash of row 1, three times.
3. The six commands in `HANDOFF.md` §1, copied from that file, not retyped. Expect rows 7 and 8.
4. `df -h ~ ~/work` and `du -sh ~/work/classical-lean/.lake` — expect about 6.8 G for `.lake` (row 5);
   no prediction for free space.
5. `git ls-remote --tags https://github.com/leanprover-community/mathlib4 'refs/tags/v4.*'` — expect
   row 20.
6. `elan toolchain list` — expect at least `v4.29.0-rc2` and `v4.33.1` (the latter from `layer/`).
7. In `~/Cowork/lean-rebuild`: `git status --short`, `git rev-parse master dsmain/master`, and
   `ls -la --time-style=full-iso` plus `sha256sum` on both `…msc-index-and-lean-coverage-plan*.md`
   files — expect rows 18 and 19.

**Done-means.** A predicted-beside-actual table in the chat: actuals for everything plan mode allowed,
"deferred" for the rest, every miss explained. Present one plan for J2 to J4 and wait for approval.
**After approval, run the deferred commands first. If any result misses rows 1 to 8, STOP and report
before J2.** (An unreachable DSMain is recorded, not a miss.)

**Undo:** nothing to undo.

---

## J2 — close the threads the last session left open

**Goal.** Close what row 1's commit named as not done, and correct the stale records, on the current
toolchain, before anything moves.

**Scope.** Doc comments only in `Order/Superadditive.lean` and `Logic/PredicateStack.lean` — no
declaration added, removed or changed. `ROADMAP.md` §1.12. `HANDOFF.md` §6. `PROVENANCE.md`: one dated
correction line under "Where the evidence lives", nothing else. `records/`. In `~/Cowork/lean-rebuild`:
one dated correction in `README.md`, and the duplicate of row 19.

1. **First writes, before anything else.** A `records/CLAIMS.md` row claiming: for J2,
   `Order/Superadditive.lean` and `Logic/PredicateStack.lean`; for J3, every module under
   `ClassicalLean/` on branch `toolchain-bump`; for J4, new files under `ClassicalLean/InformationTheory/`
   (names added to the row before J4 writes them) and `Simplex/FisherRao.lean` (the one edit J4 allows);
   and the records paths the session will write (Rule 3). A row for order `0923` in
   `records/orders/INDEX.md`. Then one commit adding both and this file.
2. **The consumer audit** of `Superadditive` and `PredicateStack`, by round 15's bar: does anything
   outside the defining file *use* the definition to do work, or does it only have an instance? Start
   from row 13. Record the verdict in each module's header and in `ROADMAP.md` §1.12, with the grep
   beside it, the way round 15 did for `Tolerance`. Whatever the verdict, both modules stay: retiring a
   module is Dustin's call.
3. **Dated corrections** of the three stale "no remote" statements (row 17). Re-read each repository's
   `dsmain` reflog for the dates; do not copy them from this file.
4. **The duplicate** (row 19). Only if both files exist on helios and `cmp` is silent: if
   `git -C ~/Cowork/lean-rebuild ls-files --error-unmatch` on the copy's name fails (untracked), then
   `mkdir -p ~/Cowork/_parked` and `mv -n` the copy there, followed by `test ! -e` on its old path. If
   it is tracked, or either file is missing, move nothing and report.
5. **A fragment** under `records/rounds/` for round 16, per Rule 1: both modules named in full; the
   verdict; each module's theorem-constant count under the `AxiomGate` `.thmInfo` predicate; whether the
   gate numbers were taken on a clean or a mixed tree; and, as findings, the two rule slips of row 10.
   Do not move round 15 out of `PROVENANCE.md`. Commit `lean-rebuild`'s README correction in that
   repository, by path.

**Done-means.** The six gates pass on a clean tree with 41 modules, 1037 theorem constants, 2 named
exceptions and 0 warnings — unchanged, because this job is documentation only. (Gate 6's "files
searched" count rises by one per new records file; that is expected.) The fragment exists, and its
commit hash is added in a follow-up edit, never predicted (Rule 1).

**Undo:** yes — documentation only; `git revert`, and `mv` the parked copy back.

---

## J3 — move to the current stable Lean and Mathlib

**Goal.** The library builds on the newest stable Lean and Mathlib pair, with every gate green, every
theorem still present, and no statement's meaning changed.

**Why now.** The pin is a release candidate, `v4.29.0-rc2`; the current stable Lean is v4.34.0 (row
21). Every module added before the move is one more to migrate, and Mathlib removes deprecated names
after a grace period, so the cost only grows. `HANDOFF.md`'s axiom paragraph ("Mathlib moves") also
waits on it.

**This lifts order F-1R's ban on `lake update`** (row 5), for the worktree only. The plan states the
download volume — the first `lake update` clones mathlib4 and its eight dependencies with full
history; then up to six toolchains and one Mathlib cache per step — and Dustin approves J3 on that
basis.

**Scope.** A separate worktree on a new branch:
`git -C ~/work/classical-lean worktree add ~/work/classical-lean-bump -b toolchain-bump`. The main tree
and its `.lake` — the only offline-built copy — are untouched until step 8. `lake update` and
`lake exe cache get` run in the worktree only. Never compile Mathlib from source. Every J3 commit,
including step 7's, goes on the branch: a commit on `master` during J3 would make the fast-forward in
step 8 fail.

**Method.**

0. **Record the starting point, once.** `mkdir -p ~/work/_bump-evidence && git -C ~/work/classical-lean rev-parse master > ~/work/_bump-evidence/PRE && cat ~/work/_bump-evidence/PRE`
   — state the hash in the chat. Never rewrite this file; `master` does not move until step 8.
1. **Before lists.** Write a listing script as `~/work/_bump-evidence/ListTheorems.lean` (outside both
   trees) that prints the sorted theorem names under `ClassicalLean`, with `privateToUserName` applied
   as `AxiomGate` does, twice: raw, and filtered by `Name.isInternalDetail`. Run it from the main tree:
   `cd ~/work/classical-lean && lake env lean ~/work/_bump-evidence/ListTheorems.lean`, and save both
   lists in `~/work/_bump-evidence/`. Expect some explained differences later: the filter keeps
   auxiliaries such as `eq_def` and `induct`.
2. **Step through the last patch release of each minor version:** `v4.29.1`, `v4.30.0`, `v4.31.0`,
   `v4.32.2`, `v4.33.1`, `v4.34.0` (row 20). Add an intermediate tag only if a step needs its
   deprecation hints. **Every command in steps 2 to 4 runs in the worktree:** first check that
   `git -C ~/work/classical-lean-bump rev-parse --abbrev-ref HEAD` prints `toolchain-bump`, and prefix
   each command with `cd ~/work/classical-lean-bump &&`. At each step:
   - `df -h ~ ~/work` — STOP if free space is under 20 GB;
   - set `rev` in `~/work/classical-lean-bump/lakefile.toml`;
   - `curl -fsSL https://raw.githubusercontent.com/leanprover-community/mathlib4/<TAG>/lean-toolchain -o lean-toolchain`;
   - `lake update mathlib`; then `cmp lean-toolchain .lake/packages/mathlib/lean-toolchain` must be
     silent; then `lake exe cache get`;
   - `lake build --no-build Mathlib` must exit 0 — exit 3 means something would be compiled; rerun
     with `-v` to see what, then STOP;
   - `lake build`, the 10 modules of row 14 first;
   - fix errors and deprecation warnings back to 0 warnings;
   - commit the green step on the branch, with its gate numbers in the message.

   Stepping keeps Mathlib's deprecated aliases as rename hints; a direct jump loses them.
3. **Row 14's option.** `backward.*` options are compatibility switches, and Lean retires them.
   Prediction, from a reading of the v4.34.0 sources by claude-ai's reviewer (not run): the option still
   exists at v4.34.0 (Lean `src/Lean/Meta/ExprDefEq.lean` line 47), beside two new switches that
   default to true, `backward.isDefEq.respectTransparency.types` and `backward.isDefEq.implicitBump`.
   If the 10 modules break, try those switches before rewriting proofs. Mathlib v4.34.0's standard
   linter set adds `linter.auxLemma`: expect new warnings. At the last step, test whether `ring` now
   works in `PowerSeries` without the option (`HANDOFF.md` §1), and record the answer either way.
4. **Re-fail-test both Lean gates under the new toolchain.** In the worktree create
   `ClassicalLean/GateProbe.lean` in `namespace ClassicalLean.GateProbe` with three theorems: one proved
   by `native_decide`, one using a bare `axiom`, and one vacuous. Add `import ClassicalLean.GateProbe`
   to the worktree's `ClassicalLean.lean`, run `lake build`, then `AxiomGate`, `VacuityGate` and
   `check_sorry.py`. Each must go red on its probe; quote the red output. Then delete the probe file —
   deleted, not parked, and never committed — and run
   `git -C ~/work/classical-lean-bump checkout -- ClassicalLean.lean`; then
   `cd ~/work/classical-lean-bump && lake build` and re-run both Lean gates: green again, so no probe
   theorem survives into step 6's lists. Both gates import only `ClassicalLean` and keep only names
   under it, so a probe outside the aggregator or the namespace proves nothing.
5. **Review before landing.** A fresh subagent reads the whole branch diff: every change to a theorem
   statement is a Mathlib rename, never a change of meaning. Step commits may come before this review;
   nothing lands before it.
6. **After lists.** Run the listing script from the worktree (adapt a copy if the new toolchain needs
   it, and keep both versions), save the lists in `~/work/_bump-evidence/`, and diff them against
   step 1's.
7. **Records, on the branch.** Re-run the searches in the G-4 order's "Status of the original G-4"
   section against the new Mathlib, plus a search for quadratic-field discriminant results; write the
   result as a dated line in the G-4 order and in its `INDEX.md` row. Then find every claim tied to the
   old pin:
   `cd ~/work/classical-lean-bump && grep -rn -i -E 'v4\.29|8f07524533|at the pinned|pinned (revision|toolchain)|Mathlib (has|proves) no|not in (this )?Mathlib|Mathlib (does not|lacks)|no hits|exit 1' ClassicalLean tools HANDOFF.md ROADMAP.md .gitignore`.
   Expect hits at least in `.gitignore` line 6, `HANDOFF.md` lines 76 and 239, `ROADMAP.md` line 630,
   `tools/AxiomGate.lean` line 42, and the headers of `Simplex/LogSumExp`, `Simplex/CrossEntropy`,
   `Algebra/CompanionMatrix`, `NumberTheory/CompositumDiscriminant`, `NumberTheory/LucasApparition`
   and `NumberTheory/LucasSequence`. Each hit that is a claim about Mathlib is either
   re-measured, or covered by one dated line in `ROADMAP.md` §4 and `HANDOFF.md` §1 that lists every
   such file and says it was measured at `8f07524533`.
8. **Land, reversibly.** Each bullet is one command chain. If a chain exits non-zero, STOP — and if
   what failed is the six gates, run the recovery chain first. `mv -n` onto an existing target is
   silent on some coreutils versions, so every move is followed by a `test` that catches a refusal.
   - Check the starting point: `test "$(git -C ~/work/classical-lean rev-parse master)" = "$(cat ~/work/_bump-evidence/PRE)"`.
   - Park the old build first, outside the repository:
     `mkdir -p ~/work/_parked && mv -nT ~/work/classical-lean/.lake ~/work/_parked/classical-lean.lake-v4.29.0-rc2 && test ! -e ~/work/classical-lean/.lake`.
   - `git -C ~/work/classical-lean merge --ff-only toolchain-bump`.
   - `mv -nT ~/work/classical-lean-bump/.lake ~/work/classical-lean/.lake && test ! -e ~/work/classical-lean-bump/.lake`
     (`-T` stops nesting; the `test` catches a refusal). No `lake update` and no `cache get` in the
     main tree.
   - Run the six gates in the main tree.
   - **If any gate is not green**, recover in one chain:
     `git -C ~/work/classical-lean reset --keep "$(cat ~/work/_bump-evidence/PRE)" && mv -nT ~/work/classical-lean/.lake ~/work/_parked/classical-lean.lake-failed-$(date -u +%Y%m%dT%H%M%SZ) && test ! -e ~/work/classical-lean/.lake && mv -nT ~/work/_parked/classical-lean.lake-v4.29.0-rc2 ~/work/classical-lean/.lake && test ! -e ~/work/_parked/classical-lean.lake-v4.29.0-rc2`.
     Then report. If any part of the recovery fails, stop the session, report, and do not go on to J4.
   - **Only when every gate is green:**
     `git -C ~/work/classical-lean worktree remove ~/work/classical-lean-bump`. Never `--force`; if it
     refuses, report.

**If J3 STOPs at any point:** leave the worktree and the branch and report their paths. Go on to J4
only if `git -C ~/work/classical-lean rev-parse master` equals `~/work/_bump-evidence/PRE`,
`git -C ~/work/classical-lean status --short` shows no tracked changes, and the six gates pass in the
main tree. Otherwise stop the session and report. Record in the
`CLAIMS.md` row and in the report that `toolchain-bump` (give its hash) is unmerged and will need a
rebase after J4's commits.

**Done-means** — all of these, or a STOP report:

1. `lean-toolchain` and the `lakefile.toml` `rev` name the newest stable pair. In the main tree,
   `lake build` rc 0 with 0 warnings.
2. `AxiomGate` rc 0, every theorem inside `{propext, Classical.choice, Quot.sound}` or the same 2 named
   exceptions; `VacuityGate` rc 0; the three text gates rc 0.
3. The filtered "after" list equals the filtered "before" list, or every difference is named and
   explained.
4. Both Lean gates seen red on the probe under the new toolchain, with the runs quoted in a commit
   message.
5. Step 7's records done; `HANDOFF.md` §1 updated (toolchain, both build notes); a dated line in
   `ROADMAP.md` §4 saying every row above it was measured at `8f07524533`; a round fragment.

**STOP and report — do not work around — if:** free disk is under 20 GB before a step; the cache cannot
be fetched or is incomplete; a fix would change what a theorem says; a gate cannot be made to go red on
its probe; something a proof needs is gone with no replacement; or any chain in step 8 exits non-zero.

**Undo:** yes, even after the worktree is removed —
`git -C ~/work/classical-lean reset --keep "$(cat ~/work/_bump-evidence/PRE)"` plus the parked `.lake`
bring back v4.29.0-rc2. Keep the parked `.lake` until Dustin says it can go.

---

## J4 — begin the information-theory tier

**Goal.** Finite Shannon entropy and relative entropy as first-class objects, and the data-processing
inequality, built on the Gibbs and log-sum-exp results the library already proves. This finishes the
entropy item of Tier 1 and starts the Stochastic and Channel modules of Tier 2 in
`~/Cowork/lean-rebuild/20260907T231327Z__claude-ai__foundation-ranked-build-order.md` — claude-ai's
proposal at Dustin's request, inside his ruling that information theory is among the areas that take
precedence. It also answers `ROADMAP.md` §3 item 3: an area with no number theory in it.

**When.** After J3 lands, on the new toolchain. If J3 STOPs, J4 runs on the current pin, under the
conditions in J3's STOP paragraph — and its Mathlib search is also run against the newest Mathlib
source J3 reached — in the worktree's `.lake/packages/mathlib`, or, after a failed landing, in
`~/work/_parked/classical-lean.lake-failed-*/packages/mathlib` — so J4 does not build what a newer
Mathlib already has. If J3 reached no newer Mathlib, skip that second search and say so.

**Scope.** A new directory `ClassicalLean/InformationTheory/` and new modules in it; one import line per
module in `ClassicalLean.lean`; new `ROADMAP.md` §2 rows; `records/`. **One edit to an existing module
is allowed:** `Simplex/FisherRao.lean` may lose its `shannonEntropy` definition and gain one import, if
the plan moves that definition into the new entropy module. Moved, it keeps its full name
`ClassicalLean.Simplex.shannonEntropy` (declared inside `namespace ClassicalLean.Simplex` in the new
file), so nothing else in `FisherRao.lean` changes: its statements name it (lines 425 and 442) and a
proof unfolds it (line 429). Every other existing module is read-only.

The new modules' file names are deliberately not written in this order. Gate 6 (`check_records.py`)
accepts a module whose path or bare file name appears in any records file, and this order must not
pre-pass it. So: do not write J4 file paths into any `records/orders/*.md` before the round fragment
exists. After creating each new module, `check_records.py` must FAIL naming it; if it passes, the file
name collides with one the records already mention (e.g. `Gibbs.lean`, `CrossEntropy.lean`) — choose
another name.

**Method.**

1. **Search the library and Mathlib first, for the mathematics, not the names** (`ROADMAP.md` §0), with
   case-insensitive `grep -rniE`. At least: `entropy` (this finds `binEntropy`, `qaryEntropy` and row
   15's `shannonEntropy`), `negMulLog`, `klFun`, `klDiv`, `mutualInfo`, `condEntropy`, `log_sum`,
   `logSum`, `stochastic` (this finds `doublyStochastic`), and the statement shape
   `'log \([^()]+ / [^()]+\)'` — a shape, not this library's variable names.
   Start from `PROVENANCE.md` round 10 (lines 480–486), which already searched Mathlib's
   `InformationTheory/`. Record every command and its hit count in the new `ROADMAP.md` row. Check
   prior art outside Mathlib too: `github.com/FujiHaruka/information-theory`, whose README claims about
   4,100 theorems on Lean v4.31.0 (read on 2026-09-23, not verified). Do not add it as a dependency;
   say in the row what it already covers.
2. **Use what the library has; never define a thing twice.** Row 15: `shannonEntropy` exists. The plan
   either moves it into the new entropy module (the one allowed `FisherRao.lean` edit) or says why it
   stays. Row 16: the Gibbs lemmas are open-simplex only, so a statement on `stdSimplex` needs a new
   Gibbs inequality with a support hypothesis. `crossEntropy_sub_entropy`
   (`Simplex/CrossEntropy.lean:104`) already is the bridge on the open simplex. `log_softmax` and
   `gibbsObjective_eq_iff` are in `Simplex/LogSumExp.lean`. `FOUNDATION-DELTA.md` maps the spine as it
   stood on 2026-09-07 (34 modules); it omits `shannonEntropy` and the seven modules added since.
3. **Junk values before statements** (`ROADMAP.md` §1.11). `Real.log 0 = 0`, `x / 0 = 0` and
   `Real.log x = Real.log |x|` make `∑ i, p i * Real.log (p i / q i)` return a finite and possibly
   negative number exactly where relative entropy is +∞ — at `p = (½, ½)`, `q = (1, 0)` it returns
   about −0.3466. Enumerate the junk cells numerically, then choose each statement's domain.
4. Write the statement list. A fresh subagent reviews it cold. Then prove.

**Suggested content** — change it to fit what the search finds:

In the statements below, `entropy` means the one Shannon entropy definition — row 15's `shannonEntropy`,
moved or not.

- **An entropy module:** that one entropy definition (moved, or the reason it stays);
  `relEntropy` — not `klDiv`, which would shadow Mathlib's `InformationTheory.klDiv`; nonnegativity and
  its equality case on `stdSimplex`, under `∀ i, q i = 0 → p i = 0` or `q` strictly positive; entropy
  at most `log (card ι)`, with equality exactly at the uniform vector; and
  `relEntropy p (softmax x) = crossEntropy x p - entropy p` stated on `stdSimplex`, where zero
  coordinates make it new — on the open simplex it is `crossEntropy_sub_entropy`.
- **A channel module** (`open scoped Matrix` for `ᵥ*`): a row-stochastic `W : Matrix ι κ ℝ` (entries
  nonnegative, rows summing to 1) maps `stdSimplex ℝ ι` into `stdSimplex ℝ κ`; the log-sum inequality; the
  data-processing inequality `relEntropy (p ᵥ* W) (q ᵥ* W) ≤ relEntropy p q`, for `p ∈ stdSimplex`, `q`
  a probability vector with `∀ i, 0 < q i` (or the support hypothesis) — without the hypotheses it is
  false under junk values: `p = (½, ½)`, `q = (1, 0)`, `W = [[1, 0], [½, ½]]` breaks it; entropy does
  not decrease under a doubly stochastic matrix, which should fall out of the data-processing
  inequality at `q` = uniform (`uniform ᵥ* W = uniform`, and `relEntropy p uniform = log n - entropy p`)
  — if it does not, that is a finding; Mathlib's `doublyStochastic` needs `[DecidableEq n]`, so the plan
  says how that fits the library's `DecidableEq` convention (`Simplex/CrossEntropy.lean` lines 24–31);
  mutual information as the relative entropy of a joint distribution to the product of its marginals,
  nonnegative, and zero exactly at independence.

**Done-means.**

1. Every shipped module: `lake build` rc 0, 0 warnings; `AxiomGate` with every new theorem inside the
   kernel trio and no new exception; `VacuityGate` rc 0; the three text gates rc 0.
2. No `sorry` ships. A statement not proved this session stays out of the file and is listed in
   `HANDOFF.md` §3 as next.
3. The reviewing subagent's verdict on the statements is quoted in the round fragment.
4. The `ROADMAP.md` §2 row carries the search commands and counts. The fragment carries each new
   module's theorem-constant count, taken with the `AxiomGate` `.thmInfo` predicate, and names
   `ClassicalLean/Simplex/FisherRao.lean` in full if the definition moved (Rule 1).
5. Some theorem outside the defining module uses each new definition, or the fragment says why not.
   Round 15's bar applies to new definitions from their first day.

**Undo:** yes — new files, one import line, and at most one moved definition; `git revert`.

---

## Close

1. `HANDOFF.md` refreshed: the §1 snapshot numbers from the six commands on a clean tree, the
   toolchain, §6's remote facts, and §3's "what next".
2. The `CLAIMS.md` row closed; `INDEX.md` rows updated.
3. A fresh subagent checks this order's Done-means against the session's whole diff —
   `git -C ~/work/classical-lean diff 202394ad..master`, `git -C ~/Cowork/lean-rebuild diff efe35b76..master`,
   and, if J3 stopped, `git -C ~/work/classical-lean diff master...toolchain-bump` — and reports any
   Done-means not met.
4. Ask Dustin, one line each:
   - "Push `classical-lean` `master` to DSMain? It moves from `202394ad` to `<new hash>`."
   - "Pushing `lean-rebuild` also pushes two 2026-09-15 commits this session did not make: `layer/`,
     the Lean project that derives the lane's FRONT / HARNESS / BACK layers (Lean v4.33.1). Push all
     three to DSMain?" On no, leave `lean-rebuild` unpushed.
5. The final chat report: predicted beside actual, what landed with commit hashes, what STOPped and
   why, and what comes next.

## Not in this order

- **G-4 itself.** It is on the number-theory track, and the 2026-09-07 build order advises not to
  interleave the tracks. J3 only re-runs its searches.
- **Anything in the lane on DSMain**, including `layer/` in `lean-rebuild`. The LEAN lane's store is a
  separate matter for claude-ai.
- **Publishing to GitHub.** A one-way door; Dustin's decision.
- **Retiring any module.**
