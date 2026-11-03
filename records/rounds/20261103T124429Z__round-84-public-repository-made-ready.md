# Round 84 — the repository made ready to be public (order PUBLIC-1)

Session: Claude Code `session_01HgueTXi2oGS6SU54fBZc2R` on DSMain, as dustin, executing order
`PUBLIC-1` (`records/orders/20261103T123021Z__claude-ai__order-public1-repository-made-ready.md`,
written by claude-ai, copied verbatim; lane `lean/PUBLIC-1/order.md`, sha256
`d9a12bfbd98e47c87a69bf32375a7d5afd3a957d3b3069740c6434a1f6d2dd3f`), to the lighter procedure (store
row 20261026-063), in the worktree `~/lean/classical-lean-paper-crypto` on branch `public-1`, from
`24a75a34310ebc0d4022bb91cd2edda8fc86ff25` (MERGE-6's last commit, master on both remotes).
Evidence: `~/lean/public1-checks/` (outside the repository); every count below is read from a saved
output there, cited by its file name.

This round changes `README.md` and `records/` only. It adds, changes and proves nothing in a
module; `ClassicalLean/`, `ClassicalLean.lean`, `tools/`, `.github/`, the lake files and the
toolchain are untouched, which the gates at G measure as an empty diff against `24a75a3`.

## Modules this round brings in

None. No `ClassicalLean/…` path is added or changed.

## Order MERGE-6's push

By records/README.md rule 2, this round's first commit inserts into MERGE-6's INDEX row (immediately
before its commits cell) and its CLAIMS row (before the final ` |`) the text `; pushed by Dustin:
master 24a75a3 on both remotes, CI run 41612812385 green`. "Green" is measured: `gh run view
41612812385 -R datasphereai/classical-lean --json status,conclusion,headSha` gave `completed`,
`success`, headSha `24a75a34310ebc0d4022bb91cd2edda8fc86ff25` on 2026-11-03 (`step1` of this
session; the order's own header states the same run). Step 3 of the order does not name this
insertion; rule 2 does, and the order's `rf_check.py` "as MERGE-6 did" checks it.

## Setup (measured in this session, 2026-11-03 UTC)

* Launch: `CLAUDE_CODE_DISABLE_AUTO_MEMORY=1`. The two deny rules the order says the launch paste
  adds (`gh repo edit`, `git push`) are not in `~/.claude/settings.json` or `settings.local.json`
  (the only deny rule there is an edit rule for the lane); if they exist they are session-scoped and
  this session cannot print them. Neither command is run in this round.
* Step 1 (`step1_pins.out`, `step1_greps.out`, and the session's git output): both fetches rc 0;
  worktree HEAD `24a75a3…`, porcelain empty; both remotes' master `24a75a3…`; `git ls-remote github`
  shows `HEAD` and `refs/heads/master` only; `README.md`, `HANDOFF.md`, `ROADMAP.md` and
  `records/README.md` sha256 as the order names; the 12 pinned files on DSMain and the 7 in the lane
  (by `ds_hash`) each with the order's sha256 and size; grep (a) 84 lines in 40 modules, greps (b)
  and (c) the order's names and counts (its "the plan's row" 41 is case-insensitive: 40 `plan's row`,
  1 `plan's rows`, 1 `plan row`); visibility `PRIVATE`; `git diff --quiet e8398c2 24a75a3` over the
  Lean tree, `tools`, `.github` and the lake files true. Then `git checkout -b public-1`.
* Step 2 (`vocab_count.py`; `step2_control.out`, `vocab-tracked.out`, `step2_plant.out`): the
  counter imports `load_terms` and `compile_terms` from `tools/banned_vocab_scan.py` and matches as
  its `main` does (lines 114 and 117 to 127; a hit forgiven only inside a match of its exception's
  context on the same line). Indexes are 1-based, as the order names them. Over the 528 tracked
  files at `24a75a3` (166343 lines): retired[8] 14 raw lines (6, 6, 1 in the three `records/` files
  the order names, 1 in `HANDOFF.md`), 0 after the tool's exceptions (its second exception's term is
  retired[8]); the forgiven index is retired[3]: 321 raw lines, 2 after exceptions (`LICENSE:189`,
  `README.md:45`, the two authorship lines; the 316 in `ClassicalLean/`, 2 in `ClassicalLean.lean`
  and 1 in `records/` are forgiven), so the pinned after-exceptions value is 2; no other index.
  Planted controls: (1) line 25 of `records/rounds/20261007T201500Z__round-33-clean-tree.md`, copied
  by `sed` into a scratch file outside the tree, is found there (retired[8] raw 1); (2) over the 159
  Lean files, after exceptions 0 on every index and retired[3] raw 318 = forgiven 318, and the tool
  itself prints PASS, 158 files, 0 hits; (3) 15 scratch lines, one per alternative of the secret
  pattern and one per range of the IP pattern, built from the alternatives by `plant_patterns.py`,
  are each found by `grep -E` with the order's pattern (11 of 11, 4 of 4). The four patterns are
  extracted from the order copy by `mkpatterns.sh` into `patterns.sh`, never retyped; the order copy
  matches neither its own secret nor its IP pattern (`mkpatterns.out`).
* The order copy: `cp` out of the lane works for dustin (`cptest.sh`: the copy's hash equals the
  pin); the copy's sha256 is the lane file's and `cmp` returned equal; its timestamp
  `20261103T123021Z` is the lane file's mtime (`ds_stat`), as MERGE-6's was.
* The RF rows: MERGE-6's push note and this order's two rows were written by
  `~/lean/public1-checks/rf_rows.py` and checked by `rf_check.py` against `24a75a3`'s files
  (`rf-check.out`), with a planted fault in each file failing as it should
  (`rf-check-control.out`, by `plant.py`, MERGE-5's unchanged).
* The new text of this commit (the order copy, this file's first part, the note and the two rows)
  through `vocab_count.py`: no index matched (`rf-vocab.out`).

## Tree state

No whole-library gate runs before G; the gates of this round run on the clean tree at G, the last
commit outside `records/`, and are quoted in this round's second part. The check at this first
commit is check_records on the staged tree.

First part written before the commits; commit hashes are added at close, below.
