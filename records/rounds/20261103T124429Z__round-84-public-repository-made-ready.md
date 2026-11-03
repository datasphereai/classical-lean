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

## Second part (written at close, 2026-11-03)

### The cited files (step 4, commit `2e65957`)

`records/scripts/` holds the 17 scripts, outputs and witness notes in order subfolders and
`records/plan/` the plan and the bridges file, each copied by `step4_copy.sh` and byte-identical to
its pinned source (sha256 and bytes equal to the order's pins, `step4_copy.out`), the seven lane
files by `cp` out of the lane. The map `records/scripts/README.md` is generated from the same pins
table (`pins.tsv`, by `step4_map.py`): one row per copied file with its cited names, the file here,
its origin, bytes and sha256; one row for the folder GamblersRuin line 133 cites; one row for each
of the five cited repository files; one row for `reviews/stmt-j2.md`, which survives nowhere. The 17
bare `checks.py` citations were re-attributed by reading the order word on each line (`step1`'s
grep output, in the session): all as the order lists. Checks (`step4_prescan.out` at the sources,
`step4_checks.out` in the tree): secret, address and IP patterns 0, 0 and 0 over the 19 files and
over the map; the host pattern 6 lines in the scripts (LEAN-25 line 158, LEAN-31 line 90, the plan's
search script lines 4, 9, 290, 566), 9 in the plan, 14 in the bridges file, and on the map exactly
the rows whose origin column names a box (14 rows, compared as line sets); `vocab_count.py` no
index over the 19 files and over the map (retired[8] 0 in the plan and the bridges file); the
network words on two lines, both Mathlib's GitHub remote in a quoted shell command.

### The README (step 5, commit `67e9a38`, G)

`README.md` is 115 lines, from `README-draft.md`, in the order's sequence of sections. The build
block is the old README's lines 17 and 18 unchanged; the "how to check" block holds `HANDOFF.md`
lines 48, 49, 50, 51 and 53 byte for byte, `python3 -I tools/witness_gate.py` from line 1309, and
the drift command from `ci.yml` line 61 without its `|| exit 1`; line 52's command is absent.
"Lean 4" is written as the toolchain string `leanprover/lean4:v4.34.0` so that no bare `4` appears,
and "gate 7" as "the seventh gate", since the order's integer rule allows neither digit.
`readme_check.py` PASS on every rule (`readme-check.out`: line count, no local path, no host name,
the three counts each only with their defining words, the three forbidden counts absent, the version
string equal to `lean-toolchain`'s, the build block, the seven command lines each a substring of its
source line with all seven present, every integer allowed, "the lane" and "API-CREDIT-1" once each in
the defining paragraph), and its four planted faults each FAIL (`readme-check-control.out`: `3932`,
a `/home/` line, line 52's command added, `5747` added). Drift PASS before the commit
(`pre-G-drift.out`). The new-text gate over the `+` lines of `git diff 24a75a3` before the commit
(6422 lines, `preG-newtext-vocab.out`): no index matched; the licence index has no hit because the
authorship line is unchanged context, not an added line; the secret and IP patterns 0; addresses the
two allowed only (`git@github.com` 2, `noreply@anthropic.com` 5, all in the order copy).

### The gates at G (`67e9a38`), clean tree, expected beside measured

Expected results: `expected.txt`, sha256
`2031df1edd2f512457e130611fef844a772ef84074063691b6b76a2ff7d2c2c2`, written before the gates ran.
Each gate ran through `run.sh` (MERGE-6's with its one `D=` line changed, `diff` one line) under the
12 GB cap (`runs.log`), one at a time, by `gates.sh` (`gates.log`, rc 0).

| gate | expected | measured |
|---|---|---|
| empty diff | `git diff --stat 24a75a3 G` over the Lean tree, `tools`, `.github` and the lake files: nothing | 0 lines (`G-diffstat.out`) |
| `G-build` | 4211 jobs, 0 warnings | `Build completed successfully (4211 jobs)`, 0 `warning:` lines; 1 s, since no Lean file changed and MERGE-6's build of this tree was in `.lake/` |
| `G-axiom` | PASS 3931 | PASS 3931, 0 scoped exceptions |
| `G-sorry` | PASS 158 | PASS 158 |
| `G-records` | PASS 158, 1 exemption | PASS 158, 1 exemption (`Simplex/Hessian.lean`) |
| `G-banned` | PASS, 158 files and the root | PASS, 158 files and the root, 0 hits |
| `G-drift` | PASS no drift | PASS no drift |

The type dump, VacuityGate, the witness gate and gate 7 were not run: the empty diff is the proof
that nothing they measure changed.

### The history and GitHub check (step 7, `history-check.out` and `history-check-g.out`)

Reported for Dustin, not acted on. (a) `git ls-remote github`: `HEAD` and `refs/heads/master` at
`24a75a3…` only. (b) `git log --all -p` over 480 commits (427186 lines): two indexes of the term list
match, retired[3] (729 lines; the exceptions do not reach a `+` diff line) and retired[8] (16 lines
raw, 0 after exceptions), no other; the secret and IP patterns 0; the address pattern
`noreply@anthropic.com` 522 and `git@github.com` 2, the 8 more than the order's 514 being the
order copy's 5 and 2 and the three new commit trailers; the planted control found 11 of 11 secret
alternatives, 4 of 4 IP ranges, 1 of 1 address and the retired[8] scratch line. (c) The 14 retired[8]
lines at HEAD (6, 6, 1 in the three `records/` files the order names, 1 in `HANDOFF.md`) are saved
with file and line in `history/retired8-lines.txt` and quoted in the report, for Dustin. (d)
Author and committer fields: 839 the owner's address, 121 `noreply@anthropic.com` (960 on 480
commits). (e) Tracked files at HEAD: secret 0, IP 0, addresses `noreply@anthropic.com` on 2 older
order files and the order copy's 5, `git@github.com` the order copy's 2; the host pattern 1881 lines
in 157 files (provenance). (f) 0 pull requests, 0 issues, 0 artifacts, 0 releases; 82 runs, by
branch master 18, cloud-math-1 to -7 8, 9, 9, 7, 9, 10, 10, cloud-ci 1, cloud-ci-fault 1; 78
distinct heads, 77 ancestors of `github/master`, 1 not: `7992041…`, which is the `cloud-ci-fault`
branch's head (the order's text calls it the `cloud-ci` head; the hash and message are the order's);
the compare API lists 1 commit, its API patch 14 lines and its `git show` 32 lines ("CI planted
fault: a sorry theorem; never merge", author and committer `noreply@anthropic.com`, 2 files):
secret 0, IP 0, host 0, no index; `refs/remotes/github` holds `master` only before and after the
fetch by hash. (g) Every run's log: `gh run view --log` printed nothing with exit 0 for every run on
this box's `gh` 2.45.0 (82 empty files, `history-check.out`), so the logs were fetched again as
zips through `gh api repos/…/actions/runs/<id>/logs`, each unzipped into its own empty folder
outside the tree (`runlogs.sh`, `history-check-g.out`): 78 fetched, 46954 lines, secret 0, IP 0,
no index, no address; the host pattern 4410 lines, all the runner's `/home/` and `/opt/` paths;
4 cancelled runs (41359306486, 41139843071, 41137378481, 39345774451) returned an empty zip and have
no log to scan. The switch waits on Dustin's reading of the 14 lines.

### Misses

* Two sessions ran this order at once (07:33 to 07:52 EST): a second Claude Code session
  (`session_01HgueTXQnTobeGGgAmcPH11`, pid 2974231) was started with the same launch paste while this
  one was in step 3; it shared `~/lean/public1-checks/` and the worktree, ran its own step 1 and
  overwrote `vocab_count.py` at 07:49:27 with its own version. This session noticed in step 4 (the
  counter printed a usage error it never had), stopped and reported the pids; Dustin ended the second
  session, which left `NOTE-two-sessions-collision.md` and its files under their own names. The
  counter was restored from this session's own text (the other kept as
  `vocab_count-second-session.py`) and the step 2 control and planted controls re-run with the same
  numbers (retired[3] 321 raw, 2 after; retired[8] 14 raw, 0 after; controls identical), the re-run at
  RF `2f952eb` (530 tracked files; the first run at `24a75a3`, 528, kept as
  `before-restore/vocab-tracked.out`). Outputs dated before 07:49 came from the original, later ones
  from the restored copy.
* `gh run view --log` was trusted once: its 82 empty logs scanned as "0 lines, 0 hits" before the
  zero was questioned; the API zips replaced it, with the runner paths as the positive control.
* The step-1 settings command held `python3 -I -c 1` (a no-op) and two heredoc edits held an empty
  `python3 -` (no-ops); the launch rule forbids both forms. Nothing was computed by them.
* One combined Bash call was denied as a whole and re-issued in parts; the first run of the
  `rf_check.py` control passed `plant.py` two arguments (nothing planted) and was re-run; a
  `git add records` was blocked by the bulk-add guard and the paths were staged by name; the
  `step4_checks.sh` awk first read the wrong table cell and the map's folder citation sat in a lane
  row, both fixed before the step 4 commit.
* The first push-review file had a defect: in `push-review.sh` the pattern variables were sourced but
  not exported, so inside each `bash -c` the four `grep -cE` calls ran with an empty pattern and counted
  every line (5799 over the 19 files, 6540 over the `+` lines, printed as if they were secret and IP
  counts). It was filed before the defect was seen and is kept in the lane as
  `lean/PUBLIC-1/data/PUBLIC-1-push-review-superseded-5e9c0aed.txt`, the record of the miss; the
  corrected file (the script exports the variables; a control shows the subshell finds 11 of 11 planted
  secret lines) is `lean/PUBLIC-1/data/PUBLIC-1-push-review-r2.txt`, the push review that counts, and
  the report names both with their hashes. This bullet is a records-only commit after the close.

### Commits

`2f952eb` (records first), `2e65957` (the cited files), `67e9a38` (README, G) and this records
commit. Nothing pushed; the push is Dustin's after claude-ai's push review, and the visibility
switch after his reading of the 14 lines.
