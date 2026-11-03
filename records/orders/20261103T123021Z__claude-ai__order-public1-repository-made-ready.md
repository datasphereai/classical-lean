# PUBLIC-1 order: the repository made ready to be public

For a plain Claude Code session on DSMain, as dustin, in tmux `cc`. Written by claude-ai on 2026-11-03 in
Project LEAN, to the lighter procedure (store row 20261026-063). Six cold passes on helios, each FAIL and
each applied: pass 1 (`~/public1-review-1/out1/review.md` 194b9ebe: citations spanning more lines than
stated; history and GitHub never searched), pass 2 (`~/public1-review-2/out2/review.md` b2695057: the order's
own text carried retired words that a verbatim copy would commit; new text unchecked against the private
list), pass 3 (`~/public1-review-3/out3/review.md` b0de3b59: the copied files never scanned for secrets; the
vocabulary counter without a control; two cited "files" that are Lean code), pass 4
(`~/public1-review-4/out4/review.md` c3a8c1b3: history and GitHub objects never scanned for secrets; the scans'
patterns not written down; a wrong attribution in the map; lane files not copyable as written; the README
never seen by a reviewer before the push), pass 5 (`~/public1-review-5/out5/review.md` 5ce905fe: the order's
own pattern text tripping its patterns; address counts that came from an untracked folder; grep (c)'s Lean names
unlisted; unreachable GitHub commits scanned only at their heads; `HANDOFF.md` gate lines off by one; eight
more). Pass 6 (`~/public1-review-6/out6/review.md` c26a8785): FAIL, three MAJOR (the secret pattern too
narrow for the keys this project could hold; a function name the tool does not export; an integer rule the
README could not satisfy) and seven MINOR, all applied here with the measurements re-run (0 secrets and 0
IPs under the wider patterns, in history, at HEAD and in the 19 files). No seventh pass: claude-ai's ruling,
veto open (store row 20261103-016): passes 4 to 6 found no missing check of the tree, only wider patterns
and text defects, and two readers still stand between this order and the switch, claude-ai's push review
of the README text itself and Dustin's reading of step 7's lines. Dustin's decisions, 2026-11-03 (store
rows 20261103-008 and -010): `datasphereai/classical-lean` goes public, right after LEAN-39 and before the
first tier-3 extraction; no rewriting of history where it can be avoided; the stray branches are already
deleted. This order makes the tree ready; the switch itself is Dustin's, after the push and after his reading
of step 7's lines (step 9).

**What kind of order this is.** A small documents-and-records order. It changes `README.md` and `records/`
only: no module, no theorem, no proof, no `tools/`, no CI. Its risk is to the record, which once public is
permanent, so every byte it adds is checked against the owner's private list and against the secret, address
and host patterns written below before it is committed; then the gates that can see a records change, and
claude-ai's push review, which sees the README text itself.

**When to start.** Any time (LEAN-39 is done, reviewed PASS, row 20261103-013). Not between 01:45 and 05:45.
About one hour.

**Launch check.** This session was started with `CLAUDE_CODE_DISABLE_AUTO_MEMORY=1`. Print it first; if it is
not `1`, stop and say so. Dustin's launch paste adds two deny rules to the session's permissions,
`Bash(gh repo edit:*)` and `Bash(git push:*)`, so the switch and the push are mechanically out of reach;
print `claude config` or the settings file's deny list if you can, and say whether they are there. Every
script you write is a file in `~/lean/public1-checks/`, run with `python3 -I <file>` or `bash <file>`; no
`python -c`, no python reading standard input.

**The patterns** (used by steps 4, 7 and 9; every grep is `grep -nE`, counts reported, matches of the secret
pattern are a stop):
- secret: `AK[I]A|s[k]-(ant|proj)-|sk-[A-Za-z0-9]{10}|gh[ousrp]_[A-Za-z0-9]{20}|githu[b]_pat_|BEGIN [A-Z ]*PRIVAT[E] KEY|BEGIN (RSA|OPENSSH)|[Pp][Aa]sswor[Dd] *[:=]|Beare[r] [A-Za-z0-9._-]{20}|xox[baprs]-|AI[z]a[0-9A-Za-z_-]{30}`
  (Anthropic, OpenAI, GitHub, AWS, Google, Slack and bearer tokens, private-key headers, password
  assignments; written so that this line does not match itself)
- address: `[A-Za-z0-9._%+-]+@[a-z0-9-]+\.[a-z]{2,6}\b` (a lowercase domain, so Lean's `@Finset.sum` and
  the like do not match); the allowed addresses are exactly `noreply@anthropic.com` and `git@github.com`, any
  other match is a stop
- IP: `192\.168\.[0-9]+\.[0-9]+|\b10\.[0-9]+\.[0-9]+\.[0-9]+\b|\b172\.(1[6-9]|2[0-9]|3[01])\.[0-9]+\.[0-9]+|\b100\.(6[4-9]|[7-9][0-9]|1[01][0-9]|12[0-7])\.[0-9]+\.[0-9]+`
  (the private ranges and the Tailscale range; a match is a stop)
- host or path: `DSMain|helios|node2|/home/|/opt/|/data/|~/` (counted and listed; never a stop by itself)

## Goal

A reader on GitHub who is not Dustin can open the repository, understand in one page what it is and is not,
build it, run the gates a stranger can run, and find inside the repository every script, output, note and
plan the library's docstrings cite as evidence for their hypotheses and witnesses, or, for the one file that
no longer exists anywhere, a row that says so.

## What is already true (measured by claude-ai, 2026-11-03, 06:03 to 07:05 EST, on DSMain over ssh from helios; store rows 20261103-008, -010, -011, -013)

- Master is `24a75a34310ebc0d4022bb91cd2edda8fc86ff25` on both remotes (MERGE-6, CI run 41612812385 green, row
  20261103-004); the worktree `~/lean/classical-lean-paper-crypto` is on branch `merge-6` at `24a75a3`,
  porcelain empty (LEAN-39 ended with it so, row 20261103-013). `git diff --quiet e8398c2 24a75a3 --
  ClassicalLean ClassicalLean.lean` is true; step 1 widens that check to `tools`, `.github`, the lake files and
  the toolchain: the library at master is MERGE-6's G, so MERGE-6's gate outputs in `~/lean/merge6-checks/`
  describe it.
- GitHub: `datasphereai/classical-lean`, visibility PRIVATE, description "Lean 4 library of classical
  mathematics, built on Mathlib", license Apache 2.0 (`LICENSE` present), default branch `master`, and after
  Dustin's deletions of 2026-11-03 (04:48 and 06:22 EST) `master` is its only branch; 0 pull requests, 0
  issues, 0 Actions artifacts, 0 releases, wiki and pages off; 82 Actions runs, whose logs become public with
  the repository. Their head commits by branch (`gh run list -L 200 --json headSha,headBranch`): master 18,
  cloud-math-1 to -7 62 in all, every one of those merged into master; `cloud-ci` 1 and `cloud-ci-fault` 1
  (`7992041`, 1 commit ahead of master; `ed0bccb`, behind master, so on it). Of the 78 distinct run heads,
  77 are ancestors of GitHub's master (`git merge-base --is-ancestor <sha> github/master`; the compare API
  agrees, 0 commits ahead for each) and one is not: the `cloud-ci` head `7992041`, 1 commit ahead. A first
  measurement against the worktree's local `master` branch, which is stale at `d723fbf`, said 11; that was
    wrong, and the store's row 20261103-015 logs it. The one commit stays fetchable by hash on GitHub after the
  branch's deletion; measured: its message is "CI planted fault: a sorry theorem; never merge" with Claude's
  trailer lines, its author and committer are `noreply@anthropic.com`, it touches 2 files; step 7 fetches it
  by hash and reads its diff and message through the patterns, and re-runs the enumeration against
  `github/master` (an absent object makes `merge-base` exit 128, which the script treats as not an ancestor
  and says so). Commit authors: dustin 415, Claude
  62; of the 954 author and committer fields on the 477 commits, 833 hold Dustin's Yahoo address and 121
  `noreply@anthropic.com`; Dustin's decision: they stay, no rewrite.
- History, measured over `git log --all -p --format='%H%n%B'` (every diff and every message of the 477
  commits): the first commit is `333b69a`, 2026-10-07 16:21 EDT, after order LEAN-5 removed the retired
  framing's files and replaced its words with the placeholders `[retired name]`, `[retired term]` and
  `[surname]` (`records/README.md` line 69); the two retired project nouns match 0 commits; the secret
  pattern as written above 0 lines; the IP pattern as written above 0 lines; the address pattern matches only
  `noreply@anthropic.com` (514 lines). Dustin's private term list (`~/.config/classical-lean/banned-terms`, JSON: 31 `retired` and 8
  `provenance` regexes, 2 `exceptions`; never printed or copied; `tools/banned_vocab_scan.py --list` prints
    it and is never run) matches two indexes in the whole history, both known: one whose matches at HEAD are
  all on lines the tool's exceptions forgive (321 raw lines; the tool reads `.lean` files only and reports
  PASS, 0 hits, at HEAD), called the forgiven index below, and retired[8] on 16 lines in history and 14 at HEAD, 13 under `records/` and 1 in
  `HANDOFF.md` (by file: `records/orders/20260924T023500Z__claude-ai__order-g7-bridges-apparition.md` 6,
  `records/rounds/20260924T160346Z__round-23-bridges.md` 6, `records/rounds/20261007T201500Z__round-33-clean-tree.md`
  1, `HANDOFF.md` 1), outside the tool's scope. Step 7 lists those 14 lines for Dustin in the report (the
  report is in the lane, not the repository). One more line for Dustin's eye, not on the list: `records/orders/20260923T122713Z__claude-ai__order-0923-pick-up.md`
  line 63 records, in plain words, that the old framing was dropped; it is the record and stays unless he says
  otherwise.
- Review, report and ruling citations in docstring prose (`cold review r80`, `review r6` and the like, by
  `grep -rnoE 'cold review [a-z]?[0-9]+|review r[0-9]+'`): 90 matches; those are the orders' review files in
  the lane, not copied, and the README says so in one sentence.
- Other searches, each measured over all tracked files at HEAD with the written patterns (`git grep` at
    HEAD, so untracked folders such as `.lake/` are not counted; an earlier count that included them is
  superseded): the address pattern gives `noreply@anthropic.com` on 2 lines and nothing else; the IP and
  secret patterns as written above 0; no `__pycache__` tracked. `git grep -nE 'records/|README' -- tools`
  hits one message string in `tools/banned_vocab_scan.py` (line 135) and nothing else, so no gate reads
  `records/` or `README.md` except `check_records` (below). Host names and
  local paths in `deploy/README.md` (lines 47 and 93) and `tools/test_breakit2_rules.py` line 4:   provenance, stay. 57 Claude Code session ids under `records/`:
  provenance, stay.
- What the library's docstrings cite that a reader cannot reach, by three greps the push review repeats:
  (a) `grep -rnE 'lean[0-9]+-checks|LEAN-[0-9]+-[a-z0-9]*\.py|\blane\b|DSMain|helios|/opt/|/data/|/home/|~/' ClassicalLean ClassicalLean.lean`:
  84 lines in 40 modules (row 20261103-011), nearly all "lane's API-CREDIT-1 work" (51 lines, naming where
  the Claude Opus 5.5 drafts came from) and lane or DSMain file names; "DSMain" twice (ChiSquared line 41,
  GamblersRuin line 133). (b) `grep -rnoE '[A-Za-z0-9_./~-]+\.(py|txt|out|jsonl|sh)\b|\bw[0-9]+/' ClassicalLean ClassicalLean.lean`,
  distinct names with line counts: `Fact.out` 24 and `hp.out` 1 (Lean code: Mathlib's `Fact.out` projection
  and a hypothesis named `hp`, not files; read, and left out), `checks.py` 17, `MATH-PLAN-library-2-checks.py`
  11, `lean/LEAN-36/data/witnesses.txt` 6, `lean/LEAN-31-checks.py` 5, `lean/LEAN-30-checks.py` 4,
  `lean/LEAN-29-checks.py` 4, `~/lean/lean25-checks/checks.py` 3, `w149-series.py` 2, `w143-runs.py` 2,
  `tools/check_sorry.py` 2 and `tools/banned_vocab_scan.py` 1 (repository files), `w145-cycles.py` 1,
    `LEAN-28-check80b.py` 1, `chk2.out` 1, `checks95.py` 1, `checks109.py` 1, and the folder
  `~/lean/lean29-checks/` 1 (GamblersRuin line 133; the map gets a row for it, pointing at the LEAN-29 copies).
  (c) `grep -rnoE '[A-Za-z0-9_./~-]+\.(md|json|csv|tsv|log|toml)\b' ClassicalLean ClassicalLean.lean`: `Real.log` 427, `-Real.log` 28,
  `HasDerivAt.log` 2, `Nat.log` 1, `hsum.log` 1, `ContinuousOn.log` 1 (Lean code, the logarithm, not files; left
  out), `MATH-PLAN-library-2-bridges-2.md` 15, `ROADMAP.md` 11, `HANDOFF.md` 2 and a `records/rounds/` file 5
    (repository files; `ClassicalLean.lean` adds nothing),
  `reviews/stmt-j2.md` 1 (Wolstenholme line 18, order G-10 of September 2026, before this repository's first
    commit; searched and not found in the repository, the lane, DSMain's `~/lean/` folders, or the pre-LEAN-5
  full-history bundle `~/lean/archive/classical-lean-full-history-20261007.bundle` (127 commits, cloned to
  scratch and `git log --all --name-only` searched: no file named `stmt-j2`)), and the plan's rows are cited 41 times as "the plan's row" (the plan is `MATH-PLAN-library-2.md`,
    in the lane). The 17 bare `checks.py` lines name their order on the
  same line or in the bullet list they sit in: LEAN-23 (Simpson 41, LinearProgram 55, EulerMaclaurin 46,
  MinMax 68), LEAN-24 (Sufficiency 140, NeymanPearson 79, JamesStein 48, GlivenkoCantelli 47, MethodOfTypes
  68), LEAN-25 (the three `~/lean/lean25-checks/` lines), LEAN-27 (GeneralizedLeastSquares 43,
  EffectiveSampleSize 77 and its bullets at 80 and 83, MinMax 39, Kantorovich 47, whose output is `chk2.out`),
  LEAN-28 (GamblersRuin 85, FiniteGame 87). Every cited file that exists was located and pinned (sha256,
  bytes, origin):
  - `~/lean/lean23-checks/checks.py` `f8f51fcd455ba5c608fc71159058c7b4427892614b343dbb3e491e7adcdcba67` 15481, LEAN-23, DSMain (imports numpy)
  - `~/lean/lean24-checks/checks.py` `b20201bf10f4d805a5574669c2c12e024f0f5f7f8e6c8f2b167276115fcc1b8f` 16908, LEAN-24, DSMain
  - `~/lean/lean25-checks/checks.py` `8451818148d5162d1f914de124d0afc3f10913eb3febcb77ae26a380d88f6116` 10522, LEAN-25, DSMain
  - `~/lean/lean27-checks/checks.py` `d35de1f56e94bc49d69df19c5c684a27b0f4573dabc80a63ec70e872999cafc7` 8938, LEAN-27, DSMain
  - `~/lean/lean27-checks/chk2.out` `c23af4bde3778bbb784c13995e746087100ed1aef3b5b66984d6a518de7fb911` 2916, LEAN-27, DSMain
  - `~/lean/lean28-checks/checks.py` `cafa7dc8519697738e08ad2e8b1b441642aeb89fc30650430db1318ab10f25cb` 17271, LEAN-28, DSMain (the one with line `85.affine`; LEAN-28's report line 116)
  - `/opt/datasphere/lane/inbox/threads/staging/lean/LEAN-28-check80b.py` `e22807bc6b50368749b4e00f24aae2e4932f2684fd2894d5ce8c131aded21e48` 3257, LEAN-28, lane
  - `/opt/datasphere/lane/inbox/threads/staging/lean/LEAN-29-checks.py` `8e82051348b8e71e67636322dd406d0f791c319d9313e9b993acf578ad023dc5` 21676, LEAN-29, lane
  - `~/lean/lean29-checks/checks95.py` `b531f3e0326617e7f1f81fe9dcbc9c138e1c50ffb2d708a203cf61388e96c3ee` 3497, LEAN-29, DSMain
  - `/opt/datasphere/lane/inbox/threads/staging/lean/LEAN-30-checks.py` `6af2e0421ffd01df5a8ea28f094945b2173b5729356c3ac500e06fc3c02ddcf7` 29272, LEAN-30, lane
  - `/opt/datasphere/lane/inbox/threads/staging/lean/LEAN-31-checks.py` `0038352f642b79804c03d9da731efd4ac8857ae8ab38c1f0326e3c7f586dc936` 26708, LEAN-31, lane
  - `~/lean/lean32-checks/scripts/checks109.py` `12b8eb0b66644d5846b5c1f7b100424b3c72b75ef8f0727aa76f52824bb4e5bf` 2766, LEAN-32, DSMain
  - `/opt/datasphere/lane/inbox/threads/staging/lean/LEAN-36/data/witnesses.txt` `2bc14e815ecf3ceb8f2bbe34268aa2831ca7884ed7015fe6f683e838dc719d17` 6578, LEAN-36, lane
  - `~/lean/lean37-checks/w143/runs.py` `45f469e02d7ff6b2dd5a1c1486f6969863cc62a6dc5221be54d056bf004c5e77` 448, LEAN-37, DSMain
  - `~/lean/lean37-checks/w145/cycles.py` `d5f62c79684d9361f868b987e249aea1fbcab551a521d3088c1477d012ae11e0` 693, LEAN-37, DSMain (LEAN-37 ruling-1's pin)
  - `~/lean/lean37-checks/w149/series.py` `0e8145adf49f11793ba7e0a56c694314def7e7da5fe150dde575c7613502fea3` 1139, LEAN-37, DSMain (LEAN-37 ruling-1's pin)
  - `~/lean/lean27-checks/MATH-PLAN-library-2-checks.py` `92eedbc6598361a06a50bdf3a1b4fa1698c1d1d7a3dfe783cc79dd9c1c38307e` 89055, the plan's search script, DSMain (byte-identical to the lane's `inbox/threads/staging/MATH-PLAN-library-2-checks.py` and to the copies in `lean28-checks/` and `vacuity3-checks/`, measured)
  - `/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library-2.md` `6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166` 71296, the plan, lane
  - `/opt/datasphere/lane/inbox/threads/staging/lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md` `4fd72d941e5f057ca1ad1ad65b2cd899601a9f08b3e2db816218e1010c08bae5` 70695, the bridges file as of LEAN-39 (rows 154 to 175; it keeps growing, so this is a dated snapshot and its copy says so), lane
    Over all 19, measured with the patterns as written above: 0 lines matching the secret, address or IP
  patterns; 6 lines matching the host pattern (1 in lean25's `checks.py`, 1 in `LEAN-31-checks.py`, 4 in `MATH-PLAN-library-2-checks.py`):
  provenance, listed by step 4. The plan and the bridges file are measured by step 4 the same way. `cp` out of
  the lane works for dustin (measured on `LEAN-29-checks.py`: the copy's hash equals the pin). 96 files under
  `records/`, `HANDOFF.md`, `ROADMAP.md` and `tools/` also name hosts and
  scratch paths; those are the record of where work was done and stay.
- Dustin's rule (row 20261103-010), no history rewrite where avoidable, is applied to docstrings too: 84 lines
  in 40 modules is a rewrite, so the docstrings stay as written (GamblersRuin line 133's "outside the
  repository" and the "lane" wording predate the copies, and the scripts README says so), every cited file
  is copied in, and the README explains the words a reader will meet.
- `README.md`, 45 lines, sha256 `45a197478de20edd973bd13b6065804c125631e45660de3c9147dcf306b4f690`, last
  changed 2026-10-07 (`1d37a3a`); its build block is `lake exe cache get   # download the prebuilt Mathlib
  files (needs network)` then `lake build           # check every proof in the library` (lines 17 and 18). It
  names four gates and lists ten areas; `ClassicalLean/` has twelve folders: Algebra, Analysis,
  Combinatorics, Geometry, GoldenRatio, InformationTheory, Logic, NumberTheory, Order, Probability, Simplex,
  Statistics. `HANDOFF.md` `49584a177aa12f0208db23b6444305670dcaf9cf1842be60784a6c4ab8993f99` (1619 lines;
  gate commands at lines 48 to 53: `lake build`, `lake env lean tools/AxiomGate.lean`, `lake env lean
  tools/VacuityGate.lean`,    `python3 tools/check_sorry.py ClassicalLean`, `python3 tools/banned_vocab_scan.py
  ClassicalLean`, `python3 tools/check_records.py`; the `elan` pointer at lines 13 and 14; the witness gate at line 1309: `python3 -I
  tools/witness_gate.py` from the repository root, "whole library about 27 minutes", line 1310 naming the
  owner's box), `ROADMAP.md` `497af0e9566f4528f3d4303dd08824aad19659a7ddf7190ea978d57212f20f6d` (1729 lines),
  `records/README.md` `b6556dee3acbd3e6b6d3174bb01b4a8ac41d3191c1aa0b695d6a34341b205123` (72 lines).
  `records/` holds `bridges/` (54 files), `orders/` (62), `rounds/` (68), `CLAIMS.md`, `rules.toml`; no
  `scripts/` or `plan/` folder. CI (`.github/workflows/ci.yml`) runs AxiomGate (line 36), check_sorry (39),
  VacuityGate (42), `compile_rules.py check` (55, 57) and `python3 tools/compile_rules.py drift
  records/rules.toml HANDOFF.md || exit 1` (61), after a build step (quote its line in the report); not the
  witness gate, the banned scan, check_records or gate 7. `tools/banned_vocab_scan.py` reads `*.lean` under
  its folder argument and the `.lean` file beside it (lines 100 to 108), exits 2 on no files and, measured,
  exits 2 when the term file is absent (`HOME=$(mktemp -d) python3 -I tools/banned_vocab_scan.py
  ClassicalLean; echo $?` gives 2). Neither `tools/witness_gate.py` nor `tools/VacuityGate.lean` reads
  `records/` or `README.md` (grep: prose only);
  `tools/check_records.py` reads `records/rounds/*.md` and `records/orders/*.md` only (its lines 62 to 65), so
  the copies under `records/scripts/` and `records/plan/` do not enter gate 6.
- Counts at `24a75a3` (MERGE-6's gates, `lean/MERGE-6/report.md`, library code identical): 158 modules; 3931
  theorem constants under the `ClassicalLean` namespace as AxiomGate counts them (auxiliary lemmas included);
  `lake build` 4211 jobs, 0 warnings; whole-library witness gate 212 witnesses OK. Lean toolchain
  `leanprover/lean4:v4.34.0` (`lean-toolchain`); Mathlib pinned in `lake-manifest.json` at `inputRev`
  `v4.34.0`. The owner's runs cap Lean at 12 GB (`run.sh`); a full build has fit under it.

## Scope

- Branch `public-1` from `24a75a3`. Nothing pushed. No sudo. Never rebase.
- You may change: `README.md`; `records/` (new folders `records/scripts/` with 17 copied files in subfolders
  and a `README.md`, and `records/plan/` with 2 copied files; this order's copy; a round; CLAIMS and INDEX
  rows). Nothing else: no file under `ClassicalLean/`, no `ClassicalLean.lean`, no `HANDOFF.md`. Needing to
  change anything else is a stop.
- `gh`: only `gh repo view datasphereai/classical-lean --json visibility`, `gh run view`, `gh run list`, `gh pr
  list`, `gh issue list`, and `gh api --method GET`. No `gh repo edit`, no `git push`. The switch is Dustin's.
- Your files: `~/lean/public1-checks/`. Lane reads: `ds_read` and `ds_hash` through the connector, and `cp`
  of the seven pinned lane files (hash equality required; a difference is a stop). Lane writes through the
  connector: the report (`ds_file`, project `lean`, job `PUBLIC-1`, kind `report`) and the push-review file
  (subdir `data`, name `PUBLIC-1-push-review.txt`, through the drop folder: copy the file to
  `/opt/datasphere/drop/PUBLIC-1-push-review.txt`, then `ds_copy_in` with its sha256; the reply's path must be
  `inbox/threads/staging/lean/PUBLIC-1/data/PUBLIC-1-push-review.txt`).
- Off limits as in every order: `~/lean/classical-lean`, every earlier order's folder (read only; you may `cp`
  the pinned files out of `~/lean/lean23-checks/`, `lean24-checks/`, `lean25-checks/`, `lean27-checks/`,
  `lean28-checks/`, `lean29-checks/`, `lean32-checks/`, `lean37-checks/` and `merge6-checks/`), `~/api-credit/`
  and `/tmp/claude-ai-*` (read only), `/data/api-credit/`, Dustin's `~/.config/classical-lean/banned-terms`
  (never printed or copied; scripts read it and print counts and indexes only, with one exception in step 7(c)),
  every GitHub branch (fetch only).
- Lean runs: one at a time, through `~/lean/public1-checks/run.sh`, a copy of `~/lean/merge6-checks/run.sh`
  with its one `D=` line changed to `/home/dustin/lean/public1-checks` (12 GB cap, refuses 01:45 to 05:45 and
  while a `lean` process runs, logs to `runs.log`).

## The work

1. **Check.** Launch variable; `git fetch origin`; `git fetch github`; in the worktree `git rev-parse HEAD` is
   `24a75a3…` and porcelain empty; both remotes' master `24a75a3…`; `git ls-remote github` shows `HEAD` and
   `refs/heads/master` only; the four document hashes above; the 19 files' sizes and sha256 as pinned (the
   lane ones through `ds_hash`); grep (a) gives 84 lines, grep (b) and (c) the names and counts listed;
   `gh repo view datasphereai/classical-lean --json visibility` is `PRIVATE`; `git diff --quiet e8398c2 24a75a3
   -- ClassicalLean ClassicalLean.lean tools .github lakefile.toml lake-manifest.json lean-toolchain` true. If
   anything differs, stop. Then `git checkout -b public-1`.
2. **The vocabulary counter and its control.** Write `~/lean/public1-checks/vocab_count.py` (a file): it
      imports `load_terms` and `compile_terms` from `tools/banned_vocab_scan.py` (`sys.path`, not a copy; the
   tool exports `load_terms`, `compile_terms` and `main`, no matcher), so the regexes and the exceptions are
   the tool's own, and matches lines the way `main` does (quote `main`'s matching loop with its line numbers
   in the report; the exception rule is the tool's, a hit forgiven only when it lies inside a match of its
   context on the same line); for the files or diff lines it is given it prints,
   per index, the count of matching lines and the file and line number of each, never the pattern. Control,
   before any commit: run it over all tracked files at `24a75a3`; expect retired[8] on 14 lines (13 under
   `records/`, 1 in `HANDOFF.md`), the forgiven index with 321 raw lines and its after-exceptions count (print
   both; record the second as the pinned value for steps 4, 5 and 9), and no other index. Then a planted
      controls: (1) copy one of the 14 retired[8] lines from `records/` into a scratch file outside the tree
   (never a line from the list) and require the counter to find it there; (2) over `ClassicalLean/**/*.lean`
   and `ClassicalLean.lean`, the counter after exceptions must give 0 on every index, which is the tool's
   measured PASS, and its raw count on the forgiven index must equal its forgiven count there; (3) over the
   patterns, one scratch line per alternative of the secret pattern and one per range of the IP pattern,
   each written from the alternative itself (the Anthropic prefix followed by letters, and so on; none of them spelled out in this order), must each be found
   by the grep. A mismatch is a stop. Save all outputs.
3. **Records first.** The header's last pass line must read a hash and a verdict, not a placeholder; a
   placeholder is a stop (claude-ai fills it before filing). Copy this order to
   `records/orders/<UTC stamp>__claude-ai__order-public1-repository-made-ready.md` verbatim (hash equal to the
   lane's); open round N+1 (`records/rounds/`, the next number after the last) in the form of round 83; add
   this order's row at the bottom of `records/orders/INDEX.md` and `records/CLAIMS.md` (the CLAIMS row's last
   cell ends `not pushed, the push is Dustin's after claude-ai's push review |`), checked by a script with a
   planted-fault control as MERGE-6 did (`rf_check.py`). Before the commit, run `vocab_count.py` over the order
   copy, the round file and the two new rows: expect no hit on any index (the order text uses placeholders and
   names no list term); any hit is a stop, since the commit would put the word into public history. Commit
   (RF).
4. **The cited files into the record.** Make `records/scripts/` holding the 17 files in subfolders, named so
   each docstring citation maps to one of them: `LEAN-23/checks.py`, `LEAN-24/checks.py`, `LEAN-25/checks.py`,
   `LEAN-27/checks.py`, `LEAN-27/chk2.out`, `LEAN-28/checks.py`, `LEAN-28/check80b.py`, `LEAN-29/checks.py`
   (the lane's `LEAN-29-checks.py`), `LEAN-29/checks95.py`, `LEAN-30/checks.py`, `LEAN-31/checks.py`,
   `LEAN-32/checks109.py`, `LEAN-36/witnesses.txt`, `LEAN-37/w143-runs.py`, `LEAN-37/w145-cycles.py`,
   `LEAN-37/w149-series.py`, `MATH-PLAN-library-2/checks.py`; and `records/plan/` holding
   `MATH-PLAN-library-2.md` and `MATH-PLAN-library-2-bridges-2.md`; each byte-identical to its source (sha256
   equal to the pinned value; any difference is a stop). Then `records/scripts/README.md`: a table with
   columns "as cited in a docstring", "file here", "origin (order; box or lane path)", "bytes", "sha256", one
   row per file, listing every cited string of greps (b) and (c) that names a file (so a reader can go    from `lean/LEAN-29-checks.py`, or "order LEAN-24's `checks.py`", or "the plan's row", or the folder
   `~/lean/lean29-checks/`, to the copy), plus one row for `reviews/stmt-j2.md`: "cited by Wolstenholme line 18
   (order G-10, September 2026); not in this repository, its history, the owner's records or the archived
   full-history bundle; the docstring's claim of a cold review has no surviving file"; then one paragraph: these are the
   exact check scripts, outputs, witness notes and plan documents the library's docstrings cite, copied
   unchanged from the orders' evidence, run at the time of their orders and not maintained since (LEAN-23's
   needs numpy); the bridges file is a snapshot dated to this order and grows in the owner's private copy; a
   docstring that calls one of them "outside the repository" or "in the lane" was written before this copy;
   "the lane" is the owner's private work-order folder, "the lane's API-CREDIT-1 work" names the order under
   which proof drafts (ids like `d127-r1-s2`, not in the repository) were bought from the Anthropic Batch API
   in October 2026 and then adapted by the sessions the docstrings name; a host name in a docstring is one of
   the owner's machines; nothing in a proof depends on any of this. Then the checks, saved: over the 19 copied
   files (`records/scripts/*/*` and `records/plan/*`): (i) the secret, address and IP patterns (expect 0, 0
   and 0; a hit is a stop); (ii) the host pattern (expect 6 lines in the scripts, listed, plus the plan's and
   the bridges file's counts, listed); (iii) `vocab_count.py` (expect no index with a hit except the licence
   index on lines the exceptions forgive; retired[8] is measured at 0 in the plan and the bridges file; any
   other hit is a stop, reported for Dustin); (iv) `socket|urllib|requests|http` (reported). Over
   `records/scripts/README.md` separately: the secret, address and IP patterns 0; the host pattern exactly its
   origin column's rows; `vocab_count.py` no hit. Commit.
5. **README.** Rewrite `README.md`, under 130 lines, in its present plain style, from a draft you write to
   `~/lean/public1-checks/README-draft.md` first. Required content, in this order: what the library is (a Lean 4
   library of classical mathematics on Lean `v4.34.0` and Mathlib at the manifest's `v4.34.0`; every proof
   checked by Lean's kernel, and AxiomGate confirms each theorem rests on Lean's standard axioms only; whether
   a statement means what its prose says is not something Lean checks, and the witness gate and the records
      address that in part, nothing fully; built by the owner, named as `LICENSE` line 189 and the present
   README's line 45 name him, with Claude Code and claude.ai, the records being the history of how); what it is not (no claim beyond the theorems as stated;
   a statement can be vacuous or rest on a junk value, which is why VacuityGate and the witness gate exist;
   nothing here is advice); the counts, each defined and dated to `24a75a3`: 158 modules, 3931 theorem
   constants as AxiomGate counts them, `lake build` 4211 jobs; the twelve areas from the folder list above,
   one line each with two or three module names; how to build (the present block, lines 17 and 18, unchanged,
      plus one sentence: with the Mathlib cache, the owner's builds run under a 12 GB cap; without the cache
   Mathlib rebuilds from source and takes hours, with no measured memory figure to give); how to check: one line per gate a stranger can run, the commands copied byte for
   byte from `HANDOFF.md` lines 48 to 51 and 53 (line 52, the banned scan, left out) and `HANDOFF.md` line
      1309's `python3 -I tools/witness_gate.py` with "about 27 minutes", each gate with one clause on what its
   PASS line looks like, the present README's `elan` sentence kept, and the
   drift command as `ci.yml` line 61 has it without `|| exit 1`; then one line saying `tools/banned_vocab_scan.py`
   reads a private word list that is not in the repository, so it exits 2 for anyone else (measured), and
   that gate 7 (a whole-library recheck in a fresh build) runs outside CI on the owner's machine; reading the
   docstrings: a paragraph saying module docstrings cite the check scripts, witness notes and plan behind
   their hypotheses by the names the orders used, that every such file is in `records/scripts/` or
   `records/plan/` with a map in `records/scripts/README.md` (one is not retained, and the map says so), and
   what "the lane", "API-CREDIT-1", draft ids, "order LEAN-NN", "order CC-NN", "claude-ai", "round", "bridge",
   "store row" and a host name mean, one sentence each (orders are in `records/orders/`, indexed by
   `INDEX.md`; a round is one order's dated record in `records/rounds/`; a bridge is a theorem that needs two
   modules; a store row is an entry in the owner's private record; a CC order was one run by a Claude Code
   session, named in its row; claude-ai is the planning chat that wrote most orders; a host name is one of the
   owner's machines); the other files (`HANDOFF.md`, `ROADMAP.md`, `records/` with one sentence that its orders
   and rounds cite hosts and scratch paths a reader cannot reach, `records/scripts/`, `records/plan/`,
   `deploy/`, `tools/` listing which files are gates and which are tests); the license; one line on
   contributions (issues welcome; pull requests go through the owner's gates before merge). No local path, no
   claim of a count not listed above. Then `readme_check.py` (a file): the README has no match for
   `/home/|/opt/|/data/|~/`, and names no host other than in the one sentence that defines what a host name
   means; each of the integers 158, 3931 and 4211 appears, and only in a sentence that also contains its
   defining words ("modules", "theorem constants", "jobs"); none of 212, 4453, 5747 appears; the Lean version
   string equals the one in `lean-toolchain`; every command line in the "how to check" block is a substring of
   one of `HANDOFF.md` lines 48, 49, 50, 51, 53 or 1309 or `ci.yml` line 61, exactly that set is present and
   line 52's command is absent, and the build block equals the present README's lines 17 and 18 (the check
      prints the matching `file:line` for each); every integer in the README, an integer being a run of digits
   not adjacent to a letter, `-`, `.`, `/` or `_` (so `API-CREDIT-1`, `v4.34.0`, `2.0` and file names are not
   integers), is one of 158, 3931, 4211, 2026, 12 (the memory cap), 27 (the witness gate's minutes), 2 (the
   exit code) or 0 (in a copied command's comment), and any other integer fails; the words "the lane" and
   "API-CREDIT-1" each appear exactly once, in the paragraph that defines them. Planted-fault controls, one
   fault per copy: a copy with `3931` changed to `3932`; a copy with one `/home/` line added; a copy with line
      52's command added; a copy with "5747" added as a bare number. Each must FAIL. Save all outputs. Then
   `python3 -I tools/compile_rules.py drift records/rules.toml HANDOFF.md` (PASS). Then the new-text gate:
   `vocab_count.py` over the `+` lines of `git diff 24a75a3` (every line this order adds): expect hits on the
   licence index only, each on `README.md`'s authorship line or licence line or on a line the exceptions
   forgive, listed in the report; any other index with a hit is a stop. Commit: this is G.
6. **Expected results,** `~/lean/public1-checks/expected.txt`, written before step 8, sha256 in the report:
   `git diff --stat 24a75a3 <G> -- ClassicalLean ClassicalLean.lean tools .github lakefile.toml
   lake-manifest.json lean-toolchain` empty; build 4211 jobs, 0 warnings (not needed for correctness, since
   no Lean file changed; run once so the report can cite it at G); AxiomGate PASS 3931; check_sorry PASS 158;
   check_records PASS 158, 1 exemption; banned scan PASS 158 files and the root; the step-4 checks and the
   step-5 gates as they expect; drift PASS. The type dump, VacuityGate, the witness gate and gate 7 are not
   run: the empty diff over the Lean tree, `tools`, CI and the lake files is the proof that nothing they
   measure changed.
7. **The history and GitHub check,** reported for Dustin, not acted on: `history_check.py` and a shell file
   that (a) print `git ls-remote github`; (b) count lines of `git log --all -p --format='%H%n%B'` matching
      each index of the term file (expect the two known indexes only) and the secret, address and IP patterns
   (expect 0; the two allowed addresses only, with the order copy's own `git@github.com` and `noreply` lines
   counted and stated; 0), with a planted control (a scratch line matching each pattern
   must be found); (c) print the 14 lines at HEAD that match retired[8], with file and line number, for Dustin
   to read in the report (the one place a matched line is printed; Scope's exception); (d) print `git log
   --all --format='%ae%n%ce' | sort | uniq -c`; (e) run the secret, address and IP patterns over all tracked
   files (expect 0; the two allowed addresses with per-path counts, the order copy's lines among them; 0); (f) `gh pr list --state all`, `gh issue list --state
   all` (expect none), `gh api --method GET repos/datasphereai/classical-lean/actions/artifacts --jq
   .total_count` (0), `…/releases --jq length` (0), `gh run list -L 200 --json headSha,headBranch` (counts
   by branch as above), then for every run head that is not an ancestor of `github/master` after `git fetch
   github` (expect 1: the `cloud-ci` head `7992041`; never the stale local `master`), `gh api --method GET
   repos/datasphereai/classical-lean/compare/master...<sha>
   --jq '.commits[].sha'` and, for each commit listed, `gh api --method GET
   repos/datasphereai/classical-lean/commits/<sha> --jq '.files[].patch'`    run through the four patterns, and `git fetch github <sha>` then `git show <sha>` (message, author and
   committer e-mail, full diff, large files included) through the same patterns and `vocab_count.py` (counts
   per commit; a secret or IP hit, an address outside the allowed two, or a list hit is reported in bold for
   Dustin and is a stop before the push), with the list of those commits saved; `git for-each-ref
   refs/remotes/github` printed; and every run's log (`gh run view <id> --log`
      for each of the 82, one at a time, kept out of the tree) through the four patterns and `vocab_count.py`,
   counts only; a secret, IP or list hit in a log is reported in bold and is a stop before the push. Save its
   output. The 14 lines are Dustin's to read before the switch; removing any of them is outside this order
   and would be a small follow-up order, so the report says plainly that the switch waits on his reading.
8. **Gates at G,** each beside its expected result, cited from its saved output: the empty diff; `lake build`
   (through `run.sh`); AxiomGate; check_sorry; check_records; the banned scan; the step-4 and step-5 checks;
   drift. Then **records closed:** write the closing round text, run `vocab_count.py` and the four patterns
   over it (no list hit; secret and IP 0; addresses none or the allowed two; host lines counted and listed),
   then one records-only commit: round completed with the commit hashes, the gate lines and
   the history check's counts; CLAIMS closed; INDEX set; `check_records` PASS at the final HEAD.
9. **Report and push-review file.** The report (`ds_file`, kind `report`): what changed, file by file; the 19
   files with hashes and the table; the step-4 checks' outputs; the README check's output and its control; the
   counter's control; each gate expected and observed; the history check, with the 14 retired[8] lines quoted
   for Dustin; misses; the push command, not run:
   `cd ~/lean/classical-lean-paper-crypto && git push origin public-1:master && git push github public-1:master`.
   The push-review file (one script writes it to `~/lean/public1-checks/PUBLIC-1-push-review.txt`; the session
   files it as Scope says, and `ds_hash` must equal the local hash): `git rev-parse HEAD`; porcelain; both
   remotes' master (still `24a75a3`); `git ls-remote github`; `gh repo view datasphereai/classical-lean --json
   visibility` (PRIVATE); `git log --first-parent --name-status --format='== %h %cI %s' 24a75a3..HEAD`; `git
   diff --name-status 24a75a3 <G>` (expected: `README.md` M and `records/` only); `git diff --stat 24a75a3 HEAD
   -- ClassicalLean ClassicalLean.lean tools .github lakefile.toml lake-manifest.json lean-toolchain` (empty);
   `sha256sum records/scripts/*/* records/plan/*` (the 19 pinned values); `git show HEAD:README.md`; `git show
   HEAD:records/scripts/README.md`; the round file; `readme_check.py`'s output and its three controls; the four patterns over the
      19 files and over the `+` lines of `git diff 24a75a3 HEAD` (secret and IP 0; addresses the allowed two with
   counts; host: counts); `vocab_count.py` over the `+` lines of `git diff 24a75a3 HEAD` (per-index counts, the licence index
   only); the banned-family greps over `ClassicalLean/` as in every push review (nothing); `git diff
   --name-only <G> HEAD` (only `records/`). Then stop: claude-ai reviews it, having read the README text in
   it and the plan and bridges copies (the same bytes as the lane's, which claude-ai read before writing this
   order), Dustin reads the 14 lines and pushes, and after CI is green Dustin makes the repository public himself, on DSMain:
   `gh repo edit datasphereai/classical-lean --visibility public --accept-visibility-change-consequences`
   (his click, not this session's), then claude-ai reads the public page without a login and records it.

## Done means

Branch `public-1` from `24a75a3`, clean, nothing pushed: RF, the scripts commit, the README commit (G), the
records commit; the counter's control passed; `records/scripts/` and `records/plan/` holding the 19 files
byte-identical to their sources, each hash and every cited name in the map, the one missing file named as
such, and the step-4 checks as expected; the README as step 5 says with its check passing, its control
failing, and the new-text gate clean; the Lean tree, `tools`, CI and the lake files untouched (empty diff);
every gate of step 8 as expected; the history check saved; the report and push-review file in `lean/PUBLIC-1/`
with hashes matching yours. Then tell Dustin in a few plain sentences what changed, point him to the 14 lines
to read, and give the push command and the visibility command.

## Not in this order

The visibility switch itself; any rewrite of history or of any docstring; any change to `HANDOFF.md`,
`ROADMAP.md`, `tools/`, `.github/` or any module; the 95 scratch paths in the records (they stay as
provenance); the 14 retired[8] lines (Dustin's reading; a follow-up order if he wants any removed); the one
`cloud-ci` commit on GitHub (only GitHub support can purge unreachable objects; Dustin's call after step 7's
read); a public site; TWINS-1; GATE-2; LEAN-39B; CLOUD-MATH-8 (next, after this).
