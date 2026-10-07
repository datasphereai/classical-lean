<!-- Copied verbatim on 2026-10-07 from /opt/datasphere/lane/inbox/threads/staging/LEAN-5-order.md (DSMain lane; sha256 3bf3255f001a1bf4d04a1bb87e4fcc289bd23edea449555bfa99d2e1c207c942, checked before reading), per records/README.md rule 2. Copied after the work began. -->

# LEAN-5: no trace of the retired framing in the library

From claude-ai (claude-ai-58), 2026-10-07 16:05 EDT. For the same plain Claude Code session on DSMain, as dustin. Follows LEAN-4-report.md. Dustin's words, 16:03: "I would like to have zero trace of my delusional pseudo-science bullshit to be in the new library." He also said RETIRED.md should not be in it.

Goal: the copy of classical-lean that anyone else will ever see (the GitHub copy, once Dustin decides to make one) contains no word, name, file or commit message from the retired framing, in its files or in its history. The proofs, the gates and the nightly check keep working.

## Scope

- As dustin, no sudo. Do not touch /opt/datasphere-mcp/, the store, or credential files. Do not push. Do not change master in the bare repo /data/git/classical-lean.git. The real clone ~/lean/classical-lean stays on master, so tonight's 03:30 run is unaffected. Work in a separate worktree on a branch `clean-tree`, as LEAN-4 did.
- Never print a retired term in the report, a commit message or the lane. Report counts and file paths only. The term list is RETIRED.md plus the patterns in tools/banned_vocab_scan.py (31 retired and 8 provenance terms per LEAN-3) plus the banned-vocabulary list in ~/CLAUDE.md.

## Steps

1. Measure first, and write predictions before each count. Count matches, case-insensitive, (a) in every tracked file at master, by path, and (b) across the whole history: commit messages, and file contents of every commit (`git log --all -p` or `git grep` over `git rev-list --all`), by count only. Also list any tracked file whose name contains a term.
2. Clean the tree on `clean-tree`:
   - delete RETIRED.md;
   - move the term list out of the repo. The scanner reads it from a file outside the repo (for example `~/.config/classical-lean/banned-terms`, mode 0600), and fails loudly if that file is missing. Keep the scanner's behaviour otherwise identical. Show it red once on a planted term in a scratch copy, then green on the real tree;
   - rewrite or remove every other match found in step 1 (records, orders, rounds, docstrings, comments, HANDOFF). Where a record only exists to describe the retirement, remove it. Where removal would break check_records, fix the records, not the gate;
   - re-run step 1(a): expect 0 matches in the tree.
3. All gates pass on `clean-tree`: lake build with 0 warnings, axiom gate (1662 constants, 0 scoped exceptions), vacuity, check_sorry, banned_vocab (now reading the outside list), check_records.
4. Prepare, but do not install, a fresh history: a branch `fresh-history` made with `git checkout --orphan` from the `clean-tree` tree, one commit, with Dustin's name as author as in the existing history. Confirm its tree hash equals `clean-tree`'s and that step 1(b) on it gives 0. Leave it unpushed.
5. Make an archive of the full old history, outside the library: `git bundle create ~/lean/archive/classical-lean-full-history-<date>.bundle --all`, mode 0600, and `git bundle verify` it. Do not delete anything else.

## Done means

1. Step 1's counts, predicted beside measured, for the tree and for the history.
2. `clean-tree` with 0 matches in its tree and every gate passing, outputs shown.
3. `fresh-history` with 0 matches in tree and history, its tree equal to `clean-tree`'s.
4. The bundle exists and verifies; its sha256 and size.
5. A report at /opt/datasphere/lane/inbox/threads/staging/LEAN-5-report.md, with the plan written before building, the outputs above, the commits, what was not checked, and the exact commands for Dustin's two later decisions, each with what it changes and how to undo it:
   - replace master with `fresh-history` in /data/git/classical-lean.git and re-point ~/lean/classical-lean so the nightly still pulls (helios's old clone then has to be re-cloned, not pulled);
   - or keep master's full history private on DSMain and use `fresh-history` only as the copy that goes to GitHub.
   Recommend one, with the reason.

If you cannot finish, stop at a clean point, commit what works on `clean-tree`, leave master untouched, and write the report.
