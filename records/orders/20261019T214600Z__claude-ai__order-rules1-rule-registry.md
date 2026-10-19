# RULES-1 (revision 4): one registry for HANDOFF.md section 6, and the rule text generated from it

From claude-ai, 2026-10-18, chat "Where were we?" (Project Skills/MCP development); revisions 2 to 4 on 2026-10-19 in
the same Project. For one Claude Code session on DSMain, as dustin, in the worktree `~/lean/classical-lean-paper-crypto`.

**Ready to run, after the LANE-LOCK live act** (`server/LANE-LOCK/ruling-2.md` section 4 wants no other Claude Code
session on DSMain during that act); Dustin's message gives this file's sha256. It replaces revision 3
(`lean/RULES-1/order-r3.md`, aec9539d), which the BREAK-IT-4 reviewer (report `server/BREAK-IT-4/report.md`,
7e55d1cb) found runnable as written, with one MINOR: after a force-push the CI gate printed `FAIL rules gate: base
not found` (N6), loudly. Revision 3 replaced revision 2 (`lean/RULES-1/order-r2.md`, cba91573), which
BREAK-IT-3 (report `server/BREAK-IT-3/report.md`, 4a3f03ff) walked through J1 to J5 in a scratch folder and found
"nearly runnable": its CI gate failed on a manual run and on a new branch's first push (F13), its Done-means count
double-counted a verified rule that is also a merge survivor (F14), J4's note replaced J3's row (F15), and its "what
changed" list was short (F16). Revision 1 (`order.md`, 41083b0b) was never run (`~/lean/rules1-checks/` did not exist
on 2026-10-19 and `master` is still `a6d5c0f`).

What changed from revision 3, and only this: one line in J5's gate, before the `case`, so a hint the checkout does
not have (a force-push's old tip) also takes the merge-base fallback (N6); a fourth way to run the gate before
committing (a hint the clone does not have); claude-ai's test of that line and the BREAK-IT-4 reviewer's walk under
"What claude-ai measured"; the report's count of gate runs; and this header.

What revision 3 changed from revision 2: the gate's base in CI falls back to `git merge-base HEAD origin/master`
when the push event's before-SHA is empty (a manual run) or all zeros (a branch's first push), and the checkout step
fetches full history (F13); Done means 1 counts distinct rules (F14); J4 appends to a survivor's `change_note`
instead of replacing it, so the J3 row stays named (F15); and this paragraph and the one below list everything
revision 2 changed, including what its own list left out (F16).

What revision 2 changed from revision 1 (its list, completed): the tools are the rules compiler v2.1 (revision 1 pinned
v1), so the file table, its hashes and the first registry's hash are new; the splice is `compile_rules.py splice`
(it replaces `splice.py`); two regression suites are added; v2.1's check needs a store row for verifying a tool and
for a merge, so J3 and J4 say where those rows come from; start check 6 (`ds_append_row` among the session's tools)
is new; and two "Known and accepted" bullets are new (check cannot look a row id up; drift guards section 6 only).
Every other line is revision 1's.

Review: revision 1 was cold-reviewed on 2026-10-18 by a fresh subagent working read-only from a named read list,
about 40 calls a pass. Pass 1: FAIL (2 BLOCKER, 6 MAJOR, 5 MINOR), all applied, three of them as changes to the
tools (the registry no longer depends on the source file's name; `check --base` now refuses a deleted rule and a
changed text without a new change_note; the builder refuses blank lines and cut titles inside the rules; the
render keeps section 6's layout so that `mkbrief.py` still quotes every rule). Pass 2: PASS WITH FINDINGS,
0 BLOCKER, 4 MAJOR (a verified tool's rule also changes its words; readers asked for a merged rule; the gate
passing on an empty or zero base; a merge dropping the survivor's own requirement), 6 MINOR, all applied in that
text. Then the tools: BREAK-IT-1 (2026-10-18, report `server/BREAK-IT-1/report.md`, 42f4080b) found C1 to C3 in v1;
v2 fixed them; BREAK-IT-2 (2026-10-19, report `server/BREAK-IT-2/report.md`, 8f8a668c) found C1 and C2 closed, C3
partly (N9) and called v2 safe to land; v2.1 adds the N9 fix, and BREAK-IT-3 found the N9 fix does what it says and
called v2.1 safe to land. Revision 2 of this order was reviewed by BREAK-IT-3 (F13 to F16, all applied here);
Revision 3 was walked by BREAK-IT-4 (J3 to J5; F13 to F16 closed; N6, applied here). Revision 4's one line was
tested by claude-ai in a scratch repository (below), not by a reviewer.

## Why

- Dustin's ruling of 2026-10-18 19:15 EDT (store row 20261018-010): one in, one out for section 6 as a stopgap,
  and what he actually wants: something that compiles the rules, so that where one rule (or better, one tool)
  can take the place of many on a subject, it does.
- Section 6 went from 34 to 39 numbered rules between 2026-10-14 and 2026-10-18, each a sentence a session must
  remember. Some already have a tool that refuses the bad act (rules 37, 38 and 39 say so in their own text).
- Measured outside this repository (research of 2026-10-18, cold-verified): instruction-following falls as the
  number of instructions rises (IFScale, arXiv 2507.11538: the best models reach 68% at 500 instructions), and
  Anthropic's guidance is that hooks and tools guarantee an act, while written instructions are advisory.
- So the registry records, for each rule, whether a tool enforces it, and the numbered list is generated from
  it: a rule whose tool really enforces it shrinks to one line naming the tool; rules on one subject can merge
  into the one that absorbs them; the self-applied rules are held to a budget that only Dustin can raise; and a
  gate refuses a numbered rule written by hand outside the generated block, a deleted rule, and a changed text
  without a note.

## Goal, scope, done means, undo

- **Goal.** Section 6's numbered rules come from `records/rules.toml` through `tools/compile_rules.py`, with
  every rule's words unchanged unless a reviewed merge changed them or a verified tool replaced them with its one
  line, and the self-applied count, at most 39, as the budget.
- **Scope.** In the repository: `tools/compile_rules.py`, `tools/build_registry.py`,
  `tools/test_compile_rules.py`, `tools/test_breakit2_rules.py`, `records/rules.toml`, section 6's numbered list
  in `HANDOFF.md` (only the lines the render replaces), the order's own records (as `records/README.md` says), and
  the CI workflow, for one gate. Outside it: `~/lean/rules1-checks/` (evidence and scratch), and
  `~/lean/recheck/run-recheck.sh` for the same gate, copied into the evidence folder before any change; and the
  store rows J3 appends (one per verified tool). Nothing else: no Lean module, no other part of `HANDOFF.md`, no
  change to what any rule requires.
- **Done means.**
  1. `records/rules.toml` holds rules 1 to 39, each with its subject, status and tool (or none);
     `compile_rules.py report records/rules.toml | tail -1` gives the totals and shows 0 retired; only merge
     survivors, the rules they absorbed and verified tools carry a `change_note`: `grep -c '^change_note'
     records/rules.toml` equals the number of distinct rules that are a survivor, an absorbed rule or a verified
     tool (a rule that is both counts once).
  2. `drift records/rules.toml HANDOFF.md` prints `PASS no drift`; `check records/rules.toml --base
     ~/lean/rules1-checks/base-rules.toml` prints `PASS`, where `base-rules.toml` is `git show
     <J2 commit>:records/rules.toml` (this check refuses a deleted rule, a changed title or body without a new
     `change_note`, a budget above the base's, and, in v2.1, a tool set to verified, a verified rule's tool
     changed, a merge or a new rule number without a `change_note` naming a store row).
  3. `mkcompare.py <HANDOFF at a6d5c0f> HANDOFF.md 39` lists as differing only the merge survivors, the
     absorbed rules and the rules with `enforcement = "verified"`; every other rule has the same words.
  4. Each of the nine tools in "Tools to verify" is `verified` under J3's three conditions, with its store row,
     or left `proposed` with the reason in the report.
  5. Each subject group is merged (reviewed as J4 says) or kept apart with a one-line reason.
  6. `meta.budget_self_applied` equals the self-applied count, at most 39.
  7. Every gate command in `run-recheck.sh` and the CI workflow, run locally, exits as it did at `a6d5c0f`
     (J1 runs them at `a6d5c0f` first and logs each rc), the new gate included. CI itself is checked in
     claude-ai's push review.
  8. The report is filed, with claude-ai's predictions P1 to P7 scored.
- **Undo.** Nothing is pushed by the session. Before Dustin's push, deleting the branch and restoring
  `run-recheck.sh` from the evidence folder undoes everything; after it, `git revert` of the order's commits. The
  J3 store rows stay (the store is append-only); a later row can supersede them.

## Read first (read only)

- This order, in full; `HANDOFF.md` sections 0 and 6; `records/README.md`; LEAN-32's close
  (`/opt/datasphere/lane/inbox/threads/staging/lean/LEAN-32/close.md`) for the gates and how they run.
- These files in `~/claude-ai-witness/rules-v2.1/` on DSMain (claude-ai's, read only; copy before use).
  `sha256sum -c MANIFEST.sha256` there checks the first seven (MANIFEST.sha256 = 3bf2d300...), and
  `cd first-run && sha256sum -c SHA256SUMS` the last four (SHA256SUMS = 0bae029c...).

| file | sha256 | what it is |
|---|---|---|
| rules/compile_rules.py | f85aff5bfd9036ff6eabdb9a6e275dbc161f83e2865df23b090f50ea7b197b56 | check, render, drift, report, splice (v2.1) |
| rules/build_registry.py | ce218ec7184905477674259839215ed73756cc6b3ac64b607730d621240f376e | section 6 to a first registry, with claude-ai's proposals for subject and tool (v2, unchanged in v2.1) |
| rules/test_compile_rules.py | 98e748dce2aa3e2b47abb88e3a0aee98ea52765e28623528029bbd960998c882 | 43 tests on made-up files; runs itself; removes its temp folder |
| rules/test_breakit2_rules.py | a07454b60939202d62674855167670ac465c458c7184c76011745f0a10ce4917 | 6 tests for v2.1's row rules (BREAK-IT-2 N9); runs itself |
| rules/test_breakit1_rules.py | e7c56aaac7e1ae50375ffad62b9fa6a61369339358f10aeab58430a7138799f1 | the BREAK-IT-1 regressions on a real HANDOFF: `test_breakit1_rules.py <HANDOFF> <empty folder> 39`; needs mkcompare.py beside it |
| rules/mkcompare.py | 94f0fd68e4d32cfe716317695d13132909970e3aefb80040532229e462e5db0e | quotes rules 1 to N from two HANDOFF files the way LEAN-31's `mkbrief.py` does, and compares the words |
| run.sh | 7d03ef40438a443a7f13839301ccca2e48e82ca888c7ab998043fe76b1323bd2 | claude-ai's staging run of the three suites (outputs in out/, hashes in OUT.sha256 = 04f9212c...) |
| first-run/HANDOFF-a6d5c0f.md | a280e22b557cad7013ea394a45e0f5b209d6c68897f316b46d114a1c99773287 | `git show a6d5c0f:HANDOFF.md` |
| first-run/claude-ai-rules.toml | 07f3ec929d7e115842a0e9d2da5a9c77eddf42449344218fa864ce8bf442707f | the first registry built by v2.1: 39 rules, 9 with a proposed tool; v1's (5590e008) plus one meta line, `outside_sha256` |
| first-run/claude-ai-rules-render.md | 12ea7e97f09449502009cb4798b5239e0aabe65ee191c01ce6ce2a743549efe1 | its render: 44 lines, 13510 bytes (byte-equal to v1's) |
| first-run/HANDOFF-spliced.md | 0fecc9383af7170bbda01a949ed4c57e3ce60e860d889a879ab4318f1961e48b | the copy at a6d5c0f with the render spliced in (162 lines became 44; byte-equal to v1's) |

The v1 tools were cold-reviewed three times on 2026-10-18 (twice with the witness hooks, once with this order);
v2 and v2.1 as the Review paragraph says.

## What claude-ai measured to write this

On 2026-10-18, DSMain, outside the repository (revision 1):

- `git --git-dir=/data/git/classical-lean.git log -1 master`: `a6d5c0f` (LEAN-32 records, 16:41:36 EDT).
- The readers of section 6 found: LEAN-30/31's `mkbrief.py` (quotes rules from a line `  N. ` up to the next
  `  M. ` or `- **`), LEAN-32's `mkbrief32.sh` (calls it with rules 17, 35, 37), and comments in `el.sh`, `ev.sh`
  and `quotecheck.py`. Not measured: the CI workflow, `run-recheck.sh`, `records/README.md`, and whether any
  other tool parses section 6.

On 2026-10-19, DSMain, outside the repository (revision 2; outputs in `~/claude-ai-witness/rules-v2.1/`):

- `master` and the worktree's `origin/master` are both still `a6d5c0f948e18231f53b2126201966b51c7d6416`;
  `git show master:HANDOFF.md` has sha256 a280e22b, section 6's rules run from line 1079 (`  1. *Check the
  invariant`) to rule 39 at line 1232, and `- **Standing answers**` is at line 1241; `~/lean/rules1-checks/`,
  `records/rules.toml` and `tools/compile_rules.py` do not exist.
- `run.sh`: MANIFEST all OK; test_compile_rules 43 passed; test_breakit2_rules 6 passed; test_breakit1_rules on
  first-run/HANDOFF-a6d5c0f.md with 39, 45 passed; no new entry left in /tmp.
- In `first-run/` (predictions in `first-run/predictions.txt`, written first): the HANDOFF copy equals `git show
  a6d5c0f:HANDOFF.md`; build 39 rules, 9 with a proposed tool; `check --first` PASS; the registry differs from v1's
  only by `outside_sha256 = "f39a512b..."` in `[meta]`; the render and the spliced copy are byte-equal to v1's;
  splice: `replaced lines 1079 to 1240 (162 lines) with 44 lines; outside sha256 f39a512b6b1d unchanged`; drift
  `PASS no drift`; mkcompare `39 of 39 rules quoted with the same words`; report: 39 self-applied (budget 39),
  0 verified, 0 merged, 0 retired.

By the BREAK-IT-3 reviewer on 2026-10-19 (revision 2; `/home/dustin/break-it-3/rules1-walk/`): the start checks
held (master `a6d5c0f`, all eleven hashes, Python 3.12.3); J1 to J5 walked through in a scratch folder with no
repository, every step passing under v2.1; in a scratch repository the CI gate as revision 2 wrote it printed
`FAIL rules gate: base not found` on `workflow_dispatch` and on a branch's first push (F13).

By the BREAK-IT-4 reviewer on 2026-10-19 (revision 3; `/home/dustin/break-it-4/rules1/`): the start checks held
(master `a6d5c0f`, every hash, Python 3.12.3); J3 to J5 walked with the append rule, rule 38's note keeping both row
ids, Done means 1 counting 5 for 5 distinct rules; the gate text passed with the hint set to a parent commit, empty
and all zeros, and failed as it should on a rule body changed with no note; after a force-push, in a clone made with
`--no-local` (CI's checkout fetches only reachable commits), it printed `FAIL rules gate: base not found` (N6).

By claude-ai on 2026-10-19 (revision 4's gate line; predictions written first): in a scratch repository whose branch
was force-pushed and then cloned with `--no-local`, revision 3's base lines and revision 4's were each run with five
hints. Revision 3's: the parent, empty and all zeros gave the merge base; the force-pushed-away tip gave `FAIL rules
gate: base not found`; a normal push's before-SHA gave itself. Revision 4's: the same, except that the
force-pushed-away tip gave the merge base. 10 of 10 as predicted.

## claude-ai's predictions (written before the session runs)

- P1. Every start check passes.
- P2. In the evidence copy: `test_compile_rules.py` 43 passed, `test_breakit2_rules.py` 6 passed, and
  `test_breakit1_rules.py HANDOFF-a6d5c0f.md <empty folder> 39` 45 passed, each with 0 failed; in `tools/`,
  43 and 6 again.
- P3. The registry built in J1 is byte-equal to `first-run/claude-ai-rules.toml` (07f3ec92), and its render to
  `first-run/claude-ai-rules-render.md` (12ea7e97).
- P4. Of the nine tools, at most 3 meet all of J3's conditions: 38 (`rootrun.sh`) and 39 (`citecheck.py`) are
  the likeliest; 23 and 32 (`ev.sh`, `land.sh`) stay proposed, because nothing makes a session use them.
- P5. After J3 and J4 the self-applied count is between 18 and 30.
- P6. Every gate exits after the change as it did at `a6d5c0f`.
- P7. `mkcompare.py` on the final `HANDOFF.md` differs only for the merge survivors, the absorbed rules and
  the verified ones.

## At the start (stop and tell Dustin if one fails)

1. The order's sha256 equals the value in Dustin's message.
2. In the worktree: `git --no-optional-locks status --porcelain` prints nothing; after `git fetch origin`,
   `master` and `origin/master` are both `a6d5c0f948e18231f53b2126201966b51c7d6416`.
3. The eleven files in the table have their sha256.
4. `python3 --version` on DSMain is 3.11 or newer (the compiler needs `tomllib`; claude-ai saw 3.12.3).
5. None of `records/rules.toml`, `tools/compile_rules.py`, `tools/build_registry.py`,
   `tools/test_compile_rules.py` or `tools/test_breakit2_rules.py` exists at `a6d5c0f`.
6. `ds_append_row` is among your tools (J3 needs it). If it is not, say so in the J1 plan; J3 then stops after its
   runs and lists the rows for claude-ai to append, and resumes (setting `verified`, `verified_by` and
   `change_note` with the row ids claude-ai reports) once Dustin pastes those ids.

## The jobs

**J1, read only.**
1. First, find `ev.sh` and `land.sh` as LEAN-32 used them, set up `~/lean/rules1-checks/` with its
   `evidence.log` the same way, and run every later command through them (section 6 rules 5, 8, 23, 30, 32).
2. Copy the six files under `rules/` into `~/lean/rules1-checks/claude-ai/` and check their sha256.
3. Save `git show a6d5c0f:HANDOFF.md` as `~/lean/rules1-checks/HANDOFF-a6d5c0f.md`. Run
   `test_compile_rules.py` and `test_breakit2_rules.py` there, and `test_breakit1_rules.py HANDOFF-a6d5c0f.md
   <a new empty folder> 39` (P2); then `build_registry.py HANDOFF-a6d5c0f.md rules-j1.toml 39`, its render,
   `compile_rules.py splice rules-j1.toml HANDOFF-a6d5c0f.md HANDOFF-j1-spliced.md`, `drift` on the spliced copy,
   and `mkcompare.py` (P3).
4. Find where each of the nine tools in "Tools to verify" lives and how it is run (LEAN-29 to LEAN-32's
   evidence folders under `~/lean/`), and every other script that reads `HANDOFF.md`; run each reader on the
   spliced copy and log whether it still works.
5. Find where the gates are listed and run (`run-recheck.sh`, the CI workflow), run every gate command at
   `a6d5c0f` and log each rc; log CI's Python version (stop if it is below 3.11; if it is not pinned, the one
   gate adds a setup step pinning 3.12). Log the CI workflow's checkout step and whether it already fetches full
   history (`fetch-depth: 0`); J5's gate needs it.
End J1 with a plan for J2 to J5 and wait for Dustin's approval. Write nothing in the repository before it.

**J2, land the tools and the registry.** On a new branch `rules-1` from `a6d5c0f`:
1. File this order as `records/README.md` says (as LEAN-32 did), byte for byte.
2. Add `tools/compile_rules.py`, `tools/build_registry.py`, `tools/test_compile_rules.py` and
   `tools/test_breakit2_rules.py` byte for byte (sha256 checked); run `python3 tools/test_compile_rules.py`
   (43 passed) and `python3 tools/test_breakit2_rules.py` (6 passed) in the worktree.
3. Copy J1's `rules-j1.toml` to `records/rules.toml` and check its sha256 (`07f3ec92...`).
4. `compile_rules.py check records/rules.toml --first` (PASS), then commit these six paths (the four tools,
   `records/rules.toml` and the filed order) and the order's records. Save `git show <this
   commit>:records/rules.toml` as `~/lean/rules1-checks/base-rules.toml`.

**J3, verify the tools.** For each row of "Tools to verify", in a scratch tree
`~/lean/rules1-checks/scratch/<rule>/` (from `git archive a6d5c0f | tar -x`, never the worktree; no sudo; do
not run a tool that would write outside the scratch tree, apart from `ev.sh`'s own line in `evidence.log`; for
rows 23 and 32 point `ev.sh` at a log inside the scratch tree; a Lean build inside the scratch tree is allowed,
under the 12G memory cap as LEAN-32 ran it, and if it is too slow, leave 37 and 38 proposed and say so): predict,
then run the tool once on the unchanged scratch copy and once with the fault planted. A tool counts as `verified` only if all three hold:
- (a) the clean run passes (rc 0) and the faulted run fails with the tool's own message naming the fault, both
  logged;
- (b) every requirement in the rule's body has a planted fault that the tool refused;
- (c) the tool runs without a session choosing to run it: it is a gate, a hook, or the only path to the act.
Then, because v2.1's `check --base` refuses a tool set to verified unless its `change_note` names a store row:
append one row with `ds_append_row` (tag `measured`; box DSMain; command: the clean and the faulted commands;
output: their rc lines and the tool's refusal message, at most 2000 characters; ran_by: the participant name the
door accepts for you; surface and session naming this order and J3), and set `enforcement = "verified"`,
`verified_by` to one line naming the faults, the evidence labels and the row id, and `change_note` to
`"RULES-1 J3: verified, store row <id>"`. No row, no `verified`: if the door refuses the row, leave the tool
`proposed` and put the refusal in the report. Otherwise leave it `proposed` and write in the report which
condition failed and what a session must still remember to call. Never change a tool to make it pass; that is a
later order.

**J4, the merge pass.** `compile_rules.py report records/rules.toml` lists the subjects with more than one
self-applied rule. For each, either draft one surviving rule whose text keeps every requirement of the rules it
absorbs and its own (it keeps its own number; its `change_note` names this order, the merge and Dustin's ruling
that this order carries out, store row 20261018-010, which v2.1's check needs for a merge, and if the rule already
carries a J3 note the merge note is appended to it after `; `, never written over it, so the J3 row stays named;
the review's sha256 goes in the report, not the registry; the others get `status = "merged"`, `merged_into` and
the same merge note), or keep them apart with a one-line reason. A group may become a tool's one line only if that
tool met J3's (b) for every absorbed rule. Then:
- Log the sha256 of the registry the reviewer will read. One fresh subagent (read list: for each merge, the
  survivor's own old title and body and every absorbed rule's title and body, all from `base-rules.toml`, the
  survivor's new text, and for a merge into a tool's line the J3 log lines; this order; about 40 tool calls)
  lists every requirement of the survivor and of every absorbed rule and quotes where the new text keeps it. Any answer but a
  clear "kept" for every requirement means the merge is not landed. A merge redrafted after review goes to a new
  reviewer. Save each review in `~/lean/rules1-checks/reviews/` and log its sha256.
- The registry committed in J5 equals the reviewed one except for merges taken out and the two meta lines J5
  sets (show the diff).
- No rule is retired in this order. Copy the report's "no recorded catch" line into the report for Dustin;
  do not research catches.

**J5, generate section 6.** Set `meta.budget_self_applied` to the self-applied count and `budget_set_by` to
"RULES-1 <date>: lowered to the self-applied count under row 20261018-010". Replace section 6's numbered list
with the render: `python3 tools/compile_rules.py splice records/rules.toml HANDOFF.md
~/lean/rules1-checks/HANDOFF-j5.md` (it refuses unless each anchor occurs once, in order, inside section 6, and
checks that nothing outside the block changed), then copy that file over `HANDOFF.md` and log both sha256.
Then run `drift` and `check --base ~/lean/rules1-checks/base-rules.toml` (both PASS), and `mkcompare.py` against
`HANDOFF-a6d5c0f.md` (P7). Run every reader of section 6 found in J1 on the final `HANDOFF.md` for each of rules
1 to 39 and log rc and output: a reader asked for a merged rule must fail loudly (a nonzero rc naming the
rule); if one exits 0 with an empty or partial quote, take that merge out and report it as a defect for the next
order. If `drift` fails on a line outside the markers, or any existing gate fails, stop: edit
neither the gate, the compiler, nor anything outside the markers. Add the gate, the same text in
`run-recheck.sh` and the CI workflow, where BASE_HINT is `$(git merge-base HEAD origin/master)` in
`run-recheck.sh` and the push event's before-SHA (`${{ github.event.before }}`) in CI, and the CI checkout step
has `fetch-depth: 0` (the gate needs the history; add it if J1 found it missing):

```
tmp=$(mktemp -d)
hint="<BASE_HINT>"
git cat-file -e "$hint^{commit}" 2>/dev/null || hint=""   # empty, all zeros, or a force-push's old tip the checkout never fetched
case "$hint" in ""|0000000000000000000000000000000000000000)
  git fetch -q origin master && hint=$(git merge-base HEAD origin/master) ;;   # a manual run, or a branch's first push
esac
base=$(git rev-parse --verify "$hint^{commit}") || { echo "FAIL rules gate: base not found"; exit 1; }
if git cat-file -e "$base:records/rules.toml" 2>/dev/null; then
  git show "$base:records/rules.toml" > "$tmp/base-rules.toml"
  python3 tools/compile_rules.py check records/rules.toml --base "$tmp/base-rules.toml" || exit 1
elif git merge-base --is-ancestor "$base" a6d5c0f948e18231f53b2126201966b51c7d6416; then
  python3 tools/compile_rules.py check records/rules.toml --first || exit 1
else
  echo "FAIL rules gate: base $base has no registry"; exit 1
fi
python3 tools/compile_rules.py drift records/rules.toml HANDOFF.md || exit 1
```

When `run-recheck.sh` runs on `origin/master` itself, its base is HEAD and the `--base` check proves nothing;
CI is the real check of the budget and the words, and the report says so. Before committing, run the gate four
ways in a scratch clone of the branch and log each: with the hint set to the branch's parent commit (expect the
`--base` branch and PASS), with it empty, with it all zeros, and with it set to a commit the clone does not have,
for example forty 1s (each of these three: expect the merge-base fallback and PASS).

Run every gate (Done means 7) and commit.

**Close.** The report (below). The push is Dustin's, after claude-ai's push review: `cd
~/lean/classical-lean-paper-crypto && git push origin rules-1:master && git push github rules-1:master`.

## Tools to verify (the tool each rule's text names, claude-ai's reading)

| rule | tool | a fault to plant (add one per requirement for condition b) |
|---|---|---|
| 22 | quotecheck.py | a block quote cut without `[...]` |
| 23 | ev.sh | a command run with no prediction argument |
| 26 | close-brief-make / mkbrief.py | a brief edited after it was built (its sha256 no longer matches) |
| 32 | ev.sh / land.sh | an evidence write outside the helper, into a scratch copy of an evidence log |
| 34 | inlinecheck.py / quotecheck.py | a paraphrased inline quote (rule 34's own planted misquote) |
| 36 | the brief builder | a line with a clock time and no date |
| 37 | el.sh | a draft that uses an unprobed name |
| 38 | rootrun.sh | the build replaced by `false` (rule 38's own test) |
| 39 | evcite.py and citecheck.py | an `Evidence:` line that leaves one label out (rule 39's own test) |

## Subjects to merge (from the first registry's report)

evidence-log 5, 8, 23, 30, 32; review-order 13, 16, 21, 29, 31; tests 3, 10, 15, 27, 28; commits 4, 6, 7, 39;
build 11, 20, 38; gates 1, 14, 25; names 2, 35, 37; quotes 22, 26, 34; records 18, 19; reviewers 12, 24;
saved-outputs 17, 33; time 9, 36. These are claude-ai's reading of each rule's text; the session may move a
rule to another subject, and says so in the report.

## Known and accepted

- The rendered list keeps today's layout (`  N. ` at a 2-space indent). After a merge or a verified tool, a
  Markdown viewer numbers each list on from its first rule (a list 22, 34, 37 shows as 22, 23, 24); the raw
  text, which sessions and `mkbrief.py` read, is correct.
- A rule absorbed by a merge is no longer quoted by number: a brief that asks for it fails loudly, and later
  orders cite the survivor.
- A rule written by hand as a sub-bullet, not numbered, passes `drift`; the gate catches numbered lines, extra
  top-level bullets and extra "## 6" headings outside the block.
- `check` sees only that a `change_note` names something shaped like a store row id; it cannot look the row up
  (no store access, by design; BREAK-IT-2 found an invented id passes, and BREAK-IT-3 that a merge note could
  stand in for a verification note, which the J4 append rule now prevents). claude-ai's push review checks that
  every row id in the registry exists and says what the note says.
- `drift` guards section 6 only; sections 0 to 5 of `HANDOFF.md` are not guarded (BREAK-IT-2, prediction Q7).
  Whether they should be is Dustin's call for a later order.
- `run-recheck.sh` run on a branch forked at or before `a6d5c0f` falls back to `--first`; CI, with the push's
  before-SHA, is the real check (BREAK-IT-3 F16).

## The rules of this order

- Section 6's rules apply as written today; this order changes their form, not what they require.
- Read only outside the worktree and `~/lean/rules1-checks/`, apart from `run-recheck.sh` as Scope says and the
  J3 store rows. Nothing pushed.

## The report

First, for Dustin, in plain words: how many rules he and the sessions now have to keep in mind (self-applied),
how many a tool really enforces, which merges landed, and the new budget. Then the commits, the start checks,
P1 to P7 hit or miss with the output that decides each, the J3 table (tool, faults, conditions a/b/c,
verified or not, evidence labels, store row), the J4 table (subject, merged or kept, reason, the review's sha256),
the gate results before and after (the four gate runs of J5 among them), the readers of section 6 and how each
fared, deviations, and the files written. File it in the lane with ds_file (project lean, job RULES-1, kind report).
