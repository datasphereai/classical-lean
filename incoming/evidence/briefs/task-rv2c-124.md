# Confirming pass `rv2c-124` (order CLOUD-MATH-3, job 2, item 124, on one fix only)

You are a cold reviewer: you have not seen this work, and you check one fix. The library is the
Lean 4 repository `classical-lean` (Lean and Mathlib v4.34.0), cloned at `$REPO`. Order CLOUD-MATH-3
lands five proved drafts as five new modules; the module review `rv2-124` of item 124's module,
`$REPO/ClassicalLean/Probability/BernsteinInequality.lean` (not yet committed), found one MINOR
finding, and the fix is now made. Your job is that fix alone. This run ends when your report is
written, and by 2026-10-21T03:30Z at the latest (`date -u` gives the time; if you reach that time,
write what you have and list the rest as not checked).

## How you work

* Start every Bash command with `. $HOME/cm3-env.sh && ` (it sets `REPO`, `T`, `EVD`, `BASE`, the
  Lean `PATH` and `PYTHONDONTWRITEBYTECODE=1`).
* Work in the scratch folder `$HOME/cm3-review-7` (create it). Never write inside `$REPO`: no file,
  no `git` command that changes anything, no `lake build`. Copy any repository script into your
  folder before importing it.
* You have at most 40 tool calls. At the cap, write what you have, and list in the report what you
  did not check.
* Write your report to `$EVD/reviews/rv2c-124.md`, then return as your final answer only that
  file's sha256 (the 64 hex digits that `sha256sum $EVD/reviews/rv2c-124.md` prints), nothing else.

## What to read

* The finding: `$EVD/reviews/rv2-124.md`, finding 1 (a path in the module docstring's sentence on
  the witness).
* The module as reviewed, `$EVD/mod/BernsteinInequality.rv2.lean`, and as fixed, the file in the
  tree, `$REPO/ClassicalLean/Probability/BernsteinInequality.lean` (equal to
  `$EVD/mod/BernsteinInequality.lean`: `$EVD/moddiff2-124.out`, `cmp` rc 0); their difference,
  `$EVD/fixdiff-124.out`.
* How the fixed file was made: the module's head `$EVD/text/head124m.lean` (the reviewed head,
  `$EVD/text/head124.lean`, with the one substitution of `$EVD/text/o124d.txt` by
  `$EVD/text/n124d.txt`), the statement file rebuilt from it by `$EVD/scripts/mkstmt.py` with the
  spec `$EVD/spec/s124m.json` (`$EVD/mkstmt-124-fix.out`), and the module reassembled by
  `$EVD/scripts/assemble.py` with the same spec as before, `$EVD/spec/a124.json`
  (`$EVD/assemble2-124.out`).
* The witness start the sentence names, `$REPO/incoming/witness-starts/w124-tail.lean`, the
  module's witness at the end of the file, and their difference, `$EVD/wdiff-124.out`.
* The fixed module's elaboration with the lakefile's four options, `$EVD/m124-module2.out`, and its
  `lake build`, `$EVD/build2-124.out` (count the lines with `warning:`).

## What to check

1. The new sentence resolves the finding: no path that will not exist after the order's merge, and
   what it says of the witness and of the start is true.
2. Nothing else changed: the two module files differ in that docstring sentence only.
3. The fixed module elaborates with rc 0 and no message, and builds with 0 warnings and 0 errors.

## The report

Its first line is `VERDICT: CONFIRMED` (the fix is right and nothing else changed) or
`VERDICT: FINDINGS <n>`. Then each point above with what you saw, a section "Not checked" (write
"nothing" if you checked everything above), and the number of tool calls you used.
