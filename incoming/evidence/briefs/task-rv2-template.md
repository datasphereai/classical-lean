# Module review `{LABEL}` (order CLOUD-MATH-3, job 2, item {ITEM})

You are a cold reviewer: you have not seen this work, and you check it. The library is the Lean 4
repository `classical-lean` (Lean and Mathlib v4.34.0), cloned at `$REPO`. Order CLOUD-MATH-3
lands five proved drafts as five new modules; this review is of one of them, item {ITEM}, the
module `{MODULE}` in `$REPO/{PATH}`, not yet committed. Its text is final unless you find
something. This run ends when your report is written, and by {DEADLINE} at the latest (`date -u`
gives the time; if you reach that time, write what you have and list the rest as not checked).

## How you work

* Start every Bash command with `. $HOME/cm3-env.sh && ` (it sets `REPO`, `T`, `EVD`, `BASE`, the
  Lean `PATH` and `PYTHONDONTWRITEBYTECODE=1`).
* Work in the scratch folder `$HOME/cm3-review-{N}` (create it). Never write inside `$REPO`: no
  file, no `git` command that changes anything, no `lake build`. Copy any repository script into
  your folder before importing it.
* You may elaborate a scratch Lean file with `$T/el.sh {LABEL}-<name> <file>` (it applies the
  lakefile's four options, and refuses a file that uses a name nobody probed; a copy of the module
  with a line changed is a fair fire test). Each label must be new and start with `{LABEL}-`.
* You have at most 40 tool calls. At the cap, write what you have, and list in the report what you
  did not check.
* Write your report to `$EVD/reviews/{LABEL}.md`, then return as your final answer only that
  file's sha256 (the 64 hex digits that `sha256sum $EVD/reviews/{LABEL}.md` prints), nothing else.

## What to read

* The module: `$REPO/{PATH}`. It is `$EVD/stmt/{MSTMT}` with the draft's proofs put back by
  `$EVD/scripts/assemble.py` (spec `$EVD/spec/a{ITEM}.json`; the assembler's output, every edit it
  made to a draft line, is `$EVD/{ASSEMBLE}.out`), and its witnesses after its last line.
  `$EVD/stmt/{MSTMT}` is the reviewed statement file `$EVD/stmt/{STMT}.lean` with {MCHANGE};
  their difference is `$EVD/{MDIFF}.out`.
* The draft: `$REPO/incoming/{DRAFT}.lean`{START}.
* The statement review of job 1, `$EVD/reviews/rv1-statements.md`, and its confirming pass if
  there is one, `$EVD/reviews/rv1c-confirm.md`.
* The evidence for this module: its elaboration with the four options, `$EVD/{ELAB}.out`; its
  `lake build`, `$EVD/{BUILD}.out` (count the lines with `warning:`); a copy of the vacuity gate
  that imports only this module, `$EVD/{VAC}.out` (its one expected complaint is a stale entry of
  `tools/vacuity_reviewed.txt` for a theorem outside this module's imports; read the rest);
  `$EVD/{SORRY}.out` (`check_sorry`).
* For the library's conventions: `HANDOFF.md` sections 4 ("Satisfiability witnesses") and 5
  (naming); one existing module, `ClassicalLean/Probability/ChiSquared.lean`, and its witness.

## What to check

1. **Each main theorem against its plan row** (the order's table, below): FAITHFUL, GENERALIZED
   or WEAKER (WEAKER is a finding). Every hypothesis: is it used by the proof (a hypothesis no
   proof step needs is a finding to report, not to fix by deleting it), and is it one the row has
   or a harmless regularity condition?
2. **Statements unchanged**: each main theorem's and definition's statement is the statement
   file's, which job 1 reviewed (compare the two files: only proofs and witnesses may differ, and
   docstrings where the witness is described).
3. **The proofs**: the draft's, changed only where the namespace, imports or the Goal list's
   changes need it: every edit `assemble.py` printed is one of those (a `show` that changed the
   goal became `change`; a `first` chain or `try` cut to the step that fires; a deprecated name
   replaced by the one its warning gives; a full name rewritten for the new namespace).
4. **Each witness against the order's rule 4** (below): its form, the theorem called by its full
   name, every chosen argument by name, the docstring, no forbidden word, one inline block with no
   helper declaration, no `open` beyond the module's top-level ones except `open … in` lines of its
   own, and not degenerate in any of the ways rule 4 lists.
5. **Every declaration in the namespace** `{NS}`, private ones included (only the witnesses, which
   are `example`s, come after its `end` line).
6. **Imports targeted**: no `import Mathlib`, each import a module the file needs.
7. **Every private helper's statement**: true, what its use needs, no hidden assumption.
8. **Docstrings**: the module docstring lists the results and says what they state, and credits
   the draft; each main theorem's docstring names its item ("Item {ITEM} of MATH-PLAN-library-2")
   and does not misstate it; what the module docstring says of the witness is what the witness is.
9. **No main theorem whose conclusion is a recursive predicate that is `True` everywhere.**
10. **The build**: `lake build` of the module reported 0 warnings and 0 errors; the vacuity copy
   flags nothing of this module.

Severities: BLOCKING (a statement wrong, weaker than its row, or not the reviewed one; a witness
that fails rule 4; a declaration outside the namespace; a warning in the build), MAJOR (an
untargeted import, a docstring that misstates a statement, a proof change beyond what the Goal list
and the namespace need), MINOR (wording, style). Give each finding's file and line, what is wrong,
and the fix you propose.

## The report

Its first line is `VERDICT: CLEAN` or `VERDICT: FINDINGS <n>` (with the count of each severity).
Then: the verdict of each main theorem against its row, with your reason in a sentence or two;
each witness against rule 4; the findings, numbered; a section "Not checked" (write "nothing" if
you checked everything above), and the number of tool calls you used.
