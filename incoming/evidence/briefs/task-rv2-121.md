# Module review `rv2-121` (order CLOUD-MATH-3, job 2, item 121)

You are a cold reviewer: you have not seen this work, and you check it. The library is the Lean 4
repository `classical-lean` (Lean and Mathlib v4.34.0), cloned at `$REPO`. Order CLOUD-MATH-3
lands five proved drafts as five new modules; this review is of one of them, item 121, the
module `ClassicalLean.Probability.EfronStein` in `$REPO/ClassicalLean/Probability/EfronStein.lean`, not yet committed. Its text is final unless you find
something. This run ends when your report is written, and by 2026-10-21T03:00Z at the latest (`date -u`
gives the time; if you reach that time, write what you have and list the rest as not checked).

## How you work

* Start every Bash command with `. $HOME/cm3-env.sh && ` (it sets `REPO`, `T`, `EVD`, `BASE`, the
  Lean `PATH` and `PYTHONDONTWRITEBYTECODE=1`).
* Work in the scratch folder `$HOME/cm3-review-4` (create it). Never write inside `$REPO`: no
  file, no `git` command that changes anything, no `lake build`. Copy any repository script into
  your folder before importing it.
* You may elaborate a scratch Lean file with `$T/el.sh rv2-121-<name> <file>` (it applies the
  lakefile's four options, and refuses a file that uses a name nobody probed; a copy of the module
  with a line changed is a fair fire test). Each label must be new and start with `rv2-121-`.
* You have at most 40 tool calls. At the cap, write what you have, and list in the report what you
  did not check.
* Write your report to `$EVD/reviews/rv2-121.md`, then return as your final answer only that
  file's sha256 (the 64 hex digits that `sha256sum $EVD/reviews/rv2-121.md` prints), nothing else.

## What to read

* The module: `$REPO/ClassicalLean/Probability/EfronStein.lean`. It is `$EVD/stmt/EfronStein.m2.lean` with the draft's proofs put back by
  `$EVD/scripts/assemble.py` (spec `$EVD/spec/a121.json`; the assembler's output, every edit it
  made to a draft line, is `$EVD/assemble2-121.out`), and its witnesses after its last line.
  `$EVD/stmt/EfronStein.m2.lean` is the reviewed statement file `$EVD/stmt/EfronStein.lean` with the import `Mathlib.Tactic.FinCases` (for the witnesses' `fin_cases`) and one sentence on the witnesses added to the module docstring;
  their difference is `$EVD/mdiff-121.out`.
* The draft: `$REPO/incoming/d121-r3-s1.lean` (the item has no witness start; its two witnesses are new).
* The statement review of job 1, `$EVD/reviews/rv1-statements.md`, and its confirming pass if
  there is one, `$EVD/reviews/rv1c-confirm.md`.
* The evidence for this module: its elaboration with the four options, `$EVD/m121-module.out`; its
  `lake build`, `$EVD/build-121.out` (count the lines with `warning:`); a copy of the vacuity gate
  that imports only this module, `$EVD/vac-121.out` (its one expected complaint is a stale entry of
  `tools/vacuity_reviewed.txt` for a theorem outside this module's imports; read the rest);
  `$EVD/sorry-121.out` (`check_sorry`).
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
5. **Every declaration in the namespace** `ClassicalLean.Probability.EfronStein`, private ones included (only the witnesses, which
   are `example`s, come after its `end` line).
6. **Imports targeted**: no `import Mathlib`, each import a module the file needs.
7. **Every private helper's statement**: true, what its use needs, no hidden assumption.
8. **Docstrings**: the module docstring lists the results and says what they state, and credits
   the draft; each main theorem's docstring names its item ("Item 121 of MATH-PLAN-library-2")
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
