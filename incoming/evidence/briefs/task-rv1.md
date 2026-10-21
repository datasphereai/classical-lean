# Statement review `rv1-statements` (order CLOUD-MATH-3, job 1 step 4)

You are a cold reviewer: you have not seen this work, and you check it. The library is the Lean 4
repository `classical-lean` (Lean and Mathlib v4.34.0), cloned at `$REPO`. Order CLOUD-MATH-3
lands five proved drafts as five new modules. Before any proof enters a module, the statements are
reviewed: that is your job. This run ends when your report is written, and by
2026-10-21T02:30Z at the latest (`date -u` gives the time; if you reach that time, write what you
have and list the rest as not checked).

## How you work

* Start every Bash command with `. $HOME/cm3-env.sh && ` (it sets `REPO`, `T`, `EVD`, `BASE`, the
  Lean `PATH` and `PYTHONDONTWRITEBYTECODE=1`).
* Work in the scratch folder `$HOME/cm3-review-1` (create it). Never write inside `$REPO`: no file,
  no `git` command that changes anything, no `lake build`. Copy any repository script into your
  folder before importing it.
* You may elaborate a scratch Lean file with `$T/el.sh rv1-<name> <file>` (it applies the
  lakefile's four options and refuses a file that uses a name nobody probed; every name in these
  files is probed already). Each label must be new and start with `rv1-`.
* You have at most 40 tool calls. At the cap, write what you have, and list in the report what you
  did not check.
* Write your report to `$EVD/reviews/rv1-statements.md`, then return as your final answer only
  that file's sha256 (the 64 hex digits that `sha256sum $EVD/reviews/rv1-statements.md` prints),
  nothing else.

## What to read

* The five statement files, one per module, each with every proof replaced by `sorry` and every
  `def` whole: `$EVD/stmt/SubgradientMethod.lean` (item 113), `$EVD/stmt/EfronStein.lean` (121),
  `$EVD/stmt/ChannelCapacity.lean` (130), `$EVD/stmt/BernsteinInequality.lean` (124),
  `$EVD/stmt/OrderStatistics.lean` (126). Each is meant to become
  `ClassicalLean/<Folder>/<Name>.lean` with the draft's proofs put back.
* The five drafts: `$REPO/incoming/d113-r1-s1.lean`, `d121-r3-s1.lean`, `d130-r1-s1.lean`,
  `d124-r4-s2.lean`, `d126-r2-s2.lean`, and the witness starts
  `$REPO/incoming/witness-starts/w124-tail.lean` and `w126-tail.lean` (the witnesses are not
  under review here; their imports are).
* The evidence: each statement file's elaboration, `$EVD/stmt-<item>.out` (rc 0, only `sorry`
  warnings); the type comparisons `$EVD/typecmp2-<item>.out` (each main theorem's and public
  definition's type printed with `pp.fullNames` from the draft and from the statement file, the
  two compared by `$EVD/scripts/typecmp3.py`, its inputs in `$EVD/typecmp/`), and the definition
  bodies compared the same way, `$EVD/printcmp-121.out`, `printcmp-130.out`, `printcmp-126.out`;
  the import tests, `$EVD/imports-113.out`, `imports4-121.out`, `imports-130.out`,
  `imports-124.out`, `imports-126.out` (each the draft with the Goal list's proof changes, its
  witness start for 124 and 126, and the statement file's imports in place of `import Mathlib`,
  elaborated: rc 0 means the imports cover the proofs; the files are `$EVD/imports/t*.lean`).
* For the library's conventions: `HANDOFF.md` sections 4 ("Satisfiability witnesses") and 5
  (naming); one existing module, `ClassicalLean/Probability/ChiSquared.lean`.

## What to check

For each of the five items:

1. **Each main theorem against its plan row** (the order's table, below): give a verdict,
   FAITHFUL (says what the row says), GENERALIZED (says more: the row's statement follows from it)
   or WEAKER (says less: a finding). Read every hypothesis and say whether it is one the row has,
   or a harmless regularity condition, or an addition that weakens the theorem.
2. **Each statement and each definition against the draft's**: only the namespace prefix may
   differ, and the changes the order's Goal list asks (below). A statement changed in any other
   way, a hypothesis added or dropped, a definition's body changed: a finding.
3. **The definitions' bodies** (121's `wmean`, `wvar`, `weight`, `expect`, `variance`,
   `coordVar`; 126's `orderStat`; 130's private `bscJoint`): a definition's body is part of the
   statement. Check that each means what its docstring and the plan row say (for example that
   `coordVar` is the variance in one coordinate with the others held, and that
   `orderStat v ⟨k - 1, _⟩` is the `k`-th smallest entry).
4. **Namespaces**: every declaration, private ones included, inside the module's namespace
   (`ClassicalLean.Analysis.SubgradientMethod`, `ClassicalLean.Probability.EfronStein`,
   `ClassicalLean.InformationTheory.ChannelCapacity`, `ClassicalLean.Probability.BernsteinInequality`,
   `ClassicalLean.Probability.OrderStatistics`); for 121, that the draft's namespace `EfronStein`
   and its `open EfronStein` are gone; for 130, that `open ClassicalLean.Simplex` stays.
5. **Imports**: no `import Mathlib`; each import targeted (a module the file needs); and the
   import tests above show they cover the proofs (and the witness starts of 124 and 126).
6. **Every private helper's statement**: is it true, is it what its proof needs, does it hide an
   assumption?
7. **Docstrings**: the module docstring lists the module's results and says what they state; each
   main theorem's docstring names its item ("Item 113 of MATH-PLAN-library-2" and so on) and does
   not misstate the theorem; a GENERALIZED claim in a docstring is right.
8. **No main theorem whose conclusion is a recursive predicate that is `True` everywhere.**

Severities: BLOCKING (a statement wrong, weaker than its row, or not the draft's; a declaration
outside the namespace), MAJOR (an untargeted import, a docstring that misstates a statement),
MINOR (wording, style). Give each finding's file and line, what is wrong, and the fix you propose.

## The report

Its first line is `VERDICT: CLEAN` or `VERDICT: FINDINGS <n>` (with the count of each severity).
Then one section per item: the verdict of each main theorem against its row, with your reason in a
sentence or two; the findings, numbered; then a section "Not checked" (write "nothing" if you
checked everything above), and the number of tool calls you used.
