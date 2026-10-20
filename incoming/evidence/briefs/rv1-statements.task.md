# Brief: the statement review of order CLOUD-MATH-2, job 1 (review `rv1-statements`)

Written on 2026-10-20 by the Claude Code cloud session executing order CLOUD-MATH-2. Your run ends
by 2026-10-20 20:15 UTC: have your report written before then.

You are a fresh reviewer: you have not seen this session's work. Review five statement files cold,
against their plan rows and their drafts. Each file is a new module of the library
`classical-lean` as it will land, with every theorem's and lemma's proof replaced by `sorry` (by
design: proofs are not reviewed now) and every definition's full body kept (a definition's body is
part of its statement).

## The order and its plan rows

The order is `/home/user/classical-lean/records/orders/20261020T181822Z__claude-ai__order-cloudmath2-power-method-pseudoinverse-chi-squared-kkt-huffman.md`.
Read in it: the first table (the plan rows, the main theorems, the modules, the drafts), the Goal
list after it (the changes asked of each draft), and its rules 1, 2 and 7.

## The files (read-only for you)

| item | statement file | draft |
|---|---|---|
| 147 | `/root/cm2-evidence/stmt/PowerMethod.lean` | `/home/user/classical-lean/incoming/d147-r1-s2.lean` |
| 150 | `/root/cm2-evidence/stmt/Pseudoinverse.lean` | `/home/user/classical-lean/incoming/d150-r1-s2.lean` |
| 151 | `/root/cm2-evidence/stmt/ChiSquared.lean` | `/home/user/classical-lean/incoming/d151-r9-s1.lean` |
| 152 | `/root/cm2-evidence/stmt/KKT.lean` | `/home/user/classical-lean/incoming/d152-r2-s1.lean` |
| 153 | `/root/cm2-evidence/stmt/Huffman.lean` | `/home/user/classical-lean/incoming/d153-r1-s2.lean` |

Evidence the session made, which you may check or redo: each statement file elaborated with rc 0
and only `sorry` warnings (`/root/cm2-evidence/stmt-PowerMethod.out`, `stmt-KKT.out`,
`stmt2-ChiSquared.out`, `stmt2-Huffman.out`, `stmt3-Pseudoinverse.out`, same folder); and a type
comparison, draft against statement file, of every main theorem and definition printed with
`set_option pp.fullNames true` (`/root/cm2-evidence/typecmp-147.out`, `typecmp-150.out`,
`typecmp-151.out`, `typecmp-152.out`, `typecmp-153.out`, `typecmp-153b.out`, made by
`/root/cm2-evidence/scripts/typecmp.py` from `types-d*.out` and `types-s*.out` in the same folder).
Do not take that evidence on trust; it is there to save you time where you agree with it.

## What you check (the order's rule 7, its statement checks)

For each item:

1. Each main theorem (the order's table names them) and each definition named there, against its
   plan row: FAITHFUL, GENERALIZED or WEAKER. WEAKER is a finding.
2. Each main theorem and definition against the draft's: the same, apart from the Goal list's
   changes and the move into the module's namespace. Any other change of meaning is a finding.
3. The Goal list's changes, where they touch statements, docstrings, namespaces and imports: made,
   and made correctly.
4. Every declaration, private ones included, inside the module's namespace (the module name).
5. Imports targeted: no `import Mathlib`, and nothing imported that the file does not need.
6. Every private helper's statement: true as far as you can tell, and saying what its docstring
   says.
7. No main theorem whose conclusion is a recursive predicate that is `True` everywhere.
8. Every docstring, the module docstring included: it says what the Lean says. A claim the Lean
   does not support (a wrong name, a wrong hypothesis, a wrong description of the proof route) is
   a finding.

## How you work

- Work in your own scratch folder, `/root/cm2-review-1` (create it). Start every Bash command with
  `. $HOME/cm2-env.sh && `. Copy any repository script into your folder before you import it.
  Write nothing in the repository, and nothing in `/root/cm2-evidence` except your report and the
  outputs that `el.sh` writes there itself.
- To elaborate a Lean file, copy it into your folder and run `$T/el.sh <label> <file>` with a label
  that starts with `rv1-` and is new each time (the tool refuses a used label). It applies the
  library's four lakefile flags and logs the run in the session's evidence log. It refuses a file
  that uses a name nobody probed; to probe, run `EL_PROBE=1 $T/el.sh rv1-probe-<n> <file>` on a
  file of `#check @Name` lines.
- Do not run `lake build`, the axiom gate, the vacuity gate, or any git command that writes.

## Your report

Write it to `/root/cm2-evidence/reviews/rv1-statements.md`, in this shape:

- for each item, each main theorem and definition with FAITHFUL, GENERALIZED or WEAKER and one
  sentence why;
- your findings, numbered, each with a severity, BLOCKING (a statement or definition wrong, weaker
  than its row, or changed beyond the Goal list; a declaration outside its namespace;
  `import Mathlib`) or MINOR (a docstring inaccuracy, a missing docstring item, an unneeded
  import), and the file and line;
- as its last line, `VERDICT: CLEAN` if you have no finding, else `VERDICT: FINDINGS <n>`.

Then return only that file's sha256 (the first field `sha256sum` prints), and nothing else.
