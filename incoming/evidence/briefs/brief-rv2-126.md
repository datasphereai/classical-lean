# Module review `rv2-126` (order CLOUD-MATH-3, job 2, item 126)

You are a cold reviewer: you have not seen this work, and you check it. The library is the Lean 4
repository `classical-lean` (Lean and Mathlib v4.34.0), cloned at `$REPO`. Order CLOUD-MATH-3
lands five proved drafts as five new modules; this review is of one of them, item 126, the
module `ClassicalLean.Probability.OrderStatistics` in `$REPO/ClassicalLean/Probability/OrderStatistics.lean`, not yet committed. Its text is final unless you find
something. This run ends when your report is written, and by 2026-10-21T03:45Z at the latest (`date -u`
gives the time; if you reach that time, write what you have and list the rest as not checked).

## How you work

* Start every Bash command with `. $HOME/cm3-env.sh && ` (it sets `REPO`, `T`, `EVD`, `BASE`, the
  Lean `PATH` and `PYTHONDONTWRITEBYTECODE=1`).
* Work in the scratch folder `$HOME/cm3-review-8` (create it). Never write inside `$REPO`: no
  file, no `git` command that changes anything, no `lake build`. Copy any repository script into
  your folder before importing it.
* You may elaborate a scratch Lean file with `$T/el.sh rv2-126-<name> <file>` (it applies the
  lakefile's four options, and refuses a file that uses a name nobody probed; a copy of the module
  with a line changed is a fair fire test). Each label must be new and start with `rv2-126-`.
* You have at most 40 tool calls. At the cap, write what you have, and list in the report what you
  did not check.
* Write your report to `$EVD/reviews/rv2-126.md`, then return as your final answer only that
  file's sha256 (the 64 hex digits that `sha256sum $EVD/reviews/rv2-126.md` prints), nothing else.

## What to read

* The module: `$REPO/ClassicalLean/Probability/OrderStatistics.lean`. It is `$EVD/stmt/OrderStatistics.m.lean` with the draft's proofs put back by
  `$EVD/scripts/assemble.py` (spec `$EVD/spec/a126.json`; the assembler's output, every edit it
  made to a draft line, is `$EVD/assemble2-126.out`), and its witnesses after its last line.
  `$EVD/stmt/OrderStatistics.m.lean` is the reviewed statement file `$EVD/stmt/OrderStatistics.lean` with its module docstring's sentence on the witness start no longer naming the start by its path in `incoming/` (a path the merge removes), and saying that the witness calls the theorem by its full name;
  their difference is `$EVD/mdiff-126.out`.
* The draft: `$REPO/incoming/d126-r2-s2.lean`, and its witness start `$REPO/incoming/witness-starts/w126-tail.lean` (the module's witness is that start with the theorem called by its full name; their difference is `$EVD/wdiff-126.out`).
* The statement review of job 1, `$EVD/reviews/rv1-statements.md`, and its confirming pass if
  there is one, `$EVD/reviews/rv1c-confirm.md`.
* The evidence for this module: its elaboration with the four options, `$EVD/m126-module.out`; its
  `lake build`, `$EVD/build-126.out` (count the lines with `warning:`); a copy of the vacuity gate
  that imports only this module, `$EVD/vac-126.out` (its one expected complaint is a stale entry of
  `tools/vacuity_reviewed.txt` for a theorem outside this module's imports; read the rest);
  `$EVD/sorry-126.out` (`check_sorry`).
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
5. **Every declaration in the namespace** `ClassicalLean.Probability.OrderStatistics`, private ones included (only the witnesses, which
   are `example`s, come after its `end` line).
6. **Imports targeted**: no `import Mathlib`, each import a module the file needs.
7. **Every private helper's statement**: true, what its use needs, no hidden assumption.
8. **Docstrings**: the module docstring lists the results and says what they state, and credits
   the draft; each main theorem's docstring names its item ("Item 126 of MATH-PLAN-library-2")
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

## The order's Goal section (quoted verbatim from the order's copy, `records/orders/20261021T002100Z__claude-ai__order-cloudmath3-subgradient-efron-stein-bernstein-order-statistics-bsc.md`; uncut)

Put five proved results into the library as five new modules, each under the library's gates, with witnesses, reviews and records, on branch `cloud-math-3`. The proofs already exist in `incoming/` (read `incoming/README.md`). The work is to land them the way this library lands work: right names and namespaces, targeted imports, docstrings, witnesses, cold reviews, records. Not to re-prove them.

| item | plan statement (the library's second plan, below its cut) | main theorems | new module | draft | its last review |
|---|---|---|---|---|---|
| 113 | The subgradient method: for convex `f` with subgradients of norm at most `G` and step `η`, the best of the first `T` points is within `(‖x₀ − z‖² + η² G² T)/(2 η T)` of `f z`. | `min_sub_le_of_subgradient` | `ClassicalLean.Analysis.SubgradientMethod` | d113-r1-s1 | GENERALIZED |
| 121 | Efron–Stein for independent coordinates on finite sets: `Var f ≤ ∑ᵢ E[Varᵢ f]`; so with bounded differences `cᵢ`, `Var f ≤ ∑ cᵢ²/4`. | `variance_le_sum_variance_coord`, `variance_le_sum_sq_div_four` (and the definitions `wmean`, `wvar`, `weight`, `expect`, `variance`, `coordVar`) | `ClassicalLean.Probability.EfronStein` | d121-r3-s1 | FAITHFUL |
| 130 | The binary symmetric channel with crossover `ε` has capacity `log 2 − h(ε)`, reached by the uniform input. | `mutualInfo_bsc_le`, `mutualInfo_bsc_half` | `ClassicalLean.InformationTheory.ChannelCapacity` | d130-r1-s1 | FAITHFUL |
| 124 | Bernstein's inequality: independent `X i` with mean 0, `X i ≤ b` and `∑ E[X i²] ≤ v` have `P(∑ X i ≥ t) ≤ exp(−t²/(2(v + b t/3)))`. | `measureReal_sum_ge_le_bernstein` | `ClassicalLean.Probability.BernsteinInequality` | d124-r4-s2 | FAITHFUL |
| 126 | Order statistics: for independent draws with `P(X i ≤ x) = F`, the `k`-th smallest is at most `x` with chance `∑_{j ≥ k} C(n, j) F^j (1 − F)^(n−j)`. | `measureReal_orderStat_le` (and the definition `orderStat`) | `ClassicalLean.Probability.OrderStatistics` | d126-r2-s2 | FAITHFUL |

The rows are in landing order, cheapest first. Every name in the "main theorems" column is a main theorem for the rules below (witness, vacuity, review). The changes asked of each draft (from its reviews, lane files you cannot read, and the measurements above):
- every item: every declaration inside its module's namespace (rule 2); targeted imports (no `import Mathlib`), which cover the witnesses too; a module docstring listing the module's results; each main theorem's docstring names its item ("Item 113 of MATH-PLAN-library-2"); a step whose effect is not determined (a `first | … | …` chain, a `try` tactic) is cut to what fires; and every warning the four-flag elaboration or `lake build` reports is fixed in the proof only, each fix listed in round 68, because a module must build with 0 warnings (rule 20: linter results count from `lake build`, which may report a little more or less than the list below). Measured at 9c0639c with the four flags:
  - 113: none.
  - 121: `show` that changes the goal, lines 81, 93, 207, 220, 228 and 241 (use `change`).
  - 124: unused branches of `first` chains, the elaboration says "this tactic is never executed", at lines 14, 146, 147, 148, 164, 178 and 199 (cut each chain to the branch that fires); the chain at lines 224 to 226, `first | (field_simp; ring) | field_simp`, whose second branch never runs, line 226 (cut it to `field_simp; ring`); the chain in `hSmeas`, lines 157 to 160, which has no warning (find the branch that fires, likely its third, `fun_prop`, since neither earlier branch is flagged, and cut the chain to it); `show` that changes the goal, line 131; `push_neg` deprecated (use `push Not`), line 194.
  - 126: `push_neg` deprecated, lines 43 and 49; `if_pos` and `if_neg` deprecated (use `ite_eq_left` and `ite_eq_right`), lines 59, 63, 114, 116, 121, 122, 126, 127, 152 and 154; `Set.mem_setOf_eq` deprecated (use `Set.mem_ofPred_eq`), lines 96 and 133; `show` that changes the goal, lines 98 and 158.
  - 130: `show` that changes the goal, lines 23, 25, 27, 29, 35, 97 and 117; `if_pos` and `if_neg` deprecated, lines 24, 26, 28 and 30.
- 121: the root namespace `EfronStein` becomes the module's namespace `ClassicalLean.Probability.EfronStein`, the two main theorems move inside it, and their `EfronStein.`-prefixed references are rewritten for it; the line `open EfronStein` after `end EfronStein` (line 261) is removed, since that namespace no longer exists. The definitions keep their names (`variance`, `expect` and the rest): inside the namespace they do not clash with Mathlib's `ProbabilityTheory.variance`, which no line opens; job 1's type comparison (step 3) confirms that each main theorem still means the draft's.
- 130: its `open ClassicalLean.Simplex` stays (it is how `mutualInfo` and `shannonEntropy_le_log_card` are reached); the private `bscJoint` and its lemmas move inside the namespace. If job 1's type comparison shows a changed type for any of 130's names, write that name with `ClassicalLean.Simplex.` in full.

## The order's rules 1, 2, 4 and 7 (quoted verbatim from the same file; each paragraph uncut)

1. **Statements as reviewed.** Each main theorem keeps its draft's statement, apart from the changes in the Goal list and moving it into the namespace. Never weaken, restate or add a hypothesis to make anything easier. A statement you find false is reported with its counterexample and narrowed, said plainly in its docstring, round 68 and the report; never dropped silently.
2. **Namespaces and imports.** Every declaration, private ones included, sits inside its module's namespace (`ClassicalLean.Analysis.SubgradientMethod` and so on; follow HANDOFF section 5 where it says more). The axiom gate checks only constants under `ClassicalLean`, so a declaration outside it escapes the gate. Imports are targeted: no `import Mathlib`.
4. **Witnesses.** Every main theorem with a hypothesis gets a witness in HANDOFF section 4's form, after its module's last line: `example := Full.name (x := …) h₁ h₂ …`, the theorem called by its full name, every chosen argument by name, optional `open … in` lines of their own and no other `open` than the module's top-level ones, the docstring "The hypotheses of `name` hold together: …", no `sorry`, `admit`, `native_decide`, `implemented_by`, `axiom` or `set_option`, one inline block with no helper declarations, and not degenerate as section 4 says (no empty, zero or single-point case, no Lean junk value, no boundary where a constant vanishes, families and matrices of size at least 2 unless the theorem fixes it, no function identically 0 past some point, no kernel or observation that does not depend on its parameter). Here that is seven witnesses: 113, 121 twice, 124, 126, 130 twice. 124 and 126 need independent random variables on one probability space, and their `[IsProbabilityMeasure μ]` binders have no name, so the law must be one Lean finds that instance for by itself. claude-ai wrote and compiled a start for each, `incoming/witness-starts/w124-tail.lean` and `w126-tail.lean`: the coordinates of `Measure.pi` of copies of Mathlib's `bernoulliMeasure` (two fair `±1` coins for 124, with `b = 1`, `v = 2` and `t = 1`; three fair `0`/`1` coins for 126, with `x = 1/2`, `F = 1/2` and `k = 2`), each elaborated at 9c0639c after its draft with rule 20's four flags, rc 0 and no message on its own lines. The starts rely on the draft's top-level `open MeasureTheory ProbabilityTheory` line (`open MeasureTheory ProbabilityTheory Finset` for 126), so keep it above the `namespace` line. Give the theorem its full name in the module and check each start as you check any witness: it is starting material, not exempt. If you change one, keep away from `t = 0`, `b = 0`, `v = 0`, `k = 1` and `k = n`. For 130, take `ε = 1/4` (at `ε = 1/2` the capacity is 0, a boundary) and, for `mutualInfo_bsc_le`, an input that is not uniform. Log `date +%s` through `ev.sh` when you start a witness; one still missing 1800 seconds later (3600 for 124 and 126) makes its item not closed.
7. **Reviews.** Job 1's statement review, then one cold review per module once its text is final, each by a fresh subagent that has not seen your work, with a brief built as rule 26 says. Each brief caps its reviewer at 40 tool calls; at the cap the reviewer writes what it has and lists what it did not check. Anything a review lists as not checked gets a fresh reviewer for those parts only, before the commit, within the same limit of two fix-and-confirm rounds. The module review checks each statement against its plan row (FAITHFUL, GENERALIZED or WEAKER; WEAKER is a finding: restore the draft's statement or report it as a narrowing under rule 1), every hypothesis used, each witness against rule 4, every declaration in the namespace, imports targeted, every private helper's statement, and no main theorem whose conclusion is a recursive predicate that is `True` everywhere. A review with findings ends with a confirming pass on the fix only, by a fresh reviewer; a review with no findings needs none. At most two fix-and-confirm rounds; an item not clean after two is not closed.

## The rules you are checked against (quoted verbatim from `HANDOFF.md` section 6, generated block; uncut)

12. *Reviewers work in a scratch directory outside the repository*, with `PYTHONDONTWRITEBYTECODE=1`, copy a repository script before importing it, and are followed by a `git status` check (round 20: two reviewers wrote outside their brief).
14. *Before-and-after evidence is a type dump, read by its `DIFF` line and judged up to proof irrelevance.* (absorbs rule 25) Before-and-after evidence is `TypeDump.lean` with `g5_typediff.py`, not name lists alone (round 19). Read its `DIFF removed= added= changed=` line, not its exit code, which is 0 whenever nothing changed even if records were removed or added (order G-6, round 21). **Amended 2026-09-24 UTC (order G-8, rule 25, now part of this rule):** the pair is now `~/work/_bump-evidence/TypeDumpPI.lean` with `g8_typediff.py`, which print today's fields and the same forms with every proof replaced by one placeholder; their `DIFF` line adds `proof_only=`. They passed their controls in order G-8's J1 (round 25). `TypeDump.lean` and `g5_typediff.py` are kept, unchanged. Type-dump Done-means are judged up to proof irrelevance: a record whose raw form differs only inside proof terms is `PROOF-ONLY`: listed, explained, and not counted as changed (round 24's addendum, item 1; order G-8 §2's ruling). Without a tool that has passed its controls, such a record is settled by a Lean file with a fire test, as round 23 did (`DefeqCheck.lean`).
17. *Every reviewer and checker output is saved verbatim, with its sha256, in the order's evidence directory when it returns.* (absorbs rule 33) Fragments quote from the saved file. A workflow returns each report's text with its sha256, and the saving command compares the two before the report is read; where reviews are dispatched outside a workflow, the same holds by extracting each agent's returned text from its hand-back and hashing the saved file against it. Sources: order G-6's Close check: the statement reviews were paraphrased and their outputs not kept (rule 17); nothing in orders G-5 to G-9 had checked that a saved review was the text its agent returned, until G-9's addendum compared all twelve against the harness's journal, round 28's addendum item 23 (rule 33).
18. *Records follow the clock.* When a step runs out of the order's sequence, or overlaps another (a search re-run after the proof, step commits cut from a finished module, proving while a review runs), the fragment says so at that step, with times (order G-7 §0 row 13; rounds 21 and 22).
19. *Research notes name the source of every proof route they propose*: derived here, a textbook with its reference, or a prior-art file, so that the module docstring's credit can be exact (round 22: the base-2 route was the prior art's).
20. *`lake env lean` checks types only: scratch proofs are elaborated with the lakefile's options, and linter results count only from `lake build`.* (absorbs rule 11) Linter results count only from `lake build`, run from the repository root: `[leanOptions]` apply only there, and the header linter finds the root by a relative path. Scratch proofs are elaborated with the lakefile's options: `lake env lean -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3 <file>`. Plain `lake env lean` applies none of `[leanOptions]`, so a proof checked only that way can land with linter warnings. Sources: rounds 19 and 20 (rule 11); round 24: four `flexible` warnings at order G-7's first J3 build, and order G-8 §0 row 17 (rule 20).
22. *Every quote in a fragment, block or inline, is checked by a script against its saved source before the fragment is committed* (absorbs rule 34), with a negative control (for inline quotes, a planted misquote), and every omission inside a quote is marked `[...]`. An inline quote is a phrase in quotation marks or backticks attributed to a document; it is checked by script against its source, as block quotes are. Sources: round 24's addendum, items 3 and 4, and `g7/close/quotecheck.py` (rule 22); `inlinecheck.py`, and round 28's addendum items 11 and 23: three inline quotes cut or paraphrased their sources and the block-quote check never saw them (rule 34).
23. *Evidence commands run through one helper, and the evidence log holds only what was measured.* (absorbs rules 5, 8, 30, 32) The helper takes the prediction as an argument, refuses to run without one, and logs the command with its own `$?`; every evidence-log line carries its command and its rc. An evidence log records only a measured rc, taken from the command's own `$?`: a run that did not happen is logged `NOT RUN`, never a placeholder, and a refused call is logged `NOT RUN` in the next helper call, with the refused command's label and the guard's message, so that the final report's count of refusals is a `grep` of `evidence.log` and not a recollection. Every write, hash and edit of an evidence or records file runs through the helper, or is listed in the plan and the fragment before the commit that carries it. A commit runs only when its gates exited 0 in the same run. Sources: round 24's addendum, items 7, 8 and 9, and order G-8's `ev.sh` and `land.sh`, round 25 (rule 23); rule 5; round 20, the Close check's addendum (rule 8); order G-9 §0 row 15: the report said "nothing stopped" and "the only refusals were my own tools" over one guard refusal the log never saw (rule 30); order G-9 ran five such commands outside the helper, round 28's addendum item 20 (rule 32).
26. *Every brief is built by script from `HANDOFF.md` and saved with its sha256 before it is sent; every reader, research and review brief quotes the rules it will be checked against* (absorbs rule 24), at least rules 16 to 25 as numbered on 2026-10-18 (where one of them has since been merged, the rule that absorbed it). Briefs are built as order G-8's Close-check brief was (`close-brief-make`); a brief that claims to quote a rule verbatim quotes it verbatim, cuts marked `[...]`. Sources: round 24's addendum, item 6 (rule 24); round 26's addendum, item 16: the J3 post-proof brief shortened rules 16–25 without marking the cuts, and the J2 briefs were never saved (rule 26).
31. *A job's work runs in order: no statement is drafted before the job's last search and cell has run, a statement review's verdict is in before any proof of those statements, and every new declaration is reviewed cold before its commit.* (absorbs rules 13, 16, 21, 29) No statement of a job is drafted until the job's last search and cell has run, the ones a plan critic adds included; a statement drafted in a plan is drafted, so a job's recorded searches and junk cells come before any of its statements is drafted, the plan's drafts included. A cell a review adds after a draft is run and logged, and the draft re-hashed and re-elaborated after it (rule 18); J1 item 12 checks it by mtime against the log. A statement review's verdict is in before any proof of those statements is written: research, other jobs' drafting, and gate runs may overlap a review; proofs of the statements under review may not. Every new declaration, private helpers included, is reviewed cold before its commit. A review fix that touches a proof line gets its delta check before the landing, as the review's condition asked. Sources: order G-9's J1 ran cells and reads after the first drafts, round 28's addendum item 17, a MAJOR finding (rule 31); round 24's addendum, item 2 (rule 21); order G-6's run: J2's and J3's statement reviews returned after their proofs were written, J2's compiled, and §0 row 13 of order G-7, rounds 21 and 22 (rule 16); round 20: three helpers were reviewed only after proving (rule 13); round 26's addendum, item 18: `hp.out` to `(Fact.out : p.Prime)` landed without its delta check, and the gates and the type dump then held, which is luck, not a check (rule 29).
