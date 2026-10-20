<!-- The order's text, as given in the prompt of Claude Code cloud session session_019tga5LT3iStpcstjGMLwLU (https://claude.ai/code/session_019tga5LT3iStpcstjGMLwLU), copied on 2026-10-20 (UTC) by that session before any Lean file changed, per records/README.md rule 2. Its file name gives claude-ai as the source, as the order's own Setup step 5 names it. -->

# Order CLOUD-MATH-2: five new modules from five proved drafts

## Goal

Put five proved results into the library as five new modules, each under the library's gates, with witnesses, reviews and records, on branch `cloud-math-2`. The proofs already exist in `incoming/` (read `incoming/README.md`). The work is to land them the way this library lands work: right names and namespaces, targeted imports, docstrings, witnesses, cold reviews, records. Not to re-prove them.

| item | plan statement (the library's second plan, below its cut) | main theorems | new module | draft | its last review |
|---|---|---|---|---|---|
| 147 | The power method: for a symmetric matrix with `\|λ₀\| > \|λ₁\|`, the iterates' direction approaches the top eigenvector at rate `(\|λ₁\|/\|λ₀\|)^k`. | `tendsto_powerIterate` | `ClassicalLean.Analysis.PowerMethod` | d147-r1-s2 | GENERALIZED |
| 150 | The Moore–Penrose pseudoinverse: its four equations, uniqueness, and least squares with a rank-deficient design. | `pinv_spec`, `pinv_unique`, `pinv_residual_dotProduct_le`, `pinv_eq_leastSquares` (and the definition `pinv`) | `ClassicalLean.Algebra.Pseudoinverse` | d150-r1-s2 | FAITHFUL |
| 151 | The chi-squared law: the sum of squares of `k` independent standard normals has the gamma law with shape `k/2` and rate `1/2`. | `hasLaw_sum_sq_gaussian` | `ClassicalLean.Probability.ChiSquared` | d151-r9-s1 | FAITHFUL |
| 152 | KKT conditions are necessary under Slater's condition (a strictly feasible point exists), for convex differentiable problems. | `exists_kkt_of_slater` | `ClassicalLean.Analysis.KKT` | d152-r2-s1 | FAITHFUL |
| 153 | Huffman's code has the least mean length among prefix-free codes. | `huffman_optimal` (and the definition `huffmanLength`) | `ClassicalLean.InformationTheory.Huffman` | d153-r1-s2 | GENERALIZED |

Every name in the "main theorems" column is a main theorem for the rules below (witness, vacuity, review). The changes asked of each draft, from its reviews (lane files you cannot read; summarised here):
- every item: every declaration inside its module's namespace (rule 2); targeted imports (no `import Mathlib`); a module docstring listing the module's results; each main theorem's docstring names its item ("Item 147 of MATH-PLAN-library-2"); a step whose effect is not determined (a `first | … | …` chain, a `try` tactic) is cut to what fires; and every warning the four-flag elaboration or `lake build` reports is fixed in the proof only, each fix listed in round 66, because a module must build with 0 warnings (rule 20: linter results count from `lake build`, which may report a little more or less than the list below). Measured at 9c0639c with the four flags:
  - 147: `show` that changes the goal, lines 12 and 22 (use `change`); `simpa` that should be `simp`, line 128; the never-run branch of the `first` chain, line 129.
  - 150: a section variable not used in the type of the private `exists_symm_ginv` (line 20), `exists_penrose` (line 85) and `penrose_unique` (lines 109 and 110): `omit … in` before each, or bind it where it is used; dropping an unused instance argument from a private helper is not a statement change of an item.
  - 151: none.
  - 152: `show` that changes the goal, lines 72, 73, 131, 132 and 202; `push_neg` deprecated (use `push Not`), lines 78, 121 and 175; `ContinuousLinearMap.add_apply`, `sum_apply`, `smul_apply` and `zero_apply` deprecated, lines 208 to 210 (use the names the warnings give).
  - 153: a section variable not used in the type of the private `exists_pair` (line 17); `dif_pos` and `dif_neg` deprecated, lines 68 and 72 (`dite_eq_left`, `dite_eq_right`); `push_neg` deprecated, line 240.
- 147: the docstring says what the iterates are (`T ^ k` applied to `x`, rescaled to unit component along the top eigenvector); the name stays `tendsto_powerIterate`; the `first` chain (lines 127 to 129) and the `try ring` (line 98) are cut to what fires.
- 151: replace the private `isProb_gamma_aux` (the draft's lines 54 to 58, docstring included) and its use in `hasLaw_sum_sq_gaussian` (`have := isProb_gamma_aux hpos …`) by Mathlib's `ProbabilityTheory.isProbabilityMeasure_gammaMeasure` (a theorem taking `0 < a` and `0 < r`, probed at 9c0639c); if the private lemma `complexMGF_gammaMeasure_aux` follows Mathlib's `ProbabilityTheory.eqOn_complexMGF_of_mgf'`, say so in a comment at that lemma.
- 153: `huffman_optimal` moves inside the module's namespace with everything else; its full-name references (`ClassicalLean.Huffman.huffAux_kraft`, `huffAux_opt`, `huffAux`, `huffmanLength`, one of them in its statement) are rewritten for the new namespace; its own binders `{ι α : Type*} [DecidableEq ι]` must not clash with the file's `variable {ι : Type*} [DecidableEq ι]` (close that section first, or drop the repeated binders).
- Witness starts: `incoming/d147-r1-s2-witness.lean` (compiled) and `incoming/d151-r9-s1-sat.lean` (compiled, its `k` a variable) are starting material for rule 4.

## This order and the repository's own documents

Where this order and `HANDOFF.md` differ, this order wins. In particular: you push `cloud-math-2` to GitHub yourself (HANDOFF section 6 says `master` moves only from DSMain; cloud sessions push only their own `cloud-*` branch); the gates are the six commands in End check 1; gate 7, the banned-vocabulary scan (it reads a term list kept only on DSMain), the bridge search and the report tool run on DSMain at the merge, not here. HANDOFF section 6's 21 rules apply as the table "HANDOFF's rules in this session" says.

## Branch rules (hard)

These override any branch this session was assigned; do not push an assigned `claude/*` branch.
- Work only on `cloud-math-2`. First confirm `origin/cloud-math-2` is `4d99afd873730fa5f1231c6d6c68f57f2601c4a0`, the seven `.lean` files' sha256s match `incoming/README.md`, and `cd incoming/tools && sha256sum -c SHA256SUMS` passes. If not, stop and report.
- Push only with `git push origin cloud-math-2`. Never push `master` or `main`, never force-push, never reset a pushed commit, open no pull request, merge nothing on GitHub. Every undo is a new commit.

## Scope

You may: add the five module files under `ClassicalLean/` (paths from the module names); add their five import lines at the end of the import block of `ClassicalLean.lean` (it lists imports in landing order); add entries to `tools/vacuity_reviewed.txt` only as rule 3 allows; write `records/` as rule 5 says; in `incoming/`, remove each draft and its witness start when its item lands or is not closed, and add `PREDICTIONS.md`, `reviews/`, `evidence/` and `REPORT.md`; `README.md` and `tools/` stay until the merge.
You may not change any existing module, any other file under `tools/`, `HANDOFF.md`, `ROADMAP.md`, `records/rules.toml`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` or `.github/`. Needing to is a stop: report it.

## Read first (all in the repository)

`records/README.md`; `HANDOFF.md` sections 0, 4 (the gates, and "Satisfiability witnesses"), 5 (naming) and 6 (all 21 rules and the standing answers); `tools/AxiomGate.lean` (how it counts, private declarations included); `incoming/README.md` and the headers of `incoming/tools/*`; the copies of orders CLOUD-MATH-1 and LEAN-32 under `records/orders/`, their INDEX and CLAIMS rows, and rounds 60 and 65 under `records/rounds/`, as the pattern for your records; one existing module from each target folder, for the licence header, the module docstring and the namespace style.

## Setup

1. Check the network: `curl -sSI https://cache.mathlib.org/ | head -3`. A connection error, or a 403 from the session's proxy, is a stop: report the exact output and do not build Mathlib from source. Any answer from cache.mathlib.org itself is a pass. Note `git ls-remote origin master` (you report it again at the end; the two must match).
2. Install the toolchain from `lean-toolchain` (elan, from GitHub) and run `lake exe cache get`. A refused download or a failed dependency clone is a stop: report it.
3. The environment file. Shell variables do not carry from one Bash call to the next, so write `$HOME/cm2-env.sh` with exactly these lines, the first with the repository's absolute path, and start every later Bash command with `. $HOME/cm2-env.sh && `:
   ```
   export REPO=<the absolute path that git rev-parse --show-toplevel prints>
   export T=$REPO/incoming/tools
   export EVD=$HOME/cm2-evidence
   export BASE=4d99afd873730fa5f1231c6d6c68f57f2601c4a0
   export PATH=$HOME/.elan/bin:$PATH
   export PYTHONDONTWRITEBYTECODE=1
   ```
   Then `mkdir -p $EVD/reviews && cp $T/allowlist.txt $EVD/`. Test the tools before first use: `CTEST=$HOME/ctools-test $T/test_ctools.sh $T > $HOME/ctools-test.out 2>&1`, which must give 41 `OK` lines and `BAD=0` (it uses its own folder and refuses to run in `$EVD`); then `cp $HOME/ctools-test.out $EVD/` and `$T/hl.sh tools-test $EVD/ctools-test.out`. A `BAD` line is a stop: report it.
   From here on: every command that measures, builds or hashes runs through `$T/ev.sh` (or `$T/hl.sh` for hashes), every Lean run on a scratch file or a module through `$T/el.sh`; every label is new (the tools refuse a used one); a records or evidence file written with the Write or Edit tool is hashed with `hl.sh` after it is written and before the commit that carries it (rule 23); after each commit you append `COMMIT <short hash>` to `$EVD/evidence.log` (rule 39).
4. Starting counts: the branch differs from 9c0639c only in `incoming/`, so 9c0639c's counts hold at the start: build 4178 jobs, axiom gate 3379 theorem constants, check_sorry 130 files, check_records 130 modules, vacuity gate PASS with 1 reviewed helper. Run `$T/ev.sh start-build "4178 jobs, 0 errors" lake build` in the background (a first build can pass the 10-minute limit on one command; its output is `$EVD/start-build.out`; read it until the build ends), then `$T/ev.sh start-axiom "PASS 3379" lake env lean tools/AxiomGate.lean`, both before any new module exists. If the VM kills the build for memory, retry once with a new label as `LEAN_NUM_THREADS=2 lake build`; if it is killed again, stop and report.
   Then the base closure, still before any new module exists: write `$EVD/closure-base.lean` with the four lines below, and run `$T/rootrun.sh closure-base "MOD lines for the library's closure" lake env lean $EVD/closure-base.lean` (rule 38's first use: it builds the root, then elaborates the file). Check through `ev.sh` (`grep` on `$EVD/evidence.log`) that the `closure-base-build` line comes before the `closure-base` line and that both name the same `head`; that is rule 38's test with the real build. `$EVD/closure-base.out` is the saved base list for rule 27.
   ```
   import ClassicalLean
   open Lean Elab Command in
   run_cmd do
     for m in (← getEnv).header.moduleNames do logInfo m!"MOD {m}"
   ```
5. Records first, in one commit with no `.lean` file: this order's text as `records/orders/<UTC>__claude-ai__order-cloudmath2-power-method-pseudoinverse-chi-squared-kkt-huffman.md`; its row in `records/orders/INDEX.md` (rows start `| CLOUD-MATH-2 |`); a row at the bottom of `records/CLAIMS.md` naming this cloud session and the five module paths; round 66's fragment, `records/rounds/<UTC>__round-66-power-method-pseudoinverse-chi-squared-kkt-huffman.md`, naming the five module files by full path. And, by records/README.md rule 2, add RULES-1's push to its INDEX row, at the end of its State column (where LEAN-32's row carries its own), and to its CLAIMS row, in the same place as LEAN-32's: "; pushed by Dustin: DSMain's master ref written 2026-10-19 20:07:42 EDT, GitHub master equal (`9c0639c`)" (measured by claude-ai); skip this if either row already records that push. If round 66 is taken on `origin/master` when you start (`git fetch origin master`, then `git ls-tree origin/master records/rounds/`), stop and report. Push.

## HANDOFF's rules in this session

Every rule of `HANDOFF.md` section 6 applies. This table says how, where a cloud session differs from DSMain:

| rule | here |
|---|---|
| 1, 2, 3, 10, 15, 18, 19, 22, 28 | as written. Rule 19: no draft cites a textbook; credit each module's proof to its draft (`incoming/README.md`: Claude Opus 5.5 through the Anthropic Batch API; order CC-151's Claude Code session for 151), adapted by this session. Rule 3 bites only if a statement is narrowed (rule 1 below). Rule 22: every quote in round 66's fragment is checked by a script you write, with a planted misquote as its negative control. |
| 12 | Reviewers work in a scratch folder outside the repository (`$HOME/cm2-review-<n>`), start every Bash command with `. $HOME/cm2-env.sh && ` (it sets `PYTHONDONTWRITEBYTECODE=1`), and copy any repository script before importing it; after each review, `git status --porcelain` must be unchanged. |
| 14 | No existing module changes, so no type dump is needed; `ClassicalLean.lean` gains only import lines (check with `git diff`). |
| 17 | Each reviewer writes its report to `$EVD/reviews/<label>.md` and returns only that file's sha256; you run `hl.sh` on the file and compare the two values before you open it. A mismatch is reported. The reports are copied to `incoming/reviews/` at the end. |
| 20 | Scratch files and modules are elaborated by `el.sh` (it carries the four flags); linter results count only from `lake build`. |
| 23 | `ev.sh` and `hl.sh` (tested in Setup 3); records files written with Write or Edit are hashed with `hl.sh` before their commit. |
| 26 | Every review brief is built by a script from `HANDOFF.md`, saved with its sha256 before it is sent, and quotes verbatim rules 14, 17, 18, 19, 20, 22, 23, 26 and 31 (the rules that absorbed rules 16 to 25 as numbered on 2026-10-18), cut only with `[...]`. |
| 27 | Theorem-constant counts, total and per module (rule 5 below), come from `census.sh` on each final module file (HANDOFF section 1 records this census, its Method B, as equal to the README's Method A). The build's job count: 4178 plus the number of modules in the import closure of a scratch file importing only the five new modules (elaborated with `el.sh` once their text is final, each module read from `env.header.moduleNames`) that are not in the base closure saved in Setup 4; no root build runs between job 2 and End check 1, so the count is not seen before it is predicted. |
| 31 | Job 1 below: the statement review's verdict is in before any proof text enters a module; every new declaration, private helpers included, gets its module's cold review before its commit; a review fix that touches a proof line gets its delta check (re-elaborated with `el.sh` and the module rebuilt through `ev.sh`) before its commit. |
| 36 | Briefs and predictions carry a date beside every clock time, and each brief gives the dated end of its own run; `briefcheck.py` passes every brief before it is sent. Time windows (the witness limit of rule 4) are measured in epoch seconds, `date +%s` logged through `ev.sh` at the start and at the end. This session has no night window. |
| 37 | `el.sh` refuses a run while a name is not probed. Probe every Mathlib and library name the statements and proofs use with `#check @Name` lines in a probe file, run with `EL_PROBE=1`. A tactic name it refuses (a token that is not a constant) may be added to `$EVD/allowlist.txt` with a reason; `el.sh` logs the list's new sha256. |
| 38 | `rootrun.sh` for Setup 4's base closure (its first use, and the test with the real build) and for any other tool that imports `ClassicalLean`. The gates are not wrapped. |
| 39 | Stage by path. A commit message is written after its gates ran, says only what `evidence.log` shows, names in its first paragraph any linter or option switched off or on, and ends with the line `python3 -I $T/evcite.py $EVD/evidence.log` prints, generated last; a helper you must run after generating it takes a label starting `commit-`. End check 2 runs `citecheck.py`. |

## Rules of this order

1. **Statements as reviewed.** Each main theorem keeps its draft's statement, apart from the changes in the Goal list and moving it into the namespace. Never weaken, restate or add a hypothesis to make anything easier. A statement you find false is reported with its counterexample and narrowed, said plainly in its docstring, round 66 and the report; never dropped silently.
2. **Namespaces and imports.** Every declaration, private ones included, sits inside its module's namespace (`ClassicalLean.Analysis.PowerMethod` and so on; follow HANDOFF section 5 where it says more). The axiom gate checks only constants under `ClassicalLean`, so a declaration outside it escapes the gate. Imports are targeted: no `import Mathlib`.
3. **The vacuity gate as the repository has it.** A flag or an UNCHECKED verdict on a main theorem makes that item not closed (rule 8). On a helper: rewrite it, remove it if Mathlib or `simp` already does its job, or list it in `tools/vacuity_reviewed.txt` as HELPER with a one-line reason its module's reviewer checks. A VACUOUS-PENDING entry makes the item not closed.
4. **Witnesses.** Every main theorem with a hypothesis gets a witness in HANDOFF section 4's form, after its module's last line: `example := Full.name (x := …) h₁ h₂ …`, the theorem called by its full name, every chosen argument by name, optional `open … in` lines of their own and no other `open` than the module's top-level ones, the docstring "The hypotheses of `name` hold together: …", no `sorry`, `admit`, `native_decide`, `implemented_by`, `axiom` or `set_option`, one inline block with no helper declarations, and not degenerate as section 4 says (no empty, zero or single-point case, no Lean junk value, no boundary where a constant vanishes, families and matrices of size at least 2 unless the theorem fixes it, no function identically 0 past some point, no kernel or observation that does not depend on its parameter). Here that is six witnesses: 147 (start from `d147-r1-s2-witness.lean`), 150 twice (`pinv_unique`, `pinv_eq_leastSquares`), 151 (a concrete `k`; start from `d151-r9-s1-sat.lean`), 152, 153. Log `date +%s` through `ev.sh` when you start a witness; one still missing 1800 seconds later makes its item not closed.
5. **Records.** As `records/README.md` says. Round 66's fragment names every module path in full, gives each module's theorem-constant count from `census.sh` (rule 27), and gets its commit hashes in a follow-up edit once they exist, never predicted. Close your CLAIMS row and set the INDEX row's state at the end.
6. **Predict, then measure.** Commit `incoming/PREDICTIONS.md` once every module's text is final (after the reviews) and before End check 1, its predictions made by rule 27's methods. Until then do not run the axiom gate on the new modules, and read only the step results of CI runs (`gh run view --json jobs`), never their logs, which print the gate's count. The vacuity gate and the check scripts may run during the work, so a flagged helper is fixed before its module's review. PREDICTIONS.md gives: the build's job count; the axiom gate's count (3379 plus the census counts); check_sorry and check_records at 130 plus the number of modules landed; the vacuity gate's verdicts and reviewed-helper count; the rules drift check PASS. A miss is reported, never fixed by changing what was measured.
7. **Reviews.** Job 1's statement review, then one cold review per module once its text is final, each by a fresh subagent that has not seen your work, with a brief built as rule 26 says. The module review checks each statement against its plan row (FAITHFUL, GENERALIZED or WEAKER; WEAKER is a finding: restore the draft's statement or report it as a narrowing under rule 1), every hypothesis used, each witness against rule 4, every declaration in the namespace, imports targeted, every private helper's statement, and no main theorem whose conclusion is a recursive predicate that is `True` everywhere. A review with findings ends with a confirming pass on the fix only, by a fresh reviewer; a review with no findings needs none. At most two fix-and-confirm rounds; an item not clean after two is not closed.
8. **Not closed.** An item not closed is undone by a new commit (never a reset): its module file, its import line and its vacuity-list entries removed, and round 66, the CLAIMS row and the report saying which item and why. The other items go on.
9. **Push often.** Push after the records commit and after each item lands, so nothing is lost if the session stops. Each push starts a CI run; `.github/workflows/ci.yml` cancels an older run on the same branch when a newer one starts, which is fine.

## Job 1: the five statement files, and their review

Goal: each module's statements, final in form, reviewed before any proof enters a module.
1. Probe (rule 37): one probe file with `#check @Name` for every Mathlib and library name the five drafts and the two witness starts use, run with `EL_PROBE=1 $T/el.sh probes <file>`. A name that does not resolve is reported and its use rewritten.
2. For each item, a scratch statement file in `$EVD/stmt/` (outside the repository): the module's imports, namespace and docstrings, and every declaration of the draft (private helpers included) as it will land, where every theorem's and lemma's proof is `sorry` and every `def` keeps its full body (a definition's body is its statement: `pinv`, `huffmanLength` and their helpers are what make items 150 and 153 true to their rows); elaborate each with `el.sh` (rc 0, only `sorry` warnings). Hash them with `hl.sh`.
3. A mechanical check that moving into the namespace changed no meaning: for each main theorem, print its type with `set_option pp.fullNames true in #check @name` from the draft (a scratch copy with the line appended, through `el.sh`) and from the statement file, and compare the two by a script you write: only the theorem's own name and its namespace prefix may differ, besides the Goal list's changes. Log the script's result through `ev.sh`.
4. One statement review of all five files by one fresh subagent (rule 7's statement checks: each statement and definition against its plan row and the draft's, the Goal list's changes, namespaces, imports). Its verdict is in before job 2 starts.

Done means: five statement files hashed; the type comparison logged; a statement review saved and hash-checked (rule 17); findings fixed and confirmed (rule 7).

## Job 2: land each item, one commit per item

For each item in the table's order: the module file under `ClassicalLean/` with the reviewed statements and the draft's proofs (adapted only where the namespace, imports or Goal list's changes need it); its import line in `ClassicalLean.lean`; its witnesses (rule 4); `el.sh` on the module file (rc 0), then `lake build` of the module through `ev.sh` (0 errors, 0 warnings); the vacuity gate and check scripts; the module's cold review (rule 7) with any fix and confirming pass; the draft and its witness start removed from `incoming/`; one commit staged by path (rule 39), then `COMMIT <hash>` into the log, then push.

Undo: rule 8.

## End checks, in this order

1. With every draft removed from `incoming/` and the predictions committed, run on the clean tree, each through `ev.sh` beside its prediction: `lake build`; `lake env lean tools/AxiomGate.lean`; `python3 -I tools/check_sorry.py`; `lake env lean tools/VacuityGate.lean`; `python3 -I tools/check_records.py`; `python3 tools/compile_rules.py drift records/rules.toml HANDOFF.md`.
   If this leads to a fix (a helper rewritten or listed as HELPER) or a rule 8 undo: commit it, get a confirming pass by a fresh reviewer on that change only (for a HELPER entry, on its reason), run all of End check 1 again, and report both runs. The predictions stay as committed.
2. `$T/ev.sh citecheck "OK for every commit" python3 -I $T/citecheck.py $EVD/evidence.log $REPO 4d99afd`: every commit after the base. A `DIFF` line is reported, not fixed by rewriting history. The last commit (step 3) comes after this check; claude-ai checks it at the merge.
3. Copy `$EVD` into `incoming/evidence/`, leaving out any file over 1 MB (name each one left out, with its size and sha256, in the report). Write `incoming/REPORT.md`: in short; for each item its final statements, any narrowing, its witnesses, its review verdicts; predicted beside measured for every gate; the vacuity-list entries with reasons; the commits; End check 2's output; misses and anything not closed. Commit it with the records closed (rule 5), then push. This is the last commit.
4. Read the CI run for that last commit to the end: `gh run list -R datasphereai/classical-lean --branch cloud-math-2 --json databaseId,headSha,status,conclusion,url`, pick the run whose `headSha` equals `git rev-parse HEAD`, then `gh run view <id> -R datasphereai/classical-lean --json jobs`. Poll every few minutes; do not use `gh run watch`. The order is done only when that run is green.

## Done means

- `cloud-math-2` holds, after 4d99afd: the records commit; one commit per landed item (module, import line, witnesses, draft and witness start removed); the predictions commit; any fix or undo commits from End check 1; the report, evidence and closed records as the last commit. Nothing outside the scope changed; `master` untouched.
- Each of the five items proved with no `sorry` and no new axiom, as stated, or its narrowing said plainly, or reported not closed and undone by rule 8.
- Every main theorem with a hypothesis has a rule 4 witness; job 1's statement review and every module's review saved and hash-checked, each ending in a confirming pass where it had findings.
- The tools passed their 41 tests before first use (their output hashed into the evidence log); every commit message ends with its `Evidence:` line, and End check 2's output is in the report.
- The six End check 1 commands as predicted, or each miss reported; the CI run on the last commit green.

Then, as your final message: what was proved, any narrowing or item not closed, the gate results beside the predictions, the CI run's URL, the branch tip's hash, and `git ls-remote origin master` at the start and at the end (they must match). Plain words; the owner is still learning to read code.
