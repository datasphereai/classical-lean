<!-- The order's text, as given in the prompt of Claude Code cloud session session_01HV9mMLe9qSe13nN9hMyEBJ (https://claude.ai/code/session_01HV9mMLe9qSe13nN9hMyEBJ), copied on 2026-10-15 (UTC) by that session before any Lean file changed, per records/README.md rule 2. Its file name gives claude-ai as the source, as the order's own Setup step 4 names it. -->

# Order CLOUD-MATH-1: five new modules from five proved drafts

## Goal

Put five proved results into the library as five new modules, each under the library's gates, with witnesses, reviews and records, on branch `cloud-math-1`. The proofs already exist in `incoming/` (read `incoming/README.md`). The work is to land them the way this library lands work: right names and namespaces, targeted imports, docstrings, witnesses, a fresh review per module, records. Not to re-prove them.

| item | plan statement (the library's second plan, below its cut) | main theorems | new module | draft |
|---|---|---|---|---|
| 131 | Han's inequality: for a joint law of `n` coordinates, `(n − 1) H(X) ≤ ∑ᵢ H(X without coordinate i)`. | `mul_shannonEntropy_le_sum` | `ClassicalLean.InformationTheory.HanInequality` | d131-r1-s1 |
| 135 | Frank–Wolfe on the simplex: for convex `f` with `L`-Lipschitz gradient, step `2/(k + 2)` gives `f(x_k) − f* ≤ 4L/(k + 2)` (the simplex has squared diameter 2). | `sub_le_of_frankWolfe`, and `fw_general` made public | `ClassicalLean.Analysis.FrankWolfe` | d135-r1-s2 |
| 136 | One-period asset pricing, finite form: with payoff matrix `D` (states by assets) and prices `π`, no portfolio costs at most nothing, never pays less than nothing, and either costs less than nothing or sometimes pays more, exactly when there are strictly positive state prices `ψ` with `Dᵀ ψ = π`. | `exists_pos_statePrices_iff` | `ClassicalLean.Analysis.StatePrices` | d136-r3-s2 |
| 137 | Pólya's urn: the share of red balls is a martingale and converges almost surely. | `martingale_urnShare`, `ae_tendsto_urnShare`, and a new theorem that the limit lies in `[0, 1]` almost surely | `ClassicalLean.Probability.PolyaUrn` | d137-r2-s1 |
| 139 | The reflection principle for the fair `±1` walk: `P(max_{k ≤ n} S_k ≥ a) = P(S_n ≥ a) + P(S_n > a)` for `a ≥ 1`. | `measureReal_max_ge_eq` | `ClassicalLean.Probability.Reflection` | d139-r2-s1 |

Every name in the "main theorems" column is a main theorem for the rules below (witness, vacuity, review). For 139, also replace `import Mathlib` by the Mathlib files it needs.

## This order and the repository's own documents

Where this order and `HANDOFF.md` differ, this order wins. In particular: you push `cloud-math-1` to GitHub yourself (HANDOFF §6's "never push to GitHub" is a rule for the home server, not for this session); the gates are the five in End checks; do not run gate 7, the bridge search or the report tool, which run on the home server at the merge.

## Branch rules (hard)

These override any branch this session was assigned; do not push an assigned `claude/*` branch.
- Work only on `cloud-math-1`. First confirm `origin/cloud-math-1` is `e2fac6da5992ea3e7d3f55ba31420e44039d7b42` and the five drafts' sha256s match `incoming/README.md`. If not, stop and report.
- Push only with `git push origin cloud-math-1`. Never push `master` or `main`, never force-push, never reset a pushed commit, open no pull request, merge nothing on GitHub. Every undo is a new commit.

## Scope

You may: add the five module files under `ClassicalLean/` (paths from the module names); add their five import lines at the end of the import block of `ClassicalLean.lean` (it lists imports in landing order); add entries to `tools/vacuity_reviewed.txt` only as rule 3 allows; write `records/` as rule 5 says; in `incoming/`, remove each draft when its item lands or is not closed, and remove `README.md` when no draft remains, and add `PREDICTIONS.md`, `reviews/` and `REPORT.md`.
You may not change any existing module, any other file under `tools/`, `HANDOFF.md`, `ROADMAP.md`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` or `.github/`. Needing to is a stop: report it.

## Read first (all in the repository)

`records/README.md`; `HANDOFF.md` sections 0, 4 (the gates, and "Satisfiability witnesses"), 5 (naming) and 6; `tools/AxiomGate.lean` (how it counts, private declarations included); the copies of orders LEAN-28 and VACUITY-3 under `records/orders/` and round 58's fragment under `records/rounds/`, as the pattern for your records; one existing module from each target folder, for the licence header, the module docstring and the namespace style.

## Setup

1. Check the network first: `curl -sSI https://cache.mathlib.org/ | head -3`. A connection error, or a 403 from the session's proxy, is a stop: report the exact output and do not build Mathlib from source. Any answer from cache.mathlib.org itself is a pass. Note `git ls-remote origin master` (you report it again at the end; the two must match).
2. Install the toolchain from `lean-toolchain` (elan, from GitHub), run `lake exe cache get`, then `lake build` in the background with its output in a log file (a first build can pass the 10-minute limit on one command); read the log until it ends. A refused download or a failed dependency clone is a stop: report it. If the VM kills the build for memory, retry once as `LEAN_NUM_THREADS=2 lake build`; if it is killed again, stop and report.
3. Starting counts: the branch differs from commit 20303cd only in `.github/` and `incoming/`, so 20303cd's counts hold at the start: build 4170 jobs, axiom gate 3228 theorem constants, 122 files under `ClassicalLean/`. Confirm the first two from your setup build and one axiom gate run before any new module exists.
4. Records first, in one commit with no `.lean` file: this order's text as `records/orders/<UTC>__claude-ai__order-cloudmath1-han-frank-wolfe-state-prices-polya-reflection.md`; its row in `records/orders/INDEX.md` (rows start `| CLOUD-MATH-1 |`); a row at the bottom of `records/CLAIMS.md` naming this cloud session and the five module paths; and round 60's fragment, `records/rounds/<UTC>__round-60-han-frank-wolfe-state-prices-polya-reflection.md`, naming the five module files by full path. Round 59 is another session's and is not on this branch; keep the number 60. Push.

## Rules

1. **Statements as reviewed.** Each main theorem keeps its draft's statement, apart from the changes in the table and moving it into the namespace. Never weaken, restate or add a hypothesis to make anything easier. A statement you find false is reported with its counterexample and narrowed, said plainly in its docstring, round 60 and the report; never dropped silently.
2. **Namespaces and imports.** Every declaration, private ones included, sits inside its module's namespace (`ClassicalLean.InformationTheory.HanInequality` and so on; follow HANDOFF §5 where it says more). The axiom gate checks only constants under `ClassicalLean`, so a declaration outside it escapes the gate. Imports are targeted: no `import Mathlib`. Each main theorem's docstring names its item ("Item 131 of MATH-PLAN-library-2"); each module docstring lists its results.
3. **The vacuity gate as the repository has it.** A flag or an UNCHECKED verdict on a main theorem makes that item not closed (rule 8). On a helper: rewrite it, remove it if Mathlib or `simp` already does its job, or list it in `tools/vacuity_reviewed.txt` as HELPER with a one-line reason the module's reviewer checks. A VACUOUS-PENDING entry makes the item not closed.
4. **Witnesses.** Every main theorem with a hypothesis gets a witness in HANDOFF §4's form (an `example` after the module's last line that applies the theorem itself, every chosen argument by name, an optional `open … in` line of its own, the docstring "The hypotheses of `name` hold together: …", no `sorry`, `admit`, `native_decide`, `implemented_by`, `axiom` or `set_option`, one inline block with no helper declarations). Not degenerate, as §4 says, and also: no hypothesis met only because a function is identically 0 past some point, and no kernel or observation that does not depend on the parameter it is about. Note the time with `date` when you start a witness; one still missing 30 minutes later makes the item not closed.
5. **Records.** As `records/README.md` says. Round 60's fragment names every module path in full, gives each module's theorem-constant count measured as the README says, and gets its commit hashes in a follow-up edit once they exist, never predicted. Close your CLAIMS row and set the INDEX row's state at the end.
6. **Predict, then measure.** Commit `incoming/PREDICTIONS.md` once every module's text is final (after the reviews) and before End check 1. Until then, do not run the axiom gate on the new modules, and read only the step results of CI runs (`gh run view --json jobs`), never their logs, which print the gate's count. The vacuity gate and the check scripts may run during the work, so a flagged helper is fixed before its module's review. It gives: the build's job count (4170 plus your count of what the five modules add, Mathlib files new to the closure included); the axiom gate's count (3228 plus your blind count of the new theorem constants, counted as `tools/AxiomGate.lean` counts); check_sorry and check_records at 122 plus the number of modules landed; the vacuity gate's verdicts. A miss is reported, never fixed by changing what was measured.
7. **Reviews.** Each module, once its statements are final, gets a cold review by a fresh subagent that has not seen your work. It checks the statement against its plan row (FAITHFUL, GENERALIZED or WEAKER; WEAKER is a finding: restore the draft's statement or report it as a narrowing under rule 1), every hypothesis used, each witness against rule 4, every declaration in the namespace, imports targeted, and no main theorem whose conclusion is a recursive predicate that is `True` everywhere. A review with findings ends with a confirming pass on the fix only, by a fresh reviewer if the fix came from a reviewer; a review with no findings needs none. At most two fix-and-confirm rounds; an item not clean after two is not closed. Save each reviewer's output in `incoming/reviews/`.
8. **Not closed.** An item not closed is undone by a new commit (never a reset): its module file, its import line and its vacuity-list entries removed, and round 60, the CLAIMS row and the report saying which item and why. The other items go on.
9. **Push often.** Push after the records commit and after each item lands, so nothing is lost if the session stops. Each push starts a CI run; `.github/workflows/ci.yml` cancels an older run on the same branch when a newer push arrives, which is fine.

## End checks, in this order

1. With every draft removed from `incoming/` and the predictions committed, run on the clean tree: `lake build`; `lake env lean tools/AxiomGate.lean`; `python3 -I tools/check_sorry.py`; `lake env lean tools/VacuityGate.lean`; `python3 -I tools/check_records.py`. Each beside its prediction.
   If this leads to a fix (a helper rewritten or listed as HELPER) or a rule 8 undo: commit it, get a confirming pass by a fresh reviewer on that change only (for a HELPER entry, on its reason), run all of End check 1 again, and report both runs. The predictions stay as committed.
2. Write `incoming/REPORT.md`: in short; for each item its final statements, any narrowing, its witnesses, its review verdicts; predicted beside measured for every gate; the vacuity-list entries with reasons; the commits; misses and anything not closed. Commit it with the records closed (rule 5), then push. This is the last commit.
3. Read the CI run for that last commit to the end: `gh run list -R datasphereai/classical-lean --branch cloud-math-1 --json databaseId,headSha,status,conclusion,url`, pick the run whose `headSha` equals `git rev-parse HEAD`, then `gh run view <id> -R datasphereai/classical-lean --json jobs`. Poll every few minutes; do not use `gh run watch`. The order is done only when that run is green.

## Done means

- `cloud-math-1` holds, after e2fac6d: the records commit; the landed modules, their import lines and the draft removals; the predictions commit; any fix or undo commits from End check 1; the report and closed records as the last commit. Nothing outside the scope changed; `master` untouched.
- Each of the five items proved with no `sorry` and no new axiom, as stated, or its narrowing said plainly, or reported not closed and undone by rule 8.
- Every main theorem with a hypothesis has a rule 4 witness; every module had a cold review, ending in a confirming pass where it had findings.
- The five gates as predicted, or each miss reported; the CI run on the last commit green.

Then, as your final message: what was proved, any narrowing or item not closed, the gate results beside the predictions, the CI run's URL, the branch tip's hash, and `git ls-remote origin master` at the start and at the end (they must match). Plain words; the owner is still learning to read code.
