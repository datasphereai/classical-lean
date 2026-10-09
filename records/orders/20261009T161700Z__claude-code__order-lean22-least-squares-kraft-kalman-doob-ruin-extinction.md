<!-- Written on 2026-10-09 by Claude Code session_015uyBADuYuNNAwLUWbUvxWF on DSMain, from the plan /opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md (sha256 5c2381ba371a3b810dbc39302c724ff7d2279fca9d9870d354f269ae6f048fc0, checked by sha256sum before this file was written; equal to the hash the order expects), as Dustin ordered in chat on 2026-10-09. Batch 6 of the plan, the order and a correction sent during the work are copied verbatim below. Written before any module was changed, per records/README.md rule 2. -->

# LEAN-22: recursive least squares, the converse of Kraft's inequality, the scalar Kalman filter's error variance, Doob's L² inequality, gambler's ruin, and Galton–Watson extinction

## Goal

Batch 6 of MATH-PLAN-library (items 40 to 45): six named results, proved in the library with no sorry and no axiom. The item numbers are the plan's: item 42 is the scalar Kalman filter (the Riccati iteration) and item 45 is Galton–Watson extinction.

Re-checked against Mathlib v4.34.0 (`5ed2965256`) before this file was written, as the order asks (`grep -rniE` over Mathlib; patterns, counts and the first hits in the session's evidence files `~/lean/lean22-checks/search.out` and `search2.out`): none of the six items is in Mathlib, so none is dropped. Hits that exist: the Woodbury identity and the matrix determinant lemma (used by item 40); `IsPrefixFree` and Kraft's inequality in its forward direction only (`InformationTheory/Coding/Kraft.lean`; no converse); Doob's maximal inequality `maximal_ineq` (its docstring says the Lp inequality "will be proved in an upcoming PR"; it is not in v4.34.0); hitting times (`hittingBtwn`, `hittingAfter`) and optional stopping for bounded stopping times, but no random walk, gambler or ruin; "watson" only as an author's name, no branching process or extinction; no Kalman or Riccati. Routes that differ from the rows: item 40 proves the estimate update directly from the normal equations and uses Mathlib's Woodbury identity for the update of `(Xᵀ X)⁻¹`; item 43 does not use the layer-cake formula: it proves a path-by-path inequality and takes means, with no square-integrability hypothesis.

## Scope

### Batch 6 — order LEAN-22

| # | area | the result | Lean names | module | rests on | cost |
|---|---|---|---|---|---|---|
| 40 | 10, bridge | Recursive least squares: one more row updates the estimate by `β + P x (y − xᵀ β)/(1 + xᵀ P x)`. | `leastSquares_append_row` | ClassicalLean.Statistics.GaussMarkov | Mathlib Woodbury (NonsingularInverse.lean:601); library `leastSquares` | M |
| 41 | 5 | Converse of Kraft's inequality: lengths with `∑ D^(−ℓ) ≤ 1` belong to a prefix-free code; so some code has mean length below `H / log D + 1`. | `exists_isPrefixFree_length_eq` | ClassicalLean.InformationTheory.SourceCoding | Mathlib `IsPrefixFree`; item 8 | M–L |
| 42 | 9 | The scalar Kalman filter's error variance converges to the positive root of its Riccati equation. | `tendsto_riccatiStep` | new ClassicalLean.Probability.KalmanVariance | Mathlib monotone limits | M |
| 43 | 8 | Doob's `L²` inequality: `E[max_{k ≤ n} M k²] ≤ 4 E[M n²]`. | `integral_sup_sq_le` | ClassicalLean.Probability.MaximalInequality | item 23; Mathlib `maximal_ineq`, layer cake | M–L |
| 44 | 8 | Gambler's ruin for the fair `±1` walk: `P(a before −b) = b/(a + b)`, mean duration `a b`. | `measureReal_hit_eq` | new ClassicalLean.Probability.GamblersRuin | Mathlib optional stopping, `hittingBtwn`; library FairGame | L |
| 45 | 8 | Galton–Watson: the iterates `fⁿ(0)` of the offspring generating function rise to its least fixed point in `[0, 1]`, which is `1` exactly when the mean is at most `1` (one child for sure excepted). | `tendsto_iterate_zero` | new ClassicalLean.Probability.Extinction | Mathlib `tsum` of nonnegative series, convexity | M–L |

Changed or added: the six results above; the module docstring of `ClassicalLean.InformationTheory.Channel` (section "Relation to Mathlib") and `HANDOFF.md` §3, which still call the bridge to Mathlib's `klDiv` future work although item 39 (order LEAN-21) proved it; `ClassicalLean.lean` (three import lines).

Not in scope: batches 7 to 10 of the plan; offering anything to Mathlib; anything under ~/trading; any edit under ~/lean/recheck (its script is only run, as gate 7); any push.

## Done-means

Dustin's order, verbatim:

LEAN-22 is batch 6 of the classical-lean library plan: items 40 to 45. It continues LEAN-21 (batch 5), which Dustin pushed; origin and github master were both 5c25955 at 15:03 UTC today.

Setup
1. Run `sha256sum` on /opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md. I expect 5c2381ba371a3b810dbc39302c724ff7d2279fca9d9870d354f269ae6f048fc0. If it differs, say so in your report. Batch 6 is unchanged unless the plan says otherwise.
2. Read, in the same folder: the plan (section 4 batch 6, section 5 searches, section 9), LEAN-21-report.md, MATH-PLAN-library-HANDOFF.md, and the "Known traps" section of LEAN-16-order.md.
3. `git fetch origin`. origin/master must be 5c25955. If it is not, stop and tell me. Otherwise branch `paper-crypto-17` from it.

The work: items 40 to 45
Follow the LEAN-19/LEAN-21 method:
- Re-check each item against Mathlib (v4.34.0) by search before building. Drop or reduce any item that is already there, and say so.
- Records first, in one commit: the order copy (new modules in dotted form only), the INDEX row, the CLAIMS row, and the next round fragment. check_records must still pass on the new module paths.
- Write the statements with `sorry` first and elaborate them.
- Write a dropped-hypothesis table, exact arithmetic where you can. Items 42 and 45 especially need their edge cases checked, for example the Galton–Watson "one child for sure" case and when the Riccati iteration really converges.
- Build one module at a time, with one cold review per module by a fresh subagent that has a read list and a limit of about 40 tool calls.
- Suggested order: 40, 42, 41, 43, 45, 44.
- Item 44 is the largest. If a module can't be closed, stop at a clean point and say exactly what was not reached. A tool-call limit is never a reason to cut work short, because Dustin will press continue.

Rules for this order
- Citations: for a paper you did not read, give author, title and year only, and say nothing about what it contains.
- Two follow-ups left over from LEAN-21: the InformationTheory/Channel.lean docstring ("Relation to Mathlib") and HANDOFF.md §3 still call the klDiv bridge future work, but item 39 proved it. Fix both and name them in the claimed files.
- Keep the constant count honest. Today it is 2516 constants and 102 modules. Predict the new count before any gate runs, by a method other than the gate's own counting rule: compile scratch copies of the new proofs and count what they add, or reconcile a grep of the new theorem and lemma lines against the gate. LEAN-21 missed by 19 because tactic helpers (`_simp_`, `eq_N`, `congr_simp`, `_proof_`) were under-modelled, so include them in your model. Reconcile any miss name by name.
- Run all six gates, then gate 7 as in LEAN-21: ~/lean/recheck/run-recheck.sh with your last commit and this repo's path (take the usage from the script's own header). Nothing may be edited under ~/lean/recheck.
- Nothing under ~/trading. No push. No sudo.

Report
Write inbox/threads/staging/LEAN-22-report.md through ds_write_staging and compare post_sha256 with your own hash. Include: each item's result in one sentence, predicted beside measured, the hypothesis table, the commits, what was not reached, and the push command as one line, not run:
cd ~/lean/classical-lean-paper-crypto && git push origin paper-crypto-17:master && git push github paper-crypto-17:master
Then stop.

Dustin is still learning to read code but reads your replies carefully. Use plain words, define a technical term the first time you use it, and ask any decision in one line with your recommended answer first.

use taskcreate

A correction sent during the work, before this file was written, verbatim:

Correction from Dustin's helper: in my prompt I listed items 42 and 45 in the wrong order. Per the plan, item 42 is the scalar Kalman filter (Riccati equation, module KalmanVariance) and item 45 is Galton–Watson extinction (module Extinction). The "one child for sure" edge case belongs to item 45; the Riccati convergence conditions belong to item 42. Check your task list, records rows and commit messages against the plan's own numbers, fix any swap, and carry on.
