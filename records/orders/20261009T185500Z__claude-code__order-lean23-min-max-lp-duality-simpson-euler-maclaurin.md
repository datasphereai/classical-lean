<!-- Written on 2026-10-09 by Claude Code session_01Sygvo6Yn77Tbb7i6N4k4a1 on DSMain, from the plan /opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md (sha256 5c2381ba371a3b810dbc39302c724ff7d2279fca9d9870d354f269ae6f048fc0, checked by sha256sum before this file was written; equal to the hash the order expects), as Dustin ordered in chat on 2026-10-09. Batch 7 of the plan and the order are copied verbatim below. Written before any module was changed, per records/README.md rule 2. -->

# LEAN-23: Courant–Fischer min–max and Weyl's inequality, strong duality for linear programs, Simpson's rule error bound, and Euler–Maclaurin to first order

## Goal

Batch 7 of MATH-PLAN-library (items 46 to 49), in one order (Dustin ruled no split): four named results, proved in the library with no sorry and no axiom. The item numbers are the plan's.

Re-checked against Mathlib v4.34.0 (`5ed2965256`) before this file was written, as the order asks (`grep -rniE` over Mathlib; patterns, counts and first hits in the session's evidence file `~/lean/lean23-checks/search.out`): none of the four items is in Mathlib, so none is dropped or reduced. What exists: `eigenvalues_antitone` and `hasEigenvalue_iSup_of_finiteDimensional` / `hasEigenvalue_iInf_of_finiteDimensional` (the top and bottom eigenvalue as a supremum and infimum only; "courant" and "fischer" have no hit, "minimax" hits are Bayes and minimax risk; "weyl" hits are Weyl groups); for item 47 the TODO in the cone file (lines 35 to 37) and Farkas' lemma only for a closed cone (`ProperCone.hyperplane_separation_of_notMem` uses the closure of the image), with no proof that a finitely generated cone is closed; for item 48 "simpson" is only an author's name, and the trapezoidal rule's error bound is the pattern; for item 49 no "Euler–Maclaurin", `periodizedBernoulli` with no summation formula, and Abel's summation formula (`sum_mul_eq_sub_sub_integral_mul`, for natural-number endpoints), which is related but not used. Routes that differ from the rows: item 47 separates by the Hahn–Banach theorem on `ι → ℝ` instead of `ProperCone.hyperplane_separation`, after proving that the image of the nonnegative orthant under a linear map is closed; item 49 is proved directly, one integration by parts per unit interval, so it holds for negative integer endpoints too.

## Scope

### Batch 7 — order LEAN-23 (large; may split)

| # | area | the result | Lean names | module | rests on | cost |
|---|---|---|---|---|---|---|
| 46 | 1 | Courant–Fischer min–max, and Weyl's eigenvalue inequality. | `eigenvalues_eq_iSup_iInf`, `eigenvalues_add_le` | new ClassicalLean.Algebra.MinMax | Mathlib `eigenvalues_antitone` (InnerProductSpace/Spectrum.lean:312), Rayleigh | L |
| 47 | 7 | Strong duality for linear programs (Mathlib's TODO, Cone/Basic.lean:35–37). | `lp_strong_duality` | new ClassicalLean.Analysis.LinearProgram | Mathlib `ProperCone.hyperplane_separation` (Cone/Dual.lean:116) | L |
| 48 | 6 | Simpson's rule error `≤ (b − a) h⁴ max |f⁗| / 180`. | `simpson_error_le` | new ClassicalLean.Analysis.Simpson | Mathlib Taylor; the TrapezoidalRule pattern | L |
| 49 | 3 | Euler–Maclaurin, first order: `∑ f k = ∫ f + (f a + f b)/2 + ∫ B̃₁ f'`. | `sum_eq_integral_add` | new ClassicalLean.Analysis.EulerMaclaurin | Mathlib `periodizedBernoulli` (ZetaValues.lean:274), integration by parts | M–L |

Changed or added: the four new modules above; `ClassicalLean.lean` (four import lines).

Not in scope: batches 8 to 10 of the plan; offering anything to Mathlib; anything under ~/trading; any edit under ~/lean/recheck (its script is only run, as gate 7); any push.

## Done-means

Dustin's order, verbatim:

LEAN-23 is batch 7 of the classical-lean library plan: items 46 to 49, in one order (Dustin ruled no split). It continues LEAN-22 (batch 6), which Dustin pushed; origin and github master should both be 607f185.

The item numbers are the plan's. Use them in every commit message, record row and report line:
- 46: Courant–Fischer min–max and Weyl's eigenvalue inequality (new module ClassicalLean.Algebra.MinMax)
- 47: strong duality for linear programs (new module ClassicalLean.Analysis.LinearProgram)
- 48: Simpson's rule error bound (new module ClassicalLean.Analysis.Simpson)
- 49: Euler–Maclaurin, first order (new module ClassicalLean.Analysis.EulerMaclaurin)

Setup
1. Run `sha256sum` on /opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md. I expect 5c2381ba371a3b810dbc39302c724ff7d2279fca9d9870d354f269ae6f048fc0 (measured a minute ago). If it differs, say so in your report. Batch 7 is unchanged unless the plan says otherwise.
2. Read, in the same folder: the plan (section 4 batch 7, section 5 searches, section 9), LEAN-22-report.md, MATH-PLAN-library-HANDOFF.md, and the "Known traps" section of LEAN-16-order.md.
3. `git fetch origin`. origin/master must be 607f185 and `git ls-remote github master` must agree. If not, stop and tell me. Otherwise branch `paper-crypto-18` from it.

The work
Follow the LEAN-19/LEAN-22 method:
- Re-check each item against Mathlib (v4.34.0) by search before building. Mathlib's TODOs for item 47 are at Cone/Basic.lean:35 to 37, and its eigenvalue lemma for item 46 is `eigenvalues_antitone`. If an item is already there, drop or reduce it and say so.
- Records first, in one commit: the order copy (new modules in dotted form only), the INDEX row, the CLAIMS row, and the next round fragment. check_records must still pass on the four new module paths.
- Write the statements with `sorry` first and elaborate them. Those sorries are scratch only and must be gone from the library before any commit that builds it.
- Write a dropped-hypothesis table with exact arithmetic where you can, and mind Lean's junk values (`x / 0 = 0`, eigenvalue ordering, empty infima and suprema). Item 47 needs care with the statement shape: say exactly what feasible, bounded and attained mean, and check each hypothesis by dropping it.
- Build one module at a time, with one cold review per module by a fresh subagent that has a read list and a limit of about 40 tool calls.
- Suggested order: 48, 49, 46, 47, so the two largest come last. If a module can't be closed, stop at a clean point and say exactly what was not reached. A tool-call limit is never a reason to cut work short, because Dustin will press continue.

Rules for this order
- Citations: for a paper or book you did not read, give author, title and year only, and say nothing about what it contains.
- Keep the constant count honest. Today it is 2640 constants and 105 modules. Predict the new count before any gate runs. Method B (compile scratch copies of the changed and new modules and count what they add) is the primary method, because it hit in LEAN-22. Method A (a model from the source lines) missed by 19 and then by 15 on helpers, so include `field_simp` and `omega` helpers, `eq_def` and `match_1` lemmas, and `_proof_` lemmas inside definitions in it. Reconcile any miss name by name.
- Predict the build job count as 4076 plus one per new module, and say why if it differs.
- Run all six gates, then gate 7 as in LEAN-22: ~/lean/recheck/run-recheck.sh with your last commit and this repo's path (take the usage from the script's own header). Nothing may be edited under ~/lean/recheck.
- Nothing under ~/trading. No push. No sudo.

Report
Write inbox/threads/staging/LEAN-23-report.md through ds_write_staging and compare post_sha256 with your own hash. Include: each item's result in one sentence, predicted beside measured, the hypothesis table, the commits, what was not reached, and the push command as one line, not run:
cd ~/lean/classical-lean-paper-crypto && git push origin paper-crypto-18:master && git push github paper-crypto-18:master
Then stop.

Dustin is still learning to read code but reads your replies carefully. Use plain words, define a technical term the first time you use it, and ask any decision in one line with your recommended answer first.

 and use taskcreate once the plan is accepted. Thank you Claude <3

Sent after the plan was approved, verbatim:

don't stop until you've cloed them all. I know you can do it.
