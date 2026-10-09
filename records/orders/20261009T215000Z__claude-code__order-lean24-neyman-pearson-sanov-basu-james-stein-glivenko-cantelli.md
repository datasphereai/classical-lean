<!-- Written on 2026-10-09 by Claude Code session_01QpAr2Yyk1XLSrhVcfEz1tw on DSMain, from the plan /opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md (sha256 5c2381ba371a3b810dbc39302c724ff7d2279fca9d9870d354f269ae6f048fc0, checked by sha256sum before this file was written; equal to the hash the order expects), as Dustin ordered in chat on 2026-10-09. Batch 8 of the plan and the order are copied verbatim below. Written before any module was changed, per records/README.md rule 2. -->

# LEAN-24: Neyman–Pearson, Karlin–Rubin, Sanov for a finite alphabet, Basu, James–Stein and Glivenko–Cantelli

## Goal

Batch 8 of MATH-PLAN-library (items 55 to 60), in one order (no split): six named results of classical testing and estimation, proved in the library with no sorry and no axiom. The item numbers are the plan's.

Re-checked against Mathlib v4.34.0 (`5ed2965256`) before this file was written, as the order asks (`grep -rliE` and `grep -rniE` over Mathlib; patterns, counts and first hits in the session's evidence files `~/lean/lean24-checks/search.out` and `search2.out`): none of the six items is in Mathlib, so none is dropped or reduced. "neyman|pearson" 0 files; "most powerful|likelihood ratio test|uniformly most" 0; "karlin|rubin|monotone likelihood" 1 file, Rubin's theorem in group actions; "basu|ancillary|complete statistic|boundedly complete" 1 file, the word "ancillary" in a ring-theory docstring; "james.?stein|stein.?s lemma|gaussian integration by parts|shrinkage" 1 file, Eisenstein's lemma; "glivenko" 0 files, and every "cantelli" hit is Borel–Cantelli; "empirical" 1 line, unrelated; "sanov|method of types" 0 apart from the phrase "type class". What exists and is used: `ProbabilityTheory.cdf` (Probability/CDF.lean), the strong law `ProbabilityTheory.strong_law_ae`, `gaussianReal` and its density (Probability/Distributions/Gaussian/Real.lean), `stdGaussian` and `multivariateGaussian` (Gaussian/Multivariate.lean, not used: the order asks for the normal law in dimension `d` built from `gaussianReal`), `Measure.pi`, and the library's `relEntropy`, `vecMeasure`, `IsSufficient` (item 50) and `IsComplete` (item 54).

## Scope

### Batch 8 — classical testing and estimation (added 2026-10-09 by claude-ai, Dustin's yes; may split)

Searched 2026-10-09 on DSMain, Mathlib v4.34.0: "Neyman.Pearson", "Karlin", "Sanov", "Basu", "James.Stein", "Glivenko" each 0 files. Re-check each by search before building, as for every batch.

| # | area | the result | Lean names | module | rests on | cost |
|---|---|---|---|---|---|---|
| 55 | 2 | Neyman–Pearson lemma: for two simple hypotheses with densities, the test that rejects when the likelihood ratio is above a threshold has the largest power among all tests of the same size or less. The theorem underneath CS-2's style of test; likelihood ratios are e-values. | `power_le_of_likelihoodRatioTest` | new ClassicalLean.Statistics.NeymanPearson | Mathlib `rnDeriv`, `integral_mono`; library LikelihoodScore | M |
| 56 | 2 | Karlin–Rubin: under a monotone likelihood ratio in a statistic `S`, the test that rejects for large `S` is uniformly most powerful for a one-sided question ("is the parameter above θ₀?"). | `isUniformlyMostPowerful_of_monotoneLikelihoodRatio` | ClassicalLean.Statistics.NeymanPearson | item 55 | M |
| 57 | 5, bridge | Sanov's theorem, finite alphabet (method of types): the chance that `n` independent draws have an empirical distribution in a set `E` is at most `(n + 1)^K · exp (−n · min over E of D(q ‖ p))`. Links the library's relative entropy to how long evidence takes. | `measureReal_empirical_mem_le` | new ClassicalLean.InformationTheory.MethodOfTypes | library `relEntropy`, Entropy; Mathlib `Finset` counting, multinomial | M–L |
| 58 | 2 | Basu's theorem: a complete sufficient statistic is independent of every ancillary statistic (one whose distribution does not depend on θ). | `indepFun_of_isComplete_of_ancillary` | ClassicalLean.Statistics.Sufficiency | items 50 and 54; Mathlib `IndepFun`, `condExp` | M |
| 59 | 2 | James–Stein: for `X` normal with mean `θ` in dimension `d ≥ 3` and identity covariance, `(1 − (d − 2)/‖X‖²) X` has smaller expected squared error than `X` for every `θ`. Needs Stein's lemma (Gaussian integration by parts) first. | `integral_norm_sq_jamesStein_lt` | new ClassicalLean.Statistics.JamesStein | Mathlib `gaussianReal`, `integral_mul_deriv_eq_deriv_mul` | L |
| 60 | 2, 8 | Glivenko–Cantelli: the empirical distribution function of independent identically distributed draws converges to the true one uniformly, almost surely. | `tendsto_sup_abs_empiricalCDF_sub` | new ClassicalLean.Probability.GlivenkoCantelli | Mathlib strong law (`strong_law_ae`), `cdf` | L |

Changed or added: four new modules, ClassicalLean.Statistics.NeymanPearson (items 55 and 56), ClassicalLean.InformationTheory.MethodOfTypes (item 57), ClassicalLean.Statistics.JamesStein (item 59) and ClassicalLean.Probability.GlivenkoCantelli (item 60); the existing module ClassicalLean.Statistics.Sufficiency (item 58); `ClassicalLean.lean` (four import lines).

Not in scope: batches 9 and 10 of the plan; offering anything to Mathlib; anything under ~/trading; any edit under ~/lean/recheck (its script is only run, as gate 7); any push; any sudo.

## Done-means

Dustin's order, verbatim:

LEAN-24 is batch 8 of the classical-lean library plan: items 55 to 60, classical testing and estimation, in one order (no split). It continues LEAN-23 (batch 7), which Dustin pushed; origin and github master should both be 4a1accf.

The item numbers are the plan's. Use them in every commit message, record row and report line:
- 55: Neyman–Pearson lemma (new module ClassicalLean.Statistics.NeymanPearson)
- 56: Karlin–Rubin (same module, rests on 55)
- 57: Sanov's theorem for a finite alphabet (new module ClassicalLean.InformationTheory.MethodOfTypes)
- 58: Basu's theorem (module ClassicalLean.Statistics.Sufficiency; rests on items 50, 54 and 61, already in the library)
- 59: James–Stein (new module ClassicalLean.Statistics.JamesStein; Stein's lemma first)
- 60: Glivenko–Cantelli (new module ClassicalLean.Probability.GlivenkoCantelli)

Setup
1. Run `sha256sum` on /opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md. I expect 5c2381ba371a3b810dbc39302c724ff7d2279fca9d9870d354f269ae6f048fc0 (measured a minute ago; the plan has 71 items in 10 batches). If it differs, say so in your report.
2. Read, in the same folder: the plan (section 4 batch 8, section 5 searches, section 9), LEAN-23-report.md, MATH-PLAN-library-HANDOFF.md, and the "Known traps" section of LEAN-16-order.md.
3. `git fetch origin`. origin/master must be 4a1accf and `git ls-remote github master` must agree. If not, stop and tell me. Otherwise branch `paper-crypto-19` from it.

The work
Follow the LEAN-19/LEAN-23 method:
- Re-check each item against Mathlib (v4.34.0) by search before building. If an item is already there, drop or reduce it and say so.
- Records first, in one commit: the order copy (new modules in dotted form only), the INDEX row, the CLAIMS row, and the next round fragment. check_records must still pass on the four new module paths.
- Write the statements with `sorry` first and elaborate them. Those sorries are scratch only and must be gone from the library before any commit that builds it.
- State each theorem exactly. For item 55 say whether tests are randomized (values in [0, 1]) so that a size can be hit exactly; for item 57 say what the alphabet size K, the set E and the case p i = 0 do; for item 58 define "ancillary" and "complete" as the library's items 50 and 54 do; for item 59 say how "normal with identity covariance in dimension d" is built from Mathlib's `gaussianReal`, and show the d ≥ 3 hypothesis is needed; for item 60 say what the supremum is over.
- Write a dropped-hypothesis table with exact arithmetic where you can, and mind Lean's junk values (`x / 0 = 0`, integral of a non-integrable function is `0`, empty infima and suprema).
- Build one module at a time, with one cold review per module by a fresh subagent that has a read list and a limit of about 40 tool calls.
- Suggested order: 55, 56, 58, 57, 60, 59, so the two L items come last. If a module can't be closed, stop at a clean point and say exactly what was not reached. A tool-call limit is never a reason to cut work short, because Dustin will press continue.

Rules for this order
- Citations: for a paper or book you did not read, give author, title and year only, and say nothing about what it contains.
- Keep the constant count honest. Today it is 2744 constants, 109 modules and 4126 build jobs. Predict the new count before any gate runs, by Method B (compile scratch copies of the new modules and count what they add). Make the prediction blind this time: LEAN-23's vacuity probe printed the module totals before the prediction was written, so write prediction.txt first and run no probe on a module until it exists. Also model the helpers for Method A (`field_simp` and `omega` helpers, `eq_def`, `match_1`, and `_proof_` lemmas inside definitions). Reconcile any miss name by name.
- Predict the build job count as 4126 plus one per new module plus the new Mathlib modules your imports pull in; list the import closure of the environment for the old and new import lists, as LEAN-23 did.
- Run all six gates, then gate 7 as in LEAN-23: ~/lean/recheck/run-recheck.sh with your last commit and this repo's path (take the usage from the script's own header). Nothing may be edited under ~/lean/recheck.
- Nothing under ~/trading. No push. No sudo. Do not start batch 9 or 10.

Report
Write inbox/threads/staging/LEAN-24-report.md through ds_write_staging and compare post_sha256 with your own hash. Include: each item's result in one sentence, predicted beside measured, the hypothesis table, the commits, what was not reached, and the push command as one line, not run:
cd ~/lean/classical-lean-paper-crypto && git push origin paper-crypto-19:master && git push github paper-crypto-19:master
Then stop.

Dustin is still learning to read code but reads your replies carefully. Use plain words, define a technical term the first time you use it, and ask any decision in one line with your recommended answer first.

Sent with the order, verbatim:

taskcreate <3

Sent after the session listed the tasks and asked whether to start, verbatim:

absolutely bro. Thanks for asking.
