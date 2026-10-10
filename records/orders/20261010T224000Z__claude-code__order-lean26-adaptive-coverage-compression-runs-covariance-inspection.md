<!-- Written on 2026-10-10 (UTC) by Claude Code session_015ETfwXkALXqpC9EJSHqpTp on DSMain, from the plan /opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md (sha256 c73957af6a9f2d19aacfd3acfc1d42d9a2a124fabefae62bbfee026090422898, checked by sha256sum before this file was written; equal to the hash the order expects), as Dustin ordered in chat on 2026-10-10. Batch 10 of the plan and the order are copied verbatim below, with the ruling on item 68 sent during the session. Written before any module was changed, per records/README.md rule 2. -->

# LEAN-26: adaptive coverage on any sequence, a code as a bet, streaks under chance, noise in correlation eigenvalues, and the inspection paradox

## Goal

Batch 10 of MATH-PLAN-library (items 67 to 71), the last batch of the plan, in one order (no split): five named results, guarantees on any sequence and tests against a null law, proved in the library with no sorry and no axiom. The item numbers are the plan's.

Re-checked against Mathlib v4.34.0 (`5ed2965256`) before this file was written, as the order asks (`grep -rliE` over Mathlib; patterns, counts and first hits in the session's evidence file `~/lean/lean26-checks/search.out`): none of the five items is in Mathlib, so none is dropped or reduced. "conformal predict|adaptive conformal" 0 files; "compress" 5 files, all set-family compressions in Combinatorics/SetFamily; "longest run|Erd.s.R.nyi|run of heads" 1 file, the random-graph model (Probability/Combinatorics/BinomialRandomGraph/Defs.lean); "runs? of (length|losses|ones|heads)|streak" 0; "Marchenko|Pastur|Wishart|sample covariance" 0; "inspection paradox|length.biased|size.biased|renewal" 0; "Kraft" 2 files (Mathlib's Kraft and Kraft–McMillan inequalities, which item 68 uses through the library's SourceCoding). Library: none of the five results.

Item 68 follows the ruling sent during the session (copied below): the compression test is a test against a null law fixed in advance, not a clumping test; a rejection means "not this null law", which can come from clumping, from a win rate different from the null's, or both.

## Scope

### Batch 10 — guarantees on any sequence, and tests for patterns (added 2026-10-09 by claude-ai at Dustin's request for advantages from fields not tied to trading; his veto open on every row; may split)

Why these: MATH-PLAN-trading.md ("Why math first") names two obstacles, that the theorems assume independent trades and that the wait for evidence is long. Item 67 holds on every sequence; items 68 and 69 are tests for clumping (trading area 5) with an exact false-alarm rate; item 70 says how much apparent structure across many markets is noise; item 71 is a sampling bias.

Searched 2026-10-09 on DSMain, Mathlib v4.34.0 (files; library in brackets): "conformal predict|adaptive conformal" 0 [0]; "compress" 5, all set-family compressions in Combinatorics/SetFamily [0]; "longest run|Erd.s.R.nyi|run of heads" 1, the random-graph model (Probability/Combinatorics/BinomialRandomGraph) [0]; "Marchenko|Pastur|Wishart|sample covariance" 0 [0]; "inspection paradox|length.biased|size.biased|renewal" 0 [0]. Not proposed, because the library has them: exponential weights (ExponentialWeights), a one-asset universal portfolio (UniversalMixture), e-BH (EValueStepUp, StepUpProcedure), Ville's inequality (MaximalInequality), Kelly (LogGrowthRate). Every numeric claim below was checked before writing by MATH-PLAN-batch10-checks.py (sha256 7059d2f00cbcf26865ef02f4ff38921a255c49a49ebe55bfc02ee27b81072a11), output MATH-PLAN-batch10-checks.out (b19342aaafba39b5198e64d771c072eebc0f581a8aaa61412ce3103a6747206b), both in this folder: all hit.

| # | area | the result | Lean names | module | rests on | cost |
|---|---|---|---|---|---|---|
| 67 | 2, 9, bridge | Adaptive coverage on any sequence: with `α ∈ (0, 1)`, `γ > 0`, `α₁ ∈ [0, 1]` and `α (t + 1) = α t + γ (α − err t)`, where `err t ∈ {0, 1}` is `0` whenever `α t ≤ 0` and `1` whenever `α t ≥ 1` (the forecast interval is everything, or empty), the mean of `err` over `T` rounds is within `(max α₁ (1 − α₁) + γ) / (γ T)` of `α`, for every sequence. No independence and no model. Check P5. | `abs_mean_err_sub_le` | new ClassicalLean.Statistics.AdaptiveCoverage | induction (`α t` stays in `[−γ, 1 + γ]`) and a telescoping sum | S |
| 68 | 5, 2, bridge | A code is a bet: for a prefix-free code on the `2^n` win–loss strings of length `n` with lengths `L x`, and a null law `p₀` with every `p₀ x > 0`, the score `2^(−L x) / p₀ x` has mean at most `1` under `p₀` (an e-value), by Kraft; under the fair-coin null, the chance that a string compresses by `k` bits or more is at most `2^(−k)`. So any compressor is a valid test for clumping with an exact false-alarm rate, and its e-value feeds EValueStepUp. Check P7. | `sum_two_pow_neg_len_div_le_one`, `measureReal_len_le_sub_le` | new ClassicalLean.InformationTheory.CompressionTest | library SourceCoding (Kraft), EValueStepUp | S–M |
| 69 | 2, 8 | Streaks under chance: in `n` independent trials that each lose with chance `q`, the chance of some run of at least `r` losses is at most `(n − r + 1) q^r`, and the chance of none is at most `(1 − q^r)^⌊n/r⌋`; so for fair trials the longest run is about `log₂ n`. Exact worked numbers (check P3): the mean longest run in 100 fair trials is 5.99; in 200 fair trials a run of 7 or more has chance 0.544. A streak counts as evidence only past these numbers. Check P4. | `measureReal_exists_run_le`, `measureReal_no_run_le` | new ClassicalLean.Probability.LongestRun | Mathlib `iIndepFun`; a union bound over start positions; disjoint blocks | S–M |
| 70 | 1, 2, bridge | Noise spreads correlation eigenvalues: if a `p × n` table `X` has independent entries of mean `0`, variance `1` and fourth moment `μ₄`, and `S = X Xᵀ / n`, then `E[tr (S²)] / p = 1 + (μ₄ + p − 2) / n`, while the true covariance has every eigenvalue `1`. With 50 markets and 250 days of Gaussian data the eigenvalues' mean square is about 20% too large from noise alone. The finite-sample core of Marchenko–Pastur; the full law is not planned (very large). Checks P1 (exact, five sizes) and P2. | `integral_trace_sq_sampleCov` | ClassicalLean.Probability.CovarianceDirections | library `integral_dotProduct_mulVec`; Mathlib `iIndepFun`, independence and `integral_mul` | M |
| 71 | 8 | The inspection paradox, finite form: for gaps `L 1, …, L k > 0` laid end to end, a point chosen uniformly at random lands in a gap of mean length `∑ L i² / ∑ L i`, which is at least the plain mean `∑ L i / k`, with equality only when all gaps are equal. So durations measured by sampling at random moments (holding times, time between events) come out too long. | `sum_sq_div_sum_ge_mean` | new ClassicalLean.Probability.InspectionParadox | Cauchy–Schwarz for finite sums (Mathlib `sq_sum_le_card_mul_sum_sq`) | S |

Changed or added: four new modules, ClassicalLean.Statistics.AdaptiveCoverage (item 67), ClassicalLean.InformationTheory.CompressionTest (item 68), ClassicalLean.Probability.LongestRun (item 69) and ClassicalLean.Probability.InspectionParadox (item 71); the existing module ClassicalLean.Probability.CovarianceDirections, extended (item 70); `ClassicalLean.lean` (four import lines).

Not in scope: the full Marchenko–Pastur law; any change to VacuityGate (its case 3 blind spot, LEAN-25 report, is a separate order); offering anything to Mathlib; anything under ~/trading; any edit under ~/lean/recheck (its script is only run, as gate 7); any push; any sudo.

## Done-means

Dustin's order, verbatim:

LEAN-26 is batch 10 of the classical-lean library plan: items 67 to 71, guarantees on any sequence and tests for patterns, in one order (no split; every item is small or small-to-medium). It continues LEAN-25 (batch 9), which Dustin pushed; origin and github master should both be bd8d151. This is the last batch of the plan.

The item numbers are the plan's. Use them in every commit message, record row and report line:
- 67: adaptive coverage on any sequence (new module ClassicalLean.Statistics.AdaptiveCoverage)
- 68: a code is a bet, compression as a test with an exact false-alarm rate (new module ClassicalLean.InformationTheory.CompressionTest)
- 69: streaks under chance (new module ClassicalLean.Probability.LongestRun)
- 70: noise spreads correlation eigenvalues, the finite-sample core (module ClassicalLean.Probability.CovarianceDirections, which already exists; extend it)
- 71: the inspection paradox, finite form (new module ClassicalLean.Probability.InspectionParadox)
Dustin's veto is open on every row of this batch and he has not used it; build the items as planned.

Setup
1. Run `sha256sum` on /opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md. I expect c73957af6a9f2d19aacfd3acfc1d42d9a2a124fabefae62bbfee026090422898 (measured a minute ago; the plan has 71 items in 10 batches). If it differs, say so in your report.
2. Read, in the same folder: the plan (section 4 batch 10, section 5 searches, section 9), LEAN-25-report.md, MATH-PLAN-library-HANDOFF.md, MATH-PLAN-batch10-checks.py and its .out (hashes in the plan), and the "Known traps" section of LEAN-16-order.md.
3. `git fetch origin`. origin/master must be bd8d151 and `git ls-remote github master` must agree. If not, stop and tell me. Otherwise branch `paper-crypto-21` from it.

The work
Follow the LEAN-19/LEAN-25 method:
- Re-check each item against Mathlib (v4.34.0) by search before building. The plan's searches found none of them, but re-run them. If an item is already there, drop or reduce it and say so.
- Records first, in one commit: the order copy (new modules in dotted form only), the INDEX row, the CLAIMS row, and the next round fragment. check_records must still pass on the four new module paths.
- Write the statements with `sorry` first and elaborate them. Those sorries are scratch only and must be gone from the library before any commit that builds it.
- State each theorem exactly. Item 67: say what "any sequence" quantifies over and where `err t` is forced to 0 or 1; item 68: say what a prefix-free code on strings of length n is as a Lean statement, and what "compresses by k bits" means; item 69: say what a run of losses in a sequence of trials is; item 70: say what "independent entries with mean 0, variance 1 and fourth moment μ₄" means in Lean, and say what integrability you assume (an integral of a non-integrable function is 0 in Lean); item 71: say what "chosen uniformly at random" means for a finite list of gaps.
- Write a dropped-hypothesis table with exact arithmetic where you can, and mind Lean's junk values (`x / 0 = 0`, `log 0 = 0`, `⌊n / 0⌋`, `r = 0` and `r > n` for runs, the empty sum, the integral of a non-integrable function).
- Build one module at a time, with one cold review per module by a fresh subagent that has a read list and a limit of about 40 tool calls. A review comes after a statement is final. If a gate forces a rewording, do it before the module's review, so the reviewer sees the final statement. If a rewording happens after a review, say so in the report and run a statement-equivalence review as in LEAN-25.
- Suggested order: 71, 67, 69, 68, 70, so the largest comes last. If a module can't be closed, stop at a clean point and say exactly what was not reached. A tool-call limit is never a reason to cut work short, because Dustin will press continue.

Rules for this order
- Citations: for a paper or book you did not read, give author, title and year only, and say nothing about what it contains.
- Keep the constant count honest. Today it is 3052 constants, 116 modules and 4160 build jobs. Predict the new count before any gate runs, by Method B (compile scratch copies of the new and changed modules and count what they add), and make the prediction blind as in LEAN-25: write prediction.txt before any census, vacuity probe or gate runs on a new module. For Method A, model the helpers by their measured rates in LEAN-25: `_proof_` lemmas inside theorem bodies (mostly from `omega` and `decide`, which LEAN-25 modelled only for definitions), `eq_N`, `eq_def` and `match_N` lemmas for recursive definitions that `simp` unfolds, and `congr_simp` lemmas; `field_simp` gave 0 helpers in LEAN-25 and 0 to 8 in LEAN-24, so give a range. Reconcile any miss name by name.
- Predict the build job count as 4160 plus one per new module plus the new Mathlib modules your imports pull in; list the import closure of the environment for the old and new import lists, as LEAN-23 to LEAN-25 did.
- Run all six gates, then gate 7: ~/lean/recheck/run-recheck.sh with your last commit and this repo's path (take the usage from the script's own header). Nothing may be edited under ~/lean/recheck. Leave VacuityGate alone: its case 3 has a known blind spot (LEAN-25 report), and any change to it is a separate order.
- Nothing under ~/trading. No push. No sudo.

Report
Write inbox/threads/staging/LEAN-26-report.md through ds_write_staging and compare post_sha256 with your own hash. Include: each item's result in one sentence, predicted beside measured, the hypothesis table, the commits, what was not reached, and the push command as one line, not run:
cd ~/lean/classical-lean-paper-crypto && git push origin paper-crypto-21:master && git push github paper-crypto-21:master
Then stop.

Dustin is still learning to read code but reads your replies carefully. Use plain words, define a technical term the first time you use it, and ask any decision in one line with your recommended answer first.

Sent with the order, verbatim:

taskcreate <3

Sent during the session, before this file was written, verbatim:

Ruling from Dustin's helper on item 68: the fair-coin test rejects for an uneven win rate as well as for clumping, so do not describe it as a clumping test. Do this:
1. Prove the general form: for a prefix-free code and any null law p₀ with every p₀ x > 0, the score 2^(−L x) / p₀ x has mean at most 1 under p₀, and for α in (0, 1) the chance under p₀ that the score is at least 1/α is at most α (Markov). State it for a product Bernoulli(p) law with a win rate p fixed before looking at the data, as well as for a general p₀.
2. Keep the fair-coin form (the chance of compressing by k bits or more is at most 2^(−k)) as the special case p = 1/2.
3. In the module docstring and in the LEAN-26 report's item 68 line, say plainly: a rejection means "not this null law", which can come from clumping, from a win rate different from p, or both. The exact false-alarm rate holds only if p is fixed in advance; estimating p from the same trades breaks it (say this by hand, with a small exact example in the dropped-hypothesis table if you can build one). Do not claim the test isolates clumping.
4. If you can, add one exact example where the win rate is 3/5, nothing clumps (independent trials), and the fair-coin test still rejects with high chance, so the point is checked, not only stated.
Carry on with the rest of the batch.
