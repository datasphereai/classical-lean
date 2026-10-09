<!-- Written on 2026-10-09 by Claude Code session_016HZA2rbHQv4Gvdu2sAUW2u on DSMain, from the plan /opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md (sha256 b9b64503909bc9d42ab562b9aa83474e86fa5661be6c14b5b3add5badf8d1789, checked by sha256sum before this file was written), as Dustin ordered in chat on 2026-10-09. Batch 3 of the plan and Dustin's order are copied verbatim below. Written before the work began, per records/README.md rule 2. -->

# LEAN-19: the descent lemma and gradient descent, KKT sufficiency, exponential weights, Rao–Blackwell, and Kolmogorov's maximal inequality

## Goal

Batch 3 of MATH-PLAN-library (items 17 to 23): seven named results, proved in the library with no sorry and no axiom; and, as its own commit, ROADMAP.md §1.14 pattern P2 brought up to date with LEAN-18's item 11.

Re-checked against Mathlib v4.34.0 before this file was written, as the order asks (`grep -rniE` over Mathlib, Mathlib's `Wanted/` folder too; patterns, counts and what the hits are in the session's evidence file `search.txt`): none of items 17 to 23 is in Mathlib, so none is dropped. Two are reduced to what Mathlib lacks. Item 22 (Rao–Blackwell) is to be derived from Mathlib's law of total variance `integral_condVar_add_variance_condExp`, not proved again. Item 23 (Kolmogorov's maximal inequality) is to be derived from Mathlib's `maximal_ineq`; the missing piece, that the square of a square-integrable martingale is a submartingale, is proved here from Mathlib's conditional variance. Item 19 takes Mathlib's `StrongConvexOn` as its hypothesis, and item 21 takes Hoeffding's lemma from Mathlib's `hasSubgaussianMGF_of_mem_Icc`.

## Scope

### Batch 3 — order LEAN-19

| # | area | the result | Lean names | module | rests on | cost |
|---|---|---|---|---|---|---|
| 17 | 7 | Descent lemma: if `∇f` is `L`-Lipschitz, `f y ≤ f x + ⟪∇f x, y − x⟫ + (L/2) ‖y − x‖²`. | `le_add_inner_gradient_add_sq` | new ClassicalLean.Analysis.GradientDescent | Mathlib `HasGradientAt` (Calculus/Gradient/Basic), mean value on `t ↦ f (x + t (y − x))`. Used by 18, 19 | M |
| 18 | 7 | A differentiable convex `f` lies above its tangent planes, and gradient descent with step `1/L` has `f (x k) − f x* ≤ L ‖x 0 − x*‖² / (2k)` (Nesterov 2004, Thm 2.1.14). | `add_inner_gradient_le`, `sub_le_of_gradientStep` | ClassicalLean.Analysis.GradientDescent | item 17; Mathlib `ConvexOn`, one-variable slope lemmas. Used by 19, 20 | M–L |
| 19 | 7 | Strongly convex and `L`-smooth: gradient descent converges at the rate `(1 − m/L)^k`. | `dist_gradientStep_le` | ClassicalLean.Analysis.GradientDescent | items 17, 18; Mathlib `StrongConvexOn` (Convex/Strong.lean:118) | M |
| 20 | 7 | The KKT conditions are sufficient for a convex problem. | `isMinOn_of_kkt` | ClassicalLean.Analysis.GradientDescent | item 18; Mathlib's own TODO (LagrangeMultipliers.lean:24) | S–M |
| 21 | 7, bridge | Hedge (exponential weights): with losses in `[0, 1]` and weights `softmax (−η · past losses)`, total expected loss is at most the best expert's plus `log K / η + η T / 8` (Freund–Schapire 1997). | `sum_inner_softmax_le` | new ClassicalLean.Analysis.ExponentialWeights | library `softmax`, `logSumExp`, `le_logSumExp`, `log_softmax`; Mathlib `hasSubgaussianMGF_of_mem_Icc` (SubGaussian.lean:857, Hoeffding's lemma) on a finite measure | M |
| 22 | 2 | Rao–Blackwell: conditioning an estimator never raises its mean squared error, `E[(E[T | m] − θ)²] ≤ E[(T − θ)²]`. | `integral_sq_condExp_sub_le` | new ClassicalLean.Statistics.RaoBlackwell | Mathlib `integral_condVar_add_variance_condExp` (CondVar.lean:135), `integral_condExp` | S |
| 23 | 8 | Kolmogorov's maximal inequality: `P(max_{k ≤ n} |S k| ≥ ε) ≤ E[S n²] / ε²` for a square-integrable martingale. | `measureReal_exists_abs_ge_le` | ClassicalLean.Probability.MaximalInequality | Mathlib `maximal_ineq` (OptionalStopping.lean:144), `condExp_mul_of_stronglyMeasurable_left` (for `S²` a submartingale) | M |

Also: ROADMAP.md §1.14, pattern P2, the sentence "Not stated as one theorem", updated to say it is proved, naming the theorems and order LEAN-18.

Not in scope: batches 4 to 7 of the plan; anything under ~/trading; any push.

## Done-means

Dustin's order, verbatim:

Do batch 3 of /opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md as order LEAN-19. It continues the Lean library where order LEAN-18 left off.

1. Run sha256sum on that plan. I expect b9b64503909bc9d42ab562b9aa83474e86fa5661be6c14b5b3add5badf8d1789. If it differs, stop and tell me.
2. Read the plan in full, then /opt/datasphere/lane/inbox/threads/staging/LEAN-18-report.md, and the "Known traps" section of /opt/datasphere/lane/inbox/threads/staging/LEAN-16-order.md.
3. git fetch origin; origin/master must be eb2a150 (LEAN-18, pushed). If it is not, stop and tell me. Branch paper-crypto-14 from it.
4. Batch 3 is items 17 to 23. Before writing anything, re-check each against Mathlib v4.34.0 by search. If Mathlib has an item, drop it or reduce it to what is missing, and say which. Where the plan names a Mathlib lemma to build on (StrongConvexOn, hasSubgaussianMGF_of_mem_Icc, integral_condVar_add_variance_condExp, maximal_ineq), use it rather than re-proving it.
5. Also, as its own small commit: LEAN-18's item 11 proved that the Hessian of logSumExp is categoricalCov (softmax x). ROADMAP.md section 1.14, pattern P2, still says "Not stated as one theorem". Update that sentence to say it is now proved, naming the theorems and order LEAN-18.
6. Work exactly as LEAN-18 did: records first; the round fragment naming each new module's path before that module's commit (in the order copy, new modules in dotted form only); statements with sorry first, then proofs; a dropped-hypothesis table with exact cases; one cold review per module by a reviewer subagent without persistent memory, before its commit; no sorry, no axiom, plain-words docstrings, no trading words in names; all six gates pass, and the constant count against 2270, with your prediction written first.
7. Nothing in ~/trading, no push.
8. Write the report at /opt/datasphere/lane/inbox/threads/staging/LEAN-19-report.md through ds_write_staging, comparing post_sha256 with your own hash. End it with the push line for me, not run. Then stop.

I am still learning to read code and have adopted the habit of reading markdowns when I am uncertain, but I read your replies meticulously. Put everything I need in the reply, in plain language. When you need a decision from me, ask in one line with your recommended answer first.
