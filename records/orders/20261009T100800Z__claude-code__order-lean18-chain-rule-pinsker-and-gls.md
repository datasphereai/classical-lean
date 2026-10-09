<!-- Written on 2026-10-09 by Claude Code session_014tMro6KYq7f532WnRJZyjY on DSMain, from the plan /opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md (sha256 b9b64503909bc9d42ab562b9aa83474e86fa5661be6c14b5b3add5badf8d1789, checked by sha256sum before this file was written), as Dustin ordered in chat on 2026-10-09. Batch 2 of the plan and Dustin's order are copied verbatim below. Written before the work began, per records/README.md rule 2. -->

# LEAN-18: the chain rule for entropy, Pinsker's inequality, the Hessian of log-sum-exp, Hermite–Hadamard and the trapezoidal rule, rounding in inner products and Horner's rule, and generalised least squares

## Goal

Batch 2 of MATH-PLAN-library (items 9 to 16): eight named results, proved in the library with no sorry and no axiom.

Re-checked against Mathlib v4.34.0 before this file was written, as the order asks (`grep -rniE` over Mathlib, Mathlib's `Wanted/` folder too): none of items 9 to 16 is in Mathlib, so none is dropped or reduced. Item 12's left half is a case of Mathlib's `ConvexOn.map_set_average_le` and is to be derived from it, not proved again. Item 13 is a different statement from Mathlib's `trapezoidal_error_le` (a bound from the second derivative, not the sign of the error for a convex function).

## Scope

### Batch 2 — order LEAN-18

| # | area | the result | Lean names | module | rests on | cost |
|---|---|---|---|---|---|---|
| 9 | 5 | Chain rule: `H(X, Y) = H(X) + H(Y | X)`. | `condEntropy`, `shannonEntropy_eq_add_condEntropy` | ClassicalLean.InformationTheory.MutualInformation | library `shannonEntropy`; Mathlib `Fintype.sum_prod_type`. Used by 36 | S |
| 10 | 5 | Pinsker's inequality: `(∑ |p i − q i|)² ≤ 2 D(p ‖ q)` for probability vectors with support. | `sq_sum_abs_sub_le_two_mul_relEntropy` | ClassicalLean.InformationTheory.Channel | item 4; library `relEntropy_vecMul_le` with the two-column channel "is `p i ≥ q i`" | M |
| 11 | 10, bridge | The Hessian of log-sum-exp is the covariance of softmax: the Fréchet derivative of `logSumExp` is the softmax functional, and that of `softmax` is `categoricalCov (softmax x)`. | `hasFDerivAt_logSumExp`, `hasFDerivAt_softmax` | ClassicalLean.Simplex.SecondOrder | library `hasDerivAt_logSumExp` (CrossEntropy), `hasDerivAt_softmax_categoricalCov` (SecondOrder); Mathlib `HasFDerivAt.log`, `HasFDerivAt.sum`. Closes ROADMAP §1.14 P2 "not stated as one theorem" | S–M |
| 12 | 3 | Hermite–Hadamard: for `f` convex and continuous on `[a, b]`, `f ((a + b)/2) ≤ (1/(b − a)) ∫ f ≤ (f a + f b)/2`. | `convexOn_midpoint_le_average`, `average_le_convexOn_endpoints` | new ClassicalLean.Analysis.HermiteHadamard | Mathlib `ConvexOn.map_set_average_le` (Convex/Integral.lean:175; the left half is a case of it), `intervalIntegral.integral_mono_on` | S–M |
| 13 | 6 | For convex `f`, Mathlib's trapezoidal approximation is at least the integral. | `integral_le_trapezoidal_integral` | ClassicalLean.Analysis.HermiteHadamard | item 12; Mathlib `trapezoidal_integral`, `sum_trapezoidal_integral_adjacent_intervals` (TrapezoidalRule.lean:87) | S |
| 14 | 6 | Rounding error of a computed inner product: within `γ n · ∑ |x i y i|` of the exact one (Higham 2002, (3.5)). | `abs_dotComputed_sub_le` | ClassicalLean.Analysis.RoundingError | library `exists_sumComputed_eq`, `abs_prod_one_add_sub_one_le`, `gamma` | S |
| 15 | 6 | Horner's rule evaluated with rounding is within `γ (2n) · ∑ |a i| |x|^i` of `p(x)` (Higham 2002, (5.3)). | `abs_hornerComputed_sub_le` | ClassicalLean.Analysis.RoundingError | library rounding lemmas, item 14's pattern | S–M |
| 16 | 1 | Generalised least squares and Aitken's theorem: with `V` positive definite, `(Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is unbiased, equals `leastSquares` at `V = 1`, and every unbiased `C` has `C V Cᵀ − (Xᵀ V⁻¹ X)⁻¹` positive semidefinite. | `glsMatrix`, `glsMatrix_one`, `posSemidef_mul_mul_transpose_sub_inv` | new ClassicalLean.Statistics.GeneralizedLeastSquares | library GaussMarkov (`leastSquares`, its `D Dᵀ` decomposition); Mathlib `PosDef.inv`, `PosSemidef.mul_mul_conjTranspose_same` | M |

Not in scope: batches 3 to 7 of the plan; anything under ~/trading; any push.

## Done-means

Dustin's order, verbatim:

Do batch 2 of /opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md as order LEAN-18. It continues the Lean library where order LEAN-17 left off.

1. Run sha256sum on that plan. I expect b9b64503909bc9d42ab562b9aa83474e86fa5661be6c14b5b3add5badf8d1789 (claude-ai corrected one sentence in batch 1's row 7 after LEAN-17). If it differs, stop and tell me.
2. Read the plan in full, then /opt/datasphere/lane/inbox/threads/staging/LEAN-17-report.md, and the "Known traps" section of /opt/datasphere/lane/inbox/threads/staging/LEAN-16-order.md.
3. git fetch origin; origin/master must be 197910f (LEAN-17, pushed). Branch paper-crypto-13 from it.
4. Batch 2 is items 9 to 16. Before writing anything, re-check each against Mathlib v4.34.0 by search, since the plan's own check may have missed something; LEAN-17 found Mathlib already had data processing in measure form. If Mathlib has an item, drop it or reduce it to what is missing, and say which. Item 12's left half is already a case of Mathlib's ConvexOn.map_set_average_le, as the plan says: use it, don't re-prove it.
5. Work exactly as LEAN-17 did: records first; the round fragment naming each new module's path before that module's commit (in the order copy, new modules in dotted form only); statements with sorry first, then proofs; a dropped-hypothesis table with exact cases; one cold review per module by a reviewer subagent without persistent memory, before its commit; no sorry, no axiom, plain-words docstrings, no trading words in names; all six gates pass, and the constant count against 2235, with your prediction written first.
6. Nothing in ~/trading, no push.
7. Write the report at /opt/datasphere/lane/inbox/threads/staging/LEAN-18-report.md through ds_write_staging, comparing post_sha256 with your own hash. End it with the push line for me, not run. Then stop.
