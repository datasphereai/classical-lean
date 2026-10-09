<!-- Written on 2026-10-09 by Claude Code session_019DbYoaqCsdYF7tW4YCkR4P on DSMain, from the plan /opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md (sha256 a3006a18bb59a1228f69b5426beb12bb9ec9f9e79ba61c2bcf91563a14665216, checked by sha256sum before this file was written), as Dustin ordered in chat on 2026-10-09. Batch 5 of the plan and Dustin's order are copied verbatim below. Written before the work began, per records/README.md rule 2. -->

# LEAN-21: Jacobi iteration, Newton's method, a finite chain with positive steps, Wald's identity, Fano's inequality, Hadamard's inequality, the variance of the binomial law, and Mathlib's relative entropy on a finite set

## Goal

Batch 5 of MATH-PLAN-library (items 32 to 39): eight named results, proved in the library with no sorry and no axiom. Item 38 is Mathlib's own `proof_wanted` (`variance_of_hasLaw_binomial`, in Mathlib's `Wanted/Probability/Distributions/Binomial.lean`, line 20); it is proved in this library with the same statement, its docstring says so, and nothing is offered to Mathlib.

Re-checked against Mathlib v4.34.0 (`5ed2965256`) before this file was written, as the order asks (`grep -rniE` over Mathlib; patterns, counts and the first hits in the session's evidence files `search.out` and `search2.out`): none of the eight items is in Mathlib, so none is dropped. Hits that exist: Newton's method only as `Polynomial.newtonMap` (Dynamics/Newton, a ring-theoretic iteration, not convergence over the reals), in Henselian rings and in `Nat.nthRoot`; `Matrix.det_le` (a bound from bounded entries, not Hadamard's); `det_ne_zero_of_sum_row_lt_diag` (Gershgorin: a strictly diagonally dominant matrix is invertible, used by item 32); "fano" only in names such as Stefano and `BinaryFan`; "Wald" only inside "Turnwald"; no stationary distribution, Doeblin or Dobrushin; `variance_of_hasLaw_binomial` only as a `proof_wanted`. Reduced to what Mathlib lacks: item 37 uses Mathlib's eigenvalues of a Hermitian matrix and the arithmetic–geometric mean inequality (not the LDL decomposition the row names); item 39 is Mathlib's `toReal_klDiv` read on a finite set, and its data-processing corollary is Mathlib's `klDiv_comp_right_le`; item 35 builds a martingale with Mathlib's `martingale_of_condExp_sub_eq_zero_nat` and uses Mathlib's `condExp_indep_eq`.

## Scope

### Batch 5 — order LEAN-21

| # | area | the result | Lean names | module | rests on | cost |
|---|---|---|---|---|---|---|
| 32 | 6 | Jacobi iteration converges for a strictly diagonally dominant matrix, with error `≤ ρ^k ‖x 0 − x*‖∞`. | `norm_jacobiIterate_sub_le` | new ClassicalLean.Analysis.JacobiIteration | Mathlib `det_ne_zero_of_sum_row_lt_diag` (Gershgorin.lean:63) | M |
| 33 | 6 | Newton's method converges quadratically near a simple root. | `abs_newtonStep_sub_le` | new ClassicalLean.Analysis.NewtonMethod | Mathlib `taylor_mean_remainder_lagrange` | M |
| 34 | 8, bridge | A finite chain whose step matrix has every entry at least `δ > 0` has one stationary distribution, approached at rate `(1 − n δ)^t` in `ℓ¹` (Doeblin). | `existsUnique_vecMul_eq_self`, `norm_vecMul_pow_sub_le` | new ClassicalLean.Probability.FiniteChain | Mathlib `rowStochastic` (Matrix/Stochastic.lean), `ContractingWith.fixedPoint`; library Channel `sum_vecMul_eq_sum`, `vecMul_nonneg`; generalises TwoStateChain | M–L |
| 35 | 8 | Wald's identity for a bounded stopping time: `E[S τ] = m E[τ]`. | `integral_stoppedValue_sum_eq` | ClassicalLean.Probability.FairGame | library `integral_stoppedValue_eq`; Mathlib `condExp_indep_eq` | M |
| 36 | 5 | Fano's inequality: `H(X | Y) ≤ h(P_e) + P_e log (|X| − 1)`. | `condEntropy_le_binEntropy_add` | new ClassicalLean.InformationTheory.Fano | item 9; Mathlib `Real.binEntropy` | M |
| 37 | 1 | Hadamard's inequality: `det A ≤ ∏ A i i` for positive semidefinite `A`. | `det_le_prod_diag` | new ClassicalLean.Algebra.HadamardInequality | Mathlib LDL (`LDL.lower_conj_diag`, Analysis/Matrix/LDL.lean) or Schur complements | M–L |
| 38 | 2 | The binomial law has variance `n p (1 − p)` (Mathlib's own `proof_wanted`). | `variance_binomial` | new ClassicalLean.Probability.BinomialVariance | Mathlib `binomial_eq_sum_dirac`, `integral_binomial` | M |
| 39 | 10, bridge | For `p, q ≥ 0` with support, `(klDiv μ_p μ_q).toReal = relEntropy p q + ∑ q − ∑ p`; the library's data-processing inequality then follows from Mathlib's. | `toReal_klDiv_eq_relEntropy` | ClassicalLean.Probability.RelativeEntropyGrowth | library `toReal_klDiv_eq_sum`; Mathlib `klDiv_comp_right_le` (KullbackLeibler/DataProcessing.lean:186) | M |


Not in scope: batches 6 to 8 of the plan; Mathlib's second `proof_wanted` in the same file (`condVar_of_hasLaw_binomial`); offering anything to Mathlib; anything under ~/trading; any edit under ~/lean/recheck (its script is only run, as gate 7); any push.

## Done-means

Dustin's order, verbatim:

Do batch 5 of /opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md as order LEAN-21. It continues the Lean library where order LEAN-20 left off.

1. Run sha256sum on that plan. I expect a3006a18bb59a1228f69b5426beb12bb9ec9f9e79ba61c2bcf91563a14665216. If it differs, stop and tell me.
2. Read /opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library-HANDOFF.md first, then the plan in full (sections 4 and 9 matter most), then LEAN-20-report.md, RECHECK-1-report.md, and the "Known traps" section of LEAN-16-order.md, all in that same lane folder.
3. git fetch origin; origin/master must be 59a4749 (LEAN-20, pushed). If it is not, stop and tell me. Branch paper-crypto-16 from it.
4. Batch 5 is items 32 to 39. Item 38 is Mathlib's own proof_wanted; prove it in this library as planned and say so in its docstring. Do not offer anything to Mathlib.
5. Before writing anything, re-check each item against Mathlib v4.34.0 by search. If Mathlib has an item, drop it or reduce it to what is missing, and say which. Check every citation of a book or paper against the statement you actually prove.
6. Work exactly as LEAN-20 did: records first; the round fragment naming each new module's path before that module's commit (in the order copy, new modules in dotted form only); statements with sorry first, then proofs; a dropped-hypothesis table with exact cases; a check script that exits with an error on any failure; one cold review per module by a reviewer subagent without persistent memory, before its commit; no sorry, no axiom, plain-words docstrings, no trading words in names.
7. Gates: the six gates, plus a seventh: ~/lean/recheck/run-recheck.sh <your last commit> ~/lean/classical-lean-paper-crypto, which must end "ALL PASSED". Run it, do not edit anything under ~/lean/recheck.
8. Theorem count against 2442. Predict it before any gate runs, and NOT with a counter that uses the gate's own rule (LEAN-20 did that, so its hit tested nothing). Predict from the source: count the theorem and lemma declarations you wrote, then say how many Lean-generated helpers you expect on top. After the gate runs, reconcile the two numbers name by name and explain every difference.
9. Nothing in ~/trading, no push.
10. Write the report at /opt/datasphere/lane/inbox/threads/staging/LEAN-21-report.md through ds_write_staging, comparing post_sha256 with your own hash. Then stop.

use taskcreate
