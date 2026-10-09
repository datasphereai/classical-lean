<!-- Written on 2026-10-09 by Claude Code session_019VHs1gNRScdbNoDT2HAccf on DSMain, from the plan /opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md (sha256 b24f5cc872ef2aa3506bddfdf6b88cb0b9aa570598d2af43647f43319d0387b2, written through the datasphereai connector, post_sha256 equal), which Dustin approved in chat on 2026-10-09 with no note, so the plan's four recommended decisions stand. Batch 1 and the plan's section 7 are copied verbatim below. Written before the work began, per records/README.md rule 2. -->

# LEAN-17: the residual variance, two-outcome Pinsker, a Chernoff bound from the score, the variance of an AR(1) average, data processing for mutual information, and source coding

## Goal

Batch 1 of MATH-PLAN-library: eight named results, each absent from Mathlib v4.34.0 by the searches in the plan's section 5, proved in the library with no sorry and no axiom.

## Scope

### Batch 1 — order LEAN-17 (8 items, about 16 main theorems)

| # | area | the result, in one sentence | Lean names | module | rests on | cost |
|---|---|---|---|---|---|---|
| 1 | 1 | For a design `X` with `n` rows, `p` columns and invertible Gram matrix, the residual maker has trace `n − p` and rank `n − p`. | `trace_residualMaker`, `rank_residualMaker` | ClassicalLean.Statistics.FrischWaughLovell | library `residualMaker`, `leastSquares_mul_self`, `residualMaker_mul_self`; Mathlib `Matrix.trace_mul_comm`, `IsIdempotentElem.isProj_range`, `LinearMap.IsProj.trace` (Trace.lean:327), `Matrix.rank_eq_finrank_range_toLin` | S (trace), M (rank) |
| 2 | 2 | The mean of a quadratic form `Xᵀ A X` of a random vector is `trace (A S) + mᵀ A m`, with `m` the mean and `S` the covariance matrix. | `integral_dotProduct_mulVec` | ClassicalLean.Probability.CovarianceDirections | library `covMatrix`; Mathlib `covariance_eq_sub` (Moments/Covariance.lean:54), `integral_finsetSum` | S |
| 3 | 10, bridge | In `y = X β + ε` with noise of mean 0 and covariance `σ² · 1`, the residual sum of squares has mean `σ² (n − p)`, so dividing it by `n − p` estimates `σ²` without bias. | `integral_residual_sq`, `integral_residual_sq_div` | new ClassicalLean.Statistics.ResidualVariance | items 1 and 2; library `residualMaker_mul_eq_zero`, `transpose_residualMaker`. Bridge: Probability.CovarianceDirections (`covMatrix`) × Statistics.FrischWaughLovell (`residualMaker`) | S |
| 4 | 5 | Pinsker's inequality for two outcomes: the relative entropy of `(q, 1 − q)` to `(p, 1 − p)` is at least `2 (q − p)²`, for `0 < p < 1`, `0 ≤ q ≤ 1`. | `two_mul_sq_sub_le_relEntropy` | ClassicalLean.InformationTheory.Entropy | library `relEntropy`; Mathlib `monotoneOn_of_deriv_nonneg`, `antitoneOn_of_deriv_nonpos` | S–M |
| 5 | 10, bridge | The Chernoff–Hoeffding bound in relative-entropy form, with no independence: outcomes in `[0, 1]`, each with mean at most `p₀` given the past; for `p₀ ≤ q < 1` the chance that `N` of them sum to at least `q N` is at most `exp (−N · D(q ‖ p₀))`, and so (item 4) at most `exp (−2 N (q − p₀)²)`. Hoeffding 1963, Theorem 1. | `measureReal_sum_ge_le_exp_neg_relEntropy`, `measureReal_sum_ge_le_exp_neg_sq` | ClassicalLean.Probability.LikelihoodScore | library `measureReal_exists_le_score`, `scoreFactor`, `relEntropy`, item 4; Mathlib `strictConcaveOn_log_Ioi`. Bridge: Probability.LikelihoodScore (Ville's inequality for the score) × InformationTheory.Entropy (`relEntropy`) | S–M |
| 6 | 9, bridge | The average of `n` values of a steady first-order recursion `x (t+1) = a x t + e t`, `0 ≤ a < 1`, noise variance `s²`, has variance at most `s² / ((1 − a)² n)`, with an exact form beside it: the long-run variance of AR(1) is `s² / (1 − a)²`. | `variance_average_eq_of_steady`, `variance_average_le_of_steady` | ClassicalLean.Probability.EffectiveSampleSize | library LinearPrediction `covariance_add`, `variance_eq_steady`; EffectiveSampleSize `variance_average`, `sum_sum_pow_eq`, `variance_average_le_of_cov_eq`. Bridge: the two modules; EffectiveSampleSize has no library user today (ROADMAP §1.16) | S |
| 7 | 10, bridge | Data processing for mutual information: if `Z` is made from `Y` alone by a channel (`X → Y → Z`), then `I(X; Z) ≤ I(X; Y)`. | `mutualInfo_markov_le` | ClassicalLean.InformationTheory.MutualInformation | library `Channel.relEntropy_vecMul_le` applied to the channel `(x, y) ↦ (x, z)` with weight `[x = x'] K y z`; `mutualInfo`. Gives `mutualInfo` its first user outside its module | S |
| 8 | 10, bridge | Shannon's source coding bound: a uniquely decodable code over `D` letters has mean codeword length at least `H(p) / log D`; prefix-free codes too. | `shannonEntropy_le_sum_mul_length`, `shannonEntropy_le_sum_mul_length_of_isPrefixFree` | new ClassicalLean.InformationTheory.SourceCoding | Mathlib `IsUniquelyDecodable.finsetSum_one_div_card_pow_length_le_one` (Coding/KraftMcMillan.lean:145), `IsPrefixFree.isUniquelyDecodable` (Coding/PrefixFree.lean:50); library `sum_sub_sum_le_relEntropy` (the unnormalised Gibbs inequality) | S |

Not in scope: batches 2 to 7 of the plan; anything under ~/trading; any push.

## Done-means

## 7. Batch 1 as order LEAN-17: how I would run it, after approval

1. **The plan to the lane.** Write this file's content to a scratch copy; `sha256sum` it; write it
   with `ds_write_staging` to `inbox/threads/staging/MATH-PLAN-library.md`; compare `post_sha256`
   with my hash. Then `ds_read` it back and hash again.
2. **Branch.** `git fetch origin`. If `origin/master` is `65e10e5`, `git checkout -b paper-crypto-12
   origin/master`; otherwise `git checkout -b paper-crypto-12 65e10e5` (paper-crypto-11's head).
   `nice -n 19 lake build` first: rc 0, 4011 jobs, 0 warnings, predicted.
3. **Records first, one commit, no `.lean` file:** the order copy
   `records/orders/<UTC>__claude-code__order-lean17-<slug>.md` (Goal / Scope / Done-means; batch 1
   of this plan verbatim, modules in dotted form only), its `INDEX.md` row, a `CLAIMS.md` row naming
   every module touched, and the first part of the round 45 fragment
   `records/rounds/<UTC>__round-45-<slug>.md`, which names the two new modules' paths
   (Statistics/ResidualVariance and InformationTheory/SourceCoding, with the `.lean` suffix) so
   check_records passes before their commits. Evidence folder `~/lean/lean17-checks/`
   (`evidence.log`: time, label, rc, prediction, command).
4. **Statements first.** All 8 items' statements in a scratch file under `~/lean/lean17-checks/`,
   elaborated with `sorry` (`lake env lean`, absolute paths): rc 0 and one `sorry` warning per
   statement. A Lean census of that file (`foldStage2`, positional arguments) gives my prediction of
   the new constant count, written before any gate is run.
5. **Hypotheses.** A standard-library Python script (exact `Fraction`s, seeded) checks each main
   theorem on cases and, for each hypothesis, an exact case that fails when it is dropped; where
   cheap, the case is also stated in a scratch `Dropped.lean` with a planted control that must fail.
   Known already: item 6 without `0 ≤ a` fails at `a = −1/2`, `n = 2` (`s²/3` against `s²/4.5`);
   item 4 without `0 < p` fails at `p = 0`, `q = 1/2` (Lean's `log 0 = 0` gives `−0.347` against
   `0.5`). Hypotheses with no case are marked "not shown needed".
6. **Proofs, one module at a time,** in this order: FrischWaughLovell (1), CovarianceDirections (2),
   ResidualVariance (3, new; added to `ClassicalLean.lean`), Entropy (4), LikelihoodScore (5),
   EffectiveSampleSize (6), MutualInformation (7), SourceCoding (8, new). Warnings judged only by
   `lake build <module>`. Before each module's commit: one cold review of its new declarations by a
   fresh general-purpose subagent with no persistent memory, in its own scratch folder, told that
   other work proceeds meanwhile; its output saved with its sha256; `~/.claude/agent-memory/` checked
   after. Plain-words docstrings; no `sorry`, no axiom, no trading words in names; each module's
   docstring gets one bullet per new theorem and its hypothesis notes. Known traps from LEAN-16
   apply (`push Not`, `integral_finsetSum`, `omit … in` before the docstring, the `git add` hook and
   asterisks, `λ` not a name). The vacuity budget stays 400000; a timeout means one line to Dustin.
7. **Gates on the clean tree:** `nice -n 19 lake build` (0 warnings), `lake env lean
   tools/AxiomGate.lean`, `lake env lean tools/VacuityGate.lean`, `python3 -I tools/check_sorry.py`,
   `python3 -I tools/banned_vocab_scan.py`, `python3 -I tools/check_records.py` (83 modules);
   check_sorry fire-tested on a planted `sorry` in a scratch copy; `#print axioms` for every new
   main theorem; the constant count against 2205 beside my census prediction. Then the records
   commit: fragment completed with hashes and quotes checked by script, INDEX row landed, claim closed.
8. **Not touched:** anything in `~/trading` (and `~/trading/science`); no push; no sudo.
9. **Report** `inbox/threads/staging/LEAN-17-report.md` through `ds_write_staging` (post_sha256
   compared): batch 1, the outputs, the hypothesis table, the commits, what was not reached, and the
   push command as one line, not run:
   `cd ~/lean/classical-lean-paper-crypto && git push origin paper-crypto-12:master && git push github paper-crypto-12:master`.
   (If LEAN-16 is still unpushed, that one push carries both orders.) Then stop and wait.
