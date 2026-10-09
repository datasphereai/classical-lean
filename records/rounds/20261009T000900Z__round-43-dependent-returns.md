# Round 43 — returns that depend on each other, the smallest edge a trade count can confirm, and what correlated quantities and pooled e-values are worth (order LEAN-15)

Session: Claude Code `session_016NFpe1U5QkBdhN4qifVB6C` on DSMain, as dustin, executing order
`LEAN-15` (`records/orders/20261008T235500Z__claude-ai__order-lean15-dependent-returns.md`), in the
worktree `~/lean/classical-lean-paper-crypto` on branch `paper-crypto-10`, made from `origin/master` =
`25cf9bb`. Lean and Mathlib v4.34.0. Nothing was pushed. Records were written before any module
change (`b5bb93d`). Evidence: `~/lean/lean15-checks/` (outside the repository), `evidence.log` (time,
label, rc, prediction, command per run). Dustin approved the plan in chat after Step 0.

Modules changed or added:

* `ClassicalLean/Probability/DependentSampleMean.lean` — item 1, `condExp_exp_mul_sub_le`, the
  one-sided conditional Hoeffding lemma (conditional mean at least `g`).
* `ClassicalLean/Probability/EdgeGrowth.lean` — items 2 and 3, a new section `dependent`:
  `integral_exp_mul_sum_le` (helper), `measureReal_wealth_lt_le_of_condExp`,
  `exp_neg_le_of_le_growth`, `measureReal_wealth_lt_le_of_condExp_of_le`; new import
  `ClassicalLean.Probability.DependentSampleMean`; item 6, the module docstring's five edits.
* `ClassicalLean/Probability/EffectiveSampleSize.lean` — new module, item 4: `variance_average`,
  `meanCrossCov`, `sum_cross_eq` (helper), `variance_average_eq`, `inv_card_le_variance_average`,
  `sum_range_pow_sub` (helper), `sum_sum_pow_eq`, `sum_sum_pow_le`, `variance_average_le_of_cov_eq`.
  Imports only `Mathlib.Probability.Moments.Variance`. Added to `ClassicalLean.lean`.
* `ClassicalLean/Probability/EValueStepUp.lean` — item 5, section `pooling`:
  `integral_average_le_one`, `integrable_prod_of_iIndepFun`, `integral_prod_le_one_of_iIndepFun`;
  new import `Mathlib.Probability.Independence.Integration`.
* `ROADMAP.md` §1.16 (two entries, each naming its measurement).
* `tools/VacuityGate.lean` — the per-theorem heartbeat budget raised from 200000 to 400000; the test
  is unchanged (below).

Statements: copied from the order's `LEAN-15-statements.lean`. One difference, recorded by review r2
(finding 1): in `measureReal_wealth_lt_le_of_condExp` and `measureReal_wealth_lt_le_of_condExp_of_le`
the binders `{μ}` and `[StandardBorelSpace Ω]` come in the other order, because `{μ}` is on
EdgeGrowth's file-level `variable` line; hypotheses, binder kinds and conclusion are identical, and
the draft statement is proved by the library theorem directly (review r2, `Stmt_r2.lean`, rc 0).

Mathlib searched first. Item 1 (`i1_search.sh`): `hoeffding` (files), `hasSubgaussianMGF_of_mem_Icc`,
`condExp` with `Real.exp` or `mgf`, `HasCondSubgaussianMGF`, `condExp.*le.*exp`: only
`Probability/Moments/SubGaussian.lean` (the two-sided lemma); no one-sided conditional form. Item 4
(`i4_search.sh`): "design effect", "effective sample", "participation ratio": 0 hits;
`variance_fun_sum` and `variance_mul_const` exist and are used.

Constant count, rule 27: a census of the four scratch files (`Census_Item*.lean`, theorem constants
of the file's own stage of the environment under the axiom gate's predicate, auxiliaries included)
gave 1 + 13 + 32 + 3 = 49, so 2106 + 49 = 2155 predicted; claude-ai-63's hand estimate was 2131 to
2181. The axiom gate on the mixed tree (every change built, nothing yet committed past item 1) gave
2155.

The vacuity gate: on that mixed tree it failed with a deterministic timeout at `isDefEq` (rc 1,
`g2-vacuity.out`). A probe outside the library (`VacuityProbe.lean`, the gate's test copied verbatim
and timed per theorem) measured `variance_average_eq` at 209673 heartbeats (thousands), over the
200000 default; the next largest were `LinearPrediction.variance_eq_steady` 102784 and
`FirstOrderRecursion.variance_succ` 102765. Each theorem's test runs in its own `liftTermElabM`,
whose `runCore` sets `initHeartbeats` afresh (Lean v4.34.0, `Lean/Elab/Command.lean`), so the budget
is per theorem. The gate now runs under `set_option maxHeartbeats 400000 in`, with the reason in a
comment. Fire test, rule from HANDOFF §0: green on the tree (`vac-green.out`, rc 0, PASS); a planted
`theorem vacuity_plant (h : (1 : ℝ) = 1) : (1 : ℝ) = 1 := h` in EffectiveSampleSize, built, gives
rc 1 naming only `vacuity_plant` (`vac-red.out`); the plant was removed, the module's sha256
(`09d46cb8…6a64`) is the one before planting, and the rebuild had 0 warnings.

This fragment is completed in the order's records commit: commits, cold reviews, the dropped
hypotheses, the clean-tree gates, the per-module counts, and the deviations.
