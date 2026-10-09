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

## Completed in the records commit

Commits on `paper-crypto-10`, on `25cf9bb`: `b5bb93d` (records first), `d257a0e` (item 1),
`b36ef60` (items 2, 3, 6), `1dada51` (the vacuity gate's budget), `a749de0` (item 4, ROADMAP §1.16,
this fragment's first part), `8b18485` (item 5), and the records commit that adds this section. In
`~/trading/paper` on `master`, on `441df64`: `a54a8c4` (item 7's plan), `b633965` (its code, not yet
run), `9e9e967` (the run and `results/lean15-dependence.md`).

Gates on the clean tree at `8b18485` (`g4-*.out`): `lake build` rc 0, nothing compiled, 0 warning
lines; AxiomGate PASS, 2155 theorem constants, 0 scoped exceptions; VacuityGate PASS; check_sorry
PASS, 80 files; banned_vocab_scan PASS, 80 files and `ClassicalLean.lean`, 0 hits; check_records
PASS, 80 modules, 50 records files, 1 exemption. `#print axioms` on the 13 new main theorems: each
`[propext, Classical.choice, Quot.sound]` (`axioms.out`). Theorem constants per module, by
`env.getModuleFor?` under the gate's predicate (`census-final.out`): DependentSampleMean 19 (+1),
EdgeGrowth 41 (28 → 41, +13), EffectiveSampleSize 32 (new), EValueStepUp 20 (+3); +49 in all,
2106 → 2155, equal to the scratch census's prediction.

Cold reviews (rule 13), each by a fresh general-purpose subagent working in a scratch directory under
`~/lean/lean15-checks/review/`, its brief built by script with HANDOFF rules 12 to 25 quoted
(`make_brief.py`), its report saved by the reviewer and its sha256 checked against the hash the
reviewer returned (rules 17, 26, 33):
- r1, item 1 (`review-r1.md`, 0159386c…7652): PASS WITH FINDINGS, 1 MAJOR (the docstring claimed a
  tail frequency), 4 MINOR; all five applied before `d257a0e`; delta-checked in r2 (rule 29: PASS).
- r2, items 2, 3, 6 and `Dropped.lean` (`review-r2.md`, e46a71ad…7e3a): PASS WITH FINDINGS, 7 MINOR;
  2 to 6 applied (wording "smallest" → "sufficient", unused names, a redundant `omit`); 1 recorded
  above; 7 (a more general helper) not taken. The changed proof lines are identical to the reviewer's
  elaborated copy (`r2-delta.out`: `diff` rc 1, only docstring lines and the reviewer's own `#check`
  lines differ).
- r3, items 4, 5 and ROADMAP §1.16 (`review-r3.md`, 20320ec1…b40d): PASS WITH FINDINGS, 8 MINOR;
  1 to 6 and 8 applied (docstring-only); 7 (`IsFiniteMeasure` would do for EffectiveSampleSize) is a
  follow-up, since the order fixes the statements.
No reviewer wrote under `~/.claude/agent-memory/` (`find -newer` the first brief: nothing). Two
reviewers ran Python on standard input against their brief: r1 once without `-I` (a script that
edited its own scratch file), r3 once with an empty program; neither wrote outside its scratch
directory. This session also ran two empty `python3 -` commands by mistake (no program, no effect).

Dropped hypotheses: the full table is in the lane report `LEAN-15-report.md`. In Lean, outside the
library (`~/lean/lean15-checks/Dropped.lean`, lane copy `LEAN-15-dropped.lean`): item 2's
"conditional mean at least `g`" (one point, the order's numbers) and "returns adapted" (LEAN-14's H2
with the trivial filtration; LEAN-14's arithmetic carried over directly, so it is in Lean, not only
Python), each with an `example` that puts the hypothesis back and derives `False` from the library
theorem; rc 0, no messages; the planted control (target `exp (-1/2)`) rc 1. Every other row cites
the check script (lines C1 to C6) or LEAN-14's rows.

Timeline (rule 18): items 2 and 3 were proved in scratch while review r1 of item 1 ran (00:12–00:15
UTC); items 4 and 5 were drafted and moved into the tree while review r2 ran (00:21–00:28), as r2
recorded; item 7's plan and code were written while r3 ran (00:25–00:32). No statement under review
was changed while its review ran. The census runs marked rc 1 in `evidence.log` (00:29:45 to
00:30:31) were errors in my census script, fixed before the counted runs.
