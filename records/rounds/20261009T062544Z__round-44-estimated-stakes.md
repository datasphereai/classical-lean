# Round 44 — the stake when the edge is only estimated, a count from the spread, what a signal is worth with cash, and a mixture of fixed stakes (order LEAN-16)

Session: Claude Code `session_01CAgquuMxBPCgwwHySSAPvP` on DSMain, as dustin, executing order
`LEAN-16` (`records/orders/20261009T061600Z__claude-ai__order-lean16-estimated-stakes.md`), in the
worktree `~/lean/classical-lean-paper-crypto` on branch `paper-crypto-11`, made from `origin/master` =
`3f910db`. Lean and Mathlib v4.34.0. Nothing pushed. Evidence: `~/lean/lean16-checks/` (outside the
repository), `evidence.log` (time, label, rc, prediction, command per run).

First part written before any module change (`1e3a71b`), so that gate 6 found the new module's path
before the module's commit (LEAN-15-CLOSE.md, trap 5); completed after the work, below. Dustin
approved the plan in chat after Step 0.

Modules this round plans to change or add (as the claim row):

* `ClassicalLean/Analysis/GeneralGrowth.lean` — item 1.
* `ClassicalLean/Analysis/LogGrowthRobustness.lean` — item 2.
* `ClassicalLean/Probability/EdgeGrowth.lean` — items 3 and 4.
* `ClassicalLean/InformationTheory/SignalGrowth.lean` — item 5.
* `ClassicalLean/Analysis/UniversalMixture.lean` — new module, item 6; added to `ClassicalLean.lean`.
* `ClassicalLean/Probability/EffectiveSampleSize.lean` — item 7.
* `ROADMAP.md` §1 (the online-learning bridge) and §1.16 (the combinatorics bridge, proved).

## Completed after the work

Commits on `paper-crypto-11`, in order: `1e3a71b` (records, before the work), `3ad554c`
(GeneralGrowth, item 1), `770863a` (LogGrowthRobustness, item 2), `3bb8b26` (EdgeGrowth, items 3
and 4, and item 7's second follow-up), `229e2e5` (SignalGrowth, item 5), `6248d27`
(UniversalMixture, `ClassicalLean.lean` and ROADMAP.md §1.17, item 6), `d32168a`
(EffectiveSampleSize and ROADMAP.md §1.16, item 7), then the records commit that completes this
fragment (its hash is in the order's report, not here).

Declarations. Item 1: `log_one_add_ge`, `log_one_add_le`, `growth_mem_Icc`, `growth_neg_of_lt`, helpers
`sum_mul_sub_sq_div` and `growth_le_sub_sq_div`. Item 2: `mul_log_one_add_le`, `mul_sum_log_le`.
Items 3 and 4: `integral_exp_mul_sum_le_pow` (the helper with any per-step constant;
`integral_exp_mul_sum_le` keeps its statement and is derived from it), `condExp_const_add_mul_add_mul`,
`condExp_log_one_add_mul_ge`, `measureReal_sum_lt_le_of_condSq`, `measureReal_wealth_lt_le_of_moments`.
Item 5: `factor`, `colGrowth`, `colGrowthWith`, `colGrowthWith_le`, `sum_mul_div_le_one_of_best`,
`colGrowthWith_le_of_best`. Item 6: `mixStake`, `sum_prod_div_card_eq_prod_mixStake`, `mixStake_mem_Icc`,
`log_prod_sub_log_card_le`, `abs_log_one_add_mul_sub_le`, `le_log_mixture`. Item 7: `sum_sum_pow_succ`,
`sum_pow_sub_succ`, `sumSumPowRec`, `isSolution_sumSumPow`, `recDenom_mul_mk_sumSumPow`; the module's
`[IsProbabilityMeasure μ]` became `[IsFiniteMeasure μ]`.

Statements: copied from the order's `LEAN-16-statements.lean`. One difference, recorded by review r3:
`condExp_log_one_add_mul_ge` writes `Measurable[m0] X`, and its implicit `m` comes after the file's
`m0` and `μ`; review r3 checked in Lean that the hypothesis is the statements file's `Measurable X`
and that the two statements imply each other. Route changes: item 5's `colGrowthWith_le` is proved
cell by cell with `log t ≤ t - 1` instead of Jensen per signal, and does not need `∑ P = 1`.

Mathlib searched first (`search-all.out`): quadratic bounds on `log (1 + u)` (none found; Mathlib has
`Real.log_le_sub_one_of_pos` and series); "Bernstein inequality", "Bennett", "Freedman", "mutual
information", "side information", "Barron", "universal portfolio", "regret": no file. Reused:
`Real.abs_exp_sub_one_sub_id_le`, `measure_ge_le_exp_mul_mgf`, `condExp_mono`, `condExp_add`,
`condExp_sub`, `condExp_smul`, `condExp_const`, `Finset.sum_pos_iff_of_nonneg`,
`strictConcaveOn_log_Ioi`, `monotoneOn_of_deriv_nonneg`, `antitoneOn_of_deriv_nonpos`.

Per-module theorem constants at `d32168a` (`env.getModuleFor?` under the axiom gate's `.thmInfo`
predicate, `Count.lean`): GeneralGrowth 16, LogGrowthRobustness 20, EdgeGrowth 46, SignalGrowth 20,
UniversalMixture 12, EffectiveSampleSize 39. The library total went from 2155 (order LEAN-15's
close) to 2205. That total was measured by the gates before any census was run, so the census is a
cross-check, not the prediction order LEAN-16 asked for (rule 27; a miss, recorded in the report).

Gates on the **clean** tree at `d32168a` (`gates.sh g3`, every rc 0): `lake build` "Build completed
successfully (4011 jobs)." with 0 warning lines; "axiom gate PASS — 2205 theorem constant(s) under
[ClassicalLean]"; "vacuity gate PASS — no vacuous theorems in [ClassicalLean]"; "check_sorry PASS — 81
file(s) under ClassicalLean"; "banned_vocab_scan PASS — 81 file(s) under ClassicalLean +
ClassicalLean.lean, 0 hits"; "check_records PASS — 81 module(s) under ClassicalLean". check_sorry was
fire-tested on a planted `sorry` in a scratch copy outside the repository: rc 1, "check_sorry FAIL — 1
violation(s) across 81 file(s)". The vacuity gate's budget was not changed (400000).

Cold reviews (rule 13), each by a fresh general-purpose subagent in its own scratch folder, brief
built by `make_brief.py` with HANDOFF rules 12 to 25 quoted: r1 GeneralGrowth (0e3de216…1d05d24a),
r2 LogGrowthRobustness (89e78a4d…174cf2b7), r3 EdgeGrowth (5f77a4db…ed068ba9), r4
SignalGrowth (cd72757f…3a5da7c9), r5 UniversalMixture (caa73c79…30f5420a), r6
EffectiveSampleSize (d7edd75b…bd22cb13). All six: PASS WITH FINDINGS, no BLOCKER; MAJOR
findings, all in docstrings or ROADMAP prose and all fixed: r3 (a sentence false when `N g < L`), r5
("within" for a one-sided bound), r6 (§1.16's "island" sentence). Findings not applied are listed in
each module's commit message. `~/.claude/agent-memory/` gained no file during the reviews.

Dropped hypotheses: the order's file `LEAN-16-dropped.lean` (item 4's conditional mean and the second
theorem's `h1`, one point, filtration `⊤`; rc 0, and its planted control rc 1); every other row is
cited from the order's check script, lines C1 to C6, rerun on DSMain with output identical to the lane
copy. The table is in the order's report.
