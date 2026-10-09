# Round 50 — recursive least squares, the converse of Kraft's inequality, the scalar Kalman filter's error variance, Doob's L² inequality, gambler's ruin, and Galton–Watson extinction (order LEAN-22)

Session: Claude Code `session_015uyBADuYuNNAwLUWbUvxWF` on DSMain, as dustin, executing order
`LEAN-22` (`records/orders/20261009T161700Z__claude-code__order-lean22-least-squares-kraft-kalman-doob-ruin-extinction.md`),
batch 6 of the plan `/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md` (sha256
5c2381ba371a3b810dbc39302c724ff7d2279fca9d9870d354f269ae6f048fc0), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `paper-crypto-17`, made from `origin/master` =
`5c25955`. Lean and Mathlib v4.34.0. Nothing pushed. Evidence: `~/lean/lean22-checks/` (outside the
repository), `evidence.log` (time, label, rc, prediction, command per run).

First part written before any module change, so that gate 6 finds the new modules' paths before
their commits; completed after the work, below. Item numbers are the plan's: item 42 is the Kalman
filter's variance, item 45 Galton–Watson extinction.

Modules this round plans to change or add (as the claim row):

* `ClassicalLean/Statistics/GaussMarkov.lean` — item 40 (recursive least squares).
* `ClassicalLean/InformationTheory/SourceCoding.lean` — item 41 (the converse of Kraft's inequality).
* `ClassicalLean/Probability/KalmanVariance.lean` — new module, item 42; added to `ClassicalLean.lean`.
* `ClassicalLean/Probability/MaximalInequality.lean` — item 43 (Doob's `L²` inequality).
* `ClassicalLean/Probability/GamblersRuin.lean` — new module, item 44; added to `ClassicalLean.lean`.
* `ClassicalLean/Probability/Extinction.lean` — new module, item 45; added to `ClassicalLean.lean`.
* `ClassicalLean/InformationTheory/Channel.lean` — module docstring only: the `klDiv` bridge is
  proved (order LEAN-21, item 39), no longer future work. `HANDOFF.md` §3 likewise.

Mathlib re-checked before the records were written (`~/lean/lean22-checks/search.out`,
`search2.out`): none of the six items is in Mathlib v4.34.0, so none is dropped. Statements
elaborated with `sorry` before this fragment: `st2.out`, rc 0, 24 `sorry` warnings, nothing else
(`st1` had 3 lint warnings besides; fixed). The exact checks behind the needed-hypothesis table:
`checks.py`, `chk1.out`, ALL OK.

## Completed after the work

All six items of batch 6 are done (40 to 45), with the plan's numbering (item 42 the Kalman
filter's variance, item 45 Galton–Watson); the order's own text had listed 42 and 45 the other way
round in one sentence, and a correction during the work confirmed the plan's numbering. Citations
of works nobody here read are author, title and year only: Kalman 1960, Watson and Galton 1875,
Doob 1953, and Acciaio, Beiglböck, Penkner, Schachermayer and Temme 2013.

Commits on `paper-crypto-17` (made from `origin/master` = `5c25955`; nothing pushed):

* `bb22128` records before the work (this fragment's first part).
* `844e418` `ClassicalLean/Statistics/GaussMarkov.lean`, item 40.
* `599971f` `ClassicalLean/Probability/KalmanVariance.lean`, item 42 (new module).
* `5f72561` `ClassicalLean/InformationTheory/SourceCoding.lean`, item 41.
* `bad6f75` `ClassicalLean/Probability/MaximalInequality.lean`, item 43.
* `83acac5` `ClassicalLean/Probability/Extinction.lean`, item 45 (new module).
* `3fdbd48` `ClassicalLean/InformationTheory/Channel.lean` (module docstring only) and `HANDOFF.md`
  §3: the `klDiv` bridge is proved (order LEAN-21, item 39), no longer future work.
* `662e700` `ClassicalLean/Probability/GamblersRuin.lean`, item 44 (new module).

Changes from the drafted statements (`~/lean/lean22-checks/Statements.lean`, `st2.out`): item 40,
`one_add_dotProduct_inv_mulVec_pos` lost its hypothesis (it holds on the junk inverse too); item
41, `exists_isPrefixFree_sum_mul_length_lt` lost `[Nonempty α]` (review r41); item 42,
`riccati_equation` renamed `riccati_equation_riccatiRoot` and `riccati_rate_lt_one` became
`riccatiRate_lt_one` about a new definition `riccatiRate` (review r42); item 43, the path-by-path
inequality is stated with a new definition `runningMaxAbs` (`runningMaxAbs_sq_add_four_mul_sum_le`),
and `integral_sup_sq_le` needs no finite measure, only a filtration σ-finite at each time (review
r43); item 45, the module's names live in `ClassicalLean.Probability.Extinction` (review r45).
Added beyond the drafts: `transpose_mulVec_appendRow`, `not_forall_leastSquares_append_row`
(review r40), `riccatiStep_pos`, `riccatiRate_nonneg`, `abs_riccatiStep_sub_le`,
`runningMaxAbs_nonneg`, `abs_le_runningMaxAbs`, `integrable_sup_sq` (review r43), the `pgf`
lemmas (`summable_pgf`, `pgf_one`, `pgf_zero`, `pgf_mono`, `pgf_mem_Icc`, `continuousOn_pgf`,
`iterate_zero_mem_Icc`, `iterate_zero_le`), the walk lemmas (`walk_zero`, `walk_succ`,
`exists_int_walk`, `abs_walk_le`, `walk_mem_Icc_of_le_exitTime`, `isStoppingTime_exitTime`,
`stoppedValue_min_mem_Icc`, `integral_stoppedValue_walk`, `integral_stoppedValue_walk_sq`),
`add_mul_measureReal_hit_eq` and `integrable_exitTime` (review r44), and private helpers.
Routes that differ from the plan's rows: item 40's estimate update comes from the normal
equations (Woodbury gives the inverse update); item 42 is a contraction, not a monotone limit;
item 43 takes means of a path-by-path inequality instead of `maximal_ineq` and the layer cake.

Cold reviews, one per module before its commit, each by a fresh general-purpose subagent with no
persistent memory, in its own scratch folder (`~/lean/lean22-checks/reviews/`); all six PASS WITH
FINDINGS, no BLOCKER. MAJOR findings: r42 (a float count in the docstring had no seeded search
behind it; one was added to the checks and its output quoted) and r45 (a wrong sentence about
where Mathlib says "generating function"); both applied. MINOR: r40 4, r41 2, r42 6, r43 7, r44 7,
r45 4; all applied except r40's renaming of `leastSquares_append_row` (the order fixes the name).
Hashes (sha256, first 16 hex digits):

| review | brief sha256 | review sha256 |
|---|---|---|
| r40 | `acd1574d5c3cb912` | `10f701e337f70cfd` |
| r41 | `04930285425aa394` | `1f07d77ca5d94752` |
| r42 | `dd069636f8a955d8` | `9f0e9db5419a5354` |
| r43 | `2f6fccbc0db9a525` | `cab060afb0f3fbce` |
| r44 | `aca0c656426ed9b3` | `d472f3fcde14f936` |
| r45 | `a9ddc99be3518ab5` | `2f1e77e3460ac115` |

`~/.claude/agent-memory/`: the sha256 of every file (58) was the same before the first review and
after the last.

Gates on the clean tree at `662e700` (`~/lean/lean22-checks/g1-*.out`): `nice -n 19 lake build`
rc 0, 4076 jobs, 0 warning lines; AxiomGate PASS, 2640 theorem constants; VacuityGate PASS;
check_sorry PASS, 105 files; banned_vocab_scan PASS, 105 files; check_records PASS, 105 modules.
The needed-hypothesis checks (`checks.py`, sha256 `a6595777140e4b38`; output `chk4.out`, ALL OK)
fail with rc 1 on a copy with one planted failure, naming only the plant (`fire-checks.out`).

Theorem constants per module, measured with `env.getModuleIdxFor?` under the `.thmInfo`
predicate on the built library (`census/envnames.out`): GaussMarkov 39, SourceCoding 12,
MaximalInequality 23, Channel 5, KalmanVariance 20, Extinction 20, GamblersRuin 51.

Theorem constants: 2640 against 2516, so 124 new. Predicted before any gate (`prediction.txt`,
sha256 `90584def998cb51d`): by compiling scratch copies of each changed module, old and new, with a
census written for this order (Method B): 2640, a hit; the built library's 170 theorem constants
in the seven modules equal the census's, name by name. From the source alone (Method A): 81
hand-written theorems (a hit) plus a modelled 28 helpers, 2625: a miss by 15, all in the helpers:
27 `_simp_` (modelled 12; from `field_simp` and `simp only` in KalmanVariance, GamblersRuin,
GaussMarkov and SourceCoding), 0 `congr_simp` (modelled 2), 6 `_proof_` (modelled 4: four from
`omega`, two inside `riccatiRoot`), 10 equation lemmas (modelled 10, but with `runningMaxAbs`
giving 5 and `riccatiRoot`, `riccatiRate` none).

Gate 7, `~/lean/recheck/run-recheck.sh 662e700 ~/lean/classical-lean-paper-crypto`: rc 0, last line
`ALL PASSED for 662e700a728be9c520cd7f6645c51f590491b70a` (`g7a-recheck.out`): 4076 jobs;
leanchecker 105 modules, 0 failed; nanoda checked 88639 declarations with no errors, only the
three standard axioms; 2640 theorems under the ClassicalLean name, counted from the export (equal
to AxiomGate); the planted wrong proof was rejected and named
(`ClassicalLean.Analysis.LogDrag.mean_log_one_add_le`). Predicted before the run: rc 0, 4076
jobs, 105 modules, 2640, 89000 to 92000 declarations: all hit except the declarations (88639, a
miss below the range; LEAN-21 had 88315).

Not touched: anything under `~/trading`; nothing under `~/lean/recheck` was edited (its script was
run). No push.
