# Round 42 — how many returns are enough, and no ceiling for the long-run results (order LEAN-14)

Session: Claude Code `session_01Te3njNUi6rRPjDGR1gDBKE` on DSMain, as dustin, executing order
`LEAN-14` (`records/orders/20261008T172700Z__claude-ai__order-lean14-hoeffding-count.md`), in the
worktree `~/lean/classical-lean-paper-crypto` on branch `paper-crypto-9`. `paper-crypto-9` sits on
`paper-crypto-8`, which is LEAN-13's three commits applied on DSMain by `git am` of the lane patches
on `origin/master` = `04fcd97` (Step 0; `7b049f1`, `0963545`, `8300e74`). Lean and Mathlib v4.34.0.
Nothing was pushed. Records were written before the module change (`62fb83d`). Evidence:
`~/lean/lean14-checks/` (outside the repository), `evidence.log` (time, label, rc, prediction,
command per run). Dustin approved the plan in chat after Step 0.

Module changed: `ClassicalLean/Probability/EdgeGrowth.lean` (no new module). Two counts: theorems
written (`theorem` and `lemma` lines) 12 → 18; theorem constants under the axiom gate's predicate
(`.thmInfo`, user name under `ClassicalLean`, per module by `env.getModuleFor?`, generated constants
included) 13 → 28. New import `Mathlib.Probability.Moments.SubGaussian`.

* Item 1, `measureReal_wealth_lt_le`: under LEAN-13's setting for (b) (returns measurable,
  `iIndepFun`, identically distributed, `-c ≤ X n ≤ C`, `0 < c`, a constant stake `0 ≤ l < 1/c`), for
  every `N` and `L ≤ N · growth`, `μ.real {wealth N < exp L} ≤ exp (-2 (N g - L)² / (N (log (1 + l C)
  - log (1 - l c))²))`. Route: Mathlib's Hoeffding lemma (`hasSubgaussianMGF_of_mem_Icc`) on each
  centred, negated log factor, independence by `iIndepFun.comp` and `iIndepFun.precomp` with
  `(· + 1)`, then `HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun`. Statement copied from the
  order's `LEAN-14-statements.lean`.
* Item 4, without the ceiling: `exists_growth_pos_of_floor` (dominated convergence with
  `l_k = 1/(2c(k+1))`), `tendsto_log_wealth_div_of_floor` (integrability of `log (1 + l X 0)` in place
  of `C`), `tendsto_wealth_atTop_of_floor`, `exists_stake_measureReal_reach_eq_one_of_floor`; helper
  `div_one_add_le_log_le`. The old four theorems stay; the docstrings say the new ones generalise them.
* Item 3: the module docstring's five edits (i)–(v) as the order lists them.

Departures from the order's statements, both making theorems more general: (a2), (b2) and (c2) do
not assume a probability measure (Mathlib's `strong_law_ae_real` takes any measure; the linter flagged
the unused section instance for (b2) and (c2); the review found (a2)'s binder unused too); (d2) keeps
it. (b2)'s unused measurability hypothesis is named `_hXm`. Checked: a copy of the order's
`LEAN-14-statements.lean` with each `sorry` replaced by `exact` of the library theorem elaborates
(rc 0, no errors, no `sorry`); a planted `-3` in place of `-2` fails (rc 1, type mismatch).

Mathlib searched first (`~/lean/lean14-checks/i1_search.sh`): `hoeffding` (case-insensitive),
`measure_sum_range_ge_le`, `measure_sum_ge_le`, and files naming both `HasSubgaussianMGF` and a
product. Hits only in `Probability/Moments/SubGaussian.lean` (Hoeffding's lemma and inequality for
sums); no statement about a product such as the wealth.

Dropped hypotheses of item 1, in Lean outside the library (`~/lean/lean14-checks/Dropped.lean`, lane
copy `LEAN-14-dropped.lean`): independence (H2: two points, every return a copy of the first,
`c = 1/2`, `C = 1`, `l = 1/2`, `N = 400`, target 2) and identical distribution (H3: one point,
`X 0 = 1`, `X n = 2^-n`, `c = C = 1`, `l = 1/2`, `N = 20`, target 3); each keeps every other
hypothesis and `L ≤ N g`, and the file proves each contradicts `measureReal_wealth_lt_le` once its
hypothesis is put back (two `example`s from the cold review). Elaborates rc 0 with no messages;
plants (H2 at `N = 60`; H3 with `X n = 1`) give rc 1. The ceiling, the floor, `l < 1/c` and `0 ≤ l`:
the order's check script, cases H4 to H7. `0 < c`: implied by `0 ≤ l < 1/c`. Measurability: not shown
needed, kept for convenience. Item 4's integrability and floor rows: report only.

Cold review (rule 13): one fresh-context subagent over the diff and `Dropped.lean`, saved verbatim at
`~/lean/lean14-checks/review/review-1.md`: PASS WITH FINDINGS, 1 MAJOR (the claim that the bound
shrinks once `N · growth` passes `L` is false for `L < 0`; fixed in both docstrings) and 7 MINOR
(findings 2–6 fixed: (a2)'s unused probability binder, `B` written out, "not proved separately",
`div_one_add_le_log_le` weakened to `-1 < t`, (c2)'s docstring; finding 7, the docstring's "Each
hypothesis is needed", left for the next order because item 3 says nothing else changes; finding 8,
fragile steps, note only). Delta check of the fixes (rule 29), same reviewer, saved at
`~/lean/lean14-checks/review/review-2-delta.md`: DELTA PASS, no new findings. The reviewer wrote a
memory note under `~/.claude/agent-memory/` in its first pass, outside its brief's scratch limit
(rule 12); nothing in either repository.

Gates on the working tree holding exactly this round's change: `lake build` rc 0, 0 warnings (and 0
for `lake build ClassicalLean.Probability.EdgeGrowth`); axiom gate PASS, 2106 (2091 at
`paper-crypto-8`, +15; predicted by the rule-27 census, 2106; hand prediction 2103–2121); vacuity
gate PASS; check_sorry PASS (79 files); banned_vocab_scan PASS (79 files, 0 hits); check_records
PASS (79 modules). `#print axioms` on the five new theorems: `[propext, Classical.choice,
Quot.sound]`. Re-run on the clean tree after the commit; see the LEAN-14 report.

Commits: records first `62fb83d`; module and this fragment `55a6a8f`. On the clean tree at `55a6a8f`:
`lake build` rc 0, 0 warnings (0 also for `lake build ClassicalLean.Probability.EdgeGrowth`); axiom
gate PASS, 2106; vacuity gate PASS; check_sorry PASS (79 files); banned_vocab_scan PASS (0 hits);
check_records PASS (79 modules). Program (`~/trading/paper`, master): plan `fde77e6`, code `e0c80e2`,
run `441df64`.
