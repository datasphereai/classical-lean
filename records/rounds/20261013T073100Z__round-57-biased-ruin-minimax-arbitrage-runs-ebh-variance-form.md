# Round 57 — the biased walk, minimax for every matrix, arbitrage counterexamples, runs, e-BH for compression scores, the variance product form (order LEAN-28)

Session: Claude Code `session_01CJNTgEfU5v3FmgQzLoqchA` on DSMain, as dustin, executing order
`LEAN-28` (`records/orders/20261013T073000Z__claude-ai__order-lean28-biased-ruin-minimax-arbitrage-runs-ebh-variance-form.md`),
batch 2 (items 84 to 88) of the plan `/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library-2.md`
(sha256 6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166), and item 80b (the product form of item 80, which
LEAN-27 left unstated), in the worktree `~/lean/classical-lean-paper-crypto` on branch `lean-28`, made
from `origin/master` = `deb08cb` (equal to `git ls-remote github master`). Lean and Mathlib v4.34.0.
Nothing pushed. Evidence: `~/lean/lean28-checks/` (outside the repository), `evidence.log` (time,
label, rc, prediction, command per run).

First part written before any Lean file changed; completed after the work, below.

## Modules this round changes (no new module)

* item 84: `ClassicalLean/Probability/GamblersRuin.lean` (extended; gains an import of
  `ClassicalLean.Probability.MaximalInequality`);
* item 85: `ClassicalLean/Analysis/FiniteGame.lean` (extended);
* item 86: `ClassicalLean/Combinatorics/ArbitrageCycle.lean` (extended: three `example`s);
* item 87: `ClassicalLean/Probability/LongestRun.lean` (the measurability hypothesis of
  `measureReal_no_run_le`: dropped, or the module says why it stays);
* item 88: `ClassicalLean/InformationTheory/CompressionTest.lean` (extended; gains an import of
  `ClassicalLean.Probability.EValueStepUp`);
* item 80b: `ClassicalLean/Probability/EffectiveSampleSize.lean` (extended: the product form
  `variance_sum_eq_mul_one_add`, with the hypotheses of `variance_sum_eq_of_stationary` only);
* `ClassicalLean.lean`: no change expected (no new module).

The vacuity gate is used as LEAN-27 left it (no change to `tools/` except a possible
`tools/vacuity_reviewed.txt` entry). Standing rule 2 of round 55 (the bridge search) applies.

## Completed after the work

(to be written after the work)
