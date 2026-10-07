# Round 34 — proportional deductions and the log-optimal fraction (order LEAN-6, part B)

Session: Claude Code `session_01KyYusMNSHJap88c9A6s6K2` on DSMain, as dustin, executing order
`LEAN-6` (`records/orders/20261007T203000Z__claude-ai__order-lean6-paper-crypto.md`), on branch
`paper-crypto` in the worktree `~/lean/classical-lean-paper-crypto`, from `master` at `333b69a`.
Lean and Mathlib v4.34.0. Nothing was pushed.

Modules added: `ClassicalLean/Analysis/LogGrowthRate.lean` (new top-level directory `Analysis/`).
`ClassicalLean.lean` gains its import line.

## What is proved

- `lt_afterTwoDeductions_iff`: for `0 < W`, `0 < a`, the amount after exchanging at rate `a` and
  back at rate `c`, losing the fraction `f` each way, exceeds `W` exactly when
  `a < c * (1 - f) ^ 2`. The equivalence needs no condition on `f`.
- `logGrowth_le_optimalFraction`: for `0 < p < 1`, `0 < b`, `0 ≤ x < 1`,
  `p log(1 + b x) + (1 - p) log(1 - x)` is at most its value at `p - (1 - p) / b`.
  `optimalFraction_mem_Ico` says that point lies in `[0, 1)` when `1 - p ≤ p b`.
- `exists_logGrowth_pos_iff`: some `x` in `[0, 1)` gives positive value exactly when
  `1 - p < p b`. `logGrowth_optimalFraction_pos`: the value at the optimum is then positive.
- `repeatedDecrease_eq`: removing the fraction `x` of what is left, `n` times, leaves
  `W (1 - x) ^ n`.

The definitions are over any field, so they evaluate exactly on `ℚ`. Three `example`s check them on
exact numbers: one value was first typed wrong by hand, Lean rejected it, and the value is now
computed with `fractions`. Before any statement was written, the three claims were checked in
Python with exact fractions and 50-digit logs: 2100, 32 and 116 cases, 0 disagreements.

Mathlib v4.34.0 has none of the three under any name: `Kelly` occurs only in category-theory
citations, and there is no break-even lemma. It supplies `Real.log_le_sub_one_of_pos` and
`Real.log_lt_sub_one_of_pos`, which the proofs use.

## Gates and counts

- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for the five inequality
  theorems, and `[propext, Quot.sound]` for `repeatedDecrease_eq`.
- The axiom gate counts 1689, with 0 scoped exceptions.
- Per-module theorem-constant count (`env.getModuleFor?` under the axiom gate's predicate):
  `Analysis/LogGrowthRate` **27**; total 1689, against 1662 at `333b69a`.
- `lake build`: 0 warnings after two long lines were split. Vacuity, check_sorry and banned_vocab
  pass. Gate 6 failed (UNRECORDED) until this fragment.
