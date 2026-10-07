/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Init
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Jacobsthal numbers

The Jacobsthal numbers `J 0 = 0`, `J 1 = 1`, `J (n + 2) = J (n + 1) + 2 * J n` are the sequence
`0, 1, 1, 3, 5, 11, 21, 43, 85, 171, 341, …` (OEIS A001045).  Their companion sequence
`j 0 = 2`, `j 1 = 1`, obeying the same recurrence, is `2, 1, 5, 7, 17, 31, 65, …`
(OEIS A014551).

Mathlib has neither sequence; both are defined here.

## Main definitions

* `ClassicalLean.jacobsthal` — the Jacobsthal numbers `J`.
* `ClassicalLean.jacobsthalCompanion` — the companion sequence `j`.

## Main results

The closed forms are proved, not merely spot-checked:

* `three_mul_jacobsthal` : `3 * J n = 2 ^ n - (-1) ^ n` over `ℤ`.
* `jacobsthalCompanion_eq` : `j n = 2 ^ n + (-1) ^ n` over `ℤ`.

Their `ℕ`-valued shadows, split by the parity of `n`, are
`three_mul_jacobsthal_add_one_of_even` (`3 * J n + 1 = 2 ^ n`) and
`three_mul_jacobsthal_of_odd` (`3 * J n = 2 ^ n + 1`); the same split for `j` is
`jacobsthalCompanion_add_one_of_odd` and `jacobsthalCompanion_of_even`.

* `jacobsthal_mul_jacobsthalCompanion` : `J n * j n = J (2 * n)`, the doubling identity, an
  immediate consequence of the two closed forms.
* `jacobsthal_succ_pos`, `jacobsthalCompanion_pos` : positivity.

## Source

Ported from a `jacobsthal` module holding five theorems.  `jacobsthal_zero`,
`jacobsthal_one` and `jacobsthal_add_two` are shipped unchanged; `jacobsthal_pos_of_pos`
(`n ≥ 1 → jacobsthal n > 0`) is `jacobsthal_succ_pos`, the same statement reindexed.  The
fifth, `jacobsthal_two` (`jacobsthal 2 = 1`), is **not** shipped as a theorem: it is a single
concrete value, and this library states concrete-number checks as `example`s — the round-1
modules contain no literal-value theorem either — so it appears among the computed examples
at the end of this file.  That is a demotion of a source theorem, recorded here rather than
left silent.

The source states the closed form only as eleven spot-checks at indices between `0` and
`15`, each discharged by compiled evaluation — the tactic this library bans, and the reason
the source's version rests on the compiler rather than the kernel.  `three_mul_jacobsthal`
proves the closed form for all `n` instead, by induction.  The companion
sequence, its closed form, the four parity corollaries and the doubling identity have no
counterpart in the source.
-/

namespace ClassicalLean

/-! ### The two sequences -/

/-- The Jacobsthal numbers: `J 0 = 0`, `J 1 = 1`, `J (n + 2) = J (n + 1) + 2 * J n`. -/
def jacobsthal : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => jacobsthal (n + 1) + 2 * jacobsthal n

/-- `J 0 = 0`, the first clause of the definition.  It holds by `rfl` and carries no content
beyond the `def`; it is stated only so that `simp` can use it. -/
@[simp] theorem jacobsthal_zero : jacobsthal 0 = 0 := rfl

/-- `J 1 = 1`, the second clause of the definition.  As with `jacobsthal_zero`, it holds by
`rfl` and adds nothing to the `def`. -/
@[simp] theorem jacobsthal_one : jacobsthal 1 = 1 := rfl

/-- The Jacobsthal recurrence `J (n + 2) = J (n + 1) + 2 * J n`.

This is the third clause of the definition and holds by `rfl`; it is a restatement of the
`def`, not a derived identity. -/
theorem jacobsthal_add_two (n : ℕ) :
    jacobsthal (n + 2) = jacobsthal (n + 1) + 2 * jacobsthal n := rfl

/-- The Jacobsthal companion sequence: `j 0 = 2`, `j 1 = 1`, and the same recurrence
`j (n + 2) = j (n + 1) + 2 * j n`. -/
def jacobsthalCompanion : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => jacobsthalCompanion (n + 1) + 2 * jacobsthalCompanion n

/-- `j 0 = 2`, the first clause of the definition, by `rfl`.  No content beyond the `def`. -/
@[simp] theorem jacobsthalCompanion_zero : jacobsthalCompanion 0 = 2 := rfl

/-- `j 1 = 1`, the second clause of the definition, by `rfl`.  No content beyond the
`def`. -/
@[simp] theorem jacobsthalCompanion_one : jacobsthalCompanion 1 = 1 := rfl

/-- The companion recurrence `j (n + 2) = j (n + 1) + 2 * j n`.

This is the third clause of the definition and holds by `rfl`; it is a restatement of the
`def`, not a derived identity. -/
theorem jacobsthalCompanion_add_two (n : ℕ) :
    jacobsthalCompanion (n + 2) = jacobsthalCompanion (n + 1) + 2 * jacobsthalCompanion n := rfl

/-! ### Positivity -/

/-- Every Jacobsthal number after the first is positive. -/
theorem jacobsthal_succ_pos (n : ℕ) : 0 < jacobsthal (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k _ ih2 =>
    rw [show k + 1 + 1 = k + 2 from rfl, jacobsthal_add_two]
    omega

/-- Every companion Jacobsthal number is positive. -/
theorem jacobsthalCompanion_pos (n : ℕ) : 0 < jacobsthalCompanion n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k ih1 ih2 =>
    rw [jacobsthalCompanion_add_two]
    omega

/-! ### Closed forms -/

/-- The Jacobsthal closed form, in the subtraction-free shape `3 * J n = 2 ^ n - (-1) ^ n`
over `ℤ`.  Equivalently `J n = (2 ^ n - (-1) ^ n) / 3`, but the multiplied form needs no
division. -/
theorem three_mul_jacobsthal (n : ℕ) :
    3 * (jacobsthal n : ℤ) = 2 ^ n - (-1) ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more k ih1 ih2 =>
    rw [jacobsthal_add_two]
    push_cast
    linear_combination ih2 + 2 * ih1

/-- The companion closed form `j n = 2 ^ n + (-1) ^ n` over `ℤ`. -/
theorem jacobsthalCompanion_eq (n : ℕ) :
    (jacobsthalCompanion n : ℤ) = 2 ^ n + (-1) ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more k ih1 ih2 =>
    rw [jacobsthalCompanion_add_two]
    push_cast
    linear_combination ih2 + 2 * ih1

/-- For even `n`, `3 * J n + 1 = 2 ^ n` in `ℕ`. -/
theorem three_mul_jacobsthal_add_one_of_even {n : ℕ} (hn : Even n) :
    3 * jacobsthal n + 1 = 2 ^ n := by
  have h := three_mul_jacobsthal n
  rw [hn.neg_one_pow] at h
  exact_mod_cast (by linarith : (3 * (jacobsthal n : ℤ) + 1 = 2 ^ n))

/-- For odd `n`, `3 * J n = 2 ^ n + 1` in `ℕ`. -/
theorem three_mul_jacobsthal_of_odd {n : ℕ} (hn : Odd n) :
    3 * jacobsthal n = 2 ^ n + 1 := by
  have h := three_mul_jacobsthal n
  rw [hn.neg_one_pow] at h
  exact_mod_cast (by linarith : (3 * (jacobsthal n : ℤ) = 2 ^ n + 1))

/-- For even `n`, `j n = 2 ^ n + 1` in `ℕ`. -/
theorem jacobsthalCompanion_of_even {n : ℕ} (hn : Even n) :
    jacobsthalCompanion n = 2 ^ n + 1 := by
  have h := jacobsthalCompanion_eq n
  rw [hn.neg_one_pow] at h
  exact_mod_cast h

/-- For odd `n`, `j n + 1 = 2 ^ n` in `ℕ`. -/
theorem jacobsthalCompanion_add_one_of_odd {n : ℕ} (hn : Odd n) :
    jacobsthalCompanion n + 1 = 2 ^ n := by
  have h := jacobsthalCompanion_eq n
  rw [hn.neg_one_pow] at h
  exact_mod_cast (by linarith : ((jacobsthalCompanion n : ℤ) + 1 = 2 ^ n))

/-! ### The doubling identity -/

/-- `J n * j n = J (2 * n)`.  Over `ℤ` this is `(2 ^ n - (-1) ^ n) * (2 ^ n + (-1) ^ n)`
`= 2 ^ (n + n) - (-1) ^ (n + n)` after multiplying by `3`, so it follows from
`three_mul_jacobsthal` and `jacobsthalCompanion_eq` by ring arithmetic. -/
theorem jacobsthal_mul_jacobsthalCompanion (n : ℕ) :
    jacobsthal n * jacobsthalCompanion n = jacobsthal (2 * n) := by
  rw [two_mul]
  have h := three_mul_jacobsthal n
  have hj := jacobsthalCompanion_eq n
  have h2 := three_mul_jacobsthal (n + n)
  have key : (3 : ℤ) * ((jacobsthal n : ℤ) * (jacobsthalCompanion n : ℤ))
      = 3 * (jacobsthal (n + n) : ℤ) := by
    rw [hj, h2, pow_add, pow_add]
    linear_combination ((2 : ℤ) ^ n + (-1) ^ n) * h
  have : (jacobsthal n : ℤ) * (jacobsthalCompanion n : ℤ) = (jacobsthal (n + n) : ℤ) := by
    linarith
  exact_mod_cast this

/-! ### Computed examples

The first of these is the source's `jacobsthal_two`, stated as an `example` rather than as a
theorem; see the module docstring. -/

example : jacobsthal 2 = 1 := rfl

example : jacobsthal 5 = 11 := by decide

example : jacobsthal 10 = 341 := by decide

example : jacobsthalCompanion 5 = 31 := by decide

-- The closed form at a handful of small indices, both parities.
example : 3 * jacobsthal 8 + 1 = 2 ^ 8 := by decide

example : 3 * jacobsthal 9 = 2 ^ 9 + 1 := by decide

example : 3 * jacobsthal 12 + 1 = 2 ^ 12 := by decide

example : jacobsthal 4 * jacobsthalCompanion 4 = jacobsthal 8 := by decide

end ClassicalLean
