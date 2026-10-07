/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import ClassicalLean.Algebra.CompanionMatrix
import ClassicalLean.Combinatorics.RecurrenceGeneratingFunction

/-!
# Tribonacci numbers

The tribonacci numbers `T 0 = 0`, `T 1 = 0`, `T 2 = 1`,
`T (n + 3) = T (n + 2) + T (n + 1) + T n` are the sequence
`0, 0, 1, 1, 2, 4, 7, 13, 24, 44, 81, 149, 274, …` (OEIS A000073): the three-term analogue of
the Fibonacci recurrence.

Mathlib has the Fibonacci numbers as `Nat.fib` but not the tribonacci numbers, so `Nat.fib` is
imported and reused, and only `tribonacci` is defined here.

## Main definitions

* `ClassicalLean.tribonacci` — the tribonacci numbers `T`.

## Main results

* `tribonacci_add_three` : the recurrence, by definition.
* `tribonacci_add_two_pos` : `0 < T (n + 2)`; the two zero terms at the start are the only ones.
* `tribonacci_monotone` : `T` is monotone.
* `two_mul_sum_tribonacci_add_one` : the partial-sum identity
  `2 * (∑ i < n + 1, T i) + 1 = T (n + 2) + T n`.
* `fib_le_tribonacci_add_two` : `Nat.fib n ≤ T (n + 2)`, comparing the two recurrences.

## Source

Ported from a `tribonacci` module holding six theorems.  `tribonacci_zero`,
`tribonacci_one`, `tribonacci_two` and `tribonacci_add_three` are shipped unchanged.  The
other two, `tribonacci_three` (`T 3 = 1`) and `tribonacci_four` (`T 4 = 2`), are **not**
shipped as theorems: each is a single concrete value, and this library states
concrete-number checks as `example`s — the round-1 modules contain no literal-value theorem
either — so both appear among the computed examples at the end of this file.  That is a
demotion of two source theorems, recorded here rather than left silent.

Positivity, monotonicity, the partial-sum identity and the Fibonacci comparison have no
counterpart in the source.
-/

namespace ClassicalLean

/-! ### Definition and recurrence -/

/-- The tribonacci numbers: `T 0 = 0`, `T 1 = 0`, `T 2 = 1`, and
`T (n + 3) = T (n + 2) + T (n + 1) + T n`. -/
def tribonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n

/-- `T 0 = 0`, the first clause of the definition.  It holds by `rfl` and carries no content
beyond the `def`; it is stated only so that `simp` can use it. -/
@[simp] theorem tribonacci_zero : tribonacci 0 = 0 := rfl

/-- `T 1 = 0`, the second clause of the definition, by `rfl`.  No content beyond the
`def`. -/
@[simp] theorem tribonacci_one : tribonacci 1 = 0 := rfl

/-- `T 2 = 1`, the third clause of the definition, by `rfl`.  No content beyond the
`def`. -/
@[simp] theorem tribonacci_two : tribonacci 2 = 1 := rfl

/-- The tribonacci recurrence `T (n + 3) = T (n + 2) + T (n + 1) + T n`.

This is the fourth clause of the definition and holds by `rfl`; it is a restatement of the
`def`, not a derived identity. -/
theorem tribonacci_add_three (n : ℕ) :
    tribonacci (n + 3) = tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n := rfl

/-! ### Positivity and monotonicity -/

/-- Every tribonacci number from index `2` on is positive; `T 0 = T 1 = 0` are the only
vanishing terms. -/
theorem tribonacci_add_two_pos (n : ℕ) : 0 < tribonacci (n + 2) := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [show k + 1 + 2 = k + 3 from rfl, tribonacci_add_three]
    omega

/-- Each tribonacci number is at most its successor.  For indices `n + 3` this is immediate
from the recurrence, since the other two summands are natural numbers. -/
theorem tribonacci_le_succ (n : ℕ) : tribonacci n ≤ tribonacci (n + 1) := by
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | k + 3 =>
    have hrec : tribonacci (k + 3 + 1)
        = tribonacci (k + 3) + tribonacci (k + 2) + tribonacci (k + 1) :=
      tribonacci_add_three (k + 1)
    omega

/-- The tribonacci sequence is monotone. -/
theorem tribonacci_monotone : Monotone tribonacci :=
  monotone_nat_of_le_succ tribonacci_le_succ

/-! ### A partial-sum identity -/

/-- `2 * (∑ i ∈ range (n + 1), T i) + 1 = T (n + 2) + T n`.

Both sides increase by `2 * T (n + 1)` when `n` becomes `n + 1`, so a one-step induction
suffices even though the recurrence has three terms. -/
theorem two_mul_sum_tribonacci_add_one (n : ℕ) :
    2 * (∑ i ∈ Finset.range (n + 1), tribonacci i) + 1 = tribonacci (n + 2) + tribonacci n := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [Finset.sum_range_succ, show k + 1 + 2 = k + 3 from rfl, tribonacci_add_three]
    omega

/-! ### Comparison with the Fibonacci numbers -/

/-- `Nat.fib n ≤ T (n + 2)`: the tribonacci sequence dominates the Fibonacci sequence, shifted
by two places.  Each Fibonacci step adds two earlier terms where the tribonacci step adds
three, and the shift lines the base cases up (`fib 0 = 0 ≤ 1 = T 2`, `fib 1 = 1 ≤ 1 = T 3`). -/
theorem fib_le_tribonacci_add_two (n : ℕ) : Nat.fib n ≤ tribonacci (n + 2) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k ih1 ih2 =>
    have hrec : tribonacci (k + 2 + 2)
        = tribonacci (k + 1 + 2) + tribonacci (k + 2) + tribonacci (k + 1) :=
      tribonacci_add_three (k + 1)
    rw [Nat.fib_add_two, hrec]
    omega

/-! ### Computed examples

The first two are the source's `tribonacci_three` and `tribonacci_four`, stated as `example`s
rather than as theorems; see the module docstring. -/

example : tribonacci 3 = 1 := rfl

example : tribonacci 4 = 2 := rfl

example : tribonacci 8 = 24 := by decide

example : tribonacci 12 = 274 := by decide

example : 2 * (∑ i ∈ Finset.range 7, tribonacci i) + 1 = tribonacci 8 + tribonacci 6 := by
  decide

example : Nat.fib 10 ≤ tribonacci 12 := by decide

/-! ### Tribonacci is an instance of the two method layers

This file predates `Algebra/CompanionMatrix.lean` and
`Combinatorics/RecurrenceGeneratingFunction.lean`, and named neither.  It is a constant-coefficient
linear recurrence of order `3`, so both layers cover it outright, and the connection is recorded
here rather than left for a reader to notice.

The coefficient vector is `![1, 1, 1]`: the recurrence has no minus signs, unlike the Lucas family,
which is why `Q` plays no role and the sequence is not a `lucasU`.  Everything is stated over `ℤ`
because `recDenom` subtracts and so needs a `CommRing`, which `ℕ` is not. -/

open PowerSeries in
/-- **Tribonacci solves the order-`3` companion recurrence** `companionRec ![1, 1, 1]`. -/
theorem tribonacci_isSol_companionRec :
    (companionRec (![1, 1, 1] : Fin 3 → ℤ)).IsSolution (fun n => (tribonacci n : ℤ)) := by
  intro n
  change (tribonacci (n + 3) : ℤ)
      = ∑ i : Fin 3, (![1, 1, 1] : Fin 3 → ℤ) i * (tribonacci (n + i) : ℤ)
  rw [Fin.sum_univ_three]
  norm_num [tribonacci_add_three]
  ring

open PowerSeries in
/-- **Tribonacci therefore has a rational generating function**, numerator over
`1 - X - X ^ 2 - X ^ 3`, with no induction and no computation of the numerator: it comes straight
from `exists_poly_mk_eq` applied to the solution property above. -/
theorem exists_poly_mk_tribonacci :
    ∃ p : Polynomial ℤ,
      (∀ m, (companionRec (![1, 1, 1] : Fin 3 → ℤ)).order ≤ m → p.coeff m = 0) ∧
      mk (fun n => (tribonacci n : ℤ))
        = (p : PowerSeries ℤ) * invOfUnit (recDenom (companionRec (![1, 1, 1] : Fin 3 → ℤ))) 1 :=
  exists_poly_mk_eq _ _ tribonacci_isSol_companionRec

open PowerSeries in
/-- The trace power sums of the same companion matrix satisfy the Tribonacci recurrence — the
order-`3` case of `trace_companionMatrix_pow_isSol`.  This is the statement `NacciTrace.lean`
needed round 6 to supply, at a different coefficient vector. -/
example : (companionRec (![1, 1, 1] : Fin 3 → ℤ)).IsSolution
    (fun k => ((companionMatrix (![1, 1, 1] : Fin 3 → ℤ)) ^ k).trace) :=
  trace_companionMatrix_pow_isSol _

end ClassicalLean
