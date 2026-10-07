/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.NumberTheory.Pell
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Pell numbers and their half-companions

The Pell numbers `P 0 = 0`, `P 1 = 1`, `P (n + 2) = 2 * P (n + 1) + P n` are the sequence
`0, 1, 2, 5, 12, 29, 70, 169, 408, 985, 2378, …` (OEIS A000129).  Their half-companions
`H n = P (n + 1) + P n` are `1, 3, 7, 17, 41, 99, …` (OEIS A001333, from its second term).

## Relation to Mathlib's `Pell` namespace

Mathlib's `Pell` namespace is about the *Pell equation*: `Pell.Solution₁ d` is the type of
integer solutions of `x ^ 2 - d * y ^ 2 = 1`, and `Pell.pell`, `Pell.xn`, `Pell.yn` in
`Mathlib/NumberTheory/PellMatiyasevic.lean` are the solution sequences for `d = a ^ 2 - 1`.
Neither is the Pell *number* sequence defined here, so the definition below is called
`pellNumber` and lives in the `ClassicalLean` namespace.  The two are connected at the end of
this file: `pellSolution` builds an element of Mathlib's `Pell.Solution₁ 2` out of an
odd-index half-companion/Pell pair.

## Main definitions

* `ClassicalLean.pellNumber` — the Pell numbers, as a function `ℕ → ℕ`.
* `ClassicalLean.pellHalfCompanion` — `H n = P (n + 1) + P n`.
* `ClassicalLean.pellSolution` — the `Pell.Solution₁ 2` built from `H (2k+1)` and `P (2k+2)`.

## Main results

* `pellNumber_add_two`, `pellHalfCompanion_add_two` : both sequences obey the recurrence
  `x (n + 2) = 2 * x (n + 1) + x n`.
* `pellNumber_succ_pos`, `pellNumber_strictMono` : positivity and strict growth.
* `pellHalfCompanion_sq_sub_two_mul_sq` : `H n ^ 2 - 2 * P (n + 1) ^ 2 = (-1) ^ (n + 1)` over `ℤ`.
  This is the arithmetic core of the file; the two results after it are corollaries.
* `coprime_pellHalfCompanion_pellNumber` : `H n` and `P (n + 1)` are coprime.
* `pellHalfCompanion_sq_sub_two_mul_sq_odd` : at odd `n` the sign is `+1`, so `H n` and
  `P (n + 1)` solve `x ^ 2 - 2 * y ^ 2 = 1`.

Context, not proved here: `H n / P (n + 1)` is the `n`-th continued-fraction convergent of
`√2`, and `P (n + 1) / P n` tends to `1 + √2`.  Neither statement appears below in any form.

## Source

Ported from a `pell` module holding five theorems.  `pell_zero`, `pell_one` and
`pell_add_two` are `pellNumber_zero`, `pellNumber_one` and `pellNumber_add_two` unchanged;
`pell_pos_of_pos` (`n ≥ 1 → pell n > 0`) is `pellNumber_succ_pos`, the same statement
reindexed.  The fifth, `pell_two` (`pell 2 = 2`), is **not** shipped as a theorem: it is a
single concrete value, and this library states concrete-number checks as `example`s — the
round-1 modules contain no literal-value theorem either — so it appears among the computed
examples at the end of this file.  That is a demotion of a source theorem, recorded here
rather than left silent.

Everything else below is an addition, with no counterpart in the source: the half-companions
and their recurrence, strict monotonicity, the Pell-equation identity and its two corollaries,
and the bridge to Mathlib's `Pell.Solution₁ 2`.
-/

namespace ClassicalLean

/-! ### The two sequences -/

/-- The Pell numbers: `P 0 = 0`, `P 1 = 1`, `P (n + 2) = 2 * P (n + 1) + P n`. -/
def pellNumber : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * pellNumber (n + 1) + pellNumber n

/-- `P 0 = 0`, the first clause of the definition.  It holds by `rfl` and carries no content
beyond the `def`; it is stated only so that `simp` can use it. -/
@[simp] theorem pellNumber_zero : pellNumber 0 = 0 := rfl

/-- `P 1 = 1`, the second clause of the definition.  As with `pellNumber_zero`, it holds by
`rfl` and adds nothing to the `def`. -/
@[simp] theorem pellNumber_one : pellNumber 1 = 1 := rfl

/-- The Pell recurrence `P (n + 2) = 2 * P (n + 1) + P n`.

This is the third clause of the definition and holds by `rfl`; it is a restatement of the
`def`, not a derived identity.  Every proof below that steps the recurrence rewrites with
it. -/
theorem pellNumber_add_two (n : ℕ) :
    pellNumber (n + 2) = 2 * pellNumber (n + 1) + pellNumber n := rfl

/-- The half-companion Pell numbers `H n = P (n + 1) + P n`, namely `1, 3, 7, 17, 41, 99, …`.

This is a definition, not a theorem: the sequence is *defined* by that formula, and the fact
that it satisfies the same recurrence as `pellNumber` is `pellHalfCompanion_add_two` below. -/
def pellHalfCompanion (n : ℕ) : ℕ := pellNumber (n + 1) + pellNumber n

/-- `H 0 = 1`.  It holds by `rfl`: unfolding `pellHalfCompanion` and then `pellNumber`
reduces both sides to `1`.  No content beyond the two `def`s. -/
@[simp] theorem pellHalfCompanion_zero : pellHalfCompanion 0 = 1 := rfl

/-- `H 1 = 3`.  It holds by `rfl`, for the same reason as `pellHalfCompanion_zero`. -/
@[simp] theorem pellHalfCompanion_one : pellHalfCompanion 1 = 3 := rfl

/-- The half-companions obey the Pell recurrence too:
`H (n + 2) = 2 * H (n + 1) + H n`. -/
theorem pellHalfCompanion_add_two (n : ℕ) :
    pellHalfCompanion (n + 2) = 2 * pellHalfCompanion (n + 1) + pellHalfCompanion n := by
  simp only [pellHalfCompanion, pellNumber_add_two]
  ring

/-! ### Positivity and growth -/

/-- Every Pell number after the first is positive. -/
theorem pellNumber_succ_pos (n : ℕ) : 0 < pellNumber (n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [pellNumber_add_two]
    omega

/-- Every half-companion Pell number is positive. -/
theorem pellHalfCompanion_pos (n : ℕ) : 0 < pellHalfCompanion n := by
  have := pellNumber_succ_pos n
  simp only [pellHalfCompanion]
  omega

/-- The Pell numbers are strictly increasing. -/
theorem pellNumber_strictMono : StrictMono pellNumber := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  match n with
  | 0 => decide
  | k + 1 =>
    have := pellNumber_succ_pos k
    rw [pellNumber_add_two]
    omega

/-! ### The Pell equation identity -/

/-- The Pell recurrence transported to `ℤ`. -/
theorem pellNumber_add_two_int (n : ℕ) :
    (pellNumber (n + 2) : ℤ) = 2 * (pellNumber (n + 1) : ℤ) + (pellNumber n : ℤ) := by
  rw [pellNumber_add_two]
  push_cast
  ring

/-- `H n ^ 2 - 2 * P (n + 1) ^ 2 = (-1) ^ (n + 1)`, over `ℤ`.

Proved by induction on `n`: writing `a = P (n + 1)` and `b = P n`, the left-hand side at `n`
is `-(a ^ 2 - 2 * a * b - b ^ 2)` and at `n + 1` it is `a ^ 2 - 2 * a * b - b ^ 2`, so each
step flips the sign. -/
theorem pellHalfCompanion_sq_sub_two_mul_sq (n : ℕ) :
    (pellHalfCompanion n : ℤ) ^ 2 - 2 * (pellNumber (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    have h1 : (pellHalfCompanion k : ℤ)
        = (pellNumber (k + 1) : ℤ) + (pellNumber k : ℤ) := by
      simp only [pellHalfCompanion]
      push_cast
      ring
    have h2 : (pellHalfCompanion (k + 1) : ℤ)
        = 3 * (pellNumber (k + 1) : ℤ) + (pellNumber k : ℤ) := by
      simp only [pellHalfCompanion, pellNumber_add_two]
      push_cast
      ring
    have h3 : (pellNumber (k + 1 + 1) : ℤ)
        = 2 * (pellNumber (k + 1) : ℤ) + (pellNumber k : ℤ) := pellNumber_add_two_int k
    rw [h1] at ih
    rw [h2, h3]
    linear_combination (-1 : ℤ) * ih

/-- `H n` and `P (n + 1)` are coprime: any common divisor divides `(-1) ^ (n + 1)`, by
`pellHalfCompanion_sq_sub_two_mul_sq`. -/
theorem coprime_pellHalfCompanion_pellNumber (n : ℕ) :
    Nat.Coprime (pellHalfCompanion n) (pellNumber (n + 1)) := by
  set d : ℕ := Nat.gcd (pellHalfCompanion n) (pellNumber (n + 1))
  have hd1 : (d : ℤ) ∣ (pellHalfCompanion n : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
  have hd2 : (d : ℤ) ∣ (pellNumber (n + 1) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)
  have hdvd : (d : ℤ) ∣ (-1 : ℤ) ^ (n + 1) := by
    rw [← pellHalfCompanion_sq_sub_two_mul_sq n]
    have h2 : (2 : ℕ) ≠ 0 := by decide
    exact dvd_sub (dvd_pow hd1 h2) ((dvd_pow hd2 h2).mul_left 2)
  have hunit : IsUnit ((-1 : ℤ) ^ (n + 1)) := (isUnit_one.neg).pow _
  have : IsUnit (d : ℤ) := isUnit_of_dvd_unit hdvd hunit
  rcases Int.isUnit_iff.mp this with h | h
  · exact_mod_cast h
  · omega

/-- At odd `n` the sign in `pellHalfCompanion_sq_sub_two_mul_sq` is `+1`, so the pair
`(H (2k+1), P (2k+2))` is an integer solution of `x ^ 2 - 2 * y ^ 2 = 1`. -/
theorem pellHalfCompanion_sq_sub_two_mul_sq_odd (k : ℕ) :
    (pellHalfCompanion (2 * k + 1) : ℤ) ^ 2 - 2 * (pellNumber (2 * k + 2) : ℤ) ^ 2 = 1 := by
  have h := pellHalfCompanion_sq_sub_two_mul_sq (2 * k + 1)
  have he : ((-1 : ℤ)) ^ (2 * k + 1 + 1) = 1 := by
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]
    norm_num
  rw [he] at h
  exact h

/-- The element of Mathlib's `Pell.Solution₁ 2` — the type of integer solutions of
`x ^ 2 - 2 * y ^ 2 = 1` — carried by the odd-index half-companion/Pell pair.  Its defining
property is `pellHalfCompanion_sq_sub_two_mul_sq_odd`; nothing is claimed here about which
solutions of the equation arise this way. -/
def pellSolution (k : ℕ) : Pell.Solution₁ 2 :=
  Pell.Solution₁.mk (pellHalfCompanion (2 * k + 1)) (pellNumber (2 * k + 2))
    (pellHalfCompanion_sq_sub_two_mul_sq_odd k)

/-- The first component of `pellSolution`.  It holds by `rfl` from the definition — the
projection of a `Pell.Solution₁.mk` — and is stated only to let `simp` see through the
construction. -/
@[simp] theorem pellSolution_x (k : ℕ) :
    (pellSolution k).x = (pellHalfCompanion (2 * k + 1) : ℤ) := rfl

/-- The second component of `pellSolution`, by `rfl` from the definition, exactly as
`pellSolution_x`. -/
@[simp] theorem pellSolution_y (k : ℕ) :
    (pellSolution k).y = (pellNumber (2 * k + 2) : ℤ) := rfl

/-! ### Computed examples

The first of these is the source's `pell_two`, stated as an `example` rather than as a
theorem; see the module docstring. -/

example : pellNumber 2 = 2 := rfl

example : pellNumber 5 = 29 := by decide

example : pellNumber 10 = 2378 := by decide

example : pellHalfCompanion 2 = 7 := rfl

example : pellHalfCompanion 3 = 17 := rfl

example : pellHalfCompanion 4 = 41 := by decide

example : pellHalfCompanion 5 = 99 := by decide

-- The identity at `n = 4`: `41 ^ 2 - 2 * 29 ^ 2 = 1681 - 1682 = -1`.
example : (pellHalfCompanion 4 : ℤ) ^ 2 - 2 * (pellNumber 5 : ℤ) ^ 2 = -1 := by decide

example : (pellSolution 1).x = 17 := by decide

example : (pellSolution 1).y = 12 := by decide

end ClassicalLean
