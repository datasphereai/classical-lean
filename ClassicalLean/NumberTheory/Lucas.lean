/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import ClassicalLean.NumberTheory.FactorialPart

/-!
# Lucas numbers

The Lucas sequence is the companion solution of the Fibonacci recurrence: it obeys the
same two-term rule `L (n + 2) = L (n + 1) + L n` but starts from `L 0 = 2`, `L 1 = 1`.
Its first terms are `2, 1, 3, 4, 7, 11, 18, 29, 47, 76, 123, 199, 322, …` (OEIS A000032).

Mathlib supplies the Fibonacci numbers as `Nat.fib`, so the Fibonacci side of every
statement below is stated against `Nat.fib` rather than against a private copy.

## Main definitions

* `ClassicalLean.lucas` — the Lucas numbers, as a function `ℕ → ℕ`.

## Main results

* `lucas_succ_eq_fib_add_fib` : `L (n + 1) = F n + F (n + 2)`, the defining link between the
  two sequences.
* `lucas_add_fib` : `L n + F n = 2 * F (n + 1)`, and `lucas_mul_fib` : `L n * F n = F (2 * n)`.
* `lucas_cassini`, `lucas_cassini_sub` : the two Cassini-type identities
  `L n * L (n + 2) = L (n + 1) ^ 2 + 5 * (-1) ^ n` and
  `L (n + 1) ^ 2 - L (n + 1) * L n - L n ^ 2 = -5 * (-1) ^ n`.
* `lucas_two_mul` : the doubling identity `L (2 * n) = L n ^ 2 - 2 * (-1) ^ n`, with the
  companion `lucas_two_mul_add_one` and the corollary `lucas_four_mul : L (4k) = L (2k) ^ 2 - 2`.
* `lucas_two_mul_recurrence` : the three-term recurrence obeyed by the even-index subsequence,
  `L (2 * (n + 2)) = 3 * L (2 * (n + 1)) - L (2 * n)`.
* `lucas_two_mul_mul_two_mul` : the product-to-sum identity
  `L (2m) * L (2n) = L (2 (m + n)) + L (2 |m - n|)`, general in `m` and `n`.
* `lucas_two_mul_eq_chebyshev_T` : `(L (2n) : ℚ) = 2 * (T ℚ n).eval (3 / 2)`, where `T` is
  Mathlib's Chebyshev polynomial of the first kind `Polynomial.Chebyshev.T`.
* `lucas_sq_sub_five_mul_fib_sq` : `L n ^ 2 - 5 * F n ^ 2 = 4 * (-1) ^ n`.
* `lucas_isSol_fibRec` : the real-valued Lucas sequence is a solution of Mathlib's
  `Real.fibRec`, the same linear recurrence `Nat.fib` solves.
* `coe_lucas_eq` : **Binet's formula for the Lucas numbers**, `(L n : ℝ) = φ ^ n + ψ ^ n`, for
  Mathlib's `Real.goldenRatio` and `Real.goldenConj`, with the even-index specialisation
  `coe_lucas_two_mul` : `(L (2n) : ℝ) = (φ ^ 2) ^ n + (ψ ^ 2) ^ n`.

## The factorial split

The two-factor decomposition of a natural number along its greatest common divisor with a
factorial — `factorialPart`, `factorialCofactor` and the general lemmas about them — lives in
`ClassicalLean/NumberTheory/FactorialPart.lean`, which also records what that split does *not*
say.  This file specialises the factorisation to `m = lucas (n + 1)` at the matching bound
`k = n + 1` (`factorialCofactor_mul_factorialPart_lucas`), and adds positivity of both
factors for `lucas n` at an arbitrary bound `k` (`factorialPart_lucas_pos` and
`factorialCofactor_lucas_pos`), which comes from `lucas_pos`.

## Implementation notes

`lucas` is defined with values in `ℕ`, because the factorial/gcd factorisation lives naturally
there and never subtracts. The identities that genuinely need subtraction and the
alternating sign `(-1) ^ n` are stated for the integer cast `(lucas n : ℤ)`; the cast
recurrence `lucas_add_two_int` is the bridge, and it is harmless because the recurrence
itself involves no truncated subtraction.  The Chebyshev statement is over `ℚ`, since the
relevant evaluation point is `3 / 2`.

The absolute difference `|m - n|` appearing in the product-to-sum identity is Mathlib's
`Nat.dist`.
-/

namespace ClassicalLean

/-! ### Definition and elementary properties -/

/-- The Lucas numbers: `L 0 = 2`, `L 1 = 1`, `L (n + 2) = L (n + 1) + L n`.

This is the companion sequence of `Nat.fib`, obeying the same recurrence from different
initial values. Its terms are `2, 1, 3, 4, 7, 11, 18, 29, 47, 76, 123, …` (OEIS A000032). -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

/-- The first initial value: `L 0 = 2`.  True by `rfl` from the definition. -/
@[simp] theorem lucas_zero : lucas 0 = 2 := rfl

/-- The second initial value: `L 1 = 1`.  True by `rfl` from the definition. -/
@[simp] theorem lucas_one : lucas 1 = 1 := rfl

/-- The first value produced by the recurrence: `L 2 = L 1 + L 0 = 3`.  True by `rfl`. -/
@[simp] theorem lucas_two : lucas 2 = 3 := rfl

/-- The Lucas recurrence `L (n + 2) = L (n + 1) + L n`. It holds by definition. -/
theorem lucas_add_two (n : ℕ) : lucas (n + 2) = lucas (n + 1) + lucas n := rfl

/-- Every Lucas number is positive. -/
theorem lucas_pos (n : ℕ) : 0 < lucas n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih1 ih2 =>
    rw [lucas_add_two]
    omega

/-- The Lucas recurrence transported to `ℤ`. This is the bridge used by every identity
below that needs genuine subtraction or the alternating sign `(-1) ^ n`. -/
theorem lucas_add_two_int (n : ℕ) :
    (lucas (n + 2) : ℤ) = (lucas (n + 1) : ℤ) + (lucas n : ℤ) := by
  rw [lucas_add_two]
  push_cast
  ring

/-! ### The link with the Fibonacci numbers -/

/-- `L (n + 1) = F n + F (n + 2)`: a Lucas number is the sum of the Fibonacci numbers on
either side of it.

The familiar form `L n = F (n - 1) + F (n + 1)` for `n ≥ 1` is this statement with `n` replaced
by `n - 1`; it is not stated separately, so that no truncated subtraction appears. -/
theorem lucas_succ_eq_fib_add_fib (n : ℕ) : lucas (n + 1) = Nat.fib n + Nat.fib (n + 2) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih1 ih2 =>
    have ih2' : lucas (n + 2) = Nat.fib (n + 1) + Nat.fib (n + 3) := ih2
    have hL : lucas (n + 3) = lucas (n + 2) + lucas (n + 1) := lucas_add_two (n + 1)
    have f1 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    have f2 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
    have f3 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
    change lucas (n + 3) = Nat.fib (n + 2) + Nat.fib (n + 4)
    omega

/-- `L n + F n = 2 * F (n + 1)`. Equivalent to `lucas_succ_eq_fib_add_fib`, but stated so that
it holds at `n = 0` too and needs no subtraction. It is proved here directly, by the same
two-step induction, rather than derived from that lemma. -/
theorem lucas_add_fib (n : ℕ) : lucas n + Nat.fib n = 2 * Nat.fib (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih1 ih2 =>
    have ih2' : lucas (n + 1) + Nat.fib (n + 1) = 2 * Nat.fib (n + 2) := ih2
    have hL : lucas (n + 2) = lucas (n + 1) + lucas n := lucas_add_two n
    have f1 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    have f2 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
    change lucas (n + 2) + Nat.fib (n + 2) = 2 * Nat.fib (n + 3)
    omega

/-- `L n * F n = F (2 * n)`.

The proof is Mathlib's `Nat.fib_two_mul` (`F (2n) = F n * (2 * F (n + 1) - F n)`) with the
inner factor identified as `L n` using `lucas_add_fib`.  Reading this as "`L n` is the ratio
`F (2n) / F n`" needs `F n ≠ 0`, that is `n ≥ 1`; the statement as written also covers `n = 0`,
where both sides are `0`. -/
theorem lucas_mul_fib (n : ℕ) : lucas n * Nat.fib n = Nat.fib (2 * n) := by
  have h := lucas_add_fib n
  have key : 2 * Nat.fib (n + 1) - Nat.fib n = lucas n := by omega
  rw [Nat.fib_two_mul, key, Nat.mul_comm]

/-! ### Cassini identities -/

/-- Cassini identity, difference form:
`L (n + 1) ^ 2 - L (n + 1) * L n - L n ^ 2 = -5 * (-1) ^ n`.

The proof is a sign-flip induction: replacing `n` by `n + 1` and expanding the recurrence
turns the left-hand side into its own negative. -/
theorem lucas_cassini_sub (n : ℕ) :
    (lucas (n + 1) : ℤ) ^ 2 - (lucas (n + 1) : ℤ) * (lucas n : ℤ) - (lucas n : ℤ) ^ 2
      = -5 * (-1 : ℤ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hrec : (lucas (n + 2) : ℤ) = (lucas (n + 1) : ℤ) + (lucas n : ℤ) :=
      lucas_add_two_int n
    change (lucas (n + 2) : ℤ) ^ 2 - (lucas (n + 2) : ℤ) * (lucas (n + 1) : ℤ)
        - (lucas (n + 1) : ℤ) ^ 2 = -5 * (-1 : ℤ) ^ (n + 1)
    rw [hrec]
    linear_combination -ih

/-- Cassini identity, product form: `L n * L (n + 2) = L (n + 1) ^ 2 + 5 * (-1) ^ n`. -/
theorem lucas_cassini (n : ℕ) :
    (lucas n : ℤ) * (lucas (n + 2) : ℤ) = (lucas (n + 1) : ℤ) ^ 2 + 5 * (-1 : ℤ) ^ n := by
  have hrec : (lucas (n + 2) : ℤ) = (lucas (n + 1) : ℤ) + (lucas n : ℤ) := lucas_add_two_int n
  have hc := lucas_cassini_sub n
  rw [hrec]
  linear_combination -hc

/-! ### Doubling -/

/-- The two halves of the doubling induction, proved simultaneously:

* `L (2n) = L n ^ 2 - 2 * (-1) ^ n`;
* `L (2n + 1) = L (n + 1) * L n - (-1) ^ n`.

Each inductive step consumes the Cassini identity. -/
private theorem lucas_doubling_aux (n : ℕ) :
    (lucas (2 * n) : ℤ) = (lucas n : ℤ) ^ 2 - 2 * (-1 : ℤ) ^ n ∧
      (lucas (2 * n + 1) : ℤ) = (lucas (n + 1) : ℤ) * (lucas n : ℤ) - (-1 : ℤ) ^ n := by
  induction n with
  | zero => constructor <;> norm_num
  | succ n ih =>
    obtain ⟨ihA, ihB⟩ := ih
    have hrec : (lucas (n + 2) : ℤ) = (lucas (n + 1) : ℤ) + (lucas n : ℤ) := lucas_add_two_int n
    have hc := lucas_cassini_sub n
    have hrec2n : (lucas (2 * n + 2) : ℤ) = (lucas (2 * n + 1) : ℤ) + (lucas (2 * n) : ℤ) :=
      lucas_add_two_int (2 * n)
    have hrec2n1 : (lucas (2 * n + 3) : ℤ) = (lucas (2 * n + 2) : ℤ) + (lucas (2 * n + 1) : ℤ) :=
      lucas_add_two_int (2 * n + 1)
    have hA : (lucas (2 * n + 2) : ℤ) = (lucas (n + 1) : ℤ) ^ 2 - 2 * (-1 : ℤ) ^ (n + 1) := by
      rw [hrec2n, ihA, ihB]
      linear_combination -hc
    have hB : (lucas (2 * n + 3) : ℤ)
        = (lucas (n + 2) : ℤ) * (lucas (n + 1) : ℤ) - (-1 : ℤ) ^ (n + 1) := by
      rw [hrec2n1, hA, ihB]
      linear_combination -(lucas (n + 1) : ℤ) * hrec
    exact ⟨hA, hB⟩

/-- Doubling identity: `L (2n) = L n ^ 2 - 2 * (-1) ^ n`.  This is the first component of
`lucas_doubling_aux`; the proof is that projection and nothing more. -/
theorem lucas_two_mul (n : ℕ) :
    (lucas (2 * n) : ℤ) = (lucas n : ℤ) ^ 2 - 2 * (-1 : ℤ) ^ n :=
  (lucas_doubling_aux n).1

/-- Companion of the doubling identity: `L (2n + 1) = L (n + 1) * L n - (-1) ^ n`.  This is the
second component of `lucas_doubling_aux`; the proof is that projection and nothing more. -/
theorem lucas_two_mul_add_one (n : ℕ) :
    (lucas (2 * n + 1) : ℤ) = (lucas (n + 1) : ℤ) * (lucas n : ℤ) - (-1 : ℤ) ^ n :=
  (lucas_doubling_aux n).2

/-- At an even index the alternating sign disappears: `L (4k) = L (2k) ^ 2 - 2`.  This is
`lucas_two_mul` at `2k`, using `(-1) ^ (2k) = 1`. -/
theorem lucas_four_mul (k : ℕ) : (lucas (4 * k) : ℤ) = (lucas (2 * k) : ℤ) ^ 2 - 2 := by
  have h := lucas_two_mul (2 * k)
  have heven : (-1 : ℤ) ^ (2 * k) = 1 := by
    rw [pow_mul]
    norm_num
  rw [show 4 * k = 2 * (2 * k) by ring, h, heven]
  ring

/-! ### The even-index subsequence -/

/-- The even-index Lucas numbers `L 0, L 2, L 4, …` satisfy a three-term recurrence of their
own: `L (2 (n + 2)) = 3 * L (2 (n + 1)) - L (2n)`.

It is obtained by iterating the Lucas recurrence twice.  It is the same three-term shape as the
Chebyshev recurrence `T (k + 2) = 2 * X * T (k + 1) - T k` evaluated at `X = 3 / 2`; that
correspondence is made precise below by `lucas_two_mul_eq_chebyshev_T`, and it is this
recurrence that drives the two-step induction behind the product-to-sum identity. -/
theorem lucas_two_mul_recurrence (n : ℕ) :
    (lucas (2 * (n + 2)) : ℤ) = 3 * (lucas (2 * (n + 1)) : ℤ) - (lucas (2 * n) : ℤ) := by
  have r1 : (lucas (2 * n + 4) : ℤ) = (lucas (2 * n + 3) : ℤ) + (lucas (2 * n + 2) : ℤ) :=
    lucas_add_two_int (2 * n + 2)
  have r2 : (lucas (2 * n + 3) : ℤ) = (lucas (2 * n + 2) : ℤ) + (lucas (2 * n + 1) : ℤ) :=
    lucas_add_two_int (2 * n + 1)
  have r3 : (lucas (2 * n + 2) : ℤ) = (lucas (2 * n + 1) : ℤ) + (lucas (2 * n) : ℤ) :=
    lucas_add_two_int (2 * n)
  change (lucas (2 * n + 4) : ℤ) = 3 * (lucas (2 * n + 2) : ℤ) - (lucas (2 * n) : ℤ)
  linarith

/-! ### The Chebyshev description of the even-index subsequence -/

open Polynomial in
/-- The even-index Lucas numbers are the Chebyshev polynomials of the first kind evaluated at
`3 / 2`, doubled: `(L (2n) : ℚ) = 2 * (T ℚ n).eval (3 / 2)`, with `T` Mathlib's
`Polynomial.Chebyshev.T`.

The proof is a two-step induction: the base cases are `T 0 = 1` and `T 1 = X`, and the step
matches Mathlib's `Polynomial.Chebyshev.T_add_two` against `lucas_two_mul_recurrence`. -/
theorem lucas_two_mul_eq_chebyshev_T (n : ℕ) :
    (lucas (2 * n) : ℚ) = 2 * (Chebyshev.T ℚ n).eval (3 / 2) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [Chebyshev.T_zero]
  | one => norm_num [Chebyshev.T_one]
  | more n ih1 ih2 =>
    have hT : (Chebyshev.T ℚ ((n : ℤ) + 2))
        = 2 * X * Chebyshev.T ℚ ((n : ℤ) + 1) - Chebyshev.T ℚ (n : ℤ) :=
      Chebyshev.T_add_two ℚ (n : ℤ)
    have hrec : (lucas (2 * (n + 2)) : ℚ)
        = 3 * (lucas (2 * (n + 1)) : ℚ) - (lucas (2 * n) : ℚ) := by
      have h := lucas_two_mul_recurrence n
      have h' : ((lucas (2 * (n + 2)) : ℤ) : ℚ)
          = ((3 * (lucas (2 * (n + 1)) : ℤ) - (lucas (2 * n) : ℤ) : ℤ) : ℚ) := by rw [h]
      push_cast at h'
      linarith
    have hcast2 : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
    have hcast1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [hrec, hcast2, hT]
    rw [hcast1] at ih2
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X]
    linarith [ih1, ih2]

/-! ### The product-to-sum identity -/

/-- The ordered half of the product-to-sum identity, proved by two-step induction on `n`
using the even-index recurrence. -/
private theorem lucas_two_mul_mul_of_le (m : ℕ) : ∀ n : ℕ, n ≤ m →
    (lucas (2 * m) : ℤ) * (lucas (2 * n) : ℤ)
      = (lucas (2 * (m + n)) : ℤ) + (lucas (2 * (m - n)) : ℤ) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    intro _
    have h0 : (lucas (2 * 0) : ℤ) = 2 := by norm_num
    rw [h0, Nat.add_zero, Nat.sub_zero]
    ring
  | one =>
    intro hm
    have hrec := lucas_two_mul_recurrence (m - 1)
    rw [show m - 1 + 2 = m + 1 by omega, show m - 1 + 1 = m by omega] at hrec
    have h1 : (lucas (2 * 1) : ℤ) = 3 := by norm_num
    rw [h1]
    linarith
  | more n ih1 ih2 =>
    intro hm
    have ih1' := ih1 (by omega)
    have ih2' := ih2 (by omega)
    rw [show m + (n + 1) = m + n + 1 by omega, show m - (n + 1) = m - n - 1 by omega] at ih2'
    rw [show m + (n + 2) = m + n + 2 by omega, show m - (n + 2) = m - n - 2 by omega]
    have E2 := lucas_two_mul_recurrence (m + n)
    have E3 : (lucas (2 * (m - n - 2)) : ℤ)
        = 3 * (lucas (2 * (m - n - 1)) : ℤ) - (lucas (2 * (m - n)) : ℤ) := by
      have h := lucas_two_mul_recurrence (m - n - 2)
      rw [show m - n - 2 + 2 = m - n by omega, show m - n - 2 + 1 = m - n - 1 by omega] at h
      linarith
    calc (lucas (2 * m) : ℤ) * (lucas (2 * (n + 2)) : ℤ)
        = (lucas (2 * m) : ℤ) * (3 * (lucas (2 * (n + 1)) : ℤ) - (lucas (2 * n) : ℤ)) := by
          rw [lucas_two_mul_recurrence n]
      _ = 3 * ((lucas (2 * m) : ℤ) * (lucas (2 * (n + 1)) : ℤ))
            - (lucas (2 * m) : ℤ) * (lucas (2 * n) : ℤ) := by ring
      _ = 3 * ((lucas (2 * (m + n + 1)) : ℤ) + (lucas (2 * (m - n - 1)) : ℤ))
            - ((lucas (2 * (m + n)) : ℤ) + (lucas (2 * (m - n)) : ℤ)) := by rw [ih2', ih1']
      _ = (lucas (2 * (m + n + 2)) : ℤ) + (lucas (2 * (m - n - 2)) : ℤ) := by linarith

/-- Product-to-sum identity for the even-index Lucas numbers, general in `m` and `n`:
`L (2m) * L (2n) = L (2 (m + n)) + L (2 |m - n|)`, where `|m - n|` is `Nat.dist m n`.

Stated over `ℕ`: no subtraction occurs, since `Nat.dist` already denotes the absolute
difference, and the hypothesis `n ≤ m` needed by the subtraction form is not required.

Context, not the proof used here: the classical reason such an identity holds is the Chebyshev
product formula `Polynomial.Chebyshev.T_mul_T` (`2 * T m * T k = T (m + k) + T (m - k)`),
transported along the description of the even-index Lucas numbers proved above as
`lucas_two_mul_eq_chebyshev_T`.  This file does not take that route: the proof below is a direct
two-step induction on `lucas_two_mul_recurrence`, and nothing here is derived from `T_mul_T`. -/
theorem lucas_two_mul_mul_two_mul (m n : ℕ) :
    lucas (2 * m) * lucas (2 * n) = lucas (2 * (m + n)) + lucas (2 * Nat.dist m n) := by
  have key : (lucas (2 * m) : ℤ) * (lucas (2 * n) : ℤ)
      = (lucas (2 * (m + n)) : ℤ) + (lucas (2 * Nat.dist m n) : ℤ) := by
    rcases le_total n m with h | h
    · rw [Nat.dist_eq_sub_of_le_right h]
      exact lucas_two_mul_mul_of_le m n h
    · rw [Nat.dist_eq_sub_of_le h, show m + n = n + m from Nat.add_comm m n]
      linear_combination lucas_two_mul_mul_of_le n m h
  exact_mod_cast key

/-! ### The discriminant identity -/

/-- The three invariants carried by the induction behind `lucas_sq_sub_five_mul_fib_sq`:
the identity at `n`, the identity at `n + 1`, and the mixed form
`L n * L (n + 1) - 5 * F n * F (n + 1) = 2 * (-1) ^ n`. -/
private theorem lucas_sq_sub_five_mul_fib_sq_aux (n : ℕ) :
    ((lucas n : ℤ) ^ 2 - 5 * (Nat.fib n : ℤ) ^ 2 = 4 * (-1 : ℤ) ^ n) ∧
      ((lucas (n + 1) : ℤ) ^ 2 - 5 * (Nat.fib (n + 1) : ℤ) ^ 2 = 4 * (-1 : ℤ) ^ (n + 1)) ∧
      ((lucas n : ℤ) * (lucas (n + 1) : ℤ)
        - 5 * (Nat.fib n : ℤ) * (Nat.fib (n + 1) : ℤ) = 2 * (-1 : ℤ) ^ n) := by
  induction n with
  | zero => refine ⟨?_, ?_, ?_⟩ <;> norm_num
  | succ n ih =>
    obtain ⟨hA, hA1, hB⟩ := ih
    have hL : (lucas (n + 2) : ℤ) = (lucas (n + 1) : ℤ) + (lucas n : ℤ) := lucas_add_two_int n
    have hF : (Nat.fib (n + 2) : ℤ) = (Nat.fib n : ℤ) + (Nat.fib (n + 1) : ℤ) := by
      rw [Nat.fib_add_two]
      push_cast
      ring
    refine ⟨hA1, ?_, ?_⟩
    · change (lucas (n + 2) : ℤ) ^ 2 - 5 * (Nat.fib (n + 2) : ℤ) ^ 2 = 4 * (-1 : ℤ) ^ (n + 2)
      rw [hL, hF]
      linear_combination hA + hA1 + 2 * hB
    · change (lucas (n + 1) : ℤ) * (lucas (n + 2) : ℤ)
          - 5 * (Nat.fib (n + 1) : ℤ) * (Nat.fib (n + 2) : ℤ) = 2 * (-1 : ℤ) ^ (n + 1)
      rw [hL, hF]
      linear_combination hA1 + hB

/-- The discriminant identity `L n ^ 2 - 5 * F n ^ 2 = 4 * (-1) ^ n`.

Context for the constant: `5` is the discriminant of `x ^ 2 - x - 1`, the shared characteristic
polynomial of the two sequences; that reading is motivation and is not what the proof uses,
which is the three-invariant induction above.  The statement is placed over `ℤ` so that both
parities are one equation; over `ℕ` the two parities would need separate statements, since the
left-hand side changes sign with `n`. -/
theorem lucas_sq_sub_five_mul_fib_sq (n : ℕ) :
    (lucas n : ℤ) ^ 2 - 5 * (Nat.fib n : ℤ) ^ 2 = 4 * (-1 : ℤ) ^ n :=
  (lucas_sq_sub_five_mul_fib_sq_aux n).1

/-- The mixed companion of the discriminant identity:
`L n * L (n + 1) - 5 * F n * F (n + 1) = 2 * (-1) ^ n`.  This is the third component of
`lucas_sq_sub_five_mul_fib_sq_aux`; the proof is that projection and nothing more. -/
theorem lucas_mul_lucas_succ_sub_five_mul_fib_mul_fib_succ (n : ℕ) :
    (lucas n : ℤ) * (lucas (n + 1) : ℤ)
      - 5 * (Nat.fib n : ℤ) * (Nat.fib (n + 1) : ℤ) = 2 * (-1 : ℤ) ^ n :=
  (lucas_sq_sub_five_mul_fib_sq_aux n).2.2

/-! ### Binet's formula -/

/-- The real-valued Lucas sequence is a solution of Mathlib's `Real.fibRec`, the linear
recurrence of order `2` with coefficients `![1, 1]`.

Mathlib records `Nat.fib` as a solution of the same recurrence (`Real.fib_isSol_fibRec`); this
is the companion statement, and it is what makes `coe_lucas_eq` below a consequence of
`LinearRecurrence.eq_iff_eqOn_range_order` — two solutions agreeing on the first `order` values are
equal — rather than a fresh induction. -/
theorem lucas_isSol_fibRec : Real.fibRec.IsSolution fun n => (lucas n : ℝ) := by
  rw [Real.fibRec]
  intro n
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero,
    Fin.val_one, Nat.add_zero, one_mul]
  rw [lucas_add_two]
  push_cast
  ring

open Real in
/-- **Binet's formula for the Lucas numbers**, as a function equality:
`(fun n => (L n : ℝ)) = fun n => φ ^ n + ψ ^ n`.

The proof is `LinearRecurrence.eq_iff_eqOn_range_order` for `Real.fibRec`: both sides are
solutions — the left by `lucas_isSol_fibRec`, the right because the solution space is a
submodule containing `φ ^ ·` and `ψ ^ ·` (Mathlib's `Real.geom_goldenRatio_isSol_fibRec` and
`Real.geom_goldenConj_isSol_fibRec`) — and they agree at `n = 0` (`2 = 1 + 1`) and at `n = 1`
(`1 = φ + ψ`, Mathlib's `Real.goldenRatio_add_goldenConj`).

This mirrors Mathlib's `Real.coe_fib_eq'` for `Nat.fib`, where the two initial values give the
difference `(φ ^ n - ψ ^ n) / √5` instead of the sum. -/
theorem coe_lucas_eq' :
    (fun n => (lucas n : ℝ)) = fun n => goldenRatio ^ n + goldenConj ^ n := by
  rw [fibRec.eq_iff_eqOn_range_order]
  · intro i hi
    norm_cast at hi
    fin_cases hi
    · norm_num
    · simp
  · exact lucas_isSol_fibRec
  · suffices LinearRecurrence.IsSolution fibRec ((goldenRatio ^ ·) + (goldenConj ^ ·)) by
      exact this
    exact (@fibRec ℝ _).solSpace.add_mem geom_goldenRatio_isSol_fibRec
      geom_goldenConj_isSol_fibRec

open Real in
/-- **Binet's formula for the Lucas numbers**: `(L n : ℝ) = φ ^ n + ψ ^ n`.

The Lucas numbers are the *sum* of the two geometric solutions of the Fibonacci recurrence,
where `Nat.fib` is their normalised difference; that is the precise sense in which the two
sequences are companions.  Unlike Mathlib's `Real.coe_fib_eq` there is no `√5` in the
denominator, because the sum of the two initial values `φ + ψ = 1` needs no normalisation.

Mathlib search behind the claim that this is not already available.  `find Mathlib -iname
'*lucas*'` returns `NumberTheory/LucasLehmer.lean`, `NumberTheory/LucasPrimality.lean`,
`Analysis/Complex/Polynomial/GaussLucas.lean` and `Data/Nat/Choose/Lucas.lean` — the
Lucas–Lehmer test, the Lucas primality test, the Gauss–Lucas theorem and Lucas' congruence for
binomial coefficients, none of them this sequence.  **That search was not sufficient**, and the
correction is recorded here rather than left out: Mathlib does carry the sequence, under another
name, as `(Polynomial.dickson 1 (-1) n).eval 1` — see the "What Mathlib has" section of
`ClassicalLean/NumberTheory/LucasSequence.lean`, which measures what `Dickson.lean` does and
does not prove.  What is genuinely absent is a `ℕ → ℕ` Lucas sequence and any closed form for
it: every theorem in `Dickson.lean` beyond the recurrence is at parameter `1` or `0`, and
`-1` is neither. -/
theorem coe_lucas_eq (n : ℕ) : (lucas n : ℝ) = goldenRatio ^ n + goldenConj ^ n :=
  congrFun coe_lucas_eq' n

open Real in
/-- Binet's formula at an even index: `(L (2n) : ℝ) = (φ ^ 2) ^ n + (ψ ^ 2) ^ n`.

This is `coe_lucas_eq` at `2 * n` with `pow_mul`, and it is the analytic counterpart of
`lucas_two_mul_recurrence`: `φ ^ 2` and `ψ ^ 2` are the two roots of `t ^ 2 - 3 * t + 1`, which
is exactly the characteristic polynomial of that three-term recurrence. -/
theorem coe_lucas_two_mul (n : ℕ) :
    (lucas (2 * n) : ℝ) = (goldenRatio ^ 2) ^ n + (goldenConj ^ 2) ^ n := by
  rw [coe_lucas_eq, pow_mul, pow_mul]

/-! ### Factorisation against the factorials -/

/-- The factorial split of a Lucas number at the matching bound: the cofactor and the factorial
part of `L (n + 1)` relative to `(n + 1)!` multiply back to `L (n + 1)`.

This is `ClassicalLean.factorialCofactor_mul_factorialPart` at `m := lucas (n + 1)` and
`k := n + 1`; it carries no Lucas-specific content beyond fixing those two arguments.  What the
split does and does not determine — in particular that the two factors need not be coprime — is
recorded in `ClassicalLean/NumberTheory/FactorialPart.lean`. -/
theorem factorialCofactor_mul_factorialPart_lucas (n : ℕ) :
    factorialCofactor (lucas (n + 1)) (n + 1) * factorialPart (lucas (n + 1)) (n + 1)
      = lucas (n + 1) :=
  factorialCofactor_mul_factorialPart (lucas (n + 1)) (n + 1)

/-- The factorial part of a Lucas number is positive at every bound.  This is
`ClassicalLean.factorialPart_pos` fed with `lucas_pos`. -/
theorem factorialPart_lucas_pos (n k : ℕ) : 0 < factorialPart (lucas n) k :=
  factorialPart_pos k (lucas_pos n)

/-- The cofactor of a Lucas number is positive at every bound.  This is
`ClassicalLean.factorialCofactor_pos` fed with `lucas_pos`. -/
theorem factorialCofactor_lucas_pos (n k : ℕ) : 0 < factorialCofactor (lucas n) k :=
  factorialCofactor_pos k (lucas_pos n)

/-! ### Spot checks -/

example : lucas 0 = 2 := rfl

example : lucas 10 = 123 := by decide

example : lucas 11 = Nat.fib 10 + Nat.fib 12 := by decide

example : lucas 6 * Nat.fib 6 = Nat.fib 12 := by decide

example : lucas 4 * lucas 6 = lucas 10 + lucas 2 := by decide

-- Binet must reproduce the sequence, not merely typecheck. At `n = 2` it gives `φ² + ψ² = 3`,
-- and at `n = 5` it gives `φ⁵ + ψ⁵ = 11`; both are read off `coe_lucas_eq` and nothing else.
example : Real.goldenRatio ^ 2 + Real.goldenConj ^ 2 = 3 := by
  have h := coe_lucas_eq 2
  rw [lucas_two] at h
  exact_mod_cast h.symm

example : Real.goldenRatio ^ 5 + Real.goldenConj ^ 5 = 11 := by
  have h := coe_lucas_eq 5
  have h5 : lucas 5 = 11 := by decide
  rw [h5] at h
  exact_mod_cast h.symm

-- `L 3 = 4` and `3 ! = 6`, so the split of `L 3` at bound `3` is `2 * 2`; the two factors of
-- the split are equal here, and in particular not coprime.
example : factorialPart (lucas 3) 3 = 2 := by decide

example : factorialCofactor (lucas 3) 3 = 2 := by decide

end ClassicalLean
