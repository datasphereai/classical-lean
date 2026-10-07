/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.NumberTheory.LucasLehmer
import ClassicalLean.NumberTheory.FactorialPart
import ClassicalLean.Order.Superadditive

/-!
# Mersenne numbers

The Mersenne numbers `M n = 2 ^ n - 1` are already available in Mathlib as `mersenne`, together
with the basic arithmetic of the sequence: `mersenne_zero`, `mersenne_pos` (`0 < M n ↔ 0 < n`),
`mersenne_succ` (the doubling recurrence `M (n + 1) = 2 * M n + 1`), `succ_mersenne`
(`M n + 1 = 2 ^ n`), `strictMono_mersenne` and `mersenne_odd`.  Nothing in this file reproves
those; they are cited where they are used.

## Arithmetic along the index

* `mersenne_eq_two_pow_sub_one`: `M n = 2 ^ n - 1`, true by `rfl` from Mathlib's definition.
* `mersenne_add`: `M (m + n) = 2 ^ n * M m + M n`.  This is the addition law of the sequence;
  its `n = 1` case is the doubling recurrence, checked below as an `example`.
* `mersenne_dvd_mersenne`: if `m ∣ n` then `M m ∣ M n`.  A restatement of Mathlib's
  `Nat.pow_sub_one_dvd_pow_sub_one`.

## The factorial split at a Mersenne number

The general two-factor decomposition `m = factorialCofactor m k * factorialPart m k` and all the
general lemmas about it live in `ClassicalLean/NumberTheory/FactorialPart.lean`, which also
records what that split does *not* say.  This file only specialises it to `m = mersenne n`:

* `factorialCofactor_mul_factorialPart_mersenne`, `factorialPart_mersenne_pos` and
  `factorialCofactor_mersenne_pos` are the general statements with `m := mersenne n`, obtained
  by citing `mersenne_pos` for positivity;
* `dvd_factorialCofactor_mul_factorialPart_of_dvd_mersenne` is the divisor form;
* `odd_factorialPart_mersenne` is the one statement below that uses a property of Mersenne
  numbers beyond positivity: because `M n` is odd for `n ≠ 0` (Mathlib's `mersenne_odd`), the
  factorial part of `M n` is odd too, so the prime `2` never divides it.
-/

namespace ClassicalLean.Mersenne

/-! ### Arithmetic of the Mersenne sequence -/

/-- The defining formula `M n = 2 ^ n - 1`, available as a rewrite rule so that a proof need not
unfold the definition.  It is `rfl`: this is Mathlib's definition of `mersenne`, not a derived
fact.  No proof in this file uses it; it is here for downstream use. -/
theorem mersenne_eq_two_pow_sub_one (n : ℕ) : mersenne n = 2 ^ n - 1 := rfl

/-- The addition law of the Mersenne sequence: `M (m + n) = 2 ^ n * M m + M n`.

Context, not proved here: in binary, `M (m + n)` is a run of `m + n` ones, and the identity is
that run split as `m` ones shifted left by `n` places, followed by `n` ones.  The `n = 1` case is
the doubling recurrence `M (m + 1) = 2 * M m + 1`; it is checked as an `example` below rather
than asserted here.

The proof adds one to both sides so that no truncated subtraction is involved, rewrites with
Mathlib's `succ_mersenne` (`M n + 1 = 2 ^ n`), and finishes with `omega`. -/
theorem mersenne_add (m n : ℕ) : mersenne (m + n) = 2 ^ n * mersenne m + mersenne n := by
  have h : mersenne (m + n) + 1 = 2 ^ n * mersenne m + mersenne n + 1 := by
    rw [succ_mersenne, pow_add,
      show 2 ^ n * mersenne m + mersenne n + 1 = 2 ^ n * mersenne m + (mersenne n + 1) by ring,
      succ_mersenne, ← succ_mersenne m]
    ring
  omega

/-- The doubling recurrence `M (m + 1) = 2 * M m + 1`, obtained from `mersenne_add` at `n = 1`.
Stated as an `example` because it is a check on the claim made in the docstring above, not a
result this library needs to export. -/
example (m : ℕ) : mersenne (m + 1) = 2 * mersenne m + 1 := by
  have h := mersenne_add m 1
  simpa [mersenne] using h

/-- Divisibility of indices is inherited by Mersenne numbers: if `m ∣ n` then `M m ∣ M n`.

This is a restatement of Mathlib's `Nat.pow_sub_one_dvd_pow_sub_one`
(`Mathlib/Algebra/Ring/GeomSum.lean`, `x ^ m - 1 ∣ x ^ k - 1` for `m ∣ k`) at `x = 2`, put into
Mersenne notation; the proof is that lemma and nothing else.  It is the elementary half of the
classical fact that `2 ^ n - 1` can only be prime when `n` is prime, whose full implication is
Mathlib's `Nat.Prime.of_mersenne`. -/
theorem mersenne_dvd_mersenne {m n : ℕ} (h : m ∣ n) : mersenne m ∣ mersenne n :=
  Nat.pow_sub_one_dvd_pow_sub_one 2 h

/-! ### The factorial split of a Mersenne number -/

/-- Every Mersenne number factors as cofactor times factorial part, for every bound `k`:
`M n = (M n / gcd (M n) k !) * gcd (M n) k !`.

This is `ClassicalLean.factorialCofactor_mul_factorialPart` at `m := mersenne n`. -/
theorem factorialCofactor_mul_factorialPart_mersenne (n k : ℕ) :
    factorialCofactor (mersenne n) k * factorialPart (mersenne n) k = mersenne n :=
  factorialCofactor_mul_factorialPart (mersenne n) k

/-- If `d ∣ M n` then `d` divides the product of the cofactor and the factorial part — which is
`M n` again.  This is `ClassicalLean.dvd_factorialCofactor_mul_factorialPart` at
`m := mersenne n`, and like that lemma it says nothing about how `d` is split between the two
factors; the prime-by-prime statement is
`ClassicalLean.prime_dvd_factorialCofactor_or_dvd_factorialPart`. -/
theorem dvd_factorialCofactor_mul_factorialPart_of_dvd_mersenne {d n k : ℕ}
    (h : d ∣ mersenne n) :
    d ∣ factorialCofactor (mersenne n) k * factorialPart (mersenne n) k :=
  dvd_factorialCofactor_mul_factorialPart h

/-- The factorial part of a nonzero Mersenne number is positive.  This is
`ClassicalLean.factorialPart_pos` fed with Mathlib's `mersenne_pos`. -/
theorem factorialPart_mersenne_pos {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    0 < factorialPart (mersenne n) k :=
  factorialPart_pos k (mersenne_pos.mpr (Nat.pos_of_ne_zero hn))

/-- For `n ≠ 0` the cofactor of `M n` is positive.  This is
`ClassicalLean.factorialCofactor_pos` fed with Mathlib's `mersenne_pos`. -/
theorem factorialCofactor_mersenne_pos {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    0 < factorialCofactor (mersenne n) k :=
  factorialCofactor_pos k (mersenne_pos.mpr (Nat.pos_of_ne_zero hn))

/-- The factorial part of a nonzero Mersenne number is odd.  The factorial part divides `M n`
and `M n` is odd for `n ≠ 0` (Mathlib's `mersenne_odd`), so `2` never divides the factorial part
of a Mersenne number.  Nothing further about which primes do divide it is claimed here; the
general description is `ClassicalLean.prime_dvd_factorialPart_iff`. -/
theorem odd_factorialPart_mersenne {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    Odd (factorialPart (mersenne n) k) := by
  have hm : mersenne n % 2 = 1 := Nat.odd_iff.mp (mersenne_odd.mpr hn)
  have hd : factorialPart (mersenne n) k ∣ mersenne n := factorialPart_dvd (mersenne n) k
  rw [Nat.odd_iff]
  by_contra hc
  have h2 : (2 : ℕ) ∣ factorialPart (mersenne n) k := by omega
  have h3 : (2 : ℕ) ∣ mersenne n := h2.trans hd
  omega

/-! ### Computed examples -/

example : mersenne 7 = 127 := rfl

example : mersenne 3 ∣ mersenne 9 := by decide

-- `M 4 = 15`, `3 ! = 6`, so the split of `15` at bound `3` is `5 * 3`.
example : factorialPart (mersenne 4) 3 = 3 := by decide

example : factorialCofactor (mersenne 4) 3 = 5 := by decide

-- `M 6 = 63 = 3 ^ 2 * 7` splits at bound `5` as `21 * 3`, and `21` is still divisible by `3`:
-- the two factors of the split are in general not coprime.
example : factorialCofactor (mersenne 6) 5 = 21 := by decide

/-! ### `mersenne` is the first instance of `Order/Superadditive.lean`

`Order/Superadditive.lean` defines `Superadditive f := ∀ m n, f m + f n ≤ f (m + n)` and proves five
theorems about it — `map_zero`, `monotone`, `linear_le`, `unbounded`, `pos_of_pos` — but until now
**nothing in the library satisfied it**, which is the shape this project does not ship: a
definition whose theorems are all conditional on a hypothesis no object is known to meet.
Corrected 2026-09-23 (order G-5, round 19): this paragraph said "six"; the module declares five
theorems, the five named (round 16, finding 5).

`mersenne` meets it, and the proof is the observation that `(2^m - 1)(2^n - 1) ≥ 0` rearranges to
`2^m + 2^n ≤ 2^m · 2^n + 1`.

The candidates were separated numerically first: `mersenne` and `tribonacci` are superadditive on
`m, n < 18` with no failures; `Nat.fib` and `jacobsthal` are **not**, each failing exactly once, at
`(1,1)` — `fib 1 + fib 1 = 2` against `fib 2 = 1`.  So the property genuinely discriminates within
the library's own sequences rather than holding for all of them. `tribonacci` is measured
superadditive and **not proved** here; it needs an induction this section does not do. -/

/-- **`mersenne` is superadditive** — `Order/Superadditive.lean`'s first instance, and the first
edge from `NumberTheory/` to `Order/`. -/
theorem superadditive_mersenne : Superadditive mersenne := by
  intro m n
  simp only [mersenne]
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hkey : 2 ^ m + 2 ^ n ≤ 2 ^ m * 2 ^ n + 1 := by
    nlinarith [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  rw [pow_add]
  omega

-- The five theorems of `Order/Superadditive.lean` therefore now say something about a real object.
-- (Corrected 2026-09-23, order G-5 round 19: this said "six"; round 16 finding 5 counted five.)
example : Monotone mersenne := superadditive_mersenne.monotone

example (n : ℕ) : n * mersenne 1 ≤ mersenne n := superadditive_mersenne.linear_le n

end ClassicalLean.Mersenne
