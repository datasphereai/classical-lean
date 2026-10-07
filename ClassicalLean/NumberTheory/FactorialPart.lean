/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Factorial

/-!
# Splitting a natural number along a factorial

Fix a natural number `m` and a bound `k`.  This file records the two-factor decomposition of `m`
obtained from its greatest common divisor with `k !`:

* `factorialPart m k = Nat.gcd m k !`, the largest divisor of `m` that also divides `k !`;
* `factorialCofactor m k = m / Nat.gcd m k !`, the complementary factor.

Nothing here is specific to any particular sequence; `ClassicalLean/NumberTheory/Mersenne.lean`
and `ClassicalLean/NumberTheory/Lucas.lean` both use these definitions at their own values of
`m` and `k`.

## Main results

* `factorialCofactor_mul_factorialPart` : `factorialCofactor m k * factorialPart m k = m`,
  with no primality or positivity hypothesis.
* `dvd_factorialPart_iff` : `d ∣ factorialPart m k ↔ d ∣ m ∧ d ∣ k !`.
* `prime_dvd_factorialPart_iff` : for a prime `p`, `p ∣ factorialPart m k ↔ p ∣ m ∧ p ≤ k`.
  This is the statement that pins down *which* primes the factorial part collects.
* `prime_dvd_factorialCofactor_or_dvd_factorialPart` : every prime factor of `m` divides at
  least one of the two factors.

## What the split does not say

Both of the following are recorded as computed examples at the end of the file, because both
are easy to assume and false.

* `factorialPart m k` is the largest divisor of `m` dividing `k !`, which is *weaker* than being
  the largest divisor of `m` whose prime factors are all at most `k`: for `m = 8` and `k = 2`
  the factorial part is `2`, even though `8` is itself a power of the small prime `2`.  So
  `prime_dvd_factorialPart_iff` characterises the primes but not their multiplicities.
* The cofactor need not be free of small primes, and the two factors need not be coprime.  For
  `m = 63 = 3 ^ 2 * 7` and `k = 5` the factorial part is `3` and the cofactor is `21`, which is
  still divisible by `3`.  In particular "at least one of the two factors" in
  `prime_dvd_factorialCofactor_or_dvd_factorialPart` cannot be strengthened to "exactly one".
-/

namespace ClassicalLean

/-- `factorialPart m k` is the largest divisor of `m` that also divides `k !`, namely
`Nat.gcd m k !`; the characterisation is `dvd_factorialPart_iff`.  Its prime divisors are exactly
the prime divisors of `m` that are at most `k` (`prime_dvd_factorialPart_iff`).  It is a divisor
of `k !` (`factorialPart_dvd_factorial`), which is the precise sense in which the multiplicities
it can carry are bounded by those in `k !`; no sharper statement about multiplicities is proved
here. -/
def factorialPart (m k : ℕ) : ℕ := Nat.gcd m (Nat.factorial k)

/-- `factorialCofactor m k` is the complementary factor `m / Nat.gcd m k !` left over after
dividing `m` by its factorial part. -/
def factorialCofactor (m k : ℕ) : ℕ := m / Nat.gcd m (Nat.factorial k)

/-- The factorial part of `m` divides `m`.  This is `Nat.gcd_dvd_left` in the notation of this
file; there is no content beyond that lemma, which is Lean core's, not Mathlib's. -/
theorem factorialPart_dvd (m k : ℕ) : factorialPart m k ∣ m :=
  Nat.gcd_dvd_left m (Nat.factorial k)

/-- The factorial part of `m` at bound `k` divides `k !`.  This is `Nat.gcd_dvd_right` in the
notation of this file; there is no content beyond that lemma, which is Lean core's, not
Mathlib's. -/
theorem factorialPart_dvd_factorial (m k : ℕ) : factorialPart m k ∣ Nat.factorial k :=
  Nat.gcd_dvd_right m (Nat.factorial k)

/-- Characterisation of the factorial part: `d` divides `factorialPart m k` exactly when `d`
divides both `m` and `k !`.  In particular `factorialPart m k` is the largest divisor of `m`
that divides `k !`.

This is Lean core's `Nat.dvd_gcd_iff` restated in the notation of this file. -/
theorem dvd_factorialPart_iff {d m k : ℕ} :
    d ∣ factorialPart m k ↔ d ∣ m ∧ d ∣ Nat.factorial k :=
  Nat.dvd_gcd_iff

/-- The two factors of the split multiply back to the original number:
`(m / gcd m k !) * gcd m k ! = m`.  This is the whole content of the decomposition, and it holds
for every `m` and every bound `k`, with no primality or positivity hypothesis.

The proof is `Nat.div_mul_cancel` applied to `factorialPart_dvd`. -/
theorem factorialCofactor_mul_factorialPart (m k : ℕ) :
    factorialCofactor m k * factorialPart m k = m :=
  Nat.div_mul_cancel (Nat.gcd_dvd_left m (Nat.factorial k))

/-- If `d` divides `m` then `d` divides `factorialCofactor m k * factorialPart m k`.

This is exactly the hypothesis `d ∣ m` rewritten through `factorialCofactor_mul_factorialPart`,
since that product *is* `m`; it is stated separately only because the product form is the one
that appears when a divisor is chased through the split.  It asserts nothing about how `d` is
distributed between the two factors — for that see
`prime_dvd_factorialCofactor_or_dvd_factorialPart`. -/
theorem dvd_factorialCofactor_mul_factorialPart {d m k : ℕ} (h : d ∣ m) :
    d ∣ factorialCofactor m k * factorialPart m k := by
  rw [factorialCofactor_mul_factorialPart]; exact h

/-- A positive number has a positive factorial part.  This is Lean core's
`Nat.gcd_pos_of_pos_left` (`Init.Data.Nat.Gcd`) in the notation of this file. -/
theorem factorialPart_pos {m : ℕ} (k : ℕ) (hm : 0 < m) : 0 < factorialPart m k :=
  Nat.gcd_pos_of_pos_left (Nat.factorial k) hm

/-- A positive number has a positive cofactor.  This is Lean core's `Nat.div_pos`
(`Init.Data.Nat.Div.Lemmas`) applied to `factorialPart_dvd` and `factorialPart_pos`. -/
theorem factorialCofactor_pos {m : ℕ} (k : ℕ) (hm : 0 < m) : 0 < factorialCofactor m k :=
  Nat.div_pos (Nat.le_of_dvd hm (Nat.gcd_dvd_left m (Nat.factorial k)))
    (factorialPart_pos k hm)

/-- Every prime dividing `factorialPart m k` is at most `k`.  This is `Nat.Prime.dvd_factorial`
composed with `factorialPart_dvd_factorial`. -/
theorem prime_le_of_dvd_factorialPart {p m k : ℕ} (hp : Nat.Prime p)
    (h : p ∣ factorialPart m k) : p ≤ k :=
  hp.dvd_factorial.mp (h.trans (factorialPart_dvd_factorial m k))

/-- The prime divisors of the factorial part are exactly the prime divisors of `m` that are at
most `k`: for `p` prime, `p ∣ factorialPart m k ↔ p ∣ m ∧ p ≤ k`.

This is a complete description of the *set* of primes involved, in both directions.  It says
nothing about multiplicities: `factorialPart 8 2 = 2` although `2 ∣ 8` with multiplicity three
(see the examples below). -/
theorem prime_dvd_factorialPart_iff {p m k : ℕ} (hp : Nat.Prime p) :
    p ∣ factorialPart m k ↔ p ∣ m ∧ p ≤ k := by
  constructor
  · intro h
    exact ⟨h.trans (factorialPart_dvd m k), prime_le_of_dvd_factorialPart hp h⟩
  · rintro ⟨hm, hk⟩
    exact Nat.dvd_gcd hm (hp.dvd_factorial.mpr hk)

/-- No prime factor of `m` escapes both sides of the split: if `p` is prime and `p ∣ m` then `p`
divides the cofactor or the factorial part.

The proof rewrites `m` as the product using `factorialCofactor_mul_factorialPart` and applies
Mathlib's `Nat.Prime.dvd_mul`.

"Or" is not exclusive here, and cannot be made so: for `m = 63` and `k = 5` the prime `3`
divides both factors (see the examples below). -/
theorem prime_dvd_factorialCofactor_or_dvd_factorialPart {p m k : ℕ} (hp : Nat.Prime p)
    (h : p ∣ m) : p ∣ factorialCofactor m k ∨ p ∣ factorialPart m k := by
  rw [← factorialCofactor_mul_factorialPart m k] at h
  exact (Nat.Prime.dvd_mul hp).mp h

/-! ### Computed examples -/

-- `3 ! = 6`, so the split of `15` at bound `3` is `5 * 3`.
example : factorialPart 15 3 = 3 := by decide

example : factorialCofactor 15 3 = 5 := by decide

-- The factorial part is not the largest divisor supported on primes at most `k`:
-- `gcd 8 2 ! = 2`, although `8` is a power of `2`.
example : factorialPart 8 2 = 2 := by decide

-- The cofactor is not free of small primes: `63 = 3 ^ 2 * 7` splits at bound `5` as `21 * 3`,
-- and `21` is still divisible by `3`.
example : factorialCofactor 63 5 = 21 := by decide

-- Consequently the two factors of the split are in general not coprime.
example : Nat.gcd (factorialCofactor 63 5) (factorialPart 63 5) = 3 := by decide

end ClassicalLean
