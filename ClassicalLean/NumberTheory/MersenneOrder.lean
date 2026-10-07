/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Data.ZMod.Basic
import ClassicalLean.NumberTheory.FactorialPart

/-!
# Divisors of Mersenne numbers, via the order of `2`

A prime `p` divides `M m = 2 ^ m - 1` exactly when the multiplicative order of `2` modulo `p`
divides `m`. That single fact controls which primes can appear in a Mersenne number, and it is
what this file proves and then uses.

* `dvd_mersenne_iff_pow_eq_one` — `p ∣ M m ↔ (2 : ZMod p) ^ m = 1`.
* `dvd_mersenne_iff_orderOf_dvd` — `p ∣ M m ↔ ord_p(2) ∣ m`.
* `factorialPart_mersenne_eq_one_of_prime` — **if `q` is prime then `gcd (M q) (k !) = 1` for
  every `k < q`**: a Mersenne number with prime exponent has no prime factor small enough to
  appear in such a factorial, so its factorial part is trivial.

The last is the interesting one. Its proof is the classical order argument: a prime `p ∣ M q`
has `ord_p(2) ∣ q`, and `ord_p(2) ∣ p - 1` by Fermat. With `q` prime the first forces the order
to be `1` or `q`; order `1` would make `p ∣ 2 - 1 = 1`, and order `q` forces `q ≤ p - 1`, so
every prime factor of `M q` exceeds `q`. A prime dividing `k !` is at most `k`, and the two
cannot both hold.

## Provenance

Proved while closing holes in an earlier open module, which carried the last
statement as one of five `sorry`s and suggested "a corollary of the closed form, or a direct
order argument". This is the direct argument, so it does **not** depend on the closed form that
is still open. `dvd_mersenne_iff_orderOf_dvd` is also one of the three ingredients that open
lemma needs; the other two — lifting-the-exponent and the `multiplicity ↔ factorization` bridge
— remain.
-/

namespace ClassicalLean

open Nat

/-- A prime `p` divides `2 ^ m - 1` exactly when `2 ^ m = 1` in `ZMod p`. The natural
subtraction is harmless because `1 ≤ 2 ^ m`. -/
theorem dvd_mersenne_iff_pow_eq_one {p m : ℕ} (hp : p.Prime) :
    p ∣ 2 ^ m - 1 ↔ (2 : ZMod p) ^ m = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
  constructor
  · intro h
    have hz : ((2 ^ m - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
    rw [Nat.cast_sub h1] at hz
    push_cast at hz
    linear_combination hz
  · intro h
    refine (ZMod.natCast_eq_zero_iff _ _).mp ?_
    rw [Nat.cast_sub h1]
    push_cast
    rw [h]
    ring

/-- **A prime divides a Mersenne number exactly when the order of `2` divides the exponent.** -/
theorem dvd_mersenne_iff_orderOf_dvd {p m : ℕ} (hp : p.Prime) :
    p ∣ 2 ^ m - 1 ↔ orderOf (2 : ZMod p) ∣ m := by
  rw [dvd_mersenne_iff_pow_eq_one hp, orderOf_dvd_iff_pow_eq_one]

/-- Every prime factor of `M q` with `q` prime is strictly larger than `q`.

The order of `2` modulo such a `p` divides `q`, so it is `1` or `q`. It cannot be `1`, since
that would give `p ∣ 2 - 1 = 1`. So it is `q`, and Fermat's little theorem puts it below
`p - 1`. -/
theorem lt_of_prime_dvd_mersenne_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpd : p ∣ 2 ^ q - 1) : q < p := by
  have : Fact p.Prime := ⟨hp⟩
  -- `p` is odd: a Mersenne number is odd, so `2` cannot divide it.
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hodd : Odd (2 ^ q - 1) := by
      have h1 : (1 : ℕ) ≤ 2 ^ q := Nat.one_le_two_pow
      have h2 : 2 ∣ 2 ^ q := dvd_pow_self 2 hq.ne_zero
      rcases h2 with ⟨c, hc⟩
      refine ⟨c - 1, ?_⟩
      omega
    rw [Nat.odd_iff] at hodd
    omega
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by push_cast; exact h)
    rcases (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two p hdvd2) with h' | h'
    · exact hp.one_lt.ne' h'
    · exact hp2 h'
  have hdvd : orderOf (2 : ZMod p) ∣ q := (dvd_mersenne_iff_orderOf_dvd hp).mp hpd
  have hdp : orderOf (2 : ZMod p) ∣ p - 1 :=
    orderOf_dvd_iff_pow_eq_one.mpr (ZMod.pow_card_sub_one_eq_one h2ne)
  rcases (Nat.Prime.eq_one_or_self_of_dvd hq _ hdvd) with h1 | h1
  · -- order `1` makes `2 = 1` in `ZMod p`, hence `p ∣ 1`
    have h2eq : (2 : ZMod p) = 1 := orderOf_eq_one_iff.mp h1
    have hd1 : p ∣ 2 ^ 1 - 1 := (dvd_mersenne_iff_pow_eq_one hp).mpr (by rw [pow_one, h2eq])
    norm_num at hd1
    exact absurd hd1 hp.one_lt.ne'
  · rw [h1] at hdp
    have hp1 : 1 < p := hp.one_lt
    have := Nat.le_of_dvd (by omega) hdp
    omega

/-- **Lifting the exponent, for Mersenne numbers.** If `p` is an odd prime dividing `M d`, then

    v_p(M (d * k)) = v_p(M d) + v_p(k).

This is Mathlib's `Nat.emultiplicity_pow_sub_pow` at `x = 2 ^ d`, `y = 1`, `n = k`, carried from
`emultiplicity` to `Nat.factorization` through `padicValNat`. The hypothesis `¬ p ∣ 2 ^ d` that
lifting-the-exponent needs is exactly oddness of `p`. -/
theorem factorization_mersenne_mul {p d k : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hd0 : d ≠ 0) (hdvd : p ∣ 2 ^ d - 1) (hk : k ≠ 0) :
    (2 ^ (d * k) - 1).factorization p
      = (2 ^ d - 1).factorization p + k.factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hodd
  have hx : ¬ p ∣ 2 ^ d := fun h => hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (hp.dvd_of_dvd_pow h))
  have hxy : p ∣ 2 ^ d - 1 ^ 1 := by simpa using hdvd
  have h2d : 2 ≤ 2 ^ d := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hd0)
  have hne1 : 2 ^ d - 1 ≠ 0 := by omega
  have h2dk : 2 ≤ 2 ^ (d * k) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (d * k) := Nat.pow_le_pow_right (by norm_num)
          (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hd0 hk))
  have hne2 : 2 ^ (d * k) - 1 ≠ 0 := by omega
  have hlte := Nat.emultiplicity_pow_sub_pow hp hpodd hxy hx k
  simp only [← pow_mul, one_pow] at hlte
  rw [← padicValNat_eq_emultiplicity hne2, ← padicValNat_eq_emultiplicity (by simpa using hne1),
      ← padicValNat_eq_emultiplicity hk] at hlte
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  exact_mod_cast hlte


/-- **The `p`-adic valuation of a Mersenne number.** For an odd prime `p`, writing
`d = ord_p(2)`:

    v_p(M m) = if d ∣ m then v_p(M d) + v_p(m) else 0.

The `else` branch is `dvd_mersenne_iff_orderOf_dvd`: if the order does not divide `m` then `p`
does not divide `M m` at all. The `then` branch is `factorization_mersenne_mul` together with
`v_p(m) = v_p(k)` for `m = d * k`, which holds because `p ∤ d` — the order divides `p - 1` and is
positive, so it is smaller than `p`. -/
theorem factorization_mersenne {p m : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hm : m ≠ 0) :
    (mersenne m).factorization p
      = if orderOf (2 : ZMod p) ∣ m
        then (mersenne (orderOf (2 : ZMod p))).factorization p + m.factorization p
        else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  set d := orderOf (2 : ZMod p) with hdef
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by push_cast; exact h)
    rcases (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two p hdvd2) with h' | h'
    · exact hp.one_lt.ne' h'
    · exact hodd h'
  have hdp : d ∣ p - 1 := orderOf_dvd_iff_pow_eq_one.mpr (ZMod.pow_card_sub_one_eq_one h2ne)
  have hp3 : 3 ≤ p := by
    rcases hp.two_le.lt_or_eq with h | h
    · omega
    · exact absurd h.symm hodd
  have hd0 : d ≠ 0 := by
    rintro h0
    rw [h0] at hdp
    have := Nat.eq_zero_of_zero_dvd hdp
    omega
  have hdlt : d < p := lt_of_le_of_lt (Nat.le_of_dvd (by omega) hdp) (by omega)
  have hpd : ¬ p ∣ d := fun h => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) h) (by omega)
  have hMd : p ∣ mersenne d := by
    rw [mersenne]
    exact (dvd_mersenne_iff_orderOf_dvd hp).mpr dvd_rfl
  by_cases hdm : d ∣ m
  · rw [ite_eq_left hdm]
    obtain ⟨k, rfl⟩ := hdm
    have hk : k ≠ 0 := by rintro rfl; simp at hm
    rw [mersenne, mersenne]
    rw [factorization_mersenne_mul hp hodd hd0 (by simpa [mersenne] using hMd) hk]
    congr 1
    rw [Nat.factorization_mul hd0 hk]
    simp [Nat.factorization_eq_zero_of_not_dvd hpd]
  · rw [ite_eq_right hdm]
    refine Nat.factorization_eq_zero_of_not_dvd ?_
    rw [mersenne]
    exact fun h => hdm ((dvd_mersenne_iff_orderOf_dvd hp).mp h)

/-- **A Mersenne number with prime exponent has trivial factorial part below that exponent.**
For `q` prime and `k < q`, `gcd (M q) (k !) = 1`.

Every prime factor of `M q` exceeds `q` (`lt_of_prime_dvd_mersenne_prime`), while every prime
factor of `k !` is at most `k < q`. No prime divides both. -/
theorem factorialPart_mersenne_eq_one_of_prime {q k : ℕ} (hq : q.Prime) (hk : k < q) :
    factorialPart (mersenne q) k = 1 := by
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  rintro p hp hpd
  have hpM : p ∣ mersenne q := hpd.trans (factorialPart_dvd _ _)
  have hpF : p ∣ k.factorial := hpd.trans (factorialPart_dvd_factorial _ _)
  have hple : p ≤ k := (Nat.Prime.dvd_factorial hp).mp hpF
  have hlt : q < p := lt_of_prime_dvd_mersenne_prime hp hq (by simpa [mersenne] using hpM)
  omega

end ClassicalLean
