/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.NumberTheory.PrimitiveDivisor
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Data.Nat.MaxPrimeFac

/-!
# Zsigmondy's theorem for `aⁿ − 1`

A prime `p` is a *primitive divisor* of `aⁿ − 1` when it divides `aⁿ − 1` and no `aᵐ − 1` with
`0 < m < n` (`IsPrimitiveDivisor`, `NumberTheory/PrimitiveDivisor`). **Zsigmondy's theorem**:
for `2 ≤ a` and every `n`, `aⁿ − 1` has a primitive divisor exactly outside three exceptions,

    (∃ p, IsPrimitiveDivisor p a n) ↔
      ¬ ((a = 2 ∧ n = 1) ∨ (a = 2 ∧ n = 6) ∨ (n = 2 ∧ ∃ k, a + 1 = 2 ^ k))

(`exists_isPrimitiveDivisor_iff`). The three exceptions: `2¹ − 1 = 1` has no prime factor;
`2⁶ − 1 = 63 = 3² · 7`, with `3 ∣ 2² − 1` and `7 ∣ 2³ − 1`; and at `n = 2` every prime factor of
`a² − 1` divides `a − 1` exactly when `a + 1` is a power of `2`. At `n = 0` both sides hold
(`a⁰ − 1 = 0` and the minimality clause is vacuous), so the statement carries no hypothesis on `n`.

## The proof

* `n = 0, 1, 2` are elementary (`isPrimitiveDivisor_zero_iff`, `isPrimitiveDivisor_one_iff`,
  `isPrimitiveDivisor_two_iff`, and the existence forms for `n = 1` and `n = 2`), and the three
  exceptions have no
  primitive divisor (`not_isPrimitiveDivisor_base_two_one`, `not_isPrimitiveDivisor_base_two_six`,
  `not_isPrimitiveDivisor_of_add_one_eq_two_pow`).
* **The key lemma.** A prime dividing `Φₙ(a)` but not `n` is primitive
  (`isPrimitiveDivisor_of_dvd_cyclotomic_eval`). A prime dividing both is the largest prime factor
  `P(n) = n.maxPrimeFac` (`eq_maxPrimeFac_of_dvd_cyclotomic_eval`): writing `n = pᵏ m` with
  `p ∤ m`, the order of `a` modulo `p` is `m`, which divides `p − 1`. For `n ≥ 3` it divides
  `Φₙ(a)` exactly once (`not_sq_dvd_cyclotomic_eval`): `Φₙ` divides `1 + x + ⋯ + x^(p−1)` with
  `x = a^(n/p)`, which Mathlib's `emultiplicity_geom_sum₂_eq_one` bounds for odd `p`; for `p = 2`,
  `n` is a power of `2` and the sum is `1 + x ≡ 2 (mod 4)`. It fails at `n = 2`: `4 ∣ Φ₂(3)`.
  Together: if `|Φₙ(a)| > P(n)` then a primitive divisor exists
  (`exists_isPrimitiveDivisor_of_maxPrimeFac_lt`).
* **Bases `a ≥ 3`.** `P ≤ 2^(P−1) ≤ 2^φ(n) ≤ (a − 1)^φ(n) < |Φₙ(a)|`, the last step Mathlib's
  `sub_one_pow_totient_lt_natAbs_cyclotomic_eval` (`maxPrimeFac_lt_natAbs_cyclotomic_eval`,
  `exists_isPrimitiveDivisor_iff_of_three_le`).
* **Base `2`.** Mathlib's lower bound gives only `(2 − 1)^φ(n) = 1` here, and this library's
  records called the case a blocker. It is not one, and the prior art already shows how (see
  below): with `n = m P`, the expansion identities `cyclotomic_expand_eq_cyclotomic` (`P ∣ m`) and
  `cyclotomic_expand_eq_cyclotomic_mul` (`P ∤ m`) move the evaluation to base `2^P`; Mathlib's
  lower bound `sub_one_pow_totient_lt_cyclotomic_eval` there and its upper bound
  `cyclotomic_eval_lt_add_one_pow_totient` at base `2` give `Φₙ(2) > P(n)` for `n > 1`,
  `n ≠ 6` (`maxPrimeFac_lt_eval_two_cyclotomic`). The four cases are `P ∣ m`, `m = 1` and
  `m = 2` (exact values; at `m = 2`, `n ≠ 6` forces `P ≥ 5`), and `m ≥ 3` (where `P ≥ 3`,
  `φ(m) ≥ 2` and `(2^P − 1)² ≥ 9 P`). Then `exists_isPrimitiveDivisor_base_two`.

## Hypotheses that are proof-route, not sharp

Measured by the cold statement review (order G-6, round 22) and kept because the proofs use
them: `0 < a` in `isPrimitiveDivisor_of_dvd_cyclotomic_eval` (at `a = 0`, `Φₙ(0) = ±1`);
`2 ≤ a` and `p ∣ Φₙ(a)` in `not_sq_dvd_cyclotomic_eval`, whose `3 ≤ n` only excludes `n = 2`;
`2 ≤ a` in `exists_isPrimitiveDivisor_of_maxPrimeFac_lt`, whose `3 ≤ n` only excludes `n = 2`;
`1 < n` in `maxPrimeFac_lt_natAbs_cyclotomic_eval`; and in the two base-`2` statements the
bounds on `n` only exclude `n = 1`. (Dropping the bounds on `n` reaches `Nat.maxPrimeFac`'s
junk values `0 ↦ 0` and `1 ↦ 1`, at which those statements still hold.) The final theorem's
`2 ≤ a` is needed: at `a = 0` and `a = 1` the two sides differ at every `n ≥ 3`.

## Junk values, enumerated first

Exact integer checks, run before the proofs were written (order G-6 round 22): the `iff`
against the definition over `a = 2..200`, `n = 0..60` (12139 cells), 0 mismatches, with three
fire tests (dropping `(2, 6)`, making the line `n = 1` exceptional, dropping the `n = 2` clause)
each caught as predicted; at `a ∈ {0, 1}` it fails at every `n ≥ 3`. Over `a = 2..200`,
`n = 3..60`, the key lemma held in all 1552 cells with a prime dividing both `n` and `Φₙ(a)` (396
with `p = 2`); exactly-once fails at `n = 2` for `a ≡ 3 (mod 4)`. `Nat.maxPrimeFac`'s junk values,
`0 ↦ 0` and `1 ↦ 1`, are never reached by the statements as stated: their hypotheses force
`n ≥ 2`. `Φₙ(2) / P(n) ≥ 11/5` for `3 ≤ n ≤ 1500`, `n ≠ 6`, tightest at `n = 10`; at `n = 6`,
`Φ₆(2) = 3 = P(6)`.

## Mathlib at v4.34.0

Searched before this file was written, `grep -rniE '<pattern>' Mathlib --include=*.lean`:
`Zsigmondy`, `primitive divisor`, `primitiveDivisor`, `Bilu`, `primitive.*prime.*divisor` and
`Birkhoff.?Vandiver` 0 each; no valuation or multiplicity of a cyclotomic value
(`padicVal[A-Za-z]* .*cyclotomic|cyclotomic.*padicVal` 0,
`multiplicity .*cyclotomic|cyclotomic.*multiplicity` 0). Mathlib's `docs/1000.yaml` lists
Zsigmondy's theorem with
"TODO: Find the code". `Nat.maxPrimeFac` had no consumer in Mathlib.

## Prior art

Two Lean formalisations are known (`ROADMAP.md` §2.5), and neither is in Mathlib: Mantas
Bakšys's Lean 3 proof (branch `zsigmondy` of `leanprover-community/mathlib3`, commit `48ba6fa`,
"finally proved!", 2022-12-20; `theorem zsigmondy` for coprime `a > b > 0`, `n ≥ 3`,
`(a, b, n) ≠ (2, 1, 6)`), and its Lean 4 port, mathlib4 pull request #28895 (authors in its header
Mantas Bakšys, Yury Kudryashov and Alex Best), closed unmerged according to `ROADMAP.md` §2.5.
Both are Apache-2.0. Both reach `Φₙ(a) > P(n)` by the classical route used here: the Lean 3 proof
handles `a = b + 1`, which contains `a = 2`, through the same expansion identities
(`proposition_1` to `proposition_3`), and #28895 through `zsigmondy_aux`. The proofs in this file
were written and compiled before either source was fetched, and nothing in them is adapted from
the source code.

**Dated 2026-09-24 (order G-8, J2; round 25):** the two-variable declarations order G-8 adds to
this file (the definition and its translations to `orderOf` and to the rank of apparition) were
derived here, on the pattern of `isPrimitiveDivisor_iff_orderOf`, with both sources known; no
code was adapted.
The route of `NumberTheory/ZsigmondyPowSubPow` and its sources are in that module's docstring.

## The order of `2` (dated 2026-09-24, order G-7, J2 step 5; round 23)

Read through `isPrimitiveDivisor_iff_orderOf`, the base-`2` case says which numbers are the order
of `2` modulo a prime: **every `n` except `1` and `6`** (`exists_prime_orderOf_two_eq_iff`). At
`n = 0` the prime is `2`, where `(2 : ZMod 2) = 0` and `orderOf 0 = 0` (Mathlib's junk value).
Its corollary: for every `n ≥ 2` some prime `p ≡ 1 (mod n)` divides `2 ^ n - 1`
(`exists_prime_dvd_two_pow_sub_one_modEq_one`), through `MersenneOrder`'s
`dvd_mersenne_iff_orderOf_dvd`; at `n = 6`, where no prime has order `6`, the prime is `7`. Checked
first by factoring `2ⁿ − 1` exactly for `1 ≤ n ≤ 90` (round 23). Searched first: `orderOf \(2` 0
and `zsigmondy` 0 in Mathlib.

## Two variables (dated 2026-09-24, order G-8, J2; round 25)

`IsPrimitiveDivisor₂ p a b n`: a prime `p` divides `aⁿ − bⁿ` and no earlier `aᵐ − bᵐ`, the
classical definition over `ℕ`, with `IsPrimitiveDivisor` its case `b = 1`
(`isPrimitiveDivisor₂_with_one`). For `b ≤ a`, `p` not dividing both, and `0 < n`, it says that
`a / b` has order `n` in `ZMod p` (`isPrimitiveDivisor₂_iff_orderOf`).
For a prime `p`, `0 < n` and `¬ p ∣ a - b`, it says that `n` is the rank of apparition of `p` in the
Lucas sequence `U(a + b, ab)` (`isPrimitiveDivisor₂_iff_lucasApparition`) — the first use of
`NumberTheory/LucasApparition` by a declaration outside that file.
The two-variable form of Zsigmondy's theorem, its sum clause, and which `n` are ranks of
apparition in `U(a + b, ab)` are in `NumberTheory/ZsigmondyPowSubPow`.
-/

namespace ClassicalLean

open Polynomial

/-! ### `n = 0`, `n = 1` and `n = 2` -/

/-- At `n = 0` every prime is a primitive divisor: `a⁰ − 1 = 0`, and no `m` has `0 < m < 0`. -/
theorem isPrimitiveDivisor_zero_iff {p a : ℕ} : IsPrimitiveDivisor p a 0 ↔ p.Prime := by
  simp [IsPrimitiveDivisor]

/-- At `n = 1` a primitive divisor is a prime factor of `a − 1`; no hypothesis on `a`. -/
theorem isPrimitiveDivisor_one_iff {p a : ℕ} : IsPrimitiveDivisor p a 1 ↔ p.Prime ∧ p ∣ a - 1 := by
  constructor
  · rintro ⟨hp, hd, -⟩
    exact ⟨hp, by simpa using hd⟩
  · rintro ⟨hp, hd⟩
    exact ⟨hp, by simpa using hd, fun m h0 h1 => absurd h1 (by omega)⟩

/-- `a¹ − 1` has a primitive divisor unless `a = 2`: the exceptional pair is `(2, 1)`, not the
line `n = 1` (at `a = 0, 1`, `a − 1` truncates to `0`, which every prime divides). -/
theorem exists_isPrimitiveDivisor_one_iff (a : ℕ) : (∃ p, IsPrimitiveDivisor p a 1) ↔ a ≠ 2 := by
  simp only [isPrimitiveDivisor_one_iff]
  constructor
  · rintro ⟨p, hp, hd⟩ rfl
    exact hp.one_lt.ne' (Nat.dvd_one.mp (by simpa using hd))
  · intro ha
    exact Nat.exists_prime_and_dvd (by omega)

/-- At `n = 2` a primitive divisor is an odd prime factor of `a + 1`: `a² − 1 = (a + 1)(a − 1)`,
and a prime dividing both `a + 1` and `a − 1` divides `2`. No hypothesis on `a`. -/
theorem isPrimitiveDivisor_two_iff {p a : ℕ} :
    IsPrimitiveDivisor p a 2 ↔ p.Prime ∧ p ∣ a + 1 ∧ p ≠ 2 := by
  have hsq : a ^ 2 - 1 = (a + 1) * (a - 1) := by
    simpa using Nat.sq_sub_sq a 1
  constructor
  · rintro ⟨hp, hd, hmin⟩
    have h1 : ¬ p ∣ a - 1 := by simpa using hmin 1 one_pos one_lt_two
    rw [hsq] at hd
    have hp1 : p ∣ a + 1 := (hp.dvd_mul.mp hd).resolve_right h1
    refine ⟨hp, hp1, fun h2 => h1 ?_⟩
    subst h2
    omega
  · rintro ⟨hp, hp1, hp2⟩
    refine ⟨hp, hsq ▸ Dvd.dvd.mul_right hp1 _, fun m h0 h2 hm => ?_⟩
    obtain rfl : m = 1 := by omega
    rw [pow_one] at hm
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · exact hp.one_lt.ne' (Nat.dvd_one.mp (by simpa using hp1))
    · have h2' : p ∣ (a + 1) - (a - 1) := Nat.dvd_sub hp1 hm
      rw [show (a + 1) - (a - 1) = 2 by omega] at h2'
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2')

/-- `a² − 1` has a primitive divisor exactly when `a + 1` is not a power of `2`. -/
theorem exists_isPrimitiveDivisor_two_iff (a : ℕ) :
    (∃ p, IsPrimitiveDivisor p a 2) ↔ ¬ ∃ k, a + 1 = 2 ^ k := by
  simp only [isPrimitiveDivisor_two_iff]
  constructor
  · rintro ⟨p, hp, hd, h2⟩ ⟨k, hk⟩
    rw [hk] at hd
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  · intro h
    rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (a + 1) with h' | ⟨p, hp, hd, hodd⟩
    · exact absurd h' h
    · exact ⟨p, hp, hd, fun h2 => by subst h2; exact (Nat.not_even_iff_odd.mpr hodd) even_two⟩

/-! ### The three exceptions have no primitive divisor -/

/-- `2¹ − 1 = 1` has no prime factor. -/
theorem not_isPrimitiveDivisor_base_two_one (p : ℕ) : ¬ IsPrimitiveDivisor p 2 1 := by
  rw [isPrimitiveDivisor_one_iff]
  rintro ⟨hp, hd⟩
  exact hp.one_lt.ne' (Nat.dvd_one.mp hd)

/-- `2⁶ − 1 = 63 = 3² · 7`, and `3 ∣ 2² − 1`, `7 ∣ 2³ − 1`. -/
theorem not_isPrimitiveDivisor_base_two_six (p : ℕ) : ¬ IsPrimitiveDivisor p 2 6 := by
  rintro ⟨hp, hd, hmin⟩
  have h3 : ¬ p ∣ 3 := by simpa using hmin 2 (by norm_num) (by norm_num)
  have h7 : ¬ p ∣ 7 := by simpa using hmin 3 (by norm_num) (by norm_num)
  have h63 : p ∣ 3 ^ 2 * 7 := by simpa using hd
  rcases hp.dvd_mul.mp h63 with h | h
  · exact h3 (hp.dvd_of_dvd_pow h)
  · exact h7 h

/-- When `a + 1` is a power of `2`, every prime factor of `a² − 1` divides `a − 1`. -/
theorem not_isPrimitiveDivisor_of_add_one_eq_two_pow {p a k : ℕ} (h : a + 1 = 2 ^ k) :
    ¬ IsPrimitiveDivisor p a 2 :=
  fun hP => (exists_isPrimitiveDivisor_two_iff a).mp ⟨p, hP⟩ ⟨k, h⟩

/-! ### The key lemma -/

/-- Any `p` with `(p : ℤ) ∣ Φₙ(a)` makes `a` a root of `Φₙ` over `ZMod p`. No hypothesis: `p`
need not be prime, and at `p = 0`, `ZMod 0 = ℤ`. The cast chain of
`exists_isPrimitiveDivisor_of_forall_prime_dvd`, as a lemma. -/
theorem isRoot_cyclotomic_of_dvd_eval {p a n : ℕ}
    (h : (p : ℤ) ∣ eval (a : ℤ) (cyclotomic n ℤ)) :
    IsRoot (cyclotomic n (ZMod p)) (Nat.castRingHom (ZMod p) a) := by
  have hc : ((a : ℤ) : ZMod p) = ↑(Int.castRingHom (ZMod p) a) := by simp
  rw [IsRoot.def, ← map_cyclotomic_int n (ZMod p), eval_map, Nat.coe_castRingHom,
    ← Int.cast_natCast, hc, eval₂_hom, Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact h

/-- **A prime dividing `Φₙ(a)` but not `n` is a primitive divisor of `aⁿ − 1`.** `0 < a` is
proof-route (at `a = 0`, `Φₙ(0) = ±1` and the hypothesis cannot hold). -/
theorem isPrimitiveDivisor_of_dvd_cyclotomic_eval {p a n : ℕ} (hp : p.Prime) (ha : 0 < a)
    (hpn : ¬ p ∣ n) (h : (p : ℤ) ∣ eval (a : ℤ) (cyclotomic n ℤ)) :
    IsPrimitiveDivisor p a n := by
  have : Fact p.Prime := ⟨hp⟩
  have hn : 0 < n := Nat.pos_of_ne_zero fun h0 => hpn (h0 ▸ dvd_zero p)
  exact (isPrimitiveDivisor_iff_orderOf hp ha hn).mpr
    (orderOf_eq_of_isRoot_cyclotomic hpn (isRoot_cyclotomic_of_dvd_eval h))

/-- A prime dividing `Φₙ(a)` splits `n` as `p ^ k * m` with `p ∤ m`, and the order of `a`
modulo `p` is `m`, which divides `p − 1`. `n ≠ 0` is proof-route (`Φ₀ = 1`). -/
private theorem exists_orderOf_of_dvd_cyclotomic_eval {p a n : ℕ} (hp : p.Prime) (hn0 : n ≠ 0)
    (h : (p : ℤ) ∣ eval (a : ℤ) (cyclotomic n ℤ)) :
    ∃ k m, ¬ p ∣ m ∧ n = p ^ k * m ∧ m ∣ p - 1 ∧ orderOf (a : ZMod p) = m := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.one_lt.ne'
  have hroot := isRoot_cyclotomic_of_dvd_eval h
  have : NeZero ((m : ZMod p)) := NeZero.of_not_dvd (ZMod p) hm
  have hprim : IsPrimitiveRoot (Nat.castRingHom (ZMod p) a) m :=
    isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp hroot
  have hm0 : m ≠ 0 := fun h0 => hm (h0 ▸ dvd_zero p)
  have hord : orderOf (a : ZMod p) = m := by simpa using hprim.eq_orderOf.symm
  have ha0 : (a : ZMod p) ≠ 0 := by simpa using hprim.ne_zero hm0
  exact ⟨k, m, hm, rfl, hord ▸ ZMod.orderOf_dvd_card_sub_one ha0, hord⟩

/-- **A prime dividing both `n` and `Φₙ(a)` is the largest prime factor of `n`.** With
`n = pᵏ m`, `p ∤ m`, the order `m` of `a` modulo `p` divides `p − 1`, so every prime factor of `n`
is at most `p`. No hypothesis on `a` or `n`. -/
theorem eq_maxPrimeFac_of_dvd_cyclotomic_eval {p a n : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (h : (p : ℤ) ∣ eval (a : ℤ) (cyclotomic n ℤ)) : p = n.maxPrimeFac := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [cyclotomic_zero, eval_one] at h
    exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h)
  obtain ⟨k, m, hm, hnk, hmp, -⟩ := exists_orderOf_of_dvd_cyclotomic_eval hp hn0 h
  have hm0 : m ≠ 0 := fun h0 => hm (h0 ▸ dvd_zero p)
  have hmlt : m < p := by
    have := Nat.le_of_dvd (by have := hp.two_le; omega) hmp
    omega
  have hn1 : 1 < n := lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn)
  refine le_antisymm (Nat.le_maxPrimeFac hn0 hp hpn) ((Nat.maxPrimeFac_le_iff hn1).2 ?_)
  intro q hq hqn
  rw [hnk] at hqn
  rcases hq.dvd_mul.mp hqn with h1 | h1
  · exact ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h1)).le
  · exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) h1).trans hmlt.le

/-- **For `n ≥ 3`, a prime dividing both `n` and `Φₙ(a)` divides `Φₙ(a)` exactly once.**
`Φₙ(a)` divides `1 + x + ⋯ + x^(p−1)`, `x = a^(n/p)`: for odd `p` that sum has `p`-adic
multiplicity one (`emultiplicity_geom_sum₂_eq_one`); for `p = 2`, `n` is a power of `2` and the sum
is `1 + x ≡ 2 (mod 4)`. It fails at `n = 2` (`4 ∣ Φ₂(3)`). `2 ≤ a` and `p ∣ Φₙ(a)` are
proof-route. -/
theorem not_sq_dvd_cyclotomic_eval {p a n : ℕ} (hp : p.Prime) (ha : 2 ≤ a) (hn : 3 ≤ n)
    (hpn : p ∣ n) (h : (p : ℤ) ∣ eval (a : ℤ) (cyclotomic n ℤ)) :
    ¬ (p : ℤ) ^ 2 ∣ eval (a : ℤ) (cyclotomic n ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : n ≠ 0 := by omega
  obtain ⟨k, m, hm, hnk, hmp, hord⟩ := exists_orderOf_of_dvd_cyclotomic_eval hp hn0 h
  -- `n = p * d`, and `m ∣ d` because `k ≥ 1`
  obtain ⟨d, rfl⟩ := hpn
  have hd0 : 0 < d := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hn
  have hk : k ≠ 0 := by
    rintro rfl
    exact hm ⟨d, by simpa using hnk.symm⟩
  have hmd : m ∣ d := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have : p * d = p * (p ^ j * m) := by rw [hnk]; ring
    exact ⟨p ^ j, by rw [Nat.eq_of_mul_eq_mul_left hp.pos this]; ring⟩
  -- `Φₙ(a)` divides the geometric sum `∑ i < p, (a ^ d) ^ i`
  have hroot := isRoot_cyclotomic_of_dvd_eval h
  have hpa : ¬ p ∣ a :=
    hp.coprime_iff_not_dvd.mp (coprime_of_root_cyclotomic (by omega) hroot).symm
  have hdlt : d < p * d := lt_mul_left hd0 hp.one_lt
  have hG : eval (a : ℤ) (cyclotomic (p * d) ℤ) ∣ ∑ i ∈ Finset.range p, ((a : ℤ) ^ d) ^ i := by
    have h1 := eval_dvd (x := (a : ℤ)) (X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ
      (Nat.mem_properDivisors.mpr ⟨dvd_mul_left d p, hdlt⟩))
    simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one] at h1
    rw [show (a : ℤ) ^ (p * d) - 1 = ((a : ℤ) ^ d - 1) * ∑ i ∈ Finset.range p, ((a : ℤ) ^ d) ^ i
      by rw [mul_geom_sum, ← pow_mul, mul_comm d p]] at h1
    have hx1 : (a : ℤ) ^ d - 1 ≠ 0 := by
      have : (2 : ℤ) ≤ (a : ℤ) ^ d :=
        le_trans (by exact_mod_cast ha) (le_self_pow₀ (by exact_mod_cast (by omega : 1 ≤ a))
          hd0.ne')
      omega
    exact (mul_dvd_mul_iff_left hx1).mp h1
  intro hsq
  have hsqG := hsq.trans hG
  -- `a ^ d ≡ 1 (mod p)`
  have hpow : ((a : ZMod p)) ^ d = 1 := orderOf_dvd_iff_pow_eq_one.mp (hord ▸ hmd)
  have hxy : (p : ℤ) ∣ (a : ℤ) ^ d - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hpow, sub_self]
  rcases hp.eq_two_or_odd' with rfl | hodd
  · -- `p = 2`: `n = 2 ^ k` with `k ≥ 2`, so `d` is even, `a` is odd and `1 + a ^ d ≡ 2 (mod 4)`
    have hm1 : m = 1 := Nat.dvd_one.mp hmp
    subst hm1
    have hdeven : Even d := by
      have h2d : 2 * d = 2 ^ k := by simpa using hnk
      rcases Nat.exists_eq_succ_of_ne_zero hk with ⟨j, rfl⟩
      rcases j with _ | j
      · simp at h2d; omega
      · exact ⟨2 ^ j, by rw [pow_succ, pow_succ] at h2d; omega⟩
    obtain ⟨e, he⟩ := hdeven
    have haodd : Odd (a : ℤ) := by
      obtain ⟨t, ht⟩ := Nat.odd_iff.mpr (by omega : a % 2 = 1)
      exact ⟨t, by rw [ht]; push_cast; ring⟩
    have h4 : ((a : ℤ) ^ e) ^ 2 % 4 = 1 := Int.sq_emod_four_eq_one_of_odd (haodd.pow)
    have hx : (a : ℤ) ^ d = ((a : ℤ) ^ e) ^ 2 := by rw [he, ← pow_mul]; ring_nf
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at hsqG
    rw [hx] at hsqG
    norm_num at hsqG
    omega
  · have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hxn : ¬ (p : ℤ) ∣ (a : ℤ) ^ d := fun hdvd =>
      hpa (hp.dvd_of_dvd_pow (Int.natCast_dvd_natCast.mp (by exact_mod_cast hdvd)))
    have hem := emultiplicity_geom_sum₂_eq_one hpz hodd hxy hxn
    simp only [one_pow, mul_one] at hem
    have hlt : emultiplicity (p : ℤ) (∑ i ∈ Finset.range p, ((a : ℤ) ^ d) ^ i) < (2 : ℕ) := by
      rw [hem]; norm_num
    exact (emultiplicity_lt_iff_not_dvd.mp hlt) hsqG

/-- **If `|Φₙ(a)| > P(n)`, then `aⁿ − 1` has a primitive divisor.** Otherwise every prime factor
of `Φₙ(a)` divides `n`, so equals `P(n)` and divides `Φₙ(a)` once, and `|Φₙ(a)| ≤ P(n)`.
`2 ≤ a` is proof-route; `3 ≤ n` only excludes `n = 2`. -/
theorem exists_isPrimitiveDivisor_of_maxPrimeFac_lt {a n : ℕ} (ha : 2 ≤ a) (hn : 3 ≤ n)
    (h : n.maxPrimeFac < (eval (a : ℤ) (cyclotomic n ℤ)).natAbs) :
    ∃ p, IsPrimitiveDivisor p a n := by
  by_contra hno
  push Not at hno
  set N := (eval (a : ℤ) (cyclotomic n ℤ)).natAbs with hN
  have hP : n.maxPrimeFac.Prime := Nat.prime_maxPrimeFac_of_one_lt (by omega)
  have hN0 : N ≠ 0 := by omega
  have huniq : ∀ {q : ℕ}, q.Prime → q ∣ N → q = n.maxPrimeFac := by
    intro q hq hqN
    have hqz : (q : ℤ) ∣ eval (a : ℤ) (cyclotomic n ℤ) := Int.natCast_dvd.mpr hqN
    by_cases hqn : q ∣ n
    · exact eq_maxPrimeFac_of_dvd_cyclotomic_eval hq hqn hqz
    · exact absurd (isPrimitiveDivisor_of_dvd_cyclotomic_eval hq (by omega) hqn hqz) (hno q)
  have hNpow := Nat.eq_prime_pow_of_unique_prime_dvd hN0 huniq
  set e := N.primeFactorsList.length with he
  have he1 : e ≤ 1 := by
    by_contra he2
    push Not at he2
    have hP2 : n.maxPrimeFac ^ 2 ∣ N := by
      rw [hNpow]
      exact pow_dvd_pow _ he2
    have hPz : (n.maxPrimeFac : ℤ) ∣ eval (a : ℤ) (cyclotomic n ℤ) :=
      Int.natCast_dvd.mpr (dvd_trans (dvd_pow_self _ two_ne_zero) hP2)
    have hP2z : (n.maxPrimeFac : ℤ) ^ 2 ∣ eval (a : ℤ) (cyclotomic n ℤ) := by
      rw [← Nat.cast_pow]
      exact Int.natCast_dvd.mpr hP2
    exact not_sq_dvd_cyclotomic_eval hP ha hn Nat.maxPrimeFac_dvd hPz hP2z
  have hle : N ≤ n.maxPrimeFac := by
    rw [hNpow]
    calc n.maxPrimeFac ^ e ≤ n.maxPrimeFac ^ 1 := Nat.pow_le_pow_right hP.pos he1
      _ = n.maxPrimeFac := pow_one _
  omega

/-! ### Bases `a ≥ 3` -/

/-- For `a ≥ 3`, `|Φₙ(a)| > P(n)`: `P ≤ 2^(P−1) ≤ 2^φ(n) ≤ (a − 1)^φ(n) < |Φₙ(a)|`. `1 < n` is
proof-route (Mathlib's bound asks for it). -/
theorem maxPrimeFac_lt_natAbs_cyclotomic_eval {a n : ℕ} (ha : 3 ≤ a) (hn : 1 < n) :
    n.maxPrimeFac < (eval (a : ℤ) (cyclotomic n ℤ)).natAbs := by
  have hP := Nat.prime_maxPrimeFac_of_one_lt hn
  have hφ : n.maxPrimeFac - 1 ≤ n.totient := by
    have h1 : n.maxPrimeFac.totient ∣ n.totient := Nat.totient_dvd_of_dvd Nat.maxPrimeFac_dvd
    rw [Nat.totient_prime hP] at h1
    exact Nat.le_of_dvd (Nat.totient_pos.mpr (by omega)) h1
  have h2 : n.maxPrimeFac - 1 < 2 ^ (n.maxPrimeFac - 1) := Nat.lt_two_pow_self
  calc n.maxPrimeFac ≤ 2 ^ (n.maxPrimeFac - 1) := by omega
    _ ≤ 2 ^ n.totient := Nat.pow_le_pow_right (by norm_num) hφ
    _ ≤ (a - 1) ^ n.totient := Nat.pow_le_pow_left (by omega) _
    _ < (eval (a : ℤ) (cyclotomic n ℤ)).natAbs :=
      sub_one_pow_totient_lt_natAbs_cyclotomic_eval hn (by omega)

/-- **Zsigmondy's theorem for bases `a ≥ 3`**: the only exception is `n = 2` with `a + 1` a power
of `2`. -/
theorem exists_isPrimitiveDivisor_iff_of_three_le {a n : ℕ} (ha : 3 ≤ a) :
    (∃ p, IsPrimitiveDivisor p a n) ↔ ¬ (n = 2 ∧ ∃ k, a + 1 = 2 ^ k) := by
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n
    · exact iff_of_true ⟨2, isPrimitiveDivisor_zero_iff.mpr Nat.prime_two⟩ (by simp)
    · exact iff_of_true ((exists_isPrimitiveDivisor_one_iff a).mpr (by omega)) (by simp)
    · rw [exists_isPrimitiveDivisor_two_iff]
      simp
  · exact iff_of_true (exists_isPrimitiveDivisor_of_maxPrimeFac_lt (by omega) hn
      (maxPrimeFac_lt_natAbs_cyclotomic_eval ha (by omega))) fun h => by have := h.1; omega

/-! ### Base `2` -/

/-- `P + 2 ≤ 2 ^ P` for `P ≥ 2`. -/
private theorem add_two_le_two_pow {P : ℕ} (h : 2 ≤ P) : P + 2 ≤ 2 ^ P :=
  Nat.le_induction (by norm_num) (fun k _ ih => by rw [pow_succ]; omega) P h

/-- `2 P + 2 ≤ 2 ^ P` for `P ≥ 3`. -/
private theorem two_mul_add_two_le_two_pow {P : ℕ} (h : 3 ≤ P) : 2 * P + 2 ≤ 2 ^ P :=
  Nat.le_induction (by norm_num) (fun k _ ih => by rw [pow_succ]; omega) P h

/-- `3 P ≤ 2 ^ P` for `P ≥ 4`. -/
private theorem three_mul_le_two_pow {P : ℕ} (h : 4 ≤ P) : 3 * P ≤ 2 ^ P :=
  Nat.le_induction (by norm_num) (fun k _ ih => by rw [pow_succ]; omega) P h

/-- **`Φₙ(2) > P(n)` for `n > 1`, `n ≠ 6`.** With `n = m P`: if `P ∣ m`, `Φₙ(2) = Φₘ(2^P)`
and Mathlib's lower bound applies at base `2^P`; otherwise `Φₙ(2) Φₘ(2) = Φₘ(2^P)`, and `m = 1`,
`m = 2` (then `P ≥ 5`) are exact, while `m ≥ 3` (then `P ≥ 3`, `φ(m) ≥ 2`, `(2^P − 1)² ≥ 9 P`)
combines the lower bound at `2^P` with the upper bound at `2`. `1 < n` only excludes `n = 1`;
`n ≠ 6` is needed (`Φ₆(2) = 3 = P(6)`). -/
theorem maxPrimeFac_lt_eval_two_cyclotomic {n : ℕ} (hn : 1 < n) (h6 : n ≠ 6) :
    (n.maxPrimeFac : ℝ) < eval 2 (cyclotomic n ℝ) := by
  have hP := Nat.prime_maxPrimeFac_of_one_lt hn
  set P := n.maxPrimeFac with hPdef
  obtain ⟨m, hm⟩ : ∃ m, n = m * P := ⟨n / P, (Nat.div_mul_cancel Nat.maxPrimeFac_dvd).symm⟩
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hm; omega
  have h2P : (1 : ℝ) < 2 ^ P := one_lt_pow₀ (by norm_num) hP.ne_zero
  have hPR : (P : ℝ) + 2 ≤ 2 ^ P := by exact_mod_cast add_two_le_two_pow hP.two_le
  rw [hm]
  by_cases hdvd : P ∣ m
  · -- `Φ_{mP}(2) = Φ_m(2 ^ P) > (2 ^ P - 1) ^ φ(m) ≥ 2 ^ P - 1 > P`
    have hexp := congrArg (eval (2 : ℝ)) (cyclotomic_expand_eq_cyclotomic hP hdvd ℝ)
    rw [expand_eval] at hexp
    rw [← hexp]
    have hm2 : 2 ≤ m := le_trans hP.two_le (Nat.le_of_dvd hm0 hdvd)
    have hlt := sub_one_pow_totient_lt_cyclotomic_eval hm2 h2P
    have hle : (2 ^ P - 1 : ℝ) ≤ (2 ^ P - 1) ^ m.totient :=
      le_self_pow₀ (by linarith) (Nat.totient_pos.mpr hm0).ne'
    linarith
  · -- `Φ_{mP}(2) * Φ_m(2) = Φ_m(2 ^ P)`
    have hexp := congrArg (eval (2 : ℝ)) (cyclotomic_expand_eq_cyclotomic_mul hP hdvd ℝ)
    rw [expand_eval, eval_mul] at hexp
    have hc := cyclotomic_pos' (m * P) (by norm_num : (1 : ℝ) < 2)
    rcases (show m = 1 ∨ m = 2 ∨ 3 ≤ m by omega) with rfl | rfl | hm3
    · simp only [cyclotomic_one, eval_sub, eval_X, eval_one] at hexp
      linarith
    · have hP2 : P ≠ 2 := fun h => hdvd ⟨1, by rw [h]⟩
      have hP3 : P ≠ 3 := fun h => h6 (by rw [hm, h])
      have hP5 : 4 ≤ P := by have := hP.two_le; omega
      have h3P : (3 * P : ℝ) ≤ 2 ^ P := by exact_mod_cast three_mul_le_two_pow hP5
      simp only [cyclotomic_two, eval_add, eval_X, eval_one] at hexp
      linarith
    · -- `m ≥ 3`: `P ≥ 3`, `φ(m) ≥ 2`, and `(2 ^ P - 1) ^ φ(m) ≥ 9 P 3 ^ (φ(m) - 2) = P 3 ^ φ(m)`
      have hq := Nat.minFac_prime (show m ≠ 1 by omega)
      have hqP : m.minFac < P := by
        have hle : m.minFac ≤ P :=
          Nat.le_maxPrimeFac (by omega) hq (hm ▸ dvd_mul_of_dvd_left (Nat.minFac_dvd m) P)
        have hne : m.minFac ≠ P := fun h => hdvd (h ▸ Nat.minFac_dvd m)
        omega
      have hP3 : 3 ≤ P := by have := hq.two_le; omega
      have hφ2 : 2 ≤ m.totient := by
        have he := Nat.totient_even (show 2 < m by omega)
        have hpos := Nat.totient_pos.mpr hm0
        rcases he with ⟨t, ht⟩
        omega
      have hup := cyclotomic_eval_lt_add_one_pow_totient hm3 (by norm_num : (1 : ℝ) < 2)
      have hlow := sub_one_pow_totient_lt_cyclotomic_eval (by omega : 2 ≤ m) h2P
      have hu := cyclotomic_pos' m (by norm_num : (1 : ℝ) < 2)
      norm_num at hup
      -- `9 P ≤ (2 ^ P - 1) ^ 2` and `3 ≤ 2 ^ P - 1`
      have hN : 9 * P ≤ (2 ^ P - 1) ^ 2 := by
        have := two_mul_add_two_le_two_pow hP3
        have h1 : 2 * P + 1 ≤ 2 ^ P - 1 := by omega
        calc 9 * P ≤ (2 * P + 1) ^ 2 := by nlinarith
          _ ≤ (2 ^ P - 1) ^ 2 := Nat.pow_le_pow_left h1 2
      have hNR : (9 * P : ℝ) ≤ (2 ^ P - 1) ^ 2 := by
        have h1 : 1 ≤ 2 ^ P := Nat.one_le_two_pow
        have := (Nat.cast_le (α := ℝ)).mpr hN
        push_cast [Nat.cast_sub h1] at this
        exact this
      have hP3R : (3 : ℝ) ≤ P := by exact_mod_cast hP3
      have h3R : (3 : ℝ) ≤ 2 ^ P - 1 := by linarith
      obtain ⟨s, hs⟩ : ∃ s, m.totient = s + 2 := ⟨m.totient - 2, by omega⟩
      rw [hs] at hup hlow
      have hpow : (P : ℝ) * 3 ^ (s + 2) ≤ (2 ^ P - 1) ^ (s + 2) := by
        have h3s : (3 : ℝ) ^ s ≤ (2 ^ P - 1) ^ s := pow_le_pow_left₀ (by norm_num) h3R s
        calc (P : ℝ) * 3 ^ (s + 2) = 3 ^ s * (9 * P) := by ring
          _ ≤ 3 ^ s * (2 ^ P - 1) ^ 2 := mul_le_mul_of_nonneg_left hNR (by positivity)
          _ ≤ (2 ^ P - 1) ^ s * (2 ^ P - 1) ^ 2 :=
            mul_le_mul_of_nonneg_right h3s (by positivity)
          _ = (2 ^ P - 1) ^ (s + 2) := by ring
      by_contra hcon
      push Not at hcon
      have : eval 2 (cyclotomic (m * P) ℝ) * eval 2 (cyclotomic m ℝ) ≤ P * 3 ^ (s + 2) := by
        have := mul_le_mul hcon hup.le hu.le (by positivity)
        linarith
      linarith

/-- **`2ⁿ − 1` has a primitive divisor for `n ≥ 3`, `n ≠ 6`.** `3 ≤ n` only excludes `n = 1`. -/
theorem exists_isPrimitiveDivisor_base_two {n : ℕ} (hn : 3 ≤ n) (h6 : n ≠ 6) :
    ∃ p, IsPrimitiveDivisor p 2 n := by
  apply exists_isPrimitiveDivisor_of_maxPrimeFac_lt le_rfl hn
  have hR := maxPrimeFac_lt_eval_two_cyclotomic (by omega) h6
  have hcast : eval (2 : ℝ) (cyclotomic n ℝ) = ((eval (2 : ℤ) (cyclotomic n ℤ) : ℤ) : ℝ) := by
    simpa using cyclotomic.eval_apply (2 : ℤ) n (Int.castRingHom ℝ)
  have hpos : 0 < eval (2 : ℤ) (cyclotomic n ℤ) := cyclotomic_pos' n (by norm_num)
  rw [hcast] at hR
  have hZ : (n.maxPrimeFac : ℤ) < eval (2 : ℤ) (cyclotomic n ℤ) := by exact_mod_cast hR
  have habs : ((eval (2 : ℤ) (cyclotomic n ℤ)).natAbs : ℤ) = eval (2 : ℤ) (cyclotomic n ℤ) :=
    Int.natAbs_of_nonneg hpos.le
  simp only [Nat.cast_ofNat]
  omega

/-! ### Zsigmondy's theorem -/

/-- **Zsigmondy's theorem for `aⁿ − 1`.** For `2 ≤ a` and every `n`, `aⁿ − 1` has a primitive
divisor exactly when `(a, n)` is not `(2, 1)`, not `(2, 6)`, and not `n = 2` with `a + 1` a power
of `2`. `2 ≤ a` is needed: at `a = 0` and `a = 1` the two sides differ at every `n ≥ 3`. -/
theorem exists_isPrimitiveDivisor_iff {a n : ℕ} (ha : 2 ≤ a) :
    (∃ p, IsPrimitiveDivisor p a n) ↔
      ¬ ((a = 2 ∧ n = 1) ∨ (a = 2 ∧ n = 6) ∨ (n = 2 ∧ ∃ k, a + 1 = 2 ^ k)) := by
  rcases eq_or_lt_of_le ha with rfl | ha3
  · have h3 : ¬ ∃ k, 2 + 1 = 2 ^ k := by
      rintro ⟨k, hk⟩
      rcases k with _ | k
      · norm_num at hk
      · rw [pow_succ] at hk
        omega
    rcases (show n = 1 ∨ n = 6 ∨ n = 0 ∨ n = 2 ∨ (3 ≤ n ∧ n ≠ 6) by omega) with
      rfl | rfl | rfl | rfl | ⟨hn3, hn6⟩
    · exact iff_of_false (fun ⟨p, hp⟩ => not_isPrimitiveDivisor_base_two_one p hp) (by simp)
    · exact iff_of_false (fun ⟨p, hp⟩ => not_isPrimitiveDivisor_base_two_six p hp) (by simp)
    · exact iff_of_true ⟨2, isPrimitiveDivisor_zero_iff.mpr Nat.prime_two⟩ (by simp)
    · exact iff_of_true ((exists_isPrimitiveDivisor_two_iff 2).mpr h3) (by simpa using h3)
    · exact iff_of_true (exists_isPrimitiveDivisor_base_two hn3 hn6)
        (by rintro (⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩) <;> omega)
  · rw [exists_isPrimitiveDivisor_iff_of_three_le ha3]
    have ha2 : a ≠ 2 := by omega
    simp [ha2]

/-! ### The order of `2` modulo a prime -/

/-- **Every `n` except `1` and `6` is the order of `2` modulo some prime.** At `n = 0` the prime
is `2`, where `(2 : ZMod 2) = 0` and `orderOf 0 = 0` (Mathlib's junk value). -/
theorem exists_prime_orderOf_two_eq_iff (n : ℕ) :
    (∃ p, p.Prime ∧ orderOf (2 : ZMod p) = n) ↔ n ≠ 1 ∧ n ≠ 6 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine iff_of_true ⟨2, Nat.prime_two, ?_⟩ (by omega)
    rw [show (2 : ZMod 2) = 0 from rfl, orderOf_zero]
  · have key : (∃ p, p.Prime ∧ orderOf (2 : ZMod p) = n) ↔ ∃ p, IsPrimitiveDivisor p 2 n := by
      constructor
      · rintro ⟨p, hp, h⟩
        exact ⟨p, (isPrimitiveDivisor_iff_orderOf hp (by norm_num) hn).mpr (by exact_mod_cast h)⟩
      · rintro ⟨p, hpd⟩
        exact ⟨p, hpd.1, by
          exact_mod_cast (isPrimitiveDivisor_iff_orderOf hpd.1 (by norm_num) hn).mp hpd⟩
    rw [key, exists_isPrimitiveDivisor_iff le_rfl]
    have h3 : ¬ ∃ k, 2 + 1 = 2 ^ k := by
      rintro ⟨k, hk⟩
      rcases k with _ | k
      · norm_num at hk
      · rw [pow_succ] at hk
        omega
    constructor
    · intro h
      exact ⟨fun h1 => h (Or.inl ⟨rfl, h1⟩), fun h6 => h (Or.inr (Or.inl ⟨rfl, h6⟩))⟩
    · rintro ⟨h1, h6⟩ (⟨-, h⟩ | ⟨-, h⟩ | ⟨-, hk⟩)
      · exact h1 h
      · exact h6 h
      · exact h3 hk

/-- For every `n ≥ 2` some prime `p ≡ 1 (mod n)` divides `2 ^ n - 1`; at `n = 6` it is `7`. -/
theorem exists_prime_dvd_two_pow_sub_one_modEq_one {n : ℕ} (hn : 2 ≤ n) :
    ∃ p, p.Prime ∧ p ∣ 2 ^ n - 1 ∧ p ≡ 1 [MOD n] := by
  by_cases h6 : n = 6
  · subst h6
    exact ⟨7, by norm_num, by norm_num, by decide⟩
  obtain ⟨p, hp, hord⟩ := (exists_prime_orderOf_two_eq_iff n).mpr ⟨by omega, h6⟩
  have := Fact.mk hp
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    rw [h, orderOf_zero] at hord
    omega
  refine ⟨p, hp, (dvd_mersenne_iff_orderOf_dvd hp).mpr (by rw [hord]), ?_⟩
  have hdvd : n ∣ p - 1 := by
    rw [← hord]
    exact ZMod.orderOf_dvd_card_sub_one h2
  exact ((Nat.modEq_iff_dvd' hp.one_le).mpr hdvd).symm

/-! ### Two variables: `aⁿ − bⁿ` (dated 2026-09-24, order G-8, J2; round 25) -/

/-- `p` is a **primitive prime divisor** of `aⁿ − bⁿ`: it divides `aⁿ − bⁿ` and divides no
earlier `aᵐ − bᵐ`. The classical definition verbatim, over `ℕ` with truncated subtraction, as
`IsPrimitiveDivisor` is (which is the case `b = 1`, `isPrimitiveDivisor₂_with_one`); each theorem
carries the hypotheses it needs. Its junk set: at `n = 0` every prime is one (`a⁰ − b⁰ = 0`, and
no `m` has `0 < m < 0`); when `a ≤ b` every `aᵐ − bᵐ` truncates to `0`, so every prime is one at
`n = 1` and none is at `n ≥ 2`; when `b ≤ a` nothing truncates. -/
def IsPrimitiveDivisor₂ (p a b n : ℕ) : Prop :=
  p.Prime ∧ p ∣ a ^ n - b ^ n ∧ ∀ m : ℕ, 0 < m → m < n → ¬ p ∣ a ^ m - b ^ m

/-- At `b = 1`, the library's `IsPrimitiveDivisor`. No hypotheses. -/
theorem isPrimitiveDivisor₂_with_one {p a n : ℕ} :
    IsPrimitiveDivisor₂ p a 1 n ↔ IsPrimitiveDivisor p a n := by
  simp [IsPrimitiveDivisor₂, IsPrimitiveDivisor]

/-- The cast step: for `b ≤ a` the truncated subtraction is harmless. -/
private theorem dvd_pow_sub_pow_iff_cast {p a b m : ℕ} (hba : b ≤ a) :
    p ∣ a ^ m - b ^ m ↔ (a : ZMod p) ^ m = (b : ZMod p) ^ m := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.pow_le_pow_left hba m), sub_eq_zero]
  push_cast
  rfl

/-- **The order translation.** For `b ≤ a`, `p` not dividing both, and `0 < n`: `p` is a primitive
divisor of `aⁿ − bⁿ` exactly when `a / b` has order `n` modulo `p`. When `p ∣ b` (so `p ∤ a`) both
sides are false: `a / b = a * 0⁻¹ = 0` has order `0`, and `p ∤ aⁿ`. `[Fact p.Prime]` is there
because `/` on `ZMod p` comes from its `Field` instance. Every hypothesis is needed (order G-8
J1's cells): `b ≤ a` (8,898 of 114,437 cells fail without it), `0 < n` (4,777 of 6,323), and
`¬ (p ∣ a ∧ p ∣ b)` (337 of 6,403) — the last is load-bearing only at `n = 1` (all 337 failures;
for `n ≥ 2`, a prime dividing both makes both sides false; the split by `n` is order G-8's
statement review's), and it is the weakest hypothesis that does not mention `n`. -/
theorem isPrimitiveDivisor₂_iff_orderOf {p a b n : ℕ} [Fact p.Prime] (hba : b ≤ a)
    (hab : ¬ (p ∣ a ∧ p ∣ b)) (hn : 0 < n) :
    IsPrimitiveDivisor₂ p a b n ↔ orderOf ((a : ZMod p) / b) = n := by
  simp only [IsPrimitiveDivisor₂, dvd_pow_sub_pow_iff_cast hba, (Fact.out : p.Prime), true_and]
  by_cases hb : (b : ZMod p) = 0
  · have ha : (a : ZMod p) ≠ 0 := fun ha =>
      hab ⟨(ZMod.natCast_eq_zero_iff _ _).mp ha, (ZMod.natCast_eq_zero_iff _ _).mp hb⟩
    rw [hb, div_zero, orderOf_zero]
    constructor
    · rintro ⟨h, -⟩
      rw [zero_pow hn.ne'] at h
      exact absurd ((pow_eq_zero_iff hn.ne').mp h) ha
    · intro h
      omega
  · have key : ∀ m : ℕ, (a : ZMod p) ^ m = (b : ZMod p) ^ m ↔ ((a : ZMod p) / b) ^ m = 1 :=
      fun m => by rw [div_pow, div_eq_one_iff_eq (pow_ne_zero m hb)]
    simp only [key]
    rw [orderOf_eq_iff hn]
    exact and_congr_right fun _ => ⟨fun h m hmn hm => h m hm hmn, fun h m hm hmn => h m hmn hm⟩

/-- **The rank of apparition reads off primitive divisors.** For a prime `p`, `0 < n` and
`¬ p ∣ a - b`: `p` is a primitive divisor of `aⁿ − bⁿ` exactly when `n` is the rank of apparition
of `p` in the Lucas sequence `U(a + b, ab)` over `ZMod p`. No coprimality and no `b < a`: the
hypothesis `¬ p ∣ a - b` contains `b < a` through truncated subtraction (`a - b = 0` otherwise), and
rules out `p` dividing both. It is `isPrimitiveDivisor₂_iff_orderOf` composed with
`lucasApparition_add_mul_eq_orderOf_div` over `ZMod p`. All three hypotheses are needed:
`p.Prime` (order G-8's statement review: 1,819 of 81,384 cells over composite moduli fail), and, in
order G-8 J1's cells, `0 < n` (5,860 of 7,914) and `¬ p ∣ a - b` (18,454 of 253,848); and
`¬ p ∣ a - b` is the weakest that does not mention `n` (at `n = 1` all 10,577 cells with
`p ∣ a - b` fail; order G-8's statement review). -/
theorem isPrimitiveDivisor₂_iff_lucasApparition {p a b n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hpab : ¬ p ∣ a - b) :
    IsPrimitiveDivisor₂ p a b n ↔ lucasApparition (a + b : ZMod p) (a * b : ZMod p) = n := by
  have : Fact p.Prime := ⟨hp⟩
  have hba : b < a := by
    by_contra h
    exact hpab (by rw [Nat.sub_eq_zero_of_le (not_lt.mp h)]; exact dvd_zero p)
  have hab : ¬ (p ∣ a ∧ p ∣ b) := fun h => hpab (Nat.dvd_sub h.1 h.2)
  have hne : (a : ZMod p) ≠ b := by
    intro h
    apply hpab
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hba.le, h, sub_self]
  rw [isPrimitiveDivisor₂_iff_orderOf hba.le hab hn, lucasApparition_add_mul_eq_orderOf_div hne]

/-- `PrimitiveDivisor`'s Mersenne example without its `p ≠ 2`: the three notions — primitive
divisor of `2ⁿ − 1`, rank of apparition in `U(3, 2)`, and (through
`lucasApparition_add_mul_eq_orderOf_div`) the order of `2` — agree at every prime, because
`¬ p ∣ 2 - 1` always holds. -/
example {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    IsPrimitiveDivisor p 2 n ↔ lucasApparition (3 : ZMod p) 2 = n := by
  rw [← isPrimitiveDivisor₂_with_one,
    isPrimitiveDivisor₂_iff_lucasApparition hp hn (by simpa using hp.not_dvd_one)]
  norm_num

end ClassicalLean
