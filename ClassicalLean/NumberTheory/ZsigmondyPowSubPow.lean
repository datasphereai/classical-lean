/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.NumberTheory.Zsigmondy

/-!
# Zsigmondy's theorem for `aⁿ − bⁿ`

A prime `p` is a *primitive divisor* of `aⁿ − bⁿ` when it divides `aⁿ − bⁿ` and no `aᵐ − bᵐ` with
`0 < m < n` (`IsPrimitiveDivisor₂`, `NumberTheory/Zsigmondy`). **Zsigmondy's theorem**: for coprime
`0 < b < a` and every `n`, `aⁿ − bⁿ` has a primitive divisor exactly outside three exceptions,

    (∃ p, IsPrimitiveDivisor₂ p a b n) ↔
      ¬ ((n = 1 ∧ a = b + 1) ∨ (n = 2 ∧ ∃ k, a + b = 2 ^ k) ∨ (n = 6 ∧ a = 2 ∧ b = 1))

(`exists_isPrimitiveDivisor₂_iff`); and `aⁿ + bⁿ` has one — a prime dividing it and no earlier
`aᵐ + bᵐ` — exactly unless `n = 3` and `{a, b} = {1, 2}` (`2³ + 1 = 9`;
`exists_primitive_prime_dvd_pow_add_pow_iff`, for coprime positive `a ≠ b`). Together these are the
statement of `docs/1000.yaml`'s Q8074796 in full; round 22 proved the case `b = 1`
(`exists_isPrimitiveDivisor_iff`, recovered here by an `example`).

Read through `isPrimitiveDivisor₂_iff_lucasApparition`, the theorem says which `n` are ranks of
apparition in the Lucas sequence `U(a + b, ab)` for distinct coprime positive integer roots:
every `n` except `1`, and except `6` at `{a, b} = {1, 2}`
(`exists_prime_lucasApparition_add_mul_eq_iff`).

## The proof

* **The homogenised value** `Φₙ(a, b) = b^φ(n) Φₙ(a / b)` (`cyclotomicHomogenized`), written
  directly as `∑ₖ cₖ aᵏ b^(φ(n) − k)` from the coefficients of `Φₙ`, so this module needs no import
  beyond `NumberTheory/Zsigmondy`. In a field where `b ≠ 0` it is `Φₙ(a / b) · b^φ(n)`
  (`cast_cyclotomicHomogenized`), and `∏_{d ∣ n} Φ_d(a, b) = aⁿ − bⁿ` for `0 < n` and `b ≠ 0`
  (`prod_cyclotomicHomogenized`).
* **Round 22's lemmas at `a / b`.** A prime of `Φₙ(a, b)` not dividing `n` is primitive
  (`isPrimitiveDivisor₂_of_dvd_cyclotomicHomogenized`); one dividing `n` is `P(n) = n.maxPrimeFac`
  (`eq_maxPrimeFac_of_dvd_cyclotomicHomogenized`) and, for `n ≥ 3`, divides `Φₙ(a, b)` once
  (`not_sq_dvd_cyclotomicHomogenized`); so `|Φₙ(a, b)| > P(n)` gives a primitive divisor
  (`exists_isPrimitiveDivisor₂_of_maxPrimeFac_lt`).
* **Sizes.** For `a − b ≥ 2`: `P(n) ≤ 2^φ(n) ≤ (a − b)^φ(n) < Φₙ(a, b)`
  (`maxPrimeFac_lt_cyclotomicHomogenized_of_add_two_le`). For `a = b + 1`, with `n = m P`: the two
  expansion identities (`cyclotomicHomogenized_mul_prime_of_dvd`,
  `cyclotomicHomogenized_mul_prime_mul`) and Mathlib's bounds at `a / b`
  (`sub_pow_totient_lt_cyclotomicHomogenized`, `cyclotomicHomogenized_lt_add_pow_totient`) reduce
  `Φₙ(b + 1, b) > P(n)` to inequalities in `b` and `P`
  (`maxPrimeFac_lt_cyclotomicHomogenized_add_one`); only `(n, b) = (6, 1)` fails.
* **Small `n`**: `n = 0, 1, 2` directly (`n = 2` uses coprimality), and `(2, 1, 6)` by round 22's
  `not_isPrimitiveDivisor_base_two_six`.
* **The sum clause** from the theorem at `2n` for `n ≥ 2`, `n = 0` by the prime `2`, `n = 1` by a
  prime of `a + b`; **the Lucas reading** from the theorem and
  `isPrimitiveDivisor₂_iff_lucasApparition` for `n ≥ 3`, directly for `n ≤ 2`, and `(2, 1, 6)`
  through round 22's `not_isPrimitiveDivisor_base_two_six`.

## Sources

The route is round 22's (`NumberTheory/Zsigmondy`), which is the prior art's for this two-variable
form — Mantas Bakšys's Lean 3 proof and its Lean 4 port, mathlib4 #28895, both described in
`NumberTheory/Zsigmondy`'s docstring — credited, with no code adapted. The homogenised value, the
product formula, the four cases for `a = b + 1` with `(a, b)` in place of round 22's `(2, 1)`, the
two expansion identities in two variables, and the measurements behind every statement are
claude-ai's, in order G-8 (its §0 rows 7–10). Derived here (order G-8, J2): the bridges to fields;
the split of the case `m = 2` at `P = 3` and `P ≥ 5`, which general `b` needs (found by order G-8's
routes critic); the inequalities for `a = b + 1` with their proofs; the sum clause's route
(corrected by order G-8's delta check at `n = 0` and `n = 1`); and the rank-of-apparition
reading.

## Hypotheses and junk values

Every hypothesis of the three main theorems is needed (order G-8 J1's cells and statement review):
see each docstring. `Nat.maxPrimeFac`'s junk values (`0 ↦ 0`, `1 ↦ 1`) are never reached: every
statement that uses it has `1 < n`, or hypotheses that force it
(`eq_maxPrimeFac_of_dvd_cyclotomicHomogenized`: `p ∣ n` and `p ∣ Φₙ(a, b)`, while `Φ₀ = 1`).
Some helpers carry hypotheses their proofs use and their statements do not need (order G-8's
post-proof review): `b ≠ 0` in `prod_cyclotomicHomogenized`, `cyclotomicHomogenized_dvd` and
`cyclotomicHomogenized_mul_dvd`; `y ≠ 0` in the two expansion identities; `b < a` in
`exists_isPrimitiveDivisor₂_one_iff`; and `0 < b`, vacuous under coprimality, in the key lemma,
the `P(n)` lemma and `not_sq_dvd_cyclotomicHomogenized`.

## Mathlib at v4.34.0

Searched first (order G-8 J1, from `.lake/packages/mathlib`): `zsigmondy` 0; `primitive divisor`
0; cyclotomic and homogenize on one line 0; `orderOf` of a quotient 0. `docs/1000.yaml` lists
Q8074796 (Zsigmondy's theorem) under Mantas Bakšys, 2022, with no declaration or link
(`# TODO: Find the code`).

## Why a module of its own (dated 2026-09-24, order G-8, J2; round 25)

The order put this material in `NumberTheory/Zsigmondy` unless that file would pass about 1,300
lines; with it, it would have reached about 1,650 (`Zsigmondy` 694 lines, this module about 970),
so it is here, importing `Zsigmondy`. The definition and the two translations stayed in
`Zsigmondy`.
-/

namespace ClassicalLean

open Polynomial

/-! ### The homogenised cyclotomic value -/

/-- **The homogenised cyclotomic value** `Φₙ(a, b) = ∑ₖ cₖ aᵏ b^(φ(n) − k)`, where `cₖ` are the
coefficients of `Φₙ` (degree `φ(n)`): the integer `b^φ(n) Φₙ(a / b)`, with no division
(`cast_cyclotomicHomogenized`). Its product over the divisors of `n` is `aⁿ − bⁿ` for `0 < n`
(`prod_cyclotomicHomogenized`, stated for `b ≠ 0`). -/
noncomputable def cyclotomicHomogenized (n : ℕ) (a b : ℤ) : ℤ :=
  ∑ k ∈ Finset.range (n.totient + 1), (cyclotomic n ℤ).coeff k * a ^ k * b ^ (n.totient - k)

/-- In any field where `b ≠ 0`, `Φₙ(a, b) = Φₙ(a / b) · b^φ(n)`. -/
theorem cast_cyclotomicHomogenized {K : Type*} [Field K] (n : ℕ) (a b : ℤ) (hb : (b : K) ≠ 0) :
    (cyclotomicHomogenized n a b : K) =
      (cyclotomic n K).eval ((a : K) / b) * (b : K) ^ n.totient := by
  have hdeg : (cyclotomic n K).natDegree < n.totient + 1 := by
    rw [natDegree_cyclotomic]; omega
  rw [eval_eq_sum_range' hdeg, Finset.sum_mul, cyclotomicHomogenized]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk : k ≤ n.totient := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hc : ((cyclotomic n ℤ).coeff k : K) = (cyclotomic n K).coeff k := by
    rw [← map_cyclotomic_int n K, coeff_map, eq_intCast]
  have hsplit : (b : K) ^ n.totient = (b : K) ^ k * (b : K) ^ (n.totient - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hk]
  rw [hc, div_pow, hsplit]
  field_simp

/-- **`aⁿ − bⁿ = ∏_{d ∣ n} Φ_d(a, b)`**, for `0 < n` and `b ≠ 0` (over `ℚ`, from
`prod_cyclotomic_eq_X_pow_sub_one` and `∑_{d ∣ n} φ(d) = n`). -/
theorem prod_cyclotomicHomogenized {n : ℕ} (hn : 0 < n) {a b : ℤ} (hb : b ≠ 0) :
    ∏ d ∈ n.divisors, cyclotomicHomogenized d a b = a ^ n - b ^ n := by
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [Finset.prod_congr rfl fun d _ => cast_cyclotomicHomogenized d a b hbq,
    Finset.prod_mul_distrib, ← eval_prod, prod_cyclotomic_eq_X_pow_sub_one hn,
    Finset.prod_pow_eq_pow_sum, Nat.sum_totient]
  simp only [eval_sub, eval_pow, eval_X, eval_one]
  rw [div_pow, sub_mul, div_mul_cancel₀ _ (pow_ne_zero n hbq), one_mul]

/-- `Φₙ(a, b) ∣ aⁿ − bⁿ` for `0 < n`, `b ≠ 0`. -/
theorem cyclotomicHomogenized_dvd {n : ℕ} (hn : 0 < n) {a b : ℤ} (hb : b ≠ 0) :
    cyclotomicHomogenized n a b ∣ a ^ n - b ^ n := by
  rw [← prod_cyclotomicHomogenized hn hb]
  exact Finset.dvd_prod_of_mem _ (Nat.mem_divisors_self n hn.ne')

/-- For a proper divisor `d` of `n`, `Φₙ(a, b) · (aᵈ − bᵈ) ∣ aⁿ − bⁿ` (`b ≠ 0`). -/
theorem cyclotomicHomogenized_mul_dvd {n d : ℕ} (hn : 0 < n) (hd : d ∣ n) (hdn : d < n)
    {a b : ℤ} (hb : b ≠ 0) :
    cyclotomicHomogenized n a b * (a ^ d - b ^ d) ∣ a ^ n - b ^ n := by
  have hd0 : 0 < d :=
    Nat.pos_of_ne_zero (by rintro rfl; exact hn.ne' (Nat.eq_zero_of_zero_dvd hd))
  have hnd : n ∉ d.divisors := fun h => absurd (Nat.divisor_le h) (not_le.mpr hdn)
  rw [← prod_cyclotomicHomogenized hn hb, ← prod_cyclotomicHomogenized hd0 hb,
    ← Finset.prod_insert (f := fun e => cyclotomicHomogenized e a b) hnd]
  apply Finset.prod_dvd_prod_of_subset
  intro e he
  rcases Finset.mem_insert.mp he with rfl | he
  · exact Nat.mem_divisors_self e hn.ne'
  · exact Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors he).trans hd, hn.ne'⟩

/-! ### The key lemma, and the prime `P(n)`, in two variables -/

/-- For coprime `a`, `b` with `0 < b` and `0 < n`, no prime of `Φₙ(a, b)` divides `b`: it divides
`aⁿ − bⁿ`, so it would divide `a` too. -/
private theorem not_dvd_right_of_dvd_cyclotomicHomogenized {p a b n : ℕ} (hp : p.Prime)
    (hn : 0 < n) (hab : a.Coprime b) (hb : 0 < b)
    (h : (p : ℤ) ∣ cyclotomicHomogenized n a b) : ¬ p ∣ b := by
  intro hpb
  have hdvd := h.trans (cyclotomicHomogenized_dvd hn (a := (a : ℤ)) (b := (b : ℤ))
    (by exact_mod_cast hb.ne'))
  have hpbz : (p : ℤ) ∣ (b : ℤ) ^ n := dvd_pow (Int.natCast_dvd_natCast.mpr hpb) hn.ne'
  have hpa : (p : ℤ) ∣ (a : ℤ) ^ n := by simpa using dvd_add hdvd hpbz
  have hpa' : p ∣ a := hp.dvd_of_dvd_pow (Int.natCast_dvd_natCast.mp (by exact_mod_cast hpa))
  exact hp.one_lt.ne' (Nat.dvd_one.mp (hab.gcd_eq_one ▸ Nat.dvd_gcd hpa' hpb))

/-- A prime `p ∤ b` dividing `Φₙ(a, b)` makes `a / b` a root of `Φₙ` over `ZMod p`. -/
private theorem isRoot_of_dvd_cyclotomicHomogenized {p a b n : ℕ} [Fact p.Prime] (hpb : ¬ p ∣ b)
    (h : (p : ℤ) ∣ cyclotomicHomogenized n a b) :
    IsRoot (cyclotomic n (ZMod p)) ((a : ZMod p) / b) := by
  have hb : (((b : ℤ) : ZMod p)) ≠ 0 := by
    rw [Int.cast_natCast]
    exact fun h0 => hpb ((ZMod.natCast_eq_zero_iff _ _).mp h0)
  have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
  rw [cast_cyclotomicHomogenized n _ _ hb] at h0
  simp only [Int.cast_natCast] at h0 hb
  exact (mul_eq_zero.mp h0).resolve_right (pow_ne_zero _ hb)

/-- A root of `Φₙ` over `ZMod p`, `n = pᵏ m` with `p ∤ m`, is a primitive `m`-th root, nonzero, and
`m ∣ p − 1`. `n ≠ 0` is proof-route (`Φ₀ = 1`). -/
private theorem exists_orderOf_of_isRoot_cyclotomic {p n : ℕ} [hp : Fact p.Prime] {μ : ZMod p}
    (hn0 : n ≠ 0) (hroot : IsRoot (cyclotomic n (ZMod p)) μ) :
    ∃ k m, ¬ p ∣ m ∧ n = p ^ k * m ∧ m ∣ p - 1 ∧ orderOf μ = m ∧ μ ≠ 0 := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.out.one_lt.ne'
  have : NeZero ((m : ZMod p)) := NeZero.of_not_dvd (ZMod p) hm
  have hprim : IsPrimitiveRoot μ m := isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp hroot
  have hm0 : m ≠ 0 := fun h0 => hm (h0 ▸ dvd_zero p)
  have hμ : μ ≠ 0 := hprim.ne_zero hm0
  refine ⟨k, m, hm, rfl, ?_, hprim.eq_orderOf.symm, hμ⟩
  rw [hprim.eq_orderOf]
  exact ZMod.orderOf_dvd_card_sub_one hμ

/-- **A prime dividing `Φₙ(a, b)` but not `n` is a primitive divisor of `aⁿ − bⁿ`**, for coprime
`0 < b ≤ a`: `a / b` is a root of `Φₙ` modulo `p`, so it has order `n`
(`isPrimitiveDivisor₂_iff_orderOf`). -/
theorem isPrimitiveDivisor₂_of_dvd_cyclotomicHomogenized {p a b n : ℕ} (hp : p.Prime)
    (hab : a.Coprime b) (hb : 0 < b) (hba : b ≤ a) (hpn : ¬ p ∣ n)
    (h : (p : ℤ) ∣ cyclotomicHomogenized n a b) : IsPrimitiveDivisor₂ p a b n := by
  have : Fact p.Prime := ⟨hp⟩
  have hn : 0 < n := Nat.pos_of_ne_zero fun h0 => hpn (h0 ▸ dvd_zero p)
  have hpb := not_dvd_right_of_dvd_cyclotomicHomogenized hp hn hab hb h
  have : NeZero (n : ZMod p) := NeZero.of_not_dvd (ZMod p) hpn
  have hprim := isRoot_cyclotomic_iff.mp (isRoot_of_dvd_cyclotomicHomogenized hpb h)
  rw [isPrimitiveDivisor₂_iff_orderOf hba (fun h => hpb h.2) hn]
  exact hprim.eq_orderOf.symm

/-- `Φ₀(a, b) = 1`. -/
theorem cyclotomicHomogenized_zero (a b : ℤ) : cyclotomicHomogenized 0 a b = 1 := by
  simp [cyclotomicHomogenized]

/-- **A prime dividing both `n` and `Φₙ(a, b)` is the largest prime factor of `n`**, for coprime
`a`, `b` with `0 < b`: with `n = pᵏ m`, `p ∤ m`, the order `m` of `a / b` modulo `p` divides
`p − 1`. -/
theorem eq_maxPrimeFac_of_dvd_cyclotomicHomogenized {p a b n : ℕ} (hp : p.Prime)
    (hab : a.Coprime b) (hb : 0 < b) (hpn : p ∣ n)
    (h : (p : ℤ) ∣ cyclotomicHomogenized n a b) : p = n.maxPrimeFac := by
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [cyclotomicHomogenized_zero] at h
    exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h)
  have hpb := not_dvd_right_of_dvd_cyclotomicHomogenized hp (Nat.pos_of_ne_zero hn0) hab hb h
  obtain ⟨k, m, hm, hnk, hmp, -, -⟩ :=
    exists_orderOf_of_isRoot_cyclotomic hn0 (isRoot_of_dvd_cyclotomicHomogenized hpb h)
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

/-- **For `n ≥ 3`, a prime dividing both `n` and `Φₙ(a, b)` divides it exactly once**, for coprime
`0 < b < a`. With `n = p d`, `Φₙ(a, b) · (aᵈ − bᵈ) ∣ aⁿ − bⁿ = (aᵈ − bᵈ) ∑ᵢ (aᵈ)ⁱ (bᵈ)^(p−1−i)`, and
the sum has `p`-adic multiplicity one for odd `p` (`emultiplicity_geom_sum₂_eq_one`, whose two
variables are `aᵈ`, `bᵈ`); for `p = 2`, `n` is a power of `2`, `a` and `b` are odd, and the sum
`aᵈ + bᵈ` is `2` modulo `4`. It fails at `n = 2` (`4 ∣ a + b` for 327 of 651 such cells,
order G-8 J1). -/
theorem not_sq_dvd_cyclotomicHomogenized {p a b n : ℕ} (hp : p.Prime) (hab : a.Coprime b)
    (hb : 0 < b) (hba : b < a) (hn : 3 ≤ n) (hpn : p ∣ n)
    (h : (p : ℤ) ∣ cyclotomicHomogenized n a b) :
    ¬ (p : ℤ) ^ 2 ∣ cyclotomicHomogenized n a b := by
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : n ≠ 0 := by omega
  have hpb := not_dvd_right_of_dvd_cyclotomicHomogenized hp (by omega) hab hb h
  obtain ⟨k, m, hm, hnk, hmp, hord, hμ⟩ :=
    exists_orderOf_of_isRoot_cyclotomic hn0 (isRoot_of_dvd_cyclotomicHomogenized hpb h)
  obtain ⟨d, rfl⟩ := hpn
  have hd0 : 0 < d := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hn
  have hk : k ≠ 0 := by
    rintro rfl
    exact hm ⟨d, by simpa using hnk.symm⟩
  have hmd : m ∣ d := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have : p * d = p * (p ^ j * m) := by rw [hnk]; ring
    exact ⟨p ^ j, by rw [Nat.eq_of_mul_eq_mul_left hp.pos this]; ring⟩
  have hbz : (b : ZMod p) ≠ 0 := fun h0 => hpb ((ZMod.natCast_eq_zero_iff _ _).mp h0)
  have hpa : ¬ p ∣ a := fun h0 => hμ (by rw [(ZMod.natCast_eq_zero_iff _ _).mpr h0, zero_div])
  set x : ℤ := (a : ℤ) ^ d with hx
  set y : ℤ := (b : ℤ) ^ d with hy
  have hxy0 : x - y ≠ 0 := by
    have : (b : ℤ) ^ d < (a : ℤ) ^ d := pow_lt_pow_left₀ (by exact_mod_cast hba) (by positivity)
      hd0.ne'
    omega
  have hG : cyclotomicHomogenized (p * d) a b ∣ ∑ i ∈ Finset.range p, x ^ i * y ^ (p - 1 - i) := by
    have h1 := cyclotomicHomogenized_mul_dvd (n := p * d) (d := d) (by positivity)
      (dvd_mul_left d p) (lt_mul_left hd0 hp.one_lt) (a := (a : ℤ)) (b := (b : ℤ))
      (by exact_mod_cast hb.ne')
    rw [show (a : ℤ) ^ (p * d) - (b : ℤ) ^ (p * d) =
        (∑ i ∈ Finset.range p, x ^ i * y ^ (p - 1 - i)) * (x - y) by
      rw [geom_sum₂_mul, hx, hy, ← pow_mul, ← pow_mul, mul_comm d p]] at h1
    exact (mul_dvd_mul_iff_right hxy0).mp h1
  intro hsq
  have hsqG := hsq.trans hG
  have hpow : ((a : ZMod p) / b) ^ d = 1 := orderOf_dvd_iff_pow_eq_one.mp (hord ▸ hmd)
  have hpow' : (a : ZMod p) ^ d = (b : ZMod p) ^ d := by
    rwa [div_pow, div_eq_one_iff_eq (pow_ne_zero _ hbz)] at hpow
  have hxy : (p : ℤ) ∣ x - y := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hx, hy]
    push_cast
    rw [hpow', sub_self]
  rcases hp.eq_two_or_odd' with rfl | hodd
  · have hm1 : m = 1 := Nat.dvd_one.mp hmp
    subst hm1
    have hab2 : (a : ZMod 2) = b := by
      rw [orderOf_eq_one_iff, div_eq_one_iff_eq hbz] at hord
      exact hord
    have hbodd : b % 2 = 1 := Nat.two_dvd_ne_zero.mp hpb
    have haodd : a % 2 = 1 := by
      have := (ZMod.natCast_eq_natCast_iff' a b 2).mp hab2
      omega
    have hdeven : Even d := by
      have h2d : 2 * d = 2 ^ k := by simpa using hnk
      rcases Nat.exists_eq_succ_of_ne_zero hk with ⟨j, rfl⟩
      rcases j with _ | j
      · simp at h2d; omega
      · exact ⟨2 ^ j, by rw [pow_succ, pow_succ] at h2d; omega⟩
    obtain ⟨e, he⟩ := hdeven
    have hsq4 : ∀ c : ℕ, c % 2 = 1 → ((c : ℤ) ^ d) % 4 = 1 := by
      intro c hc
      have hco : Odd ((c : ℤ) ^ e) := by
        have : Odd (c : ℤ) := by
          obtain ⟨t, ht⟩ := Nat.odd_iff.mpr hc
          exact ⟨t, by rw [ht]; push_cast; ring⟩
        exact this.pow
      rw [he, show (c : ℤ) ^ (e + e) = ((c : ℤ) ^ e) ^ 2 by ring]
      exact Int.sq_emod_four_eq_one_of_odd hco
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add,
      one_mul] at hsqG
    have hx4 := hsq4 a haodd
    have hy4 := hsq4 b hbodd
    rw [← hx, ← hy] at *
    norm_num at hsqG
    omega
  · have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hxn : ¬ (p : ℤ) ∣ x := fun hdvd =>
      hpa (hp.dvd_of_dvd_pow (Int.natCast_dvd_natCast.mp (by rw [hx] at hdvd; exact_mod_cast hdvd)))
    have hem := emultiplicity_geom_sum₂_eq_one hpz hodd hxy hxn
    have hlt : emultiplicity (p : ℤ) (∑ i ∈ Finset.range p, x ^ i * y ^ (p - 1 - i)) < (2 : ℕ) := by
      rw [hem]; norm_num
    exact (emultiplicity_lt_iff_not_dvd.mp hlt) hsqG

/-- **If `|Φₙ(a, b)| > P(n)`, then `aⁿ − bⁿ` has a primitive divisor**, for coprime `0 < b < a`
and `n ≥ 3`: otherwise every prime of `Φₙ(a, b)` is `P(n)`, which divides it once. -/
theorem exists_isPrimitiveDivisor₂_of_maxPrimeFac_lt {a b n : ℕ} (hab : a.Coprime b)
    (hb : 0 < b) (hba : b < a) (hn : 3 ≤ n)
    (h : n.maxPrimeFac < (cyclotomicHomogenized n a b).natAbs) :
    ∃ p, IsPrimitiveDivisor₂ p a b n := by
  by_contra hno
  push Not at hno
  set N := (cyclotomicHomogenized n a b).natAbs with hN
  have hP : n.maxPrimeFac.Prime := Nat.prime_maxPrimeFac_of_one_lt (by omega)
  have hN0 : N ≠ 0 := by omega
  have huniq : ∀ {q : ℕ}, q.Prime → q ∣ N → q = n.maxPrimeFac := by
    intro q hq hqN
    have hqz : (q : ℤ) ∣ cyclotomicHomogenized n a b := Int.natCast_dvd.mpr hqN
    by_cases hqn : q ∣ n
    · exact eq_maxPrimeFac_of_dvd_cyclotomicHomogenized hq hab hb hqn hqz
    · exact absurd (isPrimitiveDivisor₂_of_dvd_cyclotomicHomogenized hq hab hb hba.le hqn hqz)
        (hno q)
  have hNpow := Nat.eq_prime_pow_of_unique_prime_dvd hN0 huniq
  set e := N.primeFactorsList.length with he
  have he1 : e ≤ 1 := by
    by_contra he2
    push Not at he2
    have hP2 : n.maxPrimeFac ^ 2 ∣ N := by
      rw [hNpow]
      exact pow_dvd_pow _ he2
    have hPz : (n.maxPrimeFac : ℤ) ∣ cyclotomicHomogenized n a b :=
      Int.natCast_dvd.mpr (dvd_trans (dvd_pow_self _ two_ne_zero) hP2)
    have hP2z : (n.maxPrimeFac : ℤ) ^ 2 ∣ cyclotomicHomogenized n a b := by
      rw [← Nat.cast_pow]
      exact Int.natCast_dvd.mpr hP2
    exact not_sq_dvd_cyclotomicHomogenized hP hab hb hba hn Nat.maxPrimeFac_dvd hPz hP2z
  have hle : N ≤ n.maxPrimeFac := by
    rw [hNpow]
    calc n.maxPrimeFac ^ e ≤ n.maxPrimeFac ^ 1 := Nat.pow_le_pow_right hP.pos he1
      _ = n.maxPrimeFac := pow_one _
  omega

/-! ### Sizes -/

/-- `Φₙ(x, y)` over `ℝ`, for natural `0 < y`. -/
private theorem cast_real_cyclotomicHomogenized (n : ℕ) {x y : ℕ} (hy : 0 < y) :
    ((cyclotomicHomogenized n x y : ℤ) : ℝ) =
      (cyclotomic n ℝ).eval ((x : ℝ) / y) * (y : ℝ) ^ n.totient := by
  have h := cast_cyclotomicHomogenized (K := ℝ) n (x : ℤ) (y : ℤ) (by exact_mod_cast hy.ne')
  simpa using h

/-- `0 < Φₙ(x, y)` for natural `0 < y < x`. -/
theorem cyclotomicHomogenized_pos (n : ℕ) {x y : ℕ} (hy : 0 < y) (hxy : y < x) :
    0 < cyclotomicHomogenized n x y := by
  have hq : (1 : ℝ) < x / y := by
    rw [one_lt_div (by exact_mod_cast hy)]
    exact_mod_cast hxy
  have : (0 : ℝ) < ((cyclotomicHomogenized n x y : ℤ) : ℝ) := by
    rw [cast_real_cyclotomicHomogenized n hy]
    exact mul_pos (cyclotomic_pos' n hq) (by positivity)
  exact_mod_cast this

/-- **`(x − y)^φ(m) < Φₘ(x, y)`** for `2 ≤ m`, natural `0 < y < x` (Mathlib's
`sub_one_pow_totient_lt_cyclotomic_eval` at `x / y`). -/
theorem sub_pow_totient_lt_cyclotomicHomogenized {m x y : ℕ} (hm : 2 ≤ m) (hy : 0 < y)
    (hxy : y < x) :
    ((x : ℝ) - y) ^ m.totient < ((cyclotomicHomogenized m x y : ℤ) : ℝ) := by
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hq : (1 : ℝ) < x / y := by
    rw [one_lt_div hyR]
    exact_mod_cast hxy
  rw [cast_real_cyclotomicHomogenized m hy]
  have hlow := sub_one_pow_totient_lt_cyclotomic_eval hm hq
  have heq : ((x : ℝ) - y) ^ m.totient = ((x : ℝ) / y - 1) ^ m.totient * (y : ℝ) ^ m.totient := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [heq]
  exact mul_lt_mul_of_pos_right hlow (by positivity)

/-- **`Φₘ(x, y) < (x + y)^φ(m)`** for `3 ≤ m`, natural `0 < y < x` (Mathlib's
`cyclotomic_eval_lt_add_one_pow_totient` at `x / y`). -/
theorem cyclotomicHomogenized_lt_add_pow_totient {m x y : ℕ} (hm : 3 ≤ m) (hy : 0 < y)
    (hxy : y < x) :
    ((cyclotomicHomogenized m x y : ℤ) : ℝ) < ((x : ℝ) + y) ^ m.totient := by
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hq : (1 : ℝ) < x / y := by
    rw [one_lt_div hyR]
    exact_mod_cast hxy
  rw [cast_real_cyclotomicHomogenized m hy]
  have hup := cyclotomic_eval_lt_add_one_pow_totient hm hq
  have heq : ((x : ℝ) + y) ^ m.totient = ((x : ℝ) / y + 1) ^ m.totient * (y : ℝ) ^ m.totient := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [heq]
  exact mul_lt_mul_of_pos_right hup (by positivity)

/-- `Φ₁(x, y) = x − y`. -/
theorem cyclotomicHomogenized_one (x y : ℤ) : cyclotomicHomogenized 1 x y = x - y := by
  simp [cyclotomicHomogenized, cyclotomic_one, Finset.sum_range_succ, coeff_X, coeff_one]
  ring

/-- `Φ₂(x, y) = x + y`. -/
theorem cyclotomicHomogenized_two (x y : ℤ) : cyclotomicHomogenized 2 x y = x + y := by
  simp [cyclotomicHomogenized, cyclotomic_two, Finset.sum_range_succ, coeff_X, coeff_one]
  ring

/-- **Expansion, `P ∣ m`:** `Φ_{mP}(x, y) = Φₘ(xᴾ, yᴾ)` (`cyclotomic_expand_eq_cyclotomic`), for a
prime `P` and `y ≠ 0`. -/
theorem cyclotomicHomogenized_mul_prime_of_dvd {m P : ℕ} (hP : P.Prime) (hdvd : P ∣ m)
    {x y : ℤ} (hy : y ≠ 0) :
    cyclotomicHomogenized (m * P) x y = cyclotomicHomogenized m (x ^ P) (y ^ P) := by
  have hyQ : (y : ℚ) ≠ 0 := by exact_mod_cast hy
  apply Int.cast_injective (α := ℚ)
  rw [cast_cyclotomicHomogenized _ _ _ hyQ,
    cast_cyclotomicHomogenized _ _ _ (by push_cast; exact pow_ne_zero P hyQ),
    ← cyclotomic_expand_eq_cyclotomic hP hdvd, expand_eval, mul_comm m P,
    Nat.totient_mul_of_prime_of_dvd hP hdvd]
  push_cast
  rw [div_pow, pow_mul]

/-- **Expansion, `P ∤ m`:** `Φ_{mP}(x, y) Φₘ(x, y) = Φₘ(xᴾ, yᴾ)`
(`cyclotomic_expand_eq_cyclotomic_mul`), for a prime `P` and `y ≠ 0`. -/
theorem cyclotomicHomogenized_mul_prime_mul {m P : ℕ} (hP : P.Prime) (hdvd : ¬ P ∣ m)
    {x y : ℤ} (hy : y ≠ 0) :
    cyclotomicHomogenized (m * P) x y * cyclotomicHomogenized m x y =
      cyclotomicHomogenized m (x ^ P) (y ^ P) := by
  have hyQ : (y : ℚ) ≠ 0 := by exact_mod_cast hy
  have hcop : m.Coprime P := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hP).mpr hdvd))
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_mul, cast_cyclotomicHomogenized _ _ _ hyQ, cast_cyclotomicHomogenized _ _ _ hyQ,
    cast_cyclotomicHomogenized _ _ _ (by push_cast; exact pow_ne_zero P hyQ)]
  push_cast
  have hexp := congrArg (eval ((x : ℚ) / y)) (cyclotomic_expand_eq_cyclotomic_mul hP hdvd ℚ)
  rw [expand_eval, eval_mul] at hexp
  rw [← div_pow, hexp, Nat.totient_mul hcop, Nat.totient_prime hP]
  have hP1 : 1 ≤ P := hP.one_lt.le
  have : ((y : ℚ) ^ P) ^ m.totient =
      (y : ℚ) ^ (m.totient * (P - 1)) * (y : ℚ) ^ m.totient := by
    rw [← pow_add, ← pow_mul]
    congr 1
    rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ (by omega))]
    ring
  rw [this]
  ring

/-! ### Inequalities for `a = b + 1`, derived here (order G-8 J2) -/

/-- `1 + P b (b + 1) ≤ (b + 1)ᴾ − bᴾ` for `P ≥ 3`, `b ≥ 1`: the first three binomial terms, by
induction on `P` through `(b + 1)^(P+1) − b^(P+1) = (b + 1)((b + 1)ᴾ − bᴾ) + bᴾ`. -/
private theorem one_add_mul_le_add_one_pow_sub_pow {b : ℤ} (hb : 1 ≤ b) {P : ℕ} (hP : 3 ≤ P) :
    1 + P * b * (b + 1) ≤ (b + 1) ^ P - b ^ P := by
  induction P, hP using Nat.le_induction with
  | base => norm_num; nlinarith
  | succ P hP ih =>
    have hbP : 0 ≤ b ^ P := pow_nonneg (by omega) P
    have hstep : (b + 1) ^ (P + 1) - b ^ (P + 1) = (b + 1) * ((b + 1) ^ P - b ^ P) + b ^ P := by
      ring
    rw [hstep]
    push_cast
    have hP3 : (3 : ℤ) ≤ P := by exact_mod_cast hP
    have h1 := mul_le_mul_of_nonneg_left ih (by omega : (0 : ℤ) ≤ b + 1)
    have h2 : 0 ≤ b * b * ((P : ℤ) * (b + 1) - 1) :=
      mul_nonneg (mul_nonneg (by omega) (by omega)) (by nlinarith)
    nlinarith [h1, h2, hbP]

/-- `P (2b + 1) < (b + 1)ᴾ` for `P ≥ 5`, `b ≥ 1`. -/
private theorem mul_two_mul_add_one_lt_add_one_pow {b : ℤ} (hb : 1 ≤ b) {P : ℕ} (hP : 5 ≤ P) :
    P * (2 * b + 1) < (b + 1) ^ P := by
  induction P, hP using Nat.le_induction with
  | base =>
    have hb0 : (0 : ℤ) < b := by omega
    have e : (b + 1) ^ 5 = b ^ 5 + 5 * b ^ 4 + 10 * b ^ 3 + 10 * b ^ 2 + 5 * b + 1 := by ring
    push_cast
    rw [e]
    nlinarith [pow_pos hb0 3, pow_pos hb0 4, pow_pos hb0 5, pow_pos hb0 2]
  | succ P hP ih =>
    push_cast
    rw [pow_succ]
    have hP5 : (5 : ℤ) ≤ P := by exact_mod_cast hP
    have h1 := mul_lt_mul_of_pos_right ih (by omega : (0 : ℤ) < b + 1)
    have hPb : (1 : ℤ) ≤ P * b := by nlinarith
    have h2 : ((P : ℤ) + 1) * (2 * b + 1) ≤ (P : ℤ) * (2 * b + 1) * (b + 1) := by
      nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ 2 * b + 1) (by linarith : (0 : ℤ) ≤ P * b - 1)]
    linarith

/-- `P < (b + 1)ᴾ − bᴾ` for `P ≥ 2`, `b ≥ 1`. -/
private theorem lt_add_one_pow_sub_pow {b : ℤ} (hb : 1 ≤ b) {P : ℕ} (hP : 2 ≤ P) :
    (P : ℤ) < (b + 1) ^ P - b ^ P := by
  rcases (show P = 2 ∨ 3 ≤ P by omega) with rfl | hP3
  · push_cast
    nlinarith
  · have h := one_add_mul_le_add_one_pow_sub_pow hb hP3
    have hP0 : (0 : ℤ) ≤ P := by positivity
    have : (2 : ℤ) ≤ b * (b + 1) := by nlinarith
    nlinarith

/-- `P (2b + 1)ᵏ ≤ ((b + 1)ᴾ − bᴾ)ᵏ` for `P ≥ 3`, `b ≥ 1`, `k ≥ 2`: from
`(b + 1)ᴾ − bᴾ ≥ 1 + P b (b + 1)`, which gives `(b + 1)ᴾ − bᴾ ≥ 2b + 1` and
`((b + 1)ᴾ − bᴾ)² ≥ P (2b + 1)²`. -/
private theorem mul_pow_le_add_one_pow_sub_pow_pow {b : ℤ} (hb : 1 ≤ b) {P : ℕ} (hP : 3 ≤ P)
    {k : ℕ} (hk : 2 ≤ k) :
    (P : ℤ) * (2 * b + 1) ^ k ≤ ((b + 1) ^ P - b ^ P) ^ k := by
  set D := (b + 1) ^ P - b ^ P with hD
  have h1 := one_add_mul_le_add_one_pow_sub_pow hb hP
  have hP3 : (3 : ℤ) ≤ P := by exact_mod_cast hP
  set t := b * (b + 1) with ht
  have ht2 : (2 : ℤ) ≤ t := by nlinarith
  have h1' : 1 + (P : ℤ) * t ≤ D := by rw [ht]; linarith [h1]
  have hPt : 2 * (P : ℤ) ≤ P * t := by nlinarith
  have hD1 : 2 * b + 1 ≤ D := by nlinarith
  have hsq : (2 * b + 1) ^ 2 = 4 * t + 1 := by rw [ht]; ring
  have hD2 : (P : ℤ) * (2 * b + 1) ^ 2 ≤ D ^ 2 := by
    rw [hsq]
    have hsqD : (1 + (P : ℤ) * t) ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (by positivity) h1' 2
    nlinarith
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have h0 : (0 : ℤ) ≤ 2 * b + 1 := by omega
  calc (P : ℤ) * (2 * b + 1) ^ (j + 2) = ((P : ℤ) * (2 * b + 1) ^ 2) * (2 * b + 1) ^ j := by ring
    _ ≤ D ^ 2 * D ^ j := mul_le_mul hD2 (pow_le_pow_left₀ h0 hD1 j) (by positivity) (by positivity)
    _ = D ^ (j + 2) := by ring

/-- `P(n) ≤ 2^φ(n)` for `n > 1`. -/
private theorem maxPrimeFac_le_two_pow_totient {n : ℕ} (hn : 1 < n) :
    n.maxPrimeFac ≤ 2 ^ n.totient := by
  have hP := Nat.prime_maxPrimeFac_of_one_lt hn
  have hφ : n.maxPrimeFac - 1 ≤ n.totient := by
    have h1 : n.maxPrimeFac.totient ∣ n.totient := Nat.totient_dvd_of_dvd Nat.maxPrimeFac_dvd
    rw [Nat.totient_prime hP] at h1
    exact Nat.le_of_dvd (Nat.totient_pos.mpr (by omega)) h1
  have h2 : n.maxPrimeFac - 1 < 2 ^ (n.maxPrimeFac - 1) := Nat.lt_two_pow_self
  calc n.maxPrimeFac ≤ 2 ^ (n.maxPrimeFac - 1) := by omega
    _ ≤ 2 ^ n.totient := Nat.pow_le_pow_right (by norm_num) hφ

/-- **`Φₙ(a, b) > P(n)` when `a − b ≥ 2`**, for `n > 1`, `0 < b`:
`P ≤ 2^φ(n) ≤ (a − b)^φ(n) < Φₙ(a, b)`. -/
theorem maxPrimeFac_lt_cyclotomicHomogenized_of_add_two_le {a b n : ℕ} (hb : 0 < b)
    (h2 : b + 2 ≤ a) (hn : 1 < n) :
    (n.maxPrimeFac : ℤ) < cyclotomicHomogenized n a b := by
  have hlow := sub_pow_totient_lt_cyclotomicHomogenized hn hb (by omega : b < a)
  have hP2 : ((n.maxPrimeFac : ℕ) : ℝ) ≤ 2 ^ n.totient := by
    exact_mod_cast maxPrimeFac_le_two_pow_totient hn
  have hab : (2 : ℝ) ≤ (a : ℝ) - b := by
    have : ((b + 2 : ℕ) : ℝ) ≤ a := by exact_mod_cast h2
    push_cast at this
    linarith
  have h22 : (2 : ℝ) ^ n.totient ≤ ((a : ℝ) - b) ^ n.totient :=
    pow_le_pow_left₀ (by norm_num) hab _
  have : ((n.maxPrimeFac : ℕ) : ℝ) < ((cyclotomicHomogenized n a b : ℤ) : ℝ) := by linarith
  exact_mod_cast this

/-- **`Φₙ(b + 1, b) > P(n)` for `n > 1` and `(n, b) ≠ (6, 1)`**, `0 < b`; write `a = b + 1`.
With `n = m P`,
`P = P(n)`: if `P ∣ m`, `Φₙ = Φₘ(aᴾ, bᴾ) > (aᴾ − bᴾ)^φ(m) ≥ aᴾ − bᴾ > P`; if `m = 1`,
`Φ_P = aᴾ − bᴾ > P`; if `m = 2`, `(a + b) Φ_{2P} = aᴾ + bᴾ`, `> P (a + b)` for `P ≥ 5`, and
`Φ₆(b + 1, b) = b² + b + 1 > 3` for `b ≥ 2`; if `m ≥ 3`, `Φₙ Φₘ = Φₘ(aᴾ, bᴾ)`,
`Φₘ < (a + b)^φ(m)`, `Φₘ(aᴾ, bᴾ) > (aᴾ − bᴾ)^φ(m) ≥ P (a + b)^φ(m)` (`P ≥ 3`, `φ(m) ≥ 2`).
This is round 22's base-2 argument with `(a, b)` for `(2, 1)`, whose `m = 2` branch needs its own
inequalities once `b` is general (order G-8's routes critic). -/
theorem maxPrimeFac_lt_cyclotomicHomogenized_add_one {b n : ℕ} (hb : 0 < b) (hn : 1 < n)
    (h6 : ¬ (n = 6 ∧ b = 1)) :
    (n.maxPrimeFac : ℤ) < cyclotomicHomogenized n (b + 1 : ℕ) b := by
  have hP := Nat.prime_maxPrimeFac_of_one_lt hn
  set P := n.maxPrimeFac with hPdef
  obtain ⟨m, hm⟩ : ∃ m, n = m * P := ⟨n / P, (Nat.div_mul_cancel Nat.maxPrimeFac_dvd).symm⟩
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hm; omega
  have hbZ : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hbne : ((b : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
  have hbP : 0 < b ^ P := by positivity
  have hbPlt : b ^ P < (b + 1) ^ P := Nat.pow_lt_pow_left (by omega) hP.ne_zero
  have hD := lt_add_one_pow_sub_pow hbZ hP.two_le
  have hDR : (P : ℝ) < (((b + 1) ^ P : ℕ) : ℝ) - ((b ^ P : ℕ) : ℝ) := by
    have := (Int.cast_lt (R := ℝ)).mpr hD
    push_cast at this ⊢
    linarith
  rw [hm]
  by_cases hdvd : P ∣ m
  · rw [cyclotomicHomogenized_mul_prime_of_dvd hP hdvd hbne, ← Nat.cast_pow, ← Nat.cast_pow]
    have hm2 : 2 ≤ m := le_trans hP.two_le (Nat.le_of_dvd hm0 hdvd)
    have hlow := sub_pow_totient_lt_cyclotomicHomogenized hm2 hbP hbPlt
    have hge1 : (1 : ℝ) ≤ (((b + 1) ^ P : ℕ) : ℝ) - ((b ^ P : ℕ) : ℝ) := by
      have : (2 : ℝ) ≤ P := by exact_mod_cast hP.two_le
      linarith
    have hpow := le_self_pow₀ hge1 (Nat.totient_pos.mpr hm0).ne'
    have : ((P : ℕ) : ℝ) < ((cyclotomicHomogenized m ((b + 1) ^ P : ℕ) (b ^ P : ℕ) : ℤ) : ℝ) := by
      linarith
    exact_mod_cast this
  · have hE := cyclotomicHomogenized_mul_prime_mul hP hdvd (x := ((b + 1 : ℕ) : ℤ)) hbne
    rw [← Nat.cast_pow, ← Nat.cast_pow] at hE
    have hpos := cyclotomicHomogenized_pos m hb (by omega : b < b + 1)
    rcases (show m = 1 ∨ m = 2 ∨ 3 ≤ m by omega) with rfl | rfl | hm3
    · rw [cyclotomicHomogenized_one, cyclotomicHomogenized_one] at hE
      push_cast at hE ⊢
      have : (P : ℤ) < cyclotomicHomogenized (1 * P) ((b : ℤ) + 1) b := by
        have hE' : cyclotomicHomogenized (1 * P) ((b : ℤ) + 1) b = ((b : ℤ) + 1) ^ P - b ^ P := by
          rw [← hE]; ring
        rw [hE']
        exact hD
      exact this
    · have hP2 : P ≠ 2 := fun h => hdvd ⟨1, by rw [h]⟩
      rw [cyclotomicHomogenized_two, cyclotomicHomogenized_two] at hE
      push_cast at hE ⊢
      have h2b : (0 : ℤ) < 2 * b + 1 := by omega
      have hE' : cyclotomicHomogenized (2 * P) ((b : ℤ) + 1) b * (2 * b + 1) =
          ((b : ℤ) + 1) ^ P + b ^ P := by rw [← hE]; ring
      have hP35 : P = 3 ∨ 5 ≤ P := by
        have h2 := hP.two_le
        have h4 : P ≠ 4 := by
          rintro h
          rw [h] at hP
          norm_num at hP
        omega
      rcases hP35 with hP3 | hP5
      · have hb2 : 2 ≤ b := by
          by_contra hlt
          exact h6 ⟨by rw [hm, hP3], by omega⟩
        have hb2Z : (2 : ℤ) ≤ b := by exact_mod_cast hb2
        rw [hP3] at hE' ⊢
        have hfac : ((b : ℤ) + 1) ^ 3 + (b : ℤ) ^ 3 = (b ^ 2 + b + 1) * (2 * b + 1) := by ring
        rw [hfac] at hE'
        have hval : cyclotomicHomogenized (2 * 3) ((b : ℤ) + 1) b = b ^ 2 + b + 1 :=
          mul_right_cancel₀ h2b.ne' hE'
        push_cast
        rw [hval]
        nlinarith
      · have hS := mul_two_mul_add_one_lt_add_one_pow hbZ hP5
        have hbPZ : (0 : ℤ) ≤ (b : ℤ) ^ P := by positivity
        by_contra hle
        push Not at hle
        have : cyclotomicHomogenized (2 * P) ((b : ℤ) + 1) b * (2 * b + 1) ≤ P * (2 * b + 1) :=
          mul_le_mul_of_nonneg_right hle h2b.le
        linarith
    · -- `m ≥ 3`: `P ≥ 3`, `φ(m) ≥ 2`
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
      have hup := cyclotomicHomogenized_lt_add_pow_totient hm3 hb (by omega : b < b + 1)
      have hlow := sub_pow_totient_lt_cyclotomicHomogenized (by omega : 2 ≤ m) hbP hbPlt
      have hineq := mul_pow_le_add_one_pow_sub_pow_pow hbZ hP3 hφ2
      have hineqR : (P : ℝ) * (((b + 1 : ℕ) : ℝ) + (b : ℝ)) ^ m.totient ≤
          ((((b + 1) ^ P : ℕ) : ℝ) - ((b ^ P : ℕ) : ℝ)) ^ m.totient := by
        have := (Int.cast_le (R := ℝ)).mpr hineq
        push_cast at this ⊢
        rw [show ((b : ℝ) + 1 + b) = 2 * b + 1 by ring]
        exact this
      have hER := congrArg (fun z : ℤ => (z : ℝ)) hE
      simp only [Int.cast_mul] at hER
      have hposR : (0 : ℝ) < ((cyclotomicHomogenized m (b + 1 : ℕ) b : ℤ) : ℝ) := by
        exact_mod_cast hpos
      by_contra hle
      push Not at hle
      have hleR : ((cyclotomicHomogenized (m * P) (b + 1 : ℕ) b : ℤ) : ℝ) ≤ (P : ℝ) := by
        exact_mod_cast hle
      have h1 : ((cyclotomicHomogenized (m * P) (b + 1 : ℕ) b : ℤ) : ℝ) *
          ((cyclotomicHomogenized m (b + 1 : ℕ) b : ℤ) : ℝ) <
            (P : ℝ) * (((b + 1 : ℕ) : ℝ) + (b : ℝ)) ^ m.totient := by
        calc _ ≤ (P : ℝ) * ((cyclotomicHomogenized m (b + 1 : ℕ) b : ℤ) : ℝ) :=
              mul_le_mul_of_nonneg_right hleR hposR.le
          _ < (P : ℝ) * (((b + 1 : ℕ) : ℝ) + (b : ℝ)) ^ m.totient := by
              have hP0 : (0 : ℝ) < P := by exact_mod_cast hP.pos
              push_cast at hup ⊢
              exact mul_lt_mul_of_pos_left hup hP0
      rw [hER] at h1
      linarith

/-! ### `n = 0`, `n = 1`, `n = 2`, and Zsigmondy's theorem -/

/-- At `n = 0` every prime is a primitive divisor. -/
theorem isPrimitiveDivisor₂_zero_iff {p a b : ℕ} : IsPrimitiveDivisor₂ p a b 0 ↔ p.Prime := by
  simp [IsPrimitiveDivisor₂]

/-- At `n = 1` a primitive divisor is a prime factor of `a − b`. -/
theorem isPrimitiveDivisor₂_one_iff {p a b : ℕ} :
    IsPrimitiveDivisor₂ p a b 1 ↔ p.Prime ∧ p ∣ a - b := by
  constructor
  · rintro ⟨hp, hd, -⟩
    exact ⟨hp, by simpa using hd⟩
  · rintro ⟨hp, hd⟩
    exact ⟨hp, by simpa using hd, fun m h0 h1 => absurd h1 (by omega)⟩

/-- `a¹ − b¹` has a primitive divisor exactly when `a ≠ b + 1`, for `b < a`. -/
theorem exists_isPrimitiveDivisor₂_one_iff {a b : ℕ} (hba : b < a) :
    (∃ p, IsPrimitiveDivisor₂ p a b 1) ↔ a ≠ b + 1 := by
  simp only [isPrimitiveDivisor₂_one_iff]
  constructor
  · rintro ⟨p, hp, hd⟩ rfl
    exact hp.one_lt.ne' (Nat.dvd_one.mp (by simpa using hd))
  · intro ha
    exact Nat.exists_prime_and_dvd (by omega)

/-- At `n = 2`, for coprime `b ≤ a`, a primitive divisor is an odd prime factor of `a + b`: a prime
dividing both `a + b` and `a − b` divides `2a` and `2b`. -/
theorem isPrimitiveDivisor₂_two_iff {p a b : ℕ} (hab : a.Coprime b) (hba : b ≤ a) :
    IsPrimitiveDivisor₂ p a b 2 ↔ p.Prime ∧ p ∣ a + b ∧ p ≠ 2 := by
  have hsq : a ^ 2 - b ^ 2 = (a + b) * (a - b) := Nat.sq_sub_sq a b
  constructor
  · rintro ⟨hp, hd, hmin⟩
    have h1 : ¬ p ∣ a - b := by simpa using hmin 1 one_pos one_lt_two
    rw [hsq] at hd
    have hp1 : p ∣ a + b := (hp.dvd_mul.mp hd).resolve_right h1
    refine ⟨hp, hp1, fun h2 => h1 ?_⟩
    subst h2
    omega
  · rintro ⟨hp, hp1, hp2⟩
    refine ⟨hp, hsq ▸ Dvd.dvd.mul_right hp1 _, fun m h0 h2 hm => ?_⟩
    obtain rfl : m = 1 := by omega
    rw [pow_one, pow_one] at hm
    have hodd : ∀ c : ℕ, p ∣ 2 * c → p ∣ c := fun c h =>
      (hp.dvd_mul.mp h).resolve_left fun h' =>
        hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
    have h2a : p ∣ 2 * a := by
      have := Nat.dvd_add hp1 hm
      rwa [show a + b + (a - b) = 2 * a by omega] at this
    have h2b : p ∣ 2 * b := by
      have := Nat.dvd_sub hp1 hm
      rwa [show a + b - (a - b) = 2 * b by omega] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp (hab.gcd_eq_one ▸ Nat.dvd_gcd (hodd a h2a) (hodd b h2b)))

/-- `a² − b²` has a primitive divisor exactly when `a + b` is not a power of `2`, for coprime
`b ≤ a`. -/
theorem exists_isPrimitiveDivisor₂_two_iff {a b : ℕ} (hab : a.Coprime b) (hba : b ≤ a) :
    (∃ p, IsPrimitiveDivisor₂ p a b 2) ↔ ¬ ∃ k, a + b = 2 ^ k := by
  simp only [isPrimitiveDivisor₂_two_iff hab hba]
  constructor
  · rintro ⟨p, hp, hd, h2⟩ ⟨k, hk⟩
    rw [hk] at hd
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  · intro h
    rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (a + b) with h' | ⟨p, hp, hd, hodd⟩
    · exact absurd h' h
    · exact ⟨p, hp, hd, fun h2 => by subst h2; exact (Nat.not_even_iff_odd.mpr hodd) even_two⟩

/-- **Zsigmondy's theorem for `aⁿ − bⁿ`.** For coprime `0 < b < a` and every `n`, `aⁿ − bⁿ` has a
primitive prime divisor exactly unless `n = 1` and `a = b + 1` (`a − b = 1` has no prime factor),
or `n = 2` and `a + b` is a power of `2` (every prime of `a² − b²` then divides `a − b`), or
`(a, b, n) = (2, 1, 6)` (`2⁶ − 1 = 63 = 3² · 7`). At `n = 0` both sides hold. Every hypothesis is
needed (order G-8 J1's cells): without coprimality 54 of 4,898 cells fail, first `(4, 2, 6)`; with
`b = 0` or `a = b`, 28 of 31 each; with `a < b`, 8,047 of 8,618. The route is round 22's (above,
and the prior art's for this two-variable form): `Φₙ(a, b) > P(n)` for `n ≥ 3` outside
`(2, 1, 6)`, whose primes are primitive or are `P(n)` once. -/
theorem exists_isPrimitiveDivisor₂_iff {a b n : ℕ} (hab : a.Coprime b) (hb : 0 < b)
    (hba : b < a) :
    (∃ p, IsPrimitiveDivisor₂ p a b n) ↔
      ¬ ((n = 1 ∧ a = b + 1) ∨ (n = 2 ∧ ∃ k, a + b = 2 ^ k) ∨ (n = 6 ∧ a = 2 ∧ b = 1)) := by
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | rfl | hn3
  · exact iff_of_true ⟨2, isPrimitiveDivisor₂_zero_iff.mpr Nat.prime_two⟩ (by simp)
  · rw [exists_isPrimitiveDivisor₂_one_iff hba]
    simp
  · rw [exists_isPrimitiveDivisor₂_two_iff hab hba.le]
    simp
  · by_cases h6 : n = 6 ∧ a = 2 ∧ b = 1
    · obtain ⟨rfl, rfl, rfl⟩ := h6
      exact iff_of_false (fun ⟨p, hp⟩ =>
        not_isPrimitiveDivisor_base_two_six p (isPrimitiveDivisor₂_with_one.mp hp)) (by simp)
    · refine iff_of_true (exists_isPrimitiveDivisor₂_of_maxPrimeFac_lt hab hb hba hn3 ?_) ?_
      · have hpos := cyclotomicHomogenized_pos n hb hba
        have hlt : (n.maxPrimeFac : ℤ) < cyclotomicHomogenized n a b := by
          rcases (show b + 2 ≤ a ∨ a = b + 1 by omega) with h2 | rfl
          · exact maxPrimeFac_lt_cyclotomicHomogenized_of_add_two_le hb h2 (by omega)
          · exact maxPrimeFac_lt_cyclotomicHomogenized_add_one hb (by omega)
              fun ⟨h1, h2⟩ => h6 ⟨h1, by omega, h2⟩
        have habs := Int.natAbs_of_nonneg hpos.le
        omega
      · rintro (⟨h, -⟩ | ⟨h, -⟩ | h)
        · omega
        · omega
        · exact h6 h

/-- Round 22's `exists_isPrimitiveDivisor_iff`, recovered at `b = 1`. It checks the
specialisation, not an independent proof: `exists_isPrimitiveDivisor₂_iff` takes its case
`(2, 1, 6)` from round 22's `not_isPrimitiveDivisor_base_two_six`. -/
example {a n : ℕ} (ha : 2 ≤ a) :
    (∃ p, IsPrimitiveDivisor p a n) ↔
      ¬ ((a = 2 ∧ n = 1) ∨ (a = 2 ∧ n = 6) ∨ (n = 2 ∧ ∃ k, a + 1 = 2 ^ k)) := by
  simp only [← isPrimitiveDivisor₂_with_one]
  rw [exists_isPrimitiveDivisor₂_iff (Nat.coprime_one_right a) one_pos (by omega)]
  constructor
  · rintro h (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hk⟩)
    · exact h (Or.inl ⟨rfl, rfl⟩)
    · exact h (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
    · exact h (Or.inr (Or.inl ⟨rfl, hk⟩))
  · rintro h (⟨rfl, h1⟩ | ⟨rfl, hk⟩ | ⟨rfl, h2, -⟩)
    · exact h (Or.inl ⟨by omega, rfl⟩)
    · exact h (Or.inr (Or.inr ⟨rfl, hk⟩))
    · exact h (Or.inr (Or.inl ⟨h2, rfl⟩))

/-! ### The sum clause -/

/-- **Zsigmondy's theorem, the sum clause.** For coprime positive `a ≠ b` and every `n`, some prime
divides `aⁿ + bⁿ` and no `aᵐ + bᵐ` with `0 < m < n`, exactly unless `n = 3` and `{a, b} = {1, 2}`
(`2³ + 1 = 9 = 3²`, and `3 ∣ 2 + 1`). With `exists_isPrimitiveDivisor₂_iff` this is the statement of
Zsigmondy's theorem in full. From that theorem at `2n` for `n ≥ 2` (a primitive divisor of
`a²ⁿ − b²ⁿ` divides `aⁿ + bⁿ` and no earlier `aᵐ + bᵐ`); `n = 0` by the prime `2`, `n = 1` by any
prime of `a + b ≥ 3`. Stated symmetrically, since `aⁿ + bⁿ` is; the classical `a > b > 0` form is
its specialisation. Every hypothesis is needed (order G-8's cells and statement review):
coprimality (24 of 4,898 cells fail without it), `a ≠ b` (`(1, 1)` fails at 29 of 31 values of
`n`), positivity (`(0, 1)` and `(1, 0)`, 60 of 62). -/
theorem exists_primitive_prime_dvd_pow_add_pow_iff {a b n : ℕ} (hab : a.Coprime b)
    (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b) :
    (∃ p, p.Prime ∧ p ∣ a ^ n + b ^ n ∧ ∀ m : ℕ, 0 < m → m < n → ¬ p ∣ a ^ m + b ^ m) ↔
      ¬ (n = 3 ∧ ((a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2))) := by
  wlog hba : b < a generalizing a b with H
  · have h := H hab.symm hb ha hne.symm (by omega)
    have hc : ∀ k : ℕ, b ^ k + a ^ k = a ^ k + b ^ k := fun k => add_comm _ _
    simp only [hc] at h
    rw [show ((b = 2 ∧ a = 1) ∨ (b = 1 ∧ a = 2)) ↔ ((a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2)) by
      tauto] at h
    exact h
  rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with rfl | rfl | hn2
  · refine iff_of_true ⟨2, Nat.prime_two, by simp, fun m h0 h1 => absurd h1 (by omega)⟩ (by simp)
  · obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (show a + b ≠ 1 by omega)
    exact iff_of_true ⟨p, hp, by simpa using hd, fun m h0 h1 => absurd h1 (by omega)⟩ (by simp)
  · by_cases hex : n = 3 ∧ a = 2 ∧ b = 1
    · obtain ⟨rfl, rfl, rfl⟩ := hex
      refine iff_of_false ?_ (by simp)
      rintro ⟨p, hp, hd, hmin⟩
      have h3 : p = 3 := by
        have : p ∣ 3 ^ 2 := by norm_num at hd ⊢; exact hd
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow this)
      subst h3
      exact hmin 1 one_pos (by norm_num) (by norm_num)
    · have hsq : ∀ k : ℕ, a ^ (2 * k) - b ^ (2 * k) = (a ^ k + b ^ k) * (a ^ k - b ^ k) := by
        intro k
        rw [show a ^ (2 * k) = (a ^ k) ^ 2 by rw [← pow_mul, mul_comm],
          show b ^ (2 * k) = (b ^ k) ^ 2 by rw [← pow_mul, mul_comm], Nat.sq_sub_sq]
      obtain ⟨p, hp, hd, hmin⟩ := (exists_isPrimitiveDivisor₂_iff (n := 2 * n) hab hb hba).mpr
        (by rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, h2, h1⟩) <;> [omega; omega; exact hex ⟨by omega, h2, h1⟩])
      refine iff_of_true ⟨p, hp, ?_, fun m h0 h1 hm => ?_⟩ ?_
      · rw [hsq] at hd
        exact (hp.dvd_mul.mp hd).resolve_right (hmin n (by omega) (by omega))
      · exact hmin (2 * m) (by omega) (by omega) (by rw [hsq]; exact Dvd.dvd.mul_right hm _)
      · rintro ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
        · exact hex ⟨rfl, rfl, rfl⟩
        · omega

/-! ### The rank of apparition at `(a + b, ab)` -/

/-- Over a nontrivial ring the rank of apparition is never `1`, since `U 1 = 1`. -/
private theorem lucasApparition_ne_one {R : Type*} [CommRing R] [Nontrivial R] (P Q : R) :
    lucasApparition P Q ≠ 1 := by
  intro h
  have hex := (lucasApparition_pos_iff P Q).mp (by omega)
  have hmem := (lucasApparition_mem hex).2
  rw [h, lucasU_one] at hmem
  exact one_ne_zero hmem

/-- **Which `n` are ranks of apparition in `U(a + b, ab)`**, for distinct coprime positive integer
roots `a`, `b` (so `P = a + b`, `Q = ab`): every `n` except `1`, and except `6` when
`{a, b} = {1, 2}` (the Mersenne case, `U(3, 2) = 2ⁿ − 1`). `n = 0` is the rank of every prime of
`ab`; `n = 2` of every prime of `a + b`; for `n ≥ 3`, a primitive divisor of `aⁿ − bⁿ`
(`exists_isPrimitiveDivisor₂_iff`)
has rank `n` (`isPrimitiveDivisor₂_iff_lucasApparition`). This is not the classical
primitive-divisor theorem for Lucas sequences, which asks for `p ∣ U n` with
`p ∤ D · U 1 ⋯ U (n − 1)`, `D = (a − b)²`: here a prime dividing `D` counts, since a prime
`q ∣ a − b` has rank `q`. The two answers differ at `n = 2` when `a + b` is a power of `2`, where
`2 ∣ D` is the only prime of rank `2` (order G-8's statement review: 29 such pairs with `a ≤ 60`);
at an odd prime `n ∣ a − b` both hold, since a primitive divisor of `aⁿ − bⁿ` does not divide
`a − b`. Every hypothesis is needed: without
coprimality 71 of 9,021 cells fail, first `(4, 2, 0)`; at `(1, 1)` the ranks reached are the primes;
at `(0, 1)` only `0`. -/
theorem exists_prime_lucasApparition_add_mul_eq_iff {a b n : ℕ} (hab : a.Coprime b)
    (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b) :
    (∃ p, p.Prime ∧ lucasApparition (a + b : ZMod p) (a * b : ZMod p) = n) ↔
      n ≠ 1 ∧ ¬ (n = 6 ∧ ((a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2))) := by
  wlog hba : b < a generalizing a b with H
  · have h := H hab.symm hb ha hne.symm (by omega)
    have hadd : ∀ p : ℕ, (b : ZMod p) + a = a + b := fun p => add_comm _ _
    have hmul : ∀ p : ℕ, (b : ZMod p) * a = a * b := fun p => mul_comm _ _
    simp only [hadd, hmul] at h
    rw [show ((b = 2 ∧ a = 1) ∨ (b = 1 ∧ a = 2)) ↔ ((a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2)) by
      tauto] at h
    exact h
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | rfl | hn3
  · -- a prime of `a` has rank `0`: `a / b = 0` modulo it
    refine iff_of_true ?_ (by simp)
    have hp := Nat.minFac_prime (show a ≠ 1 by omega)
    have : Fact a.minFac.Prime := ⟨hp⟩
    have hpa : (a : ZMod a.minFac) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.minFac_dvd a)
    have hpb : (b : ZMod a.minFac) ≠ 0 := fun h0 =>
      hp.one_lt.ne' (Nat.dvd_one.mp (hab.gcd_eq_one ▸
        Nat.dvd_gcd (Nat.minFac_dvd a) ((ZMod.natCast_eq_zero_iff _ _).mp h0)))
    refine ⟨a.minFac, hp, ?_⟩
    rw [lucasApparition_add_mul_eq_orderOf_div (by rw [hpa]; exact hpb.symm), hpa, zero_div,
      orderOf_zero]
  · exact iff_of_false (fun ⟨p, hp, h⟩ => by
      have : Fact p.Prime := ⟨hp⟩
      exact lucasApparition_ne_one _ _ h) (by simp)
  · -- a prime of `a + b` has rank `2`: `U 2 = a + b`, `U 1 = 1`
    refine iff_of_true ?_ (by simp)
    have hp := Nat.minFac_prime (show a + b ≠ 1 by omega)
    have : Fact (a + b).minFac.Prime := ⟨hp⟩
    refine ⟨(a + b).minFac, hp, ?_⟩
    have hU2 : lucasU (a + b : ZMod (a + b).minFac) (a * b : ZMod (a + b).minFac) 2 = 0 := by
      rw [lucasU_two, ← Nat.cast_add]
      exact (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.minFac_dvd _)
    have hle := lucasApparition_le two_pos hU2
    have hpos := (lucasApparition_pos_iff _ _).mpr ⟨2, two_pos, hU2⟩
    have hne1 := lucasApparition_ne_one (a + b : ZMod (a + b).minFac) (a * b)
    omega
  · by_cases hex : n = 6 ∧ a = 2 ∧ b = 1
    · obtain ⟨rfl, rfl, rfl⟩ := hex
      refine iff_of_false ?_ (by simp)
      rintro ⟨p, hp, h⟩
      have hpd := (isPrimitiveDivisor₂_iff_lucasApparition (p := p) (a := 2) (b := 1) (n := 6) hp
        (by norm_num) (by simpa using hp.not_dvd_one)).mpr h
      exact not_isPrimitiveDivisor_base_two_six p (isPrimitiveDivisor₂_with_one.mp hpd)
    · obtain ⟨p, hpd⟩ := (exists_isPrimitiveDivisor₂_iff (n := n) hab hb hba).mpr (by
        rintro (⟨h, -⟩ | ⟨h, -⟩ | h)
        · omega
        · omega
        · exact hex h)
      have hpab : ¬ p ∣ a - b := by simpa using hpd.2.2 1 one_pos (by omega)
      refine iff_of_true ⟨p, hpd.1, (isPrimitiveDivisor₂_iff_lucasApparition hpd.1 (by omega)
        hpab).mp hpd⟩ ⟨by omega, ?_⟩
      rintro ⟨h6, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
      · exact hex ⟨h6, rfl, rfl⟩
      · omega

/-- Order G-8's J2 item 4 (C) in the order's own words: the `b < a` form, with the casts outside. -/
example {a b n : ℕ} (hab : a.Coprime b) (hb : 0 < b) (hba : b < a) :
    (∃ p, p.Prime ∧ lucasApparition ((a + b : ℕ) : ZMod p) ((a * b : ℕ) : ZMod p) = n) ↔
      n ≠ 1 ∧ ¬ (n = 6 ∧ a = 2 ∧ b = 1) := by
  simp only [Nat.cast_add, Nat.cast_mul]
  rw [exists_prime_lucasApparition_add_mul_eq_iff hab (by omega) hb (by omega)]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h6 => h2 ⟨h6.1, Or.inl h6.2⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun ⟨h6, h⟩ => ?_⟩
    rcases h with h | h
    · exact h2 ⟨h6, h⟩
    · omega

end ClassicalLean
