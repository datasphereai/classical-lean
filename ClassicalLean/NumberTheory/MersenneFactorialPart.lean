/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Data.Nat.Choose.Factorization
import ClassicalLean.NumberTheory.FactorialPart
import ClassicalLean.NumberTheory.MersenneOrder

/-!
# A closed form for `gcd(2^(n+2) - 1, (n+1)!)`

Write `M k = 2 ^ k - 1` (Mathlib's `mersenne`) and `d_p = ord_p(2)` for the multiplicative order
of `2` modulo `p`. The **factorial part** of `M(n+2)` at bound `n+1` — the part built from primes
at most `n+1` — has a closed form:

    gcd(M(n+2), (n+1)!) = ∏ p ^ min( v_p((n+1)!), v_p(M d_p) + v_p(n+2) )

the product running over the odd primes `p ≤ n+1` whose order of `2` divides `n+2`
(`closed_form`).

## The architecture

1. The valuation of a gcd is the pointwise minimum (`factorization_gcd_min`).
2. The prime `2` never contributes, because `M k` is odd — this is proved, not assumed, and is
   what lets the product range over odd primes.
3. a. `v_p((n+1)!)` is Legendre's formula (`factorial_valuation`).
   b. `v_p(M m)` is `MersenneOrder.factorization_mersenne`, by lifting-the-exponent. **This was
      the hard step.**
4. Rebuild the number from its factorisation with `Nat.prod_factorization_pow_eq_self`, after
   showing that every prime factor of the gcd satisfies the filter's four conditions.

## Provenance

This was the harvest's **one genuinely open problem**, and for a while the only `sorry` in the
library. It arrived as two files that, by their own headers, had **never been compiled by their
authors** — written without a Lean toolchain, with every cited Mathlib name flagged as unverified
because the `multiplicity` API was mid-migration to `emultiplicity`. The first port made them
elaborate, with five holes labelled by what each needed. All five are now closed:

| hole | how it closed |
|---|---|
| `factorization_gcd_min` | a citation — `Nat.factorization_gcd` with `Finsupp.inf_apply` |
| `factorial_valuation` | a citation — Legendre is `Nat.factorization_factorial` |
| `eq_one_of_prime_succ` | the direct order argument, in `MersenneOrder`; it never needed the
  closed form |
| `mersenne_valuation` | lifting-the-exponent, in `MersenneOrder`. The hard one |
| `closed_form` | the assembly below |

Three of the five were never mathematics — they were citations their author could not check
without a toolchain. Two were. The source's own note that step 3b "is the real content. The rest
is plumbing that a determined afternoon should close" was accurate.

One statement needed correcting on the way: `mersenne_valuation` requires `m ≠ 0`, which the
source's version did not carry and genuinely needs, since `M 0 = 0`.

The source also corroborated the formula at 41 values of `n` with `native_decide` — the compiler
rather than the kernel. That is no longer evidence this library depends on: the identity is
proved. Kernel-checked `decide` examples are kept below as illustrations.
-/

namespace ClassicalLean

open Nat

/-- The factorial part of a Mersenne number at the matching bound:
`gcd (2 ^ (n + 2) - 1) ((n + 1)!)`. -/
abbrev mersenneFactorialPart (n : ℕ) : ℕ := factorialPart (mersenne (n + 2)) (n + 1)

/-! ## Step 1 — the valuation of a gcd is a pointwise minimum -/

/-- For every prime `p`, the `p`-part of the factorial part is the minimum of the two `p`-parts.
`Nat.factorization_gcd` followed by `Finsupp.inf_apply`, which turns the lattice meet of the two
factorisations into a pointwise `min`. -/
theorem factorization_gcd_min (n p : ℕ) :
    (mersenneFactorialPart n).factorization p
      = min ((mersenne (n + 2)).factorization p) ((n + 1).factorial.factorization p) := by
  have hm : mersenne (n + 2) ≠ 0 := (mersenne_pos.mpr (by omega)).ne'
  have hf : (n + 1).factorial ≠ 0 := Nat.factorial_ne_zero _
  change (Nat.gcd _ _).factorization p = _
  rw [Nat.factorization_gcd hm hf, Finsupp.inf_apply]

/-! ## Step 3a — Legendre's formula -/

/-- `v_p((n+1)!) = Σ_{i ≥ 1} ⌊(n+1) / p^i⌋`. Mathlib's `Nat.factorization_factorial` asks for a
bound `b` with `log p (n+1) < b`; `b = n + 2` works because `log p m ≤ m`. -/
theorem factorial_valuation (n p : ℕ) (hp : p.Prime) :
    (n + 1).factorial.factorization p = ∑ i ∈ Finset.Ico 1 (n + 2), (n + 1) / p ^ i :=
  Nat.factorization_factorial hp (by
    calc Nat.log p (n + 1) ≤ n + 1 := Nat.log_le_self _ _
      _ < n + 2 := by omega)

/-! ## Step 4 — the closed form -/

/-- **The closed form.** `gcd(M(n+2), (n+1)!)` as a product over the odd primes `p ≤ n+1` whose
order of `2` divides `n+2`.

The proof rebuilds the number from its factorisation. Every prime in the support satisfies the
filter's conditions — it divides `(n+1)!` so it is at most `n+1`; it divides the odd number
`M(n+2)` so it is not `2`; and it divides `M(n+2)` so its order divides `n+2`. Primes in the
filter but outside the support contribute exponent `0`. On the filter the exponent is
`factorization_gcd_min` with the Mersenne valuation substituted, its `if` resolved by the
filter's own last condition. -/
theorem closed_form (n : ℕ) :
    mersenneFactorialPart n
      = ∏ p ∈ (Finset.range (n + 2)).filter
            (fun p => p.Prime ∧ p ≠ 2 ∧ p ≤ n + 1 ∧ (orderOf (2 : ZMod p)) ∣ (n + 2)),
          p ^ min ((n + 1).factorial.factorization p)
                  ((mersenne (orderOf (2 : ZMod p))).factorization p
                    + (n + 2).factorization p) := by
  set F := (Finset.range (n + 2)).filter
      (fun p => p.Prime ∧ p ≠ 2 ∧ p ≤ n + 1 ∧ (orderOf (2 : ZMod p)) ∣ (n + 2)) with hF
  set g := mersenneFactorialPart n with hgdef
  have hMpos : 0 < mersenne (n + 2) := mersenne_pos.mpr (by omega)
  have hg : g ≠ 0 := (factorialPart_pos (n + 1) hMpos).ne'
  have hgM : g ∣ mersenne (n + 2) := factorialPart_dvd _ _
  have hgF : g ∣ (n + 1).factorial := factorialPart_dvd_factorial _ _
  have hsub : g.factorization.support ⊆ F := by
    intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    obtain ⟨hpp, hpg, -⟩ := hp
    have hpM : p ∣ mersenne (n + 2) := hpg.trans hgM
    have hpF : p ∣ (n + 1).factorial := hpg.trans hgF
    have hple : p ≤ n + 1 := (Nat.Prime.dvd_factorial hpp).mp hpF
    have hp2 : p ≠ 2 := by
      rintro rfl
      have hodd : Odd (mersenne (n + 2)) := mersenne_odd.mpr (by omega)
      rw [Nat.odd_iff] at hodd
      omega
    have hdm : orderOf (2 : ZMod p) ∣ n + 2 :=
      (dvd_mersenne_iff_orderOf_dvd hpp).mp (by simpa [mersenne] using hpM)
    simp only [hF, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hpp, hp2, hple, hdm⟩
  have key : ∀ p ∈ F, g.factorization p
      = min ((n + 1).factorial.factorization p)
            ((mersenne (orderOf (2 : ZMod p))).factorization p + (n + 2).factorization p) := by
    intro p hp
    simp only [hF, Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨-, hpp, hp2, -, hdm⟩ := hp
    rw [factorization_gcd_min, factorization_mersenne hpp hp2 (by omega), ite_eq_left hdm,
      Nat.min_comm]
  calc g = g.factorization.prod (· ^ ·) := (Nat.prod_factorization_pow_eq_self hg).symm
    _ = ∏ p ∈ g.factorization.support, p ^ g.factorization p := rfl
    _ = ∏ p ∈ F, p ^ g.factorization p := by
        refine Finset.prod_subset hsub ?_
        intro x _ hxn
        have hx0 : g.factorization x = 0 := by
          by_contra h
          exact hxn (Finsupp.mem_support_iff.mpr h)
        rw [hx0, pow_zero]
    _ = _ := Finset.prod_congr rfl (fun p hp => by rw [key p hp])

/-- The factorial part is trivial whenever `n + 2` is prime — every prime factor of `M q` with
`q` prime exceeds `q`. Proved directly in `MersenneOrder`, so it does not depend on
`closed_form`. -/
theorem eq_one_of_prime_succ (n : ℕ) (h : (n + 2).Prime) : mersenneFactorialPart n = 1 :=
  factorialPart_mersenne_eq_one_of_prime h (by omega)

/-! ## Kernel-checked instances

The source corroborated the formula at 41 values of `n` with `native_decide` — the compiler
rather than the kernel. Now that the identity is proved, these are illustrations rather than
evidence, and they are `decide`, so the kernel checks them. -/

example : mersenneFactorialPart 0 = 1 := by decide
example : mersenneFactorialPart 1 = 1 := by decide
example : mersenneFactorialPart 2 = 3 := by decide
example : mersenneFactorialPart 3 = 1 := by decide

/-- `n + 2 = 5` is prime, so the factorial part is `1` — an instance of
`eq_one_of_prime_succ`, checked independently by `decide`. -/
example : mersenneFactorialPart 3 = 1 := eq_one_of_prime_succ 3 (by decide)

end ClassicalLean
