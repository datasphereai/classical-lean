/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.NumberTheory.LucasSequence
import ClassicalLean.NumberTheory.LucasSequenceCases
import ClassicalLean.NumberTheory.MersenneOrder
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.LinearAlgebra.Matrix.CharP

/-!
# The rank of apparition of a Lucas sequence

For a Lucas sequence of the first kind `U = lucasU P Q` over a commutative ring, the **rank of
apparition** is the least `n > 0` with `U n = 0`, and the theorem that earns the name is

    lucasU_eq_zero_iff_apparition_dvd :  U m = 0  ↔  α ∣ m        (α = lucasApparition P Q)

so that the zero set of a Lucas sequence is exactly a set of multiples.  Over `ZMod N` this
reads: `N ∣ U m` exactly when `α(N) ∣ m`, which is the classical statement.

## The hypothesis, and how it was found

The only hypothesis is **`IsUnit Q`**.  That is weaker than the classical `p ∤ 2QD`, and it is
not a guess: the alternatives were tested numerically before any Lean was written.  Over
`ZMod N` for `N = 1..40`, sweeping all `(P,Q)` and all `m` up to a full period, the iff held in
3 827 108 checks with 0 failures; dropping `IsUnit Q` gave 33 313 failures out of 222 222, the
first at `(P,Q,N) = (-8,-8,2)`.  Neither primality, nor `p ∤ D`, nor finiteness of the ring is
needed for the iff — `[Finite R]` is needed only to know that `α` is *positive*
(`lucasApparition_pos`), which is a separate statement.

`lucasApparition` is defined by `sInf`, so it is `0` when no positive zero exists, and
`lucasApparition_pos_iff` characterises exactly when that junk value is in play.  The iff above
is stated so that it remains **true** in the junk case: both sides then say `m = 0`.

## What is here

* `lucasU_dvd_lucasU_mul`, `lucasU_dvd_lucasU_of_dvd` — the divisibility half, `n ∣ m → U n ∣ U m`,
  over any commutative ring and with no hypothesis on `P` and `Q`.  The index shape is the
  content; the converse is false, see below.
* `lucasApparition`, `lucasApparition_pos_iff`, `lucasApparition_mem`, `lucasApparition_le` — the
  definition and its least-element API.
* `lucasU_eq_zero_iff_apparition_dvd` — the theorem.
* `map_lucasU` — transport along a ring hom, which is what carries the statement from `ℤ` to
  `ZMod N`.
* `exists_pos_lucasU_eq_zero`, `lucasApparition_pos` — existence over a *finite* ring, via the
  companion matrix: `det (lucasCompanion P Q) = Q` is a unit, so the matrix is a unit of a finite
  monoid, and `lucasCompanion_pow_succ` reads `U` off the `(1,0)` entry of `M ^ orderOf M = 1`.
* `intCast_dvd_lucasU_iff`, `prime_dvd_lucasU_iff` — the integer statements at a modulus.
* `lucasApparition_three_two_eq_orderOf` — at `(P,Q) = (3,2)`, where `U n = 2^n - 1`, the rank of
  apparition **is** the multiplicative order of `2`.
* `isCoprime_lucasU_succ_Q`, `dvd_lucasU_gcd_iff`, `lucasU_gcd` — strong divisibility over `ℤ`:
  the common divisors of `U m` and `U n` are the divisors of `U (gcd m n)`.  Proved *from* the
  iff, with no Euclidean induction.
* **Dated 2026-09-24 (order G-7, J3; round 24):** the law of apparition. Over `ZMod p`, for every
  prime `p`: `U_p = D ^ (p / 2)` (`lucasU_prime_eq_lucasDiscr_pow`), `V_p = P`
  (`lucasV_prime_eq`), and the neighbours `2 U_{p+1} = P (1 + D ^ (p / 2))` and
  `2 Q U_{p−1} = P (D ^ (p / 2) − 1)`. Over `ℤ`, for every prime: `U_p ≡ (D / p)` and
  `V_p ≡ P (mod p)` (`lucasU_prime_modEq_legendreSym`, `lucasV_prime_modEq`). For an odd prime with
  `p ∣ Q → p ∣ P`: `p ∣ U_{p − (D/p)}` (`prime_dvd_lucasU_sub_legendreSym`). For an odd prime
  `p ∤ Q`: `α(p) ∣ p − (D/p)` (`lucasApparition_dvd_sub_legendreSym`). Fibonacci: `p ∣ F_{p−1}`
  for `p ≡ ±1` and `p ∣ F_{p+1}` for `p ≡ ±2 (mod 5)` (`prime_dvd_fib_sub_one`,
  `prime_dvd_fib_add_one`). `map_lucasV` is `map_lucasU`'s companion.
* **Dated 2026-09-24 (order G-8, J2; round 25):** at `(P, Q) = (a + b, ab)`, over any field and for
  `a ≠ b`, the rank of apparition is the multiplicative order of `a / b`
  (`lucasApparition_add_mul_eq_orderOf_div`).
* **Dated 2026-09-24 (order G-8, J3; round 26):** in any commutative ring of prime characteristic
  `p`, `V_p = P ^ p` (`lucasV_prime_eq_pow`); in `R[X]` it is `dickson 1 a p = X ^ p` for every `a`
  (`dickson_one_eq_X_pow_of_charP`), which Mathlib has at `a = 1` (`dickson_one_one_charP`).
* **Dated 2026-09-25 (order G-9, J3; round 28):** in any commutative ring of prime characteristic
  `p`, `V (p n) = V n ^ p` (`lucasV_prime_mul`) and, for odd `p`, `U (p n) = D ^ (p / 2) U n ^ p`
  (`lucasU_prime_mul`); at prime powers `V (p ^ k) = P ^ (p ^ k)` (`lucasV_prime_pow_eq_pow`) and,
  for odd `p`, `U (p ^ k) = D ^ (p ^ k / 2)` (`lucasU_prime_pow_eq_lucasDiscr_pow`);
  `U p = D ^ (p / 2)` in every commutative ring of odd prime characteristic `p`
  (`lucasU_prime_eq_lucasDiscr_pow_of_charP`); and
  `dickson 1 a (p ^ k) = X ^ (p ^ k)` (`dickson_one_prime_pow_eq_X_pow`). In characteristic `2`,
  `V n = P U n` and `U (2 n) = P U n ^ 2` (`lucasV_eq_mul_lucasU_of_char_two`,
  `lucasU_two_mul_of_char_two`). Mathlib's `dickson_one_one_mul` with `dickson_one_one_charP` gives
  the slices `Q = 1` and `a = 1` (for `V (p n)` and at prime powers), and `ZMod.trace_pow_card`
  (with `lucasCompanion_pow_succ_trace`) the slice `R = ZMod p` of `V (p n) = V n ^ p`; route: the
  Frobenius on a `2 × 2` matrix (round 26's, with `M ^ n` for `M`), claude-ai's in order G-9, §0
  row 10.

## What is not here

The bound `α(p) ∣ p - (D/p)` is **not** proved: it needs the quadratic character of the
discriminant, and it is the substantial half of the classical theory.  Neither is the sharp
existence criterion, the repeated-root case `p ∣ D`, nor any `lucasV` analogue.

**Dated 2026-09-24 (order G-7, J3; round 24):** the bound is now proved here, for an odd prime
`p ∤ Q` (`lucasApparition_dvd_sub_legendreSym`), with the law of apparition itself
(`prime_dvd_lucasU_sub_legendreSym`); at `p ∣ D` the index is `p`, so the repeated-root case of the
bound is covered too. `V_p ≡ P` and `map_lucasV` are proved; no `lucasV` analogue of the rank of
apparition is. The sharp existence criterion is still not here.

**Dated 2026-09-24 (order G-8, J2; round 25):** for distinct coprime positive integer roots `a`,
`b` (`P = a + b`, `Q = ab`), which `n` are ranks of apparition is proved in
`NumberTheory/ZsigmondyPowSubPow` (`exists_prime_lucasApparition_add_mul_eq_iff`): every `n` except
`1`, and except `6` at `{a, b} = {1, 2}`. That is not the classical primitive-divisor criterion for
Lucas sequences, which excludes the primes of `D`; for other `(P, Q)` the sharp existence criterion
is still not here.

## The law of apparition: route and sources (dated 2026-09-24, order G-7, J3; round 24)

Over `ZMod p` the map `x ↦ x ^ p` is additive, and the classical proof applies it in a ring holding
a square root of `D`. Here that ring is the `2 × 2` matrices over `ZMod p`: with
`M = lucasCompanion P Q` and `N = 2 M − P`, `N² = D`, so for odd `p`
`2 M ^ p = (P + N) ^ p = P + N ^ p = P + D ^ (p / 2) N` (`add_pow_char_of_commute`, Mathlib's
`CharP` instance on square matrices, `ZMod.pow_card`). The entries of `lucasCompanion_pow_succ` at
`n = p − 1`, and its trace, then give `U_p`, `V_p` and both neighbours at once, with no identity
`2 U (n + 1) = P U n + V n` and no case split at `p ∣ D`; Euler's criterion
(`legendreSym.eq_pow`) turns `D ^ (p / 2)` into the Legendre symbol, and `p = 2` is direct. The
route is the order's Frobenius route (claude-ai, order G-7, J3 method 3) realised in matrices
rather than in `AdjoinRoot`, which has no characteristic instance in Mathlib; the matrix
realisation was derived here. This file gains `import Mathlib.LinearAlgebra.Matrix.CharP` for that
instance. Prior art in Mathlib, credited, nothing adapted: `Polynomial.dickson_one_one_zmod_p`
(`dickson 1 1 p = X ^ p`, so `V_p = P` at `Q = 1`, through `lucasV_eq_dickson_one_eval`);
`ZMod.trace_pow_card` (`trace (M ^ p) = trace M ^ p`, which with `lucasCompanion_pow_succ_trace`
also gives `V_p = P`; found by the statement review, after the recorded searches); and the
Lucas–Lehmer test's ring `X q` with its `CharP` instance, the same idea at one pair `(P, Q)`.
Searched first (round 24): `apparition` 0; `fib` on a line with
`ZMod|legendre|ModEq|orderOf|minimalPeriod` 0; `legendreSym` with `lucas|dickson|fib` 0.

## One import is heavier than it looks

`LucasSequenceCases` is imported for a single four-line identification, `lucasU_three_two_eq`,
and it transitively pulls `LucasCompanion → Geometry.Helix → Mathlib.Analysis.Quaternion` and
`Trigonometric.Basic`.  So this number-theory module carries real and quaternion analysis behind
it.  That was decided knowingly rather than noticed late: the alternative is to restate the
identification locally and duplicate it.  Anything importing *this* module inherits the weight.

## Mathlib status, measured

`grep -rni 'apparition' Mathlib --include=*.lean` returns 0 hits, but that is a search for a
*name*, and this project has twice been wrong that way.  Searching the mathematics instead:

* grepping `fib` against each of `ZMod`, `orderOf`, `minimalPeriod` and `ModEq` on one line,
  in either order, across `Mathlib --include=*.lean`, returns **0 hits** — Mathlib states
  nothing about `fib` modulo anything, under any name.
* `grep -rnE '[A-Za-z_.]+ [a-z0-9 ]*m ∣ [A-Za-z_.]+ [a-z0-9 ]*n ↔' Mathlib --include=*.lean`
  returns **exactly one line**: `Pell.y_dvd_iff` (`NumberTheory/PellMatiyasevic.lean:412`).

That one line matters and is recorded rather than glossed: **Mathlib does prove a two-sided
divisibility law for a Lucas sequence.**  `Pell.yn a1` is `lucasU (2a) 1` — the recurrence and
both initial values were checked by elaboration, not by eye — so `y_dvd_iff` is this theorem's
statement at `(P,Q) = (2a, 1)` with `P` even and `a ≥ 2`.  What is new here is the *general*
`(P,Q)`, the `ZMod N` form, and the rank of apparition itself, which Pell's development does
not define.

Mathlib does have the `(P,Q) = (1,-1)` divisibility half and strong divisibility as
`Nat.fib_dvd` and `Nat.fib_gcd` (`Data/Nat/Fib/Basic.lean:246` and `:238`); both are recovered
below as `example`s.  Note `Int.fib_gcd` is a **deprecated** alias of `Int.gcd_fib` (since
2025-12-09) and should not be cited.

Mathlib has **no iff** form of `fib` divisibility, and cannot: the converse of `Nat.fib_dvd` is
false, since `fib 2 ∣ fib 3` while `¬ (2 ∣ 3)` — `fib 1 = fib 2 = 1` is the obstruction.  That
is exactly why the iff here is stated at a modulus rather than over `ℤ`.
-/

namespace ClassicalLean

variable {R : Type*} [CommRing R]

/-- `U n ∣ U (n * k)`, over any commutative ring, with **no hypothesis on `P` and `Q`**.

There is no hypothesis to state: the index shape is the content.  The converse fails, and not
subtly — `U (1,-1)` is `fib`, and `fib 2 ∣ fib 3` while `¬ (2 ∣ 3)`, because `fib 1 = fib 2 = 1`.
That is why the two-sided statement below lives at a modulus and not over `ℤ`. -/
theorem lucasU_dvd_lucasU_mul (P Q : R) (n k : ℕ) :
    lucasU P Q n ∣ lucasU P Q (n * k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    cases n with
    | zero => simp
    | succ i =>
      have h := lucasU_add P Q ((i + 1) * k) i
      rw [show (i + 1) * k + i + 1 = (i + 1) * (k + 1) by ring] at h
      rw [h]
      exact dvd_sub (dvd_mul_left _ _) (Dvd.dvd.mul_right (Dvd.dvd.mul_left ih Q) _)

theorem lucasU_dvd_lucasU_of_dvd (P Q : R) {n m : ℕ} (h : n ∣ m) :
    lucasU P Q n ∣ lucasU P Q m := by
  obtain ⟨k, rfl⟩ := h; exact lucasU_dvd_lucasU_mul P Q n k

theorem isUnit_lucasU_of_lucasU_succ_eq_zero {P Q : R} (hQ : IsUnit Q) {n : ℕ}
    (h : lucasU P Q (n + 1) = 0) : IsUnit (lucasU P Q n) := by
  have hc := lucasU_cassini P Q n
  rw [h] at hc
  have hc' : lucasU P Q (n + 2) * lucasU P Q n = -Q ^ n := by rw [← hc]; ring
  exact isUnit_of_mul_isUnit_right (by rw [hc']; exact (hQ.pow n).neg)

noncomputable def lucasApparition (P Q : R) : ℕ := sInf {n : ℕ | 0 < n ∧ lucasU P Q n = 0}

theorem lucasApparition_pos_iff (P Q : R) :
    0 < lucasApparition P Q ↔ ∃ n : ℕ, 0 < n ∧ lucasU P Q n = 0 := by
  rw [lucasApparition, Nat.pos_iff_ne_zero, Ne, Nat.sInf_eq_zero, not_or]
  simp only [Set.mem_ofPred_eq, lt_irrefl, false_and, not_false_eq_true, true_and,
    ← Set.nonempty_iff_ne_empty, Set.nonempty_def, Set.mem_ofPred_eq]

theorem lucasApparition_mem {P Q : R} (h : ∃ n : ℕ, 0 < n ∧ lucasU P Q n = 0) :
    0 < lucasApparition P Q ∧ lucasU P Q (lucasApparition P Q) = 0 :=
  Nat.sInf_mem (by obtain ⟨n, hn⟩ := h; exact ⟨n, Set.mem_ofPred.mpr hn⟩)

theorem lucasApparition_le {P Q : R} {m : ℕ} (hm : 0 < m) (h : lucasU P Q m = 0) :
    lucasApparition P Q ≤ m := Nat.sInf_le ⟨hm, h⟩

/-- **The rank of apparition divides exactly the vanishing indices**: `U m = 0 ↔ α ∣ m`.

The one hypothesis is `IsUnit Q`, and it is load-bearing — without it the statement is false,
first at `(P,Q,N) = (-8,-8,2)`, where the rank is `2` and `U 3 = 0`.  Note what is *absent*:
no primality, no `p ∤ D`, no `[Finite R]`.  Finiteness is what makes `α` positive
(`lucasApparition_pos`); it is not needed for the equivalence, which stays true in the junk
case, where `α = 0` and both sides say `m = 0`.

The forward direction is a division-algorithm argument: write `m = α * (m / α) + m % α`, split
with `lucasU_add`, and cancel with `isUnit_lucasU_of_lucasU_succ_eq_zero`, contradicting
minimality of `α`.  The backward direction is `lucasU_dvd_lucasU_of_dvd`. -/
theorem lucasU_eq_zero_iff_apparition_dvd {P Q : R} (hQ : IsUnit Q) (m : ℕ) :
    lucasU P Q m = 0 ↔ lucasApparition P Q ∣ m := by
  by_cases hne : ∃ n : ℕ, 0 < n ∧ lucasU P Q n = 0
  · obtain ⟨hapos, hazero⟩ := lucasApparition_mem hne
    set a := lucasApparition P Q with hadef
    constructor
    · intro hm
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · exact dvd_zero a
      by_contra hnd
      have hrpos : 0 < m % a := Nat.pos_of_ne_zero fun h => hnd (Nat.dvd_of_mod_eq_zero h)
      have hrlt : m % a < a := Nat.mod_lt _ hapos
      have hq : 0 < m / a := by
        rcases Nat.eq_zero_or_pos (m / a) with h0 | h0
        · exact absurd (lucasApparition_le hmpos hm) (by
            have := Nat.div_add_mod m a
            rw [h0] at this
            omega)
        · exact h0
      obtain ⟨j, hj⟩ : ∃ j, a * (m / a) = j + 1 :=
        ⟨a * (m / a) - 1, by have := Nat.mul_pos hapos hq; omega⟩
      have hzq : lucasU P Q (j + 1) = 0 := by
        have hd := lucasU_dvd_lucasU_mul P Q a (m / a)
        rw [hazero, hj] at hd
        exact zero_dvd_iff.mp hd
      have hadd := lucasU_add P Q j (m % a)
      rw [show j + m % a + 1 = a * (m / a) + m % a by omega, Nat.div_add_mod, hzq] at hadd
      rw [hm] at hadd
      have hunit : IsUnit (Q * lucasU P Q j) :=
        hQ.mul (isUnit_lucasU_of_lucasU_succ_eq_zero hQ hzq)
      have hzero : Q * lucasU P Q j * lucasU P Q (m % a) = 0 := by linear_combination hadd
      have : lucasU P Q (m % a) = 0 := hunit.mul_right_eq_zero.mp hzero
      exact absurd (lucasApparition_le hrpos this) (by omega)
    · intro hd
      have := lucasU_dvd_lucasU_of_dvd P Q hd
      rw [hazero] at this
      exact zero_dvd_iff.mp this
  · have h0 : lucasApparition P Q = 0 := by
      by_contra h
      exact hne ((lucasApparition_pos_iff P Q).mp (Nat.pos_of_ne_zero h))
    rw [h0, zero_dvd_iff]
    push Not at hne
    exact ⟨fun hm => by by_contra hmz; exact hne m (Nat.pos_of_ne_zero hmz) hm, by rintro rfl; simp⟩

/-! ### transport along a ring hom -/
theorem map_lucasU {S : Type*} [CommRing S] (f : R →+* S) (P Q : R) :
    ∀ n : ℕ, f (lucasU P Q n) = lucasU (f P) (f Q) n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
      rw [lucasU_add_two, lucasU_add_two, map_sub, map_mul, map_mul,
        map_lucasU f P Q (n + 1), map_lucasU f P Q n]

/-- `lucasV` commutes with ring homomorphisms. -/
theorem map_lucasV {S : Type*} [CommRing S] (f : R →+* S) (P Q : R) :
    ∀ n : ℕ, f (lucasV P Q n) = lucasV (f P) (f Q) n
  | 0 => by simp [map_ofNat]
  | 1 => by simp
  | n + 2 => by
      rw [lucasV_add_two, lucasV_add_two, map_sub, map_mul, map_mul,
        map_lucasV f P Q (n + 1), map_lucasV f P Q n]

/-! ### existence over a finite ring -/
theorem exists_pos_lucasU_eq_zero {R : Type*} [CommRing R] [Finite R] {P Q : R}
    (hQ : IsUnit Q) : ∃ n : ℕ, 0 < n ∧ lucasU P Q n = 0 := by
  set M : Matrix (Fin 2) (Fin 2) R := lucasCompanion P Q with hM
  have hU : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr
    (by rw [hM, lucasCompanion_det]; exact hQ)
  obtain ⟨k, hk⟩ : ∃ k, orderOf M = k + 1 := ⟨orderOf M - 1, by
    have := hU.isOfFinOrder.orderOf_pos; omega⟩
  have hone : M ^ (k + 1) = 1 := hk ▸ pow_orderOf_eq_one M
  have hentry := lucasCompanion_pow_succ P Q k
  rw [← hM] at hentry
  refine ⟨k + 1, Nat.succ_pos k, ?_⟩
  have h : (M ^ (k + 1)) 1 0 = lucasU P Q (k + 1) := by rw [hentry]; simp
  rw [hone] at h
  simpa using h.symm

theorem lucasApparition_pos {R : Type*} [CommRing R] [Finite R] {P Q : R} (hQ : IsUnit Q) :
    0 < lucasApparition P Q := (lucasApparition_pos_iff P Q).mpr (exists_pos_lucasU_eq_zero hQ)

/-! ### the integer statement at a modulus -/
theorem intCast_dvd_lucasU_iff {N : ℕ} {P Q : ℤ} (hQ : IsUnit ((Q : ZMod N))) (m : ℕ) :
    (N : ℤ) ∣ lucasU P Q m ↔ lucasApparition ((P : ZMod N)) ((Q : ZMod N)) ∣ m := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← lucasU_eq_zero_iff_apparition_dvd hQ]
  have h : ((lucasU P Q m : ℤ) : ZMod N) = lucasU ((P : ZMod N)) ((Q : ZMod N)) m := by
    simpa using map_lucasU (Int.castRingHom (ZMod N)) P Q m
  rw [h]

theorem prime_dvd_lucasU_iff {p : ℕ} (hp : p.Prime) {P Q : ℤ} (hQ : ¬ (p : ℤ) ∣ Q) (m : ℕ) :
    (p : ℤ) ∣ lucasU P Q m ↔ lucasApparition ((P : ZMod p)) ((Q : ZMod p)) ∣ m := by
  have : Fact p.Prime := ⟨hp⟩
  exact intCast_dvd_lucasU_iff
    (isUnit_iff_ne_zero.mpr (fun h => hQ ((ZMod.intCast_zmod_eq_zero_iff_dvd Q p).mp h))) m

/-- **At `(P,Q) = (3,2)` the rank of apparition is the multiplicative order of `2`.**

Here `U n = 2 ^ n - 1` (`lucasU_three_two_eq`), so this says the least `n > 0` with
`p ∣ 2 ^ n - 1` is `ord_p(2)` — the Mersenne case, and the reason `MersenneOrder.lean` and this
module are about one object.

**Both hypotheses are proof-route, not statement.**  The equation itself holds at `p = 2` and at
composite moduli: checked for `N = 1..200` with no mismatch, `orderOf` taking Mathlib's junk
value `0` exactly when `2` is not a unit, which is exactly when the rank is `0` too.  They are
kept because they buy the short proof, not because the statement needs them.

**Dated 2026-09-24 (order G-8, J2; round 25):** `hp2` is not needed: the equation is the case
`(a, b) = (2, 1)` of `lucasApparition_add_mul_eq_orderOf_div`, over `ZMod p` for every prime `p`,
`p = 2` included (the `example` after that theorem). `hp` is still used there, for
`Field (ZMod p)`; at composite moduli the equation is measured (above), not proved. -/
theorem lucasApparition_three_two_eq_orderOf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    lucasApparition (3 : ZMod p) 2 = orderOf (2 : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by push_cast; exact h)
    rcases (Nat.prime_two.eq_one_or_self_of_dvd p this) with h' | h'
    · exact hp.one_lt.ne' h'
    · exact hp2 h'
  have hQ : IsUnit (2 : ZMod p) := isUnit_iff_ne_zero.mpr h2
  refine Nat.dvd_antisymm ?_ ?_
  · rw [← lucasU_eq_zero_iff_apparition_dvd hQ, lucasU_three_two_eq (ZMod p),
      pow_orderOf_eq_one, sub_self]
  · rw [orderOf_dvd_iff_pow_eq_one]
    have h := (lucasU_eq_zero_iff_apparition_dvd hQ (lucasApparition (3 : ZMod p) 2)).mpr dvd_rfl
    rw [lucasU_three_two_eq (ZMod p), sub_eq_zero] at h
    exact h

/-- **At `(P, Q) = (a + b, ab)` the rank of apparition is the order of `a / b`**, in any field, for
`a ≠ b` (derived here, order G-8). By `lucasU_of_roots`, `(a − b) U n = aⁿ − bⁿ`, so `U n = 0`
exactly when `(a / b)ⁿ = 1`;
both sides are the least such `n > 0`, or `0` when there is none. At `b = 0`,
`U n = aⁿ⁻¹ ≠ 0` for `n > 0` and `orderOf (a / 0) = orderOf 0 = 0` (Lean's `0⁻¹ = 0`), so both
sides are `0`. `a ≠ b` is needed as well as used: at `a = b`, `U n = n aⁿ⁻¹` (order G-8 J1: all 440
cells with `a = b` over `ZMod p`, `p < 60`, fail). A commutative-ring variant, with `b` and
`a − b` units and `a * b⁻¹` for `a / b`, also holds (8,873 cells over `ZMod N`, `2 ≤ N ≤ 40`, 0
failures; order G-8's statements critic), but it loses the case `b = 0`. -/
theorem lucasApparition_add_mul_eq_orderOf_div {K : Type*} [Field K] {a b : K} (hab : a ≠ b) :
    lucasApparition (a + b) (a * b) = orderOf (a / b) := by
  have key : ∀ n : ℕ, lucasU (a + b) (a * b) n = 0 ↔ (a / b) ^ n = 1 := by
    intro n
    have hU := lucasU_of_roots a b n
    have hsub : a - b ≠ 0 := sub_ne_zero.mpr hab
    have h1 : lucasU (a + b) (a * b) n = 0 ↔ a ^ n = b ^ n := by
      constructor
      · intro h
        rw [h, mul_zero] at hU
        exact sub_eq_zero.mp hU.symm
      · intro h
        rw [h, sub_self] at hU
        exact (mul_eq_zero.mp hU).resolve_left hsub
    rw [h1]
    rcases eq_or_ne b 0 with rfl | hb
    · have ha : a ≠ 0 := hab
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · simp [zero_pow hn.ne', pow_ne_zero n ha]
    · rw [div_pow, div_eq_one_iff_eq (pow_ne_zero n hb)]
  by_cases h : ∃ n : ℕ, 0 < n ∧ lucasU (a + b) (a * b) n = 0
  · obtain ⟨hL, hUL⟩ := lucasApparition_mem h
    symm
    rw [orderOf_eq_iff hL]
    refine ⟨(key _).mp hUL, fun m hm hm0 hpow => ?_⟩
    exact absurd (lucasApparition_le hm0 ((key m).mpr hpow)) (not_le.mpr hm)
  · have h0 : lucasApparition (a + b) (a * b) = 0 := by
      by_contra hne
      exact h ((lucasApparition_pos_iff _ _).mp (Nat.pos_of_ne_zero hne))
    rw [h0, eq_comm, orderOf_eq_zero_iff']
    exact fun n hn hpow => h ⟨n, hn, (key n).mpr hpow⟩

/-- `lucasApparition_three_two_eq_orderOf` without its `p ≠ 2`: the case `(a, b) = (2, 1)` of
`lucasApparition_add_mul_eq_orderOf_div` over `ZMod p`. At `p = 2` both sides are `0`. -/
example {p : ℕ} (hp : p.Prime) : lucasApparition (3 : ZMod p) 2 = orderOf (2 : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  have h21 : (2 : ZMod p) ≠ 1 := fun h => one_ne_zero (by linear_combination h : (1 : ZMod p) = 0)
  have h := lucasApparition_add_mul_eq_orderOf_div h21
  rwa [show (2 : ZMod p) + 1 = 3 by norm_num, mul_one, div_one] at h

/-! ### The real-work test

`MersenneOrder.dvd_mersenne_iff_orderOf_dvd` is restated verbatim below and closed from the
general theory.  It is an `example`, not a theorem: the shipped proof stays where it is, and
this records that the general statement *reaches* it, not that it should replace it.

Read honestly, this is a weak instance and the module says so.  `2 ^ m - 1` is a **geometric**
sequence, so its rank of apparition degenerates to a multiplicative order, which Mathlib
handles directly — the shipped proof is two rewrites and needs none of this file.  The `p = 2`
branch below gets nothing at all from the general theorem and is closed by that same shipped
lemma.  The instances that carry real weight are the Fibonacci ones further down, where
Mathlib's own `Nat.fib_gcd` comes back out of `lucasU_gcd`, and the entry-point statement,
for which Mathlib has nothing of the shape. -/
example {p m : ℕ} (hp : p.Prime) : p ∣ 2 ^ m - 1 ↔ orderOf (2 : ZMod p) ∣ m := by
  rcases eq_or_ne p 2 with rfl | hp2
  · rw [dvd_mersenne_iff_pow_eq_one hp, orderOf_dvd_iff_pow_eq_one]
  · have : Fact p.Prime := ⟨hp⟩
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h
      have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by push_cast; exact h)
      rcases (Nat.prime_two.eq_one_or_self_of_dvd p this) with h' | h'
      · exact hp.one_lt.ne' h'
      · exact hp2 h'
    have hQ : IsUnit (2 : ZMod p) := isUnit_iff_ne_zero.mpr h2
    rw [← lucasApparition_three_two_eq_orderOf hp hp2, dvd_mersenne_iff_pow_eq_one hp,
      ← lucasU_eq_zero_iff_apparition_dvd hQ, lucasU_three_two_eq (ZMod p), sub_eq_zero]

/-! ### Fibonacci instances -/

/-- **Mathlib's `Nat.fib_dvd`, recovered as the `(1,-1)` instance.** -/
example {m n : ℕ} (h : m ∣ n) : Nat.fib m ∣ Nat.fib n := by
  have := lucasU_dvd_lucasU_of_dvd (1 : ℤ) (-1) h
  rw [lucasU_one_neg_one ℤ, lucasU_one_neg_one ℤ] at this
  exact_mod_cast this

/-- **The Fibonacci entry point, at every modulus, with no hypothesis on `N`.**

`N ∣ fib m` exactly when the rank of apparition of `U(1,-1)` over `ZMod N` divides `m`.  The
measured Mathlib search for anything of this shape returns nothing. -/
example (N m : ℕ) : (N : ℤ) ∣ (Nat.fib m : ℤ) ↔ lucasApparition (1 : ZMod N) (-1) ∣ m := by
  have hQ : IsUnit ((-1 : ℤ) : ZMod N) := by push_cast; exact isUnit_one.neg
  have h := intCast_dvd_lucasU_iff (N := N) (P := 1) (Q := -1) hQ m
  rw [lucasU_one_neg_one ℤ] at h
  simpa using h

/-! ### Strong divisibility

Mathlib proves `Nat.fib_gcd` by a four-link Euclidean induction (`gcd_fib_add_self`,
`gcd_fib_add_mul_self`, then `Nat.gcd.induction`).  None of that is needed once the iff is
available: `d ∣ U m` and `d ∣ U n` both become statements about the rank over `ZMod d.natAbs`,
and `Nat.dvd_gcd` finishes. -/

/-- consecutive-term coprimality input: `U (n+1)` is coprime to `Q` when `P` and `Q` are. -/
theorem isCoprime_lucasU_succ_Q {P Q : ℤ} (hPQ : IsCoprime P Q) (n : ℕ) :
    IsCoprime (lucasU P Q (n + 1)) Q := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using isCoprime_one_left
  | one => simpa using hPQ
  | more n ih1 ih2 =>
      have : lucasU P Q (n + 3) = lucasU P Q (n + 2) * P + Q * (- lucasU P Q (n + 1)) := by
        rw [show n + 3 = (n + 1) + 2 from rfl, lucasU_add_two]; ring
      rw [this]
      exact IsCoprime.add_mul_left_left (ih2.mul_left hPQ) _

/-- **STRONG DIVISIBILITY**: the common divisors of `U m` and `U n` are exactly the
divisors of `U (gcd m n)`. -/
theorem dvd_lucasU_gcd_iff {P Q : ℤ} (hPQ : IsCoprime P Q) (d : ℤ) (m n : ℕ) :
    (d ∣ lucasU P Q m ∧ d ∣ lucasU P Q n) ↔ d ∣ lucasU P Q (Nat.gcd m n) := by
  constructor
  · rintro ⟨hm, hn⟩
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · simpa using hn
    -- `d ∣ U m` with `m > 0` forces `Q` to be a unit mod `d`
    obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
    have hdQ : IsCoprime d Q := (isCoprime_lucasU_succ_Q hPQ i).of_isCoprime_of_dvd_left hm
    set N := d.natAbs with hN
    have hcast : ∀ x : ℤ, ((x : ZMod N) = 0) ↔ d ∣ x := by
      intro x
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hN, Int.natAbs_dvd]
    have hQu : IsUnit ((Q : ZMod N)) := by
      obtain ⟨u, v, huv⟩ := hdQ
      have h1 : ((u * d + v * Q : ℤ) : ZMod N) = ((1 : ℤ) : ZMod N) := by rw [huv]
      have hd0 : ((d : ℤ) : ZMod N) = 0 := (hcast d).mpr dvd_rfl
      push_cast at h1
      rw [hd0, mul_zero, zero_add] at h1
      exact isUnit_of_mul_isUnit_right (by rw [h1]; exact isUnit_one)
    have key : ∀ k : ℕ, d ∣ lucasU P Q k ↔ lucasApparition ((P : ZMod N)) ((Q : ZMod N)) ∣ k := by
      intro k
      rw [← intCast_dvd_lucasU_iff hQu k, hN, Int.natAbs_dvd]
    rw [key] at hm hn ⊢
    exact Nat.dvd_gcd hm hn
  · intro h
    exact ⟨h.trans (lucasU_dvd_lucasU_of_dvd P Q (Nat.gcd_dvd_left m n)),
      h.trans (lucasU_dvd_lucasU_of_dvd P Q (Nat.gcd_dvd_right m n))⟩

/-- the `Int.gcd` spelling, the direct generalisation of `Nat.fib_gcd`. -/
theorem lucasU_gcd {P Q : ℤ} (hPQ : IsCoprime P Q) (m n : ℕ) :
    Int.gcd (lucasU P Q m) (lucasU P Q n) = (lucasU P Q (Nat.gcd m n)).natAbs := by
  refine Nat.dvd_antisymm ?_ ?_
  · have h : ((Int.gcd (lucasU P Q m) (lucasU P Q n) : ℤ)) ∣ lucasU P Q (Nat.gcd m n) :=
      (dvd_lucasU_gcd_iff hPQ _ m n).mp ⟨Int.gcd_dvd_left _ _, Int.gcd_dvd_right _ _⟩
    simpa using Int.natAbs_dvd_natAbs.mpr h
  · obtain ⟨h1, h2⟩ := (dvd_lucasU_gcd_iff hPQ (lucasU P Q (Nat.gcd m n)) m n).mpr dvd_rfl
    exact Int.dvd_gcd (Int.natAbs_dvd.mpr h1) (Int.natAbs_dvd.mpr h2)

/-- **Mathlib's `Nat.fib_gcd`, recovered as the `(1,-1)` instance** — `fib` being a strong
divisibility sequence is the special case of `lucasU_gcd`. -/
example (m n : ℕ) : Nat.fib (Nat.gcd m n) = Nat.gcd (Nat.fib m) (Nat.fib n) := by
  have h := lucasU_gcd (isCoprime_one_left (x := (-1 : ℤ))) m n
  rw [lucasU_one_neg_one ℤ, lucasU_one_neg_one ℤ, lucasU_one_neg_one ℤ] at h
  simp only [Int.natAbs_natCast, Int.gcd_natCast_natCast] at h
  exact h.symm

/-! ### The law of apparition (order G-7, J3; round 24) -/

section Frobenius

variable {p : ℕ} [Fact p.Prime]

private theorem two_ne_zero_of_ne_two (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')

/-- The Frobenius at the companion matrix: for an odd prime `p`, over `ZMod p`,
`2 M ^ p = P + D ^ (p / 2) N` with `N = 2 M − P`, `N² = D`. -/
private theorem two_smul_lucasCompanion_pow (hp2 : p ≠ 2) (P Q : ZMod p) :
    (2 : ZMod p) • lucasCompanion P Q ^ p
      = P • (1 : Matrix (Fin 2) (Fin 2) (ZMod p))
        + lucasDiscr P Q ^ (p / 2) • ((2 : ZMod p) • lucasCompanion P Q - P • 1) := by
  set N := (2 : ZMod p) • lucasCompanion P Q - P • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) with hN
  have hN2 : N ^ 2 = lucasDiscr P Q • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    rw [hN, sq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lucasCompanion, lucasDiscr, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hodd : p = 2 * (p / 2) + 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hNp : N ^ p = lucasDiscr P Q ^ (p / 2) • N := by
    have : N ^ p = N ^ (2 * (p / 2) + 1) := by rw [← hodd]
    rw [this, pow_succ, pow_mul, hN2, smul_pow, one_pow, smul_mul_assoc, one_mul]
  have hsplit : (2 : ZMod p) • lucasCompanion P Q = P • 1 + N := by rw [hN]; abel
  have hcomm : Commute (P • (1 : Matrix (Fin 2) (Fin 2) (ZMod p))) N :=
    (Commute.one_left N).smul_left P
  calc (2 : ZMod p) • lucasCompanion P Q ^ p
      = ((2 : ZMod p) • lucasCompanion P Q) ^ p := by rw [smul_pow, ZMod.pow_card]
    _ = (P • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) + N) ^ p := by rw [hsplit]
    _ = (P • (1 : Matrix (Fin 2) (Fin 2) (ZMod p))) ^ p + N ^ p := add_pow_char_of_commute p hcomm
    _ = P • 1 + lucasDiscr P Q ^ (p / 2) • N := by rw [smul_pow, one_pow, ZMod.pow_card, hNp]

/-- `lucasCompanion P Q ^ p`, entry by entry, from `lucasCompanion_pow_succ` at `n = p - 1`. -/
private theorem lucasCompanion_pow_prime (P Q : ZMod p) :
    lucasCompanion P Q ^ p
      = !![-Q * lucasU P Q (p - 1), -Q * lucasU P Q p; lucasU P Q p, lucasU P Q (p + 1)] := by
  have h1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  have := lucasCompanion_pow_succ P Q (p - 1)
  rwa [Nat.sub_add_cancel h1, show p - 1 + 2 = p + 1 by omega] at this

private theorem frobenius_entries (hp2 : p ≠ 2) (P Q : ZMod p) :
    2 * lucasU P Q p = lucasDiscr P Q ^ (p / 2) * 2 ∧
    2 * lucasU P Q (p + 1) = P + lucasDiscr P Q ^ (p / 2) * P ∧
    2 * (-Q * lucasU P Q (p - 1)) = P + lucasDiscr P Q ^ (p / 2) * -P := by
  have key := two_smul_lucasCompanion_pow hp2 P Q
  rw [lucasCompanion_pow_prime] at key
  have e10 := congrArg (fun A => A 1 0) key
  have e11 := congrArg (fun A => A 1 1) key
  have e00 := congrArg (fun A => A 0 0) key
  simp only [neg_mul, Fin.isValue, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, smul_eq_mul,
    lucasCompanion, Matrix.smul_of, Matrix.smul_cons, mul_zero, mul_neg, Matrix.smul_empty,
    mul_one, Matrix.add_apply, ne_eq, one_ne_zero, not_false_eq_true, Matrix.one_apply_ne,
    Matrix.sub_apply, sub_zero, zero_add, Matrix.one_apply_eq, zero_sub] at e10 e11 e00
  exact ⟨by linear_combination e10, by linear_combination e11, by linear_combination e00⟩

/-- **`U_p` is the Euler power of the discriminant.** Over `ZMod p`, for every prime `p`,
`U_p = D ^ (p / 2)` with `D = P² − 4Q`; with Euler's criterion this is `U_p = (D / p)`. -/
theorem lucasU_prime_eq_lucasDiscr_pow {p : ℕ} [Fact p.Prime] (P Q : ZMod p) :
    lucasU P Q p = lucasDiscr P Q ^ (p / 2) := by
  rcases (Fact.out : p.Prime).eq_two_or_odd with h2 | hodd
  · subst h2
    rw [lucasU_two, lucasDiscr, show 2 / 2 = 1 from rfl, pow_one, ZMod.pow_card,
      show (4 : ZMod 2) = 0 from rfl, zero_mul, sub_zero]
  · have hp2 : p ≠ 2 := by omega
    have h := (frobenius_entries hp2 P Q).1
    have h2 := two_ne_zero_of_ne_two hp2
    exact mul_left_cancel₀ h2 (by rw [h]; ring)

/-- **`V_p = P` over `ZMod p`**, for every prime `p`. At `Q = 1` this is Mathlib's
`Polynomial.dickson_one_one_zmod_p` evaluated at `P`; for every `Q` it is also Mathlib's
`ZMod.trace_pow_card` applied to `lucasCompanion P Q` (`lucasCompanion_pow_succ_trace`). -/
theorem lucasV_prime_eq {p : ℕ} [Fact p.Prime] (P Q : ZMod p) : lucasV P Q p = P := by
  rcases (Fact.out : p.Prime).eq_two_or_odd with h2 | hodd
  · subst h2
    rw [lucasV_two, ZMod.pow_card, show (2 : ZMod 2) = 0 from rfl, zero_mul, sub_zero]
  · have hp2 : p ≠ 2 := by omega
    have h1 : 1 ≤ p := (Fact.out : p.Prime).one_le
    have key := congrArg Matrix.trace (two_smul_lucasCompanion_pow hp2 P Q)
    have ht := lucasCompanion_pow_succ_trace P Q (p - 1)
    rw [Nat.sub_add_cancel h1] at ht
    rw [Matrix.trace_smul, ht] at key
    simp only [smul_eq_mul, lucasCompanion, Matrix.smul_of, Matrix.smul_cons, mul_zero, mul_neg,
      Matrix.smul_empty, mul_one, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
      Fintype.card_fin, Nat.cast_ofNat, Matrix.trace_sub, Matrix.trace_fin_two, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val_one, zero_add] at key
    exact mul_left_cancel₀ (two_ne_zero_of_ne_two hp2) (by linear_combination key)

/-- The Frobenius at the companion matrix over any commutative ring of odd prime characteristic
`p`: `(2 M) ^ p = P ^ p + D ^ (p / 2) N` with `N = 2 M − P`, `N² = D` (round 24's
`two_smul_lucasCompanion_pow`, over `ZMod p`, has `2 M ^ p` and `P` where this has `(2 M) ^ p`
and `P ^ p`; that one is kept). -/
private theorem two_smul_lucasCompanion_pow_charP (p : ℕ) [Fact p.Prime] [CharP R p]
    (hp2 : p ≠ 2) (P Q : R) :
    ((2 : R) • lucasCompanion P Q) ^ p
      = P ^ p • (1 : Matrix (Fin 2) (Fin 2) R)
        + lucasDiscr P Q ^ (p / 2) • ((2 : R) • lucasCompanion P Q - P • 1) := by
  set N := (2 : R) • lucasCompanion P Q - P • (1 : Matrix (Fin 2) (Fin 2) R) with hN
  have hN2 : N ^ 2 = lucasDiscr P Q • (1 : Matrix (Fin 2) (Fin 2) R) := by
    rw [hN, sq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lucasCompanion, lucasDiscr, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hodd : p = 2 * (p / 2) + 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hNp : N ^ p = lucasDiscr P Q ^ (p / 2) • N := by
    have : N ^ p = N ^ (2 * (p / 2) + 1) := by rw [← hodd]
    rw [this, pow_succ, pow_mul, hN2, smul_pow, one_pow, smul_mul_assoc, one_mul]
  have hsplit : (2 : R) • lucasCompanion P Q = P • 1 + N := by rw [hN]; abel
  have hcomm : Commute (P • (1 : Matrix (Fin 2) (Fin 2) R)) N :=
    (Commute.one_left N).smul_left P
  rw [hsplit, add_pow_char_of_commute p hcomm, smul_pow, one_pow, hNp]

/-- **`V_p = P ^ p` in characteristic `p`**: for a commutative ring `R`, a prime `p` with
`CharP R p`, and every `P`, `Q`. Round 24's `lucasV_prime_eq` (`V_p = P` over `ZMod p`) is the case
`R = ZMod p` with `ZMod.pow_card` (an `example` below). Route: round 24's Frobenius at the
companion matrix, carried from `ZMod p` to `R` (claude-ai, order G-8, J3 item 2): for odd `p`,
`(2 M) ^ p = P ^ p + D ^ (p / 2) N` and `tr N = 0`, so `2 ^ p V_p = 2 P ^ p`, and `2 ^ p = 2` with
`2` a unit in `R` (both from `ZMod p` through `ZMod.castHom`, as
`Polynomial.dickson_one_one_charP` is proved); `p = 2` directly, `V₂ = P² − 2 Q`. The binders
`(p : ℕ) [Fact p.Prime] [CharP R p]` are `dickson_one_one_charP`'s; an `ExpChar` form would add
only the trivial `p = 1`. -/
theorem lucasV_prime_eq_pow (p : ℕ) [Fact p.Prime] [CharP R p] (P Q : R) :
    lucasV P Q p = P ^ p := by
  rcases (Fact.out : p.Prime).eq_two_or_odd with h2 | hodd
  · subst h2
    have h20 : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
    rw [lucasV_two, h20, zero_mul, sub_zero]
  · have hp2 : p ≠ 2 := by omega
    have h1 : 1 ≤ p := (Fact.out : p.Prime).one_le
    have key := congrArg Matrix.trace (two_smul_lucasCompanion_pow_charP p hp2 P Q)
    have ht := lucasCompanion_pow_succ_trace P Q (p - 1)
    rw [Nat.sub_add_cancel h1] at ht
    rw [smul_pow, Matrix.trace_smul, ht] at key
    simp only [smul_eq_mul, lucasCompanion, Matrix.smul_of, Matrix.smul_cons, mul_zero, mul_neg,
      Matrix.smul_empty, mul_one, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
      Fintype.card_fin, Nat.cast_ofNat, Matrix.trace_sub, Matrix.trace_fin_two, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val_one, zero_add] at key
    have h2z : (2 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')
    have h2p : (2 : R) ^ p = 2 := by
      have h := congrArg (ZMod.castHom (dvd_refl p) R) (ZMod.pow_card (2 : ZMod p))
      rwa [map_pow, map_ofNat] at h
    have hu : IsUnit (2 : R) := by
      have h := (isUnit_iff_ne_zero.mpr h2z).map (ZMod.castHom (dvd_refl p) R)
      rwa [map_ofNat] at h
    rw [h2p] at key
    exact hu.mul_left_cancel (by linear_combination key)

open Polynomial in
/-- **`dickson 1 a p = X ^ p` in characteristic `p`**: Mathlib's
`Polynomial.dickson_one_one_charP` (`a = 1`, an `example` below) for every `a`. From
`lucasV_prime_eq_pow` in `R[X]` at `(P, Q) = (X, C a)`, through `lucasV_eq_dickson_one_eval` and
`map_dickson`. -/
theorem dickson_one_eq_X_pow_of_charP (p : ℕ) [Fact p.Prime] [CharP R p] (a : R) :
    dickson 1 a p = X ^ p := by
  have h := lucasV_prime_eq_pow (R := R[X]) p X (C a)
  rwa [lucasV_eq_dickson_one_eval, ← map_dickson (C : R →+* R[X]), eval_map, eval₂_C_X] at h

/-- Round 24's `lucasV_prime_eq`, from `lucasV_prime_eq_pow` at `R = ZMod p`. -/
example {p : ℕ} [Fact p.Prime] (P Q : ZMod p) : lucasV P Q p = P := by
  rw [lucasV_prime_eq_pow, ZMod.pow_card]

open Polynomial in
/-- Mathlib's `Polynomial.dickson_one_one_charP` (`RingTheory/Polynomial/Dickson.lean:269`) is the
case `a = 1` of `dickson_one_eq_X_pow_of_charP`. -/
example (p : ℕ) [Fact p.Prime] [CharP R p] : dickson 1 (1 : R) p = X ^ p :=
  dickson_one_eq_X_pow_of_charP p 1

/-- The neighbour above the prime index: `2 U_{p+1} = P (1 + D ^ (p / 2))` over `ZMod p`, for
every prime `p` (at `p = 2` both sides are `0`). -/
theorem two_mul_lucasU_prime_add_one {p : ℕ} [Fact p.Prime] (P Q : ZMod p) :
    2 * lucasU P Q (p + 1) = P * (1 + lucasDiscr P Q ^ (p / 2)) := by
  rcases (Fact.out : p.Prime).eq_two_or_odd with h2 | hodd
  · subst h2
    revert P Q
    decide +revert
  · have hp2 : p ≠ 2 := by omega
    linear_combination (frobenius_entries hp2 P Q).2.1

/-- The neighbour below the prime index: `2 Q U_{p−1} = P (D ^ (p / 2) − 1)` over `ZMod p`, for
every prime `p` (at `p = 2` both sides are `0`). -/
theorem two_mul_mul_lucasU_prime_sub_one {p : ℕ} [Fact p.Prime] (P Q : ZMod p) :
    2 * Q * lucasU P Q (p - 1) = P * (lucasDiscr P Q ^ (p / 2) - 1) := by
  rcases (Fact.out : p.Prime).eq_two_or_odd with h2 | hodd
  · subst h2
    revert P Q
    decide +revert
  · have hp2 : p ≠ 2 := by omega
    linear_combination -(frobenius_entries hp2 P Q).2.2

/-- The Frobenius on a `2 × 2` matrix in odd prime characteristic `p`:
`(2 A) ^ p = (tr A) ^ p + ((tr A) ² − 4 det A) ^ (p / 2) (2 A − tr A)`. It is
`two_smul_lucasCompanion_pow_charP` with a general `A` for the companion matrix (that one is kept);
`N = 2 A − tr A` has `N ² = (tr A) ² − 4 det A`, by Cayley–Hamilton for `2 × 2` matrices. -/
private theorem two_smul_pow_charP_fin_two (p : ℕ) [Fact p.Prime] [CharP R p] (hp2 : p ≠ 2)
    (A : Matrix (Fin 2) (Fin 2) R) :
    ((2 : R) • A) ^ p
      = A.trace ^ p • (1 : Matrix (Fin 2) (Fin 2) R)
        + (A.trace ^ 2 - 4 * A.det) ^ (p / 2) • ((2 : R) • A - A.trace • 1) := by
  set N := (2 : R) • A - A.trace • (1 : Matrix (Fin 2) (Fin 2) R) with hN
  have hN2 : N ^ 2 = (A.trace ^ 2 - 4 * A.det) • (1 : Matrix (Fin 2) (Fin 2) R) := by
    rw [hN, sq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring
  have hodd : p = 2 * (p / 2) + 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hNp : N ^ p = (A.trace ^ 2 - 4 * A.det) ^ (p / 2) • N := by
    have : N ^ p = N ^ (2 * (p / 2) + 1) := by rw [← hodd]
    rw [this, pow_succ, pow_mul, hN2, smul_pow, one_pow, smul_mul_assoc, one_mul]
  have hsplit : (2 : R) • A = A.trace • 1 + N := by rw [hN]; abel
  have hcomm : Commute (A.trace • (1 : Matrix (Fin 2) (Fin 2) R)) N :=
    (Commute.one_left N).smul_left A.trace
  rw [hsplit, add_pow_char_of_commute p hcomm, smul_pow, one_pow, hNp]

/-- In odd prime characteristic `p`, `2 ^ p = 2` and `2` is a unit (helper). -/
private theorem two_pow_eq_two_and_isUnit (p : ℕ) [Fact p.Prime] [CharP R p] (hp2 : p ≠ 2) :
    (2 : R) ^ p = 2 ∧ IsUnit (2 : R) := by
  have h2z : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')
  refine ⟨?_, ?_⟩
  · have h := congrArg (ZMod.castHom (dvd_refl p) R) (ZMod.pow_card (2 : ZMod p))
    rwa [map_pow, map_ofNat] at h
  · have h := (isUnit_iff_ne_zero.mpr h2z).map (ZMod.castHom (dvd_refl p) R)
    rwa [map_ofNat] at h

/-- **`V (p n) = V n ^ p` in characteristic `p`**, for every prime `p`, every `n`, and every `P`,
`Q` in a commutative ring of characteristic `p`. -/
theorem lucasV_prime_mul (p : ℕ) [Fact p.Prime] [CharP R p] (P Q : R) (n : ℕ) :
    lucasV P Q (p * n) = lucasV P Q n ^ p := by
  rcases (Fact.out : p.Prime).eq_two_or_odd with h2 | hodd
  · subst h2
    have h20 : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
    rw [lucasV_two_mul, h20, zero_mul, sub_zero]
  · have hp2 : p ≠ 2 := by omega
    have hV : ∀ k, (lucasCompanion P Q ^ k).trace = lucasV P Q k := by
      intro k
      cases k with
      | zero => simp [Matrix.trace_one]
      | succ k => exact lucasCompanion_pow_succ_trace P Q k
    obtain ⟨h2p, hu⟩ := two_pow_eq_two_and_isUnit (R := R) p hp2
    have key := congrArg Matrix.trace (two_smul_pow_charP_fin_two p hp2 (lucasCompanion P Q ^ n))
    simp only [smul_pow, ← pow_mul', Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sub,
      Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat, hV, smul_eq_mul] at key
    rw [h2p] at key
    exact hu.mul_left_cancel (by linear_combination key)

/-- **`U (p n) = D ^ (p / 2) U n ^ p` in odd characteristic `p`**, with `D = P ² − 4 Q`. `p = 2` is
excluded: there the form is `U (2 n) = P U n ^ 2` (`lucasU_two_mul_of_char_two`), not
`D U n ^ 2`. -/
theorem lucasU_prime_mul (p : ℕ) [Fact p.Prime] [CharP R p] (hp2 : p ≠ 2) (P Q : R) (n : ℕ) :
    lucasU P Q (p * n) = lucasDiscr P Q ^ (p / 2) * lucasU P Q n ^ p := by
  have hodd : p = 2 * (p / 2) + 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hV : ∀ k, (lucasCompanion P Q ^ k).trace = lucasV P Q k := by
    intro k
    cases k with
    | zero => simp [Matrix.trace_one]
    | succ k => exact lucasCompanion_pow_succ_trace P Q k
  have hU : ∀ k, (lucasCompanion P Q ^ k) 1 0 = lucasU P Q k := by
    intro k
    cases k with
    | zero => simp
    | succ k => rw [lucasCompanion_pow_succ]; simp
  have hD : lucasV P Q n ^ 2 - 4 * (lucasCompanion P Q ^ n).det
      = lucasDiscr P Q * lucasU P Q n ^ 2 := by
    rw [lucasCompanion_pow_det]
    linear_combination lucasV_sq_sub_discr_mul_lucasU_sq P Q n
  obtain ⟨h2p, hu⟩ := two_pow_eq_two_and_isUnit (R := R) p hp2
  have key := congrArg (fun A : Matrix (Fin 2) (Fin 2) R => A 1 0)
    (two_smul_pow_charP_fin_two p hp2 (lucasCompanion P Q ^ n))
  simp only [smul_pow, ← pow_mul', hV, hD, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), hU, smul_eq_mul, mul_zero, sub_zero,
    zero_add] at key
  rw [h2p] at key
  have hUp : lucasU P Q n ^ p = lucasU P Q n ^ (2 * (p / 2) + 1) := by rw [← hodd]
  refine hu.mul_left_cancel ?_
  rw [key, hUp]
  ring

/-- **`V n = P U n` in characteristic `2`.** -/
theorem lucasV_eq_mul_lucasU_of_char_two [CharP R 2] (P Q : R) (n : ℕ) :
    lucasV P Q n = P * lucasU P Q n := by
  have h20 : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  cases n with
  | zero => rw [lucasV_zero, lucasU_zero, h20, mul_zero]
  | succ m =>
    linear_combination lucasV_succ_eq P Q m + lucasU_add_two P Q m - Q * lucasU P Q m * h20

/-- **`U (2 n) = P U n ^ 2` in characteristic `2`.** -/
theorem lucasU_two_mul_of_char_two [CharP R 2] (P Q : R) (n : ℕ) :
    lucasU P Q (2 * n) = P * lucasU P Q n ^ 2 := by
  rw [lucasU_two_mul, lucasV_eq_mul_lucasU_of_char_two]
  ring

/-- **`V (p ^ k) = P ^ (p ^ k)` in characteristic `p`**, for every prime `p` and every `k`;
`lucasV_prime_eq_pow` is the case `k = 1` (an `example` below). -/
theorem lucasV_prime_pow_eq_pow (p : ℕ) [Fact p.Prime] [CharP R p] (P Q : R) (k : ℕ) :
    lucasV P Q (p ^ k) = P ^ p ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_one, lucasV_one]
  | succ k ih =>
    rw [pow_succ', lucasV_prime_mul, ih, ← pow_mul]
    ring

/-- **`U (p ^ k) = D ^ (p ^ k / 2)` in odd characteristic `p`**, for every `k` (at `k = 0` both
sides are `1`). -/
theorem lucasU_prime_pow_eq_lucasDiscr_pow (p : ℕ) [Fact p.Prime] [CharP R p] (hp2 : p ≠ 2)
    (P Q : R) (k : ℕ) :
    lucasU P Q (p ^ k) = lucasDiscr P Q ^ (p ^ k / 2) := by
  have hpo : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have h1 : ∀ c : ℕ, (2 * c + 1) / 2 = c := fun c => by omega
  have hexp : ∀ j, p / 2 + p ^ j / 2 * p = p * p ^ j / 2 := by
    intro j
    have hj : p ^ j % 2 = 1 := by
      rw [Nat.pow_mod, hpo, one_pow]
      omega
    obtain ⟨a, ha⟩ : ∃ a, p = 2 * a + 1 := ⟨p / 2, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, p ^ j = 2 * b + 1 := ⟨p ^ j / 2, by omega⟩
    have hab : (2 * a + 1) * (2 * b + 1) = 2 * (a + b * (2 * a + 1)) + 1 := by ring
    rw [hb, ha, hab, h1, h1, h1]
  induction k with
  | zero => rw [pow_zero, lucasU_one, Nat.div_eq_of_lt one_lt_two, pow_zero]
  | succ k ih =>
    rw [pow_succ', lucasU_prime_mul p hp2, ih, ← pow_mul, ← pow_add, hexp k]

/-- **`U p = D ^ (p / 2)` in any commutative ring of odd prime characteristic `p`.** Round 24's
`lucasU_prime_eq_lucasDiscr_pow` has it over `ZMod p` for every prime, `p = 2` included, where it
holds because `x ^ 2 = x` in `ZMod 2`; over a general ring of characteristic `2` it fails
(`U 2 = P`, `D = P ²` there), so `p = 2` is excluded here. -/
theorem lucasU_prime_eq_lucasDiscr_pow_of_charP (p : ℕ) [Fact p.Prime] [CharP R p] (hp2 : p ≠ 2)
    (P Q : R) :
    lucasU P Q p = lucasDiscr P Q ^ (p / 2) := by
  simpa using lucasU_prime_mul p hp2 P Q 1

open Polynomial in
/-- **`dickson 1 a (p ^ k) = X ^ (p ^ k)` in characteristic `p`**, for every `a` and every `k`;
`dickson_one_eq_X_pow_of_charP` is the case `k = 1` (an `example` below). -/
theorem dickson_one_prime_pow_eq_X_pow (p : ℕ) [Fact p.Prime] [CharP R p] (a : R) (k : ℕ) :
    dickson 1 a (p ^ k) = X ^ p ^ k := by
  have h := lucasV_prime_pow_eq_pow (R := R[X]) p X (C a) k
  rwa [lucasV_eq_dickson_one_eval, ← map_dickson (C : R →+* R[X]), eval_map, eval₂_C_X] at h

/-- `lucasV_prime_eq_pow` is `lucasV_prime_pow_eq_pow` at `k = 1`. -/
example (p : ℕ) [Fact p.Prime] [CharP R p] (P Q : R) : lucasV P Q p = P ^ p := by
  simpa using lucasV_prime_pow_eq_pow p P Q 1

open Polynomial in
/-- `dickson_one_eq_X_pow_of_charP` is `dickson_one_prime_pow_eq_X_pow` at `k = 1`. -/
example (p : ℕ) [Fact p.Prime] [CharP R p] (a : R) : dickson 1 a p = X ^ p := by
  simpa using dickson_one_prime_pow_eq_X_pow p a 1

/-- Round 24's `lucasU_prime_eq_lucasDiscr_pow`, for odd `p`, is
`lucasU_prime_eq_lucasDiscr_pow_of_charP` at `R = ZMod p`. -/
example (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (P Q : ZMod p) :
    lucasU P Q p = lucasDiscr P Q ^ (p / 2) :=
  lucasU_prime_eq_lucasDiscr_pow_of_charP p hp2 P Q

end Frobenius

/-! ### The order's four items -/

/-- The index `p − (a / p)`, as a natural number: `p`, `p − 1` or `p + 1`. -/
private theorem toNat_sub_legendreSym (p : ℕ) [Fact p.Prime] (a : ℤ) :
    ((p : ℤ) - legendreSym p a).toNat = p ∨ ((p : ℤ) - legendreSym p a).toNat = p - 1 ∨
      ((p : ℤ) - legendreSym p a).toNat = p + 1 := by
  have h1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  by_cases ha : (a : ZMod p) = 0
  · left
    rw [(legendreSym.eq_zero_iff p a).mpr ha, sub_zero, Int.toNat_natCast]
  · rcases legendreSym.eq_one_or_neg_one p ha with h | h <;> rw [h] <;> omega

/-- **Item 1: `U_p ≡ (D / p)`**, for every prime `p` and all integers `P`, `Q`. -/
theorem lucasU_prime_modEq_legendreSym (p : ℕ) [Fact p.Prime] (P Q : ℤ) :
    lucasU P Q p ≡ legendreSym p (lucasDiscr P Q) [ZMOD p] := by
  rw [← ZMod.intCast_eq_intCast_iff, legendreSym.eq_pow]
  have h := map_lucasU (Int.castRingHom (ZMod p)) P Q p
  simp only [eq_intCast] at h
  rw [h, lucasU_prime_eq_lucasDiscr_pow]
  simp [lucasDiscr]

/-- **Item 1: `V_p ≡ P`**, for every prime `p` and all integers `P`, `Q`. -/
theorem lucasV_prime_modEq {p : ℕ} (hp : p.Prime) (P Q : ℤ) : lucasV P Q p ≡ P [ZMOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_eq_intCast_iff]
  have h := map_lucasV (Int.castRingHom (ZMod p)) P Q p
  simp only [eq_intCast] at h
  rw [h, lucasV_prime_eq]

/-- **Item 2, the law of apparition** (Lucas, 1878): for an odd prime `p` with `p ∣ Q → p ∣ P`,
`p ∣ U_{p − (D/p)}`. -/
theorem prime_dvd_lucasU_sub_legendreSym {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {P Q : ℤ}
    (hPQ : (p : ℤ) ∣ Q → (p : ℤ) ∣ P) :
    (p : ℤ) ∣ lucasU P Q ((p : ℤ) - legendreSym p (lucasDiscr P Q)).toNat := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hmap : ∀ n, ((lucasU P Q n : ℤ) : ZMod p) = lucasU (P : ZMod p) (Q : ZMod p) n := by
    intro n
    have h := map_lucasU (Int.castRingHom (ZMod p)) P Q n
    simpa only [eq_intCast] using h
  rw [hmap]
  have hD : ((lucasDiscr P Q : ℤ) : ZMod p) = lucasDiscr (P : ZMod p) (Q : ZMod p) := by
    simp [lucasDiscr]
  have h2 := two_ne_zero_of_ne_two hp2
  by_cases hQ : (Q : ZMod p) = 0
  · -- `p ∣ Q`, so `p ∣ P`: the sequence vanishes from index `2` on.
    have hP : (P : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd P p).mpr
      (hPQ ((ZMod.intCast_zmod_eq_zero_iff_dvd Q p).mp hQ))
    have hk : 2 ≤ ((p : ℤ) - legendreSym p (lucasDiscr P Q)).toNat := by
      rcases toNat_sub_legendreSym p (lucasDiscr P Q) with h | h | h <;> rw [h] <;> omega
    obtain ⟨m, hm⟩ : ∃ m, ((p : ℤ) - legendreSym p (lucasDiscr P Q)).toNat = m + 2 :=
      ⟨((p : ℤ) - legendreSym p (lucasDiscr P Q)).toNat - 2, by omega⟩
    rw [hm, hP, hQ, lucasU_add_two]
    simp
  · by_cases hD0 : (lucasDiscr (P : ZMod p) (Q : ZMod p)) = 0
    · have hl : legendreSym p (lucasDiscr P Q) = 0 := by
        rw [legendreSym.eq_zero_iff, hD, hD0]
      rw [hl, sub_zero, Int.toNat_natCast, lucasU_prime_eq_lucasDiscr_pow, hD0,
        zero_pow (by omega)]
    · rcases legendreSym.eq_one_or_neg_one p (a := lucasDiscr P Q) (by rw [hD]; exact hD0)
        with hl | hl
      · have hpow : lucasDiscr (P : ZMod p) (Q : ZMod p) ^ (p / 2) = 1 := by
          rw [← hD, ← legendreSym.eq_pow, hl, Int.cast_one]
        have hidx : ((p : ℤ) - legendreSym p (lucasDiscr P Q)).toNat = p - 1 := by
          rw [hl]; omega
        rw [hidx]
        have h := two_mul_mul_lucasU_prime_sub_one (P : ZMod p) (Q : ZMod p)
        rw [hpow, sub_self, mul_zero] at h
        exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero h2 hQ)
      · have hpow : lucasDiscr (P : ZMod p) (Q : ZMod p) ^ (p / 2) = -1 := by
          rw [← hD, ← legendreSym.eq_pow, hl, Int.cast_neg, Int.cast_one]
        have hidx : ((p : ℤ) - legendreSym p (lucasDiscr P Q)).toNat = p + 1 := by
          rw [hl]; omega
        rw [hidx]
        have h := two_mul_lucasU_prime_add_one (P : ZMod p) (Q : ZMod p)
        rw [hpow, add_neg_cancel, mul_zero] at h
        exact (mul_eq_zero.mp h).resolve_left h2

/-- The order's form of item 2: `p ∤ Q`. -/
example {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {P Q : ℤ} (hQ : ¬ (p : ℤ) ∣ Q) :
    (p : ℤ) ∣ lucasU P Q ((p : ℤ) - legendreSym p (lucasDiscr P Q)).toNat :=
  prime_dvd_lucasU_sub_legendreSym hp2 fun h => absurd h hQ

/-- **Item 3: the rank of apparition divides `p − (D/p)`**, for an odd prime `p ∤ Q`. -/
theorem lucasApparition_dvd_sub_legendreSym {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {P Q : ℤ}
    (hQ : ¬ (p : ℤ) ∣ Q) :
    lucasApparition (P : ZMod p) (Q : ZMod p)
      ∣ ((p : ℤ) - legendreSym p (lucasDiscr P Q)).toNat :=
  (prime_dvd_lucasU_iff Fact.out hQ _).mp
    (prime_dvd_lucasU_sub_legendreSym hp2 fun h => absurd h hQ)

/-- `(5 / p) = (p / 5)` for an odd prime `p`, by quadratic reciprocity (`5 ≡ 1 mod 4`). -/
private theorem legendreSym_five {p : ℕ} [Fact p.Prime] [Fact (Nat.Prime 5)] (hp2 : p ≠ 2) :
    legendreSym p 5 = legendreSym 5 ((p % 5 : ℕ) : ℤ) := by
  have h := legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p) (by norm_num) hp2
  push_cast at h
  rw [h, legendreSym.mod 5 (p : ℤ)]
  norm_cast

/-- `p ∤ -1`, since `-1` is a unit, so item 2's hypothesis holds at `(P, Q) = (1, -1)`. -/
private theorem dvd_neg_one_imp {p : ℕ} (hp : p.Prime) :
    (p : ℤ) ∣ -1 → (p : ℤ) ∣ 1 := fun h =>
  absurd (Int.natCast_dvd_natCast.mp (by simpa using h : (p : ℤ) ∣ ((1 : ℕ) : ℤ)))
    hp.not_dvd_one

/-- **Item 4, Fibonacci**: `p ∣ F_{p−1}` for a prime `p ≡ ±1 (mod 5)`. -/
theorem prime_dvd_fib_sub_one {p : ℕ} (hp : p.Prime) (h5 : p % 5 = 1 ∨ p % 5 = 4) :
    p ∣ Nat.fib (p - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hl : legendreSym p (lucasDiscr (1 : ℤ) (-1)) = 1 := by
    rw [show lucasDiscr (1 : ℤ) (-1) = 5 by norm_num [lucasDiscr], legendreSym_five hp2]
    rcases h5 with h | h <;> rw [h]
    · exact legendreSym.at_one 5
    · exact legendreSym.sq_one' 5 (a := 2) (by decide +revert)
  have h := prime_dvd_lucasU_sub_legendreSym hp2 (dvd_neg_one_imp hp)
  rw [hl, show ((p : ℤ) - 1).toNat = p - 1 by omega, lucasU_one_neg_one ℤ] at h
  exact_mod_cast h

/-- **Item 4, Fibonacci**: `p ∣ F_{p+1}` for a prime `p ≡ ±2 (mod 5)`; `p = 2` included. -/
theorem prime_dvd_fib_add_one {p : ℕ} (hp : p.Prime) (h5 : p % 5 = 2 ∨ p % 5 = 3) :
    p ∣ Nat.fib (p + 1) := by
  rcases eq_or_ne p 2 with rfl | hp2
  · decide
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hl : legendreSym p (lucasDiscr (1 : ℤ) (-1)) = -1 := by
    rw [show lucasDiscr (1 : ℤ) (-1) = 5 by norm_num [lucasDiscr], legendreSym_five hp2]
    rcases h5 with h | h <;> rw [h]
    · rw [show (((2 : ℕ) : ℤ)) = 2 by norm_num, legendreSym.at_two (by norm_num)]
      decide
    · rw [show (((3 : ℕ) : ℤ)) = (-2) % ((5 : ℕ) : ℤ) by norm_num, ← legendreSym.mod,
        legendreSym.at_neg_two (by norm_num)]
      decide
  have h := prime_dvd_lucasU_sub_legendreSym hp2 (dvd_neg_one_imp hp)
  rw [hl, show ((p : ℤ) - -1).toNat = p + 1 by omega, lucasU_one_neg_one ℤ] at h
  exact_mod_cast h

/-- At `p = 5`, where `D = 5`: `5 ∣ F_5`. -/
example : 5 ∣ Nat.fib 5 := by decide

end ClassicalLean
