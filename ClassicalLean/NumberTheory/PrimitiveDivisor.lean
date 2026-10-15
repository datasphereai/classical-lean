/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorial.Basic
import ClassicalLean.NumberTheory.LucasApparition

/-!
# Primitive prime divisors of `a ^ n - 1`

A prime `p` is a **primitive divisor** of `a ^ n - 1` when it divides `a ^ n - 1` and divides no
earlier `a ^ m - 1`.  That is a statement about *divisibility*; the whole content of this file is
that it is the same statement as `orderOf (a : ZMod p) = n`, and that the cyclotomic machinery
already in Mathlib then produces such a `p`.

## What is here

* `IsPrimitiveDivisor` — the definition, in divisibility form.
* `dvd_pow_sub_one_iff` — `p ∣ a ^ m - 1 ↔ (a : ZMod p) ^ m = 1` for `0 < a`, the cast step that
  makes the natural subtraction harmless.  No primality.
* `isPrimitiveDivisor_iff_orderOf` — **the translation**: `IsPrimitiveDivisor p a n ↔
  orderOf (a : ZMod p) = n`.
* `isPrimitiveDivisor_iff_isPrimitiveRoot` — the same statement in Mathlib's own vocabulary.
* `IsPrimitiveDivisor.not_dvd_base` — a primitive divisor does not divide the base.
* `orderOf_eq_of_isRoot_cyclotomic` — the cyclotomic bridge; see the warning on it.
* `exists_isPrimitiveDivisor_of_forall_prime_dvd` — **existence** when every prime dividing `n`
  divides `a`.
* an `example` closing Mathlib's `Nat.exists_prime_gt_modEq_one` from that existence theorem, and
  an `example` tying `IsPrimitiveDivisor p 2 n` to `LucasApparition`.
* after the namespace, an `example` stating the existence theorem with `0 < a` in place of
  `2 ≤ a` (order LEAN-29).

## Why `ℕ`, and why `2 ≤ a` / `0 < a`

The definition is over `ℕ` with truncated subtraction.  That is safe, and the boundary was
enumerated numerically before any Lean was written (a script over `p` prime `< 101`,
`a = 0..30`, `n = 0..30`, 24025 triples, comparing the divisibility definition against
`orderOf`).  The measured junk set is exactly

    {n = 0, any a}  ∪  {a = 1, n = 1}  ∪  {a = 0, n = 1}

and only the last of those three is a `ℕ`-truncation artefact.  **Moving the definition to `ℤ`
buys only that one cell**: on the small grid `(a, n) ∈ 0..5 × 0..5`, the pairs where *every*
prime `< 101` counts as primitive number 8 under the `ℕ` phrasing and 7 under `(a : ℤ) ^ n - 1`
— the single pair removed is `(0,1)`, and `(1,1)` and every `(a,0)` survive in both.  So `ℤ` does
not repair the degeneracy and a hypothesis is needed either way; `ℕ` is kept because it is the
shape `MersenneOrder.dvd_mersenne_iff_orderOf_dvd` and `LucasApparition` already speak, and
because under `2 ≤ a` and `0 < n` the `ℕ` and `ℤ` phrasings were measured to agree on all 570
pairs of the grid `a = 2..20`, `n = 1..30`.

The hypotheses on the iff are `0 < a` and `0 < n`, and both are load-bearing:

* `0 < n` — at `n = 0` the definition is vacuously satisfied by *every* prime (`p ∣ a ^ 0 - 1 = 0`,
  and the `m` range is empty) while `orderOf` is never `0` in `ZMod p`.  Measured over the `ℕ`
  phrasing shipped here: with no hypothesis the two sides disagree on 732 of the 24025 triples,
  707 of them at `n = 0` and the other 25 at `a = 0`.  (The `ℤ` phrasing has exactly the 707.)
* `0 < a` — at `a = 0` and `n = 1`, `0 ^ 1 - 1` truncates to `0` and every prime divides it.
  Measured: adding `0 < n` alone cuts the 732 to exactly those 25 disagreements (one per prime
  tested), all at `a = 0`.

`0 < a` rather than `2 ≤ a` is *inferred* from two measured rows rather than measured directly:
the row `0 < n ∧ ¬ p ∣ a` (21210 triples, 0 mismatches) covers every `a = 1` triple, and the row
`0 < n ∧ 2 ≤ a` (21750 triples, 0 mismatches) covers the rest, so their union covers
`0 < n ∧ 0 < a`.  Note also that the proposed hypothesis `¬ p ∣ a` is *not* the right one on its
own: it removes none of the 707 `n = 0` failures, and for `n ≥ 1` it is redundant — of the 2040
tested triples with `p ∣ a` and `n ≥ 1`, both sides of the iff were false in all 2040.

`exists_isPrimitiveDivisor_of_forall_prime_dvd` states the stronger `2 ≤ a`; `0 < a` suffices
(the `example` at the end of this file, order LEAN-29), since `a = 1` is already excluded by the
hypothesis itself once `1 < n`. Some hypothesis excluding `a = 0` is needed: `a = 0` satisfies the
hypothesis trivially (every prime divides `0`), but for `n ≥ 2` no prime is primitive there, since
`0 ^ 1 - 1` truncates to `0`, which every prime divides (in `ℤ`, `Φₙ(0) = 1` has no prime factor).

## What is not here

**Dated 2026-09-24 UTC (order G-6, round 22):** Zsigmondy's theorem for `aⁿ − 1`, with its exact
exceptional set, is now proved in `NumberTheory/Zsigmondy` (`exists_isPrimitiveDivisor_iff`),
this file's first consumer outside it. The paragraphs below are kept as written and are
superseded on three points: the case `p ∣ n` is handled there without Lifting the Exponent, by a
geometric sum (and `Nat.emultiplicity_pow_sub_pow` is at `NumberTheory/Multiplicity.lean:216` at
v4.34.0, not `:218`); the bound needed is `Φₙ(a) > P(n)`, the largest prime factor of `n`, not
`Φₙ(a) > n`; and at `a = 2` that bound follows from Mathlib's existing bounds through the
cyclotomic expansion identities, so it was not the blocker described below.

**Zsigmondy's theorem is not here, and no part of this file should be read as a step toward it
that only needs finishing.**  The missing case is `p ∣ n`: there `p` can divide `Φₙ(a)` without
being primitive.  The standard proof handles that in two steps, and **Mathlib has the first
one already in scope from this file's own imports**: Lifting the Exponent bounds the
non-primitive part of `Φₙ(a)` to a single prime to the first power, as
`Nat.emultiplicity_pow_sub_pow` (`NumberTheory/Multiplicity.lean:218`) and its `Int` twin —
`#check` resolves both against the import block below, rc 0, and nothing here uses them.

The second step is the blocker: producing a *further* prime needs a lower bound `Φₙ(a) > n`, and
the sharpest bound Mathlib has, `sub_one_pow_totient_lt_cyclotomic_eval`, gives only
`(a - 1) ^ totient n`, which is `1` at `a = 2`.  That is not a gap in the write-up; it is exactly
why `(a, n) = (2, 6)` is exceptional — there the non-primitive part *is* all of `Φ₆(2) = 3`.

The exceptional set itself is not formalised.  It was enumerated: on `a = 2..20`, `n = 1..30`
(570 pairs) the pairs with **no** primitive divisor are exactly `(2,1), (2,6), (3,2), (7,2),
(15,2)`, and on `a = 2..50`, `n = 1..40` exactly those plus `(31,2)`.  Note the usual loose
statement "`n = 1` is exceptional" is wrong: at `n = 1` the `m` range is empty, so `p` is
primitive iff `p ∣ a - 1`, which fails only when `a - 1 = 1`.  The exceptional pair is `(2,1)`,
not the line `n = 1`.

The existence theorem here is **true but coarse**, and the file says so rather than letting the
reader assume coverage.  On the grid `a = 2..100`, `n = 1..60` (5940 pairs) its hypothesis holds
on 790 pairs (13.30%), of which 99 are the vacuous `n = 1`; its conclusion holds on 5123 pairs
(86.25%), so it captures 15.42% of the cases where its own conclusion is true.  At `a = 2` the
hypothesis admits only `n ∈ {1, 2, 4, 8, 16, 32}` — powers of two, no odd `n` at all — while 53
further `n ≤ 60` have a primitive divisor of `2 ^ n - 1` anyway.  The per-prime side condition
`¬ p ∣ n` used inside the proof is strictly stronger and covered 5940/5940 of those pairs; the
`(a, n)`-level hypothesis is what is easy to state, not what is sharp.

## Mathlib status, measured

The name search is not the evidence and is recorded only to be dismissed:
`grep -rni 'Zsigmondy\|primitive divisor\|primitiveDivisor' Mathlib --include=*.lean` returns 0.
This project has three logged instances of a gap claim resting on a grep for a *name*, so the
claim below is a search for the *mathematics*.

Positive control first, so that a zero elsewhere means something:

    grep -rnE '\^ ?[a-zA-Z]+ ?- ?1' ClassicalLean --include=*.lean | grep -E 'orderOf'

returns 3 lines, two of them the statement `p ∣ 2 ^ m - 1 ↔ orderOf (2 : ZMod p) ∣ m`
(`MersenneOrder.lean:62`, `LucasApparition.lean:283`).  The same shape against Mathlib:

    grep -rnE '∣ [a-zA-Z]+ ?\^ ?[a-zA-Z]+ ?- ?1' Mathlib --include=*.lean

returns 13 lines, and **none** of them is a prime dividing `a ^ n - 1`: they are
`x - 1 ∣ x ^ n - 1` and `x ^ m - 1 ∣ x ^ k - 1` (`Algebra/Ring/GeomSum.lean`,
`NumberTheory/FermatPsp.lean`), polynomial divisibilities *into* `X ^ n - 1`
(`RingTheory/Polynomial/Cyclotomic/Basic.lean`, and `RingTheory/RootsOfUnity/Minpoly.lean:53,125`,
whose left sides are `minpoly ℤ μ` and `P * Q`, not `cyclotomic n R`), and one comment line
(`RingTheory/LittleWedderburn.lean:84`) — which is what accounts for all 13.  For the
minimality clause,

    grep -rnE '∀ m[, ].*m < .*¬' Mathlib --include=*.lean | grep '∣'

returns exactly 1 line, `Nat.prime_def_lt'` (`Data/Nat/Prime/Defs.lean:114`), which is about
`m ∣ p`, not about `p ∣ a ^ m - 1`.  So Mathlib states nothing of this **divisibility** shape.

It does, however, *name the object*: `isRoot_cyclotomic_iff.mp hroot` at
`PrimesCongruentOne.lean:57` has type `IsPrimitiveRoot (b : ZMod p) k` before `.eq_orderOf` is
applied, and `isPrimitiveDivisor_iff_isPrimitiveRoot` below is three lines from the `orderOf`
form and needs no primality instance.  What is genuinely absent is the ℕ-**divisibility**
dictionary — the `p ∣ a ^ n - 1` phrasing the classical literature uses — not the concept.

What Mathlib has as an *argument*, inline and unnamed, is the construction.
`Nat.exists_prime_gt_modEq_one`
(`NumberTheory/PrimesCongruentOne.lean:28`) runs the entire primitive-divisor construction for
`b ^ k - 1` with `b = k * n !`, and its line 57 (`grep -n eq_orderOf` on that file returns that
one line),
`have : k = orderOf (b : ZMod p) := (isRoot_cyclotomic_iff.mp hroot).eq_orderOf`, *is* the
statement "`p` is a primitive prime divisor of `b ^ k - 1`" — written for another purpose and
never extracted.  The `example` below closes that theorem from the extraction, which is the test
that the extraction is the right one.
-/

namespace ClassicalLean

open Polynomial

/-- `p` is a **primitive prime divisor** of `a ^ n - 1`: it divides `a ^ n - 1` and divides no
earlier `a ^ m - 1`.

Stated over `ℕ`; see the module docstring for why, and for the measured junk set.  The intended
domain is `2 ≤ a` and `0 < n`, and every theorem below carries the hypothesis it actually needs
rather than folding one into the definition — the definition is the classical one verbatim, so
that `isPrimitiveDivisor_iff_orderOf` is a theorem about the classical notion and not about a
notion pre-trimmed to make it true. -/
def IsPrimitiveDivisor (p a n : ℕ) : Prop :=
  p.Prime ∧ p ∣ a ^ n - 1 ∧ ∀ m : ℕ, 0 < m → m < n → ¬ p ∣ a ^ m - 1

/-- The cast step: for `0 < a` the truncated subtraction is harmless, because `1 ≤ a ^ m`.

There is deliberately **no primality hypothesis**: nothing here needs one, and `ZMod p` for
composite `p` is a perfectly good commutative ring for this statement. -/
theorem dvd_pow_sub_one_iff {p a m : ℕ} (ha : 0 < a) :
    p ∣ a ^ m - 1 ↔ (a : ZMod p) ^ m = 1 := by
  have h1 : (1 : ℕ) ≤ a ^ m := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ ha.ne')
  constructor
  · intro h
    have hz : ((a ^ m - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
    rw [Nat.cast_sub h1] at hz
    push_cast at hz
    linear_combination hz
  · intro h
    refine (ZMod.natCast_eq_zero_iff _ _).mp ?_
    rw [Nat.cast_sub h1]
    push_cast
    rw [h]
    ring

/-- **The translation layer.**  The divisibility definition of a primitive divisor is the same
statement as `orderOf (a : ZMod p) = n`.

Read honestly: once `dvd_pow_sub_one_iff` has moved both clauses into `ZMod p`, this *is*
Mathlib's `orderOf_eq_iff` with the quantifiers permuted.  The content is not the group theory —
it is that the divisibility phrasing, the one the classical literature uses and the one Mathlib
does not state (see the module docstring's greps), is that group-theoretic statement.

Both hypotheses are load-bearing and both were located numerically, not guessed; the module
docstring records the counts.  `hp` is used only in the `←` direction, where `p.Prime` has to be
produced to build the `IsPrimitiveDivisor`. -/
theorem isPrimitiveDivisor_iff_orderOf {p a n : ℕ} (hp : p.Prime) (ha : 0 < a) (hn : 0 < n) :
    IsPrimitiveDivisor p a n ↔ orderOf ((a : ZMod p)) = n := by
  rw [orderOf_eq_iff hn]
  constructor
  · rintro ⟨-, hdvd, hmin⟩
    exact ⟨(dvd_pow_sub_one_iff ha).mp hdvd,
      fun m hmn hm hpow => hmin m hm hmn ((dvd_pow_sub_one_iff ha).mpr hpow)⟩
  · rintro ⟨hpow, hmin⟩
    exact ⟨hp, (dvd_pow_sub_one_iff ha).mpr hpow,
      fun m hm hmn hd => hmin m hmn hm ((dvd_pow_sub_one_iff ha).mp hd)⟩

/-- **The same statement in Mathlib's own vocabulary**: a primitive divisor of `a ^ n - 1` is
exactly a prime for which `a` is a primitive `n`-th root of unity mod `p`.

Worth stating because it locates precisely what Mathlib is missing.  Mathlib *has* the concept —
`IsPrimitiveRoot` — and uses it at `PrimesCongruentOne.lean:57`.  What it does not have is the
`p ∣ a ^ n - 1` dictionary, and this iff is the bridge between the two vocabularies.  It needs no
`Fact p.Prime` instance: `IsPrimitiveRoot` is defined over a `CommMonoid`. -/
theorem isPrimitiveDivisor_iff_isPrimitiveRoot {p a n : ℕ} (hp : p.Prime)
    (ha : 0 < a) (hn : 0 < n) :
    IsPrimitiveDivisor p a n ↔ IsPrimitiveRoot ((a : ZMod p)) n := by
  rw [isPrimitiveDivisor_iff_orderOf hp ha hn]
  exact ⟨fun h => h ▸ IsPrimitiveRoot.orderOf _, fun h => h.eq_orderOf.symm⟩

/-- A primitive divisor of `a ^ n - 1` does not divide `a`.

This is the hypothesis `¬ p ∣ a` that the classical statements carry, recovered rather than
assumed — measured over the same grid: of 2040 tested triples with `p ∣ a` and `n ≥ 1`, the
primitive-divisor condition was false in all 2040, and there were 0 counterexamples to this
implication. -/
theorem IsPrimitiveDivisor.not_dvd_base {p a n : ℕ} (ha : 0 < a) (hn : 0 < n)
    (h : IsPrimitiveDivisor p a n) : ¬ p ∣ a := by
  intro hpa
  have : Fact p.Prime := ⟨h.1⟩
  have h0 : (a : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpa
  have hone := (dvd_pow_sub_one_iff (p := p) (m := n) ha).mp h.2.1
  rw [h0, zero_pow hn.ne'] at hone
  exact zero_ne_one hone

/-- The cyclotomic bridge: a root of `cyclotomic n` in `ZMod p` has order exactly `n`, provided
`¬ p ∣ n`.

**This is a one-line consequence of `isRoot_cyclotomic_iff` and must not be mistaken for the
content of this module.**  The proof is `((isRoot_cyclotomic_iff.mp hroot).eq_orderOf).symm`;
everything it does is supply the `NeZero (n : ZMod p)` instance that `isRoot_cyclotomic_iff`
wants.  It is stated here only because the side condition deserves to be an explicit hypothesis
`¬ p ∣ n` — the arithmetic condition a caller can check — rather than a typeclass argument about
a cast that a caller has to discharge at the instance level.  Note `¬ p ∣ n` already forces
`n ≠ 0`, so no positivity hypothesis is stated: adding one would leave it unused.

`[Fact p.Prime]` is **proof-route, not statement** — the same category `LucasApparition.lean`
records for its `p ≠ 2`.  It is needed only to synthesize `IsDomain (ZMod p)` for
`isRoot_cyclotomic_iff`; dropping it fails with exactly that instance error.  The arithmetic
holds without it: swept over composite moduli `m < 301` and `n ≤ 30`, the 846 cells with
`m ∣ Φₙ(a)` and `¬ m ∣ n` gave 0 counterexamples to `ord_m(a) = n`, against 26 counterexamples
for the same sweep with the `¬ m ∣ n` hypothesis dropped.

In Zsigmondy language `¬ p ∣ n` is the avoidance of the hard case, and the module docstring says
why that case is out of scope. -/
theorem orderOf_eq_of_isRoot_cyclotomic {p n a : ℕ} [Fact p.Prime] (hpn : ¬ p ∣ n)
    (hroot : IsRoot (cyclotomic n (ZMod p)) (Nat.castRingHom (ZMod p) a)) :
    orderOf ((a : ZMod p)) = n := by
  have : NeZero ((n : ZMod p)) := NeZero.of_not_dvd (ZMod p) hpn
  exact ((isRoot_cyclotomic_iff.mp hroot).eq_orderOf).symm

/-- **Existence of a primitive divisor** when every prime dividing `n` also divides `a`.

The route is the one `Nat.exists_prime_gt_modEq_one` runs inline: `|Φₙ(a)| > 1` by
`sub_one_lt_natAbs_cyclotomic_eval`, take `p = minFac` of it, `p ∣ Φₙ(a)` makes `a` a root of
`cyclotomic n` over `ZMod p`, `coprime_of_root_cyclotomic` gives `¬ p ∣ a`, the hypothesis then
gives `¬ p ∣ n`, and `orderOf_eq_of_isRoot_cyclotomic` plus `isPrimitiveDivisor_iff_orderOf`
finish.  The hypothesis is exactly what turns the per-prime side condition `¬ p ∣ n` into
something checkable from `(a, n)` alone.

`1 < n` is not removable: `(a, n) = (2, 1)` is a genuine exceptional pair, since at `n = 1` a
primitive divisor is a prime factor of `a - 1` and `2 - 1 = 1` has none.  `2 ≤ a` is not
removable — but it *is* weakenable to `0 < a` by a case split, since the radical hypothesis is
itself false at `a = 1` once `1 < n`; the stronger form is the `example` at the end of this file
(order LEAN-29), and `2 ≤ a` is kept because it matches what `sub_one_lt_natAbs_cyclotomic_eval`
wants and the case split buys one vacuous value of `a`.  What removal costs: `a = 0` satisfies the
hypothesis trivially while `Φₙ(0) = 1`.  (`a = 1` needs no separate exclusion — with `1 < n` some
prime divides `n`, and no prime divides `1`.)

For how much of the ground this covers — 13.30% of a 5940-pair grid, and no odd `n` at `a = 2` —
see the module docstring.  It is a sufficient condition, not a characterisation. -/
theorem exists_isPrimitiveDivisor_of_forall_prime_dvd {a n : ℕ} (ha : 2 ≤ a) (hn : 1 < n)
    (hrad : ∀ q : ℕ, q.Prime → q ∣ n → q ∣ a) :
    ∃ p : ℕ, IsPrimitiveDivisor p a n := by
  have hgt : 1 < (eval (a : ℤ) (cyclotomic n ℤ)).natAbs := by
    calc 1 ≤ a - 1 := by omega
      _ < (eval (a : ℤ) (cyclotomic n ℤ)).natAbs :=
        sub_one_lt_natAbs_cyclotomic_eval hn (by omega)
  let p := Nat.minFac (eval (a : ℤ) (cyclotomic n ℤ)).natAbs
  have hprime : Fact p.Prime := ⟨Nat.minFac_prime (ne_of_lt hgt).symm⟩
  have hroot : IsRoot (cyclotomic n (ZMod p)) (Nat.castRingHom (ZMod p) a) := by
    have h : ((a : ℤ) : ZMod p) = ↑(Int.castRingHom (ZMod p) a) := by simp
    rw [IsRoot.def, ← map_cyclotomic_int n (ZMod p), eval_map, Nat.coe_castRingHom,
      ← Int.cast_natCast, h, eval₂_hom, Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd]
    apply Int.dvd_natAbs.1
    exact mod_cast Nat.minFac_dvd (eval (a : ℤ) (cyclotomic n ℤ)).natAbs
  have hpa : ¬ p ∣ a :=
    hprime.1.coprime_iff_not_dvd.1 (coprime_of_root_cyclotomic (by omega) hroot).symm
  have hpn : ¬ p ∣ n := fun h => hpa (hrad p hprime.1 h)
  exact ⟨p, (isPrimitiveDivisor_iff_orderOf hprime.1 (by omega) (by omega)).mpr
    (orderOf_eq_of_isRoot_cyclotomic hpn hroot)⟩

/-! ### The real-work test

`Nat.exists_prime_gt_modEq_one` is restated verbatim and closed from
`exists_isPrimitiveDivisor_of_forall_prime_dvd`.

**Nothing here is shorter, and the docstring should not imply it is.**  Mathlib's proof is 32
lines (`PrimesCongruentOne.lean:28-59`) building the primitive divisor by hand; the existence
theorem is 20 lines and this example is 25, so 45 against 32.  The existence theorem is in fact
that proof's middle section with `(b, k)` generalised to `(a, n)` — measured to use the same
eleven named lemmas in the same order.  What changed is not length: the primitive-divisor step
now has a name, a reusable statement, and a hypothesis phrased in `(a, n)` rather than in the
ad-hoc witness `k · n !`.

Two honest notes.  First, the `k = 1` branch gets **nothing** from this module and is closed by
`Nat.exists_infinite_primes`, exactly as Mathlib does.  The split is forced by
`exists_isPrimitiveDivisor_of_forall_prime_dvd`'s `1 < n`, which fails outright at `k = 1`, and
that hypothesis is there because `(a, n) = (2, 1)` is a genuine exceptional pair — at `N = 2`
the branch would be asking for a primitive divisor of `2 ^ 1 - 1 = 1`.  Being precise about
what that costs: for `N ≥ 3` the *conclusion* still holds (`N ! - 1` has a prime factor), so at
those `N` it is the hypothesis and not the mathematics that blocks, and the branch is closed by
Mathlib's own route rather than by a sharper theorem here.  Second, the choice `b = k * n !` is
what makes the hypothesis
"every prime dividing `k` divides `b`" hold, and it holds for the trivial reason `q ∣ k ∣ b`;
`IsPrimitiveDivisor.not_dvd_base` then supplies both `(b : ZMod p) ≠ 0` for Fermat and the
`n < p` step.

The test cannot be passed by accident: `Mathlib.NumberTheory.PrimesCongruentOne` is **not**
imported here, and is not reachable transitively either — elaborating this file's import block
followed by `#check @Nat.exists_prime_gt_modEq_one` fails with
`Unknown constant 'Nat.exists_prime_gt_modEq_one'`.  The statement below was separately checked
to be Mathlib's, by elaborating `fun N hk0 => Nat.exists_prime_gt_modEq_one N hk0` against it in
a file that does import that module. -/
example {k : ℕ} (N : ℕ) (hk0 : k ≠ 0) :
    ∃ p : ℕ, Nat.Prime p ∧ N < p ∧ p ≡ 1 [MOD k] := by
  rcases (Nat.one_le_iff_ne_zero.2 hk0).eq_or_lt with (rfl | hk1)
  · obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes (N + 1)
    exact ⟨p, hp, hNp, Nat.modEq_one⟩
  · set b := k * Nat.factorial N with hbdef
    have hb2 : 2 ≤ b := by
      calc 2 ≤ k := hk1
        _ = k * 1 := (mul_one k).symm
        _ ≤ k * Nat.factorial N := Nat.mul_le_mul_left k N.factorial_pos
    have hrad : ∀ q : ℕ, q.Prime → q ∣ k → q ∣ b := fun q _ hq => hq.mul_right _
    obtain ⟨p, hpd⟩ := exists_isPrimitiveDivisor_of_forall_prime_dvd hb2 hk1 hrad
    have hp : p.Prime := hpd.1
    have : Fact p.Prime := ⟨hp⟩
    have hpb : ¬ p ∣ b := hpd.not_dvd_base (by omega) (by omega)
    have hord : orderOf ((b : ZMod p)) = k :=
      (isPrimitiveDivisor_iff_orderOf hp (by omega) (by omega)).mp hpd
    have hdvd : orderOf ((b : ZMod p)) ∣ p - 1 :=
      ZMod.orderOf_dvd_card_sub_one (mt (ZMod.natCast_eq_zero_iff b p).mp hpb)
    refine ⟨p, hp, ?_, ?_⟩
    · by_contra habs
      push Not at habs
      exact hpb (by rw [hbdef]; exact dvd_mul_of_dvd_right (Nat.dvd_factorial hp.pos habs) k)
    · rw [hord] at hdvd
      exact ((Nat.modEq_iff_dvd' hp.pos).2 hdvd).symm

/-! ### Cross-item: the Mersenne slice

`ClassicalLean.lucasApparition_three_two_eq_orderOf`
(`ClassicalLean/NumberTheory/LucasApparition.lean`) says that at `(P,Q) = (3,2)`, where
`U n = 2 ^ n - 1`, the rank of apparition is `orderOf (2 : ZMod p)`.  Composing it with
`isPrimitiveDivisor_iff_orderOf` at `a = 2` says the three notions — primitive divisor of a
Mersenne number, rank of apparition of `U(3,2)`, and the multiplicative order of `2` — are one
object at this parameter.

`hn : 0 < n` is the same hypothesis the iff carries.  `hp2 : p ≠ 2` is inherited from
`lucasApparition_three_two_eq_orderOf`, where that file records it as **proof-route rather than
statement**; nothing is claimed here about `p = 2` beyond what that file measured. -/
example {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n) :
    IsPrimitiveDivisor p 2 n ↔ lucasApparition (3 : ZMod p) 2 = n := by
  rw [isPrimitiveDivisor_iff_orderOf hp (by norm_num) hn,
    lucasApparition_three_two_eq_orderOf hp hp2]
  norm_num

end ClassicalLean

/-- The stronger form of `exists_isPrimitiveDivisor_of_forall_prime_dvd` that its docstring
describes (order LEAN-29): `0 < a` in place of `2 ≤ a`, by the case split at `a = 1`, where the
radical hypothesis fails once `1 < n`, since the smallest prime factor of `n` would divide `1`. -/
example {a n : ℕ} (ha : 0 < a) (hn : 1 < n) (hrad : ∀ q : ℕ, q.Prime → q ∣ n → q ∣ a) :
    ∃ p : ℕ, ClassicalLean.IsPrimitiveDivisor p a n := by
  rcases Nat.lt_or_ge a 2 with h | h
  · obtain rfl : a = 1 := by omega
    have hq := Nat.minFac_prime (show n ≠ 1 by omega)
    exact absurd (hrad _ hq (Nat.minFac_dvd n)) hq.not_dvd_one
  · exact ClassicalLean.exists_isPrimitiveDivisor_of_forall_prime_dvd h hn hrad
