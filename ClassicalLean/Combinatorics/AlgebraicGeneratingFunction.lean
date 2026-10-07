/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Combinatorics.RecurrenceGeneratingFunction
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Schroder
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Combinatorics.Enumerative.Schroder

/-!
# Algebraic generating functions, and uniqueness of their functional equations

`Combinatorics/RecurrenceGeneratingFunction.lean` handles linear recurrences with constant
coefficients, whose generating functions are **rational**.  The Catalan, Schröder and Motzkin
numbers are not of that kind: their recurrences are **convolutions**, and their generating
functions satisfy quadratic equations.  This module is the companion for that case.

The content is one theorem:

    eq_of_eq_C_add_X_mul (hq : IsLocal q) (c) (f g)
      (hf : f = C c + X * q f) (hg : g = C c + X * q g) : f = g

A power series is determined by a functional equation `f = C c + X * q f` whenever `q` is
**local** — `coeff n (q a)` depends only on `coeff m a` for `m ≤ n`.  Locality is closed under
the operations one actually writes (`isLocal_add`, `isLocal_mul`, `isLocal_pow`,
`isLocal_const`, `isLocalId`), so for any concrete equation it is discharged by composition
rather than by a new argument.

The multiplication by `X` is what makes this true and is not decoration: it is what turns the
equation into a strong induction on coefficients.

**Dated 2026-09-24 (order G-8, J3; round 26):** the module now also holds one result that does
not use this theorem, `not_isSolution_catalan` with its `ℕ` case (see "Sibling, not extension"
and "What is here").

## Sibling, not extension

This is a **sibling** of `RecurrenceGeneratingFunction.lean`, not an extension of it, and the
distinction is a type-level fact rather than a matter of taste.  `LinearRecurrence` indexes its
coefficients by position in a fixed window — `LinearRecurrence.mk : (order : ℕ) →
(Fin order → R) → LinearRecurrence R` — so a convolution has no representation as one, and
nothing here specialises to anything there.  What *would* make it a genuine extension is
uniqueness for `f = p + X ^ d * q f` with `p` a polynomial vanishing from `d` on, after which a
`LinearRecurrence` solution is the instance `q f = ∑ C (a i) * X ^ i * f`.  That is **not**
attempted here and is not claimed.

**Dated 2026-09-24 (order G-8, J3; round 26):** this module now imports
`RecurrenceGeneratingFunction` for `not_isSolution_catalan` and its `ℕ` case: the Catalan numbers
satisfy no `LinearRecurrence` at all, over any nontrivial commutative ring — the mathematical
counterpart of the type-level remark above. It is a statement about a sequence, not the extension
this paragraph describes, which is still not attempted.

## `CommSemiring`, deliberately

Everything is stated over `[CommSemiring R]`, one class wider than
`RecurrenceGeneratingFunction.lean`, which needs `[CommRing R]` because `recDenom` subtracts.
The width is the point rather than generality for its own sake: Mathlib's `catalanSeries` and
`largeSchroderSeries` live in `PowerSeries ℕ`, which is not a ring, so a `CommRing` layer could
not reach them at all.

**Dated 2026-09-24 (order G-8, J3; round 26):** `not_isSolution_catalan` is stated over
`[CommRing S]`: a commutative semiring is not enough (in the saturating `{0, 1}`, where `1 + 1 = 1`,
every Catalan number is `1` and `u (n + 1) = 1 · u n` holds); `ℕ` is reached through `ℤ`
(`not_isSolution_catalan_nat`).

## What is here

* `IsLocal` and its five closure lemmas.
* `eq_of_eq_C_add_X_mul` — the uniqueness theorem.
* `mk_eq_of_conv`, `mk_eq_of_conv'` — the forward direction, from a convolution recurrence to
  the functional equation.
* `catalanSeries_unique`, `largeSchroderSeries_unique` — uniqueness for **Mathlib's own**
  constants.
* `motzkin`, `motzkin_add_two`, `motzkinSeries_eq`, `motzkin_unique` — the Motzkin numbers,
  shipped as an instance of the layer rather than as a subject of their own.
* **Dated 2026-09-24 (order G-8, J3; round 26):** `not_isSolution_catalan`,
  `not_isSolution_catalan_nat` — the Catalan numbers satisfy no linear recurrence.

## What Mathlib has, and what it does not — measured

Mathlib proves the *forward* direction for two such series and stops there:
`PowerSeries.catalanSeries_sq_mul_X_add_one` (`RingTheory/PowerSeries/Catalan.lean:48`) and
`largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq`
(`RingTheory/PowerSeries/Schroder.lean:95`).  There is **no uniqueness statement**:
`grep -rniE 'fixed.?point|contraction|unique.*satisf' Mathlib/RingTheory/PowerSeries
Mathlib/RingTheory/MvPowerSeries --include=*.lean` returns rc 1, 0 hits.  So
`catalanSeries_unique` is a theorem about a Mathlib object that Mathlib cannot state.

The layer also *absorbs* the second of those proofs.  Mathlib reaches its Schröder functional
equation across `Schroder.lean:51-105` — 55 lines: `coeff_X_mul_largeSchroderSeries` (11 lines,
from 51), `coeff_X_mul_largeSchroderSeriesSeries_sq` (33 lines, from 62), and the theorem itself
(11 lines, from 95).  Re-derived from `mk_eq_of_conv'` it is **15 lines**, shipped below as an
`example` so the claim is checked rather than asserted, and neither supporting lemma is needed.
Those two are ordinary `lemma`s, not private helpers — the file contains no `private` at all —
so they remain part of Mathlib's public API; what the count measures is the length of the
argument, not deletions from Mathlib.

**Dated 2026-09-24 (order G-8, J3; round 26):** at Mathlib v4.34.0 these citations have moved:
`catalanSeries_sq_mul_X_add_one` is at `Catalan.lean:47` (cited as `:48` twice in this file) and
the Schröder theorem at `Schroder.lean:94` (cited as `:95` twice); the argument spans
`Schroder.lean:51-104`, 54 lines — `coeff_X_mul_largeSchroderSeries` 10 lines from 51,
`coeff_X_mul_largeSchroderSeriesSeries_sq` 33 lines from 61, the theorem 11 lines from 94 — so the
re-derivation below replaces 54 lines with 15, not 55 (stated twice in this file); the 15
re-measured, unchanged.

**The Motzkin numbers are absent from Mathlib, but the name is not.**
`grep -rni 'Motzkin' Mathlib --include=*.lean` returns 17 lines, all Fourier–Motzkin elimination
in the `linarith` oracle or Th. Motzkin cited as an author; residual 0 after filtering.  However
`Counterexamples/Motzkin.lean` **does exist** in the same vendored tree — it is
`motzkin_polynomial_nonneg`, the nonnegative-but-not-a-sum-of-squares *polynomial*, a different
object from the Motzkin *numbers* defined here.  Named explicitly so this module's absence claim
is not read as contradicted by a file of that name.

## The `set_option`, and why it is measured

`set_option backward.isDefEq.respectTransparency false` is **necessary**, not defensive.
Measured on this file: deleting that single line and changing nothing else gives rc 1 with
**6 error sites** — two `simp made no progress`, one `Type mismatch: After simplification`, and
three `unsolved goals`, spread across `mk_eq_of_conv`, `mk_eq_of_conv'`, the two Mathlib
re-derivations and `motzkinSeries_eq`.  `RecurrenceGeneratingFunction.lean` records the same
instance-diamond finding for `[CommRing R]`; this file extends the observation to
`[CommSemiring R]`.

Superseded 2026-09-23: builds without the option at v4.34.0 (round 19).
-/

open PowerSeries Finset

namespace ClassicalLean

variable {R : Type*} [CommSemiring R]

/-- A map on power series is **local** when `coeff n (q a)` depends only on the coefficients of
`a` up to index `n`.

The bound is `m ≤ n`, not `m < n`: `coeff n (a ^ 2)` genuinely depends on `coeff n a`. -/
def IsLocal (q : PowerSeries R → PowerSeries R) : Prop :=
  ∀ (n : ℕ) (a b : PowerSeries R), (∀ m ≤ n, coeff m a = coeff m b) → coeff n (q a) = coeff n (q b)

set_option linter.defProp false in
/-- Locality of the identity map, as a **proof term rather than a theorem**.

`tools/VacuityGate.lean` rejects it as a named theorem, and is right to: unfolded, the
statement is `(∀ m ≤ n, coeff m a = coeff m b) → coeff n a = coeff n b`, an instance of its own
universally quantified hypothesis, which is the gate's third clause.  It asserts nothing.  It is
still the base case every composite locality proof needs, so it is kept as a `def` — the term is
what is wanted, and no theorem claims anything on its behalf.

`isLocal_const` below is in the same position and is deliberately left a `theorem`, which is an
asymmetry worth naming rather than hiding: its proof is `fun _ _ _ _ => rfl`, so its `IsLocal`
hypothesis is unused and its conclusion is `x = x`.  It passes the gate only because `x = x` is
not one of the gate's four clauses — a blind spot, not a verdict.  Whoever revisits this should
treat the two together, in either direction.

Lean v4.32 turned its core `linter.defProp` on by default; it flags a `def` whose type is a
proposition — exactly this declaration, for exactly the reason above.  It is silenced for this
declaration only. -/
def isLocalId : IsLocal (fun f : PowerSeries R => f) := fun n _ _ h => h n le_rfl

theorem isLocal_const (g : PowerSeries R) : IsLocal (fun _ : PowerSeries R => g) :=
  fun _ _ _ _ => rfl

theorem isLocal_add {q₁ q₂ : PowerSeries R → PowerSeries R} (h₁ : IsLocal q₁) (h₂ : IsLocal q₂) :
    IsLocal (fun f => q₁ f + q₂ f) := by
  intro n a b h; simp only [map_add, h₁ n a b h, h₂ n a b h]

theorem isLocal_mul {q₁ q₂ : PowerSeries R → PowerSeries R} (h₁ : IsLocal q₁) (h₂ : IsLocal q₂) :
    IsLocal (fun f => q₁ f * q₂ f) := by
  intro n a b h
  simp only [coeff_mul]
  refine Finset.sum_congr rfl ?_
  rintro ⟨i, j⟩ hij
  have hij' : i + j = n := Finset.mem_antidiagonal.mp hij
  have hi : i ≤ n := by omega
  have hj : j ≤ n := by omega
  dsimp only
  rw [h₁ i a b (fun m hm => h m (hm.trans hi)), h₂ j a b (fun m hm => h m (hm.trans hj))]

theorem isLocal_pow {q : PowerSeries R → PowerSeries R} (h : IsLocal q) :
    ∀ k, IsLocal (fun f => q f ^ k)
  | 0 => by simpa using isLocal_const (R := R) 1
  | (k + 1) => by
      have := isLocal_mul (isLocal_pow h k) h
      simpa [pow_succ] using this

/-- **Uniqueness.** For a local `q`, a power series is determined by `f = C c + X * q f`.

The proof is a strong induction on the coefficient index.  At `0` both sides are `c`.  At
`n + 1`, `coeff_succ_X_mul` drops the index to `n`, and locality of `q` means that coefficient
depends only on coefficients strictly below `n + 1`, which the induction hypothesis has already
matched.  The `X *` is doing the work: without it there is no descent and the statement is
false. -/
theorem eq_of_eq_C_add_X_mul {q : PowerSeries R → PowerSeries R} (hq : IsLocal q) (c : R)
    (f g : PowerSeries R) (hf : f = C c + X * q f) (hg : g = C c + X * q g) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [hf, hg]; simp
    | (m + 1) =>
      rw [hf, hg]
      simp only [map_add, coeff_C, coeff_succ_X_mul]
      congr 1
      exact hq m _ _ (fun j hj => ih j (Nat.lt_succ_of_le hj))

/-- **Forward.** A convolution recurrence gives the quadratic functional equation. -/
theorem mk_eq_of_conv (u : ℕ → R)
    (h : ∀ n, u (n + 1) = ∑ ij ∈ antidiagonal n, u ij.1 * u ij.2) :
    mk u = C (u 0) + X * (mk u) ^ 2 := by
  ext n
  match n with
  | 0 => simp
  | (m + 1) =>
    rw [map_add, coeff_C, coeff_succ_X_mul, coeff_mk, h m, sq]
    simp_rw [coeff_mul, coeff_mk]
    simp

/-- **Forward, general quadratic**: `u (n+1) = a * u n + b * (convolution)`. -/
theorem mk_eq_of_conv' (u : ℕ → R) (a b : R)
    (h : ∀ n, u (n + 1) = a * u n + b * ∑ ij ∈ antidiagonal n, u ij.1 * u ij.2) :
    mk u = C (u 0) + X * (C a * mk u + C b * (mk u) ^ 2) := by
  ext n
  match n with
  | 0 => simp
  | (m + 1) =>
    rw [map_add, coeff_C, coeff_succ_X_mul, coeff_mk, h m, map_add, coeff_C_mul, coeff_C_mul,
      coeff_mk, sq]
    simp_rw [coeff_mul, coeff_mk]
    simp

/-- The general quadratic operator is local, from the closure lemmas alone. -/
theorem isLocal_quadratic (a b : R) :
    IsLocal (fun f : PowerSeries R => C a * f + C b * f ^ 2) :=
  isLocal_add (isLocal_mul (isLocal_const _) isLocalId)
    (isLocal_mul (isLocal_const _) (isLocal_pow isLocalId 2))

/-! ### Uniqueness for Mathlib's own series -/

/-- **Mathlib's Catalan series is the unique solution of its own functional equation.**

Mathlib proves the forward direction (`catalanSeries_sq_mul_X_add_one`) and has no uniqueness
lemma anywhere in `RingTheory/PowerSeries`. -/
theorem catalanSeries_unique (f : PowerSeries ℕ) (hf : f = 1 + X * f ^ 2) :
    f = catalanSeries := by
  have h := mk_eq_of_conv catalan catalan_succ'
  rw [show PowerSeries.mk catalan = catalanSeries from rfl, catalan_zero, map_one] at h
  exact eq_of_eq_C_add_X_mul (isLocal_pow isLocalId 2) 1 f catalanSeries
    (by rw [map_one]; exact hf) (by rw [map_one]; exact h)

/-- The same for Mathlib's large Schröder series. -/
theorem largeSchroderSeries_unique (f : PowerSeries ℕ)
    (hf : f = 1 + X * (f + f ^ 2)) : f = largeSchroderSeries := by
  have h : ∀ n, Nat.largeSchroder (n + 1)
      = 1 * Nat.largeSchroder n + 1 * ∑ ij ∈ antidiagonal n,
          Nat.largeSchroder ij.1 * Nat.largeSchroder ij.2 := by
    intro n
    rw [Nat.largeSchroder_succ, one_mul, one_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    congr 1
    exact Finset.sum_congr (by ext i; simp) fun _ _ => rfl
  have h2 := mk_eq_of_conv' Nat.largeSchroder 1 1 h
  rw [show PowerSeries.mk Nat.largeSchroder = largeSchroderSeries from rfl,
    Nat.largeSchroder_zero, map_one] at h2
  refine eq_of_eq_C_add_X_mul (isLocal_add isLocalId (isLocal_pow isLocalId 2)) 1 f _
    (by rw [map_one]; exact hf) (by rw [map_one]; simpa using h2)

/-! ### The two Mathlib proofs, re-derived

Both are `example`s: the shipped Mathlib proofs stay where they are, and these record that the
layer reaches them.  The Schröder one replaces 55 lines with 15, of which 8 are only the
`∑ i ≤ n` to `antidiagonal` bridge. -/

/-- `PowerSeries.catalanSeries_sq_mul_X_add_one` (`Catalan.lean:48`), re-derived. -/
example : catalanSeries ^ 2 * X + 1 = catalanSeries := by
  have h := mk_eq_of_conv catalan catalan_succ'
  rw [show PowerSeries.mk catalan = catalanSeries from rfl, catalan_zero, map_one] at h
  conv_rhs => rw [h]
  ring

/-- Mathlib's large Schröder functional equation (`Schroder.lean:95`), re-derived. -/
example : largeSchroderSeries
    = 1 + X * largeSchroderSeries + X * largeSchroderSeries ^ 2 := by
  have h : ∀ n, Nat.largeSchroder (n + 1)
      = 1 * Nat.largeSchroder n + 1 * ∑ ij ∈ antidiagonal n,
          Nat.largeSchroder ij.1 * Nat.largeSchroder ij.2 := by
    intro n
    rw [Nat.largeSchroder_succ, one_mul, one_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    congr 1
    exact Finset.sum_congr (by ext i; simp) fun _ _ => rfl
  have h2 := mk_eq_of_conv' Nat.largeSchroder 1 1 h
  rw [show PowerSeries.mk Nat.largeSchroder = largeSchroderSeries from rfl,
    Nat.largeSchroder_zero, map_one] at h2
  conv_lhs => rw [h2]
  ring

/-! ### The Catalan numbers satisfy no linear recurrence (dated 2026-09-24, order G-8, J3; round 26)

The mathematical counterpart of this module's remark that a convolution "has no representation" as
a `LinearRecurrence`: no recurrence of any order, over any nontrivial commutative ring, has the
Catalan numbers as a solution. -/

section CatalanRecurrence

/-- In a domain, the Catalan numbers satisfy no linear recurrence. With `Q` the reversed
characteristic polynomial (`recDenom E`, as a polynomial) and `C` the Catalan series, a solution
gives `Q C = P` with `P` a polynomial (`recDenom_mul_mk_eq_coe_trunc`), and `C = 1 + X C²`
(`PowerSeries.catalanSeries_sq_mul_X_add_one`) gives `Q P = Q² + X P²`; the degrees `2 deg Q` and
`2 deg P + 1` differ in parity, so the right side has the larger of the two, which exceeds
`deg Q + deg P`. -/
private theorem not_isSolution_catalan_of_isDomain {K : Type*} [CommRing K] [IsDomain K]
    (E : LinearRecurrence K) : ¬ E.IsSolution (fun n => (catalan n : K)) := by
  intro h
  set Cs : K⟦X⟧ := PowerSeries.mk (fun n => (catalan n : K)) with hCs
  have hCeq : Cs = 1 + PowerSeries.X * Cs ^ 2 := by
    have h1 := congrArg (PowerSeries.map (Nat.castRingHom K)) catalanSeries_sq_mul_X_add_one
    have hm : PowerSeries.map (Nat.castRingHom K) catalanSeries = Cs := by
      ext n
      simp [hCs, catalanSeries_coeff]
    rw [map_add, map_mul, map_pow, PowerSeries.map_X, map_one, hm] at h1
    linear_combination (-1 : K⟦X⟧) * h1
  set Q : Polynomial K := 1 - ∑ j : Fin E.order,
    Polynomial.C (E.coeffs j.rev) * Polynomial.X ^ ((j : ℕ) + 1) with hQ
  have hQc : (Q : K⟦X⟧) = recDenom E := by
    rw [hQ, Polynomial.coe_sub, Polynomial.coe_one, recDenom,
      ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    simp [Polynomial.coe_C, Polynomial.coe_X]
  have hQ0 : Q.coeff 0 = 1 := by
    simp [hQ]
  have hQne : Q ≠ 0 := fun h0 => by simp [h0] at hQ0
  set P : Polynomial K := trunc E.order (recDenom E * Cs) with hP
  have hQP : (Q : K⟦X⟧) * Cs = (P : K⟦X⟧) := by
    rw [hQc]
    exact recDenom_mul_mk_eq_coe_trunc E _ h
  have hkey : Q * P = Q ^ 2 + Polynomial.X * P ^ 2 := by
    apply Polynomial.coe_injective
    simp only [Polynomial.coe_mul, Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X]
    rw [← hQP]
    conv_lhs => rw [hCeq]
    ring
  have hPne : P ≠ 0 := by
    intro hP0
    rw [hP0, mul_zero, zero_pow two_ne_zero, mul_zero, add_zero] at hkey
    exact hQne (pow_eq_zero_iff two_ne_zero |>.mp hkey.symm)
  have h1 : (Q * P).natDegree = Q.natDegree + P.natDegree := Polynomial.natDegree_mul hQne hPne
  have h2 : (Q ^ 2).natDegree = 2 * Q.natDegree := Polynomial.natDegree_pow Q 2
  have h3 : (Polynomial.X * P ^ 2).natDegree = 2 * P.natDegree + 1 := by
    rw [Polynomial.natDegree_X_mul (pow_ne_zero 2 hPne), Polynomial.natDegree_pow]
  rcases lt_or_ge P.natDegree Q.natDegree with hde | hde
  · have h4 : (Q ^ 2 + Polynomial.X * P ^ 2).natDegree = 2 * Q.natDegree := by
      rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt (by rw [h2, h3]; omega), h2]
    rw [← hkey, h1] at h4
    omega
  · have h4 : (Q ^ 2 + Polynomial.X * P ^ 2).natDegree = 2 * P.natDegree + 1 := by
      rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt (by rw [h2, h3]; omega), h3]
    rw [← hkey, h1] at h4
    omega

/-- **The Catalan numbers satisfy no linear recurrence**, over any nontrivial commutative ring:
for every `E : LinearRecurrence S`, `¬ E.IsSolution (fun n => (catalan n : S))`. From the domain
case at `S ⧸ m` for a maximal ideal `m` (`Ideal.exists_maximal`), the recurrence mapped
coefficientwise. `Nontrivial` is needed (in the trivial ring every recurrence holds). A commutative
semiring is not enough: in the saturating `{0, 1}` (`1 + 1 = 1`; Mathlib's `WithZero Unit`) every
Catalan number is `1` and `u (n + 1) = 1 · u n` holds (order G-8 J1); `ℕ` is covered, through `ℤ`,
by `not_isSolution_catalan_nat`. Route: claude-ai's, for order G-8 (the domain variant and the
parity form of the degree comparison derived here, order G-8's routes critic). -/
theorem not_isSolution_catalan {S : Type*} [CommRing S] [Nontrivial S]
    (E : LinearRecurrence S) : ¬ E.IsSolution (fun n => (catalan n : S)) := by
  intro h
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  have : m.IsPrime := hm.isPrime
  let E' : LinearRecurrence (S ⧸ m) := ⟨E.order, fun i => Ideal.Quotient.mk m (E.coeffs i)⟩
  apply not_isSolution_catalan_of_isDomain E'
  intro n
  have h' := congrArg (Ideal.Quotient.mk m) (h n)
  simpa [E', map_sum, map_mul, map_natCast] using h'

/-- The Catalan numbers satisfy no linear recurrence with natural-number coefficients: the case
`ℕ`, where Mathlib's `catalan` and `catalanSeries` live, obtained from `not_isSolution_catalan`
over `ℤ`. -/
theorem not_isSolution_catalan_nat (E : LinearRecurrence ℕ) : ¬ E.IsSolution catalan := by
  intro h
  let E' : LinearRecurrence ℤ := ⟨E.order, fun i => (E.coeffs i : ℤ)⟩
  apply not_isSolution_catalan E'
  intro n
  have h' := congrArg (Nat.cast : ℕ → ℤ) (h n)
  push_cast at h'
  exact h'

end CatalanRecurrence

/-! ### The Motzkin numbers, as an instance

Shipped here rather than as a module of their own.  A Motzkin module would have defined the
sequence and proved its own recurrence back, which is the shape this project does not ship; as
an instance of the layer it costs a definition and three short proofs, and comes with a
uniqueness statement no separate module would have had. -/

/-- The Motzkin numbers `1, 1, 2, 4, 9, 21, 51, 127, 323, …` — the number of lattice paths from
`(0,0)` to `(n,0)` with up, down and level steps that never go below the axis. -/
def motzkin : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => motzkin (n + 1) + ∑ i : Fin (n + 1), motzkin i * motzkin (n - i)

/-- The defining recurrence, restated over `antidiagonal`. -/
theorem motzkin_add_two (n : ℕ) : motzkin (n + 2)
    = motzkin (n + 1) + ∑ ij ∈ antidiagonal n, motzkin ij.1 * motzkin ij.2 := by
  rw [motzkin, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range]

example : (List.range 9).map motzkin = [1, 1, 2, 4, 9, 21, 51, 127, 323] := by
  decide +kernel

/-- Motzkin's operator `q f = f + X * f ^ 2` is local, from the closure lemmas alone. -/
theorem isLocal_motzkinOp :
    IsLocal (fun f : PowerSeries R => f + X * f ^ 2) :=
  isLocal_add isLocalId (isLocal_mul (isLocal_const X) (isLocal_pow isLocalId 2))

/-- The Motzkin functional equation `M = 1 + X * (M + X * M ^ 2)`. -/
theorem motzkinSeries_eq :
    PowerSeries.mk (fun n => (motzkin n : R))
      = C 1 + X * (PowerSeries.mk (fun n => (motzkin n : R))
          + X * (PowerSeries.mk (fun n => (motzkin n : R))) ^ 2) := by
  ext n
  match n with
  | 0 => simp [motzkin]
  | 1 => simp [motzkin, coeff_succ_X_mul]
  | (k + 2) =>
    rw [map_add, coeff_C, coeff_succ_X_mul, coeff_mk, map_add, coeff_mk, coeff_succ_X_mul, sq]
    simp_rw [coeff_mul, coeff_mk]
    rw [motzkin_add_two]
    push_cast
    simp

/-- **The Motzkin series is the unique solution of its functional equation** — the payoff of
shipping Motzkin as an instance rather than as a subject. -/
theorem motzkin_unique (f : PowerSeries R) (hf : f = C 1 + X * (f + X * f ^ 2)) :
    f = PowerSeries.mk (fun n => (motzkin n : R)) :=
  eq_of_eq_C_add_X_mul isLocal_motzkinOp 1 f _ hf motzkinSeries_eq

end ClassicalLean
