/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.LinearRecurrence
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Fin.Basic

/-!
# A linear recurrence is a rational generating function

For a Mathlib `LinearRecurrence` `E` of order `d` with coefficients `a : Fin d → R`, a sequence
`u` solves `E` exactly when the formal power series `∑ uₙ Xⁿ`, multiplied by the **reversed
characteristic polynomial**

    D_E = 1 - ∑_{i < d} a_i X^{d - i},

has vanishing coefficients from index `d` on — that is, when `D_E · ∑ uₙ Xⁿ` is a polynomial of
degree less than `d`.  This is `isSolution_iff_coeff_recDenom_mul_mk`, and it is an *iff*: the
recurrence and the rationality of the generating function are the same statement, read at
coefficient `n + d`.

The one computation behind it is `coeff_recDenom_mul_mk`:

    coeff (n + d) (D_E · ∑ uₖ Xᵏ)  =  u (n + d) - ∑_{i<d} a_i · u (n + i)

whose right-hand side is literally the residual of Mathlib's `LinearRecurrence.IsSolution` at
`n`.  Everything else — the `iff`, the unit, the quotient form — is bookkeeping on top of it.

## Main definitions and results

* `ClassicalLean.recDenom E` — the reversed characteristic polynomial of `E`, as a power series.
* `coeff_recDenom_mul_mk` — the coefficient identity above.
* `isSolution_iff_coeff_recDenom_mul_mk` — solving the recurrence ⟺ the product is a polynomial
  of degree `< E.order`.
* `constantCoeff_recDenom`, `isUnit_recDenom` — the denominator is a unit of `R⟦X⟧`, so the
  quotient `numerator / D_E` exists over any commutative ring, with no field and no convergence.
* `recDenom_mul_mk_eq_coe_trunc`, `exists_poly_mk_eq` — the quotient form itself: a solution's
  generating function is `p / D_E` with `p` a polynomial whose coefficients vanish from
  `E.order` on.

## What Mathlib has, and what it does not

Re-measured in `.lake/packages/mathlib` before this file was written:

* `grep -rn 'generating function\|generatingFunction' Mathlib --include=*.lean`, minus the
  probability hits (`mgf`, `cgf`, moment- and cumulant-generating functions), leaves 21 lines:
  the *exponential* generating function of the Bernoulli numbers
  (`NumberTheory/Bernoulli.lean`, `BernoulliPolynomials.lean`) and two *specific* ordinary ones,
  `RingTheory/PowerSeries/Catalan.lean` and `.../Schroder.lean`.  Both of those prove only a
  functional equation; `Catalan.lean` line 25 carries a `TODO: Find and prove the closed formula
  for the Catalan generating function`.
* `LinearRecurrence` occurs in exactly four files — `Algebra/LinearRecurrence.lean`,
  `NumberTheory/Real/GoldenRatio.lean`, `RingTheory/Polynomial/Chebyshev.lean`,
  `RingTheory/Polynomial/Dickson.lean` — and `grep -c 'PowerSeries'` is **0** in every one.

So Mathlib has the recurrences and the power series and does not connect them.  That is the gap
this file fills, and it is `ROADMAP.md` §2.3.

## Why this file sets `backward.isDefEq.respectTransparency false`

**Measured.**  Without the option, `ring` closes no goal in `R⟦X⟧` — not even `X * X = X ^ 2` —
and `rw [sub_mul]` reports that it cannot find `(?a - ?b) * ?c` in `(1 - f) * (1 - g)`.  With
the option, all of those close.  Printing a goal under `pp.explicit` and `pp.fullNames` shows
`1` elaborated through `MvPowerSeries.instOne` and `*` through `MvPowerSeries.instMul`, while
`-` goes through `PowerSeries.instAddGroup` and `0` through `PowerSeries.instZero`.  Mathlib
declares both families: `instance [AddGroup R] : AddGroup R⟦X⟧` and
`instance [CommRing R] : CommRing R⟦X⟧`, each `by dsimp only [PowerSeries]; infer_instance`
(`RingTheory/PowerSeries/Basic.lean`, lines 87 and 111).  Mathlib sets the same option
immediately before `PowerSeries.catalanSeries_sq_mul_X_add_one`
(`RingTheory/PowerSeries/Catalan.lean`), and `ClassicalLean/Geometry/Helix.lean` already sets it
for matrix goals.

**Inferred, not measured.**  That a distributivity lemma stated for one of those instance
families therefore fails to match a goal built from the other, and that the option restores the
unfolding which makes them agree.  The practical rule does not depend on the inference: in
`R⟦X⟧`, `ring`, `add_mul` and `sub_mul` need the option; `abel`, `sub_eq_add_neg` and
`coeff`-level `simp` do not.

Superseded 2026-09-23: builds without the option at v4.34.0 (round 19).
-/

namespace ClassicalLean

open PowerSeries

variable {R : Type*} [CommRing R] (E : LinearRecurrence R)

/-- The **reversed characteristic polynomial** of a linear recurrence, as a power series:
`1 - ∑_{i<d} a_i X^{d-i}` for `d = E.order` and `a = E.coeffs`.

Indexed by `Fin.rev` so that the exponent is `j + 1` and no truncated subtraction appears: as
`j` runs over `Fin d`, `j.rev` runs over the same set backwards, and `d - j.rev = j + 1`. -/
noncomputable def recDenom : R⟦X⟧ :=
  1 - ∑ j : Fin E.order, C (E.coeffs j.rev) * X ^ ((j : ℕ) + 1)

/-- **The coefficient identity.** At index `n + E.order`, the product of the reversed
characteristic polynomial with `∑ uₖ Xᵏ` is exactly the residual of the recurrence at `n`.

Every statement in this file is a reading of this one equation. -/
theorem coeff_recDenom_mul_mk (u : ℕ → R) (n : ℕ) :
    coeff (n + E.order) (recDenom E * mk u)
      = u (n + E.order) - ∑ i : Fin E.order, E.coeffs i * u (n + i) := by
  have key : ∀ j : Fin E.order,
      coeff (n + E.order) (C (E.coeffs j.rev) * X ^ ((j : ℕ) + 1) * mk u)
        = E.coeffs j.rev * u (n + (j.rev : ℕ)) := by
    intro j
    have hrev := Fin.val_rev j
    have hj := j.isLt
    have hidx : n + E.order = (n + (j.rev : ℕ)) + ((j : ℕ) + 1) := by omega
    rw [mul_assoc, hidx, coeff_C_mul, coeff_X_pow_mul, coeff_mk]
  rw [recDenom, sub_mul, one_mul, Finset.sum_mul, map_sub, coeff_mk, map_sum,
    Finset.sum_congr rfl (fun j _ => key j)]
  congr 1
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun j => rfl)

/-- **A sequence solves the recurrence exactly when its generating function is rational with
denominator the reversed characteristic polynomial.**

The right-hand side says `recDenom E * mk u` has no coefficient at or above `E.order`, i.e. it
is a polynomial of degree `< E.order` — the numerator.  The two initial-value data and the
recurrence are thus repackaged as: numerator determined by the first `order` terms, denominator
determined by the coefficients. -/
theorem isSolution_iff_coeff_recDenom_mul_mk (u : ℕ → R) :
    E.IsSolution u ↔ ∀ n, coeff (n + E.order) (recDenom E * mk u) = 0 := by
  constructor
  · intro h n
    rw [coeff_recDenom_mul_mk, h n, sub_self]
  · intro h n
    have hn := h n
    rw [coeff_recDenom_mul_mk] at hn
    exact sub_eq_zero.mp hn

/-- The reversed characteristic polynomial has constant coefficient `1`: every term of the sum
carries a positive power of `X`.  True for `E.order = 0` too, where the sum is empty. -/
@[simp] theorem constantCoeff_recDenom : constantCoeff (recDenom E) = 1 := by
  rw [recDenom, map_sub, map_one, map_sum]
  simp

/-- The reversed characteristic polynomial is a **unit** of `R⟦X⟧`.

This is what makes "the generating function is `numerator / denominator`" meaningful over an
arbitrary commutative ring: no field, no radius of convergence, no nonvanishing hypothesis —
only that the constant term is `1`, which it is by construction. -/
theorem isUnit_recDenom : IsUnit (recDenom E) :=
  ⟨⟨recDenom E, invOfUnit (recDenom E) 1,
    mul_invOfUnit _ 1 (by simp), invOfUnit_mul _ 1 (by simp)⟩, rfl⟩

/-- A rearrangement, with **no hypothesis on `u`**: for any `u` whatever,
`x = (D * x) * D⁻¹` because `D` is a unit.  It carries no information about solutions of `E` and
is `private` for that reason; it is the last step of `exists_poly_mk_eq`, where the first factor
has been shown to be a polynomial. -/
private theorem mk_eq_mul_invOfUnit_recDenom (u : ℕ → R) :
    mk u = (recDenom E * mk u) * invOfUnit (recDenom E) 1 := by
  have hinv : recDenom E * invOfUnit (recDenom E) 1 = 1 := mul_invOfUnit _ 1 (by simp)
  calc mk u = 1 * mk u := (one_mul _).symm
    _ = recDenom E * invOfUnit (recDenom E) 1 * mk u := by rw [hinv]
    _ = recDenom E * mk u * invOfUnit (recDenom E) 1 := mul_right_comm _ _ _

/-- For a solution, `recDenom E * ∑ uₙ Xⁿ` **is** its own truncation at `E.order` — that is, it
is a polynomial of degree less than `E.order`.  This is `isSolution_iff_coeff_recDenom_mul_mk`
turned from a statement about coefficients into a statement about the object. -/
theorem recDenom_mul_mk_eq_coe_trunc (u : ℕ → R) (h : E.IsSolution u) :
    recDenom E * mk u = ((trunc E.order (recDenom E * mk u) : Polynomial R) : R⟦X⟧) := by
  ext n
  rw [Polynomial.coeff_coe, coeff_trunc]
  split_ifs with hn
  · rfl
  · push Not at hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [add_comm]
    exact (isSolution_iff_coeff_recDenom_mul_mk E u).mp h k

/-- **The generating function of a solution is rational, with denominator `recDenom E` and a
numerator of degree less than `E.order`.**

This is the statement `ROADMAP.md` §2.3 asked for, and unlike the rearrangement above it has
real content: the numerator is exhibited as a *polynomial*, and "degree `< E.order`" is stated
as the vanishing of every coefficient from `E.order` on, so there is no `natDegree`/`⊥` edge
case at `E.order = 0`. -/
theorem exists_poly_mk_eq (u : ℕ → R) (h : E.IsSolution u) :
    ∃ p : Polynomial R, (∀ m, E.order ≤ m → p.coeff m = 0) ∧
      mk u = (p : R⟦X⟧) * invOfUnit (recDenom E) 1 := by
  refine ⟨trunc E.order (recDenom E * mk u), ?_, ?_⟩
  · intro m hm
    rw [coeff_trunc, ite_eq_right (Nat.not_lt.mpr hm)]
  · rw [← recDenom_mul_mk_eq_coe_trunc E u h]
    exact mk_eq_mul_invOfUnit_recDenom E u

end ClassicalLean
