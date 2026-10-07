/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import ClassicalLean.Combinatorics.RecurrenceGeneratingFunction
import ClassicalLean.NumberTheory.LucasSequence
import ClassicalLean.NumberTheory.LucasSequenceCases

/-!
# The generating function of a Lucas sequence

The two sequences of `ClassicalLean/NumberTheory/LucasSequence.lean` have rational generating
functions with the same denominator, the **reversed characteristic polynomial**
`1 - P X + Q X²` of `t² - P t + Q`:

    ∑ Uₙ Xⁿ = X / (1 - P X + Q X²)        ∑ Vₙ Xⁿ = (2 - P X) / (1 - P X + Q X²)

Stated here without division, as identities in `R⟦X⟧` for an arbitrary commutative ring:

* `lucasU_gf` : `(1 - P X + Q X²) * mk U = X`
* `lucasV_gf` : `(1 - P X + Q X²) * mk V = 2 - P X`

The division-free form is the useful one.  It needs no field, no invertibility hypothesis and no
convergence, and it is exactly equivalent to the recurrence: multiplying a power series by
`1 - P X + Q X²` and reading coefficient `n + 2` *is* the recurrence at `n`.  The quotient form
follows, since the denominator has constant coefficient `1` and is therefore a unit
(`isUnit_lucasDenom`, `mk_lucasU_eq`).

## Why this is a method and not a fact

A generating function turns "prove this identity by induction" into "compute with a rational
function".  The seven sequences identified in `LucasSequenceCases.lean` get their generating
functions here in one line each, from one theorem — `Nat.fib`, `lucas`, `pellNumber`,
`pellHalfCompanion`, `jacobsthal`, `jacobsthalCompanion` and `mersenne`.  None of them needed a
separate induction.

## The denominator factors exactly when the roots are named

`lucasDenom_of_roots : 1 - (α + β) X + αβ X² = (1 - α X)(1 - β X)`.  This is the generating-
function shadow of `lucasU_of_roots` and `lucasV_of_roots`: the partial-fraction decomposition
of `X / ((1 - αX)(1 - βX))` is what produces `(αⁿ - βⁿ)/(α - β)`, and the factorisation is the
step that makes it available.  For the Mersenne parameters `(P, Q) = (3, 2)` the factorisation
is over `ℤ` — `1 - 3X + 2X² = (1 - X)(1 - 2X)` — which is the split discriminant `D = 1` of
`ROADMAP.md` §1.1 seen from the generating-function side.

## Why this file sets `backward.isDefEq.respectTransparency false`

**Measured.**  Without the option, `ring` closes no goal in `R⟦X⟧` — not even
`X * X = X ^ 2` — and `rw [sub_mul]` reports it cannot find `(?a - ?b) * ?c` in `(1 - f) * g`.
With it, all of those close.  Under `pp.explicit` with `pp.fullNames`, `1` and `*` elaborate
through `MvPowerSeries.instOne` and `MvPowerSeries.instMul`, while `-` goes through
`PowerSeries.instAddGroup` and `0` through `PowerSeries.instZero`; Mathlib declares both
families, each `by dsimp only [PowerSeries]; infer_instance`
(`RingTheory/PowerSeries/Basic.lean` lines 87 and 111).  `abel`, `sub_eq_add_neg` and
`coeff`-level `simp` work without the option.

**Inferred.**  That a lemma stated for one instance family therefore fails to match a goal built
from the other.  The rule is what matters and does not depend on the inference.

This is not a workaround invented here.  Mathlib sets the same option immediately before
`PowerSeries.catalanSeries_sq_mul_X_add_one` (`RingTheory/PowerSeries/Catalan.lean`), and
`ClassicalLean/Geometry/Helix.lean` already sets it for matrix goals.
`ClassicalLean/Combinatorics/RecurrenceGeneratingFunction.lean` records the same finding.

Superseded 2026-09-23: builds without the option at v4.34.0 (round 19).

## Main results

* `lucasU_gf`, `lucasV_gf` — the two generating functions.
* `lucasDenom_of_roots` — the factorisation of the denominator.
* `constantCoeff_lucasDenom`, `isUnit_lucasDenom`, `mk_lucasU_eq`, `mk_lucasV_eq` — the
  quotient form, through Mathlib's `PowerSeries.invOfUnit`.
* `fib_gf`, `lucas_gf`, `pellNumber_gf`, `pellHalfCompanion_gf`, `jacobsthal_gf`,
  `jacobsthalCompanion_gf`, `mersenne_gf` — the seven instances.
-/

namespace ClassicalLean

open PowerSeries

variable {R : Type*} [CommRing R] (P Q : R)

/-! ### The denominator -/

/-- The denominator `1 - P X + Q X²` of both generating functions: the reversal of the
characteristic polynomial `t² - P t + Q`. -/
noncomputable def lucasDenom : R⟦X⟧ := 1 - C P * X + C Q * X ^ 2

/-- Expanding the product against a `mk`, in the shape the coefficient computations use. -/
private theorem lucasDenom_mul_mk (u : ℕ → R) :
    lucasDenom P Q * mk u = mk u - C P * (X * mk u) + C Q * (X ^ 2 * mk u) := by
  rw [lucasDenom]
  ring

/-- The coefficient of `lucasDenom P Q * mk u` at index `n + 2` is the residual of the
recurrence at `n`.  Every statement below is this lemma plus two initial values. -/
private theorem coeff_lucasDenom_mul_mk_add_two (u : ℕ → R) (n : ℕ) :
    coeff (n + 2) (lucasDenom P Q * mk u) = u (n + 2) - P * u (n + 1) + Q * u n := by
  rw [lucasDenom_mul_mk]
  have h1 : coeff (n + 2) (X * mk u) = u (n + 1) := by
    rw [show n + 2 = (n + 1) + 1 from rfl, coeff_succ_X_mul, coeff_mk]
  have h2 : coeff (n + 2) (X ^ 2 * mk u) = u n := by
    rw [coeff_X_pow_mul, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mk, h1, h2]

/-! ### The master theorem: any solution of the recurrence -/

/-- **The generating function of any solution of `u (n+2) = P u (n+1) - Q u n`.**

    (1 - P X + Q X²) · ∑ uₙ Xⁿ  =  u₀ + (u₁ - P u₀) X

The denominator depends only on the recurrence and the numerator only on the two initial
values, which is the whole content: a linear recurrence *is* a rational generating function
whose denominator is the reversed characteristic polynomial.

Everything else in this file is this theorem at particular initial values.  Nothing below needs
an induction of its own — that is what makes a generating function a method rather than a
fact. -/
theorem lucasDenom_mul_mk_of_rec (u : ℕ → R)
    (h : ∀ n, u (n + 2) = P * u (n + 1) - Q * u n) :
    lucasDenom P Q * mk u = C (u 0) + C (u 1 - P * u 0) * X := by
  ext n
  match n with
  | 0 =>
    rw [lucasDenom_mul_mk]
    simp
  | 1 =>
    rw [lucasDenom_mul_mk]
    have h1 : coeff 1 (X * mk u) = u 0 := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_mk]
    have h2 : coeff 1 (X ^ 2 * mk u) = 0 := by
      rw [coeff_X_pow_mul']
      simp
    simp [h1, h2]
  | (n + 2) =>
    rw [coeff_lucasDenom_mul_mk_add_two, h n]
    simp

/-! ### The two canonical solutions -/

/-- **The generating function of `U`**: `(1 - P X + Q X²) * ∑ Uₙ Xⁿ = X`.

`lucasDenom_mul_mk_of_rec` at `u₀ = 0`, `u₁ = 1`. -/
theorem lucasU_gf : lucasDenom P Q * mk (lucasU P Q) = X := by
  rw [lucasDenom_mul_mk_of_rec P Q _ (lucasU_add_two P Q)]
  simp

/-- **The generating function of `V`**: `(1 - P X + Q X²) * ∑ Vₙ Xⁿ = 2 - P X`.

`lucasDenom_mul_mk_of_rec` at `u₀ = 2`, `u₁ = P`; the numerator is `2 + (P - 2P) X`.  Same
denominator as `U`, because the denominator sees only the recurrence. -/
theorem lucasV_gf : lucasDenom P Q * mk (lucasV P Q) = C 2 - C P * X := by
  rw [lucasDenom_mul_mk_of_rec P Q _ (lucasV_add_two P Q)]
  rw [lucasV_zero, lucasV_one, show P - P * 2 = -P by ring, map_neg]
  ring

/-! ### The denominator factors at named roots -/

/-- `1 - (α + β) X + αβ X² = (1 - α X) (1 - β X)`.

The generating-function shadow of `lucasU_of_roots` and `lucasV_of_roots`: the two roots of
`t² - Pt + Q` reappear as the two linear factors of the denominator, reciprocated.  Splitting
`X / ((1 - αX)(1 - βX))` into partial fractions is what turns the generating function back into
`(αⁿ - βⁿ)/(α - β)`; this is the factorisation that step needs. -/
theorem lucasDenom_of_roots (α β : R) :
    lucasDenom (α + β) (α * β) = (1 - C α * X) * (1 - C β * X) := by
  rw [lucasDenom, map_add, map_mul]
  ring

/-! ### The quotient form -/

/-- The denominator has constant coefficient `1`. -/
@[simp] theorem constantCoeff_lucasDenom : constantCoeff (lucasDenom P Q) = 1 := by
  simp [lucasDenom]

/-- The denominator is a unit of `R⟦X⟧`, because its constant coefficient is `1`.  This is what
lets `∑ Uₙ Xⁿ = X / (1 - P X + Q X²)` be written without a field. -/
theorem isUnit_lucasDenom : IsUnit (lucasDenom P Q) :=
  ⟨⟨lucasDenom P Q, invOfUnit (lucasDenom P Q) 1,
    mul_invOfUnit _ 1 (by simp), invOfUnit_mul _ 1 (by simp)⟩, rfl⟩

/-- `∑ Uₙ Xⁿ = X * (1 - P X + Q X²)⁻¹`, with Mathlib's `invOfUnit` as the inverse. -/
theorem mk_lucasU_eq :
    mk (lucasU P Q) = X * invOfUnit (lucasDenom P Q) 1 := by
  have hinv : lucasDenom P Q * invOfUnit (lucasDenom P Q) 1 = 1 :=
    mul_invOfUnit _ 1 (by simp)
  calc mk (lucasU P Q)
      = 1 * mk (lucasU P Q) := (one_mul _).symm
    _ = lucasDenom P Q * invOfUnit (lucasDenom P Q) 1 * mk (lucasU P Q) := by rw [hinv]
    _ = lucasDenom P Q * mk (lucasU P Q) * invOfUnit (lucasDenom P Q) 1 := mul_right_comm _ _ _
    _ = X * invOfUnit (lucasDenom P Q) 1 := by rw [lucasU_gf]

/-- `∑ Vₙ Xⁿ = (2 - P X) * (1 - P X + Q X²)⁻¹`. -/
theorem mk_lucasV_eq :
    mk (lucasV P Q) = (C 2 - C P * X) * invOfUnit (lucasDenom P Q) 1 := by
  have hinv : lucasDenom P Q * invOfUnit (lucasDenom P Q) 1 = 1 :=
    mul_invOfUnit _ 1 (by simp)
  calc mk (lucasV P Q)
      = 1 * mk (lucasV P Q) := (one_mul _).symm
    _ = lucasDenom P Q * invOfUnit (lucasDenom P Q) 1 * mk (lucasV P Q) := by rw [hinv]
    _ = lucasDenom P Q * mk (lucasV P Q) * invOfUnit (lucasDenom P Q) 1 := mul_right_comm _ _ _
    _ = (C 2 - C P * X) * invOfUnit (lucasDenom P Q) 1 := by rw [lucasV_gf]

/-! ### The seven library sequences

Each is `lucasDenom_mul_mk_of_rec` at that sequence's own recurrence and its own two initial
values.  No induction appears below: the recurrence lemma each module already ships is the whole
input, and the numerator is read off `u 0` and `u 1`. -/

/-- `∑ Fₙ Xⁿ = X / (1 - X - X²)` — the Fibonacci generating function. -/
theorem fib_gf : (1 - X - X ^ 2) * mk (fun n => (Nat.fib n : R)) = X := by
  have hrec : ∀ n, (Nat.fib (n + 2) : R)
      = 1 * (Nat.fib (n + 1) : R) - (-1) * (Nat.fib n : R) := by
    intro n; rw [Nat.fib_add_two]; push_cast; ring
  have hd : (1 - X - X ^ 2 : R⟦X⟧) = lucasDenom (1 : R) (-1) := by
    rw [lucasDenom, map_one, map_neg, map_one]; ring
  rw [hd, lucasDenom_mul_mk_of_rec (1 : R) (-1) _ hrec]
  simp

/-- `∑ Lₙ Xⁿ = (2 - X) / (1 - X - X²)` — the Lucas generating function.  Same denominator as
Fibonacci, different numerator: that *is* the sense in which they are companion sequences. -/
theorem lucas_gf : (1 - X - X ^ 2) * mk (fun n => (lucas n : R)) = 2 - X := by
  have hrec : ∀ n, (lucas (n + 2) : R) = 1 * (lucas (n + 1) : R) - (-1) * (lucas n : R) := by
    intro n; rw [lucas_add_two]; push_cast; ring
  have hd : (1 - X - X ^ 2 : R⟦X⟧) = lucasDenom (1 : R) (-1) := by
    rw [lucasDenom, map_one, map_neg, map_one]; ring
  rw [hd, lucasDenom_mul_mk_of_rec (1 : R) (-1) _ hrec]
  simp only [lucas_zero, lucas_one, Nat.cast_ofNat, Nat.cast_one]
  rw [show (1 : R) - 1 * 2 = -1 by ring, map_neg, map_one, map_ofNat]
  ring

/-- `∑ Pₙ Xⁿ = X / (1 - 2X - X²)` — the Pell generating function. -/
theorem pellNumber_gf : (1 - 2 * X - X ^ 2) * mk (fun n => (pellNumber n : R)) = X := by
  have hrec : ∀ n, (pellNumber (n + 2) : R)
      = 2 * (pellNumber (n + 1) : R) - (-1) * (pellNumber n : R) := by
    intro n; rw [pellNumber_add_two]; push_cast; ring
  have hd : (1 - 2 * X - X ^ 2 : R⟦X⟧) = lucasDenom (2 : R) (-1) := by
    rw [lucasDenom, map_neg, map_one, map_ofNat]; ring
  rw [hd, lucasDenom_mul_mk_of_rec (2 : R) (-1) _ hrec]
  simp

/-- `∑ Hₙ Xⁿ = (1 + X) / (1 - 2X - X²)` — the half-companion Pell generating function.

`H` is *not* `V (2,-1)`; it is `V (2,-1)` shifted and halved (`lucasV_two_neg_one_succ`).  The
generating function does not care: `H` obeys the same recurrence, so it has the same denominator,
and the shift shows up only in the numerator `H 0 + (H 1 - 2 H 0) X = 1 + X`.  That is the
practical advantage of the master theorem over instantiating `lucasV_gf`. -/
theorem pellHalfCompanion_gf :
    (1 - 2 * X - X ^ 2) * mk (fun n => (pellHalfCompanion n : R)) = 1 + X := by
  have hrec : ∀ n, (pellHalfCompanion (n + 2) : R)
      = 2 * (pellHalfCompanion (n + 1) : R) - (-1) * (pellHalfCompanion n : R) := by
    intro n; rw [pellHalfCompanion_add_two]; push_cast; ring
  have hd : (1 - 2 * X - X ^ 2 : R⟦X⟧) = lucasDenom (2 : R) (-1) := by
    rw [lucasDenom, map_neg, map_one, map_ofNat]; ring
  rw [hd, lucasDenom_mul_mk_of_rec (2 : R) (-1) _ hrec]
  simp only [pellHalfCompanion_zero, pellHalfCompanion_one, Nat.cast_one, Nat.cast_ofNat]
  rw [show (3 : R) - 2 * 1 = 1 by ring, map_one]
  ring

/-- `∑ Jₙ Xⁿ = X / (1 - X - 2X²)` — the Jacobsthal generating function. -/
theorem jacobsthal_gf : (1 - X - 2 * X ^ 2) * mk (fun n => (jacobsthal n : R)) = X := by
  have hrec : ∀ n, (jacobsthal (n + 2) : R)
      = 1 * (jacobsthal (n + 1) : R) - (-2) * (jacobsthal n : R) := by
    intro n; rw [jacobsthal_add_two]; push_cast; ring
  have hd : (1 - X - 2 * X ^ 2 : R⟦X⟧) = lucasDenom (1 : R) (-2) := by
    rw [lucasDenom, map_one, map_neg, map_ofNat]; ring
  rw [hd, lucasDenom_mul_mk_of_rec (1 : R) (-2) _ hrec]
  simp

/-- `∑ jₙ Xⁿ = (2 - X) / (1 - X - 2X²)` — the Jacobsthal companion generating function. -/
theorem jacobsthalCompanion_gf :
    (1 - X - 2 * X ^ 2) * mk (fun n => (jacobsthalCompanion n : R)) = 2 - X := by
  have hrec : ∀ n, (jacobsthalCompanion (n + 2) : R)
      = 1 * (jacobsthalCompanion (n + 1) : R) - (-2) * (jacobsthalCompanion n : R) := by
    intro n; rw [jacobsthalCompanion_add_two]; push_cast; ring
  have hd : (1 - X - 2 * X ^ 2 : R⟦X⟧) = lucasDenom (1 : R) (-2) := by
    rw [lucasDenom, map_one, map_neg, map_ofNat]; ring
  rw [hd, lucasDenom_mul_mk_of_rec (1 : R) (-2) _ hrec]
  simp only [jacobsthalCompanion_zero, jacobsthalCompanion_one, Nat.cast_ofNat, Nat.cast_one]
  rw [show (1 : R) - 1 * 2 = -1 by ring, map_neg, map_one, map_ofNat]
  ring

/-- `∑ Mₙ Xⁿ = X / (1 - 3X + 2X²)` — the Mersenne generating function, `Mₙ = 2ⁿ - 1`.

The recurrence used is `M (n+2) = 3 M (n+1) - 2 M n`, which is not how `Mersenne.lean` states
anything; it comes from `lucasU_three_two` — the identification of `mersenne` as `U (3, 2)` from
`LucasSequenceCases.lean` — so this theorem is the two passes composing. -/
theorem mersenne_gf : (1 - 3 * X + 2 * X ^ 2) * mk (fun n => (mersenne n : R)) = X := by
  have hm : ∀ n, ((mersenne n : ℕ) : R) = 2 ^ n - 1 :=
    fun n => (lucasU_three_two R n).symm.trans (lucasU_three_two_eq R n)
  have hrec : ∀ n, ((mersenne (n + 2) : ℕ) : R)
      = 3 * ((mersenne (n + 1) : ℕ) : R) - 2 * ((mersenne n : ℕ) : R) := by
    intro n; rw [hm, hm, hm]; ring
  have hd : (1 - 3 * X + 2 * X ^ 2 : R⟦X⟧) = lucasDenom (3 : R) 2 := by
    rw [lucasDenom, map_ofNat, map_ofNat]
  rw [hd, lucasDenom_mul_mk_of_rec (3 : R) 2 _ hrec]
  have h1 : ((mersenne 1 : ℕ) : R) = 1 := by rw [hm]; ring
  simp [h1]

/-- The Mersenne denominator splits over `ℤ`: `1 - 3X + 2X² = (1 - X)(1 - 2X)`.

This is `lucasDenom_of_roots` at `α = 2`, `β = 1`, and it is `ROADMAP.md` §1.1's split
discriminant seen from the generating-function side: `D = 1` is exactly the statement that the
denominator factors over the base ring, so `∑ (2ⁿ - 1) Xⁿ` splits into two geometric series
`1/(1 - 2X) - 1/(1 - X)` instead of needing a quadratic irrationality. -/
theorem mersenne_gf_denom_factors :
    (1 - 3 * X + 2 * X ^ 2 : R⟦X⟧) = (1 - C (2 : R) * X) * (1 - C (1 : R) * X) := by
  have h := lucasDenom_of_roots (2 : R) 1
  rw [show (2 : R) + 1 = 3 by norm_num, show (2 : R) * 1 = 2 by norm_num, lucasDenom,
    map_ofNat, map_ofNat] at h
  exact h

/-! ### The two-term case is the general theorem

`ClassicalLean/Combinatorics/RecurrenceGeneratingFunction.lean` proves the same statement for a
Mathlib `LinearRecurrence` of any order.  `lucasDenom` is its `recDenom` at `lucasRec P Q`, so
everything above is that theorem at order `2`; the direct proofs are kept because they are
shorter and because the two-term case is the one every instance uses. -/

/-- `lucasDenom P Q` is the reversed characteristic polynomial of `lucasRec P Q`.

`lucasRec P Q` has order `2` and coefficients `![-Q, P]`; reversing gives `X` the coefficient
`P` and `X ^ 2` the coefficient `-Q`, which is `1 - P X + Q X ^ 2`. -/
theorem recDenom_lucasRec : recDenom (lucasRec P Q) = lucasDenom P Q := by
  rw [recDenom, lucasDenom, lucasRec]
  simp [Fin.sum_univ_two]
  ring

/-- The two-term coefficient identity is `coeff_recDenom_mul_mk` at `lucasRec P Q`; nothing about
the order-`2` case is special. -/
example (u : ℕ → R) (n : ℕ) :
    coeff (n + 2) (lucasDenom P Q * mk u) = u (n + 2) - (-Q * u n + P * u (n + 1)) := by
  have h := coeff_recDenom_mul_mk (lucasRec P Q) u n
  rw [recDenom_lucasRec] at h
  erw [Fin.sum_univ_two] at h
  simpa [lucasRec] using h

/-! ### Spot checks -/

-- The coefficients really are the sequence.
example : coeff 5 (mk (lucasU (3 : ℤ) 2)) = 31 := by rw [coeff_mk]; decide

example : coeff 10 (mk (lucasV (1 : ℤ) (-1))) = 123 := by rw [coeff_mk]; decide

-- The recurrence residual really is what the coefficient computes: at `(P, Q) = (1, -1)`,
-- index `4` gives `U 4 - 1 * U 3 + (-1) * U 2 = 3 - 2 - 1 = 0`.  Computed through
-- `coeff_lucasDenom_mul_mk_add_two`, not through `lucasU_gf`, so it tests the coefficient
-- lemma rather than re-reading `coeff 4 X`.
example : lucasU (1 : ℤ) (-1) 4 - 1 * lucasU (1 : ℤ) (-1) 3 + (-1) * lucasU (1 : ℤ) (-1) 2 = 0 := by
  decide

-- The same coefficient read off the generating function is `coeff 4 X = 0`; the two agree.
example : coeff 4 (lucasDenom (1 : ℤ) (-1) * mk (lucasU 1 (-1))) = 0 := by
  rw [lucasU_gf, coeff_X]
  norm_num

-- The numerator is not zero everywhere, so the check above is not vacuous.
example : coeff 1 (lucasDenom (1 : ℤ) (-1) * mk (lucasU 1 (-1))) = 1 := by
  rw [lucasU_gf, coeff_X]
  norm_num

end ClassicalLean
