/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Algebra.LinearRecurrence
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.RingTheory.Polynomial.Dickson
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Lucas sequences of parameters `(P, Q)`

For two elements `P, Q` of a commutative ring, the pair of sequences

* `U 0 = 0`, `U 1 = 1`,  `U (n + 2) = P * U (n + 1) - Q * U n`
* `V 0 = 2`, `V 1 = P`,  `V (n + 2) = P * V (n + 1) - Q * V n`

are the **Lucas sequences of the first and second kind** with parameters `(P, Q)`.  They are the
two canonical solutions of the linear recurrence whose characteristic polynomial is
`t ^ 2 - P * t + Q`; `U` starts from `(0, 1)` and `V` from the power sums of the roots.

This file is the general theory.  It exists because the library had proved instances of the same
identity more than once, in modules that share no import:

* `lucas_mul_fib` (`L n * F n = F (2n)`) and `jacobsthal_mul_jacobsthalCompanion`
  (`J n * j n = J (2n)`) are both `lucasU_two_mul` at different `(P, Q)`.
* `lucas_sq_sub_five_mul_fib_sq` (`L n ^ 2 - 5 * F n ^ 2 = 4 * (-1) ^ n`) and
  `pellHalfCompanion_sq_sub_two_mul_sq` (`H n ^ 2 - 2 * P (n+1) ^ 2 = (-1) ^ (n+1)`) are both
  `lucasV_sq_sub_discr_mul_lucasU_sq`.
* `three_mul_jacobsthal` (`3 * J n = 2 ^ n - (-1) ^ n`), `jacobsthalCompanion_eq`,
  `mersenne_eq_two_pow_sub_one` and `coe_lucas_eq` (`(L n : ℝ) = φ ^ n + ψ ^ n`) are all
  `lucasU_of_roots` or `lucasV_of_roots` at different roots, over different rings.

`ClassicalLean/NumberTheory/LucasSequenceCases.lean` is the companion file that proves those
identifications; nothing here mentions a specific sequence.

## Main definitions

* `ClassicalLean.lucasU`, `ClassicalLean.lucasV` — the two sequences, over any `CommRing`.
* `ClassicalLean.lucasDiscr P Q = P ^ 2 - 4 * Q` — the discriminant of `t ^ 2 - P * t + Q`.
* `ClassicalLean.lucasRec` — the same recurrence as a Mathlib `LinearRecurrence`, so that both
  sequences can be handed to `LinearRecurrence.eq_iff_eqOn_range_order` the way `Real.fibRec` is.
* `ClassicalLean.lucasCompanion P Q = !![0, -Q; 1, P]` — the companion matrix.

## Main results

* `lucasV_of_roots` : `V_{α+β, αβ} n = α ^ n + β ^ n`, and
  `lucasU_of_roots` : `(α - β) * U_{α+β, αβ} n = α ^ n - β ^ n`.
  **These are the master identities.**  Every closed form the library proves for a named
  sequence is one of these two at a named pair of roots, and the pair `(α, β)` need not lie in
  the ring where the parameters do — `(2, 1)` over `ℤ` gives the Mersenne numbers and `(φ, ψ)`
  over `ℝ` gives Binet, from the same theorem.
* `lucasV_succ_eq` : `V (n + 1) = U (n + 2) - Q * U n`, the bridge between the two kinds.
* `lucasU_add` : `U (m + n + 1) = U (m + 1) * U (n + 1) - Q * U m * U n`, the addition law.
* `lucasU_two_mul` : `U (2n) = U n * V n`, and `lucasV_two_mul` : `V (2n) = V n ^ 2 - 2 * Q ^ n`.
* `lucasU_cassini` : `U (n + 2) * U n - U (n + 1) ^ 2 = -Q ^ n`, and `lucasV_cassini` :
  `V (n + 2) * V n - V (n + 1) ^ 2 = D * Q ^ n`.
* `lucasV_sq_sub_discr_mul_lucasU_sq` : `V n ^ 2 - D * U n ^ 2 = 4 * Q ^ n`.
* `lucasCompanion_pow_succ` : `M ^ (n + 1) = !![-Q * U n, -Q * U (n + 1); U (n + 1), U (n + 2)]`,
  with `lucasCompanion_pow_succ_trace` (`= V (n + 1)`) and `lucasCompanion_pow_det`
  (`= Q ^ n`) as its trace and determinant.
* `lucasV_eq_dickson_one_eval`, `lucasU_succ_eq_dickson_two_eval` — the identification with
  Mathlib's `Polynomial.dickson`, and `lucasV_eq_chebyshev_C_eval`,
  `lucasU_succ_eq_chebyshev_S_eval` — its `Q = 1` case, Mathlib's Chebyshev `C` and `S`.

## What Mathlib has, and what it does not

**Mathlib already has both sequences, at general `Q`, under a different name.**
`Polynomial.dickson k a` (`RingTheory/Polynomial/Dickson.lean`) is defined by
`dickson k a 0 = 3 - k`, `dickson k a 1 = X`, `dickson k a (n + 2) = X * dickson k a (n + 1)
- C a * dickson k a n`.  So `dickson 1 Q` is `V` and `dickson 2 Q` is `U` shifted by one, both
with the parameter `a = Q` free.  `lucasV_eq_dickson_one_eval` and
`lucasU_succ_eq_dickson_two_eval` below prove exactly that, rather than asserting it.

An earlier draft of this file claimed the gap was "general `Q`", on the strength of
`grep -rn 'Lucas sequence\|lucasSeq\|LucasSequence' Mathlib`, which returns one prose line in
`NumberTheory/EllipticDivisibilitySequence.lean`.  That was a correct measurement of the wrong
object: it searched for the *name*, and the object is in Mathlib under another one.  The claim
is withdrawn; what follows is what is actually measured.

**What is not in Mathlib** — `Dickson.lean` is 280 lines (277 at v4.34.0, re-measured
2026-09-23, with the same 18 theorems), and every theorem in it beyond the
recurrence itself is at `a = 1` (`dickson_one_one_*`, `dickson_two_one_*`) or `a = 0`
(`dickson_two_zero`), except `map_dickson`, which transports along a ring hom.  In particular
there is **no addition law, no doubling identity, no Cassini identity, no discriminant relation
and no companion matrix, at any parameter**, and the one closed form,
`dickson_one_one_eval_add_inv : (dickson 1 1 n).eval (x + y) = x ^ n + y ^ n` given `x * y = 1`,
is fixed at `a = 1`.  `lucasV_of_roots` and `lucasU_of_roots` below are that statement with the
parameter free, which is what makes the Mersenne (`αβ = 2`) and Fibonacci (`αβ = -1`) instances
available from it.

Two further facts about the same object, also measured:

* `Polynomial.Chebyshev.C` and `.S` are `dickson 1 1` and `dickson 2 1` — Mathlib proves this
  itself, as `dickson_one_one_eq_chebyshev_C` and `dickson_two_one_eq_chebyshev_S`.  They are
  therefore the `Q = 1` slice of this file; `lucasV_eq_chebyshev_C_eval` and
  `lucasU_succ_eq_chebyshev_S_eval` below record that directly.
* `Mathlib/NumberTheory/PellMatiyasevic.lean` builds `Pell.xn a1 n` and `Pell.yn a1 n` for
  `d = a ^ 2 - 1`; these are `V (2a, 1) n / 2` and `U (2a, 1) n`, inside that same `Q = 1`
  slice and further restricted to even `P`.
* `Real.fibRec` (`NumberTheory/Real/GoldenRatio.lean`) is `lucasRec 1 (-1)` with the coefficient
  vector written `![1, 1]` rather than `![-Q, P]`.

**What this file is therefore for**: the identity set at free `Q`, and a plain `ℕ → R` sequence
rather than a polynomial that must be evaluated — which is what lets the library's `ℕ`-valued
sequences be identified with it by a cast, in
`ClassicalLean/NumberTheory/LucasSequenceCases.lean`.

## Naming

`U` and `V` with parameters `(P, Q)` and discriminant `D = P ^ 2 - 4Q` is the standard notation
of the literature, and "Lucas sequence" is the standard name — it is not an eponym imported from
this project's sources, and the library already ships `catalan`, `jacobsthal` and `pellNumber`
under their literature names. `lucasU`/`lucasV` keep the letters and disambiguate the pair.
-/

namespace ClassicalLean

variable {R : Type*} [CommRing R]

/-! ### The two sequences -/

/-- The Lucas sequence of the **first** kind: `U 0 = 0`, `U 1 = 1`,
`U (n + 2) = P * U (n + 1) - Q * U n`. -/
def lucasU (P Q : R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | n + 2 => P * lucasU P Q (n + 1) - Q * lucasU P Q n

/-- The Lucas sequence of the **second** kind: `V 0 = 2`, `V 1 = P`,
`V (n + 2) = P * V (n + 1) - Q * V n`. -/
def lucasV (P Q : R) : ℕ → R
  | 0 => 2
  | 1 => P
  | n + 2 => P * lucasV P Q (n + 1) - Q * lucasV P Q n

/-- The discriminant `D = P ^ 2 - 4Q` of `t ^ 2 - P * t + Q`. -/
def lucasDiscr (P Q : R) : R := P ^ 2 - 4 * Q

variable (P Q : R)

@[simp] theorem lucasU_zero : lucasU P Q 0 = 0 := rfl
@[simp] theorem lucasU_one : lucasU P Q 1 = 1 := rfl
@[simp] theorem lucasV_zero : lucasV P Q 0 = 2 := rfl
@[simp] theorem lucasV_one : lucasV P Q 1 = P := rfl

/-- The recurrence for `U`, true by definition. -/
theorem lucasU_add_two (n : ℕ) :
    lucasU P Q (n + 2) = P * lucasU P Q (n + 1) - Q * lucasU P Q n := rfl

/-- The recurrence for `V`, true by definition. -/
theorem lucasV_add_two (n : ℕ) :
    lucasV P Q (n + 2) = P * lucasV P Q (n + 1) - Q * lucasV P Q n := rfl

@[simp] theorem lucasU_two : lucasU P Q 2 = P := by
  change P * lucasU P Q 1 - Q * lucasU P Q 0 = P
  simp

@[simp] theorem lucasV_two : lucasV P Q 2 = P ^ 2 - 2 * Q := by
  change P * lucasV P Q 1 - Q * lucasV P Q 0 = P ^ 2 - 2 * Q
  simp only [lucasV_one, lucasV_zero]
  ring

theorem lucasU_three : lucasU P Q 3 = P ^ 2 - Q := by
  change P * lucasU P Q 2 - Q * lucasU P Q 1 = P ^ 2 - Q
  simp only [lucasU_two, lucasU_one]
  ring

theorem lucasDiscr_def : lucasDiscr P Q = P ^ 2 - 4 * Q := rfl

/-! ### The recurrence as a Mathlib `LinearRecurrence` -/

/-- The recurrence `u (n + 2) = P * u (n + 1) - Q * u n` as a Mathlib `LinearRecurrence`, with
coefficient vector `![-Q, P]`.  Mathlib's `Real.fibRec` is this at `(1, -1)`, written `![1, 1]`. -/
def lucasRec : LinearRecurrence R where
  order := 2
  coeffs := ![-Q, P]

/-- `U` is a solution of `lucasRec P Q`. -/
theorem lucasU_isSol_lucasRec : (lucasRec P Q).IsSolution (lucasU P Q) := by
  rw [lucasRec]
  intro n
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero,
    Fin.val_one, Nat.add_zero]
  rw [lucasU_add_two]
  ring

/-- `V` is a solution of `lucasRec P Q`. -/
theorem lucasV_isSol_lucasRec : (lucasRec P Q).IsSolution (lucasV P Q) := by
  rw [lucasRec]
  intro n
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero,
    Fin.val_one, Nat.add_zero]
  rw [lucasV_add_two]
  ring

/-! ### The master identities: both sequences from the roots -/

/-- **`V` is the power sum of the roots.** If `P = α + β` and `Q = α * β` then
`V n = α ^ n + β ^ n`.

The hypothesis is not that `α` and `β` are roots of anything — it is that `P` and `Q` are their
sum and product, which by Vieta is the same statement and is checkable without a factorisation
theorem.  Two-step induction; the step is `(α + β)(α^{n+1} + β^{n+1}) - αβ(α^n + β^n)`
multiplied out.

The theorem is stated for one ring at a time, and the leverage comes from choosing the ring:
`(α, β) = (2, 1)` over `ℤ` gives `2 ^ n + 1`, while the *same* parameters `(P, Q) = (1, -1)`
cast up to `ℝ`, where the roots `φ` and `ψ` live, give `(L n : ℝ) = φ ^ n + ψ ^ n`.  Both are
this theorem; only the ring changed. -/
theorem lucasV_of_roots (α β : R) (n : ℕ) :
    lucasV (α + β) (α * β) n = α ^ n + β ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp; ring
  | one => simp
  | more n ih1 ih2 =>
    have e : lucasV (α + β) (α * β) (n + 2)
        = (α + β) * lucasV (α + β) (α * β) (n + 1) - α * β * lucasV (α + β) (α * β) n :=
      lucasV_add_two _ _ n
    linear_combination e + (α + β) * ih2 - α * β * ih1

/-- **`U` is the difference quotient of the roots.** If `P = α + β` and `Q = α * β` then
`(α - β) * U n = α ^ n - β ^ n`.

Stated multiplied through by `α - β` so that it holds in every commutative ring, with no
division and no hypothesis that the two roots are distinct.  Over a field with `α ≠ β` it is
Binet's formula; over `ℤ` with `(α, β) = (2, 1)` the factor is `1` and it is the closed form of
the Mersenne numbers. -/
theorem lucasU_of_roots (α β : R) (n : ℕ) :
    (α - β) * lucasU (α + β) (α * β) n = α ^ n - β ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
    have e : lucasU (α + β) (α * β) (n + 2)
        = (α + β) * lucasU (α + β) (α * β) (n + 1) - α * β * lucasU (α + β) (α * β) n :=
      lucasU_add_two _ _ n
    linear_combination (α - β) * e + (α + β) * ih2 - α * β * ih1

/-! ### The bridge between the two kinds -/

/-- `V (n + 1) = U (n + 2) - Q * U n`: the second-kind sequence read off the first.  This is the
identity that makes `V` the trace of the companion matrix's powers. -/
theorem lucasV_succ_eq (n : ℕ) :
    lucasV P Q (n + 1) = lucasU P Q (n + 2) - Q * lucasU P Q n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    change lucasV P Q 2 = lucasU P Q 3 - Q * lucasU P Q 1
    rw [lucasV_two, lucasU_three]
    simp
    ring
  | more n ih1 ih2 =>
    have ih2' : lucasV P Q (n + 2) = lucasU P Q (n + 3) - Q * lucasU P Q (n + 1) := ih2
    have e1 : lucasV P Q (n + 3)
        = P * lucasV P Q (n + 2) - Q * lucasV P Q (n + 1) := lucasV_add_two P Q (n + 1)
    have e2 : lucasU P Q (n + 4)
        = P * lucasU P Q (n + 3) - Q * lucasU P Q (n + 2) := lucasU_add_two P Q (n + 2)
    have e3 : lucasU P Q (n + 2)
        = P * lucasU P Q (n + 1) - Q * lucasU P Q n := lucasU_add_two P Q n
    change lucasV P Q (n + 3) = lucasU P Q (n + 4) - Q * lucasU P Q (n + 2)
    linear_combination e1 + P * ih2' - Q * ih1 - e2 + Q * e3

/-! ### The addition law -/

/-- **The addition law.** `U (m + n + 1) = U (m + 1) * U (n + 1) - Q * U m * U n`.

Symmetric in `m` and `n`, as it must be.  Everything below about doubling is this at `m = n`. -/
theorem lucasU_add (m n : ℕ) :
    lucasU P Q (m + n + 1)
      = lucasU P Q (m + 1) * lucasU P Q (n + 1) - Q * lucasU P Q m * lucasU P Q n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    change lucasU P Q (m + 2) = lucasU P Q (m + 1) * lucasU P Q 2 - Q * lucasU P Q m * lucasU P Q 1
    rw [lucasU_add_two, lucasU_two, lucasU_one]
    ring
  | more n ih1 ih2 =>
    have ih2' : lucasU P Q (m + n + 2)
        = lucasU P Q (m + 1) * lucasU P Q (n + 2) - Q * lucasU P Q m * lucasU P Q (n + 1) := ih2
    have e : lucasU P Q (m + n + 3)
        = P * lucasU P Q (m + n + 2) - Q * lucasU P Q (m + n + 1) := lucasU_add_two P Q (m + n + 1)
    have g1 : lucasU P Q (n + 3)
        = P * lucasU P Q (n + 2) - Q * lucasU P Q (n + 1) := lucasU_add_two P Q (n + 1)
    have g2 : lucasU P Q (n + 2)
        = P * lucasU P Q (n + 1) - Q * lucasU P Q n := lucasU_add_two P Q n
    change lucasU P Q (m + n + 3)
        = lucasU P Q (m + 1) * lucasU P Q (n + 3) - Q * lucasU P Q m * lucasU P Q (n + 2)
    linear_combination e + P * ih2' - Q * ih1 - lucasU P Q (m + 1) * g1
      + Q * lucasU P Q m * g2

/-! ### Doubling -/

/-- **The doubling identity for `U`**: `U (2n) = U n * V n`.

This is `lucasU_add` at `m = n + 1`, with the inner factor identified as `V (n + 1)` by
`lucasV_succ_eq`.  At `(P, Q) = (1, -1)` it is `L n * F n = F (2n)` and at `(1, -2)` it is
`J n * j n = J (2n)`; the library proved those two separately before this file existed. -/
theorem lucasU_two_mul (n : ℕ) : lucasU P Q (2 * n) = lucasU P Q n * lucasV P Q n := by
  cases n with
  | zero => simp
  | succ k =>
    have h : lucasU P Q (2 * (k + 1))
        = lucasU P Q (k + 2) * lucasU P Q (k + 1) - Q * lucasU P Q (k + 1) * lucasU P Q k := by
      have h0 := lucasU_add P Q (k + 1) k
      rw [show k + 1 + k + 1 = 2 * (k + 1) from by omega] at h0
      exact h0
    rw [h, lucasV_succ_eq]
    ring

/-- The three quantities carried by the induction behind the discriminant identity: the relation
at `n`, at `n + 1`, and the mixed form.  `lucasDiscr P Q` is never unfolded in the step — the
argument uses only that the expression is bilinear in the pair `(V, U)` with a fixed coefficient,
so the value of `D` is needed once, in the base case. -/
private theorem lucas_discr_aux (n : ℕ) :
    (lucasV P Q n ^ 2 - lucasDiscr P Q * lucasU P Q n ^ 2 = 4 * Q ^ n) ∧
      (lucasV P Q (n + 1) ^ 2 - lucasDiscr P Q * lucasU P Q (n + 1) ^ 2 = 4 * Q ^ (n + 1)) ∧
      (lucasV P Q n * lucasV P Q (n + 1)
        - lucasDiscr P Q * lucasU P Q n * lucasU P Q (n + 1) = 2 * P * Q ^ n) := by
  induction n with
  | zero =>
    refine ⟨by norm_num, ?_, ?_⟩
    · change lucasV P Q 1 ^ 2 - lucasDiscr P Q * lucasU P Q 1 ^ 2 = 4 * Q ^ 1
      simp only [lucasV_one, lucasU_one, lucasDiscr_def]
      ring
    · change lucasV P Q 0 * lucasV P Q 1
          - lucasDiscr P Q * lucasU P Q 0 * lucasU P Q 1 = 2 * P * Q ^ 0
      simp only [lucasV_zero, lucasV_one, lucasU_zero, lucasU_one, lucasDiscr_def]
      ring
  | succ n ih =>
    obtain ⟨hA, hA1, hB⟩ := ih
    have eV : lucasV P Q (n + 2)
        = P * lucasV P Q (n + 1) - Q * lucasV P Q n := lucasV_add_two P Q n
    have eU : lucasU P Q (n + 2)
        = P * lucasU P Q (n + 1) - Q * lucasU P Q n := lucasU_add_two P Q n
    refine ⟨hA1, ?_, ?_⟩
    · change lucasV P Q (n + 2) ^ 2 - lucasDiscr P Q * lucasU P Q (n + 2) ^ 2 = 4 * Q ^ (n + 2)
      rw [eV, eU]
      linear_combination (P ^ 2) * hA1 - 2 * P * Q * hB + Q ^ 2 * hA
    · change lucasV P Q (n + 1) * lucasV P Q (n + 2)
          - lucasDiscr P Q * lucasU P Q (n + 1) * lucasU P Q (n + 2) = 2 * P * Q ^ (n + 1)
      rw [eV, eU]
      linear_combination P * hA1 - Q * hB

/-- **The discriminant identity**: `V n ^ 2 - D * U n ^ 2 = 4 * Q ^ n`, where `D = P ^ 2 - 4Q`.

At `(P, Q) = (1, -1)`, where `D = 5`, this is `L n ^ 2 - 5 * F n ^ 2 = 4 * (-1) ^ n`; at
`(2, -1)`, where `D = 8`, it is the Pell relation `H n ^ 2 - 2 * P (n + 1) ^ 2 = (-1) ^ (n + 1)`
after dividing by `4`.  The library proved both separately. -/
theorem lucasV_sq_sub_discr_mul_lucasU_sq (n : ℕ) :
    lucasV P Q n ^ 2 - lucasDiscr P Q * lucasU P Q n ^ 2 = 4 * Q ^ n :=
  (lucas_discr_aux P Q n).1

/-- The mixed companion of the discriminant identity:
`V n * V (n + 1) - D * U n * U (n + 1) = 2 * P * Q ^ n`. -/
theorem lucasV_mul_lucasV_succ_sub_discr (n : ℕ) :
    lucasV P Q n * lucasV P Q (n + 1)
      - lucasDiscr P Q * lucasU P Q n * lucasU P Q (n + 1) = 2 * P * Q ^ n :=
  (lucas_discr_aux P Q n).2.2

/-! ### Cassini -/

/-- **Cassini's identity for `U`**: `U (n + 2) * U n - U (n + 1) ^ 2 = -Q ^ n`.

At `(1, -1)` this is Cassini for the Fibonacci numbers. -/
theorem lucasU_cassini (n : ℕ) :
    lucasU P Q (n + 2) * lucasU P Q n - lucasU P Q (n + 1) ^ 2 = -Q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e1 : lucasU P Q (n + 3)
        = P * lucasU P Q (n + 2) - Q * lucasU P Q (n + 1) := lucasU_add_two P Q (n + 1)
    have e2 : lucasU P Q (n + 2)
        = P * lucasU P Q (n + 1) - Q * lucasU P Q n := lucasU_add_two P Q n
    change lucasU P Q (n + 3) * lucasU P Q (n + 1) - lucasU P Q (n + 2) ^ 2 = -Q ^ (n + 1)
    linear_combination lucasU P Q (n + 1) * e1 - lucasU P Q (n + 2) * e2 + Q * ih

/-- **Cassini's identity for `V`**: `V (n + 2) * V n - V (n + 1) ^ 2 = D * Q ^ n`.

The sign and the factor differ from the `U` version by exactly the discriminant; that is the
same `D` as in `lucasV_sq_sub_discr_mul_lucasU_sq`, and it is why the two Cassini identities are
not the same statement. -/
theorem lucasV_cassini (n : ℕ) :
    lucasV P Q (n + 2) * lucasV P Q n - lucasV P Q (n + 1) ^ 2 = lucasDiscr P Q * Q ^ n := by
  induction n with
  | zero =>
    change lucasV P Q 2 * lucasV P Q 0 - lucasV P Q 1 ^ 2 = lucasDiscr P Q * Q ^ 0
    simp only [lucasV_two, lucasV_zero, lucasV_one, lucasDiscr_def]
    ring
  | succ n ih =>
    have e1 : lucasV P Q (n + 3)
        = P * lucasV P Q (n + 2) - Q * lucasV P Q (n + 1) := lucasV_add_two P Q (n + 1)
    have e2 : lucasV P Q (n + 2)
        = P * lucasV P Q (n + 1) - Q * lucasV P Q n := lucasV_add_two P Q n
    change lucasV P Q (n + 3) * lucasV P Q (n + 1) - lucasV P Q (n + 2) ^ 2
        = lucasDiscr P Q * Q ^ (n + 1)
    linear_combination lucasV P Q (n + 1) * e1 - lucasV P Q (n + 2) * e2 + Q * ih

/-- The two halves of the `V`-doubling induction, proved simultaneously:
`V (2n) = V n ^ 2 - 2 Q ^ n` and `V (2n + 1) = V n * V (n + 1) - P * Q ^ n`.  Each step consumes
`lucasV_cassini`. -/
private theorem lucasV_doubling_aux (n : ℕ) :
    lucasV P Q (2 * n) = lucasV P Q n ^ 2 - 2 * Q ^ n ∧
      lucasV P Q (2 * n + 1) = lucasV P Q n * lucasV P Q (n + 1) - P * Q ^ n := by
  induction n with
  | zero =>
    constructor
    · change lucasV P Q 0 = lucasV P Q 0 ^ 2 - 2 * Q ^ 0
      simp only [lucasV_zero]
      ring
    · change lucasV P Q 1 = lucasV P Q 0 * lucasV P Q 1 - P * Q ^ 0
      simp only [lucasV_zero, lucasV_one]
      ring
  | succ k ih =>
    obtain ⟨hA, hB⟩ := ih
    have g2 : lucasV P Q (k + 2)
        = P * lucasV P Q (k + 1) - Q * lucasV P Q k := lucasV_add_two P Q k
    have hc2 : lucasV P Q k * (P * lucasV P Q (k + 1) - Q * lucasV P Q k)
        - lucasV P Q (k + 1) ^ 2 = (P ^ 2 - 4 * Q) * Q ^ k := by
      have hc := lucasV_cassini P Q k
      rw [lucasDiscr_def, g2] at hc
      linear_combination hc
    have e : lucasV P Q (2 * k + 2)
        = P * lucasV P Q (2 * k + 1) - Q * lucasV P Q (2 * k) := lucasV_add_two P Q (2 * k)
    have hAk : lucasV P Q (2 * (k + 1)) = lucasV P Q (k + 1) ^ 2 - 2 * Q ^ (k + 1) := by
      rw [show 2 * (k + 1) = 2 * k + 2 from by omega]
      linear_combination e + P * hB - Q * hA + hc2
    refine ⟨hAk, ?_⟩
    have e3 : lucasV P Q (2 * k + 3)
        = P * lucasV P Q (2 * k + 2) - Q * lucasV P Q (2 * k + 1) := lucasV_add_two P Q (2 * k + 1)
    have hAk' : lucasV P Q (2 * k + 2) = lucasV P Q (k + 1) ^ 2 - 2 * Q ^ (k + 1) := by
      rw [show 2 * k + 2 = 2 * (k + 1) from by omega]; exact hAk
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 from by omega]
    linear_combination e3 + P * hAk' - Q * hB - lucasV P Q (k + 1) * g2

/-- **The doubling identity for `V`**: `V (2n) = V n ^ 2 - 2 * Q ^ n`.

At `(1, -1)` this is `L (2n) = L n ^ 2 - 2 * (-1) ^ n`, which `NumberTheory/Lucas.lean` proves
separately by its own simultaneous induction. -/
theorem lucasV_two_mul (n : ℕ) :
    lucasV P Q (2 * n) = lucasV P Q n ^ 2 - 2 * Q ^ n :=
  (lucasV_doubling_aux P Q n).1

/-- The companion of the `V`-doubling identity: `V (2n + 1) = V n * V (n + 1) - P * Q ^ n`. -/
theorem lucasV_two_mul_add_one (n : ℕ) :
    lucasV P Q (2 * n + 1) = lucasV P Q n * lucasV P Q (n + 1) - P * Q ^ n :=
  (lucasV_doubling_aux P Q n).2

/-! ### The companion matrix -/

/-- The companion matrix `!![0, -Q; 1, P]` of `t ^ 2 - P * t + Q`.  The row convention is the one
`ClassicalLean/Geometry/Helix.lean` already uses: `Geometry.companionMatrix` is this at
`(P, Q) = (3, 1)` over `ℝ`. -/
def lucasCompanion : Matrix (Fin 2) (Fin 2) R := !![0, -Q; 1, P]

@[simp] theorem lucasCompanion_trace : (lucasCompanion P Q).trace = P := by
  simp [lucasCompanion, Matrix.trace_fin_two]

@[simp] theorem lucasCompanion_det : (lucasCompanion P Q).det = Q := by
  simp [lucasCompanion, Matrix.det_fin_two]

/-- **The powers of the companion matrix, entry by entry.**
`M ^ (n + 1) = !![-Q * U n, -Q * U (n + 1); U (n + 1), U (n + 2)]`.

This is the master statement of which everything in this section is a projection: the trace is
`V (n + 1)` by `lucasV_succ_eq`, and the determinant is `Q ^ (n + 1)`. -/
theorem lucasCompanion_pow_succ (n : ℕ) :
    lucasCompanion P Q ^ (n + 1)
      = !![-Q * lucasU P Q n, -Q * lucasU P Q (n + 1);
           lucasU P Q (n + 1), lucasU P Q (n + 2)] := by
  induction n with
  | zero =>
    rw [pow_one, lucasCompanion]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    have e1 : lucasU P Q (n + 2)
        = P * lucasU P Q (n + 1) - Q * lucasU P Q n := lucasU_add_two P Q n
    have e2 : lucasU P Q (n + 3)
        = P * lucasU P Q (n + 2) - Q * lucasU P Q (n + 1) := lucasU_add_two P Q (n + 1)
    change lucasCompanion P Q ^ (n + 1) * lucasCompanion P Q
        = !![-Q * lucasU P Q (n + 1), -Q * lucasU P Q (n + 2);
             lucasU P Q (n + 2), lucasU P Q (n + 3)]
    rw [ih, lucasCompanion, Matrix.mul_fin_two, e2, e1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The trace of `M ^ (n + 1)` is `V (n + 1)`, by `lucasV_succ_eq`. -/
theorem lucasCompanion_pow_succ_trace (n : ℕ) :
    (lucasCompanion P Q ^ (n + 1)).trace = lucasV P Q (n + 1) := by
  rw [lucasCompanion_pow_succ, Matrix.trace_fin_two, lucasV_succ_eq]
  simp
  ring

/-- The determinant of `M ^ n` is `Q ^ n`, from `Matrix.det_pow`. -/
theorem lucasCompanion_pow_det (n : ℕ) : (lucasCompanion P Q ^ n).det = Q ^ n := by
  rw [Matrix.det_pow, lucasCompanion_det]

/-- **The determinant expanded on the entries**: `det (M ^ (n+1))` is `Q` times the Cassini
expression.

Together with `lucasCompanion_pow_det` this says `Q * (U (n+1) ^ 2 - U (n+2) * U n) = Q ^ (n+1)`,
which is Cassini's identity **multiplied by `Q`**. -/
theorem lucasCompanion_pow_succ_det_eq (n : ℕ) :
    (lucasCompanion P Q ^ (n + 1)).det
      = Q * (lucasU P Q (n + 1) ^ 2 - lucasU P Q (n + 2) * lucasU P Q n) := by
  rw [lucasCompanion_pow_succ, Matrix.det_fin_two_of]; ring

/-- **Cassini's identity is *not* the determinant, and this records the exact gap.**

The determinant yields only the `Q`-multiple: cancelling `Q` needs `Q` to be a non-zero-divisor,
which is false in a general commutative ring — at `Q = 0` the determinant identity is `0 = 0` and
says nothing, while `lucasU_cassini` still gives `U (n+2) * U n - U (n+1) ^ 2 = -0 ^ n`.  So the
shipped `lucasU_cassini`, proved by induction, is **strictly stronger** than what the matrix
argument delivers, and the two are different theorems rather than two proofs of one.

The same asymmetry does *not* affect the trace: `lucasCompanion_pow_succ_trace` gives `V` on the
nose, with nothing to cancel.  Trace and determinant are the two basic invariants of the one
matrix, and they reach the two classical identities — Binet-style power sums and Cassini — with
only the first of the two coming for free. -/
theorem mul_lucasU_cassini (n : ℕ) :
    Q * (lucasU P Q (n + 2) * lucasU P Q n - lucasU P Q (n + 1) ^ 2) = Q * -Q ^ n := by
  have h := lucasCompanion_pow_succ_det_eq P Q n
  rw [lucasCompanion_pow_det] at h
  linear_combination h

/-! ### The general-parameter case is Mathlib's Dickson pair -/

open Polynomial in
/-- `V P Q n` is Mathlib's `Polynomial.dickson 1 Q` evaluated at `P`.

`dickson k a` starts from `3 - k`, so the first kind (`k = 1`) starts from `2`, which is `V 0`;
the recurrence is the same with `C a` for `Q`.  The parameter `a` is free in Mathlib's
definition, so this is the whole of `V`, not a slice of it. -/
theorem lucasV_eq_dickson_one_eval (n : ℕ) :
    lucasV P Q n = (dickson 1 Q n).eval P := by
  induction n using Nat.twoStepInduction with
  | zero => simp; norm_num
  | one => simp
  | more n ih1 ih2 =>
    rw [lucasV_add_two, dickson_add_two, ih1, ih2]
    simp

open Polynomial in
/-- `U P Q (n + 1)` is Mathlib's `Polynomial.dickson 2 Q n` evaluated at `P`.  The second kind
starts from `3 - 2 = 1`, which is `U 1`, so the index shift is by one — the same shift as the
Chebyshev statement below, which is this at `Q = 1`. -/
theorem lucasU_succ_eq_dickson_two_eval (n : ℕ) :
    lucasU P Q (n + 1) = (dickson 2 Q n).eval P := by
  induction n using Nat.twoStepInduction with
  | zero => simp; norm_num
  | one => simp
  | more n ih1 ih2 =>
    change lucasU P Q (n + 1 + 2) = (dickson 2 Q (n + 2)).eval P
    rw [lucasU_add_two, dickson_add_two, ih1, ih2]
    simp

/-! ### The `Q = 1` slice is Mathlib's Chebyshev pair -/

open Polynomial in
/-- `V P 1 n` is Mathlib's `Polynomial.Chebyshev.C` evaluated at `P`.  Both satisfy
`x 0 = 2`, `x 1 = X`, `x (n + 2) = X * x (n + 1) - x n`; this is the `Q = 1` slice of the
present file.  Mathlib itself proves `dickson_one_one_eq_chebyshev_C`, so this theorem is also
`lucasV_eq_dickson_one_eval` at `Q = 1`; it is stated separately because the Chebyshev name is
the one a reader looking for `T`, `U`, `C` or `S` will search. -/
theorem lucasV_eq_chebyshev_C_eval (n : ℕ) :
    lucasV P 1 n = (Chebyshev.C R (n : ℤ)).eval P := by
  induction n using Nat.twoStepInduction with
  | zero => simp [Chebyshev.C_zero]
  | one => simp [Chebyshev.C_one]
  | more n ih1 ih2 =>
    have hC : Chebyshev.C R ((n : ℤ) + 2)
        = X * Chebyshev.C R ((n : ℤ) + 1) - Chebyshev.C R (n : ℤ) := Chebyshev.C_add_two R n
    have h2 : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
    have h1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    have ih2' : lucasV P 1 (n + 1) = (Chebyshev.C R ((n : ℤ) + 1)).eval P := by
      rw [← h1]; exact ih2
    rw [lucasV_add_two, h2, hC, ih1, ih2']
    simp

open Polynomial in
/-- `U P 1 (n + 1)` is Mathlib's `Polynomial.Chebyshev.S` evaluated at `P`.  The index shift is
real: `S 0 = 1 = U 1`, so `S n` is `U (n + 1)`, not `U n`. -/
theorem lucasU_succ_eq_chebyshev_S_eval (n : ℕ) :
    lucasU P 1 (n + 1) = (Chebyshev.S R (n : ℤ)).eval P := by
  induction n using Nat.twoStepInduction with
  | zero => simp [Chebyshev.S_zero]
  | one => simp [Chebyshev.S_one]
  | more n ih1 ih2 =>
    have hS : Chebyshev.S R ((n : ℤ) + 2)
        = X * Chebyshev.S R ((n : ℤ) + 1) - Chebyshev.S R (n : ℤ) := Chebyshev.S_add_two R n
    have h2 : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
    have h1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    have ih2' : lucasU P 1 (n + 2) = (Chebyshev.S R ((n : ℤ) + 1)).eval P := by
      rw [← h1]; exact ih2
    change lucasU P 1 (n + 1 + 2) = (Chebyshev.S R ((n + 2 : ℕ) : ℤ)).eval P
    rw [lucasU_add_two, h2, hS, ih1, ih2']
    simp

/-! ### Spot checks -/

-- `U (3, 2)` is `2 ^ n - 1` and `V (3, 2)` is `2 ^ n + 1`.
example : lucasU (3 : ℤ) 2 5 = 31 := by decide
example : lucasV (3 : ℤ) 2 5 = 33 := by decide

-- `U (1, -1)` is Fibonacci and `V (1, -1)` is Lucas.
example : lucasU (1 : ℤ) (-1) 10 = 55 := by decide
example : lucasV (1 : ℤ) (-1) 10 = 123 := by decide

-- `U (2, -1)` is Pell.
example : lucasU (2 : ℤ) (-1) 6 = 70 := by decide

-- Doubling, at a pair where both factors are nontrivial: `U 10 = 55 = 5 * 11 = U 5 * V 5`.
example : lucasU (1 : ℤ) (-1) 5 * lucasV (1 : ℤ) (-1) 5 = lucasU (1 : ℤ) (-1) 10 := by decide

-- The discriminant identity at `(1, -1)`, where `D = 5`: `V 4 ^ 2 - 5 * U 4 ^ 2 = 4`.
example :
    lucasV (1 : ℤ) (-1) 4 ^ 2 - lucasDiscr (1 : ℤ) (-1) * lucasU (1 : ℤ) (-1) 4 ^ 2 = 4 := by
  decide

end ClassicalLean
