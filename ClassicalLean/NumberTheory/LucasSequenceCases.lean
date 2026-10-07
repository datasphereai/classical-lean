/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.NumberTheory.LucasSequence
import ClassicalLean.NumberTheory.Lucas
import ClassicalLean.NumberTheory.LucasCompanion
import ClassicalLean.NumberTheory.Pell
import ClassicalLean.NumberTheory.Jacobsthal
import ClassicalLean.NumberTheory.Mersenne
import ClassicalLean.GoldenRatio.Characterisations

/-!
# Seven library sequences are one Lucas sequence, at five parameter pairs

`ClassicalLean/NumberTheory/LucasSequence.lean` defines `lucasU P Q` and `lucasV P Q` over an
arbitrary commutative ring and proves the standard identity set once.  This file identifies the
seven named integer sequences the library ships or uses — `Nat.fib`, `lucas`, `pellNumber`,
`pellHalfCompanion`, `jacobsthal`, `jacobsthalCompanion` and Mathlib's `mersenne` — as instances
at five parameter pairs, and then exhibits theorems
that were proved separately in modules sharing no import as specialisations of a single theorem.

| library sequence | is | `(P, Q)` | `D = P² - 4Q` |
|---|---|---|---|
| `Nat.fib` (Mathlib) | `U` | `(1, -1)` | `5` |
| `ClassicalLean.lucas` | `V` | `(1, -1)` | `5` |
| `pellNumber` | `U` | `(2, -1)` | `8` |
| `2 * pellHalfCompanion` (shifted) | `V` | `(2, -1)` | `8` |
| `jacobsthal` | `U` | `(1, -2)` | `9` |
| `jacobsthalCompanion` | `V` | `(1, -2)` | `9` |
| `mersenne` (`2 ^ n - 1`) | `U` | `(3, 2)` | `1` |
| `2 ^ n + 1` | `V` | `(3, 2)` | `1` |
| `Nat.fib (2n)` | `U` | `(3, 1)` | `5` |
| `lucas (2n)` | `V` | `(3, 1)` | `5` |

The `(3, 2)` row is the one worth pausing on: **the Mersenne numbers are a Lucas sequence.**
`M n = 2 ^ n - 1` is `U (3, 2)` because `2` and `1` are the roots of `t ^ 2 - 3t + 2`, and the
discriminant is `1` — the degenerate case where the two roots are rational and the sequence is a
difference of two geometric progressions rather than a genuinely quadratic-irrational one.
That single fact places `Mersenne.lean`, `MersenneOrder.lean` and `MersenneFactorialPart.lean`
in the same family as `Lucas.lean` and `Pell.lean`, which the library had treated as unrelated.

The `(3, 1)` row says the even-index subsequences of the Fibonacci–Lucas pair are themselves a
Lucas sequence, which is `NumberTheory/LucasCompanion.lean` in one line.

## What this file is for

Not renaming.  Each library sequence keeps its own definition, its own module and its own
proofs; a definitional collapse would lose the arithmetic those modules do in `ℕ`.  What this
file adds is that a fact proved for one of them is available for all of them, and the section
"Theorems that were proved twice" below is the evidence: `lucas_mul_fib` and
`jacobsthal_mul_jacobsthalCompanion` are the *same theorem*, `lucasU_two_mul`, at two `(P, Q)`.

## Main results

* `lucasU_one_neg_one`, `lucasV_one_neg_one`, `lucasU_two_neg_one`,
  `lucasV_two_neg_one_succ`, `lucasU_one_neg_two`, `lucasV_one_neg_two`,
  `lucasU_three_two`, `lucasV_three_two`, `lucasU_three_one`, `lucasV_three_one` — the ten
  identifications of the table.
* `Geometry.companionMatrix_eq_lucasCompanion` : the matrix in `Geometry/Helix.lean` is
  `lucasCompanion (3 : ℝ) 1`, so `companionMatrix_pow_trace` is
  `lucasCompanion_pow_succ_trace` at `(3, 1)`.
-/

namespace ClassicalLean

variable (R : Type*) [CommRing R]

/-! ### Fibonacci and Lucas: `(P, Q) = (1, -1)` -/

/-- `U (1, -1)` is `Nat.fib`.  Stated over an arbitrary commutative ring, because the two uses
below are over `ℤ` and over `ℝ` and the cast of a `ℕ`-valued recurrence is exact in both. -/
theorem lucasU_one_neg_one (n : ℕ) : lucasU (1 : R) (-1) n = (Nat.fib n : R) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
    have e : lucasU (1 : R) (-1) (n + 2)
        = 1 * lucasU (1 : R) (-1) (n + 1) - (-1) * lucasU (1 : R) (-1) n :=
      lucasU_add_two 1 (-1) n
    have f : (Nat.fib (n + 2) : R) = (Nat.fib n : R) + (Nat.fib (n + 1) : R) := by
      rw [Nat.fib_add_two]; push_cast; ring
    rw [e, ih1, ih2, f]
    ring

/-- `V (1, -1)` is `ClassicalLean.lucas`. -/
theorem lucasV_one_neg_one (n : ℕ) : lucasV (1 : R) (-1) n = (lucas n : R) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
    have e : lucasV (1 : R) (-1) (n + 2)
        = 1 * lucasV (1 : R) (-1) (n + 1) - (-1) * lucasV (1 : R) (-1) n :=
      lucasV_add_two 1 (-1) n
    have f : (lucas (n + 2) : R) = (lucas (n + 1) : R) + (lucas n : R) := by
      rw [lucas_add_two]; push_cast; ring
    rw [e, ih1, ih2, f]
    ring

/-! ### Pell: `(P, Q) = (2, -1)` -/

/-- `U (2, -1)` is `pellNumber`. -/
theorem lucasU_two_neg_one (n : ℕ) : lucasU (2 : R) (-1) n = (pellNumber n : R) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
    have e : lucasU (2 : R) (-1) (n + 2)
        = 2 * lucasU (2 : R) (-1) (n + 1) - (-1) * lucasU (2 : R) (-1) n :=
      lucasU_add_two 2 (-1) n
    have f : (pellNumber (n + 2) : R) = 2 * (pellNumber (n + 1) : R) + (pellNumber n : R) := by
      rw [pellNumber_add_two]; push_cast; ring
    rw [e, ih1, ih2, f]
    ring

/-- `V (2, -1)` is twice the half-companion Pell sequence, shifted by one:
`V (n + 1) = 2 * H n`.  The shift and the factor `2` are both real — `H` is called a *half*
companion precisely because `V` is even and `H = V / 2`, and `H 0 = 1 = V 1 / 2`. -/
theorem lucasV_two_neg_one_succ (n : ℕ) :
    lucasV (2 : R) (-1) (n + 1) = 2 * (pellHalfCompanion n : R) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    change lucasV (2 : R) (-1) 2 = 2 * (pellHalfCompanion 1 : R)
    rw [lucasV_two, pellHalfCompanion_one]
    push_cast
    ring
  | more n ih1 ih2 =>
    have ih2' : lucasV (2 : R) (-1) (n + 2) = 2 * (pellHalfCompanion (n + 1) : R) := ih2
    have e : lucasV (2 : R) (-1) (n + 3)
        = 2 * lucasV (2 : R) (-1) (n + 2) - (-1) * lucasV (2 : R) (-1) (n + 1) :=
      lucasV_add_two 2 (-1) (n + 1)
    have f : (pellHalfCompanion (n + 2) : R)
        = 2 * (pellHalfCompanion (n + 1) : R) + (pellHalfCompanion n : R) := by
      rw [pellHalfCompanion_add_two]; push_cast; ring
    change lucasV (2 : R) (-1) (n + 3) = 2 * (pellHalfCompanion (n + 2) : R)
    rw [e, ih1, ih2', f]
    ring

/-! ### Jacobsthal: `(P, Q) = (1, -2)` -/

/-- `U (1, -2)` is `jacobsthal`. -/
theorem lucasU_one_neg_two (n : ℕ) : lucasU (1 : R) (-2) n = (jacobsthal n : R) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
    have e : lucasU (1 : R) (-2) (n + 2)
        = 1 * lucasU (1 : R) (-2) (n + 1) - (-2) * lucasU (1 : R) (-2) n :=
      lucasU_add_two 1 (-2) n
    have f : (jacobsthal (n + 2) : R) = (jacobsthal (n + 1) : R) + 2 * (jacobsthal n : R) := by
      rw [jacobsthal_add_two]; push_cast; ring
    rw [e, ih1, ih2, f]
    ring

/-- `V (1, -2)` is `jacobsthalCompanion`. -/
theorem lucasV_one_neg_two (n : ℕ) :
    lucasV (1 : R) (-2) n = (jacobsthalCompanion n : R) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
    have e : lucasV (1 : R) (-2) (n + 2)
        = 1 * lucasV (1 : R) (-2) (n + 1) - (-2) * lucasV (1 : R) (-2) n :=
      lucasV_add_two 1 (-2) n
    have f : (jacobsthalCompanion (n + 2) : R)
        = (jacobsthalCompanion (n + 1) : R) + 2 * (jacobsthalCompanion n : R) := by
      rw [jacobsthalCompanion_add_two]; push_cast; ring
    rw [e, ih1, ih2, f]
    ring

/-! ### Mersenne: `(P, Q) = (3, 2)`, the split case `D = 1` -/

/-- `U (3, 2) n = 2 ^ n - 1`.  This is `lucasU_of_roots` at `α = 2`, `β = 1`: the two roots of
`t ^ 2 - 3t + 2` are rational, their difference is `1`, and the identity needs no division. -/
theorem lucasU_three_two_eq (n : ℕ) : lucasU (3 : R) 2 n = 2 ^ n - 1 := by
  have h := lucasU_of_roots (2 : R) 1 n
  rw [show (2 : R) + 1 = 3 by norm_num, show (2 : R) * 1 = 2 by norm_num,
    show (2 : R) - 1 = 1 by norm_num, one_mul, one_pow] at h
  exact h

/-- **The Mersenne numbers are a Lucas sequence**: `U (3, 2) n = M n`, for Mathlib's `mersenne`.
The cast from `ℕ` is exact because `1 ≤ 2 ^ n` (Lean core's `Nat.one_le_two_pow`). -/
theorem lucasU_three_two (n : ℕ) : lucasU (3 : R) 2 n = (mersenne n : R) := by
  have hm : (mersenne n : ℕ) = 2 ^ n - 1 := rfl
  rw [lucasU_three_two_eq, hm, Nat.cast_sub Nat.one_le_two_pow]
  push_cast
  ring

/-- `V (3, 2) n = 2 ^ n + 1`, the companion of the Mersenne numbers.  This is
`lucasV_of_roots` at `α = 2`, `β = 1`. -/
theorem lucasV_three_two (n : ℕ) : lucasV (3 : R) 2 n = 2 ^ n + 1 := by
  have h := lucasV_of_roots (2 : R) 1 n
  rw [show (2 : R) + 1 = 3 by norm_num, show (2 : R) * 1 = 2 by norm_num, one_pow] at h
  exact h

/-! ### The even-index Fibonacci–Lucas pair: `(P, Q) = (3, 1)` -/

/-- `U (3, 1) n = F (2n)`. -/
theorem lucasU_three_one (n : ℕ) : lucasU (3 : R) 1 n = (Nat.fib (2 * n) : R) := by
  have f : ∀ k : ℕ, Nat.fib (2 * (k + 2)) + Nat.fib (2 * k) = 3 * Nat.fib (2 * (k + 1)) := by
    intro k
    have h1 : Nat.fib (2 * k + 2) = Nat.fib (2 * k) + Nat.fib (2 * k + 1) := Nat.fib_add_two
    have h2 : Nat.fib (2 * k + 3) = Nat.fib (2 * k + 1) + Nat.fib (2 * k + 2) := Nat.fib_add_two
    have h3 : Nat.fib (2 * k + 4) = Nat.fib (2 * k + 2) + Nat.fib (2 * k + 3) := Nat.fib_add_two
    rw [show 2 * (k + 2) = 2 * k + 4 from by omega, show 2 * (k + 1) = 2 * k + 2 from by omega]
    omega
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
    have e : lucasU (3 : R) 1 (n + 2)
        = 3 * lucasU (3 : R) 1 (n + 1) - 1 * lucasU (3 : R) 1 n := lucasU_add_two 3 1 n
    have fR : (Nat.fib (2 * (n + 2)) : R) + (Nat.fib (2 * n) : R)
        = 3 * (Nat.fib (2 * (n + 1)) : R) := by
      have := congrArg (fun m : ℕ => (m : R)) (f n)
      push_cast at this
      linear_combination this
    rw [e, ih1, ih2]
    linear_combination -fR

/-- `V (3, 1) n = L (2n)`.  With `lucasU_three_one` this says the even-index subsequences of the
Fibonacci–Lucas pair are themselves a Lucas sequence — the content of
`NumberTheory/LucasCompanion.lean`, in one parameter pair. -/
theorem lucasV_three_one (n : ℕ) : lucasV (3 : R) 1 n = (lucas (2 * n) : R) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
    have e : lucasV (3 : R) 1 (n + 2)
        = 3 * lucasV (3 : R) 1 (n + 1) - 1 * lucasV (3 : R) 1 n := lucasV_add_two 3 1 n
    have fR : (lucas (2 * (n + 2)) : R)
        = 3 * (lucas (2 * (n + 1)) : R) - (lucas (2 * n) : R) := by
      have := congrArg (fun z : ℤ => (z : R)) (lucas_two_mul_recurrence n)
      push_cast at this
      linear_combination this
    rw [e, ih1, ih2, fR]
    ring

/-! ### The companion matrix of `Geometry/Helix.lean` -/

/-- The matrix `!![0, -1; 1, 3]` that `Geometry/Helix.lean` builds is `lucasCompanion 3 1` over
`ℝ`.  It holds by `rfl`: the two definitions are the same matrix literal at `(P, Q) = (3, 1)`. -/
theorem companionMatrix_eq_lucasCompanion :
    Geometry.companionMatrix = lucasCompanion (3 : ℝ) 1 := rfl

/-! ### Theorems that were proved twice

Each `example` below closes a shipped theorem from the general identity, at the parameters of
the table.  The originals are untouched; these are the evidence that the general theorem is the
same statement, not merely a similar one. -/

-- `lucas_mul_fib : L n * F n = F (2n)` is `lucasU_two_mul` at `(1, -1)`.
example (n : ℕ) : lucas n * Nat.fib n = Nat.fib (2 * n) := by
  have h := lucasU_two_mul (1 : ℤ) (-1) n
  rw [lucasU_one_neg_one, lucasU_one_neg_one, lucasV_one_neg_one] at h
  have h' : ((Nat.fib (2 * n) : ℕ) : ℤ) = ((lucas n * Nat.fib n : ℕ) : ℤ) := by
    push_cast
    linear_combination h
  exact_mod_cast h'.symm

-- `jacobsthal_mul_jacobsthalCompanion : J n * j n = J (2n)` is `lucasU_two_mul` at `(1, -2)`.
-- The same theorem as the line above, at a different `(P, Q)`.
example (n : ℕ) : jacobsthal n * jacobsthalCompanion n = jacobsthal (2 * n) := by
  have h := lucasU_two_mul (1 : ℤ) (-2) n
  rw [lucasU_one_neg_two, lucasU_one_neg_two, lucasV_one_neg_two] at h
  have h' : ((jacobsthal (2 * n) : ℕ) : ℤ)
      = ((jacobsthal n * jacobsthalCompanion n : ℕ) : ℤ) := by
    push_cast
    linear_combination h
  exact_mod_cast h'.symm

-- `lucas_sq_sub_five_mul_fib_sq : L n ^ 2 - 5 * F n ^ 2 = 4 * (-1) ^ n` is the discriminant
-- identity at `(1, -1)`, where `D = 1 - 4 * (-1) = 5`.
example (n : ℕ) :
    (lucas n : ℤ) ^ 2 - 5 * (Nat.fib n : ℤ) ^ 2 = 4 * (-1 : ℤ) ^ n := by
  have h := lucasV_sq_sub_discr_mul_lucasU_sq (1 : ℤ) (-1) n
  rw [lucasV_one_neg_one, lucasU_one_neg_one, lucasDiscr_def] at h
  norm_num at h
  linear_combination h

-- `pellHalfCompanion_sq_sub_two_mul_sq : H n ^ 2 - 2 * P (n+1) ^ 2 = (-1) ^ (n+1)` is the
-- *same* discriminant identity at `(2, -1)`, where `D = 8`, divided by `4`.
example (n : ℕ) :
    (pellHalfCompanion n : ℤ) ^ 2 - 2 * (pellNumber (n + 1) : ℤ) ^ 2 = (-1 : ℤ) ^ (n + 1) := by
  have h := lucasV_sq_sub_discr_mul_lucasU_sq (2 : ℤ) (-1) (n + 1)
  rw [lucasV_two_neg_one_succ, lucasU_two_neg_one, lucasDiscr_def] at h
  norm_num at h
  have h4 : 4 * ((pellHalfCompanion n : ℤ) ^ 2 - 2 * (pellNumber (n + 1) : ℤ) ^ 2)
      = 4 * (-1 : ℤ) ^ (n + 1) := by linear_combination h
  linarith

-- `lucas_two_mul : L (2n) = L n ^ 2 - 2 * (-1) ^ n` is `lucasV_two_mul` at `(1, -1)`.
example (n : ℕ) : (lucas (2 * n) : ℤ) = (lucas n : ℤ) ^ 2 - 2 * (-1 : ℤ) ^ n := by
  have h := lucasV_two_mul (1 : ℤ) (-1) n
  rw [lucasV_one_neg_one, lucasV_one_neg_one] at h
  exact h

-- `three_mul_jacobsthal : 3 * J n = 2 ^ n - (-1) ^ n` is `lucasU_of_roots` at `α = 2, β = -1`,
-- where the factor `α - β` is `3`.
example (n : ℕ) : 3 * (jacobsthal n : ℤ) = 2 ^ n - (-1) ^ n := by
  have h := lucasU_of_roots (2 : ℤ) (-1) n
  rw [show (2 : ℤ) + -1 = 1 by norm_num, show (2 : ℤ) * -1 = -2 by norm_num,
    lucasU_one_neg_two] at h
  linear_combination h

-- `jacobsthalCompanion_eq : j n = 2 ^ n + (-1) ^ n` is `lucasV_of_roots` at the same roots.
example (n : ℕ) : (jacobsthalCompanion n : ℤ) = 2 ^ n + (-1) ^ n := by
  have h := lucasV_of_roots (2 : ℤ) (-1) n
  rw [show (2 : ℤ) + -1 = 1 by norm_num, show (2 : ℤ) * -1 = -2 by norm_num,
    lucasV_one_neg_two] at h
  linear_combination h

-- `coe_lucas_eq : (L n : ℝ) = φ ^ n + ψ ^ n` is `lucasV_of_roots` over `ℝ` at `α = φ, β = ψ`,
-- using Mathlib's `φ + ψ = 1` and `φ * ψ = -1`.  The ring changed; the theorem did not.
example (n : ℕ) :
    (lucas n : ℝ) = Real.goldenRatio ^ n + Real.goldenConj ^ n := by
  have h := lucasV_of_roots Real.goldenRatio Real.goldenConj n
  rw [Real.goldenRatio_add_goldenConj, Real.goldenRatio_mul_goldenConj,
    lucasV_one_neg_one ℝ] at h
  exact h

-- Mathlib's `Real.coe_fib_eq : (F n : ℝ) = (φ ^ n - ψ ^ n) / √5` is `lucasU_of_roots` at the
-- same two roots, with `φ - ψ = √5`.
example (n : ℕ) :
    Real.sqrt 5 * (Nat.fib n : ℝ) = Real.goldenRatio ^ n - Real.goldenConj ^ n := by
  have h := lucasU_of_roots Real.goldenRatio Real.goldenConj n
  rw [Real.goldenRatio_add_goldenConj, Real.goldenRatio_mul_goldenConj,
    Real.goldenRatio_sub_goldenConj, lucasU_one_neg_one ℝ] at h
  exact h

-- `companionMatrix_pow_trace : (M ^ n).trace = L (2n)` is `lucasCompanion_pow_succ_trace` at
-- `(3, 1)`, for `n ≥ 1`.
example (n : ℕ) :
    (Geometry.companionMatrix ^ (n + 1)).trace = (lucas (2 * (n + 1)) : ℝ) := by
  rw [companionMatrix_eq_lucasCompanion, lucasCompanion_pow_succ_trace, lucasV_three_one ℝ]

/-! ### `GoldenRatio/Characterisations.lean` is the `(1, -1)` case

That module was written before the general theory and sits in a directory the number-theory
modules never import, so it independently develops what `lucasU`/`lucasV` at `(P,Q) = (1,-1)`
already give.  The identifications are recorded here rather than by editing it, so its own
narrative stays intact.

The bridge is Vieta: `vieta_sum` and `vieta_prod` say exactly that `φ` and `ψ` are the root pair
with `P = φ + ψ = 1` and `Q = φψ = -1`. -/

/-- **Binet for the Lucas numbers is the `(1,-1)` instance of `lucasV_of_roots`.**

`Lucas.lean` proves `coe_lucas_eq` through Mathlib's `LinearRecurrence.eq_iff_eqOn_range_order`,
mirroring Mathlib's own `Real.coe_fib_eq'`.  Given the general root formula and Vieta, it is
three lines and no induction. -/
example (n : ℕ) :
    (lucas n : ℝ) = Real.goldenRatio ^ n + Real.goldenConj ^ n := by
  have h := lucasV_of_roots Real.goldenRatio Real.goldenConj n
  rw [GoldenRatio.vieta_sum, GoldenRatio.vieta_prod] at h
  rw [← h, lucasV_one_neg_one ℝ]

/-- **`fibMatrix` is the `(1,-1)` companion matrix, conjugated by the swap.**

`GoldenRatio.fibMatrix` is `!![1, 1; 1, 0]` and `lucasCompanion 1 (-1)` is `!![0, 1; 1, 1]`.  They
are not equal — they differ by reversing the basis order — but they are similar, and the swap
matrix is its own inverse, so this single equation carries the whole relationship. -/
theorem swap_mul_lucasCompanion_mul_swap :
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) * lucasCompanion (1 : ℝ) (-1) * !![0, 1; 1, 0]
      = GoldenRatio.fibMatrix := by
  rw [GoldenRatio.fibMatrix, lucasCompanion]
  norm_num [Matrix.mul_fin_two]

-- The invariants therefore agree, which is what `fibMatrix_trace` and `fibMatrix_det` record:
-- trace is `P = 1` and determinant is `Q = -1`.
example : GoldenRatio.fibMatrix.trace = (lucasCompanion (1 : ℝ) (-1)).trace := by
  rw [GoldenRatio.fibMatrix_trace]
  simp [lucasCompanion, Matrix.trace_fin_two]

example : GoldenRatio.fibMatrix.det = (lucasCompanion (1 : ℝ) (-1)).det := by
  rw [GoldenRatio.fibMatrix_det]
  simp [lucasCompanion, Matrix.det_fin_two]

-- And `fibMatrix_det_sub_smul` is the characteristic polynomial `x^2 - P x + Q` at `(1, -1)`.
example (x : ℝ) :
    (GoldenRatio.fibMatrix - x • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = x ^ 2 - 1 * x + (-1) := by
  rw [GoldenRatio.fibMatrix_det_sub_smul]; ring

end ClassicalLean
