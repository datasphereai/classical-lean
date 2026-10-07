/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith
import ClassicalLean.Geometry.Helix
import ClassicalLean.NumberTheory.Lucas

/-!
# The even-index Lucas numbers are the traces of the powers of a companion matrix

`ClassicalLean/Geometry/Helix.lean` builds the companion matrix `M = !![0, -1; 1, 3]` of the
quadratic `t ^ 2 - 3 * t + 1` and shows its two real roots are `φ ^ 2` and `(φ ^ 2)⁻¹ = ψ ^ 2`.
`ClassicalLean/NumberTheory/Lucas.lean` shows the even-index Lucas numbers obey
`L (2 (n + 2)) = 3 * L (2 (n + 1)) - L (2n)`.  **These are the same recurrence**, and this file
is the theorem that says so, in the form that carries content rather than resemblance:

`(M ^ n).trace = L (2n)`.

Both files previously stated the connection only in prose.  Nothing here is new mathematics;
what is new is that the two modules are now joined by a proved statement instead of a remark.

## Main results

* `companionMatrix_pow_add_two` : the powers of `M` obey the same three-term recurrence,
  `M ^ (n + 2) = 3 • M ^ (n + 1) - M ^ n`.  This is Cayley–Hamilton
  (`Geometry.companionMatrix_sq_sub`) multiplied through by `M ^ n`, and it is what makes the
  induction below match `lucas_two_mul_recurrence` term for term.
* `companionMatrix_pow_trace` : `(M ^ n).trace = L (2n)`.
* `companionMatrix_pow_det` : `(M ^ n).det = 1`, so every power of `M` lies in `SL₂(ℝ)`.
* `companionMatrix_pow_det_sub_smul` : the two together, as the characteristic polynomial of
  `M ^ n`: `det (M ^ n - x · I) = x ^ 2 - L (2n) * x + 1`.  The even-index Lucas numbers are
  exactly the traces that appear here, and the constant term never moves.
* `companionMatrix_pow_trace_eq_goldenRatio_sq_pow` : the eigenvalue reading,
  `(M ^ n).trace = (φ ^ 2) ^ n + (ψ ^ 2) ^ n`.  This is `companionMatrix_pow_trace` composed
  with `coe_lucas_two_mul`, that is with Binet's formula; it is the sense in which `L (2n)` is
  the `n`-th power sum of the two roots.
* `companionMatrix_vecMul_lucas` and `companionMatrix_mulVec_lucas` : the orbit statement, in
  both conventions.

## Which vector is the orbit

Saying "the even-index subsequence is the orbit of `M`" needs two choices made, and the two
theorems above make them differently:

* **Row action** `Matrix.vecMul`, `v ↦ v M`.  The seed is the consecutive pair
  `(L (2n), L (2n + 2))`, and it advances to `(L (2n + 2), L (2n + 4))`.
* **Column action** `Matrix.mulVec`, `v ↦ M v`.  `M` sends `(a, b)` to `(-b, a + 3b)`, so the
  seed that advances is the *signed* pair `(L (2n), -L (2n + 2))`, going to
  `(L (2n + 2), -L (2n + 4))`.

Neither action is the wrong one; the two differ by `Mᵀ`, since `v ᵥ* A = Aᵀ *ᵥ v`
(Mathlib's `Matrix.mulVec_transpose`), and `M` is not symmetric.  What is wrong is carrying the
*unsigned* consecutive pair across to the column action: `M *ᵥ (L 0, L 2) = (-3, 11)`, not
`(L 2, L 4) = (3, 7)`.  That is the final spot check in this file, and it is a control on the
seed, not on the action.

The trace statements are indifferent to all of this, since `M` and `Mᵀ` have the same trace and
the same determinant.

## Naming

`M` is `ClassicalLean.Geometry.companionMatrix`; it keeps its name and its home.  The direction
of the dependency is `NumberTheory → Geometry`, because the matrix is the older object here and
the theorem is a statement about the Lucas numbers.
-/

namespace ClassicalLean

open Geometry

/-- Cayley–Hamilton in solved form: `M ^ 2 = 3 • M - I`.  This is
`Geometry.companionMatrix_sq_sub` rearranged, and it is proved the same way — by the four
entries — rather than by moving terms across the earlier statement. -/
private theorem companionMatrix_sq_eq :
    companionMatrix ^ 2 = (3 : ℝ) • companionMatrix - 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [companionMatrix, pow_two]
  ring

/-- **The powers of `M` obey the even-index Lucas recurrence.**
`M ^ (n + 2) = 3 • M ^ (n + 1) - M ^ n`, for every `n`.

The proof is `companionMatrix_sq_eq` multiplied on the left by `M ^ n`. It is the matrix
statement of which `lucas_two_mul_recurrence` is the trace. -/
theorem companionMatrix_pow_add_two (n : ℕ) :
    companionMatrix ^ (n + 2) = (3 : ℝ) • companionMatrix ^ (n + 1) - companionMatrix ^ n := by
  calc companionMatrix ^ (n + 2)
      = companionMatrix ^ n * companionMatrix ^ 2 := by rw [pow_add]
    _ = companionMatrix ^ n * ((3 : ℝ) • companionMatrix - 1) := by rw [companionMatrix_sq_eq]
    _ = (3 : ℝ) • (companionMatrix ^ n * companionMatrix) - companionMatrix ^ n := by
        rw [mul_sub, mul_one, mul_smul_comm]
    _ = (3 : ℝ) • companionMatrix ^ (n + 1) - companionMatrix ^ n := by rw [← pow_succ]

/-- **The even-index Lucas numbers are the traces of the powers of `M`**:
`(M ^ n).trace = L (2n)`.

Two-step induction.  The base cases are `trace I = 2 = L 0` and `trace M = 3 = L 2`; the step is
`companionMatrix_pow_add_two` under the linearity of the trace, matched against
`lucas_two_mul_recurrence`.  Binet is not used: this is an identity between two integer
sequences that satisfy the same recurrence from the same two initial values. -/
theorem companionMatrix_pow_trace (n : ℕ) :
    (companionMatrix ^ n).trace = (lucas (2 * n) : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [companionMatrix_trace]
  | more n ih1 ih2 =>
    have hrec : (lucas (2 * (n + 2)) : ℝ)
        = 3 * (lucas (2 * (n + 1)) : ℝ) - (lucas (2 * n) : ℝ) := by
      have h := lucas_two_mul_recurrence n
      have h' : ((lucas (2 * (n + 2)) : ℤ) : ℝ)
          = ((3 * (lucas (2 * (n + 1)) : ℤ) - (lucas (2 * n) : ℤ) : ℤ) : ℝ) := by rw [h]
      push_cast at h'
      linarith
    rw [companionMatrix_pow_add_two, Matrix.trace_sub, Matrix.trace_smul, ih1, ih2, hrec,
      smul_eq_mul]

/-- Every power of `M` has determinant `1`: `(M ^ n).det = 1`, from `Matrix.det_pow` and
`Geometry.companionMatrix_det`.  With `companionMatrix_pow_trace` this is the pair of Vieta
data for `M ^ n`. -/
theorem companionMatrix_pow_det (n : ℕ) : (companionMatrix ^ n).det = 1 := by
  rw [Matrix.det_pow, companionMatrix_det, one_pow]

/-- For a `2 × 2` matrix, `det (A - x · I) = x ^ 2 - (trace A) * x + det A`.

Mathlib's `Matrix.charpoly_fin_two` is the polynomial form of this,
`A.charpoly = X ^ 2 - C A.trace * X + C A.det`; this is its evaluation at a real `x`, stated
directly so that no `Polynomial.eval` and no `charpoly` appear in the statement below — which
is the form `Geometry.companionMatrix_det_sub_smul` already uses, and the form the root-list
theorems in `Helix.lean` consume.

It is `private` and it is used once, by `companionMatrix_pow_det_sub_smul`.
`Geometry.companionMatrix_det_sub_smul` does not use it and is not restated in terms of it:
`Helix.lean` does not import this module, and the direction of the dependency is not going to be
reversed for a lemma. A general home for it would be a linear-algebra module this library does
not have. -/
private theorem det_sub_smul_fin_two (A : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) :
    (A - x • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = x ^ 2 - A.trace * x + A.det := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.sub_apply, Matrix.smul_apply]
  ring

/-- **The characteristic polynomial of `M ^ n` is `t ^ 2 - L (2n) * t + 1`**:
`det (M ^ n - x · I) = x ^ 2 - L (2n) * x + 1` for every real `x`.

This is `companionMatrix_pow_trace` and `companionMatrix_pow_det` read through
`det_sub_smul_fin_two`.  At `n = 1` it is `Geometry.companionMatrix_det_sub_smul`, since
`L 2 = 3`; that instance is not derived from this one, and this one is not derived from it. -/
theorem companionMatrix_pow_det_sub_smul (n : ℕ) (x : ℝ) :
    (companionMatrix ^ n - x • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det
      = x ^ 2 - (lucas (2 * n) : ℝ) * x + 1 := by
  rw [det_sub_smul_fin_two, companionMatrix_pow_trace, companionMatrix_pow_det]

/-- **The eigenvalue reading of the trace**: `(M ^ n).trace = (φ ^ 2) ^ n + (ψ ^ 2) ^ n`.

`Geometry.companionMatrix_det_sub_smul_eq_zero_iff` identifies the two real roots of
`det (M - x · I)` as `φ ^ 2` and `(φ ^ 2)⁻¹ = ψ ^ 2`.  This theorem says that the trace of the
`n`-th power is the `n`-th power sum of those two numbers — the classical statement, here
obtained by composing `companionMatrix_pow_trace` with Binet (`coe_lucas_two_mul`) rather than
by diagonalising `M`.  No diagonalisation, eigenbasis or spectral theorem appears anywhere in
this file. -/
theorem companionMatrix_pow_trace_eq_goldenRatio_sq_pow (n : ℕ) :
    (companionMatrix ^ n).trace
      = (Real.goldenRatio ^ 2) ^ n + (Real.goldenConj ^ 2) ^ n := by
  rw [companionMatrix_pow_trace, coe_lucas_two_mul]

/-- **The orbit statement, row action.** `M` moves the row vector of two consecutive even-index
Lucas numbers to the next one: `(L (2n), L (2 (n + 1))) ᵥ* M = (L (2 (n + 1)), L (2 (n + 2)))`.

This is `Matrix.vecMul`. The column action `Matrix.mulVec` has its own orbit, on the signed pair
— `companionMatrix_mulVec_lucas` — and the two differ by `Mᵀ`. -/
theorem companionMatrix_vecMul_lucas (n : ℕ) :
    Matrix.vecMul ![(lucas (2 * n) : ℝ), (lucas (2 * (n + 1)) : ℝ)] companionMatrix
      = ![(lucas (2 * (n + 1)) : ℝ), (lucas (2 * (n + 2)) : ℝ)] := by
  have hrec : (lucas (2 * (n + 2)) : ℝ)
      = 3 * (lucas (2 * (n + 1)) : ℝ) - (lucas (2 * n) : ℝ) := by
    have h := lucas_two_mul_recurrence n
    have h' : ((lucas (2 * (n + 2)) : ℤ) : ℝ)
        = ((3 * (lucas (2 * (n + 1)) : ℤ) - (lucas (2 * n) : ℤ) : ℤ) : ℝ) := by rw [h]
    push_cast at h'
    linarith
  funext i
  fin_cases i
  · simp [companionMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · simp [companionMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    linarith

/-- **The orbit statement, column action.** `M *ᵥ (L (2n), -L (2 (n + 1)))
= (L (2 (n + 1)), -L (2 (n + 2)))`.

The column action advances the same subsequence, on the pair carrying an alternating sign in its
second entry: `M` sends `(a, b)` to `(-b, a + 3b)`, and `a + 3b` is `-(3 L (2 (n + 1)) - L (2n))`
exactly when `b = -L (2 (n + 1))`. Recorded so that the module states both conventions rather than
declaring one of them wrong; the unsigned pair is what fails here, and that is the final spot
check. -/
theorem companionMatrix_mulVec_lucas (n : ℕ) :
    companionMatrix.mulVec ![(lucas (2 * n) : ℝ), -(lucas (2 * (n + 1)) : ℝ)]
      = ![(lucas (2 * (n + 1)) : ℝ), -(lucas (2 * (n + 2)) : ℝ)] := by
  have hrec : (lucas (2 * (n + 2)) : ℝ)
      = 3 * (lucas (2 * (n + 1)) : ℝ) - (lucas (2 * n) : ℝ) := by
    have h := lucas_two_mul_recurrence n
    have h' : ((lucas (2 * (n + 2)) : ℤ) : ℝ)
        = ((3 * (lucas (2 * (n + 1)) : ℤ) - (lucas (2 * n) : ℤ) : ℤ) : ℝ) := by rw [h]
    push_cast at h'
    linarith
  funext i
  fin_cases i
  · simp [companionMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [companionMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linarith

/-! ### Spot checks -/

-- `M ^ 2 = !![-1, -3; 3, 8]` has trace `7`, and `L 4 = 7`.
example : (companionMatrix ^ 2).trace = 7 := by
  have h := companionMatrix_pow_trace 2
  norm_num [show lucas 4 = 7 from by decide] at h
  exact h

-- `M ^ 3 = !![-3, -8; 8, 21]` has trace `18`, and `L 6 = 18`.
example : (companionMatrix ^ 3).trace = 18 := by
  have h := companionMatrix_pow_trace 3
  norm_num [show lucas 6 = 18 from by decide] at h
  exact h

-- The control on the seed for §"Which vector is the orbit": carried to the column action, the
-- *unsigned* consecutive pair does not advance. At `n = 0` the first entry alone already
-- fails, `-3 ≠ 3`. The signed pair does advance — that is `companionMatrix_mulVec_lucas`.
example :
    companionMatrix.mulVec ![(lucas 0 : ℝ), (lucas 2 : ℝ)] ≠ ![(lucas 2 : ℝ), (lucas 4 : ℝ)] := by
  intro h
  have h0 := congrFun h 0
  norm_num [companionMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0

end ClassicalLean
