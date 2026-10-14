/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Linear differential equations: `exp (t A) x₀` is the one solution of `x' = A x`

For a real square matrix `A` and a starting vector `x₀`:

* `hasDerivAt_exp_smul_mulVec` — `t ↦ exp (t A) x₀` has derivative `A (exp (t A) x₀)` at every
  `t`: it solves `x' = A x`, with value `x₀` at `t = 0`.
* `eq_exp_smul_mulVec` — and it is the only solution: any `x` with `x' = A x` at every time is
  `x t = exp (t A) (x 0)` for every `t`, in the past as well as the future.

Here `exp` is Mathlib's `NormedSpace.exp`, the sum `∑ (t A)ᵏ / k!`. The statements do not depend
on a choice of matrix norm; one (the `ℓ∞` operator norm) is chosen inside the proofs only, as in
Mathlib's `Analysis/Normed/Algebra/MatrixExponential`.

This is the standard fact about linear systems found in differential-equations textbooks; no
theorem number is cited, none was checked.

## Hypotheses

`eq_exp_smul_mulVec` has one hypothesis, that `x` solves `x' = A x` at every time; without it the
conclusion fails for `A = [1]` and `x` constant `1`, since `exp 1 ≠ 1` (order LEAN-20's checks,
check C30). The checks also verify the derivative exactly for 100 nilpotent matrices, whose
exponential is a finite sum, and compare a numerical solution with `exp (t A) x₀` for one diagonal
matrix (floats).

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-20, `grep -rniE` over Mathlib): a derivative or
an integral curve of `exp (t A)` applied to a vector, 0. The plan's row names
`hasDerivAt_exp_smul_const` and `ODE_solution_unique`; the forms used are the neighbouring
`hasDerivAt_exp_smul_const'` and `ODE_solution_unique_univ`. The name `eq_exp_smul_mulVec` is the
order's (review r30 notes Mathlib would add `_of_hasDerivAt`). What this file adds is that
application; it uses Mathlib's `hasDerivAt_exp_smul_const'` (the derivative of `t ↦ exp (t A)`) and
`ODE_solution_unique_univ` (uniqueness for a Lipschitz right-hand side), and proves neither again.
-/

open Matrix

namespace ClassicalLean.Analysis

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **`exp (t A) x₀` solves `x' = A x`.** Mathlib's derivative of `t ↦ exp (t A)`, which is
`A exp (t A)`, applied to the vector `x₀` (a linear operation on matrices). -/
theorem hasDerivAt_exp_smul_mulVec (A : Matrix n n ℝ) (x₀ : n → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ NormedSpace.exp (s • A) *ᵥ x₀)
      (A *ᵥ (NormedSpace.exp (t • A) *ᵥ x₀)) t := by
  let _ : NormedRing (Matrix n n ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix n n ℝ) := Matrix.linftyOpNormedAlgebra
  have h := (LinearMap.toContinuousLinearMap ((Matrix.mulVecBilin ℝ ℝ).flip x₀)).hasFDerivAt
    |>.comp_hasDerivAt t (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t)
  rw [Matrix.mulVec_mulVec]
  exact h

/-- **It is the only solution.** If `x' = A x` at every time, then `x t = exp (t A) (x 0)` for
every `t`. The right-hand side `y ↦ A y` is Lipschitz, so Mathlib's `ODE_solution_unique_univ`
applies, with `exp (t A) (x 0)` as the other solution (`hasDerivAt_exp_smul_mulVec`). -/
theorem eq_exp_smul_mulVec {A : Matrix n n ℝ} {x : ℝ → n → ℝ}
    (hx : ∀ t, HasDerivAt x (A *ᵥ x t) t) (t : ℝ) :
    x t = NormedSpace.exp (t • A) *ᵥ x 0 := by
  let _ : NormedAddCommGroup (Matrix n n ℝ) := Matrix.linftyOpNormedAddCommGroup
  have hlip : LipschitzWith ‖A‖₊ fun y : n → ℝ ↦ A *ᵥ y := by
    refine LipschitzWith.of_dist_le_mul fun y z ↦ ?_
    rw [dist_eq_norm, dist_eq_norm, ← Matrix.mulVec_sub, coe_nnnorm]
    exact Matrix.linfty_opNorm_mulVec A (y - z)
  have h := ODE_solution_unique_univ (v := fun _ y ↦ A *ᵥ y) (s := fun _ ↦ Set.univ)
    (t₀ := 0) (fun _ ↦ hlip.lipschitzOnWith) (fun t ↦ ⟨hx t, Set.mem_univ _⟩)
    (fun t ↦ ⟨hasDerivAt_exp_smul_mulVec A (x 0) t, Set.mem_univ _⟩)
    (by simp [NormedSpace.exp_zero])
  exact congrFun h t

end ClassicalLean.Analysis

open Matrix in
/-- The hypotheses of `eq_exp_smul_mulVec` hold together: for the rotation generator
`A = [[0, 1], [−1, 0]]` on `ℝ²`, the curve `x t = exp (t A) (1, 0)` has derivative `A x t` at every
`t` (the module's `hasDerivAt_exp_smul_mulVec`); `t = 1`. -/
example := ClassicalLean.Analysis.eq_exp_smul_mulVec (n := Fin 2) (A := !![0, 1; -1, 0])
  (x := fun s ↦ NormedSpace.exp (s • !![0, 1; -1, 0]) *ᵥ ![1, 0])
  (fun t ↦ ClassicalLean.Analysis.hasDerivAt_exp_smul_mulVec _ _ t) (t := 1)
