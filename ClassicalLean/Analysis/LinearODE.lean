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
* `quadForm_le_exp_mul` — order LEAN-32, item 108, **a Lyapunov bound**: if
  `v ⬝ᵥ ((Aᵀ * P + P * A + (2 * c) • P) *ᵥ v) ≤ 0` for every `v`, then every solution of `x' = A x`
  has `x t ⬝ᵥ (P *ᵥ x t) ≤ exp (−2 c t) (x 0 ⬝ᵥ (P *ᵥ x 0))` for `t ≥ 0`.

Here `exp` is Mathlib's `NormedSpace.exp`, the sum `∑ (t A)ᵏ / k!`. The statements do not depend
on a choice of matrix norm; one (the `ℓ∞` operator norm) is chosen inside the proofs only, as in
Mathlib's `Analysis/Normed/Algebra/MatrixExponential`.

These are standard facts about linear systems found in differential-equations textbooks; no
theorem number is cited, none was checked.

## Hypotheses

`eq_exp_smul_mulVec` has one hypothesis, that `x` solves `x' = A x` at every time; without it the
conclusion fails for `A = [1]` and `x` constant `1`, since `exp 1 ≠ 1` (order LEAN-20's checks,
check C30). The checks also verify the derivative exactly for 100 nilpotent matrices, whose
exponential is a finite sum, and compare a numerical solution with `exp (t A) x₀` for one diagonal
matrix (floats).

`quadForm_le_exp_mul` (item 108) is wider than the plan's row, which asks `P` positive definite
and `Aᵀ P + P A + 2 c P` negative semidefinite: it asks neither positive definiteness nor symmetry
of `P`, only the form inequality `v ⬝ᵥ (M *ᵥ v) ≤ 0` for every `v`, which is what "negative
semidefinite" means for a matrix that need not be symmetric. The derivative of `x ⬝ᵥ (P *ᵥ x)`
along a solution is `x ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ x)` for any square `P` (by hand, order LEAN-32's
checks, line `108.P_free`), so the bound needs nothing more. Positive definiteness is what makes
`x ⬝ᵥ (P *ᵥ x)` a Lyapunov function, nonnegative and zero only at `0`, so that the bound says the
solution decays to `0` when `c > 0`. The hypothesis `hx` asks `x' = A x` at every real time, as
`eq_exp_smul_mulVec` does, though only the times from `0` to `t` matter; any solution on `[0, ∞)`
of a linear system is `exp (t A) x₀` there and extends to every time. Each hypothesis is needed,
by hand (order LEAN-32's checks): `t ≥ 0`, with `A = 0`, `P = 1`, `c = -1` and `x` constant of
length `1`, the claim at `t = -1` reads `1 ≤ exp (-2)` (`108.drop.t`); the form inequality, with
`A = P = 1`, `c = 0` and `x t = exp t • v`, `|v| = 1`, the left side at `t = 1` is `e²`, above
`1` (`108.drop.hL`); the equation, with `x t = t • v`, `|v| = 1`, `A = 0`, `P = 1`, `c = 0`, the
left side at `t = 1` is `1`, above `0` (`108.drop.hx`).

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

omit [DecidableEq n] in
/-- **A Lyapunov bound for `x' = A x`** (order LEAN-32, item 108): if
`v ⬝ᵥ ((Aᵀ * P + P * A + (2 * c) • P) *ᵥ v) ≤ 0` for every `v`, then along every solution
`x t ⬝ᵥ (P *ᵥ x t) ≤ exp (−2 c t) (x 0 ⬝ᵥ (P *ᵥ x 0))` for `t ≥ 0`. `P` need be neither positive
definite nor symmetric. The derivative of `exp (2 c s) (x s ⬝ᵥ (P *ᵥ x s))` is `exp (2 c s)` times
the left side of the hypothesis at `x s`, so the product does not increase. -/
theorem quadForm_le_exp_mul {A P : Matrix n n ℝ} {c : ℝ}
    (hL : ∀ v : n → ℝ, v ⬝ᵥ ((Aᵀ * P + P * A + (2 * c) • P) *ᵥ v) ≤ 0)
    {x : ℝ → n → ℝ} (hx : ∀ t, HasDerivAt x (A *ᵥ x t) t) {t : ℝ} (ht : 0 ≤ t) :
    x t ⬝ᵥ (P *ᵥ x t) ≤ Real.exp (-(2 * c * t)) * (x 0 ⬝ᵥ (P *ᵥ x 0)) := by
  have hPx : ∀ s, HasDerivAt (fun r ↦ P *ᵥ x r) (P *ᵥ (A *ᵥ x s)) s := fun s ↦
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin P)).hasFDerivAt.comp_hasDerivAt s (hx s)
  have hV : ∀ s, HasDerivAt (fun r ↦ x r ⬝ᵥ (P *ᵥ x r))
      (x s ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ x s)) s := by
    intro s
    have h := HasDerivAt.sum (u := Finset.univ) fun i _ ↦
      (hasDerivAt_pi.1 (hx s) i).mul (hasDerivAt_pi.1 (hPx s) i)
    have he : x s ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ x s)
        = ∑ i ∈ Finset.univ, ((A *ᵥ x s) i * (P *ᵥ x s) i + x s i * (P *ᵥ (A *ᵥ x s)) i) := by
      rw [Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec (x s) Aᵀ, Matrix.vecMul_transpose, Finset.sum_add_distrib]
      rfl
    rw [he]
    convert h using 1
    ext r
    simp [dotProduct]
  have hg : ∀ s, HasDerivAt (fun r ↦ Real.exp (2 * c * r) * (x r ⬝ᵥ (P *ᵥ x r)))
      (Real.exp (2 * c * s) * (x s ⬝ᵥ ((Aᵀ * P + P * A + (2 * c) • P) *ᵥ x s))) s := by
    intro s
    have h1 : HasDerivAt (fun r ↦ Real.exp (2 * c * r)) (Real.exp (2 * c * s) * (2 * c)) s := by
      simpa using ((hasDerivAt_id s).const_mul (2 * c)).exp
    convert h1.mul (hV s) using 1
    rw [Matrix.add_mulVec (Aᵀ * P + P * A) ((2 * c) • P), dotProduct_add, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul]
    ring
  have hanti : Antitone fun r ↦ Real.exp (2 * c * r) * (x r ⬝ᵥ (P *ᵥ x r)) :=
    antitone_of_deriv_nonpos (fun s ↦ (hg s).differentiableAt) fun s ↦ by
      rw [(hg s).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (hL (x s))
  have h0 := hanti ht
  simp only [mul_zero, Real.exp_zero, one_mul] at h0
  calc x t ⬝ᵥ (P *ᵥ x t)
      = Real.exp (-(2 * c * t)) * (Real.exp (2 * c * t) * (x t ⬝ᵥ (P *ᵥ x t))) := by
        rw [Real.exp_neg, inv_mul_cancel_left₀ (Real.exp_ne_zero _)]
    _ ≤ Real.exp (-(2 * c * t)) * (x 0 ⬝ᵥ (P *ᵥ x 0)) :=
        mul_le_mul_of_nonneg_left h0 (Real.exp_pos _).le

end ClassicalLean.Analysis

open Matrix in
/-- The hypotheses of `eq_exp_smul_mulVec` hold together: for the rotation generator
`A = [[0, 1], [−1, 0]]` on `ℝ²`, the curve `x t = exp (t A) (1, 0)` has derivative `A x t` at every
`t` (the module's `hasDerivAt_exp_smul_mulVec`); `t = 1`. -/
example := ClassicalLean.Analysis.eq_exp_smul_mulVec (n := Fin 2) (A := !![0, 1; -1, 0])
  (x := fun s ↦ NormedSpace.exp (s • !![0, 1; -1, 0]) *ᵥ ![1, 0])
  (fun t ↦ ClassicalLean.Analysis.hasDerivAt_exp_smul_mulVec _ _ t) (t := 1)

open Matrix in
/-- The hypotheses of `quadForm_le_exp_mul` hold together: on `ℝ²`, the decaying rotation
`A = [[−1, 1], [−1, −1]]` (not symmetric), `P = 1` and `c = 1/2`, so that
`Aᵀ * P + P * A + (2 * c) • P = −1` and the form is `−(v₀² + v₁²) ≤ 0`; the solution
`x t = exp (t A) (1, 0)` (the module's `hasDerivAt_exp_smul_mulVec`); `t = 1`. -/
example := ClassicalLean.Analysis.quadForm_le_exp_mul (n := Fin 2) (A := !![-1, 1; -1, -1])
  (P := 1) (c := 1 / 2)
  (fun v ↦ by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply]
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)])
  (x := fun s ↦ NormedSpace.exp (s • !![-1, 1; -1, -1]) *ᵥ ![1, 0])
  (fun t ↦ ClassicalLean.Analysis.hasDerivAt_exp_smul_mulVec _ _ t) (t := 1) zero_le_one
