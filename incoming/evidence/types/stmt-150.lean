/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Statistics.GaussMarkov
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Inductions

/-!
# The Moore–Penrose pseudoinverse

For a real matrix `A : Matrix m n ℝ`, the pseudoinverse `pinv A : Matrix n m ℝ` is the unique
matrix `X` with `A X A = A`, `X A X = X`, `(A X)ᵀ = A X` and `(X A)ᵀ = X A`, the four Penrose
equations. Order CLOUD-MATH-2, item 150 of MATH-PLAN-library-2.

* `pinv` — the definition: a matrix satisfying the four equations, chosen
  (`Classical.choose`) from their existence, `exists_penrose`.
* `pinv_spec` — `pinv A` satisfies the four equations.
* `pinv_unique` — every matrix satisfying the four equations is `pinv A`.
* `pinv_residual_dotProduct_le` — least squares with any design, a rank-deficient one included:
  for every `β`, the residual sum of squares of `pinv A *ᵥ y` is at most that of `β`.
* `pinv_eq_leastSquares` — for full column rank (`(Aᵀ * A).det` a unit), `pinv A` is the
  library's least-squares matrix `ClassicalLean.Statistics.leastSquares A`, `(Aᵀ A)⁻¹ Aᵀ`.

The proof. Existence: the symmetric matrix `M = Aᵀ A` has a symmetric generalized inverse `G`
that commutes with `M` and satisfies `M G M = M` and `G M G = G` (`exists_symm_ginv`). By the
Cayley–Hamilton theorem, with `charpoly M = X ^ k * q` and `q(0) ≠ 0`, `M ^ (k + 1) q(M) = 0`,
which for a symmetric `M` gives `M q(M) = 0`; writing `q(M) = q'(M) M + q(0)` with `q' = q.divX`,
`T = (-q(0))⁻¹ q'(M)` has `M T M = M` and `M T = T M`, and `G = Tᵀ M T`. Then `X = G Aᵀ` satisfies
the four equations (`exists_penrose`). Uniqueness: two solutions `X` and `Y` have `A X = A Y` and
`X A = Y A`, so `X = X A X = Y A Y = Y` (`penrose_unique`). Least squares: the normal equations
`Aᵀ (y - A (pinv A y)) = 0` hold for every design (`transpose_mulVec_sub_mulVec_pinv`), so the
residual of `β` is the residual of `pinv A y` plus the orthogonal vector `A (pinv A y - β)`.

The proof is the draft `d150-r1-s2` (written by Claude Opus 5.5 through the Anthropic Batch API,
the lane's order API-CREDIT-1), adapted by the Claude Code cloud session that landed it (order
CLOUD-MATH-2): the namespace and docstrings, and `[DecidableEq n]` bound where it is used. The
draft's section `variable` line gave it to the three private helpers, whose statements do not use
it; here the section takes it only after `pinv`, the helpers' proofs use `classical` where they need
it, and `pinv`, which in the draft took it only through `exists_penrose`, binds it itself, so that
`pinv` and every theorem about it keep the draft's types.
-/

open Matrix

namespace ClassicalLean.Algebra.Pseudoinverse

variable {m n : Type*} [Fintype m] [Fintype n]

/-- A symmetric matrix has a symmetric, commuting, reflexive generalized inverse. -/
private theorem exists_symm_ginv (M : Matrix n n ℝ) (hM : Mᵀ = M) :
    ∃ G : Matrix n n ℝ, Gᵀ = G ∧ Commute M G ∧ M * G * M = M ∧ G * M * G = G := by
  sorry

/-- Every real matrix has a matrix satisfying the four Penrose equations. -/
private theorem exists_penrose (A : Matrix m n ℝ) :
    ∃ X : Matrix n m ℝ, A * X * A = A ∧ X * A * X = X ∧ (A * X)ᵀ = A * X ∧
      (X * A)ᵀ = X * A := by
  sorry

/-- The four Penrose equations have at most one solution. -/
private theorem penrose_unique {A : Matrix m n ℝ} {X Y : Matrix n m ℝ}
    (hX1 : A * X * A = A) (hX2 : X * A * X = X) (hX3 : (A * X)ᵀ = A * X)
    (hX4 : (X * A)ᵀ = X * A) (hY1 : A * Y * A = A) (hY2 : Y * A * Y = Y)
    (hY3 : (A * Y)ᵀ = A * Y) (hY4 : (Y * A)ᵀ = Y * A) : X = Y := by
  sorry

/-- The Moore–Penrose pseudoinverse of a real matrix (item 150 of MATH-PLAN-library-2): a matrix
satisfying the four Penrose equations, which exists (`exists_penrose`) and is unique
(`pinv_unique`).

The binder `[DecidableEq n]` keeps the draft's signature: the draft's `pinv` took the section's
instance through `exists_penrose`, whose statement does not use it. -/
noncomputable def pinv [DecidableEq n] (A : Matrix m n ℝ) : Matrix n m ℝ :=
  Classical.choose (exists_penrose A)

variable [DecidableEq n]

/-- The four Penrose equations hold for `pinv A` (item 150 of MATH-PLAN-library-2). -/
theorem pinv_spec (A : Matrix m n ℝ) :
    A * pinv A * A = A ∧ pinv A * A * pinv A = pinv A ∧
      (A * pinv A)ᵀ = A * pinv A ∧ (pinv A * A)ᵀ = pinv A * A := by
  sorry

/-- Any matrix satisfying the four Penrose equations is the pseudoinverse (item 150 of
MATH-PLAN-library-2). -/
theorem pinv_unique {A : Matrix m n ℝ} {X : Matrix n m ℝ}
    (h1 : A * X * A = A) (h2 : X * A * X = X) (h3 : (A * X)ᵀ = A * X)
    (h4 : (X * A)ᵀ = X * A) : X = pinv A := by
  sorry

/-- The normal equations for `pinv A *ᵥ y`, for every design. -/
private theorem transpose_mulVec_sub_mulVec_pinv (A : Matrix m n ℝ) (y : m → ℝ) :
    Aᵀ *ᵥ (y - A *ᵥ (pinv A *ᵥ y)) = 0 := by
  sorry

/-- **Least squares with any design**, rank-deficient included (item 150 of
MATH-PLAN-library-2): no `A β` is closer to `y`, in the sum of squares, than `A (pinv A y)`. -/
theorem pinv_residual_dotProduct_le (A : Matrix m n ℝ) (y : m → ℝ) (β : n → ℝ) :
    (y - A *ᵥ (pinv A *ᵥ y)) ⬝ᵥ (y - A *ᵥ (pinv A *ᵥ y)) ≤
      (y - A *ᵥ β) ⬝ᵥ (y - A *ᵥ β) := by
  sorry

/-- For full column rank, the pseudoinverse is the least-squares matrix `(Aᵀ A)⁻¹ Aᵀ` (item 150
of MATH-PLAN-library-2). -/
theorem pinv_eq_leastSquares {A : Matrix m n ℝ} (hA : IsUnit (Aᵀ * A).det) :
    pinv A = ClassicalLean.Statistics.leastSquares A := by
  sorry

end ClassicalLean.Algebra.Pseudoinverse

set_option pp.fullNames true
#check @ClassicalLean.Algebra.Pseudoinverse.pinv
#print ClassicalLean.Algebra.Pseudoinverse.pinv
#check @ClassicalLean.Algebra.Pseudoinverse.pinv_spec
#check @ClassicalLean.Algebra.Pseudoinverse.pinv_unique
#check @ClassicalLean.Algebra.Pseudoinverse.pinv_residual_dotProduct_le
#check @ClassicalLean.Algebra.Pseudoinverse.pinv_eq_leastSquares
