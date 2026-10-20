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
the lane's API-CREDIT-1 work), adapted by the Claude Code cloud session that landed it (order
CLOUD-MATH-2): the namespace and docstrings, and `[DecidableEq n]` bound on `pinv` and the
declarations after it. The draft's section `variable` line gave it to three of the private helpers,
`exists_symm_ginv`, `exists_penrose` and `penrose_unique`, whose statements do not use it; here the
section takes it only after `pinv`, those helpers' proofs use `classical` where they need it, and
`pinv`, which in the draft took it only through `exists_penrose`, binds it itself, so that `pinv`
and every theorem about it keep the draft's types.
-/

open Matrix

namespace ClassicalLean.Algebra.Pseudoinverse

variable {m n : Type*} [Fintype m] [Fintype n]

/-- A symmetric matrix has a symmetric, commuting, reflexive generalized inverse. -/
private theorem exists_symm_ginv (M : Matrix n n ℝ) (hM : Mᵀ = M) :
    ∃ G : Matrix n n ℝ, Gᵀ = G ∧ Commute M G ∧ M * G * M = M ∧ G * M * G = G := by
  classical
  have hker : ∀ (j : ℕ) (W : Matrix n n ℝ), M ^ (j + 1) * W = 0 → M * W = 0 := by
    intro j
    induction j with
    | zero => intro W h; simpa using h
    | succ j ih =>
      intro W h
      have h1 : M ^ (j + 1) * (M * W) = 0 := by
        rw [← Matrix.mul_assoc, ← pow_succ]; exact h
      have h2 := ih (M * W) h1
      apply conjTranspose_mul_self_eq_zero.mp
      rw [conjTranspose_eq_transpose_of_trivial, transpose_mul, hM, Matrix.mul_assoc, h2,
        Matrix.mul_zero]
  obtain ⟨q, hq, hndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd
    M.charpoly (Matrix.charpoly_monic M).ne_zero 0
  simp only [map_zero, sub_zero] at hq hndvd
  have hc0 : q.coeff 0 ≠ 0 := fun h => hndvd (Polynomial.X_dvd_iff.mpr h)
  have hCH := Matrix.aeval_self_charpoly M
  rw [hq, map_mul, map_pow, Polynomial.aeval_X] at hCH
  obtain ⟨k, hCH'⟩ : ∃ k : ℕ, M ^ k * Polynomial.aeval M q = 0 := ⟨_, hCH⟩
  have h1 : M ^ (k + 1) * Polynomial.aeval M q = 0 := by
    rw [pow_succ', Matrix.mul_assoc, hCH', Matrix.mul_zero]
  have h2 := hker k _ h1
  have hq0 : Polynomial.aeval M q =
      Polynomial.aeval M q.divX * M + q.coeff 0 • (1 : Matrix n n ℝ) := by
    have : Polynomial.aeval M (q.divX * Polynomial.X + Polynomial.C (q.coeff 0)) =
        Polynomial.aeval M q := by rw [Polynomial.divX_mul_X_add]
    rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one] at this
    exact this.symm
  rw [hq0, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_assoc] at h2
  have h3 : M * Polynomial.aeval M q.divX * M = (-q.coeff 0) • M := by
    rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h2
  have hSc : M * Polynomial.aeval M q.divX = Polynomial.aeval M q.divX * M := by
    have : Polynomial.aeval M (Polynomial.X * q.divX) =
        Polynomial.aeval M (q.divX * Polynomial.X) := by rw [mul_comm]
    simpa only [map_mul, Polynomial.aeval_X] using this
  obtain ⟨T, hMTM, hTc⟩ : ∃ T : Matrix n n ℝ, M * T * M = M ∧ M * T = T * M :=
    ⟨(-q.coeff 0)⁻¹ • Polynomial.aeval M q.divX,
      by rw [Matrix.mul_smul, Matrix.smul_mul, h3, inv_smul_smul₀ (neg_ne_zero.mpr hc0)],
      by rw [Matrix.mul_smul, Matrix.smul_mul, hSc]⟩
  have hMTMr : M * (T * M) = M := by rw [← Matrix.mul_assoc]; exact hMTM
  have hMUM : M * Tᵀ * M = M := by
    have := congrArg transpose hMTM
    rw [transpose_mul, transpose_mul, hM, ← Matrix.mul_assoc] at this
    exact this
  have hMUMr : M * (Tᵀ * M) = M := by rw [← Matrix.mul_assoc]; exact hMUM
  have hUc : M * Tᵀ = Tᵀ * M := by
    have := congrArg transpose hTc
    rw [transpose_mul, transpose_mul, hM] at this
    exact this.symm
  have hTg : ∀ Y : Matrix n n ℝ, M * (T * (M * Y)) = M * Y := fun Y => by
    rw [← Matrix.mul_assoc T, ← Matrix.mul_assoc, hMTMr]
  have hUg : ∀ Y : Matrix n n ℝ, M * (Tᵀ * (M * Y)) = M * Y := fun Y => by
    rw [← Matrix.mul_assoc Tᵀ, ← Matrix.mul_assoc, hMUMr]
  refine ⟨Tᵀ * M * T, ?_, ?_, ?_, ?_⟩
  · rw [transpose_mul, transpose_mul, hM, transpose_transpose, Matrix.mul_assoc]
  · exact ((show Commute M Tᵀ from hUc).mul_right (Commute.refl M)).mul_right hTc
  · simp only [Matrix.mul_assoc]
    rw [hMTMr, hMUMr]
  · simp only [Matrix.mul_assoc]
    rw [hTg, hUg]

/-- Every real matrix has a matrix satisfying the four Penrose equations. -/
private theorem exists_penrose (A : Matrix m n ℝ) :
    ∃ X : Matrix n m ℝ, A * X * A = A ∧ X * A * X = X ∧ (A * X)ᵀ = A * X ∧
      (X * A)ᵀ = X * A := by
  classical
  obtain ⟨G, hGt, hGc, hMGM, hGMG⟩ :=
    exists_symm_ginv (Aᵀ * A) (by rw [transpose_mul, transpose_transpose])
  have hD : Aᵀ * A * (G * (Aᵀ * A) - 1) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hMGM, sub_self]
  have hAD : A * (G * (Aᵀ * A) - 1) = 0 := by
    apply conjTranspose_mul_self_eq_zero.mp
    rw [conjTranspose_eq_transpose_of_trivial, transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc Aᵀ, hD, Matrix.mul_zero]
  have hAGM : A * (G * (Aᵀ * A)) = A := by
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hAD
    exact hAD
  refine ⟨G * Aᵀ, ?_, ?_, ?_, ?_⟩
  · calc A * (G * Aᵀ) * A = A * (G * (Aᵀ * A)) := by simp only [Matrix.mul_assoc]
      _ = A := hAGM
  · calc G * Aᵀ * A * (G * Aᵀ) = G * (Aᵀ * A) * G * Aᵀ := by simp only [Matrix.mul_assoc]
      _ = G * Aᵀ := by rw [hGMG]
  · rw [transpose_mul, transpose_mul, transpose_transpose, hGt, Matrix.mul_assoc]
  · rw [transpose_mul, transpose_mul, transpose_transpose, hGt, ← Matrix.mul_assoc, hGc.eq,
      Matrix.mul_assoc]

/-- The four Penrose equations have at most one solution. -/
private theorem penrose_unique {A : Matrix m n ℝ} {X Y : Matrix n m ℝ}
    (hX1 : A * X * A = A) (hX2 : X * A * X = X) (hX3 : (A * X)ᵀ = A * X)
    (hX4 : (X * A)ᵀ = X * A) (hY1 : A * Y * A = A) (hY2 : Y * A * Y = Y)
    (hY3 : (A * Y)ᵀ = A * Y) (hY4 : (Y * A)ᵀ = Y * A) : X = Y := by
  have hAX : A * X = A * Y := by
    calc A * X = (A * X)ᵀ := hX3.symm
      _ = (A * Y * A * X)ᵀ := by rw [hY1]
      _ = (A * X)ᵀ * (A * Y)ᵀ := by
          rw [Matrix.mul_assoc (A * Y), transpose_mul (A * Y) (A * X)]
      _ = A * X * (A * Y) := by rw [hX3, hY3]
      _ = A * Y := by rw [← Matrix.mul_assoc, hX1]
  have hXA : X * A = Y * A := by
    calc X * A = (X * A)ᵀ := hX4.symm
      _ = (X * (A * Y * A))ᵀ := by rw [hY1]
      _ = (Y * A)ᵀ * (X * A)ᵀ := by
          rw [← Matrix.mul_assoc X (A * Y) A, ← Matrix.mul_assoc X A Y,
            Matrix.mul_assoc (X * A) Y A, transpose_mul (X * A) (Y * A)]
      _ = Y * A * (X * A) := by rw [hX4, hY4]
      _ = Y * A := by rw [Matrix.mul_assoc Y A (X * A), ← Matrix.mul_assoc A X A, hX1]
  calc X = X * A * X := hX2.symm
    _ = X * (A * Y) := by rw [Matrix.mul_assoc, hAX]
    _ = Y * A * Y := by rw [← Matrix.mul_assoc, hXA]
    _ = Y := hY2

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
      (A * pinv A)ᵀ = A * pinv A ∧ (pinv A * A)ᵀ = pinv A * A :=
  Classical.choose_spec (exists_penrose A)

/-- Any matrix satisfying the four Penrose equations is the pseudoinverse (item 150 of
MATH-PLAN-library-2). -/
theorem pinv_unique {A : Matrix m n ℝ} {X : Matrix n m ℝ}
    (h1 : A * X * A = A) (h2 : X * A * X = X) (h3 : (A * X)ᵀ = A * X)
    (h4 : (X * A)ᵀ = X * A) : X = pinv A := by
  obtain ⟨p1, p2, p3, p4⟩ := pinv_spec A
  exact penrose_unique h1 h2 h3 h4 p1 p2 p3 p4

/-- The normal equations for `pinv A *ᵥ y`, for every design. -/
private theorem transpose_mulVec_sub_mulVec_pinv (A : Matrix m n ℝ) (y : m → ℝ) :
    Aᵀ *ᵥ (y - A *ᵥ (pinv A *ᵥ y)) = 0 := by
  obtain ⟨h1, -, h3, -⟩ := pinv_spec A
  have hN : Aᵀ * (A * pinv A) = Aᵀ := by
    have := congrArg transpose h1
    rw [transpose_mul, h3] at this
    exact this
  simp only [mulVec_sub, mulVec_mulVec, hN, sub_self]

/-- **Least squares with any design**, rank-deficient included (item 150 of
MATH-PLAN-library-2): no `A β` is closer to `y`, in the sum of squares, than `A (pinv A y)`. -/
theorem pinv_residual_dotProduct_le (A : Matrix m n ℝ) (y : m → ℝ) (β : n → ℝ) :
    (y - A *ᵥ (pinv A *ᵥ y)) ⬝ᵥ (y - A *ᵥ (pinv A *ᵥ y)) ≤
      (y - A *ᵥ β) ⬝ᵥ (y - A *ᵥ β) := by
  have h0 := transpose_mulVec_sub_mulVec_pinv A y
  have hsplit : y - A *ᵥ β =
      (y - A *ᵥ (pinv A *ᵥ y)) + A *ᵥ (pinv A *ᵥ y - β) := by
    rw [mulVec_sub]; abel
  rw [hsplit]
  generalize y - A *ᵥ (pinv A *ᵥ y) = r at h0 ⊢
  generalize pinv A *ᵥ y - β = d
  have horth : r ⬝ᵥ (A *ᵥ d) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, h0, zero_dotProduct]
  have hnn : 0 ≤ (A *ᵥ d) ⬝ᵥ (A *ᵥ d) := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rw [add_dotProduct, dotProduct_add, dotProduct_add, horth, dotProduct_comm (A *ᵥ d) r, horth]
  linarith

/-- For full column rank, the pseudoinverse is the least-squares matrix `(Aᵀ A)⁻¹ Aᵀ` (item 150
of MATH-PLAN-library-2). -/
theorem pinv_eq_leastSquares {A : Matrix m n ℝ} (hA : IsUnit (Aᵀ * A).det) :
    pinv A = ClassicalLean.Statistics.leastSquares A := by
  have hL := ClassicalLean.Statistics.leastSquares_mul_self hA
  refine (pinv_unique (A := A) (X := ClassicalLean.Statistics.leastSquares A)
    ?_ ?_ ?_ ?_).symm
  · rw [Matrix.mul_assoc, hL, Matrix.mul_one]
  · rw [hL, Matrix.one_mul]
  · rw [ClassicalLean.Statistics.leastSquares, transpose_mul, transpose_mul, transpose_transpose,
      transpose_nonsing_inv, transpose_mul, transpose_transpose, Matrix.mul_assoc]
  · rw [hL, transpose_one]

end ClassicalLean.Algebra.Pseudoinverse

/-- The hypotheses of `pinv_unique` hold together: `A = !![1, 2; 0, 0]`, a matrix of rank one that
is neither symmetric nor invertible, and `X = !![1/5, 0; 2/5, 0]`, which is `Aᵀ / 5` and satisfies
the four Penrose equations: `A X = !![1, 0; 0, 0]` and `X A = !![1/5, 2/5; 2/5, 4/5]` are
symmetric, `A X A = A` and `X A X = X`. -/
example := ClassicalLean.Algebra.Pseudoinverse.pinv_unique (m := Fin 2) (n := Fin 2)
    (A := !![(1 : ℝ), 2; 0, 0]) (X := !![(1 / 5 : ℝ), 0; 2 / 5, 0])
    (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two])
    (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two])
    (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two])
    (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two])

/-- The hypotheses of `pinv_eq_leastSquares` hold together: the three-by-two matrix
`A = !![1, 0; 0, 1; 1, 1]` has full column rank: `Aᵀ * A = !![2, 1; 1, 2]`, whose determinant `3`
is a unit. -/
example := ClassicalLean.Algebra.Pseudoinverse.pinv_eq_leastSquares (m := Fin 3) (n := Fin 2)
    (A := !![(1 : ℝ), 0; 0, 1; 1, 1])
    (by
      rw [isUnit_iff_ne_zero, Matrix.det_fin_two]
      norm_num [Matrix.mul_apply, Fin.sum_univ_three])

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.foldStage2 (fun acc n _ => acc.push n) (#[] : Array Name)
  logInfo m!"ALLCONST {names.size}"
  for n in names do logInfo m!"CONST {n}"
