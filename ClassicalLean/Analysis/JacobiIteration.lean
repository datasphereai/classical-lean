/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Jacobi iteration for a strictly diagonally dominant matrix

To solve `A x = b`, Jacobi's method starts from any guess and repeats one step: each coordinate
`i` is solved from equation `i` with the other coordinates taken from the previous guess,
`x' i = (b i − ∑_{j ≠ i} A i j x j) / A i i` (`jacobiStep`; `jacobiIterate` repeats it).

* `norm_jacobiStep_sub_le` — if every row has `∑_{j ≠ i} |A i j| ≤ ρ |A i i|` and `A i i ≠ 0`, one
  step multiplies the distance to a solution `y` of `A y = b` by at most `ρ`, distance being
  measured by the largest coordinate (Lean's norm on `n → ℝ`).
* `norm_jacobiIterate_sub_le` — so after `k` steps the error is at most `ρ ^ k` times the first.
* `exists_rowRatio_lt_one` — a strictly diagonally dominant matrix
  (`∑_{j ≠ i} |A i j| < |A i i|` in every row) has such a `ρ` below `1`.
* `tendsto_jacobiIterate` — then the iterates converge, from every start, to `A⁻¹ b`, which is the
  one solution of `A x = b` because `A` is invertible (Mathlib's `det_ne_zero_of_sum_row_lt_diag`,
  the Levy–Desplanques theorem, proved in Mathlib's Gershgorin file).

Citation: Jacobi 1845, "Ueber eine neue Auflösungsart der bei der Methode der kleinsten Quadrate
vorkommenden linearen Gleichungen". That a strictly diagonally dominant matrix is invertible
and Jacobi's method converges from every start is a textbook result (for example Sauer, Numerical
Analysis, section 2.5). The rate `ρ ^ k` is the standard bound `‖x_k − x‖∞ ≤ ‖T‖∞ ^ k ‖x₀ − x‖∞`
for the iteration matrix `T = D⁻¹ (L + U)`, whose largest absolute row sum is the largest row
ratio `ρ`; no theorem number is cited for it, because none was checked. The proof here works
coordinate by coordinate.

## Hypotheses

Measured in order LEAN-21's checks (check C32, exact rationals): 200 random strictly dominant
matrices of size up to `4`, `k ≤ 12`. Each hypothesis is needed: drop it alone and the conclusion
fails at:

* `A i i ≠ 0`: `A = [[0, 0], [0, 1]]`, `y = (5, 0)`, `x = y`, `ρ = 0`: error `5 > 0`.
* the row bound: `A = [[1, 2], [2, 1]]`, `ρ = 1/2`, `x = 0`, `y = (1, 1)`: error `2 > 1/2`.
* `A y = b`: `A = 1`, `b = 0`, `y = (1, 1)`, `x = y`, `ρ = 0`: error `1 > 0`.
* strict dominance, for convergence: `A = [[1, 2], [2, 1]]`, `b = (3, 3)`, `x₀ = 0`: the error
  doubles each step (`1024` after 10 steps).

`0 ≤ ρ` is not assumed: when `n` has an element it follows from `A i i ≠ 0` and the row bound.

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-21, `grep -rniE` over Mathlib):
`gauss.?seidel|jacobi iteration|jacobi method|jacobiIter|jacobi.*(converge|iterat)` 1 line (Jacobi
theta functions); `diagonal(ly)? dominan|sum_row_lt_diag|diagDominant` 2 lines, both Gershgorin's
`det_ne_zero_of_sum_row_lt_diag`, used here.
-/

open Finset Filter Topology Matrix

namespace ClassicalLean.Analysis

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- One step of Jacobi's method for `A x = b`: coordinate `i` is solved from equation `i`, with the
other coordinates taken from `x`. -/
noncomputable def jacobiStep (A : Matrix n n ℝ) (b x : n → ℝ) : n → ℝ :=
  fun i ↦ (b i - ∑ j ∈ univ.erase i, A i j * x j) / A i i

/-- `k` steps of Jacobi's method from the guess `x₀`. -/
noncomputable def jacobiIterate (A : Matrix n n ℝ) (b x₀ : n → ℝ) (k : ℕ) : n → ℝ :=
  (jacobiStep A b)^[k] x₀

/-- The error of one step, coordinate by coordinate, when `A y = b`. -/
theorem jacobiStep_sub_apply {A : Matrix n n ℝ} {b x y : n → ℝ} (hdiag : ∀ i, A i i ≠ 0)
    (hy : A *ᵥ y = b) (i : n) :
    jacobiStep A b x i - y i = (∑ j ∈ univ.erase i, A i j * (y j - x j)) / A i i := by
  have hb : b i = A i i * y i + ∑ j ∈ univ.erase i, A i j * y j := by
    rw [← hy, mulVec, dotProduct, add_sum_erase _ (fun j ↦ A i j * y j) (mem_univ i)]
  rw [jacobiStep, hb, eq_div_iff (hdiag i), sub_mul, div_mul_cancel₀ _ (hdiag i)]
  simp only [mul_sub, sum_sub_distrib]
  ring

/-- **One Jacobi step multiplies the error by at most `ρ`.** If `A i i ≠ 0` and
`∑_{j ≠ i} |A i j| ≤ ρ |A i i|` in every row, and `A y = b`, then
`‖jacobiStep A b x − y‖ ≤ ρ ‖x − y‖`, the norm being the largest absolute coordinate. -/
theorem norm_jacobiStep_sub_le {A : Matrix n n ℝ} {b x y : n → ℝ} {ρ : ℝ}
    (hdiag : ∀ i, A i i ≠ 0) (hrow : ∀ i, ∑ j ∈ univ.erase i, |A i j| ≤ ρ * |A i i|)
    (hy : A *ᵥ y = b) : ‖jacobiStep A b x - y‖ ≤ ρ * ‖x - y‖ := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · simp [Subsingleton.elim (jacobiStep A b x - y) 0, Subsingleton.elim (x - y) 0]
  have hρ : 0 ≤ ρ := by
    have h1 := hrow i₀
    have h2 : 0 ≤ ∑ j ∈ univ.erase i₀, |A i₀ j| := sum_nonneg fun _ _ ↦ abs_nonneg _
    have h3 : 0 < |A i₀ i₀| := abs_pos.mpr (hdiag i₀)
    nlinarith
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hρ (norm_nonneg _))).mpr fun i ↦ ?_
  have hpos : 0 < |A i i| := abs_pos.mpr (hdiag i)
  rw [Pi.sub_apply, jacobiStep_sub_apply hdiag hy, Real.norm_eq_abs, abs_div,
    div_le_iff₀ hpos]
  calc |∑ j ∈ univ.erase i, A i j * (y j - x j)|
      ≤ ∑ j ∈ univ.erase i, |A i j| * ‖x - y‖ := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ ↦ ?_)
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [abs_sub_comm, ← Real.norm_eq_abs]
        exact norm_le_pi_norm (x - y) j
    _ = (∑ j ∈ univ.erase i, |A i j|) * ‖x - y‖ := by rw [sum_mul]
    _ ≤ ρ * |A i i| * ‖x - y‖ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg _)
    _ = ρ * ‖x - y‖ * |A i i| := by ring

/-- **The error of Jacobi's method falls like `ρ ^ k`.** Under the hypotheses of
`norm_jacobiStep_sub_le`, `‖jacobiIterate A b x₀ k − y‖ ≤ ρ ^ k ‖x₀ − y‖`. -/
theorem norm_jacobiIterate_sub_le {A : Matrix n n ℝ} {b x₀ y : n → ℝ} {ρ : ℝ}
    (hdiag : ∀ i, A i i ≠ 0) (hrow : ∀ i, ∑ j ∈ univ.erase i, |A i j| ≤ ρ * |A i i|)
    (hy : A *ᵥ y = b) (k : ℕ) : ‖jacobiIterate A b x₀ k - y‖ ≤ ρ ^ k * ‖x₀ - y‖ := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · simp [Subsingleton.elim (jacobiIterate A b x₀ k - y) 0, Subsingleton.elim (x₀ - y) 0]
  have hρ : 0 ≤ ρ := by
    have h1 := hrow i₀
    have h2 : 0 ≤ ∑ j ∈ univ.erase i₀, |A i₀ j| := sum_nonneg fun _ _ ↦ abs_nonneg _
    have h3 : 0 < |A i₀ i₀| := abs_pos.mpr (hdiag i₀)
    nlinarith
  induction k with
  | zero => simp [jacobiIterate]
  | succ k ih =>
    rw [jacobiIterate, Function.iterate_succ_apply', ← jacobiIterate]
    calc ‖jacobiStep A b (jacobiIterate A b x₀ k) - y‖
        ≤ ρ * ‖jacobiIterate A b x₀ k - y‖ := norm_jacobiStep_sub_le hdiag hrow hy
      _ ≤ ρ * (ρ ^ k * ‖x₀ - y‖) := mul_le_mul_of_nonneg_left ih hρ
      _ = ρ ^ (k + 1) * ‖x₀ - y‖ := by ring

/-- **A strictly diagonally dominant matrix has a contraction factor below `1`.** If
`∑_{j ≠ i} |A i j| < |A i i|` in every row, some `ρ ∈ [0, 1)` has
`∑_{j ≠ i} |A i j| ≤ ρ |A i i|` in every row: the largest of the row ratios. -/
theorem exists_rowRatio_lt_one {A : Matrix n n ℝ}
    (h : ∀ i, ∑ j ∈ univ.erase i, |A i j| < |A i i|) :
    ∃ ρ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ i, ∑ j ∈ univ.erase i, |A i j| ≤ ρ * |A i i| := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨0, le_rfl, zero_lt_one, fun i ↦ (IsEmpty.false i).elim⟩
  have hpos : ∀ i, 0 < |A i i| := fun i ↦
    (sum_nonneg fun _ _ ↦ abs_nonneg _).trans_lt (h i)
  let r : n → ℝ := fun i ↦ (∑ j ∈ univ.erase i, |A i j|) / |A i i|
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max r
  refine ⟨r i₀, div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (abs_nonneg _),
    (div_lt_one (hpos i₀)).mpr (h i₀), fun i ↦ ?_⟩
  exact (div_le_iff₀ (hpos i)).mp (hi₀ i)

/-- **Jacobi's method converges for a strictly diagonally dominant matrix.** If
`∑_{j ≠ i} |A i j| < |A i i|` in every row, then from every start `x₀` the iterates converge to
`A⁻¹ b`, which is the one solution of `A x = b` because `A` is invertible. -/
theorem tendsto_jacobiIterate {A : Matrix n n ℝ}
    (h : ∀ i, ∑ j ∈ univ.erase i, |A i j| < |A i i|) (b x₀ : n → ℝ) :
    Tendsto (jacobiIterate A b x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  obtain ⟨ρ, hρ0, hρ1, hrow⟩ := exists_rowRatio_lt_one h
  have hdiag : ∀ i, A i i ≠ 0 := fun i ↦
    abs_pos.mp ((sum_nonneg fun _ _ ↦ abs_nonneg _).trans_lt (h i))
  have hdet : A.det ≠ 0 := det_ne_zero_of_sum_row_lt_diag (by simpa [Real.norm_eq_abs] using h)
  have hy : A *ᵥ (A⁻¹ *ᵥ b) = b := by
    rw [mulVec_mulVec, mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hdet), one_mulVec]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun k ↦ norm_jacobiIterate_sub_le hdiag hrow hy k) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const ‖x₀ - A⁻¹ *ᵥ b‖

end ClassicalLean.Analysis

open Finset Matrix in
/-- The hypotheses of `norm_jacobiIterate_sub_le` hold together: the `2 × 2` matrix with rows
`(4, 1)` and `(1, 4)` has nonzero diagonal and each row's off-diagonal entry `1` at most
`ρ = 1/4` times its diagonal `4`; `b = (6, 9) = A y` for `y = (1, 2)`; start `x₀ = 0`, `k = 3`. -/
example := ClassicalLean.Analysis.norm_jacobiIterate_sub_le (n := Fin 2) (A := !![4, 1; 1, 4])
  (b := ![6, 9]) (x₀ := 0) (y := ![1, 2]) (ρ := 1 / 4)
  (fun i ↦ by fin_cases i <;> simp)
  (fun i ↦ by fin_cases i <;> simp [Finset.sum_erase_eq_sub, Fin.sum_univ_two])
  (by ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num) (k := 3)
