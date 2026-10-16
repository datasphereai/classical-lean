/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Statistics.FrischWaughLovell
import ClassicalLean.Probability.CovarianceDirections

/-!
# The residual variance estimate is unbiased

In the linear model `y = X β + ε`, with a design `X` of `n` rows and `p` columns whose Gram matrix
`Xᵀ X` is invertible, and noise `ε` of mean `0` and covariance `σ² · 1`, the residuals are
`M y`, with `M = residualMaker X` the residual maker of `Statistics/FrischWaughLovell`.

* `sum_residualMaker_mulVec_sq`: the residual sum of squares `∑ i, (M y) i ^ 2` is `εᵀ M ε`,
  because `M X = 0` and `M` is symmetric and idempotent.
* `integral_residual_sq`: its mean is `σ² (n − p)`.
* `integral_residual_sq'` (order LEAN-31, item 104): the same for any measure, not only a
  probability measure.
* `integral_residual_sq_div`: so, for `p < n`, dividing it by `n − p` estimates `σ²` without bias,
  the usual estimate `s²` of the noise variance.

The proof joins two modules: the mean of the quadratic form `εᵀ M ε` is `trace (M S) + mᵀ M m`
(`Probability/CovarianceDirections`' `integral_dotProduct_mulVec`), here `σ² trace M`, and
`trace M = n − p` (`Statistics/FrischWaughLovell`'s `trace_residualMaker`). No independence and no
normal law are assumed: only the mean and the covariance of the noise.

The invertible Gram matrix, the zero mean, the covariance `σ² · 1` and `p < n` are each
needed; the cases are order LEAN-17's checks (line C3), on finite spaces with exact arithmetic.
Without the invertible Gram matrix (`X = 0`, `n = 2`, `p = 1`, `σ = 1`) the mean is `2`, not `1`.
Without the zero mean (`ε = (1, -1)` always, `X = (1, 1)ᵀ`, so `σ = 0`) it is `2`, not `0`.
Without the covariance `σ² · 1` (`p = 0`, `n = 1`, `ε = ±1`, `σ = 0`) it is `1`, not `0`.
Without `p < n` (`n = p = 1`) Lean's `x / 0 = 0` gives `0`, not `σ²`.
The finite second moments (`hε`) are not shown needed by a case here (none exists on a finite
space). The probability measure is not needed: review r3 of order LEAN-17 proved the first theorem
for any measure, by a route that does not pass through `integral_dotProduct_mulVec`; it is kept so
that the proof is the bridge above, and `integral_residual_sq'` (order LEAN-31, item 104) is that
theorem for any measure. Its other hypotheses are the first theorem's, with the rows above; its
witness, at the end of this file, uses the counting measure of mass `4` (order LEAN-31's check
`104.r3`).

## What Mathlib provides

Matrix algebra (`Matrix.mulVec_mulVec`, `Matrix.vecMul_transpose`, `Matrix.dotProduct_mulVec`,
`Matrix.trace_smul`) and `integral_div`. Mathlib v4.34.0 has no least squares and no residual
variance: `leastSquares`, `degrees of freedom`, `residual.*variance` and `unbiased.*variance` give
no hits (order LEAN-17's plan, section 5).
-/

open MeasureTheory ProbabilityTheory Matrix Finset
open ClassicalLean.Probability.CovarianceDirections

namespace ClassicalLean.Statistics

variable {ι κ Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The residual sum of squares is the quadratic form of the residual maker at the noise. -/
lemma sum_residualMaker_mulVec_sq {X : Matrix ι κ ℝ} (hX : IsUnit (Xᵀ * X).det) (β : κ → ℝ)
    (e : ι → ℝ) :
    ∑ i, (residualMaker X *ᵥ (X *ᵥ β + e)) i ^ 2 = e ⬝ᵥ (residualMaker X *ᵥ e) := by
  set M := residualMaker X
  have hMX : M *ᵥ (X *ᵥ β) = 0 := by
    rw [mulVec_mulVec, residualMaker_mul_eq_zero hX, zero_mulVec]
  rw [mulVec_add, hMX, zero_add]
  have : ∑ i, (M *ᵥ e) i ^ 2 = (M *ᵥ e) ⬝ᵥ (M *ᵥ e) := by
    simp only [dotProduct, sq]
  rw [this]
  calc (M *ᵥ e) ⬝ᵥ (M *ᵥ e) = (e ᵥ* Mᵀ) ⬝ᵥ (M *ᵥ e) := by rw [vecMul_transpose]
    _ = e ⬝ᵥ (Mᵀ *ᵥ (M *ᵥ e)) := (dotProduct_mulVec e Mᵀ (M *ᵥ e)).symm
    _ = e ⬝ᵥ (M *ᵥ e) := by
      rw [mulVec_mulVec, transpose_residualMaker, residualMaker_mul_self]

/-- **The residual sum of squares has mean `σ² (n − p)`.** In `y = X β + ε`, with `X` of `n` rows
and `p` columns and `Xᵀ X` invertible, and noise of mean `0` and covariance `σ² · 1`, the mean of
`∑ i, (M y) i ^ 2`, `M` the residual maker, is `σ² (n − p)`. -/
theorem integral_residual_sq {X : Matrix ι κ ℝ} (hX : IsUnit (Xᵀ * X).det) (β : κ → ℝ)
    {ε : ι → Ω → ℝ} (hε : ∀ i, MemLp (ε i) 2 μ) (hmean : ∀ i, μ[ε i] = 0) {σ : ℝ}
    (hcov : ∀ i j, cov[ε i, ε j; μ] = if i = j then σ ^ 2 else 0) :
    ∫ ω, ∑ i, (residualMaker X *ᵥ (X *ᵥ β + fun i ↦ ε i ω)) i ^ 2 ∂μ =
      σ ^ 2 * (Fintype.card ι - Fintype.card κ) := by
  simp_rw [sum_residualMaker_mulVec_sq hX β]
  rw [integral_dotProduct_mulVec hε]
  have hS : covMatrix ε μ = σ ^ 2 • (1 : Matrix ι ι ℝ) := by
    ext i j
    simp [covMatrix, hcov, Matrix.one_apply]
  have hm : (fun i ↦ μ[ε i]) = 0 := funext hmean
  rw [hS, hm, mulVec_zero, dotProduct_zero, add_zero, Matrix.mul_smul, Matrix.mul_one,
    trace_smul, trace_residualMaker hX, smul_eq_mul]

/-- **The residual sum of squares has mean `σ² (n − p)`, for any measure** (order LEAN-31, item
104 of MATH-PLAN-library-2; review r3 of order LEAN-17). `integral_residual_sq` with no
probability measure: the noise square-integrable, of mean `0` and with covariances `σ² δᵢⱼ` under
`μ`, whatever its total mass. With mean `0` each covariance is the integral of a product, so the
quadratic form `ε ⬝ᵥ (M *ᵥ ε)` has mean `σ²` times the trace of `M`, which is `n − p`. -/
theorem integral_residual_sq' {ι κ Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {X : Matrix ι κ ℝ} (hX : IsUnit (Xᵀ * X).det) (β : κ → ℝ)
    {ε : ι → Ω → ℝ} (hε : ∀ i, MemLp (ε i) 2 μ) (hmean : ∀ i, μ[ε i] = 0) {σ : ℝ}
    (hcov : ∀ i j, cov[ε i, ε j; μ] = if i = j then σ ^ 2 else 0) :
    ∫ ω, ∑ i, (residualMaker X *ᵥ (X *ᵥ β + fun i ↦ ε i ω)) i ^ 2 ∂μ =
      σ ^ 2 * (Fintype.card ι - Fintype.card κ) := by
  simp_rw [sum_residualMaker_mulVec_sq hX β]
  have hprod : ∀ i j, ∫ ω, ε i ω * ε j ω ∂μ = if i = j then σ ^ 2 else 0 := by
    intro i j
    have h := hcov i j
    simp only [covariance, hmean, sub_zero] at h
    exact h
  have hint : ∀ i j, Integrable (fun ω ↦ ε i ω * (residualMaker X i j * ε j ω)) μ := fun i j ↦ by
    have := ((hε j).const_mul (residualMaker X i j)).integrable_mul (hε i)
    exact this.congr (ae_of_all _ fun ω ↦ by simp only [Pi.mul_apply]; ring)
  simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j]
  simp_rw [integral_finsetSum _ fun j _ ↦ hint _ j]
  have hterm : ∀ i j, ∫ ω, ε i ω * (residualMaker X i j * ε j ω) ∂μ =
      residualMaker X i j * (if i = j then σ ^ 2 else 0) := by
    intro i j
    rw [← hprod i j, ← integral_const_mul]
    congr 1
    funext ω
    ring
  simp_rw [hterm]
  have hdiag : ∀ i, ∑ j, residualMaker X i j * (if i = j then σ ^ 2 else 0) =
      residualMaker X i i * σ ^ 2 := by
    intro i
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [Ne.symm hj])
      (fun h ↦ absurd (Finset.mem_univ i) h)]
    simp
  simp only [hdiag]
  have htr : ∑ i, residualMaker X i i = (Fintype.card ι : ℝ) - Fintype.card κ :=
    trace_residualMaker hX
  rw [← Finset.sum_mul, htr]
  ring

/-- **The residual variance estimate is unbiased.** Under the hypotheses of `integral_residual_sq`,
and with more observations than parameters, the residual sum of squares divided by `n − p` has
mean `σ²`. -/
theorem integral_residual_sq_div {X : Matrix ι κ ℝ} (hX : IsUnit (Xᵀ * X).det) (β : κ → ℝ)
    {ε : ι → Ω → ℝ} (hε : ∀ i, MemLp (ε i) 2 μ) (hmean : ∀ i, μ[ε i] = 0) {σ : ℝ}
    (hcov : ∀ i j, cov[ε i, ε j; μ] = if i = j then σ ^ 2 else 0)
    (hlt : Fintype.card κ < Fintype.card ι) :
    ∫ ω, (∑ i, (residualMaker X *ᵥ (X *ᵥ β + fun i ↦ ε i ω)) i ^ 2) /
      (Fintype.card ι - Fintype.card κ) ∂μ = σ ^ 2 := by
  have hpos : (0 : ℝ) < Fintype.card ι - Fintype.card κ := by
    have : (Fintype.card κ : ℝ) < Fintype.card ι := by exact_mod_cast hlt
    linarith
  rw [integral_div, integral_residual_sq hX β hε hmean hcov, mul_div_assoc, div_self hpos.ne',
    mul_one]

end ClassicalLean.Statistics

open MeasureTheory ProbabilityTheory Matrix in
/-- The hypotheses of `integral_residual_sq` hold together: the `3 × 2` design whose columns are
the first two unit vectors of `ℝ³` (Gram matrix `1`, determinant `1`), `β = (1, 2)`, and, under the
uniform probability on four points, the noise `ε 0 = (1, 1, -1, -1)`, `ε 1 = (1, -1, 1, -1)`,
`ε 2 = (1, -1, -1, 1)`: bounded, each of mean `0`, each of variance `1` and pairwise uncorrelated
(the rows of a `4 × 4` Hadamard matrix after its first), so `σ = 1`. -/
example := ClassicalLean.Statistics.integral_residual_sq (ι := Fin 3) (κ := Fin 2) (Ω := Fin 4)
  (μ := uniformOn Set.univ) (X := !![1, 0; 0, 1; 0, 0])
  (by simp [isUnit_iff_ne_zero, det_fin_two, mul_apply, Fin.sum_univ_three]) (β := ![1, 2])
  (ε := ![![1, 1, -1, -1], ![1, -1, 1, -1], ![1, -1, -1, 1]]) (fun _ ↦ MemLp.of_discrete)
  (fun i ↦ by
    rw [integral_fintype Integrable.of_finite]
    fin_cases i <;> simp [uniformOn_univ, Measure.real, Fin.sum_univ_four])
  (σ := 1)
  (fun i j ↦ by
    simp only [covariance]
    rw [integral_fintype Integrable.of_finite]
    fin_cases i <;> fin_cases j <;>
      simp [integral_fintype Integrable.of_finite, uniformOn_univ, Measure.real,
        Fin.sum_univ_four] <;> norm_num)

open MeasureTheory ProbabilityTheory Matrix in
/-- The hypotheses of `integral_residual_sq_div` hold together: the witness of
`integral_residual_sq` above (a `3 × 2` design with Gram matrix `1`, `β = (1, 2)`, and, under the
uniform probability on four points, three bounded noise terms of mean `0`, variance `1` and no
correlation, the rows of a `4 × 4` Hadamard matrix after its first), and `p = 2 < n = 3`, so the
divisor `n − p = 1` is not `0`. -/
example := ClassicalLean.Statistics.integral_residual_sq_div (ι := Fin 3) (κ := Fin 2) (Ω := Fin 4)
  (μ := uniformOn Set.univ) (X := !![1, 0; 0, 1; 0, 0])
  (by simp [isUnit_iff_ne_zero, det_fin_two, mul_apply, Fin.sum_univ_three]) (β := ![1, 2])
  (ε := ![![1, 1, -1, -1], ![1, -1, 1, -1], ![1, -1, -1, 1]]) (fun _ ↦ MemLp.of_discrete)
  (fun i ↦ by
    rw [integral_fintype Integrable.of_finite]
    fin_cases i <;> simp [uniformOn_univ, Measure.real, Fin.sum_univ_four])
  (σ := 1)
  (fun i j ↦ by
    simp only [covariance]
    rw [integral_fintype Integrable.of_finite]
    fin_cases i <;> fin_cases j <;>
      simp [integral_fintype Integrable.of_finite, uniformOn_univ, Measure.real,
        Fin.sum_univ_four] <;> norm_num)
  (by simp)

/-- The hypotheses of `integral_residual_sq'` hold together: under the counting measure on four
points, of mass `4`, which is not a probability measure; three centred, pairwise
uncorrelated `±1` noises, each of second moment `4 = 2²`, so `σ = 2`; and a `3 × 2` design whose
Gram matrix is `1`. -/
example := ClassicalLean.Statistics.integral_residual_sq' (ι := Fin 3) (κ := Fin 2) (Ω := Fin 4)
  (μ := Measure.count) (X := !![1, 0; 0, 1; 0, 0])
  (by simp [isUnit_iff_ne_zero, det_fin_two, mul_apply, Fin.sum_univ_three]) (β := ![1, 2])
  (ε := ![![1, 1, -1, -1], ![1, -1, 1, -1], ![1, -1, -1, 1]]) (fun _ ↦ MemLp.of_discrete)
  (fun i ↦ by
    rw [integral_fintype Integrable.of_finite]
    fin_cases i <;> simp [Measure.real, Fin.sum_univ_four])
  (σ := 2)
  (fun i j ↦ by
    simp only [covariance]
    rw [integral_fintype Integrable.of_finite]
    fin_cases i <;> fin_cases j <;>
      simp [integral_fintype Integrable.of_finite, Measure.real, Fin.sum_univ_four] <;> norm_num)
