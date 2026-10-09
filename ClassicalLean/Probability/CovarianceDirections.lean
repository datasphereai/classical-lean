/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The covariance matrix of several quantities, and the directions of largest and least variance

For finitely many real random variables `X i` with finite second moments, `covMatrix X μ` is the
matrix of covariances `cov[X i, X j]`, and `mix X w = ∑ i, w i · X i` is the mix with weights `w`.

* `variance_mix`: the variance of a mix is `w ⬝ᵥ S *ᵥ w`.
* `covMatrix_apply_eq_covarianceBilin`: the entries are Mathlib's `covarianceBilin` of the joint
  law on the coordinate vectors.
* `integral_dotProduct_mulVec`: the mean of a quadratic form, `E[Xᵀ A X] = trace (A S) + mᵀ A m`
  with `m` the mean (order LEAN-17), on a probability space. A finite measure is not enough: for
  `μ` twice a point mass, `X = 1` and `A = [[1]]`, the left side is `2` and the right side `6`.
* `posSemidef_covMatrix`: `S` is positive semidefinite (Mathlib's form of this is
  `isPosSemidef_covarianceBilin`).
* `posDef_covMatrix_iff`: `S` is positive definite exactly when no nonzero mix is almost surely
  constant. This is the condition under which `MinimumQuadraticForm` gives the least-variance
  weights.
* `exists_isMaxOn_variance_mix`, `exists_isMinOn_variance_mix`: over weights of Euclidean length
  `1`, the largest variance of a mix is reached at an eigenvector of `S`, equals the largest
  eigenvalue of `S`, and equals Mathlib's supremum of the Rayleigh quotient (likewise the least
  variance, the least eigenvalue and the infimum).

The weights live in `EuclideanSpace ℝ ι`. On plain `ι → ℝ`, Mathlib's norm is the largest entry:
then `w = (1, 1, -1)` has norm `1` and, for one covariance matrix, variance `6.5` against a
largest eigenvalue `2.26`. Length `1` is needed: `w = 10 v`, for a unit eigenvector `v`, has `100`
times the variance.
-/

open MeasureTheory ProbabilityTheory Matrix Finset Module.End
open scoped InnerProductSpace RealInnerProductSpace

namespace ClassicalLean.Probability.CovarianceDirections

variable {ι Ω : Type*} [Fintype ι] {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- The covariance matrix `S i j = cov[X i, X j]`. -/
noncomputable def covMatrix (X : ι → Ω → ℝ) (μ : Measure Ω) : Matrix ι ι ℝ :=
  fun i j ↦ cov[X i, X j; μ]

/-- The mix of the `X i` with weights `w`. -/
def mix (X : ι → Ω → ℝ) (w : ι → ℝ) : Ω → ℝ := fun ω ↦ ∑ i, w i * X i ω

variable {X : ι → Ω → ℝ}

lemma memLp_mix (hX : ∀ i, MemLp (X i) 2 μ) (w : ι → ℝ) : MemLp (mix X w) 2 μ :=
  memLp_finsetSum (f := fun i ω ↦ w i * X i ω) _ fun i _ ↦ (hX i).const_mul (w i)

/-- The entries of `covMatrix` are Mathlib's `covarianceBilin` of the joint law, on the
coordinate vectors. -/
theorem covMatrix_apply_eq_covarianceBilin [IsFiniteMeasure μ] (hX : ∀ i, MemLp (X i) 2 μ)
    (i j : ι) : covMatrix X μ i j = covarianceBilin (μ.map (fun ω ↦ WithLp.toLp 2 (X · ω)))
      (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ j) :=
  (covarianceBilin_apply_basisFun hX i j).symm

/-- **The variance of a mix.** `Var(∑ wᵢ Xᵢ) = w ⬝ᵥ S *ᵥ w`. -/
theorem variance_mix [IsFiniteMeasure μ] (hX : ∀ i, MemLp (X i) 2 μ) (w : ι → ℝ) :
    variance (mix X w) μ = w ⬝ᵥ (covMatrix X μ *ᵥ w) := by
  rw [← covariance_self (memLp_mix hX w).aemeasurable]
  have h := covariance_fun_sum_fun_sum (μ := μ) (X := fun i ω ↦ w i * X i ω)
    (Y := fun i ω ↦ w i * X i ω) (fun i ↦ (hX i).const_mul (w i)) (fun i ↦ (hX i).const_mul (w i))
  simp only at h
  rw [show mix X w = fun ω ↦ ∑ i, w i * X i ω from rfl, h]
  simp only [covariance_const_mul_left, covariance_const_mul_right, dotProduct, mulVec, covMatrix,
    mul_sum]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  ring

omit [Fintype ι] in
lemma isHermitian_covMatrix : (covMatrix X μ).IsHermitian := by
  ext i j
  simp [covMatrix, covariance_comm]

omit [Fintype ι] in
/-- **The covariance matrix is positive semidefinite.** -/
theorem posSemidef_covMatrix [Finite ι] [IsFiniteMeasure μ] (hX : ∀ i, MemLp (X i) 2 μ) :
    (covMatrix X μ).PosSemidef := by
  have := Fintype.ofFinite ι
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨isHermitian_covMatrix, fun w ↦ ?_⟩
  rw [star_trivial, ← variance_mix hX]
  exact variance_nonneg _ _

/-- **When the covariance matrix is positive definite.** `S` is positive definite exactly when no
nonzero mix is almost surely constant. -/
theorem posDef_covMatrix_iff [IsProbabilityMeasure μ] (hX : ∀ i, MemLp (X i) 2 μ) :
    (covMatrix X μ).PosDef ↔ ∀ w : ι → ℝ, w ≠ 0 → ¬ ∃ c : ℝ, mix X w =ᵐ[μ] fun _ ↦ c := by
  rw [posDef_iff_dotProduct_mulVec]
  simp only [star_trivial, ← variance_mix hX]
  constructor
  · rintro ⟨-, h⟩ w hw ⟨c, hc⟩
    have := h hw
    rw [variance_congr hc, variance_eq_integral aemeasurable_const] at this
    simp at this
  · intro h
    refine ⟨isHermitian_covMatrix, fun w hw ↦ ?_⟩
    rcases (variance_nonneg (mix X w) μ).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd ⟨_, ae_eq_integral_of_variance_eq_zero (memLp_mix hX w) heq.symm⟩ (h w hw)

/-- **The mean of a quadratic form.** For a random vector `X` on a probability space, with finite
second moments, mean `m` and covariance matrix `S`, `E[Xᵀ A X] = trace (A S) + mᵀ A m`, for every
matrix `A`. -/
theorem integral_dotProduct_mulVec [IsProbabilityMeasure μ]
    (hX : ∀ i, MemLp (X i) 2 μ) (A : Matrix ι ι ℝ) :
    ∫ ω, (fun i ↦ X i ω) ⬝ᵥ (A *ᵥ fun i ↦ X i ω) ∂μ =
      (A * covMatrix X μ).trace + (fun i ↦ μ[X i]) ⬝ᵥ (A *ᵥ fun i ↦ μ[X i]) := by
  have hint : ∀ i j, Integrable (fun ω ↦ X i ω * (A i j * X j ω)) μ := fun i j ↦ by
    have := ((hX j).const_mul (A i j)).integrable_mul (hX i)
    exact this.congr (ae_of_all _ fun ω ↦ by simp only [Pi.mul_apply]; ring)
  simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j]
  simp_rw [integral_finsetSum _ fun j _ ↦ hint _ j]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, covMatrix, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  have h := covariance_eq_sub (hX j) (hX i)
  have e : (fun ω ↦ X i ω * (A i j * X j ω)) = fun ω ↦ A i j * (X j * X i) ω := by
    ext ω; simp only [Pi.mul_apply]; ring
  rw [e, integral_const_mul, h]
  ring

section Directions

variable [DecidableEq ι]

/-- The covariance matrix as an operator on `EuclideanSpace ℝ ι`. -/
noncomputable abbrev covOp (X : ι → Ω → ℝ) (μ : Measure Ω) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  toEuclideanCLM (n := ι) (𝕜 := ℝ) (covMatrix X μ)

/-- The same operator, as a linear map. -/
noncomputable abbrev covLin (X : ι → Ω → ℝ) (μ : Measure Ω) :
    EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι :=
  (covOp X μ : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)

lemma isSelfAdjoint_covOp : IsSelfAdjoint (covOp X μ) := by
  rw [isSelfAdjoint_iff, ← map_star, star_eq_conjTranspose, isHermitian_covMatrix.eq]

lemma reApplyInnerSelf_covOp [IsFiniteMeasure μ] (hX : ∀ i, MemLp (X i) 2 μ)
    (w : EuclideanSpace ℝ ι) :
    (covOp X μ).reApplyInnerSelf w = variance (mix X (WithLp.ofLp w)) μ := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, variance_mix hX, RCLike.re_to_real,
    EuclideanSpace.inner_eq_star_dotProduct, ofLp_toEuclideanCLM, star_trivial, dotProduct_comm]

lemma variance_mix_eq_of_hasEigenvector [IsFiniteMeasure μ] (hX : ∀ i, MemLp (X i) 2 μ)
    {c : ℝ} {v : EuclideanSpace ℝ ι} (hv : HasEigenvector (covLin X μ) c v)
    (hn : ‖v‖ = 1) : variance (mix X (WithLp.ofLp v)) μ = c := by
  rw [← reApplyInnerSelf_covOp hX, ContinuousLinearMap.reApplyInnerSelf_apply]
  have h := hv.apply_eq_smul
  change covOp X μ v = c • v at h
  rw [h, inner_smul_left, real_inner_self_eq_norm_sq, hn]
  simp

omit [DecidableEq ι] in
lemma exists_unit_of_hasEigenvalue {T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι} {c : ℝ}
    (h : HasEigenvalue T c) : ∃ v, HasEigenvector T c v ∧ ‖v‖ = 1 := by
  obtain ⟨v, hv⟩ := h.exists_hasEigenvector
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv.2
  refine ⟨‖v‖⁻¹ • v, ⟨?_, ?_⟩, ?_⟩
  · exact Submodule.smul_mem _ _ hv.1
  · exact smul_ne_zero (inv_ne_zero hn) hv.2
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]

/-- **The direction of largest variance.** There is a weight vector `w₀` of Euclidean length `1`
whose mix has the largest variance among all mixes with weights of length `1`; `w₀` is an
eigenvector of `S` with that variance as eigenvalue; every eigenvalue of `S` is at most it; and it
equals the supremum of the Rayleigh quotient of `S`. -/
theorem exists_isMaxOn_variance_mix [Nonempty ι] [IsFiniteMeasure μ]
    (hX : ∀ i, MemLp (X i) 2 μ) :
    ∃ w₀ : EuclideanSpace ℝ ι, ‖w₀‖ = 1 ∧
      (∀ w : EuclideanSpace ℝ ι, ‖w‖ = 1 →
        variance (mix X (WithLp.ofLp w)) μ ≤ variance (mix X (WithLp.ofLp w₀)) μ) ∧
      HasEigenvector (covLin X μ) (variance (mix X (WithLp.ofLp w₀)) μ) w₀ ∧
      (∀ c, HasEigenvalue (covLin X μ) c → c ≤ variance (mix X (WithLp.ofLp w₀)) μ) ∧
      variance (mix X (WithLp.ofLp w₀)) μ =
        ⨆ x : { x : EuclideanSpace ℝ ι // x ≠ 0 }, (covOp X μ).rayleighQuotient x := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hne : (Metric.sphere (0 : EuclideanSpace ℝ ι) 1).Nonempty :=
    ⟨EuclideanSpace.single i 1, by simp⟩
  obtain ⟨w₀, hw₀, hmax⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ ι) 1).exists_isMaxOn hne
    (covOp X μ).reApplyInnerSelf_continuous.continuousOn
  have hn : ‖w₀‖ = 1 := by simpa using hw₀
  have hw0 : w₀ ≠ 0 := by rintro rfl; simp at hn
  have hev := isSelfAdjoint_covOp.hasEigenvector_of_isMaxOn hw0 (by rwa [hn])
  have hval := variance_mix_eq_of_hasEigenvector hX hev hn
  refine ⟨w₀, hn, fun w hw ↦ ?_, by rwa [hval], fun c hc ↦ ?_, hval⟩
  · rw [← reApplyInnerSelf_covOp hX, ← reApplyInnerSelf_covOp hX]
    exact hmax (by simpa using hw)
  · obtain ⟨v, hv, hvn⟩ := exists_unit_of_hasEigenvalue hc
    rw [← variance_mix_eq_of_hasEigenvector hX hv hvn, ← reApplyInnerSelf_covOp hX,
      ← reApplyInnerSelf_covOp hX]
    exact hmax (by simpa using hvn)

/-- **The direction of least variance.** There is a weight vector `w₀` of Euclidean length `1`
whose mix has the least variance among all mixes with weights of length `1`; `w₀` is an
eigenvector of `S` with that variance as eigenvalue; every eigenvalue of `S` is at least it; and it
equals the infimum of the Rayleigh quotient of `S`. -/
theorem exists_isMinOn_variance_mix [Nonempty ι] [IsFiniteMeasure μ]
    (hX : ∀ i, MemLp (X i) 2 μ) :
    ∃ w₀ : EuclideanSpace ℝ ι, ‖w₀‖ = 1 ∧
      (∀ w : EuclideanSpace ℝ ι, ‖w‖ = 1 →
        variance (mix X (WithLp.ofLp w₀)) μ ≤ variance (mix X (WithLp.ofLp w)) μ) ∧
      HasEigenvector (covLin X μ) (variance (mix X (WithLp.ofLp w₀)) μ) w₀ ∧
      (∀ c, HasEigenvalue (covLin X μ) c → variance (mix X (WithLp.ofLp w₀)) μ ≤ c) ∧
      variance (mix X (WithLp.ofLp w₀)) μ =
        ⨅ x : { x : EuclideanSpace ℝ ι // x ≠ 0 }, (covOp X μ).rayleighQuotient x := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hne : (Metric.sphere (0 : EuclideanSpace ℝ ι) 1).Nonempty :=
    ⟨EuclideanSpace.single i 1, by simp⟩
  obtain ⟨w₀, hw₀, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ ι) 1).exists_isMinOn hne
    (covOp X μ).reApplyInnerSelf_continuous.continuousOn
  have hn : ‖w₀‖ = 1 := by simpa using hw₀
  have hw0 : w₀ ≠ 0 := by rintro rfl; simp at hn
  have hev := isSelfAdjoint_covOp.hasEigenvector_of_isMinOn hw0 (by rwa [hn])
  have hval := variance_mix_eq_of_hasEigenvector hX hev hn
  refine ⟨w₀, hn, fun w hw ↦ ?_, by rwa [hval], fun c hc ↦ ?_, hval⟩
  · rw [← reApplyInnerSelf_covOp hX, ← reApplyInnerSelf_covOp hX]
    exact hmin (by simpa using hw)
  · obtain ⟨v, hv, hvn⟩ := exists_unit_of_hasEigenvalue hc
    rw [← variance_mix_eq_of_hasEigenvector hX hv hvn, ← reApplyInnerSelf_covOp hX,
      ← reApplyInnerSelf_covOp hX]
    exact hmin (by simpa using hvn)

end Directions

end ClassicalLean.Probability.CovarianceDirections
