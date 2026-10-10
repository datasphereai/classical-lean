/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.Matrix.Spectrum

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
* `integral_trace_sq_sampleCov` (order LEAN-26): pure noise spreads the eigenvalues of a sample
  covariance matrix; see the last section.
* `exists_isMaxOn_variance_mix`, `exists_isMinOn_variance_mix`: over weights of Euclidean length
  `1`, the largest variance of a mix is reached at an eigenvector of `S`, equals the largest
  eigenvalue of `S`, and equals Mathlib's supremum of the Rayleigh quotient (likewise the least
  variance, the least eigenvalue and the infimum).

The weights live in `EuclideanSpace ℝ ι`. On plain `ι → ℝ`, Mathlib's norm is the largest entry:
then `w = (1, 1, -1)` has norm `1` and, for one covariance matrix, variance `6.5` against a
largest eigenvalue `2.26`. Length `1` is needed: `w = 10 v`, for a unit eigenvector `v`, has `100`
times the variance.

## Noise spreads the eigenvalues (order LEAN-26, item 70 of the plan)

A table of `p` rows (markets, say) and `n` columns (days) holds pure noise: every entry has mean
`0` and variance `1`, all independent. The true covariance matrix is the identity, every
eigenvalue `1`. The sample covariance `S = X Xᵀ / n` (`sampleCov`; no sample mean is subtracted,
which is right here because the true mean `0` is known) has the right mean,
`E[S] = I` (`integral_sampleCov`), but its eigenvalues spread out: their mean square has
expectation `E[tr (S²)] / p = 1 + (μ₄ + p − 2) / n` (`integral_trace_sq_sampleCov`, and
`integral_sum_sq_eigenvalues_sampleCov` with `tr (S²) = ∑ λᵢ²` from
`trace_mul_self_eq_sum_sq_eigenvalues`), where `μ₄` is the entries' fourth moment. Since
`μ₄ ≥ 1` whenever the second moment is `1` (`one_le_integral_pow_four`), the excess over `1` is
at least `(p − 1) / n` for every law of the entries that meets the hypotheses
(`one_add_le_integral_trace_sq_sampleCov`). With Gaussian entries (`μ₄ = 3`), `50` rows
and `250` columns the mean square is `1 + 51/250 = 1.204`: about 20% too large from noise alone.
This is the finite-sample core of the Marchenko–Pastur law (its second moment); the law itself is
not proved here.

**The Lean statements.** The table is `X : ι → κ → Ω → ℝ` on a measure space, with
`p = Fintype.card ι ≥ 1` and `n = Fintype.card κ ≥ 1` (`Nonempty`). "Independent entries" is
`iIndepFun (fun q : ι × κ ↦ X q.1 q.2) μ`: the `p n` entries are mutually independent (which also
makes `μ` a probability measure). "Mean `0`, variance `1`, fourth moment `μ₄`" is
`μ[X i k] = 0`, `μ[X i k ^ 2] = 1` and `μ[X i k ^ 4] = μ₄` for every entry; the entries need not
share a law, only these three numbers. Integrability: every entry is in `L⁴`
(`MemLp (X i k) 4 μ`; `L²` for `integral_sampleCov`), so every product of four entries is
integrable (`integrable_mul_mul_mul`) and no integral in the proof takes Lean's value `0` for a
non-integrable function.

Each hypothesis is needed (order LEAN-26's checks, lines V1 to V9 and V4b; V1 to V4b enumerate
every outcome exactly, V5 to V7 are Lean's junk values worked by hand):

* the formula itself, exact by enumeration, for `±1` entries (`μ₄ = 1`) and for entries `2` with
  chance `1/5` and `−1/2` with chance `4/5` (mean `0`, variance `1`, `μ₄ = 13/4`), at
  `(p, n) = (1, 1), (2, 1), (2, 2), (3, 2), (2, 3)`; `E[S] = I` for the second law at `p = n = 2`.
* independence: every entry the same `±1` variable, `p = n = 2`: `E[tr S²] / p = 2` against
  `1 + 1/2`.
* mean `0`: every entry the constant `1` (second and fourth moments `1`), `p = n = 2`: `2` against
  `3/2`.
* variance `1`: entries `±2` (mean `0`, second moment `4`, `μ₄ = 16`), `p = 2`, `n = 1`: `32`
  against `1 + 16 = 17`.
* the fourth-moment equation fixes the `μ₄` in the formula; without it the right side holds a free
  number.
* `L⁴`: with no fourth moment, Lean's integrals of `X⁴` and of `tr S²` are both `0`; at `p = 2`,
  `n = 1` the left side is `0 / 2 = 0` and the right side `1 + (0 + 2 − 2) / 1 = 1`.
* `n ≥ 1`: with no columns `S = 0` (Lean's `x / 0`), left `0`, right `1 + (μ₄ + p − 2) / 0 = 1`.
* `p ≥ 1`: with no rows the fourth-moment hypothesis says nothing, so `μ₄ = 5` is allowed; at
  `n = 1` the left side is `0 / 0 = 0` and the right side `1 + 3 = 4`.
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

section SampleCovariance

variable {κ : Type*} [Fintype κ]

/-- The sample covariance of a `p × n` table: `S i j = (1/n) ∑ k, X i k X j k`. -/
noncomputable def sampleCov (X : ι → κ → Ω → ℝ) (ω : Ω) : Matrix ι ι ℝ :=
  fun i j ↦ (∑ k, X i k ω * X j k ω) / Fintype.card κ

/-- `|a b c d| ≤ a⁴ + b⁴ + c⁴ + d⁴`, which makes a product of four `L⁴` functions integrable. -/
lemma abs_mul_mul_mul_le (a b c d : ℝ) : |a * b * (c * d)| ≤ a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (a * b + c * d), sq_nonneg (a * b - c * d),
    sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (c ^ 2 - d ^ 2), sq_nonneg (a ^ 2 + b ^ 2),
    sq_nonneg (c ^ 2 + d ^ 2)]

/-- An `L⁴` function has an integrable fourth power. -/
lemma integrable_pow_four {f : Ω → ℝ} (hf : MemLp f 4 μ) : Integrable (fun ω ↦ f ω ^ 4) μ := by
  have := hf.integrable_norm_pow (p := 4) (by norm_num)
  refine this.congr (ae_of_all _ fun ω ↦ ?_)
  simp only [Real.norm_eq_abs]
  exact Even.pow_abs (by decide) _

/-- A product of four `L⁴` functions is integrable. -/
lemma integrable_mul_mul_mul {a b c d : Ω → ℝ} (ha : MemLp a 4 μ) (hb : MemLp b 4 μ)
    (hc : MemLp c 4 μ) (hd : MemLp d 4 μ) :
    Integrable (fun ω ↦ a ω * b ω * (c ω * d ω)) μ := by
  refine Integrable.mono' ((((integrable_pow_four ha).add (integrable_pow_four hb)).add
    (integrable_pow_four hc)).add (integrable_pow_four hd))
    ((ha.aestronglyMeasurable.mul hb.aestronglyMeasurable).mul
      (hc.aestronglyMeasurable.mul hd.aestronglyMeasurable)) (ae_of_all _ fun ω ↦ ?_)
  simpa [Real.norm_eq_abs] using abs_mul_mul_mul_le (a ω) (b ω) (c ω) (d ω)

omit [Fintype ι] [Fintype κ] in
/-- **The mean of a product of four entries** `X i k X j k X j l X i l`: `μ₄` if `i = j` and
`k = l`, `1` if exactly one of the two holds, `0` if neither (four distinct independent entries,
one with mean `0`). -/
theorem integral_entries_four [DecidableEq ι] [DecidableEq κ] {X : ι → κ → Ω → ℝ} {μ₄ : ℝ}
    (hind : iIndepFun (fun q : ι × κ ↦ X q.1 q.2) μ)
    (hX : ∀ i k, MemLp (X i k) 4 μ) (h0 : ∀ i k, μ[X i k] = 0)
    (h2 : ∀ i k, μ[fun ω ↦ X i k ω ^ 2] = 1) (h4 : ∀ i k, μ[fun ω ↦ X i k ω ^ 4] = μ₄)
    (i j : ι) (k l : κ) :
    ∫ ω, X i k ω * X j k ω * (X j l ω * X i l ω) ∂μ =
      (if k = l then 1 else 0) + (if i = j then 1 else 0) +
        (μ₄ - 2) * ((if i = j then 1 else 0) * (if k = l then 1 else 0)) := by
  have hm : ∀ q : ι × κ, AEMeasurable ((fun q : ι × κ ↦ X q.1 q.2) q) μ :=
    fun q ↦ (hX q.1 q.2).aestronglyMeasurable.aemeasurable
  have hsq : ∀ a b : ι × κ, a ≠ b →
      ∫ ω, X a.1 a.2 ω ^ 2 * X b.1 b.2 ω ^ 2 ∂μ = 1 := by
    intro a b hab
    have := (hind.indepFun hab).integral_fun_comp_mul_comp (hm a) (hm b)
      (f := fun x ↦ x ^ 2) (g := fun x ↦ x ^ 2) (continuous_pow 2).aestronglyMeasurable
      (continuous_pow 2).aestronglyMeasurable
    rw [this, h2, h2, one_mul]
  by_cases hij : i = j <;> by_cases hkl : k = l
  · subst hij hkl
    rw [show (fun ω ↦ X i k ω * X i k ω * (X i k ω * X i k ω)) = fun ω ↦ X i k ω ^ 4 from
      funext fun ω ↦ by ring, h4]
    simp; ring
  · subst hij
    have := hsq (i, k) (i, l) (by simp [hkl])
    simp only at this
    rw [show (fun ω ↦ X i k ω * X i k ω * (X i l ω * X i l ω)) =
      fun ω ↦ X i k ω ^ 2 * X i l ω ^ 2 from funext fun ω ↦ by ring, this]
    simp [hkl]
  · subst hkl
    have := hsq (i, k) (j, k) (by simp [hij])
    simp only at this
    rw [show (fun ω ↦ X i k ω * X j k ω * (X j k ω * X i k ω)) =
      fun ω ↦ X i k ω ^ 2 * X j k ω ^ 2 from funext fun ω ↦ by ring, this]
    simp [hij]
  · set Y : ι × κ → Ω → ℝ := fun q ↦ X q.1 q.2
    set s : Finset (ι × κ) := {(j, k), (j, l), (i, l)}
    have hnot : (i, k) ∉ s := by simp [s, hij, hkl]
    have hI := hind.indepFun_finsetProd_of_notMem₀ hm hnot
    have hprod : ∀ ω, (∏ q ∈ s, Y q) ω = X j k ω * (X j l ω * X i l ω) := fun ω ↦ by
      have h1 : (j, k) ∉ ({(j, l), (i, l)} : Finset (ι × κ)) := by simp [hkl]
      have h2' : (j, l) ∉ ({(i, l)} : Finset (ι × κ)) := by simp [Ne.symm hij]
      simp only [s, Finset.prod_apply, prod_insert h1, prod_insert h2', prod_singleton, Y]
    have hmeas : AEStronglyMeasurable (∏ q ∈ s, Y q) μ :=
      Finset.aestronglyMeasurable_prod _ fun q _ ↦ (hX q.1 q.2).aestronglyMeasurable
    have := hI.integral_fun_mul_eq_mul_integral hmeas (hX i k).aestronglyMeasurable
    simp only [hprod, Y] at this
    rw [show (fun ω ↦ X i k ω * X j k ω * (X j l ω * X i l ω)) =
      fun ω ↦ X j k ω * (X j l ω * X i l ω) * X i k ω from funext fun ω ↦ by ring, this, h0]
    simp [hij, hkl]

omit [Fintype ι] in
/-- **The sample covariance has the right mean**: `E[S] = I` for independent entries with mean `0`
and variance `1`. -/
theorem integral_sampleCov [DecidableEq ι] [Nonempty κ] {X : ι → κ → Ω → ℝ}
    (hind : iIndepFun (fun q : ι × κ ↦ X q.1 q.2) μ)
    (hX : ∀ i k, MemLp (X i k) 2 μ) (h0 : ∀ i k, μ[X i k] = 0)
    (h2 : ∀ i k, μ[fun ω ↦ X i k ω ^ 2] = 1) (i j : ι) :
    ∫ ω, sampleCov X ω i j ∂μ = (1 : Matrix ι ι ℝ) i j := by
  have hn : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hint : ∀ k, Integrable (fun ω ↦ X i k ω * X j k ω) μ := fun k ↦ by
    have := (hX j k).integrable_mul (hX i k)
    exact this.congr (ae_of_all _ fun ω ↦ by simp only [Pi.mul_apply]; ring)
  have hk : ∀ k, ∫ ω, X i k ω * X j k ω ∂μ = if i = j then 1 else 0 := fun k ↦ by
    by_cases hij : i = j
    · subst hij
      rw [show (fun ω ↦ X i k ω * X i k ω) = fun ω ↦ X i k ω ^ 2 from funext fun ω ↦ by ring, h2]
      simp
    · have hne : ((i, k) : ι × κ) ≠ (j, k) := by simp [hij]
      have := (hind.indepFun hne).integral_fun_mul_eq_mul_integral (hX i k).aestronglyMeasurable
        (hX j k).aestronglyMeasurable
      simp only at this
      rw [this, h0]; simp [hij]
  simp only [sampleCov]
  rw [integral_div, integral_finsetSum _ fun k _ ↦ hint k]
  simp only [hk, sum_const, card_univ, nsmul_eq_mul, Matrix.one_apply]
  split_ifs <;> field_simp

/-- **Noise spreads the eigenvalues.** For a `p × n` table of independent entries with mean `0`,
variance `1` and fourth moment `μ₄`, `E[tr (S²)] / p = 1 + (μ₄ + p − 2) / n`. -/
theorem integral_trace_sq_sampleCov [Nonempty ι] [Nonempty κ] {X : ι → κ → Ω → ℝ} {μ₄ : ℝ}
    (hind : iIndepFun (fun q : ι × κ ↦ X q.1 q.2) μ)
    (hX : ∀ i k, MemLp (X i k) 4 μ) (h0 : ∀ i k, μ[X i k] = 0)
    (h2 : ∀ i k, μ[fun ω ↦ X i k ω ^ 2] = 1) (h4 : ∀ i k, μ[fun ω ↦ X i k ω ^ 4] = μ₄) :
    (∫ ω, (sampleCov X ω * sampleCov X ω).trace ∂μ) / Fintype.card ι =
      1 + (μ₄ + Fintype.card ι - 2) / Fintype.card κ := by
  classical
  have hn : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hp : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have htr : ∀ ω, (sampleCov X ω * sampleCov X ω).trace =
      ∑ i, ∑ j, ∑ k, ∑ l, X i k ω * X j k ω * (X j l ω * X i l ω) /
        (Fintype.card κ : ℝ) ^ 2 := fun ω ↦ by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, sampleCov]
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
    rw [div_mul_div_comm, sum_mul_sum, ← sq, sum_div]
    simp only [sum_div]
  have hI : ∀ i j k l, Integrable (fun ω ↦ X i k ω * X j k ω * (X j l ω * X i l ω) /
      (Fintype.card κ : ℝ) ^ 2) μ :=
    fun i j k l ↦ (integrable_mul_mul_mul (hX i k) (hX j k) (hX j l) (hX i l)).div_const _
  simp only [htr]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    integrable_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun l _ ↦ hI i j k l]
  simp_rw [integral_finsetSum _ fun j _ ↦ integrable_finsetSum _ fun k _ ↦
    integrable_finsetSum _ fun l _ ↦ hI _ j k l]
  simp_rw [integral_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun l _ ↦ hI _ _ k l]
  simp_rw [integral_finsetSum _ fun l _ ↦ hI _ _ _ l]
  simp_rw [integral_div, integral_entries_four hind hX h0 h2 h4, ← sum_div]
  simp only [sum_add_distrib, ← mul_sum, sum_ite_eq, mem_univ, ite_true, mul_ite,
    mul_one, mul_zero, sum_const, card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- For a real symmetric matrix, `tr (A²)` is the sum of the squared eigenvalues. -/
theorem trace_mul_self_eq_sum_sq_eigenvalues [DecidableEq ι] {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) : (A * A).trace = ∑ i, hA.eigenvalues i ^ 2 := by
  conv_lhs => rw [hA.spectral_theorem, ← map_mul, Unitary.conjStarAlgAut_apply, trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, diagonal_mul_diagonal, trace_diagonal]
  simp [sq]

omit [Fintype ι] in
/-- The sample covariance is symmetric. -/
lemma isHermitian_sampleCov (X : ι → κ → Ω → ℝ) (ω : Ω) : (sampleCov X ω).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, star_trivial, sampleCov]
  congr 1
  exact sum_congr rfl fun k _ ↦ mul_comm _ _

/-- **The same, in eigenvalues**: the expected mean square of the eigenvalues of `S` is
`1 + (μ₄ + p − 2) / n`, where the true covariance has every eigenvalue `1`. -/
theorem integral_sum_sq_eigenvalues_sampleCov [DecidableEq ι] [Nonempty ι] [Nonempty κ]
    {X : ι → κ → Ω → ℝ} {μ₄ : ℝ} (hind : iIndepFun (fun q : ι × κ ↦ X q.1 q.2) μ)
    (hX : ∀ i k, MemLp (X i k) 4 μ) (h0 : ∀ i k, μ[X i k] = 0)
    (h2 : ∀ i k, μ[fun ω ↦ X i k ω ^ 2] = 1) (h4 : ∀ i k, μ[fun ω ↦ X i k ω ^ 4] = μ₄) :
    (∫ ω, ∑ i, (isHermitian_sampleCov X ω).eigenvalues i ^ 2 ∂μ) / Fintype.card ι =
      1 + (μ₄ + Fintype.card ι - 2) / Fintype.card κ := by
  simp_rw [← trace_mul_self_eq_sum_sq_eigenvalues]
  exact integral_trace_sq_sampleCov hind hX h0 h2 h4

/-- **The fourth moment is at least `1`** when the second moment is `1` (from `E[(f² − 1)²] ≥ 0`),
so the excess `(μ₄ + p − 2) / n` is at least `(p − 1) / n`. -/
theorem one_le_integral_pow_four [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 4 μ)
    (h2 : μ[fun ω ↦ f ω ^ 2] = 1) : 1 ≤ μ[fun ω ↦ f ω ^ 4] := by
  have h4 := integrable_pow_four hf
  have hsq : Integrable (fun ω ↦ f ω ^ 2) μ :=
    (hf.mono_exponent (by norm_num)).integrable_sq
  have hnn : 0 ≤ ∫ ω, (f ω ^ 2 - 1) ^ 2 ∂μ := integral_nonneg fun ω ↦ sq_nonneg _
  have e : (fun ω ↦ (f ω ^ 2 - 1) ^ 2) = fun ω ↦ f ω ^ 4 - 2 * f ω ^ 2 + 1 :=
    funext fun ω ↦ by ring
  rw [e, integral_add (f := fun ω ↦ f ω ^ 4 - 2 * f ω ^ 2) (h4.sub (hsq.const_mul 2))
    (integrable_const _), integral_sub (f := fun ω ↦ f ω ^ 4) (g := fun ω ↦ 2 * f ω ^ 2) h4
    (hsq.const_mul 2), integral_const_mul, integral_const] at hnn
  simp only [probReal_univ, smul_eq_mul, one_mul] at hnn
  rw [h2] at hnn
  linarith

/-- **The spread is at least `(p − 1) / n`** for any law of the entries that meets the hypotheses:
`E[tr (S²)] / p ≥ 1 + (p − 1) / n`. -/
theorem one_add_le_integral_trace_sq_sampleCov [Nonempty ι] [Nonempty κ] {X : ι → κ → Ω → ℝ}
    {μ₄ : ℝ} (hind : iIndepFun (fun q : ι × κ ↦ X q.1 q.2) μ)
    (hX : ∀ i k, MemLp (X i k) 4 μ) (h0 : ∀ i k, μ[X i k] = 0)
    (h2 : ∀ i k, μ[fun ω ↦ X i k ω ^ 2] = 1) (h4 : ∀ i k, μ[fun ω ↦ X i k ω ^ 4] = μ₄) :
    1 + ((Fintype.card ι : ℝ) - 1) / Fintype.card κ ≤
      (∫ ω, (sampleCov X ω * sampleCov X ω).trace ∂μ) / Fintype.card ι := by
  have := hind.isProbabilityMeasure
  obtain ⟨i⟩ := ‹Nonempty ι›; obtain ⟨k⟩ := ‹Nonempty κ›
  have hμ := one_le_integral_pow_four (hX i k) (h2 i k)
  rw [h4] at hμ
  rw [integral_trace_sq_sampleCov hind hX h0 h2 h4]
  have hn : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  have := div_le_div_of_nonneg_right
    (show (Fintype.card ι : ℝ) - 1 ≤ μ₄ + Fintype.card ι - 2 by linarith) hn.le
  linarith

end SampleCovariance

end ClassicalLean.Probability.CovarianceDirections
