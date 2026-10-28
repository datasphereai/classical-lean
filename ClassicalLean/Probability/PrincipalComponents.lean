/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Probability.CovarianceDirections
import ClassicalLean.Analysis.PowerMethod

/-!
# Principal components by power iteration

For finitely many real random variables `X i`, each in `L²` of a finite measure `μ`, the covariance
matrix acts on `EuclideanSpace ℝ ι` as the linear map `covLin X μ`
(`ClassicalLean.Probability.CovarianceDirections`). It is symmetric, `isSymmetric_covLin`, which
is `isSelfAdjoint_covOp` turned into `IsSymmetric` by Mathlib's lemma for continuous linear maps,
`IsSelfAdjoint.isSymmetric`. With `hn : Module.finrank ℝ (EuclideanSpace ℝ ι) = n`, Mathlib's
spectral theorem gives its eigenvalues `λ = isSymmetric_covLin.eigenvalues hn : Fin n → ℝ`,
largest first (`eigenvalues_antitone`), and an orthonormal basis of eigenvectors
`isSymmetric_covLin.eigenvectorBasis hn`; `u` is its first vector, the eigenvector of `λ ⟨0, _⟩`.

* `tendsto_powerIterate_covLin` — the power method on the covariance map: if the largest
  eigenvalue is strictly above the next, `λ ⟨1, _⟩ < λ ⟨0, _⟩`, and the start `x` has a nonzero
  component `⟪u, x⟫` along `u`, the iterates `(covLin X μ ^ k) x`, rescaled to unit component along
  `u`, are within `C * (λ ⟨1, _⟩ / λ ⟨0, _⟩) ^ k` of `u` for one `C` and every `k`, and tend to `u`.
* `variance_mix_eigenvectorBasis_eq_and_le` — `u` is a direction of largest variance: the mix
  with weights `u` has variance `λ ⟨0, _⟩`, and every mix with weights of Euclidean length `1` has
  variance at most `λ ⟨0, _⟩`.

Bridge row 162 of MATH-PLAN-library-2's bridges file (order CLOUD-MATH-4), stated and proved by the
Claude Code cloud session of that order from the row's sketch; no draft. Choices Lean asked for,
each the closest to the row and to `tendsto_powerIterate` (`ClassicalLean.Analysis.PowerMethod`):
the dimension is a variable `n` with `hn`, as there; the indices are `⟨0, _⟩` and `⟨1, _⟩`, the
first two places of Mathlib's order, so `2 ≤ n` is a hypothesis of the first theorem (it is what
lets `⟨1, _⟩` be written) and `0 < n` of the second; the rate is `λ ⟨1, _⟩ / λ ⟨0, _⟩` with no
absolute values, since every eigenvalue is at least `0`. The weights of a mix are
`WithLp.ofLp w` for `w : EuclideanSpace ℝ ι`, as in `exists_isMaxOn_variance_mix`.

The proof. Every eigenvalue is at least `0`: for the unit eigenvector `b i` of `λ i`,
`λ i = variance (mix X (b i)) μ ≥ 0` (`variance_mix_eq_of_hasEigenvector`, which rests on
`reApplyInnerSelf_covOp`, and `variance_nonneg`). So `|λ i| = λ i`, and for `i ≠ ⟨0, _⟩`,
`λ i ≤ λ ⟨1, _⟩` by `eigenvalues_antitone`: the dominance `tendsto_powerIterate` asks for is
derived, not assumed, and its two conclusions are the first theorem's once the absolute values are
dropped. For the second, the equality is `variance_mix_eq_of_hasEigenvector` at `u`; the bound is
Ky Fan's maximum principle at `k = 1` (`ClassicalLean.MinMax.sum_re_inner_le_sum_eigenvalues`,
the bound half of `sum_eigenvalues_eq_iSup`): a unit `w` is an orthonormal family of one vector, so
`variance (mix X w) μ = re ⟪covLin X μ w, w⟫ ≤ λ ⟨0, _⟩`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open ClassicalLean.Probability.CovarianceDirections ClassicalLean.Analysis.PowerMethod
namespace ClassicalLean.Probability.PrincipalComponents

/-- **The power method finds the first principal component.** For `X i` in `L²` of a finite
measure, write `λ = isSymmetric_covLin.eigenvalues hn` (largest first) and
`u = isSymmetric_covLin.eigenvectorBasis hn ⟨0, _⟩`. If `2 ≤ n`, `λ ⟨1, _⟩ < λ ⟨0, _⟩` and
`⟪u, x⟫ ≠ 0`, the iterates `(covLin X μ ^ k) x` rescaled to unit component along `u` are within
`C * (λ ⟨1, _⟩ / λ ⟨0, _⟩) ^ k` of `u` for one `C` and every `k`, and tend to `u`. -/
theorem tendsto_powerIterate_covLin {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ] {X : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) {n : ℕ} (hn : Module.finrank ℝ (EuclideanSpace ℝ ι) = n)
    (h2 : 2 ≤ n)
    (hgap : (isSymmetric_covLin (X := X) (μ := μ)).eigenvalues hn ⟨1, h2⟩ <
      (isSymmetric_covLin (X := X) (μ := μ)).eigenvalues hn ⟨0, by omega⟩)
    (x : EuclideanSpace ℝ ι)
    (hx : inner ℝ ((isSymmetric_covLin (X := X) (μ := μ)).eigenvectorBasis hn ⟨0, by omega⟩) x
      ≠ 0) :
    (∃ C : ℝ, ∀ k : ℕ,
      ‖(inner ℝ ((isSymmetric_covLin (X := X) (μ := μ)).eigenvectorBasis hn ⟨0, by omega⟩)
            ((covLin X μ ^ k) x))⁻¹ • (covLin X μ ^ k) x
          - (isSymmetric_covLin (X := X) (μ := μ)).eigenvectorBasis hn ⟨0, by omega⟩‖
        ≤ C * ((isSymmetric_covLin (X := X) (μ := μ)).eigenvalues hn ⟨1, h2⟩ /
          (isSymmetric_covLin (X := X) (μ := μ)).eigenvalues hn ⟨0, by omega⟩) ^ k) ∧
    Tendsto (fun k : ℕ =>
        (inner ℝ ((isSymmetric_covLin (X := X) (μ := μ)).eigenvectorBasis hn ⟨0, by omega⟩)
          ((covLin X μ ^ k) x))⁻¹ • (covLin X μ ^ k) x) atTop
      (𝓝 ((isSymmetric_covLin (X := X) (μ := μ)).eigenvectorBasis hn ⟨0, by omega⟩)) := by
  have hT := isSymmetric_covLin (X := X) (μ := μ)
  have hnn : ∀ i, 0 ≤ hT.eigenvalues hn i := fun i => by
    have hv := hT.hasEigenvector_eigenvectorBasis hn i
    rw [RCLike.ofReal_real_eq_id, id] at hv
    rw [← variance_mix_eq_of_hasEigenvector hX hv ((hT.eigenvectorBasis hn).orthonormal.1 i)]
    exact variance_nonneg _ _
  have hgap' : |hT.eigenvalues hn ⟨1, h2⟩| < |hT.eigenvalues hn ⟨0, by omega⟩| := by
    rwa [abs_of_nonneg (hnn _), abs_of_nonneg (hnn _)]
  have hdom : ∀ i, i ≠ ⟨0, by omega⟩ →
      |hT.eigenvalues hn i| ≤ |hT.eigenvalues hn ⟨1, h2⟩| := by
    intro i hi
    rw [abs_of_nonneg (hnn _), abs_of_nonneg (hnn _)]
    apply hT.eigenvalues_antitone hn
    have : i.val ≠ 0 := fun h => hi (Fin.ext h)
    change 1 ≤ i.val
    omega
  have h := tendsto_powerIterate hT hn ⟨0, by omega⟩ ⟨1, h2⟩ hgap' hdom x hx
  rwa [abs_of_nonneg (hnn _), abs_of_nonneg (hnn _)] at h

/-- **The first principal component is a direction of largest variance.** For `X i` in `L²` of a
finite measure and `0 < n`, the mix with weights `u = isSymmetric_covLin.eigenvectorBasis hn ⟨0, _⟩`
has variance `λ ⟨0, _⟩`, the largest eigenvalue, and every mix with weights `w` of Euclidean length
`1` has variance at most `λ ⟨0, _⟩`. -/
theorem variance_mix_eigenvectorBasis_eq_and_le {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ] {X : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) {n : ℕ} (hn : Module.finrank ℝ (EuclideanSpace ℝ ι) = n)
    (h0 : 0 < n) :
    variance (mix X (WithLp.ofLp
        ((isSymmetric_covLin (X := X) (μ := μ)).eigenvectorBasis hn ⟨0, h0⟩))) μ =
        (isSymmetric_covLin (X := X) (μ := μ)).eigenvalues hn ⟨0, h0⟩ ∧
      ∀ w : EuclideanSpace ℝ ι, ‖w‖ = 1 →
        variance (mix X (WithLp.ofLp w)) μ ≤
          (isSymmetric_covLin (X := X) (μ := μ)).eigenvalues hn ⟨0, h0⟩ := by
  have hT := isSymmetric_covLin (X := X) (μ := μ)
  have hv := hT.hasEigenvector_eigenvectorBasis hn ⟨0, h0⟩
  rw [RCLike.ofReal_real_eq_id, id] at hv
  refine ⟨variance_mix_eq_of_hasEigenvector hX hv ((hT.eigenvectorBasis hn).orthonormal.1 _),
    fun w hw => ?_⟩
  have hu : Orthonormal ℝ (fun _ : Fin 1 => w) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [Subsingleton.elim i j]
    simp [hw]
  have hk : 1 ≤ n := h0
  have h := ClassicalLean.MinMax.sum_re_inner_le_sum_eigenvalues hn hT hk hu
  rw [Fin.sum_univ_one, Fin.sum_univ_one, show Fin.castLE hk 0 = (⟨0, h0⟩ : Fin n) from rfl] at h
  rw [← reApplyInnerSelf_covOp hX, ContinuousLinearMap.reApplyInnerSelf_apply]
  exact h

end ClassicalLean.Probability.PrincipalComponents

open scoped NNReal in
/-- The hypotheses of `tendsto_powerIterate_covLin` hold together: two fair coin flips, the
uniform probability `μ = (1/4) · count` on the four sequences `Ω = Fin 2 → Bool`; two variables
(`ι = Fin 2`), `X 0 ω = ±2` and `X 1 ω = ±1` by the two flips, each in `L²` (a finite space). Their
means are `0`, their variances `4` and `1` and their covariance `0`, so `covLin X μ` is the map of
the diagonal matrix `diag(4, 1)` on the plane (`n = 2`), with eigenvalues `4 > 1`; an eigenvector of
a diagonal matrix with distinct entries lies on an axis, so `x = (1, 1)` has a nonzero component
along each. What moves: the second eigenvalue is `1`, not `0`, so the iterates do not reach `u` in
finitely many steps, and the rate `1/4` is not `0`. -/
example := ClassicalLean.Probability.PrincipalComponents.tendsto_powerIterate_covLin
    (ι := Fin 2) (Ω := Fin 2 → Bool) (μ := (4⁻¹ : ℝ≥0) • Measure.count)
    (X := ![fun ω => if ω 0 then (2 : ℝ) else -2, fun ω => if ω 1 then 1 else -1])
    (fun _ => MemLp.of_discrete) (hn := finrank_euclideanSpace_fin) (h2 := le_rfl)
    (hgap := by
      set X' : Fin 2 → (Fin 2 → Bool) → ℝ :=
        ![fun ω => if ω 0 then (2 : ℝ) else -2, fun ω => if ω 1 then 1 else -1]
      set μ' : Measure (Fin 2 → Bool) := (4⁻¹ : ℝ≥0) • Measure.count
      have hsum : ∀ f : (Fin 2 → Bool) → ℝ, ∑ ω, f ω =
          f ![true, true] + f ![true, false] + (f ![false, true] + f ![false, false]) := by
        intro f
        rw [← (finTwoArrowEquiv Bool).symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
          Fintype.sum_bool, Fintype.sum_bool]
        simp [finTwoArrowEquiv_symm_apply]
      have hS : covMatrix X' μ' = !![4, 0; 0, 1] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [X', μ', covMatrix, covariance, integral_smul_nnreal_measure, integral_count, hsum,
            NNReal.smul_def] <;> norm_num
      have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := finrank_euclideanSpace_fin
      have hcoord : ∀ i,
          (4 - (isSymmetric_covLin (X := X') (μ := μ')).eigenvalues hn i) *
              (isSymmetric_covLin (X := X') (μ := μ')).eigenvectorBasis hn i 0 = 0 ∧
            (1 - (isSymmetric_covLin (X := X') (μ := μ')).eigenvalues hn i) *
              (isSymmetric_covLin (X := X') (μ := μ')).eigenvectorBasis hn i 1 = 0 := by
        intro i
        have h := (isSymmetric_covLin (X := X') (μ := μ')).apply_eigenvectorBasis hn i
        generalize (isSymmetric_covLin (X := X') (μ := μ')).eigenvectorBasis hn i = v at h ⊢
        generalize (isSymmetric_covLin (X := X') (μ := μ')).eigenvalues hn i = c at h ⊢
        have e0 := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) h
        have e1 := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 1) h
        simp only [Fin.isValue, covLin, covOp, hS, ContinuousLinearMap.coe_coe,
          Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_fin_one, Matrix.cons_val_zero, Fin.sum_univ_two, Matrix.cons_val_one,
          zero_mul, add_zero, Real.ringHom_apply, PiLp.smul_apply, smul_eq_mul,
          mul_eq_mul_right_iff, one_mul, zero_add] at e0 e1
        refine ⟨?_, by linear_combination e1⟩
        rcases e0 with e0 | e0
        · rw [← e0]; ring
        · rw [e0]; ring
      have ho := ((isSymmetric_covLin (X := X') (μ := μ')).eigenvectorBasis hn).orthonormal
      rw [orthonormal_iff_ite] at ho
      have h00 := ho 0 0
      have h11 := ho 1 1
      have h01 := ho 0 1
      simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
        Fin.isValue, ↓reduceIte, zero_ne_one] at h00 h11 h01
      have hanti := (isSymmetric_covLin (X := X') (μ := μ')).eigenvalues_antitone hn
        (show (0 : Fin 2) ≤ 1 by decide)
      obtain ⟨a0, a1⟩ := hcoord 0
      obtain ⟨b0, b1⟩ := hcoord 1
      change (isSymmetric_covLin (X := X') (μ := μ')).eigenvalues hn 1 <
        (isSymmetric_covLin (X := X') (μ := μ')).eigenvalues hn 0
      refine lt_of_le_of_ne hanti fun heq => ?_
      rw [heq] at b0 b1
      generalize (isSymmetric_covLin (X := X') (μ := μ')).eigenvalues hn 0 = c at a0 a1 b0 b1
      generalize ((isSymmetric_covLin (X := X') (μ := μ')).eigenvectorBasis hn 0).ofLp 0 = p0
        at a0 h00 h01
      generalize ((isSymmetric_covLin (X := X') (μ := μ')).eigenvectorBasis hn 0).ofLp 1 = p1
        at a1 h00 h01
      generalize ((isSymmetric_covLin (X := X') (μ := μ')).eigenvectorBasis hn 1).ofLp 0 = q0
        at b0 h11 h01
      generalize ((isSymmetric_covLin (X := X') (μ := μ')).eigenvectorBasis hn 1).ofLp 1 = q1
        at b1 h11 h01
      by_cases hc : c = 4
      · have hp1 : p1 = 0 := by rw [hc] at a1; linarith
        have hq1 : q1 = 0 := by rw [hc] at b1; linarith
        rw [hp1] at h00 h01
        rw [hq1] at h11 h01
        nlinarith
      · have hc' : 4 - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
        have hp0 : p0 = 0 := (mul_eq_zero.mp a0).resolve_left hc'
        have hq0 : q0 = 0 := (mul_eq_zero.mp b0).resolve_left hc'
        rw [hp0] at h00 h01
        rw [hq0] at h11 h01
        nlinarith)
    (x := EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1)
    (hx := by
      set X' : Fin 2 → (Fin 2 → Bool) → ℝ :=
        ![fun ω => if ω 0 then (2 : ℝ) else -2, fun ω => if ω 1 then 1 else -1]
      set μ' : Measure (Fin 2 → Bool) := (4⁻¹ : ℝ≥0) • Measure.count
      have hsum : ∀ f : (Fin 2 → Bool) → ℝ, ∑ ω, f ω =
          f ![true, true] + f ![true, false] + (f ![false, true] + f ![false, false]) := by
        intro f
        rw [← (finTwoArrowEquiv Bool).symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
          Fintype.sum_bool, Fintype.sum_bool]
        simp [finTwoArrowEquiv_symm_apply]
      have hS : covMatrix X' μ' = !![4, 0; 0, 1] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [X', μ', covMatrix, covariance, integral_smul_nnreal_measure, integral_count, hsum,
            NNReal.smul_def] <;> norm_num
      have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := finrank_euclideanSpace_fin
      change inner ℝ ((isSymmetric_covLin (X := X') (μ := μ')).eigenvectorBasis hn 0)
        (EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1) ≠ 0
      have h := (isSymmetric_covLin (X := X') (μ := μ')).apply_eigenvectorBasis hn 0
      have hv0 :=
        ((isSymmetric_covLin (X := X') (μ := μ')).eigenvectorBasis hn).orthonormal.ne_zero 0
      generalize (isSymmetric_covLin (X := X') (μ := μ')).eigenvectorBasis hn 0 = v at h hv0 ⊢
      generalize (isSymmetric_covLin (X := X') (μ := μ')).eigenvalues hn 0 = c at h
      have e0 := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) h
      have e1 := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 1) h
      simp only [Fin.isValue, covLin, covOp, hS, ContinuousLinearMap.coe_coe,
        Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_fin_one, Matrix.cons_val_zero, Fin.sum_univ_two, Matrix.cons_val_one,
        zero_mul, add_zero, Real.ringHom_apply, PiLp.smul_apply, smul_eq_mul,
        mul_eq_mul_right_iff, one_mul, zero_add] at e0 e1
      intro hzero
      simp [inner_add_right, EuclideanSpace.inner_single_right] at hzero
      apply hv0
      rcases e0 with hc | hz0
      · have hz1 : v 1 = 0 := by rw [← hc] at e1; linarith
        ext j; fin_cases j
        · simp; linarith
        · simpa using hz1
      · ext j; fin_cases j
        · simpa using hz0
        · simp; linarith)

open scoped NNReal in
/-- The hypotheses of `variance_mix_eigenvectorBasis_eq_and_le` hold together: the two variables
of the witness above, `X 0 ω = ±2` and `X 1 ω = ±1` by two fair coin flips under the uniform
probability `(1/4) · count` on `Fin 2 → Bool`, each in `L²`, with covariance matrix `diag(4, 1)` on
the plane (`n = 2`, so `0 < n`): two distinct variances, so the largest is a strict maximum. -/
example := ClassicalLean.Probability.PrincipalComponents.variance_mix_eigenvectorBasis_eq_and_le
    (ι := Fin 2) (Ω := Fin 2 → Bool) (μ := (4⁻¹ : ℝ≥0) • Measure.count)
    (X := ![fun ω => if ω 0 then (2 : ℝ) else -2, fun ω => if ω 1 then 1 else -1])
    (fun _ => MemLp.of_discrete) (hn := finrank_euclideanSpace_fin) (h0 := two_pos)
