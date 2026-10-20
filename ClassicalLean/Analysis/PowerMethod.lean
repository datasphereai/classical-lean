/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Order.Archimedean.Real.Hom

/-!
# The power method

`T` is a symmetric linear map of a finite-dimensional real inner product space `E` of dimension
`n` (`hn : Module.finrank ℝ E = n`). Mathlib's spectral theorem gives its eigenvalues
`hT.eigenvalues hn : Fin n → ℝ`, ordered largest first, and an orthonormal basis of eigenvectors
`hT.eigenvectorBasis hn`. The power method applies `T` again and again to a start vector `x`: the
iterates are `(T ^ k) x`, the map `T ^ k` applied to `x`.

* `tendsto_powerIterate` — order CLOUD-MATH-2, item 147 of MATH-PLAN-library-2. Let
  `u = hT.eigenvectorBasis hn i₀`, an eigenvector with eigenvalue `λ₀ = hT.eigenvalues hn i₀`, and
  `λ₁ = hT.eigenvalues hn i₁`, with `|λ₁| < |λ₀|` and `|hT.eigenvalues hn i| ≤ |λ₁|` for every
  `i ≠ i₀`. If `x` has a nonzero component `⟪u, x⟫` along `u`, the iterate rescaled to unit
  component along `u`, `⟪u, (T ^ k) x⟫⁻¹ • (T ^ k) x`, is within `C * (|λ₁| / |λ₀|) ^ k` of `u` for
  one constant `C` and every `k`, and so tends to `u`.

Wider than the plan's row, by this session's reading (the draft's last review, as the order's table
gives it: GENERALIZED): the row speaks of a symmetric matrix, and the theorem is stated for a
symmetric linear map of any finite-dimensional real inner product space, a matrix being the case
`E = EuclideanSpace ℝ (Fin n)` (the witness below); and `λ₀` need not come first in Mathlib's
order of the eigenvalues, only be larger in absolute value than the eigenvalue at every other
index.

The proof. Write `x = c • u + w` with `c = ⟪u, x⟫ ≠ 0` and `⟪u, w⟫ = 0`. Then
`(T ^ k) u = λ₀ ^ k • u` (`pow_apply_eigen`) and `⟪u, (T ^ k) x⟫ = λ₀ ^ k * c` (`inner_pow_apply`,
from the symmetry of `T`), so the rescaled iterate minus `u` is `(λ₀ ^ k * c)⁻¹ • (T ^ k) w`.
Expanding `w` in the eigenvector basis, where its coefficient along `u` is `0`, gives
`‖(T ^ k) w‖ ≤ (∑ i, |⟪bᵢ, w⟫|) * |λ₁| ^ k` (`norm_pow_apply_le`), hence the bound with
`C = (∑ i, |⟪bᵢ, w⟫|) / |c|`; the rate `|λ₁| / |λ₀|` lies in `[0, 1)`, so the bound tends to `0`
(`power_aux`).

The proof is the draft `d147-r1-s2` (written by Claude Opus 5.5 through the Anthropic Batch API,
the lane's API-CREDIT-1 work), adapted by the Claude Code cloud session that landed it (order
CLOUD-MATH-2): the namespace, targeted imports and docstrings, `change` where a `show` changed the
goal, `simp` where a `simpa` needed no term, and a `first` chain and a `try` cut to what fires.
The witness at the end of the
file, for the matrix `!![2, 0; 0, 1]`, is the one claude-ai wrote for the order
(`d147-r1-s2-witness.lean`); it is why the file imports `Mathlib.Analysis.InnerProductSpace.Trace`,
`Mathlib.Analysis.Matrix.Hermitian`, `Mathlib.Analysis.Normed.Lp.Matrix`,
`Mathlib.LinearAlgebra.Trace` and `Mathlib.Algebra.Order.Archimedean.Real.Hom`.
-/

open Filter Topology

namespace ClassicalLean.Analysis.PowerMethod

/-- On an eigenvector `v` of `T` with eigenvalue `c`, `T ^ k` acts as multiplication by
`c ^ k`. -/
private lemma pow_apply_eigen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →ₗ[ℝ] E) (v : E) (c : ℝ) (h : T v = c • v) (k : ℕ) :
    (T ^ k) v = c ^ k • v := by
  induction k with
  | zero => rw [pow_zero, pow_zero, one_smul]; rfl
  | succ k ih =>
    rw [pow_succ']
    change T ((T ^ k) v) = _
    rw [ih, map_smul, h, smul_smul, ← pow_succ]

/-- For a symmetric `T` and an eigenvector `u` with eigenvalue `c`, the component of `(T ^ k) y`
along `u` is `c ^ k` times that of `y`. -/
private lemma inner_pow_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (u : E) (c : ℝ) (h : T u = c • u) (y : E)
    (k : ℕ) : inner ℝ u ((T ^ k) y) = c ^ k * inner ℝ u y := by
  induction k with
  | zero => rw [pow_zero, pow_zero, one_mul]; rfl
  | succ k ih =>
    rw [pow_succ']
    change inner ℝ u (T ((T ^ k) y)) = _
    rw [← hT u, h, real_inner_smul_left, ih]
    ring

/-- For `w` with no component along the basis vector `b i₀`, when `|ev i| ≤ μ` for every index
`i ≠ i₀`, `‖(T ^ k) w‖ ≤ (∑ i, |⟪b i, w⟫|) * μ ^ k`. -/
private lemma norm_pow_apply_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →ₗ[ℝ] E) {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (ev : Fin n → ℝ)
    (hb : ∀ i, T (b i) = ev i • b i) (i₀ : Fin n) (μ : ℝ)
    (hdom : ∀ i, i ≠ i₀ → |ev i| ≤ μ) (w : E) (hw : inner ℝ (b i₀) w = 0) (k : ℕ) :
    ‖(T ^ k) w‖ ≤ (∑ i, |inner ℝ (b i) w|) * μ ^ k := by
  have hrepr : w = ∑ i, inner ℝ (b i) w • b i := by
    conv_lhs => rw [← b.sum_repr w]
    simp only [OrthonormalBasis.repr_apply_apply]
  have hTw : (T ^ k) w = ∑ i, (inner ℝ (b i) w * ev i ^ k) • b i := by
    conv_lhs => rw [hrepr]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, pow_apply_eigen T (b i) (ev i) (hb i) k, smul_smul]
  rw [hTw]
  calc ‖∑ i, (inner ℝ (b i) w * ev i ^ k) • b i‖
      ≤ ∑ i, ‖(inner ℝ (b i) w * ev i ^ k) • b i‖ := norm_sum_le _ _
    _ ≤ ∑ i, |inner ℝ (b i) w| * μ ^ k := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul, b.orthonormal.1 i, mul_one, Real.norm_eq_abs, abs_mul, abs_pow]
        by_cases hi : i = i₀
        · rw [hi, hw]; simp
        · exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (abs_nonneg _) (hdom i hi) k) (abs_nonneg _)
    _ = (∑ i, |inner ℝ (b i) w|) * μ ^ k := by rw [Finset.sum_mul]

/-- The power method for any orthonormal basis of eigenvectors `b` with eigenvalues `ev`, and any
`μ ≥ 0` with `μ < |ev i₀|` and `|ev i| ≤ μ` for every index `i ≠ i₀`, and a start `x` with a
nonzero component along `b i₀`: the rate `(μ / |ev i₀|) ^ k` and the limit `b i₀`. -/
private lemma power_aux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (ev : Fin n → ℝ) (hb : ∀ i, T (b i) = ev i • b i) (i₀ : Fin n) (μ : ℝ)
    (hμ0 : 0 ≤ μ) (hgap : μ < |ev i₀|) (hdom : ∀ i, i ≠ i₀ → |ev i| ≤ μ)
    (x : E) (hx : inner ℝ (b i₀) x ≠ 0) :
    (∃ C : ℝ, ∀ k : ℕ,
      ‖(inner ℝ (b i₀) ((T ^ k) x))⁻¹ • (T ^ k) x - b i₀‖ ≤ C * (μ / |ev i₀|) ^ k) ∧
    Tendsto (fun k : ℕ => (inner ℝ (b i₀) ((T ^ k) x))⁻¹ • (T ^ k) x) atTop
      (𝓝 (b i₀)) := by
  obtain ⟨c, hc⟩ : ∃ c, c = inner ℝ (b i₀) x := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = x - c • b i₀ := ⟨_, rfl⟩
  have hu1 : inner ℝ (b i₀) (b i₀) = 1 := by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i₀]; norm_num
  have hw0 : inner ℝ (b i₀) w = 0 := by
    rw [hw, inner_sub_right, real_inner_smul_right, hu1, mul_one, ← hc, sub_self]
  have hx_dec : x = c • b i₀ + w := by rw [hw]; abel
  have hevpos : 0 < |ev i₀| := lt_of_le_of_lt hμ0 hgap
  have hev0 : ev i₀ ≠ 0 := by
    intro h; rw [h, abs_zero] at hevpos; exact lt_irrefl _ hevpos
  have hc0 : c ≠ 0 := by rw [hc]; exact hx
  have hinner : ∀ k : ℕ, inner ℝ (b i₀) ((T ^ k) x) = ev i₀ ^ k * c := fun k => by
    rw [inner_pow_apply hT (b i₀) (ev i₀) (hb i₀) x k, ← hc]
  have hd : ∀ k : ℕ, (inner ℝ (b i₀) ((T ^ k) x))⁻¹ • (T ^ k) x - b i₀
      = (ev i₀ ^ k * c)⁻¹ • (T ^ k) w := by
    intro k
    rw [hinner k]
    conv_lhs => rw [hx_dec]
    rw [map_add, map_smul, pow_apply_eigen T _ _ (hb i₀), smul_add, smul_smul, smul_smul]
    have hpk : ev i₀ ^ k ≠ 0 := pow_ne_zero _ hev0
    have h1 : (ev i₀ ^ k * c)⁻¹ * c * ev i₀ ^ k = 1 := by field_simp
    rw [h1, one_smul]
    abel
  set C : ℝ := (∑ i, |inner ℝ (b i) w|) / |c| with hC
  have habs_ev : |ev i₀| ≠ 0 := abs_ne_zero.mpr hev0
  have habs_c : |c| ≠ 0 := abs_ne_zero.mpr hc0
  have hbound : ∀ k : ℕ,
      ‖(inner ℝ (b i₀) ((T ^ k) x))⁻¹ • (T ^ k) x - b i₀‖ ≤ C * (μ / |ev i₀|) ^ k := by
    intro k
    rw [hd k, norm_smul, Real.norm_eq_abs, abs_inv, abs_mul, abs_pow]
    calc (|ev i₀| ^ k * |c|)⁻¹ * ‖(T ^ k) w‖
        ≤ (|ev i₀| ^ k * |c|)⁻¹ * ((∑ i, |inner ℝ (b i) w|) * μ ^ k) :=
          mul_le_mul_of_nonneg_left
            (norm_pow_apply_le T b ev hb i₀ μ hdom w hw0 k) (by positivity)
      _ = C * (μ / |ev i₀|) ^ k := by
          rw [hC, div_pow]
          field_simp
  refine ⟨⟨C, hbound⟩, ?_⟩
  have hr0 : 0 ≤ μ / |ev i₀| := div_nonneg hμ0 (abs_nonneg _)
  have hr1 : μ / |ev i₀| < 1 := (div_lt_one hevpos).mpr hgap
  have ht : Tendsto (fun k : ℕ => C * (μ / |ev i₀|) ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul C
  have h0 := squeeze_zero_norm
    (f := fun k : ℕ => (inner ℝ (b i₀) ((T ^ k) x))⁻¹ • (T ^ k) x - b i₀) hbound ht
  exact tendsto_sub_nhds_zero_iff.mp h0

/-- **The power method** (item 147 of MATH-PLAN-library-2). `T` is a symmetric linear map of a
finite-dimensional real inner product space of dimension `n`; `u = hT.eigenvectorBasis hn i₀` is
an eigenvector with eigenvalue `λ₀ = hT.eigenvalues hn i₀`, and `λ₁ = hT.eigenvalues hn i₁` is an
eigenvalue with `|λ₁| < |λ₀|` and `|hT.eigenvalues hn i| ≤ |λ₁|` for every index `i ≠ i₀` (so
`λ₀` is a simple eigenvalue). The iterates are `T ^ k` applied to the start vector `x`, rescaled
to unit component along `u`: `⟪u, (T ^ k) x⟫⁻¹ • (T ^ k) x`. If `x` has a nonzero component
along `u`, the rescaled iterates are within `C * (|λ₁| / |λ₀|) ^ k` of `u` for one `C` and every
`k`, and they tend to `u`. -/
theorem tendsto_powerIterate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (i₀ i₁ : Fin n)
    (hgap : |hT.eigenvalues hn i₁| < |hT.eigenvalues hn i₀|)
    (hdom : ∀ i, i ≠ i₀ → |hT.eigenvalues hn i| ≤ |hT.eigenvalues hn i₁|)
    (x : E) (hx : inner ℝ (hT.eigenvectorBasis hn i₀) x ≠ 0) :
    (∃ C : ℝ, ∀ k : ℕ,
      ‖(inner ℝ (hT.eigenvectorBasis hn i₀) ((T ^ k) x))⁻¹ • (T ^ k) x
          - hT.eigenvectorBasis hn i₀‖
        ≤ C * (|hT.eigenvalues hn i₁| / |hT.eigenvalues hn i₀|) ^ k) ∧
    Tendsto (fun k : ℕ =>
        (inner ℝ (hT.eigenvectorBasis hn i₀) ((T ^ k) x))⁻¹ • (T ^ k) x) atTop
      (𝓝 (hT.eigenvectorBasis hn i₀)) := by
  have hb : ∀ i, T (hT.eigenvectorBasis hn i)
      = hT.eigenvalues hn i • hT.eigenvectorBasis hn i := fun i => by
      simp
  exact power_aux hT (hT.eigenvectorBasis hn) (hT.eigenvalues hn) hb i₀
    |hT.eigenvalues hn i₁| (abs_nonneg _) hgap hdom x hx

end ClassicalLean.Analysis.PowerMethod

/-- The hypotheses of `tendsto_powerIterate` hold together: on the Euclidean plane
`EuclideanSpace ℝ (Fin 2)`, `T` is the symmetric map of the diagonal matrix `!![2, 0; 0, 1]`, whose
eigenvalues in Mathlib's order are `2` and `1` (`i₀ = 0` and `i₁ = 1`, so `|λ₁| < |λ₀|` and the
rate is `1 / 2`), and the start `x = (1, 1)` has a nonzero component along each eigenvector, so the
iterates do not start on the top eigenvector. -/
example := ClassicalLean.Analysis.PowerMethod.tendsto_powerIterate
    (E := EuclideanSpace ℝ (Fin 2))
    (T := Matrix.toEuclideanLin !![(2 : ℝ), 0; 0, 1])
    (hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr (by
      ext i j; fin_cases i <;> fin_cases j <;> simp))
    (hn := finrank_euclideanSpace_fin) (i₀ := 0) (i₁ := 1)
    (hgap := by
      have hsym : (Matrix.toEuclideanLin !![(2 : ℝ), 0; 0, 1]).IsSymmetric :=
        Matrix.isSymmetric_toEuclideanLin_iff.mpr (by
          ext i j; fin_cases i <;> fin_cases j <;> simp)
      have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := finrank_euclideanSpace_fin
      change |hsym.eigenvalues hn 1| < |hsym.eigenvalues hn 0|
      -- every eigenvalue is 2 or 1: the eigenvector equation, coordinate by coordinate
      have hval : ∀ i, hsym.eigenvalues hn i = 2 ∨ hsym.eigenvalues hn i = 1 := by
        intro i
        have h := hsym.apply_eigenvectorBasis hn i
        have hv0 := (hsym.eigenvectorBasis hn).orthonormal.ne_zero i
        generalize hsym.eigenvectorBasis hn i = v at h hv0
        generalize hsym.eigenvalues hn i = c at h ⊢
        have e0 := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) h
        have e1 := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 1) h
        simp only [Fin.isValue, Matrix.toEuclideanLin, Matrix.ofLp_toLpLin, Matrix.toLin'_apply,
            Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
            Matrix.cons_val_zero, Fin.sum_univ_two, Matrix.cons_val_one, zero_mul, add_zero,
            Real.ringHom_apply, PiLp.smul_apply, smul_eq_mul, mul_eq_mul_right_iff, one_mul,
            zero_add] at e0 e1
        by_contra hc
        obtain ⟨hc2, hc1⟩ := not_or.mp hc
        apply hv0
        ext j
        fin_cases j
        · simpa using e0.resolve_left (Ne.symm hc2)
        · have h1 : (1 - c) * v 1 = 0 := by
            linear_combination e1
          simpa [sub_ne_zero.mpr (Ne.symm hc1)] using h1
      -- the two eigenvalues add up to the trace, 3, and the first is the larger
      have htr := hsym.re_trace_eq_sum_eigenvalues hn
      rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis] at htr
      simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
          OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
          OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
          Matrix.ofLp_toLpLin,
          PiLp.ofLp_single, Matrix.toLin'_apply, Matrix.mulVec_single, MulOpposite.op_one,
          Pi.smul_apply, Matrix.col_apply, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_fin_one,
          one_smul, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
          RCLike.re_to_real] at htr
      have hanti := hsym.eigenvalues_antitone hn (show (0 : Fin 2) ≤ 1 by decide)
      rcases hval 0 with h0 | h0 <;> rcases hval 1 with h1 | h1
      · rw [h0, h1] at htr; norm_num at htr
      · rw [h0, h1]; norm_num
      · rw [h0, h1] at hanti; norm_num at hanti
      · rw [h0, h1] at htr; norm_num at htr)
    (hdom := by
      intro i hi
      fin_cases i
      · exact absurd rfl hi
      · exact le_rfl)
    (x := EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1)
    (hx := by
      have hsym : (Matrix.toEuclideanLin !![(2 : ℝ), 0; 0, 1]).IsSymmetric :=
        Matrix.isSymmetric_toEuclideanLin_iff.mpr (by
          ext i j; fin_cases i <;> fin_cases j <;> simp)
      have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := finrank_euclideanSpace_fin
      change inner ℝ (hsym.eigenvectorBasis hn 0)
        (EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1) ≠ 0
      intro hzero
      have h := hsym.apply_eigenvectorBasis hn 0
      have hv0 := (hsym.eigenvectorBasis hn).orthonormal.ne_zero 0
      generalize hsym.eigenvectorBasis hn 0 = v at h hv0 hzero
      generalize hsym.eigenvalues hn 0 = c at h
      have e0 := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) h
      have e1 := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 1) h
      simp only [Fin.isValue, Matrix.toEuclideanLin, Matrix.ofLp_toLpLin, Matrix.toLin'_apply,
          Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
          Matrix.cons_val_zero, Fin.sum_univ_two, Matrix.cons_val_one, zero_mul, add_zero,
          Real.ringHom_apply, PiLp.smul_apply, smul_eq_mul, mul_eq_mul_right_iff, one_mul,
          zero_add] at e0 e1
      simp [inner_add_right, EuclideanSpace.inner_single_right] at hzero
      apply hv0
      rcases e0 with hc | hz0
      · have hz1 : v 1 = 0 := by
          rw [← hc] at e1; linarith
        ext j; fin_cases j
        · simp; linarith
        · simpa using hz1
      · ext j; fin_cases j
        · simpa using hz0
        · simp; linarith)
