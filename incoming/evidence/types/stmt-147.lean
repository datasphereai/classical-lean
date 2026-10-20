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
order of the eigenvalues, only dominate the others in absolute value.

The proof. Write `x = c • u + w` with `c = ⟪u, x⟫ ≠ 0` and `⟪u, w⟫ = 0`. Then
`(T ^ k) u = λ₀ ^ k • u` (`pow_apply_eigen`) and `⟪u, (T ^ k) x⟫ = λ₀ ^ k * c` (`inner_pow_apply`,
from the symmetry of `T`), so the rescaled iterate minus `u` is `(λ₀ ^ k * c)⁻¹ • (T ^ k) w`.
Expanding `w` in the eigenvector basis, where its coefficient along `u` is `0`, gives
`‖(T ^ k) w‖ ≤ (∑ i, |⟪bᵢ, w⟫|) * |λ₁| ^ k` (`norm_pow_apply_le`), hence the bound with
`C = (∑ i, |⟪bᵢ, w⟫|) / |c|`; the rate `|λ₁| / |λ₀|` lies in `[0, 1)`, so the bound tends to `0`
(`power_aux`).

The proof is the draft `d147-r1-s2` (written by Claude Opus 5.5 through the Anthropic Batch API,
the lane's order API-CREDIT-1), adapted by the Claude Code cloud session that landed it (order
CLOUD-MATH-2): the namespace, targeted imports and docstrings, `change` where a `show` changed the
goal, and a `first` chain and a `try` cut to the step that fires. The witness at the end of the
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
  sorry

/-- For a symmetric `T` and an eigenvector `u` with eigenvalue `c`, the component of `(T ^ k) y`
along `u` is `c ^ k` times that of `y`. -/
private lemma inner_pow_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (u : E) (c : ℝ) (h : T u = c • u) (y : E)
    (k : ℕ) : inner ℝ u ((T ^ k) y) = c ^ k * inner ℝ u y := by
  sorry

/-- For `w` with no component along the basis vector `b i₀`, when every other eigenvalue is at
most `μ` in absolute value, `‖(T ^ k) w‖ ≤ (∑ i, |⟪b i, w⟫|) * μ ^ k`. -/
private lemma norm_pow_apply_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →ₗ[ℝ] E) {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (ev : Fin n → ℝ)
    (hb : ∀ i, T (b i) = ev i • b i) (i₀ : Fin n) (μ : ℝ)
    (hdom : ∀ i, i ≠ i₀ → |ev i| ≤ μ) (w : E) (hw : inner ℝ (b i₀) w = 0) (k : ℕ) :
    ‖(T ^ k) w‖ ≤ (∑ i, |inner ℝ (b i) w|) * μ ^ k := by
  sorry

/-- The power method for any orthonormal basis of eigenvectors `b` with eigenvalues `ev`, and any
`μ ≥ 0` with `μ < |ev i₀|` that bounds every other eigenvalue in absolute value, and a start `x`
with a nonzero component along `b i₀`: the rate `(μ / |ev i₀|) ^ k` and the limit `b i₀`. -/
private lemma power_aux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (ev : Fin n → ℝ) (hb : ∀ i, T (b i) = ev i • b i) (i₀ : Fin n) (μ : ℝ)
    (hμ0 : 0 ≤ μ) (hgap : μ < |ev i₀|) (hdom : ∀ i, i ≠ i₀ → |ev i| ≤ μ)
    (x : E) (hx : inner ℝ (b i₀) x ≠ 0) :
    (∃ C : ℝ, ∀ k : ℕ,
      ‖(inner ℝ (b i₀) ((T ^ k) x))⁻¹ • (T ^ k) x - b i₀‖ ≤ C * (μ / |ev i₀|) ^ k) ∧
    Tendsto (fun k : ℕ => (inner ℝ (b i₀) ((T ^ k) x))⁻¹ • (T ^ k) x) atTop
      (𝓝 (b i₀)) := by
  sorry

/-- **The power method** (item 147 of MATH-PLAN-library-2). `T` is a symmetric linear map of a
finite-dimensional real inner product space of dimension `n`; `u = hT.eigenvectorBasis hn i₀` is
an eigenvector with eigenvalue `λ₀ = hT.eigenvalues hn i₀`, and `λ₁ = hT.eigenvalues hn i₁` is an
eigenvalue with `|λ₁| < |λ₀|` that bounds every eigenvalue other than `λ₀` in absolute value. The
iterates are `T ^ k` applied to the start vector `x`, rescaled to unit component along `u`:
`⟪u, (T ^ k) x⟫⁻¹ • (T ^ k) x`. If `x` has a nonzero component along `u`, the rescaled iterates
are within `C * (|λ₁| / |λ₀|) ^ k` of `u` for one `C` and every `k`, and they tend to `u`. -/
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
  sorry

end ClassicalLean.Analysis.PowerMethod

set_option pp.fullNames true
#check @ClassicalLean.Analysis.PowerMethod.tendsto_powerIterate
