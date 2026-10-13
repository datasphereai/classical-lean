/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Courant–Fischer min–max, Weyl's eigenvalue inequalities, and Ky Fan's maximum principle

`T` is a symmetric (self-adjoint) linear map on a finite-dimensional real or complex inner product
space `E` of dimension `n`; Mathlib's `hT.eigenvalues hn : Fin n → ℝ` lists its eigenvalues
`λ_0 ≥ λ_1 ≥ ⋯ ≥ λ_{n−1}`, largest first, counted from `0`. The *quadratic form* of `T` is
`x ↦ re ⟪T x, x⟫`.

* `eigenvalues_eq_iSup_iInf` — order LEAN-23, item 46, **Courant–Fischer**: `λ_k` is the largest,
  over subspaces `V` of dimension `k + 1`, of the least value of the quadratic form on the unit
  vectors of `V`. `eigenvalues_eq_iInf_iSup` is the min–max form, over dimension `n − k`.
* The same without suprema and infima, so without Lean's junk values (an empty `⨆` or `⨅` in `ℝ`
  is `0`): `exists_re_inner_le_eigenvalues` (every subspace of dimension `> k` has a unit `x`
  with value `≤ λ_k`), `exists_submodule_eigenvalues_le` (one of dimension `k + 1` has every
  value `≥ λ_k ‖x‖²`), and the two mirror images `exists_eigenvalues_le_re_inner`,
  `exists_submodule_le_eigenvalues`.
* `eigenvalues_add_le` — item 46, **Weyl's inequality**: for symmetric `S`, `T` and `i + j ≤ k`,
  `λ_k(S + T) ≤ λ_i(S) + λ_j(T)` (the case `k = i + j` is the textbook form, counted from `1` it
  reads `λ_{i+j−1}`). `eigenvalues_add_ge` is the other side: `λ_i(S) + λ_j(T) ≤ λ_k(S + T)`
  when `k + n ≤ i + j + 1`. Both take `hS` before `hT`, in the order of `S + T`.
* `eigenvalues_le_eigenvalues_add` — adding a positive semidefinite `T` lowers no eigenvalue
  (its hypothesis is the second half of Mathlib's `LinearMap.IsPositive`).
* `sum_eigenvalues_eq_iSup` — order LEAN-27, item 83, **Ky Fan's maximum principle**: for
  `k ≤ n`, `λ₀ + ⋯ + λ_{k−1}` is the largest value of `∑ᵢ re ⟪T uᵢ, uᵢ⟫` over orthonormal families
  `u₀, …, u_{k−1}`. Without the supremum: `sum_re_inner_le_sum_eigenvalues` (every orthonormal
  family is below) and `sum_re_inner_eigenvectorBasis` (the first `k` eigenvectors reach it). The
  proof: with `wⱼ = ∑ᵢ |⟪bⱼ, uᵢ⟫|²` in the eigenvector basis `b`, the sum is `∑ⱼ λⱼ wⱼ`; each
  `wⱼ ≤ 1` by Bessel's inequality over the orthonormal `u` (Mathlib's
  `Orthonormal.sum_inner_products_le`), `∑ⱼ wⱼ = k` since each `uᵢ` has norm `1`, and then
  `sum_mul_le_sum_of_antitone` (weights in `[0, 1]` summing to `k` put at most the `k` largest
  values). Needed, by exact cases in order LEAN-27's `checks.py`: for that lemma, `λ` decreasing
  (`λ = (0, 1)`, `w = (0, 1)`, `k = 1`: `1 > 0`), `w ≥ 0` (`λ = (1, 1, 0)`, `w = (1, 1, −1)`,
  `k = 1`: `2 > 1`; cold review r83 replaced a case that also broke `w ≤ 1`), `w ≤ 1`
  (`λ = (1, 0, 0)`, `w = (2, 0, 0)`, `k = 2`: `2 > 1`) and `∑ w = k` (`λ = (1, 1)`, `w = (1, 1)`,
  `k = 1`: `2 > 1`), each case keeping the other hypotheses (the script checks that); for the
  bound, orthonormality, both halves (`T = id` on `ℝ¹`, `u₀ = 2`: `4 > 1`; and `T = diag(1, 0)` on
  `ℝ²`, `k = 2`, `u₀ = u₁ = e₀`: `2 > 1`). `k ≤ n` is what lets the first `k` eigenvalues be named;
  with `k > n` there is no orthonormal family of `k` vectors, so a `⨆` over them would be over an
  empty type, which Lean sets to `0`. For a matrix, the sorted list is Mathlib's
  `Matrix.IsHermitian.eigenvalues₀` (`eigenvalues` is indexed through an arbitrary equivalence and
  is not sorted), and the bridge to this linear-map form is `Matrix.toEuclideanLin` (import
  `Mathlib.Analysis.Matrix.Spectrum`; take `hn := finrank_euclideanSpace` and
  `hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA`, and the left side is `hA.eigenvalues₀`;
  a note for item 142 of the plan, cold review r83).

The proof of Courant–Fischer and Weyl: in an orthonormal basis of eigenvectors,
`re ⟪T x, x⟫ = ∑ λᵢ |cᵢ|²` and `‖x‖² = ∑ |cᵢ|²` (`re_inner_eq_sum`, `norm_sq_eq_sum`), so the
span of the first `k + 1` eigenvectors has `re ⟪T x, x⟫ ≥ λ_k ‖x‖²` and the span of the last
`n − k` has `≤`. Two subspaces whose dimensions add up to more than `n` share a unit vector
(`exists_unit_mem_inf`, from `dim (V ⊔ W) + dim (V ⊓ W) = dim V + dim W`). Each theorem picks
such a vector in the right intersection.

## Hypotheses

Symmetry is not a hypothesis that can be dropped: Mathlib's `eigenvalues` needs it to be
defined. Measured in order LEAN-23's checks (`checks.py`; floating point, numpy, seeded): on
2000 random real symmetric `S`, `T` with `n ≤ 5` (the complex case is not checked), both forms
of Courant–Fischer (5 random subspaces per `k` and form, and the span of the first `k + 1`, or the
last `n − k`, eigenvectors reaching `λ_k`), both Weyl inequalities, and monotonicity under
`P = Y Yᵀ`. Small cases dropping a hypothesis, eigenvalues computed (`eigvalsh`): with
`k = i + j − 1`, `S = diag(1, 0)`, `T = diag(0, 1)`, `i = j = 1` give `λ_1(S + T) = 1 > 0 + 0`;
with `k` one higher than `i + j + 1 − n`, `S = diag(2, 0)`, `T = diag(0, 1)`, `i = 0`, `j = 1`,
`k = 1` give `2 > 1`; without `T ≥ 0`, `S = 0`, `T = (−1)` lowers `λ_0`; with dimension `k` in place
of `k + 1` in the max–min form, `k = 0` leaves only `V = ⊥`, whose `⨅` over no unit vectors is
Lean's `0`, not `λ_0` (`T = diag(2, 1)`: `0 ≠ 2`); without `k < dim V`, `V = ⊥` has no unit
vector.

Citations: Courant 1920, "Über die Eigenwerte bei den Differentialgleichungen der mathematischen
Physik"; Fischer 1905, "Über quadratische Formen mit reellen Koeffizienten"; Weyl 1912, "Das
asymptotische Verteilungsgesetz der Eigenwerte linearer partieller Differentialgleichungen".
Ky Fan 1949, "On a theorem of Weyl concerning eigenvalues of linear transformations I",
Proc. Nat. Acad. Sci. 35. None was read for this file.

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-23, `grep -rniE` over Mathlib): `courant` and
`fischer` 0 lines; `courant|fischer|minimax` 37 lines in 4 files: `minimaxRisk` (Bayes and
minimax risk), Sion's minimax theorem (`Topology/Sion.lean`) and saddle points
(`Order/SaddlePoint.lean`), none about eigenvalues (review r46);
`eigenvalues.*iInf|eigenvalues.*iSup` 0; `weyl.*(eigen|inequal)|eigenvalues_add` 0 (other "weyl"
hits are Weyl groups). Mathlib has `eigenvalues_antitone`, `eigenvectorBasis`,
`eigenvectorBasis_apply_self_apply` (used here), and `hasEigenvalue_iSup_of_finiteDimensional`,
`hasEigenvalue_iInf_of_finiteDimensional` (the supremum and infimum of the Rayleigh quotient
`re ⟪T x, x⟫ / ‖x‖²` are eigenvalues; with a bound they give the cases `k = 0` and `k = n − 1`;
not used).
Main lemmas used: `Submodule.finrank_sup_add_finrank_inf_eq`, `finrank_span_eq_card`,
`Basis.mem_span_image`, `norm_smul_inv_norm`, `PiLp.inner_apply`, `EuclideanSpace.norm_sq_eq`.
For Ky Fan (order LEAN-27, re-run by MATH-PLAN-library-2's check script and by cold review r83):
`ky fan|kyFan` 0 lines in pinned Mathlib and in Mathlib master at `2da3ab0a`, 0 in the library
before this item;
the nearest Mathlib fact is `Matrix.IsHermitian.trace_eq_sum_eigenvalues` (the case `k = n`, with
no supremum). Ky Fan's proof here uses Bessel's inequality (`Orthonormal.sum_inner_products_le`),
not Courant–Fischer.
-/

open Module LinearMap Submodule
open scoped InnerProductSpace

namespace ClassicalLean.MinMax

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} (hn : finrank 𝕜 E = n)

variable {S T : E →ₗ[𝕜] E} (hS : S.IsSymmetric) (hT : T.IsSymmetric)

/-- The quadratic form of `T` in its eigenvector basis: `re ⟪T x, x⟫ = ∑ λᵢ |cᵢ|²`. -/
theorem re_inner_eq_sum (x : E) :
    RCLike.re ⟪T x, x⟫_𝕜 =
      ∑ i, hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  rw [← (hT.eigenvectorBasis hn).repr.inner_map_map, PiLp.inner_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hT.eigenvectorBasis_apply_self_apply hn, RCLike.inner_apply, map_mul (starRingEnd 𝕜),
    RCLike.conj_ofReal, mul_left_comm, RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul,
    RCLike.ofReal_re]

omit [FiniteDimensional 𝕜 E] in
theorem norm_sq_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) (x : E) :
    ‖x‖ ^ 2 = ∑ i, ‖b.repr x i‖ ^ 2 := by
  rw [← b.repr.norm_map, EuclideanSpace.norm_sq_eq]

/-- The span of the eigenvectors with index in `s`. -/
noncomputable def eigenSpan (s : Finset (Fin n)) : Submodule 𝕜 E :=
  span 𝕜 (hT.eigenvectorBasis hn '' s)

theorem finrank_eigenSpan (s : Finset (Fin n)) : finrank 𝕜 (eigenSpan hn hT s) = s.card := by
  rw [eigenSpan, Set.image_eq_range, finrank_span_eq_card]
  · simp
  · exact (hT.eigenvectorBasis hn).orthonormal.linearIndependent.comp _ Subtype.val_injective

theorem repr_eq_zero_of_mem_eigenSpan {s : Finset (Fin n)} {x : E} (hx : x ∈ eigenSpan hn hT s)
    {i : Fin n} (hi : i ∉ s) : (hT.eigenvectorBasis hn).repr x i = 0 := by
  rw [eigenSpan, ← OrthonormalBasis.coe_toBasis, Basis.mem_span_image] at hx
  have := mt (fun h ↦ hx (Finsupp.mem_support_iff.mpr h)) hi
  simpa using this

theorem eigenvectorBasis_mem_eigenSpan {s : Finset (Fin n)} {i : Fin n} (hi : i ∈ s) :
    hT.eigenvectorBasis hn i ∈ eigenSpan hn hT s :=
  subset_span ⟨i, hi, rfl⟩

/-- On the span of the first `k + 1` eigenvectors, `re ⟪T x, x⟫ ≥ λ_k ‖x‖²`. -/
theorem eigenvalues_mul_le_of_mem {k : Fin n} {x : E}
    (hx : x ∈ eigenSpan hn hT (Finset.Iic k)) :
    hT.eigenvalues hn k * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  rw [re_inner_eq_sum hn hT, norm_sq_eq_sum (hT.eigenvectorBasis hn), Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  by_cases hi : i ≤ k
  · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn hi) (by positivity)
  · rw [repr_eq_zero_of_mem_eigenSpan hn hT hx (by simpa using hi)]
    simp

/-- On the span of the eigenvectors from index `k` on, `re ⟪T x, x⟫ ≤ λ_k ‖x‖²`. -/
theorem le_eigenvalues_mul_of_mem {k : Fin n} {x : E}
    (hx : x ∈ eigenSpan hn hT (Finset.Ici k)) :
    RCLike.re ⟪T x, x⟫_𝕜 ≤ hT.eigenvalues hn k * ‖x‖ ^ 2 := by
  rw [re_inner_eq_sum hn hT, norm_sq_eq_sum (hT.eigenvectorBasis hn), Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  by_cases hi : k ≤ i
  · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn hi) (by positivity)
  · rw [repr_eq_zero_of_mem_eigenSpan hn hT hx (by simpa using hi)]
    simp

/-- Two subspaces whose dimensions add up to more than `dim E` share a unit vector. -/
theorem exists_unit_mem_inf (V W : Submodule 𝕜 E)
    (h : finrank 𝕜 E < finrank 𝕜 V + finrank 𝕜 W) : ∃ x ∈ V, x ∈ W ∧ ‖x‖ = 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq V W
  have h2 := Submodule.finrank_le (V ⊔ W)
  have hne : V ⊓ W ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at h1
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨((‖x‖ : 𝕜)⁻¹) • x, V.smul_mem _ hx.1, W.smul_mem _ hx.2, norm_smul_inv_norm hx0⟩

/-- `|re ⟪T x, x⟫| ≤ (∑ᵢ |λᵢ|) ‖x‖²`: the quadratic form is bounded on the unit sphere. -/
theorem abs_re_inner_le (x : E) :
    |RCLike.re ⟪T x, x⟫_𝕜| ≤ (∑ i, |hT.eigenvalues hn i|) * ‖x‖ ^ 2 := by
  rw [re_inner_eq_sum hn hT, norm_sq_eq_sum (hT.eigenvectorBasis hn), Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg _) 2)]
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (f := fun i ↦ |hT.eigenvalues hn i|) (fun _ _ ↦ abs_nonneg _)
      (Finset.mem_univ i)) (pow_nonneg (norm_nonneg _) 2)

/-- Every subspace of dimension more than `k` holds a unit vector `x` with
`re ⟪T x, x⟫ ≤ λ_k`. -/
theorem exists_re_inner_le_eigenvalues (k : Fin n) (V : Submodule 𝕜 E)
    (hV : k.val < finrank 𝕜 V) :
    ∃ x ∈ V, ‖x‖ = 1 ∧ RCLike.re ⟪T x, x⟫_𝕜 ≤ hT.eigenvalues hn k := by
  obtain ⟨x, hxV, hxW, hx1⟩ := exists_unit_mem_inf V (eigenSpan hn hT (Finset.Ici k))
    (by rw [hn, finrank_eigenSpan, Fin.card_Ici]; omega)
  refine ⟨x, hxV, hx1, ?_⟩
  simpa [hx1] using le_eigenvalues_mul_of_mem hn hT hxW

/-- Every subspace of dimension at least `n − k` holds a unit vector `x` with
`λ_k ≤ re ⟪T x, x⟫`. -/
theorem exists_eigenvalues_le_re_inner (k : Fin n) (V : Submodule 𝕜 E)
    (hV : n - k.val ≤ finrank 𝕜 V) :
    ∃ x ∈ V, ‖x‖ = 1 ∧ hT.eigenvalues hn k ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  obtain ⟨x, hxV, hxW, hx1⟩ := exists_unit_mem_inf V (eigenSpan hn hT (Finset.Iic k))
    (by rw [hn, finrank_eigenSpan, Fin.card_Iic]; omega)
  refine ⟨x, hxV, hx1, ?_⟩
  simpa [hx1] using eigenvalues_mul_le_of_mem hn hT hxW

/-- The span of the first `k + 1` eigenvectors has dimension `k + 1`, and on it
`re ⟪T x, x⟫ ≥ λ_k ‖x‖²`. -/
theorem exists_submodule_eigenvalues_le (k : Fin n) :
    ∃ V : Submodule 𝕜 E, finrank 𝕜 V = k.val + 1 ∧
      ∀ x ∈ V, hT.eigenvalues hn k * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜 :=
  ⟨eigenSpan hn hT (Finset.Iic k), by rw [finrank_eigenSpan, Fin.card_Iic],
    fun _ hx ↦ eigenvalues_mul_le_of_mem hn hT hx⟩

/-- The span of the eigenvectors from index `k` on has dimension `n − k`, and on it
`re ⟪T x, x⟫ ≤ λ_k ‖x‖²`. -/
theorem exists_submodule_le_eigenvalues (k : Fin n) :
    ∃ V : Submodule 𝕜 E, finrank 𝕜 V = n - k.val ∧
      ∀ x ∈ V, RCLike.re ⟪T x, x⟫_𝕜 ≤ hT.eigenvalues hn k * ‖x‖ ^ 2 :=
  ⟨eigenSpan hn hT (Finset.Ici k), by rw [finrank_eigenSpan, Fin.card_Ici],
    fun _ hx ↦ le_eigenvalues_mul_of_mem hn hT hx⟩

/-- **Courant–Fischer, max–min form.** `λ_k` is the largest, over subspaces `V` of dimension
`k + 1`, of the least value of `re ⟪T x, x⟫` on the unit vectors of `V`. -/
theorem eigenvalues_eq_iSup_iInf (k : Fin n) :
    hT.eigenvalues hn k =
      ⨆ V : {V : Submodule 𝕜 E // finrank 𝕜 V = k.val + 1},
        ⨅ x : {x : E // x ∈ V.1 ∧ ‖x‖ = 1}, RCLike.re ⟪T x, x⟫_𝕜 := by
  set B := ∑ i, |hT.eigenvalues hn i|
  have hbdd (V : Submodule 𝕜 E) :
      BddBelow (Set.range fun x : {x : E // x ∈ V ∧ ‖x‖ = 1} ↦ RCLike.re ⟪T x, x⟫_𝕜) := by
    refine ⟨-B, ?_⟩
    rintro _ ⟨x, rfl⟩
    have := abs_re_inner_le hn hT x
    rw [x.2.2, one_pow, mul_one] at this
    exact neg_le_of_abs_le this
  have hle (V : {V : Submodule 𝕜 E // finrank 𝕜 V = k.val + 1}) :
      ⨅ x : {x : E // x ∈ V.1 ∧ ‖x‖ = 1}, RCLike.re ⟪T x, x⟫_𝕜 ≤ hT.eigenvalues hn k := by
    obtain ⟨x, hxV, hx1, hx⟩ := exists_re_inner_le_eigenvalues hn hT k V.1 (by omega)
    exact (ciInf_le (hbdd V.1) ⟨x, hxV, hx1⟩).trans hx
  obtain ⟨V₀, hV₀, hV₀le⟩ := exists_submodule_eigenvalues_le hn hT k
  obtain ⟨y, hyV, hy1, -⟩ := exists_re_inner_le_eigenvalues hn hT k V₀ (by omega)
  have hge : hT.eigenvalues hn k ≤
      ⨅ x : {x : E // x ∈ V₀ ∧ ‖x‖ = 1}, RCLike.re ⟪T x, x⟫_𝕜 := by
    have : Nonempty {x : E // x ∈ V₀ ∧ ‖x‖ = 1} := ⟨⟨y, hyV, hy1⟩⟩
    exact le_ciInf fun x ↦ by simpa [x.2.2] using hV₀le x x.2.1
  have : Nonempty {V : Submodule 𝕜 E // finrank 𝕜 V = k.val + 1} := ⟨⟨V₀, hV₀⟩⟩
  refine le_antisymm (hge.trans ?_) (ciSup_le hle)
  exact le_ciSup (f := fun V : {V : Submodule 𝕜 E // finrank 𝕜 V = k.val + 1} ↦
    ⨅ x : {x : E // x ∈ V.1 ∧ ‖x‖ = 1}, RCLike.re ⟪T x, x⟫_𝕜)
    ⟨hT.eigenvalues hn k, by rintro _ ⟨V, rfl⟩; exact hle V⟩ ⟨V₀, hV₀⟩

/-- **Courant–Fischer, min–max form.** `λ_k` is the least, over subspaces `V` of dimension
`n − k`, of the largest value of `re ⟪T x, x⟫` on the unit vectors of `V`. -/
theorem eigenvalues_eq_iInf_iSup (k : Fin n) :
    hT.eigenvalues hn k =
      ⨅ V : {V : Submodule 𝕜 E // finrank 𝕜 V = n - k.val},
        ⨆ x : {x : E // x ∈ V.1 ∧ ‖x‖ = 1}, RCLike.re ⟪T x, x⟫_𝕜 := by
  set B := ∑ i, |hT.eigenvalues hn i|
  have hbdd (V : Submodule 𝕜 E) :
      BddAbove (Set.range fun x : {x : E // x ∈ V ∧ ‖x‖ = 1} ↦ RCLike.re ⟪T x, x⟫_𝕜) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨x, rfl⟩
    have := abs_re_inner_le hn hT x
    rw [x.2.2, one_pow, mul_one] at this
    exact le_of_abs_le this
  have hge (V : {V : Submodule 𝕜 E // finrank 𝕜 V = n - k.val}) :
      hT.eigenvalues hn k ≤ ⨆ x : {x : E // x ∈ V.1 ∧ ‖x‖ = 1}, RCLike.re ⟪T x, x⟫_𝕜 := by
    obtain ⟨x, hxV, hx1, hx⟩ := exists_eigenvalues_le_re_inner hn hT k V.1 (by omega)
    exact hx.trans (le_ciSup (hbdd V.1) ⟨x, hxV, hx1⟩)
  obtain ⟨W₀, hW₀, hW₀le⟩ := exists_submodule_le_eigenvalues hn hT k
  obtain ⟨y, hyW, hy1, -⟩ := exists_eigenvalues_le_re_inner hn hT k W₀ (by omega)
  have hle : ⨆ x : {x : E // x ∈ W₀ ∧ ‖x‖ = 1}, RCLike.re ⟪T x, x⟫_𝕜 ≤
      hT.eigenvalues hn k := by
    have : Nonempty {x : E // x ∈ W₀ ∧ ‖x‖ = 1} := ⟨⟨y, hyW, hy1⟩⟩
    exact ciSup_le fun x ↦ by simpa [x.2.2] using hW₀le x x.2.1
  have : Nonempty {V : Submodule 𝕜 E // finrank 𝕜 V = n - k.val} := ⟨⟨W₀, hW₀⟩⟩
  refine le_antisymm (le_ciInf hge) (le_trans ?_ hle)
  exact ciInf_le (f := fun V : {V : Submodule 𝕜 E // finrank 𝕜 V = n - k.val} ↦
    ⨆ x : {x : E // x ∈ V.1 ∧ ‖x‖ = 1}, RCLike.re ⟪T x, x⟫_𝕜)
    ⟨hT.eigenvalues hn k, by rintro _ ⟨V, rfl⟩; exact hge V⟩ ⟨W₀, hW₀⟩

omit [FiniteDimensional 𝕜 E] in
theorem re_inner_add_apply (x : E) :
    RCLike.re ⟪(S + T) x, x⟫_𝕜 = RCLike.re ⟪S x, x⟫_𝕜 + RCLike.re ⟪T x, x⟫_𝕜 := by
  rw [LinearMap.add_apply, inner_add_left, map_add]

/-- **Weyl's inequality.** For symmetric `S`, `T` and `i + j ≤ k`,
`λ_k(S + T) ≤ λ_i(S) + λ_j(T)` (eigenvalues in decreasing order, counted from `0`). -/
theorem eigenvalues_add_le (i j k : Fin n) (h : i.val + j.val ≤ k.val) :
    (hS.add hT).eigenvalues hn k ≤ hS.eigenvalues hn i + hT.eigenvalues hn j := by
  set U := eigenSpan hn hS (Finset.Ici i)
  set W := eigenSpan hn hT (Finset.Ici j)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U W
  have h2 := Submodule.finrank_le (U ⊔ W)
  rw [finrank_eigenSpan, finrank_eigenSpan, Fin.card_Ici, Fin.card_Ici] at h1
  obtain ⟨x, hx, hx1, hle⟩ :=
    exists_eigenvalues_le_re_inner hn (hS.add hT) k (U ⊓ W) (by omega)
  have hU := le_eigenvalues_mul_of_mem hn hS (Submodule.mem_inf.mp hx).1
  have hW := le_eigenvalues_mul_of_mem hn hT (Submodule.mem_inf.mp hx).2
  rw [hx1, one_pow, mul_one] at hU hW
  rw [re_inner_add_apply] at hle
  linarith

/-- **Weyl's inequality, other side.** For symmetric `S`, `T` and `k + n ≤ i + j + 1`,
`λ_i(S) + λ_j(T) ≤ λ_k(S + T)`. -/
theorem eigenvalues_add_ge (i j k : Fin n) (h : k.val + n ≤ i.val + j.val + 1) :
    hS.eigenvalues hn i + hT.eigenvalues hn j ≤ (hS.add hT).eigenvalues hn k := by
  set U := eigenSpan hn hS (Finset.Iic i)
  set W := eigenSpan hn hT (Finset.Iic j)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U W
  have h2 := Submodule.finrank_le (U ⊔ W)
  rw [finrank_eigenSpan, finrank_eigenSpan, Fin.card_Iic, Fin.card_Iic] at h1
  obtain ⟨x, hx, hx1, hle⟩ :=
    exists_re_inner_le_eigenvalues hn (hS.add hT) k (U ⊓ W) (by omega)
  have hU := eigenvalues_mul_le_of_mem hn hS (Submodule.mem_inf.mp hx).1
  have hW := eigenvalues_mul_le_of_mem hn hT (Submodule.mem_inf.mp hx).2
  rw [hx1, one_pow, mul_one] at hU hW
  rw [re_inner_add_apply] at hle
  linarith

/-- Adding a positive semidefinite `T` (`re ⟪T x, x⟫ ≥ 0` for all `x`; with symmetry this is
Mathlib's `LinearMap.IsPositive`) does not lower any eigenvalue: `λ_k(S) ≤ λ_k(S + T)`. -/
theorem eigenvalues_le_eigenvalues_add (hT0 : ∀ x, 0 ≤ RCLike.re ⟪T x, x⟫_𝕜) (k : Fin n) :
    hS.eigenvalues hn k ≤ (hS.add hT).eigenvalues hn k := by
  obtain ⟨x, hx, hx1, hle⟩ := exists_re_inner_le_eigenvalues hn (hS.add hT) k
    (eigenSpan hn hS (Finset.Iic k)) (by rw [finrank_eigenSpan, Fin.card_Iic]; omega)
  have hU := eigenvalues_mul_le_of_mem hn hS hx
  rw [hx1, one_pow, mul_one] at hU
  rw [re_inner_add_apply] at hle
  linarith [hT0 x]

/-! ### Ky Fan's maximum principle (order LEAN-27, item 83) -/

/-- Weights in `[0, 1]` summing to `k` put at most the `k` largest values: for `λ` decreasing,
`∑ λⱼ wⱼ ≤ λ₀ + ⋯ + λ_{k−1}`. -/
theorem sum_mul_le_sum_of_antitone {N : ℕ} {lam w : Fin N → ℝ} (hlam : Antitone lam)
    (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∀ j, w j ≤ 1) {k : ℕ} (hk : k ≤ N) (hsum : ∑ j, w j = k) :
    ∑ j, lam j * w j ≤ ∑ i : Fin k, lam (Fin.castLE hk i) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have hw : ∀ j, w j = 0 := fun j ↦ by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ hw0 j).mp (by simpa using hsum) j
      exact this (Finset.mem_univ j)
    simp [hw]
  set S : Finset (Fin N) := Finset.univ.image (Fin.castLE hk) with hSdef
  have hmem : ∀ j : Fin N, j ∈ S ↔ (j : ℕ) < k := fun j ↦ by
    simp only [hSdef, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ ↦ hi ▸ i.isLt, fun h ↦ ⟨⟨j, h⟩, rfl⟩⟩
  have hcard : (S.card : ℝ) = k := by
    rw [hSdef, Finset.card_image_of_injective _ (Fin.castLE_injective hk)]
    simp
  have hRHS : ∑ i : Fin k, lam (Fin.castLE hk i) = ∑ j ∈ S, lam j := by
    rw [hSdef, Finset.sum_image fun a _ b _ h ↦ Fin.castLE_injective hk h]
  set c := lam ⟨k - 1, by omega⟩
  have hin : ∀ j ∈ S, c ≤ lam j := fun j hj ↦
    hlam (Fin.mk_le_mk.mpr (by have := (hmem j).mp hj; omega) : j ≤ ⟨k - 1, by omega⟩)
  have hout : ∀ j ∈ Sᶜ, lam j ≤ c := fun j hj ↦ by
    have : ¬ (j : ℕ) < k := fun h ↦ (Finset.mem_compl.mp hj) ((hmem j).mpr h)
    exact hlam (Fin.mk_le_mk.mpr (by omega) : (⟨k - 1, by omega⟩ : Fin N) ≤ j)
  have h1 : ∑ j ∈ Sᶜ, lam j * w j ≤ ∑ j ∈ Sᶜ, c * w j :=
    Finset.sum_le_sum fun j hj ↦ mul_le_mul_of_nonneg_right (hout j hj) (hw0 j)
  have h2 : ∑ j ∈ S, c * (1 - w j) ≤ ∑ j ∈ S, lam j * (1 - w j) :=
    Finset.sum_le_sum fun j hj ↦ mul_le_mul_of_nonneg_right (hin j hj) (sub_nonneg.2 (hw1 j))
  have h3 : ∑ j ∈ S, w j + ∑ j ∈ Sᶜ, w j = k := by rw [Finset.sum_add_sum_compl, hsum]
  rw [← Finset.sum_add_sum_compl S (fun j ↦ lam j * w j), hRHS]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, ← Finset.mul_sum] at h1 h2
  rw [Finset.sum_const, nsmul_eq_mul, hcard] at h2
  have h4 : ∑ j ∈ Sᶜ, w j = k - ∑ j ∈ S, w j := by linarith
  rw [h4, mul_sub] at h1
  linarith

/-- **Ky Fan, the bound.** For every orthonormal family `u₀, …, u_{k−1}`, `k ≤ n`:
`∑ᵢ re ⟪T uᵢ, uᵢ⟫ ≤ λ₀ + ⋯ + λ_{k−1}`. -/
theorem sum_re_inner_le_sum_eigenvalues {k : ℕ} (hk : k ≤ n) {u : Fin k → E}
    (hu : Orthonormal 𝕜 u) :
    ∑ i, RCLike.re ⟪T (u i), u i⟫_𝕜 ≤ ∑ i : Fin k, hT.eigenvalues hn (Fin.castLE hk i) := by
  set b := hT.eigenvectorBasis hn
  set w : Fin n → ℝ := fun j ↦ ∑ i, ‖b.repr (u i) j‖ ^ 2
  have hsum : ∑ i, RCLike.re ⟪T (u i), u i⟫_𝕜 = ∑ j, hT.eigenvalues hn j * w j := by
    simp only [re_inner_eq_sum hn hT, w, Finset.mul_sum]
    exact Finset.sum_comm
  have hw0 : ∀ j, 0 ≤ w j := fun j ↦ Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hw1 : ∀ j, w j ≤ 1 := fun j ↦ by
    have := hu.sum_inner_products_le (x := b j) (s := Finset.univ)
    rw [b.orthonormal.1 j, one_pow] at this
    refine le_trans (le_of_eq ?_) this
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [b.repr_apply_apply, norm_inner_symm]
  have hw : ∑ j, w j = k := by
    simp only [w]
    rw [Finset.sum_comm]
    simp [← norm_sq_eq_sum, hu.1]
  rw [hsum]
  exact sum_mul_le_sum_of_antitone (hT.eigenvalues_antitone hn) hw0 hw1 hk hw

/-- **Ky Fan, reached** at the first `k` eigenvectors. -/
theorem sum_re_inner_eigenvectorBasis {k : ℕ} (hk : k ≤ n) :
    ∑ i : Fin k, RCLike.re ⟪T (hT.eigenvectorBasis hn (Fin.castLE hk i)),
        hT.eigenvectorBasis hn (Fin.castLE hk i)⟫_𝕜 =
      ∑ i : Fin k, hT.eigenvalues hn (Fin.castLE hk i) := by
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hT.apply_eigenvectorBasis, inner_smul_left, inner_self_eq_norm_sq_to_K,
    (hT.eigenvectorBasis hn).orthonormal.1]
  simp

/-- **Ky Fan's maximum principle** (order LEAN-27, item 83): for `k ≤ n`, the sum of the `k`
largest eigenvalues of `T` is the largest value of `∑ᵢ re ⟪T uᵢ, uᵢ⟫` over orthonormal families
`u₀, …, u_{k−1}`. The supremum is over a nonempty family bounded above, so it is a true maximum,
not Lean's junk `0`. -/
theorem sum_eigenvalues_eq_iSup {k : ℕ} (hk : k ≤ n) :
    ∑ i : Fin k, hT.eigenvalues hn (Fin.castLE hk i) =
      ⨆ u : {u : Fin k → E // Orthonormal 𝕜 u}, ∑ i, RCLike.re ⟪T (u.1 i), u.1 i⟫_𝕜 := by
  have hv : Orthonormal 𝕜 (hT.eigenvectorBasis hn ∘ Fin.castLE hk) :=
    (hT.eigenvectorBasis hn).orthonormal.comp _ (Fin.castLE_injective hk)
  have : Nonempty {u : Fin k → E // Orthonormal 𝕜 u} := ⟨⟨_, hv⟩⟩
  refine le_antisymm ?_ (ciSup_le fun u ↦ sum_re_inner_le_sum_eigenvalues hn hT hk u.2)
  refine le_ciSup_of_le ⟨_, Set.forall_mem_range.mpr fun u ↦
    sum_re_inner_le_sum_eigenvalues hn hT hk u.2⟩ ⟨_, hv⟩ ?_
  exact (sum_re_inner_eigenvectorBasis hn hT hk).ge

/-- The hypotheses of `sum_mul_le_sum_of_antitone` can be met together. -/
example : ∃ (lam w : Fin 2 → ℝ), Antitone lam ∧ (∀ j, 0 ≤ w j) ∧ (∀ j, w j ≤ 1) ∧ 1 ≤ 2 ∧
    ∑ j, w j = (1 : ℕ) :=
  ⟨0, fun _ ↦ 1 / 2, antitone_const, fun _ ↦ by norm_num, fun _ ↦ by norm_num, by norm_num,
    by simp⟩

/-- The hypotheses of `sum_re_inner_le_sum_eigenvalues` and `sum_eigenvalues_eq_iSup` can be met
together: the identity on `ℝ²`, `k = 1`, `u₀` the first standard basis vector. -/
example : ∃ (T : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
    (u : Fin 1 → EuclideanSpace ℝ (Fin 2)), T.IsSymmetric ∧
      finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 ∧ 1 ≤ 2 ∧ Orthonormal ℝ u :=
  ⟨LinearMap.id, EuclideanSpace.basisFun (Fin 2) ℝ ∘ Fin.castLE (by norm_num),
    LinearMap.IsSymmetric.id, finrank_euclideanSpace_fin, by norm_num,
    (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.comp _ (Fin.castLE_injective _)⟩

/-- Ky Fan applied on a concrete space, every type given (cold review r83): the identity on
`ℝ²`, `k = 1`. -/
example := sum_eigenvalues_eq_iSup (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 2))
  finrank_euclideanSpace_fin LinearMap.IsSymmetric.id (k := 1) (by norm_num)

end ClassicalLean.MinMax
