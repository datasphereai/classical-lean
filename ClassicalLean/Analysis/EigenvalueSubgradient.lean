/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Algebra.MinMax
import ClassicalLean.Analysis.SubgradientMethod

/-!
# Minimising the largest eigenvalue by the subgradient method

Bridge 171 of `MATH-PLAN-library-2-bridges-2.md` (order CLOUD-MATH-7), joining
`ClassicalLean.Algebra.MinMax` and `ClassicalLean.Analysis.SubgradientMethod`.

* `min_sub_le_of_subgradient_eigenvalues` — for symmetric maps `A₀, A 0, …, A (m - 1)` of a real
  inner product space of dimension `n + 1` and `f x = λ₀(A₀ + ∑ i, x i • A i)` on
  `EuclideanSpace ℝ (Fin m)`, the largest eigenvalue, the vector `g x = (⟪A i u, u⟫)ᵢ`, with `u`
  the unit eigenvector of `λ₀` (Mathlib's `eigenvectorBasis` at index `0`), is a subgradient of
  `f` at `x`, so the iterates `x (k + 1) = x k - η g (x k)` with `‖g‖ ≤ G` satisfy
  `min_{k < T} f (x k) - f z ≤ (‖x 0 - z‖² + η² G² T) / (2 η T)` for every `z`.

The proof. Write `T x = A₀ + ∑ i, x i • A i` and `u` for the unit eigenvector of `T x` at index
`0`. Courant–Fischer's bound at `k = 0`, `⟪T y u, u⟫ ≤ λ₀(T y) ‖u‖²` (`le_eigenvalues_mul_of_mem`;
the span of the eigenvectors from index `0` on is the whole space), and `T x u = λ₀(T x) u` give
`f y ≥ ⟪T y u, u⟫ = f x + ∑ i, (y i - x i) ⟪A i u, u⟫ = f x + ⟪g x, y - x⟫`, the hypothesis `hsub`
of `min_sub_le_of_subgradient` (SubgradientMethod), which then gives the bound.

The statement was written by order LEAN-38 (a reading order) and elaborated there stated without
a proof; this module proves it word for word.
-/

open scoped InnerProductSpace

namespace ClassicalLean.Analysis.EigenvalueSubgradient

/-- **Minimising the largest eigenvalue by the subgradient method.** For symmetric maps
`A₀, A 0, …, A (m - 1)` of a real inner product space `F` of dimension `n + 1`, let
`f x = λ₀(A₀ + ∑ i, x i • A i)`, the largest eigenvalue. With `u x` the unit eigenvector of that
eigenvalue (Mathlib's `eigenvectorBasis` at index `0`), the vector `g x = (⟪A i (u x), u x⟫)ᵢ` is
a subgradient of `f` at `x` (Courant–Fischer: `λ₀(T y) ≥ ⟪T y u, u⟫` for unit `u`), so the
subgradient method `x (k + 1) = x k - η g (x k)`, with `‖g‖ ≤ G`, has the rate of
`min_sub_le_of_subgradient`. Bridge 171 of `MATH-PLAN-library-2-bridges-2.md`. -/
theorem min_sub_le_of_subgradient_eigenvalues {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {n m : ℕ} (hn : Module.finrank ℝ F = n + 1)
    (A₀ : F →ₗ[ℝ] F) (A : Fin m → F →ₗ[ℝ] F)
    (hT : ∀ x : EuclideanSpace ℝ (Fin m), (A₀ + ∑ i, WithLp.ofLp x i • A i).IsSymmetric)
    (x : ℕ → EuclideanSpace ℝ (Fin m)) (z : EuclideanSpace ℝ (Fin m)) (η G : ℝ) (T : ℕ)
    (hη : 0 < η) (hTpos : 0 < T)
    (hg : ∀ k, ‖WithLp.toLp 2 (fun i ↦ ⟪A i ((hT (x k)).eigenvectorBasis hn 0),
        (hT (x k)).eigenvectorBasis hn 0⟫_ℝ)‖ ≤ G)
    (hstep : ∀ k, x (k + 1) = x k - η • WithLp.toLp 2 (fun i ↦
        ⟪A i ((hT (x k)).eigenvectorBasis hn 0), (hT (x k)).eigenvectorBasis hn 0⟫_ℝ)) :
    (Finset.range T).inf' ⟨0, Finset.mem_range.mpr hTpos⟩
        (fun k ↦ (hT (x k)).eigenvalues hn 0) - (hT z).eigenvalues hn 0 ≤
      (‖x 0 - z‖ ^ 2 + η ^ 2 * G ^ 2 * T) / (2 * η * T) := by
  refine ClassicalLean.Analysis.SubgradientMethod.min_sub_le_of_subgradient
    (fun y ↦ (hT y).eigenvalues hn 0) x
    (fun k ↦ WithLp.toLp 2 (fun i ↦ ⟪A i ((hT (x k)).eigenvectorBasis hn 0),
      (hT (x k)).eigenvectorBasis hn 0⟫_ℝ)) z η G T hη hTpos (fun k y ↦ ?_) hg hstep
  set u := (hT (x k)).eigenvectorBasis hn 0 with hu
  have hu1 : ‖u‖ = 1 := ((hT (x k)).eigenvectorBasis hn).norm_eq_one 0
  -- the quadratic form of `T w` at `u` is affine in `w`
  have hexp : ∀ w : EuclideanSpace ℝ (Fin m),
      ⟪(A₀ + ∑ i, WithLp.ofLp w i • A i) u, u⟫_ℝ =
        ⟪A₀ u, u⟫_ℝ + ∑ i, WithLp.ofLp w i * ⟪A i u, u⟫_ℝ := by
    intro w
    simp [LinearMap.add_apply, LinearMap.sum_apply, inner_add_left, sum_inner,
      real_inner_smul_left]
  -- Courant–Fischer at index `0`: the span of the eigenvectors from `0` on is the whole space
  have hmem : u ∈ ClassicalLean.MinMax.eigenSpan hn (hT y) (Finset.Ici 0) := by
    have hall : Finset.Ici (0 : Fin (n + 1)) = Finset.univ := by
      ext j
      simp
    rw [ClassicalLean.MinMax.eigenSpan, hall, Finset.coe_univ, Set.image_univ,
      ← OrthonormalBasis.coe_toBasis, Module.Basis.span_eq]
    exact Submodule.mem_top
  have hCF := ClassicalLean.MinMax.le_eigenvalues_mul_of_mem hn (hT y) hmem
  rw [hu1, one_pow, mul_one, RCLike.re_to_real] at hCF
  -- at `x k`, `u` is an eigenvector of the top eigenvalue
  have hev : (hT (x k)).eigenvalues hn 0 = ⟪(A₀ + ∑ i, WithLp.ofLp (x k) i • A i) u, u⟫_ℝ := by
    rw [hu, LinearMap.IsSymmetric.apply_eigenvectorBasis, ← hu, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hu1, one_pow, mul_one]
    rfl
  have hinner : ⟪WithLp.toLp 2 (fun i ↦ ⟪A i u, u⟫_ℝ), y - x k⟫_ℝ =
      ∑ i, WithLp.ofLp y i * ⟪A i u, u⟫_ℝ - ∑ i, WithLp.ofLp (x k) i * ⟪A i u, u⟫_ℝ := by
    rw [PiLp.inner_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [PiLp.sub_apply, RCLike.inner_apply, conj_trivial]
    ring
  change (hT (x k)).eigenvalues hn 0 + ⟪WithLp.toLp 2 (fun i ↦ ⟪A i u, u⟫_ℝ), y - x k⟫_ℝ ≤
    (hT y).eigenvalues hn 0
  rw [hinner, hev, hexp]
  rw [hexp] at hCF
  linarith

end ClassicalLean.Analysis.EigenvalueSubgradient

/-- The hypotheses of `min_sub_le_of_subgradient_eigenvalues` hold together: on the Euclidean plane
`F = EuclideanSpace ℝ (Fin 2)` (dimension `n + 1 = 2`), a family of `m = 2` maps,
`A₀ = diag(1, 0)`, `A 0 = diag(1, -1)` and `A 1 = diag(0, 1)`, so that
`T x = A₀ + x 0 • A 0 + x 1 • A 1 = diag(1 + x 0, -x 0 + x 1)` is symmetric for every `x`. For a
unit vector `u` with `b = u 1 ^ 2`, `g = (⟪A 0 u, u⟫, ⟪A 1 u, u⟫) = (1 - 2 b, b)` has
`‖g‖ ^ 2 = (1 - 2 b) ^ 2 + b ^ 2 ≤ 2 ≤ 4`, so `G = 2` bounds every `g`, whichever eigenvector the
basis picks. The step is `η = 1 / 2`, the horizon `T = 3`, the comparison point `z = 0`. The
iterates are defined by the recursion of `hstep` from `x 0 = (3/4, 0)`, so `hstep` holds by `rfl`.
They move at every step: `T (x 0) = diag(7/4, -3/4)`, whose top eigenvector is `e₀` up to sign, with
`g = (1, 0)`; `x 1 = (1/4, 0)` with `diag(5/4, -1/4)`; `x 2 = (-1/4, 0)` with `diag(3/4, 1/4)`;
`x 3 = (-3/4, 0)`. At each of `x 0`, `x 1`, `x 2` the top eigenvector is `e₀` up to sign,
`g = (1, 0)`, and the step moves the iterate by `(-1/2, 0)`. Inside the horizon the top eigenvalue
is never tied. -/
example :=
  ClassicalLean.Analysis.EigenvalueSubgradient.min_sub_le_of_subgradient_eigenvalues
    (F := EuclideanSpace ℝ (Fin 2)) (n := 1) (m := 2) (hn := finrank_euclideanSpace_fin)
    (A₀ := Matrix.toEuclideanLin (Matrix.diagonal ![1, 0]))
    (A := ![Matrix.toEuclideanLin (Matrix.diagonal ![1, -1]),
      Matrix.toEuclideanLin (Matrix.diagonal ![0, 1])])
    (hT := fun _ u v ↦ by
      simp [Fin.sum_univ_two, PiLp.inner_apply, Matrix.toEuclideanLin, Matrix.mulVec_diagonal]
      ring)
    (x := fun k ↦ Nat.rec (motive := fun _ ↦ EuclideanSpace ℝ (Fin 2)) (WithLp.toLp 2 ![3 / 4, 0])
      (fun _ y ↦ y - (1 / 2 : ℝ) • WithLp.toLp 2 (fun i ↦
        ⟪![Matrix.toEuclideanLin (Matrix.diagonal ![(1 : ℝ), -1]),
            Matrix.toEuclideanLin (Matrix.diagonal ![(0 : ℝ), 1])] i
          (LinearMap.IsSymmetric.eigenvectorBasis
            (T := Matrix.toEuclideanLin (Matrix.diagonal ![(1 : ℝ), 0]) +
              ∑ j, WithLp.ofLp y j • ![Matrix.toEuclideanLin (Matrix.diagonal ![(1 : ℝ), -1]),
                Matrix.toEuclideanLin (Matrix.diagonal ![(0 : ℝ), 1])] j)
            (fun u v ↦ by
              simp [Fin.sum_univ_two, PiLp.inner_apply, Matrix.toEuclideanLin,
                Matrix.mulVec_diagonal]
              ring)
            (finrank_euclideanSpace_fin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) 0),
          LinearMap.IsSymmetric.eigenvectorBasis
            (T := Matrix.toEuclideanLin (Matrix.diagonal ![(1 : ℝ), 0]) +
              ∑ j, WithLp.ofLp y j • ![Matrix.toEuclideanLin (Matrix.diagonal ![(1 : ℝ), -1]),
                Matrix.toEuclideanLin (Matrix.diagonal ![(0 : ℝ), 1])] j)
            (fun u v ↦ by
              simp [Fin.sum_univ_two, PiLp.inner_apply, Matrix.toEuclideanLin,
                Matrix.mulVec_diagonal]
              ring)
            (finrank_euclideanSpace_fin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1)
            0⟫_ℝ)) k)
    (z := 0) (η := 1 / 2) (G := 2) (T := 3) (by norm_num) (by norm_num)
    (fun _ ↦ by
      have key : ∀ u : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 →
          ‖WithLp.toLp 2 (fun i ↦ ⟪![Matrix.toEuclideanLin (Matrix.diagonal ![(1 : ℝ), -1]),
            Matrix.toEuclideanLin (Matrix.diagonal ![(0 : ℝ), 1])] i u, u⟫_ℝ)‖ ≤ 2 := by
        intro u h1
        rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_two] at h1
        rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)]
        simp [Fin.sum_univ_two, PiLp.inner_apply, Matrix.toEuclideanLin, Matrix.mulVec_diagonal]
        simp at h1
        nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
      exact key _ (OrthonormalBasis.norm_eq_one _ _))
    (fun _ ↦ rfl)
