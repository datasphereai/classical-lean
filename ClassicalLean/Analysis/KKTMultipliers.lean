/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Analysis.GradientDescent
import ClassicalLean.Analysis.KKT

/-!
# One multiplier vector serves every minimiser

Bridge 168 of `MATH-PLAN-library-2-bridges-2.md` (order CLOUD-MATH-7), joining
`ClassicalLean.Analysis.GradientDescent` and `ClassicalLean.Analysis.KKT`.

* `exists_multipliers_isMinOn_iff` — for a convex, differentiable problem on a real Hilbert space
  (minimise `f x` subject to `g i x ≤ 0`) with a Slater point and a feasible minimiser `xbar`,
  there is `w ≥ 0` such that, for every `y`, `y` is a feasible minimiser exactly when `y` is
  feasible, `w i * g i y = 0` for every `i` and `f' y + ∑ i, w i • g' i y = 0`. The KKT conditions
  are necessary in `Analysis.KKT` (`exists_kkt_of_slater`) and sufficient in
  `Analysis.GradientDescent` (`isMinOn_of_kkt`); here one `w`, found at `xbar`, works at every
  minimiser.

The proof. `exists_kkt_of_slater` gives `w ≥ 0` with complementary slackness and stationarity at
`xbar`. The Lagrangian `L = f + ∑ i, w i * g i` is convex with gradient `0` at `xbar`, so by
`add_inner_gradient_le` it is at least `L xbar = f xbar` everywhere. At a feasible minimiser `y`,
`f y = f xbar`, so `∑ i, w i * g i y ≥ 0` while every term is `≤ 0`: each is `0`. Then `y`
minimises `L` too, and its gradient vanishes there (`IsLocalMin.hasFDerivAt_eq_zero`). The converse
is `isMinOn_of_kkt`.

The statement was written by order LEAN-38 (a reading order) and elaborated there stated without
a proof; this module proves it word for word.
-/

open scoped RealInnerProductSpace

namespace ClassicalLean.Analysis.KKTMultipliers

/-- Under Slater's condition one multiplier vector serves every minimiser: there is `w ≥ 0` such
that the minimisers of a convex, differentiable problem are exactly the feasible points where `w`
satisfies complementary slackness and stationarity. Bridge 168 of
`MATH-PLAN-library-2-bridges-2.md`. -/
theorem exists_multipliers_isMinOn_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] {f : E → ℝ} {g : ι → E → ℝ} {f' : E → E}
    {g' : ι → E → E} {xbar : E} (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hf' : ∀ x, HasGradientAt f (f' x) x) (hg' : ∀ i x, HasGradientAt (g i) (g' i x) x)
    (hslater : ∃ x0, ∀ i, g i x0 < 0) (hxbar : ∀ i, g i xbar ≤ 0)
    (hmin : IsMinOn f {x | ∀ i, g i x ≤ 0} xbar) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ ∀ y : E,
      ((∀ i, g i y ≤ 0) ∧ IsMinOn f {x | ∀ i, g i x ≤ 0} y) ↔
        ((∀ i, g i y ≤ 0) ∧ (∀ i, w i * g i y = 0) ∧ f' y + ∑ i, w i • g' i y = 0) := by
  obtain ⟨w, hw0, hslack, hstat⟩ := ClassicalLean.Analysis.KKT.exists_kkt_of_slater hf hg
    (hf' xbar) (fun i ↦ hg' i xbar) hslater hxbar hmin
  -- the Lagrangian `f + ∑ i, w i * g i` lies above `f xbar` everywhere
  have hL : ∀ z, f xbar ≤ f z + ∑ i, w i * g i z := by
    intro z
    have h0 := ClassicalLean.Analysis.add_inner_gradient_le hf (Set.mem_univ xbar)
      (Set.mem_univ z) (hf' xbar)
    have hi : ∀ i, w i * g i xbar + w i * ⟪g' i xbar, z - xbar⟫ ≤ w i * g i z := fun i ↦ by
      have := ClassicalLean.Analysis.add_inner_gradient_le (hg i) (Set.mem_univ xbar)
        (Set.mem_univ z) (hg' i xbar)
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left this (hw0 i)
    rw [eq_neg_of_add_eq_zero_left hstat, inner_neg_left, sum_inner] at h0
    simp only [real_inner_smul_left] at h0
    have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hi i
    rw [Finset.sum_add_distrib, Finset.sum_eq_zero fun i _ ↦ hslack i, zero_add] at hs
    linarith
  refine ⟨w, hw0, fun y ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨hy, hminy⟩
    have hfy : f y = f xbar := le_antisymm (hminy (show xbar ∈ {x | ∀ i, g i x ≤ 0} from hxbar))
      (hmin (show y ∈ {x | ∀ i, g i x ≤ 0} from hy))
    have hterm : ∀ i ∈ Finset.univ, w i * g i y ≤ 0 := fun i _ ↦
      mul_nonpos_of_nonneg_of_nonpos (hw0 i) (hy i)
    have hsum : ∑ i, w i * g i y = 0 :=
      le_antisymm (Finset.sum_nonpos hterm) (by linarith [hL y])
    have hall := (Finset.sum_eq_zero_iff_of_nonpos hterm).mp hsum
    refine ⟨hy, fun i ↦ hall i (Finset.mem_univ i), ?_⟩
    -- `y` minimises the Lagrangian, so its gradient vanishes there
    have hloc : IsLocalMin (fun x ↦ f x + ∑ i, w i * g i x) y := by
      refine IsMinOn.isLocalMin (s := Set.univ) (fun z _ ↦ ?_) Filter.univ_mem
      change f y + ∑ i, w i * g i y ≤ f z + ∑ i, w i * g i z
      rw [hsum, add_zero, hfy]
      exact hL z
    have hsumD : HasFDerivAt (fun x ↦ ∑ i, w i * g i x)
        (∑ i, w i • InnerProductSpace.toDual ℝ E (g' i y)) y := by
      have h : HasFDerivAt (∑ i ∈ (Finset.univ : Finset ι), fun x ↦ w i * g i x)
          (∑ i ∈ (Finset.univ : Finset ι), w i • InnerProductSpace.toDual ℝ E (g' i y)) y :=
        HasFDerivAt.sum fun i _ ↦ (hasGradientAt_iff_hasFDerivAt.mp (hg' i y)).const_mul (w i)
      have heq : (∑ i ∈ (Finset.univ : Finset ι), fun x ↦ w i * g i x) =
          fun x ↦ ∑ i, w i * g i x := by
        funext x
        simp only [Finset.sum_apply]
      rwa [heq] at h
    have hD := hloc.hasFDerivAt_eq_zero ((hasGradientAt_iff_hasFDerivAt.mp (hf' y)).add hsumD)
    have hc : ⟪f' y + ∑ i, w i • g' i y, f' y + ∑ i, w i • g' i y⟫ = 0 := by
      have h2 := congrArg (fun D : E →L[ℝ] ℝ ↦ D (f' y + ∑ i, w i • g' i y)) hD
      simp only [_root_.add_apply, _root_.sum_apply, _root_.smul_apply,
        InnerProductSpace.toDual_apply_apply, smul_eq_mul, _root_.zero_apply] at h2
      rw [inner_add_left, sum_inner]
      simp only [real_inner_smul_left]
      exact h2
    exact inner_self_eq_zero.mp hc
  · rintro ⟨hy, hsl, hst⟩
    exact ⟨hy, ClassicalLean.Analysis.isMinOn_of_kkt hf hg (hf' y) (fun i ↦ hg' i y) hw0 hsl hst⟩

end ClassicalLean.Analysis.KKTMultipliers

/-- The hypotheses of `exists_multipliers_isMinOn_iff` hold together: on `E = ℝ` with `ι = Fin 2`,
minimise `f y = (y - 2) ^ 2 / 2` (convex, gradient `y - 2`) subject to `g 0 y = y - 1 ≤ 0`
(gradient `1`) and `g 1 y = -y - 5 ≤ 0` (gradient `-1`), both affine, so convex. The point
`x0 = 0` meets both constraints strictly (`-1 < 0`, `-5 < 0`). The minimiser is `xbar = 1`, where
`g 0` is active and `g 1` is slack (`-6 < 0`): every feasible `x` has `x ≤ 1`, so
`(x - 2) ^ 2 / 2 ≥ 1 / 2 = f 1`. The unconstrained minimiser `2` is infeasible, so the active
constraint's multiplier is `1`, not `0`. -/
example := ClassicalLean.Analysis.KKTMultipliers.exists_multipliers_isMinOn_iff (E := ℝ)
    (ι := Fin 2) (f := fun y ↦ (y - 2) ^ 2 / 2) (g := ![fun y ↦ y - 1, fun y ↦ -y - 5])
    (f' := fun y ↦ y - 2) (g' := ![fun _ ↦ 1, fun _ ↦ -1]) (xbar := 1)
    ⟨convex_univ, fun x _ y _ s t hs ht hst ↦ by
      obtain rfl : t = 1 - s := by linarith
      simp only [smul_eq_mul]
      nlinarith [mul_nonneg (mul_nonneg hs ht) (sq_nonneg (x - y))]⟩
    (fun i ↦ by
      fin_cases i
      · exact (convexOn_id convex_univ).sub (concaveOn_const (1 : ℝ) convex_univ)
      · exact ((concaveOn_id convex_univ).neg).sub (concaveOn_const (5 : ℝ) convex_univ))
    (fun x ↦ by
      simpa using (((hasDerivAt_id x).sub_const 2).pow 2 |>.div_const 2).hasGradientAt)
    (fun i x ↦ by
      fin_cases i
      · simpa using ((hasDerivAt_id x).sub_const 1).hasGradientAt
      · simpa using ((hasDerivAt_id x).neg.sub_const 5).hasGradientAt)
    ⟨0, fun i ↦ by fin_cases i <;> norm_num⟩
    (fun i ↦ by fin_cases i <;> norm_num)
    (isMinOn_iff.mpr fun x hx ↦ by
      have h0 := hx 0
      simp only [Matrix.cons_val_zero] at h0
      nlinarith)
