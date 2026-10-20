/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Necessity of the KKT conditions under Slater's condition

* `exists_kkt_of_slater` — order CLOUD-MATH-2, item 152 of MATH-PLAN-library-2. For the convex
  problem of minimising `f x` subject to `g i x ≤ 0` for `i` in a finite type, on a real Hilbert
  space, with `f` and every `g i` convex and differentiable at a feasible minimiser `xbar`
  (gradients `a` and `b i`): if some point satisfies every constraint strictly (Slater's
  condition), there are multipliers `w i ≥ 0` with complementary slackness `w i * g i xbar = 0`
  and stationarity `a + ∑ i, w i • b i = 0`.

The proof. The set `C` of pairs `(t, v)` such that `f x < t` and `g i x < v i` for every `i`, for
some `x`, is convex and open, and `(f xbar, 0)` lies outside it because `xbar` is a feasible
minimiser; a continuous linear functional `φ` separates the point from `C`
(`geometric_hahn_banach_point_open`). `φ` is nonnegative on pairs with nonnegative coordinates, so
`φ (t, v) = l₀ * t + ∑ i, v i * λ i` with `l₀ ≥ 0` and every `λ i ≥ 0`, and
`l₀ * f xbar ≤ l₀ * f x + ∑ i, λ i * g i x` for every `x`. Slater's point rules out `l₀ = 0`.
With `w i = λ i / l₀`, `f xbar ≤ f x + ∑ i, w i * g i x` for every `x`; at `x = xbar`, with
feasibility, this gives complementary slackness, so `xbar` minimises the Lagrangian
`f + ∑ i, w i * g i` over the whole space; the Lagrangian's derivative at `xbar`, the functional of
`a + ∑ i, w i • b i`, vanishes there (`IsLocalMin.hasFDerivAt_eq_zero`), and so does that vector.

The proof is the draft `d152-r2-s1` (written by Claude Opus 5.5 through the Anthropic Batch API,
the lane's API-CREDIT-1 work), adapted by the Claude Code cloud session that landed it (order
CLOUD-MATH-2): the namespace and docstrings; `change` where a `show` changed the goal; `push Not`
for the deprecated `push_neg`; the names Mathlib now gives four deprecated `ContinuousLinearMap`
lemmas (`add_apply`, `_root_.sum_apply`, `smul_apply`, `zero_apply`); and the import of
`Mathlib.Analysis.Calculus.FDeriv.Mul` (for `HasFDerivAt.const_mul`) in place of the draft's
import of the library's `ClassicalLean.Analysis.GradientDescent`, none of whose declarations the
proof uses.
-/

open Finset
open scoped RealInnerProductSpace

namespace ClassicalLean.Analysis.KKT

/-- A strict convex combination inequality. -/
private lemma convex_comb_lt {s t a b c d : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1)
    (hab : a < b) (hcd : c < d) : s * a + t * c < s * b + t * d := by
  rcases eq_or_lt_of_le hs with h | h
  · have ht1 : t = 1 := by linarith
    rw [← h, ht1]; linarith
  · nlinarith [mul_lt_mul_of_pos_left hab h, mul_le_mul_of_nonneg_left hcd.le ht]

/-- **KKT conditions are necessary under Slater's condition** (item 152 of MATH-PLAN-library-2).
Let `f` and every `g i` be convex on a real Hilbert space, with gradients `a` and `b i` at `xbar`.
If `xbar` is feasible and minimises `f` over `{x | ∀ i, g i x ≤ 0}`, and some point satisfies
every constraint strictly, then there are multipliers `w i ≥ 0` with `w i · g i xbar = 0` and
`a + ∑ w i b i = 0`. -/
theorem exists_kkt_of_slater {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] {f : E → ℝ} {g : ι → E → ℝ} {xbar a : E}
    {b : ι → E} (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hfa : HasGradientAt f a xbar) (hgb : ∀ i, HasGradientAt (g i) (b i) xbar)
    (hslater : ∃ x0, ∀ i, g i x0 < 0) (hxbar : ∀ i, g i xbar ≤ 0)
    (hmin : IsMinOn f {x | ∀ i, g i x ≤ 0} xbar) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∀ i, w i * g i xbar = 0) ∧ a + ∑ i, w i • b i = 0 := by
  classical
  obtain ⟨C, hC⟩ : ∃ C : Set (ℝ × (ι → ℝ)),
      C = {z | ∃ x, f x < z.1 ∧ ∀ i, g i x < z.2 i} := ⟨_, rfl⟩
  have hmem : ∀ z, z ∈ C ↔ ∃ x, f x < z.1 ∧ ∀ i, g i x < z.2 i := fun z => by
    subst hC; exact Iff.rfl
  -- convexity of `C`
  have hCconv : Convex ℝ C := by
    intro z1 hz1 z2 hz2 s t hs ht hst
    obtain ⟨x1, h11, h12⟩ := (hmem z1).mp hz1
    obtain ⟨x2, h21, h22⟩ := (hmem z2).mp hz2
    refine (hmem _).mpr ⟨s • x1 + t • x2, ?_, fun i => ?_⟩
    · have h := hf.2 (Set.mem_univ x1) (Set.mem_univ x2) hs ht hst
      simp only [smul_eq_mul] at h
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      exact lt_of_le_of_lt h (convex_comb_lt hs ht hst h11 h21)
    · have h := (hg i).2 (Set.mem_univ x1) (Set.mem_univ x2) hs ht hst
      simp only [smul_eq_mul] at h
      simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact lt_of_le_of_lt h (convex_comb_lt hs ht hst (h12 i) (h22 i))
  -- openness of `C`
  have hCopen : IsOpen C := by
    have : C = ⋃ x : E, ({z : ℝ × (ι → ℝ) | f x < z.1} ∩
        ⋂ i, {z : ℝ × (ι → ℝ) | g i x < z.2 i}) := by
      ext z; rw [hmem]; simp
    rw [this]
    exact isOpen_iUnion fun x => (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (by fun_prop))
  -- the point is outside `C`
  have hpC : ((f xbar, (0 : ι → ℝ)) : ℝ × (ι → ℝ)) ∉ C := by
    intro h
    obtain ⟨x, hx1, hx2⟩ := (hmem _).mp h
    have hfeas : ∀ i, g i x ≤ 0 := fun i => le_of_lt (hx2 i)
    have hle := isMinOn_iff.mp hmin x hfeas
    exact absurd hx1 (not_lt.mpr hle)
  obtain ⟨φ, hφ⟩ := geometric_hahn_banach_point_open hCconv hCopen hpC
  have z0mem : ((f xbar + 1, fun i => g i xbar + 1) : ℝ × (ι → ℝ)) ∈ C :=
    (hmem _).mpr ⟨xbar, by change f xbar < f xbar + 1; linarith,
      fun i => by change g i xbar < g i xbar + 1; linarith⟩
  -- nonnegative directions
  have hdir : ∀ d : ℝ × (ι → ℝ), 0 ≤ d.1 → (∀ i, 0 ≤ d.2 i) → 0 ≤ φ d := by
    intro d hd1 hd2
    by_contra hneg
    push Not at hneg
    obtain ⟨z0, hz0⟩ : ∃ z0, z0 ∈ C := ⟨_, z0mem⟩
    have hlt := hφ z0 hz0
    obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = (φ z0 - φ (f xbar, 0)) / (-φ d) := ⟨_, rfl⟩
    have hs : 0 ≤ s := by
      rw [hs_def]; exact div_nonneg (by linarith) (by linarith)
    have hmem2 : z0 + s • d ∈ C := by
      obtain ⟨x, hx1, hx2⟩ := (hmem z0).mp hz0
      refine (hmem _).mpr ⟨x, ?_, fun i => ?_⟩
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        linarith [mul_nonneg hs hd1]
      · simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linarith [mul_nonneg hs (hd2 i), hx2 i]
    have h2 := hφ _ hmem2
    rw [map_add, map_smul, smul_eq_mul] at h2
    have hsd : s * φ d = -(φ z0 - φ (f xbar, 0)) := by
      rw [hs_def, div_mul_eq_mul_div, div_eq_iff (by linarith : (0 : ℝ) < -φ d).ne']
      ring
    linarith
  -- coordinates of `φ`
  obtain ⟨l0, hl0⟩ : ∃ l0 : ℝ, l0 = φ ((1 : ℝ), (0 : ι → ℝ)) := ⟨_, rfl⟩
  obtain ⟨lam, hlami⟩ : ∃ lam : ι → ℝ,
      ∀ i, lam i = φ ((0 : ℝ), (Pi.single i (1 : ℝ) : ι → ℝ)) :=
    ⟨fun i => φ ((0 : ℝ), (Pi.single i (1 : ℝ) : ι → ℝ)), fun i => rfl⟩
  have hdec : ∀ (u : ℝ) (v : ι → ℝ), φ (u, v) = u * l0 + ∑ i, v i * lam i := by
    intro u v
    have hv : ((u, v) : ℝ × (ι → ℝ)) = u • ((1 : ℝ), (0 : ι → ℝ)) +
        ∑ i, v i • ((0 : ℝ), (Pi.single i (1 : ℝ) : ι → ℝ)) := by
      refine Prod.ext ?_ ?_
      · simp [Prod.fst_sum]
      · funext j
        simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    rw [hv, map_add, map_smul, map_sum, hl0]
    simp only [map_smul, smul_eq_mul, hlami]
  have hl0nn : 0 ≤ l0 := by
    rw [hl0]; exact hdir _ (by simp) (fun i => by simp)
  have hlam_nn : ∀ i, 0 ≤ lam i := fun i => by
    rw [hlami]
    exact hdir _ (by simp) (fun j => by rcases eq_or_ne j i with h | h <;> simp [h])
  -- the separation inequality, closed up
  have key : ∀ x, l0 * f xbar ≤ l0 * f x + ∑ i, lam i * g i x := by
    intro x
    by_contra hcon
    push Not at hcon
    have hT : 0 ≤ ∑ i, lam i := Finset.sum_nonneg fun i _ => hlam_nn i
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = l0 * f xbar - (l0 * f x + ∑ i, lam i * g i x) := ⟨_, rfl⟩
    have hδpos : 0 < δ := by rw [hδ]; linarith
    have hden : 0 < l0 + ∑ i, lam i + 1 := by linarith
    obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = δ / (l0 + ∑ i, lam i + 1) := ⟨_, rfl⟩
    have hεpos : 0 < ε := by rw [hε]; exact div_pos hδpos hden
    have hden' := hden.ne'
    have hεK : ε * (l0 + ∑ i, lam i + 1) = δ := by rw [hε]; field_simp
    have hzmem : ((f x + ε, fun i => g i x + ε) : ℝ × (ι → ℝ)) ∈ C :=
      (hmem _).mpr ⟨x, by change f x < f x + ε; linarith,
        fun i => by change g i x < g i x + ε; linarith⟩
    have h3 := hφ _ hzmem
    simp only [hdec, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] at h3
    have hs : ∑ i, (g i x + ε) * lam i = ∑ i, lam i * g i x + ε * ∑ i, lam i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    nlinarith [h3, hs, hεK, hδ, hεpos]
  -- Slater's condition gives `l0 > 0`
  obtain ⟨x0, hx0⟩ := hslater
  have hl0pos : 0 < l0 := by
    rcases hl0nn.lt_or_eq with h | h
    · exact h
    exfalso
    have hk : 0 ≤ ∑ i, lam i * g i x0 := by
      have := key x0; rw [← h] at this; linarith
    have hterm : ∀ i, lam i * g i x0 ≤ 0 := fun i =>
      mul_nonpos_of_nonneg_of_nonpos (hlam_nn i) (hx0 i).le
    have hz := (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => hterm i)).mp
      (le_antisymm (Finset.sum_nonpos fun i _ => hterm i) hk)
    have hlam0 : ∀ i, lam i = 0 := fun i => by
      have := hz i (Finset.mem_univ i)
      rcases mul_eq_zero.mp this with h' | h'
      · exact h'
      · exact absurd h' (hx0 i).ne
    have := hφ _ z0mem
    simp [hdec, ← h, hlam0] at this
  -- the multipliers
  obtain ⟨w, hwi⟩ : ∃ w : ι → ℝ, ∀ i, w i = lam i * l0⁻¹ :=
    ⟨fun i => lam i * l0⁻¹, fun i => rfl⟩
  have hne : l0 ≠ 0 := hl0pos.ne'
  have hwnn : ∀ i, 0 ≤ w i := fun i => by
    rw [hwi]; exact mul_nonneg (hlam_nn i) (inv_nonneg.mpr hl0nn)
  have hLag : ∀ x, f xbar ≤ f x + ∑ i, w i * g i x := by
    intro x
    have hk := key x
    have h' : l0 * (f x + ∑ i, w i * g i x) = l0 * f x + ∑ i, lam i * g i x := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hwi i]
      have hinv : l0 * l0⁻¹ = 1 := mul_inv_cancel₀ hne
      linear_combination (lam i * g i x) * hinv
    by_contra hc
    push Not at hc
    have := mul_lt_mul_of_pos_left hc hl0pos
    linarith
  have hterm : ∀ i, w i * g i xbar ≤ 0 := fun i =>
    mul_nonpos_of_nonneg_of_nonpos (hwnn i) (hxbar i)
  have hsum0 : ∑ i, w i * g i xbar = 0 :=
    le_antisymm (Finset.sum_nonpos fun i _ => hterm i) (by have := hLag xbar; linarith)
  have hslack : ∀ i, w i * g i xbar = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => hterm i)).mp hsum0 i (Finset.mem_univ i)
  refine ⟨w, hwnn, hslack, ?_⟩
  -- stationarity: `xbar` minimises the Lagrangian
  have hfa' : HasFDerivAt f (InnerProductSpace.toDual ℝ E a) xbar :=
    hasGradientAt_iff_hasFDerivAt.mp hfa
  have hsumD : HasFDerivAt (fun x => ∑ i, w i * g i x)
      (∑ i, w i • InnerProductSpace.toDual ℝ E (b i)) xbar := by
    have h : HasFDerivAt (∑ i ∈ (Finset.univ : Finset ι), fun y => w i * g i y)
        (∑ i ∈ (Finset.univ : Finset ι), w i • InnerProductSpace.toDual ℝ E (b i)) xbar :=
      HasFDerivAt.sum fun i _ => (hasGradientAt_iff_hasFDerivAt.mp (hgb i)).const_mul (w i)
    have heq : (∑ i ∈ (Finset.univ : Finset ι), fun y => w i * g i y) =
        fun x => ∑ i, w i * g i x := by
      funext x
      simp only [Finset.sum_apply]
    rw [heq] at h
    exact h
  have hLD := hfa'.add hsumD
  have hloc : IsLocalMin (fun x => f x + ∑ i, w i * g i x) xbar := by
    refine Filter.Eventually.of_forall fun x => ?_
    change f xbar + ∑ i, w i * g i xbar ≤ f x + ∑ i, w i * g i x
    rw [hsum0, add_zero]
    exact hLag x
  have hD := hloc.hasFDerivAt_eq_zero hLD
  have hc : ⟪a + ∑ i, w i • b i, a + ∑ i, w i • b i⟫ = 0 := by
    have h2 := congrArg (fun D : E →L[ℝ] ℝ => D (a + ∑ i, w i • b i)) hD
    simp only [add_apply, _root_.sum_apply,
      smul_apply, InnerProductSpace.toDual_apply_apply, smul_eq_mul,
      zero_apply] at h2
    rw [inner_add_left, sum_inner]
    simp only [real_inner_smul_left]
    exact h2
  exact inner_self_eq_zero.mp hc

end ClassicalLean.Analysis.KKT

/-- The hypotheses of `exists_kkt_of_slater` hold together: on the real line, minimise
`f x = x * x` subject to the two constraints `1 - x ≤ 0` and `x - 2 ≤ 0` (`ι = Fin 2`). The
minimiser is `xbar = 1`, where the first constraint is active and the second is not; the gradients
there are `a = 2` and `b = (-1, 1)`; the point `3 / 2` satisfies both constraints strictly. -/
example := ClassicalLean.Analysis.KKT.exists_kkt_of_slater (E := ℝ) (ι := Fin 2)
    (f := fun x => x * x) (g := ![fun x => 1 - x, fun x => x - 2]) (xbar := 1) (a := 2)
    (b := ![-1, 1])
    ⟨convex_univ, fun x _ y _ s t hs ht hst => by
      obtain rfl : t = 1 - s := by linarith
      simp only [smul_eq_mul]
      nlinarith [mul_nonneg (mul_nonneg hs ht) (sq_nonneg (x - y))]⟩
    (fun i => by
      fin_cases i
      · refine ⟨convex_univ, fun x _ y _ s t _ _ hst => ?_⟩
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, smul_eq_mul]
        linarith
      · refine ⟨convex_univ, fun x _ y _ s t _ _ hst => ?_⟩
        simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          smul_eq_mul]
        linarith)
    (by
      rw [hasGradientAt_iff_hasFDerivAt]
      refine ((hasFDerivAt_id (1 : ℝ)).mul (hasFDerivAt_id (1 : ℝ))).congr_fderiv ?_
      ext
      simp
      norm_num)
    (fun i => by
      fin_cases i
      · simpa using ((hasDerivAt_id (1 : ℝ)).const_sub 1).hasGradientAt'
      · simpa using ((hasDerivAt_id (1 : ℝ)).sub_const 2).hasGradientAt')
    ⟨3 / 2, fun i => by fin_cases i <;> norm_num⟩
    (fun i => by fin_cases i <;> norm_num)
    (isMinOn_iff.mpr fun x hx => by
      have h0 := hx 0
      simp only [Matrix.cons_val_zero] at h0
      nlinarith)
