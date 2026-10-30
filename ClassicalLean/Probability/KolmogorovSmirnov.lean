/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Probability.GlivenkoCantelli
import ClassicalLean.Probability.IntegralTransform

/-!
# The Kolmogorov–Smirnov statistic is distribution-free

Real draws `X 0, X 1, …` on a probability space, identically distributed, whose distribution
function `F = cdf (μ.map (X 0))` is continuous. The Kolmogorov–Smirnov statistic of the first `n`
draws is `sup over x of |F_n(x) − F(x)|`, with `F_n = empiricalCDF X n` (item 60,
`GlivenkoCantelli`). Order CLOUD-MATH-6, bridge 159 of `MATH-PLAN-library-2-bridges-2.md`.

* `sup_abs_empiricalCDF_sub_eq_of_continuous` — almost surely, for every `n`, the statistic equals
  `sup over u ∈ [0, 1] of |G_n(u) − u|`, where `G_n` is the empirical distribution function of the
  transformed draws `U i = F(X i)`. The supremum over `[0, 1]` is written over the subtype
  `Set.Icc (0 : ℝ) 1`.
* `measureReal_cdf_le_eq_of_map_eq` — each `U i = F(X i)` is uniform on `[0, 1]`:
  `P(F(X i) ≤ u) = u` for `0 ≤ u ≤ 1` (item 106, `measureReal_cdf_le_eq_of_continuous`, at `X i`,
  whose law is that of `X 0`).

Neither theorem assumes independence (the row assumes pairwise independent draws; the pathwise
identity does not need it, so the first theorem is wider). A consequence, not proved here: when the
draws are moreover mutually independent (`iIndepFun`), the `U i` are independent and uniform on
`[0, 1]`, so the law of the statistic is that of the uniform case, the same for every continuous
`F`, and one table of critical values serves every such test.

The proof of the identity: almost surely, for every `i` and every `x`, `X i ≤ x` exactly when
`F(X i) ≤ F(x)`. One direction is the monotonicity of `F`; the other fails only when `X i` lies
above a rational `q` with `F(X i) ≤ F(q)`, and for each `q` that has chance
`P(F(X i) ≤ F(q)) − P(X i ≤ q) = F(q) − F(q) = 0` (the uniform marginal). So `F_n(x) = G_n(F(x))`
for every `x`. `F` is continuous with limits `0` and `1`, so its range lies in `[0, 1]` and contains
`(0, 1)`; at `u = 0` the term is `0` almost surely (no `F(X i)` is `0`), and at `u = 1` it is `0`
for `n ≥ 1` (every `F(X i) ≤ 1`) and `1 = sup F` for `n = 0`.

The witnesses at the end of the file use the standard normal law `gaussianReal 0 1` on `ℝ` and the
draws `X i ω = ω` for even `i`, `−ω` for odd `i`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace ClassicalLean.Probability.KolmogorovSmirnov

/-- **The transformed draws are uniform** (bridge 159, theorem 2): for a draw `X i` with the law of
`X 0` (`hlaw`), measurable, whose common distribution function `F = cdf (μ.map (X 0))` is
continuous, `F(X i)` is uniform on `[0, 1]`: `P(F(X i) ≤ u) = u` for `0 ≤ u ≤ 1`. Item 106
(`measureReal_cdf_le_eq_of_continuous`) at `X i`. -/
theorem measureReal_cdf_le_eq_of_map_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} (i : ℕ) (hX : Measurable (X i))
    (hlaw : μ.map (X i) = μ.map (X 0)) (hF : Continuous (cdf (μ.map (X 0)))) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    μ.real {ω | cdf (μ.map (X 0)) (X i ω) ≤ u} = u := by
  have h := measureReal_cdf_le_eq_of_continuous hX (by rw [hlaw]; exact hF) hu0 hu1
  rwa [hlaw] at h

/-- **The Kolmogorov–Smirnov statistic is distribution-free, pathwise** (bridge 159, theorem 1).
For measurable, identically distributed real draws `X i` (`hX`, `hlaw`) whose distribution function
`F = cdf (μ.map (X 0))` is continuous, almost surely, for every `n`,
`sup over x ∈ ℝ of |F_n(x) − F(x)| = sup over u ∈ [0, 1] of |G_n(u) − u|`, where `F_n` is the
empirical distribution function of `X 0, …, X (n − 1)` and `G_n` that of the transformed draws
`F(X 0), …, F(X (n − 1))`, uniform on `[0, 1]` by `measureReal_cdf_le_eq_of_map_eq`. No
independence is assumed. Under mutual independence (`iIndepFun`) as well, the right side is the
statistic of independent uniform draws, so its law does not depend on `F` (a consequence, not
proved here). -/
theorem sup_abs_empiricalCDF_sub_eq_of_continuous {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, μ.map (X i) = μ.map (X 0)) (hF : Continuous (cdf (μ.map (X 0)))) :
    ∀ᵐ ω ∂μ, ∀ n, (⨆ x : ℝ, |empiricalCDF X n ω x - cdf (μ.map (X 0)) x|) =
      ⨆ u : Set.Icc (0 : ℝ) 1,
        |empiricalCDF (fun i ω ↦ cdf (μ.map (X 0)) (X i ω)) n ω u - u| := by
  set F := cdf (μ.map (X 0)) with hFdef
  have hunif : ∀ i {u : ℝ}, 0 ≤ u → u ≤ 1 → μ.real {ω | F (X i ω) ≤ u} = u :=
    fun i u h0 h1 ↦ measureReal_cdf_le_eq_of_map_eq i (hX i) (hlaw i) hF h0 h1
  -- almost surely, `F (X i) ≤ F q` forces `X i ≤ q`, for every `i` and every rational `q`
  have hgood : ∀ᵐ ω ∂μ, ∀ i, ∀ q : ℚ, F (X i ω) ≤ F q → X i ω ≤ q := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro q
    have hB : MeasurableSet {ω | X i ω ≤ q} := measurableSet_le (hX i) measurable_const
    have hsub : {ω | X i ω ≤ q} ⊆ {ω | F (X i ω) ≤ F q} := fun ω h ↦ F.mono h
    have hBq : μ.real {ω | X i ω ≤ q} = F q := by
      rw [hFdef, cdf_eq_real, ← hlaw i, map_measureReal_apply (hX i) measurableSet_Iic]
      rfl
    have hAq : μ.real {ω | F (X i ω) ≤ F q} = F q := hunif i (cdf_nonneg _ _) (cdf_le_one _ _)
    have hdiff : μ.real ({ω | F (X i ω) ≤ F q} \ {ω | X i ω ≤ q}) = 0 := by
      rw [measureReal_sdiff hsub hB, hAq, hBq, sub_self]
    have hnull : μ ({ω | F (X i ω) ≤ F q} \ {ω | X i ω ≤ q}) = 0 :=
      (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hdiff
    rw [ae_iff]
    refine measure_mono_null (fun ω hω ↦ ?_) hnull
    simp only [Set.mem_ofPred_eq, not_imp, not_le] at hω
    exact ⟨hω.1, not_le.2 hω.2⟩
  -- almost surely, no `F (X i)` is `0`
  have hpos : ∀ᵐ ω ∂μ, ∀ i, 0 < F (X i ω) := by
    rw [ae_all_iff]
    intro i
    have h0 : μ {ω | F (X i ω) ≤ 0} = 0 :=
      (measureReal_eq_zero_iff (measure_ne_top _ _)).1 (hunif i le_rfl zero_le_one)
    rw [ae_iff]
    simpa only [not_lt] using h0
  filter_upwards [hgood, hpos] with ω hω hω0 n
  have hiff : ∀ i x, X i ω ≤ x ↔ F (X i ω) ≤ F x := by
    intro i x
    refine ⟨fun h ↦ F.mono h, fun h ↦ ?_⟩
    by_contra hlt
    obtain ⟨q, hxq, hqX⟩ := exists_rat_btwn (not_le.1 hlt)
    have := hω i q (h.trans (F.mono hxq.le))
    linarith
  have hE : ∀ x, empiricalCDF X n ω x = empiricalCDF (fun i ω ↦ F (X i ω)) n ω (F x) := by
    intro x
    unfold empiricalCDF
    rw [Finset.filter_congr fun i _ ↦ hiff i x]
  have hbL := bddAbove_abs_empiricalCDF_sub X (μ.map (X 0)) n ω
  have hbR : BddAbove (Set.range fun u : Set.Icc (0 : ℝ) 1 ↦
      |empiricalCDF (fun i ω ↦ F (X i ω)) n ω u - u|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨u, rfl⟩
    rw [abs_le]
    constructor <;> linarith [empiricalCDF_nonneg (fun i ω ↦ F (X i ω)) n ω u,
      empiricalCDF_le_one (fun i ω ↦ F (X i ω)) n ω u, u.2.1, u.2.2]
  have hLnn : 0 ≤ ⨆ x : ℝ, |empiricalCDF X n ω x - F x| :=
    le_ciSup_of_le hbL 0 (abs_nonneg _)
  apply le_antisymm
  · exact ciSup_le fun x ↦
      le_ciSup_of_le hbR ⟨F x, cdf_nonneg _ _, cdf_le_one _ _⟩ (by rw [hE])
  · have : Nonempty (Set.Icc (0 : ℝ) 1) := ⟨⟨0, le_rfl, zero_le_one⟩⟩
    refine ciSup_le fun u ↦ ?_
    obtain ⟨u, hu0, hu1⟩ := u
    rcases hu0.eq_or_lt with h0 | h0
    · -- `u = 0`: no transformed draw is at most `0`
      subst h0
      have hG0 : empiricalCDF (fun i ω ↦ F (X i ω)) n ω 0 = 0 := by
        unfold empiricalCDF
        rw [Finset.filter_false_of_mem fun i _ ↦ not_le.2 (hω0 i)]
        simp
      simpa [hG0] using hLnn
    rcases hu1.eq_or_lt with h1 | h1
    · -- `u = 1`: every transformed draw is at most `1`
      subst h1
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        have hEz : ∀ x, empiricalCDF X 0 ω x = 0 := fun x ↦ by simp [empiricalCDF]
        have hGz : empiricalCDF (fun i ω ↦ F (X i ω)) 0 ω 1 = 0 := by simp [empiricalCDF]
        simp only [hGz, zero_sub, abs_neg, abs_one]
        refine le_of_tendsto (tendsto_cdf_atTop (μ.map (X 0))) (Eventually.of_forall fun x ↦ ?_)
        exact le_ciSup_of_le hbL x (by rw [hEz, zero_sub, abs_neg, abs_of_nonneg (cdf_nonneg _ _)])
      · have hG1 : empiricalCDF (fun i ω ↦ F (X i ω)) n ω 1 = 1 := by
          unfold empiricalCDF
          rw [Finset.filter_true_of_mem fun i _ ↦ cdf_le_one _ _]
          have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
          simp [this]
        simpa [hG1] using hLnn
    · -- `0 < u < 1`: `u = F x` for some `x`
      obtain ⟨b, hb⟩ := ((tendsto_cdf_atBot (μ.map (X 0))).eventually (gt_mem_nhds h0)).exists
      obtain ⟨c, hc⟩ := ((tendsto_cdf_atTop (μ.map (X 0))).eventually (lt_mem_nhds h1)).exists
      obtain ⟨x, hx⟩ := intermediate_value_univ b c hF ⟨hb.le, hc.le⟩
      exact le_ciSup_of_le hbL x (by rw [hE, hx])

end ClassicalLean.Probability.KolmogorovSmirnov

/-- The hypotheses of `sup_abs_empiricalCDF_sub_eq_of_continuous` hold together: `Ω = ℝ` under the
standard normal law `gaussianReal 0 1`, and the draws `X i ω = ω` for even `i`, `−ω` for odd `i`,
so the draws are not all the same function (and `X (i + 1) ≠ X i` off the null set `{0}`: the
process moves at every step). Each is measurable, and each has the standard normal law (for odd `i`
by `gaussianReal_map_neg`), so they are identically distributed; their distribution function `Φ`
is continuous because the law puts no mass on a point (`nullSingletonClass_gaussianReal`), as in
`IntegralTransform`'s witness. -/
example := ClassicalLean.Probability.KolmogorovSmirnov.sup_abs_empiricalCDF_sub_eq_of_continuous
  (Ω := ℝ) (μ := gaussianReal 0 1) (X := fun i ω ↦ if Even i then ω else -ω)
  (fun i ↦ by
    by_cases h : Even i
    · simp only [h, ite_true]; exact measurable_id
    · simp only [h, ite_false]; exact measurable_neg)
  (fun i ↦ by
    by_cases h : Even i
    · simp only [h, ite_true, Even.zero]
    · simp only [h, ite_false, Even.zero, ite_true]
      rw [gaussianReal_map_neg, neg_zero, Measure.map_id'])
  (by
    simp only [Even.zero, ite_true]
    rw [Measure.map_id']
    have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    refine continuous_iff_continuousAt.2 fun a ↦ ?_
    rw [(cdf (gaussianReal 0 1)).mono.continuousAt_iff_leftLim_eq_rightLim,
      StieltjesFunction.rightLim_eq]
    have h := (cdf (gaussianReal 0 1)).measure_singleton a
    rw [measure_cdf, MeasureTheory.measure_singleton] at h
    linarith [ENNReal.ofReal_eq_zero.1 h.symm,
      (cdf (gaussianReal 0 1)).mono.leftLim_le (le_refl a)])

/-- The hypotheses of `measureReal_cdf_le_eq_of_map_eq` hold together: the same draws under the
standard normal law, at `i = 1`, where `X 1 ω = −ω`, whose law is the standard normal law by
`gaussianReal_map_neg` (so `hlaw` is not `rfl`); `Φ` is continuous as above; `u = 1/2`, not an end
of `[0, 1]`. -/
example := ClassicalLean.Probability.KolmogorovSmirnov.measureReal_cdf_le_eq_of_map_eq
  (Ω := ℝ) (μ := gaussianReal 0 1) (X := fun i ω ↦ if Even i then ω else -ω) (i := 1)
  (by simp only [Nat.not_even_one, ite_false]; exact measurable_neg)
  (by
    simp only [Nat.not_even_one, ite_false, Even.zero, ite_true]
    rw [gaussianReal_map_neg, neg_zero, Measure.map_id'])
  (by
    simp only [Even.zero, ite_true]
    rw [Measure.map_id']
    have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    refine continuous_iff_continuousAt.2 fun a ↦ ?_
    rw [(cdf (gaussianReal 0 1)).mono.continuousAt_iff_leftLim_eq_rightLim,
      StieltjesFunction.rightLim_eq]
    have h := (cdf (gaussianReal 0 1)).measure_singleton a
    rw [measure_cdf, MeasureTheory.measure_singleton] at h
    linarith [ENNReal.ofReal_eq_zero.1 h.symm,
      (cdf (gaussianReal 0 1)).mono.leftLim_le (le_refl a)])
  (u := 1 / 2) (by norm_num) (by norm_num)
