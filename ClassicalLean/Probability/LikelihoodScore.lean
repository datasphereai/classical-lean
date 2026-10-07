/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Probability.RuinBound
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# A score that may be checked after every outcome

Outcomes `W n` lie in `[0, 1]` (a win is `1`, a loss `0`), adapted to a filtration `𝒢`, and the
chance of a win given the past is at most `p₀`: `μ[W (n+1) | 𝒢 n] ≤ p₀` almost everywhere, with
`0 < p₀ < 1`. For a fixed `q` with `p₀ ≤ q ≤ 1`, each outcome multiplies the score by
`scoreFactor p₀ q w = (1 - q)/(1 - p₀) + w (q/p₀ - (1 - q)/(1 - p₀))`, which is `q/p₀` on a win and
`(1 - q)/(1 - p₀)` on a loss. So for wins and losses the score after `n` outcomes is
`(q/p₀) ^ wins · ((1 - q)/(1 - p₀)) ^ losses` (`score_eq_pow`).

* `scoreFactor_eq`: an outcome whose win chance is `π` multiplies the score's mean by
  `1 + (π - p₀)(q - p₀)/(p₀(1 - p₀))`, which is at most `1` when `π ≤ p₀ ≤ q`.
* `supermartingale_score`: the score starts at `1` and is a nonnegative supermartingale.
* `measureReal_exists_le_score`: the chance that it reaches `1/α` (for `0 < α`) within `N`
  outcomes is at most `α` (Ville's inequality, `MaximalInequality`).
* `measureReal_exists_le_score_ever`: the same with no limit on the number of outcomes.

So the score may be looked at after every outcome, and stopping the first time it reaches `1/α`
raises a false alarm with chance at most `α`. A fixed-size test at level `0.05` re-run after every
one of 200 outcomes, with true win chance `p₀ = 1/2`, raises a false alarm with chance `0.2446`.

Each hypothesis is needed. With `q = 0.4 < p₀ = 0.5`, an outcome that always loses multiplies the
score by `1.2`, so it reaches `2` at the fourth outcome with chance `1 > 1/2`. With `q = 2 > 1`,
always losing gives the factors `-2`, and the score `4` after two outcomes. If the outcomes are
not adapted (the filtration is trivial, every outcome copies a fair first one, `p₀ = 1/2`, `q = 1`)
the score reaches `4` with chance `1/2 > 1/4`.

`q` is one number, fixed before any outcome is seen. Choosing it from the outcomes is not covered:
with `p₀ = 1/2`, `α = 1/20` and 200 outcomes, `q = 3/5` fixed in advance gives a false alarm with
chance `0.035`, but setting `q` to the win rate observed so far, recomputed at each outcome, gives
`0.094`.
-/

open MeasureTheory Filter Finset
open ClassicalLean.Probability.MaximalInequality ClassicalLean.Probability.RuinBound

namespace ClassicalLean.Probability.LikelihoodScore

/-- The factor by which an outcome `w` multiplies the score: `q/p₀` at `w = 1`, `(1-q)/(1-p₀)` at
`w = 0`, and affine in between. -/
noncomputable def scoreFactor (p₀ q w : ℝ) : ℝ :=
  (1 - q) / (1 - p₀) + w * (q / p₀ - (1 - q) / (1 - p₀))

lemma scoreFactor_one (p₀ q : ℝ) : scoreFactor p₀ q 1 = q / p₀ := by
  unfold scoreFactor; ring

lemma scoreFactor_zero (p₀ q : ℝ) : scoreFactor p₀ q 0 = (1 - q) / (1 - p₀) := by
  simp [scoreFactor]

/-- **The mean multiplier.** An outcome with win chance `π` multiplies the mean of the score by
`1 + (π - p₀)(q - p₀)/(p₀(1 - p₀))`. -/
theorem scoreFactor_eq {p₀ : ℝ} (hp0 : 0 < p₀) (hp1 : p₀ < 1) (q π : ℝ) :
    scoreFactor p₀ q π = 1 + (π - p₀) * (q - p₀) / (p₀ * (1 - p₀)) := by
  have h1 : (1 - p₀) ≠ 0 := by linarith
  unfold scoreFactor
  field_simp
  ring

lemma scoreFactor_self {p₀ : ℝ} (hp0 : 0 < p₀) (hp1 : p₀ < 1) (q : ℝ) :
    scoreFactor p₀ q p₀ = 1 := by
  rw [scoreFactor_eq hp0 hp1]; simp

lemma scoreFactor_eq_convex (p₀ q w : ℝ) :
    scoreFactor p₀ q w = (1 - w) * ((1 - q) / (1 - p₀)) + w * (q / p₀) := by
  unfold scoreFactor; ring

variable {p₀ q : ℝ}

lemma scoreFactor_nonneg (hp0 : 0 < p₀) (hp1 : p₀ < 1) (hq0 : p₀ ≤ q) (hq1 : q ≤ 1) {w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) : 0 ≤ scoreFactor p₀ q w := by
  rw [scoreFactor_eq_convex]
  have : 0 ≤ (1 - q) / (1 - p₀) := div_nonneg (by linarith) (by linarith)
  have : 0 ≤ q / p₀ := div_nonneg (by linarith) hp0.le
  have : 0 ≤ 1 - w := by linarith
  positivity

lemma scoreFactor_le (hp0 : 0 < p₀) (hp1 : p₀ < 1) (hq0 : p₀ ≤ q) (hq1 : q ≤ 1) {w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) : scoreFactor p₀ q w ≤ (1 - q) / (1 - p₀) + q / p₀ := by
  rw [scoreFactor_eq_convex]
  have h1 : 0 ≤ (1 - q) / (1 - p₀) := div_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ q / p₀ := div_nonneg (by linarith) hp0.le
  nlinarith

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The score after `n` outcomes: `∏ i < n, scoreFactor p₀ q (W (i + 1))`. -/
noncomputable def score (p₀ q : ℝ) (W : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∏ i ∈ range n, scoreFactor p₀ q (W (i + 1) ω)

/-- For wins and losses, the score is `(q/p₀) ^ wins · ((1-q)/(1-p₀)) ^ losses`. -/
theorem score_eq_pow {W : ℕ → Ω → ℝ} (hW : ∀ i ω, W i ω = 0 ∨ W i ω = 1) (n : ℕ) (ω : Ω) :
    score p₀ q W n ω = (q / p₀) ^ #{i ∈ range n | W (i + 1) ω = 1} *
      ((1 - q) / (1 - p₀)) ^ #{i ∈ range n | W (i + 1) ω = 0} := by
  unfold score
  rw [← prod_filter_mul_prod_filter_not (range n) (fun i ↦ W (i + 1) ω = 1)]
  have hnot : {i ∈ range n | ¬ W (i + 1) ω = 1} = {i ∈ range n | W (i + 1) ω = 0} := by
    ext i; simp only [mem_filter]
    rcases hW (i + 1) ω with h | h <;> simp [h]
  rw [hnot, prod_congr rfl (g := fun _ ↦ q / p₀), prod_const,
    prod_congr rfl (g := fun _ ↦ (1 - q) / (1 - p₀)), prod_const]
  · intro i hi; rw [(mem_filter.mp hi).2, scoreFactor_zero]
  · intro i hi; rw [(mem_filter.mp hi).2, scoreFactor_one]

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {𝒢 : Filtration ℕ m0}

/-- **The score is a nonnegative supermartingale.** With outcomes in `[0, 1]`, adapted to `𝒢`,
whose win chance given the past is at most `p₀` (`0 < p₀ < 1`), and `p₀ ≤ q ≤ 1`, the score is a
supermartingale for `𝒢`. -/
theorem supermartingale_score {W : ℕ → Ω → ℝ} (hadp : StronglyAdapted 𝒢 W)
    (hW0 : ∀ n ω, 0 ≤ W n ω) (hW1 : ∀ n ω, W n ω ≤ 1)
    (hcond : ∀ n, μ[W (n + 1) | 𝒢 n] ≤ᵐ[μ] fun _ ↦ p₀) (hp0 : 0 < p₀) (hp1 : p₀ < 1)
    (hq0 : p₀ ≤ q) (hq1 : q ≤ 1) : Supermartingale (score p₀ q W) 𝒢 μ := by
  set c₀ := (1 - q) / (1 - p₀) with hc₀
  set β := q / p₀ - (1 - q) / (1 - p₀) with hβ
  set K := (1 - q) / (1 - p₀) + q / p₀ with hK
  have hβ0 : 0 ≤ β := by
    have := scoreFactor_eq hp0 hp1 q 1
    rw [scoreFactor_one] at this
    have h2 : 0 ≤ (1 - p₀) * (q - p₀) / (p₀ * (1 - p₀)) :=
      div_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg hp0.le (by linarith))
    have h3 : (1 - q) / (1 - p₀) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    rw [hβ]; linarith
  set G : ℕ → Ω → ℝ := fun i ω ↦ scoreFactor p₀ q (W i ω) with hG
  have hGnn : ∀ i ω, 0 ≤ G i ω := fun i ω ↦ scoreFactor_nonneg hp0 hp1 hq0 hq1 (hW0 i ω) (hW1 i ω)
  have hGK : ∀ i ω, G i ω ≤ K := fun i ω ↦ scoreFactor_le hp0 hp1 hq0 hq1 (hW0 i ω) (hW1 i ω)
  have hGaff : ∀ i, G i = (fun _ ↦ c₀) + β • W i := by
    intro i; funext ω; simp [hG, scoreFactor, hc₀, hβ, smul_eq_mul, mul_comm]
  have hGm : ∀ i, StronglyMeasurable[𝒢 i] (G i) := fun i ↦ by
    rw [hGaff]; exact stronglyMeasurable_const.add ((hadp i).const_smul β)
  have hZnn : ∀ n ω, 0 ≤ score p₀ q W n ω := fun n ω ↦ prod_nonneg fun i _ ↦ hGnn _ _
  have hZbd : ∀ n ω, score p₀ q W n ω ≤ K ^ n := fun n ω ↦ by
    calc score p₀ q W n ω ≤ ∏ _i ∈ range n, K :=
          prod_le_prod₀ (fun i _ ↦ hGnn _ _) (fun i _ ↦ hGK _ _)
      _ = K ^ n := by rw [prod_const, card_range]
  have hadpZ : StronglyAdapted 𝒢 (score p₀ q W) := by
    intro n
    have : score p₀ q W n = ∏ i ∈ range n, G (i + 1) := by
      funext ω; simp [score, hG, Finset.prod_apply]
    rw [this]
    refine Finset.stronglyMeasurable_prod _ fun i hi ↦ ?_
    exact (hGm (i + 1)).mono (𝒢.mono (by simpa using Finset.mem_range.mp hi))
  have hint : ∀ n, Integrable (score p₀ q W n) μ := fun n ↦
    Integrable.of_bound ((hadpZ n).mono (𝒢.le n)).aestronglyMeasurable (K ^ n)
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hZnn n ω)]; exact hZbd n ω)
  have hWint : ∀ i, Integrable (W i) μ := fun i ↦
    Integrable.of_bound ((hadp i).mono (𝒢.le i)).aestronglyMeasurable 1
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hW0 i ω)]; exact hW1 i ω)
  have hGint : ∀ i, Integrable (G i) μ := fun i ↦ by
    rw [hGaff]; exact (integrable_const _).add ((hWint i).smul β)
  refine supermartingale_nat hadpZ hint fun n ↦ ?_
  have hsplit : score p₀ q W (n + 1) = score p₀ q W n * G (n + 1) := by
    funext ω; simp [score, prod_range_succ, hG]
  rw [hsplit]
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := 𝒢 n) (μ := μ)
    (hadpZ n) (by rw [← hsplit]; exact hint (n + 1)) (hGint (n + 1))
  have hlin : μ[G (n + 1) | 𝒢 n] =ᵐ[μ] (fun _ ↦ c₀) + β • μ[W (n + 1) | 𝒢 n] := by
    rw [hGaff]
    filter_upwards [condExp_add (integrable_const c₀) ((hWint (n + 1)).smul β) (𝒢 n),
      condExp_smul (μ := μ) β (W (n + 1)) (𝒢 n)] with ω h1 h2
    rw [h1, Pi.add_apply, h2, condExp_const (𝒢.le n)]
    rfl
  filter_upwards [hpull, hlin, hcond n] with ω h1 h2 h3
  rw [h1, Pi.mul_apply, h2]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hle : c₀ + β * μ[W (n + 1) | 𝒢 n] ω ≤ 1 := by
    have := scoreFactor_self hp0 hp1 q
    unfold scoreFactor at this
    rw [hc₀, hβ]
    nlinarith
  exact mul_le_of_le_one_right (hZnn n ω) hle

lemma score_zero (W : ℕ → Ω → ℝ) : score p₀ q W 0 = fun _ ↦ 1 := by
  funext ω; simp [score]

/-- **Checking after every outcome, within `N` outcomes.** Under the hypotheses of
`supermartingale_score`, the chance that the score reaches `1/α` (for `0 < α`) at some outcome
`n ≤ N` is at most `α`. -/
theorem measureReal_exists_le_score {W : ℕ → Ω → ℝ} (hadp : StronglyAdapted 𝒢 W)
    (hW0 : ∀ n ω, 0 ≤ W n ω) (hW1 : ∀ n ω, W n ω ≤ 1)
    (hcond : ∀ n, μ[W (n + 1) | 𝒢 n] ≤ᵐ[μ] fun _ ↦ p₀) (hp0 : 0 < p₀) (hp1 : p₀ < 1)
    (hq0 : p₀ ≤ q) (hq1 : q ≤ 1) {α : ℝ} (hα : 0 < α) (N : ℕ) :
    μ.real {ω | ∃ n ≤ N, 1 / α ≤ score p₀ q W n ω} ≤ α := by
  have h := measureReal_exists_le_of_supermartingale
    (supermartingale_score hadp hW0 hW1 hcond hp0 hp1 hq0 hq1)
    (fun n ω ↦ prod_nonneg fun i _ ↦ scoreFactor_nonneg hp0 hp1 hq0 hq1 (hW0 _ ω) (hW1 _ ω))
    (one_div_pos.mpr hα) N
  rw [score_zero] at h
  simpa using h

/-- **Checking after every outcome, with no limit.** Under the hypotheses of
`supermartingale_score`, the chance that the score ever reaches `1/α` is at most `α`. -/
theorem measureReal_exists_le_score_ever {W : ℕ → Ω → ℝ} (hadp : StronglyAdapted 𝒢 W)
    (hW0 : ∀ n ω, 0 ≤ W n ω) (hW1 : ∀ n ω, W n ω ≤ 1)
    (hcond : ∀ n, μ[W (n + 1) | 𝒢 n] ≤ᵐ[μ] fun _ ↦ p₀) (hp0 : 0 < p₀) (hp1 : p₀ < 1)
    (hq0 : p₀ ≤ q) (hq1 : q ≤ 1) {α : ℝ} (hα : 0 < α) :
    μ.real {ω | ∃ n, 1 / α ≤ score p₀ q W n ω} ≤ α := by
  have hU : {ω | ∃ n, 1 / α ≤ score p₀ q W n ω} =
      ⋃ N, {ω | ∃ n ≤ N, 1 / α ≤ score p₀ q W n ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨fun ⟨n, h⟩ ↦ ⟨n, n, le_rfl, h⟩, fun ⟨_, n, _, h⟩ ↦ ⟨n, h⟩⟩
  have hmono : Monotone fun N ↦ {ω | ∃ n ≤ N, 1 / α ≤ score p₀ q W n ω} := by
    intro N M hNM ω ⟨n, hn, h⟩
    exact ⟨n, hn.trans hNM, h⟩
  rw [hU]
  refine measureReal_iUnion_le_of_monotone hmono
    fun N ↦ measureReal_exists_le_score hadp hW0 hW1 hcond hp0 hp1 hq0 hq1 hα N

end ClassicalLean.Probability.LikelihoodScore
