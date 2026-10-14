/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Probability.RuinBound
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import ClassicalLean.InformationTheory.Entropy

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
* `measureReal_sum_ge_le_exp_neg_relEntropy` (order LEAN-17): for `p₀ ≤ q < 1`, the chance that
  the first `N` outcomes sum to at least `q N` is at most `exp (-N · D(q ‖ p₀))`, `D` the relative
  entropy of `(q, 1 - q)` to `(p₀, 1 - p₀)`: the Chernoff–Hoeffding bound (Hoeffding 1963,
  Theorem 1) with no independence, only the conditional win chance. On that event the score is at
  least `exp (N · D)` (`exp_mul_relEntropy_le_score`, by concavity of `log`), so Ville's inequality
  gives the bound. `measureReal_sum_ge_le_exp_neg_sq`: so, by Pinsker's inequality for two
  outcomes, at most `exp (-2 N (q - p₀)²)`: the one-sided form of `DependentSampleMean`'s bound,
  without its factor `2`, for a conditional mean at most `p₀` rather than equal to it, and with no
  `StandardBorelSpace`.
  Needed (order LEAN-17's checks, line C5): the conditional chance (`W = 1` always, `p₀ = 1/2`,
  `q = 3/4`, `N = 4`: chance `1` against `0.593`), `p₀ ≤ q` (`q = 0`: `1` against `0.125`),
  `0 ≤ W` (`W = 1` or `-9` with chances `0.9`, `0.1`, `p₀ = 0.1`, `q = 1/2`, `N = 1`: `0.9`
  against `0.600`), `W ≤ 1` (`W = 2` or `0` with chances `1/4`, `3/4`, `p₀ = 1/2`, `q = 3/4`,
  `N = 20`: `0.102` against `0.073`) and adapted outcomes (every outcome a copy of one fair coin,
  trivial filtration, `N = 10`: `1/2` against `0.270`). `q < 1` is not shown needed: at `q = 1` the
  event is that every outcome is `1`, and the bound `p₀ ^ N` still holds; the proof uses `q < 1`
  so that both factors of the score are positive. Neither `0 < p₀` nor `p₀ < 1` is claimed needed;
  the second follows from `p₀ ≤ q < 1`.

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

section RelativeEntropy

open ClassicalLean.Simplex

/-- On a sequence of outcomes in `[0, 1]` whose sum after `N` of them is at least `q N`, the score
is at least `exp (N · D(q ‖ p₀))`, for `0 < p₀ ≤ q < 1`. -/
lemma exp_mul_relEntropy_le_score {W : ℕ → Ω → ℝ} (hW0 : ∀ n ω, 0 ≤ W n ω)
    (hW1 : ∀ n ω, W n ω ≤ 1) (hp0 : 0 < p₀) (hp1 : p₀ < 1) (hq0 : p₀ ≤ q) (hq1 : q < 1)
    (N : ℕ) (ω : Ω) (hS : q * N ≤ ∑ i ∈ range N, W (i + 1) ω) :
    Real.exp (N * relEntropy ![q, 1 - q] ![p₀, 1 - p₀]) ≤ score p₀ q W N ω := by
  set a := (1 - q) / (1 - p₀) with ha
  set b := q / p₀ with hb
  have ha0 : 0 < a := div_pos (by linarith) (by linarith)
  have hb0 : 0 < b := div_pos (by linarith) hp0
  have hla : Real.log a ≤ 0 := Real.log_nonpos ha0.le ((div_le_one (by linarith)).mpr (by linarith))
  have hlb : 0 ≤ Real.log b := Real.log_nonneg ((le_div_iff₀ hp0).mpr (by linarith))
  -- each factor is the mix `(1 - w) a + w b`, so its log is at least `(1 - w) log a + w log b`
  have hfac : ∀ w, 0 ≤ w → w ≤ 1 →
      (1 - w) * Real.log a + w * Real.log b ≤ Real.log (scoreFactor p₀ q w) ∧
        0 < scoreFactor p₀ q w := by
    intro w hw0 hw1
    have he : scoreFactor p₀ q w = (1 - w) * a + w * b := by
      simp only [scoreFactor, ha, hb]; ring
    have hpos : 0 < (1 - w) * a + w * b := by
      rcases eq_or_lt_of_le hw1 with rfl | hw1'
      · simp [hb0]
      · exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) ha0) (mul_nonneg hw0 hb0.le)
    refine ⟨?_, he ▸ hpos⟩
    rw [he]
    have := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.mpr ha0) (Set.mem_Ioi.mpr hb0)
      (by linarith : (0 : ℝ) ≤ 1 - w) hw0 (by ring)
    simpa [smul_eq_mul] using this
  have hpos : ∀ i ∈ range N, 0 < scoreFactor p₀ q (W (i + 1) ω) := fun i _ ↦
    (hfac _ (hW0 _ ω) (hW1 _ ω)).2
  have hscore : 0 < score p₀ q W N ω := prod_pos hpos
  have hlog : Real.log (score p₀ q W N ω) =
      ∑ i ∈ range N, Real.log (scoreFactor p₀ q (W (i + 1) ω)) :=
    Real.log_prod fun i hi ↦ (hpos i hi).ne'
  have hsum : ∑ i ∈ range N, ((1 - W (i + 1) ω) * Real.log a + W (i + 1) ω * Real.log b) ≤
      Real.log (score p₀ q W N ω) :=
    hlog ▸ sum_le_sum fun i _ ↦ (hfac _ (hW0 _ ω) (hW1 _ ω)).1
  have hD : relEntropy ![q, 1 - q] ![p₀, 1 - p₀] = q * Real.log b + (1 - q) * Real.log a := by
    rw [relEntropy_fin_two]
  rw [← Real.exp_log hscore]
  apply Real.exp_le_exp.mpr
  refine le_trans ?_ hsum
  rw [hD, sum_add_distrib, ← sum_mul, ← sum_mul, sum_sub_distrib, sum_const, card_range,
    nsmul_eq_mul, mul_one]
  nlinarith [mul_le_mul_of_nonneg_right hS (sub_nonneg.mpr (hla.trans hlb))]

/-- **The Chernoff bound in relative-entropy form, with no independence.** Outcomes in `[0, 1]`,
adapted, each with mean at most `p₀` given the past (`0 < p₀ < 1`): for `p₀ ≤ q < 1`, the chance
that the first `N` sum to at least `q N` is at most `exp (-N · D(q ‖ p₀))`, with `D` the relative
entropy of `(q, 1 - q)` to `(p₀, 1 - p₀)` (Hoeffding 1963, Theorem 1, here for dependent outcomes).
It is Ville's inequality for the score: on that event the score is at least `exp (N · D)`. -/
theorem measureReal_sum_ge_le_exp_neg_relEntropy {W : ℕ → Ω → ℝ} (hadp : StronglyAdapted 𝒢 W)
    (hW0 : ∀ n ω, 0 ≤ W n ω) (hW1 : ∀ n ω, W n ω ≤ 1)
    (hcond : ∀ n, μ[W (n + 1) | 𝒢 n] ≤ᵐ[μ] fun _ ↦ p₀) (hp0 : 0 < p₀) (hp1 : p₀ < 1)
    (hq0 : p₀ ≤ q) (hq1 : q < 1) (N : ℕ) :
    μ.real {ω | q * N ≤ ∑ i ∈ range N, W (i + 1) ω} ≤
      Real.exp (-(N * relEntropy ![q, 1 - q] ![p₀, 1 - p₀])) := by
  set α := Real.exp (-(N * relEntropy ![q, 1 - q] ![p₀, 1 - p₀]))
  have hα : 0 < α := Real.exp_pos _
  have hsub : {ω | q * N ≤ ∑ i ∈ range N, W (i + 1) ω} ⊆
      {ω | ∃ n ≤ N, 1 / α ≤ score p₀ q W n ω} := by
    intro ω hω
    refine ⟨N, le_rfl, ?_⟩
    rw [one_div, ← Real.exp_neg, neg_neg]
    exact exp_mul_relEntropy_le_score hW0 hW1 hp0 hp1 hq0 hq1 N ω hω
  exact (measureReal_mono hsub).trans
    (measureReal_exists_le_score hadp hW0 hW1 hcond hp0 hp1 hq0 hq1.le hα N)

/-- **Hoeffding's bound, from the relative-entropy form.** Under the same hypotheses the chance is
at most `exp (-2 N (q - p₀)²)`, by Pinsker's inequality for two outcomes
(`Simplex.two_mul_sq_sub_le_relEntropy`). -/
theorem measureReal_sum_ge_le_exp_neg_sq {W : ℕ → Ω → ℝ} (hadp : StronglyAdapted 𝒢 W)
    (hW0 : ∀ n ω, 0 ≤ W n ω) (hW1 : ∀ n ω, W n ω ≤ 1)
    (hcond : ∀ n, μ[W (n + 1) | 𝒢 n] ≤ᵐ[μ] fun _ ↦ p₀) (hp0 : 0 < p₀) (hp1 : p₀ < 1)
    (hq0 : p₀ ≤ q) (hq1 : q < 1) (N : ℕ) :
    μ.real {ω | q * N ≤ ∑ i ∈ range N, W (i + 1) ω} ≤ Real.exp (-(2 * N * (q - p₀) ^ 2)) := by
  refine (measureReal_sum_ge_le_exp_neg_relEntropy hadp hW0 hW1 hcond hp0 hp1 hq0 hq1 N).trans ?_
  apply Real.exp_le_exp.mpr
  have h := two_mul_sq_sub_le_relEntropy hp0 hp1 (hp0.le.trans hq0) hq1.le
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith [mul_le_mul_of_nonneg_left h hN]

end RelativeEntropy

end ClassicalLean.Probability.LikelihoodScore

open MeasureTheory ProbabilityTheory Filter in
/-- The hypotheses of `measureReal_sum_ge_le_exp_neg_relEntropy` hold together: under the uniform
probability on two points, with the filtration in which every time knows the outcome (each `𝒢 n`
is the whole σ-algebra, so the conditional mean of `W (n + 1)` is `W (n + 1)` itself), the
outcomes `W n`, `1/2` at the point `0` and `0` at the point `1`, lie in `[0, 1]` and are at most
`p₀ = 1/2`; and `p₀ = 1/2 ≤ q = 3/4 < 1`, with `N = 4`. -/
example := ClassicalLean.Probability.LikelihoodScore.measureReal_sum_ge_le_exp_neg_relEntropy
  (p₀ := 1 / 2) (q := 3 / 4) (Ω := Fin 2) (μ := uniformOn Set.univ)
  (𝒢 := Filtration.const ℕ (inferInstance : MeasurableSpace (Fin 2)) le_rfl)
  (W := fun _ ω ↦ if ω = 0 then 1 / 2 else 0)
  (fun _ ↦ (StronglyMeasurable.of_discrete :
    StronglyMeasurable[(inferInstance : MeasurableSpace (Fin 2))] _))
  (fun _ ω ↦ by fin_cases ω <;> norm_num) (fun _ ω ↦ by fin_cases ω <;> norm_num)
  (fun n ↦ by
    rw [condExp_of_stronglyMeasurable
      ((Filtration.const ℕ (inferInstance : MeasurableSpace (Fin 2)) le_rfl).le n)
      (StronglyMeasurable.of_discrete :
        StronglyMeasurable[(inferInstance : MeasurableSpace (Fin 2))] _)
      Integrable.of_finite]
    exact Eventually.of_forall fun ω ↦ by fin_cases ω <;> norm_num)
  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (N := 4)

open MeasureTheory ProbabilityTheory Filter in
/-- The hypotheses of `measureReal_sum_ge_le_exp_neg_sq` hold together: under the uniform
probability on two points, with the filtration in which every time knows the outcome (each `𝒢 n`
is the whole σ-algebra, so the conditional mean of `W (n + 1)` is `W (n + 1)` itself), the
outcomes `W n`, `1/2` at the point `0` and `0` at the point `1`, lie in `[0, 1]` and are at most
`p₀ = 1/2`; and `p₀ = 1/2 ≤ q = 3/4 < 1`, with `N = 4`. -/
example := ClassicalLean.Probability.LikelihoodScore.measureReal_sum_ge_le_exp_neg_sq
  (p₀ := 1 / 2) (q := 3 / 4) (Ω := Fin 2) (μ := uniformOn Set.univ)
  (𝒢 := Filtration.const ℕ (inferInstance : MeasurableSpace (Fin 2)) le_rfl)
  (W := fun _ ω ↦ if ω = 0 then 1 / 2 else 0)
  (fun _ ↦ (StronglyMeasurable.of_discrete :
    StronglyMeasurable[(inferInstance : MeasurableSpace (Fin 2))] _))
  (fun _ ω ↦ by fin_cases ω <;> norm_num) (fun _ ω ↦ by fin_cases ω <;> norm_num)
  (fun n ↦ by
    rw [condExp_of_stronglyMeasurable
      ((Filtration.const ℕ (inferInstance : MeasurableSpace (Fin 2)) le_rfl).le n)
      (StronglyMeasurable.of_discrete :
        StronglyMeasurable[(inferInstance : MeasurableSpace (Fin 2))] _)
      Integrable.of_finite]
    exact Eventually.of_forall fun ω ↦ by fin_cases ω <;> norm_num)
  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (N := 4)
