/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Probability.GamblersRuin
import ClassicalLean.Probability.LikelihoodScore

/-!
# The walk rarely climbs when its up-chance given the past is small

A walk moves by `±1` steps (`GamblersRuin.walk X n = X 0 + ⋯ + X (n − 1)`), each step known by the
next time, and the conditional chance of a step `+1` given the past is at most `p`:
`μ[(X n + 1) / 2 | 𝒢 n] ≤ p` almost everywhere, with `0 < p ≤ 1/2`. Neither independence nor an
exact law of the steps is assumed. Order CLOUD-MATH-6, bridge 154 of
`MATH-PLAN-library-2-bridges-2.md`.

* `measureReal_exists_ge_le_of_condProb` — the chance that the walk ever reaches `a` is at most
  `(p / (1 - p)) ^ a`. This is item 84's bound (`GamblersRuin.measureReal_exists_ge_le_of_biased`,
  for independent steps of one law, `p < 1 - p`) under a weaker hypothesis on the steps, and with
  `p = 1/2` allowed.

The proof: the wins `W (n + 1) = (X n + 1) / 2`, `W 0 = 0`, take values in `{0, 1}` and are
adapted; `LikelihoodScore`'s score with `p₀ = p` and `q = 1 - p` (`p ≤ 1/2` gives `p₀ ≤ q`) is
`r ^ wins · (1 / r) ^ losses` with `r = (1 - p) / p ≥ 1` (`score_eq_pow`), that is `r` to the power
of the walk; reaching `a` makes it at least `r ^ a`, and `measureReal_exists_le_score_ever` at
`α = (p / (1 - p)) ^ a = 1 / r ^ a` gives the bound.

The witness at the end of the file is `GamblersRuin`'s biased walk (independent coins with three
equally likely faces, a step up when the coin shows `0`), with `p = 1/3` and `a = 2`.
-/

open MeasureTheory ProbabilityTheory Filter Finset
open ClassicalLean.Probability.GamblersRuin ClassicalLean.Probability.LikelihoodScore

namespace ClassicalLean.Probability.RuinConditional

/-- **Ville's bound for the walk under a conditional up-chance** (bridge 154). For `±1` steps
`X n`, each known by time `n + 1` (`hX`), whose conditional chance of `+1` given time `n` is at most
`p` (`hcond`: the conditional mean of `(X n + 1) / 2`, the indicator of a step up), with
`0 < p ≤ 1/2`, the chance that the walk ever reaches `a` is at most `(p / (1 - p)) ^ a`. No
independence and no exact law of the steps; item 84's `measureReal_exists_ge_le_of_biased` is the
case of independent steps of one law. -/
theorem measureReal_exists_ge_le_of_condProb {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {𝒢 : Filtration ℕ m0} {X : ℕ → Ω → ℝ}
    (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n)) (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1)
    {p : ℝ} (hcond : ∀ n, μ[fun ω ↦ (X n ω + 1) / 2 | 𝒢 n] ≤ᵐ[μ] fun _ ↦ p)
    (hp0 : 0 < p) (hp : p ≤ 1 / 2) (a : ℕ) :
    μ.real {ω | ∃ n, (a : ℝ) ≤ walk X n ω} ≤ (p / (1 - p)) ^ a := by
  have hq : 0 < 1 - p := by linarith
  -- the wins: `W 0 = 0` and `W (n + 1) = (X n + 1) / 2`
  set W : ℕ → Ω → ℝ := fun n ω ↦ if n = 0 then 0 else (X (n - 1) ω + 1) / 2 with hWdef
  have hWs : ∀ n, W (n + 1) = fun ω ↦ (X n ω + 1) / 2 := fun n ↦ by
    funext ω; simp [hWdef]
  have hW1 : ∀ i ω, W (i + 1) ω = 1 ↔ X i ω = 1 := fun i ω ↦ by
    rw [hWs]; rcases hpm i ω with h | h <;> norm_num [h]
  have hW0 : ∀ i ω, W (i + 1) ω = 0 ↔ X i ω = -1 := fun i ω ↦ by
    rw [hWs]; rcases hpm i ω with h | h <;> norm_num [h]
  have hW01 : ∀ n ω, W n ω = 0 ∨ W n ω = 1 := by
    intro n ω
    rcases n with _ | n
    · left; simp [hWdef]
    · rcases hpm n ω with h | h
      · exact Or.inr ((hW1 n ω).2 h)
      · exact Or.inl ((hW0 n ω).2 h)
  have hadp : StronglyAdapted 𝒢 W := by
    intro n
    rcases n with _ | n
    · have h : W 0 = fun _ ↦ (0 : ℝ) := by funext ω; simp [hWdef]
      rw [h]
      exact stronglyMeasurable_const
    · rw [hWs]
      exact (((hX n).measurable.add_const 1).div_const 2).stronglyMeasurable
  have hcondW : ∀ n, μ[W (n + 1) | 𝒢 n] ≤ᵐ[μ] fun _ ↦ p := fun n ↦ by
    rw [hWs]; exact hcond n
  have hα : 0 < (p / (1 - p)) ^ a := pow_pos (div_pos hp0 hq) a
  have hever := measureReal_exists_le_score_ever (p₀ := p) (q := 1 - p) hadp
    (fun n ω ↦ by rcases hW01 n ω with h | h <;> norm_num [h])
    (fun n ω ↦ by rcases hW01 n ω with h | h <;> norm_num [h])
    hcondW hp0 (by linarith) (by linarith) (by linarith) hα
  refine (measureReal_mono
    (s₂ := {ω | ∃ n, 1 / (p / (1 - p)) ^ a ≤ score p (1 - p) W n ω}) ?_).trans hever
  rintro ω ⟨n, hn⟩
  refine ⟨n, ?_⟩
  -- on reaching `a`, the score `r ^ wins (1 / r) ^ losses` is at least `r ^ a`
  set r := (1 - p) / p with hr
  have hr1 : 1 ≤ r := by rw [hr, le_div_iff₀ hp0]; linarith
  have hrs : r * (p / (1 - p)) = 1 := by
    rw [hr]; field_simp
  set w := #{i ∈ range n | X i ω = 1} with hw
  set l := #{i ∈ range n | X i ω = -1} with hl
  have hscore : score p (1 - p) W n ω = r ^ w * (p / (1 - p)) ^ l := by
    rw [score_eq_pow hW01, sub_sub_cancel, hw, hl, ← hr]
    congr 2
    · exact congrArg _ (filter_congr fun i _ ↦ hW1 i ω)
    · exact congrArg _ (filter_congr fun i _ ↦ hW0 i ω)
  have hwalk : walk X n ω = w - l := by
    unfold walk
    rw [← sum_filter_add_sum_filter_not (range n) (fun i ↦ X i ω = 1)]
    have hnot : {i ∈ range n | ¬ X i ω = 1} = {i ∈ range n | X i ω = -1} :=
      filter_congr fun i _ ↦ by rcases hpm i ω with h | h <;> simp [h] <;> norm_num
    rw [hnot, sum_congr rfl fun i hi ↦ (mem_filter.1 hi).2,
      sum_congr rfl fun i hi ↦ (mem_filter.1 hi).2]
    simp [hw, hl, sub_eq_add_neg]
  have hal : a + l ≤ w := by
    have : (a : ℝ) + l ≤ w := by linarith
    exact_mod_cast this
  rw [hscore, one_div, ← inv_pow, inv_div, ← hr]
  calc r ^ a = r ^ (a + l) * (p / (1 - p)) ^ l := by
        rw [pow_add, mul_assoc, ← mul_pow, hrs, one_pow, mul_one]
    _ ≤ r ^ w * (p / (1 - p)) ^ l :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hr1 hal)
          (pow_nonneg (div_nonneg hp0.le hq.le) l)

end ClassicalLean.Probability.RuinConditional

open MeasureTheory ProbabilityTheory in
/-- The hypotheses of `measureReal_exists_ge_le_of_condProb` hold together: a biased walk, on the
space of sequences `ℕ → Fin 3` of independent coins with three equally likely faces (Mathlib's
`Measure.infinitePi` of the uniform law on `Fin 3`), as in `GamblersRuin`'s witness of
`measureReal_exists_ge_le_of_biased`. The step `X n` is `+1` when coin `n + 1` shows `0` and `-1`
otherwise; the filtration is the one the coins' values generate (read as `±1`), so step `n` is known
at time `n + 1`; every step moves the walk, which is never constant. Given time `n`, the conditional
chance of a step up is exactly `1/3` (`hcond` holds with equality): the step is independent of what
time `n` knows, so its conditional mean is its mean (`condExp_indep_eq`), and the mean of
`(X n + 1) / 2` is `1/3`. `p = 1/3`, with `0 < 1/3 < 1/2`, and the level `a = 2`: the bound
`(1/2) ^ 2 = 1/4` is below `1`. -/
example := ClassicalLean.Probability.RuinConditional.measureReal_exists_ge_le_of_condProb
  (Ω := ℕ → Fin 3)
  (μ := Measure.infinitePi fun _ ↦ uniformOn Set.univ)
  (𝒢 := Filtration.natural (fun i (ω : ℕ → Fin 3) ↦ if ω i = 0 then (1 : ℝ) else -1)
    fun i ↦ ((measurable_of_countable fun c : Fin 3 ↦ if c = 0 then (1 : ℝ) else -1).comp
      (measurable_pi_apply i)).stronglyMeasurable)
  (X := fun n ω ↦ if ω (n + 1) = 0 then 1 else -1)
  (fun n ↦ Filtration.stronglyAdapted_natural
    (u := fun i (ω : ℕ → Fin 3) ↦ if ω i = 0 then (1 : ℝ) else -1) _ (n + 1))
  (fun n ω ↦ by split_ifs <;> simp) (p := 1 / 3)
  (fun n ↦ by
    have hY : Measurable[MeasurableSpace.comap
        (fun ω : ℕ → Fin 3 ↦ if ω (n + 1) = 0 then (1 : ℝ) else -1) inferInstance]
        (fun ω : ℕ → Fin 3 ↦ if ω (n + 1) = 0 then (1 : ℝ) else -1) :=
      measurable_iff_comap_le.2 le_rfl
    refine (condExp_indep_eq
      (((measurable_of_countable fun c : Fin 3 ↦ if c = 0 then (1 : ℝ) else -1).comp
        (measurable_pi_apply (n + 1))).comap_le)
      ((Filtration.natural (fun i (ω : ℕ → Fin 3) ↦ if ω i = 0 then (1 : ℝ) else -1)
        fun i ↦ ((measurable_of_countable fun c : Fin 3 ↦ if c = 0 then (1 : ℝ) else -1).comp
          (measurable_pi_apply i)).stronglyMeasurable).le n)
      (((hY.add_const 1).div_const 2).stronglyMeasurable)
      ((iIndepFun_infinitePi (P := fun _ : ℕ ↦ (uniformOn Set.univ : Measure (Fin 3)))
        (X := fun _ (c : Fin 3) ↦ if c = 0 then (1 : ℝ) else -1)
        fun _ ↦ measurable_of_countable _).indep_comap_natural_of_lt _
          (Nat.lt_succ_self n))).le.trans (Eventually.of_forall fun _ ↦ le_of_eq ?_)
    rw [← integral_map (φ := fun ω : ℕ → Fin 3 ↦ ω (n + 1))
      (f := fun c : Fin 3 ↦ ((if c = 0 then (1 : ℝ) else -1) + 1) / 2)
      (measurable_pi_apply (n + 1)).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable,
      Measure.infinitePi_map_eval, integral_fintype Integrable.of_finite]
    simp [Measure.real, uniformOn_univ, Fin.sum_univ_three])
  (by norm_num) (by norm_num) (a := 2)
