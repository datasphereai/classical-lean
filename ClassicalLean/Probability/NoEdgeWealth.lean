/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Probability.LikelihoodScore

/-!
# A test for "no edge" by a stake chosen from the past

Returns `X n` are adapted to a filtration `𝒢`, bounded below by `-c` (with `0 < c`) and above by
some `C`, and have no edge: the mean of the next return given the past is at most `0`,
`μ[X (n+1) | 𝒢 n] ≤ 0` almost everywhere. Before each return a stake `L n` is chosen from what is
known at that time (`L` adapted to `𝒢`), with `0 ≤ L n ≤ 1/c`. The wealth after `n` returns is
`wealth L X n = ∏ i < n, (1 + L i · X (i + 1))`.

* `supermartingale_wealth`: the wealth starts at `1`, is never negative, and is a supermartingale.
* `measureReal_exists_le_wealth`: the chance that the wealth reaches `1/α` (`0 < α`) within `N`
  returns is at most `α`.
* `measureReal_exists_le_wealth_ever`: the same with no limit on the number of returns.
* `integral_wealth_le_one`: the mean of the wealth after any fixed number `N` of returns is at most
  `1`, so that wealth is an e-value.

No independence between returns is assumed. The ceiling `C` only makes every wealth integrable;
its size never enters the bounds. It cannot simply be dropped: Mathlib sets the conditional mean
of a non-integrable function to `0`, so without a ceiling (or integrable returns) the no-edge
condition would hold for free. A return of `-1` with chance `1/2`, and otherwise a heavy tail
with chance `1/2` of being at least `9` and infinite mean, staked at `L 0 = 1`, would reach `10`
with chance `1/2 > 1/10`.

The second part applies this to the win score of `LikelihoodScore` with `q` replaced by a value
`Q n` chosen from earlier outcomes only, `p₀ ≤ Q n ≤ 1`: `scorePred p₀ Q W n` is the wealth with
returns `W - p₀`, `c = p₀` and stakes `(Q - p₀)/(p₀ (1 - p₀))` (`scorePred_eq_wealth`), so it
gets the same three bounds. This is not the case of a `q` recomputed from all the outcomes and
then applied to the whole history: that re-scores the past with each new `q`, and with
`p₀ = 1/2`, `α = 1/20` and 200 outcomes its false alarm chance is `0.094`.

Each hypothesis on the stakes is needed. With `c = 1` and the return `-1` every time, the stake
`L = 3 > 1/c` gives wealth `-2` and then `4`; the stake `L = -1 < 0` gives wealth `2`. A stake
that sees the return it is placed on (`1/2` before a gain, `0` before a loss) on returns `-1/2`
or `1` with chances `2/3` and `1/3` reaches `10` within 14 returns with chance `0.310 > 1/10`.

`wealthQ` computes the wealth over `ℚ`; `cast_wealthQ` says it agrees with `wealth`.
-/

open MeasureTheory Filter Finset
open ClassicalLean.Probability.MaximalInequality ClassicalLean.Probability.RuinBound
  ClassicalLean.Probability.LikelihoodScore

namespace ClassicalLean.Probability.NoEdgeWealth

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The wealth after `n` returns, starting from `1`: each return `X (i + 1)` multiplies it by
`1 + L i · X (i + 1)`, where `L i` is the stake placed before that return. -/
noncomputable def wealth (L X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∏ i ∈ range n, (1 + L i ω * X (i + 1) ω)

lemma wealth_zero (L X : ℕ → Ω → ℝ) : wealth L X 0 = fun _ ↦ 1 := by
  funext ω; simp [wealth]

lemma wealth_succ (L X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    wealth L X (n + 1) ω = wealth L X n ω * (1 + L n ω * X (n + 1) ω) := by
  simp [wealth, prod_range_succ]

/-- A stake in `[0, 1/c]` on a return of at least `-c` never loses more than all of the wealth. -/
lemma one_add_mul_nonneg {c l x : ℝ} (hc : 0 < c) (hx : -c ≤ x) (hl0 : 0 ≤ l) (hl1 : l ≤ 1 / c) :
    0 ≤ 1 + l * x := by
  have h1 : l * c ≤ 1 := (le_div_iff₀ hc).mp hl1
  nlinarith [mul_le_mul_of_nonneg_left hx hl0]

lemma one_add_mul_le {c C l x : ℝ} (hx : x ≤ C) (hl0 : 0 ≤ l) (hl1 : l ≤ 1 / c) :
    1 + l * x ≤ 1 + max C 0 / c := by
  have h1 : l * x ≤ l * max C 0 := mul_le_mul_of_nonneg_left (hx.trans (le_max_left _ _)) hl0
  have h2 : l * max C 0 ≤ 1 / c * max C 0 := mul_le_mul_of_nonneg_right hl1 (le_max_right _ _)
  have h3 : 1 / c * max C 0 = max C 0 / c := by ring
  linarith

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {𝒢 : Filtration ℕ m0}

lemma wealth_nonneg {L X : ℕ → Ω → ℝ} {c : ℝ} (hc : 0 < c) (hXlo : ∀ n ω, -c ≤ X n ω)
    (hL0 : ∀ n ω, 0 ≤ L n ω) (hL1 : ∀ n ω, L n ω ≤ 1 / c) (n : ℕ) (ω : Ω) :
    0 ≤ wealth L X n ω :=
  prod_nonneg fun i _ ↦ one_add_mul_nonneg hc (hXlo _ ω) (hL0 i ω) (hL1 i ω)

/-- **With no edge, the wealth is a supermartingale.** Returns `X` and stakes `L` adapted to `𝒢`,
`-c ≤ X n ≤ C` with `0 < c`, `μ[X (n+1) | 𝒢 n] ≤ 0`, and `0 ≤ L n ≤ 1/c`. -/
theorem supermartingale_wealth {L X : ℕ → Ω → ℝ} {c C : ℝ} (hX : StronglyAdapted 𝒢 X)
    (hL : StronglyAdapted 𝒢 L) (hc : 0 < c) (hXlo : ∀ n ω, -c ≤ X n ω) (hXhi : ∀ n ω, X n ω ≤ C)
    (hcond : ∀ n, μ[X (n + 1) | 𝒢 n] ≤ᵐ[μ] 0)
    (hL0 : ∀ n ω, 0 ≤ L n ω) (hL1 : ∀ n ω, L n ω ≤ 1 / c) :
    Supermartingale (wealth L X) 𝒢 μ := by
  set K := 1 + max C 0 / c with hK
  set G : ℕ → Ω → ℝ := fun i ω ↦ 1 + L i ω * X (i + 1) ω with hG
  have hGnn : ∀ i ω, 0 ≤ G i ω := fun i ω ↦ one_add_mul_nonneg hc (hXlo _ ω) (hL0 i ω) (hL1 i ω)
  have hGK : ∀ i ω, G i ω ≤ K := fun i ω ↦ one_add_mul_le (hXhi _ ω) (hL0 i ω) (hL1 i ω)
  have hGm : ∀ i, StronglyMeasurable[𝒢 (i + 1)] (G i) := fun i ↦
    stronglyMeasurable_const.add (((hL i).mono (𝒢.mono (Nat.le_succ i))).mul (hX (i + 1)))
  have hWnn : ∀ n ω, 0 ≤ wealth L X n ω := wealth_nonneg hc hXlo hL0 hL1
  have hWbd : ∀ n ω, wealth L X n ω ≤ K ^ n := fun n ω ↦ by
    calc wealth L X n ω ≤ ∏ _i ∈ range n, K :=
          prod_le_prod₀ (fun i _ ↦ hGnn _ _) (fun i _ ↦ hGK _ _)
      _ = K ^ n := by rw [prod_const, card_range]
  have hadpW : StronglyAdapted 𝒢 (wealth L X) := by
    intro n
    have : wealth L X n = ∏ i ∈ range n, G i := by
      funext ω; simp [wealth, hG, Finset.prod_apply]
    rw [this]
    refine Finset.stronglyMeasurable_prod _ fun i hi ↦ ?_
    exact (hGm i).mono (𝒢.mono (by simpa using Finset.mem_range.mp hi))
  have hint : ∀ n, Integrable (wealth L X n) μ := fun n ↦
    Integrable.of_bound ((hadpW n).mono (𝒢.le n)).aestronglyMeasurable (K ^ n)
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hWnn n ω)]; exact hWbd n ω)
  have hXabs : ∀ n ω, |X n ω| ≤ c + |C| := fun n ω ↦
    abs_le.mpr ⟨by linarith [abs_nonneg C, hXlo n ω], by linarith [le_abs_self C, hXhi n ω]⟩
  have hXint : ∀ n, Integrable (X n) μ := fun n ↦
    Integrable.of_bound ((hX n).mono (𝒢.le n)).aestronglyMeasurable (c + |C|)
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hXabs n ω)
  have hLXint : ∀ n, Integrable (L n * X (n + 1)) μ := fun n ↦
    Integrable.of_bound
      (((hL n).mono (𝒢.le n)).mul ((hX (n + 1)).mono (𝒢.le (n + 1)))).aestronglyMeasurable
      (1 / c * (c + |C|))
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul, abs_of_nonneg (hL0 n ω)]
        exact mul_le_mul (hL1 n ω) (hXabs _ ω) (abs_nonneg _) (by positivity))
  have hGeq : ∀ i, G i = (fun _ ↦ (1 : ℝ)) + L i * X (i + 1) := fun i ↦ by
    funext ω; simp [hG]
  have hGint : ∀ i, Integrable (G i) μ := fun i ↦ by
    rw [hGeq]; exact (integrable_const _).add (hLXint i)
  refine supermartingale_nat hadpW hint fun n ↦ ?_
  have hsplit : wealth L X (n + 1) = wealth L X n * G n := by
    funext ω; simp [wealth_succ, hG]
  rw [hsplit]
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := 𝒢 n) (μ := μ)
    (hadpW n) (by rw [← hsplit]; exact hint (n + 1)) (hGint n)
  have hpullL := condExp_mul_of_stronglyMeasurable_left (m := 𝒢 n) (μ := μ)
    (hL n) (hLXint n) (hXint (n + 1))
  have hlin : μ[G n | 𝒢 n] =ᵐ[μ] (fun _ ↦ (1 : ℝ)) + μ[L n * X (n + 1) | 𝒢 n] := by
    rw [hGeq]
    filter_upwards [condExp_add (integrable_const (1 : ℝ)) (hLXint n) (𝒢 n)] with ω h1
    rw [h1, Pi.add_apply, condExp_const (𝒢.le n)]
    rfl
  filter_upwards [hpull, hlin, hpullL, hcond n] with ω h1 h2 h3 h4
  rw [h1, Pi.mul_apply, h2, Pi.add_apply, h3, Pi.mul_apply]
  have h5 : L n ω * μ[X (n + 1) | 𝒢 n] ω ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (hL0 n ω) (by simpa using h4)
  exact mul_le_of_le_one_right (hWnn n ω) (by linarith)

/-- **Checking after every return, within `N` returns.** Under the hypotheses of
`supermartingale_wealth`, the chance that the wealth reaches `1/α` (for `0 < α`) at some `n ≤ N`
is at most `α`. -/
theorem measureReal_exists_le_wealth {L X : ℕ → Ω → ℝ} {c C : ℝ} (hX : StronglyAdapted 𝒢 X)
    (hL : StronglyAdapted 𝒢 L) (hc : 0 < c) (hXlo : ∀ n ω, -c ≤ X n ω) (hXhi : ∀ n ω, X n ω ≤ C)
    (hcond : ∀ n, μ[X (n + 1) | 𝒢 n] ≤ᵐ[μ] 0)
    (hL0 : ∀ n ω, 0 ≤ L n ω) (hL1 : ∀ n ω, L n ω ≤ 1 / c) {α : ℝ} (hα : 0 < α) (N : ℕ) :
    μ.real {ω | ∃ n ≤ N, 1 / α ≤ wealth L X n ω} ≤ α := by
  have h := measureReal_exists_le_of_supermartingale
    (supermartingale_wealth hX hL hc hXlo hXhi hcond hL0 hL1) (wealth_nonneg hc hXlo hL0 hL1)
    (one_div_pos.mpr hα) N
  rw [wealth_zero] at h
  simpa using h

/-- **Checking after every return, with no limit.** Under the hypotheses of
`supermartingale_wealth`, the chance that the wealth ever reaches `1/α` is at most `α`. -/
theorem measureReal_exists_le_wealth_ever {L X : ℕ → Ω → ℝ} {c C : ℝ} (hX : StronglyAdapted 𝒢 X)
    (hL : StronglyAdapted 𝒢 L) (hc : 0 < c) (hXlo : ∀ n ω, -c ≤ X n ω) (hXhi : ∀ n ω, X n ω ≤ C)
    (hcond : ∀ n, μ[X (n + 1) | 𝒢 n] ≤ᵐ[μ] 0)
    (hL0 : ∀ n ω, 0 ≤ L n ω) (hL1 : ∀ n ω, L n ω ≤ 1 / c) {α : ℝ} (hα : 0 < α) :
    μ.real {ω | ∃ n, 1 / α ≤ wealth L X n ω} ≤ α := by
  have hU : {ω | ∃ n, 1 / α ≤ wealth L X n ω} =
      ⋃ N, {ω | ∃ n ≤ N, 1 / α ≤ wealth L X n ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨fun ⟨n, h⟩ ↦ ⟨n, n, le_rfl, h⟩, fun ⟨_, n, _, h⟩ ↦ ⟨n, h⟩⟩
  have hmono : Monotone fun N ↦ {ω | ∃ n ≤ N, 1 / α ≤ wealth L X n ω} := by
    intro N M hNM ω ⟨n, hn, h⟩
    exact ⟨n, hn.trans hNM, h⟩
  rw [hU]
  exact measureReal_iUnion_le_of_monotone hmono
    fun N ↦ measureReal_exists_le_wealth hX hL hc hXlo hXhi hcond hL0 hL1 hα N

/-- **The final wealth is an e-value.** Under the hypotheses of `supermartingale_wealth`, the
mean of the wealth after any fixed number `N` of returns is at most `1`. -/
theorem integral_wealth_le_one {L X : ℕ → Ω → ℝ} {c C : ℝ} (hX : StronglyAdapted 𝒢 X)
    (hL : StronglyAdapted 𝒢 L) (hc : 0 < c) (hXlo : ∀ n ω, -c ≤ X n ω) (hXhi : ∀ n ω, X n ω ≤ C)
    (hcond : ∀ n, μ[X (n + 1) | 𝒢 n] ≤ᵐ[μ] 0)
    (hL0 : ∀ n ω, 0 ≤ L n ω) (hL1 : ∀ n ω, L n ω ≤ 1 / c) (N : ℕ) :
    ∫ ω, wealth L X N ω ∂μ ≤ 1 := by
  have h := (supermartingale_wealth hX hL hc hXlo hXhi hcond hL0 hL1).setIntegral_le
    (Nat.zero_le N) MeasurableSet.univ
  simpa [wealth_zero] using h

/-! ### The win score with `q` chosen from earlier outcomes -/

/-- The win score of `LikelihoodScore` with the fixed `q` replaced by `Q i`, the value used for
outcome `i + 1`: `∏ i < n, scoreFactor p₀ (Q i) (W (i + 1))`. -/
noncomputable def scorePred (p₀ : ℝ) (Q W : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∏ i ∈ range n, scoreFactor p₀ (Q i ω) (W (i + 1) ω)

/-- The score is the wealth with returns `W - p₀` and stakes `(Q - p₀)/(p₀ (1 - p₀))`. -/
theorem scorePred_eq_wealth {p₀ : ℝ} (hp0 : 0 < p₀) (hp1 : p₀ < 1) (Q W : ℕ → Ω → ℝ) :
    scorePred p₀ Q W =
      wealth (fun i ω ↦ (Q i ω - p₀) / (p₀ * (1 - p₀))) (fun i ω ↦ W i ω - p₀) := by
  funext n ω
  unfold scorePred wealth
  refine prod_congr rfl fun i _ ↦ ?_
  rw [scoreFactor_eq hp0 hp1]
  ring

section scorePred

variable {p₀ : ℝ} {Q W : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
lemma stronglyAdapted_stake (hQ : StronglyAdapted 𝒢 Q) :
    StronglyAdapted 𝒢 (fun i ω ↦ (Q i ω - p₀) / (p₀ * (1 - p₀))) := fun i ↦
  (((hQ i).measurable.sub_const p₀).div_const _).stronglyMeasurable

omit [IsProbabilityMeasure μ] in
lemma stronglyAdapted_centred (hW : StronglyAdapted 𝒢 W) :
    StronglyAdapted 𝒢 (fun i ω ↦ W i ω - p₀) := fun i ↦
  ((hW i).measurable.sub_const p₀).stronglyMeasurable

lemma stake_nonneg (hp0 : 0 < p₀) (hp1 : p₀ < 1) (hQ0 : ∀ n ω, p₀ ≤ Q n ω) (n : ℕ) (ω : Ω) :
    0 ≤ (Q n ω - p₀) / (p₀ * (1 - p₀)) :=
  div_nonneg (by linarith [hQ0 n ω]) (mul_nonneg hp0.le (by linarith))

lemma stake_le (hp0 : 0 < p₀) (hp1 : p₀ < 1) (hQ1 : ∀ n ω, Q n ω ≤ 1) (n : ℕ) (ω : Ω) :
    (Q n ω - p₀) / (p₀ * (1 - p₀)) ≤ 1 / p₀ := by
  have h1 : 0 < p₀ * (1 - p₀) := mul_pos hp0 (by linarith)
  rw [div_le_div_iff₀ h1 hp0]
  nlinarith [hQ1 n ω]

lemma condExp_centred_nonpos (hW : StronglyAdapted 𝒢 W) (hW0 : ∀ n ω, 0 ≤ W n ω)
    (hW1 : ∀ n ω, W n ω ≤ 1) (hcond : ∀ n, μ[W (n + 1) | 𝒢 n] ≤ᵐ[μ] fun _ ↦ p₀) (n : ℕ) :
    μ[fun ω ↦ W (n + 1) ω - p₀ | 𝒢 n] ≤ᵐ[μ] 0 := by
  have hWint : Integrable (W (n + 1)) μ :=
    Integrable.of_bound ((hW (n + 1)).mono (𝒢.le (n + 1))).aestronglyMeasurable 1
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hW0 _ ω)]; exact hW1 _ ω)
  have heq : (fun ω ↦ W (n + 1) ω - p₀) = W (n + 1) - fun _ ↦ p₀ := rfl
  rw [heq]
  filter_upwards [condExp_sub hWint (integrable_const p₀) (𝒢 n), hcond n] with ω h1 h2
  rw [h1, Pi.sub_apply, condExp_const (𝒢.le n)]
  simpa using h2

/-- **The score with `Q` from earlier outcomes is a supermartingale.** Outcomes `W` in `[0, 1]`
and values `Q` in `[p₀, 1]`, both adapted to `𝒢`, win chance given the past at most `p₀`, with
`0 < p₀ < 1`. -/
theorem supermartingale_scorePred (hW : StronglyAdapted 𝒢 W) (hQ : StronglyAdapted 𝒢 Q)
    (hW0 : ∀ n ω, 0 ≤ W n ω) (hW1 : ∀ n ω, W n ω ≤ 1)
    (hcond : ∀ n, μ[W (n + 1) | 𝒢 n] ≤ᵐ[μ] fun _ ↦ p₀) (hp0 : 0 < p₀) (hp1 : p₀ < 1)
    (hQ0 : ∀ n ω, p₀ ≤ Q n ω) (hQ1 : ∀ n ω, Q n ω ≤ 1) :
    Supermartingale (scorePred p₀ Q W) 𝒢 μ := by
  rw [scorePred_eq_wealth hp0 hp1]
  exact supermartingale_wealth (C := 1 - p₀) (stronglyAdapted_centred hW) (stronglyAdapted_stake hQ)
    hp0 (fun n ω ↦ by linarith [hW0 n ω]) (fun n ω ↦ by linarith [hW1 n ω])
    (condExp_centred_nonpos hW hW0 hW1 hcond) (stake_nonneg hp0 hp1 hQ0) (stake_le hp0 hp1 hQ1)

/-- **The score with `Q` from earlier outcomes, within `N` outcomes.** Under the hypotheses of
`supermartingale_scorePred`, the chance that it reaches `1/α` at some `n ≤ N` is at most `α`. -/
theorem measureReal_exists_le_scorePred (hW : StronglyAdapted 𝒢 W) (hQ : StronglyAdapted 𝒢 Q)
    (hW0 : ∀ n ω, 0 ≤ W n ω) (hW1 : ∀ n ω, W n ω ≤ 1)
    (hcond : ∀ n, μ[W (n + 1) | 𝒢 n] ≤ᵐ[μ] fun _ ↦ p₀) (hp0 : 0 < p₀) (hp1 : p₀ < 1)
    (hQ0 : ∀ n ω, p₀ ≤ Q n ω) (hQ1 : ∀ n ω, Q n ω ≤ 1) {α : ℝ} (hα : 0 < α) (N : ℕ) :
    μ.real {ω | ∃ n ≤ N, 1 / α ≤ scorePred p₀ Q W n ω} ≤ α := by
  rw [scorePred_eq_wealth hp0 hp1]
  exact measureReal_exists_le_wealth (C := 1 - p₀) (stronglyAdapted_centred hW)
    (stronglyAdapted_stake hQ) hp0 (fun n ω ↦ by linarith [hW0 n ω])
    (fun n ω ↦ by linarith [hW1 n ω]) (condExp_centred_nonpos hW hW0 hW1 hcond)
    (stake_nonneg hp0 hp1 hQ0) (stake_le hp0 hp1 hQ1) hα N

/-- **The score with `Q` from earlier outcomes, with no limit.** Under the hypotheses of
`supermartingale_scorePred`, the chance that it ever reaches `1/α` is at most `α`. -/
theorem measureReal_exists_le_scorePred_ever (hW : StronglyAdapted 𝒢 W) (hQ : StronglyAdapted 𝒢 Q)
    (hW0 : ∀ n ω, 0 ≤ W n ω) (hW1 : ∀ n ω, W n ω ≤ 1)
    (hcond : ∀ n, μ[W (n + 1) | 𝒢 n] ≤ᵐ[μ] fun _ ↦ p₀) (hp0 : 0 < p₀) (hp1 : p₀ < 1)
    (hQ0 : ∀ n ω, p₀ ≤ Q n ω) (hQ1 : ∀ n ω, Q n ω ≤ 1) {α : ℝ} (hα : 0 < α) :
    μ.real {ω | ∃ n, 1 / α ≤ scorePred p₀ Q W n ω} ≤ α := by
  rw [scorePred_eq_wealth hp0 hp1]
  exact measureReal_exists_le_wealth_ever (C := 1 - p₀) (stronglyAdapted_centred hW)
    (stronglyAdapted_stake hQ) hp0 (fun n ω ↦ by linarith [hW0 n ω])
    (fun n ω ↦ by linarith [hW1 n ω]) (condExp_centred_nonpos hW hW0 hW1 hcond)
    (stake_nonneg hp0 hp1 hQ0) (stake_le hp0 hp1 hQ1) hα

/-- **The score with `Q` from earlier outcomes is an e-value.** Under the hypotheses of
`supermartingale_scorePred`, its mean after any fixed number `N` of outcomes is at most `1`. -/
theorem integral_scorePred_le_one (hW : StronglyAdapted 𝒢 W) (hQ : StronglyAdapted 𝒢 Q)
    (hW0 : ∀ n ω, 0 ≤ W n ω) (hW1 : ∀ n ω, W n ω ≤ 1)
    (hcond : ∀ n, μ[W (n + 1) | 𝒢 n] ≤ᵐ[μ] fun _ ↦ p₀) (hp0 : 0 < p₀) (hp1 : p₀ < 1)
    (hQ0 : ∀ n ω, p₀ ≤ Q n ω) (hQ1 : ∀ n ω, Q n ω ≤ 1) (N : ℕ) :
    ∫ ω, scorePred p₀ Q W N ω ∂μ ≤ 1 := by
  rw [scorePred_eq_wealth hp0 hp1]
  exact integral_wealth_le_one (C := 1 - p₀) (stronglyAdapted_centred hW)
    (stronglyAdapted_stake hQ) hp0 (fun n ω ↦ by linarith [hW0 n ω])
    (fun n ω ↦ by linarith [hW1 n ω]) (condExp_centred_nonpos hW hW0 hW1 hcond)
    (stake_nonneg hp0 hp1 hQ0) (stake_le hp0 hp1 hQ1) N

end scorePred

/-! ### A computable wealth over `ℚ` -/

/-- The wealth over `ℚ`, for fixed sequences of stakes and returns. -/
def wealthQ (L X : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∏ i ∈ range n, (1 + L i * X (i + 1))

/-- `wealthQ` cast to `ℝ` is `wealth` of the cast sequences, at every point. -/
theorem cast_wealthQ (L X : ℕ → ℚ) (n : ℕ) (ω : Ω) :
    (wealthQ L X n : ℝ) = wealth (fun i _ ↦ (L i : ℝ)) (fun i _ ↦ (X i : ℝ)) n ω := by
  simp [wealthQ, wealth]

end ClassicalLean.Probability.NoEdgeWealth
