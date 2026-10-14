/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The Neyman–Pearson lemma and the Karlin–Rubin theorem

Two hypotheses about where data `ω` come from, each given by a density against one measure `ν`:
`f₀` (the null) and `f₁` (the alternative). A **test** `φ : Ω → [0, 1]` rejects the null with
chance `φ ω` on seeing `ω`; values strictly between `0` and `1` are allowed (a *randomized* test).
Its **size** is `∫ φ f₀ dν`, the chance of rejecting when the null is true, and its **power** is
`∫ φ f₁ dν`, the chance of rejecting when the alternative is true.

* `IsTest`, `IsLikelihoodRatioTest` — a likelihood ratio test with threshold `k` rejects for sure
  where `f₁ > k f₀` and never where `f₁ < k f₀`; written without division.
* `power_le_of_likelihoodRatioTest` — order LEAN-24, item 55, **the Neyman–Pearson lemma**: for
  integrable `f₀, f₁` and `k ≥ 0`, a likelihood ratio test has the largest power among all tests
  whose size is at most its own.
* `exists_lrTest_size_eq`, `exists_isMostPowerful` — for a probability density `f₀` and `f₁ ≥ 0`,
  and
  every `α ∈ (0, 1]` the test `lrTest f₀ f₁ k γ = 1{f₁ > k f₀} + γ 1{f₁ = k f₀}` has size exactly
  `α` for some `k ≥ 0` and `γ ∈ [0, 1]`, so a most powerful test of size exactly `α` exists. The
  weight `γ` is needed: without randomization some sizes cannot be reached.
* `exists_measureReal_lt_add_mul_eq` — the step behind it: for a probability measure and a
  measurable `T`, every `α ∈ (0, 1)` is `P(T > c) + γ P(T = c)` for some `c` and `γ ∈ [0, 1]`
  (from Mathlib's `cdf`).
* `HasMonotoneLikelihoodRatio`, `thresholdTest`, `IsUniformlyMostPowerful`.
* `isUniformlyMostPowerful_of_monotoneLikelihoodRatio` — order LEAN-24, item 56, **the
  Karlin–Rubin theorem**, in a narrower form than the textbook's (below): for probability
  densities `f θ` with a monotone likelihood ratio in a statistic `S`, the test
  `1{S > c} + γ 1{S = c}` is uniformly most powerful, at its own size at `θ₀`, for the null
  `θ ≤ θ₀` against `θ > θ₀`. `exists_thresholdTest_size_eq` gives `c` and `γ` for every size in
  `(0, 1)`.

## The limit of item 56

`HasMonotoneLikelihoodRatio f S` asks, for `θ < θ'`, that `f θ' = g (S ω) · f θ` for one
nondecreasing `g ≥ 0`. This forces `f θ' = 0` wherever `f θ = 0`, so it excludes every model whose
support gains points as `θ` grows: the uniform law on `[0, θ]` (checked: at `x = 3/2`,
`f_1 = 0` and `f_2 = 1/2`) and the uniform law on `[θ, θ + 1]` (at `x = 5/4`, `f_0 = 0` and
`f_{1/2} = 1`). Textbooks allow the ratio to be `+∞` there; that form is not proved here (Dustin's
ruling, order LEAN-24). Two more points are stricter than "the ratio is a nondecreasing function
of `S`": `g` must be nondecreasing on all of `ℝ`, and the product must hold at every `ω`, not
almost everywhere. So a family whose ratio is unbounded on the range of `S` needs another choice
of `S` that gives the same tests: the laws with density `β (1 − x)^(β − 1)` on `(0, 1)`, indexed
by `θ = −β`, have a ratio unbounded as `x → 1`, so no such `g` exists for `S = x`, while
`S = −log (1 − x)` works (review r55). Models that qualify include normal laws with known
variance and mean `θ`
(`S = x`, `g` an increasing exponential), coin flips with chance `p ∈ (0, 1)` (`S` the number of
heads, `g(k) = (p'/p)^k ((1 − p')/(1 − p))^(n − k) = c rᵏ` with `r > 1`; also checked exactly
on a grid of 15 pairs `p < p'` for `n ≤ 6`), and shifted exponential laws on `[θ, ∞)`, whose
support shrinks as `θ` grows (`S = x`, `g(t) = e^(θ' − θ) 1{t ≥ θ'}`; review r55, which proved
this in Lean in its scratch folder). The theorem Lean proves is
`isUniformlyMostPowerful_of_monotoneLikelihoodRatio` as stated below.

## Hypotheses

Measured in order LEAN-24's checks (`checks.py`, exact rationals, on finite spaces with counting
measure). `k ≥ 0` is needed because no sign condition on `f₀` is assumed (`f₀ = −1`, `f₁ = 1/2`,
`k = −1`: the test `1` has size `−1 ≤ 0` and power `1/2 > 0`); for `f₀, f₁ ≥ 0` a negative `k`
does no harm, since such a test rejects wherever `f₀ + f₁ > 0` and so has power `∫ f₁`, the most
possible (also no counterexample in 19,683 small cases with `k = −1`). `φ ≤ 1` is needed (`φ =
(0, 1, 2)` beats a
likelihood ratio test of the same size `1/2`, power `3/2 > 1`), and so is `φ ≥ 0`
(`φ = (−1/2, 1, 1)`: size `1/4`, power `5/8 > 1/2`). Randomization: with `f₀ = (1/2, 1/2)` the
non-randomized tests have sizes `0, 1/2, 1` only. In the existence theorems, `f₁ ≥ 0` is what
makes `k ≥ 0` possible, `∫ f₀ = 1` is needed (`f₀ = (1/4, 1/4)` allows no size above `1/2`), and
size `0` can be out of reach (on `ℕ` with `f₀ n = 2^−(n+1)`, `f₁ n = 1/((n+1)(n+2))`). For
item 56, the monotone likelihood ratio is needed (three laws on two points where `(1, 0)` beats
the threshold test at `θ = 2`, power `3/4 > 1/4`), and `∫ f θ = 1` is needed for the size part
(`f₀ = (1, 1)`: size `1 > 1/2` at `θ = 0`). Lean's integral of a non-integrable function is `0`,
so the integrability hypotheses are kept. A remark, worked by hand and not measured: on `ℕ` with
counting measure, `f₀ n = 2^−(n+1)` and `f₁ = 1`, the likelihood ratio test `1` would have power
`0` (junk), below the power `1` of the test `1{0}`.

## What is cited

For works not read here, author, title and year only: J. Neyman and E. S. Pearson, "On the
Problem of the Most Efficient Tests of Statistical Hypotheses", 1933; S. Karlin and H. Rubin,
"The Theory of Decision Procedures for Distributions with Monotone Likelihood Ratio", 1956.

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-24): "neyman|pearson" and "most powerful|
likelihood ratio test|uniformly most" have no hit; "karlin|rubin|monotone likelihood" only
Rubin's theorem in group actions. Used: `cdf`, `StieltjesFunction.measure_Iio`,
`Monotone.tendsto_leftLim`, `integral_withDensity_eq_integral_smul`, `Integrable.bdd_mul`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ClassicalLean.Statistics

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A **test**: a measurable `φ` with values in `[0, 1]`, read as the chance of rejecting the null
hypothesis on seeing `ω`. Values strictly between `0` and `1` are allowed (a randomized test),
so that every size in `(0, 1)` can be reached exactly. -/
def IsTest (φ : Ω → ℝ) : Prop := Measurable φ ∧ ∀ ω, φ ω ∈ Icc (0 : ℝ) 1

/-- A **likelihood ratio test** with threshold `k` for densities `f₀` (null) and `f₁`
(alternative): it rejects for sure where `f₁ > k f₀` and never where `f₁ < k f₀`; where
`f₁ = k f₀` it may do anything. Written without division, so points with `f₀ = 0` need no
convention. -/
def IsLikelihoodRatioTest (f₀ f₁ : Ω → ℝ) (k : ℝ) (φ : Ω → ℝ) : Prop :=
  ∀ ω, (k * f₀ ω < f₁ ω → φ ω = 1) ∧ (f₁ ω < k * f₀ ω → φ ω = 0)

theorem IsTest.integrable_mul {ν : Measure Ω} {φ f : Ω → ℝ} (hφ : IsTest φ)
    (hf : Integrable f ν) : Integrable (fun ω ↦ φ ω * f ω) ν := by
  refine hf.bdd_mul (c := 1) hφ.1.aestronglyMeasurable (ae_of_all _ fun ω ↦ ?_)
  have h := hφ.2 ω
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [h.1, h.2]

/-- **The Neyman–Pearson lemma.** Let `f₀` and `f₁` be integrable functions on a measure space
`(Ω, ν)` (the densities of the null and the alternative), and `φ'` a likelihood ratio test with
threshold `k ≥ 0`. Every test `φ` whose size `∫ φ f₀` is at most that of `φ'` has power `∫ φ f₁`
at most that of `φ'`. The proof integrates `(φ' − φ)(f₁ − k f₀) ≥ 0`; no sign condition on `f₀`
or `f₁` is used. -/
theorem power_le_of_likelihoodRatioTest {ν : Measure Ω} {f₀ f₁ : Ω → ℝ}
    (hf₀ : Integrable f₀ ν) (hf₁ : Integrable f₁ ν) {k : ℝ} (hk : 0 ≤ k) {φ' φ : Ω → ℝ}
    (hφ' : IsTest φ') (hLR : IsLikelihoodRatioTest f₀ f₁ k φ') (hφ : IsTest φ)
    (hsize : ∫ ω, φ ω * f₀ ω ∂ν ≤ ∫ ω, φ' ω * f₀ ω ∂ν) :
    ∫ ω, φ ω * f₁ ω ∂ν ≤ ∫ ω, φ' ω * f₁ ω ∂ν := by
  have hpt : ∀ ω, 0 ≤ (φ' ω - φ ω) * (f₁ ω - k * f₀ ω) := by
    intro ω
    obtain ⟨h1, h2⟩ := hLR ω
    have hφω := hφ.2 ω
    rcases lt_trichotomy (k * f₀ ω) (f₁ ω) with h | h | h
    · rw [h1 h]
      exact mul_nonneg (by linarith [hφω.2]) (by linarith)
    · rw [← h, sub_self, mul_zero]
    · rw [h2 h]
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith [hφω.1]) (by linarith)
  have e : ∫ ω, (φ' ω - φ ω) * (f₁ ω - k * f₀ ω) ∂ν =
      (∫ ω, φ' ω * f₁ ω ∂ν - ∫ ω, φ ω * f₁ ω ∂ν) -
        k * (∫ ω, φ' ω * f₀ ω ∂ν - ∫ ω, φ ω * f₀ ω ∂ν) := by
    have : (fun ω ↦ (φ' ω - φ ω) * (f₁ ω - k * f₀ ω)) = fun ω ↦
        (φ' ω * f₁ ω - φ ω * f₁ ω) - k * (φ' ω * f₀ ω - φ ω * f₀ ω) := by
      ext ω; ring
    rw [this, integral_sub, integral_sub (hφ'.integrable_mul hf₁) (hφ.integrable_mul hf₁),
      integral_const_mul, integral_sub (hφ'.integrable_mul hf₀) (hφ.integrable_mul hf₀)]
    · exact (hφ'.integrable_mul hf₁).sub (hφ.integrable_mul hf₁)
    · exact ((hφ'.integrable_mul hf₀).sub (hφ.integrable_mul hf₀)).const_mul k
  have h0 := integral_nonneg (μ := ν) (f := fun ω ↦ (φ' ω - φ ω) * (f₁ ω - k * f₀ ω)) hpt
  rw [e] at h0
  nlinarith [mul_nonneg hk (sub_nonneg.2 hsize)]

/-- The **threshold test** in a statistic `S`: reject for sure when `S > c`, with chance `γ` when
`S = c`, never when `S < c`. -/
noncomputable def thresholdTest (S : Ω → ℝ) (c γ : ℝ) (ω : Ω) : ℝ :=
  if c < S ω then 1 else if S ω = c then γ else 0

theorem isTest_thresholdTest {S : Ω → ℝ} (hS : Measurable S) (c : ℝ) {γ : ℝ}
    (hγ : γ ∈ Icc (0 : ℝ) 1) : IsTest (thresholdTest S c γ) := by
  refine ⟨Measurable.ite (measurableSet_lt measurable_const hS) measurable_const
    (Measurable.ite (measurableSet_eq_fun hS measurable_const) measurable_const
      measurable_const), fun ω ↦ ?_⟩
  unfold thresholdTest
  split_ifs
  exacts [⟨zero_le_one, le_rfl⟩, hγ, ⟨le_rfl, zero_le_one⟩]

/-- The size of a threshold test under a finite measure: `P(S > c) + γ P(S = c)`. -/
theorem integral_thresholdTest {μ : Measure Ω} [IsFiniteMeasure μ] {S : Ω → ℝ}
    (hS : Measurable S) (c γ : ℝ) :
    ∫ ω, thresholdTest S c γ ω ∂μ = μ.real {ω | c < S ω} + γ * μ.real {ω | S ω = c} := by
  have hA : MeasurableSet {ω | c < S ω} := measurableSet_lt measurable_const hS
  have hB : MeasurableSet {ω | S ω = c} := measurableSet_eq_fun hS measurable_const
  have : thresholdTest S c γ = fun ω ↦ {ω | c < S ω}.indicator (fun _ ↦ (1 : ℝ)) ω +
      {ω | S ω = c}.indicator (fun _ ↦ γ) ω := by
    ext ω
    simp only [thresholdTest, indicator, mem_ofPred_eq]
    split_ifs with h1 h2 h2 <;> linarith
  rw [this, integral_add ((integrable_const _).indicator hA) ((integrable_const _).indicator hB),
    integral_indicator_const _ hA, integral_indicator_const _ hB, smul_eq_mul, smul_eq_mul,
    mul_one, mul_comm]

theorem exists_measureReal_lt_add_mul_eq {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → ℝ}
    (hT : Measurable T) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    ∃ c γ, γ ∈ Icc (0 : ℝ) 1 ∧ μ.real {ω | c < T ω} + γ * μ.real {ω | T ω = c} = α := by
  set ν := μ.map T with hν
  set F := cdf ν with hF
  have hFx : ∀ x, F x = μ.real {ω | T ω ≤ x} := fun x ↦ by
    rw [hF, cdf_eq_real, hν, map_measureReal_apply hT measurableSet_Iic]; rfl
  set S := {x | 1 - α ≤ F x} with hS
  have hne : S.Nonempty := by
    have := (tendsto_cdf_atTop (μ := ν)).eventually
      (lt_mem_nhds (show 1 - α < 1 by linarith [hα.1]))
    obtain ⟨x, hx⟩ := this.exists
    exact ⟨x, le_of_lt hx⟩
  have hlow : ∀ᶠ x in atBot, F x < 1 - α :=
    (tendsto_cdf_atBot (μ := ν)).eventually (gt_mem_nhds (show (0 : ℝ) < 1 - α by linarith [hα.2]))
  obtain ⟨x₀, hx₀⟩ := hlow.exists_forall_of_atBot
  have hbdd : BddBelow S := ⟨x₀, fun y hy ↦ by
    by_contra h
    push Not at h
    exact absurd hy (not_le.2 (hx₀ y h.le))⟩
  set c := sInf S with hc
  -- `F c ≥ 1 - α` by right continuity
  have hFc : 1 - α ≤ F c := by
    have hcont : Tendsto F (𝓝[>] c) (𝓝 (F c)) :=
      ((F.right_continuous c).mono Ioi_subset_Ici_self)
    refine ge_of_tendsto hcont (eventually_nhdsWithin_of_forall fun x hx ↦ ?_)
    obtain ⟨y, hyS, hyx⟩ := exists_lt_of_csInf_lt hne hx
    exact hyS.trans (F.mono hyx.le)
  -- `P(T < c) ≤ 1 - α` by left limits
  have hlt : ∀ y < c, F y ≤ 1 - α := fun y hy ↦ by
    by_contra h
    push Not at h
    exact absurd (csInf_le hbdd h.le) (not_le.2 hy)
  have hleft : Function.leftLim F c ≤ 1 - α :=
    le_of_tendsto (F.mono.tendsto_leftLim c) (eventually_nhdsWithin_of_forall fun y hy ↦ hlt y hy)
  have hIio : μ.real {ω | T ω < c} = Function.leftLim F c := by
    have h1 : μ.real {ω | T ω < c} = ν.real (Iio c) := by
      rw [hν, map_measureReal_apply hT measurableSet_Iio]; rfl
    rw [h1, measureReal_def, ← measure_cdf (μ := ν), ← hF, F.measure_Iio (tendsto_cdf_atBot ν),
      sub_zero, ENNReal.toReal_ofReal]
    exact (cdf_nonneg _ _).trans (F.mono.le_leftLim (sub_one_lt c))
  have hA : μ.real {ω | c < T ω} = 1 - F c := by
    have : {ω | c < T ω} = {ω | T ω ≤ c}ᶜ := by ext ω; simp
    rw [this, probReal_compl_eq_one_sub (measurableSet_le hT measurable_const), hFx]
  have hAB : μ.real {ω | c < T ω} + μ.real {ω | T ω = c} = 1 - μ.real {ω | T ω < c} := by
    have hu : {ω | c < T ω} ∪ {ω | T ω = c} = {ω | T ω < c}ᶜ := by
      ext ω; simp only [mem_union, mem_ofPred_eq, mem_compl_iff, not_lt]
      constructor
      · rintro (h | h) <;> [exact h.le; exact h.ge]
      · intro h; rcases h.lt_or_eq with h | h <;> [exact Or.inl h; exact Or.inr h.symm]
    have hd : Disjoint {ω | c < T ω} {ω | T ω = c} :=
      Set.disjoint_left.2 fun ω h1 h2 ↦ by simp only [mem_ofPred_eq] at h1 h2; linarith
    rw [← measureReal_union hd (measurableSet_eq_fun hT measurable_const), hu,
      probReal_compl_eq_one_sub (measurableSet_lt hT measurable_const)]
  set a := μ.real {ω | c < T ω}
  set b := μ.real {ω | T ω = c}
  have ha : a ≤ α := by rw [hA]; linarith
  have hab : α ≤ a + b := by rw [hAB, hIio]; linarith
  have hb : 0 ≤ b := measureReal_nonneg
  rcases hb.eq_or_lt with hb0 | hbpos
  · exact ⟨c, 0, ⟨le_rfl, zero_le_one⟩, by rw [← hb0] at hab; linarith⟩
  · refine ⟨c, (α - a) / b, ⟨div_nonneg (by linarith) hb, (div_le_one hbpos).2 (by linarith)⟩, ?_⟩
    field_simp
    ring


/-- The measure with density `f₀` against `ν`. -/
private theorem integral_mul_eq_integral_withDensity {ν : Measure Ω} {f₀ : Ω → ℝ}
    (h₀ : Measurable f₀) (hf₀0 : 0 ≤ f₀) (g : Ω → ℝ) :
    ∫ ω, g ω * f₀ ω ∂ν =
      ∫ ω, g ω ∂(ν.withDensity fun ω ↦ ((f₀ ω).toNNReal : ℝ≥0∞)) := by
  rw [show (fun ω ↦ ((f₀ ω).toNNReal : ℝ≥0∞)) = fun ω ↦ (((Real.toNNReal ∘ f₀) ω : ℝ≥0) : ℝ≥0∞)
    from rfl, integral_withDensity_eq_integral_smul (measurable_real_toNNReal.comp h₀)]
  refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
  simp only [Function.comp_apply, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hf₀0 ω)]
  ring

private theorem isProbabilityMeasure_withDensity {ν : Measure Ω} {f₀ : Ω → ℝ}
    (hf₀ : Integrable f₀ ν) (hf₀0 : 0 ≤ f₀) (hf₀1 : ∫ ω, f₀ ω ∂ν = 1) :
    IsProbabilityMeasure (ν.withDensity fun ω ↦ ((f₀ ω).toNNReal : ℝ≥0∞)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have := ofReal_integral_eq_lintegral_ofReal hf₀ (ae_of_all _ hf₀0)
  rw [hf₀1, ENNReal.ofReal_one] at this
  exact this.symm

/-- The likelihood ratio test `1{f₁ > k f₀} + γ 1{f₁ = k f₀}`. -/
noncomputable def lrTest (f₀ f₁ : Ω → ℝ) (k γ : ℝ) (ω : Ω) : ℝ :=
  if k * f₀ ω < f₁ ω then 1 else if f₁ ω = k * f₀ ω then γ else 0

theorem isTest_lrTest {f₀ f₁ : Ω → ℝ} (h₀ : Measurable f₀) (h₁ : Measurable f₁) (k : ℝ)
    {γ : ℝ} (hγ : γ ∈ Icc (0 : ℝ) 1) : IsTest (lrTest f₀ f₁ k γ) := by
  refine ⟨Measurable.ite (measurableSet_lt (measurable_const.mul h₀) h₁) measurable_const
    (Measurable.ite (measurableSet_eq_fun h₁ (measurable_const.mul h₀)) measurable_const
      measurable_const), fun ω ↦ ?_⟩
  unfold lrTest
  split_ifs
  exacts [⟨zero_le_one, le_rfl⟩, hγ, ⟨le_rfl, zero_le_one⟩]

omit [MeasurableSpace Ω] in
theorem isLikelihoodRatioTest_lrTest (f₀ f₁ : Ω → ℝ) (k γ : ℝ) :
    IsLikelihoodRatioTest f₀ f₁ k (lrTest f₀ f₁ k γ) := fun ω ↦
  ⟨fun h ↦ ite_eq_left h, fun h ↦ by
    rw [lrTest, ite_eq_right (not_lt.2 h.le), ite_eq_right (ne_of_lt h)]⟩

/-- **A likelihood ratio test of any exact size.** For a probability density `f₀` (`f₀ ≥ 0`,
`∫ f₀ = 1`) and `f₁ ≥ 0`, and every `α ∈ (0, 1]` there are a threshold `k ≥ 0` and a weight `γ ∈
[0, 1]` such
that `1{f₁ > k f₀} + γ 1{f₁ = k f₀}` has size exactly `α`. The weight `γ` (randomization) is what
makes every size reachable when the likelihood ratio has atoms. -/
theorem exists_lrTest_size_eq {ν : Measure Ω} {f₀ f₁ : Ω → ℝ} (h₀ : Measurable f₀)
    (h₁ : Measurable f₁) (hf₀ : Integrable f₀ ν) (hf₀0 : 0 ≤ f₀) (hf₁0 : 0 ≤ f₁)
    (hf₀1 : ∫ ω, f₀ ω ∂ν = 1) {α : ℝ} (hα : α ∈ Ioc (0 : ℝ) 1) :
    ∃ k γ, 0 ≤ k ∧ γ ∈ Icc (0 : ℝ) 1 ∧ ∫ ω, lrTest f₀ f₁ k γ ω * f₀ ω ∂ν = α := by
  rcases hα.2.lt_or_eq with hα1 | rfl
  swap
  · -- size `1`: threshold `0` and weight `1` reject everywhere, since `f₁ ≥ 0`
    refine ⟨0, 1, le_rfl, ⟨zero_le_one, le_rfl⟩, ?_⟩
    have h1 : ∀ ω, lrTest f₀ f₁ 0 1 ω * f₀ ω = f₀ ω := fun ω ↦ by
      have : lrTest f₀ f₁ 0 1 ω = 1 := by
        simp only [lrTest, zero_mul]
        split_ifs with h1 h2
        · rfl
        · rfl
        · exact absurd (le_antisymm (not_lt.1 h1) (hf₁0 ω)) h2
      rw [this, one_mul]
    simp_rw [h1]
    exact hf₀1
  replace hα : α ∈ Ioo (0 : ℝ) 1 := ⟨hα.1, hα1⟩
  set μ₀ := ν.withDensity fun ω ↦ ((f₀ ω).toNNReal : ℝ≥0∞) with hμ₀
  have : IsProbabilityMeasure μ₀ := isProbabilityMeasure_withDensity hf₀ hf₀0 hf₀1
  set T : Ω → ℝ := fun ω ↦ f₁ ω / f₀ ω with hT
  have hTm : Measurable T := h₁.div h₀
  obtain ⟨c, γ, hγ, hsize⟩ := exists_measureReal_lt_add_mul_eq (μ := μ₀) hTm hα
  -- the null set `f₀ = 0`
  have hpos : ∀ᵐ ω ∂μ₀, 0 < f₀ ω := by
    have hz : μ₀ {ω | f₀ ω = 0} = 0 := by
      rw [hμ₀, withDensity_apply _ (measurableSet_eq_fun h₀ measurable_const)]
      rw [setLIntegral_congr_fun (measurableSet_eq_fun h₀ measurable_const)
        (g := fun _ ↦ 0) (fun ω hω ↦ by simp [show f₀ ω = 0 from hω])]
      simp
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hz] with ω hω
    exact lt_of_le_of_ne (hf₀0 ω) (Ne.symm hω)
  -- the threshold is nonnegative, since `T ≥ 0` everywhere
  have hc : 0 ≤ c := by
    by_contra hc
    push Not at hc
    have huniv : {ω | c < T ω} = univ :=
      eq_univ_of_forall fun ω ↦ lt_of_lt_of_le hc (div_nonneg (hf₁0 ω) (hf₀0 ω))
    rw [huniv, probReal_univ] at hsize
    have : 0 ≤ γ * μ₀.real {ω | T ω = c} := mul_nonneg hγ.1 measureReal_nonneg
    linarith [hα.2]
  refine ⟨c, γ, hc, hγ, ?_⟩
  rw [integral_mul_eq_integral_withDensity h₀ hf₀0, ← hμ₀, ← hsize,
    ← integral_thresholdTest hTm]
  refine integral_congr_ae ?_
  filter_upwards [hpos] with ω hω
  simp only [lrTest, thresholdTest, hT]
  simp only [lt_div_iff₀ hω, div_eq_iff hω.ne']

/-- **Neyman–Pearson, existence form.** For a probability density `f₀`, an integrable `f₁ ≥ 0`
and a level
`α ∈ (0, 1]` there is a test of size exactly `α` (a likelihood ratio test) whose power is at least
that of every test of size at most `α`. -/
theorem exists_isMostPowerful {ν : Measure Ω} {f₀ f₁ : Ω → ℝ} (h₀ : Measurable f₀)
    (h₁ : Measurable f₁) (hf₀ : Integrable f₀ ν) (hf₁ : Integrable f₁ ν) (hf₀0 : 0 ≤ f₀)
    (hf₁0 : 0 ≤ f₁) (hf₀1 : ∫ ω, f₀ ω ∂ν = 1) {α : ℝ} (hα : α ∈ Ioc (0 : ℝ) 1) :
    ∃ φ', IsTest φ' ∧ ∫ ω, φ' ω * f₀ ω ∂ν = α ∧ ∀ φ, IsTest φ → ∫ ω, φ ω * f₀ ω ∂ν ≤ α →
      ∫ ω, φ ω * f₁ ω ∂ν ≤ ∫ ω, φ' ω * f₁ ω ∂ν := by
  obtain ⟨k, γ, hk, hγ, hsize⟩ := exists_lrTest_size_eq h₀ h₁ hf₀ hf₀0 hf₁0 hf₀1 hα
  refine ⟨lrTest f₀ f₁ k γ, isTest_lrTest h₀ h₁ k hγ, hsize, fun φ hφ hφα ↦ ?_⟩
  exact power_le_of_likelihoodRatioTest hf₀ hf₁ hk (isTest_lrTest h₀ h₁ k hγ)
    (isLikelihoodRatioTest_lrTest f₀ f₁ k γ) hφ (hsize ▸ hφα)

/-! ### Item 56: Karlin–Rubin -/

/-- A family of densities `f θ` has a **monotone likelihood ratio** in the statistic `S` when, for
`θ < θ'`, `f θ' = g (S ω) · f θ` for some nondecreasing `g ≥ 0`: the ratio `f θ' / f θ` is a
nondecreasing function of `S` alone. Written as a product, so the ratio is never divided out; it
asks that `f θ' = 0` wherever `f θ = 0`, so families whose support grows with `θ` (the uniform law
on `[0, θ]`) are not covered; normal laws in their mean and coin flips in their chance of heads
are. See the module docstring, "The limit of item 56". -/
def HasMonotoneLikelihoodRatio {Θ : Type*} [Preorder Θ] (f : Θ → Ω → ℝ) (S : Ω → ℝ) : Prop :=
  ∀ θ θ', θ < θ' → ∃ g : ℝ → ℝ, Monotone g ∧ (∀ t, 0 ≤ g t) ∧ ∀ ω, f θ' ω = g (S ω) * f θ ω

/-- A test `φ` is **uniformly most powerful at level `α`** for the null `θ ≤ θ₀` against the
alternative `θ > θ₀` when its size is at most `α` at every `θ ≤ θ₀`, and every other such test has
power at most that of `φ` at every `θ > θ₀`. -/
def IsUniformlyMostPowerful {Θ : Type*} [Preorder Θ] (ν : Measure Ω) (f : Θ → Ω → ℝ) (θ₀ : Θ)
    (α : ℝ) (φ : Ω → ℝ) : Prop :=
  IsTest φ ∧ (∀ θ ≤ θ₀, ∫ ω, φ ω * f θ ω ∂ν ≤ α) ∧
    ∀ ψ, IsTest ψ → (∀ θ ≤ θ₀, ∫ ω, ψ ω * f θ ω ∂ν ≤ α) →
      ∀ θ, θ₀ < θ → ∫ ω, ψ ω * f θ ω ∂ν ≤ ∫ ω, φ ω * f θ ω ∂ν

omit [MeasurableSpace Ω] in
/-- Under a monotone likelihood ratio, a threshold test in `S` is a likelihood ratio test for
every pair `θ < θ'`, with threshold `g c ≥ 0`. -/
private theorem isLikelihoodRatioTest_thresholdTest {Θ : Type*} [Preorder Θ]
    {f : Θ → Ω → ℝ} {S : Ω → ℝ} (hf0 : ∀ θ, 0 ≤ f θ) {θ θ' : Θ} {g : ℝ → ℝ}
    (hg : Monotone g) (hfg : ∀ ω, f θ' ω = g (S ω) * f θ ω) (c γ : ℝ) :
    IsLikelihoodRatioTest (f θ) (f θ') (g c) (thresholdTest S c γ) := by
  intro ω
  constructor
  · intro h
    rw [hfg] at h
    have : c < S ω := by
      by_contra hle
      push Not at hle
      exact absurd h (not_lt.2 (mul_le_mul_of_nonneg_right (hg hle) (hf0 θ ω)))
    exact ite_eq_left this
  · intro h
    rw [hfg] at h
    have : S ω < c := by
      by_contra hle
      push Not at hle
      exact absurd h (not_lt.2 (mul_le_mul_of_nonneg_right (hg hle) (hf0 θ ω)))
    rw [thresholdTest, ite_eq_right (not_lt.2 this.le), ite_eq_right (ne_of_lt this)]

/-- **The Karlin–Rubin theorem.** Let `f θ` be probability densities (against `ν`), indexed by a
partial order, with a monotone likelihood ratio in a measurable statistic `S`. A threshold test in
`S`, `1{S > c} + γ 1{S = c}`, is uniformly most powerful at its own size `α` (its size at `θ₀`)
for the one-sided question "is `θ > θ₀`?": its size is at most `α` at every `θ ≤ θ₀` (its power
does not decrease in `θ`), and no test of level `α` has more power at any `θ > θ₀`. -/
theorem isUniformlyMostPowerful_of_monotoneLikelihoodRatio {Θ : Type*} [PartialOrder Θ]
    {ν : Measure Ω} {f : Θ → Ω → ℝ} {S : Ω → ℝ} (hS : Measurable S)
    (hf : ∀ θ, Integrable (f θ) ν) (hf0 : ∀ θ, 0 ≤ f θ) (hf1 : ∀ θ, ∫ ω, f θ ω ∂ν = 1)
    (hmlr : HasMonotoneLikelihoodRatio f S) (θ₀ : Θ) (c : ℝ) {γ : ℝ}
    (hγ : γ ∈ Icc (0 : ℝ) 1) :
    IsUniformlyMostPowerful ν f θ₀ (∫ ω, thresholdTest S c γ ω * f θ₀ ω ∂ν)
      (thresholdTest S c γ) := by
  have hφ := isTest_thresholdTest hS c hγ
  refine ⟨hφ, fun θ hθ ↦ ?_, fun ψ hψ hψα θ hθ ↦ ?_⟩
  · rcases hθ.lt_or_eq with hlt | rfl
    · obtain ⟨g, hg, hg0, hfg⟩ := hmlr θ θ₀ hlt
      set β := ∫ ω, thresholdTest S c γ ω * f θ ω ∂ν
      have hβ0 : 0 ≤ β := integral_nonneg fun ω ↦ mul_nonneg (hφ.2 ω).1 (hf0 θ ω)
      have hβ1 : β ≤ 1 := by
        rw [← hf1 θ]
        exact integral_mono (hφ.integrable_mul (hf θ)) (hf θ) fun ω ↦
          mul_le_of_le_one_left (hf0 θ ω) (hφ.2 ω).2
      have hconst : IsTest fun _ : Ω ↦ β := ⟨measurable_const, fun _ ↦ ⟨hβ0, hβ1⟩⟩
      have key := power_le_of_likelihoodRatioTest (hf θ) (hf θ₀) (hg0 c) hφ
        (isLikelihoodRatioTest_thresholdTest hf0 hg hfg c γ) hconst
        (by rw [integral_const_mul, hf1, mul_one])
      rwa [integral_const_mul, hf1, mul_one] at key
    · exact le_rfl
  · obtain ⟨g, hg, hg0, hfg⟩ := hmlr θ₀ θ hθ
    exact power_le_of_likelihoodRatioTest (hf θ₀) (hf θ) (hg0 c) hφ
      (isLikelihoodRatioTest_thresholdTest hf0 hg hfg c γ) hψ (hψα θ₀ le_rfl)

/-- **A threshold test of any exact size.** For a probability density `f₀` (`f₀ ≥ 0`,
`∫ f₀ = 1`, for example `f θ₀`), a measurable statistic `S` and `α ∈ (0, 1)`, there are `c` and
`γ ∈ [0, 1]` such that `1{S > c} + γ 1{S = c}` has size exactly `α` under `f₀`. -/
theorem exists_thresholdTest_size_eq {ν : Measure Ω} {f₀ : Ω → ℝ} {S : Ω → ℝ}
    (hS : Measurable S) (h₀ : Measurable f₀) (hf₀ : Integrable f₀ ν) (hf₀0 : 0 ≤ f₀)
    (hf₀1 : ∫ ω, f₀ ω ∂ν = 1) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    ∃ c γ, γ ∈ Icc (0 : ℝ) 1 ∧ ∫ ω, thresholdTest S c γ ω * f₀ ω ∂ν = α := by
  have := isProbabilityMeasure_withDensity hf₀ hf₀0 hf₀1
  obtain ⟨c, γ, hγ, hsize⟩ := exists_measureReal_lt_add_mul_eq
    (μ := ν.withDensity fun ω ↦ ((f₀ ω).toNNReal : ℝ≥0∞)) hS hα
  exact ⟨c, γ, hγ, by
    rw [integral_mul_eq_integral_withDensity h₀ hf₀0, integral_thresholdTest hS, hsize]⟩

end ClassicalLean.Statistics

open MeasureTheory in
/-- The hypotheses of `power_le_of_likelihoodRatioTest` hold together: on two points with the
counting measure, the null density `f₀ = (3/2, 1/2)` and the alternative `f₁ = (1/2, 3/2)`, both
integrable; the threshold `k = 1 ≥ 0`; the likelihood ratio test `φ' = (0, 1)`, which rejects
exactly where `f₁ > f₀`; and the test `φ = 1/4` everywhere, of size `1/2`, the same as `φ'`'s. -/
example := ClassicalLean.Statistics.power_le_of_likelihoodRatioTest (Ω := Fin 2)
  (ν := Measure.count) (f₀ := ![3 / 2, 1 / 2]) (f₁ := ![1 / 2, 3 / 2])
  Integrable.of_finite Integrable.of_finite (k := 1) (by norm_num)
  (φ' := ![0, 1]) ⟨measurable_of_finite _, fun ω ↦ by fin_cases ω <;> simp⟩
  (fun ω ↦ by fin_cases ω <;> norm_num)
  (φ := fun _ ↦ 1 / 4) ⟨measurable_const, fun _ ↦ by norm_num⟩
  (by simp [integral_fintype, Measure.real, Fin.sum_univ_two]; norm_num)

open MeasureTheory Set in
/-- The hypotheses of `isUniformlyMostPowerful_of_monotoneLikelihoodRatio` hold together: two
parameters `0 < 1`; on two points with the counting measure, the densities `f 0 = (3/4, 1/4)` and
`f 1 = (1/4, 3/4)`, integrable, nonnegative and summing to `1`; the statistic `S ω = ω`,
measurable, in which the ratio `f 1 / f 0` is `1/3` at `S = 0` and `3` at `S = 1`, nondecreasing;
the null boundary `θ₀ = 0`; the cut `c = 1`, a value of `S` (at the second point), so that the tie
chance `γ = 1/2 ∈ [0, 1]` is used there. -/
example := ClassicalLean.Statistics.isUniformlyMostPowerful_of_monotoneLikelihoodRatio
  (Ω := Fin 2) (Θ := Fin 2) (ν := Measure.count) (f := ![![3 / 4, 1 / 4], ![1 / 4, 3 / 4]])
  (S := fun ω ↦ (ω : ℝ)) (measurable_of_finite _) (fun _ ↦ Integrable.of_finite)
  (fun θ ω ↦ by fin_cases θ <;> fin_cases ω <;> norm_num)
  (fun θ ↦ by fin_cases θ <;> simp [integral_fintype, Measure.real, Fin.sum_univ_two] <;> norm_num)
  (fun θ θ' h ↦ by
    fin_cases θ <;> fin_cases θ'
    all_goals first
      | exact absurd h (by decide)
      | refine ⟨fun t ↦ if t ≤ 0 then 1 / 3 else 3, fun a b hab ↦ ?_, fun t ↦ ?_,
          fun ω ↦ by fin_cases ω <;> norm_num⟩
        · dsimp only
          split_ifs <;> linarith
        · dsimp only
          split_ifs <;> norm_num)
  (θ₀ := 0) (c := 1) (γ := 1 / 2) ⟨by norm_num, by norm_num⟩
