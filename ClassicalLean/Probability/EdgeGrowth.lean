/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Probability.NoEdgeWealth
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Moments.SubGaussian

/-!
# With a real edge, a fixed stake reaches any level

Returns `X 0, X 1, …` are independent, have the same distribution, and are bounded,
`-c ≤ X n ≤ C` with `0 < c`. The versions without a ceiling, `exists_growth_pos_of_floor`,
`tendsto_wealth_atTop_of_floor` and `exists_stake_measureReal_reach_eq_one_of_floor`, need only the
floor `-c ≤ X n`; `tendsto_log_wealth_div_of_floor` replaces the ceiling by integrability of
`log (1 + l · X 0)`. A constant stake `l` turns them into the wealth
`wealth (fun _ _ ↦ l) X n = ∏ i < n, (1 + l · X (i + 1))` of `NoEdgeWealth`. Its long-run growth
rate per return is `growth μ (X 0) l = ∫ log (1 + l · X 0)`.

* `exists_growth_pos`: if the mean of `X 0` is positive, some stake `l` with `0 < l < 1/c` has
  positive growth.
* `tendsto_log_wealth_div`: for a constant stake `0 ≤ l < 1/c`, `log (wealth) / n` tends to the
  growth almost surely (the strong law of large numbers).
* `tendsto_wealth_atTop`: if that growth is positive, the wealth tends to infinity almost surely.
* `exists_stake_measureReal_reach_eq_one`: so, with a positive mean, some stake `l` in `(0, 1/c)`
  makes the wealth reach `1/α` at some time with probability `1`, for every `α > 0`.
* `measureReal_wealth_lt_le`: how many returns are enough. After `N` returns, the chance that the
  wealth is still below `exp L` is at most `exp (-2 (N · growth - L)² / (N B²))`, where
  `B = log (1 + l C) - log (1 - l c)` (Hoeffding's inequality).
* `exists_growth_pos_of_floor`, `tendsto_log_wealth_div_of_floor`, `tendsto_wealth_atTop_of_floor`
  and `exists_stake_measureReal_reach_eq_one_of_floor`: the first four without the ceiling `C`;
  they generalise them.

This is the other half of `NoEdgeWealth`: there, with no edge, the wealth reaches `1/α` with chance
at most `α`; here, with an edge, a suitable fixed stake reaches it for sure, eventually. The stake
is chosen knowing the true mean. `measureReal_wealth_lt_le` counts the returns: for a target of
at least `1`, the bound on the chance of still being below it after `N` returns falls exponentially
in `N` once `N · growth` passes the log of the target.

Each hypothesis is needed. Returns all equal to the first (`X n = X 0`), `-1/2` or `1` with chance
`1/2` each, are not independent; the wealth never grows once the first return is `-1/2`, so the
chance of ever reaching `2` is at most `1/2`. A return of `0` every time has mean `0` and the
wealth stays `1`. Returns `X n = 2^-n` on one point have different distributions; `X 0 = 1` has
positive mean, but the wealth stays below `e < 3`. With `c = 0`, Lean's `1/0 = 0` leaves no stake
in `(0, 1/c)`.
A stake of `1/c` itself, or a negative stake, can make the wealth `0`, while Lean's convention
`log 0 = 0` still reports a positive growth; and without the ceiling `C`, or the integrability
`tendsto_log_wealth_div_of_floor` asks instead, the growth can be infinite while Lean's integral of
a non-integrable function is `0`. Among the four long-run results this matters for the rate
(`tendsto_log_wealth_div`) only.
-/

open MeasureTheory ProbabilityTheory Filter Finset Topology Function
open ClassicalLean.Probability.NoEdgeWealth

namespace ClassicalLean.Probability.EdgeGrowth

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- The growth rate of a constant stake `l` on a return `Y`: the mean of `log (1 + l · Y)`. -/
noncomputable def growth (μ : Measure Ω) (Y : Ω → ℝ) (l : ℝ) : ℝ :=
  ∫ ω, Real.log (1 + l * Y ω) ∂μ

/-- Near `0`, `log (1 + y)` is at least `y - 2 y²`. -/
lemma sub_two_mul_sq_le_log {y : ℝ} (hy : -(1 / 2) ≤ y) : y - 2 * y ^ 2 ≤ Real.log (1 + y) := by
  have ht : 0 < 1 + y := by linarith
  have hinv : (1 + y)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ ht (by norm_num)]; linarith
  have key : 1 - (1 + y)⁻¹ - (y - 2 * y ^ 2) = y ^ 2 * (2 - (1 + y)⁻¹) := by
    field_simp; ring
  have h1 := Real.one_sub_inv_le_log_of_pos ht
  nlinarith [sq_nonneg y, mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hinv)]

/-- A stake below `1/c` on a return of at least `-c` keeps each factor at least `1 - l c > 0`. -/
lemma one_sub_mul_le_one_add_mul {c l x : ℝ} (hx : -c ≤ x) (hl0 : 0 ≤ l) :
    1 - l * c ≤ 1 + l * x := by nlinarith

lemma one_sub_mul_pos {c l : ℝ} (hc : 0 < c) (hl1 : l < 1 / c) : 0 < 1 - l * c := by
  have := (lt_div_iff₀ hc).mp hl1; linarith

/-- `|log t| ≤ t + 1/t` for `t > 0`. -/
lemma abs_log_le_add_inv {t : ℝ} (ht : 0 < t) : |Real.log t| ≤ t + t⁻¹ := by
  have h1 := Real.log_le_sub_one_of_pos ht
  have h2 := Real.one_sub_inv_le_log_of_pos ht
  have h3 : 0 < t⁻¹ := inv_pos.mpr ht
  rw [abs_le]; constructor <;> linarith

/-- The log factor of a constant stake below `1/c` on a bounded return is bounded. -/
lemma abs_log_one_add_mul_le {c C l x : ℝ} (hc : 0 < c) (hx0 : -c ≤ x) (hx1 : x ≤ C)
    (hl0 : 0 ≤ l) (hl1 : l < 1 / c) :
    |Real.log (1 + l * x)| ≤ (1 + l * |C|) + (1 - l * c)⁻¹ := by
  have hpos := one_sub_mul_pos hc hl1
  have hlow := one_sub_mul_le_one_add_mul hx0 hl0
  have ht : 0 < 1 + l * x := by linarith
  refine (abs_log_le_add_inv ht).trans (add_le_add ?_ ?_)
  · nlinarith [le_abs_self C, mul_le_mul_of_nonneg_left (hx1.trans (le_abs_self C)) hl0]
  · exact inv_anti₀ hpos hlow

lemma integrable_of_bounds [IsFiniteMeasure μ] {Y : Ω → ℝ} {c C : ℝ} (hY : Measurable Y)
    (hlo : ∀ ω, -c ≤ Y ω) (hhi : ∀ ω, Y ω ≤ C) : Integrable Y μ :=
  Integrable.of_bound hY.aestronglyMeasurable (|c| + |C|) (Eventually.of_forall fun ω ↦ by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [abs_nonneg C, le_abs_self c, hlo ω],
      by linarith [le_abs_self C, abs_nonneg c, hhi ω]⟩)

lemma integrable_log_one_add_mul [IsFiniteMeasure μ] {Y : Ω → ℝ} {c C l : ℝ} (hY : Measurable Y)
    (hc : 0 < c) (hlo : ∀ ω, -c ≤ Y ω) (hhi : ∀ ω, Y ω ≤ C) (hl0 : 0 ≤ l) (hl1 : l < 1 / c) :
    Integrable (fun ω ↦ Real.log (1 + l * Y ω)) μ :=
  Integrable.of_bound ((measurable_const.add (measurable_const.mul hY)).log).aestronglyMeasurable
    ((1 + l * |C|) + (1 - l * c)⁻¹)
    (Eventually.of_forall fun ω ↦ by
      rw [Real.norm_eq_abs]; exact abs_log_one_add_mul_le hc (hlo ω) (hhi ω) hl0 hl1)

/-- **With a positive mean, some stake has positive growth.** A measurable return `Y` with
`-c ≤ Y ≤ C`, `0 < c` and a positive mean has a stake `l` with `0 < l < 1/c` and
`0 < growth μ Y l`. -/
theorem exists_growth_pos [IsProbabilityMeasure μ] {Y : Ω → ℝ} {c C : ℝ} (hY : Measurable Y)
    (hc : 0 < c) (hlo : ∀ ω, -c ≤ Y ω) (hhi : ∀ ω, Y ω ≤ C) (hm : 0 < ∫ ω, Y ω ∂μ) :
    ∃ l, 0 < l ∧ l < 1 / c ∧ 0 < growth μ Y l := by
  set m := ∫ ω, Y ω ∂μ
  set M := max c C with hM
  have hMpos : 0 < M := lt_of_lt_of_le hc (le_max_left _ _)
  set l := min (1 / (2 * M)) (m / (4 * M ^ 2)) with hl
  have hlpos : 0 < l := lt_min (by positivity) (by positivity)
  have hl2M : l ≤ 1 / (2 * M) := min_le_left _ _
  have hlm : l ≤ m / (4 * M ^ 2) := min_le_right _ _
  have hlM : l * M ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_right hl2M hMpos.le
    rwa [show 1 / (2 * M) * M = 1 / 2 by field_simp] at this
  have hlc : l < 1 / c := by
    rw [lt_div_iff₀ hc]
    have : l * c ≤ l * M := mul_le_mul_of_nonneg_left (le_max_left _ _) hlpos.le
    linarith
  refine ⟨l, hlpos, hlc, ?_⟩
  -- pointwise: `|l Y| ≤ 1/2`, so `log (1 + l Y) ≥ l Y - 2 l² M²`
  have hpt : ∀ ω, l * Y ω - 2 * l ^ 2 * M ^ 2 ≤ Real.log (1 + l * Y ω) := fun ω ↦ by
    have habs : |Y ω| ≤ M := abs_le.mpr ⟨by linarith [hlo ω, le_max_left c C],
      (hhi ω).trans (le_max_right _ _)⟩
    have hyM : |l * Y ω| ≤ l * M := by
      rw [abs_mul, abs_of_pos hlpos]; exact mul_le_mul_of_nonneg_left habs hlpos.le
    have hy : |l * Y ω| ≤ 1 / 2 := hyM.trans hlM
    have hsq : (l * Y ω) ^ 2 ≤ l ^ 2 * M ^ 2 := by
      rw [← sq_abs, ← mul_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hyM 2
    have := sub_two_mul_sq_le_log (y := l * Y ω) (by linarith [(abs_le.mp hy).1])
    linarith
  have hYint := integrable_of_bounds (μ := μ) hY hlo hhi
  have hlow : l * m - 2 * l ^ 2 * M ^ 2 ≤ growth μ Y l := by
    have h := integral_mono (f := fun ω ↦ l * Y ω - 2 * l ^ 2 * M ^ 2)
      ((hYint.const_mul l).sub (integrable_const (2 * l ^ 2 * M ^ 2)))
      (integrable_log_one_add_mul hY hc hlo hhi hlpos.le hlc) hpt
    rw [integral_sub (hYint.const_mul l) (integrable_const _), integral_const_mul,
      integral_const, probReal_univ, one_smul] at h
    exact h
  have h2 : 2 * l ^ 2 * M ^ 2 ≤ l * m / 2 := by
    have := mul_le_mul_of_nonneg_left hlm (by positivity : (0 : ℝ) ≤ 2 * l * M ^ 2)
    rw [show 2 * l * M ^ 2 * (m / (4 * M ^ 2)) = l * m / 2 by field_simp; ring] at this
    nlinarith
  have : 0 < l * m := mul_pos hlpos hm
  linarith

/-! ### The strong law for the log of the wealth -/

section iid

variable [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {c C l : ℝ}

lemma wealth_const_pos (hc : 0 < c) (hlo : ∀ n ω, -c ≤ X n ω) (hl0 : 0 ≤ l) (hl1 : l < 1 / c)
    (n : ℕ) (ω : Ω) : 0 < wealth (fun _ _ ↦ l) X n ω :=
  prod_pos fun _ _ ↦ (one_sub_mul_pos hc hl1).trans_le (one_sub_mul_le_one_add_mul (hlo _ ω) hl0)

/-- **The growth rate is the long-run rate of the log of the wealth.** Returns `X n` measurable,
independent, with the distribution of `X 0`, and `-c ≤ X n ≤ C` with `0 < c`; a constant stake
`0 ≤ l < 1/c`. Then `log (wealth) / n` tends to `growth μ (X 0) l` almost surely. -/
theorem tendsto_log_wealth_div (hXm : ∀ n, Measurable (X n)) (hind : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ) (hc : 0 < c) (hlo : ∀ n ω, -c ≤ X n ω)
    (hhi : ∀ n ω, X n ω ≤ C) (hl0 : 0 ≤ l) (hl1 : l < 1 / c) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ Real.log (wealth (fun _ _ ↦ l) X n ω) / n) atTop
      (𝓝 (growth μ (X 0) l)) := by
  set f : ℝ → ℝ := fun x ↦ Real.log (1 + l * x) with hf
  have hfm : Measurable f := by fun_prop
  set Z : ℕ → Ω → ℝ := fun i ↦ f ∘ X (i + 1) with hZ
  have hint : Integrable (Z 0) μ :=
    integrable_log_one_add_mul (hXm 1) hc (hlo 1) (hhi 1) hl0 hl1
  have hpair : Pairwise ((· ⟂ᵢ[μ] ·) on Z) := fun i j hij ↦
    (hind.indepFun (by omega : i + 1 ≠ j + 1)).comp hfm hfm
  have hident : ∀ i, IdentDistrib (Z i) (Z 0) μ μ := fun i ↦
    ((hid (i + 1)).trans (hid 1).symm).comp hfm
  have hlim : μ[Z 0] = growth μ (X 0) l := ((hid 1).comp hfm).integral_eq
  filter_upwards [strong_law_ae_real Z hint hpair hident] with ω hω
  rw [hlim] at hω
  refine hω.congr fun n ↦ ?_
  congr 1
  rw [wealth, Real.log_prod fun _ _ ↦
    ne_of_gt ((one_sub_mul_pos hc hl1).trans_le (one_sub_mul_le_one_add_mul (hlo _ ω) hl0))]
  rfl

/-- **With positive growth, the wealth tends to infinity.** Under the hypotheses of
`tendsto_log_wealth_div`, if `growth μ (X 0) l > 0` the wealth tends to infinity almost surely. -/
theorem tendsto_wealth_atTop (hXm : ∀ n, Measurable (X n)) (hind : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ) (hc : 0 < c) (hlo : ∀ n ω, -c ≤ X n ω)
    (hhi : ∀ n ω, X n ω ≤ C) (hl0 : 0 ≤ l) (hl1 : l < 1 / c) (hg : 0 < growth μ (X 0) l) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ wealth (fun _ _ ↦ l) X n ω) atTop atTop := by
  filter_upwards [tendsto_log_wealth_div hXm hind hid hc hlo hhi hl0 hl1] with ω hω
  set g := growth μ (X 0) l
  have hev : ∀ᶠ n : ℕ in atTop, g / 2 < Real.log (wealth (fun _ _ ↦ l) X n ω) / n :=
    hω.eventually (lt_mem_nhds (by linarith))
  have hexp : Tendsto (fun n : ℕ ↦ Real.exp ((n : ℝ) * (g / 2))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const (by linarith))
  refine tendsto_atTop_mono' atTop ?_ hexp
  filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hW := wealth_const_pos hc hlo hl0 hl1 n ω
  rw [← Real.exp_log hW]
  refine Real.exp_le_exp.mpr ?_
  rw [lt_div_iff₀ hnpos] at hn
  linarith

/-- **With a positive mean, some fixed stake reaches any level for sure, eventually.** Returns
`X n` measurable, independent, with the distribution of `X 0`, `-c ≤ X n ≤ C` with `0 < c`, and
`0 < ∫ X 0`. Then some stake `l` with `0 < l < 1/c` makes the wealth reach `1/α` at some time with
probability `1`, for every `α > 0`. The stake depends on the distribution of `X 0`. -/
theorem exists_stake_measureReal_reach_eq_one (hXm : ∀ n, Measurable (X n))
    (hind : iIndepFun X μ) (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ) (hc : 0 < c)
    (hlo : ∀ n ω, -c ≤ X n ω) (hhi : ∀ n ω, X n ω ≤ C) (hm : 0 < ∫ ω, X 0 ω ∂μ) :
    ∃ l, 0 < l ∧ l < 1 / c ∧
      ∀ α : ℝ, 0 < α → μ.real {ω | ∃ n, 1 / α ≤ wealth (fun _ _ ↦ l) X n ω} = 1 := by
  obtain ⟨l, hl0, hl1, hg⟩ := exists_growth_pos (μ := μ) (hXm 0) hc (hlo 0) (hhi 0) hm
  refine ⟨l, hl0, hl1, fun α _ ↦ ?_⟩
  have hae : ∀ᵐ ω ∂μ, ω ∈ {ω | ∃ n, 1 / α ≤ wealth (fun _ _ ↦ l) X n ω} := by
    filter_upwards [tendsto_wealth_atTop hXm hind hid hc hlo hhi hl0.le hl1 hg] with ω hω
    exact (hω.eventually_ge_atTop (1 / α)).exists
  rw [measureReal_congr (ae_eq_univ.mpr (ae_iff.mp hae)), probReal_univ]

/-! ### How many returns are enough -/

/-- **How many returns are enough (Hoeffding).** Returns `X n` measurable, independent, with the
distribution of `X 0`, and `-c ≤ X n ≤ C` with `0 < c`; a constant stake `0 ≤ l < 1/c`. For every
number of returns `N` and every `L` with `L ≤ N · growth`, the chance that the wealth after `N`
returns is still below `exp L` is at most
`exp (-2 (N · growth - L)² / (N (log (1 + l C) - log (1 - l c))²))`. For `L ≥ 0` the bound
shrinks as `N` grows once `N · growth` passes `L`. Since reaching the target by time `N` is implied
by being at or above it at time `N`, the same number bounds the chance of not yet having reached it
(not proved separately here). When `N = 0` or `log (1 + l C) = log (1 - l c)`, Lean's `x / 0 = 0`
makes the bound `1`. -/
theorem measureReal_wealth_lt_le (hXm : ∀ n, Measurable (X n)) (hind : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ) (hc : 0 < c) (hlo : ∀ n ω, -c ≤ X n ω)
    (hhi : ∀ n ω, X n ω ≤ C) (hl0 : 0 ≤ l) (hl1 : l < 1 / c) {N : ℕ} {L : ℝ}
    (hL : L ≤ N * growth μ (X 0) l) :
    μ.real {ω | wealth (fun _ _ ↦ l) X N ω < Real.exp L} ≤
      Real.exp (-2 * (N * growth μ (X 0) l - L) ^ 2 /
        (N * (Real.log (1 + l * C) - Real.log (1 - l * c)) ^ 2)) := by
  set g := growth μ (X 0) l with hg
  set a := Real.log (1 - l * c) with ha
  set b := Real.log (1 + l * C) with hb
  set f : ℝ → ℝ := fun x ↦ Real.log (1 + l * x) with hf
  have hfm : Measurable f := by fun_prop
  have hpos := one_sub_mul_pos hc hl1
  -- each log factor lies in `[a, b]`
  have hab : ∀ i ω, f (X i ω) ∈ Set.Icc a b := fun i ω ↦ by
    have h1 := one_sub_mul_le_one_add_mul (hlo i ω) hl0
    refine ⟨Real.log_le_log hpos h1, Real.log_le_log (hpos.trans_le h1) ?_⟩
    nlinarith [hhi i ω]
  -- the centred, negated factors
  set V : ℕ → Ω → ℝ := fun i ω ↦ g - f (X (i + 1) ω) with hV
  have hmean : ∀ i, μ[fun ω ↦ -f (X (i + 1) ω)] = -g := fun i ↦ by
    rw [integral_neg]
    congr 1
    exact ((hid (i + 1)).comp hfm).integral_eq
  have hsub : ∀ i, HasSubgaussianMGF (V i) ((‖-a - -b‖₊ / 2) ^ 2) μ := fun i ↦ by
    have h := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := fun ω ↦ -f (X (i + 1) ω))
      (a := -b) (b := -a) (hfm.comp (hXm (i + 1))).neg.aemeasurable
      (ae_of_all _ fun ω ↦ ⟨neg_le_neg (hab _ ω).2, neg_le_neg (hab _ ω).1⟩)
    rw [hmean i] at h
    convert h using 2 with ω
    simp only [hV]; ring
  have hindV : iIndepFun V μ := by
    have h1 : iIndepFun (fun i ↦ (fun x ↦ g - f x) ∘ X i) μ :=
      hind.comp (fun _ x ↦ g - f x) fun _ ↦ measurable_const.sub hfm
    exact h1.precomp (g := fun i ↦ i + 1) (add_left_injective 1)
  -- the event lies inside the Hoeffding event
  set ε := N * g - L with hε
  have hε0 : 0 ≤ ε := by rw [hε]; linarith
  have hsubset : {ω | wealth (fun _ _ ↦ l) X N ω < Real.exp L} ⊆
      {ω | ε ≤ ∑ i ∈ range N, V i ω} := fun ω hω ↦ by
    have hW := wealth_const_pos hc hlo hl0 hl1 N ω
    have hlog : Real.log (wealth (fun _ _ ↦ l) X N ω) < L := by
      rw [← Real.log_exp L]; exact Real.log_lt_log hW hω
    have hsum : Real.log (wealth (fun _ _ ↦ l) X N ω) = ∑ i ∈ range N, f (X (i + 1) ω) := by
      rw [wealth, Real.log_prod fun _ _ ↦
        ne_of_gt (hpos.trans_le (one_sub_mul_le_one_add_mul (hlo _ ω) hl0))]
    have hV' : ∑ i ∈ range N, V i ω = N * g - ∑ i ∈ range N, f (X (i + 1) ω) := by
      simp [hV, sum_sub_distrib]
    change ε ≤ ∑ i ∈ range N, V i ω
    rw [hV', hε]; linarith
  refine (measureReal_mono hsubset).trans ?_
  refine (HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hindV (fun i _ ↦ hsub i)
    hε0).trans_eq ?_
  congr 1
  have hnorm : (((‖-a - -b‖₊ / 2) ^ 2 : NNReal) : ℝ) = (b - a) ^ 2 / 4 := by
    rw [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs,
      show -a - -b = b - a by ring]
    simp only [NNReal.coe_ofNat, div_pow, sq_abs]; norm_num
  rw [hnorm, show (2 : ℝ) * N * ((b - a) ^ 2 / 4) = N * (b - a) ^ 2 / 2 by ring,
    div_div_eq_mul_div]
  ring

end iid

/-! ### Without the ceiling -/

/-- For `-1 < t`, `log (1 + t)` lies between `t / (1 + t)` and `t`. -/
lemma div_one_add_le_log_le {t : ℝ} (ht : -1 < t) :
    t / (1 + t) ≤ Real.log (1 + t) ∧ Real.log (1 + t) ≤ t := by
  have hpos : 0 < 1 + t := by linarith
  refine ⟨?_, by linarith [Real.log_le_sub_one_of_pos hpos]⟩
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have : 1 - (1 + t)⁻¹ = t / (1 + t) := by field_simp; ring
  linarith

/-- **With a positive mean, some stake has positive growth, with no ceiling.** A measurable return
`Y` with `-c ≤ Y`, `0 < c` and a positive mean has a stake `l` with `0 < l < 1/c` and
`0 < growth μ Y l`. It generalises `exists_growth_pos`, which also asks `Y ≤ C` and a probability
measure; no probability measure is assumed here. A positive mean already makes `Y` integrable in
Lean, since the integral of a non-integrable function is `0`. -/
theorem exists_growth_pos_of_floor {Y : Ω → ℝ} {c : ℝ}
    (hY : Measurable Y) (hc : 0 < c) (hlo : ∀ ω, -c ≤ Y ω) (hm : 0 < ∫ ω, Y ω ∂μ) :
    ∃ l, 0 < l ∧ l < 1 / c ∧ 0 < growth μ Y l := by
  have hYint : Integrable Y μ := by
    by_contra h; rw [integral_undef h] at hm; exact lt_irrefl _ hm
  set s : ℕ → ℝ := fun k ↦ 1 / (2 * c * (k + 1)) with hs
  have hspos : ∀ k, 0 < s k := fun k ↦ by positivity
  have hsc : ∀ k, s k * c ≤ 1 / 2 := fun k ↦ by
    simp only [hs]
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ k + 1 := by have := k.cast_nonneg (α := ℝ); linarith
    nlinarith
  have hlow : ∀ k ω, -(1 / 2) ≤ s k * Y ω := fun k ω ↦ by
    have := mul_le_mul_of_nonneg_left (hlo ω) (hspos k).le
    nlinarith [hsc k]
  set f : ℕ → Ω → ℝ := fun k ω ↦ Real.log (1 + s k * Y ω) / s k with hf
  -- `Y / (1 + s Y) ≤ f ≤ Y`
  have hbounds : ∀ k ω, Y ω / (1 + s k * Y ω) ≤ f k ω ∧ f k ω ≤ Y ω := fun k ω ↦ by
    obtain ⟨h1, h2⟩ := div_one_add_le_log_le (by linarith [hlow k ω] : -1 < s k * Y ω)
    have hsk := hspos k
    constructor
    · rw [hf, le_div_iff₀ hsk]
      calc Y ω / (1 + s k * Y ω) * s k = s k * Y ω / (1 + s k * Y ω) := by ring
        _ ≤ _ := h1
    · rw [hf, div_le_iff₀ hsk]; linarith
  have hden : ∀ k ω, 1 / 2 ≤ 1 + s k * Y ω := fun k ω ↦ by linarith [hlow k ω]
  -- pointwise limit
  have hs0 : Tendsto s atTop (𝓝 0) := by
    have h : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h2 := (h.const_mul_atTop (by positivity : (0 : ℝ) < 2 * c)).inv_tendsto_atTop
    refine h2.congr fun k ↦ ?_
    simp only [hs, one_div, mul_assoc, Pi.inv_apply]
  have hlim : ∀ ω, Tendsto (fun k ↦ f k ω) atTop (𝓝 (Y ω)) := fun ω ↦ by
    have hl : Tendsto (fun k ↦ Y ω / (1 + s k * Y ω)) atTop (𝓝 (Y ω)) := by
      have : Tendsto (fun k ↦ 1 + s k * Y ω) atTop (𝓝 (1 + 0 * Y ω)) :=
        tendsto_const_nhds.add (hs0.mul_const _)
      have h3 := (tendsto_const_nhds (x := Y ω)).div this (by norm_num)
      simp only [zero_mul, add_zero, div_one] at h3
      exact h3
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
      (fun k ↦ (hbounds k ω).1) (fun k ↦ (hbounds k ω).2)
  -- domination by `2 |Y|`
  have hdom : ∀ k ω, ‖f k ω‖ ≤ 2 * |Y ω| := fun k ω ↦ by
    obtain ⟨h1, h2⟩ := hbounds k ω
    have hd := hden k ω
    rw [Real.norm_eq_abs, abs_le]
    rcases le_or_gt 0 (Y ω) with hY0 | hY0
    · have : 0 ≤ Y ω / (1 + s k * Y ω) := div_nonneg hY0 (by linarith)
      rw [abs_of_nonneg hY0]; constructor <;> linarith
    · have hq : 2 * Y ω ≤ Y ω / (1 + s k * Y ω) := by
        rw [le_div_iff₀ (by linarith)]; nlinarith
      rw [abs_of_neg hY0]; constructor <;> linarith
  have hfm : ∀ k, AEStronglyMeasurable (f k) μ := fun k ↦
    (((measurable_const.add (measurable_const.mul hY)).log).div_const _).aestronglyMeasurable
  have hconv := tendsto_integral_of_dominated_convergence (fun ω ↦ 2 * |Y ω|) hfm
    (hYint.abs.const_mul 2) (fun k ↦ ae_of_all _ (hdom k)) (ae_of_all _ hlim)
  obtain ⟨k, hk⟩ := (hconv.eventually (lt_mem_nhds hm)).exists
  refine ⟨s k, hspos k, ?_, ?_⟩
  · rw [lt_div_iff₀ hc]; linarith [hsc k]
  · have : growth μ Y (s k) = s k * ∫ ω, f k ω ∂μ := by
      rw [hf, integral_div, growth]; field_simp [(hspos k).ne']
    rw [this]; exact mul_pos (hspos k) hk

section floor

variable {X : ℕ → Ω → ℝ} {c l : ℝ}

/-- **The long-run rate of the log of the wealth, with no ceiling.** Returns `X n` independent,
with the distribution of `X 0`, and `-c ≤ X n` with `0 < c`; a constant stake `0 ≤ l < 1/c`; and
`log (1 + l · X 0)` integrable. Then `log (wealth) / n` tends to `growth μ (X 0) l` almost surely.
It generalises `tendsto_log_wealth_div`, which asks `X n ≤ C` instead of the integrability. The
strong law used holds for any measure, so no probability measure is assumed; measurability of the
returns is not used. -/
theorem tendsto_log_wealth_div_of_floor (_hXm : ∀ n, Measurable (X n)) (hind : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ) (hc : 0 < c) (hlo : ∀ n ω, -c ≤ X n ω)
    (hl0 : 0 ≤ l) (hl1 : l < 1 / c)
    (hint : Integrable (fun ω ↦ Real.log (1 + l * X 0 ω)) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ Real.log (wealth (fun _ _ ↦ l) X n ω) / n) atTop
      (𝓝 (growth μ (X 0) l)) := by
  set f : ℝ → ℝ := fun x ↦ Real.log (1 + l * x) with hf
  have hfm : Measurable f := by fun_prop
  set Z : ℕ → Ω → ℝ := fun i ↦ f ∘ X (i + 1) with hZ
  have hint1 : Integrable (Z 0) μ := ((hid 1).comp hfm).integrable_iff.mpr hint
  have hpair : Pairwise ((· ⟂ᵢ[μ] ·) on Z) := fun i j hij ↦
    (hind.indepFun (by omega : i + 1 ≠ j + 1)).comp hfm hfm
  have hident : ∀ i, IdentDistrib (Z i) (Z 0) μ μ := fun i ↦
    ((hid (i + 1)).trans (hid 1).symm).comp hfm
  have hlim : μ[Z 0] = growth μ (X 0) l := ((hid 1).comp hfm).integral_eq
  filter_upwards [strong_law_ae_real Z hint1 hpair hident] with ω hω
  rw [hlim] at hω
  refine hω.congr fun n ↦ ?_
  congr 1
  rw [wealth, Real.log_prod fun _ _ ↦
    ne_of_gt ((one_sub_mul_pos hc hl1).trans_le (one_sub_mul_le_one_add_mul (hlo _ ω) hl0))]
  rfl

/-- **With positive growth, the wealth tends to infinity, with no ceiling.** Under the hypotheses
of `tendsto_log_wealth_div_of_floor` without the integrability, if `growth μ (X 0) l > 0` the
wealth tends to infinity almost surely: a positive growth already makes `log (1 + l · X 0)`
integrable in Lean. It generalises `tendsto_wealth_atTop`, which also asks `X n ≤ C`. No
probability measure is assumed, and measurability of the returns is not used. -/
theorem tendsto_wealth_atTop_of_floor (hXm : ∀ n, Measurable (X n)) (hind : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ) (hc : 0 < c) (hlo : ∀ n ω, -c ≤ X n ω)
    (hl0 : 0 ≤ l) (hl1 : l < 1 / c) (hg : 0 < growth μ (X 0) l) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ wealth (fun _ _ ↦ l) X n ω) atTop atTop := by
  have hint : Integrable (fun ω ↦ Real.log (1 + l * X 0 ω)) μ := by
    by_contra h; rw [growth, integral_undef h] at hg; exact lt_irrefl _ hg
  filter_upwards [tendsto_log_wealth_div_of_floor hXm hind hid hc hlo hl0 hl1 hint] with ω hω
  set g := growth μ (X 0) l
  have hev : ∀ᶠ n : ℕ in atTop, g / 2 < Real.log (wealth (fun _ _ ↦ l) X n ω) / n :=
    hω.eventually (lt_mem_nhds (by linarith))
  have hexp : Tendsto (fun n : ℕ ↦ Real.exp ((n : ℝ) * (g / 2))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const (by linarith))
  refine tendsto_atTop_mono' atTop ?_ hexp
  filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hW := wealth_const_pos hc hlo hl0 hl1 n ω
  rw [← Real.exp_log hW]
  refine Real.exp_le_exp.mpr ?_
  rw [lt_div_iff₀ hnpos] at hn
  linarith

/-- **With a positive mean, some fixed stake reaches any level for sure, with no ceiling.**
Returns `X n` measurable, independent, with the distribution of `X 0`, `-c ≤ X n` with `0 < c`,
and `0 < ∫ X 0`. Then some stake `l` with `0 < l < 1/c` makes the wealth reach `1/α` at some time
with probability `1`, for every `α > 0`. It generalises `exists_stake_measureReal_reach_eq_one`,
which also asks `X n ≤ C`. -/
theorem exists_stake_measureReal_reach_eq_one_of_floor [IsProbabilityMeasure μ]
    (hXm : ∀ n, Measurable (X n))
    (hind : iIndepFun X μ) (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ) (hc : 0 < c)
    (hlo : ∀ n ω, -c ≤ X n ω) (hm : 0 < ∫ ω, X 0 ω ∂μ) :
    ∃ l, 0 < l ∧ l < 1 / c ∧
      ∀ α : ℝ, 0 < α → μ.real {ω | ∃ n, 1 / α ≤ wealth (fun _ _ ↦ l) X n ω} = 1 := by
  obtain ⟨l, hl0, hl1, hg⟩ := exists_growth_pos_of_floor (μ := μ) (hXm 0) hc (hlo 0) hm
  refine ⟨l, hl0, hl1, fun α _ ↦ ?_⟩
  have hae : ∀ᵐ ω ∂μ, ω ∈ {ω | ∃ n, 1 / α ≤ wealth (fun _ _ ↦ l) X n ω} := by
    filter_upwards [tendsto_wealth_atTop_of_floor hXm hind hid hc hlo hl0.le hl1 hg] with ω hω
    exact (hω.eventually_ge_atTop (1 / α)).exists
  rw [measureReal_congr (ae_eq_univ.mpr (ae_iff.mp hae)), probReal_univ]

end floor

end ClassicalLean.Probability.EdgeGrowth
