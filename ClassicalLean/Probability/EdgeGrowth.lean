/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Probability.NoEdgeWealth
import ClassicalLean.Probability.DependentSampleMean
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Moments.SubGaussian

/-!
# With a real edge, a fixed stake reaches any level

Returns `X 0, X 1, …` are independent, have the same distribution, and are bounded,
`-c ≤ X n ≤ C` with `0 < c`; the counts for dependent returns below do not assume the first two.
The versions without a ceiling, `exists_growth_pos_of_floor`, `tendsto_wealth_atTop_of_floor` and
`exists_stake_measureReal_reach_eq_one_of_floor`, need only the floor `-c ≤ X n`;
`tendsto_log_wealth_div_of_floor` replaces the ceiling by integrability of `log (1 + l · X 0)`.
A constant stake `l` turns them into the wealth
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
* `measureReal_wealth_lt_le_of_condExp` and `measureReal_wealth_lt_le_of_condExp_of_le`: the count
  of returns with no independence. Returns and stakes are adapted to a filtration (stakes may be
  chosen from the past), and each return's log factor has conditional growth at least `g` given
  the past; the second gives a growth large enough for `N` returns to confirm it at level `δ`,
  and `exp_neg_le_of_le_growth` is its arithmetic.

This is the other half of `NoEdgeWealth`: there, with no edge, the wealth reaches `1/α` with chance
at most `α`; here, with an edge, a suitable fixed stake reaches it for sure, eventually. The stake
is chosen knowing the true mean. `measureReal_wealth_lt_le` counts the returns: for a target of
at least `1`, the bound on the chance of still being below it after `N` returns falls exponentially
in `N` once `N · growth` passes the log of the target.

Each hypothesis of the first four is needed, except as noted below. Returns all equal to the first
(`X n = X 0`), `-1/2` or `1` with chance `1/2` each, are not independent; the wealth never grows
once the first return is `-1/2`, so the chance of ever reaching `2` is at most `1/2`. A return of
`0` every time has mean `0` and the wealth stays `1`. Returns `X n = 2^-n` on one point have
different distributions; `X 0 = 1` has positive mean, but the wealth stays below `e < 3`. With
`c = 0`, Lean's `1/0 = 0` leaves no stake in `(0, 1/c)`.
A stake of `1/c` itself, or a negative stake, can make the wealth `0`, while Lean's convention
`log 0 = 0` still reports a positive growth; and without the ceiling `C`, or the integrability
`tendsto_log_wealth_div_of_floor` asks instead, the growth can be infinite while Lean's integral of
a non-integrable function is `0`. Among the four long-run results this matters for the rate
(`tendsto_log_wealth_div`) only.
`tendsto_log_wealth_div_of_floor` does not use its measurability hypothesis. For the counts, the
floor, the ceiling and the stake bounds are needed, and for the new counts so are adapted returns
and adapted stakes; `0 ≤ C`, `StandardBorelSpace` and the measurability in
`measureReal_wealth_lt_le` are not shown needed.
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

/-! ### How many returns are enough, when returns depend on each other -/

section dependent

variable [StandardBorelSpace Ω] [IsProbabilityMeasure μ] {𝒢 : Filtration ℕ m0}

omit [StandardBorelSpace Ω] in
/-- Increments `D i` known at time `i + 1`, with values in `[lo, hi]`, and, given the past at time
`i`, the conditional mean of `exp (s D i)` at most `exp ((hi - lo)² s² / 8)`: then
`exp (s ∑ i < N, D i)` is integrable with mean at most `exp (N (hi - lo)² s² / 8)`. -/
lemma integral_exp_mul_sum_le {D : ℕ → Ω → ℝ} {lo hi s : ℝ} (hs : 0 ≤ s)
    (hDm : ∀ i, Measurable[𝒢 (i + 1)] (D i)) (hD : ∀ i ω, D i ω ∈ Set.Icc lo hi)
    (hcond : ∀ i, μ[fun ω ↦ Real.exp (s * D i ω) | 𝒢 i] ≤ᵐ[μ]
      fun _ ↦ Real.exp ((hi - lo) ^ 2 * s ^ 2 / 8)) (N : ℕ) :
    Integrable (fun ω ↦ Real.exp (s * ∑ i ∈ range N, D i ω)) μ ∧
    ∫ ω, Real.exp (s * ∑ i ∈ range N, D i ω) ∂μ ≤ Real.exp (N * (hi - lo) ^ 2 * s ^ 2 / 8) := by
  set K := |lo| + |hi|
  have hDabs : ∀ i ω, |D i ω| ≤ K := fun i ω ↦ by
    rw [abs_le]; constructor <;> linarith [(hD i ω).1, (hD i ω).2, le_abs_self lo, neg_abs_le lo,
      le_abs_self hi, neg_abs_le hi, abs_nonneg lo, abs_nonneg hi]
  -- measurability of the partial sums for the filtration
  have hWm : ∀ N, Measurable[𝒢 N] (fun ω ↦ ∑ i ∈ range N, D i ω) := fun N ↦ by
    refine Finset.measurable_sum _ fun i hi ↦ ?_
    exact (hDm i).mono (𝒢.mono (Nat.succ_le_of_lt (mem_range.mp hi))) le_rfl
  have hint : ∀ N, Integrable (fun ω ↦ Real.exp (s * ∑ i ∈ range N, D i ω)) μ := fun N ↦ by
    refine Integrable.of_bound (C := Real.exp (s * (N * K)))
      ((Real.measurable_exp.comp (measurable_const.mul ((hWm N).mono (𝒢.le N) le_rfl)))
        |>.aestronglyMeasurable) (Filter.Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hs)
    calc ∑ i ∈ range N, D i ω ≤ ∑ _i ∈ range N, K :=
          sum_le_sum fun i _ ↦ (le_abs_self _).trans (hDabs i ω)
      _ = N * K := by rw [sum_const, card_range, nsmul_eq_mul]
  have hDint : ∀ i, Integrable (fun ω ↦ Real.exp (s * D i ω)) μ := fun i ↦ by
    refine Integrable.of_bound (C := Real.exp (s * K))
      ((Real.measurable_exp.comp (measurable_const.mul ((hDm i).mono (𝒢.le (i + 1)) le_rfl)))
        |>.aestronglyMeasurable) (Filter.Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hDabs i ω)) hs)
  refine ⟨hint N, ?_⟩
  induction N with
  | zero => simp
  | succ N ih =>
    set F : Ω → ℝ := fun ω ↦ Real.exp (s * ∑ i ∈ range N, D i ω) with hF
    set G : Ω → ℝ := fun ω ↦ Real.exp (s * D N ω) with hG
    have hFG : (fun ω ↦ Real.exp (s * ∑ i ∈ range (N + 1), D i ω)) = F * G := by
      funext ω; simp only [hF, hG, Pi.mul_apply, sum_range_succ, mul_add, Real.exp_add]
    have hFm : StronglyMeasurable[𝒢 N] F :=
      (Real.measurable_exp.comp (measurable_const.mul (hWm N))).stronglyMeasurable
    have hpull := condExp_mul_of_stronglyMeasurable_left (m := 𝒢 N) hFm
      (hFG ▸ hint (N + 1)) (hDint N)
    set c := Real.exp ((hi - lo) ^ 2 * s ^ 2 / 8) with hc
    rw [hFG, ← integral_condExp (𝒢.le N)]
    calc ∫ ω, (μ[F * G | 𝒢 N]) ω ∂μ = ∫ ω, F ω * (μ[G | 𝒢 N]) ω ∂μ :=
          integral_congr_ae hpull
      _ ≤ ∫ ω, F ω * c ∂μ := by
          refine integral_mono_ae ?_ ((hint N).mul_const c) ?_
          · exact integrable_condExp.congr hpull
          · filter_upwards [hcond N] with ω hω
            exact mul_le_mul_of_nonneg_left hω (Real.exp_pos _).le
      _ = (∫ ω, F ω ∂μ) * c := integral_mul_const c F
      _ ≤ Real.exp (N * (hi - lo) ^ 2 * s ^ 2 / 8) * c :=
          mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
      _ = Real.exp (((N + 1 : ℕ) : ℝ) * (hi - lo) ^ 2 * s ^ 2 / 8) := by
          rw [hc, ← Real.exp_add]; push_cast; ring_nf

/-- **How many returns are enough, when returns depend on each other.** Returns `X` and stakes `S`
known by the time they are used (both adapted to `𝒢`), with `-c ≤ X n ≤ C`, `0 ≤ C`,
`0 ≤ S n ≤ l` and `l < 1/c`, and the log factor `log (1 + S n · X (n + 1))` of each return having
conditional mean at least `g` given `𝒢 n`. For `L ≤ N g`, the chance that the wealth after `N`
returns is below `exp L` is at most `exp (-2 (N g - L)² / (N B²))`,
`B = log (1 + l C) - log (1 - l c)`: `measureReal_wealth_lt_le`'s bound with `g` in place of the
growth, with no independence and no identical distribution. A stake chosen from the past is
allowed, but `g` must bound the conditional growth at the stake actually chosen, at every step.
When `N B² = 0`, Lean's `x / 0 = 0` makes the bound `1`. -/
theorem measureReal_wealth_lt_le_of_condExp {S X : ℕ → Ω → ℝ} {c C l g : ℝ}
    (hX : StronglyAdapted 𝒢 X) (hS : StronglyAdapted 𝒢 S)
    (hlo : ∀ n ω, -c ≤ X n ω) (hhi : ∀ n ω, X n ω ≤ C) (hC : 0 ≤ C)
    (hS0 : ∀ n ω, 0 ≤ S n ω) (hSl : ∀ n ω, S n ω ≤ l) (hl1 : l < 1 / c)
    (hg : ∀ n, ∀ᵐ ω ∂μ, g ≤ μ[fun ω ↦ Real.log (1 + S n ω * X (n + 1) ω) | 𝒢 n] ω)
    {N : ℕ} {L : ℝ} (hL : L ≤ N * g) :
    μ.real {ω | wealth S X N ω < Real.exp L} ≤
      Real.exp (-2 * (N * g - L) ^ 2 /
        (N * (Real.log (1 + l * C) - Real.log (1 - l * c)) ^ 2)) := by
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hl0 : 0 ≤ l := (hS0 0 ω₀).trans (hSl 0 ω₀)
  have hc : 0 < c := by
    by_contra h
    have : 1 / c ≤ 0 := one_div_nonpos.mpr (not_lt.mp h)
    linarith
  have hpos := one_sub_mul_pos hc hl1
  set a := Real.log (1 - l * c)
  set b := Real.log (1 + l * C)
  set Z : ℕ → Ω → ℝ := fun n ω ↦ Real.log (1 + S n ω * X (n + 1) ω)
  -- each log factor lies in `[a, b]`
  have hlow : ∀ n ω, 1 - l * c ≤ 1 + S n ω * X (n + 1) ω := fun n ω ↦ by
    nlinarith [mul_nonneg (sub_nonneg.mpr (hSl n ω)) hc.le,
      mul_nonneg (hS0 n ω) (by linarith [hlo (n + 1) ω] : 0 ≤ X (n + 1) ω + c)]
  have hup : ∀ n ω, 1 + S n ω * X (n + 1) ω ≤ 1 + l * C := fun n ω ↦ by
    nlinarith [mul_nonneg (sub_nonneg.mpr (hSl n ω)) hC,
      mul_nonneg (hS0 n ω) (by linarith [hhi (n + 1) ω] : 0 ≤ C - X (n + 1) ω)]
  have hZab : ∀ n ω, Z n ω ∈ Set.Icc a b := fun n ω ↦
    ⟨Real.log_le_log hpos (hlow n ω), Real.log_le_log (hpos.trans_le (hlow n ω)) (hup n ω)⟩
  -- each log factor is known one step later
  have hZm : ∀ n, Measurable[𝒢 (n + 1)] (Z n) := fun n ↦ by
    have h1 : Measurable[𝒢 (n + 1)] (S n) :=
      (hS n).measurable.mono (𝒢.mono n.le_succ) le_rfl
    have h2 : Measurable[𝒢 (n + 1)] (X (n + 1)) := (hX (n + 1)).measurable
    exact (measurable_const.add (h1.mul h2)).log
  set D : ℕ → Ω → ℝ := fun n ω ↦ g - Z n ω with hD
  have hDab : ∀ n ω, D n ω ∈ Set.Icc (g - b) (g - a) := fun n ω ↦
    ⟨by simp only [hD]; linarith [(hZab n ω).2], by simp only [hD]; linarith [(hZab n ω).1]⟩
  have hDm : ∀ n, Measurable[𝒢 (n + 1)] (D n) := fun n ↦ measurable_const.sub (hZm n)
  have hwidth : (g - a) - (g - b) = b - a := by ring
  -- the moment bound, for every `s ≥ 0`
  have hmom : ∀ s, 0 ≤ s → Integrable (fun ω ↦ Real.exp (s * ∑ i ∈ range N, D i ω)) μ ∧
      ∫ ω, Real.exp (s * ∑ i ∈ range N, D i ω) ∂μ ≤
        Real.exp (N * (b - a) ^ 2 * s ^ 2 / 8) := fun s hs ↦ by
    have h := integral_exp_mul_sum_le (μ := μ) hs hDm hDab (fun i ↦ by
      rw [hwidth]
      exact DependentSampleMean.condExp_exp_mul_sub_le (𝒢.le i) ((hZm i).mono (𝒢.le (i + 1)) le_rfl)
        (Filter.Eventually.of_forall (hZab i)) (hg i) hs) N
    rwa [hwidth] at h
  -- the event lies inside `{ε ≤ ∑ D i}`
  set ε := N * g - L with hε
  have hε0 : 0 ≤ ε := by rw [hε]; linarith
  have hsubset : {ω | wealth S X N ω < Real.exp L} ⊆ {ω | ε ≤ ∑ i ∈ range N, D i ω} :=
      fun ω hω ↦ by
    have hfac : ∀ i ∈ range N, 0 < 1 + S i ω * X (i + 1) ω := fun i _ ↦
      hpos.trans_le (hlow i ω)
    have hW : 0 < wealth S X N ω := prod_pos hfac
    have hlog : Real.log (wealth S X N ω) < L := by
      rw [← Real.log_exp L]; exact Real.log_lt_log hW hω
    have hsum : Real.log (wealth S X N ω) = ∑ i ∈ range N, Z i ω := by
      rw [wealth, Real.log_prod fun i hi ↦ (hfac i hi).ne']
    have hDsum : ∑ i ∈ range N, D i ω = N * g - ∑ i ∈ range N, Z i ω := by
      simp [hD, sum_sub_distrib]
    change ε ≤ ∑ i ∈ range N, D i ω
    rw [hDsum, hε]; linarith
  -- Chernoff's bound at `s = 4 ε / (N B²)`
  set s := 4 * ε / (N * (b - a) ^ 2) with hs
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  obtain ⟨hint, hle⟩ := hmom s hs0
  refine (measureReal_mono hsubset).trans ?_
  refine (measure_ge_le_exp_mul_mgf ε hs0 hint).trans ?_
  calc Real.exp (-s * ε) * mgf (fun ω ↦ ∑ i ∈ range N, D i ω) μ s
      ≤ Real.exp (-s * ε) * Real.exp (N * (b - a) ^ 2 * s ^ 2 / 8) :=
        mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
    _ = Real.exp (-2 * ε ^ 2 / (N * (b - a) ^ 2)) := by
        rw [← Real.exp_add]
        congr 1
        by_cases h0 : (N : ℝ) * (b - a) ^ 2 = 0
        · simp [hs, h0]
        · rw [hs]; field_simp; ring

/-- **The arithmetic of a sufficient edge.** For `N > 0`, `B ≠ 0` and `δ > 0`, a growth of at least
`L/N + |B| √(log (1/δ) / (2N))` makes `exp (-2 (N g - L)² / (N B²))` at most `δ`. -/
theorem exp_neg_le_of_le_growth {N : ℕ} (hN : 0 < N) {B L g δ : ℝ} (hB : B ≠ 0) (hδ : 0 < δ)
    (hg : L / N + |B| * Real.sqrt (Real.log (1 / δ) / (2 * N)) ≤ g) :
    Real.exp (-2 * (N * g - L) ^ 2 / (N * B ^ 2)) ≤ δ := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hden : 0 < (N : ℝ) * B ^ 2 := by positivity
  set q := Real.log (1 / δ) with hq
  have hlogδ : Real.log δ = -q := by rw [hq, one_div, Real.log_inv, neg_neg]
  rw [← Real.exp_log hδ, hlogδ]
  refine Real.exp_le_exp.mpr ?_
  rw [neg_mul, neg_div, neg_le_neg_iff, le_div_iff₀ hden]
  rcases le_or_gt q 0 with hq0 | hq0
  · nlinarith [sq_nonneg ((N : ℝ) * g - L), hden.le]
  · set r := Real.sqrt (q / (2 * N))
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hr2 : r ^ 2 = q / (2 * N) := Real.sq_sqrt (by positivity)
    have hlin : N * (|B| * r) ≤ N * g - L := by
      have := mul_le_mul_of_nonneg_left hg hNpos.le
      rw [mul_add, mul_div_cancel₀ L hNpos.ne'] at this
      linarith
    have hnn : 0 ≤ N * (|B| * r) := by positivity
    have hsq : (N * (|B| * r)) ^ 2 ≤ (N * g - L) ^ 2 := pow_le_pow_left₀ hnn hlin 2
    have hval : (N * (|B| * r)) ^ 2 = N * B ^ 2 * q / 2 := by
      rw [mul_pow, mul_pow, sq_abs, hr2]; field_simp
    nlinarith [hsq, hval]

/-- **A sufficient edge for `N` returns.** Under the hypotheses of
`measureReal_wealth_lt_le_of_condExp` other than `L ≤ N g`, which follows here, with `N > 0`
returns and `δ > 0`, a conditional growth of at least `L/N + B √(log (1/δ) / (2N))` per return,
`B = log (1 + l C) - log (1 - l c)`, leaves the wealth below `exp L` with chance at most `δ`. It
reads the count the other way round: for a given number of returns it gives a growth large enough
for them to confirm it at level `δ`. -/
theorem measureReal_wealth_lt_le_of_condExp_of_le {S X : ℕ → Ω → ℝ} {c C l g : ℝ}
    (hX : StronglyAdapted 𝒢 X) (hS : StronglyAdapted 𝒢 S)
    (hlo : ∀ n ω, -c ≤ X n ω) (hhi : ∀ n ω, X n ω ≤ C) (hC : 0 ≤ C)
    (hS0 : ∀ n ω, 0 ≤ S n ω) (hSl : ∀ n ω, S n ω ≤ l) (hl1 : l < 1 / c)
    (hg : ∀ n, ∀ᵐ ω ∂μ, g ≤ μ[fun ω ↦ Real.log (1 + S n ω * X (n + 1) ω) | 𝒢 n] ω)
    {N : ℕ} (hN : 0 < N) {L δ : ℝ} (hδ : 0 < δ)
    (hgmin : L / N + (Real.log (1 + l * C) - Real.log (1 - l * c)) *
      Real.sqrt (Real.log (1 / δ) / (2 * N)) ≤ g) :
    μ.real {ω | wealth S X N ω < Real.exp L} ≤ δ := by
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hl0 : 0 ≤ l := (hS0 0 ω₀).trans (hSl 0 ω₀)
  have hc : 0 < c := by
    by_contra h
    have : 1 / c ≤ 0 := one_div_nonpos.mpr (not_lt.mp h)
    linarith
  have hpos := one_sub_mul_pos hc hl1
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  set B := Real.log (1 + l * C) - Real.log (1 - l * c)
  have hab : 1 - l * c ≤ 1 + l * C := by nlinarith [mul_nonneg hl0 hc.le, mul_nonneg hl0 hC]
  have hB0 : 0 ≤ B := sub_nonneg.mpr (Real.log_le_log hpos hab)
  have hsq0 : 0 ≤ Real.sqrt (Real.log (1 / δ) / (2 * N)) := Real.sqrt_nonneg _
  rcases hB0.eq_or_lt with hBz | hBpos
  · -- `B = 0` forces `l = 0`: every stake is `0`, the wealth is `1`, and `g ≤ 0`
    have heq : 1 + l * C = 1 - l * c := Real.log_injOn_pos
      (Set.mem_Ioi.mpr (hpos.trans_le hab)) (Set.mem_Ioi.mpr hpos) (by linarith)
    have hl : l = 0 := by
      have h0 : l * (C + c) = 0 := by linarith
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · linarith
    have hS : ∀ n ω, S n ω = 0 := fun n ω ↦ le_antisymm (hl ▸ hSl n ω) (hS0 n ω)
    have hW : ∀ ω, wealth S X N ω = 1 := fun ω ↦ by simp [wealth, hS]
    have hg0 : g ≤ 0 := by
      have h := hg 0
      simp only [hS, zero_mul, add_zero, Real.log_one] at h
      obtain ⟨ω, hω⟩ := h.exists
      rwa [condExp_const (𝒢.le 0)] at hω
    have hL : L ≤ 0 := by
      rw [← hBz, zero_mul, add_zero, div_le_iff₀ hNpos] at hgmin
      nlinarith
    have hempty : {ω | wealth S X N ω < Real.exp L} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt, hW]
      exact Real.exp_le_one_iff.mpr hL
    rw [hempty, measureReal_empty]; exact hδ.le
  · have hL : L ≤ N * g := by
      have : L / N ≤ g := by nlinarith [mul_nonneg hBpos.le hsq0]
      rwa [div_le_iff₀ hNpos, mul_comm] at this
    refine (measureReal_wealth_lt_le_of_condExp hX hS hlo hhi hC hS0 hSl hl1 hg hL).trans ?_
    exact exp_neg_le_of_le_growth hN hBpos.ne' hδ (by rwa [abs_of_pos hBpos])

end dependent

end ClassicalLean.Probability.EdgeGrowth
