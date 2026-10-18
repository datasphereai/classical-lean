/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.StrongLaw
import Mathlib.Probability.CDF
import Mathlib.Probability.HasLawExists

/-!
# The Glivenko–Cantelli theorem

Real draws `X 0, X 1, …` on a probability space, pairwise independent and identically
distributed. `F = cdf (μ.map (X 0))` is Mathlib's distribution function of `X 0`,
`F x = P(X 0 ≤ x)`.

* `empiricalCDF X n ω x` — the share of the first `n` draws that are at most `x`; `0` for `n = 0`
  (Lean's `x / 0 = 0`). `empiricalCDFLT` is the same with `< x`.
* `tendsto_sup_abs_empiricalCDF_sub` — order LEAN-24, item 60, **the Glivenko–Cantelli
  theorem**: almost surely, `⨆ x : ℝ, |empiricalCDF X n ω x − F x| → 0` as `n → ∞`.
* `eventually_lt_sup_abs_empiricalCDF_sub` — order LEAN-32, item 107, **the Kolmogorov–Smirnov
  test is consistent**: for any hypothesised distribution function `F₀ = cdf ν₀`, almost surely
  `sup |F_n − F₀|` eventually exceeds every `c < sup |F − F₀|`. By the triangle inequality,
  `sup |F − F₀| ≤ sup |F_n − F| + sup |F_n − F₀|`, and the first term tends to `0` by item 60.
* `eventually_lt_sup_abs_empiricalCDF_sub_of_tendsto` — the same item's test: if `F` differs from
  `F₀` somewhere, a test that rejects when `sup |F_n − F₀|` exceeds thresholds `c n → 0` rejects
  eventually, almost surely (apply the first theorem with half of `sup |F − F₀| > 0`).

The supremum is over all real `x`. It is a real supremum of a family bounded by `1` (both functions
take values in `[0, 1]`; `bddAbove_abs_empiricalCDF_sub`), so Lean's convention for unbounded
families (`⨆ = 0`) never applies and
the value is the true supremum, the Kolmogorov–Smirnov distance between `F_n` and `F`. Pairwise
independence is assumed, which is weaker than independence, because Mathlib's strong law
(`strong_law_ae`) asks only for that.

The proof. For each `m ≥ 1` take the `m − 1` grid points `x_j = min {x : j/m ≤ F x}`,
`0 < j < m` (`gridPoint`; real numbers, since `F → 0` at `−∞` and `→ 1` at `+∞`). Then
`F (x_j) ≥ j/m` and `F (x_j⁻) ≤ j/m`. Every `x` lies between two grid points (or beyond the
first or last) that the monotone `F_n` and `F` cannot cross by more than `1/m`, so
`sup |F_n − F| ≤ D + 1/m`, where `D` adds up `|F_n − F|` and `|F_n(·⁻) − F(·⁻)|` at the grid
points (`abs_sub_le_of_grid`). The strong law, applied to the indicators of `(−∞, x_j]` and
`(−∞, x_j)` for the countably many pairs `(m, j)`, makes every such `D` tend to `0` almost surely.

## Hypotheses

Measured in order LEAN-24's checks (`checks.py`, lines G1 to G3). Independence is needed: with
every `X i` equal to one fair coin on `{0, 1}`, `|F_n(0) − F(0)| = 1/2` for every `n` (exact).
Identical distribution is needed: with `X i = 0` for even `i` and `1` for odd `i` (constants,
hence independent), `F = 1{x ≥ 0}` and `|F_n(1/2) − F(1/2)| = ⌊n/2⌋/n`, which tends to `1/2`
(checked equal to `⌊n/2⌋/n` at `n = 10, 11, 1000, 1001`). Only `X 0` is assumed measurable, and
only to compute its law
(`map_measureReal_apply`); Mathlib's strong law needs no measurability, since `IdentDistrib`
already makes each `X i` measurable up to a null set (review r60). An illustration (FLOAT, seeded
uniform draws): the supremum is `0.0551`, `0.0243`,
`0.0043` at `n = 100, 1000, 20000`.

Item 107 is wider than the plan's row, which takes `F` to differ from `F₀` somewhere: the first
theorem asks no such thing (when `F = F₀` the supremum is `0` and the claim is about `c < 0`), and
`F₀ = cdf ν₀` for any measure `ν₀` on `ℝ`, with no instance: Mathlib's `cdf_nonneg` and
`cdf_le_one` take none, so `cdf ν₀` lies in `[0, 1]`, every supremum here is of a family bounded by
`1` and is the true one, never Lean's `⨆ = 0`. (For `ν₀` that is not a probability measure,
`cdf ν₀` is still a distribution function: `tendsto_cdf_atBot` and `tendsto_cdf_atTop` take no
instance either.) The second theorem is an addition, for the plan's "a test with thresholds
`c_n → 0` rejects eventually". Its hypotheses are needed, by hand (order LEAN-32's checks): without
`F ≠ F₀` somewhere, `X i = 0` for every `i` and `F₀ = F = 1{x ≥ 0}` give `sup |F_n − F₀| = 0` for
`n ≥ 1`, never above `c n = 1/(n + 1)` (`107.drop.hne`); without `c n → 0`, `c n = 1` is never
below `sup |F_n − F₀| ≤ 1` (`107.drop.hc`); without independence, `X i = X 0` a fair coin on
`{0, 1}` and `F₀ = 1{x ≥ 1}` give `sup |F − F₀| = 1/2`, while on `{X 0 = 1}` (chance `1/2`)
`F_n = F₀` and `sup |F_n − F₀| = 0 < 1/4` for every `n` (`107.drop.indep`); without identical
distribution, `X i = 0` for even `i` and `1` for odd `i`, `F = 1{x ≥ 0}` and `F₀` the distribution
function of `(δ₀ + δ₁)/2` give `sup |F − F₀| = 1/2` and `F_n = F₀` at every even `n ≥ 2`, so
`c = 1/4` is not eventually below `sup |F_n − F₀|` (`107.drop.ident`). `hX0` is item 60's, used to
name the law; not shown needed. The witnesses draw fair coins on `ℕ → Bool` under Mathlib's
`Measure.infinitePi` (independence by `iIndepFun_infinitePi`, identical distribution by
`Measure.infinitePi_map_eval`), the first form order LEAN-32's rule 2 asked for; this module now
imports `Mathlib.Probability.HasLawExists` for them.

## What is cited

For works not read here, author, title and year only: V. Glivenko, "Sulla determinazione empirica
delle leggi di probabilità", 1933; F. P. Cantelli, "Sulla determinazione empirica delle leggi di
probabilità", 1933.

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-24): "glivenko" has no hit, and every
"cantelli" hit is the Borel–Cantelli lemma; "empirical (cdf|distribution function)|empiricalCDF"
none. Used: `strong_law_ae`, `cdf`, `cdf_eq_real`, `measure_cdf`, `StieltjesFunction.measure_Iio`,
`Monotone.tendsto_leftLim`, `IndepFun.comp`, `IdentDistrib.comp`, `ae_all_iff`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Finset

namespace ClassicalLean.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **empirical distribution function** of the first `n` draws `X 0 ω, …, X (n − 1) ω`: the
share of them at most `x`. For `n = 0` it is `0` (Lean's `x / 0 = 0`). -/
noncomputable def empiricalCDF (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (x : ℝ) : ℝ :=
  ((Finset.range n).filter fun i ↦ X i ω ≤ x).card / n

/-- The share of the first `n` draws strictly below `x`. -/
noncomputable def empiricalCDFLT (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (x : ℝ) : ℝ :=
  ((Finset.range n).filter fun i ↦ X i ω < x).card / n

omit [MeasurableSpace Ω] in
theorem empiricalCDF_mono (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) {x y : ℝ} (h : x ≤ y) :
    empiricalCDF X n ω x ≤ empiricalCDF X n ω y := by
  unfold empiricalCDF
  gcongr with i _ hi

omit [MeasurableSpace Ω] in
theorem empiricalCDF_le_empiricalCDFLT (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) {x y : ℝ} (h : x < y) :
    empiricalCDF X n ω x ≤ empiricalCDFLT X n ω y := by
  unfold empiricalCDF empiricalCDFLT
  gcongr with i _ hi

omit [MeasurableSpace Ω] in
theorem empiricalCDF_nonneg (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (x : ℝ) :
    0 ≤ empiricalCDF X n ω x := by
  unfold empiricalCDF; positivity

omit [MeasurableSpace Ω] in
theorem empiricalCDF_le_one (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (x : ℝ) :
    empiricalCDF X n ω x ≤ 1 := by
  unfold empiricalCDF
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [div_le_one (by exact_mod_cast hn)]
  exact_mod_cast (card_filter_le _ _).trans (card_range n).le

/-- The strong law of large numbers for the indicator of a measurable set `s`. -/
private theorem ae_tendsto_indicator {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (hX0 : Measurable (X 0)) (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) {s : Set ℝ} (hs : MeasurableSet s) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ range n, s.indicator (fun _ ↦ (1 : ℝ)) (X i ω))
      atTop (𝓝 (μ.real (X 0 ⁻¹' s))) := by
  set φ : ℝ → ℝ := s.indicator fun _ ↦ 1 with hφ
  have hφm : Measurable φ := measurable_const.indicator hs
  set Y : ℕ → Ω → ℝ := fun i ↦ φ ∘ X i with hY
  have hint : Integrable (Y 0) μ := by
    refine (integrable_const (1 : ℝ)).mono' (hφm.comp hX0).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ ?_)
    simp only [hY, hφ, Function.comp_apply, indicator]
    split_ifs <;> simp
  have hind : Pairwise (Function.onFun (· ⟂ᵢ[μ] ·) Y) := fun i j hij ↦
    (hindep hij).comp hφm hφm
  have hid : ∀ i, IdentDistrib (Y i) (Y 0) μ μ := fun i ↦ (hident i).comp hφm
  have hmean : μ[Y 0] = μ.real (X 0 ⁻¹' s) := by
    have : Y 0 = (X 0 ⁻¹' s).indicator fun _ ↦ (1 : ℝ) := by
      ext ω; simp only [hY, hφ, Function.comp_apply]; rfl
    rw [this, integral_indicator_const _ (hX0 hs), smul_eq_mul, mul_one]
  filter_upwards [strong_law_ae Y hint hind hid] with ω hω
  rw [hmean] at hω
  exact hω

omit [MeasurableSpace Ω] in
private theorem inv_mul_sum_Iic (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (y : ℝ) :
    (n : ℝ)⁻¹ * ∑ i ∈ range n, (Iic y).indicator (fun _ ↦ (1 : ℝ)) (X i ω) =
      empiricalCDF X n ω y := by
  simp only [indicator_apply, Set.mem_Iic, sum_boole, empiricalCDF, inv_mul_eq_div]

omit [MeasurableSpace Ω] in
private theorem inv_mul_sum_Iio (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (y : ℝ) :
    (n : ℝ)⁻¹ * ∑ i ∈ range n, (Iio y).indicator (fun _ ↦ (1 : ℝ)) (X i ω) =
      empiricalCDFLT X n ω y := by
  simp only [indicator_apply, Set.mem_Iio, sum_boole, empiricalCDFLT, inv_mul_eq_div]

/-- The quantile of a distribution function at a level `u ∈ (0, 1)`: the least `x` with
`u ≤ F x`. -/
private theorem quantile_spec (F : StieltjesFunction ℝ) (h0 : Tendsto F atBot (𝓝 0))
    (h1 : Tendsto F atTop (𝓝 1)) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    u ≤ F (sInf {x | u ≤ F x}) ∧ (∀ x, u ≤ F x → sInf {x | u ≤ F x} ≤ x) ∧
      Function.leftLim F (sInf {x | u ≤ F x}) ≤ u := by
  set S := {x | u ≤ F x} with hS
  have hne : S.Nonempty := by
    obtain ⟨x, hx⟩ := (h1.eventually (lt_mem_nhds hu.2)).exists
    exact ⟨x, le_of_lt hx⟩
  obtain ⟨x₀, hx₀⟩ := (h0.eventually (gt_mem_nhds hu.1)).exists_forall_of_atBot
  have hbdd : BddBelow S := ⟨x₀, fun y hy ↦ by
    by_contra h
    push Not at h
    exact absurd hy (not_le.2 (hx₀ y h.le))⟩
  refine ⟨?_, fun x hx ↦ csInf_le hbdd hx, ?_⟩
  · refine ge_of_tendsto ((F.right_continuous _).mono Ioi_subset_Ici_self)
      (eventually_nhdsWithin_of_forall fun x hx ↦ ?_)
    obtain ⟨y, hyS, hyx⟩ := exists_lt_of_csInf_lt hne hx
    exact hyS.trans (F.mono hyx.le)
  · refine le_of_tendsto (F.mono.tendsto_leftLim _)
      (eventually_nhdsWithin_of_forall fun y hy ↦ ?_)
    by_contra h
    push Not at h
    exact absurd (csInf_le hbdd h.le) (not_le.2 hy)

/-- The grid point at level `j / m`: the least `x` with `j / m ≤ F x`. -/
private noncomputable def gridPoint (F : ℝ → ℝ) (m j : ℕ) : ℝ := sInf {x | (j : ℝ) / m ≤ F x}

/-- **The bracketing step.** If `Fn` is nondecreasing with values in `[0, 1]` and lies below
`Gn b` left of every `b`, then at every `x` it is within `D + 1/m` of `F`, where `D` adds up the
gaps `|Fn − F|` and `|Gn − F(·⁻)|` at the `m − 1` grid points. -/
private theorem abs_sub_le_of_grid (F : StieltjesFunction ℝ) (h0 : Tendsto F atBot (𝓝 0))
    (h1 : Tendsto F atTop (𝓝 1)) (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1) (Fn Gn : ℝ → ℝ)
    (hmono : Monotone Fn) (hlt : ∀ x b, x < b → Fn x ≤ Gn b) (hn0 : ∀ x, 0 ≤ Fn x)
    (hn1 : ∀ x, Fn x ≤ 1) {m : ℕ} (hm : 0 < m) (x : ℝ) :
    |Fn x - F x| ≤ (∑ j ∈ Finset.Ioo 0 m, (|Fn (gridPoint F m j) - F (gridPoint F m j)| +
      |Gn (gridPoint F m j) - Function.leftLim F (gridPoint F m j)|)) + 1 / m := by
  set D := ∑ j ∈ Finset.Ioo 0 m, (|Fn (gridPoint F m j) - F (gridPoint F m j)| +
      |Gn (gridPoint F m j) - Function.leftLim F (gridPoint F m j)|) with hD_def
  have hterm : ∀ j ∈ Finset.Ioo 0 m, |Fn (gridPoint F m j) - F (gridPoint F m j)| ≤ D ∧
      |Gn (gridPoint F m j) - Function.leftLim F (gridPoint F m j)| ≤ D := by
    intro j hj
    have h := single_le_sum (f := fun j ↦ |Fn (gridPoint F m j) - F (gridPoint F m j)| +
      |Gn (gridPoint F m j) - Function.leftLim F (gridPoint F m j)|)
      (fun i _ ↦ add_nonneg (abs_nonneg _) (abs_nonneg _)) hj
    exact ⟨le_trans (le_add_of_nonneg_right (abs_nonneg _)) h,
      le_trans (le_add_of_nonneg_left (abs_nonneg _)) h⟩
  have hD0 : 0 ≤ D := sum_nonneg fun i _ ↦ add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hlevel : ∀ j : ℕ, 0 < j → j < m → (j : ℝ) / m ∈ Ioo (0 : ℝ) 1 := fun j h0 h1 ↦
    ⟨div_pos (Nat.cast_pos.2 h0) hmR, (div_lt_one hmR).2 (Nat.cast_lt.2 h1)⟩
  have hstep : ∀ a : ℝ, (a + 1) / m = a / m + 1 / m := fun a ↦ add_div _ _ _
  set u := F x with hu
  set j := ⌊u * m⌋₊ with hj
  have hj1 : (j : ℝ) / m ≤ u :=
    (div_le_iff₀ hmR).2 (Nat.floor_le (mul_nonneg (hF0 x) hmR.le))
  have hj2 : u < ((j : ℝ) + 1) / m := (lt_div_iff₀ hmR).2 (Nat.lt_floor_add_one _)
  rw [abs_le]
  constructor
  · -- `F x − Fn x ≤ D + 1/m`
    set j' := min j (m - 1) with hj'
    have hj'j : (j' : ℝ) ≤ j := Nat.cast_le.2 (min_le_left _ _)
    have hFx : u ≤ ((j' : ℝ) + 1) / m := by
      rcases le_total j (m - 1) with h | h
      · rw [hj', min_eq_left h]; exact hj2.le
      · rw [hj', min_eq_right h, Nat.cast_sub hm, Nat.cast_one, sub_add_cancel, div_self hmR.ne']
        exact hF1 x
    rcases Nat.eq_zero_or_pos j' with h0' | hpos
    · rw [h0', Nat.cast_zero, zero_add] at hFx
      linarith [hn0 x]
    · have hj'm : j' < m := lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hm one_pos)
      obtain ⟨q1, q2, -⟩ := quantile_spec F h0 h1 (hlevel j' hpos hj'm)
      have ha : gridPoint F m j' ≤ x :=
        q2 x (le_trans (div_le_div_of_nonneg_right hj'j hmR.le) hj1)
      have h3 := (abs_le.1 (hterm j' (Finset.mem_Ioo.2 ⟨hpos, hj'm⟩)).1).1
      have h4 := hmono ha
      rw [hstep] at hFx
      have q1' : (j' : ℝ) / m ≤ F (gridPoint F m j') := q1
      linarith
  · -- `Fn x − F x ≤ D + 1/m`
    by_cases hjm : j + 1 < m
    · have hlev := hlevel (j + 1) (Nat.succ_pos j) hjm
      push_cast at hlev
      obtain ⟨q1, -, q3⟩ := quantile_spec F h0 h1 hlev
      have q1' : ((j : ℝ) + 1) / m ≤ F (gridPoint F m (j + 1)) := by
        simpa [gridPoint] using q1
      have q3' : Function.leftLim F (gridPoint F m (j + 1)) ≤ ((j : ℝ) + 1) / m := by
        simpa [gridPoint] using q3
      have hxb : x < gridPoint F m (j + 1) := by
        by_contra hb
        push Not at hb
        linarith [F.mono hb]
      have h3 := (abs_le.1 (hterm (j + 1)
        (Finset.mem_Ioo.2 ⟨Nat.succ_pos j, hjm⟩)).2).2
      have h4 := hlt x _ hxb
      rw [hstep] at q3'
      linarith
    · push Not at hjm
      have hmj : (m : ℝ) ≤ j + 1 := by exact_mod_cast hjm
      have : 1 ≤ ((j : ℝ) + 1) / m := (le_div_iff₀ hmR).2 (by linarith)
      rw [hstep] at this
      linarith [hn1 x]

omit [MeasurableSpace Ω] in
/-- The family under the supremum is bounded above (by `1`), so `⨆` is its true supremum and
not Lean's `0` for an unbounded family. -/
theorem bddAbove_abs_empiricalCDF_sub (X : ℕ → Ω → ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) (ω : Ω) : BddAbove (range fun x ↦ |empiricalCDF X n ω x - cdf μ x|) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨x, rfl⟩
  rw [abs_le]
  constructor <;> linarith [empiricalCDF_nonneg X n ω x, empiricalCDF_le_one X n ω x,
    cdf_nonneg μ x, cdf_le_one μ x]

/-- **The Glivenko–Cantelli theorem.** For independent (pairwise is enough), identically
distributed real draws `X 0, X 1, …`, the empirical distribution function of the first `n` draws
converges to the distribution function `F = cdf (law of X 0)` uniformly over all real `x`, almost
surely: `sup over x ∈ ℝ of |F_n(x) − F(x)| → 0`. -/
theorem tendsto_sup_abs_empiricalCDF_sub {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX0 : Measurable (X 0))
    (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ⨆ x : ℝ, |empiricalCDF X n ω x - cdf (μ.map (X 0)) x|) atTop
      (𝓝 0) := by
  set ν := μ.map (X 0) with hν
  set F := cdf ν with hFdef
  have hF : ∀ y, F y = μ.real (X 0 ⁻¹' Iic y) := fun y ↦ by
    rw [hFdef, cdf_eq_real, hν, map_measureReal_apply hX0 measurableSet_Iic]
  have hG : ∀ y, Function.leftLim F y = μ.real (X 0 ⁻¹' Iio y) := fun y ↦ by
    rw [← map_measureReal_apply hX0 measurableSet_Iio, ← hν, measureReal_def,
      ← measure_cdf (μ := ν), ← hFdef, F.measure_Iio (tendsto_cdf_atBot ν), sub_zero,
      ENNReal.toReal_ofReal]
    exact (cdf_nonneg _ _).trans (F.mono.le_leftLim (sub_one_lt y))
  have hpt : ∀ᵐ ω ∂μ, ∀ m j : ℕ,
      Tendsto (fun n ↦ empiricalCDF X n ω (gridPoint F m j)) atTop
        (𝓝 (F (gridPoint F m j))) ∧
      Tendsto (fun n ↦ empiricalCDFLT X n ω (gridPoint F m j)) atTop
        (𝓝 (Function.leftLim F (gridPoint F m j))) := by
    rw [ae_all_iff]; intro m
    rw [ae_all_iff]; intro j
    filter_upwards
      [ae_tendsto_indicator hX0 hindep hident (measurableSet_Iic (a := gridPoint F m j)),
      ae_tendsto_indicator hX0 hindep hident (measurableSet_Iio (a := gridPoint F m j))]
      with ω h1 h2
    simp only [inv_mul_sum_Iic, inv_mul_sum_Iio, ← hF, ← hG] at h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [hpt] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
  set M := k + 1 with hM
  have hMpos : 0 < M := Nat.succ_pos k
  have hD : Tendsto (fun n ↦ ∑ j ∈ Finset.Ioo 0 M,
      (|empiricalCDF X n ω (gridPoint F M j) - F (gridPoint F M j)| +
        |empiricalCDFLT X n ω (gridPoint F M j) - Function.leftLim F (gridPoint F M j)|))
      atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.Ioo 0 M) fun j _ ↦
      ((tendsto_sub_nhds_zero_iff.2 (hω M j).1).abs.add
        (tendsto_sub_nhds_zero_iff.2 (hω M j).2).abs)
    simpa using this
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hD (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hsup := ciSup_le fun x ↦ abs_sub_le_of_grid F (tendsto_cdf_atBot ν) (tendsto_cdf_atTop ν)
    (cdf_nonneg ν) (cdf_le_one ν) (empiricalCDF X n ω) (empiricalCDFLT X n ω)
    (fun a b h ↦ empiricalCDF_mono X n ω h) (fun a b h ↦ empiricalCDF_le_empiricalCDFLT X n ω h)
    (empiricalCDF_nonneg X n ω) (empiricalCDF_le_one X n ω) hMpos x
  have hnn : 0 ≤ ⨆ x : ℝ, |empiricalCDF X n ω x - F x| :=
    Real.iSup_nonneg fun x ↦ abs_nonneg _
  have hDn := hN n hn
  rw [Real.dist_eq, sub_zero] at hDn ⊢
  rw [abs_of_nonneg hnn]
  have hDabs := le_abs_self (∑ j ∈ Finset.Ioo 0 M,
      (|empiricalCDF X n ω (gridPoint F M j) - F (gridPoint F M j)| +
        |empiricalCDFLT X n ω (gridPoint F M j) - Function.leftLim F (gridPoint F M j)|))
  have hk' : (1 : ℝ) / (M : ℝ) < ε / 2 := by rw [hM]; push_cast; exact hk
  linarith

/-- **The Kolmogorov–Smirnov test is consistent** (order LEAN-32, item 107): for any measure
`ν₀` on `ℝ`, almost surely, every `c` below `sup |F − cdf ν₀|` lies below
`sup |F_n − cdf ν₀|` for all large `n`, where `F` is the distribution function of `X 0` and
`F_n` the empirical one. -/
theorem eventually_lt_sup_abs_empiricalCDF_sub {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX0 : Measurable (X 0))
    (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (ν₀ : Measure ℝ) :
    ∀ᵐ ω ∂μ, ∀ c < ⨆ x : ℝ, |cdf (μ.map (X 0)) x - cdf ν₀ x|,
      ∀ᶠ n in atTop, c < ⨆ x : ℝ, |empiricalCDF X n ω x - cdf ν₀ x| := by
  filter_upwards [tendsto_sup_abs_empiricalCDF_sub hX0 hindep hident] with ω hω
  intro c hc
  filter_upwards [hω.eventually (gt_mem_nhds (sub_pos.2 hc))] with n hn
  have hb : BddAbove (range fun x ↦ |empiricalCDF X n ω x - cdf ν₀ x|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨x, rfl⟩
    rw [abs_le]
    constructor <;> linarith [empiricalCDF_nonneg X n ω x, empiricalCDF_le_one X n ω x,
      cdf_nonneg ν₀ x, cdf_le_one ν₀ x]
  have key : ⨆ x : ℝ, |cdf (μ.map (X 0)) x - cdf ν₀ x|
      ≤ (⨆ x : ℝ, |empiricalCDF X n ω x - cdf (μ.map (X 0)) x|)
        + ⨆ x : ℝ, |empiricalCDF X n ω x - cdf ν₀ x| := by
    refine ciSup_le fun x ↦ ?_
    have h1 := le_ciSup (bddAbove_abs_empiricalCDF_sub X (μ.map (X 0)) n ω) x
    have h2 := le_ciSup hb x
    have h3 := abs_sub_le (cdf (μ.map (X 0)) x) (empiricalCDF X n ω x) (cdf ν₀ x)
    rw [abs_sub_comm (cdf (μ.map (X 0)) x) (empiricalCDF X n ω x)] at h3
    linarith
  linarith

/-- **The Kolmogorov–Smirnov test rejects eventually** (order LEAN-32, item 107): if `F` differs
from `cdf ν₀` somewhere and the thresholds `c n` tend to `0`, then almost surely
`c n < sup |F_n − cdf ν₀|` for all large `n`. -/
theorem eventually_lt_sup_abs_empiricalCDF_sub_of_tendsto {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} (hX0 : Measurable (X 0))
    (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (ν₀ : Measure ℝ)
    (hne : ∃ x, cdf (μ.map (X 0)) x ≠ cdf ν₀ x) {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, c n < ⨆ x : ℝ, |empiricalCDF X n ω x - cdf ν₀ x| := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hD : 0 < ⨆ x : ℝ, |cdf (μ.map (X 0)) x - cdf ν₀ x| := by
    have hb : BddAbove (range fun x ↦ |cdf (μ.map (X 0)) x - cdf ν₀ x|) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨x, rfl⟩
      rw [abs_le]
      constructor <;> linarith [cdf_nonneg (μ.map (X 0)) x, cdf_le_one (μ.map (X 0)) x,
        cdf_nonneg ν₀ x, cdf_le_one ν₀ x]
    exact (abs_pos.2 (sub_ne_zero.2 hx₀)).trans_le (le_ciSup hb x₀)
  filter_upwards [eventually_lt_sup_abs_empiricalCDF_sub hX0 hindep hident ν₀] with ω hω
  filter_upwards [hω _ (half_lt_self hD), hc.eventually (gt_mem_nhds (half_pos hD))]
    with n h1 h2
  exact h2.trans h1

end ClassicalLean.Probability

/-- The hypotheses of `eventually_lt_sup_abs_empiricalCDF_sub` hold together: fair coins `ω i` on
`ℕ → Bool` under `Measure.infinitePi` of the uniform law on `Bool`, `X i ω = 1` when `ω i` is
true and `0` otherwise (independent, identically distributed, not constant), and `ν₀` the point
mass at `2`. -/
example := ClassicalLean.Probability.eventually_lt_sup_abs_empiricalCDF_sub (Ω := ℕ → Bool)
  (μ := Measure.infinitePi fun _ : ℕ ↦ uniformOn (Set.univ : Set Bool))
  (X := fun i ω ↦ if ω i then 1 else 0)
  ((measurable_of_finite fun b : Bool ↦ if b then (1 : ℝ) else 0).comp (measurable_pi_apply 0))
  (fun i j hij ↦ (iIndepFun_infinitePi (P := fun _ : ℕ ↦ uniformOn (Set.univ : Set Bool))
    (X := fun _ b ↦ if b then (1 : ℝ) else 0)
    fun _ ↦ measurable_of_finite _).indepFun hij)
  (fun i ↦ (show IdentDistrib (fun ω : ℕ → Bool ↦ ω i) (fun ω : ℕ → Bool ↦ ω 0)
      (Measure.infinitePi fun _ : ℕ ↦ uniformOn (Set.univ : Set Bool))
      (Measure.infinitePi fun _ : ℕ ↦ uniformOn (Set.univ : Set Bool)) from
    ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable, by
      rw [Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]⟩).comp
    (measurable_of_finite fun b : Bool ↦ if b then (1 : ℝ) else 0))
  (ν₀ := Measure.dirac 2)

/-- The hypotheses of `eventually_lt_sup_abs_empiricalCDF_sub_of_tendsto` hold together: the same
fair coins and `ν₀` the point mass at `2`; the distribution functions differ at `1` (`1` for the
coins, every draw being at most `1`, and `0` for the point mass), and `c n = 1/(n + 1) → 0`. -/
example := ClassicalLean.Probability.eventually_lt_sup_abs_empiricalCDF_sub_of_tendsto
  (Ω := ℕ → Bool) (μ := Measure.infinitePi fun _ : ℕ ↦ uniformOn (Set.univ : Set Bool))
  (X := fun i ω ↦ if ω i then 1 else 0)
  ((measurable_of_finite fun b : Bool ↦ if b then (1 : ℝ) else 0).comp (measurable_pi_apply 0))
  (fun i j hij ↦ (iIndepFun_infinitePi (P := fun _ : ℕ ↦ uniformOn (Set.univ : Set Bool))
    (X := fun _ b ↦ if b then (1 : ℝ) else 0)
    fun _ ↦ measurable_of_finite _).indepFun hij)
  (fun i ↦ (show IdentDistrib (fun ω : ℕ → Bool ↦ ω i) (fun ω : ℕ → Bool ↦ ω 0)
      (Measure.infinitePi fun _ : ℕ ↦ uniformOn (Set.univ : Set Bool))
      (Measure.infinitePi fun _ : ℕ ↦ uniformOn (Set.univ : Set Bool)) from
    ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable, by
      rw [Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]⟩).comp
    (measurable_of_finite fun b : Bool ↦ if b then (1 : ℝ) else 0))
  (ν₀ := Measure.dirac 2)
  ⟨1, by
    rw [cdf_eq_real, cdf_eq_real, map_measureReal_apply
      (show Measurable fun ω : ℕ → Bool ↦ if ω 0 then (1 : ℝ) else 0 from
        (measurable_of_finite fun b : Bool ↦ if b then (1 : ℝ) else 0).comp
          (measurable_pi_apply 0)) measurableSet_Iic]
    have hu : (fun ω : ℕ → Bool ↦ if ω 0 then (1 : ℝ) else 0) ⁻¹' Set.Iic 1 = Set.univ :=
      Set.eq_univ_of_forall fun ω ↦ by by_cases h : ω 0 <;> simp [h]
    rw [hu, probReal_univ]
    simp [Measure.real, Measure.dirac_apply' _ measurableSet_Iic]⟩
  (c := fun n ↦ 1 / ((n : ℝ) + 1)) tendsto_one_div_add_atTop_nhds_zero_nat
