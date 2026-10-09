/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Analysis.LogDrag

/-!
# Expected log growth for a finite list of outcomes

A fraction `x` of a quantity is exposed to a return `r i` with probability `q i` (finitely many
outcomes, `q i ≥ 0`, `∑ q i = 1`). The expected log growth is
`growth q r x = ∑ q i log (1 + x r i)`.

* `eq_of_isMaxOn_growth`: there is at most one maximising fraction, as soon as some outcome with
  positive probability has a nonzero return (strict concavity of `log`).
* `growth_nonpos_of_mean_nonpos`: if the mean return `∑ q i r i` is `≤ 0`, no nonnegative
  fraction has positive expected log growth.
* `le_growth_meanOverSecondMoment`: if the mean `μ₁ = ∑ q i r i` is positive and
  `μ₂ = ∑ q i r i ^ 2 > 0`, the fraction `x₀ = μ₁ / (μ₂ c)` with `c = 1 + 2R/(1-R)` has expected log
  growth at least `μ₁² / (2 μ₂ c)`, provided `|x₀ r i| ≤ R < 1` for every outcome.
* `log_one_add_ge`: if `u ≥ -R` with `0 ≤ R < 1`, then `log (1 + u) ≥ u - u² / (2 (1 - R))`. It
  needs only the downside, and its coefficient `1 / (2 (1 - R))` is no larger (strictly smaller when
  `R > 0`) than the `(1 + R) / (2 (1 - R))` behind `le_growth_meanOverSecondMoment`.
* `log_one_add_le`: if `-1 < u ≤ U` with `U ≥ 0`, then `log (1 + u) ≤ u - u² / (2 (1 + U))`.
* `growth_mem_Icc`: when every `x r i` lies in `[-R, U]`, the expected log growth of `x` lies
  between `x m - x² s₂ / (2 (1 - R))` and `x m - x² s₂ / (2 (1 + U))`, with `m` the mean and `s₂`
  the second moment of the returns. Read informally (not a theorem here): if `θ m / s₂` and the best
  fraction both keep every `x r i` in `[-R, U]`, the first keeps at least
  `(2 θ - θ² / (1 - R)) / (1 + U)` of the second's growth, about `θ (2 - θ)` when `R` and `U` are
  small; half of it keeps about three quarters.
* `growth_neg_of_lt`: a positive fraction above `2 (1 + U) m / s₂`, with every `x r i` in `(-1, U]`,
  has negative expected log growth.
* Two helper steps: `sum_mul_sub_sq_div` (the sum expanded) and `growth_le_sub_sq_div` (the upper
  bound alone).

Not proved here: that a maximiser exists in a stated interval, and how far `x₀` is from it. An exact
check over 2095 random distributions found the true maximiser between `1.55` and `6.0` times `x₀`
(for `R = 1/2`), so `x₀` is a conservative fraction with a guaranteed growth, not an approximation
of the optimum.
-/

open Real Finset

namespace ClassicalLean.Analysis.GeneralGrowth

variable {ι : Type*} (s : Finset ι) (q r : ι → ℝ)

/-- Expected log growth `∑ q i log (1 + x r i)`. -/
noncomputable def growth (x : ℝ) : ℝ := ∑ i ∈ s, q i * log (1 + x * r i)

/-- **No positive mean, no growth.** If the mean return is `≤ 0`, every fraction `x ≥ 0` with
`1 + x r i > 0` for all outcomes has expected log growth `≤ 0`. For a trader: never bet on a rule
whose average return is not positive; no bet size makes it grow. -/
theorem growth_nonpos_of_mean_nonpos (hq : ∀ i ∈ s, 0 ≤ q i)
    (hmean : ∑ i ∈ s, q i * r i ≤ 0) {x : ℝ} (hx : 0 ≤ x) (hdom : ∀ i ∈ s, 0 < 1 + x * r i) :
    growth s q r x ≤ 0 := by
  have h : growth s q r x ≤ ∑ i ∈ s, q i * (x * r i) :=
    sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left
      (by have := Real.log_le_sub_one_of_pos (hdom i hi); linarith) (hq i hi)
  have h2 : ∑ i ∈ s, q i * (x * r i) = x * ∑ i ∈ s, q i * r i := by
    rw [mul_sum]; exact sum_congr rfl fun i _ ↦ by ring
  rw [h2] at h
  nlinarith

/-- **A guaranteed-growth fraction from the mean and the second moment.** With mean `μ₁ > 0`,
second moment `μ₂ > 0`, `R < 1` and `c = 1 + 2R/(1-R)`, the fraction `x₀ = μ₁ / (μ₂ c)` has
expected log growth at least `μ₁² / (2 μ₂ c)` when `|x₀ r i| ≤ R` for every outcome. For a trader:
"bet the mean over the second moment, scaled down by `c`" is a fraction with a proved positive
growth; it is more cautious than the growth-maximising fraction. -/
theorem le_growth_meanOverSecondMoment (hq : ∀ i ∈ s, 0 ≤ q i) {R : ℝ} (hR : R < 1)
    (hμ₁ : 0 < ∑ i ∈ s, q i * r i) (hμ₂ : 0 < ∑ i ∈ s, q i * r i ^ 2)
    (hbd : ∀ i ∈ s, |(∑ i ∈ s, q i * r i) / ((∑ i ∈ s, q i * r i ^ 2) * (1 + 2 * R / (1 - R))) *
      r i| ≤ R) :
    (∑ i ∈ s, q i * r i) ^ 2 / (2 * (∑ i ∈ s, q i * r i ^ 2) * (1 + 2 * R / (1 - R))) ≤
      growth s q r ((∑ i ∈ s, q i * r i) /
        ((∑ i ∈ s, q i * r i ^ 2) * (1 + 2 * R / (1 - R)))) := by
  set μ₁ := ∑ i ∈ s, q i * r i with hμ₁def
  set μ₂ := ∑ i ∈ s, q i * r i ^ 2 with hμ₂def
  set c := 1 + 2 * R / (1 - R) with hcdef
  have hR0 : 0 ≤ R := by
    by_contra h
    push Not at h
    obtain ⟨i, hi⟩ : s.Nonempty := by
      by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      simp [hμ₁def, hne] at hμ₁
    exact absurd ((abs_nonneg _).trans (hbd i hi)) (not_le.mpr h)
  have h1R : 0 < 1 - R := by linarith
  have hc : 0 < c := by
    rw [hcdef]; have : 0 ≤ 2 * R / (1 - R) := by positivity
    linarith
  set x₀ := μ₁ / (μ₂ * c) with hx₀
  -- termwise lower bound from `log_one_add_bounds`
  have hterm : ∀ i ∈ s, q i * (x₀ * r i - (x₀ * r i) ^ 2 * (1 / 2 + R / (1 - R))) ≤
      q i * log (1 + x₀ * r i) := fun i hi ↦
    mul_le_mul_of_nonneg_left (LogDrag.log_one_add_bounds hR (hbd i hi)).1 (hq i hi)
  have hsum := sum_le_sum hterm
  have hexpand : ∑ i ∈ s, q i * (x₀ * r i - (x₀ * r i) ^ 2 * (1 / 2 + R / (1 - R))) =
      x₀ * μ₁ - x₀ ^ 2 * μ₂ * (c / 2) := by
    have hrhs : x₀ * μ₁ - x₀ ^ 2 * μ₂ * (c / 2) =
        ∑ i ∈ s, (x₀ * (q i * r i) - x₀ ^ 2 * (q i * r i ^ 2) * (c / 2)) := by
      rw [hμ₁def, hμ₂def, sum_sub_distrib, mul_sum, mul_sum, sum_mul]
    rw [hrhs]
    refine sum_congr rfl fun i _ ↦ ?_
    have hc2 : c / 2 = 1 / 2 + R / (1 - R) := by rw [hcdef]; field_simp
    rw [hc2]; ring
  rw [hexpand] at hsum
  have hval : x₀ * μ₁ - x₀ ^ 2 * μ₂ * (c / 2) = μ₁ ^ 2 / (2 * μ₂ * c) := by
    rw [hx₀]; field_simp; ring
  rw [hval] at hsum
  exact hsum

/-- **At most one maximising fraction.** If `x₁` and `x₂` both maximise `growth` over a convex
set `D` on which every `1 + x r i` is positive, and some outcome with `q i > 0` has `r i ≠ 0`, then
`x₁ = x₂`. For a trader: the best bet size, when it exists, is a single number. -/
theorem eq_of_isMaxOn_growth (hq : ∀ i ∈ s, 0 ≤ q i) {D : Set ℝ} (hD : Convex ℝ D)
    (hdom : ∀ x ∈ D, ∀ i ∈ s, 0 < 1 + x * r i) (hnz : ∃ i ∈ s, 0 < q i ∧ r i ≠ 0)
    {x₁ x₂ : ℝ} (h₁ : x₁ ∈ D) (h₂ : x₂ ∈ D) (hmax₁ : IsMaxOn (growth s q r) D x₁)
    (hmax₂ : IsMaxOn (growth s q r) D x₂) : x₁ = x₂ := by
  by_contra hne
  set m := (x₁ + x₂) / 2 with hm
  have hmD : m ∈ D := by
    have := hD h₁ h₂ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    convert this using 1; simp only [hm, smul_eq_mul]; ring
  -- termwise midpoint inequality, strict where `r i ≠ 0`
  have hle : ∀ i ∈ s, q i * ((log (1 + x₁ * r i) + log (1 + x₂ * r i)) / 2) ≤
      q i * log (1 + m * r i) := fun i hi ↦ by
    apply mul_le_mul_of_nonneg_left _ (hq i hi)
    have hc := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.mpr (hdom x₁ h₁ i hi))
      (Set.mem_Ioi.mpr (hdom x₂ h₂ i hi)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at hc
    have e : 1 / 2 * (1 + x₁ * r i) + 1 / 2 * (1 + x₂ * r i) = 1 + m * r i := by rw [hm]; ring
    rw [e] at hc; linarith
  obtain ⟨j, hj, hqj, hrj⟩ := hnz
  have hlt : q j * ((log (1 + x₁ * r j) + log (1 + x₂ * r j)) / 2) < q j * log (1 + m * r j) := by
    apply mul_lt_mul_of_pos_left _ hqj
    have hne' : 1 + x₁ * r j ≠ 1 + x₂ * r j := fun h ↦ hne (mul_right_cancel₀ hrj (by linarith))
    have hc := strictConcaveOn_log_Ioi.2 (Set.mem_Ioi.mpr (hdom x₁ h₁ j hj))
      (Set.mem_Ioi.mpr (hdom x₂ h₂ j hj)) hne' (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at hc
    have e : 1 / 2 * (1 + x₁ * r j) + 1 / 2 * (1 + x₂ * r j) = 1 + m * r j := by rw [hm]; ring
    rw [e] at hc; linarith
  have hstrict := sum_lt_sum hle ⟨j, hj, hlt⟩
  have hsplit : ∑ i ∈ s, q i * ((log (1 + x₁ * r i) + log (1 + x₂ * r i)) / 2) =
      (growth s q r x₁ + growth s q r x₂) / 2 := by
    unfold growth
    rw [← sum_add_distrib, div_eq_mul_one_div _ (2 : ℝ), sum_mul]
    exact sum_congr rfl fun i _ ↦ by ring
  rw [hsplit] at hstrict
  have hm1 : growth s q r m ≤ growth s q r x₁ := hmax₁ hmD
  have hm2 : growth s q r m ≤ growth s q r x₂ := hmax₂ hmD
  unfold growth at hm1 hm2 hstrict
  linarith

/-! ### The growth of a stake lies between two parabolas -/

/-- A loss of at most `R < 1`: `log (1 + u) ≥ u - u² / (2 (1 - R))`. -/
theorem log_one_add_ge {u R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) (hu : -R ≤ u) :
    u - u ^ 2 / (2 * (1 - R)) ≤ Real.log (1 + u) := by
  have h1R : 0 < 1 - R := by linarith
  set f : ℝ → ℝ := fun v ↦ Real.log (1 + v) - v + v ^ 2 / (2 * (1 - R)) with hf
  have hderiv : ∀ v, -1 < v → HasDerivAt f (v * (1 / (1 - R) - 1 / (1 + v))) v := by
    intro v hv
    have hv1 : (1 + v) ≠ 0 := by linarith
    have hlog : HasDerivAt (fun v : ℝ ↦ Real.log (1 + v)) (1 / (1 + v)) v := by
      have := ((hasDerivAt_id v).const_add 1).log (by simpa using hv1)
      simpa using this
    have hsq : HasDerivAt (fun v : ℝ ↦ v ^ 2 / (2 * (1 - R))) (2 * v / (2 * (1 - R))) v := by
      have := (hasDerivAt_pow 2 v).div_const (2 * (1 - R))
      simpa using this
    have := (hlog.sub (hasDerivAt_id v)).add hsq
    have hR' : 1 - R ≠ 0 := h1R.ne'
    have key : v * (1 / (1 - R) - 1 / (1 + v)) = 1 / (1 + v) - 1 + 2 * v / (2 * (1 - R)) := by
      field_simp
      ring
    rw [key]
    exact this
  have hcont : ∀ S : Set ℝ, (∀ v ∈ S, -1 < v) → ContinuousOn f S := fun S hS v hv ↦
    (hderiv v (hS v hv)).continuousAt.continuousWithinAt
  have hf0 : f 0 = 0 := by simp [hf]
  suffices 0 ≤ f u by simp only [hf] at this; linarith
  rw [← hf0]
  rcases le_total 0 u with h0 | h0
  · -- `u ≥ 0`: `f` is monotone on `[0, ∞)`
    have hmono : MonotoneOn f (Set.Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (hcont _ fun v hv ↦ ?_) ?_ ?_
      · have : (0 : ℝ) ≤ v := hv; linarith
      · intro v hv
        rw [interior_Ici] at hv
        have hv' : (0 : ℝ) < v := hv
        exact (hderiv v (by linarith)).differentiableAt.differentiableWithinAt
      · intro v hv
        rw [interior_Ici] at hv
        have hv' : (0 : ℝ) < v := hv
        rw [(hderiv v (by linarith)).deriv]
        apply mul_nonneg hv'.le
        rw [sub_nonneg]
        apply one_div_le_one_div_of_le h1R
        linarith
    exact hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h0) h0
  · -- `-R ≤ u ≤ 0`: `f` is antitone on `[-R, 0]`
    have hanti : AntitoneOn f (Set.Icc (-R) 0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) (hcont _ fun v hv ↦ ?_) ?_ ?_
      · linarith [hv.1]
      · intro v hv
        rw [interior_Icc] at hv
        exact (hderiv v (by linarith [hv.1])).differentiableAt.differentiableWithinAt
      · intro v hv
        rw [interior_Icc] at hv
        rw [(hderiv v (by linarith [hv.1])).deriv]
        apply mul_nonpos_of_nonpos_of_nonneg hv.2.le
        rw [sub_nonneg]
        apply one_div_le_one_div_of_le (by linarith [hv.1])
        linarith [hv.1]
    exact hanti ⟨hu, h0⟩ ⟨by linarith, le_rfl⟩ h0

/-- A gain of at most `U`: `log (1 + u) ≤ u - u² / (2 (1 + U))`. -/
theorem log_one_add_le {u U : ℝ} (hU : 0 ≤ U) (hu1 : -1 < u) (hu : u ≤ U) :
    Real.log (1 + u) ≤ u - u ^ 2 / (2 * (1 + U)) := by
  have h1U : 0 < 1 + U := by linarith
  set g : ℝ → ℝ := fun v ↦ v - v ^ 2 / (2 * (1 + U)) - Real.log (1 + v) with hg
  have hderiv : ∀ v, -1 < v → HasDerivAt g (v * (1 / (1 + v) - 1 / (1 + U))) v := by
    intro v hv
    have hv1 : (1 + v) ≠ 0 := by linarith
    have hlog : HasDerivAt (fun v : ℝ ↦ Real.log (1 + v)) (1 / (1 + v)) v := by
      have := ((hasDerivAt_id v).const_add 1).log (by simpa using hv1)
      simpa using this
    have hsq : HasDerivAt (fun v : ℝ ↦ v ^ 2 / (2 * (1 + U))) (2 * v / (2 * (1 + U))) v := by
      have := (hasDerivAt_pow 2 v).div_const (2 * (1 + U))
      simpa using this
    have := ((hasDerivAt_id v).sub hsq).sub hlog
    have hU' : 1 + U ≠ 0 := h1U.ne'
    have key : v * (1 / (1 + v) - 1 / (1 + U)) = 1 - 2 * v / (2 * (1 + U)) - 1 / (1 + v) := by
      field_simp
      ring
    rw [key]
    exact this
  have hcont : ∀ S : Set ℝ, (∀ v ∈ S, -1 < v) → ContinuousOn g S := fun S hS v hv ↦
    (hderiv v (hS v hv)).continuousAt.continuousWithinAt
  have hg0 : g 0 = 0 := by simp [hg]
  suffices 0 ≤ g u by simp only [hg] at this; linarith
  rw [← hg0]
  rcases le_total 0 u with h0 | h0
  · -- `0 ≤ u ≤ U`: `g` is monotone on `[0, U]`
    have hmono : MonotoneOn g (Set.Icc 0 U) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) (hcont _ fun v hv ↦ ?_) ?_ ?_
      · linarith [hv.1]
      · intro v hv
        rw [interior_Icc] at hv
        exact (hderiv v (by linarith [hv.1])).differentiableAt.differentiableWithinAt
      · intro v hv
        rw [interior_Icc] at hv
        rw [(hderiv v (by linarith [hv.1])).deriv]
        apply mul_nonneg hv.1.le
        rw [sub_nonneg]
        apply one_div_le_one_div_of_le (by linarith [hv.1])
        linarith [hv.2]
    exact hmono ⟨le_rfl, hU⟩ ⟨h0, hu⟩ h0
  · -- `-1 < u ≤ 0`: `g` is antitone on `(-1, 0]`
    have hanti : AntitoneOn g (Set.Ioc (-1) 0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ioc _ _) (hcont _ fun v hv ↦ hv.1) ?_ ?_
      · intro v hv
        rw [interior_Ioc] at hv
        exact (hderiv v hv.1).differentiableAt.differentiableWithinAt
      · intro v hv
        rw [interior_Ioc] at hv
        rw [(hderiv v hv.1).deriv]
        apply mul_nonpos_of_nonpos_of_nonneg hv.2.le
        rw [sub_nonneg]
        exact one_div_le_one_div_of_le (by linarith [hv.1]) (by linarith [hv.2])
    exact hanti ⟨hu1, h0⟩ ⟨by norm_num, le_rfl⟩ h0

/-- The termwise sum behind both bounds: `∑ q i (x r i - (x r i)² / k) = x m - x² s₂ / k`. -/
theorem sum_mul_sub_sq_div (x k : ℝ) :
    ∑ i ∈ s, q i * (x * r i - (x * r i) ^ 2 / k) =
      x * ∑ i ∈ s, q i * r i - x ^ 2 * (∑ i ∈ s, q i * r i ^ 2) / k := by
  rw [div_eq_mul_inv _ k, mul_sum, mul_sum, sum_mul, ← sum_sub_distrib]
  exact sum_congr rfl fun i _ ↦ by ring

/-- The upper bound alone: with every `x r i` in `(-1, U]`, the expected log growth is at most
`x m - x² s₂ / (2 (1 + U))`. -/
theorem growth_le_sub_sq_div (hq : ∀ i ∈ s, 0 ≤ q i) {x U : ℝ} (hU : 0 ≤ U)
    (hlo : ∀ i ∈ s, -1 < x * r i) (hhi : ∀ i ∈ s, x * r i ≤ U) :
    growth s q r x ≤
      x * ∑ i ∈ s, q i * r i - x ^ 2 * (∑ i ∈ s, q i * r i ^ 2) / (2 * (1 + U)) := by
  rw [← sum_mul_sub_sq_div]
  exact sum_le_sum fun i hi ↦
    mul_le_mul_of_nonneg_left (log_one_add_le hU (hlo i hi) (hhi i hi)) (hq i hi)

/-- The expected log growth of the stake `x` lies between `x m - x² s₂ / (2 (1 - R))` and
`x m - x² s₂ / (2 (1 + U))`, with `m` the mean and `s₂` the second moment of the returns, when every
`x r i` lies in `[-R, U]`. -/
theorem growth_mem_Icc (hq : ∀ i ∈ s, 0 ≤ q i) {x R U : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1)
    (hU : 0 ≤ U) (hlo : ∀ i ∈ s, -R ≤ x * r i) (hhi : ∀ i ∈ s, x * r i ≤ U) :
    x * ∑ i ∈ s, q i * r i - x ^ 2 * (∑ i ∈ s, q i * r i ^ 2) / (2 * (1 - R)) ≤
        growth s q r x ∧
      growth s q r x ≤
        x * ∑ i ∈ s, q i * r i - x ^ 2 * (∑ i ∈ s, q i * r i ^ 2) / (2 * (1 + U)) := by
  refine ⟨?_, growth_le_sub_sq_div s q r hq hU (fun i hi ↦ by linarith [hlo i hi]) hhi⟩
  rw [← sum_mul_sub_sq_div]
  exact sum_le_sum fun i hi ↦
    mul_le_mul_of_nonneg_left (log_one_add_ge hR0 hR1 (hlo i hi)) (hq i hi)

/-- A stake above `2 (1 + U) m / s₂` has negative expected log growth. -/
theorem growth_neg_of_lt (hq : ∀ i ∈ s, 0 ≤ q i) {x U : ℝ} (hU : 0 ≤ U) (hx : 0 < x)
    (hlo : ∀ i ∈ s, -1 < x * r i) (hhi : ∀ i ∈ s, x * r i ≤ U)
    (h : 2 * (1 + U) * ∑ i ∈ s, q i * r i < x * ∑ i ∈ s, q i * r i ^ 2) :
    growth s q r x < 0 := by
  have hle := growth_le_sub_sq_div s q r hq hU hlo hhi
  have h1U : 0 < 2 * (1 + U) := by linarith
  have key : x * ∑ i ∈ s, q i * r i - x ^ 2 * (∑ i ∈ s, q i * r i ^ 2) / (2 * (1 + U)) =
      x * (2 * (1 + U) * ∑ i ∈ s, q i * r i - x * ∑ i ∈ s, q i * r i ^ 2) / (2 * (1 + U)) := by
    field_simp
  rw [key] at hle
  have : x * (2 * (1 + U) * ∑ i ∈ s, q i * r i - x * ∑ i ∈ s, q i * r i ^ 2) / (2 * (1 + U)) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hx (by linarith)) h1U
  linarith

end ClassicalLean.Analysis.GeneralGrowth
