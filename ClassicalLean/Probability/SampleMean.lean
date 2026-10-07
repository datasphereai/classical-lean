/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.Moments.SubGaussian

/-!
# How far the mean of bounded independent samples strays from its expectation

For independent random variables `X 0, X 1, …` with values in `[0, 1]` and common mean `p`, the
average of the first `n` is more than `e` away from `p` with probability at most
`2 * exp (-2 * n * e ^ 2)` (`measureReal_abs_sampleMean_sub_ge_le`). Read with `X i` the indicator
of "trial `i` succeeded", this says how many independent trials it takes before the observed success
rate can be trusted to within `e`.

`sampleSizeOK e δ k n` is a computable test on rationals: when it holds, `2 * exp (-2 * n * e ^ 2)
≤ δ` (`two_mul_exp_neg_le_of_sampleSizeOK`), so the observed rate is within `e` of the true one with
probability at least `1 - δ`. It rests on `(1 + y / k) ^ k ≤ exp y`. `minSampleSize` searches for
the least such `n`.

## What Mathlib provides

Hoeffding's lemma (`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`) and the one-sided Hoeffding
inequality for independent sums
(`ProbabilityTheory.HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun`). This module applies
the one-sided bound to `X i - p` and to `p - X i` and adds the two tails; the sample-size test and
its proof are new here.
-/

open MeasureTheory ProbabilityTheory Real Finset

namespace ClassicalLean.Probability.SampleMean

section Hoeffding

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The sample mean of bounded independent variables.** For independent `X i` with values in
`[0, 1]` and common mean `p`, `P(|(X 0 + ⋯ + X (n-1)) / n - p| ≥ e) ≤ 2 exp (-2 n e²)`. -/
theorem measureReal_abs_sampleMean_sub_ge_le {X : ℕ → Ω → ℝ} (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i)) (h_bdd : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    {p : ℝ} (h_mean : ∀ i, μ[X i] = p) {n : ℕ} (hn : 0 < n) {e : ℝ} (he : 0 ≤ e) :
    μ.real {ω | e ≤ |(∑ i ∈ range n, X i ω) / n - p|} ≤ 2 * exp (-2 * n * e ^ 2) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  -- the centred variables, and their negatives, are sub-Gaussian with parameter 1/4
  have hsub : ∀ i, HasSubgaussianMGF (fun ω ↦ X i ω - p) (1 / 4) μ := by
    intro i
    have h := hasSubgaussianMGF_of_mem_Icc (h_meas i).aemeasurable (h_bdd i)
    rw [h_mean i] at h
    convert h using 1
    ext
    simp only [sub_zero, NNReal.coe_div, NNReal.coe_one, NNReal.coe_pow, nnnorm_one]
    norm_num
  have hsub' : ∀ i, HasSubgaussianMGF (fun ω ↦ p - X i ω) (1 / 4) μ := by
    intro i
    convert (hsub i).neg using 1
    ext ω; simp
  have hind : iIndepFun (fun i ω ↦ X i ω - p) μ :=
    h_indep.comp (fun _ x ↦ x - p) (fun _ ↦ measurable_id.sub_const p)
  have hind' : iIndepFun (fun i ω ↦ p - X i ω) μ :=
    h_indep.comp (fun _ x ↦ p - x) (fun _ ↦ measurable_const.sub measurable_id)
  have hne : (0 : ℝ) ≤ n * e := by positivity
  have up := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hind (n := n)
    (fun i _ ↦ hsub i) hne
  have dn := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hind' (n := n)
    (fun i _ ↦ hsub' i) hne
  have hexp : -(n * e) ^ 2 / (2 * n * ((1 / 4 : NNReal) : ℝ)) = -2 * n * e ^ 2 := by
    push_cast; field_simp; ring
  rw [hexp] at up dn
  -- the event is inside the union of the two one-sided events
  have hsubset : {ω | e ≤ |(∑ i ∈ range n, X i ω) / n - p|} ⊆
      {ω | n * e ≤ ∑ i ∈ range n, (X i ω - p)} ∪ {ω | n * e ≤ ∑ i ∈ range n, (p - X i ω)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    simp only [Set.mem_union, Set.mem_ofPred_eq, sum_sub_distrib, sum_const, card_range,
      nsmul_eq_mul]
    have key : (∑ i ∈ range n, X i ω) / n - p = ((∑ i ∈ range n, X i ω) - n * p) / n := by
      field_simp
    rw [key, abs_div, abs_of_pos hn', le_div_iff₀ hn'] at hω
    rcases le_abs'.mp hω with h | h
    · right; linarith
    · left; linarith
  calc μ.real {ω | e ≤ |(∑ i ∈ range n, X i ω) / n - p|}
      ≤ μ.real ({ω | n * e ≤ ∑ i ∈ range n, (X i ω - p)} ∪
          {ω | n * e ≤ ∑ i ∈ range n, (p - X i ω)}) := measureReal_mono hsubset
    _ ≤ μ.real {ω | n * e ≤ ∑ i ∈ range n, (X i ω - p)} +
          μ.real {ω | n * e ≤ ∑ i ∈ range n, (p - X i ω)} := measureReal_union_le _ _
    _ ≤ exp (-2 * n * e ^ 2) + exp (-2 * n * e ^ 2) := add_le_add up dn
    _ = 2 * exp (-2 * n * e ^ 2) := by ring

end Hoeffding

section SampleSize

/-- A computable test on rationals: `2 ≤ δ * (1 + 2 n e² / k) ^ k`. -/
def sampleSizeOK (e δ : ℚ) (k n : ℕ) : Bool :=
  decide (2 ≤ δ * (1 + 2 * n * e ^ 2 / k) ^ k)

/-- The least `n < bound` passing `sampleSizeOK e δ k`, if there is one. -/
def minSampleSize (e δ : ℚ) (k bound : ℕ) : Option ℕ :=
  (List.range bound).find? (fun n ↦ sampleSizeOK e δ k n)

/-- `(1 + y / k) ^ k ≤ exp y` for `0 ≤ y` and `0 < k`. -/
theorem one_add_div_pow_le_exp {y : ℝ} (hy : 0 ≤ y) {k : ℕ} (hk : 0 < k) :
    (1 + y / k) ^ k ≤ exp y := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  calc (1 + y / k) ^ k ≤ (exp (y / k)) ^ k := by
        apply pow_le_pow_left₀ (by positivity)
        linarith [add_one_le_exp (y / k)]
    _ = exp y := by rw [← exp_nat_mul]; congr 1; field_simp

/-- **The sample-size test is sufficient.** If `2 ≤ δ (1 + 2 n e² / k) ^ k` then
`2 exp (-2 n e²) ≤ δ`. -/
theorem two_mul_exp_neg_le_of_le {n k : ℕ} (hk : 0 < k) {e δ : ℝ}
    (h : 2 ≤ δ * (1 + 2 * n * e ^ 2 / k) ^ k) : 2 * exp (-2 * n * e ^ 2) ≤ δ := by
  have hy : 0 ≤ 2 * (n : ℝ) * e ^ 2 := by positivity
  have hpow := one_add_div_pow_le_exp hy hk
  have hδ : 0 ≤ δ := by
    by_contra hneg
    push Not at hneg
    have : δ * (1 + 2 * n * e ^ 2 / k) ^ k ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg.le (by positivity)
    linarith
  have h2 : 2 ≤ δ * exp (2 * n * e ^ 2) := h.trans (mul_le_mul_of_nonneg_left hpow hδ)
  have hpos := exp_pos (2 * (n : ℝ) * e ^ 2)
  have hinv : exp (-2 * n * e ^ 2) * exp (2 * n * e ^ 2) = 1 := by
    rw [← exp_add]; ring_nf; exact exp_zero
  nlinarith [exp_pos (-2 * (n : ℝ) * e ^ 2)]

/-- `sampleSizeOK` on rationals gives the real inequality. -/
theorem two_mul_exp_neg_le_of_sampleSizeOK {e δ : ℚ} {k n : ℕ} (hk : 0 < k)
    (h : sampleSizeOK e δ k n = true) : 2 * exp (-2 * n * (e : ℝ) ^ 2) ≤ δ := by
  apply two_mul_exp_neg_le_of_le hk
  have h' : (2 : ℚ) ≤ δ * (1 + 2 * n * e ^ 2 / k) ^ k := by
    simpa [sampleSizeOK] using h
  exact_mod_cast h'

/-- **Trusting an observed rate.** If `sampleSizeOK e δ k n` holds, the mean of `n` independent
`[0, 1]`-valued variables with common mean `p` is within `e` of `p` except with probability at
most `δ`. -/
theorem measureReal_abs_sampleMean_sub_ge_le_of_sampleSizeOK {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i)) (h_bdd : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    {p : ℝ} (h_mean : ∀ i, μ[X i] = p) {e δ : ℚ} (he : 0 ≤ e) {k n : ℕ} (hk : 0 < k)
    (hn : 0 < n) (h : sampleSizeOK e δ k n = true) :
    μ.real {ω | (e : ℝ) ≤ |(∑ i ∈ range n, X i ω) / n - p|} ≤ δ :=
  (measureReal_abs_sampleMean_sub_ge_le h_indep h_meas h_bdd h_mean hn (by exact_mod_cast he)).trans
    (two_mul_exp_neg_le_of_sampleSizeOK hk h)

end SampleSize


end ClassicalLean.Probability.SampleMean
