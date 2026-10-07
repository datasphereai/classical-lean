/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Log growth of a split stake, and relative entropy

One of finitely many outcomes `i` happens, with chance `p i`. All of a stake is split: the share
`b i` goes on outcome `i`, which pays `o i` per unit if `i` happens. The expected log growth is
`growth p b o = ∑ i, p i * log (b i * o i)`.

* `growth_sub_growth_eq`: `growth p p o - growth p b o = ∑ i, p i * log (p i / b i)`, the relative
  entropy `D(p ‖ b)`; the payouts cancel.
* `toReal_klDiv_eq_sum`: for probability measures on a finite type with `ν {i} ≠ 0`, Mathlib's
  `InformationTheory.klDiv μ ν` is that sum. So `growth_sub_growth_eq_toReal_klDiv`: the growth lost
  by splitting by `ν` when the chances are `μ` is exactly `klDiv μ ν`.
* `sum_mul_log_div_nonneg` (Gibbs' inequality, finite form), `growth_le_growth_self`: splitting in
  proportion to the true chances gives the most growth, and `growth_eq_growth_self_iff`: only it.
* `growth_inv_eq`: with payouts `1 / r i`, `growth p b (1 / r) = D(p ‖ r) - D(p ‖ b)`.

## What Mathlib provides

`InformationTheory.klDiv` with Gibbs' inequality (`integral_llr_add_sub_measure_univ_nonneg`) and
`klDiv_eq_zero_iff`; `Measure.setLIntegral_rnDeriv`, `lintegral_singleton`, `integral_fintype`,
`Real.log_le_sub_one_of_pos`. The finite sums here are proved directly, and `toReal_klDiv_eq_sum`
links them to Mathlib's definition.
-/

open Finset Real MeasureTheory InformationTheory

namespace ClassicalLean.Probability.RelativeEntropyGrowth

variable {α : Type*} [Fintype α]

/-- Expected log growth when the share `b i` of a stake goes on outcome `i`, which happens with
chance `p i` and pays `o i` per unit staked. -/
noncomputable def growth (p b o : α → ℝ) : ℝ := ∑ i, p i * log (b i * o i)

/-- **The growth lost by a wrong split is the relative entropy.** For nonzero shares and payouts,
`growth p p o - growth p b o = ∑ i, p i * log (p i / b i)`. For a trader: splitting by beliefs `b`
instead of the true chances `p` costs exactly `D(p ‖ b)` of log growth per round, whatever the
payouts are. -/
theorem growth_sub_growth_eq (p b o : α → ℝ) (hb : ∀ i, b i ≠ 0) (ho : ∀ i, o i ≠ 0) :
    growth p p o - growth p b o = ∑ i, p i * log (p i / b i) := by
  unfold growth
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rcases eq_or_ne (p i) 0 with h | h
  · simp [h]
  · rw [← mul_sub, log_mul h (ho i), log_mul (hb i) (ho i), log_div h (hb i)]
    ring

/-- One term of Gibbs' inequality: `p - b ≤ p log (p / b)` for `p ≥ 0`, `b > 0`. -/
theorem sub_le_mul_log_div {p b : ℝ} (hp : 0 ≤ p) (hb : 0 < b) : p - b ≤ p * log (p / b) := by
  rcases hp.eq_or_lt with h | h
  · rw [← h]; simp [hb.le]
  · have hl := log_le_sub_one_of_pos (div_pos hb h)
    have e : log (p / b) = -log (b / p) := by
      rw [log_div h.ne' hb.ne', log_div hb.ne' h.ne']; ring
    have : p * (b / p - 1) = b - p := by field_simp
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hl h.le]

/-- The term is strict unless `b = p`: `p - b < p log (p / b)` for `p > 0`, `b > 0`, `b ≠ p`. -/
theorem sub_lt_mul_log_div {p b : ℝ} (hp : 0 < p) (hb : 0 < b) (hne : b ≠ p) :
    p - b < p * log (p / b) := by
  have hx : b / p ≠ 1 := fun h1 ↦ hne (by field_simp at h1; linarith)
  have hl := log_lt_sub_one_of_pos (div_pos hb hp) hx
  have e : log (p / b) = -log (b / p) := by
    rw [log_div hp.ne' hb.ne', log_div hb.ne' hp.ne']; ring
  have : p * (b / p - 1) = b - p := by field_simp
  rw [e]
  nlinarith [mul_lt_mul_of_pos_left hl hp]

/-- **Gibbs' inequality, finite form.** For `p i ≥ 0`, `b i > 0` and `∑ b ≤ ∑ p`:
`0 ≤ ∑ i, p i * log (p i / b i)`. -/
theorem sum_mul_log_div_nonneg {p b : α → ℝ} (hp : ∀ i, 0 ≤ p i) (hb : ∀ i, 0 < b i)
    (hsum : ∑ i, b i ≤ ∑ i, p i) : 0 ≤ ∑ i, p i * log (p i / b i) := by
  have key : ∀ i, p i - b i ≤ p i * log (p i / b i) := fun i ↦ sub_le_mul_log_div (hp i) (hb i)
  calc (0 : ℝ) ≤ ∑ i, (p i - b i) := by rw [sum_sub_distrib]; linarith
    _ ≤ _ := sum_le_sum fun i _ ↦ key i

/-- **Splitting by the true chances is best.** For chances `p i ≥ 0` and shares `b i > 0` with
`∑ b ≤ ∑ p`, and nonzero payouts: `growth p b o ≤ growth p p o`. For a trader: no split of the
whole stake grows faster on average than the split in proportion to the true chances. -/
theorem growth_le_growth_self {p b o : α → ℝ} (hp : ∀ i, 0 ≤ p i) (hb : ∀ i, 0 < b i)
    (hsum : ∑ i, b i ≤ ∑ i, p i) (ho : ∀ i, o i ≠ 0) : growth p b o ≤ growth p p o := by
  have := growth_sub_growth_eq p b o (fun i ↦ (hb i).ne') ho
  have := sum_mul_log_div_nonneg hp hb hsum
  linarith

/-- **Only the true chances are best.** For chances `p i ≥ 0` and shares `b i > 0` with the same
total, and nonzero payouts: `growth p b o = growth p p o` exactly when `b = p`. For a trader: any
other split of the stake grows strictly slower on average. -/
theorem growth_eq_growth_self_iff {p b o : α → ℝ} (hp : ∀ i, 0 ≤ p i) (hb : ∀ i, 0 < b i)
    (hsum : ∑ i, b i = ∑ i, p i) (ho : ∀ i, o i ≠ 0) : growth p b o = growth p p o ↔ b = p := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have hD := growth_sub_growth_eq p b o (fun i ↦ (hb i).ne') ho
  rw [h, sub_self] at hD
  set T : α → ℝ := fun i ↦ p i * log (p i / b i) - (p i - b i) with hT
  have hTnn : ∀ i, 0 ≤ T i := fun i ↦ by
    simp only [hT]; linarith [sub_le_mul_log_div (hp i) (hb i)]
  have hsumT : ∑ i, T i = 0 := by
    simp only [hT, sum_sub_distrib, ← hD, hsum, sub_self]
  rw [sum_eq_zero_iff_of_nonneg fun i _ ↦ hTnn i] at hsumT
  funext i
  have hTi := hsumT i (mem_univ i)
  simp only [hT] at hTi
  rcases (hp i).eq_or_lt with h0 | h0
  · rw [← h0] at hTi; simp at hTi; linarith [hb i]
  · by_contra hne
    linarith [sub_lt_mul_log_div h0 (hb i) hne]

/-- **Payouts set by other chances.** With payouts `o i = 1 / r i` for nonzero `r i` and nonzero
shares: `growth p b (1 / r) = ∑ p log (p / r) - ∑ p log (p / b)`, that is `D(p ‖ r) - D(p ‖ b)`.
For a trader: against payouts set by chances `r`, the average log growth is how much closer the
split `b` is to the truth than `r` is. -/
theorem growth_inv_eq (p b r : α → ℝ) (hb : ∀ i, b i ≠ 0) (hr : ∀ i, r i ≠ 0) :
    growth p b (fun i ↦ 1 / r i) =
      ∑ i, p i * log (p i / r i) - ∑ i, p i * log (p i / b i) := by
  unfold growth
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rcases eq_or_ne (p i) 0 with h | h
  · simp [h]
  · rw [← mul_sub, mul_one_div, log_div (hb i) (hr i), log_div h (hr i), log_div h (hb i)]
    ring

section Measures

variable [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **Mathlib's relative entropy on a finite set is the finite sum.** For probability measures `μ`
and `ν` on a finite type with `ν {i} ≠ 0` for every `i`:
`(klDiv μ ν).toReal = ∑ i, μ {i} * log (μ {i} / ν {i})`. -/
theorem toReal_klDiv_eq_sum (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ∀ i, ν {i} ≠ 0) :
    (klDiv μ ν).toReal = ∑ i, μ.real {i} * log (μ.real {i} / ν.real {i}) := by
  have hac : μ ≪ ν := by
    intro s hs
    have : s = ∅ := Set.eq_empty_of_forall_notMem fun i hi ↦
      hν i (measure_mono_null (Set.singleton_subset_iff.mpr hi) hs)
    simp [this]
  rw [toReal_klDiv_of_measure_eq hac (by simp), integral_fintype (Integrable.of_finite)]
  refine sum_congr rfl fun i _ ↦ ?_
  have hrn : μ.rnDeriv ν i * ν {i} = μ {i} := by
    rw [← lintegral_singleton, Measure.setLIntegral_rnDeriv hac]
  have hrn' : μ.rnDeriv ν i = μ {i} / ν {i} :=
    (ENNReal.eq_div_iff (hν i) (measure_ne_top ν _)).mpr (by rw [mul_comm, hrn])
  rw [smul_eq_mul, llr_def]
  simp only [hrn', ENNReal.toReal_div, measureReal_def]

/-- **The growth lost by a wrong split is Mathlib's `klDiv`.** For probability measures `μ` (the
true chances) and `ν` (the split) on a finite set of outcomes, with `ν {i} ≠ 0`, and nonzero
payouts: `growth μ μ o - growth μ ν o = (klDiv μ ν).toReal`. -/
theorem growth_sub_growth_eq_toReal_klDiv (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hν : ∀ i, ν {i} ≠ 0) (o : α → ℝ) (ho : ∀ i, o i ≠ 0) :
    growth (fun i ↦ μ.real {i}) (fun i ↦ μ.real {i}) o -
        growth (fun i ↦ μ.real {i}) (fun i ↦ ν.real {i}) o = (klDiv μ ν).toReal := by
  rw [toReal_klDiv_eq_sum μ ν hν, growth_sub_growth_eq _ _ o _ ho]
  intro i
  rw [measureReal_def, ENNReal.toReal_ne_zero]
  exact ⟨hν i, measure_ne_top ν _⟩

end Measures

end ClassicalLean.Probability.RelativeEntropyGrowth
