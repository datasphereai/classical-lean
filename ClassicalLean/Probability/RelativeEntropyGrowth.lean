/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import ClassicalLean.InformationTheory.Channel

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

Order LEAN-21 (item 39 of the plan) adds the link to the library's `relEntropy` for finite measures
of any total mass:

* `toReal_klDiv_eq_relEntropy`: for finite measures `μ`, `ν` on a finite type with `μ {i} = 0`
  wherever `ν {i} = 0`, `(klDiv μ ν).toReal = relEntropy μ ν + ν(univ) − μ(univ)`.
* `vecMeasure p`, the measure with mass `p i` at each point, and `toReal_klDiv_vecMeasure`: for
  `p, q ≥ 0` with `p i = 0` wherever `q i = 0`,
  `(klDiv (vecMeasure p) (vecMeasure q)).toReal = relEntropy p q + ∑ q − ∑ p`.
* `relEntropy_vecMul_le_of_klDiv`: the library's data-processing inequality
  (`ClassicalLean.Simplex.relEntropy_vecMul_le`, proved directly in InformationTheory.Channel)
  follows again from Mathlib's `klDiv_comp_right_le`, with the matrix as a Markov kernel.

Measured in order LEAN-21's checks (check C39, floating point, margin `1e-9`): 2000 random `p`, `q`
with support and stochastic `W`: data processing holds, and `relEntropy + ∑ q − ∑ p ≥ 0` (so
Mathlib's `ENNReal.ofReal` does not cut it off). Each hypothesis is needed: drop it alone and the
conclusion fails at:

* the support condition: `p = (1)`, `q = (0)`: Lean's `toReal` of `klDiv = ∞` is `0`, the right
  side `−1`; in data processing, `p = (1, 1)`, `q = (0, 2)`, `W` all `1/2`: `0 > −0.693`.
* `p ≥ 0`: `p = (−1)`, `q = (1)`: `vecMeasure p = 0` and `klDiv 0 ν = ν(univ) = 1`, the right
  side `2`; in data processing, `p = (−1, 0)`, `q = (1, 1)`, `W` all `1/2`: `0.693 > 0`
  (review r39).
* rows of `W` sum to `1`: `W = 2 · 1`, `p = (1, 0)`, `q = (1/2, 1/2)`: `1.386 > 0.693`.
* `q ≥ 0`: `p = (0)`, `q = (−1)`: `vecMeasure q = 0` and `klDiv 0 0 = 0`, the right side `−1`; in
  data processing, a `2 × 2` case found by random search is printed in the check output.
* entries of `W` at least `0` (a random search with rows summing to `1`): a `2 × 2` case is
  printed in the check output.

## What Mathlib provides

`InformationTheory.klDiv` with Gibbs' inequality (`integral_llr_add_sub_measure_univ_nonneg`) and
`klDiv_eq_zero_iff`; `Measure.setLIntegral_rnDeriv`, `lintegral_singleton`, `integral_fintype`,
`Real.log_le_sub_one_of_pos`. The finite sums here are proved directly, and `toReal_klDiv_eq_sum`
links them to Mathlib's definition. For item 39: `toReal_klDiv`, `klDiv_ne_top`,
`klDiv_comp_right_le`, `Kernel.ofFunOfCountable`, `Measure.bind_apply`. Searched before item 39 was
written (order LEAN-21, `grep -rniE` over Mathlib): `relEntropy|relative entropy` 0 lines;
`klDiv.*(sum|finite|Fintype|count)|toReal_klDiv|klDiv_comp_right_le|klDiv.*dirac` 34 lines in 2
files, all statements about measures in general (no finite-sum form).
-/

open Finset Real MeasureTheory InformationTheory ProbabilityTheory
open scoped Matrix

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

/-- On a finite set, a measure is absolutely continuous with respect to another when every point
the second gives mass `0` has mass `0` under the first. -/
private theorem absolutelyContinuous_of_singleton {γ : Type*} [MeasurableSpace γ] [Finite γ]
    {μ ν : Measure γ} (h : ∀ i, ν {i} = 0 → μ {i} = 0) : μ ≪ ν := by
  intro s hs
  have hi : ∀ i ∈ s, μ {i} = 0 := fun i hi ↦
    h i (measure_mono_null (Set.singleton_subset_iff.mpr hi) hs)
  rw [← Set.biUnion_of_singleton s]
  exact (measure_biUnion_null_iff (Set.toFinite s).countable).mpr hi

/-- **Mathlib's relative entropy on a finite set, for finite measures.** For finite measures `μ`
and `ν` on a finite type, with `μ {i} = 0` wherever `ν {i} = 0`:
`(klDiv μ ν).toReal = relEntropy μ ν + ν(univ) − μ(univ)`, the library's sum
`∑ i, μ {i} log (μ {i} / ν {i})` plus the difference of the total masses. -/
theorem toReal_klDiv_eq_relEntropy (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ i, ν {i} = 0 → μ {i} = 0) :
    (klDiv μ ν).toReal = ClassicalLean.Simplex.relEntropy (fun i ↦ μ.real {i})
      (fun i ↦ ν.real {i}) + ν.real Set.univ - μ.real Set.univ := by
  have hac := absolutelyContinuous_of_singleton h
  rw [toReal_klDiv hac Integrable.of_finite, integral_fintype Integrable.of_finite]
  congr 2
  refine sum_congr rfl fun i _ ↦ ?_
  by_cases hν : ν {i} = 0
  · simp [measureReal_def, h i hν]
  · have hrn : μ.rnDeriv ν i * ν {i} = μ {i} := by
      rw [← lintegral_singleton, Measure.setLIntegral_rnDeriv hac]
    have hrn' : μ.rnDeriv ν i = μ {i} / ν {i} :=
      (ENNReal.eq_div_iff hν (measure_ne_top ν _)).mpr (by rw [mul_comm, hrn])
    rw [smul_eq_mul, llr_def]
    simp only [hrn', ENNReal.toReal_div, measureReal_def]

/-- The measure on a finite set with mass `p i` at each point `i` (mass `0` where `p i < 0`). -/
noncomputable def vecMeasure (p : α → ℝ) : Measure α :=
  ∑ i, ENNReal.ofReal (p i) • Measure.dirac i

theorem vecMeasure_singleton (p : α → ℝ) (i : α) : vecMeasure p {i} = ENNReal.ofReal (p i) := by
  classical
  rw [vecMeasure, Measure.finsetSum_apply, sum_eq_single i]
  · simp
  · intro j _ hj
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [Measure.dirac_apply' _ (measurableSet_singleton i),
      Set.indicator_of_notMem (show j ∉ ({i} : Set α) from hj), mul_zero]
  · simp

instance (p : α → ℝ) : IsFiniteMeasure (vecMeasure p) :=
  ⟨by
    rw [vecMeasure, Measure.finsetSum_apply]
    exact ENNReal.sum_lt_top.mpr fun i _ ↦ by simp⟩

theorem measureReal_vecMeasure_singleton {p : α → ℝ} (hp : ∀ i, 0 ≤ p i) (i : α) :
    (vecMeasure p).real {i} = p i := by
  rw [measureReal_def, vecMeasure_singleton, ENNReal.toReal_ofReal (hp i)]

theorem measureReal_vecMeasure_univ {p : α → ℝ} (hp : ∀ i, 0 ≤ p i) :
    (vecMeasure p).real Set.univ = ∑ i, p i := by
  rw [← Finset.coe_univ, ← sum_measureReal_singleton]
  exact sum_congr rfl fun i _ ↦ measureReal_vecMeasure_singleton hp i

/-- **The plan's form.** For `p, q ≥ 0` with `p i = 0` wherever `q i = 0`, Mathlib's `klDiv` between
the measures with these masses is `relEntropy p q + ∑ q − ∑ p`. -/
theorem toReal_klDiv_vecMeasure {p q : α → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpq : ∀ i, q i = 0 → p i = 0) :
    (klDiv (vecMeasure p) (vecMeasure q)).toReal =
      ClassicalLean.Simplex.relEntropy p q + ∑ i, q i - ∑ i, p i := by
  rw [toReal_klDiv_eq_relEntropy _ _ fun i hi ↦ ?_, measureReal_vecMeasure_univ hp,
    measureReal_vecMeasure_univ hq]
  · simp only [measureReal_vecMeasure_singleton hp, measureReal_vecMeasure_singleton hq]
  · rw [vecMeasure_singleton, ENNReal.ofReal_eq_zero] at hi ⊢
    exact (hpq i (le_antisymm hi (hq i))).le

/-- **Data processing for relative entropy, from Mathlib's.** For `p, q ≥ 0` with `p i = 0`
wherever `q i = 0`, and a matrix `W` with entries at least `0` and rows summing to `1`,
`relEntropy (p W) (q W) ≤ relEntropy p q`. The library proves this directly
(`ClassicalLean.Simplex.relEntropy_vecMul_le`); this theorem repeats that statement by another
route, from Mathlib's `klDiv_comp_right_le` through `toReal_klDiv_vecMeasure`. The measurable
structures on `α` and `β` are needed only by that route; the statement does not use them. -/
theorem relEntropy_vecMul_le_of_klDiv {β : Type*} [Fintype β] [MeasurableSpace β]
    [MeasurableSingletonClass β] {p q : α → ℝ} {W : Matrix α β ℝ} (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i) (hpq : ∀ i, q i = 0 → p i = 0) (hW0 : ∀ i j, 0 ≤ W i j)
    (hW1 : ∀ i, ∑ j, W i j = 1) :
    ClassicalLean.Simplex.relEntropy (p ᵥ* W) (q ᵥ* W) ≤ ClassicalLean.Simplex.relEntropy p q := by
  classical
  let κ : Kernel α β := Kernel.ofFunOfCountable fun i ↦ vecMeasure (W i)
  have hκ : IsMarkovKernel κ := ⟨fun i ↦ ⟨by
    change vecMeasure (W i) Set.univ = 1
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    change ENNReal.ofReal ((vecMeasure (W i)).real Set.univ) = 1
    rw [measureReal_vecMeasure_univ (hW0 i), hW1 i, ENNReal.ofReal_one]⟩⟩
  have hcomp : ∀ r : α → ℝ, (∀ i, 0 ≤ r i) → κ ∘ₘ vecMeasure r = vecMeasure (r ᵥ* W) := by
    intro r hr
    refine Measure.ext_of_singleton fun j ↦ ?_
    rw [Measure.bind_apply (measurableSet_singleton j) κ.aemeasurable, lintegral_fintype,
      vecMeasure_singleton, Matrix.vecMul_apply_eq_sum,
      ENNReal.ofReal_sum_of_nonneg fun i _ ↦ mul_nonneg (hr i) (hW0 i j)]
    refine sum_congr rfl fun i _ ↦ ?_
    change vecMeasure (W i) {j} * vecMeasure r {i} = _
    rw [vecMeasure_singleton, vecMeasure_singleton, ← ENNReal.ofReal_mul (hW0 i j), mul_comm]
  have hle := klDiv_comp_right_le (vecMeasure p) (vecMeasure q) κ
  rw [hcomp p hp, hcomp q hq] at hle
  have hac : vecMeasure p ≪ vecMeasure q := absolutelyContinuous_of_singleton fun i hi ↦ by
    rw [vecMeasure_singleton, ENNReal.ofReal_eq_zero] at hi ⊢
    exact (hpq i (le_antisymm hi (hq i))).le
  have hfin := klDiv_ne_top hac Integrable.of_finite
  have hmono := ENNReal.toReal_mono hfin hle
  have hpW := ClassicalLean.Simplex.vecMul_nonneg hW0 hp
  have hqW := ClassicalLean.Simplex.vecMul_nonneg hW0 hq
  have hsupp : ∀ j, (q ᵥ* W) j = 0 → (p ᵥ* W) j = 0 := by
    intro j hj
    rw [Matrix.vecMul_apply_eq_sum] at hj ⊢
    have hz := (sum_eq_zero_iff_of_nonneg fun i _ ↦ mul_nonneg (hq i) (hW0 i j)).mp hj
    refine sum_eq_zero fun i hi ↦ ?_
    rcases mul_eq_zero.mp (hz i hi) with h | h
    · rw [hpq i h, zero_mul]
    · rw [h, mul_zero]
  rw [toReal_klDiv_vecMeasure hpW hqW hsupp, toReal_klDiv_vecMeasure hp hq hpq,
    ClassicalLean.Simplex.sum_vecMul_eq_sum hW1, ClassicalLean.Simplex.sum_vecMul_eq_sum hW1]
    at hmono
  linarith

end Measures

end ClassicalLean.Probability.RelativeEntropyGrowth
