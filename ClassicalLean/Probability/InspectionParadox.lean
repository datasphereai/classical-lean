/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Chebyshev

/-!
# The inspection paradox, finite form

Lay gaps of lengths `L 0, …, L (k − 1)` end to end on the line, from `0` to `S = ∑ L i`. Gap `i`
is the interval `[start i, start i + L i)`, where `start i = L 0 + ⋯ + L (i − 1)`. Pick a point
at random, uniformly on `[0, S)`, and look at the length of the gap it lands in. The mean of that
length is `∑ L i² / ∑ L i`, which is at least the plain mean `∑ L i / k` of the gaps, with
equality only when all gaps are equal. Long gaps cover more of the line, so a point picked at
random lands in them more often: durations measured by sampling at random moments (holding
times, time between events) come out too long. Order LEAN-26, item 71 of the plan.

"Chosen uniformly at random" is the law `volume[|Set.Ico 0 S]`: Lebesgue measure on `[0, S)`,
divided by `S` (Mathlib's `ProbabilityTheory.cond`).

* `sum_sq_div_sum_ge_mean`: `∑ L i / k ≤ ∑ L i² / ∑ L i` whenever `∑ L i ≥ 0`.
* `sum_sq_div_sum_eq_mean_iff`: when `∑ L i > 0`, equality holds exactly when all `k` gaps are
  equal.
* `exists_mem_gap`: the gaps cover `[0, S)` (for any lengths).
* `gap_disjoint`, `gapLength_eq_of_mem`: for gaps of length `≥ 0`, the gaps do not overlap, and
  `gapLength L k x` is the length of the gap holding `x`.
* `measureReal_gap`: the chance of landing in gap `i` is `L i / S`.
* `integral_gapLength`: the mean length of the gap the point lands in is `∑ L i² / ∑ L i`.
* `mean_le_integral_gapLength`: so that mean length is at least the plain mean `∑ L i / k`
  (review r71 of order LEAN-26).

The plan asks for gaps `L i > 0`. Less is used: the inequality needs only `∑ L i ≥ 0` (negative
gaps are allowed, as long as the total is `≥ 0`), and the measure statements need `L i ≥ 0`
(`exists_mem_gap` needs nothing). Each hypothesis is needed (order LEAN-26's checks, lines I1 to
I9, exact; review r71 for `gap_disjoint`):

* `∑ L i ≥ 0` for the inequality: `L = (−1, −2)` has plain mean `−3/2` and `∑ L² / ∑ L = −5/3`.
* `∑ L i > 0` for the equality case: `L = (1, −1)` gives `0 = 0` on both sides (Lean's
  `x / 0 = 0`), and the gaps differ.
* `L i ≥ 0` for `gap_disjoint`: `L = (2, −1, 1)` puts gap `0` at `[0, 2)` and gap `2` at
  `[1, 2)`, which overlap.
* `L i ≥ 0` for the measure statements: `L = (2, −1)`, `S = 1`: gap `0` is `[0, 2)` and gap `1`
  is empty, so the chance of gap `0` is `1`, not `L 0 / S = 2`, and the mean length is `2`, not
  `5`.

With no gaps (`k = 0`), or with every gap of length `0`, both sides are Lean's `0`: the law on an
empty interval is the zero measure, and `0 / 0 = 0`.

## What Mathlib provides

`sq_sum_le_card_mul_sum_sq` (Cauchy–Schwarz for a finite sum), `ProbabilityTheory.cond` and
`cond_apply`, `Real.volume_Ico`, `integral_indicator_const` and `integral_finsetSum`. Mathlib
v4.34.0 has no inspection paradox: `inspection paradox|length.biased|size.biased|renewal` gives no
hits (order LEAN-26's search).
-/

open MeasureTheory ProbabilityTheory Finset

namespace ClassicalLean.Probability.InspectionParadox

variable {k : ℕ} {L : ℕ → ℝ}

/-- **The inspection paradox, as an inequality.** The mean `∑ L i² / ∑ L i` of the gap a random
point lands in is at least the plain mean `∑ L i / k`, whenever `∑ L i ≥ 0`. -/
theorem sum_sq_div_sum_ge_mean (L : ℕ → ℝ) (k : ℕ) (hL : 0 ≤ ∑ i ∈ range k, L i) :
    (∑ i ∈ range k, L i) / k ≤ (∑ i ∈ range k, L i ^ 2) / ∑ i ∈ range k, L i := by
  rcases hL.eq_or_lt with h | h
  · rw [← h]; simp
  have hk : (0 : ℝ) < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at h
    · exact_mod_cast hk
  rw [div_le_div_iff₀ hk h]
  have := sq_sum_le_card_mul_sum_sq (s := range k) (f := L)
  simp only [card_range] at this
  nlinarith [this]

/-- **When the two means agree.** If `∑ L i > 0`, the two means are equal exactly when all `k`
gaps are equal. -/
theorem sum_sq_div_sum_eq_mean_iff (L : ℕ → ℝ) (k : ℕ) (hL : 0 < ∑ i ∈ range k, L i) :
    (∑ i ∈ range k, L i ^ 2) / (∑ i ∈ range k, L i) = (∑ i ∈ range k, L i) / k ↔
      ∀ i < k, ∀ j < k, L i = L j := by
  set S := ∑ i ∈ range k, L i with hS
  have hk : (0 : ℝ) < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [S] at hL
    · exact_mod_cast hk
  set m := S / k with hm
  have hdev : ∑ i ∈ range k, (L i - m) ^ 2 = ∑ i ∈ range k, L i ^ 2 - S ^ 2 / k := by
    have e : ∀ i, (L i - m) ^ 2 = L i ^ 2 - 2 * m * L i + m ^ 2 := fun i ↦ by ring
    simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_range,
      nsmul_eq_mul]
    simp only [m]; field_simp; ring
  constructor
  · intro h
    have h2 : ∑ i ∈ range k, L i ^ 2 = S ^ 2 / k := by
      rw [div_eq_div_iff hL.ne' hk.ne'] at h; field_simp; nlinarith [h]
    have h0 : ∑ i ∈ range k, (L i - m) ^ 2 = 0 := by rw [hdev, h2, sub_self]
    have hall := (sum_eq_zero_iff_of_nonneg fun i _ ↦ sq_nonneg (L i - m)).mp h0
    have hm : ∀ i < k, L i = m := fun i hi ↦ by
      have := hall i (mem_range.mpr hi); nlinarith [sq_nonneg (L i - m)]
    intro i hi j hj; rw [hm i hi, hm j hj]
  · intro h
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := Nat.exists_eq_succ_of_ne_zero (by rintro rfl; simp at hk)
    have hc : ∀ i ∈ range (k' + 1), L i = L 0 := fun i hi ↦
      h i (mem_range.mp hi) 0 (Nat.succ_pos _)
    have hS' : S = (k' + 1) * L 0 := by
      rw [hS, sum_congr rfl hc]; simp
    have hQ : ∑ i ∈ range (k' + 1), L i ^ 2 = (k' + 1) * L 0 ^ 2 := by
      rw [sum_congr rfl fun i hi ↦ by rw [hc i hi]]; simp
    have hL0 : L 0 ≠ 0 := by rintro h0; rw [hS', h0, mul_zero] at hL; exact lt_irrefl _ hL
    rw [hm, hQ, hS']; push_cast; field_simp

/-- Where gap `i` starts: the total length of the gaps before it. -/
def start (L : ℕ → ℝ) (i : ℕ) : ℝ := ∑ j ∈ range i, L j

/-- Gap `i`, the interval `[start i, start i + L i)`. -/
def gap (L : ℕ → ℝ) (i : ℕ) : Set ℝ := Set.Ico (start L i) (start L i + L i)

/-- The length of the gap among the first `k` that holds the point `x` (`0` outside them). -/
noncomputable def gapLength (L : ℕ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ range k, (gap L i).indicator (fun _ ↦ L i) x

/-- The next gap starts where gap `i` ends. -/
lemma start_succ (L : ℕ → ℝ) (i : ℕ) : start L (i + 1) = start L i + L i := sum_range_succ _ _

lemma start_mono (hL : ∀ i < k, 0 ≤ L i) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ k) :
    start L i ≤ start L j :=
  sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hij) fun m hm _ ↦
    hL m (lt_of_lt_of_le (mem_range.mp hm) hj)

lemma start_nonneg (hL : ∀ i < k, 0 ≤ L i) {i : ℕ} (hi : i ≤ k) : 0 ≤ start L i := by
  simpa [start] using start_mono hL (Nat.zero_le i) hi

lemma gap_subset (hL : ∀ i < k, 0 ≤ L i) {i : ℕ} (hi : i < k) :
    gap L i ⊆ Set.Ico 0 (∑ j ∈ range k, L j) := by
  intro x ⟨h1, h2⟩
  refine ⟨(start_nonneg hL hi.le).trans h1, h2.trans_le ?_⟩
  rw [← start_succ]; exact start_mono hL hi le_rfl

lemma measurableSet_gap (L : ℕ → ℝ) (i : ℕ) : MeasurableSet (gap L i) := measurableSet_Ico

/-- **The gaps do not overlap**, when their lengths are `≥ 0`. -/
theorem gap_disjoint (hL : ∀ i < k, 0 ≤ L i) {i j : ℕ} (hi : i < k) (hj : j < k) (hij : i ≠ j) :
    Disjoint (gap L i) (gap L j) := by
  wlog h : i < j generalizing i j
  · exact (this hj hi (Ne.symm hij) (lt_of_le_of_ne (not_lt.mp h) (Ne.symm hij))).symm
  rw [gap, gap, Set.Ico_disjoint_Ico]
  have : start L i + L i ≤ start L j := by rw [← start_succ]; exact start_mono hL h hj.le
  exact (min_le_left _ _).trans (this.trans (le_max_right _ _))

/-- **`gapLength` is the length of the gap holding `x`.** -/
theorem gapLength_eq_of_mem (hL : ∀ i < k, 0 ≤ L i) {i : ℕ} (hi : i < k) {x : ℝ}
    (hx : x ∈ gap L i) : gapLength L k x = L i := by
  rw [gapLength, sum_eq_single_of_mem i (mem_range.mpr hi), Set.indicator_of_mem hx]
  intro j hj hji
  exact Set.indicator_of_notMem (Set.disjoint_left.mp
    (gap_disjoint hL hi (mem_range.mp hj) (Ne.symm hji)) hx) _

/-- **The gaps cover `[0, S)`**, whatever the signs of the lengths. -/
theorem exists_mem_gap {x : ℝ}
    (hx : x ∈ Set.Ico 0 (∑ i ∈ range k, L i)) : ∃ i < k, x ∈ gap L i := by
  induction k with
  | zero => simp at hx
  | succ k ih =>
    by_cases h : x < ∑ i ∈ range k, L i
    · obtain ⟨i, hi, hm⟩ := ih ⟨hx.1, h⟩
      exact ⟨i, by omega, hm⟩
    · refine ⟨k, by omega, not_lt.mp h, ?_⟩
      have := hx.2; rw [sum_range_succ] at this; exact this

/-- **The chance of landing in gap `i`** is `L i / S`, for a point uniform on `[0, S)`. -/
theorem measureReal_gap (hL : ∀ i < k, 0 ≤ L i) {i : ℕ} (hi : i < k) :
    (volume[|Set.Ico 0 (∑ j ∈ range k, L j)]).real (gap L i) = L i / ∑ j ∈ range k, L j := by
  rw [measureReal_def, cond_apply measurableSet_Ico, Set.inter_eq_right.mpr (gap_subset hL hi),
    gap, Real.volume_Ico, Real.volume_Ico, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by
      have := start_nonneg hL (le_refl k); simp only [start] at this; simpa using this),
    ENNReal.toReal_ofReal (by simp [hL i hi])]
  simp [div_eq_inv_mul]

/-- **The inspection paradox.** For a point uniform on `[0, S)`, the mean length of the gap it
lands in is `∑ L i² / ∑ L i`. -/
theorem integral_gapLength (hL : ∀ i < k, 0 ≤ L i) :
    ∫ x, gapLength L k x ∂(volume[|Set.Ico 0 (∑ j ∈ range k, L j)]) =
      (∑ i ∈ range k, L i ^ 2) / ∑ i ∈ range k, L i := by
  unfold gapLength
  rw [integral_finsetSum _ fun i _ ↦ (integrable_const (L i)).indicator (measurableSet_gap L i)]
  rw [sum_div]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [integral_indicator_const _ (measurableSet_gap L i), measureReal_gap hL (mem_range.mp hi),
    smul_eq_mul]
  ring

/-- **The inspection paradox, in one statement.** For a point uniform on `[0, S)`, the mean length
of the gap it lands in is at least the plain mean `∑ L i / k` of the gaps. -/
theorem mean_le_integral_gapLength (hL : ∀ i < k, 0 ≤ L i) :
    (∑ i ∈ range k, L i) / k ≤
      ∫ x, gapLength L k x ∂(volume[|Set.Ico 0 (∑ j ∈ range k, L j)]) := by
  rw [integral_gapLength hL]
  exact sum_sq_div_sum_ge_mean L k (sum_nonneg fun i hi ↦ hL i (mem_range.mp hi))

end ClassicalLean.Probability.InspectionParadox
