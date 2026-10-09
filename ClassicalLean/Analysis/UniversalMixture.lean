/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# A mixture of fixed stakes against the best one in hindsight

Several rules each expose a fraction `S k i` of what they hold to the `i`-th value `y i`, so rule
`k` turns `1` into `∏ i < N, (1 + S k i · y i)`. Run them side by side, each on an equal share of
the start.

* `mixStake`: the stake of the mixture at step `i`, the rules' stakes averaged with weights equal to
  what each has made so far. By its definition it uses only the values before step `i`.
* `sum_prod_div_card_eq_prod_mixStake`: when every factor `1 + S k i · y i` is positive, the
  average of the rules' products is the product for `mixStake`. Running the rules side by side is
  itself one rule.
* `mixStake_mem_Icc`: with positive factors, that stake lies between the smallest and the largest
  of the rules' stakes.
* `log_prod_sub_log_card_le`: on every sequence with positive factors, the mixture's log product is
  at least each rule's less `log (card s)`. This is one-sided: the mixture can be far above a rule.
* `abs_log_one_add_mul_sub_le`: two stakes in `[0, l]` on a value `u ≥ -c`, with `0 ≤ c` and
  `l c < 1`, have log factors that differ by at most `|a - b| |u| / (1 - l c)`.
* `le_log_mixture`: for `K > 0`, the `K + 1` fixed stakes `0, l/K, …, l` with `l c < 1`, and values
  with `-c ≤ y i` and `|y i| ≤ D`, the mixture's log product is at least that of every fixed stake
  `θ ∈ [0, l]`, chosen in hindsight, less `log (K + 1) + N (l / K) D / (1 - l c)`. Its hypotheses
  `0 ≤ l` and `0 ≤ c` are not needed (review r5 of order LEAN-16 proved it without them); they are
  kept because the order fixes the statement.

No probability is involved: the guarantee holds on every sequence. This is Cover's universal
portfolio (1991) for one stream of values and cash, in a discrete form.
-/

open Finset

namespace ClassicalLean.Analysis.UniversalMixture

variable {ι : Type*}

/-- The stake of the mixture at step `i`: the average of the stakes `S k i`, weighted by what each
rule has made so far. -/
noncomputable def mixStake (s : Finset ι) (S : ι → ℕ → ℝ) (y : ℕ → ℝ) (i : ℕ) : ℝ :=
  (∑ k ∈ s, (∏ j ∈ range i, (1 + S k j * y j)) * S k i) /
    ∑ k ∈ s, ∏ j ∈ range i, (1 + S k j * y j)

/-- Running each rule on an equal share is one rule: when every factor is positive, the average of
the products is the product for `mixStake`. -/
theorem sum_prod_div_card_eq_prod_mixStake (s : Finset ι) (hs : s.Nonempty) {S : ι → ℕ → ℝ}
    {y : ℕ → ℝ} {N : ℕ} (hpos : ∀ k ∈ s, ∀ i ∈ range N, 0 < 1 + S k i * y i) :
    (∑ k ∈ s, ∏ i ∈ range N, (1 + S k i * y i)) / s.card =
      ∏ i ∈ range N, (1 + mixStake s S y i * y i) := by
  have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs.card_pos.ne'
  induction N with
  | zero => simp [hcard]
  | succ N ih =>
    have hposN : ∀ k ∈ s, ∀ i ∈ range N, 0 < 1 + S k i * y i := fun k hk i hi ↦
      hpos k hk i (mem_range.mpr ((mem_range.mp hi).trans (Nat.lt_succ_self N)))
    have hA : 0 < ∑ k ∈ s, ∏ i ∈ range N, (1 + S k i * y i) :=
      sum_pos (fun k hk ↦ prod_pos (hposN k hk)) hs
    rw [prod_range_succ, ← ih hposN]
    simp_rw [prod_range_succ]
    unfold mixStake
    field_simp
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun k _ ↦ by ring

/-- With positive factors, the mixture's stake lies between the smallest and the largest of the
rules' stakes. -/
theorem mixStake_mem_Icc (s : Finset ι) (hs : s.Nonempty) {S : ι → ℕ → ℝ} {y : ℕ → ℝ} {i : ℕ}
    {a b : ℝ} (hpos : ∀ k ∈ s, ∀ j ∈ range i, 0 < 1 + S k j * y j)
    (hS : ∀ k ∈ s, S k i ∈ Set.Icc a b) : mixStake s S y i ∈ Set.Icc a b := by
  have hw : ∀ k ∈ s, 0 < ∏ j ∈ range i, (1 + S k j * y j) := fun k hk ↦ prod_pos (hpos k hk)
  have hA : 0 < ∑ k ∈ s, ∏ j ∈ range i, (1 + S k j * y j) := sum_pos hw hs
  unfold mixStake
  constructor
  · rw [le_div_iff₀ hA, mul_sum]
    exact sum_le_sum fun k hk ↦ by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hS k hk).1 (hw k hk).le
  · rw [div_le_iff₀ hA, mul_sum]
    exact sum_le_sum fun k hk ↦ by
      rw [mul_comm b]; exact mul_le_mul_of_nonneg_left (hS k hk).2 (hw k hk).le

/-- On every sequence with positive factors, the mixture's log product is at least each rule's
less `log (card s)` (a one-sided bound). -/
theorem log_prod_sub_log_card_le (s : Finset ι) {S : ι → ℕ → ℝ} {y : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ k ∈ s, ∀ i ∈ range N, 0 < 1 + S k i * y i) {k₀ : ι} (hk₀ : k₀ ∈ s) :
    Real.log (∏ i ∈ range N, (1 + S k₀ i * y i)) - Real.log s.card ≤
      Real.log ((∑ k ∈ s, ∏ i ∈ range N, (1 + S k i * y i)) / s.card) := by
  have hcard : (0 : ℝ) < s.card := Nat.cast_pos.mpr (card_pos.mpr ⟨k₀, hk₀⟩)
  have hk : 0 < ∏ i ∈ range N, (1 + S k₀ i * y i) := prod_pos (hpos k₀ hk₀)
  rw [← Real.log_div hk.ne' hcard.ne']
  apply Real.log_le_log (div_pos hk hcard)
  apply div_le_div_of_nonneg_right _ hcard.le
  exact single_le_sum (f := fun k ↦ ∏ i ∈ range N, (1 + S k i * y i))
    (fun k hk ↦ (prod_pos (hpos k hk)).le) hk₀

/-- Two stakes in `[0, l]` on a value `u ≥ -c`, with `0 ≤ c` and `l c < 1`: their log factors
differ by at most `|a - b| |u| / (1 - l c)`. -/
theorem abs_log_one_add_mul_sub_le {a b u c l : ℝ} (hc : 0 ≤ c) (hlc : l * c < 1)
    (ha : a ∈ Set.Icc 0 l) (hb : b ∈ Set.Icc 0 l) (hu : -c ≤ u) :
    |Real.log (1 + a * u) - Real.log (1 + b * u)| ≤ |a - b| * |u| / (1 - l * c) := by
  have h1 : 0 < 1 - l * c := by linarith
  -- both factors are at least `1 - l c`
  have hlow : ∀ z ∈ Set.Icc 0 l, 1 - l * c ≤ 1 + z * u := fun z hz ↦ by
    nlinarith [mul_le_mul_of_nonneg_left hu hz.1, mul_le_mul_of_nonneg_right hz.2 hc]
  have hp := hlow a ha
  have hq := hlow b hb
  have hp0 : 0 < 1 + a * u := h1.trans_le hp
  have hq0 : 0 < 1 + b * u := h1.trans_le hq
  have hab : |a - b| * |u| = |(a - b) * u| := (abs_mul _ _).symm
  have hk : 0 ≤ |a - b| * |u| := by positivity
  -- `log p - log q ≤ p / q - 1 = (a - b) u / q`
  have side : ∀ p q : ℝ, 0 < p → 1 - l * c ≤ q → |p - q| ≤ |a - b| * |u| →
      Real.log p - Real.log q ≤ |a - b| * |u| / (1 - l * c) := fun p q hp hq hpq ↦ by
    have hq0 : 0 < q := h1.trans_le hq
    rw [← Real.log_div hp.ne' hq0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hp hq0)
    have e : p / q - 1 = (p - q) / q := by field_simp
    rw [e] at this
    have h2 : (p - q) / q ≤ |p - q| / q := div_le_div_of_nonneg_right (le_abs_self _) hq0.le
    have h3 : |p - q| / q ≤ |a - b| * |u| / q := div_le_div_of_nonneg_right hpq hq0.le
    have h4 : |a - b| * |u| / q ≤ |a - b| * |u| / (1 - l * c) :=
      div_le_div_of_nonneg_left hk h1 hq
    linarith
  have hd1 : |(1 + a * u) - (1 + b * u)| ≤ |a - b| * |u| := by
    rw [hab]; apply le_of_eq; congr 1; ring
  have hd2 : |(1 + b * u) - (1 + a * u)| ≤ |a - b| * |u| := by rwa [abs_sub_comm]
  rw [abs_le]
  constructor
  · have := side _ _ hq0 hp hd2
    linarith
  · exact side _ _ hp0 hq hd1

/-- **A mixture of fixed stakes against the best fixed stake in hindsight.** For `K > 0` and
`l c < 1`, the `K + 1` stakes `k l / K` run on equal shares: on every sequence with `-c ≤ y i` and
`|y i| ≤ D`, the log of their
average product is at least the log product of any fixed stake `θ ∈ [0, l]`, less
`log (K + 1) + N (l / K) D / (1 - l c)`. -/
theorem le_log_mixture {N K : ℕ} (hK : 0 < K) {l c D : ℝ} (hl : 0 ≤ l) (hc : 0 ≤ c)
    (hlc : l * c < 1) {y : ℕ → ℝ} (hy : ∀ i, -c ≤ y i) (hyD : ∀ i, |y i| ≤ D) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 l) :
    ∑ i ∈ range N, Real.log (1 + θ * y i) - Real.log ((K : ℝ) + 1) -
        N * (l / K) * D / (1 - l * c) ≤
      Real.log ((∑ k ∈ range (K + 1), ∏ i ∈ range N, (1 + (k : ℝ) * l / K * y i)) /
        ((K : ℝ) + 1)) := by
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have h1 : 0 < 1 - l * c := by linarith
  -- the grid point below `θ`
  set k := ⌊θ * K / l⌋₊ with hkdef
  have hgrid : ∀ j : ℕ, j ≤ K → (j : ℝ) * l / K ∈ Set.Icc 0 l := fun j hj ↦ by
    have hj' : (j : ℝ) ≤ K := Nat.cast_le.mpr hj
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hKpos]
    nlinarith
  have hkK : k ≤ K := by
    rcases hl.eq_or_lt with hl0 | hlpos
    · rw [hkdef, ← hl0, div_zero, Nat.floor_zero]; exact Nat.zero_le K
    · have hle : θ * K / l ≤ K := by
        rw [div_le_iff₀ hlpos]; nlinarith [hθ.2]
      have := (Nat.floor_le (by have := hθ.1; positivity)).trans hle
      exact_mod_cast this
  have hclose : |θ - (k : ℝ) * l / K| ≤ l / K := by
    rcases hl.eq_or_lt with hl0 | hlpos
    · have hθ0 : θ = 0 := le_antisymm (hl0 ▸ hθ.2) hθ.1
      rw [hθ0, ← hl0]; simp
    · have hx : 0 ≤ θ * K / l := by have := hθ.1; positivity
      have hlo := Nat.floor_le hx
      have hhi := Nat.lt_floor_add_one (θ * K / l)
      rw [← hkdef] at hlo hhi
      rw [abs_le]
      constructor
      · -- `θ - k l / K ≥ 0 ≥ -l / K`
        have : (k : ℝ) * l / K ≤ θ := by
          rw [div_le_iff₀ hKpos]
          rw [le_div_iff₀ hlpos] at hlo
          linarith
        have : 0 ≤ l / K := by positivity
        linarith
      · -- `θ < (k + 1) l / K`
        rw [div_lt_iff₀ hlpos] at hhi
        have : θ * K ≤ (k + 1) * l := hhi.le
        rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hKpos]
        nlinarith
  -- every grid factor is positive
  have hpos : ∀ j ∈ range (K + 1), ∀ i ∈ range N, 0 < 1 + (j : ℝ) * l / K * y i :=
    fun j hj i _ ↦ by
      have hjK := hgrid j (Nat.lt_succ_iff.mp (mem_range.mp hj))
      nlinarith [mul_le_mul_of_nonneg_left (hy i) hjK.1, mul_le_mul_of_nonneg_right hjK.2 hc]
  -- step by step, the fixed stake `θ` is within `(l / K) D / (1 - l c)` of the grid point
  have hstep : ∀ i ∈ range N, Real.log (1 + θ * y i) - Real.log (1 + (k : ℝ) * l / K * y i) ≤
      (l / K) * D / (1 - l * c) := fun i _ ↦ by
    have h := abs_log_one_add_mul_sub_le hc hlc hθ (hgrid k hkK) (hy i)
    have h2 : |θ - (k : ℝ) * l / K| * |y i| ≤ (l / K) * D :=
      mul_le_mul hclose (hyD i) (abs_nonneg _) (by positivity)
    have h3 : |θ - (k : ℝ) * l / K| * |y i| / (1 - l * c) ≤ (l / K) * D / (1 - l * c) :=
      div_le_div_of_nonneg_right h2 h1.le
    linarith [le_abs_self (Real.log (1 + θ * y i) - Real.log (1 + (k : ℝ) * l / K * y i))]
  have hsum := sum_le_sum hstep
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] at hsum
  have hgridlog : ∑ i ∈ range N, Real.log (1 + (k : ℝ) * l / K * y i) =
      Real.log (∏ i ∈ range N, (1 + (k : ℝ) * l / K * y i)) :=
    (Real.log_prod fun i hi ↦ (hpos k (mem_range.mpr (Nat.lt_succ_of_le hkK)) i hi).ne').symm
  have hmix := log_prod_sub_log_card_le (range (K + 1)) (S := fun j _ ↦ (j : ℝ) * l / K) hpos
    (mem_range.mpr (Nat.lt_succ_of_le hkK))
  simp only [card_range, Nat.cast_add, Nat.cast_one] at hmix
  have e : (N : ℝ) * (l / K * D / (1 - l * c)) = N * (l / K) * D / (1 - l * c) := by ring
  rw [hgridlog] at hsum
  linarith

end ClassicalLean.Analysis.UniversalMixture
