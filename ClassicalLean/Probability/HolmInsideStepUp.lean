/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Probability.StepDownProcedure
import ClassicalLean.Probability.StepUpProcedure

/-!
# Holm's rejections lie inside Benjamini and Hochberg's

For `m` tests indexed by a finite type `ι`, p-values `x : ι → ℝ` and a level `q ≥ 0`, every
hypothesis that Holm's step-down procedure rejects (`holmRejected q x i`,
`ClassicalLean.Probability.StepDownProcedure`) is rejected by the step-up procedure of Benjamini
and Hochberg at the same level too (`ClassicalLean.Probability.StepUpProcedure`), whose rejections
are the `i` with `x i ≤ q · numRej q x / m`:

* `le_mul_numRej_div_of_holmRejected` — for `q ≥ 0` and `holmRejected q x i`,
  `x i ≤ q * numRej q x / Fintype.card ι`.

Bridge row 158 of MATH-PLAN-library-2's bridges file (order CLOUD-MATH-5), stated and proved by the
Claude Code cloud session of that order from the row's sketch; no draft. The step-up procedure's
rejection is written as StepUpProcedure writes it in `numRej_update_eq_of_le`, with `m` as
`Fintype.card ι` and the threshold `q * numRej q x / Fintype.card ι`.

The proof. Let `k = countLE x (x i)` be the number of p-values at most `x i`; it counts `i`, so
`1 ≤ k ≤ m`. For each `j` with `x j ≤ x i`, the p-values below `x j` are among the `k` at most
`x i`, without `j` itself, so at least `m − k + 1` p-values are at least `x j`, and Holm's rule
gives `x j ≤ q / (m − k + 1)`. Since `k (m − k + 1) − m = (k − 1)(m − k) ≥ 0`, this is at most
`q k / m`. So at least `k` p-values are at most `q k / m`, `le_numRej` gives `k ≤ numRej q x`, and
`x i ≤ q k / m ≤ q · numRej q x / m` by `thr_mono`. Ties need no separate case: both procedures
count tied p-values in their definitions.
-/

open Finset
open ClassicalLean.Probability.StepDownProcedure ClassicalLean.Probability.StepUpProcedure

namespace ClassicalLean.Probability.HolmInsideStepUp

/-- **Holm's rejections lie inside Benjamini and Hochberg's.** For a level `q ≥ 0`, if Holm's
step-down procedure rejects hypothesis `i` (`holmRejected q x i`), then
`x i ≤ q · numRej q x / m`, with `m = Fintype.card ι`: the step-up procedure rejects `i` too. -/
theorem le_mul_numRej_div_of_holmRejected {ι : Type*} [Fintype ι] {q : ℝ} (hq : 0 ≤ q)
    {x : ι → ℝ} {i : ι} (h : holmRejected q x i) :
    x i ≤ q * numRej q x / Fintype.card ι := by
  classical
  set m := Fintype.card ι with hm
  set k := countLE x (x i) with hk
  have hk1 : 1 ≤ k := card_pos.mpr ⟨i, by simp⟩
  have hkm : k ≤ m := countLE_le_card x (x i)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hk1.trans hkm
  -- every p-value at most `x i` is at most `q k / m`
  have hj : ∀ j, x j ≤ x i → x j ≤ q * k / m := by
    intro j hji
    set c := (univ.filter fun l ↦ x j ≤ x l).card with hc
    -- the p-values below `x j` are among those at most `x i`, without `j`
    have hsub : (univ.filter fun l ↦ ¬ x j ≤ x l) ⊆ (univ.filter fun l ↦ x l ≤ x i).erase j := by
      intro l hl
      simp only [mem_filter, mem_univ, true_and, not_le] at hl
      simp only [mem_erase, mem_filter, mem_univ, true_and]
      exact ⟨fun h' ↦ by subst h'; exact lt_irrefl _ hl, hl.le.trans hji⟩
    have h1 := card_le_card hsub
    rw [card_erase_of_mem (by simp [hji])] at h1
    have h2 := card_filter_add_card_filter_not (s := univ) (fun l ↦ x j ≤ x l)
    rw [card_univ] at h2
    have hck : m - k + 1 ≤ c := by
      have : (univ.filter fun l ↦ x l ≤ x i).card = k := rfl
      omega
    have hcR : ((m - k + 1 : ℕ) : ℝ) = m - k + 1 := by push_cast [Nat.cast_sub hkm]; ring
    have hpos : (0 : ℝ) < ((m - k + 1 : ℕ) : ℝ) := by positivity
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hkmR : (k : ℝ) ≤ m := by exact_mod_cast hkm
    calc x j ≤ q / c := h j hji
      _ ≤ q / ((m - k + 1 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_left hq hpos (by exact_mod_cast hck)
      _ ≤ q * k / m := by
          rw [div_le_div_iff₀ hpos hm0, hcR]
          nlinarith [mul_nonneg hq (mul_nonneg (sub_nonneg.mpr hkR) (sub_nonneg.mpr hkmR))]
  -- so at least `k` p-values are at most `q k / m`, and `k ≤ numRej q x`
  have hcount : k ≤ countLE x (q * k / m) :=
    card_le_card fun j hj' ↦ by
      simp only [mem_filter, mem_univ, true_and] at hj' ⊢
      exact hj j hj'
  have hR : k ≤ numRej q x := le_numRej hkm hcount
  exact (hj i le_rfl).trans (thr_mono hq hR)

end ClassicalLean.Probability.HolmInsideStepUp

/-- The hypotheses of `le_mul_numRej_div_of_holmRejected` hold together: three tests
(`ι = Fin 3`), the p-values `x = (1/100, 1/50, 9/10)`, the level `q = 1/10 ≥ 0`, and Holm's
procedure rejects `i = 1`, which is not the smallest p-value, so both of Holm's steps are used:
`x 0 = 1/100 ≤ (1/10)/3`, three p-values being at least it, and `x 1 = 1/50 ≤ (1/10)/2`, two being
at least it; `x 2 = 9/10` is not at most `x 1`. What moves: the step-up procedure rejects
`numRej = 2` tests (`2 ≤ countLE x (2/30) = 2`, but `3 > countLE x (3/30) = 2`), and the
conclusion `1/50 ≤ (1/10) · 2/3 = 2/30` is strict. -/
example := ClassicalLean.Probability.HolmInsideStepUp.le_mul_numRej_div_of_holmRejected
  (ι := Fin 3) (q := 1 / 10) (x := ![1 / 100, 1 / 50, 9 / 10]) (i := 1) (by norm_num)
  (fun j hj ↦ by
    fin_cases j
    · rw [Finset.card_filter, Fin.sum_univ_three]
      norm_num
    · rw [Finset.card_filter, Fin.sum_univ_three]
      norm_num
    · norm_num at hj)
