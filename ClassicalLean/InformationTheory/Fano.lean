/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.InformationTheory.MutualInformation
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Fano's inequality

An observation `Y` is used to guess a hidden value `X` with finitely many possible values, by a
rule `g`. If the guess is often right, `Y` must leave little uncertainty about `X`. Fano's
inequality says how little: with `P_e` the chance that the guess `g Y` is wrong and
`h p = −p log p − (1 − p) log (1 − p)` the binary entropy,
`H(X | Y) ≤ h(P_e) + P_e log (|X| − 1)` (natural logarithms).

The joint chances are a function `P : β × α → ℝ`, with the observation `y : β` first and the
hidden value `x : α` second, so that the library's `condEntropy P` is `H(X | Y)`.

* `errorChance P g` — the chance that `g y ≠ x`.
* `shannonEntropy_le_binEntropy_add` — the one-row form: a distribution `q` on `α` and a point
  `a` have `H(q) ≤ h(1 − q a) + (1 − q a) log (|α| − 1)`.
* `condEntropy_le_binEntropy_add` — **Fano's inequality**.
* `condEntropy_le_log_two_add` — the weaker form `H(X | Y) ≤ log 2 + P_e log (|X| − 1)`.

Citation: Fano 1961, "Transmission of Information". The proof: in each row, the chance off the
guessed point is spread over `|α| − 1` values, whose entropy is at most that of the uniform spread
(Jensen's inequality for the concave `−t log t`); then the rows are averaged, and the binary entropy
is concave. This route was worked out here; no source is cited for it.

## Hypotheses

Measured in order LEAN-21's checks (check C36, floating point, margin `1e-9`): 2000 random joint
laws with about a quarter of their cells `0`, random rules `g`; largest excess of the left side
over the right `1.1e-16`. Each hypothesis is needed: drop it alone and the conclusion fails at:

* total `1`: twice the uniform law on two values of `x`, one `y`: `1.386 > 0`; in the one-row
  form, `q = (1/4, 1/4)`: `0.693 > 0.562`.
* entries at least `0` (a random search, with Lean's `log x = log |x|`): one `y`,
  `P = (2.226, 1.609, −2.835)`, `g y` the first value: `0.408 > −2.381`.

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-21, `grep -rniE` over Mathlib): `fano` 17
lines, all in names such as Stefano or `BinaryFan`;
`condEntropy|conditional entropy|binEntropy.*log|probability of error` 26 lines, all in the
binary entropy file (no conditional entropy).
Used: `Real.binEntropy`, `Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub`,
`Real.strictConcave_binEntropy`, `Real.binEntropy_le_log_two`, `Real.concaveOn_negMulLog`,
`ConcaveOn.le_map_sum`; from the library, `condEntropy_eq_sum_mul_shannonEntropy`.
-/

open Finset Real

namespace ClassicalLean.Simplex

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The chance that the guess `g y` differs from `x`, under the joint chances `P (y, x)`. -/
noncomputable def errorChance [DecidableEq α] (P : β × α → ℝ) (g : β → α) : ℝ :=
  ∑ yx, if yx.2 = g yx.1 then 0 else P yx

/-- Jensen's inequality for `−t log t` on a finite set of `k` points: values `r i ≥ 0` with total
`e` have `∑ negMulLog (r i) ≤ negMulLog e + e log k`. -/
private theorem sum_negMulLog_le {ι : Type*} (s : Finset ι) {r : ι → ℝ} (hr : ∀ i ∈ s, 0 ≤ r i) :
    ∑ i ∈ s, negMulLog (r i) ≤ negMulLog (∑ i ∈ s, r i) + (∑ i ∈ s, r i) * log s.card := by
  set e := ∑ i ∈ s, r i
  rcases s.eq_empty_or_nonempty with hs | hs
  · simp [hs, e]
  have hk : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hJ := concaveOn_negMulLog.le_map_sum (t := s) (w := fun _ ↦ (s.card : ℝ)⁻¹) (p := r)
    (fun _ _ ↦ inv_nonneg.mpr hk.le) (by rw [sum_const, nsmul_eq_mul, mul_inv_cancel₀ hk.ne'])
    (fun i hi ↦ Set.mem_Ici.mpr (hr i hi))
  simp only [smul_eq_mul, ← mul_sum] at hJ
  have he : 0 ≤ e := sum_nonneg hr
  have key : (s.card : ℝ) * negMulLog ((s.card : ℝ)⁻¹ * e) = negMulLog e + e * log s.card := by
    rcases he.eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · rw [negMulLog, negMulLog, ← div_eq_inv_mul, log_div hpos.ne' hk.ne']
      field_simp
      ring
  calc ∑ i ∈ s, negMulLog (r i) = s.card * ((s.card : ℝ)⁻¹ * ∑ i ∈ s, negMulLog (r i)) := by
        field_simp
    _ ≤ s.card * negMulLog ((s.card : ℝ)⁻¹ * e) := mul_le_mul_of_nonneg_left hJ hk.le
    _ = negMulLog e + e * log s.card := key

/-- **Fano's inequality for one distribution.** For `q ≥ 0` with total `1` on `α` and a point
`a`, `H(q) ≤ h(1 − q a) + (1 − q a) log (|α| − 1)`, with `h` the binary entropy. -/
theorem shannonEntropy_le_binEntropy_add {q : α → ℝ} (hq : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1)
    (a : α) :
    shannonEntropy q ≤ binEntropy (1 - q a) + (1 - q a) * log (Fintype.card α - 1) := by
  classical
  have hsplit := add_sum_erase univ q (mem_univ a)
  have he : ∑ x ∈ univ.erase a, q x = 1 - q a := by linarith
  have hcard : ((univ.erase a).card : ℝ) = Fintype.card α - 1 := by
    rw [card_erase_of_mem (mem_univ a), card_univ, Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨a⟩),
      Nat.cast_one]
  have hH : shannonEntropy q = negMulLog (q a) + ∑ x ∈ univ.erase a, negMulLog (q x) := by
    rw [shannonEntropy, ← add_sum_erase univ _ (mem_univ a), neg_add, ← sum_neg_distrib]
    simp only [negMulLog, neg_mul]
  have hJ := sum_negMulLog_le (univ.erase a) (r := q) fun x _ ↦ hq x
  rw [he, hcard] at hJ
  rw [hH, binEntropy_eq_negMulLog_add_negMulLog_one_sub, sub_sub_cancel]
  linarith

/-- The chance of an error, row by row: `errorChance P g = ∑ y, (∑ x, P (y, x) − P (y, g y))`. -/
private theorem errorChance_eq [DecidableEq α] (P : β × α → ℝ) (g : β → α) :
    errorChance P g = ∑ y, ((∑ x, P (y, x)) - P (y, g y)) := by
  rw [errorChance, Fintype.sum_prod_type]
  refine sum_congr rfl fun y _ ↦ ?_
  have h : ∀ x, (if x = g y then 0 else P (y, x)) = P (y, x) - if x = g y then P (y, x) else 0 :=
    fun x ↦ by split_ifs <;> simp
  simp [h, sum_sub_distrib]

/-- **Fano's inequality.** For joint chances `P (y, x) ≥ 0` with total `1` and any rule `g`
guessing `x` from `y`, with `P_e = errorChance P g` the chance of a wrong guess:
`H(X | Y) ≤ h(P_e) + P_e log (|X| − 1)`, with `h` the binary entropy. -/
theorem condEntropy_le_binEntropy_add [DecidableEq α] {P : β × α → ℝ} (hP : ∀ yx, 0 ≤ P yx)
    (hP1 : ∑ yx, P yx = 1) (g : β → α) :
    condEntropy P ≤ binEntropy (errorChance P g) +
      errorChance P g * log (Fintype.card α - 1) := by
  set r : β → ℝ := fun y ↦ ∑ x, P (y, x)
  set e : β → ℝ := fun y ↦ 1 - P (y, g y) / r y
  have hr0 : ∀ y, 0 ≤ r y := fun y ↦ sum_nonneg fun x _ ↦ hP (y, x)
  have hr1 : ∑ y, r y = 1 := by rw [← hP1, Fintype.sum_prod_type]
  have hPle : ∀ y, P (y, g y) ≤ r y := fun y ↦
    single_le_sum (f := fun x ↦ P (y, x)) (fun x _ ↦ hP (y, x)) (mem_univ (g y))
  have he01 : ∀ y, e y ∈ Set.Icc (0 : ℝ) 1 := by
    intro y
    have h1 : 0 ≤ P (y, g y) / r y := div_nonneg (hP _) (hr0 y)
    have h2 : P (y, g y) / r y ≤ 1 := div_le_one_of_le₀ (hPle y) (hr0 y)
    exact ⟨by simp only [e]; linarith, by simp only [e]; linarith⟩
  have hre : ∀ y, r y * e y = r y - P (y, g y) := by
    intro y
    rcases (hr0 y).eq_or_lt with h0 | hpos
    · have : P (y, g y) = 0 := le_antisymm (h0 ▸ hPle y) (hP _)
      simp [e, ← h0, this]
    · simp only [e]; field_simp
  have hPe : errorChance P g = ∑ y, r y * e y := by
    rw [errorChance_eq]; exact sum_congr rfl fun y _ ↦ (hre y).symm
  -- each row
  have hrow : ∀ y, r y * shannonEntropy (fun x ↦ P (y, x) / r y) ≤
      r y * (binEntropy (e y) + e y * log (Fintype.card α - 1)) := by
    intro y
    rcases (hr0 y).eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul, zero_mul]
    · refine mul_le_mul_of_nonneg_left ?_ hpos.le
      have := shannonEntropy_le_binEntropy_add (q := fun x ↦ P (y, x) / r y)
        (fun x ↦ div_nonneg (hP _) hpos.le) (by rw [← sum_div, div_self hpos.ne']) (g y)
      simpa [e] using this
  -- average the rows; the binary entropy is concave
  have hJ := strictConcave_binEntropy.concaveOn.le_map_sum (t := univ) (w := r) (p := e)
    (fun y _ ↦ hr0 y) hr1 (fun y _ ↦ he01 y)
  simp only [smul_eq_mul] at hJ
  rw [condEntropy_eq_sum_mul_shannonEntropy, hPe]
  calc ∑ y, r y * shannonEntropy (fun x ↦ P (y, x) / r y)
      ≤ ∑ y, r y * (binEntropy (e y) + e y * log (Fintype.card α - 1)) :=
        sum_le_sum fun y _ ↦ hrow y
    _ = ∑ y, r y * binEntropy (e y) + (∑ y, r y * e y) * log (Fintype.card α - 1) := by
        rw [sum_mul, ← sum_add_distrib]; exact sum_congr rfl fun y _ ↦ by ring
    _ ≤ binEntropy (∑ y, r y * e y) + (∑ y, r y * e y) * log (Fintype.card α - 1) := by
        linarith

/-- **Fano's inequality, weaker form.** Under the hypotheses of `condEntropy_le_binEntropy_add`,
`H(X | Y) ≤ log 2 + P_e log (|X| − 1)`. -/
theorem condEntropy_le_log_two_add [DecidableEq α] {P : β × α → ℝ} (hP : ∀ yx, 0 ≤ P yx)
    (hP1 : ∑ yx, P yx = 1) (g : β → α) :
    condEntropy P ≤ log 2 + errorChance P g * log (Fintype.card α - 1) := by
  have := condEntropy_le_binEntropy_add hP hP1 g
  linarith [binEntropy_le_log_two (p := errorChance P g)]

end ClassicalLean.Simplex
