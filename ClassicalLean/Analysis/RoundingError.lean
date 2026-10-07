/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Rounding error in a product and in a sum, in the standard model

In the standard model of rounding, every arithmetic result is the exact result times `1 + d` with
`|d| ≤ u`, where `u` is the unit roundoff. Write `γ n = n u / (1 - n u)` (`gamma`), for `n u < 1`.

* `abs_prod_one_add_sub_one_le`: `n` such factors give `|∏ (1 + dᵢ) - 1| ≤ γ n`.
* `abs_mul_prod_sub_le`: so a result carrying `n` rounding factors is within `γ n · |exact|` of
  the exact result.
* `abs_prodComputed_sub_le`: a product of `n + 1` numbers, formed left to right, takes `n`
  roundings and is within `γ n · |∏ xᵢ|` of the exact product.
* `abs_sumComputed_sub_le`: a sum of `n + 1` numbers, added left to right, takes `n` roundings and
  is within `γ n · ∑ |xᵢ|` of the exact sum.

Lean's `Float` is opaque to proof, so the model is stated over the reals with the `d`'s as
hypotheses. As a fact about hardware, not a theorem here: IEEE 754 double precision with round to
nearest satisfies the model with `u = 2⁻⁵³`, as long as no result overflows or underflows. Then
`γ 1000 ≈ 1.1 · 10⁻¹³` and `γ 10⁹ ≈ 1.1 · 10⁻⁷`.

Each hypothesis is needed. With `n u ≥ 1` the bound has no meaning, and Lean's `γ` is `x / 0 = 0`
at `n u = 1`: two factors `1 + 1/2` give the error `5/4` against `γ 2 = 0`. And `n u` alone is
not a bound: two factors `1 + 1/4` give `9/16 > 2 · 1/4`.
-/

open Finset

namespace ClassicalLean.Analysis.RoundingError

/-- `γ n = n u / (1 - n u)`. -/
noncomputable def gamma (u : ℝ) (n : ℕ) : ℝ := n * u / (1 - n * u)

lemma gamma_nonneg {u : ℝ} (hu : 0 ≤ u) {n : ℕ} (h : n * u < 1) : 0 ≤ gamma u n :=
  div_nonneg (by positivity) (by linarith)

/-- **One more rounding.** If `|η| ≤ γ n`, `|δ| ≤ u` and `(n + 1) u < 1`, then
`|(1 + η)(1 + δ) - 1| ≤ γ (n + 1)`. -/
theorem abs_one_add_mul_sub_one_le {u η δ : ℝ} {n : ℕ} (h : ((n : ℝ) + 1) * u < 1)
    (hη : |η| ≤ gamma u n) (hδ : |δ| ≤ u) : |(1 + η) * (1 + δ) - 1| ≤ gamma u (n + 1) := by
  have hu : 0 ≤ u := (abs_nonneg δ).trans hδ
  have hn : (n : ℝ) * u < 1 := by nlinarith
  have h1 : 0 < 1 - (n : ℝ) * u := by linarith
  have h2 : 0 < 1 - ((n : ℝ) + 1) * u := by linarith
  have hγ : 0 ≤ gamma u n := gamma_nonneg hu hn
  have e : (1 + η) * (1 + δ) - 1 = η + δ + η * δ := by ring
  have hab : |η + δ + η * δ| ≤ gamma u n + u + gamma u n * u := by
    calc |η + δ + η * δ| ≤ |η| + |δ| + |η| * |δ| := by
          rw [← abs_mul]; exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ gamma u n + u + gamma u n * u := by gcongr
  have hval : gamma u n + u + gamma u n * u = ((n : ℝ) + 1) * u / (1 - (n : ℝ) * u) := by
    unfold gamma; field_simp; ring
  rw [e]
  refine hab.trans (hval.le.trans ?_)
  unfold gamma
  push_cast
  apply div_le_div_of_nonneg_left (by positivity) h2
  nlinarith

/-- **`n` rounding factors.** If `|dᵢ| ≤ u` for `i < n` and `n u < 1`, then
`|∏_{i < n} (1 + dᵢ) - 1| ≤ γ n`. -/
theorem abs_prod_one_add_sub_one_le {u : ℝ} {d : ℕ → ℝ} {n : ℕ} (hd : ∀ i < n, |d i| ≤ u)
    (h : n * u < 1) : |∏ i ∈ range n, (1 + d i) - 1| ≤ gamma u n := by
  induction n with
  | zero => simp [gamma]
  | succ n ih =>
    have hu : 0 ≤ u := (abs_nonneg _).trans (hd 0 (Nat.succ_pos n))
    have h' : (n : ℝ) * u < 1 := by push_cast at h; nlinarith
    rw [prod_range_succ]
    push_cast at h
    have := abs_one_add_mul_sub_one_le (η := ∏ i ∈ range n, (1 + d i) - 1) h
      (ih (fun i hi ↦ hd i (hi.trans (Nat.lt_succ_self n))) h') (hd n (Nat.lt_succ_self n))
    simpa using this

/-- **A result with `n` rounding factors.** If the computed value is `e · ∏_{i < n} (1 + dᵢ)`
with `|dᵢ| ≤ u` and `n u < 1`, it is within `γ n · |e|` of the exact value `e`. -/
theorem abs_mul_prod_sub_le {u e : ℝ} {d : ℕ → ℝ} {n : ℕ} (hd : ∀ i < n, |d i| ≤ u)
    (h : n * u < 1) : |e * ∏ i ∈ range n, (1 + d i) - e| ≤ gamma u n * |e| := by
  rw [show e * ∏ i ∈ range n, (1 + d i) - e = e * (∏ i ∈ range n, (1 + d i) - 1) by ring,
    abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_prod_one_add_sub_one_le hd h) (abs_nonneg e)

/-- A product of `x 0, …, x n` formed left to right, each multiplication rounded by `1 + d k`. -/
def prodComputed (x d : ℕ → ℝ) : ℕ → ℝ
  | 0 => x 0
  | k + 1 => prodComputed x d k * x (k + 1) * (1 + d k)

lemma prodComputed_eq (x d : ℕ → ℝ) (n : ℕ) :
    prodComputed x d n = (∏ i ∈ range (n + 1), x i) * ∏ i ∈ range n, (1 + d i) := by
  induction n with
  | zero => simp [prodComputed]
  | succ n ih =>
    rw [prodComputed, ih, prod_range_succ x (n + 1), prod_range_succ (fun i ↦ 1 + d i) n]; ring

/-- **A product of `n + 1` numbers.** Formed left to right with `n` roundings, `|dₖ| ≤ u` and
`n u < 1`, the computed product is within `γ n · |∏ xᵢ|` of the exact one. -/
theorem abs_prodComputed_sub_le {u : ℝ} {x d : ℕ → ℝ} {n : ℕ} (hd : ∀ k < n, |d k| ≤ u)
    (h : n * u < 1) : |prodComputed x d n - ∏ i ∈ range (n + 1), x i| ≤
      gamma u n * |∏ i ∈ range (n + 1), x i| := by
  rw [prodComputed_eq]
  exact abs_mul_prod_sub_le hd h

/-- A sum of `x 0, …, x n` formed left to right, each addition rounded by `1 + δ k`. -/
def sumComputed (x δ : ℕ → ℝ) : ℕ → ℝ
  | 0 => x 0
  | k + 1 => (sumComputed x δ k + x (k + 1)) * (1 + δ k)

/-- Each term of the computed sum carries its own error, at most `γ n`. -/
theorem exists_sumComputed_eq {u : ℝ} {x δ : ℕ → ℝ} {n : ℕ} (hδ : ∀ k < n, |δ k| ≤ u)
    (h : n * u < 1) : ∃ η : ℕ → ℝ, (∀ i ∈ range (n + 1), |η i| ≤ gamma u n) ∧
      sumComputed x δ n = ∑ i ∈ range (n + 1), x i * (1 + η i) := by
  induction n with
  | zero => exact ⟨fun _ ↦ 0, fun i _ ↦ by simp [gamma], by simp [sumComputed]⟩
  | succ n ih =>
    have hu : 0 ≤ u := (abs_nonneg _).trans (hδ 0 (Nat.succ_pos n))
    push_cast at h
    have h' : (n : ℝ) * u < 1 := by nlinarith
    obtain ⟨η, hη, hs⟩ := ih (fun k hk ↦ hδ k (hk.trans (Nat.lt_succ_self n))) h'
    have hδn := hδ n (Nat.lt_succ_self n)
    refine ⟨fun i ↦ if i ≤ n then (1 + η i) * (1 + δ n) - 1 else δ n, fun i hi ↦ ?_, ?_⟩
    · by_cases hin : i ≤ n
      · simp only [hin, ↓reduceIte]
        exact abs_one_add_mul_sub_one_le h (hη i (mem_range.mpr (Nat.lt_succ_of_le hin))) hδn
      · simp only [hin, ↓reduceIte]
        refine hδn.trans ?_
        unfold gamma; push_cast
        rw [le_div_iff₀ (by linarith)]
        nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hu, mul_nonneg hu hu,
          mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (mul_nonneg hu hu)]
    · rw [sumComputed, hs, sum_range_succ _ (n + 1), add_mul, sum_mul]
      congr 1
      · refine sum_congr rfl fun i hi ↦ ?_
        have : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
        simp only [this, ↓reduceIte]; ring
      · simp

/-- **A sum of `n + 1` numbers.** Added left to right with `n` roundings, `|δₖ| ≤ u` and
`n u < 1`, the computed sum is within `γ n · ∑ |xᵢ|` of the exact sum. -/
theorem abs_sumComputed_sub_le {u : ℝ} {x δ : ℕ → ℝ} {n : ℕ} (hδ : ∀ k < n, |δ k| ≤ u)
    (h : n * u < 1) : |sumComputed x δ n - ∑ i ∈ range (n + 1), x i| ≤
      gamma u n * ∑ i ∈ range (n + 1), |x i| := by
  obtain ⟨η, hη, hs⟩ := exists_sumComputed_eq hδ h
  rw [hs, ← sum_sub_distrib, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi ↦ ?_)
  rw [show x i * (1 + η i) - x i = η i * x i by ring, abs_mul, mul_comm (gamma u n)]
  exact mul_le_mul_of_nonneg_right (hη i hi) (abs_nonneg _) |>.trans_eq (mul_comm _ _)

end ClassicalLean.Analysis.RoundingError
