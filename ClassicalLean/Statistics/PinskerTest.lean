/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Statistics.NeymanPearson
import ClassicalLean.InformationTheory.Channel

/-!
# A Pinsker bound for tests

On a finite set, for probability vectors `p₀` (the null) and `p₁` (the alternative) with
`p₀ i = 0 → p₁ i = 0`, every test `φ` (`IsTest`, `ClassicalLean.Statistics`) has size plus
missed-detection chance at least `1 − √(D(p₁ ‖ p₀)/2)`, with `D` the library's `relEntropy`:

* `size_add_one_sub_power_ge_pinsker` —
  `1 - √(relEntropy p₁ p₀ / 2) ≤ ∑ i, φ i * p₀ i + (1 - ∑ i, φ i * p₁ i)`.

Bridge row 164 of MATH-PLAN-library-2's bridges file (order CLOUD-MATH-5), stated and proved by the
Claude Code cloud session of that order from the row's sketch; no draft. The binders and hypotheses
are exactly those of `size_add_one_sub_power_ge` (`ClassicalLean.Statistics.NeymanPearson`, the
Bretagnolle–Huber bound of item 144), and the right side is the same expression; this is that
bound's companion with Pinsker's inequality in place of the Bretagnolle–Huber step. As there, the
hypothesis `p₀ i = 0 → p₁ i = 0` keeps out Lean's value of `relEntropy` at a cell with
`p₁ i > 0 = p₀ i`, where the true relative entropy is `+∞`; here it is also the hypothesis `hpq` of
Pinsker's inequality.

The proof. Size plus missed detection is `1 − ∑ i, φ i (p₁ i − p₀ i)`. Since `0 ≤ φ i ≤ 1`, each
term is at most the positive part of `p₁ i − p₀ i`, `(|p₁ i − p₀ i| + (p₁ i − p₀ i))/2`; both laws
sum to `1`, so the sum is at most `½ ∑ i, |p₁ i − p₀ i|`. Pinsker's inequality in the library's
form, `sq_sum_abs_sub_le_two_mul_relEntropy` at `p = p₁`, `q = p₀`
(`ClassicalLean.InformationTheory.Channel`), gives `(∑ i, |p₁ i − p₀ i|)² ≤ 2 D(p₁ ‖ p₀)`, so the
half-sum is at most `√(D/2)`.
-/

open ClassicalLean.Simplex ClassicalLean.Statistics

namespace ClassicalLean.Statistics.PinskerTest

/-- **A Pinsker bound for tests.** On a finite set, for probability vectors `p₀` (null) and `p₁`
(alternative) with `p₀ i = 0 → p₁ i = 0`, every test `φ` has size plus missed-detection chance at
least `1 − √(D(p₁ ‖ p₀)/2)`, with `D` the library's `relEntropy`. -/
theorem size_add_one_sub_power_ge_pinsker {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    {p₀ p₁ φ : ι → ℝ} (hp₀ : ∀ i, 0 ≤ p₀ i) (hp₀1 : ∑ i, p₀ i = 1)
    (hp₁ : ∀ i, 0 ≤ p₁ i) (hp₁1 : ∑ i, p₁ i = 1) (hsupp : ∀ i, p₀ i = 0 → p₁ i = 0)
    (hφ : IsTest φ) :
    1 - Real.sqrt (relEntropy p₁ p₀ / 2) ≤ ∑ i, φ i * p₀ i + (1 - ∑ i, φ i * p₁ i) := by
  -- each term `φ i (p₁ i − p₀ i)` is at most the positive part of `p₁ i − p₀ i`
  have hpt : ∀ i, φ i * (p₁ i - p₀ i) ≤ (|p₁ i - p₀ i| + (p₁ i - p₀ i)) / 2 := by
    intro i
    obtain ⟨h0, h1⟩ := hφ.2 i
    rcases le_total 0 (p₁ i - p₀ i) with hd | hd
    · rw [abs_of_nonneg hd]; nlinarith
    · rw [abs_of_nonpos hd]; nlinarith
  -- both laws sum to `1`, so the sum is at most half the total distance
  have hsum : ∑ i, φ i * (p₁ i - p₀ i) ≤ (∑ i, |p₁ i - p₀ i|) / 2 := by
    calc ∑ i, φ i * (p₁ i - p₀ i) ≤ ∑ i, (|p₁ i - p₀ i| + (p₁ i - p₀ i)) / 2 :=
          Finset.sum_le_sum fun i _ ↦ hpt i
      _ = (∑ i, |p₁ i - p₀ i|) / 2 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib, hp₀1, hp₁1]
          ring
  -- Pinsker's inequality bounds the half-distance by `√(D/2)`
  have hP := sq_sum_abs_sub_le_two_mul_relEntropy hp₁ hp₁1 hp₀ hp₀1 hsupp
  have hS0 : 0 ≤ ∑ i, |p₁ i - p₀ i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  have hhalf : (∑ i, |p₁ i - p₀ i|) / 2 ≤ Real.sqrt (relEntropy p₁ p₀ / 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hexp : ∑ i, φ i * p₀ i + (1 - ∑ i, φ i * p₁ i) = 1 - ∑ i, φ i * (p₁ i - p₀ i) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hexp]
  linarith

end ClassicalLean.Statistics.PinskerTest

/-- The hypotheses of `size_add_one_sub_power_ge_pinsker` hold together (the model of
`size_add_one_sub_power_ge`'s witness): three points; the null law `p₀ = (1/2, 1/2, 0)` and the
alternative `p₁ = (1/4, 3/4, 0)`, both nonnegative and summing to `1`, with `p₀ i = 0 → p₁ i = 0`,
which acts at the third point, where both vanish; and the test `φ = (0, 1, 0)`, measurable with
values in `[0, 1]`. What moves: the laws differ, so
`D(p₁ ‖ p₀) = (1/4) log (1/2) + (3/4) log (3/2)`, about `0.131`, is positive and the bound
`1 − √(D/2)`, about `0.744`, is below `1`; the test is not constant; its size plus missed-detection
chance is `1/2 + 1/4 = 3/4`. -/
example := ClassicalLean.Statistics.PinskerTest.size_add_one_sub_power_ge_pinsker (ι := Fin 3)
  (p₀ := ![1 / 2, 1 / 2, 0]) (p₁ := ![1 / 4, 3 / 4, 0]) (φ := ![0, 1, 0])
  (fun i ↦ by fin_cases i <;> norm_num) (by simp [Fin.sum_univ_three]; norm_num)
  (fun i ↦ by fin_cases i <;> norm_num) (by simp [Fin.sum_univ_three]; norm_num)
  (fun i h ↦ by fin_cases i <;> simp_all)
  ⟨measurable_of_finite _, fun i ↦ by fin_cases i <;> simp⟩
