/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Simplex.LogSumExp
import Mathlib.Probability.Moments.SubGaussian

/-!
# Exponential weights against the best expert

There are `K` experts. At each round each expert suffers a loss in `[0, 1]`. Before the round,
a learner puts the weight `softmax (−η · total loss so far)` on the experts, with `η > 0`: an
expert who has lost more gets exponentially less weight. The learner's loss for the round is the
weighted loss. After `T` rounds, whatever the losses were,

    learner's total loss ≤ best expert's total loss + log K / η + η T / 8.

With `η = √(8 log K / T)` (for `K ≥ 2` and `T ≥ 1`) the excess is `√(T log K / 2)`, so the
learner's average loss per round comes within `√(log K / (2 T))` of the best expert's
(arithmetic on the bound, not stated as a theorem here).

* `sum_mul_exp_mul_le_exp_of_mem_Icc` — Hoeffding's lemma for a weighted average of values in
  `[0, 1]`, taken from Mathlib's `hasSubgaussianMGF_of_mem_Icc` on the finite measure with
  masses `p j`.
* `logSumExp_add_smul_le` — so one round moves `logSumExp` of the scores by at most the weighted
  loss times the step, plus `s² / 8`.
* `sum_inner_softmax_le` — the bound above, by summing the rounds: `logSumExp` starts at
  `log K` and ends at least at `−η` times any one expert's total loss (`le_logSumExp`).

The weights are the library's `softmax` (`Simplex/LogSumExp`), so this is the same object as the
Gibbs distribution there, at the scores `−η · total loss`.

## Hypotheses

Measured in order LEAN-19's checks (check C21, floats with a tolerance of `1e-12` for the
one-round bound and `1e-9` for the main bound): the one-round bound on 3000 random cases, and
the main bound on 600 random loss sequences (up to 6 experts and 30 rounds, several `η`), for
every expert. Each hypothesis fails when dropped alone, with two
experts, one round and `i = 0`:

* `0 ≤ l`: `η = 1`, losses `(−1, 1)`: weighted loss `0` against `−1 + log 2 + 1/8 = −0.182`.
* `l ≤ 1`: `η = 1`, losses `(0, 2)`: `1` against `log 2 + 1/8 = 0.818`.
* `0 < η`: at `η = 0` Lean reads `log 2 / 0` as `0`, and the weights are equal: losses `(0, 1)`
  give `1/2` against `0`; at `η = −1` the bound is `−0.818`.

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-19, `grep -rniE` over Mathlib):
`hedge|multiplicative weight|exponential weight|regret|freund|schapire` 3 hits, all a graph
variable named `hedgeSet`. Mathlib has Hoeffding's lemma (`Probability/Moments/SubGaussian.lean`),
which is used here.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped NNReal
open ClassicalLean.Simplex

namespace ClassicalLean.Analysis

variable {ι : Type*} [Fintype ι]

/-- **Hoeffding's lemma for a finite average.** For weights `p` summing to `1` and values `l` in
`[0, 1]`, the weighted average of `exp (s l)` is at most
`exp (s · (weighted average of l) + s² / 8)`, for every real `s`. This is Mathlib's
`hasSubgaussianMGF_of_mem_Icc` applied to the probability measure that puts mass `p j` on `j`;
it is not proved again here. -/
theorem sum_mul_exp_mul_le_exp_of_mem_Icc {p l : ι → ℝ} (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (hl : ∀ j, l j ∈ Set.Icc (0 : ℝ) 1) (s : ℝ) :
    ∑ j, p j * Real.exp (s * l j) ≤ Real.exp (s * ∑ j, p j * l j + s ^ 2 / 8) := by
  let _ : MeasurableSpace ι := ⊤
  have : MeasurableSingletonClass ι := ⟨fun _ ↦ trivial⟩
  classical
  let μ : Measure ι := ∑ j, ENNReal.ofReal (p j) • Measure.dirac j
  have hμj : ∀ j, μ.real {j} = p j := by
    intro j
    simp [μ, Measure.real, Set.indicator, ENNReal.toReal_ofReal (hp j)]
  have : IsFiniteMeasure μ := by
    constructor; simp [μ]
  have hint : ∀ f : ι → ℝ, ∫ j, f j ∂μ = ∑ j, p j * f j := by
    intro f
    rw [integral_fintype Integrable.of_finite]
    simp [hμj]
  have : IsProbabilityMeasure μ := by
    constructor
    simp only [μ, Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply, Pi.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ hp j), hp1, ENNReal.ofReal_one]
  have h := (hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := l) (a := 0) (b := 1)
    (measurable_of_countable l).aemeasurable (ae_of_all _ hl)).mgf_le s
  simp only [mgf, hint] at h
  have hc : (((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) * s ^ 2 / 2 = s ^ 2 / 8 := by
    simp; ring
  rw [hc] at h
  set m := ∑ j, p j * l j
  calc ∑ j, p j * Real.exp (s * l j)
      = Real.exp (s * m) * ∑ j, p j * Real.exp (s * (l j - m)) := by
        rw [mul_sum]; refine sum_congr rfl fun j _ ↦ ?_
        rw [mul_left_comm, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (s * m) * Real.exp (s ^ 2 / 8) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = Real.exp (s * m + s ^ 2 / 8) := (Real.exp_add _ _).symm

/-- **One step of exponential weights.** For values `l` in `[0, 1]` and every real `s`:
`logSumExp (x + s • l) ≤ logSumExp x + s · ∑ softmax x j · l j + s² / 8`. -/
theorem logSumExp_add_smul_le (x : ι → ℝ) {l : ι → ℝ} (hl : ∀ j, l j ∈ Set.Icc (0 : ℝ) 1)
    (s : ℝ) :
    logSumExp (x + s • l) ≤ logSumExp x + s * ∑ j, softmax x j * l j + s ^ 2 / 8 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [univ_eq_empty, sum_empty, mul_zero, add_zero]
    have : logSumExp (x + s • l) = logSumExp x := by simp [logSumExp]
    rw [this]; linarith [sq_nonneg s]
  have hpos := sum_exp_pos x
  have hsplit : ∑ j, Real.exp ((x + s • l) j) =
      (∑ j, Real.exp (x j)) * ∑ j, softmax x j * Real.exp (s * l j) := by
    rw [mul_sum]; refine sum_congr rfl fun j _ ↦ ?_
    simp only [softmax, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Real.exp_add]
    field_simp
  have hq : 0 < ∑ j, softmax x j * Real.exp (s * l j) :=
    sum_pos (fun j _ ↦ mul_pos (softmax_pos x j) (Real.exp_pos _)) univ_nonempty
  have hb := sum_mul_exp_mul_le_exp_of_mem_Icc (fun j ↦ (softmax_pos x j).le) (sum_softmax x) hl s
  have hlog := Real.log_le_log hq hb
  rw [Real.log_exp] at hlog
  rw [logSumExp, hsplit, Real.log_mul hpos.ne' hq.ne', ← logSumExp]
  linarith

/-- **Exponential weights against the best expert** (Freund and Schapire 1997; the bound as in
Cesa-Bianchi and Lugosi 2006, Theorem 2.2). There are finitely many experts `j`; at each round
`t` every expert has a loss `l t j` in `[0, 1]`. At round `t` the weights are
`softmax (−η · losses so far)`, and the weighted loss is `∑ j, weight j · l t j` (the
"inner" of the name: the dot product of the weights with the losses). For every
`η > 0`, every number of rounds `T` and every expert `i`, the total weighted loss is at most
expert `i`'s total loss plus `log K / η + η T / 8`, with `K` the number of experts. The losses
can be chosen in any way, even after seeing the weights; no probability is involved. -/
theorem sum_inner_softmax_le {l : ℕ → ι → ℝ} (hl : ∀ t j, l t j ∈ Set.Icc (0 : ℝ) 1) {η : ℝ}
    (hη : 0 < η) (T : ℕ) (i : ι) :
    ∑ t ∈ range T, ∑ j, softmax (fun k ↦ -η * ∑ s ∈ range t, l s k) j * l t j ≤
      ∑ t ∈ range T, l t i + Real.log (Fintype.card ι) / η + η * T / 8 := by
  set A := ∑ t ∈ range T, ∑ j, softmax (fun k ↦ -η * ∑ s ∈ range t, l s k) j * l t j
  have hΦ : ∀ n : ℕ, logSumExp (fun k ↦ -η * ∑ s ∈ range n, l s k) ≤ Real.log (Fintype.card ι) -
      η * ∑ t ∈ range n, ∑ j, softmax (fun k ↦ -η * ∑ s ∈ range t, l s k) j * l t j +
        n * η ^ 2 / 8 := by
    intro n
    induction n with
    | zero => simp [logSumExp]
    | succ n ih =>
      have hv : (fun k ↦ -η * ∑ s ∈ range (n + 1), l s k) =
          (fun k ↦ -η * ∑ s ∈ range n, l s k) + (-η) • l n := by
        funext k; simp [sum_range_succ]; ring
      have h1 := logSumExp_add_smul_le (fun k ↦ -η * ∑ s ∈ range n, l s k) (hl n) (-η)
      rw [← hv] at h1
      rw [sum_range_succ]
      push_cast
      linarith
  have h1 := le_logSumExp (fun k ↦ -η * ∑ s ∈ range T, l s k) i
  have h2 := hΦ T
  have hη' : η * (Real.log (Fintype.card ι) / η) = Real.log (Fintype.card ι) :=
    mul_div_cancel₀ _ hη.ne'
  have : η * A ≤ η * (∑ t ∈ range T, l t i + Real.log (Fintype.card ι) / η + η * T / 8) := by
    rw [mul_add, mul_add, hη']
    linarith
  exact le_of_mul_le_mul_left this hη

end ClassicalLean.Analysis

/-- The hypotheses of `sum_inner_softmax_le` hold together: two experts whose losses alternate,
`l t j = 1` when `t + j` is even and `0` otherwise, so every loss lies in `[0, 1]`; the learning
rate `η = 1/2 > 0`; `T = 4` rounds, against expert `i = 1`. -/
example := ClassicalLean.Analysis.sum_inner_softmax_le (ι := Fin 2)
  (l := fun t j ↦ if (t + (j : ℕ)) % 2 = 0 then 1 else 0)
  (fun t j ↦ by split_ifs <;> norm_num) (η := 1 / 2) (by norm_num) (T := 4) (i := 1)
