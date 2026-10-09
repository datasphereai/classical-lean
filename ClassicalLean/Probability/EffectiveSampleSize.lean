/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.Moments.Variance

/-!
# What an average of correlated quantities is worth

The plain average of `k` quantities with finite variance has variance equal to the average of all
`k²` covariances (`variance_average`). With unit variances and mean cross-covariance `r` (the mean
over ordered pairs of different indices, `meanCrossCov`), that is `(1 + (k - 1) r) / k`
(`variance_average_eq`): the `k` quantities are worth `k / (1 + (k - 1) r)` independent ones, the
design effect of survey sampling (Kish). With every covariance at least `0` they are worth at most
`k` (`inv_card_le_variance_average`).

For `n` quantities in a sequence whose covariances are `σ² ρ ^ |i - j|`, `0 ≤ ρ < 1` (lag
correlations that fall off geometrically), the double sum of `ρ ^ |i - j|` has a closed form
(`sum_sum_pow_eq`) and is at most `n (1 + ρ) / (1 - ρ)` (`sum_sum_pow_le`), so the average has
variance at most `σ² (1 + ρ) / ((1 - ρ) n)` (`variance_average_le_of_cov_eq`): the `n` quantities
are worth at least `n (1 - ρ) / (1 + ρ)` independent ones. Here `|i - j|` is written
`max i j - min i j`.

## What Mathlib provides

The variance of a finite sum as the double sum of covariances (`ProbabilityTheory.variance_fun_sum`)
and the scaling rule `ProbabilityTheory.variance_mul_const`. Mathlib v4.34.0 has no design effect,
effective sample size or participation ratio (searched for those words).

## Which hypotheses are needed

Unit variances are needed for `variance_average_eq` and for the bound `1/k`: with `X₁ = 0` and
`X₂ = ±1` the average has variance `1/4`, while the identity's right side and the bound `1/k` are
both `1/2`. Covariances at least `0` are needed for the bound: `X₁ = ±1` and `X₂ = -X₁` give
variance `0 < 1/2`. `0 ≤ ρ` and `ρ < 1` are needed for the bound
on the double sum, which exceeds it already at `n = 1` for `ρ = -1/2, -9/10, 1, 3/2` (at `ρ = 1`,
Lean's `x / 0 = 0` makes the bound `0`); `ρ ≠ 1` is needed for the closed form, which at `ρ = 1`
reads `0` against `n²`.
-/

open MeasureTheory ProbabilityTheory Finset

namespace ClassicalLean.Probability.EffectiveSampleSize

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The variance of a plain average** is the average of all the covariances:
`Var ((X 1 + ⋯ + X k) / k) = (∑ i, ∑ j, cov (X i, X j)) / k²`. -/
theorem variance_average {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ) :
    Var[fun ω ↦ (∑ i, X i ω) / Fintype.card ι; μ] =
      (∑ i, ∑ j, cov[X i, X j; μ]) / (Fintype.card ι : ℝ) ^ 2 := by
  simp_rw [div_eq_mul_inv]
  rw [variance_mul_const, variance_fun_sum hX, inv_pow]

/-- The mean covariance over ordered pairs of different indices. -/
noncomputable def meanCrossCov {ι : Type*} [Fintype ι] [DecidableEq ι] (X : ι → Ω → ℝ)
    (μ : Measure Ω) : ℝ :=
  (∑ i, ∑ j ∈ univ.erase i, cov[X i, X j; μ]) /
    ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1))

omit [IsProbabilityMeasure μ] in
/-- The sum of the cross-covariances is `k (k - 1)` times their mean, also when `k ≤ 1`. -/
lemma sum_cross_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (X : ι → Ω → ℝ) :
    ∑ i, ∑ j ∈ univ.erase i, cov[X i, X j; μ] =
      (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) * meanCrossCov X μ := by
  by_cases h : (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) = 0
  · rw [h, zero_mul]
    rcases mul_eq_zero.mp h with h0 | h1
    · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp (by exact_mod_cast h0)
      simp
    · refine sum_eq_zero fun i _ ↦ ?_
      have hc : Fintype.card ι = 1 := by
        have : (Fintype.card ι : ℝ) = 1 := by linarith
        exact_mod_cast this
      have : univ.erase i = ∅ := by
        rw [← card_eq_zero, card_erase_of_mem (mem_univ i), card_univ, hc]
      rw [this, sum_empty]
  · rw [meanCrossCov, mul_div_cancel₀ _ h]

/-- **Kish's design effect.** With unit variances, the average of `k` quantities has variance
`(1 + (k - 1) r) / k`, where `r` is their mean cross-covariance: they are worth
`k / (1 + (k - 1) r)` independent ones. -/
theorem variance_average_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (h1 : ∀ i, Var[X i; μ] = 1) :
    Var[fun ω ↦ (∑ i, X i ω) / Fintype.card ι; μ] =
      (1 + ((Fintype.card ι : ℝ) - 1) * meanCrossCov X μ) / Fintype.card ι := by
  have hsplit : ∑ i, ∑ j, cov[X i, X j; μ] =
      Fintype.card ι + ∑ i, ∑ j ∈ univ.erase i, cov[X i, X j; μ] := by
    have hrow : ∀ i, ∑ j, cov[X i, X j; μ] = 1 + ∑ j ∈ univ.erase i, cov[X i, X j; μ] :=
      fun i ↦ by
        rw [← add_sum_erase _ _ (mem_univ i), covariance_self (hX i).aemeasurable, h1 i]
    simp only [hrow, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one]
  rw [variance_average hX, hsplit, sum_cross_eq]
  set k := (Fintype.card ι : ℝ)
  by_cases hk : k = 0
  · simp [hk]
  · field_simp

/-- **Correlated quantities are worth at most as many independent ones.** With unit variances and
every covariance at least `0`, the average of `k` quantities has variance at least `1/k`. -/
theorem inv_card_le_variance_average {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (h1 : ∀ i, Var[X i; μ] = 1) (h0 : ∀ i j, 0 ≤ cov[X i, X j; μ]) :
    1 / (Fintype.card ι : ℝ) ≤ Var[fun ω ↦ (∑ i, X i ω) / Fintype.card ι; μ] := by
  rw [variance_average hX]
  set k := (Fintype.card ι : ℝ)
  have hdiag : k ≤ ∑ i, ∑ j, cov[X i, X j; μ] := by
    calc k = ∑ i : ι, cov[X i, X i; μ] := by
          simp [covariance_self (hX _).aemeasurable, h1, k]
      _ ≤ ∑ i, ∑ j, cov[X i, X j; μ] :=
          sum_le_sum fun i _ ↦ single_le_sum (fun j _ ↦ h0 i j) (mem_univ i)
  by_cases hk : k = 0
  · simp [hk]
  · have hk0 : 0 < k := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hk)
    rw [div_le_div_iff₀ hk0 (by positivity)]
    nlinarith

/-- The sum `ρ + ρ² + ⋯ + ρⁿ`, written as `∑ i < n, ρ ^ (n - i)`, in closed form, for `ρ ≠ 1`. -/
lemma sum_range_pow_sub {ρ : ℝ} (h1 : ρ ≠ 1) (n : ℕ) :
    ∑ i ∈ range n, ρ ^ (n - i) = ρ * (1 - ρ ^ n) / (1 - ρ) := by
  have hρ : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : ∑ i ∈ range (n + 1), ρ ^ (n + 1 - i) = ρ * (∑ i ∈ range n, ρ ^ (n - i) + 1) := by
      rw [sum_range_succ, mul_add, mul_sum, mul_one, Nat.add_sub_cancel_left, pow_one]
      congr 1
      refine sum_congr rfl fun i hi ↦ ?_
      rw [← pow_succ', Nat.sub_add_comm (mem_range.mp hi).le]
    rw [hstep, ih]
    field_simp
    ring

/-- **The double sum of `ρ ^ |i - j|`** over `i, j < n`, in closed form, for `ρ ≠ 1`. -/
theorem sum_sum_pow_eq {ρ : ℝ} (h1 : ρ ≠ 1) (n : ℕ) :
    ∑ i ∈ range n, ∑ j ∈ range n, ρ ^ (max i j - min i j) =
      n * (1 + ρ) / (1 - ρ) - 2 * ρ * (1 - ρ ^ n) / (1 - ρ) ^ 2 := by
  have hρ : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  induction n with
  | zero => simp
  | succ n ih =>
    have hcol : ∑ i ∈ range n, ρ ^ (max i n - min i n) = ∑ i ∈ range n, ρ ^ (n - i) :=
      sum_congr rfl fun i hi ↦ by
        rw [max_eq_right (mem_range.mp hi).le, min_eq_left (mem_range.mp hi).le]
    have hrow : ∑ j ∈ range n, ρ ^ (max n j - min n j) = ∑ j ∈ range n, ρ ^ (n - j) :=
      sum_congr rfl fun j hj ↦ by
        rw [max_eq_left (mem_range.mp hj).le, min_eq_right (mem_range.mp hj).le]
    have hstep : ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), ρ ^ (max i j - min i j) =
        ∑ i ∈ range n, ∑ j ∈ range n, ρ ^ (max i j - min i j) +
          2 * ∑ i ∈ range n, ρ ^ (n - i) + 1 := by
      rw [sum_range_succ, sum_range_succ (fun j ↦ ρ ^ (max n j - min n j)), max_self, min_self,
        Nat.sub_self, pow_zero, hrow]
      simp_rw [sum_range_succ (fun j ↦ ρ ^ (max _ j - min _ j))]
      rw [sum_add_distrib, hcol]
      ring
    rw [hstep, ih, sum_range_pow_sub h1]
    push_cast
    field_simp
    ring

/-- For `0 ≤ ρ < 1`, the double sum of `ρ ^ |i - j|` over `i, j < n` is at most
`n (1 + ρ) / (1 - ρ)`. -/
theorem sum_sum_pow_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (n : ℕ) :
    ∑ i ∈ range n, ∑ j ∈ range n, ρ ^ (max i j - min i j) ≤ n * (1 + ρ) / (1 - ρ) := by
  rw [sum_sum_pow_eq h1.ne n]
  have hpow : ρ ^ n ≤ 1 := pow_le_one₀ h0 h1.le
  have : 0 ≤ 2 * ρ * (1 - ρ ^ n) / (1 - ρ) ^ 2 := by
    apply div_nonneg _ (sq_nonneg _)
    exact mul_nonneg (by linarith) (by linarith)
  linarith

/-- **Lag correlations that fall off geometrically.** `n` quantities with covariances
`σ² ρ ^ |i - j|`, `0 ≤ ρ < 1`: their average has variance at most `σ² (1 + ρ) / ((1 - ρ) n)`, so
they are worth at least `n (1 - ρ) / (1 + ρ)` independent ones. -/
theorem variance_average_le_of_cov_eq {n : ℕ} {X : Fin n → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ)
    {σ ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1)
    (hcov : ∀ i j : Fin n, cov[X i, X j; μ] = σ ^ 2 * ρ ^ (max (i : ℕ) j - min (i : ℕ) j)) :
    Var[fun ω ↦ (∑ i, X i ω) / n; μ] ≤ σ ^ 2 * (1 + ρ) / ((1 - ρ) * n) := by
  have h := variance_average hX
  rw [Fintype.card_fin] at h
  have hconv : ∑ i : Fin n, ∑ j : Fin n, ρ ^ (max (i : ℕ) j - min (i : ℕ) j) =
      ∑ i ∈ range n, ∑ j ∈ range n, ρ ^ (max i j - min i j) := by
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ ∑ j : Fin n, ρ ^ (max i (j : ℕ) - min i (j : ℕ))) n]
    exact sum_congr rfl fun i _ ↦ Fin.sum_univ_eq_sum_range (fun j ↦ ρ ^ (max i j - min i j)) n
  have hsum : ∑ i, ∑ j, cov[X i, X j; μ] =
      σ ^ 2 * ∑ i ∈ range n, ∑ j ∈ range n, ρ ^ (max i j - min i j) := by
    simp_rw [hcov, ← mul_sum, hconv]
  rw [h, hsum]
  have hS := sum_sum_pow_le h0 h1 n
  have hρ : 0 < 1 - ρ := by linarith
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    calc σ ^ 2 * (∑ i ∈ range n, ∑ j ∈ range n, ρ ^ (max i j - min i j)) / (n : ℝ) ^ 2
        ≤ σ ^ 2 * (n * (1 + ρ) / (1 - ρ)) / (n : ℝ) ^ 2 := by
          gcongr
      _ = σ ^ 2 * (1 + ρ) / ((1 - ρ) * n) := by
          field_simp

end ClassicalLean.Probability.EffectiveSampleSize
