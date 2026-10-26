/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.Moments.Variance
import ClassicalLean.Combinatorics.RecurrenceGeneratingFunction
import ClassicalLean.Probability.LinearPrediction
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Gaussian.Real

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

The measure is only assumed finite (`IsFiniteMeasure`); every statement here except the three of
order LEAN-17 below holds for it with Mathlib's `variance` and `covariance`. Read as variances, they
are about a probability measure, the case of use.

**The average of a steady first-order recursion** (order LEAN-17). For
`x (t + 1) = a x t + Z (t + 1)` (`Probability/LinearPrediction`), with the start and the noises
jointly independent, noise variance `s²`, `a² ≠ 1` and the steady start `Var x 0 = s² / (1 - a²)`,
the covariances are `s² / (1 - a²) · a ^ |i - j|` (`covariance_eq_of_steady`, from
`LinearPrediction.covariance_add`), so the average of `n` values has the exact variance
`variance_average_eq_of_steady` and, for `0 ≤ a < 1`, at most `s² / ((1 - a)² n)`
(`variance_average_le_of_steady`, from `variance_average_le_of_cov_eq`). The bound is the one the
long-run variance `s² / (1 - a)²` gives; the limit itself is not proved here. These three ask for a
probability measure, as `LinearPrediction` does.

* Needed, by order LEAN-17's checks (line C6): `0 ≤ a` (`a = -1/2`, `s = 1`, `n = 2`: `1/3`
  against `2/9`), `a < 1` (`a = 1`, `n = 2`: `1/4` against Lean's `x / 0 = 0`), the steady start
  (`a = 1/2`, `s = 1`, `Var x 0 = 100`, `n = 1`: `100` against `4`) and independent noise
  (`a = 0`, `s = 1`, one noise shared by all steps, `n = 2`: `1` against `1/2`); for the exact
  form, `a² ≠ 1` (`a = 1`, `n = 2`: `1/4` against `0`).
* Not shown needed by a case: the measurability and the finite second moments of the noises
  (`hZ`, `hZ2`) and the noise variance `s²` (`hvar`). The probability measure is not needed
  either (review r6 of order LEAN-17: Mathlib's `iIndepFun.isProbabilityMeasure` derives it from
  the independence); it is kept as `LinearPrediction` states it. `variance_average_le_of_steady'`
  (order LEAN-31, item 104) is the bound with no measure instance at all (by hand: its proof's
  first line, `iIndepFun.isProbabilityMeasure`; its witness's numbers are order LEAN-31's check
  `104.r6`); its hypotheses are the others of `variance_average_le_of_steady`, with the rows
  above. The start and the recursion (`hx0`, `hx`) define the model; they are not shown needed by
  a case.

**The combinatorics bridge.** `S n = ∑ i, j < n, ρ ^ |i - j|` satisfies the order-3 recurrence
`S (n + 3) = (2 + ρ) S (n + 2) - (1 + 2 ρ) S (n + 1) + ρ S n` for every `ρ`, `ρ = 1` included
(`isSolution_sumSumPow`, with the recurrence `sumSumPowRec ρ`), and its generating function is
rational: `recDenom (sumSumPowRec ρ) · ∑ S n Xⁿ = X + ρ X²` (`recDenom_mul_mk_sumSumPow`, through
`Combinatorics/RecurrenceGeneratingFunction`). The steps are `sum_sum_pow_succ` (a new row and a
new column) and `sum_pow_sub_succ`. The generating-function proof sets
`backward.isDefEq.respectTransparency false`, as that module explains; without it the coefficients
at indices 1 and 2 are not closed (measured 2026-10-09). `recDenom (sumSumPowRec ρ)` is
`(1 - X)² (1 - ρ X)`; review r6 of order LEAN-16 checked that identity in its own scratch file,
outside the library, and it is not stated here.

**The variance of a sum for a covariance-stationary series** (order LEAN-27, item 80). When the
covariances depend only on the lag, `cov (X i, X j) = γ |i - j|`, the double sum of covariances
collapses (`sum_sum_lag_eq`, for any `γ : ℕ → ℝ`) and
`Var (X 0 + ⋯ + X (k - 1)) = k γ 0 + 2 ∑_{1 ≤ j < k} (k - j) γ j`
(`variance_sum_eq_of_stationary`); dividing by `k γ 0` gives the variance-ratio identity
`1 + 2 ∑_{1 ≤ j < k} (1 - j / k) ρ j` with `ρ j = γ j / γ 0` (`variance_sum_div_eq`). Only the
`γ j` with `j < k` enter. Checked exactly on an MA(1) series (`X t = Z t + Z (t - 1)`, `γ = (2, 1,
0, …)`, `k = 1, …, 6`) in order LEAN-27's `checks.py`. Which hypotheses are needed:

* `k ≥ 1` and `γ 0 ≠ 0` for the ratio: at `k = 0` the left side is Lean's `0 / 0 = 0` and the right
  side `1`; with `X = 0`, `γ = 0`, `k = 2` the same (`checks.py`).
* The covariance condition: for the sum, `X 0 = X 1` with variance `1` and `γ = 0`, `k = 2`, gives
  `4` against `0`; for the ratio (keeping `γ 0 ≠ 0`, cold review r80), the same `X` with
  `γ = (1, 0)` gives `4 / 2 = 2` against `1 + 2 · (1/2) · 0 = 1` (`checks.py`; `γ = (2, 0)` would
  give `1` against `1`, so `γ 0 = 1` matters).
* `MemLp (X i) 2` (finite variances), for the sum, by hand, not computed: take `X 0` outside `L²`
  and `X 1 = Y − X 0` with `Y` in `L²` of mean `0` and variance `1`. Then the self-covariances of
  `X 0` and `X 1` and, here, the cross-covariances are Lean's junk `0`, the integral of a
  non-integrable function (with `a = X 0 − μ[X 0]` and `b = Y − μ[Y]`: where `|a| ≥ 2 |b|`,
  `|a (b − a)| ≥ a² / 2`, and elsewhere `a² ≤ 4 b²`, so `a²` and `a (b − a)` are not integrable, and
  neither is `(b − a)²`, since `a² ≤ 2 (b − a)² + 2 b²`; cold review r80), so `γ = 0` meets the
  covariance condition, while `X 0 + X 1 = Y` has variance `1`. Not every covariance with a quantity
  outside `L²` is junk: `cov (X 0, Y)` for a bounded `Y` can be an honest nonzero integral. For the
  ratio, not shown needed by a case: for a measurable `X`, the covariance condition at `(i, i)` with
  `γ 0 ≠ 0` already puts `X i` in `L²`; kept because `variance_fun_sum` asks for it.

The ratio's two hypotheses `k ≥ 1` and `γ 0 ≠ 0` are only for the division. The plan's product form
`Var (X 0 + ⋯ + X (k - 1)) = k γ 0 (1 + 2 ∑_{1 ≤ j < k} (1 − j / k) ρ j)` is
`variance_sum_eq_mul_one_add` (order LEAN-28, item 80b), with the hypotheses of
`variance_sum_eq_of_stationary` only, no extra hypothesis. At `k = 0` both sides are `0`. When
`γ 0 ≠ 0` it is the sum form multiplied out. When `γ 0 = 0`, `X 0` has variance `0`, so it equals
its integral almost everywhere (Mathlib's `ae_eq_integral_of_variance_eq_zero`), every
`cov (X 0, X j) = γ j` is `0`, and both sides are `0`. That step is needed: with `γ 0 = 0` and some
`γ j ≠ 0` the two forms differ (`k = 2`, `γ = (0, 1)`: product `0`, sum `2`; order LEAN-28's
`LEAN-28-check80b.py`, exact), but no series has such covariances. Its hypotheses are needed as the
sum's are: dropping `MemLp` gives the sum's case above (left side `1`, Lean's junk covariances `0`,
the integral of a non-integrable function, so `γ = 0` and the product form is `0`); dropping the
covariance condition, `X 0 = X 1` with variance `1` and `γ = 0`, `k = 2`, gives `4` against `0`. The
finite measure is needed by the sum and the product form alike (cold review r80b; the `∞`
`example` at the end of the module):
with masses `1`, `1` and `∞` on three points, `X 0` the indicator of the first and `X 1` minus the
indicator of the second, each centred product is a nonzero constant on the point of infinite mass,
so every covariance is Lean's junk `0` (the integral of a non-integrable function) and `γ = 0` meets
the covariance condition, while the sum has integral `0` and variance `2`; both forms give `0`.

A series indexed by `ℕ`, `X : ℕ → Ω → ℝ`, with the sum over `range k`, is
`variance_sum_range_eq_of_stationary` (for item 115 of the plan, cold review r80); the sum's rows
above apply to it unchanged, and its `example` meets its hypotheses.

The hypotheses of `variance_sum_eq_of_stationary`, `variance_sum_div_eq` and
`variance_sum_eq_mul_one_add` can be met together, with `γ 0 ≠ 0` and a lag `γ 1 ≠ 0`: their
witnesses at the end of the module (three points of mass one, `X 0 = (1, −1, 0)`,
`X 1 = (0, 1, −1)`, `γ = (2, −1, 0, …)`: `Var (X 0 + X 1) = 2 = 2 · 2 + 2 · 1 · (−1)`).

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

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]

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

omit [IsFiniteMeasure μ] in
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

/-- A new row and a new column: the double sum of `ρ ^ |i - j|` over `i, j < n + 1` is the sum over
`i, j < n`, plus twice `∑ i < n, ρ ^ (n - i)`, plus `1`. -/
lemma sum_sum_pow_succ (ρ : ℝ) (n : ℕ) :
    ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), ρ ^ (max i j - min i j) =
      ∑ i ∈ range n, ∑ j ∈ range n, ρ ^ (max i j - min i j) +
        2 * ∑ i ∈ range n, ρ ^ (n - i) + 1 := by
  have hcol : ∑ i ∈ range n, ρ ^ (max i n - min i n) = ∑ i ∈ range n, ρ ^ (n - i) :=
    sum_congr rfl fun i hi ↦ by
      rw [max_eq_right (mem_range.mp hi).le, min_eq_left (mem_range.mp hi).le]
  have hrow : ∑ j ∈ range n, ρ ^ (max n j - min n j) = ∑ j ∈ range n, ρ ^ (n - j) :=
    sum_congr rfl fun j hj ↦ by
      rw [max_eq_left (mem_range.mp hj).le, min_eq_right (mem_range.mp hj).le]
  rw [sum_range_succ, sum_range_succ (fun j ↦ ρ ^ (max n j - min n j)), max_self, min_self,
    Nat.sub_self, pow_zero, hrow]
  simp_rw [sum_range_succ (fun j ↦ ρ ^ (max _ j - min _ j))]
  rw [sum_add_distrib, hcol]
  ring

/-- `∑ i < n + 1, ρ ^ (n + 1 - i) = ρ ∑ i < n, ρ ^ (n - i) + ρ`. -/
lemma sum_pow_sub_succ (ρ : ℝ) (n : ℕ) :
    ∑ i ∈ range (n + 1), ρ ^ (n + 1 - i) = ρ * ∑ i ∈ range n, ρ ^ (n - i) + ρ := by
  rw [sum_range_succ, Nat.add_sub_cancel_left, pow_one, mul_sum]
  congr 1
  refine sum_congr rfl fun i hi ↦ ?_
  rw [Nat.sub_add_comm (mem_range.mp hi).le, pow_succ, mul_comm]

/-- **The double sum of `ρ ^ |i - j|`** over `i, j < n`, in closed form, for `ρ ≠ 1`. -/
theorem sum_sum_pow_eq {ρ : ℝ} (h1 : ρ ≠ 1) (n : ℕ) :
    ∑ i ∈ range n, ∑ j ∈ range n, ρ ^ (max i j - min i j) =
      n * (1 + ρ) / (1 - ρ) - 2 * ρ * (1 - ρ ^ n) / (1 - ρ) ^ 2 := by
  have hρ : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_sum_pow_succ, ih, sum_range_pow_sub h1]
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

/-! ### The combinatorics bridge: a recurrence and a rational generating function -/

/-- The order-3 recurrence of `S n = ∑ i, j < n, ρ ^ |i - j|`. -/
noncomputable def sumSumPowRec (ρ : ℝ) : LinearRecurrence ℝ := ⟨3, ![ρ, -(1 + 2 * ρ), 2 + ρ]⟩

/-- The double sum `S n = ∑ i, j < n, ρ ^ |i - j|` satisfies the recurrence `sumSumPowRec ρ`:
`S (n + 3) = ρ S n - (1 + 2 ρ) S (n + 1) + (2 + ρ) S (n + 2)`, for every `ρ`. -/
theorem isSolution_sumSumPow (ρ : ℝ) :
    (sumSumPowRec ρ).IsSolution fun n ↦ ∑ i ∈ range n, ∑ j ∈ range n, ρ ^ (max i j - min i j) := by
  intro n
  set S : ℕ → ℝ := fun n ↦ ∑ i ∈ range n, ∑ j ∈ range n, ρ ^ (max i j - min i j)
  set T : ℕ → ℝ := fun n ↦ ∑ i ∈ range n, ρ ^ (n - i)
  have hS : ∀ n, S (n + 1) = S n + 2 * T n + 1 := fun n ↦ sum_sum_pow_succ ρ n
  have hT : ∀ n, T (n + 1) = ρ * T n + ρ := fun n ↦ sum_pow_sub_succ ρ n
  have h1 := hS n
  have h2 := hS (n + 1)
  have h3 := hS (n + 2)
  have t1 := hT n
  have t2 := hT (n + 1)
  change S (n + 3) = ∑ i : Fin 3, ![ρ, -(1 + 2 * ρ), 2 + ρ] i * S (n + i)
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, add_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  linear_combination h3 + 2 * t2 - (1 + ρ) * h2 - 2 * t1 + ρ * h1

set_option backward.isDefEq.respectTransparency false in
/-- Its generating function: `(1 - X)² (1 - ρ X) ∑ S n Xⁿ = X + ρ X²`, the first factor being
`recDenom (sumSumPowRec ρ)`. -/
theorem recDenom_mul_mk_sumSumPow (ρ : ℝ) :
    ClassicalLean.recDenom (sumSumPowRec ρ) *
        PowerSeries.mk (fun n ↦ ∑ i ∈ range n, ∑ j ∈ range n, ρ ^ (max i j - min i j)) =
      PowerSeries.X + PowerSeries.C ρ * PowerSeries.X ^ 2 := by
  ext n
  rcases lt_or_ge n 3 with hn | hn
  · interval_cases n <;>
      simp [ClassicalLean.recDenom, sumSumPowRec, Fin.sum_univ_three, sub_mul, add_mul, mul_assoc,
        PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X, PowerSeries.coeff_X_pow,
        sum_range_succ]
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    have h := (ClassicalLean.isSolution_iff_coeff_recDenom_mul_mk (sumSumPowRec ρ) _).mp
      (isSolution_sumSumPow ρ) k
    have ho : (sumSumPowRec ρ).order = 3 := rfl
    rw [ho] at h
    rw [h]
    simp [PowerSeries.coeff_X, PowerSeries.coeff_X_pow]

/-! ### The average of a steady first-order recursion (order LEAN-17) -/

omit [IsFiniteMeasure μ] in
/-- In a steady first-order recursion (noise variance `s²`, `a² ≠ 1`, steady start), the
covariances are `s² / (1 - a²) · a ^ |i - j|`. -/
theorem covariance_eq_of_steady [IsProbabilityMeasure μ] {Z x : ℕ → Ω → ℝ} {a s : ℝ}
    (hZ : ∀ i, Measurable (Z i)) (hZ2 : ∀ i, MemLp (Z i) 2 μ) (hind : iIndepFun Z μ)
    (hx0 : x 0 = Z 0) (hx : ∀ t ω, x (t + 1) ω = a * x t ω + Z (t + 1) ω) (ha : a ^ 2 ≠ 1)
    (hvar : ∀ t, variance (Z (t + 1)) μ = s ^ 2) (hstart : variance (x 0) μ = s ^ 2 / (1 - a ^ 2))
    (i j : ℕ) : cov[x i, x j; μ] = s ^ 2 / (1 - a ^ 2) * a ^ (max i j - min i j) := by
  have hv := LinearPrediction.variance_eq_steady hZ hZ2 hind hx0 hx ha hvar hstart
  rcases le_total i j with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [LinearPrediction.covariance_add hZ hZ2 hind hx0 hx, hv, max_eq_right h, min_eq_left h,
      Nat.add_sub_cancel_left, mul_comm]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [covariance_comm, LinearPrediction.covariance_add hZ hZ2 hind hx0 hx, hv, max_eq_left h,
      min_eq_right h, Nat.add_sub_cancel_left, mul_comm]

omit [IsFiniteMeasure μ] in
/-- **The variance of the average of a steady first-order recursion, exactly.** For
`x (t + 1) = a x t + Z (t + 1)` with the start and the noises jointly independent, noise variance
`s²`, `a² ≠ 1` and the steady start `Var x 0 = s² / (1 - a²)`, the average of `x 0, …, x (n - 1)`
has variance `s² / (1 - a²) · ∑ i, j < n, a ^ |i - j| / n²`. -/
theorem variance_average_eq_of_steady [IsProbabilityMeasure μ] {Z x : ℕ → Ω → ℝ} {a s : ℝ}
    (hZ : ∀ i, Measurable (Z i))
    (hZ2 : ∀ i, MemLp (Z i) 2 μ) (hind : iIndepFun Z μ) (hx0 : x 0 = Z 0)
    (hx : ∀ t ω, x (t + 1) ω = a * x t ω + Z (t + 1) ω) (ha : a ^ 2 ≠ 1)
    (hvar : ∀ t, variance (Z (t + 1)) μ = s ^ 2) (hstart : variance (x 0) μ = s ^ 2 / (1 - a ^ 2))
    (n : ℕ) :
    Var[fun ω ↦ (∑ t ∈ range n, x t ω) / n; μ] =
      s ^ 2 / (1 - a ^ 2) * (∑ i ∈ range n, ∑ j ∈ range n, a ^ (max i j - min i j)) / n ^ 2 := by
  have hL2 : ∀ t, MemLp (x t) 2 μ := FirstOrderRecursion.memLp_two (e := fun t ↦ Z (t + 1)) hx
    (hx0 ▸ hZ2 0) (fun t ↦ hZ2 (t + 1))
  have h := variance_average (μ := μ) (X := fun i : Fin n ↦ x i) fun i ↦ hL2 i
  rw [Fintype.card_fin] at h
  have hf : (fun ω ↦ (∑ t ∈ range n, x t ω) / n) = fun ω ↦ (∑ i : Fin n, x i ω) / n := by
    funext ω; rw [Fin.sum_univ_eq_sum_range (fun t ↦ x t ω) n]
  rw [hf, h]
  simp_rw [covariance_eq_of_steady hZ hZ2 hind hx0 hx ha hvar hstart, ← mul_sum]
  congr 2
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ ∑ j : Fin n, a ^ (max i (j : ℕ) - min i (j : ℕ))) n]
  exact sum_congr rfl fun i _ ↦ Fin.sum_univ_eq_sum_range (fun j ↦ a ^ (max i j - min i j)) n

omit [IsFiniteMeasure μ] in
/-- **The variance of the average of a steady first-order recursion, bounded.** Under the same
hypotheses with `0 ≤ a < 1`, the average of `n` values has variance at most `s² / ((1 - a)² n)`:
the `n` values are worth at least `n (1 - a)² / (1 - a²) = n (1 - a) / (1 + a)` independent
ones. -/
theorem variance_average_le_of_steady [IsProbabilityMeasure μ] {Z x : ℕ → Ω → ℝ} {a s : ℝ}
    (hZ : ∀ i, Measurable (Z i))
    (hZ2 : ∀ i, MemLp (Z i) 2 μ) (hind : iIndepFun Z μ) (hx0 : x 0 = Z 0)
    (hx : ∀ t ω, x (t + 1) ω = a * x t ω + Z (t + 1) ω) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hvar : ∀ t, variance (Z (t + 1)) μ = s ^ 2) (hstart : variance (x 0) μ = s ^ 2 / (1 - a ^ 2))
    (n : ℕ) :
    Var[fun ω ↦ (∑ t ∈ range n, x t ω) / n; μ] ≤ s ^ 2 / ((1 - a) ^ 2 * n) := by
  have ha : a ^ 2 ≠ 1 := by nlinarith
  have hpos : 0 < 1 - a ^ 2 := by nlinarith
  have hL2 : ∀ t, MemLp (x t) 2 μ := FirstOrderRecursion.memLp_two (e := fun t ↦ Z (t + 1)) hx
    (hx0 ▸ hZ2 0) (fun t ↦ hZ2 (t + 1))
  set σ := Real.sqrt (s ^ 2 / (1 - a ^ 2))
  have hσ : σ ^ 2 = s ^ 2 / (1 - a ^ 2) := Real.sq_sqrt (div_nonneg (sq_nonneg s) hpos.le)
  have h := variance_average_le_of_cov_eq (μ := μ) (X := fun i : Fin n ↦ x i)
    (fun i ↦ hL2 i) (σ := σ) ha0 ha1 fun i j ↦ by
      rw [hσ]; exact covariance_eq_of_steady hZ hZ2 hind hx0 hx ha hvar hstart i j
  have hf : (fun ω ↦ (∑ t ∈ range n, x t ω) / n) = fun ω ↦ (∑ i : Fin n, x i ω) / n := by
    funext ω; rw [Fin.sum_univ_eq_sum_range (fun t ↦ x t ω) n]
  rw [hf]
  refine h.trans (le_of_eq ?_)
  rw [hσ]
  have h1 : (1 : ℝ) - a ≠ 0 := by linarith
  have h2 : (1 : ℝ) + a ≠ 0 := by linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    ring

/-- **The variance of the average of a steady first-order recursion, bounded, with no measure
instance** (order LEAN-31, item 104 of MATH-PLAN-library-2; review r6 of order LEAN-17).
`variance_average_le_of_steady` with no `[IsProbabilityMeasure μ]`: the independence of the noises
gives it (`iIndepFun.isProbabilityMeasure`). -/
theorem variance_average_le_of_steady' {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {Z x : ℕ → Ω → ℝ} {a s : ℝ}
    (hZ : ∀ i, Measurable (Z i))
    (hZ2 : ∀ i, MemLp (Z i) 2 μ) (hind : iIndepFun Z μ) (hx0 : x 0 = Z 0)
    (hx : ∀ t ω, x (t + 1) ω = a * x t ω + Z (t + 1) ω) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hvar : ∀ t, variance (Z (t + 1)) μ = s ^ 2) (hstart : variance (x 0) μ = s ^ 2 / (1 - a ^ 2))
    (n : ℕ) :
    Var[fun ω ↦ (∑ t ∈ range n, x t ω) / n; μ] ≤ s ^ 2 / ((1 - a) ^ 2 * n) := by
  have := hind.isProbabilityMeasure
  exact variance_average_le_of_steady hZ hZ2 hind hx0 hx ha0 ha1 hvar hstart n

/-! ### The variance of a sum for a covariance-stationary series (items 80 and 80b) -/

omit [IsFiniteMeasure μ] in
/-- A new row and a new column: the double sum of `γ |i - j|` over `i, j < n + 1` is the sum over
`i, j < n`, plus twice `∑ i < n, γ (n - i)`, plus `γ 0`. -/
lemma sum_sum_lag_succ (γ : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), γ (max i j - min i j) =
      ∑ i ∈ range n, ∑ j ∈ range n, γ (max i j - min i j) +
        2 * ∑ i ∈ range n, γ (n - i) + γ 0 := by
  have hcol : ∑ i ∈ range n, γ (max i n - min i n) = ∑ i ∈ range n, γ (n - i) :=
    sum_congr rfl fun i hi ↦ by
      rw [max_eq_right (mem_range.mp hi).le, min_eq_left (mem_range.mp hi).le]
  have hrow : ∑ j ∈ range n, γ (max n j - min n j) = ∑ j ∈ range n, γ (n - j) :=
    sum_congr rfl fun j hj ↦ by
      rw [max_eq_left (mem_range.mp hj).le, min_eq_right (mem_range.mp hj).le]
  rw [sum_range_succ, sum_range_succ (fun j ↦ γ (max n j - min n j)), max_self, min_self,
    Nat.sub_self, hrow]
  simp_rw [sum_range_succ (fun j ↦ γ (max _ j - min _ j))]
  rw [sum_add_distrib, hcol]
  ring

omit [IsFiniteMeasure μ] in
/-- `∑ i, j < k, γ |i - j| = 2 ∑ j < k, (k - j) γ j - k γ 0`. -/
lemma sum_sum_lag_eq_range (γ : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ range k, ∑ j ∈ range k, γ (max i j - min i j) =
      2 * ∑ j ∈ range k, ((k : ℝ) - j) * γ j - k * γ 0 := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hrefl : ∑ i ∈ range (n + 1), γ (n - i) = ∑ j ∈ range (n + 1), γ j := by
      have := sum_range_reflect γ (n + 1)
      simpa only [Nat.add_sub_cancel] using this
    rw [sum_range_succ (fun i ↦ γ (n - i)), Nat.sub_self] at hrefl
    rw [sum_sum_lag_succ, ih, sum_range_succ (fun j ↦ ((↑(n + 1) : ℝ) - j) * γ j)]
    have hw : ∑ j ∈ range n, ((↑(n + 1) : ℝ) - j) * γ j =
        ∑ j ∈ range n, ((n : ℝ) - j) * γ j + ∑ j ∈ range n, γ j := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun j _ ↦ by push_cast; ring
    rw [hw, sum_range_succ γ n] at *
    push_cast
    linarith

omit [IsFiniteMeasure μ] in
/-- **The double sum of lagged values.** For any `γ : ℕ → ℝ`,
`∑ i, j < k, γ |i - j| = k γ 0 + 2 ∑_{1 ≤ j < k} (k - j) γ j`. -/
theorem sum_sum_lag_eq (γ : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ range k, ∑ j ∈ range k, γ (max i j - min i j) =
      k * γ 0 + 2 * ∑ j ∈ Ico 1 k, ((k : ℝ) - j) * γ j := by
  rw [sum_sum_lag_eq_range]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [sum_range_eq_add_Ico _ hk]
    push_cast
    ring

/-- **The variance of a sum of a covariance-stationary series** (order LEAN-27, item 80): when
`cov (X i, X j) = γ |i - j|`, `Var (X 0 + ⋯ + X (k - 1)) = k γ 0 + 2 ∑_{1 ≤ j < k} (k - j) γ j`. -/
theorem variance_sum_eq_of_stationary {k : ℕ} {X : Fin k → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ)
    {γ : ℕ → ℝ} (hcov : ∀ i j : Fin k, cov[X i, X j; μ] = γ (max (i : ℕ) j - min (i : ℕ) j)) :
    Var[fun ω ↦ ∑ i, X i ω; μ] = k * γ 0 + 2 * ∑ j ∈ Ico 1 k, ((k : ℝ) - j) * γ j := by
  rw [variance_fun_sum hX, ← sum_sum_lag_eq]
  simp_rw [hcov]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ ∑ j : Fin k, γ (max i (j : ℕ) - min i (j : ℕ))) k]
  exact sum_congr rfl fun i _ ↦ Fin.sum_univ_eq_sum_range (fun j ↦ γ (max i j - min i j)) k

/-- **The variance-ratio identity.** With `k ≥ 1` and `γ 0 ≠ 0`, and `ρ j = γ j / γ 0`:
`Var (X 0 + ⋯ + X (k - 1)) / (k γ 0) = 1 + 2 ∑_{1 ≤ j < k} (1 - j / k) ρ j`. -/
theorem variance_sum_div_eq {k : ℕ} {X : Fin k → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ)
    {γ : ℕ → ℝ} (hcov : ∀ i j : Fin k, cov[X i, X j; μ] = γ (max (i : ℕ) j - min (i : ℕ) j))
    (hk : 0 < k) (hγ : γ 0 ≠ 0) :
    Var[fun ω ↦ ∑ i, X i ω; μ] / (k * γ 0) =
      1 + 2 * ∑ j ∈ Ico 1 k, (1 - (j : ℝ) / k) * (γ j / γ 0) := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  rw [variance_sum_eq_of_stationary hX hcov, add_div, div_self (mul_ne_zero hk' hγ),
    mul_div_assoc, sum_div]
  congr 2
  refine sum_congr rfl fun j _ ↦ ?_
  field_simp

/-- **The variance-ratio identity in product form** (order LEAN-28, item 80b): when
`cov (X i, X j) = γ |i - j|`, with `ρ j = γ j / γ 0`,
`Var (X 0 + ⋯ + X (k - 1)) = k γ 0 (1 + 2 ∑_{1 ≤ j < k} (1 - j / k) ρ j)`, with no hypothesis beyond
those of `variance_sum_eq_of_stationary`. When `γ 0 = 0` (Lean's `γ j / 0 = 0`) the series has every
`γ j = 0` for `j < k`, since `X 0` is then almost everywhere constant. -/
theorem variance_sum_eq_mul_one_add {k : ℕ} {X : Fin k → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ)
    {γ : ℕ → ℝ} (hcov : ∀ i j : Fin k, cov[X i, X j; μ] = γ (max (i : ℕ) j - min (i : ℕ) j)) :
    Var[fun ω ↦ ∑ i, X i ω; μ] =
      k * γ 0 * (1 + 2 * ∑ j ∈ Ico 1 k, (1 - (j : ℝ) / k) * (γ j / γ 0)) := by
  rw [variance_sum_eq_of_stationary hX hcov]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  by_cases hγ : γ 0 = 0
  · -- `X 0` has variance `0`, so every lag covariance `γ j = cov (X 0, X j)` is `0`
    have hv : Var[X ⟨0, hk⟩; μ] = 0 := by
      rw [← covariance_self (hX _).aemeasurable, hcov]
      simpa using hγ
    have hae := ae_eq_integral_of_variance_eq_zero (hX ⟨0, hk⟩) hv
    have h0 : ∀ j < k, γ j = 0 := by
      intro j hj
      have hc := hcov ⟨0, hk⟩ ⟨j, hj⟩
      simp only [zero_le, max_eq_right, min_eq_left, Nat.sub_zero] at hc
      rw [← hc, covariance]
      refine (integral_congr_ae ?_).trans (integral_zero _ _)
      filter_upwards [hae] with ω hω
      simp [hω]
    have hsum : ∑ j ∈ Ico 1 k, ((k : ℝ) - j) * γ j = 0 :=
      sum_eq_zero fun j hj ↦ by rw [h0 j (mem_Ico.mp hj).2, mul_zero]
    rw [hsum, hγ]
    ring
  · have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    have e : ∀ j ∈ Ico 1 k, ((k : ℝ) - j) * γ j = k * γ 0 * ((1 - (j : ℝ) / k) * (γ j / γ 0)) :=
      fun j _ ↦ by field_simp
    rw [sum_congr rfl e, ← mul_sum]
    ring

/-- The variance of a sum for a covariance-stationary series indexed by `ℕ`: the same identity
with `X : ℕ → Ω → ℝ` and the sum over `range k` (cold review r80, for item 115). -/
theorem variance_sum_range_eq_of_stationary {k : ℕ} {X : ℕ → Ω → ℝ}
    (hX : ∀ i < k, MemLp (X i) 2 μ) {γ : ℕ → ℝ}
    (hcov : ∀ i < k, ∀ j < k, cov[X i, X j; μ] = γ (max i j - min i j)) :
    Var[fun ω ↦ ∑ i ∈ range k, X i ω; μ] = k * γ 0 + 2 * ∑ j ∈ Ico 1 k, ((k : ℝ) - j) * γ j := by
  have h := variance_sum_eq_of_stationary (X := fun i : Fin k ↦ X i) (fun i ↦ hX i i.isLt)
    (fun i j ↦ hcov i i.isLt j j.isLt)
  have hfun : (fun ω ↦ ∑ i ∈ range k, X i ω) = fun ω ↦ ∑ i : Fin k, X i ω :=
    funext fun ω ↦ (Fin.sum_univ_eq_sum_range (fun i ↦ X i ω) k).symm
  rw [hfun]
  exact h

open scoped ENNReal in
/-- **Why `variance_sum_eq_of_stationary` and `variance_sum_eq_mul_one_add` need the finite
measure** (cold review r80b): masses `1`, `1` and `∞` on three points, `X 0` the indicator of the
first point and `X 1` minus the indicator of the second. Both are in `L²`, every covariance is
Lean's junk `0` (the integral of a non-integrable function, as each centred product is a nonzero
constant on the point of infinite mass), so `γ = 0` meets the covariance condition with `k = 2`;
the sum has variance `2`, and the sum form and the product form both give `0`. -/
example : ∃ (μ : Measure (Fin 3)) (X : Fin 2 → Fin 3 → ℝ) (γ : ℕ → ℝ), ¬ IsFiniteMeasure μ ∧
    (∀ i, MemLp (X i) 2 μ) ∧
    (∀ i j : Fin 2, cov[X i, X j; μ] = γ (max (i : ℕ) j - min (i : ℕ) j)) ∧
    Var[fun ω ↦ ∑ i, X i ω; μ] = 2 ∧
    ((2 : ℕ) : ℝ) * γ 0 + 2 * ∑ j ∈ Ico (1 : ℕ) 2, (((2 : ℕ) : ℝ) - j) * γ j = 0 ∧
    ((2 : ℕ) : ℝ) * γ 0 *
      (1 + 2 * ∑ j ∈ Ico (1 : ℕ) 2, (1 - (j : ℝ) / (2 : ℕ)) * (γ j / γ 0)) = 0 := by
  set ν : Measure (Fin 3) := Measure.dirac 0 + Measure.dirac 1 + (∞ : ℝ≥0∞) • Measure.dirac 2
    with hν
  have hlint : ∀ g : Fin 3 → ℝ≥0∞, ∫⁻ ω, g ω ∂ν = g 0 + g 1 + ∞ * g 2 := fun g ↦ by
    simp [hν, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac]
  -- a function is integrable exactly when it is `0` at the point of infinite mass
  have hint : ∀ f : Fin 3 → ℝ, Integrable f ν ↔ f 2 = 0 := fun f ↦ by
    refine ⟨fun h ↦ ?_, fun h ↦ ⟨(measurable_of_finite f).aestronglyMeasurable, ?_⟩⟩
    · have h2 : ∫⁻ ω, ‖f ω‖ₑ ∂ν < ∞ := h.2
      rw [hlint] at h2
      by_contra hne
      rw [ENNReal.top_mul (by simpa using hne)] at h2
      simp at h2
    · change ∫⁻ ω, ‖f ω‖ₑ ∂ν < ∞
      rw [hlint, h]
      simp
  have hinteg : ∀ f : Fin 3 → ℝ, f 2 = 0 → ∫ ω, f ω ∂ν = f 0 + f 1 := fun f h ↦ by
    have hI := (hint f).mpr h
    rw [hν] at hI ⊢
    obtain ⟨h01, h2⟩ := integrable_add_measure.mp hI
    rw [integral_add_measure h01 h2, integral_smul_measure]
    simp [integral_add_measure, Integrable.of_finite, h]
  set X : Fin 2 → Fin 3 → ℝ :=
    ![fun ω ↦ if ω = 0 then 1 else 0, fun ω ↦ if ω = 1 then -1 else 0] with hX
  have hX2 : ∀ i, X i 2 = 0 := fun i ↦ by fin_cases i <;> simp [hX]
  have hmean : ∀ i, ∫ ω, X i ω ∂ν ≠ 0 := fun i ↦ by
    rw [hinteg _ (hX2 i)]
    fin_cases i <;> simp [hX]
  refine ⟨ν, X, fun _ ↦ 0, fun h ↦ ?_, fun i ↦ ?_, fun i j ↦ ?_, ?_, by simp, by simp⟩
  · have := measure_lt_top ν Set.univ
    rw [← lintegral_one, hlint] at this
    simp at this
  · rw [memLp_two_iff_integrable_sq (measurable_of_finite _).aestronglyMeasurable, hint]
    simp [hX2 i]
  · rw [covariance]
    apply integral_undef
    rw [hint]
    simp [hX2 i, hX2 j, hmean i, hmean j]
  · have hS : ∫ ω, (∑ i, X i ω) ∂ν = 0 := by
      rw [hinteg (fun ω ↦ ∑ i, X i ω) (by simp [hX2])]
      simp [hX]
    simp only [variance, evariance]
    rw [hS, hlint]
    simp [hX]
    norm_num

end ClassicalLean.Probability.EffectiveSampleSize

/-- The hypotheses of `variance_average_le_of_steady'` hold together: with no measure instance
supplied, on `ℕ → ℝ`, the product of the Gaussian laws `N(0, 4/3)` for coordinate `0` and
`N(0, 1)` for every later one (`Measure.infinitePi`, a probability measure); the noises `Z i` the
coordinates, independent (`iIndepFun_infinitePi`); the recursion `x (t + 1) = x t / 2 + Z (t + 1)`
started at `x 0 = Z 0`, so `a = 1/2`, `s = 1`, and the start has the steady variance
`4/3 = 1 / (1 - 1/4)`, which is positive; `n = 3`. -/
example := ClassicalLean.Probability.EffectiveSampleSize.variance_average_le_of_steady'
  (Ω := ℕ → ℝ)
  (μ := Measure.infinitePi fun i : ℕ ↦
    gaussianReal 0 (if i = 0 then (⟨4 / 3, by norm_num⟩ : NNReal) else 1))
  (Z := fun i ω ↦ ω i)
  (x := fun t ↦ Nat.rec (motive := fun _ ↦ (ℕ → ℝ) → ℝ) (fun ω ↦ ω 0)
    (fun k xk ω ↦ 1 / 2 * xk ω + ω (k + 1)) t)
  (a := 1 / 2) (s := 1)
  (fun i ↦ measurable_pi_apply i)
  (fun i ↦ by
    have h : MemLp id 2 ((Measure.infinitePi fun i : ℕ ↦
        gaussianReal 0 (if i = 0 then (⟨4 / 3, by norm_num⟩ : NNReal) else 1)).map
          (fun ω ↦ ω i)) := by
      rw [Measure.infinitePi_map_eval]
      exact memLp_id_gaussianReal' 2 (by norm_num)
    exact (memLp_map_measure_iff aestronglyMeasurable_id (measurable_pi_apply i).aemeasurable).mp h)
  (iIndepFun_infinitePi (X := fun _ ↦ id) fun _ ↦ measurable_id)
  rfl (fun _ _ ↦ rfl) (by norm_num) (by norm_num)
  (fun t ↦ by
    rw [← variance_id_map (measurable_pi_apply (t + 1)).aemeasurable, Measure.infinitePi_map_eval,
      variance_id_gaussianReal]
    simp)
  (by
    change Var[fun ω : ℕ → ℝ ↦ ω 0; _] = _
    rw [← variance_id_map (measurable_pi_apply 0).aemeasurable, Measure.infinitePi_map_eval,
      variance_id_gaussianReal]
    norm_num
    rfl)
  (n := 3)

/-- The hypotheses of `variance_average_eq_of_steady` hold together: on `ℕ → ℝ`, the product of
the Gaussian laws `N(0, 4/3)` for coordinate `0` and `N(0, 1)` for every later one
(`Measure.infinitePi`, a probability measure, whose instance Lean finds); the noises `Z i` the
coordinates, independent (`iIndepFun_infinitePi`); the recursion `x (t + 1) = x t / 2 + Z (t + 1)`
started at `x 0 = Z 0`, so `a = 1/2` (and `a² ≠ 1`), `s = 1`, and the start has the steady
variance `4/3 = 1 / (1 - 1/4)`; `n = 3`. -/
example := ClassicalLean.Probability.EffectiveSampleSize.variance_average_eq_of_steady
  (Ω := ℕ → ℝ)
  (μ := Measure.infinitePi fun i : ℕ ↦
    gaussianReal 0 (if i = 0 then (⟨4 / 3, by norm_num⟩ : NNReal) else 1))
  (Z := fun i ω ↦ ω i)
  (x := fun t ↦ Nat.rec (motive := fun _ ↦ (ℕ → ℝ) → ℝ) (fun ω ↦ ω 0)
    (fun k xk ω ↦ 1 / 2 * xk ω + ω (k + 1)) t)
  (a := 1 / 2) (s := 1)
  (fun i ↦ measurable_pi_apply i)
  (fun i ↦ by
    have h : MemLp id 2 ((Measure.infinitePi fun i : ℕ ↦
        gaussianReal 0 (if i = 0 then (⟨4 / 3, by norm_num⟩ : NNReal) else 1)).map
          (fun ω ↦ ω i)) := by
      rw [Measure.infinitePi_map_eval]
      exact memLp_id_gaussianReal' 2 (by norm_num)
    exact (memLp_map_measure_iff aestronglyMeasurable_id (measurable_pi_apply i).aemeasurable).mp h)
  (iIndepFun_infinitePi (X := fun _ ↦ id) fun _ ↦ measurable_id)
  rfl (fun _ _ ↦ rfl) (by norm_num)
  (fun t ↦ by
    rw [← variance_id_map (measurable_pi_apply (t + 1)).aemeasurable, Measure.infinitePi_map_eval,
      variance_id_gaussianReal]
    simp)
  (by
    change Var[fun ω : ℕ → ℝ ↦ ω 0; _] = _
    rw [← variance_id_map (measurable_pi_apply 0).aemeasurable, Measure.infinitePi_map_eval,
      variance_id_gaussianReal]
    norm_num
    rfl)
  (n := 3)

/-- The hypotheses of `variance_average_le_of_steady` hold together: the same product of Gaussian
laws on `ℕ → ℝ` (a probability measure, whose instance Lean finds), the same independent noises
and recursion, so `0 ≤ a = 1/2 < 1`, `s = 1` and the steady start `4/3`; `n = 3`. -/
example := ClassicalLean.Probability.EffectiveSampleSize.variance_average_le_of_steady
  (Ω := ℕ → ℝ)
  (μ := Measure.infinitePi fun i : ℕ ↦
    gaussianReal 0 (if i = 0 then (⟨4 / 3, by norm_num⟩ : NNReal) else 1))
  (Z := fun i ω ↦ ω i)
  (x := fun t ↦ Nat.rec (motive := fun _ ↦ (ℕ → ℝ) → ℝ) (fun ω ↦ ω 0)
    (fun k xk ω ↦ 1 / 2 * xk ω + ω (k + 1)) t)
  (a := 1 / 2) (s := 1)
  (fun i ↦ measurable_pi_apply i)
  (fun i ↦ by
    have h : MemLp id 2 ((Measure.infinitePi fun i : ℕ ↦
        gaussianReal 0 (if i = 0 then (⟨4 / 3, by norm_num⟩ : NNReal) else 1)).map
          (fun ω ↦ ω i)) := by
      rw [Measure.infinitePi_map_eval]
      exact memLp_id_gaussianReal' 2 (by norm_num)
    exact (memLp_map_measure_iff aestronglyMeasurable_id (measurable_pi_apply i).aemeasurable).mp h)
  (iIndepFun_infinitePi (X := fun _ ↦ id) fun _ ↦ measurable_id)
  rfl (fun _ _ ↦ rfl) (by norm_num) (by norm_num)
  (fun t ↦ by
    rw [← variance_id_map (measurable_pi_apply (t + 1)).aemeasurable, Measure.infinitePi_map_eval,
      variance_id_gaussianReal]
    simp)
  (by
    change Var[fun ω : ℕ → ℝ ↦ ω 0; _] = _
    rw [← variance_id_map (measurable_pi_apply 0).aemeasurable, Measure.infinitePi_map_eval,
      variance_id_gaussianReal]
    norm_num
    rfl)
  (n := 3)

open MeasureTheory ProbabilityTheory in
/-- The hypotheses of `variance_sum_eq_of_stationary` hold together: three points of mass one each
(a finite measure of mass `3`), `X 0 = (1, -1, 0)` and `X 1 = (0, 1, -1)`, each of integral `0`;
`cov (X 0, X 0) = cov (X 1, X 1) = 2` and `cov (X 0, X 1) = -1`, so `γ = (2, -1, 0, …)`, with
`γ 0 ≠ 0` and a lag `γ 1 ≠ 0`; `X 1 ≠ X 0` at every point, the one step the theorem reads (`k = 2`).
-/
example := ClassicalLean.Probability.EffectiveSampleSize.variance_sum_eq_of_stationary
  (Ω := Fin 3) (μ := Measure.dirac 0 + Measure.dirac 1 + Measure.dirac 2)
  (k := 2) (X := ![![1, -1, 0], ![0, 1, -1]]) (fun _ ↦ MemLp.of_discrete)
  (γ := fun j ↦ if j = 0 then 2 else if j = 1 then -1 else 0)
  (fun i j ↦ by
    fin_cases i <;> fin_cases j <;>
      norm_num [covariance, integral_add_measure, integral_dirac, Integrable.of_finite])

open MeasureTheory ProbabilityTheory in
/-- The hypotheses of `variance_sum_div_eq` hold together: three points of mass one each (a finite
measure of mass `3`), `X 0 = (1, -1, 0)` and `X 1 = (0, 1, -1)`, each of integral `0`;
`cov (X 0, X 0) = cov (X 1, X 1) = 2` and `cov (X 0, X 1) = -1`, so `γ = (2, -1, 0, …)`, with
`γ 0 ≠ 0` and a lag `γ 1 ≠ 0`; `X 1 ≠ X 0` at every point, the one step the theorem reads (`k = 2`);
`k = 2 > 0`. -/
example := ClassicalLean.Probability.EffectiveSampleSize.variance_sum_div_eq
  (Ω := Fin 3) (μ := Measure.dirac 0 + Measure.dirac 1 + Measure.dirac 2)
  (k := 2) (X := ![![1, -1, 0], ![0, 1, -1]]) (fun _ ↦ MemLp.of_discrete)
  (γ := fun j ↦ if j = 0 then 2 else if j = 1 then -1 else 0)
  (fun i j ↦ by
    fin_cases i <;> fin_cases j <;>
      norm_num [covariance, integral_add_measure, integral_dirac, Integrable.of_finite])
  (by norm_num) (by norm_num)

open MeasureTheory ProbabilityTheory in
/-- The hypotheses of `variance_sum_eq_mul_one_add` hold together: three points of mass one each (a
finite measure of mass `3`), `X 0 = (1, -1, 0)` and `X 1 = (0, 1, -1)`, each of integral `0`;
`cov (X 0, X 0) = cov (X 1, X 1) = 2` and `cov (X 0, X 1) = -1`, so `γ = (2, -1, 0, …)`, with
`γ 0 ≠ 0` and a lag `γ 1 ≠ 0`; `X 1 ≠ X 0` at every point, the one step the theorem reads (`k = 2`).
-/
example := ClassicalLean.Probability.EffectiveSampleSize.variance_sum_eq_mul_one_add
  (Ω := Fin 3) (μ := Measure.dirac 0 + Measure.dirac 1 + Measure.dirac 2)
  (k := 2) (X := ![![1, -1, 0], ![0, 1, -1]]) (fun _ ↦ MemLp.of_discrete)
  (γ := fun j ↦ if j = 0 then 2 else if j = 1 then -1 else 0)
  (fun i j ↦ by
    fin_cases i <;> fin_cases j <;>
      norm_num [covariance, integral_add_measure, integral_dirac, Integrable.of_finite])

open MeasureTheory ProbabilityTheory in
/-- The hypotheses of `variance_sum_range_eq_of_stationary` hold together: the same values indexed
by `ℕ`, on three points of mass one each (a finite measure of mass `3`), `X 0 = (1, -1, 0)` and
`X 1 = (0, 1, -1)`, each of integral `0`; `cov (X 0, X 0) = cov (X 1, X 1) = 2` and
`cov (X 0, X 1) = -1`, so `γ = (2, -1, 0, …)`, with `γ 0 ≠ 0` and a lag `γ 1 ≠ 0`; `X 1 ≠ X 0` at
every point, the one step the theorem reads (`k = 2`; only `i < 2` enters); `X` alternates between
the two, so it moves at every step (review (b) group 3 gave the alternation). -/
example := ClassicalLean.Probability.EffectiveSampleSize.variance_sum_range_eq_of_stationary
  (Ω := Fin 3) (μ := Measure.dirac 0 + Measure.dirac 1 + Measure.dirac 2)
  (k := 2) (X := fun i ↦ if i % 2 = 0 then ![1, -1, 0] else ![0, 1, -1])
  (fun _ _ ↦ MemLp.of_discrete)
  (γ := fun j ↦ if j = 0 then 2 else if j = 1 then -1 else 0)
  (fun i hi j hj ↦ by
    interval_cases i <;> interval_cases j <;>
      norm_num [covariance, integral_add_measure, integral_dirac, Integrable.of_finite])
