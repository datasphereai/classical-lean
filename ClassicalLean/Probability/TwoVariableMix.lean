/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.Moments.Variance

/-!
# The variance of a mix of two random variables, and the weight that makes it smallest

* `variance_mix`: `Var[w X + (1 - w) Y] = w² Var X + (1 - w)² Var Y + 2 w (1 - w) Cov(X, Y)`.
* `mixVariance a c k w := w² a + (1 - w)² c + 2 w (1 - w) k` and
  `mixVariance_eq`: `mixVariance a c k w = mixVariance a c k w* + (a + c - 2k) (w - w*)²` with
  `w* = (c - k) / (a + c - 2k)`, so for `a + c - 2k > 0` (that is, `Var[X - Y] > 0`) the weight
  `w*` gives the smallest variance (`mixVariance_minimal`), and it is the only such weight
  (`mixVariance_eq_minimal_iff`).

## What Mathlib provides

`ProbabilityTheory.variance_add` (with the covariance term), `variance_const_mul`,
`covariance_const_mul_left/right`. The library's `Simplex.SecondOrder` and `Statistics.GaussMarkov`
(paired by LEAN-7's scan) work with positive semidefinite matrices and dot products. They were not
needed here: the two-variable case is the algebra of one quadratic. They are where the many-asset
version would start.
-/

open MeasureTheory ProbabilityTheory

namespace ClassicalLean.Probability.TwoVariableMix

/-- **Variance of a two-asset mix.** For square-integrable `X`, `Y` and weight `w`:
`Var[w X + (1 - w) Y] = w² Var X + (1 - w)² Var Y + 2 w (1 - w) Cov(X, Y)`. For a trader: how much
a two-coin portfolio swings, from each coin's swings and how they move together. -/
theorem variance_mix {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (w : ℝ) :
    variance (fun ω ↦ w * X ω + (1 - w) * Y ω) μ =
      w ^ 2 * variance X μ + (1 - w) ^ 2 * variance Y μ + 2 * w * (1 - w) * covariance X Y μ := by
  have hwX : MemLp (fun ω ↦ w * X ω) 2 μ := hX.const_mul w
  have h1wY : MemLp (fun ω ↦ (1 - w) * Y ω) 2 μ := hY.const_mul (1 - w)
  have hsum : (fun ω ↦ w * X ω + (1 - w) * Y ω) = (fun ω ↦ w * X ω) + (fun ω ↦ (1 - w) * Y ω) :=
    rfl
  rw [hsum, variance_add hwX h1wY, variance_const_mul, variance_const_mul,
    covariance_const_mul_left, covariance_const_mul_right]
  ring

/-- The variance of the mix as a function of the weight, from `a = Var X`, `c = Var Y`,
`k = Cov(X, Y)`. -/
def mixVariance (a c k w : ℝ) : ℝ := w ^ 2 * a + (1 - w) ^ 2 * c + 2 * w * (1 - w) * k

/-- The weight that minimises `mixVariance`: `(c - k) / (a + c - 2k)`. -/
noncomputable def minVarianceWeight (a c k : ℝ) : ℝ := (c - k) / (a + c - 2 * k)

/-- `mixVariance a c k w = mixVariance a c k w* + (a + c - 2k) (w - w*)²` when `a + c - 2k ≠ 0`. -/
theorem mixVariance_eq {a c k : ℝ} (h : a + c - 2 * k ≠ 0) (w : ℝ) :
    mixVariance a c k w = mixVariance a c k (minVarianceWeight a c k) +
      (a + c - 2 * k) * (w - minVarianceWeight a c k) ^ 2 := by
  unfold mixVariance minVarianceWeight
  field_simp
  ring

/-- **The minimum-variance weight.** When `a + c - 2k > 0` (the difference of the two assets is
not constant), `w* = (c - k) / (a + c - 2k)` gives the smallest variance of any mix. For a
trader: the split between two coins that swings least is set by their variances and covariance
alone. -/
theorem mixVariance_minimal {a c k : ℝ} (h : 0 < a + c - 2 * k) (w : ℝ) :
    mixVariance a c k (minVarianceWeight a c k) ≤ mixVariance a c k w := by
  rw [mixVariance_eq h.ne' w]
  nlinarith [sq_nonneg (w - minVarianceWeight a c k)]

/-- `w*` is the only minimiser: equality only at `w = w*`. -/
theorem mixVariance_eq_minimal_iff {a c k : ℝ} (h : 0 < a + c - 2 * k) (w : ℝ) :
    mixVariance a c k w = mixVariance a c k (minVarianceWeight a c k) ↔
      w = minVarianceWeight a c k := by
  rw [mixVariance_eq h.ne' w]
  constructor
  · intro he
    have : (a + c - 2 * k) * (w - minVarianceWeight a c k) ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 h.ne'
    · exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
  · rintro rfl; ring

end ClassicalLean.Probability.TwoVariableMix
