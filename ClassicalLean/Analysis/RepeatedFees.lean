/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Proportional deductions repeated many times

A quantity goes through `N` round trips. In trip `i` it is multiplied by a factor `G i`, and a
fraction `f` is deducted on the way in and again on the way out.

* `prod_mul_deductions`: what is left is `(1 - f) ^ (2N) · ∏ G i`.
* `one_le_prod_mul_deductions_iff`: it ends no lower than it started exactly when
  `∏ G i ≥ (1 / (1 - f) ^ 2) ^ N`, that is (`one_le_prod_iff_geomMean`) when the geometric mean of
  the factors is at least `1 / (1 - f) ^ 2`. The threshold per trip does not depend on `N`; the
  arithmetic mean of the factors reaching it is not enough (the geometric mean is the smaller one).
-/

open Finset

namespace ClassicalLean.Analysis.RepeatedFees

/-- **Fee drag over `N` round trips.** `∏ (G i (1 - f)²) = (1 - f) ^ (2N) ∏ G i`. For a trader:
after `N` round trips at fee `f` each way, `(1 - f) ^ (2N)` of what the trades alone would have
made is left (for `f = 0.6 %` and `N = 100`: about 30 %). -/
theorem prod_mul_deductions (G : ℕ → ℝ) (f : ℝ) (N : ℕ) :
    ∏ i ∈ range N, (G i * (1 - f) ^ 2) = (1 - f) ^ (2 * N) * ∏ i ∈ range N, G i := by
  rw [prod_mul_distrib, prod_const, card_range, ← pow_mul, mul_comm]

/-- **Break-even over `N` trips.** For `f < 1`:
`1 ≤ ∏ (G i (1 - f)²) ↔ (1 / (1 - f) ^ 2) ^ N ≤ ∏ G i`.
For a trader: over `N` trades, the trades' own factors must multiply to at least
`(1 / (1 - f)²) ^ N` just to stand still. -/
theorem one_le_prod_mul_deductions_iff (G : ℕ → ℝ) {f : ℝ} (hf : f < 1) (N : ℕ) :
    1 ≤ ∏ i ∈ range N, (G i * (1 - f) ^ 2) ↔ (1 / (1 - f) ^ 2) ^ N ≤ ∏ i ∈ range N, G i := by
  have hpos : 0 < (1 - f) ^ (2 * N) := pow_pos (by linarith) _
  rw [prod_mul_deductions, div_pow, one_pow, ← pow_mul, div_le_iff₀ (by positivity), mul_comm]

/-- **The same in geometric-mean form.** For positive factors, `N > 0` and `f < 1`: standing still
over `N` trips is the same as the geometric mean `(∏ G i) ^ (1/N)` being at least `1 / (1 - f)²`.
For a trader: the per-trade edge needed to break even is `1 / (1 - f)²` in the geometric mean
(`1.0121` for `f = 0.6 %`), whatever the number of trades. -/
theorem one_le_prod_iff_geomMean (G : ℕ → ℝ) (hG : ∀ i, 0 < G i) {f : ℝ} (hf : f < 1) {N : ℕ}
    (hN : 0 < N) :
    1 ≤ ∏ i ∈ range N, (G i * (1 - f) ^ 2) ↔
      1 / (1 - f) ^ 2 ≤ (∏ i ∈ range N, G i) ^ (1 / (N : ℝ)) := by
  have hP : 0 < ∏ i ∈ range N, G i := prod_pos fun i _ ↦ hG i
  have h1f : 0 < 1 - f := by linarith
  have hb : 0 < 1 / (1 - f) ^ 2 := by positivity
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [one_le_prod_mul_deductions_iff G hf N]
  constructor
  · intro h
    calc 1 / (1 - f) ^ 2 = ((1 / (1 - f) ^ 2) ^ N) ^ (1 / (N : ℝ)) := by
          rw [one_div (N : ℝ), Real.pow_rpow_inv_natCast hb.le hN.ne']
      _ ≤ (∏ i ∈ range N, G i) ^ (1 / (N : ℝ)) :=
          Real.rpow_le_rpow (by positivity) h (by positivity)
  · intro h
    calc (1 / (1 - f) ^ 2) ^ N ≤ ((∏ i ∈ range N, G i) ^ (1 / (N : ℝ))) ^ N :=
          pow_le_pow_left₀ hb.le h N
      _ = ∏ i ∈ range N, G i := by
          rw [one_div (N : ℝ), Real.rpow_inv_natCast_pow hP.le hN.ne']

end ClassicalLean.Analysis.RepeatedFees
