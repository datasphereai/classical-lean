/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.Distributions.Binomial

/-!
# The variance of the binomial law

The number of successes in `n` independent trials, each a success with chance `p`, has the
binomial law `Bin(n, p)`. Mathlib proves its mean is `p n` (`integral_of_hasLaw_binomial`). This
module proves its variance is `p (1 − p) n`.

* `integral_sq_binomial` — the mean square: `E[X²] = p (1 − p) n + (p n)²`.
* `variance_binomial` — the variance of the law itself: `Var = p (1 − p) n`.
* `variance_of_hasLaw_binomial` — for any random variable `X` with that law.

`variance_of_hasLaw_binomial` is Mathlib's own `proof_wanted` of that name, in Mathlib's
`Wanted/Probability/Distributions/Binomial.lean` (line 20, Mathlib v4.34.0), proved here with the
statement unchanged. It is not offered to Mathlib. The same Mathlib file has a second
`proof_wanted`, on the conditional variance (`condVar_of_hasLaw_binomial`); it is not proved here.

The proof computes the mean of `X (X − 1)` from the identity
`C(m + 2, j + 2) (j + 2) (j + 1) = (m + 2) (m + 1) C(m, j)` and the binomial theorem, as Mathlib's
proof of the mean does for `X`; then `E[X²] = E[X (X − 1)] + E[X]`.

## Hypotheses

None beyond those of Mathlib's statement: `X` has the law `Bin(n, p)` with `p ∈ [0, 1]`.
Measured in order LEAN-21's checks (check C38, exact rationals): `E[X²]` and the variance for
`n ≤ 12` and six values of `p`, `0` and `1` included.

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-21, `grep -rniE` over Mathlib):
`variance.*binomial|binomial.*variance|variance_binomial` 0 lines in `Mathlib/`; the `proof_wanted`
above in `Wanted/`. Used: `integral_map_cast_binomial`, `integral_of_hasLaw_binomial`,
`integrable_map_cast_binomial`, `HasLaw.variance_eq`, `variance_eq_sub`,
`Nat.add_one_mul_choose_eq`, `add_pow`.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ProbabilityTheory unitInterval

namespace ClassicalLean.Probability

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {n : ℕ} {p : I} {X : Ω → ℝ}

/-- The second factorial moment of the binomial weights:
`∑ k ≤ n, C(n, k) q^k (1 − q)^(n − k) k (k − 1) = q² n (n − 1)`, for every real `q`. -/
private theorem sum_choose_mul_mul_sub_one (n : ℕ) (q : ℝ) :
    ∑ k ∈ range (n + 1), (n.choose k * q ^ k * (1 - q) ^ (n - k)) * ((k : ℝ) * (k - 1)) =
      q ^ 2 * n * (n - 1) := by
  rcases n with _ | _ | m
  · simp
  · simp [sum_range_succ]
  rw [sum_range_succ', sum_range_succ']
  have h : ∀ j ∈ range (m + 1),
      ((m + 1 + 1).choose (j + 1 + 1) * q ^ (j + 1 + 1) * (1 - q) ^ (m + 1 + 1 - (j + 1 + 1))) *
        (((j + 1 + 1 : ℕ) : ℝ) * ((j + 1 + 1 : ℕ) - 1)) =
      (m + 2) * (m + 1) * q ^ 2 * (q ^ j * (1 - q) ^ (m - j) * m.choose j) := by
    intro j _
    have hc :
        ((m + 2).choose (j + 2) * ((j + 2) * (j + 1)) : ℕ) = (m + 2) * (m + 1) * m.choose j := by
      have c1 := Nat.add_one_mul_choose_eq (m + 1) (j + 1)
      have c2 := Nat.add_one_mul_choose_eq m j
      calc (m + 2).choose (j + 2) * ((j + 2) * (j + 1))
          = ((m + 1 + 1).choose (j + 1 + 1) * (j + 1 + 1)) * (j + 1) := by ring
        _ = (m + 1 + 1) * (m + 1).choose (j + 1) * (j + 1) := by rw [← c1]
        _ = (m + 2) * ((m + 1).choose (j + 1) * (j + 1)) := by ring
        _ = (m + 2) * (m + 1) * m.choose j := by rw [← c2]; ring
    have hc' :
        ((m + 2).choose (j + 2) : ℝ) * ((j + 2) * (j + 1)) = (m + 2) * (m + 1) * m.choose j := by
      exact_mod_cast hc
    rw [Nat.add_sub_add_right, Nat.add_sub_add_right]
    push_cast
    calc ((m + 1 + 1).choose (j + 1 + 1) * q ^ (j + 1 + 1) * (1 - q) ^ (m - j)) *
          ((j + 1 + 1) * (j + 1 + 1 - 1))
        = ((m + 2).choose (j + 2) * ((j + 2) * (j + 1))) * q ^ 2 * (q ^ j * (1 - q) ^ (m - j)) := by
          ring
      _ = (m + 2) * (m + 1) * q ^ 2 * (q ^ j * (1 - q) ^ (m - j) * m.choose j) := by
          rw [hc']; ring
  rw [sum_congr rfl h, ← mul_sum, ← add_pow, add_sub_cancel, one_pow]
  push_cast
  ring

/-- **The mean square of the binomial law.** `E[X²] = p (1 − p) n + (p n)²` under `Bin(n, p)`. -/
theorem integral_sq_binomial :
    ∫ x, x ^ 2 ∂Bin(ℝ, n, p) = p * (1 - p) * n + (p * n) ^ 2 := by
  have hmean : ∑ k ∈ range (n + 1), (n.choose k * (p : ℝ) ^ k * (1 - p) ^ (n - k)) * (k : ℝ) =
      p * n := by
    have := integral_of_hasLaw_binomial (HasLaw.id (μ := Bin(ℝ, n, p)))
    rw [show (fun x : ℝ ↦ id x) = id from rfl, integral_map_cast_binomial,
      ← Nat.range_succ_eq_Iic] at this
    simpa [smul_eq_mul] using this
  have h2 := sum_choose_mul_mul_sub_one n p
  rw [integral_map_cast_binomial, ← Nat.range_succ_eq_Iic]
  simp only [smul_eq_mul]
  have e : ∀ k ∈ range (n + 1), (n.choose k * (p : ℝ) ^ k * (1 - p) ^ (n - k)) * (k : ℝ) ^ 2 =
      (n.choose k * (p : ℝ) ^ k * (1 - p) ^ (n - k)) * ((k : ℝ) * (k - 1)) +
        (n.choose k * (p : ℝ) ^ k * (1 - p) ^ (n - k)) * (k : ℝ) := fun _ _ ↦ by ring
  rw [sum_congr rfl e, sum_add_distrib, h2, hmean]
  ring

/-- **The variance of the binomial law.** `Var = p (1 − p) n` under `Bin(n, p)`. -/
theorem variance_binomial : Var[id; Bin(ℝ, n, p)] = p * (1 - p) * n := by
  have hm : MemLp (id : ℝ → ℝ) 2 Bin(ℝ, n, p) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr (integrable_map_cast_binomial _)
  have hmean := integral_of_hasLaw_binomial (HasLaw.id (μ := Bin(ℝ, n, p)))
  rw [variance_eq_sub hm, hmean]
  simp only [Pi.pow_apply, id]
  rw [integral_sq_binomial]
  ring

/-- **The variance of a binomial random variable** (Mathlib's `proof_wanted` of this name and
statement). If `X` has the law `Bin(n, p)` under `P`, then `Var[X; P] = p (1 − p) n`. -/
theorem variance_of_hasLaw_binomial (hX : HasLaw X Bin(ℝ, n, p) P) :
    Var[X; P] = p * (1 - p) * n := by
  rw [hX.variance_eq, variance_binomial]

end ClassicalLean.Probability
