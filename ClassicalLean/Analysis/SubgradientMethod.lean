/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The subgradient method

A function `f : E → ℝ` on a real inner product space `E`, and points `x n` with, at each of them,
a subgradient `g n`: `f (x n) + ⟪g n, y - x n⟫_ℝ ≤ f y` for every `y`. The subgradient method steps
against the subgradient with a fixed step `η > 0`: `x (n + 1) = x n - η • g n`.

* `min_sub_le_of_subgradient` — order CLOUD-MATH-3, item 113 of MATH-PLAN-library-2. If
  `‖g n‖ ≤ G` for every `n`, then for every point `z` and every `T ≥ 1` the least of the first `T`
  values `f (x 0), …, f (x (T - 1))` (`Finset.inf'` over `Finset.range T`) is at most `f z` plus
  `(‖x 0 - z‖ ^ 2 + η ^ 2 * G ^ 2 * T) / (2 * η * T)`.

Wider than the plan's row, by this session's reading (the draft's last review, as the order's
table gives it: GENERALIZED): the row speaks of a convex `f`; the theorem asks no convexity, only
the subgradient inequality at the points `x n` themselves, which every subgradient of a convex `f`
satisfies.

The proof. The subgradient inequality at `y = z` and the expansion of
`‖x (n + 1) - z‖ ^ 2 = ‖(x n - z) - η • g n‖ ^ 2` give
`2 * η * (f (x n) - f z) ≤ ‖x n - z‖ ^ 2 - ‖x (n + 1) - z‖ ^ 2 + η ^ 2 * G ^ 2`. Summed over
`n < T`, the right side telescopes to at most `‖x 0 - z‖ ^ 2 + T * (η ^ 2 * G ^ 2)`, and the least
value is at most every term of the sum on the left.

The proof is the draft `d113-r1-s1` (written by Claude Opus 5.5 through the Anthropic Batch API,
the lane's API-CREDIT-1 work), adapted by the Claude Code cloud session that landed it (order
CLOUD-MATH-3): the namespace, the targeted import and the docstrings; its proof needed no other
change. The witness at the end of the file, `f y = y ^ 2 / 2` on the real line with the step
`η = 1 / 2`, is new: the item had no witness start.
-/

open scoped InnerProductSpace
open Finset

namespace ClassicalLean.Analysis.SubgradientMethod

/-- **The subgradient method.** Item 113 of MATH-PLAN-library-2 (order CLOUD-MATH-3). If `g n` is
a subgradient of `f` at `x n` (`hsub`), `‖g n‖ ≤ G`, and `x (n + 1) = x n - η • g n` with `η > 0`,
then for every `z` and `T ≥ 1` the best of the first `T` values `f (x n)` is within
`(‖x 0 - z‖ ^ 2 + η ^ 2 * G ^ 2 * T) / (2 * η * T)` of `f z`: their minimum minus `f z` is at most
that. -/
theorem min_sub_le_of_subgradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (x g : ℕ → E) (z : E) (η G : ℝ) (T : ℕ)
    (hη : 0 < η) (hT : 0 < T)
    (hsub : ∀ n y, f (x n) + ⟪g n, y - x n⟫_ℝ ≤ f y)
    (hg : ∀ n, ‖g n‖ ≤ G)
    (hstep : ∀ n, x (n + 1) = x n - η • g n) :
    (Finset.range T).inf' ⟨0, Finset.mem_range.mpr hT⟩ (fun n => f (x n)) - f z
      ≤ (‖x 0 - z‖ ^ 2 + η ^ 2 * G ^ 2 * T) / (2 * η * T) := by
  have key : ∀ n, 2 * η * (f (x n) - f z)
      ≤ ‖x n - z‖ ^ 2 - ‖x (n + 1) - z‖ ^ 2 + η ^ 2 * G ^ 2 := by
    intro n
    have h1 : x (n + 1) - z = x n - z - η • g n := by
      rw [hstep]; abel
    have h2 := norm_sub_sq_real (x n - z) (η • g n)
    rw [← h1, real_inner_smul_right] at h2
    have h5 : ‖η • g n‖ ^ 2 ≤ η ^ 2 * G ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      have hsq : ‖g n‖ ^ 2 ≤ G ^ 2 := by nlinarith [norm_nonneg (g n), hg n]
      exact mul_le_mul_of_nonneg_left hsq (sq_nonneg η)
    have h3 := hsub n z
    have h4 : ⟪g n, z - x n⟫_ℝ = -⟪x n - z, g n⟫_ℝ := by
      rw [inner_sub_right, inner_sub_left]
      linarith [real_inner_comm (x n) (g n), real_inner_comm z (g n)]
    have h6 : η * (f (x n) - f z) ≤ η * ⟪x n - z, g n⟫_ℝ :=
      mul_le_mul_of_nonneg_left (by linarith) hη.le
    linarith
  have hsum : ∀ N : ℕ, ∑ n ∈ range N, 2 * η * (f (x n) - f z)
      ≤ ‖x 0 - z‖ ^ 2 - ‖x N - z‖ ^ 2 + (N : ℝ) * (η ^ 2 * G ^ 2) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ]
      push_cast
      linarith [key N]
  set m := (Finset.range T).inf' ⟨0, Finset.mem_range.mpr hT⟩ (fun n => f (x n)) with hm_def
  have hle : ∑ n ∈ range T, 2 * η * (m - f z)
      ≤ ∑ n ∈ range T, 2 * η * (f (x n) - f z) := by
    apply sum_le_sum
    intro n hn
    have hmn : m ≤ f (x n) := Finset.inf'_le (fun n => f (x n)) hn
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  rw [sum_const, card_range, nsmul_eq_mul] at hle
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  rw [le_div_iff₀ (mul_pos (mul_pos two_pos hη) hT')]
  nlinarith [hsum T, sq_nonneg ‖x T - z‖, hle]

end ClassicalLean.Analysis.SubgradientMethod

/-- The hypotheses of `min_sub_le_of_subgradient` hold together: on the real line `E = ℝ`, the
function `f y = y ^ 2 / 2`, whose gradient at `y` is `y`, so that `g n = x n` is a subgradient at
`x n` (`f (x n) + x n * (y - x n) ≤ f y` is `0 ≤ (y - x n) ^ 2 / 2`); the step `η = 1 / 2` from
`x 0 = 1`, so that the iterates are `x n = (1 / 2) ^ n`, never `0`; the bound `G = 1` on
`‖g n‖ = (1 / 2) ^ n`; the point `z = 0`, the minimiser; and `T = 3` steps. -/
example := ClassicalLean.Analysis.SubgradientMethod.min_sub_le_of_subgradient (E := ℝ)
    (f := fun y => y ^ 2 / 2) (x := fun n => (1 / 2 : ℝ) ^ n) (g := fun n => (1 / 2 : ℝ) ^ n)
    (z := 0) (η := 1 / 2) (G := 1) (T := 3) (by norm_num) (by norm_num)
    (fun n y => by
      rw [RCLike.inner_apply, conj_trivial]
      nlinarith [sq_nonneg (y - (1 / 2 : ℝ) ^ n)])
    (fun n => by
      rw [Real.norm_eq_abs, abs_of_pos (pow_pos (by norm_num) n)]
      exact pow_le_one₀ (by norm_num) (by norm_num))
    (fun n => by rw [smul_eq_mul, pow_succ]; ring)
