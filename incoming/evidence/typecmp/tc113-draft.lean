import Mathlib

open scoped InnerProductSpace
open Finset

/-- Subgradient method: if `g n` is a subgradient of `f` at `x n` with `‖g n‖ ≤ G`, and
`x (n+1) = x n - η • g n`, then the best of the first `T` values `f (x n)` is within
`(‖x 0 - z‖² + η² G² T) / (2 η T)` of `f z`. -/
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

set_option pp.fullNames true in
#check @min_sub_le_of_subgradient
