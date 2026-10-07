/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# A chain with two states

State `0` ("calm") moves to state `1` ("wild") with chance `s`, and state `1` moves back with
chance `t`, both in `[0, 1]`. The step matrix is `twoStateMatrix s t = !![1 - s, s; t, 1 - t]`,
which is in Mathlib's `rowStochastic`. A distribution is a row vector `π`, and one step takes it
to `π ᵥ* P`.

* `twoStateMatrix_mem_rowStochastic`: the matrix is row-stochastic.
* `vecMul_eq_self_iff`: if `s + t > 0`, the only steady distribution is
  `(t/(s+t), s/(s+t))`.
* `vecMul_pow_apply_one`: if `s + t > 0`, the chance of state `1` after `n` steps is
  `s/(s+t) + (1 - s - t) ^ n · (start - s/(s+t))`.
* `tendsto_vecMul_pow_apply_one`: if also `s + t < 2`, it tends to `s/(s+t)` from any start: the
  start is forgotten by the factor `|1 - s - t|` per step.
* `hasSum_spell`: for `0 < s ≤ 1`, `∑_{k ≥ 1} k · s · (1 - s) ^ (k - 1) = 1/s`: a calm spell lasts
  `1/s` steps on average (from `tsum_coe_mul_geometric_of_norm_lt_one`).

Each hypothesis is needed. At `s + t = 0` the matrix is the identity and every distribution is
steady. At `s + t = 2` the chain alternates `(1,0), (0,1), (1,0), …` and never settles, though
the steady distribution `(1/2, 1/2)` is still the only one.
-/

open Matrix Filter Topology

namespace ClassicalLean.Probability.TwoStateChain

/-- The step matrix of the two-state chain. -/
def twoStateMatrix (s t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1 - s, s; t, 1 - t]

/-- The step matrix is row-stochastic. -/
theorem twoStateMatrix_mem_rowStochastic {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : twoStateMatrix s t ∈ rowStochastic ℝ (Fin 2) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j ↦ ?_, fun i ↦ ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [twoStateMatrix] <;> linarith
  · fin_cases i <;> simp [twoStateMatrix, Fin.sum_univ_two]

lemma vecMul_apply_zero (s t : ℝ) (π : Fin 2 → ℝ) :
    (π ᵥ* twoStateMatrix s t) 0 = π 0 * (1 - s) + π 1 * t := by
  simp [twoStateMatrix, vecMul, dotProduct, Fin.sum_univ_two]

lemma vecMul_apply_one (s t : ℝ) (π : Fin 2 → ℝ) :
    (π ᵥ* twoStateMatrix s t) 1 = π 0 * s + π 1 * (1 - t) := by
  simp [twoStateMatrix, vecMul, dotProduct, Fin.sum_univ_two]

/-- **The one steady distribution.** If `s + t > 0`, a distribution `π` (entries summing to `1`)
satisfies `π ᵥ* P = π` exactly when `π = (t/(s+t), s/(s+t))`. -/
theorem vecMul_eq_self_iff {s t : ℝ} (hst : 0 < s + t) {π : Fin 2 → ℝ} (hπ : π 0 + π 1 = 1) :
    π ᵥ* twoStateMatrix s t = π ↔ π = ![t / (s + t), s / (s + t)] := by
  have hne : s + t ≠ 0 := hst.ne'
  constructor
  · intro h
    have h1 := congrFun h 1
    rw [vecMul_apply_one] at h1
    have hπ1 : π 1 = s / (s + t) := by
      rw [eq_div_iff hne]; linear_combination -h1 + s * hπ
    have hπ0 : π 0 = t / (s + t) := by
      rw [eq_div_iff hne]
      have : π 0 = 1 - π 1 := by linarith
      rw [this, hπ1]; field_simp; ring
    ext i; fin_cases i <;> simp [hπ0, hπ1]
  · rintro rfl
    ext i; fin_cases i
    · simp only [Fin.zero_eta, vecMul_apply_zero]; simp; field_simp; ring
    · simp only [Fin.mk_one, vecMul_apply_one]; simp; field_simp; ring

/-- **The chance of the second state after `n` steps.** If `s + t > 0` and the start `π` sums to
`1`, then `(π ᵥ* P ^ n) 1 = s/(s+t) + (1 - s - t) ^ n · (π 1 - s/(s+t))`. -/
theorem vecMul_pow_apply_one {s t : ℝ} (hst : 0 < s + t) {π : Fin 2 → ℝ} (hπ : π 0 + π 1 = 1)
    (n : ℕ) : (π ᵥ* twoStateMatrix s t ^ n) 1 =
      s / (s + t) + (1 - s - t) ^ n * (π 1 - s / (s + t)) := by
  have hne : s + t ≠ 0 := hst.ne'
  have hsum : ∀ n, (π ᵥ* twoStateMatrix s t ^ n) 0 + (π ᵥ* twoStateMatrix s t ^ n) 1 = 1 := by
    intro n
    induction n with
    | zero => simpa using hπ
    | succ n ih =>
      rw [pow_succ, ← vecMul_vecMul, vecMul_apply_zero, vecMul_apply_one]
      linear_combination ih
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← vecMul_vecMul, vecMul_apply_one]
    have h0 : (π ᵥ* twoStateMatrix s t ^ n) 0 = 1 - (π ᵥ* twoStateMatrix s t ^ n) 1 := by
      linarith [hsum n]
    rw [h0, ih]
    field_simp
    ring

/-- **The start is forgotten.** If `0 < s + t < 2`, the chance of the second state tends to
`s/(s+t)` from any start. -/
theorem tendsto_vecMul_pow_apply_one {s t : ℝ} (hst : 0 < s + t) (hst2 : s + t < 2)
    {π : Fin 2 → ℝ} (hπ : π 0 + π 1 = 1) :
    Tendsto (fun n ↦ (π ᵥ* twoStateMatrix s t ^ n) 1) atTop (𝓝 (s / (s + t))) := by
  simp_rw [vecMul_pow_apply_one hst hπ]
  have hr : |1 - s - t| < 1 := by rw [abs_lt]; constructor <;> linarith
  have := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr).mul_const (π 1 - s / (s + t))
  rw [zero_mul] at this
  simpa using this.const_add (s / (s + t))

/-- **The mean length of a calm spell.** For `0 < s ≤ 1`, a spell that ends at each step with
chance `s` lasts `k ≥ 1` steps with chance `s (1 - s) ^ (k - 1)`, and its mean length
`∑_{k ≥ 1} k s (1 - s) ^ (k - 1)` is `1/s`. Written with `k + 1` for `k ≥ 0`. -/
theorem hasSum_spell {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    HasSum (fun k : ℕ ↦ ((k : ℝ) + 1) * s * (1 - s) ^ k) (1 / s) := by
  have hr : ‖1 - s‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hr
  have h2 := hasSum_geometric_of_norm_lt_one hr
  have h := (h1.add h2).mul_left s
  convert h using 1
  · funext k; ring
  · have : (1 : ℝ) - (1 - s) = s := by ring
    rw [this]; field_simp; ring

end ClassicalLean.Probability.TwoStateChain
