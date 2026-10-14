/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.InformationTheory.Channel
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Matrix

/-!
# A finite chain whose every step chance is at least `δ`

A chain on `n` states moves from state `i` to state `j` with chance `P i j`; a distribution `μ`
(a row of chances) becomes `μ P` (`μ ᵥ* P`) after one step and `μ P ^ t` after `t` steps. Suppose
every row of `P` sums to `1` and every entry is at least `δ`. Distances are measured by the sum of
absolute differences, `∑ j, |μ j − ν j|`.

* `sum_abs_vecMul_le` — for a row `d` that sums to `0` (the difference of two distributions),
  one step multiplies `∑ |d|` by at most `1 − n δ`, `n` the number of states.
* `sum_abs_vecMul_pow_le`, `sum_abs_vecMul_pow_sub_le` — so after `t` steps by `(1 − n δ) ^ t`;
  in particular any row `μ` with the same total as a stationary distribution `π` (one with
  `π P = π`) approaches it at that rate. `μ` may have entries of any sign.
* `existsUnique_vecMul_eq_self` — if `δ > 0` (and there is at least one state), there is exactly
  one stationary distribution.

This is Doeblin's condition in its simplest form, every entry at least `δ`, which gives
`P ≥ n δ · (uniform)`. Citation: Doeblin 1938, "Exposé de la théorie des chaînes simples
constantes de Markov à un nombre fini d'états". The nearest statement found is Levin, Peres and
Wilmer, Markov Chains and Mixing Times (2nd ed.), Theorem 4.9, a geometric bound
by the same idea, not this constant. The two-state chain of `TwoStateChain` allows zero entries,
which this module does not.

## Hypotheses

Measured in order LEAN-21's checks (check C34, exact rationals): 200 random chains with positive
entries, up to 5 states, `t < 8`, stationary distributions solved exactly. Each hypothesis is
needed: drop it alone and the conclusion fails at:

* entries at least `δ`: `P = 1` (2 states), `δ = 1/2`, `d = (1, −1)`: `2 > 0`; for uniqueness,
  the same `P` and `δ`: `(1, 0)` and `(0, 1)` are both stationary (review r34).
* rows sum to `1`: `P = 2 · 1`, `δ = 0`, `d = (1, −1)`: `4 > 2`; and for existence, `P` all `1`
  with `δ = 1`: `π P = (1, 1) ≠ π` for every `π` of total `1`.
* `∑ d = 0`: `P` all `1/2`, `δ = 1/2`, `d = (1, 1)`: `2 > 0`.
* the totals of `μ` and `π` equal: `P` all `1/2`, `μ = 0`, `t = 1`: `1 > 0`.
* `π P = π`: `P` all `1/2`, `π = μ = (1, 0)`, `t = 1`: `1 > 0`.
* `δ > 0`, for uniqueness: `P = 1`, `δ = 0`: `(1, 0)` and `(0, 1)` are both stationary.
* at least one state, for existence: no row on an empty set of states sums to `1`.

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-21, `grep -rniE` over Mathlib):
`stationary distribution|invariant distribution|doeblin|dobrushin|ergodic coefficient|perron` 6
lines, none about chains (citations and keywords); `rowStochastic.*(pow|unique|fixed)|
stochastic.*(stationary|invariant)|Tendsto.*vecMul.*\^` 0; `markov chain|MarkovChain|transition
matrix` 4 lines, docstrings of `Kernel.Irreducible` and of irreducible matrices. Used:
`cauchySeq_of_le_geometric`, `cauchySeq_tendsto_of_complete`, `Continuous.matrix_vecMul`; from the
library, `sum_vecMul_eq_sum` and `vecMul_nonneg` (InformationTheory.Channel).
-/

open Finset Filter Topology Matrix

namespace ClassicalLean.Probability

variable {n : Type*} [Fintype n]

/-- **One step shrinks a difference of distributions.** If every row of `P` sums to `1` and every
entry is at least `δ`, then for `d` with `∑ d = 0`,
`∑ j, |(d P) j| ≤ (1 − n δ) ∑ i, |d i|`, `n` the number of states. -/
theorem sum_abs_vecMul_le {P : Matrix n n ℝ} {δ : ℝ} (hP : ∀ i, ∑ j, P i j = 1)
    (hδ : ∀ i j, δ ≤ P i j) {d : n → ℝ} (hd : ∑ i, d i = 0) :
    ∑ j, |(d ᵥ* P) j| ≤ (1 - Fintype.card n * δ) * ∑ i, |d i| := by
  have e : ∀ j, (d ᵥ* P) j = ∑ i, d i * (P i j - δ) := fun j ↦ by
    simp only [vecMul_apply_eq_sum, mul_sub, sum_sub_distrib, ← sum_mul, hd, zero_mul, sub_zero]
  calc ∑ j, |(d ᵥ* P) j| = ∑ j, |∑ i, d i * (P i j - δ)| := by simp only [e]
    _ ≤ ∑ j, ∑ i, |d i| * (P i j - δ) := sum_le_sum fun j _ ↦ (abs_sum_le_sum_abs _ _).trans
        (sum_le_sum fun i _ ↦ by rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hδ i j))])
    _ = ∑ i, |d i| * ∑ j, (P i j - δ) := by rw [sum_comm]; simp only [mul_sum]
    _ = (1 - Fintype.card n * δ) * ∑ i, |d i| := by
        simp only [sum_sub_distrib, hP, sum_const, card_univ, nsmul_eq_mul, mul_sum]
        exact sum_congr rfl fun i _ ↦ by ring

/-- The factor `1 − n δ` is at least `0` when there is a state. -/
private theorem one_sub_card_mul_nonneg [Nonempty n] {P : Matrix n n ℝ} {δ : ℝ}
    (hP : ∀ i, ∑ j, P i j = 1) (hδ : ∀ i j, δ ≤ P i j) : 0 ≤ 1 - Fintype.card n * δ := by
  obtain ⟨i⟩ := ‹Nonempty n›
  have := sum_le_sum fun j (_ : j ∈ univ) ↦ hδ i j
  rw [hP i, sum_const, card_univ, nsmul_eq_mul] at this
  linarith

/-- The rows of `P ^ t` sum to `1` when the rows of `P` do. -/
private theorem sum_pow_apply_eq_one [DecidableEq n] {P : Matrix n n ℝ}
    (hP : ∀ i, ∑ j, P i j = 1) (t : ℕ) (i : n) : ∑ j, (P ^ t) i j = 1 := by
  induction t generalizing i with
  | zero => simp [one_apply]
  | succ t iht =>
    rw [pow_succ]
    simp only [mul_apply]
    rw [sum_comm]
    simp only [← mul_sum, hP, mul_one]
    exact iht i

/-- **`t` steps shrink a difference by `(1 − n δ) ^ t`.** Under the hypotheses of
`sum_abs_vecMul_le`, `∑ j, |(d P ^ t) j| ≤ (1 − n δ) ^ t ∑ i, |d i|`. -/
theorem sum_abs_vecMul_pow_le [DecidableEq n] {P : Matrix n n ℝ} {δ : ℝ}
    (hP : ∀ i, ∑ j, P i j = 1) (hδ : ∀ i j, δ ≤ P i j) {d : n → ℝ} (hd : ∑ i, d i = 0) (t : ℕ) :
    ∑ j, |(d ᵥ* P ^ t) j| ≤ (1 - Fintype.card n * δ) ^ t * ∑ i, |d i| := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp
  have hc := one_sub_card_mul_nonneg hP hδ
  induction t with
  | zero => simp
  | succ t ih =>
    have hsum : ∑ i, (d ᵥ* P ^ t) i = 0 := by
      rw [ClassicalLean.Simplex.sum_vecMul_eq_sum (sum_pow_apply_eq_one hP t), hd]
    rw [pow_succ, ← vecMul_vecMul]
    calc ∑ j, |((d ᵥ* P ^ t) ᵥ* P) j|
        ≤ (1 - Fintype.card n * δ) * ∑ i, |(d ᵥ* P ^ t) i| := sum_abs_vecMul_le hP hδ hsum
      _ ≤ (1 - Fintype.card n * δ) * ((1 - Fintype.card n * δ) ^ t * ∑ i, |d i|) :=
          mul_le_mul_of_nonneg_left ih hc
      _ = (1 - Fintype.card n * δ) ^ (t + 1) * ∑ i, |d i| := by ring

/-- **A chain with every step chance at least `δ` forgets its start at rate `(1 − n δ) ^ t`.** If
every row of `P` sums to `1`, every entry is at least `δ`, `π P = π`, and `μ` has the same total
as `π`, then `∑ j, |(μ P ^ t) j − π j| ≤ (1 − n δ) ^ t ∑ j, |μ j − π j|`. -/
theorem sum_abs_vecMul_pow_sub_le [DecidableEq n] {P : Matrix n n ℝ} {δ : ℝ}
    (hP : ∀ i, ∑ j, P i j = 1) (hδ : ∀ i j, δ ≤ P i j) {μ π : n → ℝ}
    (hμ : ∑ i, μ i = ∑ i, π i) (hπ : π ᵥ* P = π) (t : ℕ) :
    ∑ j, |(μ ᵥ* P ^ t) j - π j| ≤ (1 - Fintype.card n * δ) ^ t * ∑ j, |μ j - π j| := by
  have hπt : π ᵥ* P ^ t = π := by
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ, ← vecMul_vecMul, ih, hπ]
  have hd : ∑ i, (μ - π) i = 0 := by simp [sum_sub_distrib, hμ]
  have := sum_abs_vecMul_pow_le hP hδ hd t
  rwa [sub_vecMul, hπt] at this

/-- **One stationary distribution.** If every row of `P` sums to `1`, every entry is at least
`δ > 0`, and there is at least one state, exactly one distribution `π` (entries at least `0`,
total `1`) has `π P = π`. -/
theorem existsUnique_vecMul_eq_self [Nonempty n] {P : Matrix n n ℝ} {δ : ℝ}
    (hP : ∀ i, ∑ j, P i j = 1) (hδ0 : 0 < δ) (hδ : ∀ i j, δ ≤ P i j) :
    ∃! π : n → ℝ, ((∀ i, 0 ≤ π i) ∧ ∑ i, π i = 1) ∧ π ᵥ* P = π := by
  classical
  set c := 1 - Fintype.card n * δ
  have hc0 : 0 ≤ c := one_sub_card_mul_nonneg hP hδ
  have hc1 : c < 1 := by
    have : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
    simp only [c]; nlinarith
  have hP0 : ∀ i j, 0 ≤ P i j := fun i j ↦ hδ0.le.trans (hδ i j)
  let S : Set (n → ℝ) := {π | (∀ i, 0 ≤ π i) ∧ ∑ i, π i = 1}
  have hSstep : ∀ π ∈ S, π ᵥ* P ∈ S := fun π hπ ↦
    ⟨ClassicalLean.Simplex.vecMul_nonneg hP0 hπ.1, by
      rw [ClassicalLean.Simplex.sum_vecMul_eq_sum hP, hπ.2]⟩
  have hSclosed : IsClosed S := by
    have e : S = (⋂ i, {π : n → ℝ | 0 ≤ π i}) ∩ {π | ∑ i, π i = 1} := by
      ext π; simp [S, Set.mem_iInter]
    rw [e]
    exact (isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_eq (continuous_finsetSum _ fun i _ ↦ continuous_apply i) continuous_const)
  have hvc : Continuous fun v : n → ℝ ↦ v ᵥ* P := continuous_id.matrix_vecMul continuous_const
  -- uniqueness from the contraction
  have huniq : ∀ π₁ ∈ S, π₁ ᵥ* P = π₁ → ∀ π₂ ∈ S, π₂ ᵥ* P = π₂ → π₁ = π₂ := by
    intro π₁ h₁ f₁ π₂ h₂ f₂
    have hd : ∑ i, (π₁ - π₂) i = 0 := by simp [sum_sub_distrib, h₁.2, h₂.2]
    have h := sum_abs_vecMul_le hP hδ hd
    rw [sub_vecMul, f₁, f₂] at h
    have hz : ∑ i, |(π₁ - π₂) i| = 0 := by
      have : 0 ≤ ∑ i, |(π₁ - π₂) i| := sum_nonneg fun _ _ ↦ abs_nonneg _
      simp only [Pi.sub_apply] at h this ⊢
      nlinarith
    funext i
    have := (sum_eq_zero_iff_of_nonneg fun j _ ↦ abs_nonneg ((π₁ - π₂) j)).mp hz i (mem_univ i)
    simpa [sub_eq_zero] using this
  -- existence: the steps from one distribution form a Cauchy sequence
  obtain ⟨i₀⟩ := ‹Nonempty n›
  let u : ℕ → n → ℝ := fun t ↦ (fun i ↦ if i = i₀ then 1 else 0) ᵥ* P ^ t
  have hu_succ : ∀ t, u (t + 1) = u t ᵥ* P := fun t ↦ by
    simp only [u, pow_succ, ← vecMul_vecMul]
  have hu_mem : ∀ t, u t ∈ S := by
    intro t
    induction t with
    | zero => exact ⟨fun i ↦ by simp [u]; split_ifs <;> norm_num, by simp [u]⟩
    | succ t ih => rw [hu_succ]; exact hSstep _ ih
  have hu_dist : ∀ t, dist (u t) (u (t + 1)) ≤ (∑ i, |(u 0 - u 1) i|) * c ^ t := by
    intro t
    have hd : ∑ i, (u 0 - u 1) i = 0 := by simp [sum_sub_distrib, (hu_mem 0).2, (hu_mem 1).2]
    have h := sum_abs_vecMul_pow_le hP hδ hd t
    have e : (u 0 - u 1) ᵥ* P ^ t = u t - u (t + 1) := by
      simp only [u, sub_vecMul, vecMul_vecMul, pow_zero, Matrix.one_mul, pow_one, ← pow_succ']
    rw [e] at h
    rw [dist_eq_norm, mul_comm]
    refine le_trans ?_ h
    refine (pi_norm_le_iff_of_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _)).mpr fun j ↦ ?_
    rw [Real.norm_eq_abs]
    exact single_le_sum (f := fun j ↦ |(u t - u (t + 1)) j|) (fun _ _ ↦ abs_nonneg _) (mem_univ j)
  obtain ⟨π, hπ⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric c _ hc1 hu_dist)
  have hπS : π ∈ S := hSclosed.mem_of_tendsto hπ (Eventually.of_forall hu_mem)
  have hπfix : π ᵥ* P = π := by
    have h1 : Tendsto (fun t ↦ u t ᵥ* P) atTop (𝓝 (π ᵥ* P)) := (hvc.tendsto π).comp hπ
    have h2 : Tendsto (fun t ↦ u (t + 1)) atTop (𝓝 π) := hπ.comp (tendsto_add_atTop_nat 1)
    simp only [hu_succ] at h2
    exact tendsto_nhds_unique h1 h2
  exact ⟨π, ⟨hπS, hπfix⟩, fun π' h' ↦ huniq π' h'.1 h'.2 π hπS hπfix⟩

end ClassicalLean.Probability

open Matrix in
/-- The hypotheses of `existsUnique_vecMul_eq_self` hold together: the `2 × 2` matrix with rows
`(3/4, 1/4)` and `(1/4, 3/4)`, each row summing to `1`, every entry at least `δ = 1/4 > 0`; the
theorem's constant `1 - 2 δ` is `1/2`, not `0`. -/
example := ClassicalLean.Probability.existsUnique_vecMul_eq_self (n := Fin 2)
  (P := !![3 / 4, 1 / 4; 1 / 4, 3 / 4]) (δ := 1 / 4)
  (fun i => by fin_cases i <;> norm_num [Fin.sum_univ_two])
  (by norm_num)
  (fun i j => by fin_cases i <;> fin_cases j <;> norm_num)

open Matrix in
/-- The hypotheses of `sum_abs_vecMul_pow_sub_le` hold together: the `2 × 2` matrix with rows
`(3/4, 1/4)` and `(1/4, 3/4)`, each row summing to `1`, every entry at least `δ = 1/4`, so the
rate `1 − 2 δ = 1/2` is not `0`; the start `μ = (1, 0)` and the stationary `π = (1/2, 1/2)` both
sum to `1`, and `π P = π`; `t = 3`. -/
example := ClassicalLean.Probability.sum_abs_vecMul_pow_sub_le (n := Fin 2)
  (P := !![3 / 4, 1 / 4; 1 / 4, 3 / 4]) (δ := 1 / 4)
  (fun i ↦ by fin_cases i <;> norm_num [Fin.sum_univ_two])
  (fun i j ↦ by fin_cases i <;> fin_cases j <;> norm_num) (μ := ![1, 0]) (π := ![1 / 2, 1 / 2])
  (by norm_num [Fin.sum_univ_two])
  (by ext j; fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_two] <;> norm_num) 3
