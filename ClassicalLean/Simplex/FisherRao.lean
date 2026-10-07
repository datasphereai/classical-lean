/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.GoldenRatio.Characterisations
import ClassicalLean.InformationTheory.Entropy
import ClassicalLean.Simplex.DesignConstants
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The Fisher–Rao metric on the probability simplex, and a rank-one relaxation operator

Four things, in order.

1. **The Fisher–Rao metric** `fisherRao p u v = ∑ i, u i * v i / p i` on the open probability
   simplex: symmetry, linearity in the second argument, positive definiteness, the value at the
   uniform distribution, and a Cauchy–Schwarz bound `(∑ i, |u i|) ^ 2 ≤ G_p(u, u)` obtained from
   Mathlib's `Finset.sq_sum_div_le_sum_sq_div` (Sedrakyan's lemma). The simplex itself,
   `openSimplex ι`, is defined once in `ClassicalLean.Simplex.Basic` and only used here.

2. **A rank-one relaxation operator** `relaxationOp T c i₀`: multiplication by `T` plus a rank-one
   term supported on one distinguished coordinate. No eigenvalue other than `T` and `T + c` exists
   (`relaxationOp_eigenvalue_eq`), and over an index type with at least two elements both are
   attained (`exists_relaxationOp_eigenvector_iff`); consequently two distinct eigenvalues always
   differ by exactly `|c|`, whatever `T` and whatever the index type.
   Context, not proved here: an operator of this shape is what one expects from a relaxation flow
   whose generator is a multiple of the Fisher–Rao metric plus a barrier supported on a single
   coordinate. That derivation is not formalised in this file, so `T` and `c` remain free
   parameters and no statement below asserts a value for either.

3. **The increment that reproduces itself.** Among positive reals, `(1 - x) / x = x` holds exactly
   at `x = φ⁻¹` (`one_sub_div_eq_self_iff`), proved from the shipped
   `ClassicalLean.GoldenRatio.goldenRatio_unique_pos_root`. With that value as the increment, the
   gap between two distinct eigenvalues of the operator in part 2 is `φ⁻¹` for every `T`
   (`relaxationOp_golden_gap`).

4. **The design temperature, thermodynamically.** `designTemperature = φ / log (2 φ)` is
   declared once, in `ClassicalLean.Simplex.DesignConstants`, where it is *determined* by the
   threshold `1/φ` chosen there (`criticalTemperature_two_eq`, `designTemperature_unique`). This
   file imports that constant and does not redeclare it. What is proved here: the three-level
   partition function `Z(1/T, φ)` equals `φ`; the Boltzmann weights at that temperature are
   `(φ⁻¹, 1/(2 φ²), 1/(2 φ²))`, which is exactly the `designPoint` of that module
   (`gibbsPoint_eq_designPoint`) and lies in the open simplex; the internal energy of that vector
   against the *chosen* levels `(0, φ, φ)` is `φ⁻¹`; and the Helmholtz entropy built from those
   two proved numbers agrees with the Shannon entropy of the weights
   (`helmholtzEntropy_eq_internalEnergy_sub_free`, `helmholtzEntropy_eq_shannonEntropy`).

`φ` throughout is Mathlib's `Real.goldenRatio`. Each golden-ratio fact used is cited by name where
it is used, rather than restated.

## Not ported from the source

The following source material has no counterpart in this library, for the reasons
given.

* A four-way summary conjunction of the spectrum results: dropped. Its four components are
  shipped separately (`relaxationOp_eigenvalue_eq`, `exists_relaxationOp_eigenvector_iff`,
  `relaxationOp_gap`, `relaxationOp_golden_gap`); a conjunction of them adds nothing.
* The two source declarations about `σ` that were dropped — a vacuous translation-invariance
  statement and a duplicate wrapper — are recorded in `ClassicalLean.Simplex.Involution`, whose
  subject they are.
-/

open Finset Real

namespace ClassicalLean.Simplex

section Metric

variable {ι : Type*} [Fintype ι]

/-! ## 1. The open probability simplex

`openSimplex ι` — the probability vectors all of whose coordinates are strictly positive, on
which the metric below is defined because it divides by `p i` — is declared once, in
`ClassicalLean.Simplex.Basic`, together with `mem_openSimplex`, `convex_openSimplex` and
`openSimplex_subset_closedSimplex`. This file uses them and declares none of them. -/

/-! ## 2. The Fisher–Rao metric -/

/-- The **Fisher–Rao (Fisher information) metric** at a point `p`, evaluated on a pair of vectors:
`G_p(u, v) = ∑ i, u i * v i / p i`. The definition is stated for every `p : ι → ℝ`; the hypotheses
of the lemmas below say where it is meant to be used, namely on `openSimplex ι`. -/
noncomputable def fisherRao (p u v : ι → ℝ) : ℝ := ∑ i, u i * v i / p i

/-- The Fisher–Rao metric is symmetric in its two vector arguments. -/
theorem fisherRao_comm (p u v : ι → ℝ) : fisherRao p u v = fisherRao p v u :=
  Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm]

/-- The Fisher–Rao metric is additive in its second vector argument. -/
theorem fisherRao_add_right (p u v w : ι → ℝ) :
    fisherRao p u (v + w) = fisherRao p u v + fisherRao p u w := by
  simp only [fisherRao, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The Fisher–Rao metric is homogeneous in its second vector argument. -/
theorem fisherRao_smul_right (c : ℝ) (p u v : ι → ℝ) :
    fisherRao p u (c • v) = c * fisherRao p u v := by
  simp only [fisherRao, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- At a point with strictly positive coordinates the Fisher–Rao quadratic form is nonnegative. -/
theorem fisherRao_self_nonneg {p : ι → ℝ} (hp : ∀ i, 0 < p i) (u : ι → ℝ) :
    0 ≤ fisherRao p u u :=
  Finset.sum_nonneg fun i _ ↦ div_nonneg (mul_self_nonneg _) (hp i).le

/-- **Positive definiteness.** At a point with strictly positive coordinates the Fisher–Rao
quadratic form vanishes only at the zero vector. -/
theorem fisherRao_self_eq_zero_iff {p : ι → ℝ} (hp : ∀ i, 0 < p i) (u : ι → ℝ) :
    fisherRao p u u = 0 ↔ u = 0 := by
  constructor
  · intro h
    funext i
    have hterm : u i * u i / p i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ div_nonneg (mul_self_nonneg (u j)) (hp j).le)).mp h i (Finset.mem_univ i)
    rcases div_eq_zero_iff.mp hterm with h2 | h2
    · exact mul_self_eq_zero.mp h2
    · exact absurd h2 (hp i).ne'
  · rintro rfl
    simp [fisherRao]

/-- At the uniform distribution the Fisher–Rao metric is the Euclidean one scaled by the number of
coordinates. -/
theorem fisherRao_uniform (u v : ι → ℝ) :
    fisherRao (fun _ ↦ (Fintype.card ι : ℝ)⁻¹) u v = (Fintype.card ι : ℝ) * ∑ i, u i * v i := by
  simp only [fisherRao, div_eq_mul_inv, inv_inv, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **A Cauchy–Schwarz bound.** On the open simplex the Fisher–Rao quadratic form dominates the
square of the `ℓ¹` norm: `(∑ i, |u i|) ^ 2 ≤ G_p(u, u)`. This is Mathlib's
`Finset.sq_sum_div_le_sum_sq_div` (Sedrakyan's lemma) applied to `|u|` and `p`, together with
`∑ i, p i = 1`. -/
theorem sq_sum_abs_le_fisherRao {p : ι → ℝ} (hp : p ∈ openSimplex ι) (u : ι → ℝ) :
    (∑ i, |u i|) ^ 2 ≤ fisherRao p u u := by
  have h := Finset.sq_sum_div_le_sum_sq_div Finset.univ (fun i ↦ |u i|) (fun i _ ↦ hp.1 i)
  rw [hp.2, div_one] at h
  refine h.trans_eq (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [sq_abs]
  ring

end Metric

section RankOne

variable {ι : Type*} [DecidableEq ι]

/-! ## 3. A rank-one relaxation operator -/

/-- A **rank-one relaxation operator** on `ι → ℝ`: `R u = T • u + c * u i₀` deposited in the single
distinguished coordinate `i₀`.

Context, not proved here: operators of this shape arise from a relaxation flow whose generator is
a multiple of the Fisher–Rao metric plus a barrier term supported on one coordinate. The passage
from such a flow to this matrix is not formalised in this file, so `T` and `c` are free parameters
throughout and nothing below asserts a value for either. -/
def relaxationOp (T c : ℝ) (i₀ : ι) (u : ι → ℝ) : ι → ℝ :=
  T • u + Pi.single i₀ (c * u i₀)

/-- Coordinates of `relaxationOp`: it acts as multiplication by `T`, except at `i₀`. -/
theorem relaxationOp_apply (T c : ℝ) (i₀ : ι) (u : ι → ℝ) (i : ι) :
    relaxationOp T c i₀ u i = T * u i + (if i = i₀ then c * u i₀ else 0) := by
  simp [relaxationOp, Pi.single_apply]

/-- On vectors vanishing at the distinguished coordinate the operator is `T • ·`. -/
theorem relaxationOp_of_apply_eq_zero {T c : ℝ} {i₀ : ι} {u : ι → ℝ} (hu : u i₀ = 0) :
    relaxationOp T c i₀ u = T • u := by
  simp [relaxationOp, hu]

/-- The distinguished coordinate direction is an eigenvector with eigenvalue `T + c`. -/
theorem relaxationOp_single (T c : ℝ) (i₀ : ι) (a : ℝ) :
    relaxationOp T c i₀ (Pi.single i₀ a) = (T + c) • (Pi.single i₀ a : ι → ℝ) := by
  funext i
  rw [relaxationOp_apply]
  by_cases h : i = i₀
  · subst h
    simp only [Pi.single_eq_same, ite_true, Pi.smul_apply, smul_eq_mul]
    ring
  · simp [h]

/-- A coordinate direction is a nonzero vector. -/
theorem single_one_ne_zero (j : ι) : (Pi.single j (1 : ℝ) : ι → ℝ) ≠ 0 := by
  intro hz
  have h1 := congrFun hz j
  simp at h1

/-- **Every eigenvalue is `T` or `T + c`.** No assumption on the index type is needed for this
direction. -/
theorem relaxationOp_eigenvalue_eq {T c ρ : ℝ} {i₀ : ι} {u : ι → ℝ} (hu : u ≠ 0)
    (h : relaxationOp T c i₀ u = ρ • u) : ρ = T ∨ ρ = T + c := by
  have key : ∀ i, T * u i + (if i = i₀ then c * u i₀ else 0) = ρ * u i := by
    intro i
    have hi := congrFun h i
    rwa [relaxationOp_apply, Pi.smul_apply, smul_eq_mul] at hi
  by_cases h0 : u i₀ = 0
  · obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hu (funext fun j ↦ hcon j)
    have hjne : j ≠ i₀ := by
      intro hje
      exact hj (by rw [hje]; exact h0)
    have hkj := key j
    rw [ite_eq_right hjne] at hkj
    have hfac : (T - ρ) * u j = 0 := by linear_combination hkj
    rcases mul_eq_zero.mp hfac with h' | h'
    · exact Or.inl (sub_eq_zero.mp h').symm
    · exact absurd h' hj
  · have hkey := key i₀
    rw [ite_eq_left rfl] at hkey
    have hfac : (T + c - ρ) * u i₀ = 0 := by linear_combination hkey
    rcases mul_eq_zero.mp hfac with h' | h'
    · exact Or.inr (by linarith)
    · exact absurd h' h0

/-- **The spectrum of the relaxation operator.** For an index type with at least two elements, a
real number `ρ` admits a nonzero `u` with `R u = ρ • u` exactly when `ρ = T` or `ρ = T + c`. Both
values are attained: `T` on any coordinate direction other than `i₀`, and `T + c` on the `i₀`
direction. -/
theorem exists_relaxationOp_eigenvector_iff [Nontrivial ι] (T c : ℝ) (i₀ : ι) (ρ : ℝ) :
    (∃ u : ι → ℝ, u ≠ 0 ∧ relaxationOp T c i₀ u = ρ • u) ↔ ρ = T ∨ ρ = T + c := by
  constructor
  · rintro ⟨u, hu, h⟩
    exact relaxationOp_eigenvalue_eq hu h
  · rintro (rfl | rfl)
    · obtain ⟨j, hj⟩ := exists_ne i₀
      exact ⟨Pi.single j 1, single_one_ne_zero j,
        relaxationOp_of_apply_eq_zero (Pi.single_eq_of_ne (Ne.symm hj) 1)⟩
    · exact ⟨Pi.single i₀ 1, single_one_ne_zero i₀, relaxationOp_single _ _ _ _⟩

/-- **The spectral gap.** Two distinct eigenvalues of `relaxationOp T c i₀` differ by exactly
`|c|`, whatever the value of `T` and whatever the index type: by `relaxationOp_eigenvalue_eq` the
operator has no eigenvalue other than `T` and `T + c`, so the gap is the increment `c` alone. -/
theorem relaxationOp_gap {T c ρ₁ ρ₂ : ℝ} {i₀ : ι}
    (h₁ : ∃ u : ι → ℝ, u ≠ 0 ∧ relaxationOp T c i₀ u = ρ₁ • u)
    (h₂ : ∃ u : ι → ℝ, u ≠ 0 ∧ relaxationOp T c i₀ u = ρ₂ • u)
    (hne : ρ₁ ≠ ρ₂) : |ρ₁ - ρ₂| = |c| := by
  obtain ⟨u₁, hu₁, hh₁⟩ := h₁
  obtain ⟨u₂, hu₂, hh₂⟩ := h₂
  have e₁ := relaxationOp_eigenvalue_eq hu₁ hh₁
  have e₂ := relaxationOp_eigenvalue_eq hu₂ hh₂
  rcases e₁ with e₁ | e₁ <;> rcases e₂ with e₂ | e₂
  · exact absurd (e₁.trans e₂.symm) hne
  · rw [e₁, e₂, show T - (T + c) = -c by ring, abs_neg]
  · rw [e₁, e₂, show T + c - T = c by ring]
  · exact absurd (e₁.trans e₂.symm) hne

/-- **The gap depends on neither the temperature nor the index type.** Two distinct
eigenvalues of `relaxationOp T₁ c i₁` are separated by the same amount as two distinct
eigenvalues of `relaxationOp T₂ c i₂`, even when the two operators act on different index
types. Both gaps are `|c|` by `relaxationOp_gap`. -/
theorem relaxationOp_gap_eq_gap {ι₁ ι₂ : Type*} [DecidableEq ι₁] [DecidableEq ι₂]
    {T₁ T₂ c ρ₁ ρ₂ σ₁ σ₂ : ℝ} {i₁ : ι₁} {i₂ : ι₂}
    (h₁ : ∃ u : ι₁ → ℝ, u ≠ 0 ∧ relaxationOp T₁ c i₁ u = ρ₁ • u)
    (h₂ : ∃ u : ι₁ → ℝ, u ≠ 0 ∧ relaxationOp T₁ c i₁ u = ρ₂ • u) (hne : ρ₁ ≠ ρ₂)
    (k₁ : ∃ u : ι₂ → ℝ, u ≠ 0 ∧ relaxationOp T₂ c i₂ u = σ₁ • u)
    (k₂ : ∃ u : ι₂ → ℝ, u ≠ 0 ∧ relaxationOp T₂ c i₂ u = σ₂ • u) (hne' : σ₁ ≠ σ₂) :
    |ρ₁ - ρ₂| = |σ₁ - σ₂| := by
  rw [relaxationOp_gap h₁ h₂ hne, relaxationOp_gap k₁ k₂ hne']

end RankOne

/-! ## 4. The increment that reproduces itself -/

/-- The increment `(1 - x) / x` at `x = φ⁻¹` is `φ⁻¹` again. -/
theorem one_sub_div_inv_goldenRatio :
    (1 - goldenRatio⁻¹) / goldenRatio⁻¹ = goldenRatio⁻¹ := by
  have hinv : goldenRatio⁻¹ = goldenRatio - 1 := by
    rw [Real.inv_goldenRatio]
    linarith [Real.one_sub_goldenConj]
  rw [div_eq_iff (inv_ne_zero Real.goldenRatio_ne_zero), hinv]
  nlinarith [Real.goldenRatio_sq]

/-- `φ⁻¹` is a root of `x² + x - 1`. This is `one_sub_div_inv_goldenRatio` cleared of its
denominator, and is the polynomial form of the increment identity. -/
theorem inv_goldenRatio_sq_add_inv_goldenRatio_sub_one :
    goldenRatio⁻¹ ^ 2 + goldenRatio⁻¹ - 1 = 0 := by
  have hne : goldenRatio⁻¹ ≠ 0 := inv_ne_zero Real.goldenRatio_ne_zero
  have h2 : 1 - goldenRatio⁻¹ = goldenRatio⁻¹ * goldenRatio⁻¹ :=
    (div_eq_iff hne).mp one_sub_div_inv_goldenRatio
  linear_combination -h2

/-- **The golden characterisation of the increment.** Among positive reals, `φ⁻¹` is the *only*
`x` whose increment `(1 - x) / x` is `x` itself. Proved by substituting `y = x⁻¹`, which turns
`x ^ 2 + x - 1 = 0` into `y ^ 2 - y - 1 = 0`, and then citing
`ClassicalLean.GoldenRatio.goldenRatio_unique_pos_root`. -/
theorem one_sub_div_eq_self_iff {x : ℝ} (hx : 0 < x) :
    (1 - x) / x = x ↔ x = goldenRatio⁻¹ := by
  constructor
  · intro h
    have hxx : 1 - x = x * x := (div_eq_iff hx.ne').mp h
    have hy : (0 : ℝ) < x⁻¹ := inv_pos.mpr hx
    have hroot : x⁻¹ ^ 2 - x⁻¹ - 1 = 0 := by
      field_simp
      nlinarith [hxx]
    have hxg : x⁻¹ = goldenRatio :=
      (ClassicalLean.GoldenRatio.goldenRatio_unique_pos_root hy).mp hroot
    rw [← hxg, inv_inv]
  · rintro rfl
    exact one_sub_div_inv_goldenRatio

/-- **The golden gap.** If the increment is the one that reproduces itself, `c = φ⁻¹`, then two
distinct eigenvalues of `relaxationOp T φ⁻¹ i₀` differ by exactly `φ⁻¹`, for every `T` and every
index type. Immediate from `relaxationOp_gap`. -/
theorem relaxationOp_golden_gap {ι : Type*} [DecidableEq ι] {T ρ₁ ρ₂ : ℝ} {i₀ : ι}
    (h₁ : ∃ u : ι → ℝ, u ≠ 0 ∧ relaxationOp T goldenRatio⁻¹ i₀ u = ρ₁ • u)
    (h₂ : ∃ u : ι → ℝ, u ≠ 0 ∧ relaxationOp T goldenRatio⁻¹ i₀ u = ρ₂ • u)
    (hne : ρ₁ ≠ ρ₂) : |ρ₁ - ρ₂| = goldenRatio⁻¹ := by
  rw [relaxationOp_gap h₁ h₂ hne, abs_of_pos (inv_pos.mpr Real.goldenRatio_pos)]

/-! ## 5. A design temperature and its Boltzmann weights -/

/-- The partition function of a three-level system with energies `(0, ε, ε)` at inverse
temperature `β`: `Z(β, ε) = 1 + 2 * exp (-(β * ε))`. -/
noncomputable def boltzmannZ3 (β ε : ℝ) : ℝ := 1 + 2 * Real.exp (-(β * ε))

/-- At the design temperature the Boltzmann factor of a level of energy `φ` is `(2 φ)⁻¹`, because
`φ / designTemperature = log (2 φ)`. -/
theorem exp_neg_designTemperature_mul_goldenRatio :
    Real.exp (-(1 / designTemperature * goldenRatio)) = (2 * goldenRatio)⁻¹ := by
  have h2 : (0 : ℝ) < 2 * goldenRatio := by linarith [Real.goldenRatio_pos]
  have hne := Real.goldenRatio_ne_zero
  have hlne : Real.log (2 * goldenRatio) ≠ 0 := ne_of_gt log_two_goldenRatio_pos
  have harg : -(1 / designTemperature * goldenRatio) = -Real.log (2 * goldenRatio) := by
    rw [designTemperature]
    set L := Real.log (2 * goldenRatio)
    set x := goldenRatio
    clear_value x L
    field_simp
  rw [harg, Real.exp_neg, Real.exp_log h2]

/-- **The partition function at the design temperature is `φ`.** With energies `(0, φ, φ)`,
`Z(1/T, φ) = 1 + 2 (2 φ)⁻¹ = 1 + φ⁻¹ = φ`, the last step being the shipped
`ClassicalLean.GoldenRatio.one_add_inv_goldenRatio`. -/
theorem boltzmannZ3_designTemperature :
    boltzmannZ3 (1 / designTemperature) goldenRatio = goldenRatio := by
  have hne := Real.goldenRatio_ne_zero
  have h2inv : (2 : ℝ) * (2 * goldenRatio)⁻¹ = goldenRatio⁻¹ := by
    set x := goldenRatio
    clear_value x
    field_simp
  rw [boltzmannZ3, exp_neg_designTemperature_mul_goldenRatio, h2inv]
  exact ClassicalLean.GoldenRatio.one_add_inv_goldenRatio

/-- The Boltzmann weight of the ground level at the design temperature is `φ⁻¹`. -/
theorem boltzmannWeight_ground :
    Real.exp (-(1 / designTemperature * 0)) / boltzmannZ3 (1 / designTemperature) goldenRatio
      = goldenRatio⁻¹ := by
  rw [boltzmannZ3_designTemperature]
  norm_num

/-- The Boltzmann weight of either excited level at the design temperature is `1 / (2 φ²)`. -/
theorem boltzmannWeight_excited :
    Real.exp (-(1 / designTemperature * goldenRatio))
        / boltzmannZ3 (1 / designTemperature) goldenRatio = 1 / (2 * goldenRatio ^ 2) := by
  have hne := Real.goldenRatio_ne_zero
  rw [boltzmannZ3_designTemperature, exp_neg_designTemperature_mul_goldenRatio]
  set x := goldenRatio
  clear_value x
  field_simp

/-- The three Boltzmann weights at the design temperature, written out as a literal point of
`Fin 3 → ℝ`. It is a literal, not an object computed from `boltzmannZ3`: that the literal agrees
with the computed weights is what `boltzmannWeight_ground` and `boltzmannWeight_excited` prove.
It is the same vector as `designPoint` of `ClassicalLean.Simplex.DesignConstants`, which
`gibbsPoint_eq_designPoint` records. -/
noncomputable def gibbsPoint : Fin 3 → ℝ :=
  ![goldenRatio⁻¹, 1 / (2 * goldenRatio ^ 2), 1 / (2 * goldenRatio ^ 2)]

/-- `φ⁻¹ + (φ²)⁻¹ = 1`. This is `one_sub_designThreshold` of
`ClassicalLean.Simplex.DesignConstants` rearranged, rather than a second proof of it. -/
theorem inv_goldenRatio_add_inv_goldenRatio_sq : goldenRatio⁻¹ + (goldenRatio ^ 2)⁻¹ = 1 := by
  have h := one_sub_designThreshold
  rw [designThreshold] at h
  linarith

/-- The Boltzmann weights are a probability vector: they are nonnegative and sum to `1`. -/
theorem gibbsPoint_mem_closedSimplex : gibbsPoint ∈ closedSimplex (Fin 3) := by
  have h1 : (0 : ℝ) ≤ goldenRatio⁻¹ := (inv_pos.mpr Real.goldenRatio_pos).le
  have h2 : (0 : ℝ) ≤ 1 / (2 * goldenRatio ^ 2) := by positivity
  refine ⟨fun i ↦ ?_, ?_⟩
  · fin_cases i
    · exact h1
    · exact h2
    · exact h2
  · have h := Real.goldenRatio_sq
    have hne := Real.goldenRatio_ne_zero
    simp only [gibbsPoint, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    set x := goldenRatio
    clear_value x
    field_simp
    linarith

/-- The Boltzmann weights are the `designPoint` of `ClassicalLean.Simplex.DesignConstants`:
the two literals denote the same vector, since `designThreshold = φ⁻¹` and
`designSecond = (2 φ²)⁻¹`. -/
theorem gibbsPoint_eq_designPoint : gibbsPoint = designPoint := by
  simp only [gibbsPoint, designPoint, designThreshold, designSecond_eq, one_div]

/-- The Boltzmann weights lie in the *open* simplex, every coordinate being strictly positive.
This strengthens `gibbsPoint_mem_closedSimplex`, and comes from `designPoint_mem_openSimplex`. -/
theorem gibbsPoint_mem_openSimplex : gibbsPoint ∈ openSimplex (Fin 3) := by
  rw [gibbsPoint_eq_designPoint]
  exact designPoint_mem_openSimplex

/-- The energy levels `(0, φ, φ)` of the three-level system. The gap `φ` between the ground level
and the two excited levels is a *chosen* constant, not one derived here. -/
noncomputable def energyLevels : Fin 3 → ℝ := ![0, goldenRatio, goldenRatio]

/-- **The internal energy.** `∑ i, p i * E i = φ⁻¹` for the Boltzmann weights `p = gibbsPoint`
against the levels `(0, φ, φ)`. -/
theorem internalEnergy_gibbsPoint : ∑ i, gibbsPoint i * energyLevels i = goldenRatio⁻¹ := by
  have hne := Real.goldenRatio_ne_zero
  simp only [gibbsPoint, energyLevels, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  set x := goldenRatio
  clear_value x
  field_simp
  ring

/-- The Shannon entropy of the Boltzmann weights, before the golden identities are applied:
`H = φ⁻¹ log φ + (φ²)⁻¹ log (2 φ²)`. This step is pure algebra — it only uses `φ ≠ 0` and
`log x⁻¹ = -log x`. -/
theorem shannonEntropy_gibbsPoint_aux :
    shannonEntropy gibbsPoint
      = goldenRatio⁻¹ * Real.log goldenRatio
        + (goldenRatio ^ 2)⁻¹ * Real.log (2 * goldenRatio ^ 2) := by
  have hne := Real.goldenRatio_ne_zero
  simp only [shannonEntropy, Fin.sum_univ_three, gibbsPoint, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    one_div, Real.log_inv]
  set L := Real.log (2 * goldenRatio ^ 2)
  set A := Real.log goldenRatio
  set x := goldenRatio
  clear_value x L A
  field_simp
  ring

/-- **The Shannon entropy of the Boltzmann weights** is `log φ + log (2 φ) / φ²`. The two golden
inputs are `Real.log_mul` on `2 φ² = (2 φ) * φ` and `inv_goldenRatio_add_inv_goldenRatio_sq`. -/
theorem shannonEntropy_gibbsPoint :
    shannonEntropy gibbsPoint
      = Real.log goldenRatio + Real.log (2 * goldenRatio) / goldenRatio ^ 2 := by
  have hne := Real.goldenRatio_ne_zero
  have h2 : (0 : ℝ) < 2 * goldenRatio := by linarith [Real.goldenRatio_pos]
  have hlog2 : Real.log (2 * goldenRatio ^ 2)
      = Real.log (2 * goldenRatio) + Real.log goldenRatio := by
    rw [show (2 : ℝ) * goldenRatio ^ 2 = 2 * goldenRatio * goldenRatio by ring]
    exact Real.log_mul (ne_of_gt h2) hne
  rw [shannonEntropy_gibbsPoint_aux, hlog2,
    show goldenRatio⁻¹ * Real.log goldenRatio
        + (goldenRatio ^ 2)⁻¹ * (Real.log (2 * goldenRatio) + Real.log goldenRatio)
      = (goldenRatio⁻¹ + (goldenRatio ^ 2)⁻¹) * Real.log goldenRatio
        + (goldenRatio ^ 2)⁻¹ * Real.log (2 * goldenRatio) from by ring,
    inv_goldenRatio_add_inv_goldenRatio_sq, one_mul, div_eq_inv_mul]

/-- The **Helmholtz free energy** `F = -T log Z` of the three-level system at the design
temperature, formed from this file's own partition function. Context, not proved here: that
`-T log Z` is the right definition of free energy. -/
noncomputable def helmholtzFreeEnergy : ℝ :=
  -designTemperature * Real.log (boltzmannZ3 (1 / designTemperature) goldenRatio)

/-- The Helmholtz entropy `S = (E - F) / T` of the three-level system at the design temperature,
written with `E = φ⁻¹` and `F = -T log φ` already substituted. The substitution is *proved*, not
assumed: `helmholtzEntropy_eq_internalEnergy_sub_free` shows this literal is
`(∑ i, gibbsPoint i * energyLevels i - helmholtzFreeEnergy) / designTemperature`, using
`internalEnergy_gibbsPoint` and `boltzmannZ3_designTemperature`. Context, not proved here: that
`(E - F)/T` is the right definition of thermodynamic entropy. -/
noncomputable def helmholtzEntropy : ℝ :=
  (goldenRatio⁻¹ + designTemperature * Real.log goldenRatio) / designTemperature

/-- The Helmholtz entropy in closed form: `log φ + log (2 φ) / φ²`. -/
theorem helmholtzEntropy_eq :
    helmholtzEntropy = Real.log goldenRatio + Real.log (2 * goldenRatio) / goldenRatio ^ 2 := by
  have hne := Real.goldenRatio_ne_zero
  have hlne : Real.log (2 * goldenRatio) ≠ 0 := ne_of_gt log_two_goldenRatio_pos
  rw [helmholtzEntropy, designTemperature]
  set L := Real.log (2 * goldenRatio)
  set A := Real.log goldenRatio
  set x := goldenRatio
  clear_value x L A
  field_simp
  ring

/-- **The entropy literal is `(E - F)/T` of the objects defined in this file.** The internal
energy is `∑ i, gibbsPoint i * energyLevels i` and the free energy is `helmholtzFreeEnergy`;
rewriting them by `internalEnergy_gibbsPoint` and `boltzmannZ3_designTemperature` gives exactly
the definition of `helmholtzEntropy`. -/
theorem helmholtzEntropy_eq_internalEnergy_sub_free :
    helmholtzEntropy
      = ((∑ i, gibbsPoint i * energyLevels i) - helmholtzFreeEnergy) / designTemperature := by
  rw [helmholtzEntropy, helmholtzFreeEnergy, internalEnergy_gibbsPoint,
    boltzmannZ3_designTemperature]
  ring

/-- **Thermodynamic consistency at the design temperature.** The Helmholtz entropy — identified
with `(E - F) / T` for this file's own internal energy and free energy by
`helmholtzEntropy_eq_internalEnergy_sub_free` — equals the Shannon entropy of the Boltzmann
weights. -/
theorem helmholtzEntropy_eq_shannonEntropy :
    helmholtzEntropy = shannonEntropy gibbsPoint := by
  rw [helmholtzEntropy_eq, shannonEntropy_gibbsPoint]

/-! ## Arithmetic checks -/

/-- At infinite temperature (`β = 0`) the three-level partition function counts the levels. -/
example : boltzmannZ3 0 1 = 3 := by
  rw [boltzmannZ3, show -((0 : ℝ) * 1) = 0 by ring, Real.exp_zero]
  norm_num

/-- The uniform vector on three points lies in the open simplex. -/
example : (fun _ ↦ (1 : ℝ) / 3) ∈ openSimplex (Fin 3) :=
  ⟨fun _ ↦ by norm_num, by simp⟩

/-- A Fisher–Rao norm at the uniform point of a two-point simplex. -/
example : fisherRao ![(1 : ℝ) / 2, 1 / 2] ![1, -1] ![1, -1] = 4 := by
  rw [fisherRao, Fin.sum_univ_two]
  change (1 : ℝ) * 1 / (1 / 2) + -1 * -1 / (1 / 2) = 4
  have h₀ : (1 : ℝ) * 1 / (1 / 2) = 2 := by norm_num
  have h₁ : (-1 : ℝ) * -1 / (1 / 2) = 2 := by norm_num
  rw [h₀, h₁]
  norm_num

end ClassicalLean.Simplex
