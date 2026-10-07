/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import ClassicalLean.GoldenRatio.Characterisations

/-!
# A companion matrix for `t² - 3t + 1`, and a great circle in the unit quaternions

Two subjects that arrived together in the source material and are kept in one file. Nothing below
connects them: the companion matrix and the curve are independent.

**Part 1.** The companion matrix `!![0, -1; 1, 3]` of the quadratic `t² - 3t + 1`. Its trace is
`3`, its determinant is `1`, and `det(M - x·I) = x² - 3x + 1` for every real `x`. The real numbers
at which that determinant vanishes are exactly `φ²` and `(φ²)⁻¹`, for Mathlib's `Real.goldenRatio`.
Writing `ψ` for `Real.goldenConj`, the second root is also `ψ²`
(`inv_goldenRatio_sq_eq_goldenConj_sq`), and in that naming Vieta's two relations for this
quadratic are `φ² + ψ² = 3` and `φ² · ψ² = 1`; the product one is proved from Mathlib's
`Real.goldenRatio_mul_goldenConj` (`φψ = -1`), so it is a fact about two independently named roots
and not the notational identity `x · x⁻¹ = 1`. The two roots differ by `√5`
(`goldenRatio_sq_sub_inv_eq_sqrt_five`) and the square of that difference is the discriminant `5`
(`goldenRatio_sq_sub_inv_sq_eq_five`). That the product of the roots and `det M` are both `1` is
Vieta's theorem for a monic quadratic; the general statement is not proved here, and neither of
those two theorems is derived from the other. The matrix satisfies its own quadratic
(Cayley–Hamilton), and `(1, -φ²)` is an eigenvector for `φ²`.

As in `ClassicalLean.GoldenRatio.Characterisations`, everything about the "eigenvalues" is stated
through the vanishing of `det(M - x·I)` over `ℝ`, because that is what is proved; the general
bridge from a vanishing determinant to the spectrum of an operator is not proved here.

**Part 2.** For a nonzero real `T`, the curve `t ↦ cos(2πt/T) + sin(2πt/T)·k` of unit
quaternions. It lies on `S³` (`helix_normSq`), it converts addition to quaternion multiplication
(`helix_add`) and sends `0` to `1` (`helix_zero`) — no bundled homomorphism and no group of unit
quaternions is constructed here, so "one-parameter subgroup" below is a reading of those two
theorems, not a third one. Its value at `T/2` is `-1` and at `T` is `1`, it is `T`-periodic and
`T/2`-antiperiodic, and `T` is its *smallest* positive period. Context, not proved here: the
half-period value `-1` is the reason a rotation by `2π` is represented by `-1` rather than `1` in
the unit quaternions — but no rotation is defined in this file, so that reading is a remark.

The curve is parametrised by an arbitrary period `T`; the source fixed one particular value, which
carried no mathematical content here and has been generalised away.

**What the source file `TowerHelix_S3_Embedding.lean` had that is not shipped here.** One line per
source declaration, so that a drop is a decision on the record rather than a silence.

* `PHI`, `phi_pos`, `phi_gt_one`, `phi_sq`, `phi_sq_pos` — dropped: Mathlib's `Real.goldenRatio`,
  `Real.goldenRatio_pos`, `Real.one_lt_goldenRatio` and `Real.goldenRatio_sq` are these, and this
  file uses Mathlib's throughout rather than redefining the constant.
* `inv_phi_sq` (`(PHI²)⁻¹ = (PHI⁻¹)²`) — dropped: Mathlib's `inv_pow`. The fact this file needs in
  its place, `(φ²)⁻¹ = ψ²`, is shipped as `inv_goldenRatio_sq_eq_goldenConj_sq`.
* `T_STAR`, `OMEGA`, `two_phi_gt_two`, `log_two_phi_pos`, `t_star_pos`, `helix_period_from_omega` —
  dropped: all are about the one fixed period the source chose. With `T` a free positive parameter
  there is no constant to bound below and no `ω·T = 2π` bookkeeping to do; `t_star_pos` reappears
  as the hypothesis `0 < T` of `helix_le_of_periodic`.
* `phi_sq_plus_inv`, `eigenvalue_sum_three` — shipped as `goldenRatio_sq_add_inv_eq_three`.
  Dated 2026-09-24 (order G-7, J2 step 6; round 23): that statement and
  `inv_goldenRatio_sq_eq_goldenConj_sq` now live in `GoldenRatio/Characterisations`, as
  `ClassicalLean.GoldenRatio.…`; this file imports it, and every mention of the two names
  here refers to them.
* `phi_sq_times_inv`, `eigenvalue_product_one` (`PHI² · (PHI²)⁻¹ = 1`) — **not shipped in that
  form**, deliberately: written that way the equation is an instance of `x · x⁻¹ = 1` and says
  nothing about the quadratic. Reshaped into `goldenRatio_sq_mul_goldenConj_sq` (`φ² · ψ² = 1`,
  from `φψ = -1`) together with `inv_goldenRatio_sq_eq_goldenConj_sq`.
* `phi_sq_root_char_poly`, `inv_phi_sq_root_char_poly` — subsumed: each is the `mpr` direction of
  the shipped `sq_sub_three_mul_add_one_eq_zero_iff`, which also proves there are no other real
  roots.
* `monodromy_saddle` (`PHI² > 1 ∧ (PHI²)⁻¹ < 1`) — subsumed: it is the conjunction of the shipped
  `one_lt_goldenRatio_sq` and `inv_goldenRatio_sq_lt_one`, and is not restated as a pair.
* `monodromy_hyperbolic` (`trace M > 2`) — **not shipped as a theorem**: it appears below only as an
  anonymous `example`, which introduces no constant, is unaddressable from another module, and is
  invisible to the axiom and vacuity gates. Count it as dropped with an elaboration check, not as a
  ported theorem. Its content is `companionMatrix_trace` plus `2 < 3`.
* `M`, `monodromy_trace`, `monodromy_det`, `monodromy_cayley_hamilton`, `helix`, `helix_on_s3`,
  `helix_anti_period`, `helix_full_period`, `helix_period_theorem`, `phi_sq_gt_one`,
  `inv_phi_sq_lt_one`, `eigenvalues_distinct` — shipped, under the names used below.
-/

open scoped Quaternion
open Real

namespace ClassicalLean.Geometry

/-! ## Part 1: the companion matrix of `t² - 3t + 1` -/

/-- The companion matrix `!![0, -1; 1, 3]` of the quadratic `t² - 3t + 1`. -/
def companionMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 3]

/-- The trace is `3`, the negated linear coefficient of `t² - 3t + 1`. -/
theorem companionMatrix_trace : companionMatrix.trace = 3 := by
  simp [companionMatrix, Matrix.trace_fin_two]

/-- The determinant is `1`, the constant coefficient of `t² - 3t + 1`. -/
theorem companionMatrix_det : companionMatrix.det = 1 := by
  simp [companionMatrix, Matrix.det_fin_two]

/-- **The characteristic polynomial.** `det(M - x·I) = x² - 3x + 1` for every real `x`. -/
theorem companionMatrix_det_sub_smul (x : ℝ) :
    (companionMatrix - x • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = x ^ 2 - 3 * x + 1 := by
  simp [companionMatrix, Matrix.det_fin_two, Matrix.sub_apply, Matrix.smul_apply]
  ring

/-- **Vieta's product relation for this quadratic.** `φ² · ψ² = 1`, for `ψ = Real.goldenConj`.

Stated with the two roots named independently, so that it is a fact and not a notational identity:
it is `(φψ)² = (-1)² = 1`, resting on Mathlib's `Real.goldenRatio_mul_goldenConj`. Written instead
as `φ² · (φ²)⁻¹ = 1` the same equation would be an instance of `x · x⁻¹ = 1`, true of every nonzero
real and carrying nothing about `t² - 3t + 1`; the content is exactly that the second root is `ψ²`,
which is `inv_goldenRatio_sq_eq_goldenConj_sq`. -/
theorem goldenRatio_sq_mul_goldenConj_sq :
    goldenRatio ^ 2 * goldenConj ^ 2 = 1 := by
  have h : (goldenRatio * goldenConj) ^ 2 = 1 := by
    rw [Real.goldenRatio_mul_goldenConj]
    norm_num
  linear_combination h

/-- **The gap between the roots is `√5`.** `φ² - (φ²)⁻¹ = √5` — the same `√5` that appears in
Mathlib's definition `Real.goldenRatio = (1 + √5)/2`. Proved by rewriting the second root with
`inv_goldenRatio_sq_eq_goldenConj_sq`, flattening both squares with `Real.goldenRatio_sq` and
`Real.goldenConj_sq`, and finishing from `Real.goldenRatio_sub_goldenConj` (`φ - ψ = √5`). -/
theorem goldenRatio_sq_sub_inv_eq_sqrt_five :
    goldenRatio ^ 2 - (goldenRatio ^ 2)⁻¹ = Real.sqrt 5 := by
  rw [GoldenRatio.inv_goldenRatio_sq_eq_goldenConj_sq, Real.goldenRatio_sq, Real.goldenConj_sq]
  linear_combination Real.goldenRatio_sub_goldenConj

/-- **The discriminant of `t² - 3t + 1` is `5`.** `(φ² - (φ²)⁻¹)² = 5`: the squared gap between the
two roots is `3² - 4·1·1`. Derived from the two Vieta relations alone —
`(a - b)² = (a + b)² - 4ab = 3² - 4` — so this is a statement about the roots of *this* quadratic
and not an arithmetic evaluation of the numerals `3`, `4` and `5`. -/
theorem goldenRatio_sq_sub_inv_sq_eq_five :
    (goldenRatio ^ 2 - (goldenRatio ^ 2)⁻¹) ^ 2 = 5 := by
  have h1 := GoldenRatio.goldenRatio_sq_add_inv_eq_three
  have h2 : goldenRatio ^ 2 * (goldenRatio ^ 2)⁻¹ = 1 := by
    rw [GoldenRatio.inv_goldenRatio_sq_eq_goldenConj_sq]
    exact goldenRatio_sq_mul_goldenConj_sq
  nlinarith [h1, h2]

/-- **Completeness of the root list.** A real number satisfies `x² - 3x + 1 = 0` if and only if
it is `φ²` or `(φ²)⁻¹`. The proof factors the quadratic as `(x - φ²)(x - (φ²)⁻¹)` using the sum
relation `goldenRatio_sq_add_inv_eq_three` and the product relation
`goldenRatio_sq_mul_goldenConj_sq`, the latter carried across by
`inv_goldenRatio_sq_eq_goldenConj_sq`. -/
theorem sq_sub_three_mul_add_one_eq_zero_iff (x : ℝ) :
    x ^ 2 - 3 * x + 1 = 0 ↔ x = goldenRatio ^ 2 ∨ x = (goldenRatio ^ 2)⁻¹ := by
  have h1 := GoldenRatio.goldenRatio_sq_add_inv_eq_three
  have h2 : goldenRatio ^ 2 * (goldenRatio ^ 2)⁻¹ = 1 := by
    rw [GoldenRatio.inv_goldenRatio_sq_eq_goldenConj_sq]
    exact goldenRatio_sq_mul_goldenConj_sq
  have hfac : ∀ y : ℝ, y ^ 2 - 3 * y + 1 = (y - goldenRatio ^ 2) * (y - (goldenRatio ^ 2)⁻¹) := by
    intro y
    have hy : (y - goldenRatio ^ 2) * (y - (goldenRatio ^ 2)⁻¹)
        = y ^ 2 - (goldenRatio ^ 2 + (goldenRatio ^ 2)⁻¹) * y
          + goldenRatio ^ 2 * (goldenRatio ^ 2)⁻¹ := by ring
    rw [hy, h1, h2]
  constructor
  · intro hx
    rcases mul_eq_zero.mp ((hfac x) ▸ hx) with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  · rintro (rfl | rfl) <;> rw [hfac] <;> ring

/-- **The real numbers at which the characteristic determinant vanishes** are exactly `φ²` and
`(φ²)⁻¹`. This is `companionMatrix_det_sub_smul` composed with the root-list lemma; it is a
statement about real `x` only, and says nothing about eigenvalues over `ℂ`. -/
theorem companionMatrix_det_sub_smul_eq_zero_iff (x : ℝ) :
    (companionMatrix - x • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 ↔
      x = goldenRatio ^ 2 ∨ x = (goldenRatio ^ 2)⁻¹ := by
  rw [companionMatrix_det_sub_smul]
  exact sq_sub_three_mul_add_one_eq_zero_iff x

/-- The vector `(1, -φ²)` is nonzero — its first coordinate is `1`. Recorded so that the word
"eigenvector" below is backed by a proof: an eigenvector is by definition nonzero. -/
theorem companionMatrix_vec_ne_zero : ![1, -goldenRatio ^ 2] ≠ (0 : Fin 2 → ℝ) := by
  intro h
  have h1 : (![1, -goldenRatio ^ 2] : Fin 2 → ℝ) 0 = (0 : Fin 2 → ℝ) 0 := by rw [h]
  simp at h1

/-- **An eigenpair.** `M ⬝ᵥ (1, -φ²) = φ² • (1, -φ²)`, and `companionMatrix_vec_ne_zero` supplies
the nonvanishing that the word "eigenvector" requires. The computation reduces to
`(φ²)² - 3φ² + 1 = 0`. -/
theorem companionMatrix_mulVec_eigen :
    companionMatrix.mulVec ![1, -goldenRatio ^ 2]
      = goldenRatio ^ 2 • ![1, -goldenRatio ^ 2] := by
  funext i
  fin_cases i
  · simp [companionMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [companionMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination Real.goldenRatio_sq

/-- **Cayley–Hamilton for this matrix.** `M² - 3·M + I = 0`, the matrix satisfying its own
characteristic quadratic. -/
theorem companionMatrix_sq_sub :
    companionMatrix ^ 2 - (3 : ℝ) • companionMatrix + 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [companionMatrix, pow_two]

/-- `1 < φ²`, since `φ² = φ + 1` and `1 < φ`. -/
theorem one_lt_goldenRatio_sq : 1 < goldenRatio ^ 2 := by
  rw [Real.goldenRatio_sq]
  linarith [Real.one_lt_goldenRatio]

/-- `(φ²)⁻¹ < 1`, the reciprocal of the previous bound. -/
theorem inv_goldenRatio_sq_lt_one : (goldenRatio ^ 2)⁻¹ < 1 := by
  rw [inv_lt_one_iff₀]
  exact Or.inr one_lt_goldenRatio_sq

/-- The two roots are distinct: `φ² ≠ (φ²)⁻¹`, since one exceeds `1` and the other does not. Hence
`det(M - x·I)` has two distinct real roots. -/
theorem goldenRatio_sq_ne_inv : goldenRatio ^ 2 ≠ (goldenRatio ^ 2)⁻¹ := by
  intro h
  have h1 := one_lt_goldenRatio_sq
  have h2 := inv_goldenRatio_sq_lt_one
  rw [← h] at h2
  linarith

/-! ## Part 2: a great circle in the unit quaternions -/

/-- The curve `t ↦ cos(2πt/T) + sin(2πt/T)·k` in `ℍ`. Its image lies on the great circle of `S³`
cut out by the real plane spanned by `1` and `k`: the `imI` and `imJ` components vanish by
definition, and `helix_normSq` puts the curve on `S³`. -/
noncomputable def helix (T t : ℝ) : ℍ :=
  (⟨Real.cos (2 * π * t / T), 0, 0, Real.sin (2 * π * t / T)⟩ : ℍ)

/-- The curve lies on `S³`: `normSq (helix T t) = 1`, by `sin² + cos² = 1`. -/
theorem helix_normSq (T t : ℝ) : Quaternion.normSq (helix T t) = 1 := by
  rw [Quaternion.normSq_def']
  simp only [helix]
  nlinarith [Real.sin_sq_add_cos_sq (2 * π * t / T)]

/-- **The addition law.** `helix T (s + t) = helix T s * helix T t`: the map `ℝ → ℍ` carries
addition to quaternion multiplication. With `helix_zero` this is what "one-parameter subgroup"
means, but no bundled `MonoidHom` is constructed and no subgroup is formed, so that phrase stays a
reading of these two theorems. The proof is the addition formulas for `cos` and `sin`, read through
the quaternion product in the `(1, k)`-plane. -/
theorem helix_add (T s t : ℝ) : helix T (s + t) = helix T s * helix T t := by
  have harg : 2 * π * (s + t) / T = 2 * π * s / T + 2 * π * t / T := by ring
  apply Quaternion.ext
  · simp [helix, harg, Real.cos_add]
  · simp [helix]
  · simp [helix]
  · simp [helix, harg, Real.sin_add]
    ring

/-- The curve starts at `1`. -/
theorem helix_zero (T : ℝ) : helix T 0 = 1 := by
  apply Quaternion.ext <;> simp [helix]

/-- **The half-period value is `-1`, not `1`.** `helix T (T/2) = -1`: after half a period the
curve has reached the antipode of its starting point. -/
theorem helix_half (T : ℝ) (hT : T ≠ 0) : helix T (T / 2) = -1 := by
  have harg : 2 * π * (T / 2) / T = π := by field_simp
  apply Quaternion.ext <;> simp [helix, harg]

/-- The full-period value is `1`. -/
theorem helix_full (T : ℝ) (hT : T ≠ 0) : helix T T = 1 := by
  have harg : 2 * π * T / T = 2 * π := by field_simp
  apply Quaternion.ext <;> simp [helix, harg]

/-- The curve is `T`-periodic, in Mathlib's sense `Function.Periodic`. Proved from `helix_add`
and `helix_full`, so periodicity is the group law applied to the identity element. -/
theorem helix_periodic (T : ℝ) (hT : T ≠ 0) : Function.Periodic (helix T) T := by
  intro t
  rw [helix_add, helix_full T hT, mul_one]

/-- The curve is `T/2`-antiperiodic, in Mathlib's sense `Function.Antiperiodic`: half a period
negates it. Proved from `helix_add` and `helix_half`. -/
theorem helix_antiperiodic (T : ℝ) (hT : T ≠ 0) : Function.Antiperiodic (helix T) (T / 2) := by
  intro t
  rw [helix_add, helix_half T hT, mul_neg_one]

/-- **`T` is the minimal positive period.** Every positive period of `helix T` is at least `T`.
The proof reads `cos(2πS/T) = 1` off the real part of the period condition at `t = 0`, uses
Mathlib's `Real.cos_eq_one_iff` to get `S = n·T` for an integer `n`, and concludes `n ≥ 1` from
positivity. Together with `helix_periodic`, this makes `T` the minimal positive period. -/
theorem helix_le_of_periodic {T S : ℝ} (hT : 0 < T) (hS : 0 < S)
    (h : Function.Periodic (helix T) S) : T ≤ S := by
  have hTne : T ≠ 0 := ne_of_gt hT
  have hcos : Real.cos (2 * π * S / T) = 1 := by
    have h0 := congrArg (fun q : ℍ => q.re) (h 0)
    simpa [helix] using h0
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).mp hcos
  rw [eq_div_iff hTne] at hn
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  have hnT : (n : ℝ) * T = S := mul_left_cancel₀ h2pi (by linear_combination hn)
  have hn_pos : 0 < (n : ℝ) := by
    by_contra hc
    push Not at hc
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc (le_of_lt hT)]
  have hnZ : 0 < n := by exact_mod_cast hn_pos
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnZ
  nlinarith [hnT]

/-! ## Concrete instances -/

/-- The companion matrix squared is `!![-1, -3; 3, 8]`. -/
example : companionMatrix ^ 2 = !![(-1 : ℝ), -3; 3, 8] := by
  rw [pow_two, companionMatrix, Matrix.mul_fin_two]
  norm_num

/-- The trace exceeds `2`. Context, not proved here: for a real quadratic `t² - pt + 1` this is
the classical criterion for two distinct positive real roots. What this file actually proves
about the roots is `one_lt_goldenRatio_sq`, `inv_goldenRatio_sq_lt_one` and
`goldenRatio_sq_ne_inv`. -/
example : (2 : ℝ) < companionMatrix.trace := by
  rw [companionMatrix_trace]
  norm_num

end ClassicalLean.Geometry
