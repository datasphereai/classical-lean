/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Simplex.SecondOrder
import ClassicalLean.Statistics.GaussMarkov

/-!
# The Cramér–Rao inequality on a finite outcome set

On a finite outcome set `Ω` with weights `p`, take a statistic `T` and scores `S`, both with
one row per parameter (`T S : Matrix κ Ω ℝ`). Write `E T i = ∑ ω, p ω * T i ω`
(`weightedMean`), `Cov T` for the weighted covariance of the rows of `T` (`weightedCov`) and
`E[S Sᵀ]` for the weighted second moment of the scores (`secondMoment`), the Fisher information
when `S` is the score. The weights are not divided by their sum; the readings as a mean, a
covariance and a Fisher information are the standard ones when `∑ p = 1`.

The **information inequality**: if `p ≥ 0` and

    ∑ ω, p ω * (T i ω - E T i) * S j ω = if i = j then 1 else 0      (the hypothesis `h`)

then `Cov T - (E[S Sᵀ])⁻¹` is positive semidefinite
(`posSemidef_weightedCov_sub_inv_secondMoment`). With `E S = 0`, `h` says `E[T Sᵀ] = 1`, the
derivative of unbiasedness; with `∑ p = 1` as well, this is the **Cramér–Rao bound** for an
unbiased estimator on a finite outcome set. Neither `∑ p = 1` nor `E S = 0` is used by the proof,
so neither is a hypothesis; the categorical family below proves both for its own `p` and `S`.

The proof is the **Gauss–Markov theorem** in weighted coordinates. Scale the columns by `√p`:
`C = (T - E T) diag √p` and `X = diag √p Sᵀ`. Then `C X` is the matrix of `h`, so `C X = 1`;
`Xᵀ X = E[S Sᵀ]` and `C Cᵀ = Cov T`; and `posSemidef_self_mul_transpose_sub_inv` of
`Statistics/GaussMarkov` is the inequality. The **equality case** is Gauss–Markov's
`self_mul_transpose_eq_inv_iff`: with every weight positive, equality holds exactly for the
efficient statistic `T - E T = (E[S Sᵀ])⁻¹ S` (`weightedCov_eq_inv_secondMoment_iff`), whose proof
unfolds `leastSquares`. Under the hypotheses `E[S Sᵀ]` is invertible
(`isUnit_det_secondMoment`), so its inverse never takes Mathlib's junk value `0`.

## The categorical family

At `p = ![lam, kap, eta]`, `eta = 1 - lam - kap`, in the chart of `Simplex/Hessian`: the weights
sum to `1`; the scores `categoricalScore lam kap` have mean `0` (`weightedMean_categoricalScore`)
and Fisher information `Simplex.fisherRaoChart lam kap` (`secondMoment_categoricalScore`); the
one-hot statistic `categoricalOneHot` is unbiased, its mean is `![lam, kap]`
(`weightedMean_categoricalOneHot`), and it satisfies `h`
(`crossMoment_categoricalOneHot_categoricalScore`); its covariance is
`Simplex.categoricalCov ![lam, kap]` (`weightedCov_categoricalOneHot`), which by
`Simplex.fisherRaoChart_mul_categoricalCov` is the inverse of the Fisher information, so the
one-hot statistic **attains** the bound (`weightedCov_categoricalOneHot_eq_inv_secondMoment`).

## Junk values, enumerated first

Measured with exact rational arithmetic before this file was written (order G-6 round 21).
The general theorems: in 3000 random trials (unnormalised `p`, uncentred `S`, zero weights),
`h` was satisfiable in 1942 and `T` was solved for it exactly; in none of those was `E[S Sᵀ]`
singular, and the inequality never failed.
`0 ≤ p` is needed: at `p = ![1, -1]`, `T = !![1, 0]`, `S = !![1, 1]` the hypothesis holds,
`E[S Sᵀ] = 0` and `Cov T = !![-1]`. The equality case needs every weight positive: at
`p = ![0, 1/4, 9/4]`, `S = !![5, 2, -1/3]`, `T = !![167/15, 26/15, -2/15]` the hypothesis holds
and `Cov T = (E[S Sᵀ])⁻¹ = !![4/5]`, but `(T - E T) 0 = 11 ≠ 4 = (E[S Sᵀ]⁻¹ S) 0`. The categorical
family: `E S = 0` and `h` fail at every zero cell (`lam = 0`, `kap = 0` or `eta = 0`);
`secondMoment_categoricalScore` and `weightedCov_categoricalOneHot` hold at every point, zero
cells included; the attainment `weightedCov_categoricalOneHot_eq_inv_secondMoment` fails on
the edges of the simplex and holds at its three vertices only because Mathlib's inverse of the
singular matrix there is `0`. The family is saturated: every `T` satisfying `h` there attains the
bound, so the instance shows attainment, not that the inequality can be strict.

## Mathlib at v4.34.0

Searched before this file was written, from Mathlib's root, `grep -rniE '<pattern>' Mathlib
--include=*.lean`: `cram[eé]r.?rao` 0 (Mathlib's Cramér-named results are Cramer's rule,
`Matrix.cramer`, and the Cramér–Wold theorem, `Probability/CramerWold.lean`),
`fisher.?info|fisherInformation` 0, `information.?inequality` 0. By shape, Mathlib's nearest
result is the Schur-complement criterion `Matrix.PosDef.fromBlocks₁₁` / `fromBlocks₂₂`, the other
textbook route (the joint Gram matrix of `T - E T` and `S` is positive semidefinite, and its Schur
complement is `Cov T - (E[S Sᵀ])⁻¹`); this file follows the Gauss–Markov route. The Apache-2.0
library `github.com/FujiHaruka/information-theory` (at `7e97b77`) has Fisher information for
densities (de Bruijn, Stam) and no Cramér–Rao (recorded in order G-6 §0 row 7; not re-run here).
-/

namespace ClassicalLean.Statistics

open Matrix

section Definitions

variable {Ω κ : Type*} [Fintype Ω]

/-- `E T i = ∑ ω, p ω * T i ω`, the weighted sum of each row of `T`: its mean when `∑ p = 1`.
The weights are not divided by their sum. -/
def weightedMean (p : Ω → ℝ) (T : Matrix κ Ω ℝ) : κ → ℝ := fun i => ∑ ω, p ω * T i ω

/-- `(Cov T) i j = ∑ ω, p ω * (T i ω - E T i) * (T j ω - E T j)`, the covariance of the rows of
`T` when `∑ p = 1`. The weights are not divided by their sum. -/
def weightedCov (p : Ω → ℝ) (T : Matrix κ Ω ℝ) : Matrix κ κ ℝ :=
  Matrix.of fun i j => ∑ ω, p ω * (T i ω - weightedMean p T i) * (T j ω - weightedMean p T j)

/-- `E[S Sᵀ] i j = ∑ ω, p ω * S i ω * S j ω`: the Fisher information when `S` is the score and
`∑ p = 1`. -/
def secondMoment (p : Ω → ℝ) (S : Matrix κ Ω ℝ) : Matrix κ κ ℝ :=
  Matrix.of fun i j => ∑ ω, p ω * S i ω * S j ω

/-- For nonnegative weights `p`, scaling the columns of two matrices by `√p` and multiplying one
by the transpose of the other gives the `p`-weighted sums of products of their rows. -/
private theorem of_mul_sqrt_mul_transpose {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω)
    (A B : κ → Ω → ℝ) :
    (Matrix.of fun i ω => A i ω * √(p ω)) * (Matrix.of fun j ω => B j ω * √(p ω))ᵀ
      = Matrix.of fun i j => ∑ ω, p ω * A i ω * B j ω := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun ω _ => ?_
  linear_combination (A i ω * B j ω) * Real.mul_self_sqrt (hp ω)

end Definitions

variable {Ω κ : Type*} [Fintype Ω] [Fintype κ] [DecidableEq κ]

/-- Under the hypotheses of the information inequality, `E[S Sᵀ]` is invertible, so its inverse
never takes Mathlib's junk value `0`. -/
theorem isUnit_det_secondMoment {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) {T S : Matrix κ Ω ℝ}
    (h : ∀ i j, ∑ ω, p ω * (T i ω - weightedMean p T i) * S j ω = if i = j then 1 else 0) :
    IsUnit (secondMoment p S).det := by
  have hCX : (Matrix.of fun i ω => (T i ω - weightedMean p T i) * √(p ω))
      * (Matrix.of fun j ω => S j ω * √(p ω))ᵀ = 1 :=
    (of_mul_sqrt_mul_transpose hp (fun i ω => T i ω - weightedMean p T i) S).trans
      (by ext i j; simp [h i j, Matrix.one_apply])
  have hXX : (Matrix.of fun i ω => S i ω * √(p ω)) * (Matrix.of fun j ω => S j ω * √(p ω))ᵀ
      = secondMoment p S := of_mul_sqrt_mul_transpose hp S S
  have := isUnit_det_transpose_mul_self_of_mul_eq_one hCX
  rwa [Matrix.transpose_transpose, hXX] at this

/-- **The information inequality (Cramér–Rao) on a finite outcome set.** With nonnegative
weights, if `∑ ω, p ω * (T i ω - E T i) * S j ω` is `1` on the diagonal and `0` off it, then
`Cov T - (E[S Sᵀ])⁻¹` is positive semidefinite. With `∑ p = 1` and `E S = 0` the hypothesis says
`E[T Sᵀ] = 1`, the derivative of unbiasedness; neither is used by the proof. It is the
Gauss–Markov theorem `posSemidef_self_mul_transpose_sub_inv` at `C = (T - E T) diag √p`,
`X = diag √p Sᵀ`. -/
theorem posSemidef_weightedCov_sub_inv_secondMoment {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω)
    {T S : Matrix κ Ω ℝ}
    (h : ∀ i j, ∑ ω, p ω * (T i ω - weightedMean p T i) * S j ω = if i = j then 1 else 0) :
    (weightedCov p T - (secondMoment p S)⁻¹).PosSemidef := by
  have hCX : (Matrix.of fun i ω => (T i ω - weightedMean p T i) * √(p ω))
      * (Matrix.of fun j ω => S j ω * √(p ω))ᵀ = 1 :=
    (of_mul_sqrt_mul_transpose hp (fun i ω => T i ω - weightedMean p T i) S).trans
      (by ext i j; simp [h i j, Matrix.one_apply])
  have hXX : (Matrix.of fun i ω => S i ω * √(p ω)) * (Matrix.of fun j ω => S j ω * √(p ω))ᵀ
      = secondMoment p S := of_mul_sqrt_mul_transpose hp S S
  have hCC : (Matrix.of fun i ω => (T i ω - weightedMean p T i) * √(p ω))
      * (Matrix.of fun j ω => (T j ω - weightedMean p T j) * √(p ω))ᵀ = weightedCov p T :=
    of_mul_sqrt_mul_transpose hp (fun i ω => T i ω - weightedMean p T i)
      (fun i ω => T i ω - weightedMean p T i)
  have := posSemidef_self_mul_transpose_sub_inv hCX
  rwa [Matrix.transpose_transpose, hXX, hCC] at this

/-- **The equality case.** With every weight positive, the bound is attained exactly by the
efficient statistic: `T - E T = (E[S Sᵀ])⁻¹ S`. This is Gauss–Markov's
`self_mul_transpose_eq_inv_iff`; the positive weights let `√p` cancel. With a zero weight the
forward direction fails (see the module docstring). -/
theorem weightedCov_eq_inv_secondMoment_iff {p : Ω → ℝ} (hp : ∀ ω, 0 < p ω)
    {T S : Matrix κ Ω ℝ}
    (h : ∀ i j, ∑ ω, p ω * (T i ω - weightedMean p T i) * S j ω = if i = j then 1 else 0) :
    weightedCov p T = (secondMoment p S)⁻¹ ↔
      ∀ i ω, T i ω - weightedMean p T i = ((secondMoment p S)⁻¹ * S) i ω := by
  have hp0 : ∀ ω, 0 ≤ p ω := fun ω => (hp ω).le
  have hCX : (Matrix.of fun i ω => (T i ω - weightedMean p T i) * √(p ω))
      * (Matrix.of fun j ω => S j ω * √(p ω))ᵀ = 1 :=
    (of_mul_sqrt_mul_transpose hp0 (fun i ω => T i ω - weightedMean p T i) S).trans
      (by ext i j; simp [h i j, Matrix.one_apply])
  have hXX : (Matrix.of fun i ω => S i ω * √(p ω)) * (Matrix.of fun j ω => S j ω * √(p ω))ᵀ
      = secondMoment p S := of_mul_sqrt_mul_transpose hp0 S S
  have hCC : (Matrix.of fun i ω => (T i ω - weightedMean p T i) * √(p ω))
      * (Matrix.of fun j ω => (T j ω - weightedMean p T j) * √(p ω))ᵀ = weightedCov p T :=
    of_mul_sqrt_mul_transpose hp0 (fun i ω => T i ω - weightedMean p T i)
      (fun i ω => T i ω - weightedMean p T i)
  have key := self_mul_transpose_eq_inv_iff hCX
  rw [leastSquares, Matrix.transpose_transpose, hXX, hCC] at key
  rw [key]
  have hent : ∀ i ω, ((secondMoment p S)⁻¹ * Matrix.of fun j ω => S j ω * √(p ω)) i ω
      = ((secondMoment p S)⁻¹ * S) i ω * √(p ω) := by
    intro i ω
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul, mul_assoc]
  constructor
  · intro hC i ω
    have hiω := congrFun (congrFun hC i) ω
    rw [hent] at hiω
    exact mul_right_cancel₀ (Real.sqrt_ne_zero'.mpr (hp ω)) hiω
  · intro hT
    ext i ω
    rw [hent, Matrix.of_apply, hT i ω]

/-! ## The categorical family in the chart of `Simplex/Hessian` -/

/-- The scores of the categorical family `![lam, kap, eta]`, `eta = 1 - lam - kap`, in the
coordinates `(lam, kap)`: row `0` is `[ω = 0] / lam - [ω = 2] / eta`, the derivative of the log
weight in `lam`, and row `1` is `[ω = 1] / kap - [ω = 2] / eta`. -/
noncomputable def categoricalScore (lam kap : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![lam⁻¹, 0, -(1 - lam - kap)⁻¹; 0, kap⁻¹, -(1 - lam - kap)⁻¹]

/-- The one-hot statistic of a draw from three outcomes, first two coordinates: row `i` is
`[ω = i]`. -/
def categoricalOneHot : Matrix (Fin 2) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 0]

/-- The categorical weights sum to `1`. -/
example (lam kap : ℝ) : ∑ ω, ![lam, kap, 1 - lam - kap] ω = 1 := by
  simp [Fin.sum_univ_three]

/-- The scores have mean `0`. Needs every weight nonzero; it fails at every zero cell. -/
theorem weightedMean_categoricalScore {lam kap : ℝ} (hlam : lam ≠ 0) (hkap : kap ≠ 0)
    (heta : 1 - lam - kap ≠ 0) :
    weightedMean ![lam, kap, 1 - lam - kap] (categoricalScore lam kap) = 0 := by
  funext i
  fin_cases i <;> simp [weightedMean, categoricalScore, Fin.sum_univ_three] <;> field_simp <;> ring

/-- **The Fisher information of the categorical family is the Fisher–Rao metric in the chart.**
No hypothesis: `x * x⁻¹ * x⁻¹ = x⁻¹` also at `x = 0`. -/
theorem secondMoment_categoricalScore (lam kap : ℝ) :
    secondMoment ![lam, kap, 1 - lam - kap] (categoricalScore lam kap) =
      Simplex.fisherRaoChart lam kap := by
  have key : ∀ x : ℝ, x * x⁻¹ * x⁻¹ = x⁻¹ := fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · field_simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [secondMoment, categoricalScore, Simplex.fisherRaoChart, Fin.sum_univ_three, key]

/-- **The one-hot statistic is unbiased**: its mean is the parameter `![lam, kap]`. -/
theorem weightedMean_categoricalOneHot (lam kap : ℝ) :
    weightedMean ![lam, kap, 1 - lam - kap] categoricalOneHot = ![lam, kap] := by
  funext i
  fin_cases i <;> simp [weightedMean, categoricalOneHot, Fin.sum_univ_three]

/-- The covariance of the one-hot statistic is `Simplex.categoricalCov ![lam, kap]`. No
hypothesis. -/
theorem weightedCov_categoricalOneHot (lam kap : ℝ) :
    weightedCov ![lam, kap, 1 - lam - kap] categoricalOneHot =
      Simplex.categoricalCov ![lam, kap] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weightedCov, weightedMean, categoricalOneHot, Simplex.categoricalCov_apply,
      Fin.sum_univ_three] <;> ring

/-- The one-hot statistic satisfies the hypothesis of the information inequality: the cross
moment `∑ ω, p ω * (T i ω - E T i) * S j ω` with the scores is the identity, the derivative form
of unbiasedness. Needs every weight nonzero. -/
theorem crossMoment_categoricalOneHot_categoricalScore {lam kap : ℝ} (hlam : lam ≠ 0)
    (hkap : kap ≠ 0) (heta : 1 - lam - kap ≠ 0) (i j : Fin 2) :
    ∑ ω, ![lam, kap, 1 - lam - kap] ω *
        (categoricalOneHot i ω - weightedMean ![lam, kap, 1 - lam - kap] categoricalOneHot i) *
        categoricalScore lam kap j ω = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [weightedMean, categoricalOneHot, categoricalScore, Fin.sum_univ_three] <;>
    field_simp <;> ring

/-- **The one-hot statistic attains the bound**: its covariance is the inverse of the Fisher
information, by `Simplex.fisherRaoChart_mul_categoricalCov`. -/
theorem weightedCov_categoricalOneHot_eq_inv_secondMoment {lam kap : ℝ} (hlam : lam ≠ 0)
    (hkap : kap ≠ 0) (heta : 1 - lam - kap ≠ 0) :
    weightedCov ![lam, kap, 1 - lam - kap] categoricalOneHot =
      (secondMoment ![lam, kap, 1 - lam - kap] (categoricalScore lam kap))⁻¹ := by
  rw [secondMoment_categoricalScore, weightedCov_categoricalOneHot]
  exact (Matrix.inv_eq_right_inv (Simplex.fisherRaoChart_mul_categoricalCov hlam hkap heta)).symm

/-- The information inequality at the categorical family, its hypotheses discharged. -/
example {lam kap : ℝ} (hlam : 0 < lam) (hkap : 0 < kap) (heta : 0 < 1 - lam - kap) :
    (weightedCov ![lam, kap, 1 - lam - kap] categoricalOneHot -
      (secondMoment ![lam, kap, 1 - lam - kap] (categoricalScore lam kap))⁻¹).PosSemidef :=
  posSemidef_weightedCov_sub_inv_secondMoment (fun ω => by fin_cases ω <;> simp <;> linarith)
    (crossMoment_categoricalOneHot_categoricalScore hlam.ne' hkap.ne' heta.ne')

end ClassicalLean.Statistics
