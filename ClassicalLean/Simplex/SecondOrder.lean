/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Simplex.FisherRao
import Mathlib.Algebra.Order.Star.Real
import ClassicalLean.InformationTheory.Channel

/-!
# Second order on the simplex: the Fisher–Rao metric, the Hessian, and the covariance

Three parts of this library meet here, and none names another's declarations:
`Simplex/Hessian` computes the Hessian of a free energy in the chart `(lam, kap)` of the
2-simplex, with `eta = 1 - lam - kap`; `Simplex/FisherRao` defines the Fisher–Rao metric
`fisherRao p u v = ∑ i, u i * v i / p i`; and `Simplex/LogSumExp` with `Simplex/CrossEntropy`
has `softmax` and the first derivative of `logSumExp`. This file proves how they fit:

* **The Hessian is `T` times the Fisher–Rao metric, plus a barrier.** `fisherRaoChart lam kap`
  is the Fisher–Rao metric at `![lam, kap, eta]` on tangent vectors `![u₁, u₂, -u₁ - u₂]`, written
  in the chart (`fisherRao_eq_fisherRaoChart`), and
  `hessian T lam kap = T • fisherRaoChart lam kap + !![(lam ^ 2)⁻¹, 0; 0, 0]`
  (`hessian_eq_smul_fisherRaoChart_add`). Both are identities in the
  same inverses, so they hold with no hypothesis, even where a coordinate is `0` and `0⁻¹ = 0`.
  The metric is positive definite inside the simplex (`fisherRaoChart_posDef`), so
  `hessian_posDef` reads as a positive semidefinite barrier plus `T` times a positive definite
  metric; an `example` below proves it that way and does not restate it.
* **The softmax Jacobian is a covariance.** Moving the `k`-th logit, the derivative of
  `softmax x i` is `softmax x i * ([i = k] - softmax x k)` (`hasDerivAt_softmax`), which is the
  `(i, k)` entry of `categoricalCov (softmax x)`, the covariance matrix `diagonal p - p pᵀ` of a
  one-hot draw from `p` (`hasDerivAt_softmax_categoricalCov`). Since `hasDerivAt_logSumExp`
  says the first derivative of `logSumExp` is `softmax`, this is the reading of the covariance
  as the second derivative of `logSumExp`; the composite is not stated as one theorem here.
* **The covariance inverts the metric.** `categoricalCov p` is positive semidefinite
  (`categoricalCov_posSemidef`), kills the constant vector when `∑ p = 1`
  (`categoricalCov_mulVec_one`), and on tangent vectors inverts the Fisher–Rao metric:
  `categoricalCov p *ᵥ (u / p) = u` when `∑ u = 0` (`categoricalCov_mulVec_div`), and
  `fisherRao p (categoricalCov p *ᵥ w) v = w ⬝ᵥ v` (`fisherRao_categoricalCov_mulVec`), shown at
  `p = softmax x` by an `example`. In the chart,
  `fisherRaoChart lam kap * categoricalCov ![lam, kap] = 1`
  (`fisherRaoChart_mul_categoricalCov`), where `categoricalCov ![lam, kap]` is the matrix
  `!![lam - lam ^ 2, -(lam * kap); -(lam * kap), kap - kap ^ 2]` (`categoricalCov_fin_two`).
  Read with `hasDerivAt_logSumExp` (the composite is not stated here), the covariance at
  `softmax x` is the second derivative of `logSumExp`, the convex conjugate of the negative
  entropy by the Gibbs variational principle of `Simplex/LogSumExp`.

## Hypotheses, stated as weak as the proofs allow

Each is weaker than order G-6's text, which is recovered by an `example`:
`categoricalCov_posSemidef` needs `0 ≤ p` and `∑ p ≤ 1`, not `∑ p = 1` (so it covers the chart
matrix above, whose coordinates sum to `1 - eta`); `categoricalCov_mulVec_div` needs only that no
`p i` is `0`, not `p ∈ openSimplex`; `fisherRaoChart_mul_categoricalCov` needs `lam`, `kap` and
`eta` nonzero, not positive.

## Junk values, enumerated first

Measured with exact rational arithmetic before this file was written (order G-6 round 21):
the two chart identities hold at every point tried, including `lam = 0`, `kap = 0`, `eta = 0`
and negative coordinates, because both sides use the same inverses. A zero coordinate of `p`
breaks the tangent inverse unless `u` vanishes there (`p = [0, 1/2, 1/2]`, `u = [1, -1, 0]` gives
`[0, -1/2, 1/2]`), and so does `∑ u ≠ 0`. The chart inverse fails at every zero cell (at `lam = 0`
the product is `!![0, 1/3; 0, 1]` for `kap = 1/3`). Both hypotheses of the semidefiniteness are
needed: `∑ p = 3/2` gives the form `-3/4` at the constant vector, and `p = [-1/2, 3/2]` gives
`-3/4` at the first basis vector. The constant vector is killed only when `∑ p = 1`.

## Mathlib at v4.34.0

Searched before this file was written, from Mathlib's root, `grep -rniE '<pattern>' Mathlib
--include=*.lean`: `softmax` 0; `fisher.?rao|fisherRao|bhattacharyya` 1 (an author's name);
`fisher.?info|fisherInformation` 0; `vecMulVec` 141; `PosSemidef.*diagonal` 10;
`hasDerivAt.*exp.*div` 2 (both unrelated); `PosSemidef.*⁻¹` 3. By shape, Mathlib has the two-class
softmax: `Real.sigmoid` with `hasDerivAt_sigmoid`, `sigmoid x * (1 - sigmoid x)`, the `i = k`
entry above for two classes (`Analysis/SpecialFunctions/Sigmoid.lean`); `sigmoid` has 120 hits.
No Fisher–Rao metric, no covariance matrix of a categorical draw and no softmax Jacobian.
Mathlib's covariance is measure-theoretic (`ProbabilityTheory.covariance`, `covarianceBilin`;
`covarianceBilin` 153 hits, `ProbabilityTheory.covariance|def covariance` 5) and is not used for
this finite matrix.

## The squaring map (dated 2026-09-24, order G-7, J2 step 3; round 23)

The Fisher–Rao metric is spherical: the squaring map `x ↦ x²` pulls it back to four times the
Euclidean metric. With no hypothesis, at `x ↦ x²` and tangent vectors `2 x v`, `2 x w`, the metric
is `4` times the Euclidean product of `v` and `w` over the coordinates where `x` does not vanish
(`fisherRao_sq_two_mul`); for `x` with no zero coordinate that is `4 * (v ⬝ᵥ w)`
(`fisherRao_sq_two_mul_of_ne_zero`). `Geometry/S3Quaternion`'s `fisherRao_sqCoords` is the
instance at a quaternion's four coordinates. A zero coordinate is where the unrestricted identity
fails (`x = [0]`, `v = w = [1]` gives `0` against `4`): the squaring map's derivative vanishes
there, whatever value `0⁻¹` has. Searched first (round 23): `fisher` 0, and
`sphere.*simplex|simplex.*sphere` 31, all spheres in the Euclidean geometry of affine simplices
(circumsphere, insphere and exspheres, nine-point circle, `secondInter`).

## Contraction under a channel (dated 2026-09-24, order G-7, J2 step 4; round 23)

A fourth part now meets the three above: `InformationTheory/Channel`, which this file imports.
The Fisher–Rao metric contracts under every sub-stochastic matrix (`fisherRao_vecMul_le`):
garbling an observation cannot increase its Fisher information, the second-order companion of
`Channel`'s `relEntropy_vecMul_le`. Its hypotheses are weaker than the channel's own form, which an
`example` recovers: `0 ≤ p` with `p i = 0 → u i = 0` rather than `0 < p`, and row sums at most `1`
rather than equal to `1`; `W` may be rectangular, as in `Channel`. The proof is per column:
Cauchy–Schwarz (`Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul`, as `categoricalCov_posSemidef` uses
it) with weights `(u i ² / p i) W i j` and `p i W i j`, then a division whose two sign conditions
are `Channel`'s `vecMul_nonneg`, then the row sums. Finer forms also hold and are not stated:
row sums at most `1` are needed only where `u i ≠ 0`. Searched first (round 23): `fisher` 0; the
13 `data.?processing|chi.?squared|garbl` lines are Kullback–Leibler and Bayes-risk data processing
over measures and kernels, not a Fisher-information or finite-vector statement.
-/

open Finset
open scoped Matrix

namespace ClassicalLean.Simplex

/-- The Fisher–Rao metric of the 2-simplex in the chart `(lam, kap)`, with `eta = 1 - lam - kap`,
written with the same inverses as `hess11`, `hess12` and `hess22`. -/
noncomputable def fisherRaoChart (lam kap : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![lam⁻¹ + (1 - lam - kap)⁻¹, (1 - lam - kap)⁻¹;
    (1 - lam - kap)⁻¹, kap⁻¹ + (1 - lam - kap)⁻¹]

/-- **The Fisher–Rao metric in the chart.** At `![lam, kap, 1 - lam - kap]`, on the tangent
vectors `![u₁, u₂, -u₁ - u₂]` and `![v₁, v₂, -v₁ - v₂]`, the Fisher–Rao metric is the bilinear
form of `fisherRaoChart`. No hypothesis: both sides are the same expression in `lam⁻¹`, `kap⁻¹`
and `(1 - lam - kap)⁻¹`. -/
theorem fisherRao_eq_fisherRaoChart (lam kap u₁ u₂ v₁ v₂ : ℝ) :
    fisherRao ![lam, kap, 1 - lam - kap] ![u₁, u₂, -u₁ - u₂] ![v₁, v₂, -v₁ - v₂]
      = ![u₁, u₂] ⬝ᵥ (fisherRaoChart lam kap *ᵥ ![v₁, v₂]) := by
  simp only [fisherRao, fisherRaoChart, Fin.sum_univ_three, dotProduct, Matrix.mulVec,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one]
  ring

/-- **The Hessian is `T` times the Fisher–Rao metric, plus a barrier.** The free energy's
Hessian in the chart is `T • fisherRaoChart lam kap` plus the second derivative `(lam ^ 2)⁻¹`
of the barrier `-log lam` in its corner. No hypothesis. -/
theorem hessian_eq_smul_fisherRaoChart_add (T lam kap : ℝ) :
    hessian T lam kap = T • fisherRaoChart lam kap + !![(lam ^ 2)⁻¹, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hessian, fisherRaoChart, hess11, hess12, hess22]
  ring

/-- Inside the simplex the chart metric is positive definite: its quadratic form is the
Fisher–Rao metric of a tangent vector, which vanishes only at `0` (`fisherRao_self_eq_zero_iff`). -/
theorem fisherRaoChart_posDef {lam kap : ℝ} (hlam : 0 < lam) (hkap : 0 < kap)
    (heta : 0 < 1 - lam - kap) : (fisherRaoChart lam kap).PosDef := by
  have hp := (mem_openSimplex_chart hlam hkap heta).1
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [fisherRaoChart, Matrix.conjTranspose]
  · have hx' : ![x 0, x 1] = x := by
      funext i; fin_cases i <;> rfl
    have hquad : star x ⬝ᵥ (fisherRaoChart lam kap *ᵥ x)
        = fisherRao ![lam, kap, 1 - lam - kap] ![x 0, x 1, -x 0 - x 1]
            ![x 0, x 1, -x 0 - x 1] := by
      rw [fisherRao_eq_fisherRaoChart, hx', star_trivial]
    rw [hquad]
    refine lt_of_le_of_ne (fisherRao_self_nonneg hp _) (Ne.symm fun h => hx ?_)
    have h0 := congrFun ((fisherRao_self_eq_zero_iff hp _).mp h)
    funext i
    fin_cases i
    · simpa using h0 0
    · simpa using h0 1

/-- `hessian_posDef`, read through `hessian_eq_smul_fisherRaoChart_add`: a positive
semidefinite barrier plus `T` times the positive definite Fisher–Rao metric. -/
example {T lam kap : ℝ} (hT : 0 < T) (hlam : 0 < lam) (hkap : 0 < kap)
    (heta : 0 < 1 - lam - kap) : (hessian T lam kap).PosDef := by
  rw [hessian_eq_smul_fisherRaoChart_add, ← Matrix.diagonal_vec2]
  exact ((fisherRaoChart_posDef hlam hkap heta).smul hT).add_posSemidef
    (Matrix.posSemidef_diagonal_iff.mpr fun i => by fin_cases i <;> simp [sq_nonneg])

section Softmax

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The softmax Jacobian.** Moving the `k`-th logit, the derivative of `softmax · i` at the
point it started from is `softmax x i * ([i = k] - softmax x k)`. In the style of
`hasDerivAt_logSumExp`: one moving Boltzmann factor and a constant. -/
theorem hasDerivAt_softmax (x : ι → ℝ) (i k : ι) :
    HasDerivAt (fun t : ℝ => softmax (Function.update x k t) i)
      (softmax x i * ((if i = k then 1 else 0) - softmax x k)) (x k) := by
  set C := ∑ j ∈ Finset.univ.erase k, Real.exp (x j) with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => (Real.exp_pos (x j)).le
  have hpos : 0 < Real.exp (x k) + C := by
    have := Real.exp_pos (x k)
    linarith
  have hden : HasDerivAt (fun t : ℝ => Real.exp t + C) (Real.exp (x k)) (x k) :=
    (Real.hasDerivAt_exp (x k)).add_const C
  have hsum : ∑ j, Real.exp (x j) = Real.exp (x k) + C := sum_exp_eq_add_erase x k
  rcases eq_or_ne i k with rfl | hik
  · have hfun : (fun t : ℝ => softmax (Function.update x i t) i)
        = fun t : ℝ => Real.exp t / (Real.exp t + C) := by
      funext t
      rw [softmax, sum_exp_update, Function.update_self]
    rw [hfun]
    convert (Real.hasDerivAt_exp (x i)).fun_div hden hpos.ne' using 1
    simp only [↓reduceIte]
    rw [softmax, hsum]
    field_simp
  · have hfun : (fun t : ℝ => softmax (Function.update x k t) i)
        = fun t : ℝ => Real.exp (x i) / (Real.exp t + C) := by
      funext t
      rw [softmax, sum_exp_update, Function.update_of_ne hik]
    rw [hfun]
    convert (hasDerivAt_const (x k) (Real.exp (x i))).fun_div hden hpos.ne' using 1
    simp only [hik, ↓reduceIte]
    rw [softmax, softmax, hsum]
    field_simp
    ring

end Softmax

section Covariance

variable {ι : Type*} [DecidableEq ι]

/-- The covariance matrix of a one-hot draw from `p`: `diagonal p - p pᵀ`. When `p` is a
probability vector, entry `(i, j)` is `Cov(1[X = i], 1[X = j])` for `X` distributed by `p`. -/
def categoricalCov (p : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal p - Matrix.vecMulVec p p

/-- The entries of `categoricalCov`. -/
theorem categoricalCov_apply (p : ι → ℝ) (i j : ι) :
    categoricalCov p i j = (if i = j then p i else 0) - p i * p j := by
  simp [categoricalCov, Matrix.diagonal_apply, Matrix.vecMulVec_apply]

/-- On two coordinates `categoricalCov` is the explicit matrix
`!![lam - lam ^ 2, -(lam * kap); -(lam * kap), kap - kap ^ 2]`, which
`fisherRaoChart_mul_categoricalCov` inverts. -/
theorem categoricalCov_fin_two (lam kap : ℝ) :
    categoricalCov ![lam, kap] = !![lam - lam ^ 2, -(lam * kap); -(lam * kap), kap - kap ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [categoricalCov_apply] <;> ring

variable [Fintype ι]

/-- **The softmax Jacobian is the covariance of a one-hot draw from `softmax x`.** -/
theorem hasDerivAt_softmax_categoricalCov (x : ι → ℝ) (i k : ι) :
    HasDerivAt (fun t : ℝ => softmax (Function.update x k t) i)
      (categoricalCov (softmax x) i k) (x k) := by
  convert hasDerivAt_softmax x i k using 1
  rw [categoricalCov_apply]
  split_ifs with h
  · subst h; ring
  · ring

/-- **The covariance is positive semidefinite.** Its quadratic form is
`∑ p x² - (∑ p x)²`, a variance when `∑ p = 1`, and nonnegative whenever `0 ≤ p` and `∑ p ≤ 1`
by Cauchy–Schwarz. Both hypotheses are needed (see the module docstring). -/
theorem categoricalCov_posSemidef {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i ≤ 1) :
    (categoricalCov p).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [categoricalCov_apply, star_trivial]
    split_ifs with h h' h'
    · subst h; ring
    · exact absurd h.symm h'
    · exact absurd h'.symm h
    · ring
  · have hform : star x ⬝ᵥ (categoricalCov p *ᵥ x)
        = ∑ i, p i * x i ^ 2 - (∑ i, p i * x i) ^ 2 := by
      have h1 : star x ⬝ᵥ (Matrix.diagonal p *ᵥ x) = ∑ i, p i * x i ^ 2 := by
        simp only [star_trivial, dotProduct, Matrix.mulVec_diagonal]
        exact Finset.sum_congr rfl fun i _ => by ring
      have h2 : star x ⬝ᵥ (Matrix.vecMulVec p p *ᵥ x) = (∑ i, p i * x i) ^ 2 := by
        rw [sq, Finset.sum_mul_sum]
        simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply,
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [categoricalCov, Matrix.sub_mulVec, dotProduct_sub, h1, h2]
    rw [hform]
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (r := fun i => p i * x i) (f := p) (g := fun i => p i * x i ^ 2)
      (fun i _ => hp0 i) (fun i _ => mul_nonneg (hp0 i) (sq_nonneg _))
      (fun i _ => le_of_eq (by ring))
    have hg : 0 ≤ ∑ i, p i * x i ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hp0 i) (sq_nonneg _)
    nlinarith

/-- The constant vector is in the kernel of the covariance of a probability vector. -/
theorem categoricalCov_mulVec_one {p : ι → ℝ} (hp1 : ∑ i, p i = 1) :
    categoricalCov p *ᵥ (fun _ => 1) = 0 := by
  funext i
  simp [categoricalCov, Matrix.sub_mulVec, Matrix.mulVec_diagonal, Matrix.vecMulVec_mulVec,
    dotProduct, hp1]

/-- **The covariance inverts the Fisher–Rao metric on tangent vectors.** The metric
`fisherRao p u v = ∑ u i * v i / p i` sends a tangent vector `u` (`∑ u = 0`) to the covector
`u / p`, and `categoricalCov p` sends it back. Of `p`, only `p i ≠ 0` is used; `∑ u = 0` is
needed (see the module docstring). -/
theorem categoricalCov_mulVec_div {p u : ι → ℝ} (hp : ∀ i, p i ≠ 0) (hu : ∑ i, u i = 0) :
    categoricalCov p *ᵥ (fun i => u i / p i) = u := by
  have hs : p ⬝ᵥ (fun i => u i / p i) = 0 := by
    simp only [dotProduct]
    rw [← hu]
    exact Finset.sum_congr rfl fun i _ => by field_simp [hp i]
  funext i
  simp [categoricalCov, Matrix.sub_mulVec, Matrix.mulVec_diagonal, Matrix.vecMulVec_mulVec, hs]
  field_simp [hp i]

/-- On the closed simplex the covariance of a one-hot draw is positive semidefinite. -/
example {p : ι → ℝ} (hp : p ∈ closedSimplex ι) : (categoricalCov p).PosSemidef :=
  categoricalCov_posSemidef hp.1 hp.2.le

/-- On the open simplex the covariance sends the covector `u / p` of a tangent vector back to
`u`. -/
example {p u : ι → ℝ} (hp : p ∈ openSimplex ι) (hu : ∑ i, u i = 0) :
    categoricalCov p *ᵥ (fun i => u i / p i) = u :=
  categoricalCov_mulVec_div (fun i => (hp.1 i).ne') hu

/-- **The covariance is the inverse of the Fisher–Rao metric**, stated against `fisherRao`: for
a tangent vector `v`, the metric pairs `categoricalCov p *ᵥ w` with `v` as the plain dot product
of `w` with `v`. Only `p i ≠ 0` and `∑ v = 0` are used, and both are needed. -/
theorem fisherRao_categoricalCov_mulVec {p v : ι → ℝ} (hp : ∀ i, p i ≠ 0) (hv : ∑ i, v i = 0)
    (w : ι → ℝ) : fisherRao p (categoricalCov p *ᵥ w) v = w ⬝ᵥ v := by
  have hrow : ∀ i, (categoricalCov p *ᵥ w) i = p i * (w i - p ⬝ᵥ w) := by
    intro i
    simp [categoricalCov, Matrix.sub_mulVec, Matrix.mulVec_diagonal, Matrix.vecMulVec_mulVec]
    ring
  have hterm : ∀ i, p i * (w i - p ⬝ᵥ w) * v i / p i = w i * v i - (p ⬝ᵥ w) * v i := by
    intro i
    field_simp [hp i]
  simp only [fisherRao, hrow]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib, ← Finset.mul_sum, hv,
    mul_zero, sub_zero]
  rfl

/-- **At `softmax x`, `categoricalCov (softmax x)` inverts the Fisher–Rao metric on tangent
vectors.** Read with `hasDerivAt_softmax_categoricalCov` and `hasDerivAt_logSumExp` (the
composite is not stated here), this matrix is the second derivative of `logSumExp`. -/
example (x : ι → ℝ) {v : ι → ℝ} (hv : ∑ i, v i = 0) (w : ι → ℝ) :
    fisherRao (softmax x) (categoricalCov (softmax x) *ᵥ w) v = w ⬝ᵥ v :=
  fisherRao_categoricalCov_mulVec
    (fun i => by have : Nonempty ι := ⟨i⟩; exact (softmax_pos x i).ne') hv w

end Covariance

/-- **In the chart, the covariance is the inverse of the Fisher–Rao metric.** Needs `lam`, `kap`
and `1 - lam - kap` nonzero; it fails at every zero cell. -/
theorem fisherRaoChart_mul_categoricalCov {lam kap : ℝ} (hlam : lam ≠ 0) (hkap : kap ≠ 0)
    (heta : 1 - lam - kap ≠ 0) : fisherRaoChart lam kap * categoricalCov ![lam, kap] = 1 := by
  rw [categoricalCov_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fisherRaoChart, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- Inside the simplex, the chart metric times the matrix
`!![lam - lam ^ 2, -(lam * kap); -(lam * kap), kap - kap ^ 2]` is the identity. -/
example {lam kap : ℝ} (hlam : 0 < lam) (hkap : 0 < kap) (heta : 0 < 1 - lam - kap) :
    fisherRaoChart lam kap * !![lam - lam ^ 2, -(lam * kap); -(lam * kap), kap - kap ^ 2] = 1 := by
  rw [← categoricalCov_fin_two]
  exact fisherRaoChart_mul_categoricalCov hlam.ne' hkap.ne' heta.ne'

section SquaringMap

variable {ι : Type*} [Fintype ι]

/-- **The squaring map and the Fisher–Rao metric**, with no hypothesis: at `x ↦ x²`, with
tangent vectors `2 x v` and `2 x w`, the metric is four times the Euclidean product of `v` and
`w` over the coordinates where `x` does not vanish. -/
theorem fisherRao_sq_two_mul (x v w : ι → ℝ) :
    fisherRao (fun i => x i ^ 2) (fun i => 2 * x i * v i) (fun i => 2 * x i * w i)
      = 4 * ∑ i ∈ univ.filter (fun i => x i ≠ 0), v i * w i := by
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · field_simp
    ring
  · simp [not_not.mp h]

/-- **The squaring map pulls the Fisher–Rao metric back to four times the Euclidean one**, for `x`
with no zero coordinate. -/
theorem fisherRao_sq_two_mul_of_ne_zero {x : ι → ℝ} (hx : ∀ i, x i ≠ 0) (v w : ι → ℝ) :
    fisherRao (fun i => x i ^ 2) (fun i => 2 * x i * v i) (fun i => 2 * x i * w i)
      = 4 * (v ⬝ᵥ w) := by
  rw [fisherRao_sq_two_mul, Finset.filter_true_of_mem (fun i _ => hx i)]
  rfl

end SquaringMap

section Contraction

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **The Fisher–Rao metric contracts under every sub-stochastic matrix.** For `p` nonnegative
with `p i = 0 → u i = 0`, and `W` with nonnegative entries and row sums at most `1`,
`fisherRao (p ᵥ* W) (u ᵥ* W) (u ᵥ* W) ≤ fisherRao p u u`. Statistically: passing an observation
through a channel (garbling it) cannot increase its Fisher information. It is the second-order
companion of `relEntropy_vecMul_le`. Each hypothesis is needed: `p = (0, 1)`, `u = (3, 1)`,
`W = (1, 1)ᵀ` breaks the support condition (`16 > 1`); a row sum `5/4` gives `5/4 > 1`;
`p = (-1/2, 1)`, `u = (0, 1)` gives `2 > 1`; a negative entry with row sums `1` gives `18 > 2`. -/
theorem fisherRao_vecMul_le {p u : ι → ℝ} {W : Matrix ι κ ℝ} (hp : ∀ i, 0 ≤ p i)
    (hpu : ∀ i, p i = 0 → u i = 0) (hW0 : ∀ i j, 0 ≤ W i j) (hW1 : ∀ i, ∑ j, W i j ≤ 1) :
    fisherRao (p ᵥ* W) (u ᵥ* W) (u ᵥ* W) ≤ fisherRao p u u := by
  set q : ι → ℝ := fun i => u i * u i / p i with hq
  have hq0 : ∀ i, 0 ≤ q i := fun i => div_nonneg (mul_self_nonneg _) (hp i)
  -- Each column: Cauchy–Schwarz with weights `q i * W i j` and `p i * W i j`, then divide.
  have hcol : ∀ j, (u ᵥ* W) j * (u ᵥ* W) j / (p ᵥ* W) j ≤ (q ᵥ* W) j := by
    intro j
    have hcs : (∑ i, u i * W i j) ^ 2 ≤ (∑ i, q i * W i j) * ∑ i, p i * W i j :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul univ
        (fun i _ => mul_nonneg (hq0 i) (hW0 i j)) (fun i _ => mul_nonneg (hp i) (hW0 i j))
        fun i _ => by
          by_cases h : p i = 0
          · simp [hpu i h, h]
          · have hqp : q i * p i = u i * u i := div_mul_cancel₀ _ h
            refine le_of_eq ?_
            rw [show q i * W i j * (p i * W i j) = q i * p i * (W i j * W i j) by ring, hqp]
            ring
    refine div_le_of_le_mul₀ (vecMul_nonneg hW0 hp j) (vecMul_nonneg hW0 hq0 j) ?_
    simp only [Matrix.vecMul_apply_eq_sum]
    rw [sq] at hcs
    exact hcs
  calc fisherRao (p ᵥ* W) (u ᵥ* W) (u ᵥ* W)
      = ∑ j, (u ᵥ* W) j * (u ᵥ* W) j / (p ᵥ* W) j := rfl
    _ ≤ ∑ j, (q ᵥ* W) j := Finset.sum_le_sum fun j _ => hcol j
    _ = ∑ i, q i * ∑ j, W i j := by
        simp only [Matrix.vecMul_apply_eq_sum, Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ ∑ i, q i := Finset.sum_le_sum fun i _ => mul_le_of_le_one_right (hq0 i) (hW1 i)
    _ = fisherRao p u u := rfl

/-- `InformationTheory/Channel`'s form: a positive `p` and a stochastic `W`. -/
example {p u : ι → ℝ} {W : Matrix ι κ ℝ} (hp : ∀ i, 0 < p i) (hW0 : ∀ i j, 0 ≤ W i j)
    (hW1 : ∀ i, ∑ j, W i j = 1) :
    fisherRao (p ᵥ* W) (u ᵥ* W) (u ᵥ* W) ≤ fisherRao p u u :=
  fisherRao_vecMul_le (fun i => (hp i).le) (fun i h => absurd h (hp i).ne') hW0
    (fun i => (hW1 i).le)

end Contraction

end ClassicalLean.Simplex
