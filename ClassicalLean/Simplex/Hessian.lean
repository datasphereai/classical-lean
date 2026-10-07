/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Simplex.Gibbs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The Hessian of the free energy on the two-dimensional simplex

The two-dimensional open probability simplex is a surface in `ℝ³`, so to differentiate the free
energy of `ClassicalLean.Simplex.Gibbs` twice we work in the chart that eliminates the last
coordinate: a point is `(lam, kap, 1 - lam - kap)` with `lam`, `kap` and `1 - lam - kap` all
positive, and

    chartFreeEnergy T lam kap
      = -log lam + T * (lam * log lam + kap * log kap + (1-lam-kap) * log (1-lam-kap)).

`chartFreeEnergy_eq_freeEnergy` checks that this is the free energy of `Gibbs` composed with the
chart, and `mem_openSimplex_chart` that the chart lands in the open simplex.
`chartDerivFst_eq_symFreeEnergyDeriv` and `chartDerivSnd_of_eq` connect the two partial
derivatives to the one-variable restriction of `Gibbs` on the locus `kap = 1 - lam - kap`.

## Main results

* `deriv_deriv_chartFreeEnergy_fst`, `deriv_deriv_chartFreeEnergy_snd`,
  `deriv_deriv_chartFreeEnergy_mixed` — the three second partial derivatives are computed, not
  assumed: they equal `hess11`, `hess22` and `hess12`, namely
  `1/lam² + T·(1/lam + 1/eta)`, `T·(1/kap + 1/eta)` and `T/eta`, writing `eta = 1-lam-kap`.
  The two mixed partials are computed in both orders and shown to agree; that agreement is
  what justifies writing the matrix below with one off-diagonal entry in both places.
* `hess_det_pos`, `hess_trace_pos` — the determinant and trace of the resulting matrix are
  positive at every interior point, for every temperature `T > 0`.
* `hessian_quadraticForm_pos` — the associated quadratic form is positive on every nonzero
  vector, and `hessian_posDef` packages this as Mathlib's `Matrix.PosDef`.
* `hessian_charpoly` — the characteristic polynomial of that matrix really is
  `X² - tr·X + det`, via Mathlib's `Matrix.charpoly_fin_two`.
* `eigenvalue_pos` — every real root of the quadratic `x² - tr·x + det` in the three entries is
  strictly positive; `eigenvalue_pos_of_charpoly` states the same for the roots of
  `(hessian T lam kap).charpoly`, which `hessian_charpoly` identifies with that quadratic.

Everything is stated for a general temperature `T > 0` and a general interior point.

## Not ported from the source

The following source material has no counterpart in this library, for the reasons
given. None of the following has a
counterpart anywhere in this library.

* The rank-one Hessian and interior-versus-edge comparison (`lambda_min`, `HessianF`, and the
  four inequalities relating them): dropped. They compare a smallest eigenvalue against a
  numerical temperature, so they need the decimal-literal apparatus this port replaced by
  `Matrix.PosDef` at every interior point.
* The global strong-convexity modulus (`lam_m` and the modulus constant, with its interval
  membership, positivity, comparison with the temperature and universality): dropped. The
  modulus is a chosen decimal in the source; the statement it supports here is
  `hessian_posDef`, which is uniform in the point and needs no modulus.
* The three-dimensional Hessian and its eigenvalue positivity: dropped. The chart used here
  eliminates one coordinate of a *two*-dimensional simplex; the three-dimensional case would
  need a second chart and a `3 × 3` positive-definiteness argument, which is new work rather
  than a port.
* The third- and fourth-derivative family of the edge-curvature function (`g` and its
  derivatives): dropped here and recorded in `ClassicalLean.Simplex.Gibbs`, whose second
  derivative of `symFreeEnergy` is the highest one this library computes.
-/

open Real Set

namespace ClassicalLean.Simplex

variable {T lam kap : ℝ}

/-! ## The eliminated chart -/

/-- The free energy of `ClassicalLean.Simplex.freeEnergy` written in the chart that eliminates
the last coordinate of the two-dimensional simplex. -/
noncomputable def chartFreeEnergy (T lam kap : ℝ) : ℝ :=
  -Real.log lam + T * (lam * Real.log lam + kap * Real.log kap
    + (1 - lam - kap) * Real.log (1 - lam - kap))

/-- The chart really does compute the free energy of `Gibbs`. The proof is a definitional
unfolding of the two definitions plus a reassociation of the three-term sum — `simp only` with
no closing tactic — so this asserts no more than that the two expressions are the same one
written twice. It is stated because it is the only thing tying `chartFreeEnergy` to
`freeEnergy`. -/
theorem chartFreeEnergy_eq_freeEnergy (T lam kap : ℝ) :
    chartFreeEnergy T lam kap = freeEnergy T 0 ![lam, kap, 1 - lam - kap] := by
  simp only [chartFreeEnergy, freeEnergy, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- An interior point of the chart is a point of the open probability simplex on `Fin 3`. -/
theorem mem_openSimplex_chart (hlam : 0 < lam) (hkap : 0 < kap) (heta : 0 < 1 - lam - kap) :
    ![lam, kap, 1 - lam - kap] ∈ openSimplex (Fin 3) := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simp <;> linarith
  · simp [Fin.sum_univ_three]

/-! ## First partial derivatives -/

/-- Closed form of the partial derivative in the first chart coordinate. -/
noncomputable def chartDerivFst (T lam kap : ℝ) : ℝ :=
  -lam⁻¹ + T * (Real.log lam - Real.log (1 - lam - kap))

/-- Closed form of the partial derivative in the second chart coordinate. -/
noncomputable def chartDerivSnd (T lam kap : ℝ) : ℝ :=
  T * (Real.log kap - Real.log (1 - lam - kap))

/-- Auxiliary derivative: the eliminated coordinate as a function of the first chart
coordinate. -/
private theorem hasDerivAt_eta_fst (lam kap : ℝ) :
    HasDerivAt (fun l : ℝ => 1 - l - kap) (-1) lam := by
  simpa using ((hasDerivAt_id lam).const_sub 1).sub_const kap

/-- Auxiliary derivative: the eliminated coordinate as a function of the second chart
coordinate. -/
private theorem hasDerivAt_eta_snd (lam kap : ℝ) :
    HasDerivAt (fun k : ℝ => 1 - lam - k) (-1) kap := by
  exact (hasDerivAt_id' kap).const_sub (1 - lam)

/-- `∂/∂lam` of the free energy in the chart. -/
theorem hasDerivAt_chartFreeEnergy_fst (hlam : 0 < lam) (heta : 0 < 1 - lam - kap) :
    HasDerivAt (fun l => chartFreeEnergy T l kap) (chartDerivFst T lam kap) lam := by
  have t1 : HasDerivAt (fun l : ℝ => -Real.log l) (-lam⁻¹) lam :=
    (Real.hasDerivAt_log hlam.ne').neg
  have t2 : HasDerivAt (fun l : ℝ => l * Real.log l) (Real.log lam + 1) lam :=
    Real.hasDerivAt_mul_log hlam.ne'
  have t3 : HasDerivAt (fun _ : ℝ => kap * Real.log kap) 0 lam := hasDerivAt_const _ _
  have t4 : HasDerivAt (fun l : ℝ => (1 - l - kap) * Real.log (1 - l - kap))
      ((Real.log (1 - lam - kap) + 1) * (-1)) lam := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_mul_log heta.ne').comp lam (hasDerivAt_eta_fst lam kap)
  have hd := t1.add (((t2.add t3).add t4).const_mul T)
  refine hd.congr_deriv ?_
  rw [chartDerivFst]
  ring

/-- `∂/∂kap` of the free energy in the chart. -/
theorem hasDerivAt_chartFreeEnergy_snd (hkap : 0 < kap) (heta : 0 < 1 - lam - kap) :
    HasDerivAt (fun k => chartFreeEnergy T lam k) (chartDerivSnd T lam kap) kap := by
  have t1 : HasDerivAt (fun _ : ℝ => -Real.log lam) 0 kap := hasDerivAt_const _ _
  have t2 : HasDerivAt (fun _ : ℝ => lam * Real.log lam) 0 kap := hasDerivAt_const _ _
  have t3 : HasDerivAt (fun k : ℝ => k * Real.log k) (Real.log kap + 1) kap :=
    Real.hasDerivAt_mul_log hkap.ne'
  have t4 : HasDerivAt (fun k : ℝ => (1 - lam - k) * Real.log (1 - lam - k))
      ((Real.log (1 - lam - kap) + 1) * (-1)) kap := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_mul_log heta.ne').comp kap (hasDerivAt_eta_snd lam kap)
  have hd := t1.add (((t2.add t3).add t4).const_mul T)
  refine hd.congr_deriv ?_
  rw [chartDerivSnd]
  ring

/-- On the locus where the two remaining coordinates are equal, the partial derivative in the
first chart coordinate is the derivative of the one-variable restriction `symFreeEnergy 2 T`. -/
theorem chartDerivFst_eq_symFreeEnergyDeriv (hlam : 0 < lam) (h1 : lam < 1) :
    chartDerivFst T lam ((1 - lam) / 2) = symFreeEnergyDeriv 2 T lam := by
  have h1m : (0 : ℝ) < 1 - lam := by linarith
  rw [chartDerivFst, symFreeEnergyDeriv, show 1 - lam - (1 - lam) / 2 = (1 - lam) / 2 by ring,
    Real.log_div h1m.ne' (by norm_num), Real.log_div (by positivity) h1m.ne',
    Real.log_mul (by norm_num) hlam.ne']
  ring

/-- The partial derivative in the second chart coordinate vanishes on the locus where the two
remaining coordinates are equal, because there `kap = 1 - lam - kap`. -/
theorem chartDerivSnd_of_eq (T lam : ℝ) : chartDerivSnd T lam ((1 - lam) / 2) = 0 := by
  rw [chartDerivSnd, show 1 - lam - (1 - lam) / 2 = (1 - lam) / 2 by ring, sub_self, mul_zero]

/-! ## Second partial derivatives -/

/-- The `(1,1)` entry of the Hessian: `1/lam² + T·(1/lam + 1/eta)`. -/
noncomputable def hess11 (T lam kap : ℝ) : ℝ :=
  (lam ^ 2)⁻¹ + T * (lam⁻¹ + (1 - lam - kap)⁻¹)

/-- The `(2,2)` entry of the Hessian: `T·(1/kap + 1/eta)`. -/
noncomputable def hess22 (T lam kap : ℝ) : ℝ :=
  T * (kap⁻¹ + (1 - lam - kap)⁻¹)

/-- The off-diagonal entry of the Hessian: `T/eta`. -/
noncomputable def hess12 (T lam kap : ℝ) : ℝ :=
  T * (1 - lam - kap)⁻¹

/-- `∂/∂lam` of the first partial derivative. -/
theorem hasDerivAt_chartDerivFst_fst (hlam : 0 < lam) (heta : 0 < 1 - lam - kap) :
    HasDerivAt (fun l => chartDerivFst T l kap) (hess11 T lam kap) lam := by
  have t1 : HasDerivAt (fun l : ℝ => -l⁻¹) (-(-(lam ^ 2)⁻¹)) lam := (hasDerivAt_inv hlam.ne').neg
  have t2 : HasDerivAt Real.log lam⁻¹ lam := Real.hasDerivAt_log hlam.ne'
  have t3 : HasDerivAt (fun l : ℝ => Real.log (1 - l - kap)) ((1 - lam - kap)⁻¹ * (-1)) lam := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_log heta.ne').comp lam (hasDerivAt_eta_fst lam kap)
  have hd := t1.add ((t2.sub t3).const_mul T)
  refine hd.congr_deriv ?_
  rw [hess11]
  ring

/-- `∂/∂kap` of the second partial derivative. -/
theorem hasDerivAt_chartDerivSnd_snd (hkap : 0 < kap) (heta : 0 < 1 - lam - kap) :
    HasDerivAt (fun k => chartDerivSnd T lam k) (hess22 T lam kap) kap := by
  have t2 : HasDerivAt Real.log kap⁻¹ kap := Real.hasDerivAt_log hkap.ne'
  have t3 : HasDerivAt (fun k : ℝ => Real.log (1 - lam - k)) ((1 - lam - kap)⁻¹ * (-1)) kap := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_log heta.ne').comp kap (hasDerivAt_eta_snd lam kap)
  have hd := (t2.sub t3).const_mul T
  refine hd.congr_deriv ?_
  rw [hess22]
  ring

/-- `∂/∂lam` of the second partial derivative: the mixed second partial. -/
theorem hasDerivAt_chartDerivSnd_fst (heta : 0 < 1 - lam - kap) :
    HasDerivAt (fun l => chartDerivSnd T l kap) (hess12 T lam kap) lam := by
  have t2 : HasDerivAt (fun _ : ℝ => Real.log kap) 0 lam := hasDerivAt_const _ _
  have t3 : HasDerivAt (fun l : ℝ => Real.log (1 - l - kap)) ((1 - lam - kap)⁻¹ * (-1)) lam := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_log heta.ne').comp lam (hasDerivAt_eta_fst lam kap)
  have hd := (t2.sub t3).const_mul T
  refine hd.congr_deriv ?_
  rw [hess12]
  ring

/-- The second partial derivative in `lam` equals `hess11`. -/
theorem deriv_deriv_chartFreeEnergy_fst (hlam : 0 < lam) (heta : 0 < 1 - lam - kap) :
    deriv (deriv fun l => chartFreeEnergy T l kap) lam = hess11 T lam kap := by
  have hev : (deriv fun l => chartFreeEnergy T l kap) =ᶠ[nhds lam]
      fun l => chartDerivFst T l kap := by
    filter_upwards [Ioo_mem_nhds hlam (by linarith : lam < 1 - kap)] with y hy
    exact (hasDerivAt_chartFreeEnergy_fst hy.1 (by linarith [hy.2])).deriv
  rw [hev.deriv_eq]
  exact (hasDerivAt_chartDerivFst_fst hlam heta).deriv

/-- The second partial derivative in `kap` equals `hess22`. -/
theorem deriv_deriv_chartFreeEnergy_snd (hkap : 0 < kap) (heta : 0 < 1 - lam - kap) :
    deriv (deriv fun k => chartFreeEnergy T lam k) kap = hess22 T lam kap := by
  have hev : (deriv fun k => chartFreeEnergy T lam k) =ᶠ[nhds kap]
      fun k => chartDerivSnd T lam k := by
    filter_upwards [Ioo_mem_nhds hkap (by linarith : kap < 1 - lam)] with y hy
    exact (hasDerivAt_chartFreeEnergy_snd hy.1 (by linarith [hy.2])).deriv
  rw [hev.deriv_eq]
  exact (hasDerivAt_chartDerivSnd_snd hkap heta).deriv

/-- `∂/∂kap` of the first partial derivative: the other mixed second partial. -/
theorem hasDerivAt_chartDerivFst_snd (heta : 0 < 1 - lam - kap) :
    HasDerivAt (fun k => chartDerivFst T lam k) (hess12 T lam kap) kap := by
  have t1 : HasDerivAt (fun _ : ℝ => -lam⁻¹) 0 kap := hasDerivAt_const _ _
  have t2 : HasDerivAt (fun _ : ℝ => Real.log lam) 0 kap := hasDerivAt_const _ _
  have t3 : HasDerivAt (fun k : ℝ => Real.log (1 - lam - k)) ((1 - lam - kap)⁻¹ * (-1)) kap := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_log heta.ne').comp kap (hasDerivAt_eta_snd lam kap)
  have hd := t1.add ((t2.sub t3).const_mul T)
  refine hd.congr_deriv ?_
  rw [hess12]
  ring

/-- The mixed second partial derivative equals `hess12`. -/
theorem deriv_deriv_chartFreeEnergy_mixed (hkap : 0 < kap) (heta : 0 < 1 - lam - kap) :
    deriv (fun l => deriv (fun k => chartFreeEnergy T l k) kap) lam = hess12 T lam kap := by
  have hev : (fun l => deriv (fun k => chartFreeEnergy T l k) kap) =ᶠ[nhds lam]
      fun l => chartDerivSnd T l kap := by
    filter_upwards [Iio_mem_nhds (by linarith : lam < 1 - kap)] with y hy
    exact (hasDerivAt_chartFreeEnergy_snd hkap (by simp only [mem_Iio] at hy; linarith)).deriv
  rw [hev.deriv_eq]
  exact (hasDerivAt_chartDerivSnd_fst heta).deriv

/-- The mixed second partial derivative taken in the other order also equals `hess12`. The
matrix `hessian` below is *written* with `hess12` in both off-diagonal slots, so it is symmetric
by construction; what this theorem and `deriv_deriv_chartFreeEnergy_mixed` establish is that
writing it that way is correct, the two mixed partials being equal. -/
theorem deriv_deriv_chartFreeEnergy_mixed' (hlam : 0 < lam) (heta : 0 < 1 - lam - kap) :
    deriv (fun k => deriv (fun l => chartFreeEnergy T l k) lam) kap = hess12 T lam kap := by
  have hev : (fun k => deriv (fun l => chartFreeEnergy T l k) lam) =ᶠ[nhds kap]
      fun k => chartDerivFst T lam k := by
    filter_upwards [Iio_mem_nhds (by linarith : kap < 1 - lam)] with y hy
    exact (hasDerivAt_chartFreeEnergy_fst hlam (by simp only [mem_Iio] at hy; linarith)).deriv
  rw [hev.deriv_eq]
  exact (hasDerivAt_chartDerivFst_snd heta).deriv

/-! ## Positive-definiteness -/

theorem hess11_pos (hT : 0 < T) (hlam : 0 < lam) (heta : 0 < 1 - lam - kap) :
    0 < hess11 T lam kap := by
  have h1 : 0 < (lam ^ 2)⁻¹ := by positivity
  have h2 : 0 < lam⁻¹ + (1 - lam - kap)⁻¹ := by positivity
  have := mul_pos hT h2
  rw [hess11]; linarith

/-- The `(2,2)` entry is positive at every interior point. -/
theorem hess22_pos (hT : 0 < T) (hkap : 0 < kap) (heta : 0 < 1 - lam - kap) :
    0 < hess22 T lam kap := by
  have h2 : 0 < kap⁻¹ + (1 - lam - kap)⁻¹ := by positivity
  rw [hess22]; exact mul_pos hT h2

/-- The off-diagonal entry is positive at every interior point. -/
theorem hess12_pos (hT : 0 < T) (heta : 0 < 1 - lam - kap) : 0 < hess12 T lam kap := by
  rw [hess12]; exact mul_pos hT (inv_pos.mpr heta)

/-- The trace of the Hessian is positive at every interior point. -/
theorem hess_trace_pos (hT : 0 < T) (hlam : 0 < lam) (hkap : 0 < kap)
    (heta : 0 < 1 - lam - kap) : 0 < hess11 T lam kap + hess22 T lam kap :=
  add_pos (hess11_pos hT hlam heta) (hess22_pos hT hkap heta)

/-- The determinant of the Hessian is positive at every interior point. The proof rewrites
`H₁₁·H₂₂ - H₁₂²` in a form in which every term is manifestly positive. -/
theorem hess_det_pos (hT : 0 < T) (hlam : 0 < lam) (hkap : 0 < kap)
    (heta : 0 < 1 - lam - kap) :
    0 < hess11 T lam kap * hess22 T lam kap - hess12 T lam kap ^ 2 := by
  have ha : 0 < lam⁻¹ := inv_pos.mpr hlam
  have hk : 0 < kap⁻¹ := inv_pos.mpr hkap
  have he : 0 < (1 - lam - kap)⁻¹ := inv_pos.mpr heta
  have key : hess11 T lam kap * hess22 T lam kap - hess12 T lam kap ^ 2
      = T * lam⁻¹ ^ 2 * (kap⁻¹ + (1 - lam - kap)⁻¹)
        + T ^ 2 * (lam⁻¹ * kap⁻¹ + lam⁻¹ * (1 - lam - kap)⁻¹
          + (1 - lam - kap)⁻¹ * kap⁻¹) := by
    simp only [hess11, hess22, hess12, ← inv_pow]
    ring
  rw [key]
  have e1 : 0 < T * lam⁻¹ ^ 2 * (kap⁻¹ + (1 - lam - kap)⁻¹) :=
    mul_pos (mul_pos hT (pow_pos ha 2)) (add_pos hk he)
  have e2 : 0 < T ^ 2 * (lam⁻¹ * kap⁻¹ + lam⁻¹ * (1 - lam - kap)⁻¹
      + (1 - lam - kap)⁻¹ * kap⁻¹) :=
    mul_pos (pow_pos hT 2)
      (add_pos (add_pos (mul_pos ha hk) (mul_pos ha he)) (mul_pos he hk))
  linarith

/-- **Positive-definiteness, quadratic-form version.** At every interior point and every
temperature `T > 0` the quadratic form of the Hessian is strictly positive on nonzero
vectors. -/
theorem hessian_quadraticForm_pos (hT : 0 < T) (hlam : 0 < lam) (hkap : 0 < kap)
    (heta : 0 < 1 - lam - kap) {u v : ℝ} (huv : u ≠ 0 ∨ v ≠ 0) :
    0 < hess11 T lam kap * u ^ 2 + 2 * hess12 T lam kap * u * v
      + hess22 T lam kap * v ^ 2 := by
  have h11 := hess11_pos hT hlam heta
  have hdet := hess_det_pos hT hlam hkap heta
  rcases eq_or_ne v 0 with rfl | hv
  · have hu : u ≠ 0 := by simpa using huv
    have : 0 < u ^ 2 := by positivity
    nlinarith
  · have hv2 : 0 < v ^ 2 := by positivity
    have hsq : 0 ≤ (hess11 T lam kap * u + hess12 T lam kap * v) ^ 2 := sq_nonneg _
    nlinarith [mul_pos hdet hv2]

/-- The Hessian of the free energy in the eliminated chart. -/
noncomputable def hessian (T lam kap : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![hess11 T lam kap, hess12 T lam kap; hess12 T lam kap, hess22 T lam kap]

/-- **Positive-definiteness.** At every interior point and every temperature `T > 0` the
Hessian is positive definite in Mathlib's sense. Context, not proved here: the classical
second-derivative test turns this into a strict local minimum at a critical point. -/
theorem hessian_posDef (hT : 0 < T) (hlam : 0 < lam) (hkap : 0 < kap)
    (heta : 0 < 1 - lam - kap) : (hessian T lam kap).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hessian, Matrix.conjTranspose]
  · have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hx (funext fun i => by fin_cases i <;> simp [hcon.1, hcon.2])
    have hquad : star x ⬝ᵥ (hessian T lam kap).mulVec x
        = hess11 T lam kap * x 0 ^ 2 + 2 * hess12 T lam kap * x 0 * x 1
          + hess22 T lam kap * x 1 ^ 2 := by
      simp [hessian, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    rw [hquad]
    exact hessian_quadraticForm_pos hT hlam hkap heta (u := x 0) (v := x 1) hx'

/-- Every real root of the quadratic `x² - tr·x + det` formed from the three Hessian entries is
strictly positive: if `μ ≤ 0` then `μ² ≥ 0`, `-tr·μ ≥ 0` and `det > 0`, so the quadratic cannot
vanish at `μ`. That this quadratic is the characteristic polynomial of `hessian` is
`hessian_charpoly`; the two are combined in `eigenvalue_pos_of_charpoly`. -/
theorem eigenvalue_pos (hT : 0 < T) (hlam : 0 < lam) (hkap : 0 < kap)
    (heta : 0 < 1 - lam - kap) {μ : ℝ}
    (h : μ ^ 2 - (hess11 T lam kap + hess22 T lam kap) * μ
      + (hess11 T lam kap * hess22 T lam kap - hess12 T lam kap ^ 2) = 0) : 0 < μ := by
  by_contra hμ
  push Not at hμ
  have htr := hess_trace_pos hT hlam hkap heta
  have hdet := hess_det_pos hT hlam hkap heta
  nlinarith [sq_nonneg μ, mul_nonneg htr.le (neg_nonneg.mpr hμ)]

/-- The characteristic polynomial of the Hessian is `X² - tr·X + det`. This is Mathlib's
`Matrix.charpoly_fin_two` together with the trace and determinant of a `2 × 2` matrix; it is
what connects `eigenvalue_pos` to the word "eigenvalue". -/
theorem hessian_charpoly (T lam kap : ℝ) :
    (hessian T lam kap).charpoly
      = Polynomial.X ^ 2
        - Polynomial.C (hess11 T lam kap + hess22 T lam kap) * Polynomial.X
        + Polynomial.C (hess11 T lam kap * hess22 T lam kap - hess12 T lam kap ^ 2) := by
  rw [Matrix.charpoly_fin_two, hessian, Matrix.trace_fin_two_of, Matrix.det_fin_two_of, ← sq]

/-- **Every real root of the characteristic polynomial of the Hessian is strictly positive**, at
every interior point and every temperature `T > 0`. `hessian_charpoly` identifies that
polynomial with the quadratic of `eigenvalue_pos`. -/
theorem eigenvalue_pos_of_charpoly (hT : 0 < T) (hlam : 0 < lam) (hkap : 0 < kap)
    (heta : 0 < 1 - lam - kap) {μ : ℝ}
    (h : (hessian T lam kap).charpoly.eval μ = 0) : 0 < μ := by
  refine eigenvalue_pos hT hlam hkap heta ?_
  rw [hessian_charpoly] at h
  simpa using h

end ClassicalLean.Simplex
