/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Simplex.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Fin

/-!
# Free energy on the probability simplex: convexity, Gibbs' inequality, equilibrium

Fix a finite index set `ι`, a temperature `T > 0` and a distinguished index `i₀`. On the
**open probability simplex**

    Δ = { x : ι → ℝ | (∀ i, 0 < x i) ∧ ∑ i, x i = 1 }

— the set `openSimplex ι`, defined with its convexity in `ClassicalLean.Simplex.Basic` — this
file studies the free energy

    F(x) = -log (x i₀) + T * ∑ i, x i * log (x i),

a logarithmic barrier in one coordinate plus `T` times the negative entropy. The barrier is
what distinguishes `i₀`; without it `F` would be `T` times the negative entropy alone.

## Main results

Convexity and Gibbs' inequality, for a general finite index set:

* `sum_mul_log_div_nonneg` — **Gibbs' inequality**: for strictly positive probability vectors
  `p` and `q` the relative entropy `∑ i, p i * log (p i / q i)` is nonnegative;
  `sum_mul_log_div_pos_of_ne` sharpens this to a strict inequality when `p ≠ q`.
* `neg_log_card_le_sum_mul_log` — the entropy of a strictly positive probability vector is at
  most `log |ι|`; this is Gibbs' inequality against the uniform vector.
* `strictConvexOn_negEntropy`, `strictConvexOn_freeEnergy` — the negative entropy, and hence
  `F` for every `T > 0`, is strictly convex on `Δ`.

The one-variable restriction to the locus where all coordinates but `i₀` are equal — `m` of
them, each equal to `(1 - lam)/m`, with `lam` the distinguished coordinate:

* `symFreeEnergy_eq_freeEnergy_two`, `symFreeEnergy_eq_freeEnergy_three` — the restriction
  `symFreeEnergy m T` really is `freeEnergy` evaluated on that locus, for `m = 2` and `m = 3`.
* `hasDerivAt_symFreeEnergy`, `deriv_deriv_symFreeEnergy` — its first derivative
  `-1/lam + T·log (m·lam/(1-lam))` and its second derivative `1/lam² + T·(1/lam + 1/(1-lam))`,
  both proved as derivatives rather than assumed.
* `strictConvexOn_symFreeEnergy` — it is strictly convex on `(0,1)` for every `T > 0`.
* `deriv_symFreeEnergy_eq_zero_iff` — the **critical-point equation**
  `1/lam = T · log (m·lam/(1-lam))`.
* `gibbsWeight_eq_iff`, `deriv_symFreeEnergy_eq_zero_iff_gibbsWeight` — the critical-point
  equation says exactly that `lam` is its own Gibbs (softmax) weight against `m` degenerate
  states at energy gap `1/lam`.
* `existsUnique_temperature` — for every target `lam` strictly between the uniform point
  `1/(m+1)` and `1` there is exactly one temperature making `lam` critical, given in closed
  form by `criticalTemperature`, and it is positive.
* `isMinOn_symFreeEnergy`, `symFreeEnergy_minimiser_unique` — a critical point is the unique
  global minimiser on `(0,1)`.
* `symRatio_uniform`, `symFreeEnergyDeriv_uniform`, `symFreeEnergyDeriv_uniform_ne_zero` — at
  the uniform point `1/(m+1)` the ratio inside the logarithm is `1`, so the derivative is
  `-(m+1)` whatever the temperature and no temperature is critical there. That is why the
  hypotheses above exclude the uniform point.

Every statement is for a general `T > 0`, and every statement about `symFreeEnergy` is for a
general count `m > 0` of equal coordinates with exactly two exceptions:
`symFreeEnergy_eq_freeEnergy_two` and `symFreeEnergy_eq_freeEnergy_three` fix `m = 2` and
`m = 3`, because identifying the restriction with `freeEnergy` means writing out the
coordinates of a specific `Fin (m+1)`. No particular numerical temperature or threshold occurs
anywhere in this file; those are chosen in `ClassicalLean.Simplex.DesignConstants`.

The relabelling-group count `Fintype.card (Equiv.Perm (Fin 3)) = 6` below is deliberately an
`example` and not a theorem: it is one `rw` from Mathlib's `Fintype.card_perm`, so naming it
would add a library-level name for a Mathlib fact.

## Not ported from the source

The following source material has no counterpart in this library, for the reasons
given.

* The source's edge-curvature function `g` and its whole derivative family — positivity of `g`,
  its first and second derivatives (the third and fourth derivatives of the free energy), its
  strict convexity, and the quadratic form of `g' = 0`: dropped. `g` is half the second
  derivative of the free energy along a wall the source places at the boundary face where one
  coordinate is `0`, which is not a point of the open simplex; the wall used here is the
  symmetric one, and the positivity that the convexity argument needs is what
  `strictConvexOn_symFreeEnergy` proves. Nothing in this library differentiates
  `symFreeEnergy` more than twice, so the third- and fourth-derivative statements have no
  counterpart and none is claimed.
* The source's four headline identities at the chosen point — the critical-point equation and
  the closed form of the reciprocal threshold, on two and on three equal coordinates: not
  shipped as statements. Each is one rewrite from
  `deriv_symFreeEnergy_eq_zero_iff` together with the constants of
  `ClassicalLean.Simplex.DesignConstants`, and "one rewrite away" is not shipped; they are
  listed here rather than counted as delivered.
-/

open Real Set

namespace ClassicalLean.Simplex

/-! ## Symmetry of the entropy term

The simplex `openSimplex ι` itself, its unfolding lemma and its convexity are in
`ClassicalLean.Simplex.Basic`; this file only uses them. -/

section Simplex

variable {ι : Type*} [Fintype ι]

/-- Relabelling the index set leaves `∑ i, x i * log (x i)` unchanged: the entropy term of the
free energy is a symmetric function of the coordinates. -/
theorem sum_mul_log_comp_equiv (e : ι ≃ ι) (x : ι → ℝ) :
    ∑ i, x (e i) * Real.log (x (e i)) = ∑ i, x i * Real.log (x i) :=
  Equiv.sum_comp e fun j => x j * Real.log (x j)

/-- The relabelling group of a three-point index set has six elements. -/
example : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Fintype.card_perm, Fintype.card_fin]; decide

/-! ## Gibbs' inequality -/

/-- **Gibbs' inequality.** For strictly positive probability vectors `p` and `q` on a finite
index set the relative entropy `∑ i, p i * log (p i / q i)` is nonnegative.

The proof is the usual one: `log t ≤ t - 1` (`Real.log_le_sub_one_of_pos`) applied to
`t = q i / p i` and summed. -/
theorem sum_mul_log_div_nonneg {p q : ι → ℝ} (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    0 ≤ ∑ i, p i * Real.log (p i / q i) := by
  have hswap : ∀ i, p i * Real.log (q i / p i) = -(p i * Real.log (p i / q i)) := by
    intro i
    rw [Real.log_div (hq i).ne' (hp i).ne', Real.log_div (hp i).ne' (hq i).ne']
    ring
  have key : ∀ i ∈ Finset.univ, p i * Real.log (q i / p i) ≤ q i - p i := by
    intro i _
    have h := Real.log_le_sub_one_of_pos (div_pos (hq i) (hp i))
    have h2 := mul_le_mul_of_nonneg_left h (hp i).le
    calc p i * Real.log (q i / p i) ≤ p i * (q i / p i - 1) := h2
      _ = q i - p i := by field_simp [(hp i).ne']
  have hle : ∑ i, p i * Real.log (q i / p i) ≤ 0 := by
    calc ∑ i, p i * Real.log (q i / p i) ≤ ∑ i, (q i - p i) := Finset.sum_le_sum key
      _ = 0 := by rw [Finset.sum_sub_distrib, hp1, hq1]; ring
  rw [Finset.sum_congr rfl fun i _ => hswap i, Finset.sum_neg_distrib] at hle
  linarith

/-- **Gibbs' inequality, strict form.** Two distinct strictly positive probability vectors have
strictly positive relative entropy. The proof replaces `log t ≤ t - 1` by
`Real.log_lt_sub_one_of_pos` at an index where `p` and `q` differ. -/
theorem sum_mul_log_div_pos_of_ne {p q : ι → ℝ} (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) (hne : p ≠ q) :
    0 < ∑ i, p i * Real.log (p i / q i) := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hne
  have hswap : ∀ i, p i * Real.log (q i / p i) = -(p i * Real.log (p i / q i)) := by
    intro i
    rw [Real.log_div (hq i).ne' (hp i).ne', Real.log_div (hp i).ne' (hq i).ne']
    ring
  have key : ∀ i ∈ Finset.univ, p i * Real.log (q i / p i) ≤ q i - p i := by
    intro i _
    have h := Real.log_le_sub_one_of_pos (div_pos (hq i) (hp i))
    have h2 := mul_le_mul_of_nonneg_left h (hp i).le
    calc p i * Real.log (q i / p i) ≤ p i * (q i / p i - 1) := h2
      _ = q i - p i := by field_simp [(hp i).ne']
  have hstrict : p i₀ * Real.log (q i₀ / p i₀) < q i₀ - p i₀ := by
    have hne1 : q i₀ / p i₀ ≠ 1 := by
      rw [Ne, div_eq_one_iff_eq (hp i₀).ne']
      exact fun h => hi₀ h.symm
    have h := Real.log_lt_sub_one_of_pos (div_pos (hq i₀) (hp i₀)) hne1
    have h2 := (mul_lt_mul_of_pos_left h (hp i₀))
    calc p i₀ * Real.log (q i₀ / p i₀) < p i₀ * (q i₀ / p i₀ - 1) := h2
      _ = q i₀ - p i₀ := by field_simp [(hp i₀).ne']
  have hlt : ∑ i, p i * Real.log (q i / p i) < 0 := by
    calc ∑ i, p i * Real.log (q i / p i)
        < ∑ i, (q i - p i) := Finset.sum_lt_sum key ⟨i₀, Finset.mem_univ _, hstrict⟩
      _ = 0 := by rw [Finset.sum_sub_distrib, hp1, hq1]; ring
  rw [Finset.sum_congr rfl fun i _ => hswap i, Finset.sum_neg_distrib] at hlt
  linarith

/-- The entropy of a strictly positive probability vector is at most `log |ι|`, equivalently
`-log |ι| ≤ ∑ i, x i * log (x i)`. This is Gibbs' inequality against the uniform vector. -/
theorem neg_log_card_le_sum_mul_log [Nonempty ι] {x : ι → ℝ} (hx : x ∈ openSimplex ι) :
    -Real.log (Fintype.card ι) ≤ ∑ i, x i * Real.log (x i) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hq0 : ∀ i : ι, 0 < ((Fintype.card ι : ℝ))⁻¹ := fun _ => inv_pos.mpr hn
  have hq1 : ∑ _i : ι, ((Fintype.card ι : ℝ))⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have h := sum_mul_log_div_nonneg hx0 hq0 hx1 hq1
  have hterm : ∀ i, x i * Real.log (x i / ((Fintype.card ι : ℝ))⁻¹)
      = x i * Real.log (x i) + x i * Real.log (Fintype.card ι) := by
    intro i
    rw [Real.log_div (hx0 i).ne' (inv_pos.mpr hn).ne', Real.log_inv]
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, ← Finset.sum_mul,
    hx1, one_mul] at h
  linarith

/-! ## Strict convexity -/

/-- The negative entropy `x ↦ ∑ i, x i * log (x i)` is strictly convex on the open probability
simplex. Each summand is strictly convex by Mathlib's `Real.strictConvexOn_mul_log`; two
distinct points of the simplex differ in some coordinate, which makes one summand strict. -/
theorem strictConvexOn_negEntropy :
    StrictConvexOn ℝ (openSimplex ι) fun x => ∑ i, x i * Real.log (x i) := by
  refine ⟨convex_openSimplex, ?_⟩
  rintro x ⟨hx0, -⟩ y ⟨hy0, -⟩ hxy a b ha hb hab
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hxy
  have hle : ∀ i ∈ Finset.univ,
      (a * x i + b * y i) * Real.log (a * x i + b * y i)
        ≤ a * (x i * Real.log (x i)) + b * (y i * Real.log (y i)) := by
    intro i _
    exact Real.convexOn_mul_log.2 (hx0 i).le (hy0 i).le ha.le hb.le hab
  have hlt : (a * x i₀ + b * y i₀) * Real.log (a * x i₀ + b * y i₀)
      < a * (x i₀ * Real.log (x i₀)) + b * (y i₀ * Real.log (y i₀)) :=
    Real.strictConvexOn_mul_log.2 (hx0 i₀).le (hy0 i₀).le hi₀ ha hb hab
  have := Finset.sum_lt_sum hle ⟨i₀, Finset.mem_univ _, hlt⟩
  simpa [Finset.sum_add_distrib, Finset.mul_sum] using this

/-- The free energy on the open probability simplex: a logarithmic barrier in the coordinate
`i₀` plus `T` times the negative entropy. -/
noncomputable def freeEnergy (T : ℝ) (i₀ : ι) (x : ι → ℝ) : ℝ :=
  -Real.log (x i₀) + T * ∑ i, x i * Real.log (x i)

/-- The barrier term `x ↦ -log (x i₀)` is convex on the open probability simplex, derived from
Mathlib's `strictConcaveOn_log_Ioi`. Convexity is all that is claimed and all that is proved.
Context, not proved here: it is not *strictly* convex, because it ignores every coordinate
other than `i₀`; no declaration in this file asserts that. -/
theorem convexOn_barrier (i₀ : ι) :
    ConvexOn ℝ (openSimplex ι) fun x => -Real.log (x i₀) := by
  refine ⟨convex_openSimplex, ?_⟩
  rintro x ⟨hx0, -⟩ y ⟨hy0, -⟩ a b ha hb hab
  have h := strictConcaveOn_log_Ioi.concaveOn.2 (mem_Ioi.mpr (hx0 i₀))
    (mem_Ioi.mpr (hy0 i₀)) ha hb hab
  simp only [smul_eq_mul, Pi.add_apply, Pi.smul_apply] at h ⊢
  linarith

/-- For every temperature `T > 0` the free energy is strictly convex on the open probability
simplex: a convex barrier plus a strictly convex multiple of the negative entropy. -/
theorem strictConvexOn_freeEnergy {T : ℝ} (hT : 0 < T) (i₀ : ι) :
    StrictConvexOn ℝ (openSimplex ι) (freeEnergy T i₀) := by
  refine ⟨convex_openSimplex, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hbar := (convexOn_barrier (ι := ι) i₀).2 hx hy ha.le hb.le hab
  have hent := (strictConvexOn_negEntropy (ι := ι)).2 hx hy hxy ha hb hab
  have hent' := mul_lt_mul_of_pos_left hent hT
  simp only [freeEnergy, smul_eq_mul, Pi.add_apply, Pi.smul_apply] at hbar hent' ⊢
  linarith

end Simplex

/-! ## The symmetric wall -/

section Wall

/-- The free energy restricted to the points of the simplex at which every coordinate other
than the distinguished one is equal to every other. Writing `m` for the number of those equal
coordinates and `lam` for the distinguished one, they each equal `(1 - lam) / m`, and the free
energy becomes the one-variable function

    symFreeEnergy m T lam = -log lam + T * (lam * log lam + (1 - lam) * log ((1 - lam) / m)).

`symFreeEnergy_eq_freeEnergy_two` and `symFreeEnergy_eq_freeEnergy_three` check this against
`freeEnergy` for `m = 2` and `m = 3`. -/
noncomputable def symFreeEnergy (m T lam : ℝ) : ℝ :=
  -Real.log lam + T * (lam * Real.log lam + (1 - lam) * Real.log ((1 - lam) / m))

/-- The closed form of the derivative of `symFreeEnergy m T`; that it really is the derivative
is `hasDerivAt_symFreeEnergy`. -/
noncomputable def symFreeEnergyDeriv (m T lam : ℝ) : ℝ :=
  -lam⁻¹ + T * Real.log (m * lam / (1 - lam))

variable {m T lam : ℝ}

/-- With two equal coordinates, `symFreeEnergy` is the free energy on the two-dimensional
simplex evaluated at `(lam, (1 - lam)/2, (1 - lam)/2)`. -/
theorem symFreeEnergy_eq_freeEnergy_two (T lam : ℝ) :
    symFreeEnergy 2 T lam = freeEnergy T 0 ![lam, (1 - lam) / 2, (1 - lam) / 2] := by
  simp only [symFreeEnergy, freeEnergy, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- With three equal coordinates, `symFreeEnergy` is the free energy on the three-dimensional
simplex evaluated at `(lam, (1 - lam)/3, (1 - lam)/3, (1 - lam)/3)`. -/
theorem symFreeEnergy_eq_freeEnergy_three (T lam : ℝ) :
    symFreeEnergy 3 T lam
      = freeEnergy T 0 ![lam, (1 - lam) / 3, (1 - lam) / 3, (1 - lam) / 3] := by
  simp only [symFreeEnergy, freeEnergy, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons]
  ring

/-- The derivative of the restricted free energy at an interior point:
`d/dlam symFreeEnergy m T lam = -1/lam + T * log (m·lam/(1-lam))`. -/
theorem hasDerivAt_symFreeEnergy (hm : 0 < m) (h0 : 0 < lam) (h1 : lam < 1) :
    HasDerivAt (symFreeEnergy m T) (symFreeEnergyDeriv m T lam) lam := by
  have h1m : (0 : ℝ) < 1 - lam := by linarith
  have hev : symFreeEnergy m T =ᶠ[nhds lam] fun x =>
      -Real.log x + T * (x * Real.log x +
        ((1 - x) * Real.log (1 - x) - (1 - x) * Real.log m)) := by
    filter_upwards [Ioo_mem_nhds h0 h1] with y hy
    have hy1 : (0 : ℝ) < 1 - y := by linarith [hy.2]
    simp only [symFreeEnergy]
    rw [Real.log_div hy1.ne' hm.ne']
    ring
  have hsub : HasDerivAt (fun x : ℝ => 1 - x) (-1) lam := by
    simpa using (hasDerivAt_id lam).const_sub 1
  have t1 : HasDerivAt (fun x : ℝ => -Real.log x) (-lam⁻¹) lam :=
    (Real.hasDerivAt_log h0.ne').neg
  have t2 : HasDerivAt (fun x : ℝ => x * Real.log x) (Real.log lam + 1) lam :=
    Real.hasDerivAt_mul_log h0.ne'
  have t3 : HasDerivAt (fun x : ℝ => (1 - x) * Real.log (1 - x))
      ((Real.log (1 - lam) + 1) * (-1)) lam := by
    simpa [Function.comp_def] using (Real.hasDerivAt_mul_log h1m.ne').comp lam hsub
  have t4 : HasDerivAt (fun x : ℝ => (1 - x) * Real.log m) (-1 * Real.log m) lam :=
    hsub.mul_const _
  have hd := t1.add (((t2.add (t3.sub t4)).const_mul T))
  refine HasDerivAt.congr_of_eventuallyEq (hd.congr_deriv ?_) hev
  rw [symFreeEnergyDeriv, Real.log_div (by positivity) h1m.ne', Real.log_mul hm.ne' h0.ne']
  ring

/-- `deriv` form of `hasDerivAt_symFreeEnergy`. -/
theorem deriv_symFreeEnergy (hm : 0 < m) (h0 : 0 < lam) (h1 : lam < 1) :
    deriv (symFreeEnergy m T) lam = symFreeEnergyDeriv m T lam :=
  (hasDerivAt_symFreeEnergy hm h0 h1).deriv

/-- The derivative of the closed-form first derivative, i.e. the second derivative of the
restricted free energy: `1/lam² + T * (1/lam + 1/(1-lam))`. -/
theorem hasDerivAt_symFreeEnergyDeriv (hm : 0 < m) (h0 : 0 < lam) (h1 : lam < 1) :
    HasDerivAt (symFreeEnergyDeriv m T)
      ((lam ^ 2)⁻¹ + T * (lam⁻¹ + (1 - lam)⁻¹)) lam := by
  have h1m : (0 : ℝ) < 1 - lam := by linarith
  have hev : symFreeEnergyDeriv m T =ᶠ[nhds lam] fun x =>
      -x⁻¹ + T * (Real.log m + Real.log x - Real.log (1 - x)) := by
    filter_upwards [Ioo_mem_nhds h0 h1] with y hy
    have hy0 : (0 : ℝ) < y := hy.1
    have hy1 : (0 : ℝ) < 1 - y := by linarith [hy.2]
    simp only [symFreeEnergyDeriv]
    rw [Real.log_div (by positivity) hy1.ne', Real.log_mul hm.ne' hy0.ne']
  have hsub : HasDerivAt (fun x : ℝ => 1 - x) (-1) lam := by
    simpa using (hasDerivAt_id lam).const_sub 1
  have t1 : HasDerivAt (fun x : ℝ => -x⁻¹) (-(-(lam ^ 2)⁻¹)) lam := (hasDerivAt_inv h0.ne').neg
  have t2 : HasDerivAt (fun _ : ℝ => Real.log m) 0 lam := hasDerivAt_const _ _
  have t3 : HasDerivAt Real.log lam⁻¹ lam := Real.hasDerivAt_log h0.ne'
  have t4 : HasDerivAt (fun x : ℝ => Real.log (1 - x)) ((1 - lam)⁻¹ * (-1)) lam := by
    simpa [Function.comp_def] using (Real.hasDerivAt_log h1m.ne').comp lam hsub
  have hd := t1.add (((t2.add t3).sub t4).const_mul T)
  refine HasDerivAt.congr_of_eventuallyEq (hd.congr_deriv ?_) hev
  ring

/-- The second derivative of the restricted free energy, in closed form. -/
theorem deriv_deriv_symFreeEnergy (hm : 0 < m) (h0 : 0 < lam) (h1 : lam < 1) :
    deriv (deriv (symFreeEnergy m T)) lam = (lam ^ 2)⁻¹ + T * (lam⁻¹ + (1 - lam)⁻¹) := by
  have hev : deriv (symFreeEnergy m T) =ᶠ[nhds lam] symFreeEnergyDeriv m T := by
    filter_upwards [Ioo_mem_nhds h0 h1] with y hy
    exact deriv_symFreeEnergy hm hy.1 hy.2
  rw [hev.deriv_eq]
  exact (hasDerivAt_symFreeEnergyDeriv hm h0 h1).deriv

/-- The restricted free energy is strictly convex on `(0,1)` for every temperature `T > 0`:
its second derivative `1/lam² + T·(1/lam + 1/(1-lam))` is positive there. -/
theorem strictConvexOn_symFreeEnergy (hm : 0 < m) (hT : 0 < T) :
    StrictConvexOn ℝ (Ioo (0 : ℝ) 1) (symFreeEnergy m T) := by
  refine strictConvexOn_of_deriv2_pos (convex_Ioo 0 1) (fun x hx => ?_) (fun x hx => ?_)
  · exact (hasDerivAt_symFreeEnergy hm hx.1 hx.2).continuousAt.continuousWithinAt
  · rw [isOpen_Ioo.interior_eq] at hx
    have h1m : (0 : ℝ) < 1 - x := by linarith [hx.2]
    have hit : deriv^[2] (symFreeEnergy m T) x = deriv (deriv (symFreeEnergy m T)) x := rfl
    rw [hit, deriv_deriv_symFreeEnergy hm hx.1 hx.2]
    have := hx.1
    positivity

/-- **The critical-point equation.** An interior point `lam` is a critical point of the
restricted free energy exactly when `1/lam = T · log (m·lam/(1-lam))`. -/
theorem deriv_symFreeEnergy_eq_zero_iff (hm : 0 < m) (h0 : 0 < lam) (h1 : lam < 1) :
    deriv (symFreeEnergy m T) lam = 0 ↔ 1 / lam = T * Real.log (m * lam / (1 - lam)) := by
  rw [deriv_symFreeEnergy hm h0 h1, symFreeEnergyDeriv, one_div]
  constructor
  · intro h; linarith
  · intro h; linarith

/-! ## The Gibbs (softmax) weight -/

/-- The Gibbs weight of a single state of energy `0` against `m` states of energy `E`, at
temperature `T`: `1 / (1 + m · exp (-E/T))`. -/
noncomputable def gibbsWeight (m T E : ℝ) : ℝ := 1 / (1 + m * Real.exp (-(E / T)))

/-- The Gibbs weight of the isolated state equals a prescribed `lam ∈ (0,1)` exactly when the
energy gap is `E = T · log (m·lam/(1-lam))`. -/
theorem gibbsWeight_eq_iff (hm : 0 < m) (hT : 0 < T) (h0 : 0 < lam) (h1 : lam < 1) {E : ℝ} :
    gibbsWeight m T E = lam ↔ E = T * Real.log (m * lam / (1 - lam)) := by
  have h1m : (0 : ℝ) < 1 - lam := by linarith
  have hpos : (0 : ℝ) < 1 + m * Real.exp (-(E / T)) := by positivity
  have hlogswap : Real.log ((1 - lam) / (m * lam)) = -Real.log (m * lam / (1 - lam)) := by
    rw [Real.log_div h1m.ne' (by positivity), Real.log_div (by positivity) h1m.ne']
    ring
  constructor
  · intro h
    rw [gibbsWeight, div_eq_iff hpos.ne'] at h
    have hexp : Real.exp (-(E / T)) = (1 - lam) / (m * lam) := by
      field_simp
      nlinarith [h]
    have hlog := congrArg Real.log hexp
    rw [Real.log_exp, hlogswap] at hlog
    have hET : E / T = Real.log (m * lam / (1 - lam)) := by linarith
    rw [div_eq_iff hT.ne'] at hET
    linarith
  · intro h
    have hET : E / T = Real.log (m * lam / (1 - lam)) := by
      rw [h]; field_simp
    have hexp : Real.exp (-(E / T)) = (1 - lam) / (m * lam) := by
      rw [hET, ← Real.log_inv, Real.exp_log (by positivity), inv_div]
    rw [gibbsWeight, hexp]
    field_simp
    ring

/-- **Gibbs equilibrium.** An interior point `lam` is a critical point of the restricted free
energy exactly when it is its own Gibbs weight at energy gap `1/lam`. This is the
critical-point equation `deriv_symFreeEnergy_eq_zero_iff` read through `gibbsWeight_eq_iff`. -/
theorem deriv_symFreeEnergy_eq_zero_iff_gibbsWeight (hm : 0 < m) (hT : 0 < T)
    (h0 : 0 < lam) (h1 : lam < 1) :
    deriv (symFreeEnergy m T) lam = 0 ↔ gibbsWeight m T (1 / lam) = lam := by
  rw [deriv_symFreeEnergy_eq_zero_iff hm h0 h1, gibbsWeight_eq_iff hm hT h0 h1]

/-! ## The temperature determined by a target point -/

/-- The temperature at which a prescribed interior point `lam` solves the critical-point
equation. `deriv_symFreeEnergy_criticalTemperature` shows it does, and
`criticalTemperature_unique` that no other temperature does. -/
noncomputable def criticalTemperature (m lam : ℝ) : ℝ :=
  1 / (lam * Real.log (m * lam / (1 - lam)))

/-- For `lam` strictly between `1/(m+1)` and `1`, the argument of the logarithm in the
critical-point equation exceeds `1`. The lower endpoint `1/(m+1)` is the uniform point, at
which all `m+1` coordinates are equal. -/
theorem one_lt_symRatio (hm : 0 < m) (h0 : 1 / (m + 1) < lam) (h1 : lam < 1) :
    1 < m * lam / (1 - lam) := by
  have hm1 : (0 : ℝ) < m + 1 := by linarith
  have h1m : (0 : ℝ) < 1 - lam := by linarith
  rw [lt_div_iff₀ h1m]
  rw [div_lt_iff₀ hm1] at h0
  linarith

/-- At the uniform point `lam = 1/(m+1)` the ratio inside the logarithm equals `1`. -/
theorem symRatio_uniform (hm : 0 < m) : m * (1 / (m + 1)) / (1 - 1 / (m + 1)) = 1 := by
  have hm0 : m ≠ 0 := hm.ne'
  have hm1 : m + 1 ≠ 0 := by intro h; linarith
  rw [show (1 : ℝ) - 1 / (m + 1) = m / (m + 1) by field_simp; ring]
  field_simp

/-- **At the uniform point no temperature is critical.** The logarithm in the critical-point
equation vanishes there, so the derivative equals `-(m+1)` for every temperature `T`, and in
particular is never zero (`symFreeEnergyDeriv_uniform_ne_zero`). That is why the hypotheses
below place `lam` strictly above the uniform point `1/(m+1)`. -/
theorem symFreeEnergyDeriv_uniform (hm : 0 < m) :
    symFreeEnergyDeriv m T (1 / (m + 1)) = -(m + 1) := by
  rw [symFreeEnergyDeriv, symRatio_uniform hm, Real.log_one, one_div, inv_inv]
  ring

/-- The critical-point equation has no solution in `T` at the uniform point. -/
theorem symFreeEnergyDeriv_uniform_ne_zero (hm : 0 < m) :
    symFreeEnergyDeriv m T (1 / (m + 1)) ≠ 0 := by
  rw [symFreeEnergyDeriv_uniform hm]
  intro h
  linarith

/-- Under the same hypothesis `lam` is positive, since the uniform point `1/(m+1)` is. -/
theorem pos_of_uniform_lt (hm : 0 < m) (h0 : 1 / (m + 1) < lam) : 0 < lam :=
  lt_trans (div_pos one_pos (by linarith)) h0

/-- The determined temperature is positive. -/
theorem criticalTemperature_pos (hm : 0 < m) (h0 : 1 / (m + 1) < lam) (h1 : lam < 1) :
    0 < criticalTemperature m lam := by
  have hlam := pos_of_uniform_lt hm h0
  have hlog : 0 < Real.log (m * lam / (1 - lam)) := Real.log_pos (one_lt_symRatio hm h0 h1)
  rw [criticalTemperature]
  positivity

/-- At the determined temperature, `lam` is a critical point of the restricted free energy. -/
theorem deriv_symFreeEnergy_criticalTemperature (hm : 0 < m) (h0 : 1 / (m + 1) < lam)
    (h1 : lam < 1) :
    deriv (symFreeEnergy m (criticalTemperature m lam)) lam = 0 := by
  have hlam := pos_of_uniform_lt hm h0
  have hlog : 0 < Real.log (m * lam / (1 - lam)) := Real.log_pos (one_lt_symRatio hm h0 h1)
  rw [deriv_symFreeEnergy_eq_zero_iff hm hlam h1, criticalTemperature,
    div_mul_eq_mul_div, one_mul, mul_comm lam, ← div_div, div_self hlog.ne']

/-- No other temperature puts a critical point at `lam`: the critical-point equation is linear
in `T` with a nonzero coefficient. -/
theorem criticalTemperature_unique (hm : 0 < m) (h0 : 1 / (m + 1) < lam) (h1 : lam < 1)
    (h : deriv (symFreeEnergy m T) lam = 0) : T = criticalTemperature m lam := by
  have hlam := pos_of_uniform_lt hm h0
  have hlog : 0 < Real.log (m * lam / (1 - lam)) := Real.log_pos (one_lt_symRatio hm h0 h1)
  rw [deriv_symFreeEnergy_eq_zero_iff hm hlam h1, div_eq_iff hlam.ne'] at h
  rw [criticalTemperature, eq_div_iff (mul_pos hlam hlog).ne']
  linarith

/-- **Existence and uniqueness of the temperature.** For every target `lam` strictly between
the uniform point `1/(m+1)` and `1` there is exactly one temperature making `lam` a critical
point of the restricted free energy, and it is positive. -/
theorem existsUnique_temperature (hm : 0 < m) (h0 : 1 / (m + 1) < lam) (h1 : lam < 1) :
    ∃! T : ℝ, deriv (symFreeEnergy m T) lam = 0 :=
  ⟨criticalTemperature m lam, deriv_symFreeEnergy_criticalTemperature hm h0 h1,
    fun _ hT => criticalTemperature_unique hm h0 h1 hT⟩

/-! ## Critical points are global minimisers -/

/-- A critical point of the restricted free energy is a global minimiser on `(0,1)`: the
function is convex there, so a vanishing derivative forces a minimum. -/
theorem isMinOn_symFreeEnergy (hm : 0 < m) (hT : 0 < T) (h0 : 0 < lam) (h1 : lam < 1)
    (hcrit : deriv (symFreeEnergy m T) lam = 0) :
    IsMinOn (symFreeEnergy m T) (Ioo 0 1) lam := by
  refine (strictConvexOn_symFreeEnergy hm hT).convexOn.isMinOn_of_rightDeriv_eq_zero ?_ ?_
  · rw [isOpen_Ioo.interior_eq]; exact ⟨h0, h1⟩
  · rw [(hasDerivAt_symFreeEnergy hm h0 h1).hasDerivWithinAt.derivWithin
      (uniqueDiffWithinAt_Ioi lam), ← deriv_symFreeEnergy hm h0 h1]
    exact hcrit

/-- Strict convexity makes the minimiser unique. -/
theorem symFreeEnergy_minimiser_unique (hm : 0 < m) (hT : 0 < T) {x y : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1)
    (hxm : IsMinOn (symFreeEnergy m T) (Ioo 0 1) x)
    (hym : IsMinOn (symFreeEnergy m T) (Ioo 0 1) y) : x = y :=
  (strictConvexOn_symFreeEnergy hm hT).eq_of_isMinOn hxm hym hx hy

end Wall


end ClassicalLean.Simplex
