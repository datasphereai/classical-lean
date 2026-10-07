/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.Tactic.ComputeDegree

/-!
# The ring of integers and discriminant of `ℚ(√2, √3)`

Let `F` be a number field with a power basis over `ℚ` whose generator `θ` has minimal polynomial

  `g = X ^ 4 + 4 X ^ 3 + 2 X ^ 2 - 4 X - 2`.

In `ℚ(√2, √3)` one such `θ` is `(√2 + √6) / 2 - 1`; `θ + 1 = 2 cos (π / 12)`, the generator of
the ring of integers of the maximal real subfield of `ℚ(ζ₂₄)`.  This module proves, for every such
`F`, that `ℤ[θ]` is the ring of integers and that `discr F = 2304 = 2 ^ 8 * 3 ^ 2`.
`CompositumDiscriminant` applies it to `K1 = ℚ(√2, √3)`, where it replaced an axiom.

## Main results

* `g_isEisensteinAt_two`, `irreducible_g`, `irreducible_g_rat`.
* `discr_powerBasis : Algebra.discr ℚ B.basis = 2304`: the determinant of the matrix of power
  sums `Tr θ ^ (i + j)`, which are `4, -4, 12, -28, 80, -224, 648` (`trace_pow_values`).
* `three_dvd_coeffs`, `mem_adjoin_of_three_smul_mem`: removing a factor `3` from an element of
  `ℤ[θ]`.
* `isIntegralClosure_adjoin : IsIntegralClosure ℤ[θ] ℤ F`.
* `discr_eq : NumberField.discr F = 2304`.

## Method

The route is the one Mathlib uses for the ring of integers of `ℚ(ζ_{p ^ k})`
(`IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow`).
`Algebra.discr_mul_isIntegral_mem_adjoin` puts `2304 z` in `ℤ[θ]` for every algebraic integer `z`.
`g` is Eisenstein at `2`, so `mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt`
removes `2 ^ 8`.

The prime `3` cannot be removed the same way.  In `ℚ(√2, √3)` it has ramification index `2` and
residue degree `2` (`g ≡ (X ^ 2 + 2 X + 2) ^ 2 mod 3`), so no element of degree `4` has an
Eisenstein-at-`3` minimal polynomial.  `three_dvd_coeffs` does that step by hand.

Write `√2, √3, √6` as polynomials in `θ` (`s2`, `s3`, `s6`).  For integral `y` with
`3 y ∈ ℤ[θ]`, the integer traces of `2 y`, `2 y √2`, `v ^ 2` and `v ^ 2 √2` force `3` to divide
every coordinate.  Here `v = (C √3 + D √6) / 3` is what is left of `2 y` once its rational and
`√2` parts are removed.  The traces use only `Tr 1 = 4` and `Tr √d = 0`; the second holds
because `X ^ 2 - d` is the minimal polynomial and its next coefficient is `0`.

## What Mathlib v4.34.0 was searched for

Mathlib's `NumberField/Ideal/KummerDedekind.lean` states the Kummer–Dedekind criterion under the
hypothesis `¬ p ∣ RingOfIntegers.exponent θ`, which is what is to be proved here, not a tool for
proving it.  `grep -rniE 'dedekind.{0,20}criterion'` over Mathlib finds only that file; no
Dedekind index criterion turned up.  That is a report of a search, not a claim about Mathlib.
-/

namespace ClassicalLean.NumberTheory.BiquadraticDiscriminant

open Polynomial NumberField nonZeroDivisors

/-- `X ^ 4 + 4 X ^ 3 + 2 X ^ 2 - 4 X - 2`, the minimal polynomial of `(√2 + √6) / 2 - 1`. -/
noncomputable def g : ℤ[X] := X ^ 4 + C 4 * X ^ 3 + C 2 * X ^ 2 - C 4 * X - C 2

theorem natDegree_g : g.natDegree = 4 := by
  unfold g; compute_degree!

theorem monic_g : g.Monic := by
  unfold g; monicity!

theorem coeff_g_zero : g.coeff 0 = -2 := by simp [g, coeff_X, coeff_X_pow]
theorem coeff_g_one : g.coeff 1 = -4 := by simp [g, coeff_X, coeff_X_pow]
theorem coeff_g_two : g.coeff 2 = 2 := by simp [g, coeff_X, coeff_X_pow]
theorem coeff_g_three : g.coeff 3 = 4 := by simp [g, coeff_X, coeff_X_pow]

theorem g_isEisensteinAt_two : g.IsEisensteinAt (Ideal.span {(2 : ℤ)}) where
  leading := by
    rw [monic_g.leadingCoeff, Ideal.mem_span_singleton]; decide
  mem {n} hn := by
    rw [natDegree_g] at hn
    rw [Ideal.mem_span_singleton]
    interval_cases n <;>
      simp only [coeff_g_zero, coeff_g_one, coeff_g_two, coeff_g_three] <;> decide
  notMem := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, coeff_g_zero]; decide

theorem irreducible_g : Irreducible g :=
  g_isEisensteinAt_two.irreducible
    ((Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two) monic_g.isPrimitive
    (by rw [natDegree_g]; norm_num)

theorem irreducible_g_rat : Irreducible (g.map (algebraMap ℤ ℚ)) :=
  (IsPrimitive.Int.irreducible_iff_irreducible_map_cast monic_g.isPrimitive).mp irreducible_g

section Field

variable {F : Type*} [Field F]

/-- `√2`, written as a polynomial in a root `θ` of `g`. -/
def s2 (θ : F) : F := θ ^ 3 + 3 * θ ^ 2 - 2

/-- `√3`, written as a polynomial in a root `θ` of `g`. -/
def s3 (θ : F) : F := θ ^ 2 + 2 * θ - 1

/-- `√6`, written as a polynomial in a root `θ` of `g`. -/
def s6 (θ : F) : F := -θ ^ 3 - 3 * θ ^ 2 + 2 * θ + 4

theorem two_mul_coords (θ : F) : 2 * θ = -2 + s2 θ + s6 θ := by unfold s2 s6; ring
theorem pow_two_coords (θ : F) : θ ^ 2 = 3 - s2 θ + s3 θ - s6 θ := by unfold s2 s3 s6; ring
theorem pow_three_coords (θ : F) : θ ^ 3 = -7 + 4 * s2 θ - 3 * s3 θ + 3 * s6 θ := by
  unfold s2 s3 s6; ring

variable {θ : F} (h : θ ^ 4 + 4 * θ ^ 3 + 2 * θ ^ 2 - 4 * θ - 2 = 0)
include h

theorem s2_sq : s2 θ ^ 2 = 2 := by unfold s2; linear_combination (θ ^ 2 + 2 * θ - 1) * h
theorem s3_sq : s3 θ ^ 2 = 3 := by unfold s3; linear_combination h
theorem s6_sq : s6 θ ^ 2 = 6 := by unfold s6; linear_combination (θ ^ 2 + 2 * θ - 5) * h
theorem s2_mul_s3 : s2 θ * s3 θ = s6 θ := by unfold s2 s3 s6; linear_combination (θ + 1) * h
theorem s2_mul_s6 : s2 θ * s6 θ = 2 * s3 θ := by
  unfold s2 s3 s6; linear_combination (-θ ^ 2 - 2 * θ + 3) * h
theorem s3_mul_s6 : s3 θ * s6 θ = 3 * s2 θ := by
  unfold s2 s3 s6; linear_combination (-θ - 1) * h

theorem pow_four_coords : θ ^ 4 = 20 - 12 * s2 θ + 10 * s3 θ - 8 * s6 θ := by
  unfold s2 s3 s6; linear_combination h
theorem pow_five_coords : θ ^ 5 = -56 + 37 * s2 θ - 30 * s3 θ + 23 * s6 θ := by
  unfold s2 s3 s6; linear_combination (θ - 4) * h
theorem pow_six_coords : θ ^ 6 = 162 - 110 * s2 θ + 90 * s3 θ - 66 * s6 θ := by
  unfold s2 s3 s6; linear_combination (θ ^ 2 - 4 * θ + 14) * h

end Field

/-- `n` is not a rational square when no `k ≤ n` has `k * k = n`. -/
theorem not_isSquare_natCast {n : ℕ} (hn : ∀ k ≤ n, k * k ≠ n) : ¬ IsSquare (n : ℚ) := by
  rw [Rat.isSquare_natCast_iff]
  rintro ⟨k, hk⟩
  exact hn k (hk ▸ Nat.le_mul_self k) hk.symm

theorem not_isSquare_two : ¬ IsSquare (2 : ℚ) := by
  exact_mod_cast not_isSquare_natCast (n := 2) (by decide)
theorem not_isSquare_three : ¬ IsSquare (3 : ℚ) := by
  exact_mod_cast not_isSquare_natCast (n := 3) (by decide)
theorem not_isSquare_six : ¬ IsSquare (6 : ℚ) := by
  exact_mod_cast not_isSquare_natCast (n := 6) (by decide)

section NumberField

variable {F : Type*} [Field F] [NumberField F]

/-- An element whose square is a non-square rational has trace zero: its minimal polynomial is
`X ^ 2 - d`, whose next coefficient is `0`. -/
theorem trace_eq_zero_of_sq_eq {x : F} {d : ℚ} (hd : ¬ IsSquare d)
    (hx : x ^ 2 = algebraMap ℚ F d) : Algebra.trace ℚ F x = 0 := by
  have hirr : Irreducible (X ^ 2 - C d) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two fun b hb => hd ⟨b, by rw [← hb, sq]⟩
  have hmin : minpoly ℚ x = X ^ 2 - C d :=
    (minpoly.eq_of_irreducible_of_monic hirr (by simp [hx])
      (monic_X_pow_sub_C d two_ne_zero)).symm
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, hmin, nextCoeff, natDegree_X_pow_sub_C]
  simp

variable {θ : F} (h : θ ^ 4 + 4 * θ ^ 3 + 2 * θ ^ 2 - 4 * θ - 2 = 0)
  (hF : Module.finrank ℚ F = 4)
include h hF

/-- The trace in coordinates `1, √2, √3, √6`: only the rational part survives, times `4`. -/
theorem trace_coords (a b c d : ℚ) :
    Algebra.trace ℚ F (a • 1 + b • s2 θ + c • s3 θ + d • s6 θ) = 4 * a := by
  have t2 : Algebra.trace ℚ F (s2 θ) = 0 :=
    trace_eq_zero_of_sq_eq not_isSquare_two (by rw [s2_sq h, map_ofNat])
  have t3 : Algebra.trace ℚ F (s3 θ) = 0 :=
    trace_eq_zero_of_sq_eq not_isSquare_three (by rw [s3_sq h, map_ofNat])
  have t6 : Algebra.trace ℚ F (s6 θ) = 0 :=
    trace_eq_zero_of_sq_eq not_isSquare_six (by rw [s6_sq h, map_ofNat])
  have t1 : Algebra.trace ℚ F 1 = 4 := by
    rw [← map_one (algebraMap ℚ F), Algebra.trace_algebraMap, hF]; norm_num
  simp only [map_add, map_smul, t1, t2, t3, t6, smul_eq_mul, mul_zero, add_zero]
  ring

/-- `trace_coords` for an element given by an equation. -/
theorem trace_eq_of_coords {y : F} (a b c d : ℚ)
    (hy : y = (a : F) + (b : F) * s2 θ + (c : F) * s3 θ + (d : F) * s6 θ) :
    Algebra.trace ℚ F y = 4 * a := by
  rw [hy, ← trace_coords h hF a b c d]
  simp only [Algebra.smul_def, eq_ratCast, mul_one]

/-- The power sums `Tr θ ^ k` for `k ≤ 6`: `4, -4, 12, -28, 80, -224, 648`. -/
theorem trace_pow_values :
    Algebra.trace ℚ F (θ ^ 0) = 4 ∧ Algebra.trace ℚ F (θ ^ 1) = -4 ∧
    Algebra.trace ℚ F (θ ^ 2) = 12 ∧ Algebra.trace ℚ F (θ ^ 3) = -28 ∧
    Algebra.trace ℚ F (θ ^ 4) = 80 ∧ Algebra.trace ℚ F (θ ^ 5) = -224 ∧
    Algebra.trace ℚ F (θ ^ 6) = 648 := by
  have key := fun a b c d y => trace_eq_of_coords h hF (y := y) a b c d
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [key 1 0 0 0 _ (by simp)]; norm_num
  · rw [key (-1) (1 / 2) 0 (1 / 2) _
      (by push_cast; linear_combination (1 / 2 : F) * two_mul_coords θ)]
    norm_num
  · rw [key 3 (-1) 1 (-1) _ (by push_cast; linear_combination pow_two_coords θ)]; norm_num
  · rw [key (-7) 4 (-3) 3 _ (by push_cast; linear_combination pow_three_coords θ)]; norm_num
  · rw [key 20 (-12) 10 (-8) _ (by push_cast; linear_combination pow_four_coords h)]; norm_num
  · rw [key (-56) 37 (-30) 23 _ (by push_cast; linear_combination pow_five_coords h)]; norm_num
  · rw [key 162 (-110) 90 (-66) _ (by push_cast; linear_combination pow_six_coords h)]; norm_num

omit h hF in
/-- The trace of an algebraic integer is an integer. -/
theorem trace_mem_int {v : F} (hv : IsIntegral ℤ v) : ∃ n : ℤ, Algebra.trace ℚ F v = n := by
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace (L := ℚ) hv)
  exact ⟨n, by rw [← hn, eq_intCast]⟩

/-- **The step at `3`.**  If `y` is integral and `3 y = c₀ + c₁ θ + c₂ θ ² + c₃ θ ³` with integer
`cᵢ`, then `3` divides every `cᵢ`.  Write `6 y` in the coordinates `1, √2, √3, √6` as
`A + B √2 + C √3 + D √6` (integers).  The integer traces of `2 y` and `2 y √2` give `3 ∣ A` and
`3 ∣ B`; for `v = 2 y - A / 3 - (B / 3) √2 = (C √3 + D √6) / 3`, the integer traces of `v ²` and
`v ² √2` give `3 ∣ C ² + 2 D ²` and `3 ∣ C D`, hence `3 ∣ C` and `3 ∣ D`.  The change of
coordinates back to `cᵢ` has determinant `-8`, prime to `3`. -/
theorem three_dvd_coeffs (hθ : IsIntegral ℤ θ) {y : F} (hy : IsIntegral ℤ y) (c₀ c₁ c₂ c₃ : ℤ)
    (h3 : 3 * y = c₀ + c₁ * θ + c₂ * θ ^ 2 + c₃ * θ ^ 3) :
    3 ∣ c₀ ∧ 3 ∣ c₁ ∧ 3 ∣ c₂ ∧ 3 ∣ c₃ := by
  have i2 : IsIntegral ℤ (2 : F) := by simpa using isIntegral_algebraMap (R := ℤ) (A := F) (x := 2)
  have i3 : IsIntegral ℤ (3 : F) := by simpa using isIntegral_algebraMap (R := ℤ) (A := F) (x := 3)
  have iint : ∀ n : ℤ, IsIntegral ℤ (n : F) := fun n => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := F) (x := n)
  have is2 : IsIntegral ℤ (s2 θ) := ((hθ.pow 3).add (i3.mul (hθ.pow 2))).sub i2
  set A : ℤ := 2 * c₀ - 2 * c₁ + 6 * c₂ - 14 * c₃ with hA
  set B : ℤ := c₁ - 2 * c₂ + 8 * c₃ with hB
  set C : ℤ := 2 * c₂ - 6 * c₃ with hC
  set D : ℤ := c₁ - 2 * c₂ + 6 * c₃ with hD
  have hw : 2 * y = ((A / 3 : ℚ) : F) + ((B / 3 : ℚ) : F) * s2 θ + ((C / 3 : ℚ) : F) * s3 θ +
      ((D / 3 : ℚ) : F) * s6 θ := by
    unfold s2 s3 s6; push_cast [hA, hB, hC, hD]; linear_combination (2 / 3 : F) * h3
  have iw : IsIntegral ℤ (2 * y) := i2.mul hy
  -- `3 ∣ A`
  obtain ⟨n₀, hn₀⟩ := trace_mem_int iw
  rw [trace_eq_of_coords h hF _ _ _ _ hw] at hn₀
  have hA3 : 3 ∣ A := by
    have : 4 * A = 3 * n₀ := by
      have : (4 * A : ℚ) = 3 * n₀ := by linear_combination 3 * hn₀
      exact_mod_cast this
    omega
  -- `3 ∣ B`
  obtain ⟨n₁, hn₁⟩ := trace_mem_int (iw.mul is2)
  rw [trace_eq_of_coords h hF (2 * (B / 3)) (A / 3) (2 * (D / 3)) (C / 3) (by
    rw [hw]; push_cast
    linear_combination ((B : F) / 3) * s2_sq h + ((C : F) / 3) * s2_mul_s3 h +
      ((D : F) / 3) * s2_mul_s6 h)] at hn₁
  have hB3 : 3 ∣ B := by
    have : 8 * B = 3 * n₁ := by
      have : (8 * B : ℚ) = 3 * n₁ := by linear_combination 3 * hn₁
      exact_mod_cast this
    omega
  obtain ⟨a, ha⟩ := hA3
  obtain ⟨b, hb⟩ := hB3
  -- `v = 2 y - a - b √2 = (C √3 + D √6) / 3`
  have iv : IsIntegral ℤ (2 * y - a - b * s2 θ) := (iw.sub (iint a)).sub ((iint b).mul is2)
  have hv : 2 * y - a - b * s2 θ = ((C / 3 : ℚ) : F) * s3 θ + ((D / 3 : ℚ) : F) * s6 θ := by
    rw [hw, ha, hb]; push_cast; ring
  obtain ⟨n₂, hn₂⟩ := trace_mem_int (iv.pow 2)
  rw [trace_eq_of_coords h hF ((C ^ 2 + 2 * D ^ 2) / 3) (2 * C * D / 3) 0 0 (by
    rw [hv]; push_cast
    linear_combination ((C : F) / 3) ^ 2 * s3_sq h + ((D : F) / 3) ^ 2 * s6_sq h +
      2 * ((C : F) / 3) * ((D : F) / 3) * s3_mul_s6 h)] at hn₂
  obtain ⟨n₃, hn₃⟩ := trace_mem_int ((iv.pow 2).mul is2)
  rw [trace_eq_of_coords h hF (2 * (2 * C * D / 3)) ((C ^ 2 + 2 * D ^ 2) / 3) 0 0 (by
    rw [hv]; push_cast
    linear_combination ((C : F) / 3) ^ 2 * s2 θ * s3_sq h + ((D : F) / 3) ^ 2 * s2 θ * s6_sq h +
      2 * ((C : F) / 3) * ((D : F) / 3) * s2 θ * s3_mul_s6 h +
      (2 * ((C : F) / 3) * ((D : F) / 3) * 3 + 0) * s2_sq h)] at hn₃
  have hP : 3 ∣ C ^ 2 + 2 * D ^ 2 := by
    have : 4 * (C ^ 2 + 2 * D ^ 2) = 3 * n₂ := by
      have : (4 * (C ^ 2 + 2 * D ^ 2) : ℚ) = 3 * n₂ := by linear_combination 3 * hn₂
      exact_mod_cast this
    generalize C ^ 2 + 2 * D ^ 2 = P at this ⊢
    omega
  have hQ : 3 ∣ C * D := by
    have : 16 * (C * D) = 3 * n₃ := by
      have : (16 * (C * D) : ℚ) = 3 * n₃ := by linear_combination 3 * hn₃
      exact_mod_cast this
    generalize C * D = Q at this ⊢
    omega
  have hCD : 3 ∣ C ∧ 3 ∣ D := by
    have key : ∀ u v : ZMod 3, u * v = 0 → u ^ 2 + 2 * v ^ 2 = 0 → u = 0 ∧ v = 0 := by decide
    have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hQ
    have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hP
    push_cast at h1 h2
    obtain ⟨hu, hv⟩ := key _ _ h1 h2
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hu,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hv⟩
  obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := hCD
  omega

end NumberField

section PowerBasis

variable {F : Type*} [Field F] [NumberField F] (B : PowerBasis ℚ F)
  (hmin : minpoly ℚ B.gen = g.map (algebraMap ℤ ℚ))
include hmin

theorem gen_root : B.gen ^ 4 + 4 * B.gen ^ 3 + 2 * B.gen ^ 2 - 4 * B.gen - 2 = 0 := by
  have := minpoly.aeval ℚ B.gen
  rw [hmin, aeval_map_algebraMap] at this
  simp only [g, map_sub, map_add, map_mul, map_pow, aeval_X, map_ofNat] at this
  linear_combination this

theorem dim_eq : B.dim = 4 := by
  rw [← B.natDegree_minpoly, hmin,
    natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int, natDegree_g]

theorem finrank_eq : Module.finrank ℚ F = 4 := B.finrank.trans (dim_eq B hmin)

/-- **The discriminant of the power basis `1, θ, θ ², θ ³` is `2304`**: the determinant of
the matrix of power sums `(Tr θ ^ (i + j))`. -/
theorem discr_powerBasis : Algebra.discr ℚ B.basis = 2304 := by
  obtain ⟨t0, t1, t2, t3, t4, t5, t6⟩ :=
    trace_pow_values (gen_root B hmin) (finrank_eq B hmin)
  rw [pow_zero] at t0
  rw [pow_one] at t1
  rw [← Algebra.discr_reindex ℚ B.basis (finCongr (dim_eq B hmin)), Algebra.discr_def]
  have hM : Algebra.traceMatrix ℚ (B.basis ∘ (finCongr (dim_eq B hmin)).symm) =
      !![4, -4, 12, -28; -4, 12, -28, 80; 12, -28, 80, -224; -28, 80, -224, 648] := by
    ext i j
    rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    simp only [Function.comp_apply, PowerBasis.coe_basis, finCongr_symm, finCongr_apply,
      Fin.val_cast, ← pow_add]
    fin_cases i <;> fin_cases j <;> simp [t0, t1, t2, t3, t4, t5, t6]
  rw [hM]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  norm_num

theorem aeval_gen_g : aeval B.gen g = 0 := by
  have := gen_root B hmin
  simp only [g, map_sub, map_add, map_mul, map_pow, aeval_X, map_ofNat]
  linear_combination this

theorem isIntegral_gen : IsIntegral ℤ B.gen := ⟨g, monic_g, aeval_gen_g B hmin⟩

theorem minpoly_int_gen : minpoly ℤ B.gen = g := by
  apply map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (isIntegral_gen B hmin), hmin]

omit [NumberField F] hmin in
theorem isIntegral_zsmul (n : ℤ) {x : F} (hx : IsIntegral ℤ x) : IsIntegral ℤ (n • x) := by
  have hn : IsIntegral ℤ (n : F) := by simpa using isIntegral_algebraMap (R := ℤ) (A := F) (x := n)
  rw [zsmul_eq_mul]
  exact hn.mul hx

/-- Removing a factor `3`: if `y` is integral and `3 y ∈ ℤ[θ]`, then `y ∈ ℤ[θ]`. -/
theorem mem_adjoin_of_three_smul_mem {y : F} (hy : IsIntegral ℤ y)
    (h3 : (3 : ℤ) • y ∈ Algebra.adjoin ℤ ({B.gen} : Set F)) :
    y ∈ Algebra.adjoin ℤ ({B.gen} : Set F) := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h3
  obtain ⟨P, hP⟩ := h3
  have hQ : aeval B.gen (P %ₘ g) = (3 : ℤ) • y := by
    rw [aeval_modByMonic_eq_self_of_root (aeval_gen_g B hmin)]; exact hP
  have hg1 : g ≠ 1 := fun h1 => by simpa [h1] using natDegree_g
  have hdeg : (P %ₘ g).natDegree < 4 := natDegree_g ▸ natDegree_modByMonic_lt P monic_g hg1
  have hsum := aeval_eq_sum_range' (x := B.gen) hdeg
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
    zsmul_eq_mul, mul_one] at hsum
  obtain ⟨d₀, d₁, d₂, d₃⟩ := three_dvd_coeffs (gen_root B hmin) (finrank_eq B hmin)
    (isIntegral_gen B hmin) hy ((P %ₘ g).coeff 0) ((P %ₘ g).coeff 1) ((P %ₘ g).coeff 2)
    ((P %ₘ g).coeff 3) (by rw [← hsum, hQ, zsmul_eq_mul]; push_cast; ring)
  refine mem_adjoin_of_dvd_coeff_of_dvd_aeval (p := (3 : ℤ)) (by norm_num) (fun i hi => ?_) hQ
  have : i < 4 := lt_of_lt_of_le (Finset.mem_range.mp hi) (by omega)
  interval_cases i <;> assumption

/-- **`ℤ[θ]` is the ring of integers.**  `discr_mul_isIntegral_mem_adjoin` puts
`2304 z = 2 ^ 8 · 9 z` in `ℤ[θ]` for every algebraic integer `z`; Eisenstein at `2` removes `2 ^ 8`
(`mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt`), and
`mem_adjoin_of_three_smul_mem`, used twice, removes `9`. -/
theorem isIntegralClosure_adjoin :
    IsIntegralClosure (Algebra.adjoin ℤ ({B.gen} : Set F)) ℤ F := by
  have hint := isIntegral_gen B hmin
  refine ⟨Subtype.val_injective, @fun x => ⟨fun hx => ⟨⟨x, ?_⟩, rfl⟩, ?_⟩⟩
  swap
  · rintro ⟨y, rfl⟩
    exact IsIntegral.algebraMap
      ((le_integralClosure_iff_isIntegral.1 (adjoin_le_integralClosure hint)).isIntegral _)
  have H := Algebra.discr_mul_isIntegral_mem_adjoin ℚ hint hx
  rw [discr_powerBasis B hmin] at H
  have H' : (2 : ℤ) ^ 8 • ((3 : ℤ) • ((3 : ℤ) • x)) ∈ Algebra.adjoin ℤ ({B.gen} : Set F) := by
    convert H using 1
    rw [smul_smul, smul_smul, zsmul_eq_mul, Algebra.smul_def]
    norm_num
  have hei : (minpoly ℤ B.gen).IsEisensteinAt (Submodule.span ℤ {(2 : ℤ)}) := by
    rw [minpoly_int_gen B hmin]; exact g_isEisensteinAt_two
  have H9 := mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt Int.prime_two hint
    (isIntegral_zsmul 3 (isIntegral_zsmul 3 hx)) H' hei
  exact mem_adjoin_of_three_smul_mem B hmin hx
    (mem_adjoin_of_three_smul_mem B hmin (isIntegral_zsmul 3 hx) H9)

/-- **The absolute discriminant is `2304`.**  `ℤ[θ]` is `𝓞 F` (`isIntegralClosure_adjoin`), so
its power basis is a `ℤ`-basis of `𝓞 F`, and `NumberField.discr_eq_discr` turns its
discriminant, `2304` by `discr_powerBasis`, into `NumberField.discr F`.  The same pattern as
Mathlib's `IsCyclotomicExtension.Rat.discr_prime_pow`. -/
theorem discr_eq : NumberField.discr F = 2304 := by
  have hcl := isIntegralClosure_adjoin B hmin
  let pB₁ : PowerBasis ℤ (𝓞 F) := (Algebra.adjoin.powerBasis' (isIntegral_gen B hmin)).map
    (IsIntegralClosure.equiv ℤ (Algebra.adjoin ℤ ({B.gen} : Set F)) F (𝓞 F))
  apply (algebraMap ℤ ℚ).injective_int
  rw [← NumberField.discr_eq_discr _ pB₁.basis, ← Algebra.discr_localizationLocalization ℤ ℤ⁰ F]
  have hd : pB₁.dim = B.dim := by
    rw [← PowerBasis.finrank, ← PowerBasis.finrank]
    exact RingOfIntegers.rank F
  rw [← Algebra.discr_reindex _ _ (finCongr hd)]
  convert discr_powerBasis B hmin using 2
  · ext i
    simp only [Function.comp_apply, Module.Basis.localizationLocalization_apply,
      PowerBasis.coe_basis, finCongr_symm, finCongr_apply, Fin.val_cast]
    simp [pB₁]

end PowerBasis

end ClassicalLean.NumberTheory.BiquadraticDiscriminant
