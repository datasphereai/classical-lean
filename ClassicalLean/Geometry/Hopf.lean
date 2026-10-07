/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import ClassicalLean.Geometry.SU2SO3

/-!
# The Hopf map from the unit quaternions to the 2-sphere

The Hopf map sends a quaternion `q = a + bi + cj + dk` to the triple

`(2(ac + bd), 2(bc - ad), a² + b² - c² - d²)`.

Five things are proved about it here.

1. **It squares up.** `x² + y² + z² = (normSq q)²` for *every* quaternion (`hopfMap_sq_add`), an
   instance of Euler's four-square identity. On `S³` this says the image lies on `S²`.
2. **It is invariant under the left circle action.** Multiplying `q` on the left by a unit
   quaternion `u` with `u.imJ = u.imK = 0` — a unit of the complex subfield `ℝ + ℝi` — does not
   change the image (`hopfMap_mul_left`).
3. **Right multiplication rotates instead.** Multiplying `q` on the *right* by `cos θ + sin θ · i`
   turns the first two coordinates of the image through the angle `2θ` and leaves the third fixed
   (`hopfMap_mul_phase`). So "left, not right" is a theorem of this file, not an aside about it.
4. **Those are the only coincidences.** If two points of `S³` have the same image, they differ by
   exactly such a left factor (`exists_mul_left_of_hopfMap_eq`), so the preimage of a point is
   precisely one orbit of that circle action.
5. **It is onto `S²`** (`hopfMap_surjective`), by an explicit formula for a preimage.

**Dated 2026-09-24 (order G-7, J2 step 2; round 23):** a sixth. **It is the orbit of `i` under
the rotation action** of `Geometry/SU2SO3`, which this file now imports: for every quaternion `q`,
`adjoint (star q) i = q̄ · i · q` is the pure quaternion whose `(i, j, k)` components are the
coordinates of `hopfMap q` in reverse order (`adjoint_star_eq_hopfMap`, `hopfMap_eq_adjoint_star`).
The rotation is by `star q`, not `q`: `adjoint q i` matches `hopfMap q` under no signed permutation
of its components. `hopfMap_sq_add` is now proved from this and `adjoint_normSq` (conjugation
by `q` scales `normSq` by `(normSq q)²`), its statement unchanged.

Together, 2, 4 and 5 say that every point of `S²` has a preimage and that the preimages are exactly
the orbits of that circle action. Context, not proved here: this is what makes the map a bundle
with fibre `S¹`, and the bundle structure — local triviality, smoothness, the Hopf invariant — is
not touched below, nor is the freeness of the action. Nothing here is a sketch or an outline:
every statement in this file is proved.

Mathlib's `Quaternion ℝ` needs `set_option backward.isDefEq.respectTransparency false` for
instance search on `ℍ`, as in `Mathlib/Analysis/Quaternion.lean`.
Superseded 2026-09-23: builds without the option at v4.34.0 (round 19).

**What the source file `HopfFibration_S3_Sketch.lean` had, and where it went.** One line per source
declaration, so that a drop is a decision on the record rather than a silence.

* `UnitQuat`, `UnitVec3` (structures bundling a quaternion, resp. a real triple, with a proof that
  it is a unit) — dropped: everything below is stated for a bare `q : ℍ`, resp. a bare triple
  `(x, y, z)`, carrying the unit equation as a hypothesis where it is needed, so no new type is
  introduced. Several statements then hold with no unit hypothesis at all.
* `hopf_map` — shipped as `hopfMap`, on all of `ℍ` rather than on the subtype.
* `hopf_map_on_s2` — shipped strengthened as `hopfMap_sq_add`, which drops the unit hypothesis and
  computes `(normSq q)²`; the source's unit case is kept as `hopfMap_sq_add_of_normSq_eq_one`.
* `hopf_equiv` (the relation "`p` and `q` differ by a phase factor") — dropped as a named
  definition: it is spelled out in the statements that use it, which is one indirection fewer.
* `hopf_equiv_same_image` — shipped strengthened as `hopfMap_mul_left`, which needs no unit
  hypothesis on `q`; `hopfMap_phase_mul` is the `phase θ` form.
* `exists_cos_sin_eq` (a `private` helper) — shipped as `exists_cos_sin_of_sq_add_sq_eq_one`, not
  private, because `exists_phase_of_normSq_eq_one` and the fibre theorem both read better with it
  available.
* `hopf_fiber_s1` — shipped as `exists_mul_left_of_hopfMap_eq` and `exists_phase_mul_of_hopfMap_eq`,
  stated from the equality of images rather than from a common base point in `UnitVec3`.
* `hopf_map_surjective` — shipped under the same name.
* `hopf_coherent_hemisphere` — dropped: it unfolds the third coordinate to `a² + b² - c² - d²`,
  which is true by definition of the map and closed by `simp`, so it states nothing that
  `hopfMap` does not already say. Its source docstring is also written in vocabulary this library
  does not use.
-/

open scoped Quaternion
open Real

namespace ClassicalLean.Geometry

/-! ## The map, and the four-square identity -/

/-- The Hopf map `ℍ → ℝ³`, written out in the four real components of a quaternion. -/
noncomputable def hopfMap (q : ℍ) : ℝ × ℝ × ℝ :=
  (2 * (q.re * q.imJ + q.imI * q.imK),
   2 * (q.imI * q.imJ - q.re * q.imK),
   q.re ^ 2 + q.imI ^ 2 - q.imJ ^ 2 - q.imK ^ 2)

/-- **The Hopf map is the orbit of `i` under the rotation action.** For every quaternion `q`,
`adjoint (star q) i = q̄ · i · q` is the pure quaternion whose `(i, j, k)` components are the
coordinates of `hopfMap q` in reverse order: its real part is `0`. No unit hypothesis. -/
theorem adjoint_star_eq_hopfMap (q : ℍ) :
    adjoint (star q) ⟨0, 1, 0, 0⟩
      = (⟨0, (hopfMap q).2.2, (hopfMap q).2.1, (hopfMap q).1⟩ : ℍ) := by
  ext <;> simp [adjoint, hopfMap] <;> ring

/-- **The Hopf map reads the rotated `i`.** For every quaternion `q`, with
`x = adjoint (star q) i = q̄ · i · q`, the Hopf map is `x`'s imaginary part in reverse order
`(k, j, i)`. No unit hypothesis. -/
theorem hopfMap_eq_adjoint_star (q : ℍ) :
    hopfMap q = ((adjoint (star q) ⟨0, 1, 0, 0⟩).imK, (adjoint (star q) ⟨0, 1, 0, 0⟩).imJ,
      (adjoint (star q) ⟨0, 1, 0, 0⟩).imI) := by
  rw [adjoint_star_eq_hopfMap]

/-- **Euler's four-square identity, in Hopf coordinates.** The squared length of `hopfMap q` is
`(normSq q)²`, for every quaternion — no unit hypothesis. A single `ring` identity in the four
components.
Dated 2026-09-24 (order G-7, J2 step 2): now proved from `adjoint_star_eq_hopfMap` and
`Geometry/SU2SO3`'s `adjoint_normSq` — conjugation by `star q` scales `normSq` by
`(normSq q)²` — rather than by `ring`; the statement is unchanged. -/
theorem hopfMap_sq_add (q : ℍ) :
    (hopfMap q).1 ^ 2 + (hopfMap q).2.1 ^ 2 + (hopfMap q).2.2 ^ 2 = Quaternion.normSq q ^ 2 := by
  have h := adjoint_normSq (star q) (⟨0, 1, 0, 0⟩ : ℍ)
  rw [adjoint_star_eq_hopfMap, Quaternion.normSq_star] at h
  simp only [Quaternion.normSq_def'] at h
  rw [Quaternion.normSq_def']
  linear_combination h

/-- **The image of `S³` lies on `S²`.** Immediate from `hopfMap_sq_add`. -/
theorem hopfMap_sq_add_of_normSq_eq_one {q : ℍ} (hq : Quaternion.normSq q = 1) :
    (hopfMap q).1 ^ 2 + (hopfMap q).2.1 ^ 2 + (hopfMap q).2.2 ^ 2 = 1 := by
  rw [hopfMap_sq_add, hq, one_pow]

/-! ## The circle action and its invariance -/

/-- The unit quaternion `cos θ + sin θ · i`. As `θ` runs over `ℝ` these are exactly the unit
quaternions with vanishing `imJ` and `imK` components (see `exists_phase_of_normSq_eq_one`), i.e.
the unit circle of the complex subfield `ℝ + ℝi` of `ℍ`. -/
noncomputable def phase (θ : ℝ) : ℍ := (⟨Real.cos θ, Real.sin θ, 0, 0⟩ : ℍ)

/-- `phase θ` is a unit quaternion. -/
theorem phase_normSq (θ : ℝ) : Quaternion.normSq (phase θ) = 1 := by
  rw [Quaternion.normSq_def']
  simp only [phase]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- Any pair `(c, s)` on the unit circle of `ℝ²` is `(cos θ, sin θ)` for some `θ`. Proved from
Mathlib's `Real.cos_arccos` and `Real.sin_arccos`, splitting on the sign of `s`. -/
theorem exists_cos_sin_of_sq_add_sq_eq_one {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = c ∧ Real.sin θ = s := by
  have hc_le : c ≤ 1 := by nlinarith [sq_nonneg s]
  have hc_ge : -1 ≤ c := by nlinarith [sq_nonneg s, sq_nonneg (c + 1)]
  have hs_sq : s ^ 2 = 1 - c ^ 2 := by linarith
  by_cases hs : 0 ≤ s
  · refine ⟨Real.arccos c, Real.cos_arccos hc_ge hc_le, ?_⟩
    rw [Real.sin_arccos, ← hs_sq, Real.sqrt_sq hs]
  · push Not at hs
    refine ⟨-Real.arccos c, ?_, ?_⟩
    · rw [Real.cos_neg, Real.cos_arccos hc_ge hc_le]
    · rw [Real.sin_neg, Real.sin_arccos, ← hs_sq, Real.sqrt_sq_eq_abs, abs_of_neg hs]
      ring

/-- A unit quaternion whose `imJ` and `imK` components vanish is `phase θ` for some `θ`. -/
theorem exists_phase_of_normSq_eq_one {u : ℍ} (hu : Quaternion.normSq u = 1)
    (hj : u.imJ = 0) (hk : u.imK = 0) : ∃ θ : ℝ, u = phase θ := by
  rw [Quaternion.normSq_def', hj, hk] at hu
  obtain ⟨θ, hcos, hsin⟩ := exists_cos_sin_of_sq_add_sq_eq_one (c := u.re) (s := u.imI) (by
    linarith)
  exact ⟨θ, by apply Quaternion.ext <;> simp [phase, hcos, hsin, hj, hk]⟩

/-- **Left invariance.** Multiplying on the left by a unit quaternion of the complex subfield
`ℝ + ℝi` leaves the Hopf image unchanged. Each of the three coordinates is a `linear_combination`
of the unit constraint `u.re² + u.imI² = 1`. -/
theorem hopfMap_mul_left {u q : ℍ} (hu : Quaternion.normSq u = 1)
    (hj : u.imJ = 0) (hk : u.imK = 0) : hopfMap (u * q) = hopfMap q := by
  have hu' : u.re ^ 2 + u.imI ^ 2 = 1 := by
    rw [Quaternion.normSq_def', hj, hk] at hu; linarith
  simp only [hopfMap, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, hj, hk, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (2 * (q.re * q.imJ + q.imI * q.imK)) * hu'
  · linear_combination (2 * (q.imI * q.imJ - q.re * q.imK)) * hu'
  · linear_combination (q.re ^ 2 + q.imI ^ 2 - q.imJ ^ 2 - q.imK ^ 2) * hu'

/-- The `phase θ` form of `hopfMap_mul_left`. -/
theorem hopfMap_phase_mul (θ : ℝ) (q : ℍ) : hopfMap (phase θ * q) = hopfMap q :=
  hopfMap_mul_left (phase_normSq θ) rfl rfl

/-- **Right multiplication is not invariance: it rotates.** Multiplying `q` on the *right* by
`phase θ` turns the first two coordinates of the Hopf image through the angle `2θ` and fixes the
third. This is the precise sense in which the left action of the circle is the one the Hopf map
quotients by; no unit hypothesis on `q` is needed. After `Real.cos_two_mul'` and
`Real.sin_two_mul` the first two coordinates are bare `ring` identities; only the third needs
`sin²θ + cos²θ = 1`, as a `linear_combination`. -/
theorem hopfMap_mul_phase (q : ℍ) (θ : ℝ) :
    hopfMap (q * phase θ) =
      ((hopfMap q).1 * Real.cos (2 * θ) - (hopfMap q).2.1 * Real.sin (2 * θ),
       (hopfMap q).1 * Real.sin (2 * θ) + (hopfMap q).2.1 * Real.cos (2 * θ),
       (hopfMap q).2.2) := by
  have hcs : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  simp only [hopfMap, phase, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, Real.cos_two_mul', Real.sin_two_mul, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · ring
  · ring
  · linear_combination (q.re ^ 2 + q.imI ^ 2 - q.imJ ^ 2 - q.imK ^ 2) * hcs

/-! ## The fibre is one circle orbit -/

/-- **The fibre theorem.** Two points of `S³` with the same Hopf image differ by a left factor
from the unit circle of `ℝ + ℝi`. With `hopfMap_mul_left` this says the preimage of a point of
`S²` is exactly one orbit of the left circle action.

The factor is written down explicitly: `u = ⟨c, s, 0, 0⟩` with
`c = p.re·q.re + p.imI·q.imI + p.imJ·q.imJ + p.imK·q.imK` and
`s = p.imI·q.re - p.re·q.imI + p.imK·q.imJ - p.imJ·q.imK`; the equality of Hopf images plus the
two unit constraints give `c² + s² = 1` and then `p = u * q` coordinate by coordinate. -/
theorem exists_mul_left_of_hopfMap_eq {p q : ℍ} (hp : Quaternion.normSq p = 1)
    (hq : Quaternion.normSq q = 1) (h : hopfMap p = hopfMap q) :
    ∃ u : ℍ, Quaternion.normSq u = 1 ∧ u.imJ = 0 ∧ u.imK = 0 ∧ p = u * q := by
  simp only [hopfMap, Prod.mk.injEq] at h
  obtain ⟨hx, hy, hz⟩ := h
  have hx' : p.re * p.imJ + p.imI * p.imK = q.re * q.imJ + q.imI * q.imK := by linarith
  have hy' : p.imI * p.imJ - p.re * p.imK = q.imI * q.imJ - q.re * q.imK := by linarith
  have hp' : p.re ^ 2 + p.imI ^ 2 + p.imJ ^ 2 + p.imK ^ 2 = 1 := by
    rw [Quaternion.normSq_def'] at hp; exact hp
  have hq' : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1 := by
    rw [Quaternion.normSq_def'] at hq; exact hq
  have hzz : p.re ^ 2 + p.imI ^ 2 = q.re ^ 2 + q.imI ^ 2 := by linarith
  have hww : p.imJ ^ 2 + p.imK ^ 2 = q.imJ ^ 2 + q.imK ^ 2 := by linarith
  set c : ℝ := p.re * q.re + p.imI * q.imI + p.imJ * q.imJ + p.imK * q.imK with hc_def
  set s : ℝ := p.imI * q.re - p.re * q.imI + p.imK * q.imJ - p.imJ * q.imK with hs_def
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    have key : c ^ 2 + s ^ 2
        = (p.re ^ 2 + p.imI ^ 2) * (q.re ^ 2 + q.imI ^ 2)
          + (p.imJ ^ 2 + p.imK ^ 2) * (q.imJ ^ 2 + q.imK ^ 2)
          + 2 * (p.re * p.imJ + p.imI * p.imK) * (q.re * q.imJ + q.imI * q.imK)
          + 2 * (p.imI * p.imJ - p.re * p.imK) * (q.imI * q.imJ - q.re * q.imK) := by
      rw [hc_def, hs_def]; ring
    rw [key, ← hx', ← hy', ← hzz, ← hww]
    nlinarith [hp']
  refine ⟨(⟨c, s, 0, 0⟩ : ℍ), ?_, rfl, rfl, ?_⟩
  · rw [Quaternion.normSq_def']
    simpa using hcs
  · apply Quaternion.ext
    · simp only [Quaternion.re_mul]
      rw [hc_def, hs_def]
      linear_combination p.imJ * hx' - p.imK * hy' + p.re * hzz - p.re * hp'
    · simp only [Quaternion.imI_mul]
      rw [hc_def, hs_def]
      linear_combination p.imK * hx' + p.imJ * hy' + p.imI * hzz - p.imI * hp'
    · simp only [Quaternion.imJ_mul]
      rw [hc_def, hs_def]
      linear_combination p.re * hx' + p.imI * hy' + p.imJ * hww - p.imJ * hp'
    · simp only [Quaternion.imK_mul]
      rw [hc_def, hs_def]
      linear_combination p.imI * hx' - p.re * hy' + p.imK * hww - p.imK * hp'

/-- The `phase θ` form of the fibre theorem. -/
theorem exists_phase_mul_of_hopfMap_eq {p q : ℍ} (hp : Quaternion.normSq p = 1)
    (hq : Quaternion.normSq q = 1) (h : hopfMap p = hopfMap q) :
    ∃ θ : ℝ, p = phase θ * q := by
  obtain ⟨u, hu, hj, hk, huq⟩ := exists_mul_left_of_hopfMap_eq hp hq h
  obtain ⟨θ, rfl⟩ := exists_phase_of_normSq_eq_one hu hj hk
  exact ⟨θ, huq⟩

/-! ## Surjectivity onto `S²` -/

/-- **The Hopf map is onto `S²`.** For every `(x, y, z)` with `x² + y² + z² = 1` there is a unit
quaternion mapping to it. The witness is explicit: for `z > -1` take
`q = a + c·j + d·k` with `a = √((1+z)/2)`, `c = x/√(2(1+z))`, `d = -y/√(2(1+z))`; for the
antipode `z = -1` the constraint forces `x = y = 0` and `q = j` works. -/
theorem hopfMap_surjective {x y z : ℝ} (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    ∃ q : ℍ, Quaternion.normSq q = 1 ∧ hopfMap q = (x, y, z) := by
  have hz_ge : -1 ≤ z := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (z + 1)]
  by_cases hz : z = -1
  · have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    refine ⟨(⟨0, 0, 1, 0⟩ : ℍ), ?_, ?_⟩
    · rw [Quaternion.normSq_def']; norm_num
    · simp [hopfMap, hx, hy, hz]
  · have hz_gt : -1 < z := lt_of_le_of_ne hz_ge (Ne.symm hz)
    have h1z_pos : (0 : ℝ) < 1 + z := by linarith
    have h2_1z_pos : (0 : ℝ) < 2 * (1 + z) := by linarith
    set a : ℝ := Real.sqrt ((1 + z) / 2) with ha_def
    set t : ℝ := Real.sqrt (2 * (1 + z)) with ht_def
    have ha_pos : 0 < a := Real.sqrt_pos.mpr (by linarith)
    have ht_pos : 0 < t := Real.sqrt_pos.mpr h2_1z_pos
    have ha_sq : a ^ 2 = (1 + z) / 2 := by
      rw [ha_def, sq, Real.mul_self_sqrt (by linarith)]
    have ht_sq : t ^ 2 = 2 * (1 + z) := by
      rw [ht_def, sq, Real.mul_self_sqrt (by linarith)]
    have h2a : 2 * a = t := by nlinarith [sq_nonneg (2 * a - t), sq_nonneg (2 * a + t)]
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    have hxy : x ^ 2 + y ^ 2 = 1 - z ^ 2 := by linarith
    have hc_sq : (x / t) ^ 2 = x ^ 2 / (2 * (1 + z)) := by rw [div_pow, ht_sq]
    have hd_sq : (-y / t) ^ 2 = y ^ 2 / (2 * (1 + z)) := by rw [div_pow, ht_sq]; ring_nf
    refine ⟨(⟨a, 0, x / t, -y / t⟩ : ℍ), ?_, ?_⟩
    · rw [Quaternion.normSq_def']
      simp only
      rw [ha_sq, hc_sq, hd_sq]
      field_simp
      nlinarith [hxy]
    · simp only [hopfMap, Prod.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · field_simp
        linear_combination x * h2a
      · field_simp
        linear_combination y * h2a
      · rw [ha_sq, hc_sq, hd_sq]
        field_simp
        nlinarith [hxy, sq_nonneg (1 + z)]

/-! ## Concrete instances -/

/-- `1` maps to the north pole `(0, 0, 1)`. -/
example : hopfMap 1 = (0, 0, 1) := by
  simp [hopfMap]

/-- `j` maps to the south pole `(0, 0, -1)`, so the two poles are both attained. -/
example : hopfMap (⟨0, 0, 1, 0⟩ : ℍ) = (0, 0, -1) := by
  simp [hopfMap]

/-- `(1 + j)/√2` is a unit quaternion, and it maps to a point of the equator. The unitness is part
of the statement, so the word "unit" is carried by the proof and not by the caption. -/
example :
    Quaternion.normSq (⟨Real.sqrt 2 / 2, 0, Real.sqrt 2 / 2, 0⟩ : ℍ) = 1 ∧
      hopfMap (⟨Real.sqrt 2 / 2, 0, Real.sqrt 2 / 2, 0⟩ : ℍ) = (1, 0, 0) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [Quaternion.normSq_def']
    nlinarith [h2]
  · simp only [hopfMap, Prod.mk.injEq]
    refine ⟨by nlinarith [h2], by ring, by nlinarith [h2]⟩

end ClassicalLean.Geometry
