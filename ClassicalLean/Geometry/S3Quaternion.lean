/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.Convex.StdSimplex
import ClassicalLean.Simplex.Basic
import ClassicalLean.Simplex.SecondOrder

/-!
# The unit quaternions and the 3-sphere

The unit quaternions form the 3-sphere `S³` inside `ℍ = ℍ[ℝ]`, and they are a group under
quaternion multiplication. Both halves of that sentence are already in Mathlib, in two different
languages: `Metric.sphere (0 : ℍ) 1` carries a `Group` instance
(`Metric.unitSphere.instGroup`, for any `NormedDivisionRing`), and `unitary ℍ` is a group too —
Mathlib gives `unitary R` a `Group` instance for every star monoid `R`, in
`Mathlib/Algebra/Star/Unitary.lean`. What is *not* in Mathlib is the dictionary saying that these
two descriptions and the elementary one — "the sum of the four squared components is `1`" — pick
out the same set of quaternions.

This file is that dictionary, plus the closure and inverse facts one wants when working with the
elementary description directly, plus the map that sends a quaternion to its four squared
components and lands, on `S³`, in the standard 3-simplex.

Everything below is stated for `q : ℍ` with a hypothesis `Quaternion.normSq q = 1` rather than on
a subtype, so no new type of "unit quaternion" is introduced here: the group structure is
Mathlib's, reached through `normSq_eq_one_iff_mem_sphere` or `normSq_eq_one_iff_mem_unitary`.

Mathlib's `Quaternion ℝ` is a `def`, not an `abbrev`, and its `Zero`/`One`/`Neg` arguments make
instance search on `ℍ` sensitive to transparency; `set_option backward.isDefEq.respectTransparency
false` is the workaround Mathlib itself uses in `Mathlib/Analysis/Quaternion.lean`, and any file
that uses these declarations on `ℍ` will want it too.
Superseded 2026-09-23: builds without the option at v4.34.0 (round 19).
Corrected 2026-09-24 (order G-7, round 23): at v4.34.0 `Quaternion` is an `abbrev`
(`Mathlib/Algebra/Quaternion.lean:684`), not a `def`, and `Mathlib/Analysis/Quaternion.lean`
does not set that option (`respectTransparency` 0 matches).

**Dated 2026-09-24 (order G-7, J2 step 3; round 23):** `sqCoords` is the squaring map at the four
coordinates, written with Mathlib's `Quaternion.equivTuple ℝ q = ![q.re, q.imI, q.imJ, q.imK]`
(`sqCoords_eq_equivTuple_sq`), so `Simplex/SecondOrder`'s squaring-map identity applies to it: at
a quaternion with no zero coordinate the Fisher–Rao metric at `sqCoords q` is four times the
Euclidean one (`fisherRao_sqCoords`). This file now imports `Simplex/SecondOrder`.

**What the source file `S3Quaternion.lean` had, and where it went.** One line per source
declaration, so that a drop is a decision on the record rather than a silence.

* `UnitQuat` (a structure bundling a quaternion with a proof that its `normSq` is `1`), and the
  operations `mul_uq`, `conj_uq`, `one_uq` on it — dropped: replaced by a bare `q : ℍ` carrying the
  hypothesis, as the paragraph above explains, so the group structure is Mathlib's. Every theorem
  stated about the subtype is restated about the hypothesis.
* `normSq_expand` (`normSq q = re² + imI² + imJ² + imK²`) — dropped: it is Mathlib's
  `Quaternion.normSq_def'`, which the source itself uses to prove it.
* `quaternion_conservation` (for a unit `q`, the four squares sum to `1`) — shipped as the forward
  direction of `normSq_eq_one_iff_sq_add`, which states both directions.
* `s3_mul_closed`, `s3_conj_closed`, `uq_mul_conj` — shipped as `normSq_mul_eq_one`,
  `normSq_star_eq_one` and `mul_star_eq_one` (with `star_mul_eq_one` added on the other side).
* `toSimplex`, `toSimplex_conserved`, `toSimplex_nonneg` — shipped merged as `sqCoords₃` and
  `sqCoords₃_mem_closedSimplex`, membership in `Simplex.closedSimplex` replacing the source's
  separate sum and nonnegativity statements; `sqCoords` and `sqCoords_mem_closedSimplex` are the
  unmerged four-coordinate version, which the source did not have.
* `one_uq` (the unit quaternion `1`) — dropped: the underlying fact `normSq (1 : ℍ) = 1` is
  Mathlib's `map_one`, checked in the first `example` below rather than named as a theorem.
-/

open scoped Quaternion

namespace ClassicalLean.Geometry

/-! ## The three descriptions of `S³` -/

/-- A quaternion has `normSq = 1` exactly when it lies on the unit sphere of `ℍ`. This is the
bridge to Mathlib's group structure on the unit sphere of a normed division ring
(`Metric.unitSphere.instGroup`): via this equivalence, the unit quaternions are a group, and that
group structure is Mathlib's, not one built here. Proved from `Quaternion.normSq_eq_norm_mul_self`
and `mem_sphere_zero_iff_norm`. -/
theorem normSq_eq_one_iff_mem_sphere (q : ℍ) :
    Quaternion.normSq q = 1 ↔ q ∈ Metric.sphere (0 : ℍ) 1 := by
  rw [mem_sphere_zero_iff_norm, Quaternion.normSq_eq_norm_mul_self]
  constructor
  · intro h
    rcases mul_self_eq_one_iff.mp h with h1 | h1
    · exact h1
    · exact absurd h1 (by linarith [norm_nonneg q])
  · intro h
    rw [h, mul_one]

/-- A quaternion has `normSq = 1` exactly when it is unitary, i.e. `star q * q = q * star q = 1`.
This is the bridge to Mathlib's `unitary ℍ`, which carries a `Group` instance from
`Mathlib/Algebra/Star/Unitary.lean`. Proved from `Quaternion.star_mul_self` and
`Quaternion.self_mul_star`. -/
theorem normSq_eq_one_iff_mem_unitary (q : ℍ) :
    Quaternion.normSq q = 1 ↔ q ∈ unitary ℍ := by
  rw [Unitary.mem_iff, Quaternion.star_mul_self, Quaternion.self_mul_star]
  constructor
  · intro h
    rw [h]
    exact ⟨Quaternion.coe_one, Quaternion.coe_one⟩
  · rintro ⟨h, -⟩
    simpa using congrArg (fun x : ℍ => x.re) h

/-- The elementary description: `normSq q = 1` says the four real components of `q` have squares
summing to `1`, which is the equation of the 3-sphere in `ℝ⁴`. One rewrite by Mathlib's
`Quaternion.normSq_def'`. -/
theorem normSq_eq_one_iff_sq_add (q : ℍ) :
    Quaternion.normSq q = 1 ↔ q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1 := by
  rw [Quaternion.normSq_def']

/-! ## Closure, conjugate and inverse

These restate, for the elementary description, what the group structure above already gives; they
are the form one actually rewrites with when carrying a hypothesis `normSq q = 1` around.

`normSq (1 : ℍ) = 1` is *not* among them: it is Mathlib's `map_one` applied to `Quaternion.normSq`
and nothing else, so naming it here would add a constant without adding a proof. It is checked
below, inside the first `example`. -/

/-- The product of two unit quaternions is a unit quaternion: `normSq` is multiplicative
(`map_mul`). -/
theorem normSq_mul_eq_one {p q : ℍ} (hp : Quaternion.normSq p = 1)
    (hq : Quaternion.normSq q = 1) : Quaternion.normSq (p * q) = 1 := by
  rw [map_mul, hp, hq, mul_one]

/-- The conjugate of a unit quaternion is a unit quaternion, by `Quaternion.normSq_star`. -/
theorem normSq_star_eq_one {q : ℍ} (hq : Quaternion.normSq q = 1) :
    Quaternion.normSq (star q) = 1 := by
  rw [Quaternion.normSq_star, hq]

/-- The negative of a unit quaternion is a unit quaternion, by `Quaternion.normSq_neg`. This is
the antipodal map on `S³`. -/
theorem normSq_neg_eq_one {q : ℍ} (hq : Quaternion.normSq q = 1) :
    Quaternion.normSq (-q) = 1 := by
  rw [Quaternion.normSq_neg, hq]

/-- A unit quaternion is right-inverted by its conjugate. -/
theorem mul_star_eq_one {q : ℍ} (hq : Quaternion.normSq q = 1) : q * star q = 1 := by
  rw [Quaternion.self_mul_star, hq, Quaternion.coe_one]

/-- A unit quaternion is left-inverted by its conjugate. -/
theorem star_mul_eq_one {q : ℍ} (hq : Quaternion.normSq q = 1) : star q * q = 1 := by
  rw [Quaternion.star_mul_self, hq, Quaternion.coe_one]

/-- On the unit quaternions the inverse of `ℍ` as a division ring *is* the conjugate. Immediate
from Mathlib's `Quaternion.inv_def`, which defines `q⁻¹` as `(normSq q)⁻¹ • star q`. -/
theorem inv_eq_star {q : ℍ} (hq : Quaternion.normSq q = 1) : q⁻¹ = star q := by
  rw [Quaternion.inv_def, hq, inv_one, one_smul]

/-! ## The squared-component map

Sending `q` to the four squares `(re², imI², imJ², imK²)` maps `S³` onto its coordinate-wise
image in the standard 3-simplex. Only membership is proved below; that the map is *onto* the
simplex is true and classical (take square roots), but it is not proved here. Context, not proved
here: this is the moment map of the coordinate torus action on `S³`. -/

/-- The four squared components of a quaternion, as a point of `Fin 4 → ℝ`. -/
noncomputable def sqCoords (q : ℍ) : Fin 4 → ℝ :=
  ![q.re ^ 2, q.imI ^ 2, q.imJ ^ 2, q.imK ^ 2]

/-- On `S³` the four squared components are non-negative and sum to `1`: they form a point of
the closed simplex `Simplex.closedSimplex (Fin 4)`. -/
theorem sqCoords_mem_closedSimplex {q : ℍ} (hq : Quaternion.normSq q = 1) :
    sqCoords q ∈ Simplex.closedSimplex (Fin 4) := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> exact sq_nonneg _
  · rw [Fin.sum_univ_four]
    change q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1
    exact (normSq_eq_one_iff_sq_add q).mp hq

/-- `sqCoords` is the squaring map at the quaternion's four coordinates, written with Mathlib's
`Quaternion.equivTuple` (`![q.re, q.imI, q.imJ, q.imK]`). -/
theorem sqCoords_eq_equivTuple_sq (q : ℍ) :
    sqCoords q = fun i => Quaternion.equivTuple ℝ q i ^ 2 := by
  funext i
  fin_cases i <;> rfl

/-- The Fisher–Rao metric at `sqCoords q` is four times the Euclidean one, for `q` with no zero
coordinate: the instance of `Simplex.fisherRao_sq_two_mul_of_ne_zero` at the four coordinates. -/
theorem fisherRao_sqCoords {q : ℍ} (hq : ∀ i, Quaternion.equivTuple ℝ q i ≠ 0)
    (v w : Fin 4 → ℝ) :
    Simplex.fisherRao (sqCoords q) (fun i => 2 * Quaternion.equivTuple ℝ q i * v i)
      (fun i => 2 * Quaternion.equivTuple ℝ q i * w i) = 4 * (v ⬝ᵥ w) := by
  rw [sqCoords_eq_equivTuple_sq]
  exact Simplex.fisherRao_sq_two_mul_of_ne_zero hq v w

/-- The coarsening of `sqCoords` that merges the first two coordinates: `(re² + imI², imJ², imK²)`.
The grouping is a choice, not a theorem: `re² + imI²` is the squared modulus of the complex number
`re + imI·i` obtained by writing `q = z + w·j`. -/
noncomputable def sqCoords₃ (q : ℍ) : Fin 3 → ℝ :=
  ![q.re ^ 2 + q.imI ^ 2, q.imJ ^ 2, q.imK ^ 2]

/-- On `S³` the three merged coordinates are non-negative and sum to `1`: a point of
`Simplex.closedSimplex (Fin 3)`. -/
theorem sqCoords₃_mem_closedSimplex {q : ℍ} (hq : Quaternion.normSq q = 1) :
    sqCoords₃ q ∈ Simplex.closedSimplex (Fin 3) := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i
    · change (0 : ℝ) ≤ q.re ^ 2 + q.imI ^ 2
      positivity
    · exact sq_nonneg _
    · exact sq_nonneg _
  · rw [Fin.sum_univ_three]
    change q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1
    exact (normSq_eq_one_iff_sq_add q).mp hq

/-! ## Concrete instances -/

/-- The four basis quaternions `1, i, j, k` all lie on `S³`. -/
example :
    Quaternion.normSq (1 : ℍ) = 1 ∧ Quaternion.normSq (⟨0, 1, 0, 0⟩ : ℍ) = 1 ∧
      Quaternion.normSq (⟨0, 0, 1, 0⟩ : ℍ) = 1 ∧ Quaternion.normSq (⟨0, 0, 0, 1⟩ : ℍ) = 1 := by
  refine ⟨map_one _, ?_, ?_, ?_⟩ <;> rw [Quaternion.normSq_def'] <;> norm_num

/-- A unit quaternion with all four components equal: `(1, 1, 1, 1)/2`. -/
example : Quaternion.normSq (⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩ : ℍ) = 1 := by
  rw [Quaternion.normSq_def']
  norm_num

end ClassicalLean.Geometry
