/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.Quaternion
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Unit quaternions as SU(2), and their action on the imaginary quaternions

Two representations of the unit quaternions by matrices, and the relation between them.

**As 2×2 complex matrices.** Writing `q = z + w·j` with `z = re + imI·i` and `w = imJ + imK·i`,
the assignment

`q ↦ !![z, w; -conj w, conj z]`

is `su2` below. It is multiplicative, its determinant is `normSq q`, and `A · Aᴴ = normSq q · I`.
So a *unit* quaternion goes to a matrix of `Matrix.specialUnitaryGroup (Fin 2) ℂ`, and the map is
injective and — `exists_su2_eq` — onto that group. Multiplicativity, `su2_one`, injectivity and
surjectivity onto SU(2) are together the content of the classical isomorphism between the unit
quaternions and SU(2); the bundled `MulEquiv` is not constructed here, so no declaration below is
named or phrased as one. The point of proving them is that SU(2) here is Mathlib's group of
unitary complex 2×2 matrices of determinant `1`, not a second copy of the quaternions.

**As 3×3 real matrices.** Conjugation `v ↦ q·v·star q` (`adjoint`) scales the real part by
`normSq q` and `normSq` by `(normSq q)²`, so a *unit* quaternion fixes the real part and preserves
`normSq`; on the three imaginary coordinates it acts by a real 3×3 matrix, `adjointMatrix`.
That matrix satisfies `A · Aᵀ = (normSq q)²·I` and `det A = (normSq q)³`, so for a unit quaternion
it lies in `Matrix.specialOrthogonalGroup (Fin 3) ℝ`. The map is exactly two-to-one, and "exactly"
is proved in three steps: `adjoint_neg` says `q` and `-q` act identically; `adjoint_eq_iff` (with
its matrix form `adjointMatrix_eq_iff`) says those are the *only* coincidences, so each fibre is
contained in `{q, -q}`; and `ne_neg_self_of_normSq_eq_one` says a unit quaternion is never its own
negative, so that pair really has two elements. `adjointMatrix_fibre` puts the first two together
as a set equality and `adjointMatrix_fibre_ncard` records the count as `2`.

What is **not** proved here: that `q ↦ adjointMatrix q` is onto `SO(3)`. Surjectivity is classical
and true, and without it the phrase "double cover of SO(3)" is not established by this file; what
is established is that the image lies in `SO(3)` and that the map is exactly two-to-one onto its
image. No statement below claims more.

Mathlib's `Quaternion ℝ` needs `set_option backward.isDefEq.respectTransparency false` for
instance search on `ℍ`, as in `Mathlib/Analysis/Quaternion.lean`.
Superseded 2026-09-23: builds without the option at v4.34.0 (round 19).

**What the source file `SU2_S3_Iso.lean` had, and where it went.** One line per source
declaration, so that a drop is a decision on the record rather than a silence.

* `UnitQuat` and its operations `mul_uq`, `one_uq`, `inv_uq` — dropped: as in
  `ClassicalLean.Geometry.S3Quaternion`, a unit quaternion is a `q : ℍ` with the hypothesis
  `normSq q = 1`, and the group structure is Mathlib's.
* `mul_assoc_uq`, `mul_one_uq`, `one_mul_uq` — dropped: they are the monoid axioms for the source's
  own subtype. On `ℍ` they are Mathlib's `mul_assoc`, `mul_one` and `one_mul`, and on the unit
  quaternions they come with the `Group` instance that
  `ClassicalLean.Geometry.normSq_eq_one_iff_mem_sphere` and `…_iff_mem_unitary` reach.
* `mul_inv_uq`, `inv_mul_uq` — shipped in `S3Quaternion.lean` as `mul_star_eq_one`,
  `star_mul_eq_one` and `inv_eq_star`, which also identify the inverse with the conjugate.
* `SU2Mat` (a bare structure of four reals with a `unit` field) and `su2_mul` (a hand-written
  quadruple product) — dropped: `su2` below lands in `Matrix (Fin 2) (Fin 2) ℂ` and `su2_mul` is
  the genuine matrix product, so the target of the map is Mathlib's SU(2) and not a second copy of
  the quaternions.
* `uq_to_su2` — shipped as `su2`. `uq_to_su2_hom` — shipped as `su2_mul`.
* `su2_to_uq`, `su2_roundtrip_uq` — dropped: the source's inverse map and its round-trip identity,
  which is a projection identity closed by unfolding. What replaces them is stronger and does not
  need a hand-built inverse: `su2_injective` plus `exists_su2_eq`, the latter proving that every
  element of `Matrix.specialUnitaryGroup (Fin 2) ℂ` is hit — a statement the source does not have.
* `adjoint_action` — shipped as `adjoint`. `adjoint_action_hom` — shipped as `adjoint_mul`.
* `double_cover_adjoint` — shipped as `adjoint_neg`.
* `adjoint_preserves_pure`, `adjoint_preserves_normSq` — shipped strengthened as `adjoint_re` and
  `adjoint_normSq`, both without the unit hypothesis; the source statements are the `normSq q = 1`
  specialisations.
* `su2_double_covers_so3` — shipped strengthened as `adjoint_eq_self_iff`, an `iff` where the source
  proved one direction.
-/

open scoped Quaternion Matrix

namespace ClassicalLean.Geometry

/-! ## The 2×2 complex representation -/

/-- The 2×2 complex matrix of a quaternion `q = z + w·j`, namely `!![z, w; -conj w, conj z]`,
written out in the four real components. -/
noncomputable def su2 (q : ℍ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(⟨q.re, q.imI⟩ : ℂ), (⟨q.imJ, q.imK⟩ : ℂ);
     (⟨-q.imJ, q.imK⟩ : ℂ), (⟨q.re, -q.imI⟩ : ℂ)]

/-- `su2` sends `1` to the identity matrix. -/
theorem su2_one : su2 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [su2]

/-- **`su2` is multiplicative.** Entry by entry this is the quaternion multiplication table
rewritten as a complex 2×2 product. -/
theorem su2_mul (p q : ℍ) : su2 (p * q) = su2 p * su2 q := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [su2, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;> ring

/-- **The determinant is the squared norm.** `det (su2 q) = normSq q`, as a complex number. -/
theorem su2_det (q : ℍ) : (su2 q).det = ((Quaternion.normSq q : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two, Quaternion.normSq_def']
  apply Complex.ext <;>
    simp [su2, Complex.mul_re, Complex.mul_im, -Complex.ofReal_pow] <;> ring

/-- **The matrix is unitary up to the squared norm.** `su2 q · (su2 q)ᴴ = normSq q · I`. -/
theorem su2_mul_star (q : ℍ) :
    su2 q * star (su2 q) = ((Quaternion.normSq q : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Quaternion.normSq_def']
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [su2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im,
      -Complex.ofReal_pow] <;> ring

/-- `su2` is injective: the four real components are read straight off the first row. -/
theorem su2_injective : Function.Injective su2 := by
  intro p q h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  simp only [su2] at h00 h01
  apply Quaternion.ext
  · exact congrArg Complex.re h00
  · exact congrArg Complex.im h00
  · exact congrArg Complex.re h01
  · exact congrArg Complex.im h01

/-- **A unit quaternion lands in SU(2).** For `normSq q = 1`, `su2 q` is unitary with determinant
`1`, i.e. a member of Mathlib's `Matrix.specialUnitaryGroup (Fin 2) ℂ`. -/
theorem su2_mem_specialUnitaryGroup {q : ℍ} (hq : Quaternion.normSq q = 1) :
    su2 q ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, su2_mul_star, hq]
    simp
  · rw [su2_det, hq, Complex.ofReal_one]

/-- **Every element of SU(2) is `su2` of a unit quaternion.** The proof identifies the entries:
for `A` unitary with `det A = 1`, `Aᴴ = A⁻¹ = adjugate A`, which forces
`A 1 1 = conj (A 0 0)` and `A 1 0 = -conj (A 0 1)`; the quaternion is then read off the first
row. With `su2_injective`, `su2_mul` and `su2_one` this identifies the unit quaternions with
SU(2) as groups. -/
theorem exists_su2_eq {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ q : ℍ, Quaternion.normSq q = 1 ∧ su2 q = A := by
  obtain ⟨hu, hdet⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hA
  have hinv : A⁻¹ = star A := Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.mp hu)
  have hadj : star A = A.adjugate := by
    rw [← hinv, Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  rw [Matrix.adjugate_fin_two] at hadj
  have h11 : A 1 1 = (starRingEnd ℂ) (A 0 0) := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hadj
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] using h.symm
  have h10 : A 1 0 = -(starRingEnd ℂ) (A 0 1) := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) hadj
    simp at h
    linear_combination h
  refine ⟨(⟨(A 0 0).re, (A 0 0).im, (A 0 1).re, (A 0 1).im⟩ : ℍ), ?_, ?_⟩
  · rw [Matrix.det_fin_two, h11, h10] at hdet
    have hre := congrArg Complex.re hdet
    have hre2 : (A 0 0).re * (A 0 0).re + (A 0 0).im * (A 0 0).im
        + ((A 0 1).re * (A 0 1).re + (A 0 1).im * (A 0 1).im) = 1 := by
      simpa [Complex.mul_re] using hre
    rw [Quaternion.normSq_def']
    linear_combination hre2
  · ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [su2, h11, h10]

/-! ## The action on the imaginary quaternions -/

/-- Conjugation by `q`: the map `v ↦ q · v · star q` on `ℍ`. -/
noncomputable def adjoint (q v : ℍ) : ℍ := q * v * star q

/-- Conjugation scales the real part by `normSq q`; in particular a unit quaternion fixes it, so
conjugation by a unit quaternion preserves the subspace of imaginary quaternions. -/
theorem adjoint_re (q v : ℍ) : (adjoint q v).re = Quaternion.normSq q * v.re := by
  simp [adjoint, Quaternion.normSq_def']
  ring

/-- Conjugation scales `normSq` by `(normSq q)²`, so for `normSq q = 1` it preserves `normSq`.
Since `Quaternion.normSq_eq_norm_mul_self` gives `normSq v = ‖v‖²`, that is the statement that a
unit quaternion conjugates by a norm-preserving map. Proved from multiplicativity of `normSq`
(`map_mul`) and `Quaternion.normSq_star`. -/
theorem adjoint_normSq (q v : ℍ) :
    Quaternion.normSq (adjoint q v) = Quaternion.normSq q ^ 2 * Quaternion.normSq v := by
  simp only [adjoint, map_mul, Quaternion.normSq_star]
  ring

/-- Conjugation is a left action: `adjoint (p * q) = adjoint p ∘ adjoint q`. -/
theorem adjoint_mul (p q v : ℍ) : adjoint (p * q) v = adjoint p (adjoint q v) := by
  simp only [adjoint, star_mul, mul_assoc]

/-- **`q` and `-q` act identically.** This is the two-to-one-ness of the action. -/
theorem adjoint_neg (q v : ℍ) : adjoint (-q) v = adjoint q v := by
  simp [adjoint]

/-- **The kernel of the action is `{±1}`.** A unit quaternion that conjugates every quaternion to
itself is `1` or `-1`. The proof turns the fixed-point condition into the commutation
`q · v = v · q` for all `v`, evaluates it at `i` and `j` to kill the three imaginary components,
and then reads `q.re² = 1` off `normSq q = 1`. -/
theorem adjoint_eq_self_iff {q : ℍ} (hq : Quaternion.normSq q = 1) :
    (∀ v : ℍ, adjoint q v = v) ↔ q = 1 ∨ q = -1 := by
  constructor
  · intro h
    have hstar : star q * q = 1 := by
      rw [Quaternion.star_mul_self, hq, Quaternion.coe_one]
    have comm : ∀ v : ℍ, q * v = v * q := fun v => by
      have hv : q * v * star q = v := h v
      calc q * v = q * v * 1 := (mul_one _).symm
        _ = q * v * (star q * q) := by rw [hstar]
        _ = q * v * star q * q := by rw [← mul_assoc]
        _ = v * q := by rw [hv]
    have hi := comm (⟨0, 1, 0, 0⟩ : ℍ)
    have hj := comm (⟨0, 0, 1, 0⟩ : ℍ)
    have hK : q.imK = 0 := by
      have hc := congrArg (fun x : ℍ => x.imJ) hi
      simp at hc
      linarith
    have hJ : q.imJ = 0 := by
      have hc := congrArg (fun x : ℍ => x.imK) hi
      simp at hc
      linarith
    have hI : q.imI = 0 := by
      have hc := congrArg (fun x : ℍ => x.imK) hj
      simp at hc
      linarith
    rw [Quaternion.normSq_def', hI, hJ, hK] at hq
    have hfac : (q.re - 1) * (q.re + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with hr | hr
    · have hr2 : q.re = 1 := by linarith
      exact Or.inl (Quaternion.ext _ _ (by simp [hr2]) (by simp [hI]) (by simp [hJ])
        (by simp [hK]))
    · have hr2 : q.re = -1 := by linarith
      exact Or.inr (Quaternion.ext _ _ (by simp [hr2]) (by simp [hI]) (by simp [hJ])
        (by simp [hK]))
  · rintro (rfl | rfl) <;> intro v <;> simp [adjoint]

/-- **Exactly two unit quaternions per action.** Two unit quaternions conjugate every quaternion
the same way if and only if they are equal or opposite. This is `adjoint_eq_self_iff` transported
along the group law, and it is the precise two-to-one statement: it says `adjoint_neg` exhausts
the coincidences. -/
theorem adjoint_eq_iff {p q : ℍ} (hp : Quaternion.normSq p = 1) (hq : Quaternion.normSq q = 1) :
    (∀ v : ℍ, adjoint p v = adjoint q v) ↔ p = q ∨ p = -q := by
  have hqs : star q * q = 1 := by rw [Quaternion.star_mul_self, hq, Quaternion.coe_one]
  have hqm : q * star q = 1 := by rw [Quaternion.self_mul_star, hq, Quaternion.coe_one]
  constructor
  · intro h
    have hu : Quaternion.normSq (star q * p) = 1 := by
      rw [map_mul, Quaternion.normSq_star, hq, hp, mul_one]
    have hid : ∀ v : ℍ, adjoint (star q * p) v = v := by
      intro v
      have e1 : adjoint (star q * p) v = star q * adjoint p v * q := by
        simp only [adjoint, star_mul, star_star, mul_assoc]
      rw [e1, h v]
      have e2 : star q * adjoint q v * q = star q * q * v * (star q * q) := by
        simp only [adjoint, mul_assoc]
      rw [e2, hqs, one_mul, mul_one]
    rcases (adjoint_eq_self_iff hu).mp hid with h1 | h1
    · left
      have e : q * (star q * p) = q * 1 := by rw [h1]
      rwa [← mul_assoc, hqm, one_mul, mul_one] at e
    · right
      have e : q * (star q * p) = q * -1 := by rw [h1]
      rwa [← mul_assoc, hqm, one_mul, mul_neg_one] at e
  · rintro (rfl | rfl) <;> intro v
    · rfl
    · exact adjoint_neg q v

/-- **A unit quaternion is not its own negative.** If all four components of `q` vanish then
`normSq q = 0`, so `q = -q` is incompatible with `normSq q = 1`. This is the step that turns
`adjoint_eq_iff`'s fibre `{q, -q}` from "at most two" into "exactly two". -/
theorem ne_neg_self_of_normSq_eq_one {q : ℍ} (hq : Quaternion.normSq q = 1) : q ≠ -q := by
  intro h
  have hre : q.re = 0 := by
    have h' := congrArg (fun x : ℍ => x.re) h
    simp only [Quaternion.re_neg] at h'
    linarith
  have hI : q.imI = 0 := by
    have h' := congrArg (fun x : ℍ => x.imI) h
    simp only [Quaternion.imI_neg] at h'
    linarith
  have hJ : q.imJ = 0 := by
    have h' := congrArg (fun x : ℍ => x.imJ) h
    simp only [Quaternion.imJ_neg] at h'
    linarith
  have hK : q.imK = 0 := by
    have h' := congrArg (fun x : ℍ => x.imK) h
    simp only [Quaternion.imK_neg] at h'
    linarith
  rw [Quaternion.normSq_def', hre, hI, hJ, hK] at hq
  norm_num at hq

/-! ## The 3×3 real matrix of the action -/

/-- The real 3×3 matrix by which `adjoint q` acts on the three imaginary coordinates. Its entries
are the standard quadratic expressions in the four components of `q`; `adjointMatrix_mulVec`
proves that it really is that matrix. -/
noncomputable def adjointMatrix (q : ℍ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![q.re ^ 2 + q.imI ^ 2 - q.imJ ^ 2 - q.imK ^ 2,
       2 * (q.imI * q.imJ - q.re * q.imK), 2 * (q.imI * q.imK + q.re * q.imJ);
     2 * (q.imI * q.imJ + q.re * q.imK),
       q.re ^ 2 - q.imI ^ 2 + q.imJ ^ 2 - q.imK ^ 2, 2 * (q.imJ * q.imK - q.re * q.imI);
     2 * (q.imI * q.imK - q.re * q.imJ),
       2 * (q.imJ * q.imK + q.re * q.imI), q.re ^ 2 - q.imI ^ 2 - q.imJ ^ 2 + q.imK ^ 2]

/-- **The matrix implements the action.** Applying `adjointMatrix q` to the imaginary coordinates
of `v` gives the imaginary coordinates of `adjoint q v`. No unit hypothesis is needed: the real
part of `v` contributes only to the real part of `adjoint q v` (`adjoint_re`). -/
theorem adjointMatrix_mulVec (q v : ℍ) :
    (adjointMatrix q).mulVec ![v.imI, v.imJ, v.imK]
      = ![(adjoint q v).imI, (adjoint q v).imJ, (adjoint q v).imK] := by
  funext i
  fin_cases i <;>
    simp [adjointMatrix, adjoint, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- `A · Aᵀ = (normSq q)² · I`: the matrix is orthogonal up to the square of the norm. Nine
`ring` identities, each an instance of the four-square identity. -/
theorem adjointMatrix_mul_transpose (q : ℍ) :
    adjointMatrix q * (adjointMatrix q)ᵀ = (Quaternion.normSq q ^ 2) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adjointMatrix, Matrix.mul_apply, Fin.sum_univ_three, Quaternion.normSq_def'] <;> ring

/-- `det A = (normSq q)³`: a degree-6 polynomial identity in the four components. -/
theorem adjointMatrix_det (q : ℍ) :
    (adjointMatrix q).det = Quaternion.normSq q ^ 3 := by
  rw [Matrix.det_fin_three, Quaternion.normSq_def']
  simp [adjointMatrix]
  ring

/-- **A unit quaternion gives a rotation.** For `normSq q = 1` the matrix `adjointMatrix q` is
orthogonal with determinant `1`, i.e. a member of Mathlib's
`Matrix.specialOrthogonalGroup (Fin 3) ℝ`. That every rotation arises this way — surjectivity —
is classical but is *not* proved here. -/
theorem adjointMatrix_mem_specialOrthogonalGroup {q : ℍ} (hq : Quaternion.normSq q = 1) :
    adjointMatrix q ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff, adjointMatrix_mul_transpose, hq]
    simp
  · rw [adjointMatrix_det, hq, one_pow]

/-- `q` and `-q` have the same matrix, matching `adjoint_neg`. -/
theorem adjointMatrix_neg (q : ℍ) : adjointMatrix (-q) = adjointMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adjointMatrix]

/-- **The matrix form of the two-to-one statement.** Two unit quaternions have the same rotation
matrix exactly when they are equal or opposite. The forward direction reads the action off the
matrix with `adjointMatrix_mulVec` (the real part is handled by `adjoint_re` and the two unit
hypotheses) and then applies `adjoint_eq_iff`. -/
theorem adjointMatrix_eq_iff {p q : ℍ} (hp : Quaternion.normSq p = 1)
    (hq : Quaternion.normSq q = 1) :
    adjointMatrix p = adjointMatrix q ↔ p = q ∨ p = -q := by
  constructor
  · intro h
    refine (adjoint_eq_iff hp hq).mp fun v => ?_
    have hv := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M.mulVec ![v.imI, v.imJ, v.imK]) h
    simp only [adjointMatrix_mulVec] at hv
    apply Quaternion.ext
    · rw [adjoint_re, adjoint_re, hp, hq]
    · exact congrArg (fun w : Fin 3 → ℝ => w 0) hv
    · exact congrArg (fun w : Fin 3 → ℝ => w 1) hv
    · exact congrArg (fun w : Fin 3 → ℝ => w 2) hv
  · rintro (rfl | rfl)
    · rfl
    · exact adjointMatrix_neg q

/-- **The fibre, as a set.** The unit quaternions carrying the same rotation matrix as a given
unit `q` are exactly `q` and `-q`. This is `adjointMatrix_eq_iff` written as a set equality. -/
theorem adjointMatrix_fibre {q : ℍ} (hq : Quaternion.normSq q = 1) :
    {p : ℍ | Quaternion.normSq p = 1 ∧ adjointMatrix p = adjointMatrix q} = {q, -q} := by
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hp, hpq⟩
    exact (adjointMatrix_eq_iff hp hq).mp hpq
  · rintro (rfl | rfl)
    · exact ⟨hq, rfl⟩
    · exact ⟨by rw [Quaternion.normSq_neg]; exact hq, adjointMatrix_neg q⟩

/-- **Exactly two, not at most two.** The fibre through a unit quaternion has exactly two elements.
`adjointMatrix_fibre` identifies it with `{q, -q}` and `ne_neg_self_of_normSq_eq_one` says those two
are distinct; without the second, `{q, -q}` would bound the fibre above by two without pinning it
down, and the phrase "two-to-one" would not be earned. -/
theorem adjointMatrix_fibre_ncard {q : ℍ} (hq : Quaternion.normSq q = 1) :
    {p : ℍ | Quaternion.normSq p = 1 ∧ adjointMatrix p = adjointMatrix q}.ncard = 2 := by
  rw [adjointMatrix_fibre hq, Set.ncard_pair (ne_neg_self_of_normSq_eq_one hq)]

/-! ## Concrete instances -/

/-- `su2 i` is the Pauli-type matrix `!![i, 0; 0, -i]`. -/
example : su2 (⟨0, 1, 0, 0⟩ : ℍ) = !![Complex.I, 0; 0, -Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [su2]

/-- Conjugation by `i` is the rotation by `π` about the first axis: `diag(1, -1, -1)`. -/
example : adjointMatrix (⟨0, 1, 0, 0⟩ : ℍ) = !![(1 : ℝ), 0, 0; 0, -1, 0; 0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [adjointMatrix]

/-- Conjugation by `1` is the identity rotation. -/
example : adjointMatrix (1 : ℍ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adjointMatrix]

end ClassicalLean.Geometry
