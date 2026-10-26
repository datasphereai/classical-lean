/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul

/-!
# Three invariants of a 3×3 matrix, and the gap identity

For a 3×3 matrix `M` over a commutative ring, the three coefficients of the characteristic
polynomial are the trace, the sum of the three principal 2×2 minors, and the determinant. This
file defines the middle one (`minorSum` — Mathlib has `Matrix.trace` and `Matrix.det` already),
identifies all three by computing `det (M - x • 1)` in closed form, and proves two algebraic
identities in which they appear:

* Newton's identity `tr(M²) = tr(M)² - 2·minorSum M`;
* the **gap identity** `2·(tr(M)² - 3·minorSum M) = diagSep M + 6·offDiagCross M`, where
  `diagSep` is the sum of the squared differences of the diagonal entries and `offDiagCross` is
  the sum of the three products `M i j · M j i` with `i < j`.

The name "gap" is earned by `gap_of_roots`: if the characteristic polynomial has roots `a, b, c`
— expressed here by the two Vieta hypotheses relating them to `trace` and `minorSum` — then the
right-hand side of the gap identity is exactly `(a-b)² + (a-c)² + (b-c)²`, the sum of the squared
differences of the roots. So the identity rewrites a quantity built from the *entries* of `M` as
a quantity built from its *eigenvalues*.

Everything here holds over an arbitrary commutative ring; nothing needs an order, a field, or
symmetry of `M`. The proofs come in three shapes: the three theorems about the entries of `M`
(`det_sub_smul_one`, `trace_mul_self`, `gap_identity`) are a `simp` normalisation of the entries
followed by `ring`; the three root-side companions (`cubic_factored`, `sq_add_sq_add_sq`,
`two_mul_sq_sub_three_mul`) are bare `ring` identities in three ring elements, with no matrix in
them; and the two corollaries (`gap_identity_of_offDiagCross_eq_zero`, `gap_of_roots`) are `rw`
chains through the theorems above, with neither `simp` nor `ring`.

**What the source file this module was ported from had, and where it went.** One line per
source declaration, so that a drop is a decision on the record rather than a silence. The source
worked over a hand-rolled structure `Mat3` of nine `Int` fields; everything below is over
`Matrix (Fin 3) (Fin 3) R` for an arbitrary `[CommRing R]`, which is why the structure and its
operations have no counterpart here.

* `Mat3`, `Mat3.add`, `Mat3.mul`, `Mat3.identity` — dropped: Mathlib's `Matrix`, with its own
  addition, multiplication and `1`.
* `Mat3.trace`, `Mat3.det` — dropped: Mathlib's `Matrix.trace` and `Matrix.det`, which this file
  uses directly.
* `Mat3.cofactorSum` — shipped as `minorSum`, entry for entry the same expression.
* `Mat3.diagSep`, `Mat3.offDiagCrossSum` — shipped as `diagSep` and `offDiagCross`.
* `Mat3.traceSq` — dropped: it abbreviates `(M * M).trace`, which is written out in
  `trace_mul_self`.
* `CharPoly`, `Mat3.charPoly`, `thm_Q` — dropped: `charPoly` *defines* the triple
  `(trace, cofactorSum, det)` and `thm_Q` is then `rfl`, so the source's identification of the
  characteristic coefficients is bookkeeping rather than a theorem. Replaced by
  `det_sub_smul_one`, which computes `det (M - x·1)` and so has to prove what `thm_Q` assumed.
* `thm_N` — shipped as `gap_identity`, generalised from `Int` to any `CommRing`.
* `trace_sq_identity` — shipped as `trace_mul_self`, likewise generalised; the source wrote
  `x * x` where this file writes `x ^ 2`.
* `trace_add` — dropped: Mathlib's `Matrix.trace_add`.
* `trace_identity`, `det_identity` (trace and determinant of the identity matrix) — **not shipped
  as theorems**: they appear below only as anonymous `example`s, which introduce no constants, are
  unaddressable from another module, and are invisible to the axiom and vacuity gates. Count them
  as dropped with an elaboration check, not as ported theorems. The named facts are Mathlib's
  `Matrix.trace_one` and `Matrix.det_one`.
-/

namespace ClassicalLean.Geometry.Matrix3

variable {R : Type*} [CommRing R]

/-! ## The three characteristic coefficients -/

/-- The sum of the three principal 2×2 minors of a 3×3 matrix: the middle coefficient of the
characteristic polynomial. Mathlib supplies the outer two as `Matrix.trace` and `Matrix.det`. -/
def minorSum (M : Matrix (Fin 3) (Fin 3) R) : R :=
  (M 1 1 * M 2 2 - M 1 2 * M 2 1) + (M 0 0 * M 2 2 - M 0 2 * M 2 0) +
    (M 0 0 * M 1 1 - M 0 1 * M 1 0)

/-- **The characteristic polynomial in closed form.** For every `x`,
`det (M - x·1) = -x³ + tr(M)·x² - minorSum(M)·x + det(M)`. This is what licenses calling
`minorSum` a coefficient of the characteristic polynomial: the identity is proved, not assumed.
It is a statement about the value of the determinant at each ring element `x`, not about
polynomials; the passage from one to the other is not needed below and is not made here. -/
theorem det_sub_smul_one (M : Matrix (Fin 3) (Fin 3) R) (x : R) :
    (M - x • (1 : Matrix (Fin 3) (Fin 3) R)).det =
      -x ^ 3 + M.trace * x ^ 2 - minorSum M * x + M.det := by
  simp [Matrix.det_fin_three, Matrix.trace_fin_three, minorSum, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

/-- A monic cubic with roots `a, b, c`, expanded. Together with `det_sub_smul_one` this displays
the classical dictionary: the coefficient of `x²` is `a + b + c`, the coefficient of `x` is
`ab + ac + bc`, and the constant term is `abc`. Both sides are ring expressions, so this is a
`ring` identity; reading coefficients off an equality of polynomial *functions* would need more
and is not done here. -/
theorem cubic_factored (a b c x : R) :
    -((x - a) * (x - b) * (x - c)) =
      -x ^ 3 + (a + b + c) * x ^ 2 - (a * b + a * c + b * c) * x + a * b * c := by
  ring

/-! ## Newton's identity -/

/-- **Newton's identity** in degree two: `tr(M²) = tr(M)² - 2·minorSum M`. The matching identity
on the root side is `sq_add_sq_add_sq` below. -/
theorem trace_mul_self (M : Matrix (Fin 3) (Fin 3) R) :
    (M * M).trace = M.trace ^ 2 - 2 * minorSum M := by
  simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three, minorSum]
  ring

/-- The root-side companion of `trace_mul_self`: for any three ring elements,
`a² + b² + c² = (a+b+c)² - 2(ab+ac+bc)`. Read with `det_sub_smul_one` and `cubic_factored`, this
is the sense in which `tr(M²)` is the sum of the squares of the roots. -/
theorem sq_add_sq_add_sq (a b c : R) :
    a ^ 2 + b ^ 2 + c ^ 2 = (a + b + c) ^ 2 - 2 * (a * b + a * c + b * c) := by
  ring

/-! ## The gap identity -/

/-- The sum of the squared differences of the three diagonal entries. -/
def diagSep (M : Matrix (Fin 3) (Fin 3) R) : R :=
  (M 0 0 - M 1 1) ^ 2 + (M 0 0 - M 2 2) ^ 2 + (M 1 1 - M 2 2) ^ 2

/-- The sum of the three off-diagonal products `M i j · M j i` for `i < j`. -/
def offDiagCross (M : Matrix (Fin 3) (Fin 3) R) : R :=
  M 0 1 * M 1 0 + M 0 2 * M 2 0 + M 1 2 * M 2 1

/-- **The gap identity.** `2·(tr(M)² - 3·minorSum M) = diagSep M + 6·offDiagCross M`: the
combination `p₁² - 3p₂` of the characteristic coefficients is, up to the factor `2`, the diagonal
spread plus six times the off-diagonal coupling. -/
theorem gap_identity (M : Matrix (Fin 3) (Fin 3) R) :
    2 * (M.trace ^ 2 - 3 * minorSum M) = diagSep M + 6 * offDiagCross M := by
  simp only [Matrix.trace_fin_three, minorSum, diagSep, offDiagCross]
  ring

/-- The same combination on the root side: for any three ring elements,
`2·((a+b+c)² - 3(ab+ac+bc)) = (a-b)² + (a-c)² + (b-c)²`. -/
theorem two_mul_sq_sub_three_mul (a b c : R) :
    2 * ((a + b + c) ^ 2 - 3 * (a * b + a * c + b * c)) =
      (a - b) ^ 2 + (a - c) ^ 2 + (b - c) ^ 2 := by
  ring

/-- When the off-diagonal coupling vanishes, the gap identity reduces to the diagonal spread
alone: `2(tr(M)² - 3·minorSum M) = diagSep M`. -/
theorem gap_identity_of_offDiagCross_eq_zero {M : Matrix (Fin 3) (Fin 3) R}
    (h : offDiagCross M = 0) :
    2 * (M.trace ^ 2 - 3 * minorSum M) = diagSep M := by
  rw [gap_identity, h, mul_zero, add_zero]

/-- **The gap identity read through the roots.** If `a, b, c` are related to `M` by the two Vieta
identities that `det_sub_smul_one` and `cubic_factored` put side by side — `tr(M) = a + b + c`
and `minorSum M = ab + ac + bc` — then the entry-side quantity `diagSep M + 6·offDiagCross M` is
exactly the sum of the squared differences of `a, b, c`. This is the sense in which the identity
measures a gap. The hypotheses are assumed here, not derived: nothing below claims that such
`a, b, c` exist in `R`. -/
theorem gap_of_roots (M : Matrix (Fin 3) (Fin 3) R) (a b c : R)
    (htrace : M.trace = a + b + c) (hminor : minorSum M = a * b + a * c + b * c) :
    diagSep M + 6 * offDiagCross M = (a - b) ^ 2 + (a - c) ^ 2 + (b - c) ^ 2 := by
  rw [← gap_identity, htrace, hminor, two_mul_sq_sub_three_mul]

/-! ## Concrete instances

Trace, determinant and minor sum of the identity matrix are `3`, `1` and `3`; the first two are
Mathlib's `Matrix.trace_one` and `Matrix.det_one`. -/

example : (1 : Matrix (Fin 3) (Fin 3) ℤ).trace = 3 := by
  simp

example : (1 : Matrix (Fin 3) (Fin 3) ℤ).det = 1 := Matrix.det_one

example : minorSum (1 : Matrix (Fin 3) (Fin 3) ℤ) = 3 := by
  simp [minorSum]

example : minorSum !![(0 : ℤ), 1, 2; 3, 4, 5; 6, 7, 8] = -18 := by
  simp [minorSum]

end ClassicalLean.Geometry.Matrix3

/-- The hypotheses of `gap_identity_of_offDiagCross_eq_zero` hold together: over `ℤ`, the matrix
`!![1, 1, 1; 2, 2, 1; -3, 1, 3]` has `offDiagCross = 1 * 2 + 1 * (-3) + 1 * 1 = 0` with every
product nonzero (not a diagonal matrix, where each product is `0`), and distinct diagonal
entries. -/
example := ClassicalLean.Geometry.Matrix3.gap_identity_of_offDiagCross_eq_zero
  (R := ℤ) (M := !![1, 1, 1; 2, 2, 1; -3, 1, 3])
  (by simp [ClassicalLean.Geometry.Matrix3.offDiagCross])
