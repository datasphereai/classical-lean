/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Algebra.Pseudoinverse
import ClassicalLean.Statistics.Cochran

/-!
# The hat matrix of any design: its rank and trace

Bridge 170 of `MATH-PLAN-library-2-bridges-2.md` (order CLOUD-MATH-7), joining
`ClassicalLean.Algebra.Pseudoinverse` and `ClassicalLean.Statistics.Cochran`.

* `rank_mul_pinv_eq` — for every real `m × n` matrix `A`, rank-deficient included, the hat matrix
  `H = A * pinv A` has rank `rank A` and trace `rank A`, and the residual maker `1 - H` has rank
  `m - rank A`, the residual degrees of freedom. `Statistics.Cochran`'s `rank_mul_leastSquares` is
  the full-rank case.

The proof. `pinv_spec` gives `A (pinv A) A = A`, so `H H = (A (pinv A) A) (pinv A) = H`: `H` is
idempotent. `A = H A` gives `rank A ≤ rank H` (`Matrix.rank_mul_le_left`) and `H = A (pinv A)`
gives `rank H ≤ rank A`. `rank_eq_trace_of_isIdempotentElem` gives `trace H = rank H`. `H` and
`1 - H` are idempotent and add up to `1`, so by `sum_rank_eq_iff` their ranks add up to `m`.

The statement was written by order LEAN-38 (a reading order) and elaborated there stated without
a proof; this module proves it word for word.
-/

open Matrix

namespace ClassicalLean.Algebra.HatMatrixRank

/-- **The hat matrix of any design has rank and trace equal to the design's rank.** For every real
`m × n` matrix `A`, rank-deficient included, `H = A * pinv A` is a symmetric idempotent with
`rank H = trace H = rank A`, and the residual maker `1 - H` has rank `m - rank A`: the residual
degrees of freedom. `Statistics.Cochran`'s `rank_mul_leastSquares` is the full-rank case.
Bridge 170 of `MATH-PLAN-library-2-bridges-2.md`. -/
theorem rank_mul_pinv_eq {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) :
    (A * ClassicalLean.Algebra.Pseudoinverse.pinv A).rank = A.rank ∧
      (A * ClassicalLean.Algebra.Pseudoinverse.pinv A).trace = (A.rank : ℝ) ∧
      (1 - A * ClassicalLean.Algebra.Pseudoinverse.pinv A).rank = Fintype.card m - A.rank := by
  set H := A * ClassicalLean.Algebra.Pseudoinverse.pinv A with hH_def
  have h1 : A * ClassicalLean.Algebra.Pseudoinverse.pinv A * A = A :=
    (ClassicalLean.Algebra.Pseudoinverse.pinv_spec A).1
  have hHA : H * A = A := h1
  have hid : IsIdempotentElem H := by
    rw [IsIdempotentElem, hH_def, ← Matrix.mul_assoc, h1]
  have hr : H.rank = A.rank := by
    refine le_antisymm (Matrix.rank_mul_le_left _ _) ?_
    calc A.rank = (H * A).rank := by rw [hHA]
      _ ≤ H.rank := Matrix.rank_mul_le_left _ _
  have hid' : IsIdempotentElem (1 - H) := hid.one_sub
  let B : Bool → Matrix m m ℝ := fun b ↦ if b then H else 1 - H
  have hsum : ∑ b, B b = 1 := by simp [B]
  have hranks := (ClassicalLean.Statistics.sum_rank_eq_iff hsum).mpr (by
    rintro (_ | _) <;> simpa [B])
  simp only [Fintype.sum_bool, B, Bool.false_eq_true, ↓reduceIte] at hranks
  refine ⟨hr, ?_, by omega⟩
  rw [← ClassicalLean.Statistics.rank_eq_trace_of_isIdempotentElem hid, hr]

end ClassicalLean.Algebra.HatMatrixRank
