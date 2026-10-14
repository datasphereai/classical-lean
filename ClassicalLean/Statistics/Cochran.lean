/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Statistics.FrischWaughLovell
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Idempotents

/-!
# Cochran's theorem, the matrix form

Square matrices `A₁, …, A_k` over a field `K` that add up to the identity `1` (of size `n`):

* `mul_eq_zero_of_add_eq_one_of_rank_add_le`, `isIdempotentElem_of_add_eq_one_of_rank_add_le` —
  the two-matrix case, over any field: if `A + B = 1` and `rank A + rank B ≤ n`, then `A B = 0`
  and `A A = A`.
* `isIdempotentElem_of_sum_rank_eq` — over any field, if the ranks add up to `n`, every `Aᵢ` is
  idempotent (`Aᵢ Aᵢ = Aᵢ`).
* `sum_rank_eq_iff` — over a field of characteristic zero (the reals among them), the ranks add up
  to exactly `n` if and only if every `Aᵢ` is idempotent.
* `mul_eq_zero_of_sum_rank_eq` — and then `Aᵢ Aⱼ = 0` for `i ≠ j`, over any field with `2 ≠ 0`;
  `completeOrthogonalIdempotents_of_sum_rank_eq` says the same in Mathlib's terms.
* `rank_mul_leastSquares` — an example from order LEAN-17's residual maker: the residual maker
  `M = 1 − X (Xᵀ X)⁻¹ Xᵀ` and the matrix `H = X (Xᵀ X)⁻¹ Xᵀ` add to `1` and are idempotent, so their
  ranks add to `n`; with `rank M = n − p` (LEAN-17), `rank H = p`.

Helpers, proved here: `rank_add_le` and `rank_sum_le` (the rank of a sum is at most the sum of
the ranks) and `rank_eq_trace_of_isIdempotentElem` (over any field, an idempotent's rank, read in
`K`, is its trace).

No symmetry is assumed. In statistics the matrices are symmetric and the theorem is applied to
quadratic forms `xᵀ Aᵢ x` of a normal vector `x`.

## What is cited, and what is not

Cochran (1934, Proceedings of the Cambridge Philosophical Society 30, 178–191) stated his theorem
for quadratic forms in independent standard normal variables, whose distributions are then
independent chi-squared laws. This file proves only the matrix algebra behind it, which is often
called the algebraic form of Cochran's theorem; it does not state anything about distributions
(Mathlib has no chi-squared law). Checked for this order by web search, not against the 1934 paper,
which was not read: the paper is about quadratic forms, and no source found credits the matrix
statement here to it.

## Hypotheses

Measured in order LEAN-20's checks (check C24, exact rationals): 150 families of idempotents
summing to `1` (ranks add to `n`, pairwise products `0`) and 300 random families summing to `1`
(ranks add to `n` exactly when all are idempotent). Each hypothesis fails when dropped alone:

* characteristic zero, for "idempotent ⇒ ranks add to `n`" (the other way holds over any
  field): over the field with two elements, `A₁ = A₂ = A₃ = [1]` add up to `[1]` and are
  idempotent, but their ranks add to `3`, not `1`.
* the sum is `1`: one matrix `[2]` (`n = 1`) has rank `1 = n` and is not idempotent; and
  `A₁ = A₂ = [1]` are idempotent with ranks adding to `2`, not `1`.
* in the two-matrix case, `A + B = 1`: `A = [2]`, `B = [0]`; the rank bound: `A = [2]`, `B = [−1]`.
* in `mul_eq_zero_of_sum_rank_eq`, the ranks: `A₁ = [2]`, `A₂ = [−1]` (product `−2`); the sum:
  `A₁ = A₂ = diag(1, 0)` (`n = 2`, ranks add to `2`, product `A₁ ≠ 0`); `i ≠ j`: `[1] [1] = [1]`.
* in `rank_mul_leastSquares`, the invertible Gram matrix: at `X = 0` (two rows, one column)
  Lean's inverse of the zero matrix is `0`, so `H = 0` has rank `0`, not `1`.

`2 ≠ 0` is assumed in `mul_eq_zero_of_sum_rank_eq` because its proof divides by `2`; the
statement is true over every field (the column spaces form a direct sum), but that proof is not
written here.

The name `sum_rank_eq_iff` is the order's; Mathlib's habit would be a longer name such as
`sum_rank_eq_card_iff_forall_isIdempotentElem`. The helpers `rank_add_le` and `rank_sum_le` are
general facts about matrices kept in this namespace; Mathlib has `LinearMap.rank_add_le` only in
cardinal form (review r24).

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-20, `grep -rniE` over Mathlib): `cochran` 0;
idempotents beside rank 7 lines, all about rank-one projections. Used: `LinearMap.IsProj.trace`
(the trace of a projection is the dimension of its range) and
`Submodule.finrank_sup_add_finrank_inf_eq`.
-/

open Matrix Module

namespace ClassicalLean.Statistics

variable {K : Type*} [Field K] {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

omit [DecidableEq n] in
/-- The rank of a sum of two matrices is at most the sum of their ranks. -/
theorem rank_add_le (A B : Matrix n n K) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  calc finrank K (LinearMap.range (A + B).mulVecLin)
      ≤ finrank K ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin :
          Submodule K (n → K)) := by
        apply Submodule.finrank_mono
        rintro _ ⟨x, rfl⟩
        rw [Matrix.mulVecLin_apply, Matrix.add_mulVec]
        exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

omit [DecidableEq n] [Fintype ι] in
/-- The rank of a finite sum of matrices is at most the sum of their ranks. -/
theorem rank_sum_le {s : Finset ι} (A : ι → Matrix n n K) :
    (∑ i ∈ s, A i).rank ≤ ∑ i ∈ s, (A i).rank := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (rank_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- **The two-matrix case, the product.** If `A + B = 1` and the ranks of `A` and `B` add up to
at most `n`, then `A B = 0`. Over any field. The column spaces of `A` and `B` together span
everything (`x = A x + B x`), so the rank bound forces them to meet only in `0`; and `A B = B A`
sends every vector into both. -/
theorem mul_eq_zero_of_add_eq_one_of_rank_add_le {A B : Matrix n n K} (h : A + B = 1)
    (hr : A.rank + B.rank ≤ Fintype.card n) : A * B = 0 := by
  set U := LinearMap.range A.mulVecLin
  set V := LinearMap.range B.mulVecLin
  have hsup : U ⊔ V = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    have hx : x = A *ᵥ x + B *ᵥ x := by rw [← Matrix.add_mulVec, h, Matrix.one_mulVec]
    rw [hx]
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq U V
  rw [hsup, finrank_top, Module.finrank_fintype_fun_eq_card] at hdim
  have hinf : U ⊓ V = ⊥ := by
    rw [← Submodule.finrank_eq_zero]
    have hU : A.rank = finrank K U := rfl
    have hV : B.rank = finrank K V := rfl
    omega
  have hB : B = 1 - A := by rw [← h]; abel
  have hcomm : A * B = B * A := by rw [hB, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul]
  ext i j
  have hmem : (A * B) *ᵥ Pi.single j 1 ∈ U ⊓ V := by
    refine ⟨⟨B *ᵥ Pi.single j 1, ?_⟩, ⟨A *ᵥ Pi.single j 1, ?_⟩⟩
    · rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
    · rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hcomm]
  rw [hinf, Submodule.mem_bot] at hmem
  have := congrFun hmem i
  simpa [Matrix.mulVec_single_one] using this

/-- **The two-matrix case.** If `A + B = 1` and the ranks of `A` and `B` add up to at most `n`,
then `A` is idempotent: `A A = A`. Over any field: `A B = A (1 − A) = 0`. -/
theorem isIdempotentElem_of_add_eq_one_of_rank_add_le {A B : Matrix n n K} (h : A + B = 1)
    (hr : A.rank + B.rank ≤ Fintype.card n) : IsIdempotentElem A := by
  have hAB := mul_eq_zero_of_add_eq_one_of_rank_add_le h hr
  have hB : B = 1 - A := by rw [← h]; abel
  rw [hB, Matrix.mul_sub, Matrix.mul_one] at hAB
  exact (sub_eq_zero.mp hAB).symm

omit [DecidableEq n] in
/-- For an idempotent matrix over any field, the rank (read as an element of `K`) is the trace:
Mathlib's `LinearMap.IsProj.trace`, as order LEAN-17 used it for the residual maker. -/
theorem rank_eq_trace_of_isIdempotentElem {A : Matrix n n K} (hA : IsIdempotentElem A) :
    (A.rank : K) = A.trace := by
  classical
  have hid : IsIdempotentElem A.mulVecLin := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hA.eq]
  rw [Matrix.rank, ← (LinearMap.IsIdempotentElem.isProj_range _ hid).trace]
  exact Matrix.trace_toLin'_eq A

/-- **Ranks adding to `n` force idempotents**, over any field: if square matrices add up to `1`
and their ranks add up to `n`, each is idempotent. Each `Aᵢ` and the sum of the others satisfy
the two-matrix case. -/
theorem isIdempotentElem_of_sum_rank_eq {A : ι → Matrix n n K} (h : ∑ i, A i = 1)
    (hr : ∑ i, (A i).rank = Fintype.card n) (i : ι) : IsIdempotentElem (A i) := by
  classical
  apply isIdempotentElem_of_add_eq_one_of_rank_add_le (B := ∑ j ∈ Finset.univ.erase i, A j)
  · rw [Finset.add_sum_erase _ _ (Finset.mem_univ i), h]
  · calc (A i).rank + (∑ j ∈ Finset.univ.erase i, A j).rank
        ≤ (A i).rank + ∑ j ∈ Finset.univ.erase i, (A j).rank :=
          Nat.add_le_add_left (rank_sum_le _) _
      _ = Fintype.card n := by
        rw [Finset.add_sum_erase Finset.univ (fun j ↦ (A j).rank) (Finset.mem_univ i), hr]

/-- **Cochran's theorem, the matrix form.** Square matrices over a field of characteristic zero
that add up to `1` have ranks adding up to exactly `n` if and only if each of them is idempotent.
One way is `isIdempotentElem_of_sum_rank_eq`, over any field. The other way: the rank of an
idempotent is its trace, and the traces add to the trace of `1`, which is `n`; this way needs
characteristic zero. -/
theorem sum_rank_eq_iff [CharZero K] {A : ι → Matrix n n K} (h : ∑ i, A i = 1) :
    ∑ i, (A i).rank = Fintype.card n ↔ ∀ i, IsIdempotentElem (A i) := by
  classical
  constructor
  · exact isIdempotentElem_of_sum_rank_eq h
  · intro hid
    have htr : ((∑ i, (A i).rank : ℕ) : K) = Fintype.card n := by
      push_cast
      rw [Finset.sum_congr rfl fun i _ ↦ rank_eq_trace_of_isIdempotentElem (hid i),
        ← Matrix.trace_sum, h, Matrix.trace_one]
    exact_mod_cast htr

/-- **Then the matrices annihilate each other**: `Aᵢ Aⱼ = 0` for `i ≠ j`. The pair `Aᵢ + Aⱼ`
and the sum of the others satisfy the two-matrix case, so `Aᵢ + Aⱼ` is idempotent too, which
gives `Aᵢ Aⱼ + Aⱼ Aᵢ = 0`; multiplying by `Aᵢ` on either side gives `Aᵢ Aⱼ = Aⱼ Aᵢ`, so
`2 Aᵢ Aⱼ = 0`. The proof divides by `2`, so it assumes `2 ≠ 0` in `K`. -/
theorem mul_eq_zero_of_sum_rank_eq [NeZero (2 : K)] {A : ι → Matrix n n K} (h : ∑ i, A i = 1)
    (hr : ∑ i, (A i).rank = Fintype.card n) {i j : ι} (hij : i ≠ j) : A i * A j = 0 := by
  classical
  have hid := isIdempotentElem_of_sum_rank_eq h hr
  set s := (Finset.univ.erase i).erase j
  have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  have hsplit : ∀ f : ι → Matrix n n K, ∑ k, f k = f i + (f j + ∑ k ∈ s, f k) := fun f ↦ by
    rw [Finset.add_sum_erase _ _ hj, Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hsplitN : ∑ k, (A k).rank = (A i).rank + ((A j).rank + ∑ k ∈ s, (A k).rank) := by
    rw [Finset.add_sum_erase _ (fun k ↦ (A k).rank) hj,
      Finset.add_sum_erase Finset.univ (fun k ↦ (A k).rank) (Finset.mem_univ i)]
  have hpair : IsIdempotentElem (A i + A j) := by
    apply isIdempotentElem_of_add_eq_one_of_rank_add_le (B := ∑ k ∈ s, A k)
    · rw [add_assoc, ← hsplit, h]
    · have h1 := rank_add_le (A i) (A j)
      have h2 := rank_sum_le (s := s) A
      omega
  have hi := (hid i).eq
  have hXY : A i * A j + A j * A i = 0 := by
    have hp := hpair.eq
    simp only [Matrix.add_mul, Matrix.mul_add, hi, (hid j).eq] at hp
    have h' : A i + A j + (A i * A j + A j * A i) = A i + A j + 0 := by
      rw [add_zero]
      calc A i + A j + (A i * A j + A j * A i) = A i + A j * A i + (A i * A j + A j) := by abel
        _ = A i + A j := hp
    exact add_left_cancel h'
  have h1 : A i * A j + A i * A j * A i = 0 := by
    have := congrArg (A i * ·) hXY
    simpa [Matrix.mul_add, ← Matrix.mul_assoc, hi] using this
  have h2 : A i * A j * A i + A j * A i = 0 := by
    have := congrArg (· * A i) hXY
    simpa [Matrix.add_mul, Matrix.mul_assoc, hi] using this
  have hXeqY : A i * A j = A j * A i := by
    have h3 : A i * A j + A i * A j * A i = A i * A j * A i + A j * A i := h1.trans h2.symm
    rw [add_comm (A i * A j * A i)] at h3
    exact add_right_cancel h3
  rw [← hXeqY] at hXY
  have h2Y : (2 : K) • (A i * A j) = 0 := by rw [two_smul]; exact hXY
  exact (smul_eq_zero.mp h2Y).resolve_left two_ne_zero

/-- **In Mathlib's words**: matrices adding up to `1` with ranks adding up to `n` form a complete
family of orthogonal idempotents (Mathlib's `CompleteOrthogonalIdempotents`), when `2 ≠ 0`. -/
theorem completeOrthogonalIdempotents_of_sum_rank_eq [NeZero (2 : K)] {A : ι → Matrix n n K}
    (h : ∑ i, A i = 1) (hr : ∑ i, (A i).rank = Fintype.card n) :
    CompleteOrthogonalIdempotents A :=
  ⟨⟨isIdempotentElem_of_sum_rank_eq h hr, fun _ _ hij ↦ mul_eq_zero_of_sum_rank_eq h hr hij⟩, h⟩

omit [DecidableEq n] in
/-- **An example: the hat matrix of least squares.** For a design `X` with `n` rows, `p` columns
and invertible Gram matrix `Xᵀ X`, the matrix `X (Xᵀ X)⁻¹ Xᵀ` (here `X * leastSquares X`) has rank
`p`. It and order LEAN-17's residual maker `M = 1 − X (Xᵀ X)⁻¹ Xᵀ` are idempotent and add up to
`1`, so by `sum_rank_eq_iff` their ranks add up to `n`; LEAN-17's `rank_residualMaker` gives
`rank M = n − p`. -/
theorem rank_mul_leastSquares {κ : Type*} [Fintype κ] [DecidableEq κ] {X : Matrix n κ ℝ}
    (h : IsUnit (Xᵀ * X).det) : (X * leastSquares X).rank = Fintype.card κ := by
  classical
  set H := X * leastSquares X
  have hls : leastSquares X * X = 1 := leastSquares_mul_self h
  have hH : IsIdempotentElem H := by
    rw [IsIdempotentElem, Matrix.mul_assoc, ← Matrix.mul_assoc (leastSquares X) X, hls,
      Matrix.one_mul]
  have hM : IsIdempotentElem (residualMaker X) := residualMaker_mul_self X
  let A : Bool → Matrix n n ℝ := fun b ↦ if b then H else residualMaker X
  have hsum : ∑ b, A b = 1 := by
    simp [A, residualMaker, H]
  have hr := (sum_rank_eq_iff hsum).mpr (by rintro (_ | _) <;> simpa [A])
  simp only [Fintype.sum_bool, A, Bool.false_eq_true, ↓reduceIte] at hr
  have hMr := rank_residualMaker h
  have hle : Fintype.card κ ≤ Fintype.card n := by
    have h1 : (Xᵀ * X).rank = Fintype.card κ :=
      Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr h)
    have h2 := Matrix.rank_mul_le_right Xᵀ X
    have h3 := Matrix.rank_le_card_height X
    omega
  omega

end ClassicalLean.Statistics

open Matrix in
/-- The hypotheses of `sum_rank_eq_iff` hold together: over `ℚ` (characteristic `0`), the two
`2 × 2` matrices `diag (1, 0)` and `diag (0, 1)` sum to the identity. -/
example := ClassicalLean.Statistics.sum_rank_eq_iff (K := ℚ) (n := Fin 2) (ι := Fin 2)
  (A := ![!![1, 0; 0, 0], !![0, 0; 0, 1]])
  (by ext i j; fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two])
