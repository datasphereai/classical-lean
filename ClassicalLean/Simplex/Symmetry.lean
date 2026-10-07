/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Simplex.CrossEntropy
import ClassicalLean.Simplex.Ordered

/-!
# Relabelling coordinates, and the loop `Ordered.lean` left open

`ClassicalLean.Simplex.Ordered` proves that the sorted simplex is a **fundamental domain** for
the action of the symmetric group on `closedSimplex (Fin n)` — every probability vector is a
rearrangement of exactly one sorted one (`existsUnique_mem_orderedSimplex`). That is a reduction
principle: a quantity that does not depend on how the coordinates are labelled need only be
studied on the ordered simplex. `HANDOFF.md` §2b records that the reduction exists and that
**nothing uses it**.

This file supplies the missing half — the quantities. `logSumExp` is invariant under relabelling
and `softmax` is equivariant, so the whole of `LogSumExp.lean` and `CrossEntropy.lean` is
material the reduction applies to, and `exists_mem_orderedSimplex_logSumExp_eq` is the reduction
actually being used rather than merely available.

## The asymmetry, stated in both directions

`HANDOFF.md` §2b names an asymmetry in `Gibbs.freeEnergy T i₀ x = -log (x i₀) + T * ∑ x i log
(x i)`: the entropy term is invariant under relabelling, the barrier term is not. Both halves
are now theorems.

* Invariance of the entropy term is `Gibbs.sum_mul_log_comp_equiv`, which already existed and is
  cited here rather than reproved; `gibbsObjective_comp_perm` is built on it.
* Non-invariance of the barrier is `exists_mem_openSimplex_freeEnergy_comp_perm_ne`, which is
  new. `Gibbs.convexOn_barrier`'s docstring says the barrier "ignores every coordinate other than
  `i₀`" and adds that no declaration in that file asserts it. One does now, as an explicit
  witness on two points rather than as a remark: a negative claim needs a counterexample, and
  this is it.

Together they say the free energy is *not* a function the reduction applies to, and exactly
which term is responsible. That is worth stating: the value of a fundamental domain is decided
by which quantities are invariant, and a reader who assumes the free energy is one of them is
wrong for a locatable reason.

## Scope of the reduction

The invariance and equivariance statements hold on any `Fintype`. The reduction itself is stated
for `Fin n`, because that is where `Ordered.lean`'s fundamental-domain theorem lives — Mathlib's
sorting API (`Tuple.sort`, `Tuple.unique_antitone`) is `Fin n`-only, and `Ordered.lean` says so.

## Contents

* `logSumExp_comp_perm`, `softmax_comp_perm` — invariance and equivariance. The second is the
  sharper statement: softmax does not merely survive relabelling, it commutes with it.
* `openSimplex_comp_perm` — the open simplex is stable under relabelling, the analogue of
  `Ordered.closedSimplex_comp_perm` for the strictly positive part.
* `gibbsObjective_comp_perm`, `crossEntropy_comp_perm` — joint invariance, when the logits and
  the probability vector are relabelled together.
* `exists_mem_orderedSimplex_and_eq`, `image_closedSimplex_eq_image_orderedSimplex` — the reduction
  for an arbitrary invariant function, pointwise and as an equality of images.
* `exists_mem_orderedSimplex_logSumExp_eq` — the reduction used.
* `exists_mem_openSimplex_freeEnergy_comp_perm_ne` — the barrier is not invariant.
-/

open Finset

namespace ClassicalLean.Simplex

variable {ι : Type*} [Fintype ι]

/-! ## Invariance and equivariance -/

/-- **Log-sum-exp is invariant under relabelling.** The partition sum is a sum over all
coordinates, so a permutation of the index set permutes its terms. -/
theorem logSumExp_comp_perm (x : ι → ℝ) (σ : Equiv.Perm ι) : logSumExp (x ∘ σ) = logSumExp x := by
  simp only [logSumExp, Function.comp_apply]
  rw [Equiv.sum_comp σ fun j => Real.exp (x j)]

/-- **Softmax is equivariant.** Relabelling the logits relabels the probabilities the same way:
`softmax (x ∘ σ) = softmax x ∘ σ`. The numerator moves with the coordinate and the denominator,
being `logSumExp`'s partition sum, does not move at all. -/
theorem softmax_comp_perm (x : ι → ℝ) (σ : Equiv.Perm ι) : softmax (x ∘ σ) = softmax x ∘ σ := by
  funext i
  simp only [softmax, Function.comp_apply]
  rw [Equiv.sum_comp σ fun j => Real.exp (x j)]

/-- The open simplex is stable under relabelling: positivity is checked coordinatewise and the
sum is unchanged. This is `Ordered.closedSimplex_comp_perm` for the strictly positive part, and it
is what lets a relabelled vector be fed back to the theorems of `Gibbs.lean`. -/
theorem openSimplex_comp_perm {x : ι → ℝ} (hx : x ∈ openSimplex ι) (σ : Equiv.Perm ι) :
    x ∘ σ ∈ openSimplex ι :=
  ⟨fun i => hx.1 (σ i), (Equiv.sum_comp σ x).trans hx.2⟩

/-- **The Gibbs objective is jointly invariant**: relabelling the logits and the probability
vector together leaves it unchanged. The entropy half is `Gibbs.sum_mul_log_comp_equiv`, which
this cites rather than reproves. -/
theorem gibbsObjective_comp_perm (x p : ι → ℝ) (σ : Equiv.Perm ι) :
    gibbsObjective (x ∘ σ) (p ∘ σ) = gibbsObjective x p := by
  simp only [gibbsObjective, Function.comp_apply]
  rw [Equiv.sum_comp σ fun j => p j * x j, sum_mul_log_comp_equiv σ p]

/-- **The cross-entropy is jointly invariant**, for the same reason: `logSumExp` does not move
and the linear term is a sum over all coordinates. -/
theorem crossEntropy_comp_perm (x p : ι → ℝ) (σ : Equiv.Perm ι) :
    crossEntropy (x ∘ σ) (p ∘ σ) = crossEntropy x p := by
  simp only [crossEntropy, Function.comp_apply]
  rw [logSumExp_comp_perm x σ, Equiv.sum_comp σ fun j => p j * x j]

/-! ## The reduction to the ordered simplex

`Ordered.existsUnique_mem_orderedSimplex` says the sorted simplex meets each orbit exactly once.
For a function that is constant on orbits, that means its values on the whole simplex are its
values on the ordered part — the reduction the file's own header describes and which nothing had
used. -/

section FundamentalDomain

variable {n : ℕ}

/-- **The reduction, pointwise.** If `f` does not depend on how coordinates are labelled, then
every point of the standard simplex has a *sorted* point where `f` takes the same value. -/
theorem exists_mem_orderedSimplex_and_eq {f : (Fin n → ℝ) → ℝ}
    (hf : ∀ (y : Fin n → ℝ) (σ : Equiv.Perm (Fin n)), f (y ∘ σ) = f y)
    {x : Fin n → ℝ} (hx : x ∈ closedSimplex (Fin n)) :
    ∃ y ∈ orderedSimplex (Fin n), f y = f x := by
  obtain ⟨σ, hσ⟩ := exists_antitone_comp_perm x
  exact ⟨x ∘ σ, ⟨closedSimplex_comp_perm hx σ, hσ⟩, hf x σ⟩

/-- **The reduction, as an equality of images.** An invariant function takes exactly the same
set of values on the ordered simplex as on the whole simplex — so nothing is lost by working in
the fundamental domain, which is the content the phrase is short for. -/
theorem image_closedSimplex_eq_image_orderedSimplex {f : (Fin n → ℝ) → ℝ}
    (hf : ∀ (y : Fin n → ℝ) (σ : Equiv.Perm (Fin n)), f (y ∘ σ) = f y) :
    f '' closedSimplex (Fin n) = f '' orderedSimplex (Fin n) := by
  refine Set.Subset.antisymm ?_ (Set.image_mono orderedSimplex_subset_closedSimplex)
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hfy⟩ := exists_mem_orderedSimplex_and_eq hf hx
  exact ⟨y, hy, hfy⟩

/-- **The reduction used.** Every value `logSumExp` takes on the standard simplex it already
takes on the ordered simplex. This is the first consumer of
`Ordered.existsUnique_mem_orderedSimplex`'s machinery. -/
theorem exists_mem_orderedSimplex_logSumExp_eq {x : Fin n → ℝ}
    (hx : x ∈ closedSimplex (Fin n)) :
    ∃ y ∈ orderedSimplex (Fin n), logSumExp y = logSumExp x :=
  exists_mem_orderedSimplex_and_eq (fun y σ => logSumExp_comp_perm y σ) hx

/-- The same, as an equality of images. -/
theorem image_closedSimplex_logSumExp :
    (logSumExp : (Fin n → ℝ) → ℝ) '' closedSimplex (Fin n)
      = logSumExp '' orderedSimplex (Fin n) :=
  image_closedSimplex_eq_image_orderedSimplex fun y σ => logSumExp_comp_perm y σ

end FundamentalDomain

/-! ## The barrier is not invariant

The negative half of the asymmetry, as a witness rather than a remark. -/

/-- **The free energy is not invariant under relabelling**, and the barrier term is what breaks
it. At `T = 0` the entropy term vanishes and the free energy is exactly the barrier
`-log (x i₀)`; the two coordinates of `![1/3, 2/3]` differ, so swapping them changes the value.

This is the counterexample `Gibbs.convexOn_barrier`'s docstring points at without exhibiting,
and it is why `exists_mem_orderedSimplex_logSumExp_eq` above has no free-energy counterpart. -/
theorem exists_mem_openSimplex_freeEnergy_comp_perm_ne :
    ∃ (x : Fin 2 → ℝ) (σ : Equiv.Perm (Fin 2)), x ∈ openSimplex (Fin 2) ∧
      freeEnergy 0 (0 : Fin 2) (x ∘ σ) ≠ freeEnergy 0 (0 : Fin 2) x := by
  refine ⟨![1 / 3, 2 / 3], Equiv.swap 0 1, ⟨fun i => ?_, ?_⟩, ?_⟩
  · fin_cases i <;> norm_num
  · simp [Fin.sum_univ_two]
    norm_num
  · have h : Real.log (1 / 3) < Real.log (2 / 3) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    simp only [freeEnergy, Function.comp_apply, Equiv.swap_apply_left, zero_mul, add_zero,
      Matrix.cons_val_zero, Matrix.cons_val_one, ne_eq, neg_inj]
    exact fun hcon => absurd hcon h.ne'

end ClassicalLean.Simplex
