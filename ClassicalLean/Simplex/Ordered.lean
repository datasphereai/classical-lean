/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Simplex.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Fin.Tuple.Sort

/-!
# The ordered simplex, and its cuts by a coordinate threshold

On a finite index set with a linear order, the **ordered simplex** is the part of Mathlib's
`closedSimplex ι` whose coordinates are sorted:

    orderedSimplex ι = { x ∈ closedSimplex ι | Antitone x }

It is a **fundamental domain** for the action of the symmetric group on the simplex by
permuting coordinates — every probability vector is a rearrangement of exactly one sorted one —
which is why it turns up wherever a statement should not depend on how the coordinates are
labelled. That is `existsUnique_mem_orderedSimplex` below, proved for `Fin n`.

This file also proves the ordered simplex is convex, and that cutting it with a threshold on
one coordinate leaves a convex set whichever way the cut is taken. Each of those is Mathlib
plus one line: `convex_closedSimplex`, `convex_halfSpace_ge` / `convex_halfSpace_lt` /
`convex_hyperplane`, and `Convex.inter`.

## Provenance

Ported from a source module whose title named the fundamental Weyl alcove of the root system
`C₃` and its isomorphism with a simplex. Neither appears in it: there is no root system, no
Weyl group and no alcove, the "alcove" being an alias for the simplex it is then shown to be
isomorphic to — by `id`. What survived the port is the convexity material below, generalised
from one chosen threshold to an arbitrary one.

The object does deserve a name, and the honest version of the "alcove" reading is the
fundamental-domain property: the sorted simplex really is a set of orbit representatives for the
coordinate-permutation action. The source asserted that through a name and never proved it;
`existsUnique_mem_orderedSimplex` below proves it.

-/

open Finset

namespace ClassicalLean.Simplex

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The ordered simplex: probability vectors whose coordinates are sorted downward. For
`ι = Fin n` this is a fundamental domain for the permutation action on `closedSimplex ι`
(`existsUnique_mem_orderedSimplex`). -/
def orderedSimplex (ι : Type*) [Fintype ι] [LinearOrder ι] : Set (ι → ℝ) :=
  {x ∈ closedSimplex ι | Antitone x}

/-- Membership unfolds to the two defining conditions. A definitional unfolding — the proof is
`Iff.rfl` — stated so it can be cited by name. -/
theorem mem_orderedSimplex {x : ι → ℝ} :
    x ∈ orderedSimplex ι ↔ x ∈ closedSimplex ι ∧ Antitone x := Iff.rfl

/-- The ordered simplex sits inside `closedSimplex ι`. -/
theorem orderedSimplex_subset_closedSimplex : orderedSimplex ι ⊆ closedSimplex ι :=
  fun _ hx => hx.1

/-- The set of antitone vectors is convex: `Antitone x` is a conjunction of the linear
conditions `x j ≤ x i` for `i ≤ j`, each of which cuts out a half-space. -/
theorem convex_antitone {ι : Type*} [Preorder ι] : Convex ℝ {x : ι → ℝ | Antitone x} := by
  intro x hx y hy a b ha hb _ i j hij
  have hxij : x j ≤ x i := hx hij
  have hyij : y j ≤ y i := hy hij
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left hxij ha) (mul_le_mul_of_nonneg_left hyij hb)

/-- **The ordered simplex is convex.** `convex_closedSimplex` intersected with `convex_antitone`. -/
theorem convex_orderedSimplex : Convex ℝ (orderedSimplex ι) :=
  convex_closedSimplex.inter convex_antitone

/-! ## Cutting by a threshold on one coordinate

The source cut the simplex at `λ = 1/φ` and named the three pieces. The constant plays no part
in any of the proofs, so the cut is taken here at an arbitrary real `t` and an arbitrary
coordinate `i`. -/

/-- Evaluation at a coordinate is linear — the input the three Mathlib convexity lemmas want. -/
theorem isLinearMap_eval {ι : Type*} (i : ι) : IsLinearMap ℝ (fun x : ι → ℝ => x i) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

variable (i : ι) (t : ℝ)

/-- The part of the ordered simplex on or above a threshold in coordinate `i` is convex. -/
theorem convex_orderedSimplex_ge :
    Convex ℝ {x ∈ orderedSimplex ι | t ≤ x i} :=
  convex_orderedSimplex.inter (convex_halfSpace_ge (isLinearMap_eval i) t)

/-- The part strictly below the threshold is convex. -/
theorem convex_orderedSimplex_lt :
    Convex ℝ {x ∈ orderedSimplex ι | x i < t} := by
  have h : Convex ℝ {x : ι → ℝ | x i < t} := convex_halfSpace_lt (isLinearMap_eval i) t
  exact convex_orderedSimplex.inter h

/-- The face where coordinate `i` equals the threshold is convex. -/
theorem convex_orderedSimplex_eq :
    Convex ℝ {x ∈ orderedSimplex ι | x i = t} :=
  convex_orderedSimplex.inter (convex_hyperplane (isLinearMap_eval i) t)

/-- The threshold splits the ordered simplex into three pieces. The source stated this for its
own constant and its own three named regions; it is a trichotomy on a real number and holds for
any `t`. -/
theorem orderedSimplex_eq_union :
    orderedSimplex ι
      = {x ∈ orderedSimplex ι | t < x i}
        ∪ {x ∈ orderedSimplex ι | x i < t}
        ∪ {x ∈ orderedSimplex ι | x i = t} := by
  ext x
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · intro hx
    rcases lt_trichotomy (x i) t with h | h | h
    · exact Or.inl (Or.inr ⟨hx, h⟩)
    · exact Or.inr ⟨hx, h⟩
    · exact Or.inl (Or.inl ⟨hx, h⟩)
  · rintro ((⟨hx, _⟩ | ⟨hx, _⟩) | ⟨hx, _⟩) <;> exact hx

/-! ## The ordered simplex is a fundamental domain

The reason the sorted simplex is worth naming: the symmetric group acts on the simplex by
permuting coordinates, and **every point of the simplex is a permutation of exactly one sorted
point**. That makes the ordered simplex a set of orbit representatives — a fundamental domain —
so a statement proved there, about a quantity invariant under relabelling coordinates, holds
everywhere on the simplex.

This is the honest content of the "alcove" reading the source file asserted through a name and
never proved. It is stated here for `Fin n`, where Mathlib's sorting API lives
(`Tuple.sort`, `Tuple.monotone_sort`, `Tuple.unique_antitone`). -/

section FundamentalDomain

variable {n : ℕ}

/-- Permuting coordinates preserves membership of `closedSimplex`: it permutes the nonnegativity
conditions and leaves the sum unchanged. -/
theorem closedSimplex_comp_perm {x : Fin n → ℝ} (hx : x ∈ closedSimplex (Fin n))
    (σ : Equiv.Perm (Fin n)) : x ∘ σ ∈ closedSimplex (Fin n) :=
  ⟨fun i => hx.1 (σ i), by simpa [Function.comp] using (Equiv.sum_comp σ x).trans hx.2⟩

/-- **Existence.** Some permutation sorts any tuple downward: Mathlib's `Tuple.sort` sorts it
upward, and reversing the index order turns that into an antitone arrangement. -/
theorem exists_antitone_comp_perm (x : Fin n → ℝ) :
    ∃ σ : Equiv.Perm (Fin n), Antitone (x ∘ σ) := by
  refine ⟨Fin.revPerm.trans (Tuple.sort x), ?_⟩
  have hm : Monotone (x ∘ Tuple.sort x) := Tuple.monotone_sort x
  intro i j hij
  have hrev : (Fin.rev j : Fin n) ≤ Fin.rev i := Fin.rev_le_rev.mpr hij
  simpa [Function.comp, Equiv.trans] using hm hrev

/-- **The ordered simplex is a fundamental domain for the coordinate-permutation action.**

For every point `x` of `closedSimplex (Fin n)` there is exactly one `y` that is both a
rearrangement of `x` and sorted — one point of `orderedSimplex (Fin n)` in the orbit of `x`.

Existence is `exists_antitone_comp_perm`; uniqueness is Mathlib's `Tuple.unique_antitone`, which
says two antitone rearrangements of the same tuple are equal *as functions* (the permutations
themselves need not agree, and do not when `x` has repeated values). -/
theorem existsUnique_mem_orderedSimplex {x : Fin n → ℝ} (hx : x ∈ closedSimplex (Fin n)) :
    ∃! y : Fin n → ℝ, y ∈ orderedSimplex (Fin n) ∧ ∃ σ : Equiv.Perm (Fin n), y = x ∘ σ := by
  obtain ⟨σ₀, hσ₀⟩ := exists_antitone_comp_perm x
  refine ⟨x ∘ σ₀, ⟨⟨closedSimplex_comp_perm hx σ₀, hσ₀⟩, ⟨σ₀, rfl⟩⟩, ?_⟩
  rintro y ⟨⟨-, hy_anti⟩, ⟨τ, rfl⟩⟩
  exact Tuple.unique_antitone hy_anti hσ₀

/-- The orbit formulation: the sorted representative of `x` lies in the ordered simplex, and any
rearrangement of `x` that lies there equals it. -/
theorem eq_of_mem_orderedSimplex_of_comp_perm {x y z : Fin n → ℝ}
    (hy : y ∈ orderedSimplex (Fin n)) (hz : z ∈ orderedSimplex (Fin n))
    (σ τ : Equiv.Perm (Fin n)) (hyx : y = x ∘ σ) (hzx : z = x ∘ τ) : y = z := by
  subst hyx; subst hzx
  exact Tuple.unique_antitone hy.2 hz.2

end FundamentalDomain

end ClassicalLean.Simplex
