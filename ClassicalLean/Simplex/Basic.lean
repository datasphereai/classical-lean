/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.Convex.StdSimplex
import ClassicalLean.Logic.PredicateStack

/-!
# The open probability simplex

The one definition every module under `ClassicalLean/Simplex/` shares, extracted so that it is
made once. On a finite index set `ι`,

    openSimplex ι = { x : ι → ℝ | (∀ i, 0 < x i) ∧ ∑ i, x i = 1 },

the strictly positive part of the closed simplex `closedSimplex ι`, which asks only `0 ≤ x i`;
the free energy of `ClassicalLean.Simplex.Gibbs` takes the logarithm of a coordinate and the
Fisher–Rao metric of `ClassicalLean.Simplex.FisherRao` divides by one, so both are defined on
this smaller set.

`closedSimplex ι` has, word for word, the definition of Mathlib's `stdSimplex ℝ ι`, and the two
are equal by `rfl`. Mathlib deprecated `stdSimplex` at v4.34.0 in favour of `StdSimplex`, a
structure rather than a set, with several lemmas deprecated and no replacement; restating the
library's theorems onto it would change what they say. So the library keeps the set, under a
name for what it is, and no deprecated name ships (order 0923, J3).

## Contents

* `openSimplex`, `mem_openSimplex` — the definition and its unfolding lemma. `mem_openSimplex`
  is `Iff.rfl`: it asserts nothing beyond the definition and is here only so that later proofs
  can name the unfolding instead of relying on defeq.
* `convex_openSimplex` — the set is convex.
* `closedSimplex`, `mem_closedSimplex`, `convex_closedSimplex` — the same three for the closed
  simplex.
* `openSimplex_subset_closedSimplex` — the open simplex sits inside the closed one.

Nothing else belongs here. A fact that mentions a free energy, a metric or a numerical constant
belongs in the module that introduces that object.
-/

open Finset

namespace ClassicalLean.Simplex

variable {ι : Type*} [Fintype ι]

/-- The open probability simplex on a finite index set: the strictly positive vectors whose
coordinates sum to `1`. -/
def openSimplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {x | (∀ i, 0 < x i) ∧ ∑ i, x i = 1}

/-- Membership in `openSimplex` unfolds to its two defining conditions. This is a definitional
unfolding — the proof is `Iff.rfl` — stated so that the unfolding can be cited by name. -/
theorem mem_openSimplex {x : ι → ℝ} :
    x ∈ openSimplex ι ↔ (∀ i, 0 < x i) ∧ ∑ i, x i = 1 := Iff.rfl

/-- The open probability simplex is a convex set. -/
theorem convex_openSimplex : Convex ℝ (openSimplex ι) := by
  rintro x ⟨hx0, hx1⟩ y ⟨hy0, hy1⟩ a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.lt_or_eq with ha' | ha'
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hx0 i)) (mul_nonneg hb (hy0 i).le)
    · have hb' : (0 : ℝ) < b := by rw [← ha'] at hab; linarith
      exact add_pos_of_nonneg_of_pos (mul_nonneg ha (hx0 i).le) (mul_pos hb' (hy0 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx1, hy1]
    linarith

/-- The closed probability simplex on a finite index set: the nonnegative vectors whose
coordinates sum to `1`. The definition of Mathlib's `stdSimplex ℝ ι`, word for word; see the
module docstring for why the library names its own. -/
def closedSimplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  { f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1 }

/-- Membership in `closedSimplex` unfolds to its two defining conditions; `Iff.rfl`, stated so
that the unfolding can be cited by name. -/
theorem mem_closedSimplex {x : ι → ℝ} :
    x ∈ closedSimplex ι ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 := Iff.rfl

/-- The closed probability simplex is a convex set. -/
theorem convex_closedSimplex : Convex ℝ (closedSimplex ι) := by
  rintro x ⟨hx0, hx1⟩ y ⟨hy0, hy1⟩ a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx0 i)) (mul_nonneg hb (hy0 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx1, hy1]
    linarith

/-- The open simplex sits inside the closed one. -/
theorem openSimplex_subset_closedSimplex : openSimplex ι ⊆ closedSimplex ι :=
  fun _ hp ↦ ⟨fun i ↦ (hp.1 i).le, hp.2⟩

/-! ### The open simplex is a predicate stack

`Logic/PredicateStack.lean` defines `Stack α := List (α → Prop)` and
`Stack.Admits s x := ∀ p ∈ s, p x`, and proves that stacks weaken along sublists and splits.
Until now no *concrete* stack was ever built from a library object, so those theorems described a
construction nothing in the library used.

`openSimplex` is literally a two-predicate stack — positivity and normalisation — which is what
`mem_openSimplex` already says in conjunction form. -/

/-- The two defining conditions of the open simplex, as a `Stack`. -/
def openSimplexStack (ι : Type*) [Fintype ι] : ClassicalLean.Stack (ι → ℝ) :=
  [fun y => ∀ i, 0 < y i, fun y => ∑ i, y i = 1]

/-- **The open simplex is exactly what its stack admits.** -/
theorem admits_openSimplexStack_iff {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    ClassicalLean.Stack.Admits (openSimplexStack ι) x ↔ x ∈ openSimplex ι := by
  constructor
  · intro h
    exact ⟨h _ (List.mem_cons_self ..), h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩
  · rintro ⟨h1, h2⟩ p hp
    simp only [openSimplexStack, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact h1
    · exact h2

-- Weakening now says something about the simplex: dropping the positivity predicate leaves the
-- normalisation condition, and `Stack.admits_of_append_right` supplies it.
example {ι : Type*} [Fintype ι] {x : ι → ℝ} (hx : x ∈ openSimplex ι) :
    ClassicalLean.Stack.Admits [fun y : ι → ℝ => ∑ i, y i = 1] x :=
  ClassicalLean.Stack.admits_of_append_right
    (s := [fun y : ι → ℝ => ∀ i, 0 < y i])
    ((admits_openSimplexStack_iff x).mpr hx)

end ClassicalLean.Simplex
