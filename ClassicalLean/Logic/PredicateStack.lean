/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Data.List.Forall2
import Mathlib.Tactic.Push

/-!
# Finite conjunctions of predicates, and weakening them

A **stack** is a `List (α → Prop)`; it *admits* `x` when every predicate in it holds of `x`.
Weakening the stack pointwise — replacing each predicate by one it implies — can only enlarge
the admitted set. That monotonicity is the content of this file.

* `Stack.Admits` — the finite conjunction `∀ p ∈ s, p x`.
* `Stack.admits_of_forall₂` — if `s'` weakens `s` pointwise then everything `s` admits, `s'`
  admits. **The theorem.**
* `Stack.admits_of_append_left`, `admits_of_append_right`, `admits_of_sublist` — adding
  predicates can only shrink the admitted set. (Until round 16 this line named
  `Stack.admits_mono_append`, which has never existed in this file.)

## What is here and what is not

The source module this came from stated three results. Only the first is a theorem:

1. Pointwise weakening enlarges the admitted set. Real, proved here by induction on
   `List.Forall₂`.
2. "The set of inputs the new stack admits and the old rejects is empty iff the new stack is at
   least as strong." That is `¬ ∃ x, Q x ∧ ¬ P x ↔ ∀ x, Q x → P x` — **pure classical logic
   about two predicates**, with no list in it. Mathlib closes it with `push_neg` — renamed
   `push Not` in Mathlib v4.29.1, which is what the `example` below now calls.
3. "The old stack rejects `x` iff some gate in it rejects `x`." That is
   `¬ (∀ p ∈ s, p x) ↔ ∃ p ∈ s, ¬ p x` — De Morgan over a list. Also `push_neg`.

Both are recorded below as `example`s rather than shipped as theorems: giving a one-tactic
consequence of `push_neg` a name of its own would add a name, not a result, and the source's
versions were long only because it was working without Mathlib and reproved classical logic by
hand with `Classical.byContradiction`. The `example`s are here so the claim "these are one
tactic" is checked by the build rather than asserted in a comment.

## Consumer audit — round 16, 2026-09-23

Round 15 set the bar on `Order/Tolerance.lean`: an instance shows a definition is inhabited; only a
*consumer* shows it earns its place. Written out, a consumer is a shipped declaration outside this
file that uses `Stack` or `Stack.Admits`, or one of their lemmas, to prove something whose statement
does not mention them. An `example` creates no constant, so it is not shipped and does not count.

Measured at the constant layer, not by reading: every constant of the built library outside this
file was checked for what its type and its proof term mention. Three mention this module, all in
`Simplex/Basic.lean`, and all are stated in its terms: `openSimplexStack` (the open simplex as a
two-predicate stack), its equation lemma `openSimplexStack.eq_1`, and `admits_openSimplexStack_iff`.
**Consumers: 0.** The one use with a consumer's shape — `Stack.admits_of_append_right` deriving the
normalisation condition of a simplex point — is an `example` (`Simplex/Basic.lean` lines 91–95).
Text layer, beside it: `grep -rn 'Stack' ClassicalLean/ --include=*.lean` outside this file returns
12 lines, all in `Simplex/Basic.lean`.

Verdict: the same standing as `Tolerance` — an instance, no consumer. The module is kept. What would
change the verdict is a shipped theorem, stated without `Stack`, whose proof goes through it. The
audit script and its full output are in round 16's fragment under `records/rounds/`.
-/

namespace ClassicalLean

/-- A stack of predicates on `α`. -/
abbrev Stack (α : Type*) := List (α → Prop)

namespace Stack

variable {α : Type*}

/-- `s` admits `x` when every predicate in `s` holds of `x` — the finite conjunction of the
stack. -/
def Admits (s : Stack α) (x : α) : Prop := ∀ p ∈ s, p x

@[simp] theorem admits_nil (x : α) : Admits [] x := by simp [Admits]

@[simp] theorem admits_cons {p : α → Prop} {s : Stack α} {x : α} :
    Admits (p :: s) x ↔ p x ∧ Admits s x := by
  simp [Admits]

/-- **Pointwise weakening enlarges the admitted set.** If `s` and `s'` have the same length and
each predicate of `s'` is implied by the corresponding one of `s`, then everything `s` admits is
admitted by `s'`.

`List.Forall₂` carries both the equal-length condition and the pointwise implication, which is
what the source encoded by a four-case recursive definition with two `False` branches. -/
theorem admits_of_forall₂ {s s' : Stack α}
    (h : List.Forall₂ (fun p p' => ∀ x, p x → p' x) s s') {x : α} (hx : Admits s x) :
    Admits s' x := by
  induction h with
  | nil => simp
  | @cons p p' rest rest' hpp' _ ih =>
    rw [admits_cons] at hx ⊢
    exact ⟨hpp' x hx.1, ih hx.2⟩

/-- Adding predicates can only shrink the admitted set. -/
theorem admits_of_append_left {s t : Stack α} {x : α} (h : Admits (s ++ t) x) : Admits s x := by
  intro p hp
  exact h p (List.mem_append_left t hp)

/-- Likewise on the right. -/
theorem admits_of_append_right {s t : Stack α} {x : α} (h : Admits (s ++ t) x) : Admits t x := by
  intro p hp
  exact h p (List.mem_append_right s hp)

/-- A sublist admits everything the whole stack admits: dropping predicates is a weakening. -/
theorem admits_of_sublist {s t : Stack α} (h : s.Sublist t) {x : α} (ht : Admits t x) :
    Admits s x := fun p hp => ht p (h.mem hp)

end Stack

/-! ## The two results that are one tactic

Recorded as `example`s so that the claim is machine-checked rather than asserted. Neither is
shipped under a name: a named wrapper around `push_neg` is a name, not a theorem. -/

/-- "No input is admitted by the new stack and rejected by the old" is exactly "the new stack is
at least as strong". Note there is no list in this statement at all — it is a fact about two
predicates. -/
example {α : Type*} (P Q : α → Prop) : (¬ ∃ x, Q x ∧ ¬ P x) ↔ (∀ x, Q x → P x) := by
  push Not; rfl

/-- A stack rejects `x` exactly when one of its predicates does — De Morgan over a list. -/
example {α : Type*} (s : Stack α) (x : α) :
    ¬ Stack.Admits s x ↔ ∃ p ∈ s, ¬ p x := by
  simp [Stack.Admits]

end ClassicalLean
