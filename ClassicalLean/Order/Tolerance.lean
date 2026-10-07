/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Nat
import Mathlib.Data.Nat.Dist
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Analysis.Quaternion

/-!
# Tolerance structures: a graded family of relations from a symmetric distance

A **tolerance** on a type `T` is a symmetric `E`-valued distance vanishing on the diagonal,
where the widths `E` are preordered with a least element:

    dist : T → T → E,   dist a a = ⊥,   dist a b = dist b a.

It generates a *graded family* of relations, one per width:

    a ≈[ε] b   ⟺   dist a b ≤ ε      (`Tolerance.close`)

Each member is reflexive and symmetric, the family is monotone in `ε`, and — when the widths are
a partial order and the distance separates points — the member at `⊥` is equality itself. So the
family interpolates between equality and the total relation, which is the point of naming it.

This is a pseudometric with the codomain and its order abstracted out. Mathlib's
`PseudoMetricSpace` fixes `E = ℝ` and carries a triangle inequality; nothing here needs either,
and dropping both is what lets `E` be `ℕ`, a lattice of intervals, or a bare preorder of
tolerances.

**No triangle inequality is assumed**, so `close · · ε` is reflexive and symmetric but *not*
transitive — it is a tolerance relation, not an equivalence, which is the usual situation for
"within ε". Transitivity would need `dist a c ≤ dist a b + dist b c` and an addition on `E`.

## Status: speculative

**This module is recorded as speculative, and the word is used in a precise sense.**  It is not
uninhabited and not disconnected: `natTolerance` and `pseudoMetricTolerance` are instances, and the
latter makes every metric object in the library one — the simplex's ambient `ι → ℝ` and the
quaternions among them.  What is missing is a *consumer*.

Measured: `grep -rn 'Tolerance' ClassicalLean/ --include=*.lean` outside this file returns **0**.
No theorem anywhere in the library is stated in terms of `Tolerance`, and none needs to be.  For a
metric space, every result here — `close_rfl`, `close_mono`, `close_symm`, `close_bot_iff_eq` — is
a one-line consequence of Mathlib's `dist` API, so the generality buys nothing that is currently
used.  The one thing it does buy, widths outside `ℝ≥0`, has exactly one witness, `natTolerance`,
and nothing consumes that either.

By this project's own standard — "porting would add names, not results" — that
makes the structure a **generalisation in search of a use case**, not a result.  It is kept rather
than retired because the abstraction is correct and cheap, and because a future module that needs
graded closeness with non-real widths (interval arithmetic, a preorder of precisions, an integer
tolerance on a sequence) would want exactly this.  It should not be cited as evidence that the
library does order theory, and a reader deciding what to build next should treat it as **unproven
in its purpose**, not as settled infrastructure.

What would retire the word: a theorem elsewhere in the library whose statement genuinely needs
`Tolerance` rather than `dist` — that is, one where `E` is not `ℝ≥0`, or where the triangle
inequality is unavailable.

## Provenance

Ported from a module in the source corpus that stated the same structure with the order
hand-rolled: five fields carrying `width_le`, `width_zero`, reflexivity and transitivity of
`width_le`, and "`width_zero` is least". **Those five are Mathlib's `[Preorder E] [OrderBot E]`**,
so the structure here has two fields rather than seven, and the ε → 0 theorem takes
`[PartialOrder E]` instead of an antisymmetry hypothesis threaded through by hand. The
interpretation the source attached is dropped; what is proved is a fact about symmetric
distances, and is stated that way.
-/

namespace ClassicalLean

variable {T E : Type*}

/-- A symmetric `E`-valued distance on `T` vanishing on the diagonal. The widths `E` are
preordered with a least element `⊥`, which is all the order structure the graded family needs. -/
structure Tolerance (T E : Type*) [Preorder E] [OrderBot E] where
  /-- The distance between two points, measured as a width. -/
  dist : T → T → E
  /-- A point is at zero distance from itself. -/
  dist_self : ∀ a, dist a a = ⊥
  /-- The distance is symmetric. -/
  dist_symm : ∀ a b, dist a b = dist b a

namespace Tolerance

section Graded

variable [Preorder E] [OrderBot E] (τ : Tolerance T E)

/-- `close a b ε` — the members of the graded family: `a` and `b` agree to within width `ε`. -/
def close (a b : T) (ε : E) : Prop := τ.dist a b ≤ ε

/-- Every member of the family is reflexive, already at width `⊥`. -/
theorem close_rfl (a : T) : τ.close a a ⊥ := by
  simp [close, τ.dist_self]

/-- Equality implies closeness at *every* width — the passage from strict equality to the graded
family. -/
theorem close_of_eq {a b : T} (h : a = b) (ε : E) : τ.close a b ε := by
  subst h
  exact le_trans (le_of_eq (τ.dist_self a)) bot_le

/-- The family is monotone in the width: widening a tolerance never breaks the relation. -/
theorem close_mono {a b : T} {ε₁ ε₂ : E} (h : τ.close a b ε₁) (hε : ε₁ ≤ ε₂) :
    τ.close a b ε₂ := le_trans h hε

/-- Every member of the family is symmetric, inherited from `dist_symm`. -/
theorem close_symm {a b : T} {ε : E} (h : τ.close a b ε) : τ.close b a ε := by
  rwa [close, τ.dist_symm]

end Graded

section Separated

variable [PartialOrder E] [OrderBot E] (τ : Tolerance T E)

/-- **The ε → 0 limit.** When the widths form a partial order and the distance *separates*
points, the member of the family at `⊥` is exactly equality.

Both hypotheses do work. Antisymmetry turns the one-sided `dist a b ≤ ⊥` into `dist a b = ⊥`
(`le_bot_iff`); without separation that only gives the quotient identifying points at zero
distance, which is precisely how a pseudometric differs from a metric. Separation is a
hypothesis rather than a field so the structure can still be instantiated where it fails. -/
theorem close_bot_iff_eq
    (separated : ∀ a b : T, τ.dist a b = ⊥ → a = b) (a b : T) :
    τ.close a b ⊥ ↔ a = b := by
  constructor
  · intro h
    exact separated a b (le_bot_iff.mp h)
  · intro h
    exact τ.close_of_eq h ⊥

end Separated

end Tolerance

/-! ### Instances

The header claims this structure is "a pseudometric with the codomain and its order abstracted
out".  `pseudoMetricTolerance` below is that claim proved rather than asserted, and it is what
connects the definition to the rest of the library: every pseudometric space becomes a tolerance
with widths in `ℝ≥0`, so the simplex's ambient `ι → ℝ` and `Geometry`'s quaternions are instances
without any further work.

`natTolerance` is *not* subsumed by it, and that is the point of abstracting `E`: its widths are
`ℕ`, not `ℝ≥0`. -/

/-- **Every pseudometric space is a tolerance**, with widths in `ℝ≥0`.

This is the precise sense in which the structure generalises `PseudoMetricSpace`: drop the
triangle inequality, keep `nndist_self` and `nndist_comm`, and let the codomain vary.  `ℝ≥0` rather
than `ℝ` because the widths need an `OrderBot`, which `ℝ` does not have — that is the reason the
abstraction is stated over an `OrderBot` preorder at all. -/
noncomputable def pseudoMetricTolerance (α : Type*) [PseudoMetricSpace α] :
    Tolerance α NNReal where
  dist := nndist
  dist_self := nndist_self
  dist_symm := nndist_comm

/-- In a genuine metric space the distance separates points, so the family's `⊥` member is
equality — `close_bot_iff_eq` applied to the bridge. -/
theorem pseudoMetricTolerance_close_bot_iff {α : Type*} [MetricSpace α] (a b : α) :
    (pseudoMetricTolerance α).close a b ⊥ ↔ a = b :=
  (pseudoMetricTolerance α).close_bot_iff_eq
    (fun _ _ h => by simpa using nndist_eq_zero.mp h) a b

-- The bridge reaches the library's own objects: the simplex's ambient space, and the quaternions
-- that `Geometry/S3Quaternion.lean` and `Geometry/SU2SO3.lean` work in.
example (ι : Type*) [Fintype ι] (x y : ι → ℝ) :
    (pseudoMetricTolerance (ι → ℝ)).close x y ⊥ ↔ x = y :=
  pseudoMetricTolerance_close_bot_iff x y

example (p q : Quaternion ℝ) : (pseudoMetricTolerance (Quaternion ℝ)).close p q ⊥ ↔ p = q :=
  pseudoMetricTolerance_close_bot_iff p q

/-- `ℕ` with its absolute difference is a tolerance structure whose widths are `ℕ`, so it is **not**
an instance of `pseudoMetricTolerance` — that one has widths in `ℝ≥0`.  It is the witness that
varying `E` buys something. `Nat.dist` is Mathlib's; the source defined its own copy. -/
def natTolerance : Tolerance ℕ ℕ where
  dist := Nat.dist
  dist_self := Nat.dist_self
  dist_symm := Nat.dist_comm

/-- On `ℕ` the distance separates points, so the family's `⊥` member is equality. -/
example (a b : ℕ) : natTolerance.close a b 0 ↔ a = b :=
  natTolerance.close_bot_iff_eq (fun _ _ h => Nat.eq_of_dist_eq_zero h) a b

/-- Closeness at a positive width is strictly weaker than equality: `1` and `2` are within `1` of
each other and are not equal. This is why the family is worth grading. -/
example : natTolerance.close 1 2 1 ∧ (1 : ℕ) ≠ 2 := by
  refine ⟨?_, by decide⟩
  simp [Tolerance.close, natTolerance, Nat.dist]

end ClassicalLean
