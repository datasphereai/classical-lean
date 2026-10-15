/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Data.EReal.Operations
import Mathlib.Data.Matrix.Mul

/-!
# The convex conjugate

For `f` on `ι → ℝ` (finitely many coordinates), the *convex conjugate* is
`f* y = ⨆ x, (y ⬝ x − f x)` (Fenchel 1949). It is valued in the extended reals `EReal`, so the
supremum of an unbounded family is `⊤`, not a junk value.

* `convexConjugate f` — defined for `f` valued in `EReal`, so that `f*` (which is `EReal`-valued)
  has a conjugate too.
* `dotProduct_le_add_convexConjugate` — **Fenchel–Young**: for a real-valued `f`,
  `y ⬝ x ≤ f x + f* y`.
* `convexConjugate_anti` — `f ≤ g` gives `g* ≤ f*`.
* `convexConjugate_convexConjugate_le` — `f** ≤ f`.
* `sub_le_convexConjugate` and `convexConjugate_le_iff` — the two sides of the supremum (each
  `y ⬝ x − f x` is below `f* y`; `f* y ≤ c` exactly when every one is), for proofs that compute a
  conjugate (item 117 of the plan).

The plan's row (MATH-PLAN-library-2, item 79) asks for a real-valued `f`. Fenchel–Young is
stated for exactly that (`f` real, read in `EReal`); the other two are stated for every
`EReal`-valued `f`, which contains the plan's case (`f := fun x ↦ (g x : EReal)`), so they are
wider than the row, not narrower.

## Hypotheses, and Lean's junk values

The junk values below are checked by the seven `example`s at the end of this file (moved there by
order LEAN-29 from order LEAN-27's scratch file), against this module's own `convexConjugate`
except the real supremum, which cannot use it:

* Fenchel–Young needs `f` real-valued. Over `EReal` it fails in two ways (cold review r79 found
  the second): if `f x = ⊥` at some `x`, then `f* y = (y ⬝ x) − ⊥ = ⊤` and the right side is
  `⊥ + ⊤ = ⊥` (Mathlib's convention); and if `f` is `⊤` everywhere, then `f* = ⊥` everywhere and
  the right side is `⊤ + ⊥ = ⊥`. A single value `⊤` is harmless. A real-valued `f` avoids both.
* The conjugate is valued in `EReal`, not `ℝ`: in `ℝ`, Lean's supremum of an unbounded family is
  `0` (`⨆ x : ℝ, x = 0`), so for `f = 0` on `ℝ¹` and `y = 1` a real-valued conjugate would be `0`
  and Fenchel–Young at `x = 1` would read `1 ≤ 0 + 0`.
* `convexConjugate_anti` needs `f ≤ g`: `f = 1`, `g = 0` give `g* 0 = 0 > −1 = f* 0`.
* `convexConjugate_convexConjugate_le` has no hypothesis. At a point where `f x = ⊥`, every
  `f* y` is `⊤` and `x ⬝ y − ⊤ = ⊥`; where `f x = ⊤` there is nothing to show.

The proofs use `le_iSup`, `iSup_le`, `iSup_mono` and Mathlib's `EReal.sub_le_iff_le_add`, whose
side conditions (`b ≠ ⊥ ∨ c ≠ ⊤`, `b ≠ ⊤ ∨ c ≠ ⊥`) are where the cases above are split.

## Mathlib at v4.34.0

Searched before this file was written (MATH-PLAN-library-2, row 79, re-run by its check script in
order LEAN-27): `convexConjugate|convex conjugate|fenchel|legendre.?(transform|fenchel)` 0 lines
in pinned Mathlib and 0 in Mathlib master at `2da3ab0a` (the plan's clone); 2 lines in the
library (LogSumExp's search note and SecondOrder's prose).
-/

open Matrix

namespace ClassicalLean.Analysis.ConvexConjugate

variable {ι : Type*} [Fintype ι]

/-- The convex conjugate `f* y = ⨆ x, (y ⬝ x − f x)`, valued in the extended reals. -/
noncomputable def convexConjugate (f : (ι → ℝ) → EReal) (y : ι → ℝ) : EReal :=
  ⨆ x, ((y ⬝ᵥ x : ℝ) : EReal) - f x

/-- Each term is below the supremum: `y ⬝ x − f x ≤ f* y`. -/
theorem sub_le_convexConjugate (f : (ι → ℝ) → EReal) (x y : ι → ℝ) :
    ((y ⬝ᵥ x : ℝ) : EReal) - f x ≤ convexConjugate f y :=
  le_iSup (fun z ↦ ((y ⬝ᵥ z : ℝ) : EReal) - f z) x

/-- `f* y ≤ c` exactly when `y ⬝ x − f x ≤ c` for every `x` (cold review r79). -/
theorem convexConjugate_le_iff {f : (ι → ℝ) → EReal} {y : ι → ℝ} {c : EReal} :
    convexConjugate f y ≤ c ↔ ∀ x, ((y ⬝ᵥ x : ℝ) : EReal) - f x ≤ c :=
  iSup_le_iff

/-- **Fenchel–Young.** For a real-valued `f`, `y ⬝ x ≤ f x + f* y` for every `x` and `y`. -/
theorem dotProduct_le_add_convexConjugate (f : (ι → ℝ) → ℝ) (x y : ι → ℝ) :
    ((y ⬝ᵥ x : ℝ) : EReal) ≤ (f x : EReal) + convexConjugate (fun z ↦ (f z : EReal)) y := by
  rw [add_comm,
    ← EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))]
  exact sub_le_convexConjugate (fun z ↦ (f z : EReal)) x y

/-- **The conjugate reverses order.** `f ≤ g` gives `g* ≤ f*`. -/
theorem convexConjugate_anti {f g : (ι → ℝ) → EReal} (h : f ≤ g) :
    convexConjugate g ≤ convexConjugate f :=
  fun _ ↦ iSup_mono fun x ↦ EReal.sub_le_sub le_rfl (h x)

/-- **The biconjugate lies below.** `f** ≤ f`, for every `f` valued in `EReal`. -/
theorem convexConjugate_convexConjugate_le (f : (ι → ℝ) → EReal) :
    convexConjugate (convexConjugate f) ≤ f := by
  intro x
  refine iSup_le fun y ↦ ?_
  rcases eq_or_ne (convexConjugate f y) ⊤ with hy | hy
  · rw [hy, EReal.sub_top]
    exact bot_le
  rcases eq_or_ne (f x) ⊤ with hx | hx
  · rw [hx]
    exact le_top
  have h := sub_le_convexConjugate f x y
  have hxb : f x ≠ ⊥ := by
    intro hb
    rw [hb, EReal.coe_sub_bot, top_le_iff] at h
    exact hy h
  rw [EReal.sub_le_iff_le_add (.inl hxb) (.inl hx)] at h
  rw [EReal.sub_le_iff_le_add (.inr hx) (.inl hy), dotProduct_comm, add_comm]
  exact h

/-- The hypothesis of `convexConjugate_anti` can be met with the order really reversing:
`f = 0 ≤ g = 1` on `ℝ²`, where `g* 0 = −1 < 0 = f* 0` (the same values on `ℝ¹` are the last two
`example`s at the end of this file). -/
example : ∃ f g : (Fin 2 → ℝ) → EReal, f ≤ g := ⟨0, 1, fun _ ↦ zero_le_one⟩

end ClassicalLean.Analysis.ConvexConjugate

open ClassicalLean.Analysis.ConvexConjugate in
/-- `f = ⊥` everywhere on `ℝ¹`: its conjugate at `0` is `⊤`. -/
example : convexConjugate (fun _ : Fin 1 → ℝ ↦ (⊥ : EReal)) 0 = ⊤ := by
  simp [convexConjugate]

open ClassicalLean.Analysis.ConvexConjugate in
/-- `f = ⊥` everywhere on `ℝ¹`: Fenchel–Young fails at `x = y = 0`, as `⊥ + ⊤ = ⊥`. -/
example : ¬ (((0 : Fin 1 → ℝ) ⬝ᵥ 0 : ℝ) : EReal) ≤
    (⊥ : EReal) + convexConjugate (fun _ : Fin 1 → ℝ ↦ (⊥ : EReal)) 0 := by
  simp [convexConjugate]

open ClassicalLean.Analysis.ConvexConjugate in
/-- `f = ⊤` everywhere on `ℝ¹` (cold review r79): its conjugate at `0` is `⊥`. -/
example : convexConjugate (fun _ : Fin 1 → ℝ ↦ (⊤ : EReal)) 0 = ⊥ := by
  simp [convexConjugate]

open ClassicalLean.Analysis.ConvexConjugate in
/-- `f = ⊤` everywhere on `ℝ¹`: Fenchel–Young fails at `x = y = 0`, as `⊤ + ⊥ = ⊥`. -/
example : ¬ (((0 : Fin 1 → ℝ) ⬝ᵥ 0 : ℝ) : EReal) ≤
    (⊤ : EReal) + convexConjugate (fun _ : Fin 1 → ℝ ↦ (⊤ : EReal)) 0 := by
  simp [convexConjugate]

/-- In `ℝ`, Lean's supremum of an unbounded family is `0`: `⨆ x, 1 ⬝ x − 0 = 0` on `ℝ¹`. -/
example : (⨆ x : Fin 1 → ℝ, (1 : Fin 1 → ℝ) ⬝ᵥ x - 0) = 0 := by
  apply Real.iSup_of_not_bddAbove
  rintro ⟨b, hb⟩
  have := hb ⟨fun _ ↦ b + 1, rfl⟩
  simp [dotProduct] at this
  linarith

open ClassicalLean.Analysis.ConvexConjugate in
/-- `g = 0` on `ℝ¹`: its conjugate at `0` is `0` (the `g` of the next example). -/
example : convexConjugate (fun _ : Fin 1 → ℝ ↦ (0 : EReal)) 0 = 0 := by simp [convexConjugate]

open ClassicalLean.Analysis.ConvexConjugate in
/-- `f = 1 ≰ g = 0`: `f* 0 = −1 < 0 = g* 0`, so `convexConjugate_anti` needs `f ≤ g`. -/
example : convexConjugate (fun _ : Fin 1 → ℝ ↦ (1 : EReal)) 0 = -1 := by simp [convexConjugate]
