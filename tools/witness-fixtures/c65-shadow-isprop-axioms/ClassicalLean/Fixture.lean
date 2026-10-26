/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

namespace Fix

/-- A module helper; its full name is `Fix.Lean.Meta.isProp`. -/
def Lean.Meta.isProp (_ : Lean.Expr) : Lean.MetaM Bool := pure false

/-- A module helper; its full name is `Fix.Lean.collectAxioms`. -/
def Lean.collectAxioms {m : Type → Type} [Monad m] (_ : Lean.Name) : m (Array Lean.Name) :=
  pure #[]

/-- The hypotheses of `foo` hold together: cut short, nothing supplied. -/
example := @foo 2

/-- The hypotheses of `foo` hold together: on `sorry`. -/
example := foo (n := 2) sorry sorry

end Fix
