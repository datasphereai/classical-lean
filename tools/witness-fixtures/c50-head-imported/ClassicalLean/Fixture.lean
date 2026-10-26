/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

/-- The hypotheses of `Nat.le_of_lt` hold together: a Mathlib theorem, not this module's. -/
example := Nat.le_of_lt (n := 1) (m := 2) (by decide)
