/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

/-- The hypotheses of `foo` hold together: the first. -/
example := Fix.foo (n := 2) (by decide) (by decide)
/-- The hypotheses of `foo` hold together: the second, right below. -/
example := Fix.foo (n := 3) (by decide) (by decide)
