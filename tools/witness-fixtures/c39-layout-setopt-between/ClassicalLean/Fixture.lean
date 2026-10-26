/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

/-- The hypotheses of `foo` hold together: a `set_option … in` line follows. -/
set_option pp.all false in
example := Fix.foo (n := 2) (by decide) (by decide)
