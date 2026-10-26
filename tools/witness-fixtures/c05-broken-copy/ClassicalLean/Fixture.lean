/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

namespace Fix

theorem qux (h : 0 < 1) : (2 : ℕ) + 2 = 5 := by decide

end Fix

/-- The hypotheses of `qux` hold together: its own proof fails. -/
example := Fix.qux (by decide)
