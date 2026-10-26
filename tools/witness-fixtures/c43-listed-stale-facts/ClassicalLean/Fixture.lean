/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

namespace Fix

theorem qux (h : 0 < 1) (h2 : (1 : ℕ) < 0) : ∀ m : ℕ, m < 0 → m = 7 := by omega

end Fix

/-- The hypotheses of `qux` hold together: listed when it had one hypothesis. -/
example := Fix.qux (by decide)
