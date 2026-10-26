/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

namespace Fix

theorem le_refl (h : 0 < 1) : (2 : ℕ) ≤ 2 := Nat.le_refl 2

end Fix

/-- The hypotheses of `le_refl` hold together: the short name reaches the root `le_refl`. -/
example := Fix.le_refl (by decide)
