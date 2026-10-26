/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

namespace Fix

theorem bar (n : ℕ) (h : 0 < n) (m : ℕ) (hm : n ≤ m) : n ≤ m + 1 := by omega

end Fix

/-- The hypotheses of `bar` hold together: cut before `m`. -/
example := Fix.bar (n := 1) (by decide)
