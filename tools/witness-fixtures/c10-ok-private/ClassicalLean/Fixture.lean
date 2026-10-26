/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

namespace Fix

private theorem two_pos : 0 < (2 : ℕ) := by decide

end Fix

/-- The hypotheses of `foo` hold together: with a private lemma. -/
example := Fix.foo (n := 2) Fix.two_pos (by decide)
