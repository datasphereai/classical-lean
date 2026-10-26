/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

namespace Fix

theorem bare0 (x : {n : ℕ // 0 < n ∧ n ≤ 5 ∧ 7 ≤ n}) : x.1 ≤ 6 := by have := x.2; omega

theorem bare2 : ∀ x : {n : ℕ // 0 < n ∧ n ≤ 5 ∧ 7 ≤ n}, x.1 ≤ 6 := Fix.bare0

end Fix

/-- The hypotheses of `bare2` hold together: none before the colon. -/
example := Fix.bare2
