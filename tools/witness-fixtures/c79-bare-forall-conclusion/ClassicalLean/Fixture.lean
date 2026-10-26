/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

namespace Fix

theorem allNonneg : ∀ n : ℕ, 0 ≤ n := fun n => Nat.zero_le n

end Fix

/-- The hypotheses of `allNonneg` hold together: none before the colon. -/
example := @Fix.allNonneg
