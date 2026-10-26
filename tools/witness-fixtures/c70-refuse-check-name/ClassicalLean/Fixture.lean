/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

-- witnessGateCheck
/-- The hypotheses of `foo` hold together: `n = 2`. -/
example := Fix.foo (n := 2) (by decide) (by decide)
