import Mathlib.Algebra.Order.Group.Nat
import Std.Tactic.BVDecide

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

theorem bv : ∀ x : BitVec 8, x * x ≠ 2 := by intro x; bv_decide

end Fix

/-- The hypotheses of `foo` hold together: n = 2. -/
example := Fix.foo (n := 2) (by decide) (by decide)
