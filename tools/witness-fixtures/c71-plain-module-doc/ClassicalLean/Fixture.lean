import Mathlib.Algebra.Order.Group.Nat

/-! # A plain module

Its docstring follows the imports, as the library's do.
-/

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

/-- The hypotheses of `foo` hold together: `n = 2`. -/
example := Fix.foo (n := 2) (by decide) (by decide)
