/-
Review (a2) probe: not built, not gated. Item 4 with the binder from `variable`.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

variable (x : {n : ℕ // 0 < n ∧ n ≤ 5 ∧ 7 ≤ n})

theorem bare : x.1 ≤ 6 := by have := x.2; omega

end Fix

/-- The hypotheses of `bare` hold together: nothing supplied. -/
example := Fix.bare
