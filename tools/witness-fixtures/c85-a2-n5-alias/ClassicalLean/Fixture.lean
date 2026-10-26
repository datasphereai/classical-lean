/-
Review (a2) probe: not built, not gated. Item 4 through an `alias`.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem bare0 (x : {n : ℕ // 0 < n ∧ n ≤ 5 ∧ 7 ≤ n}) : x.1 ≤ 6 := by have := x.2; omega

alias bare := bare0

end Fix

/-- The hypotheses of `bare` hold together: nothing supplied. -/
example := Fix.bare
