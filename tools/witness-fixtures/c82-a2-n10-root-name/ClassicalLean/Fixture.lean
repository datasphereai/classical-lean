/-
Review (a2) probe: not built, not gated. Item 4 with the theorem declared through `_root_`.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Other

theorem _root_.Fix.bare (x : {n : ℕ // 0 < n ∧ n ≤ 5 ∧ 7 ≤ n}) : x.1 ≤ 6 := by have := x.2; omega

end Other

namespace Fix
theorem unused : True := trivial
end Fix

/-- The hypotheses of `bare` hold together: nothing supplied. -/
example := Fix.bare
