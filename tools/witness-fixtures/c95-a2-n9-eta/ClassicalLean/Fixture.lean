/-
Review (a2) probe: not built, not gated. Item 4 with the bare name written `fun x => Fix.bare x`.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem bare (x : {n : ℕ // 0 < n ∧ n ≤ 5 ∧ 7 ≤ n}) : x.1 ≤ 6 := by have := x.2; omega

end Fix

/-- The hypotheses of `bare` hold together: nothing supplied. -/
example := fun x => Fix.bare x
