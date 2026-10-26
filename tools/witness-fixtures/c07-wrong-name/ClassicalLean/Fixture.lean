/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

namespace Fix.A

theorem baz (h : 0 < 1) : (1 : ℕ) ≤ 1 := le_refl 1

end Fix.A

namespace Fix.B

theorem baz (h : 0 < 1) : (1 : ℕ) ≤ 2 := by decide

end Fix.B

/-- The hypotheses of `A.baz` hold together: but the value is `B.baz`. -/
example := Fix.B.baz (by decide)
