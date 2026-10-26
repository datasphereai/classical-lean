/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

section
variable (e : Empty)

/-- The hypotheses of `foo` hold together: through a section variable. -/
example := Fix.foo (n := 9) e.elim e.elim

end
