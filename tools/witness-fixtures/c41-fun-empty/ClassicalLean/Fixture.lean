/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

/-- The hypotheses of `foo` hold together: over `Empty`. -/
example := fun (e : Empty) => Fix.foo (n := 9) e.elim e.elim
