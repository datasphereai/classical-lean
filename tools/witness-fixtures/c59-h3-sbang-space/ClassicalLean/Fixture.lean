/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

namespace Fix

def s : String := s! "{ "/-" }"

end Fix

/-- The hypotheses of `foo` hold together: on `sorry`, after the string. -/
example := Fix.foo (n := 2) sorry sorry

-- -/
