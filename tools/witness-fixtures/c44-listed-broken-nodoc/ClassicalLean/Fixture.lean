/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

namespace Fix

theorem big : (10 : ℕ) < 11 := by native_decide

theorem useBig (h : (10 : ℕ) < 11) : (10 : ℕ) ≤ 11 := Nat.le_of_lt h

end Fix

example := Fix.useBig Fix.big
