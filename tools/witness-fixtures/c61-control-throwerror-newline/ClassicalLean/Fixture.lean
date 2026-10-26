/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

namespace Fix

def t : Lean.MetaM Unit := throwError
  "{ (1 : ℕ) }"

end Fix

example : (1 : ℕ) = 1 := rfl
