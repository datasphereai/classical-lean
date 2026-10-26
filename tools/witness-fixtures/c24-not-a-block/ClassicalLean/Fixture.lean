/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

/-- A theorem whose docstring has a line that starts with the word
example and so matches the pattern. -/
theorem fix_note : (1 : ℕ) ≤ 1 := le_refl 1
