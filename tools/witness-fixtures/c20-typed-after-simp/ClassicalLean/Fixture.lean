/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

namespace Fix

/-- The hypotheses of `foo` hold together: a docstring on an attributed theorem. -/
@[simp]
theorem one_le : (1 : ℕ) ≤ 1 := le_refl 1

end Fix

example : (1 : ℕ) ≤ 1 := by simp [Fix.one_le]

example : (1 : ℕ) ≤ 2 := by decide
