/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

/-- The hypotheses of `foo` hold
together, in the older form. -/
example : ∃ n : ℕ, 0 < n ∧ n ≤ 5 := ⟨2, by decide, by decide⟩
