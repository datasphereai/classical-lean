/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

/-- The hypotheses of `foo` hold together: a blank line follows. -/

example := Fix.foo (n := 1) (by decide) (by decide)

/-- The hypotheses of `foo` hold together: a line comment follows. -/
-- a line comment
example := Fix.foo (n := 2) (by decide) (by decide)

/-- The hypotheses of `foo` hold together: a plain comment follows. -/
/- a plain comment -/
example := Fix.foo (n := 3) (by decide) (by decide)

/-- The hypotheses of `foo` hold together: an attribute follows. -/
@[simp]
example := Fix.foo (n := 4) (by decide) (by decide)

/-- The hypotheses of `foo` hold together: a modifier follows. -/
private
example := Fix.foo (n := 5) (by decide) (by decide)

open Nat in
/-- The hypotheses of `foo` hold together: under an `open … in` line. -/
example := Fix.foo (n := 1) (by omega) (by decide)

set_option pp.all false in
/-- The hypotheses of `foo` hold together: under a `set_option … in` line. -/
example := Fix.foo (n := 2) (by omega) (by decide)
