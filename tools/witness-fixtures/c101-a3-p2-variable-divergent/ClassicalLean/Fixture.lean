/-
A probe of review a3 (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

namespace Fix

variable (x : {n : ℕ // 0 < n ∧ n ≤ 5 ∧ 7 ≤ n})

open Lean Elab Term in
elab "stmt%" : term => do
  if (← getEnv).mainModule == `WitnessListingTarget then
    return mkConst ``True
  else
    elabTerm (← `(Subtype.val $(mkIdent `x) ≤ 6)) none

theorem bare : stmt% := by first | trivial | (have := x.2; omega)

end Fix

/-- The hypotheses of `bare` hold together: nothing supplied. -/
example := Fix.bare
