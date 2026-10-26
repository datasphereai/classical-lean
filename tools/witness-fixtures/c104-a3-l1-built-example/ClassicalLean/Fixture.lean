/-
A probe of review a3 (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

open Lean Elab Command in
elab "mkex" : command => do
  match Parser.runParserCategory (← getEnv) `command ("exam" ++ "ple := Fix.foo (n := 2) sorry sorry") with
  | .ok stx => elabCommand stx
  | .error e => throwError e

mkex
