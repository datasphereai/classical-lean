/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

namespace Fix

theorem bar : (1 : ℕ) ≤ 6 := by decide

end Fix

open Lean Elab Command in
run_cmd do
  let t ← liftCoreM (IO.FS.readFile (← getFileName))
  let ns := (t.splitOn "@@WG").filterMap fun p =>
    let x := String.mk (p.toList.takeWhile Char.isAlphanum)
    if x.length == 16 then some x else none
  match ns.head? with
  | some k => logInfo m!"@@WG{k}|29|head|Fix.foo|WG{k}@@ @@WG{k}|29|zzz|"
  | none => pure ()

/-- The hypotheses of `foo` hold together: the head is forged. -/
example := Fix.bar -- forged-target
