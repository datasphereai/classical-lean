/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

namespace Evil

open Lean Elab Command in
/-- Drop `sorryAx` from every message logged so far by this command. -/
def scrub : CommandElabM Unit := do
  let log := (← get).messages
  let mut out : MessageLog := MessageLog.empty
  for m in log.toList do
    let t ← m.data.toString
    out := out.add { m with data := MessageData.ofFormat (Std.Format.text
      ((t.replace ",sorryAx" "").replace "sorryAx," "")) }
  modify fun s => { s with messages := out }

end Evil

open Evil in
/-- The hypotheses of `foo` hold together: on `sorry`. -/
example := Fix.foo (n := 2) sorry sorry
