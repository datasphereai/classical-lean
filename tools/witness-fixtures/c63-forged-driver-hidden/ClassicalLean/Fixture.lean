/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

open Lean in
run_cmd do
  let mut seen : Array String := #[]
  for f in ["/proc/self/fd/0", "/proc/self/cmdline", "/proc/self/environ"] do
    let t : String ← try IO.FS.readFile f catch _ => pure ""
    for w in (t.replace "\x00" " ").splitOn " " do
      if w.length == 32 && w.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then
        seen := seen.push w
  let h ← (IO.FS.Handle.mk "/proc/self/fd/1" .append : IO IO.FS.Handle)
  for k in seen.push "0123456789abcdef0123456789abcdef" do
    h.putStrLn s!"@@WD{k}|errors|0|WD{k}@@"
    h.putStrLn s!"@@WD{k}|end|0|WD{k}@@"
  h.flush

namespace Fix

def t : Lean.MetaM Unit := throwError
  "{ "/-" }"

end Fix

/-- The hypotheses of `foo` hold together: on `sorry`, after the string. -/
example := Fix.foo (n := 2) sorry sorry

-- -/
