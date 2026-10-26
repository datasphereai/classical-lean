/-
A probe of review a3 (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

namespace Fix

theorem bare (x : {n : ℕ // 0 < n ∧ n ≤ 5 ∧ 7 ≤ n}) : x.1 ≤ 6 := by have := x.2; omega

open Lean Elab Term in
elab "plant%" : term => do
  let src := (← getFileMap).source
  let pre := (src.splitOn ("theorem " ++ "other")).head!
  let p : String.Pos.Raw := ⟨pre.utf8ByteSize + 8⟩
  addTermInfo' ((mkIdent `Fix.bare).raw.setInfo (SourceInfo.synthetic p ⟨p.byteIdx + 5⟩))
    (mkConst ``Fix.bare) (isBinder := true)
  return mkConst ``True

theorem other : ∀ _y : ℕ, plant% := fun _ => trivial

end Fix

/-- The hypotheses of `bare` hold together: nothing supplied. -/
example := Fix.bare
