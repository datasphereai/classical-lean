/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

/-! A control of ruling 4: every command kind and attribute on the gate's lists. -/

universe u

namespace Fix

section

variable {α : Type u} [Inhabited α] (k : ℕ) (hk : 0 < k)

include hk in
theorem incl : 0 < k := hk

omit [Inhabited α] in
theorem om (a : α) : a = a := rfl

end

structure Pt where
  x : ℕ
  y : ℕ

def Pt.sum (p : Pt) : ℕ := p.x + p.y

abbrev two : ℕ := 2

@[simp] lemma two_eq : two = 2 := rfl

instance : Inhabited Pt := ⟨⟨0, 0⟩⟩

def Wrap : Type := ℕ

def wrapInh : Inhabited Wrap := ⟨(0 : ℕ)⟩

attribute [local instance] wrapInh

set_option maxHeartbeats 200000 in
theorem hb : two + two = 4 := by simp

open Nat in
theorem op : succ 1 = 2 := rfl

end Fix

/-- The hypotheses of `foo` hold together: `n = 2`. -/
example := Fix.foo (n := 2) (by decide) (by decide)
