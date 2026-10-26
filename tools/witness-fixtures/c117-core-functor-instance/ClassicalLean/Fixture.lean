/-
A fixture of the witness gate's tests (order VACUITY-4): not built, not gated.
-/
import Mathlib.Algebra.Order.Group.Nat

namespace Fix

theorem foo {n : ℕ} (h : 0 < n) (h2 : n ≤ 5) : n ≤ 6 := by omega

end Fix

instance (priority := high) wgFunctor {m : Type → Type} [Monad m] : Functor m where
  map f x := x >>= fun a => pure (f a)
  mapConst a _ := pure a

/-- The hypotheses of `foo` hold together: on `sorry`. -/
example := Fix.foo (n := 2) sorry sorry
