/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Algebra.Order.Group.Nat

/-!
# Superadditive functions on the naturals

A function `f : ℕ → ℕ` is **superadditive** when `f m + f n ≤ f (m + n)`. Over `ℕ` this single
condition is stronger than it looks: it forces monotonicity, and it forces at-least-linear
growth from the single value `f 1`.

* `Superadditive.monotone` — superadditivity alone implies `Monotone f`, because `ℕ` has no
  negative values to cancel the extra term.
* `Superadditive.linear_le` — `n * f 1 ≤ f n` for every `n`. The growth rate is pinned from
  below by one value.
* `Superadditive.unbounded` — if `0 < f 1` then `f` exceeds every bound.

Mathlib has `Subadditive` (for Fekete's lemma, on `ℝ`) and `SubadditiveHomClass`, but nothing
for the superadditive direction on `ℕ`, so these are proved here.

## Provenance

The mathematics is the load-bearing part of a module in the source corpus that packaged it as a
four-field structure — a cost function with `f 0 = 0`, `0 < f 1`, `Monotone f` and
superadditivity — in order to argue that a certain quantity compounds.

Two things changed on the way in. The interpretation is dropped: what is proved is a fact about
superadditive functions, and it is stated that way. And **the structure had a redundant field**:
`Monotone f` is a *consequence* of superadditivity over `ℕ` (`Superadditive.monotone` below),
not an independent assumption. Assuming it was harmless but made the result look like it needed
more than it does.

`f 0 = 0` is not assumed either. It follows for the growth results, and where it is genuinely
needed it is derivable: superadditivity at `m = n = 0` gives `f 0 + f 0 ≤ f 0`, hence `f 0 = 0`
(`Superadditive.map_zero`).

## Consumer audit — round 16, 2026-09-23

Round 15 set the bar on `Order/Tolerance.lean`: an instance shows a definition is inhabited; only a
*consumer* shows it earns its place. Written out, a consumer is a shipped declaration outside this
file that uses `Superadditive` or one of its lemmas to prove something whose statement does not
mention `Superadditive`. An `example` creates no constant, so it is not shipped and does not count.

Measured at the constant layer, not by reading: every constant of the built library outside this
file was checked for what its type and its proof term mention. Exactly one mentions this module —
`superadditive_mersenne : Superadditive mersenne` in `NumberTheory/Mersenne.lean` — and it is an
instance, stated in this module's terms. **Consumers: 0.** The two uses with a consumer's shape,
`superadditive_mersenne.monotone` and `superadditive_mersenne.linear_le`, are `example`s
(`Mersenne.lean` lines 171 and 173). Text layer, beside it: `grep -rn 'Superadditive'
ClassicalLean/ --include=*.lean` outside this file returns 6 lines, all in `Mersenne.lean`.

Verdict: the same standing as `Tolerance` — an instance, no consumer. The module is kept. What would
change the verdict is a shipped theorem, stated without `Superadditive`, whose proof goes through
it. The audit script and its full output are in round 16's fragment under `records/rounds/`.
-/

namespace ClassicalLean

/-- `f : ℕ → ℕ` is superadditive when `f m + f n ≤ f (m + n)`. -/
def Superadditive (f : ℕ → ℕ) : Prop := ∀ m n, f m + f n ≤ f (m + n)

namespace Superadditive

variable {f : ℕ → ℕ} (hf : Superadditive f)
include hf

/-- A superadditive function on `ℕ` vanishes at `0`: superadditivity at `m = n = 0` reads
`f 0 + f 0 ≤ f 0`, which over `ℕ` forces `f 0 = 0`. It does not have to be assumed. -/
theorem map_zero : f 0 = 0 := by
  have h := hf 0 0
  simp only [Nat.add_zero] at h
  omega

/-- **Superadditivity implies monotonicity on `ℕ`.** Writing `n ≤ m` as `m = n + k`,
`f n ≤ f n + f k ≤ f (n + k) = f m`; the first step is where `ℕ` is used, since there is nothing
negative for `f k` to subtract. This is why a separate monotonicity assumption is redundant. -/
theorem monotone : Monotone f := by
  intro n m hnm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  calc f n ≤ f n + f k := Nat.le_add_right _ _
    _ ≤ f (n + k) := hf n k

/-- **At-least-linear growth.** `n * f 1 ≤ f n`: a superadditive function grows at least as fast
as the linear function through `f 1`. By induction, using superadditivity to split off one unit
at each step. -/
theorem linear_le (n : ℕ) : n * f 1 ≤ f n := by
  induction n with
  | zero => simp [hf.map_zero]
  | succ n ih =>
    calc (n + 1) * f 1 = n * f 1 + f 1 := Nat.succ_mul n (f 1)
      _ ≤ f n + f 1 := Nat.add_le_add_right ih (f 1)
      _ ≤ f (n + 1) := hf n 1

/-- **Unboundedness.** If `f 1` is positive then `f` exceeds every bound — take `N = C + 1` and
apply `linear_le`. -/
theorem unbounded (h1 : 0 < f 1) : ∀ C : ℕ, ∃ N : ℕ, C < f N := by
  intro C
  refine ⟨C + 1, ?_⟩
  have hlin : (C + 1) * f 1 ≤ f (C + 1) := hf.linear_le (C + 1)
  have : C + 1 ≤ (C + 1) * f 1 := Nat.le_mul_of_pos_right _ h1
  omega

/-- With `0 < f 1`, the function is strictly positive from `1` onward. -/
theorem pos_of_pos (h1 : 0 < f 1) {n : ℕ} (hn : 0 < n) : 0 < f n := by
  have := hf.monotone (Nat.one_le_iff_ne_zero.mpr hn.ne')
  omega

end Superadditive

/-- `linear_le` is sharp: for `f = id` it holds with equality, so no bound better than
`n * f 1 ≤ f n` is available from superadditivity alone. -/
example (n : ℕ) : n * (id 1) = id n := by simp

end ClassicalLean

/-- The hypotheses of `Superadditive.map_zero` hold together: `f n = n * n`, superadditive with room
to spare (`(m + n) * (m + n) - m * m - n * n = 2 * m * n`), so not the identity's equality. -/
example := ClassicalLean.Superadditive.map_zero (f := fun n ↦ n * n)
  (fun m n ↦ by
    change m * m + n * n ≤ (m + n) * (m + n)
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega)

/-- The hypotheses of `Superadditive.monotone` hold together: `f n = n * n`, superadditive with room
to spare, so not the identity's equality. -/
example := ClassicalLean.Superadditive.monotone (f := fun n ↦ n * n)
  (fun m n ↦ by
    change m * m + n * n ≤ (m + n) * (m + n)
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega)

/-- The hypotheses of `Superadditive.linear_le` hold together: `f n = n * n` at `n = 3`, where the
bound `3 * f 1 = 3` is strict against `f 3 = 9`. -/
example := ClassicalLean.Superadditive.linear_le (f := fun n ↦ n * n) (n := 3)
  (fun m n ↦ by
    change m * m + n * n ≤ (m + n) * (m + n)
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega)

/-- The hypotheses of `Superadditive.unbounded` hold together: `f n = n * n`, with `f 1 = 1`
positive. -/
example := ClassicalLean.Superadditive.unbounded (f := fun n ↦ n * n)
  (fun m n ↦ by
    change m * m + n * n ≤ (m + n) * (m + n)
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega)
  (by decide)

/-- The hypotheses of `Superadditive.pos_of_pos` hold together: `f n = n * n`, with `f 1 = 1`
positive, at `n = 2` (at `n = 1` the conclusion would restate `0 < f 1`). -/
example := ClassicalLean.Superadditive.pos_of_pos (f := fun n ↦ n * n) (n := 2)
  (fun m n ↦ by
    change m * m + n * n ≤ (m + n) * (m + n)
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega)
  (by decide) (by decide)
