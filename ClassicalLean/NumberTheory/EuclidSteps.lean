/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.NumberTheory.Lucas
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Lamé's theorem: the number of steps of the Euclidean algorithm

`euclidSteps a b` is the number of division steps the Euclidean algorithm takes on `(a, b)`: none
when `b = 0`, and otherwise one step to `(b, a % b)` and the steps from there
(`euclidSteps_zero_right`, `euclidSteps_of_ne_zero`). Write `F n` for `Nat.fib n` and `L n` for
`lucas n` (`NumberTheory/Lucas`).

## Main results

* `fib_euclidSteps_add_one_le_right`: if the algorithm takes `n` steps on `(a, b)` with `b ≠ 0`,
  then `F (n + 1) ≤ b`.
* `fib_euclidSteps_add_two_le_left`: if it takes `n` steps on `(a, b)` with `b < a`, then
  `F (n + 2) ≤ a`.
* `euclidSteps_fib_add_three_fib_add_two`: on `(F (n + 3), F (n + 2))` it takes exactly `n + 1`
  steps, so both bounds are attained; `euclidSteps_lucas_add_two_lucas_add_one`: on
  `(L (n + 2), L (n + 1))` also exactly `n + 1`.
* `ten_pow_lt_fib_five_mul_add_two`: `10 ^ k < F (5 k + 2)` for `k ≠ 0`.
* `euclidSteps_le_five_mul_length_digits`, **Lamé's theorem** (G. Lamé, 1844): the algorithm on
  `(a, b)` takes at most five times as many steps as `b` has decimal digits. For `b ≤ a` this is the
  classical form with the smaller entry; for `a < b` that form is false (`(8, 13)` takes 6 steps).

The constant `5` is attained for one, two and three digits, by `(13, 8)`, `(144, 89)` and
`(1597, 987)` — `euclidSteps_fib_add_three_fib_add_two` at `n = 4, 9, 14` — and not for four: there
the largest count is `19`, at `(10946, 6765)` (order G-9's measurements over all `a` for one to
three digits; for four, the first bound with `F 21 = 10946 > 9999`).

## The proof

* The two equations by rewriting with the definition's unfolding lemma once each; `decide` cannot
  evaluate the definition, which is by well-founded recursion on `b`.
* The two Fibonacci bounds together, as one predicate of the pair `(b, a)`, by `Nat.gcd.induction`
  (core), which recurses on its first argument exactly as the algorithm does: at a step with
  `b ≠ 0`, let `n'` be the number of steps on the next pair `(b, a % b)`, so that `n = n' + 1`; the
  second bound there gives `F (n' + 2) ≤ b`, the first bound here; and for `b < a`, either
  `a % b ≠ 0`, so `F (n' + 1) ≤ a % b` and `a % b + b ≤ a` give `F (n' + 3) ≤ a`, or `a % b = 0`,
  so one step and `F 3 = 2 ≤ a`.
* The attaining pairs by induction on `n`, with one division step on consecutive Fibonacci numbers,
  `F (n + 3) % F (n + 2) = F (n + 1)`, and on consecutive Lucas numbers,
  `L (n + 2) % L (n + 1) = L n` (both for `n ≥ 1`).
* `10 ^ k < F (5 k + 2)` by induction on `k`, with `F (m + 5) = 3 F m + 5 F (m + 1)` (`Nat.fib_add`
  at `4`) and `3 F m ≤ 2 F (m + 1)` for `m ≥ 2`.
* Lamé's bound: with `k` the number of digits of `b ≠ 0`, `b < 10 ^ k`
  (`Nat.lt_base_pow_length_digits`); `5 k + 1` steps would give `F (5 k + 2) ≤ b`, against the
  previous item.

## Sources

The route was derived for this library by claude-ai in order G-9 (its §0 row 8) and checked there
cell by cell. Its departures here (order G-9, J2) are the base cases of the attaining pairs, which
evaluate `euclidSteps` through the two equations rather than by `decide` (which cannot evaluate it;
there `decide` is left only on values of `Nat.fib` and `lucas`), and the step `a % b + b ≤ a`, which
goes through `Nat.mod_eq_sub_mod` rather than `Nat.div_add_mod`.

## Hypotheses

Every hypothesis of a public statement is needed (order G-9 J1's cells and statement review):
`b ≠ 0` in the first bound (it fails at `b = 0` for every `a`); `b < a` in the second, with no
condition on `b` (at `b = 0 < a` it reads `F 2 = 1 ≤ a`; without `b < a` it fails at some pairs with
`b ≥ a`, on the diagonal exactly at `a ∈ {0, 1}`); `k ≠ 0` in `10 ^ k < F (5 k + 2)` (it fails at
`k = 0`); none in Lamé's bound (at `b = 0` it reads `0 ≤ 0`). The private `three_mul_fib_le`
carries `2 ≤ m`, which its proof uses; `m ≠ 1` would suffice (order G-9's statement review).

## Mathlib at v4.34.0

Searched first (order G-9 J1, from `.lake/packages/mathlib`): `lamé` 0; `euclid` with
step/iteration/count 0; `gcd` with steps/fuel/iterations 4, all docstrings, none a count of steps.
Related prior art, weaker and not a step count: the continued-fraction bound
`GenContFract.succ_nth_fib_le_of_nth_den` (`Algebra/ContinuedFractions/Computation/Approximations`),
which at `a / b` gives `F s ≤ b / gcd a b` for `s` steps — one index below the first bound here.
`docs/1000.yaml` lists Lamé's theorem (Q230848) by title only.
-/

namespace ClassicalLean

/-- The number of division steps the Euclidean algorithm takes on `(a, b)`: none when `b = 0`,
otherwise one step to `(b, a % b)` and the steps from there. -/
def euclidSteps (a b : ℕ) : ℕ :=
  if h : b = 0 then 0 else euclidSteps b (a % b) + 1
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

/-- No division step when the divisor is `0`. -/
@[simp] theorem euclidSteps_zero_right (a : ℕ) : euclidSteps a 0 = 0 := by
  rw [euclidSteps.eq_def a 0, dite_eq_left rfl]

/-- One division step: for `b ≠ 0` the algorithm passes from `(a, b)` to `(b, a % b)`. -/
theorem euclidSteps_of_ne_zero (a : ℕ) {b : ℕ} (hb : b ≠ 0) :
    euclidSteps a b = euclidSteps b (a % b) + 1 := by
  rw [euclidSteps.eq_def a b, dite_eq_right hb]

/-- The two Fibonacci bounds together, as one predicate of the pair for `Nat.gcd.induction`. -/
private theorem fib_euclidSteps_le_aux (b a : ℕ) :
    (b ≠ 0 → Nat.fib (euclidSteps a b + 1) ≤ b) ∧
      (b < a → Nat.fib (euclidSteps a b + 2) ≤ a) := by
  induction b, a using Nat.gcd.induction with
  | H0 a =>
    refine ⟨fun h => absurd rfl h, fun h => ?_⟩
    simp only [euclidSteps_zero_right, zero_add, Nat.fib_two]
    omega
  | H1 b a hb ih =>
    have hs : euclidSteps a b = euclidSteps b (a % b) + 1 := euclidSteps_of_ne_zero a hb.ne'
    have h2 : Nat.fib (euclidSteps b (a % b) + 1 + 1) ≤ b := ih.2 (Nat.mod_lt a hb)
    refine ⟨fun _ => ?_, fun hba => ?_⟩
    · rw [hs]
      exact h2
    · rw [hs]
      rcases Nat.eq_zero_or_pos (a % b) with h0 | hpos
      · have h3 : Nat.fib (0 + 1 + 2) = 2 := by decide
        rw [h0, euclidSteps_zero_right, h3]
        omega
      · have h1 : Nat.fib (euclidSteps b (a % b) + 1) ≤ a % b := ih.1 hpos.ne'
        have hle : a % b + b ≤ a := by
          have hm := Nat.mod_le (a - b) b
          rw [← Nat.mod_eq_sub_mod hba.le] at hm
          omega
        rw [Nat.fib_add_two]
        omega

/-- If the algorithm takes `n` steps on `(a, b)` with `b ≠ 0`, then `F (n + 1) ≤ b`. -/
theorem fib_euclidSteps_add_one_le_right (a : ℕ) {b : ℕ} (hb : b ≠ 0) :
    Nat.fib (euclidSteps a b + 1) ≤ b :=
  (fib_euclidSteps_le_aux b a).1 hb

/-- If the algorithm takes `n` steps on `(a, b)` with `b < a`, then `F (n + 2) ≤ a`; `b ≠ 0` is
not needed (at `b = 0 < a` this reads `F 2 = 1 ≤ a`). -/
theorem fib_euclidSteps_add_two_le_left {a b : ℕ} (h : b < a) :
    Nat.fib (euclidSteps a b + 2) ≤ a :=
  (fib_euclidSteps_le_aux b a).2 h

/-- One division step on consecutive Fibonacci numbers (helper). -/
private theorem fib_add_three_mod_fib_add_two {n : ℕ} (hn : 1 ≤ n) :
    Nat.fib (n + 3) % Nat.fib (n + 2) = Nat.fib (n + 1) := by
  have h3 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
  have hlt : Nat.fib (n + 1) < Nat.fib (n + 2) := Nat.fib_lt_fib_succ (by omega)
  rw [h3, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]

/-- The algorithm takes `n + 1` steps on `(F (n + 3), F (n + 2))`, so consecutive Fibonacci
numbers attain `fib_euclidSteps_add_one_le_right` and `fib_euclidSteps_add_two_le_left` with
equality. -/
theorem euclidSteps_fib_add_three_fib_add_two (n : ℕ) :
    euclidSteps (Nat.fib (n + 3)) (Nat.fib (n + 2)) = n + 1 := by
  induction n with
  | zero =>
    have h2 : Nat.fib (0 + 2) ≠ 0 := by decide
    have hm : Nat.fib (0 + 3) % Nat.fib (0 + 2) = 0 := by decide
    rw [euclidSteps_of_ne_zero _ h2, hm, euclidSteps_zero_right]
  | succ n ih =>
    have hne : Nat.fib (n + 1 + 2) ≠ 0 := (Nat.fib_pos.mpr (by omega)).ne'
    rw [euclidSteps_of_ne_zero _ hne, fib_add_three_mod_fib_add_two (by omega : 1 ≤ n + 1)]
    exact congrArg (· + 1) ih

/-- One division step on consecutive Lucas numbers (helper). -/
private theorem lucas_add_two_mod_lucas_add_one {n : ℕ} (hn : 1 ≤ n) :
    lucas (n + 2) % lucas (n + 1) = lucas n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hlt : lucas (m + 1) < lucas (m + 1 + 1) := by
    change lucas (m + 1) < lucas (m + 2)
    rw [lucas_add_two]
    have := lucas_pos m
    omega
  rw [lucas_add_two, Nat.add_mod_left, Nat.mod_eq_of_lt hlt]

/-- The algorithm takes `n + 1` steps on `(L (n + 2), L (n + 1))`, `L` the Lucas numbers. -/
theorem euclidSteps_lucas_add_two_lucas_add_one (n : ℕ) :
    euclidSteps (lucas (n + 2)) (lucas (n + 1)) = n + 1 := by
  induction n with
  | zero =>
    have h1 : lucas (0 + 1) ≠ 0 := by decide
    have hm : lucas (0 + 2) % lucas (0 + 1) = 0 := by decide
    rw [euclidSteps_of_ne_zero _ h1, hm, euclidSteps_zero_right]
  | succ n ih =>
    rw [euclidSteps_of_ne_zero _ (lucas_pos _).ne',
      lucas_add_two_mod_lucas_add_one (by omega : 1 ≤ n + 1)]
    exact congrArg (· + 1) ih

/-- `F (m + 5) = 3 F m + 5 F (m + 1)`, `Nat.fib_add` at `4` (helper). -/
private theorem fib_add_five (m : ℕ) : Nat.fib (m + 5) = 3 * Nat.fib m + 5 * Nat.fib (m + 1) := by
  have h4 : Nat.fib 4 = 3 := by decide
  have h5 : Nat.fib (4 + 1) = 5 := by decide
  calc Nat.fib (m + 5) = Nat.fib (m + 4 + 1) := rfl
    _ = Nat.fib m * Nat.fib 4 + Nat.fib (m + 1) * Nat.fib (4 + 1) := Nat.fib_add m 4
    _ = 3 * Nat.fib m + 5 * Nat.fib (m + 1) := by rw [h4, h5]; ring

/-- `3 F m ≤ 2 F (m + 1)` from `m = 2` on; false at `m = 1` (helper). -/
private theorem three_mul_fib_le {m : ℕ} (hm : 2 ≤ m) : 3 * Nat.fib m ≤ 2 * Nat.fib (m + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  have h1 : Nat.fib (j + 2) = Nat.fib j + Nat.fib (j + 1) := Nat.fib_add_two
  have h2 : Nat.fib (j + 2 + 1) = Nat.fib (j + 1) + Nat.fib (j + 2) := Nat.fib_add_two
  have h3 : Nat.fib j ≤ Nat.fib (j + 1) := Nat.fib_le_fib_succ
  omega

/-- `10 ^ k < F (5 * k + 2)` for `k ≠ 0`: every number with `k` decimal digits is below
`F (5 * k + 2)`. False at `k = 0`, where it reads `1 < F 2 = 1`. -/
theorem ten_pow_lt_fib_five_mul_add_two {k : ℕ} (hk : k ≠ 0) : 10 ^ k < Nat.fib (5 * k + 2) := by
  induction k with
  | zero => exact absurd rfl hk
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · decide
    · have hX := ih hk0.ne'
      have h5 := fib_add_five (5 * k + 2)
      have h3 := three_mul_fib_le (m := 5 * k + 2) (by omega)
      rw [show 5 * (k + 1) + 2 = 5 * k + 2 + 5 by ring, pow_succ]
      omega

/-- **Lamé's theorem**: the Euclidean algorithm on `(a, b)` takes at most five times as many steps
as the second argument `b` has decimal digits. For `b ≤ a` this is the classical form with the
smaller entry; for `a < b` that form is false (`(8, 13)` takes 6 steps). -/
theorem euclidSteps_le_five_mul_length_digits (a b : ℕ) :
    euclidSteps a b ≤ 5 * (Nat.digits 10 b).length := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  · have hlt : b < 10 ^ (Nat.digits 10 b).length := Nat.lt_base_pow_length_digits (by norm_num)
    generalize (Nat.digits 10 b).length = k at hlt ⊢
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hlt
      omega
    by_contra! hcon
    have h1 := fib_euclidSteps_add_one_le_right a hb.ne'
    have h2 : Nat.fib (5 * k + 2) ≤ Nat.fib (euclidSteps a b + 1) := Nat.fib_mono (by omega)
    have h3 := ten_pow_lt_fib_five_mul_add_two hk0
    omega

end ClassicalLean
