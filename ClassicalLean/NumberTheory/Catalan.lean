/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# Catalan numbers: the binomial form

The Catalan numbers are already in Mathlib as `catalan : ℕ → ℕ`, defined by
`catalan 0 = 1` and `catalan (n + 1) = ∑ i : Fin (n + 1), catalan i * catalan (n - i)`
(`Mathlib/Combinatorics/Enumerative/Catalan.lean`).  Mathlib also proves the closed form
against the central binomial coefficient, `catalan_eq_centralBinom_div`
(`catalan n = n.centralBinom / (n + 1)`), its division-free companion
`succ_mul_catalan_eq_centralBinom` (`(n + 1) * catalan n = n.centralBinom`), and the
integrality statement behind the division, `Nat.succ_dvd_centralBinom`
(`n + 1 ∣ n.centralBinom`, in `Mathlib/Data/Nat/Choose/Central.lean`), together with
`catalan_zero`, `catalan_one`, `catalan_two`, `catalan_three` and the enumeration theorem
`treesOfNumNodesEq_card_eq_catalan`.  None of that is reproved here.

Three of those results — the two closed forms and the divisibility — are restated below with
`Nat.centralBinom` unfolded to its Mathlib definition `Nat.centralBinom n = (2 * n).choose n`,
so that they read directly in terms of `Nat.choose`.  Each of the three is proved by the
corresponding Mathlib term and by nothing else: they are Mathlib's results in different
notation, not additions of this library.  The single statement this file adds is
`catalan_pos`.

## Main results

* `catalan_eq_choose_div`, `succ_mul_catalan_eq_choose`, `succ_dvd_choose_two_mul` :
  Mathlib's `catalan_eq_centralBinom_div`, `succ_mul_catalan_eq_centralBinom` and
  `Nat.succ_dvd_centralBinom` respectively, written with `Nat.choose` in place of
  `Nat.centralBinom`.  Mathlib's own term is the whole proof in all three cases.
* `catalan_pos` : `0 < catalan n`.  This is the one addition, and the search for a Mathlib
  original was made twice: enumerating every non-internal constant in the environment after
  `import Mathlib` whose name contains `catalan` gives 21 names — equation and match
  auxiliaries included — none of which states positivity, and `exact?` on the goal
  `0 < catalan n` closes nothing.  Neither measurement rules out some unnamed formulation
  reachable in several steps; both say no Mathlib lemma states it.  It is derived here from
  Mathlib's `Nat.centralBinom_pos`.

## Source

Ported from a `catalan` module that *defined* `catalan n := choose (2 * n) n / (n + 1)` on
top of its own Pascal-triangle `choose`, and proved `catalan_zero`, `catalan_one` from that
definition.  Both definitions are dropped in favour of Mathlib's `Nat.choose` and Mathlib's
recursively defined `catalan`, and the source's defining formula reappears here as the
*theorem* `catalan_eq_choose_div` — which is Mathlib's theorem, not new work.

The source's five theorems are dropped with it, each because Mathlib already has it:
`choose_zero_right`, `choose_zero_left` and `choose_succ_succ` are `Nat.choose_zero_right`,
`Nat.choose_zero_succ` and `Nat.choose_succ_succ` (the last also stated in `+ 1` form as
`Nat.choose_succ_succ'`), all three measured present; and `catalan_zero`, `catalan_one` are
the numerical facts Mathlib states as `catalan_zero` and `catalan_one` — about Mathlib's
`catalan`, which `catalan_eq_choose_div` identifies with the source's definition.  None of
the five is restated here.
-/

namespace ClassicalLean

/-- `catalan n = (2 * n).choose n / (n + 1)`.

Mathlib's result in different notation: this is `catalan_eq_centralBinom_div` with
`Nat.centralBinom` unfolded to its definition `Nat.centralBinom n = (2 * n).choose n`, and
the Mathlib term is the entire proof.  The division is `ℕ`-division, exact by
`succ_dvd_choose_two_mul` below. -/
theorem catalan_eq_choose_div (n : ℕ) : catalan n = (2 * n).choose n / (n + 1) :=
  catalan_eq_centralBinom_div n

/-- `(n + 1) * catalan n = (2 * n).choose n`, the division-free form.

Mathlib's result in different notation: this is `succ_mul_catalan_eq_centralBinom` with
`Nat.centralBinom` unfolded, and the Mathlib term is the entire proof. -/
theorem succ_mul_catalan_eq_choose (n : ℕ) : (n + 1) * catalan n = (2 * n).choose n :=
  succ_mul_catalan_eq_centralBinom n

/-- Every Catalan number is positive.

Unlike the three restatements around it, this one has no Mathlib original: no Mathlib
declaration whose name mentions `catalan` states positivity, and `exact?` on this goal finds
nothing (see the module docstring for both measurements).  The product `(n + 1) * catalan n`
is the central binomial coefficient, which is positive by Mathlib's `Nat.centralBinom_pos`,
so neither factor can vanish. -/
theorem catalan_pos (n : ℕ) : 0 < catalan n := by
  have h := succ_mul_catalan_eq_centralBinom n
  have hpos := Nat.centralBinom_pos n
  rw [← h] at hpos
  exact Nat.pos_of_mul_pos_left (by omega)

/-- `n + 1` divides the central binomial coefficient `(2 * n).choose n`.

Mathlib's result in different notation: this is `Nat.succ_dvd_centralBinom` with
`Nat.centralBinom` unfolded, and the Mathlib term is the entire proof.  Nothing is added
here.  It is the integrality statement behind the `ℕ`-division in `catalan_eq_choose_div`,
and `succ_mul_catalan_eq_choose` exhibits `catalan n` as the quotient. -/
theorem succ_dvd_choose_two_mul (n : ℕ) : (n + 1) ∣ (2 * n).choose n :=
  Nat.succ_dvd_centralBinom n

/-! ### Computed examples

`catalan` is defined by well-founded recursion in Mathlib, so `decide` cannot evaluate it.
The first four checks therefore rewrite with the closed form and then compute `Nat.choose`;
the fifth mentions no `catalan` at all and is computed directly by `decide`. -/

example : catalan 4 = 14 := by rw [catalan_eq_choose_div]; rfl

example : catalan 5 = 42 := by rw [catalan_eq_choose_div]; rfl

example : catalan 8 = 1430 := by rw [catalan_eq_choose_div]; rfl

example : catalan 10 = 16796 := by rw [catalan_eq_choose_div]; rfl

example : (11 : ℕ) ∣ (20).choose 10 := by decide

end ClassicalLean
