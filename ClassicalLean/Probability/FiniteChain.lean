/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.InformationTheory.Channel
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Matrix

/-!
# A finite chain whose every step chance is at least `δ`

A chain on `n` states moves from state `i` to state `j` with chance `P i j`; a distribution `μ`
(a row of chances) becomes `μ P` (`μ ᵥ* P`) after one step and `μ P ^ t` after `t` steps. Suppose
every row of `P` sums to `1` and every entry is at least `δ`. Distances are measured by the sum of
absolute differences, `∑ j, |μ j − ν j|`.

* `sum_abs_vecMul_le` — for a row `d` that sums to `0` (the difference of two distributions),
  one step multiplies `∑ |d|` by at most `1 − n δ`, `n` the number of states.
* `sum_abs_vecMul_pow_le`, `sum_abs_vecMul_pow_sub_le` — so after `t` steps by `(1 − n δ) ^ t`;
  in particular any row `μ` with the same total as a stationary distribution `π` (one with
  `π P = π`) approaches it at that rate. `μ` may have entries of any sign.
* `existsUnique_vecMul_eq_self` — if `δ > 0` (and there is at least one state), there is exactly
  one stationary distribution.
* `relEntropy_vecMul_le_of_stationary` (order LEAN-30, item 97) — relative entropy to a stationary
  vector never increases along the chain: `D(μ P ‖ π) ≤ D(μ ‖ π)`.
* `existsUnique_vecMul_eq_self_of_pow`, `sum_abs_vecMul_pow_sub_le_of_pow` (order LEAN-30, item
  100) — Perron–Frobenius for a primitive chain: if some power `P ^ k` has every entry positive
  (`P` itself may have zeros), there is exactly one stationary distribution, and a row with the
  stationary vector's total approaches it at rate `(1 − n δ) ^ ⌊t / k⌋` when every entry of
  `P ^ k` is at least `δ`.
* `meanHitting_eq`, `meanHitting_eq_of_le` (order LEAN-35, item 148 of MATH-PLAN-library-2) —
  **mean hitting times.** If `P ≥ 0`, its rows sum to `1` and a target `A` can be reached from every
  state, the series `h i = ∑ₜ (Q ^ t *ᵥ u) i` (`Q` the chain killed on entering `A`, `u` the
  indicator off `A`) converge, and `h` is the only solution of `g = 0` on `A`,
  `g i = 1 + ∑ j, P i j * g j` off `A`; the corollary asks instead that every entry be at least
  `δ > 0` and `A` be nonempty. The proofs are the amended draft `d1148-r1-s1` (written by Claude
  Opus 5.5 through the Anthropic Batch API in the lane's API-CREDIT-1 amendment round), adapted by
  order LEAN-35's session: inside this namespace, each theorem binding its own types as the draft
  does; the draft's module docstring and its `open` line (this module's own) not carried; both
  docstrings rewritten (the item, the credit, the reading as a hitting time marked as a reading,
  the corollary's target nonempty by `hA`); the draft's private Bernoulli inequality replaced by
  Mathlib's `one_add_mul_le_pow` at its one use; nine `show`s that changed the goal written as
  `change`. The proof bounds the chance of staying outside `A` for `N` steps by some `c < 1`,
  takes a one-step rate `ρ < 1` with `c ≤ ρ ^ N`, and gets uniqueness from
  `Q ^ t (g − h) = g − h → 0`; it does not use `sum_abs_vecMul_pow_sub_le`, which the plan's row
  names, and it uses Mathlib's `summable_geometric_of_lt_one`,
  `tendsto_pow_atTop_nhds_zero_of_lt_one`, `hasSum_nat_add_iff'` and `one_add_mul_le_pow`. Their
  hypotheses were not drop-tested by this order. Their witnesses are at the end of the file.

This is Doeblin's condition in its simplest form, every entry at least `δ`, which gives
`P ≥ n δ · (uniform)`. Citation: Doeblin 1938, "Exposé de la théorie des chaînes simples
constantes de Markov à un nombre fini d'états". The nearest statement found is Levin, Peres and
Wilmer, Markov Chains and Mixing Times (2nd ed.), Theorem 4.9, a geometric bound
by the same idea, not this constant. The two-state chain of `TwoStateChain` allows zero entries,
which this module does not.

## Hypotheses

Measured in order LEAN-21's checks (check C34, exact rationals): 200 random chains with positive
entries, up to 5 states, `t < 8`, stationary distributions solved exactly. Each hypothesis is
needed: drop it alone and the conclusion fails at:

* entries at least `δ`: `P = 1` (2 states), `δ = 1/2`, `d = (1, −1)`: `2 > 0`; for uniqueness,
  the same `P` and `δ`: `(1, 0)` and `(0, 1)` are both stationary (review r34).
* rows sum to `1`: `P = 2 · 1`, `δ = 0`, `d = (1, −1)`: `4 > 2`; and for existence, `P` all `1`
  with `δ = 1`: `π P = (1, 1) ≠ π` for every `π` of total `1`.
* `∑ d = 0`: `P` all `1/2`, `δ = 1/2`, `d = (1, 1)`: `2 > 0`.
* the totals of `μ` and `π` equal: `P` all `1/2`, `μ = 0`, `t = 1`: `1 > 0`.
* `π P = π`: `P` all `1/2`, `π = μ = (1, 0)`, `t = 1`: `1 > 0`.
* `δ > 0`, for uniqueness: `P = 1`, `δ = 0`: `(1, 0)` and `(0, 1)` are both stationary.
* at least one state, for existence: no row on an empty set of states sums to `1`.

## Relative entropy along a chain (order LEAN-30, item 97 of MATH-PLAN-library-2)

`relEntropy_vecMul_le_of_stationary`: if `P ≥ 0`, every row of `P` sums to `1`, `μ ≥ 0`, `μ i = 0`
wherever `π i = 0`, and `π P = π`, then `D(μ P ‖ π) ≤ D(μ ‖ π)`, with `D` the library's
`ClassicalLean.Simplex.relEntropy p q = ∑ i, p i log (p i / q i)`. Read as the "H-theorem" for a
finite chain: relative entropy to the stationary law never increases (a reading, not a further
theorem). The route: `|π|` is stationary too (entrywise `|π| P ≥ |π P| = |π|`, and both sides have
the same total, `sum_vecMul_eq_sum`); Lean's `relEntropy p π` sees `π` only through `|π|`
(`Real.log x = Real.log |x|`); and the data-processing inequality `relEntropy_vecMul_le`
(`InformationTheory.Channel`) for `μ` and `|π|` through the channel `P` finishes.

**Wider than the plan's reading:** `π` need not be a law (no `π ≥ 0` and no total `1`); a stationary
`π` of any sign gives the stationary `|π|` (order LEAN-30's check `97.signs` and its BY HAND line).
**Also, as written in the order's statement, not a new change:** `μ` need not sum to `1` either;
`relEntropy_vecMul_le` asks no total.

Each hypothesis is needed (order LEAN-30's exact checks, lane `lean/LEAN-30-checks.py`, in floating
point for the logarithms, each gap at least `0.1`, each case failing only the hypothesis named):

* `P ≥ 0` (`97.drop.hP0`): `P = [[3/2, −1/2], [−1/2, 3/2]]`, `π = (1/2, 1/2)`, `μ = (1, 0)`:
  `1.648 > 0.693`. Lean's `Real.log` of a negative number is the log of its absolute value.
* rows summing to `1` (`97.drop.hP`): `P = [[1, 1], [0, 0]]`, the same `π` and `μ`: `1.386 > 0.693`.
* `μ ≥ 0` (`97.drop.hmu`): `P` all `1/2`, `π = (1/2, 1/2)`, `μ = (−1, 0)`: `0 > −0.693` (Lean's
  `Real.log (−1) = 0`).
* `μ i = 0` wherever `π i = 0` (`97.drop.hmupi`): `P = [[1, 0], [1, 0]]`, `π = (1, 0)`,
  `μ = (1/2, 1/2)`: `0 > −0.347`; Lean's `x / 0 = 0` and `Real.log 0 = 0` make the term at
  `π i = 0` vanish. (The plan's own case `μ = (1/e, 1 − 1/e)` fails the same way.)
* `π P = π` (`97.drop.hpi`): `P = [[1, 0], [1, 0]]`, `π = μ = (1/2, 1/2)`: `0.693 > 0`.

Also measured: 300 random chains (`97.random`) and 100 with `π` negative on one closed class
(`97.signs`). The plan's search (`MATH-PLAN-library-2-checks.py`, line `row.X8`:
`h-theorem|entropy production`) found 0 lines in pinned Mathlib, in Mathlib master at `2da3ab0a` and
in the library when order LEAN-30 began.

## Perron–Frobenius for a primitive chain (order LEAN-30, item 100 of MATH-PLAN-library-2)

A chain is primitive when some power `P ^ k` has every entry positive, though `P` may have zeros.

* `existsUnique_vecMul_eq_self_of_pow`: if every row of `P` sums to `1` and every entry of `P ^ k`
  is positive, and there is a state, exactly one distribution `π` has `π P = π`. The route: the rows
  of `Q = P ^ k` sum to `1` and its least entry `δ` is positive, so `existsUnique_vecMul_eq_self`
  gives `Q` one stationary distribution `π*`; `π* P` is also fixed by `Q` (`P Q = Q P`) and has
  total `1`, so the difference `π* P − π*` sums to `0` and is fixed by `Q`, and
  `sum_abs_vecMul_le` (any sign) makes it `0`. A distribution fixed by `P` is fixed by `Q`, so it
  is `π*`.
* `sum_abs_vecMul_pow_sub_le_of_pow`: if `P ≥ 0`, every row sums to `1`, every entry of `P ^ k` is
  at least `δ`, `π P = π` and `μ` has `π`'s total, then
  `∑ j, |(μ P ^ t) j − π j| ≤ (1 − n δ) ^ (t / k) ∑ j, |μ j − π j|`. The route:
  `t = k (t / k) + t % k`; first `sum_abs_vecMul_pow_sub_le` for `P ^ k` over the `t / k` steps,
  then `sum_abs_vecMul_pow_le` with `δ = 0` (factor `1`) over the remaining `t % k` steps of `P`,
  so no sign of `1 − n δ` is needed.

**Wider than the plan's reading:** the plan states the hypothesis with Mathlib's
`Matrix.IsPrimitive` "where it fits". It does not fit here: `Matrix.IsPrimitive` is not in this
module's imports, and it carries two conditions the uniqueness theorem does not need, `P ≥ 0`
(`100.unique.neg`, and the BY HAND line `100.unique`) and `k > 0` (at `k = 0`, `P ^ 0 = 1` has every
entry positive only with one state, where `P = (1)`; the same BY HAND line `100.unique`). Nor does
the rate theorem need `k > 0`: Lean's `t / 0 = 0` makes the factor `1` (`100.k0`). A primitive
matrix in Mathlib's sense (`Matrix.IsPrimitive`, `LinearAlgebra/Matrix/Irreducible/Defs.lean`)
meets `hpos` through its field `exists_pos_pow` (named here, not imported). **Also, as written in
the order's statement, not a new change:** the rate theorem asks no `δ > 0` (any real `δ`; for
`δ ≤ 0` the factor is at least `1`), lets `μ` have any sign, and lets `π` be any stationary vector
with `μ`'s total, exactly as `sum_abs_vecMul_pow_sub_le` above.

Each hypothesis is needed (order LEAN-30's exact checks, each case keeping the other hypotheses):

* uniqueness, rows summing to `1` (`100.drop.u.hP`): `P` all `1` (rows sum to `2`), `P ^ 1 > 0`: no
  stationary vector of total `1`.
* uniqueness, `P ^ k > 0` (`100.drop.u.hpos`): `P = 1` with two states: `(1, 0)` and `(0, 1)` are
  both stationary laws.
* uniqueness, a state (`100.drop.u.nonempty`): with none, no vector has total `1`.
* rate, `P ≥ 0` (`100.drop.r.hP0`): `P = [[3/2, −1/2], [−1/2, 3/2]]`, `k = 2`, `δ = −3/2`,
  `μ = (1, 0)`, `π = (1/2, 1/2)`, `t = 1`: `2 > 1`.
* rate, rows summing to `1` (`100.drop.r.hP`): `P = 2 · 1`, `k = 1`, `δ = 0`, `μ = (1, −1)`,
  `π = 0`, `t = 1`: `4 > 2`.
* rate, `P ^ k ≥ δ` (`100.drop.r.hdelta`): `P = 1`, `k = 1`, `δ = 1/2`, `μ = (1, 0)`, `π = (0, 1)`,
  `t = 1`: `2 > 0`.
* rate, equal totals (`100.drop.r.hmu`): `P` all `1/2`, `k = 1`, `δ = 1/2`, `μ = 0`,
  `π = (1/2, 1/2)`, `t = 1`: `1 > 0`.
* rate, `π P = π` (`100.drop.r.hpi`): `P` all `1/2`, `k = 1`, `δ = 1/2`, `μ = π = (1, 0)`, `t = 1`:
  `1 > 0`.

Also measured exactly: 200 chains with a zero entry (`100.unique`), 100 with a negative entry
(`100.unique.neg`), and the rate on 200 chains for `t ≤ 12` (`100.rate`).

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-21, `grep -rniE` over Mathlib):
`stationary distribution|invariant distribution|doeblin|dobrushin|ergodic coefficient|perron` 6
lines, none about chains (citations and keywords); `rowStochastic.*(pow|unique|fixed)|
stochastic.*(stationary|invariant)|Tendsto.*vecMul.*\^` 0; `markov chain|MarkovChain|transition
matrix` 4 lines, docstrings of `Kernel.Irreducible` and of irreducible matrices. Used:
`cauchySeq_of_le_geometric`, `cauchySeq_tendsto_of_complete`, `Continuous.matrix_vecMul`; from the
library, `sum_vecMul_eq_sum` and `vecMul_nonneg` (InformationTheory.Channel).

Order LEAN-30 (item 100), the plan's search (`MATH-PLAN-library-2-checks.py`, lines `row.L7`), in
order LEAN-30's run of it before this module changed: `perron` 6 lines in 6 files of pinned
Mathlib and of Mathlib master at `2da3ab0a`; by hand, reading the six lines of pinned Mathlib:
the generalised Perron integral (`BoxIntegral`) and two citations of a book on it, two citations
of Moss and Perrone (ergodic decomposition), and the keyword line of
`LinearAlgebra/Matrix/Irreducible/Defs.lean` ("primitive, perron-frobenius"), with no theorem
about matrices among them; `stationary distribution|invariant distribution` 0 in both. Mathlib
defines primitive matrices, `Matrix.IsPrimitive`, in that file, whose only theorem about them is
that a primitive matrix is irreducible (by hand, reading the file). A primitive matrix in
Mathlib's sense meets this module's `hpos` through its field `exists_pos_pow` (named here, not
imported). Item 97 uses `relEntropy_vecMul_le` (InformationTheory.Channel); item 100 uses this
module's own `existsUnique_vecMul_eq_self`, `sum_abs_vecMul_le`, `sum_abs_vecMul_pow_le` and
`sum_abs_vecMul_pow_sub_le`.
-/

open Finset Filter Topology Matrix

namespace ClassicalLean.Probability

variable {n : Type*} [Fintype n]

/-- **One step shrinks a difference of distributions.** If every row of `P` sums to `1` and every
entry is at least `δ`, then for `d` with `∑ d = 0`,
`∑ j, |(d P) j| ≤ (1 − n δ) ∑ i, |d i|`, `n` the number of states. -/
theorem sum_abs_vecMul_le {P : Matrix n n ℝ} {δ : ℝ} (hP : ∀ i, ∑ j, P i j = 1)
    (hδ : ∀ i j, δ ≤ P i j) {d : n → ℝ} (hd : ∑ i, d i = 0) :
    ∑ j, |(d ᵥ* P) j| ≤ (1 - Fintype.card n * δ) * ∑ i, |d i| := by
  have e : ∀ j, (d ᵥ* P) j = ∑ i, d i * (P i j - δ) := fun j ↦ by
    simp only [vecMul_apply_eq_sum, mul_sub, sum_sub_distrib, ← sum_mul, hd, zero_mul, sub_zero]
  calc ∑ j, |(d ᵥ* P) j| = ∑ j, |∑ i, d i * (P i j - δ)| := by simp only [e]
    _ ≤ ∑ j, ∑ i, |d i| * (P i j - δ) := sum_le_sum fun j _ ↦ (abs_sum_le_sum_abs _ _).trans
        (sum_le_sum fun i _ ↦ by rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hδ i j))])
    _ = ∑ i, |d i| * ∑ j, (P i j - δ) := by rw [sum_comm]; simp only [mul_sum]
    _ = (1 - Fintype.card n * δ) * ∑ i, |d i| := by
        simp only [sum_sub_distrib, hP, sum_const, card_univ, nsmul_eq_mul, mul_sum]
        exact sum_congr rfl fun i _ ↦ by ring

/-- The factor `1 − n δ` is at least `0` when there is a state. -/
private theorem one_sub_card_mul_nonneg [Nonempty n] {P : Matrix n n ℝ} {δ : ℝ}
    (hP : ∀ i, ∑ j, P i j = 1) (hδ : ∀ i j, δ ≤ P i j) : 0 ≤ 1 - Fintype.card n * δ := by
  obtain ⟨i⟩ := ‹Nonempty n›
  have := sum_le_sum fun j (_ : j ∈ univ) ↦ hδ i j
  rw [hP i, sum_const, card_univ, nsmul_eq_mul] at this
  linarith

/-- The rows of `P ^ t` sum to `1` when the rows of `P` do. -/
private theorem sum_pow_apply_eq_one [DecidableEq n] {P : Matrix n n ℝ}
    (hP : ∀ i, ∑ j, P i j = 1) (t : ℕ) (i : n) : ∑ j, (P ^ t) i j = 1 := by
  induction t generalizing i with
  | zero => simp [one_apply]
  | succ t iht =>
    rw [pow_succ]
    simp only [mul_apply]
    rw [sum_comm]
    simp only [← mul_sum, hP, mul_one]
    exact iht i

/-- **`t` steps shrink a difference by `(1 − n δ) ^ t`.** Under the hypotheses of
`sum_abs_vecMul_le`, `∑ j, |(d P ^ t) j| ≤ (1 − n δ) ^ t ∑ i, |d i|`. -/
theorem sum_abs_vecMul_pow_le [DecidableEq n] {P : Matrix n n ℝ} {δ : ℝ}
    (hP : ∀ i, ∑ j, P i j = 1) (hδ : ∀ i j, δ ≤ P i j) {d : n → ℝ} (hd : ∑ i, d i = 0) (t : ℕ) :
    ∑ j, |(d ᵥ* P ^ t) j| ≤ (1 - Fintype.card n * δ) ^ t * ∑ i, |d i| := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp
  have hc := one_sub_card_mul_nonneg hP hδ
  induction t with
  | zero => simp
  | succ t ih =>
    have hsum : ∑ i, (d ᵥ* P ^ t) i = 0 := by
      rw [ClassicalLean.Simplex.sum_vecMul_eq_sum (sum_pow_apply_eq_one hP t), hd]
    rw [pow_succ, ← vecMul_vecMul]
    calc ∑ j, |((d ᵥ* P ^ t) ᵥ* P) j|
        ≤ (1 - Fintype.card n * δ) * ∑ i, |(d ᵥ* P ^ t) i| := sum_abs_vecMul_le hP hδ hsum
      _ ≤ (1 - Fintype.card n * δ) * ((1 - Fintype.card n * δ) ^ t * ∑ i, |d i|) :=
          mul_le_mul_of_nonneg_left ih hc
      _ = (1 - Fintype.card n * δ) ^ (t + 1) * ∑ i, |d i| := by ring

/-- **A chain with every step chance at least `δ` forgets its start at rate `(1 − n δ) ^ t`.** If
every row of `P` sums to `1`, every entry is at least `δ`, `π P = π`, and `μ` has the same total
as `π`, then `∑ j, |(μ P ^ t) j − π j| ≤ (1 − n δ) ^ t ∑ j, |μ j − π j|`. -/
theorem sum_abs_vecMul_pow_sub_le [DecidableEq n] {P : Matrix n n ℝ} {δ : ℝ}
    (hP : ∀ i, ∑ j, P i j = 1) (hδ : ∀ i j, δ ≤ P i j) {μ π : n → ℝ}
    (hμ : ∑ i, μ i = ∑ i, π i) (hπ : π ᵥ* P = π) (t : ℕ) :
    ∑ j, |(μ ᵥ* P ^ t) j - π j| ≤ (1 - Fintype.card n * δ) ^ t * ∑ j, |μ j - π j| := by
  have hπt : π ᵥ* P ^ t = π := by
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ, ← vecMul_vecMul, ih, hπ]
  have hd : ∑ i, (μ - π) i = 0 := by simp [sum_sub_distrib, hμ]
  have := sum_abs_vecMul_pow_le hP hδ hd t
  rwa [sub_vecMul, hπt] at this

/-- **One stationary distribution.** If every row of `P` sums to `1`, every entry is at least
`δ > 0`, and there is at least one state, exactly one distribution `π` (entries at least `0`,
total `1`) has `π P = π`. -/
theorem existsUnique_vecMul_eq_self [Nonempty n] {P : Matrix n n ℝ} {δ : ℝ}
    (hP : ∀ i, ∑ j, P i j = 1) (hδ0 : 0 < δ) (hδ : ∀ i j, δ ≤ P i j) :
    ∃! π : n → ℝ, ((∀ i, 0 ≤ π i) ∧ ∑ i, π i = 1) ∧ π ᵥ* P = π := by
  classical
  set c := 1 - Fintype.card n * δ
  have hc0 : 0 ≤ c := one_sub_card_mul_nonneg hP hδ
  have hc1 : c < 1 := by
    have : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
    simp only [c]; nlinarith
  have hP0 : ∀ i j, 0 ≤ P i j := fun i j ↦ hδ0.le.trans (hδ i j)
  let S : Set (n → ℝ) := {π | (∀ i, 0 ≤ π i) ∧ ∑ i, π i = 1}
  have hSstep : ∀ π ∈ S, π ᵥ* P ∈ S := fun π hπ ↦
    ⟨ClassicalLean.Simplex.vecMul_nonneg hP0 hπ.1, by
      rw [ClassicalLean.Simplex.sum_vecMul_eq_sum hP, hπ.2]⟩
  have hSclosed : IsClosed S := by
    have e : S = (⋂ i, {π : n → ℝ | 0 ≤ π i}) ∩ {π | ∑ i, π i = 1} := by
      ext π; simp [S, Set.mem_iInter]
    rw [e]
    exact (isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_eq (continuous_finsetSum _ fun i _ ↦ continuous_apply i) continuous_const)
  have hvc : Continuous fun v : n → ℝ ↦ v ᵥ* P := continuous_id.matrix_vecMul continuous_const
  -- uniqueness from the contraction
  have huniq : ∀ π₁ ∈ S, π₁ ᵥ* P = π₁ → ∀ π₂ ∈ S, π₂ ᵥ* P = π₂ → π₁ = π₂ := by
    intro π₁ h₁ f₁ π₂ h₂ f₂
    have hd : ∑ i, (π₁ - π₂) i = 0 := by simp [sum_sub_distrib, h₁.2, h₂.2]
    have h := sum_abs_vecMul_le hP hδ hd
    rw [sub_vecMul, f₁, f₂] at h
    have hz : ∑ i, |(π₁ - π₂) i| = 0 := by
      have : 0 ≤ ∑ i, |(π₁ - π₂) i| := sum_nonneg fun _ _ ↦ abs_nonneg _
      simp only [Pi.sub_apply] at h this ⊢
      nlinarith
    funext i
    have := (sum_eq_zero_iff_of_nonneg fun j _ ↦ abs_nonneg ((π₁ - π₂) j)).mp hz i (mem_univ i)
    simpa [sub_eq_zero] using this
  -- existence: the steps from one distribution form a Cauchy sequence
  obtain ⟨i₀⟩ := ‹Nonempty n›
  let u : ℕ → n → ℝ := fun t ↦ (fun i ↦ if i = i₀ then 1 else 0) ᵥ* P ^ t
  have hu_succ : ∀ t, u (t + 1) = u t ᵥ* P := fun t ↦ by
    simp only [u, pow_succ, ← vecMul_vecMul]
  have hu_mem : ∀ t, u t ∈ S := by
    intro t
    induction t with
    | zero => exact ⟨fun i ↦ by simp [u]; split_ifs <;> norm_num, by simp [u]⟩
    | succ t ih => rw [hu_succ]; exact hSstep _ ih
  have hu_dist : ∀ t, dist (u t) (u (t + 1)) ≤ (∑ i, |(u 0 - u 1) i|) * c ^ t := by
    intro t
    have hd : ∑ i, (u 0 - u 1) i = 0 := by simp [sum_sub_distrib, (hu_mem 0).2, (hu_mem 1).2]
    have h := sum_abs_vecMul_pow_le hP hδ hd t
    have e : (u 0 - u 1) ᵥ* P ^ t = u t - u (t + 1) := by
      simp only [u, sub_vecMul, vecMul_vecMul, pow_zero, Matrix.one_mul, pow_one, ← pow_succ']
    rw [e] at h
    rw [dist_eq_norm, mul_comm]
    refine le_trans ?_ h
    refine (pi_norm_le_iff_of_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _)).mpr fun j ↦ ?_
    rw [Real.norm_eq_abs]
    exact single_le_sum (f := fun j ↦ |(u t - u (t + 1)) j|) (fun _ _ ↦ abs_nonneg _) (mem_univ j)
  obtain ⟨π, hπ⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric c _ hc1 hu_dist)
  have hπS : π ∈ S := hSclosed.mem_of_tendsto hπ (Eventually.of_forall hu_mem)
  have hπfix : π ᵥ* P = π := by
    have h1 : Tendsto (fun t ↦ u t ᵥ* P) atTop (𝓝 (π ᵥ* P)) := (hvc.tendsto π).comp hπ
    have h2 : Tendsto (fun t ↦ u (t + 1)) atTop (𝓝 π) := hπ.comp (tendsto_add_atTop_nat 1)
    simp only [hu_succ] at h2
    exact tendsto_nhds_unique h1 h2
  exact ⟨π, ⟨hπS, hπfix⟩, fun π' h' ↦ huniq π' h'.1 h'.2 π hπS hπfix⟩

/-- **Relative entropy to a stationary vector never increases along the chain** (order LEAN-30,
item 97 of MATH-PLAN-library-2). If `P ≥ 0`, every row of `P` sums to `1`, `μ ≥ 0`, `μ i = 0`
wherever `π i = 0`, and `π P = π`, then `D(μ P ‖ π) ≤ D(μ ‖ π)`. `π` need not be a law (wider than
the plan's reading), and `μ` need not sum to `1` (as written in the order's statement, not a new
change). Through `|π|`, which is stationary too, and the data-processing inequality. -/
theorem relEntropy_vecMul_le_of_stationary {P : Matrix n n ℝ} {μ π : n → ℝ}
    (hP0 : ∀ i j, 0 ≤ P i j) (hP : ∀ i, ∑ j, P i j = 1) (hμ : ∀ i, 0 ≤ μ i)
    (hμπ : ∀ i, π i = 0 → μ i = 0) (hπ : π ᵥ* P = π) :
    ClassicalLean.Simplex.relEntropy (μ ᵥ* P) π ≤ ClassicalLean.Simplex.relEntropy μ π := by
  -- `|π|` is stationary too: entrywise `|π| P ≥ |π P| = |π|`, with the same total
  have hle : ∀ j, |π j| ≤ ((fun i ↦ |π i|) ᵥ* P) j := fun j ↦ by
    have h : |(π ᵥ* P) j| ≤ ((fun i ↦ |π i|) ᵥ* P) j := by
      rw [vecMul_apply_eq_sum, vecMul_apply_eq_sum]
      refine (abs_sum_le_sum_abs _ _).trans_eq (sum_congr rfl fun i _ ↦ ?_)
      rw [abs_mul, abs_of_nonneg (hP0 i j)]
    rwa [hπ] at h
  have hsum : ∑ j, ((fun i ↦ |π i|) ᵥ* P) j = ∑ j, |π j| :=
    ClassicalLean.Simplex.sum_vecMul_eq_sum hP
  have hfix : (fun i ↦ |π i|) ᵥ* P = fun i ↦ |π i| := by
    have h := (sum_eq_sum_iff_of_le fun j (_ : j ∈ univ) ↦ hle j).mp hsum.symm
    funext j
    exact (h j (mem_univ j)).symm
  -- relative entropy sees `q` only through `|q|`
  have habs : ∀ p : n → ℝ, ClassicalLean.Simplex.relEntropy p π =
      ClassicalLean.Simplex.relEntropy p (fun i ↦ |π i|) := fun p ↦ by
    unfold ClassicalLean.Simplex.relEntropy
    refine sum_congr rfl fun i _ ↦ ?_
    rw [← Real.log_abs (p i / π i), ← Real.log_abs (p i / |π i|), abs_div, abs_div, abs_abs]
  have h := ClassicalLean.Simplex.relEntropy_vecMul_le hμ (fun i ↦ abs_nonneg (π i))
    (fun i hi ↦ hμπ i (abs_eq_zero.mp hi)) hP0 hP
  rw [hfix] at h
  rwa [habs, habs]

/-- **Perron–Frobenius for a primitive chain: one stationary distribution** (order LEAN-30, item
100 of MATH-PLAN-library-2). If every row of `P` sums to `1`, some power `P ^ k` has every entry
positive and there is a state, exactly one distribution `π` has `π P = π`. `P` may have zeros; no
`P ≥ 0` and no `k > 0` are asked (wider than the plan's reading through `Matrix.IsPrimitive`). -/
theorem existsUnique_vecMul_eq_self_of_pow [DecidableEq n] [Nonempty n] {P : Matrix n n ℝ}
    {k : ℕ} (hP : ∀ i, ∑ j, P i j = 1) (hpos : ∀ i j, 0 < (P ^ k) i j) :
    ∃! π : n → ℝ, ((∀ i, 0 ≤ π i) ∧ ∑ i, π i = 1) ∧ π ᵥ* P = π := by
  have hQ : ∀ i, ∑ j, (P ^ k) i j = 1 := sum_pow_apply_eq_one hP k
  obtain ⟨ab, -, hmin⟩ := exists_min_image (univ : Finset (n × n)) (fun x ↦ (P ^ k) x.1 x.2)
    univ_nonempty
  have hδ0 : 0 < (P ^ k) ab.1 ab.2 := hpos ab.1 ab.2
  have hδ : ∀ i j, (P ^ k) ab.1 ab.2 ≤ (P ^ k) i j := fun i j ↦ hmin (i, j) (mem_univ _)
  obtain ⟨π, ⟨hπS, hπQ⟩, huniq⟩ := existsUnique_vecMul_eq_self hQ hδ0 hδ
  have hcomm : P * P ^ k = P ^ k * P := (pow_succ' P k).symm.trans (pow_succ P k)
  have hfix : (π ᵥ* P) ᵥ* P ^ k = π ᵥ* P := by
    rw [vecMul_vecMul, hcomm, ← vecMul_vecMul, hπQ]
  have hdsum : ∑ i, (π ᵥ* P - π) i = 0 := by
    simp [sum_sub_distrib, ClassicalLean.Simplex.sum_vecMul_eq_sum hP, hπS.2]
  have hdQ : (π ᵥ* P - π) ᵥ* P ^ k = π ᵥ* P - π := by rw [sub_vecMul, hfix, hπQ]
  have h := sum_abs_vecMul_le hQ hδ hdsum
  rw [hdQ] at h
  have hn : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have h0 : 0 ≤ ∑ i, |(π ᵥ* P - π) i| := sum_nonneg fun _ _ ↦ abs_nonneg _
  have hz : ∑ i, |(π ᵥ* P - π) i| = 0 := by nlinarith [mul_pos hn hδ0]
  have hπP : π ᵥ* P = π := by
    refine sub_eq_zero.mp (funext fun i ↦ abs_eq_zero.mp ?_)
    exact (sum_eq_zero_iff_of_nonneg fun j _ ↦ abs_nonneg _).mp hz i (mem_univ i)
  refine ⟨π, ⟨hπS, hπP⟩, fun π' h' ↦ huniq π' ⟨h'.1, ?_⟩⟩
  have ht : ∀ t : ℕ, π' ᵥ* P ^ t = π' := fun t ↦ by
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ, ← vecMul_vecMul, ih, h'.2]
  exact ht k

/-- **Perron–Frobenius for a primitive chain: the rate** (order LEAN-30, item 100 of
MATH-PLAN-library-2). If `P ≥ 0`, every row sums to `1`, every entry of `P ^ k` is at least `δ`,
`π P = π` and `μ` has `π`'s total, then
`∑ j, |(μ P ^ t) j − π j| ≤ (1 − n δ) ^ (t / k) ∑ j, |μ j − π j|`. No `k > 0` is asked (Lean's
`t / 0 = 0`; wider than the plan's reading); any real `δ`, `μ` of any sign and any stationary `π`
with `μ`'s total, as written in the order's statement, not a new change. -/
theorem sum_abs_vecMul_pow_sub_le_of_pow [DecidableEq n] {P : Matrix n n ℝ} {k : ℕ} {δ : ℝ}
    (hP0 : ∀ i j, 0 ≤ P i j) (hP : ∀ i, ∑ j, P i j = 1) (hδ : ∀ i j, δ ≤ (P ^ k) i j)
    {μ π : n → ℝ} (hμ : ∑ i, μ i = ∑ i, π i) (hπ : π ᵥ* P = π) (t : ℕ) :
    ∑ j, |(μ ᵥ* P ^ t) j - π j| ≤ (1 - Fintype.card n * δ) ^ (t / k) * ∑ j, |μ j - π j| := by
  have hπt : ∀ s : ℕ, π ᵥ* P ^ s = π := fun s ↦ by
    induction s with
    | zero => simp
    | succ s ih => rw [pow_succ, ← vecMul_vecMul, ih, hπ]
  have hQ : ∀ i, ∑ j, (P ^ k) i j = 1 := sum_pow_apply_eq_one hP k
  -- the `t / k` steps of `P ^ k` first
  have h1 := sum_abs_vecMul_pow_sub_le hQ hδ hμ (hπt k) (t / k)
  -- then the remaining `t % k` steps of `P`, with factor `1`
  have hν : ∑ i, (μ ᵥ* (P ^ k) ^ (t / k) - π) i = 0 := by
    simp [sum_sub_distrib, ClassicalLean.Simplex.sum_vecMul_eq_sum (sum_pow_apply_eq_one hQ _), hμ]
  have h2 := sum_abs_vecMul_pow_le (δ := 0) hP (fun i j ↦ by simpa using hP0 i j) hν (t % k)
  rw [sub_vecMul, hπt] at h2
  simp only [mul_zero, sub_zero, one_pow, one_mul] at h2
  have e : μ ᵥ* P ^ t = (μ ᵥ* (P ^ k) ^ (t / k)) ᵥ* P ^ (t % k) := by
    rw [vecMul_vecMul, ← pow_mul, ← pow_add, Nat.div_add_mod]
  rw [e]
  simp only [Pi.sub_apply] at h2
  exact h2.trans h1

/-- **Mean hitting times of a finite chain** (item 148 of MATH-PLAN-library-2; the amended draft
`d1148-r1-s1`, written by Claude Opus 5.5 through the Anthropic Batch API in the lane's
API-CREDIT-1 amendment round, adapted by order LEAN-35's session). Let `P` have nonnegative entries
and rows summing to `1`, and let the target `A` be reachable from every state outside it. With `Q`
the chain killed on entering `A` (its rows and columns at `A` set to `0`) and `u` the indicator of
the complement of `A`, `(Q ^ t *ᵥ u) i` is the chance that the chain started at `i` has not reached
`A` by time `t`, so `h i = ∑ₜ (Q ^ t *ᵥ u) i` is the mean time for the chain started at `i` to reach
`A` (a reading: no random process is built here). Every series converges, and `h` is the only
solution of `g = 0` on `A`, `g i = 1 + ∑ j, P i j * g j` off `A`. -/
theorem meanHitting_eq {n : Type*} [Fintype n] [DecidableEq n] {P : Matrix n n ℝ}
    (hP : ∀ i, ∑ j, P i j = 1) (hP0 : ∀ i j, 0 ≤ P i j) {A : Finset n}
    (hreach : ∀ i ∉ A, ∃ t, ∃ a ∈ A, 0 < (P ^ t) i a) :
    let Q : Matrix n n ℝ := Matrix.of fun i j => if i ∈ A ∨ j ∈ A then 0 else P i j
    let u : n → ℝ := fun i => if i ∈ A then 0 else 1
    let h : n → ℝ := fun i => ∑' t, (Q ^ t *ᵥ u) i
    (∀ i, Summable fun t => (Q ^ t *ᵥ u) i) ∧
    ∀ g : n → ℝ, ((∀ i ∈ A, g i = 0) ∧ ∀ i ∉ A, g i = 1 + ∑ j, P i j * g j) ↔ g = h := by
  intro Q u h
  have hQ0 : ∀ i j, 0 ≤ Q i j := fun i j => by
    simp only [Q, Matrix.of_apply]
    split_ifs
    · exact le_rfl
    · exact hP0 i j
  have hQle : ∀ i j, Q i j ≤ P i j := fun i j => by
    simp only [Q, Matrix.of_apply]
    split_ifs
    · exact hP0 i j
    · exact le_rfl
  have hPt0 : ∀ t i j, 0 ≤ (P ^ t) i j := by
    intro t
    induction t with
    | zero => intro i j; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    | succ t ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      exact sum_nonneg fun k _ => mul_nonneg (ih i k) (hP0 k j)
  have hQt0 : ∀ t i j, 0 ≤ (Q ^ t) i j := by
    intro t
    induction t with
    | zero => intro i j; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    | succ t ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      exact sum_nonneg fun k _ => mul_nonneg (ih i k) (hQ0 k j)
  have hQtle : ∀ t i j, (Q ^ t) i j ≤ (P ^ t) i j := by
    intro t
    induction t with
    | zero => intro i j; rw [pow_zero, pow_zero]
    | succ t ih =>
      intro i j
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
      exact sum_le_sum fun k _ => mul_le_mul (ih i k) (hQle k j) (hQ0 k j) (hPt0 t i k)
  have hmono : ∀ t (v w : n → ℝ), (∀ j, v j ≤ w j) → ∀ i, (Q ^ t *ᵥ v) i ≤ (Q ^ t *ᵥ w) i := by
    intro t v w hvw i
    change ∑ j, (Q ^ t) i j * v j ≤ ∑ j, (Q ^ t) i j * w j
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hvw j) (hQt0 t i j)
  have hnn : ∀ (v : n → ℝ), (∀ j, 0 ≤ v j) → ∀ t i, 0 ≤ (Q ^ t *ᵥ v) i := by
    intro v hv t
    induction t with
    | zero => intro i; simpa using hv i
    | succ t ih =>
      intro i
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      change 0 ≤ ∑ j, Q i j * (Q ^ t *ᵥ v) j
      exact sum_nonneg fun j _ => mul_nonneg (hQ0 i j) (ih j)
  have hu0 : ∀ j, 0 ≤ u j := fun j => by simp only [u]; split_ifs <;> norm_num
  have hu1 : ∀ j, |u j| ≤ 1 := fun j => by simp only [u]; split_ifs <;> norm_num
  have hQA : ∀ i ∈ A, ∀ v : n → ℝ, (Q *ᵥ v) i = 0 := by
    intro i hi v
    change ∑ j, Q i j * v j = 0
    exact sum_eq_zero fun j _ => by simp [Q, hi]
  have hQoff : ∀ i ∉ A, ∀ v : n → ℝ, (∀ j ∈ A, v j = 0) →
      (Q *ᵥ v) i = ∑ j, P i j * v j := by
    intro i hi v hv
    change ∑ j, Q i j * v j = _
    refine sum_congr rfl fun j _ => ?_
    by_cases hj : j ∈ A
    · simp [hv j hj]
    · simp [Q, hi, hj]
  -- rows of `Q` sum to at most `1`, and `Q 1 ≤ u`
  have hQ1 : ∀ i, (Q *ᵥ fun _ => (1:ℝ)) i ≤ 1 := by
    intro i
    change ∑ j, Q i j * 1 ≤ 1
    have := sum_le_sum fun j (_ : j ∈ univ) => hQle i j
    simpa [hP i] using this
  have hQu : ∀ j, (Q *ᵥ fun _ => (1:ℝ)) j ≤ u j := by
    intro j
    by_cases hj : j ∈ A
    · rw [hQA j hj]; exact hu0 j
    · have hu : u j = 1 := by simp [u, hj]
      rw [hu]; exact hQ1 j
  have he_succ : ∀ t i, (Q ^ (t + 1) *ᵥ fun _ => (1:ℝ)) i ≤ (Q ^ t *ᵥ fun _ => (1:ℝ)) i := by
    intro t i
    rw [pow_succ, ← Matrix.mulVec_mulVec]
    exact hmono t _ _ hQ1 i
  have hanti : ∀ i s t, s ≤ t →
      (Q ^ t *ᵥ fun _ => (1:ℝ)) i ≤ (Q ^ s *ᵥ fun _ => (1:ℝ)) i := by
    intro i s t hst
    induction t, hst using Nat.le_induction with
    | base => exact le_rfl
    | succ t _ ih => exact (he_succ t i).trans ih
  have he1 : ∀ t i, (Q ^ t *ᵥ fun _ => (1:ℝ)) i ≤ 1 := fun t i =>
    (hanti i 0 t (Nat.zero_le _)).trans (by simp)
  have hPone : ∀ t, (P ^ t *ᵥ fun _ => (1:ℝ)) = fun _ => 1 := by
    have hP1 : (P *ᵥ fun _ => (1:ℝ)) = fun _ => 1 := funext fun i => by
      change ∑ j, P i j * 1 = 1
      simp [hP i]
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hP1, ih]
  have hQPu : ∀ t i, (Q ^ t *ᵥ u) i ≤ (P ^ t *ᵥ u) i := by
    intro t i
    change ∑ j, (Q ^ t) i j * u j ≤ ∑ j, (P ^ t) i j * u j
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hQtle t i j) (hu0 j)
  -- from every start, the chance of staying outside `A` eventually drops below `1`
  have hex : ∀ i, ∃ s, (Q ^ s *ᵥ fun _ => (1:ℝ)) i < 1 := by
    intro i
    by_cases hi : i ∈ A
    · refine ⟨1, ?_⟩
      rw [pow_one, hQA i hi]
      norm_num
    · obtain ⟨t, a, ha, hpos⟩ := hreach i hi
      refine ⟨t + 1, ?_⟩
      have h1 : (Q ^ (t + 1) *ᵥ fun _ => (1:ℝ)) i ≤ (P ^ t *ᵥ u) i := by
        rw [pow_succ, ← Matrix.mulVec_mulVec]
        exact (hmono t _ _ hQu i).trans (hQPu t i)
      have h2 : (P ^ t *ᵥ u) i + (P ^ t) i a ≤ 1 := by
        have e1 : (P ^ t *ᵥ fun _ => (1:ℝ)) i = 1 := by rw [hPone t]
        have e2 : (P ^ t *ᵥ fun _ => (1:ℝ)) i - (P ^ t *ᵥ u) i
            = ∑ j, (P ^ t) i j * (1 - u j) := by
          change ∑ j, (P ^ t) i j * 1 - ∑ j, (P ^ t) i j * u j = _
          rw [← sum_sub_distrib]
          exact sum_congr rfl fun j _ => by ring
        have h3 : (P ^ t) i a * (1 - u a) ≤ ∑ j, (P ^ t) i j * (1 - u j) :=
          single_le_sum (f := fun j => (P ^ t) i j * (1 - u j))
            (fun j _ => mul_nonneg (hPt0 t i j) (by simp only [u]; split_ifs <;> norm_num))
            (mem_univ a)
        have hua : u a = 0 := by simp [u, ha]
        rw [hua, sub_zero, mul_one] at h3
        linarith
      linarith
  choose s hs using hex
  obtain ⟨N, hN1, hsN⟩ : ∃ N : ℕ, 1 ≤ N ∧ ∀ i, s i ≤ N :=
    ⟨univ.sup s + 1, by omega, fun i => (le_sup (f := s) (mem_univ i)).trans (Nat.le_succ _)⟩
  obtain ⟨c, hc0, hc1, hcN⟩ : ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
      ∀ i, (Q ^ N *ᵥ fun _ => (1:ℝ)) i ≤ c := by
    rcases isEmpty_or_nonempty n with hn | hn
    · exact ⟨0, le_rfl, one_pos, fun i => isEmptyElim i⟩
    · obtain ⟨k, -, hk⟩ :=
        exists_max_image univ (fun i => (Q ^ N *ᵥ fun _ => (1:ℝ)) i) univ_nonempty
      exact ⟨max ((Q ^ N *ᵥ fun _ => (1:ℝ)) k) 0, le_max_right _ _,
        max_lt ((hanti k _ _ (hsN k)).trans_lt (hs k)) one_pos,
        fun i => (hk i (mem_univ i)).trans (le_max_left _ _)⟩
  -- a one-step rate `ρ` with `c ≤ ρ ^ N`
  obtain ⟨ρ, hρ0, hρ1, hρN⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ c ≤ ρ ^ N := by
    have hNpos : (0:ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hN1' : (1:ℝ) ≤ N := by exact_mod_cast hN1
    have hx0 : 0 < (1 - c) / (2 * N) := div_pos (by linarith) (by positivity)
    have hxh : (1 - c) / (2 * N) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hNx : (N:ℝ) * ((1 - c) / (2 * N)) = (1 - c) / 2 := by
      calc (N:ℝ) * ((1 - c) / (2 * N)) = (1 - c) / 2 * ((N:ℝ) / N) := by ring
        _ = (1 - c) / 2 := by rw [div_self hNpos.ne', mul_one]
    have hb : 1 - (N : ℝ) * ((1 - c) / (2 * N)) ≤ (1 - (1 - c) / (2 * N)) ^ N := by
      simpa [sub_eq_add_neg] using one_add_mul_le_pow (a := -((1 - c) / (2 * N))) (by linarith) N
    refine ⟨1 - (1 - c) / (2 * N), by linarith, by linarith, ?_⟩
    linarith
  have habs : ∀ t (v : n → ℝ) (M : ℝ), (∀ j, |v j| ≤ M) →
      ∀ i, |(Q ^ t *ᵥ v) i| ≤ (Q ^ t *ᵥ fun _ => (1:ℝ)) i * M := by
    intro t v M hv i
    calc |(Q ^ t *ᵥ v) i| = |∑ j, (Q ^ t) i j * v j| := rfl
      _ ≤ ∑ j, |(Q ^ t) i j * v j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, (Q ^ t) i j * M := sum_le_sum fun j _ => by
          rw [abs_mul, abs_of_nonneg (hQt0 t i j)]
          exact mul_le_mul_of_nonneg_left (hv j) (hQt0 t i j)
      _ = (Q ^ t *ᵥ fun _ => (1:ℝ)) i * M := by
          rw [show (Q ^ t *ᵥ fun _ => (1:ℝ)) i = ∑ j, (Q ^ t) i j * 1 from rfl, sum_mul]
          simp only [mul_one]
  have hK : ∀ t, t ≤ N → 1 ≤ (ρ ^ N)⁻¹ * ρ ^ t := by
    intro t ht
    have hpos : 0 < ρ ^ N := pow_pos hρ0 N
    calc (1:ℝ) = (ρ ^ N)⁻¹ * ρ ^ N := (inv_mul_cancel₀ hpos.ne').symm
      _ ≤ (ρ ^ N)⁻¹ * ρ ^ t :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ0.le hρ1.le ht)
            (inv_nonneg.mpr hpos.le)
  have hdec' : ∀ T t, t ≤ T → ∀ (v : n → ℝ) (M : ℝ), (∀ j, |v j| ≤ M) →
      ∀ i, |(Q ^ t *ᵥ v) i| ≤ (ρ ^ N)⁻¹ * ρ ^ t * M := by
    have small : ∀ t, t < N → ∀ (v : n → ℝ) (M : ℝ), (∀ j, |v j| ≤ M) →
        ∀ i, |(Q ^ t *ᵥ v) i| ≤ (ρ ^ N)⁻¹ * ρ ^ t * M := by
      intro t ht v M hv i
      have hM : 0 ≤ M := (abs_nonneg _).trans (hv i)
      calc |(Q ^ t *ᵥ v) i| ≤ (Q ^ t *ᵥ fun _ => (1:ℝ)) i * M := habs t v M hv i
        _ ≤ 1 * M := mul_le_mul_of_nonneg_right (he1 t i) hM
        _ ≤ (ρ ^ N)⁻¹ * ρ ^ t * M := mul_le_mul_of_nonneg_right (hK t ht.le) hM
    intro T
    induction T with
    | zero => intro t ht; exact small t (by omega)
    | succ T ih =>
      intro t ht v M hv i
      by_cases htN : t < N
      · exact small t htN v M hv i
      · have hM : 0 ≤ M := (abs_nonneg _).trans (hv i)
        have hv' : ∀ j, |(Q ^ N *ᵥ v) j| ≤ ρ ^ N * M := fun j =>
          (habs N v M hv j).trans (mul_le_mul_of_nonneg_right ((hcN j).trans hρN) hM)
        have e1 : Q ^ t *ᵥ v = Q ^ (t - N) *ᵥ (Q ^ N *ᵥ v) := by
          rw [Matrix.mulVec_mulVec, ← pow_add, Nat.sub_add_cancel (by omega : N ≤ t)]
        have e2 : ρ ^ t = ρ ^ (t - N) * ρ ^ N := by
          rw [← pow_add, Nat.sub_add_cancel (by omega : N ≤ t)]
        rw [e1]
        calc _ ≤ (ρ ^ N)⁻¹ * ρ ^ (t - N) * (ρ ^ N * M) := ih (t - N) (by omega) _ _ hv' i
          _ = (ρ ^ N)⁻¹ * ρ ^ t * M := by rw [e2]; ring
  have hdec : ∀ t (v : n → ℝ) (M : ℝ), (∀ j, |v j| ≤ M) →
      ∀ i, |(Q ^ t *ᵥ v) i| ≤ (ρ ^ N)⁻¹ * ρ ^ t * M := fun t => hdec' t t le_rfl
  have hsum : ∀ i, Summable fun t => (Q ^ t *ᵥ u) i := fun i =>
    Summable.of_nonneg_of_le (fun t => hnn u hu0 t i)
      (fun t => by
        have := hdec t u 1 hu1 i
        rwa [abs_of_nonneg (hnn u hu0 t i)] at this)
      (((summable_geometric_of_lt_one hρ0.le hρ1).mul_left ((ρ ^ N)⁻¹)).mul_right 1)
  have fixsol : ∀ g : n → ℝ, g = u + Q *ᵥ g →
      (∀ i ∈ A, g i = 0) ∧ ∀ i ∉ A, g i = 1 + ∑ j, P i j * g j := by
    intro g hg
    have h0 : ∀ i ∈ A, g i = 0 := fun i hi => by
      have := congrFun hg i
      rw [Pi.add_apply, hQA i hi] at this
      simpa [u, hi] using this
    refine ⟨h0, fun i hi => ?_⟩
    have := congrFun hg i
    rw [Pi.add_apply, hQoff i hi g h0] at this
    simpa [u, hi] using this
  have solfix : ∀ g : n → ℝ,
      ((∀ i ∈ A, g i = 0) ∧ ∀ i ∉ A, g i = 1 + ∑ j, P i j * g j) → g = u + Q *ᵥ g := by
    rintro g ⟨h0, h1⟩
    funext i
    rw [Pi.add_apply]
    by_cases hi : i ∈ A
    · rw [h0 i hi, hQA i hi]; simp [u, hi]
    · rw [hQoff i hi g h0, h1 i hi]; simp [u, hi]
  have hfixh : h = u + Q *ᵥ h := by
    funext i
    have H1 : HasSum (fun t => (Q ^ (t + 1) *ᵥ u) i)
        (h i - ∑ k ∈ range 1, (Q ^ k *ᵥ u) i) :=
      (hasSum_nat_add_iff' 1).mpr (hsum i).hasSum
    have H2 : HasSum (fun t => (Q ^ (t + 1) *ᵥ u) i) (∑ j, Q i j * h j) := by
      have e : (fun t => (Q ^ (t + 1) *ᵥ u) i) = fun t => ∑ j, Q i j * (Q ^ t *ᵥ u) j := by
        funext t
        rw [pow_succ', ← Matrix.mulVec_mulVec]
        rfl
      rw [e]
      exact hasSum_sum fun j _ => (hsum j).hasSum.mul_left (Q i j)
    have := H1.unique H2
    rw [Finset.sum_range_one, pow_zero, Matrix.one_mulVec] at this
    change h i = u i + ∑ j, Q i j * h j
    linarith
  refine ⟨hsum, fun g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · have hg' := solfix g hg
    have hd : Q *ᵥ (g - h) = g - h := by
      funext i
      have e1 := congrFun hg' i
      have e2 := congrFun hfixh i
      rw [Pi.add_apply] at e1 e2
      simp only [Matrix.mulVec_sub, Pi.sub_apply]
      linarith
    have hdt : ∀ t : ℕ, Q ^ t *ᵥ (g - h) = g - h := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, hd]
    funext i
    have hb : ∀ t : ℕ, |(g - h) i| ≤ (ρ ^ N)⁻¹ * ρ ^ t * ∑ j, |(g - h) j| := fun t => by
      have := hdec t (g - h) (∑ j, |(g - h) j|)
        (fun j => single_le_sum (f := fun j => |(g - h) j|) (fun j _ => abs_nonneg _)
          (mem_univ j)) i
      rwa [hdt t] at this
    have hlim : Tendsto (fun t : ℕ => (ρ ^ N)⁻¹ * ρ ^ t * ∑ j, |(g - h) j|) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).const_mul
        ((ρ ^ N)⁻¹)).mul_const (∑ j, |(g - h) j|)
      rwa [mul_zero, zero_mul] at this
    have h3 := ge_of_tendsto' hlim hb
    have h4 : (g - h) i = 0 := abs_nonpos_iff.mp h3
    rwa [Pi.sub_apply, sub_eq_zero] at h4
  · rw [hg]
    exact fixsol h hfixh

/-- **Mean hitting times when every step chance is at least `δ > 0`** (item 148 of
MATH-PLAN-library-2: the draft's earlier statement, kept as a corollary of `meanHitting_eq`). With
`P`, `Q`, `u` and `h` as in `meanHitting_eq`, and every entry of `P` at least `δ > 0`: the target
`A` is nonempty (`hA`), so from every state it is reached in one step with chance at least `δ`,
and `meanHitting_eq` applies. -/
theorem meanHitting_eq_of_le {n : Type*} [Fintype n] [DecidableEq n] {P : Matrix n n ℝ} {δ : ℝ}
    (hP : ∀ i, ∑ j, P i j = 1) (hδ0 : 0 < δ) (hδ : ∀ i j, δ ≤ P i j) {A : Finset n}
    (hA : A.Nonempty) :
    let Q : Matrix n n ℝ := Matrix.of fun i j => if i ∈ A ∨ j ∈ A then 0 else P i j
    let u : n → ℝ := fun i => if i ∈ A then 0 else 1
    let h : n → ℝ := fun i => ∑' t, (Q ^ t *ᵥ u) i
    (∀ i, Summable fun t => (Q ^ t *ᵥ u) i) ∧
    ∀ g : n → ℝ, ((∀ i ∈ A, g i = 0) ∧ ∀ i ∉ A, g i = 1 + ∑ j, P i j * g j) ↔ g = h := by
  obtain ⟨a, ha⟩ := hA
  exact meanHitting_eq hP (fun i j => hδ0.le.trans (hδ i j))
    (fun i _ => ⟨1, a, ha, by rw [pow_one]; exact hδ0.trans_le (hδ i a)⟩)

end ClassicalLean.Probability

open Matrix in
/-- The hypotheses of `existsUnique_vecMul_eq_self` hold together: the `2 × 2` matrix with rows
`(3/4, 1/4)` and `(1/4, 3/4)`, each row summing to `1`, every entry at least `δ = 1/4 > 0`; the
theorem's constant `1 - 2 δ` is `1/2`, not `0`. -/
example := ClassicalLean.Probability.existsUnique_vecMul_eq_self (n := Fin 2)
  (P := !![3 / 4, 1 / 4; 1 / 4, 3 / 4]) (δ := 1 / 4)
  (fun i => by fin_cases i <;> norm_num [Fin.sum_univ_two])
  (by norm_num)
  (fun i j => by fin_cases i <;> fin_cases j <;> norm_num)

open Matrix in
/-- The hypotheses of `sum_abs_vecMul_pow_sub_le` hold together: the `2 × 2` matrix with rows
`(3/4, 1/4)` and `(1/4, 3/4)`, each row summing to `1`, every entry at least `δ = 1/4`, so the
rate `1 − 2 δ = 1/2` is not `0`; the start `μ = (1, 0)` and the stationary `π = (1/2, 1/2)` both
sum to `1`, and `π P = π`; `t = 3`. -/
example := ClassicalLean.Probability.sum_abs_vecMul_pow_sub_le (n := Fin 2)
  (P := !![3 / 4, 1 / 4; 1 / 4, 3 / 4]) (δ := 1 / 4)
  (fun i ↦ by fin_cases i <;> norm_num [Fin.sum_univ_two])
  (fun i j ↦ by fin_cases i <;> fin_cases j <;> norm_num) (μ := ![1, 0]) (π := ![1 / 2, 1 / 2])
  (by norm_num [Fin.sum_univ_two])
  (by ext j; fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_two] <;> norm_num) (t := 3)

open Matrix in
/-- The hypotheses of `relEntropy_vecMul_le_of_stationary` hold together: the chain with rows
`(1/2, 1/2)` and `(1/4, 3/4)`, its stationary law `π = (1/3, 2/3)` (positive, so the support
condition holds for every `μ`), and `μ = (1, 0)`, which is not stationary, so the two sides
differ. -/
example := ClassicalLean.Probability.relEntropy_vecMul_le_of_stationary (n := Fin 2)
  (P := !![1 / 2, 1 / 2; 1 / 4, 3 / 4]) (μ := ![1, 0]) (π := ![1 / 3, 2 / 3])
  (fun i j ↦ by fin_cases i <;> fin_cases j <;> norm_num)
  (fun i ↦ by fin_cases i <;> norm_num [Fin.sum_univ_two])
  (fun i ↦ by fin_cases i <;> norm_num)
  (fun i h ↦ by fin_cases i <;> norm_num at h)
  (by ext j; fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_two] <;> norm_num)

open Matrix in
/-- The hypotheses of `existsUnique_vecMul_eq_self_of_pow` hold together: the chain with rows
`(0, 1)` and `(1/2, 1/2)`, which has a zero entry (so `existsUnique_vecMul_eq_self` does not apply
to it), and `k = 2`: `P ^ 2` has rows `(1/2, 1/2)` and `(1/4, 3/4)`, every entry positive. -/
example := ClassicalLean.Probability.existsUnique_vecMul_eq_self_of_pow (n := Fin 2)
  (P := !![0, 1; 1 / 2, 1 / 2]) (k := 2)
  (fun i ↦ by fin_cases i <;> norm_num [Fin.sum_univ_two])
  (fun i j ↦ by fin_cases i <;> fin_cases j <;> norm_num [sq, mul_apply, Fin.sum_univ_two])

open Matrix in
/-- The hypotheses of `sum_abs_vecMul_pow_sub_le_of_pow` hold together: the same chain (a zero
entry, `P ≥ 0`, rows summing to `1`), `k = 2` and `δ = 1/4`, the least entry of `P ^ 2`, so the
rate `1 − 2 δ = 1/2` is not `0`; the start `μ = (1, 0)` and the stationary `π = (1/3, 2/3)` both
sum to `1`; `t = 5`, so `t / k = 2` steps of the rate count. -/
example := ClassicalLean.Probability.sum_abs_vecMul_pow_sub_le_of_pow (n := Fin 2)
  (P := !![0, 1; 1 / 2, 1 / 2]) (k := 2) (δ := 1 / 4)
  (fun i j ↦ by fin_cases i <;> fin_cases j <;> norm_num)
  (fun i ↦ by fin_cases i <;> norm_num [Fin.sum_univ_two])
  (fun i j ↦ by fin_cases i <;> fin_cases j <;> norm_num [sq, mul_apply, Fin.sum_univ_two])
  (μ := ![1, 0]) (π := ![1 / 3, 2 / 3]) (by norm_num [Fin.sum_univ_two])
  (by ext j; fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_two] <;> norm_num) (t := 5)

open Matrix in
/-- The hypotheses of `meanHitting_eq` hold together: the chain on three states with rows
`(1/2, 1/2, 0)`, `(0, 1/2, 1/2)` and `(0, 0, 1)`, each row summing to `1` and every entry at least
`0` (it has zero entries, so `meanHitting_eq_of_le` does not apply to it), and the target
`A = {2}`, reached from state `1` in one step and from state `0` only in two. The witness was
proposed by order LEAN-35's review (e). -/
example := ClassicalLean.Probability.meanHitting_eq (n := Fin 3)
  (P := !![1 / 2, 1 / 2, 0; 0, 1 / 2, 1 / 2; 0, 0, 1])
  (fun i ↦ by fin_cases i <;> norm_num [Fin.sum_univ_three])
  (fun i j ↦ by fin_cases i <;> fin_cases j <;> norm_num)
  (A := {2})
  (fun i hi ↦ by
    fin_cases i
    · exact ⟨2, 2, by simp, by norm_num [sq, Matrix.mul_apply, Fin.sum_univ_three]⟩
    · exact ⟨1, 2, by simp, by norm_num⟩
    · simp at hi)

open Matrix in
/-- The hypotheses of `meanHitting_eq_of_le` hold together: the chain on two states with rows
`(3/4, 1/4)` and `(1/4, 3/4)`, each row summing to `1` and every entry at least `δ = 1/4 > 0`, and
the target `A = {1}`, nonempty. -/
example := ClassicalLean.Probability.meanHitting_eq_of_le (n := Fin 2)
  (P := !![3 / 4, 1 / 4; 1 / 4, 3 / 4]) (δ := 1 / 4)
  (fun i ↦ by fin_cases i <;> norm_num [Fin.sum_univ_two])
  (by norm_num)
  (fun i j ↦ by fin_cases i <;> fin_cases j <;> norm_num)
  (A := {1}) ⟨1, by simp⟩
