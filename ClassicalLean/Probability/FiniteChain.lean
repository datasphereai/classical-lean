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
  `∑ j, |(μ P ^ t) j − π j| ≤ (1 − n δ) ^ (t / k) ∑ j, |μ j − π j|`. The route: `t = k (t / k) +
  t % k`; first `sum_abs_vecMul_pow_sub_le` for `P ^ k` over the `t / k` steps, then
  `sum_abs_vecMul_pow_le` with `δ = 0` (factor `1`) over the remaining `t % k` steps of `P`, so no
  sign of `1 − n δ` is needed.

**Wider than the plan's reading:** the plan states the hypothesis with Mathlib's
`Matrix.IsPrimitive` "where it fits". It does not fit here: `Matrix.IsPrimitive` is not in this
module's imports, and it carries two conditions the uniqueness theorem does not need, `P ≥ 0`
(`100.unique.neg`, and the BY HAND line `100.unique`) and `k > 0` (at `k = 0`, `P ^ 0 = 1` has every
entry positive only with one state, where `P = (1)`). Nor does the rate theorem need `k > 0`: Lean's
`t / 0 = 0` makes the factor `1` (`100.k0`). A primitive matrix in Mathlib's sense
(`Matrix.IsPrimitive`, `LinearAlgebra/Matrix/Irreducible/Defs.lean`) meets `hpos` through its
field `exists_pos_pow` (named here, not imported). **Also, as written in the order's statement, not
a new change:** the rate theorem asks no `δ > 0` (any real `δ`; for `δ ≤ 0` the factor is at least
`1`), lets `μ` have any sign, and lets `π` be any stationary vector with `μ`'s total, exactly as
`sum_abs_vecMul_pow_sub_le` above.

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

Order LEAN-30 (item 100), the plan's search (`MATH-PLAN-library-2-checks.py`, lines `row.L7`):
`perron` 6 lines in 6 files of pinned Mathlib and of Mathlib master at `2da3ab0a`, the Perron
integral (`BoxIntegral`) and its citations, none about matrices; `stationary distribution|invariant
distribution` 0 in both; Mathlib defines primitive matrices, `Matrix.IsPrimitive`, with no theorem
of this kind. Item 97 uses `relEntropy_vecMul_le` (InformationTheory.Channel); item 100 uses this
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
