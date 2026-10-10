/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Analysis.ExponentialWeights
import ClassicalLean.Simplex.Basic
import Mathlib.Topology.Sion
import Mathlib.Probability.Decision.Risk.Basic
import Mathlib.Probability.Decision.Risk.Countable

/-!
# Finite games: the minimax theorem, Bayes equals minimax, and the value by learning

A finite two-player zero-sum game is a real matrix `A` with rows `ι` and columns `κ`. The row
player picks a mixed strategy `x` (a probability vector on the rows, a point of
`closedSimplex ι`), the column player picks `y`, and the row player pays the column player
`payoff A x y = xᵀ A y`. The row player wants it small, the column player large.

* **Item 62, von Neumann's minimax theorem.** `exists_isSaddlePoint_matrix`: there are
  strategies `x*` and `y*` with `payoff A x* y ≤ payoff A x* y* ≤ payoff A x y*` for all
  strategies `x` and `y` (Mathlib's `IsSaddlePointOn`): neither player gains by moving alone.
  `minimax_eq_of_matrix`: the upper value `⨅ x, ⨆ y, payoff A x y` equals the lower value
  `⨆ y, ⨅ x, payoff A x y`. Both are taken over the strategies as a subtype, so no infimum or
  supremum over an empty set appears; the families are bounded (`abs_payoff_le`). Proved from
  Mathlib's Sion theorem (`Sion.exists_isSaddlePointOn`) on the two simplices, which are
  compact (`isCompact_closedSimplex`) and convex, with a payoff linear in each strategy.
* **Item 63, Bayes equals minimax.** `iSup_bayesRisk_eq_minimaxRisk_of_finite`: with finitely
  many parameters `Θ`, data values `𝓧` and actions `𝓨`, every singleton measurable, a finite
  kernel `P` (the law of the data under each parameter) and a loss `ℓ` with no infinite value,
  the largest Bayes risk over prior probability measures equals the minimax risk. Mathlib's
  own `bayesRisk` and `minimaxRisk` are used as they are: rules are Markov kernels from data
  to actions (randomized rules), losses take values in `[0, ∞]`. Mathlib proves only `≤`
  (`iSup_bayesRisk_le_minimaxRisk`). The proof writes a rule as a matrix `K x y` (the chance
  of action `y` after data `x`; `ruleSet`) and a prior as a probability vector, so the average
  risk `matrixAvgRisk` is a game linear in each; Sion's theorem gives a saddle point, as for
  item 62, and `ruleKernel`, `priorMeasure` and `lintegral_comp_eq_ofReal_matrixRisk` carry it
  to Mathlib's definitions.
* **Item 66, the value by exponential weights.** For payoffs in `[0, 1]`, the row player runs
  the library's exponential weights (`ExponentialWeights`), treating row `i`'s payment
  `(A y_t) i` in round `t` as that expert's loss: `ewStrategy A η y t = softmax (−η · the
  payments so far)`. In each round the column player answers with a best response `y t`: a
  strategy with the largest payoff against `x t = ewStrategy A η y t` (`IsBestResponse`; a pure
  one always exists, `exists_bestResponse`, so such sequences exist,
  `exists_bestResponse_seq`). The averaged strategies are `x̄ = (1/T) ∑_{t<T} x t` and
  `ȳ = (1/T) ∑_{t<T} y t` (`average`). Then `gap_le_of_exponentialWeights`: `x̄` and `ȳ`
  are strategies and

      (⨆ y, payoff A x̄ y) − (⨅ x, payoff A x ȳ) ≤ log m / (η T) + η / 8,

  `m` the number of rows; with `η = √(8 log m / T)` the right side is `√(log m / (2 T))`
  (`gap_le_sqrt_of_exponentialWeights`; with one row `η = 0` and the gap is `0`). Since the
  lower value is at most the upper value (`iSup_iInf_le_iInf_iSup`, weak duality), `x̄` is
  within that of the best the row player can guarantee, and `ȳ` likewise for the column player,
  with explicit strategies. This is proved without item 62:
  `abs_value_sub_le_of_exponentialWeights` and `abs_value_sub_le_sqrt_of_exponentialWeights`
  bound the gap between the upper and lower values by the same quantities, and letting `T` grow
  gives
  `minimax_eq_of_exponentialWeights`, **a second proof of the equality in item 62**, for
  payoffs in `[0, 1]` (any matrix reduces to that by an affine change of payoffs, not proved
  here).

## Hypotheses

Checked in order LEAN-25 (`~/lean/lean25-checks/checks.py`; exact fractions unless marked):

* Item 62, nonempty `ι` and `κ`: with no rows the simplex is empty and no saddle point
  exists. The equality of values would still hold, but only because Lean reads an infimum or
  supremum over an empty family of reals as `0`.
* Item 66, payoffs in `[0, 1]`: the range enters only through Hoeffding's lemma
  (`logSumExp_add_smul_le`, the `η² / 8` term, Hoeffding's bound for values in an interval of
  length `1`), and the `1/2` under the root comes from that `8`. With `A = 10 · I₂` and
  `T = 1`: `x̄ = (1/2, 1/2)`, the upper side is `5`, a pure best response gives lower side
  `0`, gap `5 > √(log 2 / 2)`.
  Adding a constant to every payoff changes nothing; the lower bound `0` is kept for the
  library lemma.
* Item 66, `η > 0`: at `η = 0`, `log m / (0 · T)` is Lean's `0`, the weights stay uniform,
  and for `A = I₂` with best response always the first column the gap is `1/2 > 0`.
* Item 66, `T > 0`: at `T = 0` the averages are `0 / 0 = 0`, not strategies.
* Item 63, `ℓ θ y ≠ ∞`: kept; whether it is needed is open (an example with an infinite loss
  still gives equality, both sides `1`).
* Item 63, a nonempty action set `𝓨`: with no parameters, some data value and no action, the
  left side is `0` (no prior exists) and the right side is `∞` (no Markov kernel exists, and
  Lean's infimum over nothing in `[0, ∞]` is `∞`). That is the only failing case (by hand):
  with no action, some data value and some parameter both sides are `∞`; with no action and no
  data value the one empty rule is a Markov kernel and both sides are `0`. With no parameters
  and some action both sides are `0`, which the theorem covers.

## What is cited

Von Neumann 1928, "Zur Theorie der Gesellschaftsspiele"; Sion 1958, "On general minimax
theorems" (the proof is Mathlib's); Wald 1950, "Statistical Decision Functions"; Freund and
Schapire 1999, "Adaptive game playing using multiplicative weights". Not read here: author,
title and year only.

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-25, `grep -rliE`): "minimax|Minimax" 4
files: Sion's theorem (Topology/Sion.lean, whose docstring lists the von Neumann case as still
to do), `IsSaddlePointOn`, and Probability/Decision/Risk (the definitions and the inequality
only); "exponential weight|multiplicative weight" 0. Mathlib's `stdSimplex` is deprecated at
v4.34.0; the library's `closedSimplex` is the same set (see `Simplex/Basic`).
-/

open Finset Matrix
open ClassicalLean.Simplex

namespace ClassicalLean.Analysis

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The payoff `xᵀ A y` that the row player (strategy `x`) pays the column player (`y`). -/
def payoff (A : Matrix ι κ ℝ) (x : ι → ℝ) (y : κ → ℝ) : ℝ := x ⬝ᵥ A *ᵥ y

/-- The closed simplex is compact: closed, inside the cube `[0, 1]^ι`. -/
theorem isCompact_closedSimplex : IsCompact (closedSimplex ι) := by
  have hsub : closedSimplex ι ⊆ Set.univ.pi fun _ ↦ Set.Icc (0 : ℝ) 1 := by
    intro x hx i _
    refine ⟨hx.1 i, ?_⟩
    calc x i = ∑ j ∈ {i}, x j := by simp
      _ ≤ ∑ j, x j := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun j _ _ ↦ hx.1 j
      _ = 1 := hx.2
  have hclosed : IsClosed (closedSimplex ι) := by
    have : closedSimplex ι = (⋂ i, {x : ι → ℝ | 0 ≤ x i}) ∩ {x | ∑ i, x i = 1} := by
      ext x; simp [closedSimplex]
    rw [this]
    exact (isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_eq (by fun_prop) continuous_const)
  exact (isCompact_univ_pi fun _ ↦ isCompact_Icc).of_isClosed_subset hclosed hsub

/-- The simplex on a nonempty index set is nonempty (a corner). -/
theorem closedSimplex_nonempty [Nonempty ι] : (closedSimplex ι).Nonempty := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine ⟨Pi.single i 1, fun j ↦ ?_, by simp⟩
  by_cases h : j = i <;> simp [h]

/-- The payoff is additive in the row strategy. -/
theorem payoff_add_left (A : Matrix ι κ ℝ) (x x' : ι → ℝ) (y : κ → ℝ) :
    payoff A (x + x') y = payoff A x y + payoff A x' y := add_dotProduct _ _ _

/-- The payoff is homogeneous in the row strategy. -/
theorem payoff_smul_left (A : Matrix ι κ ℝ) (a : ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    payoff A (a • x) y = a * payoff A x y := smul_dotProduct _ _ _

/-- The payoff is additive in the column strategy. -/
theorem payoff_add_right (A : Matrix ι κ ℝ) (x : ι → ℝ) (y y' : κ → ℝ) :
    payoff A x (y + y') = payoff A x y + payoff A x y' := by
  simp [payoff, mulVec_add, dotProduct_add]

/-- The payoff is homogeneous in the column strategy. -/
theorem payoff_smul_right (A : Matrix ι κ ℝ) (a : ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    payoff A x (a • y) = a * payoff A x y := by
  simp [payoff, mulVec_smul, dotProduct_smul]

/-- The payoff is continuous in the row strategy. -/
theorem continuous_payoff_left (A : Matrix ι κ ℝ) (y : κ → ℝ) :
    Continuous fun x ↦ payoff A x y := by
  unfold payoff; fun_prop

/-- The payoff is continuous in the column strategy. -/
theorem continuous_payoff_right (A : Matrix ι κ ℝ) (x : ι → ℝ) :
    Continuous fun y ↦ payoff A x y := by
  unfold payoff; simp only [dotProduct, mulVec]; fun_prop

/-- **Von Neumann's minimax theorem (item 62), saddle-point form.** Both players have optimal
mixed strategies: `x*` and `y*` with `payoff A x* y ≤ payoff A x* y* ≤ payoff A x y*` for all
strategies `x`, `y`. -/
theorem exists_isSaddlePoint_matrix [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) :
    ∃ x ∈ closedSimplex ι, ∃ y ∈ closedSimplex κ,
      IsSaddlePointOn (closedSimplex ι) (closedSimplex κ) (payoff A) x y := by
  refine Sion.exists_isSaddlePointOn closedSimplex_nonempty convex_closedSimplex
    isCompact_closedSimplex
    (fun y _ ↦ (continuous_payoff_left A y).lowerSemicontinuous.lowerSemicontinuousOn _)
    (fun y _ ↦ ?_) convex_closedSimplex closedSimplex_nonempty isCompact_closedSimplex
    (fun x _ ↦ (continuous_payoff_right A x).upperSemicontinuous.upperSemicontinuousOn _)
    (fun x _ ↦ ?_)
  · refine ConvexOn.quasiconvexOn ⟨convex_closedSimplex, fun a _ b _ s t _ _ _ ↦ ?_⟩
    simp [payoff_add_left, payoff_smul_left]
  · refine ConcaveOn.quasiconcaveOn ⟨convex_closedSimplex, fun a _ b _ s t _ _ _ ↦ ?_⟩
    simp [payoff_add_right, payoff_smul_right]

/-- On the simplices the payoff is bounded by the sum of the entries' sizes. -/
theorem abs_payoff_le (A : Matrix ι κ ℝ) {x : ι → ℝ} {y : κ → ℝ} (hx : x ∈ closedSimplex ι)
    (hy : y ∈ closedSimplex κ) : |payoff A x y| ≤ ∑ i, ∑ j, |A i j| := by
  have hx1 : ∀ i, x i ≤ 1 := fun i ↦ by
    calc x i = ∑ j ∈ {i}, x j := by simp
      _ ≤ ∑ j, x j := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun j _ _ ↦ hx.1 j
      _ = 1 := hx.2
  have hy1 : ∀ j, y j ≤ 1 := fun j ↦ by
    calc y j = ∑ k ∈ {j}, y k := by simp
      _ ≤ ∑ k, y k := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun k _ _ ↦ hy.1 k
      _ = 1 := hy.2
  simp only [payoff, dotProduct, mulVec, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ ?_)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ ↦ ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg (hx.1 i), abs_of_nonneg (hy.1 j)]
  calc x i * (|A i j| * y j) ≤ 1 * (|A i j| * 1) := by
        gcongr
        · exact mul_nonneg (abs_nonneg _) (hy.1 j)
        · exact hx1 i
        · exact hy1 j
    _ = |A i j| := by ring

/-- Against a fixed row strategy, the payoffs over column strategies are bounded above. -/
theorem bddAbove_payoff (A : Matrix ι κ ℝ) {x : ι → ℝ} (hx : x ∈ closedSimplex ι) :
    BddAbove (Set.range fun y : closedSimplex κ ↦ payoff A x y) :=
  ⟨∑ i, ∑ j, |A i j|, by
    rintro _ ⟨y, rfl⟩; exact (le_abs_self _).trans (abs_payoff_le A hx y.2)⟩

/-- Against a fixed column strategy, the payoffs over row strategies are bounded below. -/
theorem bddBelow_payoff (A : Matrix ι κ ℝ) {y : κ → ℝ} (hy : y ∈ closedSimplex κ) :
    BddBelow (Set.range fun x : closedSimplex ι ↦ payoff A x y) :=
  ⟨-∑ i, ∑ j, |A i j|, by
    rintro _ ⟨x, rfl⟩; exact neg_le_of_abs_le (abs_payoff_le A x.2 hy)⟩

/-- The row player's worst cases are bounded below. -/
theorem bddBelow_iSup_payoff [Nonempty κ] (A : Matrix ι κ ℝ) :
    BddBelow (Set.range fun x : closedSimplex ι ↦ ⨆ y : closedSimplex κ, payoff A x y) := by
  have : Nonempty (closedSimplex κ) := closedSimplex_nonempty.to_subtype
  obtain ⟨y⟩ := this
  refine ⟨-∑ i, ∑ j, |A i j|, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (neg_le_of_abs_le (abs_payoff_le A x.2 y.2)).trans (le_ciSup (bddAbove_payoff A x.2) y)

/-- The column player's worst cases are bounded above. -/
theorem bddAbove_iInf_payoff [Nonempty ι] (A : Matrix ι κ ℝ) :
    BddAbove (Set.range fun y : closedSimplex κ ↦ ⨅ x : closedSimplex ι, payoff A x y) := by
  have : Nonempty (closedSimplex ι) := closedSimplex_nonempty.to_subtype
  obtain ⟨x⟩ := this
  refine ⟨∑ i, ∑ j, |A i j|, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact (ciInf_le (bddBelow_payoff A y.2) x).trans ((le_abs_self _).trans (abs_payoff_le A x.2 y.2))

/-- Weak duality: the lower value is at most the upper value. -/
theorem iSup_iInf_le_iInf_iSup [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) :
    ⨆ y : closedSimplex κ, ⨅ x : closedSimplex ι, payoff A x y ≤
      ⨅ x : closedSimplex ι, ⨆ y : closedSimplex κ, payoff A x y := by
  have : Nonempty (closedSimplex ι) := closedSimplex_nonempty.to_subtype
  have : Nonempty (closedSimplex κ) := closedSimplex_nonempty.to_subtype
  exact ciSup_le fun y ↦ le_ciInf fun x ↦
    (ciInf_le (bddBelow_payoff A y.2) x).trans (le_ciSup (bddAbove_payoff A x.2) y)

/-- **Von Neumann's minimax theorem (item 62), value form.** The upper value equals the lower
value. -/
theorem minimax_eq_of_matrix [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) :
    ⨅ x : closedSimplex ι, ⨆ y : closedSimplex κ, payoff A x y =
      ⨆ y : closedSimplex κ, ⨅ x : closedSimplex ι, payoff A x y := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_isSaddlePoint_matrix A
  have : Nonempty (closedSimplex ι) := closedSimplex_nonempty.to_subtype
  have : Nonempty (closedSimplex κ) := closedSimplex_nonempty.to_subtype
  refine le_antisymm ?_ (iSup_iInf_le_iInf_iSup A)
  calc ⨅ x : closedSimplex ι, ⨆ y : closedSimplex κ, payoff A x y
      ≤ ⨆ y : closedSimplex κ, payoff A a y := ciInf_le (bddBelow_iSup_payoff A) ⟨a, ha⟩
    _ ≤ payoff A a b := ciSup_le fun y ↦ hab a ha y y.2
    _ ≤ ⨅ x : closedSimplex ι, payoff A x b := le_ciInf fun x ↦ hab x x.2 b hb
    _ ≤ ⨆ y : closedSimplex κ, ⨅ x : closedSimplex ι, payoff A x y :=
        le_ciSup (f := fun y : closedSimplex κ ↦ ⨅ x : closedSimplex ι, payoff A x y)
          (bddAbove_iInf_payoff A) ⟨b, hb⟩

/-! ### Item 66 -/

/-- Exponential weights for the row player against column strategies `y`. -/
noncomputable def ewStrategy (A : Matrix ι κ ℝ) (η : ℝ) (y : ℕ → κ → ℝ) (t : ℕ) : ι → ℝ :=
  softmax fun i ↦ -η * ∑ s ∈ range t, (A *ᵥ y s) i

/-- `y` is a best response to the row strategy `x`: a column strategy with the largest payoff
against `x`. -/
def IsBestResponse (A : Matrix ι κ ℝ) (x : ι → ℝ) (y : κ → ℝ) : Prop :=
  y ∈ closedSimplex κ ∧ ∀ y' ∈ closedSimplex κ, payoff A x y' ≤ payoff A x y

/-- The average of the first `T` vectors of a sequence: `(1/T) ∑_{t<T} z t`. -/
noncomputable def average {α : Type*} (T : ℕ) (z : ℕ → α → ℝ) : α → ℝ :=
  fun a ↦ (∑ t ∈ range T, z t a) / T

/-- Exponential weights give a strategy. -/
theorem ewStrategy_mem [Nonempty ι] (A : Matrix ι κ ℝ) (η : ℝ) (y : ℕ → κ → ℝ) (t : ℕ) :
    ewStrategy A η y t ∈ closedSimplex ι :=
  ⟨fun i ↦ (softmax_pos _ i).le, sum_softmax _⟩

/-- An average of strategies is a strategy, for `T > 0`. -/
theorem average_mem {α : Type*} [Fintype α] {T : ℕ} (hT : 0 < T) {z : ℕ → α → ℝ}
    (hz : ∀ t, z t ∈ closedSimplex α) : average T z ∈ closedSimplex α := by
  have hT' : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  refine ⟨fun a ↦ div_nonneg (sum_nonneg fun t _ ↦ (hz t).1 a) hT'.le, ?_⟩
  simp only [average, ← sum_div]
  rw [sum_comm, sum_congr rfl fun t _ ↦ (hz t).2, sum_const, card_range, nsmul_eq_mul, mul_one,
    div_self hT'.ne']

/-- The payoff of an averaged row strategy is the average payoff. -/
theorem payoff_average_left (A : Matrix ι κ ℝ) (T : ℕ) (z : ℕ → ι → ℝ) (y : κ → ℝ) :
    payoff A (average T z) y = (∑ t ∈ range T, payoff A (z t) y) / T := by
  simp only [payoff, dotProduct, average, sum_div, div_mul_eq_mul_div, sum_mul]
  exact sum_comm

omit [Fintype ι] in
/-- `A` applied to an average is the average of `A` applied. -/
theorem mulVec_average (A : Matrix ι κ ℝ) (T : ℕ) (z : ℕ → κ → ℝ) (i : ι) :
    (A *ᵥ average T z) i = (∑ t ∈ range T, (A *ᵥ z t) i) / T := by
  simp only [mulVec, dotProduct, average, mul_div_assoc', ← sum_div, mul_sum]
  rw [sum_comm]

omit [Fintype ι] in
/-- With entries in `[0, 1]`, each row's payment against a strategy is in `[0, 1]`. -/
theorem mulVec_mem_Icc {A : Matrix ι κ ℝ} (hA : ∀ i j, A i j ∈ Set.Icc (0 : ℝ) 1)
    {y : κ → ℝ} (hy : y ∈ closedSimplex κ) (i : ι) : (A *ᵥ y) i ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨sum_nonneg fun j _ ↦ mul_nonneg (hA i j).1 (hy.1 j), ?_⟩
  calc (A *ᵥ y) i = ∑ j, A i j * y j := rfl
    _ ≤ ∑ j, 1 * y j := sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_right (hA i j).2 (hy.1 j)
    _ = 1 := by simp [hy.2]

/-- A strategy's average of numbers that are all at least `b` is at least `b`. -/
theorem le_dotProduct_of_le {x : ι → ℝ} (hx : x ∈ closedSimplex ι) {c : ι → ℝ} {b : ℝ}
    (hc : ∀ i, b ≤ c i) : b ≤ x ⬝ᵥ c := by
  calc b = ∑ i, x i * b := by rw [← sum_mul, hx.2, one_mul]
    _ ≤ ∑ i, x i * c i := sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hc i) (hx.1 i)

/-- **The game's value by exponential weights (item 66).** For payoffs in `[0, 1]`, `η > 0` and
`T > 0`, against best responses, the averaged strategies `x̄` and `ȳ` are strategies and
`(⨆ y, payoff A x̄ y) − (⨅ x, payoff A x ȳ) ≤ log m / (η T) + η / 8`. Item 62 is not used. -/
theorem gap_le_of_exponentialWeights [Nonempty ι] [Nonempty κ] {A : Matrix ι κ ℝ}
    (hA : ∀ i j, A i j ∈ Set.Icc (0 : ℝ) 1) {η : ℝ} (hη : 0 < η) {T : ℕ} (hT : 0 < T)
    {y : ℕ → κ → ℝ} (hy : ∀ t, IsBestResponse A (ewStrategy A η y t) (y t)) :
    average T (ewStrategy A η y) ∈ closedSimplex ι ∧ average T y ∈ closedSimplex κ ∧
    (⨆ y' : closedSimplex κ, payoff A (average T (ewStrategy A η y)) y') -
      (⨅ x' : closedSimplex ι, payoff A x' (average T y)) ≤
        Real.log (Fintype.card ι) / (η * T) + η / 8 := by
  have : Nonempty (closedSimplex ι) := closedSimplex_nonempty.to_subtype
  have : Nonempty (closedSimplex κ) := closedSimplex_nonempty.to_subtype
  have hT' : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  set x := ewStrategy A η y
  set ε := Real.log (Fintype.card ι) / (η * T) + η / 8
  set P := (∑ t ∈ range T, payoff A (x t) (y t)) / T
  refine ⟨average_mem hT (ewStrategy_mem A η y), average_mem hT fun t ↦ (hy t).1, ?_⟩
  have hup : ⨆ y' : closedSimplex κ, payoff A (average T x) y' ≤ P := by
    refine ciSup_le fun y' ↦ ?_
    rw [payoff_average_left]
    exact div_le_div_of_nonneg_right (sum_le_sum fun t _ ↦ (hy t).2 y' y'.2) hT'.le
  have hreg : ∀ i, P - ε ≤ (A *ᵥ average T y) i := by
    intro i
    have h := sum_inner_softmax_le (l := fun t j ↦ (A *ᵥ y t) j)
      (fun t j ↦ mulVec_mem_Icc hA (hy t).1 j) hη T i
    have hP : ∑ t ∈ range T, payoff A (x t) (y t) =
        ∑ t ∈ range T, ∑ j, softmax (fun k ↦ -η * ∑ s ∈ range t, (A *ᵥ y s) k) j *
          (A *ᵥ y t) j := rfl
    rw [mulVec_average]
    have hε : ε = (Real.log (Fintype.card ι) / η + η * T / 8) / T := by
      simp only [ε]; field_simp
    rw [hε, show P = (∑ t ∈ range T, payoff A (x t) (y t)) / T from rfl, hP, ← sub_div]
    exact div_le_div_of_nonneg_right (by linarith) hT'.le
  have hdown : P - ε ≤ ⨅ x' : closedSimplex ι, payoff A x' (average T y) :=
    le_ciInf fun x' ↦ le_dotProduct_of_le x'.2 hreg
  linarith

omit [Fintype κ] in
/-- The payoff against an averaged column strategy is the average payoff. -/
theorem payoff_average_right [Fintype κ] (A : Matrix ι κ ℝ) (T : ℕ) (x : ι → ℝ)
    (z : ℕ → κ → ℝ) : payoff A x (average T z) = (∑ t ∈ range T, payoff A x (z t)) / T := by
  simp only [payoff, dotProduct, mulVec_average, mul_div_assoc', mul_sum, ← sum_div]
  rw [sum_comm]

/-- With one row there is one strategy for the row player. -/
theorem eq_of_mem_closedSimplex_of_card_eq_one (hι : Fintype.card ι = 1) {x x' : ι → ℝ}
    (hx : x ∈ closedSimplex ι) (hx' : x' ∈ closedSimplex ι) : x = x' := by
  obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.mp hι
  have key : ∀ z ∈ closedSimplex ι, z = fun _ ↦ 1 := fun z hz ↦ by
    funext j
    rw [hi j, ← hz.2, Fintype.sum_eq_single i fun k hk ↦ absurd (hi k) hk]
  rw [key x hx, key x' hx']

/-- With one row, any row strategies against best responses leave no gap. -/
theorem gap_nonpos_of_card_eq_one [Nonempty ι] [Nonempty κ] {A : Matrix ι κ ℝ}
    (hι : Fintype.card ι = 1) {T : ℕ} (hT : 0 < T) {x : ℕ → ι → ℝ} {y : ℕ → κ → ℝ}
    (hx : ∀ t, x t ∈ closedSimplex ι) (hy : ∀ t, IsBestResponse A (x t) (y t)) :
    (⨆ y' : closedSimplex κ, payoff A (average T x) y') -
      (⨅ x' : closedSimplex ι, payoff A x' (average T y)) ≤ 0 := by
  have : Nonempty (closedSimplex ι) := closedSimplex_nonempty.to_subtype
  have : Nonempty (closedSimplex κ) := closedSimplex_nonempty.to_subtype
  have hT' : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  set x0 := average T x
  have hx0 : x0 ∈ closedSimplex ι := average_mem hT hx
  have hxt : ∀ t, x t = x0 := fun t ↦ eq_of_mem_closedSimplex_of_card_eq_one hι (hx t) hx0
  have h1 : ⨆ y' : closedSimplex κ, payoff A x0 y' ≤ payoff A x0 (average T y) := by
    refine ciSup_le fun y' ↦ ?_
    rw [payoff_average_right]
    rw [le_div_iff₀ hT']
    calc payoff A x0 y' * T = ∑ t ∈ range T, payoff A x0 y' := by simp [mul_comm]
      _ ≤ ∑ t ∈ range T, payoff A x0 (y t) :=
          sum_le_sum fun t _ ↦ hxt t ▸ (hy t).2 y' y'.2
  have h2 : payoff A x0 (average T y) ≤ ⨅ x' : closedSimplex ι, payoff A x' (average T y) :=
    le_ciInf fun x' ↦ le_of_eq (by rw [eq_of_mem_closedSimplex_of_card_eq_one hι hx0 x'.2])
  linarith

/-- **Item 66 with the tuned step** `η = √(8 log m / T)`: the gap is at most
`√(log m / (2 T))`. With one row (`m = 1`, so `η = 0`) the gap is `0`. -/
theorem gap_le_sqrt_of_exponentialWeights [Nonempty ι] [Nonempty κ] {A : Matrix ι κ ℝ}
    (hA : ∀ i j, A i j ∈ Set.Icc (0 : ℝ) 1) {T : ℕ} (hT : 0 < T)
    {y : ℕ → κ → ℝ}
    (hy : ∀ t, IsBestResponse A (ewStrategy A (√(8 * Real.log (Fintype.card ι) / T)) y t)
      (y t)) :
    (⨆ y' : closedSimplex κ,
        payoff A (average T (ewStrategy A (√(8 * Real.log (Fintype.card ι) / T)) y)) y') -
      (⨅ x' : closedSimplex ι, payoff A x' (average T y)) ≤
        √(Real.log (Fintype.card ι) / (2 * T)) := by
  rcases Nat.lt_or_ge 1 (Fintype.card ι) with hm | hm
  · have hT' : (0 : ℝ) < T := Nat.cast_pos.mpr hT
    have ha : 0 < Real.log (Fintype.card ι) :=
      Real.log_pos (by exact_mod_cast hm)
    set a := Real.log (Fintype.card ι)
    set η := √(8 * a / T)
    have hη : 0 < η := Real.sqrt_pos.mpr (by positivity)
    have hη2 : η ^ 2 = 8 * a / T := Real.sq_sqrt (by positivity)
    have hη2' : η ^ 2 * T = 8 * a := by rw [hη2]; field_simp
    refine (gap_le_of_exponentialWeights hA hη hT hy).2.2.trans (le_of_eq ?_)
    have h1 : a / (η * T) = η / 8 := by
      field_simp
      linarith [hη2']
    rw [h1]
    have h2 : √(a / (2 * T)) = η / 4 := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
      field_simp
      linarith [hη2']
    rw [h2]; ring
  · have h1 : Fintype.card ι = 1 := le_antisymm hm Fintype.card_pos
    have h0 := gap_nonpos_of_card_eq_one h1 hT (ewStrategy_mem A _ y) hy
    exact h0.trans (Real.sqrt_nonneg _)

/-- A pure best response exists against any row strategy, so best-response sequences exist. -/
theorem exists_bestResponse [Nonempty κ] (A : Matrix ι κ ℝ) (x : ι → ℝ) :
    ∃ y, IsBestResponse A x y := by
  classical
  obtain ⟨j, -, hj⟩ := exists_max_image univ (fun j ↦ (x ᵥ* A) j) univ_nonempty
  refine ⟨Pi.single j 1, ⟨fun k ↦ ?_, by simp⟩, fun y' hy' ↦ ?_⟩
  · by_cases h : k = j <;> simp [h]
  · have hpay : ∀ z : κ → ℝ, payoff A x z = ∑ k, (x ᵥ* A) k * z k := fun z ↦ by
      rw [payoff, dotProduct_mulVec]; rfl
    rw [hpay, hpay]
    calc ∑ k, (x ᵥ* A) k * y' k ≤ ∑ k, (x ᵥ* A) j * y' k :=
          sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_right (hj k (mem_univ k)) (hy'.1 k)
      _ = ∑ k, (x ᵥ* A) k * (Pi.single j (1 : ℝ) : κ → ℝ) k := by
          rw [← mul_sum, hy'.2]; simp [Pi.single_apply]

/-- Best-response sequences against exponential weights exist (the weights at round `t` use
only the answers before `t`). -/
theorem exists_bestResponse_seq [Nonempty κ] (A : Matrix ι κ ℝ) (η : ℝ) :
    ∃ y : ℕ → κ → ℝ, ∀ t, IsBestResponse A (ewStrategy A η y t) (y t) := by
  choose br hbr using exists_bestResponse A
  let S : ℕ → ι → ℝ := fun n ↦ Nat.rec 0 (fun t St ↦ St + A *ᵥ br (softmax fun i ↦ -η * St i)) n
  refine ⟨fun t ↦ br (softmax fun i ↦ -η * S t i), fun t ↦ ?_⟩
  have hS : ∀ t, (fun i ↦ ∑ s ∈ range t, (A *ᵥ br (softmax fun i ↦ -η * S s i)) i) = S t := by
    intro t
    induction t with
    | zero => funext i; simp [S]
    | succ t ih =>
      funext i
      rw [sum_range_succ, congrFun ih i]
      rfl
  have : ewStrategy A η (fun t ↦ br (softmax fun i ↦ -η * S t i)) t =
      softmax fun i ↦ -η * S t i := by
    simp only [ewStrategy]
    rw [← hS t]
  rw [this]
  exact hbr _

/-- Item 66 without item 62: the upper and lower values differ by at most the gap. -/
theorem abs_value_sub_le_of_exponentialWeights [Nonempty ι] [Nonempty κ] {A : Matrix ι κ ℝ}
    (hA : ∀ i j, A i j ∈ Set.Icc (0 : ℝ) 1) {η : ℝ} (hη : 0 < η) {T : ℕ} (hT : 0 < T) :
    |(⨅ x : closedSimplex ι, ⨆ y : closedSimplex κ, payoff A x y) -
      ⨆ y : closedSimplex κ, ⨅ x : closedSimplex ι, payoff A x y| ≤
        Real.log (Fintype.card ι) / (η * T) + η / 8 := by
  obtain ⟨y, hy⟩ := exists_bestResponse_seq A η
  obtain ⟨hxbar, hybar, hgap⟩ := gap_le_of_exponentialWeights hA hη hT hy
  rw [abs_of_nonneg (sub_nonneg.mpr (iSup_iInf_le_iInf_iSup A))]
  have h1 : ⨅ x : closedSimplex ι, ⨆ y : closedSimplex κ, payoff A x y ≤
      ⨆ y' : closedSimplex κ, payoff A (average T (ewStrategy A η y)) y' :=
    ciInf_le (bddBelow_iSup_payoff A) ⟨_, hxbar⟩
  have h2 : ⨅ x' : closedSimplex ι, payoff A x' (average T y) ≤
      ⨆ y : closedSimplex κ, ⨅ x : closedSimplex ι, payoff A x y :=
    le_ciSup (f := fun y : closedSimplex κ ↦ ⨅ x : closedSimplex ι, payoff A x y)
      (bddAbove_iInf_payoff A) ⟨_, hybar⟩
  linarith

/-- Item 66 for the values with the tuned step: for every `T > 0` the upper and lower values
differ by at most `√(log m / (2 T))`, without item 62. -/
theorem abs_value_sub_le_sqrt_of_exponentialWeights [Nonempty ι] [Nonempty κ]
    {A : Matrix ι κ ℝ} (hA : ∀ i j, A i j ∈ Set.Icc (0 : ℝ) 1) {T : ℕ} (hT : 0 < T) :
    |(⨅ x : closedSimplex ι, ⨆ y : closedSimplex κ, payoff A x y) -
      ⨆ y : closedSimplex κ, ⨅ x : closedSimplex ι, payoff A x y| ≤
        √(Real.log (Fintype.card ι) / (2 * T)) := by
  obtain ⟨y, hy⟩ := exists_bestResponse_seq A (√(8 * Real.log (Fintype.card ι) / T))
  have hgap := gap_le_sqrt_of_exponentialWeights hA hT hy
  rw [abs_of_nonneg (sub_nonneg.mpr (iSup_iInf_le_iInf_iSup A))]
  have h1 := ciInf_le (bddBelow_iSup_payoff A)
    ⟨_, average_mem hT (ewStrategy_mem A (√(8 * Real.log (Fintype.card ι) / T)) y)⟩
  have h2 := le_ciSup (f := fun y : closedSimplex κ ↦ ⨅ x : closedSimplex ι, payoff A x y)
    (bddAbove_iInf_payoff A) ⟨_, average_mem hT fun t ↦ (hy t).1⟩
  simp only at h1 h2
  linarith

/-- A second proof of the equality in item 62, for payoffs in `[0, 1]`, by learning. -/
theorem minimax_eq_of_exponentialWeights [Nonempty ι] [Nonempty κ] {A : Matrix ι κ ℝ}
    (hA : ∀ i j, A i j ∈ Set.Icc (0 : ℝ) 1) :
    ⨅ x : closedSimplex ι, ⨆ y : closedSimplex κ, payoff A x y =
      ⨆ y : closedSimplex κ, ⨅ x : closedSimplex ι, payoff A x y := by
  refine le_antisymm (le_of_forall_pos_le_add fun δ hδ ↦ ?_) (iSup_iInf_le_iInf_iSup A)
  have hlog : 0 ≤ Real.log (Fintype.card ι) := Real.log_natCast_nonneg _
  obtain ⟨T, hT⟩ := exists_nat_gt (Real.log (Fintype.card ι) / (2 * δ ^ 2))
  have hT0 : 0 < T := by
    have : (0 : ℝ) < T := lt_of_le_of_lt (by positivity) hT
    exact_mod_cast this
  have hT' : (0 : ℝ) < T := Nat.cast_pos.mpr hT0
  have h := abs_value_sub_le_of_exponentialWeights hA (η := 4 * δ) (by positivity) hT0
  have hb : Real.log (Fintype.card ι) / (4 * δ * T) ≤ δ / 2 := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hT
    nlinarith
  linarith [le_abs_self ((⨅ x : closedSimplex ι, ⨆ y : closedSimplex κ, payoff A x y) -
      ⨆ y : closedSimplex κ, ⨅ x : closedSimplex ι, payoff A x y)]

/-! ### Item 63 -/

section Bayes

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Θ 𝓧 𝓨 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
  [Fintype Θ] [Fintype 𝓧] [Fintype 𝓨]

/-- The risk at `θ` of the randomized rule given by the matrix `K x y` (the chance of action `y`
after data `x`), in real numbers. -/
noncomputable def matrixRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (K : 𝓧 → 𝓨 → ℝ) (θ : Θ) : ℝ :=
  ∑ x, ∑ y, (P θ {x}).toReal * K x y * (ℓ θ y).toReal

/-- The average risk of `K` under the prior vector `π`. -/
noncomputable def matrixAvgRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (K : 𝓧 → 𝓨 → ℝ)
    (π : Θ → ℝ) : ℝ :=
  ∑ θ, π θ * matrixRisk ℓ P K θ

/-- Randomized rules as matrices: every row is a probability vector on the actions. -/
def ruleSet (𝓧 𝓨 : Type*) [Fintype 𝓨] : Set (𝓧 → 𝓨 → ℝ) := Set.univ.pi fun _ ↦ closedSimplex 𝓨

omit [MeasurableSpace 𝓨] in
/-- The average risk as one triple sum. -/
theorem matrixAvgRisk_eq (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (K : 𝓧 → 𝓨 → ℝ) (π : Θ → ℝ) :
    matrixAvgRisk ℓ P K π =
      ∑ θ, ∑ x, ∑ y, π θ * ((P θ {x}).toReal * K x y * (ℓ θ y).toReal) := by
  simp [matrixAvgRisk, matrixRisk, mul_sum]

omit [MeasurableSpace 𝓨] in
/-- Sion's theorem for the decision problem as a game: a rule matrix and a prior vector forming
a saddle point of the average risk. -/
theorem exists_saddle_matrixAvgRisk [Nonempty Θ] [Nonempty 𝓨] (ℓ : Θ → 𝓨 → ℝ≥0∞)
    (P : Kernel Θ 𝓧) :
    ∃ K ∈ ruleSet 𝓧 𝓨, ∃ π ∈ closedSimplex Θ,
      IsSaddlePointOn (ruleSet 𝓧 𝓨) (closedSimplex Θ) (matrixAvgRisk ℓ P) K π := by
  have hne : (ruleSet 𝓧 𝓨).Nonempty := by
    obtain ⟨y, hy⟩ := (closedSimplex_nonempty (ι := 𝓨))
    exact ⟨fun _ ↦ y, fun _ _ ↦ hy⟩
  have hconv : Convex ℝ (ruleSet 𝓧 𝓨) := convex_pi fun _ _ ↦ convex_closedSimplex
  have hcomp : IsCompact (ruleSet 𝓧 𝓨) := isCompact_univ_pi fun _ ↦ isCompact_closedSimplex
  have hcont : ∀ K π, (Continuous fun K' ↦ matrixAvgRisk ℓ P K' π) ∧
      (Continuous fun π' ↦ matrixAvgRisk ℓ P K π') := by
    intro K π
    simp only [matrixAvgRisk_eq]
    constructor <;> fun_prop
  refine Sion.exists_isSaddlePointOn hne hconv hcomp
    (fun π _ ↦ (hcont 0 π).1.lowerSemicontinuous.lowerSemicontinuousOn _)
    (fun π _ ↦ ?_) convex_closedSimplex closedSimplex_nonempty isCompact_closedSimplex
    (fun K _ ↦ (hcont K 0).2.upperSemicontinuous.upperSemicontinuousOn _)
    (fun K _ ↦ ?_)
  · refine ConvexOn.quasiconvexOn ⟨hconv, fun a _ b _ s t _ _ _ ↦ le_of_eq ?_⟩
    simp only [matrixAvgRisk_eq, smul_eq_mul, mul_sum]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun θ _ ↦ ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun y _ ↦ ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · refine ConcaveOn.quasiconcaveOn ⟨convex_closedSimplex, fun a _ b _ s t _ _ _ ↦ le_of_eq ?_⟩
    simp only [matrixAvgRisk_eq, smul_eq_mul, mul_sum]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun θ _ ↦ ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun y _ ↦ ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

variable [MeasurableSingletonClass Θ] [MeasurableSingletonClass 𝓧] [MeasurableSingletonClass 𝓨]

omit [Fintype Θ] [MeasurableSingletonClass Θ] in
/-- The risk of a Markov kernel, as Mathlib writes it, is that of its matrix. -/
theorem lintegral_comp_eq_ofReal_matrixRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (hℓ : ∀ θ y, ℓ θ y ≠ ∞)
    (P : Kernel Θ 𝓧) [IsFiniteKernel P] (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] (θ : Θ) :
    ∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ) = ENNReal.ofReal (matrixRisk ℓ P (fun x y ↦ (κ x {y}).toReal) θ) := by
  have hcomp : ∀ y, (κ ∘ₖ P) θ {y} = ∑ x, κ x {y} * P θ {x} := fun y ↦ by
    rw [Kernel.comp_apply' _ _ _ (measurableSet_singleton y), lintegral_fintype]
  rw [lintegral_fintype]
  simp only [hcomp]
  have hfin : ∀ y, ℓ θ y * ∑ x, κ x {y} * P θ {x} ≠ ∞ := fun y ↦
    ENNReal.mul_ne_top (hℓ θ y) (ENNReal.sum_ne_top.mpr fun x _ ↦
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
  rw [← ENNReal.ofReal_toReal (ENNReal.sum_ne_top.mpr fun y _ ↦ hfin y)]
  congr 1
  rw [ENNReal.toReal_sum fun y _ ↦ hfin y, matrixRisk, sum_comm]
  refine sum_congr rfl fun y _ ↦ ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_sum fun x _ ↦
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _), mul_sum]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [ENNReal.toReal_mul]; ring

omit [Fintype 𝓧] [MeasurableSingletonClass 𝓧] in
/-- The matrix of a Markov kernel is a rule matrix. -/
theorem kernel_mem_ruleSet (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] :
    (fun x y ↦ (κ x {y}).toReal) ∈ ruleSet 𝓧 𝓨 := by
  intro x _
  refine ⟨fun y ↦ ENNReal.toReal_nonneg, ?_⟩
  rw [← ENNReal.toReal_sum fun y _ ↦ measure_ne_top _ _]
  have : ∑ y, κ x {y} = 1 := by
    rw [← measure_biUnion_finset (fun a _ b _ h ↦ Set.disjoint_singleton.mpr h)
      fun y _ ↦ measurableSet_singleton y]
    simp [Set.iUnion_of_singleton]
  rw [this, ENNReal.toReal_one]

/-- The Markov kernel of a rule matrix. -/
noncomputable def ruleKernel (K : 𝓧 → 𝓨 → ℝ) : Kernel 𝓧 𝓨 :=
  Kernel.ofFunOfCountable fun x ↦ ∑ y, ENNReal.ofReal (K x y) • Measure.dirac y

/-- The kernel of a rule matrix gives action `y` after `x` the chance `K x y`. -/
theorem ruleKernel_singleton (K : 𝓧 → 𝓨 → ℝ) (x : 𝓧) (y : 𝓨) :
    ruleKernel K x {y} = ENNReal.ofReal (K x y) := by
  classical
  simp [ruleKernel, Kernel.ofFunOfCountable, Measure.dirac_apply' _ (measurableSet_singleton y),
    Set.indicator_apply]

omit [MeasurableSingletonClass 𝓨] in
/-- The kernel of a rule matrix is a Markov kernel. -/
theorem isMarkovKernel_ruleKernel {K : 𝓧 → 𝓨 → ℝ} (hK : K ∈ ruleSet 𝓧 𝓨) :
    IsMarkovKernel (ruleKernel K) := by
  refine ⟨fun x ↦ ⟨?_⟩⟩
  simp only [ruleKernel, Kernel.ofFunOfCountable, Kernel.coe_mk, Measure.coe_finsetSum,
    Finset.sum_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun y _ ↦ (hK x (Set.mem_univ x)).1 y,
    (hK x (Set.mem_univ x)).2, ENNReal.ofReal_one]

/-- The prior measure of a probability vector. -/
noncomputable def priorMeasure (π : Θ → ℝ) : Measure Θ :=
  ∑ θ, ENNReal.ofReal (π θ) • Measure.dirac θ

/-- The prior measure gives `θ` the mass `π θ`. -/
theorem priorMeasure_singleton (π : Θ → ℝ) (θ : Θ) :
    priorMeasure π {θ} = ENNReal.ofReal (π θ) := by
  classical
  simp [priorMeasure, Measure.dirac_apply' _ (measurableSet_singleton θ), Set.indicator_apply]

omit [MeasurableSingletonClass Θ] in
/-- The prior measure of a probability vector is a probability measure. -/
theorem isProbabilityMeasure_priorMeasure {π : Θ → ℝ} (hπ : π ∈ closedSimplex Θ) :
    IsProbabilityMeasure (priorMeasure π) := by
  refine ⟨?_⟩
  simp only [priorMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun θ _ ↦ hπ.1 θ, hπ.2, ENNReal.ofReal_one]

omit [MeasurableSpace 𝓨] [Fintype Θ] [MeasurableSingletonClass Θ] [MeasurableSingletonClass 𝓧]
  [MeasurableSingletonClass 𝓨] in
/-- Risks of rule matrices are nonnegative. -/
theorem matrixRisk_nonneg (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) {K : 𝓧 → 𝓨 → ℝ}
    (hK : K ∈ ruleSet 𝓧 𝓨) (θ : Θ) : 0 ≤ matrixRisk ℓ P K θ :=
  sum_nonneg fun x _ ↦ sum_nonneg fun y _ ↦
    mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ((hK x (Set.mem_univ x)).1 y))
      ENNReal.toReal_nonneg

end Bayes

section BayesFinite

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Bayes equals minimax for a finite decision problem (item 63).** Finitely many parameters
`Θ`, data values `𝓧` and actions `𝓨`, all singletons measurable, at least one action, a finite
kernel `P` and a loss `ℓ` with no infinite value: the largest Bayes risk over prior probability
measures equals the minimax risk, both in Mathlib's definitions (rules are Markov kernels from
`𝓧` to `𝓨`). Mathlib proves `≤` (`iSup_bayesRisk_le_minimaxRisk`). With no parameter both sides
are `0`. -/
theorem iSup_bayesRisk_eq_minimaxRisk_of_finite {Θ 𝓧 𝓨 : Type*} [MeasurableSpace Θ]
    [MeasurableSpace 𝓧] [MeasurableSpace 𝓨] [Finite Θ] [Finite 𝓧] [Finite 𝓨]
    [MeasurableSingletonClass Θ] [MeasurableSingletonClass 𝓧] [MeasurableSingletonClass 𝓨]
    [Nonempty 𝓨] (ℓ : Θ → 𝓨 → ℝ≥0∞) (hℓ : ∀ θ y, ℓ θ y ≠ ∞) (P : Kernel Θ 𝓧)
    [IsFiniteKernel P] :
    ⨆ (π : Measure Θ) (_ : IsProbabilityMeasure π), bayesRisk ℓ P π = minimaxRisk ℓ P := by
  classical
  cases nonempty_fintype Θ; cases nonempty_fintype 𝓧; cases nonempty_fintype 𝓨
  refine le_antisymm (iSup_bayesRisk_le_minimaxRisk ℓ P) ?_
  rcases isEmpty_or_nonempty Θ with hΘ | hΘ
  · obtain ⟨y⟩ := ‹Nonempty 𝓨›
    have hκ : IsMarkovKernel (Kernel.const 𝓧 (Measure.dirac y)) := inferInstance
    calc minimaxRisk ℓ P
        ≤ ⨆ θ, ∫⁻ y', ℓ θ y' ∂((Kernel.const 𝓧 (Measure.dirac y) ∘ₖ P) θ) :=
          iInf₂_le (Kernel.const 𝓧 (Measure.dirac y)) hκ
      _ = 0 := by simp
      _ ≤ _ := by simp
  · obtain ⟨K, hK, π, hπ, hsad⟩ := exists_saddle_matrixAvgRisk ℓ P
    set v := matrixAvgRisk ℓ P K π
    have := isMarkovKernel_ruleKernel hK
    have hKK : (fun x y ↦ (ruleKernel K x {y}).toReal) = K := by
      funext x y
      rw [ruleKernel_singleton, ENNReal.toReal_ofReal ((hK x (Set.mem_univ x)).1 y)]
    have hup : minimaxRisk ℓ P ≤ ENNReal.ofReal v := by
      refine (iInf₂_le (ruleKernel K) this).trans (iSup_le fun θ ↦ ?_)
      rw [lintegral_comp_eq_ofReal_matrixRisk ℓ hℓ P, hKK]
      refine ENNReal.ofReal_le_ofReal ?_
      have hδ : (Pi.single θ 1 : Θ → ℝ) ∈ closedSimplex Θ := by
        refine ⟨fun θ' ↦ ?_, by simp⟩
        by_cases h : θ' = θ <;> simp [h]
      have h1 := hsad K hK _ hδ
      have h2 : matrixRisk ℓ P K θ ≤ matrixAvgRisk ℓ P K π := by
        simpa [matrixAvgRisk, Pi.single_apply] using h1
      exact h2
    have hdown : ENNReal.ofReal v ≤ bayesRisk ℓ P (priorMeasure π) := by
      refine le_iInf₂ fun κ hκ ↦ ?_
      rw [avgRisk_fintype]
      simp only [lintegral_comp_eq_ofReal_matrixRisk ℓ hℓ P, priorMeasure_singleton,
        ← ENNReal.ofReal_mul (matrixRisk_nonneg ℓ P (kernel_mem_ruleSet κ) _)]
      rw [← ENNReal.ofReal_sum_of_nonneg fun θ _ ↦
        mul_nonneg (matrixRisk_nonneg ℓ P (kernel_mem_ruleSet κ) _) (hπ.1 θ)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := hsad _ (kernel_mem_ruleSet κ) π hπ
      have h2 : matrixAvgRisk ℓ P K π ≤
          ∑ θ, matrixRisk ℓ P (fun x y ↦ (κ x {y}).toReal) θ * π θ := by
        simpa [matrixAvgRisk, mul_comm] using h1
      exact h2
    have := isProbabilityMeasure_priorMeasure hπ
    exact hup.trans (hdown.trans (le_iSup₂ (f := fun π (_ : IsProbabilityMeasure π) ↦
      bayesRisk ℓ P π) (priorMeasure π) this))

end BayesFinite

end ClassicalLean.Analysis
