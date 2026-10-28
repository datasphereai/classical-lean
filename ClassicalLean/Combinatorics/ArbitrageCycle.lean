/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import ClassicalLean.Analysis.LinearProgram

/-!
# No gain around any cycle, three ways, and Bellman–Ford

There are finitely many assets `ι`. Converting one unit of asset `i` gives `r i j > 0` units of
asset `j`, fees included (item 65). A **cycle** is a list `c = [c₀, …, cₖ]`, read as the round
trip `c₀ → c₁ → ⋯ → cₖ → c₀` (`cycleProd`, `cycleSum`); vertices may repeat, and `[i]` is the
trip `i → i` at the rate `r i i` (usually `1`).

* (a) `NoGainCycle r`: every cycle's product of rates is at most `1`; no round trip gains.
* (b) `HasPrices r`: there are positive prices `p` with `r i j · p j ≤ p i` for every pair; no
  single conversion gains value at those prices.
* (c) `NoNegativeCycle (negLog r)`: with weights `−log r i j` (`negLog`), no cycle has negative
  total weight.

`noGainCycle_iff_noNegativeCycle`: (a) ⇔ (c), since the weight of a cycle is `−log` of its
product. `forall_cycle_prod_le_one_iff_exists_prices`: (a) ⇔ (b); (b) ⇒ (a) is telescoping
(`cycleSum_nonneg_of_potential`), (a) ⇒ (b) takes the prices from Bellman–Ford.

**Bellman–Ford** (`bellmanFord w k j`): start every asset at `0` (a virtual source joined to
each by weight `0`) and relax `k` times, `d (k + 1) j = min (d k j) (minᵢ (d k i + w i j))`; then
`d k j` is the least weight of a walk with at most `k` edges ending at `j` (this is the
round-by-round form, each round using only the previous round's values; the in-place form can
settle sooner)
(`bellmanFord_le_walkSum`, `exists_walkSum_eq_bellmanFord`). With `n` assets:

* `bellmanFord_add_eq_of_stable`: once a round changes nothing, no later round does.
* `bellmanFord_stable_of_short`: if no cycle of length at most `n` has negative weight, round
  `n` changes nothing after round `n − 1` (a walk with `n` edges repeats a vertex, and removing
  the cycle between the repeats does not raise its weight).
* `bellmanFord_stable_iff`: round `n` changes nothing after round `n − 1` exactly when (a) holds;
  `exists_bellmanFord_lt_iff`: a further improving round exists exactly when some cycle gains.
* `prices_of_bellmanFord`: then `p = exp (d (n − 1))` are prices as in (b).
* `noGainCycle_of_short`: so checking cycles of length at most `n` (`NoShortGainCycle`)
  suffices for (a).

Use: a consistency check on prices from several sources. Quotes that admit no prices are stale,
wrong, or a real gap, and Bellman–Ford finds out in `n` rounds.

`hasPrices_iff_of_lp` (order LEAN-37, item 145): (b) ⇔ (a) again, by linear-program duality. The
potentials `log p` are the variables of a linear program with constraints
`z j − z i ≤ −log r i j`; by Farkas' lemma (`farkas`, module `ClassicalLean.Analysis.LinearProgram`)
it is feasible exactly when every nonnegative certificate on the pairs with nonnegative net inflow
at every vertex has nonnegative weight, and such a certificate splits into cycles.

## Hypotheses

Checked in order LEAN-25 (`~/lean/lean25-checks/checks.py`, A1 to A4):

* `r i j > 0`, for (c) and Bellman–Ford: Lean's `log 0 = 0` reads a rate `0` as a rate `1`:
  with `r 0 1 = 0`, `r 1 0 = 2`, the cycle `[0, 1]` has product `0` (no gain) but weight
  `−log 2 < 0`, so (a) holds and (c) fails. For (a) ⇔ (b) alone `r i j ≥ 0` would do (by hand,
  review r65), not proved here. With negative rates `r 0 1 = r 1 0 = −2`, `p = (1, 1)` are
  prices but the cycle `[0, 1]` has product `4`: (b) holds and (a) fails.
* `n − 1` rounds: with weights `w 0 1 = w 1 2 = −1`, `0` on the diagonal and `5` elsewhere (no
  negative cycle), round 1 gives `(0, −1, −1)` and round 2 gives `(0, −1, −2)`: `n − 2` rounds do
  not always settle.
* Finitely many assets: (a) ⇒ (b) holds for any set of assets (by hand: fix an asset `o` and
  let `p i` be the supremum of the products along walks from `i` to `o`, at most `1 / r o i`
  because a walk back from `o` closes a cycle, and at least `r i o > 0`); finiteness is used
  here for Bellman–Ford.
* A nonempty set of assets for Bellman–Ford, whose minimum is over the assets; with no asset
  every statement about cycles is about the empty list only and holds.

The three exact cases above (A1 to A3 of order LEAN-25's table) are Lean `example`s at the end of
this file (order LEAN-28, item 86), each stated with this file's own definitions. A1 and A2 give
only the rates between the two assets; both take the rate `1` from an asset to itself, which keeps
the side that holds true (a single asset `[i]` is a cycle too, with product `r i i`): in A1 every
cycle has product at most `1` (the prices `(1, 2)` telescope along any cycle, since every rate is at
least `0`), and in A2 `p = (1, 1)` are prices (for the pair `(i, i)` prices ask `r i i · p i ≤ p i`,
which the rate `1` meets). A3 takes the weights as given (`0` on the diagonal) and Bellman–Ford's
round function `bellmanFord w k j` directly: with three assets and no negative cycle, round `2`
still lowers the value at asset `2` after round `1` (from `−1` to `−2`), so stopping at round
`n − 2` would be wrong; round `3` changes nothing (`bellmanFord_stable_iff` compares rounds `n` and
`n − 1`; with the rates `exp (−w)`, `negLog` gives back `w`, so A3 is a case of it with positive
rates).

## What is cited

Bellman 1958, "On a routing problem"; Ford 1956, "Network Flow Theory". Not read here: author,
title and year only.

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-25, `grep -rliE`): "Bellman|negative
cycle|arbitrage|shortest path" 1 file, a docstring in Combinatorics/Quiver/Arborescence.lean.
Item 47 of the plan (linear-program duality, `Analysis/LinearProgram`) is the general form of
(a) ⇔ (b); this file proves the finite case directly.
-/

open Finset

namespace ClassicalLean.Combinatorics

variable {ι : Type*}

/-- The weight of the walk `a₀ → a₁ → ⋯ → aₘ`: `∑ w aₜ aₜ₊₁`. -/
def walkSum (w : ι → ι → ℝ) : List ι → ℝ
  | a :: b :: rest => w a b + walkSum w (b :: rest)
  | _ => 0

/-- The product of the rates along the walk. -/
def walkProd (r : ι → ι → ℝ) : List ι → ℝ
  | a :: b :: rest => r a b * walkProd r (b :: rest)
  | _ => 1

/-- The weight around the cycle `c₀ → c₁ → ⋯ → cₖ → c₀`. -/
def cycleSum (w : ι → ι → ℝ) (c : List ι) : ℝ := walkSum w (c ++ c.take 1)

/-- The product of the rates around the cycle `c₀ → c₁ → ⋯ → cₖ → c₀`. -/
def cycleProd (r : ι → ι → ℝ) (c : List ι) : ℝ := walkProd r (c ++ c.take 1)

/-- (a) No round trip gains: every cycle's product of rates is at most `1`. -/
def NoGainCycle (r : ι → ι → ℝ) : Prop := ∀ c : List ι, c ≠ [] → cycleProd r c ≤ 1

/-- No round trip of at most `n` steps gains: every cycle of length at most `n` has product at
most `1`. -/
def NoShortGainCycle (r : ι → ι → ℝ) (n : ℕ) : Prop :=
  ∀ c : List ι, c ≠ [] → c.length ≤ n → cycleProd r c ≤ 1

/-- (b) Positive prices at which no single conversion gains: `r i j · p j ≤ p i`. -/
def HasPrices (r : ι → ι → ℝ) : Prop := ∃ p : ι → ℝ, (∀ i, 0 < p i) ∧ ∀ i j, r i j * p j ≤ p i

/-- (c) No cycle has negative total weight. -/
def NoNegativeCycle (w : ι → ι → ℝ) : Prop := ∀ c : List ι, c ≠ [] → 0 ≤ cycleSum w c

/-- The weights `−log r i j`. -/
noncomputable def negLog (r : ι → ι → ℝ) (i j : ι) : ℝ := -Real.log (r i j)

/-! ### Walks -/

/-- Splitting a walk at a vertex. -/
theorem walkSum_append (w : ι → ι → ℝ) (A : List ι) (x : ι) (B : List ι) :
    walkSum w (A ++ x :: B) = walkSum w (A ++ [x]) + walkSum w (x :: B) := by
  induction A with
  | nil => simp [walkSum]
  | cons a A ih =>
    cases A with
    | nil => simp [walkSum]
    | cons a' A' =>
      simp only [List.cons_append, walkSum] at ih ⊢
      rw [ih]; ring

/-- Along a walk, the weight is at least the change in a potential. -/
theorem walkSum_ge_of_potential {w : ι → ι → ℝ} {φ : ι → ℝ} (hφ : ∀ i j, φ j ≤ φ i + w i j) :
    ∀ (a : ι) (L : List ι), φ ((a :: L).getLast (List.cons_ne_nil a L)) - φ a ≤ walkSum w (a :: L)
  | a, [] => by simp [walkSum]
  | a, b :: L => by
    have ih := walkSum_ge_of_potential hφ b L
    simp only [walkSum, List.getLast_cons_cons] at ih ⊢
    have := hφ a b
    linarith

/-- A potential (`φ j ≤ φ i + w i j`) rules out negative cycles: the weight telescopes. -/
theorem cycleSum_nonneg_of_potential {w : ι → ι → ℝ} {φ : ι → ℝ}
    (hφ : ∀ i j, φ j ≤ φ i + w i j) : NoNegativeCycle w := by
  rintro (_ | ⟨a, L⟩) hc
  · exact absurd rfl hc
  have h := walkSum_ge_of_potential hφ a (L ++ [a])
  simp only [List.take_succ_cons, List.take_zero, cycleSum, List.cons_append] at h ⊢
  have hl : (a :: (L ++ [a])).getLast (List.cons_ne_nil _ _) = a := by
    rw [List.getLast_cons (by simp), List.getLast_append_singleton]
  rw [hl, sub_self] at h
  exact h

/-- Products of positive rates are positive. -/
theorem walkProd_pos {r : ι → ι → ℝ} (hr : ∀ i j, 0 < r i j) : ∀ L : List ι, 0 < walkProd r L
  | a :: b :: rest => by
    simp only [walkProd]; exact mul_pos (hr a b) (walkProd_pos hr (b :: rest))
  | [] => by simp [walkProd]
  | [_] => by simp [walkProd]

/-- The weight `−log r` of a walk is `−log` of its product of rates. -/
theorem walkSum_negLog {r : ι → ι → ℝ} (hr : ∀ i j, 0 < r i j) :
    ∀ L : List ι, walkSum (negLog r) L = -Real.log (walkProd r L)
  | a :: b :: rest => by
    simp only [walkSum, walkProd, negLog]
    rw [walkSum_negLog hr (b :: rest), Real.log_mul (hr a b).ne' (walkProd_pos hr _).ne']
    ring
  | [] => by simp [walkSum, walkProd]
  | [_] => by simp [walkSum, walkProd]

/-- A cycle gains nothing exactly when its weight for `−log r` is nonnegative. -/
theorem cycleProd_le_one_iff {r : ι → ι → ℝ} (hr : ∀ i j, 0 < r i j) (c : List ι) :
    cycleProd r c ≤ 1 ↔ 0 ≤ cycleSum (negLog r) c := by
  rw [cycleSum, walkSum_negLog hr, cycleProd, neg_nonneg,
    Real.log_nonpos_iff (walkProd_pos hr _).le]

/-- **(a) ⇔ (c) (item 65).** No cycle gains if and only if no cycle has negative weight for
`−log r`. -/
theorem noGainCycle_iff_noNegativeCycle {r : ι → ι → ℝ} (hr : ∀ i j, 0 < r i j) :
    NoGainCycle r ↔ NoNegativeCycle (negLog r) :=
  forall₂_congr fun c _ ↦ cycleProd_le_one_iff hr c

/-- A potential for `−log r` gives prices `exp φ`. -/
theorem mul_exp_le_of_potential {r : ι → ι → ℝ} (hr : ∀ i j, 0 < r i j) {φ : ι → ℝ}
    {i j : ι} (h : φ j ≤ φ i + negLog r i j) : r i j * Real.exp (φ j) ≤ Real.exp (φ i) := by
  simp only [negLog] at h
  calc r i j * Real.exp (φ j) = Real.exp (Real.log (r i j) + φ j) := by
        rw [Real.exp_add, Real.exp_log (hr i j)]
    _ ≤ Real.exp (φ i) := Real.exp_le_exp.mpr (by linarith)

/-- Prices are a potential for `−log r`, through `p = exp φ`. -/
theorem hasPrices_iff_potential {r : ι → ι → ℝ} (hr : ∀ i j, 0 < r i j) :
    HasPrices r ↔ ∃ φ : ι → ℝ, ∀ i j, φ j ≤ φ i + negLog r i j := by
  constructor
  · rintro ⟨p, hp, h⟩
    refine ⟨fun i ↦ Real.log (p i), fun i j ↦ ?_⟩
    have := Real.log_le_log (mul_pos (hr i j) (hp j)) (h i j)
    rw [Real.log_mul (hr i j).ne' (hp j).ne'] at this
    simp only [negLog]; linarith
  · rintro ⟨φ, h⟩
    exact ⟨fun i ↦ Real.exp (φ i), fun i ↦ Real.exp_pos _,
      fun i j ↦ mul_exp_le_of_potential hr (h i j)⟩

/-! ### Bellman–Ford -/

section BellmanFord

variable [Fintype ι] [Nonempty ι]

/-- Bellman–Ford from a virtual source joined to every vertex by weight `0`: after `k` rounds,
`bellmanFord w k j` is the least weight of a walk with at most `k` edges ending at `j`. -/
noncomputable def bellmanFord (w : ι → ι → ℝ) : ℕ → ι → ℝ
  | 0 => fun _ ↦ 0
  | k + 1 => fun j ↦
      min (bellmanFord w k j) (univ.inf' univ_nonempty fun i ↦ bellmanFord w k i + w i j)

/-- One more round never raises a value. -/
theorem bellmanFord_succ_le (w : ι → ι → ℝ) (k : ℕ) (j : ι) :
    bellmanFord w (k + 1) j ≤ bellmanFord w k j := min_le_left _ _

/-- Once a round changes nothing, no later round does: the values have settled. -/
theorem bellmanFord_add_eq_of_stable {w : ι → ι → ℝ} {k : ℕ}
    (h : bellmanFord w (k + 1) = bellmanFord w k) : ∀ m, bellmanFord w (k + m) = bellmanFord w k
  | 0 => rfl
  | m + 1 => by
    have ih := bellmanFord_add_eq_of_stable h m
    rw [← add_assoc]
    funext j
    change min _ _ = _
    rw [ih]
    exact congrFun h j

omit [Fintype ι] [Nonempty ι] in
/-- Extending a walk by one edge. -/
theorem walkSum_concat (w : ι → ι → ℝ) (A : List ι) (i j : ι) :
    walkSum w (A ++ [i] ++ [j]) = walkSum w (A ++ [i]) + w i j := by
  rw [List.append_assoc, List.singleton_append, walkSum_append]
  simp [walkSum]

/-- After `k` rounds, the value at `j` is at most the weight of any walk with at most `k`
edges ending at `j`. -/
theorem bellmanFord_le_walkSum (w : ι → ι → ℝ) :
    ∀ (k : ℕ) (j : ι) (A : List ι), A.length ≤ k → bellmanFord w k j ≤ walkSum w (A ++ [j])
  | 0, j, A, hA => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hA)]
    simp [bellmanFord, walkSum]
  | k + 1, j, A, hA => by
    rcases List.eq_nil_or_concat' A with rfl | ⟨A', i, rfl⟩
    · exact (bellmanFord_succ_le w k j).trans (bellmanFord_le_walkSum w k j [] (Nat.zero_le _))
    · rw [walkSum_concat]
      simp only [List.length_append, List.length_singleton] at hA
      calc bellmanFord w (k + 1) j
          ≤ univ.inf' univ_nonempty (fun i ↦ bellmanFord w k i + w i j) := min_le_right _ _
        _ ≤ bellmanFord w k i + w i j := inf'_le _ (mem_univ i)
        _ ≤ walkSum w (A' ++ [i]) + w i j := by
            gcongr; exact bellmanFord_le_walkSum w k i A' (by omega)

/-- After `k` rounds, the value at `j` is the weight of some walk with at most `k` edges ending
at `j`. -/
theorem exists_walkSum_eq_bellmanFord (w : ι → ι → ℝ) :
    ∀ (k : ℕ) (j : ι), ∃ A : List ι, A.length ≤ k ∧ bellmanFord w k j = walkSum w (A ++ [j])
  | 0, j => ⟨[], le_rfl, by simp [bellmanFord, walkSum]⟩
  | k + 1, j => by
    rcases min_choice (bellmanFord w k j)
        (univ.inf' univ_nonempty fun i ↦ bellmanFord w k i + w i j) with h | h
    · obtain ⟨A, hA, e⟩ := exists_walkSum_eq_bellmanFord w k j
      exact ⟨A, hA.trans (Nat.le_succ k), by change min _ _ = _; rw [h, e]⟩
    · obtain ⟨i, -, hi⟩ := exists_mem_eq_inf' univ_nonempty fun i ↦ bellmanFord w k i + w i j
      obtain ⟨A, hA, e⟩ := exists_walkSum_eq_bellmanFord w k i
      refine ⟨A ++ [i], by simp; omega, ?_⟩
      rw [walkSum_concat, ← e, ← hi, ← h]
      rfl

end BellmanFord

/-- A list with a repeat splits around two copies of one element. -/
theorem exists_dup_of_not_nodup : ∀ {L : List ι}, ¬ L.Nodup →
    ∃ s x u v, L = s ++ x :: (u ++ x :: v)
  | [], h => absurd List.nodup_nil h
  | a :: L, h => by
    rw [List.nodup_cons, not_and_or, not_not] at h
    rcases h with h | h
    · obtain ⟨u, v, rfl⟩ := List.append_of_mem h
      exact ⟨[], a, u, v, rfl⟩
    · obtain ⟨s, x, u, v, rfl⟩ := exists_dup_of_not_nodup h
      exact ⟨a :: s, x, u, v, rfl⟩

/-- Removing a cycle from a walk: the weight drops by the cycle's weight. -/
theorem walkSum_remove_cycle (w : ι → ι → ℝ) (s : List ι) (x : ι) (u v : List ι) :
    walkSum w (s ++ x :: (u ++ x :: v)) = walkSum w (s ++ x :: v) + cycleSum w (x :: u) := by
  rw [walkSum_append w s x (u ++ x :: v), walkSum_append w s x v, cycleSum]
  have : x :: (u ++ x :: v) = (x :: u) ++ x :: v := rfl
  rw [this, walkSum_append w (x :: u) x v]
  simp only [List.take_succ_cons, List.take_zero]
  ring

section Stable

variable [Fintype ι] [Nonempty ι]

/-- **Bellman–Ford settles after `n − 1` rounds** (`n` the number of vertices) when no cycle of
length at most `n` has negative weight. -/
theorem bellmanFord_stable_of_short {w : ι → ι → ℝ}
    (h : ∀ c : List ι, c ≠ [] → c.length ≤ Fintype.card ι → 0 ≤ cycleSum w c) :
    bellmanFord w (Fintype.card ι) = bellmanFord w (Fintype.card ι - 1) := by
  have hn : Fintype.card ι = Fintype.card ι - 1 + 1 := (Nat.sub_add_cancel Fintype.card_pos).symm
  funext j
  refine le_antisymm (by rw [hn]; exact bellmanFord_succ_le w _ j) ?_
  obtain ⟨A, hA, e⟩ := exists_walkSum_eq_bellmanFord w (Fintype.card ι) j
  rw [e]
  by_cases hlen : A.length ≤ Fintype.card ι - 1
  · exact bellmanFord_le_walkSum w _ j A hlen
  have hL : ¬ (A ++ [j]).Nodup := fun hnd ↦ by
    have := hnd.length_le_card
    simp only [List.length_append, List.length_singleton] at this
    omega
  obtain ⟨s, x, u, v, hsv⟩ := exists_dup_of_not_nodup hL
  have hlen' : (A ++ [j]).length = Fintype.card ι + 1 := by simp; omega
  rw [hsv] at hlen'
  simp only [List.length_append, List.length_cons] at hlen'
  rw [hsv, walkSum_remove_cycle]
  have hc := h (x :: u) (List.cons_ne_nil _ _) (by simp; omega)
  -- the shorter walk still ends at `j`
  have hne : s ++ x :: v ≠ [] := by simp
  have hlast : (s ++ x :: v).getLast hne = j := by
    have h1 : (s ++ x :: (u ++ x :: v)).getLast? = some j := by rw [← hsv]; simp
    have e : (x :: (u ++ x :: v)).getLast? = (x :: v).getLast? := by
      rw [show x :: (u ++ x :: v) = (x :: u) ++ (x :: v) from rfl, List.getLast?_append]
      rw [List.getLast?_eq_some_getLast (List.cons_ne_nil x v)]
      rfl
    have h2 : (s ++ x :: v).getLast? = some j := by
      rw [← h1, List.getLast?_append, List.getLast?_append, e]
    have h3 := List.getLast?_eq_some_getLast hne
    rw [h2] at h3
    exact (Option.some.inj h3).symm
  have hsplit := List.dropLast_append_getLast hne
  rw [hlast] at hsplit
  have hdl : ((s ++ x :: v).dropLast).length ≤ Fintype.card ι - 1 := by
    rw [List.length_dropLast]; simp; omega
  calc bellmanFord w (Fintype.card ι - 1) j
      ≤ walkSum w ((s ++ x :: v).dropLast ++ [j]) := bellmanFord_le_walkSum w _ j _ hdl
    _ = walkSum w (s ++ x :: v) := by rw [hsplit]
    _ ≤ walkSum w (s ++ x :: v) + cycleSum w (x :: u) := le_add_of_nonneg_right hc

/-- When Bellman–Ford has settled, its values are a potential: `d j ≤ d i + w i j`. -/
theorem potential_of_bellmanFord_stable {w : ι → ι → ℝ}
    (h : bellmanFord w (Fintype.card ι) = bellmanFord w (Fintype.card ι - 1)) (i j : ι) :
    bellmanFord w (Fintype.card ι - 1) j ≤ bellmanFord w (Fintype.card ι - 1) i + w i j := by
  have hn : Fintype.card ι = Fintype.card ι - 1 + 1 := (Nat.sub_add_cancel Fintype.card_pos).symm
  have hj : bellmanFord w (Fintype.card ι - 1 + 1) j = bellmanFord w (Fintype.card ι - 1) j := by
    rw [← hn]; exact congrFun h j
  change min _ _ = _ at hj
  exact (min_eq_left_iff.mp hj).trans (inf'_le _ (mem_univ i))

end Stable

/-! ### The three conditions and Bellman–Ford -/

section Main

variable [Fintype ι]

/-- **Bellman–Ford settles exactly when no cycle gains (item 65).** With `n` assets and the
weights `−log r`, round `n` of Bellman–Ford changes nothing after round `n − 1` if and only if
every cycle's product of rates is at most `1`. -/
theorem bellmanFord_stable_iff [Nonempty ι] {r : ι → ι → ℝ} (hr : ∀ i j, 0 < r i j) :
    bellmanFord (negLog r) (Fintype.card ι) = bellmanFord (negLog r) (Fintype.card ι - 1) ↔
      NoGainCycle r := by
  constructor
  · intro h
    exact (noGainCycle_iff_noNegativeCycle hr).mpr
      (cycleSum_nonneg_of_potential (potential_of_bellmanFord_stable h))
  · intro h
    exact bellmanFord_stable_of_short fun c hc _ ↦ (cycleProd_le_one_iff hr c).mp (h c hc)

/-- **A further improving round exists exactly when some cycle gains (item 65).** -/
theorem exists_bellmanFord_lt_iff [Nonempty ι] {r : ι → ι → ℝ} (hr : ∀ i j, 0 < r i j) :
    (∃ j, bellmanFord (negLog r) (Fintype.card ι) j <
        bellmanFord (negLog r) (Fintype.card ι - 1) j) ↔
      ∃ c : List ι, c ≠ [] ∧ 1 < cycleProd r c := by
  have hle : ∀ j, bellmanFord (negLog r) (Fintype.card ι) j ≤
      bellmanFord (negLog r) (Fintype.card ι - 1) j := fun j ↦ by
    have hn : Fintype.card ι = Fintype.card ι - 1 + 1 :=
      (Nat.sub_add_cancel Fintype.card_pos).symm
    rw [hn]; exact bellmanFord_succ_le _ _ j
  have h1 : (∃ j, bellmanFord (negLog r) (Fintype.card ι) j <
      bellmanFord (negLog r) (Fintype.card ι - 1) j) ↔
      ¬ bellmanFord (negLog r) (Fintype.card ι) = bellmanFord (negLog r) (Fintype.card ι - 1) := by
    constructor
    · rintro ⟨j, hj⟩ h; rw [h] at hj; exact lt_irrefl _ hj
    · intro h
      by_contra hn
      push Not at hn
      exact h (funext fun j ↦ le_antisymm (hle j) (hn j))
  rw [h1, bellmanFord_stable_iff hr, NoGainCycle]
  push Not
  rfl

/-- **Checking cycles of length at most `n` suffices (item 65).** -/
theorem noGainCycle_of_short {r : ι → ι → ℝ} (hr : ∀ i j, 0 < r i j)
    (h : NoShortGainCycle r (Fintype.card ι)) : NoGainCycle r := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rintro (_ | ⟨a, _⟩) hc
    · exact absurd rfl hc
    · exact hι.elim a
  · exact (bellmanFord_stable_iff hr).mp
      (bellmanFord_stable_of_short fun c hc hl ↦ (cycleProd_le_one_iff hr c).mp (h c hc hl))

/-- **Prices from Bellman–Ford (item 65).** When no cycle gains, `p = exp (d)`, with `d` the
values after `n − 1` rounds, are prices: `r i j · p j ≤ p i`. -/
theorem prices_of_bellmanFord [Nonempty ι] {r : ι → ι → ℝ} (hr : ∀ i j, 0 < r i j)
    (h : NoGainCycle r) (i j : ι) :
    r i j * Real.exp (bellmanFord (negLog r) (Fintype.card ι - 1) j) ≤
      Real.exp (bellmanFord (negLog r) (Fintype.card ι - 1) i) :=
  mul_exp_le_of_potential hr
    (potential_of_bellmanFord_stable ((bellmanFord_stable_iff hr).mpr h) i j)

end Main

/-- **No gain around any cycle ⇔ consistent prices (item 65, (a) ⇔ (b)).** For finitely many
assets and rates `r i j > 0`: every cycle's product of rates is at most `1` if and only if
there are positive prices `p` with `r i j · p j ≤ p i` for every pair. -/
theorem forall_cycle_prod_le_one_iff_exists_prices [Finite ι] {r : ι → ι → ℝ}
    (hr : ∀ i j, 0 < r i j) : NoGainCycle r ↔ HasPrices r := by
  constructor
  · intro h
    cases nonempty_fintype ι
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨fun _ ↦ 1, fun _ ↦ one_pos, fun i ↦ hι.elim i⟩
    · exact ⟨_, fun i ↦ Real.exp_pos _, prices_of_bellmanFord hr h⟩
  · intro h
    obtain ⟨φ, hφ⟩ := (hasPrices_iff_potential hr).mp h
    exact (noGainCycle_iff_noNegativeCycle hr).mpr (cycleSum_nonneg_of_potential hφ)

/-! ### Item 65's exact counterexamples (order LEAN-28, item 86) -/

/-- **A1: a rate `0` breaks (a) ⇔ (c).** Rates `r 0 1 = 0`, `r 1 0 = 2` and `1` on the diagonal: no
cycle gains (prices `(1, 2)`, telescoping), but with Lean's `log 0 = 0` the cycle `[0, 1]` has
weight `−log 0 − log 2 = −log 2 < 0`. -/
example : NoGainCycle (![![1, 0], ![2, 1]] : Fin 2 → Fin 2 → ℝ) ∧
    ¬ NoNegativeCycle (negLog (![![1, 0], ![2, 1]] : Fin 2 → Fin 2 → ℝ)) := by
  set r : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![2, 1]] with hr
  set p : Fin 2 → ℝ := ![1, 2] with hp
  have hp0 : ∀ i, 0 < p i := fun i ↦ by fin_cases i <;> norm_num [hp]
  have hr0 : ∀ i j, 0 ≤ r i j := fun i j ↦ by fin_cases i <;> fin_cases j <;> norm_num [hr]
  have hrp : ∀ i j, r i j * p j ≤ p i := fun i j ↦ by
    fin_cases i <;> fin_cases j <;> norm_num [hr, hp]
  -- along a walk, the product of rates times the last price is at most the first price
  have tele : ∀ (L : List (Fin 2)) (a : Fin 2),
      walkProd r (a :: L) * p ((a :: L).getLast (List.cons_ne_nil a L)) ≤ p a := by
    intro L
    induction L with
    | nil => intro a; simp [walkProd]
    | cons b L ih =>
      intro a
      have h := ih b
      simp only [walkProd, List.getLast_cons_cons]
      calc r a b * walkProd r (b :: L) * p ((b :: L).getLast (List.cons_ne_nil b L))
          = r a b * (walkProd r (b :: L) * p ((b :: L).getLast (List.cons_ne_nil b L))) := by ring
        _ ≤ r a b * p b := mul_le_mul_of_nonneg_left h (hr0 a b)
        _ ≤ p a := hrp a b
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro (_ | ⟨a, L⟩) hc
    · exact absurd rfl hc
    have h := tele (L ++ [a]) a
    have hl : (a :: (L ++ [a])).getLast (List.cons_ne_nil _ _) = a := by
      rw [List.getLast_cons (by simp), List.getLast_append_singleton]
    rw [hl] at h
    have e : cycleProd r (a :: L) = walkProd r (a :: (L ++ [a])) := by
      simp [cycleProd]
    rw [e]
    nlinarith [hp0 a]
  · have h01 := h [0, 1] (by simp)
    simp [cycleSum, walkSum, negLog, hr] at h01
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- **A2: negative rates break (a) ⇔ (b).** Rates `r 0 1 = r 1 0 = −2` and `1` on the diagonal:
`p = (1, 1)` are prices, but the cycle `[0, 1]` has product `4 > 1`. -/
example : HasPrices (![![1, -2], ![-2, 1]] : Fin 2 → Fin 2 → ℝ) ∧
    ¬ NoGainCycle (![![1, -2], ![-2, 1]] : Fin 2 → Fin 2 → ℝ) := by
  refine ⟨⟨fun _ ↦ 1, fun _ ↦ one_pos, fun i j ↦ ?_⟩, fun h ↦ ?_⟩
  · fin_cases i <;> fin_cases j <;> norm_num
  · have h01 := h [0, 1] (by simp)
    norm_num [cycleProd, walkProd] at h01

/-- **A3: `n − 2` rounds of Bellman–Ford do not settle.** Three assets, weights
`w 0 1 = w 1 2 = −1`, `0` on the diagonal and `5` elsewhere: no cycle has negative weight (the
potential `(0, −1, −2)`), yet round `2` lowers the value at asset `2` after round `1` (from `−1` to
`−2`); round `3` changes nothing. -/
example : NoNegativeCycle (![![0, -1, 5], ![5, 0, -1], ![5, 5, 0]] : Fin 3 → Fin 3 → ℝ) ∧
    bellmanFord (![![0, -1, 5], ![5, 0, -1], ![5, 5, 0]] : Fin 3 → Fin 3 → ℝ) 2 ≠
      bellmanFord (![![0, -1, 5], ![5, 0, -1], ![5, 5, 0]] : Fin 3 → Fin 3 → ℝ) 1 ∧
    bellmanFord (![![0, -1, 5], ![5, 0, -1], ![5, 5, 0]] : Fin 3 → Fin 3 → ℝ) 3 =
      bellmanFord (![![0, -1, 5], ![5, 0, -1], ![5, 5, 0]] : Fin 3 → Fin 3 → ℝ) 2 := by
  set w : Fin 3 → Fin 3 → ℝ := ![![0, -1, 5], ![5, 0, -1], ![5, 5, 0]] with hw
  have hneg : NoNegativeCycle w :=
    cycleSum_nonneg_of_potential (φ := ![0, -1, -2]) fun i j ↦ by
      fin_cases i <;> fin_cases j <;> norm_num [hw]
  refine ⟨hneg, fun h ↦ ?_, ?_⟩
  · have hw01 : w 0 1 = -1 := by simp [hw]
    have hw12 : w 1 2 = -1 := by simp [hw]
    have h2 : bellmanFord w 2 2 ≤ -2 := by
      have := bellmanFord_le_walkSum w 2 2 [0, 1] (by simp)
      simp only [List.cons_append, List.nil_append, walkSum, hw01, hw12] at this
      linarith
    have h1 : -1 ≤ bellmanFord w 1 2 := by
      change -1 ≤ min (bellmanFord w 0 2)
        (univ.inf' univ_nonempty fun i ↦ bellmanFord w 0 i + w i 2)
      refine le_min (by simp [bellmanFord]) (le_inf' _ _ fun i _ ↦ ?_)
      fin_cases i <;> norm_num [bellmanFord, hw]
    have := congrFun h 2
    linarith
  · simpa using bellmanFord_stable_of_short (w := w) fun c hc _ ↦ hneg c hc

/-! ### Item 145 (order LEAN-37): (b) ⇔ (a) by linear-program duality -/

section LinearProgramDual

open ClassicalLean.LinearProgram

/-- Every consecutive pair of the walk carries a positive entry of `y`. -/
private def LpPosWalk {ι : Type*} (y : ι × ι → ℝ) : List ι → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => 0 < y (a, b) ∧ LpPosWalk y (b :: rest)

/-- How often each pair occurs consecutively along a walk. -/
private noncomputable def lpMult {ι : Type*} [DecidableEq ι] : List ι → ι × ι → ℝ
  | [], _ => 0
  | [_], _ => 0
  | a :: b :: rest, p => (if p = (a, b) then 1 else 0) + lpMult (b :: rest) p

private theorem lpPosWalk_tail {ι : Type*} {y : ι × ι → ℝ} :
    ∀ {a : ι} {L : List ι}, LpPosWalk y (a :: L) → LpPosWalk y L
  | _, [], _ => by simp [LpPosWalk]
  | _, _ :: _, h => by simp only [LpPosWalk] at h; exact h.2

private theorem lpPosWalk_append_left {ι : Type*} {y : ι × ι → ℝ} :
    ∀ (A B : List ι), LpPosWalk y (A ++ B) → LpPosWalk y B
  | [], _, h => h
  | _ :: A, B, h => lpPosWalk_append_left A B (lpPosWalk_tail h)

private theorem lpPosWalk_append_right {ι : Type*} {y : ι × ι → ℝ} :
    ∀ (A B : List ι), LpPosWalk y (A ++ B) → LpPosWalk y A
  | [], _, _ => by simp [LpPosWalk]
  | [_], _, _ => by simp [LpPosWalk]
  | a :: b :: A, B, h => by
    have h' : LpPosWalk y (a :: b :: (A ++ B)) := h
    simp only [LpPosWalk] at h' ⊢
    exact ⟨h'.1, lpPosWalk_append_right (b :: A) B h'.2⟩

private theorem lpMult_nonneg {ι : Type*} [DecidableEq ι] :
    ∀ (L : List ι) (p : ι × ι), 0 ≤ lpMult L p
  | [], _ => by simp [lpMult]
  | [_], _ => by simp [lpMult]
  | a :: b :: rest, p => by
    have := lpMult_nonneg (b :: rest) p
    simp only [lpMult]
    split_ifs <;> linarith

private theorem lpPos_of_mult {ι : Type*} [DecidableEq ι] {y : ι × ι → ℝ} :
    ∀ (L : List ι) (p : ι × ι), LpPosWalk y L → lpMult L p ≠ 0 → 0 < y p
  | [], _, _, hm => by simp [lpMult] at hm
  | [_], _, _, hm => by simp [lpMult] at hm
  | a :: b :: rest, p, h, hm => by
    simp only [LpPosWalk] at h
    simp only [lpMult] at hm
    by_cases hp : p = (a, b)
    · rw [hp]; exact h.1
    · rw [ite_eq_right hp, zero_add] at hm
      exact lpPos_of_mult (b :: rest) p h.2 hm

private theorem lpSum_mult {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∀ (L : List ι) (f : ι × ι → ℝ),
      ∑ p, lpMult L p * f p = walkSum (fun i j => f (i, j)) L
  | [], _ => by simp [lpMult, walkSum]
  | [_], _ => by simp [lpMult, walkSum]
  | a :: b :: rest, f => by
    have ih := lpSum_mult (b :: rest) f
    simp [lpMult, walkSum, add_mul, Finset.sum_add_distrib, ih]

/-- A nonnegative certificate with nonnegative net inflow everywhere has nonnegative weight
when no cycle has negative weight. -/
private theorem lpKey {ι : Type*} [Fintype ι] {w : ι → ι → ℝ}
    (hw : NoNegativeCycle w) : ∀ (n : ℕ) (y : ι × ι → ℝ),
      (univ.filter fun p => 0 < y p).card = n → 0 ≤ y →
      (∀ z : ι → ℝ, 0 ≤ z → 0 ≤ ∑ p, y p * (z p.2 - z p.1)) →
      0 ≤ ∑ p, y p * w p.1 p.2 := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro y hn hy H
  have hy' : ∀ p, 0 ≤ y p := fun p => hy p
  rcases em (∃ p, 0 < y p) with ⟨⟨k, j⟩, hkj⟩ | hpos
  swap
  · refine le_of_eq (Finset.sum_eq_zero fun p _ => ?_).symm
    have : y p = 0 := le_antisymm (not_lt.mp fun h => hpos ⟨p, h⟩) (hy' p)
    rw [this, zero_mul]
  -- an edge leaving `a` forces an edge entering `a`
  have pred : ∀ a b, 0 < y (a, b) → ∃ i, 0 < y (i, a) := by
    intro a b hab
    by_contra hno
    have hno' : ∀ i, y (i, a) = 0 :=
      fun i => le_antisymm (not_lt.mp fun h => hno ⟨i, h⟩) (hy' _)
    set ind : ι → ℝ := fun m => if m = a then 1 else 0 with hind
    have hx : 0 ≤ ind := fun m => by
      simp only [hind, Pi.zero_apply]
      split_ifs <;> norm_num
    have hba : b ≠ a := fun e => by
      rw [e, hno' a] at hab
      exact lt_irrefl _ hab
    have hlt : ∑ p, y p * (ind p.2 - ind p.1) < ∑ _p : ι × ι, (0 : ℝ) := by
      refine Finset.sum_lt_sum (fun p _ => ?_) ⟨(a, b), Finset.mem_univ _, ?_⟩
      · obtain ⟨c, d⟩ := p
        change y (c, d) * (ind d - ind c) ≤ 0
        by_cases hd : d = a
        · have : y (c, d) = 0 := by rw [hd]; exact hno' c
          simp [this]
        · have h1 : ind d = 0 := by simp [hind, hd]
          have h2 : (0 : ℝ) ≤ ind c := hx c
          rw [h1]
          nlinarith [hy' (c, d), h2]
      · change y (a, b) * (ind b - ind a) < 0
        have h1 : ind b = 0 := by simp [hind, hba]
        have h2 : ind a = 1 := by simp [hind]
        rw [h1, h2]
        linarith
    rw [Finset.sum_const_zero] at hlt
    linarith [H ind hx]
  -- a long backward walk along positive entries
  have walk : ∀ m : ℕ, ∃ a L, L.length = m ∧ LpPosWalk y (a :: L) ∧ ∃ b, 0 < y (a, b) := by
    intro m
    induction m with
    | zero => exact ⟨k, [], rfl, by simp [LpPosWalk], j, hkj⟩
    | succ m ihm =>
      obtain ⟨a, L, hL, hP, b, hb⟩ := ihm
      obtain ⟨i, hi⟩ := pred a b hb
      refine ⟨i, a :: L, by simp [hL], ?_, a, hi⟩
      simp only [LpPosWalk]
      exact ⟨hi, hP⟩
  obtain ⟨a, L, hL, hP, -⟩ := walk (Fintype.card ι)
  have hnd : ¬ (a :: L).Nodup := fun hnd => by
    have := hnd.length_le_card
    simp only [List.length_cons, hL] at this
    omega
  obtain ⟨s, x, u, v, hsv⟩ := exists_dup_of_not_nodup hnd
  have hC : LpPosWalk y (x :: (u ++ [x])) := by
    have e : a :: L = s ++ ((x :: (u ++ [x])) ++ v) := by rw [hsv]; simp
    rw [e] at hP
    exact lpPosWalk_append_right _ _ (lpPosWalk_append_left _ _ hP)
  have hcyc : ∀ w' : ι → ι → ℝ, cycleSum w' (x :: u) = walkSum w' (x :: (u ++ [x])) :=
    fun w' => by rfl
  obtain ⟨b, rest, hbr⟩ := List.exists_cons_of_ne_nil (show u ++ [x] ≠ [] by simp)
  have hm0 : 0 < lpMult (x :: (u ++ [x])) (x, b) := by
    rw [hbr]
    have h1 : lpMult (x :: b :: rest) (x, b) = 1 + lpMult (b :: rest) (x, b) := by
      simp [lpMult]
    rw [h1]
    linarith [lpMult_nonneg (b :: rest) (x, b)]
  obtain ⟨p0, hp0P, hmin⟩ :=
    (univ.filter fun p => 0 < lpMult (x :: (u ++ [x])) p).exists_min_image
      (fun p => y p / lpMult (x :: (u ++ [x])) p)
      ⟨(x, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm0⟩⟩
  have hmp0 : 0 < lpMult (x :: (u ++ [x])) p0 := (Finset.mem_filter.mp hp0P).2
  have hyp0 : 0 < y p0 := lpPos_of_mult _ p0 hC hmp0.ne'
  obtain ⟨t, ht_def⟩ : ∃ t, t = y p0 / lpMult (x :: (u ++ [x])) p0 := ⟨_, rfl⟩
  have ht : 0 ≤ t := by rw [ht_def]; exact div_nonneg hyp0.le hmp0.le
  have htm : t * lpMult (x :: (u ++ [x])) p0 = y p0 := by
    rw [ht_def]; exact div_mul_cancel₀ _ hmp0.ne'
  have hle : ∀ p, t * lpMult (x :: (u ++ [x])) p ≤ y p := by
    intro p
    by_cases hp : 0 < lpMult (x :: (u ++ [x])) p
    · have h3 : y p0 / lpMult (x :: (u ++ [x])) p0 ≤ y p / lpMult (x :: (u ++ [x])) p :=
        hmin p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
      rw [← ht_def, le_div_iff₀ hp] at h3
      exact h3
    · have : lpMult (x :: (u ++ [x])) p = 0 :=
        le_antisymm (not_lt.mp hp) (lpMult_nonneg _ p)
      rw [this, mul_zero]
      exact hy' p
  have hy'0 : (0 : ι × ι → ℝ) ≤ fun p => y p - t * lpMult (x :: (u ++ [x])) p := fun p => by
    change (0 : ℝ) ≤ y p - t * lpMult (x :: (u ++ [x])) p
    linarith [hle p]
  have hsplit : ∀ f : ι × ι → ℝ, ∑ p, (y p - t * lpMult (x :: (u ++ [x])) p) * f p =
      ∑ p, y p * f p - t * ∑ p, lpMult (x :: (u ++ [x])) p * f p := by
    intro f
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  -- a cycle contributes nothing to the net inflow
  have hZ : ∀ z : ι → ℝ, ∑ p, lpMult (x :: (u ++ [x])) p * (z p.2 - z p.1) = 0 := by
    intro z
    have e1 : ∑ p, lpMult (x :: (u ++ [x])) p * (z p.2 - z p.1) =
        walkSum (fun i j => z j - z i) (x :: (u ++ [x])) :=
      lpSum_mult _ (fun p => z p.2 - z p.1)
    have e2 : ∑ p, lpMult (x :: (u ++ [x])) p * (z p.1 - z p.2) =
        walkSum (fun i j => z i - z j) (x :: (u ++ [x])) :=
      lpSum_mult _ (fun p => z p.1 - z p.2)
    have c1 : 0 ≤ cycleSum (fun i j => z j - z i) (x :: u) :=
      cycleSum_nonneg_of_potential (w := fun i j => z j - z i) (φ := z)
        (fun i j => show z j ≤ z i + (z j - z i) by linarith) _ (List.cons_ne_nil _ _)
    have c2 : 0 ≤ cycleSum (fun i j => z i - z j) (x :: u) :=
      cycleSum_nonneg_of_potential (w := fun i j => z i - z j) (φ := fun i => -z i)
        (fun i j => show -z j ≤ -z i + (z i - z j) by linarith) _ (List.cons_ne_nil _ _)
    rw [hcyc] at c1 c2
    have e3 : ∑ p, lpMult (x :: (u ++ [x])) p * (z p.1 - z p.2) =
        -∑ p, lpMult (x :: (u ++ [x])) p * (z p.2 - z p.1) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun p _ => by ring
    apply le_antisymm <;> linarith
  have hcard : (univ.filter fun p => 0 < y p - t * lpMult (x :: (u ++ [x])) p).card < n := by
    rw [← hn]
    have hsub : (univ.filter fun p => 0 < y p - t * lpMult (x :: (u ++ [x])) p) ⊆
        univ.filter fun p => 0 < y p := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      linarith [mul_nonneg ht (lpMult_nonneg (x :: (u ++ [x])) p)]
    exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr
      ⟨p0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyp0⟩, by simp [htm]⟩)
  have H' : ∀ z : ι → ℝ, 0 ≤ z →
      0 ≤ ∑ p, (y p - t * lpMult (x :: (u ++ [x])) p) * (z p.2 - z p.1) := by
    intro z hz
    rw [hsplit (fun p => z p.2 - z p.1), hZ z, mul_zero, sub_zero]
    exact H z hz
  have hrec : 0 ≤ ∑ p, (y p - t * lpMult (x :: (u ++ [x])) p) * w p.1 p.2 :=
    ih _ hcard (fun p => y p - t * lpMult (x :: (u ++ [x])) p) rfl hy'0 H'
  have hcw : 0 ≤ ∑ p, lpMult (x :: (u ++ [x])) p * w p.1 p.2 := by
    have e : ∑ p, lpMult (x :: (u ++ [x])) p * w p.1 p.2 = walkSum w (x :: (u ++ [x])) :=
      lpSum_mult _ (fun p => w p.1 p.2)
    rw [e, ← hcyc w]
    exact hw _ (List.cons_ne_nil _ _)
  rw [hsplit (fun p => w p.1 p.2)] at hrec
  linarith [mul_nonneg ht hcw]

/-- **Prices ⇔ no gain around any cycle, by linear-program duality.** For finitely many assets
with positive rates, positive prices with `r i j · p j ≤ p i` exist exactly when every cycle's
product of rates is at most `1`; the potentials `log p` are the variables of a linear program,
whose feasibility Farkas' lemma reduces to cycles. -/
theorem hasPrices_iff_of_lp {ι : Type*} [Finite ι] {r : ι → ι → ℝ}
    (hr : ∀ i j, 0 < r i j) : HasPrices r ↔ NoGainCycle r := by
  constructor
  · intro h
    obtain ⟨φ, hφ⟩ := (hasPrices_iff_potential hr).mp h
    exact (noGainCycle_iff_noNegativeCycle hr).mpr (cycleSum_nonneg_of_potential hφ)
  · intro h
    classical
    cases nonempty_fintype ι
    have hw : NoNegativeCycle (negLog r) := (noGainCycle_iff_noNegativeCycle hr).mp h
    let Lm : (ι → ℝ) →ₗ[ℝ] (ι × ι → ℝ) :=
      LinearMap.funLeft ℝ ℝ Prod.snd - LinearMap.funLeft ℝ ℝ Prod.fst
    obtain ⟨z, -, hz⟩ := (farkas Lm (fun p : ι × ι => negLog r p.1 p.2)).mpr
      fun y hy hyL => lpKey hw _ y rfl hy fun x hx => hyL x hx
    exact (hasPrices_iff_potential hr).mpr ⟨z, fun i j => by
      have h1 : z j - z i ≤ negLog r i j := hz (i, j)
      linarith⟩

end LinearProgramDual

end ClassicalLean.Combinatorics

/-- The hypotheses of `bellmanFord_stable_iff` hold together: three assets, the rate `1` from an
asset to itself and `1/2` between two different ones, all positive. -/
example := ClassicalLean.Combinatorics.bellmanFord_stable_iff (ι := Fin 3)
  (r := fun i j ↦ if i = j then 1 else 1 / 2) (fun i j ↦ by split_ifs <;> norm_num)

/-- The hypotheses of `forall_cycle_prod_le_one_iff_exists_prices` hold together: three assets, the
rate `1` from an asset to itself and `1/2` between two different ones, all positive. -/
example := ClassicalLean.Combinatorics.forall_cycle_prod_le_one_iff_exists_prices (ι := Fin 3)
  (r := fun i j ↦ if i = j then 1 else 1 / 2) (fun i j ↦ by split_ifs <;> norm_num)

/-- The hypotheses of `hasPrices_iff_of_lp` hold together: three assets with positive rates, not all
equal: `1` from an asset to itself, `2` from `0` to `1`, `1/2` back and `1/2` for every other pair.
Every cycle's product is at most `1`; it is exactly `1` only for cycles that use no conversion but
`0 → 1`, `1 → 0` and the trips `i → i` (the round trip `0 → 1 → 0` has product `2 · 1/2 = 1`, which
forces `p₀ = 2 p₁` on any prices), and below `1` for every cycle using another conversion (all
3279 cycles of length at most `7`, in exact fractions, `~/lean/lean37-checks/w145/cycles.py`). -/
example := ClassicalLean.Combinatorics.hasPrices_iff_of_lp (ι := Fin 3)
  (r := ![![1, 2, 1 / 2], ![1 / 2, 1, 1 / 2], ![1 / 2, 1 / 2, 1]])
  (fun i j ↦ by fin_cases i <;> fin_cases j <;> norm_num)
