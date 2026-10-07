/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.InformationTheory.MutualInformation
import ClassicalLean.Probability.RelativeEntropyGrowth

/-!
# What a signal is worth: the gain in best growth is the mutual information

Outcomes `x : α` and signals `y : β` have a joint distribution `P` (`P ≥ 0`, `∑ P = 1`), with
marginals `pX x = ∑ y, P (x, y)` and `pY y = ∑ x, P (x, y)`. Outcome `x` pays `o x > 0` per unit
staked, and all wealth is staked each round.

* Without the signal, stakes `b x ≥ 0` sum to `1` and are positive wherever `pX x > 0`; the growth
  is `growthWithout P o b = ∑ x, pX x · log (b x · o x)`.
* With the signal, the stakes `b (x, y) ≥ 0` sum to `1` over `x` for each `y` and are positive
  wherever `P (x, y) > 0`; the growth is
  `growthWith P o b = ∑ (x, y), P (x, y) · log (b (x, y) · o x)`.

* `growthWithout_le`: the best stakes without the signal are `pX`.
* `growthWith_le`: the best stakes with the signal are `P (x, y) / pY y`.
* `growthWith_sub_growthWithout`: the best growth with the signal minus the best growth without it
  is `mutualInfo P`, for any positive payouts (Kelly, 1956).

The per-term step is the one behind `RelativeEntropyGrowth.growth_le_growth_self`
(`RelativeEntropyGrowth.sub_le_mul_log_div`); here stakes may be `0` where the chance is `0`.

Each hypothesis is needed. With Lean's `log 0 = 0`, a zero stake on a possible outcome scores as if
it cost nothing: chances `1/2, 1/2`, payouts `2`, stakes `(1, 0)` give `0.347` against `0` for
staking in proportion. If cash may be held back (stakes summing to less than `1`), the gain can
differ from `I(X; Y)`: with payouts `1.5` on a fair coin and a perfect signal, the gain is
`log 1.5 = 0.405`, not `log 2 = 0.693`.
-/

open Finset Real
open ClassicalLean.Simplex ClassicalLean.Probability

namespace ClassicalLean.InformationTheory.SignalGrowth

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Growth without the signal: `∑ x, pX x · log (b x · o x)`. -/
noncomputable def growthWithout (P : α × β → ℝ) (o b : α → ℝ) : ℝ :=
  ∑ x, (∑ y, P (x, y)) * log (b x * o x)

/-- Growth with the signal: `∑ (x, y), P (x, y) · log (b (x, y) · o x)`. -/
noncomputable def growthWith (P : α × β → ℝ) (o : α → ℝ) (b : α × β → ℝ) : ℝ :=
  ∑ xy, P xy * log (b xy * o xy.1)

/-- The best stakes with the signal: `P (x, y) / pY y`. -/
noncomputable def bestWith (P : α × β → ℝ) (xy : α × β) : ℝ := P xy / ∑ x, P (x, xy.2)

/-- One term: for `p, c, b ≥ 0`, `o > 0`, with `b > 0` and `c > 0` where `p > 0`,
`p log (b o) ≤ p log ((p / c) o) - p + c b`. -/
theorem mul_log_le {p c b o : ℝ} (hp : 0 ≤ p) (hc : 0 ≤ c) (hb : 0 ≤ b) (ho : 0 < o)
    (hbp : 0 < p → 0 < b) (hcp : 0 < p → 0 < c) :
    p * log (b * o) ≤ p * log (p / c * o) - p + c * b := by
  rcases hp.eq_or_lt with h | h
  · rw [← h]
    simp only [zero_mul, zero_div, log_zero, mul_zero, sub_self, zero_add]
    positivity
  · have hb' := hbp h
    have hc' := hcp h
    have key := RelativeEntropyGrowth.sub_le_mul_log_div h.le (mul_pos hc' hb')
    have e : log (p / c * o) = log (b * o) + log (p / (c * b)) := by
      rw [← log_mul (by positivity) (by positivity)]
      congr 1; field_simp
    rw [e]; nlinarith

variable {P : α × β → ℝ}

omit [Fintype α] in
lemma le_marginal_left (hP0 : ∀ xy, 0 ≤ P xy) (x : α) (y : β) : P (x, y) ≤ ∑ y', P (x, y') :=
  single_le_sum (f := fun y' ↦ P (x, y')) (fun _ _ ↦ hP0 _) (mem_univ y)

omit [Fintype β] in
lemma le_marginal_right (hP0 : ∀ xy, 0 ≤ P xy) (x : α) (y : β) : P (x, y) ≤ ∑ x', P (x', y) :=
  single_le_sum (f := fun x' ↦ P (x', y)) (fun _ _ ↦ hP0 _) (mem_univ x)

/-- **Best stakes without the signal.** For stakes `b ≥ 0` summing to `1`, positive wherever
`pX > 0`, and positive payouts: `growthWithout P o b ≤ growthWithout P o pX`. -/
theorem growthWithout_le (hP0 : ∀ xy, 0 ≤ P xy) (hP1 : ∑ xy, P xy = 1) {o b : α → ℝ}
    (ho : ∀ x, 0 < o x) (hb0 : ∀ x, 0 ≤ b x) (hb1 : ∑ x, b x = 1)
    (hbp : ∀ x, 0 < ∑ y, P (x, y) → 0 < b x) :
    growthWithout P o b ≤ growthWithout P o (fun x ↦ ∑ y, P (x, y)) := by
  have hsum : ∑ x, ∑ y, P (x, y) = 1 := by rw [← Fintype.sum_prod_type, hP1]
  have h := sum_le_sum fun x (_ : x ∈ univ) ↦
    mul_log_le (sum_nonneg fun y _ ↦ hP0 (x, y)) zero_le_one (hb0 x) (ho x) (hbp x)
      (fun _ ↦ one_pos)
  simp only [div_one, one_mul, sum_add_distrib, sum_sub_distrib, hsum, hb1] at h
  unfold growthWithout
  linarith

/-- **Best stakes with the signal.** For stakes `b ≥ 0` summing to `1` over `x` for each `y`,
positive wherever `P (x, y) > 0`, and positive payouts:
`growthWith P o b ≤ growthWith P o (bestWith P)`. -/
theorem growthWith_le (hP0 : ∀ xy, 0 ≤ P xy) (hP1 : ∑ xy, P xy = 1) {o : α → ℝ}
    (ho : ∀ x, 0 < o x) {b : α × β → ℝ} (hb0 : ∀ xy, 0 ≤ b xy) (hb1 : ∀ y, ∑ x, b (x, y) = 1)
    (hbp : ∀ xy, 0 < P xy → 0 < b xy) : growthWith P o b ≤ growthWith P o (bestWith P) := by
  have h := sum_le_sum fun xy (_ : xy ∈ univ) ↦
    mul_log_le (c := ∑ x, P (x, xy.2)) (hP0 xy) (sum_nonneg fun x _ ↦ hP0 (x, xy.2)) (hb0 xy)
      (ho xy.1) (hbp xy) (fun h ↦ h.trans_le (le_marginal_right hP0 xy.1 xy.2))
  have hcb : ∑ xy : α × β, (∑ x, P (x, xy.2)) * b xy = 1 := by
    rw [Fintype.sum_prod_type_right]
    simp_rw [← mul_sum, hb1, mul_one]
    rw [← hP1, Fintype.sum_prod_type_right]
  simp only [sum_add_distrib, sum_sub_distrib, hcb, hP1] at h
  unfold growthWith bestWith
  linarith

omit [Fintype β] in
/-- The best stakes with the signal are admissible: nonnegative, summing to `1` over `x` when
`pY y > 0`, and positive wherever `P (x, y) > 0`. -/
theorem bestWith_admissible (hP0 : ∀ xy, 0 ≤ P xy) :
    (∀ xy, 0 ≤ bestWith P xy) ∧ (∀ y, 0 < ∑ x, P (x, y) → ∑ x, bestWith P (x, y) = 1) ∧
      ∀ xy, 0 < P xy → 0 < bestWith P xy := by
  refine ⟨fun xy ↦ div_nonneg (hP0 xy) (sum_nonneg fun x _ ↦ hP0 _), fun y hy ↦ ?_,
    fun xy h ↦ div_pos h (h.trans_le (le_marginal_right hP0 xy.1 xy.2))⟩
  simp only [bestWith]
  rw [← sum_div, div_self hy.ne']

/-- **The value of the signal.** For a joint distribution `P` and positive payouts, the best
growth with the signal minus the best growth without it is the mutual information `I(X; Y)`. -/
theorem growthWith_sub_growthWithout (hP0 : ∀ xy, 0 ≤ P xy) {o : α → ℝ} (ho : ∀ x, 0 < o x) :
    growthWith P o (bestWith P) - growthWithout P o (fun x ↦ ∑ y, P (x, y)) = mutualInfo P := by
  unfold growthWith growthWithout mutualInfo relEntropy bestWith
  have hW : ∑ x, (∑ y, P (x, y)) * log ((∑ y, P (x, y)) * o x) =
      ∑ xy : α × β, P xy * log ((∑ y, P (xy.1, y)) * o xy.1) := by
    rw [Fintype.sum_prod_type]
    simp_rw [sum_mul]
  rw [hW, ← sum_sub_distrib]
  refine sum_congr rfl fun xy _ ↦ ?_
  rcases (hP0 xy).eq_or_lt with h | h
  · rw [← h]; simp
  · have hx : 0 < ∑ y, P (xy.1, y) := h.trans_le (le_marginal_left hP0 xy.1 xy.2)
    have hy : 0 < ∑ x, P (x, xy.2) := h.trans_le (le_marginal_right hP0 xy.1 xy.2)
    have hox := ho xy.1
    rw [← mul_sub, ← log_div (by positivity) (by positivity)]
    congr 2
    field_simp

end ClassicalLean.InformationTheory.SignalGrowth
