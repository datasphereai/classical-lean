/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.InformationTheory.MutualInformation
import ClassicalLean.Probability.RelativeEntropyGrowth
import ClassicalLean.Analysis.GeneralGrowth

/-!
# What a signal is worth: at most the mutual information, and exactly it when all is staked

Outcomes `x : α` and signals `y : β` have a joint distribution `P` (`P ≥ 0`, `∑ P = 1`), with
marginals `pX x = ∑ y, P (x, y)` and `pY y = ∑ x, P (x, y)`. In the first part, outcome `x` pays
`o x > 0` per unit staked, and all wealth is staked each round.

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
`log 1.5 = 0.405`, not `log 2 = 0.693`. `colGrowthWith_le_of_best` covers that case: there the gain
is at most `I(X; Y)` (in the example, `log 1.5` against `log 2`).

## Columns with any payoffs, cash allowed

Column `j` pays `R j x` per unit in outcome `x` (cash is a
column paying `1` in every outcome), and a weight vector `w` splits the whole among the columns.

* `factor R w x = ∑ j, w j · R j x`: the factor by which the whole changes in outcome `x`.
* `colGrowth P R w = ∑ x, pX x · log (factor R w x)`: the expected log growth without the signal.
* `colGrowthWith P R W = ∑ (x, y), P (x, y) · log (factor R (W y) x)`: with the weight vector `W y`
  chosen after seeing `y`.
* `colGrowthWith_le`: given the first-order condition
  `∑ x, pX x · factor R (W y) x / factor R w x ≤ 1` for each `y`, and the positivity conditions,
  the gain is at most `mutualInfo P`.
* `sum_mul_div_le_one_of_best`: a `w` best in a convex set `D` (among the members whose factors are
  positive wherever `pX > 0`; every member having factors at least `0` there) satisfies that
  condition against every member of `D`.
* `colGrowthWith_le_of_best`: so, with `w` best in `D` and every `W y ∈ D`, the gain in expected
  log growth from the signal is at most `mutualInfo P`, whatever the columns pay (Barron and Cover,
  1988). The route is derived here: cell by cell, `log t ≤ t - 1` at
  `t = factor R (W y) x · pX x · pY y / (factor R w x · P (x, y))`, summed with the first-order
  condition; the first-order condition itself comes from `GeneralGrowth.log_one_add_ge` along the
  segment from `w` to `v`.
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

/-! ### Columns with any payoffs, cash allowed -/

section columns

variable {γ : Type*} [Fintype γ]

/-- The factor by which the whole changes in outcome `x` when the weight `w j` goes to column `j`,
which pays `R j x` per unit. -/
noncomputable def factor (R : γ → α → ℝ) (w : γ → ℝ) (x : α) : ℝ := ∑ j, w j * R j x

/-- Expected log growth without the signal: one weight vector `w` for every signal. -/
noncomputable def colGrowth (P : α × β → ℝ) (R : γ → α → ℝ) (w : γ → ℝ) : ℝ :=
  ∑ x, (∑ y, P (x, y)) * Real.log (factor R w x)

/-- Expected log growth with the signal: the weight vector `W y` after seeing `y`. -/
noncomputable def colGrowthWith (P : α × β → ℝ) (R : γ → α → ℝ) (W : β → γ → ℝ) : ℝ :=
  ∑ xy : α × β, P xy * Real.log (factor R (W xy.2) xy.1)

/-- The value of a signal is at most the mutual information, given the first-order condition of
`w` against each `W y`: `w`'s factors positive where `P > 0`, each `W y`'s factors positive where
`P (x, y) > 0` and at least `0` wherever `x` has positive chance. -/
theorem colGrowthWith_le (P : α × β → ℝ) (hP0 : ∀ xy, 0 ≤ P xy) (R : γ → α → ℝ)
    {w : γ → ℝ} {W : β → γ → ℝ}
    (hpos : ∀ xy, 0 < P xy → 0 < factor R w xy.1)
    (hWpos : ∀ xy, 0 < P xy → 0 < factor R (W xy.2) xy.1)
    (hWnn : ∀ x y, 0 < ∑ y', P (x, y') → 0 ≤ factor R (W y) x)
    (hkkt : ∀ y, ∑ x, (∑ y', P (x, y')) * (factor R (W y) x / factor R w x) ≤ 1) :
    colGrowthWith P R W ≤ colGrowth P R w + mutualInfo P := by
  -- the cell bound: `P (log F - log f - log (P / (pX pY))) ≤ F pX pY / f - P`
  have hcell : ∀ xy : α × β,
      P xy * Real.log (factor R (W xy.2) xy.1) - P xy * Real.log (factor R w xy.1) -
          P xy * Real.log (P xy / ((∑ b, P (xy.1, b)) * ∑ a, P (a, xy.2))) ≤
        (∑ b, P (xy.1, b)) * (∑ a, P (a, xy.2)) *
            (factor R (W xy.2) xy.1 / factor R w xy.1) - P xy := by
    rintro ⟨x, y⟩
    set pX := ∑ b, P (x, b)
    set pY := ∑ a, P (a, y)
    have hpX0 : 0 ≤ pX := sum_nonneg fun _ _ ↦ hP0 _
    have hpY0 : 0 ≤ pY := sum_nonneg fun _ _ ↦ hP0 _
    rcases (hP0 (x, y)).eq_or_lt with h0 | hP
    · -- an empty cell: the right side is at least `0`
      rw [← h0]
      simp only [zero_mul, sub_zero, sub_self]
      rcases hpX0.eq_or_lt with hx0 | hx
      · rw [← hx0]; simp
      · obtain ⟨y', -, hy'⟩ := (sum_pos_iff_of_nonneg fun y _ ↦ hP0 (x, y)).1 hx
        have hf := hpos (x, y') hy'
        have hF := hWnn x y hx
        positivity
    · have hpX : 0 < pX := hP.trans_le (single_le_sum (f := fun b ↦ P (x, b))
        (fun _ _ ↦ hP0 _) (mem_univ y))
      have hpY : 0 < pY := hP.trans_le (single_le_sum (f := fun a ↦ P (a, y))
        (fun _ _ ↦ hP0 _) (mem_univ x))
      have hf := hpos (x, y) hP
      have hF := hWpos (x, y) hP
      simp only at hf hF ⊢
      set F := factor R (W y) x
      set f := factor R w x
      have ht : 0 < F * pX * pY / (f * P (x, y)) := by positivity
      have hlog := Real.log_le_sub_one_of_pos ht
      have e : Real.log (F * pX * pY / (f * P (x, y))) =
          Real.log F - Real.log f - Real.log (P (x, y) / (pX * pY)) := by
        rw [Real.log_div (by positivity) (by positivity), Real.log_div (by positivity)
          (by positivity), Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
          (by positivity), Real.log_mul (by positivity) (by positivity)]
        ring
      rw [e] at hlog
      have e2 : P (x, y) * (F * pX * pY / (f * P (x, y)) - 1) = pX * pY * (F / f) - P (x, y) := by
        field_simp
      have := mul_le_mul_of_nonneg_left hlog hP.le
      rw [e2] at this
      linarith
  -- sum the cells
  have hG : colGrowth P R w = ∑ xy : α × β, P xy * Real.log (factor R w xy.1) := by
    unfold colGrowth
    rw [Fintype.sum_prod_type]
    simp_rw [sum_mul]
  have hsum := sum_le_sum fun xy (_ : xy ∈ (univ : Finset (α × β))) ↦ hcell xy
  have hR : ∑ xy : α × β, ((∑ b, P (xy.1, b)) * (∑ a, P (a, xy.2)) *
        (factor R (W xy.2) xy.1 / factor R w xy.1) - P xy) =
      ∑ y, (∑ a, P (a, y)) * ∑ x, (∑ b, P (x, b)) * (factor R (W y) x / factor R w x) -
        ∑ xy : α × β, P xy := by
    rw [sum_sub_distrib, Fintype.sum_prod_type, sum_comm]
    congr 1
    refine sum_congr rfl fun y _ ↦ ?_
    rw [mul_sum]
    exact sum_congr rfl fun x _ ↦ by ring
  have hkk : ∑ y, (∑ a, P (a, y)) * ∑ x, (∑ b, P (x, b)) * (factor R (W y) x / factor R w x) ≤
      ∑ y, ∑ a, P (a, y) := sum_le_sum fun y _ ↦ by
    have := mul_le_mul_of_nonneg_left (hkkt y)
      (sum_nonneg (s := univ) (f := fun a ↦ P (a, y)) fun a _ ↦ hP0 (a, y))
    linarith
  have hPsum : ∑ y, ∑ a, P (a, y) = ∑ xy : α × β, P xy := by
    rw [sum_comm, ← Fintype.sum_prod_type]
  rw [hR] at hsum
  rw [sum_sub_distrib, sum_sub_distrib] at hsum
  unfold colGrowthWith mutualInfo relEntropy
  rw [hG]
  linarith

/-- A best weight vector `w` in a convex set `D` (best among the members of `D` whose factors are
positive wherever the outcome has positive chance; every member of `D` has factors at least `0`
there) satisfies the first-order condition against every member of `D`. -/
theorem sum_mul_div_le_one_of_best (P : α × β → ℝ) (hP0 : ∀ xy, 0 ≤ P xy)
    (hP1 : ∑ xy, P xy = 1) (R : γ → α → ℝ) {D : Set (γ → ℝ)} (hD : Convex ℝ D)
    {w v : γ → ℝ} (hw : w ∈ D) (hv : v ∈ D)
    (hwpos : ∀ x, 0 < ∑ y, P (x, y) → 0 < factor R w x)
    (hmax : ∀ u ∈ D, (∀ x, 0 < ∑ y, P (x, y) → 0 < factor R u x) →
      colGrowth P R u ≤ colGrowth P R w)
    (hDnn : ∀ u ∈ D, ∀ x, 0 < ∑ y, P (x, y) → 0 ≤ factor R u x) :
    ∑ x, (∑ y, P (x, y)) * (factor R v x / factor R w x) ≤ 1 := by
  set pX : α → ℝ := fun x ↦ ∑ y, P (x, y) with hpXdef
  have hpX0 : ∀ x, 0 ≤ pX x := fun x ↦ sum_nonneg fun _ _ ↦ hP0 _
  have hpX1 : ∑ x, pX x = 1 := by rw [hpXdef, ← Fintype.sum_prod_type, hP1]
  set a : α → ℝ := fun x ↦ factor R v x / factor R w x - 1 with hadef
  set S := ∑ x, pX x * a x with hS
  set Q := ∑ x, pX x * a x ^ 2 with hQ
  have hQ0 : 0 ≤ Q := sum_nonneg fun x _ ↦ mul_nonneg (hpX0 x) (sq_nonneg _)
  -- the factor of a mixture
  have hfac : ∀ t : ℝ, ∀ x, factor R ((1 - t) • w + t • v) x =
      (1 - t) * factor R w x + t * factor R v x := fun t x ↦ by
    simp only [factor, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, sum_add_distrib,
      mul_sum, mul_assoc]
  -- for every `t ∈ (0, 1/2]`, `S ≤ t Q`
  have hstep : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → S ≤ t * Q := fun t ht0 ht1 ↦ by
    have hmem : (1 - t) • w + t • v ∈ D := hD hw hv (by linarith) ht0.le (by ring)
    have hpos : ∀ x, 0 < pX x → 0 < factor R ((1 - t) • w + t • v) x := fun x hx ↦ by
      rw [hfac]
      have := hwpos x hx
      have := hDnn v hv x hx
      have : 0 < 1 - t := by linarith
      positivity
    have hle := hmax _ hmem hpos
    -- termwise: `pX (t a - t² a² / (2 (1 - t))) ≤ pX (log (mixture) - log w)`
    have hterm : ∀ x, pX x * (t * a x - (t * a x) ^ 2 / (2 * (1 - t))) ≤
        pX x * Real.log (factor R ((1 - t) • w + t • v) x) -
          pX x * Real.log (factor R w x) := fun x ↦ by
      rcases (hpX0 x).eq_or_lt with h0 | hx
      · rw [← h0]; simp
      · have hf := hwpos x hx
        have hg := hDnn v hv x hx
        have hval : factor R ((1 - t) • w + t • v) x = factor R w x * (1 + t * a x) := by
          rw [hfac, hadef]; field_simp; ring
        have hta : -t ≤ t * a x := by
          have : -1 ≤ a x := by
            rw [hadef]; have : 0 ≤ factor R v x / factor R w x := div_nonneg hg hf.le
            linarith
          nlinarith
        have h1 : 0 < 1 + t * a x := by linarith
        have hlog := ClassicalLean.Analysis.GeneralGrowth.log_one_add_ge ht0.le (by linarith) hta
        rw [hval, Real.log_mul hf.ne' h1.ne', ← mul_sub]
        apply mul_le_mul_of_nonneg_left _ hx.le
        linarith
    have hsum := sum_le_sum fun x (_ : x ∈ (univ : Finset α)) ↦ hterm x
    rw [sum_sub_distrib] at hsum
    have hL : ∑ x, pX x * (t * a x - (t * a x) ^ 2 / (2 * (1 - t))) =
        t * S - t ^ 2 / (2 * (1 - t)) * Q := by
      rw [hS, hQ, mul_sum, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun x _ ↦ ?_
      ring
    rw [hL] at hsum
    unfold colGrowth at hle
    have h1t : 0 < 1 - t := by linarith
    -- `t S ≤ t² Q / (2 (1 - t)) ≤ t² Q`
    have hk : t ^ 2 / (2 * (1 - t)) * Q ≤ t ^ 2 * Q := by
      apply mul_le_mul_of_nonneg_right _ hQ0
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg t]
    have : t * S ≤ t * (t * Q) := by nlinarith
    exact le_of_mul_le_mul_left this ht0
  -- hence `S ≤ 0`
  have hS0 : S ≤ 0 := by
    by_contra hpos
    push Not at hpos
    set t := min (1 / 2) (S / (Q + 1)) with ht
    have ht0 : 0 < t := lt_min (by norm_num) (div_pos hpos (by linarith))
    have h := hstep t ht0 (min_le_left _ _)
    have htQ : t * Q ≤ S / (Q + 1) * Q := mul_le_mul_of_nonneg_right (min_le_right _ _) hQ0
    have : S / (Q + 1) * Q < S := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  -- the first-order sum is `S + ∑ pX = S + 1`
  have heq : ∑ x, pX x * (factor R v x / factor R w x) = S + ∑ x, pX x := by
    rw [hS, ← sum_add_distrib]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [hadef]; ring
  change ∑ x, pX x * (factor R v x / factor R w x) ≤ 1
  rw [heq, hpX1]
  linarith

/-- **The value of a signal (Barron and Cover, 1988).** With `w` best in `D` without the signal (as
in `sum_mul_div_le_one_of_best`), and any `W y ∈ D` whose factors are positive where `P (x, y) > 0`,
the gain in expected log growth is at most the mutual information, whatever the columns pay, cash (a
column paying `1` in every outcome) included. -/
theorem colGrowthWith_le_of_best (P : α × β → ℝ) (hP0 : ∀ xy, 0 ≤ P xy)
    (hP1 : ∑ xy, P xy = 1) (R : γ → α → ℝ) {D : Set (γ → ℝ)} (hD : Convex ℝ D)
    {w : γ → ℝ} (hw : w ∈ D) (hwpos : ∀ x, 0 < ∑ y, P (x, y) → 0 < factor R w x)
    (hmax : ∀ u ∈ D, (∀ x, 0 < ∑ y, P (x, y) → 0 < factor R u x) →
      colGrowth P R u ≤ colGrowth P R w)
    (hDnn : ∀ u ∈ D, ∀ x, 0 < ∑ y, P (x, y) → 0 ≤ factor R u x)
    {W : β → γ → ℝ} (hW : ∀ y, W y ∈ D)
    (hWpos : ∀ xy, 0 < P xy → 0 < factor R (W xy.2) xy.1) :
    colGrowthWith P R W ≤ colGrowth P R w + mutualInfo P :=
  colGrowthWith_le P hP0 R
    (fun xy h ↦ hwpos xy.1 (h.trans_le (single_le_sum (f := fun y ↦ P (xy.1, y))
      (fun _ _ ↦ hP0 _) (mem_univ xy.2))))
    hWpos (fun x y hx ↦ hDnn (W y) (hW y) x hx)
    (fun y ↦ sum_mul_div_le_one_of_best P hP0 hP1 R hD hw (hW y) hwpos hmax hDnn)

end columns

end ClassicalLean.InformationTheory.SignalGrowth
