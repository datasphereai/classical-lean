/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Ring.GeomSum

/-!
# Galton–Watson extinction: the least fixed point of the generating function

In a Galton–Watson family tree, started from one member, each member has `k` children with
chance `p k`, independently of everyone else. The chance that the family has died out by
generation `n` is `fⁿ(0)`, where `f s = ∑ p k s ^ k` is the generating function of `p`
(`pgf p`). That reading is the standard one and is not proved here: this file is about the
iterates of `f` on `[0, 1]`. Citation: Watson and Galton 1875, "On the probability of the
extinction of families".

Order LEAN-22 (item 45 of the plan) proves, for `p k ≥ 0` with `∑ p k = 1`:

* `monotone_iterate_zero`: the iterates `fⁿ(0)` rise;
* `tendsto_iterate_zero`: they converge to `extinctionChance p`, defined as the least `s ∈ [0, 1]`
  with `f s = s`; `isLeast_extinctionChance`: that least fixed point exists;
* `extinctionChance_eq_one_iff`: when `p 1 ≠ 1`, it is `1` exactly when the mean number of
  children `∑ k p k` is finite and at most `1`;
* `extinctionChance_eq_zero_of_eq_one`: the exception, one child for sure (`p 1 = 1`): then
  `f s = s` for every `s`, the least fixed point is `0` (the family never dies out), while the
  mean is `1`.

The mean is written `Summable (fun k ↦ k * p k) ∧ ∑' k, k * p k ≤ 1`, so that an infinite mean
counts as above `1` (Lean's `∑'` of a series that is not summable is `0`).

The proof of the last part: `1 − f s = ∑ p k (1 − s ^ k)`. Bernoulli's inequality
`1 − s ^ k ≤ k (1 − s)` (Mathlib's `one_add_mul_le_pow`) gives `1 − f s ≤ m (1 − s)`, strictly
when some `p k > 0` with `k ≥ 2`, so for `m ≤ 1` no `s < 1` is fixed; one child for sure is the
only law with `m = 1` and no `p k > 0` for `k ≥ 2`. When `m > 1` (or infinite), a partial sum of
`k p k` exceeds `1`, so for `s` close to `1`, `(1 − f s) / (1 − s) > 1`: `f s < s`, and the
iterates stay below that `s`.

## Hypotheses

Measured in order LEAN-22's checks (check C45; exact unless marked): with `p = (1/4, 1/4, 1/2)`,
mean `5/4`, the fixed points in `[0, 1]` are `1/2` and `1` and the iterates rise below `1/2`; with
`p = (1/2, 0, 1/2)`, mean `1`, the only fixed point is `1`; on 1899 random laws with at most 6
outcomes (FLOAT; 101 of 2000 drawn were skipped because their mean was within `0.05` of `1`) the
limit is `1` exactly when the mean is at most `1`. Each hypothesis is needed;
drop it alone and a conclusion fails:

* `p 1 ≠ 1` (for "mean at most 1 gives 1"): one child for sure: the least fixed point is `0`, the
  mean `1`.
* `∑ p k = 1`: `p = (1/2)`: `f = 1/2`, the least fixed point is `1/2` and the mean `0`; with
  `p = (2)` there is no fixed point in `[0, 1]` at all.
* `p k ≥ 0`: `p = (−1, 0, 2)`: `f s = 2 s² − 1`, the only fixed point in `[0, 1]` is `1`, but the
  mean is `4`; and the iterates `0, −1, 1, 1, …` do not rise.

## What Mathlib provides

No branching process: `galton|watson|branching process|extinction` has 1 hit in Mathlib v4.34.0, a
citation of a book by Whittaker and Watson; in `Probability/`, "generating function" appears only
for the moment and cumulant generating functions, and there is no probability generating function
(order LEAN-22's search; elsewhere the words occur for power series in combinatorics). Used:
`continuousOn_tsum` (the generating function is continuous on `[0, 1]`), `tendsto_atTop_ciSup`,
`one_add_mul_le_pow`, `mul_neg_geom_sum`, `not_summable_iff_tendsto_nat_atTop_of_nonneg`.
-/

open Filter Topology Set

namespace ClassicalLean.Probability.Extinction

variable {p : ℕ → ℝ}

/-- The generating function `∑ p k s ^ k` of the law `p` on `{0, 1, 2, …}`. -/
noncomputable def pgf (p : ℕ → ℝ) (s : ℝ) : ℝ := ∑' k, p k * s ^ k

/-- The least fixed point of the generating function in `[0, 1]` (Lean's `sInf`; it exists by
`isLeast_extinctionChance`). -/
noncomputable def extinctionChance (p : ℕ → ℝ) : ℝ := sInf {s | s ∈ Icc 0 1 ∧ pgf p s = s}

section

variable (hp0 : ∀ k, 0 ≤ p k) (hp : HasSum p 1)
include hp0 hp

/-- The series of the generating function converges on `[0, 1]`. -/
theorem summable_pgf {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : Summable fun k ↦ p k * s ^ k :=
  Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (hp0 k) (pow_nonneg hs.1 k))
    (fun k ↦ mul_le_of_le_one_right (hp0 k) (pow_le_one₀ hs.1 hs.2)) hp.summable

omit hp0 in
/-- `f 1 = 1`. -/
theorem pgf_one : pgf p 1 = 1 := by simp [pgf, hp.tsum_eq]

omit hp0 hp in
/-- `f 0 = p 0`. -/
theorem pgf_zero (p : ℕ → ℝ) : pgf p 0 = p 0 := by
  rw [pgf, tsum_eq_single 0 fun k hk ↦ by simp [zero_pow hk]]
  simp

/-- The generating function is increasing on `[0, 1]`. -/
theorem pgf_mono {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) :
    pgf p s ≤ pgf p t :=
  (summable_pgf hp0 hp hs).tsum_le_tsum
    (fun k ↦ mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.1 hst k) (hp0 k))
    (summable_pgf hp0 hp ht)

/-- The generating function maps `[0, 1]` into itself. -/
theorem pgf_mem_Icc {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : pgf p s ∈ Icc (0 : ℝ) 1 :=
  ⟨tsum_nonneg fun k ↦ mul_nonneg (hp0 k) (pow_nonneg hs.1 k),
    (pgf_one hp) ▸ pgf_mono hp0 hp hs ⟨zero_le_one, le_rfl⟩ hs.2⟩

/-- The generating function is continuous on `[0, 1]`. -/
theorem continuousOn_pgf : ContinuousOn (pgf p) (Icc 0 1) := by
  refine continuousOn_tsum (fun k ↦ (continuous_const.mul (continuous_pow k)).continuousOn)
    hp.summable fun k s hs ↦ ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp0 k) (pow_nonneg hs.1 k))]
  exact mul_le_of_le_one_right (hp0 k) (pow_le_one₀ hs.1 hs.2)

/-- The iterates from `0` stay in `[0, 1]`. -/
theorem iterate_zero_mem_Icc (n : ℕ) : (pgf p)^[n] 0 ∈ Icc (0 : ℝ) 1 := by
  induction n with
  | zero => exact ⟨le_rfl, zero_le_one⟩
  | succ n ih => rw [Function.iterate_succ_apply']; exact pgf_mem_Icc hp0 hp ih

/-- The iterates `fⁿ(0)` rise. -/
theorem monotone_iterate_zero : Monotone fun n ↦ (pgf p)^[n] 0 := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  induction n with
  | zero =>
    simp only [Function.iterate_zero, id_eq]
    exact (pgf_mem_Icc hp0 hp ⟨le_rfl, zero_le_one⟩).1
  | succ n ih =>
    rw [Function.iterate_succ_apply' _ (n + 1), Function.iterate_succ_apply' _ n]
    exact pgf_mono hp0 hp (iterate_zero_mem_Icc hp0 hp n)
      (pgf_mem_Icc hp0 hp (iterate_zero_mem_Icc hp0 hp n))
      (by rwa [Function.iterate_succ_apply'] at ih)

/-- All the iterates from `0` stay below any point `s ∈ [0, 1]` with `pgf s ≤ s`. -/
theorem iterate_zero_le {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hfs : pgf p s ≤ s) (n : ℕ) :
    (pgf p)^[n] 0 ≤ s := by
  induction n with
  | zero => exact hs.1
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (pgf_mono hp0 hp (iterate_zero_mem_Icc hp0 hp n) hs ih).trans hfs

/-- The limit of the iterates, and its properties. -/
private theorem limit_spec : IsLeast {s | s ∈ Icc 0 1 ∧ pgf p s = s} (⨆ n, (pgf p)^[n] 0) ∧
    Tendsto (fun n ↦ (pgf p)^[n] 0) atTop (𝓝 (⨆ n, (pgf p)^[n] 0)) := by
  set x : ℕ → ℝ := fun n ↦ (pgf p)^[n] 0
  have hbdd : BddAbove (range x) :=
    ⟨1, by rintro _ ⟨n, rfl⟩; exact (iterate_zero_mem_Icc hp0 hp n).2⟩
  have ht : Tendsto x atTop (𝓝 (⨆ n, x n)) :=
    tendsto_atTop_ciSup (monotone_iterate_zero hp0 hp) hbdd
  have hL : (⨆ n, x n) ∈ Icc (0 : ℝ) 1 :=
    ⟨(iterate_zero_mem_Icc hp0 hp 0).1.trans (le_ciSup hbdd 0),
      ciSup_le fun n ↦ (iterate_zero_mem_Icc hp0 hp n).2⟩
  have hfix : pgf p (⨆ n, x n) = ⨆ n, x n := by
    have h1 : Tendsto (fun n ↦ pgf p (x n)) atTop (𝓝 (pgf p (⨆ n, x n))) :=
      ((continuousOn_pgf hp0 hp) _ hL).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr
          ⟨ht, Eventually.of_forall fun n ↦ iterate_zero_mem_Icc hp0 hp n⟩)
    have h2 : Tendsto (fun n ↦ pgf p (x n)) atTop (𝓝 (⨆ n, x n)) := by
      have := ht.comp (tendsto_add_atTop_nat 1)
      refine this.congr fun n ↦ ?_
      simp only [Function.comp_apply, x, Function.iterate_succ_apply']
    exact tendsto_nhds_unique h1 h2
  refine ⟨⟨⟨hL, hfix⟩, fun s ⟨hs, hfs⟩ ↦ ciSup_le fun n ↦ iterate_zero_le hp0 hp hs hfs.le n⟩, ht⟩

/-- The generating function has a least fixed point in `[0, 1]`. -/
theorem isLeast_extinctionChance :
    IsLeast {s | s ∈ Icc 0 1 ∧ pgf p s = s} (extinctionChance p) := by
  have h := (limit_spec hp0 hp).1
  rwa [extinctionChance, h.csInf_eq]

/-- **Galton–Watson.** The iterates `fⁿ(0)` converge to the least fixed point of `f` in
`[0, 1]`. -/
theorem tendsto_iterate_zero :
    Tendsto (fun n ↦ (pgf p)^[n] 0) atTop (𝓝 (extinctionChance p)) := by
  have h := limit_spec hp0 hp
  rw [extinctionChance, h.1.csInf_eq]
  exact h.2

/-- One child for sure: the least fixed point is `0`. Without `∑ p = 1` this would still hold,
but in the case `p 0 > 0` only because Lean's `sInf` of the empty set is `0` (review r45), so the
hypothesis is kept; `p ≥ 0` is needed (`p = (1, 1, −1)`). -/
theorem extinctionChance_eq_zero_of_eq_one (hp1 : p 1 = 1) : extinctionChance p = 0 := by
  have hk : ∀ k, k ≠ 1 → p k = 0 := fun k hk ↦ by
    have h := hp.summable.sum_le_tsum {1, k} fun i _ ↦ hp0 i
    rw [hp.tsum_eq, Finset.sum_pair (Ne.symm hk), hp1] at h
    linarith [hp0 k]
  have h0 : (0 : ℝ) ∈ {s | s ∈ Icc 0 1 ∧ pgf p s = s} :=
    ⟨⟨le_rfl, zero_le_one⟩, by rw [pgf_zero, hk 0 zero_ne_one]⟩
  exact (isLeast_extinctionChance hp0 hp).unique ⟨h0, fun s hs ↦ hs.1.1⟩

omit hp0 hp in
/-- Bernoulli's inequality on `[0, 1]`: `1 − s ^ k ≤ k (1 − s)`. -/
private theorem one_sub_pow_le {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (k : ℕ) :
    1 - s ^ k ≤ k * (1 - s) := by
  have := one_add_mul_le_pow (a := s - 1) (by linarith [hs.1]) k
  rw [add_sub_cancel] at this
  linarith

omit hp0 hp in
/-- Strictly, for `k ≥ 2` and `0 ≤ s < 1`. -/
private theorem one_sub_pow_lt {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) {k : ℕ} (hk : 2 ≤ k) :
    1 - s ^ k < k * (1 - s) := by
  induction k, hk using Nat.le_induction with
  | base => push_cast; nlinarith
  | succ k hk ih =>
    have hsk : s ^ k ≤ 1 := pow_le_one₀ hs0 hs1.le
    rw [pow_succ]
    push_cast
    nlinarith

/-- `1 − pgf s = ∑ p k (1 − s ^ k)`. -/
private theorem one_sub_pgf {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    HasSum (fun k ↦ p k * (1 - s ^ k)) (1 - pgf p s) := by
  have e : (fun k ↦ p k * (1 - s ^ k)) = fun k ↦ p k - p k * s ^ k := by funext k; ring
  rw [e]
  exact hp.sub (summable_pgf hp0 hp hs).hasSum

/-- **The family surely dies out exactly when the mean is at most `1`.** When `p 1 ≠ 1`, the
least fixed point is `1` exactly when the mean number of children `∑ k p k` is finite and at
most `1`. -/
theorem extinctionChance_eq_one_iff (hp1 : p 1 ≠ 1) :
    extinctionChance p = 1 ↔
      Summable (fun k : ℕ ↦ (k : ℝ) * p k) ∧ ∑' k : ℕ, (k : ℝ) * p k ≤ 1 := by
  have hL := isLeast_extinctionChance hp0 hp
  have hnn : ∀ {s : ℝ}, s ∈ Icc (0 : ℝ) 1 → ∀ k, 0 ≤ p k * (1 - s ^ k) := fun hs k ↦
    mul_nonneg (hp0 k) (sub_nonneg.mpr (pow_le_one₀ hs.1 hs.2))
  constructor
  · intro h1
    by_contra hcon
    -- some partial sum of `k p k` exceeds `1`
    obtain ⟨K, hK⟩ : ∃ K, 1 < ∑ k ∈ Finset.range K, (k : ℝ) * p k := by
      by_cases hs : Summable fun k : ℕ ↦ (k : ℝ) * p k
      · have hgt : 1 < ∑' k : ℕ, (k : ℝ) * p k := by
          by_contra h; exact hcon ⟨hs, not_lt.mp h⟩
        exact (hs.hasSum.tendsto_sum_nat.eventually (lt_mem_nhds hgt)).exists
      · have := (not_summable_iff_tendsto_nat_atTop_of_nonneg
          fun k ↦ mul_nonneg k.cast_nonneg (hp0 k)).mp hs
        exact (this.eventually (eventually_gt_atTop 1)).exists
    -- `g s = ∑_{k < K} p k (1 + s + ⋯ + s ^ (k − 1))` is continuous, with `g 1 > 1`
    set g : ℝ → ℝ := fun s ↦ ∑ k ∈ Finset.range K, p k * ∑ j ∈ Finset.range k, s ^ j
    have hg1 : g 1 = ∑ k ∈ Finset.range K, (k : ℝ) * p k := by simp [g, mul_comm]
    have hgc : Continuous g := by fun_prop
    have hev : ∀ᶠ s in 𝓝[<] 1, 1 < g s ∧ s ∈ Ioo 0 1 :=
      (((hgc.tendsto 1).eventually (lt_mem_nhds (hg1 ▸ hK))).filter_mono
        nhdsWithin_le_nhds).and (Ioo_mem_nhdsLT zero_lt_one)
    obtain ⟨s, hgs, hs⟩ := hev.exists
    have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
    -- `1 − pgf s ≥ ∑_{k < K} p k (1 − s ^ k) = (1 − s) g s > 1 − s`, so `pgf s < s`
    have hpart := (one_sub_pgf hp0 hp hsI).summable.sum_le_tsum (Finset.range K)
      fun k _ ↦ hnn hsI k
    rw [(one_sub_pgf hp0 hp hsI).tsum_eq] at hpart
    have hfin : ∑ k ∈ Finset.range K, p k * (1 - s ^ k) = (1 - s) * g s := by
      simp only [g, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [← mul_neg_geom_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    have : (1 - s) * 1 < (1 - s) * g s := mul_lt_mul_of_pos_left hgs (by linarith [hs.2])
    have hlt : pgf p s < s := by linarith
    have : extinctionChance p ≤ s :=
      le_of_tendsto' (tendsto_iterate_zero hp0 hp) (iterate_zero_le hp0 hp hsI hlt.le)
    linarith [hs.2]
  · rintro ⟨hs, hm⟩
    refine le_antisymm hL.1.1.2 (not_lt.mp fun hlt ↦ ?_)
    set s := extinctionChance p
    have hsI := hL.1.1
    have hfix : pgf p s = s := hL.1.2
    have hsum := one_sub_pgf hp0 hp hsI
    have hb : ∀ k : ℕ, p k * (1 - s ^ k) ≤ (1 - s) * ((k : ℝ) * p k) := fun k ↦ by
      have := mul_le_mul_of_nonneg_left (one_sub_pow_le hsI k) (hp0 k)
      linarith
    have hg := (hs.mul_left (1 - s)).hasSum
    have hpos : 0 < 1 - s := by linarith
    -- strictly below `(1 − s) · 1` in both cases
    have key : 1 - pgf p s < (1 - s) * 1 := by
      rcases lt_or_eq_of_le hm with hm1 | hm1
      · calc 1 - pgf p s ≤ (1 - s) * ∑' k : ℕ, (k : ℝ) * p k := by
              rw [← hs.tsum_mul_left]; exact hasSum_le hb hsum (hs.mul_left _).hasSum
          _ < (1 - s) * 1 := mul_lt_mul_of_pos_left hm1 hpos
      · obtain ⟨k, hk2, hpk⟩ : ∃ k, 2 ≤ k ∧ 0 < p k := by
          by_contra hno
          push Not at hno
          have hzero : ∀ k : ℕ, k ≠ 1 → (k : ℝ) * p k = 0 := fun k hk ↦ by
            rcases k with _ | _ | k
            · simp
            · exact absurd rfl hk
            · rw [le_antisymm (hno (k + 2) (by omega)) (hp0 (k + 2)), mul_zero]
          rw [tsum_eq_single 1 hzero, Nat.cast_one, one_mul] at hm1
          exact hp1 hm1
        have hstrict : p k * (1 - s ^ k) < (1 - s) * ((k : ℝ) * p k) := by
          have := mul_lt_mul_of_pos_left (one_sub_pow_lt hsI.1 hlt hk2) hpk
          linarith
        calc 1 - pgf p s < (1 - s) * ∑' k : ℕ, (k : ℝ) * p k := by
              rw [← hs.tsum_mul_left, ← hsum.tsum_eq]
              exact hsum.summable.tsum_lt_tsum hb hstrict (hs.mul_left _)
          _ = (1 - s) * 1 := by rw [hm1]
    rw [hfix, mul_one] at key
    exact lt_irrefl _ key

end

end ClassicalLean.Probability.Extinction

/-- The hypotheses of `tendsto_iterate_zero` hold together: the offspring law with chance `1/4` of
no child, `1/4` of one and `1/2` of two (mean `5/4`, so the line can survive), nonnegative and
summing to `1`. -/
example := ClassicalLean.Probability.Extinction.tendsto_iterate_zero
  (p := fun k : ℕ ↦ if k = 0 then (1 / 4 : ℝ) else if k = 1 then 1 / 4 else if k = 2 then 1 / 2
    else 0)
  (hp0 := fun k ↦ by split_ifs <;> norm_num)
  (hp := by
    have h : HasSum (fun k : ℕ ↦ if k = 0 then (1 / 4 : ℝ) else if k = 1 then 1 / 4
        else if k = 2 then 1 / 2 else 0)
        (∑ k ∈ Finset.range 3, if k = 0 then (1 / 4 : ℝ) else if k = 1 then 1 / 4
          else if k = 2 then 1 / 2 else 0) :=
      hasSum_sum_of_ne_finset_zero fun k hk ↦ by
        simp only [Finset.mem_range, not_lt] at hk
        simp [show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega]
    norm_num [Finset.sum_range_succ] at h
    exact h)
