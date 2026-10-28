/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Ring.GeomSum
import ClassicalLean.Combinatorics.AlgebraicGeneratingFunction
import Mathlib.RingTheory.PowerSeries.Trunc

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

Order LEAN-37 (item 149 of the plan) adds the total-progeny series `T = X · f(T)` (a power series
in `X`; its `n`-th coefficient is the chance that the family has `n` members in all):

* `existsUnique_progeny`: the equation has exactly one power-series solution, for every `p`
  (through the library's functional-equation theorem, `ClassicalLean.IsLocal`);
* `progeny_eval_one_eq_extinctionChance`: for `p k ≥ 0` with `∑ p k = 1`, the coefficients of the
  solution sum to `extinctionChance p` (the plan's row asks `p 0 > 0`; with `p 0 = 0` both sides
  are `0`);
* `coeff_progeny_catalan`: for `f s = (1 + s²)/2` the odd coefficients are the Catalan numbers
  over powers of `2`, the even ones `0`, and they sum to `1`.

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

/-! ### Order LEAN-37, item 149: the total-progeny series -/

section Progeny

open PowerSeries

/-- Coefficientwise nonnegativity is closed under products. -/
private lemma coeff_mul_nonneg' {A B : ℝ⟦X⟧} (hA : ∀ n, 0 ≤ coeff n A)
    (hB : ∀ n, 0 ≤ coeff n B) (n : ℕ) : 0 ≤ coeff n (A * B) := by
  rw [coeff_mul]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hA _) (hB _)

/-- Coefficientwise nonnegativity is closed under powers. -/
private lemma coeff_pow_nonneg' {A : ℝ⟦X⟧} (hA : ∀ n, 0 ≤ coeff n A) (k : ℕ) :
    ∀ n, 0 ≤ coeff n (A ^ k) := by
  induction k with
  | zero => intro n; rw [pow_zero, coeff_one]; split_ifs <;> norm_num
  | succ k ih => intro n; rw [pow_succ]; exact coeff_mul_nonneg' ih hA n

/-- Powers are coefficientwise monotone on nonnegative series. -/
private lemma coeff_pow_mono' {A B : ℝ⟦X⟧} (hA : ∀ n, 0 ≤ coeff n A)
    (hAB : ∀ n, coeff n A ≤ coeff n B) (k : ℕ) :
    ∀ n, coeff n (A ^ k) ≤ coeff n (B ^ k) := by
  induction k with
  | zero => intro n; exact le_rfl
  | succ k ih =>
    intro n
    rw [pow_succ, pow_succ, coeff_mul, coeff_mul]
    exact Finset.sum_le_sum fun x _ =>
      mul_le_mul (ih _) (hAB _) (hA _) ((coeff_pow_nonneg' hA k _).trans (ih _))

/-- The `n`-th coefficient of a power depends only on coefficients up to `n`. -/
private lemma coeff_pow_eq_of_agree {A B : ℝ⟦X⟧} (n k : ℕ)
    (h : ∀ m ≤ n, coeff m A = coeff m B) : coeff n (A ^ k) = coeff n (B ^ k) :=
  ClassicalLean.isLocal_pow (ClassicalLean.isLocalId (R := ℝ)) k n A B h

private lemma coeff_pow_nonneg_of_le {T : ℝ⟦X⟧} (n k : ℕ) (h : ∀ m ≤ n, 0 ≤ coeff m T) :
    0 ≤ coeff n (T ^ k) := by
  rw [coeff_pow_eq_of_agree n k (B := PowerSeries.mk fun j => if j ≤ n then coeff j T else 0)
    fun j hj => by rw [coeff_mk, ite_eq_left hj]]
  refine coeff_pow_nonneg' (fun j => ?_) k n
  rw [coeff_mk]
  split_ifs with hj
  · exact h j hj
  · exact le_rfl

/-- The value at `1` of a polynomial is the sum of its coefficients. -/
private lemma eval_one_eq_sum (Q : Polynomial ℝ) {M : ℕ} (h : Q.natDegree < M) :
    Q.eval 1 = ∑ n ∈ Finset.range M, Q.coeff n := by
  rw [Polynomial.eval_eq_sum_range' h]
  simp

private lemma sum_coeff_le_eval_one (Q : Polynomial ℝ) (hQ : ∀ n, 0 ≤ Q.coeff n) (M : ℕ) :
    ∑ n ∈ Finset.range M, Q.coeff n ≤ Q.eval 1 := by
  rw [eval_one_eq_sum Q (M := max M (Q.natDegree + 1))
    (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _))]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun i hi => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) (le_max_left _ _)))
    fun i _ _ => hQ i

/-- **Total progeny and extinction.** If `T = X f(T)` as power series, the coefficients of `T`
sum to the least fixed point of `f` in `[0, 1]`. -/
theorem progeny_eval_one_eq_extinctionChance {p : ℕ → ℝ} (hp0 : ∀ k, 0 ≤ p k)
    (hp : HasSum p 1) (T : ℝ⟦X⟧)
    (hT : T = X * PowerSeries.mk (fun n => ∑' k, p k * coeff n (T ^ k))) :
    HasSum (fun n => coeff n T) (extinctionChance p) := by
  obtain ⟨U, hU⟩ : ∃ U, T = X * U := ⟨_, hT⟩
  have hzero : ∀ n k, n < k → coeff n (T ^ k) = 0 := by
    intro n k hnk
    rw [hU, mul_pow, coeff_X_pow_mul', ite_eq_right (by omega)]
  have h0 : coeff 0 T = 0 := by rw [hU]; simp
  have hrec : ∀ n, coeff (n + 1) T = ∑ k ∈ Finset.range (n + 1), p k * coeff n (T ^ k) := by
    intro n
    conv_lhs => rw [hT]
    rw [coeff_succ_X_mul, coeff_mk]
    exact tsum_eq_sum (s := Finset.range (n + 1)) fun k hk => by
      rw [hzero n k (by rw [Finset.mem_range] at hk; omega), mul_zero]
  have hnn : ∀ n, 0 ≤ coeff n T := by
    have key : ∀ n, ∀ m ≤ n, 0 ≤ coeff m T := by
      intro n
      induction n with
      | zero =>
        intro m hm
        obtain rfl : m = 0 := by omega
        exact h0.ge
      | succ n ih =>
        intro m hm
        rcases Nat.lt_or_ge m (n + 1) with h | h
        · exact ih m (by omega)
        · obtain rfl : m = n + 1 := by omega
          rw [hrec]
          exact Finset.sum_nonneg fun k _ => mul_nonneg (hp0 k) (coeff_pow_nonneg_of_le n k ih)
    exact fun n => key n n le_rfl
  have hdeg : ∀ N, (PowerSeries.trunc N T).natDegree ≤ N := fun N =>
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => by
      rw [coeff_trunc, ite_eq_right (by omega)]
  have hPc : ∀ N m, coeff m (↑(PowerSeries.trunc N T) : ℝ⟦X⟧)
      = if m < N then coeff m T else 0 := fun N m => by
    rw [Polynomial.coeff_coe, coeff_trunc]
  have hPnn' : ∀ N m, 0 ≤ coeff m (↑(PowerSeries.trunc N T) : ℝ⟦X⟧) := fun N m => by
    rw [hPc]; split_ifs
    · exact hnn m
    · exact le_rfl
  have hPnn : ∀ N k n, 0 ≤ ((PowerSeries.trunc N T) ^ k).coeff n := fun N k n => by
    rw [← Polynomial.coeff_coe, Polynomial.coe_pow]
    exact coeff_pow_nonneg' (hPnn' N) k n
  have hPe : ∀ N, (PowerSeries.trunc N T).eval 1 = ∑ n ∈ Finset.range N, coeff n T := by
    intro N
    rw [eval_one_eq_sum _ (M := N + 1) (Nat.lt_succ_of_le (hdeg N)), Finset.sum_range_succ,
      coeff_trunc, ite_eq_right (lt_irrefl N), add_zero]
    exact Finset.sum_congr rfl fun n hn => by rw [coeff_trunc, ite_eq_left (Finset.mem_range.mp hn)]
  have step : ∀ N, (∑ n ∈ Finset.range N, coeff n T) ∈ Icc (0 : ℝ) 1 →
      ∑ n ∈ Finset.range (N + 1), coeff n T ≤ pgf p (∑ n ∈ Finset.range N, coeff n T) := by
    intro N hSI
    calc ∑ n ∈ Finset.range (N + 1), coeff n T
        = ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (n + 1),
            p k * ((PowerSeries.trunc N T) ^ k).coeff n := by
          rw [Finset.sum_range_succ', h0, add_zero]
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [hrec]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← Polynomial.coeff_coe, Polynomial.coe_pow]
          congr 1
          refine coeff_pow_eq_of_agree n k fun m hm => ?_
          rw [hPc, ite_eq_left (by rw [Finset.mem_range] at hn; omega)]
      _ ≤ ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range N,
            p k * ((PowerSeries.trunc N T) ^ k).coeff n := by
          refine Finset.sum_le_sum fun n hn => ?_
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_
            fun k _ _ => mul_nonneg (hp0 k) (hPnn N k n)
          intro k hk
          rw [Finset.mem_range] at hk hn ⊢
          omega
      _ = ∑ k ∈ Finset.range N, p k * ∑ n ∈ Finset.range N,
            ((PowerSeries.trunc N T) ^ k).coeff n := by
          simp_rw [Finset.mul_sum]
          exact Finset.sum_comm
      _ ≤ ∑ k ∈ Finset.range N, p k * (∑ n ∈ Finset.range N, coeff n T) ^ k := by
          refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (hp0 k)
          rw [← hPe N, ← Polynomial.eval_pow]
          exact sum_coeff_le_eval_one _ (hPnn N k) N
      _ ≤ pgf p (∑ n ∈ Finset.range N, coeff n T) :=
          (summable_pgf hp0 hp hSI).sum_le_tsum _
            fun k _ => mul_nonneg (hp0 k) (pow_nonneg hSI.1 k)
  have hqI : extinctionChance p ∈ Icc (0 : ℝ) 1 := (isLeast_extinctionChance hp0 hp).1.1
  have hqfix : pgf p (extinctionChance p) = extinctionChance p :=
    (isLeast_extinctionChance hp0 hp).1.2
  have hS : ∀ N, ∑ n ∈ Finset.range N, coeff n T ≤ extinctionChance p := by
    intro N
    induction N with
    | zero => simpa using hqI.1
    | succ N ih =>
      have hSI : (∑ n ∈ Finset.range N, coeff n T) ∈ Icc (0 : ℝ) 1 :=
        ⟨Finset.sum_nonneg fun n _ => hnn n, ih.trans hqI.2⟩
      calc _ ≤ pgf p (∑ n ∈ Finset.range N, coeff n T) := step N hSI
        _ ≤ pgf p (extinctionChance p) := pgf_mono hp0 hp hSI hqI ih
        _ = extinctionChance p := hqfix
  have hsum : Summable (fun n => coeff n T) := summable_of_sum_range_le hnn hS
  have hSq : ∑' n, coeff n T ≤ extinctionChance p := Real.tsum_le_of_sum_range_le hnn hS
  have hSI : (∑' n, coeff n T) ∈ Icc (0 : ℝ) 1 := ⟨tsum_nonneg hnn, hSq.trans hqI.2⟩
  have lower : ∀ N K, ∑ k ∈ Finset.range K, p k * (∑ n ∈ Finset.range N, coeff n T) ^ k
      ≤ ∑' n, coeff n T := by
    intro N K
    calc ∑ k ∈ Finset.range K, p k * (∑ n ∈ Finset.range N, coeff n T) ^ k
        = ∑ k ∈ Finset.range K, p k * ∑ n ∈ Finset.range (K * N + 1),
            ((PowerSeries.trunc N T) ^ k).coeff n := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hdk : ((PowerSeries.trunc N T) ^ k).natDegree < K * N + 1 :=
            Nat.lt_succ_of_le (Polynomial.natDegree_pow_le.trans
              (Nat.mul_le_mul (Finset.mem_range.mp hk).le (hdeg N)))
          rw [← hPe N, ← Polynomial.eval_pow, eval_one_eq_sum _ hdk]
      _ ≤ ∑ k ∈ Finset.range K, p k * ∑ n ∈ Finset.range (K * N + 1), coeff n (T ^ k) := by
          refine Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => ?_) (hp0 k)
          rw [← Polynomial.coeff_coe, Polynomial.coe_pow]
          refine coeff_pow_mono' (hPnn' N) (fun m => ?_) k n
          rw [hPc]
          split_ifs
          · exact le_rfl
          · exact hnn m
      _ = ∑ n ∈ Finset.range (K * N + 1), ∑ k ∈ Finset.range K, p k * coeff n (T ^ k) := by
          simp_rw [Finset.mul_sum]
          exact Finset.sum_comm
      _ ≤ ∑ n ∈ Finset.range (K * N + 1), coeff (n + 1) T := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [hrec]
          have hg : ∀ k, 0 ≤ p k * coeff n (T ^ k) := fun k =>
            mul_nonneg (hp0 k) (coeff_pow_nonneg' hnn k n)
          calc ∑ k ∈ Finset.range K, p k * coeff n (T ^ k)
              ≤ ∑ k ∈ Finset.range (K + (n + 1)), p k * coeff n (T ^ k) :=
                Finset.sum_le_sum_of_subset_of_nonneg
                  (fun k hk => by rw [Finset.mem_range] at hk ⊢; omega) fun k _ _ => hg k
            _ = ∑ k ∈ Finset.range (n + 1), p k * coeff n (T ^ k) :=
                (Finset.sum_subset (fun k hk => by rw [Finset.mem_range] at hk ⊢; omega)
                  fun k _ hk => by
                    rw [hzero n k (by rw [Finset.mem_range] at hk; omega), mul_zero]).symm
      _ = ∑ n ∈ Finset.range (K * N + 1 + 1), coeff n T := by
          rw [Finset.sum_range_succ' _ (K * N + 1), h0, add_zero]
      _ ≤ ∑' n, coeff n T := sum_le_hasSum _ (fun i _ => hnn i) hsum.hasSum
  have hfS : pgf p (∑' n, coeff n T) ≤ ∑' n, coeff n T := by
    change ∑' k, p k * (∑' n, coeff n T) ^ k ≤ ∑' n, coeff n T
    refine Real.tsum_le_of_sum_range_le
      (fun k => mul_nonneg (hp0 k) (pow_nonneg hSI.1 k)) fun K => ?_
    have ht : Tendsto (fun N => ∑ k ∈ Finset.range K,
        p k * (∑ n ∈ Finset.range N, coeff n T) ^ k) atTop
        (𝓝 (∑ k ∈ Finset.range K, p k * (∑' n, coeff n T) ^ k)) :=
      tendsto_finsetSum _ fun k _ => (hsum.hasSum.tendsto_sum_nat.pow k).const_mul (p k)
    exact le_of_tendsto' ht fun N => lower N K
  have hqS : extinctionChance p ≤ ∑' n, coeff n T :=
    le_of_tendsto' (tendsto_iterate_zero hp0 hp) (iterate_zero_le hp0 hp hSI hfS)
  have := hsum.hasSum
  rwa [le_antisymm hSq hqS] at this

/-! ### Existence and uniqueness of the progeny series -/

/-- The operator `T ↦ f(T)`, coefficientwise `∑' k, p k * coeff n (T ^ k)`. -/
private noncomputable def progenyOp (p : ℕ → ℝ) (T : ℝ⟦X⟧) : ℝ⟦X⟧ :=
  PowerSeries.mk fun n => ∑' k, p k * coeff n (T ^ k)

/-- The operator is local: coefficient `n` of `f(T)` depends on coefficients of `T` up to `n`. -/
private lemma isLocal_progenyOp (p : ℕ → ℝ) : ClassicalLean.IsLocal (progenyOp p) := by
  intro n a b h
  simp only [progenyOp, coeff_mk]
  exact tsum_congr fun k => by rw [coeff_pow_eq_of_agree n k h]

/-- The iterates `T₀ = 0`, `T_{N+1} = X f(T_N)`. -/
private noncomputable def progenyApprox (p : ℕ → ℝ) : ℕ → ℝ⟦X⟧
  | 0 => 0
  | N + 1 => X * progenyOp p (progenyApprox p N)

private lemma approx_succ (p : ℕ → ℝ) (N : ℕ) :
    progenyApprox p (N + 1) = X * progenyOp p (progenyApprox p N) := rfl

/-- Consecutive iterates agree below `N`. -/
private lemma approx_stab (p : ℕ → ℝ) : ∀ N m, m < N →
    coeff m (progenyApprox p N) = coeff m (progenyApprox p (N + 1)) := by
  intro N
  induction N with
  | zero => intro m hm; omega
  | succ N ih =>
    intro m hm
    rcases m with _ | j
    · simp only [approx_succ, coeff_zero_X_mul]
    · rw [approx_succ p N, approx_succ p (N + 1), coeff_succ_X_mul, coeff_succ_X_mul]
      exact isLocal_progenyOp p j _ _ fun i hi => ih i (by omega)

/-- Coefficient `n` is fixed from the iterate `n + 1` on. -/
private lemma approx_stable (p : ℕ → ℝ) (n : ℕ) : ∀ N, n + 1 ≤ N →
    coeff n (progenyApprox p N) = coeff n (progenyApprox p (n + 1)) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih => exact (approx_stab p N n (by omega)).symm.trans ih

/-- The limit of the iterates. -/
private noncomputable def progenyLimit (p : ℕ → ℝ) : ℝ⟦X⟧ :=
  PowerSeries.mk fun n => coeff n (progenyApprox p (n + 1))

private lemma coeff_progenyLimit (p : ℕ → ℝ) (n : ℕ) :
    coeff n (progenyLimit p) = coeff n (progenyApprox p (n + 1)) := coeff_mk _ _

private lemma progenyLimit_eq (p : ℕ → ℝ) :
    progenyLimit p = X * progenyOp p (progenyLimit p) := by
  ext n
  rcases n with _ | j
  · rw [coeff_zero_X_mul, coeff_progenyLimit, approx_succ, coeff_zero_X_mul]
  · rw [coeff_succ_X_mul, coeff_progenyLimit, approx_succ, coeff_succ_X_mul]
    exact isLocal_progenyOp p j _ _ fun i hi => by
      rw [coeff_progenyLimit]; exact approx_stable p i (j + 1) (by omega)

/-- **The progeny equation has exactly one solution.** For every sequence `p`, exactly one power
series satisfies `T = X f(T)`; each `∑'` is a finite sum since `T` has no constant term. -/
theorem existsUnique_progeny (p : ℕ → ℝ) :
    ∃! T : ℝ⟦X⟧, T = X * PowerSeries.mk (fun n => ∑' k, p k * coeff n (T ^ k)) := by
  refine ⟨progenyLimit p, progenyLimit_eq p, fun U hU => ?_⟩
  refine ClassicalLean.eq_of_eq_C_add_X_mul (isLocal_progenyOp p) 0 U (progenyLimit p) ?_ ?_
  · rw [map_zero, zero_add]; exact hU
  · rw [map_zero, zero_add]; exact progenyLimit_eq p

/-! ### The law `(1/2, 0, 1/2)`: Catalan numbers -/

/-- The law with `f s = (1 + s²)/2`. -/
private noncomputable def catalanLaw (k : ℕ) : ℝ := if k = 0 ∨ k = 2 then 1 / 2 else 0

/-- The embedding `(a, b) ↦ (2a + 1, 2b + 1)`. -/
private def oddEmb : ℕ × ℕ ↪ ℕ × ℕ :=
  ⟨fun x => (2 * x.1 + 1, 2 * x.2 + 1), fun x y h => by
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    exact Prod.ext (by omega) (by omega)⟩

/-- When the even coefficients vanish, the convolution at `2k + 2` only sees odd pairs. -/
private lemma sum_antidiagonal_odd (T : ℝ⟦X⟧) (hf : ∀ i, coeff (2 * i) T = 0) (k : ℕ) :
    ∑ x ∈ Finset.antidiagonal (2 * k + 2), coeff x.1 T * coeff x.2 T
      = ∑ x ∈ Finset.antidiagonal k, coeff (2 * x.1 + 1) T * coeff (2 * x.2 + 1) T := by
  have hmap : ∑ x ∈ Finset.antidiagonal k, coeff (2 * x.1 + 1) T * coeff (2 * x.2 + 1) T
      = ∑ x ∈ (Finset.antidiagonal k).map oddEmb, coeff x.1 T * coeff x.2 T :=
    (Finset.sum_map (Finset.antidiagonal k) oddEmb fun x => coeff x.1 T * coeff x.2 T).symm
  rw [hmap]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    have hy' : y.1 + y.2 = k := Finset.mem_antidiagonal.mp hy
    exact Finset.mem_antidiagonal.mpr (by change 2 * y.1 + 1 + (2 * y.2 + 1) = 2 * k + 2; omega)
  · rintro ⟨i, j⟩ hx hnot
    have hx' : i + j = 2 * k + 2 := Finset.mem_antidiagonal.mp hx
    change coeff i T * coeff j T = 0
    rcases Nat.even_or_odd' i with ⟨a, ha | ha⟩
    · rw [ha, hf, zero_mul]
    · exfalso
      obtain ⟨b, hb⟩ : ∃ b, j = 2 * b + 1 := ⟨j / 2, by omega⟩
      exact hnot (Finset.mem_map.mpr ⟨(a, b),
        Finset.mem_antidiagonal.mpr (by change a + b = k; omega), by subst ha hb; rfl⟩)

/-- **Catalan numbers.** For `f s = (1 + s²)/2`, the solution of `T = X f(T)` has
`coeff (2n+1) T = C_n / 2^(2n+1)`, vanishing even coefficients, and coefficients summing to `1`. -/
theorem coeff_progeny_catalan (T : ℝ⟦X⟧)
    (hT : T = X * PowerSeries.mk (fun n =>
      ∑' k, (if k = 0 ∨ k = 2 then (1 / 2 : ℝ) else 0) * coeff n (T ^ k))) :
    (∀ n, coeff (2 * n + 1) T = (catalan n : ℝ) / 2 ^ (2 * n + 1)) ∧
      (∀ n, coeff (2 * n) T = 0) ∧ HasSum (fun n => coeff n T) 1 := by
  -- the quadratic form `T = X (1/2 + T²/2)`
  have hop : PowerSeries.mk (fun n =>
      ∑' k, (if k = 0 ∨ k = 2 then (1 / 2 : ℝ) else 0) * coeff n (T ^ k))
      = C (1 / 2 : ℝ) + C (1 / 2 : ℝ) * T ^ 2 := by
    ext n
    rw [coeff_mk, tsum_eq_sum (s := ({0, 2} : Finset ℕ)) (fun k hk => by
        rw [ite_eq_right (show ¬(k = 0 ∨ k = 2) by simpa using hk), zero_mul]),
      Finset.sum_pair (show (0 : ℕ) ≠ 2 by norm_num)]
    by_cases hn : n = 0 <;> simp [hn, coeff_one, coeff_C]
  have hT2 : T = X * (C (1 / 2 : ℝ) + C (1 / 2 : ℝ) * T ^ 2) := by
    rw [← hop]; exact hT
  have hloc : ClassicalLean.IsLocal (fun f : ℝ⟦X⟧ => C (1 / 2 : ℝ) + C (1 / 2 : ℝ) * f ^ 2) :=
    ClassicalLean.isLocal_add (ClassicalLean.isLocal_const _)
      (ClassicalLean.isLocal_mul (ClassicalLean.isLocal_const _)
        (ClassicalLean.isLocal_pow ClassicalLean.isLocalId 2))
  -- `T` is odd: `-T(-X)` solves the same equation
  have hRX : rescale (-1 : ℝ) X = -X := by
    ext n
    rw [coeff_rescale, map_neg, coeff_X]
    split_ifs with h
    · subst h; norm_num
    · simp
  have hRC : ∀ c : ℝ, rescale (-1 : ℝ) (C c) = C c := by
    intro c
    ext n
    rw [coeff_rescale, coeff_C]
    split_ifs with h
    · subst h; simp
    · simp
  have hR : rescale (-1 : ℝ) T
      = -X * (C (1 / 2 : ℝ) + C (1 / 2 : ℝ) * (rescale (-1 : ℝ) T) ^ 2) := by
    conv_lhs => rw [hT2]
    rw [map_mul, map_add, map_mul, map_pow, hRX, hRC]
  have hneg : -rescale (-1 : ℝ) T
      = X * (C (1 / 2 : ℝ) + C (1 / 2 : ℝ) * (-rescale (-1 : ℝ) T) ^ 2) := by
    linear_combination (-1 : ℝ⟦X⟧) * hR
  have huniq : -rescale (-1 : ℝ) T = T :=
    ClassicalLean.eq_of_eq_C_add_X_mul hloc 0 _ _
      (by rw [map_zero, zero_add]; exact hneg) (by rw [map_zero, zero_add]; exact hT2)
  have hodd : ∀ i, coeff (2 * i) T = 0 := by
    intro i
    have h : coeff (2 * i) (-rescale (-1 : ℝ) T) = coeff (2 * i) T := by rw [huniq]
    rw [map_neg, coeff_rescale, pow_mul, neg_one_sq, one_pow, one_mul] at h
    linarith
  have h0 : coeff 0 T = 0 := by simpa using hodd 0
  -- the coefficient recursion
  have hrec : ∀ n, coeff (n + 1) T = (if n = 0 then (1 / 2 : ℝ) else 0)
      + 1 / 2 * ∑ x ∈ Finset.antidiagonal n, coeff x.1 T * coeff x.2 T := by
    intro n
    conv_lhs => rw [hT2]
    rw [coeff_succ_X_mul, map_add, coeff_C, coeff_C_mul, sq, coeff_mul]
  have hcat : ∀ k, coeff (2 * k + 1) T = (catalan k : ℝ) / 2 ^ (2 * k + 1) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases k with _ | k
      · have hz : ∑ x ∈ Finset.antidiagonal 0, coeff x.1 T * coeff x.2 T = 0 :=
          Finset.sum_eq_zero fun x hx => by
            have : x.1 = 0 := by have := Finset.mem_antidiagonal.mp hx; omega
            rw [this, h0, zero_mul]
        change coeff (0 + 1) T = _
        rw [hrec 0, hz, ite_eq_left rfl, catalan_zero]
        norm_num
      · have hs : ∑ x ∈ Finset.antidiagonal k, coeff (2 * x.1 + 1) T * coeff (2 * x.2 + 1) T
            = ∑ x ∈ Finset.antidiagonal k,
                (catalan x.1 : ℝ) * catalan x.2 / 2 ^ (2 * k + 2) := by
          refine Finset.sum_congr rfl fun x hx => ?_
          have hx' := Finset.mem_antidiagonal.mp hx
          rw [ih x.1 (by omega), ih x.2 (by omega), div_mul_div_comm, ← pow_add,
            show 2 * x.1 + 1 + (2 * x.2 + 1) = 2 * k + 2 by omega]
        rw [show 2 * (k + 1) + 1 = 2 * k + 2 + 1 by ring, hrec (2 * k + 2),
          ite_eq_right (show ¬(2 * k + 2 = 0) by omega), zero_add, sum_antidiagonal_odd T hodd k,
          hs]
        simp only [div_eq_mul_inv]
        rw [← Finset.sum_mul, catalan_succ']
        push_cast
        ring
  -- the coefficients sum to the extinction chance, which is `1`
  have hq0 : ∀ k, 0 ≤ catalanLaw k := fun k => by
    unfold catalanLaw; split_ifs <;> norm_num
  have hsupp : ∀ k ∉ ({0, 2} : Finset ℕ), catalanLaw k = 0 := fun k hk => by
    rw [catalanLaw, ite_eq_right (show ¬(k = 0 ∨ k = 2) by simpa using hk)]
  have hq : HasSum catalanLaw 1 := by
    have h02 : catalanLaw 0 + catalanLaw 2 = 1 := by norm_num [catalanLaw]
    have hfin : HasSum catalanLaw (∑ k ∈ ({0, 2} : Finset ℕ), catalanLaw k) :=
      hasSum_sum_of_ne_finset_zero hsupp
    rwa [Finset.sum_pair (show (0 : ℕ) ≠ 2 by norm_num), h02] at hfin
  have hpgf : ∀ s, pgf catalanLaw s = 1 / 2 + 1 / 2 * s ^ 2 := by
    intro s
    rw [pgf, tsum_eq_sum (s := ({0, 2} : Finset ℕ)) (fun k hk => by rw [hsupp k hk, zero_mul]),
      Finset.sum_pair (show (0 : ℕ) ≠ 2 by norm_num)]
    norm_num [catalanLaw]
  have hext : extinctionChance catalanLaw = 1 := by
    obtain ⟨⟨hI, hfix⟩, -⟩ := isLeast_extinctionChance hq0 hq
    rw [hpgf] at hfix
    have h2 : (extinctionChance catalanLaw - 1) ^ 2 = 0 := by nlinarith
    have h3 := (pow_eq_zero_iff two_ne_zero).mp h2
    linarith
  have hsum := progeny_eval_one_eq_extinctionChance hq0 hq T hT
  rw [hext] at hsum
  exact ⟨hcat, hodd, hsum⟩

end Progeny

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

/-- The hypotheses of `progeny_eval_one_eq_extinctionChance` hold together: the offspring law with
chance `1/4` of no child, `1/4` of one and `1/2` of two (mean `5/4`), nonnegative and summing to
`1`, as in the witness of `tendsto_iterate_zero`; `T` is the progeny series, the solution
`existsUnique_progeny` gives (`Classical.choose`), and `hT` its defining equation
(`Classical.choose_spec`). `p 0 > 0` and `p` is not a point mass, so the progeny series has
infinitely many nonzero coefficients (`1/4`, `1/16`, `3/64`, `7/256`, …; all of the first 80
nonzero, in exact fractions, `~/lean/lean37-checks/w149/series.py`) and its sum is the extinction
chance `1/2`, strictly between `0` and `1`. -/
example := ClassicalLean.Probability.Extinction.progeny_eval_one_eq_extinctionChance
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
  (T := Classical.choose (ClassicalLean.Probability.Extinction.existsUnique_progeny _).exists)
  (hT := Classical.choose_spec (ClassicalLean.Probability.Extinction.existsUnique_progeny _).exists)

/-- The hypotheses of `coeff_progeny_catalan` hold together: `T` is the progeny series of the law `p
k = 1/2` for `k = 0` and `k = 2`, `0` otherwise (written as in the theorem's hypothesis), the
solution `existsUnique_progeny` gives (`Classical.choose`), and `hT` its defining equation
(`Classical.choose_spec`); `existsUnique_progeny` does not rest on this theorem. What moves: the odd
coefficients are the Catalan numbers over powers of `2`, `1/2`, `1/8`, `2/32`, …, all positive
(checked to degree 80 in `~/lean/lean37-checks/w149/series.py`). -/
example := ClassicalLean.Probability.Extinction.coeff_progeny_catalan
  (T := Classical.choose (ClassicalLean.Probability.Extinction.existsUnique_progeny
    (fun k ↦ if k = 0 ∨ k = 2 then 1 / 2 else 0)).exists)
  (hT := Classical.choose_spec (ClassicalLean.Probability.Extinction.existsUnique_progeny
    (fun k ↦ if k = 0 ∨ k = 2 then 1 / 2 else 0)).exists)
