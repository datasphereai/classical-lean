/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Independence.Integration

/-!
# Many tests at once from e-values, under any dependence

There are `m` tests, each with an e-value `e j`, and a level `q > 0`. The procedure (e-BH, Wang
and Ramdas 2022) finds the largest `k ≤ m` such that at least `k` of the e-values are at least
`m / (q k)` (`eNumRej`, `0` if there is none), and rejects every test whose e-value is at least
`m / (q · eNumRej)`, provided `eNumRej ≥ 1`.

* `card_eRejected`: exactly `eNumRej q e` tests are rejected.
* `eFalseShare_le`: for every outcome, the share of the rejections that fall in a set `H` (the
  true nulls) is at most `q / m · ∑ i ∈ H, e i`, when `e i ≥ 0` for `i ∈ H`. Tests outside `H`
  may have any sign.
* `integral_eFalseShare_le`: so for random e-values `E i`, nonnegative, integrable and with mean
  at most `1` on `H`, the mean share of false finds is at most `q · |H| / m`. Nothing is assumed
  about how the e-values depend on each other.

Each hypothesis is needed. Mean at most `1`: one test with `e = 4` always and `q = 1/4` is
rejected every time, a false share of `1 > 1/4`. `e ≥ 0` on `H`: `e = (100, -100)`, both null,
`q = 1/2`, gives false share `1 > 0`. `q > 0`: with `q = -1` and `e = (-3/2, -1/2)`, Lean's
`x / 0 = 0` makes `eNumRej = 1` but rejects both tests. The condition `eNumRej ≥ 1` in the rule
is needed for the exact count, because `m / (q · 0) = 0` in Lean: without it, `e = 1/2`, `m = 1`,
`q = 1/10` rejects one test while `eNumRej = 0`. Do not turn e-values into p-values as `1 / e`:
`1 / 0 = 0` would reject an e-value of `0`.

`eNumRejQ` computes `eNumRej` over `ℚ`; `cast_eNumRejQ` says the two agree.

Pooling e-values. `integral_average_le_one`: the average of e-values is an e-value, whatever their
dependence. `integral_prod_le_one_of_iIndepFun`: the product of mutually independent nonnegative
e-values is an e-value, and `integrable_prod_of_iIndepFun` makes the product integrable. E-values
computed from overlapping data need not be independent; without a proof of independence, only the
average applies.
Independence is needed for the product: a variable taking `0` or `2` with chance `1/2` each, used
twice, has product mean `2`; nonnegativity is needed too: the constants `-2` and `-2` have product
`4`. E-values taken one after another (adapted, nonnegative, bounded above, each with conditional
mean at most `1` given the past) already multiply into `NoEdgeWealth.supermartingale_wealth`:
write each as `1 + 1 · (E - 1)`, with `c = 1`.

## What Mathlib provides

`Nat.findGreatest` and its lemmas, `integral_mono_of_nonneg`, `integral_finsetSum`,
`integrable_finsetSum`, `iIndepFun.integral_fun_prod_eq_prod_integral`, `IndepFun.integrable_mul`
and `iIndepFun.indepFun_finsetProd_of_notMem`. Mathlib has no multiple-testing procedure.
-/

open Finset MeasureTheory

namespace ClassicalLean.Probability.EValueStepUp

variable {ι : Type*} [Fintype ι]

/-- How many of the values `e j` are at least `c`. -/
noncomputable def countGE (e : ι → ℝ) (c : ℝ) : ℕ :=
  (univ.filter fun j ↦ c ≤ e j).card

/-- The number of rejections of e-BH at level `q`: the largest `k ≤ m` with at least `k` of the
e-values at least `m / (q k)`, and `0` if there is none. -/
noncomputable def eNumRej (q : ℝ) (e : ι → ℝ) : ℕ :=
  Nat.findGreatest (fun k ↦ k ≤ countGE e (Fintype.card ι / (q * k))) (Fintype.card ι)

/-- The rejected tests: those whose e-value is at least `m / (q · eNumRej)`, when `eNumRej ≥ 1`. -/
noncomputable def eRejected (q : ℝ) (e : ι → ℝ) : Finset ι :=
  univ.filter fun j ↦ 1 ≤ eNumRej q e ∧ (Fintype.card ι : ℝ) / (q * eNumRej q e) ≤ e j

theorem countGE_le_card (e : ι → ℝ) (c : ℝ) : countGE e c ≤ Fintype.card ι :=
  (card_filter_le _ _).trans_eq card_univ

theorem countGE_anti (e : ι → ℝ) {c d : ℝ} (h : c ≤ d) : countGE e d ≤ countGE e c :=
  card_le_card fun j hj ↦ by
    simp only [mem_filter, mem_univ, true_and] at hj ⊢; linarith

theorem eNumRej_le_card (q : ℝ) (e : ι → ℝ) : eNumRej q e ≤ Fintype.card ι :=
  Nat.findGreatest_le _

theorem eNumRej_le_countGE (q : ℝ) (e : ι → ℝ) :
    eNumRej q e ≤ countGE e (Fintype.card ι / (q * eNumRej q e)) :=
  Nat.findGreatest_spec (P := fun k ↦ k ≤ countGE e (Fintype.card ι / (q * k)))
    (Nat.zero_le _) (Nat.zero_le _)

theorem le_eNumRej {q : ℝ} {e : ι → ℝ} {k : ℕ} (hk : k ≤ Fintype.card ι)
    (h : k ≤ countGE e (Fintype.card ι / (q * k))) : k ≤ eNumRej q e :=
  Nat.le_findGreatest hk h

theorem eRejected_eq_empty {q : ℝ} {e : ι → ℝ} (h : eNumRej q e = 0) : eRejected q e = ∅ := by
  ext j; simp [eRejected, h]

theorem card_eRejected_of_pos {q : ℝ} {e : ι → ℝ} (h : 1 ≤ eNumRej q e) :
    (eRejected q e).card = countGE e (Fintype.card ι / (q * eNumRej q e)) := by
  unfold eRejected countGE
  congr 1
  ext j
  simp [h]

/-- **Exactly `eNumRej q e` tests are rejected**, for `q > 0`. -/
theorem card_eRejected {q : ℝ} (hq : 0 < q) (e : ι → ℝ) :
    (eRejected q e).card = eNumRej q e := by
  set R := eNumRej q e with hR
  rcases Nat.eq_zero_or_pos R with h0 | hpos
  · rw [eRejected_eq_empty h0, h0, card_empty]
  rw [card_eRejected_of_pos hpos]
  set k := countGE e (Fintype.card ι / (q * R)) with hk
  have hRk : R ≤ k := eNumRej_le_countGE q e
  refine le_antisymm ?_ hRk
  by_contra hle
  have hlt := not_le.mp hle
  have hkm : k ≤ Fintype.card ι := countGE_le_card e _
  have hthr : (Fintype.card ι : ℝ) / (q * k) ≤ Fintype.card ι / (q * R) := by
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
    · exact mul_pos hq (by exact_mod_cast hpos)
    · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hlt.le) hq.le
  have hP : k ≤ countGE e (Fintype.card ι / (q * k)) := hk ▸ countGE_anti e hthr
  have := le_eNumRej hkm hP
  omega

section share

variable [DecidableEq ι]

/-- The share of the rejections that fall in `H`, and `0` when nothing is rejected. -/
noncomputable def eFalseShare (q : ℝ) (H : Finset ι) (e : ι → ℝ) : ℝ :=
  ((H ∩ eRejected q e).card : ℝ) / eNumRej q e

/-- **The false share, outcome by outcome.** For `q > 0` and `e i ≥ 0` on `H`, the share of the
rejections that fall in `H` is at most `q / m · ∑ i ∈ H, e i`. -/
theorem eFalseShare_le {q : ℝ} (hq : 0 < q) (H : Finset ι) {e : ι → ℝ}
    (he : ∀ i ∈ H, 0 ≤ e i) :
    eFalseShare q H e ≤ q / Fintype.card ι * ∑ i ∈ H, e i := by
  have hsum : 0 ≤ ∑ i ∈ H, e i := sum_nonneg he
  have hrhs : 0 ≤ q / Fintype.card ι * ∑ i ∈ H, e i :=
    mul_nonneg (div_nonneg hq.le (Nat.cast_nonneg _)) hsum
  set R := eNumRej q e with hR
  rcases Nat.eq_zero_or_pos R with h0 | hpos
  · simp [eFalseShare, ← hR, h0, hrhs]
  have hm : 0 < Fintype.card ι := lt_of_lt_of_le hpos (eNumRej_le_card q e)
  have hmR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hm
  have hRR : (0 : ℝ) < R := by exact_mod_cast hpos
  have hshare : eFalseShare q H e = ∑ _j ∈ H ∩ eRejected q e, (1 / (R : ℝ)) := by
    rw [sum_const, nsmul_eq_mul, eFalseShare, ← hR]; ring
  rw [hshare]
  calc ∑ _j ∈ H ∩ eRejected q e, (1 / (R : ℝ))
      ≤ ∑ j ∈ H ∩ eRejected q e, q / Fintype.card ι * e j := by
        refine sum_le_sum fun j hj ↦ ?_
        have hj' := (mem_filter.mp (mem_inter.mp hj).2).2.2
        rw [← hR] at hj'
        have h1 : 1 / (R : ℝ) = q / Fintype.card ι * (Fintype.card ι / (q * R)) := by
          field_simp
        rw [h1]
        exact mul_le_mul_of_nonneg_left hj' (div_nonneg hq.le hmR.le)
    _ ≤ ∑ j ∈ H, q / Fintype.card ι * e j :=
        sum_le_sum_of_subset_of_nonneg inter_subset_left fun j hj _ ↦
          mul_nonneg (div_nonneg hq.le hmR.le) (he j hj)
    _ = q / Fintype.card ι * ∑ i ∈ H, e i := by rw [mul_sum]

/-- **The mean false share, under any dependence.** For random e-values `E i`, nonnegative,
integrable and with mean at most `1` for every `i ∈ H`, and `q > 0`, the mean share of the
rejections that fall in `H` is at most `q · |H| / m`. -/
theorem integral_eFalseShare_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {q : ℝ}
    (hq : 0 < q) (H : Finset ι) {E : ι → Ω → ℝ} (hE0 : ∀ i ∈ H, ∀ ω, 0 ≤ E i ω)
    (hEint : ∀ i ∈ H, Integrable (E i) μ) (hE1 : ∀ i ∈ H, ∫ ω, E i ω ∂μ ≤ 1) :
    ∫ ω, eFalseShare q H (fun i ↦ E i ω) ∂μ ≤ q * H.card / Fintype.card ι := by
  have hc : 0 ≤ q / Fintype.card ι := div_nonneg hq.le (Nat.cast_nonneg _)
  calc ∫ ω, eFalseShare q H (fun i ↦ E i ω) ∂μ
      ≤ ∫ ω, q / Fintype.card ι * ∑ i ∈ H, E i ω ∂μ := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun ω ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          ((integrable_finsetSum H hEint).const_mul _)
          (Filter.Eventually.of_forall fun ω ↦ eFalseShare_le hq H fun i hi ↦ hE0 i hi ω)
    _ = q / Fintype.card ι * ∑ i ∈ H, ∫ ω, E i ω ∂μ := by
        rw [integral_const_mul, integral_finsetSum H hEint]
    _ ≤ q / Fintype.card ι * ∑ _i ∈ H, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (sum_le_sum hE1) hc
    _ = q * H.card / Fintype.card ι := by
        rw [sum_const, nsmul_eq_mul, mul_one]; ring

end share

/-! ### A computable count over `ℚ` -/

/-- How many of the rational values `e j` are at least `c`. -/
def countGEQ (e : ι → ℚ) (c : ℚ) : ℕ :=
  (univ.filter fun j ↦ c ≤ e j).card

/-- `eNumRej` over `ℚ`. -/
def eNumRejQ (q : ℚ) (e : ι → ℚ) : ℕ :=
  Nat.findGreatest (fun k ↦ k ≤ countGEQ e (Fintype.card ι / (q * k))) (Fintype.card ι)

theorem countGEQ_eq (e : ι → ℚ) (c : ℚ) :
    countGEQ e c = countGE (fun i ↦ (e i : ℝ)) (c : ℝ) := by
  unfold countGEQ countGE
  congr 1
  ext j
  simp

/-- `eNumRejQ` equals `eNumRej` of the cast values. -/
theorem cast_eNumRejQ (q : ℚ) (e : ι → ℚ) :
    eNumRejQ q e = eNumRej (q : ℝ) (fun i ↦ (e i : ℝ)) := by
  have hP : ∀ k : ℕ, (k ≤ countGEQ e (Fintype.card ι / (q * k))) ↔
      (k ≤ countGE (fun i ↦ (e i : ℝ)) (Fintype.card ι / ((q : ℝ) * k))) := by
    intro k
    rw [countGEQ_eq]
    push_cast
    rfl
  unfold eNumRejQ eNumRej
  refine le_antisymm (Nat.le_findGreatest (Nat.findGreatest_le _) ?_)
    (Nat.le_findGreatest (Nat.findGreatest_le _) ?_)
  · exact (hP _).mp (Nat.findGreatest_spec (P := fun k ↦ k ≤ countGEQ e (Fintype.card ι / (q * k)))
      (Nat.zero_le _) (Nat.zero_le _))
  · exact (hP _).mpr (Nat.findGreatest_spec
      (P := fun k ↦ k ≤ countGE (fun i ↦ (e i : ℝ)) (Fintype.card ι / ((q : ℝ) * k)))
      (Nat.zero_le _) (Nat.zero_le _))

/-! ### Pooling e-values -/

section pooling

open ProbabilityTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- The average of e-values is an e-value, whatever their dependence: integrable, each with mean at
most `1`, so their average has mean at most `1`. -/
theorem integral_average_le_one {ι : Type*} [Fintype ι] {E : ι → Ω → ℝ}
    (hint : ∀ i, Integrable (E i) μ) (hle : ∀ i, ∫ ω, E i ω ∂μ ≤ 1) :
    ∫ ω, (∑ i, E i ω) / Fintype.card ι ∂μ ≤ 1 := by
  rw [integral_div, integral_finsetSum _ fun i _ ↦ hint i]
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hk | hk
  · simp [hk]
  · have hkpos : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr hk
    rw [div_le_one hkpos]
    calc ∑ i, ∫ ω, E i ω ∂μ ≤ ∑ _i : ι, (1 : ℝ) := sum_le_sum fun i _ ↦ hle i
      _ = Fintype.card ι := by simp

/-- The product of independent integrable functions is integrable. -/
theorem integrable_prod_of_iIndepFun {ι : Type*} [Fintype ι] {E : ι → Ω → ℝ}
    (hind : iIndepFun E μ) (hm : ∀ i, Measurable (E i)) (hint : ∀ i, Integrable (E i) μ) :
    Integrable (fun ω ↦ ∏ i, E i ω) μ := by
  have := hind.isProbabilityMeasure
  classical
  have key : ∀ s : Finset ι, Integrable (fun ω ↦ ∏ i ∈ s, E i ω) μ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      have hindep := hind.indepFun_finsetProd_of_notMem hm ha
      have ih' : Integrable (∏ j ∈ s, E j) μ :=
        ih.congr (Filter.Eventually.of_forall fun ω ↦ (Finset.prod_apply ω s E).symm)
      have h := hindep.integrable_mul ih' (hint a)
      refine h.congr (Filter.Eventually.of_forall fun ω ↦ ?_)
      simp [Finset.prod_insert ha, Finset.prod_apply, mul_comm]
  exact key univ

/-- The product of independent nonnegative e-values is an e-value: its integral is at most `1`.
With each `E i` integrable, the product is integrable (`integrable_prod_of_iIndepFun`) and this is
its mean; integrability is not assumed here, and Lean's integral of a non-integrable function is
`0`. -/
theorem integral_prod_le_one_of_iIndepFun {ι : Type*} [Fintype ι] {E : ι → Ω → ℝ}
    (hind : iIndepFun E μ) (hm : ∀ i, Measurable (E i)) (h0 : ∀ i ω, 0 ≤ E i ω)
    (hle : ∀ i, ∫ ω, E i ω ∂μ ≤ 1) :
    ∫ ω, ∏ i, E i ω ∂μ ≤ 1 := by
  rw [hind.integral_fun_prod_eq_prod_integral fun i ↦ (hm i).aestronglyMeasurable]
  exact prod_le_one₀ (fun i _ ↦ integral_nonneg (h0 i)) fun i _ ↦ hle i

end pooling

end ClassicalLean.Probability.EValueStepUp
