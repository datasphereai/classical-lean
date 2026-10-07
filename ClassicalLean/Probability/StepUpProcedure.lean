/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The step-up procedure of Benjamini and Hochberg

There are `m` tests with p-values `x j` and a level `q ≥ 0`. The procedure finds the largest
`k ≤ m` such that at least `k` of the p-values are at most `q k / m` (`numRej`, `0` if there is
none), and rejects every test whose p-value is at most `q · numRej / m`.

* `countLE_numRej`: exactly `numRej` tests are rejected.
* `numRej_update_eq_of_le`, `numRej_eq_of_le_update`: a rejected p-value can be set to `0` without
  changing the number of rejections, and conversely. This is the counting fact behind the proof.
* `falseShare_eq_sum`: so the share of rejections that are true nulls splits into one term per
  null test and per possible count `k`.
* `integral_falseShare_le`: for independent p-values, those of the true nulls satisfying
  `P(p ≤ t) ≤ t`, the expected share of false finds is at most `q m₀ / m ≤ q`, with `m₀` the
  number of true nulls.

## What Mathlib provides

`iIndepFun.indepFun_finset` (one p-value is independent of the others), `IndepFun.comp`,
`IndepFun.measure_inter_preimage_eq_mul`, `integral_indicator_const`, `measureReal_biUnion_finset`,
`measurable_to_countable'`. Mathlib has no multiple-testing procedure.
-/

open Finset MeasureTheory ProbabilityTheory

namespace ClassicalLean.Probability.StepUpProcedure

variable {ι : Type*} [Fintype ι]

/-- How many of the values `x j` are at most `c`. -/
noncomputable def countLE (x : ι → ℝ) (c : ℝ) : ℕ :=
  (univ.filter fun j ↦ x j ≤ c).card

/-- The ranks `k ≤ m` with at least `k` values at most `q k / m`. -/
noncomputable def passing (q : ℝ) (x : ι → ℝ) : Finset ℕ :=
  (range (Fintype.card ι + 1)).filter fun k ↦ k ≤ countLE x (q * k / Fintype.card ι)

theorem zero_mem_passing (q : ℝ) (x : ι → ℝ) : 0 ∈ passing q x := by
  simp [passing]

/-- The number of rejections of the step-up procedure at level `q`: the largest `k ≤ m` with at
least `k` of the values at most `q k / m`, and `0` if there is none. -/
noncomputable def numRej (q : ℝ) (x : ι → ℝ) : ℕ :=
  (passing q x).max' ⟨0, zero_mem_passing q x⟩

theorem countLE_mono (x : ι → ℝ) {c d : ℝ} (h : c ≤ d) : countLE x c ≤ countLE x d :=
  card_le_card fun j hj ↦ by
    simp only [mem_filter, mem_univ, true_and] at hj ⊢; linarith

theorem countLE_le_card (x : ι → ℝ) (c : ℝ) : countLE x c ≤ Fintype.card ι :=
  (card_filter_le _ _).trans_eq (card_univ)

theorem numRej_mem (q : ℝ) (x : ι → ℝ) : numRej q x ∈ passing q x := max'_mem _ _

theorem numRej_le_card (q : ℝ) (x : ι → ℝ) : numRej q x ≤ Fintype.card ι := by
  have := numRej_mem q x
  simp only [passing, mem_filter, mem_range] at this; omega

theorem numRej_le_countLE (q : ℝ) (x : ι → ℝ) :
    numRej q x ≤ countLE x (q * numRej q x / Fintype.card ι) := by
  have := numRej_mem q x
  simp only [passing, mem_filter] at this; exact this.2

theorem le_numRej {q : ℝ} {x : ι → ℝ} {k : ℕ} (hk : k ≤ Fintype.card ι)
    (h : k ≤ countLE x (q * k / Fintype.card ι)) : k ≤ numRej q x :=
  le_max' _ _ (by simp only [passing, mem_filter, mem_range]; exact ⟨by omega, h⟩)

theorem thr_mono {q : ℝ} (hq : 0 ≤ q) {k l : ℕ} (h : k ≤ l) :
    q * k / Fintype.card ι ≤ q * l / Fintype.card ι :=
  div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast h) hq)
    (Nat.cast_nonneg _)

theorem thr_nonneg {q : ℝ} (hq : 0 ≤ q) (k : ℕ) : 0 ≤ q * k / Fintype.card ι := by positivity

/-- **Exactly `numRej` tests are rejected.** For `q ≥ 0`, the number of values at most
`q · numRej / m` is `numRej`. -/
theorem countLE_numRej {q : ℝ} (hq : 0 ≤ q) (x : ι → ℝ) :
    countLE x (q * numRej q x / Fintype.card ι) = numRej q x := by
  refine le_antisymm ?_ (numRej_le_countLE q x)
  by_contra hlt
  replace hlt := not_le.mp hlt
  have hle : numRej q x + 1 ≤ Fintype.card ι := hlt.trans_le (countLE_le_card _ _)
  have : numRej q x + 1 ≤ numRej q x := by
    refine le_numRej hle (hlt.trans_le (countLE_mono x ?_))
    exact_mod_cast thr_mono (ι := ι) hq (Nat.le_succ _)
  omega

variable [DecidableEq ι]

/-- Setting one value to `0` never lowers a count at a level `c ≥ 0`. -/
theorem countLE_le_countLE_update (x : ι → ℝ) (i : ι) {c : ℝ} (hc : 0 ≤ c) :
    countLE x c ≤ countLE (Function.update x i 0) c :=
  card_le_card fun j hj ↦ by
    simp only [mem_filter, mem_univ, true_and] at hj ⊢
    rcases eq_or_ne j i with rfl | h
    · simpa using hc
    · simpa [Function.update_of_ne h] using hj

/-- Setting the value at `i` to `0` leaves a count at level `c` unchanged when `x i ≤ c`. -/
theorem countLE_update_eq (x : ι → ℝ) (i : ι) {c : ℝ} (hc : 0 ≤ c) (hi : x i ≤ c) :
    countLE (Function.update x i 0) c = countLE x c := by
  unfold countLE
  congr 1
  ext j
  simp only [mem_filter, mem_univ, true_and]
  rcases eq_or_ne j i with rfl | h
  · simp [hc, hi]
  · simp [Function.update_of_ne h]

theorem numRej_le_numRej_update {q : ℝ} (hq : 0 ≤ q) (x : ι → ℝ) (i : ι) :
    numRej q x ≤ numRej q (Function.update x i 0) :=
  le_numRej (numRej_le_card q x)
    ((numRej_le_countLE q x).trans (countLE_le_countLE_update x i (thr_nonneg hq _)))

/-- **A rejected value can be set to `0`.** For `q ≥ 0`, if `x i ≤ q · numRej / m` (test `i` is
rejected), setting `x i` to `0` does not change the number of rejections. -/
theorem numRej_update_eq_of_le {q : ℝ} (hq : 0 ≤ q) {x : ι → ℝ} {i : ι}
    (h : x i ≤ q * numRej q x / Fintype.card ι) :
    numRej q (Function.update x i 0) = numRej q x := by
  refine le_antisymm ?_ (numRej_le_numRej_update hq x i)
  set R' := numRej q (Function.update x i 0)
  have hi : x i ≤ q * R' / Fintype.card ι :=
    h.trans (thr_mono hq (numRej_le_numRej_update hq x i))
  refine le_numRej (numRej_le_card q _) ?_
  rw [← countLE_update_eq x i (thr_nonneg hq _) hi]
  exact numRej_le_countLE q _

/-- **The converse.** For `q ≥ 0`, if `x i` is at most `q / m` times the number of rejections with
`x i` set to `0`, then the number of rejections is the same with or without that change. -/
theorem numRej_eq_of_le_update {q : ℝ} (hq : 0 ≤ q) {x : ι → ℝ} {i : ι}
    (h : x i ≤ q * numRej q (Function.update x i 0) / Fintype.card ι) :
    numRej q x = numRej q (Function.update x i 0) := by
  refine le_antisymm (numRej_le_numRej_update hq x i) ?_
  refine le_numRej (numRej_le_card q _) ?_
  rw [← countLE_update_eq x i (thr_nonneg hq _) h]
  exact numRej_le_countLE q _

/-- With one value set to `0`, at least one test is rejected. -/
theorem one_le_numRej_update {q : ℝ} (hq : 0 ≤ q) (x : ι → ℝ) (i : ι) :
    1 ≤ numRej q (Function.update x i 0) := by
  have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  refine le_numRej hcard ?_
  refine card_pos.mpr ⟨i, ?_⟩
  simp only [mem_filter, mem_univ, true_and, Function.update_self]
  exact_mod_cast thr_nonneg (ι := ι) hq 1

/-- **One test's part of the false-find share.** For `q ≥ 0`, with `R` the number of rejections
and `Rᵢ` the number with `x i` set to `0`:
`[x i ≤ q R / m] / R = ∑ k ∈ [1, m], [Rᵢ = k and x i ≤ q k / m] / k`. -/
theorem indicator_div_numRej_eq_sum {q : ℝ} (hq : 0 ≤ q) (x : ι → ℝ) (i : ι) :
    (if x i ≤ q * numRej q x / Fintype.card ι then (1 : ℝ) else 0) / numRej q x =
      ∑ k ∈ Icc 1 (Fintype.card ι),
        if numRej q (Function.update x i 0) = k ∧ x i ≤ q * k / Fintype.card ι
          then (1 : ℝ) / k else 0 := by
  set r := numRej q (Function.update x i 0) with hr
  have hmem : r ∈ Icc 1 (Fintype.card ι) :=
    mem_Icc.mpr ⟨one_le_numRej_update hq x i, numRej_le_card q _⟩
  simp_rw [ite_and]
  rw [sum_ite_eq, ite_eq_left hmem]
  by_cases h : x i ≤ q * numRej q x / Fintype.card ι
  · have he := numRej_update_eq_of_le hq h
    rw [ite_eq_left h, hr, he, ite_eq_left h, one_div]
  · have hn : ¬ x i ≤ q * r / Fintype.card ι := fun h' ↦
      h (by rw [numRej_eq_of_le_update hq h']; exact h')
    rw [ite_eq_right h, ite_eq_right hn, zero_div]

/-- The share of rejections that are in `H`: (rejected tests in `H`) / (all rejections), and `0`
when nothing is rejected. With `H` the true nulls, this is the share of false finds. -/
noncomputable def falseShare (q : ℝ) (H : Finset ι) (x : ι → ℝ) : ℝ :=
  ((H.filter fun j ↦ x j ≤ q * numRej q x / Fintype.card ι).card : ℝ) / numRej q x

/-- **The false-find share, split by test and by count.** For `q ≥ 0`:
`falseShare = ∑ i ∈ H, ∑ k ∈ [1, m], [Rᵢ = k and x i ≤ q k / m] / k`. -/
theorem falseShare_eq_sum {q : ℝ} (hq : 0 ≤ q) (H : Finset ι) (x : ι → ℝ) :
    falseShare q H x = ∑ i ∈ H, ∑ k ∈ Icc 1 (Fintype.card ι),
      if numRej q (Function.update x i 0) = k ∧ x i ≤ q * k / Fintype.card ι
        then (1 : ℝ) / k else 0 := by
  rw [falseShare, card_filter, Nat.cast_sum, sum_div]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← indicator_div_numRej_eq_sum hq x i]
  push_cast
  rfl

section Probability

omit [DecidableEq ι] in
theorem measurable_countLE (c : ℝ) : Measurable fun x : ι → ℝ ↦ (countLE x c : ℝ) := by
  have : (fun x : ι → ℝ ↦ (countLE x c : ℝ)) = fun x ↦ ∑ j, if x j ≤ c then (1 : ℝ) else 0 := by
    funext x
    simp only [countLE, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [this]
  refine Finset.measurable_sum _ fun j _ ↦ ?_
  exact Measurable.ite (measurableSet_le (measurable_pi_apply j) measurable_const)
    measurable_const measurable_const

omit [DecidableEq ι] in
/-- The number of rejections is a measurable function of the p-values. -/
theorem measurable_numRej (q : ℝ) : Measurable (numRej q : (ι → ℝ) → ℕ) := by
  refine measurable_to_countable' fun k ↦ ?_
  have hset : (numRej q : (ι → ℝ) → ℕ) ⁻¹' {k} =
      {x : ι → ℝ | k ∈ passing q x ∧ ∀ l : ℕ, l ∈ passing q x → l ≤ k} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro rfl; exact ⟨numRej_mem q x, fun l hl ↦ le_max' _ _ hl⟩
    · rintro ⟨hk, hmax⟩; exact le_antisymm (max'_le _ _ _ hmax) (le_max' _ _ hk)
  have hmem : ∀ l : ℕ, Measurable fun x : ι → ℝ ↦ l ∈ passing q x := fun l ↦ by
    have hle : Measurable fun x : ι → ℝ ↦ l ≤ countLE x (q * l / Fintype.card ι) := by
      have := measurableSet_le (f := fun _ : ι → ℝ ↦ (l : ℝ)) measurable_const
        (measurable_countLE (ι := ι) (q * l / Fintype.card ι))
      simp only [Nat.cast_le] at this
      exact measurableSet_setOfPred.1 this
    simp only [passing, mem_filter]
    exact measurable_const.and hle
  rw [hset]
  exact measurableSet_setOfPred.2
    ((hmem k).and (Measurable.forall fun l ↦ (hmem l).imp measurable_const))

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- **One p-value is independent of the count of rejections with it set to `0`.** -/
theorem indepFun_numRej_update {P : ι → Ω → ℝ} (hP : ∀ i, Measurable (P i))
    (hind : iIndepFun P μ) (q : ℝ) (i : ι) :
    IndepFun (P i) (fun ω ↦ numRej q (Function.update (fun j ↦ P j ω) i 0)) μ := by
  have h := hind.indepFun_finset {i} (univ.erase i) (by simp) hP
  have hφ : Measurable fun v : ↥({i} : Finset ι) → ℝ ↦ v ⟨i, mem_singleton_self i⟩ :=
    measurable_pi_apply _
  have hψ : Measurable fun v : ↥(univ.erase i) → ℝ ↦
      numRej q (fun j ↦ if h : j ∈ univ.erase i then v ⟨j, h⟩ else 0) := by
    refine (measurable_numRej q).comp (Measurable.of_eval fun j ↦ ?_)
    by_cases hj : j ∈ univ.erase i
    · simp only [hj, dite_true]; exact measurable_pi_apply _
    · simp only [hj, dite_false]; exact measurable_const
  have e2 : (fun ω ↦ numRej q (Function.update (fun j ↦ P j ω) i 0)) =
      (fun v : ↥(univ.erase i) → ℝ ↦
        numRej q (fun j ↦ if h : j ∈ univ.erase i then v ⟨j, h⟩ else 0)) ∘
        (fun a (j : ↥(univ.erase i)) ↦ P j a) := by
    funext ω
    simp only [Function.comp_apply]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [e2]
  exact h.comp hφ hψ

omit [DecidableEq ι] in
/-- **Benjamini-Hochberg: the expected share of false finds is at most `q m₀ / m`.** Let the
p-values `P j` be independent and measurable, let `H` be the true nulls, each with
`P(P i ≤ t) ≤ t` for `t ≥ 0`, and let `q ≥ 0`. Then the expected value of
(rejected tests in `H`) / (all rejections) is at most `|H| q / m`. For a trader testing many rules
at once: if the rules' tests are independent, keeping every rule the procedure keeps leaves, on
average, at most the share `q` of kept rules that have no real edge. -/
theorem integral_falseShare_le {P : ι → Ω → ℝ} (hP : ∀ i, Measurable (P i))
    (hind : iIndepFun P μ) {H : Finset ι}
    (hnull : ∀ i ∈ H, ∀ t : ℝ, 0 ≤ t → μ.real {ω | P i ω ≤ t} ≤ t) {q : ℝ} (hq : 0 ≤ q) :
    ∫ ω, falseShare q H (fun j ↦ P j ω) ∂μ ≤ H.card * q / Fintype.card ι := by
  classical
  set m := Fintype.card ι with hm
  set Rf : ι → Ω → ℕ := fun i ω ↦ numRej q (Function.update (fun j ↦ P j ω) i 0) with hRf
  set A : ι → ℕ → Set Ω := fun i k ↦ {ω | P i ω ≤ q * k / m} with hA
  set B : ι → ℕ → Set Ω := fun i k ↦ Rf i ⁻¹' {k} with hB
  have hRm : ∀ i, Measurable (Rf i) := fun i ↦ by
    refine (measurable_numRej q).comp (Measurable.of_eval fun j ↦ ?_)
    by_cases hj : j = i
    · subst hj; simp only [Function.update_self]; exact measurable_const
    · simp only [Function.update_of_ne hj]; exact hP j
  have hAm : ∀ i k, MeasurableSet (A i k) := fun i k ↦
    measurableSet_le (hP i) measurable_const
  have hBm : ∀ i k, MeasurableSet (B i k) := fun i k ↦ hRm i (measurableSet_singleton k)
  -- the share, written as a sum of indicators
  have hpt : (fun ω ↦ falseShare q H (fun j ↦ P j ω)) = fun ω ↦
      ∑ i ∈ H, ∑ k ∈ Icc 1 m, (B i k ∩ A i k).indicator (fun _ ↦ (1 : ℝ) / k) ω := by
    funext ω
    rw [falseShare_eq_sum hq]
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun k _ ↦ ?_
    by_cases hmem : ω ∈ B i k ∩ A i k
    · rw [Set.indicator_of_mem hmem]; exact ite_eq_left hmem
    · rw [Set.indicator_of_notMem hmem]; exact ite_eq_right hmem
  rw [hpt, integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun k _ ↦
    (integrable_const _).indicator ((hBm i k).inter (hAm i k))]
  -- each null test contributes at most q / m
  have hterm : ∀ i ∈ H, ∫ ω, ∑ k ∈ Icc 1 m, (B i k ∩ A i k).indicator (fun _ ↦ (1 : ℝ) / k) ω ∂μ
      ≤ q / m := by
    intro i hi
    rw [integral_finsetSum _ fun k _ ↦
      (integrable_const _).indicator ((hBm i k).inter (hAm i k))]
    simp only [integral_indicator_const _ ((hBm _ _).inter (hAm _ _)), smul_eq_mul]
    have hind_i := indepFun_numRej_update hP hind q i
    have hprod : ∀ k, μ.real (B i k ∩ A i k) = μ.real (B i k) * μ.real (A i k) := fun k ↦ by
      have := hind_i.measure_inter_preimage_eq_mul (Set.Iic (q * k / m)) {k}
        measurableSet_Iic (measurableSet_singleton k)
      rw [Set.inter_comm, measureReal_def, measureReal_def, measureReal_def, mul_comm,
        ← ENNReal.toReal_mul]
      exact congrArg ENNReal.toReal this
    calc ∑ k ∈ Icc 1 m, μ.real (B i k ∩ A i k) * (1 / k)
        ≤ ∑ k ∈ Icc 1 m, μ.real (B i k) * (q / m) := by
          refine sum_le_sum fun k hk ↦ ?_
          have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
          rw [hprod k, mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
          calc μ.real (A i k) * (1 / k) ≤ q * k / m * (1 / k) :=
                mul_le_mul_of_nonneg_right (hnull i hi _ (thr_nonneg hq k)) (by positivity)
            _ = q / m := by field_simp
      _ = (∑ k ∈ Icc 1 m, μ.real (B i k)) * (q / m) := by rw [sum_mul]
      _ ≤ 1 * (q / m) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [← measureReal_biUnion_finset]
          · exact measureReal_le_one
          · intro a _ b _ hab
            exact Set.disjoint_left.mpr fun ω h1 h2 ↦ hab (h1.symm.trans h2)
          · exact fun k _ ↦ hBm i k
      _ = q / m := one_mul _
  calc ∑ i ∈ H, ∫ ω, ∑ k ∈ Icc 1 m, (B i k ∩ A i k).indicator (fun _ ↦ (1 : ℝ) / k) ω ∂μ
      ≤ ∑ _i ∈ H, q / m := sum_le_sum hterm
    _ = H.card * q / m := by rw [sum_const, nsmul_eq_mul]; ring

end Probability

end ClassicalLean.Probability.StepUpProcedure
