/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Kernel.Condexp

/-!
# Trusting an average when the samples are not independent

`measureReal_abs_sum_ge_le_of_hasCondSubgaussianMGF`: if the surprises `Y i` (outcome minus its
expected value) are adapted to a filtration, the first one is sub-Gaussian with parameter `1/4`, and
each later one is conditionally sub-Gaussian with parameter `1/4` given the past, then
`P(|Y 0 + ⋯ + Y (n-1)| ≥ n e) ≤ 2 exp (-2 n e²)`: the same bound as for independent samples
(`ClassicalLean.Probability.SampleMean.measureReal_abs_sampleMean_sub_ge_le`), hence the same
number of samples (190 for `e = 0.1`, `δ = 0.05`).

Parameter `1/4` is what a variable with values in an interval of length `1` and mean `0` has
(Hoeffding's lemma). The conditional version, from "values in an interval of length `1` and
conditional mean `0` given the past" to "conditionally sub-Gaussian with parameter `1/4`", is proved
here (`hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero`), so the plain statement
`measureReal_abs_sampleMean_sub_ge_le_of_condExp` needs only: outcomes in `[0, 1]`, and each
outcome's conditional win probability given the past equal to the same `p`.

## What Mathlib provides

The Azuma–Hoeffding inequality for conditionally sub-Gaussian increments
(`ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF`), and negation of sub-Gaussian
variables. This module adds the two-sided form, the conditional Hoeffding lemma
(via the conditional expectation kernel), a one-sided conditional Hoeffding bound for a conditional
mean at least `g` (`condExp_exp_mul_sub_le`), and the plain win-rate statement.
-/

open MeasureTheory ProbabilityTheory Real Finset

open scoped NNReal

namespace ClassicalLean.Probability.DependentSampleMean

variable {Ω : Type*} {m0 : MeasurableSpace Ω} [StandardBorelSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0}

/-- **Trusting an average of dependent samples (two-sided Azuma–Hoeffding).** For `Y` adapted to
`ℱ`, `Y 0` sub-Gaussian with parameter `1/4` and each `Y (i + 1)` conditionally sub-Gaussian with
parameter `1/4` given `ℱ i`: `P(|∑ i < n, Y i| ≥ n e) ≤ 2 exp (-2 n e²)`. For a trader: even when
trades depend on each other, as long as each trade's surprise averages zero given everything
before it, the observed win rate is as trustworthy as for independent trades. -/
theorem measureReal_abs_sum_ge_le_of_hasCondSubgaussianMGF {Y : ℕ → Ω → ℝ}
    (h_adapted : StronglyAdapted ℱ Y) (h0 : HasSubgaussianMGF (Y 0) (1 / 4) μ)
    (h_subG : ∀ i, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (1 / 4) μ)
    {n : ℕ} (hn : 0 < n) {e : ℝ} (he : 0 ≤ e) :
    μ.real {ω | n * e ≤ |∑ i ∈ range n, Y i ω|} ≤ 2 * exp (-2 * n * e ^ 2) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hne : (0 : ℝ) ≤ n * e := by positivity
  have hsumc : ∑ _i ∈ range n, ((1 / 4 : ℝ≥0) : ℝ) = n / 4 := by
    rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  have hexp : -(n * e) ^ 2 / (2 * (n / 4 : ℝ)) = -2 * n * e ^ 2 := by
    field_simp; ring
  have up := measure_sum_ge_le_of_hasCondSubgaussianMGF (cY := fun _ ↦ 1 / 4) h_adapted h0 n
    (fun i _ ↦ h_subG i) hne
  have hnegadapt : StronglyAdapted ℱ (fun i ω ↦ -Y i ω) := fun i ↦ (h_adapted i).neg
  have hneg0 : HasSubgaussianMGF (fun ω ↦ -Y 0 ω) (1 / 4) μ := h0.neg
  have hnegsub : ∀ i, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (fun ω ↦ -Y (i + 1) ω) (1 / 4) μ :=
    fun i ↦ Kernel.HasSubgaussianMGF.neg (h_subG i)
  have dn := measure_sum_ge_le_of_hasCondSubgaussianMGF (cY := fun _ ↦ 1 / 4) hnegadapt hneg0 n
    (fun i _ ↦ hnegsub i) hne
  push_cast at up dn
  rw [show ∑ _i ∈ range n, (1 / 4 : ℝ) = n / 4 by rw [sum_const, card_range, nsmul_eq_mul]; ring,
    hexp] at up dn
  have hsubset : {ω | n * e ≤ |∑ i ∈ range n, Y i ω|} ⊆
      {ω | n * e ≤ ∑ i ∈ range n, Y i ω} ∪ {ω | n * e ≤ ∑ i ∈ range n, -Y i ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    simp only [Set.mem_union, Set.mem_ofPred_eq, sum_neg_distrib]
    rcases le_abs'.mp hω with h | h
    · right; linarith
    · left; linarith
  calc μ.real {ω | n * e ≤ |∑ i ∈ range n, Y i ω|}
      ≤ μ.real ({ω | n * e ≤ ∑ i ∈ range n, Y i ω} ∪ {ω | n * e ≤ ∑ i ∈ range n, -Y i ω}) :=
        measureReal_mono hsubset
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ exp (-2 * n * e ^ 2) + exp (-2 * n * e ^ 2) := add_le_add up dn
    _ = 2 * exp (-2 * n * e ^ 2) := by ring

end ClassicalLean.Probability.DependentSampleMean

namespace ClassicalLean.Probability.DependentSampleMean

section ConditionalHoeffding

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} [StandardBorelSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- **Conditional Hoeffding lemma.** A variable with values in `[a, b]` whose conditional
expectation given `m` is `0` is conditionally sub-Gaussian given `m`, with parameter
`((b - a) / 2) ^ 2`. For a trader: a trade outcome that is bounded and has no predictable part
given the past behaves, for the purpose of averaging, like an independent one. -/
theorem hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero (hm : m ≤ m0) {X : Ω → ℝ} {a b : ℝ}
    (hX : Measurable X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (hc : μ[X | m] =ᵐ[μ] 0) :
    HasCondSubgaussianMGF m hm X ((‖b - a‖₊ / 2) ^ 2) μ := by
  have hXint : Integrable X μ := Integrable.of_mem_Icc a b hX.aemeasurable hb
  have hcomp : condExpKernel μ m ∘ₘ μ.trim hm = μ := condExpKernel_comp_trim hm
  refine ⟨fun t ↦ ?_, ?_⟩
  · rw [hcomp]; exact integrable_exp_mul_of_mem_Icc hX.aemeasurable hb
  · -- bounds hold for almost every conditional distribution
    have hA : ∀ᵐ ω' ∂(μ.trim hm), ∀ᵐ ω ∂(condExpKernel μ m ω'), X ω ∈ Set.Icc a b := by
      apply Measure.ae_ae_of_ae_comp; rw [hcomp]; exact hb
    -- conditional mean zero, read under the trimmed measure
    have h0 : μ[X | m] =ᵐ[μ.trim hm] 0 :=
      StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm stronglyMeasurable_condExp
        stronglyMeasurable_const hc
    have hB : ∀ᵐ ω' ∂(μ.trim hm), ∫ y, X y ∂(condExpKernel μ m ω') = 0 := by
      filter_upwards [(condExp_ae_eq_trim_integral_condExpKernel hm hXint).symm.trans h0]
        with ω' h using h
    filter_upwards [hA, hB] with ω' hA' hB' t
    exact (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hX.aemeasurable hA' hB').mgf_le t

/-- **One-sided conditional Hoeffding lemma.** A variable with values almost surely in `[a, b]`
whose conditional expectation given `m` is almost surely at least `g`: for every `s ≥ 0`, the
conditional expectation of `exp (s (g - X))` given `m` is almost surely at most
`exp ((b - a)² s² / 8)`. Only the lower side of the conditional mean is assumed, so the two-sided
`HasCondSubgaussianMGF` is not available; the proof reads both conditional expectations through the
conditional expectation kernel and applies Hoeffding's lemma under almost every conditional
distribution. For a trader: given the past, the shortfall of a bounded outcome below `g` has the
same exponential-moment bound as for an independent outcome with mean at least `g`; this is the
step that lets the independent-case count carry over to dependent returns. -/
theorem condExp_exp_mul_sub_le (hm : m ≤ m0) {X : Ω → ℝ} {a b g s : ℝ} (hX : Measurable X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (hg : ∀ᵐ ω ∂μ, g ≤ μ[X | m] ω) (hs : 0 ≤ s) :
    μ[fun ω ↦ Real.exp (s * (g - X ω)) | m] ≤ᵐ[μ]
      fun _ ↦ Real.exp ((b - a) ^ 2 * s ^ 2 / 8) := by
  have hXint : Integrable X μ := Integrable.of_mem_Icc a b hX.aemeasurable hb
  have hcomp : condExpKernel μ m ∘ₘ μ.trim hm = μ := condExpKernel_comp_trim hm
  have hEint : Integrable (fun ω ↦ Real.exp (s * (g - X ω))) μ := by
    have h := (integrable_exp_mul_of_mem_Icc (t := -s) hX.aemeasurable hb).const_mul
      (Real.exp (s * g))
    refine h.congr (Filter.Eventually.of_forall fun ω ↦ ?_)
    dsimp only
    rw [← Real.exp_add]; ring_nf
  -- the bounds hold for almost every conditional distribution, read under `μ`
  have hA : ∀ᵐ ω' ∂μ, ∀ᵐ ω ∂(condExpKernel μ m ω'), X ω ∈ Set.Icc a b := by
    refine ae_of_ae_trim hm ?_
    apply Measure.ae_ae_of_ae_comp; rw [hcomp]; exact hb
  filter_upwards [hA, hg, condExp_ae_eq_integral_condExpKernel hm hXint,
    condExp_ae_eq_integral_condExpKernel hm hEint] with ω hAω hgω hBω hCω
  rw [hCω]
  set κ := condExpKernel μ m ω
  set p := ∫ y, X y ∂κ
  have hgp : g ≤ p := hgω.trans_eq hBω
  have hsub := (hasSubgaussianMGF_of_mem_Icc hX.aemeasurable hAω).mgf_le (-s)
  have hsplit : (fun y ↦ Real.exp (s * (g - X y))) =
      fun y ↦ Real.exp (s * (g - p)) * Real.exp (-s * (X y - p)) := by
    funext y; rw [← Real.exp_add]; ring_nf
  have hmgf : ∫ y, Real.exp (s * (g - X y)) ∂κ =
      Real.exp (s * (g - p)) * mgf (fun y ↦ X y - p) κ (-s) := by
    rw [hsplit, integral_const_mul]; rfl
  have h1 : Real.exp (s * (g - p)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hs (by linarith))
  have hc : (((‖b - a‖₊ / 2) ^ 2 : NNReal) : ℝ) * (-s) ^ 2 / 2 = (b - a) ^ 2 * s ^ 2 / 8 := by
    push_cast
    rw [Real.norm_eq_abs]
    rw [div_pow, sq_abs]; ring
  rw [hmgf]
  calc Real.exp (s * (g - p)) * mgf (fun y ↦ X y - p) κ (-s)
      ≤ 1 * mgf (fun y ↦ X y - p) κ (-s) :=
        mul_le_mul_of_nonneg_right h1 mgf_nonneg
    _ ≤ Real.exp ((b - a) ^ 2 * s ^ 2 / 8) := by
        rw [one_mul, ← hc]; exact hsub

end ConditionalHoeffding

end ClassicalLean.Probability.DependentSampleMean

namespace ClassicalLean.Probability.DependentSampleMean

variable {Ω : Type*} {m0 : MeasurableSpace Ω} [StandardBorelSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}

/-- **Trusting a win rate when trades depend on each other.** Let `X i` be adapted to `ℱ`, with
values in `[0, 1]`, `E[X 0] = p` and `E[X (i + 1) | ℱ i] = p`: each trade wins with probability
`p` given everything before it, however the trades depend on each other otherwise. Then the
observed win rate over `n` trades is `e` or more from `p` with probability at most
`2 exp (-2 n e²)`, exactly the independent-trades bound, so the same 190 trades suffice for
`e = 0.1`, `δ = 0.05`. -/
theorem measureReal_abs_sampleMean_sub_ge_le_of_condExp {X : ℕ → Ω → ℝ}
    (h_adapted : StronglyAdapted ℱ X) (h_meas : ∀ i, Measurable (X i))
    (h_bdd : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (h0 : μ[X 0] = p)
    (hcond : ∀ i, μ[X (i + 1) | ℱ i] =ᵐ[μ] fun _ ↦ p) {n : ℕ} (hn : 0 < n) {e : ℝ}
    (he : 0 ≤ e) :
    μ.real {ω | e ≤ |(∑ i ∈ range n, X i ω) / n - p|} ≤ 2 * exp (-2 * n * e ^ 2) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set Y : ℕ → Ω → ℝ := fun i ω ↦ X i ω - p with hY
  have hYadapt : StronglyAdapted ℱ Y := fun i ↦ (h_adapted i).sub stronglyMeasurable_const
  have hYbdd : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (-p) (1 - p) := fun i ↦ by
    filter_upwards [h_bdd i] with ω hω
    exact ⟨by simp [hY]; linarith [hω.1], by simp [hY]; linarith [hω.2]⟩
  have hlen : ((‖(1 - p) - -p‖₊ / 2) ^ 2 : NNReal) = 1 / 4 := by
    have : (1 - p) - -p = 1 := by ring
    rw [this, nnnorm_one]; norm_num
  have hY0 : HasSubgaussianMGF (Y 0) (1 / 4) μ := by
    have h := hasSubgaussianMGF_of_mem_Icc (h_meas 0).aemeasurable (h_bdd 0)
    rw [h0] at h
    convert h using 1
    rw [sub_zero, nnnorm_one]; norm_num
  have hYsub : ∀ i, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (1 / 4) μ := fun i ↦ by
    have hc : μ[Y (i + 1) | ℱ i] =ᵐ[μ] 0 := by
      have hsub := condExp_sub (m := ℱ i) (μ := μ)
        (Integrable.of_mem_Icc 0 1 (h_meas (i + 1)).aemeasurable (h_bdd (i + 1)))
        (integrable_const p)
      filter_upwards [hsub, hcond i] with ω h1 h2
      simp only [hY] at h1 ⊢
      rw [show (fun ω ↦ X (i + 1) ω - p) = X (i + 1) - fun _ ↦ p from rfl, h1, Pi.sub_apply, h2,
        condExp_const (ℱ.le i)]
      simp
    rw [← hlen]
    exact hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero (ℱ.le i)
      ((h_meas (i + 1)).sub measurable_const) (hYbdd (i + 1)) hc
  have hmain := measureReal_abs_sum_ge_le_of_hasCondSubgaussianMGF hYadapt hY0 hYsub hn he
  have hsubset : {ω | e ≤ |(∑ i ∈ range n, X i ω) / n - p|} ⊆
      {ω | n * e ≤ |∑ i ∈ range n, Y i ω|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have key : ∑ i ∈ range n, Y i ω = n * ((∑ i ∈ range n, X i ω) / n - p) := by
      simp only [hY, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]; field_simp
    rw [key, abs_mul, abs_of_pos hn']
    exact mul_le_mul_of_nonneg_left hω hn'.le
  exact (measureReal_mono hsubset).trans hmain

end ClassicalLean.Probability.DependentSampleMean
