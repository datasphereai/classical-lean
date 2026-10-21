/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.InformationTheory.MutualInformation
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import ClassicalLean.Probability.TwoStateChain

/-!
# The capacity of the binary symmetric channel

The binary symmetric channel with crossover probability `ε` receives an input `a : Fin 2` as the
output `b = a` with probability `1 - ε`, and as the other symbol with probability `ε`. An input law
`p : Fin 2 → ℝ` gives input and output the joint law `p a * (if a = b then 1 - ε else ε)`; its
mutual information is the library's `mutualInfo` (`InformationTheory/MutualInformation`), the
relative entropy of the joint law to the product of its marginals, with the natural logarithm.
`Real.binEntropy ε` is the binary entropy `h(ε) = -ε log ε - (1 - ε) log (1 - ε)`.

The results, order CLOUD-MATH-3, item 130 of MATH-PLAN-library-2:

* `mutualInfo_bsc_le` — for every `ε ∈ [0, 1]` and every input law `p`, the mutual information is
  at most `log 2 - h(ε)`;
* `mutualInfo_bsc_half` — at the uniform input, `p a = 1 / 2`, it equals `log 2 - h(ε)`.

Together: the capacity of the channel, the largest mutual information over input laws, is
`log 2 - h(ε)`, and the uniform input reaches it.

Row 163 of MATH-PLAN-library-2's bridges file (order LEAN-34), `n` channels in series, whose
joint law is `p a * (twoStateMatrix ε ε ^ n) a b` (TwoStateChain's matrix, imported here):

* `mutualInfo_bsc_pow_le` — for `ε ∈ (0, 1]`, every input law and every `n`, the mutual
  information is at most `log 2 - h(εₙ)` with `εₙ = (1 - (1 - 2ε)^n)/2`;
* `mutualInfo_bsc_pow_half` — the uniform input attains it;
* `tendsto_capacity_bsc_pow` — for `ε ∈ (0, 1)`, `log 2 - h(εₙ) → 0`: a long cascade forgets its
  input.

These three statements are claude-ai's, from the bridges file's row 163; their proofs are order
LEAN-34's session's.

The proof. For a nonnegative joint law the mutual information is the sum of the entropies of the
two marginals minus the entropy of the joint law
(`mutualInfo_eq_shannonEntropy_add_shannonEntropy_sub_shannonEntropy`). Here the entropy of the
joint law is the input's entropy plus `h(ε)`, from `x y log (x y) = y (x log x) + x (y log y)`
(`mul_mul_log_mul`), so the mutual information is the output's entropy minus `h(ε)`
(`mutualInfo_bscJoint`). The output's entropy is at most `log 2` (`shannonEntropy_le_log_card`),
and at the uniform input the output law is uniform (`bscJoint_output_half`), with entropy `log 2`.

The proof is the draft `d130-r1-s1` (written by Claude Opus 5.5 through the Anthropic Batch API,
the lane's API-CREDIT-1 work), adapted by the Claude Code cloud session that landed it (order
CLOUD-MATH-3): the namespace, which the private `bscJoint` and its lemmas moved into with the main
theorems; docstrings; `change` where a `show` changed the goal; and `ite_eq_left` and
`ite_eq_right` for the deprecated `if_pos` and `if_neg`. Its two imports were already targeted.
The five witnesses at the end of the file, at `ε = 1 / 4`, are new: the item had no witness start;
the last three are for row 163 (order LEAN-34), and the two for the bounds take also `n = 3`.
-/

open ClassicalLean.Simplex

namespace ClassicalLean.InformationTheory.ChannelCapacity

/-- The joint law of input and output of the binary symmetric channel. -/
private noncomputable def bscJoint (ε : ℝ) (p : Fin 2 → ℝ) : Fin 2 × Fin 2 → ℝ :=
  fun ab => p ab.1 * (if ab.1 = ab.2 then 1 - ε else ε)

private theorem bscJoint_values (ε : ℝ) (p : Fin 2 → ℝ) :
    bscJoint ε p (0, 0) = p 0 * (1 - ε) ∧ bscJoint ε p (0, 1) = p 0 * ε ∧
      bscJoint ε p (1, 0) = p 1 * ε ∧ bscJoint ε p (1, 1) = p 1 * (1 - ε) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · change p 0 * (if (0 : Fin 2) = 0 then 1 - ε else ε) = _
    rw [ite_eq_left rfl]
  · change p 0 * (if (0 : Fin 2) = 1 then 1 - ε else ε) = _
    rw [ite_eq_right h01]
  · change p 1 * (if (1 : Fin 2) = 0 then 1 - ε else ε) = _
    rw [ite_eq_right h01.symm]
  · change p 1 * (if (1 : Fin 2) = 1 then 1 - ε else ε) = _
    rw [ite_eq_left rfl]

private theorem bscJoint_nonneg {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {p : Fin 2 → ℝ}
    (hp0 : ∀ a, 0 ≤ p a) : ∀ ab, 0 ≤ bscJoint ε p ab := by
  intro ab
  change 0 ≤ p ab.1 * (if ab.1 = ab.2 then 1 - ε else ε)
  exact mul_nonneg (hp0 _) (by split_ifs <;> linarith)

/-- `x y log (x y) = y (x log x) + x (y log y)` for all real `x`, `y`. -/
private theorem mul_mul_log_mul (x y : ℝ) :
    x * y * Real.log (x * y) = y * (x * Real.log x) + x * (y * Real.log y) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rw [Real.log_mul hx hy]
  ring

/-- The mutual information of the binary symmetric channel is the output entropy minus `h(ε)`. -/
private theorem mutualInfo_bscJoint {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {p : Fin 2 → ℝ}
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    mutualInfo (bscJoint ε p)
      = shannonEntropy (fun b => ∑ a, bscJoint ε p (a, b)) - Real.binEntropy ε := by
  obtain ⟨e00, e01, e10, e11⟩ := bscJoint_values ε p
  have hP0 := bscJoint_nonneg hε0 hε1 hp0
  have h1 : p 1 = 1 - p 0 := by
    have h := hp1
    rw [Fin.sum_univ_two] at h
    linarith
  have hrow' : ∀ a, ∑ b, bscJoint ε p (a, b) = p a := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · rw [Fin.sum_univ_two, e00, e01]; ring
    · rw [Fin.sum_univ_two, e10, e11]; ring
  have hrow : (fun a => ∑ b, bscJoint ε p (a, b)) = p := funext hrow'
  have hp' : shannonEntropy p = -(p 0 * Real.log (p 0) + p 1 * Real.log (p 1)) := by
    simp only [shannonEntropy, Fin.sum_univ_two]
  have hPH : shannonEntropy (bscJoint ε p) =
      -(bscJoint ε p (0, 0) * Real.log (bscJoint ε p (0, 0))
        + bscJoint ε p (0, 1) * Real.log (bscJoint ε p (0, 1))
        + (bscJoint ε p (1, 0) * Real.log (bscJoint ε p (1, 0))
          + bscJoint ε p (1, 1) * Real.log (bscJoint ε p (1, 1)))) := by
    simp only [shannonEntropy, Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [e00, e01, e10, e11, mul_mul_log_mul, mul_mul_log_mul, mul_mul_log_mul,
    mul_mul_log_mul] at hPH
  have hb : Real.binEntropy ε = -(ε * Real.log ε) - (1 - ε) * Real.log (1 - ε) := by
    rw [Real.binEntropy, Real.log_inv, Real.log_inv]
    ring
  rw [mutualInfo_eq_shannonEntropy_add_shannonEntropy_sub_shannonEntropy hP0, hrow, hPH, hp',
    hb, h1]
  ring

/-- At the uniform input the output law is uniform. -/
private theorem bscJoint_output_half {ε : ℝ} {p : Fin 2 → ℝ} (hp : ∀ a, p a = 1 / 2) :
    (fun b => ∑ a, bscJoint ε p (a, b)) = fun _ => (2 : ℝ)⁻¹ := by
  obtain ⟨e00, e01, e10, e11⟩ := bscJoint_values ε p
  have hv : ∀ b, ∑ a, bscJoint ε p (a, b) = (2 : ℝ)⁻¹ := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · rw [Fin.sum_univ_two, e00, e10, hp 0, hp 1]; ring
    · rw [Fin.sum_univ_two, e01, e11, hp 0, hp 1]; ring
  exact funext hv

/-- **The capacity bound for the binary symmetric channel.** Item 130 of MATH-PLAN-library-2
(order CLOUD-MATH-3). For a crossover probability `ε ∈ [0, 1]` and every input law `p` on `Fin 2`,
the mutual information of input and output, whose joint law is
`p a * (if a = b then 1 - ε else ε)`, is at most `log 2 - h(ε)`. -/
theorem mutualInfo_bsc_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {p : Fin 2 → ℝ}
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    mutualInfo (fun ab : Fin 2 × Fin 2 => p ab.1 * (if ab.1 = ab.2 then 1 - ε else ε))
      ≤ Real.log 2 - Real.binEntropy ε := by
  change mutualInfo (bscJoint ε p) ≤ Real.log 2 - Real.binEntropy ε
  obtain ⟨e00, e01, e10, e11⟩ := bscJoint_values ε p
  have hP0 := bscJoint_nonneg hε0 hε1 hp0
  have hY0 : ∀ b, 0 ≤ ∑ a, bscJoint ε p (a, b) :=
    fun b => Finset.sum_nonneg fun a _ => hP0 (a, b)
  have hY1 : ∑ b, ∑ a, bscJoint ε p (a, b) = 1 := by
    have h := hp1
    rw [Fin.sum_univ_two] at h
    simp only [Fin.sum_univ_two]
    rw [e00, e01, e10, e11]
    linear_combination h
  have hY := shannonEntropy_le_log_card (p := fun b => ∑ a, bscJoint ε p (a, b)) hY0 hY1
  simp only [Fintype.card_fin, Nat.cast_ofNat] at hY
  rw [mutualInfo_bscJoint hε0 hε1 hp0 hp1]
  linarith

/-- **The uniform input attains the capacity** `log 2 - h(ε)` of the binary symmetric channel.
Item 130 of MATH-PLAN-library-2 (order CLOUD-MATH-3). -/
theorem mutualInfo_bsc_half {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    mutualInfo (fun ab : Fin 2 × Fin 2 => (1 / 2 : ℝ) * (if ab.1 = ab.2 then 1 - ε else ε))
      = Real.log 2 - Real.binEntropy ε := by
  change mutualInfo (bscJoint ε (fun _ => (1 / 2 : ℝ))) = Real.log 2 - Real.binEntropy ε
  rw [mutualInfo_bscJoint (p := fun _ => (1 / 2 : ℝ)) hε0 hε1 (fun _ => by norm_num)
      (by norm_num [Fin.sum_univ_two]),
    bscJoint_output_half (p := fun _ => (1 / 2 : ℝ)) (fun _ => rfl)]
  simp only [shannonEntropy, Fin.sum_univ_two, Real.log_inv]
  ring

open ClassicalLean.Probability.TwoStateChain Matrix in
/-- The entries of the `n`-th power of the symmetric two-state matrix: `1 − εₙ` on the diagonal
and `εₙ = (1 − (1 − 2ε)^n)/2` off it. The column-`1` entries come from TwoStateChain's
`vecMul_pow_apply_one` at `s = t = ε`, started at each symbol (`Pi.single a 1`), and the column-`0`
entries from the rows' sums (the power is row-stochastic). -/
private theorem twoStateMatrix_pow_apply {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (n : ℕ)
    (a b : Fin 2) :
    (twoStateMatrix ε ε ^ n) a b =
      if a = b then 1 - (1 - (1 - 2 * ε) ^ n) / 2 else (1 - (1 - 2 * ε) ^ n) / 2 := by
  have hst : 0 < ε + ε := by linarith
  have hcol1 : ∀ a : Fin 2, (twoStateMatrix ε ε ^ n) a 1 =
      ε / (ε + ε) + (1 - ε - ε) ^ n * ((Pi.single a 1 : Fin 2 → ℝ) 1 - ε / (ε + ε)) := by
    intro a
    have h := vecMul_pow_apply_one hst (π := Pi.single a 1) (by fin_cases a <;> simp) n
    rwa [single_one_vecMul] at h
  have hrow : ∀ a : Fin 2, (twoStateMatrix ε ε ^ n) a 0 + (twoStateMatrix ε ε ^ n) a 1 = 1 := by
    intro a
    have hM := pow_mem (twoStateMatrix_mem_rowStochastic hε0.le hε1 hε0.le hε1) n
    simpa [Fin.sum_univ_two] using sum_row_of_mem_rowStochastic hM a
  have hhalf : ε / (ε + ε) = 1 / 2 := by field_simp; ring
  have h12 : 1 - ε - ε = 1 - 2 * ε := by ring
  have h10 := hcol1 0
  have h11 := hcol1 1
  have h00 := hrow 0
  have h01 := hrow 1
  simp only [hhalf, h12] at h10 h11
  fin_cases a <;> fin_cases b <;> simp at h10 h11 h00 h01 ⊢ <;> linarith

/-- `εₙ = (1 − (1 − 2ε)^n)/2` lies in `[0, 1]` for `ε ∈ (0, 1]`, since `|1 − 2ε| ≤ 1`. -/
private theorem crossover_pow_mem_Icc {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (n : ℕ) :
    0 ≤ (1 - (1 - 2 * ε) ^ n) / 2 ∧ (1 - (1 - 2 * ε) ^ n) / 2 ≤ 1 := by
  have hx : |(1 - 2 * ε) ^ n| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr ⟨by linarith, by linarith⟩)
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  constructor <;> linarith

open ClassicalLean.Probability.TwoStateChain in
/-- **Binary symmetric channels in series.** For a crossover probability `ε ∈ (0, 1]`, every input
law `p` on `Fin 2` and every `n`, the mutual information of input and output of `n` binary
symmetric channels in series, whose joint law is `p a * (twoStateMatrix ε ε ^ n) a b`, is at most
`log 2 - h(εₙ)` with `εₙ = (1 - (1 - 2ε)^n)/2`. Row 163 of MATH-PLAN-library-2's bridges file; the
statement is claude-ai's (order LEAN-34), the proof order LEAN-34's session's. -/
theorem mutualInfo_bsc_pow_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {p : Fin 2 → ℝ}
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) (n : ℕ) :
    mutualInfo (fun ab : Fin 2 × Fin 2 => p ab.1 * (twoStateMatrix ε ε ^ n) ab.1 ab.2)
      ≤ Real.log 2 - Real.binEntropy ((1 - (1 - 2 * ε) ^ n) / 2) := by
  obtain ⟨h0, h1⟩ := crossover_pow_mem_Icc hε0 hε1 n
  have hfun : (fun ab : Fin 2 × Fin 2 => p ab.1 * (twoStateMatrix ε ε ^ n) ab.1 ab.2) =
      fun ab : Fin 2 × Fin 2 => p ab.1 * (if ab.1 = ab.2 then 1 - (1 - (1 - 2 * ε) ^ n) / 2
        else (1 - (1 - 2 * ε) ^ n) / 2) := by
    funext ab
    rw [twoStateMatrix_pow_apply hε0 hε1]
  rw [hfun]
  exact mutualInfo_bsc_le h0 h1 hp0 hp1

open ClassicalLean.Probability.TwoStateChain in
/-- **The uniform input attains it.** Row 163 of MATH-PLAN-library-2's bridges file; the statement
is claude-ai's (order LEAN-34), the proof order LEAN-34's session's. -/
theorem mutualInfo_bsc_pow_half {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (n : ℕ) :
    mutualInfo (fun ab : Fin 2 × Fin 2 => (1 / 2 : ℝ) * (twoStateMatrix ε ε ^ n) ab.1 ab.2)
      = Real.log 2 - Real.binEntropy ((1 - (1 - 2 * ε) ^ n) / 2) := by
  obtain ⟨h0, h1⟩ := crossover_pow_mem_Icc hε0 hε1 n
  have hfun : (fun ab : Fin 2 × Fin 2 => (1 / 2 : ℝ) * (twoStateMatrix ε ε ^ n) ab.1 ab.2) =
      fun ab : Fin 2 × Fin 2 => (1 / 2 : ℝ) * (if ab.1 = ab.2 then 1 - (1 - (1 - 2 * ε) ^ n) / 2
        else (1 - (1 - 2 * ε) ^ n) / 2) := by
    funext ab
    rw [twoStateMatrix_pow_apply hε0 hε1]
  rw [hfun]
  exact mutualInfo_bsc_half h0 h1

open Filter Topology in
/-- **A long cascade forgets its input.** For `ε ∈ (0, 1)` the capacity `log 2 - h(εₙ)` of `n`
binary symmetric channels in series tends to `0`. Row 163 of MATH-PLAN-library-2's bridges file;
the statement is claude-ai's (order LEAN-34), the proof order LEAN-34's session's. -/
theorem tendsto_capacity_bsc_pow {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ => Real.log 2 - Real.binEntropy ((1 - (1 - 2 * ε) ^ n) / 2)) atTop
      (𝓝 0) := by
  have hr : |1 - 2 * ε| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have h1 : Tendsto (fun n : ℕ => (1 - (1 - 2 * ε) ^ n) / 2) atTop (𝓝 2⁻¹) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr).const_sub 1).div_const 2
    simpa using h
  have h2 := ((Real.binEntropy_continuous.tendsto _).comp h1).const_sub (Real.log 2)
  simpa [Real.binEntropy_two_inv] using h2

end ClassicalLean.InformationTheory.ChannelCapacity

/-- The hypotheses of `mutualInfo_bsc_le` hold together: the crossover probability `ε = 1 / 4`,
inside `[0, 1]` and away from `1 / 2` (where the capacity is `0`), and the input law
`p = (1 / 3, 2 / 3)`, which is not uniform. -/
example := ClassicalLean.InformationTheory.ChannelCapacity.mutualInfo_bsc_le (ε := 1 / 4)
    (p := ![1 / 3, 2 / 3]) (by norm_num) (by norm_num)
    (fun a => by fin_cases a <;> norm_num) (by norm_num [Fin.sum_univ_two])

/-- The hypotheses of `mutualInfo_bsc_half` hold together: the crossover probability
`ε = 1 / 4`, inside `[0, 1]` and away from `1 / 2` (where the capacity is `0`). -/
example := ClassicalLean.InformationTheory.ChannelCapacity.mutualInfo_bsc_half (ε := 1 / 4)
    (by norm_num) (by norm_num)

/-- The hypotheses of `mutualInfo_bsc_pow_le` hold together: the crossover probability
`ε = 1 / 4`, inside `(0, 1]` and away from `1 / 2` (where the cascade's capacity is `0`); the
input law `p = (1 / 3, 2 / 3)`, which is not uniform; and `n = 3` channels in series. -/
example := ClassicalLean.InformationTheory.ChannelCapacity.mutualInfo_bsc_pow_le (ε := 1 / 4)
    (by norm_num) (by norm_num) (p := ![1 / 3, 2 / 3])
    (fun a => by fin_cases a <;> norm_num) (by norm_num [Fin.sum_univ_two]) (n := 3)

/-- The hypotheses of `mutualInfo_bsc_pow_half` hold together: the crossover probability
`ε = 1 / 4`, inside `(0, 1]` and away from `1 / 2` (where the cascade's capacity is `0`), and
`n = 3` channels in series. -/
example := ClassicalLean.InformationTheory.ChannelCapacity.mutualInfo_bsc_pow_half (ε := 1 / 4)
    (by norm_num) (by norm_num) (n := 3)

/-- The hypotheses of `tendsto_capacity_bsc_pow` hold together: the crossover probability
`ε = 1 / 4`, inside `(0, 1)` and away from `1 / 2` (where every cascade of at least one channel
already has capacity `0`). -/
example := ClassicalLean.InformationTheory.ChannelCapacity.tendsto_capacity_bsc_pow (ε := 1 / 4)
    (by norm_num) (by norm_num)
