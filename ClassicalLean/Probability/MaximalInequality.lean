/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.HittingTime
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.CondVar

/-!
# Ville's inequality over finitely many steps, the chance of falling to half, and Kolmogorov's
# maximal inequality

* `measureReal_exists_le_of_supermartingale` (Ville's inequality, finite horizon): for a
  nonnegative supermartingale `Z` and `c > 0`, the chance that `Z n ≥ c` for some `n ≤ N` is at
  most `E[Z 0] / c`.
* `measureReal_exists_le_half`: if a positive quantity `W` starts at `w₀` and `(w₀ / W n) ^ θ` is a
  supermartingale for some `θ > 0`, the chance that `W` falls to half its start within `N` steps is
  at most `2 ^ (-θ)`. For a fraction `x` of `W` staked on a bet that pays `b` times the stake with
  probability `p`, independently each time, `(w₀ / W n) ^ θ` is a supermartingale exactly when
  `p (1 + b x) ^ (-θ) + (1 - p) (1 - x) ^ (-θ) ≤ 1`.
* `submartingale_sq`: the square of a square-integrable martingale is a submartingale.
* `measureReal_exists_abs_ge_le` (Kolmogorov's maximal inequality, order LEAN-19): for a
  square-integrable martingale `S` and `ε > 0`, the chance that `|S k| ≥ ε` for some `k ≤ n` is at
  most `E[S n ²] / ε²`. It comes from Mathlib's `maximal_ineq` applied to `S ²`.

## Hypotheses of Kolmogorov's inequality

Measured in order LEAN-19's checks (check C23, exact enumeration of every path): the inequality
holds on 300 martingales of up to 6 steps with two-valued steps of mean `0`, some scaled by a
factor that depends on the past. Each of the three hypotheses below fails when dropped alone (the
cases are worked out by hand, not computed by the checks; the first and the third were also proved
false in Lean in review r23's scratch folder):

* the martingale: `S 0 = 1`, `S 1 = 0` for sure, `n = 1`, `ε = 1`: the chance is `1`, the bound
  `0`; the same path makes `S ²` fall, so `submartingale_sq` fails too.
* square-integrability: on `[0, 1]` with length, `S k = x^(-1/2)` for every `k` (a martingale for
  the filtration that is the whole σ-algebra at every step) has `S ²` not integrable, so Lean's
  `E[S n ²]` is `0` while the chance at `ε = 1` is `1`; and `S ²` is then not a submartingale.
* `0 < ε`: with `S = 0` on a probability space, at `ε = 0` the chance is `1` and Lean's bound
  `0 / 0` is `0`; at `ε = -1` the chance is `1` and the bound `0`.

Not needed in full: only `S n` must be square-integrable, since each earlier `S k` is a
conditional mean of it (review r23 proved this form in a scratch file); the statement keeps the
order's "square-integrable martingale". The finite measure is assumed because `maximal_ineq` is.

## What Mathlib provides

Optional stopping in monotone form (`MeasureTheory.Submartingale.expected_stoppedValue_mono`),
hitting times as stopping times (`MeasureTheory.Adapted.isStoppingTime_hittingBtwn`,
`MeasureTheory.stoppedValue_hittingBtwn_mem`), integrability of stopped values, and Markov's
inequality (`MeasureTheory.mul_meas_ge_le_integral_of_nonneg`). Doob's maximal inequality is
there for submartingales (`MeasureTheory.maximal_ineq`); the supermartingale form proved here
(Ville's inequality) is not. Searched in order LEAN-19 (`grep -rniE` over Mathlib v4.34.0):
`kolmogorov.?s? (maximal|inequality)` 0, and no statement that the square of a martingale is a
submartingale; Mathlib has the conditional variance (`Probability/CondVar.lean`), used here.
It also has the conditional Jensen inequality
(`MeasureTheory/Function/ConditionalExpectation/CondJensen.lean`, `ConvexOn.map_condExp_le_univ`,
`Integrable.norm_condExp_rpow_le`), which this order's search missed and which gives another
proof of `submartingale_sq` (review r23).
-/

open MeasureTheory Filter Finset

namespace ClassicalLean.Probability.MaximalInequality

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {𝒢 : Filtration ℕ m0} [SigmaFiniteFiltration μ 𝒢]

/-- **Ville's inequality, finite horizon.** For a nonnegative supermartingale `Z` and `c > 0`,
`P(Z n ≥ c for some n ≤ N) ≤ E[Z 0] / c`. For a trader: if a quantity tends to shrink on average,
the chance it ever climbs to `c` times its expected start is at most `1 / c`. -/
theorem measureReal_exists_le_of_supermartingale {Z : ℕ → Ω → ℝ} (hZ : Supermartingale Z 𝒢 μ)
    (hnonneg : ∀ n ω, 0 ≤ Z n ω) {c : ℝ} (hc : 0 < c) (N : ℕ) :
    μ.real {ω | ∃ n ≤ N, c ≤ Z n ω} ≤ (∫ ω, Z 0 ω ∂μ) / c := by
  set τ : Ω → ℕ := fun ω ↦ hittingBtwn Z {y : ℝ | c ≤ y} 0 N ω with hτdef
  have hτ : IsStoppingTime 𝒢 (fun ω ↦ (τ ω : WithTop ℕ)) :=
    hZ.1.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hτN : ∀ ω, (τ ω : WithTop ℕ) ≤ N := fun ω ↦ WithTop.coe_le_coe.mpr (hittingBtwn_le ω)
  have h0 := isStoppingTime_const 𝒢 (0 : ℕ)
  have hle : ∀ ω, ((0 : ℕ) : WithTop ℕ) ≤ (τ ω : WithTop ℕ) := fun ω ↦
    WithTop.coe_le_coe.mpr (Nat.zero_le _)
  -- `-Z` is a submartingale, so `E[(-Z)_0] ≤ E[(-Z)_τ]`, i.e. `E[Z_τ] ≤ E[Z_0]`
  have hmono := hZ.neg.expected_stoppedValue_mono h0 hτ (fun ω ↦ hle ω) hτN
  rw [stoppedValue_const] at hmono
  have hsv : stoppedValue (-Z) (fun ω ↦ (τ ω : WithTop ℕ)) =
      fun ω ↦ -stoppedValue Z (fun ω ↦ (τ ω : WithTop ℕ)) ω := by
    funext ω; simp [stoppedValue]
  rw [hsv, integral_neg] at hmono
  have h2 : ∫ ω, (-Z) 0 ω ∂μ = -∫ ω, Z 0 ω ∂μ := by
    simp only [Pi.neg_apply]; exact integral_neg _
  rw [h2] at hmono
  have hEZ : ∫ ω, stoppedValue Z (fun ω ↦ (τ ω : WithTop ℕ)) ω ∂μ ≤ ∫ ω, Z 0 ω ∂μ := by linarith
  -- on the event, the stopped value is at least `c`
  have hsub : {ω | ∃ n ≤ N, c ≤ Z n ω} ⊆
      {ω | c ≤ stoppedValue Z (fun ω ↦ (τ ω : WithTop ℕ)) ω} := by
    rintro ω ⟨n, hn, hcn⟩
    have hmem := stoppedValue_hittingBtwn_mem (u := Z) (s := {y : ℝ | c ≤ y}) (n := 0) (m := N)
      (ω := ω) ⟨n, ⟨Nat.zero_le _, hn⟩, hcn⟩
    simpa [stoppedValue] using hmem
  have hint : Integrable (stoppedValue Z (fun ω ↦ (τ ω : WithTop ℕ))) μ :=
    integrable_stoppedValue ℕ hτ hZ.integrable hτN
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun ω ↦ by simp only [Pi.zero_apply, stoppedValue]; exact hnonneg _ _)
    hint c
  have hmeas : μ.real {ω | ∃ n ≤ N, c ≤ Z n ω} ≤
      μ.real {ω | c ≤ stoppedValue Z (fun ω ↦ (τ ω : WithTop ℕ)) ω} := measureReal_mono hsub
  rw [le_div_iff₀ hc]
  nlinarith

/-- **The chance of falling to half.** If `W` is positive, starts at `w₀ > 0`, and
`(w₀ / W n) ^ θ` is a supermartingale for some `θ > 0`, then
`P(W n ≤ w₀ / 2 for some n ≤ N) ≤ 2 ^ (-θ)`. For a trader: betting a fixed fraction with a
positive edge, the chance of ever halving the account is bounded by `2 ^ (-θ)`, where a larger
`θ` (a smaller fraction) gives a smaller chance. -/
theorem measureReal_exists_le_half {W : ℕ → Ω → ℝ} {w₀ θ : ℝ} (hw₀ : 0 < w₀) (hθ : 0 < θ)
    (hW : ∀ n ω, 0 < W n ω) (hstart : ∀ ω, W 0 ω = w₀)
    (hZ : Supermartingale (fun n ω ↦ (w₀ / W n ω) ^ θ) 𝒢 μ) [IsProbabilityMeasure μ] (N : ℕ) :
    μ.real {ω | ∃ n ≤ N, W n ω ≤ w₀ / 2} ≤ (2 : ℝ) ^ (-θ) := by
  have hc : (0 : ℝ) < 2 ^ θ := Real.rpow_pos_of_pos two_pos θ
  have hville := measureReal_exists_le_of_supermartingale hZ
    (fun n ω ↦ Real.rpow_nonneg (div_pos hw₀ (hW n ω)).le θ) hc N
  have hZ0 : ∫ ω, (fun n ω ↦ (w₀ / W n ω) ^ θ) 0 ω ∂μ = 1 := by
    simp [hstart, div_self hw₀.ne']
  rw [hZ0] at hville
  have hsub : {ω | ∃ n ≤ N, W n ω ≤ w₀ / 2} ⊆
      {ω | ∃ n ≤ N, (2 : ℝ) ^ θ ≤ (fun n ω ↦ (w₀ / W n ω) ^ θ) n ω} := by
    rintro ω ⟨n, hn, hhalf⟩
    refine ⟨n, hn, ?_⟩
    have h2 : (2 : ℝ) ≤ w₀ / W n ω := by
      rw [le_div_iff₀ (hW n ω)]; linarith
    exact Real.rpow_le_rpow two_pos.le h2 hθ.le
  calc μ.real {ω | ∃ n ≤ N, W n ω ≤ w₀ / 2}
      ≤ μ.real {ω | ∃ n ≤ N, (2 : ℝ) ^ θ ≤ (fun n ω ↦ (w₀ / W n ω) ^ θ) n ω} :=
        measureReal_mono hsub
    _ ≤ 1 / 2 ^ θ := hville
    _ = (2 : ℝ) ^ (-θ) := by rw [Real.rpow_neg two_pos.le, one_div]

/-- **The condition behind `measureReal_exists_le_half`, as an exact check.** For a bet that pays
`b` times the stake with probability `p` and loses the stake otherwise, staking the fraction `x`
each time, and a whole-number `θ`: `p / (1 + b x) ^ θ + (1 - p) / (1 - x) ^ θ ≤ 1`, decided exactly
on rationals. `ruinConditionOK_iff` says this is the real-number condition. A program citing
`measureReal_exists_le_half` must check this for its actual `p`, `b`, `x`. -/
def ruinConditionOK (p b x : ℚ) (θ : ℕ) : Bool :=
  decide (p / (1 + b * x) ^ θ + (1 - p) / (1 - x) ^ θ ≤ 1)

/-- `ruinConditionOK` holds exactly when the real condition
`p (1 + b x) ^ (-θ) + (1 - p) (1 - x) ^ (-θ) ≤ 1` holds (with `0 < 1 + b x` and `0 < 1 - x`). -/
theorem ruinConditionOK_iff {p b x : ℚ} (θ : ℕ) (hu : 0 < 1 + b * x) (hv : 0 < 1 - x) :
    ruinConditionOK p b x θ = true ↔
      (p : ℝ) * (1 + b * x : ℝ) ^ (-(θ : ℝ)) + (1 - p) * (1 - x : ℝ) ^ (-(θ : ℝ)) ≤ 1 := by
  have hu' : (0 : ℝ) < 1 + (b : ℝ) * x := by exact_mod_cast hu
  have hv' : (0 : ℝ) < 1 - (x : ℝ) := by exact_mod_cast hv
  rw [Real.rpow_neg hu'.le, Real.rpow_neg hv'.le, Real.rpow_natCast, Real.rpow_natCast]
  simp only [ruinConditionOK, decide_eq_true_eq, div_eq_mul_inv]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

section Independent

open ProbabilityTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Products of independent factors with mean at most `1` form a supermartingale.** For
independent, bounded, nonnegative `G i` with `E[G (i+1)] ≤ 1`, the running product
`∏ i < n, G (i + 1)` is a supermartingale for the natural filtration of `G`. For a trader: when
each step's factor averages at most `1` and the steps are independent, the running product
shrinks on average. -/
theorem supermartingale_prod {G : ℕ → Ω → ℝ} (hG : ∀ i, StronglyMeasurable (G i))
    (hind : iIndepFun G μ) {K : ℝ} (hnn : ∀ i ω, 0 ≤ G i ω) (hK : ∀ i ω, G i ω ≤ K)
    (hmean : ∀ i, ∫ ω, G (i + 1) ω ∂μ ≤ 1) :
    Supermartingale (fun n ω ↦ ∏ i ∈ range n, G (i + 1) ω) (Filtration.natural G hG) μ := by
  have hZnn : ∀ n ω, 0 ≤ ∏ i ∈ range n, G (i + 1) ω := fun n ω ↦
    prod_nonneg fun i _ ↦ hnn _ _
  have hZbd : ∀ n ω, ∏ i ∈ range n, G (i + 1) ω ≤ K ^ n := fun n ω ↦ by
    calc ∏ i ∈ range n, G (i + 1) ω ≤ ∏ _i ∈ range n, K :=
          Finset.prod_le_prod₀ (fun i _ ↦ hnn _ _) (fun i _ ↦ hK _ _)
      _ = K ^ n := by rw [prod_const, card_range]
  have hadp : StronglyAdapted (Filtration.natural G hG) (fun n ω ↦ ∏ i ∈ range n, G (i + 1) ω) := by
    intro n
    change StronglyMeasurable[Filtration.natural G hG n] (fun ω ↦ ∏ i ∈ range n, G (i + 1) ω)
    have : (fun ω ↦ ∏ i ∈ range n, G (i + 1) ω) = ∏ i ∈ range n, G (i + 1) := by
      funext ω; simp [Finset.prod_apply]
    rw [this]
    refine Finset.stronglyMeasurable_prod _ fun i hi ↦ ?_
    exact (Filtration.stronglyAdapted_natural hG (i + 1)).mono
      (Filtration.mono _ (by simpa using Finset.mem_range.mp hi))
  have hint : ∀ n, Integrable (fun ω ↦ ∏ i ∈ range n, G (i + 1) ω) μ := fun n ↦
    Integrable.of_bound ((hadp n).mono ((Filtration.natural G hG).le n)).aestronglyMeasurable
      (K ^ n)
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hZnn n ω)]; exact hZbd n ω)
  have hGint : ∀ i, Integrable (G i) μ := fun i ↦
    Integrable.of_bound (hG i).aestronglyMeasurable K
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (hnn i ω)]; exact hK i ω)
  refine supermartingale_nat hadp hint fun n ↦ ?_
  have hsplit : (fun ω ↦ ∏ i ∈ range (n + 1), G (i + 1) ω) =
      (fun ω ↦ ∏ i ∈ range n, G (i + 1) ω) * G (n + 1) := by
    funext ω; simp [prod_range_succ]
  rw [hsplit]
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := Filtration.natural G hG n) (μ := μ)
    (hadp n) (by rw [← hsplit]; exact hint (n + 1)) (hGint (n + 1))
  have hindep := hind.condExp_natural_ae_eq_of_lt hG (Nat.lt_succ_self n)
  filter_upwards [hpull, hindep] with ω h1 h2
  rw [h1, Pi.mul_apply, h2]
  exact mul_le_of_le_one_right (hZnn n ω) (hmean n)

/-- **The chance of falling to half, for independent bets.** Let `W n = w₀ · ∏ i < n, F (i + 1)`
with independent step factors `F i` in `[lo, hi]`, `0 < lo`, and suppose `E[F i ^ (-θ)] ≤ 1`
for some `θ > 0`. Then `P(W n ≤ w₀ / 2 for some n ≤ N) ≤ 2 ^ (-θ)`. Here the supermartingale is
proved, not assumed. The remaining condition is about one bet: for a bet paying `b` times the
stake with probability `p` (fraction `x` staked) it reads
`p (1 + b x) ^ (-θ) + (1 - p) (1 - x) ^ (-θ) ≤ 1`, which `ruinConditionOK` checks exactly. For a
trader: if that check passes for the actual bet, the chance of ever halving within `N` bets is
at most `2 ^ (-θ)`. -/
theorem measureReal_exists_le_half_of_iIndepFun {F : ℕ → Ω → ℝ} (hF : ∀ i, StronglyMeasurable (F i))
    (hind : iIndepFun F μ) {lo hi : ℝ} (hlo : 0 < lo) (hbd : ∀ i ω, lo ≤ F i ω ∧ F i ω ≤ hi)
    {θ : ℝ} (hθ : 0 < θ) (hmean : ∀ i, ∫ ω, F i ω ^ (-θ) ∂μ ≤ 1) {w₀ : ℝ} (hw₀ : 0 < w₀)
    (N : ℕ) :
    μ.real {ω | ∃ n ≤ N, w₀ * ∏ i ∈ range n, F (i + 1) ω ≤ w₀ / 2} ≤ (2 : ℝ) ^ (-θ) := by
  set G : ℕ → Ω → ℝ := fun i ω ↦ F i ω ^ (-θ) with hGdef
  have hFpos : ∀ i ω, 0 < F i ω := fun i ω ↦ hlo.trans_le (hbd i ω).1
  have hGm : ∀ i, StronglyMeasurable (G i) := fun i ↦
    ((hF i).measurable.pow_const (-θ)).stronglyMeasurable
  have hGind : iIndepFun G μ :=
    hind.comp (fun _ x ↦ x ^ (-θ)) (fun _ ↦ measurable_id.pow_const (-θ))
  have hGnn : ∀ i ω, 0 ≤ G i ω := fun i ω ↦ Real.rpow_nonneg (hFpos i ω).le _
  have hGK : ∀ i ω, G i ω ≤ lo ^ (-θ) := fun i ω ↦
    Real.rpow_le_rpow_of_nonpos hlo (hbd i ω).1 (by linarith)
  have hsuper := supermartingale_prod hGm hGind hGnn hGK (fun i ↦ hmean (i + 1))
  have hville := measureReal_exists_le_of_supermartingale hsuper
    (fun n ω ↦ prod_nonneg fun i _ ↦ hGnn _ _) (Real.rpow_pos_of_pos two_pos θ) N
  have hZ0 : ∫ ω, (fun n ω ↦ ∏ i ∈ range n, G (i + 1) ω) 0 ω ∂μ = 1 := by simp
  rw [hZ0] at hville
  have hsub : {ω | ∃ n ≤ N, w₀ * ∏ i ∈ range n, F (i + 1) ω ≤ w₀ / 2} ⊆
      {ω | ∃ n ≤ N, (2 : ℝ) ^ θ ≤ ∏ i ∈ range n, G (i + 1) ω} := by
    rintro ω ⟨n, hn, hhalf⟩
    refine ⟨n, hn, ?_⟩
    have hP : 0 < ∏ i ∈ range n, F (i + 1) ω := prod_pos fun i _ ↦ hFpos _ _
    have hP2 : ∏ i ∈ range n, F (i + 1) ω ≤ 1 / 2 := by
      have := hhalf; rw [show w₀ / 2 = w₀ * (1 / 2) by ring] at this
      exact le_of_mul_le_mul_left this hw₀
    have hprod : ∏ i ∈ range n, G (i + 1) ω = (∏ i ∈ range n, F (i + 1) ω) ^ (-θ) := by
      rw [hGdef, Real.finsetProd_rpow _ _ (fun i _ ↦ (hFpos _ _).le)]
    rw [hprod, Real.rpow_neg hP.le, ← Real.inv_rpow hP.le]
    apply Real.rpow_le_rpow two_pos.le _ hθ.le
    rw [le_inv_comm₀ two_pos hP]; linarith
  calc μ.real {ω | ∃ n ≤ N, w₀ * ∏ i ∈ range n, F (i + 1) ω ≤ w₀ / 2}
      ≤ μ.real {ω | ∃ n ≤ N, (2 : ℝ) ^ θ ≤ ∏ i ∈ range n, G (i + 1) ω} := measureReal_mono hsub
    _ ≤ 1 / 2 ^ θ := hville
    _ = (2 : ℝ) ^ (-θ) := by rw [Real.rpow_neg two_pos.le, one_div]

end Independent

section Kolmogorov

open ProbabilityTheory
open scoped NNReal

omit [SigmaFiniteFiltration μ 𝒢] in
/-- **The square of a martingale is a submartingale.** If `S` is a martingale and each `S n` is
square-integrable, then `S n ²` is a submartingale. Given the past, the mean of `S j ²` exceeds
the square of the mean of `S j`, which is `S i ²`, by the conditional variance (Mathlib's
`condVar_ae_eq_condExp_sq_sub_sq_condExp`), which is at least `0`. -/
theorem submartingale_sq {S : ℕ → Ω → ℝ} (hS : Martingale S 𝒢 μ) (hS2 : ∀ n, MemLp (S n) 2 μ) :
    Submartingale (fun n ω ↦ S n ω ^ 2) 𝒢 μ := by
  refine ⟨fun n ↦ (hS.1 n).pow 2, fun i j hij ↦ ?_, fun n ↦ (hS2 n).integrable_sq⟩
  have hv := condVar_ae_eq_condExp_sq_sub_sq_condExp (𝒢.le i) (hS2 j)
  have hnn : 0 ≤ᵐ[μ] Var[S j; μ | 𝒢 i] := by
    unfold condVar
    exact condExp_nonneg (ae_of_all _ fun ω ↦ sq_nonneg ((S j - μ[S j | 𝒢 i]) ω))
  have hm := hS.condExp_ae_eq hij
  change (fun ω ↦ S i ω ^ 2) ≤ᵐ[μ] μ[S j ^ 2 | 𝒢 i]
  filter_upwards [hv, hnn, hm] with ω hv hnn hm
  simp only [Pi.sub_apply, Pi.pow_apply, Pi.zero_apply] at hv hnn hm ⊢
  rw [hv, hm] at hnn
  linarith

omit [SigmaFiniteFiltration μ 𝒢] in
/-- **Kolmogorov's maximal inequality.** For a martingale `S` with each `S n` square-integrable
and `ε > 0`, the chance that `|S k| ≥ ε` for some `k ≤ n` is at most `E[S n ²] / ε²`. It is
Doob's maximal inequality (Mathlib's `maximal_ineq`), used and not proved again, applied to the
nonnegative submartingale `S ²` (`submartingale_sq`) at the level `ε²`. For sums of independent
steps of mean `0` this gives the classical statement, once their partial sums are shown to be a
martingale, which is not done here. -/
theorem measureReal_exists_abs_ge_le {S : ℕ → Ω → ℝ} (hS : Martingale S 𝒢 μ)
    (hS2 : ∀ n, MemLp (S n) 2 μ) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    μ.real {ω | ∃ k ≤ n, ε ≤ |S k ω|} ≤ (∫ ω, S n ω ^ 2 ∂μ) / ε ^ 2 := by
  set e : ℝ≥0 := ⟨ε ^ 2, by positivity⟩
  have he : (e : ℝ) = ε ^ 2 := rfl
  have hmax := maximal_ineq (submartingale_sq hS hS2) (fun n ω ↦ sq_nonneg (S n ω)) (ε := e) n
  have hset : {ω | ((e : ℝ)) ≤ (range (n + 1)).sup' nonempty_range_add_one
      (fun k ↦ S k ω ^ 2)} = {ω | ∃ k ≤ n, ε ≤ |S k ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, he, le_sup'_iff, mem_range, Nat.lt_succ_iff]
    refine exists_congr fun k ↦ and_congr_right fun _ ↦ ?_
    rw [sq_le_sq, abs_of_pos hε]
  rw [hset] at hmax
  set A := {ω | ∃ k ≤ n, ε ≤ |S k ω|}
  have hint : ∫ ω in A, S n ω ^ 2 ∂μ ≤ ∫ ω, S n ω ^ 2 ∂μ :=
    setIntegral_le_integral (hS2 n).integrable_sq (ae_of_all _ fun ω ↦ sq_nonneg _)
  have h1 : (↑e * μ A).toReal ≤ ∫ ω in A, S n ω ^ 2 ∂μ := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmax
    rwa [ENNReal.toReal_ofReal (integral_nonneg fun ω ↦ sq_nonneg (S n ω))] at this
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, he] at h1
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact h1.trans hint

end Kolmogorov

end ClassicalLean.Probability.MaximalInequality
