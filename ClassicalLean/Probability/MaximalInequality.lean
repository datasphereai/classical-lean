/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.HittingTime
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.BorelCantelli

/-!
# Ville's inequality over finitely many steps, and the chance of falling to half

* `measureReal_exists_le_of_supermartingale` (Ville's inequality, finite horizon): for a
  nonnegative supermartingale `Z` and `c > 0`, the chance that `Z n ≥ c` for some `n ≤ N` is at
  most `E[Z 0] / c`.
* `measureReal_exists_le_half`: if a positive quantity `W` starts at `w₀` and `(w₀ / W n) ^ θ` is a
  supermartingale for some `θ > 0`, the chance that `W` falls to half its start within `N` steps is
  at most `2 ^ (-θ)`. For a fraction `x` of `W` staked on a bet that pays `b` times the stake with
  probability `p`, independently each time, `(w₀ / W n) ^ θ` is a supermartingale exactly when
  `p (1 + b x) ^ (-θ) + (1 - p) (1 - x) ^ (-θ) ≤ 1`.

## What Mathlib provides

Optional stopping in monotone form (`MeasureTheory.Submartingale.expected_stoppedValue_mono`),
hitting times as stopping times (`MeasureTheory.Adapted.isStoppingTime_hittingBtwn`,
`MeasureTheory.stoppedValue_hittingBtwn_mem`), integrability of stopped values, and Markov's
inequality (`MeasureTheory.mul_meas_ge_le_integral_of_nonneg`). Doob's maximal inequality is
there for submartingales (`MeasureTheory.maximal_ineq`); the supermartingale form proved here
(Ville's inequality) is not.
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

end ClassicalLean.Probability.MaximalInequality
