/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.HittingTime
import Mathlib.Analysis.SpecialFunctions.Pow.Real

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

end ClassicalLean.Probability.MaximalInequality
