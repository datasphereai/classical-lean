/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.Martingale.OptionalStopping

/-!
# No stopping rule beats a fair game

If `f n` is a martingale (each step's expected change is `0` given everything up to that step),
then for any stopping rule `τ` that never waits past a fixed time `N`, the expected value at the
moment of stopping equals the expected value at the start (`integral_stoppedValue_eq`). Deciding
*when* to stop, using only what has happened so far, cannot turn a fair game into a favourable one.

## What Mathlib provides

The optional stopping theorem in its monotone form,
`MeasureTheory.Submartingale.expected_stoppedValue_mono`: for a submartingale and bounded stopping
times `τ ≤ π`, `E[f_τ] ≤ E[f_π]`. This module applies it to the martingale and to its negative,
with the constant stopping time `0`, to get equality.
-/

open MeasureTheory

namespace ClassicalLean.Probability.FairGame

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}
  [SigmaFiniteFiltration μ 𝒢]

/-- **No stopping rule beats a fair game.** For a real martingale `f` and a stopping time `τ` with
`τ ≤ N` everywhere, `E[f_τ] = E[f_0]`. -/
theorem integral_stoppedValue_eq {f : ℕ → Ω → ℝ} (hf : Martingale f 𝒢 μ) {τ : Ω → WithTop ℕ}
    (hτ : IsStoppingTime 𝒢 τ) {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    ∫ ω, stoppedValue f τ ω ∂μ = ∫ ω, f 0 ω ∂μ := by
  have h0 := isStoppingTime_const 𝒢 (0 : ℕ)
  have hle : ∀ ω, ((0 : ℕ) : WithTop ℕ) ≤ τ ω := fun ω ↦ by
    cases τ ω with
    | top => exact le_top
    | coe n => exact WithTop.coe_le_coe.mpr (Nat.zero_le n)
  have up := hf.submartingale.expected_stoppedValue_mono h0 hτ (fun ω ↦ hle ω) hbdd
  have dn := hf.neg.submartingale.expected_stoppedValue_mono h0 hτ (fun ω ↦ hle ω) hbdd
  rw [stoppedValue_const] at up dn
  have hneg : stoppedValue (-f) τ = fun ω ↦ -stoppedValue f τ ω := by
    funext ω; simp [stoppedValue]
  rw [hneg, integral_neg] at dn
  have h2 : ∫ ω, (-f) 0 ω ∂μ = -∫ ω, f 0 ω ∂μ := by
    simp only [Pi.neg_apply]; exact integral_neg _
  rw [h2] at dn
  linarith

end ClassicalLean.Probability.FairGame
