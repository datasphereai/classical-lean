/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Simplex.Hessian
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# One choice of threshold, and the constants it determines

The general theory in `ClassicalLean.Simplex.Gibbs` and `ClassicalLean.Simplex.Hessian` never
fixes a numerical value. This file records one particular choice and works out what follows
from it.

**The choice.** `designThreshold = 1/φ`, the reciprocal of the golden ratio, as the value of the
distinguished coordinate. This value is *chosen*, not derived: nothing in the previous two files
singles it out, and every theorem there holds for any interior point.

**What the choice determines.** `existsUnique_temperature` says that once an interior point is
named, exactly one temperature makes it a critical point of the restricted free energy. For
`designThreshold` with two equal remaining coordinates that temperature is
`designTemperature = φ / log (2φ)`; with three, it is `designTemperature₃ = φ / log (3φ)`. These
two constants are therefore *determined* by the choice — see `criticalTemperature_two_eq` and
`criticalTemperature_three_eq` — but the choice itself is free.

## Main results

* `designThreshold_mem_Ioo`, `one_third_lt_designThreshold`, `one_quarter_lt_designThreshold` —
  the chosen point is interior, and lies above the uniform point of both simplices.
* `criticalTemperature_two_eq`, `criticalTemperature_three_eq` — the determined temperatures in
  closed form.
* `deriv_symFreeEnergy_designTemperature`, `designTemperature_unique` — at `designTemperature`
  the chosen point is a critical point of the restricted free energy on the two-dimensional
  simplex, and no other temperature does that; `deriv_symFreeEnergy₃_designTemperature₃` and
  `designTemperature₃_unique` are the same statements on the three-dimensional simplex.
* `isMinOn_designThreshold` — it is then the global minimiser on `(0,1)`.
* `gibbsWeight_designTemperature` — equivalently, the chosen point is its own Gibbs weight
  against two degenerate states at energy gap `φ`.
* `designPoint`, `designPoint_mem_openSimplex` — the resulting point `(1/φ, 1/(2φ²), 1/(2φ²))`
  of the two-dimensional open simplex.
* `deriv_chartFreeEnergy_fst_designPoint`, `deriv_chartFreeEnergy_snd_designPoint` — both
  partial derivatives of `chartFreeEnergy`, the free energy read in the chart of
  `ClassicalLean.Simplex.Hessian`, vanish there, and not only the one along the
  equal-coordinate locus. What is *not* proved, here or anywhere in this library: that the
  chart parametrises the open simplex — `mem_openSimplex_chart` gives one inclusion and no
  more — or any statement about a derivative of `freeEnergy` itself on `openSimplex (Fin 3)`.
  "Critical point of the free energy on the simplex" is context, not a theorem here.
* `hess11_at_designPoint`, `hess22_at_designPoint`, `hess12_at_designPoint` and
  `hessian_posDef_at_designPoint` — the Hessian entries at the resulting point, in closed form
  over `φ` and `designTemperature`, and its positive-definiteness;
  `hess_trace_at_designPoint` and `hess_det_at_designPoint` are the resulting closed forms of
  the trace and the determinant.
* `one_lt_designTemperature` — the determined temperature exceeds `1`.
* `log_two_goldenRatio`, `log_three_goldenRatio` — the two logarithm splittings, and
  `goldenRatio_sq_add_goldenConj_sq` the trace identity `φ² + ψ² = 3`.

## Not ported from the source

The following source material has no counterpart in this library, for the reasons
given.

* The decimal-literal constants and every fact about them — minimum and maximum eigenvalue
  bounds, a convergence modulus, time constants, a condition number, decay and recovery
  bounds, and a numerical temperature: dropped. Each is an inequality between chosen decimals,
  so it records an arithmetic check on numbers this port replaced by symbolic statements.
* The golden-ratio algebra of the source (positivity, bounds, the two Vieta relations, the
  reciprocal identities, and their duplicates in a second source module): dropped as
  superseded. Mathlib's `Real.goldenRatio_pos`, `goldenRatio_lt_two`, `goldenRatio_sq`,
  `goldenRatio_add_goldenConj` and `goldenRatio_mul_goldenConj` are used directly instead.
  Dated 2026-09-24 (order G-7, J2 step 6; round 23): two duplicates had shipped here all the
  same, `goldenConj_sq_eq_inv_goldenRatio_sq` and `goldenRatio_sq_add_inv_sq`; they are
  deleted, and the two statements are proved once, in `GoldenRatio/Characterisations`
  (`inv_goldenRatio_sq_eq_goldenConj_sq`, `goldenRatio_sq_add_inv_eq_three`).
* The source's summary conjunctions and named bundles, which collect several already-shipped
  facts into one `∧`-chain: dropped. A conjunction of theorems is not a theorem the library
  lacks.
* The source's small arithmetic facts about `2φ` — its positivity, that it exceeds `1`, and
  that `log (2φ) ≠ 0` — together with `1 + φ⁻¹ = φ`: dropped as trivia already covered.
  `log_two_goldenRatio_pos` above is the only one anything here needs, and
  `ClassicalLean.GoldenRatio.one_add_inv_goldenRatio` is the last of them.
* The three-coordinate normalisation `λ* + 3ρ* = 1`: dropped because it is `ring`-true of any
  `x` in place of `λ*` once `ρ* = (1-x)/3`, so it asserts nothing about the chosen threshold.
* The bridge family built on a real exponent `2 ^ (log₂ φ) = φ`: dropped. Its source names are
  project vocabulary this library does not carry, and the mathematics is one application of
  `Real.rpow_logb`, on which nothing else here depends.
* A convergent optimiser flow with a limit theorem, and a four-coordinate development: both
  dropped. Neither has any counterpart in this library, and porting either is new work — a
  `Tendsto` statement and a four-dimensional simplex — rather than a restatement.
-/

open Real Set

namespace ClassicalLean.Simplex

/-! ## Golden-ratio algebra

`Real.goldenRatio` is a reducible abbreviation, so `field_simp` would expand it into `√5`.
These auxiliary lemmas are stated for an abstract `x` satisfying `x² = x + 1`, which keeps the
algebra below symbolic. -/

private theorem one_sub_inv_of_sq {x : ℝ} (hx : 0 < x) (hsq : x ^ 2 = x + 1) :
    1 - x⁻¹ = (x ^ 2)⁻¹ := by
  have hx0 : x ≠ 0 := hx.ne'
  field_simp
  linarith [hsq]

/-- `c·x⁻¹ / (1 - x⁻¹) = c·x` when `x² = x + 1`. -/
private theorem mul_inv_div_one_sub_inv (c : ℝ) {x : ℝ} (hx : 0 < x) (hsq : x ^ 2 = x + 1) :
    c * x⁻¹ / (1 - x⁻¹) = c * x := by
  have hx0 : x ≠ 0 := hx.ne'
  rw [one_sub_inv_of_sq hx hsq]
  field_simp

/-- `1 / (x⁻¹ · L) = x / L` for nonzero `x` and `L`. -/
private theorem one_div_inv_mul {x L : ℝ} (hx : x ≠ 0) (hL : L ≠ 0) : 1 / (x⁻¹ * L) = x / L := by
  field_simp

/-- `y⁻¹ / 2 = (2y)⁻¹` for nonzero `y`. -/
private theorem inv_div_two_eq {y : ℝ} (hy : y ≠ 0) : y⁻¹ / 2 = (2 * y)⁻¹ := by
  field_simp

/-! ## The chosen threshold -/

/-- **Design constant.** The value chosen for the distinguished coordinate: the reciprocal of
the golden ratio. The value is chosen, not derived — the general theory holds at every interior
point of the simplex and singles out none of them. -/
noncomputable def designThreshold : ℝ := goldenRatio⁻¹

/-- The chosen threshold is positive. -/
theorem designThreshold_pos : 0 < designThreshold := inv_pos.mpr goldenRatio_pos

/-- `1 - 1/φ = 1/φ²`, from Mathlib's `Real.goldenRatio_sq`. -/
theorem one_sub_designThreshold : 1 - designThreshold = (goldenRatio ^ 2)⁻¹ :=
  one_sub_inv_of_sq goldenRatio_pos goldenRatio_sq

/-- The chosen threshold is below `1`, so it is an interior point of `(0,1)`. -/
theorem designThreshold_lt_one : designThreshold < 1 := by
  have hφ : (0 : ℝ) < goldenRatio := goldenRatio_pos
  have h := one_sub_designThreshold
  have hpos : (0 : ℝ) < (goldenRatio ^ 2)⁻¹ := by positivity
  linarith

/-- The two previous facts packaged as membership in `(0,1)`. -/
theorem designThreshold_mem_Ioo : designThreshold ∈ Ioo (0 : ℝ) 1 :=
  ⟨designThreshold_pos, designThreshold_lt_one⟩

/-- The chosen point lies above the uniform point `1/3` of the two-dimensional simplex, because
`φ < 2 < 3`. -/
theorem one_third_lt_designThreshold : 1 / ((2 : ℝ) + 1) < designThreshold := by
  have hφ : (0 : ℝ) < goldenRatio := goldenRatio_pos
  have h2 : goldenRatio < 2 := goldenRatio_lt_two
  rw [designThreshold, one_div, inv_lt_inv₀ (by norm_num) hφ]
  linarith

/-- The chosen point lies above the uniform point `1/4` of the three-dimensional simplex. -/
theorem one_quarter_lt_designThreshold : 1 / ((3 : ℝ) + 1) < designThreshold := by
  have hφ : (0 : ℝ) < goldenRatio := goldenRatio_pos
  have h2 : goldenRatio < 2 := goldenRatio_lt_two
  rw [designThreshold, one_div, inv_lt_inv₀ (by norm_num) hφ]
  linarith

/-! ## The determined temperatures -/

/-- **Determined constant.** The unique temperature at which `designThreshold` is a critical
point of the free energy restricted to the two equal-coordinate locus of the two-dimensional
simplex: `criticalTemperature_two_eq` identifies it with `criticalTemperature 2
designThreshold`, `deriv_symFreeEnergy_designTemperature` shows the derivative vanishes there,
and `designTemperature_unique` that no other temperature does. Determined, that is, by the
*chosen* threshold — the choice itself is free, see `designThreshold`. This is the library's
only declaration of the name; `ClassicalLean.Simplex.FisherRao` imports it. -/
noncomputable def designTemperature : ℝ := goldenRatio / Real.log (2 * goldenRatio)

/-- **Determined constant.** The same for three equal coordinates, on the three-dimensional
simplex; see `criticalTemperature_three_eq`. -/
noncomputable def designTemperature₃ : ℝ := goldenRatio / Real.log (3 * goldenRatio)

/-- At the chosen point the ratio appearing in the critical-point equation with two equal
coordinates is `2φ`. -/
theorem ratio_two_eq : 2 * designThreshold / (1 - designThreshold) = 2 * goldenRatio :=
  mul_inv_div_one_sub_inv 2 goldenRatio_pos goldenRatio_sq

/-- At the chosen point the ratio appearing in the critical-point equation with three equal
coordinates is `3φ`. -/
theorem ratio_three_eq : 3 * designThreshold / (1 - designThreshold) = 3 * goldenRatio :=
  mul_inv_div_one_sub_inv 3 goldenRatio_pos goldenRatio_sq

/-- `log (2φ) > 0`, since `2φ > 1`. -/
theorem log_two_goldenRatio_pos : 0 < Real.log (2 * goldenRatio) :=
  Real.log_pos (by linarith [one_lt_goldenRatio])

/-- `log (3φ) > 0`, since `3φ > 1`. -/
theorem log_three_goldenRatio_pos : 0 < Real.log (3 * goldenRatio) :=
  Real.log_pos (by linarith [one_lt_goldenRatio])

/-- The temperature determined by the chosen threshold, for two equal coordinates, is
`φ / log (2φ)`. -/
theorem criticalTemperature_two_eq :
    criticalTemperature 2 designThreshold = designTemperature := by
  rw [criticalTemperature, ratio_two_eq, designThreshold, designTemperature,
    one_div_inv_mul goldenRatio_pos.ne' log_two_goldenRatio_pos.ne']

/-- The temperature determined by the chosen threshold, for three equal coordinates, is
`φ / log (3φ)`. -/
theorem criticalTemperature_three_eq :
    criticalTemperature 3 designThreshold = designTemperature₃ := by
  rw [criticalTemperature, ratio_three_eq, designThreshold, designTemperature₃,
    one_div_inv_mul goldenRatio_pos.ne' log_three_goldenRatio_pos.ne']

/-- The determined temperature is positive. -/
theorem designTemperature_pos : 0 < designTemperature :=
  div_pos goldenRatio_pos log_two_goldenRatio_pos

/-- The determined three-coordinate temperature is positive. -/
theorem designTemperature₃_pos : 0 < designTemperature₃ :=
  div_pos goldenRatio_pos log_three_goldenRatio_pos

/-! ## The chosen point as an equilibrium -/

/-- At the determined temperature the chosen point is a critical point of the restricted free
energy on the two-dimensional simplex. -/
theorem deriv_symFreeEnergy_designTemperature :
    deriv (symFreeEnergy 2 designTemperature) designThreshold = 0 := by
  have h := deriv_symFreeEnergy_criticalTemperature (m := 2) (lam := designThreshold)
    (by norm_num) one_third_lt_designThreshold designThreshold_lt_one
  rwa [criticalTemperature_two_eq] at h

/-- At the determined temperature the chosen point is a critical point of the restricted free
energy on the three-dimensional simplex. -/
theorem deriv_symFreeEnergy₃_designTemperature₃ :
    deriv (symFreeEnergy 3 designTemperature₃) designThreshold = 0 := by
  have h := deriv_symFreeEnergy_criticalTemperature (m := 3) (lam := designThreshold)
    (by norm_num) one_quarter_lt_designThreshold designThreshold_lt_one
  rwa [criticalTemperature_three_eq] at h

/-- No other temperature makes the chosen point critical. This is the general uniqueness
statement `criticalTemperature_unique` at the chosen point. -/
theorem designTemperature_unique {T : ℝ}
    (h : deriv (symFreeEnergy 2 T) designThreshold = 0) : T = designTemperature := by
  rw [← criticalTemperature_two_eq]
  exact criticalTemperature_unique (by norm_num) one_third_lt_designThreshold
    designThreshold_lt_one h

/-- The same uniqueness on the three-dimensional simplex. -/
theorem designTemperature₃_unique {T : ℝ}
    (h : deriv (symFreeEnergy 3 T) designThreshold = 0) : T = designTemperature₃ := by
  rw [← criticalTemperature_three_eq]
  exact criticalTemperature_unique (by norm_num) one_quarter_lt_designThreshold
    designThreshold_lt_one h

/-- At the determined temperature the chosen point is the global minimiser of the restricted
free energy on `(0,1)`. -/
theorem isMinOn_designThreshold :
    IsMinOn (symFreeEnergy 2 designTemperature) (Ioo 0 1) designThreshold :=
  isMinOn_symFreeEnergy (by norm_num) designTemperature_pos designThreshold_pos
    designThreshold_lt_one deriv_symFreeEnergy_designTemperature

/-- Equivalently: at the determined temperature the chosen point is its own Gibbs weight
against two degenerate states at energy gap `φ`, since `1 / designThreshold = φ`. -/
theorem gibbsWeight_designTemperature :
    gibbsWeight 2 designTemperature goldenRatio = designThreshold := by
  have hinv : 1 / designThreshold = goldenRatio := by
    rw [designThreshold, one_div, inv_inv]
  have h := (deriv_symFreeEnergy_eq_zero_iff_gibbsWeight (m := 2) (T := designTemperature)
    (lam := designThreshold) (by norm_num) designTemperature_pos designThreshold_pos
    designThreshold_lt_one).mp deriv_symFreeEnergy_designTemperature
  rwa [hinv] at h

/-! ## The Hessian at the resulting point -/

/-- The second coordinate of the resulting point of the two-dimensional simplex: with the two
remaining coordinates equal, each is `(1 - 1/φ)/2 = 1/(2φ²)`. -/
noncomputable def designSecond : ℝ := (1 - designThreshold) / 2

/-- Closed form of the second coordinate: `(1 - 1/φ)/2 = 1/(2φ²)`. -/
theorem designSecond_eq : designSecond = (2 * goldenRatio ^ 2)⁻¹ := by
  have hφ : (0 : ℝ) < goldenRatio := goldenRatio_pos
  rw [designSecond, one_sub_designThreshold, inv_div_two_eq (by positivity)]

/-- The second coordinate is positive. -/
theorem designSecond_pos : 0 < designSecond := by
  have hφ : (0 : ℝ) < goldenRatio := goldenRatio_pos
  rw [designSecond_eq]
  positivity

/-- The third coordinate equals the second, both `1/(2φ²)`. -/
theorem designThird_eq : 1 - designThreshold - designSecond = (2 * goldenRatio ^ 2)⁻¹ := by
  have hhalf : 1 - designThreshold - designSecond = designSecond := by
    rw [designSecond]; ring
  rw [hhalf, designSecond_eq]

/-- The third coordinate is positive, so the point is interior to the simplex. -/
theorem designThird_pos : 0 < 1 - designThreshold - designSecond := by
  have hφ : (0 : ℝ) < goldenRatio := goldenRatio_pos
  rw [designThird_eq]
  positivity

/-- The third coordinate equals the second, so the resulting point has its two non-distinguished
coordinates equal. This unfolds `designSecond`, which was defined as `(1 - designThreshold)/2`
in order to make it true, and closes by `ring`; it asserts nothing beyond that definition. It is
stated because `designPoint` is written with `designSecond` in both slots and this is what
licenses writing it that way. -/
theorem designThird_eq_designSecond : 1 - designThreshold - designSecond = designSecond := by
  rw [designSecond]; ring

/-- The point of the two-dimensional open simplex determined by the choice:
`(1/φ, 1/(2φ²), 1/(2φ²))`. -/
noncomputable def designPoint : Fin 3 → ℝ := ![designThreshold, designSecond, designSecond]

/-- The resulting point lies in the open probability simplex. -/
theorem designPoint_mem_openSimplex : designPoint ∈ openSimplex (Fin 3) := by
  have h : designPoint
      = ![designThreshold, designSecond, 1 - designThreshold - designSecond] := by
    rw [designPoint, designThird_eq_designSecond]
  rw [h]
  exact mem_openSimplex_chart designThreshold_pos designSecond_pos designThird_pos

/-- The partial derivative of `chartFreeEnergy` in the first chart coordinate is zero at the
resulting point. With `deriv_chartFreeEnergy_snd_designPoint` this says both chart partials
vanish. It says nothing about a derivative of `freeEnergy` on `openSimplex (Fin 3)`: that would
need the chart to be shown to parametrise the simplex, which is not proved here. -/
theorem deriv_chartFreeEnergy_fst_designPoint :
    deriv (fun l => chartFreeEnergy designTemperature l designSecond) designThreshold = 0 := by
  rw [(hasDerivAt_chartFreeEnergy_fst (T := designTemperature) (lam := designThreshold)
      (kap := designSecond) designThreshold_pos designThird_pos).deriv, designSecond,
    chartDerivFst_eq_symFreeEnergyDeriv designThreshold_pos designThreshold_lt_one,
    ← deriv_symFreeEnergy (m := 2) (by norm_num) designThreshold_pos designThreshold_lt_one]
  exact deriv_symFreeEnergy_designTemperature

/-- The partial derivative in the second chart coordinate is zero at the resulting point, since
its two non-distinguished coordinates are equal. -/
theorem deriv_chartFreeEnergy_snd_designPoint :
    deriv (fun k => chartFreeEnergy designTemperature designThreshold k) designSecond = 0 := by
  rw [(hasDerivAt_chartFreeEnergy_snd (T := designTemperature) (lam := designThreshold)
      (kap := designSecond) designSecond_pos designThird_pos).deriv, designSecond,
    chartDerivSnd_of_eq]

/-- The `(1,1)` Hessian entry at the resulting point: `φ² + T·(φ + 2φ²)`. -/
theorem hess11_at_designPoint :
    hess11 designTemperature designThreshold designSecond
      = goldenRatio ^ 2 + designTemperature * (goldenRatio + 2 * goldenRatio ^ 2) := by
  rw [hess11, designThird_eq, designThreshold, inv_pow, inv_inv, inv_inv, inv_inv]

/-- The `(2,2)` Hessian entry at the resulting point: `4·T·φ²`. -/
theorem hess22_at_designPoint :
    hess22 designTemperature designThreshold designSecond
      = 4 * designTemperature * goldenRatio ^ 2 := by
  rw [hess22, designThird_eq, designSecond_eq, inv_inv]
  ring

/-- The off-diagonal Hessian entry at the resulting point: `2·T·φ²`. -/
theorem hess12_at_designPoint :
    hess12 designTemperature designThreshold designSecond
      = 2 * designTemperature * goldenRatio ^ 2 := by
  rw [hess12, designThird_eq, inv_inv]
  ring

/-- The trace of the Hessian at the resulting point: `φ² + T·φ + 6·T·φ²`. -/
theorem hess_trace_at_designPoint :
    hess11 designTemperature designThreshold designSecond
        + hess22 designTemperature designThreshold designSecond
      = goldenRatio ^ 2 + designTemperature * goldenRatio
        + 6 * designTemperature * goldenRatio ^ 2 := by
  rw [hess11_at_designPoint, hess22_at_designPoint]
  ring

/-- The determinant of the Hessian at the resulting point:
`4·T·φ⁴ + 4·T²·φ³ + 4·T²·φ⁴`. -/
theorem hess_det_at_designPoint :
    hess11 designTemperature designThreshold designSecond
        * hess22 designTemperature designThreshold designSecond
        - hess12 designTemperature designThreshold designSecond ^ 2
      = 4 * designTemperature * goldenRatio ^ 4
        + 4 * designTemperature ^ 2 * goldenRatio ^ 3
        + 4 * designTemperature ^ 2 * goldenRatio ^ 4 := by
  rw [hess11_at_designPoint, hess22_at_designPoint, hess12_at_designPoint]
  ring

/-- The Hessian is positive definite at the resulting point. This is the general
`hessian_posDef` instantiated there; nothing about the particular numbers enters the proof. -/
theorem hessian_posDef_at_designPoint :
    (hessian designTemperature designThreshold designSecond).PosDef :=
  hessian_posDef designTemperature_pos designThreshold_pos designSecond_pos designThird_pos

/-! ## Size of the determined temperature -/

/-- `log (2φ) = log 2 + log φ`, a one-line instance of Mathlib's `Real.log_mul`. -/
theorem log_two_goldenRatio : Real.log (2 * goldenRatio) = Real.log 2 + Real.log goldenRatio :=
  Real.log_mul two_ne_zero goldenRatio_pos.ne'

/-- `log (3φ) = log 3 + log φ`, the three-level analogue of `log_two_goldenRatio`. -/
theorem log_three_goldenRatio :
    Real.log (3 * goldenRatio) = Real.log 3 + Real.log goldenRatio :=
  Real.log_mul three_ne_zero goldenRatio_pos.ne'

/-- **Trace identity.** `φ² + ψ² = 3`, where `ψ` is the conjugate root. Immediate from
Mathlib's `Real.goldenRatio_sq`, `Real.goldenConj_sq` and `Real.goldenRatio_add_goldenConj`. -/
theorem goldenRatio_sq_add_goldenConj_sq : goldenRatio ^ 2 + goldenConj ^ 2 = 3 := by
  have h1 := goldenRatio_sq
  have h2 := goldenConj_sq
  have h3 := goldenRatio_add_goldenConj
  linarith

/-- The determined temperature exceeds `1`, because `log (2φ) < φ`: `log 2 < 1` and
`log φ ≤ φ - 1`. -/
theorem one_lt_designTemperature : 1 < designTemperature := by
  have hφ : (0 : ℝ) < goldenRatio := goldenRatio_pos
  have hlog := log_two_goldenRatio_pos
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
    linarith
  have hlogφ : Real.log goldenRatio ≤ goldenRatio - 1 := Real.log_le_sub_one_of_pos hφ
  have hlt : Real.log (2 * goldenRatio) < goldenRatio := by
    rw [log_two_goldenRatio]; linarith
  rw [designTemperature, lt_div_iff₀ hlog]
  linarith

end ClassicalLean.Simplex
