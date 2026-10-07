/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Probability.FirstOrderRecursion
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Independence.Basic

/-!
# How much one quantity predicts another, and the lag correlation of the first-order recursion

**Best linear prediction.** For `X`, `Y` with finite second moments and `Var X > 0`, the leftover
`Var[Y - c X] = E[(Y - EY - c (X - EX))²]` is least exactly at `c* = Cov(X, Y) / Var X`, and the
least leftover is `Var Y - Cov² / Var X = Var Y · (1 - ρ²)`, with `ρ` the correlation.

* `variance_sub_mul_eq`: `Var[Y - c X] = Var X · (c - c*)² + (Var Y - Cov² / Var X)`.
* `variance_sub_mul_le`, `variance_sub_mul_eq_iff`: `c*` is a minimiser, and the only one.
* `variance_sub_bestCoeff_mul`: the least leftover is `Var Y · (1 - ρ²)` (for `Var Y > 0`).

**Lag correlation.** For `x (t + 1) = a x t + e t` (`FirstOrderRecursion`), with the start and all
the noises jointly independent (`iIndepFun` of the family `x 0, e 0, e 1, …`), `|a| < 1`, noise
variance `s² > 0` and the steady start `Var x 0 = s² / (1 - a²)`:

* `indepFun_of_le`: each `x t` is independent of every later noise `e u`, `t ≤ u`, derived from
  joint independence;
* `covariance_add`: `Cov(x t, x (t + k)) = a ^ k · Var (x t)`;
* `correlation_add`: `corr(x t, x (t + k)) = a ^ k`.

Each hypothesis is needed. With `Var X = 0` every `c` leaves the same. If each noise is only
independent of the current value (LEAN-10's hypothesis), a Gaussian case with `a = 1/2`,
`Var x 0 = 4/3`, `Var e 0 = Var e 1 = 1`, `Cov(x 0, e 0) = 0`, `Cov(x 0, e 1) = 3/10`,
`Cov(e 0, e 1) = -3/20` has `Cov(x 1, e 1) = 0` but `corr(x 0, x 2) = 19/40`, not `a² = 1/4`.
With `s² = 0` every value is constant and Lean's correlation is `0 / 0 = 0`, not `a ^ k`. From the
start `Var x 0 = 1` with `a = 1/2` and noise variance `1`, `corr(x 0, x 1) = 0.447`, not `0.5`.
-/

open MeasureTheory ProbabilityTheory Filter Finset Real
open ClassicalLean.Probability.FirstOrderRecursion

namespace ClassicalLean.Probability.LinearPrediction

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The correlation `Cov(X, Y) / √(Var X · Var Y)`. -/
noncomputable def correlation (X Y : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  cov[X, Y; μ] / √(variance X μ * variance Y μ)

/-- The best coefficient `Cov(X, Y) / Var X`. -/
noncomputable def bestCoeff (X Y : Ω → ℝ) (μ : Measure Ω) : ℝ := cov[X, Y; μ] / variance X μ

section Prediction

variable {X Y : Ω → ℝ}

/-- The leftover written as the mean square of the centred error. -/
theorem variance_sub_mul_eq_integral (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (c : ℝ) :
    variance (fun ω ↦ Y ω - c * X ω) μ =
      ∫ ω, (Y ω - μ[Y] - c * (X ω - μ[X])) ^ 2 ∂μ := by
  have hm : MemLp (fun ω ↦ Y ω - c * X ω) 2 μ := hY.sub (hX.const_mul c)
  rw [variance_eq_integral hm.aemeasurable]
  have hE : μ[fun ω ↦ Y ω - c * X ω] = μ[Y] - c * μ[X] := by
    rw [integral_sub (hY.integrable one_le_two) ((hX.integrable one_le_two).const_mul c),
      integral_const_mul]
  rw [hE]
  congr 1; funext ω; ring

lemma variance_sub_mul (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (c : ℝ) :
    variance (fun ω ↦ Y ω - c * X ω) μ =
      variance Y μ - 2 * c * cov[X, Y; μ] + c ^ 2 * variance X μ := by
  have hcX : MemLp (fun ω ↦ c * X ω) 2 μ := hX.const_mul c
  rw [show (fun ω ↦ Y ω - c * X ω) = Y - (fun ω ↦ c * X ω) from rfl,
    ← covariance_self (hY.sub hcX).aemeasurable, covariance_sub_left hY hcX (hY.sub hcX),
    covariance_sub_right hY hY hcX, covariance_sub_right hcX hY hcX,
    covariance_const_mul_left, covariance_const_mul_left, covariance_const_mul_right,
    covariance_const_mul_right, covariance_self hY.aemeasurable, covariance_self hX.aemeasurable,
    covariance_comm Y X]
  ring

/-- **The leftover as a square.** For `Var X > 0`,
`Var[Y - c X] = Var X · (c - c*)² + (Var Y - Cov² / Var X)` with `c* = Cov / Var X`. -/
theorem variance_sub_mul_eq (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hv : 0 < variance X μ)
    (c : ℝ) : variance (fun ω ↦ Y ω - c * X ω) μ =
      variance X μ * (c - bestCoeff X Y μ) ^ 2 +
        (variance Y μ - cov[X, Y; μ] ^ 2 / variance X μ) := by
  rw [variance_sub_mul hX hY, bestCoeff]
  field_simp
  ring

/-- **The best coefficient is a minimiser.** -/
theorem variance_sub_mul_le (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hv : 0 < variance X μ)
    (c : ℝ) : variance (fun ω ↦ Y ω - bestCoeff X Y μ * X ω) μ ≤
      variance (fun ω ↦ Y ω - c * X ω) μ := by
  rw [variance_sub_mul_eq hX hY hv, variance_sub_mul_eq hX hY hv, sub_self]
  nlinarith [mul_nonneg hv.le (sq_nonneg (c - bestCoeff X Y μ))]

/-- **The best coefficient is the only minimiser.** -/
theorem variance_sub_mul_eq_iff (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hv : 0 < variance X μ)
    (c : ℝ) : variance (fun ω ↦ Y ω - c * X ω) μ =
      variance (fun ω ↦ Y ω - bestCoeff X Y μ * X ω) μ ↔ c = bestCoeff X Y μ := by
  rw [variance_sub_mul_eq hX hY hv, variance_sub_mul_eq hX hY hv, sub_self]
  constructor
  · intro h
    have : variance X μ * (c - bestCoeff X Y μ) ^ 2 = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hv.ne'
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  · rintro rfl; rw [sub_self]

/-- **What is left.** The least leftover is `Var Y - Cov² / Var X`, which is `Var Y · (1 - ρ²)`
when `Var Y > 0`. -/
theorem variance_sub_bestCoeff_mul (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hv : 0 < variance X μ) (hw : 0 < variance Y μ) :
    variance (fun ω ↦ Y ω - bestCoeff X Y μ * X ω) μ =
      variance Y μ - cov[X, Y; μ] ^ 2 / variance X μ ∧
    variance (fun ω ↦ Y ω - bestCoeff X Y μ * X ω) μ =
      variance Y μ * (1 - correlation X Y μ ^ 2) := by
  have h := variance_sub_mul_eq hX hY hv (bestCoeff X Y μ)
  rw [sub_self, zero_pow two_ne_zero, mul_zero, zero_add] at h
  refine ⟨h, ?_⟩
  rw [h, correlation, div_pow, sq_sqrt (mul_nonneg hv.le hw.le)]
  field_simp

end Prediction

section Lag

variable {Z : ℕ → Ω → ℝ} {x : ℕ → Ω → ℝ} {a : ℝ}

/-- The value `x t` depends only on `Z 0, …, Z t`. -/
lemma measurable_iSup (hx0 : x 0 = Z 0)
    (hx : ∀ t ω, x (t + 1) ω = a * x t ω + Z (t + 1) ω) (t : ℕ) :
    Measurable[⨆ i ∈ Set.Iic t, MeasurableSpace.comap (Z i) inferInstance] (x t) := by
  induction t with
  | zero =>
    rw [hx0, measurable_iff_comap_le]
    exact le_iSup₂ (f := fun i (_ : i ∈ Set.Iic 0) ↦ MeasurableSpace.comap (Z i) inferInstance)
      0 (Set.mem_Iic.mpr le_rfl)
  | succ t ih =>
    have hmono : (⨆ i ∈ Set.Iic t, MeasurableSpace.comap (Z i) inferInstance) ≤
        ⨆ i ∈ Set.Iic (t + 1), MeasurableSpace.comap (Z i) inferInstance :=
      iSup₂_mono' fun i hi ↦ ⟨i, Set.Iic_subset_Iic.mpr (Nat.le_succ t) hi, le_rfl⟩
    have hZt : Measurable[⨆ i ∈ Set.Iic (t + 1), MeasurableSpace.comap (Z i) inferInstance]
        (Z (t + 1)) := by
      rw [measurable_iff_comap_le]
      exact le_iSup₂ (f := fun i (_ : i ∈ Set.Iic (t + 1)) ↦
        MeasurableSpace.comap (Z i) inferInstance) (t + 1) (Set.mem_Iic.mpr le_rfl)
    rw [show x (t + 1) = fun ω ↦ a * x t ω + Z (t + 1) ω from funext (hx t)]
    exact ((ih.mono hmono le_rfl).const_mul a).add hZt

omit [IsProbabilityMeasure μ] in
/-- **Each value is independent of every later noise.** If `x 0 = Z 0`, `x (t+1) = a x t + Z (t+1)`
and the family `Z` is jointly independent, then `x t` and `Z (u + 1)` are independent for
`t ≤ u`. -/
theorem indepFun_of_le (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z μ) (hx0 : x 0 = Z 0)
    (hx : ∀ t ω, x (t + 1) ω = a * x t ω + Z (t + 1) ω) {t u : ℕ} (htu : t ≤ u) :
    IndepFun (x t) (Z (u + 1)) μ := by
  have hle : ∀ i, MeasurableSpace.comap (Z i) inferInstance ≤ m0 := fun i ↦ (hZ i).comap_le
  have hdisj : Disjoint (Set.Iic t) {u + 1} := by
    rw [Set.disjoint_singleton_right, Set.mem_Iic]; omega
  have hI := indep_iSup_of_disjoint hle hind.iIndep hdisj
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hI ?_) ?_
  · exact measurable_iff_comap_le.mp (measurable_iSup hx0 hx t)
  · exact le_iSup₂ (f := fun i (_ : i ∈ ({u + 1} : Set ℕ)) ↦
      MeasurableSpace.comap (Z i) inferInstance) (u + 1) rfl

/-- **The lag covariance.** Under joint independence, `Cov(x t, x (t + k)) = a ^ k Var (x t)`. -/
theorem covariance_add (hZ : ∀ i, Measurable (Z i)) (hZ2 : ∀ i, MemLp (Z i) 2 μ)
    (hind : iIndepFun Z μ) (hx0 : x 0 = Z 0) (hx : ∀ t ω, x (t + 1) ω = a * x t ω + Z (t + 1) ω)
    (t k : ℕ) : cov[x t, x (t + k); μ] = a ^ k * variance (x t) μ := by
  have hL2 : ∀ t, MemLp (x t) 2 μ :=
    memLp_two (e := fun t ↦ Z (t + 1)) hx (hx0 ▸ hZ2 0) (fun t ↦ hZ2 (t + 1))
  induction k with
  | zero => simp [covariance_self (hL2 t).aemeasurable]
  | succ k ih =>
    rw [← add_assoc, show x (t + k + 1) = (fun ω ↦ a * x (t + k) ω) + Z (t + k + 1) from
      funext (hx (t + k)), covariance_add_right (hL2 t) ((hL2 (t + k)).const_mul a) (hZ2 _),
      covariance_const_mul_right, ih,
      (indepFun_of_le hZ hind hx0 hx (Nat.le_add_right t k)).covariance_eq_zero (hL2 t) (hZ2 _)]
    ring

omit [IsProbabilityMeasure μ] in
/-- **The steady variance stays.** If `Var x 0 = s² / (1 - a²)` and every noise has variance
`s²`, every `x t` has variance `s² / (1 - a²)` (for `a² ≠ 1`). -/
theorem variance_eq_steady (hZ : ∀ i, Measurable (Z i)) (hZ2 : ∀ i, MemLp (Z i) 2 μ)
    (hind : iIndepFun Z μ) (hx0 : x 0 = Z 0) (hx : ∀ t ω, x (t + 1) ω = a * x t ω + Z (t + 1) ω)
    {s : ℝ} (ha : a ^ 2 ≠ 1) (hvar : ∀ t, variance (Z (t + 1)) μ = s ^ 2)
    (hstart : variance (x 0) μ = s ^ 2 / (1 - a ^ 2)) (t : ℕ) :
    variance (x t) μ = s ^ 2 / (1 - a ^ 2) := by
  have h1 : 1 - a ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  induction t with
  | zero => exact hstart
  | succ t ih =>
    rw [variance_succ (e := fun t ↦ Z (t + 1)) hx (hx0 ▸ hZ2 0) (fun t ↦ hZ2 (t + 1))
      (fun t ↦ indepFun_of_le hZ hind hx0 hx le_rfl) hvar, ih]
    field_simp
    ring

/-- **The lag correlation.** For `x (t + 1) = a x t + e t` with the start and the noises jointly
independent, `|a| < 1`, noise variance `s² > 0` and the steady start `Var x 0 = s² / (1 - a²)`:
`corr(x t, x (t + k)) = a ^ k`. -/
theorem correlation_add (hZ : ∀ i, Measurable (Z i)) (hZ2 : ∀ i, MemLp (Z i) 2 μ)
    (hind : iIndepFun Z μ) (hx0 : x 0 = Z 0) (hx : ∀ t ω, x (t + 1) ω = a * x t ω + Z (t + 1) ω)
    {s : ℝ} (ha : |a| < 1) (hs : 0 < s ^ 2) (hvar : ∀ t, variance (Z (t + 1)) μ = s ^ 2)
    (hstart : variance (x 0) μ = s ^ 2 / (1 - a ^ 2)) (t k : ℕ) :
    correlation (x t) (x (t + k)) μ = a ^ k := by
  have ha2 : a ^ 2 < 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg a]
  have hv := variance_eq_steady hZ hZ2 hind hx0 hx ha2.ne hvar hstart
  have hpos : 0 < s ^ 2 / (1 - a ^ 2) := div_pos hs (by linarith)
  rw [correlation, covariance_add hZ hZ2 hind hx0 hx, hv t, hv (t + k),
    sqrt_mul_self hpos.le, mul_div_assoc, div_self hpos.ne', mul_one]

end Lag

end ClassicalLean.Probability.LinearPrediction
