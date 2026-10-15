/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Martingale.Convergence

/-!
# Pólya's urn

An urn holds `r` red and `b` blue balls. At each step a ball is drawn at random, and put back
together with one more ball of its colour. `X n ∈ {0, 1}` says whether draw `n` (counting from `0`)
is red; `urnRed r X n` is the number of red balls after `n` draws, and `urnShare r b X n` their
share of the `r + b + n` balls. "Drawn at random" is said through a filtration `ℱ`: draw `n` is
known at time `n + 1`, and given what is known at time `n` it is red with chance the current
share, `μ[X n | ℱ n] = urnShare r b X n` almost everywhere. Order CLOUD-MATH-1, item 137 of
MATH-PLAN-library-2.

* `martingale_urnShare` — the share of red balls is a martingale.
* `ae_tendsto_urnShare` — the share converges almost surely (Doob's martingale convergence
  theorem, Mathlib's `Submartingale.ae_tendsto_limitProcess`, for a martingale bounded in `L¹`).
* `ae_mem_Icc_of_tendsto_urnShare` — an almost sure limit of the share lies in `[0, 1]` almost
  surely.

The martingale step: after draw `n` the share is `(R + X n) / (N + 1)`, with `R` red balls among
`N = r + b + n`; its conditional mean given time `n` is `(R + R / N) / (N + 1) = R / N`.

The import of `Mathlib.Probability.Kernel.IonescuTulcea.Traj` serves only the witnesses at the end
of the file, which build the paths of an urn with `r = b = 1` by the Ionescu-Tulcea theorem.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace ClassicalLean.Probability.PolyaUrn

/-- Number of red balls after `n` draws, starting with `r` red balls; `X i ∈ {0,1}`
indicates that the `(i+1)`-st draw is red. -/
noncomputable def urnRed {Ω : Type*} (r : ℕ) (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => r
  | n + 1, ω => urnRed r X n ω + X n ω

/-- Share of red balls after `n` draws; the urn then contains `r + b + n` balls. -/
noncomputable def urnShare {Ω : Type*} (r b : ℕ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  urnRed r X n ω / ((r + b + n : ℕ) : ℝ)

private lemma urnRed_zero {Ω : Type*} (r : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    urnRed r X 0 ω = r := rfl

private lemma urnRed_succ {Ω : Type*} (r : ℕ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    urnRed r X (n + 1) ω = urnRed r X n ω + X n ω := rfl

private lemma urnRed_bounds {Ω : Type*} (r : ℕ) (X : ℕ → Ω → ℝ)
    (hX01 : ∀ n ω, X n ω = 0 ∨ X n ω = 1) :
    ∀ n ω, 0 ≤ urnRed r X n ω ∧ urnRed r X n ω ≤ (r : ℝ) + n := by
  intro n ω
  induction n with
  | zero =>
    rw [urnRed_zero]
    exact ⟨Nat.cast_nonneg r, by simp⟩
  | succ n ih =>
    rw [urnRed_succ]
    push_cast
    obtain ⟨i1, i2⟩ := ih
    rcases hX01 n ω with h | h <;> rw [h] <;> constructor <;> linarith

private lemma urnShare_norm_le {Ω : Type*} (r b : ℕ) (hrb : 0 < r + b) (X : ℕ → Ω → ℝ)
    (hX01 : ∀ n ω, X n ω = 0 ∨ X n ω = 1) (n : ℕ) (ω : Ω) :
    ‖urnShare r b X n ω‖ ≤ 1 := by
  obtain ⟨h0, h1⟩ := urnRed_bounds r X hX01 n ω
  have hN : (0 : ℝ) < ((r + b + n : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < r + b + n by omega)
  have hle : urnRed r X n ω ≤ ((r + b + n : ℕ) : ℝ) := by
    push_cast
    have : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
    linarith
  have a0 : 0 ≤ urnShare r b X n ω := div_nonneg h0 hN.le
  have a1 : urnShare r b X n ω ≤ 1 := (div_le_one hN).mpr hle
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

private lemma urnRed_stronglyMeasurable {Ω : Type*} {m0 : MeasurableSpace Ω}
    (ℱ : Filtration ℕ m0) (r : ℕ) (X : ℕ → Ω → ℝ)
    (hX : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n)) :
    ∀ n, StronglyMeasurable[ℱ n] (urnRed r X n) := by
  intro n
  induction n with
  | zero =>
    have h : urnRed r X 0 = fun _ => (r : ℝ) := by
      funext ω; rfl
    rw [h]
    exact stronglyMeasurable_const
  | succ n ih =>
    have h : urnRed r X (n + 1) = urnRed r X n + X n := by
      funext ω; rfl
    rw [h]
    exact (ih.mono (ℱ.mono (Nat.le_succ n))).add (hX n)

private lemma urnRed_integrable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (r : ℕ) (X : ℕ → Ω → ℝ)
    (hX01 : ∀ n ω, X n ω = 0 ∨ X n ω = 1)
    (hX : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n)) (n : ℕ) :
    Integrable (urnRed r X n) μ := by
  refine Integrable.mono' (integrable_const ((r : ℝ) + n))
    (((urnRed_stronglyMeasurable ℱ r X hX n).mono (ℱ.le n)).aestronglyMeasurable)
    (ae_of_all μ fun ω => ?_)
  change ‖urnRed r X n ω‖ ≤ (r : ℝ) + n
  rw [Real.norm_eq_abs, abs_le]
  obtain ⟨h0, h1⟩ := urnRed_bounds r X hX01 n ω
  have : (0 : ℝ) ≤ (r : ℝ) + n := by positivity
  constructor <;> linarith

private lemma share_key (R N : ℝ) (hN : 0 < N) :
    1 / (N + 1) * R + 1 / (N + 1) * (R / N) = R / N := by
  have h1 : N + 1 ≠ 0 := (by linarith : (0 : ℝ) < N + 1).ne'
  have h2 : N ≠ 0 := hN.ne'
  have hi : N * N⁻¹ = 1 := mul_inv_cancel₀ h2
  have hj : (N + 1) * (N + 1)⁻¹ = 1 := mul_inv_cancel₀ h1
  linear_combination (R * N⁻¹) * hj - ((N + 1)⁻¹ * R) * hi

/-- **Pólya's urn: the share of red balls is a martingale** (item 137 of MATH-PLAN-library-2).
The urn starts with `r` red and `b` blue balls, `r + b > 0`; draw `n` is red (`X n = 1`) or blue
(`X n = 0`), is known at time `n + 1`, and given what is known at time `n` is red with chance the
current share of red balls (`μ[X n | ℱ n] = urnShare r b X n` almost everywhere); each drawn ball
goes back with one more of its colour. Then the share `urnShare r b X n` is a martingale. -/
theorem martingale_urnShare {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (r b : ℕ) (hrb : 0 < r + b)
    (X : ℕ → Ω → ℝ) (hX01 : ∀ n ω, X n ω = 0 ∨ X n ω = 1)
    (hX_meas : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hX_cond : ∀ n, μ[X n | ℱ n] =ᵐ[μ] urnShare r b X n) :
    Martingale (urnShare r b X) ℱ μ := by
  have hRmeas := urnRed_stronglyMeasurable ℱ r X hX_meas
  have hRint : ∀ n, Integrable (urnRed r X n) μ :=
    fun n => urnRed_integrable ℱ r X hX01 hX_meas n
  have hXint : ∀ n, Integrable (X n) μ := fun n =>
    Integrable.mono' (integrable_const (1 : ℝ))
      (((hX_meas n).mono (ℱ.le (n + 1))).aestronglyMeasurable)
      (ae_of_all μ fun ω => by
        change ‖X n ω‖ ≤ 1
        rcases hX01 n ω with h | h <;> simp [h])
  have hSmeas : ∀ n, StronglyMeasurable[ℱ n] (urnShare r b X n) := by
    intro n
    have heq : urnShare r b X n
        = fun ω => urnRed r X n ω * (((r + b + n : ℕ) : ℝ))⁻¹ := by
      funext ω; exact div_eq_mul_inv _ _
    rw [heq]
    exact (hRmeas n).mul_const _
  have hSint : ∀ n, Integrable (urnShare r b X n) μ := fun n =>
    Integrable.mono' (integrable_const (1 : ℝ))
      (((hSmeas n).mono (ℱ.le n)).aestronglyMeasurable)
      (ae_of_all μ fun ω => urnShare_norm_le r b hrb X hX01 n ω)
  refine martingale_nat (fun n => hSmeas n) hSint (fun n => ?_)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / ((r + b + (n + 1) : ℕ) : ℝ) := ⟨_, rfl⟩
  have hsplit : urnShare r b X (n + 1) = c • urnRed r X n + c • X n := by
    funext ω
    simp only [urnShare, urnRed_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc]
    ring
  have h1 : μ[urnShare r b X (n + 1) | ℱ n]
      =ᵐ[μ] μ[c • urnRed r X n | ℱ n] + μ[c • X n | ℱ n] := by
    rw [hsplit]
    exact condExp_add (m := ℱ n) ((hRint n).smul c) ((hXint n).smul c)
  have h2 : μ[c • urnRed r X n | ℱ n] = c • urnRed r X n :=
    condExp_of_stronglyMeasurable (ℱ.le n) ((hRmeas n).const_smul c) ((hRint n).smul c)
  have h3 : μ[c • X n | ℱ n] =ᵐ[μ] c • μ[X n | ℱ n] :=
    condExp_smul (m := ℱ n) c (X n)
  have hN : (0 : ℝ) < ((r + b + n : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < r + b + n by omega)
  have hcast : ((r + b + (n + 1) : ℕ) : ℝ) = ((r + b + n : ℕ) : ℝ) + 1 := by
    push_cast; ring
  filter_upwards [h1, h3, hX_cond n] with ω e1 e3 e4
  rw [e1, Pi.add_apply, h2, e3]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [e4, hc, hcast]
  simp only [urnShare]
  exact (share_key _ _ hN).symm

/-- **Pólya's urn: the share of red balls converges almost surely** (item 137 of
MATH-PLAN-library-2), under the hypotheses of `martingale_urnShare`: the share is a martingale
with values in `[0, 1]`, so bounded in `L¹`, and the martingale convergence theorem applies. -/
theorem ae_tendsto_urnShare {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (r b : ℕ) (hrb : 0 < r + b)
    (X : ℕ → Ω → ℝ) (hX01 : ∀ n ω, X n ω = 0 ∨ X n ω = 1)
    (hX_meas : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hX_cond : ∀ n, μ[X n | ℱ n] =ᵐ[μ] urnShare r b X n) :
    ∃ L : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n => urnShare r b X n ω) atTop (𝓝 (L ω)) := by
  have hmart := martingale_urnShare ℱ r b hrb X hX01 hX_meas hX_cond
  have hbdd : ∀ n, eLpNorm (urnShare r b X n) 1 μ ≤ ((1 : ℝ≥0) : ℝ≥0∞) := by
    intro n
    have hae : AEStronglyMeasurable (urnShare r b X n) μ :=
      (hmart.integrable n).aestronglyMeasurable
    have hb : ∀ᵐ ω ∂μ, ‖urnShare r b X n ω‖ ≤ (1 : ℝ) :=
      ae_of_all μ fun ω => urnShare_norm_le r b hrb X hX01 n ω
    exact (eLpNorm_le_of_ae_bound hae hb).trans (by simp)
  exact ⟨ℱ.limitProcess (urnShare r b X) μ,
    hmart.submartingale.ae_tendsto_limitProcess hbdd⟩

/-- The share of red balls lies in `[0, 1]` after any number of draws, whatever `r` and `b`: the
red balls are at least `0` and at most `r + n ≤ r + b + n` (and when `r + b + n = 0`, Lean's
`0 / 0 = 0`). -/
private lemma urnShare_mem_Icc {Ω : Type*} (r b : ℕ) (X : ℕ → Ω → ℝ)
    (hX01 : ∀ n ω, X n ω = 0 ∨ X n ω = 1) (n : ℕ) (ω : Ω) :
    urnShare r b X n ω ∈ Set.Icc 0 1 := by
  obtain ⟨h0, h1⟩ := urnRed_bounds r X hX01 n ω
  have hN : (0 : ℝ) ≤ ((r + b + n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hle : urnRed r X n ω ≤ ((r + b + n : ℕ) : ℝ) := by
    push_cast
    have : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
    linarith
  exact ⟨div_nonneg h0 hN, div_le_one_of_le₀ hle hN⟩

/-- **Pólya's urn: the limit share lies in `[0, 1]` almost surely** (item 137 of
MATH-PLAN-library-2). Whenever the share of red balls converges almost surely to some `L` (as it
does under the hypotheses of `ae_tendsto_urnShare`), `L` lies in `[0, 1]` almost surely. Only the
draws being `0` or `1` is needed: every share lies in the closed set `[0, 1]`. -/
theorem ae_mem_Icc_of_tendsto_urnShare {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    (r b : ℕ) (X : ℕ → Ω → ℝ) (hX01 : ∀ n ω, X n ω = 0 ∨ X n ω = 1) {L : Ω → ℝ}
    (hL : ∀ᵐ ω ∂μ, Tendsto (fun n => urnShare r b X n ω) atTop (𝓝 (L ω))) :
    ∀ᵐ ω ∂μ, L ω ∈ Set.Icc 0 1 := by
  filter_upwards [hL] with ω hω
  exact isClosed_Icc.mem_of_tendsto hω
    (Eventually.of_forall fun n => urnShare_mem_Icc r b X hX01 n ω)

end ClassicalLean.Probability.PolyaUrn

open MeasureTheory ProbabilityTheory Finset ClassicalLean.Probability.PolyaUrn in
/-- The hypotheses of `martingale_urnShare` hold together: Pólya's urn itself, its paths built by
Mathlib's Ionescu-Tulcea theorem (`Kernel.traj`). A path is `ω : ℕ → Bool`; coordinate `n + 1` is
draw `n` (`true` for red), coordinate `0` plays no part. The urn starts with `r = 1` red and `b = 1`
blue ball. The kernel `κ n` draws coordinate `n + 1` red with chance the share of red balls after
the draws in coordinates `1, …, n`, a chance that depends on those draws and lies between
`1 / (n + 2)` and `(n + 1) / (n + 2)`, so every draw is random. Draw `n` is `X n ω = 1` when
coordinate `n + 1` is `true` and `0` otherwise, so it is `0` or `1`; the filtration is `piLE`, the
coordinates up to each time, so draw `n` is known at time `n + 1`; and given time `n`, the mean of
draw `n` is the current share (Mathlib's `Kernel.condExp_traj` and `Kernel.map_traj_succ_self`, and
the share at time `n` depends only on the coordinates up to `n`). -/
example := ClassicalLean.Probability.PolyaUrn.martingale_urnShare
    (μ := @Kernel.traj (fun _ ↦ Bool) _
      (fun n ↦ Kernel.ofFunOfCountable fun z : (Π _ : Iic n, Bool) ↦
        ENNReal.ofReal (urnShare 1 1 (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0) n
            fun i ↦ if h : i ≤ n then z ⟨i, mem_Iic.2 h⟩ else false) • Measure.dirac true +
          ENNReal.ofReal (1 - urnShare 1 1
            (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0) n
            fun i ↦ if h : i ≤ n then z ⟨i, mem_Iic.2 h⟩ else false) • Measure.dirac false)
      (fun n ↦ ⟨fun z ↦ ⟨by
        obtain ⟨h0, h1⟩ := urnShare_mem_Icc 1 1
          (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0)
          (fun j ω ↦ by by_cases h : ω (j + 1) <;> simp [h]) n
          (fun i ↦ if h : i ≤ n then z ⟨i, mem_Iic.2 h⟩ else false)
        simp [Kernel.ofFunOfCountable, ← ENNReal.ofReal_add h0 (sub_nonneg.2 h1)]⟩⟩)
      0 fun _ ↦ false)
    (ℱ := Filtration.piLE) (r := 1) (b := 1) (by norm_num)
    (X := fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0)
    (fun j ω ↦ by by_cases h : ω (j + 1) <;> simp [h])
    (fun n ↦ by
      have h : Measurable[Filtration.piLE (n + 1)] fun ω : ℕ → Bool ↦ ω (n + 1) := by
        rw [Filtration.piLE_eq_comap_frestrictLe]
        exact (measurable_pi_apply (⟨n + 1, mem_Iic.2 le_rfl⟩ : Iic (n + 1))).comp
          (comap_measurable (Preorder.frestrictLe (π := fun _ : ℕ ↦ Bool) (n + 1)))
      exact ((measurable_of_countable fun c : Bool ↦ if c then (1 : ℝ) else 0).comp
        h).stronglyMeasurable)
    (fun n ↦ by
      have : ∀ n, IsMarkovKernel (Kernel.ofFunOfCountable fun z : (Π _ : Iic n, Bool) ↦
          ENNReal.ofReal (urnShare 1 1 (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0)
              n fun i ↦ if h : i ≤ n then z ⟨i, mem_Iic.2 h⟩ else false) • Measure.dirac true +
            ENNReal.ofReal (1 - urnShare 1 1
              (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0) n
              fun i ↦ if h : i ≤ n then z ⟨i, mem_Iic.2 h⟩ else false) • Measure.dirac false) :=
        fun n ↦ ⟨fun z ↦ ⟨by
          obtain ⟨h0, h1⟩ := urnShare_mem_Icc 1 1
            (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0)
            (fun j ω ↦ by by_cases h : ω (j + 1) <;> simp [h]) n
            (fun i ↦ if h : i ≤ n then z ⟨i, mem_Iic.2 h⟩ else false)
          simp [Kernel.ofFunOfCountable, ← ENNReal.ofReal_add h0 (sub_nonneg.2 h1)]⟩⟩
      have hm : ∀ k, StronglyMeasurable[Filtration.piLE (k + 1)]
          fun ω : ℕ → Bool ↦ if ω (k + 1) then (1 : ℝ) else 0 := fun k ↦ by
        have h : Measurable[Filtration.piLE (k + 1)] fun ω : ℕ → Bool ↦ ω (k + 1) := by
          rw [Filtration.piLE_eq_comap_frestrictLe]
          exact (measurable_pi_apply (⟨k + 1, mem_Iic.2 le_rfl⟩ : Iic (k + 1))).comp
            (comap_measurable (Preorder.frestrictLe (π := fun _ : ℕ ↦ Bool) (k + 1)))
        exact ((measurable_of_countable fun c : Bool ↦ if c then (1 : ℝ) else 0).comp
          h).stronglyMeasurable
      refine (Kernel.condExp_traj (Nat.zero_le n) (Integrable.of_bound
        ((hm n).mono ((Filtration.piLE).le _)).aestronglyMeasurable 1
        (ae_of_all _ fun ω ↦ by by_cases h : ω (n + 1) <;> simp [h]))).trans
        (ae_of_all _ fun ω ↦ ?_)
      beta_reduce
      rw [← integral_map (φ := fun y : ℕ → Bool ↦ y (n + 1))
        (f := fun c : Bool ↦ if c then (1 : ℝ) else 0) (measurable_pi_apply _).aemeasurable
        (measurable_of_countable _).aestronglyMeasurable,
        ← Kernel.map_apply _ (measurable_pi_apply (n + 1)), Kernel.map_traj_succ_self]
      have heq : urnShare 1 1 (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0) n
          (fun i ↦ decide (i ≤ n) && ω i) =
          urnShare 1 1 (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0) n ω :=
        Measurable.dependsOn_of_piLE
          ((urnRed_stronglyMeasurable Filtration.piLE 1 _ hm n).measurable.div_const _)
          fun i hi ↦ by simp [Set.mem_Iic.1 hi]
      have h0 := (urnShare_mem_Icc 1 1 (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0)
        (fun j ω ↦ by by_cases h : ω (j + 1) <;> simp [h]) n ω).1
      rw [integral_fintype .of_finite]
      simp [Kernel.ofFunOfCountable, Measure.real, heq, ENNReal.toReal_ofReal h0])

open MeasureTheory ProbabilityTheory Finset ClassicalLean.Probability.PolyaUrn in
/-- The hypotheses of `ae_tendsto_urnShare` hold together: Pólya's urn itself, its paths built by
Mathlib's Ionescu-Tulcea theorem (`Kernel.traj`). A path is `ω : ℕ → Bool`; coordinate `n + 1` is
draw `n` (`true` for red), coordinate `0` plays no part. The urn starts with `r = 1` red and `b = 1`
blue ball. The kernel `κ n` draws coordinate `n + 1` red with chance the share of red balls after
the draws in coordinates `1, …, n`, a chance that depends on those draws and lies between
`1 / (n + 2)` and `(n + 1) / (n + 2)`, so every draw is random. Draw `n` is `X n ω = 1` when
coordinate `n + 1` is `true` and `0` otherwise, so it is `0` or `1`; the filtration is `piLE`, the
coordinates up to each time, so draw `n` is known at time `n + 1`; and given time `n`, the mean of
draw `n` is the current share (Mathlib's `Kernel.condExp_traj` and `Kernel.map_traj_succ_self`, and
the share at time `n` depends only on the coordinates up to `n`). -/
example := ClassicalLean.Probability.PolyaUrn.ae_tendsto_urnShare
    (μ := @Kernel.traj (fun _ ↦ Bool) _
      (fun n ↦ Kernel.ofFunOfCountable fun z : (Π _ : Iic n, Bool) ↦
        ENNReal.ofReal (urnShare 1 1 (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0) n
            fun i ↦ if h : i ≤ n then z ⟨i, mem_Iic.2 h⟩ else false) • Measure.dirac true +
          ENNReal.ofReal (1 - urnShare 1 1
            (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0) n
            fun i ↦ if h : i ≤ n then z ⟨i, mem_Iic.2 h⟩ else false) • Measure.dirac false)
      (fun n ↦ ⟨fun z ↦ ⟨by
        obtain ⟨h0, h1⟩ := urnShare_mem_Icc 1 1
          (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0)
          (fun j ω ↦ by by_cases h : ω (j + 1) <;> simp [h]) n
          (fun i ↦ if h : i ≤ n then z ⟨i, mem_Iic.2 h⟩ else false)
        simp [Kernel.ofFunOfCountable, ← ENNReal.ofReal_add h0 (sub_nonneg.2 h1)]⟩⟩)
      0 fun _ ↦ false)
    (ℱ := Filtration.piLE) (r := 1) (b := 1) (by norm_num)
    (X := fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0)
    (fun j ω ↦ by by_cases h : ω (j + 1) <;> simp [h])
    (fun n ↦ by
      have h : Measurable[Filtration.piLE (n + 1)] fun ω : ℕ → Bool ↦ ω (n + 1) := by
        rw [Filtration.piLE_eq_comap_frestrictLe]
        exact (measurable_pi_apply (⟨n + 1, mem_Iic.2 le_rfl⟩ : Iic (n + 1))).comp
          (comap_measurable (Preorder.frestrictLe (π := fun _ : ℕ ↦ Bool) (n + 1)))
      exact ((measurable_of_countable fun c : Bool ↦ if c then (1 : ℝ) else 0).comp
        h).stronglyMeasurable)
    (fun n ↦ by
      have : ∀ n, IsMarkovKernel (Kernel.ofFunOfCountable fun z : (Π _ : Iic n, Bool) ↦
          ENNReal.ofReal (urnShare 1 1 (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0)
              n fun i ↦ if h : i ≤ n then z ⟨i, mem_Iic.2 h⟩ else false) • Measure.dirac true +
            ENNReal.ofReal (1 - urnShare 1 1
              (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0) n
              fun i ↦ if h : i ≤ n then z ⟨i, mem_Iic.2 h⟩ else false) • Measure.dirac false) :=
        fun n ↦ ⟨fun z ↦ ⟨by
          obtain ⟨h0, h1⟩ := urnShare_mem_Icc 1 1
            (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0)
            (fun j ω ↦ by by_cases h : ω (j + 1) <;> simp [h]) n
            (fun i ↦ if h : i ≤ n then z ⟨i, mem_Iic.2 h⟩ else false)
          simp [Kernel.ofFunOfCountable, ← ENNReal.ofReal_add h0 (sub_nonneg.2 h1)]⟩⟩
      have hm : ∀ k, StronglyMeasurable[Filtration.piLE (k + 1)]
          fun ω : ℕ → Bool ↦ if ω (k + 1) then (1 : ℝ) else 0 := fun k ↦ by
        have h : Measurable[Filtration.piLE (k + 1)] fun ω : ℕ → Bool ↦ ω (k + 1) := by
          rw [Filtration.piLE_eq_comap_frestrictLe]
          exact (measurable_pi_apply (⟨k + 1, mem_Iic.2 le_rfl⟩ : Iic (k + 1))).comp
            (comap_measurable (Preorder.frestrictLe (π := fun _ : ℕ ↦ Bool) (k + 1)))
        exact ((measurable_of_countable fun c : Bool ↦ if c then (1 : ℝ) else 0).comp
          h).stronglyMeasurable
      refine (Kernel.condExp_traj (Nat.zero_le n) (Integrable.of_bound
        ((hm n).mono ((Filtration.piLE).le _)).aestronglyMeasurable 1
        (ae_of_all _ fun ω ↦ by by_cases h : ω (n + 1) <;> simp [h]))).trans
        (ae_of_all _ fun ω ↦ ?_)
      beta_reduce
      rw [← integral_map (φ := fun y : ℕ → Bool ↦ y (n + 1))
        (f := fun c : Bool ↦ if c then (1 : ℝ) else 0) (measurable_pi_apply _).aemeasurable
        (measurable_of_countable _).aestronglyMeasurable,
        ← Kernel.map_apply _ (measurable_pi_apply (n + 1)), Kernel.map_traj_succ_self]
      have heq : urnShare 1 1 (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0) n
          (fun i ↦ decide (i ≤ n) && ω i) =
          urnShare 1 1 (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0) n ω :=
        Measurable.dependsOn_of_piLE
          ((urnRed_stronglyMeasurable Filtration.piLE 1 _ hm n).measurable.div_const _)
          fun i hi ↦ by simp [Set.mem_Iic.1 hi]
      have h0 := (urnShare_mem_Icc 1 1 (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0)
        (fun j ω ↦ by by_cases h : ω (j + 1) <;> simp [h]) n ω).1
      rw [integral_fintype .of_finite]
      simp [Kernel.ofFunOfCountable, Measure.real, heq, ENNReal.toReal_ofReal h0])

open MeasureTheory ProbabilityTheory Finset ClassicalLean.Probability.PolyaUrn in
/-- The hypotheses of `ae_mem_Icc_of_tendsto_urnShare` hold together: on the probability space of
the Pólya urn of the witnesses above (`r = b = 1`, the path measure of `Kernel.traj`), the draws are
`0` or `1`, and `L` is the almost sure limit of the share that `ae_tendsto_urnShare` gives for that
urn (chosen with `Classical.choose`), so the share converges to `L` almost surely. -/
example := ClassicalLean.Probability.PolyaUrn.ae_mem_Icc_of_tendsto_urnShare
    (μ := @Kernel.traj (fun _ ↦ Bool) _
      (fun n ↦ Kernel.ofFunOfCountable fun z : (Π _ : Iic n, Bool) ↦
        ENNReal.ofReal (urnShare 1 1 (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0) n
            fun i ↦ if h : i ≤ n then z ⟨i, mem_Iic.2 h⟩ else false) • Measure.dirac true +
          ENNReal.ofReal (1 - urnShare 1 1
            (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0) n
            fun i ↦ if h : i ≤ n then z ⟨i, mem_Iic.2 h⟩ else false) • Measure.dirac false)
      (fun n ↦ ⟨fun z ↦ ⟨by
        obtain ⟨h0, h1⟩ := urnShare_mem_Icc 1 1
          (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0)
          (fun j ω ↦ by by_cases h : ω (j + 1) <;> simp [h]) n
          (fun i ↦ if h : i ≤ n then z ⟨i, mem_Iic.2 h⟩ else false)
        simp [Kernel.ofFunOfCountable, ← ENNReal.ofReal_add h0 (sub_nonneg.2 h1)]⟩⟩)
      0 fun _ ↦ false)
    (r := 1) (b := 1) (X := fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0)
    (fun j ω ↦ by by_cases h : ω (j + 1) <;> simp [h])
    (L := Classical.choose (ClassicalLean.Probability.PolyaUrn.ae_tendsto_urnShare
        (μ := @Kernel.traj (fun _ ↦ Bool) _
          (fun n ↦ Kernel.ofFunOfCountable fun z : (Π _ : Iic n, Bool) ↦
            ENNReal.ofReal (urnShare 1 1 (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0) n
                fun i ↦ if h : i ≤ n then z ⟨i, mem_Iic.2 h⟩ else false) • Measure.dirac true +
              ENNReal.ofReal (1 - urnShare 1 1
                (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0) n
                fun i ↦ if h : i ≤ n then z ⟨i, mem_Iic.2 h⟩ else false) • Measure.dirac false)
          (fun n ↦ ⟨fun z ↦ ⟨by
            obtain ⟨h0, h1⟩ := urnShare_mem_Icc 1 1
              (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0)
              (fun j ω ↦ by by_cases h : ω (j + 1) <;> simp [h]) n
              (fun i ↦ if h : i ≤ n then z ⟨i, mem_Iic.2 h⟩ else false)
            simp [Kernel.ofFunOfCountable, ← ENNReal.ofReal_add h0 (sub_nonneg.2 h1)]⟩⟩)
          0 fun _ ↦ false)
        (ℱ := Filtration.piLE) (r := 1) (b := 1) (by norm_num)
        (X := fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0)
        (fun j ω ↦ by by_cases h : ω (j + 1) <;> simp [h])
        (fun n ↦ by
          have h : Measurable[Filtration.piLE (n + 1)] fun ω : ℕ → Bool ↦ ω (n + 1) := by
            rw [Filtration.piLE_eq_comap_frestrictLe]
            exact (measurable_pi_apply (⟨n + 1, mem_Iic.2 le_rfl⟩ : Iic (n + 1))).comp
              (comap_measurable (Preorder.frestrictLe (π := fun _ : ℕ ↦ Bool) (n + 1)))
          exact ((measurable_of_countable fun c : Bool ↦ if c then (1 : ℝ) else 0).comp
            h).stronglyMeasurable)
        (fun n ↦ by
          have : ∀ n, IsMarkovKernel (Kernel.ofFunOfCountable fun z : (Π _ : Iic n, Bool) ↦
              ENNReal.ofReal (urnShare 1 1 (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0)
                  n fun i ↦ if h : i ≤ n then z ⟨i, mem_Iic.2 h⟩ else false) • Measure.dirac true +
                ENNReal.ofReal (1 - urnShare 1 1
                  (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0) n
                  fun i ↦ if h : i ≤ n then z ⟨i, mem_Iic.2 h⟩ else false) • Measure.dirac false) :=
            fun n ↦ ⟨fun z ↦ ⟨by
              obtain ⟨h0, h1⟩ := urnShare_mem_Icc 1 1
                (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0)
                (fun j ω ↦ by by_cases h : ω (j + 1) <;> simp [h]) n
                (fun i ↦ if h : i ≤ n then z ⟨i, mem_Iic.2 h⟩ else false)
              simp [Kernel.ofFunOfCountable, ← ENNReal.ofReal_add h0 (sub_nonneg.2 h1)]⟩⟩
          have hm : ∀ k, StronglyMeasurable[Filtration.piLE (k + 1)]
              fun ω : ℕ → Bool ↦ if ω (k + 1) then (1 : ℝ) else 0 := fun k ↦ by
            have h : Measurable[Filtration.piLE (k + 1)] fun ω : ℕ → Bool ↦ ω (k + 1) := by
              rw [Filtration.piLE_eq_comap_frestrictLe]
              exact (measurable_pi_apply (⟨k + 1, mem_Iic.2 le_rfl⟩ : Iic (k + 1))).comp
                (comap_measurable (Preorder.frestrictLe (π := fun _ : ℕ ↦ Bool) (k + 1)))
            exact ((measurable_of_countable fun c : Bool ↦ if c then (1 : ℝ) else 0).comp
              h).stronglyMeasurable
          refine (Kernel.condExp_traj (Nat.zero_le n) (Integrable.of_bound
            ((hm n).mono ((Filtration.piLE).le _)).aestronglyMeasurable 1
            (ae_of_all _ fun ω ↦ by by_cases h : ω (n + 1) <;> simp [h]))).trans
            (ae_of_all _ fun ω ↦ ?_)
          beta_reduce
          rw [← integral_map (φ := fun y : ℕ → Bool ↦ y (n + 1))
            (f := fun c : Bool ↦ if c then (1 : ℝ) else 0) (measurable_pi_apply _).aemeasurable
            (measurable_of_countable _).aestronglyMeasurable,
            ← Kernel.map_apply _ (measurable_pi_apply (n + 1)), Kernel.map_traj_succ_self]
          have heq : urnShare 1 1 (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0) n
              (fun i ↦ decide (i ≤ n) && ω i) =
              urnShare 1 1 (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0) n ω :=
            Measurable.dependsOn_of_piLE
              ((urnRed_stronglyMeasurable Filtration.piLE 1 _ hm n).measurable.div_const _)
              fun i hi ↦ by simp [Set.mem_Iic.1 hi]
          have h0 := (urnShare_mem_Icc 1 1 (fun j (ω : ℕ → Bool) ↦ if ω (j + 1) then (1 : ℝ) else 0)
            (fun j ω ↦ by by_cases h : ω (j + 1) <;> simp [h]) n ω).1
          rw [integral_fintype .of_finite]
          simp [Kernel.ofFunOfCountable, Measure.real, heq, ENNReal.toReal_ofReal h0])))
    (by generalize_proofs; exact Classical.choose_spec ‹∃ _, _›)
