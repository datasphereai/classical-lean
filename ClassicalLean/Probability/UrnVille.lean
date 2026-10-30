/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Probability.PolyaUrn
import ClassicalLean.Probability.MaximalInequality

/-!
# Pólya's urn rarely runs far up

An urn starts with `r` red and `b` blue balls, `r + b > 0`, and each drawn ball goes back with one
more of its colour (`PolyaUrn`, item 137 of MATH-PLAN-library-2). The share of red balls is a
martingale (`martingale_urnShare`) with values in `[0, 1]` that starts at the constant
`r / (r + b)`. Order CLOUD-MATH-6, bridge 157 of `MATH-PLAN-library-2-bridges-2.md`.

* `measureReal_exists_urnShare_ge_le` — for `c > 0`, the chance that the share of red balls ever
  reaches `c` is at most `r / ((r + b) c)` (for `c ≤ r / (r + b)` the bound is at least `1` and says
  nothing). Ville's inequality for a nonnegative supermartingale
  (`MaximalInequality.measureReal_exists_le_of_supermartingale`) bounds the chance up to each
  horizon `N` by `E[share at 0] / c`, and the events grow with `N` (continuity of the measure from
  below, `Monotone.measure_iUnion`), as `GamblersRuin.measureReal_exists_ge_le_of_biased` does for
  the walk.
* `urnShare_mem_Icc`, `urnRed_stronglyMeasurable` — the share lies in `[0, 1]` when every draw is
  `0` or `1`, and the number of red balls after `n` draws is known at time `n`. `PolyaUrn` proves
  both as `private` lemmas; they are stated again here because the proof and the witness use them.

The witness at the end of the file is `PolyaUrn`'s urn with `r = b = 1`, its paths built by
Mathlib's Ionescu-Tulcea theorem (`Kernel.traj`), at the level `c = 3/4`.
-/

open MeasureTheory ProbabilityTheory Filter
open ClassicalLean.Probability.PolyaUrn

namespace ClassicalLean.Probability.UrnVille

/-- The share of red balls lies in `[0, 1]` after any number of draws, when every draw is `0` or
`1`: the red balls are at least `0` and at most `r + n ≤ r + b + n` (and when `r + b + n = 0`,
Lean's `0 / 0 = 0`). -/
theorem urnShare_mem_Icc {Ω : Type*} (r b : ℕ) (X : ℕ → Ω → ℝ)
    (hX01 : ∀ n ω, X n ω = 0 ∨ X n ω = 1) (n : ℕ) (ω : Ω) :
    urnShare r b X n ω ∈ Set.Icc 0 1 := by
  have hbd : ∀ k, 0 ≤ urnRed r X k ω ∧ urnRed r X k ω ≤ (r : ℝ) + k := by
    intro k
    induction k with
    | zero => exact ⟨Nat.cast_nonneg r, by change (r : ℝ) ≤ r + ((0 : ℕ) : ℝ); simp⟩
    | succ k ih =>
      change 0 ≤ urnRed r X k ω + X k ω ∧ urnRed r X k ω + X k ω ≤ (r : ℝ) + ((k + 1 : ℕ) : ℝ)
      push_cast
      obtain ⟨i1, i2⟩ := ih
      rcases hX01 k ω with h | h <;> rw [h] <;> constructor <;> linarith
  obtain ⟨h0, h1⟩ := hbd n
  have hN : (0 : ℝ) ≤ ((r + b + n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hle : urnRed r X n ω ≤ ((r + b + n : ℕ) : ℝ) := by
    push_cast
    have : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
    linarith
  exact ⟨div_nonneg h0 hN, div_le_one_of_le₀ hle hN⟩

/-- The number of red balls after `n` draws is known at time `n`, when draw `n` is known at time
`n + 1`. -/
theorem urnRed_stronglyMeasurable {Ω : Type*} {m0 : MeasurableSpace Ω}
    (ℱ : Filtration ℕ m0) (r : ℕ) (X : ℕ → Ω → ℝ)
    (hX : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n)) :
    ∀ n, StronglyMeasurable[ℱ n] (urnRed r X n) := by
  intro n
  induction n with
  | zero =>
    have h : urnRed r X 0 = fun _ ↦ (r : ℝ) := by
      funext ω; rfl
    rw [h]
    exact stronglyMeasurable_const
  | succ n ih =>
    have h : urnRed r X (n + 1) = urnRed r X n + X n := by
      funext ω; rfl
    rw [h]
    exact (ih.mono (ℱ.mono (Nat.le_succ n))).add (hX n)

/-- **Pólya's urn rarely runs far up** (bridge 157). Under the hypotheses of `martingale_urnShare`
(an urn of `r` red and `b` blue balls, `r + b > 0`; draw `n` is `0` or `1`, known at time `n + 1`,
and red with chance the current share given time `n`), for every `c > 0` the chance that the share
of red balls ever reaches `c` is at most `r / ((r + b) c)`: `P(urnShare n ≥ c for some n) ≤
r / ((r + b) c)`. For `c ≤ r / (r + b)` the bound is at least `1`. -/
theorem measureReal_exists_urnShare_ge_le {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (r b : ℕ) (hrb : 0 < r + b)
    (X : ℕ → Ω → ℝ) (hX01 : ∀ n ω, X n ω = 0 ∨ X n ω = 1)
    (hX_meas : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hX_cond : ∀ n, μ[X n | ℱ n] =ᵐ[μ] urnShare r b X n) {c : ℝ} (hc : 0 < c) :
    μ.real {ω | ∃ n, c ≤ urnShare r b X n ω} ≤ (r : ℝ) / (((r : ℝ) + b) * c) := by
  have hmart := martingale_urnShare ℱ r b hrb X hX01 hX_meas hX_cond
  have hnn : ∀ n ω, 0 ≤ urnShare r b X n ω := fun n ω ↦ (urnShare_mem_Icc r b X hX01 n ω).1
  have hbound : 0 ≤ (r : ℝ) / (((r : ℝ) + b) * c) := by positivity
  have h0 : ∫ ω, urnShare r b X 0 ω ∂μ = (r : ℝ) / ((r : ℝ) + b) := by
    have h : ∀ ω, urnShare r b X 0 ω = (r : ℝ) / ((r : ℝ) + b) := fun ω ↦ by
      simp [urnShare, urnRed]
    simp [h]
  have hN : ∀ N : ℕ, μ.real {ω | ∃ n ≤ N, c ≤ urnShare r b X n ω} ≤
      (r : ℝ) / (((r : ℝ) + b) * c) := by
    intro N
    have h := MaximalInequality.measureReal_exists_le_of_supermartingale
      hmart.supermartingale hnn hc N
    rwa [h0, div_div] at h
  have hU : {ω | ∃ n, c ≤ urnShare r b X n ω} =
      ⋃ N : ℕ, {ω | ∃ n ≤ N, c ≤ urnShare r b X n ω} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, n, le_rfl, hn⟩
    · rintro ⟨N, n, -, hn⟩
      exact ⟨n, hn⟩
  have hmono : Monotone fun N : ℕ ↦ {ω | ∃ n ≤ N, c ≤ urnShare r b X n ω} :=
    fun N N' hNN' ω ⟨n, hn, h⟩ ↦ ⟨n, hn.trans hNN', h⟩
  rw [hU, measureReal_def, hmono.measure_iUnion]
  refine ENNReal.toReal_le_of_le_ofReal hbound (iSup_le fun N ↦ ?_)
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact ENNReal.ofReal_le_ofReal (hN N)

end ClassicalLean.Probability.UrnVille

open MeasureTheory ProbabilityTheory Finset ClassicalLean.Probability.PolyaUrn
  ClassicalLean.Probability.UrnVille in
/-- The hypotheses of `measureReal_exists_urnShare_ge_le` hold together: Pólya's urn itself, its
paths built by Mathlib's Ionescu-Tulcea theorem (`Kernel.traj`), as in `PolyaUrn`'s witness of
`martingale_urnShare`. A path is `ω : ℕ → Bool`; coordinate `n + 1` is draw `n` (`true` for red),
coordinate `0` plays no part. The urn starts with `r = 1` red and `b = 1` blue ball. The kernel
`κ n` draws coordinate `n + 1` red with chance the share of red balls after the draws in
coordinates `1, …, n`, a chance that depends on those draws and lies between `1 / (n + 2)` and
`(n + 1) / (n + 2)`, so every draw is random and the share moves at every step. Draw `n` is
`X n ω = 1` when coordinate `n + 1` is `true` and `0` otherwise, so it is `0` or `1`; the
filtration is `piLE`, the coordinates up to each time, so draw `n` is known at time `n + 1`; and
given time `n`, the mean of draw `n` is the current share (Mathlib's `Kernel.condExp_traj` and
`Kernel.map_traj_succ_self`, and the share at time `n` depends only on the coordinates up to `n`).
The level is `c = 3/4`: the share starts at `1/2 < 3/4`, so the event is not sure, and the bound
`1 / (2 · 3/4) = 2/3` is below `1`. -/
example := ClassicalLean.Probability.UrnVille.measureReal_exists_urnShare_ge_le
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
    (c := 3 / 4) (by norm_num)
