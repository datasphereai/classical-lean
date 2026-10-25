/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.BorelCantelli

/-!
# No stopping rule beats a fair game

If `f n` is a martingale (each step's expected change is `0` given everything up to that step),
then for any stopping rule `τ` that never waits past a fixed time `N`, the expected value at the
moment of stopping equals the expected value at the start (`integral_stoppedValue_eq`). Deciding
*when* to stop, using only what has happened so far, cannot turn a fair game into a favourable one.

## Wald's identity for a bounded stopping time

Order LEAN-21 (item 35 of the plan) adds Wald's identity: for running sums `S n` with `S 0 = 0`,
whose every step has mean `m` given the past, and a stopping rule `τ` that never waits past `N`,
`E[S τ] = m E[τ]` (`integral_stoppedValue_eq_mul`). The usual form, with independent steps of mean
`m`, follows (`integral_stoppedValue_sum_eq`). Citation: Wald 1944, "On cumulative sums of random
variables". Only stopping times bounded by a fixed `N` are covered here, and the steps need not be
independent or identically distributed, only of mean `m` given the past. `E[τ]` is written
`∫ ω, ((τ ω).untopA : ℝ) ∂μ`, the mean of the stopping time's value.

Measured in order LEAN-21's checks (check C35, exact enumeration): four step laws (means `0`,
`1/2`, `1/4`, `7/5`) with bounded stopping rules. Each hypothesis below is needed: drop it alone
and the conclusion fails at the case given (worked out by hand; the check script records the
arithmetic):

* each step of mean `m` given the past: `X₀ = ±1` fair, `X₁ = X₀`, `τ = 2` if `X₀ = 1` else `1`,
  `m = 0`: `E[S τ] = 1/2`.
* `S 0 = 0`: `S n = 1 +` a fair `±1` walk, `τ = 1`, `m = 0`: `E[S τ] = 1`.
* `τ` a stopping time: fair `±1` steps, `τ = 1` if `X₁ = −1` else `2` (it looks ahead): `1/2 ≠ 0`.
* `τ ≤ N`: a fair walk stopped when it first reaches `1`; `S τ = 1` almost surely, so
  `E[S τ] = 1`, while `m = 0` gives `m E[τ] = 0`.

Not claimed needed: that `S` is adapted, and in the independent form that `X n` is known by time
`n + 1` (both serve the proof, which builds a martingale); and `S 0 = 0` only fixes the start,
since `E[S τ] = E[S 0] + m E[τ]` follows in the same way (review r35).

## Wald's second identity (order LEAN-35)

Order LEAN-35 (item 138 of MATH-PLAN-library-2) adds **Wald's second identity**
(`integral_stoppedValue_sq_eq`): on a probability space, for steps `X n` known by time `n + 1`,
square integrable with mean `0` and second moment `σ²`, each independent of the past `𝒢 n`, and a
stopping time `τ ≤ N`, the sum `S_τ` of the first `τ` steps has `E[S_τ²] = σ² E[τ]`. Wider than
the plan's row: each step is asked to be independent only of the past, and `𝒢` is any filtration
in which step `n` is known at time `n + 1`; `GamblersRuin`'s `integral_stoppedValue_walk_sq` is the
fair `±1` case. The proof is the draft `d138-r1-s1` (written by Claude Opus 5.5 through the
Anthropic Batch API, the lane's API-CREDIT-1 work), adapted by order LEAN-35's session: inside this
namespace, binding its own types as the draft does (so this module's `variable` lines do not reach
it); its docstring rewritten (the item, the credit, `E[τ]` written out, "(variance)" read as
"(so variance)", the wider reading, `GamblersRuin`'s fair `±1` case and the proof's route); the
deprecated `memLp_finset_sum` replaced by `memLp_finsetSum`; one `show` that changed the goal
written as `change`. For its witness, on independent fair coins, this module now imports
`Mathlib.Probability.Independence.InfinitePi` and `Mathlib.Probability.BorelCantelli`; nothing
else uses them. Its hypotheses were not drop-tested by this order. Its witness is at the end of the
file.

## What Mathlib provides

The optional stopping theorem in its monotone form,
`MeasureTheory.Submartingale.expected_stoppedValue_mono`: for a submartingale and bounded stopping
times `τ ≤ π`, `E[f_τ] ≤ E[f_π]`. This module applies it to the martingale and to its negative,
with the constant stopping time `0`, to get equality. For Wald's identity:
`martingale_of_condExp_sub_eq_zero_nat`, `condExp_indep_eq`, `integrable_stoppedValue`. Searched
before item 35 was written (order LEAN-21, `grep -rniE` over Mathlib): `wald` matches only inside
an author's name ("Turnwald"); `stoppedValue.*integral|integral.*stoppedValue` 1 line, optional
stopping.
-/

open MeasureTheory ProbabilityTheory Finset

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

omit [SigmaFiniteFiltration μ 𝒢] in
/-- **Wald's identity for a bounded stopping time.** On a finite measure, let `S` be adapted and
integrable with `S 0 = 0`, and let every step `S (n + 1) − S n` have conditional mean `m` given
the past `𝒢 n`. For a stopping time `τ ≤ N`, `E[S τ] = m E[τ]`. -/
theorem integral_stoppedValue_eq_mul [IsFiniteMeasure μ] {S : ℕ → Ω → ℝ} {m : ℝ}
    (hadp : StronglyAdapted 𝒢 S) (hint : ∀ n, Integrable (S n) μ) (h0 : ∀ ω, S 0 ω = 0)
    (hstep : ∀ n, μ[S (n + 1) - S n | 𝒢 n] =ᵐ[μ] fun _ ↦ m) {τ : Ω → WithTop ℕ}
    (hτ : IsStoppingTime 𝒢 τ) {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    ∫ ω, stoppedValue S τ ω ∂μ = m * ∫ ω, ((τ ω).untopA : ℝ) ∂μ := by
  let D : ℕ → Ω → ℝ := fun n _ ↦ n * m
  have hD : ∀ n, Integrable (D n) μ := fun n ↦ integrable_const _
  have hmart : Martingale (S - D) 𝒢 μ := by
    refine martingale_of_condExp_sub_eq_zero_nat
      (fun n ↦ (hadp n).sub stronglyMeasurable_const) (fun n ↦ (hint n).sub (hD n)) fun n ↦ ?_
    have e : (S - D) (n + 1) - (S - D) n = (S (n + 1) - S n) - fun _ ↦ m := by
      funext ω; simp only [Pi.sub_apply, D]; push_cast; ring
    rw [e]
    filter_upwards [condExp_sub ((hint _).sub (hint _)) (integrable_const m) (𝒢 n), hstep n]
      with ω h1 h2
    rw [h1, condExp_const (𝒢.le n), Pi.sub_apply, h2, sub_self]
    rfl
  have h := ClassicalLean.Probability.FairGame.integral_stoppedValue_eq hmart hτ hbdd
  have hsplit : stoppedValue (S - D) τ = fun ω ↦ stoppedValue S τ ω - stoppedValue D τ ω := rfl
  rw [hsplit, integral_sub (integrable_stoppedValue ℕ hτ hint hbdd)
    (integrable_stoppedValue ℕ hτ hD hbdd)] at h
  have hS0 : ∫ ω, (S - D) 0 ω ∂μ = 0 := by simp [D, h0]
  rw [hS0, sub_eq_zero] at h
  rw [h, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by
    simp only [stoppedValue, D]; ring)

omit [SigmaFiniteFiltration μ 𝒢] in
/-- **Wald's identity, independent steps.** On a probability space, let each step `X n` be known
by time `n + 1`, integrable with mean `m`, and independent of the past `𝒢 n`. For a stopping time
`τ ≤ N`, the sum of the first `τ` steps has mean `m E[τ]`. -/
theorem integral_stoppedValue_sum_eq [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {m : ℝ}
    (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n)) (hint : ∀ n, Integrable (X n) μ)
    (hmean : ∀ n, ∫ ω, X n ω ∂μ = m)
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime 𝒢 τ) {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    ∫ ω, stoppedValue (fun n ω ↦ ∑ i ∈ range n, X i ω) τ ω ∂μ =
      m * ∫ ω, ((τ ω).untopA : ℝ) ∂μ := by
  refine integral_stoppedValue_eq_mul (fun n ↦ ?_) (fun n ↦ integrable_finsetSum _ fun i _ ↦ hint i)
    (fun ω ↦ by simp) (fun n ↦ ?_) hτ hbdd
  · exact Finset.stronglyMeasurable_fun_sum _ fun i hi ↦
      (hX i).mono (𝒢.mono (Nat.succ_le_of_lt (mem_range.mp hi)))
  · have e : (fun ω ↦ ∑ i ∈ range (n + 1), X i ω) - (fun ω ↦ ∑ i ∈ range n, X i ω) = X n := by
      funext ω; simp [sum_range_succ]
    rw [e]
    have hXm : Measurable (X n) := (hX n).measurable.mono (𝒢.le (n + 1)) le_rfl
    have := condExp_indep_eq hXm.comap_le (𝒢.le n)
      (comap_measurable (X n)).stronglyMeasurable (hind n)
    rwa [hmean n] at this

/-- **Wald's second identity for a bounded stopping time** (item 138 of MATH-PLAN-library-2; the
draft `d138-r1-s1`, written by Claude Opus 5.5 through the Anthropic Batch API, the lane's
API-CREDIT-1 work, adapted by order LEAN-35's session). On a probability space, let each step
`X n` be known by time `n + 1`, square integrable with mean `0` and second moment (so variance)
`σ²`, and independent of the past `𝒢 n`. For a stopping time `τ ≤ N`, the sum `S_τ` of the first
`τ` steps satisfies `E[S_τ²] = σ² E[τ]`, with `E[τ]` written `∫ ω, ((τ ω).untopA : ℝ) ∂μ`. Wider
than the plan's row (review r6: GENERALIZED): each step need only be independent of the past
`𝒢 n`, not of a family independent from the start, and `𝒢` is any filtration in which step `n` is
known at time `n + 1`.
`GamblersRuin`'s `integral_stoppedValue_walk_sq` is the fair `±1` case. The proof applies
`integral_stoppedValue_eq_mul` to the squares `S n²`, whose steps have conditional mean `σ²`. -/
theorem integral_stoppedValue_sq_eq {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {𝒢 : Filtration ℕ m0} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {σ : ℝ}
    (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n)) (hL2 : ∀ n, MemLp (X n) 2 μ)
    (hmean : ∀ n, ∫ ω, X n ω ∂μ = 0) (hvar : ∀ n, ∫ ω, X n ω ^ 2 ∂μ = σ ^ 2)
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime 𝒢 τ) {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    ∫ ω, (stoppedValue (fun n ω ↦ ∑ i ∈ range n, X i ω) τ ω) ^ 2 ∂μ =
      σ ^ 2 * ∫ ω, ((τ ω).untopA : ℝ) ∂μ := by
  have hSm : ∀ n, StronglyMeasurable[𝒢 n] (fun ω ↦ ∑ i ∈ range n, X i ω) := fun n ↦
    Finset.stronglyMeasurable_fun_sum _ fun i hi ↦
      (hX i).mono (𝒢.mono (Nat.succ_le_of_lt (mem_range.mp hi)))
  have hSL2 : ∀ n, MemLp (fun ω ↦ ∑ i ∈ range n, X i ω) 2 μ := fun n ↦
    memLp_finsetSum (range n) fun i _ ↦ hL2 i
  have hXint : ∀ n, Integrable (X n) μ := fun n ↦ (hL2 n).integrable (by norm_num)
  have key : ∀ a b : ℝ, |2 * a * b| ≤ a ^ 2 + b ^ 2 := fun a b ↦
    abs_le.mpr ⟨by nlinarith [sq_nonneg (a + b)], by nlinarith [sq_nonneg (a - b)]⟩
  refine ClassicalLean.Probability.FairGame.integral_stoppedValue_eq_mul
    (S := fun n ω ↦ (∑ i ∈ range n, X i ω) ^ 2) (m := σ ^ 2)
    (fun n ↦ ((hSm n).measurable.pow_const 2).stronglyMeasurable)
    (fun n ↦ (hSL2 n).integrable_sq) (fun ω ↦ by simp) (fun n ↦ ?_) hτ hbdd
  show μ[(fun ω ↦ (∑ i ∈ range (n + 1), X i ω) ^ 2) - (fun ω ↦ (∑ i ∈ range n, X i ω) ^ 2)
    | 𝒢 n] =ᵐ[μ] fun _ ↦ σ ^ 2
  have e : (fun ω ↦ (∑ i ∈ range (n + 1), X i ω) ^ 2) - (fun ω ↦ (∑ i ∈ range n, X i ω) ^ 2)
      = (fun ω ↦ 2 * ∑ i ∈ range n, X i ω) * X n + fun ω ↦ X n ω ^ 2 := by
    funext ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, sum_range_succ]
    ring
  rw [e]
  have hXm : Measurable (X n) := (hX n).measurable.mono (𝒢.le (n + 1)) le_rfl
  have hSmeas : Measurable (fun ω ↦ ∑ i ∈ range n, X i ω) :=
    (hSm n).measurable.mono (𝒢.le n) le_rfl
  have hfm : StronglyMeasurable[𝒢 n] (fun ω ↦ 2 * ∑ i ∈ range n, X i ω) :=
    ((hSm n).measurable.const_mul 2).stronglyMeasurable
  have hi1 : Integrable ((fun ω ↦ 2 * ∑ i ∈ range n, X i ω) * X n) μ := by
    refine Integrable.mono' ((hSL2 n).integrable_sq.add (hL2 n).integrable_sq)
      ((hSmeas.const_mul 2).mul hXm).aestronglyMeasurable (ae_of_all _ fun ω ↦ ?_)
    change ‖2 * (∑ i ∈ range n, X i ω) * X n ω‖ ≤ _
    rw [Real.norm_eq_abs]
    exact key _ _
  have hi2 : Integrable (fun ω ↦ X n ω ^ 2) μ := (hL2 n).integrable_sq
  have h3 : μ[X n | 𝒢 n] =ᵐ[μ] fun _ ↦ (0 : ℝ) := by
    have := condExp_indep_eq hXm.comap_le (𝒢.le n)
      (comap_measurable (X n)).stronglyMeasurable (hind n)
    rwa [hmean n] at this
  have h4 : μ[fun ω ↦ X n ω ^ 2 | 𝒢 n] =ᵐ[μ] fun _ ↦ σ ^ 2 := by
    have := condExp_indep_eq (m₁ := MeasurableSpace.comap (X n) inferInstance)
      (f := fun ω ↦ X n ω ^ 2) hXm.comap_le (𝒢.le n)
      ((comap_measurable (X n)).pow_const 2).stronglyMeasurable (hind n)
    rwa [hvar n] at this
  filter_upwards [condExp_add hi1 hi2 (𝒢 n),
    condExp_mul_of_stronglyMeasurable_left hfm hi1 (hXint n), h3, h4] with ω h1 h2 h3' h4'
  rw [h1, Pi.add_apply, h2, Pi.mul_apply, h3', h4']
  simp

end ClassicalLean.Probability.FairGame

open MeasureTheory ProbabilityTheory in
/-- The hypotheses of `integral_stoppedValue_sum_eq` hold together: under the uniform probability
on two points, the filtration that knows nothing at time `0` and everything from time `1` on; the
first step `X 0 = (0, 2)`, of mean `m = 1`, known at time `1` and independent of what time `0`
knows (nothing), and the later steps `X n = 1`, constants, so of mean `1` and independent of
everything; the stopping time `τ = 1` at the point `0` and `2` at the point `1`, which time `0`
does not need to know (no point stops at `0`) and time `1` knows, bounded by `N = 2`. -/
example := ClassicalLean.Probability.FairGame.integral_stoppedValue_sum_eq (Ω := Fin 2)
  (μ := uniformOn Set.univ)
  (𝒢 := ⟨fun n ↦ if n = 0 then ⊥ else (inferInstance : MeasurableSpace (Fin 2)),
    fun i j hij ↦ by
      rcases i with _ | i
      · exact bot_le
      · rcases j with _ | j
        · omega
        · exact le_rfl,
    fun i ↦ by rcases i with _ | i; exacts [bot_le, le_rfl]⟩)
  (X := fun n ω ↦ if n = 0 then ![0, 2] ω else 1) (m := 1)
  (fun n ↦ (StronglyMeasurable.of_discrete :
    StronglyMeasurable[(inferInstance : MeasurableSpace (Fin 2))] (_ : Fin 2 → ℝ)))
  (fun _ ↦ Integrable.of_finite)
  (fun n ↦ by
    rw [integral_fintype Integrable.of_finite]
    rcases n with _ | n <;> simp [uniformOn_univ, Measure.real, Fin.sum_univ_two])
  (fun n ↦ by
    rcases n with _ | n
    · exact indep_bot_right _
    · change Indep (MeasurableSpace.comap (fun _ : Fin 2 ↦ (1 : ℝ)) _) _ _
      rw [MeasurableSpace.comap_const]
      exact indep_bot_left _)
  (τ := fun ω ↦ if ω = 0 then 1 else 2)
  (fun i ↦ by
    rcases i with _ | i
    · change MeasurableSet[⊥] _
      convert @MeasurableSet.empty (Fin 2) ⊥
      ext ω; fin_cases ω <;> simp
    · exact (MeasurableSet.of_discrete :
        MeasurableSet[(inferInstance : MeasurableSpace (Fin 2))] _))
  (N := 2) (fun ω ↦ by fin_cases ω <;> simp)

open MeasureTheory ProbabilityTheory in
/-- The hypotheses of `integral_stoppedValue_sq_eq` hold together: on the space of coin sequences
`ℕ → Bool` with independent fair coins (Mathlib's `Measure.infinitePi` of the uniform law on
`Bool`), the filtration the coins' values generate; the steps `X n = ±1` read from coin `n + 1`, so
step `n` is known at time `n + 1` and independent of what time `n` knows; each step is bounded, so
square integrable, of mean `0` and second moment `σ² = 1`; the stopping time `τ = 1` when coin `1`
is heads and `2` otherwise, known at time `1`, bounded by `N = 2`, so it stops at two different
times. -/
example := ClassicalLean.Probability.FairGame.integral_stoppedValue_sq_eq (Ω := ℕ → Bool)
  (μ := Measure.infinitePi fun _ ↦ uniformOn Set.univ)
  (𝒢 := Filtration.natural (fun i (ω : ℕ → Bool) ↦ if ω i then (1 : ℝ) else -1)
    fun i ↦ ((measurable_of_countable fun c : Bool ↦ if c then (1 : ℝ) else -1).comp
      (measurable_pi_apply i)).stronglyMeasurable)
  (X := fun n ω ↦ if ω (n + 1) then 1 else -1) (σ := 1)
  (fun n ↦ Filtration.stronglyAdapted_natural
    (u := fun i (ω : ℕ → Bool) ↦ if ω i then (1 : ℝ) else -1) _ (n + 1))
  (fun n ↦ MemLp.of_bound ((measurable_of_countable fun c : Bool ↦ if c then (1 : ℝ) else -1).comp
      (measurable_pi_apply (n + 1))).aestronglyMeasurable 1
    (ae_of_all _ fun ω ↦ by split_ifs <;> simp))
  (fun n ↦ by
    rw [← integral_map (φ := fun ω : ℕ → Bool ↦ ω (n + 1))
      (f := fun c : Bool ↦ if c then (1 : ℝ) else -1) (measurable_pi_apply (n + 1)).aemeasurable
      (measurable_of_countable fun c : Bool ↦ if c then (1 : ℝ) else -1).aestronglyMeasurable,
      Measure.infinitePi_map_eval, integral_fintype Integrable.of_finite]
    simp only [Measure.real, uniformOn_univ]
    simp)
  (fun n ↦ by
    have h : (fun ω : ℕ → Bool ↦ (if ω (n + 1) then (1 : ℝ) else -1) ^ 2) = fun _ ↦ 1 := by
      funext ω
      split_ifs <;> norm_num
    simp only [h, integral_const, probReal_univ, smul_eq_mul, mul_one, one_pow])
  (fun n ↦ (iIndepFun_infinitePi (P := fun _ : ℕ ↦ (uniformOn Set.univ : Measure Bool))
    (X := fun _ (c : Bool) ↦ if c then (1 : ℝ) else -1)
    fun _ ↦ measurable_of_countable _).indep_comap_natural_of_lt _ (Nat.lt_succ_self n))
  (τ := fun ω ↦ if ω 1 then 1 else 2)
  (fun i ↦ by
    rcases i with _ | _ | i
    · convert MeasurableSet.empty
      ext ω
      by_cases h : ω 1 <;> simp [h]
    · have hm := (Filtration.stronglyAdapted_natural
        (u := fun i (ω : ℕ → Bool) ↦ if ω i then (1 : ℝ) else -1)
        (fun i ↦ ((measurable_of_countable fun c : Bool ↦ if c then (1 : ℝ) else -1).comp
          (measurable_pi_apply i)).stronglyMeasurable) 1).measurable
      convert hm (measurableSet_singleton (1 : ℝ)) using 1
      ext ω
      by_cases h : ω 1
      · simp [h]
      · simp [h]
        norm_num
    · convert MeasurableSet.univ
      ext ω
      by_cases h : ω 1
      · simp [h]
      · simp [h]
        norm_cast
        omega)
  (N := 2) (fun ω ↦ by split_ifs <;> simp)
