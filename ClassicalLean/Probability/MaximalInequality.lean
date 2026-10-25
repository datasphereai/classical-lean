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
# Ville's inequality over finitely many steps, the chance of falling to half, Kolmogorov's
# maximal inequality, and Doob's `L²` inequality

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
* `integral_sup_sq_le` (Doob's `L²` inequality, order LEAN-22, item 43): for a martingale `M`
  (for a filtration whose measure is σ-finite at each time, as for any finite measure),
  `E[max_{k ≤ n} M k ²] ≤ 4 E[M n ²]`; `integrable_sup_sq`: when `M n` is square-integrable, the
  maximum square is integrable, so the left side is a real mean, not Lean's junk `0`.
* `measureReal_exists_mul_abs_ge_le` (the Hájek–Rényi inequality, item 125 of MATH-PLAN-library-2,
  order LEAN-35): for a square-integrable martingale `S`, weights `c 0 ≥ c 1 ≥ ⋯ > 0` and
  `ε > 0`, the chance that `c k |S k| ≥ ε` for some `k ≤ n` is at most
  `(c 0² E[S 0²] + ∑_{k < n} c (k + 1)² E[(S (k + 1) − S k)²]) / ε²`. Wider than the plan's row:
  any finite measure, and no `S 0 = 0`. It applies `maximal_ineq` to the weighted running sum
  (the private `hajekW`), a nonnegative submartingale by `submartingale_sq`. The proof is the draft
  `d125-r3-s2` (written by Claude Opus 5.5 through the Anthropic Batch API, the lane's API-CREDIT-1
  work), adapted by order LEAN-35's session: inside this namespace after section `DoobL2`, outside
  the three sections, each declaration binding its own types as the draft does;
  `open scoped NNReal in` on the theorem in place of the draft's file-level `open scoped NNReal`
  (the draft's other `open` line is this module's own); its docstring rewritten (the item, the
  credit, `P` and `E` defined, the wider reading); one `show` that changed the goal written as
  `change`. Its hypotheses were not drop-tested by this order. Its witness is at the end of the
  file.

## Doob's `L²` inequality

The proof takes means of an inequality that holds path by path
(`runningMaxAbs_sq_add_four_mul_sum_le`): for real numbers `x 0, …, x T`, with
`y t = max_{s ≤ t} |x s|` (`runningMaxAbs`) and `σ t = 1` if `x t ≥ 0`, `σ t = −1` otherwise,

    y T ² + 4 ∑_{t < T} y t σ t (x (t + 1) − x t) ≤ 4 x T ².

For a martingale, each term `y t σ t (M (t + 1) − M t)` is a bet placed with what is known at time
`t`, so its mean is `0`; what is left is the inequality. This proof (a running quantity that
never decreases, then `(2 |x T| − y T)² ≥ 0`) was written without reading the works cited below;
nothing is claimed about whether the inequality is new. The plan's row named Mathlib's
`maximal_ineq` and the layer-cake formula, which are not used. Citations, not read: Doob 1953,
"Stochastic Processes"; Acciaio, Beiglböck, Penkner, Schachermayer and Temme 2013, "A trajectorial
interpretation of Doob's martingale inequalities".

Measured in order LEAN-22's checks (check C43, exact arithmetic): the path-by-path inequality on
20,000 random rational paths and on all 625 paths with values in `{-2, …, 2}` and 3 steps; the
inequality itself on 16,384 martingales of 3 steps whose step sizes depend on the past. Needed,
worked out by hand: the martingale (`M 0 = 1`, `M 1 = 0` for sure, `n = 1`: the mean of the
maximum square is `1`, the bound `0`). No square-integrability is assumed: for a martingale, if
`M n` is square-integrable so is every earlier `M k` (a conditional mean of it, Mathlib's
`MemLp.condExp`); and if `M n` is not, the maximum square is not integrable either, and Lean's
integrals on both sides are `0`. No finite measure is assumed: a filtration σ-finite at each
time is enough (review r43 of order LEAN-22 found the first draft's finite measure unused).

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

section DoobL2

/-- The running maximum of `|x 0|, …, |x t|`. -/
noncomputable def runningMaxAbs (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => |x 0|
  | t + 1 => max (runningMaxAbs x t) |x (t + 1)|

/-- The running maximum is at least `0`. -/
theorem runningMaxAbs_nonneg (x : ℕ → ℝ) (t : ℕ) : 0 ≤ runningMaxAbs x t := by
  cases t with
  | zero => exact abs_nonneg _
  | succ t => exact (abs_nonneg _).trans (le_max_right _ _)

/-- The running maximum is at most the sum of the `|x k|`. -/
private theorem runningMaxAbs_le_sum (x : ℕ → ℝ) (t : ℕ) :
    runningMaxAbs x t ≤ ∑ k ∈ range (t + 1), |x k| := by
  induction t with
  | zero => simp [runningMaxAbs]
  | succ t ih =>
    rw [sum_range_succ]
    have := sum_nonneg fun k (_ : k ∈ range (t + 1)) ↦ abs_nonneg (x k)
    exact max_le (by linarith [abs_nonneg (x (t + 1))]) (by linarith)

/-- Each `|x k|` with `k ≤ t` is at most the running maximum at `t`. -/
theorem abs_le_runningMaxAbs (x : ℕ → ℝ) {k t : ℕ} (hkt : k ≤ t) : |x k| ≤ runningMaxAbs x t := by
  induction t with
  | zero => rw [Nat.le_zero.mp hkt]; rfl
  | succ t ih =>
    rcases Nat.lt_or_eq_of_le hkt with h | h
    · exact (ih (Nat.lt_succ_iff.mp h)).trans (le_max_left _ _)
    · rw [h]; exact le_max_right _ _

/-- With `σ = 1` at `u ≥ 0` and `σ = −1` below: `σ (v − u) ≤ |v| − |u|`. -/
private theorem sign_mul_le (u v : ℝ) :
    (if 0 ≤ u then 1 else -1) * (v - u) ≤ |v| - |u| := by
  split_ifs with h
  · rw [abs_of_nonneg h]; linarith [le_abs_self v]
  · rw [abs_of_neg (not_le.mp h)]; linarith [neg_abs_le v]

/-- **Doob's `L²` inequality, path by path.** For any real numbers `x 0, …, x T`, with
`y t = max_{s ≤ t} |x s|` and `σ t = 1` if `x t ≥ 0`, `σ t = −1` otherwise,
`y T ² + 4 ∑_{t < T} y t σ t (x (t + 1) − x t) ≤ 4 x T ²`. -/
theorem runningMaxAbs_sq_add_four_mul_sum_le (x : ℕ → ℝ) (T : ℕ) :
    runningMaxAbs x T ^ 2 + 4 * ∑ t ∈ range T,
      runningMaxAbs x t * (if 0 ≤ x t then 1 else -1) * (x (t + 1) - x t) ≤ 4 * x T ^ 2 := by
  set y := runningMaxAbs x
  -- the invariant `I T = y T |x T| − y T ² / 2 − |x 0|² / 2 − ∑_{t<T} y t (|x (t+1)| − |x t|) ≥ 0`
  have hI : ∀ T, 0 ≤ y T * |x T| - y T ^ 2 / 2 - |x 0| ^ 2 / 2 -
      ∑ t ∈ range T, y t * (|x (t + 1)| - |x t|) := by
    intro T
    induction T with
    | zero => simp [y, runningMaxAbs]; ring_nf; rfl
    | succ T ih =>
      rw [sum_range_succ]
      have hy : y (T + 1) = max (y T) |x (T + 1)| := rfl
      rcases le_total |x (T + 1)| (y T) with h | h
      · rw [hy, max_eq_left h]; linarith
      · rw [hy, max_eq_right h]; nlinarith
  have hsum : ∑ t ∈ range T, y t * (if 0 ≤ x t then 1 else -1) * (x (t + 1) - x t) ≤
      ∑ t ∈ range T, y t * (|x (t + 1)| - |x t|) :=
    sum_le_sum fun t _ ↦ by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (sign_mul_le _ _) (runningMaxAbs_nonneg x t)
  have h0 := sq_nonneg (2 * |x T| - y T)
  have hx := sq_abs (x T)
  nlinarith [hI T, sq_nonneg (x 0)]

omit [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝒢] in
/-- For a martingale with `M n` square-integrable, `max_{k ≤ n} M k ²` is integrable (it is at most
`∑_{k ≤ n} M k ²`, and each earlier `M k` is a conditional mean of `M n`). -/
theorem integrable_sup_sq {M : ℕ → Ω → ℝ} (hM : Martingale M 𝒢 μ) {n : ℕ}
    (hL2 : MemLp (M n) 2 μ) :
    Integrable (fun ω ↦ (range (n + 1)).sup' nonempty_range_add_one (fun k ↦ M k ω ^ 2)) μ := by
  have hL2k : ∀ k ≤ n, MemLp (M k) 2 μ := fun k hk ↦
    (hL2.condExp (m := 𝒢 k) (by norm_num)).ae_eq (hM.condExp_ae_eq hk)
  refine (integrable_finsetSum (range (n + 1)) fun k hk ↦
    (hL2k k (Nat.lt_succ_iff.mp (mem_range.mp hk))).integrable_sq).mono'
    (Finset.measurable_range_sup'' fun k _ ↦
      (((hM.1 k).mono (𝒢.le k)).measurable.pow_const 2)).aestronglyMeasurable
    (ae_of_all _ fun ω ↦ ?_)
  have hnn : 0 ≤ (range (n + 1)).sup' nonempty_range_add_one (fun k ↦ M k ω ^ 2) :=
    (sq_nonneg (M 0 ω)).trans (le_sup' (fun k ↦ M k ω ^ 2) (mem_range.mpr (Nat.succ_pos n)))
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact sup'_le _ _ fun k hk ↦ single_le_sum (fun j _ ↦ sq_nonneg (M j ω)) hk

omit [IsFiniteMeasure μ] in
/-- **Doob's `L²` inequality.** For a martingale `M` for a filtration that is σ-finite at each
time, `E[max_{k ≤ n} M k ²] ≤ 4 E[M n ²]`. No square-integrability is assumed (see the module
docstring). -/
theorem integral_sup_sq_le {M : ℕ → Ω → ℝ} (hM : Martingale M 𝒢 μ) (n : ℕ) :
    ∫ ω, (range (n + 1)).sup' nonempty_range_add_one (fun k ↦ M k ω ^ 2) ∂μ ≤
      4 * ∫ ω, M n ω ^ 2 ∂μ := by
  set Y : ℕ → Ω → ℝ := fun t ω ↦ runningMaxAbs (fun k ↦ M k ω) t
  have hsupY : ∀ ω, (range (n + 1)).sup' nonempty_range_add_one (fun k ↦ M k ω ^ 2) ≤
      Y n ω ^ 2 := fun ω ↦ by
    refine sup'_le _ _ fun k hk ↦ ?_
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (abs_le_runningMaxAbs (fun k ↦ M k ω) (Nat.lt_succ_iff.mp (mem_range.mp hk))) 2
  have hsup0 : 0 ≤ᵐ[μ] fun ω ↦
      (range (n + 1)).sup' nonempty_range_add_one (fun k ↦ M k ω ^ 2) :=
    ae_of_all _ fun ω ↦ (sq_nonneg (M 0 ω)).trans
      (le_sup' (fun k ↦ M k ω ^ 2) (mem_range.mpr (Nat.succ_pos n)))
  have hmeas : ∀ k, StronglyMeasurable[𝒢 k] (M k) := fun k ↦ hM.1 k
  have hmeasm : ∀ k, StronglyMeasurable (M k) := fun k ↦ (hmeas k).mono (𝒢.le k)
  by_cases hL2 : MemLp (M n) 2 μ
  swap
  · -- not square-integrable: both sides are `0`
    have hnot : ¬ Integrable (fun ω ↦ M n ω ^ 2) μ := fun h ↦
      hL2 ((memLp_two_iff_integrable_sq (hmeasm n).aestronglyMeasurable).mpr h)
    have hnotL : ¬ Integrable (fun ω ↦
        (range (n + 1)).sup' nonempty_range_add_one (fun k ↦ M k ω ^ 2)) μ := fun h ↦
      hnot (h.mono' ((hmeasm n).aestronglyMeasurable.pow 2) (ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact le_sup' (fun k ↦ M k ω ^ 2) (mem_range.mpr (Nat.lt_succ_self n))))
    rw [integral_undef hnotL, integral_undef hnot, mul_zero]
  -- every `M k` with `k ≤ n` is square-integrable
  have hL2k : ∀ k ≤ n, MemLp (M k) 2 μ := fun k hk ↦
    (hL2.condExp (m := 𝒢 k) (by norm_num)).ae_eq (hM.condExp_ae_eq hk)
  -- `Y t` is known at time `t`, and square-integrable for `t ≤ n`
  have hYm : ∀ t, Measurable[𝒢 t] (Y t) := by
    intro t
    induction t with
    | zero => exact continuous_abs.measurable.comp (hmeas 0).measurable
    | succ t ih =>
      exact (ih.mono (𝒢.mono (Nat.le_succ t)) le_rfl).max
        (continuous_abs.measurable.comp (hmeas (t + 1)).measurable)
  have hYL2 : ∀ t ≤ n, MemLp (Y t) 2 μ := fun t ht ↦ by
    refine (memLp_finsetSum (range (t + 1)) fun k hk ↦ (hL2k k ?_).norm).of_le
      ((hYm t).mono (𝒢.le t) le_rfl).aestronglyMeasurable (ae_of_all _ fun ω ↦ ?_)
    · exact (Nat.lt_succ_iff.mp (mem_range.mp hk)).trans ht
    · rw [Real.norm_eq_abs, abs_of_nonneg (runningMaxAbs_nonneg _ _), Real.norm_eq_abs,
        abs_of_nonneg (sum_nonneg fun k _ ↦ norm_nonneg _)]
      exact runningMaxAbs_le_sum _ _
  -- the bets `H t = Y t · (sign of M t)`
  set H : ℕ → Ω → ℝ := fun t ω ↦ Y t ω * (if 0 ≤ M t ω then 1 else -1)
  have hHm : ∀ t, StronglyMeasurable[𝒢 t] (H t) := fun t ↦
    ((hYm t).mul (Measurable.ite (measurableSet_le measurable_const (hmeas t).measurable)
      measurable_const measurable_const)).stronglyMeasurable
  have hHL2 : ∀ t ≤ n, MemLp (H t) 2 μ := fun t ht ↦
    (hYL2 t ht).of_le ((hHm t).mono (𝒢.le t)).aestronglyMeasurable (ae_of_all _ fun ω ↦ by
      simp only [H, norm_mul]
      split_ifs <;> simp)
  -- each bet has mean gain `0`
  have hfair : ∀ t < n, ∫ ω, H t ω * (M (t + 1) ω - M t ω) ∂μ = 0 := fun t ht ↦ by
    have hi1 : Integrable (H t * M (t + 1)) μ := (hHL2 t ht.le).integrable_mul (hL2k (t + 1) ht)
    have hi0 : Integrable (H t * M t) μ := (hHL2 t ht.le).integrable_mul (hL2k t ht.le)
    have hce := condExp_mul_of_stronglyMeasurable_left (m := 𝒢 t) (hHm t) hi1
      (hM.integrable (t + 1))
    have h1 : ∫ ω, H t ω * M (t + 1) ω ∂μ = ∫ ω, H t ω * M t ω ∂μ := by
      have e1 : ∫ ω, H t ω * M (t + 1) ω ∂μ = ∫ ω, (μ[H t * M (t + 1) | 𝒢 t]) ω ∂μ :=
        (integral_condExp (𝒢.le t)).symm
      rw [e1]
      refine integral_congr_ae ?_
      filter_upwards [hce, hM.condExp_ae_eq (Nat.le_succ t)] with ω h1 h2
      rw [h1, Pi.mul_apply, h2]
    have e2 := integral_sub hi1 hi0
    simp only [Pi.mul_apply] at e2
    simp only [mul_sub]
    rw [e2, h1, sub_self]
  -- integrate the path-by-path inequality
  have hpath : ∀ ω, Y n ω ^ 2 + 4 * ∑ t ∈ range n, H t ω * (M (t + 1) ω - M t ω) ≤
      4 * M n ω ^ 2 := fun ω ↦ by
    simpa [H, Y, mul_assoc] using
      runningMaxAbs_sq_add_four_mul_sum_le (fun k ↦ M k ω) n
  have hiY : Integrable (fun ω ↦ Y n ω ^ 2) μ := (hYL2 n le_rfl).integrable_sq
  have hiS : ∀ t ∈ range n, Integrable (fun ω ↦ H t ω * (M (t + 1) ω - M t ω)) μ := fun t ht ↦
    (hHL2 t (mem_range.mp ht).le).integrable_mul
      ((hL2k (t + 1) (mem_range.mp ht)).sub (hL2k t (mem_range.mp ht).le))
  have hint := integral_mono
    (f := fun ω ↦ Y n ω ^ 2 + 4 * ∑ t ∈ range n, H t ω * (M (t + 1) ω - M t ω))
    (g := fun ω ↦ 4 * M n ω ^ 2) (μ := μ)
    ((hiY.add ((integrable_finsetSum _ hiS).const_mul 4))) (hL2.integrable_sq.const_mul 4) hpath
  rw [integral_add hiY ((integrable_finsetSum _ hiS).const_mul 4), integral_const_mul,
    integral_finsetSum _ hiS, sum_eq_zero fun t ht ↦ hfair t (mem_range.mp ht), mul_zero,
    add_zero, integral_const_mul] at hint
  exact (integral_mono_of_nonneg hsup0 hiY (ae_of_all _ hsupY)).trans hint

end DoobL2

/-- The weighted running sum `c₀² S₀² + ∑_{j<k} c_{j+1}² (S_{j+1}² − S_j²)`. -/
private noncomputable def hajekW {Ω : Type*} (c : ℕ → ℝ) (S : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  c 0 ^ 2 * S 0 ω ^ 2 + ∑ j ∈ range k, c (j + 1) ^ 2 * (S (j + 1) ω ^ 2 - S j ω ^ 2)

private lemma hajekW_zero {Ω : Type*} (c : ℕ → ℝ) (S : ℕ → Ω → ℝ) (ω : Ω) :
    hajekW c S 0 ω = c 0 ^ 2 * S 0 ω ^ 2 := by
  simp [hajekW]

private lemma hajekW_succ {Ω : Type*} (c : ℕ → ℝ) (S : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    hajekW c S (k + 1) ω =
      hajekW c S k ω + c (k + 1) ^ 2 * (S (k + 1) ω ^ 2 - S k ω ^ 2) := by
  unfold hajekW
  rw [sum_range_succ]
  ring

open scoped NNReal in
/-- **The Hájek–Rényi inequality** (item 125 of MATH-PLAN-library-2; the draft `d125-r3-s2`,
written by Claude Opus 5.5 through the Anthropic Batch API, the lane's API-CREDIT-1 work, adapted
by order LEAN-35's session). For a martingale `S` with each `S n` square-integrable, weights
`c 0 ≥ c 1 ≥ ⋯ > 0` and `ε > 0`, with increments `ξ 0 = S 0`, `ξ (k+1) = S (k+1) − S k`:
`P(∃ k ≤ n, c k |S k| ≥ ε) ≤ ε⁻² ∑_{k ≤ n} c k ² E[ξ k ²]`, where `P` is `μ.real` and `E[·]` is
`∫ · ∂μ` for the finite measure `μ`. Wider than the plan's row (round 1's
review: GENERALIZED): `μ` is any finite measure, not only a probability, and `S 0` need not be `0`
(its term `c 0² E[S 0²]` is `0` in the classical form, where `S 0 = 0`); the weights are indexed
from `0`. The proof applies Doob's maximal inequality (Mathlib's `maximal_ineq`) to the weighted
running sum `c 0² S 0² + ∑_{j<k} c (j+1)² (S (j+1)² − S j²)`, a nonnegative submartingale because
`S ²` is a submartingale (`submartingale_sq`) and the weights decrease. -/
theorem measureReal_exists_mul_abs_ge_le {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {S : ℕ → Ω → ℝ} (hS : Martingale S 𝒢 μ)
    (hS2 : ∀ n, MemLp (S n) 2 μ) {c : ℕ → ℝ} (hc : ∀ k, 0 < c k) (hanti : Antitone c)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    μ.real {ω | ∃ k ≤ n, ε ≤ c k * |S k ω|} ≤
      (c 0 ^ 2 * ∫ ω, S 0 ω ^ 2 ∂μ +
        ∑ k ∈ range n, c (k + 1) ^ 2 * ∫ ω, (S (k + 1) ω - S k ω) ^ 2 ∂μ) / ε ^ 2 := by
  have hX : ∀ k, Integrable (fun ω ↦ S k ω ^ 2) μ := fun k ↦ (hS2 k).integrable_sq
  have hsq := ClassicalLean.Probability.MaximalInequality.submartingale_sq hS hS2
  have hWm : ∀ k, Measurable[𝒢 k] (hajekW c S k) := by
    intro k
    induction k with
    | zero =>
      rw [show hajekW c S 0 = fun ω ↦ c 0 ^ 2 * S 0 ω ^ 2 from funext (hajekW_zero c S)]
      exact ((hS.1 0).measurable.pow_const 2).const_mul _
    | succ k ih =>
      rw [show hajekW c S (k + 1) = fun ω ↦ hajekW c S k ω +
          c (k + 1) ^ 2 * (S (k + 1) ω ^ 2 - S k ω ^ 2) from funext (hajekW_succ c S k)]
      exact (ih.mono (𝒢.mono (Nat.le_succ k)) le_rfl).add
        ((((hS.1 (k + 1)).measurable.pow_const 2).sub
          (((hS.1 k).measurable.mono (𝒢.mono (Nat.le_succ k)) le_rfl).pow_const 2)).const_mul _)
  have hWint : ∀ k, Integrable (hajekW c S k) μ := by
    intro k
    induction k with
    | zero =>
      rw [show hajekW c S 0 = fun ω ↦ c 0 ^ 2 * S 0 ω ^ 2 from funext (hajekW_zero c S)]
      exact (hX 0).const_mul _
    | succ k ih =>
      rw [show hajekW c S (k + 1) = fun ω ↦ hajekW c S k ω +
          c (k + 1) ^ 2 * (S (k + 1) ω ^ 2 - S k ω ^ 2) from funext (hajekW_succ c S k)]
      exact ih.add (((hX (k + 1)).sub (hX k)).const_mul _)
  have hdom : ∀ k ω, c k ^ 2 * S k ω ^ 2 ≤ hajekW c S k ω := by
    intro k
    induction k with
    | zero => intro ω; rw [hajekW_zero]
    | succ k ih =>
      intro ω
      rw [hajekW_succ]
      have h1 := ih ω
      have hcc : c (k + 1) ^ 2 ≤ c k ^ 2 :=
        pow_le_pow_left₀ (hc _).le (hanti (Nat.le_succ k)) 2
      have h2 := mul_le_mul_of_nonneg_right hcc (sq_nonneg (S k ω))
      linarith
  have hWnn : ∀ k ω, 0 ≤ hajekW c S k ω := fun k ω ↦
    (mul_nonneg (sq_nonneg _) (sq_nonneg _)).trans (hdom k ω)
  have hadp : StronglyAdapted 𝒢 (hajekW c S) := fun k ↦ (hWm k).stronglyMeasurable
  have hdiff : ∀ i, hajekW c S (i + 1) - hajekW c S i =
      c (i + 1) ^ 2 • ((fun ω ↦ S (i + 1) ω ^ 2) - (fun ω ↦ S i ω ^ 2)) := by
    intro i
    funext ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hajekW_succ]
    ring
  have hWsub : Submartingale (hajekW c S) 𝒢 μ := by
    refine submartingale_of_condExp_sub_nonneg_nat hadp hWint fun i ↦ ?_
    rw [hdiff i]
    filter_upwards [condExp_smul (m := 𝒢 i) (c (i + 1) ^ 2)
        ((fun ω ↦ S (i + 1) ω ^ 2) - (fun ω ↦ S i ω ^ 2)),
      hsq.condExp_sub_nonneg (Nat.le_succ i)] with ω h1 h2
    rw [h1, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (sq_nonneg _) h2
  -- the mean of each step of `S ²` is the mean square increment
  have hinc : ∀ j, ∫ ω, (S (j + 1) ω ^ 2 - S j ω ^ 2) ∂μ =
      ∫ ω, (S (j + 1) ω - S j ω) ^ 2 ∂μ := by
    intro j
    have hprod : Integrable (S j * S (j + 1)) μ := (hS2 j).integrable_mul (hS2 (j + 1))
    have hprod' : Integrable (fun ω ↦ S j ω * S (j + 1) ω) μ := hprod
    have hcross : ∫ ω, S j ω * S (j + 1) ω ∂μ = ∫ ω, S j ω ^ 2 ∂μ := by
      have hce := condExp_mul_of_stronglyMeasurable_left (m := 𝒢 j) (hS.1 j) hprod
        (hS.integrable (j + 1))
      calc ∫ ω, S j ω * S (j + 1) ω ∂μ = ∫ ω, (μ[S j * S (j + 1) | 𝒢 j]) ω ∂μ :=
            (integral_condExp (𝒢.le j)).symm
        _ = ∫ ω, S j ω ^ 2 ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [hce, hS.condExp_ae_eq (Nat.le_succ j)] with ω h1 h2
            rw [h1, Pi.mul_apply, h2, sq]
    have e1 : (fun ω ↦ (S (j + 1) ω - S j ω) ^ 2) = fun ω ↦
        (S (j + 1) ω ^ 2 - S j ω ^ 2) - 2 * (S j ω * S (j + 1) ω - S j ω ^ 2) := by
      funext ω; ring
    have hd : Integrable (fun ω ↦ S (j + 1) ω ^ 2 - S j ω ^ 2) μ := (hX _).sub (hX _)
    have hc2 : Integrable (fun ω ↦ 2 * (S j ω * S (j + 1) ω - S j ω ^ 2)) μ :=
      (hprod'.sub (hX j)).const_mul 2
    rw [e1, integral_sub hd hc2, integral_const_mul, integral_sub hprod' (hX j), hcross,
      sub_self, mul_zero, sub_zero]
  have hEW : ∫ ω, hajekW c S n ω ∂μ = c 0 ^ 2 * ∫ ω, S 0 ω ^ 2 ∂μ +
      ∑ k ∈ range n, c (k + 1) ^ 2 * ∫ ω, (S (k + 1) ω - S k ω) ^ 2 ∂μ := by
    have hterm : ∀ j ∈ range n, Integrable
        (fun ω ↦ c (j + 1) ^ 2 * (S (j + 1) ω ^ 2 - S j ω ^ 2)) μ := fun j _ ↦
      ((hX (j + 1)).sub (hX j)).const_mul _
    have h0 : Integrable (fun ω ↦ c 0 ^ 2 * S 0 ω ^ 2) μ := (hX 0).const_mul _
    simp only [hajekW]
    rw [integral_add h0 (integrable_finsetSum _ hterm), integral_const_mul,
      integral_finsetSum _ hterm]
    congr 1
    refine sum_congr rfl fun j _ ↦ ?_
    rw [integral_const_mul, hinc]
  -- Doob's maximal inequality for `W` at the level `ε²`
  set e : ℝ≥0 := ⟨ε ^ 2, by positivity⟩ with he_def
  have he : (e : ℝ) = ε ^ 2 := rfl
  set B : Set Ω := {ω | (e : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one
      (fun k ↦ hajekW c S k ω)} with hB
  have hmax := maximal_ineq hWsub (fun k ω ↦ hWnn k ω) (ε := e) n
  have hAB : {ω | ∃ k ≤ n, ε ≤ c k * |S k ω|} ⊆ B := by
    rintro ω ⟨k, hk, hkε⟩
    change (e : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one (fun k ↦ hajekW c S k ω)
    have h1 : ε ^ 2 ≤ c k ^ 2 * S k ω ^ 2 := by
      have := pow_le_pow_left₀ hε.le hkε 2
      rw [mul_pow, sq_abs] at this
      exact this
    exact (he.le.trans h1).trans ((hdom k ω).trans
      (le_sup' (fun k ↦ hajekW c S k ω) (mem_range.mpr (Nat.lt_succ_of_le hk))))
  have hint' : ∫ ω in B, hajekW c S n ω ∂μ ≤ ∫ ω, hajekW c S n ω ∂μ :=
    setIntegral_le_integral (hWint n) (ae_of_all _ fun ω ↦ hWnn n ω)
  have h1 : (↑e * μ B).toReal ≤ ∫ ω in B, hajekW c S n ω ∂μ := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmax
    rwa [ENNReal.toReal_ofReal (integral_nonneg fun ω ↦ hWnn n ω)] at this
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, he] at h1
  have hB' : μ.real {ω | ∃ k ≤ n, ε ≤ c k * |S k ω|} ≤ (μ B).toReal := measureReal_mono hAB
  rw [le_div_iff₀ (by positivity)]
  have h3 := mul_le_mul_of_nonneg_right hB' (sq_nonneg ε)
  linarith

end ClassicalLean.Probability.MaximalInequality

open MeasureTheory ProbabilityTheory Filter in
/-- The hypotheses of `measureReal_exists_abs_ge_le` hold together: under the uniform probability
on two points, the filtration that knows nothing at time `0` and everything from time `1` on, and
the walk `S 0 = 0`, `S n = (1, −1)` for `n ≥ 1` (one fair `±1` step, then still): `S` is adapted
(`S 0` is a constant), its conditional mean given time `0` is its mean `0 = S 0`, and from time `1`
on it is known, so it is a martingale; each `S n` is bounded, so square integrable; `ε = 1/2 > 0`,
`n = 2`. -/
example := ClassicalLean.Probability.MaximalInequality.measureReal_exists_abs_ge_le (Ω := Fin 2)
  (μ := uniformOn Set.univ)
  (𝒢 := ⟨fun n ↦ if n = 0 then ⊥ else (inferInstance : MeasurableSpace (Fin 2)),
    fun i j hij ↦ by
      rcases i with _ | i
      · exact bot_le
      · rcases j with _ | j
        · omega
        · exact le_rfl,
    fun i ↦ by rcases i with _ | i; exacts [bot_le, le_rfl]⟩)
  (S := fun n ω ↦ if n = 0 then 0 else ![1, -1] ω)
  ⟨fun n ↦ by
      rcases n with _ | n
      · exact (stronglyMeasurable_const : StronglyMeasurable[⊥] fun _ : Fin 2 ↦ (0 : ℝ))
      · exact (StronglyMeasurable.of_discrete :
          StronglyMeasurable[(inferInstance : MeasurableSpace (Fin 2))] (_ : Fin 2 → ℝ)),
    fun i j hij ↦ by
      rcases i with _ | i
      · change condExp ⊥ (uniformOn Set.univ) _ =ᵐ[uniformOn Set.univ] _
        rw [condExp_bot]
        refine Eventually.of_forall fun ω ↦ ?_
        rcases j with _ | j
        · simp
        · rw [integral_fintype Integrable.of_finite]
          simp [uniformOn_univ, Measure.real, Fin.sum_univ_two]
      · rcases j with _ | j
        · omega
        · change condExp (inferInstance : MeasurableSpace (Fin 2)) (uniformOn Set.univ) _ =ᵐ[_] _
          rw [condExp_of_stronglyMeasurable le_rfl StronglyMeasurable.of_discrete
            Integrable.of_finite]
          exact Eventually.of_forall fun ω ↦ by simp⟩
  (fun _ ↦ MemLp.of_discrete) (ε := 1 / 2) (by norm_num) (n := 2)

open MeasureTheory ProbabilityTheory Filter in
/-- The hypotheses of `integral_sup_sq_le` hold together: under the uniform probability on two
points, the filtration that knows nothing at time `0` and everything from time `1` on, and the walk
`M 0 = 0`, `M n = (1, −1)` for `n ≥ 1` (one fair `±1` step, then still): `M` is adapted (`M 0` is a
constant), its conditional mean given time `0` is its mean `0 = M 0`, and from time `1` on it is
known, so it is a martingale; `n = 2`. -/
example := ClassicalLean.Probability.MaximalInequality.integral_sup_sq_le (Ω := Fin 2)
  (μ := uniformOn Set.univ)
  (𝒢 := ⟨fun n ↦ if n = 0 then ⊥ else (inferInstance : MeasurableSpace (Fin 2)),
    fun i j hij ↦ by
      rcases i with _ | i
      · exact bot_le
      · rcases j with _ | j
        · omega
        · exact le_rfl,
    fun i ↦ by rcases i with _ | i; exacts [bot_le, le_rfl]⟩)
  (M := fun n ω ↦ if n = 0 then 0 else ![1, -1] ω)
  ⟨fun n ↦ by
      rcases n with _ | n
      · exact (stronglyMeasurable_const : StronglyMeasurable[⊥] fun _ : Fin 2 ↦ (0 : ℝ))
      · exact (StronglyMeasurable.of_discrete :
          StronglyMeasurable[(inferInstance : MeasurableSpace (Fin 2))] (_ : Fin 2 → ℝ)),
    fun i j hij ↦ by
      rcases i with _ | i
      · change condExp ⊥ (uniformOn Set.univ) _ =ᵐ[uniformOn Set.univ] _
        rw [condExp_bot]
        refine Eventually.of_forall fun ω ↦ ?_
        rcases j with _ | j
        · simp
        · rw [integral_fintype Integrable.of_finite]
          simp [uniformOn_univ, Measure.real, Fin.sum_univ_two]
      · rcases j with _ | j
        · omega
        · change condExp (inferInstance : MeasurableSpace (Fin 2)) (uniformOn Set.univ) _ =ᵐ[_] _
          rw [condExp_of_stronglyMeasurable le_rfl StronglyMeasurable.of_discrete
            Integrable.of_finite]
          exact Eventually.of_forall fun ω ↦ by simp⟩
  (n := 2)

open MeasureTheory ProbabilityTheory Filter in
/-- The hypotheses of `measureReal_exists_mul_abs_ge_le` hold together: under the uniform
probability on two points, the filtration that knows nothing at time `0` and everything from
time `1` on, and the walk `S 0 = 1/2`, `S n = (3/2, −1/2)` for `n ≥ 1` (a start that is not `0`,
then one fair `±1` step): `S` is adapted (`S 0` is a constant), its conditional mean given time `0`
is its mean `1/2 = S 0`, and from time `1` on it is known, so it is a martingale; each `S n` is
bounded, so square integrable; the weights `c k = 1/(k + 1)`, positive and strictly decreasing;
`ε = 3/4 > 0`; the horizon `n = 1`, so both increments it counts, `S 0` and `S 1 − S 0`, are not
`0` (the walk stops moving only after the horizon). The witness was proposed by order LEAN-35's
review (c). -/
example := ClassicalLean.Probability.MaximalInequality.measureReal_exists_mul_abs_ge_le (Ω := Fin 2)
  (μ := uniformOn Set.univ)
  (𝒢 := ⟨fun n ↦ if n = 0 then ⊥ else (inferInstance : MeasurableSpace (Fin 2)),
    fun i j hij ↦ by
      rcases i with _ | i
      · exact bot_le
      · rcases j with _ | j
        · omega
        · exact le_rfl,
    fun i ↦ by rcases i with _ | i; exacts [bot_le, le_rfl]⟩)
  (S := fun n ω ↦ if n = 0 then 1 / 2 else ![3 / 2, -1 / 2] ω)
  ⟨fun n ↦ by
      rcases n with _ | n
      · exact (stronglyMeasurable_const : StronglyMeasurable[⊥] fun _ : Fin 2 ↦ (1 / 2 : ℝ))
      · exact (StronglyMeasurable.of_discrete :
          StronglyMeasurable[(inferInstance : MeasurableSpace (Fin 2))] (_ : Fin 2 → ℝ)),
    fun i j hij ↦ by
      rcases i with _ | i
      · change condExp ⊥ (uniformOn Set.univ) _ =ᵐ[uniformOn Set.univ] _
        rw [condExp_bot]
        refine Eventually.of_forall fun ω ↦ ?_
        rcases j with _ | j
        · simp
        · rw [integral_fintype Integrable.of_finite]
          simp [uniformOn_univ, Measure.real, Fin.sum_univ_two]
          norm_num
      · rcases j with _ | j
        · omega
        · change condExp (inferInstance : MeasurableSpace (Fin 2)) (uniformOn Set.univ) _ =ᵐ[_] _
          rw [condExp_of_stronglyMeasurable le_rfl StronglyMeasurable.of_discrete
            Integrable.of_finite]
          exact Eventually.of_forall fun ω ↦ by simp⟩
  (fun _ ↦ MemLp.of_discrete) (c := fun k ↦ 1 / ((k : ℝ) + 1)) (fun _ ↦ Nat.one_div_pos_of_nat)
  (fun i j hij ↦ one_div_le_one_div_of_le (by positivity)
    (by exact_mod_cast Nat.add_le_add_right hij 1))
  (ε := 3 / 4) (by norm_num) (n := 1)
