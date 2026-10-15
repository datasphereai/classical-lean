/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Probability.FairGame
import ClassicalLean.Probability.MaximalInequality
import Mathlib.Probability.Process.HittingTime
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.HasLawExists
import ClassicalLean.NumberTheory.LucasSequence

/-!
# Gambler's ruin for the fair and the biased `±1` walk

A walk starts at `0` and moves up or down by `1` at each step (`walk X n = X 0 + ⋯ + X (n − 1)`),
each step `X n = ±1` independent of the past; the fair walk's steps have mean `0`. `exitTime X a b`
is the first time the walk is at `a` or above, or at `-b` or below (`⊤` if never). Order LEAN-22
(item 44 of the plan) proves, for whole numbers `a, b ≥ 0`:

* `ae_exitTime_ne_top`: the walk leaves `(-b, a)` with chance `1`;
* `measureReal_hit_eq`: it reaches `a` before `-b` with chance `b / (a + b)`
  (`add_mul_measureReal_hit_eq`: `(a + b) P = b`, with no division);
* `integral_exitTime_eq`: the mean time until it reaches `a` or `-b` is `a b`, and
  `integrable_exitTime`: that mean is finite.

The steps: Wald's identity at a bounded stopping time (the library's `FairGame`) gives
`E[S τ'] = 0` and `E[S τ' ²] = E[τ']` for the exit time capped at `N`
(`integral_stoppedValue_walk`, `integral_stoppedValue_walk_sq`); up to the exit time the walk
stays in `[-b, a]`, since it moves by `1` through whole numbers (`walk_mem_Icc_of_le_exitTime`);
so `E[τ'] ≤ (a + b)²`, and Markov's inequality makes the exit time finite with chance `1`. Letting
`N` grow (dominated convergence for the walk, monotone convergence for the time), `E[S τ] = 0`
and `E[τ] = E[S τ ²]`. At the exit time the walk is at `a` on the event of reaching `a` first and
at `-b` otherwise, so `a P − b (1 − P) = 0` and `E[τ] = a² P + b² (1 − P) = a b`.

## Hypotheses

Measured in order LEAN-22's checks (check C44, exact arithmetic): `b / (a + b)` and
`(a − x)(x + b)` solve the boundary problems of the walk started at `x`; and for `a, b` from `1`
to `4`, the exact law of the walk stopped at the exit time or at step 200 gives a chance of `a`
first within the unstopped mass of `b / (a + b)`, and `E[min(τ, 200)] ≤ a b`. Each hypothesis is
needed; drop it alone and a conclusion fails (the first two cases computed exactly by the checks,
the rest worked out by hand):

* steps `±1`: fair steps of `±2` with `a = b = 1` never land on `1`, so the chance is `0`, not
  `1/2`; with `a = 1`, `b = 2` the mean time is `1`, not `2`.
* mean `0`: every step `+1` with `a = b = 1` gives chance `1`, not `1/2`.
* independence: `X n = X 0` for every `n`, `X 0` fair, `a = 1`, `b = 2`: chance `1/2` (not `2/3`)
  and mean time `3/2` (not `2`).

* each step known by the next time: with the filtration that knows nothing at every time,
  independence holds for any steps, and `X n = X 0` as above gives `1/2`, not `2/3` (review r44).
* a probability measure: the zero measure satisfies the other hypotheses and gives chance `0`.

No hypothesis on `a` and `b` is needed (worked out by hand): with `a = 0 < b` the event holds at
`n = 0` and the chance is `1 = b / b`; with `b = 0` the condition `-0 < walk 0` fails, so the chance
is `0`; with `a = b = 0` the chance is Lean's `0 / 0 = 0`; in all three the exit time is `0`.

## The biased walk (order LEAN-28, item 84)

Each step is `1` with chance `p` and `-1` otherwise (`μ.real {X n = 1} = p` for every `n`), known by
the next time and independent of the past, as above; `r = (1 - p) / p`.

* `ae_exitTime_ne_top_of_biased`: the walk leaves `(-b, a)` with chance `1`, for **every** `p`
  (wider than the plan's `0 < p < 1`, `p ≠ 1/2`). At `p = 1/2` it is `ae_exitTime_ne_top`;
  otherwise Wald's identity (`FairGame`) gives `(2 p - 1) E[τ ∧ N] = E[S (τ ∧ N)]`, at most `a + b`
  in size, so the capped exit times have mean at most `(a + b) / |2 p - 1|` and Markov's inequality
  finishes as before.
* `measureReal_hit_eq_of_biased`: for `0 < p < 1`, `p ≠ 1/2`, the walk reaches `a` before `-b`
  with chance `(r ^ b - 1) / (r ^ (a + b) - 1)`. Since `E[r ^ X n] = p r + (1 - p) / r = 1`,
  `r ^ (walk n)` is a martingale; stopped at the exit time capped at `N` it has mean `1`; it stays
  between `r ^ (-b)` and `r ^ a`, so dominated convergence gives `E[r ^ (walk τ)] = 1`, that is
  `r ^ a P + r ^ (-b) (1 - P) = 1`. At `a = b = 0` both sides are `0` (the right one Lean's
  `0 / 0`).
* `measureReal_exists_ge_le_of_biased`: for `0 < p < 1 - p`, the chance that the walk ever reaches
  `a` is at most `(p / (1 - p)) ^ a`: the martingale `r ^ (walk n)` is nonnegative with mean `1`,
  and on reaching `a` it is at least `r ^ a`; Ville's inequality (`MaximalInequality`, finite
  horizon) bounds each horizon `N`, and the events grow with `N` (continuity of the measure from
  below).
* The hypotheses hold together: the first `example` at the end of the file, at `p = 1/3`
  (independent steps from Mathlib's `ProbabilityTheory.exists_iid`, which brings in
  `Mathlib.Probability.HasLawExists`).

Which hypotheses are needed (order LEAN-28's `checks.py`, exact, unless a row says otherwise; each
case keeps the others):

* `p > 0` (second theorem): at `p = 0` Lean's `r = 1 / 0 = 0` makes the formula
  `(0 - 1) / (0 - 1) = 1` at `a = b = 1`, while the walk falls to `-1` first: chance `0` (the plan's
  junk-value case). For the third theorem `p > 0` is not needed (at `p = 0` the walk only falls:
  chance `1 ≤ 0 ^ 0 = 1` at `a = 0`, `0` after); it is kept for the proof's `r = (1 - p) / p`.
* `p < 1` (second theorem): not needed by a case (at `p = 1`, `r = 0` and Lean's `0 ^ 0 = 1` make
  the formula equal the true chance for every `a`, `b`); kept for the proof.
* `p ≠ 1/2` (second theorem): at `p = 1/2`, `r = 1` and the formula is Lean's `0 / 0 = 0`, against
  the fair walk's `b / (a + b) = 1/2` at `a = b = 1`.
* `p < 1 - p` (third theorem): for `1/2 ≤ p < 1` the bound is at least `1` and holds; at `p = 1`
  Lean's `p / (1 - p) = 1 / 0 = 0` makes the bound `0` at `a = 1`, against a chance `1`.
* the steps' single law (`hp` with one `p`): steps `+1, -1, +1, …` (deterministic, so independent)
  never leave `(-1, 2)`; for the other two, fair steps with `p = 1/3` stated give `1/3` against
  `1/2` (second, `a = b = 1`) and a chance `5/8 > 1/2` of reaching `1` within three steps (third).
* steps `±1`: steps `0` (with `p = 0`) never leave `(-1, 1)` (first theorem); steps `+1` with chance
  `1/3` and `-2` otherwise reach `1` before `-2` with chance `1/3`, against the formula's `3/7`
  (second, `a = 1`, `b = 2`); steps `+1` with chance `1/3` and `+2` otherwise reach `1` with chance
  `1 > 1/2` (third, `a = 1`). Steps that are never `1`, such as `±2`, would not do for the second
  and third: through `hp` they force `p = 0`, which those theorems exclude (cold review r84).
* independence: `X n = (-1) ^ n X 0` with `X 0` fair never leaves `(-2, 2)`; `X n = X 0` with up
  chance `1/3`, `a = 1`, `b = 2`, gives `1/3` against `3/7`; three paths of mass `1/3`, each step
  `+1` on exactly one, reach `1` with chance `2/3 > 1/2`. With the filtration that knows nothing,
  independence holds and the same steps break only "each step known by the next time".
* a probability measure: needed by the first theorem (cold review r84; the second `example` at
  the end of the file): on one point of mass `∞`, Lean's `μ.real` of every set is
  `∞.toReal = 0`, so `hp` holds with `p = 0` for the steps `+1, -1, +1, …`, which are independent
  and known in time, and the walk never leaves `(-1, 2)`: the set where it stays has mass `∞`, not
  `0`. For the second and third theorems it follows from the others (by hand): independence of
  the step's set `{X n = 1}` from the whole space gives `μ s = μ s · μ univ`, so when the mass is
  not `1` the step's set has measure `0` or `∞`, its `μ.real` is `0`, and `hp` forces `p = 0`,
  against `p > 0`. (The mass is then `0` or `∞`, as the whole space, in both σ-algebras, gives
  `μ univ = μ univ · μ univ`.)

## The ruin chance as Lucas numbers (order LEAN-29, item 95)

* `measureReal_hit_eq_lucasU`: for `0 < p < 1` the walk reaches `a` before `-b` with chance
  `U b / U (a + b)`, where `U = lucasU (1 + r) r` is the Lucas sequence
  (`NumberTheory/LucasSequence`) whose characteristic roots are `1` and `r = (1 - p) / p`; the
  shared object is the recurrence `h x = p h (x + 1) + (1 - p) h (x - 1)`. **Wider than item 84**:
  there is no `p ≠ 1/2`. At `p = 1/2`, `r = 1`, `lucasU 2 1 n = n`, and the formula is the fair
  walk's `b / (a + b)`; for `p ≠ 1/2` it is item 84's `(r ^ b - 1) / (r ^ (a + b) - 1)` with both
  terms divided by `r - 1` (`lucasU_of_roots`). One formula covers the fair and the biased walk.
  At `a = b = 0` both sides are `0`: the event is empty, and `U 0 / U 0` is Lean's `0 / 0`.

Which hypotheses are needed, each case keeping the others (order LEAN-29's exact checks, lane
`lean/LEAN-29-checks.py`, and the order's own script `checks95.py`, kept with the order's evidence
in `~/lean/lean29-checks/` on DSMain, outside the repository; each by the label of its line, which
computes the chance; or by hand, as said). Which hypothesis a row's model breaks, and that it keeps
the others, is by hand in every row.

* `p > 0` (`95.drop.hp0`): at `p = 0` Lean's `r = 1 / 0 = 0`, so `U = lucasU 1 0` and
  `U 1 / U 2 = 1` at `a = b = 1`, while the walk falls to `-1` first: chance `0`.
* `p < 1`: not needed (`95.p1`: at `p = 1` the formula is right in every cell of the grid; by
  hand, `r = 0` and `U = lucasU 1 0` is `0, 1, 1, 1, …`, which gives the true chance for every `a`
  and `b`; and, by hand, `p > 1` cannot occur, since `hp` makes `p` a chance); kept because the
  route goes through item 84's theorem, which asks for it.
* no `p ≠ 1/2` is asked: the cells with `p = 1/2` of `95.grid` hold.
* each step known by the next time (`95.mine.copy`): the filtration that knows nothing, with every
  step equal to the first, up with chance `1/3` (`r = 2`, `U = lucasU 3 2`): independence holds,
  this hypothesis fails; at `(a, b) = (1, 2)` the chance is `1/3`, against `U 2 / U 3 = 3/7`.
* independence (`95.mine.copy`): the steps' own filtration, with every step equal to the first:
  `1/3` against `3/7`.
* steps `±1` (`95.mine.hpm`): independent steps `+1` with chance `1/3` and `-2` otherwise,
  `(a, b) = (1, 2)`: `1/3` against `3/7`.
* the steps' single law (`95.mine.hp`): fair steps with `p = 1/3` stated, `(a, b) = (1, 1)`: `1/2`
  against `U 1 / U 2 = 1/3`.
* a probability measure (an instance of the section): follows from the others, by hand, as for
  item 84's second theorem above.
* The hypotheses hold together: the last `example` at the end of the file (coins with three equally
  likely faces, a step up when the coin shows `0`, so `p = 1/3`; `a = 1`, `b = 2`).

## What Mathlib provides

Hitting times as stopping times (`hittingAfter`, `Adapted.isStoppingTime_hittingAfter`),
`IsStoppingTime.min_const`, `integrable_stoppedValue`, `condExp_indep_eq`,
`condExp_mul_of_stronglyMeasurable_left`, dominated and monotone convergence. No random walk and no
gambler's ruin: `gambler|ruin` has 2 unrelated hits and `random ?walk|simple random|symmetric walk`
none in Mathlib v4.34.0 (order LEAN-22's search), and `biased.*walk|asymmetric.*walk` none, pinned
and on master (order LEAN-28's search). The biased part also uses
`martingale_of_condExp_sub_eq_zero_nat`, `ProbabilityTheory.exists_iid`,
`iIndepFun.indep_comap_natural_of_lt` and `Monotone.measure_iUnion`.

For order LEAN-29 (item 95, row X4 of MATH-PLAN-library-2, run by the plan's check script
`MATH-PLAN-library-2-checks.py`, line `row.X4`, at 2026-10-15 02:19 UTC, before item 95's text was
written): `lucas.*(ruin|walk)|ruin.*lucas` gave 0 lines in pinned Mathlib, 0 in Mathlib master at
`2da3ab0a`, and 0 in the library; the library's matches now are this module's own text. Item 95
uses the library's `lucasU`, `lucasU_add_two` and `lucasU_of_roots`.
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology

namespace ClassicalLean.Probability.GamblersRuin

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}

/-- The walk: the sum of the first `n` steps. -/
def walk (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ := ∑ i ∈ range n, X i ω

/-- The first time the walk is at `a` or above, or at `-b` or below (`⊤` if never). -/
noncomputable def exitTime (X : ℕ → Ω → ℝ) (a b : ℕ) : Ω → WithTop ℕ :=
  hittingAfter (walk X) {x | x ≤ -(b : ℝ) ∨ (a : ℝ) ≤ x} 0

section Path

variable {X : ℕ → Ω → ℝ}

omit m0 in
/-- The walk starts at `0`. -/
theorem walk_zero (ω : Ω) : walk X 0 ω = 0 := by simp [walk]

omit m0 in
/-- Each step adds `X n`. -/
theorem walk_succ (n : ℕ) (ω : Ω) : walk X (n + 1) ω = walk X n ω + X n ω := by
  simp [walk, sum_range_succ]

omit m0 in
/-- The walk takes whole-number values. -/
theorem exists_int_walk (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) (n : ℕ) (ω : Ω) :
    ∃ z : ℤ, walk X n ω = z := by
  induction n with
  | zero => exact ⟨0, by simp [walk_zero]⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    rcases hpm n ω with h | h
    · exact ⟨z + 1, by rw [walk_succ, hz, h]; push_cast; ring⟩
    · exact ⟨z - 1, by rw [walk_succ, hz, h]; push_cast; ring⟩

omit m0 in
/-- After `n` steps of `±1` the walk is within `n` of `0`. -/
theorem abs_walk_le (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) (n : ℕ) (ω : Ω) :
    |walk X n ω| ≤ n := by
  induction n with
  | zero => simp [walk_zero]
  | succ n ih =>
    rw [walk_succ]
    have : |X n ω| = 1 := by rcases hpm n ω with h | h <;> simp [h]
    calc |walk X n ω + X n ω| ≤ |walk X n ω| + |X n ω| := abs_add_le _ _
      _ ≤ n + 1 := by linarith
      _ = ((n + 1 : ℕ) : ℝ) := by push_cast; ring

omit m0 in
/-- Up to the exit time the walk stays in `[-b, a]`. -/
theorem walk_mem_Icc_of_le_exitTime (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) (a b : ℕ) {ω : Ω}
    {k : ℕ} (hk : (k : WithTop ℕ) ≤ exitTime X a b ω) :
    walk X k ω ∈ Set.Icc (-(b : ℝ)) a := by
  induction k with
  | zero => rw [walk_zero]; exact ⟨by simp, by simp⟩
  | succ k ih =>
    have hlt : (k : WithTop ℕ) < exitTime X a b ω :=
      lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self k)) hk
    have hnot : walk X k ω ∉ {x : ℝ | x ≤ -(b : ℝ) ∨ (a : ℝ) ≤ x} :=
      notMem_of_lt_hittingAfter hlt (Nat.zero_le k)
    simp only [Set.mem_ofPred_eq, not_or, not_le] at hnot
    obtain ⟨z, hz⟩ := exists_int_walk hpm k ω
    rw [hz] at hnot
    have h1 : -(b : ℤ) < z := by exact_mod_cast hnot.1
    have h2 : z < (a : ℤ) := by exact_mod_cast hnot.2
    have e1 : ((-(b : ℤ) : ℤ) : ℝ) ≤ ((z - 1 : ℤ) : ℝ) := Int.cast_le.mpr (by omega)
    have e2 : ((z + 1 : ℤ) : ℝ) ≤ ((a : ℤ) : ℝ) := Int.cast_le.mpr (by omega)
    push_cast at e1 e2
    rw [walk_succ, hz]
    rcases hpm k ω with h | h <;> rw [h] <;> constructor <;> linarith

end Path

section Mean

variable [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
private theorem stronglyMeasurable_walk (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n)) (n : ℕ) :
    StronglyMeasurable[𝒢 n] (walk X n) :=
  Finset.stronglyMeasurable_fun_sum _ fun i hi ↦
    (hX i).mono (𝒢.mono (Nat.succ_le_of_lt (mem_range.mp hi)))

private theorem integrable_step (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) (n : ℕ) : Integrable (X n) μ :=
  Integrable.of_bound ((hX n).mono (𝒢.le _)).aestronglyMeasurable 1
    (ae_of_all _ fun ω ↦ by rcases hpm n ω with h | h <;> simp [h])

private theorem integrable_walk_mul (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) (n : ℕ) (c : ℝ) {g : Ω → ℝ}
    (hg : StronglyMeasurable g) (hgb : ∀ ω, |g ω| ≤ 1) :
    Integrable (fun ω ↦ c * walk X n ω * g ω) μ :=
  Integrable.of_bound
    ((((stronglyMeasurable_walk hX n).mono (𝒢.le n)).const_mul c).mul hg).aestronglyMeasurable
    (|c| * n) (ae_of_all _ fun ω ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |c| * |walk X n ω| * |g ω| ≤ |c| * n * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left (abs_walk_le hpm n ω) (abs_nonneg c)) (hgb ω)
              (abs_nonneg _) (by positivity)
        _ = |c| * n := mul_one _)

private theorem integrable_walk (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) (n : ℕ) : Integrable (walk X n) μ :=
  Integrable.of_bound ((stronglyMeasurable_walk hX n).mono (𝒢.le n)).aestronglyMeasurable n
    (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact abs_walk_le hpm n ω)

private theorem integrable_walk_sq (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) (n : ℕ) :
    Integrable (fun ω ↦ walk X n ω ^ 2) μ :=
  Integrable.of_bound (((stronglyMeasurable_walk hX n).mono (𝒢.le n)).pow 2).aestronglyMeasurable
    ((n : ℝ) ^ 2) (ae_of_all _ fun ω ↦ by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_walk_le hpm n ω) 2)

/-- At a stopping time bounded by `N`, the walk has mean `0` (Wald's identity, `m = 0`). -/
theorem integral_stoppedValue_walk (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ)
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) (hmean : ∀ n, ∫ ω, X n ω ∂μ = 0)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime 𝒢 τ) {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    ∫ ω, stoppedValue (walk X) τ ω ∂μ = 0 := by
  have := FairGame.integral_stoppedValue_sum_eq hX (integrable_step hX hpm) hmean hind hτ hbdd
  rw [zero_mul] at this
  exact this

/-- At a stopping time bounded by `N`, the walk's square has mean `E[τ]`. -/
theorem integral_stoppedValue_walk_sq (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ)
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) (hmean : ∀ n, ∫ ω, X n ω ∂μ = 0)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime 𝒢 τ) {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    ∫ ω, stoppedValue (fun n ω ↦ walk X n ω ^ 2) τ ω ∂μ = ∫ ω, ((τ ω).untopA : ℝ) ∂μ := by
  have hadp : StronglyAdapted 𝒢 fun n ω ↦ walk X n ω ^ 2 := fun n ↦
    (stronglyMeasurable_walk hX n).pow 2
  have hint := integrable_walk_sq (μ := μ) hX hpm
  have hstep : ∀ n, μ[(fun ω ↦ walk X (n + 1) ω ^ 2) - (fun ω ↦ walk X n ω ^ 2) | 𝒢 n] =ᵐ[μ]
      fun _ ↦ (1 : ℝ) := fun n ↦ by
    have e : (fun ω ↦ walk X (n + 1) ω ^ 2) - (fun ω ↦ walk X n ω ^ 2) =
        (fun ω ↦ 2 * walk X n ω) * X n + fun _ ↦ 1 := by
      funext ω
      simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, walk_succ]
      rcases hpm n ω with h | h <;> rw [h] <;> ring
    rw [e]
    have hXm : Measurable (X n) := (hX n).measurable.mono (𝒢.le (n + 1)) le_rfl
    have hce := condExp_indep_eq hXm.comap_le (𝒢.le n)
      (comap_measurable (X n)).stronglyMeasurable (hind n)
    rw [hmean n] at hce
    have hi1 : Integrable ((fun ω ↦ 2 * walk X n ω) * X n) μ := by
      have := integrable_walk_mul (μ := μ) hX hpm n 2 ((hX n).mono (𝒢.le _))
        fun ω ↦ by rcases hpm n ω with h | h <;> simp [h]
      exact this
    have hmul := condExp_mul_of_stronglyMeasurable_left (m := 𝒢 n)
      ((stronglyMeasurable_walk hX n).const_mul 2) hi1 (integrable_step hX hpm n)
    filter_upwards [condExp_add hi1 (integrable_const (1 : ℝ)) (𝒢 n), hmul, hce] with ω h1 h2 h3
    rw [h1, Pi.add_apply, h2, Pi.mul_apply, h3, condExp_const (𝒢.le n)]
    simp
  have := FairGame.integral_stoppedValue_eq_mul hadp hint (fun ω ↦ by simp [walk_zero]) hstep hτ
    hbdd
  rw [one_mul] at this
  exact this

end Mean

section Ruin

omit m0 in
private theorem min_coe_coe (n N : ℕ) :
    min (WithTop.some n) (WithTop.some N) = WithTop.some (min n N) := by
  rcases le_total n N with h | h
  · rw [min_eq_left (WithTop.coe_le_coe.mpr h), min_eq_left h]
  · rw [min_eq_right (WithTop.coe_le_coe.mpr h), min_eq_right h]

omit m0 in
private theorem untopA_min_top (N : ℕ) : (min (⊤ : WithTop ℕ) (WithTop.some N)).untopA = N := by
  rw [min_eq_right le_top]; rfl

omit m0 in
private theorem untopA_min_coe (n N : ℕ) :
    (min (WithTop.some n) (WithTop.some N)).untopA = min n N := by
  rw [min_coe_coe]; rfl

omit m0 in
private theorem coe_untopA_min (t : WithTop ℕ) (N : ℕ) :
    (WithTop.some (min t (WithTop.some N)).untopA) = min t (WithTop.some N) := by
  cases t with
  | top => rw [untopA_min_top, min_eq_right le_top]
  | coe n => rw [untopA_min_coe, min_coe_coe]

omit m0 in
private theorem untopA_min_le (t : WithTop ℕ) (N : ℕ) : (min t (WithTop.some N)).untopA ≤ N := by
  cases t with
  | top => rw [untopA_min_top]
  | coe n => rw [untopA_min_coe]; exact min_le_right _ _

variable [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
/-- The exit time is a stopping time. -/
theorem isStoppingTime_exitTime (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n)) (a b : ℕ) :
    IsStoppingTime 𝒢 (exitTime X a b) :=
  Adapted.isStoppingTime_hittingAfter (fun n ↦ (stronglyMeasurable_walk hX n).measurable)
    ((measurableSet_le measurable_id measurable_const).union
      (measurableSet_le measurable_const measurable_id))

omit m0 in
/-- The walk stopped at the exit time, or at `N` if that is earlier, is in `[-b, a]`. -/
theorem stoppedValue_min_mem_Icc (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) (a b N : ℕ) (ω : Ω) :
    stoppedValue (walk X) (fun ω ↦ min (exitTime X a b ω) (WithTop.some N)) ω ∈
      Set.Icc (-(b : ℝ)) a :=
  walk_mem_Icc_of_le_exitTime hpm a b (by
    change (WithTop.some (min (exitTime X a b ω) (WithTop.some N)).untopA) ≤ _
    rw [coe_untopA_min]; exact min_le_left _ _)

omit m0 in
private theorem abs_stoppedValue_min_le (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) (a b N : ℕ)
    (ω : Ω) :
    |stoppedValue (walk X) (fun ω ↦ min (exitTime X a b ω) (WithTop.some N)) ω| ≤ a + b := by
  have h := stoppedValue_min_mem_Icc hpm a b N ω
  rw [abs_le]
  constructor <;> linarith [h.1, h.2, (Nat.cast_nonneg a : (0 : ℝ) ≤ a),
    (Nat.cast_nonneg b : (0 : ℝ) ≤ b)]

omit [IsProbabilityMeasure μ] in
private theorem measurable_untopA_min {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime 𝒢 τ) (N : ℕ) :
    Measurable fun ω ↦ ((min (τ ω) (WithTop.some N)).untopA : ℝ) :=
  (measurable_of_countable fun t : WithTop ℕ ↦ ((min t (WithTop.some N)).untopA : ℝ)).comp
    hτ.measurable'

private theorem integrable_untopA_min {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime 𝒢 τ) (N : ℕ) :
    Integrable (fun ω ↦ ((min (τ ω) (WithTop.some N)).untopA : ℝ)) μ :=
  Integrable.of_bound (measurable_untopA_min hτ N).aestronglyMeasurable N
    (ae_of_all _ fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), Nat.cast_le]
      exact untopA_min_le _ _)

/-- The mean of the exit time capped at `N` is at most `(a + b)²`. -/
private theorem integral_untopA_min_le (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ)
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) (hmean : ∀ n, ∫ ω, X n ω ∂μ = 0) (a b N : ℕ) :
    ∫ ω, ((min (exitTime X a b ω) (WithTop.some N)).untopA : ℝ) ∂μ ≤ ((a : ℝ) + b) ^ 2 := by
  have hτ := (isStoppingTime_exitTime hX a b).min_const N
  have h := integral_stoppedValue_walk_sq hX hind hpm hmean hτ fun ω ↦ min_le_right _ _
  rw [← h]
  calc ∫ ω, stoppedValue (fun n ω ↦ walk X n ω ^ 2)
        (fun ω ↦ min (exitTime X a b ω) (WithTop.some N)) ω ∂μ
      ≤ ∫ _ω, ((a : ℝ) + b) ^ 2 ∂μ := by
        refine integral_mono (integrable_stoppedValue ℕ hτ (integrable_walk_sq hX hpm)
          fun ω ↦ min_le_right _ _) (integrable_const _) fun ω ↦ ?_
        have e : stoppedValue (fun n ω ↦ walk X n ω ^ 2)
            (fun ω ↦ min (exitTime X a b ω) (WithTop.some N)) ω =
            stoppedValue (walk X) (fun ω ↦ min (exitTime X a b ω) (WithTop.some N)) ω ^ 2 := rfl
        rw [e, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_stoppedValue_min_le hpm a b N ω) 2
    _ = ((a : ℝ) + b) ^ 2 := by simp

/-- The walk leaves `(-b, a)` with chance `1`. -/
theorem ae_exitTime_ne_top (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ)
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) (hmean : ∀ n, ∫ ω, X n ω ∂μ = 0) (a b : ℕ) :
    ∀ᵐ ω ∂μ, exitTime X a b ω ≠ ⊤ := by
  have hτ := isStoppingTime_exitTime hX a b
  have hbound : ∀ N : ℕ, 0 < N → μ.real {ω | exitTime X a b ω = ⊤} ≤ ((a : ℝ) + b) ^ 2 / N := by
    intro N hN
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hint := integrable_untopA_min (μ := μ) hτ N
    have hmk := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω ↦ Nat.cast_nonneg _) hint N
    have hsub : {ω | exitTime X a b ω = ⊤} ⊆
        {ω | (N : ℝ) ≤ ((min (exitTime X a b ω) (WithTop.some N)).untopA : ℝ)} := fun ω hω ↦ by
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rw [hω, untopA_min_top]
    rw [le_div_iff₀ hNpos, mul_comm]
    exact (mul_le_mul_of_nonneg_left (measureReal_mono hsub) hNpos.le).trans
      (hmk.trans (integral_untopA_min_le hX hind hpm hmean a b N))
  have h0 : μ.real {ω | exitTime X a b ω = ⊤} ≤ 0 := by
    refine ge_of_tendsto (tendsto_const_div_atTop_nhds_zero_nat (((a : ℝ) + b) ^ 2)) ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact hbound N hN
  have hzero : μ {ω | exitTime X a b ω = ⊤} = 0 :=
    (measureReal_eq_zero_iff).mp (le_antisymm h0 measureReal_nonneg)
  rw [ae_iff]
  simpa only [ne_eq, not_not] using hzero

open scoped Classical in
omit m0 in
/-- At the exit time (when finite) the walk is at `a` if it reached `a` before `-b`, else at
`-b`. -/
private theorem stoppedValue_exitTime_eq (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) (a b : ℕ)
    {ω : Ω} (hω : exitTime X a b ω ≠ ⊤) :
    stoppedValue (walk X) (exitTime X a b) ω =
      if ω ∈ {ω | ∃ n, walk X n ω = a ∧ ∀ k ≤ n, -(b : ℝ) < walk X k ω} then (a : ℝ)
      else -(b : ℝ) := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
  have hV : stoppedValue (walk X) (exitTime X a b) ω = walk X n ω := by
    simp only [stoppedValue, ← hn]; rfl
  have hmem : walk X n ω ∈ {x : ℝ | x ≤ -(b : ℝ) ∨ (a : ℝ) ≤ x} := by
    have := hittingAfter_mem_set_of_ne_top hω
    change walk X (exitTime X a b ω).untopA ω ∈ _ at this
    rw [← hn] at this
    exact this
  have hIcc := walk_mem_Icc_of_le_exitTime hpm a b (le_of_eq hn)
  have h2 : walk X n ω = -(b : ℝ) ∨ walk X n ω = a := by
    rcases hmem with h | h
    · exact Or.inl (le_antisymm h hIcc.1)
    · exact Or.inr (le_antisymm hIcc.2 h)
  rw [hV]
  split_ifs with hA
  · obtain ⟨m, hm, hlt⟩ := hA
    have hle : exitTime X a b ω ≤ m := hittingAfter_le_of_mem (Nat.zero_le m) (Or.inr hm.symm.le)
    have hnm : n ≤ m := WithTop.coe_le_coe.mp (hn ▸ hle)
    have := hlt n hnm
    rcases h2 with h | h
    · linarith
    · exact h
  · rcases h2 with h | h
    · exact h
    · by_cases hab : (a : ℝ) = -(b : ℝ)
      · rw [h, hab]
      · exfalso
        refine hA ⟨n, h, fun k hk ↦ ?_⟩
        rcases lt_or_eq_of_le hk with hk | rfl
        · have hnot : walk X k ω ∉ {x : ℝ | x ≤ -(b : ℝ) ∨ (a : ℝ) ≤ x} :=
            notMem_of_lt_hittingAfter (lt_of_lt_of_eq (WithTop.coe_lt_coe.mpr hk) hn)
              (Nat.zero_le k)
          simp only [Set.mem_ofPred_eq, not_or, not_le] at hnot
          exact hnot.1
        · rw [h]
          have : -(b : ℝ) ≤ a := by
            linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a), (Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
          exact lt_of_le_of_ne this (Ne.symm hab)

omit [IsProbabilityMeasure μ] in
private theorem measurableSet_hit (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n)) (a b : ℕ) :
    MeasurableSet {ω | ∃ n, walk X n ω = a ∧ ∀ k ≤ n, -(b : ℝ) < walk X k ω} := by
  have hm : ∀ n, Measurable (walk X n) := fun n ↦
    ((stronglyMeasurable_walk hX n).mono (𝒢.le n)).measurable
  have e : {ω | ∃ n, walk X n ω = a ∧ ∀ k ≤ n, -(b : ℝ) < walk X k ω} =
      ⋃ n, ({ω | walk X n ω = a} ∩ ⋂ k ∈ Set.Iic n, {ω | -(b : ℝ) < walk X k ω}) := by
    ext ω; simp
  rw [e]
  exact MeasurableSet.iUnion fun n ↦ (measurableSet_eq_fun (hm n) measurable_const).inter
    (MeasurableSet.biInter (Set.to_countable _) fun k _ ↦ measurableSet_lt measurable_const (hm k))

omit m0 in
private theorem tendsto_stoppedValue_min {τ : Ω → WithTop ℕ} {ω : Ω} (hω : τ ω ≠ ⊤)
    (f : ℕ → Ω → ℝ) :
    Tendsto (fun N : ℕ ↦ stoppedValue f (fun ω ↦ min (τ ω) (WithTop.some N)) ω) atTop
      (𝓝 (stoppedValue f τ ω)) := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
  refine tendsto_atTop_of_eventually_const (i₀ := n) fun N hN ↦ ?_
  simp only [stoppedValue, ← hn, min_coe_coe, min_eq_left hN]

open scoped Classical in
private theorem integral_ite {A : Set Ω} (hA : MeasurableSet A) (c d : ℝ) :
    ∫ ω, (if ω ∈ A then c else d) ∂μ = d + (c - d) * μ.real A := by
  have e : (fun ω ↦ if ω ∈ A then c else d) =
      fun ω ↦ d + (c - d) * A.indicator (fun _ ↦ (1 : ℝ)) ω := by
    funext ω; by_cases h : ω ∈ A <;> simp [h]
  rw [e, integral_add (integrable_const d) (((integrable_const (1 : ℝ)).indicator hA).const_mul _),
    integral_const_mul, integral_indicator_const _ hA]
  simp

/-- The two limits behind the main theorems: `E[V] = 0` and `E[τ] = E[V²]`, where `V` is the
walk at the exit time `τ`. -/
private theorem integral_stoppedValue_exitTime
    (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ)
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) (hmean : ∀ n, ∫ ω, X n ω ∂μ = 0) (a b : ℕ) :
    ∫ ω, stoppedValue (walk X) (exitTime X a b) ω ∂μ = 0 ∧
      Integrable (fun ω ↦ ((exitTime X a b ω).untopA : ℝ)) μ ∧
      ∫ ω, ((exitTime X a b ω).untopA : ℝ) ∂μ =
        ∫ ω, stoppedValue (walk X) (exitTime X a b) ω ^ 2 ∂μ := by
  set τ := exitTime X a b
  have hτ := isStoppingTime_exitTime hX a b
  have hae := ae_exitTime_ne_top hX hind hpm hmean a b
  have hτN : ∀ N : ℕ, IsStoppingTime 𝒢 fun ω ↦ min (τ ω) (WithTop.some N) := hτ.min_const
  -- the walk
  have hlim1 := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun N ω ↦ stoppedValue (walk X) (fun ω ↦ min (τ ω) (WithTop.some N)) ω)
    (fun _ ↦ (a : ℝ) + b)
    (fun N ↦ (integrable_stoppedValue ℕ (hτN N) (integrable_walk hX hpm)
      fun ω ↦ min_le_right _ _).aestronglyMeasurable) (integrable_const _)
    (fun N ↦ ae_of_all _ fun ω ↦ by
      rw [Real.norm_eq_abs]; exact abs_stoppedValue_min_le hpm a b N ω)
    (by filter_upwards [hae] with ω hω using tendsto_stoppedValue_min hω (walk X))
  have h0 : ∀ N : ℕ, ∫ ω, stoppedValue (walk X) (fun ω ↦ min (τ ω) (WithTop.some N)) ω ∂μ = 0 :=
    fun N ↦ integral_stoppedValue_walk hX hind hpm hmean (hτN N) fun ω ↦ min_le_right _ _
  simp only [h0] at hlim1
  refine ⟨(tendsto_nhds_unique tendsto_const_nhds hlim1).symm, ?_⟩
  -- the square of the walk
  have hlim2 := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun N ω ↦ stoppedValue (fun n ω ↦ walk X n ω ^ 2)
      (fun ω ↦ min (τ ω) (WithTop.some N)) ω)
    (fun _ ↦ ((a : ℝ) + b) ^ 2)
    (fun N ↦ (integrable_stoppedValue ℕ (hτN N) (integrable_walk_sq hX hpm)
      fun ω ↦ min_le_right _ _).aestronglyMeasurable) (integrable_const _)
    (fun N ↦ ae_of_all _ fun ω ↦ by
      have e : stoppedValue (fun n ω ↦ walk X n ω ^ 2)
          (fun ω ↦ min (τ ω) (WithTop.some N)) ω =
          stoppedValue (walk X) (fun ω ↦ min (τ ω) (WithTop.some N)) ω ^ 2 := rfl
      rw [e, Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_stoppedValue_min_le hpm a b N ω) 2)
    (by filter_upwards [hae] with ω hω using tendsto_stoppedValue_min hω _)
  have h2 : ∀ N : ℕ, ∫ ω, stoppedValue (fun n ω ↦ walk X n ω ^ 2)
      (fun ω ↦ min (τ ω) (WithTop.some N)) ω ∂μ =
      ∫ ω, ((min (τ ω) (WithTop.some N)).untopA : ℝ) ∂μ :=
    fun N ↦ integral_stoppedValue_walk_sq hX hind hpm hmean (hτN N) fun ω ↦ min_le_right _ _
  have hlim3 : Tendsto (fun N : ℕ ↦ ∫ ω, ((min (τ ω) (WithTop.some N)).untopA : ℝ) ∂μ) atTop
      (𝓝 (∫ ω, stoppedValue (walk X) τ ω ^ 2 ∂μ)) := hlim2.congr h2
  -- monotone convergence for the capped exit times
  have hfi := integrable_untopA_min (μ := μ) hτ
  have hmct := lintegral_tendsto_of_tendsto_of_monotone (μ := μ)
    (f := fun N ω ↦ ENNReal.ofReal ((min (τ ω) (WithTop.some N)).untopA : ℝ))
    (F := fun ω ↦ ENNReal.ofReal ((τ ω).untopA : ℝ))
    (fun N ↦ ENNReal.measurable_ofReal.comp_aemeasurable
      (measurable_untopA_min hτ N).aemeasurable)
    (ae_of_all _ fun ω ↦ by
      intro N M hNM
      refine ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr ?_)
      cases τ ω with
      | top => rw [untopA_min_top, untopA_min_top]; exact hNM
      | coe n => rw [untopA_min_coe, untopA_min_coe]; exact min_le_min_left n hNM)
    (by
      filter_upwards [hae] with ω hω
      exact (ENNReal.continuous_ofReal.tendsto _).comp
        (tendsto_stoppedValue_min hω fun n _ ↦ (n : ℝ)))
  have hmct' : Tendsto (fun N : ℕ ↦ ENNReal.ofReal
      (∫ ω, ((min (τ ω) (WithTop.some N)).untopA : ℝ) ∂μ)) atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal ((τ ω).untopA : ℝ) ∂μ)) := by
    refine hmct.congr fun N ↦ ?_
    exact (ofReal_integral_eq_lintegral_ofReal (hfi N)
      (ae_of_all _ fun ω ↦ Nat.cast_nonneg _)).symm
  have hlin := tendsto_nhds_unique hmct' (ENNReal.tendsto_ofReal hlim3)
  have hmeas : AEStronglyMeasurable (fun ω ↦ ((τ ω).untopA : ℝ)) μ :=
    ((measurable_of_countable fun t : WithTop ℕ ↦ (t.untopA : ℝ)).comp
      hτ.measurable').aestronglyMeasurable
  refine ⟨⟨hmeas, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω ↦ Nat.cast_nonneg _), hlin]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω ↦ Nat.cast_nonneg _) hmeas, hlin,
      ENNReal.toReal_ofReal (integral_nonneg fun ω ↦ sq_nonneg _)]

/-- **Gambler's ruin, without division.** For the fair `±1` walk from `0`, with `P` the chance of
reaching `a` before `-b`, `(a + b) P = b`. -/
theorem add_mul_measureReal_hit_eq (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ)
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) (hmean : ∀ n, ∫ ω, X n ω ∂μ = 0) (a b : ℕ) :
    ((a : ℝ) + b) * μ.real {ω | ∃ n, walk X n ω = a ∧ ∀ k ≤ n, -(b : ℝ) < walk X k ω} = b := by
  classical
  have hA := measurableSet_hit hX a b
  have hV := (integral_stoppedValue_exitTime hX hind hpm hmean a b).1
  rw [integral_congr_ae ((ae_exitTime_ne_top hX hind hpm hmean a b).mono
    fun ω hω ↦ stoppedValue_exitTime_eq hpm a b hω), integral_ite hA] at hV
  linarith

/-- **Gambler's ruin, the chance.** For the fair `±1` walk from `0`, the chance of reaching `a`
before `-b` is `b / (a + b)` (at `a = b = 0` both sides are `0`, the right one as Lean's
`0 / 0`). -/
theorem measureReal_hit_eq (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ)
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) (hmean : ∀ n, ∫ ω, X n ω ∂μ = 0) (a b : ℕ) :
    μ.real {ω | ∃ n, walk X n ω = a ∧ ∀ k ≤ n, -(b : ℝ) < walk X k ω} = b / (a + b) := by
  set A := {ω | ∃ n, walk X n ω = a ∧ ∀ k ≤ n, -(b : ℝ) < walk X k ω}
  have hV := add_mul_measureReal_hit_eq hX hind hpm hmean a b
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  rcases eq_or_lt_of_le (add_nonneg ha hb) with hab | hab
  · have hb0 : (b : ℝ) = 0 := by linarith
    have hempty : A = ∅ := by
      ext ω
      simp only [A, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro n _ h
      have := h 0 (Nat.zero_le n)
      rw [walk_zero, hb0] at this
      simp at this
    rw [hempty, measureReal_empty, ← hab, div_zero]
  · rw [eq_div_iff hab.ne', mul_comm]
    exact hV

/-- The exit time has a finite mean (so `integral_exitTime_eq` is about a true mean, not Lean's
`0` for a function that is not integrable). -/
theorem integrable_exitTime (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ)
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) (hmean : ∀ n, ∫ ω, X n ω ∂μ = 0) (a b : ℕ) :
    Integrable (fun ω ↦ ((exitTime X a b ω).untopA : ℝ)) μ :=
  (integral_stoppedValue_exitTime hX hind hpm hmean a b).2.1

/-- **Gambler's ruin, the duration.** For the fair `±1` walk from `0`, the mean time to reach `a`
or `-b` is `a b`. -/
theorem integral_exitTime_eq (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ)
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) (hmean : ∀ n, ∫ ω, X n ω ∂μ = 0) (a b : ℕ) :
    ∫ ω, ((exitTime X a b ω).untopA : ℝ) ∂μ = a * b := by
  classical
  set A := {ω | ∃ n, walk X n ω = a ∧ ∀ k ≤ n, -(b : ℝ) < walk X k ω}
  have hA := measurableSet_hit hX a b
  have hP := measureReal_hit_eq hX hind hpm hmean a b
  rw [(integral_stoppedValue_exitTime hX hind hpm hmean a b).2.2]
  have hsq : (fun ω ↦ stoppedValue (walk X) (exitTime X a b) ω ^ 2) =ᵐ[μ]
      fun ω ↦ if ω ∈ A then (a : ℝ) ^ 2 else (b : ℝ) ^ 2 := by
    filter_upwards [ae_exitTime_ne_top hX hind hpm hmean a b] with ω hω
    rw [stoppedValue_exitTime_eq hpm a b hω]
    split_ifs <;> ring
  rw [integral_congr_ae hsq, integral_ite hA, hP]
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  rcases eq_or_lt_of_le (add_nonneg ha hb) with hab | hab
  · have ha0 : (a : ℝ) = 0 := by linarith
    have hb0 : (b : ℝ) = 0 := by linarith
    rw [ha0, hb0]; ring
  · field_simp
    ring

end Ruin

/-! ### The biased walk (order LEAN-28, item 84) -/

section Biased

variable [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}

omit m0 in
/-- A function of a `±1` step, written with the indicator of the step being `1`. -/
private theorem comp_step_eq (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) (n : ℕ) (f : ℝ → ℝ) :
    (fun ω ↦ f (X n ω)) =
      fun ω ↦ f (-1) + (f 1 - f (-1)) * {ω | X n ω = 1}.indicator (fun _ ↦ (1 : ℝ)) ω := by
  funext ω
  rcases hpm n ω with h | h
  · rw [Set.indicator_of_mem (show ω ∈ {ω | X n ω = 1} from h), h]
    ring
  · have hne : ω ∉ {ω | X n ω = 1} := fun hm ↦ by
      have h1 : X n ω = 1 := hm
      rw [h] at h1
      norm_num at h1
    rw [Set.indicator_of_notMem hne, h]
    ring

omit [IsProbabilityMeasure μ] in
private theorem measurableSet_step_eq_one (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (n : ℕ) : MeasurableSet {ω | X n ω = 1} :=
  measurableSet_eq_fun ((hX n).measurable.mono (𝒢.le (n + 1)) le_rfl) measurable_const

/-- Any function of a `±1` step is integrable. -/
private theorem integrable_comp_step (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) (n : ℕ) (f : ℝ → ℝ) :
    Integrable (fun ω ↦ f (X n ω)) μ := by
  rw [comp_step_eq hpm n f]
  exact (integrable_const _).add
    (((integrable_const (1 : ℝ)).indicator (measurableSet_step_eq_one hX n)).const_mul _)

/-- The mean of a function of a step that is `1` with chance `p` and `-1` otherwise. -/
private theorem integral_comp_step (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) {p : ℝ} (hp : ∀ n, μ.real {ω | X n ω = 1} = p)
    (n : ℕ) (f : ℝ → ℝ) :
    ∫ ω, f (X n ω) ∂μ = f (-1) + (f 1 - f (-1)) * p := by
  have hA := measurableSet_step_eq_one hX n
  rw [comp_step_eq hpm n f, integral_add (integrable_const _)
    (((integrable_const (1 : ℝ)).indicator hA).const_mul _), integral_const_mul,
    integral_indicator_const _ hA, hp n]
  simp

omit m0 in
/-- For `r > 0` and `|x| ≤ c`, `r ^ x ≤ r ^ c + r ^ (-c)`. -/
private theorem rpow_le_add_of_abs_le {r x c : ℝ} (hr : 0 < r) (hx : |x| ≤ c) :
    r ^ x ≤ r ^ c + r ^ (-c) := by
  have h1 := Real.rpow_pos_of_pos hr c
  have h2 := Real.rpow_pos_of_pos hr (-c)
  rcases le_total 1 r with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h (le_of_abs_le hx)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hr h (neg_le_of_abs_le hx)
    linarith

/-- From a bound on the mean of the capped exit times, the walk leaves `(-b, a)` with chance `1`
(Markov's inequality, as in `ae_exitTime_ne_top`). -/
private theorem ae_exitTime_ne_top_of_le (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (a b : ℕ) {C : ℝ}
    (hC : ∀ N : ℕ, ∫ ω, ((min (exitTime X a b ω) (WithTop.some N)).untopA : ℝ) ∂μ ≤ C) :
    ∀ᵐ ω ∂μ, exitTime X a b ω ≠ ⊤ := by
  have hτ := isStoppingTime_exitTime hX a b
  have hbound : ∀ N : ℕ, 0 < N → μ.real {ω | exitTime X a b ω = ⊤} ≤ C / N := by
    intro N hN
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hint := integrable_untopA_min (μ := μ) hτ N
    have hmk := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω ↦ Nat.cast_nonneg _) hint N
    have hsub : {ω | exitTime X a b ω = ⊤} ⊆
        {ω | (N : ℝ) ≤ ((min (exitTime X a b ω) (WithTop.some N)).untopA : ℝ)} := fun ω hω ↦ by
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rw [hω, untopA_min_top]
    rw [le_div_iff₀ hNpos, mul_comm]
    exact (mul_le_mul_of_nonneg_left (measureReal_mono hsub) hNpos.le).trans (hmk.trans (hC N))
  have h0 : μ.real {ω | exitTime X a b ω = ⊤} ≤ 0 := by
    refine ge_of_tendsto (tendsto_const_div_atTop_nhds_zero_nat C) ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact hbound N hN
  have hzero : μ {ω | exitTime X a b ω = ⊤} = 0 :=
    (measureReal_eq_zero_iff).mp (le_antisymm h0 measureReal_nonneg)
  rw [ae_iff]
  simpa only [ne_eq, not_not] using hzero

/-- **The `±1` walk with independent steps of one law leaves `(-b, a)` with chance `1`** (order
LEAN-28, item 84): each step is `1` with chance `p` and `-1` otherwise, for any `p` (wider than the
plan's `0 < p < 1`, `p ≠ 1/2`). For `p = 1/2` this is `ae_exitTime_ne_top`; otherwise Wald's
identity gives `(2 p - 1) E[τ ∧ N] = E[S (τ ∧ N)]`, at most `a + b` in size, so the capped exit
times have mean at most `(a + b) / |2 p - 1|`. -/
theorem ae_exitTime_ne_top_of_biased (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ)
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) {p : ℝ} (hp : ∀ n, μ.real {ω | X n ω = 1} = p)
    (a b : ℕ) : ∀ᵐ ω ∂μ, exitTime X a b ω ≠ ⊤ := by
  have hmean : ∀ n, ∫ ω, X n ω ∂μ = 2 * p - 1 := fun n ↦ by
    have h := integral_comp_step hX hpm hp n id
    simp only [id_eq] at h
    rw [h]
    ring
  by_cases hp2 : 2 * p - 1 = 0
  · exact ae_exitTime_ne_top hX hind hpm (fun n ↦ by rw [hmean n, hp2]) a b
  have hτ := isStoppingTime_exitTime hX a b
  refine ae_exitTime_ne_top_of_le hX a b (C := ((a : ℝ) + b) / |2 * p - 1|) fun N ↦ ?_
  have hτN := hτ.min_const N
  have hW := FairGame.integral_stoppedValue_sum_eq hX (integrable_step hX hpm) hmean hind hτN
    (fun ω ↦ min_le_right _ _)
  have hint :
      Integrable (stoppedValue (walk X) fun ω ↦ min (exitTime X a b ω) (WithTop.some N)) μ :=
    integrable_stoppedValue ℕ hτN (integrable_walk hX hpm) fun ω ↦ min_le_right _ _
  have hbd : |∫ ω, stoppedValue (walk X) (fun ω ↦ min (exitTime X a b ω) (WithTop.some N)) ω ∂μ|
      ≤ a + b :=
    calc _ ≤ ∫ ω, |stoppedValue (walk X) (fun ω ↦ min (exitTime X a b ω) (WithTop.some N)) ω| ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _ω, ((a : ℝ) + b) ∂μ :=
          integral_mono hint.abs (integrable_const _) fun ω ↦ abs_stoppedValue_min_le hpm a b N ω
      _ = a + b := by simp
  have hW' : ∫ ω, stoppedValue (walk X) (fun ω ↦ min (exitTime X a b ω) (WithTop.some N)) ω ∂μ =
      (2 * p - 1) * ∫ ω, ((min (exitTime X a b ω) (WithTop.some N)).untopA : ℝ) ∂μ := hW
  have hE0 : 0 ≤ ∫ ω, ((min (exitTime X a b ω) (WithTop.some N)).untopA : ℝ) ∂μ :=
    integral_nonneg fun ω ↦ Nat.cast_nonneg _
  rw [hW', abs_mul, abs_of_nonneg hE0] at hbd
  rw [le_div_iff₀ (abs_pos.mpr hp2), mul_comm]
  exact hbd

/-- For a step up with chance `p ∈ (0, 1)` and `r = (1 - p) / p`, `r ^ (walk n)` is a martingale:
`E[r ^ X n] = p r + (1 - p) / r = 1`. -/
private theorem martingale_rpow_walk (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ)
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hp : ∀ n, μ.real {ω | X n ω = 1} = p) :
    Martingale (fun n ω ↦ ((1 - p) / p) ^ walk X n ω) 𝒢 μ := by
  set r := (1 - p) / p with hr
  have hr0 : 0 < r := div_pos (by linarith) hp0
  have hmeas : ∀ n, StronglyMeasurable[𝒢 n] (fun ω ↦ r ^ walk X n ω) := fun n ↦
    (measurable_const.pow (stronglyMeasurable_walk hX n).measurable).stronglyMeasurable
  have hint : ∀ n, Integrable (fun ω ↦ r ^ walk X n ω) μ := fun n ↦
    Integrable.of_bound ((hmeas n).mono (𝒢.le n)).aestronglyMeasurable
      (r ^ (n : ℝ) + r ^ (-(n : ℝ)))
      (ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hr0 _)]
        exact rpow_le_add_of_abs_le hr0 (abs_walk_le hpm n ω))
  refine martingale_of_condExp_sub_eq_zero_nat hmeas hint fun n ↦ ?_
  change μ[(fun ω ↦ r ^ walk X (n + 1) ω) - (fun ω ↦ r ^ walk X n ω) | 𝒢 n] =ᵐ[μ] 0
  have e : (fun ω ↦ r ^ walk X (n + 1) ω) - (fun ω ↦ r ^ walk X n ω) =
      (fun ω ↦ r ^ walk X n ω) * fun ω ↦ r ^ X n ω - 1 := by
    funext ω
    simp only [Pi.sub_apply, Pi.mul_apply, walk_succ, Real.rpow_add hr0]
    ring
  rw [e]
  have hXm : Measurable (X n) := (hX n).measurable.mono (𝒢.le (n + 1)) le_rfl
  have hGm : StronglyMeasurable[MeasurableSpace.comap (X n) inferInstance]
      (fun ω ↦ r ^ X n ω - 1) :=
    (((measurable_const.pow measurable_id).sub_const 1).comp
      (comap_measurable (X n))).stronglyMeasurable
  have hce := condExp_indep_eq hXm.comap_le (𝒢.le n) hGm (hind n)
  have hp0' : p ≠ 0 := hp0.ne'
  have hq0 : 1 - p ≠ 0 := (sub_pos.mpr hp1).ne'
  have hG0 : ∫ ω, (r ^ X n ω - 1) ∂μ = 0 := by
    rw [integral_comp_step hX hpm hp n fun x ↦ r ^ x - 1]
    simp only [Real.rpow_one, Real.rpow_neg_one, hr]
    field_simp
    ring
  have hGint : Integrable (fun ω ↦ r ^ X n ω - 1) μ :=
    integrable_comp_step hX hpm n fun x ↦ r ^ x - 1
  have hprod : Integrable ((fun ω ↦ r ^ walk X n ω) * fun ω ↦ r ^ X n ω - 1) μ := by
    rw [← e]
    exact (hint (n + 1)).sub (hint n)
  have hmul := condExp_mul_of_stronglyMeasurable_left (m := 𝒢 n) (hmeas n) hprod hGint
  filter_upwards [hmul, hce] with ω h1 h2
  rw [h1, Pi.mul_apply, h2]
  simp only [hG0, mul_zero, Pi.zero_apply]

/-- **The biased walk reaches `a` first with chance `(r ^ b - 1) / (r ^ (a + b) - 1)`** (order
LEAN-28, item 84), `r = (1 - p) / p`, for a step up with chance `p`, `0 < p < 1`, `p ≠ 1/2`. -/
theorem measureReal_hit_eq_of_biased (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ)
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hp2 : p ≠ 1 / 2)
    (hp : ∀ n, μ.real {ω | X n ω = 1} = p) (a b : ℕ) :
    μ.real {ω | ∃ n, walk X n ω = a ∧ ∀ k ≤ n, -(b : ℝ) < walk X k ω} =
      (((1 - p) / p) ^ b - 1) / (((1 - p) / p) ^ (a + b) - 1) := by
  classical
  set A := {ω | ∃ n, walk X n ω = a ∧ ∀ k ≤ n, -(b : ℝ) < walk X k ω}
  set r := (1 - p) / p with hr
  have hr0 : 0 < r := div_pos (by linarith) hp0
  have hr1 : r ≠ 1 := by
    intro h
    rw [hr, div_eq_one_iff_eq hp0.ne'] at h
    exact hp2 (by linarith)
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  -- `a = b = 0`: the event is empty and the right side is Lean's `0 / 0`
  rcases Nat.eq_zero_or_pos (a + b) with hab | hab
  · have hb0 : b = 0 := by omega
    have hempty : A = ∅ := by
      ext ω
      simp only [A, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro n _ h
      have := h 0 (Nat.zero_le n)
      rw [walk_zero, hb0] at this
      simp at this
    rw [hempty, measureReal_empty, hab, hb0]
    simp
  set M : ℕ → Ω → ℝ := fun n ω ↦ r ^ walk X n ω
  have hmart : Martingale M 𝒢 μ := martingale_rpow_walk hX hind hpm hp0 hp1 hp
  have hτ := isStoppingTime_exitTime hX a b
  have hτN : ∀ N : ℕ, IsStoppingTime 𝒢 fun ω ↦ min (exitTime X a b ω) (WithTop.some N) :=
    hτ.min_const
  have hae := ae_exitTime_ne_top_of_biased hX hind hpm hp a b
  -- `E[M (τ ∧ N)] = E[M 0] = 1`
  have hE : ∀ N : ℕ,
      ∫ ω, stoppedValue M (fun ω ↦ min (exitTime X a b ω) (WithTop.some N)) ω ∂μ = 1 := fun N ↦ by
    rw [FairGame.integral_stoppedValue_eq hmart (hτN N) fun ω ↦ min_le_right _ _]
    simp [M, walk_zero]
  -- dominated convergence, with the bound `r ^ (a + b) + r ^ (-(a + b))`
  have hlim := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun N ω ↦ stoppedValue M (fun ω ↦ min (exitTime X a b ω) (WithTop.some N)) ω)
    (fun _ ↦ r ^ ((a : ℝ) + b) + r ^ (-((a : ℝ) + b)))
    (fun N ↦ (integrable_stoppedValue ℕ (hτN N) hmart.integrable
      fun ω ↦ min_le_right _ _).aestronglyMeasurable) (integrable_const _)
    (fun N ↦ ae_of_all _ fun ω ↦ by
      have hI := stoppedValue_min_mem_Icc hpm a b N ω
      have e : stoppedValue M (fun ω ↦ min (exitTime X a b ω) (WithTop.some N)) ω =
          r ^ stoppedValue (walk X) (fun ω ↦ min (exitTime X a b ω) (WithTop.some N)) ω := rfl
      rw [e, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hr0 _)]
      refine rpow_le_add_of_abs_le hr0 (abs_le.mpr ⟨?_, ?_⟩) <;> linarith [hI.1, hI.2])
    (by filter_upwards [hae] with ω hω using tendsto_stoppedValue_min hω M)
  simp only [hE] at hlim
  have hEτ : ∫ ω, stoppedValue M (exitTime X a b) ω ∂μ = 1 :=
    (tendsto_nhds_unique tendsto_const_nhds hlim).symm
  -- at the exit time the walk is at `a` on `A` and at `-b` off it
  have hA : MeasurableSet A := measurableSet_hit hX a b
  have hsv : (fun ω ↦ stoppedValue M (exitTime X a b) ω) =ᵐ[μ]
      fun ω ↦ r ^ (if ω ∈ A then (a : ℝ) else -(b : ℝ)) := by
    filter_upwards [hae] with ω hω
    exact congrArg (r ^ ·) (stoppedValue_exitTime_eq hpm a b hω)
  have hite : (fun ω ↦ r ^ (if ω ∈ A then (a : ℝ) else -(b : ℝ))) =
      fun ω ↦ if ω ∈ A then r ^ (a : ℝ) else r ^ (-(b : ℝ)) := by
    funext ω
    split_ifs <;> rfl
  rw [integral_congr_ae hsv, hite, integral_ite hA, Real.rpow_neg hr0.le, Real.rpow_natCast,
    Real.rpow_natCast] at hEτ
  -- `hEτ : (r ^ b)⁻¹ + (r ^ a - (r ^ b)⁻¹) P = 1`
  have hrb : 0 < r ^ b := pow_pos hr0 b
  have hinv : r ^ b * (r ^ b)⁻¹ = 1 := mul_inv_cancel₀ hrb.ne'
  have key : (r ^ (a + b) - 1) * μ.real A = r ^ b - 1 := by
    linear_combination r ^ b * hEτ - (1 - μ.real A) * hinv
  have hne : r ^ (a + b) - 1 ≠ 0 := by
    intro h
    have h1 : r ^ (a + b) = 1 := by linarith
    exact hr1 ((pow_eq_one_iff_of_nonneg hr0.le (by omega)).mp h1)
  rw [eq_div_iff hne, mul_comm (μ.real A)]
  exact key

/-- **Ville's inequality for the biased walk** (order LEAN-28, item 84): when a step goes up with
chance `p < 1 - p` (`p > 0`), the chance that the walk ever reaches `a` is at most
`(p / (1 - p)) ^ a`. The martingale `r ^ (walk n)`, `r = (1 - p) / p > 1`, is nonnegative and
starts at `1`; on reaching `a` it is at least `r ^ a`. Ville's inequality
(`MaximalInequality.measureReal_exists_le_of_supermartingale`) bounds each horizon `N`, and the
events grow with `N`. -/
theorem measureReal_exists_ge_le_of_biased (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ)
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) {p : ℝ} (hp0 : 0 < p) (hpq : p < 1 - p)
    (hp : ∀ n, μ.real {ω | X n ω = 1} = p) (a : ℕ) :
    μ.real {ω | ∃ n, (a : ℝ) ≤ walk X n ω} ≤ (p / (1 - p)) ^ a := by
  set r := (1 - p) / p with hr
  have hr0 : 0 < r := div_pos (by linarith) hp0
  have hr1 : 1 ≤ r := by
    rw [hr, le_div_iff₀ hp0]
    linarith
  have hmart : Martingale (fun n ω ↦ r ^ walk X n ω) 𝒢 μ :=
    martingale_rpow_walk hX hind hpm hp0 (by linarith) hp
  have hc : 0 ≤ (p / (1 - p)) ^ a := pow_nonneg (div_nonneg hp0.le (by linarith)) a
  have hN : ∀ N : ℕ, μ.real {ω | ∃ n ≤ N, (a : ℝ) ≤ walk X n ω} ≤ (p / (1 - p)) ^ a := by
    intro N
    have hville := MaximalInequality.measureReal_exists_le_of_supermartingale
      hmart.supermartingale (fun n ω ↦ (Real.rpow_pos_of_pos hr0 _).le)
      (Real.rpow_pos_of_pos hr0 (a : ℝ)) N
    have hM0 : ∫ ω, (fun n ω ↦ r ^ walk X n ω) 0 ω ∂μ = 1 := by simp [walk_zero]
    rw [hM0] at hville
    calc μ.real {ω | ∃ n ≤ N, (a : ℝ) ≤ walk X n ω}
        ≤ μ.real {ω | ∃ n ≤ N, r ^ (a : ℝ) ≤ (fun n ω ↦ r ^ walk X n ω) n ω} := by
          refine measureReal_mono fun ω ⟨n, hn, h⟩ ↦ ⟨n, hn, ?_⟩
          exact Real.rpow_le_rpow_of_exponent_le hr1 h
      _ ≤ 1 / r ^ (a : ℝ) := hville
      _ = (p / (1 - p)) ^ a := by
          rw [Real.rpow_natCast, one_div, ← inv_pow, hr, inv_div]
  have hU : {ω | ∃ n, (a : ℝ) ≤ walk X n ω} =
      ⋃ N : ℕ, {ω | ∃ n ≤ N, (a : ℝ) ≤ walk X n ω} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, n, le_rfl, hn⟩
    · rintro ⟨N, n, -, hn⟩
      exact ⟨n, hn⟩
  have hmono : Monotone fun N : ℕ ↦ {ω | ∃ n ≤ N, (a : ℝ) ≤ walk X n ω} :=
    fun N N' hNN' ω ⟨n, hn, h⟩ ↦ ⟨n, hn.trans hNN', h⟩
  rw [hU, measureReal_def, hmono.measure_iUnion]
  refine ENNReal.toReal_le_of_le_ofReal hc (iSup_le fun N ↦ ?_)
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact ENNReal.ofReal_le_ofReal (hN N)

/-- **The ruin chance as a ratio of Lucas numbers** (order LEAN-29, item 95 of
MATH-PLAN-library-2). For the `±1` walk with independent steps that are `1` with chance `p`,
`0 < p < 1`, the chance of reaching `a` before `-b` is `U b / U (a + b)`, where `U` is the Lucas
sequence `lucasU (1 + r) r` (`NumberTheory/LucasSequence`), `r = (1 - p) / p`, whose
characteristic roots are `1` and `r`. **Wider than item 84** (`measureReal_hit_eq_of_biased`):
there is no `p ≠ 1/2`. For `p ≠ 1/2` this is item 84's `(r ^ b - 1) / (r ^ (a + b) - 1)` with
both terms divided by `r - 1` (`lucasU_of_roots` at the roots `r` and `1`); at `p = 1/2`, `r = 1`,
`lucasU 2 1 n = n` and the formula is the fair walk's `b / (a + b)` (`measureReal_hit_eq`), so one
formula covers the fair and the biased walk. -/
theorem measureReal_hit_eq_lucasU (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ)
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hp : ∀ n, μ.real {ω | X n ω = 1} = p) (a b : ℕ) :
    μ.real {ω | ∃ n, walk X n ω = a ∧ ∀ k ≤ n, -(b : ℝ) < walk X k ω} =
      lucasU (1 + (1 - p) / p) ((1 - p) / p) b /
        lucasU (1 + (1 - p) / p) ((1 - p) / p) (a + b) := by
  set r := (1 - p) / p with hr
  by_cases hp2 : p = 1 / 2
  · -- the fair walk: `r = 1` and `lucasU 2 1 n = n`
    have hr1 : r = 1 := by rw [hr, hp2]; norm_num
    have hU : ∀ n : ℕ, lucasU (1 + r) r n = n := by
      intro n
      rw [hr1]
      induction n using Nat.twoStepInduction with
      | zero => simp
      | one => simp
      | more n ih1 ih2 => rw [lucasU_add_two, ih1, ih2]; push_cast; ring
    have hmean : ∀ n, ∫ ω, X n ω ∂μ = 0 := fun n ↦ by
      have h := integral_comp_step hX hpm hp n id
      simp only [id_eq] at h
      rw [h, hp2]
      ring
    rw [measureReal_hit_eq hX hind hpm hmean a b, hU, hU]
    push_cast
    ring
  · -- the biased walk: item 84's formula, divided through by `r - 1`
    have hr1 : r - 1 ≠ 0 := by
      intro h
      have h1 : (1 - p) / p = 1 := by rw [← hr]; linarith
      rw [div_eq_one_iff_eq hp0.ne'] at h1
      exact hp2 (by linarith)
    have key : ∀ n : ℕ, (r - 1) * lucasU (1 + r) r n = r ^ n - 1 := fun n ↦ by
      have h := lucasU_of_roots r 1 n
      rwa [mul_one, one_pow, add_comm r 1] at h
    rw [measureReal_hit_eq_of_biased hX hind hpm hp0 hp1 hp2 hp a b, ← key b, ← key (a + b),
      mul_div_mul_left _ _ hr1]

end Biased

/-- The hypotheses of `ae_exitTime_ne_top_of_biased`, `measureReal_hit_eq_of_biased` and
`measureReal_exists_ge_le_of_biased` hold together, at `p = 1/3`: independent steps `B n`, `true`
with chance `1/3` (Mathlib's `ProbabilityTheory.exists_iid`), read as `±1`; the step at time `n` is
the one indexed `n + 1`, and the filtration is the one the steps generate. -/
example : ∃ (Ω : Type) (m0 : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
    (𝒢 : Filtration ℕ m0) (X : ℕ → Ω → ℝ),
    (∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n)) ∧
      (∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ) ∧
      (∀ n ω, X n ω = 1 ∨ X n ω = -1) ∧ (∀ n, μ.real {ω | X n ω = 1} = 1 / 3) ∧
      (0 : ℝ) < 1 / 3 ∧ (1 / 3 : ℝ) < 1 ∧ (1 / 3 : ℝ) ≠ 1 / 2 ∧ (1 / 3 : ℝ) < 1 - 1 / 3 := by
  set ν : Measure Bool := ENNReal.ofReal (1 / 3) • Measure.dirac true +
    ENNReal.ofReal (2 / 3) • Measure.dirac false with hν
  have hν1 : IsProbabilityMeasure ν := ⟨by
    simp only [hν, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num⟩
  obtain ⟨Ω, mΩ, P, B, hBm, hBlaw, hBind, hP⟩ := exists_iid ℕ ν
  set g : Bool → ℝ := fun c ↦ if c then 1 else -1 with hg
  have hgm : Measurable g := measurable_of_countable g
  set f : ℕ → Ω → ℝ := fun i ω ↦ g (B i ω) with hf
  have hfm : ∀ i, StronglyMeasurable (f i) := fun i ↦ (hgm.comp (hBm i)).stronglyMeasurable
  have hfind : iIndepFun f P := hBind.comp (fun _ ↦ g) fun _ ↦ hgm
  refine ⟨Ω, mΩ, P, hP, Filtration.natural f hfm, fun n ↦ f (n + 1), fun n ↦ ?_, fun n ↦ ?_,
    fun n ω ↦ ?_, fun n ↦ ?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact Filtration.stronglyAdapted_natural hfm (n + 1)
  · exact hfind.indep_comap_natural_of_lt hfm (Nat.lt_succ_self n)
  · simp only [f, g]
    split_ifs <;> simp
  · have hset : {ω | f (n + 1) ω = 1} = B (n + 1) ⁻¹' {true} := by
      ext ω
      simp only [f, g, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      cases B (n + 1) ω <;> norm_num
    rw [hset, measureReal_def, ← Measure.map_apply (hBm _) (measurableSet_singleton _),
      (hBlaw (n + 1)).map_eq]
    simp [hν]

open scoped ENNReal in
/-- **Why `ae_exitTime_ne_top_of_biased` needs a probability measure** (cold review r84): one point
of mass `∞`. Lean's `μ.real` of every set is `∞.toReal = 0`, so `hp` holds with `p = 0` for the
steps `+1, -1, +1, …`, which are independent and known in advance (the filtration that knows
nothing), and the walk `0, 1, 0, 1, …` never leaves `(-1, 2)`: the set where it stays has mass `∞`,
not `0`. -/
example : ∃ (μ : Measure Unit) (𝒢 : Filtration ℕ (inferInstance : MeasurableSpace Unit))
    (X : ℕ → Unit → ℝ) (p : ℝ), ¬ IsProbabilityMeasure μ ∧
    (∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n)) ∧
    (∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ) ∧
    (∀ n ω, X n ω = 1 ∨ X n ω = -1) ∧ (∀ n, μ.real {ω | X n ω = 1} = p) ∧
    ¬ (∀ᵐ ω ∂μ, exitTime X 2 1 ω ≠ ⊤) := by
  set μ : Measure Unit := (∞ : ℝ≥0∞) • Measure.dirac () with hμ
  have hμu : μ Set.univ = ∞ := by simp [hμ]
  have hset : ∀ s : Set Unit, s = ∅ ∨ s = Set.univ := fun s ↦ by
    by_cases h : () ∈ s
    · exact Or.inr (Set.eq_univ_of_forall fun x ↦ by cases x; exact h)
    · exact Or.inl (Set.eq_empty_of_forall_notMem fun x ↦ by cases x; exact h)
  set X : ℕ → Unit → ℝ := fun n _ ↦ (-1 : ℝ) ^ n with hX
  have hwalk : ∀ n, walk X n () = if Even n then 0 else 1 := fun n ↦ by
    induction n with
    | zero => simp [walk]
    | succ n ih =>
      have hs : walk X (n + 1) () = walk X n () + (-1 : ℝ) ^ n := by
        simp [walk, sum_range_succ, hX]
      rw [hs, ih]
      rcases Nat.even_or_odd n with h | h
      · simp [h, h.neg_one_pow, Nat.even_add_one]
      · simp [Nat.not_even_iff_odd.mpr h, h.neg_one_pow, Nat.even_add_one]
  have hexit : exitTime X 2 1 () = ⊤ := by
    rw [exitTime, hittingAfter_eq_top_iff]
    intro j _
    simp only [Set.mem_ofPred_eq, hwalk]
    split_ifs <;> norm_num
  refine ⟨μ, ⊥, X, 0, fun h ↦ ?_, fun n ↦ stronglyMeasurable_const, fun n ↦ ?_, fun n ω ↦ ?_,
    fun n ↦ ?_, fun h ↦ ?_⟩
  · have := h.measure_univ
    rw [hμu] at this
    exact ENNReal.top_ne_one this
  · rw [Indep_iff]
    intro t1 t2 _ _
    rcases hset t1 with h1 | h1 <;> rcases hset t2 with h2 | h2 <;> simp [h1, h2, hμu]
  · rcases Nat.even_or_odd n with h | h
    · exact Or.inl h.neg_one_pow
    · exact Or.inr h.neg_one_pow
  · rcases hset {ω | X n ω = 1} with h | h
    · rw [h, measureReal_empty]
    · rw [h, measureReal_def, hμu]
      simp
  · rw [ae_iff] at h
    have hs : {ω | ¬ exitTime X 2 1 ω ≠ ⊤} = Set.univ :=
      Set.eq_univ_of_forall fun ω ↦ by cases ω; exact not_not.mpr hexit
    rw [hs, hμu] at h
    exact ENNReal.top_ne_zero h

end ClassicalLean.Probability.GamblersRuin

open MeasureTheory ProbabilityTheory in
/-- The hypotheses of `measureReal_hit_eq` hold together: on the space of coin sequences `ℕ → Bool`
with independent fair coins (Mathlib's `Measure.infinitePi` of the uniform law on `Bool`), the
steps `X n = ±1` read from coin `n + 1`; the filtration is the one the coins' values generate, so
step `n` is known at time `n + 1` and independent of what time `n` knows; each step is `1` or
`-1`, and of mean `0`; the targets `a = 2` and `b = 1`. -/
example := ClassicalLean.Probability.GamblersRuin.measureReal_hit_eq (Ω := ℕ → Bool)
  (μ := Measure.infinitePi fun _ ↦ uniformOn Set.univ)
  (𝒢 := Filtration.natural (fun i (ω : ℕ → Bool) ↦ if ω i then (1 : ℝ) else -1)
    fun i ↦ ((measurable_of_countable fun c : Bool ↦ if c then (1 : ℝ) else -1).comp
      (measurable_pi_apply i)).stronglyMeasurable)
  (X := fun n ω ↦ if ω (n + 1) then 1 else -1)
  (fun n ↦ Filtration.stronglyAdapted_natural
    (u := fun i (ω : ℕ → Bool) ↦ if ω i then (1 : ℝ) else -1) _ (n + 1))
  (fun n ↦ (iIndepFun_infinitePi (P := fun _ : ℕ ↦ (uniformOn Set.univ : Measure Bool))
    (X := fun _ (c : Bool) ↦ if c then (1 : ℝ) else -1)
    fun _ ↦ measurable_of_countable _).indep_comap_natural_of_lt _ (Nat.lt_succ_self n))
  (fun n ω ↦ by split_ifs <;> simp)
  (fun n ↦ by
    rw [← integral_map (φ := fun ω : ℕ → Bool ↦ ω (n + 1))
      (f := fun c : Bool ↦ if c then (1 : ℝ) else -1) (measurable_pi_apply (n + 1)).aemeasurable
      (measurable_of_countable fun c : Bool ↦ if c then (1 : ℝ) else -1).aestronglyMeasurable,
      Measure.infinitePi_map_eval, integral_fintype Integrable.of_finite]
    simp only [Measure.real, uniformOn_univ]
    simp)
  (a := 2) (b := 1)

open MeasureTheory ProbabilityTheory in
/-- The hypotheses of `measureReal_hit_eq_lucasU` hold together: a biased walk, on the space of
sequences `ℕ → Fin 3` of independent coins with three equally likely faces (Mathlib's
`Measure.infinitePi` of the uniform law on `Fin 3`), the step `X n` is `+1` when coin `n + 1`
shows `0` and `-1` otherwise, so each step is `1` with chance `p = 1/3` (`r = 2`); the filtration
is the one the coins' values generate (read as `±1`), so step `n` is known at time `n + 1` and
independent of what time `n` knows; `0 < 1/3 < 1`; the targets `a = 1` and `b = 2`. -/
example := ClassicalLean.Probability.GamblersRuin.measureReal_hit_eq_lucasU (Ω := ℕ → Fin 3)
  (μ := Measure.infinitePi fun _ ↦ uniformOn Set.univ)
  (𝒢 := Filtration.natural (fun i (ω : ℕ → Fin 3) ↦ if ω i = 0 then (1 : ℝ) else -1)
    fun i ↦ ((measurable_of_countable fun c : Fin 3 ↦ if c = 0 then (1 : ℝ) else -1).comp
      (measurable_pi_apply i)).stronglyMeasurable)
  (X := fun n ω ↦ if ω (n + 1) = 0 then 1 else -1)
  (fun n ↦ Filtration.stronglyAdapted_natural
    (u := fun i (ω : ℕ → Fin 3) ↦ if ω i = 0 then (1 : ℝ) else -1) _ (n + 1))
  (fun n ↦ (iIndepFun_infinitePi (P := fun _ : ℕ ↦ (uniformOn Set.univ : Measure (Fin 3)))
    (X := fun _ (c : Fin 3) ↦ if c = 0 then (1 : ℝ) else -1)
    fun _ ↦ measurable_of_countable _).indep_comap_natural_of_lt _ (Nat.lt_succ_self n))
  (fun n ω ↦ by split_ifs <;> simp) (p := 1 / 3) (by norm_num) (by norm_num)
  (fun n ↦ by
    have hset : {ω : ℕ → Fin 3 | (if ω (n + 1) = 0 then (1 : ℝ) else -1) = 1} =
        (fun ω : ℕ → Fin 3 ↦ ω (n + 1)) ⁻¹' {0} := by
      ext ω
      by_cases h : ω (n + 1) = 0
      · simp [h]
      · norm_num [h]
    rw [hset, measureReal_def, ← Measure.map_apply (measurable_pi_apply (n + 1))
      (measurableSet_singleton 0), Measure.infinitePi_map_eval, uniformOn_univ]
    simp)
  (a := 1) (b := 2)
