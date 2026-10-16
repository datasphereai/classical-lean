/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Statistics.RaoBlackwell
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# Sufficiency, Rao–Blackwell, Fisher–Neyman, Lehmann–Scheffé and Basu

A family `P θ` of distributions on one sample space, and a σ-algebra `m` (for example the one a
statistic `S` generates: what can be known from `S` alone).

* `IsSufficient P m` — **sufficiency**: `m` is a sub-σ-algebra and, for every event, one
  `m`-measurable function is the chance of the event given `m` under every `P θ` at once.
* `IsSufficient.exists_condExp_eq` — then the same holds for every measurable `T` that is
  integrable under every `P θ`: one `m`-measurable `g` is `E[T | m]` under every `P θ`. Finite
  measures suffice.
* `IsSufficient.raoBlackwell` — **the Rao–Blackwell theorem**: for `T` square-integrable under
  every `P θ`, that `g` is one statistic for all `θ`, has `T`'s mean under every `P θ`, and for
  every `θ` and every target `τ` has mean squared error at most `T`'s, with equality only when
  `T = g` almost surely under `P θ`. The inequality is order LEAN-19's conditioning inequality
  (`integral_sq_condExp_sub_le`), used and not proved again.
* `integral_sub_condExp_sq_eq`, `integral_sub_sq_eq_integral_condExp_sub_sq_add` — the identities
  behind the equality case: `E[(T − E[T | m])²] = Var T − Var E[T | m]`, and the mean squared error
  splits along conditioning.
* `IsComplete P m` — **completeness**: an `m`-measurable function, integrable with mean `0` under
  every `P θ`, is `0` almost surely under every `P θ`.
* `variance_le_of_isSufficient_of_isComplete`, `ae_eq_of_variance_eq_of_isSufficient_of_isComplete`
  — **the Lehmann–Scheffé theorem**: with `m` sufficient and complete, an unbiased `m`-measurable
  estimator has the least variance among all unbiased estimators, under every `θ`, and is the only
  one with that variance (almost surely).
* `IsAncillary P A` — **ancillarity**: the law `(P θ).map A` of a statistic `A` is the same for
  every `θ`.
* `indep_of_isSufficient_of_isComplete_of_isAncillary`, `indepFun_of_isComplete_of_ancillary` —
  order LEAN-24, item 58, **Basu's theorem**: a σ-algebra `m` (or a statistic `S`) that is
  sufficient (`IsSufficient`, item 50) and complete (`IsComplete`, item 54) for a family of
  probability measures is independent, under every `P θ`, of every measurable ancillary
  statistic `A`. Ancillary and complete are defined here in the same style: one condition for all
  `θ` at once. Completeness here is for every integrable function with mean `0`; Basu's theorem
  is usually stated with the weaker hypothesis of bounded completeness (review r58, from the
  reviewer's knowledge, not checked against a source), so this form is narrower in that respect;
  `indep_of_isSufficient_of_isBoundedlyComplete_of_isAncillary` (item 102, below) is that form.
* `IsBoundedlyComplete P m`, `IsComplete.isBoundedlyComplete`,
  `indep_of_isSufficient_of_isBoundedlyComplete_of_isAncillary` — order LEAN-31, item 102:
  **bounded completeness** (only the bounded `m`-measurable functions with mean `0` under every
  `P θ` must vanish); completeness gives it, for finite measures and `m ≤ m₀`; and **Basu's theorem
  with bounded completeness**, which is wider than item 58's: item 58's theorem follows from it
  through `IsComplete.isBoundedlyComplete hS.1`.
* `isSufficient_iff_factorization` — **the Fisher–Neyman factorization theorem**, finite form: on a
  finite space where every point has positive chance, `S` is sufficient exactly when
  `P θ {ω} = a θ (S ω) · b ω`. Helpers: `condExp_comap_ae_eq` (conditional expectation given `S`
  on a finite space is a weighted average over the fibre of `S`), `comap_le_of_finite`,
  `stronglyMeasurable_comp_comap`, `eq_of_ae_eq_of_pos`.
* Coin flips, built from Mathlib's `bernoulliMeasure` and `Measure.pi`: `coinFlips n p`,
  `numHeads`, `coinFlips_real_singleton`, `coinFlips_real_singleton_eq_pow`, `numHeads_le`.
  (Mathlib's `binomial` and `setBer` are another model of the same flips; the product of Bernoulli
  laws is used here so that a sequence of flips is a point of the sample space.)
  `isSufficient_numHeads` (the number of heads is sufficient for `p ∈ (0, 1)`);
  `condExp_firstFlip_ae_eq` (given the number of heads `k` in `n + 1` flips, the first flip's
  conditional mean is `k / (n + 1)`, for every `p`: Rao–Blackwell turns the first flip into the
  sample mean); `integral_sampleMean_sub_sq_le` (so its mean squared error is smaller, by order
  LEAN-19's conditioning inequality; `IsSufficient.raoBlackwell` itself is not restated for coin
  flips).
* Item 61, added during order LEAN-20: `isComplete_numHeads` (the number of heads is complete for
  `p ∈ (0, 1)`), so `variance_sampleMean_le` and `eq_sampleMean_of_variance_eq`: the sample mean
  is the one unbiased estimator of `p` with least variance, under every `p`.

Names: the plan's rows name `isSufficient_sum_bernoulli`, `isComplete_sum_bernoulli` and
`sampleMean_isMinVariance`; the statistic here is `numHeads`, so the theorems are
`isSufficient_numHeads` and `isComplete_numHeads`, and the least-variance result is stated as the
two theorems `variance_sampleMean_le` and `eq_sampleMean_of_variance_eq` (no `IsMinVariance` is
defined). `IsComplete` is the plan's name; inside this namespace it hides Mathlib's
`_root_.IsComplete` (complete sets of a uniform space), which is unrelated (review r50).

## What is cited

Checked for this order by web search against the publication records, not by reading the papers:
sufficiency defined through a common version of the conditional chances, as here, is in the spirit
of Halmos and Savage (1949, Annals of Mathematical Statistics 20, 225–241; the exact form of their
definition was not checked); the factorization theorem is Fisher's (1922, Philosophical
Transactions of the Royal Society A 222, 309–368) and Neyman's (1935, Giornale dell'Istituto
Italiano degli Attuari 6), proved here only for finite spaces with positive chances; Rao–Blackwell
is Rao's (1945, Bulletin of the Calcutta Mathematical Society 37) and Blackwell's (1947, Annals of
Mathematical Statistics 18, 105–110); Lehmann–Scheffé is Lehmann and Scheffé's (1950, Sankhyā 10,
305–340). No textbook theorem number is cited; none was checked.

## Hypotheses

Measured in order LEAN-20's checks (checks C50 to C54 and C61, exact rationals): 120 families on
finite spaces with every mass positive (sufficient exactly when factorizable), 120 sufficient
families (one `g` for all `θ`, same mean, the mean-squared-error identity, the inequality, equality
exactly when `T = g`), 30 coin-flip families, and 60 coin-flip families with `n + 1` values of
`θ` (the number of heads complete, the sample mean of least variance). Each hypothesis below fails
when dropped alone:

* sufficiency, in `exists_condExp_eq` and `raoBlackwell`: on `{0, 1}` with `P θ` Bernoulli for
  `θ = 1/3, 2/3` and `m` trivial, `E_θ[1_{1}] = θ` differs between the two.
* `T` integrable under every `P θ` (worked by hand): on `ℕ` with all sets measurable,
  `P θ (ω) = (1 − θ) θ^ω` for `θ = 1/4, 3/4`, and `T ω = 2^ω`: integrable under `1/4`, where
  `E[T | m] = T`, but not under `3/4`, where Lean's `E[T | m]` is `0`; both measures charge every
  point, so no `g` is both.
* `m ≤ m₀`, now part of `IsSufficient` (order LEAN-19's case): on `Bool` with `m₀` trivial and `m`
  all sets, Lean's `E[T | m]` is `0`, so `g = 0` would be a common version of everything and for
  `T = 1` the means differ.
* `T` square-integrable, in `raoBlackwell` (worked by hand, as in order LEAN-19): on `[0, 1]`, `m`
  generated by `[0, 1/2)`, `T = x^(−1/2)` on it and `0` off it: Lean's `E[T²]` is `0` while
  `E[g²] > 0`.
* completeness, in Lehmann–Scheffé: two coin flips with `m` all sets (sufficient, not complete):
  the first flip is unbiased and `m`-measurable but has variance `2/9` at `θ = 1/3`, more than the
  sample mean's `1/9`.
* sufficiency, in Lehmann–Scheffé: two flips with `m` generated by the first flip (complete, not
  sufficient): the same two estimators, `2/9 > 1/9`.
* `U` `m`-measurable: with `m` from the number of heads, `U` the first flip: `2/9 > 1/9`.
* `T` unbiased: `T = 0` has variance `0`, less than the sample mean's.
* `Var T = Var U`, in the uniqueness: `T` the first flip is not the sample mean.
* in `isComplete_numHeads`, the range of `θ`: with only `n` values of `θ`, some nonzero function of
  the number of heads has mean `0` under each (check C61); and a function that is not a function of
  the number of heads, `ω ↦ [ω 0] − [ω 1]`, has mean `0` for every `θ` and is not `0`.

* `T` measurable, in `exists_condExp_eq` (review r50's case): the family of point masses at every
  real number, with `m` all Borel sets and `T` the indicator of a set that is not Borel: under each
  point mass `T` is almost surely constant, and no Borel `g` matches all of them. So the plan's
  row, which asks only that `T` be integrable, is false in Lean, and measurability is assumed.
* in Lehmann–Scheffé (review r50, worked by hand, not checked here): `U` integrable is needed in
  the uniqueness (a geometric family with `U ω = ω!`); `T` square-integrable is needed in the
  variance inequality (Lean's variance of a function that is not square-integrable is `0`).

Not shown needed: every mass positive in the factorization theorem (review r50 argues it can be
removed; assumed as the plan states it); `p ∈ (0, 1)` rather than `[0, 1]` for the coin flips
(completeness needs only `n + 1` values of `p`). The theorems about families assume finite
(`exists_condExp_eq`) or probability measures (`raoBlackwell`, Lehmann–Scheffé, because order
LEAN-19's variance-plus-bias identity does); `m ≤ m₀` is part of `IsSufficient`.

Basu's theorem (order LEAN-24, `checks.py` lines B1 to B4, exact rationals; B2 and B3 only check
the final arithmetic, their models are worked by hand). Each hypothesis fails when dropped
alone. Sufficiency: on `{0, 1, 2, 3}` with `P₀ = (1/8, 1/8, 1/4, 1/2)` and
`P₁ = (1/8, 1/8, 3/8, 3/8)`, `m` generated by the cells `{0, 2}`, `{1, 3}` is complete but not
sufficient, `A = 1{2, 3}` is ancillary (chance `3/4` under both), and
`P₀({0, 2} ∩ {A = 1}) = 1/4 ≠ (3/8)(3/4) = 9/32`. Completeness: one law, uniform on two points,
`m` all events and `A` the identity: `1/2 ≠ 1/4`. Ancillarity: one coin flip with `A = S`:
`1/2 ≠ 1/4` at `p = 1/2`. The theorem is not restated for coin flips (item 61), because there it
says nothing: every event whose chance does not depend on `p` has chance `0` or `1`. The chance
is a polynomial in `p`; if it is constant on `(0, 1)` it equals its limit as `p → 0`, the number
of all-tails sequences in the event, `0` or `1` (review r58; also checked exhaustively over all
events of up to five flips, by their counts of sequences with each number of heads).

Item 102 (order LEAN-31's exact checks, lane `lean/LEAN-31-checks.py`, exact fractions). For
`indep_of_isSufficient_of_isBoundedlyComplete_of_isAncillary`, with any one hypothesis dropped,
the theorem fails. Bounded completeness (`102.drop.hC`): one law, uniform on two points, `m` all
events, `A` the identity: `m` is sufficient and `A` ancillary, `1_{0} − 1/2` is bounded with mean
`0` and not `0`, and `1/2 ≠ 1/4`. Sufficiency (`102.drop.hS`): item 58's case above, `m` complete
so boundedly complete. Ancillarity (`102.drop.hanc`): one coin, `θ` in `{1/3, 2/3}`, `m` all
events, `A` the coin: `1/3 ≠ 1/9`. `A` measurable (`102.drop.hA`, the arithmetic; the case by
hand): four points, `m₀ = m` generated by `{0, 1}` and `{2, 3}`, `A` the identity, not almost
everywhere measurable, so Lean's `map` is the zero measure for every `θ` and `A` counts as
ancillary; with the outer measure `1/3 ≠ 1/9`. The probability measures (`102.drop.prob`, the
arithmetic; the case by hand): one point, `P = 2 δ`, `m` all events: `2 ≠ 4`. For
`IsComplete.isBoundedlyComplete` (claude-ai's cases): completeness (the model of `102.drop.hC`:
finite, `m ≤ m₀`, neither complete nor boundedly complete); `m ≤ m₀` (by hand): on `Bool` with
`m₀` trivial and `m` all sets, one law; an integrable function is almost everywhere
`m₀`-measurable, so constant, and only `0` has mean `0`, so `IsComplete` holds; the indicator of
`true` is bounded and `m`-measurable but not integrable, so its Lean integral is `0`, and it is not
`0` almost surely; the finite measures (by hand): the counting measure on `ℕ`, `m` trivial; the
`m`-measurable functions are the constants and only `0` is integrable, so `IsComplete` holds; the
constant `1` is bounded, not integrable, of Lean integral `0`, and not `0` almost surely. Junk
value in the last two: the integral of a function that is not integrable is `0`.

## What is cited (Basu)

For a work not read here, author, title and year only: D. Basu, "On Statistics Independent of a
Complete Sufficient Statistic", 1955.

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-20, `grep -rniE` over Mathlib): "sufficient
statistic" only in citations of Fritz 2020; `rao.?blackwell` 0; `fisher|neyman` 0; `lehmann|scheff`
0; completeness of a statistic 0; `unbiased|UMVU|minimum.?variance` 0 (item 61: binomial
completeness 0, `sampleMean` 0). Order LEAN-24: "basu|ancillary|complete statistic|boundedly
complete" has one hit, the word "ancillary" in a ring-theory docstring. Order LEAN-31: the plan's
search `boundedly complete|bounded completeness` (`MATH-PLAN-library-2-checks.py`, line `row.L14`),
before item 102 was written, found 0 lines in pinned Mathlib and in Mathlib master at `2da3ab0a`,
and 1 in the library, this file's Basu bullet. Used: `condExp_tsum`,
`SimpleFunc.eapproxDiff`,
`ae_eq_condExp_of_forall_setIntegral_eq`, `integral_condVar_add_variance_condExp`,
`bernoulliMeasure`, `Measure.pi`, `measurePreserving_eval`,
`Polynomial.eq_zero_of_infinite_isRoot`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace ClassicalLean.Statistics

variable {Θ Ω : Type*}

section General

variable {m m₀ : MeasurableSpace Ω}

/-- **Sufficiency.** A σ-algebra `m` (for example the one a statistic generates) is sufficient for
a family `P θ` of distributions when it is a sub-σ-algebra and, for every event `s`, one
`m`-measurable function is a version of the chance of `s` given `m` under every `P θ` at once: the
conditional chance does not depend on `θ`. The condition `m ≤ m₀` is part of the definition
(review r50): without it Mathlib's conditional expectation is `0` by convention, and every family
would count as sufficient. The theorems below also assume finite measures, for the same reason. -/
def IsSufficient (P : Θ → Measure[m₀] Ω) (m : MeasurableSpace Ω) : Prop :=
  m ≤ m₀ ∧ ∀ s, MeasurableSet[m₀] s → ∃ g : Ω → ℝ, StronglyMeasurable[m] g ∧
    ∀ θ, g =ᵐ[P θ] (P θ)[s.indicator fun _ ↦ (1 : ℝ) | m]

/-- One `m`-measurable function that is a version of `E[f | m]` under every `P θ`. -/
private def HasCommonCondExp (P : Θ → Measure[m₀] Ω) (m : MeasurableSpace Ω) (f : Ω → ℝ) :
    Prop :=
  ∃ g : Ω → ℝ, StronglyMeasurable[m] g ∧ ∀ θ, g =ᵐ[P θ] (P θ)[f | m]

section Extension

variable {P : Θ → Measure[m₀] Ω}

private theorem hasCommonCondExp_indicator (hP : IsSufficient P m) (c : ℝ) {s : Set Ω}
    (hs : MeasurableSet[m₀] s) : HasCommonCondExp P m (s.indicator fun _ ↦ c) := by
  obtain ⟨g, hg, hgθ⟩ := hP.2 s hs
  refine ⟨c • g, hg.const_smul c, fun θ ↦ ?_⟩
  have hc : (s.indicator fun _ ↦ c) = c • s.indicator fun _ ↦ (1 : ℝ) := by
    ext ω
    by_cases hω : ω ∈ s <;> simp [hω]
  rw [hc]
  filter_upwards [hgθ θ, condExp_smul (μ := P θ) c (s.indicator fun _ ↦ (1 : ℝ)) m]
    with ω h1 h2
  rw [h2, Pi.smul_apply, Pi.smul_apply, h1]

private theorem HasCommonCondExp.add {f g : Ω → ℝ} (hf : ∀ θ, Integrable f (P θ))
    (hg : ∀ θ, Integrable g (P θ)) (h1 : HasCommonCondExp P m f) (h2 : HasCommonCondExp P m g) :
    HasCommonCondExp P m (f + g) := by
  obtain ⟨g1, hg1, h1θ⟩ := h1
  obtain ⟨g2, hg2, h2θ⟩ := h2
  exact ⟨g1 + g2, hg1.add hg2, fun θ ↦
    ((h1θ θ).add (h2θ θ)).trans (condExp_add (hf θ) (hg θ) m).symm⟩

private theorem HasCommonCondExp.sub {f g : Ω → ℝ} (hf : ∀ θ, Integrable f (P θ))
    (hg : ∀ θ, Integrable g (P θ)) (h1 : HasCommonCondExp P m f) (h2 : HasCommonCondExp P m g) :
    HasCommonCondExp P m (f - g) := by
  obtain ⟨g1, hg1, h1θ⟩ := h1
  obtain ⟨g2, hg2, h2θ⟩ := h2
  exact ⟨g1 - g2, hg1.sub hg2, fun θ ↦
    ((h1θ θ).sub (h2θ θ)).trans (condExp_sub (hf θ) (hg θ) m).symm⟩

variable [∀ θ, IsFiniteMeasure (P θ)]

private theorem hasCommonCondExp_simpleFunc (hP : IsSufficient P m) (d : @SimpleFunc Ω m₀ ℝ) :
    HasCommonCondExp P m d := by
  induction d using SimpleFunc.induction with
  | @const c t ht =>
    convert hasCommonCondExp_indicator hP c ht using 1
    ext ω
    by_cases hω : ω ∈ t <;> simp [SimpleFunc.piecewise_apply, hω]
  | add _ hf hg =>
    rw [SimpleFunc.coe_add]
    exact hf.add (fun θ ↦ SimpleFunc.integrable_of_isFiniteMeasure _)
      (fun θ ↦ SimpleFunc.integrable_of_isFiniteMeasure _) hg

private theorem hasCommonCondExp_of_nonneg (hP : IsSufficient P m) {T : Ω → ℝ}
    (hTm : Measurable[m₀] T) (h0 : ∀ ω, 0 ≤ T ω) (hT : ∀ θ, Integrable T (P θ)) :
    HasCommonCondExp P m T := by
  set f : Ω → ℝ≥0∞ := fun ω ↦ ENNReal.ofReal (T ω)
  have hf : Measurable f := ENNReal.measurable_ofReal.comp hTm
  set d : ℕ → Ω → ℝ := fun n ω ↦ (SimpleFunc.eapproxDiff f n ω : ℝ)
  have hd_simple : ∀ n, d n = ⇑((SimpleFunc.eapproxDiff f n).map ((↑) : ℝ≥0 → ℝ)) := by
    intro n
    ext ω
    simp [d]
  have hsum : ∀ ω, ∑' n, d n ω = T ω := by
    intro ω
    have h1 := SimpleFunc.tsum_eapproxDiff f hf ω
    have hs : Summable fun n ↦ (SimpleFunc.eapproxDiff f n ω : ℝ≥0) :=
      ENNReal.tsum_coe_ne_top_iff_summable.mp (h1 ▸ ENNReal.ofReal_ne_top)
    have h2 : ((∑' n, SimpleFunc.eapproxDiff f n ω : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (T ω) := by
      rw [ENNReal.coe_tsum hs]
      exact h1
    have h3 : (∑' n, SimpleFunc.eapproxDiff f n ω : ℝ≥0) = (T ω).toNNReal :=
      ENNReal.coe_injective h2
    simp only [d]
    rw [← NNReal.coe_tsum, h3, Real.coe_toNNReal _ (h0 ω)]
  have hc : ∀ n, HasCommonCondExp P m (d n) := fun n ↦ by
    rw [hd_simple n]
    exact hasCommonCondExp_simpleFunc hP _
  choose g hgm hgθ using hc
  set G : Ω → ℝ := fun ω ↦ ∑' n, g n ω
  have hGm : StronglyMeasurable[m] G := by
    let _ : MeasurableSpace Ω := m
    exact StronglyMeasurable.tsum hgm
  refine ⟨G, hGm, fun θ ↦ ?_⟩
  have hint_d : ∀ n, Integrable (d n) (P θ) := fun n ↦ by
    rw [hd_simple n]
    exact SimpleFunc.integrable_of_isFiniteMeasure _
  have hfin : ∑' n, ∫⁻ ω, ‖d n ω‖ₑ ∂P θ ≠ ∞ := by
    have he : ∀ n, ∫⁻ ω, ‖d n ω‖ₑ ∂P θ = ∫⁻ ω, (SimpleFunc.eapproxDiff f n ω : ℝ≥0∞) ∂P θ :=
      fun n ↦ lintegral_congr fun ω ↦ by simp [d]
    simp_rw [he]
    rw [← lintegral_tsum fun n ↦ (SimpleFunc.measurable _).coe_nnreal_ennreal.aemeasurable]
    simp_rw [SimpleFunc.tsum_eapproxDiff f hf]
    rw [← ofReal_integral_eq_lintegral_ofReal (hT θ) (ae_of_all _ h0)]
    exact ENNReal.ofReal_ne_top
  have hae := condExp_tsum (μ := P θ) (m := m) (f := d)
    (fun n ↦ (hint_d n).aestronglyMeasurable) hfin
  have hT' : (P θ)[T | m] = (P θ)[fun ω ↦ ∑' n, d n ω | m] := by
    congr 1
    funext ω
    exact (hsum ω).symm
  filter_upwards [ae_all_iff.2 fun n ↦ hgθ n θ, hae] with ω h1 h3
  rw [hT', h3]
  exact tsum_congr h1

/-- **From events to statistics.** If `m` is sufficient for a family of finite measures, then
for every measurable `T` that is integrable under every `P θ`, one `m`-measurable function `g` is
a version of `E[T | m]` under every `P θ` at once. Simple functions are finite sums of events;
a nonnegative `T` is a countable sum of nonnegative simple functions (Mathlib's
`SimpleFunc.eapproxDiff`), and the conditional expectation of such a sum is the sum of the
conditional expectations (Mathlib's `condExp_tsum`), almost surely under each `P θ`; a general
`T` is its positive part minus its negative part. -/
theorem IsSufficient.exists_condExp_eq (hP : IsSufficient P m) {T : Ω → ℝ}
    (hTm : StronglyMeasurable[m₀] T) (hT : ∀ θ, Integrable T (P θ)) :
    ∃ g : Ω → ℝ, StronglyMeasurable[m] g ∧ ∀ θ, g =ᵐ[P θ] (P θ)[T | m] := by
  have hpm : Measurable[m₀] fun ω ↦ max (T ω) 0 := hTm.measurable.max measurable_const
  have hnm : Measurable[m₀] fun ω ↦ max (-T ω) 0 := hTm.measurable.neg.max measurable_const
  have hpi : ∀ θ, Integrable (fun ω ↦ max (T ω) 0) (P θ) := fun θ ↦ (hT θ).pos_part
  have hni : ∀ θ, Integrable (fun ω ↦ max (-T ω) 0) (P θ) := fun θ ↦ (hT θ).neg_part
  have h := (hasCommonCondExp_of_nonneg hP hpm (fun ω ↦ le_max_right _ _) hpi).sub hpi hni
    (hasCommonCondExp_of_nonneg hP hnm (fun ω ↦ le_max_right _ _) hni)
  have hT' : ((fun ω ↦ max (T ω) 0) - fun ω ↦ max (-T ω) 0) = T := by
    ext ω
    simp only [Pi.sub_apply]
    rcases le_total 0 (T ω) with h0 | h0
    · rw [max_eq_left h0, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right h0, max_eq_left (by linarith)]
      ring
  rwa [hT'] at h

end Extension

section RaoBlackwell

variable {μ : Measure[m₀] Ω} [IsProbabilityMeasure μ]

/-- **What conditioning removes.** For `T` square-integrable and `m` a sub-σ-algebra, the mean
squared distance from `T` to `E[T | m]` is `Var T − Var E[T | m]`: Mathlib's law of total
variance, read through the definition of the conditional variance. -/
theorem integral_sub_condExp_sq_eq (hm : m ≤ m₀) {T : Ω → ℝ} (hT : MemLp T 2 μ) :
    ∫ ω, (T ω - μ[T | m] ω) ^ 2 ∂μ = Var[T; μ] - Var[μ[T | m]; μ] := by
  have h := integral_condVar_add_variance_condExp hm hT
  have hcv : ∫ ω, Var[T; μ | m] ω ∂μ = ∫ ω, (T ω - μ[T | m] ω) ^ 2 ∂μ := by
    unfold condVar
    rw [integral_condExp hm]
    rfl
  rw [← hcv]
  linarith

/-- **Mean squared error splits along conditioning.** For `T` square-integrable, `m` a
sub-σ-algebra and any number `τ`:
`E[(T − τ)²] = E[(E[T | m] − τ)²] + E[(T − E[T | m])²]`. Order LEAN-19's variance-plus-bias
identity for both `T` and `E[T | m]`, which have the same mean, and `integral_sub_condExp_sq_eq`. -/
theorem integral_sub_sq_eq_integral_condExp_sub_sq_add (hm : m ≤ m₀) {T : Ω → ℝ}
    (hT : MemLp T 2 μ) (τ : ℝ) :
    ∫ ω, (T ω - τ) ^ 2 ∂μ
      = ∫ ω, (μ[T | m] ω - τ) ^ 2 ∂μ + ∫ ω, (T ω - μ[T | m] ω) ^ 2 ∂μ := by
  rw [integral_sub_sq_eq_variance_add_sq hT τ,
    integral_sub_sq_eq_variance_add_sq (hT.condExp one_le_two) τ, integral_condExp hm,
    integral_sub_condExp_sq_eq hm hT]
  ring

/-- **The Rao–Blackwell theorem.** If `m` is sufficient for a family of probability measures and
`T` is measurable and square-integrable under every `P θ`, there is one `m`-measurable `g` (a
statistic: computing it does not need the true `θ`) that is a version of `E[T | m]` under every
`P θ`, has the same mean as `T` under every `P θ`, and for every `θ` and every target `τ` has mean
squared error `E[(g − τ)²]` at most `T`'s, with equality only when `T = g` almost surely under
`P θ`. The inequality is order LEAN-19's `integral_sq_condExp_sub_le`, applied under each `P θ`;
sufficiency is what makes `g` one function for all `θ`. -/
theorem IsSufficient.raoBlackwell {P : Θ → Measure[m₀] Ω} [∀ θ, IsProbabilityMeasure (P θ)]
    (hP : IsSufficient P m) {T : Ω → ℝ} (hTm : StronglyMeasurable[m₀] T)
    (hT : ∀ θ, MemLp T 2 (P θ)) :
    ∃ g : Ω → ℝ, StronglyMeasurable[m] g ∧ ∀ θ, g =ᵐ[P θ] (P θ)[T | m] ∧
      ∫ ω, g ω ∂P θ = ∫ ω, T ω ∂P θ ∧
      ∀ τ : ℝ, ∫ ω, (g ω - τ) ^ 2 ∂P θ ≤ ∫ ω, (T ω - τ) ^ 2 ∂P θ ∧
        (∫ ω, (g ω - τ) ^ 2 ∂P θ = ∫ ω, (T ω - τ) ^ 2 ∂P θ → T =ᵐ[P θ] g) := by
  have hm := hP.1
  obtain ⟨g, hgm, hg⟩ := hP.exists_condExp_eq hTm fun θ ↦ (hT θ).integrable one_le_two
  refine ⟨g, hgm, fun θ ↦ ⟨hg θ, ?_, fun τ ↦ ?_⟩⟩
  · rw [integral_congr_ae (hg θ), integral_condExp hm]
  have hsq : ∫ ω, (g ω - τ) ^ 2 ∂P θ = ∫ ω, ((P θ)[T | m] ω - τ) ^ 2 ∂P θ :=
    integral_congr_ae ((hg θ).mono fun ω h ↦ by simp only [h])
  rw [hsq]
  refine ⟨integral_sq_condExp_sub_le hm (hT θ) τ, fun heq ↦ ?_⟩
  have hsplit := integral_sub_sq_eq_integral_condExp_sub_sq_add hm (hT θ) τ
  have hzero : ∫ ω, (T ω - (P θ)[T | m] ω) ^ 2 ∂P θ = 0 := by linarith
  have hint : Integrable (fun ω ↦ (T ω - (P θ)[T | m] ω) ^ 2) (P θ) :=
    ((hT θ).sub ((hT θ).condExp one_le_two)).integrable_sq
  have hae := (integral_eq_zero_iff_of_nonneg (fun ω ↦ sq_nonneg _) hint).mp hzero
  filter_upwards [hae, hg θ] with ω h1 h2
  have : T ω - (P θ)[T | m] ω = 0 := by simpa using h1
  rw [h2]
  linarith

end RaoBlackwell

/-- **Completeness.** A σ-algebra `m` is complete for a family `P θ` of distributions when the
only `m`-measurable function that is integrable with mean `0` under every `P θ` is `0`, almost
surely under every `P θ`. -/
def IsComplete (P : Θ → Measure[m₀] Ω) (m : MeasurableSpace Ω) : Prop :=
  ∀ f : Ω → ℝ, StronglyMeasurable[m] f → (∀ θ, Integrable f (P θ)) →
    (∀ θ, ∫ ω, f ω ∂P θ = 0) → ∀ θ, f =ᵐ[P θ] 0

/-- **Bounded completeness** (order LEAN-31, item 102 of MATH-PLAN-library-2). Only the bounded
`m`-measurable functions with mean `0` under every `P θ` must vanish, almost surely under every
`P θ`. "Bounded" is a bound at every point; a function bounded almost surely under every `P θ`
by one constant equals a bounded one almost surely under every `P θ` (set it to `0` where it
exceeds the bound), so the two readings give the same condition. -/
def IsBoundedlyComplete (P : Θ → Measure[m₀] Ω) (m : MeasurableSpace Ω) : Prop :=
  ∀ f : Ω → ℝ, StronglyMeasurable[m] f → (∃ C, ∀ ω, |f ω| ≤ C) →
    (∀ θ, ∫ ω, f ω ∂P θ = 0) → ∀ θ, f =ᵐ[P θ] 0

/-- **Completeness gives bounded completeness** (order LEAN-31, item 102), for finite measures and
`m ≤ m₀`: a bounded `m`-measurable function is integrable under each finite `P θ`, so
completeness applies to it. So `IsBoundedlyComplete` is the weaker hypothesis. -/
theorem IsComplete.isBoundedlyComplete {P : Θ → Measure[m₀] Ω} [∀ θ, IsFiniteMeasure (P θ)]
    (hm : m ≤ m₀) (hC : IsComplete P m) : IsBoundedlyComplete P m := by
  intro f hf ⟨C, hCf⟩ hmean θ
  refine hC f hf (fun θ' ↦ ?_) hmean θ
  exact Integrable.of_bound (hf.mono hm).aestronglyMeasurable C
    (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hCf ω)

section LehmannScheffe

variable {P : Θ → Measure[m₀] Ω} [∀ θ, IsProbabilityMeasure (P θ)]

/-- The Rao–Blackwell improvement of an unbiased `T` is, under every `P θ`, almost surely equal to
any unbiased `m`-measurable `U`, when `m` is sufficient and complete. -/
private theorem ae_eq_condExp_of_isComplete (hS : IsSufficient P m)
    (hC : IsComplete P m) {U T : Ω → ℝ} {τ : Θ → ℝ} (hUm : StronglyMeasurable[m] U)
    (hU : ∀ θ, Integrable U (P θ)) (hUτ : ∀ θ, ∫ ω, U ω ∂P θ = τ θ)
    (hTm : StronglyMeasurable[m₀] T) (hT : ∀ θ, MemLp T 2 (P θ))
    (hTτ : ∀ θ, ∫ ω, T ω ∂P θ = τ θ) (θ : Θ) : U =ᵐ[P θ] (P θ)[T | m] := by
  have hm := hS.1
  obtain ⟨g, hgm, hg⟩ := hS.exists_condExp_eq hTm fun θ ↦ (hT θ).integrable one_le_two
  have hgi : ∀ θ, Integrable g (P θ) := fun θ ↦ integrable_condExp.congr (hg θ).symm
  have hmean : ∀ θ, ∫ ω, (g - U) ω ∂P θ = 0 := fun θ ↦ by
    rw [Pi.sub_def, integral_sub (hgi θ) (hU θ), integral_congr_ae (hg θ), integral_condExp hm,
      hTτ, hUτ, sub_self]
  have h0 := hC (g - U) (hgm.sub hUm) (fun θ ↦ (hgi θ).sub (hU θ)) hmean θ
  filter_upwards [h0, hg θ] with ω h1 h2
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h1
  rw [← h2, h1]

/-- **The Lehmann–Scheffé theorem.** If `m` is sufficient and complete for a family of probability
measures, an unbiased estimator `U` of `τ θ` that is `m`-measurable has the least variance among
all unbiased estimators, under every `θ` at once: `Var U ≤ Var T` for every measurable `T` that is
square-integrable with mean `τ θ` under every `P θ`. The Rao–Blackwell improvement of `T` is
unbiased and `m`-measurable, so by completeness it is `U`; and conditioning does not raise
variance (order LEAN-19's `variance_condExp_le`). -/
theorem variance_le_of_isSufficient_of_isComplete (hS : IsSufficient P m)
    (hC : IsComplete P m) {U T : Ω → ℝ} {τ : Θ → ℝ} (hUm : StronglyMeasurable[m] U)
    (hU : ∀ θ, Integrable U (P θ)) (hUτ : ∀ θ, ∫ ω, U ω ∂P θ = τ θ)
    (hTm : StronglyMeasurable[m₀] T) (hT : ∀ θ, MemLp T 2 (P θ))
    (hTτ : ∀ θ, ∫ ω, T ω ∂P θ = τ θ) (θ : Θ) :
    Var[U; P θ] ≤ Var[T; P θ] := by
  rw [variance_congr (ae_eq_condExp_of_isComplete hS hC hUm hU hUτ hTm hT hTτ θ)]
  exact variance_condExp_le (hT θ)

/-- **The least-variance unbiased estimator is unique.** Under the hypotheses of
`variance_le_of_isSufficient_of_isComplete`, an unbiased `T` with the same variance as `U` under
`P θ` is equal to `U` almost surely under `P θ`: the variance `T` loses on conditioning is
`E[(T − E[T | m])²]`, which is then `0`. -/
theorem ae_eq_of_variance_eq_of_isSufficient_of_isComplete
    (hS : IsSufficient P m) (hC : IsComplete P m) {U T : Ω → ℝ} {τ : Θ → ℝ}
    (hUm : StronglyMeasurable[m] U) (hU : ∀ θ, Integrable U (P θ))
    (hUτ : ∀ θ, ∫ ω, U ω ∂P θ = τ θ) (hTm : StronglyMeasurable[m₀] T)
    (hT : ∀ θ, MemLp T 2 (P θ)) (hTτ : ∀ θ, ∫ ω, T ω ∂P θ = τ θ) (θ : Θ)
    (hvar : Var[T; P θ] = Var[U; P θ]) :
    T =ᵐ[P θ] U := by
  have hm := hS.1
  have hUe := ae_eq_condExp_of_isComplete hS hC hUm hU hUτ hTm hT hTτ θ
  rw [variance_congr hUe] at hvar
  have hzero : ∫ ω, (T ω - (P θ)[T | m] ω) ^ 2 ∂P θ = 0 := by
    rw [integral_sub_condExp_sq_eq hm (hT θ), hvar, sub_self]
  have hint : Integrable (fun ω ↦ (T ω - (P θ)[T | m] ω) ^ 2) (P θ) :=
    ((hT θ).sub ((hT θ).condExp one_le_two)).integrable_sq
  have hae := (integral_eq_zero_iff_of_nonneg (fun ω ↦ sq_nonneg _) hint).mp hzero
  filter_upwards [hae, hUe] with ω h1 h2
  have : T ω - (P θ)[T | m] ω = 0 := by simpa using h1
  rw [h2]
  linarith

end LehmannScheffe

section Basu

/-! ### Item 58: Basu's theorem -/

variable {β : Type*} [MeasurableSpace β]

/-- **Ancillary statistic.** `A` is ancillary for a family `P θ` when its law does not depend on
`θ`: the image measures `(P θ).map A` are all equal. Meant for measurable `A`: for a statistic
that is not almost everywhere measurable, Mathlib's `map` gives a junk measure, and for
probability measures that junk is the same for every `θ`, so such an `A` counts as ancillary
(review r58); the theorems below assume `A` measurable. -/
def IsAncillary (P : Θ → Measure[m₀] Ω) (A : Ω → β) : Prop :=
  ∀ θ θ', (P θ).map A = (P θ').map A

/-- **Basu's theorem.** If `m` is sufficient (item 50) and complete (item 54) for a family of
probability measures, it is independent, under every `P θ`, of the σ-algebra generated by any
ancillary statistic `A`. For an event `B = {A ∈ B'}`, its chance `c` is the same under every
`P θ`; the common version `g` of `P(B | m)` has mean `c` under every `P θ`, so by completeness
`g = c` almost surely, and `P(C ∩ B) = ∫_C g = c P(C)` for every `C ∈ m`. -/
theorem indep_of_isSufficient_of_isComplete_of_isAncillary {P : Θ → Measure[m₀] Ω}
    [∀ θ, IsProbabilityMeasure (P θ)] (hS : IsSufficient P m) (hC : IsComplete P m)
    {A : Ω → β} (hA : Measurable[m₀] A) (hanc : IsAncillary P A) (θ : Θ) :
    Indep m (MeasurableSpace.comap A inferInstance) (P θ) := by
  have hm := hS.1
  rw [Indep_iff]
  intro C B hCm hBm
  obtain ⟨B', hB', rfl⟩ := hBm
  have hB : MeasurableSet[m₀] (A ⁻¹' B') := hA hB'
  set c := (P θ).real (A ⁻¹' B') with hc_def
  have hc : ∀ θ', (P θ').real (A ⁻¹' B') = c := fun θ' ↦ by
    rw [hc_def, ← map_measureReal_apply hA hB', ← map_measureReal_apply hA hB', hanc θ' θ]
  obtain ⟨g, hgm, hg⟩ := hS.2 _ hB
  have hgi : ∀ θ', Integrable g (P θ') := fun θ' ↦ integrable_condExp.congr (hg θ').symm
  have hind : ∀ θ', Integrable ((A ⁻¹' B').indicator fun _ ↦ (1 : ℝ)) (P θ') :=
    fun θ' ↦ (integrable_const _).indicator hB
  have hmean : ∀ θ', ∫ ω, (fun ω ↦ g ω - c) ω ∂P θ' = 0 := fun θ' ↦ by
    rw [integral_sub (hgi θ') (integrable_const c), integral_congr_ae (hg θ'),
      integral_condExp hm, integral_indicator_const _ hB, smul_eq_mul, mul_one, hc,
      integral_const, probReal_univ, one_smul, sub_self]
  have h0 := hC (fun ω ↦ g ω - c) (hgm.sub stronglyMeasurable_const)
    (fun θ' ↦ (hgi θ').sub (integrable_const c)) hmean θ
  have hgc : g =ᵐ[P θ] fun _ ↦ c := by
    filter_upwards [h0] with ω hω
    simpa [sub_eq_zero] using hω
  have hreal : (P θ).real (C ∩ A ⁻¹' B') = (P θ).real C * (P θ).real (A ⁻¹' B') := by
    have h1 : (P θ).real (C ∩ A ⁻¹' B') =
        ∫ ω in C, (A ⁻¹' B').indicator (fun _ ↦ (1 : ℝ)) ω ∂P θ := by
      rw [integral_indicator_const _ hB, smul_eq_mul, mul_one, measureReal_restrict_apply hB,
        Set.inter_comm]
    rw [h1, ← setIntegral_condExp hm (hind θ) hCm,
      setIntegral_congr_ae (hm C hCm) (by filter_upwards [hg θ, hgc] with ω h1 h2 _; rw [← h1, h2]),
      setIntegral_const, smul_eq_mul, mul_comm]
  rw [measureReal_def, measureReal_def, measureReal_def, ← ENNReal.toReal_mul] at hreal
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).1 hreal

/-- **Basu's theorem, for statistics.** A sufficient and complete statistic `S` is independent of
every measurable ancillary statistic `A`, under every `P θ`. The name is the plan's; it leaves out
that `S` must also be sufficient (`hS`). -/
theorem indepFun_of_isComplete_of_ancillary {γ : Type*} [MeasurableSpace γ]
    {P : Θ → Measure[m₀] Ω} [∀ θ, IsProbabilityMeasure (P θ)] {S : Ω → γ}
    (hS : IsSufficient P (MeasurableSpace.comap S inferInstance))
    (hC : IsComplete P (MeasurableSpace.comap S inferInstance)) {A : Ω → β}
    (hA : Measurable[m₀] A) (hanc : IsAncillary P A) (θ : Θ) :
    IndepFun S A (P θ) := by
  rw [IndepFun_iff_Indep]
  exact indep_of_isSufficient_of_isComplete_of_isAncillary hS hC hA hanc θ

/-- **Basu's theorem with bounded completeness** (order LEAN-31, item 102 of MATH-PLAN-library-2).
If `m` is sufficient and boundedly complete for a family of probability measures, it is
independent, under every `P θ`, of the σ-algebra generated by any measurable ancillary statistic
`A`. Item 58's proof, with one change: the common version `g` of `P(B | m)` lies in `[-1, 1]`
almost surely under every `P θ` (a conditional expectation of an indicator), so its truncation
`max (-1) (min 1 g)` is `m`-measurable, bounded and almost surely equal to `g`, and bounded
completeness applies to it minus its mean. Since completeness gives bounded completeness
(`IsComplete.isBoundedlyComplete`, with `m ≤ m₀` from sufficiency), this theorem is wider than
`indep_of_isSufficient_of_isComplete_of_isAncillary`. -/
theorem indep_of_isSufficient_of_isBoundedlyComplete_of_isAncillary {β : Type*}
    [MeasurableSpace β] {P : Θ → Measure[m₀] Ω} [∀ θ, IsProbabilityMeasure (P θ)]
    (hS : IsSufficient P m) (hC : IsBoundedlyComplete P m) {A : Ω → β} (hA : Measurable[m₀] A)
    (hanc : IsAncillary P A) (θ : Θ) :
    Indep m (MeasurableSpace.comap A inferInstance) (P θ) := by
  have hm := hS.1
  rw [Indep_iff]
  intro C B hCm hBm
  obtain ⟨B', hB', rfl⟩ := hBm
  have hB : MeasurableSet[m₀] (A ⁻¹' B') := hA hB'
  set c := (P θ).real (A ⁻¹' B') with hc_def
  have hc : ∀ θ', (P θ').real (A ⁻¹' B') = c := fun θ' ↦ by
    rw [hc_def, ← map_measureReal_apply hA hB', ← map_measureReal_apply hA hB', hanc θ' θ]
  obtain ⟨g, hgm, hg⟩ := hS.2 _ hB
  have hgi : ∀ θ', Integrable g (P θ') := fun θ' ↦ integrable_condExp.congr (hg θ').symm
  have hind : ∀ θ', Integrable ((A ⁻¹' B').indicator fun _ ↦ (1 : ℝ)) (P θ') :=
    fun θ' ↦ (integrable_const _).indicator hB
  have hmean : ∀ θ', ∫ ω, (fun ω ↦ g ω - c) ω ∂P θ' = 0 := fun θ' ↦ by
    rw [integral_sub (hgi θ') (integrable_const c), integral_congr_ae (hg θ'),
      integral_condExp hm, integral_indicator_const _ hB, smul_eq_mul, mul_one, hc,
      integral_const, probReal_univ, one_smul, sub_self]
  -- the truncation of `g` to `[-1, 1]`, bounded and almost surely equal to `g`
  set g' : Ω → ℝ := fun ω ↦ max (-1) (min 1 (g ω)) with hg'_def
  have hg'm : StronglyMeasurable[m] g' :=
    (show Continuous fun x : ℝ ↦ max (-1) (min 1 x) from
      continuous_const.max (continuous_const.min continuous_id)).comp_stronglyMeasurable hgm
  have hgg' : ∀ θ', g' =ᵐ[P θ'] g := fun θ' ↦ by
    have hb : ∀ᵐ ω ∂P θ', |(P θ')[(A ⁻¹' B').indicator fun _ ↦ (1 : ℝ) | m] ω| ≤ 1 :=
      ae_bdd_abs_condExp_of_ae_bdd_abs (ae_of_all _ fun ω ↦ by
        by_cases h : ω ∈ A ⁻¹' B' <;> simp [h])
    filter_upwards [hg θ', hb] with ω h1 h2
    rw [← h1] at h2
    obtain ⟨h3, h4⟩ := abs_le.mp h2
    simp only [hg'_def, min_eq_right h4, max_eq_right h3]
  have hbd : ∀ ω, |g' ω - c| ≤ 1 + |c| := fun ω ↦ by
    have h5 : |g' ω| ≤ 1 :=
      abs_le.mpr ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
    exact (abs_sub _ _).trans (add_le_add h5 le_rfl)
  have hmean' : ∀ θ', ∫ ω, (fun ω ↦ g' ω - c) ω ∂P θ' = 0 := fun θ' ↦ by
    rw [← hmean θ']
    exact integral_congr_ae (by filter_upwards [hgg' θ'] with ω h; simp only [h])
  have h0 := hC (fun ω ↦ g' ω - c) (hg'm.sub stronglyMeasurable_const) ⟨1 + |c|, hbd⟩ hmean' θ
  have hgc : g =ᵐ[P θ] fun _ ↦ c := by
    filter_upwards [h0, hgg' θ] with ω hω h
    rw [← h]
    simpa [sub_eq_zero] using hω
  have hreal : (P θ).real (C ∩ A ⁻¹' B') = (P θ).real C * (P θ).real (A ⁻¹' B') := by
    have h1 : (P θ).real (C ∩ A ⁻¹' B') =
        ∫ ω in C, (A ⁻¹' B').indicator (fun _ ↦ (1 : ℝ)) ω ∂P θ := by
      rw [integral_indicator_const _ hB, smul_eq_mul, mul_one, measureReal_restrict_apply hB,
        Set.inter_comm]
    rw [h1, ← setIntegral_condExp hm (hind θ) hCm,
      setIntegral_congr_ae (hm C hCm) (by filter_upwards [hg θ, hgc] with ω h1 h2 _; rw [← h1, h2]),
      setIntegral_const, smul_eq_mul, mul_comm]
  rw [measureReal_def, measureReal_def, measureReal_def, ← ENNReal.toReal_mul] at hreal
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).1 hreal

end Basu

end General

section Finite

/-! ### Finite sample spaces -/

variable {β : Type*}

/-- Sums over the fibres of `S`: with nonnegative weights `w`,
`∑ᵢ [S i ∈ B] wᵢ (∑ⱼ [S j = S i] wⱼ Fⱼ) / (∑ⱼ [S j = S i] wⱼ) = ∑ᵢ [S i ∈ B] wᵢ Fᵢ`. Each fibre's
weighted average, weighted again by the fibre's weights, gives back the fibre's weighted sum. -/
private theorem sum_fibre_average {ι : Type*} [Fintype ι] [DecidableEq β] (w F : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (S : ι → β) (B : Set β) [DecidablePred (· ∈ B)] :
    ∑ i, (if S i ∈ B then w i * ((∑ j, if S j = S i then w j * F j else 0) /
        ∑ j, if S j = S i then w j else 0) else 0)
      = ∑ i, if S i ∈ B then w i * F i else 0 := by
  set D : ι → ℝ := fun i ↦ ∑ j, if S j = S i then w j else 0
  have hD : ∀ i j, S j = S i → D j = D i := fun i j h ↦ by simp only [D, h]
  have hwD : ∀ i, w i ≤ D i := fun i ↦ by
    have := Finset.single_le_sum (f := fun j ↦ if S j = S i then w j else 0)
      (fun j _ ↦ by split_ifs <;> simp [hw]) (Finset.mem_univ i)
    simpa using this
  have step1 : ∀ i, (if S i ∈ B then w i * ((∑ j, if S j = S i then w j * F j else 0) / D i)
      else 0) = ∑ j, if S i ∈ B ∧ S j = S i then w i * (w j * F j) / D i else 0 := by
    intro i
    by_cases hi : S i ∈ B
    · simp only [hi, ↓reduceIte]
      rw [mul_div_assoc', Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      by_cases hj : S j = S i <;> simp [hj]
    · simp [hi]
  simp only [D] at step1
  rw [Finset.sum_congr rfl fun i _ ↦ step1 i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have step2 : ∀ i, (if S i ∈ B ∧ S j = S i then w i * (w j * F j) / D i else 0)
      = (if S i = S j then w i else 0) * (if S j ∈ B then w j * F j / D j else 0) := by
    intro i
    by_cases hij : S i = S j
    · rw [hD j i hij]
      by_cases hjB : S j ∈ B
      · simp [hij, hjB, mul_div_assoc]
      · simp [hij, hjB]
    · have : ¬ S j = S i := fun h ↦ hij h.symm
      simp [hij, this]
  simp only [D] at step2
  rw [Finset.sum_congr rfl fun i _ ↦ step2 i, ← Finset.sum_mul]
  by_cases hjB : S j ∈ B
  · simp only [hjB, ↓reduceIte]
    change D j * (w j * F j / D j) = w j * F j
    rcases (le_trans (hw j) (hwD j)).eq_or_lt with h0 | hpos
    · have : w j = 0 := le_antisymm (h0 ▸ hwD j) (hw j)
      rw [← h0, this]
      ring
    · field_simp
  · simp [hjB]

/-- A function of a statistic is measurable for the statistic's σ-algebra. -/
theorem stronglyMeasurable_comp_comap (S : Ω → β) (H : β → ℝ) :
    StronglyMeasurable[MeasurableSpace.comap S ⊤] fun ω ↦ H (S ω) := by
  let _ : MeasurableSpace Ω := MeasurableSpace.comap S ⊤
  let _ : MeasurableSpace β := ⊤
  exact (measurable_from_top.comp (comap_measurable S)).stronglyMeasurable

variable [MeasurableSpace Ω]

/-- With every point of positive mass, almost sure equality is equality. -/
theorem eq_of_ae_eq_of_pos {μ : Measure Ω} (hpos : ∀ ω, 0 < μ.real {ω})
    {f g : Ω → ℝ} (h : f =ᵐ[μ] g) : f = g := by
  funext ω
  by_contra hne
  have h0 : μ {x | ¬ f x = g x} = 0 := ae_iff.mp h
  have h1 : μ {ω} = 0 := measure_mono_null (by simpa using hne) h0
  have := hpos ω
  rw [measureReal_def, h1] at this
  simp at this

variable [Finite Ω] [MeasurableSingletonClass Ω]

/-- On a finite space, a set integral is a finite sum. -/
private theorem setIntegral_eq_sum [Fintype Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (t : Set Ω)
    [DecidablePred (· ∈ t)] (F : Ω → ℝ) :
    ∫ x in t, F x ∂μ = ∑ x, if x ∈ t then μ.real {x} * F x else 0 := by
  rw [integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [measureReal_restrict_apply (measurableSet_singleton x), smul_eq_mul]
  by_cases hx : x ∈ t
  · simp only [Set.singleton_inter_of_mem hx, hx, ↓reduceIte]
  · simp only [Set.singleton_inter_eq_empty.mpr hx, hx, ↓reduceIte, measureReal_empty, zero_mul]

/-- Every set is measurable on a finite space with measurable points, so the σ-algebra of a
statistic `S` is a sub-σ-algebra. -/
theorem comap_le_of_finite (S : Ω → β) :
    MeasurableSpace.comap S ⊤ ≤ ‹MeasurableSpace Ω› :=
  fun s _ ↦ (Set.toFinite s).measurableSet

omit [Finite Ω] in
/-- **Conditional expectation on a finite space, given a statistic.** Given `S`, the conditional
expectation of `f` is, almost surely, the average of `f` over the fibre `{S = S ω}`, weighted by
the masses of its points. -/
theorem condExp_comap_ae_eq [Fintype Ω] [DecidableEq β] (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : Ω → β) (f : Ω → ℝ) :
    μ[f | MeasurableSpace.comap S ⊤] =ᵐ[μ] fun ω ↦
      (∑ x, if S x = S ω then μ.real {x} * f x else 0) /
        ∑ x, if S x = S ω then μ.real {x} else 0 := by
  have hm := comap_le_of_finite (Ω := Ω) S
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm Integrable.of_finite
    (fun _ _ _ ↦ Integrable.of_finite.integrableOn) ?_ ?_).symm
  · rintro t ⟨B, -, rfl⟩ -
    classical
    rw [setIntegral_eq_sum, setIntegral_eq_sum]
    exact sum_fibre_average (fun x ↦ μ.real {x}) f (fun x ↦ measureReal_nonneg) S B
  · exact (stronglyMeasurable_comp_comap S fun y ↦
      (∑ x, if S x = y then μ.real {x} * f x else 0) /
        ∑ x, if S x = y then μ.real {x} else 0).aestronglyMeasurable

/-- **The Fisher–Neyman factorization theorem, finite form.** On a finite sample space where every
point has positive chance under every `P θ`, a statistic `S` is sufficient if and only if each
chance factors as `P θ {ω} = a θ (S ω) · b ω`: a part that sees the data only through `S`, times a
part that does not depend on `θ`. Given `S = y`, the conditional chance of `ω` is
`b ω / ∑_{S x = y} b x`, the same for every `θ`; and conversely the common conditional chance of
`{ω}` is a valid `b`. -/
theorem isSufficient_iff_factorization {P : Θ → Measure Ω} [∀ θ, IsProbabilityMeasure (P θ)]
    (hpos : ∀ θ ω, 0 < (P θ).real {ω}) (S : Ω → β) :
    IsSufficient P (MeasurableSpace.comap S ⊤) ↔
      ∃ a : Θ → β → ℝ, ∃ b : Ω → ℝ, ∀ θ ω, (P θ).real {ω} = a θ (S ω) * b ω := by
  classical
  have := Fintype.ofFinite Ω
  constructor
  · intro hS
    have hsing := fun ω ↦ hS.2 {ω} (measurableSet_singleton ω)
    choose g _ hg using hsing
    refine ⟨fun θ y ↦ ∑ x, if S x = y then (P θ).real {x} else 0, fun ω ↦ g ω ω,
      fun θ ω ↦ ?_⟩
    have h1 := eq_of_ae_eq_of_pos (hpos θ)
      ((hg ω θ).trans (condExp_comap_ae_eq (P θ) S _))
    have h2 := congrFun h1 ω
    have hnum : (∑ x, if S x = S ω then (P θ).real {x} *
        ({ω} : Set Ω).indicator (fun _ ↦ (1 : ℝ)) x else 0) = (P θ).real {ω} := by
      rw [Finset.sum_eq_single ω]
      · simp
      · intro x _ hx
        simp [hx]
      · simp
    rw [hnum] at h2
    have hD : 0 < ∑ x, if S x = S ω then (P θ).real {x} else 0 := by
      have := Finset.single_le_sum (f := fun x ↦ if S x = S ω then (P θ).real {x} else 0)
        (fun x _ ↦ by split_ifs <;> simp) (Finset.mem_univ ω)
      simp only [↓reduceIte] at this
      linarith [hpos θ ω]
    simp only
    rw [h2]
    field_simp
  · rintro ⟨a, b, hab⟩
    refine ⟨comap_le_of_finite S, fun s _ ↦ ?_⟩
    refine ⟨fun ω ↦ (∑ x, if S x = S ω then b x * s.indicator (fun _ ↦ (1 : ℝ)) x else 0) /
        ∑ x, if S x = S ω then b x else 0,
      stronglyMeasurable_comp_comap S fun y ↦
        (∑ x, if S x = y then b x * s.indicator (fun _ ↦ (1 : ℝ)) x else 0) /
          ∑ x, if S x = y then b x else 0, fun θ ↦ ?_⟩
    refine EventuallyEq.trans ?_ (condExp_comap_ae_eq (P θ) S _).symm
    refine ae_of_all _ fun ω ↦ ?_
    have ha : a θ (S ω) ≠ 0 := by
      intro h0
      have := hpos θ ω
      rw [hab, h0, zero_mul] at this
      exact lt_irrefl 0 this
    have hnum : (∑ x, if S x = S ω then (P θ).real {x} *
        s.indicator (fun _ ↦ (1 : ℝ)) x else 0)
        = a θ (S ω) * ∑ x, if S x = S ω then b x * s.indicator (fun _ ↦ (1 : ℝ)) x else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      by_cases hx : S x = S ω
      · simp only [hx, ↓reduceIte]
        rw [hab, hx]
        ring
      · simp only [hx, ↓reduceIte, mul_zero]
    have hden : (∑ x, if S x = S ω then (P θ).real {x} else 0)
        = a θ (S ω) * ∑ x, if S x = S ω then b x else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      by_cases hx : S x = S ω
      · simp only [hx, ↓reduceIte]
        rw [hab, hx]
      · simp only [hx, ↓reduceIte, mul_zero]
    simp only
    rw [hnum, hden, mul_div_mul_left _ _ ha]

end Finite

section CoinFlips

/-! ### Coin flips -/

open scoped unitInterval

/-- `n` independent flips of a coin with chance `p` of heads: Mathlib's product of `n` copies of
the Bernoulli law on `Bool` (`true` for heads). -/
noncomputable def coinFlips (n : ℕ) (p : I) : Measure (Fin n → Bool) :=
  Measure.pi fun _ ↦ bernoulliMeasure true false p

instance (n : ℕ) (p : I) : IsProbabilityMeasure (coinFlips n p) := by
  unfold coinFlips
  infer_instance

/-- The number of heads. -/
def numHeads {n : ℕ} (ω : Fin n → Bool) : ℕ := (Finset.univ.filter fun i ↦ ω i = true).card

/-- The chance of one sequence of flips is the product of the chances of its flips. -/
theorem coinFlips_real_singleton (n : ℕ) (p : I) (ω : Fin n → Bool) :
    (coinFlips n p).real {ω} = ∏ i, if ω i then (p : ℝ) else 1 - p := by
  rw [← Set.univ_pi_singleton, measureReal_def, coinFlips, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← measureReal_def, bernoulliMeasure_real_apply _ (measurableSet_singleton _)]
  cases ω i <;> simp [unitInterval.coe_symm_eq]

/-- The chance of one sequence of `n` flips with `k` heads is `p^k (1 − p)^(n − k)`. -/
theorem coinFlips_real_singleton_eq_pow (n : ℕ) (p : I) (ω : Fin n → Bool) :
    (coinFlips n p).real {ω} = (p : ℝ) ^ numHeads ω * (1 - p) ^ (n - numHeads ω) := by
  classical
  have htails : (Finset.univ.filter fun i ↦ ¬ ω i = true).card = n - numHeads ω := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i : Fin n ↦ ω i = true)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    simp only [numHeads]
    omega
  rw [coinFlips_real_singleton, Finset.prod_ite, Finset.prod_const, Finset.prod_const, htails]
  rfl

private theorem coinFlips_pos (n : ℕ) (p : Set.Ioo (0 : I) 1) (ω : Fin n → Bool) :
    0 < (coinFlips n p).real {ω} := by
  rw [coinFlips_real_singleton]
  have h0 : (0 : ℝ) < (p : I) := p.2.1
  have h1 : ((p : I) : ℝ) < 1 := p.2.2
  exact Finset.prod_pos fun i _ ↦ by split_ifs <;> linarith

theorem numHeads_le {n : ℕ} (ω : Fin n → Bool) : numHeads ω ≤ n := by
  simpa [numHeads] using Finset.card_filter_le Finset.univ fun i ↦ ω i = true

/-- **The number of heads is sufficient** for `n` coin flips with any chance of heads strictly
between `0` and `1`: the chance of a sequence is `p^k (1 − p)^(n − k)`, a function of the number
of heads `k` alone (Fisher–Neyman, `isSufficient_iff_factorization`, with `b = 1`). -/
theorem isSufficient_numHeads (n : ℕ) :
    IsSufficient (fun p : Set.Ioo (0 : I) 1 ↦ coinFlips n p)
      (MeasurableSpace.comap (numHeads (n := n)) ⊤) :=
  (isSufficient_iff_factorization (fun p ω ↦ coinFlips_pos n p ω) numHeads).mpr
    ⟨fun p k ↦ ((p : I) : ℝ) ^ k * (1 - p) ^ (n - k), fun _ ↦ 1, fun p ω ↦ by
      rw [coinFlips_real_singleton_eq_pow, mul_one]⟩

/-- Relabelling the flips does not change the number of heads. -/
private theorem numHeads_comp_perm {n : ℕ} (e : Equiv.Perm (Fin n)) (ω : Fin n → Bool) :
    numHeads (ω ∘ e) = numHeads ω := by
  classical
  simp only [numHeads, Finset.card_filter]
  exact Equiv.sum_comp e fun i ↦ if ω i = true then 1 else 0

/-- **Rao–Blackwell turns the first flip into the sample mean.** Given the number of heads `k` in
`n + 1` flips, the chance that the first flip is heads is `k / (n + 1)`, whatever `p`: by symmetry
every flip has the same conditional chance, and they add up to `k`. -/
theorem condExp_firstFlip_ae_eq (n : ℕ) (p : I) :
    (coinFlips (n + 1) p)[fun ω ↦ if ω 0 then (1 : ℝ) else 0
        | MeasurableSpace.comap (numHeads (n := n + 1)) ⊤]
      =ᵐ[coinFlips (n + 1) p] fun ω ↦ (numHeads ω : ℝ) / (n + 1) := by
  classical
  set μ := coinFlips (n + 1) p
  set w : (Fin (n + 1) → Bool) → ℝ := fun x ↦ μ.real {x}
  have hw : ∀ x, w x = ∏ j, if x j then (p : ℝ) else 1 - p := coinFlips_real_singleton _ p
  -- the weighted count of sequences with `k` heads and flip `i` a head is the same for every `i`
  set N : Fin (n + 1) → ℕ → ℝ := fun i k ↦
    ∑ x, if numHeads x = k then w x * (if x i then 1 else 0) else 0
  have hsymm : ∀ i k, N i k = N 0 k := by
    intro i k
    let sw := Equiv.swap (0 : Fin (n + 1)) i
    let e : (Fin (n + 1) → Bool) ≃ (Fin (n + 1) → Bool) :=
      { toFun := fun x ↦ x ∘ sw, invFun := fun x ↦ x ∘ sw,
        left_inv := fun x ↦ by ext j; simp [sw, Equiv.swap_apply_self],
        right_inv := fun x ↦ by ext j; simp [sw, Equiv.swap_apply_self] }
    simp only [N]
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have h1 : numHeads (e x) = numHeads x := numHeads_comp_perm sw x
    have h2 : w (e x) = w x := by
      rw [hw, hw]
      exact Equiv.prod_comp sw fun j ↦ if x j then (p : ℝ) else 1 - p
    have h3 : (e x) i = x 0 := by simp [e, sw]
    rw [h1, h2, h3]
  set D : ℕ → ℝ := fun k ↦ ∑ x, if numHeads x = k then w x else 0
  have hsumN : ∀ k, ∑ i, N i k = k * D k := by
    intro k
    simp only [N, D]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases hx : numHeads x = k
    · simp only [hx, ↓reduceIte]
      rw [← Finset.mul_sum, mul_comm]
      congr 1
      rw [← hx, numHeads, Finset.card_filter]
      push_cast
      rfl
    · simp [hx]
  have hND : ∀ k, (n + 1 : ℝ) * N 0 k = k * D k := by
    intro k
    rw [← hsumN, Finset.sum_congr rfl fun i _ ↦ hsymm i k]
    simp
  refine (condExp_comap_ae_eq μ numHeads _).trans ?_
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro ω hω
  have hwpos : 0 < w ω := by
    have := measureReal_nonneg (μ := μ) (s := {ω})
    rcases this.eq_or_lt with h | h
    · exfalso
      apply hω
      rw [measureReal_def] at h
      exact (ENNReal.toReal_eq_zero_iff _).mp h.symm |>.resolve_right (measure_ne_top _ _)
    · exact h
  have hDpos : 0 < D (numHeads ω) := by
    have := Finset.single_le_sum (f := fun x ↦ if numHeads x = numHeads ω then w x else 0)
      (fun x _ ↦ by split_ifs <;> simp [w]) (Finset.mem_univ ω)
    simp only [↓reduceIte] at this
    exact lt_of_lt_of_le hwpos this
  have hN := hND (numHeads ω)
  change N 0 (numHeads ω) / D (numHeads ω) = _
  rw [div_eq_div_iff hDpos.ne' (by positivity)]
  linarith

/-- **The sample mean has smaller mean squared error than the first flip**:
`E[(k/(n + 1) − p)²] ≤ E[(first flip − p)²]`, from order LEAN-19's conditioning inequality and
`condExp_firstFlip_ae_eq`. -/
theorem integral_sampleMean_sub_sq_le (n : ℕ) (p : I) :
    ∫ ω, ((numHeads ω : ℝ) / (n + 1) - p) ^ 2 ∂coinFlips (n + 1) p
      ≤ ∫ ω, ((if ω 0 then (1 : ℝ) else 0) - p) ^ 2 ∂coinFlips (n + 1) p := by
  have h := integral_sq_condExp_sub_le (μ := coinFlips (n + 1) p)
    (comap_le_of_finite (numHeads (n := n + 1)))
    (T := fun ω ↦ if ω 0 then (1 : ℝ) else 0) MemLp.of_discrete (p : ℝ)
  have hc := condExp_firstFlip_ae_eq n p
  set g := (coinFlips (n + 1) p)[fun ω ↦ if ω 0 then (1 : ℝ) else 0
    | MeasurableSpace.comap (numHeads (n := n + 1)) ⊤]
  have he : ∫ ω, (g ω - p) ^ 2 ∂coinFlips (n + 1) p
      = ∫ ω, ((numHeads ω : ℝ) / (n + 1) - p) ^ 2 ∂coinFlips (n + 1) p :=
    integral_congr_ae (by filter_upwards [hc] with ω hω; rw [hω])
  rwa [he] at h

/-! ### Item 61: the number of heads is complete -/

/-- **The number of heads is complete** for `n` coin flips with chance of heads ranging over
`(0, 1)`: a function `g` of the number of heads with `E g = 0` for every such chance is `0`.
`E g = ∑_k G_k p^k (1 − p)^(n − k)`, where `G_k` sums `g` over the sequences with `k` heads;
dividing by `(1 − p)^n` and putting `r = p / (1 − p)` gives a polynomial `∑ G_k r^k` with a root
at every `r > 0`, so it is `0`, and each `G_k` is `0`. -/
theorem isComplete_numHeads (n : ℕ) :
    IsComplete (fun p : Set.Ioo (0 : I) 1 ↦ coinFlips n p)
      (MeasurableSpace.comap (numHeads (n := n)) ⊤) := by
  classical
  intro f hf _ hmean θ
  -- `f` is constant on each set of sequences with the same number of heads
  have hconst : ∀ ω ω', numHeads ω' = numHeads ω → f ω' = f ω := by
    intro ω ω' h
    obtain ⟨B, -, hB⟩ := hf.measurable (measurableSet_singleton (f ω))
    have hω : ω ∈ numHeads ⁻¹' B := by rw [hB]; rfl
    have hω' : ω' ∈ numHeads ⁻¹' B := by simpa [Set.mem_preimage, h] using hω
    rw [hB] at hω'
    exact hω'
  set G : ℕ → ℝ := fun k ↦ ∑ x ∈ Finset.univ.filter (fun x ↦ numHeads x = k), f x
  -- the mean of `f` as a sum over the number of heads
  have hmeanG : ∀ q : Set.Ioo (0 : I) 1, ∫ ω, f ω ∂coinFlips n q
      = ∑ k ∈ Finset.range (n + 1), ((q : I) : ℝ) ^ k * (1 - q) ^ (n - k) * G k := by
    intro q
    rw [integral_fintype Integrable.of_finite]
    simp_rw [coinFlips_real_singleton_eq_pow, smul_eq_mul]
    rw [← Finset.sum_fiberwise_of_maps_to (g := numHeads) (t := Finset.range (n + 1))
      fun x _ ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le (numHeads_le x))]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [(Finset.mem_filter.mp hx).2]
  set Q : Polynomial ℝ := ∑ k ∈ Finset.range (n + 1), Polynomial.C (G k) * Polynomial.X ^ k
  have hroot : ∀ r : ℝ, 0 < r → Q.IsRoot r := by
    intro r hr
    set q : ℝ := r / (1 + r)
    have hq0 : 0 < q := div_pos hr (by linarith)
    have hq1 : q < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    let θ' : Set.Ioo (0 : I) 1 := ⟨⟨q, hq0.le, hq1.le⟩, hq0, hq1⟩
    have h0 := hmean θ'
    rw [hmeanG θ'] at h0
    have hterm : ∀ k ∈ Finset.range (n + 1),
        (1 + r) ^ n * (q ^ k * (1 - q) ^ (n - k) * G k) = G k * r ^ k := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have h1r : (1 + r) ≠ 0 := by positivity
      have hsplit : (1 + r) ^ n = (1 + r) ^ k * (1 + r) ^ (n - k) := by
        rw [← pow_add, Nat.add_sub_cancel' hkn]
      have hq : (1 + r) * q = r := by simp only [q]; field_simp
      have h1q : (1 + r) * (1 - q) = 1 := by simp only [q]; field_simp; ring
      rw [hsplit]
      calc (1 + r) ^ k * (1 + r) ^ (n - k) * (q ^ k * (1 - q) ^ (n - k) * G k)
          = ((1 + r) * q) ^ k * ((1 + r) * (1 - q)) ^ (n - k) * G k := by
            rw [mul_pow, mul_pow]
            ring
        _ = G k * r ^ k := by rw [hq, h1q, one_pow]; ring
    have heval : Q.eval r = (1 + r) ^ n *
        ∑ k ∈ Finset.range (n + 1), q ^ k * (1 - q) ^ (n - k) * G k := by
      simp only [Q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k hk ↦ (hterm k hk).symm
    change Q.eval r = 0
    rw [heval]
    have : (∑ k ∈ Finset.range (n + 1), q ^ k * (1 - q) ^ (n - k) * G k) = 0 := h0
    rw [this, mul_zero]
  have hQ : Q = 0 := Polynomial.eq_zero_of_infinite_isRoot Q
    ((Set.Ioi_infinite (0 : ℝ)).mono fun r hr ↦ hroot r hr)
  have hG : ∀ k ≤ n, G k = 0 := by
    intro k hk
    have := congrArg (fun P : Polynomial ℝ ↦ P.coeff k) hQ
    simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at this
    rw [Finset.sum_ite_eq (Finset.range (n + 1)) k] at this
    simpa [Finset.mem_range, Nat.lt_succ_of_le hk] using this
  refine ae_of_all _ fun ω ↦ ?_
  have h0 := hG (numHeads ω) (numHeads_le ω)
  have hGω : G (numHeads ω)
      = (Finset.univ.filter fun x : Fin n → Bool ↦ numHeads x = numHeads ω).card * f ω := by
    simp only [G]
    rw [Finset.sum_congr rfl fun x hx ↦ hconst ω x (Finset.mem_filter.mp hx).2,
      Finset.sum_const, nsmul_eq_mul]
  have hcard : 0 < (Finset.univ.filter fun x : Fin n → Bool ↦ numHeads x = numHeads ω).card :=
    Finset.card_pos.mpr ⟨ω, Finset.mem_filter.mpr ⟨Finset.mem_univ ω, rfl⟩⟩
  rw [hGω] at h0
  rw [Pi.zero_apply]
  simpa [hcard.ne'] using h0

/-- The first flip has mean `p`. -/
private theorem integral_firstFlip (n : ℕ) (p : I) :
    ∫ ω, (if ω 0 then (1 : ℝ) else 0) ∂coinFlips (n + 1) p = p := by
  have hmap := (measurePreserving_eval (μ := fun _ : Fin (n + 1) ↦
    bernoulliMeasure true false p) 0).map_eq
  have := integral_map (μ := coinFlips (n + 1) p) (φ := fun ω : Fin (n + 1) → Bool ↦ ω 0)
    (f := fun b : Bool ↦ if b then (1 : ℝ) else 0) (measurable_pi_apply 0).aemeasurable
    (measurable_of_finite _).aestronglyMeasurable
  rw [← this]
  unfold coinFlips
  rw [hmap, integral_bernoulliMeasure]
  simp

/-- **The sample mean is the least-variance unbiased estimator of `p`** (Lehmann–Scheffé on
coin flips): for `n + 1` flips, every `T` with mean `p` under every `p ∈ (0, 1)` has variance at
least that of the sample mean, under every `p`. -/
theorem variance_sampleMean_le (n : ℕ) {T : (Fin (n + 1) → Bool) → ℝ}
    (hT : ∀ p : Set.Ioo (0 : I) 1, ∫ ω, T ω ∂coinFlips (n + 1) p = p) (p : Set.Ioo (0 : I) 1) :
    Var[fun ω ↦ (numHeads ω : ℝ) / (n + 1); coinFlips (n + 1) p]
      ≤ Var[T; coinFlips (n + 1) p] := by
  refine variance_le_of_isSufficient_of_isComplete (P := fun p : Set.Ioo (0 : I) 1 ↦
      coinFlips (n + 1) p) (isSufficient_numHeads (n + 1))
    (isComplete_numHeads (n + 1)) (τ := fun p ↦ ((p : I) : ℝ))
    (stronglyMeasurable_comp_comap numHeads fun k ↦ (k : ℝ) / (n + 1))
    (fun _ ↦ Integrable.of_finite) (fun q ↦ ?_) (measurable_of_finite T).stronglyMeasurable
    (fun _ ↦ MemLp.of_discrete) hT p
  rw [← integral_congr_ae (condExp_firstFlip_ae_eq n q),
    integral_condExp (comap_le_of_finite numHeads), integral_firstFlip]

/-- **And it is the only one**: an estimator `T` with mean `p` under every `p ∈ (0, 1)` and the
same variance as the sample mean under one `p` is the sample mean. (Every sequence of flips has
positive chance, so "almost surely" is "everywhere".) -/
theorem eq_sampleMean_of_variance_eq (n : ℕ) {T : (Fin (n + 1) → Bool) → ℝ}
    (hT : ∀ p : Set.Ioo (0 : I) 1, ∫ ω, T ω ∂coinFlips (n + 1) p = p) (p : Set.Ioo (0 : I) 1)
    (hvar : Var[T; coinFlips (n + 1) p]
      = Var[fun ω ↦ (numHeads ω : ℝ) / (n + 1); coinFlips (n + 1) p]) :
    T = fun ω ↦ (numHeads ω : ℝ) / (n + 1) := by
  refine eq_of_ae_eq_of_pos (coinFlips_pos (n + 1) p) ?_
  refine ae_eq_of_variance_eq_of_isSufficient_of_isComplete (P := fun p : Set.Ioo (0 : I) 1 ↦
      coinFlips (n + 1) p) (isSufficient_numHeads (n + 1))
    (isComplete_numHeads (n + 1)) (τ := fun p ↦ ((p : I) : ℝ))
    (stronglyMeasurable_comp_comap numHeads fun k ↦ (k : ℝ) / (n + 1))
    (fun _ ↦ Integrable.of_finite) (fun q ↦ ?_) (measurable_of_finite T).stronglyMeasurable
    (fun _ ↦ MemLp.of_discrete) hT p hvar
  rw [← integral_congr_ae (condExp_firstFlip_ae_eq n q),
    integral_condExp (comap_le_of_finite numHeads), integral_firstFlip]

end CoinFlips

end ClassicalLean.Statistics

open MeasureTheory ClassicalLean.Statistics in
/-- The hypotheses of `IsSufficient.exists_condExp_eq` hold together: two flips of a coin with
chance `p` of heads, for every `p` strictly between `0` and `1` (the family `coinFlips 2 p`), and
the number of heads, sufficient by the module's `isSufficient_numHeads`; the statistic `T` is `1`
when the first flip is heads and `0` otherwise, measurable and integrable on the finite space. -/
example := ClassicalLean.Statistics.IsSufficient.exists_condExp_eq
  (P := fun p : Set.Ioo (0 : unitInterval) 1 ↦ coinFlips 2 p)
  (m := MeasurableSpace.comap (numHeads (n := 2)) ⊤) (isSufficient_numHeads 2)
  (T := fun ω ↦ if ω 0 then 1 else 0) (measurable_of_countable _).stronglyMeasurable
  (fun _ ↦ Integrable.of_finite)

open MeasureTheory ClassicalLean.Statistics in
/-- The hypotheses of `IsSufficient.raoBlackwell` hold together: two flips of a coin with chance
`p` of heads, for every `p` strictly between `0` and `1`, each a probability measure, and the
number of heads, sufficient by the module's `isSufficient_numHeads`; the estimator `T` is `1` when
the first flip is heads and `0` otherwise, measurable and bounded, so square integrable. -/
example := ClassicalLean.Statistics.IsSufficient.raoBlackwell
  (P := fun p : Set.Ioo (0 : unitInterval) 1 ↦ coinFlips 2 p)
  (m := MeasurableSpace.comap (numHeads (n := 2)) ⊤) (isSufficient_numHeads 2)
  (T := fun ω ↦ if ω 0 then 1 else 0) (measurable_of_countable _).stronglyMeasurable
  (fun _ ↦ MemLp.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω ↦ by split_ifs <;> simp))

open MeasureTheory ClassicalLean.Statistics in
/-- The hypotheses of `isSufficient_iff_factorization` hold together: two flips of a coin with
chance `p` of heads, for every `p` strictly between `0` and `1`, each a probability measure, give
every sequence the positive chance `p ^ k (1 − p) ^ (2 − k)`, `k` its number of heads; the statistic
is the number of heads. -/
example := ClassicalLean.Statistics.isSufficient_iff_factorization
  (P := fun p : Set.Ioo (0 : unitInterval) 1 ↦ coinFlips 2 p)
  (fun p ω ↦ by
    rw [coinFlips_real_singleton_eq_pow]
    have h0 : (0 : ℝ) < (p : unitInterval) := p.2.1
    have h1 : ((p : unitInterval) : ℝ) < 1 := p.2.2
    have : (0 : ℝ) < 1 - (p : unitInterval) := by linarith
    positivity)
  (S := numHeads (n := 2))

open MeasureTheory ClassicalLean.Statistics in
/-- The hypotheses of `variance_le_of_isSufficient_of_isComplete` hold together: two flips of a
coin with chance `p` of heads, for every `p` strictly between `0` and `1`, each a probability
measure; the number of heads, sufficient and complete (the module's `isSufficient_numHeads` and
`isComplete_numHeads`); the sample mean `U`, half the number of heads, a function of it, bounded,
of mean `p`; the first flip `T` (`1` for heads), bounded, also of mean `p`; `τ p = p`, at
`p = 1/2`. -/
example := ClassicalLean.Statistics.variance_le_of_isSufficient_of_isComplete
  (P := fun p : Set.Ioo (0 : unitInterval) 1 ↦ coinFlips 2 p)
  (m := MeasurableSpace.comap (numHeads (n := 2)) ⊤) (isSufficient_numHeads 2)
  (isComplete_numHeads 2) (U := fun ω ↦ (numHeads ω : ℝ) / 2)
  (T := fun ω ↦ if ω 0 then 1 else 0) (τ := fun p ↦ ((p : unitInterval) : ℝ))
  ((measurable_of_countable fun k : ℕ ↦ (k : ℝ) / 2).comp
    (comap_measurable numHeads)).stronglyMeasurable
  (fun _ ↦ Integrable.of_finite)
  (fun p ↦ by
    rw [integral_fintype Integrable.of_finite, show (Finset.univ : Finset (Fin 2 → Bool)) =
      {![true, true], ![true, false], ![false, true], ![false, false]} by decide]
    simp [coinFlips_real_singleton, Fin.prod_univ_two,
      show numHeads ![true, true] = 2 by decide, show numHeads ![true, false] = 1 by decide,
      show numHeads ![false, true] = 1 by decide, show numHeads ![false, false] = 0 by decide]
    ring)
  (measurable_of_countable _).stronglyMeasurable
  (fun _ ↦ MemLp.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω ↦ by split_ifs <;> simp))
  (fun p ↦ by
    rw [integral_fintype Integrable.of_finite, show (Finset.univ : Finset (Fin 2 → Bool)) =
      {![true, true], ![true, false], ![false, true], ![false, false]} by decide]
    simp [coinFlips_real_singleton, Fin.prod_univ_two]
    ring)
  (θ := ⟨⟨1 / 2, by norm_num, by norm_num⟩, by
    constructor <;> norm_num [← Subtype.coe_lt_coe]⟩)

open MeasureTheory ProbabilityTheory ClassicalLean.Statistics in
/-- The hypotheses of `indepFun_of_isComplete_of_ancillary` hold together: a coin with chance `p`
of heads, for every `p` strictly between `0` and `1`, flipped beside a fair coin, so every one of
the four outcomes has positive chance; the first coin `S`, sufficient (the chance of an outcome is
the first coin's chance times the second's) and complete (a mean of `0` at `p = 1/2` and `p = 1/4`
forces a function of `S` to be `0`); the second coin `A`, measurable, not constant, its law the
fair coin's for every `p`; `θ = 1/2`. (The model is the group 9 reviewer's.) -/
example := ClassicalLean.Statistics.indepFun_of_isComplete_of_ancillary
  (P := fun p : Set.Ioo (0 : unitInterval) 1 ↦ (bernoulliMeasure true false (p : unitInterval)).prod
    (bernoulliMeasure true false (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)))
  (S := Prod.fst)
  (by
    have ber : ∀ (q : unitInterval) (x : Bool),
        (bernoulliMeasure true false q).real {x} = if x then (q : ℝ) else 1 - q := by
      intro q x
      rw [bernoulliMeasure_real_apply q (measurableSet_singleton x)]
      cases x <;> simp [unitInterval.coe_symm_eq]
    have Qreal : ∀ (p : Set.Ioo (0 : unitInterval) 1) (ω : Bool × Bool),
        ((bernoulliMeasure true false (p : unitInterval)).prod (bernoulliMeasure true false
          (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval))).real {ω} =
        (bernoulliMeasure true false (p : unitInterval)).real {ω.1} *
          (bernoulliMeasure true false (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)).real
            {ω.2} := by
      rintro p ⟨a, b⟩
      rw [← Set.singleton_prod_singleton, measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]
      rfl
    refine (isSufficient_iff_factorization (fun p ω ↦ ?_) (S := Prod.fst)).mpr
      ⟨fun p x ↦ (bernoulliMeasure true false (p : unitInterval)).real {x},
        fun ω ↦ (bernoulliMeasure true false
          (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)).real {ω.2}, fun p ω ↦ Qreal p ω⟩
    have h0 : (0 : ℝ) < (p : unitInterval) := p.2.1
    have h1 : ((p : unitInterval) : ℝ) < 1 := p.2.2
    obtain ⟨a, b⟩ := ω
    rw [Qreal, ber, ber]
    change 0 < (if a then _ else _) * (if b then (1 / 2 : ℝ) else 1 - 1 / 2)
    cases a <;> cases b <;> simp only [↓reduceIte, Bool.false_eq_true] <;> nlinarith)
  (by
    have ber : ∀ (q : unitInterval) (x : Bool),
        (bernoulliMeasure true false q).real {x} = if x then (q : ℝ) else 1 - q := by
      intro q x
      rw [bernoulliMeasure_real_apply q (measurableSet_singleton x)]
      cases x <;> simp [unitInterval.coe_symm_eq]
    have Qreal : ∀ (p : Set.Ioo (0 : unitInterval) 1) (ω : Bool × Bool),
        ((bernoulliMeasure true false (p : unitInterval)).prod (bernoulliMeasure true false
          (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval))).real {ω} =
        (bernoulliMeasure true false (p : unitInterval)).real {ω.1} *
          (bernoulliMeasure true false (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)).real
            {ω.2} := by
      rintro p ⟨a, b⟩
      rw [← Set.singleton_prod_singleton, measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]
      rfl
    intro f hf _ hmean θ
    have hconst : ∀ ω ω' : Bool × Bool, ω'.1 = ω.1 → f ω' = f ω := by
      intro ω ω' h
      obtain ⟨B, -, hB⟩ := hf.measurable (measurableSet_singleton (f ω))
      have hω : ω ∈ Prod.fst ⁻¹' B := by rw [hB]; rfl
      have hω' : ω' ∈ Prod.fst ⁻¹' B := by simpa [Set.mem_preimage, h] using hω
      rw [hB] at hω'
      exact hω'
    have hform : ∀ p : Set.Ioo (0 : unitInterval) 1,
        ∫ ω, f ω ∂((bernoulliMeasure true false (p : unitInterval)).prod
          (bernoulliMeasure true false (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval))) =
        ((p : unitInterval) : ℝ) * f (true, true) + (1 - (p : unitInterval)) * f (false, true) := by
      intro p
      rw [integral_fintype Integrable.of_finite]
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, smul_eq_mul, Qreal, ber,
        ↓reduceIte, Bool.false_eq_true, hconst (true, true) (true, false) rfl,
        hconst (false, true) (false, false) rfl]
      change (p : ℝ) * (1 / 2) * f (true, true) + (p : ℝ) * (1 - 1 / 2) * f (true, true) +
        ((1 - p) * (1 / 2) * f (false, true) + (1 - p) * (1 - 1 / 2) * f (false, true)) = _
      ring
    have e1 := (hform ⟨⟨1 / 2, by norm_num, by norm_num⟩, by
      constructor <;> norm_num [← Subtype.coe_lt_coe]⟩).symm.trans (hmean _)
    have e2 := (hform ⟨⟨1 / 4, by norm_num, by norm_num⟩, by
      constructor <;> norm_num [← Subtype.coe_lt_coe]⟩).symm.trans (hmean _)
    change (1 / 2 : ℝ) * f (true, true) + (1 - 1 / 2) * f (false, true) = 0 at e1
    change (1 / 4 : ℝ) * f (true, true) + (1 - 1 / 4) * f (false, true) = 0 at e2
    have ht : f (true, true) = 0 := by linarith
    have hf' : f (false, true) = 0 := by linarith
    refine ae_of_all _ fun ω ↦ ?_
    obtain ⟨a, b⟩ := ω
    cases a
    · rw [hconst (false, true) (false, b) rfl, hf']; rfl
    · rw [hconst (true, true) (true, b) rfl, ht]; rfl)
  (A := Prod.snd) measurable_snd
  (fun θ θ' ↦ by simp only [Measure.map_snd_prod, measure_univ, one_smul])
  (θ := ⟨⟨1 / 2, by norm_num, by norm_num⟩, by constructor <;> norm_num [← Subtype.coe_lt_coe]⟩)

open MeasureTheory ClassicalLean.Statistics in
/-- The hypotheses of `eq_sampleMean_of_variance_eq` hold together: two flips (`n + 1 = 2`) of a
coin with chance `p` of heads; the estimator `T`, half the number of heads, has mean `p` for every
`p` strictly between `0` and `1` (computed over the four sequences); at `p = 1/2` its variance
equals the sample mean's, since it is the sample mean, the only estimator the theorem allows. -/
example := ClassicalLean.Statistics.eq_sampleMean_of_variance_eq (n := 1)
  (T := fun ω ↦ (numHeads ω : ℝ) / 2)
  (fun p ↦ by
    rw [integral_fintype Integrable.of_finite, show (Finset.univ : Finset (Fin 2 → Bool)) =
      {![true, true], ![true, false], ![false, true], ![false, false]} by decide]
    simp [coinFlips_real_singleton, Fin.prod_univ_two,
      show numHeads ![true, true] = 2 by decide, show numHeads ![true, false] = 1 by decide,
      show numHeads ![false, true] = 1 by decide, show numHeads ![false, false] = 0 by decide]
    ring)
  (p := ⟨⟨1 / 2, by norm_num, by norm_num⟩, by constructor <;> norm_num [← Subtype.coe_lt_coe]⟩)
  (by norm_num)

open MeasureTheory ClassicalLean.Statistics in
/-- The hypotheses of `variance_sampleMean_le` hold together: two flips (`n + 1 = 2`) of a coin with
chance `p` of heads; the estimator `T`, `1` when the first flip is heads and `0` otherwise, has mean
`p` for every `p` strictly between `0` and `1` (computed over the four sequences); `p = 1/2`. -/
example := ClassicalLean.Statistics.variance_sampleMean_le (n := 1)
  (T := fun ω ↦ if ω 0 then 1 else 0)
  (fun p ↦ by
    rw [integral_fintype Integrable.of_finite, show (Finset.univ : Finset (Fin 2 → Bool)) =
      {![true, true], ![true, false], ![false, true], ![false, false]} by decide]
    simp [coinFlips_real_singleton, Fin.prod_univ_two]
    ring)
  (p := ⟨⟨1 / 2, by norm_num, by norm_num⟩, by constructor <;> norm_num [← Subtype.coe_lt_coe]⟩)

open MeasureTheory ClassicalLean.Statistics in
/-- The hypotheses of `IsComplete.isBoundedlyComplete` hold together: two flips of a coin with
chance `p` of heads, for every `p` strictly between `0` and `1` (a family that depends on `p`);
the σ-algebra of the number of heads, a sub-σ-algebra because the space is finite
(`comap_le_of_finite`), and complete (`isComplete_numHeads`). -/
example := ClassicalLean.Statistics.IsComplete.isBoundedlyComplete
  (P := fun p : Set.Ioo (0 : unitInterval) 1 ↦ coinFlips 2 p)
  (m := MeasurableSpace.comap (numHeads (n := 2)) ⊤)
  (comap_le_of_finite numHeads) (isComplete_numHeads 2)

open MeasureTheory ProbabilityTheory ClassicalLean.Statistics in
/-- The hypotheses of `indep_of_isSufficient_of_isBoundedlyComplete_of_isAncillary` hold together:
the module's Basu model, a coin with chance `p` of heads, for every `p` strictly between `0` and
`1`, flipped beside a fair coin, so every one of the four outcomes has positive chance; `m` the
σ-algebra of the first coin, sufficient (the chance of an outcome is the first coin's chance times
the second's) and complete (a mean of `0` at `p = 1/2` and `p = 1/4` forces a function of the
first coin to be `0`), so boundedly complete (`IsComplete.isBoundedlyComplete`); the second coin
`A`, measurable, not constant, its law the fair coin's for every `p`; `θ = 1/2`. -/
example := ClassicalLean.Statistics.indep_of_isSufficient_of_isBoundedlyComplete_of_isAncillary
  (P := fun p : Set.Ioo (0 : unitInterval) 1 ↦ (bernoulliMeasure true false (p : unitInterval)).prod
    (bernoulliMeasure true false (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)))
  (m := MeasurableSpace.comap Prod.fst inferInstance)
  (by
    have ber : ∀ (q : unitInterval) (x : Bool),
        (bernoulliMeasure true false q).real {x} = if x then (q : ℝ) else 1 - q := by
      intro q x
      rw [bernoulliMeasure_real_apply q (measurableSet_singleton x)]
      cases x <;> simp [unitInterval.coe_symm_eq]
    have Qreal : ∀ (p : Set.Ioo (0 : unitInterval) 1) (ω : Bool × Bool),
        ((bernoulliMeasure true false (p : unitInterval)).prod (bernoulliMeasure true false
          (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval))).real {ω} =
        (bernoulliMeasure true false (p : unitInterval)).real {ω.1} *
          (bernoulliMeasure true false (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)).real
            {ω.2} := by
      rintro p ⟨a, b⟩
      rw [← Set.singleton_prod_singleton, measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]
      rfl
    refine (isSufficient_iff_factorization (fun p ω ↦ ?_) (S := Prod.fst)).mpr
      ⟨fun p x ↦ (bernoulliMeasure true false (p : unitInterval)).real {x},
        fun ω ↦ (bernoulliMeasure true false
          (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)).real {ω.2}, fun p ω ↦ Qreal p ω⟩
    have h0 : (0 : ℝ) < (p : unitInterval) := p.2.1
    have h1 : ((p : unitInterval) : ℝ) < 1 := p.2.2
    obtain ⟨a, b⟩ := ω
    rw [Qreal, ber, ber]
    change 0 < (if a then _ else _) * (if b then (1 / 2 : ℝ) else 1 - 1 / 2)
    cases a <;> cases b <;> simp only [↓reduceIte, Bool.false_eq_true] <;> nlinarith)
  (IsComplete.isBoundedlyComplete measurable_fst.comap_le (by
    have ber : ∀ (q : unitInterval) (x : Bool),
        (bernoulliMeasure true false q).real {x} = if x then (q : ℝ) else 1 - q := by
      intro q x
      rw [bernoulliMeasure_real_apply q (measurableSet_singleton x)]
      cases x <;> simp [unitInterval.coe_symm_eq]
    have Qreal : ∀ (p : Set.Ioo (0 : unitInterval) 1) (ω : Bool × Bool),
        ((bernoulliMeasure true false (p : unitInterval)).prod (bernoulliMeasure true false
          (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval))).real {ω} =
        (bernoulliMeasure true false (p : unitInterval)).real {ω.1} *
          (bernoulliMeasure true false (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)).real
            {ω.2} := by
      rintro p ⟨a, b⟩
      rw [← Set.singleton_prod_singleton, measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]
      rfl
    intro f hf _ hmean θ
    have hconst : ∀ ω ω' : Bool × Bool, ω'.1 = ω.1 → f ω' = f ω := by
      intro ω ω' h
      obtain ⟨B, -, hB⟩ := hf.measurable (measurableSet_singleton (f ω))
      have hω : ω ∈ Prod.fst ⁻¹' B := by rw [hB]; rfl
      have hω' : ω' ∈ Prod.fst ⁻¹' B := by simpa [Set.mem_preimage, h] using hω
      rw [hB] at hω'
      exact hω'
    have hform : ∀ p : Set.Ioo (0 : unitInterval) 1,
        ∫ ω, f ω ∂((bernoulliMeasure true false (p : unitInterval)).prod
          (bernoulliMeasure true false (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval))) =
        ((p : unitInterval) : ℝ) * f (true, true) + (1 - (p : unitInterval)) * f (false, true) := by
      intro p
      rw [integral_fintype Integrable.of_finite]
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, smul_eq_mul, Qreal, ber,
        ↓reduceIte, Bool.false_eq_true, hconst (true, true) (true, false) rfl,
        hconst (false, true) (false, false) rfl]
      change (p : ℝ) * (1 / 2) * f (true, true) + (p : ℝ) * (1 - 1 / 2) * f (true, true) +
        ((1 - p) * (1 / 2) * f (false, true) + (1 - p) * (1 - 1 / 2) * f (false, true)) = _
      ring
    have e1 := (hform ⟨⟨1 / 2, by norm_num, by norm_num⟩, by
      constructor <;> norm_num [← Subtype.coe_lt_coe]⟩).symm.trans (hmean _)
    have e2 := (hform ⟨⟨1 / 4, by norm_num, by norm_num⟩, by
      constructor <;> norm_num [← Subtype.coe_lt_coe]⟩).symm.trans (hmean _)
    change (1 / 2 : ℝ) * f (true, true) + (1 - 1 / 2) * f (false, true) = 0 at e1
    change (1 / 4 : ℝ) * f (true, true) + (1 - 1 / 4) * f (false, true) = 0 at e2
    have ht : f (true, true) = 0 := by linarith
    have hf' : f (false, true) = 0 := by linarith
    refine ae_of_all _ fun ω ↦ ?_
    obtain ⟨a, b⟩ := ω
    cases a
    · rw [hconst (false, true) (false, b) rfl, hf']; rfl
    · rw [hconst (true, true) (true, b) rfl, ht]; rfl))
  (A := Prod.snd) measurable_snd
  (fun θ θ' ↦ by simp only [Measure.map_snd_prod, measure_univ, one_smul])
  (θ := ⟨⟨1 / 2, by norm_num, by norm_num⟩, by constructor <;> norm_num [← Subtype.coe_lt_coe]⟩)
