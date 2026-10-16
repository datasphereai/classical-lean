/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.UniformOn

/-!
# The step-down procedure of Holm

There are tests indexed by a finite type `ι`, with p-values `x j`, and a level `q`. Holm's
procedure sorts the p-values, `x₍₁₎ ≤ ⋯ ≤ x₍ₘ₎`, and rejects the hypotheses with the `k`
smallest, for the largest `k` such that `x₍ᵣ₎ ≤ q / (m − r + 1)` for every `r ≤ k`.

* `holmRejected q x i` — Holm's rule written without sorting: hypothesis `i` is rejected when
  every p-value `x j` at most `x i` is at most `q` divided by the number of p-values at least
  `x j`. For the first rank `r` that `x j` takes, that number is `m − r + 1`, so ties get Holm's
  strictest threshold and a tied group is rejected together, as Holm's sorted rule does (order
  LEAN-31's exact check `105.sorted`: every vector of up to four p-values on a grid with ties, at
  four levels). The count is at least `1` (it counts `j` itself), so no `x / 0` arises.
* `measureReal_exists_holmRejected_true_le` — order LEAN-31, item 105 of MATH-PLAN-library-2:
  if every true null's p-value is valid, `μ {P i ≤ u} ≤ u` for every `u ≥ 0`, the chance that
  Holm's procedure rejects some true null is at most `q`, whatever the dependence between the
  p-values. With `h` true nulls and `ω` in that event, the smallest true-null p-value is rejected
  too, at most `q / c` where `c` counts the p-values at least it; every true null is among them,
  so `h ≤ c` and the event lies inside `⋃ i ∈ H, {P i ≤ q / h}`, whose measure is at most
  `h · (q / h) = q`. **Wider than the plan's reading:** any finite measure, not only a
  probability measure (order LEAN-31's ruling).

`ClassicalLean.Probability.StepUpProcedure` beside this module is the Benjamini–Hochberg step-up
procedure; neither imports the other.

## Hypotheses

With any one hypothesis dropped, the theorem fails (order LEAN-31's exact checks, lane
`lean/LEAN-31-checks.py`, exact fractions):

* `0 ≤ q` (`105.drop.hq`): with no true null the event is empty, of measure `0`, and `q = −1`.
* validity of the true nulls' p-values (`105.drop.valid`): one point, `x = 0`, one true null,
  `q = 1/2`: it is rejected, chance `1 > 1/2`.
* the finite measure (`105.drop.finite`, the arithmetic; the case by hand): the counting measure
  on `ℕ`, two p-values, the true null's `3/4` on the points `0` and `1` and the other's `0` there,
  `3/4` and `5` elsewhere: validity holds because every set `{x₀ ≤ u}` is empty or all of `ℕ`,
  whose measure is `∞` and whose real value is Lean's `0`; the event holds at exactly the two
  points, so its real measure is `2 > 1 = q`. Junk value: `μ.real` of a set of infinite measure
  is `0`.

Validity is asked for `u ≥ 0` only: for `u < 0` it would ask a chance to be negative, so no
measure meets it; for a probability measure it is the same as asking it for `u` in `[0, 1]`; for a
finite measure of mass above `1` the part `u > 1` is needed (by hand: one point of mass `2`, one
test, `H = {0}`, `P 0 = 6/5`, `q = 3/2`: validity holds for every `u` in `[0, 1]` but not at
`u = 6/5`, and Holm's procedure rejects, measure `2 > 3/2`).

## What is cited

For a work not read here, author, title and year only: S. Holm, "A simple sequentially rejective
multiple test procedure", Scandinavian Journal of Statistics, 1979.

## Mathlib at v4.34.0

The plan's search (`MATH-PLAN-library-2-checks.py`, line `row.B3`:
`\bholm\b|bonferroni|familywise error|family.wise error|step.?down (procedure|test)`), in order
LEAN-31's run of it before this module was written, found 0 lines in pinned Mathlib, in Mathlib
master at `2da3ab0a` and in the library. Used: `measureReal_biUnion_finset_le` (the union bound),
`Finset.exists_min_image`, `div_le_div_of_nonneg_left`.
-/

open MeasureTheory Finset

namespace ClassicalLean.Probability.StepDownProcedure

variable {ι : Type*} [Fintype ι]

/-- **Holm's step-down procedure** at level `q`, for the p-values `x` (order LEAN-31, item 105 of
MATH-PLAN-library-2). Hypothesis `i` is rejected when every p-value `x j` at most `x i` is at most
`q` divided by the number of p-values at least `x j` (ties counted, which is Holm's rule with the
p-values sorted). -/
def holmRejected (q : ℝ) (x : ι → ℝ) (i : ι) : Prop :=
  ∀ j, x j ≤ x i → x j ≤ q / (univ.filter fun l ↦ x j ≤ x l).card

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Holm's procedure controls the chance of any false rejection** (order LEAN-31, item 105 of
MATH-PLAN-library-2). For p-values `P j` under a finite measure, true nulls `H` whose p-values are
valid (`μ {P i ≤ u} ≤ u` for `u ≥ 0`) and a level `q ≥ 0`, the measure of the event that Holm's
procedure rejects some true null is at most `q`, under any dependence. -/
theorem measureReal_exists_holmRejected_true_le [IsFiniteMeasure μ] {P : ι → Ω → ℝ}
    {H : Finset ι} {q : ℝ} (hq : 0 ≤ q)
    (hP : ∀ i ∈ H, ∀ u, 0 ≤ u → μ.real {ω | P i ω ≤ u} ≤ u) :
    μ.real {ω | ∃ i ∈ H, holmRejected q (fun j ↦ P j ω) i} ≤ q := by
  classical
  rcases Finset.eq_empty_or_nonempty H with rfl | hH
  · simp [hq]
  have hpos : (0 : ℝ) < H.card := by exact_mod_cast hH.card_pos
  have hsub : {ω | ∃ i ∈ H, holmRejected q (fun j ↦ P j ω) i} ⊆
      ⋃ i ∈ H, {ω | P i ω ≤ q / H.card} := by
    rintro ω ⟨i, hi, hrej⟩
    obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image H (fun j ↦ P j ω) hH
    have hk' : P k ω ≤ q / (univ.filter fun l ↦ P k ω ≤ P l ω).card := hrej k (hmin i hi)
    have hcard : H.card ≤ (univ.filter fun l ↦ P k ω ≤ P l ω).card :=
      Finset.card_le_card fun l hl ↦ by simp [hmin l hl]
    have hdiv : q / ((univ.filter fun l ↦ P k ω ≤ P l ω).card : ℝ) ≤ q / H.card :=
      div_le_div_of_nonneg_left hq hpos (by exact_mod_cast hcard)
    exact Set.mem_biUnion hk (hk'.trans hdiv)
  calc μ.real {ω | ∃ i ∈ H, holmRejected q (fun j ↦ P j ω) i}
      ≤ μ.real (⋃ i ∈ H, {ω | P i ω ≤ q / H.card}) := measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ ∑ i ∈ H, μ.real {ω | P i ω ≤ q / H.card} := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ H, q / H.card :=
        Finset.sum_le_sum fun i hi ↦ hP i hi _ (div_nonneg hq hpos.le)
    _ = q := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_div_cancel₀ q hpos.ne'

end ClassicalLean.Probability.StepDownProcedure

open MeasureTheory ProbabilityTheory in
/-- The hypotheses of `measureReal_exists_holmRejected_true_le` hold together: two equally likely
points (the uniform probability on `Fin 2`); two p-values, the true null's `P 0` equal to `1/2`
at the first point and `1` at the second, valid at every `u ≥ 0` (its chance of being at most `u`
is `0`, `1/2` or `1`), and the other's `P 1 = 0`; `H = {0}` and `q = 1/2`. Holm's procedure
rejects the true null at the first point only, so the bound `1/2` is reached (by hand; order
LEAN-31's exact check `105.witness`). -/
example := ClassicalLean.Probability.StepDownProcedure.measureReal_exists_holmRejected_true_le
  (ι := Fin 2) (μ := (uniformOn Set.univ : Measure (Fin 2)))
  (P := fun j ω ↦ if j = 0 then (if ω = 0 then 1 / 2 else 1) else 0) (H := {0}) (q := 1 / 2)
  (by norm_num)
  (fun i hi u hu ↦ by
    rw [Finset.mem_singleton] at hi
    subst hi
    have hpt : ∀ ω : Fin 2, (uniformOn Set.univ : Measure (Fin 2)).real {ω} = 1 / 2 := fun ω ↦ by
      simp [uniformOn_univ, Measure.real]
    simp only [↓reduceIte]
    by_cases h1 : 1 ≤ u
    · calc (uniformOn Set.univ : Measure (Fin 2)).real
            {ω | (if ω = 0 then (1 / 2 : ℝ) else 1) ≤ u}
          ≤ (uniformOn Set.univ : Measure (Fin 2)).real Set.univ :=
            measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)
        _ = 1 := probReal_univ
        _ ≤ u := h1
    · by_cases h2 : 1 / 2 ≤ u
      · have hs : {ω : Fin 2 | (if ω = 0 then (1 / 2 : ℝ) else 1) ≤ u} ⊆ {0} := by
          intro ω hω
          rw [Set.mem_ofPred_eq] at hω
          rw [Set.mem_singleton_iff]
          by_contra hne
          simp only [hne, ↓reduceIte] at hω
          exact h1 hω
        calc (uniformOn Set.univ : Measure (Fin 2)).real
              {ω | (if ω = 0 then (1 / 2 : ℝ) else 1) ≤ u}
            ≤ (uniformOn Set.univ : Measure (Fin 2)).real {0} :=
              measureReal_mono hs (measure_ne_top _ _)
          _ = 1 / 2 := hpt 0
          _ ≤ u := h2
      · have hs : {ω : Fin 2 | (if ω = 0 then (1 / 2 : ℝ) else 1) ≤ u} = ∅ := by
          refine Set.eq_empty_iff_forall_notMem.mpr fun ω hω ↦ ?_
          rw [Set.mem_ofPred_eq] at hω
          split_ifs at hω <;> linarith
        rw [hs, measureReal_empty]
        exact hu)
