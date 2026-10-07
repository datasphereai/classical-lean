/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Simplex.Gibbs
import Mathlib.Algebra.BigOperators.Field

/-!
# Log-sum-exp, softmax, and the Gibbs variational principle

Two definitions and the single theorem that ties them together. On a finite index set `ι`,

    logSumExp x = log ∑ i, exp (x i)          softmax x i = exp (x i) / ∑ j, exp (x j)

and for every `p` in the open probability simplex

    (∑ i, p i * x i) - ∑ i, p i * log (p i)  ≤  logSumExp x,

with equality exactly at `p = softmax x`. Read left to right this is the **Gibbs variational
principle**: log-sum-exp is the largest that the expected value of `x` plus the Shannon entropy
can be made over probability vectors, and the softmax is the unique vector attaining it. Read
right to left it says that log-sum-exp is a supremum of affine functions of `x`, which is where
`convexOn_logSumExp` comes from — no second convexity argument is needed.

The whole file rests on `ClassicalLean.Simplex.Gibbs.sum_mul_log_div_nonneg` and its strict
companion. The bridge is `logSumExp_sub_gibbsObjective`, an identity rather than an inequality:
the gap between the objective at `p` and `logSumExp x` *is* the relative entropy of `p` against
`softmax x`. Both directions of the principle, and the uniqueness, are that identity plus Gibbs'
inequality; nothing here reproves a convexity fact that `Gibbs.lean` already has.

## Relation to `Gibbs.freeEnergy`

`Gibbs.freeEnergy T i₀ x = -log (x i₀) + T * ∑ i, x i * log (x i)` is a *different* function of a
*different* argument: it is a logarithmic barrier plus negative entropy, a function on the
simplex used there to study a wall, and its first argument is the point of the simplex.
`gibbsObjective x p` below is a function of two arguments, linear in `x` and concave in `p`, and
carries no barrier term. The shared word is "Gibbs" and the shared ingredient is
`∑ p i * log (p i)`; the objects are not specialisations of one another.

## Mathlib coverage

Searched in the vendored Mathlib at the pinned revision, over `Mathlib/**/*.lean`, case
insensitively: `logsumexp`, `log_sum_exp`, `logSumExp` — no hits; `softmax`, `soft_max` — no
hits; `convexConjugate`, `fenchel`, `legendre` — hits are the Legendre symbol and Legendre's
duplication formula for `Gamma`, nothing convex-analytic. `Mathlib.InformationTheory.\
KullbackLeibler.Basic` has `klDiv`, but measure-theoretically, over `Measure α` and valued in
`ℝ≥0∞`; the finite relative entropy used here is the `Finset` sum already in `Gibbs.lean`, and
routing a finite statement through a measure buys nothing at this size.

## Contents

* `logSumExp`, `softmax` — the definitions.
* `sum_exp_pos`, `softmax_pos`, `sum_softmax`, `softmax_mem_openSimplex` — softmax lands in
  `openSimplex`, so every lemma of `Basic.lean` and `Gibbs.lean` applies to it.
* `log_softmax` — `log (softmax x i) = x i - logSumExp x`. This one line is what makes the
  identity below fall out.
* `le_logSumExp`, `logSumExp_le_sup'_add_log_card` — the elementary two-sided bound.
* `logSumExp_add_const`, `softmax_add_const` — the shift equivariance and shift invariance that
  make softmax a function of the differences of the coordinates alone.
* `gibbsObjective`, `logSumExp_sub_gibbsObjective` — the objective and the exact gap identity.
* `gibbsObjective_le`, `gibbsObjective_softmax`, `isMaxOn_gibbsObjective`,
  `gibbsObjective_lt_of_ne`, `gibbsObjective_eq_iff` — the principle, its attainment and the
  uniqueness of the maximiser.
* `convexOn_logSumExp` — convexity, derived from the principle in four lines.

A `Nonempty ι` hypothesis is not decoration: on an empty index set `∑ i, exp (x i) = 0`, its
logarithm is `Real.log 0 = 0` by Mathlib's junk-value convention, and softmax is `0 / 0`. Every
statement whose proof divides by that sum, or asserts a coordinate is positive, carries it.
Three do not, and are marked `omit [Nonempty ι]` rather than left to the section: `le_logSumExp`
(its own index argument already supplies the nonemptiness), `sum_exp_add_const` and
`softmax_add_const` (both are identities between the two sides as written, and `0 = 0 * exp c`
and `0 / 0 = 0 / 0` are among the cases they cover). The `omit` is load-bearing — without it the
`unusedSectionVars` linter fails the build, which is how the three were found.
-/

open Finset

namespace ClassicalLean.Simplex

variable {ι : Type*} [Fintype ι]

/-- The log-sum-exp of a real vector on a finite index set: `log ∑ i, exp (x i)`. -/
noncomputable def logSumExp (x : ι → ℝ) : ℝ := Real.log (∑ i, Real.exp (x i))

/-- The softmax of a real vector: the probability vector proportional to `exp (x i)`. -/
noncomputable def softmax (x : ι → ℝ) (i : ι) : ℝ := Real.exp (x i) / ∑ j, Real.exp (x j)

/-- The Gibbs objective at an inverse temperature absorbed into `x`: the expected value of `x`
under `p` plus the Shannon entropy of `p`, written with the negative entropy that `Gibbs.lean`
uses so that the two files share one expression for it. -/
noncomputable def gibbsObjective (x p : ι → ℝ) : ℝ :=
  (∑ i, p i * x i) - ∑ i, p i * Real.log (p i)

section Nonempty

variable [Nonempty ι]

/-- The partition sum is strictly positive, which is what every division below needs. -/
theorem sum_exp_pos (x : ι → ℝ) : 0 < ∑ i, Real.exp (x i) :=
  Finset.sum_pos (fun i _ => Real.exp_pos (x i)) Finset.univ_nonempty

/-- Every softmax coordinate is strictly positive. -/
theorem softmax_pos (x : ι → ℝ) (i : ι) : 0 < softmax x i :=
  div_pos (Real.exp_pos (x i)) (sum_exp_pos x)

/-- The softmax coordinates sum to `1`. -/
theorem sum_softmax (x : ι → ℝ) : ∑ i, softmax x i = 1 := by
  simp only [softmax]
  rw [← Finset.sum_div, div_self (sum_exp_pos x).ne']

/-- The softmax of any vector lies in the open probability simplex of `Basic.lean`. -/
theorem softmax_mem_openSimplex (x : ι → ℝ) : softmax x ∈ openSimplex ι :=
  ⟨softmax_pos x, sum_softmax x⟩

/-- `log (softmax x i) = x i - logSumExp x`. The log-partition function is exactly the constant
that turns the coordinates of `x` into log-probabilities. -/
theorem log_softmax (x : ι → ℝ) (i : ι) : Real.log (softmax x i) = x i - logSumExp x := by
  rw [softmax, Real.log_div (Real.exp_ne_zero (x i)) (sum_exp_pos x).ne', Real.log_exp, logSumExp]

omit [Nonempty ι] in
/-- Log-sum-exp dominates every coordinate. -/
theorem le_logSumExp (x : ι → ℝ) (i : ι) : x i ≤ logSumExp x := by
  have h : Real.exp (x i) ≤ ∑ j, Real.exp (x j) :=
    Finset.single_le_sum (fun j _ => (Real.exp_pos (x j)).le) (Finset.mem_univ i)
  calc x i = Real.log (Real.exp (x i)) := (Real.log_exp (x i)).symm
    _ ≤ logSumExp x := Real.log_le_log (Real.exp_pos (x i)) h

/-- Log-sum-exp exceeds the largest coordinate by at most `log |ι|`. With `le_logSumExp` this
is the standard statement that log-sum-exp is a smooth maximum, sandwiched between the maximum
and the maximum plus `log |ι|`. -/
theorem logSumExp_le_sup'_add_log_card (x : ι → ℝ) :
    logSumExp x ≤ Finset.univ.sup' Finset.univ_nonempty x + Real.log (Fintype.card ι) := by
  set M := Finset.univ.sup' Finset.univ_nonempty x with hM
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hle : ∑ i, Real.exp (x i) ≤ (Fintype.card ι : ℝ) * Real.exp M := by
    calc ∑ i, Real.exp (x i) ≤ ∑ _i : ι, Real.exp M :=
          Finset.sum_le_sum fun i _ =>
            Real.exp_le_exp.mpr (hM ▸ Finset.le_sup' x (Finset.mem_univ i))
      _ = (Fintype.card ι : ℝ) * Real.exp M := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc logSumExp x ≤ Real.log ((Fintype.card ι : ℝ) * Real.exp M) :=
        Real.log_le_log (sum_exp_pos x) hle
    _ = M + Real.log (Fintype.card ι) := by
        rw [Real.log_mul hcard.ne' (Real.exp_ne_zero M), Real.log_exp]; ring

omit [Nonempty ι] in
/-- The partition sum of a shifted vector. Extracted because both shift lemmas need it. -/
theorem sum_exp_add_const (x : ι → ℝ) (c : ℝ) :
    ∑ i, Real.exp (x i + c) = (∑ i, Real.exp (x i)) * Real.exp c := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => Real.exp_add (x i) c

/-- Adding a constant to every coordinate adds it to the log-sum-exp. -/
theorem logSumExp_add_const (x : ι → ℝ) (c : ℝ) :
    logSumExp (fun i => x i + c) = logSumExp x + c := by
  simp only [logSumExp]
  rw [sum_exp_add_const x c, Real.log_mul (sum_exp_pos x).ne' (Real.exp_ne_zero c), Real.log_exp]

omit [Nonempty ι] in
/-- Adding a constant to every coordinate leaves the softmax unchanged: softmax depends only on
the differences of the coordinates. -/
theorem softmax_add_const (x : ι → ℝ) (c : ℝ) : softmax (fun i => x i + c) = softmax x := by
  funext i
  simp only [softmax]
  rw [sum_exp_add_const x c, Real.exp_add (x i) c,
    mul_div_mul_right _ _ (Real.exp_ne_zero c)]

/-! ## The gap identity

Everything below is this one identity read in a different direction. -/

/-- **The gap is a relative entropy.** For `p` in the open simplex, the amount by which the
Gibbs objective at `p` falls short of `logSumExp x` is exactly the relative entropy of `p`
against `softmax x`. This is an equation, not a bound: the inequality, the attainment and the
uniqueness below are each this identity combined with one fact from `Gibbs.lean`. -/
theorem logSumExp_sub_gibbsObjective (x : ι → ℝ) {p : ι → ℝ} (hp : p ∈ openSimplex ι) :
    logSumExp x - gibbsObjective x p = ∑ i, p i * Real.log (p i / softmax x i) := by
  obtain ⟨hp0, hp1⟩ := hp
  have hterm : ∀ i, p i * Real.log (p i / softmax x i)
      = p i * Real.log (p i) - p i * x i + p i * logSumExp x := by
    intro i
    rw [Real.log_div (hp0 i).ne' (softmax_pos x i).ne', log_softmax]
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hp1, one_mul]
  simp only [gibbsObjective]
  ring

/-- **The Gibbs variational principle, upper bound.** No probability vector on the open simplex
makes the expected value of `x` plus its entropy exceed `logSumExp x`. -/
theorem gibbsObjective_le (x : ι → ℝ) {p : ι → ℝ} (hp : p ∈ openSimplex ι) :
    gibbsObjective x p ≤ logSumExp x := by
  have h := sum_mul_log_div_nonneg hp.1 (softmax_pos x) hp.2 (sum_softmax x)
  rw [← logSumExp_sub_gibbsObjective x hp] at h
  linarith

/-- **The bound is attained at the softmax**, where the relative entropy of the gap identity is
the relative entropy of a vector against itself. -/
theorem gibbsObjective_softmax (x : ι → ℝ) : gibbsObjective x (softmax x) = logSumExp x := by
  have h := logSumExp_sub_gibbsObjective x (softmax_mem_openSimplex x)
  have hz : ∑ i, softmax x i * Real.log (softmax x i / softmax x i) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      rw [div_self (softmax_pos x i).ne', Real.log_one, mul_zero]
  rw [hz] at h
  linarith

/-- The softmax maximises the Gibbs objective over the open probability simplex. -/
theorem isMaxOn_gibbsObjective (x : ι → ℝ) :
    IsMaxOn (gibbsObjective x) (openSimplex ι) (softmax x) := by
  intro p hp
  simp only [Set.mem_ofPred_eq, gibbsObjective_softmax x]
  exact gibbsObjective_le x hp

/-- **Uniqueness of the maximiser.** Any other point of the open simplex is strictly below
`logSumExp x`, by the strict form of Gibbs' inequality. -/
theorem gibbsObjective_lt_of_ne (x : ι → ℝ) {p : ι → ℝ} (hp : p ∈ openSimplex ι)
    (hne : p ≠ softmax x) : gibbsObjective x p < logSumExp x := by
  have h := sum_mul_log_div_pos_of_ne hp.1 (softmax_pos x) hp.2 (sum_softmax x) hne
  rw [← logSumExp_sub_gibbsObjective x hp] at h
  linarith

/-- **The variational principle in the form that identifies the maximiser.** On the open
simplex, attaining `logSumExp x` characterises the softmax. -/
theorem gibbsObjective_eq_iff (x : ι → ℝ) {p : ι → ℝ} (hp : p ∈ openSimplex ι) :
    gibbsObjective x p = logSumExp x ↔ p = softmax x := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra hne
    exact absurd h (gibbsObjective_lt_of_ne x hp hne).ne
  · rintro rfl
    exact gibbsObjective_softmax x

/-! ## Convexity, for free

`gibbsObjective x p` is affine in `x` for each fixed `p`, so the principle exhibits `logSumExp`
as a pointwise supremum of affine functions. The proof below is that observation and nothing
else: evaluate the objective at the maximiser of the *midpoint*, split it, and bound each half
by its own log-sum-exp. -/

/-- Log-sum-exp is convex on the whole of `ι → ℝ`. -/
theorem convexOn_logSumExp : ConvexOn ℝ (Set.univ : Set (ι → ℝ)) (logSumExp (ι := ι)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  set q := softmax (a • x + b • y) with hqdef
  have hq : q ∈ openSimplex ι := softmax_mem_openSimplex _
  have hsplit : gibbsObjective (a • x + b • y) q
      = a * gibbsObjective x q + b * gibbsObjective y q := by
    simp only [gibbsObjective, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : ∑ i, q i * (a * x i + b * y i)
        = a * ∑ i, q i * x i + b * ∑ i, q i * y i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1]
    linear_combination (∑ i, q i * Real.log (q i)) * hab
  simp only [smul_eq_mul]
  calc logSumExp (a • x + b • y) = gibbsObjective (a • x + b • y) q :=
        (gibbsObjective_softmax _).symm
    _ = a * gibbsObjective x q + b * gibbsObjective y q := hsplit
    _ ≤ a * logSumExp x + b * logSumExp y :=
        add_le_add (mul_le_mul_of_nonneg_left (gibbsObjective_le x hq) ha)
          (mul_le_mul_of_nonneg_left (gibbsObjective_le y hq) hb)

end Nonempty

end ClassicalLean.Simplex
