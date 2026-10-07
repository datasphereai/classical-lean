/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Simplex.LogSumExp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Cross-entropy, and the derivative half of the variational principle

`ClassicalLean.Simplex.LogSumExp` proves the Gibbs variational principle and reads convexity off
it. That is the static half: it says what the maximum is and where it is attained. This file is
the derivative half. Its three results are

    hasDerivAt_logSumExp      d/dt logSumExp (update x k t) |_{t = x k}  =  softmax x k
    crossEntropy_sub_entropy  crossEntropy x p - H p  =  relative entropy of p against softmax x
    hasDerivAt_crossEntropy   d/dt crossEntropy (update x k t) p |_{t = x k}  =  softmax x k - p k

Together: softmax is the gradient of log-sum-exp, and the gradient of the cross-entropy in the
logits is `softmax - p`. The second is the rule that a gradient step on a linear model follows,
and it is a corollary of the first — the entropy term of `crossEntropy` does not depend on `x`,
so differentiating it contributes the `-p k` and nothing more.

`log_softmax : Real.log (softmax x i) = x i - logSumExp x` is most of the work: after
`sum_exp_update` splits the partition sum into the one moving Boltzmann factor and a constant,
the derivative is Mathlib's `HasDerivAt.log` applied to `Real.hasDerivAt_exp`.

## The `DecidableEq` decision

`Function.update` needs `[DecidableEq ι]` and `LogSumExp.lean` does not carry it. This file
takes the `Function.update` route and carries the instance, **scoped to the section that uses
it** rather than at module level: `crossEntropy` and the four statements that do not
differentiate are stated without it, so nothing downstream inherits a decidability hypothesis it
does not need. There is no `Finset.sum`-splitting variant of the same statements anywhere here;
the two forms are not mixed.

## Mathlib coverage

`grep -rniE 'crossentropy|cross_entropy' Mathlib/` over the vendored tree at the pinned
revision returns **no hits** (exit 1). `Mathlib.InformationTheory` holds `Coding`,
`Hamming.lean` and `KullbackLeibler`; the last is measure-theoretic, over `Measure α` and valued
in `ℝ≥0∞`, and is the same object `LogSumExp.lean`'s header declines to route a finite statement
through. Mathlib has `Real.hasDerivAt_exp` and `HasDerivAt.log`, which is all this file borrows.

## Contents

* `crossEntropy x p = logSumExp x - ∑ i, p i * x i` — the cross-entropy of `p` against
  `softmax x`, written in the logits.
* `crossEntropy_eq_neg_sum_mul_log_softmax` — that the definition *is* `-∑ i, p i * log (q i)`
  for `q = softmax x`, which is what makes the name true. It holds on the simplex, where
  `∑ p i = 1` is what collapses the `logSumExp` terms.
* `sum_exp_update`, `sum_mul_update`, `sum_exp_eq_add_erase` — the splitting lemmas, isolating
  the single coordinate that moves from the constant that does not.
* `hasDerivAt_logSumExp` — softmax is the gradient.
* `hasDerivAt_crossEntropy` — the derivative in one logit is `softmax x k - p k`.
* `crossEntropy_sub_entropy` — cross-entropy minus entropy is the relative entropy to softmax.
* `crossEntropy_nonneg_sub`, `crossEntropy_eq_iff` — that difference is nonnegative, and zero
  exactly at `p = softmax x`.

## What is cited rather than reproved

`crossEntropy_sub_entropy` is `logSumExp_sub_gibbsObjective` rearranged and cites it.
`crossEntropy_nonneg_sub` and `crossEntropy_eq_iff` cite `gibbsObjective_le` and
`gibbsObjective_eq_iff`. Those two are already exactly `Gibbs.sum_mul_log_div_nonneg` and
`Gibbs.sum_mul_log_div_pos_of_ne` applied to `softmax_mem_openSimplex` — that application *is*
their proof — so citing the Gibbs lemmas directly here would duplicate it. Nothing in this file
reproves an inequality that `Gibbs.lean` or `LogSumExp.lean` already has.

`hasDerivAt_crossEntropy` is stated for an arbitrary `p`, with no `p ∈ openSimplex ι`
hypothesis. The derivative computation never uses positivity or `∑ p i = 1`; carrying the
hypothesis would weaken the theorem for nothing, and Lean's `unusedVariables` linter would fail
the build over it.
-/

open Finset

namespace ClassicalLean.Simplex

variable {ι : Type*} [Fintype ι]

/-- The cross-entropy of a probability vector `p` against the softmax of `x`, written in the
logits `x`. On the simplex this equals `-∑ i, p i * log (softmax x i)`; see
`crossEntropy_eq_neg_sum_mul_log_softmax`. -/
noncomputable def crossEntropy (x p : ι → ℝ) : ℝ := logSumExp x - ∑ i, p i * x i

section Simplex

variable [Nonempty ι]

/-- **The definition is the cross-entropy its name claims.** For `p` on the open simplex,
`crossEntropy x p = -∑ i, p i * log (softmax x i)`. The logit form and the log-probability form
agree because `log (softmax x i) = x i - logSumExp x` and the `logSumExp` terms collect against
`∑ i, p i = 1`. -/
theorem crossEntropy_eq_neg_sum_mul_log_softmax (x : ι → ℝ) {p : ι → ℝ}
    (hp : p ∈ openSimplex ι) : crossEntropy x p = -∑ i, p i * Real.log (softmax x i) := by
  have hterm : ∀ i, p i * Real.log (softmax x i) = p i * x i - p i * logSumExp x := by
    intro i
    rw [log_softmax]
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2,
    one_mul]
  simp only [crossEntropy]
  ring

/-- **Cross-entropy minus entropy is the relative entropy to the softmax.** This is
`logSumExp_sub_gibbsObjective` rearranged: `crossEntropy x p + ∑ i, p i * log (p i)` and
`logSumExp x - gibbsObjective x p` are the same expression. -/
theorem crossEntropy_sub_entropy (x : ι → ℝ) {p : ι → ℝ} (hp : p ∈ openSimplex ι) :
    crossEntropy x p - (-∑ i, p i * Real.log (p i))
      = ∑ i, p i * Real.log (p i / softmax x i) := by
  rw [← logSumExp_sub_gibbsObjective x hp]
  simp only [crossEntropy, gibbsObjective]
  ring

/-- **Cross-entropy is at least entropy.** The gap is a relative entropy, so this is
`gibbsObjective_le` read through `crossEntropy_sub_entropy`. -/
theorem crossEntropy_nonneg_sub (x : ι → ℝ) {p : ι → ℝ} (hp : p ∈ openSimplex ι) :
    0 ≤ crossEntropy x p - (-∑ i, p i * Real.log (p i)) := by
  have h := gibbsObjective_le x hp
  simp only [crossEntropy, gibbsObjective] at h ⊢
  linarith

/-- **Equality holds exactly at the softmax.** The cross-entropy of `p` against `softmax x`
equals the entropy of `p` if and only if `p` *is* `softmax x` — the identification of the
minimiser, restated from `gibbsObjective_eq_iff`. -/
theorem crossEntropy_eq_iff (x : ι → ℝ) {p : ι → ℝ} (hp : p ∈ openSimplex ι) :
    crossEntropy x p = -∑ i, p i * Real.log (p i) ↔ p = softmax x := by
  rw [← gibbsObjective_eq_iff x hp]
  simp only [crossEntropy, gibbsObjective]
  constructor <;> intro h <;> linarith

end Simplex

/-! ## The derivative in one logit

`Function.update x k t` is `x` with its `k`-th coordinate replaced by `t`. Differentiating in
`t` splits every sum into the one term that moves and a constant, which is what the three
lemmas below do; the derivative is then Mathlib's. `[DecidableEq ι]` enters here and nowhere
else in this file. -/

section Update

variable [DecidableEq ι]

/-- The partition sum with one logit replaced: one moving Boltzmann factor `exp t`, and a
constant that does not depend on `t`. -/
theorem sum_exp_update (x : ι → ℝ) (k : ι) (t : ℝ) :
    ∑ i, Real.exp (Function.update x k t i)
      = Real.exp t + ∑ i ∈ Finset.univ.erase k, Real.exp (x i) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), Function.update_self]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- The same split for the linear term `∑ i, p i * x i`. -/
theorem sum_mul_update (p x : ι → ℝ) (k : ι) (t : ℝ) :
    ∑ i, p i * Function.update x k t i
      = p k * t + ∑ i ∈ Finset.univ.erase k, p i * x i := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), Function.update_self]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- The partition sum with the `k`-th factor pulled out. This is `sum_exp_update` at the value
the coordinate already has, and it is what identifies the derivative below as `softmax x k`
rather than as an unnamed quotient. -/
theorem sum_exp_eq_add_erase (x : ι → ℝ) (k : ι) :
    ∑ i, Real.exp (x i) = Real.exp (x k) + ∑ i ∈ Finset.univ.erase k, Real.exp (x i) :=
  (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm

/-- **Softmax is the gradient of log-sum-exp.** Moving the `k`-th logit and holding the rest
fixed, the derivative of `logSumExp` at the point the logit started from is `softmax x k`. -/
theorem hasDerivAt_logSumExp [Nonempty ι] (x : ι → ℝ) (k : ι) :
    HasDerivAt (fun t : ℝ => logSumExp (Function.update x k t)) (softmax x k) (x k) := by
  have hC0 : (0 : ℝ) ≤ ∑ i ∈ Finset.univ.erase k, Real.exp (x i) :=
    Finset.sum_nonneg fun i _ => (Real.exp_pos (x i)).le
  have hpos : 0 < Real.exp (x k) + ∑ i ∈ Finset.univ.erase k, Real.exp (x i) := by
    have := Real.exp_pos (x k)
    linarith
  have hfun : (fun t : ℝ => logSumExp (Function.update x k t))
      = fun t : ℝ => Real.log (Real.exp t + ∑ i ∈ Finset.univ.erase k, Real.exp (x i)) := by
    funext t
    rw [logSumExp, sum_exp_update]
  have hsm : softmax x k
      = Real.exp (x k) / (Real.exp (x k) + ∑ i ∈ Finset.univ.erase k, Real.exp (x i)) := by
    rw [softmax, sum_exp_eq_add_erase x k]
  rw [hfun, hsm]
  exact ((Real.hasDerivAt_exp (x k)).add_const _).log hpos.ne'

/-- **The gradient of the cross-entropy in the logits is `softmax - p`.** Moving the `k`-th
logit, the derivative of `crossEntropy · p` is `softmax x k - p k`. No hypothesis on `p`: the
`logSumExp` term contributes `softmax x k` by `hasDerivAt_logSumExp` and the linear term
contributes `p k`, and neither step uses positivity or that `p` sums to `1`. -/
theorem hasDerivAt_crossEntropy [Nonempty ι] (x p : ι → ℝ) (k : ι) :
    HasDerivAt (fun t : ℝ => crossEntropy (Function.update x k t) p)
      (softmax x k - p k) (x k) := by
  have hlin : HasDerivAt (fun t : ℝ => ∑ i, p i * Function.update x k t i) (p k) (x k) := by
    have hfun : (fun t : ℝ => ∑ i, p i * Function.update x k t i)
        = fun t : ℝ => p k * t + ∑ i ∈ Finset.univ.erase k, p i * x i := by
      funext t
      rw [sum_mul_update]
    rw [hfun]
    simpa using ((hasDerivAt_id (x k)).const_mul (p k)).add_const
      (∑ i ∈ Finset.univ.erase k, p i * x i)
  simpa only [crossEntropy, Pi.sub_def] using (hasDerivAt_logSumExp x k).sub hlin

end Update

end ClassicalLean.Simplex
