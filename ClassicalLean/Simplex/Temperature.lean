/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Simplex.Involution
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.Order.Field

/-!
# Temperature

The softmax at temperature `T` is the softmax of the logits scaled by `T⁻¹`:

    softmaxT T x = softmax (T⁻¹ • x),      softmaxT T x i = exp (x i / T) / ∑ j, exp (x j / T)

`T` interpolates between two degenerate regimes, and both limits are proved below:
as `T → ∞` every coordinate is equally likely, and as `T → 0⁺` all the mass moves to the
largest logit. `T = 1` recovers `softmax` itself.

## What this connects

Three parts of the library used the temperature idea in a special case and could not say so.

* `Gibbs.gibbsWeight m T E = 1 / (1 + m * exp (-(E / T)))` is introduced there as an algebraic
  expression, and `Gibbs.criticalTemperature` and `Simplex/DesignConstants` are built on it.
  `gibbsWeight_eq_softmaxT` identifies it: it **is** the softmax weight, at temperature `T`, of
  the dominant level of a system with one level at energy `E` and `m` at energy `0`. That is the
  first statement joining `LogSumExp.lean` to the free-energy work.
* `Involution.twoLevelEnergy n τ` is that same energy vector with `E = 1`, already divided by the
  temperature. `softmaxT_levelGap_one` says the two constructions agree, and
  `softmaxT_levelGap_one_thresholdTemperature` restates the golden threshold as a statement
  about `softmaxT`.
* `levelGap n E` is the shared object all three were writing out by hand.

## Contents

* `softmaxT`, `softmaxT_apply`, `softmaxT_one`, `softmaxT_mem_openSimplex` — the definition and
  its basic properties. Membership is inherited from `softmax_mem_openSimplex`, not reproved.
* `levelGap`, `softmaxT_levelGap` — the two-level system and its dominant weight.
* `gibbsWeight_eq_softmaxT`, `softmaxT_levelGap_one`,
  `softmaxT_levelGap_one_thresholdTemperature` — the three connections above.
* `softmaxT_eq_inv_sum`, `softmaxT_eq_mul_softmaxT` — the two rearrangements the limits need.
  Both are exact identities and hold at every `T`, `T = 0` included, where every `x i / T` is
  `0` by Mathlib's junk-value convention and `softmaxT 0 x` is the uniform vector.
* `tendsto_softmaxT_atTop` — the high-temperature limit is uniform.
* `tendsto_softmaxT_nhdsGT_zero`, `tendsto_softmaxT_nhdsGT_zero_of_ne` — the low-temperature
  limit concentrates on a strict maximiser.

## Two hypotheses that are not decoration

The low-temperature limit assumes a **strict** maximiser (`∀ j ≠ k, x j < x k`). Without it the
limit is not the indicator of `k`: on tied logits the mass splits evenly over the tied set, and
`softmaxT T ![0, 0] 0 = 1/2` for every `T`. The theorem is stated for a strict maximiser because
that is the case where the limit is `1`.

No `[DecidableEq ι]` is carried anywhere in this file. The low-temperature proof does use a
`Finset.erase` to separate the maximising coordinate from the rest, but only inside the proof, so
it is obtained by `classical` rather than by a hypothesis on the statement. This is the opposite
resolution to `CrossEntropy.lean`'s, and for a reason: there `Function.update` appears in the
*statements*, so the instance has to be assumed; here it does not, and Lean's
`unusedDecidableInType` linter fails the build if it is assumed anyway.
-/

open Finset Filter Topology

namespace ClassicalLean.Simplex

variable {ι : Type*} [Fintype ι]

/-- The softmax at temperature `T`: the softmax of the logits scaled by `T⁻¹`. Low `T`
sharpens the distribution, high `T` flattens it. -/
noncomputable def softmaxT (T : ℝ) (x : ι → ℝ) : ι → ℝ := softmax (T⁻¹ • x)

/-- The coordinate formula. `T⁻¹ * x i` is written as `x i / T` from here on. -/
theorem softmaxT_apply (T : ℝ) (x : ι → ℝ) (i : ι) :
    softmaxT T x i = Real.exp (x i / T) / ∑ j, Real.exp (x j / T) := by
  simp only [softmaxT, softmax, Pi.smul_apply, smul_eq_mul, inv_mul_eq_div]

/-- At temperature `1` this is the softmax of `LogSumExp.lean`. -/
theorem softmaxT_one (x : ι → ℝ) : softmaxT 1 x = softmax x := by
  simp [softmaxT]

/-- The softmax at any temperature is a strictly positive probability vector — inherited from
`softmax_mem_openSimplex`, since `softmaxT T x` is a `softmax` by definition. -/
theorem softmaxT_mem_openSimplex [Nonempty ι] (T : ℝ) (x : ι → ℝ) :
    softmaxT T x ∈ openSimplex ι :=
  softmax_mem_openSimplex _

/-! ## The two-level system

One level at energy `E`, `n` levels at energy `0`. This is the object `Gibbs.gibbsWeight` and
`Involution.twoLevelEnergy` were each writing out separately. -/

/-- The energy vector of a two-level system on `n + 1` states: the dominant level at energy `E`,
the other `n` at energy `0`. -/
def levelGap (n : ℕ) (E : ℝ) : Fin (n + 1) → ℝ := fun i => if i = 0 then E else 0

/-- The partition sum of the two-level system at temperature `T`. -/
theorem sum_exp_levelGap (n : ℕ) (T E : ℝ) :
    ∑ j, Real.exp (levelGap n E j / T) = Real.exp (E / T) + n := by
  rw [Fin.sum_univ_succ]
  simp [levelGap, Fin.succ_ne_zero]

/-- The dominant weight of the two-level system at temperature `T`. -/
theorem softmaxT_levelGap (n : ℕ) (T E : ℝ) :
    softmaxT T (levelGap n E) 0 = Real.exp (E / T) / (Real.exp (E / T) + n) := by
  rw [softmaxT_apply, sum_exp_levelGap]
  congr 1

/-- **`Gibbs.gibbsWeight` is a softmax weight.** The expression `1 / (1 + m * exp (-(E / T)))`
that `Gibbs.lean` introduces algebraically, and on which `criticalTemperature` and
`Simplex/DesignConstants` are built, is the temperature-`T` softmax weight of the dominant level
of a two-level system with `m` suppressed states.

No hypothesis on `T`: at `T = 0` both sides are `1 / (1 + m)` under Mathlib's junk-value
convention for division by zero, so the identity is unconditional rather than conditional on
`T ≠ 0`. -/
theorem gibbsWeight_eq_softmaxT (n : ℕ) (T E : ℝ) :
    gibbsWeight (n : ℝ) T E = softmaxT T (levelGap n E) 0 := by
  rw [softmaxT_levelGap, gibbsWeight, Real.exp_neg]
  have hp : (0 : ℝ) < Real.exp (E / T) := Real.exp_pos _
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hd : Real.exp (E / T) + (n : ℝ) ≠ 0 := by positivity
  field_simp

/-- **`Involution.twoLevelEnergy` is `levelGap` at unit energy.** The two constructions agree:
`twoLevelEnergy n τ` has the temperature already divided in, and `softmaxT` divides it in. -/
theorem softmaxT_levelGap_one (n : ℕ) (T : ℝ) :
    softmaxT T (levelGap n 1) = softmax (twoLevelEnergy n T) := by
  unfold softmaxT twoLevelEnergy levelGap
  congr 1
  funext i
  by_cases h : i = 0 <;> simp [h, div_eq_inv_mul]

/-- **The golden threshold, restated at temperature.** `Involution`'s statement that the dominant
weight at the threshold temperature is `φ⁻¹` is a statement about `softmaxT` of a two-level
system, once both sides are named. -/
theorem softmaxT_levelGap_one_thresholdTemperature {n : ℕ} (hn : 1 ≤ n) :
    softmaxT (thresholdTemperature (n : ℝ)) (levelGap n 1) 0 = Real.goldenRatio⁻¹ := by
  rw [softmaxT_levelGap_one]
  exact softmax_twoLevelEnergy_thresholdTemperature hn

/-! ## The two limits -/

/-- Every coordinate as a multiple of a chosen one. -/
theorem softmaxT_eq_mul_softmaxT (T : ℝ) (x : ι → ℝ) (j k : ι) :
    softmaxT T x j = Real.exp ((x j - x k) / T) * softmaxT T x k := by
  simp only [softmaxT_apply, sub_div, Real.exp_sub]
  field_simp

/-- The chosen coordinate as the reciprocal of a sum of relative Boltzmann factors. This is the
form the low-temperature limit is taken in: every term with `x j < x k` vanishes. -/
theorem softmaxT_eq_inv_sum (T : ℝ) (x : ι → ℝ) (k : ι) :
    softmaxT T x k = (∑ j, Real.exp ((x j - x k) / T))⁻¹ := by
  have h : ∑ j, Real.exp ((x j - x k) / T)
      = (∑ j, Real.exp (x j / T)) / Real.exp (x k / T) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by rw [sub_div, Real.exp_sub]
  rw [softmaxT_apply, h, inv_div]

/-- **The high-temperature limit is uniform.** As `T → ∞` every logit is divided away and each
coordinate tends to `1 / |ι|`, whatever the logits were. -/
theorem tendsto_softmaxT_atTop [Nonempty ι] (x : ι → ℝ) (i : ι) :
    Tendsto (fun T : ℝ => softmaxT T x i) atTop (nhds ((Fintype.card ι : ℝ)⁻¹)) := by
  have hexp : ∀ j : ι, Tendsto (fun T : ℝ => Real.exp (x j / T)) atTop (nhds 1) := by
    intro j
    have hdiv : Tendsto (fun T : ℝ => x j / T) atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
    simpa [Function.comp_def] using (Real.continuous_exp.tendsto 0).comp hdiv
  have hsum : Tendsto (fun T : ℝ => ∑ j, Real.exp (x j / T)) atTop
      (nhds (Fintype.card ι : ℝ)) := by
    simpa using tendsto_finsetSum Finset.univ fun j (_ : j ∈ Finset.univ) => hexp j
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [softmaxT_apply]
  simpa [Pi.div_def] using (hexp i).div hsum hcard

section LowTemperature

/-- Each suppressed Boltzmann factor vanishes as the temperature falls: `x j < x k` makes
`(x j - x k) / T` tend to `-∞` as `T → 0⁺`. -/
theorem tendsto_exp_sub_div_nhdsGT_zero {a : ℝ} (ha : a < 0) :
    Tendsto (fun T : ℝ => Real.exp (a / T)) (𝓝[>] (0 : ℝ)) (nhds 0) := by
  have h : Tendsto (fun T : ℝ => a / T) (𝓝[>] (0 : ℝ)) atBot := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_mul_atBot_of_neg ha).mpr tendsto_inv_nhdsGT_zero
  exact Real.tendsto_exp_atBot.comp h

/-- **The low-temperature limit concentrates on a strict maximiser.** If `x k` strictly exceeds
every other logit, then `softmaxT T x k → 1` as `T → 0⁺`. -/
theorem tendsto_softmaxT_nhdsGT_zero [Nonempty ι] {x : ι → ℝ} {k : ι}
    (hk : ∀ j, j ≠ k → x j < x k) :
    Tendsto (fun T : ℝ => softmaxT T x k) (𝓝[>] (0 : ℝ)) (nhds 1) := by
  classical
  have hsplit : ∀ T : ℝ, ∑ j, Real.exp ((x j - x k) / T)
      = 1 + ∑ j ∈ Finset.univ.erase k, Real.exp ((x j - x k) / T) := by
    intro T
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    simp
  have hzero : ∀ j ∈ Finset.univ.erase k,
      Tendsto (fun T : ℝ => Real.exp ((x j - x k) / T)) (𝓝[>] (0 : ℝ)) (nhds 0) := fun j hj =>
    tendsto_exp_sub_div_nhdsGT_zero (sub_neg.mpr (hk j (Finset.ne_of_mem_erase hj)))
  have hsum : Tendsto (fun T : ℝ => ∑ j, Real.exp ((x j - x k) / T)) (𝓝[>] (0 : ℝ)) (nhds 1) := by
    refine Filter.Tendsto.congr (fun T => (hsplit T).symm) ?_
    have herase := tendsto_finsetSum (Finset.univ.erase k) hzero
    rw [Finset.sum_const_zero] at herase
    have h1 : Tendsto (fun T : ℝ => (1 : ℝ) + ∑ j ∈ Finset.univ.erase k,
        Real.exp ((x j - x k) / T)) (𝓝[>] (0 : ℝ)) (nhds ((1 : ℝ) + 0)) :=
      tendsto_const_nhds.add herase
    rwa [add_zero] at h1
  simp only [softmaxT_eq_inv_sum]
  simpa using hsum.inv₀ one_ne_zero

/-- The other coordinates vanish in the same limit. -/
theorem tendsto_softmaxT_nhdsGT_zero_of_ne [Nonempty ι] {x : ι → ℝ} {k : ι}
    (hk : ∀ j, j ≠ k → x j < x k) {j : ι} (hj : j ≠ k) :
    Tendsto (fun T : ℝ => softmaxT T x j) (𝓝[>] (0 : ℝ)) (nhds 0) := by
  have h := (tendsto_exp_sub_div_nhdsGT_zero (sub_neg.mpr (hk j hj))).mul
    (tendsto_softmaxT_nhdsGT_zero hk)
  simpa [softmaxT_eq_mul_softmaxT (x := x) (j := j) (k := k)] using h

end LowTemperature

end ClassicalLean.Simplex
