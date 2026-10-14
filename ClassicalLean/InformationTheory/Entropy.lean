/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Simplex.CrossEntropy

/-!
# Finite Shannon entropy and relative entropy

Entropy and relative entropy of finite real vectors, stated with explicit hypotheses rather than
on a simplex, so that each theorem carries exactly the hypotheses its proof uses.

* `shannonEntropy p = -∑ i, p i * log (p i)` — moved here unchanged from `Simplex/FisherRao.lean`,
  keeping its full name `ClassicalLean.Simplex.shannonEntropy`; `FisherRao.lean` now imports it.
* `relEntropy p q = ∑ i, p i * log (p i / q i)` — the Kullback–Leibler divergence. Not `klDiv`,
  which would collide with Mathlib's `InformationTheory.klDiv` under `open InformationTheory`.
* `sum_sub_sum_le_relEntropy` — `∑ p - ∑ q ≤ relEntropy p q` for `p, q ≥ 0` with the support
  condition `q i = 0 → p i = 0`, unnormalised; `relEntropy_nonneg` and `relEntropy_eq_zero_iff`
  are Gibbs' inequality and its equality case on probability vectors, zero coordinates included.
* `mul_log_le_relEntropy` — the log-sum inequality.
* `relEntropy_uniform`, `shannonEntropy_le_log_card`, `shannonEntropy_eq_log_card_iff` — entropy
  is at most `log (card ι)`, with equality exactly at the uniform vector.
* `two_mul_sq_sub_le_relEntropy` — Pinsker's inequality for two outcomes: for `0 < p < 1` and
  `0 ≤ q ≤ 1`, `relEntropy ![q, 1 - q] ![p, 1 - p] ≥ 2 (q - p)²` (order LEAN-17). Each bound on
  `p` and `q` is needed: at `p = 0`, `q = 1/2` Lean's `log 0 = 0` gives `-0.347 < 0.5`, and the
  same at `p = 1`; at `p = 1/2`, `q = -1` or `q = 2` Lean's `log |x|` gives `2.079 < 4.5`.
  `relEntropy_fin_two` writes the two-outcome relative entropy out; the other two helpers are
  private.
* `relEntropy_softmax` — `relEntropy p (softmax x) = crossEntropy x p - shannonEntropy p` whenever
  `∑ p = 1`. On the open simplex this is `crossEntropy_sub_entropy` (`Simplex/CrossEntropy.lean`);
  zero and negative coordinates are what is new.

## Junk values (`ROADMAP.md` §1.11)

Under `Real.log 0 = 0`, `Real.log x = Real.log |x|` and `x / 0 = 0`, the term `p * log (p / q)`
has exactly one junk cell among meaningful inputs: `p > 0, q = 0`, where Lean returns `0` and the
true value is `+∞`. So `relEntropy (½, ½) (1, 0) = -(log 2) / 2 ≈ -0.3466`, and the support
hypothesis is what every inequality below needs. Enumerated numerically before any statement was
written; the enumeration and the random searches are recorded in round 18's fragment.

## Relation to Mathlib and to this library

Mathlib has no relative or Shannon entropy of a general finite vector — only the two-point and
`q`-ary cases `Real.binEntropy` and `Real.qaryEntropy`
(`Analysis/SpecialFunctions/BinaryEntropy.lean`); search commands and counts in `ROADMAP.md` §2.8.
It has the measure-theoretic counterparts, over `Measure α` and valued in `ℝ≥0∞`:
`InformationTheory.integral_llr_add_sub_measure_univ_nonneg` (the analogue of
`sum_sub_sum_le_relEntropy`), `InformationTheory.mul_log_le_toReal_klDiv` (log-sum),
`InformationTheory.klDiv_eq_zero_iff` (the equality case). The one-coordinate fact behind all of
them is Mathlib's `InformationTheory.klFun_nonneg`, `0 ≤ x → 0 ≤ x * log x + 1 - x`; it is proved
here from `Real.log_le_sub_one_of_pos` directly, because the module that defines `klFun` imports
measure theory. Routing a finite statement through a measure buys nothing at this size — the
judgement `Simplex/LogSumExp.lean` made first.

`Gibbs.sum_mul_log_div_nonneg`, `Gibbs.sum_mul_log_div_pos_of_ne` and
`Gibbs.neg_log_card_le_sum_mul_log` are the open-simplex special cases of the theorems below.
-/

open Finset Real

namespace ClassicalLean.Simplex

/-- The **Shannon entropy** of a finite vector of weights: `H(p) = -∑ i, p i * log (p i)`. -/
noncomputable def shannonEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  -∑ i, p i * Real.log (p i)

variable {ι : Type*} [Fintype ι]

/-- The **relative entropy** (Kullback–Leibler divergence) of `p` from `q`:
`∑ i, p i * log (p i / q i)`. Meaningful for `p, q ≥ 0` with `q i = 0 → p i = 0`; see the module
docstring for what Lean returns outside that domain. -/
noncomputable def relEntropy (p q : ι → ℝ) : ℝ :=
  ∑ i, p i * Real.log (p i / q i)

/-- One coordinate of `sum_sub_sum_le_relEntropy`: `a - b ≤ a * log (a / b)`. For `a, b > 0` this is
`log (b / a) ≤ b / a - 1`; the support hypothesis removes the junk cell `a > 0, b = 0`. -/
private theorem sub_le_mul_log_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b = 0 → a = 0) :
    a - b ≤ a * Real.log (a / b) := by
  rcases hb.eq_or_lt with hb0 | hb0
  · have ha0 : a = 0 := hab hb0.symm
    rw [ha0, ← hb0]
    simp
  · rcases ha.eq_or_lt with ha0 | ha0
    · rw [← ha0]
      simp only [zero_sub, zero_div, Real.log_zero, mul_zero, neg_nonpos]
      exact hb
    · have h := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
      have hinv : Real.log (a / b) = -Real.log (b / a) := by
        rw [← Real.log_inv, inv_div]
      have h2 : a * (b / a - 1) = b - a := by
        field_simp
      have h3 : a * Real.log (b / a) ≤ a * (b / a - 1) := mul_le_mul_of_nonneg_left h ha
      rw [hinv]
      linarith

/-- The equality case of `sub_le_mul_log_div`: under the same hypotheses, equality holds exactly
when `a = b`. For `a, b > 0` this is the strict inequality `log x < x - 1` for `x ≠ 1`. -/
private theorem mul_log_div_eq_sub_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : b = 0 → a = 0) : a * Real.log (a / b) = a - b ↔ a = b := by
  constructor
  · intro h
    rcases hb.eq_or_lt with hb0 | hb0
    · rw [← hb0, hab hb0.symm]
    · rcases ha.eq_or_lt with ha0 | ha0
      · rw [← ha0] at h
        simp only [zero_div, Real.log_zero, mul_zero, zero_sub] at h
        linarith
      · by_contra hne
        have hx : b / a ≠ 1 := fun h1 => hne ((div_eq_one_iff_eq ha0.ne').mp h1).symm
        have hlt := Real.log_lt_sub_one_of_pos (div_pos hb0 ha0) hx
        have hinv : Real.log (a / b) = -Real.log (b / a) := by
          rw [← Real.log_inv, inv_div]
        have h2 : a * (b / a - 1) = b - a := by
          field_simp
        have h3 : a * Real.log (b / a) < a * (b / a - 1) := mul_lt_mul_of_pos_left hlt ha0
        rw [hinv] at h
        linarith
  · rintro rfl
    rcases ha.eq_or_lt with ha0 | ha0
    · rw [← ha0]
      simp
    · rw [div_self ha0.ne', Real.log_one, mul_zero, sub_self]

/-- A vector with total `1` has a nonempty index type. -/
private theorem nonempty_of_sum_eq_one {p : ι → ℝ} (hp : ∑ i, p i = 1) : Nonempty ι := by
  by_contra h
  rw [not_nonempty_iff] at h
  rw [Finset.univ_eq_empty, Finset.sum_empty] at hp
  exact zero_ne_one hp

/-- **`∑ p - ∑ q ≤ relEntropy p q`**, for nonnegative `p` and `q` with `q i = 0 → p i = 0`, and no
normalisation. The finite form of Mathlib's
`InformationTheory.integral_llr_add_sub_measure_univ_nonneg`. Each hypothesis is needed: dropping
any one admits a counterexample. -/
theorem sum_sub_sum_le_relEntropy {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpq : ∀ i, q i = 0 → p i = 0) : ∑ i, p i - ∑ i, q i ≤ relEntropy p q := by
  rw [relEntropy, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i _ => sub_le_mul_log_div (hp i) (hq i) (hpq i)

/-- **The log-sum inequality**: `(∑ a) * log (∑ a / ∑ b) ≤ ∑ a i * log (a i / b i)` for nonnegative
`a` and `b` with `b i = 0 → a i = 0`. The finite form of Mathlib's
`InformationTheory.mul_log_le_toReal_klDiv`; proved from `sum_sub_sum_le_relEntropy` applied to `b`
rescaled to the total of `a`. -/
theorem mul_log_le_relEntropy {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hab : ∀ i, b i = 0 → a i = 0) :
    (∑ i, a i) * Real.log ((∑ i, a i) / ∑ i, b i) ≤ relEntropy a b := by
  have hA0 : 0 ≤ ∑ i, a i := Finset.sum_nonneg fun i _ => ha i
  have hB0 : 0 ≤ ∑ i, b i := Finset.sum_nonneg fun i _ => hb i
  have hbz : ∑ i, b i = 0 → ∀ i, a i = 0 := fun h i =>
    hab i ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => hb j).mp h i (Finset.mem_univ i))
  rcases hA0.eq_or_lt with hA | hA
  · have hz : ∀ i, a i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => ha j).mp hA.symm i (Finset.mem_univ i)
    rw [← hA, zero_mul, relEntropy]
    exact le_of_eq (Finset.sum_eq_zero fun i _ => by rw [hz i, zero_mul]).symm
  · rcases hB0.eq_or_lt with hB | hB
    · have hz := hbz hB.symm
      have : ∑ i, a i = 0 := Finset.sum_eq_zero fun i _ => hz i
      linarith
    · set c := (∑ i, a i) / ∑ i, b i with hc_def
      have hc : 0 < c := div_pos hA hB
      have key := sum_sub_sum_le_relEntropy ha (fun i => mul_nonneg (hb i) hc.le)
        (fun i h => hab i ((mul_eq_zero.mp h).resolve_right hc.ne'))
      have hsum : ∑ i, b i * c = ∑ i, a i := by
        rw [← Finset.sum_mul, hc_def]
        field_simp
      have hsplit : relEntropy a (fun i => b i * c) = relEntropy a b - (∑ i, a i) * Real.log c := by
        rw [relEntropy, relEntropy, Finset.sum_mul, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hai : a i = 0
        · rw [hai]
          simp
        · have hbi : b i ≠ 0 := fun h => hai (hab i h)
          rw [← div_div, Real.log_div (div_ne_zero hai hbi) hc.ne']
          ring
      rw [hsum, hsplit] at key
      linarith

/-- **Gibbs' inequality** on probability vectors, zero coordinates included: `0 ≤ relEntropy p q`
when `q i = 0 → p i = 0`. Without the support hypothesis it fails:
`relEntropy (½, ½) (1, 0) = -(log 2) / 2`. -/
theorem relEntropy_nonneg {p q : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1) (hpq : ∀ i, q i = 0 → p i = 0) :
    0 ≤ relEntropy p q := by
  have h := sum_sub_sum_le_relEntropy hp0 hq0 hpq
  rw [hp1, hq1, sub_self] at h
  exact h

/-- **The equality case of Gibbs' inequality**: on probability vectors with `q i = 0 → p i = 0`,
`relEntropy p q = 0` exactly when `p = q`. The support hypothesis is needed: without it
`relEntropy (0, 1) (1, 0) = 0`. -/
theorem relEntropy_eq_zero_iff {p q : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1) (hpq : ∀ i, q i = 0 → p i = 0) :
    relEntropy p q = 0 ↔ p = q := by
  constructor
  · intro h
    have hnn : ∀ i ∈ (Finset.univ : Finset ι),
        0 ≤ p i * Real.log (p i / q i) - (p i - q i) :=
      fun i _ => sub_nonneg.mpr (sub_le_mul_log_div (hp0 i) (hq0 i) (hpq i))
    have hrel : relEntropy p q = ∑ i, p i * Real.log (p i / q i) := rfl
    have hsum : ∑ i, (p i * Real.log (p i / q i) - (p i - q i)) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hp1, hq1, ← hrel, h]
      ring
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
    funext i
    exact (mul_log_div_eq_sub_iff (hp0 i) (hq0 i) (hpq i)).mp
      (sub_eq_zero.mp (hz i (Finset.mem_univ i)))
  · rintro rfl
    rw [relEntropy]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact (mul_log_div_eq_sub_iff (hp0 i) (hp0 i) (fun h => h)).mpr rfl |>.trans (sub_self _)

/-- **Relative entropy to the uniform vector** is `log (card ι) - shannonEntropy p`, whenever
`∑ p = 1` — negative coordinates included, since `Real.log (a * b) = Real.log a + Real.log b` needs
only `a, b ≠ 0`. -/
theorem relEntropy_uniform {p : ι → ℝ} (hp : ∑ i, p i = 1) :
    relEntropy p (fun _ => (Fintype.card ι : ℝ)⁻¹)
      = Real.log (Fintype.card ι) - shannonEntropy p := by
  have hne : Nonempty ι := nonempty_of_sum_eq_one hp
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hterm : ∀ i, p i * Real.log (p i / (Fintype.card ι : ℝ)⁻¹)
      = p i * Real.log (p i) + p i * Real.log (Fintype.card ι) := by
    intro i
    by_cases hpi : p i = 0
    · rw [hpi]
      simp
    · rw [div_inv_eq_mul, Real.log_mul hpi hn.ne']
      ring
  rw [relEntropy, shannonEntropy, Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
    ← Finset.sum_mul, hp, one_mul]
  ring

/-- The uniform vector is a probability vector with no zero coordinate — the three facts
`shannonEntropy_le_log_card` and `shannonEntropy_eq_log_card_iff` feed to Gibbs' inequality. -/
private theorem uniform_facts [Nonempty ι] :
    (∀ _i : ι, 0 ≤ (Fintype.card ι : ℝ)⁻¹) ∧ ∑ _i : ι, (Fintype.card ι : ℝ)⁻¹ = 1 ∧
      ∀ _i : ι, (Fintype.card ι : ℝ)⁻¹ ≠ 0 := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  refine ⟨fun _ => (inv_pos.mpr hn).le, ?_, fun _ => (inv_pos.mpr hn).ne'⟩
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **Entropy is at most `log (card ι)`** on probability vectors, zero coordinates included. Both
hypotheses are needed: `(-10, 5.5, 5.5)` sums to `1` and has entropy above `log 3`; `(0.625)` on a
one-point type is nonnegative and has entropy above `log 1 = 0`. -/
theorem shannonEntropy_le_log_card {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    shannonEntropy p ≤ Real.log (Fintype.card ι) := by
  have hne : Nonempty ι := nonempty_of_sum_eq_one hp1
  obtain ⟨hu0, hu1, hu⟩ := uniform_facts (ι := ι)
  have h := relEntropy_nonneg hp0 hp1 hu0 hu1 fun i h => absurd h (hu i)
  rw [relEntropy_uniform hp1] at h
  linarith

/-- **Equality in `shannonEntropy_le_log_card` holds exactly at the uniform vector.** -/
theorem shannonEntropy_eq_log_card_iff {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    shannonEntropy p = Real.log (Fintype.card ι) ↔ p = fun _ => (Fintype.card ι : ℝ)⁻¹ := by
  have hne : Nonempty ι := nonempty_of_sum_eq_one hp1
  obtain ⟨hu0, hu1, hu⟩ := uniform_facts (ι := ι)
  have hiff := relEntropy_eq_zero_iff hp0 hp1 hu0 hu1 fun i h => absurd h (hu i)
  rw [relEntropy_uniform hp1] at hiff
  rw [← hiff]
  constructor <;> intro h <;> linarith

/-- **Relative entropy to a softmax is cross-entropy minus entropy**, whenever `∑ p = 1`. On the
open simplex this is `crossEntropy_sub_entropy`; here zero and negative coordinates are allowed, and
`Nonempty ι` follows from `∑ p = 1` rather than being assumed. -/
theorem relEntropy_softmax (x : ι → ℝ) {p : ι → ℝ} (hp : ∑ i, p i = 1) :
    relEntropy p (softmax x) = crossEntropy x p - shannonEntropy p := by
  have hne : Nonempty ι := nonempty_of_sum_eq_one hp
  have hterm : ∀ i, p i * Real.log (p i / softmax x i)
      = p i * Real.log (p i) - p i * x i + p i * logSumExp x := by
    intro i
    by_cases hpi : p i = 0
    · rw [hpi]
      simp
    · rw [Real.log_div hpi (softmax_pos x i).ne', log_softmax]
      ring
  rw [relEntropy, crossEntropy, shannonEntropy, Finset.sum_congr rfl fun i _ => hterm i,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hp, one_mul]
  ring

/-- The two-outcome relative entropy, written out. -/
theorem relEntropy_fin_two (q p : ℝ) :
    relEntropy ![q, 1 - q] ![p, 1 - p] = q * log (q / p) + (1 - q) * log ((1 - q) / (1 - p)) := by
  simp [relEntropy, Fin.sum_univ_two]

/-- `a log (a / b) = a log a - a log b` for `b ≠ 0`, `a = 0` included. -/
private theorem mul_log_div_eq {a b : ℝ} (hb : b ≠ 0) :
    a * log (a / b) = a * log a - a * log b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [log_div ha hb, mul_sub]

/-- One side of two-outcome Pinsker, `p ≤ q`: the function
`t ↦ q log (q / t) + (1 - q) log ((1 - q) / (1 - t)) - 2 (q - t)²` falls on `[p, q]` to `0` at
`t = q`, because its derivative `(t - q) (1 - 4 t (1 - t)) / (t (1 - t))` is at most `0` there. -/
private theorem two_mul_sq_sub_le_of_le {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hpq : p ≤ q)
    (hq1 : q ≤ 1) :
    2 * (q - p) ^ 2 ≤ q * log (q / p) + (1 - q) * log ((1 - q) / (1 - p)) := by
  set C := q * log q + (1 - q) * log (1 - q)
  let G : ℝ → ℝ := fun t ↦ C - q * log t - (1 - q) * log (1 - t) - 2 * (q - t) ^ 2
  have hGp : G p = q * log (q / p) + (1 - q) * log ((1 - q) / (1 - p)) - 2 * (q - p) ^ 2 := by
    simp only [G, C, mul_log_div_eq hp0.ne', mul_log_div_eq (sub_pos.mpr hp1).ne']
    ring
  have hGq : G q = 0 := by simp only [G, C]; ring
  -- `(1 - q) log (1 - t)` is `0` when `q = 1`, and continuous on `t < 1` otherwise
  have hcont : ContinuousOn G (Set.Icc p q) := by
    have h1 : ContinuousOn (fun t : ℝ ↦ q * log t) (Set.Icc p q) :=
      continuousOn_const.mul (continuousOn_log.mono fun t ht ↦ (hp0.trans_le ht.1).ne')
    have h2 : ContinuousOn (fun t : ℝ ↦ (1 - q) * log (1 - t)) (Set.Icc p q) := by
      rcases eq_or_lt_of_le hq1 with rfl | hq
      · simp only [sub_self, zero_mul]; exact continuousOn_const
      · refine continuousOn_const.mul (ContinuousOn.log (by fun_prop) fun t ht ↦ ?_)
        linarith [ht.2]
    exact ((continuousOn_const.sub h1).sub h2).sub (by fun_prop)
  have hderiv : ∀ t ∈ Set.Ioo p q,
      HasDerivAt G (-(q / t) + (1 - q) / (1 - t) + 4 * (q - t)) t := by
    intro t ht
    have ht0 : 0 < t := hp0.trans ht.1
    have ht1 : 0 < 1 - t := by linarith [ht.2]
    have hl1 := (hasDerivAt_log ht0.ne').const_mul q
    have hl2 := ((hasDerivAt_id t).const_sub 1).log ht1.ne'
    have hl3 := ((hasDerivAt_id t).const_sub q).pow 2
    have := (((hasDerivAt_const t C).sub hl1).sub (hl2.const_mul (1 - q))).sub (hl3.const_mul 2)
    have hG : G = ((((fun _ ↦ C) - fun y ↦ q * log y) - fun y ↦ (1 - q) * log (1 - id y)) -
        fun y ↦ 2 * ((fun x ↦ q - id x) ^ 2) y) := by
      funext y; simp only [G, Pi.sub_apply, Pi.pow_apply, id]
    rw [hG]
    convert this using 1
    simp only [id, Nat.cast_ofNat]
    field_simp
    ring
  have hanti : AntitoneOn G (Set.Icc p q) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc p q) hcont ?_ ?_
    · rw [interior_Icc]; exact fun t ht ↦ (hderiv t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      have ht0 : 0 < t := hp0.trans ht.1
      have ht1 : 0 < 1 - t := by linarith [ht.2]
      rw [(hderiv t ht).deriv]
      have key : -(q / t) + (1 - q) / (1 - t) + 4 * (q - t) =
          (t - q) * (1 - 4 * (t * (1 - t))) / (t * (1 - t)) := by
        field_simp; ring
      rw [key]
      apply div_nonpos_of_nonpos_of_nonneg _ (mul_pos ht0 ht1).le
      apply mul_nonpos_of_nonpos_of_nonneg (by linarith [ht.2])
      nlinarith [sq_nonneg (2 * t - 1)]
  have := hanti ⟨le_rfl, hpq⟩ ⟨hpq, le_rfl⟩ hpq
  rw [hGp, hGq] at this
  linarith

/-- **Pinsker's inequality for two outcomes.** For `0 < p < 1` and `0 ≤ q ≤ 1`, the relative entropy
of `(q, 1 - q)` to `(p, 1 - p)` is at least `2 (q - p)²`. -/
theorem two_mul_sq_sub_le_relEntropy {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) : 2 * (q - p) ^ 2 ≤ relEntropy ![q, 1 - q] ![p, 1 - p] := by
  rw [relEntropy_fin_two]
  rcases le_total p q with hpq | hqp
  · exact two_mul_sq_sub_le_of_le hp0 hp1 hpq hq1
  · have h := two_mul_sq_sub_le_of_le (p := 1 - p) (q := 1 - q) (by linarith) (by linarith)
      (by linarith) (by linarith)
    simp only [sub_sub_cancel] at h
    nlinarith [h]

end ClassicalLean.Simplex

/-- The hypotheses of `two_mul_sq_sub_le_relEntropy` hold together: `p = 1/2` lies strictly
between `0` and `1`, and `q = 1/4` lies in `[0, 1]` without being an end point. -/
example := ClassicalLean.Simplex.two_mul_sq_sub_le_relEntropy (p := 1 / 2) (q := 1 / 4)
  (by norm_num) (by norm_num) (by norm_num) (by norm_num)
