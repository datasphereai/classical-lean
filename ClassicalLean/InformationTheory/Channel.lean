/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.InformationTheory.Entropy
import Mathlib.Analysis.Convex.DoublyStochasticMatrix

/-!
# Finite channels and the data-processing inequality

A channel from `ι` to `κ` is a matrix `W : Matrix ι κ ℝ` with nonnegative entries and rows summing
to `1`: row `i` is the output distribution for input `i`, and an input distribution `p` is sent to
`p ᵥ* W`, whose `j`-th entry is `∑ i, p i * W i j`. The two conditions are explicit hypotheses:
Mathlib's `Matrix.rowStochastic` is square, `Matrix n n R` with `[DecidableEq n]`, and a channel
need not be.

* `sum_vecMul_eq_sum`, `vecMul_nonneg` — a channel preserves the total and nonnegativity, so it
  sends probability vectors to probability vectors. The total needs only the row sums.
* `relEntropy_vecMul_le` — **the data-processing inequality**: passing both arguments through the
  same channel does not increase relative entropy. Proved column by column from the log-sum
  inequality `mul_log_le_relEntropy`.
* `shannonEntropy_le_shannonEntropy_vecMul` — entropy does not decrease under a doubly stochastic
  matrix: the data-processing inequality at the uniform vector, which a doubly stochastic matrix
  fixes.
* `sq_sum_abs_sub_le_two_mul_relEntropy` — **Pinsker's inequality** (order LEAN-18):
  `(∑ i, |p i - q i|)² ≤ 2 relEntropy p q` for probability vectors `p`, `q` with
  `q i = 0 → p i = 0`. The channel with two outputs that reports whether `p i ≥ q i` sends `p` and
  `q` to two-outcome vectors whose distance is the whole of `∑ |p - q|`, and the two-outcome case
  is `two_mul_sq_sub_le_relEntropy` (`InformationTheory/Entropy`). Each of the five hypotheses is
  needed (order LEAN-18, check C10; each case keeps the other four): `p = (3/2, -1/2)`,
  `q = (1/2, 1/2)` gives `4 > 3.296`; `p = (0, 0)`, `q = (1/2, 1/2)` gives `1 > 0`;
  `p = (1/2, 1/2)`, `q = (3/2, -1/2)` gives `4 > -1.099`; `p = (1/2, 1/2)`, `q = (1, 1)` gives
  `1 > -1.386`; and without support `p = (1/2, 1/2)`, `q = (1, 0)` gives `1 > -0.693`. The route
  is the textbook one (Cover and Thomas, *Elements of Information Theory*, 2nd ed., Lemma
  11.6.1). A Pinsker inequality in random-variable form outside Mathlib is recorded in
  `ROADMAP.md` (prior art, `tvNorm_le_sqrt_klDiv`).

## Hypotheses (`ROADMAP.md` §1.11)

The data-processing inequality needs `p, q ≥ 0`, `q i = 0 → p i = 0`, and a channel — and nothing
else: neither vector need be normalised, and `q` need not be positive. Each hypothesis is needed.
Without support it fails at `p = (½, ½)`, `q = (1, 0)`, `W = [[1, 0], [½, ½]]`: the left side is
`(3/4) * log (3/4) ≈ -0.216` and the right side `-(log 2)/2 ≈ -0.347`. The doubly stochastic
theorem needs both row and column sums: `W = [[1, 0], [1, 0]]` (rows only) sends `(½, ½)` from
entropy `log 2` to `0`, and `W = [[1, 1], [0, 0]]` (columns only) sends `(0.9, 0.1)` from entropy
`≈ 0.325` to `≈ 0.190`.

## Relation to Mathlib

Mathlib at v4.34.0 proves the data-processing inequality for Markov kernels between measures,
`InformationTheory.klDiv_comp_right_le` (`InformationTheory/KullbackLeibler/DataProcessing.lean`);
it was absent at `8f07524533`, this library's pin before order 0923. That is the measure form,
valued in `ℝ≥0∞`, and Mathlib's `klDiv μ ν` carries the mass term `ν.real univ - μ.real univ`. A
finite channel is a Markov kernel on a finite type, so the bridge — for `p, q ≥ 0` with
`q i = 0 → p i = 0`, `(klDiv μ_p μ_q).toReal = relEntropy p q + ∑ i, q i - ∑ i, p i` — makes
`relEntropy_vecMul_le` a corollary of it, since a channel preserves both totals
(`sum_vecMul_eq_sum`). Without the mass term the bridge is false off equal totals (`p = (1)`,
`q = (2)`: `relEntropy = -log 2`, `toReal = 1 - log 2`); without support `klDiv = ∞`, whose
`toReal` is `0`. The bridge is proved, in `ClassicalLean.Probability.RelativeEntropyGrowth` (order
LEAN-21, item 39 of the library plan): `toReal_klDiv_vecMeasure`, and the inequality again from
Mathlib's as `relEntropy_vecMul_le_of_klDiv`. The direct proof here stays, since that module
imports this one.
-/

open Finset Real
open scoped Matrix

namespace ClassicalLean.Simplex

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **A channel preserves the total**: `∑ j, (p ᵥ* W) j = ∑ i, p i`. Only the row sums are used. -/
theorem sum_vecMul_eq_sum {p : ι → ℝ} {W : Matrix ι κ ℝ} (hW1 : ∀ i, ∑ j, W i j = 1) :
    ∑ j, (p ᵥ* W) j = ∑ i, p i := by
  simp only [Matrix.vecMul_apply_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, hW1 i, mul_one]

omit [Fintype κ] in
/-- **A nonnegative matrix preserves nonnegativity.** -/
theorem vecMul_nonneg {p : ι → ℝ} {W : Matrix ι κ ℝ} (hW0 : ∀ i j, 0 ≤ W i j)
    (hp0 : ∀ i, 0 ≤ p i) (j : κ) : 0 ≤ (p ᵥ* W) j := by
  rw [Matrix.vecMul_apply_eq_sum]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hp0 i) (hW0 i j)

/-- **The data-processing inequality** for a finite channel: `relEntropy (p ᵥ* W) (q ᵥ* W) ≤
relEntropy p q` for nonnegative `p`, `q` with `q i = 0 → p i = 0`. The finite form of Mathlib's
`InformationTheory.klDiv_comp_right_le` (v4.34.0). -/
theorem relEntropy_vecMul_le {p q : ι → ℝ} {W : Matrix ι κ ℝ} (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i) (hpq : ∀ i, q i = 0 → p i = 0) (hW0 : ∀ i j, 0 ≤ W i j)
    (hW1 : ∀ i, ∑ j, W i j = 1) : relEntropy (p ᵥ* W) (q ᵥ* W) ≤ relEntropy p q := by
  have hcol : ∀ j, (p ᵥ* W) j * Real.log ((p ᵥ* W) j / (q ᵥ* W) j)
      ≤ ∑ i, p i * W i j * Real.log (p i * W i j / (q i * W i j)) := by
    intro j
    have h := mul_log_le_relEntropy (a := fun i => p i * W i j) (b := fun i => q i * W i j)
      (fun i => mul_nonneg (hp i) (hW0 i j)) (fun i => mul_nonneg (hq i) (hW0 i j))
      (fun i h => by
        rcases mul_eq_zero.mp h with h' | h'
        · rw [hpq i h', zero_mul]
        · rw [h', mul_zero])
    rw [Matrix.vecMul_apply_eq_sum, Matrix.vecMul_apply_eq_sum]
    exact h
  have hterm : ∀ i j, p i * W i j * Real.log (p i * W i j / (q i * W i j))
      = W i j * (p i * Real.log (p i / q i)) := by
    intro i j
    by_cases hW : W i j = 0
    · rw [hW]
      simp
    · rw [mul_div_mul_right _ _ hW]
      ring
  calc relEntropy (p ᵥ* W) (q ᵥ* W)
      = ∑ j, (p ᵥ* W) j * Real.log ((p ᵥ* W) j / (q ᵥ* W) j) := rfl
    _ ≤ ∑ j, ∑ i, p i * W i j * Real.log (p i * W i j / (q i * W i j)) :=
        Finset.sum_le_sum fun j _ => hcol j
    _ = ∑ i, p i * Real.log (p i / q i) := by
        simp only [hterm]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_mul, hW1 i, one_mul]
    _ = relEntropy p q := rfl

/-- **Entropy does not decrease under a doubly stochastic matrix.** The data-processing inequality
at the uniform vector, which a doubly stochastic matrix fixes, read through `relEntropy_uniform`.
`[DecidableEq ι]` is Mathlib's, for `doublyStochastic`, and is scoped to this statement alone. -/
theorem shannonEntropy_le_shannonEntropy_vecMul [DecidableEq ι] {p : ι → ℝ} {W : Matrix ι ι ℝ}
    (hW : W ∈ doublyStochastic ℝ ι) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    shannonEntropy p ≤ shannonEntropy (p ᵥ* W) := by
  obtain ⟨hW0, hW1, hWc⟩ := mem_doublyStochastic_iff_sum.mp hW
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hp1
    exact zero_ne_one hp1
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have huW : (fun _ => (Fintype.card ι : ℝ)⁻¹) ᵥ* W = fun _ => (Fintype.card ι : ℝ)⁻¹ := by
    funext j
    rw [Matrix.vecMul_apply_eq_sum, ← Finset.mul_sum, hWc j, mul_one]
  have hpW1 : ∑ i, (p ᵥ* W) i = 1 := by rw [sum_vecMul_eq_sum hW1, hp1]
  have h := relEntropy_vecMul_le (q := fun _ => (Fintype.card ι : ℝ)⁻¹) hp0
    (fun _ => (inv_pos.mpr hn).le) (fun _ h => absurd h (inv_pos.mpr hn).ne') hW0 hW1
  rw [huW, relEntropy_uniform hpW1, relEntropy_uniform hp1] at h
  linarith

/-- **Pinsker's inequality.** For probability vectors `p` and `q` with `q i = 0 → p i = 0`, the
square of the total distance `∑ i, |p i - q i|` is at most twice the relative entropy of `p` to `q`.
Pass both through the channel with two outputs that reports whether `p i ≥ q i`: the distance
becomes `2 (P(A) - Q(A))`, with `A` the set where `p ≥ q`, the relative entropy can only fall
(`relEntropy_vecMul_le`), and the two-outcome case `two_mul_sq_sub_le_relEntropy` finishes when
`0 < Q(A) < 1`; otherwise `P(A) = Q(A)` and the left side is `0`. The textbook route (Cover and
Thomas, *Elements of Information Theory*, 2nd ed., Lemma 11.6.1). -/
theorem sq_sum_abs_sub_le_two_mul_relEntropy {p q : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1) (hpq : ∀ i, q i = 0 → p i = 0) :
    (∑ i, |p i - q i|) ^ 2 ≤ 2 * relEntropy p q := by
  -- the chances of the set `A` where `p ≥ q`
  set PA := ∑ i, if q i ≤ p i then p i else 0
  set QA := ∑ i, if q i ≤ p i then q i else 0 with hQA
  have habs : ∑ i, |p i - q i| = 2 * (PA - QA) := by
    have h : ∀ i, |p i - q i|
        = 2 * ((if q i ≤ p i then p i else 0) - (if q i ≤ p i then q i else 0)) - (p i - q i) := by
      intro i
      split_ifs with h
      · rw [abs_of_nonneg (sub_nonneg.mpr h)]; ring
      · rw [abs_of_neg (by linarith [not_le.mp h])]; ring
    simp_rw [h]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      hp1, hq1]
    ring
  have hrel0 : 0 ≤ relEntropy p q := relEntropy_nonneg hp0 hp1 hq0 hq1 hpq
  have hQA0 : 0 ≤ QA := Finset.sum_nonneg fun i _ ↦ by split_ifs <;> simp [hq0 i]
  have hQA1 : QA ≤ 1 := hq1 ▸ Finset.sum_le_sum fun i _ ↦ by split_ifs <;> simp [hq0 i]
  have hPA0 : 0 ≤ PA := Finset.sum_nonneg fun i _ ↦ by split_ifs <;> simp [hp0 i]
  have hPA1 : PA ≤ 1 := hp1 ▸ Finset.sum_le_sum fun i _ ↦ by split_ifs <;> simp [hp0 i]
  by_cases hQ : 0 < QA ∧ QA < 1
  · -- the two-column channel that reports whether `p i ≥ q i`
    let W : Matrix ι (Fin 2) ℝ := fun i ↦ ![if q i ≤ p i then 1 else 0, if q i ≤ p i then 0 else 1]
    have hW0 : ∀ i j, 0 ≤ W i j := fun i j ↦ by
      fin_cases j <;> simp only [W] <;> split_ifs <;> simp
    have hW1 : ∀ i, ∑ j, W i j = 1 := fun i ↦ by
      simp only [W, Fin.sum_univ_two]; split_ifs <;> simp
    have hvec : ∀ r : ι → ℝ, (∑ i, r i = 1) →
        r ᵥ* W = ![∑ i, if q i ≤ p i then r i else 0, 1 - ∑ i, if q i ≤ p i then r i else 0] := by
      intro r hr
      have h0 : (r ᵥ* W) 0 = ∑ i, if q i ≤ p i then r i else 0 := by
        simp only [Matrix.vecMul, dotProduct, W]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        by_cases h : q i ≤ p i <;> simp [h]
      have h1 : (r ᵥ* W) 1 = ∑ i, r i - ∑ i, if q i ≤ p i then r i else 0 := by
        simp only [Matrix.vecMul, dotProduct, W]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        by_cases h : q i ≤ p i <;> simp [h]
      funext j
      fin_cases j
      · simpa using h0
      · simpa [hr] using h1
    have hdpi := relEntropy_vecMul_le hp0 hq0 hpq hW0 hW1
    rw [hvec p hp1, hvec q hq1] at hdpi
    have h2 := two_mul_sq_sub_le_relEntropy hQ.1 hQ.2 hPA0 hPA1
    rw [habs]
    linarith
  · -- `QA` is `0` or `1`, and then `PA = QA`: the left side is `0`
    have hPQ : PA = QA := by
      rcases not_and_or.mp hQ with h | h
      · have hQ0 : QA = 0 := le_antisymm (not_lt.mp h) hQA0
        have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ by
          split_ifs <;> simp [hq0 i]).mp hQ0
        rw [hQ0]
        refine Finset.sum_eq_zero fun i hi ↦ ?_
        have := hz i hi
        split_ifs at this ⊢ with hle
        · exact hpq i this
        · rfl
      · have hQ1 : QA = 1 := le_antisymm hQA1 (not_lt.mp h)
        -- the rest of `q` vanishes, so no `i` has `p i < q i`
        have hrest : ∑ i, (if q i ≤ p i then 0 else q i) = 0 := by
          have : ∑ i, (if q i ≤ p i then 0 else q i) = ∑ i, q i - QA := by
            rw [hQA, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            split_ifs <;> ring
          rw [this, hq1, hQ1, sub_self]
        have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ by
          split_ifs <;> simp [hq0 i]).mp hrest
        have hall : ∀ i, q i ≤ p i := fun i ↦ by
          by_contra hlt
          have := hz i (Finset.mem_univ i)
          simp only [hlt, ↓reduceIte] at this
          exact hlt (this ▸ hp0 i)
        have : PA = ∑ i, p i := Finset.sum_congr rfl fun i _ ↦ by simp [hall i]
        rw [this, hp1, hQ1]
    rw [habs, hPQ, sub_self, mul_zero]
    linarith

end ClassicalLean.Simplex

/-- The hypotheses of `sq_sum_abs_sub_le_two_mul_relEntropy` hold together: on two symbols, `p =
(1/4, 3/4)` and `q = (1/2, 1/2)` are probability vectors, and `q` is never `0`, so `p` has support
where `q` does. -/
example := ClassicalLean.Simplex.sq_sum_abs_sub_le_two_mul_relEntropy (ι := Fin 2)
  (p := ![1 / 4, 3 / 4]) (q := ![1 / 2, 1 / 2])
  (fun i ↦ by fin_cases i <;> norm_num) (by simp [Fin.sum_univ_two]; norm_num)
  (fun i ↦ by fin_cases i <;> norm_num) (by simp [Fin.sum_univ_two]; norm_num)
  (fun i h ↦ by fin_cases i <;> simp_all)
