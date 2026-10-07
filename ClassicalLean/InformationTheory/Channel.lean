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
`q i = 0 → p i = 0`, `(klDiv μ_p μ_q).toReal = relEntropy p q + ∑ i, q i - ∑ i, p i` — would make
`relEntropy_vecMul_le` a corollary of it, since a channel preserves both totals
(`sum_vecMul_eq_sum`). Without the mass term the bridge is false off equal totals (`p = (1)`,
`q = (2)`: `relEntropy = -log 2`, `toReal = 1 - log 2`); without support `klDiv = ∞`, whose
`toReal` is `0`. The bridge is recorded in `HANDOFF.md` §3 as next.
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

end ClassicalLean.Simplex
