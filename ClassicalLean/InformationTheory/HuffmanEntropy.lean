/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.InformationTheory.Huffman

/-!
# Huffman's code is within one bit of the entropy

For weights `p : ι → ℝ` on a finite set of symbols with `∑ i, p i = 1`, Huffman's binary codeword
lengths `huffmanLength p` (`ClassicalLean.InformationTheory.Huffman`) have mean length
`∑ i, p i * huffmanLength p i` between the entropy in bits and one bit more:

* `le_sum_mul_huffmanLength` — `shannonEntropy p / Real.log 2 ≤ ∑ i, p i * huffmanLength p i`,
  for nonnegative weights.
* `sum_mul_huffmanLength_lt` — `∑ i, p i * huffmanLength p i < shannonEntropy p / Real.log 2 + 1`,
  for positive weights.

Bridge row 160 of MATH-PLAN-library-2's bridges file (order CLOUD-MATH-4), stated and proved by the
Claude Code cloud session of that order from the row's sketch; no draft. `shannonEntropy` is the
library's entropy in nats (`ClassicalLean.Simplex.shannonEntropy`), so dividing by `log 2` gives
bits. The lengths are natural numbers and enter the mean through the cast `ℕ → ℝ`.

Wider than the row, as order CLOUD-MATH-4's table asks: the row asks every `p i > 0` for both
sides; the lower side needs only `p i ≥ 0` (Shannon's bound allows zero weights), so it is stated
with that.

The proof. Take the two-letter alphabet `Bool` (`Fintype.card Bool = 2`). `huffman_optimal` gives an
injective prefix-free code `c : ι → List Bool` with Huffman's lengths whose mean length is at most
that of every injective prefix-free code. The lower side is Shannon's bound for `c`,
`shannonEntropy_le_sum_mul_length_of_isPrefixFree`, divided by `log 2 > 0`. The upper side compares
`c`, by its optimality, with the code of `exists_isPrefixFree_sum_mul_length_lt` (Shannon's
lengths), whose mean length is below `shannonEntropy p / log 2 + 1`.
-/

open Finset ClassicalLean.Simplex ClassicalLean.InformationTheory.Huffman

namespace ClassicalLean.InformationTheory.HuffmanEntropy

/-- **Huffman's mean length is at least the entropy in bits.** For nonnegative weights `p` with
`∑ i, p i = 1`, `shannonEntropy p / log 2 ≤ ∑ i, p i * huffmanLength p i`. -/
theorem le_sum_mul_huffmanLength {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    shannonEntropy p / Real.log 2 ≤ ∑ i, p i * (huffmanLength p i : ℝ) := by
  obtain ⟨c, hinj, hpf, hlen, -⟩ := huffman_optimal (α := Bool) Fintype.card_bool hp0
  have h := shannonEntropy_le_sum_mul_length_of_isPrefixFree hp0 hp1 hinj hpf
  rw [Fintype.card_bool, Nat.cast_ofNat] at h
  simp only [hlen] at h
  exact (div_le_iff₀ (Real.log_pos one_lt_two)).mpr h

/-- **Huffman's mean length is less than one bit above the entropy.** For positive weights `p`
with `∑ i, p i = 1`, `∑ i, p i * huffmanLength p i < shannonEntropy p / log 2 + 1`. -/
theorem sum_mul_huffmanLength_lt {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → ℝ}
    (hp0 : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1) :
    ∑ i, p i * (huffmanLength p i : ℝ) < shannonEntropy p / Real.log 2 + 1 := by
  obtain ⟨c, -, -, hlen, hopt⟩ :=
    huffman_optimal (α := Bool) Fintype.card_bool fun i => (hp0 i).le
  obtain ⟨c', hinj', hpf', hlt⟩ :=
    exists_isPrefixFree_sum_mul_length_lt (α := Bool) hp0 hp1 (by rw [Fintype.card_bool])
  rw [Fintype.card_bool, Nat.cast_ofNat] at hlt
  have h := hopt c' hinj' hpf'
  simp only [hlen] at h
  linarith

end ClassicalLean.InformationTheory.HuffmanEntropy

/-- The hypotheses of `le_sum_mul_huffmanLength` hold together: three symbols (`ι = Fin 3`) with
the weights `p = (1/2, 1/3, 1/6)`, all positive and summing to `1`, not uniform and not all
powers of `1/2`, so the bound is strict: the entropy is about `1.459` bits and Huffman's lengths
`(1, 2, 2)` have mean `3/2`. -/
example := ClassicalLean.InformationTheory.HuffmanEntropy.le_sum_mul_huffmanLength (ι := Fin 3)
    (p := ![1 / 2, 1 / 3, 1 / 6]) (fun i => by fin_cases i <;> norm_num)
    (by rw [Fin.sum_univ_three]; norm_num)

/-- The hypotheses of `sum_mul_huffmanLength_lt` hold together: three symbols (`ι = Fin 3`) with
the weights `p = (1/2, 1/3, 1/6)`, all positive and summing to `1`, not uniform and not all
powers of `1/2`: Huffman's mean length `3/2` lies strictly between the entropy, about `1.459` bits,
and one bit more, about `2.459`. -/
example := ClassicalLean.InformationTheory.HuffmanEntropy.sum_mul_huffmanLength_lt (ι := Fin 3)
    (p := ![1 / 2, 1 / 3, 1 / 6]) (fun i => by fin_cases i <;> norm_num)
    (by rw [Fin.sum_univ_three]; norm_num)
