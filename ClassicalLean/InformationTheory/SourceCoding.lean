/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.InformationTheory.Entropy
import Mathlib.InformationTheory.Coding.Kraft

/-!
# Shannon's source coding bound

A code gives each symbol `i` (with chance `p i`) a word `c i` over an alphabet `α` of `D` letters.
If the code is uniquely decodable, its mean word length is at least the entropy in base `D`:
`H(p) ≤ (∑ i, p i · |c i|) · log D`.

* `shannonEntropy_le_sum_mul_length_of_kraft`: any lengths `ℓ i` whose Kraft sum `∑ D^(-ℓ i)` is
  at most `1` have `H(p) ≤ (∑ i, p i ℓ i) · log D`, for a probability vector `p`.
* `shannonEntropy_le_sum_mul_length`: so for every injective code whose set of words is uniquely
  decodable (Shannon's source coding theorem, the lower bound).
* `shannonEntropy_le_sum_mul_length_of_isPrefixFree`: and for every injective prefix-free code.

The proof joins Mathlib's coding theory to this library's entropy: the Kraft–McMillan inequality
(`InformationTheory.IsUniquelyDecodable.finsetSum_one_div_card_pow_length_le_one`) for a uniquely
decodable code, or Kraft's inequality
(`InformationTheory.IsPrefixFree.finsetSum_one_div_card_pow_length_le_one`, which allows the empty
word) for a prefix-free one, gives `∑ q ≤ 1` for `q i = D^(-|c i|)`, and the unnormalised Gibbs
inequality (`Entropy.sum_sub_sum_le_relEntropy`) gives `1 - ∑ q ≤ relEntropy p q`, which is
`-H(p) + (∑ p i |c i|) log D`. The unnormalised form is the one that applies, since `q` need not
sum to `1`.

Each named hypothesis of the two main theorems is needed (order LEAN-17's checks, line C8).
Without injectivity: three symbols all coded `a` over two letters, uniform, give `H = 1.099`
against `0.693`. Without unique decodability: the words `a, b, aa, ab`, uniform, give `1.386`
against `1.040`. Without `∑ p = 1`: `p = (1/e, 1/e)` with words `a, b` gives `0.736` against
`0.510`. Without `0 ≤ p`: `p = (2, -1)` with words `a, bbbbb` gives `-1.386` against `-2.079`
(Lean's `log |x|`).
The alphabet need not be nonempty for the two main theorems (review r8 of order LEAN-17); only the
helper uses it, since an empty alphabet makes every Kraft sum `0` under `1 / 0 = 0`. The helper's
Kraft hypothesis is needed too: lengths `0, 0` over two letters, uniform, give `0.693` against `0`.

## What Mathlib provides

Kraft's and McMillan's inequalities (`InformationTheory/Coding/Kraft.lean`,
`KraftMcMillan.lean`, `PrefixFree.lean`). Mathlib v4.34.0 has no entropy of a finite vector and
no source coding statement: `source coding`, `noiseless coding`, `expected length` and
`entropy.*length` give no hits (order LEAN-17's plan, section 5).
-/

open Finset Real

namespace ClassicalLean.Simplex

variable {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty α]

/-- If the Kraft sum of the codeword lengths is at most `1`, the mean length times `log D` is at
least the entropy. -/
theorem shannonEntropy_le_sum_mul_length_of_kraft {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (ℓ : ι → ℕ)
    (hkraft : ∑ i, (1 / (Fintype.card α : ℝ)) ^ ℓ i ≤ 1) :
    shannonEntropy p ≤ (∑ i, p i * ℓ i) * Real.log (Fintype.card α) := by
  set D : ℝ := (Fintype.card α : ℝ)
  have hD : 0 < D := Nat.cast_pos.mpr (Fintype.card_pos (α := α))
  set q : ι → ℝ := fun i ↦ (1 / D) ^ ℓ i
  have hq : ∀ i, 0 < q i := fun i ↦ pow_pos (one_div_pos.mpr hD) _
  have h := sum_sub_sum_le_relEntropy hp0 (fun i ↦ (hq i).le) fun i h ↦ absurd h (hq i).ne'
  have hrel : relEntropy p q = -shannonEntropy p + (∑ i, p i * ℓ i) * Real.log D := by
    rw [relEntropy, shannonEntropy, sum_mul, neg_neg, ← sum_add_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rcases eq_or_ne (p i) 0 with h0 | h0
    · simp [h0]
    · rw [Real.log_div h0 (hq i).ne', Real.log_pow, one_div, Real.log_inv]
      ring
  rw [hrel, hp1] at h
  linarith

/-- **Shannon's source coding bound.** A uniquely decodable code `c` over an alphabet of `D`
letters (injective, its codewords a uniquely decodable set) has mean codeword length at least
`H(p) / log D`: `H(p) ≤ (∑ i, p i · |c i|) · log D`. -/
theorem shannonEntropy_le_sum_mul_length {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    {c : ι → List α} (hc : Function.Injective c)
    (hud : InformationTheory.IsUniquelyDecodable (Set.range c)) :
    shannonEntropy p ≤ (∑ i, p i * (c i).length) * Real.log (Fintype.card α) := by
  classical
  refine shannonEntropy_le_sum_mul_length_of_kraft hp0 hp1 (fun i ↦ (c i).length) ?_
  have hS : ((univ.image c : Finset (List α)) : Set (List α)) = Set.range c := by simp
  have := (hS ▸ hud).finsetSum_one_div_card_pow_length_le_one
  rwa [sum_image fun i _ j _ h ↦ hc h] at this

/-- **The source coding bound for a prefix-free code.** The same bound when the codewords form a
prefix-free set, the empty word allowed (Mathlib's Kraft inequality, which needs no condition on
it). -/
theorem shannonEntropy_le_sum_mul_length_of_isPrefixFree {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) {c : ι → List α} (hc : Function.Injective c)
    (hpf : InformationTheory.IsPrefixFree (Set.range c)) :
    shannonEntropy p ≤ (∑ i, p i * (c i).length) * Real.log (Fintype.card α) := by
  classical
  refine shannonEntropy_le_sum_mul_length_of_kraft hp0 hp1 (fun i ↦ (c i).length) ?_
  have hS : ((univ.image c : Finset (List α)) : Set (List α)) = Set.range c := by simp
  have := (hS ▸ hpf).finsetSum_one_div_card_pow_length_le_one
  rwa [sum_image fun i _ j _ h ↦ hc h] at this

end ClassicalLean.Simplex
