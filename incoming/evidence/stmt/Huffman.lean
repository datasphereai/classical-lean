/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.InformationTheory.SourceCoding

/-!
# Optimality of Huffman's code

Binary Huffman coding of the symbols `ι` with weights `p`: repeatedly merge the two lightest
symbols into one, whose weight is the sum of theirs, and give each of the two merged symbols the
codeword length of the merged one plus one.

* `huffmanLength` — Huffman's codeword lengths for the weights `p`, defined by the recursion
  `huffAux` on finite sets of symbols (`Fintype.card ι` steps of the recursion; each step with
  at least two symbols left merges the two lightest, which `pick` chooses).
* `huffman_optimal` — order CLOUD-MATH-2, item 153 of MATH-PLAN-library-2: for nonnegative
  weights `p` and a two-letter alphabet `α`, some injective prefix-free code `c : ι → List α` has
  Huffman's lengths, and its mean length `∑ i, p i * (c i).length` is at most that of every
  injective prefix-free code.

Wider than the plan's row, by this session's reading (the draft's last review, as the order's table
gives it: GENERALIZED): the row says Huffman's code has the least mean length among prefix-free
codes; the theorem also gives the code (an injective prefix-free code with Huffman's lengths
exists), and the weights need only be nonnegative, not sum to `1`.

The proof. Huffman's lengths have Kraft sum at most `1` (`huffAux_kraft`, by induction on the
number of symbols: splitting the merged symbol back into two of one more length keeps the sum,
`kraft_mergeLen`), so the library's converse of Kraft's inequality
(`ClassicalLean.Simplex.exists_isPrefixFree_length_eq`) gives an injective prefix-free code with
those lengths. Optimality (`huffAux_opt`, by the same induction): lengths with Kraft sum at most
`1` can be rearranged by two exchanges (`Equiv.swap`), without raising the cost, so that the two
lightest symbols get the two largest lengths, and then the two can be merged into one symbol of one
less length, with Kraft sum still at most `1` and cost, plus the two weights, at most the cost
before (`reduce_step`, `merge_step`); Huffman's recursion pays exactly the two weights at that step
(`cost_mergeLen`). The lengths of every prefix-free code pass Kraft's test (Mathlib's
`InformationTheory.IsPrefixFree.finsetSum_one_div_card_pow_length_le_one`).

The proof is the draft `d153-r1-s2` (written by Claude Opus 5.5 through the Anthropic Batch API,
the lane's order API-CREDIT-1), adapted by the Claude Code cloud session that landed it (order
CLOUD-MATH-2): every declaration in the namespace `ClassicalLean.InformationTheory.Huffman` (the
draft had the helpers in `ClassicalLean.Huffman` and `huffman_optimal` outside any namespace), the
helpers' `variable` line in a section closed before `huffman_optimal`, whose own binders are the
draft's; docstrings; `omit [DecidableEq ι] in` on `exists_pair` (with `classical` in its proof)
and on `pick_spec`, so the private `pick`, whose value never used the instance, no longer takes
it (`huffAux` and `huffmanLength` take it, as in the draft, for `Finset.erase`); `dite_eq_left`
and `dite_eq_right` for the deprecated `dif_pos` and `dif_neg`; `push Not` for the deprecated
`push_neg`.
-/

open Finset

namespace ClassicalLean.InformationTheory.Huffman

section Recursion

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- Two distinct elements of `s`, the first of least weight, the second of least weight among
the rest. -/
private theorem exists_pair (w : ι → ℝ) (s : Finset ι) (h : 2 ≤ s.card) :
    ∃ ab : ι × ι, ab.1 ∈ s ∧ ab.2 ∈ s ∧ ab.1 ≠ ab.2 ∧ (∀ x ∈ s, w ab.1 ≤ w x) ∧
      ∀ x ∈ s, x ≠ ab.1 → w ab.2 ≤ w x := by
  sorry

/-- The two symbols Huffman's step merges: a lightest symbol of `s` and a lightest of the rest. -/
private noncomputable def pick (w : ι → ℝ) (s : Finset ι) (h : 2 ≤ s.card) : ι × ι :=
  Classical.choose (exists_pair w s h)

omit [DecidableEq ι] in
/-- What `pick` gives: two distinct symbols of `s`, the first of least weight, the second of
least weight among the rest. -/
private theorem pick_spec (w : ι → ℝ) (s : Finset ι) (h : 2 ≤ s.card) :
    (pick w s h).1 ∈ s ∧ (pick w s h).2 ∈ s ∧ (pick w s h).1 ≠ (pick w s h).2 ∧
      (∀ x ∈ s, w (pick w s h).1 ≤ w x) ∧
      ∀ x ∈ s, x ≠ (pick w s h).1 → w (pick w s h).2 ≤ w x := by
  sorry

/-- Lengths after splitting the merged node `a` back into `a` and `b`. -/
private def mergeLen (ℓ : ι → ℕ) (a b : ι) : ι → ℕ :=
  Function.update (Function.update ℓ a (ℓ a + 1)) b (ℓ a + 1)

/-- Weights after merging `b` into `a`. -/
private def mergeW (w : ι → ℝ) (a b : ι) : ι → ℝ :=
  Function.update w a (w a + w b)

/-- Huffman's recursion on a finite set of symbols. -/
private noncomputable def huffAux : ℕ → (ι → ℝ) → Finset ι → ι → ℕ
  | 0, _, _ => fun _ => 0
  | n + 1, w, s =>
    if h : 2 ≤ s.card then
      mergeLen (huffAux n (mergeW w (pick w s h).1 (pick w s h).2) (s.erase (pick w s h).2))
        (pick w s h).1 (pick w s h).2
    else fun _ => 0

/-- **Huffman's codeword lengths** for weights `p`, binary alphabet (item 153 of
MATH-PLAN-library-2). -/
noncomputable def huffmanLength [Fintype ι] (p : ι → ℝ) : ι → ℕ :=
  huffAux (Fintype.card ι) p Finset.univ

private theorem huffAux_zero (w : ι → ℝ) (s : Finset ι) : huffAux 0 w s = fun _ => 0 := by
  sorry

private theorem huffAux_succ (n : ℕ) (w : ι → ℝ) (s : Finset ι) (h : 2 ≤ s.card) :
    huffAux (n + 1) w s =
      mergeLen (huffAux n (mergeW w (pick w s h).1 (pick w s h).2) (s.erase (pick w s h).2))
        (pick w s h).1 (pick w s h).2 := by
  sorry

private theorem huffAux_succ_of_not (n : ℕ) (w : ι → ℝ) (s : Finset ι) (h : ¬ 2 ≤ s.card) :
    huffAux (n + 1) w s = fun _ => 0 := by
  sorry

private theorem mergeLen_left {ℓ : ι → ℕ} {a b : ι} (hab : a ≠ b) :
    mergeLen ℓ a b a = ℓ a + 1 := by
  sorry

private theorem mergeLen_right {ℓ : ι → ℕ} {a b : ι} : mergeLen ℓ a b b = ℓ a + 1 := by
  sorry

private theorem mergeLen_of_ne {ℓ : ι → ℕ} {a b z : ι} (hza : z ≠ a) (hzb : z ≠ b) :
    mergeLen ℓ a b z = ℓ z := by
  sorry

private theorem mergeW_self (w : ι → ℝ) (a b : ι) : mergeW w a b a = w a + w b := by
  sorry

private theorem mergeW_of_ne {w : ι → ℝ} {a b z : ι} (h : z ≠ a) : mergeW w a b z = w z := by
  sorry

private theorem mergeW_nonneg {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (a b : ι) (i : ι) :
    0 ≤ mergeW w a b i := by
  sorry

private theorem sum_split {s : Finset ι} {a b : ι} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (f : ι → ℝ) : ∑ i ∈ s, f i = f a + f b + ∑ i ∈ (s.erase b).erase a, f i := by
  sorry

private theorem sum_erase_split {s : Finset ι} {a b : ι} (ha : a ∈ s) (hab : a ≠ b)
    (f : ι → ℝ) : ∑ i ∈ s.erase b, f i = f a + ∑ i ∈ (s.erase b).erase a, f i := by
  sorry

private theorem swap_mem {s : Finset ι} {u v z : ι} (hu : u ∈ s) (hv : v ∈ s) (hz : z ∈ s) :
    Equiv.swap u v z ∈ s := by
  sorry

/-- Exchanging the lengths of `u` and `v` changes a sum of per-symbol terms by four terms. -/
private theorem sum_swap {s : Finset ι} {u v : ι} (hu : u ∈ s) (hv : v ∈ s) (F : ι → ℕ → ℝ)
    (ℓ : ι → ℕ) :
    ∑ z ∈ s, F z (ℓ (Equiv.swap u v z)) =
      ∑ z ∈ s, F z (ℓ z) + (F u (ℓ v) + F v (ℓ u) - F u (ℓ u) - F v (ℓ v)) := by
  sorry

private theorem two_pow_mul_half_pow {k M : ℕ} (hk : k ≤ M) :
    (2 : ℝ) ^ M * (1 / 2) ^ k = ((2 ^ (M - k) : ℕ) : ℝ) := by
  sorry

private theorem kraft_mergeLen {s : Finset ι} {a b : ι} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (ℓ : ι → ℕ) :
    ∑ i ∈ s, (1 / 2 : ℝ) ^ (mergeLen ℓ a b i) = ∑ i ∈ s.erase b, (1 / 2 : ℝ) ^ (ℓ i) := by
  sorry

private theorem cost_mergeLen (w : ι → ℝ) {s : Finset ι} {a b : ι} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) (ℓ : ι → ℕ) :
    ∑ i ∈ s, w i * (mergeLen ℓ a b i : ℝ) =
      ∑ i ∈ s.erase b, mergeW w a b i * (ℓ i : ℝ) + w a + w b := by
  sorry

/-- Merging `a` (longest) and `b` (second longest) into one symbol of length `ℓ b - 1`. -/
private theorem merge_step {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) {s : Finset ι} {a b : ι}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) {ℓ : ι → ℕ} (hba : ℓ b ≤ ℓ a)
    (hle : ∀ z ∈ s, z ≠ a → ℓ z ≤ ℓ b) (hk : ∑ i ∈ s, (1 / 2 : ℝ) ^ ℓ i ≤ 1) :
    ∃ ℓ' : ι → ℕ, ∑ i ∈ s.erase b, (1 / 2 : ℝ) ^ ℓ' i ≤ 1 ∧
      ∑ i ∈ s.erase b, mergeW w a b i * (ℓ' i : ℝ) + w a + w b ≤ ∑ i ∈ s, w i * (ℓ i : ℝ) := by
  sorry

/-- Any lengths with Kraft sum at most `1` cost at least the merged problem plus `w a + w b`. -/
private theorem reduce_step {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) {s : Finset ι} {a b : ι}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (hamin : ∀ x ∈ s, w a ≤ w x)
    (hbmin : ∀ x ∈ s, x ≠ a → w b ≤ w x) {ℓ : ι → ℕ} (hk : ∑ i ∈ s, (1 / 2 : ℝ) ^ ℓ i ≤ 1) :
    ∃ ℓ' : ι → ℕ, ∑ i ∈ s.erase b, (1 / 2 : ℝ) ^ ℓ' i ≤ 1 ∧
      ∑ i ∈ s.erase b, mergeW w a b i * (ℓ' i : ℝ) + w a + w b ≤ ∑ i ∈ s, w i * (ℓ i : ℝ) := by
  sorry

/-- Huffman's lengths on a set of `n` symbols have Kraft sum at most `1`. -/
private theorem huffAux_kraft (n : ℕ) : ∀ (w : ι → ℝ) (s : Finset ι), s.card = n →
    ∑ i ∈ s, (1 / 2 : ℝ) ^ (huffAux n w s i) ≤ 1 := by
  sorry

/-- On a set of `n` symbols with nonnegative weights, Huffman's lengths cost at most any lengths
with Kraft sum at most `1`. -/
private theorem huffAux_opt (n : ℕ) : ∀ (w : ι → ℝ) (s : Finset ι), (∀ i, 0 ≤ w i) →
    s.card = n → ∀ ℓ : ι → ℕ, ∑ i ∈ s, (1 / 2 : ℝ) ^ ℓ i ≤ 1 →
      ∑ i ∈ s, w i * (huffAux n w s i : ℝ) ≤ ∑ i ∈ s, w i * (ℓ i : ℝ) := by
  sorry

end Recursion

/-- **Optimality of Huffman's code** (item 153 of MATH-PLAN-library-2). For nonnegative weights
`p` and a two-letter alphabet, some injective prefix-free code has Huffman's codeword lengths, and
its mean length `∑ p i · |c i|` is at most that of every injective prefix-free code. -/
theorem huffman_optimal {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (hα : Fintype.card α = 2) {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) :
    ∃ c : ι → List α, Function.Injective c ∧ InformationTheory.IsPrefixFree (Set.range c) ∧
      (∀ i, (c i).length = huffmanLength p i) ∧
      ∀ c' : ι → List α, Function.Injective c' →
        InformationTheory.IsPrefixFree (Set.range c') →
          ∑ i, p i * ((c i).length : ℝ) ≤ ∑ i, p i * ((c' i).length : ℝ) := by
  sorry

end ClassicalLean.InformationTheory.Huffman
