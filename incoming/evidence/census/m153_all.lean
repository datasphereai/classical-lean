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
lightest symbols get the two largest lengths, and then the two can be merged into one symbol whose
length is one less than the second largest, with Kraft sum still at most `1` and cost, plus the two
weights, at most the cost before (`reduce_step`, `merge_step`); Huffman's recursion pays exactly
the two weights at that step (`cost_mergeLen`), and the induction hypothesis, on the merged
weights and one symbol fewer, bounds the rest by the merged lengths' cost.
The lengths of every prefix-free code pass Kraft's test (Mathlib's
`InformationTheory.IsPrefixFree.finsetSum_one_div_card_pow_length_le_one`).

The proof is the draft `d153-r1-s2` (written by Claude Opus 5.5 through the Anthropic Batch API,
the lane's API-CREDIT-1 work), adapted by the Claude Code cloud session that landed it (order
CLOUD-MATH-2): every declaration in the namespace `ClassicalLean.InformationTheory.Huffman` (the
draft had the helpers in `ClassicalLean.Huffman` and `huffman_optimal` outside any namespace), the
helpers' `variable` line in a section closed before `huffman_optimal`, whose own binders are the
draft's; docstrings; `omit [DecidableEq ι] in` on `exists_pair` (with `classical` in its proof)
and on `pick_spec`, so the private `pick`, which used the instance only inside the proof it gives
`Classical.choose`, no longer takes it (`huffAux` and `huffmanLength` take it, as in the draft,
for `Finset.erase` and `Function.update`); `dite_eq_left` and `dite_eq_right` for the deprecated
`dif_pos` and `dif_neg`; `push Not` for the deprecated `push_neg`.
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
  classical
  have hs : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha, hamin⟩ := s.exists_min_image w hs
  have hs' : (s.erase a).Nonempty :=
    Finset.card_pos.mp (by rw [Finset.card_erase_of_mem ha]; omega)
  obtain ⟨b, hb, hbmin⟩ := (s.erase a).exists_min_image w hs'
  refine ⟨(a, b), ha, mem_of_mem_erase hb, (ne_of_mem_erase hb).symm, hamin, ?_⟩
  intro x hx hxa
  exact hbmin x (mem_erase.mpr ⟨hxa, hx⟩)

/-- The two symbols Huffman's step merges: a lightest symbol of `s` and a lightest of the rest. -/
private noncomputable def pick (w : ι → ℝ) (s : Finset ι) (h : 2 ≤ s.card) : ι × ι :=
  Classical.choose (exists_pair w s h)

omit [DecidableEq ι] in
/-- What `pick` gives: two distinct symbols of `s`, the first of least weight, the second of
least weight among the rest. -/
private theorem pick_spec (w : ι → ℝ) (s : Finset ι) (h : 2 ≤ s.card) :
    (pick w s h).1 ∈ s ∧ (pick w s h).2 ∈ s ∧ (pick w s h).1 ≠ (pick w s h).2 ∧
      (∀ x ∈ s, w (pick w s h).1 ≤ w x) ∧
      ∀ x ∈ s, x ≠ (pick w s h).1 → w (pick w s h).2 ≤ w x :=
  Classical.choose_spec (exists_pair w s h)

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
  rw [huffAux]

private theorem huffAux_succ (n : ℕ) (w : ι → ℝ) (s : Finset ι) (h : 2 ≤ s.card) :
    huffAux (n + 1) w s =
      mergeLen (huffAux n (mergeW w (pick w s h).1 (pick w s h).2) (s.erase (pick w s h).2))
        (pick w s h).1 (pick w s h).2 := by
  rw [huffAux, dite_eq_left h]

private theorem huffAux_succ_of_not (n : ℕ) (w : ι → ℝ) (s : Finset ι) (h : ¬ 2 ≤ s.card) :
    huffAux (n + 1) w s = fun _ => 0 := by
  rw [huffAux, dite_eq_right h]

private theorem mergeLen_left {ℓ : ι → ℕ} {a b : ι} (hab : a ≠ b) :
    mergeLen ℓ a b a = ℓ a + 1 := by
  unfold mergeLen
  rw [Function.update_of_ne hab, Function.update_self]

private theorem mergeLen_right {ℓ : ι → ℕ} {a b : ι} : mergeLen ℓ a b b = ℓ a + 1 := by
  unfold mergeLen
  rw [Function.update_self]

private theorem mergeLen_of_ne {ℓ : ι → ℕ} {a b z : ι} (hza : z ≠ a) (hzb : z ≠ b) :
    mergeLen ℓ a b z = ℓ z := by
  unfold mergeLen
  rw [Function.update_of_ne hzb, Function.update_of_ne hza]

private theorem mergeW_self (w : ι → ℝ) (a b : ι) : mergeW w a b a = w a + w b := by
  unfold mergeW
  rw [Function.update_self]

private theorem mergeW_of_ne {w : ι → ℝ} {a b z : ι} (h : z ≠ a) : mergeW w a b z = w z := by
  unfold mergeW
  rw [Function.update_of_ne h]

private theorem mergeW_nonneg {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (a b : ι) (i : ι) :
    0 ≤ mergeW w a b i := by
  by_cases h : i = a
  · rw [h, mergeW_self]; linarith [hw a, hw b]
  · rw [mergeW_of_ne h]; exact hw i

private theorem sum_split {s : Finset ι} {a b : ι} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (f : ι → ℝ) : ∑ i ∈ s, f i = f a + f b + ∑ i ∈ (s.erase b).erase a, f i := by
  rw [← Finset.add_sum_erase s f hb,
    ← Finset.add_sum_erase (s.erase b) f (mem_erase.mpr ⟨hab, ha⟩)]
  ring

private theorem sum_erase_split {s : Finset ι} {a b : ι} (ha : a ∈ s) (hab : a ≠ b)
    (f : ι → ℝ) : ∑ i ∈ s.erase b, f i = f a + ∑ i ∈ (s.erase b).erase a, f i :=
  (Finset.add_sum_erase (s.erase b) f (mem_erase.mpr ⟨hab, ha⟩)).symm

private theorem swap_mem {s : Finset ι} {u v z : ι} (hu : u ∈ s) (hv : v ∈ s) (hz : z ∈ s) :
    Equiv.swap u v z ∈ s := by
  rw [Equiv.swap_apply_def]
  split_ifs <;> assumption

/-- Exchanging the lengths of `u` and `v` changes a sum of per-symbol terms by four terms. -/
private theorem sum_swap {s : Finset ι} {u v : ι} (hu : u ∈ s) (hv : v ∈ s) (F : ι → ℕ → ℝ)
    (ℓ : ι → ℕ) :
    ∑ z ∈ s, F z (ℓ (Equiv.swap u v z)) =
      ∑ z ∈ s, F z (ℓ z) + (F u (ℓ v) + F v (ℓ u) - F u (ℓ u) - F v (ℓ v)) := by
  rcases eq_or_ne u v with rfl | huv
  · simp only [Equiv.swap_self, Equiv.refl_apply]
    ring
  · have h1 : ∑ z ∈ s, F z (ℓ (Equiv.swap u v z)) =
        F u (ℓ (Equiv.swap u v u)) + F v (ℓ (Equiv.swap u v v)) +
          ∑ z ∈ (s.erase v).erase u, F z (ℓ (Equiv.swap u v z)) := sum_split hu hv huv _
    have h2 : ∑ z ∈ s, F z (ℓ z) =
        F u (ℓ u) + F v (ℓ v) + ∑ z ∈ (s.erase v).erase u, F z (ℓ z) := sum_split hu hv huv _
    have h3 : ∑ z ∈ (s.erase v).erase u, F z (ℓ (Equiv.swap u v z)) =
        ∑ z ∈ (s.erase v).erase u, F z (ℓ z) :=
      sum_congr rfl fun z hz => by
        rw [Equiv.swap_apply_of_ne_of_ne (ne_of_mem_erase hz)
          (ne_of_mem_erase (mem_of_mem_erase hz))]
    rw [h1, h2, h3, Equiv.swap_apply_left, Equiv.swap_apply_right]
    ring

private theorem two_pow_mul_half_pow {k M : ℕ} (hk : k ≤ M) :
    (2 : ℝ) ^ M * (1 / 2) ^ k = ((2 ^ (M - k) : ℕ) : ℝ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left, pow_add]
  push_cast
  have h : (2 : ℝ) ^ k * (1 / 2) ^ k = 1 := by rw [← mul_pow]; norm_num
  linear_combination (2 : ℝ) ^ d * h

private theorem kraft_mergeLen {s : Finset ι} {a b : ι} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (ℓ : ι → ℕ) :
    ∑ i ∈ s, (1 / 2 : ℝ) ^ (mergeLen ℓ a b i) = ∑ i ∈ s.erase b, (1 / 2 : ℝ) ^ (ℓ i) := by
  have h1 : ∑ i ∈ s, (1 / 2 : ℝ) ^ (mergeLen ℓ a b i) =
      (1 / 2) ^ (mergeLen ℓ a b a) + (1 / 2) ^ (mergeLen ℓ a b b) +
        ∑ i ∈ (s.erase b).erase a, (1 / 2 : ℝ) ^ (mergeLen ℓ a b i) := sum_split ha hb hab _
  have h2 : ∑ i ∈ s.erase b, (1 / 2 : ℝ) ^ (ℓ i) =
      (1 / 2) ^ (ℓ a) + ∑ i ∈ (s.erase b).erase a, (1 / 2 : ℝ) ^ (ℓ i) :=
    sum_erase_split ha hab _
  have h3 : ∑ i ∈ (s.erase b).erase a, (1 / 2 : ℝ) ^ (mergeLen ℓ a b i) =
      ∑ i ∈ (s.erase b).erase a, (1 / 2 : ℝ) ^ (ℓ i) :=
    sum_congr rfl fun z hz => by
      rw [mergeLen_of_ne (ne_of_mem_erase hz) (ne_of_mem_erase (mem_of_mem_erase hz))]
  rw [h1, h2, h3, mergeLen_left hab, mergeLen_right]
  ring

private theorem cost_mergeLen (w : ι → ℝ) {s : Finset ι} {a b : ι} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) (ℓ : ι → ℕ) :
    ∑ i ∈ s, w i * (mergeLen ℓ a b i : ℝ) =
      ∑ i ∈ s.erase b, mergeW w a b i * (ℓ i : ℝ) + w a + w b := by
  have h1 : ∑ i ∈ s, w i * (mergeLen ℓ a b i : ℝ) =
      w a * (mergeLen ℓ a b a : ℝ) + w b * (mergeLen ℓ a b b : ℝ) +
        ∑ i ∈ (s.erase b).erase a, w i * (mergeLen ℓ a b i : ℝ) := sum_split ha hb hab _
  have h2 : ∑ i ∈ s.erase b, mergeW w a b i * (ℓ i : ℝ) =
      mergeW w a b a * (ℓ a : ℝ) + ∑ i ∈ (s.erase b).erase a, mergeW w a b i * (ℓ i : ℝ) :=
    sum_erase_split ha hab _
  have h3 : ∑ i ∈ (s.erase b).erase a, w i * (mergeLen ℓ a b i : ℝ) =
      ∑ i ∈ (s.erase b).erase a, mergeW w a b i * (ℓ i : ℝ) :=
    sum_congr rfl fun z hz => by
      rw [mergeLen_of_ne (ne_of_mem_erase hz) (ne_of_mem_erase (mem_of_mem_erase hz)),
        mergeW_of_ne (ne_of_mem_erase hz)]
  rw [h1, h2, h3, mergeLen_left hab, mergeLen_right, mergeW_self]
  push_cast
  ring

/-- Merging `a` (longest) and `b` (second longest): some lengths on `s.erase b` have Kraft sum at
most `1` and cost, plus `w a + w b`, at most the cost of `ℓ` (the proof gives the merged symbol
the length `ℓ b - 1`). -/
private theorem merge_step {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) {s : Finset ι} {a b : ι}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) {ℓ : ι → ℕ} (hba : ℓ b ≤ ℓ a)
    (hle : ∀ z ∈ s, z ≠ a → ℓ z ≤ ℓ b) (hk : ∑ i ∈ s, (1 / 2 : ℝ) ^ ℓ i ≤ 1) :
    ∃ ℓ' : ι → ℕ, ∑ i ∈ s.erase b, (1 / 2 : ℝ) ^ ℓ' i ≤ 1 ∧
      ∑ i ∈ s.erase b, mergeW w a b i * (ℓ' i : ℝ) + w a + w b ≤ ∑ i ∈ s, w i * (ℓ i : ℝ) := by
  have hzt : ∀ z ∈ (s.erase b).erase a, z ≠ a ∧ z ≠ b ∧ z ∈ s := fun z hz =>
    ⟨ne_of_mem_erase hz, ne_of_mem_erase (mem_of_mem_erase hz),
      mem_of_mem_erase (mem_of_mem_erase hz)⟩
  have hks : ∑ i ∈ s, (1 / 2 : ℝ) ^ ℓ i =
      (1 / 2) ^ ℓ a + (1 / 2) ^ ℓ b + ∑ i ∈ (s.erase b).erase a, (1 / 2 : ℝ) ^ ℓ i :=
    sum_split ha hb hab _
  have hR0 : 0 ≤ ∑ i ∈ (s.erase b).erase a, (1 / 2 : ℝ) ^ ℓ i :=
    sum_nonneg fun i _ => by positivity
  have hpa : 0 < (1 / 2 : ℝ) ^ ℓ a := by positivity
  have hM1 : 1 ≤ ℓ b := by
    by_contra h0
    have h0' : ℓ b = 0 := by omega
    rw [h0', pow_zero] at hks
    linarith
  have hℓ'a : Function.update ℓ a (ℓ b - 1) a = ℓ b - 1 := by rw [Function.update_self]
  have hℓ'z : ∀ z, z ≠ a → Function.update ℓ a (ℓ b - 1) z = ℓ z := fun z hz => by
    rw [Function.update_of_ne hz]
  refine ⟨Function.update ℓ a (ℓ b - 1), ?_, ?_⟩
  · have hsplit : ∑ i ∈ s.erase b, (1 / 2 : ℝ) ^ (Function.update ℓ a (ℓ b - 1) i) =
        (1 / 2) ^ (Function.update ℓ a (ℓ b - 1) a) +
          ∑ i ∈ (s.erase b).erase a, (1 / 2 : ℝ) ^ (Function.update ℓ a (ℓ b - 1) i) :=
      sum_erase_split ha hab _
    have hrest : ∑ i ∈ (s.erase b).erase a, (1 / 2 : ℝ) ^ (Function.update ℓ a (ℓ b - 1) i) =
        ∑ i ∈ (s.erase b).erase a, (1 / 2 : ℝ) ^ ℓ i :=
      sum_congr rfl fun z hz => by rw [hℓ'z z (hzt z hz).1]
    rw [hsplit, hrest, hℓ'a]
    have hq : (1 / 2 : ℝ) ^ (ℓ b - 1) = 2 * (1 / 2) ^ (ℓ b) := by
      obtain ⟨k, hkk⟩ := Nat.exists_eq_add_of_le hM1
      rw [hkk, Nat.add_sub_cancel_left, pow_add]
      ring
    have hN : (2 : ℝ) ^ (ℓ b) * ∑ i ∈ (s.erase b).erase a, (1 / 2 : ℝ) ^ ℓ i =
        ((∑ i ∈ (s.erase b).erase a, 2 ^ (ℓ b - ℓ i) : ℕ) : ℝ) := by
      rw [mul_sum, Nat.cast_sum]
      exact sum_congr rfl fun z hz => two_pow_mul_half_pow (hle z (hzt z hz).2.2 (hzt z hz).1)
    have hX : (0 : ℝ) < 2 ^ (ℓ b) := by positivity
    have hXq : (2 : ℝ) ^ (ℓ b) * (1 / 2) ^ (ℓ b) = 1 := by rw [← mul_pow]; norm_num
    have hXa : 0 < (2 : ℝ) ^ (ℓ b) * (1 / 2) ^ (ℓ a) := mul_pos hX hpa
    have h1 := mul_le_mul_of_nonneg_left hk hX.le
    rw [hks] at h1
    have e : (2 : ℝ) ^ (ℓ b) * ((1 / 2) ^ ℓ a + (1 / 2) ^ ℓ b +
        ∑ i ∈ (s.erase b).erase a, (1 / 2 : ℝ) ^ ℓ i) =
        2 ^ (ℓ b) * (1 / 2) ^ (ℓ a) + 2 ^ (ℓ b) * (1 / 2) ^ (ℓ b) +
          2 ^ (ℓ b) * ∑ i ∈ (s.erase b).erase a, (1 / 2 : ℝ) ^ ℓ i := by ring
    have h2 : ((∑ i ∈ (s.erase b).erase a, 2 ^ (ℓ b - ℓ i) : ℕ) : ℝ) + 1 < 2 ^ (ℓ b) := by
      linarith [e, hXq, hN, hXa, h1]
    have h3 : (∑ i ∈ (s.erase b).erase a, 2 ^ (ℓ b - ℓ i) : ℕ) + 2 ≤ 2 ^ (ℓ b) := by
      have : (∑ i ∈ (s.erase b).erase a, 2 ^ (ℓ b - ℓ i) : ℕ) + 1 < 2 ^ (ℓ b) := by
        exact_mod_cast h2
      omega
    have h4 : ((∑ i ∈ (s.erase b).erase a, 2 ^ (ℓ b - ℓ i) : ℕ) : ℝ) + 2 ≤ 2 ^ (ℓ b) := by
      exact_mod_cast h3
    rw [hq]
    by_contra hc
    push Not at hc
    have hlt := mul_lt_mul_of_pos_left hc hX
    have e2 : (2 : ℝ) ^ (ℓ b) * (2 * (1 / 2) ^ (ℓ b) +
        ∑ i ∈ (s.erase b).erase a, (1 / 2 : ℝ) ^ ℓ i) =
        2 * (2 ^ (ℓ b) * (1 / 2) ^ (ℓ b)) +
          2 ^ (ℓ b) * ∑ i ∈ (s.erase b).erase a, (1 / 2 : ℝ) ^ ℓ i := by ring
    linarith [e2, hXq, hN, h4, hlt]
  · have hsplit : ∑ i ∈ s.erase b,
        mergeW w a b i * ((Function.update ℓ a (ℓ b - 1) i : ℕ) : ℝ) =
        mergeW w a b a * ((Function.update ℓ a (ℓ b - 1) a : ℕ) : ℝ) +
          ∑ i ∈ (s.erase b).erase a,
            mergeW w a b i * ((Function.update ℓ a (ℓ b - 1) i : ℕ) : ℝ) :=
      sum_erase_split ha hab _
    have hrest : ∑ i ∈ (s.erase b).erase a,
        mergeW w a b i * ((Function.update ℓ a (ℓ b - 1) i : ℕ) : ℝ) =
        ∑ i ∈ (s.erase b).erase a, w i * (ℓ i : ℝ) :=
      sum_congr rfl fun z hz => by rw [hℓ'z z (hzt z hz).1, mergeW_of_ne (hzt z hz).1]
    have hs2 : ∑ i ∈ s, w i * (ℓ i : ℝ) =
        w a * (ℓ a : ℝ) + w b * (ℓ b : ℝ) + ∑ i ∈ (s.erase b).erase a, w i * (ℓ i : ℝ) :=
      sum_split ha hb hab _
    rw [hsplit, hrest, hs2, hℓ'a, mergeW_self, Nat.cast_sub hM1, Nat.cast_one]
    have : w a * (ℓ b : ℝ) ≤ w a * ℓ a :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hba) (hw a)
    nlinarith [this]

/-- Any lengths with Kraft sum at most `1` cost at least the merged problem plus `w a + w b`. -/
private theorem reduce_step {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) {s : Finset ι} {a b : ι}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (hamin : ∀ x ∈ s, w a ≤ w x)
    (hbmin : ∀ x ∈ s, x ≠ a → w b ≤ w x) {ℓ : ι → ℕ} (hk : ∑ i ∈ s, (1 / 2 : ℝ) ^ ℓ i ≤ 1) :
    ∃ ℓ' : ι → ℕ, ∑ i ∈ s.erase b, (1 / 2 : ℝ) ^ ℓ' i ≤ 1 ∧
      ∑ i ∈ s.erase b, mergeW w a b i * (ℓ' i : ℝ) + w a + w b ≤ ∑ i ∈ s, w i * (ℓ i : ℝ) := by
  obtain ⟨x, hx, hxmax⟩ := s.exists_max_image ℓ ⟨a, ha⟩
  have hne : (s.erase x).Nonempty := by
    by_cases hax : a = x
    · exact ⟨b, mem_erase.mpr ⟨fun h => hab (hax.trans h.symm), hb⟩⟩
    · exact ⟨a, mem_erase.mpr ⟨hax, ha⟩⟩
  obtain ⟨y, hy, hymax⟩ := (s.erase x).exists_max_image ℓ hne
  have hyx : y ≠ x := ne_of_mem_erase hy
  have hys : y ∈ s := mem_of_mem_erase hy
  obtain ⟨y', hy'⟩ : ∃ y', y' = Equiv.swap a x y := ⟨_, rfl⟩
  have hy's : y' ∈ s := by rw [hy']; exact swap_mem ha hx hys
  have e2 : Equiv.swap a x a = x := by simp
  have e3 : Equiv.swap a x y' = y := by rw [hy']; simp
  have e1 : Equiv.swap b y' b = y' := by simp
  have hy'a : y' ≠ a := by
    intro h
    apply hyx
    rw [← e3, h, e2]
  have e0 : Equiv.swap b y' a = a := Equiv.swap_apply_of_ne_of_ne hab hy'a.symm
  have k1 : ∑ i ∈ s, (1 / 2 : ℝ) ^ (ℓ (Equiv.swap a x i)) = ∑ i ∈ s, (1 / 2 : ℝ) ^ (ℓ i) +
      ((1 / 2 : ℝ) ^ (ℓ x) + (1 / 2) ^ (ℓ a) - (1 / 2) ^ (ℓ a) - (1 / 2) ^ (ℓ x)) :=
    sum_swap ha hx (fun _ k => (1 / 2 : ℝ) ^ k) ℓ
  have k2 : ∑ i ∈ s, (1 / 2 : ℝ) ^ (ℓ (Equiv.swap a x (Equiv.swap b y' i))) =
      ∑ i ∈ s, (1 / 2 : ℝ) ^ (ℓ (Equiv.swap a x i)) +
      ((1 / 2 : ℝ) ^ (ℓ (Equiv.swap a x y')) + (1 / 2) ^ (ℓ (Equiv.swap a x b)) -
        (1 / 2) ^ (ℓ (Equiv.swap a x b)) - (1 / 2) ^ (ℓ (Equiv.swap a x y'))) :=
    sum_swap hb hy's (fun _ k => (1 / 2 : ℝ) ^ k) (fun z => ℓ (Equiv.swap a x z))
  have hk2 : ∑ i ∈ s, (1 / 2 : ℝ) ^ (ℓ (Equiv.swap a x (Equiv.swap b y' i))) ≤ 1 := by
    rw [k2, k1]; linarith
  have c1 : ∑ i ∈ s, w i * (ℓ (Equiv.swap a x i) : ℝ) = ∑ i ∈ s, w i * (ℓ i : ℝ) +
      (w a * ℓ x + w x * ℓ a - w a * ℓ a - w x * ℓ x) :=
    sum_swap ha hx (fun z k => w z * (k : ℝ)) ℓ
  have c2 : ∑ i ∈ s, w i * (ℓ (Equiv.swap a x (Equiv.swap b y' i)) : ℝ) =
      ∑ i ∈ s, w i * (ℓ (Equiv.swap a x i) : ℝ) +
      (w b * ℓ (Equiv.swap a x y') + w y' * ℓ (Equiv.swap a x b) -
        w b * ℓ (Equiv.swap a x b) - w y' * ℓ (Equiv.swap a x y')) :=
    sum_swap hb hy's (fun z k => w z * (k : ℝ)) (fun z => ℓ (Equiv.swap a x z))
  rw [e3] at c2
  have hxb : Equiv.swap a x b ≠ x := by
    intro h
    apply hab
    have : Equiv.swap a x b = Equiv.swap a x a := h.trans e2.symm
    exact ((Equiv.swap a x).injective this).symm
  have hb1 : ℓ (Equiv.swap a x b) ≤ ℓ y := hymax _ (mem_erase.mpr ⟨hxb, swap_mem ha hx hb⟩)
  have d1 : 0 ≤ (w x - w a) * ((ℓ x : ℝ) - ℓ a) :=
    mul_nonneg (sub_nonneg.mpr (hamin x hx)) (sub_nonneg.mpr (by exact_mod_cast hxmax a ha))
  have d2 : 0 ≤ (w y' - w b) * ((ℓ y : ℝ) - ℓ (Equiv.swap a x b)) :=
    mul_nonneg (sub_nonneg.mpr (hbmin y' hy's hy'a)) (sub_nonneg.mpr (by exact_mod_cast hb1))
  have hc2 : ∑ i ∈ s, w i * (ℓ (Equiv.swap a x (Equiv.swap b y' i)) : ℝ) ≤
      ∑ i ∈ s, w i * (ℓ i : ℝ) := by
    nlinarith [c1, c2, d1, d2]
  have hba : ℓ (Equiv.swap a x (Equiv.swap b y' b)) ≤ ℓ (Equiv.swap a x (Equiv.swap b y' a)) := by
    rw [e1, e3, e0, e2]; exact hxmax y hys
  have hle : ∀ z ∈ s, z ≠ a →
      ℓ (Equiv.swap a x (Equiv.swap b y' z)) ≤ ℓ (Equiv.swap a x (Equiv.swap b y' b)) := by
    intro z hz hza
    rw [e1, e3]
    have hu : Equiv.swap b y' z ≠ a := by
      intro h
      apply hza
      exact (Equiv.swap b y').injective (h.trans e0.symm)
    apply hymax
    refine mem_erase.mpr ⟨fun h => hu ((Equiv.swap a x).injective (h.trans e2.symm)), ?_⟩
    exact swap_mem ha hx (swap_mem hb hy's hz)
  obtain ⟨ℓ', hk', hc'⟩ := merge_step hw ha hb hab
    (ℓ := fun z => ℓ (Equiv.swap a x (Equiv.swap b y' z))) hba hle hk2
  refine ⟨ℓ', hk', ?_⟩
  have hc'' : ∑ i ∈ s.erase b, mergeW w a b i * (ℓ' i : ℝ) + w a + w b ≤
      ∑ i ∈ s, w i * (ℓ (Equiv.swap a x (Equiv.swap b y' i)) : ℝ) := hc'
  linarith

/-- Huffman's lengths on a set of `n` symbols have Kraft sum at most `1`. -/
private theorem huffAux_kraft (n : ℕ) : ∀ (w : ι → ℝ) (s : Finset ι), s.card = n →
    ∑ i ∈ s, (1 / 2 : ℝ) ^ (huffAux n w s i) ≤ 1 := by
  induction n with
  | zero =>
    intro w s hs
    rw [Finset.card_eq_zero.mp hs]
    simp
  | succ n ih =>
    intro w s hs
    by_cases h : 2 ≤ s.card
    · rw [huffAux_succ n w s h]
      obtain ⟨ha, hb, hab, -, -⟩ := pick_spec w s h
      rw [kraft_mergeLen ha hb hab]
      exact ih _ _ (by rw [card_erase_of_mem hb]; omega)
    · rw [huffAux_succ_of_not n w s h]
      simp only [pow_zero, sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast (show s.card ≤ 1 by omega)

/-- On a set of `n` symbols with nonnegative weights, Huffman's lengths cost at most any lengths
with Kraft sum at most `1`. -/
private theorem huffAux_opt (n : ℕ) : ∀ (w : ι → ℝ) (s : Finset ι), (∀ i, 0 ≤ w i) →
    s.card = n → ∀ ℓ : ι → ℕ, ∑ i ∈ s, (1 / 2 : ℝ) ^ ℓ i ≤ 1 →
      ∑ i ∈ s, w i * (huffAux n w s i : ℝ) ≤ ∑ i ∈ s, w i * (ℓ i : ℝ) := by
  induction n with
  | zero =>
    intro w s hw _ ℓ _
    rw [huffAux_zero]
    simp only [Nat.cast_zero, mul_zero, sum_const_zero]
    exact sum_nonneg fun i _ => mul_nonneg (hw i) (Nat.cast_nonneg _)
  | succ n ih =>
    intro w s hw hs ℓ hk
    by_cases h : 2 ≤ s.card
    · rw [huffAux_succ n w s h]
      obtain ⟨ha, hb, hab, hamin, hbmin⟩ := pick_spec w s h
      obtain ⟨ℓ', hk', hc'⟩ := reduce_step hw ha hb hab hamin hbmin hk
      have hcard : (s.erase (pick w s h).2).card = n := by
        rw [card_erase_of_mem hb]; omega
      have hw' : ∀ i, 0 ≤ mergeW w (pick w s h).1 (pick w s h).2 i := mergeW_nonneg hw _ _
      have hIH := ih _ _ hw' hcard ℓ' hk'
      rw [cost_mergeLen w ha hb hab]
      linarith
    · rw [huffAux_succ_of_not n w s h]
      simp only [Nat.cast_zero, mul_zero, sum_const_zero]
      exact sum_nonneg fun i _ => mul_nonneg (hw i) (Nat.cast_nonneg _)

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
  have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  have hD : (1 / (Fintype.card α : ℝ)) = 1 / 2 := by rw [hα]; norm_num
  have hk := huffAux_kraft (Fintype.card ι) p univ Finset.card_univ
  obtain ⟨c, hinj, hpf, hlen⟩ := ClassicalLean.Simplex.exists_isPrefixFree_length_eq (α := α)
    (huffmanLength p) (by rw [hD]; exact hk)
  refine ⟨c, hinj, hpf, hlen, fun c' hinj' hpf' => ?_⟩
  have hk' : ∑ i, (1 / 2 : ℝ) ^ (c' i).length ≤ 1 := by
    classical
    have hS : ((univ.image c' : Finset (List α)) : Set (List α)) = Set.range c' := by simp
    have := (hS ▸ hpf').finsetSum_one_div_card_pow_length_le_one
    calc ∑ i, (1 / 2 : ℝ) ^ (c' i).length
        = ∑ i, (1 / (Fintype.card α : ℝ)) ^ (c' i).length := by rw [hD]
      _ ≤ 1 := by rwa [sum_image fun i _ j _ h => hinj' h] at this
  have hopt := huffAux_opt (Fintype.card ι) p univ hp Finset.card_univ
    (fun i => (c' i).length) hk'
  have e : ∀ i, ((c i).length : ℝ) =
      (huffAux (Fintype.card ι) p univ i : ℝ) := fun i => by
    rw [hlen i, huffmanLength]
  have e2 : ∑ i, p i * ((c i).length : ℝ) =
      ∑ i, p i * (huffAux (Fintype.card ι) p univ i : ℝ) :=
    sum_congr rfl fun i _ => by rw [e i]
  rw [e2]
  exact hopt

end ClassicalLean.InformationTheory.Huffman

/-- The hypotheses of `huffman_optimal` hold together: three symbols (`ι = Fin 3`) with the
weights `p = (1/2, 1/4, 1/4)`, all positive and not all equal, and the two-letter alphabet
`α = Bool`. -/
example := ClassicalLean.InformationTheory.Huffman.huffman_optimal (ι := Fin 3) (α := Bool)
    (p := ![1 / 2, 1 / 4, 1 / 4]) Fintype.card_bool (fun i => by fin_cases i <;> norm_num)

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.foldStage2 (fun acc n _ => acc.push n) (#[] : Array Name)
  logInfo m!"ALLCONST {names.size}"
  for n in names do logInfo m!"CONST {n}"
