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

## The converse, and the upper bound (order LEAN-22, item 41 of the plan)

* `exists_isPrefixFree_length_eq` (the converse of Kraft's inequality): any lengths `ℓ i` with
  `∑ D^(-ℓ i) ≤ 1` are the lengths of an injective prefix-free code over the `D` letters. The proof
  places the symbols one at a time, shortest first (Mathlib's `Finset.induction_on_max_value`):
  the next symbol, of length `L`, needs a word of length `L` that no earlier codeword begins; the
  earlier codewords begin at most `∑ D^(L - ℓ i) ≤ D^L - 1` of the `D^L` words, by Kraft's sum.
* `exists_isPrefixFree_sum_mul_length_lt`: for a probability vector `p` with every `p i > 0` and
  `D ≥ 2` letters, some injective prefix-free code has mean length below `H(p) / log D + 1`
  (Shannon's lengths `⌈-log (p i) / log D⌉`). With
  `shannonEntropy_le_sum_mul_length_of_isPrefixFree` above: every injective prefix-free code has
  mean length at least `H / log D`, and some such code has mean length below `H / log D + 1`.

Measured in order LEAN-22's checks (check C41, exact enumeration): the construction of the proof
gives a code for all 181 length lists with Kraft sum at most `1` (alphabets of 1 to 3 letters, up
to 4 symbols, lengths below 4). Each hypothesis is needed; drop it alone and the conclusion fails:

* Kraft's sum at most `1`: lengths `(1, 1, 1)` over 2 letters (sum `3/2`): no code exists.
* a nonempty alphabet (first theorem; the second gets it from `D ≥ 2`): with no letters Lean's
  Kraft sum of one length `1` is `(1 / 0)^1 = 0 ≤ 1`, and there is no word of length `1`.
* every `p i > 0` (second theorem): `p = (1, 0)` over 2 letters: `H = 0`, the bound is `1`, and
  every injective prefix-free code for two symbols has both words nonempty, so mean length `≥ 1`.
* `D ≥ 2`: over one letter, two words are always one a prefix of the other, so no injective
  prefix-free code for two symbols exists.
* `∑ p = 1`: `p = (2, 2)` over 2 letters: the bound is `-4 + 1 = -3` and mean lengths are `≥ 0`.

## What Mathlib provides

Kraft's and McMillan's inequalities (`InformationTheory/Coding/Kraft.lean`,
`KraftMcMillan.lean`, `PrefixFree.lean`). Mathlib v4.34.0 has no entropy of a finite vector and
no source coding statement: `source coding`, `noiseless coding`, `expected length` and
`entropy.*length` give no hits (order LEAN-17's plan, section 5). The converse of Kraft's
inequality is not in Mathlib v4.34.0 either: `exists.*IsPrefixFree|kraft.*converse` gives no hits,
and `IsPrefixFree` appears only in `PrefixFree.lean` and `Kraft.lean` (order LEAN-22's search).
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

omit [Nonempty α] in
/-- The words of length `L` over `α`, as a finite set of lists. -/
private theorem exists_words (L : ℕ) : ∃ W : Finset (List α),
    (∀ w, w ∈ W ↔ w.length = L) ∧ #W = Fintype.card α ^ L := by
  refine ⟨(Finset.univ : Finset (List.Vector α L)).map
    ⟨List.Vector.toList, List.Vector.toList_injective⟩, fun w ↦ ?_, ?_⟩
  · simp only [mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk]
    exact ⟨fun ⟨v, hv⟩ ↦ hv ▸ v.toList_length, fun h ↦ ⟨⟨w, h⟩, rfl⟩⟩
  · rw [card_map, card_univ, card_vector]

omit [Nonempty α] in
/-- At most `D ^ (L − |u|)` words of length `L` start with `u`. -/
private theorem card_filter_prefix_le [DecidableEq α] {W : Finset (List α)} {L : ℕ}
    (hW : ∀ w, w ∈ W ↔ w.length = L) (u : List α) :
    #(W.filter (u <+: ·)) ≤ Fintype.card α ^ (L - u.length) := by
  obtain ⟨V, hV, hcard⟩ := exists_words (α := α) (L - u.length)
  calc #(W.filter (u <+: ·)) ≤ #(V.image (u ++ ·)) := by
        refine card_le_card fun w hw ↦ ?_
        rw [mem_filter, hW] at hw
        rw [mem_image]
        refine ⟨w.drop u.length, (hV _).mpr (by rw [List.length_drop, hw.1]), ?_⟩
        exact List.prefix_iff_eq_append.mp hw.2
    _ ≤ #V := card_image_le
    _ = _ := hcard

/-- `D ^ L · (1 / D) ^ k = D ^ (L − k)` for `k ≤ L`. -/
private theorem pow_mul_one_div_pow {D : ℝ} (hD : D ≠ 0) {k L : ℕ} (hk : k ≤ L) :
    D ^ L * (1 / D) ^ k = D ^ (L - k) := by
  rw [← Nat.sub_add_cancel hk, pow_add, Nat.add_sub_cancel, mul_assoc, ← mul_pow,
    mul_one_div_cancel hD, one_pow, mul_one]

omit [Fintype ι] in
/-- The induction behind the converse of Kraft's inequality, on a finite set of symbols. -/
private theorem exists_code_on (ℓ : ι → ℕ) (s : Finset ι)
    (hk : ∑ i ∈ s, (1 / (Fintype.card α : ℝ)) ^ ℓ i ≤ 1) :
    ∃ c : ι → List α, (∀ i ∈ s, (c i).length = ℓ i) ∧ Set.InjOn c s ∧
      InformationTheory.IsPrefixFree (c '' s) := by
  classical
  induction s using Finset.induction_on_max_value ℓ with
  | empty => exact ⟨fun _ ↦ [], by simp, by simp, by simp [InformationTheory.IsPrefixFree]⟩
  | insert a s ha hmax ih =>
    rw [sum_insert ha] at hk
    have hD : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
    obtain ⟨c, hlen, hinj, hpf⟩ := ih (le_trans (le_add_of_nonneg_left (by positivity)) hk)
    set L := ℓ a
    obtain ⟨W, hW, hWcard⟩ := exists_words (α := α) L
    set B := s.biUnion fun x ↦ W.filter (c x <+: ·)
    -- the count: fewer than `D ^ L` words of length `L` start with an old codeword
    have hsum : ((∑ x ∈ s, Fintype.card α ^ (L - ℓ x) : ℕ) : ℝ) < (Fintype.card α : ℝ) ^ L := by
      push_cast
      have h1 : ∑ x ∈ s, (Fintype.card α : ℝ) ^ (L - ℓ x) =
          (Fintype.card α : ℝ) ^ L * ∑ x ∈ s, (1 / (Fintype.card α : ℝ)) ^ ℓ x := by
        rw [mul_sum]
        exact sum_congr rfl fun x hx ↦ (pow_mul_one_div_pow hD.ne' (hmax x hx)).symm
      have h2 : (Fintype.card α : ℝ) ^ L * (1 / (Fintype.card α : ℝ)) ^ L = 1 := by
        rw [pow_mul_one_div_pow hD.ne' le_rfl, Nat.sub_self, pow_zero]
      rw [h1]
      nlinarith [pow_pos hD L]
    have hB : #B < #W := by
      rw [hWcard]
      calc #B ≤ ∑ x ∈ s, #(W.filter (c x <+: ·)) := card_biUnion_le
        _ ≤ ∑ x ∈ s, Fintype.card α ^ (L - ℓ x) := sum_le_sum fun x hx ↦ by
          rw [← hlen x hx]; exact card_filter_prefix_le hW (c x)
        _ < Fintype.card α ^ L := by exact_mod_cast hsum
    obtain ⟨w, hwW, hwB⟩ := exists_mem_notMem_of_card_lt_card hB
    have hwl : w.length = L := (hW w).mp hwW
    have hnot : ∀ x ∈ s, ¬ c x <+: w := fun x hx hp ↦
      hwB (mem_biUnion.mpr ⟨x, hx, mem_filter.mpr ⟨hwW, hp⟩⟩)
    have hupd : ∀ x ∈ s, Function.update c a w x = c x := fun x hx ↦
      Function.update_of_ne (by rintro rfl; exact ha hx) _ _
    have himg : Function.update c a w '' ↑(insert a s) = insert w (c '' s) := by
      rw [coe_insert, Set.image_insert_eq, Function.update_self]
      congr 1
      exact Set.image_congr fun x hx ↦ hupd x hx
    refine ⟨Function.update c a w, fun i hi ↦ ?_, ?_, ?_⟩
    · rcases mem_insert.mp hi with rfl | hi
      · rw [Function.update_self, hwl]
      · rw [hupd i hi, hlen i hi]
    · rw [coe_insert, Set.injOn_insert (by exact_mod_cast ha), Function.update_self]
      refine ⟨(hinj.congr fun x hx ↦ (hupd x hx).symm), ?_⟩
      rintro ⟨x, hx, hxw⟩
      rw [hupd x hx] at hxw
      exact hnot x hx (hxw ▸ List.prefix_refl _)
    · rw [himg]
      rintro u (rfl | ⟨i, hi, rfl⟩) v (rfl | ⟨j, hj, rfl⟩) huv
      · rfl
      · exact huv.eq_of_length (le_antisymm huv.length_le (by rw [hwl, hlen j hj]; exact hmax j hj))
      · exact absurd huv (hnot i hi)
      · exact hpf _ (Set.mem_image_of_mem c hi) _ (Set.mem_image_of_mem c hj) huv

/-- **The converse of Kraft's inequality.** Lengths `ℓ i` whose Kraft sum `∑ D^(-ℓ i)` is at
most `1` are the lengths of an injective prefix-free code over an alphabet of `D` letters. -/
theorem exists_isPrefixFree_length_eq (ℓ : ι → ℕ)
    (hkraft : ∑ i, (1 / (Fintype.card α : ℝ)) ^ ℓ i ≤ 1) :
    ∃ c : ι → List α, Function.Injective c ∧ InformationTheory.IsPrefixFree (Set.range c) ∧
      ∀ i, (c i).length = ℓ i := by
  obtain ⟨c, hlen, hinj, hpf⟩ := exists_code_on (α := α) ℓ univ hkraft
  refine ⟨c, ?_, ?_, fun i ↦ hlen i (mem_univ i)⟩
  · rw [coe_univ, Set.injOn_univ] at hinj; exact hinj
  · rw [coe_univ, Set.image_univ] at hpf; exact hpf

omit [Nonempty α] in
/-- **A code within one letter of the entropy.** For a probability vector `p` with every
`p i > 0` and an alphabet of `D ≥ 2` letters, some injective prefix-free code has mean length
below `H(p) / log D + 1`: give symbol `i` a word of length `⌈-log (p i) / log D⌉` (Shannon's
lengths), which pass Kraft's test, and use `exists_isPrefixFree_length_eq`. -/
theorem exists_isPrefixFree_sum_mul_length_lt {p : ι → ℝ} (hp0 : ∀ i, 0 < p i)
    (hp1 : ∑ i, p i = 1) (hα : 2 ≤ Fintype.card α) :
    ∃ c : ι → List α, Function.Injective c ∧ InformationTheory.IsPrefixFree (Set.range c) ∧
      ∑ i, p i * (c i).length < shannonEntropy p / Real.log (Fintype.card α) + 1 := by
  have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  set D : ℝ := (Fintype.card α : ℝ)
  have hD : 1 < D := by
    have : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hα
    simp only [D]; linarith
  have hlog : 0 < Real.log D := Real.log_pos hD
  have hp_le : ∀ i, p i ≤ 1 := fun i ↦
    hp1 ▸ single_le_sum (fun j _ ↦ (hp0 j).le) (mem_univ i)
  have hx0 : ∀ i, 0 ≤ -Real.log (p i) / Real.log D := fun i ↦
    div_nonneg (neg_nonneg.mpr (Real.log_nonpos (hp0 i).le (hp_le i))) hlog.le
  set ℓ : ι → ℕ := fun i ↦ ⌈-Real.log (p i) / Real.log D⌉₊
  have hkraft_i : ∀ i, (1 / D) ^ ℓ i ≤ p i := fun i ↦ by
    have h1 : -Real.log (p i) ≤ ℓ i * Real.log D :=
      (div_le_iff₀ hlog).mp (Nat.le_ceil _)
    rw [← Real.log_le_log_iff (by positivity) (hp0 i), Real.log_pow, one_div, Real.log_inv]
    linarith
  obtain ⟨c, hinj, hpf, hlen⟩ := exists_isPrefixFree_length_eq (α := α) ℓ
    ((sum_le_sum fun i _ ↦ hkraft_i i).trans hp1.le)
  refine ⟨c, hinj, hpf, ?_⟩
  have hne : (univ : Finset ι).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty.mp h, sum_empty] at hp1
    exact zero_ne_one hp1
  calc ∑ i, p i * (c i).length
      < ∑ i, p i * (-Real.log (p i) / Real.log D + 1) := by
        refine sum_lt_sum_of_nonempty hne fun i _ ↦ mul_lt_mul_of_pos_left ?_ (hp0 i)
        rw [hlen i]
        exact Nat.ceil_lt_add_one (hx0 i)
    _ = (∑ i, -(p i * Real.log (p i))) / Real.log D + ∑ i, p i := by
        rw [sum_div, ← sum_add_distrib]
        exact sum_congr rfl fun i _ ↦ by ring
    _ = shannonEntropy p / Real.log D + 1 := by
        rw [sum_neg_distrib, hp1]
        rfl

end ClassicalLean.Simplex

open InformationTheory in
/-- The hypotheses of `shannonEntropy_le_sum_mul_length` hold together: the probability vector
`p = (1/2, 1/4, 1/4)` on three symbols and the binary code `[true]`, `[false, true]`,
`[false, false]`, which is injective, and uniquely decodable because it is prefix-free and does not
contain the empty word. -/
example := ClassicalLean.Simplex.shannonEntropy_le_sum_mul_length (ι := Fin 3) (α := Bool)
  (p := ![1 / 2, 1 / 4, 1 / 4]) (fun i ↦ by fin_cases i <;> norm_num)
  (by simp [Fin.sum_univ_three]; norm_num)
  (c := ![[true], [false, true], [false, false]])
  (fun i j h ↦ by fin_cases i <;> fin_cases j <;> simp_all)
  (IsPrefixFree.isUniquelyDecodable
    (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ h
      fin_cases i <;> fin_cases j <;> simp_all)
    (by rintro ⟨i, hi⟩; fin_cases i <;> simp_all))

open InformationTheory in
/-- The hypotheses of `shannonEntropy_le_sum_mul_length_of_isPrefixFree` hold together: the
probability vector `p = (1/2, 1/4, 1/4)` on three symbols and the binary code `[true]`,
`[false, true]`, `[false, false]`, which is injective and prefix-free. -/
example := ClassicalLean.Simplex.shannonEntropy_le_sum_mul_length_of_isPrefixFree (ι := Fin 3)
  (α := Bool) (p := ![1 / 2, 1 / 4, 1 / 4]) (fun i ↦ by fin_cases i <;> norm_num)
  (by simp [Fin.sum_univ_three]; norm_num)
  (c := ![[true], [false, true], [false, false]])
  (fun i j h ↦ by fin_cases i <;> fin_cases j <;> simp_all)
  (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ h
    fin_cases i <;> fin_cases j <;> simp_all)

/-- The hypotheses of `exists_isPrefixFree_length_eq` hold together: over the binary alphabet,
the lengths `1, 2, 3` have Kraft sum `1/2 + 1/4 + 1/8 = 7/8 ≤ 1`. -/
example := ClassicalLean.Simplex.exists_isPrefixFree_length_eq (ι := Fin 3) (α := Bool)
  (ℓ := ![1, 2, 3]) (by simp [Fin.sum_univ_three]; norm_num)
