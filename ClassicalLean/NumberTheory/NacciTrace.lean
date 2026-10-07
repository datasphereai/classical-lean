/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import ClassicalLean.NumberTheory.Lucas
import ClassicalLean.NumberTheory.Mersenne

/-!
# The n-nacci trace tower and its Mersenne prefix

For a parameter `n`, this file studies the integer sequence `A n` defined by

* `A n 0 = n + 1`,
* `A n 1 = 2`,
* `A n k = 2 * A n (k - 1)` for `2 ≤ k ≤ n`,
* `A n k = 2 * A n (k - 1) - A n (k - (n + 1))` for `k ≥ n + 1`,

and its shift `S n k = A n k - 1`.  The last two lines are the two branches of the single
recursive equation of `nacciAugmented`, and are recorded separately as
`nacciAugmented_double` and `nacciAugmented_sub`.  Both sequences are *defined* this way;
everything below is a statement about the recurrence and is proved from it.

Context, not formalised here.  The recurrence is the one Newton's identities produce for the
power sums of the roots of `x ^ (n + 1) - 2 * x ^ n + 1`, which is `(x - 1)` times the n-nacci
characteristic polynomial `x ^ n - x ^ (n - 1) - ⋯ - x - 1`; on that reading `A n k` is the
`k`-th power sum of the roots of the augmented polynomial, the extra root `1` contributes the
`- 1` in `S`, and `S n k` is the `k`-th power sum of the roots of the n-nacci polynomial
itself.  No splitting field, no polynomial and no root appears anywhere below, and no result
in this file depends on that reading; it is recorded only to explain the shape of the
recurrence and the names.

## Main definitions

* `ClassicalLean.nacciAugmented` — the sequence `A` above.
* `ClassicalLean.nacciTrace` — the shift `S n k = A n k - 1`.

## Main results

* `nacciTrace_mersenne_prefix` : `S n k = 2 ^ k - 1` for `1 ≤ k ≤ n`, and
  `nacciTrace_eq_mersenne` : the same statement written against Mathlib's `mersenne`,
  `S n k = M k`.  This is the reason for the name: at the indices `k = 1, 2, …, n`, and only
  there, the row `S n` runs through `M 1, M 2, …, M n`.  Index `0` is outside the claim —
  `S n 0 = n`, which is `M 0 = 0` only when `n = 0` — so this is a statement about `n` of the
  terms, not about the first `n` terms of a `0`-indexed sequence.  At `n = 0` the index range
  is empty and the statement is vacuous; at `n = 1` it has the single instance `S 1 1 = 1`.
* `nacciTrace_departure` : at the first index past the prefix the pattern breaks by exactly
  `n + 1`, `S n (n + 1) = 2 ^ (n + 1) - 1 - (n + 1)`.
* `nacciTrace_recurrence` : for `k ≥ n + 1`, `S n (k + 1) = 2 * S n k - S n (k - n)`.
* `nacciTrace_master` : the three statements above packaged for `n ≥ 2`.
* `nacciTrace_two_eq_lucas` : `S 2 k = L k` for every `k`, where `L` is `ClassicalLean.lucas`
  from `ClassicalLean/NumberTheory/Lucas.lean`.  So the `n = 2` row of the tower is the Lucas
  sequence.  Composing that with `nacciTrace_eq_mersenne` at `n = 2` gives `L 1 = M 1` and
  `L 2 = M 2`.  That composition is *not* shipped as a named theorem — it is two literal
  indices, not a general statement — but it is not merely asserted either: the last two
  `example`s in this file are exactly that composition of the two theorems, term for term.

## Source

Ported from `LP0002/MersennePrefix.lean`: its two definitions `q` and `Tr` are carried over
as `nacciAugmented` and `nacciTrace`, and all twelve of its theorems are shipped, renamed off
those two names and otherwise stated unchanged (`q_succ_succ` is `nacciAugmented_add_two`,
`q_aug` is `nacciAugmented_sub`, `q_aug_recurrence` is `nacciAugmented_recurrence`,
`mersenne_prefix_general` is `nacciTrace_master`).  Nothing from that file was dropped.
`nacciTrace_sub`, `nacciTrace_eq_mersenne` and `nacciTrace_two_eq_lucas` are additions, the
last two bridging to Mathlib's `mersenne` and to `ClassicalLean.lucas`.
-/

namespace ClassicalLean

/-! ### The two sequences -/

/-- The augmented tower `A n`.  See the module docstring for the four defining equations; the
branch on `k + 2 ≤ n` is what separates the doubling regime from the corrected one. -/
def nacciAugmented (n : ℕ) : ℕ → ℤ
  | 0 => (n : ℤ) + 1
  | 1 => 2
  | k + 2 =>
      if k + 2 ≤ n then 2 * nacciAugmented n (k + 1)
      else 2 * nacciAugmented n (k + 1) - nacciAugmented n ((k + 2) - (n + 1))

/-- The trace tower `S n k = A n k - 1`.  This is a definition, not a derived identity. -/
def nacciTrace (n k : ℕ) : ℤ := nacciAugmented n k - 1

/-- `A n 0 = n + 1`: the first clause of the definition, restated as a `simp` lemma.

It carries no content beyond the `def`.  `nacciAugmented` is compiled by well-founded
recursion, so — measured — `rfl` does **not** close it; what discharges it is the equation
lemma of the definition, applied by `simp [nacciAugmented]`. -/
@[simp] theorem nacciAugmented_zero (n : ℕ) : nacciAugmented n 0 = (n : ℤ) + 1 := by
  simp [nacciAugmented]

/-- `A n 1 = 2`: the second clause of the definition, restated as a `simp` lemma.  As with
`nacciAugmented_zero` it carries no content beyond the `def`, and `rfl` does not close it. -/
@[simp] theorem nacciAugmented_one (n : ℕ) : nacciAugmented n 1 = 2 := by
  simp [nacciAugmented]

/-- The defining equation at index `k + 2`, with its branch intact.

Like the two above, this is the `def` restated and nothing more; it is the equation lemma,
not `rfl`.  The two theorems after it are the useful form — each branch taken separately
under the hypothesis that selects it. -/
theorem nacciAugmented_add_two (n k : ℕ) :
    nacciAugmented n (k + 2) =
      if k + 2 ≤ n then 2 * nacciAugmented n (k + 1)
      else 2 * nacciAugmented n (k + 1) - nacciAugmented n ((k + 2) - (n + 1)) := by
  simp [nacciAugmented]

/-- Inside the prefix range the branch collapses to plain doubling:
`A n m = 2 * A n (m - 1)` whenever `2 ≤ m ≤ n`. -/
theorem nacciAugmented_double (n m : ℕ) (h1 : 2 ≤ m) (h2 : m ≤ n) :
    nacciAugmented n m = 2 * nacciAugmented n (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [nacciAugmented_add_two]
  rw [show k + 2 - 1 = k + 1 from by omega, ite_eq_left h2]

/-- Past the prefix the correction term fires:
`A n m = 2 * A n (m - 1) - A n (m - (n + 1))` whenever `2 ≤ m` and `n + 1 ≤ m`. -/
theorem nacciAugmented_sub (n m : ℕ) (h1 : 2 ≤ m) (h2 : n + 1 ≤ m) :
    nacciAugmented n m = 2 * nacciAugmented n (m - 1) - nacciAugmented n (m - (n + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [nacciAugmented_add_two]
  rw [show k + 2 - 1 = k + 1 from by omega, ite_eq_right (by omega)]

/-- The step law of `nacciAugmented_sub`, transported to `S`. -/
theorem nacciTrace_sub (n m : ℕ) (h1 : 2 ≤ m) (h2 : n + 1 ≤ m) :
    nacciTrace n m = 2 * nacciTrace n (m - 1) - nacciTrace n (m - (n + 1)) := by
  simp only [nacciTrace, nacciAugmented_sub n m h1 h2]
  ring

/-! ### The Mersenne prefix -/

/-- On the augmented tower: `A n k = 2 ^ k` for `1 ≤ k ≤ n`. -/
theorem nacciAugmented_mersenne_prefix (n k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ n) :
    nacciAugmented n k = 2 ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      simp
    · have hd : nacciAugmented n (k + 1) = 2 * nacciAugmented n k := by
        have h := nacciAugmented_double n (k + 1) (by omega) h2
        rwa [show k + 1 - 1 = k from by omega] at h
      rw [hd, ih (by omega) (by omega)]
      ring

/-- The Mersenne prefix: `S n k = 2 ^ k - 1` for `1 ≤ k ≤ n`. -/
theorem nacciTrace_mersenne_prefix (n k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ n) :
    nacciTrace n k = 2 ^ k - 1 := by
  simp [nacciTrace, nacciAugmented_mersenne_prefix n k h1 h2]

/-- The Mersenne prefix against Mathlib's `mersenne`: for `1 ≤ k ≤ n`, `S n k = M k`.

This is `nacciTrace_mersenne_prefix` with `2 ^ k - 1` recognised as `mersenne k`; the cast
from `ℕ` to `ℤ` is exact because `1 ≤ 2 ^ k`, which is **Lean core's** `Nat.one_le_two_pow`
(`Init.Data.Nat.Lemmas`), not Mathlib's — resolved with `Environment.getModuleFor?` rather
than assumed. -/
theorem nacciTrace_eq_mersenne (n k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ n) :
    nacciTrace n k = (mersenne k : ℤ) := by
  have hm : (mersenne k : ℤ) = 2 ^ k - 1 := by
    have hle : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
    have hdef : mersenne k = 2 ^ k - 1 := rfl
    rw [hdef, Nat.cast_sub hle]
    push_cast
    ring
  rw [nacciTrace_mersenne_prefix n k h1 h2, hm]

/-! ### Departure from the prefix -/

/-- On the augmented tower: `A n (n + 1) = 2 ^ (n + 1) - (n + 1)` for `n ≥ 1`. -/
theorem nacciAugmented_departure (n : ℕ) (hn : 1 ≤ n) :
    nacciAugmented n (n + 1) = 2 ^ (n + 1) - ((n : ℤ) + 1) := by
  have h := nacciAugmented_sub n (n + 1) (by omega) (le_refl _)
  rw [show n + 1 - 1 = n from by omega, show n + 1 - (n + 1) = 0 from by omega] at h
  rw [h, nacciAugmented_zero, nacciAugmented_mersenne_prefix n n hn (le_refl _)]
  ring

/-- Departure: the term immediately after the Mersenne prefix falls short of `2 ^ (n+1) - 1`
by exactly `n + 1`.  For `n ≥ 1`, `S n (n + 1) = 2 ^ (n + 1) - 1 - (n + 1)`. -/
theorem nacciTrace_departure (n : ℕ) (hn : 1 ≤ n) :
    nacciTrace n (n + 1) = 2 ^ (n + 1) - 1 - ((n : ℤ) + 1) := by
  rw [nacciTrace, nacciAugmented_departure n hn]
  ring

/-! ### The recurrence past the prefix -/

/-- On the augmented tower: for `n + 1 ≤ k`, `A n (k + 1) = 2 * A n k - A n (k - n)`. -/
theorem nacciAugmented_recurrence (n k : ℕ) (h : n + 1 ≤ k) :
    nacciAugmented n (k + 1) = 2 * nacciAugmented n k - nacciAugmented n (k - n) := by
  have hs := nacciAugmented_sub n (k + 1) (by omega) (by omega)
  rwa [show k + 1 - 1 = k from by omega, show k + 1 - (n + 1) = k - n from by omega] at hs

/-- For `n + 1 ≤ k`, `S n (k + 1) = 2 * S n k - S n (k - n)`. -/
theorem nacciTrace_recurrence (n k : ℕ) (h : n + 1 ≤ k) :
    nacciTrace n (k + 1) = 2 * nacciTrace n k - nacciTrace n (k - n) := by
  rw [nacciTrace, nacciTrace, nacciTrace, nacciAugmented_recurrence n k h]
  ring

/-- The three statements above, packaged for `n ≥ 2`: the Mersenne prefix, the departure and
the recurrence past the prefix.

This is a repackaging and proves nothing new: every conjunct is one of the named theorems,
applied to its own hypotheses, and the term below is the triple of those three applications.
The hypothesis `2 ≤ n` is used only to supply `1 ≤ n` to the departure clause. -/
theorem nacciTrace_master (n : ℕ) (hn : 2 ≤ n) :
    (∀ k, 1 ≤ k → k ≤ n → nacciTrace n k = 2 ^ k - 1) ∧
      nacciTrace n (n + 1) = 2 ^ (n + 1) - 1 - ((n : ℤ) + 1) ∧
      ∀ k, n + 1 ≤ k → nacciTrace n (k + 1) = 2 * nacciTrace n k - nacciTrace n (k - n) :=
  ⟨fun k hk1 hkn => nacciTrace_mersenne_prefix n k hk1 hkn,
    nacciTrace_departure n (by omega),
    fun k hk => nacciTrace_recurrence n k hk⟩

/-! ### The row `n = 2` is the Lucas sequence -/

/-- `S 2 k = L k` for every `k`, where `L` is `ClassicalLean.lucas`.

Both sides satisfy `x (k + 3) = 2 * x (k + 2) - x k` — for `S 2` that is `nacciTrace_sub`,
for `L` it is the Lucas recurrence used twice — and they agree at `k = 0, 1, 2`, so a
three-term induction identifies them. -/
theorem nacciTrace_two_eq_lucas (k : ℕ) : nacciTrace 2 k = (lucas k : ℤ) := by
  have key : ∀ m : ℕ, nacciTrace 2 m = (lucas m : ℤ) ∧
      nacciTrace 2 (m + 1) = (lucas (m + 1) : ℤ) ∧
      nacciTrace 2 (m + 2) = (lucas (m + 2) : ℤ) := by
    intro m
    induction m with
    | zero => refine ⟨?_, ?_, ?_⟩ <;> norm_num [nacciTrace, nacciAugmented]
    | succ j ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      refine ⟨h1, h2, ?_⟩
      have hs : nacciTrace 2 (j + 3) = 2 * nacciTrace 2 (j + 2) - nacciTrace 2 j := by
        have h := nacciTrace_sub 2 (j + 3) (by omega) (by omega)
        rwa [show j + 3 - 1 = j + 2 from by omega,
          show j + 3 - (2 + 1) = j from by omega] at h
      have e1 : (lucas (j + 3) : ℤ) = (lucas (j + 2) : ℤ) + (lucas (j + 1) : ℤ) :=
        lucas_add_two_int (j + 1)
      have e2 : (lucas (j + 2) : ℤ) = (lucas (j + 1) : ℤ) + (lucas j : ℤ) :=
        lucas_add_two_int j
      rw [show j + 1 + 2 = j + 3 from rfl, hs, h0, h2]
      linarith
  exact (key k).1

/-! ### Computed examples -/

-- The `n = 5` row opens with `M 1, …, M 5 = 1, 3, 7, 15, 31` and then departs by `6`.
example : nacciTrace 5 3 = 7 := by norm_num [nacciTrace, nacciAugmented]

example : nacciTrace 5 5 = 31 := by norm_num [nacciTrace, nacciAugmented]

example : nacciTrace 5 5 = (mersenne 5 : ℤ) := by norm_num [nacciTrace, nacciAugmented, mersenne]

example : nacciTrace 5 6 = 2 ^ 6 - 1 - 6 := by norm_num [nacciTrace, nacciAugmented]

-- The `n = 2` row is `2, 1, 3, 4, 7, 11, 18, …`, the Lucas sequence.
example : nacciTrace 2 6 = 18 := by norm_num [nacciTrace, nacciAugmented]

example : nacciTrace 2 6 = (lucas 6 : ℤ) := by
  have hl : lucas 6 = 18 := by decide
  norm_num [nacciTrace, nacciAugmented, hl]

-- The `n = 3` row: `1, 3, 7` and then `11 = 2 ^ 4 - 1 - 4`.
example : nacciTrace 3 4 = 11 := by norm_num [nacciTrace, nacciAugmented]

-- `L 1 = M 1` and `L 2 = M 2`: the Lucas row's own Mersenne prefix.  These two are not
-- arithmetic checks — each is the composition of `nacciTrace_two_eq_lucas` with
-- `nacciTrace_eq_mersenne` at `n = 2`, which is what the module docstring says they are.
example : (lucas 1 : ℤ) = (mersenne 1 : ℤ) :=
  (nacciTrace_two_eq_lucas 1).symm.trans (nacciTrace_eq_mersenne 2 1 (by decide) (by decide))

example : (lucas 2 : ℤ) = (mersenne 2 : ℤ) :=
  (nacciTrace_two_eq_lucas 2).symm.trans (nacciTrace_eq_mersenne 2 2 (by decide) (by decide))

end ClassicalLean
