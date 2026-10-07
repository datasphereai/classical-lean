/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.InformationTheory.Entropy

/-!
# Mutual information of a finite joint distribution

A joint distribution on `α × β` is a vector `P : α × β → ℝ`; its marginals are
`fun a => ∑ b, P (a, b)` and `fun b => ∑ a, P (a, b)`, written out rather than named, so that no
definition is added without a use.

* `mutualInfo P` — the relative entropy of `P` to the product of its marginals.
* `mutualInfo_nonneg` and `mutualInfo_eq_zero_iff` — nonnegative on probability vectors, and zero
  exactly when `P` factorises as `P (a, b) = r a * s b`, i.e. at independence.
* `mutualInfo_eq_shannonEntropy_add_shannonEntropy_sub_shannonEntropy` —
  `I(P) = H(marginal₁) + H(marginal₂) - H(P)` for every nonnegative `P`, normalised or not.
* `shannonEntropy_le_shannonEntropy_add_shannonEntropy` — subadditivity, `H(X, Y) ≤ H(X) + H(Y)`.

No support hypothesis appears: for `P ≥ 0`, `P (a, b)` is at most each of its marginals, so the
product of the marginals vanishes only where `P` does, and the junk cell of `relEntropy` never
arises. Both hypotheses of `mutualInfo_nonneg` are needed: `P = [[2]]` is nonnegative and gives
`-2 * log 2`; `P = [[-1/2, -2], [5/2, 1]]` sums to `1` and gives `≈ -2.229`.

Mathlib has no `mutualInfo` at `8f07524533` or at v4.34.0 (`grep -rniE 'mutualInfo'`, 0 hits);
the prior art `github.com/FujiHaruka/information-theory` states it for random variables, as the
KL divergence of the joint law from the product of the marginals — the same definition, in measure
form.

`mutualInfo` has no user outside this module. Its one consequence stated without it,
subadditivity, is a fact about joint distributions and lives here; a channel-form corollary was
drafted and dropped on review because every joint law already has that form, so it would have added
a name and no result.
-/

open Finset Real

namespace ClassicalLean.Simplex

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The **mutual information** of a joint weight vector `P` on `α × β`: its relative entropy to the
product of its two marginals. -/
noncomputable def mutualInfo (P : α × β → ℝ) : ℝ :=
  relEntropy P (fun ab => (∑ b, P (ab.1, b)) * ∑ a, P (a, ab.2))

/-- The product of the marginals of a probability vector is a probability vector, and it vanishes
only where `P` does — the three facts Gibbs' inequality needs. -/
private theorem product_facts {P : α × β → ℝ} (hP0 : ∀ ab, 0 ≤ P ab) (hP1 : ∑ ab, P ab = 1) :
    (∀ ab : α × β, 0 ≤ (∑ b, P (ab.1, b)) * ∑ a, P (a, ab.2)) ∧
      ∑ ab : α × β, (∑ b, P (ab.1, b)) * ∑ a, P (a, ab.2) = 1 ∧
      ∀ ab : α × β, (∑ b, P (ab.1, b)) * ∑ a, P (a, ab.2) = 0 → P ab = 0 := by
  refine ⟨fun ab => mul_nonneg (Finset.sum_nonneg fun b _ => hP0 _)
    (Finset.sum_nonneg fun a _ => hP0 _), ?_, ?_⟩
  · have h1 : ∑ a, ∑ b, P (a, b) = 1 := by rw [← Fintype.sum_prod_type, hP1]
    have h2 : ∑ b, ∑ a, P (a, b) = 1 := by rw [Finset.sum_comm, ← Fintype.sum_prod_type, hP1]
    rw [Fintype.sum_prod_type]
    calc ∑ a, ∑ b, (∑ b', P (a, b')) * ∑ a', P (a', b)
        = (∑ a, ∑ b', P (a, b')) * ∑ b, ∑ a', P (a', b) := (Finset.sum_mul_sum _ _ _ _).symm
      _ = 1 := by rw [h1, h2, one_mul]
  · rintro ⟨a, b⟩ h
    have h' : (∑ b', P (a, b')) * ∑ a', P (a', b) = 0 := h
    have hle1 : P (a, b) ≤ ∑ b', P (a, b') :=
      Finset.single_le_sum (fun b' _ => hP0 (a, b')) (Finset.mem_univ b)
    have hle2 : P (a, b) ≤ ∑ a', P (a', b) :=
      Finset.single_le_sum (fun a' _ => hP0 (a', b)) (Finset.mem_univ a)
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact le_antisymm (h1 ▸ hle1) (hP0 _)
    · exact le_antisymm (h1 ▸ hle2) (hP0 _)

/-- **Mutual information is nonnegative** on probability vectors. -/
theorem mutualInfo_nonneg {P : α × β → ℝ} (hP0 : ∀ ab, 0 ≤ P ab) (hP1 : ∑ ab, P ab = 1) :
    0 ≤ mutualInfo P := by
  obtain ⟨hq0, hq1, hsupp⟩ := product_facts hP0 hP1
  exact relEntropy_nonneg hP0 hP1 hq0 hq1 hsupp

/-- **Mutual information vanishes exactly at independence**: on probability vectors, `I(P) = 0`
if and only if `P` factorises as `P (a, b) = r a * s b`. -/
theorem mutualInfo_eq_zero_iff {P : α × β → ℝ} (hP0 : ∀ ab, 0 ≤ P ab) (hP1 : ∑ ab, P ab = 1) :
    mutualInfo P = 0 ↔ ∃ r : α → ℝ, ∃ s : β → ℝ, ∀ a b, P (a, b) = r a * s b := by
  obtain ⟨hq0, hq1, hsupp⟩ := product_facts hP0 hP1
  rw [mutualInfo, relEntropy_eq_zero_iff hP0 hP1 hq0 hq1 hsupp]
  constructor
  · intro h
    exact ⟨fun a => ∑ b, P (a, b), fun b => ∑ a, P (a, b), fun a b => congrFun h (a, b)⟩
  · rintro ⟨r, s, hrs⟩
    have htot : (∑ a, r a) * ∑ b, s b = 1 := by
      rw [Finset.sum_mul_sum, ← hP1, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => (hrs a b).symm
    funext ab
    obtain ⟨a, b⟩ := ab
    change P (a, b) = (∑ b', P (a, b')) * ∑ a', P (a', b)
    have hR : ∑ b', P (a, b') = r a * ∑ b', s b' := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b' _ => hrs a b'
    have hS : ∑ a', P (a', b) = (∑ a', r a') * s b := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a' _ => hrs a' b
    rw [hR, hS, hrs]
    calc r a * s b = r a * s b * ((∑ a', r a') * ∑ b', s b') := by rw [htot, mul_one]
      _ = r a * (∑ b', s b') * ((∑ a', r a') * s b) := by ring

/-- **Mutual information in terms of entropies**: `I(P) = H(marginal₁) + H(marginal₂) - H(P)` for
every nonnegative `P`, normalised or not. Nonnegativity is needed: with a zero marginal made of
entries of both signs the identity fails. -/
theorem mutualInfo_eq_shannonEntropy_add_shannonEntropy_sub_shannonEntropy
    {P : α × β → ℝ} (hP : ∀ ab, 0 ≤ P ab) :
    mutualInfo P = shannonEntropy (fun a => ∑ b, P (a, b))
      + shannonEntropy (fun b => ∑ a, P (a, b)) - shannonEntropy P := by
  have hterm : ∀ a b, P (a, b) * Real.log (P (a, b) / ((∑ b', P (a, b')) * ∑ a', P (a', b)))
      = P (a, b) * Real.log (P (a, b)) - P (a, b) * Real.log (∑ b', P (a, b'))
        - P (a, b) * Real.log (∑ a', P (a', b)) := by
    intro a b
    by_cases h0 : P (a, b) = 0
    · rw [h0]
      simp
    · have hpos : 0 < P (a, b) := lt_of_le_of_ne (hP _) (Ne.symm h0)
      have h1 : 0 < ∑ b', P (a, b') := lt_of_lt_of_le hpos
        (Finset.single_le_sum (fun b' _ => hP (a, b')) (Finset.mem_univ b))
      have h2 : 0 < ∑ a', P (a', b) := lt_of_lt_of_le hpos
        (Finset.single_le_sum (fun a' _ => hP (a', b)) (Finset.mem_univ a))
      rw [Real.log_div h0 (mul_pos h1 h2).ne', Real.log_mul h1.ne' h2.ne']
      ring
  have hmain : mutualInfo P = ∑ a, ∑ b, P (a, b) * Real.log (P (a, b))
      - ∑ a, ∑ b, P (a, b) * Real.log (∑ b', P (a, b'))
      - ∑ a, ∑ b, P (a, b) * Real.log (∑ a', P (a', b)) := by
    rw [mutualInfo, relEntropy, Fintype.sum_prod_type, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => hterm a b
  have e1 : ∑ a, ∑ b, P (a, b) * Real.log (P (a, b)) = -shannonEntropy P := by
    rw [shannonEntropy, neg_neg, Fintype.sum_prod_type]
  have e2 : ∑ a, ∑ b, P (a, b) * Real.log (∑ b', P (a, b'))
      = -shannonEntropy (fun a => ∑ b, P (a, b)) := by
    rw [shannonEntropy, neg_neg]
    exact Finset.sum_congr rfl fun a _ => (Finset.sum_mul _ _ _).symm
  have e3 : ∑ a, ∑ b, P (a, b) * Real.log (∑ a', P (a', b))
      = -shannonEntropy (fun b => ∑ a, P (a, b)) := by
    rw [shannonEntropy, neg_neg, Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => (Finset.sum_mul _ _ _).symm
  rw [hmain, e1, e2, e3]
  ring

/-- **Subadditivity of entropy**: `H(X, Y) ≤ H(X) + H(Y)` for a joint probability vector, the
difference being the mutual information. -/
theorem shannonEntropy_le_shannonEntropy_add_shannonEntropy {P : α × β → ℝ}
    (hP0 : ∀ ab, 0 ≤ P ab) (hP1 : ∑ ab, P ab = 1) :
    shannonEntropy P
      ≤ shannonEntropy (fun a => ∑ b, P (a, b)) + shannonEntropy (fun b => ∑ a, P (a, b)) := by
  have h := mutualInfo_nonneg hP0 hP1
  rw [mutualInfo_eq_shannonEntropy_add_shannonEntropy_sub_shannonEntropy hP0] at h
  linarith

end ClassicalLean.Simplex
