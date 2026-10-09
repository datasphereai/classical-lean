/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.InformationTheory.Channel

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
* `mutualInfo_markov_le` — data processing (order LEAN-17): along a Markov chain `X → Y → Z`,
  `I(X; Z) ≤ I(X; Y)`; `Channel`'s `relEntropy_vecMul_le` with the channel `(x, y) ↦ (x, z)`. Each
  hypothesis is needed (order LEAN-17's checks, line C7; each case keeps the other two): a
  negative entry of `P` (`P = [[1/2, -1/2], [1, 1/2]]`, `K = [[0, 1], [0, 1]]`: `-0.608 > -0.811`),
  a negative entry of `K` (`P = [[3/4, 3/4], [0, 1/4]]`, `K = [[-1, 2], [1, 0]]`:
  `-0.262 > -0.824`), and rows of `K` not summing to `1` (`P = [[1/2, 1/2], [0, 1/2]]`,
  `K = [[0, 0], [0, 1]]`: `0 > -0.347`).
* `condEntropy P` — the conditional entropy `H(Y | X)` of the second coordinate given the first,
  `-∑ P (a, b) log (P (a, b) / ∑ b', P (a, b'))` (order LEAN-18).
  It is `-relEntropy P` against the row totals, by definition.
  `condEntropy_eq_sum_mul_shannonEntropy` writes it as the sum over rows of the row total times
  the entropy of that row scaled to sum to `1` (an average of the rows' entropies when `P` is a
  probability vector), for every `P`, with no hypothesis.
* `shannonEntropy_eq_add_condEntropy` — the chain rule, `H(X, Y) = H(X) + H(Y | X)`, for every
  nonnegative `P`, normalised or not. Nonnegativity cannot simply be dropped: `P = [[2, -1, -1]]`
  has row total `0`, and gives `H(P) = -1.386` against `H(X) + H(Y | X) = 0` (order LEAN-18,
  check C9). A row of total `0` that is not all zeros is what breaks it; the identity also holds
  for signed `P` without such a row, which is not stated here.

No support hypothesis appears: for `P ≥ 0`, `P (a, b)` is at most each of its marginals, so the
product of the marginals vanishes only where `P` does, and the junk cell of `relEntropy` never
arises. Both hypotheses of `mutualInfo_nonneg` are needed: `P = [[2]]` is nonnegative and gives
`-2 * log 2`; `P = [[-1/2, -2], [5/2, 1]]` sums to `1` and gives `≈ -2.229`.

Mathlib has no `mutualInfo` at `8f07524533` or at v4.34.0 (`grep -rniE 'mutualInfo'`, 0 hits);
the prior art `github.com/FujiHaruka/information-theory` states it for random variables, as the
KL divergence of the joint law from the product of the marginals — the same definition, in measure
form.

`mutualInfo`'s users outside this module: `InformationTheory/SignalGrowth` (orders LEAN-11 and
LEAN-16). Corrected 2026-10-09 (order LEAN-17, review r7): this paragraph said until then that
`mutualInfo` had no user outside this module, which SignalGrowth's import had already made false.
Subadditivity, the one consequence stated without `mutualInfo`, is a fact about joint distributions
and lives here; a channel-form corollary was drafted and dropped on review because every joint law
already has that form, so it would have added a name and no result. `mutualInfo_markov_le` makes
this module the second to use `InformationTheory/Channel` (after `Simplex/SecondOrder`) and the
first besides `Channel` itself to use its `relEntropy_vecMul_le`.
-/

open Finset Real
open scoped Matrix

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

/-- **Data processing for mutual information.** If `Z` is made from `Y` alone, by a channel `K`
(nonnegative, rows summing to `1`), so that `X → Y → Z` is a Markov chain with joint law
`P (x, y) K y z`, then `I(X; Z) ≤ I(X; Y)`, for every nonnegative `P`. It is
`Channel`'s `relEntropy_vecMul_le` for the channel `(x, y) ↦ (x, z)` with weight `K y z`, which
sends `P` to the law of `(X, Z)`, and the product of `P`'s marginals to the product of the marginals
of the law of `(X, Z)`. -/
theorem mutualInfo_markov_le {γ : Type*} [Fintype γ] {P : α × β → ℝ} (hP : ∀ ab, 0 ≤ P ab)
    {K : Matrix β γ ℝ} (hK0 : ∀ b c, 0 ≤ K b c) (hK1 : ∀ b, ∑ c, K b c = 1) :
    mutualInfo (fun ac : α × γ ↦ ∑ b, P (ac.1, b) * K b ac.2) ≤ mutualInfo P := by
  classical
  -- the channel `(a, b) ↦ (a, c)` with weight `K b c`
  let W : Matrix (α × β) (α × γ) ℝ := fun ab ac ↦ if ab.1 = ac.1 then K ab.2 ac.2 else 0
  have hW0 : ∀ ab ac, 0 ≤ W ab ac := fun ab ac ↦ by
    simp only [W]; split_ifs
    · exact hK0 _ _
    · exact le_rfl
  have hW1 : ∀ ab, ∑ ac, W ab ac = 1 := fun ab ↦ by
    simp only [W, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp [hK1]
  have hvec : ∀ f : α × β → ℝ, ∀ ac : α × γ, (f ᵥ* W) ac = ∑ b, f (ac.1, b) * K b ac.2 := by
    intro f ac
    simp only [Matrix.vecMul, dotProduct, W, Fintype.sum_prod_type, mul_ite, mul_zero]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun b _ ↦ Finset.sum_ite_eq' _ _ _]
    simp
  set Q : α × β → ℝ := fun ab ↦ (∑ b, P (ab.1, b)) * ∑ a, P (a, ab.2) with hQ
  have hQ0 : ∀ ab, 0 ≤ Q ab := fun ab ↦
    mul_nonneg (sum_nonneg fun b _ ↦ hP _) (sum_nonneg fun a _ ↦ hP _)
  have hsupp : ∀ ab, Q ab = 0 → P ab = 0 := by
    rintro ⟨a, b⟩ h
    rcases mul_eq_zero.mp h with h | h
    · exact (sum_eq_zero_iff_of_nonneg fun b _ ↦ hP _).mp h b (mem_univ b)
    · exact (sum_eq_zero_iff_of_nonneg fun a _ ↦ hP _).mp h a (mem_univ a)
  have hdpi := relEntropy_vecMul_le hP hQ0 hsupp hW0 hW1
  -- the joint law of `(X, Z)` is `P ᵥ* W`, and the product of its marginals is `Q ᵥ* W`
  have hX : ∀ a, ∑ c, ∑ b, P (a, b) * K b c = ∑ b, P (a, b) := fun a ↦ by
    rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum, hK1, mul_one]
  have hZ : ∀ c, ∑ a, ∑ b, P (a, b) * K b c = ∑ b, (∑ a, P (a, b)) * K b c := fun c ↦ by
    rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]
  calc mutualInfo (fun ac : α × γ ↦ ∑ b, P (ac.1, b) * K b ac.2)
      = relEntropy (P ᵥ* W) (Q ᵥ* W) := by
        unfold mutualInfo
        congr 1
        · exact funext fun ac ↦ (hvec P ac).symm
        · funext ac
          rw [hvec Q ac, hX, hZ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ ↦ ?_
          simp only [hQ]; ring
    _ ≤ relEntropy P Q := hdpi
    _ = mutualInfo P := rfl

/-- The **conditional entropy** `H(Y | X)` of a joint weight vector `P` on `α × β`: the second
coordinate given the first, `-∑ P (a, b) log (P (a, b) / ∑ b', P (a, b'))`. Each term divides by
the total of its row, which is the chance of `X = a` when `P` sums to `1`. By definition it is
`-relEntropy P` against the vector `(a, b) ↦ ∑ b', P (a, b')`. -/
noncomputable def condEntropy (P : α × β → ℝ) : ℝ :=
  -∑ ab, P ab * Real.log (P ab / ∑ b, P (ab.1, b))

/-- **Conditional entropy row by row.** `H(Y | X)` is the sum over rows of the row total times the
entropy of that row scaled to sum to `1`; when `P` is a probability vector this is the average of
the rows' entropies, weighted by the chance of each row. No hypothesis: a row with total `0`
contributes `0` on both sides. -/
theorem condEntropy_eq_sum_mul_shannonEntropy (P : α × β → ℝ) :
    condEntropy P = ∑ a, (∑ b, P (a, b)) * shannonEntropy (fun b ↦ P (a, b) / ∑ b', P (a, b')) := by
  rw [condEntropy, Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [shannonEntropy, mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rcases eq_or_ne (∑ b', P (a, b')) 0 with h | h
  · simp [h]
  · rw [← mul_assoc, mul_div_cancel₀ _ h]

/-- **The chain rule for entropy**: `H(X, Y) = H(X) + H(Y | X)` for every nonnegative `P`,
normalised or not. Term by term, `log P (a, b)` is the log of the row total plus the log of the
share of the row; where `P (a, b) > 0` the row total is positive too. -/
theorem shannonEntropy_eq_add_condEntropy {P : α × β → ℝ} (hP : ∀ ab, 0 ≤ P ab) :
    shannonEntropy P = shannonEntropy (fun a ↦ ∑ b, P (a, b)) + condEntropy P := by
  have hterm : ∀ a b, P (a, b) * Real.log (P (a, b)) = P (a, b) * Real.log (∑ b', P (a, b'))
      + P (a, b) * Real.log (P (a, b) / ∑ b', P (a, b')) := by
    intro a b
    rcases (hP (a, b)).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have hm : 0 < ∑ b', P (a, b') :=
        hpos.trans_le (Finset.single_le_sum (fun b' _ ↦ hP (a, b')) (Finset.mem_univ b))
      rw [Real.log_div hpos.ne' hm.ne']
      ring
  have e1 : ∑ a, (∑ b, P (a, b)) * Real.log (∑ b, P (a, b))
      = ∑ a, ∑ b, P (a, b) * Real.log (∑ b', P (a, b')) :=
    Finset.sum_congr rfl fun a _ ↦ Finset.sum_mul _ _ _
  rw [shannonEntropy, shannonEntropy, condEntropy, Fintype.sum_prod_type, Fintype.sum_prod_type, e1]
  simp_rw [hterm, Finset.sum_add_distrib]
  ring

end ClassicalLean.Simplex
