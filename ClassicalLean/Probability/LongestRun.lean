/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real

/-!
# Streaks under chance

In `n` independent trials that each lose with chance `q`, how likely is a streak of `r` losses in
a row? Order LEAN-26, item 69 of the plan.

* `measureReal_exists_run_le`: the chance of some run of at least `r` losses is at most
  `(n − r + 1) q^r` (a union bound over the `n − r + 1` places a run can start).
* `measureReal_no_run_le`: the chance of no such run is at most `(1 − q^r)^⌊n / r⌋` (the `⌊n / r⌋`
  disjoint blocks of `r` trials are independent, and none of them may be all losses).

**The setting.** `A i` is the event "trial `i` is a loss", for the trials `i = 0, …, n − 1`. The
trials are independent: `iIndepSet (fun i : Fin n ↦ A i) P` (Mathlib's mutual independence of the
events, which says the chance of any finite intersection is the product). Each loses with chance
`q`: `P.real (A i) = q` for `i < n`. The trials from `n` on play no part. No separate assumption
that `P` is a probability measure is made: Mathlib's `iIndepSet.isProbabilityMeasure` derives it
from the independence (review r69 of order LEAN-26).

**A run of losses.** `runEvent A n r` is the event that for some start `s` with `s + r ≤ n`, the
trials `s, s + 1, …, s + r − 1` are all losses. A longer streak contains one of length `r`, so this
is "a run of at least `r` losses".

The edge cases, with Lean's conventions (order LEAN-26's checks, lines R5 and R6, exact):

* `r = 0`: every outcome has a run of length `0` (`s = 0`), so the first chance is `1 ≤ n + 1`;
  the second bound is `(1 − 1)^⌊n / 0⌋ = 0^0 = 1` (Lean's `n / 0 = 0`), against a chance `0`.
* `r > n`: no run fits, the chance is `0`. The factor `n + 1 − r` is subtraction in `ℕ`, which
  stops at `0`. In `ℝ` it would be negative for `r ≥ n + 2`: with `n = 3`, `r = 5`, `q = 1/2`, the
  bound `(n − r + 1) q^r = −1/32` would be false.

Each other hypothesis is needed (lines R3 and R4):

* independence, for the first bound: all trials one fair coin (`A i = A 0`), `n = 10`, `r = 5`:
  a run has chance `1/2 > 6 · 2⁻⁵ = 3/16`.
* independence, for the second bound: alternating trials (trial `i + 1` loses exactly when trial
  `i` wins), each with chance `1/2`, `n = 4`, `r = 2`: no run has chance `1 > (3/4)^2 = 9/16`.
* The second theorem also assumes each `A i` measurable, which Mathlib's lemma on independence
  of disjoint groups of events asks for; whether the bound needs it is not settled here.

Measured in the same checks (exact dynamic programming, not proved in Lean): both bounds hold for
`q ∈ {1/2, 1/3, 3/5, 9/10}`, `n ≤ 40`, every `r ≤ n + 3` (line R1); for fair trials the mean
longest run in `100` trials is `5.99` and a run of `7` or more in `200` trials has chance `0.544`
(line R2, the plan's numbers). For fair trials the first bound is small once `2^r` is large
against `n`, that is `r` past about `log₂ n`. The second bound gives the other side, by hand
(`1 − x ≤ e^(−x)`, not proved here): no run of `r` has chance at most `exp (−⌊n / r⌋ / 2^r)`, which
is small once `r` is below about `log₂ n − log₂ log₂ n`. So for fair trials the longest run is
near `log₂ n`, and a streak counts as evidence only past these numbers.
The first bound is exact when `n = r` (line R7).

## What Mathlib provides

`iIndepSet.meas_biInter`, `iIndepSet.indep_generateFrom_of_disjoint`, `Indep_iff` and
`measureReal_biUnion_finset_le`. Mathlib v4.34.0 has no result on runs: `longest run|run of heads`
finds only the random-graph model, and `streak` and `runs of` give no hits (order LEAN-26's
search).
-/

open MeasureTheory ProbabilityTheory Finset

namespace ClassicalLean.Probability.LongestRun

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- Some `r` consecutive trials among the first `n`, the trials `s, s + 1, …, s + r − 1` with
`s + r ≤ n`, are all losses. -/
def runEvent (A : ℕ → Set Ω) (n r : ℕ) : Set Ω :=
  {ω | ∃ s, s + r ≤ n ∧ ∀ i ∈ Ico s (s + r), ω ∈ A i}

/-- The trials `s, …, s + r − 1`, as indices in `Fin n`. -/
def block (n s r : ℕ) : Finset (Fin n) := univ.filter fun j ↦ s ≤ (j : ℕ) ∧ (j : ℕ) < s + r

/-- There are `r` trials in a block that fits. -/
lemma card_block {n s r : ℕ} (h : s + r ≤ n) : (block n s r).card = r := by
  have : (block n s r).map Fin.valEmbedding = Ico s (s + r) := by
    ext i
    simp only [block, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ico]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro hi; exact ⟨⟨i, by omega⟩, hi, rfl⟩
  rw [← card_map, this, Nat.card_Ico]; omega

lemma iInter_block {A : ℕ → Set Ω} {n s r : ℕ} (h : s + r ≤ n) :
    ⋂ j ∈ block n s r, A (j : ℕ) = ⋂ i ∈ Ico s (s + r), A i := by
  ext ω
  simp only [Set.mem_iInter, block, mem_filter, mem_univ, true_and, mem_Ico]
  constructor
  · intro hω i hi; exact hω ⟨i, by omega⟩ hi
  · intro hω j hj; exact hω j hj

lemma measureReal_iInter_Ico {P : Measure Ω} {A : ℕ → Set Ω} {n s r : ℕ} {q : ℝ}
    (hind : iIndepSet (fun i : Fin n ↦ A i) P) (hq : ∀ i < n, P.real (A i) = q)
    (h : s + r ≤ n) : P.real (⋂ i ∈ Ico s (s + r), A i) = q ^ r := by
  rw [← iInter_block h, measureReal_def, hind.meas_biInter, ENNReal.toReal_prod]
  simp_rw [← measureReal_def]
  rw [prod_congr rfl fun (j : Fin n) _ ↦ hq j j.isLt, prod_const, card_block h]

/-- **A streak is unlikely when `(n − r + 1) q^r` is small.** In `n` independent trials that each
lose with chance `q`, the chance of some run of at least `r` losses is at most `(n + 1 − r) q^r`,
with subtraction in `ℕ`. -/
theorem measureReal_exists_run_le {P : Measure Ω} {A : ℕ → Set Ω}
    {n r : ℕ} {q : ℝ} (hind : iIndepSet (fun i : Fin n ↦ A i) P)
    (hq : ∀ i < n, P.real (A i) = q) :
    P.real (runEvent A n r) ≤ ((n + 1 - r : ℕ) : ℝ) * q ^ r := by
  have := hind.isProbabilityMeasure
  have hset : runEvent A n r = ⋃ s ∈ range (n + 1 - r), ⋂ i ∈ Ico s (s + r), A i := by
    ext ω
    simp only [runEvent, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, mem_range, exists_prop]
    constructor
    · rintro ⟨s, hs, h⟩; exact ⟨s, by omega, h⟩
    · rintro ⟨s, hs, h⟩; exact ⟨s, by omega, h⟩
  rw [hset]
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  rw [sum_congr rfl fun s hs ↦ measureReal_iInter_Ico hind hq (by
    have := mem_range.mp hs; omega), sum_const, card_range, nsmul_eq_mul]

/-- The `j`-th block of `r` trials, `j r, …, j r + r − 1`, holds only losses. -/
def allLost (A : ℕ → Set Ω) (r j : ℕ) : Set Ω := ⋂ i ∈ Ico (j * r) (j * r + r), A i

lemma measurableSet_allLost {A : ℕ → Set Ω} (hA : ∀ i, MeasurableSet (A i)) (r j : ℕ) :
    MeasurableSet (allLost A r j) :=
  Finset.measurableSet_biInter _ fun i _ ↦ hA i

/-- **No streak is unlikely when `(1 − q^r)^⌊n / r⌋` is small.** In `n` independent trials that
each lose with chance `q`, the chance of no run of `r` losses is at most `(1 − q^r)^⌊n / r⌋`. -/
theorem measureReal_no_run_le {P : Measure Ω} {A : ℕ → Set Ω}
    {n r : ℕ} {q : ℝ} (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet (fun i : Fin n ↦ A i) P)
    (hq : ∀ i < n, P.real (A i) = q) :
    P.real (runEvent A n r)ᶜ ≤ (1 - q ^ r) ^ (n / r) := by
  have := hind.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  set J := n / r
  have hJ : J * r ≤ n := Nat.div_mul_le_self n r
  -- the blocks before block `J'` and block `J'` itself are independent
  have key : ∀ J' ≤ J, P.real (⋂ j ∈ range J', (allLost A r j)ᶜ) = (1 - q ^ r) ^ J' := by
    intro J' hJ'
    induction J' with
    | zero => simp
    | succ J' ih =>
      have hJ'n : J' * r + r ≤ n := by
        have := Nat.mul_le_mul_right r hJ'; rw [Nat.succ_mul] at this; omega
      have hS : Disjoint {j : Fin n | (j : ℕ) < J' * r}
          {j : Fin n | J' * r ≤ (j : ℕ) ∧ (j : ℕ) < J' * r + r} := by
        rw [Set.disjoint_left]; intro j h1 h2; simp only [Set.mem_ofPred_eq] at h1 h2; omega
      have hI := hind.indep_generateFrom_of_disjoint (s := fun i : Fin n ↦ A i)
        (fun j ↦ hA j) _ _ hS
      have gen : ∀ (T : Set (Fin n)) (i : ℕ) (hi : i < n), (⟨i, hi⟩ : Fin n) ∈ T →
          MeasurableSet[MeasurableSpace.generateFrom {t | ∃ m ∈ T, A m = t}] (A i) :=
        fun T i hi hT ↦ MeasurableSpace.measurableSet_generateFrom ⟨⟨i, hi⟩, hT, rfl⟩
      have m1 : MeasurableSet[MeasurableSpace.generateFrom
          {t | ∃ m ∈ {j : Fin n | (j : ℕ) < J' * r}, A m = t}]
          (⋂ j ∈ range J', (allLost A r j)ᶜ) := by
        refine Finset.measurableSet_biInter _ fun j hj ↦ (Finset.measurableSet_biInter _
          fun i hi ↦ ?_).compl
        have hj := mem_range.mp hj; have hi := mem_Ico.mp hi
        have : j * r + r ≤ J' * r := by
          have := Nat.mul_le_mul_right r (Nat.succ_le_of_lt hj); rw [Nat.succ_mul] at this
          exact this
        exact gen _ i (by omega) (by simp only [Set.mem_ofPred_eq]; omega)
      have m2 : MeasurableSet[MeasurableSpace.generateFrom
          {t | ∃ m ∈ {j : Fin n | J' * r ≤ (j : ℕ) ∧ (j : ℕ) < J' * r + r}, A m = t}]
          (allLost A r J')ᶜ := by
        refine (Finset.measurableSet_biInter _ fun i hi ↦ ?_).compl
        have hi := mem_Ico.mp hi
        exact gen _ i (by omega) (by simp only [Set.mem_ofPred_eq]; omega)
      rw [range_add_one, Finset.set_biInter_insert, Set.inter_comm, measureReal_def,
        (Indep_iff _ _ P).mp hI _ _ m1 m2, ENNReal.toReal_mul, ← measureReal_def,
        ← measureReal_def, ih (by omega), measureReal_compl (measurableSet_allLost hA r J'),
        probReal_univ, allLost, measureReal_iInter_Ico hind hq hJ'n, pow_succ]
  refine (measureReal_mono ?_).trans (key J le_rfl).le
  intro ω hω
  simp only [Set.mem_iInter, mem_range, Set.mem_compl_iff]
  intro j hj hall
  apply hω
  refine ⟨j * r, ?_, fun i hi ↦ ?_⟩
  · have := Nat.mul_le_mul_right r (Nat.succ_le_of_lt hj); rw [Nat.succ_mul] at this; omega
  · exact Set.mem_iInter₂.mp hall i hi

end ClassicalLean.Probability.LongestRun
