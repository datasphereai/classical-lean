/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Complex.Exponential

/-!
# Streaks under chance

In `n` independent trials that each lose with chance `q`, how likely is a streak of `r` losses in
a row? Order LEAN-26, item 69 of the plan.

* `measureReal_exists_run_le`: the chance of some run of at least `r` losses is at most
  `(n − r + 1) q^r` (a union bound over the `n − r + 1` places a run can start).
* `measureReal_no_run_le`: the chance of no such run is at most `(1 − q^r)^⌊n / r⌋` (the `⌊n / r⌋`
  disjoint blocks of `r` trials are independent, and none of them may be all losses).
* `measureReal_no_run_le_exp` (order LEAN-29, item 91): the same chance is at most
  `exp (−⌊n / r⌋ q^r)`, from the second bound and `1 − x ≤ e^(−x)`.

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
* The second theorem assumes each trial's event `A i`, `i < n`, measurable, and the bound needs it
  (order LEAN-28, item 87): without it, one trial on a two-point space where only `∅` and the whole
  space are measurable, with the point mass at `true` and `A 0 = {true}`, is independent (one event
  always is, under a probability measure). Lean's `P.real` of a set the σ-algebra cannot measure is
  its outer measure: for `{true}` it is `1`, so the trial loses with chance `q = 1`, and for
  `{false}` it is also `1`, so the chance of no run of `1` loss is `1 > (1 − 1)^1 = 0` (the second
  `example` at the end of this file). Both outer measures matter: read as inner measures (`0` each)
  the bound would hold. The trials from `n` on need not be measurable (they play no part), so the
  hypothesis is stated for `i < n` only; this makes the theorem wider than order LEAN-26's, whose
  statement (with `∀ i`) follows from it.
* each trial losing with chance `q` (cold review r87; the third `example` at the end of this file
  for the second theorem, the fourth for the first): for the second theorem,
  `A i = ∅` for every `i` (measurable and independent) with `q = 1` stated, `n = r = 1`: no run has
  chance `1 > (1 − 1)^1 = 0`; for the first, `A i` the whole space with `q = 0` stated, `n = r = 1`:
  a run has chance `1 > 1 · 0^1 = 0`.
* The hypotheses of the second theorem hold together: the first `example` at the end of this file
  (`Bool`, the point mass at `true`, every `A i = {true}`, `n = r = 1`, `q = 1`).

Measured in the same checks (exact dynamic programming, not proved in Lean): both bounds hold for
`q ∈ {1/2, 1/3, 3/5, 9/10}`, `n ≤ 40`, every `r ≤ n + 3` (line R1); for fair trials the mean
longest run in `100` trials is `5.99` and a run of `7` or more in `200` trials has chance `0.544`
(line R2, the plan's numbers). For fair trials the first bound is small once `2^r` is large
against `n`, that is `r` past about `log₂ n`. The second bound gives the other side:
`measureReal_no_run_le_exp` (order LEAN-29) turns it into `exp (−⌊n / r⌋ q^r)`, so for fair trials
(`q = 1/2`) no run of `r` has chance at most `exp (−⌊n / r⌋ / 2^r)`, which is small once `n / r` is
large compared with `2^r`, that is once `r` is below about `log₂ n − log₂ log₂ n` (this reading of
the theorem at `q = 1/2` is by hand). So for fair trials the longest run is near `log₂ n`, and a
streak counts as evidence only past these numbers.
The first bound is exact when `n = r` (line R7).

For `measureReal_no_run_le_exp` (order LEAN-29's exact checks, lane `lean/LEAN-29-checks.py`, by
the label of each line): on a grid of `n ≤ 10`, `r ≤ 4` and six values of `q`, the exact chance,
`(1 − q^r)^⌊n / r⌋` and the exponential bound come in that order in all 330 cells (`91.grid`). Each
hypothesis is needed:

* measurability (`91.drop.hA`, by hand, order LEAN-28's case for the second bound, the second
  `example` at the end of this file): on `Bool` with only `∅` and the whole space measurable, the
  point mass at `true`, `A 0 = {true}`, `n = r = 1`, `q = 1`, Lean's chance of no run (an outer
  measure) is `1`, against `exp (−1) < 0.37`.
* independence (`91.drop.hind`): every trial the same event of chance `q`; the first failing cell is
  `(n, r, q) = (2, 1, 1/10)`: chance `9/10`, against `exp (−1/5) < 0.82`.
* each trial losing with chance `q` (`91.drop.hq`): every event empty while `q` is stated; the first
  failing cell is `(1, 1, 1/10)`: chance `1`, against `exp (−1/10) < 1`.

Lean's junk values here decide nothing but are named: `n / r` is division in `ℕ`, so `n / 0 = 0`
and the bound is then `exp 0 = 1`; and `q ^ 0 = 1`. The hypotheses hold together: the last
`example` at the end of this file (two fair flips, `n = 2`, runs of `r = 1`).

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

/-- A block of losses is an event when the block's own trials are (order LEAN-28: only the block's
trials, `j r ≤ i < j r + r`, need to be measurable). -/
lemma measurableSet_allLost {A : ℕ → Set Ω} {r j : ℕ}
    (hA : ∀ i ∈ Ico (j * r) (j * r + r), MeasurableSet (A i)) : MeasurableSet (allLost A r j) :=
  Finset.measurableSet_biInter _ hA

/-- **No streak is unlikely when `(1 − q^r)^⌊n / r⌋` is small.** In `n` independent trials that
each lose with chance `q`, the chance of no run of `r` losses is at most `(1 − q^r)^⌊n / r⌋`. The
trials' events must be measurable: without that the bound fails (the second `example` at the end
of this file; the first shows the hypotheses hold together). -/
theorem measureReal_no_run_le {P : Measure Ω} {A : ℕ → Set Ω}
    {n r : ℕ} {q : ℝ} (hA : ∀ i < n, MeasurableSet (A i))
    (hind : iIndepSet (fun i : Fin n ↦ A i) P) (hq : ∀ i < n, P.real (A i) = q) :
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
        (fun j ↦ hA j j.isLt) _ _ hS
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
        ← measureReal_def, ih (by omega),
        measureReal_compl (measurableSet_allLost (r := r) (j := J') fun i hi ↦
          hA i (by have := mem_Ico.mp hi; omega)),
        probReal_univ, allLost, measureReal_iInter_Ico hind hq hJ'n, pow_succ]
  refine (measureReal_mono ?_).trans (key J le_rfl).le
  intro ω hω
  simp only [Set.mem_iInter, mem_range, Set.mem_compl_iff]
  intro j hj hall
  apply hω
  refine ⟨j * r, ?_, fun i hi ↦ ?_⟩
  · have := Nat.mul_le_mul_right r (Nat.succ_le_of_lt hj); rw [Nat.succ_mul] at this; omega
  · exact Set.mem_iInter₂.mp hall i hi

/-- **No streak is unlikely when `exp (−⌊n / r⌋ q^r)` is small** (order LEAN-29, item 91 of
MATH-PLAN-library-2, the lower side of item 69's `log₂ n` reading). In `n` independent trials that
each lose with chance `q`, the chance of no run of `r` losses is at most `exp (−⌊n / r⌋ q^r)`:
`measureReal_no_run_le` and `1 − x ≤ e^(−x)`. For fair trials (`q = 1/2`) this reads: no run of `r`
losses has chance at most `exp (−⌊n / r⌋ / 2^r)`, so a run of `r` losses is all but certain once
`n / r` is large compared with `2^r`. When `n / r = 0` (no whole block, or Lean's `n / 0 = 0`) the
bound is `1`. -/
theorem measureReal_no_run_le_exp {P : Measure Ω} {A : ℕ → Set Ω}
    {n r : ℕ} {q : ℝ} (hA : ∀ i < n, MeasurableSet (A i))
    (hind : iIndepSet (fun i : Fin n ↦ A i) P) (hq : ∀ i < n, P.real (A i) = q) :
    P.real (runEvent A n r)ᶜ ≤ Real.exp (-(((n / r : ℕ) : ℝ) * q ^ r)) := by
  have := hind.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos (n / r) with hm | hm
  · rw [hm, Nat.cast_zero, zero_mul, neg_zero, Real.exp_zero]
    exact measureReal_le_one
  -- at least one block: `1 ≤ r ≤ n`, so trial `0` exists and `q` is a chance
  have hrn : r ≤ n := by
    by_contra h
    rw [Nat.div_eq_of_lt (Nat.lt_of_not_le h)] at hm
    exact lt_irrefl 0 hm
  have hr : 0 < r := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hm
  have hq0 : P.real (A 0) = q := hq 0 (by omega)
  have hq1 : q ^ r ≤ 1 :=
    pow_le_one₀ (hq0 ▸ measureReal_nonneg) (hq0 ▸ measureReal_le_one)
  calc P.real (runEvent A n r)ᶜ ≤ (1 - q ^ r) ^ (n / r) := measureReal_no_run_le hA hind hq
    _ ≤ Real.exp (-(q ^ r)) ^ (n / r) :=
        pow_le_pow_left₀ (sub_nonneg.mpr hq1) (Real.one_sub_le_exp_neg _) _
    _ = Real.exp (-(((n / r : ℕ) : ℝ) * q ^ r)) := by
        rw [← Real.exp_nat_mul]
        ring_nf

/-- The hypotheses of `measureReal_no_run_le` hold together (order LEAN-28, item 87, cold review
r87): `Bool` with all its subsets measurable, the point mass at `true`, every trial's event
`{true}`, `n = r = 1`, `q = 1`. -/
example : ∃ (P : Measure Bool) (A : ℕ → Set Bool), (∀ i < 1, MeasurableSet (A i)) ∧
    iIndepSet (fun i : Fin 1 ↦ A i) P ∧ (∀ i < 1, P.real (A i) = 1) := by
  refine ⟨Measure.dirac true, fun _ ↦ {true}, fun _ _ ↦ measurableSet_singleton _, ?_,
    fun i _ ↦ ?_⟩
  · change iIndep (fun i : Fin 1 ↦ MeasurableSpace.generateFrom {({true} : Set Bool)}) _
    rw [iIndep_iff]
    intro s f _
    rcases Finset.eq_empty_or_nonempty s with rfl | ⟨i₀, hi₀⟩
    · simp
    · have hs : s = {i₀} := by
        ext i
        simp only [Finset.mem_singleton, Subsingleton.elim i i₀, hi₀]
      subst hs
      simp
  · simp [measureReal_def, Measure.dirac_apply_of_mem (Set.mem_singleton true)]

/-- **Why `measureReal_no_run_le` keeps its measurability hypothesis** (order LEAN-28, item 87). On
`Bool` with the σ-algebra `⊥` (only `∅` and `univ` measurable) and the point mass at `true`, the
single event `A 0 = {true}` is independent (one trial) and loses with chance `1` (Lean's outer
measure of `{true}`), yet the chance of no run of one loss, Lean's outer measure of `{false}`, is
`1`, above the bound `(1 − 1^1)^1 = 0`. -/
example : ∃ (P : @Measure Bool ⊥) (A : ℕ → Set Bool),
    iIndepSet (fun i : Fin 1 ↦ A i) P ∧ (∀ i < 1, P.real (A i) = 1) ∧
      (1 - (1 : ℝ) ^ 1) ^ (1 / 1) < P.real (runEvent A 1 1)ᶜ := by
  let _ : MeasurableSpace Bool := ⊥
  refine ⟨Measure.dirac true, fun _ ↦ {true}, ?_, fun i _ ↦ ?_, ?_⟩
  · change iIndep (fun i : Fin 1 ↦ MeasurableSpace.generateFrom {({true} : Set Bool)}) _
    rw [iIndep_iff]
    intro s f _
    rcases Finset.eq_empty_or_nonempty s with rfl | ⟨i₀, hi₀⟩
    · simp
    · have hs : s = {i₀} := by
        ext i
        simp only [Finset.mem_singleton, Subsingleton.elim i i₀, hi₀]
      subst hs
      simp
  · simp [measureReal_def, Measure.dirac_apply_of_mem (Set.mem_singleton true)]
  · have hrun : runEvent (fun _ ↦ ({true} : Set Bool)) 1 1 = {true} := by
      ext ω
      simp only [runEvent, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨s, hs, h⟩
        exact h s (mem_Ico.mpr ⟨le_rfl, Nat.lt_succ_self s⟩)
      · intro h
        exact ⟨0, le_rfl, fun i _ ↦ h⟩
    rw [hrun]
    have htop : ∀ t : Set Bool, MeasurableSet t → ({true}ᶜ : Set Bool) ⊆ t → t = Set.univ := by
      intro t ht hsub
      rcases MeasurableSpace.measurableSet_bot_iff.mp ht with rfl | rfl
      · exact absurd (hsub (show false ∈ ({true}ᶜ : Set Bool) by simp)) (by simp)
      · rfl
    have h1 : (Measure.dirac true : Measure Bool) ({true}ᶜ : Set Bool) = 1 := by
      rw [← measure_toMeasurable,
        htop _ (measurableSet_toMeasurable _ _) (subset_toMeasurable _ _)]
      simp
    rw [measureReal_def, h1]
    norm_num

/-- **Why `measureReal_no_run_le` needs each trial to lose with chance `q`** (cold review r87): one
trial on `Bool` with the point mass at `true`, `A 0 = ∅` (measurable, and independent, as one event
is under a probability measure), and `q = 1` stated, `n = r = 1`: no run has chance `1`, above the
bound `(1 − 1^1)^1 = 0`. -/
example : ∃ (P : Measure Bool) (A : ℕ → Set Bool), (∀ i < 1, MeasurableSet (A i)) ∧
    iIndepSet (fun i : Fin 1 ↦ A i) P ∧
      (1 - (1 : ℝ) ^ 1) ^ (1 / 1) < P.real (runEvent A 1 1)ᶜ := by
  refine ⟨Measure.dirac true, fun _ ↦ ∅, fun _ _ ↦ MeasurableSet.empty, ?_, ?_⟩
  · change iIndep (fun i : Fin 1 ↦ MeasurableSpace.generateFrom {(∅ : Set Bool)}) _
    rw [iIndep_iff]
    intro s f _
    rcases Finset.eq_empty_or_nonempty s with rfl | ⟨i₀, hi₀⟩
    · simp
    · have hs : s = {i₀} := by
        ext i
        simp only [Finset.mem_singleton, Subsingleton.elim i i₀, hi₀]
      subst hs
      simp
  · have hrun : runEvent (fun _ ↦ (∅ : Set Bool)) 1 1 = ∅ := by
      ext ω
      simp only [runEvent, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists,
        not_and]
      intro s hs h
      exact h s (mem_Ico.mpr ⟨le_rfl, Nat.lt_succ_self s⟩)
    rw [hrun, Set.compl_empty, probReal_univ]
    norm_num

/-- **Why `measureReal_exists_run_le` needs each trial to lose with chance `q`** (cold review r87):
one trial on `Bool` with the point mass at `true`, `A 0` the whole space (independent, as one event
is under a probability measure), and `q = 0` stated, `n = r = 1`: a run has chance `1`, above the
bound `1 · 0^1 = 0`. -/
example : ∃ (P : Measure Bool) (A : ℕ → Set Bool), iIndepSet (fun i : Fin 1 ↦ A i) P ∧
    ((1 + 1 - 1 : ℕ) : ℝ) * (0 : ℝ) ^ 1 < P.real (runEvent A 1 1) := by
  refine ⟨Measure.dirac true, fun _ ↦ Set.univ, ?_, ?_⟩
  · change iIndep (fun i : Fin 1 ↦ MeasurableSpace.generateFrom {(Set.univ : Set Bool)}) _
    rw [iIndep_iff]
    intro s f _
    rcases Finset.eq_empty_or_nonempty s with rfl | ⟨i₀, hi₀⟩
    · simp
    · have hs : s = {i₀} := by
        ext i
        simp only [Finset.mem_singleton, Subsingleton.elim i i₀, hi₀]
      subst hs
      simp
  · have hrun : runEvent (fun _ ↦ (Set.univ : Set Bool)) 1 1 = Set.univ :=
      Set.eq_univ_of_forall fun _ ↦ ⟨0, le_rfl, fun _ _ ↦ Set.mem_univ _⟩
    rw [hrun, probReal_univ]
    norm_num

end ClassicalLean.Probability.LongestRun

open MeasureTheory ProbabilityTheory in
open scoped ENNReal in
/-- The hypotheses of `measureReal_exists_run_le` hold together: two fair coin flips, the uniform
probability `(1/4) · count` on the four sequences `Fin 2 → Bool`; the events `A i`, flip `i` comes
up heads (a loss), for `i < 2`, which are independent (the chance of both is `1/4 = 1/2 · 1/2`);
each has chance `q = 1/2`; `n = 2` trials and runs of `r = 2` losses. -/
example := ClassicalLean.Probability.LongestRun.measureReal_exists_run_le (Ω := Fin 2 → Bool)
  (P := (4⁻¹ : ℝ≥0∞) • Measure.count)
  (A := fun i ↦ {ω | ∃ h : i < 2, ω ⟨i, h⟩ = true}) (n := 2) (r := 2) (q := 1 / 2)
  (by
    have c0 : Measure.count {ω : Fin 2 → Bool | ω 0 = true} = 2 := by
      rw [Measure.count_apply_finite _ (Set.toFinite _)]
      simp only [Set.Finite.toFinset_ofPred]
      norm_cast
    have c1 : Measure.count {ω : Fin 2 → Bool | ω 1 = true} = 2 := by
      rw [Measure.count_apply_finite _ (Set.toFinite _)]
      simp only [Set.Finite.toFinset_ofPred]
      norm_cast
    have c01 : Measure.count ({ω : Fin 2 → Bool | ω 0 = true} ∩ {ω | ω 1 = true}) = 1 := by
      rw [Measure.count_apply_finite _ (Set.toFinite _)]
      simp only [Set.toFinite_toFinset, Set.toFinset_inter, Set.toFinset_ofPred]
      norm_cast
    have h2 : (4⁻¹ : ℝ≥0∞) * 2 = 2⁻¹ := by
      rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp), mul_assoc,
        ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]
    have h4 : (4⁻¹ : ℝ≥0∞) = 2⁻¹ * 2⁻¹ := by
      rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp)]
    rw [iIndepSet_iff_meas_biInter fun _ ↦ MeasurableSet.of_discrete]
    intro s
    have e : ∀ (S : Set (Fin 2 → Bool)) (j : Fin 2), S = {ω | ω j = true} →
        Measure.count {ω : Fin 2 → Bool | ω j = true} = 2 → (4⁻¹ : ℝ≥0∞) * Measure.count S = 2⁻¹ :=
      fun S j hS hc ↦ by rw [hS, hc, h2]
    fin_cases s
    · simp only [Multiset.coe_nil, mk_zero, notMem_empty, Fin.eta, Order.lt_two_iff, exists_prop,
        isEmpty_Prop, not_false_eq_true, Set.iInter_of_empty, Set.iInter_univ, Measure.smul_apply,
        Measure.count_univ, ENat.card_eq_coe_fintype_card, Fintype.card_pi, Fintype.card_bool,
        prod_const, card_univ, Fintype.card_fin, Nat.reducePow, Nat.cast_ofNat,
        ENat.toENNReal_ofNat, smul_eq_mul, prod_empty]
      exact ENNReal.inv_mul_cancel (by simp) (by simp)
    · simp only [Fin.zero_eta, Fin.isValue, Multiset.coe_singleton, mem_mk, Multiset.mem_singleton,
        Fin.eta, Order.lt_two_iff, exists_prop, Measure.smul_apply, smul_eq_mul, prod_mk,
        Multiset.map_singleton, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_le, true_and,
        Multiset.prod_singleton]
      rw [e _ 0 (by ext ω; simp [Finset.mem_def]) c0, ← h2, c0]
    · simp only [Fin.mk_one, Fin.isValue, Multiset.coe_singleton, mem_mk, Multiset.mem_singleton,
        Fin.eta, Order.lt_two_iff, exists_prop, Measure.smul_apply, smul_eq_mul, prod_mk,
        Multiset.map_singleton, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Std.le_refl, true_and,
        Multiset.prod_singleton]
      rw [e _ 1 (by ext ω; simp [Finset.mem_def]) c1, ← h2, c1]
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, mem_mk, Multiset.mem_coe, List.mem_cons,
        List.not_mem_nil, or_false, Fin.eta, Order.lt_two_iff, exists_prop,
        Set.iInter_iInter_eq_or_left, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_le, true_and,
        Set.iInter_iInter_eq_left, Nat.mod_succ, Std.le_refl, Measure.smul_apply, smul_eq_mul,
        prod_mk, Multiset.map_coe, List.map_cons, List.map_nil, Multiset.prod_coe, List.prod_cons,
        List.prod_nil, mul_one]
      rw [c01, c0, c1, h2, mul_one, h4])
  (fun i hi ↦ by
    have c0 : Measure.count {ω : Fin 2 → Bool | ω 0 = true} = 2 := by
      rw [Measure.count_apply_finite _ (Set.toFinite _)]
      simp only [Set.Finite.toFinset_ofPred]
      norm_cast
    have c1 : Measure.count {ω : Fin 2 → Bool | ω 1 = true} = 2 := by
      rw [Measure.count_apply_finite _ (Set.toFinite _)]
      simp only [Set.Finite.toFinset_ofPred]
      norm_cast
    have h2 : (4⁻¹ : ℝ≥0∞) * 2 = 2⁻¹ := by
      rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp), mul_assoc,
        ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]
    rcases i with _ | _ | i
    · simp [Measure.real, c0, h2]
    · simp [Measure.real, c1, h2]
    · omega)

open MeasureTheory ProbabilityTheory in
open scoped ENNReal in
/-- The hypotheses of `measureReal_no_run_le` hold together: two fair coin flips, the uniform
probability `(1/4) · count` on the four sequences `Fin 2 → Bool`; the events `A i`, flip `i` comes
up heads (a loss), for `i < 2`, which are independent (the chance of both is `1/4 = 1/2 · 1/2`);
each is measurable (every set of the four sequences is) and has chance `q = 1/2`; `n = 2` trials and
runs of `r = 2` losses. -/
example := ClassicalLean.Probability.LongestRun.measureReal_no_run_le (Ω := Fin 2 → Bool)
  (P := (4⁻¹ : ℝ≥0∞) • Measure.count)
  (A := fun i ↦ {ω | ∃ h : i < 2, ω ⟨i, h⟩ = true}) (n := 2) (r := 2) (q := 1 / 2)
  (fun _ _ ↦ MeasurableSet.of_discrete)
  (by
    have c0 : Measure.count {ω : Fin 2 → Bool | ω 0 = true} = 2 := by
      rw [Measure.count_apply_finite _ (Set.toFinite _)]
      simp only [Set.Finite.toFinset_ofPred]
      norm_cast
    have c1 : Measure.count {ω : Fin 2 → Bool | ω 1 = true} = 2 := by
      rw [Measure.count_apply_finite _ (Set.toFinite _)]
      simp only [Set.Finite.toFinset_ofPred]
      norm_cast
    have c01 : Measure.count ({ω : Fin 2 → Bool | ω 0 = true} ∩ {ω | ω 1 = true}) = 1 := by
      rw [Measure.count_apply_finite _ (Set.toFinite _)]
      simp only [Set.toFinite_toFinset, Set.toFinset_inter, Set.toFinset_ofPred]
      norm_cast
    have h2 : (4⁻¹ : ℝ≥0∞) * 2 = 2⁻¹ := by
      rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp), mul_assoc,
        ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]
    have h4 : (4⁻¹ : ℝ≥0∞) = 2⁻¹ * 2⁻¹ := by
      rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp)]
    rw [iIndepSet_iff_meas_biInter fun _ ↦ MeasurableSet.of_discrete]
    intro s
    have e : ∀ (S : Set (Fin 2 → Bool)) (j : Fin 2), S = {ω | ω j = true} →
        Measure.count {ω : Fin 2 → Bool | ω j = true} = 2 → (4⁻¹ : ℝ≥0∞) * Measure.count S = 2⁻¹ :=
      fun S j hS hc ↦ by rw [hS, hc, h2]
    fin_cases s
    · simp only [Multiset.coe_nil, mk_zero, notMem_empty, Fin.eta, Order.lt_two_iff, exists_prop,
        isEmpty_Prop, not_false_eq_true, Set.iInter_of_empty, Set.iInter_univ, Measure.smul_apply,
        Measure.count_univ, ENat.card_eq_coe_fintype_card, Fintype.card_pi, Fintype.card_bool,
        prod_const, card_univ, Fintype.card_fin, Nat.reducePow, Nat.cast_ofNat,
        ENat.toENNReal_ofNat, smul_eq_mul, prod_empty]
      exact ENNReal.inv_mul_cancel (by simp) (by simp)
    · simp only [Fin.zero_eta, Fin.isValue, Multiset.coe_singleton, mem_mk, Multiset.mem_singleton,
        Fin.eta, Order.lt_two_iff, exists_prop, Measure.smul_apply, smul_eq_mul, prod_mk,
        Multiset.map_singleton, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_le, true_and,
        Multiset.prod_singleton]
      rw [e _ 0 (by ext ω; simp [Finset.mem_def]) c0, ← h2, c0]
    · simp only [Fin.mk_one, Fin.isValue, Multiset.coe_singleton, mem_mk, Multiset.mem_singleton,
        Fin.eta, Order.lt_two_iff, exists_prop, Measure.smul_apply, smul_eq_mul, prod_mk,
        Multiset.map_singleton, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Std.le_refl, true_and,
        Multiset.prod_singleton]
      rw [e _ 1 (by ext ω; simp [Finset.mem_def]) c1, ← h2, c1]
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, mem_mk, Multiset.mem_coe, List.mem_cons,
        List.not_mem_nil, or_false, Fin.eta, Order.lt_two_iff, exists_prop,
        Set.iInter_iInter_eq_or_left, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_le, true_and,
        Set.iInter_iInter_eq_left, Nat.mod_succ, Std.le_refl, Measure.smul_apply, smul_eq_mul,
        prod_mk, Multiset.map_coe, List.map_cons, List.map_nil, Multiset.prod_coe, List.prod_cons,
        List.prod_nil, mul_one]
      rw [c01, c0, c1, h2, mul_one, h4])
  (fun i hi ↦ by
    have c0 : Measure.count {ω : Fin 2 → Bool | ω 0 = true} = 2 := by
      rw [Measure.count_apply_finite _ (Set.toFinite _)]
      simp only [Set.Finite.toFinset_ofPred]
      norm_cast
    have c1 : Measure.count {ω : Fin 2 → Bool | ω 1 = true} = 2 := by
      rw [Measure.count_apply_finite _ (Set.toFinite _)]
      simp only [Set.Finite.toFinset_ofPred]
      norm_cast
    have h2 : (4⁻¹ : ℝ≥0∞) * 2 = 2⁻¹ := by
      rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp), mul_assoc,
        ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]
    rcases i with _ | _ | i
    · simp [Measure.real, c0, h2]
    · simp [Measure.real, c1, h2]
    · omega)

open MeasureTheory ProbabilityTheory in
open scoped ENNReal in
/-- The hypotheses of `measureReal_no_run_le_exp` hold together: two fair coin flips, the uniform
probability `(1/4) · count` on the four sequences `Fin 2 → Bool`; the events `A i`, flip `i` comes
up heads (a loss), for `i < 2`, which are independent (the chance of both is `1/4 = 1/2 · 1/2`);
each is measurable (every set of the four sequences is) and has chance `q = 1/2`; `n = 2` trials and
runs of `r = 1` loss, so that `n / r = 2` blocks count, not one. -/
example := ClassicalLean.Probability.LongestRun.measureReal_no_run_le_exp (Ω := Fin 2 → Bool)
  (P := (4⁻¹ : ℝ≥0∞) • Measure.count)
  (A := fun i ↦ {ω | ∃ h : i < 2, ω ⟨i, h⟩ = true}) (n := 2) (r := 1) (q := 1 / 2)
  (fun _ _ ↦ MeasurableSet.of_discrete)
  (by
    have c0 : Measure.count {ω : Fin 2 → Bool | ω 0 = true} = 2 := by
      rw [Measure.count_apply_finite _ (Set.toFinite _)]
      simp only [Set.Finite.toFinset_ofPred]
      norm_cast
    have c1 : Measure.count {ω : Fin 2 → Bool | ω 1 = true} = 2 := by
      rw [Measure.count_apply_finite _ (Set.toFinite _)]
      simp only [Set.Finite.toFinset_ofPred]
      norm_cast
    have c01 : Measure.count ({ω : Fin 2 → Bool | ω 0 = true} ∩ {ω | ω 1 = true}) = 1 := by
      rw [Measure.count_apply_finite _ (Set.toFinite _)]
      simp only [Set.toFinite_toFinset, Set.toFinset_inter, Set.toFinset_ofPred]
      norm_cast
    have h2 : (4⁻¹ : ℝ≥0∞) * 2 = 2⁻¹ := by
      rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp), mul_assoc,
        ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]
    have h4 : (4⁻¹ : ℝ≥0∞) = 2⁻¹ * 2⁻¹ := by
      rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp)]
    rw [iIndepSet_iff_meas_biInter fun _ ↦ MeasurableSet.of_discrete]
    intro s
    have e : ∀ (S : Set (Fin 2 → Bool)) (j : Fin 2), S = {ω | ω j = true} →
        Measure.count {ω : Fin 2 → Bool | ω j = true} = 2 → (4⁻¹ : ℝ≥0∞) * Measure.count S = 2⁻¹ :=
      fun S j hS hc ↦ by rw [hS, hc, h2]
    fin_cases s
    · simp only [Multiset.coe_nil, mk_zero, notMem_empty, Fin.eta, Order.lt_two_iff, exists_prop,
        isEmpty_Prop, not_false_eq_true, Set.iInter_of_empty, Set.iInter_univ, Measure.smul_apply,
        Measure.count_univ, ENat.card_eq_coe_fintype_card, Fintype.card_pi, Fintype.card_bool,
        prod_const, card_univ, Fintype.card_fin, Nat.reducePow, Nat.cast_ofNat,
        ENat.toENNReal_ofNat, smul_eq_mul, prod_empty]
      exact ENNReal.inv_mul_cancel (by simp) (by simp)
    · simp only [Fin.zero_eta, Fin.isValue, Multiset.coe_singleton, mem_mk, Multiset.mem_singleton,
        Fin.eta, Order.lt_two_iff, exists_prop, Measure.smul_apply, smul_eq_mul, prod_mk,
        Multiset.map_singleton, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_le, true_and,
        Multiset.prod_singleton]
      rw [e _ 0 (by ext ω; simp [Finset.mem_def]) c0, ← h2, c0]
    · simp only [Fin.mk_one, Fin.isValue, Multiset.coe_singleton, mem_mk, Multiset.mem_singleton,
        Fin.eta, Order.lt_two_iff, exists_prop, Measure.smul_apply, smul_eq_mul, prod_mk,
        Multiset.map_singleton, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Std.le_refl, true_and,
        Multiset.prod_singleton]
      rw [e _ 1 (by ext ω; simp [Finset.mem_def]) c1, ← h2, c1]
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, mem_mk, Multiset.mem_coe, List.mem_cons,
        List.not_mem_nil, or_false, Fin.eta, Order.lt_two_iff, exists_prop,
        Set.iInter_iInter_eq_or_left, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_le, true_and,
        Set.iInter_iInter_eq_left, Nat.mod_succ, Std.le_refl, Measure.smul_apply, smul_eq_mul,
        prod_mk, Multiset.map_coe, List.map_cons, List.map_nil, Multiset.prod_coe, List.prod_cons,
        List.prod_nil, mul_one]
      rw [c01, c0, c1, h2, mul_one, h4])
  (fun i hi ↦ by
    have c0 : Measure.count {ω : Fin 2 → Bool | ω 0 = true} = 2 := by
      rw [Measure.count_apply_finite _ (Set.toFinite _)]
      simp only [Set.Finite.toFinset_ofPred]
      norm_cast
    have c1 : Measure.count {ω : Fin 2 → Bool | ω 1 = true} = 2 := by
      rw [Measure.count_apply_finite _ (Set.toFinite _)]
      simp only [Set.Finite.toFinset_ofPred]
      norm_cast
    have h2 : (4⁻¹ : ℝ≥0∞) * 2 = 2⁻¹ := by
      rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp), mul_assoc,
        ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]
    rcases i with _ | _ | i
    · simp [Measure.real, c0, h2]
    · simp [Measure.real, c1, h2]
    · omega)
