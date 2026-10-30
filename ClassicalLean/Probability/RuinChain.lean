/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Probability.GamblersRuin
import ClassicalLean.Probability.FiniteChain

/-!
# Gambler's ruin by first-step analysis

The fair `±1` walk from `0`, stopped on leaving `(-b, a)`, has a chain on the `a + b + 1` positions
`-b, …, a`: `ruinChain a b`, a matrix indexed by `Fin (a + b + 1)`, index `i` standing for position
`i - b`. From an inside index it moves one down or one up with chance `1/2` each; the two end
indices `0` and `a + b` (positions `-b` and `a`) stay where they are. The target is the set of the
two ends, `{0, Fin.last (a + b)}`. Order CLOUD-MATH-6, bridge 165 of
`MATH-PLAN-library-2-bridges-2.md`.

* `ruinChain_meanHitting_iff` — the first-step equations of the mean time to reach the ends,
  `g = 0` at the ends and `g i = 1 + ∑ j, ruinChain a b i j * g j` inside, have exactly one
  solution, `g i = (a + b - i) i` in index terms (at position `x = i - b`, `(a - x)(x + b)`). The
  chain has rows summing to `1`, entries at least `0`, and an end is reachable from every inside
  index (walking down `i` steps, `(P ^ i) i 0 ≥ (1/2) ^ i > 0`), so `FiniteChain.meanHitting_eq`
  (item 148) says the equations have exactly one solution, its series `h`; `(a + b - i) i` solves
  them.
* `sum_ruinChain`, `ruinChain_nonneg`, `exists_pow_ruinChain_pos` — `meanHitting_eq`'s three
  hypotheses for `ruinChain a b` and the two ends (added after the cold review of the statements,
  so that the row's form `∫ τ dμ = h b` follows from stated theorems).
* `integral_exitTime_eq_meanHitting` — for the fair walk (the hypotheses of
  `GamblersRuin.integral_exitTime_eq`), every solution `g` of the equations gives, at the start
  index `b` (position `0`), the walk's mean exit time: `∫ τ dμ = g b`. Both are `a b`.

Both theorems hold for all `a b : ℕ`: if `a = 0` or `b = 0` the start is an end and both sides are
`0`, and at `a + b ≤ 1` every index is an end, so the reachability of an end asks nothing.

The witness at the end of the file is `GamblersRuin`'s fair walk (independent fair coins under
Mathlib's `Measure.infinitePi`) with `a = 2`, `b = 3` and `g i = (5 - i) i`.
-/

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open ClassicalLean.Probability.GamblersRuin

namespace ClassicalLean.Probability.RuinChain

/-- The chain of the fair `±1` walk stopped on leaving `(-b, a)`, on the `a + b + 1` positions
`-b, …, a`, index `i : Fin (a + b + 1)` standing for position `i - b`. From an end index (`0`,
position `-b`, or `a + b`, position `a`) it stays where it is, with chance `1`; from an inside index
`i` it moves to `i - 1` or to `i + 1`, with chance `1/2` each. -/
noncomputable def ruinChain (a b : ℕ) : Matrix (Fin (a + b + 1)) (Fin (a + b + 1)) ℝ :=
  Matrix.of fun i j ↦
    if (i : ℕ) = 0 ∨ (i : ℕ) = a + b then (if j = i then 1 else 0)
    else if (j : ℕ) + 1 = i ∨ (j : ℕ) = (i : ℕ) + 1 then 1 / 2 else 0

/-- At an inside index, the chain's row is `1/2` at `i - 1` and `1/2` at `i + 1`. -/
private theorem ruinChain_apply_inside {a b : ℕ} {i : Fin (a + b + 1)} (h0 : (i : ℕ) ≠ 0)
    (h1 : (i : ℕ) ≠ a + b) (j : Fin (a + b + 1)) :
    ruinChain a b i j =
      (if (j : ℕ) = i - 1 then 1 / 2 else 0) + (if (j : ℕ) = i + 1 then 1 / 2 else 0) := by
  simp only [ruinChain, Matrix.of_apply, h0, h1, or_self, ite_false]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- A sum over `Fin N` of a term that is `0` except where the index's value is `k`. -/
private theorem sum_ite_val_eq {N : ℕ} {k : ℕ} (hk : k < N) (f : Fin N → ℝ) :
    ∑ j : Fin N, (if (j : ℕ) = k then f j else 0) = f ⟨k, hk⟩ := by
  rw [Finset.sum_eq_single ⟨k, hk⟩ (fun j _ hj ↦ by
    simp only [ite_eq_right_iff]; exact fun h ↦ absurd (Fin.ext h) hj)
    (fun h ↦ absurd (Finset.mem_univ _) h)]
  simp

/-- The rows of `ruinChain a b` sum to `1` (one of `meanHitting_eq`'s hypotheses). -/
theorem sum_ruinChain (a b : ℕ) (i : Fin (a + b + 1)) : ∑ j, ruinChain a b i j = 1 := by
  by_cases he : (i : ℕ) = 0 ∨ (i : ℕ) = a + b
  · have hrow : ∀ j, ruinChain a b i j = if j = i then 1 else 0 := fun j ↦ by
      simp only [ruinChain, Matrix.of_apply]
      exact ite_eq_left he
    simp [hrow]
  · rw [not_or] at he
    simp only [ruinChain_apply_inside he.1 he.2, Finset.sum_add_distrib]
    rw [sum_ite_val_eq (f := fun _ ↦ (1 / 2 : ℝ)) (by omega),
      sum_ite_val_eq (f := fun _ ↦ (1 / 2 : ℝ)) (by omega)]
    norm_num

/-- The entries of `ruinChain a b` are at least `0` (one of `meanHitting_eq`'s hypotheses). -/
theorem ruinChain_nonneg (a b : ℕ) (i j : Fin (a + b + 1)) : 0 ≤ ruinChain a b i j := by
  simp only [ruinChain, Matrix.of_apply]
  split_ifs <;> norm_num

/-- From every inside index an end is reached with positive chance: walking down `i` steps,
`(ruinChain a b ^ i) i 0 ≥ (1/2) ^ i > 0` (one of `meanHitting_eq`'s hypotheses). -/
theorem exists_pow_ruinChain_pos (a b : ℕ) :
    ∀ i ∉ ({0, Fin.last (a + b)} : Finset (Fin (a + b + 1))),
      ∃ t, ∃ e ∈ ({0, Fin.last (a + b)} : Finset (Fin (a + b + 1))),
        0 < (ruinChain a b ^ t) i e := by
  have hpow0 : ∀ t (i j : Fin (a + b + 1)), 0 ≤ (ruinChain a b ^ t) i j := by
    intro t
    induction t with
    | zero => intro i j; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    | succ t ih =>
      intro i j
      rw [pow_succ', Matrix.mul_apply]
      exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (ruinChain_nonneg a b i k) (ih k j)
  have key : ∀ k (i : Fin (a + b + 1)), (i : ℕ) = k → (k < a + b ∨ k = 0) →
      0 < (ruinChain a b ^ k) i 0 := by
    intro k
    induction k with
    | zero =>
      intro i hi _
      have : i = 0 := Fin.ext hi
      rw [this, pow_zero, Matrix.one_apply_eq]
      exact one_pos
    | succ k ih =>
      intro i hi hk
      have hk' : k + 1 < a + b := by omega
      rw [pow_succ', Matrix.mul_apply]
      have hterm : 0 < ruinChain a b i ⟨k, by omega⟩ * (ruinChain a b ^ k) ⟨k, by omega⟩ 0 := by
        refine mul_pos ?_ (ih _ rfl (Or.inl (by omega)))
        rw [ruinChain_apply_inside (by omega) (by omega)]
        simp only [hi]
        split_ifs <;> first | (exfalso; omega) | norm_num
      exact hterm.trans_le (Finset.single_le_sum (f := fun j ↦
        ruinChain a b i j * (ruinChain a b ^ k) j 0)
        (fun j _ ↦ mul_nonneg (ruinChain_nonneg a b i j) (hpow0 k j 0))
        (Finset.mem_univ _))
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  refine ⟨i, 0, by simp, key i i rfl (Or.inl ?_)⟩
  have h1 : (i : ℕ) ≠ a + b := fun h ↦ hi.2 (Fin.ext (by simpa using h))
  omega

/-- **The mean time to the ends, by first-step analysis** (bridge 165, theorem 2). For the chain
`ruinChain a b` and the two ends `{0, Fin.last (a + b)}`, a function `g` on the indices is `0` at
the ends and satisfies `g i = 1 + ∑ j, ruinChain a b i j * g j` at every inside index if and only
if `g i = (a + b - i) i` for every index `i` (at position `x = i - b`, `(a - x)(x + b)`). So these
equations, whose only solution `FiniteChain.meanHitting_eq` names as the series `h` of the chain's
mean hitting times, have the solution `(a + b - i) i`, and no other. -/
theorem ruinChain_meanHitting_iff (a b : ℕ) (g : Fin (a + b + 1) → ℝ) :
    ((∀ i ∈ ({0, Fin.last (a + b)} : Finset (Fin (a + b + 1))), g i = 0) ∧
        ∀ i ∉ ({0, Fin.last (a + b)} : Finset (Fin (a + b + 1))),
          g i = 1 + ∑ j, ruinChain a b i j * g j) ↔
      g = fun i : Fin (a + b + 1) ↦ ((a : ℝ) + b - ((i : ℕ) : ℝ)) * ((i : ℕ) : ℝ) := by
  have key := (meanHitting_eq (sum_ruinChain a b) (ruinChain_nonneg a b)
    (exists_pow_ruinChain_pos a b)).2
  -- `(a + b - i) i` solves the equations
  have hg0 : (∀ i ∈ ({0, Fin.last (a + b)} : Finset (Fin (a + b + 1))),
        (fun i : Fin (a + b + 1) ↦ ((a : ℝ) + b - ((i : ℕ) : ℝ)) * ((i : ℕ) : ℝ)) i = 0) ∧
      ∀ i ∉ ({0, Fin.last (a + b)} : Finset (Fin (a + b + 1))),
        (fun i : Fin (a + b + 1) ↦ ((a : ℝ) + b - ((i : ℕ) : ℝ)) * ((i : ℕ) : ℝ)) i =
          1 + ∑ j, ruinChain a b i j *
            (fun i : Fin (a + b + 1) ↦ ((a : ℝ) + b - ((i : ℕ) : ℝ)) * ((i : ℕ) : ℝ)) j := by
    constructor
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> simp
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      have h0 : (i : ℕ) ≠ 0 := fun h ↦ hi.1 (Fin.ext h)
      have h1 : (i : ℕ) ≠ a + b := fun h ↦ hi.2 (Fin.ext (by simpa using h))
      simp only [ruinChain_apply_inside h0 h1, add_mul, ite_mul, zero_mul,
        Finset.sum_add_distrib]
      rw [sum_ite_val_eq (f := fun j : Fin (a + b + 1) ↦
          1 / 2 * (((a : ℝ) + b - ((j : ℕ) : ℝ)) * ((j : ℕ) : ℝ))) (by omega),
        sum_ite_val_eq (f := fun j : Fin (a + b + 1) ↦
          1 / 2 * (((a : ℝ) + b - ((j : ℕ) : ℝ)) * ((j : ℕ) : ℝ))) (by omega)]
      have hi1 : (((i : ℕ) - 1 : ℕ) : ℝ) = ((i : ℕ) : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      simp only [hi1]
      push_cast
      ring
  have hh := (key _).1 hg0
  constructor
  · intro hsys
    exact ((key g).1 hsys).trans hh.symm
  · rintro rfl
    exact hg0

/-- **Gambler's ruin by first-step analysis** (bridge 165, theorem 1). For the fair `±1` walk from
`0` (each step known by the next time, independent of the past, `±1`, of mean `0`: the hypotheses of
`integral_exitTime_eq`), and every `g` that is `0` at the two ends `{0, Fin.last (a + b)}` and
satisfies `g i = 1 + ∑ j, ruinChain a b i j * g j` at every inside index, the walk's mean exit time
from `(-b, a)` is `g` at the start index `b` (position `0`): `∫ τ dμ = g b`. With
`ruinChain_meanHitting_iff` (the equations have a solution) and `FiniteChain.meanHitting_eq` (every
solution is the series `h` of the chain's mean hitting times, the chain's hypotheses being
`sum_ruinChain`, `ruinChain_nonneg` and `exists_pow_ruinChain_pos`), this is `∫ τ dμ = h b`, the
row's form: the mean exit time of the walk is the mean hitting time of its chain at the start. Both
are `a b`. -/
theorem integral_exitTime_eq_meanHitting {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {𝒢 : Filtration ℕ m0} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ)
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) (hmean : ∀ n, ∫ ω, X n ω ∂μ = 0) (a b : ℕ)
    (g : Fin (a + b + 1) → ℝ)
    (hgA : ∀ i ∈ ({0, Fin.last (a + b)} : Finset (Fin (a + b + 1))), g i = 0)
    (hg : ∀ i ∉ ({0, Fin.last (a + b)} : Finset (Fin (a + b + 1))),
      g i = 1 + ∑ j, ruinChain a b i j * g j) :
    ∫ ω, ((exitTime X a b ω).untopA : ℝ) ∂μ = g ⟨b, by omega⟩ := by
  rw [integral_exitTime_eq hX hind hpm hmean a b, (ruinChain_meanHitting_iff a b g).1 ⟨hgA, hg⟩]
  simp

end ClassicalLean.Probability.RuinChain

open MeasureTheory ProbabilityTheory in
/-- The hypotheses of `integral_exitTime_eq_meanHitting` hold together: the fair walk of
`GamblersRuin`'s witness of `measureReal_hit_eq`, on the space of coin sequences `ℕ → Bool` with
independent fair coins (Mathlib's `Measure.infinitePi` of the uniform law on `Bool`); the steps
`X n = ±1` read from coin `n + 1`; the filtration is the one the coins' values generate, so step
`n` is known at time `n + 1` and independent of what time `n` knows; each step is `1` or `-1`, of
mean `0`, so the walk moves at every step. The targets `a = 2` and `b = 3`: six positions, four of
them inside, and the start index `3` is inside. `g i = (5 - i) i`, that is `0, 4, 6, 6, 4, 0`, is
`0` at the two ends and satisfies the first-step equation at each of the four inside indices
(checked at each of the six indices). -/
example := ClassicalLean.Probability.RuinChain.integral_exitTime_eq_meanHitting (Ω := ℕ → Bool)
  (μ := Measure.infinitePi fun _ ↦ uniformOn Set.univ)
  (𝒢 := Filtration.natural (fun i (ω : ℕ → Bool) ↦ if ω i then (1 : ℝ) else -1)
    fun i ↦ ((measurable_of_countable fun c : Bool ↦ if c then (1 : ℝ) else -1).comp
      (measurable_pi_apply i)).stronglyMeasurable)
  (X := fun n ω ↦ if ω (n + 1) then 1 else -1)
  (fun n ↦ Filtration.stronglyAdapted_natural
    (u := fun i (ω : ℕ → Bool) ↦ if ω i then (1 : ℝ) else -1) _ (n + 1))
  (fun n ↦ (iIndepFun_infinitePi (P := fun _ : ℕ ↦ (uniformOn Set.univ : Measure Bool))
    (X := fun _ (c : Bool) ↦ if c then (1 : ℝ) else -1)
    fun _ ↦ measurable_of_countable _).indep_comap_natural_of_lt _ (Nat.lt_succ_self n))
  (fun n ω ↦ by split_ifs <;> simp)
  (fun n ↦ by
    rw [← integral_map (φ := fun ω : ℕ → Bool ↦ ω (n + 1))
      (f := fun c : Bool ↦ if c then (1 : ℝ) else -1) (measurable_pi_apply (n + 1)).aemeasurable
      (measurable_of_countable fun c : Bool ↦ if c then (1 : ℝ) else -1).aestronglyMeasurable,
      Measure.infinitePi_map_eval, integral_fintype Integrable.of_finite]
    simp only [Measure.real, uniformOn_univ]
    simp)
  (a := 2) (b := 3) (g := fun i ↦ (5 - ((i : ℕ) : ℝ)) * (i : ℕ))
  (fun i hi ↦ by
    fin_cases i <;> simp at hi ⊢)
  (fun i hi ↦ by
    fin_cases i <;>
      simp [ClassicalLean.Probability.RuinChain.ruinChain, Fin.sum_univ_succ, Fin.last] at hi ⊢ <;>
      norm_num)
