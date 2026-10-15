/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Probability.UniformOn

/-!
# The reflection principle for the fair `±1` walk

A path of `n` fair coin flips is `ω : Fin n → Bool`, every path with the same chance
(`uniformOn Set.univ`). Flip `j` moves the walk up by `1` (`true`) or down by `1` (`false`);
`walk n ω k` is its position after `k` steps. Order CLOUD-MATH-1, item 139 of MATH-PLAN-library-2.

* `measureReal_max_ge_eq` — **the reflection principle**: for a level `a ≥ 1`,
  `P(max_{k ≤ n} S_k ≥ a) = P(S_n ≥ a) + P(S_n > a)`.

The proof counts paths. A path reaches `a` (`Hit n a ω`) either ending at or above `a`, or ending
below `a`. Reflecting a path after its first visit to `a` (`reflect n a ω`: every flip from
`tau n a ω` on reversed, `flipFrom`) is its own inverse, and turns the paths that reach `a` and
end below `a` into the paths that end above `a`; a walk that moves by `1` reaches `a ≥ 1`
exactly at `a`, so its end `S_n` goes to `2 a − S_n`. So the count of paths that reach `a` is
the count that end at or above `a` plus the count that end above `a`, and dividing by `2 ^ n`
gives the chances.

Definitions: `step` (one flip's `±1`, `0` past `n`), `walk`, `flipFrom` (reverse every flip from a
time on), `Hit` (the walk reaches `a` by time `n`), `tau` (the first time it does), `reflect`.
-/

open MeasureTheory ProbabilityTheory

namespace ClassicalLean.Probability.Reflection

/-- The `j`-th increment of the walk: `+1` or `-1` by the `j`-th coordinate, `0` past `n`. -/
def step (n : ℕ) (ω : Fin n → Bool) (j : ℕ) : ℤ :=
  if h : j < n then (if ω ⟨j, h⟩ then 1 else -1) else 0

/-- The position of the walk after `k` steps. -/
def walk (n : ℕ) (ω : Fin n → Bool) (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range k, step n ω j

private lemma walk_zero (n : ℕ) (ω : Fin n → Bool) : walk n ω 0 = 0 := by
  simp [walk]

private lemma walk_succ (n : ℕ) (ω : Fin n → Bool) (k : ℕ) :
    walk n ω (k + 1) = walk n ω k + step n ω k := by
  unfold walk
  rw [Finset.sum_range_succ]

private lemma step_le_one (n : ℕ) (ω : Fin n → Bool) (j : ℕ) : step n ω j ≤ 1 := by
  unfold step
  split_ifs <;> norm_num

/-- Flip all coordinates from index `t` on. -/
def flipFrom (n t : ℕ) (ω : Fin n → Bool) : Fin n → Bool :=
  fun i => if t ≤ (i : ℕ) then !ω i else ω i

private lemma flipFrom_flipFrom (n t : ℕ) (ω : Fin n → Bool) :
    flipFrom n t (flipFrom n t ω) = ω := by
  funext i
  simp only [flipFrom]
  by_cases h : t ≤ (i : ℕ) <;> simp [h]

private lemma step_flipFrom (n t : ℕ) (ω : Fin n → Bool) (j : ℕ) :
    step n (flipFrom n t ω) j = if t ≤ j then -step n ω j else step n ω j := by
  by_cases hj : j < n
  · by_cases ht : t ≤ j
    · cases hω : ω ⟨j, hj⟩ <;> simp [step, flipFrom, hj, ht, hω]
    · simp [step, flipFrom, hj, ht]
  · simp [step, hj]

private lemma walk_flipFrom_of_le (n t : ℕ) (ω : Fin n → Bool) :
    ∀ k, k ≤ t → walk n (flipFrom n t ω) k = walk n ω k := by
  intro k
  induction k with
  | zero => intro _; rw [walk_zero, walk_zero]
  | succ k ih =>
    intro hk
    rw [walk_succ, walk_succ, ih (by omega), step_flipFrom,
      ite_eq_right (show ¬ t ≤ k by omega)]

private lemma walk_flipFrom_of_ge (n t : ℕ) (ω : Fin n → Bool) (k : ℕ) (hk : t ≤ k) :
    walk n (flipFrom n t ω) k = 2 * walk n ω t - walk n ω k := by
  induction k, hk using Nat.le_induction with
  | base => rw [walk_flipFrom_of_le n t ω t le_rfl]; ring
  | succ k hk ih =>
    rw [walk_succ, walk_succ, ih, step_flipFrom, ite_eq_left hk]; ring

/-- The walk reaches level `a` at some time `k ≤ n`. -/
abbrev Hit (n : ℕ) (a : ℤ) (ω : Fin n → Bool) : Prop :=
  ∃ k, k ≤ n ∧ a ≤ walk n ω k

open Classical in
/-- First time the walk reaches level `a`. -/
noncomputable def tau (n : ℕ) (a : ℤ) (ω : Fin n → Bool) : ℕ :=
  if h : Hit n a ω then Nat.find h else 0

open Classical in
/-- Reflection of the path after its first passage at level `a`. -/
noncomputable def reflect (n : ℕ) (a : ℤ) (ω : Fin n → Bool) : Fin n → Bool :=
  if Hit n a ω then flipFrom n (tau n a ω) ω else ω

private lemma tau_spec {n : ℕ} {a : ℤ} {ω : Fin n → Bool} (h : Hit n a ω) :
    tau n a ω ≤ n ∧ a ≤ walk n ω (tau n a ω) := by
  unfold tau
  rw [dite_eq_left h]
  exact Nat.find_spec h

private lemma tau_min {n : ℕ} {a : ℤ} {ω : Fin n → Bool} (h : Hit n a ω) (k : ℕ)
    (hk : k ≤ n) (hak : a ≤ walk n ω k) : tau n a ω ≤ k := by
  unfold tau
  rw [dite_eq_left h]
  exact Nat.find_min' h ⟨hk, hak⟩

private lemma walk_tau {n : ℕ} {a : ℤ} {ω : Fin n → Bool} (ha : 1 ≤ a) (h : Hit n a ω) :
    walk n ω (tau n a ω) = a := by
  obtain ⟨h1, h2⟩ := tau_spec h
  have hpos : tau n a ω ≠ 0 := by
    intro h0
    rw [h0, walk_zero] at h2
    omega
  obtain ⟨m, hm⟩ : ∃ m, tau n a ω = m + 1 := ⟨tau n a ω - 1, by omega⟩
  have hlt : walk n ω m < a := by
    by_contra hc
    push Not at hc
    have := tau_min h m (by omega) hc
    omega
  have := step_le_one n ω m
  rw [hm, walk_succ] at h2 ⊢
  omega

private lemma hit_flip {n : ℕ} {a : ℤ} {ω : Fin n → Bool} (h : Hit n a ω) :
    Hit n a (flipFrom n (tau n a ω) ω) ∧
      tau n a (flipFrom n (tau n a ω) ω) = tau n a ω := by
  obtain ⟨h1, h2⟩ := tau_spec h
  have hw : walk n (flipFrom n (tau n a ω) ω) (tau n a ω) = walk n ω (tau n a ω) :=
    walk_flipFrom_of_le n (tau n a ω) ω (tau n a ω) le_rfl
  have h3 : a ≤ walk n (flipFrom n (tau n a ω) ω) (tau n a ω) := by
    rw [hw]; exact h2
  have h' : Hit n a (flipFrom n (tau n a ω) ω) := ⟨tau n a ω, h1, h3⟩
  refine ⟨h', le_antisymm (tau_min h' _ h1 h3) ?_⟩
  obtain ⟨s1, s2⟩ := tau_spec h'
  by_contra hc
  push Not at hc
  rw [walk_flipFrom_of_le n (tau n a ω) ω _ hc.le] at s2
  have := tau_min h _ s1 s2
  omega

private lemma reflect_of_hit {n : ℕ} {a : ℤ} {ω : Fin n → Bool} (h : Hit n a ω) :
    reflect n a ω = flipFrom n (tau n a ω) ω := by
  unfold reflect
  rw [ite_eq_left h]

private lemma reflect_of_not {n : ℕ} {a : ℤ} {ω : Fin n → Bool} (h : ¬ Hit n a ω) :
    reflect n a ω = ω := by
  unfold reflect
  rw [ite_eq_right h]

private lemma reflect_reflect {n : ℕ} {a : ℤ} (ω : Fin n → Bool) :
    reflect n a (reflect n a ω) = ω := by
  by_cases h : Hit n a ω
  · obtain ⟨h', ht⟩ := hit_flip h
    rw [reflect_of_hit h, reflect_of_hit h', ht, flipFrom_flipFrom]
  · rw [reflect_of_not h, reflect_of_not h]

private lemma walk_reflect_end {n : ℕ} {a : ℤ} {ω : Fin n → Bool} (ha : 1 ≤ a)
    (h : Hit n a ω) : walk n (reflect n a ω) n = 2 * a - walk n ω n := by
  rw [reflect_of_hit h, walk_flipFrom_of_ge n _ ω n (tau_spec h).1, walk_tau ha h]

private lemma card_eq (n : ℕ) (a : ℤ) (ha : 1 ≤ a)
    [DecidablePred (fun ω : Fin n → Bool => Hit n a ω)]
    [DecidablePred (fun ω : Fin n → Bool => a ≤ walk n ω n)]
    [DecidablePred (fun ω : Fin n → Bool => a < walk n ω n)] :
    (Finset.univ.filter (fun ω : Fin n → Bool => Hit n a ω)).card =
      (Finset.univ.filter (fun ω : Fin n → Bool => a ≤ walk n ω n)).card +
      (Finset.univ.filter (fun ω : Fin n → Bool => a < walk n ω n)).card := by
  classical
  have hunion : Finset.univ.filter (fun ω : Fin n → Bool => Hit n a ω) =
      Finset.univ.filter (fun ω : Fin n → Bool => a ≤ walk n ω n) ∪
      Finset.univ.filter (fun ω : Fin n → Bool => Hit n a ω ∧ walk n ω n < a) := by
    ext ω
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      by_cases h' : a ≤ walk n ω n
      · exact Or.inl h'
      · exact Or.inr ⟨h, by omega⟩
    · rintro (h | ⟨h, _⟩)
      · exact ⟨n, le_rfl, h⟩
      · exact h
  have hinter : Finset.univ.filter (fun ω : Fin n → Bool => a ≤ walk n ω n) ∩
      Finset.univ.filter (fun ω : Fin n → Bool => Hit n a ω ∧ walk n ω n < a) = ∅ := by
    ext ω
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, _, h2⟩
      omega
    · intro h
      simp at h
  have hD : (Finset.univ.filter
        (fun ω : Fin n → Bool => Hit n a ω ∧ walk n ω n < a)).card =
      (Finset.univ.filter (fun ω : Fin n → Bool => a < walk n ω n)).card := by
    apply Finset.card_nbij' (reflect n a) (reflect n a)
    · intro ω hω
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      obtain ⟨h, hlt⟩ := hω
      rw [walk_reflect_end ha h]
      omega
    · intro ω hω
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      have h : Hit n a ω := ⟨n, le_rfl, hω.le⟩
      refine ⟨?_, ?_⟩
      · rw [reflect_of_hit h]
        exact (hit_flip h).1
      · rw [walk_reflect_end ha h]
        omega
    · intro ω _
      exact reflect_reflect ω
    · intro ω _
      exact reflect_reflect ω
  have key := Finset.card_union_add_card_inter
    (Finset.univ.filter (fun ω : Fin n → Bool => a ≤ walk n ω n))
    (Finset.univ.filter (fun ω : Fin n → Bool => Hit n a ω ∧ walk n ω n < a))
  rw [← hunion, hinter, Finset.card_empty, add_zero] at key
  rw [key, hD]

private lemma real_uniform {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (p : Ω → Prop) [DecidablePred p] :
    (uniformOn (Set.univ : Set Ω)).real {ω | p ω} =
      ((Finset.univ.filter p).card : ℝ) / Fintype.card Ω := by
  have h : {ω | p ω} = ((Finset.univ.filter p : Finset Ω) : Set Ω) := by
    ext; simp
  rw [measureReal_def, uniformOn_univ, h, Measure.count_apply_finset, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast]

/-- **The reflection principle** for the fair `±1` walk of length `n` (item 139 of
MATH-PLAN-library-2): for a level `a ≥ 1`, the chance that the walk's maximum over the times
`0, 1, …, n` is at least `a` equals the chance that it ends at or above `a` plus the chance that it
ends above `a`: `P(max_{k ≤ n} S_k ≥ a) = P(S_n ≥ a) + P(S_n > a)`. -/
theorem measureReal_max_ge_eq (n : ℕ) (a : ℤ) (ha : 1 ≤ a) :
    (uniformOn (Set.univ : Set (Fin n → Bool))).real
        {ω | a ≤ (Finset.range (n + 1)).sup' ⟨0, by simp⟩ (walk n ω)} =
      (uniformOn (Set.univ : Set (Fin n → Bool))).real
          {ω | a ≤ walk n ω n} +
        (uniformOn (Set.univ : Set (Fin n → Bool))).real
          {ω | a < walk n ω n} := by
  classical
  have hset : {ω : Fin n → Bool |
      a ≤ (Finset.range (n + 1)).sup' ⟨0, by simp⟩ (walk n ω)} =
      {ω | Hit n a ω} := by
    ext ω
    change a ≤ (Finset.range (n + 1)).sup' ⟨0, by simp⟩ (walk n ω) ↔
      Hit n a ω
    constructor
    · intro h
      obtain ⟨k, hk, hk'⟩ :=
        Finset.exists_mem_eq_sup' (⟨0, by simp⟩ : (Finset.range (n + 1)).Nonempty)
          (walk n ω)
      have hk2 : k < n + 1 := Finset.mem_range.1 hk
      exact ⟨k, by omega, h.trans hk'.le⟩
    · rintro ⟨k, hk, h⟩
      exact h.trans (Finset.le_sup' (walk n ω) (Finset.mem_range.2 (by omega)))
  rw [hset, real_uniform, real_uniform, real_uniform,
    card_eq n a ha]
  push_cast
  ring

end ClassicalLean.Probability.Reflection

/-- The hypotheses of `measureReal_max_ge_eq` hold together: a walk of `n = 4` fair steps and the
level `a = 2`, which is at least `1` and which the walk can reach within its `4` steps. -/
example := ClassicalLean.Probability.Reflection.measureReal_max_ge_eq (n := 4) (a := 2)
  (by norm_num)
