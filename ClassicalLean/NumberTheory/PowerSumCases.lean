/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Algebra.CompanionMatrix
import ClassicalLean.Geometry.Spectral3x3
import ClassicalLean.NumberTheory.LucasSequence
import ClassicalLean.NumberTheory.LucasCompanion
import ClassicalLean.NumberTheory.NacciTrace

/-!
# The library's two trace towers are power sums of a companion matrix

`ClassicalLean/Algebra/CompanionMatrix.lean` proves that `k ↦ (M ^ k).trace` — the power sums
of a monic polynomial — solves the linear recurrence given by its coefficients.  This file
identifies the two places the library had already computed such traces.

## `Geometry/Helix.lean` and `NumberTheory/LucasCompanion.lean` — absorbed completely

`Geometry.companionMatrix = !![0, -1; 1, 3]` is `companionMatrix ![-1, 3]`, the general
construction at `d = 1` with `(P, Q) = (3, 1)`.  Since a second-order solution is pinned by two
values, and `trace (M ^ 0) = 2 = V 0` and `trace M = c (last) = P = V 1` come from the general
theorems, `lucasCompanion_pow_trace` below holds **for every `k`** — where
`LucasCompanion.lean` proved it only for `k ≥ 1`, by its own induction.  The `k = 0` case was
not an oversight there: `lucasCompanion_pow_succ` is stated at `n + 1` because the entry formula
degenerates at `n = 0`.  The trace does not.

## `NumberTheory/NacciTrace.lean` — absorbed completely

`nacciAugmented n` is the sequence whose module header says, in prose, that it is "the `k`-th
power sum of the roots of `x^(n+1) - 2x^n + 1`".  That polynomial's companion matrix is
`companionMatrix (nacciCoeffs n)` for `nacciCoeffs n = ![-1, 0, …, 0, 2]`, and this file proves:

* `nacciAugmented_isSol` — `nacciAugmented n` **is** a solution of `companionRec (nacciCoeffs n)`,
  which is `nacciAugmented_sub` repackaged;
* `trace_nacciCompanion_pow_zero` and `_one` — the traces at `0` and `1` are `n + 1` and `2`,
  matching `nacciAugmented n 0` and `nacciAugmented n 1`;
* `nacciAugmented_eq_trace_of_initial` — given agreement at every index `2 ≤ k ≤ n`, the two
  sequences are equal at every index, by `LinearRecurrence.eq_iff_eqOn_range_order`;
* `trace_nacciCompanion_pow` — that agreement, i.e. `trace (M ^ k) = 2 ^ k` for `1 ≤ k ≤ n`.
  Its hypothesis is `1 ≤ k`, one index weaker than the `2 ≤ k` the previous item asks for; the
  proof needs no more than `1 ≤ k`, so it is stated at the range it proves, not the range it
  is used at;
* `nacciAugmented_eq_trace` — the conclusion, **unconditionally**:
  `nacciAugmented n k = trace (M ^ k)` for every `k`.

`trace_nacciCompanion_pow` is Newton's identity in the regime `k ≤ d`, which
`CompanionMatrix.lean` does *not* prove for arbitrary coefficients — it proves only `k > d`,
which is Cayley–Hamilton.  What makes this family tractable is that `c 1, …, c (n-1)` all
vanish, so `M ^ m *ᵥ e_last` has a closed form (`nacciPow`): a geometric tail `-2 ^ (m-1-j)` on
the first `m` coordinates and `2 ^ m` in the last.  Given that, only the last diagonal entry of
`M ^ k` is nonzero for `k ≤ n`, and it is `2 ^ k`.

So the prose of `NacciTrace.lean` — "`A n k` is the `k`-th power sum of the roots of
`x^(n+1) - 2x^n + 1`", which that module explicitly flags as *not* formalised and *not* used —
is now a theorem.

## Naming

`nacciCoeffs` is named for the polynomial it presents, in the vocabulary
`NumberTheory/NacciTrace.lean` already uses.
-/

namespace ClassicalLean

open Matrix

/-! ### The Lucas companion matrix, absorbed -/

/-- `Geometry.companionMatrix` is the general companion matrix at `d = 1`, `c = ![-1, 3]`. -/
theorem geometry_companionMatrix_eq :
    Geometry.companionMatrix = companionMatrix (![-1, 3] : Fin 2 → ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Geometry.companionMatrix, companionMatrix_apply, Fin.last]

/-- `lucasCompanion P Q` is `companionMatrix ![-Q, P]`. -/
theorem lucasCompanion_eq_companionMatrix {R : Type*} [CommRing R] (P Q : R) :
    lucasCompanion P Q = companionMatrix ![-Q, P] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lucasCompanion, companionMatrix_apply, Fin.last]

/-- **The trace of every power, including the zeroth.**
`(lucasCompanion P Q ^ k).trace = V k` for every `k : ℕ`.

`LucasCompanion.lean` proves this for `k ≥ 1` by its own induction on the matrix entries.  Here
it is the general power-sum theorem: the traces solve the order-`2` recurrence
(`trace_companionMatrix_pow_isSol`), the two initial values are `trace (M ^ 0) = 2 = V 0` and
`trace M = P = V 1` (`trace_companionMatrix_pow_zero`, `trace_companionMatrix`), and a
second-order solution is determined by two values. -/
theorem lucasCompanion_pow_trace {R : Type*} [CommRing R] (P Q : R) (k : ℕ) :
    (lucasCompanion P Q ^ k).trace = lucasV P Q k := by
  have hM := lucasCompanion_eq_companionMatrix P Q
  have hrec := trace_companionMatrix_pow_isSol (![-Q, P] : Fin 2 → R)
  induction k using Nat.twoStepInduction with
  | zero =>
    rw [hM, trace_companionMatrix_pow_zero]
    simp
    norm_num
  | one =>
    rw [hM, pow_one, trace_companionMatrix]
    simp [Fin.last]
  | more k ih1 ih2 =>
    have h := hrec k
    simp only [companionRec] at h
    rw [hM] at ih1 ih2 ⊢
    rw [h]
    erw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero, Fin.val_one,
      Nat.add_zero]
    rw [ih1, ih2, lucasV_add_two]
    ring

/-! ### The n-nacci trace tower -/

/-- The coefficient vector of `x ^ (n+1) - 2 x ^ n + 1`, presented as
`x ^ (n+1) - (2 x ^ n - 1)`: `c 0 = -1`, `c n = 2`, and every coefficient between them is `0`.

Written as a sum of two indicators rather than nested `if`s, because that is the form the sum
over `Fin (n+1)` collapses in.  At `n = 0` the two indicators coincide and the vector is `1`;
every theorem below assumes `1 ≤ n`. -/
def nacciCoeffs (n : ℕ) : Fin (n + 1) → ℤ :=
  fun i => (if i = 0 then -1 else 0) + (if i = Fin.last n then 2 else 0)

theorem nacciCoeffs_last (n : ℕ) (hn : 1 ≤ n) : nacciCoeffs n (Fin.last n) = 2 := by
  have h : (Fin.last n : Fin (n + 1)) ≠ 0 := by
    simp only [Ne, Fin.ext_iff, Fin.val_last, Fin.val_zero]
    omega
  simp [nacciCoeffs, h]

theorem nacciCoeffs_zero (n : ℕ) (hn : 1 ≤ n) : nacciCoeffs n 0 = -1 := by
  have h : (0 : Fin (n + 1)) ≠ Fin.last n := by
    simp only [Ne, Fin.ext_iff, Fin.val_last, Fin.val_zero]
    omega
  simp [nacciCoeffs, h]

/-- `trace (M ^ 0) = n + 1`, matching `nacciAugmented n 0`.

Stated without `1 ≤ n` on purpose, and it is true at `n = 0`: `nacciAugmented 0 0 = 1` and
`M ^ 0` is the `1 × 1` identity, whose trace is `1`.  Adding `hn` here would weaken a true
statement. -/
theorem trace_nacciCompanion_pow_zero (n : ℕ) :
    (companionMatrix (nacciCoeffs n) ^ 0).trace = nacciAugmented n 0 := by
  rw [trace_companionMatrix_pow_zero, nacciAugmented_zero]

/-- `trace M = 2`, matching `nacciAugmented n 1`. -/
theorem trace_nacciCompanion_pow_one (n : ℕ) (hn : 1 ≤ n) :
    (companionMatrix (nacciCoeffs n) ^ 1).trace = nacciAugmented n 1 := by
  rw [pow_one, trace_companionMatrix, nacciCoeffs_last n hn, nacciAugmented_one]

/-- The sum against `nacciCoeffs` collapses to the two nonzero coefficients. -/
private theorem sum_nacciCoeffs (n : ℕ) (u : ℕ → ℤ) (m : ℕ) :
    ∑ i : Fin (n + 1), nacciCoeffs n i * u (m + (i : ℕ))
      = -u m + 2 * u (m + n) := by
  have h : ∀ i : Fin (n + 1), nacciCoeffs n i * u (m + (i : ℕ))
      = (if i = 0 then (-1 : ℤ) * u (m + (i : ℕ)) else 0)
        + (if i = Fin.last n then (2 : ℤ) * u (m + (i : ℕ)) else 0) := by
    intro i
    rw [nacciCoeffs]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (0 : Fin (n + 1)) (fun i => (-1 : ℤ) * u (m + (i : ℕ))),
    Finset.sum_ite_eq' Finset.univ (Fin.last n) (fun i => (2 : ℤ) * u (m + (i : ℕ)))]
  simp

/-- **`nacciAugmented n` solves the companion recurrence.**  This is `nacciAugmented_sub` — the
past-the-prefix branch of the definition — repackaged as Mathlib's `IsSolution`, which is what
lets `eq_iff_eqOn_range_order` be applied below. -/
theorem nacciAugmented_isSol (n : ℕ) (hn : 1 ≤ n) :
    (companionRec (nacciCoeffs n)).IsSolution (nacciAugmented n) := by
  intro m
  simp only [companionRec]
  have hsub := nacciAugmented_sub n (m + (n + 1)) (by omega) (by omega)
  rw [show m + (n + 1) - 1 = m + n from by omega,
    show m + (n + 1) - (n + 1) = m from by omega] at hsub
  rw [hsub]
  erw [sum_nacciCoeffs]
  ring

/-! ### Newton's identity in the regime `k ≤ d`, for this polynomial

The general file proves the recurrence only for `k > d`.  For `x ^ (n+1) - 2 x ^ n + 1` the
intermediate coefficients all vanish, and that is enough to compute `M ^ m *ᵥ e_last`
explicitly and read the remaining traces off it. -/

/-- `M ^ m *ᵥ e_last` in closed form, for `m ≤ n`: a geometric tail `-2 ^ (m-1-j)` on the first
`m` coordinates, and `2 ^ m` in the last.  At `m = 0` it is `e_last` itself. -/
private def nacciPow (n m : ℕ) : Fin (n + 1) → ℤ :=
  fun j => (if (j : ℕ) < m then -2 ^ (m - 1 - (j : ℕ)) else 0)
         + (if j = Fin.last n then 2 ^ m else 0)

private theorem nacciPow_apply_last (n m : ℕ) (h : m ≤ n) :
    nacciPow n m (Fin.last n) = 2 ^ m := by
  simp only [nacciPow, Fin.val_last]
  rw [ite_eq_right (by omega)]
  simp

private theorem nacciPow_zero (n : ℕ) : nacciPow n 0 = Pi.single (Fin.last n) 1 := by
  funext j
  simp only [nacciPow, Nat.not_lt_zero, pow_zero, Pi.single_apply]
  by_cases h : j = Fin.last n
  · simp [h]
  · simp [h]

/-- The closed form, by induction on `m`. -/
private theorem nacciCompanion_pow_mulVec_last (n : ℕ) (hn : 1 ≤ n) :
    ∀ m : ℕ, m ≤ n →
      companionMatrix (nacciCoeffs n) ^ m *ᵥ (Pi.single (Fin.last n) 1) = nacciPow n m := by
  intro m
  induction m with
  | zero => intro _; rw [pow_zero, Matrix.one_mulVec, nacciPow_zero]
  | succ m ih =>
    intro hm
    have hmn : m ≤ n := by omega
    rw [pow_succ', ← mulVec_mulVec, ih hmn]
    funext i
    have hlastval : nacciPow n m (Fin.last n) = 2 ^ m := nacciPow_apply_last n m hmn
    obtain ⟨iv, hiv⟩ := i
    match iv, hiv with
    | 0, hiv =>
      have h0 : (⟨0, hiv⟩ : Fin (n + 1)) = 0 := rfl
      rw [h0, companionMatrix_mulVec_apply_zero, hlastval, nacciCoeffs_zero n hn]
      have hne : (0 : Fin (n + 1)) ≠ Fin.last n := by
        simp only [Ne, Fin.ext_iff, Fin.val_last, Fin.val_zero]; omega
      simp only [nacciPow, Fin.val_zero, ite_eq_left (Nat.succ_pos m), ite_eq_right hne, add_zero,
        Nat.add_sub_cancel, Nat.sub_zero]
      ring
    | (p + 1), hiv =>
      rw [companionMatrix_mulVec_apply_succ _ _ p hiv, hlastval]
      by_cases hlast : p + 1 = n
      · have he : (⟨p + 1, hiv⟩ : Fin (n + 1)) = Fin.last n := by
          simp [Fin.ext_iff, hlast]
        rw [he, nacciCoeffs_last n hn, nacciPow_apply_last n (m + 1) hm]
        have hpm : ¬ (p < m) := by omega
        have hpn : (⟨p, by omega⟩ : Fin (n + 1)) ≠ Fin.last n := by
          simp only [Ne, Fin.ext_iff, Fin.val_last]; omega
        simp only [nacciPow, ite_eq_right hpm, ite_eq_right hpn, add_zero, zero_add]
        ring
      · have hne : (⟨p + 1, hiv⟩ : Fin (n + 1)) ≠ Fin.last n := by
          simp only [Ne, Fin.ext_iff, Fin.val_last]; omega
        have hc : nacciCoeffs n ⟨p + 1, hiv⟩ = 0 := by
          have h0 : (⟨p + 1, hiv⟩ : Fin (n + 1)) ≠ 0 := by
            simp only [Ne, Fin.ext_iff, Fin.val_zero]
            omega
          simp [nacciCoeffs, h0, hne]
        have hpn : (⟨p, by omega⟩ : Fin (n + 1)) ≠ Fin.last n := by
          simp only [Ne, Fin.ext_iff, Fin.val_last]; omega
        rw [hc]
        simp only [nacciPow, ite_eq_right hpn, ite_eq_right hne, add_zero, zero_mul, add_zero]
        by_cases hpm : p < m
        · rw [ite_eq_left hpm, ite_eq_left (by omega)]
          congr 2
          omega
        · rw [ite_eq_right hpm, ite_eq_right (by omega)]

/-- **The missing regime, discharged for this polynomial.**
`trace (M ^ k) = 2 ^ k` for `1 ≤ k ≤ n`.

Only the last diagonal entry contributes: for `j` with `j + k ≤ n` the shift has not wrapped and
`M ^ k *ᵥ eⱼ = e_{j+k}` has no `j`-component, while for `j` past that point the vector is
`nacciPow n (k - (n - j))`, whose `j`-component vanishes unless `j` is the last index. -/
theorem trace_nacciCompanion_pow (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ n) :
    (companionMatrix (nacciCoeffs n) ^ k).trace = 2 ^ k := by
  rw [trace_eq_sum_mulVec_single]
  have hterm : ∀ j : Fin (n + 1),
      (companionMatrix (nacciCoeffs n) ^ k *ᵥ (Pi.single j 1)) j
        = if j = Fin.last n then (2 : ℤ) ^ k else 0 := by
    intro j
    obtain ⟨jv, hjv⟩ := j
    by_cases hwrap : jv + k ≤ n
    · have hne : (⟨jv, hjv⟩ : Fin (n + 1)) ≠ Fin.last n := by
        simp only [Ne, Fin.ext_iff, Fin.val_last]; omega
      rw [companionMatrix_pow_mulVec_single _ jv k (by omega), ite_eq_right hne, Pi.single_apply,
        ite_eq_right (by simp only [Fin.ext_iff]; omega)]
    · push Not at hwrap
      have hr : jv + (n - jv) = n := by omega
      have hstep : companionMatrix (nacciCoeffs n) ^ k *ᵥ (Pi.single (⟨jv, hjv⟩ : Fin (n + 1)) 1)
          = companionMatrix (nacciCoeffs n) ^ (k - (n - jv)) *ᵥ (Pi.single (Fin.last n) 1) := by
        have hsplit : k = (k - (n - jv)) + (n - jv) := by omega
        have hidx : (⟨jv + (n - jv), by omega⟩ : Fin (n + 1)) = Fin.last n :=
          Fin.ext (by change jv + (n - jv) = n; omega)
        rw [hsplit, pow_add, ← mulVec_mulVec,
          companionMatrix_pow_mulVec_single _ jv (n - jv) (by omega), hidx,
          show k - (n - jv) + (n - jv) - (n - jv) = k - (n - jv) from by omega]
      rw [hstep, nacciCompanion_pow_mulVec_last n hn _ (by omega)]
      by_cases hl : jv = n
      · have he : (⟨jv, hjv⟩ : Fin (n + 1)) = Fin.last n := by simp [Fin.ext_iff, hl]
        rw [he, ite_eq_left rfl, show n - jv = 0 from by omega, Nat.sub_zero,
          nacciPow_apply_last n k (by omega)]
      · have hne : (⟨jv, hjv⟩ : Fin (n + 1)) ≠ Fin.last n := by
          simp only [Ne, Fin.ext_iff, Fin.val_last]; omega
        rw [ite_eq_right hne]
        simp only [nacciPow, ite_eq_right hne]
        rw [ite_eq_right (by omega), add_zero]
  rw [Finset.sum_congr rfl (fun j _ => hterm j),
    Finset.sum_ite_eq' Finset.univ (Fin.last n) (fun _ => (2 : ℤ) ^ k)]
  simp

/-- **The identification, modulo the one missing regime.**  If the companion matrix's power-sum
traces agree with `nacciAugmented n` at every index `2 ≤ k ≤ n`, then they agree at *every*
index — both are solutions of the same order-`(n+1)` recurrence, and they already agree at `0`
and `1`.

The hypothesis is Newton's identity in the regime `k ≤ d`; see the module header.  Discharging
it turns the prose of `NacciTrace.lean` — "`A n k` is the `k`-th power sum of the roots of
`x^(n+1) - 2x^n + 1`" — into a theorem. -/
theorem nacciAugmented_eq_trace_of_initial (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ k, 2 ≤ k → k ≤ n → (companionMatrix (nacciCoeffs n) ^ k).trace = nacciAugmented n k) :
    ∀ k, nacciAugmented n k = (companionMatrix (nacciCoeffs n) ^ k).trace := by
  have hEq : nacciAugmented n = fun k => (companionMatrix (nacciCoeffs n) ^ k).trace := by
    rw [(companionRec (nacciCoeffs n)).eq_iff_eqOn_range_order _ _ (nacciAugmented_isSol n hn)
      (trace_companionMatrix_pow_isSol _)]
    intro k hk
    simp only [companionRec_order, Finset.coe_range, Set.mem_Iio] at hk
    match k, hk with
    | 0, _ => exact (trace_nacciCompanion_pow_zero n).symm
    | 1, _ => exact (trace_nacciCompanion_pow_one n hn).symm
    | (k + 2), hk => exact (h (k + 2) (by omega) (by omega)).symm
  intro k
  exact congrFun hEq k

/-- **The identification, unconditionally.**
`nacciAugmented n k = trace (M ^ k)` for every `k`, where `M` is the companion matrix of
`x ^ (n+1) - 2 x ^ n + 1`.

This is what `NumberTheory/NacciTrace.lean` says in prose — "`A n k` is the `k`-th power sum of
the roots of the augmented polynomial" — and it is now a theorem.  The three ingredients are
`nacciAugmented_isSol` (the past-the-prefix branch is the companion recurrence),
`trace_nacciCompanion_pow` (the prefix branch is Newton's `k ≤ d` regime, computed here for this
polynomial), and `nacciAugmented_mersenne_prefix` (which is what the prefix branch *says*). -/
theorem nacciAugmented_eq_trace (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    nacciAugmented n k = (companionMatrix (nacciCoeffs n) ^ k).trace := by
  refine nacciAugmented_eq_trace_of_initial n hn (fun j hj1 hj2 => ?_) k
  rw [trace_nacciCompanion_pow n hn j (by omega) hj2,
    nacciAugmented_mersenne_prefix n j (by omega) hj2]

/-! ### Spot checks -/

-- `n = 3`: the polynomial is `x⁴ - 2x³ + 1`, its companion matrix is 4×4, and the traces of its
-- powers are `4, 2, 4, 8, 18, …` — the augmented tower `A 3`.
example : (companionMatrix (nacciCoeffs 3) ^ 0).trace = 4 := by decide

example : (companionMatrix (nacciCoeffs 3) ^ 2).trace = 4 := by decide

example : (companionMatrix (nacciCoeffs 3) ^ 3).trace = 8 := by decide

-- Past the prefix the doubling breaks by exactly `n + 1 = 4`: `A 3 4 = 2*8 - 4 = 12`, not `16`.
example : (companionMatrix (nacciCoeffs 3) ^ 4).trace = 12 := by decide

-- `nacciAugmented` is compiled by well-founded recursion, so `decide` cannot reduce it
-- directly; going through `nacciAugmented_eq_trace` makes it computable, which is itself a use
-- of the theorem.
example : nacciAugmented 3 4 = 12 := by
  rw [nacciAugmented_eq_trace 3 (by omega) 4]
  decide

/-! ### `Geometry/Spectral3x3.lean` supplies the `k = 2` case of Newton's identity

`Algebra/CompanionMatrix.lean` proves Newton's identity in the regime `k > d`, by Cayley–Hamilton,
for arbitrary coefficients — and its header records that the regime `k ≤ d` is **not** proved in
general, only for the nacci family by an explicit closed form.

`Geometry/Spectral3x3.lean` has the `k = 2` case for `3 × 3` matrices and has had it all along, as
`Matrix3.trace_mul_self : (M * M).trace = M.trace ^ 2 - 2 * minorSum M`.  It was invisible to the
absorption passes because it is filed under `Geometry`, and because it is stated for a general
`3 × 3` matrix rather than for a companion matrix.  Specialised here, it closes `k = 2` at `d = 2`
for **arbitrary** coefficients — the first instance of that regime in the library which is not
family-specific. -/

/-- The second invariant of the order-`3` companion matrix reads off the middle coefficient. -/
theorem minorSum_companionMatrix {R : Type*} [CommRing R] (c : Fin 3 → R) :
    Geometry.Matrix3.minorSum (companionMatrix c) = -c 1 := by
  simp [Geometry.Matrix3.minorSum, companionMatrix]

/-- **Newton's identity at `k = 2`, for the order-`3` companion matrix with arbitrary
coefficients**: `trace (M ^ 2) = c₂ ^ 2 + 2 c₁`.

This is the `k ≤ d` regime `CompanionMatrix.lean` does not prove in general, obtained by
specialising a theorem that was already in the library under `Geometry`. -/
theorem trace_companionMatrix_sq {R : Type*} [CommRing R] (c : Fin 3 → R) :
    ((companionMatrix c) ^ 2).trace = c 2 ^ 2 + 2 * c 1 := by
  rw [pow_two, Geometry.Matrix3.trace_mul_self, minorSum_companionMatrix,
    trace_companionMatrix]
  have h : (Fin.last 2 : Fin 3) = 2 := rfl
  rw [h]
  ring

end ClassicalLean
