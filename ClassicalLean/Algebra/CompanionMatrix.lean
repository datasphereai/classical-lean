/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.LinearRecurrence
import Mathlib.Tactic.FinCases
import ClassicalLean.Combinatorics.RecurrenceGeneratingFunction

/-!
# The companion matrix of a monic polynomial, and the traces of its powers

For coefficients `c : Fin (d+1) → R`, `companionMatrix c` is the `(d+1) × (d+1)` matrix

    M i j = [i = j + 1] + [j = last] * c i

the companion matrix of the monic polynomial `X^(d+1) - ∑_{i ≤ d} c i * X^i`.  In the column
convention this is the shift on the first `d` basis vectors together with
`M *ᵥ e_last = c`, and that is exactly how everything below is proved: nothing here computes a
characteristic polynomial or mentions a root.

## Main results

* `companionMatrix_pow_mulVec_single_zero` : `M ^ k *ᵥ e₀ = e_k` for `k ≤ d` — the shift.
* `companionMatrix_pow_last` : **Cayley–Hamilton in usable form**,
  `M ^ (d+1) = ∑ i, c i • M ^ i`.  Proved from the shift by the basis argument: the difference
  kills `e₀`, commutes with `M`, and therefore kills every `e_j = M ^ j *ᵥ e₀`.
* `trace_companionMatrix_pow_isSol` : the sequence `k ↦ (M ^ k).trace` — the **power sums** of
  the polynomial — is a solution of the Mathlib `LinearRecurrence` of order `d+1` with
  coefficients `c`.
* `trace_companionMatrix_pow_zero` (`= d + 1`) and `trace_companionMatrix` (`= c (last d)`) —
  the two values that pin the solution when `d = 1`.

Composed with `ClassicalLean/Combinatorics/RecurrenceGeneratingFunction.lean`, the power sums
therefore have a rational generating function with denominator the reversed characteristic
polynomial; that is `trace_companionMatrix_pow_gf` at the end.

## What is *not* here

Newton's identities in the regime `k ≤ d`, **in general**.  The recurrence above holds for
`k ≥ d + 1`; the values `(M ^ k).trace` for `2 ≤ k ≤ d` obey the other branch of Newton's
identities, with the extra term `k * c (d - k)`, and nothing in this file proves it for
arbitrary `c`.

What is proved, in `ClassicalLean/NumberTheory/PowerSumCases.lean`, is that regime for one
family: the coefficients of `x ^ (n+1) - 2 x ^ n + 1`.  The route is the shift lemmas below —
`companionMatrix_mulVec_apply_zero`, `_succ` and `companionMatrix_pow_mulVec_single` — which
compute `M ^ m` on the last basis vector in closed form when the intermediate coefficients
vanish.  Those lemmas are stated here, for general `c`, precisely because they are the general
part of that argument; only the closed form is family-specific.

Measured, in `.lake/packages/mathlib`:
`grep -rn 'Matrix.companion\|companionMatrix\|companion matrix' Mathlib --include=*.lean`
returns **0 hits** — Mathlib has no companion matrix at all.  `LinearRecurrence.charPoly`
(`Algebra/LinearRecurrence.lean`) gives the characteristic polynomial of a recurrence without
the matrix that realises it, and `grep -rn 'trace_pow\|powerSum' Mathlib --include=*.lean`
returns 3 hits, all `FiniteField.trace_pow_card` / `ZMod.trace_pow_card`, a Frobenius statement
(`trace (M ^ card K) = trace M ^ card K`) and not `trace (M ^ k) = p_k`.
-/

namespace ClassicalLean

open Matrix

variable {R : Type*} [CommRing R] {d : ℕ} (c : Fin (d + 1) → R)

/-- The companion matrix of `X ^ (d+1) - ∑ i, c i * X ^ i`: the subdiagonal is `1` and the last
column is `c`. -/
def companionMatrix : Matrix (Fin (d + 1)) (Fin (d + 1)) R :=
  Matrix.of fun i j =>
    (if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) + (if j = Fin.last d then c i else 0)

theorem companionMatrix_apply (i j : Fin (d + 1)) :
    companionMatrix c i j =
      (if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) + (if j = Fin.last d then c i else 0) := rfl

/-- Away from the last column the companion matrix is the shift: column `j` is `e_{j+1}`. -/
theorem companionMatrix_mulVec_single (k : ℕ) (hk : k < d) :
    companionMatrix c *ᵥ (Pi.single ⟨k, by omega⟩ 1)
      = Pi.single (⟨k + 1, by omega⟩ : Fin (d + 1)) 1 := by
  rw [mulVec_single_one]
  funext i
  have hne : (⟨k, by omega⟩ : Fin (d + 1)) ≠ Fin.last d := by
    simp [Fin.ext_iff]
    omega
  simp only [Matrix.col_apply, companionMatrix_apply, ite_eq_right hne, add_zero, Pi.single_apply]
  by_cases h : (i : ℕ) = k + 1
  · rw [ite_eq_left h, ite_eq_left (by simp [Fin.ext_iff, h])]
  · rw [ite_eq_right h, ite_eq_right (by simp [Fin.ext_iff]; omega)]

/-- The last column of the companion matrix is `c` itself. -/
theorem companionMatrix_mulVec_single_last :
    companionMatrix c *ᵥ (Pi.single (Fin.last d) 1) = c := by
  rw [mulVec_single_one]
  funext i
  have hi := i.isLt
  have hlast : (i : ℕ) ≠ d + 1 := by omega
  simp [Matrix.col_apply, companionMatrix_apply, Fin.val_last, hlast]

/-- **The shift.** `M ^ k *ᵥ e₀ = e_k` for every `k ≤ d`. -/
theorem companionMatrix_pow_mulVec_single_zero (k : ℕ) (hk : k ≤ d) :
    companionMatrix c ^ k *ᵥ (Pi.single (0 : Fin (d + 1)) 1)
      = Pi.single (⟨k, by omega⟩ : Fin (d + 1)) 1 := by
  induction k with
  | zero =>
    simp only [pow_zero, one_mulVec]
    rfl
  | succ k ih =>
    have hk' : k ≤ d := by omega
    rw [pow_succ', ← mulVec_mulVec, ih hk']
    exact companionMatrix_mulVec_single c k (by omega)

/-- **Cayley–Hamilton for the companion matrix**, in the form the recurrence needs:
`M ^ (d+1) = ∑ i, c i • M ^ i`.

The proof is the basis argument.  `M ^ (d+1) *ᵥ e₀ = M *ᵥ e_last = c = ∑ i, c i • e_i`, so the
difference `A` kills `e₀`; `A` is a polynomial in `M` and therefore commutes with `M`, so it
kills `e_j = M ^ j *ᵥ e₀` for every `j`; and a matrix killing every basis vector has every
column zero. -/
theorem companionMatrix_pow_last :
    companionMatrix c ^ (d + 1) = ∑ i, c i • companionMatrix c ^ (i : ℕ) := by
  set M := companionMatrix c with hM
  set A := M ^ (d + 1) - ∑ i, c i • M ^ (i : ℕ) with hA
  have hMA : Commute M A := by
    rw [hA]
    refine Commute.sub_right ((Commute.refl _).pow_right _) ?_
    exact Commute.sum_right _ _ _ (fun i _ => ((Commute.refl _).pow_right _).smul_right _)
  have hcomm : ∀ k : ℕ, A * M ^ k = M ^ k * A := fun k => ((hMA.pow_left k).eq).symm
  have hzero : A *ᵥ (Pi.single (0 : Fin (d + 1)) 1) = 0 := by
    have h1 : M ^ (d + 1) *ᵥ (Pi.single (0 : Fin (d + 1)) 1) = c := by
      rw [pow_succ', ← mulVec_mulVec,
        companionMatrix_pow_mulVec_single_zero c d le_rfl]
      have : (⟨d, by omega⟩ : Fin (d + 1)) = Fin.last d := rfl
      rw [this]
      exact companionMatrix_mulVec_single_last c
    have h2 : (∑ i, c i • M ^ (i : ℕ)) *ᵥ (Pi.single (0 : Fin (d + 1)) 1) = c := by
      rw [Matrix.sum_mulVec]
      have : ∀ i : Fin (d + 1),
          (c i • M ^ (i : ℕ)) *ᵥ (Pi.single (0 : Fin (d + 1)) 1)
            = c i • (Pi.single i 1 : Fin (d + 1) → R) := by
        intro i
        rw [Matrix.smul_mulVec, companionMatrix_pow_mulVec_single_zero c (i : ℕ) (by omega)]
      rw [Finset.sum_congr rfl (fun i _ => this i)]
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hA, sub_mulVec, h1, h2, sub_self]
  have hall : ∀ j : Fin (d + 1), A *ᵥ (Pi.single j 1) = 0 := by
    intro j
    have hj : (Pi.single j 1 : Fin (d + 1) → R)
        = M ^ (j : ℕ) *ᵥ (Pi.single (0 : Fin (d + 1)) 1) := by
      rw [companionMatrix_pow_mulVec_single_zero c (j : ℕ) (by omega)]
    rw [hj, mulVec_mulVec, hcomm, ← mulVec_mulVec, hzero, mulVec_zero]
  have : A = 0 := by
    ext i j
    have := congrFun (hall j) i
    rwa [mulVec_single_one, Matrix.col_apply, Pi.zero_apply] at this
  rwa [hA, sub_eq_zero] at this

/-! ### The action on a general vector -/

/-- The companion matrix at row `0`: only the last column contributes, since row `0` has no
subdiagonal entry. -/
theorem companionMatrix_mulVec_apply_zero (v : Fin (d + 1) → R) :
    (companionMatrix c *ᵥ v) 0 = c 0 * v (Fin.last d) := by
  simp only [Matrix.mulVec, dotProduct, companionMatrix_apply, add_mul]
  rw [Finset.sum_add_distrib]
  have h0 : ∀ j : Fin (d + 1),
      (if ((0 : Fin (d + 1)) : ℕ) = (j : ℕ) + 1 then (1 : R) else 0) * v j = 0 := by
    intro j
    rw [ite_eq_right (by simp)]
    ring
  have h1 : ∀ j : Fin (d + 1),
      (if j = Fin.last d then c 0 else 0) * v j
        = if j = Fin.last d then c 0 * v (Fin.last d) else 0 := by
    intro j
    split_ifs with h
    · rw [h]
    · ring
  rw [Finset.sum_congr rfl (fun j _ => h0 j), Finset.sum_congr rfl (fun j _ => h1 j)]
  simp

/-- The companion matrix at a row below the first: the subdiagonal shifts, and the last column
adds `c i` times the last coordinate. -/
theorem companionMatrix_mulVec_apply_succ (v : Fin (d + 1) → R) (p : ℕ) (hp : p + 1 < d + 1) :
    (companionMatrix c *ᵥ v) ⟨p + 1, hp⟩
      = v ⟨p, by omega⟩ + c ⟨p + 1, hp⟩ * v (Fin.last d) := by
  simp only [Matrix.mulVec, dotProduct, companionMatrix_apply, add_mul]
  rw [Finset.sum_add_distrib]
  have h0 : ∀ j : Fin (d + 1),
      (if ((⟨p + 1, hp⟩ : Fin (d + 1)) : ℕ) = (j : ℕ) + 1 then (1 : R) else 0) * v j
        = if j = (⟨p, by omega⟩ : Fin (d + 1)) then v ⟨p, by omega⟩ else 0 := by
    intro j
    by_cases h : (j : ℕ) = p
    · rw [ite_eq_left (by simpa using h.symm), ite_eq_left (by simp [Fin.ext_iff, h])]
      have : j = (⟨p, by omega⟩ : Fin (d + 1)) := by simp [Fin.ext_iff, h]
      rw [this]
      ring
    · rw [ite_eq_right (by simpa using fun hh => h (by omega)),
        ite_eq_right (by simp [Fin.ext_iff, h])]
      ring
  have h1 : ∀ j : Fin (d + 1),
      (if j = Fin.last d then c ⟨p + 1, hp⟩ else 0) * v j
        = if j = Fin.last d then c ⟨p + 1, hp⟩ * v (Fin.last d) else 0 := by
    intro j
    split_ifs with h
    · rw [h]
    · ring
  rw [Finset.sum_congr rfl (fun j _ => h0 j), Finset.sum_congr rfl (fun j _ => h1 j)]
  simp

/-- `M ^ k *ᵥ eⱼ = e_{j+k}` whenever the shift does not wrap.  This is
`companionMatrix_pow_mulVec_single_zero` transported along `eⱼ = M ^ j *ᵥ e₀`. -/
theorem companionMatrix_pow_mulVec_single (j k : ℕ) (h : j + k ≤ d) :
    companionMatrix c ^ k *ᵥ (Pi.single (⟨j, by omega⟩ : Fin (d + 1)) 1)
      = Pi.single (⟨j + k, by omega⟩ : Fin (d + 1)) 1 := by
  rw [← companionMatrix_pow_mulVec_single_zero c j (by omega), mulVec_mulVec, ← pow_add,
    Nat.add_comm k j]
  exact companionMatrix_pow_mulVec_single_zero c (j + k) (by omega)

/-- The trace, read off the columns: `trace A = ∑ j, (A *ᵥ eⱼ) j`. -/
theorem trace_eq_sum_mulVec_single (A : Matrix (Fin (d + 1)) (Fin (d + 1)) R) :
    A.trace = ∑ j, (A *ᵥ (Pi.single j 1)) j := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [mulVec_single_one, Matrix.col_apply, Matrix.diag_apply]

/-! ### The traces of the powers: the power sums -/

/-- The linear recurrence realised by the companion matrix: order `d + 1`, coefficients `c`. -/
def companionRec : LinearRecurrence R where
  order := d + 1
  coeffs := c

@[simp] theorem companionRec_order : (companionRec c).order = d + 1 := rfl

/-- `trace (M ^ 0) = d + 1`, the degree of the polynomial.  This is `p₀`: the number of roots,
counted with multiplicity, without any root being named. -/
@[simp] theorem trace_companionMatrix_pow_zero :
    (companionMatrix c ^ 0).trace = ((d : R) + 1) := by
  rw [pow_zero, Matrix.trace_one]
  simp

/-- `trace M = c (last d)`, which is `p₁`: the sum of the roots, i.e. the negated
subleading coefficient.  The subdiagonal contributes nothing to the diagonal. -/
@[simp] theorem trace_companionMatrix : (companionMatrix c).trace = c (Fin.last d) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, companionMatrix_apply]
  have h : ∀ i : Fin (d + 1), (if (i : ℕ) = (i : ℕ) + 1 then (1 : R) else 0) = 0 := by
    intro i
    rw [ite_eq_right (by omega)]
  simp only [h, zero_add]
  exact Finset.sum_ite_eq' Finset.univ (Fin.last d) c ▸ by simp

/-- **The power sums solve the recurrence.**  `k ↦ trace (M ^ k)` is a solution of
`companionRec c`, i.e. `p_{k+d+1} = ∑ i, c i * p_{k+i}` for every `k`.

This is `companionMatrix_pow_last` under the linearity of the trace, and it is Newton's identity
in the regime `k > d` — the regime that needs no correction term.  It says nothing about
`p_k` for `k ≤ d`; see the module header. -/
theorem trace_companionMatrix_pow_isSol :
    (companionRec c).IsSolution (fun k => (companionMatrix c ^ k).trace) := by
  intro n
  simp only [companionRec]
  rw [pow_add, companionMatrix_pow_last, Finset.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_smul_comm, Matrix.trace_smul, ← pow_add, smul_eq_mul]

/-- **The power sums have a rational generating function**, with denominator the reversed
characteristic polynomial and a numerator of degree less than `d + 1`.

This is `ClassicalLean/Combinatorics/RecurrenceGeneratingFunction.lean`'s `exists_poly_mk_eq`
fed with `trace_companionMatrix_pow_isSol`; no new work, which is the point of having built the
generating-function layer first. -/
theorem exists_poly_mk_trace_companionMatrix_pow :
    ∃ p : Polynomial R, (∀ m, d + 1 ≤ m → p.coeff m = 0) ∧
      PowerSeries.mk (fun k => (companionMatrix c ^ k).trace)
        = (p : PowerSeries R) * PowerSeries.invOfUnit (recDenom (companionRec c)) 1 :=
  exists_poly_mk_eq (companionRec c) _ (trace_companionMatrix_pow_isSol c)

/-! ### Spot checks -/

-- The `d = 1` companion matrix of `t² - P t + Q` is `!![0, -Q; 1, P]`, the matrix
-- `ClassicalLean/Geometry/Helix.lean` builds by hand.
example (P Q : ℤ) : companionMatrix ![-Q, P] = !![0, -Q; 1, P] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [companionMatrix_apply, Fin.last]

-- `trace (M ^ 0) = 2` and `trace M = P` at `d = 1`: the two values that pin a second-order
-- solution.
example (P Q : ℤ) : (companionMatrix ![-Q, P] ^ 0).trace = 2 := by
  rw [trace_companionMatrix_pow_zero]
  norm_num

example (P Q : ℤ) : (companionMatrix ![-Q, P]).trace = P := by
  rw [trace_companionMatrix]
  rfl

-- A `d = 3` numeric check that the recurrence really is Newton's: for `c = ![3, -1, 2, 5]`,
-- `p₄ = 5 p₃ + 2 p₂ - p₁ + 3 p₀ = 5*152 + 2*29 - 5 + 3*4 = 825`.
example : (companionMatrix (![3, -1, 2, 5] : Fin 4 → ℤ) ^ 4).trace = 825 := by decide

example : (companionMatrix (![3, -1, 2, 5] : Fin 4 → ℤ) ^ 3).trace = 152 := by decide

end ClassicalLean
