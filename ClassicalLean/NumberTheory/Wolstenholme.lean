/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.NumberTheory.Catalan
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Wolstenholme's theorem

Order G-10 J2. Statements reviewed cold (ACCEPT, `reviews/stmt-j2.md`). All seven proved, no
`sorry`: `sum_inv_sq_eq_zero` (W7), `sum_inv_mul_sub_eq_zero` (W6),
`choose_two_mul_sub_one_modEq_one` (W2, the classical binomial form), `choose_two_mul_modEq_two`
(W3), `centralBinom_modEq_two` (W4), `catalan_prime_modEq` (W5), `two_le_padicValRat_harmonic`
(W1, the harmonic form). Theorems are in dependency order, reordered from the reviewed skeleton's
W1…W7 (rule 18). A private helper `prod_one_add_of_mul_eq_zero` supports the `ZMod (p³)` pairing.

See the reviewed statement skeleton for the full docstring, the route sketch (§0 row 8), the Mathlib
searches (§0 row 12), the prior-art note (none) and the correction to order G-9 §0 row 12.
-/

open Finset

namespace ClassicalLean

/-- Helper: in a commutative ring, `∏ (1 + xᵢ) = 1 + ∑ xᵢ` when every pairwise product of the `xᵢ`
vanishes (so all higher terms in the expansion drop out). -/
private theorem prod_one_add_of_mul_eq_zero {R : Type*} [CommRing R] {ι : Type*}
    {s : Finset ι} {x : ι → R} (h : ∀ i ∈ s, ∀ j ∈ s, x i * x j = 0) :
    ∏ i ∈ s, (1 + x i) = 1 + ∑ i ∈ s, x i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ih (fun i hi j hj => h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))]
    have hz : x a * (∑ i ∈ s, x i) = 0 := by
      rw [mul_sum]
      exact Finset.sum_eq_zero fun j hj =>
        h a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj)
    have hexp : (1 + x a) * (1 + ∑ i ∈ s, x i)
        = 1 + (x a + ∑ i ∈ s, x i) + x a * (∑ i ∈ s, x i) := by ring
    rw [hexp, hz, add_zero]

/-- The sum of inverse squares of the nonzero residues vanishes for `p ≥ 5`. -/
theorem sum_inv_sq_eq_zero (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) :
    ∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p) ^ 2)⁻¹ = 0 := by
  have hpz : NeZero p := ⟨by omega⟩
  have hne : ∀ i ∈ Finset.Icc 1 (p - 1), (i : ZMod p) ≠ 0 := by
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have key : ∀ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p) ^ 2)⁻¹ = (i : ZMod p) ^ (p - 3) := by
    intro i hi
    have hfermat : (i : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one (hne i hi)
    have hsplit : (i : ZMod p) ^ (p - 3) * (i : ZMod p) ^ 2 = 1 := by
      rw [← pow_add, show p - 3 + 2 = p - 1 by omega, hfermat]
    exact inv_eq_of_mul_eq_one_left hsplit
  rw [Finset.sum_congr rfl key]
  have hsum0 : ∑ x : ZMod p, x ^ (p - 3) = 0 := by
    apply FiniteField.sum_pow_lt_card_sub_one
    rw [ZMod.card]; omega
  have reindex : ∑ i ∈ Finset.Icc 1 (p - 1), (i : ZMod p) ^ (p - 3)
      = ∑ x ∈ (Finset.univ.erase (0 : ZMod p)), x ^ (p - 3) := by
    refine Finset.sum_nbij' (fun i => (i : ZMod p)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
    · intro i hi; exact Finset.mem_erase.mpr ⟨hne i hi, Finset.mem_univ _⟩
    · intro x hx
      have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
      have hlt : x.val < p := ZMod.val_lt x
      have hv0 : x.val ≠ 0 := by
        intro h
        have hr := ZMod.natCast_rightInverse (n := p) x
        rw [h, Nat.cast_zero] at hr
        exact hx0 hr.symm
      exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hv0, by omega⟩
    · intro i hi; exact ZMod.val_cast_of_lt (by have := Finset.mem_Icc.mp hi; omega)
    · intro x _; exact ZMod.natCast_rightInverse x
    · intro i _; rfl
  have erase_eq : ∑ x ∈ (Finset.univ.erase (0 : ZMod p)), x ^ (p - 3)
      = ∑ x : ZMod p, x ^ (p - 3) := by
    apply Finset.sum_subset (Finset.erase_subset _ _)
    intro x _ hx
    have hx0 : x = 0 := by
      by_contra hne'
      exact hx (Finset.mem_erase.mpr ⟨hne', Finset.mem_univ _⟩)
    rw [hx0, zero_pow (by omega)]
  rw [reindex, erase_eq, hsum0]

/-- The half sum behind both forms: in `ZMod p`, `∑_{i=1}^{(p-1)/2} (i (p − i))⁻¹ = 0` for a prime
`p ≥ 5`. -/
theorem sum_inv_mul_sub_eq_zero (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) :
    ∑ i ∈ Finset.Icc 1 ((p - 1) / 2), ((i : ZMod p) * ((p : ZMod p) - i))⁻¹ = 0 := by
  have hpz : NeZero p := ⟨by omega⟩
  have hp : p.Prime := Fact.out
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two hp (by omega))
  set m := (p - 1) / 2 with hm
  have hunion : Finset.Icc 1 (p - 1) = Finset.Icc 1 m ∪ Finset.Icc (m + 1) (p - 1) := by
    ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc 1 m) (Finset.Icc (m + 1) (p - 1)) := by
    rw [Finset.disjoint_left]; intro x hx hx'
    simp only [Finset.mem_Icc] at hx hx'; omega
  have hreflect : ∑ i ∈ Finset.Icc (m + 1) (p - 1), ((i : ZMod p) ^ 2)⁻¹
      = ∑ i ∈ Finset.Icc 1 m, ((i : ZMod p) ^ 2)⁻¹ := by
    refine Finset.sum_nbij' (fun i => p - i) (fun j => p - j) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_Icc] at hi ⊢; omega
    · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
    · intro i hi; simp only [Finset.mem_Icc] at hi; exact Nat.sub_sub_self (by omega)
    · intro j hj; simp only [Finset.mem_Icc] at hj; exact Nat.sub_sub_self (by omega)
    · intro i hi
      simp only [Finset.mem_Icc] at hi
      show ((i : ZMod p) ^ 2)⁻¹ = (((p - i : ℕ) : ZMod p) ^ 2)⁻¹
      have hle : i ≤ p := by omega
      rw [Nat.cast_sub hle, ZMod.natCast_self, zero_sub, neg_sq]
  have hhalf : ∑ i ∈ Finset.Icc 1 m, ((i : ZMod p) ^ 2)⁻¹ = 0 := by
    have hw := sum_inv_sq_eq_zero p h5
    rw [hunion, Finset.sum_union hdisj, hreflect, ← two_mul] at hw
    have h2 : (2 : ZMod p) ≠ 0 := by
      have : ((2 : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
      simpa using this
    exact (mul_eq_zero.mp hw).resolve_left h2
  have step : ∀ i ∈ Finset.Icc 1 m,
      ((i : ZMod p) * ((p : ZMod p) - i))⁻¹ = -((i : ZMod p) ^ 2)⁻¹ := by
    intro i _; rw [ZMod.natCast_self, zero_sub, mul_neg, ← pow_two, inv_neg]
  rw [Finset.sum_congr rfl step, Finset.sum_neg_distrib, hhalf, neg_zero]

/-- **Wolstenholme's theorem, the binomial form**: `C(2p − 1, p − 1) ≡ 1 (mod p ^ 3)` for a prime
`p ≥ 5`. -/
theorem choose_two_mul_sub_one_modEq_one (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) :
    (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3] := by
  have hp : p.Prime := Fact.out
  have w6 := sum_inv_mul_sub_eq_zero p h5
  have hp3 : NeZero (p ^ 3) := ⟨pow_ne_zero 3 (by omega)⟩
  have hpz : NeZero p := ⟨by omega⟩
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two hp (by omega))
  set m := (p - 1) / 2 with hm
  have hnat : Nat.factorial (p - 1) * (2 * p - 1).choose (p - 1)
      = ∏ j ∈ Finset.Icc 1 (p - 1), (p + j) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range]
    refine Finset.prod_nbij' (fun i => p - 1 - i) (fun j => p - 1 - j) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_range] at hi; simp only [Finset.mem_Icc]; omega
    · intro j hj; simp only [Finset.mem_Icc] at hj; simp only [Finset.mem_range]; omega
    · intro i hi; simp only [Finset.mem_range] at hi; exact Nat.sub_sub_self (by omega)
    · intro j hj; simp only [Finset.mem_Icc] at hj; exact Nat.sub_sub_self (by omega)
    · intro i hi; simp only [Finset.mem_range] at hi
      show 2 * p - 1 - i = p + (p - 1 - i); omega
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_one]
  have hjunit : ∀ j ∈ Finset.Icc 1 (p - 1), IsUnit ((j : ℕ) : ZMod (p ^ 3)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [ZMod.isUnit_iff_coprime]
    have hjp : ¬ p ∣ j := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
    exact (((Nat.Prime.coprime_iff_not_dvd hp).mpr hjp).symm).pow_right 3
  have hfacunit : IsUnit ((Nat.factorial (p - 1) : ℕ) : ZMod (p ^ 3)) := by
    rw [ZMod.isUnit_iff_coprime]
    have hfp : ¬ p ∣ Nat.factorial (p - 1) := by
      rw [Nat.Prime.dvd_factorial hp]; omega
    exact (((Nat.Prime.coprime_iff_not_dvd hp).mpr hfp).symm).pow_right 3
  have hfactnat : ∏ j ∈ Finset.Icc 1 (p - 1), j = Nat.factorial (p - 1) := by
    rw [← Finset.prod_range_add_one_eq_factorial]
    refine Finset.prod_nbij' (fun j => j - 1) (fun i => i + 1) ?_ ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_Icc] at hj; simp only [Finset.mem_range]; omega
    · intro i hi; simp only [Finset.mem_range] at hi; simp only [Finset.mem_Icc]; omega
    · intro j hj; simp only [Finset.mem_Icc] at hj; omega
    · intro i hi; simp only [Finset.mem_range] at hi; omega
    · intro j hj; simp only [Finset.mem_Icc] at hj; omega
  have hfact : ((Nat.factorial (p - 1) : ℕ) : ZMod (p ^ 3))
      = ∏ j ∈ Finset.Icc 1 (p - 1), (j : ZMod (p ^ 3)) := by
    rw [← hfactnat, Nat.cast_prod]
  have hprodfactor : ∏ j ∈ Finset.Icc 1 (p - 1), ((p : ZMod (p ^ 3)) + (j : ZMod (p ^ 3)))
      = ((Nat.factorial (p - 1) : ℕ) : ZMod (p ^ 3))
        * ∏ j ∈ Finset.Icc 1 (p - 1), (1 + (p : ZMod (p ^ 3)) * ((j : ℕ) : ZMod (p ^ 3))⁻¹) := by
    rw [hfact, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    have hu : ((j : ℕ) : ZMod (p ^ 3)) * ((j : ℕ) : ZMod (p ^ 3))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ (hjunit j hj)
    have hexp : ((j : ℕ) : ZMod (p ^ 3)) * (1 + (p : ZMod (p ^ 3)) * ((j : ℕ) : ZMod (p ^ 3))⁻¹)
        = ((j : ℕ) : ZMod (p ^ 3)) + (p : ZMod (p ^ 3))
          * (((j : ℕ) : ZMod (p ^ 3)) * ((j : ℕ) : ZMod (p ^ 3))⁻¹) := by ring
    rw [hexp, hu, mul_one, add_comm]
  have hcast : ((Nat.factorial (p - 1) : ℕ) : ZMod (p ^ 3))
      * (((2 * p - 1).choose (p - 1) : ℕ) : ZMod (p ^ 3))
      = ∏ j ∈ Finset.Icc 1 (p - 1), ((p : ZMod (p ^ 3)) + (j : ZMod (p ^ 3))) := by
    have h : ((Nat.factorial (p - 1) * (2 * p - 1).choose (p - 1) : ℕ) : ZMod (p ^ 3))
        = ((∏ j ∈ Finset.Icc 1 (p - 1), (p + j) : ℕ) : ZMod (p ^ 3)) := by rw [hnat]
    push_cast at h
    exact h
  have hC : (((2 * p - 1).choose (p - 1) : ℕ) : ZMod (p ^ 3))
      = ∏ j ∈ Finset.Icc 1 (p - 1), (1 + (p : ZMod (p ^ 3)) * ((j : ℕ) : ZMod (p ^ 3))⁻¹) := by
    have := hcast
    rw [hprodfactor] at this
    exact hfacunit.mul_left_cancel this
  rw [hC]
  have hp30 : (p : ZMod (p ^ 3)) ^ 3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hp40 : (p : ZMod (p ^ 3)) ^ 4 = 0 := by
    have e : (p : ZMod (p ^ 3)) ^ 4 = (p : ZMod (p ^ 3)) ^ 3 * (p : ZMod (p ^ 3)) := by ring
    rw [e, hp30, zero_mul]
  have hunion : Finset.Icc 1 (p - 1) = Finset.Icc 1 m ∪ Finset.Icc (m + 1) (p - 1) := by
    ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc 1 m) (Finset.Icc (m + 1) (p - 1)) := by
    rw [Finset.disjoint_left]; intro x hx hx'
    simp only [Finset.mem_Icc] at hx hx'; omega
  have hreflect : ∏ j ∈ Finset.Icc (m + 1) (p - 1),
        (1 + (p : ZMod (p ^ 3)) * ((j : ℕ) : ZMod (p ^ 3))⁻¹)
      = ∏ k ∈ Finset.Icc 1 m, (1 + (p : ZMod (p ^ 3)) * (((p - k) : ℕ) : ZMod (p ^ 3))⁻¹) := by
    refine (Finset.prod_nbij' (fun k => p - k) (fun j => p - j) ?_ ?_ ?_ ?_ ?_).symm
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
    · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk; exact Nat.sub_sub_self (by omega)
    · intro j hj; simp only [Finset.mem_Icc] at hj; exact Nat.sub_sub_self (by omega)
    · intro k _; rfl
  have hpair : ∀ k ∈ Finset.Icc 1 m,
      (1 + (p : ZMod (p ^ 3)) * ((k : ℕ) : ZMod (p ^ 3))⁻¹)
        * (1 + (p : ZMod (p ^ 3)) * (((p - k) : ℕ) : ZMod (p ^ 3))⁻¹)
      = 1 + 2 * (p : ZMod (p ^ 3)) ^ 2
          * (((k : ℕ) : ZMod (p ^ 3))⁻¹ * (((p - k) : ℕ) : ZMod (p ^ 3))⁻¹) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hku : IsUnit ((k : ℕ) : ZMod (p ^ 3)) := hjunit k (by simp only [Finset.mem_Icc]; omega)
    have hpku : IsUnit (((p - k) : ℕ) : ZMod (p ^ 3)) :=
      hjunit (p - k) (by simp only [Finset.mem_Icc]; omega)
    have huu : ((k : ℕ) : ZMod (p ^ 3)) * ((k : ℕ) : ZMod (p ^ 3))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ hku
    have hvv : (((p - k) : ℕ) : ZMod (p ^ 3)) * (((p - k) : ℕ) : ZMod (p ^ 3))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ hpku
    have huv : ((k : ℕ) : ZMod (p ^ 3)) + (((p - k) : ℕ) : ZMod (p ^ 3)) = (p : ZMod (p ^ 3)) := by
      rw [← Nat.cast_add, Nat.add_sub_cancel' (by omega)]
    have hab : ((k : ℕ) : ZMod (p ^ 3))⁻¹ + (((p - k) : ℕ) : ZMod (p ^ 3))⁻¹
        = (p : ZMod (p ^ 3)) * (((k : ℕ) : ZMod (p ^ 3))⁻¹ * (((p - k) : ℕ) : ZMod (p ^ 3))⁻¹) := by
      rw [← huv]
      have e : (((k : ℕ) : ZMod (p ^ 3)) + (((p - k) : ℕ) : ZMod (p ^ 3)))
            * (((k : ℕ) : ZMod (p ^ 3))⁻¹ * (((p - k) : ℕ) : ZMod (p ^ 3))⁻¹)
          = (((k : ℕ) : ZMod (p ^ 3)) * ((k : ℕ) : ZMod (p ^ 3))⁻¹)
              * (((p - k) : ℕ) : ZMod (p ^ 3))⁻¹
            + (((p - k) : ℕ) : ZMod (p ^ 3)) * (((p - k) : ℕ) : ZMod (p ^ 3))⁻¹
              * ((k : ℕ) : ZMod (p ^ 3))⁻¹ := by
        ring
      rw [e, huu, hvv, one_mul, one_mul, add_comm]
    have expand : (1 + (p : ZMod (p ^ 3)) * ((k : ℕ) : ZMod (p ^ 3))⁻¹)
          * (1 + (p : ZMod (p ^ 3)) * (((p - k) : ℕ) : ZMod (p ^ 3))⁻¹)
        = 1 + (p : ZMod (p ^ 3)) * (((k : ℕ) : ZMod (p ^ 3))⁻¹ + (((p - k) : ℕ) : ZMod (p ^ 3))⁻¹)
          + (p : ZMod (p ^ 3)) ^ 2
            * (((k : ℕ) : ZMod (p ^ 3))⁻¹ * (((p - k) : ℕ) : ZMod (p ^ 3))⁻¹) := by
      ring
    rw [expand, hab]; ring
  rw [hunion, Finset.prod_union hdisj, hreflect, ← Finset.prod_mul_distrib,
    Finset.prod_congr rfl hpair]
  have hXzero : ∀ i ∈ Finset.Icc 1 m, ∀ j ∈ Finset.Icc 1 m,
      (2 * (p : ZMod (p ^ 3)) ^ 2
          * (((i : ℕ) : ZMod (p ^ 3))⁻¹ * (((p - i) : ℕ) : ZMod (p ^ 3))⁻¹))
        * (2 * (p : ZMod (p ^ 3)) ^ 2
            * (((j : ℕ) : ZMod (p ^ 3))⁻¹ * (((p - j) : ℕ) : ZMod (p ^ 3))⁻¹)) = 0 := by
    intro i _ j _
    have e : (2 * (p : ZMod (p ^ 3)) ^ 2
            * (((i : ℕ) : ZMod (p ^ 3))⁻¹ * (((p - i) : ℕ) : ZMod (p ^ 3))⁻¹))
          * (2 * (p : ZMod (p ^ 3)) ^ 2
              * (((j : ℕ) : ZMod (p ^ 3))⁻¹ * (((p - j) : ℕ) : ZMod (p ^ 3))⁻¹))
        = (p : ZMod (p ^ 3)) ^ 4
            * (4 * (((i : ℕ) : ZMod (p ^ 3))⁻¹ * (((p - i) : ℕ) : ZMod (p ^ 3))⁻¹
                * (((j : ℕ) : ZMod (p ^ 3))⁻¹ * (((p - j) : ℕ) : ZMod (p ^ 3))⁻¹))) := by ring
    rw [e, hp40, zero_mul]
  rw [prod_one_add_of_mul_eq_zero hXzero]
  set S := ∑ k ∈ Finset.Icc 1 m,
    (((k : ℕ) : ZMod (p ^ 3))⁻¹ * (((p - k) : ℕ) : ZMod (p ^ 3))⁻¹) with hSdef
  have hXsum : ∑ k ∈ Finset.Icc 1 m,
      (2 * (p : ZMod (p ^ 3)) ^ 2 * (((k : ℕ) : ZMod (p ^ 3))⁻¹ * (((p - k) : ℕ) : ZMod (p ^ 3))⁻¹))
      = 2 * (p : ZMod (p ^ 3)) ^ 2 * S := by
    rw [hSdef, Finset.mul_sum]
  rw [hXsum]
  have hpp3 : p ∣ p ^ 3 := dvd_pow_self p (by norm_num)
  have hinv : ∀ x : ZMod (p ^ 3), IsUnit x →
      (ZMod.castHom hpp3 (ZMod p)) x⁻¹ = ((ZMod.castHom hpp3 (ZMod p)) x)⁻¹ := by
    intro x hx
    have h1 : (ZMod.castHom hpp3 (ZMod p)) x⁻¹ * (ZMod.castHom hpp3 (ZMod p)) x = 1 := by
      rw [← map_mul, mul_comm, ZMod.mul_inv_of_unit x hx, map_one]
    exact (inv_eq_of_mul_eq_one_left h1).symm
  have hφS : (ZMod.castHom hpp3 (ZMod p)) S = 0 := by
    rw [hSdef, map_sum, ← w6]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hku : IsUnit ((k : ℕ) : ZMod (p ^ 3)) := hjunit k (by simp only [Finset.mem_Icc]; omega)
    have hpku : IsUnit (((p - k) : ℕ) : ZMod (p ^ 3)) :=
      hjunit (p - k) (by simp only [Finset.mem_Icc]; omega)
    rw [map_mul, hinv _ hku, hinv _ hpku, map_natCast, map_natCast, ← mul_inv,
      Nat.cast_sub (by omega)]
  have hval : p ∣ S.val := by
    have hφval : (ZMod.castHom hpp3 (ZMod p)) S = ((S.val : ℕ) : ZMod p) := by
      have hr : ((S.val : ℕ) : ZMod (p ^ 3)) = S := ZMod.natCast_rightInverse S
      calc (ZMod.castHom hpp3 (ZMod p)) S
          = (ZMod.castHom hpp3 (ZMod p)) ((S.val : ℕ) : ZMod (p ^ 3)) := by rw [hr]
        _ = ((S.val : ℕ) : ZMod p) := map_natCast _ _
    exact (ZMod.natCast_eq_zero_iff _ _).mp (hφval.symm.trans hφS)
  obtain ⟨t, ht⟩ := hval
  have hSeq : S = (p : ZMod (p ^ 3)) * (t : ZMod (p ^ 3)) := by
    calc S = ((S.val : ℕ) : ZMod (p ^ 3)) := (ZMod.natCast_rightInverse S).symm
      _ = ((p * t : ℕ) : ZMod (p ^ 3)) := by rw [ht]
      _ = (p : ZMod (p ^ 3)) * (t : ZMod (p ^ 3)) := by push_cast; ring
  have hSred : 2 * (p : ZMod (p ^ 3)) ^ 2 * S = 0 := by
    rw [hSeq]
    have e : 2 * (p : ZMod (p ^ 3)) ^ 2 * ((p : ZMod (p ^ 3)) * (t : ZMod (p ^ 3)))
        = 2 * (t : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) ^ 3 := by ring
    rw [e, hp30, mul_zero]
  rw [hSred, add_zero]

/-- The central form: `C(2p, p) ≡ 2 (mod p ^ 3)`. -/
theorem choose_two_mul_modEq_two (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) :
    (2 * p).choose p ≡ 2 [MOD p ^ 3] := by
  have h1 : (2 * p).choose p = (2 * p - 1).choose (p - 1) + (2 * p - 1).choose p := by
    have := Nat.choose_succ_succ' (2 * p - 1) (p - 1)
    rwa [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)] at this
  have h2 : (2 * p - 1).choose p = (2 * p - 1).choose (p - 1) := by
    rw [← Nat.choose_symm (by omega : p ≤ 2 * p - 1)]; congr 1; omega
  have hident : (2 * p).choose p = 2 * (2 * p - 1).choose (p - 1) := by rw [h1, h2]; ring
  rw [hident]
  have h2' := (choose_two_mul_sub_one_modEq_one p h5).mul_left 2
  rwa [mul_one] at h2'

/-- The same for Mathlib's `Nat.centralBinom`. -/
theorem centralBinom_modEq_two (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) :
    p.centralBinom ≡ 2 [MOD p ^ 3] :=
  choose_two_mul_modEq_two p h5

/-- The Catalan number at a prime `p ≥ 5`: `catalan p ≡ 2 + 2p ^ 2 − 2p (mod p ^ 3)`, from
`(p + 1) · catalan p = C(2p, p)` and `(p + 1)(1 − p + p ^ 2) ≡ 1 (mod p ^ 3)`. -/
theorem catalan_prime_modEq (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) :
    catalan p ≡ 2 + 2 * p ^ 2 - 2 * p [MOD p ^ 3] := by
  have hcat : (p + 1) * catalan p = (2 * p).choose p := succ_mul_catalan_eq_choose p
  have hlhs : (p + 1) * catalan p ≡ 2 [MOD p ^ 3] := hcat ▸ choose_two_mul_modEq_two p h5
  have hle : 2 * p ≤ 2 + 2 * p ^ 2 := by nlinarith [sq_nonneg p, Nat.zero_le p]
  have hprod : (p + 1) * (2 + 2 * p ^ 2 - 2 * p) = 2 * p ^ 3 + 2 := by zify [hle]; ring
  have hrhs : (p + 1) * (2 + 2 * p ^ 2 - 2 * p) ≡ 2 [MOD p ^ 3] := by
    rw [hprod]
    have : 2 * p ^ 3 + 2 ≡ 0 + 2 [MOD p ^ 3] :=
      Nat.ModEq.add_right 2 ((Nat.modEq_zero_iff_dvd).mpr ⟨2, by ring⟩)
    rwa [zero_add] at this
  have hpp1 : Nat.Coprime p (p + 1) := by
    unfold Nat.Coprime
    rw [show p + 1 = 1 + 1 * p by ring, Nat.gcd_add_mul_right_right, Nat.gcd_one_right]
  have hcop : Nat.Coprime (p ^ 3) (p + 1) := hpp1.pow_left 3
  exact Nat.ModEq.cancel_left_of_coprime hcop (hlhs.trans hrhs.symm)

/-- **Wolstenholme's theorem, the harmonic form**: for a prime `p ≥ 5`, `p ^ 2` divides the
numerator of `H_{p - 1} = 1 + 1/2 + ⋯ + 1/(p - 1)`, stated with the `p`-adic valuation. -/
theorem two_le_padicValRat_harmonic (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) :
    2 ≤ padicValRat p (harmonic (p - 1)) := by
  have hp : p.Prime := Fact.out
  have hpz : NeZero p := ⟨by omega⟩
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two hp (by omega))
  have w6 := sum_inv_mul_sub_eq_zero p h5
  set m := (p - 1) / 2 with hm
  set fac := Nat.factorial (p - 1) with hfacdef
  have hcrux : p ^ 2 ∣ ∑ k ∈ Finset.Icc 1 (p - 1), fac / k := by
    have hfactnat : ∏ j ∈ Finset.Icc 1 (p - 1), j = fac := by
      rw [hfacdef, ← Finset.prod_range_add_one_eq_factorial]
      refine Finset.prod_nbij' (fun j => j - 1) (fun i => i + 1) ?_ ?_ ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_Icc] at hj; simp only [Finset.mem_range]; omega
      · intro i hi; simp only [Finset.mem_range] at hi; simp only [Finset.mem_Icc]; omega
      · intro j hj; simp only [Finset.mem_Icc] at hj; omega
      · intro i hi; simp only [Finset.mem_range] at hi; omega
      · intro j hj; simp only [Finset.mem_Icc] at hj; omega
    have hddvd : ∀ k ∈ Finset.Icc 1 m, k * (p - k) ∣ fac := by
      intro k hk
      simp only [Finset.mem_Icc] at hk
      have hsub : ({k, p - k} : Finset ℕ) ⊆ Finset.Icc 1 (p - 1) := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_Icc]; rcases hx with h | h <;> omega
      have hne : k ≠ p - k := by omega
      have := Finset.prod_dvd_prod_of_subset _ _ (fun j => j) hsub
      rwa [Finset.prod_pair hne, hfactnat] at this
    have hpair : ∀ k ∈ Finset.Icc 1 m, fac / k + fac / (p - k) = p * (fac / (k * (p - k))) := by
      intro k hk
      simp only [Finset.mem_Icc] at hk
      have hd := hddvd k (by simp only [Finset.mem_Icc]; omega)
      have hc : fac = (fac / (k * (p - k))) * (k * (p - k)) := (Nat.div_mul_cancel hd).symm
      have e1 : fac / k = (fac / (k * (p - k))) * (p - k) := by
        apply Nat.div_eq_of_eq_mul_left (by omega); exact hc.trans (by ring)
      have e2 : fac / (p - k) = (fac / (k * (p - k))) * k := by
        apply Nat.div_eq_of_eq_mul_left (by omega); exact hc.trans (by ring)
      rw [e1, e2, ← mul_add, Nat.sub_add_cancel (by omega), mul_comm]
    have hunion : Finset.Icc 1 (p - 1) = Finset.Icc 1 m ∪ Finset.Icc (m + 1) (p - 1) := by
      ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    have hdisj : Disjoint (Finset.Icc 1 m) (Finset.Icc (m + 1) (p - 1)) := by
      rw [Finset.disjoint_left]; intro x hx hx'; simp only [Finset.mem_Icc] at hx hx'; omega
    have hreflect : ∑ k ∈ Finset.Icc (m + 1) (p - 1), fac / k
        = ∑ k ∈ Finset.Icc 1 m, fac / (p - k) := by
      refine Finset.sum_nbij' (fun k => p - k) (fun j => p - j) ?_ ?_ ?_ ?_ ?_
      · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
      · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
      · intro k hk; simp only [Finset.mem_Icc] at hk; exact Nat.sub_sub_self (by omega)
      · intro j hj; simp only [Finset.mem_Icc] at hj; exact Nat.sub_sub_self (by omega)
      · intro k hk; simp only [Finset.mem_Icc] at hk; rw [Nat.sub_sub_self (by omega)]
    have hAeq : ∑ k ∈ Finset.Icc 1 (p - 1), fac / k
        = ∑ k ∈ Finset.Icc 1 m, (fac / k + fac / (p - k)) := by
      rw [hunion, Finset.sum_union hdisj, hreflect, ← Finset.sum_add_distrib]
    rw [hAeq, Finset.sum_congr rfl hpair, ← Finset.mul_sum]
    set B := ∑ k ∈ Finset.Icc 1 m, fac / (k * (p - k)) with hBdef
    have hdunit : ∀ k ∈ Finset.Icc 1 m, IsUnit ((k * (p - k) : ℕ) : ZMod p) := by
      intro k hk; simp only [Finset.mem_Icc] at hk
      rw [ZMod.isUnit_iff_coprime]
      have hk' : Nat.Coprime k p :=
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr
          (fun hd => by have := Nat.le_of_dvd (by omega) hd; omega)).symm
      have hpk' : Nat.Coprime (p - k) p :=
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr
          (fun hd => by have := Nat.le_of_dvd (by omega) hd; omega)).symm
      exact (Nat.Coprime.mul_right hk'.symm hpk'.symm).symm
    have hBz : ((B : ℕ) : ZMod p) = 0 := by
      have step : ∀ k ∈ Finset.Icc 1 m,
          ((fac / (k * (p - k)) : ℕ) : ZMod p)
            = (fac : ZMod p) * ((k * (p - k) : ℕ) : ZMod p)⁻¹ := by
        intro k hk
        have hdc : ((fac / (k * (p - k)) : ℕ) : ZMod p) * ((k * (p - k) : ℕ) : ZMod p)
            = (fac : ZMod p) := by
          rw [← Nat.cast_mul, Nat.div_mul_cancel (hddvd k hk)]
        rw [← hdc, mul_assoc, ZMod.mul_inv_of_unit _ (hdunit k hk), mul_one]
      have hw : ∑ k ∈ Finset.Icc 1 m, ((k * (p - k) : ℕ) : ZMod p)⁻¹ = 0 := by
        rw [← w6]; apply Finset.sum_congr rfl; intro k hk; simp only [Finset.mem_Icc] at hk
        rw [Nat.cast_mul, Nat.cast_sub (by omega), ZMod.natCast_self]
      rw [hBdef, Nat.cast_sum, Finset.sum_congr rfl step, ← Finset.mul_sum, hw, mul_zero]
    obtain ⟨B', hB'⟩ := (ZMod.natCast_eq_zero_iff B p).mp hBz
    exact ⟨B', by rw [hB']; ring⟩
  set A := ∑ k ∈ Finset.Icc 1 (p - 1), fac / k with hAdef
  have hfac0 : (fac : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos (p - 1)).ne'
  have hApos : 0 < A := by
    rw [hAdef]; apply Finset.sum_pos
    · intro k hk; simp only [Finset.mem_Icc] at hk
      exact Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos _)
        (Nat.dvd_factorial (by omega) (by omega))) (by omega)
    · exact ⟨1, by simp only [Finset.mem_Icc]; omega⟩
  have hharm : harmonic (p - 1) = (A : ℚ) / (fac : ℚ) := by
    rw [eq_div_iff hfac0, harmonic, hAdef, Finset.sum_mul, Nat.cast_sum]
    refine Finset.sum_nbij' (fun i => i + 1) (fun k => k - 1) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_range] at hi; simp only [Finset.mem_Icc]; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk; simp only [Finset.mem_range]; omega
    · intro i hi; simp only [Finset.mem_range] at hi; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk; omega
    · intro i hi; simp only [Finset.mem_range] at hi
      have hk1 : (i + 1) ∣ fac := Nat.dvd_factorial (by omega) (by omega)
      have hi0 : ((i + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : i + 1 ≠ 0)
      rw [Nat.cast_div hk1 hi0, div_eq_mul_inv, mul_comm]
  rw [hharm, padicValRat.div (by exact_mod_cast hApos.ne') hfac0,
    padicValRat.of_nat, padicValRat.of_nat]
  have hfacval : padicValNat p fac = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    rw [hfacdef, Nat.Prime.dvd_factorial hp]; omega
  rw [hfacval]
  simp only [Nat.cast_zero, sub_zero]
  have hAval : 2 ≤ padicValNat p A := by
    rcases (padicValNat_dvd_iff 2 A).mp hcrux with h | h
    · omega
    · exact h
  exact_mod_cast hAval

/-- `p = 3` is excluded: `C(5, 2) = 10 ≢ 1 (mod 27)`; and `p = 2`: `C(3, 1) = 3 ≢ 1 (mod 8)`. -/
example : ¬ ((2 * 3 - 1).choose (3 - 1) ≡ 1 [MOD 3 ^ 3]) := by decide
example : ¬ ((2 * 2 - 1).choose (2 - 1) ≡ 1 [MOD 2 ^ 3]) := by decide
example : (2 * 5 - 1).choose (5 - 1) ≡ 1 [MOD 5 ^ 3] := by decide
example : catalan 5 = 42 := by rw [catalan_eq_centralBinom_div]; rfl

end ClassicalLean
