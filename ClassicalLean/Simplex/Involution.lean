/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.GoldenRatio.Characterisations
import ClassicalLean.Simplex.Basic
import ClassicalLean.Simplex.LogSumExp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The map `σ x = 1 - 2 x`, and a golden softmax threshold

The file is named for the map `σ`; its principal result about `σ` is *negative*
(`sigmaMap_not_involutive`), so read the name as naming the map studied, not a property proved
of it.

## The map `σ`

`sigmaMap x i = 1 - 2 * x i` is the coordinatewise affine map `x ↦ 1 - 2 x`. Two facts fix its
shape. Its unique fixed point is the constant vector `1/3` (`sigmaMap_eq_self_iff`), and it moves
every coordinate away from that value by the factor `-2` (`sigmaMap_sub_third`): it is the
homothety of ratio `-2` about the constant vector `1/3`. It is therefore *not* an involution
(`sigmaMap_not_involutive`; its second iterate is `x ↦ 4 x - 1`, `sigmaMap_sigmaMap`), and
iterating it multiplies the distance of each coordinate from `1/3` by `2` each time
(`abs_sigmaMap_iterate_sub_third`), so every orbit other than the fixed vector's is unbounded
(`exists_lt_abs_sigmaMap_iterate_sub_third`).

On three coordinates the fixed vector `1/3` lies in the standard simplex, and `σ` preserves the
affine hyperplane `∑ x i = 1` (`sum_sigmaMap_fin3`). It does not preserve the simplex itself:
`sigmaMap_mem_closedSimplex_iff` says the image of a probability vector is again a probability
vector exactly when every coordinate is at most `1/2`.

## The golden threshold

`φ⁻¹` exceeds `1/2` (`half_lt_inv_goldenRatio`), so a probability vector with a coordinate at
least `φ⁻¹` is carried out of the simplex in one step
(`sigmaMap_notMem_closedSimplex_of_inv_goldenRatio_le`); quantitatively that coordinate lands at or
below `-(φ³)⁻¹` (`sigmaMap_le_neg_inv_goldenRatio_pow_three`). The three golden powers
`φ⁻¹, (φ³)⁻¹, (φ⁴)⁻¹` themselves sum to `1`
(`inv_goldenRatio_add_inv_pow_three_add_inv_pow_four`) and, being also strictly positive, are the
coordinates of a point of the open simplex and hence of the standard simplex
(`goldenPoint_mem_openSimplex`, `goldenPoint_mem_closedSimplex`). Summing to `1` alone would not
give membership: `closedSimplex` asks for nonnegativity too.

## A softmax threshold identity

For every nonzero real `m`, `m φ / (m φ + m) = φ⁻¹` (`softmax_dominant`). What makes the value
independent of `m` is simply that `m` cancels — `m φ + m = m φ²` — which is why the identity is
stated for a free nonzero factor, with the `n`-state form as a corollary.
`thresholdTemperature` names the temperature at which the Boltzmann factor takes that value; it
is a chosen constant.

The reading that gives those results their names — that the left-hand side is the dominant
weight of a softmax over `1 + m` states, one at energy `1` and `m` at energy `0` — used to be
prose in this paragraph. It is now proved. `twoLevelEnergy` builds that energy vector and
`softmax_twoLevelEnergy_thresholdTemperature` states the conclusion about the `softmax` of
`ClassicalLean.Simplex.LogSumExp` rather than about a quotient that resembles one. The identity
above is still the whole of the content; the quotient-level theorems are kept because they are
the steps the proof takes.

`φ` throughout is Mathlib's `Real.goldenRatio`, and the golden-ratio facts used are cited by name
where they are used.

## Not ported from the source

The following source material has no counterpart in this library, for the reasons
given.

* A statement of the form `(∑ x = 1) → ∀ _ : ℝ, (∑ x = 1)`, whose source proof is `exact h`:
  dropped. Its conclusion is one of its own hypotheses under a quantifier over an unused
  variable — the shape `tools/VacuityGate.lean` exists to reject.
* A wrapper theorem whose source proof applies another source theorem of the same statement to
  the same arguments: dropped as a duplicate of
  `sigmaMap_le_neg_inv_goldenRatio_pow_three`.
-/

open Finset Real

namespace ClassicalLean.Simplex

section Sigma

variable {ι : Type*}

/-! ## 1. The map `σ x = 1 - 2 x` -/

/-- The coordinatewise affine map `σ x = 1 - 2 x` on `ι → ℝ`. -/
def sigmaMap (x : ι → ℝ) : ι → ℝ := fun i ↦ 1 - 2 * x i

/-- Coordinates of `σ`. A definitional unfolding — the proof is `rfl` — stated so that later
proofs can rewrite by name instead of relying on defeq. -/
theorem sigmaMap_apply (x : ι → ℝ) (i : ι) : sigmaMap x i = 1 - 2 * x i := rfl

/-- **`σ` is a homothety of ratio `-2` about the constant vector `1/3`.** Each coordinate's
signed distance from `1/3` is multiplied by `-2`. -/
theorem sigmaMap_sub_third (x : ι → ℝ) (i : ι) :
    sigmaMap x i - 1 / 3 = -2 * (x i - 1 / 3) := by
  rw [sigmaMap_apply]; ring

/-- **The unique fixed point of `σ`** is the constant vector `1/3`. -/
theorem sigmaMap_eq_self_iff (x : ι → ℝ) : sigmaMap x = x ↔ x = fun _ ↦ (1 : ℝ) / 3 := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    rw [sigmaMap_apply] at hi
    change x i = 1 / 3
    linarith
  · rintro rfl
    funext i
    rw [sigmaMap_apply]
    norm_num

/-- The second iterate of `σ` is `x ↦ 4 x - 1`. -/
theorem sigmaMap_sigmaMap (x : ι → ℝ) : sigmaMap (sigmaMap x) = fun i ↦ 4 * x i - 1 := by
  funext i
  rw [sigmaMap_apply, sigmaMap_apply]
  ring

/-- **`σ` is not an involution** on a nonempty index type: `sigmaMap_sigmaMap` sends `0` to the
constant vector `-1`, not back to `0`. (On an empty index type every map is the identity, so the
nonemptiness hypothesis is not removable.) -/
theorem sigmaMap_not_involutive [Nonempty ι] :
    ¬ Function.Involutive (sigmaMap : (ι → ℝ) → ι → ℝ) := by
  intro h
  have h0 := congrFun (h 0) (Classical.arbitrary ι)
  simp only [sigmaMap_apply, Pi.zero_apply] at h0
  linarith

/-- **The iterates of `σ`.** The signed distance of a coordinate from `1/3` is multiplied by
`(-2) ^ n` after `n` steps. -/
theorem sigmaMap_iterate_sub_third (x : ι → ℝ) (i : ι) (n : ℕ) :
    (sigmaMap^[n] x) i - 1 / 3 = (-2 : ℝ) ^ n * (x i - 1 / 3) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', sigmaMap_sub_third, ih]
    ring

/-- **Escape.** After `n` steps the distance of a coordinate from `1/3` has grown by the factor
`2 ^ n`. That this makes the orbit unbounded is the next statement. -/
theorem abs_sigmaMap_iterate_sub_third (x : ι → ℝ) (i : ι) (n : ℕ) :
    |(sigmaMap^[n] x) i - 1 / 3| = 2 ^ n * |x i - 1 / 3| := by
  rw [sigmaMap_iterate_sub_third, abs_mul, abs_pow]
  norm_num

/-- **The orbit of any point other than the fixed vector is unbounded** in every coordinate where
it differs from `1/3`: no bound `M` is respected by all iterates. Proved from
`abs_sigmaMap_iterate_sub_third` and Mathlib's `pow_unbounded_of_one_lt`. -/
theorem exists_lt_abs_sigmaMap_iterate_sub_third (x : ι → ℝ) (i : ι) (hx : x i ≠ 1 / 3) (M : ℝ) :
    ∃ n : ℕ, M < |(sigmaMap^[n] x) i - 1 / 3| := by
  have hc : 0 < |x i - 1 / 3| := abs_pos.mpr (sub_ne_zero.mpr hx)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M / |x i - 1 / 3|) (by norm_num : (1 : ℝ) < 2)
  rw [div_lt_iff₀ hc] at hn
  exact ⟨n, by rw [abs_sigmaMap_iterate_sub_third]; exact hn⟩

/-- The coordinate sum after applying `σ`. -/
theorem sum_sigmaMap [Fintype ι] (x : ι → ℝ) :
    ∑ i, sigmaMap x i = (Fintype.card ι : ℝ) - 2 * ∑ i, x i := by
  simp only [sigmaMap, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, ← Finset.mul_sum]

end Sigma

/-! ## 2. Three coordinates: the simplex and its image -/

/-- On three coordinates `σ` preserves the affine hyperplane `∑ x i = 1`, because
`3 - 2 * 1 = 1`. -/
theorem sum_sigmaMap_fin3 {x : Fin 3 → ℝ} (h : ∑ i, x i = 1) : ∑ i, sigmaMap x i = 1 := by
  have hc : (Fintype.card (Fin 3) : ℝ) = 3 := by simp
  rw [sum_sigmaMap, h, hc]
  ring

/-- **The image of a probability vector under `σ` is a probability vector exactly on the box
`x i ≤ 1/2`.** The sum condition is automatic by `sum_sigmaMap_fin3`; only nonnegativity of
`1 - 2 * x i` is at issue. -/
theorem sigmaMap_mem_closedSimplex_iff {x : Fin 3 → ℝ} (hx : x ∈ closedSimplex (Fin 3)) :
    sigmaMap x ∈ closedSimplex (Fin 3) ↔ ∀ i, x i ≤ 1 / 2 := by
  constructor
  · intro h i
    have hi := h.1 i
    rw [sigmaMap_apply] at hi
    linarith
  · intro h
    refine ⟨fun i ↦ ?_, sum_sigmaMap_fin3 hx.2⟩
    rw [sigmaMap_apply]
    linarith [h i]

/-! ## 3. Golden powers and the threshold `φ⁻¹` -/

/-- `φ ^ 3 = 2 φ + 1`, from `Real.goldenRatio_pow_sub_goldenRatio_pow` and
`Real.goldenRatio_sq`. -/
theorem goldenRatio_pow_three : goldenRatio ^ 3 = 2 * goldenRatio + 1 := by
  have h := Real.goldenRatio_pow_sub_goldenRatio_pow 1
  have h2 := Real.goldenRatio_sq
  norm_num at h
  linarith

/-- `φ ^ 4 = 3 φ + 2`, from `Real.goldenRatio_pow_sub_goldenRatio_pow` and
`Real.goldenRatio_sq`. -/
theorem goldenRatio_pow_four : goldenRatio ^ 4 = 3 * goldenRatio + 2 := by
  have h := Real.goldenRatio_pow_sub_goldenRatio_pow 2
  have h1 := Real.goldenRatio_pow_sub_goldenRatio_pow 1
  have h2 := Real.goldenRatio_sq
  norm_num at h h1
  linarith

/-- `1 - 2 φ⁻¹ = -(φ³)⁻¹`: the value `σ` gives a coordinate sitting exactly at `φ⁻¹`. -/
theorem one_sub_two_mul_inv_goldenRatio :
    1 - 2 * goldenRatio⁻¹ = -(goldenRatio ^ 3)⁻¹ := by
  have h3 := goldenRatio_pow_three
  have h2 := Real.goldenRatio_sq
  have hne := Real.goldenRatio_ne_zero
  set x := goldenRatio
  clear_value x
  field_simp
  linarith

/-- `φ⁻¹ - 1/2 = (φ³)⁻¹ / 2`: how far the threshold `φ⁻¹` sits above the value `1/2` at which
`σ` changes the sign of a coordinate. -/
theorem inv_goldenRatio_sub_half : goldenRatio⁻¹ - 1 / 2 = (goldenRatio ^ 3)⁻¹ / 2 := by
  linarith [one_sub_two_mul_inv_goldenRatio]

/-- `1/2 < φ⁻¹`, since `φ < 2` (`Real.goldenRatio_lt_two`). -/
theorem half_lt_inv_goldenRatio : 1 / 2 < goldenRatio⁻¹ := by
  have hpos := Real.goldenRatio_pos
  have hlt := Real.goldenRatio_lt_two
  have hmul : goldenRatio * goldenRatio⁻¹ = 1 := mul_inv_cancel₀ Real.goldenRatio_ne_zero
  nlinarith [hmul, hpos, hlt]

/-- `φ⁻¹ + (φ³)⁻¹ + (φ⁴)⁻¹ = 1`, from `goldenRatio_pow_three` and `goldenRatio_pow_four`. -/
theorem inv_goldenRatio_add_inv_pow_three_add_inv_pow_four :
    goldenRatio⁻¹ + (goldenRatio ^ 3)⁻¹ + (goldenRatio ^ 4)⁻¹ = 1 := by
  have h3 := goldenRatio_pow_three
  have h4 := goldenRatio_pow_four
  have hne := Real.goldenRatio_ne_zero
  set x := goldenRatio
  clear_value x
  field_simp
  linarith

/-- The point of `Fin 3 → ℝ` whose coordinates are the golden powers `φ⁻¹, (φ³)⁻¹, (φ⁴)⁻¹`. -/
noncomputable def goldenPoint : Fin 3 → ℝ :=
  ![goldenRatio⁻¹, (goldenRatio ^ 3)⁻¹, (goldenRatio ^ 4)⁻¹]

/-- The three golden powers `φ⁻¹, (φ³)⁻¹, (φ⁴)⁻¹` are strictly positive and sum to `1`, so they
are the coordinates of a point of the **open** simplex. Positivity is part of what is asserted
here, unlike in `goldenPoint_mem_closedSimplex` below. -/
theorem goldenPoint_mem_openSimplex : goldenPoint ∈ openSimplex (Fin 3) := by
  have hpos := Real.goldenRatio_pos
  have h1 : (0 : ℝ) < goldenRatio⁻¹ := inv_pos.mpr hpos
  have h3 : (0 : ℝ) < (goldenRatio ^ 3)⁻¹ := inv_pos.mpr (by positivity)
  have h4 : (0 : ℝ) < (goldenRatio ^ 4)⁻¹ := inv_pos.mpr (by positivity)
  refine ⟨fun i ↦ ?_, ?_⟩
  · fin_cases i
    · exact h1
    · exact h3
    · exact h4
  · simp only [goldenPoint, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    exact inv_goldenRatio_add_inv_pow_three_add_inv_pow_four

/-- The same point lies in the closed simplex `closedSimplex (Fin 3)`, whose defining conditions are
nonnegativity — not positivity — and summing to `1`. -/
theorem goldenPoint_mem_closedSimplex : goldenPoint ∈ closedSimplex (Fin 3) :=
  openSimplex_subset_closedSimplex goldenPoint_mem_openSimplex

/-- `-(φ³)⁻¹ < 0`. -/
theorem neg_inv_goldenRatio_pow_three_neg : -(goldenRatio ^ 3)⁻¹ < 0 :=
  neg_lt_zero.mpr (inv_pos.mpr (pow_pos Real.goldenRatio_pos 3))

/-- `1 - 2 φ⁻¹ < 0`: a coordinate sitting exactly at the threshold `φ⁻¹` is carried strictly
below zero. This is `one_sub_two_mul_inv_goldenRatio` read with
`neg_inv_goldenRatio_pow_three_neg`. -/
theorem one_sub_two_mul_inv_goldenRatio_neg : 1 - 2 * goldenRatio⁻¹ < 0 := by
  rw [one_sub_two_mul_inv_goldenRatio]
  exact neg_inv_goldenRatio_pow_three_neg

/-- A coordinate at or above the threshold `φ⁻¹` is sent by `σ` to a value at or below `-(φ³)⁻¹`,
which is negative by `neg_inv_goldenRatio_pow_three_neg`. -/
theorem sigmaMap_le_neg_inv_goldenRatio_pow_three {ι : Type*} (x : ι → ℝ) (i : ι)
    (h : goldenRatio⁻¹ ≤ x i) : sigmaMap x i ≤ -(goldenRatio ^ 3)⁻¹ := by
  rw [sigmaMap_apply, ← one_sub_two_mul_inv_goldenRatio]
  linarith

/-- **A probability vector with a coordinate at or above `φ⁻¹` leaves the simplex in one step.**
Because `1/2 < φ⁻¹`, such a vector fails the criterion of `sigmaMap_mem_closedSimplex_iff`. -/
theorem sigmaMap_notMem_closedSimplex_of_inv_goldenRatio_le {x : Fin 3 → ℝ}
    (hx : x ∈ closedSimplex (Fin 3)) (i : Fin 3) (h : goldenRatio⁻¹ ≤ x i) :
    sigmaMap x ∉ closedSimplex (Fin 3) := by
  intro hmem
  have hle := (sigmaMap_mem_closedSimplex_iff hx).mp hmem i
  linarith [half_lt_inv_goldenRatio]

/-! ## 4. A softmax threshold identity -/

/-- **The softmax identity.** For any nonzero `m`, `m φ / (m φ + m) = φ⁻¹`. The factor `m` cancels
because `m φ + m = m (φ + 1) = m φ²` (`Real.goldenRatio_sq`); that cancellation is the whole
reason the value does not depend on `m`. Named for the softmax weight it computes; that the
quotient *is* that weight is `softmax_twoLevelEnergy_thresholdTemperature`, below. -/
theorem softmax_dominant (m : ℝ) (hm : m ≠ 0) :
    m * goldenRatio / (m * goldenRatio + m) = goldenRatio⁻¹ := by
  have hne := Real.goldenRatio_ne_zero
  have key : m * goldenRatio + m = m * goldenRatio ^ 2 := by
    rw [Real.goldenRatio_sq]; ring
  rw [key]
  set x := goldenRatio
  clear_value x
  field_simp

/-- **Design constant.** The value `1 / log (m φ)`. Read as a temperature, it is the one at which
the Boltzmann factor `exp (1 / τ)` between the dominant level and a suppressed one equals `m φ`;
that reading is context, and the value is *chosen*, with nothing here proving any requirement
forces it. What is proved about it is `exp_inv_thresholdTemperature`. -/
noncomputable def thresholdTemperature (m : ℝ) : ℝ := 1 / Real.log (m * goldenRatio)

/-- At the threshold temperature the Boltzmann factor is `m φ`, for every `m > 0`. -/
theorem exp_inv_thresholdTemperature {m : ℝ} (hm : 0 < m) :
    Real.exp (1 / thresholdTemperature m) = m * goldenRatio := by
  rw [thresholdTemperature, one_div_one_div]
  exact Real.exp_log (mul_pos hm Real.goldenRatio_pos)

/-- **The dominant softmax weight at the threshold temperature is `φ⁻¹`,** for every `m > 0` — in
particular it does not depend on `m`. Stated at the level of the quotient; the statement about
`softmax` itself is `softmax_twoLevelEnergy_thresholdTemperature`. -/
theorem softmax_at_thresholdTemperature {m : ℝ} (hm : 0 < m) :
    Real.exp (1 / thresholdTemperature m) / (Real.exp (1 / thresholdTemperature m) + m)
      = goldenRatio⁻¹ := by
  rw [exp_inv_thresholdTemperature hm]
  exact softmax_dominant m hm.ne'

/-- The `n`-state form: for `n ≥ 2` states, one dominant and `n - 1` suppressed, the dominant
softmax weight at the threshold temperature is `φ⁻¹` independently of `n`. A corollary of
`softmax_at_thresholdTemperature` with `m = n - 1`. -/
theorem softmax_at_thresholdTemperature_nat {n : ℕ} (hn : 2 ≤ n) :
    Real.exp (1 / thresholdTemperature ((n : ℝ) - 1))
        / (Real.exp (1 / thresholdTemperature ((n : ℝ) - 1)) + ((n : ℝ) - 1))
      = goldenRatio⁻¹ := by
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact softmax_at_thresholdTemperature (by linarith)

/-! ### The same statement about the `softmax` object

The three results above are quotients of exponentials that a reader has to be *told* are softmax
weights. `ClassicalLean.Simplex.LogSumExp` defines `softmax`, so the reading can be stated
instead: build the energy vector and take its dominant coordinate. -/

/-- The two-level energy vector on `n + 1` states at temperature `τ`: one dominant level of
energy `1` and `n` suppressed levels of energy `0`, each divided by `τ`. -/
noncomputable def twoLevelEnergy (n : ℕ) (τ : ℝ) : Fin (n + 1) → ℝ :=
  fun i => if i = 0 then 1 / τ else 0

/-- The partition sum of `twoLevelEnergy`: one Boltzmann factor `exp (1 / τ)`, and `n` factors
equal to `1` because `exp 0 = 1`. -/
theorem sum_exp_twoLevelEnergy (n : ℕ) (τ : ℝ) :
    ∑ j, Real.exp (twoLevelEnergy n τ j) = Real.exp (1 / τ) + n := by
  rw [Fin.sum_univ_succ]
  simp [twoLevelEnergy, Fin.succ_ne_zero]

/-- The dominant softmax coordinate of the two-level energy vector, as a quotient. -/
theorem softmax_twoLevelEnergy (n : ℕ) (τ : ℝ) :
    softmax (twoLevelEnergy n τ) 0 = Real.exp (1 / τ) / (Real.exp (1 / τ) + n) := by
  have h0 : twoLevelEnergy n τ 0 = 1 / τ := by simp [twoLevelEnergy]
  rw [softmax, h0, sum_exp_twoLevelEnergy]

/-- **The dominant softmax weight at the threshold temperature is `φ⁻¹`** — as a statement about
`softmax` rather than about a quotient that resembles one. On `n + 1` states with one dominant
level, at the temperature whose Boltzmann factor is `n φ`, the dominant coordinate of the
softmax is `φ⁻¹` for every `n ≥ 1`, independently of `n`. This is what `softmax_dominant` and
`softmax_at_thresholdTemperature` are named for; the cancellation `n φ + n = n φ²` remains the
only content, and those two supply it. -/
theorem softmax_twoLevelEnergy_thresholdTemperature {n : ℕ} (hn : 1 ≤ n) :
    softmax (twoLevelEnergy n (thresholdTemperature (n : ℝ))) 0 = goldenRatio⁻¹ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [softmax_twoLevelEnergy]
  exact softmax_at_thresholdTemperature hn'

/-! ## Arithmetic checks -/

/-- `σ` sends the vertex `(1, 0, 0)` of the simplex to `(-1, 1, 1)`, outside it. -/
example : sigmaMap ![(1 : ℝ), 0, 0] = ![-1, 1, 1] := by
  funext i
  fin_cases i <;> norm_num [sigmaMap]

/-- The fixed vector of `σ` lies in the three-point simplex. -/
example : (fun _ ↦ (1 : ℝ) / 3) ∈ closedSimplex (Fin 3) :=
  ⟨fun _ ↦ by norm_num, by simp⟩

/-- `σ` fixes that vector. -/
example : sigmaMap (fun _ ↦ (1 : ℝ) / 3) = (fun _ : Fin 3 ↦ (1 : ℝ) / 3) := by
  funext i
  rw [sigmaMap_apply]
  norm_num

/-- Two steps of `σ` from a vertex: `1 ↦ -1 ↦ 3`, matching `sigmaMap_sigmaMap`'s `4 x - 1`. -/
example : sigmaMap (sigmaMap ![(1 : ℝ), 0, 0]) 0 = 3 := by
  norm_num [sigmaMap]

end ClassicalLean.Simplex
