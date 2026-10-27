/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Rounding error in products, sums, inner products and Horner's rule, in the standard model

In the standard model of rounding, every arithmetic result is the exact result times `1 + d` with
`|d| ≤ u`, where `u` is the unit roundoff. Write `γ n = n u / (1 - n u)` (`gamma`), for `n u < 1`.

* `abs_prod_one_add_sub_one_le`: `n` such factors give `|∏ (1 + dᵢ) - 1| ≤ γ n`.
* `abs_mul_prod_sub_le`: so a result carrying `n` rounding factors is within `γ n · |exact|` of
  the exact result.
* `abs_prodComputed_sub_le`: a product of `n + 1` numbers, formed left to right, takes `n`
  roundings and is within `γ n · |∏ xᵢ|` of the exact product.
* `abs_sumComputed_sub_le`: a sum of `n + 1` numbers, added left to right, takes `n` roundings and
  is within `γ n · ∑ |xᵢ|` of the exact sum.
* `abs_dotComputed_sub_le` (order LEAN-18): an inner product of `n + 1` terms, each product
  rounded once and the products added left to right, is within `γ (n + 1) · ∑ |xᵢ yᵢ|` of the
  exact one (Higham 2002, (3.5), there for `n` terms and `γ n`).
* `abs_hornerComputed_sub_le` (order LEAN-18): Horner's rule for `∑ aᵢ xⁱ` of degree `n`, each
  multiplication and each addition rounded, is within `γ (2n) · ∑ |aᵢ| |x|ⁱ` of `p(x)` (Higham
  2002, (5.3)). `hornerRev` runs the rule on the coefficients listed from the highest;
  `exists_hornerRev_eq` gives each term its own error of at most `γ (2k)` after `k` steps, as
  `exists_sumComputed_eq` does for a sum; `self_le_gamma` is `u ≤ γ m` for `m ≥ 1`.
* `exists_forwardSubstComputed_eq` — order LEAN-36, item 133, **forward substitution is backward
  stable**: `forwardSubstComputed` solves a lower-triangular `L x = b` row by row, each product,
  subtraction and division rounded (`subComputed` is one row's running remainder); with nonzero
  diagonal, every rounding at most `u` in size and `n u < 1`, the computed `x` solves
  `(L + ΔL) x = b` exactly on rows `i < n`, with `|ΔL i j| ≤ γ n · |L i j|` for `j ≤ i < n` (the
  plan's row cites Higham 2002, Theorem 8.5; not checked against the book by this order). Against
  the plan's row (FAITHFUL): `L`, `b` and the roundings are functions on `ℕ`, the system is the
  first `n` rows, and the bound is stated where forward substitution reads `L`, on and below the
  diagonal. The proofs are the draft `d133-r1-s1` (written by Claude Opus 5.5 through the Anthropic
  Batch API, the lane's API-CREDIT-1 work), adapted by order LEAN-36's session: inside this
  namespace without the draft's `open … RoundingError`; in `forwardSubstComputed`, `if h : j < i`
  written `if _h : j < i` (the name is unused); in four proof lines about the private `deltaL`,
  Lean's deprecated `if_pos` and `if_neg` replaced by `ite_eq_left` and `ite_eq_right`, as its
  deprecation warnings name; the private `gamma_mono'` kept, this module having no monotonicity
  lemma for `γ`. The session did not drop-test the theorem's five hypotheses; order LEAN-36's review
  (e) did, outside the library: dropping any one alone, the conclusion fails at an instance where
  the other four hold (the failure proved in Lean). The witness is claude-ai's (lane
  `lean/LEAN-36/data/witnesses.txt`, section RoundingError), its head written as the full name and
  its `b` changed by the session (said in its docstring).

Lean's `Float` is opaque to proof, so the model is stated over the reals with the `d`'s as
hypotheses. As a fact about hardware, not a theorem here: IEEE 754 double precision with round to
nearest satisfies the model with `u = 2⁻⁵³`, as long as no result overflows or underflows. Then
`γ 1000 ≈ 1.1 · 10⁻¹³` and `γ 10⁹ ≈ 1.1 · 10⁻⁷`.

Each hypothesis is needed. With `n u ≥ 1` the bound has no meaning, and Lean's `γ` is `x / 0 = 0`
at `n u = 1`: two factors `1 + 1/2` give the error `5/4` against `γ 2 = 0`. And `n u` alone is
not a bound: two factors `1 + 1/4` give `9/16 > 2 · 1/4`.

The two theorems of order LEAN-18 need each of their hypotheses too (order LEAN-18, checks C14 and
C15, exact rationals; each case keeps the other hypotheses; both bounds hold on 3000 random
cases). Inner product: a product rounding `ε = 1/2` above `u = 1/4` (`n = 0`, `x = y = 1`) gives
the error `1/2` against `γ 1 = 1/3`; an addition rounding `δ = 1` above `u = 1/10` (`n = 1`,
`x = y = (1, 1)`) gives `2` against `1/2`; and `(n + 1) u = 1` (`n = 0`, `u = ε = 1`) gives `1`
against Lean's `γ 1 = 0`. Horner's rule, for `p(x) = x` at `x = 1` (`n = 1`): `ε = 1` or `δ = 1`
above `u = 1/10` gives `1` against `1/4`, and `2 n u = 1` (`u = ε = δ = 1/2`) gives `5/4`
against `γ 2 = 0`.
-/

open Finset

namespace ClassicalLean.Analysis.RoundingError

/-- `γ n = n u / (1 - n u)`. -/
noncomputable def gamma (u : ℝ) (n : ℕ) : ℝ := n * u / (1 - n * u)

lemma gamma_nonneg {u : ℝ} (hu : 0 ≤ u) {n : ℕ} (h : n * u < 1) : 0 ≤ gamma u n :=
  div_nonneg (by positivity) (by linarith)

/-- **One more rounding.** If `|η| ≤ γ n`, `|δ| ≤ u` and `(n + 1) u < 1`, then
`|(1 + η)(1 + δ) - 1| ≤ γ (n + 1)`. -/
theorem abs_one_add_mul_sub_one_le {u η δ : ℝ} {n : ℕ} (h : ((n : ℝ) + 1) * u < 1)
    (hη : |η| ≤ gamma u n) (hδ : |δ| ≤ u) : |(1 + η) * (1 + δ) - 1| ≤ gamma u (n + 1) := by
  have hu : 0 ≤ u := (abs_nonneg δ).trans hδ
  have hn : (n : ℝ) * u < 1 := by nlinarith
  have h1 : 0 < 1 - (n : ℝ) * u := by linarith
  have h2 : 0 < 1 - ((n : ℝ) + 1) * u := by linarith
  have hγ : 0 ≤ gamma u n := gamma_nonneg hu hn
  have e : (1 + η) * (1 + δ) - 1 = η + δ + η * δ := by ring
  have hab : |η + δ + η * δ| ≤ gamma u n + u + gamma u n * u := by
    calc |η + δ + η * δ| ≤ |η| + |δ| + |η| * |δ| := by
          rw [← abs_mul]; exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ gamma u n + u + gamma u n * u := by gcongr
  have hval : gamma u n + u + gamma u n * u = ((n : ℝ) + 1) * u / (1 - (n : ℝ) * u) := by
    unfold gamma; field_simp; ring
  rw [e]
  refine hab.trans (hval.le.trans ?_)
  unfold gamma
  push_cast
  apply div_le_div_of_nonneg_left (by positivity) h2
  nlinarith

/-- **`n` rounding factors.** If `|dᵢ| ≤ u` for `i < n` and `n u < 1`, then
`|∏_{i < n} (1 + dᵢ) - 1| ≤ γ n`. -/
theorem abs_prod_one_add_sub_one_le {u : ℝ} {d : ℕ → ℝ} {n : ℕ} (hd : ∀ i < n, |d i| ≤ u)
    (h : n * u < 1) : |∏ i ∈ range n, (1 + d i) - 1| ≤ gamma u n := by
  induction n with
  | zero => simp [gamma]
  | succ n ih =>
    have hu : 0 ≤ u := (abs_nonneg _).trans (hd 0 (Nat.succ_pos n))
    have h' : (n : ℝ) * u < 1 := by push_cast at h; nlinarith
    rw [prod_range_succ]
    push_cast at h
    have := abs_one_add_mul_sub_one_le (η := ∏ i ∈ range n, (1 + d i) - 1) h
      (ih (fun i hi ↦ hd i (hi.trans (Nat.lt_succ_self n))) h') (hd n (Nat.lt_succ_self n))
    simpa using this

/-- **A result with `n` rounding factors.** If the computed value is `e · ∏_{i < n} (1 + dᵢ)`
with `|dᵢ| ≤ u` and `n u < 1`, it is within `γ n · |e|` of the exact value `e`. -/
theorem abs_mul_prod_sub_le {u e : ℝ} {d : ℕ → ℝ} {n : ℕ} (hd : ∀ i < n, |d i| ≤ u)
    (h : n * u < 1) : |e * ∏ i ∈ range n, (1 + d i) - e| ≤ gamma u n * |e| := by
  rw [show e * ∏ i ∈ range n, (1 + d i) - e = e * (∏ i ∈ range n, (1 + d i) - 1) by ring,
    abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_prod_one_add_sub_one_le hd h) (abs_nonneg e)

/-- A product of `x 0, …, x n` formed left to right, each multiplication rounded by `1 + d k`. -/
def prodComputed (x d : ℕ → ℝ) : ℕ → ℝ
  | 0 => x 0
  | k + 1 => prodComputed x d k * x (k + 1) * (1 + d k)

lemma prodComputed_eq (x d : ℕ → ℝ) (n : ℕ) :
    prodComputed x d n = (∏ i ∈ range (n + 1), x i) * ∏ i ∈ range n, (1 + d i) := by
  induction n with
  | zero => simp [prodComputed]
  | succ n ih =>
    rw [prodComputed, ih, prod_range_succ x (n + 1), prod_range_succ (fun i ↦ 1 + d i) n]; ring

/-- **A product of `n + 1` numbers.** Formed left to right with `n` roundings, `|dₖ| ≤ u` and
`n u < 1`, the computed product is within `γ n · |∏ xᵢ|` of the exact one. -/
theorem abs_prodComputed_sub_le {u : ℝ} {x d : ℕ → ℝ} {n : ℕ} (hd : ∀ k < n, |d k| ≤ u)
    (h : n * u < 1) : |prodComputed x d n - ∏ i ∈ range (n + 1), x i| ≤
      gamma u n * |∏ i ∈ range (n + 1), x i| := by
  rw [prodComputed_eq]
  exact abs_mul_prod_sub_le hd h

/-- A sum of `x 0, …, x n` formed left to right, each addition rounded by `1 + δ k`. -/
def sumComputed (x δ : ℕ → ℝ) : ℕ → ℝ
  | 0 => x 0
  | k + 1 => (sumComputed x δ k + x (k + 1)) * (1 + δ k)

/-- Each term of the computed sum carries its own error, at most `γ n`. -/
theorem exists_sumComputed_eq {u : ℝ} {x δ : ℕ → ℝ} {n : ℕ} (hδ : ∀ k < n, |δ k| ≤ u)
    (h : n * u < 1) : ∃ η : ℕ → ℝ, (∀ i ∈ range (n + 1), |η i| ≤ gamma u n) ∧
      sumComputed x δ n = ∑ i ∈ range (n + 1), x i * (1 + η i) := by
  induction n with
  | zero => exact ⟨fun _ ↦ 0, fun i _ ↦ by simp [gamma], by simp [sumComputed]⟩
  | succ n ih =>
    have hu : 0 ≤ u := (abs_nonneg _).trans (hδ 0 (Nat.succ_pos n))
    push_cast at h
    have h' : (n : ℝ) * u < 1 := by nlinarith
    obtain ⟨η, hη, hs⟩ := ih (fun k hk ↦ hδ k (hk.trans (Nat.lt_succ_self n))) h'
    have hδn := hδ n (Nat.lt_succ_self n)
    refine ⟨fun i ↦ if i ≤ n then (1 + η i) * (1 + δ n) - 1 else δ n, fun i hi ↦ ?_, ?_⟩
    · by_cases hin : i ≤ n
      · simp only [hin, ↓reduceIte]
        exact abs_one_add_mul_sub_one_le h (hη i (mem_range.mpr (Nat.lt_succ_of_le hin))) hδn
      · simp only [hin, ↓reduceIte]
        refine hδn.trans ?_
        unfold gamma; push_cast
        rw [le_div_iff₀ (by linarith)]
        nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hu, mul_nonneg hu hu,
          mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (mul_nonneg hu hu)]
    · rw [sumComputed, hs, sum_range_succ _ (n + 1), add_mul, sum_mul]
      congr 1
      · refine sum_congr rfl fun i hi ↦ ?_
        have : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
        simp only [this, ↓reduceIte]; ring
      · simp

/-- **A sum of `n + 1` numbers.** Added left to right with `n` roundings, `|δₖ| ≤ u` and
`n u < 1`, the computed sum is within `γ n · ∑ |xᵢ|` of the exact sum. -/
theorem abs_sumComputed_sub_le {u : ℝ} {x δ : ℕ → ℝ} {n : ℕ} (hδ : ∀ k < n, |δ k| ≤ u)
    (h : n * u < 1) : |sumComputed x δ n - ∑ i ∈ range (n + 1), x i| ≤
      gamma u n * ∑ i ∈ range (n + 1), |x i| := by
  obtain ⟨η, hη, hs⟩ := exists_sumComputed_eq hδ h
  rw [hs, ← sum_sub_distrib, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi ↦ ?_)
  rw [show x i * (1 + η i) - x i = η i * x i by ring, abs_mul, mul_comm (gamma u n)]
  exact mul_le_mul_of_nonneg_right (hη i hi) (abs_nonneg _) |>.trans_eq (mul_comm _ _)

/-- An inner product `∑ xᵢ yᵢ` of `n + 1` terms in the standard model: each product
`x i * y i` is rounded by `1 + ε i`, and the products are added left to right with `sumComputed`,
each addition rounded by `1 + δ k`. -/
def dotComputed (x y ε δ : ℕ → ℝ) (n : ℕ) : ℝ :=
  sumComputed (fun i ↦ x i * y i * (1 + ε i)) δ n

/-- **An inner product of `n + 1` terms.** With every rounding at most `u` in size and
`(n + 1) u < 1`, the computed inner product is within `γ (n + 1) · ∑ |xᵢ yᵢ|` of the exact one:
each product carries its own rounding and at most `n` from the additions. -/
theorem abs_dotComputed_sub_le {u : ℝ} {x y ε δ : ℕ → ℝ} {n : ℕ} (hε : ∀ i ≤ n, |ε i| ≤ u)
    (hδ : ∀ k < n, |δ k| ≤ u) (h : ((n : ℝ) + 1) * u < 1) :
    |dotComputed x y ε δ n - ∑ i ∈ range (n + 1), x i * y i| ≤
      gamma u (n + 1) * ∑ i ∈ range (n + 1), |x i * y i| := by
  have hu : 0 ≤ u := (abs_nonneg _).trans (hε 0 (Nat.zero_le n))
  have h' : (n : ℝ) * u < 1 := by nlinarith
  obtain ⟨η, hη, hs⟩ := exists_sumComputed_eq (x := fun i ↦ x i * y i * (1 + ε i)) hδ h'
  rw [dotComputed, hs, ← sum_sub_distrib, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi ↦ ?_)
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hb := abs_one_add_mul_sub_one_le h (hη i hi) (hε i hi')
  rw [show x i * y i * (1 + ε i) * (1 + η i) - x i * y i
      = x i * y i * ((1 + η i) * (1 + ε i) - 1) by ring, abs_mul, mul_comm (gamma u (n + 1))]
  exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)

/-- Horner's rule on the coefficients `c 0, c 1, …` listed from the highest: start from `c 0`;
at step `k + 1` multiply by `x` (rounded by `1 + ε k`) and add `c (k + 1)` (rounded by `1 + δ k`).
With no rounding, step `k` gives `∑ i ≤ k, c i * x ^ (k - i)`. -/
def hornerRev (c : ℕ → ℝ) (x : ℝ) (ε δ : ℕ → ℝ) : ℕ → ℝ
  | 0 => c 0
  | k + 1 => (hornerRev c x ε δ k * x * (1 + ε k) + c (k + 1)) * (1 + δ k)

/-- Horner's rule for `∑ i ≤ n, a i * x ^ i` in the standard model: `hornerRev` on the
coefficients `a n, a (n - 1), …, a 0`. -/
def hornerComputed (a : ℕ → ℝ) (x : ℝ) (ε δ : ℕ → ℝ) (n : ℕ) : ℝ :=
  hornerRev (fun i ↦ a (n - i)) x ε δ n

/-- One rounding is within `γ m` for any `m ≥ 1` with `m u < 1`. -/
lemma self_le_gamma {u : ℝ} (hu : 0 ≤ u) {m : ℕ} (hm : 1 ≤ m) (h : m * u < 1) : u ≤ gamma u m := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold gamma
  rw [le_div_iff₀ (by linarith)]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ m) hu]

/-- After `k` steps of Horner's rule, each term `c i * x ^ (k - i)` carries its own error, at
most `γ (2k)`: `c 0` is rounded twice at each of the `k` steps, and a coefficient added at step
`j ≥ 1` once by that addition and twice at each later step. -/
theorem exists_hornerRev_eq {u x : ℝ} {c ε δ : ℕ → ℝ} {k : ℕ} (hε : ∀ j < k, |ε j| ≤ u)
    (hδ : ∀ j < k, |δ j| ≤ u) (h : 2 * (k : ℝ) * u < 1) :
    ∃ η : ℕ → ℝ, (∀ i ∈ range (k + 1), |η i| ≤ gamma u (2 * k)) ∧
      hornerRev c x ε δ k = ∑ i ∈ range (k + 1), c i * x ^ (k - i) * (1 + η i) := by
  induction k with
  | zero => exact ⟨fun _ ↦ 0, fun i _ ↦ by simp [gamma], by simp [hornerRev]⟩
  | succ k ih =>
    have hu : 0 ≤ u := (abs_nonneg _).trans (hε 0 (Nat.succ_pos k))
    push_cast at h
    have h' : 2 * (k : ℝ) * u < 1 := by nlinarith
    obtain ⟨η, hη, hs⟩ := ih (fun j hj ↦ hε j (hj.trans (Nat.lt_succ_self k)))
      (fun j hj ↦ hδ j (hj.trans (Nat.lt_succ_self k))) h'
    have hεk := hε k (Nat.lt_succ_self k)
    have hδk := hδ k (Nat.lt_succ_self k)
    have h1 : ((2 * k : ℕ) + 1 : ℝ) * u < 1 := by push_cast; nlinarith
    have h2 : ((2 * k + 1 : ℕ) + 1 : ℝ) * u < 1 := by push_cast; nlinarith
    refine ⟨fun i ↦ if i ≤ k then (1 + η i) * (1 + ε k) * (1 + δ k) - 1 else δ k,
      fun i hi ↦ ?_, ?_⟩
    · by_cases hik : i ≤ k
      · simp only [hik, ↓reduceIte]
        have hz := abs_one_add_mul_sub_one_le h1
          (hη i (mem_range.mpr (Nat.lt_succ_of_le hik))) hεk
        have hz2 := abs_one_add_mul_sub_one_le h2
          (η := (1 + η i) * (1 + ε k) - 1) hz hδk
        rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
        simpa using hz2
      · simp only [hik, ↓reduceIte]
        refine hδk.trans (self_le_gamma hu (by omega) ?_)
        push_cast; linarith
    · rw [hornerRev, hs, sum_range_succ _ (k + 1), Nat.sub_self, pow_zero, add_mul, sum_mul,
        sum_mul, sum_mul]
      congr 1
      · refine sum_congr rfl fun i hi ↦ ?_
        have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
        simp only [hik, ↓reduceIte]
        rw [Nat.succ_sub hik, pow_succ]
        ring
      · simp

/-- **Horner's rule.** For a polynomial of degree `n`, with every rounding at most `u` in size and
`2 n u < 1`, the computed value is within `γ (2n) · ∑ |aᵢ| |x|ⁱ` of `p(x) = ∑ aᵢ xⁱ`. -/
theorem abs_hornerComputed_sub_le {u x : ℝ} {a ε δ : ℕ → ℝ} {n : ℕ} (hε : ∀ k < n, |ε k| ≤ u)
    (hδ : ∀ k < n, |δ k| ≤ u) (h : 2 * (n : ℝ) * u < 1) :
    |hornerComputed a x ε δ n - ∑ i ∈ range (n + 1), a i * x ^ i| ≤
      gamma u (2 * n) * ∑ i ∈ range (n + 1), |a i| * |x| ^ i := by
  obtain ⟨η, hη, hs⟩ := exists_hornerRev_eq (c := fun i ↦ a (n - i)) (x := x) hε hδ h
  have hp : ∑ i ∈ range (n + 1), a i * x ^ i = ∑ i ∈ range (n + 1), a (n - i) * x ^ (n - i) := by
    rw [← sum_range_reflect (fun i ↦ a i * x ^ i) (n + 1)]
    simp
  have hq : ∑ i ∈ range (n + 1), |a i| * |x| ^ i
      = ∑ i ∈ range (n + 1), |a (n - i)| * |x| ^ (n - i) := by
    rw [← sum_range_reflect (fun i ↦ |a i| * |x| ^ i) (n + 1)]
    simp
  rw [hornerComputed, hs, hp, hq, ← sum_sub_distrib, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi ↦ ?_)
  rw [show a (n - i) * x ^ (n - i) * (1 + η i) - a (n - i) * x ^ (n - i)
      = η i * (a (n - i) * x ^ (n - i)) by ring, abs_mul, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_right (hη i hi) (by positivity)

/-- Row `i` of forward substitution: start from `b i`; at step `k + 1` subtract `l i k * x k`,
the product rounded by `1 + ε i k` and the subtraction rounded in the form `exact / (1 + δ i k)`. -/
noncomputable def subComputed (l : ℕ → ℕ → ℝ) (b x : ℕ → ℝ) (ε δ : ℕ → ℕ → ℝ) (i : ℕ) :
    ℕ → ℝ
  | 0 => b i
  | k + 1 => (subComputed l b x ε δ i k - l i k * x k * (1 + ε i k)) / (1 + δ i k)

/-- Forward substitution for lower-triangular `L x = b` in the standard model: `x i` is the
computed `(b i - ∑_{j<i} l i j x j)` divided by `l i i`, the division rounded in the form
`exact / (1 + ρ i)`. -/
noncomputable def forwardSubstComputed (l : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (ε δ : ℕ → ℕ → ℝ)
    (ρ : ℕ → ℝ) (i : ℕ) : ℝ :=
  subComputed l b (fun j ↦ if _h : j < i then forwardSubstComputed l b ε δ ρ j else 0) ε δ i i
    / l i i / (1 + ρ i)
termination_by i

/-- The backward error of forward substitution. -/
private noncomputable def deltaL (l : ℕ → ℕ → ℝ) (ε δ : ℕ → ℕ → ℝ) (ρ : ℕ → ℝ) (i j : ℕ) : ℝ :=
  if j < i then l i j * ((1 + ε i j) * ∏ m ∈ range j, (1 + δ i m) - 1)
  else if j = i then l i i * ((1 + ρ i) * ∏ m ∈ range i, (1 + δ i m) - 1) else 0

private lemma subComputed_congr (l : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (ε δ : ℕ → ℕ → ℝ) (i : ℕ)
    {x x' : ℕ → ℝ} (k : ℕ) (h : ∀ j < k, x j = x' j) :
    subComputed l b x ε δ i k = subComputed l b x' ε δ i k := by
  induction k with
  | zero => simp [subComputed]
  | succ k ih =>
    simp only [subComputed]
    rw [ih (fun j hj ↦ h j (by omega)), h k (by omega)]

private lemma forwardSubstComputed_eq_sub (l : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (ε δ : ℕ → ℕ → ℝ)
    (ρ : ℕ → ℝ) (i : ℕ) :
    forwardSubstComputed l b ε δ ρ i =
      subComputed l b (forwardSubstComputed l b ε δ ρ) ε δ i i / l i i / (1 + ρ i) := by
  rw [forwardSubstComputed]
  have := subComputed_congr l b ε δ i
    (x := fun j ↦ if h : j < i then forwardSubstComputed l b ε δ ρ j else 0)
    (x' := forwardSubstComputed l b ε δ ρ) i (fun j hj ↦ by simp [hj])
  rw [this]

private lemma subComputed_mul_prod (l : ℕ → ℕ → ℝ) (b x : ℕ → ℝ) (ε δ : ℕ → ℕ → ℝ)
    (i k : ℕ) (hne : ∀ m < k, 1 + δ i m ≠ 0) :
    subComputed l b x ε δ i k * ∏ m ∈ range k, (1 + δ i m) +
      ∑ j ∈ range k, l i j * x j * (1 + ε i j) * ∏ m ∈ range j, (1 + δ i m) = b i := by
  induction k with
  | zero => simp [subComputed]
  | succ k ih =>
    have ih' := ih (fun m hm ↦ hne m (by omega))
    have hk := hne k (by omega)
    have e : subComputed l b x ε δ i (k + 1) * (1 + δ i k)
        = subComputed l b x ε δ i k - l i k * x k * (1 + ε i k) := by
      simp only [subComputed]
      field_simp
    rw [prod_range_succ, sum_range_succ]
    linear_combination ih' + (∏ m ∈ range k, (1 + δ i m)) * e

private lemma gamma_mono' {u : ℝ} (hu : 0 ≤ u) {a b : ℕ} (hab : a ≤ b) (h : (b : ℝ) * u < 1) :
    gamma u a ≤ gamma u b := by
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hm := mul_le_mul_of_nonneg_right hab' hu
  have ha : (a : ℝ) * u < 1 := by nlinarith
  unfold gamma
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

private lemma abs_one_add_mul_prod_sub_one_le' {u r : ℝ} {d : ℕ → ℝ} {m n : ℕ}
    (hd : ∀ k < m, |d k| ≤ u) (hr : |r| ≤ u) (hmn : m + 1 ≤ n) (h : (n : ℝ) * u < 1) :
    |(1 + r) * ∏ k ∈ range m, (1 + d k) - 1| ≤ gamma u n := by
  have hu : 0 ≤ u := (abs_nonneg r).trans hr
  have hmn' : ((m : ℝ) + 1) ≤ n := by exact_mod_cast hmn
  have hmul := mul_le_mul_of_nonneg_right hmn' hu
  have h1 : ((m : ℝ) + 1) * u < 1 := by nlinarith
  have h0 : (m : ℝ) * u < 1 := by nlinarith
  have hP := abs_prod_one_add_sub_one_le hd h0
  have hb := abs_one_add_mul_sub_one_le h1 hP hr
  have e : (1 + (∏ k ∈ range m, (1 + d k) - 1)) * (1 + r) - 1
      = (1 + r) * ∏ k ∈ range m, (1 + d k) - 1 := by ring
  rw [e] at hb
  exact hb.trans (gamma_mono' hu hmn h)

private lemma one_add_ne_zero' {u r : ℝ} {n : ℕ} (hr : |r| ≤ u) (hn : 1 ≤ n)
    (h : (n : ℝ) * u < 1) : 1 + r ≠ 0 := by
  intro h0
  have hr' : r = -1 := by linarith
  rw [hr', abs_neg, abs_one] at hr
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- **Forward substitution is backward stable** (item 133 of MATH-PLAN-library-2, whose row cites
Higham 2002, Theorem 8.5, not checked against the book; the draft `d133-r1-s1`, written by Claude
Opus 5.5 through the Anthropic Batch API, the lane's API-CREDIT-1 work, adapted by order LEAN-36's
session). With every rounding at most `u` in size, `n u < 1` and nonzero diagonal, the computed
solution `forwardSubstComputed` of the lower-triangular system `L x = b` (rows `i < n`) solves
`(L + ΔL) x = b` exactly, with `|ΔL i j| ≤ γ n · |L i j|` for `j ≤ i < n`. Only the entries with
`j ≤ i` enter: forward substitution never reads the entries above the diagonal, and the statement
says nothing of `ΔL` there. The proof takes `ΔL` from the rounding factors each product,
subtraction and division carries (`abs_prod_one_add_sub_one_le`, `abs_one_add_mul_sub_one_le`). -/
theorem exists_forwardSubstComputed_eq {u : ℝ} {l : ℕ → ℕ → ℝ} {b : ℕ → ℝ}
    {ε δ : ℕ → ℕ → ℝ} {ρ : ℕ → ℝ} {n : ℕ}
    (hl : ∀ i < n, l i i ≠ 0)
    (hε : ∀ i < n, ∀ j < i, |ε i j| ≤ u) (hδ : ∀ i < n, ∀ j < i, |δ i j| ≤ u)
    (hρ : ∀ i < n, |ρ i| ≤ u) (h : (n : ℝ) * u < 1) :
    ∃ ΔL : ℕ → ℕ → ℝ, (∀ i < n, ∀ j ≤ i, |ΔL i j| ≤ gamma u n * |l i j|) ∧
      ∀ i < n, ∑ j ∈ range (i + 1), (l i j + ΔL i j) * forwardSubstComputed l b ε δ ρ j
        = b i := by
  refine ⟨deltaL l ε δ ρ, ?_, ?_⟩
  · intro i hi j hj
    by_cases hji : j < i
    · rw [deltaL, ite_eq_left hji, abs_mul, mul_comm (gamma u n)]
      exact mul_le_mul_of_nonneg_left
        (abs_one_add_mul_prod_sub_one_le' (m := j) (d := δ i)
          (fun k hk ↦ hδ i hi k (by omega)) (hε i hi j hji) (by omega) h) (abs_nonneg _)
    · have hji' : j = i := by omega
      rw [hji', deltaL, ite_eq_right (lt_irrefl i), ite_eq_left rfl, abs_mul, mul_comm (gamma u n)]
      exact mul_le_mul_of_nonneg_left
        (abs_one_add_mul_prod_sub_one_le' (m := i) (d := δ i)
          (fun k hk ↦ hδ i hi k hk) (hρ i hi) (by omega) h) (abs_nonneg _)
  · intro i hi
    have hne : ∀ m < i, 1 + δ i m ≠ 0 := fun m hm ↦
      one_add_ne_zero' (hδ i hi m hm) (by omega) h
    have hρne : 1 + ρ i ≠ 0 := one_add_ne_zero' (hρ i hi) (by omega) h
    have hli : l i i ≠ 0 := hl i hi
    have hrow := subComputed_mul_prod l b (forwardSubstComputed l b ε δ ρ) ε δ i i hne
    have hs : forwardSubstComputed l b ε δ ρ i * (1 + ρ i) * l i i
        = subComputed l b (forwardSubstComputed l b ε δ ρ) ε δ i i := by
      rw [forwardSubstComputed_eq_sub l b ε δ ρ i]
      field_simp
    have hsum : ∑ j ∈ range i, (l i j + deltaL l ε δ ρ i j) * forwardSubstComputed l b ε δ ρ j
        = ∑ j ∈ range i, l i j * forwardSubstComputed l b ε δ ρ j * (1 + ε i j) *
            ∏ m ∈ range j, (1 + δ i m) :=
      sum_congr rfl fun j hj ↦ by rw [deltaL, ite_eq_left (mem_range.mp hj)]; ring
    have hdiag : l i i + deltaL l ε δ ρ i i
        = l i i * ((1 + ρ i) * ∏ m ∈ range i, (1 + δ i m)) := by
      rw [deltaL, ite_eq_right (lt_irrefl i), ite_eq_left rfl]; ring
    rw [sum_range_succ, hsum, hdiag]
    linear_combination hrow + (∏ m ∈ range i, (1 + δ i m)) * hs

end ClassicalLean.Analysis.RoundingError

/-- The hypotheses of `abs_dotComputed_sub_le` hold together: unit roundoff `u = 1/10`, every
rounding error `ε i` and `δ k` equal to `1/20`, so at most `u` in size, and `n = 2` (three terms),
where `(n + 1) u = 3/10 < 1`; the vectors are `x i = i + 1` and `y i = 2`. -/
example := ClassicalLean.Analysis.RoundingError.abs_dotComputed_sub_le (u := 1 / 10)
  (x := fun i ↦ i + 1) (y := fun _ ↦ 2) (ε := fun _ ↦ 1 / 20) (δ := fun _ ↦ 1 / 20) (n := 2)
  (fun _ _ ↦ by norm_num [abs_of_pos]) (fun _ _ ↦ by norm_num [abs_of_pos]) (by norm_num)

/-- The hypotheses of `abs_hornerComputed_sub_le` hold together: unit roundoff `u = 1/10`, every
rounding error `ε k` and `δ k` equal to `1/20`, so at most `u` in size, and degree `n = 2`, where
`2 n u = 2/5 < 1`; the coefficients are `a i = i + 1` at the point `x = 3`. -/
example := ClassicalLean.Analysis.RoundingError.abs_hornerComputed_sub_le (u := 1 / 10) (x := 3)
  (a := fun i ↦ i + 1) (ε := fun _ ↦ 1 / 20) (δ := fun _ ↦ 1 / 20) (n := 2)
  (fun _ _ ↦ by norm_num [abs_of_pos]) (fun _ _ ↦ by norm_num [abs_of_pos]) (by norm_num)

/-- The hypotheses of `exists_forwardSubstComputed_eq` hold together: unit roundoff `u = 1/10`,
the lower-triangular `l` with `l i j = 2` below the diagonal, `1` on it (so `l i i ≠ 0`) and `0`
above, `b i = 2 i + 1`, every rounding error `ε i j`, `δ i j` and `ρ i` equal to `1/20`, so at most
`u` in size and none zero, and `n = 2` rows, where `n u = 1/5 < 1`. Order LEAN-36's session
changed `b` from claude-ai's `b i = i + 1`, under which row 1's remainder is exactly `0`, so that
its subtraction and division roundings act on an exact zero; with `b i = 2 i + 1` every rounding
moves the computed solution. -/
example := ClassicalLean.Analysis.RoundingError.exists_forwardSubstComputed_eq (u := 1 / 10)
  (l := fun i j ↦ if j < i then 2 else if j = i then 1 else 0) (b := fun i ↦ 2 * i + 1)
  (ε := fun _ _ ↦ 1 / 20) (δ := fun _ _ ↦ 1 / 20) (ρ := fun _ ↦ 1 / 20) (n := 2)
  (fun i _ ↦ by simp)
  (fun _ _ _ _ ↦ by norm_num [abs_of_pos]) (fun _ _ _ _ ↦ by norm_num [abs_of_pos])
  (fun _ _ ↦ by norm_num [abs_of_pos]) (by norm_num)
