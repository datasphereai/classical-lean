/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Combinatorics.RecurrenceGeneratingFunction
import Mathlib.Probability.Moments.Covariance

/-!
# The Yule–Walker equations

An autoregression of order `p`: from time `p` on,
`X t = a₀ X (t − 1) + a₁ X (t − 2) + ⋯ + a_{p−1} X (t − p) + e t`,
where the noise `e t` is uncorrelated with every earlier value `X s`, `s < t`. Suppose the
process is covariance-stationary: the covariance of `X (s + k)` and `X s` is a number `γ k` that
does not depend on `s`. Then:

* `covariance_eq_sum` — for every lag `k ≥ 1`,
  `γ k = a₀ γ |k − 1| + a₁ γ |k − 2| + ⋯ + a_{p−1} γ |k − p|`
  (the Yule–Walker equations).
* `isSolution_autocovariance` — for `p ≥ 1`, the autocovariances `γ 0, γ 1, …` solve the linear
  recurrence `γ (n + p) = a_{p−1} γ n + ⋯ + a₀ γ (n + p − 1)` (Mathlib's `LinearRecurrence`, with
  the coefficients reversed).
* `exists_poly_mk_autocovariance_eq` — so their generating function `∑ γ n Xⁿ` is rational: a
  polynomial of degree less than `p` divided by `1 − a₀ X − a₁ X² − ⋯ − a_{p−1} X^p` (the library's
  `recDenom`, from `Combinatorics/RecurrenceGeneratingFunction`, present by order G-5).
* `durbinLevinson_spec` — item 140 of MATH-PLAN-library-2 (order LEAN-34): **the Durbin–Levinson
  recursion.** For an even `γ` whose Toeplitz matrix of size `n + 2` is positive definite, a
  solution `a` of the order-`n` prediction equations gives the order-`(n + 1)` solution `b` by
  `b j = a j − φ a (n − 1 − j)`, `b n = φ`, with error variance `v_{n+1} = v_n (1 − φ²) > 0`, where
  `v_n = γ 0 − ∑ a_j γ(j + 1)` and `φ = (γ(n + 1) − ∑ a_j γ(n − j)) / v_n`. The
  proof is the draft `d140-r1-s2` (written by Claude Opus 5.5 through the Anthropic Batch API, the
  lane's API-CREDIT-1 work), adapted by order LEAN-34's session: inside this namespace, two unused
  `simp` arguments removed, and a `show` that changed the goal written as `change`. Its witness
  is at the end of the file.

Nothing here says a stationary solution exists; it is assumed. The lag-`0` equation, which brings
in the noise variance, is not stated.

The equations are named after Yule (1927, Philosophical Transactions of the Royal Society A 226,
267–298) and Walker (1931, Proceedings of the Royal Society A 131, 518–532), by convention. Checked
for this order by web search: the two papers exist as cited; neither was read, so this file does not
claim that either states the general-`p` form proved here.

## Hypotheses

Measured in order LEAN-20's checks (check C25, exact rationals): 40 stationary autoregressions of
orders 1 to 3, built from exact covariances, where every hypothesis was verified and both
conclusions hold. Each hypothesis fails when dropped alone (the first three cases computed in the
checks, the others worked by hand and checked in review r25):

* `1 ≤ k`: at `k = 0` the true equation has the noise variance added; for `X t = X (t − 1)/2 + e t`
  with noise variance `1`, `γ 0 = 4/3` but `a₀ γ 1 = 1/3`.
* the noise uncorrelated with the past: `p = 1`, `a₀ = 0`, `X t = e t = Z t + Z (t − 1)` with `Z`
  uncorrelated of variance `1`: `γ 1 = 1` but `a₀ γ 0 = 0`.
* the recursion: `p = 1`, `a₀ = 0`, `e = 0`, `X t = Z` for every `t`: `γ 1 = 1`, `a₀ γ 0 = 0`.
* stationarity (that `γ` is the autocovariance): `p = 1`, `a₀ = 0`, `X = e = 0`,
  `γ = (0, 1, 0, …)`.
* `0 < p` in `isSolution_autocovariance`: with `p = 0`, `X = e` is white noise with `γ 0 = 1`, but a
  recurrence of order `0` says every term is `0`.

* `X t` square-integrable (review r25's case): on `[0, 1] × {±1}`, `X t = W + H t` with `W` the
  sign and `H t` a mean-zero function on `[2^(−t−1), 2^(−t))` that is integrable but not
  square-integrable; `p = 1`, `a₀ = 1`, `e t = H t − H (t − 1)`. Lean's junk value `0` for
  integrals that do not exist makes `γ = (0, 1, 1, …)` satisfy every other hypothesis, and
  `γ 1 = γ 0` fails.

The noise needs no separate square-integrability: from time `p` on, `e t` is `X t` minus a
combination of earlier `X`, and the noise before time `p` is never used.

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-20, `grep -rniE` over Mathlib):
`yule|walker|autoregress|autocovarian|autocorrelat` 1 line, an author's name. Used: Mathlib's
covariance algebra (`covariance_add_left`, `covariance_fun_sum_left`, `covariance_const_mul_left`,
`covariance_comm`) and `memLp_finsetSum`. The name `covariance_eq_sum` is the order's; a name
mentioning autoregression would say more (review r25).
-/

open MeasureTheory ProbabilityTheory

namespace ClassicalLean.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]

/-- **The Yule–Walker equations.** For a covariance-stationary autoregression of order `p`
(`X t = ∑ aᵢ X (t − 1 − i) + e t` from time `p` on, the noise `e t` uncorrelated with every
earlier `X s`, and `cov(X (s + k), X s) = γ k` for all `s` and `k`), every lag `k ≥ 1` has
`γ k = ∑ aᵢ γ |k − (i + 1)|`. Take the covariance of both sides of the recursion at time `p + k`
with `X p`; the noise term drops out. -/
theorem covariance_eq_sum {p : ℕ} {a : Fin p → ℝ} {X e : ℕ → Ω → ℝ} {γ : ℕ → ℝ}
    (hX : ∀ t, MemLp (X t) 2 μ)
    (hrec : ∀ t, p ≤ t → ∀ ω, X t ω = ∑ i : Fin p, a i * X (t - 1 - i) ω + e t ω)
    (hγ : ∀ s k, cov[X (s + k), X s; μ] = γ k)
    (hnoise : ∀ s t, s < t → cov[e t, X s; μ] = 0) {k : ℕ} (hk : 1 ≤ k) :
    γ k = ∑ i : Fin p, a i * γ (Int.natAbs ((k : ℤ) - ((i : ℕ) + 1))) := by
  have hXk : X (p + k) = (fun ω ↦ ∑ i : Fin p, a i * X (p + k - 1 - i) ω) + e (p + k) :=
    funext (hrec (p + k) (by omega))
  have hterm : ∀ i : Fin p, MemLp (fun ω ↦ a i * X (p + k - 1 - i) ω) 2 μ :=
    fun i ↦ (hX _).const_mul (a i)
  have hsum : MemLp (fun ω ↦ ∑ i : Fin p, a i * X (p + k - 1 - i) ω) 2 μ :=
    memLp_finsetSum (f := fun i ω ↦ a i * X (p + k - 1 - i) ω) _ fun i _ ↦ hterm i
  have he : MemLp (e (p + k)) 2 μ := by
    have : e (p + k) = X (p + k) - (fun ω ↦ ∑ i : Fin p, a i * X (p + k - 1 - i) ω) := by
      rw [hXk]; ext ω; simp
    rw [this]
    exact (hX _).sub hsum
  rw [← hγ p k, hXk, covariance_add_left hsum he (hX p),
    covariance_fun_sum_left (X := fun i ω ↦ a i * X (p + k - 1 - i) ω) hterm (hX p),
    hnoise p (p + k) (by omega), add_zero]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [covariance_const_mul_left]
  congr 1
  have hi := i.isLt
  by_cases hik : (i : ℕ) + 1 ≤ k
  · have h1 : p + k - 1 - i = p + (k - 1 - i) := by omega
    have h2 : Int.natAbs ((k : ℤ) - ((i : ℕ) + 1)) = k - 1 - i := by omega
    rw [h1, hγ, h2]
  · have h1 : p = (p + k - 1 - i) + (i + 1 - k) := by omega
    have h2 : Int.natAbs ((k : ℤ) - ((i : ℕ) + 1)) = i + 1 - k := by omega
    rw [h2, covariance_comm, ← hγ (p + k - 1 - i) (i + 1 - k), ← h1]

/-- **The autocovariances solve the autoregression's recurrence.** For `p ≥ 1`, under the
hypotheses of `covariance_eq_sum`, `γ (n + p) = ∑ⱼ a_{p−1−j} γ (n + j)` for every `n`: the
Yule–Walker equations at the lags `k = n + p ≥ p`, where `|k − (i + 1)| = k − 1 − i`. In Mathlib's
terms, `γ` is a solution of the `LinearRecurrence` of order `p` with coefficients `a` reversed. -/
theorem isSolution_autocovariance {p : ℕ} {a : Fin p → ℝ} {X e : ℕ → Ω → ℝ} {γ : ℕ → ℝ}
    (hX : ∀ t, MemLp (X t) 2 μ)
    (hrec : ∀ t, p ≤ t → ∀ ω, X t ω = ∑ i : Fin p, a i * X (t - 1 - i) ω + e t ω)
    (hγ : ∀ s k, cov[X (s + k), X s; μ] = γ k)
    (hnoise : ∀ s t, s < t → cov[e t, X s; μ] = 0) (hp : 0 < p) :
    (⟨p, fun j ↦ a j.rev⟩ : LinearRecurrence ℝ).IsSolution γ := by
  intro n
  change γ (n + p) = ∑ j : Fin p, a j.rev * γ (n + j)
  rw [covariance_eq_sum hX hrec hγ hnoise (k := n + p) (by omega)]
  refine (Fintype.sum_equiv Fin.revPerm _ _ fun i ↦ ?_)
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  congr 2
  have := i.isLt
  rw [Fin.val_rev]
  omega

/-- **The generating function of the autocovariances is rational.** Under the hypotheses of
`isSolution_autocovariance`, `∑ γ n Xⁿ = q · D⁻¹` for a polynomial `q` of degree less than `p`,
where `D = 1 − a₀ X − ⋯ − a_{p−1} X^p` is the library's `recDenom` for the recurrence (a unit of
the power series ring). The library's `exists_poly_mk_eq`, applied. -/
theorem exists_poly_mk_autocovariance_eq {p : ℕ} {a : Fin p → ℝ} {X e : ℕ → Ω → ℝ}
    {γ : ℕ → ℝ}
    (hX : ∀ t, MemLp (X t) 2 μ)
    (hrec : ∀ t, p ≤ t → ∀ ω, X t ω = ∑ i : Fin p, a i * X (t - 1 - i) ω + e t ω)
    (hγ : ∀ s k, cov[X (s + k), X s; μ] = γ k)
    (hnoise : ∀ s t, s < t → cov[e t, X s; μ] = 0) (hp : 0 < p) :
    ∃ q : Polynomial ℝ, (∀ j, p ≤ j → q.coeff j = 0) ∧
      PowerSeries.mk γ = (q : PowerSeries ℝ) *
        PowerSeries.invOfUnit (recDenom ⟨p, fun j ↦ a j.rev⟩) 1 :=
  exists_poly_mk_eq _ γ (isSolution_autocovariance hX hrec hγ hnoise hp)

open Finset in
/-- A solution `c` of the order-`m` prediction equations has positive error variance, when the
Toeplitz matrix of size `N > m` is positive definite. -/
private theorem pos_of_pred {γ : ℤ → ℝ} (hγ : ∀ z, γ (-z) = γ z) {m N : ℕ} (hmN : m + 1 ≤ N)
    (hpos : ∀ x : ℕ → ℝ, (∃ i < N, x i ≠ 0) →
      0 < ∑ i ∈ range N, ∑ j ∈ range N, x i * x j * γ ((i : ℤ) - j))
    {c : ℕ → ℝ}
    (hc : ∀ i : ℕ, 1 ≤ i → i ≤ m → ∑ j ∈ range m, c j * γ ((i : ℤ) - ((j : ℤ) + 1)) = γ i) :
    0 < γ 0 - ∑ j ∈ range m, c j * γ ((j : ℤ) + 1) := by
  set x : ℕ → ℝ := fun i => if i = 0 then 1 else if i ≤ m then -c (i - 1) else 0 with hx
  have hx0 : x 0 = 1 := by simp [hx]
  have hxs : ∀ j, j < m → x (j + 1) = -c j := by
    intro j hj
    simp [hx, show j + 1 ≤ m by omega]
  have hxz : ∀ i, m < i → x i = 0 := by
    intro i hi
    simp [hx, show i ≠ 0 by omega, show ¬ i ≤ m by omega]
  have hsub : range (m + 1) ⊆ range N := fun i hi =>
    Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega)
  have hred : ∑ i ∈ range N, ∑ j ∈ range N, x i * x j * γ ((i : ℤ) - j)
      = ∑ i ∈ range (m + 1), ∑ j ∈ range (m + 1), x i * x j * γ ((i : ℤ) - j) := by
    symm
    calc ∑ i ∈ range (m + 1), ∑ j ∈ range (m + 1), x i * x j * γ ((i : ℤ) - j)
        = ∑ i ∈ range (m + 1), ∑ j ∈ range N, x i * x j * γ ((i : ℤ) - j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_subset hsub fun j _ hj => by
            rw [hxz j (by by_contra h; exact hj (Finset.mem_range.mpr (by omega)))]; ring
      _ = ∑ i ∈ range N, ∑ j ∈ range N, x i * x j * γ ((i : ℤ) - j) :=
          Finset.sum_subset hsub fun i _ hi => Finset.sum_eq_zero fun j _ => by
            rw [hxz i (by by_contra h; exact hi (Finset.mem_range.mpr (by omega)))]; ring
  have hinner : ∀ i : ℕ, ∑ j ∈ range (m + 1), x j * γ ((i : ℤ) - j)
      = γ i - ∑ j ∈ range m, c j * γ ((i : ℤ) - ((j : ℤ) + 1)) := by
    intro i
    have h1 : ∑ j ∈ range m, x (j + 1) * γ ((i : ℤ) - ((j + 1 : ℕ) : ℤ))
        = -∑ j ∈ range m, c j * γ ((i : ℤ) - ((j : ℤ) + 1)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hxs j (Finset.mem_range.mp hj), Nat.cast_add, Nat.cast_one]
      ring
    rw [Finset.sum_range_succ', h1, hx0, Nat.cast_zero, sub_zero, one_mul]
    ring
  have hQ : ∑ i ∈ range (m + 1), ∑ j ∈ range (m + 1), x i * x j * γ ((i : ℤ) - j)
      = ∑ i ∈ range (m + 1),
          x i * (γ i - ∑ j ∈ range m, c j * γ ((i : ℤ) - ((j : ℤ) + 1))) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hinner i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hz : ∑ i ∈ range m, x (i + 1) * (γ ((i + 1 : ℕ) : ℤ)
      - ∑ j ∈ range m, c j * γ (((i + 1 : ℕ) : ℤ) - ((j : ℤ) + 1))) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      have := Finset.mem_range.mp hi
      rw [hc (i + 1) (by omega) (by omega), sub_self, mul_zero]
  have hz2 : ∑ j ∈ range m, c j * γ (((0 : ℕ) : ℤ) - ((j : ℤ) + 1))
      = ∑ j ∈ range m, c j * γ ((j : ℤ) + 1) :=
    Finset.sum_congr rfl fun j _ => by rw [Nat.cast_zero, zero_sub, hγ]
  have key := hpos x ⟨0, by omega, by rw [hx0]; exact one_ne_zero⟩
  rw [hred, hQ, Finset.sum_range_succ', hz, zero_add, hx0, one_mul, hz2, Nat.cast_zero] at key
  exact key

open Finset in
/-- **The Durbin–Levinson recursion** (item 140 of MATH-PLAN-library-2; the draft `d140-r1-s2`,
written by Claude Opus 5.5 through the Anthropic Batch API, the lane's API-CREDIT-1 work, adapted by
order LEAN-34's session). Let `γ` be even with positive definite Toeplitz matrix
`(γ(i − j))_{i,j < n+2}`, and let `a` (with `a j = φ_{n,j+1}`) solve the order-`n` prediction
equations `∑_j a_j γ(i − (j+1)) = γ i`, `1 ≤ i ≤ n`. Put
`φ = (γ(n+1) − ∑ a_j γ(n − j)) / v_n` with `v_n = γ 0 − ∑ a_j γ(j+1)`, and
`b_j = a_j − φ a_{n−1−j}` for `j < n`, `b_n = φ`. Then `b` solves the order-`(n+1)` equations,
its error variance is `v_{n+1} = v_n (1 − φ²)`, and `v_{n+1} > 0`. The hypothesis `hpos` is the
positive definiteness of the Toeplitz matrix written out as a quadratic form
(`∑ᵢ ∑ⱼ xᵢ xⱼ γ(i − j) > 0` for every `x` that is not zero below `n + 2`), not as Mathlib's
`Matrix.PosDef`; `γ` is any even function, not only the autocovariance of a process. -/
theorem durbinLevinson_spec {γ : ℤ → ℝ} (hγ : ∀ z, γ (-z) = γ z) {n : ℕ}
    (hpos : ∀ x : ℕ → ℝ, (∃ i < n + 2, x i ≠ 0) →
      0 < ∑ i ∈ range (n + 2), ∑ j ∈ range (n + 2), x i * x j * γ ((i : ℤ) - j))
    {a : ℕ → ℝ}
    (ha : ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ∑ j ∈ range n, a j * γ ((i : ℤ) - ((j : ℤ) + 1)) = γ i)
    {φ : ℝ} (hφ : φ = (γ ((n : ℤ) + 1) - ∑ j ∈ range n, a j * γ ((n : ℤ) - j)) /
      (γ 0 - ∑ j ∈ range n, a j * γ ((j : ℤ) + 1)))
    {b : ℕ → ℝ} (hb : ∀ j < n, b j = a j - φ * a (n - 1 - j)) (hbn : b n = φ) :
    (∀ i : ℕ, 1 ≤ i → i ≤ n + 1 →
      ∑ j ∈ range (n + 1), b j * γ ((i : ℤ) - ((j : ℤ) + 1)) = γ i) ∧
    γ 0 - ∑ j ∈ range (n + 1), b j * γ ((j : ℤ) + 1) =
      (γ 0 - ∑ j ∈ range n, a j * γ ((j : ℤ) + 1)) * (1 - φ ^ 2) ∧
    0 < γ 0 - ∑ j ∈ range (n + 1), b j * γ ((j : ℤ) + 1) := by
  have hva : 0 < γ 0 - ∑ j ∈ range n, a j * γ ((j : ℤ) + 1) :=
    pos_of_pred hγ (by omega : n + 1 ≤ n + 2) hpos ha
  have hv := hva.ne'
  have hkey : φ * (γ 0 - ∑ j ∈ range n, a j * γ ((j : ℤ) + 1))
      = γ ((n : ℤ) + 1) - ∑ j ∈ range n, a j * γ ((n : ℤ) - j) := by
    rw [hφ, div_mul_eq_mul_div, mul_div_assoc, div_self hv, mul_one]
  have hrefl : ∀ i : ℤ, ∑ j ∈ range n, a (n - 1 - j) * γ (i - ((j : ℤ) + 1))
      = ∑ j ∈ range n, a j * γ (((n : ℤ) + 1 - i) - ((j : ℤ) + 1)) := by
    intro i
    refine Eq.trans ?_
      (Finset.sum_range_reflect (fun j => a j * γ (((n : ℤ) + 1 - i) - ((j : ℤ) + 1))) n)
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < n := Finset.mem_range.mp hj
    have hc : ((n - 1 - j : ℕ) : ℤ) = (n : ℤ) - 1 - j := by omega
    change a (n - 1 - j) * γ (i - ((j : ℤ) + 1))
      = a (n - 1 - j) * γ (((n : ℤ) + 1 - i) - (((n - 1 - j : ℕ) : ℤ) + 1))
    rw [hc, show (n : ℤ) + 1 - i - ((n : ℤ) - 1 - j + 1) = -(i - ((j : ℤ) + 1)) by ring, hγ]
  have hsplit : ∀ i : ℤ, ∑ j ∈ range (n + 1), b j * γ (i - ((j : ℤ) + 1))
      = ∑ j ∈ range n, a j * γ (i - ((j : ℤ) + 1))
        - φ * ∑ j ∈ range n, a j * γ (((n : ℤ) + 1 - i) - ((j : ℤ) + 1))
        + φ * γ (i - ((n : ℤ) + 1)) := by
    intro i
    rw [Finset.sum_range_succ, hbn, ← hrefl i, Finset.mul_sum, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hb j (Finset.mem_range.mp hj)]
    ring
  have hPn : ∑ j ∈ range n, a j * γ (((n : ℤ) + 1) - ((j : ℤ) + 1))
      = ∑ j ∈ range n, a j * γ ((n : ℤ) - j) :=
    Finset.sum_congr rfl fun j _ => by
      rw [show ((n : ℤ) + 1) - ((j : ℤ) + 1) = (n : ℤ) - j by ring]
  have hP0 : ∑ j ∈ range n, a j * γ (0 - ((j : ℤ) + 1))
      = ∑ j ∈ range n, a j * γ ((j : ℤ) + 1) :=
    Finset.sum_congr rfl fun j _ => by rw [zero_sub, hγ]
  have heq : ∀ i : ℕ, 1 ≤ i → i ≤ n + 1 →
      ∑ j ∈ range (n + 1), b j * γ ((i : ℤ) - ((j : ℤ) + 1)) = γ i := by
    intro i hi1 hi2
    rw [hsplit]
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · have e1 := ha i hi1 (by omega)
      have e2 := ha (n + 1 - i) (by omega) (by omega)
      have hc : ((n + 1 - i : ℕ) : ℤ) = (n : ℤ) + 1 - i := by omega
      rw [hc] at e2
      have e3 : γ ((i : ℤ) - ((n : ℤ) + 1)) = γ ((n : ℤ) + 1 - i) := by
        rw [show (i : ℤ) - ((n : ℤ) + 1) = -((n : ℤ) + 1 - i) by ring, hγ]
      rw [e1, e2, e3]
      ring
    · have hi : (i : ℤ) = (n : ℤ) + 1 := by omega
      rw [hi, show (n : ℤ) + 1 - ((n : ℤ) + 1) = 0 by ring, hPn, hP0]
      linear_combination hkey
  have hvar : γ 0 - ∑ j ∈ range (n + 1), b j * γ ((j : ℤ) + 1) =
      (γ 0 - ∑ j ∈ range n, a j * γ ((j : ℤ) + 1)) * (1 - φ ^ 2) := by
    have h0 := hsplit 0
    have hl : ∑ j ∈ range (n + 1), b j * γ ((j : ℤ) + 1)
        = ∑ j ∈ range (n + 1), b j * γ (0 - ((j : ℤ) + 1)) :=
      Finset.sum_congr rfl fun j _ => by rw [zero_sub, hγ]
    rw [hl, h0, hP0, show (n : ℤ) + 1 - 0 = (n : ℤ) + 1 by ring, hPn,
      show (0 : ℤ) - ((n : ℤ) + 1) = -((n : ℤ) + 1) by ring, hγ ((n : ℤ) + 1)]
    linear_combination φ * hkey
  exact ⟨heq, hvar, pos_of_pred hγ (by omega : n + 1 + 1 ≤ n + 2) hpos heq⟩

end ClassicalLean.Probability

open Finset in
/-- The hypotheses of `durbinLevinson_spec` hold together: order `n = 2`; the even function
`γ 0 = 1`, `γ z = 1/2` for `z ≠ 0` (not `0` past any lag), whose Toeplitz matrix of size `4` is
positive definite, its quadratic form being `½ ∑ xᵢ² + ½ (∑ xᵢ)²`; `a = (1/3, 1/3)`, which
solves both order-2 equations, with error variance `v₂ = 2/3`; `φ = 1/4`, from its formula; and
`b = (1/4, 1/4, 1/4)`, which meets `b j = a j − φ a (1 − j)` and `b 2 = φ`. -/
example := ClassicalLean.Probability.durbinLevinson_spec
  (γ := fun z ↦ if z = 0 then 1 else 1 / 2) (fun z ↦ by simp)
  (n := 2)
  (fun x ⟨i, hi, hx⟩ ↦ by
    simp only [sum_range_succ, sum_range_zero]
    norm_num
    interval_cases i
    all_goals nlinarith [mul_self_pos.mpr hx, sq_nonneg (x 0 + x 1 + x 2 + x 3), sq_nonneg (x 0),
      sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)])
  (a := fun _ ↦ 1 / 3)
  (fun i hi1 hi2 ↦ by
    interval_cases i <;> simp only [sum_range_succ, sum_range_zero] <;> norm_num)
  (φ := 1 / 4) (by simp only [sum_range_succ, sum_range_zero]; norm_num)
  (b := fun _ ↦ 1 / 4) (fun j hj ↦ by norm_num) rfl
