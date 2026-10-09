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

end ClassicalLean.Probability
