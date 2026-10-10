/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.InformationTheory.Coding.Kraft
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# A code is a bet: compression as a test against a null law fixed in advance

Write a record of `n` trials as a string `x` of wins (`true`) and losses (`false`). A prefix-free
code `c` turns each string into a word of `L x = |c x|` bits. Given a null law `p₀` on strings,
fixed before the data are seen, the **score** of a string is `2^(−L x) / p₀ {x}`: how much more
weight the code gives `x` than the null law does. Order LEAN-26, item 68 of the plan, in the form
of the ruling sent during that order.

* `sum_inv_two_pow_length_le_one`: Kraft's inequality, `∑ x, 2^(−L x) ≤ 1`.
* `integral_score_le_one`: the score has mean at most `1` under `p₀`, for any finite measure
  `p₀`. With `score_nonneg`, the score is an e-value: a nonnegative quantity whose mean under the
  null is at most `1`, the kind `EValueStepUp`'s `integral_eFalseShare_le` takes (nonnegative,
  integrable, mean at most `1`). No Lean lemma here joins the two; the plan's "feeds EValueStepUp"
  is that match of hypotheses.
* `measureReal_score_ge_le`: so, for `α > 0`, the chance under `p₀` that the score is at least
  `1 / α` is at most `α` (Markov's inequality). Rejecting the null when the score reaches `1 / α`
  is a test whose false-alarm rate is at most `α`.
* `bernProd n p`: the law of `n` independent trials, each a win with chance `p`.
  `bernProd_real_singleton` gives its mass on a string, `∏ i, (p if a win, else 1 − p)`, and
  `integral_score_bernProd_le_one`, `measureReal_score_bernProd_ge_le` are the two statements
  above for this null law.
* `measureReal_len_add_le_le`: for the fair coin (`p = 1/2`, `fairCoin`), the chance that a string
  compresses by `k` bits or more, `L x + k ≤ n`, is at most `2^(−k)`.

**The Lean statements.** Strings of length `n` are `Fin n → Bool`. A prefix-free code on them is
`c : (Fin n → Bool) → List Bool` with `Function.Injective c` (different strings get different
words) and `InformationTheory.IsPrefixFree (Set.range c)` (no word begins another; Mathlib's
definition). "Compresses by `k` bits" is `(c x).length + k ≤ n`, with no subtraction, so no
truncation in `ℕ` can enter. The win rate `p` of `bernProd n p` is a constant of the statement:
it may not depend on `x`, which is what "fixed in advance" means here.

**What a rejection means.** A rejection says "not this null law". Under `bernProd n p` it can come
from clumping (trials that depend on each other), from a win rate other than `p`, or from both.
The test does not isolate clumping. Exact example (order LEAN-26's checks, line C7): independent
trials with win rate `3/5`, nothing clumped, the fair-coin test at `α = 1/8` (`k = 3`) with a
two-part code (the number of wins in `⌈log₂ (n + 1)⌉` bits, then which string with that many wins
in `⌈log₂ C(n, wins)⌉` bits; Kraft sum at most `1`, line C6) rejects with chance `0.4161` at
`n = 200`, `0.9068` at `n = 500`, `0.9991` at `n = 1000` and above `0.9999` at `n = 2000`; under the
fair coin the same test rejects with chance below `0.0023` each time.

**Estimating `p` from the same trades.** The rate `α` is proved for a `p` fixed in advance. The
ruling sent during order LEAN-26 says that estimating `p` from the same trades breaks it; the
checks (exact, lines C8 and C9) and the argument below support a narrower statement: what breaks
the rate is letting the data choose the code without paying for the choice, while plugging an
estimate into the null law does not:

* fitting the code to the estimated win rate without sending the count, `L x = ⌈n H₂(p̂)⌉` with
  `p̂` the share of wins in `x` and `H₂` the binary entropy, at `n = 2`: lengths `0, 2, 2, 0`, Kraft
  sum `5/2 > 1`, and under the fair coin "compresses by `2` bits" has chance `1/2 > 1/4`. This
  "code" breaks Kraft's inequality, the same failure as dropping the prefix-free or injective
  hypothesis below; sending the count first (the two-part code above) restores it.
* putting the estimate into the null law with a fixed code, score `2^(−L x) / P_{p̂(x)} {x}`: the
  maximum-likelihood rate `p̂(x)` gives the observed string at least the mass any fixed `p` gives
  it, so this score is at most the score for every fixed `p`, and its rejections are among the
  fixed-`p` test's rejections: the false-alarm rate stays at most `α` under every Bernoulli law
  (since `P_{p̂(x)} {x} = 2^(−n H₂(p̂(x)))`, it rejects when `L x + k ≤ n H₂(p̂(x))`). This
  argument is by hand, not proved in Lean; as a cross-check, every string up to `n = 8`, true
  `p ∈ {1/2, 1/3, 3/5}` and `α ∈ {1/2, 1/4, 1/8}` gave a false-alarm rate of at most `α`.

**Hypotheses** (order LEAN-26's checks, lines C1 to C5, exact):

* prefix-free: the injective code with words `[]`, `[0]`, `[1]`, `[0, 0]` at `n = 2` has Kraft sum
  `9/4`, and "compresses by `1` bit" has fair-coin chance `3/4 > 1/2`.
* injective: the code sending every string to `[]` has a prefix-free image `{[]}`, Kraft sum `4`
  over the strings at `n = 2`, and "compresses by `2` bits" has chance `1 > 1/4`.
* `α > 0`: at `α = 0`, Lean's `1 / 0 = 0` and every score is at least `0`, so the chance is
  `1 > 0`.
* The ruling's `p₀ x > 0` for every `x` is not needed for the two statements: a string with
  `p₀ {x} = 0` has Lean's score `2^(−L x) / 0 = 0` and adds nothing to either side. For such a
  string the score is not the ratio it stands for; the null law gives those strings no weight.
* The plan's run-length code (first bit, then the number of runs and each run length in Elias
  gamma code) meets Kraft and the fair-coin bound for every `n ≤ 12` (line C1).

## What Mathlib provides

Kraft's inequality (`InformationTheory.IsPrefixFree.finsetSum_one_div_card_pow_length_le_one`),
`ProbabilityTheory.bernoulliMeasure`, `Measure.pi` and `Measure.pi_pi`, `integral_fintype` and
Markov's inequality `mul_meas_ge_le_integral_of_nonneg`. The library's `SourceCoding` uses the
same Kraft inequality for Shannon's bounds. Mathlib v4.34.0 has no compression test: `compress`
finds only set-family compressions (order LEAN-26's search).
-/

open MeasureTheory Finset

namespace ClassicalLean.InformationTheory.CompressionTest

variable {n : ℕ}

/-- The score of a string: `2^(−L x) / p₀ {x}`. -/
noncomputable def score (c : (Fin n → Bool) → List Bool) (p₀ : Measure (Fin n → Bool))
    (x : Fin n → Bool) : ℝ :=
  (2 : ℝ)⁻¹ ^ (c x).length / p₀.real {x}

/-- **Kraft's inequality** for a prefix-free code on the strings of length `n`. -/
theorem sum_inv_two_pow_length_le_one {c : (Fin n → Bool) → List Bool}
    (hc : Function.Injective c) (hpf : InformationTheory.IsPrefixFree (Set.range c)) :
    ∑ x, (2 : ℝ)⁻¹ ^ (c x).length ≤ 1 := by
  classical
  have hS : ((univ.image c : Finset (List Bool)) : Set (List Bool)) = Set.range c := by simp
  have := (hS ▸ hpf).finsetSum_one_div_card_pow_length_le_one
  rw [sum_image fun i _ j _ h ↦ hc h] at this
  simpa using this

/-- The score is never negative. -/
lemma score_nonneg (c : (Fin n → Bool) → List Bool) (p₀ : Measure (Fin n → Bool))
    (x : Fin n → Bool) : 0 ≤ score c p₀ x :=
  div_nonneg (by positivity) measureReal_nonneg

/-- **A code is a bet.** Under any null law `p₀` (a finite measure on the strings), the score
`2^(−L x) / p₀ {x}` has mean at most `1`. -/
theorem integral_score_le_one {c : (Fin n → Bool) → List Bool}
    (hc : Function.Injective c) (hpf : InformationTheory.IsPrefixFree (Set.range c))
    (p₀ : Measure (Fin n → Bool)) [IsFiniteMeasure p₀] :
    ∫ x, score c p₀ x ∂p₀ ≤ 1 := by
  rw [integral_fintype Integrable.of_finite]
  refine le_trans (sum_le_sum fun x _ ↦ ?_) (sum_inv_two_pow_length_le_one hc hpf)
  rw [smul_eq_mul, score]
  rcases (measureReal_nonneg (μ := p₀) (s := {x})).eq_or_lt with h | h
  · rw [← h]; simp
  · rw [mul_div_cancel₀ _ h.ne']

/-- **The false-alarm rate.** Under the null law `p₀`, the chance that the score reaches `1 / α`
is at most `α`, for every `α > 0`. -/
theorem measureReal_score_ge_le {c : (Fin n → Bool) → List Bool}
    (hc : Function.Injective c) (hpf : InformationTheory.IsPrefixFree (Set.range c))
    (p₀ : Measure (Fin n → Bool)) [IsFiniteMeasure p₀] {α : ℝ} (hα : 0 < α) :
    p₀.real {x | 1 / α ≤ score c p₀ x} ≤ α := by
  have h := mul_meas_ge_le_integral_of_nonneg (μ := p₀) (ae_of_all _ (score_nonneg c p₀))
    Integrable.of_finite (1 / α)
  have h1 := h.trans (integral_score_le_one hc hpf p₀)
  rwa [one_div_mul_eq_div, div_le_iff₀ hα, one_mul] at h1

/-- `n` independent trials, each a win (`true`) with chance `p`. -/
noncomputable def bernProd (n : ℕ) (p : unitInterval) : Measure (Fin n → Bool) :=
  Measure.pi fun _ ↦ ProbabilityTheory.bernoulliMeasure true false p

/-- The law of the trials is a probability measure. -/
instance (p : unitInterval) : IsProbabilityMeasure (bernProd n p) := by
  unfold bernProd; infer_instance

/-- The mass of one string under `n` independent trials with win rate `p`. -/
theorem bernProd_real_singleton (p : unitInterval) (x : Fin n → Bool) :
    (bernProd n p).real {x} = ∏ i, if x i then (p : ℝ) else 1 - p := by
  rw [bernProd, ← Set.univ_pi_singleton, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  refine prod_congr rfl fun i _ ↦ ?_
  rw [← measureReal_def]
  cases x i <;> simp

/-- **A code is a bet, against independent trials with win rate `p`.** -/
theorem integral_score_bernProd_le_one {c : (Fin n → Bool) → List Bool}
    (hc : Function.Injective c) (hpf : InformationTheory.IsPrefixFree (Set.range c))
    (p : unitInterval) : ∫ x, score c (bernProd n p) x ∂(bernProd n p) ≤ 1 :=
  integral_score_le_one hc hpf _

/-- **The false-alarm rate against independent trials with win rate `p`**, `p` fixed in advance. -/
theorem measureReal_score_bernProd_ge_le {c : (Fin n → Bool) → List Bool}
    (hc : Function.Injective c) (hpf : InformationTheory.IsPrefixFree (Set.range c))
    (p : unitInterval) {α : ℝ} (hα : 0 < α) :
    (bernProd n p).real {x | 1 / α ≤ score c (bernProd n p) x} ≤ α :=
  measureReal_score_ge_le hc hpf _ hα

/-- The fair coin, `p = 1/2`. -/
noncomputable def fairCoin : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

/-- Under the fair coin every string has mass `2^(−n)`. -/
theorem bernProd_fairCoin_real_singleton (x : Fin n → Bool) :
    (bernProd n fairCoin).real {x} = (2 : ℝ)⁻¹ ^ n := by
  rw [bernProd_real_singleton]
  have : ∀ i, (if x i then ((fairCoin : unitInterval) : ℝ) else 1 - fairCoin) = 2⁻¹ := fun i ↦ by
    cases x i <;> norm_num [fairCoin]
  simp [this]

/-- **Compression under the fair coin.** The chance that a string compresses by `k` bits or more,
`L x + k ≤ n`, is at most `2^(−k)`. -/
theorem measureReal_len_add_le_le {c : (Fin n → Bool) → List Bool}
    (hc : Function.Injective c) (hpf : InformationTheory.IsPrefixFree (Set.range c)) (k : ℕ) :
    (bernProd n fairCoin).real {x | (c x).length + k ≤ n} ≤ (2 : ℝ)⁻¹ ^ k := by
  refine le_trans (measureReal_mono fun x hx ↦ ?_)
    (measureReal_score_bernProd_ge_le hc hpf fairCoin (α := (2 : ℝ)⁻¹ ^ k) (by positivity))
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [score, bernProd_fairCoin_real_singleton, one_div, ← inv_pow, inv_inv,
    le_div_iff₀ (by positivity)]
  have h1 : (2 : ℝ)⁻¹ ^ n ≤ 2⁻¹ ^ ((c x).length + k) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hx
  calc (2 : ℝ) ^ k * 2⁻¹ ^ n ≤ 2 ^ k * 2⁻¹ ^ ((c x).length + k) := by gcongr
    _ = 2⁻¹ ^ (c x).length := by
      rw [pow_add, mul_comm, mul_assoc, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow, mul_one]

end ClassicalLean.InformationTheory.CompressionTest
