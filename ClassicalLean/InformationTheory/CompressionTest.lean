/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.InformationTheory.Coding.Kraft
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import ClassicalLean.Probability.EValueStepUp

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
  integrable, mean at most `1`).
* `integral_eFalseShare_score_le` (order LEAN-28, item 88): many such tests at once. Test `i` reads
  its own string `X i ω` (of its own length) with its own code `c i` and its own null law `p₀ i`,
  all fixed in advance. Feed the scores to e-BH at level `q > 0` (`EValueStepUp`: with `m` tests,
  reject every test whose score is at least `m / (q k)`, where `k` is the largest count that works):
  if, for every true null `i ∈ H`, the code is injective and prefix-free and the string's law is
  `p₀ i`, the mean share of the rejections that fall in `H` is at most `q`, however the tests depend
  on each other; `integral_eFalseShare_score_le_mul_card_div` gives the sharper `q · |H| / m`, where
  `|H|` is the number of true nulls. The mean is taken under a probability measure `μ`. Nothing is
  assumed about the tests outside `H`.
* `measureReal_score_ge_le`: so, for `α > 0`, the chance under `p₀` that the score is at least
  `1 / α` is at most `α` (Markov's inequality). Rejecting the null when the score reaches `1 / α`
  is a test whose false-alarm rate is at most `α`.
* `bernProd n p`: the law of `n` independent trials, each a win with chance `p`.
  `bernProd_real_singleton` gives its mass on a string, `∏ i, (p if a win, else 1 − p)`, and
  `integral_score_bernProd_le_one`, `measureReal_score_bernProd_ge_le` are the two statements
  above for this null law.
* `measureReal_len_add_le_le`: for the fair coin (`p = 1/2`, `fairCoin`), the chance that a string
  compresses by `k` bits or more, `L x + k ≤ n`, is at most `2^(−k)`.
* `winRate`, `score_plugIn_le`, `measureReal_score_plugIn_ge_le` (order LEAN-30, item 99): the
  plug-in score, with the string's own win rate put into the null law, is at most every
  fixed-rate score, and its false-alarm rate stays at most `α` under every Bernoulli law. See
  "Estimating `p` from the same trades" below.

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
  (since `P_{p̂(x)} {x} = 2^(−n H₂(p̂(x)))`, it rejects when `L x + k ≤ n H₂(p̂(x))`). Order
  LEAN-30 (item 99) proves both steps: `score_plugIn_le` and `measureReal_score_plugIn_ge_le`,
  with the plug-in rate `winRate`, by the weighted arithmetic–geometric mean inequality; as a
  cross-check, every string up to `n = 8`, true
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

**Hypotheses of the e-BH statements** (order LEAN-28's checks, exact, one test unless said):

* `q > 0`: at `q = 0`, with strings of length `0` (one string, score `1`), Lean's `1 / (0 · 1) = 0`
  makes the test reject always: mean false share `1 > 0`.
* the code injective, for a null: every string of length `2` sent to `[]`, fair coin, `q = 1/4`:
  every score is `4`, the test always rejects, `1 > 1/4`.
* the code prefix-free, for a null: words `[]`, `[0]`, `[1]`, `[0, 0]` at length `2`, fair coin,
  `q = 1/2`: scores `4, 2, 2, 1`, three of four strings rejected, `3/4 > 1/2`.
* the null law is the string's law: the string is always `[true]` (length `1`), the null law is
  win rate `1/8`, code `x ↦ [x 0]`, `q = 1/4`: score `(1/2) / (1/8) = 4`, always rejected,
  `1 > 1/4`.
* a probability measure (the share's mean is an expected value): needed, through Lean's junk law of
  a string that is not almost everywhere measurable. Mathlib's `μ.map (X i)` is then a point mass of
  mass `1` whatever the mass of `μ` (`Measure.map_of_not_aemeasurable_of_ne_zero`). On `Bool` with
  the σ-algebra `⊥` and `μ` five times the point mass at `true`, take two nulls with code
  `x ↦ [x 0]`: the first string equals Mathlib's junk point (`Classical.ofNonempty`) only at `true`,
  the second only at `false`. Under `⊥` the only measurable sets are `∅` and `Bool`, and `μ` gives
  every nonempty set measure `5`, so only a constant string is almost everywhere measurable, and
  neither of these is. Their scores are `(1/2, 0)` and `(0, 1/2)`; at `q = 4` e-BH rejects one null
  at every outcome: the integral of the false share is `5 > 4 = q` (`= q · |H| / m`). When every
  null string is measurable a finite measure would do (each score has integral at most `1`); not
  stated here.
* Lean's junk values decide three cases and keep the statements true: a string with null mass `0`
  has score `2^(−L) / 0 = 0`; for a string that is not almost everywhere measurable the null law is
  that point mass, so its score is at most `1` everywhere (`2^(−L) / 1` at the point, Lean's
  `2^(−L) / 0 = 0` elsewhere), and the proof bounds it by the constant `1`; and if the share itself
  is not almost everywhere measurable (a test outside `H` may read a string that is not measurable),
  Lean's integral of it is `0`. The bound holds all the same: at every outcome the share is at most
  `q / m` times a sum of integrable functions, one per true null, each with integral at most `1`.

**Hypotheses of the plug-in statements** (order LEAN-30, item 99; its exact checks, lane
`lean/LEAN-30-checks.py`, each case keeping the other hypotheses, codes written out by their words):

* `score_plugIn_le`, the fixed rate gives `x` positive mass (`99.drop.hx`): `n = 1`, `p = 0`, the
  string "win" with a word of length `1`: plug-in score `1/2` against Lean's fixed score
  `2⁻¹ / 0 = 0`. Not a narrowing: the plan's sentence is false there under Lean's junk value, and
  the rate theorem needs no such hypothesis (those strings have mass `0` under `p`).
* the code injective (`99.drop.hc`): every string of length `2` sent to `[]` (prefix-free, not
  injective), fair coin, `α = 1/4`: chance `1/2`.
* the code prefix-free (`99.drop.hpf`): `n = 3`, the injective words `[]`, `[0]`, `[1]` on three
  strings with both a win and a loss (Kraft sum `25/8`), fair coin, `α = 1/3`: chance `3/8`.
* `α > 0` (`99.drop.halpha`): the code writing each string of length `2` out as it is, `α = 0`:
  Lean's `1 / 0 = 0` is at most every score, chance `1`.

Lean's `0 / 0 = 0` makes the plug-in rate `0` at `n = 0`; there is one empty string, of mass `1`
under every rate, so it decides nothing. Also measured exactly: the maximum-likelihood step for
`n ≤ 10` (`99.ml`), the scores for `n ≤ 6` (`99.score`) and the rate for `n ≤ 8`, five levels `α`
and two codes (`99.rate`). The plan's search (`MATH-PLAN-library-2-checks.py`, line `row.L3`:
`maximum.likelihood|plug-in estimate`) found 0 lines in pinned Mathlib and in Mathlib master at
`2da3ab0a`, and 1 line in the library (this module's paragraph above) when order LEAN-30 began.

## What Mathlib provides

Kraft's inequality (`InformationTheory.IsPrefixFree.finsetSum_one_div_card_pow_length_le_one`),
`ProbabilityTheory.bernoulliMeasure`, `Measure.pi` and `Measure.pi_pi`, `integral_fintype` and
Markov's inequality `mul_meas_ge_le_integral_of_nonneg`. The library's `SourceCoding` uses the same
Kraft inequality for Shannon's bounds. Item 88 also uses
`Measure.map_of_not_aemeasurable_of_ne_zero` (the image of a nonzero measure under a map that is not
almost everywhere measurable is a point mass of mass `1`), `integral_map`, `integrable_map_measure`,
`integral_mono_of_nonneg` and `integral_finsetSum`. Mathlib v4.34.0 has no compression test:
`compress` finds only set-family compressions (order LEAN-26's search).
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

/-! ### The estimated rate put into the null law (order LEAN-30, item 99) -/

/-- The share of wins in a string, `k / n` with `k` the number of wins (Lean's `0` at `n = 0`); as a
`unitInterval`, a win rate (order LEAN-30, item 99). -/
noncomputable def winRate (x : Fin n → Bool) : unitInterval :=
  ⟨((univ.filter fun i ↦ x i = true).card : ℝ) / n, by positivity,
    div_le_one_of_le₀ (by exact_mod_cast (card_filter_le _ _).trans (by simp)) (by positivity)⟩

/-- The maximum-likelihood step: `p ^ K (1 − p) ^ M ≤ q ^ K (1 − q) ^ M` for `q = K / (K + M)`, by
the weighted arithmetic–geometric mean inequality at the points `p / q`, `(1 − p) / (1 − q)` with
weights `q`, `1 − q`, raised to the power `K + M` (`0 ^ 0 = 1`; at `K = 0` or `M = 0` the right side
is `1`). -/
private theorem pow_mul_pow_le_winRate (K M : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p ^ K * (1 - p) ^ M ≤ ((K : ℝ) / (K + M)) ^ K * (1 - (K : ℝ) / (K + M)) ^ M := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simpa using pow_le_one₀ (sub_nonneg.2 hp1) (by linarith)
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
    simpa [div_self hK0] using pow_le_one₀ hp0 hp1
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hN : (0 : ℝ) < K + M := by positivity
  have h1q : 1 - (K : ℝ) / (K + M) = M / (K + M) := by field_simp; ring
  rw [h1q]
  set q := (K : ℝ) / (K + M) with hqdef
  set r := (M : ℝ) / (K + M) with hrdef
  have hq : 0 < q := div_pos hKr hN
  have hr : 0 < r := div_pos hMr hN
  have hqr : q + r = 1 := by rw [hqdef, hrdef]; field_simp
  -- weighted AM–GM at the points `p / q` and `(1 − p) / r`, weights `q` and `r`
  have h := Real.geom_mean_le_arith_mean2_weighted hq.le hr.le (div_nonneg hp0 hq.le)
    (div_nonneg (sub_nonneg.2 hp1) hr.le) hqr
  have hsum : q * (p / q) + r * ((1 - p) / r) = 1 := by
    rw [mul_div_cancel₀ _ hq.ne', mul_div_cancel₀ _ hr.ne']; ring
  rw [hsum] at h
  have hqK : q * (K + M) = K := by rw [hqdef]; field_simp
  have hrM : r * (K + M) = M := by rw [hrdef]; field_simp
  clear_value q r
  -- raised to the power `K + M`
  have key : ∀ x : ℝ, 0 ≤ x → ∀ (w : ℝ) (j : ℕ), w * (K + M) = j → (x ^ w) ^ (K + M) = x ^ j := by
    intro x hx w j hw
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx, Nat.cast_add, hw, Real.rpow_natCast]
  have hG := pow_le_one₀ (n := K + M)
    (mul_nonneg (Real.rpow_nonneg (div_nonneg hp0 hq.le) _)
      (Real.rpow_nonneg (div_nonneg (sub_nonneg.2 hp1) hr.le) _)) h
  rw [mul_pow, key _ (div_nonneg hp0 hq.le) q K hqK,
    key _ (div_nonneg (sub_nonneg.2 hp1) hr.le) r M hrM, div_pow, div_pow,
    div_mul_div_comm, div_le_one (by positivity)] at hG
  exact hG

/-- The plug-in rate gives a string at least the mass any fixed rate gives it. -/
private theorem measureReal_singleton_le_winRate (p : unitInterval) (x : Fin n → Bool) :
    (bernProd n p).real {x} ≤ (bernProd n (winRate x)).real {x} := by
  rw [bernProd_real_singleton, bernProd_real_singleton, prod_ite, prod_ite, prod_const, prod_const,
    prod_const, prod_const]
  have hw : ((winRate x : unitInterval) : ℝ) =
      ((univ.filter fun i ↦ x i = true).card : ℝ) /
        ((univ.filter fun i ↦ x i = true).card + (univ.filter fun i ↦ ¬ x i = true).card) := by
    rw [← Nat.cast_add, card_filter_add_card_filter_not, card_univ, Fintype.card_fin]
    rfl
  rw [hw]
  exact pow_mul_pow_le_winRate _ _ (unitInterval.nonneg p) (unitInterval.le_one p)

/-- **The plug-in score is at most every fixed-rate score** (order LEAN-30, item 99 of
MATH-PLAN-library-2): putting the string's own win rate `winRate x` into the null law gives `x` at
least the mass a fixed rate `p` gives it, so with the same code the score is no larger, wherever the
fixed rate gives `x` positive mass (`hx`; Lean's `2^(−L) / 0 = 0` otherwise). -/
theorem score_plugIn_le (c : (Fin n → Bool) → List Bool) (p : unitInterval) (x : Fin n → Bool)
    (hx : (bernProd n p).real {x} ≠ 0) :
    score c (bernProd n (winRate x)) x ≤ score c (bernProd n p) x :=
  div_le_div_of_nonneg_left (by positivity) (measureReal_nonneg.lt_of_ne (Ne.symm hx))
    (measureReal_singleton_le_winRate p x)

/-- **The plug-in test keeps its false-alarm rate** (order LEAN-30, item 99 of MATH-PLAN-library-2):
under every Bernoulli law `bernProd n p`, the chance that the plug-in score reaches `1 / α` is at
most `α`. Its rejections are among the fixed-`p` test's (`score_plugIn_le`), apart from strings of
mass `0` under `p`. -/
theorem measureReal_score_plugIn_ge_le {c : (Fin n → Bool) → List Bool}
    (hc : Function.Injective c) (hpf : InformationTheory.IsPrefixFree (Set.range c))
    (p : unitInterval) {α : ℝ} (hα : 0 < α) :
    (bernProd n p).real {x | 1 / α ≤ score c (bernProd n (winRate x)) x} ≤ α := by
  have hsub : {x | 1 / α ≤ score c (bernProd n (winRate x)) x} ⊆
      {x | 1 / α ≤ score c (bernProd n p) x} ∪ {x | (bernProd n p).real {x} = 0} := by
    intro x hx
    by_cases h0 : (bernProd n p).real {x} = 0
    · exact Or.inr h0
    · exact Or.inl (le_trans hx (score_plugIn_le c p x h0))
  have hnull : (bernProd n p).real {x | (bernProd n p).real {x} = 0} = 0 := by
    rw [measureReal_eq_zero_iff, ← Set.biUnion_of_singleton {x | (bernProd n p).real {x} = 0}]
    exact (measure_biUnion_null_iff (Set.toFinite _).countable).mpr
      fun x hx ↦ (measureReal_eq_zero_iff).mp hx
  calc (bernProd n p).real {x | 1 / α ≤ score c (bernProd n (winRate x)) x}
      ≤ (bernProd n p).real
          ({x | 1 / α ≤ score c (bernProd n p) x} ∪ {x | (bernProd n p).real {x} = 0}) :=
        measureReal_mono hsub
    _ ≤ (bernProd n p).real {x | 1 / α ≤ score c (bernProd n p) x} +
          (bernProd n p).real {x | (bernProd n p).real {x} = 0} := measureReal_union_le _ _
    _ ≤ α := by rw [hnull, add_zero]; exact measureReal_score_bernProd_ge_le hc hpf p hα

/-! ### Many compression tests at once, by e-BH (order LEAN-28, item 88) -/

section EBH

open ClassicalLean.Probability.EValueStepUp

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {len : ι → ℕ} {c : (i : ι) → (Fin (len i) → Bool) → List Bool}
  {p₀ : (i : ι) → Measure (Fin (len i) → Bool)} {X : (i : ι) → Ω → Fin (len i) → Bool}

omit [Fintype ι] [DecidableEq ι] in
/-- For a true null, the score of test `i`, `ω ↦ score (c i) (p₀ i) (X i ω)`, is at most an
integrable quantity with mean at most `1`: the score itself when `X i` is almost everywhere
measurable, and the constant `1` otherwise. In that case Mathlib's `μ.map (X i)` is a point mass
(`Measure.map_of_not_aemeasurable_of_ne_zero`), so `p₀ i` is one, and every score is at most `1`. -/
private theorem exists_score_le {i : ι} (hc : Function.Injective (c i))
    (hpf : InformationTheory.IsPrefixFree (Set.range (c i))) (hlaw : μ.map (X i) = p₀ i) :
    ∃ g : Ω → ℝ, Integrable g μ ∧ ∫ ω, g ω ∂μ ≤ 1 ∧ ∀ ω, score (c i) (p₀ i) (X i ω) ≤ g ω := by
  by_cases hXm : AEMeasurable (X i) μ
  · have : IsFiniteMeasure (p₀ i) := hlaw ▸ inferInstance
    have hsm : AEStronglyMeasurable (score (c i) (p₀ i)) (μ.map (X i)) :=
      (Measurable.of_discrete).aestronglyMeasurable
    have hint : Integrable (score (c i) (p₀ i)) (μ.map (X i)) := by
      rw [hlaw]
      exact Integrable.of_finite
    refine ⟨fun ω ↦ score (c i) (p₀ i) (X i ω), (integrable_map_measure hsm hXm).mp hint, ?_,
      fun ω ↦ le_rfl⟩
    rw [← integral_map hXm hsm, hlaw]
    exact integral_score_le_one hc hpf (p₀ i)
  · refine ⟨fun _ ↦ 1, integrable_const _, by simp, fun ω ↦ ?_⟩
    obtain ⟨y, hy⟩ : ∃ y, p₀ i = Measure.dirac y :=
      ⟨_, hlaw.symm.trans (Measure.map_of_not_aemeasurable_of_ne_zero hXm
        (IsProbabilityMeasure.ne_zero μ))⟩
    have hL : (2 : ℝ)⁻¹ ^ (c i (X i ω)).length ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    rw [score, hy, measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton _)]
    by_cases hxy : y = X i ω
    · simpa [hxy] using hL
    · simp [hxy]

/-- **Compression tests fed to e-BH, sharp form** (order LEAN-28, item 88): under the hypotheses of
`integral_eFalseShare_score_le`, the mean share of false finds is at most `q · |H| / m` (`m` tests,
`|H|` true nulls). Each true null's score is at most a quantity of mean at most `1`
(`exists_score_le`), and e-BH's share is, outcome by outcome, at most `q / m` times the sum of the
null scores (`EValueStepUp.eFalseShare_le`). -/
theorem integral_eFalseShare_score_le_mul_card_div {q : ℝ} (hq : 0 < q) {H : Finset ι}
    (hc : ∀ i ∈ H, Function.Injective (c i))
    (hpf : ∀ i ∈ H, InformationTheory.IsPrefixFree (Set.range (c i)))
    (hlaw : ∀ i ∈ H, μ.map (X i) = p₀ i) :
    ∫ ω, eFalseShare q H (fun i ↦ score (c i) (p₀ i) (X i ω)) ∂μ ≤
      q * H.card / Fintype.card ι := by
  choose! g hgint hg1 hle using fun i (hi : i ∈ H) ↦
    exists_score_le (hc i hi) (hpf i hi) (hlaw i hi)
  have hk : 0 ≤ q / Fintype.card ι := div_nonneg hq.le (Nat.cast_nonneg _)
  calc ∫ ω, eFalseShare q H (fun i ↦ score (c i) (p₀ i) (X i ω)) ∂μ
      ≤ ∫ ω, q / Fintype.card ι * ∑ i ∈ H, g i ω ∂μ := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun ω ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          ((integrable_finsetSum H hgint).const_mul _) (Filter.Eventually.of_forall fun ω ↦ ?_)
        exact (eFalseShare_le hq H fun i _ ↦ score_nonneg _ _ _).trans
          (mul_le_mul_of_nonneg_left (sum_le_sum fun i hi ↦ hle i hi ω) hk)
    _ = q / Fintype.card ι * ∑ i ∈ H, ∫ ω, g i ω ∂μ := by
        rw [integral_const_mul, integral_finsetSum H hgint]
    _ ≤ q / Fintype.card ι * ∑ _i ∈ H, (1 : ℝ) := mul_le_mul_of_nonneg_left (sum_le_sum hg1) hk
    _ = q * H.card / Fintype.card ι := by
        rw [sum_const, nsmul_eq_mul, mul_one]
        ring

/-- **Compression tests fed to e-BH keep the expected false share at most `q`** (order LEAN-28,
item 88). Each test `i` has its own code `c i` and its own null law `p₀ i`, fixed in advance; for
every true null `i ∈ H` the code is injective and prefix-free and the law of the string `X i` is
`p₀ i`. Then, at level `q > 0` and under a probability measure `μ`, the mean share of e-BH's
rejections that fall in `H` is at most `q`, whatever the dependence between the tests. -/
theorem integral_eFalseShare_score_le {q : ℝ} (hq : 0 < q) {H : Finset ι}
    (hc : ∀ i ∈ H, Function.Injective (c i))
    (hpf : ∀ i ∈ H, InformationTheory.IsPrefixFree (Set.range (c i)))
    (hlaw : ∀ i ∈ H, μ.map (X i) = p₀ i) :
    ∫ ω, eFalseShare q H (fun i ↦ score (c i) (p₀ i) (X i ω)) ∂μ ≤ q := by
  refine (integral_eFalseShare_score_le_mul_card_div hq hc hpf hlaw).trans ?_
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
  · simp [h, hq.le]
  · rw [div_le_iff₀ (by exact_mod_cast h)]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast H.card_le_univ) hq.le

end EBH

/-- The hypotheses of `integral_eFalseShare_score_le` and
`integral_eFalseShare_score_le_mul_card_div` hold together: one test, strings of length `1`
under the fair coin, the code `x ↦ [x 0]`, the null law the fair coin, `q = 1/2`. -/
example : ∃ (μ : Measure (Fin 1 → Bool)) (_ : IsProbabilityMeasure μ)
    (c : Unit → (Fin 1 → Bool) → List Bool) (p₀ : Unit → Measure (Fin 1 → Bool))
    (X : Unit → (Fin 1 → Bool) → Fin 1 → Bool),
    (0 : ℝ) < 1 / 2 ∧ (∀ i ∈ (univ : Finset Unit), Function.Injective (c i)) ∧
      (∀ i ∈ (univ : Finset Unit), InformationTheory.IsPrefixFree (Set.range (c i))) ∧
      (∀ i ∈ (univ : Finset Unit), μ.map (X i) = p₀ i) := by
  refine ⟨bernProd 1 fairCoin, inferInstance, fun _ x ↦ [x 0], fun _ ↦ bernProd 1 fairCoin,
    fun _ ↦ id, by norm_num, fun _ _ x y h ↦ ?_, fun _ _ ↦ ?_, fun _ _ ↦ Measure.map_id⟩
  · funext j
    rw [Subsingleton.elim j 0]
    simpa using h
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    exact hxy.eq_of_length (by simp)

end ClassicalLean.InformationTheory.CompressionTest

open InformationTheory in
/-- The hypotheses of `measureReal_len_add_le_le` hold together: on strings of `n = 2` win–loss
outcomes, the code `(true, true) ↦ [false]`, `(true, false) ↦ [true, false]`,
`(false, b) ↦ [true, true, b]`, with words of lengths `1, 2, 3, 3` (Kraft sum `1`), injective and
prefix-free; `k = 1` bit of compression asked for, which only the string `(true, true)` gets, with
chance `1/4`. (The model is the group 11 reviewer's.) -/
example := ClassicalLean.InformationTheory.CompressionTest.measureReal_len_add_le_le (n := 2)
  (c := fun x ↦ if x 0 then (if x 1 then [false] else [true, false]) else [true, true, x 1])
  (fun x y h ↦ by
    funext i
    fin_cases i <;> cases hx0 : x 0 <;> cases hx1 : x 1 <;> cases hy0 : y 0 <;>
      cases hy1 : y 1 <;> simp_all)
  (by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
    cases hx0 : x 0 <;> cases hx1 : x 1 <;> cases hy0 : y 0 <;> cases hy1 : y 1 <;>
      simp_all)
  (k := 1)

open InformationTheory in
/-- The hypotheses of `sum_inv_two_pow_length_le_one` hold together: on strings of `n = 2` win–loss
outcomes, the code that writes each string out as it is, `[x 0, x 1]`, which is injective and
prefix-free (all its words have length `2`). -/
example := ClassicalLean.InformationTheory.CompressionTest.sum_inv_two_pow_length_le_one (n := 2)
  (c := fun x ↦ [x 0, x 1])
  (fun x y h ↦ by funext i; fin_cases i <;> simp_all)
  (by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
    exact (List.IsPrefix.eq_of_length h (by simp)))

open InformationTheory in
/-- The hypotheses of `score_plugIn_le` hold together: strings of `n = 2` win–loss outcomes, the
code writing each string out as it is, the fixed win rate `p = 1/3` and the string (win, loss). The
fixed rate gives it mass `2/9 ≠ 0`, below the plug-in mass `1/4` (`winRate` is `1/2`), so the
inequality is strict here (order LEAN-30's check `99.witness`). -/
example := ClassicalLean.InformationTheory.CompressionTest.score_plugIn_le (n := 2)
  (fun x ↦ [x 0, x 1]) ⟨1 / 3, by norm_num, by norm_num⟩ ![true, false]
  (by
    rw [ClassicalLean.InformationTheory.CompressionTest.bernProd_real_singleton]
    norm_num [Fin.prod_univ_two])

open InformationTheory in
/-- The hypotheses of `measureReal_score_plugIn_ge_le` hold together: strings of `n = 2` win–loss
outcomes, the code writing each string out as it is (injective, and prefix-free since all its words
have length `2`), the win rate `p = 1/3` (neither `0`, `1` nor `1/2`) and `α = 1/2`. -/
example := ClassicalLean.InformationTheory.CompressionTest.measureReal_score_plugIn_ge_le (n := 2)
  (c := fun x ↦ [x 0, x 1])
  (fun x y h ↦ by funext i; fin_cases i <;> simp_all)
  (by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
    exact (List.IsPrefix.eq_of_length h (by simp)))
  ⟨1 / 3, by norm_num, by norm_num⟩ (α := 1 / 2) (by norm_num)
