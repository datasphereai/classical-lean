/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Probability.RelativeEntropyGrowth
import ClassicalLean.InformationTheory.Entropy
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.HasLawExists

/-!
# The method of types: Sanov's theorem for a finite alphabet, upper bound

`n` independent draws from a law `p` on a finite alphabet `α` with `K = card α` letters. The
*type* (empirical distribution) of the draws `ω` is the vector `empirical ω i = N i / n`, where
`N i = typeCount ω i` is the number of draws equal to `i`.

* `draws n p` — the product of `n` copies of the library's `vecMeasure p` (mass `p i` at `i`).
* `measureReal_draws_singleton`, `measureReal_draws` — the chance of a sequence is `∏ j, p (ω j)`,
  and of a finite set of sequences the sum of these.
* `prod_eq_prod_pow_typeCount` — that chance depends only on the counts: `∏ i, p i ^ N i`.
* `measureReal_empirical_eq_le` — one type class: the chance that the type equals `q` is at most
  `exp (−n D(q ‖ p))`, with `D` the library's `relEntropy`.
* `measureReal_empirical_mem_le` — order LEAN-24, item 57, **Sanov's theorem, upper half**: for
  every set `E` of vectors and every `d` with `d ≤ D(q ‖ p)` at each type `q` of `n` draws that
  lies in `E`, the chance that the type lies in `E` is at most `(n + 1)^K · exp (−n d)`. The
  textbook hypothesis, `d ≤ D(q ‖ p)` for all `q ∈ E` (so `d` the least `D` over `E`), implies
  this one when `E` lies inside the probability vectors. The hypothesis asks nothing at other
  points of `E` (review r57): there Lean's `relEntropy` is a junk value that can be negative
  (`((−1, −1) ‖ (1/2, 1/2))` gives `−2 log 2`), which would only have weakened the bound. The
  matching lower bound (for open `E`) is not proved.
* `tendsto_neg_log_div_shannonEntropy` — order LEAN-32, item 109, **the asymptotic equipartition
  property**: for pairwise independent, identically distributed draws `X 0, X 1, …` with law `p`
  on the finite alphabet `α`, `−(1/n) ∑_{i<n} log p (X i) → H(p)` almost surely, `H` the
  library's `shannonEntropy`. It is the strong law (`strong_law_ae`) for `−log p (X i)`, whose mean
  is `∑ a, p a · (−log p a) = H(p)`.

What `K`, `E` and `p i = 0` do. `K` enters only through the number of types: each type is a
vector of counts in `{0, …, n}`, so there are at most `(n + 1)^K` of them. `E` is any set of real
vectors (no measurability or openness is needed); its points that are not types of `n` draws add
nothing to the chance and are not used in the hypothesis on `d`, and if `E` holds no type the
hypothesis is empty and the chance is `0`. Letters with
`p i = 0` are allowed. Where `q i > 0 = p i` the true divergence is `+∞`, but Lean's `relEntropy`
counts that cell as `q i · log (q i / 0) = q i · log 0 = 0`, so its value is finite and can even be
negative (`p = (1, 0)`, `q = (1/2, 1/2)` gives `(1/2) log (1/2)`). The bound still holds, because
a type that uses a letter of chance `0` has chance `0`; it is then weaker than the true one. For
`n = 0` the type is `0` (Lean's `x / 0 = 0`) and the bound is `1`.

The proof: on the type class of `q`, `∏ p i ^ N i = (∏ q i ^ N i) · exp (−n D(q ‖ p))`, and the
class has chance at most `1` under `n` draws from `q` itself, since `∑ over all sequences of
∏ j, q (ω j) = (∑ q)^n = 1`. No multinomial coefficient is needed.

## Hypotheses

Measured in order LEAN-24's checks (`checks.py`, lines S1 to S5; FLOAT where marked). The
one-class bound holds on 607 types of 60 random laws (`K ≤ 3`, `n ≤ 6`, zero entries included;
FLOAT), with equality in degenerate cases (for `n = 1` and the type of a single letter `i`, the
chance and the bound are both `p i`). The theorem holds for a fair coin with
`E = {q : q 0 ≥ 3/4}` and `n = 100, 200, 400, 800`, exact binomial tail sums against the bound
(FLOAT for the exponential); the bound is loose there mostly by its factor `(n + 1)^2`: at
`n = 800`, `log P` is `−107.67` and `−n d` is `−104.65`. The case `p i = 0` above is check S3
(exact). The
hypothesis `d ≤ D` on `E` is needed: for `E = {(1/2, 1/2)}`, `p = (1/2, 1/2)`, `n = 10` and
`d = 1`, the chance `63/256` is above `121 e^−10` (FLOAT). Not needed and not assumed: `∑ p = 1`
(with `p = (2, 2)`, `n = 1`, `q = (1, 0)`: chance `2 = exp (−D)`, check S5). Kept but not shown
needed: `p ≥ 0` (by hand: `vecMeasure` gives mass `0` to a letter with `p i < 0`, so a type using
it has chance `0`; the hypothesis is used to read off `vecMeasure`'s masses).

Item 109 is wider than the plan's row in two ways. The law is given as
`μ.real {ω | X 0 ω = a} = p a` for every letter, which carries `p ≥ 0` and `∑ p = 1`, with no
measurability beyond what `IdentDistrib` gives (`X 0` is almost everywhere measurable,
`IdentDistrib.aemeasurable_fst`); and pairwise independence is enough, where the plan says
independent draws, since Mathlib's strong law asks no more. The plan's row names the library's
`vecMeasure`; the statement does not use it, the law being given as above. Lean's `log 0 = 0` does
not matter: a letter with `p a = 0` is drawn with chance `0`. Each hypothesis is needed, with a law
that is not uniform (when `p` is uniform, `−log p a = log |α| = H(p)` for every letter, so the
conclusion holds whatever the draws are and no case exists): `p = (1/4, 3/4)`, so
`H(p) = log 4 − (3/4) log 3`. Without the law, true law `(1, 0)`: the limit is `log 4`, not `H(p)`
(the exact checks written for item 109 under order LEAN-32, `checks109.py`, line `109.drop.law`);
without independence, `X i = X 0` for every `i`: the average is `log 4` or `log (4/3)`, never `H(p)`
(`109.drop.indep`); without identical distribution, `X 0` with law `p` and `X i` the second letter
for every `i ≥ 1` (constants, so independent): the limit is `log (4/3)` (`109.drop.ident`). Each
"not `H(p)`" is reduced by hand to a fact about whole numbers (`3³ ≠ 1`, `3 ≠ 1`), which the script
checks exactly. The witness draws uniform letters of `Fin 4` under Mathlib's `Measure.infinitePi`
and reads `X i = (ω i = 0)`, so the law on `Bool` is `p true = 1/4`, `p false = 3/4`, not uniform;
the module imports `Mathlib.Probability.HasLawExists` for it.

## What is cited

For a work not read here, author, title and year only: I. N. Sanov, "On the probability of large
deviations of random variables", 1957 (an English title of a paper in Russian).

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-24): "sanov|method of types" no hit apart from
the phrase "type class"; "empirical" one unrelated line. Used: `Measure.pi_pi`,
`Fintype.prod_fiberwise'`, `Fintype.prod_sum`, `sum_measureReal_singleton`,
`measureReal_biUnion_finset_le`; library `vecMeasure`, `measureReal_vecMeasure_singleton`,
`relEntropy`.
-/

open MeasureTheory Real Finset
open ClassicalLean.Simplex ClassicalLean.Probability.RelativeEntropyGrowth

namespace ClassicalLean.InformationTheory

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- How many of the draws `ω` equal `i`. -/
def typeCount {n : ℕ} (ω : Fin n → α) (i : α) : ℕ := (univ.filter fun j ↦ ω j = i).card

/-- The **empirical distribution** (the *type*) of `n` draws: the share of draws equal to `i`.
For `n = 0` it is `0` (Lean's `x / 0 = 0`). -/
noncomputable def empirical {n : ℕ} (ω : Fin n → α) (i : α) : ℝ := (typeCount ω i : ℝ) / n

omit [Fintype α] in
theorem typeCount_le {n : ℕ} (ω : Fin n → α) (i : α) : typeCount ω i ≤ n := by
  simpa [typeCount] using card_filter_le univ fun j ↦ ω j = i

theorem sum_typeCount {n : ℕ} (ω : Fin n → α) : ∑ i, typeCount ω i = n := by
  simp only [typeCount]
  rw [← card_eq_sum_card_fiberwise (f := ω) (fun j _ ↦ mem_univ (ω j)), card_univ,
    Fintype.card_fin]

/-- The chance of a sequence of draws depends only on its counts. -/
theorem prod_eq_prod_pow_typeCount {n : ℕ} (ω : Fin n → α) (p : α → ℝ) :
    ∏ j, p (ω j) = ∏ i, p i ^ typeCount ω i := by
  rw [← Fintype.prod_fiberwise' ω p]
  refine prod_congr rfl fun i _ ↦ ?_
  rw [prod_const, card_univ, Fintype.card_subtype, typeCount]

omit [Fintype α] in
theorem empirical_nonneg {n : ℕ} (ω : Fin n → α) (i : α) : 0 ≤ empirical ω i :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem sum_empirical {n : ℕ} (hn : n ≠ 0) (ω : Fin n → α) : ∑ i, empirical ω i = 1 := by
  simp only [empirical, ← sum_div, ← Nat.cast_sum, sum_typeCount]
  exact div_self (Nat.cast_ne_zero.2 hn)

variable [MeasurableSpace α] [MeasurableSingletonClass α]

/-- `n` independent draws from the law `p` on the finite alphabet `α`: the product of `n` copies
of the library's `vecMeasure p`. -/
noncomputable def draws (n : ℕ) (p : α → ℝ) : Measure (Fin n → α) :=
  Measure.pi fun _ ↦ vecMeasure p

instance (n : ℕ) (p : α → ℝ) : IsFiniteMeasure (draws n p) := by
  unfold draws
  infer_instance

omit [DecidableEq α] in
theorem measureReal_draws_singleton {p : α → ℝ} (hp0 : ∀ i, 0 ≤ p i) (n : ℕ)
    (ω : Fin n → α) : (draws n p).real {ω} = ∏ j, p (ω j) := by
  rw [← Set.univ_pi_singleton, measureReal_def, draws, Measure.pi_pi, ENNReal.toReal_prod]
  exact prod_congr rfl fun j _ ↦ measureReal_vecMeasure_singleton hp0 (ω j)

omit [DecidableEq α] in
theorem measureReal_draws {p : α → ℝ} (hp0 : ∀ i, 0 ≤ p i) (n : ℕ) (s : Finset (Fin n → α)) :
    (draws n p).real s = ∑ ω ∈ s, ∏ j, p (ω j) := by
  rw [← sum_measureReal_singleton]
  exact sum_congr rfl fun ω _ ↦ measureReal_draws_singleton hp0 n ω

/-- **One type class.** The chance that `n` draws from `p` have empirical distribution `q` is at
most `exp (−n D(q ‖ p))`, with `D` the library's `relEntropy`. Where `q i > 0 = p i` the true
divergence is `+∞` while Lean's `relEntropy` counts that cell as `0`; the bound still holds there,
because such a type has chance `0`. -/
theorem measureReal_empirical_eq_le {p : α → ℝ} (hp0 : ∀ i, 0 ≤ p i) (n : ℕ) (q : α → ℝ) :
    (draws n p).real {ω | empirical ω = q} ≤ exp (-(n * relEntropy q p)) := by
  classical
  by_cases hE : ∃ ω₀ : Fin n → α, empirical ω₀ = q
  swap
  · push Not at hE
    have : {ω : Fin n → α | empirical ω = q} = ∅ :=
      Set.eq_empty_of_forall_notMem fun ω hω ↦ hE ω hω
    rw [this, measureReal_empty]
    exact (exp_pos _).le
  obtain ⟨ω₀, rfl⟩ := hE
  have hset : {ω : Fin n → α | empirical ω = empirical ω₀} =
      ↑(univ.filter fun ω : Fin n → α ↦ empirical ω = empirical ω₀) := by
    ext ω; simp
  rw [hset, measureReal_draws hp0]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [CharP.cast_eq_zero, zero_mul, neg_zero, exp_zero]
    refine (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun ω _ _ ↦ by simp).trans ?_
    simp
  set q := empirical ω₀ with hq
  -- every sequence of the class has the same counts `N i = n q i`
  have hcount : ∀ ω ∈ univ.filter fun ω : Fin n → α ↦ empirical ω = q,
      typeCount ω = typeCount ω₀ := by
    intro ω hω
    rw [mem_filter] at hω
    replace hω := hω.2
    funext i
    have := congrFun hω i
    simp only [hq, empirical] at this
    exact_mod_cast (div_left_inj' (Nat.cast_ne_zero.2 hn.ne')).1 this
  by_cases hsupp : ∃ i, 0 < typeCount ω₀ i ∧ p i = 0
  · -- a type that uses a letter of chance `0` has chance `0`
    obtain ⟨i, hi, hpi⟩ := hsupp
    refine le_trans (le_of_eq ?_) (exp_pos _).le
    refine sum_eq_zero fun ω hω ↦ ?_
    rw [prod_eq_prod_pow_typeCount, hcount ω hω]
    exact prod_eq_zero (mem_univ i) (by rw [hpi, zero_pow hi.ne'])
  push Not at hsupp
  -- `p^N = q^N · exp (−n D(q ‖ p))` on the class
  have hkey : ∏ i, p i ^ typeCount ω₀ i =
      (∏ i, q i ^ typeCount ω₀ i) * exp (-(n * relEntropy q p)) := by
    have hD : (n : ℝ) * relEntropy q p = ∑ i, (typeCount ω₀ i : ℝ) * Real.log (q i / p i) := by
      rw [relEntropy, mul_sum]
      refine sum_congr rfl fun i _ ↦ ?_
      rw [hq, empirical, ← mul_assoc, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hn.ne')]
    rw [hD, ← sum_neg_distrib, exp_sum, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ ↦ ?_
    rcases Nat.eq_zero_or_pos (typeCount ω₀ i) with h0 | hpos
    · simp [h0]
    have hpi : 0 < p i := lt_of_le_of_ne (hp0 i) (Ne.symm (hsupp i hpos))
    have hqi : 0 < q i := by
      rw [hq, empirical]
      exact div_pos (Nat.cast_pos.2 hpos) (Nat.cast_pos.2 hn)
    rw [show -((typeCount ω₀ i : ℝ) * Real.log (q i / p i)) =
        (typeCount ω₀ i : ℝ) * Real.log (p i / q i) by
      rw [show Real.log (q i / p i) = -Real.log (p i / q i) by rw [← Real.log_inv, inv_div]]
      ring, ← Real.log_pow, exp_log (pow_pos (div_pos hpi hqi) _),
      div_pow, mul_div_cancel₀ _ (pow_pos hqi _).ne']
  calc ∑ ω ∈ univ.filter fun ω : Fin n → α ↦ empirical ω = q, ∏ j, p (ω j)
      = ∑ ω ∈ univ.filter fun ω : Fin n → α ↦ empirical ω = q,
          (∏ j, q (ω j)) * exp (-(n * relEntropy q p)) := by
        refine sum_congr rfl fun ω hω ↦ ?_
        rw [prod_eq_prod_pow_typeCount, prod_eq_prod_pow_typeCount, hcount ω hω, hkey]
    _ ≤ ∑ ω : Fin n → α, (∏ j, q (ω j)) * exp (-(n * relEntropy q p)) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun ω _ _ ↦
          mul_nonneg (prod_nonneg fun j _ ↦ empirical_nonneg ω₀ _) (exp_pos _).le
    _ = exp (-(n * relEntropy q p)) := by
        rw [← sum_mul, ← Fintype.prod_sum (fun _ : Fin n ↦ q), hq,
          sum_empirical hn.ne' ω₀, prod_const_one, one_mul]

/-- **Sanov's theorem for a finite alphabet, upper bound** (method of types). For `n` independent
draws from a law `p` on an alphabet of `K = card α` letters, any set `E` of vectors, and any `d`
with `d ≤ relEntropy q p` at every type `q` of `n` draws that lies in `E`, the chance that the
empirical distribution lies in `E` is at most
`(n + 1)^K · exp (−n d)`. -/
theorem measureReal_empirical_mem_le {p : α → ℝ} (hp0 : ∀ i, 0 ≤ p i) (n : ℕ)
    (E : Set (α → ℝ)) {d : ℝ}
    (hd : ∀ ω : Fin n → α, empirical ω ∈ E → d ≤ relEntropy (empirical ω) p) :
    (draws n p).real {ω | empirical ω ∈ E} ≤ (n + 1) ^ Fintype.card α * exp (-(n * d)) := by
  classical
  set T := (univ.image (fun ω : Fin n → α ↦ empirical ω)).filter (· ∈ E) with hT
  have hcover : {ω : Fin n → α | empirical ω ∈ E} ⊆ ⋃ q ∈ T, {ω | empirical ω = q} := by
    intro ω hω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨empirical ω, ?_, rfl⟩
    simp only [hT, mem_filter, mem_image, mem_univ, true_and]
    exact ⟨⟨ω, rfl⟩, hω⟩
  -- the number of types is at most `(n + 1)^K`
  have hcard : (T.card : ℝ) ≤ (n + 1) ^ Fintype.card α := by
    have h1 : T.card ≤ (univ.image fun ω : Fin n → α ↦ empirical ω).card := card_filter_le _ _
    have h2 : (univ.image fun ω : Fin n → α ↦ empirical ω).card ≤
        (univ.image fun ω : Fin n → α ↦ fun i ↦ (⟨typeCount ω i,
          Nat.lt_succ_of_le (typeCount_le ω i)⟩ : Fin (n + 1))).card := by
      have : (univ.image fun ω : Fin n → α ↦ empirical ω) =
          (univ.image fun ω : Fin n → α ↦ fun i ↦ (⟨typeCount ω i,
            Nat.lt_succ_of_le (typeCount_le ω i)⟩ : Fin (n + 1))).image
            (fun c i ↦ ((c i : ℕ) : ℝ) / n) := by
        rw [image_image]; rfl
      rw [this]
      exact card_image_le
    have h3 := card_le_univ (univ.image fun ω : Fin n → α ↦ fun i ↦ (⟨typeCount ω i,
      Nat.lt_succ_of_le (typeCount_le ω i)⟩ : Fin (n + 1)))
    rw [Fintype.card_fun, Fintype.card_fin] at h3
    exact_mod_cast (h1.trans h2).trans h3
  calc (draws n p).real {ω | empirical ω ∈ E}
      ≤ (draws n p).real (⋃ q ∈ T, {ω | empirical ω = q}) :=
        measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ q ∈ T, (draws n p).real {ω | empirical ω = q} := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ T, exp (-(n * d)) := by
        refine sum_le_sum fun q hq ↦ (measureReal_empirical_eq_le hp0 n q).trans ?_
        refine exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)))
        obtain ⟨ω, -, rfl⟩ := mem_image.1 (mem_filter.1 hq).1
        exact hd ω (mem_filter.1 hq).2
    _ = T.card * exp (-(n * d)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (n + 1) ^ Fintype.card α * exp (-(n * d)) :=
        mul_le_mul_of_nonneg_right hcard (exp_pos _).le

open ProbabilityTheory Filter Topology in
omit [DecidableEq α] in
/-- **The asymptotic equipartition property** (order LEAN-32, item 109): for pairwise independent,
identically distributed draws `X i` on a finite alphabet with law `p`, almost surely
`−(1/n) ∑_{i<n} log p (X i) → H(p)`, the strong law for `−log p (X i)`. -/
theorem tendsto_neg_log_div_shannonEntropy {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → α}
    (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) {p : α → ℝ}
    (hlaw : ∀ a, μ.real {ω | X 0 ω = a} = p a) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ -(∑ i ∈ range n, Real.log (p (X i ω))) / n) atTop
      (𝓝 (ClassicalLean.Simplex.shannonEntropy p)) := by
  have hg : Measurable fun a : α ↦ -Real.log (p a) := measurable_of_finite _
  have hX0 : AEMeasurable (X 0) μ := (hident 0).aemeasurable_fst
  have hint : Integrable ((fun a : α ↦ -Real.log (p a)) ∘ X 0) μ :=
    (Integrable.of_finite (μ := μ.map (X 0))).comp_aemeasurable hX0
  have hmean : ∫ ω, ((fun a : α ↦ -Real.log (p a)) ∘ X 0) ω ∂μ = shannonEntropy p := by
    rw [show ∫ ω, ((fun a : α ↦ -Real.log (p a)) ∘ X 0) ω ∂μ
        = ∫ a, -Real.log (p a) ∂(μ.map (X 0)) from
          (integral_map (f := fun a : α ↦ -Real.log (p a)) hX0
            (measurable_of_finite _).aestronglyMeasurable).symm,
      integral_fintype Integrable.of_finite]
    simp only [map_measureReal_apply_of_aemeasurable hX0 (measurableSet_singleton _),
      smul_eq_mul, shannonEntropy, mul_neg, Finset.sum_neg_distrib]
    refine congrArg Neg.neg (Finset.sum_congr rfl fun a _ ↦ ?_)
    rw [← hlaw a]
    rfl
  have h := strong_law_ae (fun i ↦ (fun a : α ↦ -Real.log (p a)) ∘ X i) hint
    (fun i j hij ↦ (hindep hij).comp hg hg) fun i ↦ (hident i).comp hg
  filter_upwards [h] with ω hω
  rw [hmean] at hω
  refine hω.congr fun n ↦ ?_
  simp only [Function.comp_apply, smul_eq_mul, Finset.sum_neg_distrib]
  ring

end ClassicalLean.InformationTheory

open ClassicalLean.Simplex in
/-- The hypotheses of `measureReal_empirical_mem_le` hold together: a fair choice between two
letters, `p = (1/2, 1/2)`, nonnegative; `n = 4` draws; the set `E` holding the one empirical law
`(3/4, 1/4)`, and `d` its relative entropy to `p`, `3/4 · log (3/2) + 1/4 · log (1/2)`, which is
positive: every empirical law in `E` is at relative entropy at least `d` from `p`, with no zero
coordinate. -/
example := ClassicalLean.InformationTheory.measureReal_empirical_mem_le (α := Fin 2)
  (p := ![1 / 2, 1 / 2]) (fun i ↦ by fin_cases i <;> norm_num) (n := 4)
  (E := {![3 / 4, 1 / 4]}) (d := relEntropy ![3 / 4, 1 / 4] ![1 / 2, 1 / 2])
  (fun ω h ↦ by rw [Set.mem_singleton_iff.mp h])

open ProbabilityTheory in
/-- The hypotheses of `tendsto_neg_log_div_shannonEntropy` hold together: uniform letters `ω i` of
`Fin 4`, independent under `Measure.infinitePi`, read as `X i ω = (ω i = 0)` in `Bool`, so the law
is `p true = 1/4`, `p false = 3/4`, not uniform. -/
example := ClassicalLean.InformationTheory.tendsto_neg_log_div_shannonEntropy (α := Bool)
  (Ω := ℕ → Fin 4) (μ := Measure.infinitePi fun _ : ℕ ↦ uniformOn (Set.univ : Set (Fin 4)))
  (X := fun i ω ↦ decide (ω i = 0))
  (fun i j hij ↦ (iIndepFun_infinitePi (P := fun _ : ℕ ↦ uniformOn (Set.univ : Set (Fin 4)))
    (X := fun _ k ↦ decide (k = 0)) fun _ ↦ measurable_of_finite _).indepFun hij)
  (fun i ↦ (show IdentDistrib (fun ω : ℕ → Fin 4 ↦ ω i) (fun ω : ℕ → Fin 4 ↦ ω 0)
      (Measure.infinitePi fun _ : ℕ ↦ uniformOn (Set.univ : Set (Fin 4)))
      (Measure.infinitePi fun _ : ℕ ↦ uniformOn (Set.univ : Set (Fin 4))) from
    ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable, by
      rw [Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]⟩).comp
    (measurable_of_finite fun k : Fin 4 ↦ decide (k = 0)))
  (p := fun b ↦ if b then 1 / 4 else 3 / 4)
  (fun a ↦ by
    rw [show {ω : ℕ → Fin 4 | decide (ω 0 = 0) = a}
        = (fun ω : ℕ → Fin 4 ↦ ω 0) ⁻¹' {k | decide (k = 0) = a} from rfl,
      ← map_measureReal_apply (measurable_pi_apply 0) (Set.toFinite _).measurableSet,
      Measure.infinitePi_map_eval]
    cases a
    · rw [show {k : Fin 4 | decide (k = 0) = false} = ↑({1, 2, 3} : Finset (Fin 4)) by
        ext k; fin_cases k <;> simp]
      rw [measureReal_def, uniformOn_univ, Measure.count_apply_finset]
      norm_num
    · rw [show {k : Fin 4 | decide (k = 0) = true} = ↑({0} : Finset (Fin 4)) by
        ext k; fin_cases k <;> simp]
      rw [measureReal_def, uniformOn_univ, Measure.count_apply_finset]
      norm_num)
