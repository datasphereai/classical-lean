/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Efron–Stein inequality on a finite product space

Coordinates `x i ∈ Ω i`, for `i : Fin n`, each `Ω i` a finite type with a probability vector
`p i : Ω i → ℝ` (`0 ≤ p i a` and `∑ a, p i a = 1`), drawn independently: the point `x` has
weight `∏ i, p i (x i)`. The definitions, for a function `f` of the point:

* `wmean r h` and `wvar r h` — the mean `∑ a, r a * h a` and the variance
  `∑ a, r a * (h a - wmean r h) ^ 2` of `h` under the weights `r`;
* `weight p x` — the product weight `∏ i, p i (x i)` of the point `x`;
* `expect p f` and `variance p f` — the mean and the variance of `f` under the product law
  (`wmean` and `wvar` with the weights `weight p`);
* `coordVar p i f x` — the variance of `f` in coordinate `i` alone, the other coordinates held at
  those of `x`: `wvar (p i) (fun a => f (Function.update x i a))`.

The results, order CLOUD-MATH-3, item 121 of MATH-PLAN-library-2:

* `variance_le_sum_variance_coord` — the Efron–Stein inequality,
  `variance p f ≤ ∑ i, expect p (coordVar p i f)`, that is `Var f ≤ ∑ᵢ E[Varᵢ f]`;
* `variance_le_sum_sq_div_four` — bounded differences: if changing coordinate `i` alone moves `f`
  by at most `c i`, then `variance p f ≤ ∑ i, c i ^ 2 / 4`.

The proof is by induction on `n`, splitting off coordinate `0`. The law of total variance
(`variance_split`) writes `variance p f` as the mean, over the other coordinates, of the variance
in coordinate `0`, plus the variance of the average over coordinate `0` (`marg`). The first term is
the mean of `coordVar p 0 f` (`expect_coordVar_zero`); the induction hypothesis bounds the second,
and since the variance of an average is at most the average of the variances (`wvar_mix_le`), each
of its coordinate terms is at most the matching term for `f` (`coord_succ_le`). Bounded
differences then follow from the weighted Popoviciu inequality: values in a band of width `c` have
variance at most `c ^ 2 / 4` (`wvar_le_of_bdd`).

The proof is the draft `d121-r3-s1` (written by Claude Opus 5.5 through the Anthropic Batch API,
the lane's API-CREDIT-1 work), adapted by the Claude Code cloud session that landed it (order
CLOUD-MATH-3): the draft's namespace `EfronStein` became this module's, the two main theorems moved
inside it and their references to `EfronStein.…` lost the prefix; targeted imports, docstrings, and
`change` where a `show` changed the goal.
-/

universe u

namespace ClassicalLean.Probability.EfronStein

/-- Weighted mean of `h` with weights `r`. -/
def wmean {α : Type*} [Fintype α] (r h : α → ℝ) : ℝ := ∑ a, r a * h a

/-- Weighted variance of `h` with weights `r`. -/
def wvar {α : Type*} [Fintype α] (r h : α → ℝ) : ℝ := ∑ a, r a * (h a - wmean r h) ^ 2

/-- Product weight of a point of the product space. -/
def weight {n : ℕ} {Ω : Fin n → Type*} (p : ∀ i, Ω i → ℝ) (x : ∀ i, Ω i) : ℝ :=
  ∏ i, p i (x i)

/-- Expectation under the product of the coordinate distributions. -/
def expect {n : ℕ} {Ω : Fin n → Type*} [∀ i, Fintype (Ω i)] (p : ∀ i, Ω i → ℝ)
    (f : (∀ i, Ω i) → ℝ) : ℝ :=
  wmean (weight p) f

/-- Variance under the product of the coordinate distributions. -/
def variance {n : ℕ} {Ω : Fin n → Type*} [∀ i, Fintype (Ω i)] (p : ∀ i, Ω i → ℝ)
    (f : (∀ i, Ω i) → ℝ) : ℝ :=
  wvar (weight p) f

/-- Variance in coordinate `i` with all other coordinates of `x` fixed. -/
def coordVar {n : ℕ} {Ω : Fin n → Type*} [∀ i, Fintype (Ω i)] (p : ∀ i, Ω i → ℝ)
    (i : Fin n) (f : (∀ i, Ω i) → ℝ) (x : ∀ i, Ω i) : ℝ :=
  wvar (p i) (fun a => f (Function.update x i a))

private lemma sum_sq_shift {α : Type*} [Fintype α] (r h : α → ℝ) (hr1 : ∑ a, r a = 1)
    (m : ℝ) : ∑ a, r a * (h a - m) ^ 2 = wvar r h + (wmean r h - m) ^ 2 := by
  sorry

private lemma wvar_le {α : Type*} [Fintype α] (r h : α → ℝ) (hr1 : ∑ a, r a = 1) (m : ℝ) :
    wvar r h ≤ ∑ a, r a * (h a - m) ^ 2 := by
  sorry

private lemma wvar_nonneg {α : Type*} [Fintype α] (r h : α → ℝ) (hr0 : ∀ a, 0 ≤ r a) :
    0 ≤ wvar r h := by
  sorry

private lemma sq_wmean_le {α : Type*} [Fintype α] (r h : α → ℝ) (hr0 : ∀ a, 0 ≤ r a)
    (hr1 : ∑ a, r a = 1) : wmean r h ^ 2 ≤ ∑ a, r a * h a ^ 2 := by
  sorry

/-- Variance of a mixture of functions is at most the mixture of their variances. -/
private lemma wvar_mix_le {α β : Type*} [Fintype α] [Fintype β] (q : α → ℝ) (r : β → ℝ)
    (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∑ a, q a = 1) (hr0 : ∀ b, 0 ≤ r b) (hr1 : ∑ b, r b = 1)
    (H : α → β → ℝ) :
    wvar r (fun b => ∑ a, q a * H a b) ≤ ∑ a, q a * wvar r (H a) := by
  sorry

/-- Weighted Popoviciu inequality: values within a band of width `c` have variance
at most `c ^ 2 / 4`. -/
private lemma wvar_le_of_bdd {α : Type*} [Fintype α] (r h : α → ℝ) (hr0 : ∀ a, 0 ≤ r a)
    (hr1 : ∑ a, r a = 1) (c : ℝ) (hc : ∀ a b, |h a - h b| ≤ c) : wvar r h ≤ c ^ 2 / 4 := by
  sorry

private lemma weight_nonneg {n : ℕ} {Ω : Fin n → Type*} (p : ∀ i, Ω i → ℝ)
    (hp0 : ∀ i a, 0 ≤ p i a) (x : ∀ i, Ω i) : 0 ≤ weight p x := by
  sorry

private def consEquiv' {n : ℕ} (Ω : Fin (n + 1) → Type*) :
    Ω 0 × (∀ i : Fin n, Ω i.succ) ≃ ∀ i, Ω i where
  toFun z := Fin.cons z.1 z.2
  invFun x := (x 0, Fin.tail x)
  left_inv z := by rcases z with ⟨a, y⟩; simp
  right_inv x := by simp

private lemma sum_cons {n : ℕ} {Ω : Fin (n + 1) → Type*} [∀ i, Fintype (Ω i)]
    (F : (∀ i, Ω i) → ℝ) :
    ∑ x, F x = ∑ a : Ω 0, ∑ y : (∀ i : Fin n, Ω i.succ), F (Fin.cons a y) := by
  sorry

private lemma weight_cons {n : ℕ} {Ω : Fin (n + 1) → Type*} (p : ∀ i, Ω i → ℝ) (a : Ω 0)
    (y : ∀ i : Fin n, Ω i.succ) :
    weight p (Fin.cons a y : ∀ i, Ω i) = p 0 a * weight (fun i : Fin n => p i.succ) y := by
  sorry

private lemma sum_weight_cons {n : ℕ} {Ω : Fin (n + 1) → Type*} [∀ i, Fintype (Ω i)]
    (p : ∀ i, Ω i → ℝ) (h : (∀ i, Ω i) → ℝ) :
    ∑ x, weight p x * h x = ∑ y : (∀ i : Fin n, Ω i.succ),
      weight (fun i : Fin n => p i.succ) y * ∑ a, p 0 a * h (Fin.cons a y) := by
  sorry

private theorem sum_weight (n : ℕ) : ∀ (Ω : Fin n → Type u) [∀ i, Fintype (Ω i)]
    (p : ∀ i, Ω i → ℝ), (∀ i, ∑ a, p i a = 1) → ∑ x, weight p x = 1 := by
  sorry

/-- Average over the first coordinate. -/
private def marg {n : ℕ} {Ω : Fin (n + 1) → Type*} [∀ i, Fintype (Ω i)]
    (p : ∀ i, Ω i → ℝ) (f : (∀ i, Ω i) → ℝ) (y : ∀ i : Fin n, Ω i.succ) : ℝ :=
  wmean (p 0) (fun a => f (Fin.cons a y))

private lemma expect_marg {n : ℕ} {Ω : Fin (n + 1) → Type*} [∀ i, Fintype (Ω i)]
    (p : ∀ i, Ω i → ℝ) (f : (∀ i, Ω i) → ℝ) :
    expect p f = expect (fun j : Fin n => p j.succ) (marg p f) := by
  sorry

/-- Law of total variance, splitting off the first coordinate. -/
private lemma variance_split {n : ℕ} {Ω : Fin (n + 1) → Type*} [∀ i, Fintype (Ω i)]
    (p : ∀ i, Ω i → ℝ) (f : (∀ i, Ω i) → ℝ) (hp1 : ∑ a, p 0 a = 1) :
    variance p f = (∑ y : (∀ i : Fin n, Ω i.succ), weight (fun j : Fin n => p j.succ) y *
        wvar (p 0) (fun a => f (Fin.cons a y))) +
      variance (fun j : Fin n => p j.succ) (marg p f) := by
  sorry

private lemma expect_coordVar_zero {n : ℕ} {Ω : Fin (n + 1) → Type*} [∀ i, Fintype (Ω i)]
    (p : ∀ i, Ω i → ℝ) (f : (∀ i, Ω i) → ℝ) (hp1 : ∑ a, p 0 a = 1) :
    expect p (coordVar p 0 f) = ∑ y : (∀ i : Fin n, Ω i.succ),
      weight (fun j : Fin n => p j.succ) y * wvar (p 0) (fun a => f (Fin.cons a y)) := by
  sorry

private lemma coord_succ_le {n : ℕ} {Ω : Fin (n + 1) → Type*} [∀ i, Fintype (Ω i)]
    (p : ∀ i, Ω i → ℝ) (f : (∀ i, Ω i) → ℝ) (hp0 : ∀ i a, 0 ≤ p i a)
    (hp1 : ∀ i, ∑ a, p i a = 1) (i : Fin n) :
    expect (fun j : Fin n => p j.succ) (coordVar (fun j : Fin n => p j.succ) i (marg p f))
      ≤ expect p (coordVar p i.succ f) := by
  sorry

private theorem es_aux (n : ℕ) : ∀ (Ω : Fin n → Type u) [∀ i, Fintype (Ω i)]
    (p : ∀ i, Ω i → ℝ), (∀ i a, 0 ≤ p i a) → (∀ i, ∑ a, p i a = 1) →
    ∀ f : (∀ i, Ω i) → ℝ, variance p f ≤ ∑ i, expect p (coordVar p i f) := by
  sorry

/-- **The Efron–Stein inequality** for independent coordinates on finite sets. Item 121 of
MATH-PLAN-library-2 (order CLOUD-MATH-3). Under the product of the probability vectors `p i`, the
variance of `f` is at most the sum, over the coordinates, of the mean of its variance in that
coordinate alone: `Var f ≤ ∑ᵢ E[Varᵢ f]`. -/
theorem variance_le_sum_variance_coord {n : ℕ} {Ω : Fin n → Type u} [∀ i, Fintype (Ω i)]
    (p : ∀ i, Ω i → ℝ) (hp0 : ∀ i a, 0 ≤ p i a) (hp1 : ∀ i, ∑ a, p i a = 1)
    (f : (∀ i, Ω i) → ℝ) :
    variance p f ≤ ∑ i, expect p (coordVar p i f) := by
  sorry

/-- **Bounded differences.** Item 121 of MATH-PLAN-library-2 (order CLOUD-MATH-3). If changing
coordinate `i` alone moves `f` by at most `c i`, then the variance of `f` under the product of the
probability vectors `p i` is at most `∑ i, c i ^ 2 / 4`. -/
theorem variance_le_sum_sq_div_four {n : ℕ} {Ω : Fin n → Type u} [∀ i, Fintype (Ω i)]
    (p : ∀ i, Ω i → ℝ) (hp0 : ∀ i a, 0 ≤ p i a) (hp1 : ∀ i, ∑ a, p i a = 1)
    (f : (∀ i, Ω i) → ℝ) (c : Fin n → ℝ)
    (hc : ∀ i (x : ∀ i, Ω i) (a b : Ω i),
      |f (Function.update x i a) - f (Function.update x i b)| ≤ c i) :
    variance p f ≤ ∑ i, c i ^ 2 / 4 := by
  sorry

end ClassicalLean.Probability.EfronStein
