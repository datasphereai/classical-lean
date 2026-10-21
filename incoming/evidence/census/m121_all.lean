/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
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
`change` where a `show` changed the goal. The two witnesses at the end of the file are new (the item
had no witness start): two coordinates with values in `Fin 2` and different weights, and
`f = x 0 + 2 * x 1`.
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
  have hμ : ∑ a, r a * h a = wmean r h := rfl
  have h2 : ∑ a, r a * (h a - wmean r h) = 0 := by
    have : ∑ a, r a * (h a - wmean r h) = ∑ a, r a * h a - (∑ a, r a) * wmean r h := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [this, hr1, hμ]; ring
  have h1 : ∑ a, r a * (h a - m) ^ 2 = ∑ a, r a * (h a - wmean r h) ^ 2
      + 2 * (wmean r h - m) * ∑ a, r a * (h a - wmean r h)
      + (∑ a, r a) * (wmean r h - m) ^ 2 := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [h1, h2, hr1]
  have hw : wvar r h = ∑ a, r a * (h a - wmean r h) ^ 2 := rfl
  rw [hw]; ring

private lemma wvar_le {α : Type*} [Fintype α] (r h : α → ℝ) (hr1 : ∑ a, r a = 1) (m : ℝ) :
    wvar r h ≤ ∑ a, r a * (h a - m) ^ 2 := by
  rw [sum_sq_shift r h hr1 m]
  have := sq_nonneg (wmean r h - m)
  linarith

private lemma wvar_nonneg {α : Type*} [Fintype α] (r h : α → ℝ) (hr0 : ∀ a, 0 ≤ r a) :
    0 ≤ wvar r h :=
  Finset.sum_nonneg fun a _ => mul_nonneg (hr0 a) (sq_nonneg _)

private lemma sq_wmean_le {α : Type*} [Fintype α] (r h : α → ℝ) (hr0 : ∀ a, 0 ≤ r a)
    (hr1 : ∑ a, r a = 1) : wmean r h ^ 2 ≤ ∑ a, r a * h a ^ 2 := by
  have e := sum_sq_shift r h hr1 0
  simp only [sub_zero] at e
  rw [e]
  have := wvar_nonneg r h hr0
  linarith

/-- The variance of a weighted average of functions, `fun b => ∑ a, q a * H a b`, is at most the
weighted average `∑ a, q a * wvar r (H a)` of their variances. -/
private lemma wvar_mix_le {α β : Type*} [Fintype α] [Fintype β] (q : α → ℝ) (r : β → ℝ)
    (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∑ a, q a = 1) (hr0 : ∀ b, 0 ≤ r b) (hr1 : ∑ b, r b = 1)
    (H : α → β → ℝ) :
    wvar r (fun b => ∑ a, q a * H a b) ≤ ∑ a, q a * wvar r (H a) := by
  have step1 := wvar_le r (fun b => ∑ a, q a * H a b) hr1 (∑ a, q a * wmean r (H a))
  refine step1.trans ?_
  have step2 : ∀ b, (∑ a, q a * H a b - ∑ a, q a * wmean r (H a)) ^ 2
      ≤ ∑ a, q a * (H a b - wmean r (H a)) ^ 2 := by
    intro b
    have e : ∑ a, q a * H a b - ∑ a, q a * wmean r (H a)
        = wmean q (fun a => H a b - wmean r (H a)) := by
      change _ = ∑ a, q a * (H a b - wmean r (H a))
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [e]
    exact sq_wmean_le q _ hq0 hq1
  calc _ ≤ ∑ b, r b * ∑ a, q a * (H a b - wmean r (H a)) ^ 2 :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (step2 b) (hr0 b)
    _ = ∑ a, q a * wvar r (H a) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        change _ = q a * ∑ b, r b * (H a b - wmean r (H a)) ^ 2
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring

/-- Weighted Popoviciu inequality: values within a band of width `c` have variance
at most `c ^ 2 / 4`. -/
private lemma wvar_le_of_bdd {α : Type*} [Fintype α] (r h : α → ℝ) (hr0 : ∀ a, 0 ≤ r a)
    (hr1 : ∑ a, r a = 1) (c : ℝ) (hc : ∀ a b, |h a - h b| ≤ c) : wvar r h ≤ c ^ 2 / 4 := by
  have hne : (Finset.univ : Finset α).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    rw [hcon, Finset.sum_empty] at hr1
    exact zero_ne_one hr1
  obtain ⟨a0, -, ha0⟩ := Finset.exists_min_image Finset.univ h hne
  have key : ∀ a, (h a - (h a0 + c / 2)) ^ 2 ≤ c ^ 2 / 4 := by
    intro a
    have h1 : h a0 ≤ h a := ha0 a (Finset.mem_univ a)
    have h2 : h a - h a0 ≤ c := (le_abs_self _).trans (hc a a0)
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]
  calc wvar r h ≤ ∑ a, r a * (h a - (h a0 + c / 2)) ^ 2 := wvar_le r h hr1 _
    _ ≤ ∑ a, r a * (c ^ 2 / 4) :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (key a) (hr0 a)
    _ = c ^ 2 / 4 := by rw [← Finset.sum_mul, hr1, one_mul]

private lemma weight_nonneg {n : ℕ} {Ω : Fin n → Type*} (p : ∀ i, Ω i → ℝ)
    (hp0 : ∀ i a, 0 ≤ p i a) (x : ∀ i, Ω i) : 0 ≤ weight p x :=
  Finset.prod_nonneg fun i _ => hp0 i (x i)

private def consEquiv' {n : ℕ} (Ω : Fin (n + 1) → Type*) :
    Ω 0 × (∀ i : Fin n, Ω i.succ) ≃ ∀ i, Ω i where
  toFun z := Fin.cons z.1 z.2
  invFun x := (x 0, Fin.tail x)
  left_inv z := by rcases z with ⟨a, y⟩; simp
  right_inv x := by simp

private lemma sum_cons {n : ℕ} {Ω : Fin (n + 1) → Type*} [∀ i, Fintype (Ω i)]
    (F : (∀ i, Ω i) → ℝ) :
    ∑ x, F x = ∑ a : Ω 0, ∑ y : (∀ i : Fin n, Ω i.succ), F (Fin.cons a y) := by
  calc ∑ x, F x = ∑ z, F (consEquiv' Ω z) := ((consEquiv' Ω).sum_comp F).symm
    _ = ∑ a : Ω 0, ∑ y : (∀ i : Fin n, Ω i.succ), F (consEquiv' Ω (a, y)) := by
        rw [Fintype.sum_prod_type]
    _ = ∑ a : Ω 0, ∑ y : (∀ i : Fin n, Ω i.succ), F (Fin.cons a y) := rfl

private lemma weight_cons {n : ℕ} {Ω : Fin (n + 1) → Type*} (p : ∀ i, Ω i → ℝ) (a : Ω 0)
    (y : ∀ i : Fin n, Ω i.succ) :
    weight p (Fin.cons a y : ∀ i, Ω i) = p 0 a * weight (fun i : Fin n => p i.succ) y := by
  simp only [weight, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

private lemma sum_weight_cons {n : ℕ} {Ω : Fin (n + 1) → Type*} [∀ i, Fintype (Ω i)]
    (p : ∀ i, Ω i → ℝ) (h : (∀ i, Ω i) → ℝ) :
    ∑ x, weight p x * h x = ∑ y : (∀ i : Fin n, Ω i.succ),
      weight (fun i : Fin n => p i.succ) y * ∑ a, p 0 a * h (Fin.cons a y) := by
  rw [sum_cons, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [weight_cons p a y]
  ring

private theorem sum_weight (n : ℕ) : ∀ (Ω : Fin n → Type u) [∀ i, Fintype (Ω i)]
    (p : ∀ i, Ω i → ℝ), (∀ i, ∑ a, p i a = 1) → ∑ x, weight p x = 1 := by
  induction n with
  | zero =>
    intro Ω _ p _
    rw [Fintype.sum_unique]
    simp [weight]
  | succ n ih =>
    intro Ω _ p hp1
    have e := sum_weight_cons p (fun _ => (1 : ℝ))
    simp only [mul_one] at e
    rw [e, hp1 0]
    simp only [mul_one]
    exact ih (fun j => Ω j.succ) (fun j => p j.succ) (fun j => hp1 _)

/-- Average over the first coordinate. -/
private def marg {n : ℕ} {Ω : Fin (n + 1) → Type*} [∀ i, Fintype (Ω i)]
    (p : ∀ i, Ω i → ℝ) (f : (∀ i, Ω i) → ℝ) (y : ∀ i : Fin n, Ω i.succ) : ℝ :=
  wmean (p 0) (fun a => f (Fin.cons a y))

private lemma expect_marg {n : ℕ} {Ω : Fin (n + 1) → Type*} [∀ i, Fintype (Ω i)]
    (p : ∀ i, Ω i → ℝ) (f : (∀ i, Ω i) → ℝ) :
    expect p f = expect (fun j : Fin n => p j.succ) (marg p f) :=
  sum_weight_cons p f

/-- Law of total variance, splitting off the first coordinate. -/
private lemma variance_split {n : ℕ} {Ω : Fin (n + 1) → Type*} [∀ i, Fintype (Ω i)]
    (p : ∀ i, Ω i → ℝ) (f : (∀ i, Ω i) → ℝ) (hp1 : ∑ a, p 0 a = 1) :
    variance p f = (∑ y : (∀ i : Fin n, Ω i.succ), weight (fun j : Fin n => p j.succ) y *
        wvar (p 0) (fun a => f (Fin.cons a y))) +
      variance (fun j : Fin n => p j.succ) (marg p f) := by
  have e1 : variance p f = ∑ y : (∀ i : Fin n, Ω i.succ), weight (fun j : Fin n => p j.succ) y *
      ∑ a, p 0 a * (f (Fin.cons a y) - expect p f) ^ 2 :=
    sum_weight_cons p (fun x => (f x - expect p f) ^ 2)
  rw [e1]
  have e2 : ∀ y : (∀ i : Fin n, Ω i.succ), ∑ a, p 0 a * (f (Fin.cons a y) - expect p f) ^ 2
      = wvar (p 0) (fun a => f (Fin.cons a y)) + (marg p f y - expect p f) ^ 2 :=
    fun y => sum_sq_shift (p 0) (fun a => f (Fin.cons a y)) hp1 (expect p f)
  simp only [e2, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [expect_marg p f]
  rfl

private lemma expect_coordVar_zero {n : ℕ} {Ω : Fin (n + 1) → Type*} [∀ i, Fintype (Ω i)]
    (p : ∀ i, Ω i → ℝ) (f : (∀ i, Ω i) → ℝ) (hp1 : ∑ a, p 0 a = 1) :
    expect p (coordVar p 0 f) = ∑ y : (∀ i : Fin n, Ω i.succ),
      weight (fun j : Fin n => p j.succ) y * wvar (p 0) (fun a => f (Fin.cons a y)) := by
  have e1 : expect p (coordVar p 0 f) = ∑ y : (∀ i : Fin n, Ω i.succ),
      weight (fun j : Fin n => p j.succ) y * ∑ a, p 0 a * coordVar p 0 f (Fin.cons a y) :=
    sum_weight_cons p (coordVar p 0 f)
  rw [e1]
  refine Finset.sum_congr rfl fun y _ => ?_
  have e3 : ∀ a : Ω 0, coordVar p 0 f (Fin.cons a y) = wvar (p 0) (fun b => f (Fin.cons b y)) := by
    intro a
    change wvar (p 0) (fun b => f (Function.update (Fin.cons a y) 0 b)) = _
    simp only [Fin.update_cons_zero]
  simp only [e3, ← Finset.sum_mul, hp1, one_mul]

private lemma coord_succ_le {n : ℕ} {Ω : Fin (n + 1) → Type*} [∀ i, Fintype (Ω i)]
    (p : ∀ i, Ω i → ℝ) (f : (∀ i, Ω i) → ℝ) (hp0 : ∀ i a, 0 ≤ p i a)
    (hp1 : ∀ i, ∑ a, p i a = 1) (i : Fin n) :
    expect (fun j : Fin n => p j.succ) (coordVar (fun j : Fin n => p j.succ) i (marg p f))
      ≤ expect p (coordVar p i.succ f) := by
  have e1 : expect p (coordVar p i.succ f) = ∑ y : (∀ j : Fin n, Ω j.succ),
      weight (fun j : Fin n => p j.succ) y * ∑ a, p 0 a * coordVar p i.succ f (Fin.cons a y) :=
    sum_weight_cons p (coordVar p i.succ f)
  rw [e1]
  change ∑ y : (∀ j : Fin n, Ω j.succ), weight (fun j : Fin n => p j.succ) y *
      coordVar (fun j : Fin n => p j.succ) i (marg p f) y ≤ _
  refine Finset.sum_le_sum fun y _ => ?_
  refine mul_le_mul_of_nonneg_left ?_
    (weight_nonneg (fun j : Fin n => p j.succ) (fun j a => hp0 _ a) y)
  have e3 : ∀ a : Ω 0, coordVar p i.succ f (Fin.cons a y)
      = wvar (p i.succ) (fun b => f (Fin.cons a (Function.update y i b))) := by
    intro a
    change wvar (p i.succ) (fun b => f (Function.update (Fin.cons a y) i.succ b)) = _
    simp only [← Fin.cons_update]
  simp only [e3]
  exact wvar_mix_le (p 0) (p i.succ) (hp0 0) (hp1 0) (hp0 i.succ) (hp1 i.succ)
    (fun a b => f (Fin.cons a (Function.update y i b)))

private theorem es_aux (n : ℕ) : ∀ (Ω : Fin n → Type u) [∀ i, Fintype (Ω i)]
    (p : ∀ i, Ω i → ℝ), (∀ i a, 0 ≤ p i a) → (∀ i, ∑ a, p i a = 1) →
    ∀ f : (∀ i, Ω i) → ℝ, variance p f ≤ ∑ i, expect p (coordVar p i f) := by
  induction n with
  | zero =>
    intro Ω _ p _ _ f
    have hv : variance p f = 0 := by
      change ∑ x, weight p x * (f x - ∑ y, weight p y * f y) ^ 2 = 0
      rw [Fintype.sum_unique, Fintype.sum_unique]
      simp [weight]
    rw [hv]
    simp
  | succ n ih =>
    intro Ω _ p hp0 hp1 f
    have IH : variance (fun j : Fin n => p j.succ) (marg p f) ≤
        ∑ i : Fin n, expect (fun j : Fin n => p j.succ)
          (coordVar (fun j : Fin n => p j.succ) i (marg p f)) :=
      ih (fun j => Ω j.succ) (fun j => p j.succ) (fun j a => hp0 _ a) (fun j => hp1 _) (marg p f)
    have hF : ∑ i : Fin n, expect (fun j : Fin n => p j.succ)
          (coordVar (fun j : Fin n => p j.succ) i (marg p f))
        ≤ ∑ i : Fin n, expect p (coordVar p i.succ f) :=
      Finset.sum_le_sum fun i _ => coord_succ_le p f hp0 hp1 i
    rw [variance_split p f (hp1 0), Fin.sum_univ_succ]
    exact add_le_add (le_of_eq (expect_coordVar_zero p f (hp1 0)).symm) (IH.trans hF)

/-- **The Efron–Stein inequality** for independent coordinates on finite sets. Item 121 of
MATH-PLAN-library-2 (order CLOUD-MATH-3). Under the product of the probability vectors `p i`, the
variance of `f` is at most the sum, over the coordinates, of the mean of its variance in that
coordinate alone: `Var f ≤ ∑ᵢ E[Varᵢ f]`. -/
theorem variance_le_sum_variance_coord {n : ℕ} {Ω : Fin n → Type u} [∀ i, Fintype (Ω i)]
    (p : ∀ i, Ω i → ℝ) (hp0 : ∀ i a, 0 ≤ p i a) (hp1 : ∀ i, ∑ a, p i a = 1)
    (f : (∀ i, Ω i) → ℝ) :
    variance p f ≤ ∑ i, expect p (coordVar p i f) :=
  es_aux n Ω p hp0 hp1 f

/-- **Bounded differences.** Item 121 of MATH-PLAN-library-2 (order CLOUD-MATH-3). If changing
coordinate `i` alone moves `f` by at most `c i`, then the variance of `f` under the product of the
probability vectors `p i` is at most `∑ i, c i ^ 2 / 4`. -/
theorem variance_le_sum_sq_div_four {n : ℕ} {Ω : Fin n → Type u} [∀ i, Fintype (Ω i)]
    (p : ∀ i, Ω i → ℝ) (hp0 : ∀ i a, 0 ≤ p i a) (hp1 : ∀ i, ∑ a, p i a = 1)
    (f : (∀ i, Ω i) → ℝ) (c : Fin n → ℝ)
    (hc : ∀ i (x : ∀ i, Ω i) (a b : Ω i),
      |f (Function.update x i a) - f (Function.update x i b)| ≤ c i) :
    variance p f ≤ ∑ i, c i ^ 2 / 4 := by
  have hE : ∀ i, expect p (coordVar p i f) ≤ c i ^ 2 / 4 := by
    intro i
    calc expect p (coordVar p i f)
        = ∑ x, weight p x * coordVar p i f x := rfl
      _ ≤ ∑ x, weight p x * (c i ^ 2 / 4) :=
          Finset.sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_left
              (wvar_le_of_bdd (p i) (fun a => f (Function.update x i a))
                (hp0 i) (hp1 i) (c i) (fun a b => hc i x a b))
              (weight_nonneg p hp0 x)
      _ = c i ^ 2 / 4 := by
          rw [← Finset.sum_mul, sum_weight n Ω p hp1, one_mul]
  exact (variance_le_sum_variance_coord p hp0 hp1 f).trans
    (Finset.sum_le_sum fun i _ => hE i)

end ClassicalLean.Probability.EfronStein

/-- The hypotheses of `variance_le_sum_variance_coord` hold together: two coordinates (`n = 2`),
each taking the two values of `Fin 2`, the first with the weights `1 / 4` and `3 / 4`, the second
with `1 / 2` and `1 / 2`, so that each `p i` is a probability vector and the two differ; `f` is
`x 0 + 2 * x 1`, the values read as reals, which depends on both coordinates. -/
example := ClassicalLean.Probability.EfronStein.variance_le_sum_variance_coord (n := 2)
    (Ω := fun _ => Fin 2) (p := fun i a => ![![1 / 4, 3 / 4], ![1 / 2, 1 / 2]] i a)
    (fun i a => by fin_cases i <;> fin_cases a <;> norm_num)
    (fun i => by fin_cases i <;> norm_num [Fin.sum_univ_two])
    (f := fun x => ((x 0 : ℕ) : ℝ) + 2 * ((x 1 : ℕ) : ℝ))

/-- The hypotheses of `variance_le_sum_sq_div_four` hold together: the same two coordinates,
weights and `f = x 0 + 2 * x 1` as above, and the bounds `c = (1, 2)`: changing coordinate `0`
alone moves `f` by `0` or `1`, and changing coordinate `1` alone moves it by `0` or `2`. -/
example := ClassicalLean.Probability.EfronStein.variance_le_sum_sq_div_four (n := 2)
    (Ω := fun _ => Fin 2) (p := fun i a => ![![1 / 4, 3 / 4], ![1 / 2, 1 / 2]] i a)
    (fun i a => by fin_cases i <;> fin_cases a <;> norm_num)
    (fun i => by fin_cases i <;> norm_num [Fin.sum_univ_two])
    (f := fun x => ((x 0 : ℕ) : ℝ) + 2 * ((x 1 : ℕ) : ℝ)) (c := ![1, 2])
    (fun i x a b => by
      fin_cases i <;> fin_cases a <;> fin_cases b <;> norm_num [Function.update])

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.foldStage2 (fun acc n _ => acc.push n) (#[] : Array Name)
  logInfo m!"ALLCONST {names.size}"
  for n in names do logInfo m!"CONST {n}"
