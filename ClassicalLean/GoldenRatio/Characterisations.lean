/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Matrix.Mul

/-!
# Five characterisations of the golden ratio

The golden ratio `φ = (1 + √5)/2` can be pinned down in several independent ways.
This file collects five of them and states each against Mathlib's `Real.goldenRatio`,
together with a sixth, hyperbolic, identity that relates `φ` to `cosh`.

1. **Algebraic** — `φ` is a root of `X² - X - 1`; the real roots of that polynomial are
   exactly `φ` and its conjugate `ψ = (1 - √5)/2`; and `φ` is the *only positive* one.
2. **Limit** — `φ` is the limit of the ratios `F(n+1)/F(n)` of consecutive Fibonacci numbers.
3. **Trigonometric** — `φ = 2·cos(π/5)`.
4. **Spectral** — `(φ, 1)` is an eigenvector of the Fibonacci companion matrix `!![1,1;1,0]`
   with eigenvalue `φ`, and the real numbers `x` at which `det(M - x·I)` vanishes are exactly
   `φ` and `ψ`, so `φ` is the largest of them in absolute value. Everything here is stated
   through the determinant, which is what is proved; the general bridge from a vanishing
   determinant to the spectrum of an operator is not proved in this file.
5. **Dynamical** — `φ` is the unique positive fixed point of the map `T(x) = 1 + 1/x`.
6. **Hyperbolic** — `cosh(log φ) = √5/2`, next to the companion identity `cosh(log 2) = 5/4`.

Dated 2026-09-24 (order G-7, J2 step 6; round 23): a seventh section holds two facts about
`φ²`, a root of `x² - 3x + 1`, moved here from `Geometry/Helix` so that each is proved once:
`inv_goldenRatio_sq_eq_goldenConj_sq` and `goldenRatio_sq_add_inv_eq_three`.

Several of these results are Mathlib's own and are gathered here rather than reproved. Those
docstrings open with the marker **Mathlib re-export** and name the lemma; a declaration that is
merely derived from a Mathlib lemma names that lemma too, and everything else is proved here.
So a reader can tell at a glance which statements this file proves and which it collects.
-/

open Matrix Real Filter Topology

namespace ClassicalLean.GoldenRatio

/-! ## 1. The algebraic characterisation

`φ` is a root of `X² - X - 1`, the real roots of that quadratic are exactly `φ` and `ψ`,
their sum is `1` and their product is `-1` (Vieta), and `φ` is the unique positive root. -/

/-- The golden ratio is a root of `X² - X - 1`, i.e. `φ² = φ + 1`. One `linarith` away from
Mathlib's `Real.goldenRatio_sq`. -/
theorem goldenRatio_isRoot : goldenRatio ^ 2 - goldenRatio - 1 = 0 := by
  have h : goldenRatio ^ 2 = goldenRatio + 1 := Real.goldenRatio_sq
  linarith

/-- The conjugate `ψ = (1 - √5)/2` is the second root of `X² - X - 1`. One `linarith` away from
Mathlib's `Real.goldenConj_sq`. -/
theorem goldenConj_isRoot : goldenConj ^ 2 - goldenConj - 1 = 0 := by
  have h : goldenConj ^ 2 = goldenConj + 1 := Real.goldenConj_sq
  linarith

/-- **Mathlib re-export** of `Real.goldenRatio_add_goldenConj`, collected here as Vieta's sum
relation: the two roots of `X² - X - 1` add up to `1`, the negated linear coefficient. -/
theorem vieta_sum : goldenRatio + goldenConj = 1 :=
  Real.goldenRatio_add_goldenConj

/-- **Mathlib re-export** of `Real.goldenRatio_mul_goldenConj`, collected here as Vieta's
product relation: the two roots of `X² - X - 1` multiply to `-1`, the constant coefficient. -/
theorem vieta_prod : goldenRatio * goldenConj = -1 :=
  Real.goldenRatio_mul_goldenConj

/-- **Completeness of the root list.** A real number satisfies `x² - x - 1 = 0` if and only
if it is `φ` or `ψ`. The proof factors the quadratic as `(x - φ)(x - ψ)` using Vieta. -/
theorem quadratic_roots (x : ℝ) :
    x ^ 2 - x - 1 = 0 ↔ x = goldenRatio ∨ x = goldenConj := by
  have h1 : goldenRatio + goldenConj = 1 := Real.goldenRatio_add_goldenConj
  have h2 : goldenRatio * goldenConj = -1 := Real.goldenRatio_mul_goldenConj
  have hfac : ∀ y : ℝ, y ^ 2 - y - 1 = (y - goldenRatio) * (y - goldenConj) := by
    intro y
    have : (y - goldenRatio) * (y - goldenConj)
        = y ^ 2 - (goldenRatio + goldenConj) * y + goldenRatio * goldenConj := by ring
    rw [this, h1, h2]; ring
  constructor
  · intro hx
    rcases mul_eq_zero.mp ((hfac x) ▸ hx) with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  · rintro (rfl | rfl) <;> rw [hfac] <;> simp

/-- **The algebraic characterisation.** Among the positive reals, `φ` is the *only* root of
`X² - X - 1`: the other root `ψ` is negative. This is what makes "the positive root of
`x² = x + 1`" a definition rather than merely a description. -/
theorem goldenRatio_unique_pos_root {x : ℝ} (hx : 0 < x) :
    x ^ 2 - x - 1 = 0 ↔ x = goldenRatio := by
  constructor
  · intro h
    rcases (quadratic_roots x).mp h with rfl | rfl
    · rfl
    · linarith [Real.goldenConj_neg]
  · rintro rfl
    exact goldenRatio_isRoot

/-- **Mathlib re-export** of `Real.one_lt_goldenRatio` and `Real.goldenRatio_lt_two`, paired
here: `1 < φ` and `φ < 2`, which localises the positive root of `X² - X - 1`. -/
theorem one_lt_goldenRatio_and_lt_two : 1 < goldenRatio ∧ goldenRatio < 2 :=
  ⟨Real.one_lt_goldenRatio, Real.goldenRatio_lt_two⟩

/-- The polynomial `x² - x - 1` is negative at `1` and positive at `2`. This is a `norm_num`
evaluation at those two points and nothing more: no intermediate value theorem is invoked and
no interval membership is derived from it. The bounds on `φ` itself are the separate theorem
`one_lt_goldenRatio_and_lt_two` above; the sign change is the classical reason to look for a
root between `1` and `2` in the first place. -/
example : (1 : ℝ) ^ 2 - 1 - 1 < 0 ∧ (0 : ℝ) < (2 : ℝ) ^ 2 - 2 - 1 := by norm_num

/-- The closed form of the golden ratio. This holds by `rfl`: Mathlib's `Real.goldenRatio` is
an `abbrev` for `(1 + √5)/2`, so the equation is a definitional unfolding, not a computation. -/
example : goldenRatio = (1 + Real.sqrt 5) / 2 := rfl

/-! ## 2. The limit characterisation

`φ` is the limit of the ratios of consecutive Fibonacci numbers. -/

/-- **Mathlib re-export** of `tendsto_fib_succ_div_fib_atTop` (the statement here only spells
the casts into `ℝ` out; the proof is that lemma verbatim). The limit characterisation: the
ratio `F(n+1)/F(n)` of consecutive Fibonacci numbers converges to the golden ratio. -/
theorem fib_ratio_tendsto_goldenRatio :
    Tendsto (fun n : ℕ => (Nat.fib (n + 1) : ℝ) / (Nat.fib n : ℝ))
      atTop (𝓝 goldenRatio) :=
  tendsto_fib_succ_div_fib_atTop

/-- A single Fibonacci convergent: `F(13)/F(12) = 233/144`, a `norm_num` evaluation. Its
decimal value `1.6180…` is a remark, not part of the statement. -/
example : (Nat.fib 13 : ℚ) / (Nat.fib 12 : ℚ) = 233 / 144 := by norm_num

/-! ## 3. The trigonometric characterisation

`φ = 2·cos(π/5)`: the golden ratio is twice the cosine of `π/5`. Context, not proved here: in a
regular pentagon inscribed in a circle of radius `R` the side subtends central angle `2π/5` and
a diagonal subtends `4π/5`, so their lengths are `2R·sin(π/5)` and `2R·sin(2π/5)`, which is
what makes `sin(2π/5)/sin(π/5)` the diagonal-to-side ratio. -/

/-- **Mathlib re-export** of `Real.cos_pi_div_five`: the cosine of `π/5` in closed form. -/
theorem cos_pi_div_five_eq : Real.cos (π / 5) = (1 + Real.sqrt 5) / 4 :=
  Real.cos_pi_div_five

/-- **The trigonometric characterisation.** `2·cos(π/5) = φ`. Proved here by combining the
re-exported `cos_pi_div_five_eq` with the definition of `Real.goldenRatio`. -/
theorem two_cos_pi_div_five_eq_goldenRatio : 2 * Real.cos (π / 5) = goldenRatio := by
  rw [cos_pi_div_five_eq, Real.goldenRatio]; ring

/-- **Mathlib re-export** of `Real.quadratic_root_cos_pi_div_five`: `c = cos(π/5)` is a root of
`4X² - 2X - 1`, the quadratic obtained from `X² - X - 1` by the substitution `X = 2c`. That this
quadratic is the *minimal* polynomial of `c` over `ℚ` is classical context: it needs
irreducibility, which is not proved here, so neither the statement nor the name of this
declaration claims it. -/
theorem cos_pi_div_five_quadratic_root :
    4 * Real.cos (π / 5) ^ 2 - 2 * Real.cos (π / 5) - 1 = 0 :=
  Real.quadratic_root_cos_pi_div_five

/-- `cos(π/5)` is irrational. Proved here from `two_cos_pi_div_five_eq_goldenRatio` and
Mathlib's `Real.goldenRatio_irrational`: `cos(π/5)` is `φ/2`, and `φ` is irrational. -/
theorem cos_pi_div_five_irrational : Irrational (Real.cos (π / 5)) := by
  rintro ⟨q, hq⟩
  exact Real.goldenRatio_irrational
    ⟨2 * q, by rw [← two_cos_pi_div_five_eq_goldenRatio, ← hq]; push_cast; ring⟩

/-- **A chord-ratio identity.** `sin(2π/5) / sin(π/5) = 2·cos(π/5)`, proved here from the
double-angle formula for `sin`. Context, not proved here: in a regular pentagon inscribed in a
circle the left-hand side is the ratio of a diagonal to a side; combined with
`two_cos_pi_div_five_eq_goldenRatio` that identifies the ratio with `φ`. -/
theorem chord_ratio_eq_two_cos :
    Real.sin (2 * π / 5) / Real.sin (π / 5) = 2 * Real.cos (π / 5) := by
  have hs : Real.sin (π / 5) ≠ 0 := by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    linarith [Real.pi_pos]
  rw [show 2 * π / 5 = 2 * (π / 5) by ring, Real.sin_two_mul]
  field_simp

/-! ## 4. The spectral characterisation

`(φ, 1)` is an eigenvector of the Fibonacci companion matrix `!![1,1;1,0]` with eigenvalue `φ`,
and the real `x` at which `det(M - x·I)` vanishes are exactly `φ` and `ψ`; since `|ψ| < φ`, the
largest such absolute value is `φ`.

Everything in this section is stated through the determinant `det(M - x·I)`, because that is
what is proved. The step from "the determinant vanishes at `x`" to "`x` is an eigenvalue" is
classical and true, but it is not proved here, so no statement below is phrased as a claim about
the spectrum of an operator. Context, not proved here: the matrix is called the companion matrix
of the Fibonacci recurrence because its powers generate the Fibonacci sequence. -/

/-- The Fibonacci companion matrix `!![1,1;1,0]`. Its action on a vector is `fibMatrix_mulVec`
below. -/
def fibMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 0]

/-- The companion matrix sends `(a, b)` to `(a + b, a)`. This is the sense in which it carries
the Fibonacci recurrence: the first coordinate of the image is the sum of the two inputs. -/
theorem fibMatrix_mulVec (a b : ℝ) : fibMatrix.mulVec ![a, b] = ![a + b, a] := by
  funext i
  fin_cases i <;> simp [fibMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The companion matrix has trace `1`, the negated linear coefficient of `X² - X - 1`. -/
theorem fibMatrix_trace : fibMatrix.trace = 1 := by
  simp [fibMatrix, Matrix.trace_fin_two]

/-- The companion matrix has determinant `-1`, the constant coefficient of `X² - X - 1`. -/
theorem fibMatrix_det : fibMatrix.det = -1 := by
  simp [fibMatrix, Matrix.det_fin_two]

/-- The companion matrix is symmetric. Symmetry is the whole claim here. It is worth recording
because of the classical spectral theorem — a real symmetric matrix has a real spectrum — but
that general theorem is neither invoked nor proved in this file, and nothing below is derived
from it. What this file does prove about this particular matrix is
`fibMatrix_det_sub_smul_eq_zero_iff`, which pins down the real `x` where `det(M - x·I)` vanishes
as exactly `φ` and `ψ`. -/
theorem fibMatrix_isSymm : fibMatrix.IsSymm := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- The vector `(φ, 1)` is nonzero — its second coordinate is `1`. Recorded so that the word
"eigenvector" in `fibMatrix_mulVec_eigen` is backed by a proof rather than left to the reader:
an eigenvector is by definition nonzero. -/
theorem goldenRatio_vec_ne_zero : ![goldenRatio, 1] ≠ (0 : Fin 2 → ℝ) := by
  intro h
  have h1 : (![goldenRatio, 1] : Fin 2 → ℝ) 1 = (0 : Fin 2 → ℝ) 1 := by rw [h]
  simp at h1

/-- **An eigenpair.** `(φ, 1)` is an eigenvector of the companion matrix with eigenvalue `φ`:
this statement gives `M ⬝ᵥ (φ,1) = φ • (φ,1)`, and `goldenRatio_vec_ne_zero` gives the
nonvanishing that the word "eigenvector" requires. The computation reduces to `φ² = φ + 1`.
That this eigenvalue is the dominant one is not this statement; it is
`goldenRatio_isSpectralRadius` below, via `abs_goldenConj_lt_goldenRatio`. -/
theorem fibMatrix_mulVec_eigen :
    fibMatrix.mulVec ![goldenRatio, 1] = goldenRatio • ![goldenRatio, 1] := by
  funext i
  fin_cases i <;>
    simp [fibMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  nlinarith [Real.goldenRatio_sq]

/-- **The characteristic polynomial.** `det(M - x·I) = x² - x - 1` for every real `x`. Which
real `x` make that determinant vanish is the next lemma. -/
theorem fibMatrix_det_sub_smul (x : ℝ) :
    (fibMatrix - x • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = x ^ 2 - x - 1 := by
  simp [fibMatrix, Matrix.det_fin_two, Matrix.sub_apply, Matrix.smul_apply]
  ring

/-- **The real spectrum of the companion matrix.** A real number `x` satisfies
`det(M - x·I) = 0` if and only if it is `φ` or `ψ`: the real roots of the characteristic
polynomial are exactly the roots of `X² - X - 1`. This is `fibMatrix_det_sub_smul`
composed with `quadratic_roots`; it is a statement about real `x` only and says nothing about
eigenvalues over `ℂ`. -/
theorem fibMatrix_det_sub_smul_eq_zero_iff (x : ℝ) :
    (fibMatrix - x • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 ↔
      x = goldenRatio ∨ x = goldenConj := by
  rw [fibMatrix_det_sub_smul]
  exact quadratic_roots x

/-- **Dominance.** `|ψ| < φ`: the second root of `X² - X - 1` is smaller in absolute value than
the first. Context, not proved here: this gap is the classical reason the Fibonacci growth rate
is exactly `φ`. -/
theorem abs_goldenConj_lt_goldenRatio : |goldenConj| < goldenRatio := by
  have hψ : goldenConj < 0 := Real.goldenConj_neg
  have hsum : goldenRatio + goldenConj = 1 := Real.goldenRatio_add_goldenConj
  rw [abs_of_neg hψ]; linarith

/-- **The spectral characterisation.** Three conjuncts:

* `M ⬝ᵥ (φ,1) = φ • (φ,1)` — with `goldenRatio_vec_ne_zero`, an eigenpair;
* `det(M - φ·I) = 0` — the value `φ` is *attained*;
* every real `x` with `det(M - x·I) = 0` satisfies `|x| ≤ φ` — and none is exceeded.

Attainment is the conjunct that makes "largest" a maximum rather than an upper bound, so it is
proved rather than left implicit. Together the three say that `φ` is the largest absolute value
at which `det(M - x·I)` vanishes over `ℝ` — the spectral radius computed over `ℝ`, phrased
throughout by the determinant, which is what this file proves. -/
theorem goldenRatio_isSpectralRadius :
    (fibMatrix.mulVec ![goldenRatio, 1] = goldenRatio • ![goldenRatio, 1])
    ∧ (fibMatrix - goldenRatio • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0
    ∧ (∀ x : ℝ, (fibMatrix - x • 1).det = 0 → |x| ≤ goldenRatio) := by
  refine ⟨fibMatrix_mulVec_eigen,
    (fibMatrix_det_sub_smul_eq_zero_iff goldenRatio).mpr (Or.inl rfl), fun x hx => ?_⟩
  have hroot : x = goldenRatio ∨ x = goldenConj :=
    (quadratic_roots x).mp (by rw [← fibMatrix_det_sub_smul]; exact hx)
  rcases hroot with rfl | rfl
  · rw [abs_of_pos Real.goldenRatio_pos]
  · exact le_of_lt abs_goldenConj_lt_goldenRatio

/-! ## 5. The dynamical characterisation

`φ` is the unique positive fixed point of the continued-fraction map `T(x) = 1 + 1/x`. -/

/-- **The fixed-point equation.** `1 + φ⁻¹ = φ`, i.e. `φ` is a fixed point of `T(x) = 1 + 1/x`.
Derived here by rewriting with Mathlib's `Real.inv_goldenRatio` and one `linarith` from
`Real.one_sub_goldenRatio`.
Context, not proved here: iterating the equation displays `φ` as the continued fraction
`1 + 1/(1 + 1/(1 + …))` of all ones. -/
theorem one_add_inv_goldenRatio : 1 + goldenRatio⁻¹ = goldenRatio := by
  rw [Real.inv_goldenRatio]
  linarith [Real.one_sub_goldenRatio]

/-- **The dynamical characterisation.** Among the positive reals, `φ` is the *only* fixed
point of `T(x) = 1 + 1/x`. Clearing the denominator turns the fixed-point equation into
`x² - x - 1 = 0`, whose unique positive solution is `φ`. -/
theorem goldenRatio_unique_pos_fixedPoint {x : ℝ} (hx : 0 < x) :
    1 + x⁻¹ = x ↔ x = goldenRatio := by
  constructor
  · intro h
    have h2 : x * (1 + x⁻¹) = x * x := by rw [h]
    rw [mul_add, mul_one, mul_inv_cancel₀ hx.ne'] at h2
    exact (goldenRatio_unique_pos_root hx).mp (by nlinarith [h2])
  · rintro rfl
    exact one_add_inv_goldenRatio

/-- Four iterates of `T(x) = 1 + 1/x` starting from `1` give `8/5 = F(6)/F(5)`. This is the
single arithmetic instance; that the whole orbit of `T` runs through the Fibonacci convergents
is context, not proved here. -/
example : (1 : ℚ) + (1 + (1 + (1 + (1 : ℚ)⁻¹)⁻¹)⁻¹)⁻¹ = 8 / 5 := by norm_num

/-! ## 6. A hyperbolic identity

For positive `x`, Mathlib's `Real.cosh_log` gives `cosh(log x) = (x + x⁻¹)/2`, so the
hyperbolic cosine of a logarithm reads off the "self-plus-reciprocal" of its argument. Both
identities below are that lemma evaluated at a point: at `2` it gives `5/4`, and at `φ` it
gives `√5/2`, using Mathlib's `Real.inv_goldenRatio` (`φ⁻¹ = -ψ`) and
`Real.goldenRatio_sub_goldenConj` (`φ - ψ = √5`). -/

/-- `cosh(log 2) = 5/4`, since `(2 + 2⁻¹)/2 = 5/4`. Proved here from Mathlib's
`Real.cosh_log`. -/
theorem cosh_log_two : Real.cosh (Real.log 2) = 5 / 4 := by
  rw [Real.cosh_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- `cosh(log φ) = √5/2` for Mathlib's `Real.goldenRatio`, since `φ⁻¹ = -ψ` and `φ - ψ = √5`.
Proved here from Mathlib's `Real.cosh_log`, `Real.inv_goldenRatio` and
`Real.goldenRatio_sub_goldenConj`. -/
theorem cosh_log_goldenRatio : Real.cosh (Real.log goldenRatio) = Real.sqrt 5 / 2 := by
  rw [Real.cosh_log Real.goldenRatio_pos, Real.inv_goldenRatio]
  linarith [Real.goldenRatio_sub_goldenConj]

/-! ## 7. The square `φ²` and its reciprocal

Dated 2026-09-24 (order G-7, J2 step 6; round 23): moved here from `Geometry/Helix`, which imports
this file and uses both. The two statements had also been proved in `Simplex/DesignConstants`
(`goldenConj_sq_eq_inv_goldenRatio_sq`, `goldenRatio_sq_add_inv_sq`, deleted there); this is now
their one home. Both are derived from Mathlib lemmas, named in each docstring. -/

/-- **The second root of `x² - 3x + 1`, written two ways.** `(φ²)⁻¹ = ψ²`, for
`ψ = Real.goldenConj`. This is Mathlib's `Real.inv_goldenRatio` (`φ⁻¹ = -ψ`) squared. It bridges
two namings in `Geometry/Helix`: there the roots of `x² - 3x + 1` are listed with `(φ²)⁻¹`, while
Vieta's product relation for that quadratic, `φ² · ψ² = 1`, is proved about `ψ²`, because that
form carries content. -/
theorem inv_goldenRatio_sq_eq_goldenConj_sq :
    (goldenRatio ^ 2)⁻¹ = goldenConj ^ 2 := by
  rw [← inv_pow, Real.inv_goldenRatio, neg_sq]

/-- **Vieta's sum relation for `x² - 3x + 1`.** `φ² + (φ²)⁻¹ = 3`, i.e. `φ² + ψ² = 3` through
`inv_goldenRatio_sq_eq_goldenConj_sq`. Proved from Mathlib's `Real.goldenRatio_sq`,
`Real.goldenConj_sq` and `Real.goldenRatio_add_goldenConj`. -/
theorem goldenRatio_sq_add_inv_eq_three :
    goldenRatio ^ 2 + (goldenRatio ^ 2)⁻¹ = 3 := by
  rw [inv_goldenRatio_sq_eq_goldenConj_sq, Real.goldenRatio_sq, Real.goldenConj_sq]
  linarith [Real.goldenRatio_add_goldenConj]

end ClassicalLean.GoldenRatio
