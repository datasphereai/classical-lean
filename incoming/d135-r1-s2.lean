import ClassicalLean.Analysis.GradientDescent
import ClassicalLean.Simplex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Frank–Wolfe on the probability simplex

With step `2 / (k + 2)`, for convex `f` whose gradient is `L`-Lipschitz, the Frank–Wolfe
iterates satisfy `f (x k) - f z ≤ 4 L / (k + 2)` for every `k > 0` and every point `z` of the
simplex. The constant comes from the squared diameter `2` of the simplex.
-/

open scoped RealInnerProductSpace NNReal
open ClassicalLean.Analysis ClassicalLean.Simplex

/-- One Frank–Wolfe step on a set of squared diameter at most `D`. -/
private lemma fw_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {f' : E → E} {L : ℝ≥0} {K : Set E} {D : ℝ}
    (hconv : ConvexOn ℝ K f) (hf : ∀ x, HasGradientAt f (f' x) x) (hL : LipschitzWith L f')
    (hD : ∀ a ∈ K, ∀ b ∈ K, ‖a - b‖ ^ 2 ≤ D) {x s z : E} {γ : ℝ}
    (hx : x ∈ K) (hs : s ∈ K) (hz : z ∈ K) (hmin : ⟪f' x, s⟫ ≤ ⟪f' x, z⟫) (hγ : 0 ≤ γ) :
    f (x + γ • (s - x)) - f z ≤ (1 - γ) * (f x - f z) + γ ^ 2 * ((L : ℝ) * D / 2) := by
  have hd := le_add_inner_gradient_add_sq hf hL x (x + γ • (s - x))
  have hdiff : x + γ • (s - x) - x = γ • (s - x) := by abel
  rw [hdiff, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ,
    mul_pow] at hd
  have h1 : ⟪f' x, s - x⟫ ≤ ⟪f' x, z - x⟫ := by
    rw [inner_sub_right, inner_sub_right]; linarith
  have h2 := add_inner_gradient_le hconv hx hz (hf x)
  have h3 := hD s hs x hx
  have h4 := mul_le_mul_of_nonneg_left h1 hγ
  have h5 : γ * ⟪f' x, z - x⟫ ≤ γ * (f z - f x) :=
    mul_le_mul_of_nonneg_left (by linarith) hγ
  have h6 : (L : ℝ) / 2 * (γ ^ 2 * ‖s - x‖ ^ 2) ≤ (L : ℝ) / 2 * (γ ^ 2 * D) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (sq_nonneg γ)) (by positivity)
  linarith

/-- Frank–Wolfe on a convex set of squared diameter at most `D`. -/
private lemma fw_general {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {f' : E → E} {L : ℝ≥0} {K : Set E} {D : ℝ}
    (hK : Convex ℝ K) (hconv : ConvexOn ℝ K f) (hf : ∀ x, HasGradientAt f (f' x) x)
    (hL : LipschitzWith L f') (hD : ∀ a ∈ K, ∀ b ∈ K, ‖a - b‖ ^ 2 ≤ D)
    {x s : ℕ → E} (hx0 : x 0 ∈ K) (hs : ∀ k, s k ∈ K)
    (hmin : ∀ k, ∀ y ∈ K, ⟪f' (x k), s k⟫ ≤ ⟪f' (x k), y⟫)
    (hx : ∀ k : ℕ, x (k + 1) = x k + (2 / ((k : ℝ) + 2)) • (s k - x k))
    {z : E} (hz : z ∈ K) (k : ℕ) :
    f (x (k + 1)) - f z ≤ 2 * (L : ℝ) * D / ((k : ℝ) + 3) := by
  have hDn : 0 ≤ D := by have := hD z hz z hz; simpa using this
  have hM : 0 ≤ (L : ℝ) * D := mul_nonneg L.coe_nonneg hDn
  have hmem : ∀ k, x k ∈ K := by
    intro k
    induction k with
    | zero => exact hx0
    | succ k ih =>
      have hc : (0 : ℝ) ≤ k := k.cast_nonneg
      rw [hx k]
      exact hK.add_smul_sub_mem ih (hs k)
        ⟨by positivity, by rw [div_le_one (by positivity)]; linarith⟩
  have hstep : ∀ k : ℕ, f (x (k + 1)) - f z ≤
      (1 - 2 / ((k : ℝ) + 2)) * (f (x k) - f z) + (2 / ((k : ℝ) + 2)) ^ 2 * ((L : ℝ) * D / 2) := by
    intro k
    rw [hx k]
    exact fw_step hconv hf hL hD (hmem k) (hs k) hz (hmin k z hz) (by positivity)
  induction k with
  | zero =>
    have h := hstep 0
    rw [show (1 : ℝ) - 2 / (((0 : ℕ) : ℝ) + 2) = 0 by norm_num,
      show (2 / (((0 : ℕ) : ℝ) + 2)) ^ 2 = (1 : ℝ) by norm_num] at h
    rw [show (((0 : ℕ) : ℝ) + 3) = 3 by norm_num]
    linarith
  | succ k ih =>
    have h := hstep (k + 1)
    have hc : (0 : ℝ) ≤ k := k.cast_nonneg
    have hne : (k : ℝ) + 3 ≠ 0 := by positivity
    rw [show (((k + 1 : ℕ) : ℝ) + 2) = (k : ℝ) + 3 by push_cast; ring] at h
    have eγ' : (1 : ℝ) - 2 / ((k : ℝ) + 3) = ((k : ℝ) + 1) / ((k : ℝ) + 3) := by
      rw [eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne]; ring
    rw [eγ'] at h
    rw [show (((k + 1 : ℕ) : ℝ) + 3) = (k : ℝ) + 4 by push_cast; ring]
    have h1 : ((k : ℝ) + 1) / ((k : ℝ) + 3) * (f (x (k + 1)) - f z) ≤
        ((k : ℝ) + 1) / ((k : ℝ) + 3) * (2 * (L : ℝ) * D / ((k : ℝ) + 3)) :=
      mul_le_mul_of_nonneg_left ih (by positivity)
    have heq : ((k : ℝ) + 1) / ((k : ℝ) + 3) * (2 * (L : ℝ) * D / ((k : ℝ) + 3)) +
        (2 / ((k : ℝ) + 3)) ^ 2 * ((L : ℝ) * D / 2) =
        2 * (L : ℝ) * D * ((k : ℝ) + 2) / ((k : ℝ) + 3) ^ 2 := by
      first
        | (field_simp; ring)
        | field_simp
    have h2 : 2 * (L : ℝ) * D * ((k : ℝ) + 2) / ((k : ℝ) + 3) ^ 2 ≤
        2 * (L : ℝ) * D / ((k : ℝ) + 4) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hM]
    linarith

/-- The closed simplex, read in Euclidean space, has squared diameter at most `2`. -/
private lemma norm_sub_sq_le_two {ι : Type*} [Fintype ι] {a b : EuclideanSpace ℝ ι}
    (ha : WithLp.ofLp a ∈ closedSimplex ι) (hb : WithLp.ofLp b ∈ closedSimplex ι) :
    ‖a - b‖ ^ 2 ≤ 2 := by
  obtain ⟨ha0, ha1⟩ := mem_closedSimplex.mp ha
  obtain ⟨hb0, hb1⟩ := mem_closedSimplex.mp hb
  have hale : ∀ i, WithLp.ofLp a i ≤ 1 := fun i => by
    rw [← ha1]; exact Finset.single_le_sum (fun j _ => ha0 j) (Finset.mem_univ i)
  have hble : ∀ i, WithLp.ofLp b i ≤ 1 := fun i => by
    rw [← hb1]; exact Finset.single_le_sum (fun j _ => hb0 j) (Finset.mem_univ i)
  have hn : ‖a - b‖ ^ 2 = ∑ i, (WithLp.ofLp a i - WithLp.ofLp b i) ^ 2 := by
    first
      | (rw [EuclideanSpace.norm_sq_eq]; simp [Real.norm_eq_abs, sq_abs])
      | (rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)];
         simp [Real.norm_eq_abs, sq_abs])
  rw [hn]
  calc ∑ i, (WithLp.ofLp a i - WithLp.ofLp b i) ^ 2
      ≤ ∑ i, (WithLp.ofLp a i + WithLp.ofLp b i) :=
        Finset.sum_le_sum fun i _ => by
          nlinarith [mul_nonneg (ha0 i) (hb0 i), mul_nonneg (ha0 i) (sub_nonneg.2 (hale i)),
            mul_nonneg (hb0 i) (sub_nonneg.2 (hble i))]
    _ = 2 := by rw [Finset.sum_add_distrib, ha1, hb1]; norm_num

/-- **Frank–Wolfe on the simplex.** For `f` convex on the closed simplex with `L`-Lipschitz
gradient, linear-minimisation points `s k` and step `2 / (k + 2)`, every `k > 0` and every point
`z` of the simplex satisfy `f (x k) - f z ≤ 4 L / (k + 2)`. -/
theorem sub_le_of_frankWolfe {ι : Type*} [Fintype ι] {f : EuclideanSpace ℝ ι → ℝ}
    {f' : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {L : ℝ≥0}
    (hconv : ConvexOn ℝ {y : EuclideanSpace ℝ ι | WithLp.ofLp y ∈ closedSimplex ι} f)
    (hf : ∀ y, HasGradientAt f (f' y) y) (hL : LipschitzWith L f')
    {x s : ℕ → EuclideanSpace ℝ ι} (hx0 : WithLp.ofLp (x 0) ∈ closedSimplex ι)
    (hs : ∀ k, WithLp.ofLp (s k) ∈ closedSimplex ι)
    (hmin : ∀ k, ∀ y : EuclideanSpace ℝ ι, WithLp.ofLp y ∈ closedSimplex ι →
      ⟪f' (x k), s k⟫ ≤ ⟪f' (x k), y⟫)
    (hx : ∀ k : ℕ, x (k + 1) = x k + (2 / ((k : ℝ) + 2)) • (s k - x k))
    {z : EuclideanSpace ℝ ι} (hz : WithLp.ofLp z ∈ closedSimplex ι) {k : ℕ} (hk : 0 < k) :
    f (x k) - f z ≤ 4 * L / (k + 2) := by
  have hK : Convex ℝ {y : EuclideanSpace ℝ ι | WithLp.ofLp y ∈ closedSimplex ι} := by
    intro a ha b hb t u ht hu htu
    have := convex_closedSimplex ha hb ht hu htu
    first
      | exact this
      | simpa using this
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := fw_general (D := 2) hK hconv hf hL (fun a ha b hb => norm_sub_sq_le_two ha hb)
    hx0 hs hmin hx hz j
  rw [show (((j + 1 : ℕ) : ℝ) + 2) = (j : ℝ) + 3 by push_cast; ring]
  have : 2 * (L : ℝ) * 2 / ((j : ℝ) + 3) = 4 * L / ((j : ℝ) + 3) := by ring
  linarith
