import Mathlib

open Filter Topology

private lemma pow_apply_eigen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →ₗ[ℝ] E) (v : E) (c : ℝ) (h : T v = c • v) (k : ℕ) :
    (T ^ k) v = c ^ k • v := by
  induction k with
  | zero => rw [pow_zero, pow_zero, one_smul]; rfl
  | succ k ih =>
    rw [pow_succ']
    show T ((T ^ k) v) = _
    rw [ih, map_smul, h, smul_smul, ← pow_succ]

private lemma inner_pow_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (u : E) (c : ℝ) (h : T u = c • u) (y : E)
    (k : ℕ) : inner ℝ u ((T ^ k) y) = c ^ k * inner ℝ u y := by
  induction k with
  | zero => rw [pow_zero, pow_zero, one_mul]; rfl
  | succ k ih =>
    rw [pow_succ']
    show inner ℝ u (T ((T ^ k) y)) = _
    rw [← hT u, h, real_inner_smul_left, ih]
    ring

private lemma norm_pow_apply_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →ₗ[ℝ] E) {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (ev : Fin n → ℝ)
    (hb : ∀ i, T (b i) = ev i • b i) (i₀ : Fin n) (μ : ℝ)
    (hdom : ∀ i, i ≠ i₀ → |ev i| ≤ μ) (w : E) (hw : inner ℝ (b i₀) w = 0) (k : ℕ) :
    ‖(T ^ k) w‖ ≤ (∑ i, |inner ℝ (b i) w|) * μ ^ k := by
  have hrepr : w = ∑ i, inner ℝ (b i) w • b i := by
    conv_lhs => rw [← b.sum_repr w]
    simp only [OrthonormalBasis.repr_apply_apply]
  have hTw : (T ^ k) w = ∑ i, (inner ℝ (b i) w * ev i ^ k) • b i := by
    conv_lhs => rw [hrepr]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, pow_apply_eigen T (b i) (ev i) (hb i) k, smul_smul]
  rw [hTw]
  calc ‖∑ i, (inner ℝ (b i) w * ev i ^ k) • b i‖
      ≤ ∑ i, ‖(inner ℝ (b i) w * ev i ^ k) • b i‖ := norm_sum_le _ _
    _ ≤ ∑ i, |inner ℝ (b i) w| * μ ^ k := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul, b.orthonormal.1 i, mul_one, Real.norm_eq_abs, abs_mul, abs_pow]
        by_cases hi : i = i₀
        · rw [hi, hw]; simp
        · exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (abs_nonneg _) (hdom i hi) k) (abs_nonneg _)
    _ = (∑ i, |inner ℝ (b i) w|) * μ ^ k := by rw [Finset.sum_mul]

private lemma power_aux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (ev : Fin n → ℝ) (hb : ∀ i, T (b i) = ev i • b i) (i₀ : Fin n) (μ : ℝ)
    (hμ0 : 0 ≤ μ) (hgap : μ < |ev i₀|) (hdom : ∀ i, i ≠ i₀ → |ev i| ≤ μ)
    (x : E) (hx : inner ℝ (b i₀) x ≠ 0) :
    (∃ C : ℝ, ∀ k : ℕ,
      ‖(inner ℝ (b i₀) ((T ^ k) x))⁻¹ • (T ^ k) x - b i₀‖ ≤ C * (μ / |ev i₀|) ^ k) ∧
    Tendsto (fun k : ℕ => (inner ℝ (b i₀) ((T ^ k) x))⁻¹ • (T ^ k) x) atTop
      (𝓝 (b i₀)) := by
  obtain ⟨c, hc⟩ : ∃ c, c = inner ℝ (b i₀) x := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = x - c • b i₀ := ⟨_, rfl⟩
  have hu1 : inner ℝ (b i₀) (b i₀) = 1 := by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i₀]; norm_num
  have hw0 : inner ℝ (b i₀) w = 0 := by
    rw [hw, inner_sub_right, real_inner_smul_right, hu1, mul_one, ← hc, sub_self]
  have hx_dec : x = c • b i₀ + w := by rw [hw]; abel
  have hevpos : 0 < |ev i₀| := lt_of_le_of_lt hμ0 hgap
  have hev0 : ev i₀ ≠ 0 := by
    intro h; rw [h, abs_zero] at hevpos; exact lt_irrefl _ hevpos
  have hc0 : c ≠ 0 := by rw [hc]; exact hx
  have hinner : ∀ k : ℕ, inner ℝ (b i₀) ((T ^ k) x) = ev i₀ ^ k * c := fun k => by
    rw [inner_pow_apply hT (b i₀) (ev i₀) (hb i₀) x k, ← hc]
  have hd : ∀ k : ℕ, (inner ℝ (b i₀) ((T ^ k) x))⁻¹ • (T ^ k) x - b i₀
      = (ev i₀ ^ k * c)⁻¹ • (T ^ k) w := by
    intro k
    rw [hinner k]
    conv_lhs => rw [hx_dec]
    rw [map_add, map_smul, pow_apply_eigen T _ _ (hb i₀), smul_add, smul_smul, smul_smul]
    have hpk : ev i₀ ^ k ≠ 0 := pow_ne_zero _ hev0
    have h1 : (ev i₀ ^ k * c)⁻¹ * c * ev i₀ ^ k = 1 := by field_simp
    rw [h1, one_smul]
    abel
  set C : ℝ := (∑ i, |inner ℝ (b i) w|) / |c| with hC
  have habs_ev : |ev i₀| ≠ 0 := abs_ne_zero.mpr hev0
  have habs_c : |c| ≠ 0 := abs_ne_zero.mpr hc0
  have hbound : ∀ k : ℕ,
      ‖(inner ℝ (b i₀) ((T ^ k) x))⁻¹ • (T ^ k) x - b i₀‖ ≤ C * (μ / |ev i₀|) ^ k := by
    intro k
    rw [hd k, norm_smul, Real.norm_eq_abs, abs_inv, abs_mul, abs_pow]
    calc (|ev i₀| ^ k * |c|)⁻¹ * ‖(T ^ k) w‖
        ≤ (|ev i₀| ^ k * |c|)⁻¹ * ((∑ i, |inner ℝ (b i) w|) * μ ^ k) :=
          mul_le_mul_of_nonneg_left
            (norm_pow_apply_le T b ev hb i₀ μ hdom w hw0 k) (by positivity)
      _ = C * (μ / |ev i₀|) ^ k := by
          rw [hC, div_pow]
          field_simp
          try ring
  refine ⟨⟨C, hbound⟩, ?_⟩
  have hr0 : 0 ≤ μ / |ev i₀| := div_nonneg hμ0 (abs_nonneg _)
  have hr1 : μ / |ev i₀| < 1 := (div_lt_one hevpos).mpr hgap
  have ht : Tendsto (fun k : ℕ => C * (μ / |ev i₀|) ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul C
  have h0 := squeeze_zero_norm
    (f := fun k : ℕ => (inner ℝ (b i₀) ((T ^ k) x))⁻¹ • (T ^ k) x - b i₀) hbound ht
  exact tendsto_sub_nhds_zero_iff.mp h0

/-- Power method: if the eigenvalue `λ₀ = eigenvalues i₀` strictly dominates in absolute
value an eigenvalue `λ₁ = eigenvalues i₁` which bounds all the others, and the start vector
has a nonzero component along the top eigenvector `u`, then the iterates `Tᵏ x`, rescaled to
unit `u`-component, approach `u` at rate `(|λ₁|/|λ₀|)^k`. -/
theorem tendsto_powerIterate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (i₀ i₁ : Fin n)
    (hgap : |hT.eigenvalues hn i₁| < |hT.eigenvalues hn i₀|)
    (hdom : ∀ i, i ≠ i₀ → |hT.eigenvalues hn i| ≤ |hT.eigenvalues hn i₁|)
    (x : E) (hx : inner ℝ (hT.eigenvectorBasis hn i₀) x ≠ 0) :
    (∃ C : ℝ, ∀ k : ℕ,
      ‖(inner ℝ (hT.eigenvectorBasis hn i₀) ((T ^ k) x))⁻¹ • (T ^ k) x
          - hT.eigenvectorBasis hn i₀‖
        ≤ C * (|hT.eigenvalues hn i₁| / |hT.eigenvalues hn i₀|) ^ k) ∧
    Tendsto (fun k : ℕ =>
        (inner ℝ (hT.eigenvectorBasis hn i₀) ((T ^ k) x))⁻¹ • (T ^ k) x) atTop
      (𝓝 (hT.eigenvectorBasis hn i₀)) := by
  have hb : ∀ i, T (hT.eigenvectorBasis hn i)
      = hT.eigenvalues hn i • hT.eigenvectorBasis hn i := fun i => by
    first
      | simpa using hT.apply_eigenvectorBasis hn i
      | (rw [hT.apply_eigenvectorBasis hn i]; rfl)
  exact power_aux hT (hT.eigenvectorBasis hn) (hT.eigenvalues hn) hb i₀
    |hT.eigenvalues hn i₁| (abs_nonneg _) hgap hdom x hx
