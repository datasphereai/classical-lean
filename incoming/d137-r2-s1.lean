import Mathlib.Probability.Martingale.Convergence

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

/-- Number of red balls after `n` draws, starting with `r` red balls; `X i ∈ {0,1}`
indicates that the `(i+1)`-st draw is red. -/
noncomputable def urnRed {Ω : Type*} (r : ℕ) (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => r
  | n + 1, ω => urnRed r X n ω + X n ω

/-- Share of red balls after `n` draws; the urn then contains `r + b + n` balls. -/
noncomputable def urnShare {Ω : Type*} (r b : ℕ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  urnRed r X n ω / ((r + b + n : ℕ) : ℝ)

private lemma urnRed_zero {Ω : Type*} (r : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    urnRed r X 0 ω = r := rfl

private lemma urnRed_succ {Ω : Type*} (r : ℕ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    urnRed r X (n + 1) ω = urnRed r X n ω + X n ω := rfl

private lemma urnRed_bounds {Ω : Type*} (r : ℕ) (X : ℕ → Ω → ℝ)
    (hX01 : ∀ n ω, X n ω = 0 ∨ X n ω = 1) :
    ∀ n ω, 0 ≤ urnRed r X n ω ∧ urnRed r X n ω ≤ (r : ℝ) + n := by
  intro n ω
  induction n with
  | zero =>
    rw [urnRed_zero]
    exact ⟨Nat.cast_nonneg r, by simp⟩
  | succ n ih =>
    rw [urnRed_succ]
    push_cast
    obtain ⟨i1, i2⟩ := ih
    rcases hX01 n ω with h | h <;> rw [h] <;> constructor <;> linarith

private lemma urnShare_norm_le {Ω : Type*} (r b : ℕ) (hrb : 0 < r + b) (X : ℕ → Ω → ℝ)
    (hX01 : ∀ n ω, X n ω = 0 ∨ X n ω = 1) (n : ℕ) (ω : Ω) :
    ‖urnShare r b X n ω‖ ≤ 1 := by
  obtain ⟨h0, h1⟩ := urnRed_bounds r X hX01 n ω
  have hN : (0 : ℝ) < ((r + b + n : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < r + b + n by omega)
  have hle : urnRed r X n ω ≤ ((r + b + n : ℕ) : ℝ) := by
    push_cast
    have : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
    linarith
  have a0 : 0 ≤ urnShare r b X n ω := div_nonneg h0 hN.le
  have a1 : urnShare r b X n ω ≤ 1 := (div_le_one hN).mpr hle
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

private lemma urnRed_stronglyMeasurable {Ω : Type*} {m0 : MeasurableSpace Ω}
    (ℱ : Filtration ℕ m0) (r : ℕ) (X : ℕ → Ω → ℝ)
    (hX : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n)) :
    ∀ n, StronglyMeasurable[ℱ n] (urnRed r X n) := by
  intro n
  induction n with
  | zero =>
    have h : urnRed r X 0 = fun _ => (r : ℝ) := by
      funext ω; rfl
    rw [h]
    exact stronglyMeasurable_const
  | succ n ih =>
    have h : urnRed r X (n + 1) = urnRed r X n + X n := by
      funext ω; rfl
    rw [h]
    exact (ih.mono (ℱ.mono (Nat.le_succ n))).add (hX n)

private lemma urnRed_integrable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (r : ℕ) (X : ℕ → Ω → ℝ)
    (hX01 : ∀ n ω, X n ω = 0 ∨ X n ω = 1)
    (hX : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n)) (n : ℕ) :
    Integrable (urnRed r X n) μ := by
  refine Integrable.mono' (integrable_const ((r : ℝ) + n))
    (((urnRed_stronglyMeasurable ℱ r X hX n).mono (ℱ.le n)).aestronglyMeasurable)
    (ae_of_all μ fun ω => ?_)
  show ‖urnRed r X n ω‖ ≤ (r : ℝ) + n
  rw [Real.norm_eq_abs, abs_le]
  obtain ⟨h0, h1⟩ := urnRed_bounds r X hX01 n ω
  have : (0 : ℝ) ≤ (r : ℝ) + n := by positivity
  constructor <;> linarith

private lemma share_key (R N : ℝ) (hN : 0 < N) :
    1 / (N + 1) * R + 1 / (N + 1) * (R / N) = R / N := by
  have h1 : N + 1 ≠ 0 := (by linarith : (0 : ℝ) < N + 1).ne'
  have h2 : N ≠ 0 := hN.ne'
  have hi : N * N⁻¹ = 1 := mul_inv_cancel₀ h2
  have hj : (N + 1) * (N + 1)⁻¹ = 1 := mul_inv_cancel₀ h1
  linear_combination (R * N⁻¹) * hj - ((N + 1)⁻¹ * R) * hi

/-- Pólya's urn: the share of red balls is a martingale. -/
theorem martingale_urnShare {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (r b : ℕ) (hrb : 0 < r + b)
    (X : ℕ → Ω → ℝ) (hX01 : ∀ n ω, X n ω = 0 ∨ X n ω = 1)
    (hX_meas : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hX_cond : ∀ n, μ[X n | ℱ n] =ᵐ[μ] urnShare r b X n) :
    Martingale (urnShare r b X) ℱ μ := by
  have hRmeas := urnRed_stronglyMeasurable ℱ r X hX_meas
  have hRint : ∀ n, Integrable (urnRed r X n) μ :=
    fun n => urnRed_integrable ℱ r X hX01 hX_meas n
  have hXint : ∀ n, Integrable (X n) μ := fun n =>
    Integrable.mono' (integrable_const (1 : ℝ))
      (((hX_meas n).mono (ℱ.le (n + 1))).aestronglyMeasurable)
      (ae_of_all μ fun ω => by
        show ‖X n ω‖ ≤ 1
        rcases hX01 n ω with h | h <;> simp [h])
  have hSmeas : ∀ n, StronglyMeasurable[ℱ n] (urnShare r b X n) := by
    intro n
    have heq : urnShare r b X n
        = fun ω => urnRed r X n ω * (((r + b + n : ℕ) : ℝ))⁻¹ := by
      funext ω; exact div_eq_mul_inv _ _
    rw [heq]
    exact (hRmeas n).mul_const _
  have hSint : ∀ n, Integrable (urnShare r b X n) μ := fun n =>
    Integrable.mono' (integrable_const (1 : ℝ))
      (((hSmeas n).mono (ℱ.le n)).aestronglyMeasurable)
      (ae_of_all μ fun ω => urnShare_norm_le r b hrb X hX01 n ω)
  refine martingale_nat (fun n => hSmeas n) hSint (fun n => ?_)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / ((r + b + (n + 1) : ℕ) : ℝ) := ⟨_, rfl⟩
  have hsplit : urnShare r b X (n + 1) = c • urnRed r X n + c • X n := by
    funext ω
    simp only [urnShare, urnRed_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc]
    ring
  have h1 : μ[urnShare r b X (n + 1) | ℱ n]
      =ᵐ[μ] μ[c • urnRed r X n | ℱ n] + μ[c • X n | ℱ n] := by
    rw [hsplit]
    exact condExp_add (m := ℱ n) ((hRint n).smul c) ((hXint n).smul c)
  have h2 : μ[c • urnRed r X n | ℱ n] = c • urnRed r X n :=
    condExp_of_stronglyMeasurable (ℱ.le n) ((hRmeas n).const_smul c) ((hRint n).smul c)
  have h3 : μ[c • X n | ℱ n] =ᵐ[μ] c • μ[X n | ℱ n] :=
    condExp_smul (m := ℱ n) c (X n)
  have hN : (0 : ℝ) < ((r + b + n : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < r + b + n by omega)
  have hcast : ((r + b + (n + 1) : ℕ) : ℝ) = ((r + b + n : ℕ) : ℝ) + 1 := by
    push_cast; ring
  filter_upwards [h1, h3, hX_cond n] with ω e1 e3 e4
  rw [e1, Pi.add_apply, h2, e3]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [e4, hc, hcast]
  simp only [urnShare]
  exact (share_key _ _ hN).symm

/-- Pólya's urn: the share of red balls converges almost surely. -/
theorem ae_tendsto_urnShare {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (r b : ℕ) (hrb : 0 < r + b)
    (X : ℕ → Ω → ℝ) (hX01 : ∀ n ω, X n ω = 0 ∨ X n ω = 1)
    (hX_meas : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hX_cond : ∀ n, μ[X n | ℱ n] =ᵐ[μ] urnShare r b X n) :
    ∃ L : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n => urnShare r b X n ω) atTop (𝓝 (L ω)) := by
  have hmart := martingale_urnShare ℱ r b hrb X hX01 hX_meas hX_cond
  have hbdd : ∀ n, eLpNorm (urnShare r b X n) 1 μ ≤ ((1 : ℝ≥0) : ℝ≥0∞) := by
    intro n
    have hae : AEStronglyMeasurable (urnShare r b X n) μ :=
      (hmart.integrable n).aestronglyMeasurable
    have hb : ∀ᵐ ω ∂μ, ‖urnShare r b X n ω‖ ≤ (1 : ℝ) :=
      ae_of_all μ fun ω => urnShare_norm_le r b hrb X hX01 n ω
    first
      | exact (eLpNorm_le_of_ae_bound hae hb).trans (by simp)
      | exact (eLpNorm_le_of_ae_bound hb).trans (by simp)
  exact ⟨ℱ.limitProcess (urnShare r b X) μ,
    hmart.submartingale.ae_tendsto_limitProcess hbdd⟩
