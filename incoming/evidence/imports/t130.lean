import ClassicalLean.InformationTheory.MutualInformation
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Capacity of the binary symmetric channel

With crossover probability `ε`, the input `a` is received as `b` with probability `1 - ε` when
`b = a` and `ε` otherwise. For every input law the mutual information is at most `log 2 - h(ε)`,
and the uniform input attains it.
-/

open ClassicalLean.Simplex

/-- The joint law of input and output of the binary symmetric channel. -/
private noncomputable def bscJoint (ε : ℝ) (p : Fin 2 → ℝ) : Fin 2 × Fin 2 → ℝ :=
  fun ab => p ab.1 * (if ab.1 = ab.2 then 1 - ε else ε)

private theorem bscJoint_values (ε : ℝ) (p : Fin 2 → ℝ) :
    bscJoint ε p (0, 0) = p 0 * (1 - ε) ∧ bscJoint ε p (0, 1) = p 0 * ε ∧
      bscJoint ε p (1, 0) = p 1 * ε ∧ bscJoint ε p (1, 1) = p 1 * (1 - ε) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · change p 0 * (if (0 : Fin 2) = 0 then 1 - ε else ε) = _
    rw [ite_eq_left rfl]
  · change p 0 * (if (0 : Fin 2) = 1 then 1 - ε else ε) = _
    rw [ite_eq_right h01]
  · change p 1 * (if (1 : Fin 2) = 0 then 1 - ε else ε) = _
    rw [ite_eq_right h01.symm]
  · change p 1 * (if (1 : Fin 2) = 1 then 1 - ε else ε) = _
    rw [ite_eq_left rfl]

private theorem bscJoint_nonneg {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {p : Fin 2 → ℝ}
    (hp0 : ∀ a, 0 ≤ p a) : ∀ ab, 0 ≤ bscJoint ε p ab := by
  intro ab
  change 0 ≤ p ab.1 * (if ab.1 = ab.2 then 1 - ε else ε)
  exact mul_nonneg (hp0 _) (by split_ifs <;> linarith)

/-- `x y log (x y) = y (x log x) + x (y log y)` for all real `x`, `y`. -/
private theorem mul_mul_log_mul (x y : ℝ) :
    x * y * Real.log (x * y) = y * (x * Real.log x) + x * (y * Real.log y) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rw [Real.log_mul hx hy]
  ring

/-- The mutual information of the binary symmetric channel is the output entropy minus `h(ε)`. -/
private theorem mutualInfo_bscJoint {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {p : Fin 2 → ℝ}
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    mutualInfo (bscJoint ε p)
      = shannonEntropy (fun b => ∑ a, bscJoint ε p (a, b)) - Real.binEntropy ε := by
  obtain ⟨e00, e01, e10, e11⟩ := bscJoint_values ε p
  have hP0 := bscJoint_nonneg hε0 hε1 hp0
  have h1 : p 1 = 1 - p 0 := by
    have h := hp1
    rw [Fin.sum_univ_two] at h
    linarith
  have hrow' : ∀ a, ∑ b, bscJoint ε p (a, b) = p a := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · rw [Fin.sum_univ_two, e00, e01]; ring
    · rw [Fin.sum_univ_two, e10, e11]; ring
  have hrow : (fun a => ∑ b, bscJoint ε p (a, b)) = p := funext hrow'
  have hp' : shannonEntropy p = -(p 0 * Real.log (p 0) + p 1 * Real.log (p 1)) := by
    simp only [shannonEntropy, Fin.sum_univ_two]
  have hPH : shannonEntropy (bscJoint ε p) =
      -(bscJoint ε p (0, 0) * Real.log (bscJoint ε p (0, 0))
        + bscJoint ε p (0, 1) * Real.log (bscJoint ε p (0, 1))
        + (bscJoint ε p (1, 0) * Real.log (bscJoint ε p (1, 0))
          + bscJoint ε p (1, 1) * Real.log (bscJoint ε p (1, 1)))) := by
    simp only [shannonEntropy, Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [e00, e01, e10, e11, mul_mul_log_mul, mul_mul_log_mul, mul_mul_log_mul,
    mul_mul_log_mul] at hPH
  have hb : Real.binEntropy ε = -(ε * Real.log ε) - (1 - ε) * Real.log (1 - ε) := by
    rw [Real.binEntropy, Real.log_inv, Real.log_inv]
    ring
  rw [mutualInfo_eq_shannonEntropy_add_shannonEntropy_sub_shannonEntropy hP0, hrow, hPH, hp',
    hb, h1]
  ring

/-- At the uniform input the output law is uniform. -/
private theorem bscJoint_output_half {ε : ℝ} {p : Fin 2 → ℝ} (hp : ∀ a, p a = 1 / 2) :
    (fun b => ∑ a, bscJoint ε p (a, b)) = fun _ => (2 : ℝ)⁻¹ := by
  obtain ⟨e00, e01, e10, e11⟩ := bscJoint_values ε p
  have hv : ∀ b, ∑ a, bscJoint ε p (a, b) = (2 : ℝ)⁻¹ := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · rw [Fin.sum_univ_two, e00, e10, hp 0, hp 1]; ring
    · rw [Fin.sum_univ_two, e01, e11, hp 0, hp 1]; ring
  exact funext hv

/-- **The capacity bound for the binary symmetric channel**: for every input law `p`, the mutual
information of input and output is at most `log 2 - h(ε)`. -/
theorem mutualInfo_bsc_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {p : Fin 2 → ℝ}
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    mutualInfo (fun ab : Fin 2 × Fin 2 => p ab.1 * (if ab.1 = ab.2 then 1 - ε else ε))
      ≤ Real.log 2 - Real.binEntropy ε := by
  change mutualInfo (bscJoint ε p) ≤ Real.log 2 - Real.binEntropy ε
  obtain ⟨e00, e01, e10, e11⟩ := bscJoint_values ε p
  have hP0 := bscJoint_nonneg hε0 hε1 hp0
  have hY0 : ∀ b, 0 ≤ ∑ a, bscJoint ε p (a, b) :=
    fun b => Finset.sum_nonneg fun a _ => hP0 (a, b)
  have hY1 : ∑ b, ∑ a, bscJoint ε p (a, b) = 1 := by
    have h := hp1
    rw [Fin.sum_univ_two] at h
    simp only [Fin.sum_univ_two]
    rw [e00, e01, e10, e11]
    linear_combination h
  have hY := shannonEntropy_le_log_card (p := fun b => ∑ a, bscJoint ε p (a, b)) hY0 hY1
  simp only [Fintype.card_fin, Nat.cast_ofNat] at hY
  rw [mutualInfo_bscJoint hε0 hε1 hp0 hp1]
  linarith

/-- **The uniform input attains the capacity** `log 2 - h(ε)` of the binary symmetric channel. -/
theorem mutualInfo_bsc_half {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    mutualInfo (fun ab : Fin 2 × Fin 2 => (1 / 2 : ℝ) * (if ab.1 = ab.2 then 1 - ε else ε))
      = Real.log 2 - Real.binEntropy ε := by
  change mutualInfo (bscJoint ε (fun _ => (1 / 2 : ℝ))) = Real.log 2 - Real.binEntropy ε
  rw [mutualInfo_bscJoint (p := fun _ => (1 / 2 : ℝ)) hε0 hε1 (fun _ => by norm_num)
      (by norm_num [Fin.sum_univ_two]),
    bscJoint_output_half (p := fun _ => (1 / 2 : ℝ)) (fun _ => rfl)]
  simp only [shannonEntropy, Fin.sum_univ_two, Real.log_inv]
  ring
