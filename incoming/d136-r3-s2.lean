import ClassicalLean.Analysis.LinearProgram

/-!
# State prices in a one-period market

A payoff matrix `D` (rows are states, columns are assets) and a price vector `π` are given.
A portfolio `θ` costs `π ⬝ᵥ θ` and pays `D *ᵥ θ` across the states. No portfolio costs at most
`0`, pays at least `0` in every state, and either costs less than `0` or pays more than `0` in
some state, exactly when there are strictly positive state prices `ψ` with `Dᵀ ψ = π`.

The proof applies Farkas' lemma to the system `Dᵀ u − s π = π − Dᵀ 1` in `u ≥ 0`, `s ≥ 0`.
-/

open Matrix Finset ClassicalLean.LinearProgram

namespace ClassicalLean.StatePrices

/-- The map `(u, s) ↦ (Dᵀ u − s π, −(Dᵀ u − s π))`. -/
private def sysMap {m n : Type*} [Fintype m] (D : Matrix m n ℝ) (π : n → ℝ) :
    ((m ⊕ Unit) → ℝ) →ₗ[ℝ] ((n ⊕ n) → ℝ) where
  toFun x := Sum.elim (Dᵀ *ᵥ (fun i ↦ x (Sum.inl i)) - x (Sum.inr ()) • π)
    (-(Dᵀ *ᵥ (fun i ↦ x (Sum.inl i)) - x (Sum.inr ()) • π))
  map_add' x y := by
    have h1 : (fun i ↦ (x + y) (Sum.inl i)) = (fun i ↦ x (Sum.inl i)) + fun i ↦ y (Sum.inl i) :=
      rfl
    rw [h1]
    ext (j | j) <;> simp [mulVec_add, add_smul] <;> ring
  map_smul' r x := by
    have h1 : (fun i ↦ (r • x) (Sum.inl i)) = r • fun i ↦ x (Sum.inl i) := rfl
    rw [h1]
    ext (j | j) <;> simp [mulVec_smul] <;> ring

private theorem sysMap_apply {m n : Type*} [Fintype m] (D : Matrix m n ℝ) (π : n → ℝ)
    (z : (m ⊕ Unit) → ℝ) :
    sysMap D π z = Sum.elim (Dᵀ *ᵥ (fun i ↦ z (Sum.inl i)) - z (Sum.inr ()) • π)
      (-(Dᵀ *ᵥ (fun i ↦ z (Sum.inl i)) - z (Sum.inr ()) • π)) := rfl

end ClassicalLean.StatePrices

open ClassicalLean.StatePrices

/-- **State prices.** No portfolio costs at most nothing, never pays less than nothing, and
either costs less than nothing or sometimes pays more, exactly when there are strictly positive
state prices `ψ` with `Dᵀ ψ = π`. -/
theorem exists_pos_statePrices_iff {m n : Type*} [Fintype m] [Fintype n]
    (D : Matrix m n ℝ) (π : n → ℝ) :
    (¬∃ θ : n → ℝ, π ⬝ᵥ θ ≤ 0 ∧ 0 ≤ D *ᵥ θ ∧ (π ⬝ᵥ θ < 0 ∨ ∃ i, 0 < (D *ᵥ θ) i)) ↔
      ∃ ψ : m → ℝ, (∀ i, 0 < ψ i) ∧ Dᵀ *ᵥ ψ = π := by
  classical
  constructor
  · intro hNA
    by_cases hz : ∃ z, 0 ≤ z ∧ sysMap D π z ≤ Sum.elim (π - Dᵀ *ᵥ 1) (-(π - Dᵀ *ᵥ 1))
    · obtain ⟨z, hz0, hzb⟩ := hz
      have hs : (0 : ℝ) ≤ z (Sum.inr ()) := hz0 _
      have hs1 : z (Sum.inr ()) + 1 ≠ 0 := by linarith
      refine ⟨(z (Sum.inr ()) + 1)⁻¹ • ((fun i ↦ z (Sum.inl i)) + 1), fun i ↦ ?_, ?_⟩
      · have hu : (0 : ℝ) ≤ z (Sum.inl i) := hz0 _
        simp only [Pi.smul_apply, Pi.add_apply, Pi.one_apply, smul_eq_mul]
        exact mul_pos (inv_pos.mpr (by linarith)) (by linarith)
      · ext j
        have h1 := hzb (Sum.inl j)
        have h2 := hzb (Sum.inr j)
        rw [sysMap_apply] at h1 h2
        simp only [Sum.elim_inl, Sum.elim_inr, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
          smul_eq_mul] at h1 h2
        rw [mulVec_smul, mulVec_add]
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        rw [inv_mul_eq_iff_eq_mul₀ hs1]
        linarith
    · exfalso
      have hf := (farkas (sysMap D π) (Sum.elim (π - Dᵀ *ᵥ 1) (-(π - Dᵀ *ᵥ 1)))).not.mp hz
      push Not at hf
      obtain ⟨y, hy0, hyL, hyb⟩ := hf
      obtain ⟨θ, hθ⟩ : ∃ θ : n → ℝ, θ = fun j ↦ y (Sum.inl j) - y (Sum.inr j) := ⟨_, rfl⟩
      have hyw : ∀ w : n → ℝ, y ⬝ᵥ Sum.elim w (-w) = θ ⬝ᵥ w := by
        intro w
        rw [hθ]
        simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply,
          sub_mul, Finset.sum_sub_distrib, mul_neg, Finset.sum_neg_distrib]
        ring
      have hyz : ∀ (u : m → ℝ) (s : Unit → ℝ),
          y ⬝ᵥ sysMap D π (Sum.elim u s) = θ ⬝ᵥ (Dᵀ *ᵥ u - s () • π) := by
        intro u s
        rw [sysMap_apply, hyw]
        rfl
      have hDθ : 0 ≤ D *ᵥ θ := nonneg_of_forall_dotProduct_nonneg fun u hu ↦ by
        have h := hyL (Sum.elim u 0) (fun k ↦ by
          cases k with
          | inl i => exact hu i
          | inr _ => simp)
        rw [hyz] at h
        simp only [Pi.zero_apply, zero_smul, sub_zero] at h
        rwa [dotProduct_mulVec, vecMul_transpose] at h
      have hπθ : θ ⬝ᵥ π ≤ 0 := by
        have h := hyL (Sum.elim 0 1) (fun k ↦ by
          cases k with
          | inl i => simp
          | inr _ => simp)
        rw [hyz] at h
        simp only [mulVec_zero, Pi.one_apply, one_smul, zero_sub, dotProduct_neg] at h
        linarith
      rw [hyw, dotProduct_sub, dotProduct_mulVec, vecMul_transpose] at hyb
      refine hNA ⟨θ, by rw [dotProduct_comm]; exact hπθ, hDθ, ?_⟩
      by_cases hpos : ∃ i, 0 < (D *ᵥ θ) i
      · exact Or.inr hpos
      · left
        push Not at hpos
        have h1 : (D *ᵥ θ) ⬝ᵥ 1 ≤ 0 := by
          simp only [dotProduct, Pi.one_apply, mul_one]
          exact Finset.sum_nonpos fun i _ ↦ hpos i
        rw [dotProduct_comm]
        linarith
  · rintro ⟨ψ, hψ, hDψ⟩ ⟨θ, hc, hp, hor⟩
    have key : π ⬝ᵥ θ = ψ ⬝ᵥ D *ᵥ θ := by
      rw [← hDψ, mulVec_transpose, ← dotProduct_mulVec]
    have hnn : 0 ≤ ψ ⬝ᵥ D *ᵥ θ := dotProduct_nonneg_of_nonneg (fun i ↦ (hψ i).le) hp
    rcases hor with h | ⟨i, hi⟩
    · linarith
    · have hpos : 0 < ψ ⬝ᵥ D *ᵥ θ := by
        show 0 < ∑ j, ψ j * (D *ᵥ θ) j
        exact Finset.sum_pos' (fun j _ ↦ mul_nonneg (hψ j).le (hp j))
          ⟨i, Finset.mem_univ _, mul_pos (hψ i) hi⟩
      linarith
