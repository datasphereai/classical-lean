/-- The hypotheses of `tendsto_powerIterate` hold together: on the Euclidean plane
`EuclideanSpace ℝ (Fin 2)`, `T` is the symmetric map of the diagonal matrix `!![2, 0; 0, 1]`, whose
eigenvalues in Mathlib's order are `2` and `1` (`i₀ = 0` and `i₁ = 1`, so `|λ₁| < |λ₀|` and the
rate is `1 / 2`), and the start `x = (1, 1)` has a nonzero component along each eigenvector, so the
iterates do not start on the top eigenvector. -/
example := ClassicalLean.Analysis.PowerMethod.tendsto_powerIterate
    (E := EuclideanSpace ℝ (Fin 2))
    (T := Matrix.toEuclideanLin !![(2 : ℝ), 0; 0, 1])
    (hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr (by
      ext i j; fin_cases i <;> fin_cases j <;> simp))
    (hn := finrank_euclideanSpace_fin) (i₀ := 0) (i₁ := 1)
    (hgap := by
      have hsym : (Matrix.toEuclideanLin !![(2 : ℝ), 0; 0, 1]).IsSymmetric :=
        Matrix.isSymmetric_toEuclideanLin_iff.mpr (by
          ext i j; fin_cases i <;> fin_cases j <;> simp)
      have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := finrank_euclideanSpace_fin
      change |hsym.eigenvalues hn 1| < |hsym.eigenvalues hn 0|
      -- every eigenvalue is 2 or 1: the eigenvector equation, coordinate by coordinate
      have hval : ∀ i, hsym.eigenvalues hn i = 2 ∨ hsym.eigenvalues hn i = 1 := by
        intro i
        have h := hsym.apply_eigenvectorBasis hn i
        have hv0 := (hsym.eigenvectorBasis hn).orthonormal.ne_zero i
        generalize hsym.eigenvectorBasis hn i = v at h hv0
        generalize hsym.eigenvalues hn i = c at h ⊢
        have e0 := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) h
        have e1 := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 1) h
        simp only [Fin.isValue, Matrix.toEuclideanLin, Matrix.ofLp_toLpLin, Matrix.toLin'_apply,
            Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
            Matrix.cons_val_zero, Fin.sum_univ_two, Matrix.cons_val_one, zero_mul, add_zero,
            Real.ringHom_apply, PiLp.smul_apply, smul_eq_mul, mul_eq_mul_right_iff, one_mul,
            zero_add] at e0 e1
        by_contra hc
        obtain ⟨hc2, hc1⟩ := not_or.mp hc
        apply hv0
        ext j
        fin_cases j
        · simpa using e0.resolve_left (Ne.symm hc2)
        · have h1 : (1 - c) * v 1 = 0 := by
            linear_combination e1
          simpa [sub_ne_zero.mpr (Ne.symm hc1)] using h1
      -- the two eigenvalues add up to the trace, 3, and the first is the larger
      have htr := hsym.re_trace_eq_sum_eigenvalues hn
      rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis] at htr
      simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
          OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
          OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
          Matrix.ofLp_toLpLin,
          PiLp.ofLp_single, Matrix.toLin'_apply, Matrix.mulVec_single, MulOpposite.op_one,
          Pi.smul_apply, Matrix.col_apply, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_fin_one,
          one_smul, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
          RCLike.re_to_real] at htr
      have hanti := hsym.eigenvalues_antitone hn (show (0 : Fin 2) ≤ 1 by decide)
      rcases hval 0 with h0 | h0 <;> rcases hval 1 with h1 | h1
      · rw [h0, h1] at htr; norm_num at htr
      · rw [h0, h1]; norm_num
      · rw [h0, h1] at hanti; norm_num at hanti
      · rw [h0, h1] at htr; norm_num at htr)
    (hdom := by
      intro i hi
      fin_cases i
      · exact absurd rfl hi
      · exact le_rfl)
    (x := EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1)
    (hx := by
      have hsym : (Matrix.toEuclideanLin !![(2 : ℝ), 0; 0, 1]).IsSymmetric :=
        Matrix.isSymmetric_toEuclideanLin_iff.mpr (by
          ext i j; fin_cases i <;> fin_cases j <;> simp)
      have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := finrank_euclideanSpace_fin
      change inner ℝ (hsym.eigenvectorBasis hn 0)
        (EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1) ≠ 0
      intro hzero
      have h := hsym.apply_eigenvectorBasis hn 0
      have hv0 := (hsym.eigenvectorBasis hn).orthonormal.ne_zero 0
      generalize hsym.eigenvectorBasis hn 0 = v at h hv0 hzero
      generalize hsym.eigenvalues hn 0 = c at h
      have e0 := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) h
      have e1 := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 1) h
      simp only [Fin.isValue, Matrix.toEuclideanLin, Matrix.ofLp_toLpLin, Matrix.toLin'_apply,
          Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
          Matrix.cons_val_zero, Fin.sum_univ_two, Matrix.cons_val_one, zero_mul, add_zero,
          Real.ringHom_apply, PiLp.smul_apply, smul_eq_mul, mul_eq_mul_right_iff, one_mul,
          zero_add] at e0 e1
      simp [inner_add_right, EuclideanSpace.inner_single_right] at hzero
      apply hv0
      rcases e0 with hc | hz0
      · have hz1 : v 1 = 0 := by
          rw [← hc] at e1; linarith
        ext j; fin_cases j
        · simp; linarith
        · simpa using hz1
      · ext j; fin_cases j
        · simpa using hz0
        · simp; linarith)
