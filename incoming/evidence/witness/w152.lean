/-- The hypotheses of `exists_kkt_of_slater` hold together: on the real line, minimise
`f x = x * x` subject to the two constraints `1 - x ≤ 0` and `x - 2 ≤ 0` (`ι = Fin 2`). The
minimiser is `xbar = 1`, where the first constraint is active and the second is not; the gradients
there are `a = 2` and `b = (-1, 1)`; the point `3 / 2` satisfies both constraints strictly. -/
example := ClassicalLean.Analysis.KKT.exists_kkt_of_slater (E := ℝ) (ι := Fin 2)
    (f := fun x => x * x) (g := ![fun x => 1 - x, fun x => x - 2]) (xbar := 1) (a := 2)
    (b := ![-1, 1])
    ⟨convex_univ, fun x _ y _ s t hs ht hst => by
      obtain rfl : t = 1 - s := by linarith
      simp only [smul_eq_mul]
      nlinarith [mul_nonneg (mul_nonneg hs ht) (sq_nonneg (x - y))]⟩
    (fun i => by
      fin_cases i
      · refine ⟨convex_univ, fun x _ y _ s t _ _ hst => ?_⟩
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, smul_eq_mul]
        linarith
      · refine ⟨convex_univ, fun x _ y _ s t _ _ hst => ?_⟩
        simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          smul_eq_mul]
        linarith)
    (by
      rw [hasGradientAt_iff_hasFDerivAt]
      refine ((hasFDerivAt_id (1 : ℝ)).mul (hasFDerivAt_id (1 : ℝ))).congr_fderiv ?_
      ext
      simp
      norm_num)
    (fun i => by
      fin_cases i
      · simpa using ((hasDerivAt_id (1 : ℝ)).const_sub 1).hasGradientAt'
      · simpa using ((hasDerivAt_id (1 : ℝ)).sub_const 2).hasGradientAt')
    ⟨3 / 2, fun i => by fin_cases i <;> norm_num⟩
    (fun i => by fin_cases i <;> norm_num)
    (isMinOn_iff.mpr fun x hx => by
      have h0 := hx 0
      simp only [Matrix.cons_val_zero] at h0
      nlinarith)
