

/-- The hypotheses of `measureReal_sum_ge_le_bernstein` hold together: two independent fair `±1`
coins, the coordinates of the product of two copies of `Ber(1, -1, 1/2)`, with `b = 1`, `v = 2` and
`t = 1`. -/
example := measureReal_sum_ge_le_bernstein (Ω := Fin 2 → ℝ) (ι := Fin 2)
    (μ := Measure.pi fun _ => bernoulliMeasure (1 : ℝ) (-1) ⟨1 / 2, by norm_num, by norm_num⟩)
    (X := fun i ω => ω i) (s := Finset.univ)
    (hind := iIndepFun_pi fun _ => aemeasurable_id)
    (hmeas := fun i => measurable_pi_apply i)
    (hint := fun _ _ => integrable_eval (integrable_bernoulliMeasure _ _ _ _))
    (hint2 := fun i _ => integrable_comp_eval (X := fun _ : Fin 2 => ℝ) (i := i)
      (f := fun x : ℝ => x ^ 2) (integrable_bernoulliMeasure _ _ _ _))
    (hmean := fun _ _ => by
      rw [integral_eval, integral_bernoulliMeasure]
      norm_num)
    (b := 1) (v := 2) (t := 1) (hb0 := by norm_num)
    (hb := fun i _ => by
      have h : ∀ᵐ x ∂bernoulliMeasure (1 : ℝ) (-1) ⟨1 / 2, by norm_num, by norm_num⟩, x ≤ 1 := by
        rw [bernoulliMeasure_def, ae_add_measure_iff]
        exact ⟨Measure.ae_smul_measure ((ae_dirac_iff measurableSet_Iic).2 le_rfl) _,
          Measure.ae_smul_measure ((ae_dirac_iff measurableSet_Iic).2 (by norm_num)) _⟩
      exact (measurePreserving_eval (fun _ : Fin 2 =>
        bernoulliMeasure (1 : ℝ) (-1) ⟨1 / 2, by norm_num, by norm_num⟩)
          i).quasiMeasurePreserving.ae h)
    (hv := by
      have h : ∀ i : Fin 2, ∫ ω, ω i ^ 2 ∂(Measure.pi fun _ =>
          bernoulliMeasure (1 : ℝ) (-1) ⟨1 / 2, by norm_num, by norm_num⟩) = 1 := fun i =>
        (integral_comp_eval (X := fun _ : Fin 2 => ℝ) (i := i) (f := fun x : ℝ => x ^ 2)
          (continuous_pow 2).aestronglyMeasurable).trans
          ((integral_bernoulliMeasure _ _ _ (fun x : ℝ => x ^ 2)).trans (by norm_num))
      rw [Fin.sum_univ_two]
      linarith [h 0, h 1])
    (ht := by norm_num)
