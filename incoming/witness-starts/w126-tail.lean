

/-- The hypotheses of `measureReal_orderStat_le` hold together: three independent fair coins with
values `1` and `0`, the coordinates of the product of three copies of `Ber(1, 0, 1/2)`, at
`x = 1/2` (so `F = 1/2`) and `k = 2`. -/
example := measureReal_orderStat_le (Ω := Fin 3 → ℝ) (n := 3)
    (μ := Measure.pi fun _ => bernoulliMeasure (1 : ℝ) 0 ⟨1 / 2, by norm_num, by norm_num⟩)
    (X := fun i ω => ω i)
    (hX := fun i => measurable_pi_apply i)
    (hind := iIndepFun_pi fun _ => aemeasurable_id)
    (x := 1 / 2) (F := 1 / 2)
    (hF := fun i => by
      change (Measure.pi fun _ => bernoulliMeasure (1 : ℝ) 0 ⟨1 / 2, by norm_num, by norm_num⟩).real
        (Function.eval i ⁻¹' Set.Iic (1 / 2)) = 1 / 2
      rw [(measurePreserving_eval _ i).measureReal_preimage measurableSet_Iic.nullMeasurableSet,
        bernoulliMeasure_real_apply _ measurableSet_Iic]
      norm_num)
    (k := 2) (hk := by norm_num) (hkn := by norm_num)
