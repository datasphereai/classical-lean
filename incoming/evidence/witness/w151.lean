/-- The hypotheses of `hasLaw_sum_sq_gaussian` hold together: `k = 3` coordinates `X i ω = ω i`
on `Fin 3 → ℝ` under the product `Measure.pi fun _ => gaussianReal 0 1` of three standard normal
laws, a probability measure; the coordinates are measurable, independent (`iIndepFun_pi`), and
each has the standard normal law, a coordinate of a product measure having its factor as its law
(`measurePreserving_eval`). -/
example := ClassicalLean.Probability.ChiSquared.hasLaw_sum_sq_gaussian (Ω := Fin 3 → ℝ)
    (P := Measure.pi fun _ => gaussianReal 0 1) (k := 3) (X := fun i ω => ω i) (by norm_num)
    (fun i => measurable_pi_apply i) (iIndepFun_pi (fun _ => aemeasurable_id))
    (fun i => ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩)
