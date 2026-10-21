/-- The hypotheses of `variance_le_sum_variance_coord` hold together: two coordinates (`n = 2`),
each taking the two values of `Fin 2`, the first with the weights `1 / 4` and `3 / 4`, the second
with `1 / 2` and `1 / 2`, so that each `p i` is a probability vector and the two differ; `f` is
`x 0 + 2 * x 1`, the values read as reals, which depends on both coordinates. -/
example := ClassicalLean.Probability.EfronStein.variance_le_sum_variance_coord (n := 2)
    (Ω := fun _ => Fin 2) (p := fun i a => ![![1 / 4, 3 / 4], ![1 / 2, 1 / 2]] i a)
    (fun i a => by fin_cases i <;> fin_cases a <;> norm_num)
    (fun i => by fin_cases i <;> norm_num [Fin.sum_univ_two])
    (f := fun x => ((x 0 : ℕ) : ℝ) + 2 * ((x 1 : ℕ) : ℝ))

/-- The hypotheses of `variance_le_sum_sq_div_four` hold together: the same two coordinates,
weights and `f = x 0 + 2 * x 1` as above, and the bounds `c = (1, 2)`: changing coordinate `0`
alone moves `f` by `0` or `1`, and changing coordinate `1` alone moves it by `0` or `2`. -/
example := ClassicalLean.Probability.EfronStein.variance_le_sum_sq_div_four (n := 2)
    (Ω := fun _ => Fin 2) (p := fun i a => ![![1 / 4, 3 / 4], ![1 / 2, 1 / 2]] i a)
    (fun i a => by fin_cases i <;> fin_cases a <;> norm_num)
    (fun i => by fin_cases i <;> norm_num [Fin.sum_univ_two])
    (f := fun x => ((x 0 : ℕ) : ℝ) + 2 * ((x 1 : ℕ) : ℝ)) (c := ![1, 2])
    (fun i x a b => by
      fin_cases i <;> fin_cases a <;> fin_cases b <;> norm_num [Function.update])
