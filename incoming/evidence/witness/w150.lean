/-- The hypotheses of `pinv_unique` hold together: `A = !![1, 2; 0, 0]`, a matrix of rank one that
is neither symmetric nor invertible, and `X = !![1/5, 0; 2/5, 0]`, which is `Aᵀ / 5` and satisfies
the four Penrose equations: `A X = !![1, 0; 0, 0]` and `X A = !![1/5, 2/5; 2/5, 4/5]` are
symmetric, `A X A = A` and `X A X = X`. -/
example := ClassicalLean.Algebra.Pseudoinverse.pinv_unique (m := Fin 2) (n := Fin 2)
    (A := !![(1 : ℝ), 2; 0, 0]) (X := !![(1 / 5 : ℝ), 0; 2 / 5, 0])
    (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two])
    (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two])
    (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two])
    (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two])

/-- The hypotheses of `pinv_eq_leastSquares` hold together: the three-by-two matrix
`A = !![1, 0; 0, 1; 1, 1]` has full column rank: `Aᵀ * A = !![2, 1; 1, 2]`, whose determinant `3`
is a unit. -/
example := ClassicalLean.Algebra.Pseudoinverse.pinv_eq_leastSquares (m := Fin 3) (n := Fin 2)
    (A := !![(1 : ℝ), 0; 0, 1; 1, 1])
    (by
      rw [isUnit_iff_ne_zero, Matrix.det_fin_two]
      norm_num [Matrix.mul_apply, Fin.sum_univ_three])
