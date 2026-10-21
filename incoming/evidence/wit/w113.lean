/-- The hypotheses of `min_sub_le_of_subgradient` hold together: on the real line `E = ℝ`, the
function `f y = y ^ 2 / 2`, whose gradient at `y` is `y`, so that `g n = x n` is a subgradient at
`x n` (`f (x n) + x n * (y - x n) ≤ f y` is `0 ≤ (y - x n) ^ 2 / 2`); the step `η = 1 / 2` from
`x 0 = 1`, so that the iterates are `x n = (1 / 2) ^ n`, never `0`; the bound `G = 1` on
`‖g n‖ = (1 / 2) ^ n`; the point `z = 0`, the minimiser; and `T = 3` steps. -/
example := ClassicalLean.Analysis.SubgradientMethod.min_sub_le_of_subgradient (E := ℝ)
    (f := fun y => y ^ 2 / 2) (x := fun n => (1 / 2 : ℝ) ^ n) (g := fun n => (1 / 2 : ℝ) ^ n)
    (z := 0) (η := 1 / 2) (G := 1) (T := 3) (by norm_num) (by norm_num)
    (fun n y => by
      rw [RCLike.inner_apply, conj_trivial]
      nlinarith [sq_nonneg (y - (1 / 2 : ℝ) ^ n)])
    (fun n => by
      rw [Real.norm_eq_abs, abs_of_pos (pow_pos (by norm_num) n)]
      exact pow_le_one₀ (by norm_num) (by norm_num))
    (fun n => by rw [smul_eq_mul, pow_succ]; ring)
