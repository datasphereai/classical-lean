import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic

example : HasGradientAt (fun x : ℝ => x * x) 2 1 := by
  rw [hasGradientAt_iff_hasFDerivAt]
  refine ((hasFDerivAt_id (1 : ℝ)).mul (hasFDerivAt_id (1 : ℝ))).congr_fderiv ?_
  ext
  simp
  norm_num
