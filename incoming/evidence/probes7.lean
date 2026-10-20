import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic

#check @hasGradientAt_iff_hasFDerivAt
#check @HasDerivAt.hasGradientAt'
#check @hasDerivAt_id
#check @HasDerivAt.const_sub
#check @HasDerivAt.sub_const
#check @hasFDerivAt_id
#check @HasFDerivAt.mul
#check @convex_univ
#check @isMinOn_iff
#check @sq_nonneg
#check @Fin.zero_eta
#check @Fin.mk_one
#check @Matrix.cons_val_one
