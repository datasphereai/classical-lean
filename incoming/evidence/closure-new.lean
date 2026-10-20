import ClassicalLean.Analysis.PowerMethod
import ClassicalLean.Algebra.Pseudoinverse
import ClassicalLean.Probability.ChiSquared
import ClassicalLean.Analysis.KKT
import ClassicalLean.InformationTheory.Huffman
open Lean Elab Command in
run_cmd do
  for m in (← getEnv).header.moduleNames do logInfo m!"MOD {m}"
