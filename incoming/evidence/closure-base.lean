import ClassicalLean
open Lean Elab Command in
run_cmd do
  for m in (← getEnv).header.moduleNames do logInfo m!"MOD {m}"
