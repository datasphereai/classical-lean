
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.foldStage2 (fun acc n ci =>
    if (`ClassicalLean).isPrefixOf (privateToUserName n) && (ci matches .thmInfo _) then
      acc.push n else acc) (#[] : Array Name)
  logInfo m!"CENSUS {names.size}"
  for n in names do logInfo m!"NAME {privateToUserName n}"
