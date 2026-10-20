
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.foldStage2 (fun acc n _ => acc.push n) (#[] : Array Name)
  logInfo m!"ALLCONST {names.size}"
  for n in names do logInfo m!"CONST {n}"
