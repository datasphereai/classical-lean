import Mathlib
import ClassicalLean.InformationTheory.MutualInformation

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names : List Name := [`«ClassicalLean».«Simplex».«mutualInfo», `«ClassicalLean».«Simplex».«mutualInfo_eq_shannonEntropy_add_shannonEntropy_sub_shannonEntropy», `«ClassicalLean».«Simplex».«shannonEntropy», `«ClassicalLean».«Simplex».«shannonEntropy_le_log_card», `«Eq».«symm», `«Fin», `«Fin».«forall_fin_two», `«Fin».«sum_univ_two», `«Finset».«sum_nonneg», `«Fintype».«card_fin», `«Fintype».«sum_prod_type», `«Nat».«cast_ofNat», `«Ne».«symm», `«Real».«binEntropy», `«Real».«log», `«Real».«log_inv», `«Real».«log_mul», `«eq_or_ne», `«funext», `«ite_eq_left», `«ite_eq_right», `«mul_nonneg», `«rfl»]
  let mut mods : Array Name := #[]
  for n in names do
    match env.getModuleIdxFor? n with
    | some i =>
      let m := env.header.moduleNames[i.toNat]!
      logInfo m!"MODOF {n} {m}"
      unless mods.contains m do mods := mods.push m
    | none => logInfo m!"MODOF {n} (none)"
  let mut idx : Std.HashMap Name Nat := {}
  for h : k in [0:env.header.moduleNames.size] do
    idx := idx.insert env.header.moduleNames[k] k
  -- the modules each of `mods` imports, directly or not
  let mut below : Array NameSet := #[]
  for m in mods do
    let mut seen : NameSet := {}
    let mut stack : Array Name := #[m]
    while !stack.isEmpty do
      let a := stack.back!
      stack := stack.pop
      match idx[a]? with
      | some k =>
        for imp in env.header.moduleData[k]!.imports do
          unless seen.contains imp.module do
            seen := seen.insert imp.module
            stack := stack.push imp.module
      | none => pure ()
    below := below.push seen
  for m in mods do
    unless below.any (·.contains m) do logInfo m!"MINIMAL {m}"
