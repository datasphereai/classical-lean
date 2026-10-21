import Mathlib

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names : List Name := [`«Eq».«trans», `«Equiv».«left_inv», `«Equiv».«right_inv», `«Equiv».«sum_comp», `«Fin», `«Fin».«cons», `«Fin».«cons_succ», `«Fin».«cons_update», `«Fin».«cons_zero», `«Fin».«prod_univ_succ», `«Fin».«succ», `«Fin».«sum_univ_succ», `«Fin».«tail», `«Fin».«update_cons_zero», `«Finset», `«Finset».«exists_min_image», `«Finset».«mem_univ», `«Finset».«mul_sum», `«Finset».«not_nonempty_iff_eq_empty», `«Finset».«prod_nonneg», `«Finset».«sum_add_distrib», `«Finset».«sum_comm», `«Finset».«sum_congr», `«Finset».«sum_empty», `«Finset».«sum_le_sum», `«Finset».«sum_mul», `«Finset».«sum_nonneg», `«Finset».«sum_sub_distrib», `«Finset».«univ», `«Fintype», `«Fintype».«sum_prod_type», `«Fintype».«sum_unique», `«Function».«update», `«LE».«le».«trans», `«Nonempty», `«Trans».«trans», `«add_le_add», `«le_abs_self», `«le_of_eq», `«mul_add», `«mul_le_mul_of_nonneg_left», `«mul_nonneg», `«mul_one», `«one_mul», `«rfl», `«sq_nonneg», `«sub_nonneg», `«sub_zero», `«zero_ne_one»]
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
