import Mathlib

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names : List Name := [`«Finset».«card_range», `«Finset».«inf'», `«Finset».«inf'_le», `«Finset».«mem_range», `«Finset».«range», `«Finset».«sum_const», `«Finset».«sum_le_sum», `«Finset».«sum_range_succ», `«InnerProductSpace», `«LE».«le», `«LT».«lt».«le», `«NormedAddCommGroup», `«Real».«norm_eq_abs», `«inner_sub_left», `«inner_sub_right», `«le_div_iff₀», `«mul_le_mul_of_nonneg_left», `«mul_pos», `«mul_pow», `«norm_nonneg», `«norm_smul», `«norm_sub_sq_real», `«nsmul_eq_mul», `«real_inner_comm», `«real_inner_smul_right», `«sq_abs», `«sq_nonneg», `«two_pos»]
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
