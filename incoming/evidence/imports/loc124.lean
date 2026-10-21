import Mathlib

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names : List Name := [`«Antitone», `«Differentiable», `«Differentiable».«continuous», `«Differentiable».«differentiableOn», `«Filter».«eventually_all_finset», `«Fin», `«Fin».«sum_univ_two», `«Finset», `«Finset».«card», `«Finset».«induction_on», `«Finset».«mem_insert_of_mem», `«Finset».«mem_insert_self», `«Finset».«mul_sum», `«Finset».«prod_insert», `«Finset».«prod_nonneg», `«Finset».«sum_apply», `«Finset».«sum_const», `«Finset».«sum_le_sum», `«Finset».«sum_nonneg», `«Finset».«univ», `«HasDerivAt», `«HasDerivAt».«add», `«HasDerivAt».«congr_deriv», `«HasDerivAt».«const_mul», `«HasDerivAt».«div_const», `«HasDerivAt».«exp», `«HasDerivAt».«mul», `«HasDerivAt».«neg», `«HasDerivAt».«sub», `«LE».«le», `«LT».«lt».«le», `«LT».«lt».«ne'», `«Measurable», `«Measurable».«const_mul», `«MeasurableSpace», `«MeasureTheory».«Integrable», `«MeasureTheory».«Integrable».«add», `«MeasureTheory».«Integrable».«const_mul», `«MeasureTheory».«Integrable».«mono'», `«MeasureTheory».«IsProbabilityMeasure», `«MeasureTheory».«Measure», `«MeasureTheory».«Measure».«ae_smul_measure», `«MeasureTheory».«Measure».«pi», `«MeasureTheory».«Measure».«real», `«MeasureTheory».«MeasurePreserving».«quasiMeasurePreserving», `«MeasureTheory».«ae_add_measure_iff», `«MeasureTheory».«ae_dirac_iff», `«MeasureTheory».«integrable_comp_eval», `«MeasureTheory».«integrable_const», `«MeasureTheory».«integrable_eval», `«MeasureTheory».«integral_add», `«MeasureTheory».«integral_comp_eval», `«MeasureTheory».«integral_const_mul», `«MeasureTheory».«integral_eval», `«MeasureTheory».«integral_mono_ae», `«MeasureTheory».«integral_nonneg», `«MeasureTheory».«measurePreserving_eval», `«MonotoneOn», `«Neg».«neg», `«Not», `«Pi».«add_apply», `«Pi».«mul_apply», `«Pi».«neg_apply», `«ProbabilityTheory».«bernoulliMeasure», `«ProbabilityTheory».«bernoulliMeasure_def», `«ProbabilityTheory».«iIndepFun», `«ProbabilityTheory».«iIndepFun».«mgf_sum», `«ProbabilityTheory».«iIndepFun_pi», `«ProbabilityTheory».«integrable_bernoulliMeasure», `«ProbabilityTheory».«integral_bernoulliMeasure», `«ProbabilityTheory».«measure_ge_le_exp_mul_mgf», `«ProbabilityTheory».«mgf», `«ProbabilityTheory».«mgf_nonneg», `«Real».«add_one_le_exp», `«Real».«exp», `«Real».«exp_add», `«Real».«exp_le_exp», `«Real».«exp_pos», `«Real».«exp_sum», `«Real».«exp_zero», `«Real».«hasDerivAt_exp», `«Real».«measurable_exp», `«Real».«norm_of_nonneg», `«Real».«quadratic_le_exp_of_nonneg», `«Set».«Ici», `«Set».«mem_Ici», `«aemeasurable_id», `«antitone_of_deriv_nonpos», `«congrArg», `«continuous_pow», `«convex_Ici», `«deriv», `«div_lt_iff₀», `«div_mul_cancel₀», `«div_mul_eq_mul_div», `«div_nonneg», `«div_nonneg_of_nonpos», `«eq_div_iff», `«eq_or_lt_of_le», `«hasDerivAt_const», `«hasDerivAt_id'», `«interior_Ici», `«le_div_iff₀», `«le_of_eq», `«le_rfl», `«le_total», `«le_trans», `«measurableSet_Iic», `«measurable_pi_apply», `«monotoneOn_of_deriv_nonneg», `«mul_assoc», `«mul_le_mul», `«mul_le_mul_of_nonneg_left», `«mul_nonneg», `«neg_zero», `«nsmul_eq_mul», `«one_mul», `«rfl», `«sq_nonneg», `«sub_nonneg»]
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
