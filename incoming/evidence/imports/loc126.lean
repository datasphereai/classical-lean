import Mathlib

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names : List Name := [`«ENNReal».«toReal_one», `«ENNReal».«toReal_prod», `«ENNReal».«toReal_sum», `«Eq».«symm», `«Eq».«trans», `«Equiv».«coe_toEmbedding», `«Equiv».«symm», `«Equiv».«toEmbedding», `«Fin», `«Fin».«card_Iic», `«Fin».«card_Iio», `«Fin».«isLt», `«Fin».«val», `«Finset», `«Finset».«Icc», `«Finset».«Iic», `«Finset».«Iio», `«Finset».«card», `«Finset».«card_compl», `«Finset».«card_le_card», `«Finset».«card_map», `«Finset».«card_univ», `«Finset».«filter», `«Finset».«map», `«Finset».«measurableSet_biInter», `«Finset».«mem_Icc», `«Finset».«mem_Iic», `«Finset».«mem_Iio», `«Finset».«mem_compl», `«Finset».«mem_filter», `«Finset».«mem_map», `«Finset».«mem_range», `«Finset».«mem_univ», `«Finset».«powerset_univ», `«Finset».«prod_congr», `«Finset».«prod_const», `«Finset».«prod_mul_prod_compl», `«Finset».«range», `«Finset».«sum_congr», `«Finset».«sum_filter», `«Finset».«sum_powerset_apply_card», `«Finset».«univ», `«Fintype».«card», `«Fintype».«card_fin», `«Function».«eval», `«Measurable», `«MeasurableSet», `«MeasurableSpace», `«MeasureTheory».«IsProbabilityMeasure», `«MeasureTheory».«IsProbabilityMeasure».«measure_univ», `«MeasureTheory».«Measure», `«MeasureTheory».«Measure».«pi», `«MeasureTheory».«Measure».«real», `«MeasureTheory».«MeasurePreserving».«measureReal_preimage», `«MeasureTheory».«measurePreserving_eval», `«MeasureTheory».«measureReal_compl», `«MeasureTheory».«measureReal_def», `«MeasureTheory».«measure_biUnion_finset», `«MeasureTheory».«measure_ne_top», `«Monotone», `«Nat».«choose», `«Nat».«sub_add_cancel», `«Not», `«ProbabilityTheory».«bernoulliMeasure», `«ProbabilityTheory».«bernoulliMeasure_real_apply», `«ProbabilityTheory».«iIndepFun», `«ProbabilityTheory».«iIndepFun».«measure_inter_preimage_eq_mul», `«ProbabilityTheory».«iIndepFun_pi», `«Set», `«Set».«Iic», `«Set».«Ioi», `«Set».«PairwiseDisjoint», `«Set».«disjoint_left», `«Set».«mem_Iic», `«Set».«mem_Ioi», `«Set».«mem_iInter», `«Set».«mem_iUnion», `«Set».«mem_ofPred_eq», `«Set».«mem_preimage», `«Subtype».«val», `«Tuple».«monotone_sort», `«Tuple».«sort», `«absurd», `«aemeasurable_id», `«exists_prop», `«ite_eq_left», `«ite_eq_right», `«le_trans», `«lt_of_lt_of_le», `«measurableSet_Iic», `«measurableSet_Ioi», `«measurableSet_le», `«measurable_const», `«measurable_pi_apply», `«not_le», `«not_lt», `«nsmul_eq_mul», `«rfl», `«true_and», `«true_implies», `«unitInterval».«symm»]
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
