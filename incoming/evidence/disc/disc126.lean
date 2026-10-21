import Mathlib

open MeasureTheory ProbabilityTheory Finset

/-- The `k`-th smallest entry (counting from `0`) of a real tuple: sort the tuple
increasingly and read off position `k`. -/
noncomputable def orderStat {n : ℕ} (v : Fin n → ℝ) (k : Fin n) : ℝ :=
  v (Tuple.sort v k)

/-- The entry at sorted position `k` is at most `x` iff at least `k + 1` entries are. -/
private lemma orderStat_le_iff {n : ℕ} (v : Fin n → ℝ) (k : Fin n) (x : ℝ) :
    orderStat v k ≤ x ↔ k.val + 1 ≤ (Finset.univ.filter fun i => v i ≤ x).card := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := k.isLt; omega⟩
  unfold orderStat
  set σ := Tuple.sort v with hσ
  have hmono : Monotone (v ∘ σ) := Tuple.monotone_sort v
  have hmap : (Finset.univ.filter fun j => v (σ j) ≤ x).map σ.toEmbedding
      = Finset.univ.filter fun i => v i ≤ x := by
    ext i
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hj
    · intro hi
      exact ⟨σ.symm i, by simpa using hi, by simp⟩
  have hcard : (Finset.univ.filter fun i => v i ≤ x).card
      = (Finset.univ.filter fun j => v (σ j) ≤ x).card := by
    rw [← hmap, Finset.card_map]
  rw [hcard]
  constructor
  · intro hk
    have hsub : Finset.Iic k ⊆ Finset.univ.filter fun j => v (σ j) ≤ x := by
      intro j hj
      rw [Finset.mem_Iic] at hj
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, le_trans (hmono hj) hk⟩
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    exact this
  · intro hk
    by_contra hlt
    push Not at hlt
    have hsub : (Finset.univ.filter fun j => v (σ j) ≤ x) ⊆ Finset.Iio k := by
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_Iio]
      by_contra hjk
      push Not at hjk
      exact (not_lt.2 hj.2) (lt_of_lt_of_le hlt (hmono hjk))
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

/-- A product of `a` over `S` and `b` off `S`. -/
private lemma prod_ite_mem_eq {n : ℕ} (S : Finset (Fin n)) (a b : ℝ) :
    ∏ i, (if i ∈ S then a else b) = a ^ S.card * b ^ (n - S.card) := by
  have h1 : ∏ i ∈ S, (if i ∈ S then a else b) = a ^ S.card := by
    rw [Finset.prod_congr rfl (fun i hi => (ite_eq_left hi : (if i ∈ S then a else b) = a)),
      Finset.prod_const]
  have h2 : ∏ i ∈ Sᶜ, (if i ∈ S then a else b) = b ^ (n - S.card) := by
    rw [Finset.prod_congr rfl
      (fun i hi => (ite_eq_right (Finset.mem_compl.1 hi) : (if i ∈ S then a else b) = b)),
      Finset.prod_const, Finset.card_compl, Fintype.card_fin]
  rw [← Finset.prod_mul_prod_compl S, h1, h2]

/-- Summing over subsets of size at least `k`, grouped by size. -/
private lemma sum_filter_card (n k : ℕ) (a b : ℝ) :
    ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => k ≤ S.card),
        a ^ S.card * b ^ (n - S.card)
      = ∑ j ∈ Finset.Icc k n, (n.choose j : ℝ) * a ^ j * b ^ (n - j) := by
  rw [Finset.sum_filter, ← Finset.powerset_univ,
    Finset.sum_powerset_apply_card (f := fun j => if k ≤ j then a ^ j * b ^ (n - j) else 0),
    Finset.card_univ, Fintype.card_fin]
  have hIcc : Finset.Icc k n = (Finset.range (n + 1)).filter (fun j => k ≤ j) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]
    omega
  rw [hIcc, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [nsmul_eq_mul]; ring
  · simp

/-- Distribution of the `k`-th smallest of `n` independent draws with common
value `F = P(X i ≤ x)`. -/
theorem measureReal_orderStat_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ) {x F : ℝ} (hF : ∀ i, μ.real {ω | X i ω ≤ x} = F)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    μ.real {ω | orderStat (fun i => X i ω) ⟨k - 1, by omega⟩ ≤ x}
      = ∑ j ∈ Finset.Icc k n, (n.choose j : ℝ) * F ^ j * (1 - F) ^ (n - j) := by
  have hev : {ω | orderStat (fun i => X i ω) ⟨k - 1, by omega⟩ ≤ x}
      = {ω | k ≤ (Finset.univ.filter fun i => X i ω ≤ x).card} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [orderStat_le_iff]
    change k - 1 + 1 ≤ (Finset.univ.filter fun i => X i ω ≤ x).card ↔
      k ≤ (Finset.univ.filter fun i => X i ω ≤ x).card
    rw [Nat.sub_add_cancel hk]
  let A : Finset (Fin n) → Fin n → Set ℝ :=
    fun S i => if i ∈ S then Set.Iic x else Set.Ioi x
  let E : Finset (Fin n) → Set Ω :=
    fun S => ⋂ i ∈ (Finset.univ : Finset (Fin n)), X i ⁻¹' A S i
  have hmemE : ∀ S ω, ω ∈ E S ↔ (Finset.univ.filter fun i => X i ω ≤ x) = S := by
    intro S ω
    simp only [E, A, Set.mem_iInter, Set.mem_preimage, Finset.mem_univ, true_implies]
    constructor
    · intro h
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hi := h i
      by_cases hiS : i ∈ S
      · rw [ite_eq_left hiS, Set.mem_Iic] at hi
        exact ⟨fun _ => hiS, fun _ => hi⟩
      · rw [ite_eq_right hiS, Set.mem_Ioi] at hi
        exact ⟨fun h' => absurd h' (not_le.2 hi), fun h' => absurd h' hiS⟩
    · intro h i
      have hi : i ∈ S ↔ X i ω ≤ x := by rw [← h]; simp
      by_cases hiS : i ∈ S
      · rw [ite_eq_left hiS, Set.mem_Iic]; exact hi.1 hiS
      · rw [ite_eq_right hiS, Set.mem_Ioi]; exact not_le.1 (fun h' => hiS (hi.2 h'))
  have hA : ∀ S i, MeasurableSet (A S i) := by
    intro S i
    by_cases h : i ∈ S
    · simp only [A, ite_eq_left h]; exact measurableSet_Iic
    · simp only [A, ite_eq_right h]; exact measurableSet_Ioi
  have hE : ∀ S, MeasurableSet (E S) := fun S =>
    Finset.measurableSet_biInter _ fun i _ => (hX i) (hA S i)
  let T : Finset (Finset (Fin n)) := Finset.univ.filter fun S => k ≤ S.card
  have hU : {ω | k ≤ (Finset.univ.filter fun i => X i ω ≤ x).card} = ⋃ S ∈ T, E S := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, T, Finset.mem_filter, Finset.mem_univ,
      true_and, exists_prop]
    constructor
    · intro h
      exact ⟨_, h, (hmemE _ ω).2 rfl⟩
    · rintro ⟨S, hS, hωS⟩
      rw [(hmemE S ω).1 hωS]
      exact hS
  have hdisj : Set.PairwiseDisjoint (↑T : Set (Finset (Fin n))) E := by
    intro S _ S' _ hne
    exact Set.disjoint_left.2 fun ω h1 h2 =>
      hne (((hmemE S ω).1 h1).symm.trans ((hmemE S' ω).1 h2))
  have hpiece : ∀ S, (μ (E S)).toReal = F ^ S.card * (1 - F) ^ (n - S.card) := by
    intro S
    have h1 : μ (E S) = ∏ i ∈ (Finset.univ : Finset (Fin n)), μ (X i ⁻¹' A S i) :=
      hind.measure_inter_preimage_eq_mul Finset.univ (fun i _ => hA S i)
    have h2 : ∀ i, (μ (X i ⁻¹' A S i)).toReal = if i ∈ S then F else 1 - F := by
      intro i
      by_cases hiS : i ∈ S
      · simp only [A, ite_eq_left hiS]
        exact hF i
      · simp only [A, ite_eq_right hiS]
        have hc : X i ⁻¹' Set.Ioi x = {ω | X i ω ≤ x}ᶜ := by
          ext ω; simp
        rw [hc]
        change μ.real ({ω | X i ω ≤ x}ᶜ) = 1 - F
        rw [measureReal_compl (measurableSet_le (hX i) measurable_const), hF i,
          measureReal_def, measure_univ, ENNReal.toReal_one]
    rw [h1, ENNReal.toReal_prod, Finset.prod_congr rfl (fun i _ => h2 i)]
    exact prod_ite_mem_eq S F (1 - F)
  rw [hev, hU, measureReal_def, measure_biUnion_finset hdisj (fun S _ => hE S),
    ENNReal.toReal_sum (fun S _ => measure_ne_top μ (E S)),
    Finset.sum_congr rfl (fun S _ => hpiece S)]
  exact sum_filter_card n k F (1 - F)


/-- The hypotheses of `measureReal_orderStat_le` hold together: three independent fair coins with
values `1` and `0`, the coordinates of the product of three copies of `Ber(1, 0, 1/2)`, at
`x = 1/2` (so `F = 1/2`) and `k = 2`. -/
noncomputable def disc_w1 := measureReal_orderStat_le (Ω := Fin 3 → ℝ) (n := 3)
    (μ := Measure.pi fun _ => bernoulliMeasure (1 : ℝ) 0 ⟨1 / 2, by norm_num, by norm_num⟩)
    (X := fun i ω => ω i)
    (hX := fun i => measurable_pi_apply i)
    (hind := iIndepFun_pi fun _ => aemeasurable_id)
    (x := 1 / 2) (F := 1 / 2)
    (hF := fun i => by
      change (Measure.pi fun _ => bernoulliMeasure (1 : ℝ) 0 ⟨1 / 2, by norm_num, by norm_num⟩).real
        (Function.eval i ⁻¹' Set.Iic (1 / 2)) = 1 / 2
      rw [(measurePreserving_eval _ i).measureReal_preimage measurableSet_Iic.nullMeasurableSet,
        bernoulliMeasure_real_apply _ measurableSet_Iic]
      norm_num)
    (k := 2) (hk := by norm_num) (hkn := by norm_num)

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let cands : List (String × List Name) := [
    ("noncomputable", [`«noncomputable»]),
    ("def", [`«def»]),
    ("orderStat", [`«orderStat»]),
    ("n", [`«n»]),
    ("ℕ", [`«ℕ»]),
    ("v", [`«v»]),
    ("Fin", [`«Fin»]),
    ("ℝ", [`«ℝ»]),
    ("k", [`«k»]),
    ("Tuple.sort", [`«Tuple».«sort», `«Tuple»]),
    ("private", [`«private»]),
    ("lemma", [`«lemma»]),
    ("orderStat_le_iff", [`«orderStat_le_iff»]),
    ("x", [`«x»]),
    ("k.val", [`«k».«val», `«k»]),
    ("Finset.univ.filter", [`«Finset».«univ».«filter», `«Finset».«univ», `«Finset»]),
    ("fun", [`«fun»]),
    ("i", [`«i»]),
    ("card", [`«card»]),
    ("by", [`«by»]),
    ("obtain", [`«obtain»]),
    ("m", [`«m»]),
    ("rfl", [`«rfl»]),
    ("have", [`«have»]),
    ("k.isLt", [`«k».«isLt», `«k»]),
    ("omega", [`«omega»]),
    ("unfold", [`«unfold»]),
    ("set", [`«set»]),
    ("σ", [`«σ»]),
    ("with", [`«with»]),
    ("hσ", [`«hσ»]),
    ("hmono", [`«hmono»]),
    ("Monotone", [`«Monotone»]),
    ("Tuple.monotone_sort", [`«Tuple».«monotone_sort», `«Tuple»]),
    ("hmap", [`«hmap»]),
    ("j", [`«j»]),
    ("map", [`«map»]),
    ("σ.toEmbedding", [`«σ».«toEmbedding», `«σ»]),
    ("ext", [`«ext»]),
    ("simp", [`«simp»]),
    ("only", [`«only»]),
    ("Finset.mem_map", [`«Finset».«mem_map», `«Finset»]),
    ("Finset.mem_filter", [`«Finset».«mem_filter», `«Finset»]),
    ("Finset.mem_univ", [`«Finset».«mem_univ», `«Finset»]),
    ("true_and", [`«true_and»]),
    ("Equiv.coe_toEmbedding", [`«Equiv».«coe_toEmbedding», `«Equiv»]),
    ("constructor", [`«constructor»]),
    ("rintro", [`«rintro»]),
    ("hj", [`«hj»]),
    ("exact", [`«exact»]),
    ("intro", [`«intro»]),
    ("hi", [`«hi»]),
    ("σ.symm", [`«σ».«symm», `«σ»]),
    ("simpa", [`«simpa»]),
    ("using", [`«using»]),
    ("hcard", [`«hcard»]),
    ("rw", [`«rw»]),
    ("Finset.card_map", [`«Finset».«card_map», `«Finset»]),
    ("hk", [`«hk»]),
    ("hsub", [`«hsub»]),
    ("Finset.Iic", [`«Finset».«Iic», `«Finset»]),
    ("Finset.mem_Iic", [`«Finset».«mem_Iic», `«Finset»]),
    ("at", [`«at»]),
    ("_", [`«_»]),
    ("le_trans", [`«le_trans»]),
    ("Finset.card_le_card", [`«Finset».«card_le_card», `«Finset»]),
    ("Fin.card_Iic", [`«Fin».«card_Iic», `«Fin»]),
    ("this", [`«this»]),
    ("by_contra", [`«by_contra»]),
    ("hlt", [`«hlt»]),
    ("push", [`«push»]),
    ("Not", [`«Not»]),
    ("Finset.Iio", [`«Finset».«Iio», `«Finset»]),
    ("Finset.mem_Iio", [`«Finset».«mem_Iio», `«Finset»]),
    ("hjk", [`«hjk»]),
    ("not_lt", [`«not_lt»]),
    ("lt_of_lt_of_le", [`«lt_of_lt_of_le»]),
    ("Fin.card_Iio", [`«Fin».«card_Iio», `«Fin»]),
    ("prod_ite_mem_eq", [`«prod_ite_mem_eq»]),
    ("S", [`«S»]),
    ("Finset", [`«Finset»]),
    ("a", [`«a»]),
    ("b", [`«b»]),
    ("if", [`«if»]),
    ("then", [`«then»]),
    ("else", [`«else»]),
    ("S.card", [`«S».«card», `«S»]),
    ("h1", [`«h1»]),
    ("Finset.prod_congr", [`«Finset».«prod_congr», `«Finset»]),
    ("ite_eq_left", [`«ite_eq_left»]),
    ("Finset.prod_const", [`«Finset».«prod_const», `«Finset»]),
    ("h2", [`«h2»]),
    ("Sᶜ", [`«Sᶜ»]),
    ("ite_eq_right", [`«ite_eq_right»]),
    ("Finset.mem_compl", [`«Finset».«mem_compl», `«Finset»]),
    ("Finset.card_compl", [`«Finset».«card_compl», `«Finset»]),
    ("Fintype.card_fin", [`«Fintype».«card_fin», `«Fintype»]),
    ("Finset.prod_mul_prod_compl", [`«Finset».«prod_mul_prod_compl», `«Finset»]),
    ("sum_filter_card", [`«sum_filter_card»]),
    ("Finset.univ", [`«Finset».«univ», `«Finset»]),
    ("filter", [`«filter»]),
    ("Finset.Icc", [`«Finset».«Icc», `«Finset»]),
    ("n.choose", [`«n».«choose», `«n»]),
    ("Finset.sum_filter", [`«Finset».«sum_filter», `«Finset»]),
    ("Finset.powerset_univ", [`«Finset».«powerset_univ», `«Finset»]),
    ("Finset.sum_powerset_apply_card", [`«Finset».«sum_powerset_apply_card», `«Finset»]),
    ("f", [`«f»]),
    ("Finset.card_univ", [`«Finset».«card_univ», `«Finset»]),
    ("hIcc", [`«hIcc»]),
    ("Finset.range", [`«Finset».«range», `«Finset»]),
    ("Finset.mem_Icc", [`«Finset».«mem_Icc», `«Finset»]),
    ("Finset.mem_range", [`«Finset».«mem_range», `«Finset»]),
    ("refine", [`«refine»]),
    ("Finset.sum_congr", [`«Finset».«sum_congr», `«Finset»]),
    ("split_ifs", [`«split_ifs»]),
    ("h", [`«h»]),
    ("nsmul_eq_mul", [`«nsmul_eq_mul»]),
    ("ring", [`«ring»]),
    ("theorem", [`«theorem»]),
    ("measureReal_orderStat_le", [`«measureReal_orderStat_le»]),
    ("Ω", [`«Ω»]),
    ("Type", [`«Type»]),
    ("MeasurableSpace", [`«MeasurableSpace»]),
    ("μ", [`«μ»]),
    ("Measure", [`«Measure»]),
    ("IsProbabilityMeasure", [`«IsProbabilityMeasure»]),
    ("X", [`«X»]),
    ("hX", [`«hX»]),
    ("Measurable", [`«Measurable»]),
    ("hind", [`«hind»]),
    ("iIndepFun", [`«iIndepFun»]),
    ("F", [`«F»]),
    ("hF", [`«hF»]),
    ("μ.real", [`«μ».«real», `«μ»]),
    ("ω", [`«ω»]),
    ("hkn", [`«hkn»]),
    ("hev", [`«hev»]),
    ("Set.mem_ofPred_eq", [`«Set».«mem_ofPred_eq», `«Set»]),
    ("change", [`«change»]),
    ("Nat.sub_add_cancel", [`«Nat».«sub_add_cancel», `«Nat»]),
    ("let", [`«let»]),
    ("A", [`«A»]),
    ("Set", [`«Set»]),
    ("Set.Iic", [`«Set».«Iic», `«Set»]),
    ("Set.Ioi", [`«Set».«Ioi», `«Set»]),
    ("E", [`«E»]),
    ("hmemE", [`«hmemE»]),
    ("Set.mem_iInter", [`«Set».«mem_iInter», `«Set»]),
    ("Set.mem_preimage", [`«Set».«mem_preimage», `«Set»]),
    ("true_implies", [`«true_implies»]),
    ("by_cases", [`«by_cases»]),
    ("hiS", [`«hiS»]),
    ("Set.mem_Iic", [`«Set».«mem_Iic», `«Set»]),
    ("Set.mem_Ioi", [`«Set».«mem_Ioi», `«Set»]),
    ("h'", [`«h'»]),
    ("absurd", [`«absurd»]),
    ("not_le", [`«not_le»]),
    ("hA", [`«hA»]),
    ("MeasurableSet", [`«MeasurableSet»]),
    ("measurableSet_Iic", [`«measurableSet_Iic»]),
    ("measurableSet_Ioi", [`«measurableSet_Ioi»]),
    ("hE", [`«hE»]),
    ("Finset.measurableSet_biInter", [`«Finset».«measurableSet_biInter», `«Finset»]),
    ("T", [`«T»]),
    ("hU", [`«hU»]),
    ("Set.mem_iUnion", [`«Set».«mem_iUnion», `«Set»]),
    ("exists_prop", [`«exists_prop»]),
    ("hS", [`«hS»]),
    ("hωS", [`«hωS»]),
    ("hdisj", [`«hdisj»]),
    ("Set.PairwiseDisjoint", [`«Set».«PairwiseDisjoint», `«Set»]),
    ("S'", [`«S'»]),
    ("hne", [`«hne»]),
    ("Set.disjoint_left", [`«Set».«disjoint_left», `«Set»]),
    ("symm.trans", [`«symm».«trans», `«symm»]),
    ("hpiece", [`«hpiece»]),
    ("toReal", [`«toReal»]),
    ("hind.measure_inter_preimage_eq_mul", [`«hind».«measure_inter_preimage_eq_mul», `«hind»]),
    ("hc", [`«hc»]),
    ("ᶜ", [`«ᶜ»]),
    ("measureReal_compl", [`«measureReal_compl»]),
    ("measurableSet_le", [`«measurableSet_le»]),
    ("measurable_const", [`«measurable_const»]),
    ("measureReal_def", [`«measureReal_def»]),
    ("measure_univ", [`«measure_univ»]),
    ("ENNReal.toReal_one", [`«ENNReal».«toReal_one», `«ENNReal»]),
    ("ENNReal.toReal_prod", [`«ENNReal».«toReal_prod», `«ENNReal»]),
    ("measure_biUnion_finset", [`«measure_biUnion_finset»]),
    ("ENNReal.toReal_sum", [`«ENNReal».«toReal_sum», `«ENNReal»]),
    ("measure_ne_top", [`«measure_ne_top»]),
    ("example", [`«example»]),
    ("Measure.pi", [`«Measure».«pi», `«Measure»]),
    ("bernoulliMeasure", [`«bernoulliMeasure»]),
    ("norm_num", [`«norm_num»]),
    ("measurable_pi_apply", [`«measurable_pi_apply»]),
    ("iIndepFun_pi", [`«iIndepFun_pi»]),
    ("aemeasurable_id", [`«aemeasurable_id»]),
    ("real", [`«real»]),
    ("Function.eval", [`«Function».«eval», `«Function»]),
    ("measurePreserving_eval", [`«measurePreserving_eval»]),
    ("measureReal_preimage", [`«measureReal_preimage»]),
    ("measurableSet_Iic.nullMeasurableSet", [`«measurableSet_Iic».«nullMeasurableSet», `«measurableSet_Iic»]),
    ("bernoulliMeasure_real_apply", [`«bernoulliMeasure_real_apply»])
  ]
  for (s, ps) in cands do
    let mut found := false
    for p in ps do
      unless found do
        try
          let n ← liftCoreM (realizeGlobalConstNoOverload (mkIdent p))
          if (env.getModuleIdxFor? n).isSome then logInfo m!"FULL {s} {n}"
          else logInfo m!"LOCAL {s} {n}"
          found := true
        catch _ => pure ()
    unless found do logInfo m!"NONE {s}"
  let mut used : NameSet := {}
  for (_, ci) in env.constants.map₂.toList do
    let cs := ci.type.getUsedConstants ++ (match ci.value? with | some v => v.getUsedConstants | none => #[])
    for c in cs do
      if (env.getModuleIdxFor? c).isSome then used := used.insert c
  for c in used.toList do logInfo m!"USED {c}"
