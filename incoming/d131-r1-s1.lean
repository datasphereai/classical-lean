import ClassicalLean.InformationTheory.MutualInformation

/-!
# Han's inequality

For a joint law `P` of the coordinates of `x : ι → α`, `(n - 1) H(X) ≤ ∑ᵢ H(X without coordinate i)`,
with `n` the number of coordinates. The proof orders the coordinates, applies strong
subadditivity `H(C, A, B) + H(C) ≤ H(C, A) + H(C, B)` with `C` the coordinates before `i`, `A` the
coordinate `i` and `B` the coordinates after it, and sums the resulting inequalities, whose prefix
terms telescope.
-/

open ClassicalLean.Simplex

/-- The pushforward of a weight vector along a map. -/
private noncomputable def marg {X Y : Type*} [Fintype X] [DecidableEq Y] (f : X → Y)
    (P : X → ℝ) : Y → ℝ :=
  fun y => ∑ x, if f x = y then P x else 0

/-- Restriction of a family to the coordinates satisfying `S`. -/
private def restr {ι α : Type*} (S : ι → Prop) (x : ι → α) : {j // S j} → α := fun j => x j.1

private theorem restr_eq_iff {ι α : Type*} {S : ι → Prop} {x y : ι → α} :
    restr S x = restr S y ↔ ∀ j, S j → x j = y j :=
  ⟨fun h j hj => congrFun h ⟨j, hj⟩, fun h => funext fun j => h j.1 j.2⟩

private theorem marg_nonneg {X Y : Type*} [Fintype X] [DecidableEq Y] {P : X → ℝ}
    (hP : ∀ x, 0 ≤ P x) (f : X → Y) (y : Y) : 0 ≤ marg f P y :=
  Finset.sum_nonneg fun x _ => by split_ifs <;> simp [hP x]

private theorem shannonEntropy_marg {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (P : X → ℝ) :
    shannonEntropy (marg f P)
      = -∑ x, P x * Real.log (∑ x', if f x' = f x then P x' else 0) := by
  rw [shannonEntropy]
  congr 1
  simp only [marg, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [ite_mul, zero_mul]
  first | rw [Finset.sum_ite_eq] | rw [Finset.sum_ite_eq']
  rw [if_pos (Finset.mem_univ _)]

private theorem shannonEntropy_marg_congr {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq Y] [DecidableEq Z] (f : X → Y) (g : X → Z) {P : X → ℝ}
    (h : ∀ x x', f x' = f x ↔ g x' = g x) :
    shannonEntropy (marg f P) = shannonEntropy (marg g P) := by
  rw [shannonEntropy_marg, shannonEntropy_marg]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 2
  refine Finset.sum_congr rfl fun x' _ => ?_
  by_cases hx : f x' = f x
  · rw [if_pos hx, if_pos ((h x x').mp hx)]
  · rw [if_neg hx, if_neg fun h' => hx ((h x x').mpr h')]

private theorem shannonEntropy_marg_of_injective {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] {f : X → Y} (hf : Function.Injective f) (P : X → ℝ) :
    shannonEntropy (marg f P) = shannonEntropy P := by
  rw [shannonEntropy_marg, shannonEntropy]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x, if_pos rfl]
  · intro x' _ hx'
    exact if_neg fun h => hx' (hf h)
  · intro hx
    exact absurd (Finset.mem_univ x) hx

private theorem marg_comp {X Y Z : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    [DecidableEq Z] (f : X → Y) (g : Y → Z) (P : X → ℝ) :
    marg g (marg f P) = marg (fun x => g (f x)) P := by
  funext z
  simp only [marg]
  calc ∑ y, (if g y = z then ∑ x, (if f x = y then P x else 0) else 0)
      = ∑ y, ∑ x, (if f x = y then (if g (f x) = z then P x else 0) else 0) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        by_cases h : g y = z
        · rw [if_pos h]
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases h1 : f x = y
          · rw [if_pos h1, if_pos h1, if_pos (by rw [h1]; exact h)]
          · rw [if_neg h1, if_neg h1]
        · rw [if_neg h]
          symm
          refine Finset.sum_eq_zero fun x _ => ?_
          by_cases h1 : f x = y
          · rw [if_pos h1, if_neg (fun h2 => h (by rw [h1] at h2; exact h2))]
          · rw [if_neg h1]
    _ = ∑ x, ∑ y, (if f x = y then (if g (f x) = z then P x else 0) else 0) := Finset.sum_comm
    _ = ∑ x, (if g (f x) = z then P x else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        first | rw [Finset.sum_ite_eq] | rw [Finset.sum_ite_eq']
        rw [if_pos (Finset.mem_univ _)]

private theorem marg_equiv {Y Z : Type*} [Fintype Y] [DecidableEq Z] (e : Y ≃ Z) (R : Y → ℝ) :
    marg e R = fun z => R (e.symm z) := by
  funext z
  simp only [marg]
  rw [Finset.sum_eq_single (e.symm z)]
  · simp
  · intro y _ hy
    rw [if_neg]
    intro h
    exact hy (by rw [← h, Equiv.symm_apply_apply])
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem marg_fst {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (R : α × β → ℝ) : marg Prod.fst R = fun a => ∑ b, R (a, b) := by
  funext a
  simp only [marg]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp
  · intro a' _ ha'
    exact Finset.sum_eq_zero fun b _ => if_neg ha'
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem marg_via_equiv {Y Z W : Type*} [Fintype Y] [Fintype Z] [Fintype W]
    [DecidableEq Z] [DecidableEq W] (e : Y ≃ Z × W) (R : Y → ℝ) :
    marg (fun y => (e y).1) R = fun z => ∑ w, R (e.symm (z, w)) :=
  calc marg (fun y => (e y).1) R = marg Prod.fst (marg e R) := (marg_comp e Prod.fst R).symm
    _ = marg Prod.fst (fun p => R (e.symm p)) := by rw [marg_equiv]
    _ = fun z => ∑ w, R (e.symm (z, w)) := marg_fst (fun p => R (e.symm p))

/-- Strong subadditivity for a nonnegative weight vector on `C × (A × B)`. -/
private theorem ssa_sum {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    {Q : C × (A × B) → ℝ} (hQ : ∀ q, 0 ≤ Q q) :
    shannonEntropy Q + shannonEntropy (fun c => ∑ ab, Q (c, ab))
      ≤ shannonEntropy (fun ca : C × A => ∑ b, Q (ca.1, (ca.2, b)))
        + shannonEntropy (fun cb : C × B => ∑ a, Q (cb.1, (a, cb.2))) := by
  have hTa : ∀ c, ∑ a, ∑ b, Q (c, (a, b)) = ∑ ab, Q (c, ab) := fun c => by
    rw [Fintype.sum_prod_type]
  have hTb : ∀ c, ∑ b, ∑ a, Q (c, (a, b)) = ∑ ab, Q (c, ab) := fun c => by
    rw [Finset.sum_comm]; exact hTa c
  have hQa : ∀ ca : C × A, 0 ≤ ∑ b, Q (ca.1, (ca.2, b)) := fun ca =>
    Finset.sum_nonneg fun b _ => hQ _
  have hQb : ∀ cb : C × B, 0 ≤ ∑ a, Q (cb.1, (a, cb.2)) := fun cb =>
    Finset.sum_nonneg fun a _ => hQ _
  have h1 := shannonEntropy_eq_add_condEntropy hQ
  have h2 : shannonEntropy (fun ca : C × A => ∑ b, Q (ca.1, (ca.2, b)))
      = shannonEntropy (fun c => ∑ ab, Q (c, ab))
        + condEntropy (fun ca : C × A => ∑ b, Q (ca.1, (ca.2, b))) := by
    have := shannonEntropy_eq_add_condEntropy hQa
    have hf : (fun c => ∑ a, ∑ b, Q (c, (a, b))) = fun c => ∑ ab, Q (c, ab) := funext hTa
    rw [← hf]
    exact this
  have h3 : shannonEntropy (fun cb : C × B => ∑ a, Q (cb.1, (a, cb.2)))
      = shannonEntropy (fun c => ∑ ab, Q (c, ab))
        + condEntropy (fun cb : C × B => ∑ a, Q (cb.1, (a, cb.2))) := by
    have := shannonEntropy_eq_add_condEntropy hQb
    have hf : (fun c => ∑ b, ∑ a, Q (c, (a, b))) = fun c => ∑ ab, Q (c, ab) := funext hTb
    rw [← hf]
    exact this
  have hc : condEntropy Q ≤ condEntropy (fun ca : C × A => ∑ b, Q (ca.1, (ca.2, b)))
      + condEntropy (fun cb : C × B => ∑ a, Q (cb.1, (a, cb.2))) := by
    rw [condEntropy_eq_sum_mul_shannonEntropy, condEntropy_eq_sum_mul_shannonEntropy,
      condEntropy_eq_sum_mul_shannonEntropy, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun c _ => ?_
    show (∑ ab, Q (c, ab)) * shannonEntropy (fun ab => Q (c, ab) / ∑ ab', Q (c, ab'))
      ≤ (∑ a, ∑ b, Q (c, (a, b)))
          * shannonEntropy (fun a => (∑ b, Q (c, (a, b))) / ∑ a', ∑ b, Q (c, (a', b)))
        + (∑ b, ∑ a, Q (c, (a, b)))
          * shannonEntropy (fun b => (∑ a, Q (c, (a, b))) / ∑ b', ∑ a, Q (c, (a, b')))
    rw [hTa c, hTb c]
    rcases (Finset.sum_nonneg fun ab _ => hQ (c, ab) : (0 : ℝ) ≤ ∑ ab, Q (c, ab)).eq_or_lt
      with h0 | hpos
    · rw [← h0]; simp
    · have hR0 : ∀ ab, 0 ≤ Q (c, ab) / ∑ ab', Q (c, ab') := fun ab =>
        div_nonneg (hQ _) hpos.le
      have hR1 : ∑ ab, Q (c, ab) / ∑ ab', Q (c, ab') = 1 := by
        rw [← Finset.sum_div, div_self hpos.ne']
      have hsub := shannonEntropy_le_shannonEntropy_add_shannonEntropy hR0 hR1
      simp only [← Finset.sum_div] at hsub
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left hsub hpos.le
  linarith [h1, h2, h3, hc]

/-- Strong subadditivity for three functions of a common variable. -/
private theorem ssa_marg {X A B C : Type*} [Fintype X] [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] {P : X → ℝ} (hP : ∀ x, 0 ≤ P x)
    (c : X → C) (a : X → A) (b : X → B) :
    shannonEntropy (marg (fun x => (c x, (a x, b x))) P) + shannonEntropy (marg c P)
      ≤ shannonEntropy (marg (fun x => (c x, a x)) P)
        + shannonEntropy (marg (fun x => (c x, b x)) P) := by
  set Q := marg (fun x => (c x, (a x, b x))) P with hQ
  have hQ0 : ∀ q, 0 ≤ Q q := fun q => marg_nonneg hP _ q
  let E1 : C × (A × B) ≃ (C × A) × B :=
    { toFun := fun q => ((q.1, q.2.1), q.2.2), invFun := fun p => (p.1.1, (p.1.2, p.2)),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  let E2 : C × (A × B) ≃ (C × B) × A :=
    { toFun := fun q => ((q.1, q.2.2), q.2.1), invFun := fun p => (p.1.1, (p.2, p.1.2)),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have e1 : marg c P = fun c' => ∑ ab, Q (c', ab) :=
    calc marg c P = marg Prod.fst Q :=
          (marg_comp (fun x => (c x, (a x, b x))) Prod.fst P).symm
      _ = fun c' => ∑ ab, Q (c', ab) := marg_fst Q
  have e2 : marg (fun x => (c x, a x)) P = fun ca : C × A => ∑ b', Q (ca.1, (ca.2, b')) :=
    calc marg (fun x => (c x, a x)) P = marg (fun q => (E1 q).1) Q :=
          (marg_comp (fun x => (c x, (a x, b x))) (fun q => (E1 q).1) P).symm
      _ = fun ca : C × A => ∑ b', Q (ca.1, (ca.2, b')) := marg_via_equiv E1 Q
  have e3 : marg (fun x => (c x, b x)) P = fun cb : C × B => ∑ a', Q (cb.1, (a', cb.2)) :=
    calc marg (fun x => (c x, b x)) P = marg (fun q => (E2 q).1) Q :=
          (marg_comp (fun x => (c x, (a x, b x))) (fun q => (E2 q).1) P).symm
      _ = fun cb : C × B => ∑ a', Q (cb.1, (a', cb.2)) := marg_via_equiv E2 Q
  have h := ssa_sum hQ0
  rw [e1, e2, e3]
  exact h

/-- **Han's inequality.** For a joint probability law `P` of the coordinates of `x : ι → α`,
`(n - 1) H(X) ≤ ∑ᵢ H(X without coordinate i)`, where `n` is the number of coordinates and the
law of `X` without coordinate `i` is the marginal of `P` on `{j // j ≠ i} → α`. -/
theorem mul_shannonEntropy_le_sum {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    [DecidableEq α] {P : (ι → α) → ℝ} (hP0 : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1) :
    ((Fintype.card ι : ℝ) - 1) * shannonEntropy P
      ≤ ∑ i, shannonEntropy (fun y : {j // j ≠ i} → α =>
          ∑ x, if (fun j : {j // j ≠ i} => x j.1) = y then P x else 0) := by
  obtain ⟨e⟩ : Nonempty (ι ≃ Fin (Fintype.card ι)) := ⟨Fintype.equivFin ι⟩
  let F : ℕ → ℝ := fun k => shannonEntropy (marg (restr (fun j => (e j).val < k)) P)
  have hA : ∀ i, shannonEntropy P + F (e i).val
      ≤ F ((e i).val + 1) + shannonEntropy (marg (restr (fun j => j ≠ i)) P) := by
    intro i
    show shannonEntropy P + shannonEntropy (marg (restr (fun j => (e j).val < (e i).val)) P)
      ≤ shannonEntropy (marg (restr (fun j => (e j).val < (e i).val + 1)) P)
        + shannonEntropy (marg (restr (fun j => j ≠ i)) P)
    have h : shannonEntropy (marg (fun x : ι → α => (restr (fun j => (e j).val < (e i).val) x,
          (x i, restr (fun j => (e i).val < (e j).val) x))) P)
        + shannonEntropy (marg (restr (fun j => (e j).val < (e i).val)) P)
        ≤ shannonEntropy (marg (fun x : ι → α =>
            (restr (fun j => (e j).val < (e i).val) x, x i)) P)
          + shannonEntropy (marg (fun x : ι → α => (restr (fun j => (e j).val < (e i).val) x,
            restr (fun j => (e i).val < (e j).val) x)) P) :=
      ssa_marg hP0 (restr (fun j => (e j).val < (e i).val)) (fun x => x i)
        (restr (fun j => (e i).val < (e j).val))
    have h1 : shannonEntropy (marg (fun x : ι → α => (restr (fun j => (e j).val < (e i).val) x,
          (x i, restr (fun j => (e i).val < (e j).val) x))) P) = shannonEntropy P := by
      apply shannonEntropy_marg_of_injective
      intro x y hxy
      simp only [Prod.mk.injEq, restr_eq_iff] at hxy
      obtain ⟨ha, hb, hc⟩ := hxy
      funext j
      rcases lt_trichotomy (e j).val (e i).val with hj | hj | hj
      · exact ha j hj
      · rw [e.injective (Fin.ext hj)]; exact hb
      · exact hc j hj
    have h2 : shannonEntropy (marg (fun x : ι → α =>
          (restr (fun j => (e j).val < (e i).val) x, x i)) P)
        = shannonEntropy (marg (restr (fun j => (e j).val < (e i).val + 1)) P) := by
      refine shannonEntropy_marg_congr _ _ fun x x' => ?_
      simp only [Prod.mk.injEq, restr_eq_iff]
      constructor
      · rintro ⟨ha, hb⟩ j hj
        rcases (show (e j).val < (e i).val ∨ (e j).val = (e i).val by omega) with hl | hl
        · exact ha j hl
        · rw [e.injective (Fin.ext hl)]; exact hb
      · intro hall
        exact ⟨fun j hj => hall j (by omega), hall i (by omega)⟩
    have h3 : shannonEntropy (marg (fun x : ι → α => (restr (fun j => (e j).val < (e i).val) x,
          restr (fun j => (e i).val < (e j).val) x)) P)
        = shannonEntropy (marg (restr (fun j => j ≠ i)) P) := by
      refine shannonEntropy_marg_congr _ _ fun x x' => ?_
      simp only [Prod.mk.injEq, restr_eq_iff]
      constructor
      · rintro ⟨ha, hb⟩ j hj
        have hne : (e j).val ≠ (e i).val := fun hv => hj (e.injective (Fin.ext hv))
        rcases Nat.lt_or_gt_of_ne hne with hl | hl
        · exact ha j hl
        · exact hb j hl
      · intro hall
        exact ⟨fun j hj => hall j fun hji => by rw [hji] at hj; exact lt_irrefl _ hj,
          fun j hj => hall j fun hji => by rw [hji] at hj; exact lt_irrefl _ hj⟩
    linarith
  have hFn : F (Fintype.card ι) = shannonEntropy P :=
    shannonEntropy_marg_of_injective (f := restr (fun j => (e j).val < Fintype.card ι))
      (fun x y hxy => funext fun j => restr_eq_iff.mp hxy j (e j).isLt) P
  have hF0 : F 0 = 0 := by
    show shannonEntropy (marg (restr (fun j => (e j).val < 0)) P) = 0
    rw [shannonEntropy_marg]
    have hall : ∀ x : ι → α, (∑ x', if restr (fun j => (e j).val < 0) x'
        = restr (fun j => (e j).val < 0) x then P x' else 0) = 1 := by
      intro x
      rw [← hP1]
      exact Finset.sum_congr rfl fun x' _ =>
        if_pos (funext fun j => absurd j.2 (Nat.not_lt_zero _))
    simp only [hall, Real.log_one, mul_zero, Finset.sum_const_zero, neg_zero]
  have htel : ∑ i, (F ((e i).val + 1) - F (e i).val) = F (Fintype.card ι) - F 0 :=
    calc ∑ i, (F ((e i).val + 1) - F (e i).val)
        = ∑ k : Fin (Fintype.card ι), (F (k.val + 1) - F k.val) :=
          Equiv.sum_comp e (fun k : Fin (Fintype.card ι) => F (k.val + 1) - F k.val)
      _ = ∑ k ∈ Finset.range (Fintype.card ι), (F (k + 1) - F k) :=
          Fin.sum_univ_eq_sum_range (fun k => F (k + 1) - F k) _
      _ = F (Fintype.card ι) - F 0 := Finset.sum_range_sub F _
  rw [Finset.sum_sub_distrib] at htel
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hA i
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  have hD : (∑ i, shannonEntropy (fun y : {j // j ≠ i} → α =>
      ∑ x, if (fun j : {j // j ≠ i} => x j.1) = y then P x else 0))
      = ∑ i, shannonEntropy (marg (restr (fun j => j ≠ i)) P) := rfl
  rw [hD]
  linarith
