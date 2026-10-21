import Mathlib

open MeasureTheory ProbabilityTheory

private lemma exp_le_quad_of_nonpos {y : ℝ} (hy : y ≤ 0) :
    Real.exp y ≤ 1 + y + y ^ 2 / 2 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => 1 + x + x * x / 2 - Real.exp x)
      (1 + x - Real.exp x) x := by
    intro x
    have h1 := (((hasDerivAt_const x (1:ℝ)).add (hasDerivAt_id' x)).add
      (((hasDerivAt_id' x).mul (hasDerivAt_id' x)).div_const 2)).sub (Real.hasDerivAt_exp x)
    first
    | exact h1.congr_deriv (by ring)
    | (convert h1 using 1; ring)
  have hanti : Antitone (fun x : ℝ => 1 + x + x * x / 2 - Real.exp x) :=
    antitone_of_deriv_nonpos (fun x => (hd x).differentiableAt)
      (fun x => by rw [(hd x).deriv]; linarith [Real.add_one_le_exp x])
  have h := hanti hy
  simp only [Real.exp_zero] at h
  nlinarith [h]

private lemma exp_mul_three_sub_le {y : ℝ} (hy : 0 ≤ y) :
    Real.exp y * (3 - y) ≤ 3 + 2 * y + y * y / 2 := by
  have hd : ∀ x : ℝ, HasDerivAt
      (fun y => Real.exp (-y) * (3 + 2 * y + y * y / 2) + y - 3)
      (1 - Real.exp (-x) * (1 + x + x * x / 2)) x := by
    intro x
    have h1 := ((((hasDerivAt_id' x).neg.exp).mul
      (((hasDerivAt_const x (3:ℝ)).add ((hasDerivAt_id' x).const_mul 2)).add
        (((hasDerivAt_id' x).mul (hasDerivAt_id' x)).div_const 2))).add
      (hasDerivAt_id' x)).sub (hasDerivAt_const x (3:ℝ))
    convert h1 using 1
    simp only [Pi.add_apply, Pi.neg_apply, Pi.mul_apply]
    ring
  have hdiff : Differentiable ℝ
      (fun y => Real.exp (-y) * (3 + 2 * y + y * y / 2) + y - 3) :=
    fun x => (hd x).differentiableAt
  have hmono : MonotoneOn (fun y => Real.exp (-y) * (3 + 2 * y + y * y / 2) + y - 3)
      (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hdiff.continuous.continuousOn
      hdiff.differentiableOn ?_
    intro x hx
    rw [interior_Ici] at hx
    have hx' : 0 < x := hx
    rw [(hd x).deriv]
    have q := Real.quadratic_le_exp_of_nonneg hx'.le
    have he : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    have q' : 1 + x + x * x / 2 ≤ Real.exp x := by nlinarith [q]
    have q2 := mul_le_mul_of_nonneg_left q' (Real.exp_pos (-x)).le
    linarith
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy) hy
  simp only [neg_zero, Real.exp_zero] at h
  have key : 3 - y ≤ Real.exp (-y) * (3 + 2 * y + y * y / 2) := by linarith
  have he : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
  calc Real.exp y * (3 - y) ≤ Real.exp y * (Real.exp (-y) * (3 + 2 * y + y * y / 2)) :=
        mul_le_mul_of_nonneg_left key (Real.exp_pos y).le
    _ = 3 + 2 * y + y * y / 2 := by rw [← mul_assoc, he, one_mul]

private lemma exp_le_bernstein {y c : ℝ} (hc0 : 0 ≤ c) (hc3 : c < 3) (hy : y ≤ c) :
    Real.exp y ≤ 1 + y + y ^ 2 / (2 * (1 - c / 3)) := by
  have hD : 0 < 2 * (1 - c / 3) := by linarith
  rcases le_total y 0 with hy0 | hy0
  · have hA := exp_le_quad_of_nonpos hy0
    have hq : y ^ 2 / 2 ≤ y ^ 2 / (2 * (1 - c / 3)) := by
      rw [le_div_iff₀ hD]
      nlinarith [mul_nonneg (sq_nonneg y) hc0]
    linarith
  · have hB := exp_mul_three_sub_le hy0
    have h1 : 0 ≤ Real.exp y - 1 - y := by linarith [Real.add_one_le_exp y]
    have hq : Real.exp y - 1 - y ≤ y ^ 2 / (2 * (1 - c / 3)) := by
      rw [le_div_iff₀ hD]
      nlinarith [mul_nonneg h1 (sub_nonneg.mpr hy)]
    linarith

private lemma exp_mul_le_quad {l b x : ℝ} (hl : 0 ≤ l) (hb0 : 0 ≤ b) (hlb : l * b < 3)
    (hx : x ≤ b) :
    Real.exp (l * x) ≤ 1 + l * x + l ^ 2 / (2 * (1 - l * b / 3)) * x ^ 2 := by
  have key := exp_le_bernstein (y := l * x) (c := l * b) (mul_nonneg hl hb0) hlb
    (mul_le_mul_of_nonneg_left hx hl)
  have e : (l * x) ^ 2 / (2 * (1 - l * b / 3)) = l ^ 2 / (2 * (1 - l * b / 3)) * x ^ 2 := by
    ring
  rw [e] at key
  exact key

private lemma prod_le_prod_aux {ι : Type*} (f g : ι → ℝ) :
    ∀ t : Finset ι, (∀ i ∈ t, 0 ≤ f i) → (∀ i ∈ t, f i ≤ g i) →
      ∏ i ∈ t, f i ≤ ∏ i ∈ t, g i := by
  classical
  intro t
  refine Finset.induction_on t ?_ ?_
  · intro _ _; simp
  · intro a t ha ih h0 h1
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    apply mul_le_mul (h1 a (Finset.mem_insert_self a t))
      (ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => h1 i (Finset.mem_insert_of_mem hi)))
    · exact Finset.prod_nonneg (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
    · exact (h0 a (Finset.mem_insert_self a t)).trans (h1 a (Finset.mem_insert_self a t))

theorem measureReal_sum_ge_le_bernstein {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ι → Ω → ℝ} (s : Finset ι)
    (hind : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hint : ∀ i ∈ s, Integrable (X i) μ)
    (hint2 : ∀ i ∈ s, Integrable (fun ω => X i ω ^ 2) μ)
    (hmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) {b v t : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ≤ b)
    (hv : ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ ≤ v) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i ∈ s, X i ω} ≤ Real.exp (-t ^ 2 / (2 * (v + b * t / 3))) := by
  have hgen : ∀ l : ℝ, 0 ≤ l → l * b < 3 →
      μ.real {ω | t ≤ ∑ i ∈ s, X i ω} ≤
        Real.exp (-l * t + l ^ 2 / (2 * (1 - l * b / 3)) * v) := by
    intro l hl hlb
    obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = l ^ 2 / (2 * (1 - l * b / 3)) := ⟨_, rfl⟩
    rw [← hκ]
    have hκ0 : 0 ≤ κ := by
      rw [hκ]; exact div_nonneg (sq_nonneg l) (by linarith)
    have hexpint : ∀ i ∈ s, Integrable (fun ω => Real.exp (l * X i ω)) μ := by
      intro i hi
      refine Integrable.mono' (integrable_const (Real.exp (l * b))) ?_ ?_
      · exact (Real.measurable_exp.comp ((hmeas i).const_mul l)).aestronglyMeasurable
      · filter_upwards [hb i hi] with ω hω
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω hl)
    have hmgf : ∀ i ∈ s, mgf (X i) μ l ≤ Real.exp (κ * ∫ ω, X i ω ^ 2 ∂μ) := by
      intro i hi
      have hA : Integrable (fun ω => (1:ℝ) + l * X i ω) μ :=
        (integrable_const (1:ℝ)).add ((hint i hi).const_mul l)
      have hB : Integrable (fun ω => κ * X i ω ^ 2) μ := (hint2 i hi).const_mul κ
      have hbd_int : Integrable (fun ω => 1 + l * X i ω + κ * X i ω ^ 2) μ := hA.add hB
      have hle : mgf (X i) μ l ≤ ∫ ω, (1 + l * X i ω + κ * X i ω ^ 2) ∂μ := by
        show ∫ ω, Real.exp (l * X i ω) ∂μ ≤ _
        refine integral_mono_ae (hexpint i hi) hbd_int ?_
        filter_upwards [hb i hi] with ω hω
        rw [hκ]
        exact exp_mul_le_quad hl hb0 hlb hω
      have hcalc : ∫ ω, (1 + l * X i ω + κ * X i ω ^ 2) ∂μ
          = 1 + κ * ∫ ω, X i ω ^ 2 ∂μ := by
        rw [integral_add hA hB, integral_add (integrable_const (1:ℝ)) ((hint i hi).const_mul l),
          integral_const_mul, integral_const_mul, hmean i hi]
        simp
      rw [hcalc] at hle
      linarith [Real.add_one_le_exp (κ * ∫ ω, X i ω ^ 2 ∂μ)]
    have hsum : mgf (∑ i ∈ s, X i) μ l = ∏ i ∈ s, mgf (X i) μ l := by
      first
      | exact hind.mgf_sum hmeas s
      | exact hind.mgf_sum (fun i => (hmeas i).aemeasurable) s
      | exact hind.mgf_sum hmeas
      | exact hind.mgf_sum (fun i => (hmeas i).aemeasurable)
    have hprod : mgf (∑ i ∈ s, X i) μ l ≤ Real.exp (κ * v) := by
      rw [hsum]
      calc ∏ i ∈ s, mgf (X i) μ l ≤ ∏ i ∈ s, Real.exp (κ * ∫ ω, X i ω ^ 2 ∂μ) :=
            prod_le_prod_aux _ _ s (fun i _ => mgf_nonneg) hmgf
        _ = Real.exp (κ * ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ) := by
            rw [Finset.mul_sum, Real.exp_sum]
        _ ≤ Real.exp (κ * v) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hv hκ0)
    have hSmeas : Measurable (∑ i ∈ s, X i) := by
      first
      | exact Finset.measurable_sum' s (fun i _ => hmeas i)
      | exact Finset.measurable_sum s (fun i _ => hmeas i)
      | fun_prop
    have hall : ∀ᵐ ω ∂μ, ∀ i ∈ s, X i ω ≤ b := by
      first
      | exact (Filter.eventually_all_finset s).mpr hb
      | exact Filter.eventually_all_finset.mpr hb
    have hSint : Integrable (fun ω => Real.exp (l * (∑ i ∈ s, X i) ω)) μ := by
      refine Integrable.mono' (integrable_const (Real.exp (l * (s.card * b)))) ?_ ?_
      · exact (Real.measurable_exp.comp (hSmeas.const_mul l)).aestronglyMeasurable
      · filter_upwards [hall] with ω hω
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hl)
        rw [Finset.sum_apply]
        calc ∑ i ∈ s, X i ω ≤ ∑ i ∈ s, b := Finset.sum_le_sum hω
          _ = s.card * b := by rw [Finset.sum_const, nsmul_eq_mul]
    have hmarkov : μ.real {ω | t ≤ (∑ i ∈ s, X i) ω} ≤
        Real.exp (-l * t) * mgf (∑ i ∈ s, X i) μ l := by
      first
      | exact measure_ge_le_exp_mul_mgf t hl hSint
      | exact (by simpa [Measure.real] using measure_ge_le_exp_mul_mgf t hl hSint)
    have hset : {ω | t ≤ (∑ i ∈ s, X i) ω} = {ω | t ≤ ∑ i ∈ s, X i ω} := by
      ext ω; simp [Finset.sum_apply]
    rw [hset] at hmarkov
    calc μ.real {ω | t ≤ ∑ i ∈ s, X i ω}
        ≤ Real.exp (-l * t) * mgf (∑ i ∈ s, X i) μ l := hmarkov
      _ ≤ Real.exp (-l * t) * Real.exp (κ * v) :=
          mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
      _ = Real.exp (-l * t + κ * v) := (Real.exp_add _ _).symm
  have hv0 : 0 ≤ v :=
    le_trans (Finset.sum_nonneg fun i _ => integral_nonneg fun ω => sq_nonneg (X i ω)) hv
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · refine (hgen 0 le_rfl (by norm_num)).trans (le_of_eq ?_)
    rw [← ht0]; simp
  by_cases hDpos : 0 < v + b * t / 3
  swap
  · push_neg at hDpos
    refine (hgen 0 le_rfl (by norm_num)).trans (Real.exp_le_exp.mpr ?_)
    have h1 : 0 ≤ -t ^ 2 / (2 * (v + b * t / 3)) := by
      first
      | exact div_nonneg_of_nonpos (by nlinarith) (by linarith)
      | (rw [div_nonneg_iff]; right; exact ⟨by nlinarith, by linarith⟩)
    have h2 : -0 * t + (0:ℝ) ^ 2 / (2 * (1 - 0 * b / 3)) * v = 0 := by simp
    linarith
  rcases eq_or_lt_of_le hv0 with hv00 | hvpos
  · have hl : 0 ≤ t / (2 * (v + b * t / 3)) := div_nonneg ht (by linarith)
    have hlb : t / (2 * (v + b * t / 3)) * b < 3 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    refine (hgen _ hl hlb).trans (le_of_eq (congrArg Real.exp ?_))
    rw [← hv00]
    ring
  · obtain ⟨D, hD⟩ : ∃ D, D = v + b * t / 3 := ⟨_, rfl⟩
    rw [← hD] at hDpos ⊢
    have hDne : D ≠ 0 := hDpos.ne'
    have hvne : v ≠ 0 := hvpos.ne'
    have hl : 0 ≤ t / D := div_nonneg ht hDpos.le
    have hlb : t / D * b < 3 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hDpos]
      nlinarith
    refine (hgen _ hl hlb).trans (le_of_eq (congrArg Real.exp ?_))
    have h1 : 1 - t / D * b / 3 = v / D := by
      rw [eq_div_iff hDne]
      have hq : t / D * D = t := div_mul_cancel₀ t hDne
      linear_combination (-b / 3) * hq + hD
    rw [h1]
    first
    | (field_simp; ring)
    | field_simp

set_option pp.fullNames true in
#check @measureReal_sum_ge_le_bernstein
