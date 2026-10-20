import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.ComplexMGF

open MeasureTheory ProbabilityTheory
open scoped Real Topology

/-- For a positive real `p`, complex powers split over the product `p * z`. -/
private lemma cpow_ofReal_mul_aux {p : ℝ} (hp : 0 < p) {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    ((p : ℂ) * z) ^ w = (p : ℂ) ^ w * z ^ w := by
  have hp' : (p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hp.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hp' hz), Complex.log_ofReal_mul hp hz,
    Complex.cpow_def_of_ne_zero hp', Complex.cpow_def_of_ne_zero hz, ← Complex.exp_add,
    ← Complex.ofReal_log hp.le, add_mul]

/-- Characteristic function of an image measure as an expectation. -/
private lemma charFun_map_eq_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {f : Ω → ℝ}
    (hf : Measurable f) (t : ℝ) :
    charFun (P.map f) t = ∫ ω, Complex.exp ((t : ℂ) * (f ω : ℂ) * Complex.I) ∂P := by
  have hc : Continuous fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) := by
    fun_prop
  rw [charFun_apply_real]
  exact integral_map hf.aemeasurable hc.aestronglyMeasurable

/-- Independence factorises the expectation of `exp(it(A+B))`. -/
private lemma integral_exp_add_of_indep_aux {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A B : Ω → ℝ} (hA : Measurable A) (hB : Measurable B)
    (h : IndepFun A B P) (t : ℝ) :
    ∫ ω, Complex.exp ((t : ℂ) * ((A ω + B ω : ℝ) : ℂ) * Complex.I) ∂P
      = (∫ ω, Complex.exp ((t : ℂ) * (A ω : ℂ) * Complex.I) ∂P)
        * ∫ ω, Complex.exp ((t : ℂ) * (B ω : ℂ) * Complex.I) ∂P := by
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hA.aemeasurable hB.aemeasurable).1 h
  have hc : Continuous fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) := by
    fun_prop
  have hc2 : Continuous fun p : ℝ × ℝ =>
      Complex.exp ((t : ℂ) * (p.1 : ℂ) * Complex.I)
        * Complex.exp ((t : ℂ) * (p.2 : ℂ) * Complex.I) := by fun_prop
  have hAB : Measurable fun ω => (A ω, B ω) := by fun_prop
  have h1 : ∫ ω, Complex.exp ((t : ℂ) * ((A ω + B ω : ℝ) : ℂ) * Complex.I) ∂P
      = ∫ p, Complex.exp ((t : ℂ) * (p.1 : ℂ) * Complex.I)
          * Complex.exp ((t : ℂ) * (p.2 : ℂ) * Complex.I) ∂(P.map (fun ω => (A ω, B ω))) := by
    rw [integral_map hAB.aemeasurable hc2.aestronglyMeasurable]
    congr 1
    funext ω
    dsimp only
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h1, hprod,
    integral_prod_mul (fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
      (fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)),
    integral_map hA.aemeasurable hc.aestronglyMeasurable,
    integral_map hB.aemeasurable hc.aestronglyMeasurable]

/-- The gamma law is a probability measure. -/
private lemma isProb_gamma_aux {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IsProbabilityMeasure (gammaMeasure a r) :=
  ⟨by rw [gammaMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_gammaPDF_eq_one ha hr]⟩

/-- The mgf of the gamma law at a real point `s` below the rate. The integral has the real
rate `r - s`, so Mathlib's real gamma integral applies. -/
private lemma mgf_gammaMeasure_aux {a r : ℝ} (ha : 0 < a) (hr : 0 < r) {s : ℝ} (hs : s < r) :
    mgf id (gammaMeasure a r) s = r ^ a * (1 / (r - s)) ^ a := by
  have hm : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hpt : ∀ x : ℝ, (gammaPDF a r x).toReal • Real.exp (s * x)
      = Set.indicator (Set.Ici 0) (fun x : ℝ => r ^ a / Real.Gamma a *
          (x ^ (a - 1) * Real.exp (-((r - s) * x)))) x := by
    intro x
    rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x), smul_eq_mul]
    by_cases hx : 0 ≤ x
    · rw [Set.indicator_of_mem (Set.mem_Ici.2 hx), gammaPDFReal, ite_eq_left hx]
      have he : Real.exp (-(r * x)) * Real.exp (s * x) = Real.exp (-((r - s) * x)) := by
        rw [← Real.exp_add]; congr 1; ring
      linear_combination (r ^ a / Real.Gamma a * x ^ (a - 1)) * he
    · rw [Set.indicator_of_notMem (fun h => hx (Set.mem_Ici.1 h)), gammaPDFReal, ite_eq_right hx]
      simp
  change ∫ x, Real.exp (s * x) ∂(gammaMeasure a r) = r ^ a * (1 / (r - s)) ^ a
  rw [gammaMeasure,
    integral_withDensity_eq_integral_toReal_smul hm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [hpt]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi ha (sub_pos.2 hs),
    mul_comm ((1 / (r - s)) ^ a), ← mul_assoc, div_mul_cancel₀ _ hG]

/-- Every real point below the rate lies in the gamma law's `integrableExpSet`. -/
private lemma Iio_subset_integrableExpSet_gamma_aux {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Set.Iio r ⊆ integrableExpSet id (gammaMeasure a r) := by
  intro s hs
  have hs' : s < r := hs
  have h : ∫ x, Real.exp (s * x) ∂(gammaMeasure a r) = r ^ a * (1 / (r - s)) ^ a :=
    mgf_gammaMeasure_aux ha hr hs'
  change Integrable (fun x => Real.exp (s * x)) (gammaMeasure a r)
  refine MeasureTheory.Integrable.of_integral_ne_zero ?_
  rw [h]
  exact (mul_pos (Real.rpow_pos_of_pos hr a)
    (Real.rpow_pos_of_pos (one_div_pos.2 (sub_pos.2 hs')) a)).ne'

/-- The complex mgf of the gamma law at a real point below the rate. -/
private lemma complexMGF_gammaMeasure_ofReal_aux {a r : ℝ} (ha : 0 < a) (hr : 0 < r) {s : ℝ}
    (hs : s < r) :
    complexMGF id (gammaMeasure a r) s = (r : ℂ) ^ (a : ℂ) * (1 / ((r : ℂ) - s)) ^ (a : ℂ) := by
  have hrs : (0 : ℝ) ≤ 1 / (r - s) := (one_div_pos.2 (sub_pos.2 hs)).le
  rw [complexMGF_ofReal, mgf_gammaMeasure_aux ha hr hs, Complex.ofReal_mul,
    Complex.ofReal_cpow hr.le, Complex.ofReal_cpow hrs]
  push_cast
  rfl

/-- The complex mgf of the gamma law on the half-plane `re z < r`. Both sides are analytic
there and agree at the real points, so they agree on the whole half-plane. -/
private lemma complexMGF_gammaMeasure_aux {a r : ℝ} (ha : 0 < a) (hr : 0 < r) {z : ℂ}
    (hz : z.re < r) :
    complexMGF id (gammaMeasure a r) z = (r : ℂ) ^ (a : ℂ) * (1 / ((r : ℂ) - z)) ^ (a : ℂ) := by
  have hU : IsPreconnected {w : ℂ | w.re < r} := (convex_halfSpace_re_lt r).isPreconnected
  have hf : AnalyticOnNhd ℂ (complexMGF id (gammaMeasure a r)) {w : ℂ | w.re < r} :=
    analyticOnNhd_complexMGF.mono fun w hw =>
      interior_maximal (Iio_subset_integrableExpSet_gamma_aux ha hr) isOpen_Iio hw
  have hg : AnalyticOnNhd ℂ (fun w : ℂ => (r : ℂ) ^ (a : ℂ) * (1 / ((r : ℂ) - w)) ^ (a : ℂ))
      {w : ℂ | w.re < r} := by
    intro w hw
    have hw' : w.re < r := hw
    have hre : 0 < ((r : ℂ) - w).re := by simpa using hw'
    have hne : (r : ℂ) - w ≠ 0 := by
      intro h
      rw [h, Complex.zero_re] at hre
      exact lt_irrefl _ hre
    have hslit : 1 / ((r : ℂ) - w) ∈ Complex.slitPlane := by
      refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
      rw [one_div, Complex.inv_re]
      exact div_pos hre (Complex.normSq_pos.2 hne)
    exact analyticAt_const.fun_mul
      ((analyticAt_const.fun_div (analyticAt_const.fun_sub analyticAt_id) hne).cpow
        analyticAt_const hslit)
  have h0 : ((0 : ℝ) : ℂ) ∈ {w : ℂ | w.re < r} := by simpa using hr
  have h_real : ∃ᶠ x : ℝ in 𝓝[≠] (0 : ℝ), complexMGF id (gammaMeasure a r) (x : ℂ)
      = (r : ℂ) ^ (a : ℂ) * (1 / ((r : ℂ) - (x : ℂ))) ^ (a : ℂ) := by
    refine Filter.Eventually.frequently ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr)] with x hx
    exact complexMGF_gammaMeasure_ofReal_aux ha hr hx
  have hfreq : ∃ᶠ w in 𝓝[≠] ((0 : ℝ) : ℂ), complexMGF id (gammaMeasure a r) w
      = (r : ℂ) ^ (a : ℂ) * (1 / ((r : ℂ) - w)) ^ (a : ℂ) := by
    rw [Filter.frequently_iff_seq_forall] at h_real ⊢
    obtain ⟨xs, hx_tendsto, hx_eq⟩ := h_real
    refine ⟨fun n => (xs n : ℂ), ?_, fun n => hx_eq n⟩
    rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
    constructor
    · rw [Filter.tendsto_ofReal_iff]
      exact hx_tendsto.1
    · simpa using hx_tendsto.2
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hU h0 hfreq hz

/-- Characteristic function of the gamma law. -/
private lemma charFun_gammaMeasure_aux {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (t : ℝ) :
    charFun (gammaMeasure a r) t
      = (r : ℂ) ^ (a : ℂ) * (1 / ((r : ℂ) - (t : ℂ) * Complex.I)) ^ (a : ℂ) := by
  have hz : ((t : ℂ) * Complex.I).re < r := by simpa using hr
  have h := complexMGF_gammaMeasure_aux ha hr hz
  rwa [complexMGF_mul_I aemeasurable_id, Measure.map_id] at h

/-- Algebraic identity relating the Gaussian integral to the gamma formula. -/
private lemma sq_gauss_alg_aux (b : ℂ) (hb : b ≠ 0) :
    (((Real.sqrt (2 * π))⁻¹ : ℝ) : ℂ) * ((π : ℂ) / b) ^ (1 / 2 : ℂ)
      = ((1 / 2 : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ) * (1 / b) ^ ((1 / 2 : ℝ) : ℂ) := by
  have h12 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have h12' : ((1 / 2 : ℝ) : ℂ) ≠ 0 := by norm_num
  have hb' : (1 / b) ≠ 0 := one_div_ne_zero hb
  have hsplit : (π : ℂ) / b = ((2 * π : ℝ) : ℂ) * (((1 / 2 : ℝ) : ℂ) * (1 / b)) := by
    push_cast; ring
  have hsq : ((2 * π : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ) = ((Real.sqrt (2 * π) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ 2 * π)]
  have hs0 : ((Real.sqrt (2 * π) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (by positivity)
  rw [h12, hsplit, cpow_ofReal_mul_aux (p := 2 * π) (by positivity) (mul_ne_zero h12' hb'),
    cpow_ofReal_mul_aux (p := 1 / 2) (by norm_num) hb', hsq, Complex.ofReal_inv,
    ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]

/-- The square of a standard normal has the gamma law with shape and rate `1/2`
(at the level of characteristic functions). -/
private lemma charFun_sq_gaussian_aux (t : ℝ) :
    charFun ((gaussianReal 0 1).map (fun x : ℝ => x ^ 2)) t
      = charFun (gammaMeasure (1 / 2) (1 / 2)) t := by
  have hb : ((1 / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hpt : ∀ x : ℝ,
      gaussianPDFReal 0 1 x • Complex.exp ((t : ℂ) * ((x ^ 2 : ℝ) : ℂ) * Complex.I)
        = (((Real.sqrt (2 * π))⁻¹ : ℝ) : ℂ)
          * Complex.exp (-(((1 / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I) * (x : ℂ) ^ 2) := by
    intro x
    rw [gaussianPDFReal]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    rw [Complex.real_smul, Complex.ofReal_mul, mul_assoc, Complex.ofReal_exp,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [charFun_map_eq_aux _ (by fun_prop : Measurable fun x : ℝ => x ^ 2) t,
    charFun_gammaMeasure_aux (a := 1 / 2) (r := 1 / 2) (by norm_num) (by norm_num),
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  refine (integral_congr_ae (ae_of_all _ hpt)).trans ?_
  rw [integral_const_mul, integral_gaussian_complex (by norm_num)]
  exact sq_gauss_alg_aux _ hb

/-- Expectation of `exp(itY²)` for a standard normal `Y`. -/
private lemma integral_sq_eq_aux {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → ℝ} (hY : Measurable Y) (hlaw : HasLaw Y (gaussianReal 0 1) P) (t : ℝ) :
    ∫ ω, Complex.exp ((t : ℂ) * ((Y ω ^ 2 : ℝ) : ℂ) * Complex.I) ∂P
      = charFun (gammaMeasure (1 / 2) (1 / 2)) t := by
  have hc : Continuous fun x : ℝ =>
      Complex.exp ((t : ℂ) * ((x ^ 2 : ℝ) : ℂ) * Complex.I) := by fun_prop
  rw [← charFun_sq_gaussian_aux t,
    charFun_map_eq_aux _ (by fun_prop : Measurable fun x : ℝ => x ^ 2) t,
    ← hlaw.map_eq, integral_map hY.aemeasurable hc.aestronglyMeasurable]

/-- The chi-squared law: the sum of squares of `k ≥ 1` independent standard normal
random variables has the gamma law with shape `k/2` and rate `1/2`. -/
theorem hasLaw_sum_sq_gaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {k : ℕ} (hk : 0 < k) {X : Fin k → Ω → ℝ}
    (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) :
    HasLaw (fun ω => ∑ i, X i ω ^ 2) (gammaMeasure ((k : ℝ) / 2) (1 / 2)) P := by
  have hindY : iIndepFun (fun j ω => X j ω ^ 2) P :=
    hind.comp (fun _ x => x ^ 2) (fun _ => measurable_id.pow_const 2)
  have key : ∀ (s : Finset (Fin k)) (t : ℝ),
      ∫ ω, Complex.exp ((t : ℂ) * ((∑ j ∈ s, X j ω ^ 2 : ℝ) : ℂ) * Complex.I) ∂P
        = charFun (gammaMeasure (1 / 2) (1 / 2)) t ^ s.card := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro t
      simp
    · intro i s hi ih t
      have h2 := hindY.indepFun_finsetSum_of_notMem (fun j => (hmeas j).pow_const 2) hi
      have h3 : IndepFun (fun ω => ∑ j ∈ s, X j ω ^ 2) (fun ω => X i ω ^ 2) P := by
        convert h2 using 1
        all_goals (funext ω; simp [Finset.sum_apply])
      simp only [Finset.sum_insert hi]
      rw [integral_exp_add_of_indep_aux ((hmeas i).pow_const 2)
          (Finset.measurable_sum s fun j _ => (hmeas j).pow_const 2) h3.symm t,
        ih, integral_sq_eq_aux (hmeas i) (hlaw i) t, Finset.card_insert_of_notMem hi]
      ring
  have hmeasSum : Measurable fun ω => ∑ i, X i ω ^ 2 :=
    Finset.measurable_sum _ fun j _ => (hmeas j).pow_const 2
  have hpos : (0 : ℝ) < (k : ℝ) / 2 := div_pos (Nat.cast_pos.2 hk) two_pos
  have := isProb_gamma_aux hpos (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨hmeasSum.aemeasurable, ?_⟩
  apply Measure.ext_of_charFun
  funext t
  have hc : (((k : ℝ) / 2 : ℝ) : ℂ) = (k : ℂ) * ((1 / 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [charFun_map_eq_aux P hmeasSum t, key Finset.univ t, Finset.card_univ, Fintype.card_fin,
    charFun_gammaMeasure_aux (a := 1 / 2) (r := 1 / 2) (by norm_num) (by norm_num),
    charFun_gammaMeasure_aux (a := (k : ℝ) / 2) (r := 1 / 2) hpos (by norm_num),
    hc, Complex.cpow_nat_mul, Complex.cpow_nat_mul, mul_pow]

/-! Satisfiability check by claude-ai (2026-10-13), not part of the draft: the
hypotheses of `hasLaw_sum_sq_gaussian` hold for the coordinates of the product of
`k` standard normal laws. -/
example (k : ℕ) (hk : 0 < k) :
    HasLaw (fun ω : Fin k → ℝ => ∑ i, ω i ^ 2) (gammaMeasure ((k : ℝ) / 2) (1 / 2))
      (Measure.pi fun _ => gaussianReal 0 1) :=
  hasLaw_sum_sq_gaussian hk (fun i => measurable_pi_apply i)
    (iIndepFun_pi (fun _ => aemeasurable_id))
    (fun i => ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩)

