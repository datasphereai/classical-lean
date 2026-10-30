/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import ClassicalLean.Probability.GamblersRuin
import ClassicalLean.NumberTheory.LucasApparition

/-!
# The ruin chance and the divisibility of Lucas numbers

A `±1` walk from `0` with independent steps, each `+1` with chance `p = 1/(r + 1)` for a positive
whole number `r` (`p = 1/2, 1/3, 1/4, …`), reaches `a` before `-b` with chance `U b / U (a + b)`,
where `U = lucasU (1 + r) r` (item 95, `GamblersRuin.measureReal_hit_eq_lucasU`, since
`(1 - p) / p = r`). Order CLOUD-MATH-6, bridge 156 of `MATH-PLAN-library-2-bridges-2.md`.

* `measureReal_hit_eq_inv_iff_dvd` — for `b ≥ 1`, that chance is the reciprocal `1 / m` of a
  positive whole number `m` exactly when `b` divides `a`. At `p = 1/2` (`r = 1`) the chance is
  `b / (a + b)`.

The proof works with the integer sequence `U = lucasU (1 + r) r` over `ℤ` (`map_lucasU` for the cast
`ℤ → ℝ`): `U 0 = 0` and `U (n + 1) = U n + r ^ n`, so `U` is positive and strictly increasing from
`n = 1`; `1 + r` and `r` are coprime, so `gcd (U m, U n) = U (gcd m n)` (`lucasU_gcd`,
`NumberTheory.LucasApparition`). The chance is `1 / m` exactly when `U b ∣ U (a + b)`, exactly when
`U (gcd b (a + b)) = U b`, exactly when `gcd b (a + b) = b`, that is `b ∣ a`.

The witness at the end of the file is `GamblersRuin`'s biased walk (independent coins with three
equally likely faces, a step up when the coin shows `0`), with `r = 2` (`p = 1/3`), `a = 4` and
`b = 2`.
-/

open MeasureTheory ProbabilityTheory Filter
open ClassicalLean ClassicalLean.Probability.GamblersRuin

namespace ClassicalLean.Probability.RuinDivisibility

/-- **The ruin chance is the reciprocal of a whole number exactly when `b ∣ a`** (bridge 156).
For the `±1` walk from `0` with steps known by the next time and independent of the past (`hX`,
`hind`, `hpm`, as in `measureReal_hit_eq_lucasU`), each step `+1` with chance `1 / (r + 1)` for a
whole number `r ≥ 1`, and `b ≥ 1`: the chance of reaching `a` before `-b` is `1 / m` for some whole
number `m > 0` if and only if `b` divides `a`. -/
theorem measureReal_hit_eq_inv_iff_dvd {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {𝒢 : Filtration ℕ m0} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ)
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) {r : ℕ} (hr : 0 < r)
    (hp : ∀ n, μ.real {ω | X n ω = 1} = 1 / ((r : ℝ) + 1)) (a b : ℕ) (hb : 0 < b) :
    (∃ m : ℕ, 0 < m ∧
        μ.real {ω | ∃ n, walk X n ω = a ∧ ∀ k ≤ n, -(b : ℝ) < walk X k ω} = 1 / m) ↔
      b ∣ a := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hp0 : (0 : ℝ) < 1 / ((r : ℝ) + 1) := by positivity
  have hp1 : 1 / ((r : ℝ) + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have hrp : (1 - 1 / ((r : ℝ) + 1)) / (1 / ((r : ℝ) + 1)) = r := by
    field_simp; ring
  have hchance := measureReal_hit_eq_lucasU hX hind hpm hp0 hp1 hp a b
  rw [hrp] at hchance
  -- the integer sequence `U = lucasU (1 + r) r`
  set U : ℕ → ℤ := lucasU (1 + (r : ℤ)) r with hU
  have hcast : ∀ n, lucasU (1 + (r : ℝ)) (r : ℝ) n = (U n : ℝ) := fun n ↦ by
    have h := map_lucasU (Int.castRingHom ℝ) (1 + (r : ℤ)) (r : ℤ) n
    simp only [eq_intCast, Int.cast_add, Int.cast_one, Int.cast_natCast] at h
    exact h.symm
  rw [hcast, hcast] at hchance
  have hstep : ∀ n, U (n + 1) = U n + (r : ℤ) ^ n := by
    intro n
    induction n with
    | zero => simp [hU]
    | succ n ih =>
      have h2 : U (n + 2) = (1 + (r : ℤ)) * U (n + 1) - r * U n := lucasU_add_two _ _ n
      rw [h2, ih]
      ring
  have hmono : StrictMono U := strictMono_nat_of_lt_succ fun n ↦ by
    rw [hstep]
    have : (0 : ℤ) < (r : ℤ) ^ n := pow_pos (by exact_mod_cast hr) n
    linarith
  have hU0 : U 0 = 0 := by simp [hU]
  have hUnn : ∀ n, 0 ≤ U n := fun n ↦ hU0 ▸ hmono.monotone (Nat.zero_le n)
  have hu : 0 < U b := hU0 ▸ hmono hb
  have hv : 0 < U (a + b) := hU0 ▸ hmono (by omega)
  have huR : (0 : ℝ) < U b := by exact_mod_cast hu
  have hvR : (0 : ℝ) < U (a + b) := by exact_mod_cast hv
  rw [hchance]
  constructor
  · rintro ⟨m, hm, heq⟩
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    -- `U (a + b) = U b * m`, so `U b ∣ U (a + b)`
    have hmul : ((U (a + b) : ℤ) : ℝ) = ((U b * (m : ℤ) : ℤ) : ℝ) := by
      rw [div_eq_div_iff hvR.ne' hmR.ne'] at heq
      push_cast
      linarith
    have hdvd : U b ∣ U (a + b) := ⟨m, Int.cast_injective hmul⟩
    have hcop : IsCoprime (1 + (r : ℤ)) (r : ℤ) := ⟨1, -1, by ring⟩
    have hg := lucasU_gcd hcop b (a + b)
    rw [← hU] at hg
    have hgl : ((Int.gcd (U b) (U (a + b)) : ℕ) : ℤ) = U b := Int.gcd_eq_left hu.le hdvd
    have hgb : U (Nat.gcd b (a + b)) = U b := by
      rw [← Int.natAbs_of_nonneg (hUnn _), ← hg, hgl]
    have hgcd : Nat.gcd b (a + b) = b := hmono.injective hgb
    exact Nat.dvd_add_self_right.1 (Nat.gcd_eq_left_iff_dvd.1 hgcd)
  · intro hba
    obtain ⟨k, hk⟩ := lucasU_dvd_lucasU_of_dvd (1 + (r : ℤ)) (r : ℤ)
      (Nat.dvd_add_self_right.2 hba)
    rw [← hU] at hk
    have hk0 : 0 < k := by
      by_contra h
      have : U b * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu.le (not_lt.1 h)
      linarith
    refine ⟨k.toNat, by omega, ?_⟩
    have hkR : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hk0.le]
    rw [hkR, hk]
    push_cast
    field_simp

end ClassicalLean.Probability.RuinDivisibility

open MeasureTheory ProbabilityTheory in
/-- The hypotheses of `measureReal_hit_eq_inv_iff_dvd` hold together: a biased walk, on the space
of sequences `ℕ → Fin 3` of independent coins with three equally likely faces (Mathlib's
`Measure.infinitePi` of the uniform law on `Fin 3`), as in `GamblersRuin`'s witness of
`measureReal_hit_eq_lucasU`. The step `X n` is `+1` when coin `n + 1` shows `0` and `-1` otherwise,
so each step is `1` with chance `1/3 = 1 / (r + 1)` at `r = 2`; the filtration is the one the coins'
values generate (read as `±1`), so step `n` is known at time `n + 1` and independent of what time
`n` knows; every step moves the walk. The targets `a = 4` and `b = 2`: `b > 1` and `a > b`, so
neither side of the `↔` is a boundary case (here `b ∣ a`, and the chance is
`U 2 / U 6 = 3 / 63 = 1 / 21`, with `U = lucasU 3 2`, `U n = 2 ^ n - 1`). -/
example := ClassicalLean.Probability.RuinDivisibility.measureReal_hit_eq_inv_iff_dvd
  (Ω := ℕ → Fin 3)
  (μ := Measure.infinitePi fun _ ↦ uniformOn Set.univ)
  (𝒢 := Filtration.natural (fun i (ω : ℕ → Fin 3) ↦ if ω i = 0 then (1 : ℝ) else -1)
    fun i ↦ ((measurable_of_countable fun c : Fin 3 ↦ if c = 0 then (1 : ℝ) else -1).comp
      (measurable_pi_apply i)).stronglyMeasurable)
  (X := fun n ω ↦ if ω (n + 1) = 0 then 1 else -1)
  (fun n ↦ Filtration.stronglyAdapted_natural
    (u := fun i (ω : ℕ → Fin 3) ↦ if ω i = 0 then (1 : ℝ) else -1) _ (n + 1))
  (fun n ↦ (iIndepFun_infinitePi (P := fun _ : ℕ ↦ (uniformOn Set.univ : Measure (Fin 3)))
    (X := fun _ (c : Fin 3) ↦ if c = 0 then (1 : ℝ) else -1)
    fun _ ↦ measurable_of_countable _).indep_comap_natural_of_lt _ (Nat.lt_succ_self n))
  (fun n ω ↦ by split_ifs <;> simp) (r := 2) (by norm_num)
  (fun n ↦ by
    have hset : {ω : ℕ → Fin 3 | (if ω (n + 1) = 0 then (1 : ℝ) else -1) = 1} =
        (fun ω : ℕ → Fin 3 ↦ ω (n + 1)) ⁻¹' {0} := by
      ext ω
      by_cases h : ω (n + 1) = 0
      · simp [h]
      · norm_num [h]
    rw [hset, measureReal_def, ← Measure.map_apply (measurable_pi_apply (n + 1))
      (measurableSet_singleton 0), Measure.infinitePi_map_eval, uniformOn_univ]
    norm_num)
  (a := 4) (b := 2) (by norm_num)
