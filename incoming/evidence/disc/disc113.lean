import Mathlib

open scoped InnerProductSpace
open Finset

/-- Subgradient method: if `g n` is a subgradient of `f` at `x n` with `‖g n‖ ≤ G`, and
`x (n+1) = x n - η • g n`, then the best of the first `T` values `f (x n)` is within
`(‖x 0 - z‖² + η² G² T) / (2 η T)` of `f z`. -/
theorem min_sub_le_of_subgradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (x g : ℕ → E) (z : E) (η G : ℝ) (T : ℕ)
    (hη : 0 < η) (hT : 0 < T)
    (hsub : ∀ n y, f (x n) + ⟪g n, y - x n⟫_ℝ ≤ f y)
    (hg : ∀ n, ‖g n‖ ≤ G)
    (hstep : ∀ n, x (n + 1) = x n - η • g n) :
    (Finset.range T).inf' ⟨0, Finset.mem_range.mpr hT⟩ (fun n => f (x n)) - f z
      ≤ (‖x 0 - z‖ ^ 2 + η ^ 2 * G ^ 2 * T) / (2 * η * T) := by
  have key : ∀ n, 2 * η * (f (x n) - f z)
      ≤ ‖x n - z‖ ^ 2 - ‖x (n + 1) - z‖ ^ 2 + η ^ 2 * G ^ 2 := by
    intro n
    have h1 : x (n + 1) - z = x n - z - η • g n := by
      rw [hstep]; abel
    have h2 := norm_sub_sq_real (x n - z) (η • g n)
    rw [← h1, real_inner_smul_right] at h2
    have h5 : ‖η • g n‖ ^ 2 ≤ η ^ 2 * G ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      have hsq : ‖g n‖ ^ 2 ≤ G ^ 2 := by nlinarith [norm_nonneg (g n), hg n]
      exact mul_le_mul_of_nonneg_left hsq (sq_nonneg η)
    have h3 := hsub n z
    have h4 : ⟪g n, z - x n⟫_ℝ = -⟪x n - z, g n⟫_ℝ := by
      rw [inner_sub_right, inner_sub_left]
      linarith [real_inner_comm (x n) (g n), real_inner_comm z (g n)]
    have h6 : η * (f (x n) - f z) ≤ η * ⟪x n - z, g n⟫_ℝ :=
      mul_le_mul_of_nonneg_left (by linarith) hη.le
    linarith
  have hsum : ∀ N : ℕ, ∑ n ∈ range N, 2 * η * (f (x n) - f z)
      ≤ ‖x 0 - z‖ ^ 2 - ‖x N - z‖ ^ 2 + (N : ℝ) * (η ^ 2 * G ^ 2) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ]
      push_cast
      linarith [key N]
  set m := (Finset.range T).inf' ⟨0, Finset.mem_range.mpr hT⟩ (fun n => f (x n)) with hm_def
  have hle : ∑ n ∈ range T, 2 * η * (m - f z)
      ≤ ∑ n ∈ range T, 2 * η * (f (x n) - f z) := by
    apply sum_le_sum
    intro n hn
    have hmn : m ≤ f (x n) := Finset.inf'_le (fun n => f (x n)) hn
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  rw [sum_const, card_range, nsmul_eq_mul] at hle
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  rw [le_div_iff₀ (mul_pos (mul_pos two_pos hη) hT')]
  nlinarith [hsum T, sq_nonneg ‖x T - z‖, hle]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let cands : List (String × List Name) := [
    ("theorem", [`«theorem»]),
    ("min_sub_le_of_subgradient", [`«min_sub_le_of_subgradient»]),
    ("E", [`«E»]),
    ("Type", [`«Type»]),
    ("NormedAddCommGroup", [`«NormedAddCommGroup»]),
    ("InnerProductSpace", [`«InnerProductSpace»]),
    ("ℝ", [`«ℝ»]),
    ("f", [`«f»]),
    ("x", [`«x»]),
    ("g", [`«g»]),
    ("ℕ", [`«ℕ»]),
    ("z", [`«z»]),
    ("η", [`«η»]),
    ("G", [`«G»]),
    ("T", [`«T»]),
    ("hη", [`«hη»]),
    ("hT", [`«hT»]),
    ("hsub", [`«hsub»]),
    ("n", [`«n»]),
    ("y", [`«y»]),
    ("_ℝ", [`«_ℝ»]),
    ("hg", [`«hg»]),
    ("hstep", [`«hstep»]),
    ("Finset.range", [`«Finset».«range», `«Finset»]),
    ("inf'", [`«inf'»]),
    ("Finset.mem_range.mpr", [`«Finset».«mem_range».«mpr», `«Finset».«mem_range», `«Finset»]),
    ("fun", [`«fun»]),
    ("by", [`«by»]),
    ("have", [`«have»]),
    ("key", [`«key»]),
    ("intro", [`«intro»]),
    ("h1", [`«h1»]),
    ("rw", [`«rw»]),
    ("abel", [`«abel»]),
    ("h2", [`«h2»]),
    ("norm_sub_sq_real", [`«norm_sub_sq_real»]),
    ("real_inner_smul_right", [`«real_inner_smul_right»]),
    ("at", [`«at»]),
    ("h5", [`«h5»]),
    ("norm_smul", [`«norm_smul»]),
    ("mul_pow", [`«mul_pow»]),
    ("Real.norm_eq_abs", [`«Real».«norm_eq_abs», `«Real»]),
    ("sq_abs", [`«sq_abs»]),
    ("hsq", [`«hsq»]),
    ("nlinarith", [`«nlinarith»]),
    ("norm_nonneg", [`«norm_nonneg»]),
    ("exact", [`«exact»]),
    ("mul_le_mul_of_nonneg_left", [`«mul_le_mul_of_nonneg_left»]),
    ("sq_nonneg", [`«sq_nonneg»]),
    ("h3", [`«h3»]),
    ("h4", [`«h4»]),
    ("inner_sub_right", [`«inner_sub_right»]),
    ("inner_sub_left", [`«inner_sub_left»]),
    ("linarith", [`«linarith»]),
    ("real_inner_comm", [`«real_inner_comm»]),
    ("h6", [`«h6»]),
    ("hη.le", [`«hη».«le», `«hη»]),
    ("hsum", [`«hsum»]),
    ("N", [`«N»]),
    ("range", [`«range»]),
    ("induction", [`«induction»]),
    ("with", [`«with»]),
    ("zero", [`«zero»]),
    ("simp", [`«simp»]),
    ("succ", [`«succ»]),
    ("ih", [`«ih»]),
    ("sum_range_succ", [`«sum_range_succ»]),
    ("push_cast", [`«push_cast»]),
    ("set", [`«set»]),
    ("m", [`«m»]),
    ("hm_def", [`«hm_def»]),
    ("hle", [`«hle»]),
    ("apply", [`«apply»]),
    ("sum_le_sum", [`«sum_le_sum»]),
    ("hn", [`«hn»]),
    ("hmn", [`«hmn»]),
    ("Finset.inf'_le", [`«Finset».«inf'_le», `«Finset»]),
    ("sum_const", [`«sum_const»]),
    ("card_range", [`«card_range»]),
    ("nsmul_eq_mul", [`«nsmul_eq_mul»]),
    ("hT'", [`«hT'»]),
    ("exact_mod_cast", [`«exact_mod_cast»]),
    ("le_div_iff₀", [`«le_div_iff₀»]),
    ("mul_pos", [`«mul_pos»]),
    ("two_pos", [`«two_pos»])
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
