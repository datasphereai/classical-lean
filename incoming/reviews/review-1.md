# Order CLOUD-MATH-4, statement stage: cold review 1 (bridges 160, 162, 161)

Brief: `/root/cm4/review/brief.md`, sha256 `1767e9bd96f1ec68fefc6f709a4af0832e923f64823f95179f91c683aa014539`. It **matched** the sha256 I was given (`sha256sum`, and the brief's own `brief.sha256`). The three modules in section F are byte-identical to the untracked files on branch `cloud-math-4` (checked by script).

Method. I copied each module into `/root/cm4/review/scratch/` and ran `lake env lean` on it. All three elaborate, and the only warnings are the four expected `declaration uses sorry`, so all six witnesses check. I renamed each `example` to a `def` and ran `#check` on it: every witness elaborates to a closed proposition, not a function, so no explicit binder is left unsupplied. To test whether the statements can be proved, I wrote scratch proofs of my own:
* both 160 theorems, in full;
* both 162 theorems, in full;
* the 161 risk theorem, from the inverse moment.

All of these compile. Every Mathlib or library name cited in a docstring was checked with `#check`. No file in the repository was modified except this report.

## 1. `ClassicalLean.InformationTheory.HuffmanEntropy` (bridge 160)

**Main theorems.**
- `le_sum_mul_huffmanLength`: `shannonEntropy p / Real.log 2 ≤ ∑ i, p i * (huffmanLength p i : ℝ)` under `∀ i, 0 ≤ p i` and `∑ i, p i = 1`.
  - FAITHFUL to the order's table, which asks `p i ≥ 0` on this side.
  - GENERALIZED against the row, which asks `p i > 0` for both sides.
- `sum_mul_huffmanLength_lt`: `∑ i, p i * (huffmanLength p i : ℝ) < shannonEntropy p / Real.log 2 + 1` under `∀ i, 0 < p i` and `∑ i, p i = 1`. FAITHFUL to both the table and the row.
- The cast `ℕ → ℝ` on the lengths is the only choice Lean forced, and the module docstring states it.

**Hypotheses: fine.**
- `[Fintype ι] [DecidableEq ι]` are both required. `#check @huffmanLength` gives `{ι} → [DecidableEq ι] → [Fintype ι] → …`.
- `hp0` is needed: `huffman_optimal` and Shannon's bound ask `0 ≤ p i`, and `exists_isPrefixFree_sum_mul_length_lt` asks `0 < p i`. `hp1` is needed by both SourceCoding results.
- Nothing is missing. My scratch proofs follow the row exactly and compile:
  - lower side: `huffman_optimal (α := Bool)`, then `shannonEntropy_le_sum_mul_length_of_isPrefixFree`, then `div_le_iff₀ (Real.log_pos one_lt_two)`;
  - upper side: optimality against the Shannon code, then `linarith`.

**Witnesses.**
- `le_sum_mul_huffmanLength` witness: **PASS**.
  - Form: `example := Full.name (ι := Fin 3) (p := ![1/2, 1/3, 1/6]) h₁ h₂`, one inline block, no helper declaration, no `open` and no forbidden word. The docstring opens with "The hypotheses of `le_sum_mul_huffmanLength` hold together: …".
  - Arithmetic: 1/2 + 1/3 + 1/6 = 1, and every weight is positive.
  - Huffman's lengths are (1, 2, 2). I traced this through `huffAux`/`pick`/`mergeLen`. The first merge takes the two lightest, 1/6 and 1/3, which is unambiguous. The second merge joins the two remaining weights of 1/2 each, and either tie-break gives both nodes length 1.
  - Mean length: 1/2·1 + 1/3·2 + 1/6·2 = 3/2.
  - Entropy in bits: 1/2·1 + 1/3·log₂3 + 1/6·log₂6 = 1.4591…, so the docstring's "about 1.459" is right, and 1.459 < 1.5 makes the bound strict as claimed.
  - Not degenerate: three symbols, no zero weight, and the weights are not dyadic, so the bound is not an equality. The docstring says this.
- `sum_mul_huffmanLength_lt` witness: **PASS**.
  - Same form and same weights as above.
  - 1.459… < 3/2 < 2.459…, matching the docstring's values.
  - Not degenerate: the inequality is strict with room on both sides.

**Namespaces and imports.**
- Both theorems sit inside `namespace ClassicalLean.InformationTheory.HuffmanEntropy`, which equals the module name. The witnesses come after `end`.
- The only import is `ClassicalLean.InformationTheory.Huffman`, exactly as the table says, and there is no `import Mathlib`.
- The single `open Finset ClassicalLean.Simplex ClassicalLean.InformationTheory.Huffman` line sits after the import and before the namespace.

**Docstrings.**
- What is proved, the nats-to-bits division, the `ℕ → ℝ` cast and the proof sketch are all stated truthfully.
- Every name they mention exists: `ClassicalLean.Simplex.shannonEntropy`, `huffman_optimal`, `shannonEntropy_le_sum_mul_length_of_isPrefixFree` and `exists_isPrefixFree_sum_mul_length_lt`.
- One wording point, finding 1: the module docstring credits the `p i ≥ 0` widening to "this session's reading", but the order's table asks for it.

## 2. `ClassicalLean.Probability.PrincipalComponents` (bridge 162)

**Main theorems.**
- `tendsto_powerIterate_covLin`: **FAITHFUL.**
  - The symmetry proof is the library's `isSymmetric_covLin (X := X) (μ := μ)`. It is written inside the statement and is not a hypothesis. Its body (CovarianceDirections line 353) is exactly `(isSelfAdjoint_covOp …).isSymmetric`, the continuous-linear-map lemma the order names.
  - The dimension is `{n}` with `hn : Module.finrank ℝ (EuclideanSpace ℝ ι) = n`, and the indices are `⟨0, _⟩` and `⟨1, h2⟩`. That is Mathlib's order, largest first.
  - Hypotheses beyond `hX`: `h2 : 2 ≤ n`, `hgap : λ ⟨1,_⟩ < λ ⟨0,_⟩` and `hx : ⟪u, x⟫ ≠ 0`, with `x` a plain argument and `hn` the setup binder the order itself writes. These are exactly the hypotheses the order allows.
  - The conclusion is `tendsto_powerIterate`'s two conclusions with `T = covLin X μ`, `i₀ = ⟨0,_⟩` and `i₁ = ⟨1,_⟩`. The `∃ C` bound has ratio `λ ⟨1,_⟩ / λ ⟨0,_⟩` and no absolute values, and the limit is `u`.
  - The dominance hypothesis is derived, not assumed.
- `variance_mix_eigenvectorBasis_eq_and_le` (the order's "your name" slot): **FAITHFUL.** The hypotheses are only `hX` and `h0 : 0 < n`. The conclusion has the order's exact shape: `variance (mix X (WithLp.ofLp u)) μ = λ ⟨0,_⟩ ∧ ∀ w, ‖w‖ = 1 → variance (mix X (WithLp.ofLp w)) μ ≤ λ ⟨0,_⟩`.

**Hypotheses: fine.**
- The binders `[Fintype ι] [DecidableEq ι]` are required by `covOp` (`toEuclideanCLM`) and by `isSymmetric_covLin`.
- `[IsFiniteMeasure μ]` and `hX` are needed for `variance_mix_eq_of_hasEigenvector` and `reApplyInnerSelf_covOp`, and the order asks for them. There is no stray `[Nonempty ι]`: `0 < n` plays that role, as the order asks.
- `h2` and `h0` are what allow `⟨1,_⟩` and `⟨0,_⟩` to be written.
- I proved both theorems in scratch as stated, so nothing is missing:
  - Eigenvalue nonnegativity: `hasEigenvector_eigenvectorBasis` with `variance_mix_eq_of_hasEigenvector` and `variance_nonneg`.
  - Theorem 1: rewrite `|λ i| = λ i`, take dominance from `eigenvalues_antitone` (for `i ≠ 0`, `1 ≤ i`), apply `tendsto_powerIterate`, then `simpa only [abs_of_nonneg]`.
  - Theorem 2:
    - the equality is `variance_mix_eq_of_hasEigenvector`;
    - the bound applies `ClassicalLean.MinMax.sum_re_inner_le_sum_eigenvalues` at `k = 1` to the orthonormal family `fun _ : Fin 1 => w`;
    - `reApplyInnerSelf_covOp` turns the variance into the inner product the bound is about;
    - `Fin.castLE _ 0 = ⟨0, h0⟩` closes it.

**Witnesses.**
- `tendsto_powerIterate_covLin` witness: **PASS**.
  - Form: every chosen argument is given by name (`ι`, `Ω`, `μ`, `X`, `hn`, `h2`, `hgap`, `x`, `hx`) and `hX` is given positionally. Every explicit binder is supplied, and `#check` shows a closed proposition. `n` and `m0` are inferred, which follows PowerMethod's own witness (it does not name `n`).
  - It is one inline block. The `set`/`have` steps are local tactic steps, not declarations.
  - No forbidden word. `↓reduceIte` is an ordinary simp simproc, not in the `reduceBool` family, and is used elsewhere in the library.
  - No `open … in` line. The block relies only on the module's top-level opens, but see finding 2.
  - The docstring opens with "The hypotheses of … hold together: …" and has a "What moves:" sentence.
  - Arithmetic, under `μ = (1/4)·count` on the four points of `Fin 2 → Bool` (total mass 4·1/4 = 1, a probability):
    - `X 0 = ±2` according to `ω 0`, true on two points: mean (2+2−2−2)/4 = 0 and variance (4·4)/4 = 4.
    - `X 1 = ±1` according to `ω 1`: mean 0 and variance 1.
    - Covariance: E[X0·X1] = (2·1 + 2·(−1) + (−2)·1 + (−2)·(−1))/4 = 0.
    - So the covariance map is diag(4, 1), with Mathlib-ordered eigenvalues λ₀ = 4 > λ₁ = 1 > 0 and u = ±e₀.
    - With x = (1, 1), ⟪u, x⟫ = ±1 ≠ 0, and Tᵏx = (4ᵏ, 1).
    - The rescaled iterate is ±(1, 4⁻ᵏ), its distance to u is 4⁻ᵏ ≠ 0 at every k, and the rate is 1/4 ≠ 0.
  - Not degenerate: `ι = Fin 2` (the theorem forces n ≥ 2), Ω has 4 points, λ₁ ≠ 0, and the iterates move at every step and never reach u. This meets the moving-process case for a limit with no horizon, and the docstring says it.
- `variance_mix_eigenvectorBasis_eq_and_le` witness: **PASS**.
  - Same data and same form; `h0 := two_pos` with n = 2.
  - The covariance is diag(4, 1) as computed above.
  - Not degenerate: the variances 4 and 1 are distinct, so the bound is strict at w = e₁ (1 < 4) and `u` is the strict maximizer up to sign. The docstring's "two distinct variances, so the largest is a strict maximum" says what moves.

**Namespaces and imports.**
- Both theorems sit inside `namespace ClassicalLean.Probability.PrincipalComponents`, which equals the module name.
- The imports are exactly `ClassicalLean.Probability.CovarianceDirections` and `ClassicalLean.Analysis.PowerMethod`, with no `import Mathlib`.
- The `open` lines sit after the imports and before the namespace, including `open ClassicalLean.Probability.CovarianceDirections ClassicalLean.Analysis.PowerMethod`, the one that reaches other modules.
- The third top-level line, `open scoped NNReal`, serves only the witnesses (finding 2).

**Docstrings.** True, and they record the choices the order asks to be recorded:
- the dimension `n` with `hn`;
- the indices `⟨0,_⟩` and `⟨1,_⟩` in Mathlib's largest-first order, with `2 ≤ n` and `0 < n` as the hypotheses that make them writable;
- no absolute values in the rate;
- weights written `WithLp.ofLp w`.

The claim that `isSymmetric_covLin` is `isSelfAdjoint_covOp` turned into `IsSymmetric` by `IsSelfAdjoint.isSymmetric` is verified, and that Mathlib lemma exists at root with `{A : E →L[𝕜] E}`. Every name cited exists: `eigenvalues_antitone`, `variance_mix_eq_of_hasEigenvector`, `reApplyInnerSelf_covOp`, `variance_nonneg`, `ClassicalLean.MinMax.sum_re_inner_le_sum_eigenvalues` and `sum_eigenvalues_eq_iSup`. The proof sketch is the one I carried out.

## 3. `ClassicalLean.Statistics.JamesSteinRisk` (bridge 161)

**Main theorems.**
- `integral_inv_sqNorm_zero` (the order's "your name" slot): `∫ x, (sqNorm x)⁻¹ ∂normalVec d 0 = 1 / ((d : ℝ) - 2)` for `3 ≤ d`. **FAITHFUL.** The cast `ℕ → ℝ` is stated in the module docstring.
- `integral_sqNorm_jamesStein_zero`: `∫ x, sqNorm (jamesStein x) ∂normalVec d 0 = 2` for `3 ≤ d`. **FAITHFUL** to both the table and the row. The docstring records that the `- 0` of the risk at θ = 0 is dropped.

**Hypotheses: fine.**
- `hd : 3 ≤ d` is asked for by the order and the row, and is needed by `integral_sqNorm_jamesStein_sub_eq`.
- `hd` is also needed for the inverse moment at d ∈ {0, 1}: there the right side is −1/2 or −1, while the left side is ≥ 0.
- At d = 2 both identities happen to hold through Lean's junk values (`1/0 = 0`, a non-integrable function integrates to `0`, and `jamesStein = id`). That is no reason to widen beyond the order's `3 ≤ d`.
- There are no typeclass binders.
- Nothing is missing:
  - I proved the risk theorem from the inverse moment in scratch: `integral_sqNorm_jamesStein_sub_eq hd 0`, `sub_zero`, then `field_simp` and `ring` using `(d:ℝ) − 2 ≠ 0`.
  - The inverse moment follows the documented route through Mathlib names I checked: `iIndepFun_pi`, `measurePreserving_eval`, `hasLaw_sum_sq_gaussian` (needs `0 < d`) and `Real.integral_rpow_mul_exp_neg_mul_Ioi` with `Real.Gamma_add_one`.

**Witnesses.**
- `integral_inv_sqNorm_zero` witness: **PASS**.
  - Form: `example := Full.name (d := 4) (by norm_num)`, one inline block, no `open` and no forbidden word. The docstring opens correctly.
  - Arithmetic: d = 4 ≥ 3 and d − 2 = 2 ≠ 0. The value is 1/(4−2) = 1/2, which agrees with E[1/χ²₄] = (1/2)/(2−1) = 1/2.
  - d = 2 is indeed the boundary where the inverse moment is infinite (E[1/χ²₂] = ∞).
  - Not degenerate: the dimension is away from both the theorem's least value and the boundary, and the docstring says so.
- `integral_sqNorm_jamesStein_zero` witness: **PASS**.
  - Same form.
  - Risk 2 against `integral_sqNorm_sub`'s 4. At d = 2 the factor d − 2 vanishes and the estimator is X itself, as the docstring says.

**Namespaces and imports.**
- Both theorems sit inside `namespace ClassicalLean.Statistics.JamesSteinRisk`, which equals the module name.
- The imports are exactly `ClassicalLean.Statistics.JamesStein` and `ClassicalLean.Probability.ChiSquared`, with no `import Mathlib`.
- `open MeasureTheory ProbabilityTheory Set` and `open ClassicalLean.Statistics ClassicalLean.Probability.ChiSquared` sit after the imports and before the namespace.

**Docstrings.**
- What is proved, the treatment of θ = 0 and the `d` cast are stated truthfully.
- The gamma computation is right:
  - (rᵃ/Γ(a))·Γ(a−1)/rᵃ⁻¹ = r/(a−1), and at a = d/2, r = 1/2 this is 1/(d−2);
  - it is finite since a ≥ 3/2 > 1.
- Every cited name exists: `normalVec`, `integral_sqNorm_sub`, `iIndepFun_pi`, `measurePreserving_eval`, `ClassicalLean.Probability.ChiSquared.hasLaw_sum_sq_gaussian`, `Real.integral_rpow_mul_exp_neg_mul_Ioi`, `Real.Gamma_add_one` and `integral_sqNorm_jamesStein_sub_eq`.

## Findings

1. **MINOR** (HuffmanEntropy, module docstring, the "Wider than the row" paragraph). The sentence says the lower side was widened to `p i ≥ 0` "by this session's reading". The widening is what order CLOUD-MATH-4's own table asks for: "`… ≤ ∑ i, p i * huffmanLength p i` when every `p i ≥ 0`". So the docstring credits the choice to the wrong source. The statement itself is correct.
   - Fix: replace `Wider than the row, by this session's reading: the row asks every \`p i > 0\` for both sides; the lower side needs only \`p i ≥ 0\` (Shannon's bound allows zero weights), so it is stated with that.`
   - with `Wider than the row, as order CLOUD-MATH-4's table asks: the row asks every \`p i > 0\` for both sides; the lower side needs only \`p i ≥ 0\` (Shannon's bound allows zero weights), so it is stated with that.`
2. **MINOR** (PrincipalComponents, line 52). The top-level `open scoped NNReal` serves nothing in the module's statements, and the proofs I wrote did not need it. It exists only for the two witnesses' `(4⁻¹ : ℝ≥0)`. Rule 3 gives a witness its own `open … in` lines for exactly this purpose. The library's precedent (MaximalInequality's docstring, line 42) moved a file-level `open scoped NNReal` to an `open scoped NNReal in` line.
   - Fix:
     - delete line 52 (`open scoped NNReal`) and the blank line after it;
     - put `open scoped NNReal in` on a line of its own directly above each witness docstring: `/-- The hypotheses of \`tendsto_powerIterate_covLin\` …` and `/-- The hypotheses of \`variance_mix_eigenvectorBasis_eq_and_le\` …`.
   - I checked this in scratch (`/root/cm4/review/scratch/PC_fix.lean`): it elaborates with only the two expected `sorry` warnings.
   - Leave the line as it is if the proof stage turns out to use `ℝ≥0` in the module itself.

No BLOCKING findings: every statement is FAITHFUL to the order's table, or GENERALIZED against its row only where the table asks for it; no theorem is WEAKER; and all six witnesses PASS.

Overall: FINDINGS 2
