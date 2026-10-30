# Cold review 1, order CLOUD-MATH-5, statement stage

- Reviewed: the five new modules as they stand (statements final, proofs `sorry`, witnesses complete):
  `ClassicalLean/Probability/HolmInsideStepUp.lean` (158), `ClassicalLean/Probability/CorrelationBound.lean` (155),
  `ClassicalLean/Statistics/PinskerTest.lean` (164), `ClassicalLean/Analysis/HeunRichardson.lean` (166),
  `ClassicalLean/Analysis/HeunEulerMaclaurin.lean` (167).
- Brief: `/root/cm5/review/brief.md`, sha256 `cc678ae580087b33d7049b9f2c69a262886f2419ea5b6eada346bebb1bf45572`
  (checked with `sha256sum`; it matches). Every module in the repository is byte-identical to its copy in the brief's section 6.
- The reviewer had not seen this work before. No file in the repository was changed and no git command that changes anything was run.
- What I ran. All scratch files are under `/root/cm5/review/scratch/`:
  - `s<bridge>.lean`: a copy of each module with `#check @…` and `pp.fullNames`/`pp.numericTypes`/`pp.parens`/`pp.explicit` lines, to see how each statement parses and which constants it names.
  - `pa_<Module>.lean`: each witness term re-elaborated under `#check`. Every one has a non-`∀` type, so it is fully applied.
  - `opt_<Module>.lean`: each module elaborated with the package's `[leanOptions]` from `lakefile.toml`.
  - `inst.lean`: instance search for 155's measure, and a check of the name `ProbabilityTheory.correlation`.
  - `tools/witness_gate.py` on the five modules, run with `TMPDIR` and `--keep` set to the scratch folder. Result: all 7 blocks `BROKEN` only through `sorryAx`, which is expected at this stage; `copy-error=0`, `lines=7/7`, `keywords=7/7`, no `WRONG-NAME`, `NO-DOCSTRING` or `UNREAD`.
  - Exact-fraction Python for every numeric claim (`checks.py`, `c158.py` in the session scratchpad).

---

## Bridge 158: `HolmInsideStepUp`

### Statement
`le_mul_numRej_div_of_holmRejected {ι} [Fintype ι] {q : ℝ} (hq : 0 ≤ q) {x : ι → ℝ} {i : ι} (h : holmRejected q x i) : x i ≤ q * numRej q x / Fintype.card ι`

**FAITHFUL.** Elaborated (`pp.explicit`), the statement is `x i ≤ q * ↑(numRej q x) / ↑(Fintype.card ι)`, with both ℕ→ℝ casts on the atoms. It uses the same `holmRejected` and `numRej` constants with the same instance, and it is word for word the threshold of `numRej_update_eq_of_le`. The name matches the table and the row, and so do the binders (`[Fintype ι]`, `q ≥ 0`, `x`, `i`, `holmRejected q x i`).

### Hypotheses
- `hq : 0 ≤ q` is **needed**. Counterexample without it, found by hand and checked exactly: `m = 6`, `q = -1`, `x = (-1, -1, -1, -2/5, 5, 5)`, `i = 3`.
  - Holm rejects `i`. The thresholds for the tied `-1`s are `-1/6`, and for `x 3` it is `-1/3` (`-2/5 ≤ -1/3`).
  - `numRej = 3`, because `countLE x (-1/2) = 3`, but `countLE x (-2/3) = 3 < 4`.
  - The conclusion `-2/5 ≤ -1/2` is false.
  - A brute force over `m ≤ 3` (61390 Holm rejections, `q` from `-2` to `1`) found nothing. That is expected: the failure needs `m ≥ r(m − r)`, which first breaks at `m ≥ 5`.
- `h` is needed, since it is the premise.
- Nothing is extra.

### Witness (`ι = Fin 3`, `q = 1/10`, `x = (1/100, 1/50, 9/10)`, `i = 1`)
- **Form.** Every chosen argument is given by name (`ι q x i`). `[Fintype]` is found by instance search. `hq` and `h` are supplied. There is one inline block, no `open`, no forbidden word, and no `decide`: the cards go through `Finset.card_filter` and `Fin.sum_univ_three`, as asked. The docstring begins correctly.
- **Arithmetic, all checked and right.**
  - `c_j = #{l : x j ≤ x l} = (3, 2, 1)`.
  - Holm's thresholds are `q/c_j = 1/30, 1/20, 1/10`.
  - `x 0 = 1/100 ≤ 1/30` and `x 1 = 1/50 ≤ 1/20`. `x 2 = 9/10` is not at most `x 1`.
  - `holmRejected` holds for `i = 1` (and `i = 0`) but not for `i = 2`.
  - `countLE x (k/30)` for `k = 0..3` is `0, 2, 2, 2`. So `2 ≤ 2` passes and `3 > 2` fails, giving `numRej = 2`.
  - Conclusion: `1/50 ≤ (1/10)·2/3 = 2/30`, strict. The docstring's `2 ≤ countLE x (2/30) = 2`, `3 > countLE x (3/30) = 2` and `1/50 ≤ 2/30` are all right.
- **Not degenerate.**
  - `m = 3`, and `q > 0` is not the boundary `q = 0`.
  - `i` is not the smallest p-value, so both of Holm's steps act.
  - There are no ties, and the values are genuine p-values in `[0, 1]`.

### Namespaces and imports
The imports are exactly StepDownProcedure and StepUpProcedure. Both `open` lines come after the imports and before the namespace, and the one theorem is inside `ClassicalLean.Probability.HolmInsideStepUp`. `open Finset` is unused by the statement (the witness writes `Finset.` in full); it is harmless and probably meant for the proof.

### Docstrings
- The module docstring states the choice: the rejection is written as in `numRej_update_eq_of_le`, with `m = Fintype.card ι`.
- The proof sketch is correct. In particular, `#{l : x l < x j} ≤ k − 1` gives `c_j ≥ m − k + 1`, and `k(m − k + 1) − m = (k − 1)(m − k)` checks out.
- Line 29 is 101 characters long (finding 1).

---

## Bridge 155: `CorrelationBound`

### Statements
`variable {Ω} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [hμ : IsProbabilityMeasure μ] {X Y : Ω → ℝ}`

- `covariance_sq_le_variance_mul (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) : cov[X, Y; μ] ^ 2 ≤ variance X μ * variance Y μ`: **FAITHFUL**.
- `abs_correlation_le_one (hX) (hY) : |correlation X Y μ| ≤ 1`: **FAITHFUL**.
  - Elaborated with `pp.fullNames`, `correlation` is `ClassicalLean.Probability.LinearPrediction.correlation`.
  - There is no `ProbabilityTheory.correlation` in this Mathlib (`inst.lean`: unknown identifier), so the short name is not ambiguous.
- The probability measure is kept as `[IsProbabilityMeasure μ]`, not widened, as the order says. The instance is named `hμ`, so the witness can supply it.

### Hypotheses
- **`hX` and `hY` are needed for theorem 1.** Take `X ∈ L¹ \ L²` on a probability space. Then `evariance X = ∞`, so Lean's `variance X μ = 0`. With the bounded `Y = 1{X > E X}`, `cov[X, Y] = E[(X − EX)(Y − EY)] = E[(X − EX)·1{X > EX}] > 0`, while the right side is `0`.
- **Some finiteness of `μ` is needed.** On an infinite measure, `X − μ[X]` with `μ[X] ≠ 0` is not in L², so `Var X = 0`, while `cov` can be nonzero. The probability measure is the row's own choice.
- **Observation, not a finding:** theorem 2 appears to stay true without `hX` and `hY`. Outside L² one variance is `0` (`toReal ∞`), so the correlation is `x/0 = 0`. The hypotheses are what the intended proof (through theorem 1) needs, and the row says "in L²", so keeping them is right.

### Witnesses (both: `Ω = Fin 2 → Bool`, `μ = (4⁻¹ : ℝ≥0) • count`, `X = ±1` by flip 0, `Y = X + (±1 by flip 1)`)
- **Form.**
  - `Ω`, `μ`, `hμ`, `X` and `Y` are given by name, and `hX`, `hY` by `MemLp.of_discrete`.
  - `m0` is not named; it is fixed by unification with `μ`'s type. That is the same practice as Gruss's reviewed witness, and the witness gate counts unification-filled implicits.
  - The `open scoped NNReal in` line sits on its own line before the docstring, the order Lean accepts and the same as PrincipalComponents' witnesses.
  - There is no forbidden word.
- **Instance claim.** "Lean does not find the instance" is **true**: `inst.lean` gives `failed to synthesize IsProbabilityMeasure (4⁻¹ • Measure.count)`.
- **Arithmetic, checked exactly on the four equally likely outcomes.**
  - `(T,T)`: `X = 1`, `Y = 2`. `(T,F)`: `X = 1`, `Y = 0`. `(F,T)`: `X = −1`, `Y = 0`. `(F,F)`: `X = −1`, `Y = −2`.
  - `E X = E Y = 0`, `Var X = 1`, `Var Y = (4+0+0+4)/4 = 2`, and `cov = (2+0+0+2)/4 = 1`.
  - `cov² = 1 < 2 = Var X·Var Y`, strict.
  - `corr = 1/√2 ≈ 0.7071`, strictly inside `(−1, 1)`, with root `√2 ≠ 0`, so the `x/0` case does not enter.
  - The total mass is `4⁻¹·4 = 1`.
  - The docstrings' "neither constant, neither independent (cov ≠ 0) nor proportional" are all right.
- **Not degenerate:** two genuine coins and two non-constant variables, with no junk value used.

### Namespaces and imports
The imports are exactly Gruss and LinearPrediction. `open MeasureTheory ProbabilityTheory` and `open ClassicalLean.Probability.LinearPrediction` come after the imports and before the namespace, and both theorems are inside it.

### Docstrings
- The `x / 0 = 0` case is stated in the module docstring and in `abs_correlation_le_one`'s docstring, as the order requires.
- The "copied step, Gruss unchanged" remark is present.
- Two problems: the first witness's docstring has a stray line break (finding 7), and the witnesses' `simp` raises the `linter.flexible` warning (finding 2).

---

## Bridge 164: `PinskerTest`

### Statement
`size_add_one_sub_power_ge_pinsker {ι} [Fintype ι] [MeasurableSpace ι] {p₀ p₁ φ} (hp₀) (hp₀1) (hp₁) (hp₁1) (hsupp : ∀ i, p₀ i = 0 → p₁ i = 0) (hφ : IsTest φ) : 1 - √(relEntropy p₁ p₀ / 2) ≤ ∑ i, φ i * p₀ i + (1 - ∑ i, φ i * p₁ i)`

**FAITHFUL.**
- `#check` prints the binders and hypotheses identically to `ClassicalLean.Statistics.size_add_one_sub_power_ge`: the same constants (`ClassicalLean.Simplex.relEntropy`, `ClassicalLean.Statistics.IsTest`), the same order and the same names.
- Only the left side differs, and it is the table's expression. `relEntropy p₁ p₀` has the arguments in the right order (`D(p₁ ‖ p₀)`, Pinsker at `p = p₁`, `q = p₀`).
- No comparison with Bretagnolle–Huber is stated.

### Hypotheses
- `hsupp` is **needed**. Take `p₀ = (1, 0)`, `p₁ = (0, 1)`, `φ = (0, 1)`. Lean's `D = 0·log 0 + 1·log(1/0) = 0`, so the bound is `1`, but the left side is `0 + (1 − 1) = 0`.
- `hp₀` is **needed**. Take `p₀ = (−1, 2)`, `p₁ = (0, 1)`, `φ = (1, 0)`. Then `D = log(1/2) < 0`, `√` of a negative number is `0`, the bound is `1`, and the left side is `−1 + 1 = 0`.
- `hp₁` is **needed**. Take `p₁ = (−1, 2)`, `p₀ = (1/2, 1/2)`, `φ = (0, 1)`. Then `D ≈ 2.08`, the bound is `≈ −0.02`, and the left side is `−0.5`.
- The sums are needed by Pinsker.
- `[MeasurableSpace ι]` and the `Measurable` half of `IsTest` are not used by the proof, which needs only `φ i ∈ [0, 1]`. The order prescribes "exactly the binders and hypotheses of `size_add_one_sub_power_ge`", so they are mandated, not extra.

### Witness (`Fin 3`, `p₀ = (1/2, 1/2, 0)`, `p₁ = (1/4, 3/4, 0)`, `φ = (0, 1, 0)`)
- **Form:** OK. It is the same block as NeymanPearson's reviewed witness, renamed, with every argument by name and no `open`.
- **Arithmetic.**
  - `D = ¼ log ½ + ¾ log (3/2) = −0.173287 + 0.304099 = 0.130812`, which matches "about 0.131". The third cell gives `0·log(0/0) = 0`, the true convention, so no junk value matters.
  - `√(D/2) = 0.255746`, so the bound is `0.744254`, which matches "about 0.744", below `1`.
  - Size plus missed detection is `1/2 + (1 − 3/4) = 3/4 = 0.75 ≥ 0.7443`. That holds, by a margin of `0.0057`.
  - Pinsker sanity check: the half-sum `½∑|p₁ − p₀| = 1/4 ≤ 0.2557`.
- **Not degenerate.** The laws differ, so `D > 0`. `φ` is not constant. There are three cells, and `hsupp`'s antecedent holds at cell 3.

### Namespaces and imports
The imports are exactly NeymanPearson and Channel. `open ClassicalLean.Simplex ClassicalLean.Statistics` comes before the namespace, and the theorem is inside it.

### Docstrings
They are correct, including the positive-part argument `(|d| + d)/2` and `∑ d = 0`. Lines 31, 32 and 56 are over 100 characters (finding 1).

---

## Bridge 166: `HeunRichardson`

### Statements (as elaborated)
- Helper `heunIterate_eq_add_sum (g) (a h y₀) (n) : heunIterate (fun t _ ↦ g t) a h y₀ n = y₀ + h / 2 * ∑ k ∈ range n, (g (a + k * h) + g (a + k * h + h))`.
  - True: by induction, it matches the definition's step with `f` ignoring `y`.
  - It has no hypotheses and its conclusion is an equation, so it is nothing the vacuity gate flags: not `True`, not a hypothesis.
  - It is inside the namespace.
- `heunIterate_add_eq_trapezoidal (g) (a b y₀) (N) : heunIterate … a ((b - a) / ↑N) y₀ N = y₀ + trapezoidal_integral g N a b`.
  - **FAITHFUL** to the table: every `N`, no hypothesis.
  - **GENERALIZED** relative to the row, which says `N ≥ 1`; `N = 0` and `a > b` are included.
  - Checked exactly on 200 random polynomial cases, `N = 0..5`, both signs of `b − a`.
- `richardson_heunIterate_eq_simpson (g) (a b y₀) (N) : (4 * heunIterate … ((b - a) / ((2:ℝ) * ↑N)) y₀ ((2:ℕ) * N) - heunIterate … ((b - a) / ↑N) y₀ N) / 3 = y₀ + simpson g N a b`.
  - **FAITHFUL.** The `2N` run's step is `(b - a) / (2 * (N : ℝ))` as ordered, and the step count `2 * N` is in ℕ.
  - Checked exactly on the same 200 cases.
- `abs_sub_richardson_heunIterate_le {g g₁ g₂ g₃ g₄} {a b M y₀} (hab) {N} (hN : 0 < N) (hf hf₁ hf₂ hf₃ hM) : |(y₀ + ∫ x in a..b, g x) - (Richardson value)| ≤ (b - a) * ((b - a) / (2 * ↑N)) ^ 4 * M / 180`.
  - **FAITHFUL.** The hypotheses are `simpson_error_le`'s, binder for binder, with `f` renamed `g` and `Icc` being `Set.Icc`. The bound is identical to `simpson_error_le`'s, with `2 * ↑N` cast on the atom.
  - "Of `y b`" is written `y₀ + ∫ₐᵇ g`, with no solution `y`.
  - The absolute value's argument is `(y₀ + ∫) − (y₀ + simpson) = ∫ − simpson`.
  - `open Set Finset` makes `Icc` overloaded, but `#check` shows `Set.Icc`, because ℝ has no `LocallyFiniteOrder`.

### Hypotheses of theorem 3
All are needed.
- `hab`: take `a = 1`, `b = 0`, `N = 1`, `g ≡ 0` with derivatives `0`, and `M = 1`. Every hypothesis holds vacuously on the empty `Icc`. The left side is `0` and the right side is `−1/2880`.
- `hN`: take `N = 0`, `g ≡ 1` on `[0, 1]`, and `M = 0`. The extrapolated value is `y₀`, so the left side is `1` and the right side is `0`.
- Derivative chain: take `g = |x − 1/2|` with "derivatives" `0` and `M = 0`, `N = 1`. Simpson gives `1/6` against `∫ = 1/4`, so the left side is positive and the right side is `0`.
- `hM`: take `M = −1`, which makes the right side negative.

### Witness (theorem 3: `[0, 1]`, `y₀ = 1`, `N = 2`, `g = x⁴`, `g₁…g₄ = 4x³, 12x², 24x, 24`, `M = 24`)
- **Form.**
  - Every binder is supplied: `g g₁ g₂ g₃ g₄ a b M y₀` by name, `hab`, `N` by name, `hN`, `hf…hM`.
  - It is one block with no `open` beyond the top-level `open Set` (for `Icc`), and no forbidden word.
  - Theorems 1 and 2 and the helper have no hypotheses and correctly have no witness.
- **Arithmetic.**
  - The bound is `1·(1/4)⁴·24/180 = 24/46080 = 1/1920`, as the docstring says, and it is positive.
  - Exactly, the 2-step run gives `u₂ = 41/32` and the 4-step run gives `u₄ = 625/512`.
  - The Richardson value is `(4u₄ − u₂)/3 = 461/384`, which is `y₀ + simpson = 1 + 77/384`.
  - `y₀ + ∫ = 6/5`, so the error is **exactly `1/1920`**, and the bound is attained, as it must be for `x⁴`, where Simpson's error formula is exact.
  - This is not degenerate under any case of rule 3, and it is a good witness of sharpness. The docstring could say so (finding 5).
- **Moving process.** The iterates move at every step.
  - `N = 2` run: increments `1/64` and `17/64`.
  - `2N` run: increments `1/2048`, `17/2048`, `97/2048` and `337/2048`.
  - The docstring does not say so (finding 5).
- **Not degenerate:** `[0, 1]` is not a point, `g⁗ = 24 ≠ 0`, `M > 0`, and both runs take at least 2 steps.

### Namespaces and imports
- The imports are exactly EulerMethod and Simpson. `open Set Finset` comes before the namespace, and all four theorems, the helper included, are inside it.
- `heunIterate` and `simpson` resolve through the parent namespaces (`ClassicalLean.Analysis.heunIterate` and `ClassicalLean.simpson`, as printed).
- There is no definition or notation for `heun`, as ordered.

### Docstrings
- The choices are stated: `y b` is `y₀ + ∫ₐᵇ g` with no solution `y`, in the module docstring and in theorem 3's docstring; the `2N` step's form is stated; and the `N = 0` case is stated.
- Two typesetting errors: the helper's formula (finding 3) and a backtick slip in the module's proof sketch (finding 4).
- Line 32 is over 100 characters (finding 1).

---

## Bridge 167: `HeunEulerMaclaurin`

### Statements (as elaborated with `pp.parens`)
- `heunIterate_one_eq_add_sum_sub {g} {a b : ℤ} {y₀} (hab : a ≤ b) : heunIterate (fun t _ ↦ g t) ↑a 1 y₀ (b - a).toNat = (y₀ + ∑ k ∈ Finset.Icc a b, g ↑k) - (g ↑a + g ↑b) / 2`.
  - **FAITHFUL.** The parsing trap is avoided: the sum stops before `-`, so the term is `(y₀ + ∑ …) − (g a + g b)/2`, not `∑ (g k − …)`.
  - ℤ→ℝ casts are on `k`, `a` and `b`, and the index set is `Finset.Icc a b` in ℤ, as in `sum_eq_integral_add_two`.
  - Checked exactly on 200 random cases, `a ∈ [−5, 5]`, `b − a ∈ [0, 5]`, including `a = b`.
- `sub_heunIterate_eq_eulerMaclaurin {g g' g''} {a b : ℤ} {y₀} (hab hf hf' hf'c hf'' hint) : (y₀ + ∫ t in ↑a..↑b, g t) - heunIterate … = (-(g' ↑b - g' ↑a)) / 12 + ∫ t in ↑a..↑b, bernoulliFun 2 (Int.fract t) / 2 * g'' t`.
  - **FAITHFUL.** The hypotheses are `sum_eq_integral_add_two`'s, binder for binder (`f f' f''` renamed `g g' g''`).
  - The identity follows: `Σ = ∫ + (g a + g b)/2 + (g'b − g'a)/12 − R`, so `(y₀ + ∫) − iterate = −(g'b − g'a)/12 + R`.

### Hypotheses
- Theorem 1's `hab` is needed. For `a > b`, `toNat` is `0` and `Icc` is empty: with `a = 1`, `b = 0`, `g = x² + 1`, the left side is `1` and the right side is `−1/2`. The docstring says this correctly.
- Theorem 2's hypotheses are prescribed by the order. With `a > b`, everything is vacuous on the empty interval and the identity fails for generic `g`, so `hab` is needed.

### Witnesses
**Theorem 1** (`a = 0`, `b = 3`, `g = x²`, `y₀ = 1`):
- Form: OK, with `g a b y₀` by name and `hab`.
- Increments: `(g k + g(k+1))/2 = 1/2, 5/2, 13/2`. The iterate is `21/2`, and the right side is `1 + (0+1+4+9) − (0+9)/2 = 21/2`. All the docstring's numbers are right.
- Moving process: `n = 3 ≥ 1`, and the iterate moves at every step, as the docstring says.
- Observation: `g a = 0` at `a = 0`, so the end correction exercises only `g b`. That is not a rule-3 case, since the only hypothesis `0 ≤ 3` is not met through a zero.

**Theorem 2** (`a = 0`, `b = 2`, `g = x⁴`, `g' = 4x³`, `g'' = 12x²`, `y₀ = 1`):
- Form: OK. It is the same block as EulerMaclaurin's reviewed witness, plus `y₀`.
- Arithmetic. On the unit interval `[j, j+1]`, the remainder is `∫₀¹ B₂(s)/2·12(s+j)² ds = 6∫₀¹ B₂ s² = 6(1/5 − 1/4 + 1/18) = 6/180 = 1/30`, because `∫B₂ = ∫sB₂ = 0`. That is `1/30` on each interval and `1/15` in all, as the docstring says. A cubic gives `0`, also checked.
- Whole identity: `(1 + 32/5) − 10 = −13/5 = −32/12 + 1/15`, which checks.
- Moving process: the iterate moves at both steps (`1/2`, then `17/2`, to `10`), but the docstring does not say so (finding 6).

### Namespaces and imports
The imports are exactly EulerMethod and EulerMaclaurin. `open Set MeasureTheory` comes before the namespace, and both theorems are inside it.

### Docstrings
- The module docstring and theorem 2's docstring say `y b = y₀ + ∫ₐᵇ g`, with no solution `y`.
- The choices are stated: `toNat`, the cast `(a : ℝ)`, `Finset.Icc` in ℤ, and unit steps only.
- Line 52 is over 100 characters (finding 1).

---

## FINDINGS

No statement is wrong or WEAKER. Every witness meets rule 3, and every numeric claim is right. All findings are MINOR. Findings 1 and 2 will, however, block the "0 warnings" build gate if they are left.

1. **MINOR (blocks the 0-warning build).** Six lines exceed 100 characters. With the package's `[leanOptions]` (`weak.linter.mathlibStandardSet=true`), `lake build` raises a `linter.style.longLine` warning on each.
   - The lines: `HolmInsideStepUp.lean:29` (101), `PinskerTest.lean:31` (101), `:32` (105), `:56` (101, in the witness docstring), `HeunRichardson.lean:32` (101) and `HeunEulerMaclaurin.lean:52` (101).
   - The brief's section 7 outputs ("only `sorry`") came from `lake env lean` without these options. With the options (`scratch/opt_*.out`), the modules give 8 non-`sorry` warnings: these six and the two in finding 2.
   - Fix: re-wrap the lines, and elaborate with `-Dweak.linter.mathlibStandardSet=true` (or `lake build`) at the next check.
2. **MINOR (blocks the 0-warning build).** `CorrelationBound.lean:66` and `:80`: in the witnesses' `hμ` proofs, `simp [Measure.smul_apply, ENNReal.smul_def]` followed by `exact …` raises `linter.flexible`.
   - Fix: use the `simp only [Measure.smul_apply, Measure.count_univ, ENat.card_eq_coe_fintype_card, Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.reducePow, Nat.cast_ofNat, ENat.toENNReal_ofNat]` that the linter suggests, or close the goal with a single terminal tactic.
   - This changes a proof inside the witness block, not the witness's arguments.
3. **MINOR (wording).** `HeunRichardson.lean:45`, the helper's docstring: `∑ₖ₍ₖ₍ₙ₎` is garbled.
   - Fix: write ``y₀ + h/2 · ∑_{k<n} (g (a + k h) + g (a + k h + h))`` (or `∑ k ∈ range n`).
4. **MINOR (wording).** `HeunRichardson.lean:37`, the module's proof sketch: ``h ((g a + g b)/2 + g` at the inner nodes`)`` has its backticks misplaced.
   - Fix: ``h ((g a + g b)/2 + ∑ g`` at the inner nodes``)`` or plain prose: "`h` times `(g a + g b)/2` plus the sum of `g` at the inner nodes".
5. **MINOR (witness docstring, what moves).** `HeunRichardson.lean:87–92`: the conclusion is about the two Heun runs, but the docstring does not say they move at every step (VACUITY-4's moving-process case). They do: the `N = 2` run by `1/64` and `17/64` (to `41/32`), and the `2N` run by `1/2048`, `17/2048`, `97/2048` and `337/2048` (to `625/512`).
   - Fix: add these, and optionally that the Richardson value `461/384` misses `y₀ + ∫ = 6/5` by exactly `1/1920`, so the bound is attained.
6. **MINOR (witness docstring, what moves).** `HeunEulerMaclaurin.lean:74–79`: the theorem-2 witness does not say that the iterate moves at both steps (by `1/2` and `17/2`, to `10`).
   - Fix: add it, and optionally the value of each side, `−13/5`.
7. **MINOR (formatting).** `CorrelationBound.lean:59–60`: the first witness's docstring breaks after "`X = ±1` by the", which leaves a short line.
   - Fix: re-flow the paragraph.

Notes, not findings:
- 155: theorem 2 seems true without `hX` and `hY`, through the junk value `Var = 0`, but the row and the proof route want L².
- 164: `[MeasurableSpace ι]` and `Measurable φ` are unused by the proof but mandated by the order.
- 158: `open Finset` is unused at the statement stage.
- 166: theorems 1 and 2 are GENERALIZED relative to the row (`N ≥ 1` dropped), as the order's table asks.

None of the fixes changes a statement or a witness's arguments. Finding 2 changes one tactic line inside a witness block, so a second pass is not required under the order's rule 5.

**Overall verdict: PASS WITH FINDINGS (7)**
