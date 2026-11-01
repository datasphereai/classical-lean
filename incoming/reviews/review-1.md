# Cold review 1 of order CLOUD-MATH-7 (statement stage)

Brief reviewed: `/root/cm7/review/brief.md`, sha256 `79d5ce7767182373318c97b124858ec2d504488dfae4182a6569cb45349aef6e`.

The five module texts quoted in the brief's section F are byte-identical to `/root/cm7/stage/ClassicalLean/…`. I checked this by script. I edited no file in the repository.

Checks done with tools (scratch files only, under `/root/cm7/review/scratch/`):
- A script compared each module's main statement with the order's. All five match byte for byte, with no namespace prefix dropped. Each docstring is the order's text, unchanged apart from line wrapping, followed by "Bridge N of `MATH-PLAN-library-2-bridges-2.md`."
- I grepped the five modules for `sorry`, `native`, `plausible`, `admit`, `implemented_by`, `axiom`, `set_option`, `(config :=` and `reduceBool`. The only hits are the five `sorry` proof tactics, none of them in a docstring or comment. The modules use "stated without a proof" for the scratch files.
- I ran `lake env lean` on a copy of each module with a `MetaM` probe that lists every `ClassicalLean.*` constant in the main theorem's type. This checks whether the module's namespace silently captures a short name. The results are exactly the intended constants: 170 `[Pseudoinverse.pinv]`, 172 `[Pseudoinverse.pinv, Simplex.categoricalCov]`, 168 `[]`, 169 `[Statistics.IsUniformlyMostPowerful, Statistics.thresholdTest]`, 171 `[]`. Each copy, witnesses included, elaborated with only the single `declaration uses 'sorry'` warning, which matches section G.

## Verdicts on the main theorems

- **170 `rank_mul_pinv_eq`: FAITHFUL.** It is word for word the order's statement. It gives all three claims of the row: `rank H = rank A`, `trace H = rank A` (as reals) and `rank (1 − H) = card m − rank A`. The ℕ subtraction is harmless because `rank A ≤ card m`. No hypothesis is missing or extra; `[DecidableEq m]` is needed for `1`. There is no hypothesis, so no witness is needed.
- **172 `pinv_categoricalCov`: FAITHFUL.** It is word for word, and the row's "strictly positive probability vector" is `hp` with `hp1`. I worked the four Penrose equations by hand. With `C = D − ppᵀ`, `X = P D⁻¹ P`, `C1 = 0` and `C` symmetric:
  - `CP = PC = C`.
  - `C D⁻¹ = I − p1ᵀ`, because `(δᵢⱼpⱼ − pᵢpⱼ)/pⱼ = δᵢⱼ − pᵢ`. Then `1ᵀP = 0`, so `CX = (I − p1ᵀ)P = P` and `XC = (CX)ᵀ = P`.
  - `CXC = PC = C` and `XCX = PX = X`.

  So the statement is true. Only `p i ≠ 0` is used; positivity is the order's choice and not a defect.
- **168 `exists_multipliers_isMinOn_iff`: FAITHFUL.** It is word for word. It has the row's hypotheses: convexity, gradients everywhere, a Slater point, `xbar` feasible and a minimiser. `hxbar` is needed because `IsMinOn` does not assert membership. The conclusion has the row's shape, one `w ≥ 0` and then `∀ y` (feasible minimiser ↔ feasible, slack and stationary), and the precedence reads as intended. The proof sketch is sound: `L ≥ L xbar = f xbar` and `L y ≤ f y = f xbar` force each `w i g i y = 0`, then `∇L y = 0`; the converse is `isMinOn_of_kkt`.
- **169 `isUniformlyMostPowerful_sum_sq_gaussian`: FAITHFUL.** It is word for word. `Θ = Set.Ioi (0 : ℝ≥0)` encodes `v > 0`, `c` is arbitrary, and the level is `gammaMeasure (k/2) (1/2)` of `Ioi (c/v₀)`. The ratio `f v'/f v = (v/v')^{k/2} exp(S(1/v − 1/v')/2)` is nondecreasing in `S` on all of ℝ for `v < v'`, so `HasMonotoneLikelihoodRatio` holds. For `c ≤ 0` the level is 1, which is also consistent. `hk` is needed, since at `k = 0` the shape is `0`.
- **171 `min_sub_le_of_subgradient_eigenvalues`: FAITHFUL.** It is word for word. `hT` for every `x` is equivalent to all of `A₀, A i` being symmetric: `x = 0` gives `A₀`, and `x = eᵢ` gives `A₀ + A i`. Index `0` is the top eigenvalue (`eigenvalues_antitone`, which I confirmed in Mathlib). The subgradient inequality is `λ₀(Ty) ≥ ⟪Ty u,u⟫ = λ₀(Tx) + Σ(yᵢ − xᵢ)⟪Aᵢu,u⟫`. The conclusion is `min_sub_le_of_subgradient`'s bound for every `z`.

## Witnesses

- **172: PASS.** The form is `(ι := Fin 3) (p := ![1/2, 1/3, 1/6]) hp hp1`, which supplies every binder (instances are inferred). Arithmetic:
  - all three entries are positive;
  - `1/2 + 1/3 + 1/6 = 3/6 + 2/6 + 1/6 = 1`;
  - `1/p = (2, 3, 6)`, matching the docstring's `diag (2, 3, 6)`, and it is not constant, so `diagonal (1/p)` is not a multiple of `1`.

  The size is 3 ≥ 2, and the case is not uniform, so it is not degenerate.
- **168: PASS.** It names `E, ι, f, g, f', g', xbar`, then gives 7 positional hypotheses: `hf, hg, hf', hg', hslater, hxbar, hmin`. Arithmetic:
  - Gradients: `d/dy (y−2)²/2 = y − 2`, `d/dy (y − 1) = 1`, `d/dy (−y − 5) = −1`.
  - Slater point: `g 0 0 = −1 < 0` and `g 1 0 = −5 < 0`.
  - At `xbar = 1`: `g 0 1 = 0` (active) and `g 1 1 = −6 < 0` (slack).
  - The feasible set is `[−5, 1]`. For `x ≤ 1`, `x − 2 ≤ −1`, so `(x−2)²/2 ≥ 1/2 = (1−2)²/2 = f 1`.
  - Multipliers: slackness gives `w 1 = 0`, and stationarity `−1 + w 0 − w 1 = 0` gives `w 0 = 1`, not `0`.
  - The unconstrained minimiser `2` has `g 0 2 = 1 > 0`, so it is infeasible.

  All numbers are correct, and `ι` has size 2.
- **169: PASS.** It supplies `(k := 2) (hk) (v₀ := ⟨1, _⟩) (c := 3)`, so all four binders before the colon are given. Putting the positional `hk` between named arguments follows library precedent (ChiSquared line 316, NeymanPearson line 694). Arithmetic: `0 < 2`, and `0 < 1` in `ℝ≥0`. The level is `gammaMeasure (2/2) (1/2) (Ioi (3/1))`. With density `(1/2)e^{−x/2}` on `x ≥ 0` (Mathlib's `gammaPDFReal 1 (1/2)`), it equals `e^{−3/2} ≈ 0.2231`, so it is strictly between 0 and 1 as the docstring says. `c = 3` is not a boundary value: `c ≤ 0` would give level 1. See finding 2 on the docstring.
- **171: PASS.** It names `F, n, m, hn, A₀, A, hT, x, z, η, G, T`, then gives `hη, hTpos, hg, hstep` positionally, so every binder is supplied. The iterates are one inline `Nat.rec`, there is no helper declaration, and `hstep` holds by `rfl`. Arithmetic:
  - The maps: `T x = diag(1,0) + x₀ diag(1,−1) + x₁ diag(0,1) = diag(1 + x₀, −x₀ + x₁)`.
  - The bound `G`: for unit `u` with `b = u₁² ∈ [0,1]`, `⟪A 0 u,u⟫ = u₀² − u₁² = 1 − 2b` and `⟪A 1 u,u⟫ = b`. So `‖g‖² = 5b² − 4b + 1`, a convex quadratic whose maximum on `[0,1]` is at `b = 1` and equals `2`. Hence `‖g‖ ≤ √2 ≈ 1.414 ≤ 2 = G`, and `2 ≤ 4 = G²`.
  - The iterates, with `η = 1/2`:
    - `x 0 = (3/4, 0)` gives `T = diag(7/4, −3/4)`, top eigenvector `±e₀`, `g = (1, 0)`;
    - `x 1 = (3/4 − 1/2, 0) = (1/4, 0)` gives `diag(5/4, −1/4)`, `g = (1, 0)`;
    - `x 2 = (−1/4, 0)` gives `diag(3/4, 1/4)`, `g = (1, 0)`;
    - `x 3 = (−3/4, 0)`.
  - There are no ties inside the horizon (7/4 vs −3/4, 5/4 vs −1/4, 3/4 vs 1/4), and each step moves by `(−1/2, 0) ≠ 0`, with `T = 3 ≥ 1`.
  - The conclusion at these values, which the docstring does not claim: the left side is `min(7/4, 5/4, 3/4) − λ₀(diag(1,0)) = 3/4 − 1 = −1/4`. The right side is `(9/16 + (1/4)·4·3)/(2·(1/2)·3) = (57/16)/3 = 19/16`.

  All docstring numbers are correct. See finding 1.

## Namespaces, imports, opens, docstrings

- **Namespaces:** each module has one main theorem, inside a namespace equal to the module name (`ClassicalLean.Algebra.HatMatrixRank`, `…Algebra.CategoricalPseudoinverse`, `…Analysis.KKTMultipliers`, `…Statistics.ChiSquaredTest`, `…Analysis.EigenvalueSubgradient`). There are no other declarations, and the examples sit after `end`.
- **Imports:** exactly the table's two per module, with no `import Mathlib` and no extra Mathlib line.
- **Opens:** the only `open` that reaches another module's names is 172's `open ClassicalLean.Algebra.Pseudoinverse ClassicalLean.Simplex`. It sits after the imports and before the namespace. The other opens are Mathlib's, placed the same way. The witnesses use no `open`.
- **Docstrings:** none contains a forbidden word, and every witness docstring begins "The hypotheses of `name` hold together:".

## FINDINGS

1. **MINOR (171 witness docstring).** The order asks the docstring to show that "each step uses `u = e₀`, `g = (1, 0)`, and moves". The docstring states the top eigenvector `e₀` and `g = (1, 0)` only at `x 0`; for `x 1` and `x 2` it gives only the diagonal matrices. The values are right, since `x 2 = x 1 − (1/2)(1,0)` needs `g(x 1) = (1, 0)`, but they are left implicit. Suggested fix: after the list of iterates, add "at each of `x 0`, `x 1`, `x 2` the top eigenvector is `e₀` up to sign, `g = (1, 0)`, and the step moves the iterate by `(-1/2, 0)`."
2. **MINOR (169 witness docstring).** Rule 3 asks the docstring to say what moves. It names `k`, `v₀`, `c` and says the level is strictly between 0 and 1, but it neither says what moves nor gives the number behind that claim. Suggested fix: append "the densities move with the variance `v` (at `x = 0` the product density is `1 / (2πv)`: `1/(2π)` at `v = 1`, `1/(4π)` at `v = 2`), and the level is `P(χ²₂ > 3) = e^(-3/2) ≈ 0.223`, since `gammaMeasure 1 (1/2)` has density `e^(-x/2)/2` on `x ≥ 0`."

Observations (not counted as findings; no change needed under the rules):
- In the 171 witness, the second coordinate of the iterates stays `0` and `g₁ = 0` inside the horizon, so `A 1` never acts along the path. It still enters `hT` and the bound `G` (through `b = u₁²`), and no rule-3 case is triggered. If a witness where both maps act on the path is wanted, `x 0 = (0, 2)` works:
  - `x 0` gives `diag(1, 2)`, top `e₁`, `g = (−1, 1)`;
  - `x 1 = (1/2, 3/2)` gives `diag(3/2, 1)`, `g = (1, 0)`;
  - `x 2 = (0, 3/2)` gives `diag(1, 3/2)`, `g = (−1, 1)`;
  - `x 3 = (1/2, 1)`.

  There are no ties, both coordinates move, and `‖x 0 − z‖² = 4`. The order's model was followed, so this is optional.
- The 168 witness has a unique minimiser (`{1}`), so the "every minimiser" side of the iff meets one point. This is allowed, since a witness only shows the hypotheses hold together.
- Each module docstring says "this module proves it word for word". That becomes true only once the `sorry` proofs are replaced, which is expected at this stage.

FINDINGS 2
