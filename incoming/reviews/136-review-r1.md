# Review of ClassicalLean/Analysis/StatePrices.lean (item 136)

Reviewed read-only. The draft `incoming/d136-r3-s2.lean` has sha256 `a40db108…0e612`, which matches `incoming/README.md:15`. I elaborated two scratch files, both in `/tmp/claude-0/-home-user-classical-lean/19408406-f39d-5a72-8f6f-124d894b525a/scratchpad/review/reviewer-136/`:
- `check1.lean` imports the module.
- `copy.lean` is a verbatim copy of the module, which imports only `ClassicalLean.Analysis.LinearProgram`.

## A. Statement against the plan row and the draft

**FAITHFUL.** Here is the statement as Lean prints it (`#check`, check1.lean):
```
∀ {m : Type u_1} {n : Type u_2} [inst : Fintype m] [inst_1 : Fintype n] (D : Matrix m n ℝ) (π : n → ℝ),
  (¬∃ θ, π ⬝ᵥ θ ≤ 0 ∧ 0 ≤ D.mulVec θ ∧ (π ⬝ᵥ θ < 0 ∨ ∃ i, 0 < D.mulVec θ i)) ↔
    ∃ ψ, (∀ (i : m), 0 < ψ i) ∧ D.transpose.mulVec ψ = π
```
Each part of the plan row maps directly to the formal statement:
- "payoff matrix `D` (states by assets)" is `Matrix m n ℝ`, with rows as states.
- "costs at most nothing" is `π ⬝ᵥ θ ≤ 0`.
- "never pays less than nothing" is `0 ≤ D *ᵥ θ`.
- "either costs less than nothing or sometimes pays more" is `π ⬝ᵥ θ < 0 ∨ ∃ i, 0 < (D *ᵥ θ) i`.
- "strictly positive state prices `ψ` with `Dᵀ ψ = π`" is `(∀ i, 0 < ψ i) ∧ Dᵀ *ᵥ ψ = π`.

The index types are any `Fintype`, which is the plan's "finite form". This is not a generalization beyond the row.

**Same as the draft.** I ran `diff` between the draft and the module. The statement (draft lines 45–48, module lines 57–60) is identical character for character. Only these things changed:
- the licence header was added;
- the module and theorem docstrings were reworded;
- the namespace changed from `ClassicalLean.StatePrices` to `ClassicalLean.Analysis.StatePrices`;
- the main theorem moved from the root into that namespace, and the `open ClassicalLean.StatePrices` line was dropped;
- `show` became `change` at line 132.

The order's table row for 136 (`records/orders/…cloudmath1….md:13`) lists no change to the statement. Its meaning is unchanged.

## B. Hypotheses used

The theorem has no propositional hypotheses. Its binders are:
- the data `D` and `π`, both used in the statement and the proof;
- the instance arguments `[Fintype m]` and `[Fintype n]`. Both are needed for the statement to typecheck: `[Fintype n]` for `π ⬝ᵥ θ` and `D *ᵥ θ`, which sum over the assets, and `[Fintype m]` for `Dᵀ *ᵥ ψ`, which sums over the states.

The no-arbitrage side is half of the conclusion, not a hypothesis. Both directions of the iff are proved: lines 63–124 and 125–135. No finding.

## C. Witnesses

The file has no `example` after its last `end` (line 137). I agree that rule 4 asks for no witness here, because the main theorem has no hypothesis: `D` and `π` are data, and the instance arguments are not propositions. HANDOFF §4 covers only "a theorem with hypotheses".

An iff with no hypotheses cannot be vacuous. As a check, check1.lean shows both sides take both truth values on non-degenerate 2×2 data. Both examples elaborated with no error (only a `push_neg` deprecation warning from my own scratch code):
- With `D = 1` and `π = ![2, 3]`, the right side holds with `ψ = ![2, 3]`.
- With `D = !![1, 1; 1, 2]` and `π = ![1, 1]`, the right side fails. The proof rewrites with `← exists_pos_statePrices_iff` and gives the arbitrage `θ = ![-1, 1]`: it costs 0 and pays `(0, 1)`.

No finding.

## D. Namespaces

All declarations sit in `namespace ClassicalLean.Analysis.StatePrices` (lines 31–137): `sysMap` (l.34), `sysMap_apply` (l.48) and `exists_pos_statePrices_iff` (l.57). check1.lean enumerated every constant whose module is `ClassicalLean.Analysis.StatePrices`:
```
[ClassicalLean.Analysis.StatePrices.exists_pos_statePrices_iff,
 _private.ClassicalLean.Analysis.StatePrices.0.ClassicalLean.Analysis.StatePrices.sysMap,
 _private.….0.ClassicalLean.Analysis.StatePrices.sysMap._proof_1,
 _private.….0.ClassicalLean.Analysis.StatePrices.sysMap._proof_2,
 _private.….0.ClassicalLean.Analysis.StatePrices.sysMap_apply]
```
Every user-facing name is under the namespace. `tools/AxiomGate.lean:103,119` strips `_private` with `privateToUserName`, so the private helpers stay inside the gate. Nothing is left at the root. `#print axioms` gives `[propext, Classical.choice, Quot.sound]`. No finding.

## E. Imports

There is a single import, `import ClassicalLean.Analysis.LinearProgram` (l.7). It is a specific file, and there is no `import Mathlib`. It provides `farkas` (`LinearProgram.lean:200`) and `nonneg_of_forall_dotProduct_nonneg` (l.193), and through it the specific Mathlib files `Matrix.DotProduct` etc. The import line was added to `ClassicalLean.lean` (git diff). No finding.

## F. Recursive-True conclusion

None. The conclusion is an iff between a first-order statement about portfolios and one about state prices. As shown in C, it is non-trivial in both directions. No finding.

## G. Docstrings

- The main theorem's docstring (l.53) says "**State prices** (item 136 of MATH-PLAN-library-2)". The module docstring (l.13–18) names order CLOUD-MATH-1 and item 136, and lists `exists_pos_statePrices_iff` with an accurate statement.
- I checked every mathematical claim in the docstrings and all are true:
  - "every portfolio's cost is `ψ ⬝ᵥ D θ`": this is `key` (l.126), and it follows from `Dᵀψ = π`.
  - Nonnegative payoffs give cost ≥ 0, and a strictly positive payoff gives cost > 0: this is `Finset.sum_pos'` with ψ > 0.
  - The system `Dᵀ u − s π = π − Dᵀ 1`, with `u, s ≥ 0`, written as two inequalities by `sysMap`: this matches `sysMap`'s `toFun` (l.36–37) and the bound at l.64.
  - "`ψ = (u + 1) / (s + 1)`": `Dᵀ(u+1) = (s+1)π`, and the code uses `(s+1)⁻¹ • (u+1)` (l.68).
  - A Farkas certificate gives an arbitrage `θ`: here `θ = y_inl − y_inr`, `Dθ ≥ 0`, `θ⬝π ≤ 0`, and `θ⬝π < (Dθ)⬝1`, so either the cost is negative or some payoff is positive.
- `sysMap`'s docstring "`(u, s) ↦ (Dᵀ u − s π, −(Dᵀ u − s π))`" is accurate.
- The cited name `ClassicalLean.LinearProgram.farkas` exists under that name: `LinearProgram.lean` uses namespace `ClassicalLean.LinearProgram`, l.88.
- The licence header matches the existing modules (`LinearProgram.lean`, `ConvexConjugate.lean`).

No finding.

## H. Anything else

- copy.lean (the module verbatim, with the repository's standard flags including `weak.linter.mathlibStandardSet=true`) elaborated with no output and exit 0: no errors, no warnings, no lints.
- The olean (02:41:08) is newer than the source (02:40:59).
- Observation, not a finding: by Mathlib's naming convention, `exists_pos_statePrices_iff` suggests the `∃ ψ` side is on the left, but it is on the right. To rewrite `∃ ψ …` into the no-arbitrage condition you need `rw [← exists_pos_statePrices_iff]`, as in check1.lean. The order fixes the name and rule 1 fixes the statement, so there is nothing to change.
- Observation, unverified (I was limited to two Lean runs): `open … Finset …` (l.29) may be unused, since every `Finset` lemma in the proof is fully qualified. This is cosmetic, with no rule involved.

## Findings

None.

## Verdict
VERDICT: PASS
exists_pos_statePrices_iff: FAITHFUL
