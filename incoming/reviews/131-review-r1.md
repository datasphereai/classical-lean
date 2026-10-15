# Review of ClassicalLean/InformationTheory/HanInequality.lean (item 131)

I read the whole module (336 lines), the draft `incoming/d131-r1-s1.lean` (its sha256 4bcbcc2a…530dd matches `incoming/README.md`), the order's table and rules, HANDOFF §4 and §5, the library lemmas the proof uses (`Entropy.lean:66`, `MutualInformation.lean:173, 236, 243, 257`) and how `tools/AxiomGate.lean` handles private names. I elaborated one scratch file, `/tmp/claude-0/-home-user-classical-lean/19408406-f39d-5a72-8f6f-124d894b525a/scratchpad/review/cold-reviewer-131/Check1.lean`, which imports only the module under review, using the brief's exact command. It contains four things: `#print axioms`, a scan of every constant the module adds, a counterexample showing `hP1` is needed, and a verbatim copy of the witness. The module's `.olean` (02:43:02) is newer than its source (02:42:53). I changed no repository file.

## A. Statement against the plan row and the draft
**FAITHFUL.** The plan row reads: "for a joint law of `n` coordinates, `(n − 1) H(X) ≤ ∑ᵢ H(X without coordinate i)`". Lines 232–236 state this:
- `P : (ι → α) → ℝ`, with `hP0 : ∀ x, 0 ≤ P x` and `hP1 : ∑ x, P x = 1`. This is a joint law of `n = Fintype.card ι` coordinates over the finite alphabet `α`.
- The conclusion is `((Fintype.card ι : ℝ) - 1) * shannonEntropy P ≤ ∑ i, shannonEntropy (fun y : {j // j ≠ i} → α => ∑ x, if (fun j => x j.1) = y then P x else 0)`. The summand is exactly the pushforward of `P` to the family without coordinate `i`.
- The subtraction `n − 1` is done in ℝ, so it is not truncated: at `n = 0` it is `-1 · 0 ≤ 0`, which is true.
- Using one alphabet for all coordinates loses nothing, because any finite alphabets embed in one finite type.

**The statement did not change from the draft.** `diff` of draft lines 210–217 against module lines 228–236 shows only the docstring changed (it gained "(item 131 of MATH-PLAN-library-2)"). The theorem moved inside `namespace ClassicalLean.InformationTheory.HanInequality`. Every other difference in the body is in a helper or a proof, and all are the linter changes the order lists:
- the dead `first | … | rw [Finset.sum_ite_eq']` alternative was removed;
- `show` became `change` (lines 178, 242, 296);
- `if_pos`/`if_neg` became `ite_eq_left`/`ite_eq_right`;
- `marg_via_equiv` now takes `[Finite Z]` and no `[DecidableEq W]`, adding `classical` and `have := Fintype.ofFinite Z` (lines 135–142).

None of these changes the meaning of any statement.

## B. Every hypothesis used
Both hypotheses are used.
- `hP0` is used at line 252 (`ssa_marg hP0 …`), which gives strong subadditivity for each `i`.
- `hP1` is used at line 301 (`rw [← hP1]`), in `hF0`: the entropy of the marginal on the empty set of coordinates is `0`.

Both are also needed for the theorem to hold:
- **`hP1`, checked in Lean.** In `Check1.lean`, the statement `¬ ((card (Fin 2) - 1) * H(fun _ : Fin 2 → Fin 2 => 1) ≤ ∑ i, H(marginal_i))` elaborates with no error. With `P ≡ 1` (so `hP0` holds and `hP1` fails), the left side is `0` and the right side is `-8 log 2`.
- **`hP0`, by hand.** Take `ι = α = Fin 2` and `P(00, 01, 10, 11) = (1, 1, −1, 0)`, which sums to `1`. Then `H(P) = 0`, because `Real.log (−1) = 0`. The marginals are `(0, 1)` with `H = 0` and `(2, −1)` with `H = −2 log 2`. The conclusion becomes `0 ≤ −2 log 2`, which is false.

## C. Witness (lines 324–336)
It meets rule 4 and HANDOFF §4.
- **Applies the theorem itself:** `example := ClassicalLean.InformationTheory.HanInequality.mul_shannonEntropy_le_sum (ι := Fin 2) (α := Fin 2) (P := fun x ↦ if x 0 = x 1 then 3 / 8 else 1 / 8) (…) (by …)`.
- **Arguments:** every chosen argument is given by name; the two hypothesis proofs are positional, as §4's form allows.
- **No `open`:** it uses fully qualified names, so it relies on no `open`.
- **Docstring:** it begins "The hypotheses of `mul_shannonEntropy_le_sum` hold together: …".
- **Forbidden words:** `grep` finds no `sorry`, `admit`, `native_decide`, `implemented_by`, `axiom` or `set_option` anywhere in the file.
- **Form:** one inline block with no helper declarations.
- **Elaborates:** the verbatim copy at the end of `Check1.lean` elaborates with no error and no linter warning.

It is not degenerate. Going hypothesis by hypothesis:
- **Sizes:** both `ι` and `α` have size 2.
- **The theorem's constant:** `n − 1 = 1`, so it does not vanish.
- **`hP0`:** it holds because every weight is strictly positive (`3/8` or `1/8`), not because some weight is zero.
- **`hP1`:** the sum runs over all four families and equals `1`. It does not rely on an empty sum or a junk value.
- **The law itself:** it is neither a point mass, nor uniform, nor a product law, since `P(x₀ = x₁) = 3/4`.
- **Rule 4's extra cases:** there is no function that is identically 0 past some point, and there is no kernel or observation.

**The docstring is true:** the two families whose coordinates agree get `3/8` each, the two that differ get `1/8` each, and `3/8 + 3/8 + 1/8 + 1/8 = 1`. The only main theorem has hypotheses, and it is witnessed.

*Observation, not a finding:* at `n = 2`, Han's inequality is plain subadditivity. The rules require only size ≥ 2, so this is compliant.

## D. Every declaration inside the namespace
All declarations are inside. `namespace ClassicalLean.InformationTheory.HanInequality` opens at line 29 and `end` is at line 322; every `def` and `theorem` lies between them.

The scan in `Check1.lean` lists every constant whose module is `HanInequality` and tests its name with `privateToUserName`. It reports `constants from the module: 20` and no `OUTSIDE:` lines. The private helpers appear as `_private.ClassicalLean.InformationTheory.HanInequality.0.ClassicalLean.InformationTheory.HanInequality.<name>`. `tools/AxiomGate.lean:97–103` tests the user name, so the axiom gate covers them.

The `open ClassicalLean.Simplex` at line 27 is not a declaration. The witness after `end` is not a declaration.

## E. Imports targeted
Yes. There is one import, `import ClassicalLean.InformationTheory.MutualInformation` (line 7), and no `import Mathlib`. That file is where `condEntropy`, `condEntropy_eq_sum_mul_shannonEntropy`, `shannonEntropy_eq_add_condEntropy` and `shannonEntropy_le_shannonEntropy_add_shannonEntropy` live.

## F. No conclusion that is a recursive predicate true everywhere
None. The conclusion is a real-number inequality.

## G. Docstrings
All present and true.
- **Item named:** the main theorem's docstring says "**Han's inequality** (item 131 of MATH-PLAN-library-2)" (line 228). The module docstring says "Order CLOUD-MATH-1, item 131 of MATH-PLAN-library-2" (line 14) and lists `mul_shannonEntropy_le_sum` (line 16).
- **"`shannonEntropy` is the library's `ClassicalLean.Simplex.shannonEntropy`":** true (`Entropy.lean:66`).
- **"the law of `X` without coordinate `i` is the marginal of `P` on `{j // j ≠ i} → α`":** true, as the statement shows.
- **Proof sketch:** "strong subadditivity `H(C, A, B) + H(C) ≤ H(C, A) + H(C, B)` with `C` the coordinates before `i`, `A` the coordinate `i` and `B` the coordinates after it… prefix terms telescope". This matches the proof:
  - lines 252–253 apply SSA with `c = restr (· < e i)`, `a = x i`, `b = restr (e i < ·)`;
  - `h1`, `h2` and `h3` identify the three terms as `H(P)`, `F(e i + 1)` and `H(X without i)`;
  - `htel` (lines 305–311) does the telescoping.
- **"Strong subadditivity (`ssa_sum`) comes from the library's chain rule (`shannonEntropy_eq_add_condEntropy`) and subadditivity (`shannonEntropy_le_shannonEntropy_add_shannonEntropy`) applied row by row":** true (lines 158–194). These are the names and roles in `MutualInformation.lean:173, 257`.
- **Helper docstrings:** `marg`, `restr`, `ssa_sum` (stated for any nonnegative `Q`, which holds because both sides scale alike) and `ssa_marg` are accurate.

## H. Anything else
Nothing wrong.
- **Linter and gates:** no line exceeds 100 characters (Python check). `#print axioms` gives `[propext, Classical.choice, Quot.sound]`. `ClassicalLean.lean` gains the import line. `tools/vacuity_reviewed.txt` is unchanged and has no `HanInequality` entries, so there is no HELPER reason to check.
- **Header:** the licence header matches the library's form.
- **Naming:** the theorem name `mul_shannonEntropy_le_sum` describes the result, and the module name `HanInequality` is the one the order prescribes (the order takes precedence over HANDOFF §5).

## Findings
None.

## Verdict
VERDICT: PASS
mul_shannonEntropy_le_sum: FAITHFUL
