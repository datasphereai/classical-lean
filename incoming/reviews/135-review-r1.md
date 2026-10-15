# Review of ClassicalLean/Analysis/FrankWolfe.lean (item 135)

Method: I read the module (320 lines) and the draft `incoming/d135-r1-s2.lean` (143 lines) in full, diffed them, and read the lemmas the module relies on (`ClassicalLean/Analysis/GradientDescent.lean:123,136`, `ClassicalLean/Simplex/Basic.lean:75-84`). I checked the witness iterates with exact rational arithmetic in Python for k < 40. I made two Lean runs on one scratch file, `/tmp/claude-0/-home-user-classical-lean/19408406-f39d-5a72-8f6f-124d894b525a/scratchpad/review/cold-reviewer-135/FWCopy.lean`. It is a verbatim copy of the module, so it imports only the module's own three imports, with checks appended after it, and it used the brief's flags. The copy, both witnesses included, elaborates with no errors and no warnings. Nothing in the repository was written.

## A. Statements against the plan row and the draft

**`sub_le_of_frankWolfe`: FAITHFUL.**
- The plan row asks for `f(x_k) − f* ≤ 4L/(k+2)` with step `2/(k+2)`, for convex `f` with `L`-Lipschitz gradient on the simplex.
- The theorem (lines 146-156) proves `f (x k) - f z ≤ 4 * ↑L / (↑k + 2)` in ℝ, as confirmed by `#check`, for every `z` in the closed simplex and every `k > 0`. Because this holds for every `z`, it is the `f*` bound.
- The setting is the plan's: `EuclideanSpace ℝ ι`, so the Euclidean norm, which gives squared diameter 2. `hmin` (lines 152-153) is the linear-minimisation step and `hx` (line 154) is the step rule.
- `hk : 0 < k` is needed, not a weakening. At `k = 0` the claim fails: take a linear `f`, `L = 0`, and `x 0` a vertex that does not minimise `f`.
- Convexity is assumed only on the simplex, which is more general than the plan. The gradient is assumed to exist and be `L`-Lipschitz on the whole space, which is the usual L-smooth setting.

**`fw_general`: GENERALIZED.** It works on any convex `K` of squared diameter at most `D` in any real Hilbert space and gives `2 L D / (k+3)` at `x (k+1)`. With `D = 2` this is exactly the plan's bound.

**Unchanged from the draft.**
- The diff shows the signatures are byte-identical to the draft (draft 39-47 against module 67-75, and draft 121-131 against module 146-156).
- The only changes are:
  - `private lemma fw_general` became `theorem fw_general`, as the order's table says.
  - The namespace was added (lines 37 and 168).
  - The docstrings were rewritten.
  - In the proofs, the dead `first` alternatives were removed (draft 86-88, 106-109, 135-137).
- No statement changed in meaning.

## B. Every hypothesis is used

I added a scratch command (`#hyp_use`) that takes each theorem's proof term and checks whether each binder occurs in the body. Every binder of both theorems does, including the `CompleteSpace` instance, which `HasGradientAt` needs. The output was:
- `fw_general`: `hK hconv hf hL hD hx0 hs hmin hx hz … used_in_proof=true` (all 23 binders).
- `sub_le_of_frankWolfe`: `hconv hf hL hx0 hs hmin hx hz hk … used_in_proof=true` (all 18 binders).

Reading the proof agrees:
- In `fw_general`, `hK`, `hx0`, `hs` and `hx` are used to show every iterate stays in `K` (lines 78-86).
- `hD` is used through `fw_step` and to show `0 ≤ D` (line 76).
- `hmin` is used at `z` (line 91).
- In `sub_le_of_frankWolfe`, `hk` is used at line 161.

A note, not a finding: `hK` in `fw_general` follows from `hconv`, since `ConvexOn` includes convexity of the set. In Lean, `example … (hconv : ConvexOn ℝ K f) : Convex ℝ K := hconv.1` elaborates. The draft had the same hypothesis and rule 1 keeps the draft's statement, so nothing should change.

## C. Witnesses (lines 170-242 and 244-320)

Both main theorems have hypotheses, and both are witnessed.

**Form.**
- Each is an `example :=` that applies the theorem itself by its full name (lines 179 and 254), after the last `end` (line 168).
- Every chosen argument is given by name:
  - `sub_le_of_frankWolfe`: `ι f f' L x s z k`.
  - `fw_general`: `E f f' L K D x s z k`; its explicit `k` is also passed as `(k := 3)`.
- Each has its own `open InnerProductSpace in` line. Otherwise it relies only on the module's top-level `open`s (lines 34-35).
- The docstrings begin "The hypotheses of `…` hold together:".
- `grep -nE "sorry|admit|native_decide|implemented_by|axiom|set_option"` on the file finds nothing.
- Each witness is one inline block, and the only `have`s are local.
- The `fw_general` witness cites the module's private lemma `norm_sub_sq_le_two` (line 271). That lemma comes from the draft and is not a helper written for the witness, so it is not a violation.

**Non-degeneracy, hypothesis by hypothesis.**
- `ι = Fin 2`: the family has size 2.
- `f y = ‖y‖²`: not constant. Convexity is proved properly (strongly convex, then uniformly convex, then convex).
- `f' y = 2y`: the true gradient, proved through `hasStrictFDerivAt_norm_sq`.
- `L = 2`: positive and the exact Lipschitz constant, so the theorem's constant does not vanish.
- `D = 2`: the exact squared diameter of the 2-simplex, attained at its vertices.
- `x 0 = (0,1)`: a genuine vertex.
- `x` and `s` are genuine Frank–Wolfe iterates, not identically 0 and not constant past any point. The Python check runs the real method (`f' = 2x`, linear minimisation over both vertices, step `2/(k+2)`) and matches the witness's closed form and its `s` for every k < 40:
  - iterates (0,1), (1,0), (1/3,2/3), (2/3,1/3), (2/5,3/5), (3/5,2/5), …;
  - `s` alternates (1,0), (0,1).
  - The two gradient coordinates are never equal, so each `s k` is the unique minimiser.
  - Lean checks `hmin` against every `y` in the simplex, for all `k`.
- No junk value is used. The `(k+1)/(2k)` branch is taken only for odd `k ≥ 1`, and the proofs carry `hk1 : 1 ≤ k`.
- `z = (1/2,1/2)` is the true minimiser of `f`, the hardest comparison point.
- `k = 3`, so `0 < 3` is not a boundary case. The instance is `1/18 ≤ 8/5`.

**Docstring claims.** I checked all of them and they are true:
- the even and odd closed forms;
- first coordinate `≤ 1/2` at even `k` and `≥ 1/2` at odd `k`;
- the iterates approach (1/2,1/2) from both sides and never reach it;
- convexity, gradient and Lipschitz constant;
- the 2-simplex is convex with squared diameter at most 2.

## D. Namespace

All four declarations sit inside `namespace ClassicalLean.Analysis.FrankWolfe` … `end ClassicalLean.Analysis.FrankWolfe` (lines 37-168):
- `fw_step` (private, line 40)
- `fw_general` (line 67)
- `norm_sub_sq_le_two` (private, line 122)
- `sub_le_of_frankWolfe` (line 146)

Lines 34-35 are `open`s, not declarations. `#print axioms` on both theorems gives `[propext, Classical.choice, Quot.sound]`.

## E. Imports

The imports are lines 7-9: `ClassicalLean.Analysis.GradientDescent`, `ClassicalLean.Simplex.Basic` and `Mathlib.Analysis.InnerProductSpace.PiL2`. Each is a specific file, and there is no `import Mathlib`.

## F. Recursive-`True` conclusions

There are none. Both conclusions are real inequalities.

## G. Docstrings

- Item numbers: `fw_general` says "item 135 of MATH-PLAN-library-2" (lines 61-62), and so does `sub_le_of_frankWolfe` (line 141).
- The module docstring lists both results (lines 19-23) and names the order and item (line 17).
- These claims are correct:
  - the proof sketch at lines 25-31, which matches `le_add_inner_gradient_add_sq` and `add_inner_gradient_le` in `GradientDescent`;
  - the one-step inequality;
  - `(aᵢ − bᵢ)² ≤ aᵢ + bᵢ` on `[0,1]`.
- One imprecise claim:
  - Line 22 says the closed simplex "is" of squared diameter `2`, and lines 144-145 say "the squared diameter `2` of the simplex".
  - For a general `Fintype ι` that holds only when `ι` has at least two elements. With one element the simplex is a single point (diameter 0); with none it is empty.
  - The lemma docstring (line 121) and the proof correctly use "at most `2`". The theorem is unaffected; only the wording is off.

## H. Other

- The proofs are unchanged in substance from the draft.
- The library root imports the module (`ClassicalLean.lean:132`).
- The name `fw_general` is kept as the order requires.
- I found nothing misleading beyond the point in G.

## Findings
1. MINOR — The docstrings at lines 22-23 and 144-145 state the simplex's squared diameter as exactly `2`, which is false when `ι` has fewer than two elements. Proposed fix:
   - line 22: "whose squared diameter is at most `2` (exactly `2` once `ι` has two elements)";
   - lines 144-145: "`fw_general` with `D = 2`, which bounds the squared diameter of the simplex (`norm_sub_sq_le_two`)".

   This is a docstring-only change.

## Verdict
VERDICT: PASS WITH FINDINGS (0 blocker, 0 major, 1 minor)
sub_le_of_frankWolfe: FAITHFUL
fw_general: GENERALIZED
