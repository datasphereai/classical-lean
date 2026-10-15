# Review of ClassicalLean/Probability/Reflection.lean (item 139)

Brief read in full. Its sha256 matched: b3d8bc2865738da1a7650d0d27422ad10c51a1222f318b3442284f9d12b8fdea. I did not change anything in the repository. My one Lean file was `/tmp/claude-0/-home-user-classical-lean/19408406-f39d-5a72-8f6f-124d894b525a/scratchpad/review/cold-reviewer-139/Check139.lean`. It is a byte-for-byte copy of the module, witness included, with my checks added at the end. Its only import is the module's own `Mathlib.Probability.UniformOn`. It ran with the flags the brief gives and printed no errors or warnings. Its outputs are quoted below.

## A. Statement against the plan row, and against the draft
**FAITHFUL.**
- **Plan row:** `P(max_{k ≤ n} S_k ≥ a) = P(S_n ≥ a) + P(S_n > a)` for `a ≥ 1`, for the fair `±1` walk.
- **Theorem (Reflection.lean:241–247):**
  - The measure is `uniformOn Set.univ` on `Fin n → Bool`, so all `2^n` paths have the same chance: a fair walk.
  - Steps are `+1` on `true` and `−1` on `false` (`step`, l.36–37). `walk n ω k` is the sum of the first `k` steps (l.40–41).
  - The left side is `{ω | a ≤ (Finset.range (n + 1)).sup' ⟨0, _⟩ (walk n ω)}`, which is the event max over `k = 0..n` of `S_k ≥ a`.
  - The right side is `{a ≤ walk n ω n}` and `{a < walk n ω n}`.
  - The hypothesis is `(ha : 1 ≤ a)`. It is neither weaker nor stronger than the plan row.
- **Against the draft:** I diffed `incoming/d139-r2-s1.lean` against the module after deleting the `Reflection.` qualifiers. The differences are only:
  - the licence header and module docstring;
  - `namespace Reflection` becoming `namespace ClassicalLean.Probability.Reflection`, with the theorem moved inside it;
  - `import Mathlib` becoming `import Mathlib.Probability.UniformOn`;
  - `if_pos`/`if_neg`/`dif_pos`/`push_neg` becoming `ite_eq_left`/`ite_eq_right`/`dite_eq_left`/`push Not` (l.81, 88, 107, 113, 126, 145, 153, 158). Core gives these the same forms: `ite_eq_left (hc : c) : ite c t e = t` and so on, in `Init/Core.lean:1179/1188/1204`;
  - the theorem's docstring.
- The statement lines (draft l.213–219, module l.241–247) are identical. `step` and `walk` are identical.
- **No change in meaning.**

## B. Every hypothesis used
The only hypothesis is `ha : 1 ≤ a`. It is used:
- l.265: `card_eq n a ha`;
- inside `card_eq` (l.208, l.216): `walk_reflect_end ha h`;
- inside that (l.169): `walk_tau ha h`;
- inside `walk_tau` (l.119–122): it rules out `tau = 0`, since `walk 0 = 0 < a`.

It is also needed. My scratch file proves the negation of the statement at `n = 1`, `a = −1`: the left side is 2/2 and the right side is 2/2 + 1/2. That `example : ¬ (...)` checked with no error.

An `#eval` of the path counts (hit, end ≥ a, end > a) for n = 0..5 and a = −2..3 gives:
- the identity fails for a = −2 and a = −1 at every n;
- it holds for a = 0..3 at every n.

## C. Witness (l.271–274)
`example := ClassicalLean.Probability.Reflection.measureReal_max_ge_eq (n := 4) (a := 2) (by norm_num)`
- It applies the theorem itself by its full name, not a `∃` restatement.
- Both chosen arguments are given by name. The hypothesis proof is positional, as HANDOFF §4's form `Full.name (x := …) h₁ …` has it.
- It has no `open … in` line and no helper declarations, and is one inline block.
- The docstring starts with "The hypotheses of `measureReal_max_ge_eq` hold together:".
- None of the forbidden words appear anywhere in the file. A grep for sorry, admit, native_decide, implemented_by, axiom, set_option and `import Mathlib` found nothing.
- It sits after the module's last line (`end …`, l.269).
- **Not degenerate.**
  - The one hypothesis, `1 ≤ a`, is met by `a = 2`. That is not the boundary `a = 1`, and nothing about it is empty, zero, a junk value or a vanishing constant.
  - The path space `Fin 4 → Bool` has 16 points.
  - The event is non-trivial: `#eval counts 4 2` gives `(6, 5, 1, 16)`. So 6 of 16 paths reach 2, 5 end at or above 2 and 1 ends above 2, giving 6/16 = 5/16 + 1/16.
  - No function is identically 0 past some point, and no kernel is involved.
- **Docstring truth:** "a walk of `n = 4` fair steps and the level `a = 2`, which is at least `1` and which the walk can reach within its `4` steps" is true; 6 paths reach it.
- `#check` of the witness term gives the theorem's statement at `n = 4`, `a = 2`.
- The one main theorem with a hypothesis is witnessed.

## D. Namespace
`namespace ClassicalLean.Probability.Reflection` (l.33) to `end ClassicalLean.Probability.Reflection` (l.269) holds every declaration, private ones included:
- `step`, `walk`, `walk_zero`, `walk_succ`, `step_le_one`, `flipFrom`, `flipFrom_flipFrom`, `step_flipFrom`;
- `walk_flipFrom_of_le`, `walk_flipFrom_of_ge`, `Hit`, `tau`, `reflect`, `tau_spec`, `tau_min`, `walk_tau`;
- `hit_flip`, `reflect_of_hit`, `reflect_of_not`, `reflect_reflect`, `walk_reflect_end`, `card_eq`, `real_uniform`, `measureReal_max_ge_eq`.

Before l.33 there are only the header, the import, the module docstring and `open MeasureTheory ProbabilityTheory`. The only thing after l.269 is the witness `example`.

`#print axioms` gives `[propext, Classical.choice, Quot.sound]`.

## E. Imports
There is one import, `Mathlib.Probability.UniformOn` (l.7), a specific file that exists in `.lake/packages/mathlib`. There is no `import Mathlib`. The scratch copy, with only that import, elaborated cleanly, so the import is enough.

## F. Recursive-predicate conclusion
None. The conclusion is an equation between real numbers. No `Prop`-valued recursive definition appears; `Hit` is a non-recursive `∃`.

## G. Docstrings
- The theorem's docstring (l.237–240) names "item 139 of MATH-PLAN-library-2".
- The module docstring (l.9–29) lists the result `measureReal_max_ge_eq`, names the order and item, and lists the definitions.
- I checked each mathematical claim, and all are true:
  - Paths are uniform.
  - `true` means up 1 and `false` means down 1.
  - A path that hits `a` ends either at or above it or below it.
  - `reflect` is its own inverse; `reflect_reflect` holds for every `ω`.
  - `reflect` maps "hit and end below `a`" onto "end above `a`".
  - A ±1 walk first reaches `a ≥ 1` exactly at `a`, so the end `S_n` goes to `2a − S_n` (`walk_tau`, `walk_flipFrom_of_ge`).
  - Dividing by `2^n` gives the chances (`real_uniform` divides by `Fintype.card (Fin n → Bool) = 2^n`).
  - `flipFrom` reverses the flips at indices `≥ t`, which is the docstring's "from `tau` on", and leaves `walk` unchanged up to time `t`.
- The definition docstrings for `step` ("0 past n"), `Hit`, `tau` and `reflect` match their definitions.

## H. Anything else
Nothing wrong found.
- The licence header matches the other modules.
- No name is an eponym (HANDOFF §5).
- `Hit` is UpperCamelCase as a `Prop`.
- The scratch copy gave no deprecation or linter warnings.
- One observation, **not a finding**: the identity also holds at `a = 0`. There both sides equal 1, by the symmetry `ω ↦ ¬ω`, and the `#eval` above confirms it for n = 0..5. So the hypothesis could be relaxed to `0 ≤ a`. The plan row asks for `a ≥ 1` and the theorem matches it, so no change is needed.

## Findings
None.

## Verdict
VERDICT: PASS
measureReal_max_ge_eq: FAITHFUL
