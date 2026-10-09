# Round 46 — the chain rule for entropy, Pinsker's inequality, the Hessian of log-sum-exp, Hermite–Hadamard and the trapezoidal rule, rounding in inner products and Horner's rule, and generalised least squares (order LEAN-18)

Session: Claude Code `session_014tMro6KYq7f532WnRJZyjY` on DSMain, as dustin, executing order
`LEAN-18` (`records/orders/20261009T100800Z__claude-code__order-lean18-chain-rule-pinsker-and-gls.md`), batch 2 of the plan
`/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md` (sha256
b9b64503909bc9d42ab562b9aa83474e86fa5661be6c14b5b3add5badf8d1789), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `paper-crypto-13`, made from `origin/master` =
`197910f`. Lean and Mathlib v4.34.0. Nothing pushed. Evidence: `~/lean/lean18-checks/` (outside the
repository), `evidence.log` (time, label, rc, prediction, command per run).

First part written before any module change, so that gate 6 finds the new modules' paths before
their commits; completed after the work, below.

Modules this round plans to change or add (as the claim row):

* `ClassicalLean/InformationTheory/MutualInformation.lean` — item 9.
* `ClassicalLean/InformationTheory/Channel.lean` — item 10.
* `ClassicalLean/Simplex/SecondOrder.lean` — item 11.
* `ClassicalLean/Analysis/HermiteHadamard.lean` — new module, items 12 and 13; added to `ClassicalLean.lean`.
* `ClassicalLean/Analysis/RoundingError.lean` — items 14 and 15.
* `ClassicalLean/Statistics/GeneralizedLeastSquares.lean` — new module, item 16; added to `ClassicalLean.lean`.

Mathlib re-checked before the records were written (`~/lean/lean18-checks/search.txt`): none of
items 9 to 16 is in Mathlib v4.34.0; item 12's left half is to come from Mathlib's
`ConvexOn.map_set_average_le`.

## Completed after the work

Commits on `paper-crypto-13`, in order: `1e643e1` (records, before the work), `c0ba2fa`
(MutualInformation, item 9), `b458731` (Channel, item 10), `13b2d32` (HermiteHadamard and
`ClassicalLean.lean`, items 12 and 13), `1c44fd7` (RoundingError, items 14 and 15), `097fe4c`
(GeneralizedLeastSquares and `ClassicalLean.lean`, item 16), `da86558` (SecondOrder, item 11), then
the records commit that completes this fragment (its hash is in the order's report, not here).

Declarations. Item 9: `condEntropy` (definition), `condEntropy_eq_sum_mul_shannonEntropy`,
`shannonEntropy_eq_add_condEntropy`. Item 10: `sq_sum_abs_sub_le_two_mul_relEntropy`. Item 11:
`hasFDerivAt_logSumExp`, `hasFDerivAt_softmax`, `hasFDerivAt_fderiv_logSumExp_apply`. Items 12 and
13: `convexOn_midpoint_le_average`, `integral_le_mul_add_div_two_of_convexOn` (helper),
`average_le_convexOn_endpoints`, `integral_le_trapezoidal_integral`. Items 14 and 15:
`dotComputed`, `hornerRev`, `hornerComputed` (definitions), `abs_dotComputed_sub_le`,
`self_le_gamma` (helper), `exists_hornerRev_eq` (helper), `abs_hornerComputed_sub_le`. Item 16:
`glsMatrix` (definition), `glsMatrix_one`, `glsMatrix_mul_self`, `glsMatrix_mul_mul_transpose`,
`posSemidef_mul_mul_transpose_sub_inv`.

Added beyond the plan's names, each drafted in the statements file before any proof:
`condEntropy_eq_sum_mul_shannonEntropy` (reads the definition as the rows' entropies, weighted by
the row totals; Fano, the plan's item 36, will want it); `hasFDerivAt_fderiv_logSumExp_apply` (the
composite the plan's row says this item closes, one direction at a time); `glsMatrix_mul_self`
(the plan's "is unbiased") and `glsMatrix_mul_mul_transpose` (the covariance factor, used by
Aitken's proof).

Mathlib re-checked before the records were written (`~/lean/lean18-checks/search.txt`, each
pattern with its count, Mathlib's `Wanted/` folder included): none of items 9 to 16 is in
Mathlib v4.34.0, so none was dropped or reduced. Item 12's left half is Mathlib's
`ConvexOn.map_set_average_le` applied to the identity, not proved again. Reused from Mathlib:
`ConvexOn.map_set_average_le`, `interval_average_eq`, `integral_comp_sub_left`,
`integral_mono_on`, `sum_integral_adjacent_intervals`,
`sum_trapezoidal_integral_adjacent_intervals`, `trapezoidal_integral_one`, `HasFDerivAt.sum`,
`HasFDerivAt.log`, `HasFDerivAt.exp`, `hasFDerivAt_pi`, `hasFDerivAt_apply`,
`Matrix.dotProduct_mulVec`, `Matrix.PosDef.inv`, `Matrix.PosDef.conjTranspose_mul_mul_same`,
`Matrix.PosSemidef.mul_mul_conjTranspose_same`, `Matrix.transpose_nonsing_inv`,
`Matrix.mulVec_injective_iff_isUnit`.

Statements: drafted in `~/lean/lean18-checks/Statements.lean` and elaborated with `sorry` before
any proof (16 statements; `st3.out`: rc 0, 16 `sorry` warnings, nothing else). Before any proof,
two drafted hypotheses were found unneeded and removed (the statements are stronger):
`condEntropy_eq_sum_mul_shannonEntropy` holds for every `P`, and `glsMatrix_mul_mul_transpose`
for every `V` and `X`. Aitken's theorem takes `V` positive semidefinite, weaker than the plan's
positive definite. Run `st1` was the same file with a misplaced `DecidableEq` (a linter note).

Differences from the plan's rows. Item 14: `abs_dotComputed_sub_le` has `n + 1` terms and
`γ (n + 1)`, which is Higham's `γ n` for `n` terms, and rests on `abs_one_add_mul_sub_one_le` and
`exists_sumComputed_eq`, not on `abs_prod_one_add_sub_one_le` as the row says. Item 12's helper is
named `integral_le_mul_add_div_two_of_convexOn` and item 15's `self_le_gamma`, after reviews r12
and r14.

Hypotheses: each main theorem's hypotheses are named needed or not shown needed in its module's
docstring, with the exact case; the cases are `~/lean/lean18-checks/checks.py` (standard
library, seeded, exact Fractions where rational, Lean's `log 0 = 0`, `log x = log |x|`,
`x / 0 = 0` and zero inverse of a singular matrix), output `chk1.out`, `ALL OK`, run before any
proof. Not shown needed: continuity in items 12 and 13 (believed removable, not proved).
Reviews r12 and r14 also proved the stated cases false in Lean, in their scratch folders.

Records follow the clock (rule 18): items 10 to 16 were proved while the reviews of earlier
items ran; no proof of a statement was written while that statement's own review ran, and every
module was committed only after its own review returned and its fixes were built. Statements and
proofs of each module were reviewed together; there was no separate statement review. Items 10 and
11 were proved in scratch files while review r9 read MutualInformation, and put into their modules
only after r9 returned, because MutualInformation imports Channel. Item 16's import line in
`ClassicalLean.lean` waited for review r12, which read that file.

Cold reviews (rule 13), each by a fresh general-purpose subagent in its own scratch folder under
`~/lean/lean18-checks/review/`, brief built by `prep_review.sh` with HANDOFF rules 12 to 25 quoted
verbatim (`make_brief.py`); `~/.claude/agent-memory/` unchanged after each. All six: PASS WITH
FINDINGS, no BLOCKER and no MAJOR.

| review | module | findings | applied | not done (recorded here) |
|---|---|---|---|---|
| r9 | MutualInformation | 5 MINOR | 1, 2, 3, 5a; 4 recorded above | 5b a longer name (the order fixes it) |
| r10 | Channel | 4 MINOR | 1, 2, 3, 4 | — |
| r11 | SecondOrder | 3 MINOR | 1; 3 in the docstring only | 2 `ROADMAP.md` §1.14 P2 still says "not stated as one theorem" (ROADMAP is not in this claim); 3 the bilinear Hessian, a strict derivative and smoothness |
| r12 | HermiteHadamard | 5 MINOR | 2, 3, 4a | 1 drop continuity; 4b state with `⨍`; 5 the multiplied left half |
| r14 | RoundingError | 4 MINOR | 1, 2; 4 recorded above | 3 reuse `self_le_gamma` in the existing `exists_sumComputed_eq` |
| r16 | GeneralizedLeastSquares | 3 MINOR | 1, 2 | 3 a Loewner-order corollary and an equality case |

Review files and sha256: r9 3f83efcf...d29d2a, r10 2375b52b...8d1bae, r11 e38ea1ca...0e3bab,
r12 a92dce8a...d35094, r14 d2a3e8b2...303829, r16 1183fa4a...257a59.

New theorem constants: 37 predicted by a census of the six scratch files `census/C9.lean` to
`census/C16.lean` (rule 27), written before any whole-library gate (`census/prediction.txt`,
2272 predicted); the axiom gate then measured 2270 (order LEAN-17's close: 2235), 35 new. The
miss of 2 is two private equation lemmas of `hornerRev`'s match (`hornerRev.match_1.eq_1`,
`eq_2`), which the census counted and the gate does not (`Count.lean`, `count.out`; the other
name differences are renumbered auxiliaries, one for one). A clean tree.

Gates on the clean tree at `da86558` (`gates.sh g1`, every rc 0): `lake build` "Build completed
successfully (4021 jobs)." with 0 warning lines; "axiom gate PASS — 2270 theorem constant(s) under
[ClassicalLean]"; "vacuity gate PASS — no vacuous theorems in [ClassicalLean]"; "check_sorry PASS —
85 file(s) under ClassicalLean"; "banned_vocab_scan PASS — 85 file(s) under ClassicalLean +
ClassicalLean.lean, 0 hits"; "check_records PASS — 85 module(s) under ClassicalLean". check_sorry
fire test: a `sorry` planted in a scratch copy outside the repository gave rc 1, "check_sorry FAIL —
1 violation(s) across 85 file(s)", naming only the plant. `#print axioms` (`Axioms.lean`, rc 0):
all 16 main theorems print exactly `[propext, Classical.choice, Quot.sound]` (counted by script).
The vacuity gate's budget was not changed.
