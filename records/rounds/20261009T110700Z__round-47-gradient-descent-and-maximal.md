# Round 47 — the descent lemma and gradient descent, KKT sufficiency, exponential weights, Rao–Blackwell, and Kolmogorov's maximal inequality (order LEAN-19)

Session: Claude Code `session_016HZA2rbHQv4Gvdu2sAUW2u` on DSMain, as dustin, executing order
`LEAN-19` (`records/orders/20261009T110600Z__claude-code__order-lean19-gradient-descent-and-maximal.md`), batch 3 of the plan
`/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md` (sha256
b9b64503909bc9d42ab562b9aa83474e86fa5661be6c14b5b3add5badf8d1789), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `paper-crypto-14`, made from `origin/master` =
`eb2a150`. Lean and Mathlib v4.34.0. Nothing pushed. Evidence: `~/lean/lean19-checks/` (outside the
repository), `evidence.log` (time, label, rc, prediction, command per run).

First part written before any module change, so that gate 6 finds the new modules' paths before
their commits; completed after the work, below.

Modules this round plans to change or add (as the claim row):

* `ClassicalLean/Analysis/GradientDescent.lean` — new module, items 17 to 20; added to `ClassicalLean.lean`.
* `ClassicalLean/Analysis/ExponentialWeights.lean` — new module, item 21; added to `ClassicalLean.lean`.
* `ClassicalLean/Statistics/RaoBlackwell.lean` — new module, item 22; added to `ClassicalLean.lean`.
* `ClassicalLean/Probability/MaximalInequality.lean` — item 23.
* `ROADMAP.md` — §1.14, pattern P2 (its own commit).

Mathlib re-checked before the records were written (`~/lean/lean19-checks/search.txt`): none of
items 17 to 23 is in Mathlib v4.34.0, so none is dropped. Item 22 is to come from Mathlib's
`integral_condVar_add_variance_condExp` and item 23 from Mathlib's `maximal_ineq`; what this round
adds for item 23 is that the square of a square-integrable martingale is a submartingale.

## Completed after the work

Commits on `paper-crypto-14`, in order: `a95a5e5` (records, before the work), `54f33a8`
(`ROADMAP.md` §1.14 P2, its own commit as the order asks), `51ab8d7` (GradientDescent and
`ClassicalLean.lean`, items 17 to 20), `51ef2ab` (ExponentialWeights and `ClassicalLean.lean`,
item 21), `0ceedd8` (RaoBlackwell and `ClassicalLean.lean`, item 22), `6219153`
(MaximalInequality, item 23), then the records commit that completes this fragment (its hash is in
the order's report, not here).

Declarations. Items 17 to 20 (`ClassicalLean/Analysis/GradientDescent.lean`):
`le_add_inner_gradient_add_sq`, `le_sub_of_gradientStep`, `add_inner_gradient_le`,
`sub_le_sq_sub_sq_of_gradientStep`, `mul_sub_le_of_gradientStep`, `sub_le_of_gradientStep`,
`add_inner_gradient_add_sq_le`, `dist_gradientStep_le`, `isMinOn_of_kkt`, and the helpers
`hasDerivAt_comp_add_smul_sub`, `convexOn_comp_add_smul_sub`. Item 21
(`ClassicalLean/Analysis/ExponentialWeights.lean`): `sum_mul_exp_mul_le_exp_of_mem_Icc`,
`logSumExp_add_smul_le`, `sum_inner_softmax_le`. Item 22
(`ClassicalLean/Statistics/RaoBlackwell.lean`): `variance_condExp_le`,
`integral_sub_sq_eq_variance_add_sq`, `integral_sq_condExp_sub_le`. Item 23
(`ClassicalLean/Probability/MaximalInequality.lean`): `submartingale_sq`,
`measureReal_exists_abs_ge_le`.

Item 22 is the conditioning inequality behind Rao–Blackwell, not the full theorem: the full
Rao–Blackwell theorem also needs a sufficient statistic over a family of distributions, which the
module does not state (Dustin's ruling in chat, 2026-10-09, during the work). The module keeps the
name `ClassicalLean.Statistics.RaoBlackwell` because the records commit `a95a5e5` already named
it; its docstrings say what it is.

Mathlib re-checked before the records were written (`~/lean/lean19-checks/search.txt`): none of
items 17 to 23 is in Mathlib v4.34.0, so none was dropped. Reduced to what is missing: item 22
uses Mathlib's `integral_condVar_add_variance_condExp`, item 23 Mathlib's `maximal_ineq`, item 19
Mathlib's `StrongConvexOn` (through `strongConvexOn_iff_convex`), item 21 Mathlib's
`hasSubgaussianMGF_of_mem_Icc`; none of them is proved again. The search missed Mathlib's
conditional Jensen inequality (`CondJensen.lean`), which review r23 found; it is named in
MaximalInequality's docstring. One line of `search.txt` first said `condVar_nonneg` is in
Mathlib; it is not, and the line was corrected before the records commit.

Statements: drafted in `~/lean/lean19-checks/Statements.lean` and elaborated with `sorry` before
any proof (`st1`: rc 0, 14 `sorry` warnings, nothing else; my prediction said 15, a miscount of my
own statements). Before any proof, `0 < L` was found unneeded and removed from
`le_sub_of_gradientStep` and `dist_gradientStep_le` (at `L = 0` the gradient is constant and the
step does not move; `st2`: rc 0, 14). Added while proving, after the statements run, so not in
the statements file: the helpers `hasDerivAt_comp_add_smul_sub` and `convexOn_comp_add_smul_sub`
and the step lemma `sub_le_sq_sub_sq_of_gradientStep` (11:16 to 11:18 UTC),
`sum_mul_exp_mul_le_exp_of_mem_Icc` (11:22), `integral_sub_sq_eq_variance_add_sq` (11:25). After
review r22, `variance_condExp_le` lost its hypothesis `m ≤ m₀` (stronger). Helper renamed after
review r21: `sum_mul_exp_mul_le` to `sum_mul_exp_mul_le_exp_of_mem_Icc`.

Hypotheses: each module's docstring names, for each main theorem, the hypotheses that fail when
dropped, with the exact case, and those not shown needed. The cases are
`~/lean/lean19-checks/checks.py` (standard library, seeded, exact Fractions except item 21's
floats). Runs: `chk1` printed `FAILURES 1` (check C20 drew 45 KKT problems against its own floor
of 50) but was logged rc 0, because the script then had no exit code; `chk2`, after raising C20's
tries from 500 to 3000, `ALL OK`; `chk3`, after review r17 (cases for
`sub_le_sq_sub_sq_of_gradientStep`, and `raise SystemExit(1 if bad else 0)`), `ALL OK`, rc 0.
The module docstrings quote `chk3`. Several dropped cases in the script are typed-in arithmetic,
not computed; reviews r21, r22 and r23 proved some of them false in Lean in their scratch folders.

Records follow the clock (rule 18): items 21, 22 and 23 were proved while the reviews of earlier
modules ran; each module was committed only after its own review returned and its fixes were
built. `ClassicalLean.lean` was committed one import line at a time, so that no commit carried an
unreviewed module's line (review r17, finding 8).

Cold reviews (rule 13), each by a fresh general-purpose subagent in its own scratch folder under
`~/lean/lean19-checks/review/`, brief built by `prep_review.sh` with HANDOFF rules 12 to 25 quoted
verbatim; the sha256 of every file under `~/.claude/agent-memory/` was the same before r17 and
after r23. All four: PASS WITH FINDINGS, no BLOCKER and no MAJOR.

| review | module | findings | applied | not done (recorded here) |
|---|---|---|---|---|
| r17 | GradientDescent | 8 MINOR | 1, 2, 3, 4, 5, 6, 8; 7 the double blank line | 7 the names (`gradientStep` with no `def`; dot-notation namespaces): the order fixes the names |
| r21 | ExponentialWeights | 8 MINOR | 1, 2, 3 (recorded above), 4, 5, 6, 8 | 7a losses needed only for rounds `t < T`; 7b the `[a, b]` form |
| r22 | RaoBlackwell | 5 MINOR | 1, 2, 3, 4 (in the docstring) | 4 the main inequality for any finite measure (the order asks for Mathlib's law of total variance, which needs a probability measure); 5 the name `integral_sq_condExp_sub_le` against Mathlib's `_sub_sq` convention (the order fixes it) |
| r23 | MaximalInequality | 6 MINOR | 1 (in the docstring), 3, 4, 5 | 2 only `S n` square-integrable (stated in the docstring, not taken); 6 the names; 1 the conditional-Jensen proof |

Review files and sha256: r17 a0f83555...9c9aaa, r21 15d01501...394220, r22 5b0df05b...8f94eb,
r23 c5442cb8...6b10f8.

New theorem constants: 46 predicted by a census of `census/C17.lean`, `C21`, `C22`, `C23`
(rule 27), written at 11:35:26 UTC before any whole-library gate (`census/prediction.txt`, 2316
predicted; C23 re-run after review r23, unchanged). The axiom gate then measured 2316 (order
LEAN-18's close: 2270): a hit. By module with the gate's own rule (`Count.lean`, `count.out`):
GradientDescent 35, ExponentialWeights 3, RaoBlackwell 3, and so 5 in MaximalInequality. Most are
auxiliary lemmas Lean makes for `simp` and `abel`. A clean tree.

Gates on the clean tree at `6219153` (`gates.sh g1`, every rc 0): `lake build` "Build completed
successfully (4027 jobs)." with 0 warning lines (my guess was 4024, a miss); "axiom gate PASS —
2316 theorem constant(s) under [ClassicalLean]"; "vacuity gate PASS — no vacuous theorems in
[ClassicalLean]"; "check_sorry PASS — 88 file(s) under ClassicalLean"; "banned_vocab_scan PASS —
88 file(s) under ClassicalLean + ClassicalLean.lean, 0 hits"; "check_records PASS — 88 module(s)
under ClassicalLean". check_sorry fire test: a `sorry` planted in a scratch copy outside the
repository gave rc 1, "check_sorry FAIL — 1 violation(s) across 88 file(s).", naming only the
plant. `#print axioms` (`Axioms.lean`, rc 0): all 19 new declarations print exactly
`[propext, Classical.choice, Quot.sound]` (counted by script). The vacuity gate's budget was not
changed.
