# Round 45 — the residual variance, two-outcome Pinsker, a Chernoff bound from the score, an AR(1) average, data processing for mutual information, and source coding (order LEAN-17)

Session: Claude Code `session_019VHs1gNRScdbNoDT2HAccf` on DSMain, as dustin, executing order
`LEAN-17` (`records/orders/20261009T091024Z__claude-code__order-lean17-residual-variance-and-coding.md`), batch 1 of the plan
`/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md` (sha256
b24f5cc872ef2aa3506bddfdf6b88cb0b9aa570598d2af43647f43319d0387b2), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `paper-crypto-12`, made from `origin/master` =
`65e10e5`. Lean and Mathlib v4.34.0. Nothing pushed. Evidence: `~/lean/lean17-checks/` (outside the
repository), `evidence.log` (time, label, rc, prediction, command per run).

First part written before any module change, so that gate 6 finds the new modules' paths before
their commits; completed after the work, below.

Modules this round plans to change or add (as the claim row):

* `ClassicalLean/Statistics/FrischWaughLovell.lean` — item 1.
* `ClassicalLean/Probability/CovarianceDirections.lean` — item 2.
* `ClassicalLean/Statistics/ResidualVariance.lean` — new module, item 3; added to `ClassicalLean.lean`.
* `ClassicalLean/InformationTheory/Entropy.lean` — item 4.
* `ClassicalLean/Probability/LikelihoodScore.lean` — item 5.
* `ClassicalLean/Probability/EffectiveSampleSize.lean` — item 6.
* `ClassicalLean/InformationTheory/MutualInformation.lean` — item 7.
* `ClassicalLean/InformationTheory/SourceCoding.lean` — new module, item 8; added to `ClassicalLean.lean`.

## Completed after the work

Commits on `paper-crypto-12`, in order: `aca9d17` (records, before the work), `4231f37`
(FrischWaughLovell, item 1), `37f9f6d` (CovarianceDirections, item 2), `303d685`
(ResidualVariance and `ClassicalLean.lean`, item 3), `7a15647` (Entropy, item 4), `b739a62`
(LikelihoodScore, item 5), `bdf8f11` (EffectiveSampleSize, item 6), `e9a2b7c`
(MutualInformation, item 7), `44ac1c0` (SourceCoding and `ClassicalLean.lean`, item 8), then the
records commit that completes this fragment (its hash is in the order's report, not here).

Declarations. Item 1: `trace_residualMaker`, `rank_residualMaker`. Item 2:
`integral_dotProduct_mulVec`. Item 3: `sum_residualMaker_mulVec_sq` (helper),
`integral_residual_sq`, `integral_residual_sq_div`. Item 4: `relEntropy_fin_two` (public helper),
two private helpers, `two_mul_sq_sub_le_relEntropy`. Item 5: `exp_mul_relEntropy_le_score`
(helper), `measureReal_sum_ge_le_exp_neg_relEntropy`, `measureReal_sum_ge_le_exp_neg_sq`. Item 6:
`covariance_eq_of_steady` (helper), `variance_average_eq_of_steady`, `variance_average_le_of_steady`.
Item 7: `mutualInfo_markov_le`. Item 8: `shannonEntropy_le_sum_mul_length_of_kraft` (helper),
`shannonEntropy_le_sum_mul_length`, `shannonEntropy_le_sum_mul_length_of_isPrefixFree`.

Statements: drafted in `~/lean/lean17-checks/Statements.lean` and elaborated with `sorry` before any
proof (13 statements, rc 0, 13 `sorry` warnings and nothing else, `st3.out`). Differences from the
draft: item 8's prefix-free theorem lost its draft hypothesis that no codeword is empty, because
Mathlib's Kraft inequality needs none (the statement is stronger); items 2 and 7 bind `X` and `γ` as
their modules do. New imports: LikelihoodScore imports InformationTheory.Entropy;
EffectiveSampleSize imports Probability.LinearPrediction; MutualInformation imports
InformationTheory.Channel in place of Entropy (Channel imports Entropy).

Records follow the clock (rule 18): items 2 to 8 were proved while the reviews of earlier items
ran; no proof of a statement was written while that statement's own review ran, and every module
was committed only after its own review returned and its fixes were built.

A wrong premise in the plan and the order, found by review r7: "Gives `mutualInfo` its first user
outside its module". `InformationTheory/SignalGrowth` had already used `mutualInfo` since orders
LEAN-11 and LEAN-16, and the new theorem sits inside MutualInformation. MutualInformation's module
docstring, which said the same thing, is corrected and dated. Its claim to be the first user of
`InformationTheory/Channel` was wrong too (Simplex/SecondOrder imports it); corrected.

Mathlib searched first: the plan's section 5 (`MATH-PLAN-library.md`, sha256 b24f5cc8...387b2), each
pattern with its count, at v4.34.0. Reused from Mathlib: `LinearMap.IsProj.trace`,
`LinearMap.isProj_range_iff_isIdempotentElem`, `Matrix.trace_toLin'_eq`, `covariance_eq_sub`,
`integral_finsetSum`, `antitoneOn_of_deriv_nonpos`, `strictConcaveOn_log_Ioi`, `Real.log_prod`,
`measureReal_mono`, `iIndepFun`, `IsUniquelyDecodable.finsetSum_one_div_card_pow_length_le_one`,
`IsPrefixFree.finsetSum_one_div_card_pow_length_le_one`.

Hypotheses: each main theorem's hypotheses are named needed or not shown needed in its module's
docstring, with the exact case; the cases are `~/lean/lean17-checks/checks.py` (standard library,
seeded, exact Fractions where rational), output `chk3.out`, `ALL OK`. Run 1 (`chk1.out`) missed a
case for item 8's `0 ≤ p` (the search space was too small; a case found by hand was added, `chk2.out`);
review r7 found item 7's search case for `0 ≤ K` also broke the row sums and printed a rounded `K`
(exact cases, each breaking one hypothesis only, `chk3.out`; the only other changed line is item 8's
random sample size, 1080 to 1076, because item 7 no longer draws from the random stream).

Cold reviews (rule 13), each by a fresh general-purpose subagent in its own scratch folder under
`~/lean/lean17-checks/review/`, brief built by `prep_review.sh` with HANDOFF rules 12 to 25 quoted
verbatim (`make_brief.py`); `~/.claude/agent-memory/` unchanged after each. All eight: PASS WITH
FINDINGS.

| review | module | findings | applied | not done (recorded here) |
|---|---|---|---|---|
| r1 | FrischWaughLovell | 5 MINOR | 2, 3 | 1 a general "rank = trace" lemma; 4 Lean witnesses of the dropped hypothesis; 5 one bullet per theorem |
| r2 | CovarianceDirections | 3 MINOR | 1, 2 | 3 a shorter integrability step |
| r3 | ResidualVariance | 3 MINOR | 1 | 2 prove it for any measure; 3 a weaker mean condition |
| r4 | Entropy | 3 MINOR | 1 | 2 a removable hypothesis of a private helper; 3 the closed simplex under support conditions |
| r5 | LikelihoodScore | 4 MINOR | 3, 4 | 1 drop the implied `p₀ < 1`; 2 allow `q = 1` |
| r6 | EffectiveSampleSize | 7 MINOR | 1, 3, 5, part of 4 | 2 drop the probability-measure instance; 6 a closed form; 7 move the helper, a shorter route |
| r7 | MutualInformation | 3 MAJOR, 4 MINOR | 1, 2, 3, 4, 5, 7 | 6 share two steps with `product_facts` |
| r8 | SourceCoding | 5 MINOR | 1, 2 | 3 the helper for any real `D > 0`; 4 a shared private lemma; 5 names |

Review files and sha256: r1 e36f0b11...97f540, r2 ab90ef78...af5c0bef, r3 da265a06...b471dc,
r4 f0687611...53cd6ad, r5 f92f3c45...a40c18e, r6 9e1163bd...569e2b, r7 0befda1c...85ba5e1,
r8 52d626c3...1063590.

Per-module theorem constants at `44ac1c0` (`env.getModuleFor?` under the axiom gate's `.thmInfo`
predicate, `Count.lean`): FrischWaughLovell 19, CovarianceDirections 19, ResidualVariance 3, Entropy
26, LikelihoodScore 19, EffectiveSampleSize 50, MutualInformation 8, SourceCoding 3. New constants:
30 by a census of the eight scratch proof files (`census/C1..C8.lean`, rule 27), written before any
whole-library gate (`census/prediction.txt`, 2235 predicted); the axiom gate then measured 2235
(order LEAN-16's close: 2205). A clean tree.

Gates on the clean tree at `44ac1c0` (`gates.sh g1`, every rc 0): `lake build` "Build completed
successfully (4017 jobs)." with 0 warning lines; "axiom gate PASS — 2235 theorem constant(s) under
[ClassicalLean]"; "vacuity gate PASS — no vacuous theorems in [ClassicalLean]"; "check_sorry PASS —
83 file(s) under ClassicalLean"; "banned_vocab_scan PASS — 83 file(s) under ClassicalLean +
ClassicalLean.lean, 0 hits"; "check_records PASS — 83 module(s) under ClassicalLean". check_sorry
fire test: a `sorry` planted in a scratch copy outside the repository gave rc 1, "check_sorry FAIL —
1 violation(s) across 83 file(s)", naming only the plant. `#print axioms` (`Axioms.lean`, rc 0): all
13 main theorems print exactly `[propext, Classical.choice, Quot.sound]` (counted by script). The
vacuity gate's budget was not changed.
