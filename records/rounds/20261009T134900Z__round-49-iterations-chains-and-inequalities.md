# Round 49 — Jacobi iteration, Newton's method, finite chains, Wald's identity, Fano's and Hadamard's inequalities, the binomial variance, and Mathlib's relative entropy on a finite set (order LEAN-21)

Session: Claude Code `session_019DbYoaqCsdYF7tW4YCkR4P` on DSMain, as dustin, executing order
`LEAN-21` (`records/orders/20261009T134800Z__claude-code__order-lean21-iterations-chains-and-inequalities.md`), batch 5 of the plan
`/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md` (sha256
a3006a18bb59a1228f69b5426beb12bb9ec9f9e79ba61c2bcf91563a14665216), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `paper-crypto-16`, made from `origin/master` =
`59a4749`. Lean and Mathlib v4.34.0. Nothing pushed. Evidence: `~/lean/lean21-checks/` (outside the
repository), `evidence.log` (time, label, rc, prediction, command per run).

First part written before any module change, so that gate 6 finds the new modules' paths before
their commits; completed after the work, below.

Modules this round plans to change or add (as the claim row):

* `ClassicalLean/Analysis/JacobiIteration.lean` — new module, item 32; added to `ClassicalLean.lean`.
* `ClassicalLean/Analysis/NewtonMethod.lean` — new module, item 33; added to `ClassicalLean.lean`.
* `ClassicalLean/Probability/FiniteChain.lean` — new module, item 34; added to `ClassicalLean.lean`.
* `ClassicalLean/Probability/FairGame.lean` — item 35 (Wald's identity).
* `ClassicalLean/InformationTheory/Fano.lean` — new module, item 36; added to `ClassicalLean.lean`.
* `ClassicalLean/Algebra/HadamardInequality.lean` — new module, item 37; added to `ClassicalLean.lean`.
* `ClassicalLean/Probability/BinomialVariance.lean` — new module, item 38 (Mathlib's `proof_wanted`); added to `ClassicalLean.lean`.
* `ClassicalLean/Probability/RelativeEntropyGrowth.lean` — item 39.

Mathlib re-checked before the records were written (`~/lean/lean21-checks/search.out`,
`search2.out`): none of the eight items is in Mathlib v4.34.0, so none is dropped. Item 38 is a
`proof_wanted` there (`Wanted/Probability/Distributions/Binomial.lean`, line 20), proved here with
its statement unchanged. Statements elaborated with `sorry` before this fragment: `st2.out`, rc 0,
24 `sorry` warnings, nothing else (`st1` had 5 lint warnings besides; fixed).

## Completed after the work

All eight items of batch 5 are done (32 to 39). On Dustin's instruction during the work, every
citation of a paper nobody read is author, title and year only (Jacobi 1845, Doeblin 1938, Wald
1944, Fano 1961, Hadamard 1893); Sauer's section 2.5 and Levin, Peres and Wilmer's Theorem 4.9,
which the citation check's subagent saw, keep their sentences.

Commits on `paper-crypto-16` (made from `origin/master` = `59a4749`; nothing pushed):

* `e2e616b` records before the work (this fragment's first part).
* `6a1a13f` `ClassicalLean/Analysis/JacobiIteration.lean`, item 32.
* `81329ef` `ClassicalLean/Analysis/NewtonMethod.lean`, item 33.
* `a7dbc28` `ClassicalLean/Probability/FiniteChain.lean`, item 34.
* `90a754d` `ClassicalLean/Probability/FairGame.lean`, item 35.
* `2bf72e6` citations in `ClassicalLean/Analysis/JacobiIteration.lean` and
  `ClassicalLean/Probability/FiniteChain.lean` cut to author, title and year (docstrings only).
* `54f5fee` `ClassicalLean/InformationTheory/Fano.lean`, item 36.
* `0342f74` `ClassicalLean/Algebra/HadamardInequality.lean`, item 37.
* `e18a442` `ClassicalLean/Probability/BinomialVariance.lean`, item 38 (Mathlib's `proof_wanted`
  `variance_of_hasLaw_binomial`, statement unchanged; nothing offered to Mathlib).
* `7a9813e` `ClassicalLean/Probability/RelativeEntropyGrowth.lean`, item 39.

Changes from the drafted statements (`~/lean/lean21-checks/Statements.lean`, `st2.out`):
`norm_jacobiIterate_sub_le` lost `0 ≤ ρ` (it follows from the other hypotheses);
`abs_sub_sub_mul_le_of_lipschitzOn` was renamed `abs_sub_sub_mul_le_half_mul_sq` (review r33);
`integral_stoppedValue_eq_mul` takes a finite measure, not a probability measure (review r35 asked
for this to be recorded); added, not drafted: `jacobiStep_sub_apply`, `sum_abs_vecMul_pow_le`,
`vecMeasure_singleton`, `measureReal_vecMeasure_singleton`, `measureReal_vecMeasure_univ`, the
`IsFiniteMeasure (vecMeasure p)` instance, and eight private helpers. The order's row names that
changed: item 34 `norm_vecMul_pow_sub_le` is `sum_abs_vecMul_pow_sub_le` (the distance is a sum of
absolute values, not Lean's norm); item 39's data processing is `relEntropy_vecMul_le_of_klDiv`.

Cold reviews, one per module before its commit, each by a fresh general-purpose subagent with no
persistent memory, in its own scratch folder (`~/lean/lean21-checks/review/`); all eight PASS WITH
FINDINGS, no BLOCKER. MAJOR findings: r32 (the rate `ρ ^ k` had been called unsourced; it is the
standard bound, now said so with no unchecked theorem number) and r33 (a docstring stated a rate
`tendsto_newtonIterate` does not export); both applied. Not applied, and why: r32's repeated
four-line block and r39's two refactors (each would add a declaration after the prediction);
r37's optional `[Nonempty n]` removal; the order's names kept (r32, r35, r38); r39's finding that
`ClassicalLean/InformationTheory/Channel.lean`'s "Relation to Mathlib" paragraph is now out of
date (that file is outside this order's claim; reported to Dustin). The fragment's table of hashes
(sha256, first 16 hex digits, computed by script, `review-hashes.txt`):

| review | brief sha256 | review sha256 |
|---|---|---|
| r32 | `13251e67ae28fc70` | `e1c4008e66036011` |
| r33 | `aad1ef62a7c7324d` | `e1745a41d9ddcb92` |
| r34 | `fc58ad134a78b9dc` | `d67e44d4cde724e0` |
| r35 | `3dd95d2e916a74e0` | `a2ac59c9fcf969fa` |
| r36 | `bcd6c096ba9b9705` | `bf9e2195a64345b4` |
| r37 | `c90f71cc37cdbd79` | `0b71cd06c6ea8cde` |
| r38 | `eea1063c7f4cbf49` | `223ca4911c76545c` |
| r39 | `e69e8295cdff4874` | `f7311f14b1df4b9c` |

`~/.claude/agent-memory/`: the sha256 of every file was the same before the first review and
after the last.

Gates on the clean tree at `7a9813e` (`~/lean/lean21-checks/g1-*.out`): `nice -n 19 lake build`
rc 0, 4073 jobs, 0 warning lines; AxiomGate PASS, 2516 theorem constants; VacuityGate PASS;
check_sorry PASS, 102 files; banned_vocab_scan PASS, 102 files; check_records PASS, 102 modules.
check_sorry fire test on a copy with one planted `sorry`: rc 1, exactly that one violation.
`#print axioms`-style check by script on the 38 new hand-written declarations: 38 of 38 depend on
exactly `[propext, Classical.choice, Quot.sound]` (`axioms.out`).

Theorem constants: 2516 against 2442, so 74 new. Predicted before any gate (`prediction.txt`,
14:16:02Z), from the source and not with the gate's counter: 2497, range 2488 to 2506: a miss by
19. Name by name (`reconcile-names.txt`, every theorem constant in the eight modules; 17 of them
existed at `59a4749`): 38 hand-written (predicted 38, hit; the instance is stored as a theorem),
5 `eq_1` (predicted 5, hit), 28 `_simp_1_k` (predicted 12: they come from `field_simp`, 7, 7 and 8
in its three theorems, and also from `simp only [← lemma]`, 4, 1 and 1 in three FiniteChain
theorems, which the prediction left out), 2 `congr_simp` for `jacobiStep` and `jacobiIterate`
(not predicted), 1 `vecMeasure._proof_1` (not predicted). 38 + 5 + 28 + 2 + 1 = 74.

Gate 7, `~/lean/recheck/run-recheck.sh 7a9813e ~/lean/classical-lean-paper-crypto`: rc 0, last line
`ALL PASSED for 7a9813ea5510b7573f49eed9cdf8bf688fe1efca` (`g7a-recheck.out`): 4073 jobs;
leanchecker 102 modules, 0 failed; nanoda checked 88315 declarations with no errors, only the
three standard axioms; 2516 theorems under the ClassicalLean name, counted from the export (equal
to AxiomGate); the planted wrong proof was rejected and named
(`ClassicalLean.Analysis.LogDrag.mean_log_one_add_le`). Predicted before the run: rc 0, 4073
jobs, 102 modules, 2516, 85000 to 90000 declarations: all hit.

Not touched: anything under `~/trading`; nothing under `~/lean/recheck` was edited (its script was
run). No push.
