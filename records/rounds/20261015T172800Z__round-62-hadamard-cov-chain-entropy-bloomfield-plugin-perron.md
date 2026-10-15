# Round 62 — Hadamard for a covariance matrix, relative entropy along a chain, Bloomfield–Watson for a common mean, the plug-in compression score, Perron–Frobenius for a primitive chain (order LEAN-30)

Session: Claude Code `session_0148mpze7NidhsLJoJvBQsng` on DSMain, as dustin, executing order
`LEAN-30` (`records/orders/20261015T172700Z__claude-ai__order-lean30-hadamard-cov-chain-entropy-bloomfield-plugin-perron.md`),
batch 4 (items 96 to 100) of the plan `/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library-2.md`
(sha256 6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166), and its job 0 (five older
docstring lines, LEAN-29's review j0 finding 1 and review r92c's note), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `lean-30`, made from `origin/master` = MERGE =
`132e9d82a8e74944be325650fee9ba4134be76de` (order MERGE-1's pushed merge; equal to
`git ls-remote github master`). Lean and Mathlib v4.34.0. Nothing pushed. Evidence:
`~/lean/lean30-checks/` (outside the repository), `evidence.log` (UTC time, label, rc, prediction,
command per run). Plan: lane `lean/LEAN-30-PLAN.md` (sha256
f53f9e646bac6a412ca8b212b3704b73436bcf96996297025b1b51b16a0476c8), approved by Dustin on 2026-10-15
with three additions (claude-ai's ruling, store row 20261015-019). The lane file
`MATH-PLAN-library-2-bridges-2.md` is read at `0dea55c0…` (MERGE-1's row 157 appended), not the
order's `f0aa214a…`, by the ruling of store row 20261015-017.

First part written before any Lean file changed; completed after the work, below.

## Files this round changes

Module files, each spelled in full:

* item 96: `ClassicalLean/Probability/CovarianceDirections.lean` (extended; gains an import of
  `ClassicalLean.Algebra.HadamardInequality`);
* items 97 and 100: `ClassicalLean/Probability/FiniteChain.lean` (extended);
* item 98: `ClassicalLean/Statistics/GeneralizedLeastSquares.lean` (extended; gains an import of
  `ClassicalLean.Algebra.Kantorovich`);
* item 99: `ClassicalLean/InformationTheory/CompressionTest.lean` (extended; gains an import of
  `ClassicalLean.InformationTheory.Entropy` only if item 99 takes route (b));
* job 0: `ClassicalLean/NumberTheory/PrimitiveDivisor.lean` and `ClassicalLean/Analysis/Gruss.lean`
  (docstring and comment lines, and in PrimitiveDivisor at most one `example` appended after the
  last line; no theorem, definition, proof or existing `example` changes).

No new module; `ClassicalLean.lean` does not change. Also, as the order allows:
`tools/vacuity_reviewed.txt` (only if a helper is listed under job 2's 2c), `records/` (this
fragment, `records/orders/INDEX.md`, `records/CLAIMS.md`, the order's copy, and the new bridge
baseline `records/bridges/LEAN-30/`), `HANDOFF.md` and `ROADMAP.md` (job 3).

Records files written by this session's commands, not by the evidence helper (HANDOFF.md rule 32):
the order's copy (by `cp` from the lane inside `ev.sh --nolean`, label `order-copy`, its sha256
then checked equal to the order's,
`2452e0c6c9635f19b364e16ff315b9f0337450713b9ce8ad4578bb524b94a85d`), this fragment, the INDEX row
and the CLAIMS row (by the editor tools).

The vacuity gate is used as LEAN-29 left it. The standing rules of round 58 apply (witnesses apply
the theorem itself; the report tool is re-run and its summary lines reported), and so does the
bridge search's standing rule of round 55. Counts after MERGE are order MERGE-1's measured values
(4176 jobs, 3335 theorem constants, 128 modules; bridge baseline `records/bridges/MERGE-1/`), as the
order asks.

## Completed after the work

Items 96 to 100 of MATH-PLAN-library-2 are proved, no `sorry`, no new axiom, and job 0 is done.
**Narrowing: none.** **Wider than the plan's reading, five conditions** (the order's Goal; claude-ai's
rulings, Dustin's veto open): item 96 for any finite measure; item 97 with a stationary `π` that need
not be a law (no `π ≥ 0`, no `∑ π = 1`); item 100's uniqueness with no `P ≥ 0` and no `k > 0`; item
100's rate with no `k > 0`. **Also, as written in the order's statements, not a new change** (not
counted among the five; claude-ai's ruling, store row 20261015-019): item 97's `μ` need not sum to
`1`; item 100's rate takes any real `δ`, `μ` of any sign and any stationary `π` with `μ`'s total.
Neither stop rule fired: item 97 has no `π ≥ 0` and item 100's uniqueness no `P ≥ 0`. Item 99 took
route (a), the weighted arithmetic–geometric mean inequality, with no new import.

The statement review of HANDOFF.md rule 16 for these statements is the order's two cold reviews of
A2 to A5 with the plan's plan-fit check (lane `lean/LEAN-30-PLAN.md`, sha256
f53f9e646bac6a412ca8b212b3704b73436bcf96996297025b1b51b16a0476c8, section 3), closed by Dustin's
approval; no statement changed after it (each module review compared the statements with
Appendix A, word for word).

Commits on `lean-30` (from `132e9d8`; nothing pushed), with each module's cold review and confirming
passes (BLOCKER/MAJOR/MINOR; files under `~/lean/lean30-checks/reviews/`, sha256 of each `review.md`
by script):

* job 0, `ClassicalLean/NumberTheory/PrimitiveDivisor.lean` and `ClassicalLean/Analysis/Gruss.lean`:
  9f9a3d9; review j0 PASS WITH FINDINGS 0/2/5 (6e9ff2c624496721eda32c9c31d1d78dc17045139dfcb3cf288069d11d130215); fix 267ddc5;
  confirming pass j0c PASS WITH FINDINGS 0/0/2 (e29d68c08cc18ee31ca0842c494a21c6fa4ad825d7b6edfab3d6ac119c05cf83); fix 23edcdb;
  j0c2 PASS WITH FINDINGS 0/0/1 (ef40bfa556bd8247a44081b7eba5eb678af65e48b6232ee8100c3f10649b5dac); third fix, docstrings only, d3b1481
  (the order's rule 7: code-only comparison with a negative control, a rebuild with 0 warnings);
  fresh review j0c3 PASS (cd14bf35e23bdd56df7ff64a705ce3d97bc91c1f1fe157dec60eb2db175a18ac). Census of both modules before and after
  equal, name for name (PrimitiveDivisor 10 theorem constants, Gruss 2). The four PrimitiveDivisor
  passages were first written in `333b69a` (`git log -S`, label j0-logS); line 98's claim is now the
  `example` naming `Nat.emultiplicity_pow_sub_pow` and its `Int` twin; line 265's is "by hand";
  lines 346 to 350 are past runs with no file kept.
* item 96, `ClassicalLean/Probability/CovarianceDirections.lean` (now importing
  `ClassicalLean.Algebra.HadamardInequality`), `det_covMatrix_le_prod_variance`: 9107808; r96
  PASS WITH FINDINGS 0/0/4 (927f801320a500fbaa960de3c2a5b5577920252c850d01288bfd9b87879e284e); fix 1c77c14; r96c PASS WITH FINDINGS
  0/0/1 (692c78788a4c6eb23bb7e7316f577fdeffc10a80762a9170d78c4b016baf43ea), a records-only finding, answered in the evidence folder.
* item 98, `ClassicalLean/Statistics/GeneralizedLeastSquares.lean` (now importing
  `ClassicalLean.Algebra.Kantorovich`), `onesQuad_mul_onesInvOnes_le`: c3313ca; r98 PASS WITH
  FINDINGS 0/1/4 (383a5326a635e43b82a2324f4ed4c03b364b2e81787481151b488fef8c85431a); fix 090f28b; r98c PASS WITH FINDINGS 0/0/1
  (05facde9b088fc61fe8e1f89553db6fcce52023dcd0173c57c87e7a9d225bbf1), answered in the records: the module cites the plan's search by its
  script and line, and this fragment ties `row.X6` and `row.X16` (and `row.L3`, `row.L7`, `row.X8`)
  to order LEAN-30's run of the plan's checks, label `checks0` (2026-10-15T17:31:19Z), before any module
  changed.
* items 97 and 100, `ClassicalLean/Probability/FiniteChain.lean`,
  `relEntropy_vecMul_le_of_stationary`, `existsUnique_vecMul_eq_self_of_pow`,
  `sum_abs_vecMul_pow_sub_le_of_pow`: d7f8838; r97100 PASS WITH FINDINGS 0/1/6
  (0abb09b51675b1e9cc673ccf3abf774dbb4f76fbdd8f5e0df7ece953b289c3df); fix ece0ac5; r97100c PASS WITH FINDINGS 0/0/3
  (916222dcce944ca8194ecbe8a47b64cbaab6e026f7005c78dc22d7ab3ea92016); fix 84f2e30; r97100c2 PASS (c95ae19595bfc63f46a775ea28ce9766bed8f06a08dc85bd18463588ade89ecc).
* item 99, `ClassicalLean/InformationTheory/CompressionTest.lean`, `winRate`, `score_plugIn_le`,
  `measureReal_score_plugIn_ge_le` (two private helpers, `pow_mul_pow_le_winRate` and
  `measureReal_singleton_le_winRate`): 5c03b98; r99 PASS WITH FINDINGS 0/0/5
  (f4cb0c14d68113e4c97e80d5869a923c25015f446efb9a8fec3ae6843cacc1f8); fix bbad5cf; r99c PASS WITH FINDINGS 0/0/1
  (4ccefc5af1f7d62b4a42a02dadbb8b46f40bcc53f77eb3f606eadfef8024ff33), a records-only finding, answered in the evidence folder.
* documents (job 3), `HANDOFF.md` and `ROADMAP.md`: 6f6a7b1; d3 PASS WITH FINDINGS 0/1/5
  (01bc621110cc018e50cbece52052519edf37d78653706c6e3eb85f1db19e6e9a); fix 4d4ec55; d3c PASS WITH FINDINGS 0/0/3
  (c7423f644bf1a3401a693016970ef552c3f908c1776b769b7602fe512c6840c5); fix 3b293a1; d3c2 PASS (014e346f4c97efff4b01b2128fc6c8dab246aa45d12188275d73268ddad58768). HANDOFF.md
  §6 gains rule 35, from the order's rule 8.
* the bridge baseline `records/bridges/LEAN-30/` (job 4a, records only): 6dafe23.

Seven witnesses, in round 58's standing form with VACUITY-3 ruling 3's two rule-3 cases, each
checked by its module's reviewer: items 96, 97, 98, 99 twice and 100 twice. Item 99's second
witness meets its hypotheses at the order's `α = 1/2`, where the rejection set is empty (said in its
docstring). Every reviewer answered rule 1: no new conclusion is a recursive all-`True` predicate;
the two private helpers carry content. No vacuity-list entry was added. `~/.claude/agent-memory/`
hashed before the first review and after the last: equal (labels amhash-before, amhash-after).

**Theorem constants, per module** (census of each module's source, `.thmInfo` under
`ClassicalLean`, labels `census_B_old_*`, `census_B_new_*`): CovarianceDirections 42 → 43,
GeneralizedLeastSquares 12 → 13, FiniteChain 12 → 15, CompressionTest 18 → 23 (the four
hand-written and `winRate._proof_1`), PrimitiveDivisor 10 → 10, Gruss 2 → 2: 3335 + 10 = 3345.
Predicted blind by Method A at 3352, range 3346 to 3361 (a miss of 7, outside the range: the four
`field_simp` calls made no helper here, 5 estimated; `winRate` made 1 abstracted proof, 2
estimated), and by Method B at 3345, in `pred/prediction.txt` (878dff3c19ba4437eb2ae62976bc9b67d62af33a49345211706212e6bf430df0).

**Records follow the clock** (HANDOFF.md rule 18):

* rule 8's probes. Names reached in the drafts without a `#check` before the first draft that used
  them, probed after it (all resolve): item 96's witness `MemLp.of_discrete` and `uniformOn`
  (probed in the same run as the draft, i96-1); item 98's `one_pos` (p98-late); item 100's
  `pow_succ'`, `sq`, `Finset.sum_sub_distrib`, `mul_zero`, `sub_zero`, `one_mul`, `Nat.cast_zero`,
  `Matrix.vecMul`, `dotProduct` (p100-late; `Nat.cast_zero` not probed, later removed); item 99's
  `mul_div_cancel₀`, `mul_nonneg`, `Fin.prod_univ_two`, `List.IsPrefix.eq_of_length`, `le_trans`,
  `add_zero`, `Ne.symm` (p99-late); `LE.le.trans_eq` and `LE.le.lt_of_ne`, by dot notation in items
  96, 97 and 99 (pdot-late). Several commit messages overstate or understate their evidence in
  smaller ways (9f9a3d9, c3313ca, d7f8838, 5c03b98, 1c77c14, ece0ac5, 6f6a7b1, 4d4ec55); each is
  recorded in the evidence folder's `misses.md` with what the outputs show; no message is
  rewritten.
* the four item reviewers read the briefs' "none after 01:45 EDT" as already past at 13:53 EDT and
  elaborated no Lean file; their reviews rest on reading and on the session's build outputs.
* items 97 and 100's module build `i97-100-build` failed (rc 1) on item 97's witness, which had not
  been elaborated before it went into the module (`norm_num at h ⊢`), and on long lines; fixed before
  the commit (fix-fc1, i97-100-build2).
* the plan's checks at setup (`checks0`, 2026-10-15T17:31:19Z): 180 of 232, not the predicted 186; the
  six further misses are the library searches of rows E2, H4, H5 (two lines), K1 and K3, the five
  items order CLOUD-MATH-1 landed, whose modules now hold those words. No row 96 to 100 line missed.

**End checks** (job 4, on the clean tree):

* 4a, the bridge search at 4d4ec55 against `records/bridges/MERGE-1/`, under the 12G cap (label
  `bridges`, rc 1): 2556 pairs, 607 shape candidates, N = 127; 28 new (18 pairs, 10
  shapes), 41 gone (pairs). Predicted (`pred/pred-bridges.md`, c538642d5861f76bf788174f4f02b6d20bdefb2dd8e83ea42cf2ce7e955e1ac2): the 10
  new shapes exactly, 0 shapes gone, the 2 pairs the new import edges relate gone (ranks 123 and
  128), 5 to 60 new pairs (18); 0 to 15 pairs gone by the document-frequency cut, a miss: 39, as
  `div_pow`, `add_pos'` and `Fintype.card_pos` crossed the cut. No real bridge (checked by hand,
  `bridges/review.md`, 7d16b699f0cf56ca9d5cd8f626326c9bb50ddc72fa8e881c57c858a3213ad9dc); no row 158; the lane file is unchanged.
* 4b, the report tool at 6dafe23, under the cap (label `report-after`, rc 0):
  self-test 0 mismatches; 1848 written theorems; section A 1071 (0 close, 1032 open, 39 dependent);
  section B 777 (16 close: 15 by `simp`, 1 by `positivity`; 761 open); section C 34 Prop-valued, 0
  recursive; no `CLOSES` line names a theorem of this order. All as predicted
  (`pred/pred-gates.md`, 6c8058a3d07065e4095a3e51816a4c9b4dad39c780ed750646bcf32ffc573d88).
* 4c, the six gates at 3b293a1: build rc 0, 4176 jobs, 0 warnings; AxiomGate PASS
  3345, 0 scoped exceptions; VacuityGate PASS (1 reviewed helper, 0 VACUOUS-PENDING, 0 run-outs, no
  UNCHECKED, no new flag), its tests 89 / 47 flagged / 3 UNCHECKED as expected / 0 mismatches;
  check_sorry PASS 128; check_records PASS 128; gate 7 (`~/lean/recheck/run-recheck.sh 3b293a1 ~/lean/classical-lean-paper-crypto`, under the cap, label `g7`, rc 0): ALL PASSED for 3b293a1, 4176 jobs, 128 modules 0 failed, 91038 declarations with no errors, the three standard axioms, 3345 theorems under `ClassicalLean`, the planted fault named (`LogDrag.mean_log_one_add_le`); 21:14.53, 4754808 KB. Every gate as predicted. Also,
  not a gate, `tools/banned_vocab_scan.py`: PASS, 0 hits. Commits after the gates touch only
  `records/`.
