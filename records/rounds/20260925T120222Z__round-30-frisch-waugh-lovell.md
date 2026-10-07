# Round 30 — The Frisch–Waugh–Lovell theorem: the `X₂`-coefficients of `y` on `[X₁ X₂]` are those of `M₁ y` on `M₁ X₂` (order G-10, J3)

Session: Claude Code `session_01LSEckQnr5DiDZ1uDaGnUiT` on helios, executing order `G-10`
(`records/orders/20260925T060100Z__claude-ai__order-g10-wolstenholme-fwl.md`), job J3, in
`ClassicalLean/Statistics/FrischWaughLovell.lean`. Lean and Mathlib v4.34.0. Evidence:
`~/work/_bump-evidence/g10/`. Times are UTC, from `evidence.log`. The gate numbers for J3's commit
are `land.sh check`'s, on the tree with the change in place; the clean-tree numbers after it are
recorded at the records step. The order's Close (steps 1–3) is an addendum to this round.

## Searches, junk cells and statements

**Searches** (rule 21; J1 item 11, `searches_row12.sh`/`searches_shape.sh`; `item11b-row12`
08:22:06Z, `item11b-shape` 08:23:16Z): prior art **0** — no residual-maker / annihilator matrix, no
`leastSquares`, no Frisch/Waugh/Lovell or partial-regression statement in Mathlib (new); the
block-matrix and Schur-complement lemmas the route needs are present
(`Data/Matrix/ColumnRowPartitioned.lean`, `LinearAlgebra/Matrix/SchurComplement.lean`,
`NonsingularInverse.lean`). The 30 `#check` probes of §0 row 10's names all resolve
(`item11-elab-fwl` 08:20:07Z: rc 0, 10 `sorry` warnings and nothing else). `IsIdempotentElem` may
exist generally (noted; the module proves `M₁ * M₁ = M₁` directly).

**Junk cells** (exact; every line predicted first; `fwl_cells.py` sha256 `e442b8e6…c896`,
`fwl_side_cells.py` sha256 `d29ac6d8…7a1b`; `item11d-fwl` 08:29:09Z): over 400 random exact trials
(`n ≤ 7` rows, `k₁, k₂ ≤ 3` columns), the 239 with `Xᵀ X` invertible give **0 failures** of (F1),
(F2), (F3), and 0 of (F4) over 228 such trials with a fresh seed; side facts 0 failures — (S1)
`M₁ᵀ = M₁` and (S2) `M₁ * M₁ = M₁` over every `2×1`/`2×2` matrix in `{−1,0,1}` (90 cells, singular
included), (S3)–(S5) over 672 cells. The witness `X₁ = 0`, `X₂ = (1,1)`, `y = (1,3)` gives left
`[0]` (`Xᵀ X` singular, `leastSquares = 0`) and right `[2]` (`M₁ = 1`, `leastSquares (1,1) *ᵥ y = 2`).
Hypotheses dropped, first failing cell in enumeration order: (S3) without its hypothesis fails 32 of
90, first at `X₁ = [[−1,−1],[−1,−1]]`; (S4) 9 of 81, first at `X₁ = 0, X₂ = (−1,−1)`; (S5) 25 of 81,
first at `X₁ = X₂ = (−1,−1)`. A fact the cells found that the statements do not use: when `Xᵀ X` is
singular but `X₁ᵀ X₁` a unit, both sides of (F1) are `0` in all 109 such trials (no witness in 2000
random tries), so (F1) plausibly holds under the weaker `IsUnit (X₁ᵀ X₁).det` alone [inferred, not
proved] — the module's docstring records this as a remark, left for a later order.

**Rule 21/31**: the cells ran in J1, before any J3 statement was drafted to a file
(`item12-rule31-gate` 08:30:20Z).

**Statements, reviewed before any proof** (rule 16; the authoritative returned text is
`reviews/stmt-j3.journal.md`, sha256 `b51976d6…fa8f`; rule 33, the saved `reviews/stmt-j3.md`
differed by 59 bytes and the journal wins):

> VERDICT: ACCEPT-WITH-CHANGES

> No BLOCKER and no MAJOR. One MINOR naming change is recommended (a `_mul_self_` name that means

The recommended renames were applied: (S3) `residualMaker_mul_self_eq_zero → residualMaker_mul_eq_zero`
(finding 1), and (S1) `residualMaker_transpose → transpose_residualMaker` (finding 2, the Mathlib
`transpose_` prefix). No content changed; the eleven declarations elaborated under rule 20's flags
with 10 `sorry` warnings and nothing else (`item11-elab-fwl`). The statements are the order's §J3.

## Proofs

**The route** (order §0 row 10, derived here from the normal equations `GaussMarkov` has;
`GaussMarkov` read-only):

- **def** `residualMaker X₁ := 1 - X₁ * leastSquares X₁` — the annihilator `M₁`.
- **(S1)** `transpose_residualMaker`: `M₁ᵀ = M₁`, from `transpose_nonsing_inv` and `simp` (no hypothesis).
- **(S2)** `residualMaker_mul_self`: `M₁ * M₁ = M₁`, `by_cases` on `IsUnit (X₁ᵀX₁).det`
  (`leastSquares_mul_self` on the unit branch, `leastSquares_eq_zero_of_not_isUnit_det` on the junk
  branch), `noncomm_ring`/`abel` (no hypothesis).
- **(S3)** `residualMaker_mul_eq_zero`: `M₁ X₁ = 0` under `IsUnit (X₁ᵀX₁).det`, from
  `leastSquares_mul_self`.
- **(S4)** `isUnit_det_transpose_mul_self_left`: from the unit Gram of `[X₁ X₂]`, `mulVec` is
  injective (`mulVec_injective_iff_isUnit`), hence `fromCols`-mulVec is, hence `X₁`-mulVec is (via
  `Sum.elim u 0` and `fromCols_mulVec_sumElim`), so `X₁ᵀX₁` is `PosDef`
  (`PosDef.conjTranspose_mul_self`) and a unit. (`omit [DecidableEq ι] in`, since its statement has
  no identity matrix.)
- **(S5)** `isUnit_det_transpose_mul_self_residualMaker`: the Schur complement. `(M₁X₂)ᵀ(M₁X₂) =
  X₂ᵀX₂ − X₂ᵀX₁ ⅟(X₁ᵀX₁) X₁ᵀX₂`, and `det [Xᵀ X in blocks] = det(X₁ᵀX₁)·det((M₁X₂)ᵀ(M₁X₂))` by
  `det_fromBlocks₁₁`, so `IsUnit.mul_iff` extracts the second factor. (`set_option
  linter.style.haveILetI false in`, because the `letI : Invertible (X₁ᵀX₁)` is genuine data — it
  carries `⅟` — required by `det_fromBlocks₁₁`; a style linter, not soundness, scoped to this one
  theorem.)
- **(F1)** `leastSquares_fromCols_mulVec_inr`: the normal equations
  (`transpose_mulVec_sub_mulVec_leastSquares`) split into blocks (`transpose_fromCols`,
  `fromRows_mulVec`), the residual `r` is orthogonal to the columns of `X₁` and `X₂` (`hr1`, `hr2`),
  so `M₁ r = r`; then `(M₁X₂)ᵀ(M₁X₂) β₂ = (M₁X₂)ᵀ(M₁ y)` (using `M₁ X₁ = 0`), and the least-squares
  candidate solves the same equation (`mul_nonsing_inv`, guarded by (S5)), cancelled by the
  injectivity of the unit Gram.
- **(F2)** `leastSquares_fromCols_mulVec_inr'`: (F1) with `y` on the right, via the absorption
  `leastSquares (M₁X₂) * M₁ = leastSquares (M₁X₂)` (because `(M₁X₂)ᵀ M₁ = (M₁X₂)ᵀ`, from (S1)/(S2)).
- **(F3)** `toRows₂_leastSquares_fromCols`: the matrix form, from (F2) evaluated at the basis
  vectors `Pi.single j 1` (`Matrix.mulVec_single`, `Matrix.toRows₂_apply`).
- **(F4)** `residual_eq_residualMaker_sub`: the residuals agree, from (F1), (S3) and the same
  `r`-machinery.
- **the witness** `not_forall_leastSquares_fromCols_mulVec_inr`: at `X₁ = 0`, `X₂ = !![1;1]`,
  `y = ![1,3]`. `leastSquares (fromCols 0 X₂) = 0` (its Gram has a zero row,
  `Matrix.det_eq_zero_of_row_eq_zero`), so the left side is `0`; `residualMaker 0 = 1` and
  `leastSquares !![1;1] = !![1/2, 1/2]` (`GaussMarkov`'s `leastSquares_ones_two`), so the right side
  is `2`; `0 ≠ 2`.

**Dependency graph as proved** (Done-means 2, recorded as proved where it differs from the order's):
(F1)←(S1)–(S5); (F2)←(F1),(S1),(S2); (F3)←(F2); (F4)←(F1),(S3),(S4); (S5)←(S1),(S2),(S4); (S1),
(S2),(S3),(S4) and the witness on nothing else in J3. The order predicted (F4) on (S1)–(S2),(S4);
as proved it uses (S3) (`residualMaker_mul_eq_zero`) and (S4), through (F1). Theorem order in the
file is the proved order (vector forms first, matrix form last), not the skeleton's — a
reordering, not a content change (the post-proof review notes this).

**The census (rule 27), as a difference** (`g10-census-j3-modthmcount`, `g10-census-j3-listthms`):
the module contributes **17 theorem constants** (`ClassicalLean.Statistics.FrischWaughLovell 17`),
**0 private** (every declaration is public; `residualMaker` is a public `noncomputable def`). Library
totals: `MODULE-THM-COUNT total 1578 → 1595` (+17), `modules 51 → 52`; `#COUNTS raw 1578 → 1595,
filtered 895 → 906` (+11 — the eleven declarations), `private 209 → 209` (unchanged). Predicted by
hand "1578 + d, d ≥ 11"; the 17 is the eleven declarations plus six `simp`/`ring`/`abel`
auxiliaries. Axioms: all within the kernel trio (gate 2 `AxiomGate`).

**Post-proof review** (rule 13; `reviews/post-j3.md`, sha256 `e326d4e2…e7ec`; dispatched to an
`adversarial-critic` subagent, its returned text saved from the hand-back and hashed):

> VERDICT: PASS

> All 11 statements (residualMaker def + 10 theorems, including variable block and `omit`) match the accepted skeleton exactly [...] The witness arithmetic was verified by hand and matches the docstring (LHS=0, RHS=2). The one linter suppression is legitimate and non-soundness. The sole finding is a documentation ambiguity that does not touch the mathematics, so it is MINOR and the artifact is ready to commit.

> Hidden cheats — NONE. No `native_decide`, no `axiom`, no `sorry`/`admit`, no `maxHeartbeats`.

The one finding (`post-j3` [1], MINOR) was cosmetic: the module docstring's empirical remark cited
"400 exact random trials … no counterexample in 2000 tries" — two counts a reader cannot reconcile;
it was reworded to "In all 109 of 2000 random exact trials where `Xᵀ X` is singular but `X₁ᵀ X₁` is a
unit" (the order §0 row 9's own figures). No statement or proof line changed, so rule 29 has nothing
to check; the module was re-elaborated after the edit (rc 0, 0 warnings). The reviews were dispatched
with the Agent tool (not a workflow); each subagent's authoritative returned text was extracted from
its hand-back and hashed (rule 33).

**Landing.** The landed file is the reviewed file, byte for byte (`cp` then `sha256 bda42929…4005` =
the work file; R28). One import line added to `ClassicalLean.lean`
(`import ClassicalLean.Statistics.FrischWaughLovell`, alphabetical, after `CramerRao`). `lake build`:
rc 0, **0 warnings**, 3804 jobs (gate 1). Gate 6 fire-tested (rule 18): with the module and import in
place but before this fragment, `check_records` FAILed (`g10-firetest-records-j3`: 52 modules, 1
UNRECORDED `ClassicalLean/Statistics/FrischWaughLovell.lean`); it passes once this fragment names the
module. The Lean-side import closure (J1 item 7, `item7-gaussmarkov`): `GaussMarkov` loaded alone
reaches `GaussMarkov`, `Analysis.Matrix.Order` and `LinearAlgebra.Matrix.SchurComplement` (positive
controls), and **not** `Data.Matrix.ColumnRowPartitioned` (negative control fires) — which is why the
module imports `ColumnRowPartitioned` (and `SchurComplement`) explicitly beside `GaussMarkov`.

**Per-module count**: `Statistics/FrischWaughLovell` 0 → 17 theorem constants (private 0 → 0;
filtered 0 → 11), from the census of the landed text. `GaussMarkov`'s own census is unchanged.

**Commit**: `b489d5c` (J3, `j3-commit`).

**After the landing** (clean tree at `b489d5c`): the six gates pass — `lake build` rc 0, 0 warnings,
3804 jobs; `AxiomGate` PASS; `VacuityGate` PASS; `check_sorry` PASS; `banned_vocab_scan` PASS, 0
hits; `check_records` PASS, 52 modules, 25 records files, 1 exemption. Census `raw 1595 filtered 906
private 209`, `modules 52`. The type dump against J1's baseline (`g10-typediff`,
`g10-before/typedump.jsonl` vs the landed `TypeDumpPI` dump): `DIFF removed=0 added=109 changed=0
proof_only=0` — only additions across both G-10 modules, so `GaussMarkov`, `Catalan` and every prior
declaration are unchanged up to proof irrelevance (rule 25). Appendix A (`g10-after-j3-*`): declgraph
1782 constants, **islands 2** (`CompositumDiscriminant`, `Tolerance`), `FrischWaughLovell usedBy=0
uses=1` (`GaussMarkov`), `GaussMarkov usedBy=2 uses=0`; `pairs.py` `modules=52 edges=85 pairs=97`;
`DupCheck: 5 TWIN, 0 SWAP`.

## Addendum — the Close check (order G-10's Close step 3)

Two fresh subagents (the Agent tool, not a workflow) checked every Done-means of J1, J2, J3 and the
Close against `git diff 3b3aad8^..HEAD` and the landed tree, each returning a report saved and hashed
(rule 33): `reviews/close-A.md` (J1 + J2, sha256 `ed6ed6d6…d046`) and `reviews/close-B.md` (J3 +
Close, sha256 `5728f157…2858`). Both verdicts are PASS with no findings:

> VERDICT: PASS

> Every J1 and J2 Done-means that is observable from git + the landed files holds. No discrepancy found between the round-29 fragment, the J2 commit message, and the landed tree.

> No BLOCKER, MAJOR, or MINOR findings. Every J3 and Close Done-means holds against the landed files and git history. All five review passes run.

Checker A recomputed the four J2 `example`s, traced the (W1)–(W7) dependency graph against the
routing, and confirmed R28 (the landed `Wolstenholme.lean` hash `4365a5b5…7ee2` equals the tested
work file) and both J2 review sha256. Checker B recomputed the FWL witness (`0 ≠ 2`), judged the one
`set_option linter.style.haveILetI false` legitimate data-carrying use, re-ran `quotecheck.py` on
this fragment (`missing_segments=0`), and confirmed the Appendix-A numbers chain 51 → 52 modules and
declgraph 1764 → 1782. Both re-ran the three non-`lake` gates (`check_records`, `check_sorry`,
`banned_vocab_scan`) at rc 0; the `lake`-gated gates (build, `AxiomGate`, `VacuityGate`, the type
dump) were taken as recorded, since subagents do not run `lake`. One observation, not a defect
(Checker B): this fragment's dependency-graph line records F3←F2 and narrates the F4 divergence from
the routed graph in prose — Done-means 2 is met, the as-proved graph is recorded.

The `INDEX.md` row is set to closed by the commit that carries this addendum (the two-commit ruling,
`HANDOFF.md` §6).
