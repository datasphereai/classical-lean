# Round 69 — batch 3 of the API-credit drafts and five VACUITY-3 witness rows (order LEAN-33)

Session: Claude Code `session_01PW3tftVKo5SFPJdJKDaHsZ` on DSMain, as dustin, executing order
`LEAN-33` (`records/orders/20261021T012500Z__claude-ai__order-lean33-steepest-pl-mirror-conjugate-projected-witnesses.md`),
in the worktree `~/lean/classical-lean-paper-crypto` on branch `lean-33`, made from `origin/master` =
`04e4a38` (MERGE-2's last commit, equal to `git ls-remote github master`). Lean and Mathlib v4.34.0.
Nothing pushed. Evidence: `~/lean/lean33-checks/` (outside the repository), `evidence.log` (UTC
time, label, rc, prediction, command per run). Plan: lane `lean/LEAN-33/plan.md` (sha256
2a60a3585f4ed8f707ea79a698f601f35789e09ea2e6fe662df80539c595b245), approved by Dustin on
2026-10-20 (EDT); the first Setup 1 line of `evidence.log` is at 2026-10-21T01:22:40Z.

Dustin's rulings with the approval: (1) `pgrep -a lean` matches the Samba process
`smbd: cleanupd`, so before each whole-library run both `pgrep -a lean` and `pgrep -ax lean` are
logged and "no Lean running" is judged by the exact match and by reading the process names;
(2) item 134: claude-ai's ruling stands, `hKc : IsClosed K` is removed and the verdict is
GENERALIZED (accepted by Dustin at 2026-10-20 21:17 EDT); (3) item 116: job 1 checks in a scratch
file whether the draft's set `{y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1}` equals the library's
`closedSimplex ι` by `rfl`; if it does, the theorem is stated with `closedSimplex ι` and the change
is recorded here and in the report; if not, the draft's set stays and this fragment says so.

Order CLOUD-MATH-3 runs at the same time in a Claude Code cloud session on GitHub branch
`cloud-math-3`; it changes no module of this round. Whichever of the two reaches master second is
merged by a later order.

First part written before the work; completed after it, below.

## Files this round changes

Module files (no module is added):

* item 111: `ClassicalLean/Algebra/Kantorovich.lean`;
* items 112 and 134: `ClassicalLean/Analysis/GradientDescent.lean`;
* item 116: `ClassicalLean/Analysis/ExponentialWeights.lean` (new import line
  `import ClassicalLean.InformationTheory.Entropy`);
* item 117: `ClassicalLean/Analysis/ConvexConjugate.lean` (new import line
  `import ClassicalLean.Simplex.LogSumExp`);
* VACUITY-3 rows 7 and 8: `ClassicalLean/Probability/LikelihoodScore.lean`;
* VACUITY-3 rows 9 and 10: `ClassicalLean/Probability/EffectiveSampleSize.lean`;
* VACUITY-3 row 67: `ClassicalLean/Probability/GlivenkoCantelli.lean`.

Also changed: `records/CLAIMS.md` and `records/orders/INDEX.md` (this order's rows appended at the
bottom), this fragment, the order's copy, `HANDOFF.md` sections 1 and 4, `ROADMAP.md` (section
1.26), the new bridge baseline `records/bridges/LEAN-33/`, and `tools/vacuity_reviewed.txt` only if
a helper is listed. No other `.lean` file, no other import line, nothing else under `tools/`,
`.github/` or `records/rules.toml`; `HANDOFF.md` section 6 untouched.

**MERGE-2's INDEX and CLAIMS rows are not touched here** (order LEAN-33, rule 6):
`records/README.md` rule 2 gives the next order's records commit MERGE-2's push, and
CLOUD-MATH-3's records commit on its branch carries it, so the push is recorded once. The later
merge of `lean-33` and `cloud-math-3` must take CLOUD-MATH-3's side for those two rows and append
LEAN-33's rows after it (both branches append rows at the bottom of INDEX and CLAIMS, so those files
conflict). The other places the later merge must handle: `tools/vacuity_reviewed.txt` (if this
round lists a helper), `ROADMAP.md` section 1.26, and `HANDOFF.md` section 1's last paragraph.

Records files written by this session's commands, not by the evidence helper (HANDOFF.md rule 23):
the order's copy (by `cp` from the lane, through `ev.sh --nolean`, label `records1`, its sha256
checked equal to the order's), this fragment, the INDEX row and the CLAIMS row (written with the
Write tool into the evidence folder, hashed by `hl.sh`, and copied or appended by `records1.sh`
through `ev.sh --nolean`, label `records1`).

## Completed after the work

Times are UTC (the evidence log's clock), all on 2026-10-21. Setup ran from 01:22Z to 01:29Z; job 1
from 01:29Z to 01:48Z; job 2 from 01:48Z to 02:26Z; jobs 3 and 4 from 02:26Z to 02:37Z; job 5 from
02:37Z to 03:07Z. Every prediction file was written and hashed before the runs it predicts
(`pre/`, `pred-setup`, `pred-records`, `pred-rfl116`, `pred-job1`, `pred-census`, `pred-closure`,
`pred-main`). Two header times in them are wrong, not their order: `pred-setup.md` says "about 21:50
EDT" and was written about 21:24 EDT on 2026-10-20 (01:24Z); `pred-main.md` says "about 22:35 EDT"
and was written 22:30 EDT (02:30Z), before the documents (review docs, note 4).

Dustin's three rulings with the approval (above) were applied: `pgrep -a lean` and `pgrep -ax lean`
logged before every whole-library run, "no Lean running" judged by the exact match (each
`pgrep -a lean` showed only `smbd: cleanupd`, each `pgrep -ax lean` rc 1); item 134's `hKc` removed,
verdict GENERALIZED; item 116 stated with `closedSimplex ι`, since the draft's set equals it by `rfl`
(`rfl-116`, rc 0; its planted control `rfl-116-fire`, a strict inequality, rc 1).

### The items

Each main theorem's verdict, from its cold module review (none WEAKER; narrowing: none):

* item 111, `ClassicalLean/Algebra/Kantorovich.lean`: `quadForm_steepestStep_le`, FAITHFUL;
* item 112, `ClassicalLean/Analysis/GradientDescent.lean`: `sub_le_pow_mul_of_polyakLojasiewicz`,
  GENERALIZED (`fstar` any lower bound; nothing asked of `μ` or `L`);
* item 134, `ClassicalLean/Analysis/GradientDescent.lean`: `sub_le_of_projGradientStep`, with the
  private `projStep_aux`, GENERALIZED (no `IsClosed K`; `f` convex on `K` only);
* item 116, `ClassicalLean/Analysis/ExponentialWeights.lean`: `isMinOn_inner_add_relEntropy_softmax`,
  with the private `inner_add_relEntropy_eq_aux`, FAITHFUL;
* item 117, `ClassicalLean/Analysis/ConvexConjugate.lean`: `convexConjugate_logSumExp`, FAITHFUL.

Proof changes beyond the move into the namespaces, each in the Goal list or a review's finding:
111's `field_simp <;> ring` is `field_simp`; 117's first `show` is `change` and its second, which
changed nothing the next `rw` needs, is cut (review d117, finding 1); 134's `hKc` removed; 116's set
written `closedSimplex ι`. No other proof line of a draft changed.

The witnesses (rule 5), each with its review's verdict OK: 111, `A = diag(1, 2)`, `m = 1`, `M = 2`,
`x = (1, 1)`; 112, `f = y²/2` on `ℝ`, `L = 2`, `μ = 1`, `x k = (1/2)^k`; 134, the same `f` on
`K = [1/4, 1]`, iterates `1, 1/2, 1/4, 1/4, …`; 116, `Fin 2`, `x = (1, 2)`, `ℓ = (0, 1)`, `η = 1`;
117, `p = (1/4, 3/4)`. Each was in place within 65 seconds of its logged start (`w111-start` and the
others; the limit is 1800).

The witness rows: rows 7 and 8 (`ClassicalLean/Probability/LikelihoodScore.lean`, old lines 399 to
471 replaced, blank line 472 kept) from carry `d3005-r1-s2` with its 8 four-flag warnings fixed in
the proof only (the forms the module's primed witness uses) and the docstrings in rule 2's form;
rows 9 and 10 (`ClassicalLean/Probability/EffectiveSampleSize.lean`) and row 67
(`ClassicalLean/Probability/GlivenkoCantelli.lean`) from claude-ai's `w9-10.lean` and `w67.lean`,
unchanged. Review rows: all five OK, no findings.

### Reviews (each saved in `~/lean/lean33-checks/reviews/` and hash-checked against its agent's returned sha256)

Statement review `review-stmt` (no BLOCKER, no MAJOR, four MINOR; fixed and confirmed,
`review-stmt-confirm`). Module reviews: `review-d117` (two MINOR, fixed and confirmed,
`review-d117c`), `review-d111` (two MINOR, `review-d111c`), `review-d116` (one MINOR,
`review-d116c`), `review-d112` for items 112 and 134 (two MINOR, `review-d112c`; that pass's own
optional wording point was not taken), `review-rows` (none). Documents review `review-docs` (three
MINOR, fixed and confirmed, `review-docsc`; that pass's MINOR finding, an edit after the drift check,
is the `docs-wrap-note` line and the re-run `docs-drift3`). No review needed a second round.

### Counts (rule 27), measured

Theorem constants per changed module, by census on scratch copies (`mkcensus.sh`, the axiom gate's
`.thmInfo` predicate, `privateToUserName`), old copy at `04e4a38` and final copy:
Kantorovich 3 → 4, GradientDescent 35 → 41 (`projStep_aux` brings three `abel` auxiliaries),
ExponentialWeights 3 → 5, ConvexConjugate 5 → 6, LikelihoodScore 20, EffectiveSampleSize 73,
GlivenkoCantelli 18 (unchanged: witnesses are `example`s). New: 10.

The gates at G, on its clean tree, each as `pred-main.md` predicted: `g1-build` rc 0, 4188 jobs,
0 warnings; `g2-axiom` PASS 3468; `g3-vacuity` PASS, 1 reviewed helper, 0 VACUOUS-PENDING;
`g3-tests` 89 tests, 47 flagged, 0 rule-5 run-outs, 0 mismatches; `g4-sorry` PASS 135; `g5-records`
PASS 135, 100 records files; `g6-drift` PASS; `g6-banned` PASS, 135 files and the root, 0 hits;
`g7` "ALL PASSED for 94619863901a332e303a803be9ba1b23d74ad671" (4188 jobs, 135 modules 0 failed, 3468
theorems, the three standard axioms, the planted fault `ClassicalLean.Analysis.LogDrag.mean_log_one_add_le`
named). The type dump at G (`td-after`, 3940 records, 3468 thm, 472 def, elided 0, missing_fields 0)
against the records commit's (`td-before`): "DIFF removed=0 added=10 changed=0 proof_only=0", the
ten ADDED names the census's ten. These gate numbers were taken on a clean tree.

The bridge search at G against `records/bridges/MERGE-2/`: 2897 pairs, 735 shape candidates, N =
134; 22 new pairs, 36 new shapes (32 import-unrelated), 2 gone pairs; no real bridge, so no row is
appended to the lane's bridges file. How they were checked (plan 2's ruling 5): each of the 22 new
pairs was read by its shared-constant list in `pairs.tsv`, and every one shares only one or two
general lemmas (`mul_inv_cancel₀`, `Real.exp_log`, `isEmpty_or_nonempty`, `mul_self_nonneg`,
`inv_nonneg`, `norm_zero`, `mul_sub`, `Set.Elem`; scores 2.6 to 5.9). The 32 unrelated new shapes
were judged by group, not statement by statement: `log-sum-exp` with `Analysis.ConvexConjugate`
(item 117 itself is the bridge the plan's row names; Fenchel–Young at log-sum-exp restates the
existing `gibbsObjective_le`), `relative entropy` with `Analysis.ExponentialWeights` (item 116 shares
the word, not a theorem another module needs), `stochastic matrix` with `Algebra.Kantorovich`
(matched on matrix words; no stochastic matrix in item 111). The 2 gone pairs are
`Analysis.ExponentialWeights × InformationTheory.Entropy` and `Analysis.FiniteGame ×
InformationTheory.Entropy`, now import-related through item 116's new import line. Hand prediction
missed: new shapes 36 against at most 30.

The report tool at G: written theorems 1925, A with a hypothesis 1137 (0 close), B 788 (16 close),
C 36 Prop-valued, 0 recursive, self-test mismatches 0, as hand-predicted; no `CLOSES` line names a
declaration of this order.

The job count: the seven modules' import closure, by import lines, is the same at `ce41eef` and at
HEAD (4491 modules, 18 under `ClassicalLean`), so no module enters the build (4188 jobs, as gate 1
measured). Not done as the order words it: the Lean count `env.header.moduleNames` was taken at HEAD
only (4849); at the records commit only the import-line count was taken, and that script
under-counts core modules (4491 against 4849), so only its equality is used.

### Misses and departures, in order

1. The before-approval hash check: predicted "40", the list held 39; all 39 OK.
2. `pgrep -a lean` matched `smbd: cleanupd` (ruled by Dustin, ruling 1).
3. Four of the predicted timers are cron jobs.
4. `t-briefverify-plant`: a muddled no-op line (`true`) logged during Setup 2; the real negative
   controls are `t-briefverify-plant14` and `t-briefverify-plantw`.
5. Ten type-comparison runs refused by rule 37 (`set_option`, `pp.fullNames` not cleared), logged
   `NOT RUN`; the two tokens added to `allowlist.txt` with reasons, its hash logged; the runs then
   passed. With `t-empty`, `t-rootrun-false` and `t-el-1` (Setup 2's planted refusals), 13
   `NOT RUN` lines in all.
6. `typecmp.py` adapted (it looked for a `setOption` warning that `set_option … in` does not give).
7. Probes: `p-d134` failed on the keyword `lemma` (rewritten without it, `p-d134-r2`); the field
   name `StrongConvexOn.convexOn` is the constant `UniformConvexOn.convexOn` (`r2` extras).
8. `m117-vac` (a vacuity copy) failed only because the reviewed entry's module was outside its
   imports; predicted PASS; `m117-vac-b` with that module imported passed.
9. 111's witness took two compile fixes of its matrix identities (`m111-el`, `m111-el2`).
10. `docs-sec6`'s prediction was worded "empty" for a grep that lists the hunks; the hunks are in
    sections 1 and 4 only.
11. `docs-wrap-note`: a note line appended to `evidence.log` by `printf`, not through a helper.
12. Three times a `python3 -I -` with an empty here-document ran by mistake (no input, no effect);
    not logged.
13. `quotes-r69-part1`: a second no-op line (`true`) logged, while this part's quotes were checked;
    the real checks are `quotes-r69-r2`, `quotes-r69-plant-r2` and `quotes-r69-full`.

### Commits on `lean-33` (from `04e4a38`; nothing pushed)

* `ce41eef` records first; `3d642a0` item 117; `9f17eaf` item 111; `8112439` item 116; `a2ce362`
  items 112 and 134; `052fc94` the witness rows; `9461986` documents (G); `1652b67` the bridge
  baseline; and the records commit that adds this part.

### For the later merge of `lean-33` with `cloud-math-3`

`records/CLAIMS.md` and `records/orders/INDEX.md`: take CLOUD-MATH-3's side for MERGE-2's rows and
append LEAN-33's rows after it. Also `ROADMAP.md` section 1.26 and `HANDOFF.md` section 1's last
paragraph (CLOUD-MATH-3 may add its own). `tools/vacuity_reviewed.txt`: not changed by this order.
