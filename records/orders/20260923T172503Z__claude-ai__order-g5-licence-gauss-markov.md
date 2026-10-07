# ORDER G-5 — pay order 0923's debts, license the library, and open statistics with Gauss–Markov

Written 2026-09-23T17:25:03Z by claude-ai (Cowork, linked to helios) for one Claude Code session on
helios. Library: `~/work/classical-lean`. **Source of truth:** this file and `records/orders/INDEX.md`.

It replaces an unfiled draft, "order 0923b" (information theory part 2), which is parked at
`~/Cowork/_parked/20260923T162835Z__claude-ai__order-0923b-info-theory-2.md` and was never started.
Dustin asked claude-ai to act on four recommendations. What changed because of them:

- **Licence.** Dustin chose Apache-2.0 on 2026-09-23, with "Dustin [surname]" on the copyright and
  Authors lines. J2 applies it and turns the header linter back on. The library bans the word
  `[surname]` (the retired corpus's eponym), so J2 first adds one exception that allows exactly the
  two licence lines. That exception is claude-ai's decision on Dustin's delegation; his veto is open.
- **Prior art.** The draft's J3 (conditional entropy, the chain rule, data processing along a Markov
  chain) already exists, in random-variable form, in an Apache-2.0 Lean library that this one does
  not depend on (§0 row 7). The finite-vector forms would still be new here, so dropping them is a
  ranking decision, not a finding that they add nothing. Decided by claude-ai on Dustin's
  delegation; his veto is open.
- **Measured gap.** J3 is now the Gauss–Markov theorem, the library's first statistics module
  (§0 row 9).
- **More mathematics.** J2 has a budget, J3 is the main job, and the final report counts new
  theorems and areas.

It starts only after order 0923 is closed. It waits in `~/Cowork/lean-orders/` until J1 files it.
A second agent reviewed it cold, twice, before it was placed there. The first pass found one blocker
(the `[surname]` ban) and twenty smaller points. The second pass confirmed those fixes and found
thirteen small points, which were applied without a third review. Two standing answers in §2
(`mem_closedSimplex`, the parked build) and their Close lines were added after both reviews.

Three jobs, J1 to J3, then a close. Each has Goal / Scope / Done-means and an undo line. A STOP at a
gate is a report, not a close.

---

## 0. What claude-ai measured

Read-only, 2026-09-23 between 16:50Z and 17:25Z: staged copies of the helios tree, a sparse clone of
Mathlib v4.34.0 (`5ed2965256`), and a clone of the prior-art repository. No Lean was run by
claude-ai. Line numbers were read then; order 0923's close may move some, so find each place by its
text.

| # | Fact | Value |
|---|---|---|
| 1 | Order 0923 | J3 landed: `master` at `f04bf6b` on v4.34.0 (`HANDOFF.md` §1). Its session reported a Close commit `6b70bf4` and a final Done-means check running at about 17:00Z; claude-ai saw that on the session's page, not in git. `INDEX.md` row 0923 still said "open" at 16:56Z. |
| 2 | The library | 44 modules. None contains `Copyright`; all 44 have a module docstring as the first command after the imports; all 44, and `ClassicalLean.lean`, begin with `import`. `lakefile.toml` lines 10–13 are a comment and line 14 is `weak.linter.style.header = false`. There is no `LICENSE` file. 9 top-level directories under `ClassicalLean/`. |
| 3 | `backward.isDefEq.respectTransparency false` | 15 `set_option` lines in 10 modules: 9 file-level, plus 6 scoped `… in` lines in `CompositumDiscriminant`. |
| 4 | Round numbers | 16, 17 and 18 exist. This order writes 19 (J2) and 20 (J3). |
| 5 | Tools kept in `~/work/_bump-evidence/` | `ListTheorems.lean` (the v4.34.0 copy), `ModuleThmCount.lean`, `import_closure.py`, `junk_cells.py`, `RingPowerSeries.lean` |
| 6 | Mathlib's header linter at v4.34.0 | `Mathlib/Tactic/Linter/Header.lean`. It is in `linter.mathlibStandardSet` (`Mathlib/Init.lean:100`). It checks only files the library root imports, not the root itself. It wants `Copyright (c) YYYY <names>. All rights reserved.`, then the licence line set by `linter.style.header.license` (default `Released under Apache 2.0 license as described in the file LICENSE.`, lines 231–233), then `Authors: …` with no final period, then a module docstring as the first command after the imports. Mathlib's own `LICENSE`: 201 lines, sha256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, the Apache-2.0 text in GitHub's template form (`{yyyy}` placeholders). |
| 7 | Prior art | `github.com/FujiHaruka/information-theory` at `7e97b77` (2026-09-14): Apache-2.0; Lean and Mathlib v4.31.0; 418 modules; 4,055 `theorem`/`lemma` declarations (the README claims 4,108; the count below misses `@[attr] theorem` lines); 0 `axiom` declarations; 27 `sorry` tokens, all in prose. Commands below the table. Random-variable form: `entropy μ Xs` (`Shannon/Bridge.lean:40`). It has `condEntropy`, `mutualInfo_chain_rule` (`Shannon/CondMutualInfo.lean:224`), `condEntropy_pi_chain_rule`, the Markov data-processing inequality `mutualInfo_le_of_markov` (`Shannon/CondMutualInfo.lean:366`), Pinsker (`tvNorm_le_sqrt_klDiv`), Fano, Kraft and Huffman optimality. |
| 8 | Mathlib v4.34.0 `InformationTheory/` | Nine files: `Coding/{Kraft, KraftMcMillan, PrefixFree, UniquelyDecodable}`, `Hamming`, `KullbackLeibler/{Basic, ChainRule, DataProcessing, KLFun}`. Round 18 and `ROADMAP.md` §2.8 name only the last four. |
| 9 | Gauss–Markov | Mathlib v4.34.0 has no Gauss–Markov theorem, and nothing named least squares, "unbiased" or regression (J3 step 1 gives the commands). It has least-squares minimisation in geometric form (`Submodule.starProjection_minimal`, `Analysis/InnerProductSpace/Projection/Basic.lean:228`), no matrix pseudoinverse (`LinearAlgebra/Matrix/NonsingularInverse.lean`, lines 21–22), `Matrix.PosSemidef` (`LinearAlgebra/Matrix/PosDef.lean:60`), a Loewner order scoped to `MatrixOrder` (`Analysis/Matrix/Order.lean:58`, `Matrix.le_iff`), and `Matrix.gram` with `posSemidef_gram`. The prior art has no Gauss–Markov theorem and nothing named
least squares. Mathlib's list of famous theorems (`docs/1000.yaml`, entry Q428134) records no formalisation. |

Row 7's counts, as claude-ai ran them inside the clone:

```
find InformationTheory -name '*.lean' | wc -l                                                # 418
grep -rhE '^\s*((private|protected) )?(theorem|lemma)\s' --include=*.lean InformationTheory | wc -l  # 4055
grep -rhE '^\s*((private|protected|noncomputable) )*axiom\s' --include=*.lean . | wc -l      # 0
grep -rhow sorry --include=*.lean InformationTheory InformationTheory.lean | wc -l           # 27
```

**Predict J1 from `HANDOFF.md` §1, `records/orders/INDEX.md` and `records/CLAIMS.md` as order 0923's
close leaves them, not from this table.**

---

## 1. Rules for this session

- **Dustin does not read code or files.** Everything he needs goes in your chat reply. When he must
  act, give the exact command, the box, and the output you expect.
- **Predict, then measure.** Before any command that prints a count, a hash or an rc, write the value
  you expect, or write "no prediction". Report predicted beside actual.
- **Run every command from `~/work/classical-lean`**, or give `git -C` and absolute paths. Shell state
  does not carry between calls.
- **This repository's rules hold unchanged:** `HANDOFF.md` §0, §4, §5 and §6, and `records/README.md`
  Rules 1 to 4. Dustin's rulings of 2026-09-07 hold as order 0923 §1 states them.
- **Seven rules learned in order 0923's run.** Their sources: round 17 (rules 1 and 5: its dated
  amendment; rule 4: Findings 1; rule 6: "Options and linters"; rule 7: Findings 3); round 18 (rules 2
  and 3: Findings 1 and 2; rules 4 to 6 again in its closing addendum); and the session's final
  report.
  1. **Check the invariant, not a proxy.** The cache check tested all of Mathlib, and so it stopped the
     move over a module this library never imports.
  2. **Read a Mathlib definition before stating anything about it.** The `klDiv` bridge was written
     from the name; the definition carries a mass term.
  3. **Junk cells need random trials plus constructed exact-zero cases.** Random search missed a
     measure-zero failure.
  4. **Stage every commit by path**, branch commits included.
  5. **Every evidence-log line carries its command and its rc.**
  6. **Any linter or option you switch off or on** goes in the first paragraph of the commit message,
     and in `HANDOFF.md` §1.
  7. **Write a commit message only after its gates have run.**
- **State hypotheses explicitly**, as round 18 did.
- **J2 is upkeep and J3 is the job.** If a J2 step needs more than a small edit, record it as debt in
  round 19 and move on.
- **Git.** Commit locally, and never push to GitHub or add a remote. Park, never delete: `mv -n` into a
  `_parked/` folder outside the repository, then `test` both paths. Reach DSMain only with
  `GIT_SSH_COMMAND='ssh -o BatchMode=yes -o ConnectTimeout=15'`. If DSMain is unreachable, record
  "unreachable" and carry on. Never touch the VPN, routes or ssh configuration.
- **A second party for everything you write.** A fresh subagent that did not write it reviews every
  new or changed statement cold, before proving. A second fresh subagent reviews every shipped
  statement after proving, as round 18 did.
- **Builds run one at a time.** Subagents never run `lake`.

## 2. Standing answers — do not stop to ask these

- **A Mathlib cache gap outside this library's import closure:** use the import-closure check plus the
  `.olean` sha256 manifest taken before and after `lake build`. Ruled for order 0923's J3, 2026-09-23.
- **A deprecation whose replacement changes what a statement says:** give the library its own object
  with the identical definition, check it equal by `rfl` in a scratch file, and switch to it. Same
  ruling, same date.
- **The licence is Apache-2.0**, chosen by Dustin on 2026-09-23. The copyright and Authors lines name
  "Dustin [surname]".
- **The `[surname]` ban stays.** One anchored exception permits exactly the two licence lines, and
  nothing else (J2 step 1).
- **`mem_closedSimplex` stays**, by `mem_openSimplex`'s precedent. Order 0923's final report left this
  to Dustin; claude-ai decided it on his delegation on 2026-09-23, and his veto is open.
- **The parked v4.29.0-rc2 build** (`~/work/_parked/classical-lean.lake-v4.29.0-rc2`) stays parked.
  Only Dustin deletes; the Close says whether it is still needed.
- **Anything that needs Dustin:** ask in one line, recommended answer first, and keep working on
  whatever does not depend on it. Pushing, publishing and offering anything to Mathlib are his.

---

## J1 — open and re-measure (read-only)

**Goal.** Know that order 0923 is closed, and that the tree is what its records say, before touching
it.

**Scope.** Read-only. Run what plan mode allows. List the rest with predictions, marked "deferred".

**Measure, predicting each value first:**

1. `records/orders/INDEX.md` row `0923`: its state, and what landed.
2. `lean-toolchain` and `lakefile.toml` `rev`: expect v4.34.0.
3. `git -C ~/work/classical-lean worktree list`: expect no `classical-lean-bump`.
4. `git -C ~/work/classical-lean status --short`: expect nothing, because this order still sits outside
   the repository.
5. For each of `~/work/classical-lean` and `~/Cowork/lean-rebuild`:
   `git -C <repo> rev-parse master dsmain/master`, and
   `GIT_SSH_COMMAND='ssh -o BatchMode=yes -o ConnectTimeout=15' git -C <repo> ls-remote dsmain master`.
   Expect `dsmain/master` and `ls-remote` to agree, or record "unreachable". If order 0923 pushed
   before its last records commit, `classical-lean` `master` is ahead of DSMain by that commit: say
   which. For `lean-rebuild`, expect all three equal.
6. The six commands in `HANDOFF.md` §1, copied from it. Predict from its snapshot.
7. `grep -rn '^ *set_option backward.isDefEq.respectTransparency' ClassicalLean`: expect 15 lines.
8. `test -e LICENSE` (expect rc 1); the number of files under `ClassicalLean/` containing
   `Copyright (c)` (expect 0); `grep -n 'linter.style.header' lakefile.toml` (expect 2 lines: 10,
   the comment, and 14, `weak.linter.style.header = false`).

**If order 0923 is not closed — J3 not landed, or a CLAIMS row still open — STOP and report.** Do not
start this order.

**Done-means.** A predicted-beside-actual table in the chat, with every miss explained. Then one plan
for J2 and J3, and wait for approval.

**After approval, in this order:**

1. **Run the deferred commands.** STOP before J2 on any miss you cannot explain.
2. **File the order:**
   `mv -n ~/Cowork/lean-orders/20260923T172503Z__claude-ai__order-g5-licence-gauss-markov.md ~/work/classical-lean/records/orders/ && test ! -e ~/Cowork/lean-orders/20260923T172503Z__claude-ai__order-g5-licence-gauss-markov.md && test -f ~/work/classical-lean/records/orders/20260923T172503Z__claude-ai__order-g5-licence-gauss-markov.md`.
3. **Add the records rows, then commit exactly three paths:** the filed order, `records/orders/INDEX.md`
   and `records/CLAIMS.md`.
   - `INDEX.md`: a row for `G-5`.
   - `CLAIMS.md`: a row naming every module (J2's headers touch all of them), `ClassicalLean.lean`,
     `LICENSE`, `lakefile.toml`, `tools/banned_vocab_scan.py`, J3's new file (added before J3 writes
     it), and the records paths: `HANDOFF.md`, `ROADMAP.md`, `RETIRED.md`, the round 19 and 20
     fragments, `CLAIMS.md` and `INDEX.md`.
4. **Take the "before" evidence on a clean tree.** Run the v4.34.0 `ListTheorems.lean` for the raw and
   filtered name lists. Add a dump of `name : type` for every theorem constant under `ClassicalLean`,
   with a sha256 of each type's printed form. Save all of it in `~/work/_bump-evidence/g5-before/`.
   J2 and J3 diff against these.

**Undo:** nothing to undo.

---

## J2 — debts, the licence, and the records

**Goal.** Clear what order 0923 left, apply the licence, and correct the information-theory records.
No theorem's meaning changes.

**Scope.**
- Every `.lean` file under `ClassicalLean/`, and `ClassicalLean.lean`: the licence header only, except
  for the named edits in steps 3 to 5.
- `LICENSE` (new), `lakefile.toml`, and one `EXCEPTIONS` entry in `tools/banned_vocab_scan.py`.
- `HANDOFF.md` §1, §3, §4, §5 and §6; `ROADMAP.md` §2.8; one dated line in `RETIRED.md`; records.

1. **The vocabulary exception — first, as its own commit.**
   - `tools/banned_vocab_scan.py` bans `[surname]`: line 66, case-insensitive, comments included, the
     retired corpus's eponym (`RETIRED.md`, "A note on the names quoted in this file"). The headers
     of step 2 would fail that gate with 88 hits, two per module.
   - Add exactly one entry to `EXCEPTIONS`, with a comment naming Dustin's choice of 2026-09-23:
     `(r"[surname]", r"^(Copyright \(c\) 20\d\d Dustin [surname]\. All rights reserved\.|Authors: Dustin [surname])$"),`
     The year is `20\d\d` so that a module first written in a later year needs no new exception.
   - Fail-test it, per `HANDOFF.md` §0: a scratch line `-- the [surname] theorem` in one module must
     FAIL, and a module with only the two header lines added must PASS. Restore the module, and put
     both runs in the commit message.
   - Add one dated line to `RETIRED.md`'s note on names, and to `HANDOFF.md` §4 and §5: the only
     permitted occurrences are these two licence lines.
2. **The licence and the headers — second, as their own commit.**
   - `cp -n .lake/packages/mathlib/LICENSE LICENSE`, then `sha256sum LICENSE`: expect §0 row 6's hash.
     Keep it byte for byte, placeholders included.
   - Insert these five lines, each starting at column 1, and one blank line at the top of each of the
     45 files. Use a script that asserts it touched 45 files and that each began with `import`.

```
/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin [surname]
-/
```

   - Delete line 14, `weak.linter.style.header = false`, and its comment, lines 10–13, from
     `lakefile.toml`. `weak.linter.mathlibStandardSet = true` then turns the linter back on.
   - Before the checks, edit `HANDOFF.md`, to be committed with the headers. In §1, the sentence "Two
     linters are off" becomes one linter; add a dated line: the header linter is on since round 19,
     licence Apache-2.0, chosen by Dustin on 2026-09-23. `linter.defProp` on `isLocalId` stays off,
     as its docstring explains. In §3, mark the bullet "`linter.style.header` is off library-wide…"
     superseded, dated.
   - Checks before committing:
     - Unstaged `git diff --numstat` shows `6 0` for each of the 45 files, `0 5` for `lakefile.toml`,
       and a row for `HANDOFF.md`. `LICENSE` is untracked, so it is not in that list.
     - `lake build` rc 0 with 0 warnings; `banned_vocab_scan.py` PASS with 0 hits; the raw and
       filtered name lists, and every type hash, equal J1's "before" evidence.
     - **Fire test.** Copy `ClassicalLean/NumberTheory/Catalan.lean` (a leaf: only the root imports it)
       to `~/work/_bump-evidence/g5-fire/Catalan.lean`, outside the repository, so no gate sees the
       copy. Delete the module's `Authors:` line and build: expect a header warning naming that
       file. Copy it back, `cmp` against the saved copy, and build again: expect 0 warnings.
   - Commit by path; staged, `git diff --cached --numstat` adds `201 0` for `LICENSE`. Put both fire-test
     runs in the commit message.
3. **The 15 `backward.isDefEq.respectTransparency false` settings.**
   - Re-run `~/work/_bump-evidence/RingPowerSeries.lean` once, logging the command and rc. Its log
     `ring-v4.34.0.txt` is empty because that run printed nothing.
   - Then remove each setting wherever its module still builds with 0 warnings without it. Small proof
     edits are allowed.
   - Where a setting goes, the text saying it is needed becomes false: in the module docstring, and in
     any code comment directly above a removed `set_option … in`. Keep that text and add one dated
     line: "Superseded: builds without the option at v4.34.0 (round 19)." The module docstrings to
     watch: `AlgebraicGeneratingFunction`, `RecurrenceGeneratingFunction`,
     `LucasSequenceGeneratingFunction`, `Hopf`, `SU2SO3` and `S3Quaternion`.
   - In `CompositumDiscriminant`, only the comment above `finrank_K2_eq`'s setting says the option is
     needed. The comment above `finrank_K1_eq`'s setting documents `maxHeartbeats 400000`, measured
     with the option on. If that option goes, re-measure the heartbeat figures and date them; do not
     mark them superseded.
   - A setting that is still needed stays, with a one-line comment naming the proof that needs it and
     why. Predict how many of the 15 go, per module.
   - Mark the matching `HANDOFF.md` §3 bullet done, dated. Once this step is done, add a dated line to
     `HANDOFF.md` §1's `ring`-in-`PowerSeries` note (order 0923 already wrote that it no longer
     applies) saying which settings went.
4. **Swap `Channel`'s private `vecMul_eq_sum`** for Mathlib's `Matrix.vecMul_apply_eq_sum`
   (`Data/Matrix/Mul.lean:726` at v4.34.0). Read the Mathlib statement first. Mark the matching
   `HANDOFF.md` §3 bullet done, dated.
5. **Correct two counts in prose, each with a dated note** (round 16, finding 5):
   - `NumberTheory/Mersenne.lean` says in two places that `Order/Superadditive.lean` proves six
     theorems; it declares five.
   - `HANDOFF.md` §3 describes that module as "a definition, four theorems".
6. **The information-theory records.**
   - **Correct round 18** in round 19's fragment: Mathlib v4.34.0's `InformationTheory/` has nine
     files (§0 row 8). `ChainRule` holds `klDiv_compProd_eq_add`, a chain rule for the KL divergence,
     not for entropy. `DataProcessing` holds `klDiv_comp_right_le`, `klDiv_map_le` and
     `klDiv_trim_le`. `Coding/` holds the Kraft–McMillan inequality. Update `ROADMAP.md` §2.8's
     Mathlib paragraph to match.
   - **The prior art.** Do not clone it. Beside `ROADMAP.md` §2.8's "not verified", add a dated line
     with §0 row 7's facts and commands, measured by claude-ai on 2026-09-23. Keep the README's
     4,108 claim; `ROADMAP.md` §4 says corrections are written into the row, not swapped.
   - **Record the decision** in `ROADMAP.md` §2.8 and `HANDOFF.md` §3: information theory part 2 is
     declined for now, on the prior-art ground Dustin asked claude-ai to apply on 2026-09-23.
     Conditional entropy, the chain rule, Markov data processing, Pinsker and Fano exist, in
     random-variable form, in an Apache-2.0 library this one does not depend on. The finite-vector
     forms would still be new here, so this is a ranking decision, not a finding that they add
     nothing. The three finite modules stay as they are. `mutualInfo` keeps no consumer, and round 19
     says why. The `klDiv` bridge stays listed as the first step if the finite layer is ever offered
     to Mathlib. Dustin's veto is open.
7. **Move this order's lessons into the repository.** Add §1's seven rules and §2's standing answers,
   the licence and the exception included, to `HANDOFF.md` §6, each with its date and source. The
   next order will cite §6 instead of repeating them. Leave out anything §0, §4 or §6 already says.
   Mark `HANDOFF.md` §3's `mem_closedSimplex` bullet settled, per §2, dated.
8. **A fragment for round 19**, per Rule 1.

**Done-means.**
1. The six gates pass on a clean tree, with the header linter on, 0 warnings, and 0 vocabulary hits.
2. The exception's fail test and the header fire test each went red, then green, and both runs of each
   are in their commit messages. `LICENSE` has §0 row 6's hash. 45 files carry the header.
3. The filtered name list differs from J1's "before" list only by the removal of
   `ClassicalLean.Simplex.vecMul_eq_sum`, which is private but listed, because `ListTheorems.lean`
   applies `privateToUserName` (round 18: "filtered +22 … 6 private"). The raw list differs by that
   and by any compiler auxiliaries a proof edit renamed, each named in the fragment. Every other
   theorem in the filtered list has an unchanged type hash.
4. The fragment gives, per module, which settings went and which stayed, and why. It carries the
   correction to round 18, the prior-art facts and who measured them, and the decision.
5. `HANDOFF.md` §6 carries the rules and standing answers of step 7, each with its source. No
   `HANDOFF.md` §3 bullet describes as pending something this job finished.

**Undo:** yes — `git revert`, one commit at a time.

---

## J3 — statistics: the Gauss–Markov theorem

**Goal.** The library's first statistics module: the Gauss–Markov theorem for linear estimators, in
matrix form, with its equality case and a worked example showing that the inequality can be strict.

**Why this.** Ranked by claude-ai on Dustin's delegation; his veto is open.
- The gap is measured (§0 row 9), and it is a theorem people cite.
- It is in Dustin's 2026-09-07 precedence (data science).
- It is an area with no number theory in it (`ROADMAP.md` §3, item 3).
- It fits in one order, and later statistics can build on it: generalised least squares, Cochran's
  theorem.

**Scope.**
- One new module, suggested `ClassicalLean/Statistics/GaussMarkov`, and at most one optional second
  module for the `covarianceBilin` restatement below. Each gets J2's header, one import line inside
  `ClassicalLean.lean`'s import block (which starts at line 7 after J2), a `CLAIMS.md` entry before it
  is written, its own gate-6 FAIL check, and an `import_closure.py` run with its positive control.
- Naming, pre-answered: `HANDOFF.md` §5's "no eponyms" means the source corpus's names. Standard
  eponyms are already module names here (`Lucas`, `Pell`, `Catalan`, `Hopf`, `Gibbs`), so
  `GaussMarkov` is fine. Mathlib has no `Statistics/` directory.
- A new `ROADMAP.md` §2 row for statistics; `HANDOFF.md` §3 for anything left unproved; records.
- Every other module is read-only.

**Gate 6 must stay a real check for each new file.**
- Until round 20's fragment names a new file, write its name into none of the files gate 6 searches:
  `PROVENANCE.md`, `records/rounds/*.md` and `records/orders/*.md` (`INDEX.md` included).
  `CLAIMS.md`, `ROADMAP.md` and `HANDOFF.md` are not searched and may name it.
- `check_records.py` must FAIL on each new file before its fragment exists. If it passes, find the
  record that names the file. If that record existed before this order, or is this order's own file,
  rename the new file; do not edit a filed order. If this order wrote any other record naming it,
  remove the name from that record.

**Method.**

1. **Search first**, and record every command and count in the `ROADMAP.md` row. At least:
   - `grep -rniE 'gauss.?markov|best linear unbiased|unbiased|least.?squares|leastSquares|regression' .lake/packages/mathlib/Mathlib --include=*.lean`.
     claude-ai's run gave 26 lines in 5 files, every one the word "regression" in a tactic-analysis
     option or comment.
   - `grep -rniE 'pseudo.?inverse|moore.?penrose' .lake/packages/mathlib/Mathlib --include=*.lean`.
     claude-ai's run gave 3 lines in 2 files: `LinearAlgebra/Matrix/NonsingularInverse.lean:22`
     ("pseudoinverses which we do not consider here"), and class-design prose in
     `Algebra/Group/DivInvMonoid.lean`, lines 71 and 73. No Moore–Penrose inverse.
   - The statement's shape: `grep -rnE 'PosSemidef.*⁻¹' .lake/packages/mathlib/Mathlib --include=*.lean`.
     claude-ai's run gave 3 lines: `PosSemidef.inv`, and two Schur-complement lemmas
     (`LinearAlgebra/Matrix/PosDef.lean` lines 615 and 634). They are not the theorem, but they give
     a second route to it.
   - Read `Matrix.PosSemidef`'s definition and `Analysis/Matrix/Order.lean` before stating anything
     (rule 2).
2. **Definitions, then statements, then a cold review, then proofs.** Enumerate the junk cells first,
   with constructed cases (rule 3). Mathlib's `Matrix.inv` returns 0 for a singular matrix.
   claude-ai's reading is that `C * X = 1` forces `Xᵀ * X` to be invertible: if `Xᵀ * X` kills `v`,
   then `X v` has zero length, so `X v = 0` and `v = C (X v) = 0`. So no junk inverse can make the
   main theorem hold emptily. Check that reading in Lean; do not assume it.
3. **Prose:** the vocabulary gate also bans `the\s+framework` (`banned_vocab_scan.py`, line 77). Write
   "the linear model", not "[retired term] of the linear model".

**Suggested content** — change it to fit what the search finds:

- `X : Matrix (Fin n) (Fin k) ℝ` is the design. `C : Matrix (Fin k) (Fin n) ℝ` is a linear estimator,
  `β̂ = C *ᵥ y`.
- **Unbiasedness:** `(∀ β, C *ᵥ (X *ᵥ β) = β) ↔ C * X = 1`.
- **The least-squares matrix** `M = (Xᵀ * X)⁻¹ * Xᵀ`. If some `C` has `C * X = 1`, then `M * X = 1`
  and `M * Mᵀ = (Xᵀ * X)⁻¹`.
- **The normal equations, so that `M` earns its name:** if some `C` has `C * X = 1`, then
  `Xᵀ *ᵥ (y - X *ᵥ (M *ᵥ y)) = 0`. Without the hypothesis it is false: for `X = !![1, 1; 1, 1]` the
  junk inverse makes `M = 0`, and `y = ![1, 0]` gives `![1, 1]`. State any "least" claim with `⬝ᵥ`,
  not `‖·‖`: on `Fin n → ℝ`, Mathlib's norm is the sup norm.
- **Gauss–Markov:** if `C * X = 1`, then `(C * Cᵀ - (Xᵀ * X)⁻¹).PosSemidef`.
  - Expected route: `D = C - M` has `D * X = 0`, the cross terms vanish, and
    `C * Cᵀ - (Xᵀ * X)⁻¹ = D * Dᵀ`.
  - `Matrix.posSemidef_self_mul_conjTranspose` (`LinearAlgebra/Matrix/PosDef.lean:393`) covers
    `D * Dᴴ`, and over ℝ `ᴴ` is `ᵀ`.
  - Second route: the block matrix with rows `[C * Cᵀ, 1]` and `[1, Xᵀ * X]` is a matrix times its own
    transpose, so it is positive semidefinite. The Schur-complement lemma `fromBlocks₂₂` (line 634)
    then gives the theorem; it needs `Xᵀ * X` positive definite, `Invertible`, and `DecidableEq`.
- **Equality case:** under `C * X = 1`, `C * Cᵀ = (Xᵀ * X)⁻¹ ↔ C = M`.
- **The variance reading:** under `C * X = 1`, for every `a`,
  `a ⬝ᵥ ((Xᵀ * X)⁻¹ *ᵥ a) ≤ a ⬝ᵥ ((C * Cᵀ) *ᵥ a)`. Without the hypothesis it is false: `X = !![1; 1]`,
  `C = 0`, `a = 1` gives `1/2 ≤ 0`. When the noise has covariance `σ² • 1`, the two sides times `σ²`
  are the variances of `a ⬝ᵥ β̂` for least squares and for `C`. State it as matrix algebra, and say
  so in the docstring.
- **The Loewner form:** under `C * X = 1`, `(Xᵀ * X)⁻¹ ≤ C * Cᵀ` with `open scoped MatrixOrder`; it is
  false without the hypothesis, as above. The reviewer's closure
  count: `Mathlib.Analysis.Matrix.Order` adds 73 modules to the library's import closure and does not
  reach `Mathlib.Probability.Kernel.Invariance`. Confirm with `import_closure.py`; if Invariance
  enters the closure, leave this form out and say why.
- **A worked example where the inequality is strict.** Two observations of one mean, so
  `X = !![1; 1]`.
  - The sample mean, `C = !![1/2, 1/2]`, is `M`, with variance factor `1/2`.
  - The first observation alone, `C = !![1, 0]`, is unbiased, with variance factor `1`.
  - This is the inhabited-hypothesis witness `HANDOFF.md` §3 asks for; `VacuityGate` cannot see an
    uninhabited hypothesis (§4).
- claude-ai checked the matrix inequality in floating point: 4,000 random full-rank cases, no
  counterexample, and equality exactly when `D = 0`; the reviewer ran 20,000 more. That checks the
  algebra, not the Lean statement.
- Nothing in the main module goes through Mathlib's probability measures. If there is time, the
  optional second module restates the variance reading with `ProbabilityTheory.covarianceBilin`
  (the reviewer's count: it adds 126 modules and does not reach Invariance). Otherwise
  `HANDOFF.md` §3 lists it.

**Done-means.**
1. **Each new module passes every gate:**
   - `lake build` rc 0 with 0 warnings, header linter on;
   - `AxiomGate` with every new theorem inside the kernel trio and no new exception;
   - `VacuityGate` rc 0;
   - the three text gates rc 0.
2. **No `sorry` ships.** An unproved statement stays out of the files and is listed in `HANDOFF.md` §3.
3. **Both reviews are recorded.** Each verdict — before proving, and after, over every shipped
   statement — is quoted in round 20's fragment.
4. **The fragment is complete.** It carries the per-module counts, the junk cells, the search, and the
   import-closure results.
5. **Consumers are accounted for.** Each new definition has a consumer in round 16's sense, or the
   fragment says why.

**Undo:** yes — new files and their import lines; `git revert`.

---

## Close

1. **Refresh `HANDOFF.md`.**
   - §1: the snapshot from the six commands on a clean tree.
   - §3's "what next": check claude-ai's ranking below against what this order found, and write the
     result. Give each item a `ROADMAP.md` §2 row holding its search command and count, or update the
     row it already has.
     1. **Zsigmondy's theorem** (number theory; 0 Mathlib hits; `ROADMAP.md` §2.5 has its row).
        Mathlib's `docs/1000.yaml` entry Q8074796 records a 2022 formalisation by Mantas Bakšys
        whose code that file has not located (`# TODO: Find the code`). Find it and say what it
        covers before ranking this first. `NumberTheory/PrimitiveDivisor` already has the
        definition and an existence theorem, and names the blocker: a lower bound `Φₙ(a) > n`
        sharper than Mathlib's `sub_one_pow_totient_lt_cyclotomic_eval`.
     2. **Max-flow min-cut, and Menger's theorem** (combinatorics and computing; Q608294, Q928813;
        0 Mathlib hits for `menger` or `max.?flow|min.?cut`).
     3. **More statistics on J3's module:** generalised least squares; Cochran's theorem (Q599876).
     4. **`Applied/Integrity`** from Tier 3 of
        `~/Cowork/lean-rebuild/20260907T231327Z__claude-ai__foundation-ranked-build-order.md`: an
        append-only hash chain whose committed prefix cannot change, and decidable acyclicity for a
        finite relation.
     5. **Statements on Mathlib's own wanted list that this library could prove.** Mathlib v4.34.0's
        `Wanted/` holds 34 `proof_wanted` statements in 18 files. Within reach:
        `Order.height_of_linearOrder`, `Order.coheight_of_linearOrder` and
        `ProbabilityTheory.variance_of_hasLaw_binomial`. Offering them to Mathlib is Dustin's
        decision.
2. Close the `CLAIMS.md` row and update the `INDEX.md` rows.
3. A fresh subagent checks every Done-means against `git diff <this order's first commit>^..master`.
   Record its verdict as an addendum to round 20, as order 0923 did in round 18.
4. **Ask Dustin, in one line:** "Push classical-lean master to DSMain? It moves from <old> to <new>."
   Push only on yes:
   `GIT_SSH_COMMAND='ssh -o BatchMode=yes -o ConnectTimeout=15' git -C ~/work/classical-lean push dsmain master`,
   fast-forward only, never `--force`.
5. **The final chat report:** predicted beside actual, what landed with commit hashes, what stopped
   and why, and what comes next. Include two counts for the roadmap's goal of a library that spans
   mathematics: the net change in theorem constants (filtered list, J1's "before" against the close),
   naming the one removal; and top-level directories under `ClassicalLean/` (expect 9 before and 10
   after). Then, in one line each, the three decisions made on his delegation with his veto open: the
   `[surname]` exception, the decline of information theory part 2, and keeping `mem_closedSimplex`.
   Last, one line on the parked v4.29.0-rc2 build: whether anything still needs it, and if not, the
   command for Dustin to delete it himself.

## Not in this order

- **G-4**: the number-theory track.
- **Publishing to GitHub**: a one-way door, and Dustin's decision. The licence publishes nothing.
- **Offering anything to Mathlib**: Dustin's decision.
- **Retiring any module**: Dustin's decision.
- **Information theory part 2 and the `klDiv` bridge**: declined for now; J2 step 6 records why.
- **Anything in the lane on DSMain.**
