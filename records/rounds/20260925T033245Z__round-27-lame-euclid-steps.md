# Round 27 — Lamé's theorem: the number of steps of the Euclidean algorithm (order G-9, J1 and J2)

Session: Claude Code `session_01JcSz4wLVqhs25F7venK1Sh` on helios, executing order `G-9`
(`records/orders/20260924T235500Z__claude-ai__order-g9-lame-frobenius.md`), jobs J1 and J2. Lean and
Mathlib v4.34.0 throughout. Evidence: `~/work/_bump-evidence/g9/` — `evidence.log` (one line per
command: UTC time, label, the command's own rc, its `PIPESTATUS`, the prediction, the output file),
`out/` (each command's output), `critics/` and `reviews/` (every critic and review verbatim, with
the brief it was given), `work/` (the proofs as written), `j1-table.md` (J1's predicted-beside-actual
table, sha256 `57e31f06…52a7`). Times are UTC, from `evidence.log`.

This fragment opens with J2's commit, which lands the new module
`ClassicalLean/NumberTheory/EuclidSteps.lean` with its import line in `ClassicalLean.lean`. The gate
numbers quoted for that commit are `land.sh check`'s, on the tree with the change in place (mixed:
the change and nothing else); the clean-tree numbers after it are recorded at the records step.

## J1 (read-only), 2026-09-25 01:09–02:34Z

The order's sha256 matched Dustin's value (`c8e6529f…37f4`). Order G-8 closed: its `INDEX.md` row and
`CLAIMS.md` row closed, its 9 landed hashes ancestors of `master`, the only later commit `196a87d`
(its Close check); `master`, `dsmain/master` and DSMain's `master` all `196a87d`; `HANDOFF.md` §6
lacks exactly the push `87683e3..196a87d` (2026-09-24T23:25:19Z, the reflog; `push.log`). Gates 2–6
passed at `196a87d` (1434 theorem constants, 49 modules, 19 records files); gate 1's read-only probe
"All targets up-to-date (3799 jobs)". Appendix A: 1617 constants, 49 modules, islands `Catalan`,
`CompositumDiscriminant`, `Tolerance`; `DupCheck: 5 TWIN, 0 SWAP`; `pairs.py`
`modules=49 edges=82 rare_df<=3 pairs_without_edge_sharing_rare=87`.

**The tools (item 0, rule 23).** `g9/ev.sh` is `g8/ev.sh` with its evidence path changed; its eleven
fail tests of round 25 held (`t2a`–`t2a5`, `t1b`–`t1f`; `t2d2-outer` evidences the run with
`BASH_ENV` unset). `g9/land.sh` is `g8/land.sh` with its evidence path, `export LC_ALL=C`, and each
`comm`'s exit status read into a `fail` line (`0.land2`), which closes round 26's Close finding: on
helios `sort` and `comm` are the Rust coreutils 0.8.0, `sort` collates by the locale and `comm`
compares bytes (`0.sort`, `0.comm`). Round 25's eleven `land.sh` cases held on a throwaway clone, and
the new cases held (`land-test-*-r2`): a mixed-case path list passes; the unfixed script gives a
false report when a listed path is unchanged (`mixed-unchanged-unfixed`) where the fixed one reports
exactly the unchanged path; a `comm` that exits 1 refuses the check, where the unfixed script
passed it. The Python gates behave the same under `LC_ALL=C` (`0.gatesC`).

**Findings that correct the order's records** (none a wrong theorem): §0 row 6 (seven pairs share
four rare constants, not four; the four ranked third to sixth are `CompositumDiscriminant`'s);
§0 row 7 and J1 item 11 (the tight pairs: over all `a` the largest step count is 5, 10 and 15 for
one, two and three digits of `b`, attained by `(13, 8)`, `(144, 89)`, `(1597, 987)`; `(233, 377)`'s
13 is only the maximum of the grid `a, b ≤ 600`; four digits reach 19, not 20; `S5-tight`); §0 row 9
(the prime-power cells are 20 and 16 with `11³` included, against the order's 19 and 15); §0 row 12
and the J2 Scope ("prior art: none in Mathlib" — Mathlib's continued fractions prove
`GenContFract.succ_nth_fib_le_of_nth_den`, one Fibonacci index weaker, no step count, `S6-cf`; the
order's `fib` search looked only in `Data/Nat/Fib/`, and the wider one finds 10 files, `S6-wide`);
J1 item 7 (`NumberTheory/Lucas` already reaches `Mathlib.Data.Nat.Digits.Lemmas`, nine imports deep
through `Mathlib.NumberTheory.Real.GoldenRatio`, `7a`, `7a-path`); J1 item 11 (Mathlib's `Wanted/` is
in the package on helios, `11.0`); §0 row 8 (`decide` cannot evaluate `euclidSteps`, which is by
well-founded recursion, `probe`); `Nat.digits_len` is a deprecated alias of `Nat.length_digits`
(`s2-04b`); the order's drafts (`/tmp/claude-ai-g9/`) are not on helios, so §0 row 11's draft hashes
could not be checked; the order's J1 Undo line ("nothing to undo in the repository") stopped holding
at J1's commit `f90f392` (undo: revert it, and restore the order file to `~/Cowork/lean-orders/`
from git).

**J1's misses and lapses** (every miss with its explanation is in `j1-table.md`): `0.land1` ran in
parallel with an edit the tool refused (the file had not been read), so it measured the unedited copy
— void, as is `0.land-copy`; that refusal was logged `NOT RUN` at 01:43:14Z, not in the next helper
call (01:13:40Z, rule 30); six later edit refusals (about 02:07Z) were noted in the next helper call
and given one line each at 02:31Z; the first `mixed-unfixed` case was a harness error (the case
before had committed `records/x.md`); `Defs.lean`, predicted in item 11 (b), ran only in the
supplement (`S1-defs`); `predictions-j1.md` was first hashed after item 0 ran (each prediction was
also fixed in its `ev.sh` call); `namecheck` v1 was stopped after 620 s (rc 143, void) and replaced;
the v2 drafts' own comment lines needed five runs to fit 100 characters; one inline `python3 -c`
(`critics-hash`); commands outside the helper are listed in plan v3 §6. **Rule 21, both jobs:** the
item-11 searches and cells ran before the first drafts (`dj2` 01:29:50Z, `dj3` 01:30:01Z), but the
supplement that the plan critics asked for ran after them — for J2 the tight pairs over all `a`
(`S5-tight` 02:08:44Z), the Lean-side definition reads (`S1-defs`, `S1b-reads` 02:08:58Z) and the
widened `fib` search (`S6-cf`, `S6-wide` 02:09:02Z); none changed a statement, and the drafts were
re-hashed and re-elaborated after every cell (`T3-dj2v2` 02:31:16Z). A closed instance,
`euclidSteps 3 1 = 1` (the base value (L5) needs), was proved by `simp` in `drafts/DefProbe.lean`
(`probe`, 01:30:02Z), before any statement review (rules 16 and 18); no line of it is reused.

**The plan's review.** Four cold critics (statements, compliance, routes, evidence; 01:47–02:04Z)
and a delta critic (02:13–02:30Z), briefs built by `brief_make.py` quoting rules 16–30, all
GO-WITH-FIXES; every finding disposed in plan v3 (`plan-j2-j3.v3.md`, sha256 `84946016…8f18`), which
Dustin approved at 02:43Z (`approval`). Then the deferred `lake build` (rc 0, 0 warnings, 3799 jobs,
nothing rebuilt; `5.1`), the order filed by its own line (`file-order`, sha256 unchanged), and J1's
commit `f90f392` through `land.sh` (the six gates each against its logged prediction, gate 6 at 20
records files; `j1-gate-verify`). The "before" evidence (`g9-before/`, by `before.sh`, whose refusal
of a non-empty directory was fire-tested first): type dump `CHECK thm=1434`, `#COUNTS raw=1434
filtered=863 private=190`, `MODULE-THM-COUNT total=1434 modules=49`, Appendix A as above.

## J2 — Lamé's theorem, `ClassicalLean/NumberTheory/EuclidSteps.lean` (new)

**Searches** (rule 21; J1 item 11, `j1-search.sh`), over `.lake/packages/mathlib/Mathlib`: the
order's row 12 reproduced exactly (`lam[ée]` 0; `euclid` with step/iteration/count 0; `gcd` with
steps/fuel/iterations 4, all docstrings — three in `RingTheory/DiscreteValuationRing/Basic.lean` on
a DVR's two-step gcd, one in `Tactic/NormNum/LegendreSymbol.lean`); `Nat.gcd.induction` in core at
`Init/Data/Nat/Gcd.lean:79`; `Nat.fib_add` `:141`, `Nat.fib_add_two` `:75`, `Nat.fib_lt_fib_succ`
`:97`, `Nat.fib_mono` `:84` (`Data/Nat/Fib/Basic.lean`); `Nat.lt_base_pow_length_digits`
`Data/Nat/Digits/Defs.lean:390`. `docs/1000.yaml` lists Lamé's theorem (Q230848) by title only
(`r13`: 1199 entries, 955 with no `decl`, `decls` or `url`).

**Junk cells** (`j2cells`, every line predicted first; all held): the three bounds on the grid
`a, b ≤ 600` (the first bound 360,600 cells, the second 180,300, Lamé's 361,201) and on 201,100
seeded random pairs below `10¹²`, 0 failures; without its hypothesis the first bound fails at `b = 0`
for all 601 `a`, the second fails on 7,359 of the 180,901 cells with `b ≥ a` (on the diagonal
exactly at `a ∈ {0, 1}`) and holds at `b = 0 < a`; the attaining pairs for `n < 60`; `10 ^ k < F (5k +
2)` fails exactly at `k = 0`; the route of order §0 row 8 cell by cell (361,201 cells, 0 failures).

**Statements, reviewed before any proof** (rule 16). Drafted after the searches and cells, re-drafted
after the plan critics, and sent with J3's to one cold reviewer each (`reviews/stmt-j2.md`, sha256
`1c06acca…b916`; dispatched 02:47:06Z, verdict saved 03:04:46Z). The reviewer:

> Every statement is true as written, has exactly the hypotheses it needs, and has exactly the order's content.

It ruled the public nonzero hypotheses into Mathlib's form, which the order writes as `0 < b` and
`1 ≤ k` — a change of form, not content:

> **Hypothesis form: `b ≠ 0` and `k ≠ 0` in the public statements.**

> Content is unchanged (`Nat.pos_iff_ne_zero`).

and renamed five declarations (`euclidSteps_of_ne_zero`, `fib_euclidSteps_add_one_le_right`,
`fib_euclidSteps_add_two_le_left`, `euclidSteps_fib_add_three_fib_add_two`,
`euclidSteps_lucas_add_two_lucas_add_one`), each checked free. On the prior art:

> `GenContFract.succ_nth_fib_le_of_nth_den` is related prior art to credit, not a restatement of any J2 statement.

The statements as landed are the reviewer's block byte for byte (`j2-block-cmp`), and elaborated
before any proof with 13 `sorry` warnings and nothing else (`j2-stmts-elab`).

**Proofs** (after the verdict: `j2-proof-start` 03:09:13Z). The route is order §0 row 8's (derived by
claude-ai, rule 19), with the departures the module docstring names: the attaining pairs' base cases
evaluate `euclidSteps` through its two equations (`decide` cannot), and `a % b + b ≤ a` goes through
`Nat.mod_eq_sub_mod`. Two proof lines predate the verdict (rule 18): plan v2 §2 (about 02:11Z) and
v3 §2 (about 02:33Z) already carried the two equations' proofs, `rw [euclidSteps.eq_def a 0,
dif_pos rfl]` and its `dif_neg` twin, and the landed lines descend from them; no other J2 proof text
was composed before 03:04:46Z. `j2-proof-1` (03:10:08Z) had 3 warnings against a prediction of none —
`dif_pos` and `dif_neg` are deprecated in favour of `dite_eq_left`/`dite_eq_right` (core
`Init/Core.lean`; since 2026-07-21 by the post-proof reviewer's reading, not measured here), and the
style linter asked for `change` in place of one `show` — so the statement review's own suggestion
`dif_neg hb` was a deprecated name; `j2-proof-2` (03:10:34Z): rc 0, no output.

**The census (rule 27), beside the prediction.** Predicted `thm=16 private=5 filtered=14` from the
statements' census (`j2-census`, 03:11:15Z); measured **`thm=33 private=14 filtered=14`**. The 17
more are `_proof_1_N` auxiliaries, one per `omega` call (`omega` wraps its proofs with
`mkAuxTheorem`), which the post-proof reviewer confirmed:

> There is exactly one per `omega` call

They are internal details, outside the filtered list, and they count in gate 2: the landing's
prediction is 1434 + 33 = 1467 theorem constants, and the filtered list 863 + 14 = 877. The axiom
check (a run of `collectAxioms` on each new theorem, fire-tested on a planted `sorry`,
`axioms-fire`): all 33 within `propext`, `Classical.choice`, `Quot.sound` (`j2-axioms`; the
prediction's 16 missed with the census).

**Post-proof review** (rule 13; `reviews/post-j2.md`, sha256 `5e7455b5…a1c`; dispatched 03:14:10Z,
saved 03:30:31Z):

> Every proof is correct.

> The 13 statements and the definition are byte-identical to the reviewed block.

It required three docstring corrections (the route item's `n'`, the Sources paragraph, the
Hypotheses paragraph) and proposed one more (the four-digit maximum), each as exact text; applied
verbatim — the file with the three required ones equals the reviewer's proposed file
(`post-j2-apply-cmp`, `5ab77a51…064c`), and the fourth is its text exactly (`post-j2-f7-diff`). No
proof line changed, so rule 29's delta check does not apply; the file was re-elaborated (`j2-proof-3`:
rc 0, no output), re-censused (`j2-census-3`: `thm=33 private=14 filtered=14`) and re-scanned
(`j2-textgates-3`).

**Landing.** The landed module is the reviewed file byte for byte (`j2-place`: `cmp` rc 0, sha256
`43258c08…d650`). With it and its import line in place, `check_records.py` failed as predicted,
naming it (`j2-gate6-fail`: `UNRECORDED  ClassicalLean/NumberTheory/EuclidSteps.lean`); this fragment
names it. `lake build ClassicalLean.NumberTheory.EuclidSteps`: rc 0, 0 warnings (`j2-build-module`).
The Lean-side import closure (`env.header.moduleNames`, `ImportCheckEuclid.lean`; `j2-importcheck`):
3397 modules, 3 of the library's — `EuclidSteps`, `Lucas`, `FactorialPart`; positive controls
`Lucas` and `Mathlib.Data.Nat.Digits.Lemmas` true, negative controls `LucasApparition` and
`ZsigmondyPowSubPow` false. `Mathlib.Data.Nat.Digits.Lemmas` is imported as the order's §2 names it;
`Lucas` already reaches it, so it adds no module.

**Per-module count**: `NumberTheory/EuclidSteps` 33 theorem constants (14 private; 14 on the filtered
list), from the census of the landed text.

**Commit**: `4dd8904` (J2, 03:35:10Z, `j2-land-commit`), after J1's `f90f392`. Hash added by the
records commit (below).

**After the landing** (clean tree, `clean_gates.sh` and `after.sh j2`, each line predicted first,
`land/pg-j2-clean.txt`, `land/pr-j2-after.txt`): the six gates pass — build rc 0, 0 warnings, 3800
jobs; 1467 theorem constants; 50 files; 50 modules and 21 records files; `#COUNTS raw=1467
filtered=877 private=204`; the raw list against `g9-before` 33 lines added, 0 removed; the type dump
`CHECK thm=1467` and against `g9-before` `DIFF removed=0 added=36 changed=0 proof_only=0` (the 33
theorems and three definitions: `euclidSteps`, its `_unary` form and the compiler's `_unsafe_rec`);
`MODULE-THM-COUNT total=1467 modules=50`, the one differing line `+ EuclidSteps 33`; Appendix A:
1653 constants (a hand estimate of 1652 missed the `_unsafe_rec` definition), islands 3,
`EuclidSteps usedBy= 0 uses= 1`, `Lucas usedBy= 5`, `DupCheck: 5 TWIN, 0 SWAP`; `pairs.py`
`modules=50 edges=83 rare_df<=3 pairs_without_edge_sharing_rare=90` (not predicted).

**The records step** (J2's method 4 and J3's records, one commit after both landings, as plan v3 §4
set out; so J2's records came after J3's landing, rule 18): `HANDOFF.md` §6 gains rules 26–30 with
the lead-in naming five orders, their text order G-9's except the emphasis (italics, as rules 1–25)
and "§0 row" qualified as order G-9's; the dated push line for `87683e3..196a87d`; a standing answer
for `TZ=UTC` and for `LC_ALL=C` with `sort` and `comm`. `HANDOFF.md` §3: the fourth item and two
open items done. `ROADMAP.md`: row 2.13 (the pairs the module proves, `(13, 8)`, `(144, 89)`,
`(1597, 987)`, not the order's `(5, 8)`, `(55, 89)`, `(233, 377)`), and dated lines in §1.15 and
§2.1.
