# Round 76 — interlacing, minimax by LP, runs, prices by LP, progeny series (order LEAN-37)

Session: Claude Code `session_01HgueTbGDPjToeXbmtvR4Wd` on DSMain, as dustin, executing order
`LEAN-37` (`records/orders/20261027T234445Z__claude-ai__order-lean37-interlacing-minimax-lp-runs-prices-progeny.md`,
written by claude-ai, copied verbatim; lane `lean/LEAN-37/order.md`, sha256
`06c7c140a70d437e41863acfe4e84685be488d8ee23bce5e24e5680d94b09123`), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `lean-37`, made from `67d05bf` (VACUITY-5's last
commit, equal to `git ls-remote origin master` and `git ls-remote github master`, both read
2026-10-28 15:37 EDT). Nothing pushed. Lighter procedure (store row 20261026-063). Scratch files:
`~/lean/lean37-checks/` (outside the repository). The launch variable
`CLAUDE_CODE_DISABLE_AUTO_MEMORY` printed `1` (2026-10-28 15:37 EDT).

The order's copy: its sha256 read through the connector (`ds_hash`, equal to the value above), then
the file copied byte for byte into `records/orders/` and its sha256 checked equal. The two type-dump
files (`TypeDumpPI.lean`, `g8_typediff.py`) were read through the connector and written from its
replies, each sha256 checked against the order's value (`~/lean/lean37-checks/step2-scripts.sha256`).

Before the work, on the clean tree at `67d05bf`: `lake build` completed (4193 jobs,
`~/lean/lean37-checks/build-before.out`); the type dump `td-before.jsonl` checked
`CHECK records=4163 thm=3666 def=497 elided=0 missing_fields=0` (`~/lean/lean37-checks/td-before.check`).

First part written before the work; completed after it, below.

## Files this round changes

Module files (no module is added):

* `ClassicalLean/Algebra/MinMax.lean` (item 123): `eigenvalues_compression_le`,
  `le_eigenvalues_compression`, two witnesses.
* `ClassicalLean/Analysis/FiniteGame.lean` (item 141): `minimax_eq_of_lp`; import line
  `ClassicalLean.Analysis.LinearProgram`.
* `ClassicalLean/Combinatorics/ArbitrageCycle.lean` (item 145): `hasPrices_iff_of_lp` and its
  private helpers, one witness; import line `ClassicalLean.Analysis.LinearProgram`.
* `ClassicalLean/Probability/LongestRun.lean` (item 143): `measureReal_no_run_two_eq`,
  `measureReal_no_run_three_eq` and their private helpers, two witnesses; import line
  `ClassicalLean.NumberTheory.Tribonacci`.
* `ClassicalLean/Probability/Extinction.lean` (item 149): `progeny_eval_one_eq_extinctionChance`,
  `existsUnique_progeny`, `coeff_progeny_catalan` and their private helpers, two witnesses; import
  lines `ClassicalLean.Combinatorics.AlgebraicGeneratingFunction` and
  `Mathlib.RingTheory.PowerSeries.Trunc`.

Also changed: `records/CLAIMS.md` and `records/orders/INDEX.md` (this order's rows appended at the
bottom, and VACUITY-5's push recorded in VACUITY-5's two rows), this fragment, the order's copy,
`HANDOFF.md` section 1 (one dated paragraph), `ROADMAP.md` (section 1.31),
`tools/vacuity_reviewed.txt` only if a helper is listed, and `records/bridges/LEAN-37/`.

## Order VACUITY-5's push

By records/README.md rule 2, this round's first commit inserts into VACUITY-5's INDEX row (right
after `type dump removed 0, added 0, changed 0, proof-only 0; drift PASS`, before its commits cell)
and its CLAIMS row (before the final ` |`) the text
`; pushed by Dustin: master 67d05bf on both remotes, CI run 40559114678 green`, as the order gives
it, by the script `~/lean/lean37-checks/pushnote.py`, which asserts one matching row and one anchor
in each before inserting. Re-measured before the commit: `git ls-remote origin master` and
`git ls-remote github master` both gave `67d05bfbd0efa80f0de679813b54500ae8c69122`
(`~/lean/lean37-checks/step1-check.out`). The CI run's number and colour are the order's (store row
20261027-017), not measured here.

## Witness scripts (ruling 1)

Lane `lean/LEAN-37/ruling-1.md` (sha256 `f9ddd0b77871156de3d4ad3eef6ca854cabfcd827e9ca071ebcc52e77f1f85c8`):
the three scripts that back counts in witness docstrings, copied byte for byte from DSMain's scratch
folder; each block's sha256 equals its file's (checked by script). The docstrings point here.

### w143-runs.py

Old path `~/lean/lean37-checks/w143/runs.py`, sha256 `45f469e02d7ff6b2dd5a1c1486f6969863cc62a6dc5221be54d056bf004c5e77`.

```python
# Item 143 witness: of the 16 sequences of four fair flips, how many have no run of 2 / 3 trues.
from itertools import product
seqs = list(product([False, True], repeat=4))
no2 = sum(1 for s in seqs if not any(s[k] and s[k + 1] for k in range(3)))
no3 = sum(1 for s in seqs if not any(s[k] and s[k + 1] and s[k + 2] for k in range(2)))
print("sequences", len(seqs), "no run of 2:", no2, "no run of 3:", no3, "windows of 2:", 3, "windows of 3:", 2)
```

### w145-cycles.py

Old path `~/lean/lean37-checks/w145/cycles.py`, sha256 `d5f62c79684d9361f868b987e249aea1fbcab551a521d3088c1477d012ae11e0`.

```python
# Item 145 witness: every cycle (closed walk c0 -> c1 -> ... -> ck -> c0, length 1..7) of r on Fin 3.
from fractions import Fraction as F
from itertools import product
r = [[F(1), F(2), F(1, 2)], [F(1, 2), F(1), F(1, 2)], [F(1, 2), F(1, 2), F(1)]]
mx, eq1, n = F(0), set(), 0
for k in range(1, 8):
    for c in product(range(3), repeat=k):
        p = F(1)
        for a, b in zip(c, c[1:] + c[:1]):
            p *= r[a][b]
        n += 1; mx = max(mx, p)
        if p == 1:
            eq1.add(frozenset((a, b) for a, b in zip(c, c[1:] + c[:1]) if a != b))
print("cycles", n, "max product", mx)
print("off-diagonal edge sets of the cycles with product exactly 1:", sorted(map(sorted, eq1)))
```

### w149-series.py

Old path `~/lean/lean37-checks/w149/series.py`, sha256 `0e8145adf49f11793ba7e0a56c694314def7e7da5fe150dde575c7613502fea3`.

```python
# Item 149 witnesses: the coefficients of T = X * f(T), f(s) = sum p_k s^k, by fixed-point iteration
# to degree N (coefficient n of T depends only on coefficients < n, so N iterations are exact to N).
from fractions import Fraction as F
from math import comb
N = 80
def solve(p):
    T = [F(0)] * (N + 1)
    for _ in range(N + 1):
        fT = [F(0)] * (N + 1); P = [F(1)] + [F(0)] * N  # P = T^k
        for k, pk in enumerate(p):
            for i in range(N + 1): fT[i] += pk * P[i]
            P = [sum(P[a] * T[i - a] for a in range(i + 1)) for i in range(N + 1)]
        T = [F(0)] + fT[:N]
    return T
T1 = solve([F(1, 4), F(1, 4), F(1, 2)])
print("law (1/4,1/4,1/2): first coefficients", [str(c) for c in T1[:6]])
print("  nonzero coefficients up to", N, ":", sum(1 for c in T1 if c != 0), "; partial sum", float(sum(T1)))
T2 = solve([F(1, 2), F(0), F(1, 2)])
cat = lambda n: comb(2 * n, n) // (n + 1)
print("law (1/2,0,1/2): odd = catalan/2^(2n+1):", all(T2[2 * n + 1] == F(cat(n), 2 ** (2 * n + 1)) for n in range(N // 2)),
      "; even = 0:", all(T2[2 * n] == 0 for n in range(N // 2 + 1)), "; partial sum", float(sum(T2)))
```

## Completed after the work (2026-10-28 UTC)

### What landed

| commit | what |
|---|---|
| `2123af1` | records first (this fragment's first part, the order's copy, the INDEX and CLAIMS rows, VACUITY-5's push) |
| `f1e1a0e` | item 123, `ClassicalLean/Algebra/MinMax.lean`: `eigenvalues_compression_le`, `le_eigenvalues_compression`, two witnesses |
| `cbaf9d5` | item 141, `ClassicalLean/Analysis/FiniteGame.lean`: `minimax_eq_of_lp` (no hypothesis, no witness); import `ClassicalLean.Analysis.LinearProgram` |
| `ab2c5c5` | item 145, `ClassicalLean/Combinatorics/ArbitrageCycle.lean`: `hasPrices_iff_of_lp` and helpers, one witness; import `ClassicalLean.Analysis.LinearProgram` |
| `b834a99` | item 143, `ClassicalLean/Probability/LongestRun.lean`: `measureReal_no_run_two_eq`, `measureReal_no_run_three_eq` and helpers, two witnesses; import `ClassicalLean.NumberTheory.Tribonacci` |
| `f6a9dd7` | item 149, `ClassicalLean/Probability/Extinction.lean`: `progeny_eval_one_eq_extinctionChance`, `existsUnique_progeny`, `coeff_progeny_catalan` and helpers, two witnesses; imports `ClassicalLean.Combinatorics.AlgebraicGeneratingFunction`, `Mathlib.RingTheory.PowerSeries.Trunc` |
| `afb7d99` | review r1's fixes (findings 1, 2, 3, 5) and ruling 1 (the witness scripts below; docstring pointers) |
| `43c9019` | `HANDOFF.md` section 1, `ROADMAP.md` section 1.31 (documents, G) |

Statements: all nine as drafted; type check (`set_option pp.fullNames true in #check @…`, draft on
the clean `67d05bf` against the landed module, compared by `typecmp.py` after universe renaming)
SAME for all nine, the last runs after `afb7d99` (planted control: without the rename map, 0/2 for
item 123). Narrowing: none. Verdicts (cold review r1): 123, 141, 143, 145 FAITHFUL; 149's
`progeny_eval_one_eq_extinctionChance` and `existsUnique_progeny` GENERALIZED (no `p 0 > 0`; the
uniqueness a theorem of its own), `coeff_progeny_catalan` FAITHFUL with one extra conjunct. The
order predicted 141 GENERALIZED (no nonempty sides); the review called it FAITHFUL to its row (the
row's statement is item 85's, which has no nonempty sides either); HANDOFF and ROADMAP keep the
order's GENERALIZED against `minimax_eq_of_matrix`.

Departures from the drafts, proof text and helpers only: the deprecated `if_pos`, `if_neg`,
`tendsto_finset_sum` replaced as the warnings say; never-executed tactics removed; goal-changing
`show` became `change` (the module build's style linter, 18 places: FiniteGame 2, ArbitrageCycle 3,
LongestRun 8, Extinction 5); `lpKey` lost its unused `[DecidableEq ι]` (the `unusedDecidableInType`
linter) and uses `classical`; `lrPre` is a `private abbrev`, not `@[instance_reducible] def` as the
linter suggests, because the witness gate's attribute allowlist (`simp`, `instance`) refuses that
attribute (first LongestRun gate run: COPY-ERROR); review finding 3 replaced `LpPosWalk` and its
three lemmas by Mathlib's `List.IsChain`.

The cold review (one fresh subagent; `~/lean/lean37-checks/review/review-1.md`): PASS WITH
FINDINGS, no MAJOR, seven MINOR. Applied: 1 and 2 (docstrings), 3 (in part: `LpPosWalk` and its
lemmas; `lpMult` kept, its equality with `List.count` on `L.zip L.tail` was read, not checked), 5
(docstring wording). Not applied: 4 (a general existence theorem in `AlgebraicGeneratingFunction`,
outside this order's Scope: a follow-up), 6 (the session's packet extractor repeated blocks; the
reviewer read the module sources), 7 (a note: item 123 uses the lemmas beneath
`eigenvalues_eq_iSup_iInf`). No statement and no witness argument changed, so no second pass.

Witnesses (seven, rule 2's form, each OK in the witness gate): 123 twice on `ℝ³`,
`T = diag(3, 2, 1)`, `V = span {e₀ + e₁, e₂}`; 145 on three assets with rates `2`, `1/2`, `1/2`;
143 twice on four fair flips (`Fin 4 → Bool`, `(1/16) · count`); 149 on the law `(1/4, 1/4, 1/2)`
and on the law `1/2` at `0` and `2`, each `T` from `existsUnique_progeny` (the review ruled this
acceptable: no circularity, by a dependency walk with a positive control).

Heads-ups passed in by Dustin: (1) witness docstrings cited DSMain scratch paths: ruling 1, applied
below and in `afb7d99`; (2) step 5's predictions predated `afb7d99`: revision 2 written before G
(below).

### Expected results (step 5)

`~/lean/lean37-checks/expected-step5.txt`, revision 2, sha256
`a5c63327873d6fb99de4b8baddebc27470acad6d72bda491abed49f7ec14a42c`, written after `afb7d99` and
before G and before any gate ran; revision 1 (`expected-step5-r1.txt`, sha256 `467bddd2…906e`:
added 204, thm 171, AxiomGate 3837) predated `afb7d99`'s removal of four helpers (21 constants
gone, 3 proof constants of `lpKey` renumbered). The ADDED list `added-predicted.txt`, sha256
`35af0cbe…e5e9`, 183 lines.

### The gates, on the clean tree at G `43c9019`

| gate | expected | measured |
|---|---|---|
| `lake build` | 4193 jobs, 0 warnings | `Build completed successfully (4193 jobs).`, 0 warning lines, 0 error lines |
| AxiomGate | PASS 3827 | `axiom gate PASS — 3827 theorem constant(s)`, 0 scoped exceptions |
| check_sorry | PASS | `check_sorry PASS — 140 file(s)` |
| check_records | PASS 140 | `check_records PASS — 140 module(s)`, 116 files searched |
| VacuityGate | PASS | `vacuity gate PASS`, 1 reviewed helper, 0 VACUOUS-PENDING, 0 rule-5 run-outs |
| run_vacuity_tests | 0 mismatches | `89 tests, 47 flagged, 0 rule-5 run-outs, 0 mismatches` |
| banned scan | PASS | `banned_vocab_scan PASS — 140 file(s) … 0 hits` |
| witness gate, library | PASS, OK 189, copy-error 0 | `WITNESSGATE PASS modules=140 elaborated=72 OK=189 … TYPED=205 … LISTED=1 … copy-error=0`, 1642.9 s |
| witness_gate_tests | pass | `WITNESSGATE-TESTS 119 cases, 0 mismatch(es)` |
| module count | 5729 | `MODULES 5729` |
| type dump | 4346 records; removed 0, added 183, changed 0, proof-only 0 | `CHECK records=4346 thm=3827 def=519 elided=0 missing_fields=0`; `DIFF removed=0 added=183 changed=0 proof_only=0`; the 183 ADDED lines equal `added-predicted.txt` (`diff`, no output) |
| gate 7 | ALL PASSED | `SUMMARY modules=140 failed=0`; the three standard axioms; planted fault `FAILED ClassicalLean.Analysis.LogDrag.mean_log_one_add_le` caught; `ALL PASSED for 43c9019c0323cb3e0b8c6fcb9eea7b46b242cc3a` |
| drift (on G) | PASS | `PASS no drift` |

Misses against the order's own predictions: none in the gates. The push-review prediction "only
ArbitrageCycle line 45" for the `admit` prose is line 46 now (the module's new import line).
Outputs: `~/lean/lean37-checks/G-*.out`.

### Bridge search

`python3 -I tools/bridge_search.py --diff records/bridges/LEAN-36/ --out
~/lean/lean37-checks/bridges/LEAN-37`, rc 1: 3039 pairs, 788 shape candidates, 55 NEW pairs, 15
NEW shapes, 42 GONE keys. Read: 50 of the new pairs share only general lemmas (`add_mul`,
`pow_mul`, `Finset.sum_ite_eq'`, `Nat.cast_sum`, `Finset.exists_min_image`, …); `NumberTheory.Catalan
× Probability.Extinction` shares `catalan`, but Mathlib's `succ_mul_catalan_eq_centralBinom` and
`catalan_eq_centralBinom_div` already give what the library's Catalan module adds, so no proof needs
both modules; the Fibonacci modules × `Probability.LongestRun` share `Nat.fib` and
`Nat.twoStepInduction`, and a statement joining them only restates Mathlib's Fibonacci facts at
`fib (n + 2) / 2^n`; `NumberTheory.LucasSequenceGeneratingFunction × Probability.Extinction` share
`PowerSeries` machinery, not an object; the 15 new shapes are all `stochastic matrix` on
`Analysis.FiniteGame`, the shape's regex matching `vecMul` in `minimax_eq_of_lp`'s proof (no
stochastic matrix there). No real bridge: no row appended. Baseline: `records/bridges/LEAN-37/`.

### Report tool

`lake env lean tools/UninformativeReport.lean`, once: no `CLOSES` line names this order's theorems
(they are listed `A OPEN` or `A DEPENDENT`).

Theorem-constant count: 3827 (3666 + 161), measured by AxiomGate at G.
