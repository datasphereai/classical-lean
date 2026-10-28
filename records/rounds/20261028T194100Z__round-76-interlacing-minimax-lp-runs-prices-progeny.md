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
