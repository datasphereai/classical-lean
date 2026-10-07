# ORDER G-8 — Zsigmondy's theorem for aⁿ − bⁿ and its rank of apparition; the Catalan numbers and V_p in characteristic p

Written 2026-09-24T18:25:00Z by claude-ai (Cowork, linked to helios) for one Claude Code session on
helios. Library: `~/work/classical-lean`. **Source of truth:** this file and `records/orders/INDEX.md`.
It waits in `~/Cowork/lean-orders/` until J1 files it, and starts only after order G-7 is closed.
A second agent reviewed it cold, twice, before it was placed there. The first pass found one major
point (rule 23 could not bind before its helper existed) and twelve minor ones; the second confirmed
those fixes, one of them incomplete, and found three minor points, which were applied without a
third review. Every number in §0 that the reviewer could re-run in the cloud, its own scripts
reproduced.

It rests on three things:
- **Order G-7's close**: `HANDOFF.md` §3's ranking puts Zsigmondy's theorem for `aⁿ − bⁿ` first
  and Carmichael's theorem second; its "also open" list names `lucasV P Q p = P ^ p` in
  characteristic `p` and the type-dump tooling item; `ROADMAP.md` §2.1 records the sharp existence
  criterion as not proved, and §1.15 four islands.
- **claude-ai's measurements of the library at `87683e3`** (§0): the declaration graph (four
  islands, and `LucasApparition` used by no module), a new comparison of module pairs whose
  statements share rare Mathlib constants but which never use each other, the duplicate check,
  exact checks of every statement below and of each step of the route J2 is given, and the Mathlib
  searches. They also measure Carmichael's theorem, and find it larger than "in reach now" (row 13).
- **The lessons of order G-7's run** (§1, rules 20–25). Its mathematics passed every gate. Its
  Close check failed nine items: one type-dump Done-means, ruled on in §2, and eight records and
  process lapses (round 24's addendum).

Three jobs, J1 to J3, then a close. Each has Goal / Scope / Done-means and an undo line. A STOP at a
gate is a report, not a close.

---

## 0. What claude-ai measured

Read-only, 2026-09-24 between 17:45Z and 19:15Z (drafted at 18:25Z, corrected after its
reviews): the helios tree at `87683e3`, run through the four scripts of Appendix A with
`lake env lean` from the repository root (no `lake build`, nothing written in the repository;
`git status --porcelain` empty before and after), with scratch files in `/tmp/claude-ai-g8/`; the
evidence of order G-7 under `~/work/_bump-evidence/g7/`, read-only; a sparse clone of Mathlib
v4.34.0 (`5ed2965256`); order G-7's session page; exact checks in Python (integers, `fractions`,
sympy). Line numbers were read then; find each place by its text. "The reviewer" is the cold
reviewer of this order; facts it found are marked so.

| # | Fact | Value |
|---|---|---|
| 1 | Order G-7 | Closed (`INDEX.md`, `CLAIMS.md`). `master`, `dsmain/master` and `ls-remote dsmain master` are all `87683e3`. The push `cca6f8a..87683e3` is in `~/work/_bump-evidence/push.log` (`rc=0 push [G-7, Dustin's yes 2026-09-24]`) and in the `dsmain/master` reflog at 2026-09-24T17:43:46Z (`update by push`), and not yet in `HANDOFF.md` §6, by design (G-7's Close step 4). `~/Cowork/lean-orders/` held no file before this one. |
| 2 | The library | 48 modules in 10 top-level directories; 1283 theorem constants and a filtered list of 816 (round 24; `g7/after-j3/list-raw.txt` 1283 lines, `list-filtered.txt` 816). 15,302 lines under `ClassicalLean/` (14,757 at `e686bde^`). 49 files whose line 4 is `Authors: Dustin [surname], Claude (Anthropic)`. Gate 6 searches 16 records files. |
| 3 | Four orders, measured from git and the rounds | See the table after this one. |
| 4 | Declaration graph (`DeclGraph.lean`, then `islands.py`) | 1461 constants in 48 modules. **Four islands**, unchanged since round 23: `Combinatorics/AlgebraicGeneratingFunction`, `NumberTheory/Catalan`, `NumberTheory/CompositumDiscriminant`, `Order/Tolerance`. **`NumberTheory/LucasApparition` is used by no module** (`usedBy= 0 uses= 2`): `PrimitiveDivisor` imports it and names its constants only in an `example`. `NumberTheory/Zsigmondy` uses two modules and is used by none. |
| 5 | Duplicates (`DupCheck.lean`) | `DupCheck: 5 TWIN line(s), 0 SWAP line(s)`, the five labelled "Mathlib re-export"s of `GoldenRatio/Characterisations`. |
| 6 | Pairs that share rare concepts and no use (`pairs.py`, new, Appendix A) | For two modules with no use in either direction, the Mathlib constants that both modules' public statements name and that at most three modules' statements name. 76 ordered pairs of modules have a use; 84 unordered pairs without one share such a constant. Highest scores: `AlgebraicGeneratingFunction ~ RecurrenceGeneratingFunction` (10 shared, among them `PowerSeries.C`, `PowerSeries.X`, `PowerSeries.coeff`) and `S3Quaternion ~ SU2SO3` (10: the quaternion star and parts, `Submonoid`). `LucasApparition ~ Zsigmondy` shares 4 (`GT.gt`, `Int.instDvd`, `Int.natAbs`, `semigroupDvd`). J2 joins that pair, J3 the first. The score is a sum of logarithms of inverse frequencies: it ranks candidates; it does not show that a bridge exists. |
| 7 | Zsigmondy for `aⁿ − bⁿ` | A prime `p` is a primitive divisor of `aⁿ − bⁿ` when `p ∣ a ^ n - b ^ n` and `¬ p ∣ a ^ m - b ^ m` for `0 < m < n` (over `ℕ`, truncated subtraction). For coprime `0 < b < a` and every `n`, one exists exactly unless `n = 1 ∧ a = b + 1`, or `n = 2` with `a + b` a power of `2`, or `(a, b, n) = (2, 1, 6)`. Checked from the definition, exactly (gcd division, no factoring), over `a ≤ 120`, `n ≤ 80`: 355,185 cells, 0 mismatches. Each hypothesis fails when dropped (`a, b ≤ 30`, `n ≤ 30`): not coprime, 54 of 4,898 cells, first `(4, 2, 6)` (`4⁶ − 2⁶ = 4032 = 2⁶ · 3² · 7`, with `2 ∣ 4 − 2`, `3 ∣ 4² − 2²`, `7 ∣ 4³ − 2³`); `b = 0`, 28 of 31, first `(1, 0, 3)`; `a = b`, 28 of 31, first `(1, 1, 3)`; `a < b`, 8,047 of 8,618. Four fire tests of the checker, each caught: dropping `(2, 1, 6)` (1 cell), making all of `n = 1` exceptional (248), dropping the `n = 2` clause (14), dropping the `n = 1` clause (29). |
| 8 | The route for row 7, each step checked | `Φₙ(a, b) = b ^ φ(n) · Φₙ(a / b)`, the homogenized cyclotomic value, in exact integers over coprime `1 ≤ b < a ≤ 80`, `1 ≤ n ≤ 72`: `aⁿ − bⁿ = ∏_{d ∣ n} Φ_d(a, b)` (141,480 cells); for `n ≥ 2` every prime of `Φₙ(a, b)` not dividing `n` is primitive (139,515 cells, by gcds); a prime dividing both `n` and `Φₙ(a, b)` is `P(n)`, the largest prime factor of `n` (13,855 cells), and for `n ≥ 3` it divides `Φₙ(a, b)` once (13,204 cells; at `n = 2` it fails, `4 ∣ a + b` for 327 coprime pairs with `a ≤ 80`); `Φₙ(a, b) > P(n)` for `n ≥ 3` in 137,549 of 137,550 cells, the one failure `Φ₆(2, 1) = 3 = P(6)`. The size, for `a − b ≥ 2`: `Φₙ(a, b) > (a − b)^φ(n) ≥ 2^φ(n) ≥ 2^(P − 1) ≥ P` (133,906 cells, `n ≥ 2`). For `a = b + 1`, with `n = m · P`, round 22's four cases hold with `(a, b)` in place of `(2, 1)` (5,609 cells; and `Φₙ(b + 1, b) > P(n)` for `b ≤ 300`, `3 ≤ n ≤ 60`, 17,400 cells, except `(2, 1, 6)`): `P ∣ m`: `Φₙ(a, b) = Φₘ(aᴾ, bᴾ) > (aᴾ − bᴾ)^φ(m)` and `aᴾ − bᴾ > P`; `m = 1`: `Φ_P(a, b) = aᴾ − bᴾ > P`; `m = 2`: `(a + b) · Φ_{2P}(a, b) = aᴾ + bᴾ`, and `Φ_{2P}(a, b) > P` except at `(2, 1, 3)`, which is `n = 6`; `m ≥ 3`: `Φₙ(a, b) · Φₘ(a, b) = Φₘ(aᴾ, bᴾ)`, `Φₘ(a, b) < (a + b)^φ(m)`, `Φₘ(aᴾ, bᴾ) > (aᴾ − bᴾ)^φ(m) ≥ P · (a + b)^φ(m)`, where `P ≥ 3` and `φ(m) ≥ 2`. The case `m ≥ 3` needs, for every `b ≥ 1`, `((b + 1)ᴾ − bᴾ)² ≥ P · (2b + 1)²` and `(b + 1)ᴾ − bᴾ ≥ 2b + 1`; the reviewer found both hold for `b ≤ 1000` and odd primes `P < 50`. |
| 9 | The order translation | For a prime `p`, `b ≤ a`, `¬ (p ∣ a ∧ p ∣ b)` and `0 < n`: `p` is a primitive divisor of `aⁿ − bⁿ` exactly when `orderOf ((a : ZMod p) / b) = n` (Lean's `0⁻¹ = 0`, so `b ≡ 0` gives `orderOf 0 = 0`). Primes `p < 30`, `a, b ≤ 35`, `n < 20`: 120,137 cells, 0 failures. Each hypothesis dropped, one witness `(p, a, b, n)`: `¬ (p ∣ a ∧ p ∣ b)`, `(3, 6, 3, 1)`; `b ≤ a`, `(5, 1, 3, 1)`; `0 < n`, `(2, 1, 1, 0)`. The stronger `¬ p ∣ b` also gives 0 failures (104,044 cells). In Lean, `/` on `ZMod p` comes only from its `Field` instance, which needs `[Fact p.Prime]` (the reviewer: `Algebra/Field/ZMod.lean:17` and `:30`; `ZMod n` has `Inv` but no `Div`). |
| 10 | The rank of apparition at `(a + b, ab)` | **(A)** In a field, for `a ≠ b`: `lucasApparition (a + b) (a * b) = orderOf (a / b)`. Over `ZMod p`, `p < 60`, all 16,316 cells with `a ≠ b`: 0 failures, `b = 0` included (both sides `0`); with `a = b` all 440 cells fail (`U n = n * a ^ (n - 1)` has rank `p`, or `2` at `a = 0`, against `orderOf 1 = 1` or `orderOf 0 = 0`). At `(a, b) = (2, 1)` it is `lucasApparition_three_two_eq_orderOf` without that theorem's `p ≠ 2`: at `p = 2` both sides are `0`. **(B)** For a prime `p`, `0 < n` and `¬ p ∣ a - b` (over `ℕ`): `p` is a primitive divisor of `aⁿ − bⁿ` exactly when `lucasApparition ((a + b : ℕ) : ZMod p) ((a * b : ℕ) : ZMod p) = n`, with no coprimality and no `b < a` (at `a ≤ b`, `a - b = 0` and the hypothesis fails). Primes `p < 32`, `a, b ≤ 40`, `n ≤ 24`: 189,936 cells, 0 failures. Dropped: `0 < n`, 5,860 of 7,914 cells fail, e.g. `(5, 3, 2, 0)`; `¬ p ∣ a - b`, 18,454 of 253,848, e.g. `(3, 4, 1, 3)` (rank `3`, while `3 ∣ 4 − 1`). **(C)** For coprime `0 < b < a` and every `n`: some prime has rank of apparition `n` in `U(a + b, ab)` exactly unless `n = 1` or `(a, b, n) = (2, 1, 6)`. `a ≤ 60`, `n ≤ 40`: 45,141 cells, 0 failures. Its junk cells differ from row 7's: `n = 0` holds, through the primes dividing `ab` (their rank is `sInf ∅ = 0`); `n = 1` never (`U 1 = 1`); `n = 2` always, through any prime factor of `a + b` — when `a + b` is a power of `2` that prime is `2`, which divides `a − b` and is not a primitive divisor. The reviewer found a weaker form: `U(a + b, ab)` is symmetric in `a` and `b`, and (C) holds for coprime positive `a ≠ b` with the exception written `n = 6 ∧ ((a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2))` (30,318 cells, coprime positive `a ≠ b ≤ 40`, `n ≤ 30`, 0 failures); coprimality is needed, already at `n = 0` (71 of 9,021 non-coprime cells with `0 < b < a ≤ 40`, `n ≤ 30` fail, first `(4, 2, 0)`: `2` is the only prime of `ab` and it divides `a + b`, so its rank is `2`). |
| 11 | The Catalan numbers and linear recurrences | For every order `d ≤ 15` the matrix `[catalan (n + i)]` (`n < 60 − d`, `i ≤ d`) has rank `d + 1` over `ℚ` and over `ZMod p` for every prime `p < 30`, so no recurrence `u (n + d) = ∑_{i < d} cᵢ u (n + i)` of order `d ≤ 15` holds; by brute force none of order `≤ 6` over `ZMod 4`, `≤ 5` over `ZMod 6`, `≤ 4` over `ZMod 8` and `ZMod 9`. Over the trivial ring every recurrence holds, so `Nontrivial` is needed. `AlgebraicGeneratingFunction`'s docstring cites `catalanSeries_sq_mul_X_add_one` at `RingTheory/PowerSeries/Catalan.lean:48`; at v4.34.0 it is line 47 (the reviewer found six more stale line citations there, J3 Scope). |
| 12 | `V_p` in characteristic `p` | As polynomials in `P`, `Q` over `ℤ`: `V_p − P ^ p` has every coefficient divisible by `p` for each prime `p < 60`; for `2 ≤ n ≤ 39` the same holds exactly at the primes; in characteristic `0`, `V_2 − P ^ 2 = −2Q`. Mathlib has the case `Q = 1` only: `dickson_one_one_charP` (`RingTheory/Polynomial/Dickson.lean:269`) and `dickson_one_one_zmod_p` (`:202`). |
| 13 | Carmichael's theorem, measured and not proposed | `F_n` has a primitive prime divisor exactly for `n ∉ {1, 2, 6, 12}`: checked from the definition for `n ≤ 400`. Its analytic core is the Fibonacci cyclotomic numbers `c_n = ∏_{d ∣ n} F_d ^ μ(n / d)`: `c_n ≥ 0.618 · φ ^ φ(n)` for `3 ≤ n ≤ 300`, while the triangle inequality, which bounds each factor `α − ζβ` below by `φ − φ⁻¹ = 1` in absolute value, gives only `c_n ≥ 1`. Round 22's key lemma does not carry over: `c_6 = 4` and `c_12 = 6` exceed `P(n) = 3`, yet `F_6` and `F_12` have no primitive divisor, because `2` divides both `n` and `c_n` (the rank of apparition of `2` is `3 = 2 + 1`). Mathlib has no identity for `Φₙ(−X)` and no reversal lemma (row 14). It needs cyclotomic values at a pair of conjugate quadratic irrationals and its own treatment of `p = 2` and `p = 5`. |
| 14 | Mathlib v4.34.0 searches (commands below) | `zsigmondy` 0; `primitive divisor` 0; `lucasU`, Lucas sequence or apparition 1 (a docstring line in `NumberTheory/EllipticDivisibilitySequence.lean`); `homogenize` in one file, `Algebra/Polynomial/Homogenize.lean` (`homogenize_mul` `:181`, `homogenize_finsetProd` `:187`, `eval_homogenize` `:227`), which never mentions cyclotomic polynomials; `orderOf` of a quotient 0; a cyclotomic theorem about negation or reversal 3, all positivity statements (`cyclotomic_neg_one_pos`, private, `cyclotomic_pos_and_nonneg`, `cyclotomic_nonneg`); Catalan with a recurrence 0; C-finite and its synonyms 0; `LinearRecurrence` with `PowerSeries` 0; `dickson` with `CharP` or `ZMod` 4 lines, all at `a = 1`; `wolstenholme` 0. Present: `emultiplicity_geom_sum₂_eq_one` (`NumberTheory/Multiplicity.lean:154`, already two-variable), `Int.emultiplicity_pow_sub_pow` (`:190`), `catalanSeries_sq_mul_X_add_one` (`RingTheory/PowerSeries/Catalan.lean:47`), `IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul` (`RingTheory/Polynomial/Cyclotomic/Basic.lean:629`), `sub_one_pow_totient_lt_cyclotomic_eval` (`Cyclotomic/Eval.lean:171`), `cyclotomic_eval_lt_add_one_pow_totient` (`:223`), `cyclotomic_expand_eq_cyclotomic` (`Cyclotomic/Expand.lean:87`) and `cyclotomic_expand_eq_cyclotomic_mul` (`:38`). |
| 15 | `docs/1000.yaml` at v4.34.0 | Of 1199 entries, 955 carry no `decl`, `decls` or `url`, as in order G-7. Confirmed by search in the file, each with no `decl`, `decls` or `url`: Q8074796 Zsigmondy's theorem (`# TODO: Find the code`, Mantas Bakšys, 2022), Q3889376 Carmichael's theorem, Q230848 Lamé's theorem, Q1059151 "FWL theorem", Q599876 Cochran's theorem, Q608294 max flow min cut, Q928813 Menger's theorem, Q579515 Rao–Blackwell, Q428134 Gauss–Markov. New in this cross-match: Q1724049 Wolstenholme's theorem, title only, and `wolstenholme` 0 in Mathlib; `C(2p − 1, p − 1) ≡ 1 (mod p³)` holds for the primes `5 ≤ p < 400` and for no composite `n < 2000`. If J2's item 3 lands, the library proves Q8074796's statement in full; listing it needs a public URL, and is Dustin's decision. |
| 16 | Order G-7's run, from its page and evidence (UTC) | Session from 14:39:36; J1 and the plan 14:43–15:38 (four readers, round 23; three critics with 27 findings; a delta check with 10); Dustin approved the plan and step V in one message at 15:39:08; J2's steps 16:04–17:10, J3 17:10–17:23, the Close 17:24–17:42. Eleven review workflows, 305–780 s each (`g7/reviews/times.txt`); of the eight post-proof and records reviews, seven returned FIX, most for docstring or records text, and one (step 4) LAND. The local guard refused two whole Bash calls because they contained `python3 -`, Python reading its program from stdin (15:56:02 and 17:24:19). J3's first build of the landed file had 4 `flexible` warnings (round 24). The Close check: 63 held, 9 failed, 5 pending by design (round 24's addendum). |
| 17 | `lake env lean` and the lakefile's options | `lake env lean` applies none of `lakefile.toml`'s `[leanOptions]`. A scratch file with two non-terminal `simp at h` followed by `rw [h]` (`/tmp/claude-ai-g8/FlexTest.lean`, sha256 `bfed1762…12d9e`): plain `lake env lean`, rc 0 and 0 warnings; with `-Dweak.linter.mathlibStandardSet=true`, 2 `flexible` warnings; with all four options as `-D` flags, rc 0 and the same 2. The header linter did not fire on the file, which lies outside the package. |
| 18 | Order G-7's J2 Done-means 3, re-checked | From the repository root, `lake env lean ~/work/_bump-evidence/g7/j2/step4/DefeqCheck.lean`: rc 0, no output — the landed `hasDerivAt_softmax` and `hasDerivAt_softmax_categoricalCov` prove both statements written with the instance elaborated before step 4, `PolynormableSpace.continuousSMul ℝ ℝ`. Its fire test, `DefeqCheckFire.lean` in the same directory: rc 1, one type-mismatch error. `~/work/_bump-evidence/TypeDump.lean` (sha256 `83791d61…4b363`) prints types with their proof terms, and `g5_typediff.py` (`9e50d9ef…fa51`) compares them by sha256, so it cannot tell such a record from a changed statement. |
| 19 | Import probes (scratch files in `/tmp/claude-ai-g8/`) | With only `AlgebraicGeneratingFunction` and `RecurrenceGeneratingFunction` imported: `Ideal.exists_maximal`, `Ideal.Quotient.field`, `PowerSeries.catalanSeries_sq_mul_X_add_one`, `PowerSeries.map` and `Polynomial.coe_injective` resolve. With only `LucasApparition` imported: `add_pow_char_of_commute`, `Polynomial.map_dickson`, `lucasV_eq_dickson_one_eval`, `lucasU_of_roots`, `orderOf_eq_zero_iff'` and a `CharP (Polynomial R) p` instance resolve. Both rc 0. With only `Zsigmondy` imported, `emultiplicity_geom_sum₂_eq_one` and `lucasApparition` resolve, and `Polynomial.homogenize`, `eval_homogenize` and `homogenize_finsetProd` are unknown (rc 1): `Zsigmondy` does not reach `Mathlib.Algebra.Polynomial.Homogenize`. |

Row 3, the four orders. "Wall clock" runs from the order's filing commit to its closing commit,
UTC; "commits" is `git rev-list --count <filing commit>^..<closing commit>`. The first three rows
are order G-7 §0's.

| Order | Wall clock | Commits | Modules | Lines under `ClassicalLean/` | Filtered list | Close check | Dustin's decisions |
|---|---|---|---|---|---|---|---|
| 0923 | 09-23 14:09–17:12 (includes a STOP) | 18 | 41 → 44 | 12,446 → 13,069 | → 725 (round 17) | every checkable item met, after findings | the STOP (delegated to claude-ai), the push |
| G-5 | 09-23 18:54–20:34 | 12 | 44 → 45 | → 13,619 | 725 → 746 | every checkable item met, after an evidence-log finding | the plan, the push |
| G-6 | 09-24 00:49–02:04 (J1 from 00:12) | 14 | 45 → 48 | → 14,757 | 746 → 791 | 41 held, 2 failed (records), both remedied | the plan with the credit, the push |
| G-7 | 09-24 15:40–17:42 (J1 from 14:43) | 11 | 48 → 48 | 14,757 → 15,302 | 791 → 816 | 63 held, 9 failed (one type-dump item, eight records and process), 5 pending by design | the plan with step V, the push |

Row 14's searches, from the Mathlib clone's root:

```
grep -rniE 'zsigmondy' Mathlib --include=*.lean | wc -l                                         # 0
grep -rniE 'primitive.?(prime.?)?divisor' Mathlib --include=*.lean | wc -l                      # 0
grep -rniE 'lucasU|lucas.?sequence|apparition' Mathlib --include=*.lean | wc -l                 # 1
grep -rlE 'homogenize' Mathlib/Algebra Mathlib/RingTheory Mathlib/NumberTheory --include=*.lean | wc -l   # 1
grep -rniE 'cyclotomic' Mathlib/Algebra/Polynomial/Homogenize.lean | wc -l                      # 0
grep -rnE 'orderOf \((\(?[a-z]+ : ZMod [a-z]+\)?|[a-z]+) / ' Mathlib --include=*.lean | wc -l   # 0
grep -rnE 'theorem [a-zA-Z_.]*cyclotomic[a-zA-Z_.]*' Mathlib/RingTheory/Polynomial/Cyclotomic/*.lean | grep -ciE 'neg|reverse|reflect|mirror|palin'   # 3
grep -rniE 'catalan' Mathlib --include=*.lean | grep -ciE 'LinearRecurrence|IsSolution|recurrence|rational'   # 0
grep -rniE '\bc-finite\b|holonomic|\bd-finite\b|p-recursive|constant-recursive' Mathlib --include=*.lean | wc -l   # 0
grep -rnE 'LinearRecurrence' Mathlib --include=*.lean | grep -ciE 'PowerSeries|power series'   # 0
grep -rnE 'dickson' Mathlib --include=*.lean | grep -cE 'CharP|ZMod'                           # 4
grep -rniE 'wolstenholme' Mathlib --include=*.lean | wc -l                                      # 0
```

**Predict J1 from `HANDOFF.md` §1 and §6, `records/orders/INDEX.md`, `records/CLAIMS.md` and
`push.log`, not from this table** — except J1 items 6, 7, 9, 10 and 11, which re-run claude-ai's
measurements and predict from rows 4–15 and 17–19. §6 lags the last push by design, so `push.log`
predicts item 4.

---

## 1. Rules for this session

- **`HANDOFF.md` §6 holds**: rules 1–19 and the standing answers, with §0, §3, §4 and §5, and
  README Rules 1 to 4. They are not repeated here.
- **Dustin does not read code or files.** Everything he needs goes in your chat reply. When he must
  act, give the exact command, the box, and the output you expect.
- **Predict, then measure.** Write the expected value, or "no prediction", before any command that
  prints a count, a hash or an rc. Report predicted beside actual.
- **Run every command from `~/work/classical-lean`**, or give `git -C` and absolute paths.
- **Six rules learned in order G-7's run** (§0 rows 16–18, round 24 and its addendum), numbered as
  J2 step 4 will file them in `HANDOFF.md` §6. In this order "rule N" means `HANDOFF.md` §6's rule
  N, 1–25; `records/README.md`'s rules are written "README Rule N".
  20. **Scratch proofs are elaborated with the lakefile's options.** `lake env lean` applies none of
     `[leanOptions]`, so a proof checked only that way can land with linter warnings (round 24: J3's
     first build, 4 `flexible` warnings against a prediction of 0). Elaborate scratch files with
     the four options as flags, which surfaces them (§0 row 17):
     `lake env lean -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3 <file>`.
     Rule 11 still holds: linter results count only from `lake build`.
  21. **A statement drafted in a plan is drafted.** A job's recorded searches and junk cells come
     before any of its statements is drafted, the plan's drafts included; J1 runs them, read-only
     (round 24's addendum, item 2: J3's statements were drafted in the plan at 15:04:51Z and its
     searches recorded at 15:47:39Z).
  22. **Every quote in a fragment is checked by a script against its saved source before the
     fragment is committed**, with a negative control, and every omission inside a quote is marked
     `[...]` (round 24's addendum, items 3 and 4; `g7/close/quotecheck.py` is the precedent).
  23. **Evidence commands run through one helper** that takes the prediction as an argument, refuses
     to run without one, and logs the command with its own `$?`; a commit runs only when its gates
     exited 0 in the same run (round 24's addendum, items 7, 8 and 9: 12 of 119 `cmd:` lines had no
     rc, `0e44376`'s message was composed with its gates, and some runs had no prediction). It
     binds from J1 item 0, which builds the helper.
  24. **Every reader, research and review brief quotes the rules it will be checked against**, at
     least rules 16–25 (round 24's addendum, item 6: the readers' notes named no source for the
     routes they proposed).
  25. **Type-dump Done-means are judged up to proof irrelevance.** A record whose raw form differs
     only inside proof terms is `PROOF-ONLY`: listed, explained, and not counted as changed (round
     24's addendum, item 1; §2's ruling). J1 step 4 builds the tool; until it passes its controls,
     such a record is settled by a Lean file with a fire test, as round 23 did (`DefeqCheck.lean`).
     It amends rule 14: once its controls pass, the new pair, which prints today's fields too, is
     rule 14's evidence; J2 step 4 files the amendment, dated.
- **Environment facts, measured in order G-6's and G-7's runs:** write every commit message to a
  file and commit with `git commit -F <file>`; write scripts to files in the evidence directory and
  run them as `python3 <file>`. The local guard refuses inline `python3 -c`, chained in-place edits,
  and any Bash call that contains `python3 -` reading from stdin (§0 row 16).
- **Steps and commits.** Land a step as its own commit when it was proved as a step. If a module is
  proved whole before its first landing, land it in one commit and record its step structure in
  the fragment (rule 18); do not cut step commits from a finished file.
- **Gate 6.** J2 and J3 create no module file, unless J2's size clause applies. If a job creates
  one, the rules of order G-6 §1 apply to it: until a round fragment names the new file, write its
  path or bare filename into none of the files gate 6 searches (`PROVENANCE.md`,
  `records/rounds/*.md`, `records/orders/*.md`, `INDEX.md` included); show `check_records.py` FAIL
  on it with its import line in place; then commit it together with the fragment that names it.
- **Git, reviews and builds** as in order G-5 §1:
  - commit locally, never push to GitHub or add a remote, park and never delete;
  - reach DSMain only with `GIT_SSH_COMMAND='ssh -o BatchMode=yes -o ConnectTimeout=15'`; if DSMain
    is unreachable, record "unreachable" and carry on; never touch the VPN, routes or ssh
    configuration;
  - a fresh cold reviewer before and after proving; builds one at a time; subagents never run `lake`.

## 2. Standing answers — do not stop to ask these

- **Everything in `HANDOFF.md` §6's standing answers** still holds.
- **The push record.** J1 compares `HANDOFF.md` §6 with `push.log` and the `dsmain/master` reflog.
  J2 step 4 adds the dated line for `cca6f8a..87683e3`, taken from `push.log` and the reflog.
- **Order G-7's J2 Done-means 3 is ruled.** claude-ai, as order G-7's author, confirms its
  executor's ruling: the two records `hasDerivAt_softmax` and `hasDerivAt_softmax_categoricalCov`
  changed only inside a `Prop`-valued instance argument, and their statements did not change —
  re-checked this cycle (§0 row 18). Dustin's veto stays open. J2 step 4 files it as a standing
  answer, with rule 25.
- **Where the new theorems live**, pre-answered; a different home is allowed if the plan says why
  and the import closure is recorded:
  - J2's definition, the order translation, Zsigmondy's theorem and items 4 (B) and (C) in
    `NumberTheory/Zsigmondy`, which reaches `LucasApparition` already, through `PrimitiveDivisor`.
    It does not reach `Polynomial.homogenize` (§0 row 19): if the route uses it, `Zsigmondy` gains
    `import Mathlib.Algebra.Polynomial.Homogenize`, its one new import, with the closure recorded;
    the homogenized value can also be written directly, with no import;
  - J2's item 4 (A) and J3's item 2 in `NumberTheory/LucasApparition`, which needs no new import
    (§0 row 19);
  - J3's item 1 in `Combinatorics/AlgebraicGeneratingFunction`, which gains
    `import ClassicalLean.Combinatorics.RecurrenceGeneratingFunction` and no other import (§0 row 19).
  None of these closes a cycle: at `87683e3` `RecurrenceGeneratingFunction` imports only Mathlib.
  J1 checks it (item 7).
- **Names are suggestions** for the statement reviews; Mathlib's naming conventions decide.
- **Anything that needs Dustin:** ask in one line, recommended answer first, and keep working on
  whatever does not depend on it. Pushing, publishing, listing anything in Mathlib's
  `docs/1000.yaml`, offering anything to Mathlib and retiring modules are his.

---

## J1 — open and re-measure (read-only)

**Goal.** Know that order G-7 is closed and that the tree is what its records say, and record the
searches and junk cells of J2 and J3 (rule 21), before touching the tree.

**Scope.** Read-only in the repository. Write only under `~/work/_bump-evidence/`: `g8/`, and after
approval `g8-before/` and the new type-dump pair beside `TypeDump.lean`. Run what plan mode allows.
List the rest with predictions, marked "deferred".

**Measure, predicting each value first:**

0. **The evidence helper first** (rule 23). Write one helper under `g8/` that takes a prediction
   ("no prediction" allowed, empty refused), a label and the command; writes the command, the
   prediction, the output file's path and the command's own `$?` to `g8/evidence.log`; and refuses to
   run, logging nothing, without a prediction. Fail-test it, predictions first: no prediction,
   refused; `false`, logged rc 1; `true`, logged rc 0. Run every later command through it; the gate
   runner and the commit step call it, and a commit runs only when all six gates exited 0 in the
   same run.
1. `records/orders/INDEX.md` row `G-7`: its state, and what landed. `CLAIMS.md`: no open row.
2. `lean-toolchain` and `lakefile.toml` `rev`: expect v4.34.0.
3. `git -C ~/work/classical-lean status --short`: expect nothing.
4. `git -C ~/work/classical-lean rev-parse master dsmain/master`, and
   `GIT_SSH_COMMAND='ssh -o BatchMode=yes -o ConnectTimeout=15' git -C ~/work/classical-lean ls-remote dsmain master`:
   predict from `push.log`'s last push line, or record "unreachable". Compare §6's push list with
   `push.log` and the reflog, and name every push §6 lacks.
5. The six commands in `HANDOFF.md` §1, copied from it. Predict from its snapshot.
6. **Appendix A.** Write its four files into `~/work/_bump-evidence/g8/claude-ai/`, check each
   sha256 against the appendix, and run them as their headers say. Predict from §0 rows 4–6:
   1461 constants, 48 modules, 4 islands by name, `LucasApparition` with `usedBy= 0`;
   `DupCheck: 5 TWIN line(s), 0 SWAP line(s)`; `pairs.py`'s first line
   `modules=48 edges=76 rare_df<=3 pairs_without_edge_sharing_rare=84`.
7. **The import checks of §2.** List `RecurrenceGeneratingFunction`'s transitive `ClassicalLean`
   imports and confirm `AlgebraicGeneratingFunction` is not among them. Confirm that `Zsigmondy`
   reaches `LucasApparition`, that `LucasApparition` imports `Mathlib.LinearAlgebra.Matrix.CharP`,
   and whether `Zsigmondy` reaches `Mathlib.Algebra.Polynomial.Homogenize` (§0 row 19: it does not).
8. The number of files under `ClassicalLean/` and `ClassicalLean.lean` whose line 4 is exactly
   `Authors: Dustin [surname], Claude (Anthropic)`: expect 49.
9. **Rule 20's flags.** Elaborate a scratch file outside the repository with two non-terminal
   `simp at h`, each followed by `rw [h]`, once with plain `lake env lean` and once with the four
   options as flags. Predict from §0 row 17: 0 warnings, then 2 `flexible` warnings.
10. **The evidence tools.** sha256 of `~/work/_bump-evidence/TypeDump.lean` and
    `~/work/_bump-evidence/g5_typediff.py`; predict from §0 row 18.
11. **J2's and J3's searches and junk cells (rule 21)**, written under `g8/` before the plan drafts
    any statement:
    - re-run §0 row 14's commands over `.lake/packages/mathlib/Mathlib`, and add shape searches:
      for J2 at least `homogenize` with `eval`, `cyclotomic_expand_eq_cyclotomic`,
      `sub_one_pow_totient_lt_cyclotomic_eval`, `pow_sub_pow_eq_prod_sub_mul` and
      `orderOf_eq_zero_iff`; for J3 at least `catalanSeries`, `Ideal.exists_maximal`,
      `Ideal.Quotient` with `Field`, `add_pow_char_of_commute`, `map_dickson` and a `CharP`
      instance on `Polynomial`. Record every command and count.
    - read every Mathlib and library definition the statements use, and the theorems their routes
      rest on (rule 2): `lucasApparition`, `lucasU_of_roots`, `IsPrimitiveDivisor`, `orderOf`, the
      `Inv` and `Field` instances of `ZMod` (`0⁻¹ = 0`; `Field` needs `Fact p.Prime`),
      `Polynomial.homogenize`, `LinearRecurrence.IsSolution`, `recDenom`, `catalan`,
      `catalanSeries`, `CharP`, `lucasV`, `Polynomial.dickson`.
    - junk cells, random plus constructed (rule 3), each script predicted first: for J2 the cells of
      §0 rows 7, 9 and 10 (`n ∈ {0, 1, 2, 6}`, `a + b` a power of `2`, `b = 0`, `a = b`, `a < b`,
      `p ∣ a − b`, `p ∣ a` and `p ∣ b` together); for J3 `E.order = 0`, the trivial ring, `ZMod 4`,
      `p = 2`, a composite modulus, characteristic `0`.

**If order G-7 is not closed, STOP and report.**

**Done-means.** A predicted-beside-actual table in the chat, with every miss explained. Then one plan
for J2 and J3, with their statements drafted after item 11, and wait for approval. The plan states
§2's ruling, and ends with Dustin's decision in one line, recommended answer first:
- "Recommended: yes — approve this plan."

**After approval, in this order:**

1. **Run the deferred commands.** STOP before J2 on any miss you cannot explain.
2. **File the order:**
   `mv -n ~/Cowork/lean-orders/20260924T182500Z__claude-ai__order-g8-zsigmondy-catalan.md ~/work/classical-lean/records/orders/ && test ! -e ~/Cowork/lean-orders/20260924T182500Z__claude-ai__order-g8-zsigmondy-catalan.md && test -f ~/work/classical-lean/records/orders/20260924T182500Z__claude-ai__order-g8-zsigmondy-catalan.md`.
3. **Add the records rows, then commit exactly three paths:** the filed order,
   `records/orders/INDEX.md` and `records/CLAIMS.md`.
   - `INDEX.md`: a row for `G-8`, naming no new file.
   - `CLAIMS.md`: a row naming the modules J2 and J3 edit (`NumberTheory/Zsigmondy`,
     `NumberTheory/LucasApparition`, `Combinatorics/AlgebraicGeneratingFunction`; `ClassicalLean.lean`
     only if J2's size clause creates a module) and the records paths: `HANDOFF.md`, `ROADMAP.md`,
     the round 25 and 26 fragments, `CLAIMS.md` and `INDEX.md`.
4. **A type dump up to proof irrelevance** (rule 25), outside the repository, fail-tested with its
   predictions written first. Beside today's fields, print each type, and each definition's value,
   with every proof term replaced by one placeholder; and a diff that reports a record whose raw
   forms differ but whose proof-erased forms agree as `PROOF-ONLY`, counted apart from `changed=`.
   Keep `TypeDump.lean` and `g5_typediff.py` unchanged; write the new pair beside them under new
   names. Controls: (a) round 23's two statements, with the old instance and with
   today's (`~/work/_bump-evidence/g7/j2/step4/DefeqCheck.lean` writes the old one), compared as
   `Prop`s: `PROOF-ONLY`; (b) the same with `-` changed to `+`
   (`~/work/_bump-evidence/g7/j2/step4/DefeqCheckFire.lean`): `CHANGED`; (c) on the clean tree the
   new dump's `thm` count equals AxiomGate's, and no record is dropped or truncated. If a control
   fails, keep the old tools, say so in round 25's fragment, and apply rule 25's fallback.
5. **Take the "before" evidence on a clean tree** into `~/work/_bump-evidence/g8-before/`: the type
   dump (the new one if its controls passed), the raw and filtered name lists, and item 6's four
   outputs. J2 and J3 diff against these.

**Undo:** nothing to undo in the repository; the evidence tools live outside it.

---

## J2 — Zsigmondy's theorem for aⁿ − bⁿ, and its rank of apparition

**Goal.** The classical two-variable form of Zsigmondy's theorem, which completes `docs/1000.yaml`'s
Q8074796 (the library proves `b = 1`, round 22), and its reading in `LucasApparition`'s terms, which
gives `LucasApparition` its first user (§0 row 4) and joins the pair `LucasApparition ~ Zsigmondy`
(§0 row 6).

**Scope.**
- `NumberTheory/Zsigmondy` (whose docstring credits the two-variable prior art) and
  `NumberTheory/LucasApparition` (item 4 (A), and a dated line in its "What is not here", which
  says "The sharp existence criterion is still not here", naming where item 4 (C) proves it for
  integer roots). Existing modules gain declarations; no existing statement changes, and no
  existing proof changes unless a step says so. If `Zsigmondy` would pass about 1,300 lines, the
  new material may go in a new module that imports it: the plan names it, and §1's gate-6 rules
  apply, with a `CLAIMS.md` entry, the header with the current Authors line, one import line in
  `ClassicalLean.lean`, and an `import_closure.py` run with its positive control.
- `HANDOFF.md` §3 and §6, `ROADMAP.md` §1 and §2, records. Round 25's fragment opens with the first
  J2 commit.

**The statements** (content fixed by §0; the names are suggestions):

1. **The definition.** `IsPrimitiveDivisor₂ p a b n := p.Prime ∧ p ∣ a ^ n - b ^ n ∧ ∀ m : ℕ, 0 < m →
   m < n → ¬ p ∣ a ^ m - b ^ m`, over `ℕ`: `IsPrimitiveDivisor` with `b ^ n` for `1`, and like it
   the classical definition verbatim (its docstring says why). With it,
   `IsPrimitiveDivisor₂ p a 1 n ↔ IsPrimitiveDivisor p a n`.
2. **The order translation** (§0 row 9): for `p` with `[Fact p.Prime]` (`/` on `ZMod p` needs it),
   `b ≤ a`, `¬ (p ∣ a ∧ p ∣ b)` and `0 < n`:
   `IsPrimitiveDivisor₂ p a b n ↔ orderOf ((a : ZMod p) / b) = n`.
3. **Zsigmondy's theorem** (§0 row 7): for `a.Coprime b`, `0 < b` and `b < a`, and every `n`:
   `(∃ p, IsPrimitiveDivisor₂ p a b n) ↔ ¬ ((n = 1 ∧ a = b + 1) ∨ (n = 2 ∧ ∃ k, a + b = 2 ^ k) ∨
   (n = 6 ∧ a = 2 ∧ b = 1))`. Recover round 22's `exists_isPrimitiveDivisor_iff` at `b = 1` by an
   `example`.
4. **In `LucasApparition`'s terms** (§0 row 10):
   - (A) for a field `K` and `a b : K` with `a ≠ b`: `lucasApparition (a + b) (a * b) = orderOf (a / b)`.
     Recover `lucasApparition_three_two_eq_orderOf` from it by an `example` at `(2, 1)` over
     `ZMod p` with no `p ≠ 2` (its `Field` instance from `hp` through `Fact`), and add a dated line
     to that theorem's docstring saying so.
   - (B) for a prime `p`, `0 < n` and `¬ p ∣ a - b`:
     `IsPrimitiveDivisor₂ p a b n ↔ lucasApparition ((a + b : ℕ) : ZMod p) ((a * b : ℕ) : ZMod p) = n`.
   - (C) for `a.Coprime b`, `0 < b` and `b < a`, and every `n`:
     `(∃ p, p.Prime ∧ lucasApparition ((a + b : ℕ) : ZMod p) ((a * b : ℕ) : ZMod p) = n) ↔
     n ≠ 1 ∧ ¬ (n = 6 ∧ a = 2 ∧ b = 1)`.
   State each with the weakest hypotheses the proof allows; §0 records weaker forms that hold.

**Method.**

1. **Statement review before proving** (rule 16). The searches and junk cells are J1 item 11's
   (rule 21). Draft every J2 statement, elaborate them with `sorry` under rule 20's flags, and send
   the list to one cold statement review whose brief quotes rules 16–25 (rule 24). Its verdict is
   in before any J2 proof is written.
2. **The route** (§0 row 8). It is round 22's, which is the prior art's for the two-variable form
   (Bakšys's Lean 3 proof and mathlib4 #28895, both in `Zsigmondy`'s docstring): credit it there,
   and adapt no code (rule 19). The homogenized cyclotomic value `Φₙ(a, b)`, through Mathlib's
   `Polynomial.homogenize` (§0 row 14; `homogenize_finsetProd`, `eval_homogenize`; §2 on its
   import) or written directly; `aⁿ − bⁿ = ∏_{d ∣ n} Φ_d(a, b)`; the key lemma (a prime of
   `Φₙ(a, b)` not dividing `n` is primitive); the `P(n)` lemma; exactly-once for `n ≥ 3` (odd `p`
   through `emultiplicity_geom_sum₂_eq_one`, which is two-variable already; `p = 2` through `n` a
   power of `2` and `aᵈ + bᵈ ≡ 2 (mod 4)`); then
   `Φₙ(a, b) > P(n)`: for `a − b ≥ 2` through `sub_one_pow_totient_lt_cyclotomic_eval` at `a / b`,
   for `a = b + 1` through round 22's four cases with `(a, b)` for `(2, 1)`, using
   `cyclotomic_expand_eq_cyclotomic`, `cyclotomic_expand_eq_cyclotomic_mul` and
   `cyclotomic_eval_lt_add_one_pow_totient`. Another route is fine if the fragment names its source.
3. **Land** per statement group if you prove per group, in one commit if the material is proved
   whole first (§1). A post-proof review covers every new declaration, private helpers included
   (rule 13), before its commit; quotes from it are script-checked (rule 22).
4. **Records** (after steps 1–3 have landed; each line records only what landed).
   - `HANDOFF.md` §6: §1's rules 20–25, each with its date and source; the lead-in names four orders
     (0923: 1–7; G-5: 8–15; G-6: 16–19; G-7: 20–25). The dated push line of §2. Two standing
     answers: the environment facts of §1 (the `python3 -` refusal added), and §2's ruling with rule
     25.
   - `ROADMAP.md`: a dated paragraph in §2.5 (the two-variable form proved; Q8074796's statement in
     full); a dated line in §2.1 (the rank of apparition at `(a + b, ab)` is the order of `a / b`,
     and item 4 (C) is the existence criterion for integer roots); a dated line in §1.15 (the pair
     joined, and `pairs.py`).
   - `HANDOFF.md` §3: the tooling item, done or not as J1 step 4 went.
   - Complete round 25's fragment (README Rule 1).

**Done-means.**
1. The six gates pass on a clean tree, with 0 warnings and 0 vocabulary hits.
2. Every new theorem is within the kernel trio. The statement review and the post-proof review are
   saved (rule 17) and quoted in round 25's fragment, every quote script-checked (rule 22).
3. The type dump against J1's evidence shows only additions, judged up to proof irrelevance
   (rule 25): any `PROOF-ONLY` record is listed and explained.
4. Appendix A on the landed tree: `LucasApparition` used by at least one module if item 4 (B) or
   (C) landed (0 at `87683e3`); islands 4; `DupCheck: 5 TWIN line(s), 0 SWAP line(s)`.
5. The fragment carries the searches, the junk cells, the route with its sources, the per-module
   counts, and the import-closure result for any module that gained an import.
6. No `sorry` ships. A statement group that did not close stays out of the files and is described
   in `HANDOFF.md` §3. Items 1, 2, 4 (A) and 4 (B) do not depend on item 3; item 4 (C) does.
7. If item 4 (C) landed, `LucasApparition`'s "What is not here" carries the dated line of the
   scope.

**Undo:** yes — `git revert`, one commit at a time.

---

## J3 — the Catalan numbers satisfy no linear recurrence; V_p = P^p in characteristic p

**Goal.** Two small items, each measured in §0. Item 1 joins §0 row 6's first pair and takes
`AlgebraicGeneratingFunction` off the islands list (4 → 3). It is the mathematical counterpart of
that module's remark that a convolution "has no representation" as a `LinearRecurrence`, which the
module states as a fact about types. Item 2 is `HANDOFF.md` §3's open item from round 24's
statement review, and extends Mathlib's `dickson_one_one_charP` from `Q = 1` to every `Q`.

1. **The Catalan numbers satisfy no linear recurrence** (§0 row 11): for a commutative ring `R` with
   `Nontrivial R` and every `E : LinearRecurrence R`, `¬ E.IsSolution (fun n => (catalan n : R))`.
   Route, derived by claude-ai for this order (rule 19): over a field `K` first. `recDenom E` is a
   power series; first show it is the coercion of the polynomial
   `Q = 1 - ∑ j, C (E.coeffs j.rev) * X ^ ((j : ℕ) + 1)`, whose constant coefficient is `1`. Then
   `recDenom_mul_mk_eq_coe_trunc` gives `Q · C = P` with `P` a polynomial; Mathlib's
   `catalanSeries_sq_mul_X_add_one`, mapped to `K`, gives `C = 1 + X · C²`; so
   `Q · P = Q² + X · P²` in `K[X]`. If `P = 0` then `Q = 0`, which is false. If `deg P ≥ deg Q`,
   `X · P²` alone reaches degree `2 deg P + 1`; otherwise `Q²` alone reaches `2 deg Q`; either way a
   leading coefficient squares to `0` in a domain. For a general `R`, pass to `R ⧸ m` for a maximal
   ideal `m`. `Nontrivial` is needed (§0 row 11); if the passage to a field costs more than it is
   worth, state the theorem for a field or a domain and record why.
2. **`V_p = P ^ p` in characteristic `p`** (§0 row 12): for a commutative ring `R`, a prime `p` with
   `[CharP R p]` and `P Q : R`: `lucasV P Q p = P ^ p`; and, in Mathlib's shape, `dickson 1 a p = X ^ p`
   for every `a : R`. Route: round 24's Frobenius section, carried from `ZMod p` to `R` (for odd `p`,
   `2` is a unit of `R` and `2 ^ p = 2` there); `p = 2` directly, `V_2 = P ^ 2 - 2 * Q`; the
   polynomial form from the evaluation form in `R[X]`, through `lucasV_eq_dickson_one_eval` and
   `map_dickson`. Recover `lucasV_prime_eq` (round 24) by an `example`.

**Scope.** `Combinatorics/AlgebraicGeneratingFunction` (item 1, with §2's import, and one dated
line correcting the Mathlib line numbers its docstring cites, re-measured at v4.34.0: the
reviewer found `RingTheory/PowerSeries/Catalan.lean:48` now `:47`, cited twice;
`RingTheory/PowerSeries/Schroder.lean:95` now `:94`, cited twice; in the sentence citing `51-105`,
the range, "from 62" and "from 95" now 51–104, 61 and 94; and the line counts there and in
"replaces 55 lines with 15" to be re-measured) and `NumberTheory/LucasApparition` (item 2).
`ROADMAP.md` §1.15 (the islands after J3), §2.4 (item 1) and §2.1 (item 2); `HANDOFF.md` §3 (item 2
done). Records. Round 26's fragment. Every other module is read-only.

**Method.**
1. The searches and junk cells are J1 item 11's (rule 21).
2. **Statement review before proving** (rule 16), under rule 20's flags, with rule 24's brief.
3. Land per item; a post-proof review before each commit (rule 13).

**Done-means.**
1. Every landed commit passes the six gates with 0 warnings, and every theorem is within the kernel
   trio.
2. No `sorry` ships. An item that did not close stays out of the files and is described in
   `HANDOFF.md` §3.
3. Both reviews are saved and quoted in round 26's fragment (rules 17 and 22). The fragment carries
   the searches, the junk cells, the routes and their sources, the per-module counts, and, if item 1
   landed, the import-closure result for `AlgebraicGeneratingFunction`'s new import.
4. Appendix A on the landed tree: islands 3 (`Catalan`, `CompositumDiscriminant`, `Tolerance`) if
   item 1 landed, otherwise 4 with the reason in `HANDOFF.md` §3;
   `DupCheck: 5 TWIN line(s), 0 SWAP line(s)`. The type dump against J1's evidence shows only
   additions, judged up to proof irrelevance (rule 25).

**Undo:** yes — `git revert`.

---

## Close

1. **Refresh `HANDOFF.md`.**
   - §1: the snapshot from the six commands on a clean tree.
   - §3's "what next", re-ranked with this order's results. The list: Carmichael's theorem
     (Q3889376), with §0 row 13's measurement of what it needs; majorization (Mathlib's TODO); the
     FWL theorem, then Cochran (Q1059151, Q599876); Lamé's theorem (Q230848); Wolstenholme's theorem
     (Q1724049, new, §0 row 15); max-flow min-cut and Menger (Q608294, Q928813); Mathlib's wanted
     list; and, not ranked, the remaining islands and the other pairs of §0 row 6.
2. Close the `CLAIMS.md` row and update the `INDEX.md` rows.
3. **The Close check.** Fresh subagents check every Done-means against
   `git diff <this order's first commit>^..master`, with the rules they check in their brief
   (rule 24). Save their outputs first (rule 17), then record the verdict, quoted and
   script-checked (rule 22), as an addendum to round 26. If it runs before step 2, as order G-7's
   did, say so (rule 18).
4. **Ask Dustin, in one line:** "Recommended: yes — push classical-lean master to DSMain, a
   fast-forward from 87683e3 to <new>." Push only on yes:
   `GIT_SSH_COMMAND='ssh -o BatchMode=yes -o ConnectTimeout=15' git -C ~/work/classical-lean push dsmain master`,
   fast-forward only, never `--force`. Then log the push in `push.log`. The next order records it in
   §6.
5. **The final chat report:** predicted beside actual, what landed with commit hashes, what stopped
   and why, what comes next, and:
   - the net change in theorem constants on the filtered list;
   - Appendix A's numbers before and after (islands, `LucasApparition`'s users, `TWIN` and `SWAP`
     lines, `pairs.py`'s first line);
   - this order's row for §0's order table, in the same columns;
   - one line each on any decision made on Dustin's delegation, and on any overlap rule 18 recorded.

## Not in this order

- **G-4**: the number-theory track.
- **Publishing, listing in `docs/1000.yaml`, or offering anything to Mathlib**: Dustin's decisions.
  If J2's item 3 lands, the library proves Q8074796's statement in full; J3's `dickson` form is a
  candidate for Mathlib.
- **Retiring any module**: Dustin's decision. Three islands remain if J3's item 1 lands, recorded,
  not bridged.
- **Carmichael's theorem** (§0 row 13), **majorization, FWL and Cochran, Lamé, Wolstenholme,
  max-flow min-cut**: ranked at the Close.
- **The other pairs of §0 row 6**, `S3Quaternion ~ SU2SO3` among them: recorded, not bridged.
- **Any change to `tools/`** or to the banned-vocabulary list.
- **Anything in the lane on DSMain**, and the Claude Code configuration on helios.

---

## Appendix A — claude-ai's four evidence scripts

Write each into `~/work/_bump-evidence/g8/claude-ai/` byte for byte (the text between the fences,
ending with one newline), and check its sha256 before running it. The first three are order G-7's
Appendix A, unchanged, their docstrings included; `pairs.py` is new.

```
a120cee455d000e78a7a60ad6cff1b93d9c1a6e15abaccf13e83a6dd95e8b3e0  DeclGraph.lean
9687c7ff6a81312c2aa9ccabbf380514ceffa479d63ade5afba2584f188c53e9  DupCheck.lean
f9aff2c78593cff456ab3e0970d3747cbaac32763aa53a03ed879c6395ec0404  islands.py
f734b8108ea1cf2c3e53c09877364891c24d71dcce74f3e3440ac4608222018a  pairs.py
```

Run, from `~/work/classical-lean`:

```
lake env lean ~/work/_bump-evidence/g8/claude-ai/DeclGraph.lean > ~/work/_bump-evidence/g8/claude-ai/declgraph.jsonl
python3 ~/work/_bump-evidence/g8/claude-ai/islands.py ~/work/_bump-evidence/g8/claude-ai/declgraph.jsonl
python3 ~/work/_bump-evidence/g8/claude-ai/pairs.py ~/work/_bump-evidence/g8/claude-ai/declgraph.jsonl
lake env lean ~/work/_bump-evidence/g8/claude-ai/DupCheck.lean
```

`DeclGraph.lean`:

```lean
import ClassicalLean
import ImportGraph.Lean.Environment

/-! Evidence script for order G-7 (claude-ai, 2026-09-24), outside the repository. Read-only.
One JSON line per `ClassicalLean` constant: its module, kind, whether private, the library
constants its type (`tyLib`) and value (`valLib`) name, and every constant its type names
(`tyAll`). Run: `lake env lean <this file> > declgraph.jsonl` from the repository root. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if n.hasMacroScopes then continue
    let u := privateToUserName n
    unless (`ClassicalLean).isPrefixOf u do continue
    let kind := match ci with
      | .thmInfo _ => "thm" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
      | .inductInfo _ => "induct" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
      | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot"
    let m := (env.getModuleFor? n).getD .anonymous
    let lib (a : Array Name) : Array Json :=
      (a.filter fun c => (`ClassicalLean).isPrefixOf (privateToUserName c)).map
        fun c => Json.str (privateToUserName c).toString
    let tyAll := ci.type.getUsedConstants
    let valAll : Array Name := match ci.value? (allowOpaque := true) with
      | some v => v.getUsedConstants | none => #[]
    let j := Json.mkObj [("raw", Json.str n.toString), ("user", Json.str u.toString),
      ("kind", Json.str kind), ("module", Json.str m.toString),
      ("private", Json.bool (isPrivateName n)),
      ("tyLib", Json.arr (lib tyAll)), ("valLib", Json.arr (lib valAll)),
      ("tyAll", Json.arr (tyAll.map fun c => Json.str c.toString))]
    IO.println j.compress
```

`DupCheck.lean`:

```lean
import ClassicalLean

/-! Evidence script for order G-7 (claude-ai, 2026-09-24), outside the repository. Read-only.
For every public `ClassicalLean` theorem, the theorems anywhere in the environment (Mathlib
included) whose type is the same `Expr` (`TWIN`), or the same with the two sides of a final `Eq`
or `Iff` swapped (`SWAP`). Run: `lake env lean <this file>` from the repository root. -/

open Lean Elab Command

partial def swapSides : Expr → Option Expr
  | .forallE n d b bi => (swapSides b).map fun b' => .forallE n d b' bi
  | e =>
    if e.isAppOfArity ``Eq 3 then
      some (mkApp3 e.appFn!.appFn!.appFn! e.appFn!.appFn!.appArg! e.appArg! e.appFn!.appArg!)
    else if e.isAppOfArity ``Iff 2 then
      some (mkApp2 e.appFn!.appFn! e.appArg! e.appFn!.appArg!)
    else none

run_cmd do
  let env ← getEnv
  let mut tbl : Std.HashMap UInt64 (Array Name) := {}
  for (n, ci) in env.constants.toList do
    if n.hasMacroScopes || n.isInternalDetail then continue
    unless ci matches .thmInfo _ do continue
    tbl := tbl.insert ci.type.hash ((tbl.getD ci.type.hash #[]).push n)
  let mut twins := 0
  let mut swaps := 0
  for (n, ci) in env.constants.toList do
    if n.hasMacroScopes || n.isInternalDetail || isPrivateName n then continue
    unless (`ClassicalLean).isPrefixOf n do continue
    unless ci matches .thmInfo _ do continue
    let same := (tbl.getD ci.type.hash #[]).filter fun m =>
      m != n && (env.find? m).any (·.type == ci.type)
    if !same.isEmpty then
      twins := twins + 1
      IO.println s!"TWIN {n} == {same}"
    if let some t' := swapSides ci.type then
      let sw := (tbl.getD t'.hash #[]).filter fun m => m != n && (env.find? m).any (·.type == t')
      if !sw.isEmpty then
        swaps := swaps + 1
        IO.println s!"SWAP {n} == symm {sw}"
  IO.println s!"DupCheck: {twins} TWIN line(s), {swaps} SWAP line(s)"
```

`islands.py`:

```python
"""Evidence script for order G-7 (claude-ai, 2026-09-24), outside the repository. Read-only.
Reads DeclGraph.lean's output and prints, per module, how many other modules use it and how many
it uses (a use: a constant of one module named in the type or value of a constant of another),
then the islands (used by none and using none). Usage: python3 islands.py declgraph.jsonl"""
import json, sys, collections
rows = [json.loads(l) for l in open(sys.argv[1])]
own = {r['user']: r['module'] for r in rows}
users, uses = collections.defaultdict(set), collections.defaultdict(set)
for r in rows:
    for c in set(r['tyLib']) | set(r['valLib']):
        m = own.get(c)
        if m and m != r['module']:
            users[m].add(r['module']); uses[r['module']].add(m)
mods = sorted(set(own.values()))
for m in mods:
    print(f"{m.removeprefix('ClassicalLean.'):46s} usedBy={len(users[m]):2d} uses={len(uses[m]):2d}")
isl = [m.removeprefix('ClassicalLean.') for m in mods if not users[m] and not uses[m]]
print(f"modules={len(mods)} constants={len(rows)} islands={len(isl)}: {', '.join(isl)}")
```

`pairs.py`:

```python
"""Evidence script for order G-8 (claude-ai, 2026-09-24), outside the repository. Read-only.
Reads DeclGraph.lean's output. For every pair of modules with no declaration-level use in either
direction, lists the rare non-library constants that the statements (types) of both modules name.
A constant is rare when the types of at most MAXDF modules name it. Usage:
python3 pairs.py declgraph.jsonl [MAXDF]"""
import json, sys, collections, itertools, math
rows = [json.loads(l) for l in open(sys.argv[1])]
MAXDF = int(sys.argv[2]) if len(sys.argv) > 2 else 3
own = {r['user']: r['module'] for r in rows}
edge = set()
for r in rows:
    for c in set(r['tyLib']) | set(r['valLib']):
        m = own.get(c)
        if m and m != r['module']:
            edge.add((r['module'], m))
conc = collections.defaultdict(set)
for r in rows:
    if r['private']:
        continue
    for c in r['tyAll']:
        if c.startswith('ClassicalLean') or c.startswith('_private'):
            continue
        conc[r['module']].add(c)
df = collections.Counter()
for m, cs in conc.items():
    for c in cs:
        df[c] += 1
mods = sorted(conc)
out = []
for a, b in itertools.combinations(mods, 2):
    if (a, b) in edge or (b, a) in edge:
        continue
    shared = sorted(c for c in conc[a] & conc[b] if df[c] <= MAXDF)
    if shared:
        score = sum(math.log(len(mods) / df[c]) for c in shared)
        out.append((score, a, b, shared))
out.sort(key=lambda t: -t[0])
print(f"modules={len(mods)} edges={len(edge)} rare_df<={MAXDF} pairs_without_edge_sharing_rare={len(out)}")
for score, a, b, shared in out[:40]:
    s = lambda m: m.removeprefix('ClassicalLean.')
    print(f"{score:6.2f} {s(a)} ~ {s(b)} :: {len(shared)} :: {', '.join(shared[:12])}")
```
