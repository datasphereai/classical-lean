# ORDER G-9 — Lamé's theorem; Frobenius for Lucas sequences in characteristic p

Written 2026-09-24T23:55:00Z by claude-ai (Cowork, linked to helios) for one Claude Code session on
helios. Library: `~/work/classical-lean`. **Source of truth:** this file and `records/orders/INDEX.md`.
It waits in `~/Cowork/lean-orders/` until J1 files it, and starts only after order G-8 is closed.
A second agent reviewed it cold, twice, before it was placed there. The first pass found no
blocker, four major points (a cell script that did not check (L5); two miscounted searches; a
tool `land.sh` needs that J1 item 0 did not copy; the review line itself) and eleven minor
ones; the second confirmed those fixes, found that one of them had regressed §0 row 8's route
sentence, and four minor wordings, all applied without a third review. Every number in §0 that
the reviewer could re-run in the cloud, its own runs reproduced; it settled row 13's count.

It rests on three things:
- **Order G-8's close**: `HANDOFF.md` §3's ranking at that close puts Carmichael's theorem first,
  majorization second, the Frisch–Waugh–Lovell theorem third, Lamé's theorem fourth and
  Wolstenholme's theorem fifth; its "also open" list names `V_{p^k} = P ^ (p ^ k)` in
  characteristic `p`, the `ExpChar` form, a `lucasV` analogue of the rank of apparition, and
  `land.sh` under `LC_ALL=C`. This order takes the fourth item and the `V_{p^k}` item of the open list. It does
  not take the first item: order G-8 §0 row 13 measured what Carmichael's theorem needs, and §0
  row 16 below says why that is not one session's work yet.
- **claude-ai's measurements of the library at `196a87d`** (§0): the declaration graph (three
  islands; `LucasApparition` used by two modules), the module-pair comparison, the duplicate check,
  exact checks of every statement below with each hypothesis dropped, the Mathlib searches, and
  both statement lists elaborated with `sorry` in the library's environment on helios.
- **The lessons of order G-8's run** (§1, rules 26–30). Its mathematics passed every gate. Its
  Close check failed 21 items, none a wrong proof, statement or gate result: records corrections,
  two rulings, and three process lapses (round 26's addendum). Its two largest prediction misses
  were counts Lean generates, predicted by hand.

Three jobs, J1 to J3, then a close. Each has Goal / Scope / Done-means and an undo line. A STOP at a
gate is a report, not a close.

---

## 0. What claude-ai measured

Read-only, 2026-09-24 between 23:29Z and 23:55Z: the helios tree at `196a87d`, run through the four
scripts of Appendix A with `lake env lean` from the repository root (no `lake build`, nothing
written in the repository; `GIT_OPTIONAL_LOCKS=0 git status --porcelain` empty before and after),
with scratch files in `/tmp/claude-ai-g9/`; the evidence of order G-8 under
`~/work/_bump-evidence/g8/`, read-only; a sparse clone of Mathlib v4.34.0 (`5ed2965256`, the
manifest's pin); order G-8's session page, read end to end; exact checks in Python (integers, and
polynomials over `ℤ` in two variables). Line numbers were read then; find each place by its text.
"The reviewer" is the cold reviewer of this order; facts it found are marked so.

| # | Fact | Value |
|---|---|---|
| 1 | Order G-8 | Closed (`INDEX.md`, `CLAIMS.md`). `master`, `dsmain/master` and `ls-remote dsmain master` are all `196a87d`. The push `87683e3..196a87d` is in `~/work/_bump-evidence/push.log` (`rc=0 push [G-8, Dustin's yes 2026-09-24] :: To dsmain:/data/git/classical-lean.git 87683e3..196a87d master -> master`, followed by its `ls-remote` line) and in the `dsmain/master` reflog at 2026-09-24T23:25:19Z (`update by push`), and not yet in `HANDOFF.md` §6, by design (G-8's Close step 4). `~/Cowork/lean-orders/` held no file before this one. |
| 2 | The library | 49 modules in 10 top-level directories; 1434 theorem constants, 190 of them private, and a filtered list of 863 (`ListTheorems.lean`: `#COUNTS raw=1434 filtered=863 private=190`; `ModuleThmCount.lean`: `total=1434 private=190 modules=49`). 16,655 lines under `ClassicalLean/` (15,302 at `87683e3`). 50 files whose line 4 is `Authors: Dustin [surname], Claude (Anthropic)`: the 49 modules and `ClassicalLean.lean`. Gate 6 searches 19 records files and passes with its one named exemption (`Simplex/Hessian.lean`); gate 5 passes, 0 hits. `lean-toolchain` `v4.34.0`; the manifest's Mathlib `rev` `5ed2965256…`. |
| 3 | Five orders, measured from git and the rounds | See the table after this one. |
| 4 | Declaration graph (`DeclGraph.lean`, then `islands.py`) | 1617 constants in 49 modules. **Three islands**: `NumberTheory/Catalan`, `NumberTheory/CompositumDiscriminant`, `Order/Tolerance`. `NumberTheory/LucasApparition` `usedBy= 2 uses= 2`; `NumberTheory/ZsigmondyPowSubPow` `usedBy= 0 uses= 4`; `NumberTheory/Lucas` `usedBy= 4 uses= 1`; `Combinatorics/AlgebraicGeneratingFunction` `usedBy= 0 uses= 1`. All as order G-8's final report predicted. |
| 5 | Duplicates (`DupCheck.lean`) | `DupCheck: 5 TWIN line(s), 0 SWAP line(s)`, the five labelled "Mathlib re-export"s of `GoldenRatio/Characterisations`. |
| 6 | Pairs that share rare concepts and no use (`pairs.py`) | First line `modules=49 edges=82 rare_df<=3 pairs_without_edge_sharing_rare=87`. Highest: `S3Quaternion ~ SU2SO3` (10 shared), `Hopf ~ S3Quaternion` (6), then four pairs at 4, three of them with the island `CompositumDiscriminant` (`SU2SO3`, `Lucas`, `Simplex/Ordered`, and `LucasApparition` through `Field`, `Int.instCommSemiring`, `IsCoprime`). J2's new module will use `NumberTheory/Lucas` (item 4 below), so it is an edge, not a fourth island; J3 stays inside `LucasApparition`. Neither joins a listed pair. |
| 7 | Lamé's theorem, the statements (`lame_cells.py`, exact) | `euclidSteps a b` is the number of division steps of the Euclidean algorithm on `(a, b)`: `0` when `b = 0`, else `euclidSteps b (a % b) + 1`. Over `a, b ≤ 600` (361,201 cells) and 200,000 random pairs below `10¹²`, 0 failures of each of: **(L1)** `0 < b → fib (euclidSteps a b + 1) ≤ b`; **(L2)** `b < a → fib (euclidSteps a b + 2) ≤ a`; **(L4)** `euclidSteps a b ≤ 5 * (Nat.digits 10 b).length`, no hypothesis (`b = 0` gives `0 ≤ 0`; `a < b` costs one swap step and holds: the cells include it); and the weak form `0 < a → fib (euclidSteps a b) ≤ a`. Hypotheses dropped: (L1) at `b = 0` fails at every `a` (`fib 1 = 1 ≤ 0`, 601 of 601); (L2) with `b ≥ a` fails in 7,359 of 180,901 cells, first `(0, 0)`, and among `a = b` exactly at `a ∈ {0, 1}` (`(1, 1)`: one step, `fib 3 = 2 > 1`), while (L2) at `b = 0 < a` holds (600 of 600), so `0 < b` is not needed. **(L3)** `euclidSteps (fib (n + 3)) (fib (n + 2)) = n + 1` for `n < 60`; the form `euclidSteps (fib (n + 2)) (fib (n + 1)) = n` fails at `n = 0` only (`(1, 1)` takes one step). **(L5)** `euclidSteps (lucas (n + 2)) (lucas (n + 1)) = n + 1` for `n < 60` (`lucas 0 = 2`, `lucas 1 = 1`, the library's `NumberTheory/Lucas`), 0 failures; the one-step reductions `fib (n + 3) % fib (n + 2) = fib (n + 1)` and `lucas (n + 2) % lucas (n + 1) = lucas n` hold for `1 ≤ n < 60` and fail at `n = 0` (the reviewer found (L5) missing from the script's first version; the version that printed these numbers is `lame_cells.py`, sha256 `29c28567…870e`, and `frobenius_cells.py` is `166440d9…90e0`, both in claude-ai's cloud scratch; J1 item 11 writes its own cells). (L4)'s largest counts: one digit, 5 steps at `(5, 8)`; two, 10 at `(55, 89)`; three, 13 at `(233, 377)` — so the constant `5` is attained. |
| 8 | Lamé's theorem, the route (`lame_cells.py`) | (L1) and (L2) together, as one predicate `P b a` of the pair, by `Nat.gcd.induction` (core; used at `Data/Nat/Fib/Basic.lean:232`), which recurses on its first argument: at `b = 0`, (L1) is vacuous and (L2) is `fib 2 = 1 ≤ a` from `0 < a`; at `0 < b`, with `n' = euclidSteps b (a % b)` and `n = n' + 1`, the pair for `(b, a % b)` gives `fib (n' + 2) ≤ b` (its (L2), since `a % b < b`), which is (L1) for `(a, b)`; and for `b < a`, either `0 < a % b`, so `fib (n' + 1) ≤ a % b` (its (L1)) and `a ≥ b + a % b` (`Nat.div_add_mod`, `1 ≤ a / b`) give `fib (n' + 3) = fib (n' + 1) + fib (n' + 2) ≤ a` (`Nat.fib_add_two`), or `a % b = 0`, so `n' = 0` and `fib 3 = 2 ≤ 2 b ≤ a`. (L3), (L5): induction on `n` with `fib (n + 3) % fib (n + 2) = fib (n + 1)` for `n ≥ 1` (`fib (n + 3) = fib (n + 2) + fib (n + 1)`, `fib (n + 1) < fib (n + 2)` for `n + 1 ≥ 2`: `Nat.fib_lt_fib_succ` at `:97`) and `lucas (n + 2) % lucas (n + 1) = lucas n` for `n ≥ 1` (`lucas_add_two`, `lucas n < lucas (n + 1)` for `n ≥ 1`); the base cases `(2, 1)` and `(3, 1)` by `decide`. (L4): let `k = (Nat.digits 10 b).length`; `b < 10 ^ k` (`Nat.lt_base_pow_length_digits`, `Data/Nat/Digits/Defs.lean:390`); if `5 k + 1 ≤ euclidSteps a b` then by (L1) `fib (5 k + 2) ≤ b < 10 ^ k`, against **(L6)** `1 ≤ k → 10 ^ k < fib (5 k + 2)`; at `k = 0`, `b = 0` and the count is `0`. (L6) by induction: `10 < 13 = fib 7`; `fib (m + 5) = 3 fib m + 5 fib (m + 1)` (`Nat.fib_add` at `:141` with `n = 4`; checked `m < 70`) and `3 fib m ≤ 2 fib (m + 1)` for `2 ≤ m` (checked `m < 70`; false at `m = 1`), so `fib (5 k + 7) ≥ 3 fib (5 k + 2) + (15/2) fib (5 k + 2) > 10 · 10 ^ k`. `10 ^ k < fib (5 k + 2)` holds for `1 ≤ k ≤ 12` and fails at `k = 0` (`1 < 1`). Every identity here was checked exactly. |
| 9 | Frobenius for Lucas sequences, the statements (`frobenius_cells.py`, exact polynomials in `ℤ[P, Q]`; an identity "holds in characteristic `p`" when every coefficient of the difference is divisible by `p`, which is the identity in `ℤ[P, Q]/(p)` and so in every commutative ring of characteristic `p`) | **(F1)** `V (p n) = V n ^ p` for every prime `p < 24`, `n ≤ 12`: 117 cells, 0 failures; the control at the composite moduli `4, 6, 8, 9` fails at every `n ≤ 12` (already at `n = 0`: `2 − 2 ^ m`). **(F2)** `U (p n) = D ^ (p / 2) · U n ^ p` for the odd primes `p < 24`, `n ≤ 12`: 104 cells, 0 failures; at `p = 2` the `D`-form fails at every `1 ≤ n ≤ 12` (first difference `U 2 − D = P − P ² + 4 Q`, nonzero mod `2`), while **(F4)** `U (2 n) = P · U n ^ 2` holds mod `2` for `n ≤ 12`; **(F3)** `V n = P · U n` in characteristic `2` is the identity `V (n + 1) = U (n + 2) − Q U n = P U (n + 1) − 2 Q U n` (`lucasV_succ_eq`) and `V 0 = 2 = 0 = P · U 0`. **(F5)** `V (p ^ k) = P ^ (p ^ k)`, primes `p < 12`, `k ≤ 3`: 19 cells, 0 failures. **(F6)** `U (p ^ k) = D ^ (p ^ k / 2)`, odd primes `p < 12`, `k ≤ 3`: 15 cells, 0 failures; its exponent step `(p − 1)/2 + p (p ^ k − 1)/2 = (p ^ (k+1) − 1)/2` checked for `p ≤ 13`, `k < 6`. **(F7)**, its case `k = 1`, `U p = D ^ (p / 2)` in any commutative ring of odd prime characteristic: round 24 has it over `ZMod p` for every prime, including `2`, where it holds because `x ^ 2 = x` in `ZMod 2` — over a general ring of characteristic `2` it fails (the `p = 2` line of (F2)). **(F8)** `dickson 1 a (p ^ k) = X ^ (p ^ k)`: the polynomial form of (F5), as J3a's `dickson_one_eq_X_pow_of_charP` is of `lucasV_prime_eq_pow`. Characteristic-`0` controls: `V 2 − P ^ 2 = −2 Q`, `V 6 − V 2 ^ 3 ≠ 0`. `V n ^ 2 − D U n ^ 2 = 4 Q ^ n` re-checked for `n ≤ 40` (the library's `lucasV_sq_sub_discr_mul_lucasU_sq`). |
| 10 | Frobenius, the route | Round 26's J3a, with `M ^ n` in place of `M`. For a `2 × 2` matrix `A` over `R` with `CharP R p`, `p` odd, put `N = 2 A − (tr A) 1`; then `N ^ 2 = ((tr A) ^ 2 − 4 det A) 1` (`Matrix.det_fin_two` at `Determinant/Basic.lean:806`, `Matrix.trace_fin_two` at `Trace.lean:220`, `fin_cases` and `ring`, as `two_smul_lucasCompanion_pow_charP` does), `(2 A) ^ p = ((tr A) 1 + N) ^ p = (tr A) ^ p 1 + N ^ p` (`add_pow_char_of_commute`), `N ^ p = ((tr A) ^ 2 − 4 det A) ^ (p / 2) N` (odd `p`). At `A = M ^ n` with `n ≥ 1`: `tr A = V n` (`lucasCompanion_pow_succ_trace`), `det A = Q ^ n` (`lucasCompanion_pow_det`), `A ^ p = M ^ (p n)`, and `(tr A) ^ 2 − 4 det A = D · U n ^ 2` (`lucasV_sq_sub_discr_mul_lucasU_sq`). The trace gives `2 ^ p V (p n) = 2 V n ^ p` (`tr N = 0`), the `(1, 0)` entry (`lucasCompanion_pow_succ`: the entry below the diagonal of `M ^ (m + 1)` is `U (m + 1)`) gives `2 ^ p U (p n) = 2 (D U n ^ 2) ^ (p / 2) U n = 2 D ^ (p / 2) U n ^ p`; `2 ^ p = 2` and `2` a unit in `R` from `ZMod p` through `ZMod.castHom`, as J3a does; `n = 0` by `simp` (`V 0 = 2`, `2 ^ p = 2`; `U 0 = 0`). `p = 2`: (F1) from `lucasV_two_mul` (`V (2 n) = V n ^ 2 − 2 Q ^ n`); (F3) by `lucasV_succ_eq`; (F4) from `lucasU_two_mul` (`U (2 n) = U n · V n`) and (F3). (F5), (F6): induction on `k` from (F1), (F2) with `p ^ (k + 1) = p · p ^ k`, and `add_pow_char_pow_of_commute` (`Algebra/CharP/Lemmas.lean:146`) or `ZMod.pow_card_pow` (`FieldTheory/Finite/Basic.lean:592`) are not needed for that induction; (F7) is (F6) at `k = 1` or (F2) at `n = 1`; (F8) from (F5) in `R[X]` at `(X, C a)` through `lucasV_eq_dickson_one_eval` and `map_dickson`, as J3a. The route is derived here (rule 19), on J3a's pattern. |
| 11 | Both statement lists elaborated with `sorry` on helios | `/tmp/claude-ai-g9/DraftLame.lean` (sha256 `e21e27e0…e849`; imports `ClassicalLean.NumberTheory.Lucas` and `Mathlib.Data.Nat.Digits.Lemmas`; the definition by well-founded recursion on `b`, `euclidSteps_zero_right`, `euclidSteps_of_pos`, and (L1)–(L6)): `lake env lean` with rule 20's four flags, rc 0; six `sorry` warnings, two `unusedVariables` warnings on the definition's unused pattern `a`, one long line. `/tmp/claude-ai-g9/DraftFrobenius.lean` (sha256 `fb72cc28…cbc4`; imports `ClassicalLean.NumberTheory.LucasApparition` only; (F1)–(F8) and the `example` recovering `lucasV_prime_eq_pow` from (F5) at `k = 1` by `simpa`): rc 0; eight `sorry` warnings; the fifteen `#check`s of row 10's Mathlib and library names all resolve from that one import (`add_pow_char_pow_of_commute`, `ZMod.pow_card_pow`, `Matrix.det_fin_two`, `Matrix.trace_fin_two`, `Matrix.det_pow`, `lucasV_two_mul`, `lucasU_two_mul`, `lucasV_succ_eq`, `lucasCompanion_pow_det`, `lucasCompanion_pow_succ`, `lucasCompanion_pow_succ_trace`, `lucasV_sq_sub_discr_mul_lucasU_sq`, `lucasV_prime_eq_pow`, `dickson_one_eq_X_pow_of_charP`, `ZMod.castHom`). Porcelain 0 after both. So J3 needs no new import, and J2's module needs `NumberTheory/Lucas` and `Mathlib.Data.Nat.Digits.Lemmas` (`Nat.lt_base_pow_length_digits` is in `Digits/Defs.lean`, which `Lemmas` imports). |
| 12 | Mathlib v4.34.0 searches (commands below) | `lam[ée]` 0; `euclid` with step/iteration/count 0; `wolstenholme` 0; harmonic numbers modulo a prime 0 — the command's one hit is a docstring line of `SumPrimeReciprocals.lean` matching `Primes`, and the `NumberTheory/Harmonic/` files are real-analytic; Lucas sequence or apparition 1 (unchanged); `dickson` with `CharP` or `ZMod` 4 lines, all at `a = 1`, none at a prime power; `trace_pow_card` 2 (`ZMod.trace_pow_card`, `Charpoly/FiniteField.lean:60`, over `ZMod p` only — it gives (F1) over `ZMod p` in two lines and nothing over a general ring). Present: `Nat.fib_gcd` (`Data/Nat/Fib/Basic.lean:231`), `Nat.fib_add` (`:141`), `Nat.fib_add_two` (`:75`), `Nat.fib_lt_fib_succ` (`:97`), `Nat.fib_add_two_strictMono` (`:103`), `Nat.le_fib_self` (`:116`), `Nat.lt_base_pow_length_digits` (`Digits/Defs.lean:390`), `Nat.digits_length_le_iff` (`Digits/Lemmas.lean:68`), `add_pow_char_pow_of_commute` (`Algebra/CharP/Lemmas.lean:146`), `ZMod.pow_card_pow` (`FieldTheory/Finite/Basic.lean:592`), `dickson_one_one_mul` (`Dickson.lean:183`), `dickson_one_one_charP` (`:269`). `Wanted/` has nothing on Fibonacci, Euclid, Lamé, Wolstenholme or Carmichael. |
| 13 | `docs/1000.yaml` at v4.34.0 | 1199 entries, 955 with no `decl`, `decls` or `url` (order G-8 §0 row 15's numbers; the reviewer confirmed them with `yaml.safe_load`). claude-ai's first parse, a split on `^Q\d+:` lines, gave 1179 and 936: it misses the 20 keys with a letter suffix (`Q180345X`, `Q4724004A`, …) — a parser error, recorded here as one. Confirmed by search, each with no `decl`, `decls` or `url`: Q230848 `Lamé’s theorem` (a curly apostrophe in the file), Q1724049 Wolstenholme's theorem, Q3889376 Carmichael's theorem, Q8074796 Zsigmondy's theorem, Q1059151 FWL theorem, Q599876 Cochran's theorem, Q608294 max flow min cut, Q928813 Menger's theorem. If J2 lands, the library proves Q230848's statement; listing it needs a public URL, and is Dustin's decision. |
| 14 | Order G-8's run, from its page and evidence (UTC) | Session from about 19:39 (its first read; round 25's reference file `g8/ref-j1-start` at 19:43:02; `predictions-j1.md` after it); Dustin's two messages: `yes plan approved` at 21:13:57 and `yes` to the push at about 23:25. J1's report and the plan at about 21:05; approval; the deferred build 21:14; the order filed 21:16:55; `ada6126` 21:18:01. J2a–J2c `cfdd276`, `5767c78`, `18e92ce` at 21:56:34–22:01:09; J2d/J2e `25eee92` 22:24:19; J3a `1f49f9e` 22:35:59; J3b `87653a4` 22:38:38; records `552c38a` 22:45:30; Close `a972c77` 22:48:37; the Close check dispatched 22:50:19, its three reports saved 23:09:17, 23:11:49, 23:19:10; the addendum `196a87d` 23:21:04; the push 23:25:19. `evidence.log`: 658 lines, 19:47:19 to 23:25:32. Workflows on the page: four plan critics, one delta check, two statement reviews (first dispatch failed on a template-string parse error, re-dispatched), three post-proof reviews (J2a–c, J2d/e, J3), three Close checkers; one re-launch of the critic script by mistake, stopped within seconds, the saved reports shown unchanged. The local guard refused one whole Bash call, for a stray `python3 -` line (J3's docstring edits, about 22:07); the session's context was compacted once (at the J2d/J2e commit, about 22:24). Prediction misses, all counts Lean generates: AxiomGate 1288 against 1286 (J2a), 1421 against 1326–1345 (J2d/J2e: 95 auxiliaries), 143 against 132–140 (type-dump records), 81 against 78 (edges), 16 against 5–8 (import closure). |
| 15 | Order G-8's records against its evidence files | The nine review files' modification times (UTC) — `stmt-j2.md` 21:34:26, `stmt-j3.md` 21:35:20, `post-j2abc.md` 21:52:59, `post-j2de.md` 22:20:27, `post-j3.md` 22:22:28, `close-B.md` 23:09:17, `close-A.md` 23:11:49, `close-C.md` 23:19:10, `close-brief.md` 22:49:29 — each precede or equal the hash time rounds 25 and 26 give them. `git rev-list --count ada6126^..196a87d` is 10, as the final report's row says; the lines under `ClassicalLean/` are 15,302 → 16,655 and the filtered list 816 → 863, as it says. One claim of the final report is contradicted by the page: "Nothing stopped. The only refusals were my own tools" — the guard's refusal (row 14) is a refusal the report did not count; it is not in `evidence.log`, since the helper never ran (rule 30). A pitfall for the next cycle: helios's `ls --time-style` prints local time (EDT); read evidence times with `TZ=UTC`. |
| 16 | Carmichael's theorem, why not this order | Order G-8 §0 row 13's measurement stands: the analytic core is a lower bound on the Fibonacci cyclotomic numbers `c_n` that the triangle inequality does not give, Mathlib has no `Φₙ(−X)` identity and no reversal lemma, round 22's key lemma fails at `n = 6, 12`, and `p = 2`, `p = 5` need their own treatment. Nothing was re-measured this cycle. The elementary route (Yabuta 2001, through the rank of apparition and the bound `α(p) ≤ p + 1`, which round 24 has) has not been measured cell by cell; that measurement is claude-ai's next-cycle job, before any order proposes the theorem. |
| 17 | Order G-8's tools, for J1 item 0 | `~/work/_bump-evidence/g8/ev.sh` sha256 `0a426beb…3766` (v2, sets `pipefail`); `g8/land.sh` sha256 `a9b871cb…c3c2` — it hard-codes `E=/home/dustin/work/_bump-evidence/g8`, compares the changed paths with the listed ones by `comm -23` and `comm -13` after `sort -u` inside command substitutions, and never reads `comm`'s exit status; on helios `sort` and `comm` are the Rust coreutils and disagree on collation for mixed-case names (round 26's Close: a false refusal is possible, a false pass is not). `g8/quotecheck.py`, byte for byte `g7/close/quotecheck.py`. `TypeDumpPI.lean` (2026-09-24T21:24:50Z) with `g8_typediff.py` are rule 14's pair; `TypeDump.lean` and `g5_typediff.py` unchanged since 2026-09-23. |

Row 3, the five orders. "Wall clock" runs from the order's filing commit to its closing commit,
UTC; "commits" is `git rev-list --count <filing commit>^..<closing commit>`. The first four rows
are order G-8 §0's; the fifth is this cycle's, from the page and git (row 14).

| Order | Wall clock | Commits | Modules | Lines under `ClassicalLean/` | Filtered list | Close check | Dustin's decisions |
|---|---|---|---|---|---|---|---|
| 0923 | 09-23 14:09–17:12 (includes a STOP) | 18 | 41 → 44 | 12,446 → 13,069 | → 725 (round 17) | every checkable item met, after findings | the STOP (delegated to claude-ai), the push |
| G-5 | 09-23 18:54–20:34 | 12 | 44 → 45 | → 13,619 | 725 → 746 | every checkable item met, after an evidence-log finding | the plan, the push |
| G-6 | 09-24 00:49–02:04 (J1 from 00:12) | 14 | 45 → 48 | → 14,757 | 746 → 791 | 41 held, 2 failed (records), both remedied | the plan with the credit, the push |
| G-7 | 09-24 15:40–17:42 (J1 from 14:43) | 11 | 48 → 48 | 14,757 → 15,302 | 791 → 816 | 63 held, 9 failed (one type-dump item, eight records and process), 5 pending by design | the plan with step V, the push |
| G-8 | 09-24 21:18–23:21 (J1 from 19:43, round 25's reference file; session from about 19:39) | 10 | 48 → 49 | 15,302 → 16,655 | 816 → 863 | 213 held, 21 failed (18 distinct: 13 records corrections, 2 departures ruled, 3 process lapses), 7 not checkable | the plan (v3), the push |

Row 12's searches, from the Mathlib clone's root:

```
grep -rniE "lam[ée]'?s? theorem|lamé" Mathlib --include=*.lean | wc -l                          # 0
grep -rniE 'euclid' Mathlib --include=*.lean | grep -ciE 'step|iteration|count|number of'       # 0
grep -rniE 'wolstenholme' Mathlib --include=*.lean | wc -l                                      # 0
grep -rniE 'harmonic' Mathlib --include=*.lean | grep -ciE 'ZMod|prime|mod '                    # 1, a docstring line of NumberTheory/SumPrimeReciprocals.lean ("Primes")
grep -rniE 'lucasU|lucas.?sequence|apparition' Mathlib --include=*.lean | wc -l                 # 1
grep -rnE 'dickson' Mathlib --include=*.lean | grep -cE 'CharP|ZMod'                           # 4
grep -rnE 'trace_pow_card' Mathlib --include=*.lean | grep -c theorem                          # 2
grep -rnE 'theorem [a-zA-Z_.]*fib[a-zA-Z_.]*' Mathlib/Data/Nat/Fib/*.lean | grep -ciE 'gcd|digit|log'   # 3, all gcd
grep -rnE 'lemma (add_pow_char_pow_of_commute|sub_pow_char_pow_of_commute)' Mathlib --include=*.lean | wc -l   # 2
grep -rniE 'lam[ée]|euclid|wolstenholme|carmichael|fibonacci' Wanted | grep -viEc 'EuclideanSpace|euclidean'  # 0 (7 without -E: the seven Euclidean-space lines; the reviewer's finding)
```

**Predict J1 from `HANDOFF.md` §1 and §6, `records/orders/INDEX.md`, `records/CLAIMS.md` and
`push.log`, not from this table** — except J1 items 6, 7, 9, 10 and 11, which re-run claude-ai's
measurements and predict from rows 4–13 and 17. §6 lags the last push by design, so `push.log`
predicts item 4.

---

## 1. Rules for this session

- **`HANDOFF.md` §6 holds**: rules 1–25 and the standing answers, with §0, §3, §4 and §5, and
  README Rules 1 to 4. They are not repeated here.
- **Dustin does not read code or files.** Everything he needs goes in your chat reply. When he must
  act, give the exact command, the box, and the output you expect.
- **Predict, then measure.** Write the expected value, or "no prediction", before any command that
  prints a count, a hash or an rc. Report predicted beside actual.
- **Run every command from `~/work/classical-lean`**, or give `git -C` and absolute paths.
- **Five rules learned in order G-8's run** (§0 rows 14 and 15, round 25's timeline, round 26's
  addendum), numbered as J2's records step will file them in `HANDOFF.md` §6. In this order
  "rule N" means `HANDOFF.md` §6's rule N, 1–30; `records/README.md`'s rules are written
  "README Rule N".
  26. **Every brief is built by script from `HANDOFF.md` and saved with its sha256 before it is
     sent**, as order G-8's Close-check brief was (`close-brief-make`); a brief that claims to
     quote a rule verbatim quotes it verbatim, cuts marked `[...]` (round 26's addendum, item 16:
     the J3 post-proof brief shortened rules 16–25 without marking the cuts, and the J2 briefs were
     never saved).
  27. **A count that Lean generates is predicted by a Lean measurement of the scratch file, not by
     hand.** Theorem constants: a census of the elaborated scratch file's environment under the
     axiom gate's `.thmInfo` predicate, restricted to the declarations being landed, auxiliaries
     included; import closures: `env.header.moduleNames` of a file importing the module alone
     (order G-8: 1421 against a hand prediction of 1326–1345, 16 modules against 5–8; §0 row 14).
     A hand prediction may accompany the measurement; it does not replace it.
  28. **A workflow or script that consumes inputs takes them as arguments and refuses to run
     without them.** Order G-8's critic script ignored its arguments; re-invoked by mistake it
     would have re-run four critics over the old draft and overwritten their saved reports
     (round 25's timeline, 20:29:42Z; §0 row 14).
  29. **A review fix that touches a proof line gets its delta check before the landing**, as the
     review's condition asked (round 26's addendum, item 18: `hp.out` to `(Fact.out : p.Prime)`
     landed without it; the gates and the type dump then held, which is luck, not a check).
  30. **A refused call is logged `NOT RUN`** (rule 8) in the next helper call, with the refused
     command's label and the guard's message, so that the final report's count of refusals is a
     `grep` of `evidence.log` and not a recollection (§0 row 15: the report said "nothing stopped"
     and "the only refusals were my own tools" over one guard refusal the log never saw).
- **Environment facts** (`HANDOFF.md` §6's standing answers, dated order G-7 and G-8): write every
  commit message to a file and commit with `git commit -F <file>`; write scripts to files in the
  evidence directory and run them as `python3 <file>`; the local guard refuses inline `python3 -c`,
  chained in-place edits, and any Bash call that contains `python3 -` reading from stdin; helios's
  `BASH_ENV` switches `pipefail` on; a read-only status runs as `GIT_OPTIONAL_LOCKS=0 git status`;
  helios's `ls` prints local time — read evidence times with `TZ=UTC` (§0 row 15).
- **Steps and commits.** Land a step as its own commit when it was proved as a step. If a module is
  proved whole before its first landing, land it in one commit and record its step structure in
  the fragment (rule 18); do not cut step commits from a finished file.
- **Gate 6.** J2 creates one module; J3 creates none. The rules of order G-6 §1 apply to J2's
  module: until a round fragment names the new file, write its path or bare filename into none of
  the files gate 6 searches (`PROVENANCE.md`, `records/rounds/*.md`, `records/orders/*.md`,
  `INDEX.md` included; `CLAIMS.md` is not searched and does name it, as J1 step 3 says); show
  `check_records.py` FAIL on it with its import line in place; then commit it together with the
  fragment that names it. This order does not name it; the plan does (J1's Done-means).
- **Git, reviews and builds** as in order G-5 §1:
  - commit locally, never push to GitHub or add a remote, park and never delete;
  - reach DSMain only with `GIT_SSH_COMMAND='ssh -o BatchMode=yes -o ConnectTimeout=15'`; if DSMain
    is unreachable, record "unreachable" and carry on; never touch the VPN, routes or ssh
    configuration;
  - a fresh cold reviewer before and after proving; builds one at a time; subagents never run `lake`.

## 2. Standing answers — do not stop to ask these

- **Everything in `HANDOFF.md` §6's standing answers** still holds.
- **The push record.** J1 compares `HANDOFF.md` §6 with `push.log` and the `dsmain/master` reflog.
  J2's records step adds the dated line for `87683e3..196a87d` (2026-09-24T23:25:19Z, on Dustin's
  yes to order G-8's push question), taken from `push.log` and the reflog.
- **Order G-8's two rulings on Dustin's delegation stand** (round 26's addendum, items 14 and 15):
  the revised type-dump pair is rule 14's evidence, and the Lean-side import closure
  (`env.header.moduleNames`, with a positive and a negative control) is the record of an import
  closure. This order uses both; his veto stays open.
- **Where the new theorems live**, pre-answered; a different home is allowed if the plan says why
  and the import closure is recorded:
  - J2, all of (L1)–(L6) and the definition, in one new module under `NumberTheory/`, named in the
    plan (§1's gate-6 rules), which imports `ClassicalLean.NumberTheory.Lucas` (for (L5); `Lucas`
    imports `Mathlib.Data.Nat.Fib.Basic` and `NumberTheory/FactorialPart`) and
    `Mathlib.Data.Nat.Digits.Lemmas` (for (L4)), and no other library module; `ClassicalLean.lean`
    gains its one import line. (§0 row 11: those two imports suffice for the statements.)
  - J3, all of (F1)–(F8), at the end of `NumberTheory/LucasApparition`'s `section Frobenius`, before `end Frobenius`
    (its last two theorems are `two_mul_lucasU_prime_add_one` and
    `two_mul_mul_lucasU_prime_sub_one`); no new import (§0 row 11).
  Neither closes a cycle: `Lucas` uses one library module (`FactorialPart`), and `LucasApparition`
  gains no import. J1 checks it (item 7).
- **`euclidSteps`'s definition is content, its name and its recursion form are not.** The
  definition is fixed by its equations: `euclidSteps a 0 = 0` and, for `0 < b`,
  `euclidSteps a b = euclidSteps b (a % b) + 1` (§0 row 7). Whether it recurses by well-founded
  recursion on `b` (as the draft does) or mirrors `Nat.gcd`'s argument order is the plan's choice;
  both equations are proved as theorems either way.
- **Names are suggestions** for the statement reviews; Mathlib's naming conventions decide.
- **Anything that needs Dustin:** ask in one line, recommended answer first, and keep working on
  whatever does not depend on it. Pushing, publishing, listing anything in Mathlib's
  `docs/1000.yaml`, offering anything to Mathlib and retiring modules are his.

---

## J1 — open and re-measure (read-only)

**Goal.** Know that order G-8 is closed and that the tree is what its records say, and record the
searches and junk cells of J2 and J3 (rule 21), before touching the tree.

**Scope.** Read-only in the repository. Write only under `~/work/_bump-evidence/`: `g9/`, and after
approval `g9-before/`. Run what plan mode allows. List the rest with predictions, marked "deferred".

**Measure, predicting each value first:**

0. **The tools first** (rule 23). Copy `g8/ev.sh`, `g8/land.sh` and `g8/quotecheck.py` (which `land.sh` runs on every listed
   fragment, at `$E/quotecheck.py`; the reviewer's finding) to `g9/`, byte for byte except:
   the one executable path in each shell tool becomes `g9` (`land.sh` line 25, `E=`; `ev.sh` line
   24, `EV=`; their header comments may keep their `g8` text, and `quotecheck.py` is unchanged);
   `export LC_ALL=C` before any `sort` or `comm`; and each `comm` runs outside a command
   substitution or has its exit status read, so a non-zero `comm` refuses the check (§0 row 17).
   Record all three files' sha256 before and after. Fail-test them, predictions first: `ev.sh`'s eleven
   tests of round 25 (`t1*`, `t2*`; no prediction refused, `false` logged rc 1, `true` rc 0,
   `false | true` rc 1), and `land.sh`'s eleven cases of round 25 on a throwaway clone with stub
   gates, plus one case whose listed paths mix upper- and lower-case initials (`HANDOFF.md`,
   `records/x.md`, `ROADMAP.md`): pass. Run every later command through `ev.sh`; the gate runner
   and the commit step call it, and a commit runs only when all six gates exited 0 in the same
   run. A guard refusal is logged `NOT RUN` (rule 30).
1. `records/orders/INDEX.md` row `G-8`: its state, and what landed. `CLAIMS.md`: no open row.
2. `lean-toolchain` and `lakefile.toml` `rev`: expect v4.34.0.
3. `GIT_OPTIONAL_LOCKS=0 git -C ~/work/classical-lean status --short`: expect nothing.
4. `git -C ~/work/classical-lean rev-parse master dsmain/master`, and
   `GIT_SSH_COMMAND='ssh -o BatchMode=yes -o ConnectTimeout=15' git -C ~/work/classical-lean ls-remote dsmain master`:
   predict from `push.log`'s last push line, or record "unreachable". Compare §6's push list with
   `push.log` and the reflog, and name every push §6 lacks (expect one: G-8's).
5. The six commands in `HANDOFF.md` §1, copied from it. Predict from its snapshot. Gate 1 is
   deferred until approval, as in order G-8; a read-only probe stands in for it.
6. **Appendix A.** Write its four files into `~/work/_bump-evidence/g9/claude-ai/`, check each
   sha256 against the appendix, and run them as their headers say. Predict from §0 rows 4–6:
   1617 constants, 49 modules, 3 islands by name, `LucasApparition` with `usedBy= 2`;
   `DupCheck: 5 TWIN line(s), 0 SWAP line(s)`; `pairs.py`'s first line
   `modules=49 edges=82 rare_df<=3 pairs_without_edge_sharing_rare=87`.
7. **The import checks of §2**, Lean-side (`env.header.moduleNames`, positive and negative
   control): `Lucas`'s closure holds `FactorialPart` and no other library module;
   `LucasApparition` loaded alone reaches `Mathlib.Algebra.CharP.Lemmas`,
   `Mathlib.FieldTheory.Finite.Basic` and `Mathlib.RingTheory.Polynomial.Dickson`; `Lucas` loaded
   alone reaches `Mathlib.Data.Nat.Fib.Basic` and does not reach `Mathlib.Data.Nat.Digits.Lemmas`
   (§0 row 11: the draft imports it explicitly; predict from that).
8. The number of files under `ClassicalLean/` and `ClassicalLean.lean` whose line 4 is exactly
   `Authors: Dustin [surname], Claude (Anthropic)`: expect 50.
9. **Rule 20's flags.** Re-run order G-8's `FlexTest.lean` (`g8/FlexTest.lean`; measured present by `ls g8/` this cycle) once with plain
   `lake env lean` and once with the four options as flags: 0 warnings, then 2 `flexible`.
10. **The evidence tools.** sha256 of `~/work/_bump-evidence/TypeDumpPI.lean`, `g8_typediff.py`,
    `g8/ev.sh`, `g8/land.sh`, `g8/quotecheck.py`; predict `ev.sh` (`0a426beb…3766`) and `land.sh` (`a9b871cb…c3c2`) from §0 row 17,
    the rest "no prediction", and record them for round 27.
11. **J2's and J3's searches and junk cells (rule 21)**, written under `g9/` before the plan drafts
    any statement:
    - re-run §0 row 12's commands over `.lake/packages/mathlib/Mathlib` (and `Wanted/` is not in
      the package: record that line as "not reproducible on helios" unless the clone is there), and
      add shape searches: for J2 at least `Nat.gcd.induction` (core, not in Mathlib's tree: the search finds its uses, `Fib/Basic.lean:232` among them), `Nat.fib_add`, `Nat.fib_add_two`,
      `Nat.fib_lt_fib_succ`, `Nat.lt_base_pow_length_digits`, `Nat.digits_length_le_iff`,
      `Nat.div_add_mod`, `Nat.mod_lt`, and a search for any Mathlib count of Euclid's steps
      (`gcd` with `steps|fuel|iterations`); for J3 at least `add_pow_char_of_commute`,
      `add_pow_char_pow_of_commute`, `ZMod.pow_card_pow`, `ZMod.trace_pow_card`,
      `Matrix.det_fin_two`, `Matrix.trace_fin_two`, `dickson_one_one_charP` and every `dickson`
      theorem naming a power `p ^`. Record every command and count.
    - read every Mathlib and library definition the statements use, and the theorems their routes
      rest on (rule 2): `Nat.fib`, `Nat.digits` (and `Nat.digits 10 0 = []`), `Nat.gcd.induction`,
      `lucas` (`NumberTheory/Lucas`), `lucasU`, `lucasV`, `lucasDiscr`, `lucasCompanion`,
      `lucasCompanion_pow_succ`, `lucasCompanion_pow_succ_trace`, `lucasCompanion_pow_det`,
      `lucasV_sq_sub_discr_mul_lucasU_sq`, `lucasV_two_mul`, `lucasU_two_mul`, `lucasV_succ_eq`,
      `two_smul_lucasCompanion_pow_charP` (private; read it as the pattern), `lucasV_prime_eq_pow`,
      `lucasU_prime_eq_lucasDiscr_pow`, `CharP` (declared `class _root_.CharP`; search with the
      prefix), `Polynomial.dickson`.
    - junk cells, random plus constructed (rule 3), each script predicted first: for J2 the cells of
      §0 rows 7 and 8 (`b = 0`, `a = 0`, `a = b` at `0` and `1`, `a < b`, the tight pairs
      `(5, 8)`, `(55, 89)`, `(233, 377)`, `k = 0` and `m = 1` in (L6)'s identities); for J3 the
      cells of §0 row 9 (`n = 0`, `p = 2` in both forms, the composite moduli that must fail,
      characteristic `0`, `k = 0`).

**If order G-8 is not closed, STOP and report.**

**Done-means.** A predicted-beside-actual table in the chat, with every miss explained. Then one plan
for J2 and J3, with their statements drafted after item 11, naming J2's module, and wait for
approval. The plan ends with Dustin's decision in one line, recommended answer first:
- "Recommended: yes — approve this plan."

**After approval, in this order:**

1. **Run the deferred commands.** STOP before J2 on any miss you cannot explain.
2. **File the order:**
   `mv -n ~/Cowork/lean-orders/20260924T235500Z__claude-ai__order-g9-lame-frobenius.md ~/work/classical-lean/records/orders/ && test ! -e ~/Cowork/lean-orders/20260924T235500Z__claude-ai__order-g9-lame-frobenius.md && test -f ~/work/classical-lean/records/orders/20260924T235500Z__claude-ai__order-g9-lame-frobenius.md`.
3. **Add the records rows, then commit exactly three paths:** the filed order,
   `records/orders/INDEX.md` and `records/CLAIMS.md`.
   - `INDEX.md`: a row for `G-9`, naming no new file.
   - `CLAIMS.md`: a row naming the modules J2 and J3 write (J2's new module by the plan's name,
     `ClassicalLean.lean` for its import line, `NumberTheory/LucasApparition`) and the records
     paths: `HANDOFF.md`, `ROADMAP.md`, the round 27 and 28 fragments, `CLAIMS.md` and `INDEX.md`.
4. **Take the "before" evidence on a clean tree** into `~/work/_bump-evidence/g9-before/`: the
   type dump (`TypeDumpPI.lean` with `g8_typediff.py`, rule 14 as amended), the raw and filtered
   name lists, `ModuleThmCount`, and item 6's four outputs. J2 and J3 diff against these.

**Undo:** nothing to undo in the repository; the evidence tools live outside it.

---

## J2 — Lamé's theorem

**Goal.** The classical bound on the Euclidean algorithm — after `n` division steps on `(a, b)`
the entries are at least `F (n + 2)` and `F (n + 1)`, attained by consecutive Fibonacci numbers,
so the algorithm takes at most five times as many steps as the smaller entry has decimal digits
(Lamé 1844; `docs/1000.yaml` Q230848, title only, §0 row 13). It is `HANDOFF.md` §3's fourth item,
and the first Euclidean-algorithm statement in the library.

**Scope.**
- One new module under `NumberTheory/`, named in the plan (§1's gate-6 rules; §2's home): the
  definition, (L1)–(L6), and a docstring that records the searches (§0 row 12) and the prior art
  (none in Mathlib; the route is the textbook induction, derived here from the cells). It imports
  `ClassicalLean.NumberTheory.Lucas` and `Mathlib.Data.Nat.Digits.Lemmas`; the header with the
  current Authors line; one import line in `ClassicalLean.lean`; the Lean-side import closure with
  its positive and negative control (§2).
- `HANDOFF.md` §3 and §6, `ROADMAP.md` §2 (a new row, `2.13`, in the form of the `DONE` rows) and
  §1.15 (islands unchanged at three, the new module an edge through `Lucas`), records. Round 27's
  fragment opens with the first J2 commit.

**The statements** (content fixed by §0 rows 7 and 8; the names are suggestions):

1. **The definition.** `euclidSteps : ℕ → ℕ → ℕ` with `euclidSteps a 0 = 0` and, for `0 < b`,
   `euclidSteps a b = euclidSteps b (a % b) + 1`; both as theorems (§2).
2. **(L1)** for `0 < b`: `Nat.fib (euclidSteps a b + 1) ≤ b`.
3. **(L2)** for `b < a`: `Nat.fib (euclidSteps a b + 2) ≤ a`. (No `0 < b`: §0 row 7.)
4. **(L3)** `euclidSteps (Nat.fib (n + 3)) (Nat.fib (n + 2)) = n + 1`, every `n`.
5. **(L5)** `euclidSteps (lucas (n + 2)) (lucas (n + 1)) = n + 1`, every `n` — the module's use of
   `NumberTheory/Lucas`.
6. **(L4)** `euclidSteps a b ≤ 5 * (Nat.digits 10 b).length`, every `a`, `b`, with **(L6)**
   `1 ≤ k → 10 ^ k < Nat.fib (5 * k + 2)` as its lemma (public or private, the plan's choice).
   State each with the weakest hypotheses the proof allows; §0 row 7 records which hypothesis each
   needs and the cell that fails without it.

**Method.**

1. **Statement review before proving** (rule 16). The searches and junk cells are J1 item 11's
   (rule 21). Draft every J2 statement, elaborate them with `sorry` under rule 20's flags in the
   module's scope, and send the list to one cold statement review whose brief is built by script
   and quotes rules 16–30 (rules 24 and 26). Its verdict is in before any J2 proof is written.
2. **The route** (§0 row 8): `Nat.gcd.induction` for (L1) and (L2) together; induction on `n` for
   (L3) and (L5) with the one-step reductions `fib (n + 3) % fib (n + 2) = fib (n + 1)` and
   `lucas (n + 2) % lucas (n + 1) = lucas n` (both for `n ≥ 1`; the bases by `decide`); (L4) from
   (L1), `Nat.lt_base_pow_length_digits` and (L6); (L6) by induction with `Nat.fib_add` at `n = 4`
   and `3 fib m ≤ 2 fib (m + 1)` for `2 ≤ m`. Another route is fine if the fragment names its
   source.
3. **Land** in one commit if the module is proved whole (§1), a post-proof review of every new
   declaration before it (rule 13), quotes script-checked (rule 22). Gate 6's sequence (§1): the
   module and its import line in place, `check_records.py` shown FAIL on it, then the fragment
   section that names it, then one commit.
4. **Records** (after step 3 has landed; each line records only what landed).
   - `HANDOFF.md` §6: §1's rules 26–30, each with its date and source; the lead-in names five
     orders (0923: 1–7; G-5: 8–15; G-6: 16–19; G-7: 20–25; G-8: 26–30). The dated push line of
     §2. A standing answer for `TZ=UTC` (§1's environment facts).
   - `ROADMAP.md`: row `2.13`, Lamé's theorem, `DONE`, with §0 row 12's searches and the three
     tight pairs of §0 row 7; a dated line in §1.15 (the new module uses `Lucas`; islands three).
   - `HANDOFF.md` §3: the fourth item done.
   - Complete round 27's fragment (README Rule 1).

**Done-means.**
1. The six gates pass on a clean tree, with 0 warnings and 0 vocabulary hits.
2. Every new theorem is within the kernel trio. The statement review and the post-proof review are
   saved (rule 17) and quoted in round 27's fragment, every quote script-checked (rule 22).
3. The type dump against J1's evidence shows only additions, judged up to proof irrelevance
   (rule 25).
4. Appendix A on the landed tree: 50 modules, islands 3, the new module `uses= 1` (`Lucas`) and
   `Lucas` `usedBy= 5`; `DupCheck: 5 TWIN line(s), 0 SWAP line(s)`.
5. The fragment carries the searches, the junk cells, the route with its sources, the per-module
   counts (rule 27's census beside the prediction), and the Lean-side import closure of the new
   module with its two controls.
6. No `sorry` ships. A statement that did not close stays out of the file and is described in
   `HANDOFF.md` §3. (L4) depends on (L1) and (L6); (L3) and (L5) depend on nothing else.

**Undo:** yes — `git revert` of the one commit (it removes the module and its import line).

---

## J3 — Frobenius for Lucas sequences in characteristic p

**Goal.** The Frobenius identities `V (p n) = V n ^ p` and, for odd `p`,
`U (p n) = D ^ (p / 2) · U n ^ p` in any commutative ring of characteristic `p`, with their
prime-power cases `V (p ^ k) = P ^ (p ^ k)` and `U (p ^ k) = D ^ (p ^ k / 2)`, the `dickson` form,
and the characteristic-`2` identities. `V (p ^ k) = P ^ (p ^ k)` is `HANDOFF.md` §3's open item
from round 26's statement review (its cell D); the rest is what the same matrix computation gives
once `M ^ n` replaces `M` (§0 row 10), and (F1) is Mathlib's `ZMod.trace_pow_card` shape carried to
every ring of characteristic `p` and to the second entry.

**Scope.** `NumberTheory/LucasApparition`, at the end of `section Frobenius`, before
`end Frobenius` (§2): new declarations, a dated bullet in the module docstring, and a dated line
under its "What is not here" only if something there becomes false. No existing statement changes;
no existing proof changes unless a step says so; `two_smul_lucasCompanion_pow_charP` and
`lucasV_prime_eq_pow` stay byte for byte (the generalised helper is a new private theorem beside
them). `ROADMAP.md` §2.1 (a dated line) and `HANDOFF.md` §3 (the open item done). Records. Round
28's fragment. Every other module is read-only.

**The statements** (content fixed by §0 row 9; `[Fact p.Prime] [CharP R p]` as
`lucasV_prime_eq_pow` has them; the names are suggestions):

1. **(F1)** `lucasV P Q (p * n) = lucasV P Q n ^ p`, every prime `p`, every `n`.
2. **(F2)** for `p ≠ 2`: `lucasU P Q (p * n) = lucasDiscr P Q ^ (p / 2) * lucasU P Q n ^ p`.
3. **(F3)** in characteristic `2`: `lucasV P Q n = P * lucasU P Q n`.
4. **(F4)** in characteristic `2`: `lucasU P Q (2 * n) = P * lucasU P Q n ^ 2`.
5. **(F5)** `lucasV P Q (p ^ k) = P ^ (p ^ k)`, every `k`.
6. **(F6)** for `p ≠ 2`: `lucasU P Q (p ^ k) = lucasDiscr P Q ^ (p ^ k / 2)`, every `k`.
7. **(F7)** for `p ≠ 2`: `lucasU P Q p = lucasDiscr P Q ^ (p / 2)` — round 24's
   `lucasU_prime_eq_lucasDiscr_pow` (over `ZMod p`, every prime) in any ring of odd prime
   characteristic; the docstring says why `p = 2` is excluded here and not there (§0 row 9).
8. **(F8)** `dickson 1 a (p ^ k) = X ^ (p ^ k)` in `R[X]`, every `a`, every `k`.
Recover `lucasV_prime_eq_pow` from (F5) at `k = 1` by an `example` (the draft's `simpa` closes it),
and `dickson_one_eq_X_pow_of_charP` from (F8) at `k = 1`.

**Method.**
1. The searches and junk cells are J1 item 11's (rule 21).
2. **Statement review before proving** (rule 16), under rule 20's flags, with a brief built by
   script (rules 24 and 26).
3. **The route** (§0 row 10): the private helper for a general `2 × 2` matrix in odd characteristic
   (round 26's `two_smul_lucasCompanion_pow_charP` with `A` for `M`), applied at `A = M ^ n`; the
   trace for (F1), the `(1, 0)` entry with `lucasCompanion_pow_succ` and
   `lucasV_sq_sub_discr_mul_lucasU_sq` for (F2); `p = 2` from `lucasV_two_mul`, `lucasV_succ_eq`,
   `lucasU_two_mul`; (F5), (F6) by induction on `k`; (F8) as J3a. Another route is fine if the
   fragment names its source; `ZMod.trace_pow_card` gives (F1) over `ZMod p` only, and the fragment
   says so if it is used for anything.
4. Land per statement group if proved per group, in one commit if proved whole (§1); a post-proof
   review before each commit (rule 13); a fix touching a proof line gets its delta check (rule 29).

**Done-means.**
1. Every landed commit passes the six gates with 0 warnings, and every theorem is within the kernel
   trio.
2. No `sorry` ships. A statement that did not close stays out of the file and is described in
   `HANDOFF.md` §3. As routed, (F5) and (F8) depend on (F1) only; (F6) and (F7) on (F2) only; (F4) on (F3); (F1), (F2) and (F3) on nothing else in J3.
3. Both reviews are saved and quoted in round 28's fragment (rules 17 and 22). The fragment carries
   the searches, the junk cells, the route and its source, the per-module count (rule 27's census
   beside the prediction), and that `LucasApparition` gained no import.
4. Appendix A on the landed tree: islands unchanged; `DupCheck: 5 TWIN line(s), 0 SWAP line(s)`.
   The type dump against J1's evidence shows only additions, judged up to proof irrelevance
   (rule 25): `two_smul_lucasCompanion_pow_charP`, `lucasV_prime_eq_pow` and
   `dickson_one_eq_X_pow_of_charP` unchanged.

**Undo:** yes — `git revert`.

---

## Close

1. **Refresh `HANDOFF.md`.**
   - §1: the snapshot from the six commands on a clean tree.
   - §3's "what next", re-ranked with this order's results. The list: Carmichael's theorem
     (Q3889376), first, with §0 row 16's note that the elementary route is measured before an
     order proposes it; majorization (Mathlib's TODO); the FWL theorem, then Cochran (Q1059151,
     Q599876); Wolstenholme's theorem (Q1724049; §0 row 12: Mathlib has no harmonic sum modulo a
     prime, so the route `H_{p−1} ≡ 0 (mod p²)` is all new); max-flow min-cut and Menger (Q608294,
     Q928813); Mathlib's wanted list; and, not ranked, the three islands, the other pairs of §0
     row 6, the `ExpChar` form, and a `lucasV` analogue of the rank of apparition.
2. Close the `CLAIMS.md` row and update the `INDEX.md` rows.
3. **The Close check.** Fresh subagents check every Done-means against
   `git diff <this order's first commit>^..master`, with a brief built by script that quotes rules
   16–30 verbatim (rules 24 and 26). Save their outputs first, hashed in the same command (rule
   17), then record the verdict, quoted and script-checked (rule 22), as an addendum to round 28.
   If it runs before step 2, say so (rule 18).
4. **Ask Dustin, in one line:** "Recommended: yes — push classical-lean master to DSMain, a
   fast-forward from 196a87d to <new>." Push only on yes:
   `GIT_SSH_COMMAND='ssh -o BatchMode=yes -o ConnectTimeout=15' git -C ~/work/classical-lean push dsmain master`,
   fast-forward only, never `--force`. Then log the push in `push.log`. The next order records it in
   §6.
5. **The final chat report:** predicted beside actual, what landed with commit hashes, what stopped
   and why, what comes next, and:
   - the net change in theorem constants on the filtered list;
   - Appendix A's numbers before and after (islands, the new module's uses, `TWIN` and `SWAP`
     lines, `pairs.py`'s first line);
   - this order's row for §0's order table, in the same columns;
   - the count of refusals, as a `grep` of `evidence.log` (rule 30), and of void runs;
   - one line each on any decision made on Dustin's delegation, and on any overlap rule 18 recorded.

## Not in this order

- **G-4**: the number-theory track.
- **Publishing, listing in `docs/1000.yaml`, or offering anything to Mathlib**: Dustin's decisions.
  If J2 lands, the library proves Q230848's statement; J3's `dickson` forms, with J3a's, are
  candidates for Mathlib, and a Mathlib reviewer would ask for the `ExpChar` form (`HANDOFF.md` §3).
- **Retiring any module**: Dustin's decision. Three islands remain, recorded, not bridged.
- **Carmichael's theorem** (§0 row 16), **majorization, FWL and Cochran, Wolstenholme, max-flow
  min-cut**: ranked at the Close.
- **The other pairs of §0 row 6**, `S3Quaternion ~ SU2SO3` among them: recorded, not bridged.
- **Any change to `tools/`** or to the banned-vocabulary list.
- **Anything in the lane on DSMain**, and the Claude Code configuration on helios.

---

## Appendix A — claude-ai's four evidence scripts

Write each into `~/work/_bump-evidence/g9/claude-ai/` byte for byte (the text between the fences,
ending with one newline), and check its sha256 before running it. All four are order G-8's
Appendix A, unchanged, their docstrings included (they still say "order G-7" and "order G-8": that
is their text).

```
a120cee455d000e78a7a60ad6cff1b93d9c1a6e15abaccf13e83a6dd95e8b3e0  DeclGraph.lean
9687c7ff6a81312c2aa9ccabbf380514ceffa479d63ade5afba2584f188c53e9  DupCheck.lean
f9aff2c78593cff456ab3e0970d3747cbaac32763aa53a03ed879c6395ec0404  islands.py
f734b8108ea1cf2c3e53c09877364891c24d71dcce74f3e3440ac4608222018a  pairs.py
```

Run, from `~/work/classical-lean`:

```
lake env lean ~/work/_bump-evidence/g9/claude-ai/DeclGraph.lean > ~/work/_bump-evidence/g9/claude-ai/declgraph.jsonl
python3 ~/work/_bump-evidence/g9/claude-ai/islands.py ~/work/_bump-evidence/g9/claude-ai/declgraph.jsonl
python3 ~/work/_bump-evidence/g9/claude-ai/pairs.py ~/work/_bump-evidence/g9/claude-ai/declgraph.jsonl
lake env lean ~/work/_bump-evidence/g9/claude-ai/DupCheck.lean
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
