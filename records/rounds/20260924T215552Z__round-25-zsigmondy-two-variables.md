# Round 25 — Zsigmondy's theorem for aⁿ − bⁿ and its rank of apparition (order G-8, J1 and J2)

Session: Claude Code `session_01PsgZp4vkZNjXMztz4FHTzX` on helios, executing order `G-8`
(`records/orders/20260924T182500Z__claude-ai__order-g8-zsigmondy-catalan.md`), jobs J1 and J2.
Lean and Mathlib v4.34.0 throughout. Evidence: `~/work/_bump-evidence/g8/` — `evidence.log` (one
line per command, its own rc), `out/` (each command's output), `reviews/` (every review verbatim,
hashed in `evidence.log` on return), `critics/`, `scratch/` (the proofs as written).

This fragment opens with J2's first commit (the order's J2 Scope) and gains a section per landing.
Every number below is from a clean tree unless it says "mixed".

## J1 — open and re-measure (read-only), and the steps after approval

J1 ran 2026-09-24 from 19:43:02Z (reference file `g8/ref-j1-start`) to the plan's approval at
21:13:57Z (`evidence.log` label `approval`). Its predicted-beside-actual table is in the session's
report to Dustin; the record of every command is `~/work/_bump-evidence/g8/evidence.log` (one line
per command: UTC time, label, the command's own rc, its pipeline's `PIPESTATUS`, the prediction, the
output file). Predictions: `g8/predictions-j1.md`, `predictions-j1-item11.md`,
`predictions-j1-supplement.md`, `predictions-land.md`.

### The evidence helper (rule 23; J1 item 0)

`g8/ev.sh` takes a prediction, a label and a command; refuses (exit 125, nothing run, nothing
logged) on an empty or blank prediction, a bad label, an empty command or a wrong argument count;
otherwise runs the command from the repository root and appends one line with the command's own
`$?`. v1 missed one fail test (`false | true`: rc 1 against a prediction of 0), because helios's
`BASH_ENV` (`~/.bash_env`) switches pipefail on in every non-interactive bash; v2 sets pipefail
itself, so the rc no longer depends on the calling shell, and all eleven tests held, one of them with
`BASH_ENV` unset (labels `t1*`; the refusals re-run inside an outer logged call, `t2*`).

### Timeline (rule 18)

- 19:47–19:48Z helper built and fail-tested; 19:48:14–19:48:47Z J1 items 1–10.
- 19:49:40–19:50:50Z item 11's searches; `s3-12` at 19:58:19Z.
- 19:58:08–19:59:51Z junk cells; 20:00:47Z the first drafts elaborated with `sorry`.
- 20:03:44Z the plan draft; about 20:05Z–20:20:55Z four cold critics (statements, compliance,
  routes, evidence), their reports saved with sha256 (`critics-hash`).
- 20:24–20:27Z a supplement closing the gaps the critics found, and the cells for three statements
  they proposed (the sum clause, `ℕ` for Catalan, the symmetric existence criterion), then the drafts
  re-elaborated in each home module's scope (20:26:51–20:26:56Z).
- 20:29:42Z plan v2; a slip: the critic script was re-launched by mistake and stopped within seconds;
  `critics-rehash` (20:29:55Z) shows the four saved reports unchanged. About 20:30:22Z–20:47:50Z a
  cold delta check of v2; plan v3 applied it.
- 21:13:57Z Dustin approved plan v3. 21:14:08Z the deferred `lake build` (rc 0, 0 warnings, nothing
  rebuilt). 21:15–21:17Z `land.sh` built and fail-tested on a throwaway clone (11 cases); the quote
  checker's negative control. 21:16:55Z the order filed. The J1 commit through `land.sh`, then the
  clean-tree gates.
- About 21:20Z the J2 and J3 statement reviews dispatched together, while the proof-irrelevant type
  dump was built and controlled (rule 16 allows tool work to overlap a review; no proof was written
  before the verdicts).

### Searches and junk cells (rule 21), before any statement was drafted

The order's §0 row 14 commands re-run over `.lake/packages/mathlib/Mathlib`: 12 of 12 counts as
recorded (`r14-01`…`r14-12`: 0, 0, 1, 1, 0, 0, 3, 0, 0, 0, 4, 0). Shape searches for J2 and J3
(`s2-*`, `s3-*`), the library searches (`L-*`) and the definitions read for rule 2 (`defs`, `defs2b`)
are in `g8/out/`. Junk cells, exact integers, every line predicted first (`j2cells`, `j3cells`,
`supp-*`, `j3semiring`, `posctl2`): all held, reproducing the order's §0 rows 7–12 exactly (Zsigmondy
355,185 cells; the order translation 120,137; 4 (B) 189,936; 4 (C) 45,141 and its symmetric form
30,318; the route 141,480 … 14,000). Five of those lines cannot fail by construction and are listed
apart, not as measurements: `def.b=1`, `item1.trivial-ring`, `item1.order0`, `item2.trivial-ring`,
`item2.dickson`. The item-1 zeros are not vacuous: `j3_cells.item1` run unchanged on the Fibonacci
numbers reports 154 rank failures and hits in every modulus (`posctl2`).

### J1's own findings

- Misses: `0d` (pipefail, above); `5.2` (predicted one scoped exception; AxiomGate lists two
  theorems resting on the one axiom); `R1`, `R1c` (plain `git status` bumps `.git`'s mtime — see
  below); `stmts-count` (Lean quotes `sorry` in backticks). Refiled: `s2-11` a void run (shell
  quoting); `s2-09` a hit that corrects the order's §0 row 9 (`Algebra/Field/ZMod.lean:17` is `:18`).
- Search lessons: two declarations written `_root_.X` or `class _root_.X` missed by name patterns
  (`s2-05`, `defs` CharP); one prefix match read the wrong theorem (`defs`,
  `exists_isPrimitiveDivisor_iff` matched `…_of_three_le`); one filename-less `grep -rn` on a single
  file broke a parser (`defs2`, corrected by `defs2b`).
- `.git`'s directory mtime: plain `git status` takes `index.lock` for an optional refresh. J1 ran it
  at 19:48:14Z (twice, the order's item 3), 20:00:58Z and 20:01:15Z (twice, once on purpose to prove
  the cause — that test belonged on a throwaway clone). No content changed: `.git/index` untouched,
  porcelain empty, `HEAD` `87683e3`. The mtime also moved at 20:30:32Z with no command of this
  session's, inferred to be the harness's own `git status` when it spawned the delta checker. From
  then on every read-only status is `GIT_OPTIONAL_LOCKS=0`.
- Undisclosed pre-prediction read: at 19:39:36Z a `git log -3` and `git status` showed `87683e3` and
  a clean tree before `predictions-j1.md` was written — the values items `1c`, `3a`, `3b` and `R2`
  predict.
- Commands outside the helper after it existed: hashes and searches at 19:47:39–19:55:22Z, so
  `s2-05b` and `defs-charp` are reproductions of unlogged probes, not blind predictions; again at
  20:24:38Z and 20:29:36Z in the supplement, whose cited pre-hash `958a2b6b…a129` is therefore
  transcript-only; and one log line written by `tee`, not the helper (`evidence.log` line 29).
- `predictions-land.md` says `land.sh`'s hash was logged before its one edit; the edit came first,
  so both logged hashes are of the edited file.

### After approval

- `lake build` (label `5.1`): rc 0, 0 warnings, "Build completed successfully (3798 jobs)".
- `land.sh` (rule 23's commit half): `check` runs the six gates through the helper and records a
  fingerprint — `git diff HEAD --binary`, the untracked list, and the content of every listed path —
  and `commit` refuses unless that fingerprint, the path list and `HEAD` are unchanged, the message
  file is newer than the check, and the staged set equals the list. Fail-tested on a throwaway clone
  with stub gates, eleven cases, each predicted and each held: a failing gate, a build warning, an
  unlisted changed path, a listed unchanged path, a pre-staged path, a tracked edit after `check`, an
  untracked edit after `check`, a message older than `check`, a path staged at commit time, and the
  success path (exactly the two listed files, then reuse refused); every refusal left index and
  `HEAD` unchanged (`land-test-*`).
- The quote checker (rule 22): `g7/close/quotecheck.py` copied byte for byte to `g8/quotecheck.py`;
  negative control: a one-word alteration and an unmarked omission each FAIL, the same omission
  marked `[...]` passes (`qc-*`).
- The order filed by its own `mv -n` line (`file-order`), sha256 `0356ed2a…62c4` unchanged.
- The type dump up to proof irrelevance (rule 25): `TypeDumpPI.lean` and `g8_typediff.py`, beside
  `TypeDump.lean` and `g5_typediff.py`, which are unchanged. v1 failed control (a): it kept each
  proof's proposition as `inferType` gives it, and two proofs filling the same slot report it
  through different, definitionally equal instance paths. v2 replaces each proof by a bare
  placeholder; with the whole-library run needing `maxHeartbeats 0`, the final tool passed every
  control on its own final text: (a) round 23's two statements, old instance against today's, as
  named theorems dumped by the tool with only its import line changed: `PROOF-ONLY` ×2, changed 0
  (`ctl3-a`); (b) the `+` variant: `CHANGED` ×1 (`ctl3-b`); (c) on the clean tree: 1283 `thm`
  records, as AxiomGate; every record of the old dump present, with identical `pp`, `expr` and `val`;
  nothing elided (`before2-*`). The old tool on (a) reports both as changed (`ctl-a-old`), which is
  the blind spot rule 25 closes.
- "Before" evidence, clean tree, `~/work/_bump-evidence/g8-before/`: the new dump and the old one,
  `ListTheorems` (raw 1283, filtered 816), `ModuleThmCount` (1283 in 48 modules), Appendix A
  (1461 constants, 4 islands, `LucasApparition` used by no module, `DupCheck` 5 TWIN, 0 SWAP,
  `pairs.py` 84).

## J2 — statements, reviewed before any proof (rule 16)

The statements were drafted after J1's searches and junk cells (rule 21), elaborated with `sorry`
in their home modules' scopes under rule 20's four flags (`home-*`, 20:26:51–20:26:56Z), and sent
with J3's to cold statement reviews at 21:20:21Z (`stmt-reviews-dispatch`), which returned by
21:36:06Z (`stmt-reviews-hash`; J2's `reviews/stmt-j2.md`, sha256 `e48f09d5…cd61`). Its verdict:

> ## Overall verdict: GO-WITH-CHANGES
>
> Proofs may start at once on statements 1–3 and 5–9, as drafted. They may start on the changed
> list once it has been elaborated:

The changes — casts at the leaves in 4 (B) and 4 (C), the sum clause in the symmetric form under
the name `exists_primitive_prime_dvd_pow_add_pow_iff`, 4 (C) named
`exists_prime_lucasApparition_add_mul_eq_iff` in the symmetric form, and the order's `b < a` form
of 4 (C) as an `example` — were applied and the changed list elaborated with `sorry` (`rev-*`:
rc 0, only the predicted `sorry` warnings) before any proof. No J2 proof existed before the verdict.

## J2a — the definition and the order translation (`ClassicalLean/NumberTheory/Zsigmondy.lean`)

Adds, at the end of `ClassicalLean/NumberTheory/Zsigmondy.lean`: `IsPrimitiveDivisor₂` (the
classical definition over `ℕ`), `isPrimitiveDivisor₂_with_one` (its case `b = 1` is
`IsPrimitiveDivisor`), the private cast step `dvd_pow_sub_pow_iff_cast`, and
`isPrimitiveDivisor₂_iff_orderOf` (for `b ≤ a`, `¬ (p ∣ a ∧ p ∣ b)`, `0 < n`: a primitive divisor
exactly when `a / b` has order `n` in `ZMod p`); a dated section in the module docstring and a
dated line in its Prior art section. No import changes.

Route (rule 19): derived here, on the pattern of `isPrimitiveDivisor_iff_orderOf` — the cast step,
then `orderOf_eq_iff`; the case `p ∣ b` by `div_zero` and `orderOf_zero`.

Timeline (rule 18): proved at 21:37:41–21:37:52Z in `scratch/J2a.lean` (`j2a-try1`: one line over
100 characters; `j2a-try2`: rc 0, 0 warnings). J2b, J2c and all of J2d and J2e were then proved in
scratch files while J2a–J2c's post-proof review ran (21:39Z to 21:54:18Z); none of those proofs
touched a statement under review. The review (`reviews/post-j2abc.md`, sha256
`1de6cb52…6dbf`):

> **Verdict: FIX.** The proofs are sound, and every statement except one matches the reviewed text
> character for character.

Its five fixes were applied before this commit: the instance binder written `[Fact p.Prime]` as
reviewed (F3); the dated lines' texts corrected and written out in full (F1, F2, F5); "all three
hypotheses" in 4 (B)'s docstring (F4); the split by `n` credited to the statement review (N1). The
landed text was elaborated first as a file, by a script whose every insertion asserts its anchor
occurs once, on a scratch copy (`j2a-dry-apply`, `j2a-dry-elab`: rc 0, no output).

Commit: `cfdd276`. After it, on the clean tree (`after.sh j2a`): the six gates pass (lake build
0 warnings; AxiomGate 1288; check_records 48 modules, 18 files). AxiomGate was predicted at 1286;
the two extra constants are Lean's auxiliaries `IsPrimitiveDivisor₂.eq_1` (the equation lemma
`simp` creates when it unfolds the definition, predicted) and
`isPrimitiveDivisor₂_iff_orderOf._proof_1_2` (an extracted proof term, not predicted). Per-module
theorem constants (`ModuleThmCount.lean`): `ClassicalLean/NumberTheory/Zsigmondy.lean` 82 → 87.
The type dump against `g8-before`, up to proof irrelevance: removed 0, added 6, changed 0,
PROOF-ONLY 0. Appendix A: 1467 constants, 4 islands, `LucasApparition` used by no module yet,
`DupCheck` 5 TWIN, 0 SWAP; `pairs.py` 81 pairs (84 before).

## J2b — the rank of apparition at `(a + b, ab)` (`ClassicalLean/NumberTheory/LucasApparition.lean`)

Adds to `ClassicalLean/NumberTheory/LucasApparition.lean`, after
`lucasApparition_three_two_eq_orderOf`: `lucasApparition_add_mul_eq_orderOf_div` (in any field, for
`a ≠ b`, the rank of apparition of `U(a + b, ab)` is `orderOf (a / b)`) and an `example` recovering
`lucasApparition_three_two_eq_orderOf` without its `p ≠ 2` (at `p = 2` both sides are `0`); a dated
line in that theorem's docstring and a dated bullet in the module docstring. No import changes.

Route (rule 19): derived here — `lucasU_of_roots` gives `(a − b) U n = aⁿ − bⁿ`, so `U n = 0`
exactly when `(a / b)ⁿ = 1` (for `b = 0`, never at `n > 0`); then `lucasApparition_mem` and
`lucasApparition_le` against `orderOf_eq_iff`, or both sides `0` by `orderOf_eq_zero_iff'`.

Timeline: proved at 21:38:49Z (`j2b-try1`: rc 0, 0 warnings, first attempt); reviewed with J2a
(above). The dated line on `lucasApparition_three_two_eq_orderOf` is the post-proof review's F1
text: it removes `hp2` only, not the primality.

Commit: `5767c78`. After it, on the clean tree (`after.sh j2b`): the six gates pass (AxiomGate 1289,
as predicted); `ClassicalLean/NumberTheory/LucasApparition.lean` 66 → 67 theorem constants; the
type dump against `g8-before`: removed 0, added 7, changed 0, PROOF-ONLY 0; Appendix A: 1468
constants, 4 islands, `DupCheck` 5 TWIN, 0 SWAP.

## J2c — the rank of apparition reads off primitive divisors (`ClassicalLean/NumberTheory/Zsigmondy.lean`)

Adds to `ClassicalLean/NumberTheory/Zsigmondy.lean`: `isPrimitiveDivisor₂_iff_lucasApparition` (for
a prime `p`, `0 < n` and `¬ p ∣ a - b`: `p` is a primitive divisor of `aⁿ − bⁿ` exactly when `n` is
the rank of apparition of `p` in `U(a + b, ab)` over `ZMod p`; no coprimality, and `b < a` is
contained in `¬ p ∣ a - b`), and an `example`: `PrimitiveDivisor`'s Mersenne example without its
`p ≠ 2`. The module docstring's two-variable section and its Prior-art line gain the Lucas reading.
This is `LucasApparition`'s first use by a declaration in another module (order G-8 §0 row 4: used by
no module).

Route (rule 19): derived here — item 2 composed with 4 (A) over `ZMod p`. The rewrite chain closes
by `rfl`: the casts sit at the leaves, and item 2's and 4 (A)'s right sides are one term (the
post-proof review's N4, confirming two inferences the statement review had left unchecked).

Timeline: proved at 21:39:18Z (`j2c-try1`: rc 0, 0 warnings, first attempt), in one file with J2a
and J2b assembled by `scratch/combine.py`; the post-proof review's F4 ("all three hypotheses") applied.

Commit: `18e92ce`. After it, on the clean tree (`after.sh j2c`): the six gates pass (AxiomGate 1290,
within the predicted 1290–1292); `ClassicalLean/NumberTheory/Zsigmondy.lean` 82 → 88 theorem
constants over J2a and J2c; the type dump against `g8-before`: removed 0, added 8, changed 0,
PROOF-ONLY 0; Appendix A: 1469 constants, 4 islands, `LucasApparition` used by one module
(`Zsigmondy`) — J2 Done-means 4 — so the pair `LucasApparition ~ Zsigmondy` of order G-8 §0 row 6
is now an edge (`pairs.py`: 77 edges, 80 pairs); `DupCheck` 5 TWIN, 0 SWAP.

## J2d and J2e — Zsigmondy's theorem for aⁿ − bⁿ, its sum clause, and the ranks of apparition (`ClassicalLean/NumberTheory/ZsigmondyPowSubPow.lean`, new)

**One commit, not two** (rule 18). The plan landed J2d and J2e separately. They were proved
together, and the post-proof review found that the J2d file alone would carry docstring text about
J2e's theorem (its F1), so they land together, as the order allows for material proved whole.

Creates `ClassicalLean/NumberTheory/ZsigmondyPowSubPow.lean` (974 lines), which imports only
`NumberTheory/Zsigmondy`, and adds its import line to `ClassicalLean.lean`. Public declarations:
`cyclotomicHomogenized` (the homogenised value `Φₙ(a, b)`), `cast_cyclotomicHomogenized`,
`prod_cyclotomicHomogenized`, `cyclotomicHomogenized_dvd`, `cyclotomicHomogenized_mul_dvd`,
`isPrimitiveDivisor₂_of_dvd_cyclotomicHomogenized`, `cyclotomicHomogenized_zero`,
`eq_maxPrimeFac_of_dvd_cyclotomicHomogenized`, `not_sq_dvd_cyclotomicHomogenized`,
`exists_isPrimitiveDivisor₂_of_maxPrimeFac_lt`, `cyclotomicHomogenized_pos`,
`sub_pow_totient_lt_cyclotomicHomogenized`, `cyclotomicHomogenized_lt_add_pow_totient`,
`cyclotomicHomogenized_one`, `cyclotomicHomogenized_two`, `cyclotomicHomogenized_mul_prime_of_dvd`,
`cyclotomicHomogenized_mul_prime_mul`, `maxPrimeFac_lt_cyclotomicHomogenized_of_add_two_le`,
`maxPrimeFac_lt_cyclotomicHomogenized_add_one`, `isPrimitiveDivisor₂_zero_iff`,
`isPrimitiveDivisor₂_one_iff`, `exists_isPrimitiveDivisor₂_one_iff`, `isPrimitiveDivisor₂_two_iff`,
`exists_isPrimitiveDivisor₂_two_iff`, **`exists_isPrimitiveDivisor₂_iff`** (Zsigmondy's theorem),
**`exists_primitive_prime_dvd_pow_add_pow_iff`** (the sum clause), and
**`exists_prime_lucasApparition_add_mul_eq_iff`** (which `n` are ranks of apparition in
`U(a + b, ab)`); two `example`s (round 22's theorem at `b = 1`, and 4 (C) in the order's `b < a`
form); private helpers for the key lemma and for the inequalities. With the sum clause, the library
proves the statement of `docs/1000.yaml`'s Q8074796 in full. `NumberTheory/Zsigmondy`'s two-variable
section and Prior-art line point here; `NumberTheory/LucasApparition`'s "What is not here" gains a
dated paragraph (the criterion for distinct coprime positive integer roots; the sharp criterion for
other `(P, Q)` still not there).

Size clause: `Zsigmondy.lean` 694 lines and this module 974 — about 1,650 in one file, past the
order's "about 1,300" — so the order's escape applies, as plan v3 §2.3 predicted.

Where the landed route departs from plan v3 §2.2 (the post-proof review's N-g): no
`Mathlib.Algebra.Polynomial.Homogenize` import — the homogenised value is a direct sum of
coefficients (the order allowed "or written directly"); the bridges go through
`eval_eq_sum_range'`, not `eval_homogenize`; the product formula through `ℚ`, not
`homogenize_finsetProd`; 4 (C) at `(2, 1, 6)` through 4 (B) and `not_isPrimitiveDivisor_base_two_six`,
not 4 (A) and `exists_prime_orderOf_two_eq_iff`; and for `m = 2`, `P ≥ 5`, the stronger
`P (2b + 1) < (b + 1)ᴾ`. Sources as in the module docstring: the route is round 22's, which is the
prior art's; the homogenised value, the product formula, the four cases and the expansion
identities in two variables are claude-ai's (order G-8 §0 rows 7–10); the bridges, the split at
`m = 2`, the inequalities, the sum clause's route and the Lucas reading were derived here.

Timeline (rule 18): J2d's six parts were proved in `scratch/J2d.lean` at 21:41:50–21:51:32Z and
J2e at 21:52:32–21:53:15Z, all elaborated together at 21:53:50Z (`j2all-final2`: rc 0, 0 warnings)
— while J2a–J2c's post-proof review was out (it returned at 21:54:18Z) and before J2a–J2c landed
(21:56–22:00Z); none of them touched a statement under review. Their post-proof review was
dispatched at about 22:03Z (transcript only) and returned at 22:21:39Z (`reviews/post-j2de.md`,
sha256 `7c718e60…0b50`):

> The mathematics is sound and every statement is the reviewed one.

Its fixes F2–F7 (credit, one false "exactly", three inexact docstring claims, one piece of process
text) and notes N-a to N-d were applied, and F1 by the single commit; the fixed module elaborated
as a file before landing (`newmod2-dry-elab`: rc 0, no output). Gate 6's sequence: the module and
its import line were put in place without this section and `check_records.py` was shown FAIL on
the module, then this section was added and both committed together.

Commit: `25eee92` (22:24:19Z). After it, on the clean tree (`after.sh j2de`): the six gates pass
(lake build 0 warnings, 3799 jobs; AxiomGate 1421; check_records 49 modules, 18 files). AxiomGate
was predicted at about 1326–1345, from the source's 36 theorems (26 public, 10 private;
`j2de-srcdecls`) and a guessed allowance for Lean's auxiliaries. The module has 131 theorem constants
(`ModuleThmCount.lean`; `Zsigmondy` 88 and `LucasApparition` 67, unchanged), so 95 are auxiliaries:
79 extracted proof terms (`…_proof_N`), 15 `simp` auxiliary lemmas (`…_simp_N`) and the definition's
equation lemma `cyclotomicHomogenized.eq_1`, most of them under the three main theorems and two size
lemmas (`j2de-auxclass`, `j2de-auxparents`). The type dump against `g8-before`, up to proof
irrelevance: removed 0, added 143, changed 0, PROOF-ONLY 0 (predicted 132–140; the excess is three
definitions not predicted, pattern-match compilations `…match_1_N`, two under
`exists_isPrimitiveDivisor₂_iff` and one under `exists_prime_lucasApparition_add_mul_eq_iff`).
Appendix A: 1604 constants, 4 islands; the new module uses four modules (`Zsigmondy`,
`LucasApparition`, `LucasSequence`, `PrimitiveDivisor`; `j2de-uses`), so `pairs.py` reads 81 edges
(predicted 78: its statements name `lucasApparition` and `lucasU` directly, not only through
`Zsigmondy`) and 85 pairs; `DupCheck` 5 TWIN, 0 SWAP. Import closure, Lean-side
(`env.header.moduleNames` in a file importing only the new module; `j2de-importcheck`): 16
`ClassicalLean` modules (predicted 5 to 8: the prediction counted the chain through `Zsigmondy`, not
those modules' own imports); the module itself and `Zsigmondy` loaded (positive controls),
`AlgebraicGeneratingFunction` not (negative control), and `Mathlib.Algebra.Polynomial.Homogenize`
not loaded.

J2's records step (plan step 4) ran after J3, in one records commit with J3's; round 26's
"Records" section lists what it changed.
