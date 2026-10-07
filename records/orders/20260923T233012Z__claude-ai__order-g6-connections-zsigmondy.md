# ORDER G-6 — credit Claude, prove the information-geometry connections, then Zsigmondy for aⁿ − 1

Written 2026-09-23T23:30:12Z by claude-ai (Cowork, linked to helios) for one Claude Code session on
helios. Library: `~/work/classical-lean`. **Source of truth:** this file and `records/orders/INDEX.md`.
It waits in `~/Cowork/lean-orders/` until J1 files it, and starts only after order G-5 is closed.
A second agent reviewed it cold, twice, before it was placed there. The first pass found one blocker
and twenty-two smaller points; the second confirmed those fixes and found six small points, which
were applied without a third review.

It rests on three things:
- **Order G-5's close**: the ranked next steps in `HANDOFF.md` §3 and `ROADMAP.md` §2.5, §2.9–§2.12.
- **claude-ai's pattern analysis of the library**: connections between modules that never cite each
  other's declarations. Rows 4–6 of §0 become J2; row 9 records four more.
- **Dustin's wish, 2026-09-23, to credit Claude** on the Authors line. J2 step 1 does it; the
  copyright line stays his.

Three jobs, J1 to J3, then a close. Each has Goal / Scope / Done-means and an undo line. A STOP at a
gate is a report, not a close.

---

## 0. What claude-ai measured

Read-only, 2026-09-23 between 23:00Z and 23:30Z: staged copies of the helios tree, a sparse clone
of Mathlib v4.34.0 (`5ed2965256`), a clone of `github.com/FujiHaruka/information-theory` at
`7e97b77`, the order G-5 session's page, and symbolic and numeric checks in Python (sympy 1.14,
numpy). No Lean was run by claude-ai. Line numbers were read then; find each place by its text.

| # | Fact | Value |
|---|---|---|
| 1 | Order G-5 | Closed (`INDEX.md`). DSMain has `59fa0d9`, pushed on Dustin's yes at 17:04:46 EDT, and `master` is one records commit ahead (`HANDOFF.md` §6). From the session's page, not the records: that commit is `e115720`, and the session recommended leaving it for this order's push. |
| 2 | The library | 45 modules in 10 top-level directories; 1098 theorem constants, filtered list 746 (round 20). 46 files (45 modules and `ClassicalLean.lean`) have line 4 exactly `Authors: Dustin [surname]`. The `[surname]` exception in `tools/banned_vocab_scan.py` (line 144) permits exactly that line and the copyright line. |
| 3 | Evidence tools | In `~/work/_bump-evidence/`: `TypeDump.lean`, `ListTheorems.lean`, `ModuleThmCount.lean`, `import_closure.py`, `junk_cells.py`, `g5/j3/junk_cells_gm.py`. Round 19 names `g5_typediff.py`, which compares two type dumps, but not its directory; J1 finds it. |
| 4 | Pattern P1 | `Simplex/Hessian`'s matrix is `T` times the Fisher–Rao metric in the chart, plus the barrier: `hessian T lam kap = T • !![lam⁻¹ + eta⁻¹, eta⁻¹; eta⁻¹, kap⁻¹ + eta⁻¹] + !![(lam ^ 2)⁻¹, 0; 0, 0]`, `eta = 1 - lam - kap`. The 2×2 matrix is `Simplex/FisherRao`'s `∑ uᵢ vᵢ / pᵢ` at `p = ![lam, kap, eta]` with `u = ![u₁, u₂, -u₁ - u₂]`. Symbolic check: the difference is the zero matrix, even at the junk value `0⁻¹ = 0`. `FisherRao` reaches `Hessian` only indirectly, through `DesignConstants`, and names none of its declarations. |
| 5 | Pattern P2 | The covariance of a one-hot draw, `Σ(p) = diagonal p - vecMulVec p p`, inverts the Fisher–Rao metric on the tangent space: `Σ(p) *ᵥ (u / p) = u` whenever `∑ u = 0` and no `pᵢ` is `0`, and in the chart above `FisherRaoChart * Σ = 1` when `lam`, `kap` and `eta` are positive (symbolic). `Σ(softmax x)` is the Hessian of `logSumExp` (symbolic, three coordinates). So the Legendre pair of `Simplex/LogSumExp` is inverse at second order too. The library has only first derivatives (`hasDerivAt_logSumExp`, `hasDerivAt_crossEntropy`). |
| 6 | Pattern P3 | The Gauss–Markov theorem, in weighted coordinates, **is** the Cramér–Rao inequality on a finite outcome set. With weights `p ≥ 0`, a centred statistic `T - E T` and scores `S`, put `C = (T - E T) * diagonal √p` and `X = diagonal √p * Sᵀ`. Then `C * X = E[(T - E T) Sᵀ]`, `Xᵀ * X = E[S Sᵀ]` (the Fisher information) and `C * Cᵀ = Cov T`. Numeric check: 2,000 random cases, identities exact to 1e-8, least eigenvalue of `Cov T − E[S Sᵀ]⁻¹` is −2e-11; the reviewer's exact rational checks found no failure in 678 cases, including unnormalised `p` and uncentred `S`. For the categorical family in the chart of P1, the Fisher information is P1's 2×2 matrix, and the one-hot estimator's covariance is its inverse, so it attains the bound. |
| 7 | Mathlib v4.34.0 and the prior art (commands below) | `softmax`: 0 in both. Cramér–Rao: 0 in Mathlib (only Cramer's rule), 0 in the prior art (only Cramér's large-deviation theorem). Fisher information: 0 in Mathlib; 686 lines in 54 files of the prior art, for densities (de Bruijn, Stam), with no Cramér–Rao. Fisher–Rao, Bhattacharyya: nothing in either; Mathlib's one hit is an author's name. These are name searches; J2 step 2 adds shape searches. |
| 8 | Zsigmondy's exceptional set | Numeric, from cyclotomic values: over `a = 2..60`, `n = 1..40` (2,360 pairs), `aⁿ − 1` has no primitive prime divisor exactly at `(2, 1)`, `(2, 6)`, and `n = 2` with `a + 1` a power of 2 (`(3, 2)`, `(7, 2)`, `(15, 2)`, `(31, 2)`): 0 mismatches with J3's statement. The reviewer confirmed it from the definition over `a = 2..300`, `n = 1..60`. |
| 9 | Patterns recorded, not proved in this order | **P4**, the Fisher–Rao metric is spherical: for `x` with no zero coordinate, `fisherRao (x²) (2x⊙v) (2x⊙w) = 4 ⟨v, w⟩` (symbolic). It would join `Geometry/S3Quaternion`'s `sqCoords` to `Simplex/FisherRao`, a second link from `S3Quaternion` into Simplex after `sqCoords_mem_closedSimplex`; it is not the number-theory link `ROADMAP.md` §1.5 asks for. **P5**: `Geometry/Hopf`'s map is the `(k, j, i)` components of `q̄ * i * q`, which is `Geometry/SU2SO3`'s `adjoint (star q) i` (symbolic): the Hopf map is the orbit of `i` under that rotation action. **P6**, the law of apparition `α(p) ∣ p − (D/p)`: 684 checks over 9 `(P, Q)`, primes below 400 not dividing `2QD`, 0 failures. Its split case, `(3, 2)` with `D = 1`, is Fermat's little theorem in `MersenneOrder`; `LucasApparition` (line 63) says the general bound is not proved. **P7**, majorization: Mathlib's own TODO, `Analysis/Convex/Birkhoff.lean:29–30`, reads "Show that for `x y : n → R`, `x` is majorized by `y` if and only if there is a doubly stochastic matrix `M` such that `M *ᵥ y = x`." The library has entropy under doubly stochastic matrices (`InformationTheory/Channel`), the sorted simplex as a fundamental domain (`Simplex/Ordered`) and permutation invariance (`Simplex/Symmetry`), and never names majorization. |

Row 7's searches, as claude-ai ran them (Mathlib from the clone's root, the prior art from its root):

```
grep -rniE 'softmax' Mathlib --include=*.lean | wc -l                                      # 0
grep -rniE 'cram[eé]r.?rao' Mathlib --include=*.lean | wc -l                               # 0
grep -rniE 'fisher.?info|fisherInformation' Mathlib --include=*.lean | wc -l               # 0
grep -rniE 'fisher.?rao|fisherRao|bhattacharyya' Mathlib --include=*.lean | wc -l          # 1 (an author's name)
grep -rniE 'softmax' InformationTheory --include=*.lean | wc -l                           # 0
grep -rniE 'cram[eé]r.?rao' InformationTheory --include=*.lean | wc -l                     # 0
grep -rniE 'fisher.?info|fisherInformation' InformationTheory --include=*.lean | wc -l     # 686
grep -rniE 'fisher.?rao|fisherRao|bhattacharyya' InformationTheory --include=*.lean | wc -l  # 0
```

**Predict J1 from `HANDOFF.md` §1 and §6, `records/orders/INDEX.md` and `records/CLAIMS.md`, not
from this table.**

---

## 1. Rules for this session

- **`HANDOFF.md` §6 holds** — order 0923's seven rules and order G-5's standing answers — with §0, §3,
  §4 and §5, and `records/README.md` Rules 1 to 4. They are not repeated here.
- **Dustin does not read code or files.** Everything he needs goes in your chat reply. When he must
  act, give the exact command, the box, and the output you expect.
- **Predict, then measure.** Write the expected value, or "no prediction", before any command that
  prints a count, a hash or an rc. Report predicted beside actual.
- **Run every command from `~/work/classical-lean`**, or give `git -C` and absolute paths.
- **Eight rules learned in order G-5's run.** J2 step 6 moves them into `HANDOFF.md` §6 as rules 8
  to 15, so that §6 keeps one numbered list.
  1. **An evidence log records only a measured rc**, taken from the command's own `$?`. A run that
     did not happen is logged `NOT RUN`, never a placeholder (round 20, the Close check's addendum).
  2. **Time windows use epoch seconds, or `find -newer <reference file>`**, never a formatted UTC
     time without its `Z` (order G-5's session page, as claude-ai read it; not recorded in round 20).
  3. **Test harnesses match identifiers exactly, never by prefix.** Suspect the harness first when a
     result surprises (round 20: `S1` matched `S10`).
  4. **`lake env lean` checks types only.** Linter results count only from `lake build`, run from the
     repository root: `[leanOptions]` apply only there, and the header linter finds the root by a
     relative path (rounds 19 and 20).
  5. **Reviewers work in a scratch directory outside the repository**, with
     `PYTHONDONTWRITEBYTECODE=1`, copy a repository script before importing it, and are followed by
     a `git status` check (round 20: two reviewers wrote outside their brief).
  6. **Every new declaration, private helpers included, is reviewed cold before its commit** (round
     20: three helpers were reviewed only after proving).
  7. **Before-and-after evidence is `TypeDump.lean` with `g5_typediff.py`**, not name lists alone
     (round 19, "The type dump, and its fire test").
  8. **A pattern written for a tool is tested under that tool's own compile flags** (round 19:
     claude-ai's exception, compiled with `re.I`, also admitted lowercase variants).
- **Gate 6 at every commit.**
  - Until a round fragment names a new file, write its path or bare filename into none of the files
    gate 6 searches: `PROVENANCE.md`, `records/rounds/*.md` and `records/orders/*.md` (`INDEX.md`
    included). `CLAIMS.md`, `HANDOFF.md` and `ROADMAP.md` are not searched.
  - Show `check_records.py` FAIL on each new file with its import line in place. Then commit the
    module together with the fragment that names it: J2 step 3 creates round 21's fragment, step 4
    adds to it, and step 7 completes it; J3's first landing creates round 22's.
  - If gate 6 passes before the fragment exists, find the record that names the file. If that
    record is this order, rename the new file; never edit a filed order.
- **J3 is large.** Land it in the steps given, one commit each, so that a STOP still leaves proved
  mathematics behind.
- **Git, reviews and builds** as in order G-5 §1:
  - commit locally, never push to GitHub or add a remote, park and never delete;
  - reach DSMain only with `GIT_SSH_COMMAND='ssh -o BatchMode=yes -o ConnectTimeout=15'`; if DSMain
    is unreachable, record "unreachable" and carry on; never touch the VPN, routes or ssh
    configuration;
  - a fresh cold reviewer before and after proving; builds one at a time; subagents never run `lake`.

## 2. Standing answers — do not stop to ask these

- **Everything in `HANDOFF.md` §6's standing answers** still holds: the cache gap, the deprecation
  rule, the licence, `mem_closedSimplex`, the parked build, and the `[surname]` exception as landed,
  until J2 step 1 changes its Authors alternative.
- **The credit line.** Dustin said on 2026-09-23 that he wanted to credit Claude in the licence
  header, and chose otherwise only because of earlier advice. claude-ai's advice now: the copyright
  line stays Dustin's, and the Authors line credits Claude as a co-author. J2 step 1 applies it. If
  Dustin says "skip the credit" at plan approval, drop J2 step 1 and change nothing else.
- **The push record.** J1 compares `HANDOFF.md` §6 with `~/work/_bump-evidence/push.log` and the
  `dsmain/master` reflog, and reports any push §6 lacks. J2 step 6 adds the dated line.
- **Anything that needs Dustin:** ask in one line, recommended answer first, and keep working on
  whatever does not depend on it. Pushing, publishing and offering anything to Mathlib are his.

---

## J1 — open and re-measure (read-only)

**Goal.** Know that order G-5 is closed, and that the tree is what its records say, before touching
it.

**Scope.** Read-only. Run what plan mode allows. List the rest with predictions, marked "deferred".

**Measure, predicting each value first:**

1. `records/orders/INDEX.md` row `G-5`: its state, and what landed.
2. `lean-toolchain` and `lakefile.toml` `rev`: expect v4.34.0.
3. `git -C ~/work/classical-lean status --short`: expect nothing.
4. `git -C ~/work/classical-lean rev-parse master dsmain/master`, and
   `GIT_SSH_COMMAND='ssh -o BatchMode=yes -o ConnectTimeout=15' git -C ~/work/classical-lean ls-remote dsmain master`:
   expect `master` one commit ahead, and `dsmain/master` equal to `ls-remote`, or record
   "unreachable". Compare §6's push list with the last line of `push.log` and the reflog.
5. The six commands in `HANDOFF.md` §1, copied from it. Predict from its snapshot.
6. The number of files whose line 4 is exactly `Authors: Dustin [surname]`: expect 46.
7. The tools of §0 row 3, and where `g5_typediff.py` is.

**If order G-5 is not closed, STOP and report.**

**Done-means.** A predicted-beside-actual table in the chat, with every miss explained. Then one plan
for J2 and J3, and wait for approval.

**After approval, in this order:**

1. **Run the deferred commands.** STOP before J2 on any miss you cannot explain.
2. **File the order:**
   `mv -n ~/Cowork/lean-orders/20260923T233012Z__claude-ai__order-g6-connections-zsigmondy.md ~/work/classical-lean/records/orders/ && test ! -e ~/Cowork/lean-orders/20260923T233012Z__claude-ai__order-g6-connections-zsigmondy.md && test -f ~/work/classical-lean/records/orders/20260923T233012Z__claude-ai__order-g6-connections-zsigmondy.md`.
3. **Add the records rows, then commit exactly three paths:** the filed order,
   `records/orders/INDEX.md` and `records/CLAIMS.md`.
   - `INDEX.md`: a row for `G-6`, naming no new file (§1, gate 6).
   - `CLAIMS.md`: a row naming every module and `ClassicalLean.lean` (J2 step 1 touches all of
     them), `tools/banned_vocab_scan.py`, J2's and J3's new files (added before they are written),
     and the records paths: `HANDOFF.md`, `ROADMAP.md`, `RETIRED.md`, the round 21 and 22
     fragments, `CLAIMS.md` and `INDEX.md`.
4. **Take the "before" evidence on a clean tree:** `TypeDump.lean`, and the raw and filtered name
   lists, into `~/work/_bump-evidence/g6-before/`. J2 and J3 diff against these.

**Undo:** nothing to undo.

---

## J2 — the credit line, and the information-geometry connections

**Goal.** Credit Claude on the Authors line. Then prove the connections of §0 rows 4–6, so that
modules that never cited each other now do: `Simplex/Hessian` and `Simplex/FisherRao`,
`Simplex/LogSumExp` and `Simplex/FisherRao`, and `Statistics/GaussMarkov` and all of them.

**Scope.**
- Step 1: line 4 of the 46 files; one sentence of `ClassicalLean.lean`'s docstring; the
  `EXCEPTIONS` entry of `tools/banned_vocab_scan.py`, with one comment line above it.
- Steps 3 and 4: two new modules, suggested `ClassicalLean/Simplex/SecondOrder` and
  `ClassicalLean/Statistics/CramerRao`.
  - Naming, pre-answered: `HANDOFF.md` §5's "no eponyms" means the source corpus's names, and
    standard eponyms such as `GaussMarkov` are already module names here.
  - Each new module gets the header with the Authors line of step 1 (the old one if Dustin skipped
    the credit), one import line inside `ClassicalLean.lean`'s import block, a `CLAIMS.md` entry,
    a gate-6 FAIL check (§1), and an `import_closure.py` run with its positive control.
  - Existing modules may gain lemmas; none of their statements changes.
- `HANDOFF.md` §1, §3, §4, §5 and §6; `ROADMAP.md` §1 and §2; one dated line in `RETIRED.md`; records.

1. **The credit line — first, as its own commit.**
   - Replace line 4, `Authors: Dustin [surname]`, by `Authors: Dustin [surname], Claude (Anthropic)` in
     each of the 46 files. Use a script that asserts 46 exact matches on line 4 and nothing else.
     Mathlib's Authors-line check forbids double spaces, " and " and a final period; this line has
     none.
   - Change only the second alternative of the `[surname]` exception, keeping the `(?-i:…)` form and
     `[0-9]`: `Authors: Dustin [surname]` becomes `Authors: Dustin [surname], Claude \(Anthropic\)`. Add
     one comment line, a single line starting with `#`, above the entry:

```
    # 2026-09-23 (order G-6, J2 step 1): the Authors alternative also credits Claude (Anthropic).
```

   - Test the exception in place on `NumberTheory/Catalan.lean`, as round 19 did. Save a copy outside
     the repository, and restore and `cmp` after every run. Run it under the scanner's own compile
     flags (rule 8):
     - the new header passes;
     - the old Authors line fails;
     - the new line in lower case fails;
     - `Authors: Dustin [surname], Claude (Anthropic), X` fails;
     - `-- the [surname] theorem` fails.

     Put all five runs in the commit message.
   - Add one sentence to the end of `ClassicalLean.lean`'s module docstring, without the surname
     (gate 5 does not scan this file, so the ban is kept by hand here): "The Authors line credits
     Claude (Anthropic) alongside the copyright holder; how the library was written and ported is
     recorded in `PROVENANCE.md` and `records/`." Afterwards `grep -c [surname] ClassicalLean.lean`
     is 2 (lines 2 and 4).
   - Add one dated line each to `RETIRED.md`'s note on names, and to `HANDOFF.md` §4, §5 and §6: the
     two permitted lines are now the copyright line and the new Authors line.
   - Checks: `lake build` rc 0 with 0 warnings; `banned_vocab_scan.py` PASS with 0 hits; the type
     dump against J1's "before" evidence shows nothing removed, added or changed.
2. **Search first, and enumerate the junk cells first**, before steps 3 and 4.
   - Search Mathlib first (`HANDOFF.md` §3). Over `.lake/packages/mathlib/Mathlib`, re-run §0 row
     7's Mathlib commands, and add shape searches: `vecMulVec`, `PosSemidef.*diagonal`,
     `hasDerivAt.*exp.*div`, and G-5's `PosSemidef.*⁻¹`. Record every command and count.
   - Read every Mathlib definition you use before stating anything (§6, order 0923's rule 2).
   - Enumerate junk cells with random trials plus constructed cases (§6, order 0923's rule 3). At
     least these, constructed:
     - `p` with a zero coordinate, where `u / p` is junk;
     - `∑ u ≠ 0`;
     - `lam + kap = 1`, where `eta = 0`;
     - a singular `E[S Sᵀ]`: can the hypotheses of step 4 hold then?
3. **`Simplex/SecondOrder`: the Fisher–Rao metric is the Hessian of the negative entropy, and the
   covariance inverts it.**
   - **The chart matrix.** Define `fisherRaoChart lam kap`, the 2×2 matrix of §0 row 4, written with
     the same inverses as `Simplex/Hessian`'s `hess11`, `hess12` and `hess22`. Prove two things:
     - `fisherRao ![lam, kap, 1 - lam - kap] ![u₁, u₂, -u₁ - u₂] ![v₁, v₂, -v₁ - v₂] = ![u₁, u₂] ⬝ᵥ
       (fisherRaoChart lam kap *ᵥ ![v₁, v₂])`;
     - `hessian T lam kap = T • fisherRaoChart lam kap + !![(lam ^ 2)⁻¹, 0; 0, 0]`.

     Both are identities in the same inverses and need no positivity hypothesis, even at `0⁻¹ = 0`
     (checked by the reviewer). Afterwards `hessian_posDef` is the barrier plus `T` times a
     positive definite metric. Show that as an `example`, and do not restate it.
   - **The softmax Jacobian.** In `CrossEntropy`'s `Function.update` style, prove that the derivative
     of `softmax (Function.update x k t) i` at `t = x k` is `softmax x i * ((if i = k then 1 else 0)
     - softmax x k)`. That is the second derivative of `logSumExp`, since `hasDerivAt_logSumExp` is
     the first.
   - **The covariance.** Define `categoricalCov p := Matrix.diagonal p - Matrix.vecMulVec p p`, the
     covariance of a one-hot draw from `p`. Prove:
     - the derivative above is `categoricalCov (softmax x) i k`;
     - `categoricalCov p` is positive semidefinite when `0 ≤ p` and `∑ p = 1` (its quadratic form is
       a variance);
     - `categoricalCov p *ᵥ (fun _ => 1) = 0` when `∑ p = 1`;
     - **the inverse on the tangent space:** for `p` in `openSimplex` and `∑ u = 0`,
       `categoricalCov p *ᵥ (fun i => u i / p i) = u`;
     - in the chart, `fisherRaoChart lam kap * !![lam - lam ^ 2, -(lam * kap); -(lam * kap), kap -
       kap ^ 2] = 1` for `lam`, `kap` and `1 - lam - kap` positive.
4. **`Statistics/CramerRao`: the Cramér–Rao inequality on a finite outcome set, from Gauss–Markov.**
   - **The information inequality.** Over a finite type `Ω` with `[DecidableEq Ω]`, take weights `p`
     with `0 ≤ p ω`, a statistic `T : Matrix κ Ω ℝ` and scores `S : Matrix κ Ω ℝ`. Assume
     `∑ ω, p ω * (T i ω - E T i) * S j ω = if i = j then 1 else 0`. Then `Cov T - (E[S Sᵀ])⁻¹` is
     positive semidefinite, where `E T i = ∑ ω, p ω * T i ω`,
     `(Cov T) i j = ∑ ω, p ω * (T i ω - E T i) * (T j ω - E T j)` and
     `E[S Sᵀ] i j = ∑ ω, p ω * S i ω * S j ω`.
   - **State only the hypotheses the proof uses.** `∑ p = 1` and `E S = 0` are the probabilistic
     reading: with them the hypothesis says `E[T Sᵀ] = 1`, the derivative of unbiasedness. So they
     go in the docstring, and the categorical instance below proves both. Carried as hypotheses
     they would be unused, and the unused-variables linter fails the build over that (see
     `Simplex/CrossEntropy`'s docstring).
   - **The route** is §0 row 6. Apply `posSemidef_self_mul_transpose_sub_inv` to
     `C = (T - E T) * diagonal (√p)` and `X = diagonal (√p) * Sᵀ`. That makes it
     `Statistics/GaussMarkov`'s first consumer outside its own file.
   - **The equality case**, from `self_mul_transpose_eq_inv_iff`, needs `0 < p ω`: equality exactly
     when `T - E T = (E[S Sᵀ])⁻¹ * S`, the efficient statistic.
   - **The categorical family in P1's chart**, `p = ![lam, kap, 1 - lam - kap]` with all three
     positive:
     - its scores `S₁ ω = [ω = 0] / lam - [ω = 2] / eta` and `S₂ ω = [ω = 1] / kap - [ω = 2] / eta`,
       with `E S = 0`;
     - its Fisher information `E[S Sᵀ]` equals `fisherRaoChart lam kap`, which uses step 3;
     - the one-hot estimator `T ω = ![[ω = 0], [ω = 1]]` satisfies the hypothesis;
     - it **attains** the bound: its covariance is the inverse of `fisherRaoChart`, by step 3's
       chart identity.
   - A general `m`-outcome version is welcome if it costs little; the chart version is the
     Done-means.
5. **The records of the patterns.**
   - In `ROADMAP.md` §1, add one entry per pattern of §0 rows 4–6 and 9, with its hypotheses. Label
     each "proved, round 21" or "measured by claude-ai 2026-09-23, not proved".
   - Add a dated line to §1.5. P4 would join `Geometry/S3Quaternion` to `Simplex/FisherRao`: pulled
     back along the squaring map of `sqCoords`, the Fisher–Rao metric is 4 times the Euclidean one.
     Geometry already reaches Simplex through `sqCoords_mem_closedSimplex`, and neither link joins
     the corner to the number-theory half, which is what §1.5 asks for.
   - Add P6 and P7 to `HANDOFF.md` §3's candidates, with Mathlib's `Analysis/Convex/Birkhoff.lean`
     TODO named for P7.
6. **Move §1's eight rules into `HANDOFF.md` §6** as rules 8 to 15, each with its date and source.
   Retitle the list's lead-in to name both orders (0923: rules 1–7; G-5: rules 8–15). Add a dated
   line for any push J1 found missing (§2).
7. **Complete round 21's fragment**, per Rule 1.

**Done-means.**
1. The six gates pass on a clean tree, with 0 warnings and 0 vocabulary hits.
2. Step 1: 46 files carry the new Authors line. The five exception tests are in their commit
   message. The type dump against J1's evidence shows nothing removed, added or changed.
3. Steps 3 and 4: every new theorem is within the kernel trio. Both reviews, before and after
   proving, are quoted in round 21's fragment. The type dump against J1's evidence shows only
   additions.
4. Consumers:
   - `Statistics/CramerRao` uses `posSemidef_self_mul_transpose_sub_inv`;
   - the categorical instance uses `fisherRaoChart` and the chart identity;
   - `Simplex/SecondOrder` uses `hessian`, `fisherRao` and `softmax`.

   The fragment lists them.
5. The fragment carries the searches, the junk cells, the per-module counts and the import-closure
   results.

**Undo:** yes — `git revert`, one commit at a time.

---

## J3 — Zsigmondy's theorem for aⁿ − 1

**Goal.** The theorem that order G-5's close ranked first (`HANDOFF.md` §3, `ROADMAP.md` §2.5):

    for 2 ≤ a and every n:  (∃ p, IsPrimitiveDivisor p a n)  ↔
      ¬ ((a = 2 ∧ n = 1) ∨ (a = 2 ∧ n = 6) ∨ (n = 2 ∧ ∃ k, a + 1 = 2 ^ k))

- `IsPrimitiveDivisor` is `NumberTheory/PrimitiveDivisor`'s definition, which includes primality.
- At `n = 0` both sides hold: every prime divides `a⁰ − 1 = 0`, and the minimality clause is
  vacuous. So the statement carries no hypothesis on `n`.
- `2 ≤ a` is needed: at `a = 1`, `n = 3` the left side is false and the right side true.
- §0 row 8 checked the exceptional set numerically.

**Scope.**
- One new module, suggested `ClassicalLean/NumberTheory/Zsigmondy` (a standard eponym, not on the
  banned list). It gets the header, its import line, a `CLAIMS.md` entry, a gate-6 FAIL check (§1),
  and an `import_closure.py` run with its positive control.
- `NumberTheory/PrimitiveDivisor` may gain lemmas, and its "What is not here" text gets a dated line.
- `ROADMAP.md` §2.5, `HANDOFF.md` §3, records. Every other module is read-only.

**Method.**

1. **Search first.** Re-run `ROADMAP.md` §2.5's dated searches at v4.34.0. Read these before stating
   anything:
   - the cyclotomic bounds `sub_one_pow_totient_lt_cyclotomic_eval` (strict; needs `2 ≤ n` and
     `1 < q`) and `sub_one_pow_totient_lt_natAbs_cyclotomic_eval`;
   - lifting the exponent: `Nat.emultiplicity_pow_sub_pow` covers odd primes only, so the `p = 2`
     case (`n = 2ᵏ`, `k ≥ 2`) needs `Nat.two_pow_sub_pow`, or the fact that `Φ_{2ᵏ}(a) ≡ 2 (mod 4)`
     for odd `a`;
   - the largest prime factor `P(n)`: `Nat.maxPrimeFac` (`Data/Nat/MaxPrimeFac.lean`), whose junk
     values are `0 ↦ 0` and `1 ↦ 1`.
2. **The prior art** is Bakšys's Lean 3 branch (2022) and mathlib4 pull request #28895, closed
   unmerged.
   - If helios reaches `github.com`, fetch only the two proof files, with at most a few HTTPS
     requests each (a file listing, then the file), into `~/work/_bump-evidence/g6/prior-art/`. Do
     not clone either repository.
   - If it does not, record "unreachable" and cite `ROADMAP.md` §2.5's attributed facts.
   - Write the proofs here, and cite both as prior art. Adapting their code would mean keeping the
     source's copyright notice (Apache-2.0 §4), which the header's pinned copyright line cannot
     carry. Ask Dustin before adapting any.
3. **Junk cells first**, random plus constructed: `n = 0`, `a ∈ {0, 1}`, and `(a, n) = (2, 1)`, where
   `2¹ − 1 = 1` has no prime factor.
4. **Land in steps, one commit each:**
   1. `n = 1` and `n = 2`, which are elementary. For `n = 2`: `gcd (a − 1, a + 1) ∣ 2`, so a primitive
      divisor exists exactly when `a + 1` has an odd prime factor.
   2. **The three exceptions have no primitive divisor:**
      - `(2, 1)`: `1` has no prime factor;
      - `(2, 6)`: `63 = 3² · 7`, where `3 ∣ 2² − 1` and `7 ∣ 2³ − 1`;
      - `n = 2` with `a + 1 = 2 ^ k`: every prime divisor of `a² − 1` divides `a − 1`.
   3. **The key lemma, for `n ≥ 3`.** A prime dividing both `n` and `Φₙ(a)` is the largest prime
      factor `P(n)` of `n`, and divides `Φₙ(a)` exactly once. It fails at `n = 2`: `2²` divides
      `Φ₂(3) = 4`. A prime dividing `Φₙ(a)` but not `n` is primitive; that is
      `orderOf_eq_of_isRoot_cyclotomic`, already in `PrimitiveDivisor`.
   4. **Existence, and the `iff`, for `a ≥ 3`**: `(∃ p, IsPrimitiveDivisor p a n) ↔ ¬ (n = 2 ∧ ∃ k,
      a + 1 = 2 ^ k)`. For `n ≥ 3`, `Φₙ(a) > P(n)` follows from Mathlib's strict `(a − 1) ^ φ(n)`
      bound, because `φ(n) ≥ P(n) − 1` and `2 ^ (P − 1) ≥ P`.
   5. **Existence for `a = 2`, `n ≥ 3`, `n ≠ 6`.** This needs a new inequality, `Φₙ(2) > P(n)`, which is
      the known blocker. If it does not close this session, stop the `a = 2` existence there, keep
      steps 1–4, and record how far it got in `HANDOFF.md` §3.
   6. **The full `iff`**, from steps 1–5.

**Done-means.**
1. Every landed step passes the six gates with 0 warnings, and every theorem is within the kernel
   trio.
2. No `sorry` ships. A step that did not close stays out of the files and is described in
   `HANDOFF.md` §3.
3. Both reviews are quoted in round 22's fragment. The fragment carries the searches, the junk
   cells, the per-module count, the import-closure result and the prior-art citations.
4. `NumberTheory/PrimitiveDivisor` has its first consumer outside its own file.

**Undo:** yes — a new file and one import line; `git revert`.

---

## Close

1. **Refresh `HANDOFF.md`.**
   - §1: the snapshot from the six commands on a clean tree.
   - §3's "what next": re-rank with this order's results. The list:
     - Zsigmondy for `a = 2`, if J3 step 4.5 stopped;
     - the law of apparition (P6);
     - majorization (P7, Mathlib's TODO);
     - max-flow min-cut and Menger;
     - more statistics — the Frisch–Waugh–Lovell theorem (`docs/1000.yaml` Q1059151, no
       formalisation recorded), generalised least squares, Cochran;
     - Mathlib's wanted list.
2. Close the `CLAIMS.md` row and update the `INDEX.md` rows.
3. A fresh subagent checks every Done-means against `git diff <this order's first commit>^..master`.
   Record its verdict as an addendum to round 22.
4. **Ask Dustin, in one line:** "Push classical-lean master to DSMain? It moves from <old> to <new>."
   Push only on yes:
   `GIT_SSH_COMMAND='ssh -o BatchMode=yes -o ConnectTimeout=15' git -C ~/work/classical-lean push dsmain master`,
   fast-forward only, never `--force`. Then log the push in `push.log`. The next order records it
   in §6 (§2).
5. **The final chat report:** predicted beside actual, what landed with commit hashes, what stopped
   and why, and what comes next. Include:
   - the net change in theorem constants on the filtered list;
   - the top-level directories under `ClassicalLean/` (expect 10 before and 10 after);
   - one line each on any decision made on Dustin's delegation.

## Not in this order

- **G-4**: the number-theory track.
- **Publishing to GitHub, or offering anything to Mathlib**: Dustin's decisions.
- **Retiring any module**: Dustin's decision.
- **Proofs of P4–P7**: recorded in J2 step 5 only.
- **Information theory part 2 and the `klDiv` bridge**: declined in order G-5.
- **Anything in the lane on DSMain.**
