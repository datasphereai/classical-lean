# ORDER G-7 — bridges between the library's islands, then the law of apparition

Written 2026-09-24T02:35:00Z by claude-ai (Cowork, linked to helios) for one Claude Code session on
helios. Library: `~/work/classical-lean`. **Source of truth:** this file and `records/orders/INDEX.md`.
It waits in `~/Cowork/lean-orders/` until J1 files it, and starts only after order G-6 is closed.
A second agent reviewed it cold, twice, before it was placed there. The first pass found two
blockers and thirteen smaller points; the second confirmed those fixes and found one major and seven
minor points, which were applied without a third review.

It rests on three things:
- **Order G-6's close**: `HANDOFF.md` §3's ranking puts the law of apparition first; `ROADMAP.md`
  §1.14 records P4–P7 as measured, not proved.
- **claude-ai's measurements of the library at `cca6f8a`** (§0): a declaration-level graph of which
  module uses which, a duplicate-statement check against the whole environment, and a cross-match
  with Mathlib's `docs/1000.yaml`. They find six modules that use no other module and are used by
  none, and two statements proved twice in two modules.
- **The lessons of order G-6's run** (§1, rules 16–19). Its mathematics passed every gate. Its two
  Close-check failures were records: the statement reviews were paraphrased, not quoted, and their
  outputs had not been saved.

Three jobs, J1 to J3, then a close. Each has Goal / Scope / Done-means and an undo line. A STOP at a
gate is a report, not a close.

---

## 0. What claude-ai measured

Read-only, 2026-09-24 between 02:06Z and 03:10Z (drafted at 02:35Z, corrected after its review):
the helios tree at `cca6f8a`, run through the three scripts of Appendix A with `lake env lean` from
the repository root (no `lake build`, nothing written in the repository; `git status --porcelain`
empty before and after); a sparse clone of Mathlib v4.34.0 (`5ed2965256`); the order G-6 session's
page; exact checks in Python (`fractions`, sympy). Line numbers were read then; find each place by
its text.

| # | Fact | Value |
|---|---|---|
| 1 | Order G-6 | Closed (`INDEX.md`, `CLAIMS.md`). `master`, `dsmain/master` and `ls-remote dsmain master` are all `cca6f8a`. The push `59fa0d9..cca6f8a` is in `~/work/_bump-evidence/push.log`, marked "Dustin's yes 2026-09-24", and not yet in `HANDOFF.md` §6, by design (G-6's Close step 4). |
| 2 | The library | 48 modules in 10 top-level directories; 1225 theorem constants, filtered list 791 (round 22). 14,757 lines under `ClassicalLean/`. |
| 3 | Three orders, measured from git and the rounds | See the table after this one. |
| 4 | Declaration graph (`DeclGraph.lean`, then `islands.py`) | 1401 constants in 48 modules. **Six islands**, modules that use no other module's constant and whose constants no other module uses: `Combinatorics/AlgebraicGeneratingFunction`, `Geometry/Hopf`, `Geometry/SU2SO3`, `NumberTheory/Catalan`, `NumberTheory/CompositumDiscriminant`, `Order/Tolerance`. Used by no module, though they use others: `InformationTheory/Channel` and `NumberTheory/Zsigmondy`, among others. `NumberTheory/MersenneOrder` is used by one module, `MersenneFactorialPart`. The most used constant is `lucasU`: 33 constants in other modules name it. |
| 5 | Duplicates (`DupCheck.lean`) | 7 `TWIN` lines and 2 `SWAP` lines (each library pair prints twice, once from each side). **Two statements are proved twice**, in modules that do not import each other: `Geometry/Helix`'s `goldenRatio_sq_add_inv_eq_three` and `Simplex/DesignConstants`'s `goldenRatio_sq_add_inv_sq` (the same type, `φ² + (φ²)⁻¹ = 3`); `Geometry/Helix`'s `inv_goldenRatio_sq_eq_goldenConj_sq` and `Simplex/DesignConstants`'s `goldenConj_sq_eq_inv_goldenRatio_sq` (the same equation, sides swapped). No record names either pair. The other five `TWIN` lines are `GoldenRatio/Characterisations`'s labelled "Mathlib re-export"s (`vieta_sum`, `vieta_prod`, `fib_ratio_tendsto_goldenRatio`, `cos_pi_div_five_eq`, `cos_pi_div_five_quadratic_root`), which are deliberate. |
| 6 | P5, the Hopf map is an orbit | For every quaternion `q`, with `x := adjoint (star q) ⟨0, 1, 0, 0⟩` (`Geometry/SU2SO3`'s `adjoint q v = q * v * star q`, so `x = q̄ i q`): `hopfMap q = (x.imK, x.imJ, x.imI)` and `x.re = 0`. Symbolic (sympy), no unit hypothesis. |
| 7 | P4, the squaring map | For `x : ι → ℝ` with no zero coordinate: `fisherRao (fun i => x i ^ 2) (fun i => 2 * x i * v i) (fun i => 2 * x i * w i) = 4 * ∑ i, v i * w i` (symbolic). Under `0⁻¹ = 0` the left side drops every coordinate where `x i = 0`, so with a zero coordinate the identity can fail. `Geometry/S3Quaternion`'s `sqCoords q` is `![q.re ^ 2, q.imI ^ 2, q.imJ ^ 2, q.imK ^ 2]`, this map at the quaternion's coordinates. |
| 8 | P8, Fisher–Rao contracts under a channel | For `0 < p i` for all `i`, `0 ≤ W i j` and `∑ j, W i j = 1`: `fisherRao (p ᵥ* W) (u ᵥ* W) (u ᵥ* W) ≤ fisherRao p u u`. Exact rational check with Lean's `0⁻¹ = 0`: 6,000 trials, sizes 1–5, about 30% zero entries in `W`, `u` not constrained to sum to `0`: 0 failures, 1,348 equalities. Dropping positivity of one `p i` (with `u i` free): 1,630 failures. A negative entry in `W`: 571 failures. The reviewer found it also holds with `0 ≤ p i` and `p i = 0 → u i = 0`, and with row sums at most `1`. Route: Mathlib's `Finset.sq_sum_div_le_sum_sq_div` (Sedrakyan's lemma, `Algebra/Order/BigOperators/Ring/Finset.lean:181`) in each column, over the rows where `W i j ≠ 0` (the lemma needs `0 < g i` on its whole index set), then `Finset.sum_comm` and the row sums. |
| 9 | Zsigmondy for the order of 2 | For `n` in 1..120, a prime `p` with `orderOf (2 : ZMod p) = n` exists except exactly at `n = 1` and `n = 6` (sympy `n_order`). Junk cell: at `n = 0`, `p = 2` works, since `(2 : ZMod 2) = 0` and `orderOf 0 = 0`. A prime `p ∣ 2 ^ n - 1` with `p ≡ 1 (mod n)` exists for every `n ≥ 2`, `n = 6` included (`7 ∣ 63`): the reviewer checked `n = 2..39`. |
| 10 | P6, the law of apparition | For odd primes `p` and integers `P`, `Q`, with `D = P² − 4Q` and `(D/p)` the Legendre symbol (`0` when `p ∣ D`): `U_p ≡ (D/p)` and `V_p ≡ P (mod p)` in 43,245 cells (`P, Q ∈ [−15, 15]`, `Q = 0` included, `p < 200`), 0 failures. `p ∣ U_{p − (D/p)}` for odd `p ∤ Q`: 41,106 cells, 0 failures, 1,202 of them with `p ∣ D`. It fails when `p ∣ Q`: 296 of the 400 cells with `P, Q ∈ [−12, 12]`, `Q ≠ 0`, odd `p < 60` dividing `Q`. At `p = 2` the congruence for `U_p` still holds (Mathlib's `legendreSym 2 a` is `1` for odd `a`; the reviewer: 961 cells), and the law fails (256 of 496 cells). Fibonacci: `p ∣ F_{p−1}` for `p ≡ ±1 (mod 5)` and `p ∣ F_{p+1}` for `p ≡ ±2 (mod 5)`, every prime below 5000 including 2 and 3: 0 failures; `5 ∣ F_5`. |
| 11 | Mathlib v4.34.0 searches (commands below) | `apparition` 0; `fib` on a line with `ZMod`, `legendre`, `ModEq`, `orderOf` or `minimalPeriod` 0; `legendreSym` with `lucas`, `dickson` or `fib` 0; `fisher` 0; `hopf.?(map\|fibration)` 0. Present: `legendreSym.eq_pow` (Euler's criterion, `NumberTheory/LegendreSymbol/Basic.lean:116`), `legendreSym.quadratic_reciprocity_one_mod_four` (`QuadraticReciprocity.lean:133`), `ZMod.pow_card` (`FieldTheory/Finite/Basic.lean:588`). |
| 12 | `docs/1000.yaml` at v4.34.0 | Of 1199 entries, 955 carry no `decl`, `decls` or `url`. Among them: Q8074796 Zsigmondy's theorem (its statement is for `aⁿ − bⁿ`; the library proves `b = 1`), Q428134 Gauss–Markov (the library proves the matrix form, round 20), Q1059151 FWL, Q599876 Cochran, Q3889376 Carmichael's theorem, Q230848 Lamé's theorem, Q608294 max-flow min-cut, Q928813 Menger, Q579515 Rao–Blackwell. Q7686760 "Bang's theorem" is Wikidata's "Tarski's plank problem" (Bang's plank theorem), not the `b = 1` case of Zsigmondy's theorem, so the library does not claim it. Listing anything there needs a public URL: Dustin's decision. |
| 13 | Order G-6's run, from its page and evidence (UTC) | J2's statement reviews returned at 01:04–01:05, after its proofs compiled (01:00 and 01:02–01:03, round 21's addendum). J3's review was dispatched 01:11:42 and returned 01:20:14, after `ZsigmondyWork.lean` (01:18:51). J3's Mathlib searches were re-run at 01:19:28, after the proof file; the research workflow had searched at 00:30. J3's six step commits were cut from the finished module by a generator (`make_step.sh`, 01:32); round 22 says so at its head. The base-2 route came from the research notes (`j3-research-notes.md`), and the post-proof review found it is the prior art's route. The local guard refused inline Python twice and blocked a heredoc commit message containing `*`; the session then wrote every message to a file. |

Row 3, the three orders. "Wall clock" runs from the order's filing commit to its closing commit,
UTC; "commits" is `git rev-list --count <filing commit>^..<closing commit>`.

| Order | Wall clock | Commits | Modules | Lines under `ClassicalLean/` | Filtered list | Close check | Dustin's decisions |
|---|---|---|---|---|---|---|---|
| 0923 | 09-23 14:09–17:12 (includes a STOP) | 18 | 41 → 44 | 12,446 → 13,069 | → 725 (round 17) | every checkable item met, after findings | the STOP (delegated to claude-ai), the push |
| G-5 | 09-23 18:54–20:34 | 12 | 44 → 45 | → 13,619 | 725 → 746 | every checkable item met, after an evidence-log finding | the plan, the push |
| G-6 | 09-24 00:49–02:04 (J1 from 00:12) | 14 | 45 → 48 | → 14,757 | 746 → 791 | 41 held, 2 failed (records), both remedied | the plan with the credit, the push |

G-6's final report says "15 commits, `42cceb4` to `cca6f8a`"; the count is 14. Its push carried 15,
since `e115720` (order G-5's push line) went with it.

Row 11's searches, from the Mathlib clone's root:

```
grep -rniE 'apparition' Mathlib --include=*.lean | wc -l                                        # 0
grep -rnE 'fib' Mathlib --include=*.lean | grep -ciE 'zmod|legendre|modeq|orderOf|minimalPeriod' # 0
grep -rniE 'legendreSym.*(lucas|dickson|fib)|(lucas|dickson|fib).*legendreSym' Mathlib --include=*.lean | wc -l  # 0
grep -rniE 'fisher' Mathlib --include=*.lean | wc -l                                            # 0
grep -rniE 'hopf.?(map|fibration)' Mathlib --include=*.lean | wc -l                             # 0
```

**Predict J1 from `HANDOFF.md` §1 and §6, `records/orders/INDEX.md`, `records/CLAIMS.md` and
`push.log`, not from this table** — except J1 item 6, which re-runs Appendix A and predicts from rows
4 and 5. §6 lags the last push by design, so `push.log` predicts item 4.

---

## 1. Rules for this session

- **`HANDOFF.md` §6 holds**: rules 1–15 and the standing answers, with §0, §3, §4 and §5, and
  README Rules 1 to 4. They are not repeated here.
- **Dustin does not read code or files.** Everything he needs goes in your chat reply. When he must
  act, give the exact command, the box, and the output you expect.
- **Predict, then measure.** Write the expected value, or "no prediction", before any command that
  prints a count, a hash or an rc. Report predicted beside actual.
- **Run every command from `~/work/classical-lean`**, or give `git -C` and absolute paths.
- **Four rules learned in order G-6's run** (§0 row 13, rounds 21 and 22, the Close check),
  numbered as J2 step 7 will file them in `HANDOFF.md` §6. In this order "rule N" means `HANDOFF.md`
  §6's rule N, 1–19; `records/README.md`'s rules are written "README Rule N".
  16. **A statement review's verdict is in before any proof of those statements is written.**
     Research, other jobs' drafting, and gate runs may overlap a review; proofs of the statements
     under review may not.
  17. **Every reviewer and checker output is saved verbatim, with its sha256, in the order's
     evidence directory when it returns.** Fragments quote from the saved file.
  18. **Records follow the clock.** When a step runs out of the order's sequence, or overlaps
     another (a search re-run after the proof, step commits cut from a finished module, proving
     while a review runs), the fragment says so at that step, with times.
  19. **Research notes name the source of every proof route they propose**: derived here, a textbook
     with its reference, or a prior-art file. The module docstring's credit can then be exact.
- **Environment facts, measured in order G-6's run:** write every commit message to a file and
  commit with `git commit -F <file>`; the local guard blocks a heredoc message that contains `*`.
  Write scripts to files in the evidence directory and run them; the guard refuses inline
  `python3 -c` and chained in-place edits.
- **Steps and commits.** Land a step as its own commit when it was proved as a step. If a module is
  proved whole before its first landing, land it in one commit and record its step structure in
  the fragment (rule 18); do not cut step commits from a finished file.
- **Gate 6.** J2 creates no module file. If J3 creates one, the rules of order G-6 §1 apply to it:
  until a round fragment names the new file, write its path or bare filename into none of the files
  gate 6 searches (`PROVENANCE.md`, `records/rounds/*.md`, `records/orders/*.md`, `INDEX.md`
  included); show `check_records.py` FAIL on it with its import line in place; then commit it
  together with the fragment that names it.
- **Git, reviews and builds** as in order G-5 §1:
  - commit locally, never push to GitHub or add a remote, park and never delete;
  - reach DSMain only with `GIT_SSH_COMMAND='ssh -o BatchMode=yes -o ConnectTimeout=15'`; if DSMain
    is unreachable, record "unreachable" and carry on; never touch the VPN, routes or ssh
    configuration;
  - a fresh cold reviewer before and after proving; builds one at a time; subagents never run `lake`.

## 2. Standing answers — do not stop to ask these

- **Everything in `HANDOFF.md` §6's standing answers** still holds, the `[surname]` exception as landed
  in order G-6 included.
- **The push record.** J1 compares `HANDOFF.md` §6 with `push.log` and the `dsmain/master` reflog.
  J2 step 7 adds the dated line for `59fa0d9..cca6f8a`, taken from `push.log`.
- **Where the bridges live** (J2), pre-answered; a different home is allowed if the plan says why
  and the import closure is recorded:
  - P5 in `Geometry/Hopf`, which gains `import ClassicalLean.Geometry.SU2SO3`;
  - P4's general identity in `Simplex/SecondOrder`, its quaternion instance in
    `Geometry/S3Quaternion`, which gains `import ClassicalLean.Simplex.SecondOrder`;
  - P8 in `Simplex/SecondOrder`, which gains `import ClassicalLean.InformationTheory.Channel`;
  - the order-of-2 theorems in `NumberTheory/Zsigmondy`, which needs no new import: it reaches
    `MersenneOrder` already, through `PrimitiveDivisor` and `LucasApparition`;
  - the two golden-ratio statements in `GoldenRatio/Characterisations`, which `Geometry/Helix` then
    imports (J2 step 6).
  None of these imports closes a cycle: at `cca6f8a` no imported module reaches the module that
  imports it, directly or through others. J1 checks it (item 7).
- **The duplicates are resolved by claude-ai's ruling**, as order G-5 §2 ruled on
  `mem_closedSimplex`: one statement, one name, one home (J2 step 6). The plan states it; Dustin's
  approval of the plan covers it, and his veto stays open.
- **The vocabulary step is Dustin's.** J2 step V runs only if he answers yes to the plan's
  vocabulary question (J1 Done-means). Otherwise skip it and change nothing in
  `tools/banned_vocab_scan.py`.
- **Anything that needs Dustin:** ask in one line, recommended answer first, and keep working on
  whatever does not depend on it. Pushing, publishing, listing anything in Mathlib's `docs/1000.yaml`
  and offering anything to Mathlib are his.

---

## J1 — open and re-measure (read-only)

**Goal.** Know that order G-6 is closed and that the tree is what its records say, before touching
it.

**Scope.** Read-only in the repository. Write only under `~/work/_bump-evidence/` (`g7/` and, after
approval, `g7-before/`). Run what plan mode allows. List the rest with predictions, marked "deferred".

**Measure, predicting each value first:**

1. `records/orders/INDEX.md` row `G-6`: its state, and what landed. `CLAIMS.md`: no open row.
2. `lean-toolchain` and `lakefile.toml` `rev`: expect v4.34.0.
3. `git -C ~/work/classical-lean status --short`: expect nothing.
4. `git -C ~/work/classical-lean rev-parse master dsmain/master`, and
   `GIT_SSH_COMMAND='ssh -o BatchMode=yes -o ConnectTimeout=15' git -C ~/work/classical-lean ls-remote dsmain master`:
   predict from `push.log`'s last push line, or record "unreachable". Compare §6's push list with
   `push.log` and the reflog, and name every push §6 lacks.
5. The six commands in `HANDOFF.md` §1, copied from it. Predict from its snapshot.
6. **Appendix A.** Write its three files into `~/work/_bump-evidence/g7/claude-ai/`, check each
   sha256 against the appendix, and run them as their headers say. Predict from §0 rows 4 and 5:
   1401 constants, 48 modules, 6 islands by name; `DupCheck: 7 TWIN line(s), 2 SWAP line(s)`.
7. **The import checks of §2** (J2 steps 2–4 and 6). For each proposed import `A` gains `B`, list
   `B`'s transitive `ClassicalLean` imports and confirm `A` is not among them. Also confirm that
   `Zsigmondy` already reaches `MersenneOrder`.
8. The number of files under `ClassicalLean/` and `ClassicalLean.lean` whose line 4 is exactly
   `Authors: Dustin [surname], Claude (Anthropic)`: expect 49.

**If order G-6 is not closed, STOP and report.**

**Done-means.** A predicted-beside-actual table in the chat, with every miss explained. Then one plan
for J2 and J3, and wait for approval. The plan ends with Dustin's two decisions, each in one line,
recommended answer first:
- "Recommended: yes — approve this plan."
- "Recommended: yes — also let the vocabulary gate scan `ClassicalLean.lean`, stop exempting lines
  that mention 'retired', make each exception forgive only its own word, and allow
  'unconscious statistician'." A yes here approves J2 step V.

**After approval, in this order:**

1. **Run the deferred commands.** STOP before J2 on any miss you cannot explain.
2. **File the order:**
   `mv -n ~/Cowork/lean-orders/20260924T023500Z__claude-ai__order-g7-bridges-apparition.md ~/work/classical-lean/records/orders/ && test ! -e ~/Cowork/lean-orders/20260924T023500Z__claude-ai__order-g7-bridges-apparition.md && test -f ~/work/classical-lean/records/orders/20260924T023500Z__claude-ai__order-g7-bridges-apparition.md`.
3. **Add the records rows, then commit exactly three paths:** the filed order,
   `records/orders/INDEX.md` and `records/CLAIMS.md`.
   - `INDEX.md`: a row for `G-7`, naming no new file.
   - `CLAIMS.md`: a row naming the modules J2 edits (§2's homes, `Geometry/Helix`,
     `Simplex/DesignConstants`, and any module that uses a name step 6 moves); `ClassicalLean.lean`
     (step V, or J3's import line if J3 creates a module); `tools/banned_vocab_scan.py` and
     `RETIRED.md` if Dustin approved step V; J3's module; and the records paths: `HANDOFF.md`,
     `ROADMAP.md`, the round 23 and 24 fragments, `CLAIMS.md` and `INDEX.md`.
4. **Take the "before" evidence on a clean tree** into `~/work/_bump-evidence/g7-before/`:
   `TypeDump.lean`, the raw and filtered name lists, and item 6's three outputs. J2 and J3 diff
   against these.

**Undo:** nothing to undo.

---

## J2 — bridges between the islands

**Goal.** Join modules that share mathematics and never use each other, each join a theorem someone
would cite; and remove the two duplicated statements. Measured by Appendix A: islands 6 → 4 (`Hopf`
and `SU2SO3` leave the list), `Channel` and `MersenneOrder` gain a user, and `DupCheck` prints
5 `TWIN` lines and 0 `SWAP` lines.

**Scope.**
- Existing modules only: §2's homes, `Geometry/Helix` and `Simplex/DesignConstants`, and any module
  that uses a name step 6 moves. Existing modules gain lemmas and at most one import line each;
  outside step 6, no existing statement changes, and an existing proof may change only where a step
  says so.
- If Dustin approved it, step V: `tools/banned_vocab_scan.py`, one dated line in `RETIRED.md`, and
  dated lines in `HANDOFF.md` §4 and §5.
- `HANDOFF.md` §3 and §6, `ROADMAP.md` §1, records. Round 23's fragment opens with the first J2
  commit.

1. **Search first, and enumerate the junk cells first**, before any statement is written.
   - Re-run §0 row 11's commands over `.lake/packages/mathlib/Mathlib`, and add shape searches for
     each statement below (for P8 at least `sq_sum_div_le_sum_sq_div`, `inner_mul_le_norm_mul_norm`
     and `vecMul`; for P5 `q \* .* \* star q` and `imK`). Record every command and count.
   - Read every Mathlib and library definition you use before stating anything (rule 2).
   - Junk cells, random plus constructed (rule 3): a zero `p i`, a zero entry and a zero column of
     `W` for P8; a
     zero coordinate of `x` for P4; `q = 0` for P5; `n ∈ {0, 1, 6}` for step 5.
   - Draft every J2 statement, then send the list to one cold statement review. Its verdict is in
     before any J2 proof is written (rule 16).
   - State each theorem with the weakest hypotheses the proof allows, as `Simplex/SecondOrder`'s
     docstring asks; §0 records weaker forms that hold.
2. **P5 — the Hopf map is the orbit of `i` under the rotation action** (`Geometry/Hopf`).
   - State §0 row 6 for every quaternion: `hopfMap q` is `(x.imK, x.imJ, x.imI)` for
     `x = adjoint (star q) ⟨0, 1, 0, 0⟩`, and `x.re = 0`.
   - **Consumer:** re-prove `hopfMap_sq_add` from `SU2SO3`'s `adjoint_normSq` (and `adjoint_re`),
     keeping its statement. The type dump must show it unchanged.
3. **P4 — the squaring map pulls the Fisher–Rao metric back to four times the Euclidean one.**
   - In `Simplex/SecondOrder`: §0 row 7's identity, for `x` with no zero coordinate.
   - In `Geometry/S3Quaternion`: its instance at the quaternion's four coordinates, so that
     `sqCoords` is the squaring map. Name how the four coordinates are written.
4. **P8 — the Fisher–Rao metric contracts under every stochastic matrix** (`Simplex/SecondOrder`).
   - State §0 row 8 in the weakest form the proof allows (row 8 records forms that hold), and
     recover `InformationTheory/Channel`'s form (`0 ≤ W i j`, `∑ j, W i j = 1`, `0 < p i`) by an
     `example`, as `Simplex/SecondOrder` already does for its own statements. The inequality in
     either form is the Done-means.
   - Use at least one of `Channel`'s declarations where the proof needs it, so that `Channel` has a
     user: `vecMul_nonneg` fits either form; `sum_vecMul_eq_sum` needs row sums equal to `1`.
   - The docstring gives the statistical reading: garbling an observation cannot increase its
     Fisher information. It is the second-order companion of `Channel`'s `relEntropy_vecMul_le`.
     An equality case is welcome if it costs little; the inequality is the Done-means.
5. **Every `n` except 1 and 6 is the order of 2 modulo some prime** (`NumberTheory/Zsigmondy`).
   - `(∃ p, p.Prime ∧ orderOf (2 : ZMod p) = n) ↔ n ≠ 1 ∧ n ≠ 6`, for every `n`. Check the junk
     cell at `n = 0` (§0 row 9) before stating; if it does not hold as §0 says, state the existence
     for `2 ≤ n` instead and record why.
   - Its corollary: for every `2 ≤ n`, some prime `p` divides `2 ^ n - 1` with `p ≡ 1 [MOD n]`. At
     `n = 6`, where the iff has no prime, `7` is the witness (§0 row 9).
   - Use `MersenneOrder`'s `dvd_mersenne_iff_orderOf_dvd` where the proof needs it, so that
     `MersenneOrder` gains a user. `Zsigmondy` stays unused by other modules; that is expected.
6. **The two duplicated statements** (§0 row 5).
   - Keep `Geometry/Helix`'s two, moved into `GoldenRatio/Characterisations` as
     `ClassicalLean.GoldenRatio.goldenRatio_sq_add_inv_eq_three` and
     `ClassicalLean.GoldenRatio.inv_goldenRatio_sq_eq_goldenConj_sq`. `Geometry/Helix` imports
     `GoldenRatio/Characterisations` and uses them.
   - Delete `Simplex/DesignConstants`' two copies, `goldenRatio_sq_add_inv_sq` and
     `goldenConj_sq_eq_inv_goldenRatio_sq`. The reviewer found no use of either outside their own
     lines; re-check that before deleting. `DesignConstants` then needs no new import.
   - Add one dated line to each affected module's header where it records the source name it
     shipped (for example `Geometry/Helix`'s "shipped as `goldenRatio_sq_add_inv_eq_three`").
   - The type dump shows exactly the 4 removed names (two in `ClassicalLean.Geometry`, two in
     `ClassicalLean.Simplex`), the 2 added names and nothing changed. If the move needs more than
     these declarations and their direct uses, STOP the step, keep steps 2–5, and record how far it
     got in `HANDOFF.md` §3.
7. **Records** (after steps 2–6 have landed).
   - `HANDOFF.md` §6: §1's rules 16–19, each with its date and source; the lead-in
     names three orders (0923: 1–7; G-5: 8–15; G-6: 16–19). The environment facts of §1 become one
     standing answer. The dated push line of §2.
   - `ROADMAP.md` §1: a new §1.15 with the island list before and after, the duplicates and their
     resolution, P8 with its hypotheses, and §0 row 12's overlap with `docs/1000.yaml`. Mark P4
     and P5 in §1.14 "proved, round 23". One dated line in §1.5, and one in §1.7 (the golden ratio's
     two treatments now share two statements).
   - Those two dated lines also correct what is stale there. §1.7: "No `NumberTheory` module imports
     it" (`NumberTheory/LucasSequenceCases` does, its line 13) and "imported by exactly two
     modules" (three at `cca6f8a`, four after step 6). §1.5: "`Simplex/DesignConstants.lean` and
     `Simplex/Involution.lean` import `GoldenRatio/Characterisations.lean`" (`DesignConstants` does
     not; `Simplex/FisherRao` does) and "`Geometry/Helix.lean` uses `Real.goldenRatio`" (after step
     6 it also imports `GoldenRatio/Characterisations`). Measure each with `grep` before writing.
   - `HANDOFF.md` §3: add Carmichael's theorem (Q3889376; it needs J3) and Lamé's theorem
     (Q230848). The FWL theorem is already listed there.
   - Complete round 23's fragment (README Rule 1).

**Step V — only if Dustin answered yes to the vocabulary question.** Run it after step 6 and before
step 7, as its own commit. Four changes to `tools/banned_vocab_scan.py`, each tested under the
scanner's own compile flags (rule 15), in place on a module saved outside the repository and
restored with `cmp` after every run, as round 21 did:
- **Scan `ClassicalLean.lean` too.** Today its docstring is outside gate 5 (order G-6 J2 step 1:
  "gate 5 does not scan this file").
- **Remove the audit-marker allowlist.** The scanner reads only `.lean` files, so it never sees
  `RETIRED.md` or `PROVENANCE.md`, and inside its scope the allowlist only hides lines: four today
  (`Order/Tolerance.lean` lines 53 and 55, `Simplex/Ordered.lean` line 36, `ClassicalLean.lean` line
  75), none carrying a banned term. Delete `AUDIT_MARKERS` and rewrite the three passages that
  describe it (the module docstring's paragraph on audit markers, its Scope paragraph, and the
  comment above `AUDIT_MARKERS`).
- **An exception forgives only its own term, and only inside its context.** Today a line is
  forgiven every term if any exception's term and context both match it
  (`any(tp.search(line) and cp.search(line) …)` in `main`), so an unanchored exception would also
  forgive other banned words, or a second use of its own word, on its line. Check every match of
  the term on the line (`finditer`, not `search`, which finds only the first), and forgive a match
  only when its span lies inside a match of its own exception's context. The `[surname]` exception is
  anchored to whole lines, so it is unaffected.
- **One exception:** `(r"[retired term]", r"unconscious statistician")`, so that the law of the
  unconscious statistician can be named (Mathlib names it, `Probability/Density.lean:38`). Nothing
  else on the list changes.
- Tests, each predicted first: a planted `-- [retired term], retired` line FAILS (it passed before);
  a planted `-- [retired term]` line in `ClassicalLean.lean` FAILS (it passed before); a docstring line
  `Law of the unconscious statistician` PASSES (it failed before); a line with both
  `unconscious statistician` and `[retired term]` FAILS; `-- a [retired term] choice by the
  unconscious statistician` FAILS; `-- the unconscious statistician, then a [retired term] choice` FAILS (it passes
  under a first-match check); `-- a [retired term] choice` FAILS (unchanged); the full scan on the landed
  tree PASSES with 0 hits.
- **Records of the change:** one dated line each in `RETIRED.md`'s note on names (it says the
  scanner permits the eponym "outside audit-marked lines (one `EXCEPTIONS` entry)") and in
  `HANDOFF.md` §4 ("An audit-marker allowlist lets `RETIRED.md` name what it retires") and §5
  ("outside audit-marked lines"); the §6 standing answer on the eponym gains one dated sentence.

**Done-means.**
1. The six gates pass on a clean tree, with 0 warnings and 0 vocabulary hits.
2. Every new theorem is within the kernel trio. The statement review (before proving) and the
   post-proof review are saved (rule 17) and quoted in round 23's fragment.
3. The type dump against J1's evidence shows only additions, except step 6's exact list.
4. Appendix A on the landed tree: islands 4 (`AlgebraicGeneratingFunction`, `Catalan`,
   `CompositumDiscriminant`, `Tolerance`); `Channel`, `SU2SO3` and `MersenneOrder` each used by at
   least one more module than at `cca6f8a`; `DupCheck: 5 TWIN line(s), 0 SWAP line(s)`.
5. The fragment carries the searches, the junk cells, the per-module counts, the import-closure
   results for every module that gained an import, and, if step V ran, its eight tests.

**Undo:** yes — `git revert`, one commit at a time.

---

## J3 — the law of apparition

**Goal.** The half of the classical theory (Lucas, 1878) that `NumberTheory/LucasApparition`'s
docstring records as not proved ("The bound `α(p) ∣ p - (D/p)` is **not** proved"), and the pattern
`HANDOFF.md` §3 ranks first. With `D = P ^ 2 - 4 * Q` over `ℤ`, and `legendreSym` Mathlib's:

1. **The two congruences at a prime index.** For every prime `p` and all `P Q : ℤ`:
   `lucasU P Q p ≡ legendreSym p D [ZMOD p]` and `lucasV P Q p ≡ P [ZMOD p]`. Handle `p = 2`
   directly: `U 2 = P`, and Mathlib's `legendreSym 2 D` is `1` for odd `D` and `0` for even `D`,
   so both sides are `P` mod 2 (§0 row 10).
2. **The law of apparition.** For an odd prime `p` with `¬ (p : ℤ) ∣ Q`:
   `(p : ℤ) ∣ lucasU P Q ((p : ℤ) - legendreSym p D).toNat`.
3. **In `LucasApparition`'s terms:** for an odd prime `p` with `¬ (p : ℤ) ∣ Q`, the rank of
   apparition of `(P, Q)` over `ZMod p` divides `((p : ℤ) - legendreSym p D).toNat`, from item 2
   and the module's `prime_dvd_lucasU_iff` or `lucasU_eq_zero_iff_apparition_dvd`. Keep
   `¬ (p : ℤ) ∣ Q` here even if item 2 is weakened: when `p` divides both `P` and `Q` the rank is
   `2` and the index `p` is odd (the reviewer: 136 of 136 such cells fail).
4. **Fibonacci.** For a prime `p`: `p % 5 = 1 ∨ p % 5 = 4 → p ∣ Nat.fib (p - 1)`, and
   `p % 5 = 2 ∨ p % 5 = 3 → p ∣ Nat.fib (p + 1)`, the classical Fibonacci case. Through
   `LucasSequenceCases`'s `lucasU_one_neg_one` and quadratic reciprocity for `5 ≡ 1 (mod 4)`.
   `p = 2` falls in the second case (`2 ∣ F_3`); state `5 ∣ Nat.fib 5` as an `example`.

- §0 row 10 checked all four, and the hypotheses: item 2 fails when `p ∣ Q`, and at `p = 2`. The
  reviewer found item 2 holds again when `p` divides both `P` and `Q` (136 cells, 0 failures); item 3
  does not. State the weakest hypotheses the proof allows.
- Names are suggestions for the statement review; Mathlib's naming conventions decide.

**Scope.** `NumberTheory/LucasApparition` (preferred: its docstring records the gap), or a new module
if the imports get heavy, suggested `ClassicalLean/NumberTheory/LawOfApparition`; then §1's gate-6
rules apply, with a `CLAIMS.md` entry, the header with the current Authors line, one import line in
`ClassicalLean.lean`, and an `import_closure.py` run with its positive control.
`LucasApparition`'s "What is not here" gets a dated line saying where the bound is proved.
`ROADMAP.md` §2's item 2.1 (the rank of apparition) gets a dated line. `HANDOFF.md` §3, records.
Every other module is read-only.

**Method.**
1. **Search first, recorded before any statement is drafted** (rule 18): re-run §0 row 11, add shape
   searches (`add_pow_char`, `Nat.Prime.dvd_choose_self`, `AdjoinRoot`, and whatever
   `LucasSequence` has for `2 * U (n + 1) = P * U n + V n`), and read `legendreSym`, `lucasU`,
   `lucasV` and `lucasU_of_roots` before stating anything.
2. **Junk cells first**: `p ∣ D` (index `p`); `p ∣ Q` (false, and why); `p = 2`; `P = 0`; negative
   `Q`; `(p - legendreSym p D).toNat` when the Legendre symbol is `1`, `-1` or `0`.
3. **Two routes are known**; choose one and record why, naming its sources (rule 19):
   - **Binomial.** `2 * (P + s) ^ n = 2 ^ n * (V n + U n * s)` in a ring with `s ^ 2 = D` (true
     at `n = 0` too), or
     the equivalent sums with binomial coefficients; at `n = p` the middle coefficients vanish mod
     `p`, Euler's criterion (`legendreSym.eq_pow`) gives `D ^ (p / 2) ≡ (D / p)`, and Fermat gives
     `P ^ p ≡ P` and `2 ^ (p - 1) ≡ 1`.
   - **Frobenius.** In a commutative ring of characteristic `p` holding `s` with `s ^ 2 = D`, for
     example `AdjoinRoot (X ^ 2 - C D)` over `ZMod p`, `add_pow_char` gives
     `(P + s) ^ p = P + s * D ^ (p / 2)`; `lucasU_of_roots` then reads off `U` and `V`.
   Either way, item 2 follows from item 1 through `2 * U (p + 1) = P * U p + V p` and
   `2 * Q * U (p - 1) = P * U p - V p`, with `2` and `Q` invertible mod `p`.
4. **Statement review before proving** (rule 16), then land. Commit per statement group if you prove
   per group; one commit if the module is proved whole first (§1).

**Done-means.**
1. Every landed commit passes the six gates with 0 warnings, and every theorem is within the kernel
   trio.
2. No `sorry` ships. An item that did not close stays out of the files and is described in
   `HANDOFF.md` §3.
3. Both reviews are saved and quoted in round 24's fragment. The fragment carries the searches, the
   junk cells, the chosen route and its sources, the per-module count, and, for a new module, the
   import-closure result.
4. `LucasApparition`'s "What is not here" carries a dated line naming where the bound is proved.

**Undo:** yes — `git revert`.

---

## Close

1. **Refresh `HANDOFF.md`.**
   - §1: the snapshot from the six commands on a clean tree.
   - §3's "what next", re-ranked with this order's results. The list: Zsigmondy for `aⁿ − bⁿ`
     (completes Q8074796's statement; the prior art's route, credited); Carmichael's theorem
     (Q3889376, after J3); majorization (Mathlib's TODO); the FWL theorem, then Cochran (Q1059151,
     Q599876); Lamé's theorem (Q230848); max-flow min-cut and Menger (Q608294, Q928813); Mathlib's
     wanted list.
2. Close the `CLAIMS.md` row and update the `INDEX.md` rows.
3. **The Close check.** Fresh subagents check every Done-means against
   `git diff <this order's first commit>^..master`. Save their outputs first (rule 17), then record
   the verdict, quoted, as an addendum to round 24.
4. **Ask Dustin, in one line:** "Recommended: yes — push classical-lean master to DSMain, a
   fast-forward from <old> to <new>." Push only on yes:
   `GIT_SSH_COMMAND='ssh -o BatchMode=yes -o ConnectTimeout=15' git -C ~/work/classical-lean push dsmain master`,
   fast-forward only, never `--force`. Then log the push in `push.log`. The next order records it in
   §6.
5. **The final chat report:** predicted beside actual, what landed with commit hashes, what stopped
   and why, what comes next, and:
   - the net change in theorem constants on the filtered list;
   - Appendix A's numbers before and after (islands, `TWIN` and `SWAP` lines);
   - this order's row for §0's three-order table, in the same columns;
   - one line each on any decision made on Dustin's delegation, and on any overlap rule 18 recorded.

## Not in this order

- **G-4**: the number-theory track.
- **Publishing, listing in `docs/1000.yaml`, or offering anything to Mathlib**: Dustin's decisions.
- **Retiring any module**: Dustin's decision. The four remaining islands are recorded, not bridged.
- **Zsigmondy for `aⁿ − bⁿ`, Carmichael, majorization, FWL**: ranked for the next order.
- **Any other change to the banned-vocabulary list**: step V is the whole of it.
- **Anything in the lane on DSMain.**

---

## Appendix A — claude-ai's three evidence scripts

Write each into `~/work/_bump-evidence/g7/claude-ai/` byte for byte (the text between the fences,
ending with one newline), and check its sha256 before running it:

```
a120cee455d000e78a7a60ad6cff1b93d9c1a6e15abaccf13e83a6dd95e8b3e0  DeclGraph.lean
9687c7ff6a81312c2aa9ccabbf380514ceffa479d63ade5afba2584f188c53e9  DupCheck.lean
f9aff2c78593cff456ab3e0970d3747cbaac32763aa53a03ed879c6395ec0404  islands.py
```

Run, from `~/work/classical-lean`:

```
lake env lean ~/work/_bump-evidence/g7/claude-ai/DeclGraph.lean > ~/work/_bump-evidence/g7/claude-ai/declgraph.jsonl
python3 ~/work/_bump-evidence/g7/claude-ai/islands.py ~/work/_bump-evidence/g7/claude-ai/declgraph.jsonl
lake env lean ~/work/_bump-evidence/g7/claude-ai/DupCheck.lean
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
