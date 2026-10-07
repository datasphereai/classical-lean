# Round 18 — finite information theory: entropy, relative entropy, mutual information, channels

Session: Claude Code `session_01A172nPt1wcsnUPA6SyKERL` on helios, executing order `0923`
(`records/orders/20260923T122713Z__claude-ai__order-0923-pick-up.md`), job J4. J3 (the toolchain
move) had stopped, so J4 ran on the current pin, Lean `v4.29.0-rc2` / Mathlib `8f07524533`, as the
order's J3 STOP paragraph directs (section "J3 status" below).

Commit (added in a follow-up edit, records/README.md Rule 1): **`3e600b2`**. Preceded by `668183e`,
which named these three files in `records/CLAIMS.md` before any of them existed.

## Modules

Added:

* `ClassicalLean/InformationTheory/Entropy.lean`
* `ClassicalLean/InformationTheory/MutualInformation.lean`
* `ClassicalLean/InformationTheory/Channel.lean`

Changed: `ClassicalLean/Simplex/FisherRao.lean` — the one edit order 0923 allows: its
`shannonEntropy` definition moved to `InformationTheory/Entropy.lean`, keeping the full name
`ClassicalLean.Simplex.shannonEntropy` and a byte-identical statement and body, and the module
gained `import ClassicalLean.InformationTheory.Entropy`. No other line of it changed; its
statements that name `shannonEntropy` are untouched. `ClassicalLean.lean` gained one import per
new module.

## What each module states

All declarations are in `namespace ClassicalLean.Simplex` (the moved definition had to keep that
name; the choice also keeps clear of Mathlib's `InformationTheory` namespace).

* **Entropy** — `shannonEntropy` (moved), `relEntropy p q = ∑ p i * log (p i / q i)`;
  `sum_sub_sum_le_relEntropy`, `mul_log_le_relEntropy` (log-sum), `relEntropy_nonneg`,
  `relEntropy_eq_zero_iff`, `relEntropy_uniform`, `shannonEntropy_le_log_card`,
  `shannonEntropy_eq_log_card_iff`, `relEntropy_softmax`.
* **MutualInformation** — `mutualInfo` (relative entropy to the product of the marginals);
  `mutualInfo_nonneg`, `mutualInfo_eq_zero_iff` (zero exactly at `P (a, b) = r a * s b`),
  `mutualInfo_eq_shannonEntropy_add_shannonEntropy_sub_shannonEntropy`,
  `shannonEntropy_le_shannonEntropy_add_shannonEntropy` (subadditivity).
* **Channel** — `sum_vecMul_eq_sum`, `vecMul_nonneg`, `relEntropy_vecMul_le` (the
  data-processing inequality), `shannonEntropy_le_shannonEntropy_vecMul` (entropy under a doubly
  stochastic matrix).

Every hypothesis is explicit (`0 ≤ p i`, `∑ p = 1`, `q i = 0 → p i = 0`, a channel's row sums),
none is `stdSimplex` — deprecated at Mathlib v4.34.0.

## Per-module theorem-constant counts

`~/work/_bump-evidence/ModuleThmCount.lean` (AxiomGate's `.thmInfo` predicate, owning module from
`env.getModuleFor?`), run on the working tree before this round's commit; the total equals
AxiomGate's own count on the same tree.

| module | theorem constants |
|---|---|
| `ClassicalLean/InformationTheory/Entropy.lean` | 29 — 8 public and 4 private theorems, 15 `_simp_` auxiliaries, `relEntropy.eq_1`, `shannonEntropy.eq_1` |
| `ClassicalLean/InformationTheory/MutualInformation.lean` | 6 — 4 public, 1 private, `mutualInfo.eq_1` |
| `ClassicalLean/InformationTheory/Channel.lean` | 5 — 4 public, 1 private |
| `ClassicalLean/Simplex/FisherRao.lean` | 42 (was 43: `shannonEntropy.eq_1` now belongs to `Entropy`) |
| **library total** | **1076**, was 1037: +39 new constants, 0 removed (+40 in the new modules, less the one moved) |

Theorem lists before and after (`~/work/_bump-evidence/ListTheorems.lean`, privateToUserName
applied): raw +39, −0; filtered (`isInternalDetail` on the user name) +22, −0 — the 16 public and 6
private theorems above.

## Consumers (order J4 Done-means 5; round 15's bar)

* `relEntropy` — used outside its module by `MutualInformation` (the definition of `mutualInfo`
  and every theorem there) and by `Channel`; `shannonEntropy_le_shannonEntropy_vecMul`, stated in
  entropy alone, is proved through it (the data-processing inequality at the uniform vector, read
  through `relEntropy_uniform`). It meets the strict bar.
* `mutualInfo` — **no user outside its own module, and this is why.** Its one consequence stated
  without it, subadditivity `H(X, Y) ≤ H(X) + H(Y)`, is a fact about joint distributions, so it lives
  in `MutualInformation` with the definition it is proved through. A channel-form corollary,
  `shannonEntropy_joint_le`, was drafted in Channel and dropped on review: every joint law on
  `α × β` equals `p ⊗ W` for its first marginal `p` and a row-stochastic `W`, so the channel form
  carried two extra hypotheses and no extra content — a name, not a result (`RETIRED.md`:111). The
  next user is named in `HANDOFF.md` §3: data processing for mutual information along a Markov chain.
* `shannonEntropy` (moved, not new) — used by `Simplex/FisherRao.lean` as before, and by both new
  modules.

## Junk values, enumerated first (`ROADMAP.md` §1.11)

`~/work/_bump-evidence/junk_cells.py`, output `junk_cells.out`. Of the meaningful sign cells of one
term `p * log (p / q)` under `Real.log 0 = 0`, `Real.log x = Real.log |x|`, `x / 0 = 0`, exactly one
is junk: `p > 0, q = 0`, value `0` against a true `+∞`. The order's numbers reproduce exactly:
`relEntropy (½, ½) (1, 0) = -(log 2)/2 = -0.346574`, and at `W = [[1, 0], [½, ½]]` the
data-processing inequality's left side is `-0.215762 > -0.346574`. Random search, 40 000 trials per
case with zeros forced in: the data-processing inequality holds under support with `p, q ≥ 0`,
normalised or not; fails without support (gap 5.98) or with a negative `q` entry (gap 11.6).

## Mathlib search

Commands and counts in `ROADMAP.md` §2.8, run against the library, Mathlib at the pin, and Mathlib
v4.34.0 (the toolchain-bump worktree, the newest Mathlib J3 reached). Summary: no Shannon or
relative entropy of a general finite vector (only the two-point and `q`-ary `Real.binEntropy`,
`Real.qaryEntropy`) and no `mutualInfo` in either Mathlib, by name or by the shape of the sum; the
measure-theoretic counterparts exist (`klDiv`, `mul_log_le_toReal_klDiv`, `klDiv_eq_zero_iff`,
and at v4.34.0 only the data-processing inequality `klDiv_comp_right_le`). Prior art
`github.com/FujiHaruka/information-theory` recorded there, not added as a dependency.

## Review

Order 0923 requires a fresh subagent to review statements cold before anything lands.

**First review — the statement list, before any proof.** Two reviewers, neither the author, each
with a lens, read-only, numeric checks under Lean's conventions.

* *Truth and content* — **17 PASS, 1 FLAG, 0 REJECT.** Quoted: "Every statement holds exactly as
  written under its stated hypotheses, including every edge case the order named." The FLAG:
  `Matrix.doublyStochastic` does not exist — Mathlib's `doublyStochastic` is root-namespace
  (measured from the `.ilean` declarations of both builds). Fixed.
* *Conventions, names, redundancy* — **7 PASS, 11 FLAG, 0 REJECT.** Quoted: "Every statement came
  out true in inline python3 checks that use Lean's junk conventions, and no hypothesis was
  redundant. None is contentless in the HANDOFF §4 sense." Required changes, all adopted:
  `stdSimplex` hypotheses made explicit (deprecated at v4.34.0, `Analysis/Convex/StdSimplex.lean:38`);
  the log-sum inequality renamed `mul_log_le_relEntropy` and moved to the entropy module (in this
  library `sum_mul_log_div` already names the relative-entropy sum, so the old name read as
  `x ≤ x`); `shannonEntropy_le_shannonEntropy_vecMul` and
  `mutualInfo_eq_shannonEntropy_add_shannonEntropy_sub_shannonEntropy` renamed to Mathlib's
  convention of naming each side; `vecMul_mem_stdSimplex` split into `sum_vecMul_eq_sum` and
  `vecMul_nonneg`; the channel-form `shannonEntropy_joint_le` replaced by general subadditivity
  (see Consumers).

**Second review — every shipped statement, after proving.** A third reviewer, fresh, read-only,
over the three finished modules and the `FisherRao.lean` diff, against the reviewed list and the
seven adopted changes, including the six `private` theorems the first list did not contain.
Quoted: **"all 22 statements PASS. No statement needs to change. Three docstring fixes are
required, one of them substantive (R1)."** It confirmed the moved `shannonEntropy` byte-identical
(the removed lines and the new ones hash alike, `b252d2615dfc…`), recomputed every numeric claim in
the docstrings, grepped every Mathlib claim in both trees, and found a counterexample for each
hypothesis every "is needed" sentence names. The three required fixes, each checked against the
source before it was applied, and applied:

* **R1** — the planned `relEntropy`/`klDiv` bridge was stated as `relEntropy p q = (klDiv μ_p
  μ_q).toReal`, which is **false**: Mathlib's `klDiv` is `ofReal (∫ llr + ν.real univ -
  μ.real univ)` (`KullbackLeibler/Basic.lean:57`), so the bridge is `(klDiv μ_p μ_q).toReal =
  relEntropy p q + ∑ q - ∑ p` under support; at `p = (1)`, `q = (2)` the stated form gives
  `-0.6931` against `0.3069`. Corrected in `Channel.lean`, `HANDOFF.md` §3 and `ROADMAP.md` §2.8
  before landing. See Findings.
* **R2** — `klFun_nonneg` was cited without its hypothesis `0 ≤ x`. Corrected.
* **R3** — "Mathlib has no finite, real-valued Shannon entropy" overclaimed: `Real.binEntropy` and
  `Real.qaryEntropy` are the two-point and `q`-ary cases. Corrected in the module header, the
  ROADMAP row and this fragment.

Its optional notes were taken too: the missing second witness for each "both hypotheses are
needed" sentence (recomputed here before writing: `(0.625)` on a one-point type, entropy `0.2938 >
0`; `P = [[-1/2, -2], [5/2, 1]]`, mutual information `-2.2292`; `W = [[1, 1], [0, 0]]` at
`(0.9, 0.1)`, entropy `0.3251 → 0.1896`), and "would shadow `klDiv`" tightened to "would collide
under `open InformationTheory`". Its one forward note: at v4.34.0 the private `vecMul_eq_sum`
duplicates Mathlib's `Matrix.vecMul_apply_eq_sum` (absent at the pin) — swap it when J3 lands.

## Findings

1. **A false statement of mine in prose, caught by review before landing.** The bridge to
   Mathlib's `klDiv` was written in three places without Mathlib's mass term (R1 above) — a claim
   about Mathlib made from the shape of the name `klDiv` rather than from its definition. Had it
   landed, the next session's work item would have been to prove a false equation.
2. **Random search does not reach measure-zero junk cells.** The first reviewer's random signed
   search found no failure of the mutual-information identity without `P ≥ 0`, yet a hand-built
   case with an exactly-zero marginal breaks it. §1.11's enumerate-first rule needs constructed
   exact-zero cases as well as random trials.
3. **`stdSimplex` is deprecated at Mathlib v4.34.0** in favour of `StdSimplex`; four existing
   modules use it (see J3 status).

## J3 status (the toolchain move), for the session that resumes it

Branch `toolchain-bump`, worktree `~/work/classical-lean-bump`, head `6d7b911`: five steps
green and committed, v4.29.1 → v4.33.1, each with 0 warnings, the filtered theorem list identical
to the before list, no statement changed, and no `backward.*` option added. It stopped at the
sixth step: Mathlib v4.34.0's cache on `cache.mathlib.org` lacks the build products of
`Mathlib.Probability.Kernel.Invariance` (re-probed once, same result), so
`lake build --no-build Mathlib` exits 3 and the order says STOP. Measured since: this library's
static import closure (3875 modules, 3384 of them Mathlib; `import_closure.py`, with a positive
control) does **not** reach that module. The branch is unmerged and needs a rebase over this round's
commits. Things that resumption will meet: `stdSimplex` is deprecated at v4.34.0 and used by
`Simplex/Basic`, `Simplex/Ordered`, `Simplex/Symmetry` and `Simplex/FisherRao` (this round's modules
avoid it); and at v4.34.0 `ring` closes goals in `PowerSeries R` with no option set (tested in three
states, `~/work/_bump-evidence/ring-v4.34.0.txt`), so the second build note in `HANDOFF.md` §1 and
the ten modules' `backward.isDefEq.respectTransparency false` lines become candidates for removal.

## Gates

The six commands of `HANDOFF.md` §1, copied from its lines 49–54, run on a **clean** tree
(`git status --porcelain` empty) at `3e600b2`, on helios, Lean `v4.29.0-rc2`. Each was predicted
first; each matched.

| gate | result |
|---|---|
| `lake build` | rc 0, **0 warnings**, "Build completed successfully (3524 jobs)" |
| `tools/AxiomGate.lean` | rc 0 — **1076** theorem constants, all within `{propext, Classical.choice, Quot.sound}`; the same **2** scoped exceptions, **no new exception** |
| `tools/VacuityGate.lean` | rc 0 |
| `tools/check_sorry.py` | rc 0, PASS, 44 files — no `sorry` ships |
| `tools/banned_vocab_scan.py` | rc 0, PASS, 0 hits |
| `tools/check_records.py` | rc 0, PASS, 44 modules, **6** files searched (this fragment is the sixth), 1 exemption |

Gate 6 was also seen failing on each new module first, as order 0923 requires: after
`Entropy.lean` was created it returned rc 1, `UNRECORDED ClassicalLean/InformationTheory/Entropy.lean`,
and before this fragment existed it named all three — so none of the three file names had been
pre-passed by an earlier record. Per-module counts re-taken on the clean tree: 29 / 6 / 5, and
`FisherRao` 42, total 1076, unchanged from the table above.

## Addendum at order 0923's close (2026-09-23)

The order's Close item 3 — a fresh subagent checking every Done-means against the session's whole
diff (`202394ad..master`, `lean-rebuild efe35b76..master`, `master...toolchain-bump`) — returned
**every item checked MET**, and the J3 STOP handled as its paragraph requires. Its findings, each
recorded here for the session that resumes J3:

* **The branch commits staged by sweep** — each staged the whole output of
  `git diff --name-only` rather than naming its paths, against order 0923's "stage by path".
  Nothing unrelated was swept in (26 files, all J3's). Resume with named paths, and have J3's
  step-5 review confirm the file list.
* **Two linters turned off on the branch** — `weak.linter.style.header = false` in `lakefile.toml`
  (library-wide; its warnings asked for a Mathlib copyright block, a licence decision that is
  Dustin's) and `set_option linter.defProp false in` on `isLocalId`. "No `backward.*` option added"
  is true and does not say this; `HANDOFF.md` §1 now does. Both belong in J3's step-5 review.
* **The worktree holds the uncommitted v4.34.0 pin** (`lakefile.toml`, `lean-toolchain`,
  `lake-manifest.json`), left in place as the state where J3 stopped.
* **Round 17 is reserved for J3** and does not exist on `master` because J3 has not landed; the
  numbering gap between rounds 16 and 18 is that, not a lost record.
* The evidence logs under `~/work/_bump-evidence/` hold gate output but not each command's rc or
  the porcelain status, which exist only in the session transcript; next time write `rc=` into the
  log. `ring-v4.34.0.txt` is empty because that run printed nothing — no error at any of the six
  examples; the same file printed 72 error lines at `v4.29.0-rc2`.
