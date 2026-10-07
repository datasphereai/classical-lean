# Round 19 — the licence, order 0923's debts, and the information-theory records

Session: Claude Code `session_01BJXvpG7w5sbVN7yDWgdFwE` on helios, executing order `G-5`
(`records/orders/20260923T172503Z__claude-ai__order-g5-licence-gauss-markov.md`), job J2.
Lean and Mathlib v4.34.0 throughout.

Commits: J1's records `d9ed3b6`; J2 step 1 `288935b`, step 2 `327a100`, step 3 `84056fb`,
step 4 `27163db`, step 5 `c0d136c`; this fragment's own commit is added in a follow-up edit
(records/README.md Rule 1). This fragment is the appointed records commit for steps 1 to 5,
which landed before it (Rule 4): gate 6 cannot see a missing round entry for modules that are
already named, so it is named here, not left to the next session.

Evidence, outside the repository: `~/work/_bump-evidence/g5/evidence.log` (every line a command
and its rc), the before dump `~/work/_bump-evidence/g5-before/`, per-step logs and dumps under
`~/work/_bump-evidence/g5/`.

## Modules

Changed, the licence header only (five lines and a blank line at the top):

* `ClassicalLean/Algebra/CompanionMatrix.lean`
* `ClassicalLean/Combinatorics/AlgebraicGeneratingFunction.lean`
* `ClassicalLean/Combinatorics/RecurrenceGeneratingFunction.lean`
* `ClassicalLean/Geometry/Helix.lean`
* `ClassicalLean/Geometry/Hopf.lean`
* `ClassicalLean/Geometry/S3Quaternion.lean`
* `ClassicalLean/Geometry/SU2SO3.lean`
* `ClassicalLean/Geometry/Spectral3x3.lean`
* `ClassicalLean/GoldenRatio/Characterisations.lean`
* `ClassicalLean/InformationTheory/Channel.lean`
* `ClassicalLean/InformationTheory/Entropy.lean`
* `ClassicalLean/InformationTheory/MutualInformation.lean`
* `ClassicalLean/Logic/PredicateStack.lean`
* `ClassicalLean/NumberTheory/Catalan.lean`
* `ClassicalLean/NumberTheory/CompositumDiscriminant.lean`
* `ClassicalLean/NumberTheory/FactorialPart.lean`
* `ClassicalLean/NumberTheory/Jacobsthal.lean`
* `ClassicalLean/NumberTheory/Lucas.lean`
* `ClassicalLean/NumberTheory/LucasApparition.lean`
* `ClassicalLean/NumberTheory/LucasCompanion.lean`
* `ClassicalLean/NumberTheory/LucasSequence.lean`
* `ClassicalLean/NumberTheory/LucasSequenceCases.lean`
* `ClassicalLean/NumberTheory/LucasSequenceGeneratingFunction.lean`
* `ClassicalLean/NumberTheory/Mersenne.lean`
* `ClassicalLean/NumberTheory/MersenneFactorialPart.lean`
* `ClassicalLean/NumberTheory/MersenneOrder.lean`
* `ClassicalLean/NumberTheory/NacciTrace.lean`
* `ClassicalLean/NumberTheory/Pell.lean`
* `ClassicalLean/NumberTheory/PowerSumCases.lean`
* `ClassicalLean/NumberTheory/PrimitiveDivisor.lean`
* `ClassicalLean/NumberTheory/Tribonacci.lean`
* `ClassicalLean/Order/Superadditive.lean`
* `ClassicalLean/Order/Tolerance.lean`
* `ClassicalLean/Simplex/Basic.lean`
* `ClassicalLean/Simplex/CrossEntropy.lean`
* `ClassicalLean/Simplex/DesignConstants.lean`
* `ClassicalLean/Simplex/FisherRao.lean`
* `ClassicalLean/Simplex/Gibbs.lean`
* `ClassicalLean/Simplex/Hessian.lean`
* `ClassicalLean/Simplex/Involution.lean`
* `ClassicalLean/Simplex/LogSumExp.lean`
* `ClassicalLean/Simplex/Ordered.lean`
* `ClassicalLean/Simplex/Symmetry.lean`
* `ClassicalLean/Simplex/Temperature.lean`

and `ClassicalLean.lean`. Changed beyond the header: the ten modules of step 3,
`InformationTheory/Channel.lean` (step 4) and `NumberTheory/Mersenne.lean` (step 5), as below.
No module was added or removed. Also changed: `LICENSE` (new), `lakefile.toml`,
`tools/banned_vocab_scan.py`, `HANDOFF.md`, `ROADMAP.md`, `RETIRED.md`.

## Hypotheses, stated before measuring

* **H1.** `backward.isDefEq.respectTransparency` acts on elaboration. So a removal after which
  the library builds with 0 warnings, and after which every theorem type and every definition's
  type and value is unchanged, changes no statement's meaning. Tested for each removal by the
  type dump below. *Measured*, per removal.
* **H2.** Where a removal broke a proof, the cause was the instance argument of a `Finset.sum`,
  not the summands: `rw` reported "Did not find an occurrence of the pattern `∑ i, ?f i`" on a
  goal that visibly contained such a sum, and `erw`, which unfolds instances when matching,
  succeeded. *Inferred* from those two outputs; the instance terms were not printed.

## The type dump, and its fire test

`~/work/_bump-evidence/TypeDump.lean` prints one JSON line per constant under `ClassicalLean`
(AxiomGate's predicate): each theorem's type and each definition's type and value, in two
forms, `pp.all` with `pp.maxSteps` raised (no elision) and the structural `toString` of the
`Expr`. `g5_typediff.py` compares two dumps by raw name. Before evidence, clean tree at
`d9ed3b6`: 1233 records, 1072 theorems and 161 definitions, 0 elided; the theorems' user names
equal `ListTheorems.lean`'s raw list. Fire test (HANDOFF §0): a second dump of the same tree gave
`changed=0` (rc 0); a copy with one theorem's type altered and one definition removed gave
`REMOVED 1, CHANGED 1` (rc 1); a missing file gave rc 125. The first planted copy planted
nothing — the edit looked for text the chosen type did not contain — and the comparator
correctly reported `changed=0`; the script was fixed to change the type unconditionally and to
assert that it did, and the second run is the one quoted.

## Step 1 — the vocabulary exception (`288935b`)

One `EXCEPTIONS` entry, the scanner's first live one. **Deviation from the order's text, by this
session's ruling (R24; recorded here, Dustin's veto open):** the scanner compiles every
exception with `re.I` (`tools/banned_vocab_scan.py`, the line building `exceptions`), and
Python's `\d` matches every Unicode digit. So the order's pattern as written would also have
exempted `authors: dustin [surname]`, `AUTHORS: DUSTIN [surname]`, `Copyright (C) 2026 …` and a
year in another digit script — measured in memory, all four `True` — which is more than
"exactly the two licence lines". The landed pattern wraps it in `(?-i:…)` and uses `[0-9]`:

    (r"[surname]", r"(?-i:^(Copyright \(c\) 20[0-9][0-9] Dustin [surname]\. All rights reserved\.|Authors: Dustin [surname])$)")

Stated limit: the exception is by line text, not by position; the same whole line elsewhere in
a scanned file would pass. Lines carrying an audit marker were already exempt.

Fail test on `NumberTheory/Catalan.lean`, restored and `cmp`'d after every run. Predicted, then
measured: without the exception, the header gives 2 hits, rc 1 (lines 2 and 4). With it: a
scratch line `-- the [surname] theorem` 1 hit, rc 1; the header alone 0 hits, rc 0; an Authors
line with trailing text 1 hit, rc 1; the Authors line lowercased 1 hit, rc 1. All five held.

## Step 2 — the licence and the header (`327a100`)

`LICENSE` is Mathlib's, byte for byte (sha256 `b40930bb…33e1`, 201 lines, the one `{yyyy}`
placeholder kept). The header was prepended to 45 files by a script that asserted the count
and that each began with `import`; `head -6` of all 45 equals it. `lakefile.toml` lost
`weak.linter.style.header = false` and its comment, so `weak.linter.mathlibStandardSet` turns
Mathlib's header linter on. Two limits of that linter, read in
`Mathlib/Tactic/Linter/Header.lean`: it never checks the library root file, and it locates the
root by a relative path, so its copyright checks run only when `lake build` starts in the
repository root. Unstaged numstat `6 0` ×45, `0 5`, one HANDOFF row. `lake build` rc 0, 0
warnings, 45 files rebuilt. Name lists byte-identical to before; type dump `changed=0`. Fire
test: `Catalan.lean` without its Authors line gave exactly one warning, predicted —
``Catalan.lean:4:0: * `-/`:`` / `Copyright too short!` — and 0 once restored (`cmp` rc 0).

## Step 3 — the fifteen `respectTransparency` settings (`84056fb`)

Each removed alone, then a full `lake build` and a type dump against before. **Predicted 13 of
15 go, with `finrank_K1_eq`'s and `disc_K_eq_240_pow_4`'s most likely to stay; actual 15 of 15.**
Every removal: build rc 0, 0 warnings, `removed=0 added=0 changed=0`.

| module | setting | result | proof edit |
|---|---|---|---|
| `NumberTheory/LucasSequenceGeneratingFunction` | file-level | went | the `example` after `recDenom_lucasRec`: `erw [Fin.sum_univ_two] at h; simpa [lucasRec] using h` |
| `Combinatorics/RecurrenceGeneratingFunction` | file-level | went | none |
| `Combinatorics/AlgebraicGeneratingFunction` | file-level | went | none; the six errors its docstring measured at `v4.29.0-rc2` do not occur |
| `Geometry/Hopf` | file-level | went | none |
| `Geometry/S3Quaternion` | file-level | went | none |
| `Geometry/SU2SO3` | file-level | went | none |
| `Geometry/Helix` | file-level | went | none |
| `Algebra/CompanionMatrix` | file-level | went | none |
| `NumberTheory/PowerSumCases` | file-level | went | two: `rw [h, Fin.sum_univ_two]` and `rw [hsub, sum_nacciCoeffs]`, each split with the sum lemma by `erw` |
| `NumberTheory/CompositumDiscriminant` | `finrank_K2_eq`, `finrank_F5`, `finrank_Q_sqrt2`, `finrank_Q_sqrt3`, `finrank_K1_eq`, `disc_K_eq_240_pow_4`, each `… in` | all six went | none |

Tries in `LucasSequenceGeneratingFunction`, in order: adding `dsimp only [lucasRec] at h` —
same `Type mismatch`; `rw [Fin.sum_univ_two] at h` — "Did not find an occurrence of the
pattern"; `dsimp` then `erw` — builds; `erw` without `dsimp` then `simpa using h` — mismatch on
`(lucasRec P Q).order`; `erw`, then `simpa [lucasRec]` — builds, kept (a two-line change).

Why they could go, measured in both Mathlib trees with `grep -c respectTransparency`: every
upstream reason the library's text gives is gone at v4.34.0. `Analysis/Quaternion.lean` 18 → 0
(cited by `Hopf`, `SU2SO3`, `S3Quaternion`); `RingTheory/PowerSeries/Basic.lean` 14 → 0, and its
`instance [AddGroup R] : AddGroup R⟦X⟧` and `instance [CommRing R] : CommRing R⟦X⟧` (cited by the
two generating-function docstrings) are gone, `infer_instance` 13 → 0; `PowerSeries/Catalan.lean`
1 → 0; `FieldTheory/IntermediateField/Adjoin/Basic.lean` 19 → 1, none above `adjoin.finrank`
(cited above `finrank_K2_eq`). File-level settings in all of Mathlib: 14 → 0. The texts saying the
option is needed keep their words and carry "Superseded 2026-09-23: builds without the option at
v4.34.0 (round 19)."

`finrank_K1_eq`'s heartbeat figures, re-measured because its option went, and dated in the
module, not superseded: `#count_heartbeats` 91057 without the option and 84249 with it put back
(temporary edits, the file restored and `cmp`'d); it builds at the default 200000 and at 250000.
So it is the toolchain, not the option, that brought it under the default. Its
`maxHeartbeats 400000` stays, and `HANDOFF.md` §3 lists it as a one-line removal for later.
`RingPowerSeries.lean` re-run once: rc 0, no output (`ring-v4.34.0-g5.txt`, command and rc in
the file).

## Step 4 — `Channel`'s private lemma (`27163db`)

Mathlib's `Matrix.vecMul_apply_eq_sum` (`Data/Matrix/Mul.lean:726`) states the private
`vecMul_eq_sum` exactly, by `rfl`. Its five uses name it in full, and the private theorem is
gone. Raw 1072 → 1071, filtered 725 → 724, private 136 → 135; the only line gone from either
list is `ClassicalLean.Simplex.vecMul_eq_sum`, and the dump's only change is that removal.

## Step 5 — two counts (`c0d136c`)

`Order/Superadditive.lean` declares five theorems (eight constants with three `_proof_1_1`
auxiliaries), as round 16's finding 5 said. `NumberTheory/Mersenne.lean` said "six" twice and
`HANDOFF.md` §3 said "four"; each now says five with a dated note.

## Step 6 — the information-theory records

**Correction to round 18.** Round 18 wrote that Mathlib has, "at v4.34.0 only, the
data-processing inequality `klDiv_comp_right_le`", and named no other file of Mathlib's
`InformationTheory/` beyond `KullbackLeibler/Basic.lean`. Nothing it said is false; it is
incomplete. Measured in both trees (`find InformationTheory -name '*.lean' | sort` under each
`Mathlib/`): v4.34.0 has **nine** files — `Coding/{Kraft, KraftMcMillan, PrefixFree,
UniquelyDecodable}`, `Hamming`, `KullbackLeibler/{Basic, ChainRule, DataProcessing, KLFun}` — and
the pin `8f07524533` had five, the last four of those absent. `ChainRule.lean:204` holds
`klDiv_compProd_eq_add`, a chain rule for the KL divergence, not for entropy.
`DataProcessing.lean` holds three data-processing inequalities: `klDiv_map_le` (:160),
`klDiv_trim_le` (:180) and `klDiv_comp_right_le` (:186). `Coding/` holds the Kraft–McMillan
inequality (`KraftMcMillan.lean:145`, at the pin too) and Kraft's inequality for prefix-free
codes (`Kraft.lean:43`, `:71`). `ROADMAP.md` §2.8 carries this as a dated line beside its
paragraph.

**Prior art, measured by claude-ai, not by this session.** In a clone of
`github.com/FujiHaruka/information-theory` at `7e97b77` (2026-09-14): Apache-2.0; Lean and
Mathlib v4.31.0; 418 modules; 4,055 `theorem`/`lemma` declarations by its grep (which, claude-ai
notes, misses `@[attr] theorem` lines; the README claims 4,108); 0 `axiom` declarations; 27
`sorry` tokens, all in prose. Random-variable form (`entropy μ Xs`, `Shannon/Bridge.lean:40`),
with `condEntropy`, `mutualInfo_chain_rule`, `condEntropy_pi_chain_rule`, the Markov
data-processing inequality `mutualInfo_le_of_markov`, Pinsker, Fano, Kraft and Huffman
optimality. The commands are in `ROADMAP.md` §2.8 and in order G-5 §0. This session read only
the saved README (`~/work/_bump-evidence/fujiharuka-README.md`): its 4,108, and its
`mutualInfo_le_of_postprocess` linked to `Shannon/DPI.lean`, a different theorem from
`mutualInfo_le_of_markov`.

**The decision.** Information theory part 2 — conditional entropy, the chain rule, Markov data
processing, Pinsker, Fano — is declined for now, on the prior-art ground Dustin asked claude-ai
to apply on 2026-09-23; claude-ai decided it on his delegation, and his veto is open. The
finite-vector forms would still be new here, so this is a ranking decision, not a finding that
they add nothing. The three finite modules stay as they are. Recorded in `ROADMAP.md` §2.8 and
`HANDOFF.md` §3.

**Why `mutualInfo` keeps no consumer.** Round 18's Consumers section: its one consequence
stated without it, subadditivity, is a fact about joint distributions and lives in its own
module; a channel-form corollary was dropped on review as a name, not a result. The one user
round 18 named, data processing for mutual information along a Markov chain, is declined above.
So it keeps none, deliberately: it is the definition the nonnegativity, the independence
characterisation and `I = H(X) + H(Y) - H(X, Y)` are stated through, and a finite Markov
data-processing inequality, if the veto reopens that line, is still where its first outside
user would come from. The `klDiv` bridge stays listed as the first step if the finite layer is
ever offered to Mathlib.

## Step 7 — lessons moved into the repository

`HANDOFF.md` §6 carries order 0923's seven rules and order G-5's standing answers (the cache
gap, the deprecation rule, the licence, the exception as landed, `mem_closedSimplex`, the parked
build, asking Dustin), each with its date and source. §3's `mem_closedSimplex` bullet is marked
settled. §6's push list gains the `025b729` push, from the `dsmain/master` reflog and
`push.log`, without an approval this repository does not record: J1 had predicted
`dsmain/master` at `7ad841e` from that list, and measured `025b729`.

## Per-module theorem-constant counts

`~/work/_bump-evidence/ModuleThmCount.lean`, AxiomGate's `.thmInfo` predicate, owning module from
`env.getModuleFor?`; run at `c0d136c` with only `HANDOFF.md` and `ROADMAP.md` uncommitted (no
`.lean` difference): total 1071, private 135, 44 modules, equal to AxiomGate's 1071 on the same
tree. Against order 0923's saved counts (`j3r-module-thm-count.txt`, total 1072) the only
difference is `Channel`, 5 → 4.

| module | theorem constants |
|---|---|
| `ClassicalLean/Algebra/CompanionMatrix.lean` | 33 |
| `ClassicalLean/Combinatorics/AlgebraicGeneratingFunction.lean` | 27 |
| `ClassicalLean/Combinatorics/RecurrenceGeneratingFunction.lean` | 9 |
| `ClassicalLean/Geometry/Helix.lean` | 28 |
| `ClassicalLean/Geometry/Hopf.lean` | 14 |
| `ClassicalLean/Geometry/S3Quaternion.lean` | 11 |
| `ClassicalLean/Geometry/SU2SO3.lean` | 28 |
| `ClassicalLean/Geometry/Spectral3x3.lean` | 12 |
| `ClassicalLean/GoldenRatio/Characterisations.lean` | 35 |
| `ClassicalLean/InformationTheory/Channel.lean` | 4 |
| `ClassicalLean/InformationTheory/Entropy.lean` | 22 |
| `ClassicalLean/InformationTheory/MutualInformation.lean` | 6 |
| `ClassicalLean/Logic/PredicateStack.lean` | 9 |
| `ClassicalLean/NumberTheory/Catalan.lean` | 4 |
| `ClassicalLean/NumberTheory/CompositumDiscriminant.lean` | 110 |
| `ClassicalLean/NumberTheory/FactorialPart.lean` | 10 |
| `ClassicalLean/NumberTheory/Jacobsthal.lean` | 17 |
| `ClassicalLean/NumberTheory/Lucas.lean` | 43 |
| `ClassicalLean/NumberTheory/LucasApparition.lean` | 26 |
| `ClassicalLean/NumberTheory/LucasCompanion.lean` | 9 |
| `ClassicalLean/NumberTheory/LucasSequence.lean` | 44 |
| `ClassicalLean/NumberTheory/LucasSequenceCases.lean` | 16 |
| `ClassicalLean/NumberTheory/LucasSequenceGeneratingFunction.lean` | 20 |
| `ClassicalLean/NumberTheory/Mersenne.lean` | 13 |
| `ClassicalLean/NumberTheory/MersenneFactorialPart.lean` | 14 |
| `ClassicalLean/NumberTheory/MersenneOrder.lean` | 19 |
| `ClassicalLean/NumberTheory/NacciTrace.lean` | 48 |
| `ClassicalLean/NumberTheory/Pell.lean` | 20 |
| `ClassicalLean/NumberTheory/PowerSumCases.lean` | 58 |
| `ClassicalLean/NumberTheory/PrimitiveDivisor.lean` | 10 |
| `ClassicalLean/NumberTheory/Tribonacci.lean` | 15 |
| `ClassicalLean/Order/Superadditive.lean` | 8 |
| `ClassicalLean/Order/Tolerance.lean` | 12 |
| `ClassicalLean/Simplex/Basic.lean` | 9 |
| `ClassicalLean/Simplex/CrossEntropy.lean` | 10 |
| `ClassicalLean/Simplex/DesignConstants.lean` | 58 |
| `ClassicalLean/Simplex/FisherRao.lean` | 42 |
| `ClassicalLean/Simplex/Gibbs.lean` | 54 |
| `ClassicalLean/Simplex/Hessian.lean` | 36 |
| `ClassicalLean/Simplex/Involution.lean` | 38 |
| `ClassicalLean/Simplex/LogSumExp.lean` | 20 |
| `ClassicalLean/Simplex/Ordered.lean` | 14 |
| `ClassicalLean/Simplex/Symmetry.lean` | 11 |
| `ClassicalLean/Simplex/Temperature.lean` | 25 |
| **total** | **1071** |

## Whole-library gate numbers — clean or mixed

Each step's numbers were taken on the tree that became its commit, with nothing else
uncommitted, and are in its commit message. J2's Done-means numbers are taken on a clean tree at
this fragment's commit and added with its hash.

**Added in the follow-up edit (Rule 1): this fragment's commit is `3baff97`.** J2's Done-means,
on a clean tree at `3baff97` (`git status --porcelain` empty): `lake build` rc 0, 0 warnings,
header linter on (`grep linter.style.header lakefile.toml` rc 1); AxiomGate 1071 PASS,
VacuityGate PASS, check_sorry PASS, banned_vocab_scan PASS with 0 hits, check_records PASS (44
modules, 9 files), each rc 0; 45 of 45 files begin with the header; `LICENSE` sha256
`b40930bb…33e1`. `ListTheorems.lean`: raw 1071, filtered 724, private 135; against J1's before
lists the filtered and the raw list each differ by exactly one line, the removal of
`ClassicalLean.Simplex.vecMul_eq_sum`, and no auxiliary was renamed. Type dump against before:
`REMOVED thm _private.ClassicalLean.InformationTheory.Channel.0.ClassicalLean.Simplex.vecMul_eq_sum`,
`removed=1 added=0 changed=0` — every other theorem type and every definition unchanged.

## J1, for the record

J1 was read-only; its predicted-beside-actual table is in the session's report. Two predictions
missed: `dsmain/master` and DSMain were at `025b729`, not `7ad841e` (the push list, above), and
one `.lean` file had changed after `f04bf6b` — `AlgebraicGeneratingFunction`'s docstring, a
review fix in `6b70bf4`. The deferred `lake build`: rc 0, 0 warnings, nothing built.
