# Round 16 — the consumer audit round 15 named and did not run, and the stale "no remote"

Session: Claude Code `session_01A172nPt1wcsnUPA6SyKERL` on helios, executing order `0923`
(`records/orders/20260923T122713Z__claude-ai__order-0923-pick-up.md`), job J2. Documentation only:
**no declaration added, removed or changed.**

Commits (added in a follow-up edit, records/README.md Rule 1): **`77550f5`** — this round's content;
**`12553d7`** — a whitespace rewrap in `ClassicalLean/Order/Superadditive.lean` after the long-line
linter fired on `77550f5` (see Gates). Preceded by `d97c276`, which filed order 0923 and claimed.

## Modules touched (doc comments only)

* `ClassicalLean/Order/Superadditive.lean` — a "Consumer audit — round 16" section in the header.
* `ClassicalLean/Logic/PredicateStack.lean` — the same section, and one corrected identifier: the
  header's contents list named `Stack.admits_mono_append`, which has never existed in the file (the
  module owns 11 constants, listed below, and none has that name). It now names
  `Stack.admits_of_append_left` and `admits_of_append_right`, and says what it used to say.

## The criterion

Round 15 (`PROVENANCE.md`, the round-15 section) moved `Order/Tolerance.lean` from "has an instance"
to "has no consumer" and named the same test as not run for `Superadditive` and `PredicateStack`.
Written out, as used here: **a consumer is a shipped declaration outside the defining file that
uses the definition or its lemmas to prove something whose statement does not mention the
definition.** An `example` creates no constant, so it is not shipped and cannot count.

## Measured at the constant layer

A text grep cannot separate an instance from a consumer, and dot notation hides the name
(`superadditive_mersenne.monotone` contains no `Superadditive`). So the audit walks every constant
of the built library and compares what its **type** and its **proof term** mention. Script, run
from the main tree as `lake env lean ~/work/_bump-evidence/ConsumerAudit.lean`, rc 0:

```lean
import ClassicalLean
import ImportGraph.Lean.Environment
open Lean Elab Command
def auditTargets : List Name :=
  [`ClassicalLean.Order.Superadditive, `ClassicalLean.Logic.PredicateStack]
run_cmd do
  let env ← getEnv
  let all := env.constants.toList
  for tgt in auditTargets do
    let owned : List Name := all.filterMap fun (n, _) =>
      if env.getModuleFor? n == some tgt then some n else none
    let mut lines : Array String := #[]
    let mut consumers := 0
    for (n, ci) in all do
      if n.hasMacroScopes then continue
      let some m := env.getModuleFor? n | continue
      if m == tgt then continue
      unless (`ClassicalLean).isPrefixOf m do continue
      let tyUses := ci.type.getUsedConstantsAsSet
      let valUses : NameSet := match ci.value? with
        | some v => v.getUsedConstantsAsSet
        | none => {}
      let tyHit := owned.filter tyUses.contains
      let valHit := owned.filter valUses.contains
      if tyHit.isEmpty && valHit.isEmpty then continue
      let kind := match ci with
        | .thmInfo _ => "theorem" | .defnInfo _ => "def" | _ => "other"
      let isConsumer := tyHit.isEmpty
      if isConsumer then consumers := consumers + 1
      let verdict := if isConsumer then "CONSUMER" else "stated-in-its-terms"
      lines := lines.push s!"  {privateToUserName n}  [{kind}; {m}]  type:{tyHit}  value:{valHit}  => {verdict}"
    logInfo s!"AUDIT {tgt}: owns {owned.length} constants {owned}; {lines.size} user(s) outside, {consumers} consumer(s)\n{String.intercalate "\n" lines.toList}"
```

Output, verbatim apart from line wrapping:

```
AUDIT ClassicalLean.Order.Superadditive: owns 9 constants [ClassicalLean.Superadditive.pos_of_pos._proof_1_1,
  ClassicalLean.Superadditive, ClassicalLean.Superadditive.unbounded._proof_1_1, ClassicalLean.Superadditive.linear_le,
  ClassicalLean.Superadditive.map_zero._proof_1_1, ClassicalLean.Superadditive.monotone, ClassicalLean.Superadditive.unbounded,
  ClassicalLean.Superadditive.map_zero, ClassicalLean.Superadditive.pos_of_pos]; 1 user(s) outside, 0 consumer(s)
  ClassicalLean.Mersenne.superadditive_mersenne  [theorem; ClassicalLean.NumberTheory.Mersenne]  type:[ClassicalLean.Superadditive]  value:[]  => stated-in-its-terms
AUDIT ClassicalLean.Logic.PredicateStack: owns 11 constants [ClassicalLean.Stack.admits_cons._simp_1,
  ClassicalLean.Stack.admits_nil._simp_1, ClassicalLean.Stack.Admits, ClassicalLean.Stack.admits_cons, ClassicalLean.Stack.Admits.eq_1,
  ClassicalLean.Stack.admits_of_sublist, ClassicalLean.Stack.admits_nil, ClassicalLean.Stack, ClassicalLean.Stack.admits_of_append_right,
  ClassicalLean.Stack.admits_of_append_left, ClassicalLean.Stack.admits_of_forall₂]; 3 user(s) outside, 0 consumer(s)
  ClassicalLean.Simplex.admits_openSimplexStack_iff  [theorem; ClassicalLean.Simplex.Basic]  type:[ClassicalLean.Stack.Admits]  value:[ClassicalLean.Stack.Admits, ClassicalLean.Stack]  => stated-in-its-terms
  ClassicalLean.Simplex.openSimplexStack.eq_1  [theorem; ClassicalLean.Simplex.Basic]  type:[ClassicalLean.Stack]  value:[ClassicalLean.Stack]  => stated-in-its-terms
  ClassicalLean.Simplex.openSimplexStack  [def; ClassicalLean.Simplex.Basic]  type:[ClassicalLean.Stack]  value:[]  => stated-in-its-terms
```

Text layer, beside it, in round 15's form: `grep -rn 'Superadditive' ClassicalLean/ --include=*.lean`
outside its own file → **6 lines, all in `NumberTheory/Mersenne.lean`**; `grep -rn 'Stack'
ClassicalLean/ --include=*.lean` outside its own file → **12 lines, all in `Simplex/Basic.lean`**.
The consumer-shaped uses are `example`s: `Mersenne.lean` lines 171 and 173
(`superadditive_mersenne.monotone`, `.linear_le`) and `Simplex/Basic.lean` lines 91–95
(`Stack.admits_of_append_right` giving a simplex point's normalisation).

Predicted before running, beside actual: Superadditive 1 outside user / 0 consumers — **1 / 0**;
PredicateStack 2 outside users / 0 consumers — **3 / 0**. The miss is the auto-generated equation
lemma `openSimplexStack.eq_1`, a constant the prediction did not count.

## Verdict

**Both modules: an instance, no consumer — the standing round 15 gave `Tolerance`. Both are kept**;
retiring a module is Dustin's call, not an audit's. What would change either verdict: a shipped
theorem, stated without the definition, whose proof goes through it — for instance promoting one of
the `example`s above to a named theorem, if its statement is wanted for its own sake.

Recorded in each module header, and in `ROADMAP.md` §1.12 as a dated correction **beside** round
15's paragraph, which is kept as written.

## Per-module theorem-constant counts

`~/work/_bump-evidence/ModuleThmCount.lean`, run from the main tree, rc 0. The predicate is
`tools/AxiomGate.lean`'s exactly — skip `hasMacroScopes`; keep a constant when `ClassicalLean`
prefixes `privateToUserName n`; count `.thmInfo` — with the owning module from `env.getModuleFor?`.
The script prints the all-module total first, and it was checked against AxiomGate before either
number below was used:

| | predicted | measured |
|---|---|---|
| total over all modules | 1037 (AxiomGate's count) | **1037**, over 41 modules; 122 of them private |
| `ClassicalLean/Order/Superadditive.lean` | ≥ 5 (declared theorems) | **8** — 5 declared plus 3 `_proof_1_1` auxiliaries |
| `ClassicalLean/Logic/PredicateStack.lean` | ≥ 4 (declared theorems) | **9** — 6 declared plus 2 `_simp_1` and `Admits.eq_1` |

The PredicateStack prediction rested on a source grep, `^(private |protected )?(theorem|lemma) `,
that returned 4. The file declares **6** theorems: `admits_nil` and `admits_cons` are written
`@[simp] theorem …` and the line-anchored pattern missed both. So the ≥ 4 held, but on a wrong count.

These were taken **before** the doc-comment edits, on the tree at `d97c276`; doc comments do not
change constants, and the clean-tree gate run after this round's commit (below) re-checks the total.

A note on the API that `records/README.md` Rule 1 names: `env.getModuleFor?` is not in Lean core
(`Lean/Environment.lean` at v4.29.0-rc2 has `getModuleIdxFor?`). It is
`Lean.Environment.getModuleFor?` from ImportGraph (`ImportGraph/Lean/Environment.lean:13`), which
Mathlib imports through `Mathlib/Tactic/Common.lean`; the scripts import it explicitly.

## Other edits in this round

* **"No remote" corrected**, three places, dates re-read from each repository's `dsmain` reflog
  (`lean-rebuild` first push 2026-09-08T23:27:12Z; `classical-lean` 2026-09-09T19:41:09Z):
  `HANDOFF.md` §6 (a dated line under the stale bullet); `PROVENANCE.md` "Where the evidence lives"
  (the one dated line order 0923 allows — nothing else in `PROVENANCE.md` changed); and
  `~/Cowork/lean-rebuild/README.md` (committed there as `b84de8f`). `51c7b71`, the evidence commit
  `PROVENANCE.md` pins, is an ancestor of `lean-rebuild`'s DSMain `master` `3a48ceb5`, read with
  `git ls-remote` and `git merge-base --is-ancestor`.
* **`lean-rebuild`'s untracked evidence committed** (`0f99991`, by path, 12 files, 2.8 MB, all text
  or JSON; a credential-pattern scan hit only the MSC class 94A62 label "Authentication, digital
  signatures and secret sharing"): the G-1 order `records/orders/INDEX.md` points at, the
  foundation-ranked build order and `design/FOUNDATION-DELTA.md` that order 0923 cites, the
  msc-index plan, the thread-A and thread-B notes, and `scripts/`. `INDEX.md`'s G-1 row now says so.
* **The duplicate parked**: `~/Cowork/lean-rebuild/20260907T225350Z__claude-ai__msc-index-and-lean-coverage-plan (copy 1).md`
  (13011 B, sha256 `ab83e613…`, byte-identical to the file without ` (copy 1)`, untracked) moved to
  `~/Cowork/_parked/`, preconditions re-checked in the same chain.

## Findings

1. **Round 15 was written into `PROVENANCE.md`** (its heading at line 42), although
   `records/README.md` Rule 1 sends new rounds to `records/rounds/`. Left there, as order 0923
   directs; this fragment is the first under `records/rounds/`.
2. **Round 15 wrote no `records/CLAIMS.md` row** (the last row before this session's was dated
   2026-09-08), against Rule 3.
3. **Round 15's commit message lists five gates**; `tools/check_records.py`, gate 6, is missing from
   its gate table.
4. **Round 15's sentence is false as worded.** "Neither has a theorem stated in its terms outside
   its own file" (`PROVENANCE.md` line 73, formerly 71; `ROADMAP.md` line 319):
   `superadditive_mersenne` and `admits_openSimplexStack_iff` are exactly such theorems. What was
   meant is the consumer criterion above. The `PROVENANCE.md` copy is in the round-15 archive and is
   **left untouched**; this finding is its correction. The `ROADMAP.md` copy has a dated correction
   beside it.
5. **Two theorem counts in prose do not match the source**, recorded and not edited (outside this
   round's claim): `NumberTheory/Mersenne.lean` lines 144 and 170 say `Order/Superadditive.lean`
   "proves six" / "The six theorems" — the file declares **5** (8 theorem constants with
   auxiliaries); `HANDOFF.md` §3 describes that module as "a definition, four theorems".
6. **`PredicateStack.lean`'s header named a theorem that does not exist**, `Stack.admits_mono_append`;
   corrected in this round (above).
7. **`records/rounds/` was not tracked by git** while empty — git cannot track an empty directory,
   so a fresh clone would not have had it. This fragment is its first file.
8. **`lean-rebuild` held 12 untracked evidence files**, some of them cited by this library's records,
   in no commit and not on DSMain. Committed as `0f99991` (above).

## Gates

The six commands of `HANDOFF.md` §1, copied from its lines 49–54, each run on a **clean** tree
(`git status --porcelain` empty) on helios.

**Run 1, at `77550f5` — one gate red.** `lake build` rc 0 but **1 warning**:
`ClassicalLean/Order/Superadditive.lean:51:100: This line exceeds the 100 character limit` — a line
of this round's own header text. Predicted 0 warnings; the miss is mine, and it is the failure
`HANDOFF.md` §0 names: warnings exist only at the `lake build` layer. The other five matched the
prediction (AxiomGate 1037 / 2 exceptions; VacuityGate rc 0; text gates PASS, gate 6 at 5 files).

**Run 2, at `12553d7`, after the rewrap — all green, as predicted:**

| gate | result |
|---|---|
| `lake build` | rc 0, **0 warnings**, "Build completed successfully (3508 jobs)"; 9 modules rebuilt |
| `tools/AxiomGate.lean` | rc 0 — **1037** theorem constants, all within `{propext, Classical.choice, Quot.sound}`; the same **2** scoped exceptions (`K1_K2_isCoprime`, `disc_K_eq_240_pow_4` ← `disc_biquadratic_23`) |
| `tools/VacuityGate.lean` | rc 0 |
| `tools/check_sorry.py` | rc 0, PASS, 41 files |
| `tools/banned_vocab_scan.py` | rc 0, PASS, 0 hits |
| `tools/check_records.py` | rc 0, PASS, 41 modules, **5** files searched (this fragment is the fifth), 1 exemption |

Unchanged from round 15, as expected for documentation only: 41 modules, 1037, 2 exceptions.
