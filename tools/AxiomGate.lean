import Lean
import ClassicalLean

/-!
# Axiom gate

A build-time gate on the axiom footprint of every theorem this library ships.

`lake env lean tools/AxiomGate.lean` exits 0 when every theorem constant under
the `ClassicalLean` namespace depends only on axioms in `allowed`, and fails the
elaboration (nonzero exit) otherwise, naming each offender and the axiom that
disqualified it.

## Why this shape

The predecessor of this file listed each theorem by hand in a `#guard_msgs`
block asserting the exact string
`'X' depends on axioms: [propext, Classical.choice, Quot.sound]`.
That has two defects, both of which this file fixes:

1. **It only gates what someone remembered to list.** A new theorem with a
   `native_decide` proof passes, because nobody added a block for it. This gate
   enumerates the environment instead, so a theorem is covered the moment it
   exists.
2. **It rejects clean proofs.** A theorem proved by `rfl` or `decide` prints
   `does not depend on any axioms` — *strictly cleaner* than the kernel trio —
   and fails a `#guard_msgs` written against the trio's exact string. The right
   test is a **subset** test against `allowed`, not string equality.

## Allowed axioms

`propext`, `Classical.choice`, `Quot.sound` — the ambient axioms of Lean 4 plus
Mathlib's classical foundation. Nothing in a Lean library can be more pure than
a subset of these.

Deliberately NOT allowed, and the reason each matters here:

- anything introduced by `native_decide`. This moves the check from the kernel to
  the compiler. Most of the corpus this library was harvested from is proved this
  way; keeping those proofs out is the whole point of the rebuild. Note the axiom
  is not always named the same: older Lean surfaced `Lean.ofReduceBool` and
  `Lean.trustCompiler`, while v4.29 emits a *per-declaration* axiom named
  `<theorem>._native.native_decide.ax_1_1`. A subset test against `allowed`
  catches every spelling; a denylist of known names would not. That is the main
  reason this gate is written as an allowlist.
- `sorryAx` — an admitted proof.
- Any project-declared axiom. If a module ever needs one, add it to
  `scopedExceptions` **by name** together with the theorems allowed to use it,
  so the exception is a record rather than a hole.
-/

open Lean Elab Command

namespace AxiomGate

/-- The kernel/classical trio. A theorem may depend on any subset of these. -/
def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Namespaces policed by this gate. -/
def targets : List Name := [`ClassicalLean]

/-- Per-theorem axiom exceptions, `(theorem, extra axiom it may use)`.
    Adding a row here is a deliberate, reviewable act: it records that a named
    theorem rests on a named axiom beyond the trio.

    **Dated 2026-10-07 (order LEAN-3):** the list is empty.  It held two rows, `K1_K2_isCoprime`
    and `disc_K_eq_240_pow_4` resting on the axiom `disc_biquadratic_23`
    (`|discr ℚ(√2, √3)| = 2304`) in `NumberTheory/CompositumDiscriminant.lean`.  That axiom is
    now a theorem with the same statement, proved through the ring of integers in
    `NumberTheory/BiquadraticDiscriminant.lean`, so the library declares no axiom.

    Names are written as raw `Name` literals (single backtick) rather than resolved
    constants (double backtick), because this file imports only the aggregator and
    these constants need not be in its environment for the list to elaborate. -/
def scopedExceptions : List (Name × Name) := []

/-- Is `ax` permitted for theorem `thm`?  Both names are compared on their user form, so a
    scoped exception can be written with the name as it appears in the source even when the
    declaration is `private`. -/
def permitted (thm ax : Name) : Bool :=
  allowed.contains ax
    || scopedExceptions.any fun (t, a) =>
         t == privateToUserName thm && a == privateToUserName ax

/-- Theorem constants under `targets`, paired with the axioms they use that are
    not permitted. An empty result means the gate passes. -/
def scan : CommandElabM (Array (Name × Array Name)) := do
  let env ← getEnv
  let mut bad : Array (Name × Array Name) := #[]
  for (n, ci) in env.constants.toList do
    -- Compiler- and macro-generated declarations are not user claims.
    if n.hasMacroScopes then continue
    -- `isInternal` is deliberately NOT used to skip: it also skips user
    -- declarations whose name starts with `_`, which would let a leading
    -- underscore walk past the gate.
    --
    -- The namespace test runs on the USER name.  A `private theorem` is stored as
    -- `_private.<Module>.0.<realName>`, which is NOT prefixed by `ClassicalLean`, so
    -- testing the raw name silently exempted every private declaration in the library
    -- — measured: 89 of 625 theorem constants, including real private lemmas such as
    -- `lucas_doubling_aux` and `sqrt5_isIntegral`.  A private theorem proved by
    -- `native_decide` or `sorry` would have walked straight past this gate.
    unless targets.any (fun ns => ns.isPrefixOf (privateToUserName n)) do continue
    match ci with
    | .thmInfo _ =>
      let axs ← collectAxioms n
      let offending := axs.filter (fun a => !permitted n a)
      if !offending.isEmpty then
        bad := bad.push (n, offending)
    | _ => pure ()
  return bad

/-- Every theorem constant under `targets`, for the count reported on success. -/
def theoremCount : CommandElabM Nat := do
  let env ← getEnv
  let mut k := 0
  for (n, ci) in env.constants.toList do
    if n.hasMacroScopes then continue
    unless targets.any (fun ns => ns.isPrefixOf (privateToUserName n)) do continue
    match ci with
    | .thmInfo _ => k := k + 1
    | _ => pure ()
  return k

end AxiomGate

run_cmd do
  let bad ← AxiomGate.scan
  let total ← AxiomGate.theoremCount
  if bad.isEmpty then
    -- A scoped exception is a theorem resting on a named project axiom.  Reporting the
    -- count as if it were a subset of the trio would be exactly the overclaim this gate
    -- exists to prevent, so the pass message names the exceptions when there are any.
    let exc := AxiomGate.scopedExceptions
    let note :=
      if exc.isEmpty then "; 0 scoped exceptions"
      else s!"\n  {exc.length} scoped exception(s), each a named theorem resting on a named \
project axiom: {exc.map (fun (t, a) => s!"{t} ← {a}")}"
    logInfo s!"axiom gate PASS — {total} theorem constant(s) under {AxiomGate.targets}, \
every one depending only on a subset of {AxiomGate.allowed}{note}"
  else
    let rows := bad.toList.map (fun (n, axs) => s!"{n}  ←  {axs.toList}")
    throwError s!"axiom gate FAIL — {bad.size} of {total} theorem(s) depend on a disallowed axiom:\n  \
{String.intercalate "\n  " rows}\n\n\
Allowed: {AxiomGate.allowed} (any subset; a theorem proved by rfl/decide uses none of them).\n\
An axiom named `…_native.native_decide.ax…` (or `Lean.ofReduceBool` / `Lean.trustCompiler` on older \
toolchains) means a `native_decide` proof — the compiler checked it, not the kernel. `sorryAx` means \
an admitted proof. Replace the proof, or move the declaration to a module this gate does not police."
