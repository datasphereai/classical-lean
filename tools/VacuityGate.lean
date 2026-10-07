import Lean
import ClassicalLean

/-!
# Vacuity gate

A semantic guard against the failure mode that no build and no axiom check can
see: a theorem whose **statement asserts nothing**. A declaration of the form

```
theorem foo : True := trivial
theorem bar (h : P) : P := h
```

builds green, is `sorry`-free, and passes the axiom gate with a perfectly clean
footprint — while proving no property at all. `lake build` and `#print axioms`
both say yes. This says no.

`lake env lean tools/VacuityGate.lean` exits 0 when clean; a nonzero exit names
the offending declarations.

Detected:

1. conclusion is `True`;
2. conclusion is definitionally equal to one of the theorem's own `Prop`
   hypotheses (`P → P`, `∀ h : P, P`, tautologies proved by `id`).

**Known limitation, stated rather than hidden:** a predicate that is
*semantically* always true — an always-satisfiable definition dressed as a
hypothesis — is not detected. Proving a predicate constant is undecidable in
general, so that case has to be caught in review. The two forms above cover the
bulk of what goes wrong in machine-assisted proof production.

Adapted from a checker written for the retired Mathlib-free corpus, where it was
introduced after a run of green-but-empty theorems. The adaptation is the target
namespace and this header; the detection logic is unchanged because it was
right.
-/

open Lean Lean.Meta Lean.Elab.Command

namespace VacuityGate

/-- Namespaces policed by this gate. -/
def targets : List Name := [`ClassicalLean]

/-- Is the conclusion of the shape `∃ y, y = e` (or `∃ y, e = y`) with `e` not mentioning
    `y`?  Such a statement is provable by `⟨e, rfl⟩` for *any* `e`, so it asserts nothing about
    `e`: "there exists a value equal to `f x`" is true of every function and every argument.
    Measured in the wild, dressed as a named law about self-reference. -/
def isTrivialExists (concl : Expr) : Bool :=
  match concl with
  | .app (.app (.const ``Exists _) _) (.lam _ _ body _) =>
    match body with
    | .app (.app (.app (.const ``Eq _) _) lhs) rhs =>
      (lhs == .bvar 0 && !rhs.hasLooseBVars) || (rhs == .bvar 0 && !lhs.hasLooseBVars)
    | _ => false
  | _ => false

/-- A statement is *vacuous* if any of the following hold.

    1. Its conclusion is `True`.
    2. Its conclusion is defeq to one of its own `Prop` hypotheses — a `P → P` tautology.
    3. Its conclusion is defeq to an *instantiation* of a universally quantified `Prop`
       hypothesis. This is case 2 one step out: from `h : ∀ a, P a` the statement `P a` is
       proved by `h a` and asserts nothing the hypothesis did not. The two-rule version of this
       gate missed that shape, which is how it read `(∀ X S s, observed X S s ≥ psi S s) →
       observed X S s ≥ psi S s` as a theorem.
    4. Its conclusion is `∃ y, y = e` with `e` independent of `y` — see `isTrivialExists`.

    Known limitation, stated rather than hidden: a statement that is true but carries no
    information about its subject — `0 ≤ f x` for `f` valued in `Nat`, say — is not
    detected, because being uninformative is not a syntactic property. That case has to be
    caught in review. -/
def isVacuousType (type : Expr) : MetaM Bool :=
  forallTelescopeReducing type fun xs concl => do
    if concl.isConstOf ``True then return true
    if isTrivialExists concl then return true
    for x in xs do
      let t ← inferType x
      if (← isProp t) then
        -- case 2: the hypothesis itself.
        if (← isDefEq t concl) then return true
        -- case 3: some instantiation of it.  `forallMetaTelescope` opens the hypothesis's
        -- leading `∀`s as metavariables; if the body then unifies with the conclusion, the
        -- theorem is `h` applied to whatever those metavariables were solved to.
        let (_, _, body) ← forallMetaTelescope t
        if body != t then
          if (← isProp body) then
            if (← isDefEq body concl) then return true
    return false

/-- Scan the target namespaces; return the vacuous theorem names. -/
def scan : CommandElabM (Array Name) := do
  let env ← getEnv
  let mut bad : Array Name := #[]
  for (n, ci) in env.constants.toList do
    match ci with
    | .thmInfo ti =>
      -- Skip only compiler/macro-generated declarations. `isInternal` is NOT
      -- used, because it also skips user theorems whose name starts with `_`,
      -- which would let a leading underscore bypass the gate. Auto-generated
      -- equation and projection lemmas (`.eq_1`, `.injEq`, …) have real
      -- equality conclusions, so the vacuity test never matches them.
      if n.hasMacroScopes then continue
      -- On the USER name: a `private theorem` is stored as `_private.<Module>.0.<name>`,
      -- which no `ClassicalLean` prefix test matches, so testing the raw name would exempt
      -- every private declaration — the same hole that was measured in `AxiomGate`.
      if targets.any (fun ns => ns.isPrefixOf (privateToUserName n)) then
        if ← liftTermElabM (isVacuousType ti.type) then
          bad := bad.push n
    | _ => pure ()
  return bad

end VacuityGate

run_cmd do
  let bad ← VacuityGate.scan
  if bad.isEmpty then
    logInfo s!"vacuity gate PASS — no vacuous theorems in {VacuityGate.targets}"
  else
    let names := String.intercalate "\n  " (bad.toList.map toString)
    throwError s!"vacuity gate FAIL — {bad.size} vacuous theorem(s):\n  {names}\n\n\
A statement is vacuous here if its conclusion is `True`; is one of its own hypotheses \
(`P → P`); is an instance of a universally quantified hypothesis (`(∀ a, P a) → P a`, proved \
by applying the hypothesis); or is `∃ y, y = e` with `e` independent of `y` (provable by \
`⟨e, rfl⟩` for any `e`).\n\
Such a theorem builds green and is sorry-free while proving nothing. State a real conclusion \
over real objects, or delete it."
