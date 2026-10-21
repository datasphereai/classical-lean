import Lean
import ClassicalLean.InformationTheory.ChannelCapacity

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

Detected (see `isVacuousType`):

* the **fixed test**, cases 1 to 5 of `isVacuousType`: (1) the conclusion is `True`; (2) it is
  one of the theorem's own hypotheses (`P → P`); (3) it follows from one hypothesis by applying
  it, with that hypothesis's own premises met by the theorem's other hypotheses
  (`(∀ a, P a) → P a`, `(S ⊆ T) → x ∈ S → x ∈ T`); (4) it is `∃ y, y = e` with `e` independent
  of `y`; (5) it is an `∧`, an `↔` or another structure whose type is a proposition, every part
  of which is `True` or closed by one hypothesis (Dustin's ruling of 2026-10-11);
* the **old case 3**, kept by ruling: the conclusion of a `∀` hypothesis unifies with the
  conclusion, whatever that hypothesis's premises (`oldCase3`);
* **rule 5** (order VACUITY-2): the hypotheses contradict each other: one of a short fixed list
  of closing tactics proves `False` from them (`rule5`), within its own heartbeat budget.

The gate flags a theorem when any of these fires and says which. Every flag of the fixed test and
of rule 5 stands for a proof, checked by the kernel (`kernelCheck`); the old
case 3 builds no proof, and its flags say `old case 3 only` where nothing else fired. The known
limits are listed in the docstring of `isVacuousType`.

A theorem flagged here can still pass when it is on the reviewed list
`tools/vacuity_reviewed.txt` under its name **and the hash of its statement** (see `Entry`); a
change to the statement drops it off the list. Entries marked `VACUOUS-PENDING` are printed on
every run.

**Known limitation, stated rather than hidden:** a predicate that is
*semantically* always true — an always-satisfiable definition dressed as a
hypothesis — is not detected. Proving a predicate constant is undecidable in
general, so that case has to be caught in review. The forms above cover the
bulk of what goes wrong in machine-assisted proof production.

Adapted from a checker written for the retired Mathlib-free corpus, where it was
introduced after a run of green-but-empty theorems. Case 3 of `isVacuousType` was rewritten in
order VACUITY-1: it used to match the conclusion of a `∀` hypothesis without looking at that
hypothesis's premises (so it flagged real theorems), and it did not open `⊆` or a named
definition (so the same wrapping hid empty ones). Tests: `tools/VacuityGateTests.lean`, run by
`python3 -I tools/run_vacuity_tests.py`.
-/

open Lean Lean.Meta Lean.Elab.Command

namespace VacuityGate

/-- Namespaces policed by this gate. -/
def targets : List Name := [`ClassicalLean]

/-- The reviewed list, relative to the repository root (where `lake env lean` runs). -/
def reviewedPath : System.FilePath := "tools/vacuity_reviewed.txt"

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

/-! ### Case 3: the conclusion follows from one hypothesis -/

/-- At most this many levels opened, per hypothesis: `∀`s and `→`s, halves of an `∧`,
    directions of an `↔`, and heads unfolded. -/
def maxLevels : Nat := 64

/-- Open the hypothesis `pf : t` one level at a time and call `k ms pf' t'` at every level (`ms`:
    the metavariables so far; `pf'`: the proof built so far, of `t'`; `t'`: what is left),
    starting with nothing opened. A level is one of: a `∀` or `→`, opened as a metavariable
    (`pf' = pf m`); either half of an `∧` (`pf.1`, `pf.2`, order VACUITY-2); either direction of
    an `↔` (`pf.mp`, `pf.mpr`, order VACUITY-2). When `t'` is none of these, its head is unfolded
    with `whnf` at all transparency, so `@[irreducible]` definitions are opened too (order
    VACUITY-2; test `vac_irreducible`): this is how `S ⊆ T`, `Monotone f` and a named definition such as
    `NoShortGainCycle r n` are opened. One `whnf` call unfolds every nested definition down to
    the next binder or connective (six nested ones: test `vac_deep_unfold`), so no count of
    unfoldings is kept. With `dataOnly`, it stops at the first binder whose type is a
    proposition. Returns `true` as soon as `k` does; a level where `k` fails leaves no
    assignment behind. -/
partial def openLevels (pf t : Expr) (dataOnly : Bool)
    (k : Array Expr → Expr → Expr → MetaM Bool) : MetaM Bool :=
  go pf t #[] 0
where
  go (pf t : Expr) (ms : Array Expr) (depth : Nat) : MetaM Bool := do
    let s ← saveState
    if ← k ms pf t then return true
    s.restore
    if depth ≥ maxLevels then return false
    match ← instantiateMVars t with
    | .forallE _ d b _ =>
      if dataOnly && (← isProp d) then return false
      let m ← mkFreshExprMVar d
      go (mkApp pf m) (b.instantiate1 m) (ms.push m) (depth + 1)
    | t =>
      let t' ← withTransparency .all (whnf t)
      match t'.getAppFnArgs with
      | (``And, #[a, b]) =>
        if ← go (mkApp3 (mkConst ``And.left) a b pf) a ms (depth + 1) then return true
        s.restore
        go (mkApp3 (mkConst ``And.right) a b pf) b ms (depth + 1)
      | (``Iff, #[a, b]) =>
        if ← go (mkApp3 (mkConst ``Iff.mp) a b pf) (← mkArrow a b) ms (depth + 1) then
          return true
        s.restore
        go (mkApp3 (mkConst ``Iff.mpr) a b pf) (← mkArrow b a) ms (depth + 1)
      | _ => if t'.isForall then go pf t' ms (depth + 1) else return false

/-- Prove the goal `g` (a metavariable whose type is a proposition) from the hypotheses
    `locals`, then run `k`; try another proof of `g` when `k` fails. A proof is one of:
    an instance found by instance search; one hypothesis, instantiated at its variables but not
    at its premises (no chains of hypotheses), or a half of it when it is an `∧`; `True.intro`; `⟨_, _⟩` for `∧` and `∃` with each
    part proved the same way; `Or.inl` or `Or.inr` for `∨`; `rfl` when the two sides are definitionally equal; `decide` for a
    closed proposition (no free variables) that evaluates to `true`. -/
partial def solve (locals : Array Expr) (g : Expr) (k : MetaM Bool) : MetaM Bool := do
  let gid := g.mvarId!
  if ← gid.isAssigned then return ← k
  let p ← instantiateMVars (← inferType g)
  let s ← saveState
  if (← isClass? p).isSome then
    try
      gid.assign (← synthInstance p)
      if ← k then return true
    catch _ => pure ()
    s.restore
  for l in locals do
    let lt ← inferType l
    if ← isProp lt then
      let found ← openLevels l lt true fun _ pf ty => do
        if ← isDefEq ty p then
          gid.assign pf
          k
        else return false
      if found then return true
  let p' ← whnf p
  match p'.getAppFnArgs with
  | (``True, #[]) =>
    gid.assign (mkConst ``True.intro)
    if ← k then return true
  | (``And, #[a, b]) =>
    let ga ← mkFreshExprMVar a
    let gb ← mkFreshExprMVar b
    gid.assign (mkApp4 (mkConst ``And.intro) a b ga gb)
    if ← solve locals ga (solve locals gb k) then return true
  | (``Or, #[a, b]) =>
    let ga ← mkFreshExprMVar a
    gid.assign (mkApp3 (mkConst ``Or.inl) a b ga)
    if ← solve locals ga k then return true
    s.restore
    let gb ← mkFreshExprMVar b
    gid.assign (mkApp3 (mkConst ``Or.inr) a b gb)
    if ← solve locals gb k then return true
  | (``Exists, #[α, f]) =>
    let w ← mkFreshExprMVar α
    let gb ← mkFreshExprMVar (f.beta #[w])
    gid.assign (mkApp4 (mkConst ``Exists.intro p'.getAppFn.constLevels!) α f w gb)
    if ← solve locals gb k then return true
  | (``Eq, #[α, a, b]) =>
    if ← isDefEq a b then
      gid.assign (mkApp2 (mkConst ``Eq.refl p'.getAppFn.constLevels!) α a)
      if ← k then return true
  | _ =>
    if !p.hasFVar && !p.hasMVar then
      try
        let d ← mkDecide p
        if (← withAtLeastTransparency .default (whnf d)).isConstOf ``true then
          gid.assign (← mkDecideProof p)
          if ← k then return true
      catch _ => pure ()
  s.restore
  return false

/-- Give a value to a metavariable that no step fixed: an instance, a hypothesis of its type,
    or `default` when the type is `Inhabited`. -/
def fill (locals : Array Expr) (m : MVarId) : MetaM Bool := do
  let ty ← instantiateMVars (← m.getType)
  if (← isClass? ty).isSome then
    try
      m.assign (← synthInstance ty)
      return true
    catch _ => return false
  for l in locals do
    let s ← saveState
    if ← isDefEq (← inferType l) ty then
      m.assign l
      return true
    s.restore
  try
    let inst ← synthInstance (← mkAppM ``Inhabited #[ty])
    m.assign (← mkAppOptM ``Inhabited.default #[some ty, some inst])
    return true
  catch _ => return false

/-- Finish a candidate proof `pf` of `concl`: every metavariable left must be data (a premise
    left open means the candidate fails), filled by `fill`; then the proof term is checked by
    `Meta.check` and its type compared with the conclusion. Only a proof that passes both counts,
    so a flag from case 3 always stands for an actual proof term made of hypotheses; the proof is
    put in `found`, and `judge` sends it to the kernel as well (order VACUITY-2). -/
def finish (locals : Array Expr) (pf concl : Expr) (found : IO.Ref (Option Expr)) :
    MetaM Bool := do
  for m in ← getMVars (← instantiateMVars pf) do
    if ← m.isAssigned then continue
    if ← isProp (← m.getType) then return false
    unless ← fill locals m do return false
  let pf ← instantiateMVars pf
  if pf.hasMVar then return false
  -- at all transparency, as `openLevels` unfolds: `h a` for `h : IWrap P` with `IWrap`
  -- irreducible is a function application only once `IWrap` is unfolded (test `vac_irreducible`)
  try
    let ok ← withTransparency .all do
      check pf
      isDefEq (← inferType pf) concl
    if ok then found.set (some pf)
    return ok
  catch _ => return false

/-- Prove each goal in `gs` in turn by `solve`, backing up when a later one fails. -/
def solveAll (locals : Array Expr) : List Expr → MetaM Bool → MetaM Bool
  | [], k => k
  | g :: gs, k => solve locals g (solveAll locals gs k)

/-- Cases 2 and 3: does `concl` follow from one hypothesis `x` among `xs`, by applying it?
    `x` is opened level by level (`openLevels`, which unfolds `⊆` and named definitions and opens
    `∧` and `↔`); at a
    level whose rest is definitionally equal to `concl`, every premise opened so far must be
    proved from `xs` by `solve` and the result checked by `finish`. With nothing opened this is
    case 2, the conclusion being a hypothesis. -/
def followsFromHyp (xs : Array Expr) (concl : Expr) : MetaM (Option Expr) := do
  let proof ← IO.mkRef none
  for x in xs do
    let t ← inferType x
    if ← isProp t then
      let found ← openLevels x t false fun ms pf body => do
        unless ← isDefEq body concl do return false
        let prems ← ms.filterM fun m => do
          return !(← m.mvarId!.isAssigned) && (← isProp (← inferType m))
        solveAll xs prems.toList (finish xs pf concl proof)
      if found then return ← proof.get
  return none

/-- Unfold the head of `e` by definitions only, without computing: stops at `ite`, `dite`, `cond`
    and `decide`, so `Small 3` for `Small n := if n < 10 then True else False` stays an `ite`
    and is not read as `True`, while `Triv := True` is (cold review r3, finding 2). `whnfCore`
    runs with `iota := false` (`Meta.Config`), so it reduces no `match` and no recursor, and
    `Small2 0` for `Small2` defined by cases stays a `match` (order LEAN-27, job 0; under the
    default `smartUnfolding` option, `unfoldDefinition?` does not unfold a matcher either).
    Limit, on the strict side: only the `whnfCore` call runs with `iota := false`; the
    `unfoldDefinition?` call below runs with `iota` on, and for a definition by structural
    recursion it takes the smart-unfolding path (`_sunfold`), whose `reduceMatcher?` reduces the
    `match` (through `whnf`, which reads `iota`). So `Small3 0` for
    `Small3 | 0 => True | n + 1 => Small3 n` is still read as `True` and `P a ∧ Small3 0` is
    flagged (test `real_hyp_and_small3`, listed; a list entry, never a silent pass). Wrapping that
    call too would close it; order LEAN-27 allowed only the `whnfCore` call.
    A `match` that `whnfCore` leaves stuck (`matchMatcherApp?`) is opened branch by branch
    (`lambdaBoundedTelescope` over each alternative's `altNumParams` parameters: its pattern
    variables, and any unit thunk and `h :` equations), and each branch body is unfolded the same
    way, at most `maxLevels` matches deep (each branch keeps the same `fuel` for definitions).
    When every branch is `True` the match is read as `True`; otherwise it stays stuck (Dustin's
    ruling of 2026-10-12: nothing is computed when every branch is `True`). So `PairT x` for
    `PairT (_, _) := True` is `True` (test `vac_pair_true`), while `Small2 0`, with a `True` and a
    `False` branch, is not. Where the reading is used (`vacuousProof`, `gluedProof`), `confirmTrue`
    asks whether `True.intro` proves it: yes for a match on a constructor, or on a variable of a
    structure whose patterns are only the constructor with variable fields (`PairT`'s `(_, _)`,
    by eta); no for a variable of `ℕ`, `Bool` or another inductive, nor for `Fin 2`, whose literal
    patterns make the match go on to split the natural number inside (see `confirmTrue`; test
    `vac_unchecked_fin_true`, the confirming review of `5344c16`). When it cannot, a hypothesis
    that closes the part is tried (test `vac_hyp_and_nat_true`, flagged), and failing that the
    theorem is UNCHECKED, which fails the gate, never a pass
    (`unconfirmedMsg`; Dustin's ruling of 2026-10-13; tests `vac_unchecked_nat_true`,
    `vac_unchecked_hyp_and_nat_true`). A part with content still makes the glue fail first
    (`real_nat_true_and_work` passes). A match with no branch stays stuck. -/
partial def unfoldNamed (e : Expr) (fuel : Nat := 32) (depth : Nat := 0) : MetaM Expr := do
  let e ← withConfig (fun c => { c with iota := false }) <| whnfCore e
  if fuel == 0 then return e
  if let .const c _ := e.getAppFn then
    if [``ite, ``dite, ``cond, ``Decidable.decide].contains c then return e
  -- a `match` that `whnfCore` left stuck: `True` when every branch, its parameters bound,
  -- unfolds to `True` (Dustin's ruling of 2026-10-12, order LEAN-27 job 0); whether `True.intro`
  -- proves it is checked where the reading is used (`confirmTrue`, Dustin's ruling of 2026-10-13)
  if let some app ← matchMatcherApp? e then
    if depth ≥ maxLevels || app.alts.isEmpty then return e
    for alt in app.alts, k in app.altNumParams do
      let isTrue ← lambdaBoundedTelescope alt k fun xs body => do
        if xs.size < k then return false
        return (← unfoldNamed (mkAppN body app.remaining) fuel (depth + 1)).isConstOf ``True
      unless isTrue do return e
    return mkConst ``True
  match ← unfoldDefinition? e with
  | some e' => unfoldNamed e' (fuel - 1) depth
  | none => return e

/-- Is `e`, which `unfoldNamed` reads as `True`, `True` for Lean's `isDefEq` at `.all`, so that
    `True.intro` is a proof the kernel accepts? Measured, not a general rule: yes for a match on a
    constructor, and for a match on a variable of a structure whose patterns are only the
    constructor with variable fields, which eta reduces (`PairT`'s `(_, _)` on a pair; test
    `vac_pair_true`); no for an all-`True` match on a variable of `ℕ`, `Bool` or another inductive
    type without eta (job 0's review of `f70aa50`). Being a structure is not enough: `Fin 2`'s
    patterns `0` and `1` are literals, so its compiled match opens the structure and then splits
    the natural number inside with `Nat.casesOn`, which stays stuck on a variable (measured in
    order VACUITY-3, `#print FinT.match_1`); its all-`True` match is not confirmed (the confirming
    review of `5344c16`; test `vac_unchecked_fin_true`, order VACUITY-3's ruling 1), and such a
    theorem fails closed. -/
def confirmTrue (e : Expr) : MetaM Bool :=
  withTransparency .all (isDefEq e (mkConst ``True))

/-- The message of a theorem the fixed test reads as empty through an all-`True` match whose
    `True.intro` proof it cannot confirm: the test fails closed, so `judge` returns UNCHECKED, which
    fails the gate, never a pass (Dustin's ruling of 2026-10-13, order LEAN-27 job 0). -/
def unconfirmedMsg : String := "every case is True; kernel could not confirm the proof"

/-- Case 5, a glued conclusion (Dustin's ruling of 2026-10-11 on cold review r2's finding 3): the
    conclusion, its head unfolded, is a structure whose type is a proposition (`∧`, `↔`, or
    another such as `Fact p`), and every field of it, in turn, is closed by `True`, by one
    hypothesis (case 2, or applied as in case 3: `followsFromHyp`, whose premises may be met as
    in case 3, by `rfl` or `decide` among others), or by being glued itself. A part counts as
    `True` only when `unfoldNamed` reaches `True`, without computing. Returns the proof, the
    structure's constructor applied to the parts. A part that itself needs `rfl`, `decide`, an
    instance, computation or any other step makes it fail, so a computed fact such as
    `fib 10 = 55` or `Small 3` is not flagged (tests `real_hyp_and_computed`,
    `real_hyp_and_small`); but where a definition by structural recursion, applied to a literal or
    a constructor, reduces through smart unfolding all the way to `True` (`unfoldNamed`), the part
    is read as `True`, so `P a ∧ Small3 0` is flagged (test `real_hyp_and_small3`, listed). A
    part under a binder (`∀ x, Q x ∧ R x`, `Q a → Q a`) is not opened. At most `maxLevels`
    levels deep, so a structure that contains itself (`Loop p` with a field of type `Loop p`)
    ends (cold review r3, finding 1; test `real_loop_wrap`).
    `top`: the whole conclusion, which `vacuousProof` has already tried as one part. -/
partial def gluedProof (xs : Array Expr) (concl : Expr) (unconf : IO.Ref Bool)
    (top : Bool := true) (depth : Nat := 0) : MetaM (Option Expr) := do
  if depth ≥ maxLevels then return none
  let c ← whnf concl
  unless top do
    if (← unfoldNamed concl).isConstOf ``True then
      if ← confirmTrue concl then return some (mkConst ``True.intro)
      if let some pf ← followsFromHyp xs concl then return some pf
      -- read `True` (every case of a match is `True`), but `True.intro` is no proof the kernel
      -- accepts: the glue goes on, and `vacuousProof` fails closed if it succeeds
      unconf.set true
      return some (mkConst ``True.intro)
    if let some pf ← followsFromHyp xs concl then return some pf
  let .const sn us := c.getAppFn | return none
  unless isStructure (← getEnv) sn do return none
  let .inductInfo iv ← getConstInfo sn | return none
  let [ctor] := iv.ctors | return none
  unless iv.numIndices == 0 && c.getAppNumArgs == iv.numParams do return none
  unless ← isProp c do return none
  let mk := mkAppN (mkConst ctor us) c.getAppArgs
  let mut t ← inferType mk
  let mut parts : Array Expr := #[]
  repeat
    match ← whnf t with
    | .forallE _ d b _ =>
      let some pf ← gluedProof xs d unconf false (depth + 1) | return none
      parts := parts.push pf
      t := b.instantiate1 pf
    | _ => break
  return some (mkAppN mk parts)

/-- A statement is *vacuous* if any of the following hold.

    1. Its conclusion is `True`.
    2. Its conclusion is defeq to one of its own `Prop` hypotheses — a `P → P` tautology.
    3. Its conclusion follows from one hypothesis by applying it: from `h : ∀ a, Q a → P a` and
       `hq : Q a`, the statement `P a` is `h a hq` and asserts nothing the hypotheses did not.
       The hypothesis is opened through `⊆`, `Monotone`-style predicates and named definitions
       (`openLevels`), and *every* premise of it that the application needs must be met by the
       theorem's other hypotheses (`solve`). The version before order VACUITY-1 skipped that
       last step, so it flagged `∀ a p, par a = some p → a ∈ S → p ∈ S` against `b ∈ S`, where
       nothing gives `par ?a = some b` (an induction is needed); and it did not open `⊆` or
       named definitions, so `(h : S ⊆ T) (hx : x ∈ S) : x ∈ T` passed. Its first form, without
       instantiation, read `(∀ X S s, observed X S s ≥ psi S s) → observed X S s ≥ psi S s` as a
       theorem.
    4. Its conclusion is `∃ y, y = e` with `e` independent of `y` — see `isTrivialExists`.
    5. Its conclusion is glued from hypotheses: an `∧`, an `↔` or another structure whose type
       is a proposition, every part of which is `True` or closed by one hypothesis as in cases
       2 and 3 (`gluedProof`; Dustin's ruling of 2026-10-11).

    Known limitations of the whole gate (the fixed test, the old case 3 and rule 5), stated
    rather than hidden; they have to be caught in review. As they stand after order LEAN-27's
    job 0 (order VACUITY-3 corrected this text and changed no verdict):

    * a statement that is true but carries no information about its subject — `0 ≤ f x` for
      `f` valued in `Nat`, say — is not detected: being uninformative is not a syntactic
      property;
    * contradictory hypotheses that rule 5's tactics (`contradiction`, `linarith`, `omega`,
      `norm_num`, `decide`, within `rule5Heartbeats`) do not refute are not detected; nor are
      contradictions when no hypothesis is a proposition (`(e : Empty) : F 0`), since rule 5
      runs only when one is;
    * a closed premise that `decide` cannot finish (`Nat.Prime 1000003`) makes the fixed test
      run out: the theorem is UNCHECKED, which fails the gate (it fails closed, a false alarm for
      a real theorem of that shape), unless the old case 3 flags it, which it does when the
      hypothesis is a plain `∀`;
    * a conclusion that needs two hypotheses chained (`h (hq hr)`, how real lemmas such as
      `Monotone.comp` are proved), or a premise that is true for every value but not by `rfl` or
      `decide` (`0 + n = n`), is caught only by the old case 3, so only when the hypothesis is a
      plain `∀` (its `∀`s written out); inside `⊆`, a named definition, `∧` or `↔` it is missed;
    * a `_proof_` lemma with no source position that some declaration uses is skipped
      (`isTacticHelper`), so a theorem added under such a name by meta code (`addDecl`) and used
      by another declaration is not tested;
    * (cold review r2, narrowed by case 5) a conclusion glued from hypotheses is detected only
      when it is an `∧`, an `↔` or another structure whose type is a proposition, and every part
      is `True` or closed by one hypothesis; a part that itself needs `rfl`, `decide`, an
      instance, computation or any other step makes the theorem pass, so a computed fact is
      not flagged (`(h : P a) : P a ∧ 2 + 2 = 4`, test `real_hyp_and_computed`), except where
      a definition by structural recursion, applied to a literal or a constructor, reduces
      through smart unfolding all the way to `True` (`unfoldNamed`): `P a ∧ Small3 0` is flagged
      (the strict side; test `real_hyp_and_small3`, listed; order LEAN-27, job 0); a part under
      a binder is not opened (`P a ∧ ∀ x, Q x ∧ R x` with each piece a hypothesis, or
      `P a ↔ Q a` from `P a` and `Q a`, pass; cold review r3, finding 3); and a conclusion
      glued with `∨` or `∃` (`Or.inl hp`, `⟨a, hp⟩`) is not detected;
    * (cold review r2) rule 5 reads the statement as written, with no unfolding, so the same
      fact can be read two ways: `p → False` as a conclusion is opened (its conclusion is `False`
      and rule 5 does not run), `¬ p` is not; a `∀ x ∈ [], F x` written out is an empty-premise
      helper that rule 5 flags (test `real_forall_mem_nil`, listed), while the same `∀` inside a
      definition (`PredicateStack.admits_nil`) is not read;
    * (cold review r2) the scan selects theorems by the namespace `ClassicalLean`, not by module,
      so a theorem a library module declares in another namespace is not tested; measured at
      VACUITY-2: 5 such theorems, all generated equation lemmas (`harmonic.eq_1` and the like);
    * (order LEAN-27, job 0) an all-`True` `match` is read as `True` (`unfoldNamed`), but where
      `True.intro` cannot be confirmed as its proof (`confirmTrue`: a match on a variable of `ℕ`,
      `Bool` or another inductive without eta, and `Fin 2`'s match too), the theorem is UNCHECKED
      unless a hypothesis closes that part (it fails closed; tests `vac_unchecked_nat_true`,
      `vac_unchecked_hyp_and_nat_true`, and `vac_unchecked_fin_true` for `Fin 2`, after the
      confirming review of `5344c16`); a chain of all-`True` matches costs about `kᵈ` calls,
      bounded by the heartbeat budget (worst case UNCHECKED);
    * (the confirming review of `5344c16`) a **recursive** all-`True` predicate
      (`NatT2 | 0 => True | n + 1 => NatT2 n`) is not read as `True`, so `∀ n, NatT2 n` passes
      silently; catching it needs induction and its own ruling. `tools/UninformativeReport.lean`
      lists every recursive Prop-valued definition of the library for a human (its section C;
      none at order VACUITY-3).

    Flagged on purpose, not a limit: a lemma that is a projection, the identity, or (case 5) a
    pairing of its hypotheses once its definitions and instances are unfolded (`S ∩ T ⊆ S`,
    `Monotone id`, `a < b → a + 1 ≤ b` on `ℕ`, `x ∈ S → x ∈ T → x ∈ S ∩ T`, and
    `a ≤ c → b ≤ d → (a, b) ≤ (c, d)`, the shape of `Prod.mk_le_mk`). The fixed
    test opens the conclusion as well as the hypotheses (test `vac_concl_subset`), so such a
    lemma is flagged and stays only through a reviewed-list entry, as
    `Simplex.orderedSimplex_subset_closedSimplex` does.

    Tests: `tools/VacuityGateTests.lean`.

    `vacuousProof` returns the statement with its hypotheses abstracted and a closed proof of it
    (`True.intro`, `⟨e, rfl⟩`, or the proof `followsFromHyp` built), which `judge` sends to the
    kernel (`kernelCheck`). -/
def vacuousProof (type : Expr) : MetaM (Option (Expr × Expr)) :=
  forallTelescopeReducing type fun xs concl => do
    -- the proof is closed over the hypotheses and checked against the theorem's own statement
    -- `type` (cold review r2, finding 7), which the kernel unfolds as needed
    let close (pf : Expr) : MetaM (Option (Expr × Expr)) := do
      return some (type, ← mkLambdaFVars xs pf)
    -- cases 1 and 4 also on the conclusion with its head unfolded by definitions, without
    -- computing, so `True` or `∃ y, y = e` behind a named definition is seen (cold review r2,
    -- finding 4) and a computed fact is not read as `True` (cold review r3, finding 2)
    let c' ← unfoldNamed concl
    if concl.isConstOf ``True then return ← close (mkConst ``True.intro)
    if c'.isConstOf ``True then
      if ← confirmTrue concl then return ← close (mkConst ``True.intro)
      if let some pf ← followsFromHyp xs concl then return ← close pf
      throwError unconfirmedMsg
    for c in [concl, c'] do
      if isTrivialExists c then
        if let .app (.app (.const ``Exists us) α) f@(.lam _ _ (.app (.app _ lhs) rhs) _) := c then
          let e := if lhs == .bvar 0 then rhs else lhs
          return ← close (mkApp4 (mkConst ``Exists.intro us) α f e (mkApp2 (mkConst ``Eq.refl us) α e))
    if let some pf ← followsFromHyp xs concl then return ← close pf
    -- case 5, checked as `finish` checks case 3, then by the kernel in `judge`
    let unconf ← IO.mkRef false
    let some pf ← gluedProof xs concl unconf | return none
    if ← unconf.get then throwError unconfirmedMsg
    let ok ← try withTransparency .all do
        check pf
        isDefEq (← inferType pf) concl
      catch _ => pure false
    if ok then close pf else return none

/-- The fixed test as a yes or no (the test runner's template for older gates calls it). -/
def isVacuousType (type : Expr) : MetaM Bool := return (← vacuousProof type).isSome

/-- What the kernel said about the proof behind a flag. -/
inductive KernelCheck
  | accepted
  /-- the kernel refused the proof, a term the gate built and believed correct (for the fixed
      test: checked before by `Meta.check` in `finish` in cases 2 and 3, by `check` in
      `vacuousProof` in case 5, by `isDefEq` in case 1, and not at all in case 4; for rule 5,
      built by a tactic); a resource limit is `notChecked`, below, not this -/
  | rejected (msg : String)
  /-- the kernel stopped on a resource limit (its heartbeats, memory, recursion depth) or was
      interrupted: the proof was not checked, which says nothing against it -/
  | notChecked (msg : String)

/-- The kernel's check of a flag's proof (order VACUITY-2): the proof `pf` of the statement `ty`
    is added as a theorem to a copy of the environment, which is then dropped, so nothing is
    added. `Meta.check` (in `finish`) is the elaborator's checker; the kernel is the part of Lean
    every proof finally answers to. A kernel time-out is `notChecked`, not `rejected`: a check
    with rule 5's budget set to 1 heartbeat showed "(kernel) deterministic timeout" coming back
    as a rejection before this was split. -/
def kernelCheck (lps : List Name) (ty pf : Expr) : CoreM KernelCheck := do
  let decl := Declaration.thmDecl
    { name := `_vacuityGate_kernelCheck, levelParams := lps, type := ty, value := pf }
  match (← getEnv).toKernelEnv.addDecl (← getOptions) decl with
  | .ok _ => return .accepted
  | .error e =>
    let m := (← (e.toMessageData (← getOptions)).toString).splitOn "\n" |>.head!
    match e with
    | .deterministicTimeout | .excessiveMemory | .deepRecursion | .interrupted =>
      return .notChecked m
    | _ => return .rejected m

/-! ### Rule 5: contradictory hypotheses (order VACUITY-2) -/

/-- Rule 5's own heartbeat budget per theorem, apart from the fixed test's: the gate's budget
    before VACUITY-1. All of rule 5's tactics share it, so a slow rule 5 cannot starve the fixed
    test into UNCHECKED, and adds at most this much work per theorem. -/
def rule5Heartbeats : Nat := 400000

/-- The closing tactics rule 5 tries, in this order. `norm_num` is run `at *`, so that it reads
    the hypotheses; on the goal `False` alone it can do nothing. -/
def rule5Tactics : Lean.Elab.Term.TermElabM (Array (TSyntax `tactic)) := do
  return #[← `(tactic| contradiction), ← `(tactic| linarith), ← `(tactic| omega),
    ← `(tactic| norm_num at *), ← `(tactic| decide)]

/-- Rule 5: do the theorem's hypotheses contradict each other? The hypotheses are the binders
    written in the statement, opened **without unfolding** (`forallTelescope`): unfolding would
    also open the conclusion, and `v ≠ 0` would become a hypothesis `v = 0` that rule 5 refutes
    (the first library run flagged four real theorems so, among them
    `Simplex.single_one_ne_zero`; tests `real_ne_zero_concl`, `real_not_mem_nil`). Rule 5 runs
    only when a hypothesis is a proposition and the conclusion is not `False`: a theorem whose
    conclusion is `False` states that its hypotheses contradict (test `real_false_concl`). It
    tries each of `rule5Tactics` on the goal `False` with the hypotheses in context. A proof found (complete, no `sorry`) is closed over the hypotheses,
    `∀ xs, False`, and sent to the kernel (`kernelCheck`) before the tactic's state is dropped.
    Returns `none` when no tactic closed the goal, and the kernel's answer when one did. Running
    out of heartbeats is not caught here: it ends the search, and `judge` reports it. -/
def rule5 (lps : List Name) (type : Expr) : Lean.Elab.Term.TermElabM (Option KernelCheck) :=
  forallTelescope type fun xs concl => do
    if concl.isConstOf ``False then return none
    unless ← xs.anyM (fun x => do isProp (← inferType x)) do return none
    for tac in ← rule5Tactics do
      let s ← Lean.Elab.Term.saveState
      let r ← try
          let g ← mkFreshExprMVar (mkConst ``False)
          let rest ← Lean.Elab.Term.withoutErrToSorry <|
            Lean.Elab.Tactic.run g.mvarId! (Lean.Elab.Tactic.evalTactic tac)
          Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
          let pf ← instantiateMVars g
          if !rest.isEmpty || pf.hasMVar || pf.hasSorry then pure none
          else
            let ty ← mkForallFVars xs (mkConst ``False)
            pure (some (← kernelCheck lps ty (← mkLambdaFVars xs pf)))
        catch e => if e.isRuntime then throw e else pure none
      s.restore
      if r.isSome then return r
    return none

/-- The old case 3, kept beside the fixed test by ruling during order VACUITY-1, so the gate
    catches everything it caught before. The conclusion of a hypothesis whose leading `∀`s are
    opened as metavariables (no unfolding) unifies with the theorem's conclusion; the
    hypothesis's premises are **not** looked at. So it also flags real theorems whose premise no
    hypothesis gives (old `Tremaux.anc_mem`) and chains (`h (hq hr)`); those can stay only through
    the reviewed list. Unchanged from `416a90d`. -/
def oldCase3 (type : Expr) : MetaM Bool :=
  forallTelescopeReducing type fun xs concl => do
    for x in xs do
      let t ← inferType x
      if (← isProp t) then
        let (_, _, body) ← forallMetaTelescope t
        if body != t then
          if (← isProp body) then
            if (← isDefEq body concl) then return true
    return false

/-! ### The reviewed list -/

namespace SHA256
/-- The 64 round constants of SHA-256 (FIPS 180-4, section 4.2.2). -/
def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- SHA-256 of `msg`, as 64 lowercase hex digits. -/
def hex (msg : ByteArray) : String := Id.run do
  let mut b := msg.push 0x80
  while b.size % 64 != 56 do b := b.push 0
  let bits : UInt64 := msg.size.toUInt64 * 8
  for i in [0:8] do b := b.push (bits >>> (8 * (7 - i)).toUInt64).toUInt8
  let mut h : Array UInt32 := #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
  for c in [0:b.size / 64] do
    let mut w : Array UInt32 := #[]
    for i in [0:16] do
      let o := 64 * c + 4 * i
      w := w.push ((b[o]!.toUInt32 <<< 24) ||| (b[o+1]!.toUInt32 <<< 16) |||
        (b[o+2]!.toUInt32 <<< 8) ||| b[o+3]!.toUInt32)
    for i in [16:64] do
      let s0 := rotr w[i-15]! 7 ^^^ rotr w[i-15]! 18 ^^^ (w[i-15]! >>> 3)
      let s1 := rotr w[i-2]! 17 ^^^ rotr w[i-2]! 19 ^^^ (w[i-2]! >>> 10)
      w := w.push (w[i-16]! + s0 + w[i-7]! + s1)
    let mut v := h
    for i in [0:64] do
      let S1 := rotr v[4]! 6 ^^^ rotr v[4]! 11 ^^^ rotr v[4]! 25
      let ch := (v[4]! &&& v[5]!) ^^^ (~~~v[4]! &&& v[6]!)
      let t1 := v[7]! + S1 + ch + K[i]! + w[i]!
      let S0 := rotr v[0]! 2 ^^^ rotr v[0]! 13 ^^^ rotr v[0]! 22
      let maj := (v[0]! &&& v[1]!) ^^^ (v[0]! &&& v[2]!) ^^^ (v[1]! &&& v[2]!)
      let t2 := S0 + maj
      v := #[t1 + t2, v[0]!, v[1]!, v[2]!, v[3]! + t1, v[4]!, v[5]!, v[6]!]
    h := (h.zip v).map fun (x, y) => x + y
  let digit (x : UInt32) : String :=
    let s := String.ofList (Nat.toDigits 16 x.toNat)
    "".pushn '0' (8 - s.length) ++ s
  return String.join (h.toList.map digit)
end SHA256

/-- The hash that the reviewed list keys on: SHA-256 of the elaborated statement, printed in
    full by `Expr.dbgToString`. Any change to the statement, a binder name included, changes it. -/
def statementHash (type : Expr) : String := SHA256.hex type.dbgToString.toUTF8

/-- One line of the reviewed list: `<full name> <sha256 of the statement> <kind> <reason>`, where
    kind is `HELPER` (a deliberate helper that applies a hypothesis) or `VACUOUS-PENDING` (proves
    nothing beyond its hypothesis; listed only so the library passes until a later order deals
    with it, and printed on every run). Lines starting with `#` and blank lines are skipped. -/
structure Entry where
  name : Name
  hash : String
  pending : Bool
  reason : String

def parseList (text : String) : Except String (Array Entry) := do
  let mut out := #[]
  for (line, i) in text.splitOn "\n" |>.zipIdx do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn " " with
    | n :: h :: kind :: reason =>
      unless h.length == 64 do throw s!"line {i + 1}: the hash must have 64 hex digits"
      let pending ← match kind with
        | "HELPER" => pure false
        | "VACUOUS-PENDING" => pure true
        | _ => throw s!"line {i + 1}: kind must be HELPER or VACUOUS-PENDING"
      if reason.isEmpty then throw s!"line {i + 1}: a reason is needed"
      out := out.push ⟨n.toName, h, pending, " ".intercalate reason⟩
    | _ => throw s!"line {i + 1}: expected <name> <sha256> <kind> <reason>"
  return out

def loadList (path : System.FilePath) : IO (Array Entry) := do
  unless ← path.pathExists do return #[]
  match parseList (← IO.FS.readFile path) with
  | .ok es => return es
  | .error e => throw <| IO.userError s!"{path}: {e}"

/-- What the gate says about one theorem. -/
inductive Verdict
  | pass
  /-- flagged and not on the list (or on it under another statement) -/
  | flag (hash : String) (listedUnder : Option String) (why : String)
  | listed (e : Entry) (why : String)
  /-- the fixed test, or `judge` itself, did not finish, and the old case 3 did not flag the
      theorem (rule 5 is then not run); fails the gate, never a pass. `msg` is the first line of
      the reason. Every path to it (order VACUITY-3): the fixed test runs out of its heartbeat
      budget; it reads an all-`True` match whose `True.intro` proof it cannot confirm
      (`unconfirmedMsg`); the kernel stops on a resource limit while it checks the fixed test's
      proof (`KernelCheck.notChecked`, re-thrown in `judge`); any other exception from the fixed
      test; and, in `scan`, any exception that `judge` throws outside its own `try`, such as the
      old case 3 running out. When the old case 3 fired, the first four give a flag instead,
      labelled `old case 3 only (fixed test UNCHECKED: …)` unless rule 5 also fired (then
      `old case 3 + rule 5`, and the fixed test's message is dropped; a kernel rejection of rule
      5's proof gives KERNEL-REJECTED). Rule 5 running out never gives it:
      that is counted apart. -/
  | unchecked (msg : String)
  /-- the kernel refused the proof behind a flag, a term the gate built and believed correct
      (see `KernelCheck.rejected` for what checked it before); fails the gate (order VACUITY-2).
      A kernel that stops on a resource limit is not this verdict but `KernelCheck.notChecked`,
      which `judge` treats as the test not finishing. -/
  | kernelRejected (why : String) (msg : String)

/-- Flagged when the old case 3, the fixed test (cases 1 to 5, `vacuousProof`) **or** rule 5
    (`rule5`) flags it; `why` says which fired. A flag of the fixed test or of rule 5 stands only
    once the kernel accepts its proof (`kernelCheck`); a rejection is its own verdict, and a
    kernel that stops on a resource limit counts as the test running out. The old
    case 3 builds no proof, so its flags carry the label `old case 3 only` where no other test
    fired. Each test runs in its own `liftTermElabM` (its own heartbeat count); rule 5's budget
    is `rule5Heartbeats`. At this level `try` also catches running out of heartbeats: if the
    fixed test does not finish (it runs out, cannot confirm an all-`True` reading, or throws; see
    `Verdict.unchecked`), the theorem is still flagged when the old case 3 fired, and is
    UNCHECKED otherwise. Such a flag is labelled `old case 3 only (fixed test UNCHECKED: …)`
    (`old case 3 + rule 5` when rule 5 fired too), and that label can sit on an empty theorem:
    the fixed test, which might have proved the theorem empty, did not finish, so
    `old case 3 only` does not mean that only the old case 3 would have fired (order VACUITY-3).
    If rule 5 runs out, that is returned beside the verdict (the second
    part): the gate prints it and counts it, and does not fail on it, since rule 5 is an
    incomplete search and running out tells no more than finding nothing. -/
def judge (list : Array Entry) (n : Name) (type : Expr) :
    CommandElabM (Verdict × Option String) := do
  let lps := (← getConstInfo n).levelParams
  let old ← liftTermElabM (oldCase3 type)
  let mut fixed := false
  let mut fixedOut : Option String := none
  try
    if let some (ty, pf) ← liftTermElabM (vacuousProof type) then
      match ← liftCoreM (kernelCheck lps ty pf) with
      | .accepted => fixed := true
      | .rejected m => return (.kernelRejected "fixed test" m, none)
      | .notChecked m => throwError m
  catch e =>
    let m := (← e.toMessageData.toString).splitOn "\n" |>.head!
    unless old do return (.unchecked m, none)
    fixedOut := some m
  let mut r5 := false
  let mut ranOut : Option String := none
  try
    let r ← withScope (fun s => { s with opts := maxHeartbeats.set s.opts rule5Heartbeats }) <|
      liftTermElabM (rule5 lps type)
    match r with
    | some .accepted => r5 := true
    | some (.rejected m) => return (.kernelRejected "rule 5" m, none)
    | some (.notChecked m) => ranOut := some m
    | none => pure ()
  catch e => ranOut := some ((← e.toMessageData.toString).splitOn "\n" |>.head!)
  if !old && !fixed && !r5 then return (.pass, ranOut)
  -- the label: which tests fired; `old case 3 only` when no test with a proof fired, also when
  -- the fixed test ran out (cold review r2, finding 8)
  let mut why : Array String := #[]
  if old then
    why := why.push <| if fixed || r5 then "old case 3" else
      "old case 3 only" ++ (fixedOut.map (s!" (fixed test UNCHECKED: {·})") |>.getD "")
  if fixed then why := why.push "fixed test"
  if r5 then why := why.push "rule 5"
  let w := " + ".intercalate why.toList
  let h := statementHash type
  match list.find? (·.name == privateToUserName n) with
  | some e => return (if e.hash == h then .listed e w else .flag h (some e.hash) w, ranOut)
  | none => return (.flag h none w, ranOut)

/-- The `_proof_` constants that some declaration of the target modules, or of the current file,
    uses in its statement or its proof. Declarations of other modules (Mathlib) cannot use a
    constant of the library, so they are not read. -/
def usedHelpers : CoreM NameSet := do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut s : NameSet := {}
  for (n, ci) in env.constants.toList do
    let inScope := match env.getModuleIdxFor? n with
      | some i => targets.any (·.isPrefixOf mods[i.toNat]!)
      | none => true
    unless inScope do continue
    let mut cs := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
    for c in cs do
      if let .str _ x := c then
        if x.startsWith "_proof_" then s := s.insert c
  return s

/-- A `_proof_N` lemma that a tactic (mostly `omega`) or the elaborator abstracted out of a
    proof, such as `¬2 * (k + 2) = 2 * k + 4 → False`. Its statement is often trivial on purpose,
    and it is no one's theorem. Lean records no source position for these; every declaration
    written in a file has one, so a hand-written theorem called `foo._proof_1` is still tested
    (test `vac_named_like_helper._proof_1`). And a tactic makes one to use it, so since order
    VACUITY-2 a `_proof_` lemma is skipped only when some declaration uses it (`used`, from
    `usedHelpers`): one added by meta code (`addDecl`) and used by nothing is tested (test
    `vac_meta_helper._proof_1`). Measured at VACUITY-1: 589 of the library's 3158 theorem
    constants are `_proof_` lemmas, none with a source position; 586 are used. -/
def isTacticHelper (used : NameSet) (n : Name) : CommandElabM Bool := do
  match n with
  | .str _ s => if s.startsWith "_proof_" then
                  return (← findDeclarationRanges? n).isNone && used.contains n
                else return false
  | _ => return false

/-- Scan the target namespaces; return every theorem's verdict that is not a plain pass, and
    every theorem on which rule 5 ran out of heartbeats, with the message. -/
def scan (list : Array Entry) :
    CommandElabM (Array (Name × Verdict) × Array (Name × String)) := do
  let env ← getEnv
  let used ← liftCoreM usedHelpers
  let mut out := #[]
  let mut ranOut := #[]
  for (n, ci) in env.constants.toList do
    match ci with
    | .thmInfo ti =>
      -- Skip only tactic helpers that something uses. `isInternal` is NOT used, because it also
      -- skips user theorems whose name starts with `_`, which would let a leading underscore
      -- bypass the gate. Auto-generated equation and projection lemmas (`.eq_1`, `.injEq`, …)
      -- have real equality conclusions, so the vacuity test never matches them. Theorems with
      -- macro scopes (written by a hygienic macro) are tested since order VACUITY-2 (test
      -- `vac_macro_scoped`); the library has none.
      if ← isTacticHelper used n then continue
      -- On the USER name: a `private theorem` is stored as `_private.<Module>.0.<name>`,
      -- which no `ClassicalLean` prefix test matches, so testing the raw name would exempt
      -- every private declaration — the same hole that was measured in `AxiomGate`.
      if targets.any (fun ns => ns.isPrefixOf (privateToUserName n)) then
        -- At the command level `try` also catches running out of heartbeats, so a theorem whose
        -- test does not finish is reported as UNCHECKED, never passed.
        let (v, r) ← try judge list n ti.type
          catch e => pure (.unchecked ((← e.toMessageData.toString).splitOn "\n" |>.head!), none)
        if let some m := r then ranOut := ranOut.push (privateToUserName n, m)
        match v with
        | .pass => pure ()
        | v => out := out.push (privateToUserName n, v)
    | _ => pure ()
  return (out.qsort (·.1.toString < ·.1.toString), ranOut.qsort (·.1.toString < ·.1.toString))

end VacuityGate

-- Each theorem's test runs in its own `liftTermElabM`, which starts a fresh heartbeat count, so
-- this is a per-theorem budget. Raised from the default 200000 in order LEAN-15 (round 43):
-- testing `EffectiveSampleSize.variance_average_eq` (hypothesis `Var[X i; μ] = 1` against a
-- conclusion that is also an equation of reals) takes 209673, measured by a probe that times the
-- same test per theorem; the next largest are 102784 and 102765. Raised again in order VACUITY-1,
-- whose test opens hypotheses and conclusions through definitions: `StepUpProcedure.
-- indepFun_numRej_update` and `LinearPrediction.indepFun_of_le` (`iIndepFun` against `IndepFun`)
-- take 1279270 and 1279258, measured the same way; the next largest is 209667. A theorem that
-- still runs out is reported as UNCHECKED and fails the gate (unless the old case 3 flagged it).
set_option maxHeartbeats 2000000 in
run_cmd do
  let list ← VacuityGate.loadList VacuityGate.reviewedPath
  let (found, ranOut) ← VacuityGate.scan list
  let mut bad : Array String := #[]
  let mut helpers := 0
  let mut pending : Array String := #[]
  for (n, v) in found do
    match v with
    | .flag h none w => bad := bad.push s!"{n} {h} [{w}]"
    | .flag h (some old) w =>
      bad := bad.push s!"{n} {h} [{w}] (listed under {old}: the statement changed)"
    | .unchecked m => bad := bad.push s!"{n} UNCHECKED: {m}"
    | .kernelRejected w m => bad := bad.push s!"{n} KERNEL-REJECTED [{w}]: {m}"
    | .listed e w =>
      if e.pending then pending := pending.push s!"{n} [{w}]: {e.reason}" else helpers := helpers + 1
    | .pass => pure ()
  -- An entry no flagged theorem matches by name is stale: the theorem was renamed, removed or
  -- no longer flagged. The list must say exactly what the gate flags.
  let stale := list.filter fun e => !found.any (·.1 == e.name)
  for e in stale do bad := bad.push s!"{e.name} (stale entry in {VacuityGate.reviewedPath})"
  -- Rule 5 running out is printed, theorem by theorem, and counted on the summary line, but does
  -- not fail the gate (see `VacuityGate.judge`).
  let r5 := s!"rule 5 ran out of its {VacuityGate.rule5Heartbeats} heartbeats on {ranOut.size} \
theorem{if ranOut.size == 1 then "" else "s"}"
  unless ranOut.isEmpty do
    logInfo s!"vacuity gate: {r5} (not a failure; rule 5 is an incomplete search):\n  \
{String.intercalate "\n  " (ranOut.toList.map fun (n, m) => s!"{n}: {m}")}"
  unless pending.isEmpty do
    logInfo s!"vacuity gate: {pending.size} VACUOUS-PENDING entr{if pending.size == 1 then "y" else "ies"} \
(theorems that prove nothing beyond a hypothesis, left for a later order):\n  \
{String.intercalate "\n  " pending.toList}"
  if bad.isEmpty then
    logInfo s!"vacuity gate PASS — no vacuous theorems in {VacuityGate.targets} \
({helpers} reviewed helpers and {pending.size} VACUOUS-PENDING on {VacuityGate.reviewedPath}); {r5}"
  else
    throwError s!"vacuity gate FAIL — {bad.size} problem(s) (name, statement sha256); {r5}:\n  \
{String.intercalate "\n  " bad.toList}\n\n\
A statement is vacuous here if its conclusion is `True`; is one of its own hypotheses \
(`P → P`); follows from one hypothesis by applying it, with that hypothesis's premises met by \
the other hypotheses (`(∀ a, Q a → P a) → Q a → P a`, also through `⊆` and named definitions; \
a flag labelled `old case 3 only` matched a hypothesis's conclusion without meeting its premises); \
or is `∃ y, y = e` with `e` independent of `y` (provable by `⟨e, rfl⟩` for any `e`); or its \
hypotheses contradict each other (rule 5: `contradiction`, `linarith`, `omega`, `norm_num` or \
`decide` proves `False` from them).\n\
Such a theorem builds green and is sorry-free while proving nothing. State a real conclusion \
over real objects, or delete it. A deliberate helper that applies a hypothesis can go on \
{VacuityGate.reviewedPath} under its name and statement hash, after review."
