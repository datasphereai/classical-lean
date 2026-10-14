import ClassicalLean

/-!
# Uninformative-statement report

Item 90 of MATH-PLAN-library-2 (order VACUITY-3). The vacuity gate (`tools/VacuityGate.lean`)
cannot see a statement that is true but carries no information, because being uninformative is
not a property of a statement's form. This tool narrows that limit for a human reader: it lists
every written theorem whose conclusion closes **with no hypotheses** by `simp`, `norm_num` or
`positivity`. It is a **report, not a check**: nothing it lists about the library fails anything.
Only its own self-test and its own count check can fail it (rc 1).

Run from the repository root: `lake env lean tools/UninformativeReport.lean`.

What it reads. Every theorem constant (`.thmInfo`) whose user name (`privateToUserName`, so
`private` theorems are read too) is under the namespace `ClassicalLean` and that has a declaration
range (a theorem written in a file, not a `_proof_` helper or an equation lemma), in name order.
Binders are taken as written (`forallTelescope`, no unfolding). A **hypothesis** is a binder that is
not an instance binder and whose type is a proposition.

* **Section A**, theorems with at least one hypothesis. The hypotheses are cleared from the goal;
  a theorem whose conclusion, or another binder, needs one of them cannot be cleared and is
  `DEPENDENT`. Otherwise `simp`, `norm_num` and `positivity` are tried in that order, each from a
  saved state. One line per theorem: `A CLOSES <tactic> <name> uses=[…]`, `A OPEN <name>`,
  `A DEPENDENT <name>`, `A TIMEOUT <name>` or `A ERROR <name>: <first line of the message>`.
* **Section B**, theorems with no hypothesis: the same three tactics. The theorems that close are
  listed (`B CLOSES …`); the others are only counted.
* **Self-use.** `simp` and `norm_num` run with the theorem itself erased from the default simp set
  (through the simp-set API, so private names work too; erased only when the set holds it, in
  either direction). Every `CLOSES` line names the library constants its proof term uses, and says
  `USES-ITSELF` when the proof's constants, unfiltered, include the theorem or a constant that has
  the theorem's name as a strict prefix (`<name>._simp_1`, `<name>.eq_1`).
* **Section C**, the gap HANDOFF.md §4 leaves for a later gate order: every definition under
  `ClassicalLean` with a declaration range whose type ends in `Prop` (after
  `forallTelescopeReducing`) and whose value names a `brecOn`, a recursor `rec` or a well-founded
  fixpoint (`WellFounded.fix`, `WellFounded.fixF`, `WellFounded.Nat.fix`), also one level down, in the constants the value names that have no
  declaration range (a well-founded recursion on two arguments goes through `<name>._unary`).
  These are listed for a human: the vacuity gate does not read a recursive all-`True` predicate
  (`NatT2 | 0 => True | n + 1 => NatT2 n`) as `True`.

Budgets and outcomes. Each theorem's whole try has its own heartbeat count, `libraryBudget`
(200000, the default `maxHeartbeats`), set per theorem; it is not to be changed without asking
Dustin (order LEAN-16's known trap). `TIMEOUT` means only running out of heartbeats
(`Exception.isMaxHeartbeat`), and stops that theorem's try; a theorem that runs out is never a
pass. A tactic that fails or leaves goals is not an error: it did not close the goal, and the next
one is tried. Any other exception from a theorem's try is `ERROR`. A `CLOSES` whose proof term
holds `sorryAx` or an unassigned metavariable is an `ERROR` too.

Output: the self-test's lines (`SELFTEST …`), then sections A, B and C, then `SUMMARY` lines with
every category, zeros included. The tool checks that section A's and section B's counts add up to
the number of written theorems and raises an error if they do not. Wall time and peak memory are
taken outside it (`/usr/bin/time -v`).

Limits, stated:
* a proposition in an instance binder (`[Fact p.Prime]`) is not counted as a hypothesis, so it
  stays in the context and the tactics may use it;
* binders are read as written: a hypothesis hidden inside a definition of the conclusion (`S ⊆ T`
  unfolds to a `∀ x, x ∈ S → x ∈ T`) is part of the conclusion here;
* three tactics with their default settings; a conclusion that `decide`, `rfl`, `omega` or
  `linarith` would close with no hypotheses is not tried;
* a `CLOSES` line is a statement for a human to read, not a finding: a value lemma such as
  `lucas_zero` closes by `simp` and is still a useful theorem;
* section C reads one level below a definition's value, and only the three markers above.

Order VACUITY-3, job 1. Started from claude-ai's prototype (the order's appendix A1, with A2 for
section C).
-/

/-! ## The self-test's planted declarations (outside `ClassicalLean`, so never in the library's
sections or counts) -/

namespace UninformativeReportSelfTest

/-- Section A, expected `CLOSES simp`. -/
theorem bySimp (x : ℕ) (_h : x = 5) : x + 0 = x := by simp
/-- Section A, expected `CLOSES norm_num`. -/
theorem byNormNum (x : ℕ) (_h : x = 5) : (2 : ℝ) + 2 = 4 := by norm_num
/-- Section A, expected `CLOSES positivity`. -/
theorem byPositivity (x : ℝ) (h : 0 < x) : 0 ≤ x ^ 2 := by positivity
/-- Section A, expected `OPEN`: the conclusion is the hypothesis. -/
theorem notClosed (x : ℝ) (h : 0 < x) : 0 < x := h
/-- Section A, expected `DEPENDENT`: the conclusion names the hypothesis. -/
theorem dep (n : ℕ) (h : 0 < n) : (⟨0, h⟩ : Fin n).val = 0 := rfl
/-- Section A, expected `DEPENDENT`: a later binder that is not a proposition has a type that
names the hypothesis, while the conclusion does not. -/
theorem dep2 (n : ℕ) (h : 0 < n) (_w : {f : Fin n → ℕ // f ⟨0, h⟩ = 0}) : n = n := rfl
/-- Section A, expected `TIMEOUT` under the self-test's small budget `selfTestBudget`, and
`CLOSES norm_num` under the library's (the control). -/
theorem slow (x : ℕ) (_h : x = 5) : Nat.Prime 1000003 := by norm_num
/-- A definition that only its own simp lemma unfolds. -/
@[irreducible] def selfDef (n : ℕ) : ℕ := n + 2
/-- Section B, expected `OPEN` once it is erased from the simp set, for `simp` and `norm_num`
alike; and `CLOSES simp USES-ITSELF` with the erasure switched off (the control). -/
@[simp] theorem selfDef_three : selfDef 3 = 5 := by unfold selfDef; rfl
/-- Section B, expected `CLOSES simp`. -/
theorem noHypCloses : (2 : ℕ) + 2 = 4 := rfl
/-- Section C, expected: structural recursion, all branches `True`. -/
def NatT2 : ℕ → Prop
  | 0 => True
  | n + 1 => NatT2 n
/-- Section C, expected: well-founded recursion on two arguments, through `WF2._unary`. -/
def WF2 (n m : ℕ) : Prop := if n = 0 then True else WF2 (n - 1) (m + 1)
termination_by n
decreasing_by omega
/-- Not in section C: Prop-valued, not recursive. -/
def NotRec (n : ℕ) : Prop := n = n

end UninformativeReportSelfTest

open Lean Meta Elab Term Tactic Command

namespace UninformativeReport

/-- Each library theorem's whole try: the default `maxHeartbeats` (in thousands). -/
def libraryBudget : Nat := 200000

/-- The self-test's small budget for its TIMEOUT case (at least 1: `maxHeartbeats 0` means no
limit). -/
def selfTestBudget : Nat := 1

/-- The outcome of one theorem's try. -/
structure Outcome where
  /-- `CLOSES <tactic>`, `OPEN`, `DEPENDENT`, `TIMEOUT` or `ERROR` -/
  verdict : String
  /-- the library constants the proof uses (CLOSES only) -/
  uses : Array Name := #[]
  usesItself : Bool := false
  /-- the message (ERROR only) -/
  msg : String := ""

/-- The three tactics, in order. -/
def tactics : TermElabM (Array (String × TSyntax `tactic)) := do
  return #[("simp", ← `(tactic| simp)), ("norm_num", ← `(tactic| norm_num)),
    ("positivity", ← `(tactic| positivity))]

/-- The environment with `n` erased from the default simp set, in both directions, where the set
holds it (`SimpTheorems.eraseCore`; never an error for a theorem without `@[simp]`). -/
def eraseFromSimp (n : Name) : CoreM Unit := do
  let thms ← getSimpTheorems
  let mut ids : Array Origin := #[]
  for o in [Origin.decl n, Origin.decl n (inv := true)] do
    if thms.isLemma o then ids := ids.push o
  unless ids.isEmpty do
    modifyEnv fun env => simpExtension.modifyState env fun s => ids.foldl (·.eraseCore ·) s

/-- Is `c` the theorem `n` or a constant under it (`n._simp_1`, `n.eq_1`)? -/
def isSelf (n c : Name) : Bool := c == n || n.isPrefixOf c

/-- Try one tactic on `g` from a saved state; restore the state afterwards. `some` with the proof
term when it closes the goal. A failing tactic is `none`; running out of heartbeats is not caught
here (it is a runtime exception), so it ends the theorem's try. -/
def tryClose (g : MVarId) (tac : TSyntax `tactic) (erase : Option Name) :
    TermElabM (Option Expr) := do
  let s ← saveState
  try
    if let some n := erase then eraseFromSimp n
    let gs ← Tactic.run g (evalTactic tac)
    let r ← if gs.isEmpty then pure (some (← instantiateMVars (mkMVar g))) else pure none
    s.restore
    return r
  catch _ =>
    s.restore
    return none

/-- One theorem's try. `erase`: erase the theorem from the simp set (switched off only by the
self-test's control). Returns the outcome and the number of hypotheses. -/
def analyze (n : Name) (ty : Expr) (erase : Bool := true) : TermElabM (Outcome × Nat) :=
  forallTelescope ty fun xs body => do
    let mut hyps : Array FVarId := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isInstImplicit then continue
      if ← isProp d.type then hyps := hyps.push x.fvarId!
    let k := hyps.size
    if hyps.any (body.containsFVar ·) then return ({ verdict := "DEPENDENT" }, k)
    let g ← mkFreshExprMVar body
    let gid ← g.mvarId!.tryClearMany hyps
    let lctx := (← gid.getDecl).lctx
    if hyps.any (lctx.contains ·) then return ({ verdict := "DEPENDENT" }, k)
    for (nm, tac) in ← tactics do
      let er := if erase && nm != "positivity" then some n else none
      if let some pf ← tryClose gid tac er then
        if pf.hasSorry || pf.hasExprMVar then
          return ({ verdict := "ERROR", msg := s!"{nm} closed the goal with sorryAx or an \
            unassigned metavariable in its proof" }, k)
        let cs := pf.getUsedConstants
        let uses := cs.filter fun c => (`ClassicalLean).isPrefixOf (privateToUserName c)
        return ({ verdict := s!"CLOSES {nm}", uses, usesItself := cs.any (isSelf n) }, k)
    return ({ verdict := "OPEN" }, k)

/-- Run `analyze` under its own heartbeat count `budget`, at the command level, where running out
of heartbeats can be caught: `TIMEOUT` for that, `ERROR` for any other exception. The number of
hypotheses for a theorem that did not finish is counted again without the tactics. -/
def judge (n : Name) (ty : Expr) (budget : Nat := libraryBudget) (erase : Bool := true) :
    CommandElabM (Outcome × Nat) := do
  try
    withScope (fun s => { s with opts := maxHeartbeats.set s.opts budget }) <|
      liftTermElabM (analyze n ty erase)
  catch e =>
    let k ← liftTermElabM <| forallTelescope ty fun xs _ => do
      let mut k := 0
      for x in xs do
        let d ← x.fvarId!.getDecl
        if d.binderInfo.isInstImplicit then continue
        if ← isProp d.type then k := k + 1
      return k
    if e.isMaxHeartbeat then return ({ verdict := "TIMEOUT" }, k)
    let m := (← e.toMessageData.toString).splitOn "\n" |>.head!
    return ({ verdict := "ERROR", msg := m }, k)

/-- The line for one theorem, without its section letter. -/
def line (n : Name) (o : Outcome) : String :=
  let u := privateToUserName n
  if o.verdict.startsWith "CLOSES" then
    let self := if o.usesItself then " USES-ITSELF" else ""
    let us := ", ".intercalate (o.uses.toList.map fun c => (privateToUserName c).toString)
    s!"{o.verdict} {u}{self} uses=[{us}]"
  else if o.verdict == "ERROR" then s!"ERROR {u}: {o.msg}"
  else s!"{o.verdict} {u}"

/-- Section C's markers of recursion: a `brecOn`, a recursor `rec`, or one of the well-founded
fixpoints `WellFounded.fix`, `WellFounded.fixF` and `WellFounded.Nat.fix`. The last is how Lean
v4.34.0 compiles a recursion whose measure is a natural number (the self-test's `WF2` goes through
`WF2._unary`, whose value names `WellFounded.Nat.fix`, not `WellFounded.fix`; measured in order
VACUITY-3). -/
def isRecursionMarker (c : Name) : Bool :=
  [``WellFounded.fix, ``WellFounded.fixF, ``WellFounded.Nat.fix].contains c ||
    (match c with | .str _ s => s == "brecOn" || s == "rec" | _ => false)

/-- Section C's test: a Prop-valued definition whose value names a recursion marker
(`isRecursionMarker`), looking also one level down into constants with no declaration range.
Returns the markers found. -/
def recursionMarkers (di : DefinitionVal) : CoreM (Array Name) := do
  let env ← getEnv
  let marker := isRecursionMarker
  let top := di.value.getUsedConstants
  let mut found := top.filter marker
  for c in top do
    if (← findDeclarationRanges? c).isSome then continue
    if let some v := (env.find? c).bind (·.value? (allowOpaque := true)) then
      found := found ++ (v.getUsedConstants.filter marker)
  return found

/-- Is `di` a definition whose type ends in `Prop`? -/
def isPropValued (di : DefinitionVal) : MetaM Bool :=
  forallTelescopeReducing di.type fun _ b => return b.isProp

/-- The theorems and Prop-valued definitions under a namespace, with declaration ranges. -/
def collect (ns : Name) : CommandElabM (Array (Name × Expr) × Array DefinitionVal) := do
  let env ← getEnv
  let mut thms : Array (Name × Expr) := #[]
  let mut defs : Array DefinitionVal := #[]
  for (n, ci) in env.constants.toList do
    unless ns.isPrefixOf (privateToUserName n) do continue
    if (← findDeclarationRanges? n).isNone then continue
    match ci with
    | .thmInfo ti => thms := thms.push (n, ti.type)
    | .defnInfo di => if ← liftTermElabM (isPropValued di) then defs := defs.push di
    | _ => pure ()
  let key (n : Name) := (privateToUserName n).toString
  return (thms.qsort (key ·.1 < key ·.1), defs.qsort (key ·.name < key ·.name))

/-- The self-test, run first: every planted declaration with its expected verdict. Returns the
number of mismatches. -/
def selfTest : CommandElabM Nat := do
  let p (s : String) : Name := (`UninformativeReportSelfTest).str s
  -- (name, budget, erase from the simp set, expected section, expected verdict and self-use)
  let cases : List (String × Nat × Bool × String × String) := [
    ("bySimp", libraryBudget, true, "A", "CLOSES simp"),
    ("byNormNum", libraryBudget, true, "A", "CLOSES norm_num"),
    ("byPositivity", libraryBudget, true, "A", "CLOSES positivity"),
    ("notClosed", libraryBudget, true, "A", "OPEN"),
    ("dep", libraryBudget, true, "A", "DEPENDENT"),
    ("dep2", libraryBudget, true, "A", "DEPENDENT"),
    ("slow", selfTestBudget, true, "A", "TIMEOUT"),
    ("slow", libraryBudget, true, "A", "CLOSES norm_num"),
    ("selfDef_three", libraryBudget, true, "B", "OPEN"),
    ("selfDef_three", libraryBudget, false, "B", "CLOSES simp USES-ITSELF"),
    ("noHypCloses", libraryBudget, true, "B", "CLOSES simp")]
  let mut bad := 0
  for (s, budget, erase, sec, want) in cases do
    let n := p s
    let ty := (← getConstInfo n).type
    let (o, k) ← judge n ty budget erase
    let gotSec := if k ≥ 1 then "A" else "B"
    let got := o.verdict ++ (if o.usesItself then " USES-ITSELF" else "")
    let ok := got == want && gotSec == sec
    unless ok do bad := bad + 1
    IO.println s!"SELFTEST {if ok then "ok" else "MISMATCH"} {s} budget={budget} \
      erase={erase}: expected {sec} {want}, got {gotSec} {got}"
  -- section C on the planted namespace: exactly `NatT2` and `WF2`
  let (_, defs) ← collect `UninformativeReportSelfTest
  let mut recs : Array Name := #[]
  for di in defs do
    unless (← liftCoreM (recursionMarkers di)).isEmpty do recs := recs.push di.name
  let wantC := #[p "NatT2", p "WF2"]
  let okC := recs == wantC
  unless okC do bad := bad + 1
  IO.println s!"SELFTEST {if okC then "ok" else "MISMATCH"} section C: expected {wantC.toList}, \
    got {recs.toList} (of {defs.size} Prop-valued definitions)"
  IO.println s!"SELFTEST {if bad == 0 then "PASS" else "FAIL"}: {bad} mismatch(es)"
  return bad

end UninformativeReport

open UninformativeReport in
-- The budget of each theorem is set inside `judge`; this outer one only bounds the command.
set_option maxHeartbeats 0 in
run_cmd do
  let bad ← selfTest
  let (thms, defs) ← collect `ClassicalLean
  let mut counts : Std.HashMap String Nat := {}
  let bump (m : Std.HashMap String Nat) (k : String) := m.insert k (m.getD k 0 + 1)
  let mut nA := 0
  let mut nB := 0
  for (n, ty) in thms do
    let (o, k) ← judge n ty
    let sec := if k ≥ 1 then "A" else "B"
    if k ≥ 1 then nA := nA + 1 else nB := nB + 1
    let v := (o.verdict.splitOn " ").head!
    counts := bump counts s!"{sec} {o.verdict}"
    if o.usesItself then counts := bump counts s!"{sec} USES-ITSELF"
    if sec == "A" || v == "CLOSES" || v == "TIMEOUT" || v == "ERROR" then
      IO.println s!"{sec} {line n o}"
  let mut nC := 0
  for di in defs do
    let ms ← liftCoreM (recursionMarkers di)
    unless ms.isEmpty do
      nC := nC + 1
      IO.println s!"C RECURSIVE {privateToUserName di.name} via={ms.toList}"
  IO.println s!"SUMMARY written theorems {thms.size}"
  IO.println s!"SUMMARY A theorems with a hypothesis {nA}"
  for v in ["CLOSES simp", "CLOSES norm_num", "CLOSES positivity", "OPEN", "DEPENDENT", "TIMEOUT",
      "ERROR", "USES-ITSELF"] do
    IO.println s!"SUMMARY A {v} {counts.getD s!"A {v}" 0}"
  IO.println s!"SUMMARY B theorems with no hypothesis {nB}"
  for v in ["CLOSES simp", "CLOSES norm_num", "CLOSES positivity", "OPEN", "DEPENDENT", "TIMEOUT",
      "ERROR", "USES-ITSELF"] do
    IO.println s!"SUMMARY B {v} {counts.getD s!"B {v}" 0}"
  IO.println s!"SUMMARY C Prop-valued definitions {defs.size}"
  IO.println s!"SUMMARY C recursive {nC}"
  IO.println s!"SUMMARY self-test mismatches {bad}"
  unless nA + nB == thms.size do
    throwError s!"count check failed: section A {nA} + section B {nB} ≠ written theorems {thms.size}"
  unless bad == 0 do
    throwError s!"self-test failed: {bad} mismatch(es)"
