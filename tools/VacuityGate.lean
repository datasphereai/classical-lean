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

Detected (see `isVacuousType`):

1. conclusion is `True`;
2. conclusion is one of the theorem's own hypotheses, or follows from one hypothesis by
   applying it, with that hypothesis's own premises met by the theorem's other hypotheses
   (`P → P`, `(∀ a, P a) → P a`, `(S ⊆ T) → x ∈ S → x ∈ T`);
3. conclusion is `∃ y, y = e` with `e` independent of `y`;
4. (the old case 3, kept by ruling) the conclusion of a `∀` hypothesis unifies with the
   conclusion, whatever that hypothesis's premises (`oldCase3`). The gate flags a theorem when
   either test fires and says which.

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
    so a flag from case 3 always stands for an actual proof term made of hypotheses. -/
def finish (locals : Array Expr) (pf concl : Expr) : MetaM Bool := do
  for m in ← getMVars (← instantiateMVars pf) do
    if ← m.isAssigned then continue
    if ← isProp (← m.getType) then return false
    unless ← fill locals m do return false
  let pf ← instantiateMVars pf
  if pf.hasMVar then return false
  -- at all transparency, as `openLevels` unfolds: `h a` for `h : IWrap P` with `IWrap`
  -- irreducible is a function application only once `IWrap` is unfolded (test `vac_irreducible`)
  try withTransparency .all do
    check pf
    isDefEq (← inferType pf) concl
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
def followsFromHyp (xs : Array Expr) (concl : Expr) : MetaM Bool := do
  for x in xs do
    let t ← inferType x
    if ← isProp t then
      let found ← openLevels x t false fun ms pf body => do
        unless ← isDefEq body concl do return false
        let prems ← ms.filterM fun m => do
          return !(← m.mvarId!.isAssigned) && (← isProp (← inferType m))
        solveAll xs prems.toList (finish xs pf concl)
      if found then return true
  return false

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

    Known limitations, stated rather than hidden. Not detected: a statement that is true but
    carries no information about its subject — `0 ≤ f x` for `f` valued in `Nat`, say — because
    being uninformative is not a syntactic property; a conclusion that needs two hypotheses
    chained (`h (hq hr)`), because that is how real lemmas such as `Monotone.comp` are proved; a
    premise that is true for every value but not by `rfl` or `decide` (`0 + n = n`); a
    contradictory hypothesis. A closed premise that `decide` cannot finish
    (`Nat.Prime 1000003`) makes the theorem UNCHECKED, which fails the gate: safe, but a false
    alarm for a real theorem of that shape. The scan skips a `_proof_` lemma with no source
    position that some declaration uses (`isTacticHelper`), so a theorem added by meta code
    (`addDecl`) under such a name and used by another declaration is not tested. These have to
    be caught in review. Tests of the first ones: `tools/VacuityGateTests.lean`. -/
def isVacuousType (type : Expr) : MetaM Bool :=
  forallTelescopeReducing type fun xs concl => do
    if concl.isConstOf ``True then return true
    if isTrivialExists concl then return true
    followsFromHyp xs concl

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
  /-- the test did not finish within the heartbeat budget -/
  | unchecked (msg : String)

/-- Flagged when the old case 3 **or** the fixed test (cases 1 to 4, `isVacuousType`) flags it;
    `why` says which fired: `old case 3`, `fixed test`, or both. Each test runs in its own
    `liftTermElabM` (its own heartbeat count). At this level `try` also catches running out of
    heartbeats: if the fixed test runs out, the theorem is still flagged when the old case 3
    fired, and is UNCHECKED otherwise. -/
def judge (list : Array Entry) (n : Name) (type : Expr) : CommandElabM Verdict := do
  let old ← liftTermElabM (oldCase3 type)
  let mut why : Array String := if old then #["old case 3"] else #[]
  try
    if ← liftTermElabM (isVacuousType type) then why := why.push "fixed test"
  catch e =>
    let m := (← e.toMessageData.toString).splitOn "\n" |>.head!
    unless old do return .unchecked m
    why := why.push s!"fixed test UNCHECKED: {m}"
  if why.isEmpty then return .pass
  let w := " + ".intercalate why.toList
  let h := statementHash type
  match list.find? (·.name == privateToUserName n) with
  | some e => return if e.hash == h then .listed e w else .flag h (some e.hash) w
  | none => return .flag h none w

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

/-- Scan the target namespaces; return every theorem's verdict that is not a plain pass. -/
def scan (list : Array Entry) : CommandElabM (Array (Name × Verdict)) := do
  let env ← getEnv
  let used ← liftCoreM usedHelpers
  let mut out := #[]
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
        let v ← try judge list n ti.type
          catch e => pure (.unchecked ((← e.toMessageData.toString).splitOn "\n" |>.head!))
        match v with
        | .pass => pure ()
        | v => out := out.push (privateToUserName n, v)
    | _ => pure ()
  return out.qsort (·.1.toString < ·.1.toString)

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
  let found ← VacuityGate.scan list
  let mut bad : Array String := #[]
  let mut helpers := 0
  let mut pending : Array String := #[]
  for (n, v) in found do
    match v with
    | .flag h none w => bad := bad.push s!"{n} {h} [{w}]"
    | .flag h (some old) w =>
      bad := bad.push s!"{n} {h} [{w}] (listed under {old}: the statement changed)"
    | .unchecked m => bad := bad.push s!"{n} UNCHECKED: {m}"
    | .listed e w =>
      if e.pending then pending := pending.push s!"{n} [{w}]: {e.reason}" else helpers := helpers + 1
    | .pass => pure ()
  -- An entry no flagged theorem matches by name is stale: the theorem was renamed, removed or
  -- no longer flagged. The list must say exactly what the gate flags.
  let stale := list.filter fun e => !found.any (·.1 == e.name)
  for e in stale do bad := bad.push s!"{e.name} (stale entry in {VacuityGate.reviewedPath})"
  unless pending.isEmpty do
    logInfo s!"vacuity gate: {pending.size} VACUOUS-PENDING entr{if pending.size == 1 then "y" else "ies"} \
(theorems that prove nothing beyond a hypothesis, left for a later order):\n  \
{String.intercalate "\n  " pending.toList}"
  if bad.isEmpty then
    logInfo s!"vacuity gate PASS — no vacuous theorems in {VacuityGate.targets} \
({helpers} reviewed helpers and {pending.size} VACUOUS-PENDING on {VacuityGate.reviewedPath})"
  else
    throwError s!"vacuity gate FAIL — {bad.size} problem(s) (name, statement sha256):\n  \
{String.intercalate "\n  " bad.toList}\n\n\
A statement is vacuous here if its conclusion is `True`; is one of its own hypotheses \
(`P → P`); follows from one hypothesis by applying it, with that hypothesis's premises met by \
the other hypotheses (`(∀ a, Q a → P a) → Q a → P a`, also through `⊆` and named definitions); \
or is `∃ y, y = e` with `e` independent of `y` (provable by `⟨e, rfl⟩` for any `e`).\n\
Such a theorem builds green and is sorry-free while proving nothing. State a real conclusion \
over real objects, or delete it. A deliberate helper that applies a hypothesis can go on \
{VacuityGate.reviewedPath} under its name and statement hash, after review."
