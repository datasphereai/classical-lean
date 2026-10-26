import Lean

/-!
# The witness gate's listing driver (order VACUITY-4, ruling 2, section 3 items 1 and 3)

Run by `tools/witness_gate.py`, never by hand and never as text placed in a module:
`lake env lean <the lakefile's options> --run tools/WitnessListing.lean <module file>`, with its
standard input: line 1 a value made fresh for each run (the nonce), then one line per probe point,
`<module line> <block line> <inserted text, with each line break written as \n>`.

It runs Lean's frontend over the original module, command by command: it parses each command,
checks it, and only then elaborates it (ruling 4, section 2 item 1). It prints:

* `cmd|<line>|<kind>`: each command's kind, before it is elaborated (a `declaration` by its own
  form, `theorem`, `definition`, …; `… in` and `mutual` crossed);
* `inner|<line>|<kind>`, `attr|<line>|<attribute>`, `opt|<line>|<option>`: each node inside the
  command whose kind is in `codeKinds`, each attribute, each option name;
* `refuse|<why>`: a command whose kind is not in `allowedCommands`, that holds a node of a kind in
  `codeKinds` or an attribute not in `allowedAttrs` (refused before it is elaborated), or that
  declared a constant item 4 refuses (`deny4|<why>` too); the driver then elaborates nothing more,
  and prints only its closing lines. With `--census` it prints the same lines and refuses nothing
  (ruling 4, section 3 item 1);
* `leanproof|<count>|<names>`: information: the proofs whose terms mention `Lean.` names;

* `ex|<line>:<column>`: one line for each `example` keyword in the parsed syntax of every command
  (it walks the whole syntax tree, so `… in`, `mutual`, attributes and modifiers are crossed);
* `probe|<block line>|…`: at each probe point, before the first command that starts on or after that
  line (the scope the gate's check will run in), the parsed shape of the inserted text and the
  macro and elaborator entries of every syntax kind `run_cmd` passes through, read after the
  inserted text's `open … in` and `set_option … in` prefixes are elaborated in a scratch state;
* `sig|<constant>|<n>|<binders written before the colon>`: each `theorem`, `lemma`, `def`,
  `abbrev`, `instance` and `opaque` (ruling 3, section 2 items 1 and 2). The constant is the one
  Lean's info tree names at the declaration's identifier (the binder entry Lean records for the
  declared constant), so `_root_`, the namespace and `private` resolve as Lean resolves them; it is
  printed `private:<name>` for a private constant (the private prefix carries the run's main
  module; this run's is `_stdin`, as the copy's is, since ruling 4, item 7). n is the number of `∀` binders at the
  head of the constant's type minus the number at the head of the type after the colon as Lean
  elaborated it (read from the info tree), so it counts every binder Lean put before the colon:
  each kind of bracket, section `variable`s and auto-bound implicits. `?` when Lean's reading of
  the type after the colon is not found, or the difference is less than the binders written;
* `alias|<constant>|<target constant>`: each `alias a := b` of Batteries, its target read from the
  constant's value;
* `nosig|<line>|<name as written>`: a declaration whose constant the info tree does not name;
* `error|<line>` for each of the module's own error messages, then `errors|<count>`;
* `clash|<name>`: a constant with a name part that starts with `witnessGate`;
* `end|<count of ex lines>`, last.

Each line is `@@WD<nonce>|…|WD<nonce>@@`. The nonce is read from standard input before any module
text is elaborated, and the lines go to the standard output stream captured at start. Since ruling
4 a module runs none of its own code while it elaborates (what the checks above allow), so it
cannot print a line here at all.
-/

open Lean Elab Frontend

namespace WitnessListing

/-- The kinds whose macro and elaborator entries are compared with the baseline, besides the kinds
in the parsed inserted text and in the parsed expansion `discard do …` of `run_cmd`. -/
def fixedKinds : List Name :=
  [``Lean.Parser.Command.in, ``Lean.Parser.Command.section, ``Lean.Parser.Command.end,
   ``Lean.Parser.Command.open, ``Lean.Parser.Command.set_option, ``Lean.runCmd,
   ``Lean.Parser.Term.app, ``Lean.Parser.Term.do, `ident]

/-- The shape of a syntax tree: kinds and atoms, with every identifier written `ID`. -/
partial def shape : Syntax → String
  | .node _ k args => s!"{k}(" ++ ",".intercalate (args.toList.map shape) ++ ")"
  | .atom _ v => (repr v).pretty
  | .ident .. => "ID"
  | .missing => "MISSING"

partial def kinds (acc : NameSet) : Syntax → NameSet
  | .node _ k args => args.foldl kinds (acc.insert k)
  | .ident .. => acc.insert `ident
  | _ => acc

/-- Every `example` keyword: an atom `example` that is a child of a node of kind
`Lean.Parser.Command.example`. -/
partial def examples (acc : Array String.Pos.Raw) : Syntax → Array String.Pos.Raw
  | .node _ k args =>
    let acc := if k == ``Lean.Parser.Command.example then
      args.foldl (fun a c => match c with
        | .atom (.original _ p _ _) "example" => a.push p
        | .atom (.synthetic p _ _) "example" => a.push p
        | _ => a) acc
    else acc
    args.foldl examples acc
  | _ => acc

/-- The declarations in one command that item 4 counts: (kind, identifier node, binders written
before the colon, the type after the colon if written). `alias` has no binders of its own. -/
partial def decls (acc : Array (Name × Syntax × Syntax × Option Syntax)) (stx : Syntax) :
    Array (Name × Syntax × Syntax × Option Syntax) :=
  match stx with
  | .node _ k args =>
    let acc :=
      if k == ``Lean.Parser.Command.theorem || k == `lemma || k == ``Lean.Parser.Command.definition ||
          k == ``Lean.Parser.Command.abbrev || k == ``Lean.Parser.Command.instance ||
          k == ``Lean.Parser.Command.opaque then
        match stx.find? (·.getKind == ``Lean.Parser.Command.declId),
              stx.find? (fun s => s.getKind == ``Lean.Parser.Command.declSig ||
                s.getKind == ``Lean.Parser.Command.optDeclSig) with
        | some d, some sig =>
          let ty := if sig.getKind == ``Lean.Parser.Command.declSig then some sig[1][1]
            else if sig[1].getNumArgs > 0 then some sig[1][0][1] else none
          acc.push (k, d, sig[0], ty)
        | _, _ => acc
      else if k == `Batteries.Tactic.Alias.alias then acc.push (k, stx[2], .missing, none)
      else acc
    args.foldl decls acc
  | _ => acc

/-- The binders written before the colon: one per name in a bracketed group, one for an instance
binder, one for a bare identifier or hole. -/
def written (bs : Syntax) : Nat :=
  bs.getArgs.foldl (fun c b =>
    let k := b.getKind
    if k == ``Lean.Parser.Term.explicitBinder || k == ``Lean.Parser.Term.implicitBinder ||
        k == ``Lean.Parser.Term.strictImplicitBinder then c + b[1].getNumArgs
    else c + 1) 0

/-! ## What a module may do (ruling 4, section 2) -/

/-- The command kinds a module may use (ruling 4, section 2 item 2): an allowlist, from the census
of the library (`r5/census`). A `declaration` is named by its own form (`theorem`, `definition`, …);
`… in` and `mutual` are crossed and each part is checked. -/
def allowedCommands : List Name :=
  [``Lean.Parser.Command.theorem, `lemma, ``Lean.Parser.Command.definition,
   ``Lean.Parser.Command.abbrev, ``Lean.Parser.Command.instance, ``Lean.Parser.Command.structure,
   ``Lean.Parser.Command.example, ``Lean.Parser.Command.moduleDoc, ``Lean.Parser.Command.namespace,
   ``Lean.Parser.Command.section, ``Lean.Parser.Command.end, ``Lean.Parser.Command.open,
   ``Lean.Parser.Command.in, ``Lean.Parser.Command.variable, ``Lean.Parser.Command.omit,
   ``Lean.Parser.Command.include, ``Lean.Parser.Command.universe, ``Lean.Parser.Command.set_option,
   ``Lean.Parser.Command.attribute, ``Lean.Parser.Command.eoi]

/-- The syntax kinds, anywhere inside an allowed command, that run code while Lean elaborates them
(ruling 4, section 2 item 3): a list, not an allowlist, found by asking Lean for the kinds Lean and
Mathlib register (run `r5-askkinds`). -/
def codeKinds : List Name :=
  [`Lean.byElab, `Lean.runCmd, `Lean.runElab, `Lean.runMeta, `Lean.Parser.Tactic.runTac,
   `Lean.Parser.Command.eval, `Lean.Parser.Command.evalBang, `Qq.termBy_elabq_,
   `Lean.Parser.Tactic.nativeDecide]

/-- The attributes a module may write (ruling 4, section 2 item 5): an allowlist, from the census. An
attribute is named by its syntax kind, or by its name for `Lean.Parser.Attr.simple`. -/
def allowedAttrs : List String :=
  ["Lean.Parser.Attr.simp", "Lean.Parser.Attr.instance"]

/-- The commands inside one command, as the allowlist names them. -/
partial def cmdKinds (stx : Syntax) : Array Name :=
  let k := stx.getKind
  if k == ``Lean.Parser.Command.in then cmdKinds stx[0] ++ #[k] ++ cmdKinds stx[2]
  else if k == ``Lean.Parser.Command.mutual then
    stx[1].getArgs.foldl (fun a c => a ++ cmdKinds c) #[k]
  else if k == ``Lean.Parser.Command.declaration then #[stx[1].getKind]
  else #[k]

/-- Every node of a kind in `codeKinds`, every attribute and every option name inside a command. -/
partial def inner (acc : Array (String × String.Pos.Raw × String)) (stx : Syntax) :
    Array (String × String.Pos.Raw × String) :=
  match stx with
  | .node _ k args =>
    let p := stx.getPos?.getD 0
    let acc := if codeKinds.contains k then acc.push ("inner", p, toString k) else acc
    let acc := if k == ``Lean.Parser.Term.attrInstance then
        let a := stx[1]
        let w := if a.getKind == ``Lean.Parser.Attr.simple then a[0].getId.toString else toString a.getKind
        acc.push ("attr", p, w)
      else acc
    let acc := if k == ``Lean.Parser.Command.set_option || k == ``Lean.Parser.Term.set_option ||
        k == ``Lean.Parser.Tactic.set_option then acc.push ("opt", p, toString stx[1].getId) else acc
    args.foldl inner acc
  | _ => acc

/-- A name that is part of Lean's own machinery (ruling 4, section 2 item 4). -/
def machinery (n : Name) : Bool :=
  let r := (privateToUserName n).getRoot
  [`Lean, `IO, `EIO, `BaseIO, `ST, `EST].contains r

def unsafeName (n : Name) : Bool :=
  (privateToUserName n).components.any fun c => c.toString.startsWith "unsafe"

/-- The axioms behind `native_decide` and `decide +native` in older Lean versions, and their kin. -/
def nativeNames : List Name :=
  [``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler, ``Lean.reduceBool, ``Lean.reduceNat]

/-- Why item 4 refuses a constant the module added, if it does: `refused` holds the module's
constants already refused. -/
def refuse4 (env : Environment) (refused : NameSet) (ci : ConstantInfo) (proof : Bool) :
    Option String :=
  let ty := ci.type.getUsedConstants
  let v := match ci.value? (allowOpaque := true) with
    | some e => e.getUsedConstants
    | none => #[]
  if let some c := ty.find? machinery then some s!"its type mentions {c}"
  else if ci matches .axiomInfo _ then
    -- in Lean v4.34 `native_decide` and `decide +native` each add an axiom `…._native.…ax_…`,
    -- not a mention of `Lean.ofReduceBool` (run r5-pnative)
    some "it is an axiom the module adds"
  else if ci.isUnsafe then some "it is marked unsafe"
  else if (Compiler.getImplementedBy? env ci.name).isSome then some "it carries implemented_by"
  else if isExtern env ci.name then some "it carries extern"
  else if unsafeName ci.name then some "its name begins with unsafe"
  else if let some c := v.find? (nativeNames.contains ·) then some s!"its value mentions {c}"
  else if let some c := (if proof then none else v.find? fun c => machinery c || unsafeName c) then
    some s!"it is not a proof and its value mentions {c}"
  else if let some c := (ty ++ v).find? refused.contains then
    some s!"it mentions {c}, which the gate refused"
  else none

/-- A constant as the check prints it too: `private:<name>` for a private one. -/
def ident (n : Name) : String :=
  if isPrivateName n then "private:" ++ toString (privateToUserName n) else toString n

def entries (env : Environment) (k : Name) : String :=
  let names (xs : List Name) := ",".intercalate (xs.map toString)
  let m := names ((macroAttribute.getEntries env k).map (·.declName))
  let c := names ((Command.commandElabAttribute.getEntries env k).map (·.declName))
  let t := names ((Term.termElabAttribute.getEntries env k).map (·.declName))
  let d := names ((Do.doElemElabAttribute.getEntries env k).map (·.declName))
  s!"{k}:macro={m}/command={c}/term={t}/do={d}"

/-- Read the scope at a probe point: parse the inserted text there, elaborate its prefixes in a
scratch state, and read the entries. The frontend state is not changed. -/
def probe (emit : String → IO Unit) (line : Nat) (text : String) :
    FrontendM Unit := do
  let s ← get
  let cmdState := s.commandState
  let scope := cmdState.scopes.head!
  let pmctx : Parser.ParserModuleContext :=
    { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace,
      openDecls := scope.openDecls }
  let ictx := Parser.mkInputContext text "<witness-gate-insert>"
  let (stx, ps, msgs) := Parser.parseCommand ictx pmctx {} {}
  let rest := String.Pos.Raw.extract text ps.pos text.rawEndPos
  let err := msgs.hasErrors || !rest.trimAscii.isEmpty
  let errText ← if err then
      pure (" | ".intercalate (← msgs.toList.mapM fun m => m.data.toString) ++ " rest=" ++ rest)
    else pure ""
  -- the `in` prefixes, outermost first, and the command inside them
  let mut cur := stx
  let mut pre : Array Syntax := #[]
  while cur.getKind == ``Lean.Parser.Command.in do
    pre := pre.push cur[0]
    cur := cur[2]
  -- elaborate `section` and each prefix command in a scratch state
  let ctx ← read
  let cmdCtx : Command.Context :=
    { cmdPos := s.cmdPos, fileName := ctx.inputCtx.fileName, fileMap := ctx.inputCtx.fileMap,
      snap? := none, cancelTk? := none }
  let act : Command.CommandElabM Environment := do
    Command.elabCommand (← `(section))
    for p in pre do
      Command.elabCommand p
    getEnv
  let env ← match (← liftM <| EIO.toIO' <| (act cmdCtx).run cmdState) with
    | .ok (e, _) => pure (some e)
    | .error _ => pure none
  let term := Parser.runParserCategory cmdState.env `term "discard do witnessGateCheckLx"
  let ks := kinds (kinds (fixedKinds.foldl NameSet.insert {}) cur)
    (match term with | .ok t => t | .error _ => .missing)
  let preKinds := ",".intercalate (pre.toList.map (toString ·.getKind))
  let ents := match env with
    | some e => " ;; ".intercalate ((ks.toList.toArray.qsort Name.lt).toList.map
        fun k => entries e k)
    | none => "PREFIX-ERROR"
  emit s!"probe|{line}|err={err}{errText};pre={preKinds};core={shape cur};term={match term with | .ok t => shape t | .error e => "ERROR " ++ e};entries={ents}"

end WitnessListing

open WitnessListing in
unsafe def main (args : List String) : IO UInt32 := do
  -- `--census` (ruling 4, section 3 item 1): print what the checks would refuse, refuse nothing
  let (census, args) := match args with
    | "--census" :: rest => (true, rest)
    | _ => (false, args)
  let path :: optArgs := args | IO.eprintln "usage: WitnessListing [--census] <module file> [-Dkey=value …]"; return 2
  -- the gate's Lean options (the lakefile's `leanOptions`), as `lean` reads `-D`
  -- elaborate each command before the next, as the probes need (no proof is left in a task)
  let mut opts : Options := Options.empty.insert `Elab.async (.ofBool false)
  for a in optArgs do
    match (a.drop 2).toString.splitOn "=" with
    | [k, v] =>
      let k := if k.startsWith "weak." then (k.drop 5).toString else k
      let dv : DataValue := if v == "true" then .ofBool true else if v == "false" then .ofBool false
        else match v.toNat? with | some n => .ofNat n | none => .ofString v
      opts := opts.insert k.toName dv
    | _ => IO.eprintln s!"bad option {a}"; return 2
  let out ← IO.getStdout
  let stdin ← IO.getStdin
  let nonce := (← stdin.getLine).trimAscii.toString
  if nonce.length < 16 then
    IO.eprintln "no nonce"; return 2
  let mut probes : Array (Nat × Nat × String) := #[]
  repeat
    let l ← stdin.getLine
    if l.isEmpty then break
    let l := l.trimAsciiEnd.toString
    match l.splitOn " " with
    | n :: b :: rest =>
      match n.toNat?, b.toNat? with
      | some k, some j => probes := probes.push (k, j, (" ".intercalate rest).replace "\\n" "\n")
      | _, _ => IO.eprintln s!"bad probe line {l}"; return 2
    | _ => IO.eprintln s!"bad probe line {l}"; return 2
  let emit (s : String) : IO Unit := do
    out.putStrLn s!"@@WD{nonce}|{s.replace "\n" " "}|WD{nonce}@@"
    out.flush
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  enableInitializersExecution
  let (env, messages) ← processHeader header opts messages inputCtx (mainModule := `_stdin)
  if messages.hasErrors then
    for m in messages.toList do
      IO.eprintln (← m.toString)
    return 3
  let commandState := Command.mkState env messages opts
  let fmap := inputCtx.fileMap
  let lineOf (p : String.Pos.Raw) := (fmap.toPosition p).line
  let loop : FrontendM (Nat × Array Nat × Bool) := do
    let mut count := 0
    let mut refusedAny := false
    let mut seen : NameSet := {}
    let mut refused : NameSet := {}
    let mut proofLean : NameSet := {}
    let mut proofLeanCount := 0
    let mut pending := probes.qsort (·.1 < ·.1) |>.toList
    let mut errs : Array Nat := #[]
    repeat
      -- the first token of the next command: skip whitespace and comments
      let ps ← getParserState
      let wsEnd := (Parser.whitespace.run inputCtx {env := (← getCommandState).env, options := {}}
        (Parser.getTokenTable (← getCommandState).env) (Parser.mkParserState input |>.setPos ps.pos)).pos
      let nextLine := if wsEnd.byteIdx >= input.utf8ByteSize then 1000000000 else lineOf wsEnd
      while !pending.isEmpty && pending.head!.1 <= nextLine do
        let (_, j, t) := pending.head!
        WitnessListing.probe emit j t
        pending := pending.tail
      -- parse the command as `processCommand` does, check it, and only then elaborate it
      -- (ruling 4, section 2 item 1)
      updateCmdPos
      let cs0 ← getCommandState
      let scope := cs0.scopes.head!
      let pmctx : Parser.ParserModuleContext :=
        { env := cs0.env, options := scope.opts, currNamespace := scope.currNamespace,
          openDecls := scope.openDecls }
      let (cmd, ps', msgs) := Parser.parseCommand inputCtx pmctx (← getParserState) cs0.messages
      modify fun s => { s with commands := s.commands.push cmd }
      setParserState ps'
      setMessages msgs
      let done := Parser.isTerminalCommand cmd
      let cline := lineOf (cmd.getPos?.getD ps'.pos)
      let mut why : Array String := #[]
      for k in cmdKinds cmd do
        emit s!"cmd|{cline}|{k}"
        if !allowedCommands.contains k then
          why := why.push s!"line {cline}: command kind {k} is not on the gate's list: a module may not run its own code while it elaborates"
      for (w, p, x) in inner #[] cmd do
        emit s!"{w}|{lineOf p}|{x}"
        if w == "inner" then
          why := why.push s!"line {lineOf p}: {x} runs code while Lean elaborates it"
        else if w == "attr" && !allowedAttrs.contains x then
          why := why.push s!"line {lineOf p}: attribute {x} is not on the gate's list"
      if !why.isEmpty && !census then
        for r in why do emit s!"refuse|{r}"
        refusedAny := true
        break
      elabCommandAtFrontend cmd
      -- each command starts a fresh message log (`elabCommandTopLevel`), so count its errors now
      for m in (← getCommandState).messages.reportedPlusUnreported.toList do
        if m.severity == .error then
          errs := errs.push m.pos.line
      let cmd := (← get).commands.back!
      for p in examples #[] cmd do
        let pos := fmap.toPosition p
        emit s!"ex|{pos.line}:{pos.column}"
        count := count + 1
      let ds := decls #[] cmd
      if !ds.isEmpty then
        let cst ← getCommandState
        let env := cst.env
        let infos := cst.infoState.trees.foldl (init := (#[] : Array (ContextInfo × TermInfo))) fun acc t =>
          t.foldInfo (init := acc) fun ctx i acc => match i with
            | .ofTermInfo ti => acc.push (ctx, ti)
            | _ => acc
        for (k, d, bs, ty?) in ds do
          let (p0, p1) := (d.getPos?.getD 0, d.getTailPos?.getD 0)
          let c? := infos.findSome? fun (_, ti) =>
            match ti.stx.getPos? with
            | some q => if ti.isBinder && ti.expr.isConst && p0.byteIdx <= q.byteIdx &&
                q.byteIdx <= p1.byteIdx then
                some ti.expr.constName! else none
            | none => none
          match c?, (c?.bind env.find?) with
          | some c, some ci =>
            if k == `Batteries.Tactic.Alias.alias then
              match ci.value? (allowOpaque := true) with
              | some (.const t _) => emit s!"alias|{ident c}|{ident t}"
              | _ => emit s!"sig|{ident c}|?|0"
            else
              let w := written bs
              -- the type after the colon as Lean elaborated it: the first entry for that syntax
              let mut a? : Option Nat := none
              if let some ty := ty? then
                if let some (ctx, ti) := infos.find? fun (_, ti) => !ti.isBinder &&
                    ti.stx.getPos? == ty.getPos? && ti.stx.getTailPos? == ty.getTailPos? then
                  a? := some (← ctx.runMetaM ti.lctx do
                    pure (← instantiateMVars ti.expr).getNumHeadForalls)
              let t := ci.type.getNumHeadForalls
              let n := match a? with
                | some a => if a <= t && t - a >= w then toString (t - a) else "?"
                | none => "?"
              emit s!"sig|{ident c}|{n}|{w}"
          | _, _ => emit s!"nosig|{lineOf (d.getPos?.getD 0)}|{if d.isIdent then d.getId else d[0].getId}"
      -- what the command declared (ruling 4, section 2 item 4)
      let env := (← getCommandState).env
      let mut fresh : Array ConstantInfo := #[]
      for (n, ci) in env.constants.map₂.toList do
        if !seen.contains n then
          seen := seen.insert n
          fresh := fresh.push ci
      let mut proofs : NameSet := {}
      for ci in fresh do
        let isPf ← runCommandElabM <| try Command.liftTermElabM (Meta.isProp ci.type) catch _ => pure false
        if ci matches .thmInfo _ || isPf then proofs := proofs.insert ci.name
      -- to a fixed point, so a refusal reaches every constant of the command that mentions it
      let mut changed := true
      let mut why4 : Array (Name × String) := #[]
      while changed do
        changed := false
        for ci in fresh do
          if !refused.contains ci.name then
            if let some r := refuse4 env refused ci (proofs.contains ci.name) then
              refused := refused.insert ci.name
              why4 := why4.push (ci.name, s!"line {cline}: {ident ci.name} uses Lean's own machinery: {r}")
              changed := true
      for ci in fresh do
        if proofs.contains ci.name && !refused.contains ci.name then
          if let some e := ci.value? (allowOpaque := true) then
            let ms := e.getUsedConstants.filter machinery
            if !ms.isEmpty then
              proofLeanCount := proofLeanCount + 1
              proofLean := ms.foldl NameSet.insert proofLean
      let sorted4 := (why4.qsort fun a b => (!a.1.isInternal && b.1.isInternal) ||
        (a.1.isInternal == b.1.isInternal && Name.lt a.1 b.1)).map (·.2)
      for r in sorted4 do
        emit s!"deny4|{r}"
      if !sorted4.isEmpty && !census then
        for r in sorted4 do emit s!"refuse|{r}"
        refusedAny := true
        break
      if done then break
    if !refusedAny then
      for (_, j, t) in pending do
        WitnessListing.probe emit j t
    -- information (ruling 4, section 3 item 1): proofs whose terms mention Lean's own names
    let names := (proofLean.toList.toArray.qsort Name.lt).toList.take 40
    emit s!"leanproof|{proofLeanCount}|{",".intercalate (names.map toString)}"
    return (count, errs, refusedAny)
  let ((count, errCount, _), st) ← (loop { inputCtx }).run
    { commandState, parserState, cmdPos := parserState.pos }
  let env := st.commandState.env
  for (n, _) in env.constants.toList do
    if n.components.any (fun c => (c.toString.splitOn "witnessGate").length > 1) then
      emit s!"clash|{n}"
  -- the module's own errors: the gate requires none (the library builds), else the driver's
  -- reading is not the build's
  for l in errCount do
    emit s!"error|{l}"
  emit s!"errors|{errCount.size}"
  emit s!"end|{count}"
  return 0
