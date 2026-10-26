#!/usr/bin/env python3
r"""The witness gate (order VACUITY-4): every `example` block of the library, read in place.

Usage, from the repository root:

    python3 -I tools/witness_gate.py [--root DIR] [--keep DIR] [--driver-timeout S] [MODULE ...]

With no MODULE it reads every `.lean` file under `ClassicalLean/` (or `DIR/ClassicalLean/` with
`--root`); a MODULE is a path relative to that folder (`Order/Superadditive.lean`). `--keep DIR`
keeps the generated copies there. `--driver-timeout S` stops the listing driver after S seconds
(1 to 1800), for the tests: the driver's failure then fails the run. Exit 0: `WITNESSGATE PASS`; 1: `WITNESSGATE FAIL`; 2: a setup
error (no `lake`, no `lakefile.toml`, a `lakefile.lean`, an unreadable listing file).

What a witness is. HANDOFF.md §4, "Satisfiability witnesses": an `example` after its module's last
line that applies a theorem to concrete arguments, `example := Full.name (x := …) h₁ h₂ …`, with
the docstring "The hypotheses of `NAME` hold together: …". Lean checks such a block only for type
correctness, so a witness cut short (a hypothesis left out: the block is then a function), one
naming the wrong theorem, or one resting on `sorry` or `native_decide` builds green. This gate
re-reads each one.

How it reads a module (Python). One pass marks every character as code, comment or string, as
Lean's lexer does: block comments `/- … -/` nest (`/-- … -/` and `/-! … -/` are block comments
too), `--` runs to the end of the line, string literals `"…"` with escapes, character literals
(`'"'`, `'\''`) where no identifier is going on (a `'` after an identifier character belongs to
the identifier, as in `h'`), and raw strings `r"…"`, `r#"…"#`. The keyword `example` is found in
code only, by identifier rules (`example'`, `example_x`, `foo.example` are not it). A keyword at
column 0 with nothing before it on its line is a block: `example :=` the witness form, `example :`
the typed form, `example` and a binder bracket the binder form. Its docstring is the comment Lean
attaches: going back from the keyword over whitespace (blank lines too), `--` comments and plain
`/- … -/` comments, the modifiers `private`, `protected`, `noncomputable`, `unsafe`, `partial`,
`nonrec`, an attribute only when its `]` closes a bracket opened by `@[` (matched in code), and
whole `open … in` and `set_option … in` prefixes, the text just before must close a comment opened
with `/--`; a `/-!` comment or code there means no docstring. A docstring reached only by stepping
over such a prefix is not the block's: Lean refuses a docstring followed by `open … in` or
`set_option … in` and attaches it to nothing, so the walk follows Lean (order VACUITY-4, ruling 4,
measured in its layout experiment). Its phrases are read with runs of
whitespace collapsed to one space. The module's `namespace`, `section` and `end` lines give the
namespaces it opens (nested ones joined).

How it checks a witness (Lean). For a module with at least one witness-form block, it writes a
copy of the module's own text outside the repository (`tempfile.mkdtemp`), with four changes and
nothing else: right after the `import` lines, before any module text, the check itself, `def
witnessGateCheck`, and for each block a `def witnessGateCheckL<line>` that calls it with the
block's line, the name its docstring gives and the module's namespaces, each under the two
`set_option` lines below (defined there, every name they use is resolved before the module can
declare one: review (ac2), F2); each witness-form block's keyword `example` is replaced by `noncomputable def
witnessGateL<line>` (its line in the module), so the block elaborates where it stood, in its
namespace, beside the module's private lemmas, under its own `open … in` lines; two lines
`set_option linter.defProp false in` and `set_option linter.style.longLine false in` are put above
the block's first line, because a definition whose type is a proposition, and a longer header,
raise warnings the `example` did not (each on a line of its own, so every command still starts at
column 0); and after the block, at its insertion point, `set_option linter.style.longLine false
in`, the block's own `open … in` lines and `run_cmd witnessGateCheckL<line>`, which prints what
Lean knows of the turned definition (it reads the namespace and the name resolution of that scope
when it runs). The insertion point is the first
later line that is not blank and whose first character, at column 0, is not inside a comment or
string opened on an earlier line, so the check never lands between the next block's docstring and
its keyword. The copy is elaborated with `lake env lean` from the repository root with the
package's `[leanOptions]` read from `lakefile.toml`, one process at a time. Every line number the
gate prints is a line of the module, not of the copy.

How Lean decides where the blocks are (order VACUITY-4, ruling 2, section 3). The Python reading
above is a first pass only. Every module the gate reads is also run, unchanged, through the listing
driver `tools/WitnessListing.lean` (`lake env lean --run`, the same options), a Lean program that
runs Lean's frontend over the module command by command and prints the line and column of every
`example` keyword in the parsed syntax; the gate compares that list with its own keywords, and any
difference is `COPY-ERROR` for the module (review (ac2), F1: strings Lean reads with `{…}` holes
that the lexer misread hid a `sorry` witness from both of the gate's own cross-checks). At each
witness-form block's insertion point, in the scope there, the driver also elaborates the block's
`open … in` and `set_option … in` prefixes in a scratch state, parses the inserted call, and reads
the macro and elaborator entries (`macro`, `command_elab`, `term_elab`, `doElem_elab`) of every
syntax kind the call and `run_cmd`'s expansion `discard do …` pass through, and `in`, `section`,
`end`, `open` and `set_option`; the reading must equal `RUNCMD_BASELINE`, measured with only Lean
core and only the library's Mathlib imports (both gave the same line), else `COPY-ERROR` "run_cmd
changed by module or import" (a library module that changes `run_cmd` needs a ruling, not a gate
edit). The driver also prints, for each `theorem`, `lemma`, `def`, `abbrev`, `instance` and
`opaque`, the constant Lean's info tree names at its identifier and n, its binders before the colon
as Lean elaborated them (the `∀` binders at the head of the constant's type minus those at the
head of the type after the colon: every kind of bracket, section `variable`s and auto-bound
implicits), and for each Batteries `alias` its target constant (for the argument-count rule
below), what it refused (below), the module's own errors (any outside every witness-form block is `COPY-ERROR`: the library builds, so
the driver's reading would not be the build's; one inside a block is the copy's `BROKEN`), any constant whose name has a part
starting `witnessGate` (`COPY-ERROR`), and an end line with its count. Its lines carry a value made
fresh for each run, given on its standard input and never written to a file; a line is read only
if it is exactly one such line, and a key printed twice is `COPY-ERROR`.

What a module may do (order VACUITY-4, ruling 4). A module may not run its own code while Lean
elaborates it, and the gate refuses what it sees of that; what it does not see is the limit stated
after the checks below (review a4c; ruling 6). The driver
parses each command and checks it before it elaborates it; a module it refuses is `COPY-ERROR`
from the driver's own line, nothing after the refused command is elaborated anywhere, no copy is
made, and each witness-form block is `BROKEN` ("not checked"). The checks, each decided by Lean:
* command kinds, by an allowlist (`allowedCommands` in the driver), the kinds the library used at
  the census of 2026-10-26 (run r5-census, 140 modules): `theorem`, `lemma`, `def`, `abbrev`,
  `instance`, `structure`, `example` (declarations: Lean checks them and adds constants; `mutual` is
  not on the list, so a `mutual` block is refused), the module docstring `/-! … -/`, `namespace`, `section`, `end`, `open`, `… in`, `variable`, `omit`,
  `include`, `universe` (scope: names and binders only), `set_option` (an option's value, no code)
  and `attribute` (whose attributes are checked below), and the end of input. A kind outside it,
  harmless or not, is refused: a module that needs one needs a ruling first. `macro`, `elab`,
  `syntax`, `notation`, `initialize`, `run_cmd`, `#eval` and their kin are never on it;
* code inside an allowed command, by a list (`codeKinds`), not an allowlist: `by_elab`,
  `by_elabq`, `run_tac`, `run_cmd`, `run_elab`, `run_meta`, `#eval`, `#eval!` and
  `native_decide`, anywhere in the command's syntax, and the configuration item `native`
  (`decide +native`, `(native := true)`, a field `native := …`). The list was found by asking Lean
  and Mathlib for the kinds they register whose names show they run code (run r5-askkinds), so a
  kind whose name does not show it can be missing (the configuration item was, until review a4,
  F1); since a module can no longer add syntax, Lean's and Mathlib's forms are all there are. A
  form missed here meets the next check only if it leaves a constant behind, and inside a tactic
  branch the elaborator discards it leaves none (review a4c; the limit below);
* attributes, by an allowlist (`allowedAttrs`): `simp` and `instance`, read from every `@[…]` and
  `attribute […]` in the syntax (neither runs code: `simp` adds a rewrite lemma, `instance` a
  candidate for instance search, both of them terms Lean has checked);
* after each command, the constants it added: refused when the type mentions Lean's own machinery
  (a name under `Lean.`, `IO.`, `EIO.`, `BaseIO.`, `ST.`, `EST.`, or `IO`, `EIO`, `BaseIO`, `ST`,
  `EST`), when a constant that is not a proof has such a name, or one with a part starting
  `unsafe`, in its value, when it is an axiom (in Lean v4.34 `native_decide` and `decide +native`
  each add one, `…._native.…ax_…`: run r5-pnative), when it is `unsafe` or carries `implemented_by`
  or `extern`, when its value mentions `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`, `Lean.reduceBool` or
  `Lean.reduceNat` (what older Lean versions leave), and when it mentions a constant refused before. `Lean.`
  names inside proofs are allowed (`omega` leaves them; a proof term runs no code).
The census found none of these refusals in the library.
The limit (review a4c; order VACUITY-4, ruling 6): a module's own pure code can be compiled and run
during elaboration, inside a tactic branch the elaborator then discards (for example a
`(config := ...)` value or `Lean.reduceBool` under `first`), and the gate does not see it. A witness
that rests on such a run is still caught, by the checked copy's axiom check. Whether such a run can
do IO was tried once and not reproduced; it is not excluded.

The verdicts, one line each:

* for a witness-form block (`example :=` at column 0) with a witness docstring
  ("The hypotheses of `NAME` hold together"), in this order:
  * `BROKEN`: an error inside the block, or the definition missing, or an axiom of the definition
    (`Lean.collectAxioms`, through every constant it uses) outside `propext`, `Classical.choice`,
    `Quot.sound` (so `sorryAx`, and `native_decide`'s per-declaration axiom, are caught);
  * `WRONG-NAME`: the head constant of the definition's value (read under its lambdas: named
    arguments followed by missing explicit ones make Lean eta-expand the value) is not the constant
    NAME names. If NAME resolves in the block's own scope (`Lean.resolveGlobalName`, with the
    block's namespace and `open`s) to exactly one constant, the head must be it; to more than one,
    `WRONG-NAME`; to none, exactly one `N.NAME` must exist for a namespace `N` the module opens
    (as a private constant of the module, if not as a public one), and the head must be it;
    Extension E2 (review (a), finding 9; beyond Goal item 1's text, kept by ruling 2, section 5):
    the head must also be a constant of the module itself, as a witness applies its own module's
    theorem;
  * `PARTIAL`: the definition's type, opened with `forallTelescopeReducing` at reducible
    transparency, has a binder whose type is a proposition (instance and implicit binders
    included): a hypothesis is still missing. Extension E1 (review (a), finding 1; beyond Goal
    item 1's text, kept by ruling 2, section 5): also when the value itself opens with a lambda of
    any type (a function over an empty type passes the binder test, but is no witness). Ruling 2,
    section 3 item 4, as ruling 3, section 2 restated it: also when the head is applied to k
    arguments, fewer than the n binders the head declares before its colon. k is read by the
    check from the elaborated value (metadata stripped; parentheses, `@` and type ascriptions
    leave no trace there), and counts every argument Lean put there, including an implicit it
    filled by unification, an instance it synthesised and a default of `optParam` or `autoParam`;
    n is the listing driver's count for the head, compared by Lean's name for the constant
    (`private:<name>` for a private one), following an `alias` to the constant at the end of its
    chain and nothing else (a `theorem` whose value is another constant keeps its own n). The
    reason is "the bare theorem, applied to nothing" when k is 0, else "the theorem, applied to k
    of its n binders before the colon". A head with no count from the driver is `COPY-ERROR` "no
    binder count for <head>", never a count of 0. This rule only turns an `OK` into a `PARTIAL`;
  * `OK`: none of these; its line carries the head, k and n;
* `NO-DOCSTRING`: a witness-form block without a witness docstring (still elaborated and checked);
* `TYPED-CLAIM`: a typed or binder example whose docstring has "hypotheses of", "hypothesis of",
  "can be met" or "hold together" (case ignored); fails;
* `TYPED`: any other typed or binder example at column 0 (Lean has checked it against its stated
  type; passes);
* `NOT-A-BLOCK`: a line inside a comment, docstring or string that matches the pattern below
  (passes);
* `UNREAD`: a line matching `^\s*(@\[.*\]\s*)?(private |noncomputable )*example\b` that is none of
  the forms above (an indented, attributed, `private` or `noncomputable` example), and any
  `example` keyword in code that does not start its line; fails;
* `LISTED`: a block with a matching entry in `tools/witness_reviewed.txt` (or
  `DIR/tools/witness_reviewed.txt` with `--root`); passes; `LISTED-FAULT` for an entry whose reason
  starts `FAULT, later order:`, counted apart;
* `COPY-ERROR <module>`: an error outside every turned block, or a nonzero rc of `lake env lean`
  with no error inside a block, or any fault the listing driver finds (above), or a module the
  driver refused (ruling 4, above); fails.

Lines counted apart, each a failure: `COPY-ERROR`; `STALE-LISTING` (an entry whose hash matches no
block of a module that was read, whose block now gets a different verdict, which names a verdict
that may not be listed, or which repeats another entry's hash); `RANGE-MISMATCH` (Lean's end of the
turned definition is not the last line of code before the insertion point: the copy did not read
the block as the gate did, for example a block whose next line at column 0 continues it); and
`DOC-MISMATCH` (Lean's docstring of the turned definition, `Lean.findDocString?`, whitespace
collapsed, differs from the comment the walk above found: in every run Lean, not the walk, decides
a witness's docstring; order VACUITY-4, ruling 4). `NOTE` lines carry Lean's warnings on a copy and
change no verdict.

The listing file: `#` lines and blank lines are skipped; an entry is five tab-separated fields:
module path, the sha256 of the block's whole source (from its first `open … in` line, modifier,
attribute or docstring line, or its keyword's line, through the end of the definition as Lean read
it), the verdict the block would otherwise get, the sha256 of what Lean reported of the block (its
head, its lambdas, its proposition binders and its axioms; the fifth field, review (a), finding 2,
beyond Goal item 1's text, kept by ruling 2, section 5: a listed block whose theorem changes goes
stale), and a one-line reason.
Each witness-form verdict line ends `[block <sha256> lean <sha256>]`, the two values an entry for it
holds. Entries are matched by module and hash; one entry covers identical blocks of one module.
Only witness-form blocks can be listed, and never a broken one, whatever its verdict (an error, a
missing definition, an axiom outside the three). `NO-DOCSTRING` and `PARTIAL` are blind spots of the
check; a reason starting `FAULT, later order:` may carry `OK`, `PARTIAL`, `WRONG-NAME` or
`NO-DOCSTRING`; any other verdict is refused. On a whole-library run an entry for a module that does
not exist is stale; a run on named modules skips the other modules' entries.

Hardening after review (a) and its confirming passes: the check's markers carry a random value made
fresh for each run, and a marker is read only from a line that is exactly one marker; module code
that reads the value from the copy can then only print a line the real check also prints, and a
value printed twice makes the block `BROKEN`, so a forged marker can make a block fail, never pass,
as long as the real check runs, which the driver's `run_cmd` reading stands for. The lexer, a first
pass, reads the `{…}` holes of interpolated strings as code (`x!"…"`, and a string right after
`throwError`), and a comment or string left open at the end of a file is `COPY-ERROR`; where it
still misreads (review (ac2)'s probes: a line break or a comment between `throwError` and its
string, `s! "…"`, `panic!"{"`), Lean's listing differs and the module is `COPY-ERROR`. Each Lean
run (a copy's, the driver's) runs in its own process group and is stopped, the whole group, after
1800 s (`COPY-ERROR`), and on Ctrl-C or SIGTERM to the gate before the gate exits (review (ac2),
F3). The fingerprint of
a listing entry holds pretty-printed types, so a Lean or Mathlib upgrade that prints a type another
way makes the entry stale: it fails closed, and the entry is listed again.

The last line: `WITNESSGATE PASS` or `WITNESSGATE FAIL`, the modules read and elaborated, every
verdict's count, the lines counted apart, and two cross-checks, each a failure when its two sides
differ: `lines=<verdict lines>/<lines matching the pattern + UNREAD keywords not starting their
line>`, `keywords=<example keywords in code>/<verdicts other than NOT-A-BLOCK>` and
`lean=<example keywords in Lean's listing>/<the gate's, in the same modules>` (ruling 2).

Known limits, stated: a hypothesis hidden behind a definition that reducible unfolding does not
open (`theorem t : P` with `def P := A → B`) passes as `OK`; a theorem whose conclusion itself
opens with a hypothesis binder (`∀ x, x ∈ s → …`) gives a false `PARTIAL`, listed with its reason;
a process that stops moving inside the theorem's horizon is not seen (rule 3's case of the moving
process is met by review); typed and binder examples are not elaborated, only read, so their
docstrings are read by the walk alone (it agreed with Lean on every layout of the order's ruling 4
experiment); a witness wrapped in `show … from`, a projection, `let` or `have` is refused as
`WRONG-NAME` (its head is not the theorem), which fails closed; the lexer's misreadings of strings
are no longer a way to hide a block, since Lean's listing decides (and a module can no longer make
an `example` with its own macro: ruling 4); a theorem whose hypotheses are bundled inside a data
argument (`(x : {n // P n})`) passes as `OK` when the witness applies it but supplies nothing real
inside that argument (review (ac), N3's wider form; only a head applied to fewer arguments than
its binders before the colon is caught), and the unrewritten `OK` blocks are not read for it by
hand; the argument-count rule counts an argument Lean filled from an `optParam` or `autoParam`
default as supplied; it has no count, so gives `COPY-ERROR`, for a head declared by a command
other than those named above (an `alias ⟨…⟩` of an `iff`, a constant made by an attribute such
as `to_additive`, a structure's projection) and for a `def` with no type written; the `run_cmd` reading covers the macro and elaborator
tables of the kinds named above, not a change to how Lean itself runs outside the environment, and
not an imported module's `initialize` (a linter or hook it registers runs on the copy; a library
module with one is itself refused where it is read); an instance on a class of Lean's core
(`Functor`, `Monad`, …) over every monad, whose type names none of Lean's machinery, is allowed,
and `run_cmd`'s call consults such instances (by reasoning, and by fixture c117 for one such instance: an
instance over every monad cannot name the check's messages, so it can at most stop the check from
running, which makes the block `BROKEN`); the code
Lean's and Mathlib's own elaborators, delaborators and option handlers run is not the module's
and is not checked (a `set_option` can change how they behave; the census found four options:
`backward.isDefEq.respectTransparency`, `linter.defProp`, `linter.style.haveILetI`,
`maxHeartbeats`); a module's pure definitions can still be compiled and run by Lean's own
elaborators (a tactic's configuration term, `Lean.reduceBool`), unseen inside a branch the
elaborator discards (the limit stated above, review a4c); and the check's fingerprint
and props text use `ppExpr`, which only Lean's and Mathlib's delaborators now act on.

Scope of the fixtures (`tools/witness-fixtures/`, read by `tools/witness_gate_tests.py`): they lie
outside every other gate. `tools/check_sorry.py` skips `tools/` (its `SKIP_DIRS`) and walks
`ClassicalLean/`; `tools/banned_vocab_scan.py` is run on `ClassicalLean` and the root file beside
it; `tools/compile_rules.py` opens only the rule registry, its base copy and `HANDOFF.md`;
`tools/check_records.py` walks only `ClassicalLean/`; the axiom and vacuity gates import
`ClassicalLean`, which does not contain them.
"""
import hashlib
import os
import re
import secrets
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import tomllib

PATTERN = re.compile(r"^\s*(@\[.*\]\s*)?(private |noncomputable )*example\b")
WITNESS = re.compile(r"The hypotheses of `([^`]+)` hold together")
CLAIMS = ("hypotheses of", "hypothesis of", "can be met", "hold together")
MODIFIERS = {"private", "protected", "noncomputable", "unsafe", "partial", "nonrec"}
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
LISTABLE = {"NO-DOCSTRING", "PARTIAL"}
FAULT_LISTABLE = {"OK", "PARTIAL", "WRONG-NAME", "NO-DOCSTRING"}
FAULT_PREFIX = "FAULT, later order:"
TURNED = "witnessGate"
PREFIX_LINES = ["set_option linter.defProp false in", "set_option linter.style.longLine false in"]
DRIVER = "tools/WitnessListing.lean"
# What the driver reads of `run_cmd` at a probe point (ruling 2, section 3 item 3): measured on
# 2026-10-26 in an environment importing only Lean core (`import Lean`) and in one importing the
# 215 Mathlib modules the library's headers import (wl/baseline/, runs baseline2-Core and
# baseline2-Mathlib); all six readings were this one line. The kinds: `run_cmd`'s syntax and the
# term `discard do …` its elaborator builds (BuiltinEvalCommand.lean, `elabRunCmd`), and `in`,
# `section`, `end`, `open` and `set_option`, which the inserted prefixes pass through.
RUNCMD_BASELINE = " ;; ".join([
    'core=Lean.runCmd("run_cmd",Lean.Parser.Term.doSeqIndent(null(Lean.Parser.Term.doSeqItem(Lean.Parser.Term.doExpr(ID),null()))));term=Lean.Parser.Term.app(ID,null(Lean.Parser.Term.do("do",Lean.Parser.Term.doSeqIndent(null(Lean.Parser.Term.doSeqItem(Lean.Parser.Term.doExpr(ID),null()))))));entries=ident:macro=/command=/term=Lean.Elab.Term.elabIdent/do=',
    'null:macro=/command=/term=/do=',
    'Lean.runCmd:macro=/command=Lean.Elab.Command.elabRunCmd/term=/do=',
    'Lean.Parser.Command.end:macro=/command=Lean.Elab.Command.elabEnd/term=/do=',
    'Lean.Parser.Command.in:macro=Lean.Elab.Command.expandInCmd/command=/term=/do=',
    'Lean.Parser.Command.open:macro=/command=Lean.Elab.Command.elabOpen/term=/do=',
    'Lean.Parser.Command.section:macro=/command=Lean.Elab.Command.elabSection/term=/do=',
    'Lean.Parser.Command.set_option:macro=/command=Lean.Elab.Command.elabSetOption/term=/do=',
    'Lean.Parser.Term.app:macro=/command=/term=Lean.Elab.Term.elabApp/do=',
    'Lean.Parser.Term.do:macro=/command=/term=Lean.Elab.Term.elabDo/do=',
    'Lean.Parser.Term.doExpr:macro=/command=/term=/do=Lean.Elab.Do.elabDoExpr',
    'Lean.Parser.Term.doSeqIndent:macro=/command=/term=/do=',
    'Lean.Parser.Term.doSeqItem:macro=/command=/term=/do=',
])
PREFIX_KINDS = {"Lean.Parser.Command.open", "Lean.Parser.Command.set_option"}


def ident_char(ch):
    return ch.isalnum() or ch in "_'!?" or ch in "«»"


# ---------------------------------------------------------------------------------------------
# The lexer: code, comments and strings, as Lean reads them.

class Comment:
    def __init__(self, start, end, kind):
        self.start, self.end, self.kind = start, end, kind   # kind: line, block, doc, moddoc


def lex(text):
    """Return (mask, comments, problems): mask[i] is 'c' (code), 'm' (comment) or 's' (string);
    problems lists every comment or string still open at the end of the file (a file that builds
    has none, so one means the lexer and Lean disagree: review (a), finding 3)."""
    n = len(text)
    mask = ["c"] * n
    comments = []
    problems = []
    _scan(text, 0, n, mask, comments, problems, False)
    return mask, comments, problems


INTERP_WORDS = ("throwError",)


def _interpolated(text, i):
    """Is the `"` at i the start of an interpolated string? `s!"`, `m!"`, `f!"` (any `x!"`), and a
    string right after `throwError`, which Lean also reads with holes (review (ac), N2, measured
    there). Other forms that may read holes (`throwErrorAt t "…"`, `trace[…] "…"`, `dbg_trace "…"`,
    not measured) are not recognised: a stated limit."""
    if i >= 2 and text[i - 1] == "!" and ident_char(text[i - 2]):
        return True
    j = i
    while j > 0 and text[j - 1] in " \t":
        j -= 1
    return any(text[:j].endswith(w) and (j == len(w) or not ident_char(text[j - len(w) - 1]))
               for w in INTERP_WORDS)


def _scan(text, i, n, mask, comments, problems, in_hole):
    """Lex text[i:] as code; in a hole of an interpolated string, stop at its closing `}` and
    return the index just after it."""
    depth = 0
    while i < n:
        ch = text[i]
        if in_hole and ch == "{":
            depth += 1
        elif in_hole and ch == "}":
            if depth == 0:
                return i + 1
            depth -= 1
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                mask[k] = "m"
            comments.append(Comment(i, j, "line"))
            i = j
            continue
        if text.startswith("/-", i):
            kind = "doc" if text.startswith("/--", i) and not text.startswith("/--/", i) else (
                "moddoc" if text.startswith("/-!", i) else "block")
            # its own counter: the hole's brace count `depth` must survive a comment inside the
            # hole (review (ac), N1)
            cdepth, j = 1, i + 2
            while j < n and cdepth:
                if text.startswith("/-", j):
                    cdepth += 1
                    j += 2
                elif text.startswith("-/", j):
                    cdepth -= 1
                    j += 2
                else:
                    j += 1
            if cdepth:
                problems.append((i, "a block comment that never closes"))
            for k in range(i, j):
                mask[k] = "m"
            comments.append(Comment(i, j, kind))
            i = j
            continue
        if ch == '"':
            interp = _interpolated(text, i)
            j = i + 1
            while j < n and text[j] != '"':
                if text[j] == "\\":
                    j += 2
                    continue
                if interp and text[j] == "{":
                    for k in range(i, j + 1):
                        mask[k] = "s"
                    j = _scan(text, j + 1, n, mask, comments, problems, True)
                    mask[j - 1] = "s"
                    i = j
                    continue
                j += 1
            if j >= n:
                problems.append((i, "a string that never closes"))
            j = min(j + 1, n)
            for k in range(i, j):
                mask[k] = "s"
            i = j
            continue
        if ch == "r" and (i == 0 or not ident_char(text[i - 1])):
            m = re.match(r'r(#*)"', text[i:])
            if m:
                close = '"' + m.group(1)
                j = text.find(close, i + len(m.group(0)))
                if j < 0:
                    problems.append((i, "a raw string that never closes"))
                j = n if j < 0 else j + len(close)
                for k in range(i, j):
                    mask[k] = "s"
                i = j
                continue
        if ch == "'" and (i == 0 or not ident_char(text[i - 1])):
            m = re.match(r"'(\\u\{[0-9a-fA-F]+\}|\\x[0-9a-fA-F]{2}|\\.|[^\\'\n])'", text[i:])
            if m:
                j = i + len(m.group(0))
                for k in range(i, j):
                    mask[k] = "s"
                i = j
                continue
        if ch == "«":
            j = text.find("»", i)
            i = n if j < 0 else j + 1
            continue
        i += 1
    if in_hole:
        problems.append((i, "an interpolated string's `{` that never closes"))
    return n


# ---------------------------------------------------------------------------------------------
# One module, read as text.

class Block:
    def __init__(self, line, form):
        self.line = line            # 1-based line of the keyword
        self.form = form            # witness, typed, binder
        self.doc = None             # Comment or None
        self.first = line           # 1-based first line of the block's source
        self.prefixes = []          # the block's own `open … in` / `set_option … in` texts
        self.insert = None          # 1-based line before which the check goes (None: end of file)
        self.last_code = line       # 1-based last line with code before the insertion point
        self.verdict = None
        self.detail = ""


class Module:
    def __init__(self, rel, text):
        self.rel, self.text = rel, text
        self.lines = text.split("\n")
        self.starts = [0]
        for ln in self.lines[:-1]:
            self.starts.append(self.starts[-1] + len(ln) + 1)
        self.mask, self.comments, self.problems = lex(text)
        self.comment_end = {c.end: c for c in self.comments}
        self.comment_at = {}
        for c in self.comments:
            self.comment_at[c.start] = c
        self.namespaces = []
        self.blocks = []            # every keyword at column 0 in one of the three forms
        self.unread = []            # (line, why)
        self.not_a_block = []       # lines
        self.keywords = 0
        self.keyword_pos = []       # (line, column) of each `example` keyword in code
        self.pattern_lines = 0
        self.nonstart_keywords = 0

    def line_of(self, pos):
        lo, hi = 0, len(self.starts) - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if self.starts[mid] <= pos:
                lo = mid
            else:
                hi = mid - 1
        return lo + 1

    def code(self, pos):
        return self.mask[pos] == "c"

    # -- the docstring walk ---------------------------------------------------------------
    def word_before(self, p):
        j = p
        while j > 0 and self.code(j - 1) and ident_char(self.text[j - 1]):
            j -= 1
        while j > 0 and self.code(j - 1) and self.text[j - 1] == "." and j - 1 > 0 and ident_char(self.text[j - 2]):
            j -= 1
            while j > 0 and self.code(j - 1) and ident_char(self.text[j - 1]):
                j -= 1
        return j, self.text[j:p]

    def skip_space(self, p):
        while p > 0 and self.code(p - 1) and self.text[p - 1] in " \t\r\n":
            p -= 1
        return p

    def prefix_start(self, p):
        """p ends just after a word `in`; return the start of a whole `open … in` or
        `set_option … in` prefix ending there, or None."""
        q = p - 2
        lo = self.starts[self.line_of(q) - 1]
        seg = self.text[lo:q]
        if any(not self.code(k) for k in range(lo, q)):
            return None
        m = re.search(r"(?:^|(?<=\s))(open|set_option)\s[^\n]*$", seg)
        if not m or not seg[:m.start()].strip() == "":
            return None
        return lo + m.start()

    def walk(self, p):
        """Walk back from the keyword at p; return (doc, prefixes, first_pos).

        A docstring found only after stepping over an `open … in` or `set_option … in` prefix is
        not the block's: Lean refuses that text (`unexpected token 'open'; expected 'lemma'`) and
        attaches no docstring (order VACUITY-4, ruling 4: the layout experiment's L7 and L9), so the
        walk follows Lean and reports none."""
        prefixes = []
        first = p
        crossed = False
        while True:
            p = self.skip_space(p)
            if p == 0:
                return None, prefixes, first
            if not self.code(p - 1):
                c = self.comment_end.get(p)
                if c is None:
                    return None, prefixes, first
                if c.kind in ("line", "block"):
                    p = c.start
                    continue
                if c.kind == "doc":
                    return (None if crossed else c), prefixes, first
                return None, prefixes, first
            ch = self.text[p - 1]
            if ch == "]":
                depth, j = 0, p - 1
                while j >= 0:
                    if self.code(j):
                        if self.text[j] == "]":
                            depth += 1
                        elif self.text[j] == "[":
                            depth -= 1
                            if depth == 0:
                                break
                    j -= 1
                if j > 0 and self.text[j - 1] == "@" and self.code(j - 1):
                    # the attribute belongs to the block (review (a), finding 5)
                    p = first = j - 1
                    continue
                return None, prefixes, first
            j, w = self.word_before(p)
            if w in MODIFIERS:
                p = first = j
                continue
            if w == "in":
                s = self.prefix_start(p)
                if s is None:
                    return None, prefixes, first
                prefixes.insert(0, self.text[s:p])
                p = first = s
                crossed = True
                continue
            return None, prefixes, first

    def outer_prefixes(self, p):
        """From a docstring's start, the whole `open … in` / `set_option … in` prefixes above it."""
        prefixes = []
        first = p
        while True:
            q = self.skip_space(p)
            if q == 0 or not self.code(q - 1):
                return prefixes, first
            j, w = self.word_before(q)
            if w != "in":
                return prefixes, first
            s = self.prefix_start(q)
            if s is None:
                return prefixes, first
            prefixes.insert(0, self.text[s:q])
            p = first = s

    # -- reading the module ------------------------------------------------------------------
    def read(self):
        text, n = self.text, len(self.text)
        # namespaces
        stack = []
        for i, ln in enumerate(self.lines):
            if not ln or not self.code(self.starts[i]):
                continue
            m = re.match(r"namespace\s+([^\s]+)", ln)
            if m:
                stack.append(("ns", m.group(1)))
                cur = ".".join(name for kind, name in stack if kind == "ns")
                if cur not in self.namespaces:
                    self.namespaces.append(cur)
                continue
            if re.match(r"(noncomputable\s+)?section\b", ln):
                stack.append(("sec", ""))
                continue
            if re.match(r"end\b", ln) and stack:
                stack.pop()
        # keywords
        for m in re.finditer(r"example", text):
            i = m.start()
            if not self.code(i):
                continue
            if i > 0 and (ident_char(text[i - 1]) or text[i - 1] == "."):
                continue
            j = m.end()
            if j < n and ident_char(text[j]):
                continue
            self.keywords += 1
            ln = self.line_of(i)
            col = i - self.starts[ln - 1]
            self.keyword_pos.append((ln, col))
            if col == 0:
                rest = self.lines[ln - 1]
                if rest.startswith("example :="):
                    form = "witness"
                elif rest.startswith("example :"):
                    form = "typed"
                elif re.match(r"example\s*(\(|\{|\[|⦃)", rest):
                    form = "binder"
                else:
                    form = None
                if form:
                    b = Block(ln, form)
                    doc, pre, first = self.walk(i)
                    b.doc = doc
                    if doc is not None:
                        pre2, first2 = self.outer_prefixes(doc.start)
                        pre = pre2 + pre
                        first = first2
                    b.prefixes = pre
                    b.first = self.line_of(first)
                    self.blocks.append(b)
                else:
                    self.unread.append((ln, "an `example` at column 0 in none of the three forms"))
            else:
                if not PATTERN.match(self.lines[ln - 1]):
                    self.nonstart_keywords += 1
                    self.unread.append((ln, "an `example` keyword that does not start its line"))
        # pattern lines
        block_lines = {b.line for b in self.blocks}
        unread_lines = {ln for ln, _ in self.unread}
        for i, ln in enumerate(self.lines):
            if not PATTERN.match(ln):
                continue
            self.pattern_lines += 1
            first_nonspace = self.starts[i] + (len(ln) - len(ln.lstrip()))
            if not self.code(first_nonspace):
                self.not_a_block.append(i + 1)
            elif (i + 1) not in block_lines and (i + 1) not in unread_lines:
                self.unread.append((i + 1, "a line matching the pattern that is none of the forms"))
        # insertion points and last code lines of witness-form blocks
        for b in self.blocks:
            if b.form != "witness":
                continue
            ip = None
            for k in range(b.line, len(self.lines)):          # 0-based index of line k + 1
                s = self.lines[k]
                if not s.strip():
                    continue
                pos = self.starts[k]
                if s[0] in " \t":
                    continue
                if self.code(pos) or self.comment_at.get(pos) is not None or (
                        self.mask[pos] == "s" and (pos == 0 or self.mask[pos - 1] != "s")):
                    ip = k + 1
                    break
            b.insert = ip
            end = (ip - 1) if ip else len(self.lines)
            last = b.line
            for k in range(b.line, end + 1):
                s = self.lines[k - 1]
                p0 = self.starts[k - 1]
                if any(self.code(p0 + c) and not s[c].isspace() for c in range(len(s))):
                    last = k
            b.last_code = last

    def doc_text(self, b):
        if b.doc is None:
            return None
        return self.text[b.doc.start + 3:b.doc.end - 2]


def collapse(s):
    return " ".join(s.split())


def classify_text(mod, b):
    """Verdicts the text alone decides; witness-form blocks are decided later with Lean."""
    d = mod.doc_text(b)
    if b.form == "witness":
        m = WITNESS.search(collapse(d)) if d is not None else None
        b.name = m.group(1) if m else None
        return
    low = collapse(d).lower() if d is not None else ""
    if any(ph in low for ph in CLAIMS):
        b.verdict = "TYPED-CLAIM"
        b.detail = "a typed or binder example whose docstring claims a witness"
    else:
        b.verdict = "TYPED"


# ---------------------------------------------------------------------------------------------
# The copy and its check.

def lean_str(x):
    return '"' + x.replace("\\", "\\\\").replace('"', '\\"') + '"'


def check_def(nonce):
    """The check, defined once, right after the copy's `import` lines and before any module text,
    so every name it uses is resolved before the module can declare one (review (ac2), F2: a
    module's own `Fix.Lean.Meta.isProp` shadowed the check's call when the check was pasted inside
    the module's namespace). Every value it prints is bracketed by markers that carry `nonce`, a
    random value made fresh for each run (review (a), finding 4). What it reads of the scope (the
    current namespace, name resolution) it reads when it runs, at the block's call."""
    return PREFIX_LINES + f'''def {TURNED}Check (line : Nat) (nm : String) (nss : List String) :
    Lean.Elab.Command.CommandElabM Unit := do
  let env ← Lean.getEnv
  let fold := fun (s : String) => s.replace "\\n" " "
  let emit := fun (k v : String) => Lean.logInfo m!"@@WG{nonce}|{{line}}|{{k}}|{{fold v}}|WG{nonce}@@"
  let n0 := Lean.Name.append (← Lean.getCurrNamespace) (Lean.Name.mkSimple ("{TURNED}L" ++ toString line))
  let n := if env.contains n0 then n0 else Lean.mkPrivateName env n0
  match env.find? n with
  | none => emit "missing" ""
  | some ci =>
    let (lams, head, hm, nargs, hid) ← Lean.Elab.Command.liftTermElabM <| match ci.value? with
      | some v => Lean.Meta.lambdaTelescope v fun xs b => do
          -- the head constant and the number of arguments it is applied to, metadata stripped at
          -- every step of the application (ruling 3, section 2 item 1)
          let mut e ← Lean.instantiateMVars b
          let mut k := 0
          repeat
            match e with
            | .mdata _ e' => e := e'
            | .app f _ =>
              e := f
              k := k + 1
            | _ => break
          let c? := e.constName?
          let hm := match c? with
            | some c => if (env.getModuleIdxFor? c).isNone then "local" else "imported"
            | none => "none"
          let hid := match c? with
            | some c => if Lean.isPrivateName c then "private:" ++ toString (Lean.privateToUserName c)
                else toString c
            | none => "?"
          pure (xs.size, (c?.map toString).getD "?", hm, k, hid)
      | none => pure (0, "?", "none", 0, "?")
    emit "head" head
    emit "lams" (toString lams)
    emit "headmod" hm
    emit "nargs" (toString nargs)
    emit "headid" hid
    let res ← Lean.Elab.Command.liftCoreM <| Lean.resolveGlobalName (String.toName nm)
    let resolved := res.filterMap fun (c, fs) =>
      if fs.isEmpty && env.contains c then some (toString c) else none
    emit "resolved" (String.intercalate "," resolved)
    let cands := nss.filterMap fun s =>
      let c := Lean.Name.append (String.toName s) (String.toName nm)
      -- a private theorem is stored under its private name (ruling 3, fixture c90)
      if env.contains c then some (toString c)
      else if env.contains (Lean.mkPrivateName env c) then some (toString (Lean.mkPrivateName env c))
      else none
    emit "candidates" (String.intercalate "," cands)
    let axs ← Lean.collectAxioms n
    emit "axioms" (String.intercalate "," (axs.toList.map toString))
    let props ← Lean.Elab.Command.liftTermElabM <| Lean.Meta.withReducible <|
      Lean.Meta.forallTelescopeReducing ci.type fun xs _ => do
        let mut out : Array String := #[]
        for x in xs do
          let t ← Lean.Meta.inferType x
          if ← Lean.Meta.isProp t then
            out := out.push (toString (← Lean.Meta.ppExpr t))
        return out
    emit "props" (toString props.size ++ " " ++ String.intercalate " ;; " props.toList)
    match ← Lean.findDeclarationRanges? n with
    | some r => emit "range" s!"{{r.range.pos.line}}:{{r.range.pos.column}}-{{r.range.endPos.line}}:{{r.range.endPos.column}}"
    | none => emit "range" "none"
    match ← Lean.findDocString? env n with
    | some d => emit "doc" d
    | none => emit "doc" "NONE"
'''.split("\n")[:-1]


def block_def(line, name, namespaces):
    """One block's call, defined before the module text with the check: the inserted `run_cmd`
    names only it, so the `run_cmd` line holds no literal and no other name."""
    nss = ", ".join(lean_str(n) for n in namespaces)
    nm = name if name is not None else "_"
    return PREFIX_LINES + [f"def {TURNED}CheckL{line} : Lean.Elab.Command.CommandElabM Unit :=",
                           f"  {TURNED}Check {line} {lean_str(nm)} [{nss}]"]


def call_lines(b):
    """The text inserted after a block: the `set_option` first, so it also covers the copied
    `open … in` lines (finding 10), then those lines, then the call."""
    return (["set_option linter.style.longLine false in"] + [p.strip() for p in b.prefixes]
            + [f"run_cmd {TURNED}CheckL{b.line}"])


def header_end(mod):
    """The last line of the module's header (its `module` and `import` lines, with comments and
    blank lines between), as Lean reads a header; 0 when there is none."""
    last = 0
    for i, ln in enumerate(mod.lines, 1):
        start = mod.starts[i - 1]
        code = "".join(ch for k, ch in enumerate(ln) if mod.code(start + k)).strip()
        if not code:
            continue
        if code == "module" or re.match(r"(?:(?:public|meta|private)\s+)*import\s", code):
            last = i
            continue
        break
    return last


def build_copy(mod, nonce):
    """Return (copy text, map from copy line to module line or None)."""
    wit = [b for b in mod.blocks if b.form == "witness"]
    before = {}       # module line -> list of (order, lines)
    at_end = []
    head = check_def(nonce)
    for b in wit:
        head = head + block_def(b.line, b.name, mod.namespaces)
        before.setdefault(b.first, []).append((1, PREFIX_LINES))
        chk = call_lines(b)
        if b.insert is None:
            at_end.append(chk)
        else:
            before.setdefault(b.insert, []).append((0, chk))
    hend = header_end(mod)
    out, cmap = [], []
    if hend == 0:
        for e in head:
            out.append(e)
            cmap.append(None)
    wit_lines = {b.line for b in wit}
    for i, ln in enumerate(mod.lines, 1):
        for order, extra in sorted(before.get(i, []), key=lambda t: t[0]):
            for e in extra:
                out.append(e)
                # the two prefix lines belong to the block whose first line follows them; the
                # check's lines belong to no module line
                cmap.append(i if order == 1 else None)
        if i in wit_lines:
            ln = f"noncomputable def {TURNED}L{i}" + ln[len("example"):]
        out.append(ln)
        cmap.append(i)
        if i == hend:
            for e in head:
                out.append(e)
                cmap.append(None)
    for chk in at_end:
        out.append("")
        cmap.append(None)
        for e in chk:
            out.append(e)
            cmap.append(None)
    text = "\n".join(out)
    return (text if text.endswith("\n") else text + "\n"), cmap


HEADER = re.compile(r"^(?P<path>.+?):(?P<line>\d+):(?P<col>\d+): (?P<sev>error|warning|info)(?:\([^)]*\))?: ?(?P<msg>.*)$")


TIMEOUT = 1800   # seconds for one Lean run (finding 10); a run that takes longer fails
DRIVER_TIMEOUT = [TIMEOUT]   # `--driver-timeout`, lower only: the M1 fixture (ruling 4, item 8)


def _stop(p):
    """Stop a Lean run's whole process group and wait for it (review (ac2), F3)."""
    try:
        os.killpg(p.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    p.wait()


def run_lean(cmd, repo, stdin_text=None, timeout=TIMEOUT):
    """Run `cmd` in its own process group (so a stop reaches `lean`, not only `lake`: review (ac),
    N7). Returns (rc, output), rc None on a timeout. On any other way out (Ctrl-C, SIGTERM, which
    `main` turns into an exception) the group is stopped first, then the exception goes on. Its
    process group's id goes to the standard error, for the signal test."""
    p = subprocess.Popen(cmd, cwd=repo, stdin=subprocess.DEVNULL if stdin_text is None else subprocess.PIPE,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                         start_new_session=True)
    print(f"LEAN-SESSION {p.pid}", file=sys.stderr, flush=True)
    try:
        out, _ = p.communicate(input=stdin_text, timeout=timeout)
    except subprocess.TimeoutExpired:
        _stop(p)
        return None, ""
    except BaseException:
        _stop(p)
        raise
    return p.returncode, out


def run_copy(mod, repo, opts, workdir, nonce):
    text, cmap = build_copy(mod, nonce)
    path = os.path.join(workdir, mod.rel.replace("/", "__"))
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)
    rc, out = run_lean(["lake", "env", "lean"] + opts + [path], repo)
    if rc is None:
        return None, [], {}, cmap, ""
    msgs = []        # (sev, copy line, text)
    cur = None
    wg = {}
    # Each value the check prints is one whole line: the check folds newlines into spaces. A
    # marker is read only from a line that is exactly one marker, so text that opens a marker in
    # one message cannot swallow a later one; a forged line can only repeat a key the real check
    # also prints, which makes the block BROKEN (review (ac), N4).
    whole = re.compile(rf"^@@WG{nonce}\|(\d+)\|(\w+)\|(.*)\|WG{nonce}@@$")
    for ln in out.split("\n"):
        m = HEADER.match(ln)
        if m and os.path.abspath(m.group("path")) == os.path.abspath(path):
            cur = [m.group("sev"), int(m.group("line")), m.group("msg")]
            msgs.append(cur)
            continue
        w = whole.match(ln)
        if w:
            cur = None
            d = wg.setdefault(int(w.group(1)), {})
            if w.group(2) in d:
                d["duplicate"] = w.group(2)
            d[w.group(2)] = w.group(3)
            continue
        if f"@@WG{nonce}" in ln:
            cur = None
            continue
        if cur is not None:
            cur[2] += " " + ln
    return rc, msgs, wg, cmap, out


class Listing:
    """What the listing driver (`tools/WitnessListing.lean`) printed for one module."""
    def __init__(self):
        self.errors = []        # COPY-ERROR reasons
        self.ex = []            # (line, column) of each `example` keyword Lean parsed
        self.count = 0
        self.refusals = []      # why the driver refused the module, before elaborating (ruling 4)
        self.sigs = {}          # constant -> n, its binders before the colon ("?" if not read)
        self.aliases = {}       # constant made by `alias` -> its target constant
        self.error_lines = []   # the module's own errors, by line
        self.failed = False     # no complete reading (its own COPY-ERROR says why)


def run_driver(mod, path, repo, opts):
    """Run the listing driver on the original module (ruling 2, section 3 items 1 and 3). Its
    value is made fresh for this run and given on its standard input, never in a file; a line is
    read only if it is exactly one such line, and a key printed twice is `COPY-ERROR`."""
    lst = Listing()
    dn = secrets.token_hex(16)
    wit = [b for b in mod.blocks if b.form == "witness"]
    feed = [dn] + [f"{b.insert if b.insert is not None else 10 ** 9} {b.line} " + "\\n".join(call_lines(b))
                   for b in wit]
    rc, out = run_lean(["lake", "env", "lean", "--run", DRIVER, path] + opts, repo, "\n".join(feed) + "\n",
                       timeout=DRIVER_TIMEOUT[0])
    if rc is None:
        lst.errors.append(f"the listing driver took more than {DRIVER_TIMEOUT[0]} s and was stopped")
        lst.failed = True
        return lst
    if rc != 0:
        lst.errors.append(f"the listing driver failed (rc {rc}): {collapse(out)[:200]}")
        lst.failed = True
        return lst
    line = re.compile(rf"^@@WD{dn}\|(.*)\|WD{dn}@@$")
    seen = set()
    probes = {}
    end = errs = None
    for ln in out.split("\n"):
        m = line.match(ln)
        if not m:
            continue
        pl = m.group(1)
        kind, _, rest = pl.partition("|")
        key = pl if kind in ("ex", "clash", "sig", "alias", "nosig") else kind + "|" + rest.split("|")[0]
        # what the driver lists of each command (ruling 4) is information, and may repeat
        if key in seen and kind not in ("error", "cmd", "inner", "attr", "opt", "deny4", "refuse"):
            lst.errors.append(f"the listing driver printed `{key[:80]}` twice")
        seen.add(key)
        if kind == "ex":
            a, _, c = rest.partition(":")
            lst.ex.append((int(a), int(c)))
        elif kind == "probe":
            bl, _, val = rest.partition("|")
            probes[int(bl)] = val
        elif kind == "refuse":
            lst.refusals.append(rest)
        elif kind == "sig":
            c, n, _ = rest.rsplit("|", 2)
            lst.sigs[c] = n
        elif kind == "alias":
            c, _, t = rest.partition("|")
            lst.aliases[c] = t
        elif kind == "clash":
            lst.errors.append(f"a constant named `{rest}` exists: the gate's own names start "
                              f"`{TURNED}`, so the copy's could clash")
        elif kind == "error":
            lst.error_lines.append(int(rest))
        elif kind == "errors":
            errs = int(rest)
        elif kind == "end":
            end = int(rest)
    if end is None:
        lst.errors.append("the listing driver printed no end line")
        lst.failed = True
    elif end != len(lst.ex):
        lst.errors.append(f"the listing driver's end line says {end} `example` keywords, it printed {len(lst.ex)}")
    if lst.refusals:
        # the driver stopped before the refused command: nothing after it was elaborated, so its
        # lists are partial and nothing else is compared (ruling 4, section 2 item 1)
        lst.count = len(lst.ex)
        return lst
    # an error inside a witness-form block is the copy's to judge (`BROKEN`); any other error means
    # the module does not build, so the driver's reading is not the build's
    spans = [(b.first, b.last_code) for b in wit]
    outside = [ln for ln in lst.error_lines if not any(lo <= ln <= hi for lo, hi in spans)]
    if errs is None or errs != len(lst.error_lines):
        lst.errors.append("the listing driver's error lines do not match its error count")
    elif outside:
        lst.errors.append(f"the module has {len(outside)} error(s) outside every witness-form block in the "
                          f"listing driver's run, first at line {outside[0]} (the library builds, so the "
                          "driver's reading is not the build's)")
    lst.count = len(lst.ex)
    # Lean's `example` keywords against the gate's
    lean, gate = sorted(lst.ex), sorted(mod.keyword_pos)
    if lean != gate:
        only_l = [f"{a}:{c}" for a, c in lean if (a, c) not in gate]
        only_g = [f"{a}:{c}" for a, c in gate if (a, c) not in lean]
        lst.errors.append(f"Lean's listing of `example` keywords differs from the gate's: Lean only at "
                          f"[{', '.join(only_l[:5])}], the gate only at [{', '.join(only_g[:5])}]")
    # `run_cmd` at each block's call, against the baseline
    for b in wit:
        val = probes.get(b.line)
        if val is None:
            lst.errors.append(f"the listing driver read no scope for the block at line {b.line}")
            continue
        # `err=…;pre=…;` then the reading compared with the baseline (`core=…;term=…;entries=…`)
        if not val.startswith("err=false;"):
            lst.errors.append(f"at the block at line {b.line}: the call does not parse there ({val[:160]})")
            continue
        parts = val.split(";", 2)
        fields = dict(f.split("=", 1) for f in parts[:2])
        rest = parts[2] if len(parts) > 2 else ""
        pre = [k for k in fields.get("pre", "").split(",") if k]
        why = None
        if any(k not in PREFIX_KINDS for k in pre):
            why = f"a prefix is not `open` or `set_option` ({', '.join(pre)})"
        elif rest != RUNCMD_BASELINE:
            got, want = rest.split(" ;; "), RUNCMD_BASELINE.split(" ;; ")
            diff = [g for g in got if g not in want][:2] or [w for w in want if w not in got][:2]
            why = f"run_cmd changed by module or import: {' ;; '.join(diff)[:240]}"
        if why:
            lst.errors.append(f"at the block at line {b.line}: {why}")
    return lst


def module_line(cmap, copy_line):
    if 1 <= copy_line <= len(cmap):
        return cmap[copy_line - 1]
    return None


def binder_count(c, lst):
    """n for the constant `c` as the listing driver read it, following `alias` to its end (ruling 3,
    section 2 items 2 and 3); None when the driver gave no count."""
    seen = set()
    while c in lst.aliases and c not in seen:
        seen.add(c)
        c = lst.aliases[c]
    if c in seen:
        return None
    n = lst.sigs.get(c)
    return int(n) if n is not None and n.isdigit() else None


def decide(mod, rc, msgs, wg, cmap, lst=None):
    """Verdicts for the module's witness-form blocks; returns (copy_errors, range_mm, doc_mm, notes)."""
    wit = [b for b in mod.blocks if b.form == "witness"]
    spans = [(b, b.first, b.last_code) for b in wit]
    copy_errors, range_mm, doc_mm, notes = [], [], [], []
    errors_in = {b.line: [] for b in wit}
    outside = []
    if rc is None:
        copy_errors.append(f"the Lean run took more than {TIMEOUT} s and was stopped")
    for sev, cl, text in msgs:
        ml = module_line(cmap, cl)
        if sev == "error":
            hit = None
            if ml is not None:
                for b, lo, hi in spans:
                    if lo <= ml <= hi:
                        hit = b
            if hit is not None:
                errors_in[hit.line].append((ml, text))
            else:
                outside.append((ml, cl, text))
        elif sev == "warning":
            notes.append((ml, collapse(text)[:300]))
    if outside or (rc not in (0, None) and not any(errors_in.values())):
        if outside:
            ml, cl, text = outside[0]
            where = f"line {ml}" if ml is not None else f"copy line {cl} (an inserted line)"
            copy_errors.append(f"{len(outside)} error(s) outside every turned block; first at {where}: "
                               f"{collapse(text)[:200]}")
        else:
            copy_errors.append(f"lake env lean rc {rc} with no error inside a turned block")
    for b in wit:
        info = wg.get(b.line, {})
        # Lean's extent of the turned definition
        rng = info.get("range")
        lean_end = None
        if rng and rng != "none":
            m = re.match(r"(\d+):(\d+)-(\d+):(\d+)", rng)
            if m:
                e_line = module_line(cmap, int(m.group(3)))
                lean_end = (e_line, int(m.group(4)))
                if e_line != b.last_code:
                    range_mm.append((b.line, f"Lean's end of the turned definition is line {e_line}, "
                                     f"the last code line before the insertion point is {b.last_code}"))
        b.lean_end = lean_end
        # Lean's docstring against the walk's
        if "doc" in info:
            ld = None if info["doc"] == "NONE" else collapse(info["doc"])
            pd = mod.doc_text(b)
            pd = None if pd is None else collapse(pd)
            if ld != pd:
                doc_mm.append((b.line, f"Lean reads {ld!r:.120}, the walk read {pd!r:.120}"))
        errs = errors_in[b.line]
        axs = [a for a in info.get("axioms", "").split(",") if a]
        # what makes a block broken, whatever its docstring (a broken block may never be listed,
        # under any verdict: review (a), finding 2)
        broken = None
        if "duplicate" in info:
            broken = f"the check printed `{info['duplicate']}` twice"
        elif errs:
            ml, text = errs[0]
            broken = f"error at line {ml}: {collapse(text)[:200]}"
        elif not info or "missing" in info or "head" not in info:
            # review a3, M2: not "did not parse"; with no error inside the block, the check did not run
            broken = "the turned definition is missing, with no error inside the block (the check did not run)"
        elif any(a not in AXIOMS for a in axs):
            broken = f"axioms [{', '.join(axs)}]"
        b.broken = broken
        # what Lean reported, for a listing entry's fifth field (review (a), finding 2)
        b.fingerprint = hashlib.sha256(
            f"head={info.get('head')};lams={info.get('lams')};props={info.get('props')};"
            f"axioms={info.get('axioms')}".encode("utf-8")).hexdigest()
        if b.name is None:
            b.verdict = "NO-DOCSTRING"
            b.detail = "a witness-form block without a witness docstring"
            if broken:
                b.detail += f"; it is also broken: {broken}"
            continue
        if broken:
            b.verdict, b.detail = "BROKEN", broken
        else:
            head = info["head"]
            res = [r for r in info.get("resolved", "").split(",") if r]
            cands = [c for c in info.get("candidates", "").split(",") if c]
            target = None
            why = ""
            if len(res) == 1:
                target = res[0]
            elif len(res) > 1:
                why = f"`{b.name}` resolves to {len(res)} constants: {', '.join(res)}"
            elif len(cands) == 1:
                target = cands[0]
            else:
                why = f"`{b.name}` resolves to nothing, and {len(cands)} N.NAME exist: {', '.join(cands)}"
            lams = info.get("lams", "0")
            if target is None or head != target:
                b.verdict = "WRONG-NAME"
                b.detail = f"head {head}, docstring names {b.name}" + (f" ({why})" if why else f" = {target}")
            elif info.get("headmod") != "local":
                # extension E2 (review (a), finding 9): a witness applies a theorem of its own module
                b.verdict = "WRONG-NAME"
                b.detail = f"head {head} is not a constant of this module (extension E2)"
            else:
                k, _, types = info.get("props", "0 ").partition(" ")
                if k.isdigit() and int(k) > 0:
                    b.verdict = "PARTIAL"
                    b.detail = f"{k} proposition binder(s) left: {types[:200]}"
                elif lams.isdigit() and int(lams) > 0:
                    # extension E1 (review (a), finding 1): the value is a function, not the
                    # theorem applied to concrete arguments
                    b.verdict = "PARTIAL"
                    b.detail = f"the value is a function of {lams} argument(s) (extension E1)"
                else:
                    # ruling 3, section 2: the head applied to fewer arguments than its binders
                    # before the colon (k from the check, n from the listing driver)
                    ks = info.get("nargs", "")
                    n = binder_count(info.get("headid", ""), lst) if lst is not None else None
                    if not ks.isdigit() or n is None:
                        if lst is None or not lst.failed:
                            copy_errors.append(f"no binder count for {head} (the block at line {b.line})")
                        # review a3, M1: no count is no verdict of OK
                        b.verdict = "BROKEN"
                        b.detail = (f"no binder count for {head}" + (" (the listing driver failed)"
                                    if lst is not None and lst.failed else "") + f"; k={ks or '?'} n=?")
                    elif int(ks) < n:
                        b.verdict = "PARTIAL"
                        b.detail = ("the bare theorem, applied to nothing (ruling 2, section 3 item 4)"
                                    if int(ks) == 0 else
                                    f"the theorem, applied to {ks} of its {n} binders before the colon "
                                    "(ruling 3, section 2)")
                    else:
                        b.verdict, b.detail = "OK", f"{b.name} = {head}; k={ks} n={n}"
    return copy_errors, range_mm, doc_mm, notes


def block_hash(mod, b):
    start = mod.starts[b.first - 1]
    if getattr(b, "lean_end", None) and b.lean_end[0] is not None:
        el, ec = b.lean_end
        if el == b.line:
            ec -= len(f"noncomputable def {TURNED}L{b.line}") - len("example")
        end = mod.starts[el - 1] + ec
    else:
        end = mod.starts[b.last_code - 1] + len(mod.lines[b.last_code - 1])
    return hashlib.sha256(mod.text[start:end].encode("utf-8")).hexdigest()


# ---------------------------------------------------------------------------------------------

def lean_options(repo):
    if os.path.exists(os.path.join(repo, "lakefile.lean")):
        raise SystemExit("setup: lakefile.lean is not read by this gate (it reads lakefile.toml)")
    path = os.path.join(repo, "lakefile.toml")
    if not os.path.exists(path):
        raise SystemExit("setup: no lakefile.toml")
    with open(path, "rb") as f:
        lt = tomllib.load(f)
    flat = []

    def walk(prefix, d):
        for k, v in d.items():
            key = f"{prefix}.{k}" if prefix else k
            if isinstance(v, dict):
                walk(key, v)
            else:
                val = ("true" if v else "false") if isinstance(v, bool) else str(v)
                flat.append(f"-D{key}={val}")
    walk("", lt.get("leanOptions", {}))
    return flat


def load_listing(path):
    entries = []
    if not os.path.exists(path):
        return entries
    with open(path, encoding="utf-8") as f:
        for i, ln in enumerate(f, 1):
            ln = ln.rstrip("\n")
            if not ln.strip() or ln.startswith("#"):
                continue
            parts = ln.split("\t")
            if len(parts) != 5:
                raise SystemExit(f"setup: {path}:{i}: an entry has five tab-separated fields "
                                 "(module, block sha256, verdict, Lean fingerprint, reason)")
            mod = parts[0][len("ClassicalLean/"):] if parts[0].startswith("ClassicalLean/") else parts[0]
            entries.append({"line": i, "module": mod, "hash": parts[1], "verdict": parts[2],
                            "fingerprint": parts[3], "reason": parts[4]})
    return entries


def main(argv):
    args = list(argv)
    root = None
    keep = None
    mods = []
    while args:
        a = args.pop(0)
        if a == "--root":
            root = args.pop(0)
        elif a == "--keep":
            keep = args.pop(0)
        elif a == "--driver-timeout":
            # for the tests only (fixture M1): it can only make the driver fail sooner
            v = args.pop(0)
            if not v.isdigit() or not 0 < int(v) <= TIMEOUT:
                print(f"setup: --driver-timeout takes 1 to {TIMEOUT} seconds")
                return 2
            DRIVER_TIMEOUT[0] = int(v)
        elif a.startswith("-"):
            print(f"setup: unknown option {a}")
            return 2
        else:
            mods.append(a)
    repo = os.getcwd()
    base = os.path.abspath(root) if root else repo
    src = os.path.join(base, "ClassicalLean")
    if shutil.which("lake") is None:
        print("setup: no `lake` on the path")
        return 2
    try:
        opts = lean_options(repo)
        listing = load_listing(os.path.join(base, "tools", "witness_reviewed.txt"))
    except SystemExit as e:
        print(e)
        return 2
    explicit = bool(mods)
    if not mods:
        mods = sorted(os.path.relpath(os.path.join(d, f), src).replace(os.sep, "/")
                      for d, _, fs in os.walk(src) for f in fs if f.endswith(".lean"))
    t0 = time.time()
    # SIGTERM as an exception, so a Lean run under way is stopped first (review (ac2), F3)
    def _term(signum, frame):
        raise SystemExit(128 + signum)
    signal.signal(signal.SIGTERM, _term)
    nonce = secrets.token_hex(8)
    print("OPTIONS " + " ".join(opts))
    workdir = keep if keep else tempfile.mkdtemp(prefix="witness-gate-")
    os.makedirs(workdir, exist_ok=True)
    lines_out = []
    counts = {}
    apart = {"COPY-ERROR": 0, "STALE-LISTING": 0, "RANGE-MISMATCH": 0, "DOC-MISMATCH": 0}
    lean_count = gate_count = 0     # `example` keywords: Lean's listing / the gate's, same modules
    verdict_lines = 0
    keywords = pattern = nonstart = 0
    elaborated = 0
    block_hashes = {}
    all_blocks = []
    try:
        for rel in mods:
            with open(os.path.join(src, rel), encoding="utf-8") as f:
                mod = Module(rel, f.read())
            if TURNED in mod.text:
                lines_out.append((rel, 0, f"COPY-ERROR {mod_path(rel)}: the text `{TURNED}` occurs in "
                                  "the module, so the copy's names could clash; refused"))
                apart["COPY-ERROR"] += 1
                continue
            if mod.problems:
                pos, what = mod.problems[0]
                lines_out.append((rel, 0, f"COPY-ERROR {mod_path(rel)}: the lexer found {what} at "
                                  f"line {mod.line_of(min(pos, len(mod.text) - 1))}; a module that "
                                  "builds has none, so the gate's reading cannot be trusted; refused"))
                apart["COPY-ERROR"] += 1
                continue
            mod.read()
            keywords += mod.keywords
            pattern += mod.pattern_lines
            nonstart += mod.nonstart_keywords
            for b in mod.blocks:
                classify_text(mod, b)
            # Lean decides where the blocks are (ruling 2, section 3 item 1): every module read
            lst = run_driver(mod, os.path.join(src, rel), repo, opts)
            lean_count += lst.count
            gate_count += mod.keywords
            for c in lst.errors:
                lines_out.append((rel, 0, f"COPY-ERROR {mod_path(rel)}: {c}"))
                apart["COPY-ERROR"] += 1
            if lst.refusals:
                # ruling 4: the module may run its own code while it elaborates; the driver stopped
                # before that command, and no copy is elaborated, so the copy decides nothing
                lines_out.append((rel, 0, f"COPY-ERROR {mod_path(rel)}: the listing driver refused the "
                                  f"module (ruling 4): {'; '.join(lst.refusals)[:600]}"))
                apart["COPY-ERROR"] += 1
                for b in mod.blocks:
                    if b.form == "witness":
                        b.verdict, b.broken = "BROKEN", "not checked: the listing driver refused the module"
                        b.detail = b.broken + " (ruling 4), so no copy was elaborated"
            elif any(b.form == "witness" for b in mod.blocks):
                elaborated += 1
                rc, msgs, wg, cmap, raw = run_copy(mod, repo, opts, workdir, nonce)
                ce, rm, dm, notes = decide(mod, rc, msgs, wg, cmap, lst)
                for c in ce:
                    lines_out.append((rel, 0, f"COPY-ERROR {mod_path(rel)}: {c}"))
                    apart["COPY-ERROR"] += 1
                for ln, why in rm:
                    lines_out.append((rel, ln, f"RANGE-MISMATCH {mod_path(rel)}:{ln}: {why}"))
                    apart["RANGE-MISMATCH"] += 1
                for ln, why in dm:
                    lines_out.append((rel, ln, f"DOC-MISMATCH {mod_path(rel)}:{ln}: {why}"))
                    apart["DOC-MISMATCH"] += 1
                for ln, why in notes:
                    lines_out.append((rel, ln or 0, f"NOTE {mod_path(rel)}:{ln}: warning: {why}"))
                for b in mod.blocks:
                    if b.form == "witness":
                        b.hash = block_hash(mod, b)
                        block_hashes.setdefault((rel, b.hash), []).append(b)
            for b in mod.blocks:
                b.rel = rel
            for ln in mod.not_a_block:
                lines_out.append((rel, ln, f"NOT-A-BLOCK {mod_path(rel)}:{ln}"))
                counts["NOT-A-BLOCK"] = counts.get("NOT-A-BLOCK", 0) + 1
                verdict_lines += 1
            for ln, why in mod.unread:
                lines_out.append((rel, ln, f"UNREAD {mod_path(rel)}:{ln}: {why}"))
                counts["UNREAD"] = counts.get("UNREAD", 0) + 1
                verdict_lines += 1
            all_blocks.extend(mod.blocks)
        read = set(mods)
        whole = not explicit
        seen = set()
        listed = {}

        def stale(e, ln, why):
            lines_out.append((e["module"], ln, f"STALE-LISTING line {e['line']}: {why}"))
            apart["STALE-LISTING"] += 1

        for e in listing:
            ok_verdict = (e["verdict"] in LISTABLE) or (
                e["reason"].startswith(FAULT_PREFIX) and e["verdict"] in FAULT_LISTABLE)
            if e["module"] not in read:
                # on a whole-library run, an entry for a module that does not exist is stale
                # (review (a), finding 6); a run on named modules skips the others' entries
                if whole:
                    stale(e, 0, f"its module {mod_path(e['module'])} does not exist")
                continue
            if not ok_verdict:
                stale(e, 0, f"refused verdict {e['verdict']} (only NO-DOCSTRING and PARTIAL, or a "
                      "FAULT entry with OK, PARTIAL, WRONG-NAME or NO-DOCSTRING)")
                continue
            key = (e["module"], e["hash"])
            if key in seen:
                stale(e, 0, "a second entry for the same block")
                continue
            seen.add(key)
            hits = block_hashes.get(key)
            if not hits:
                stale(e, 0, "its hash matches no block of the module")
                continue
            for b in hits:
                if b.broken:
                    stale(e, b.line, f"the block at {mod_path(b.rel)}:{b.line} is broken ({b.broken}); "
                          "a broken block may never be listed")
                elif b.verdict != e["verdict"]:
                    stale(e, b.line, f"the block at {mod_path(b.rel)}:{b.line} now gets {b.verdict}, "
                          f"the entry says {e['verdict']}")
                elif b.fingerprint != e["fingerprint"]:
                    stale(e, b.line, f"what Lean reports of the block at {mod_path(b.rel)}:{b.line} "
                          f"changed (fingerprint {b.fingerprint}, the entry says {e['fingerprint']})")
                else:
                    listed[id(b)] = e
        for b in all_blocks:
            v = b.verdict
            e = listed.get(id(b))
            if e is not None:
                v2 = "LISTED-FAULT" if e["reason"].startswith(FAULT_PREFIX) else "LISTED"
                text = f"{v2} {mod_path(b.rel)}:{b.line} (would be {v}): {e['reason']}"
                v = v2
            else:
                text = f"{v} {mod_path(b.rel)}:{b.line}" + (f" {b.detail}" if b.detail else "")
            if b.form == "witness" and getattr(b, "hash", None):
                # what a listing entry for this block would hold
                text += f" [block {b.hash} lean {getattr(b, 'fingerprint', '-')}]"
            lines_out.append((b.rel, b.line, text))
            counts[v] = counts.get(v, 0) + 1
            verdict_lines += 1
    finally:
        if not keep:
            shutil.rmtree(workdir, ignore_errors=True)
    for _, _, text in sorted(lines_out, key=lambda t: (t[0], t[1])):
        print(text)
    passing = {"OK", "TYPED", "NOT-A-BLOCK", "LISTED", "LISTED-FAULT"}
    failed = any(v not in passing for v in counts) or any(apart.values())
    nonnab = verdict_lines - counts.get("NOT-A-BLOCK", 0)
    lines_ok = verdict_lines == pattern + nonstart
    kw_ok = keywords == nonnab
    lean_ok = lean_count == gate_count
    failed = failed or not lines_ok or not kw_ok or not lean_ok
    order = ["OK", "PARTIAL", "WRONG-NAME", "BROKEN", "NO-DOCSTRING", "TYPED-CLAIM", "TYPED",
             "NOT-A-BLOCK", "UNREAD", "LISTED"]
    summary = " ".join(f"{v}={counts.get(v, 0)}" for v in order)
    extra = " ".join(f"{k.lower()}={v}" for k, v in apart.items())
    print(f"WITNESSGATE {'FAIL' if failed else 'PASS'} modules={len(mods)} elaborated={elaborated} "
          f"{summary} LISTED-FAULT={counts.get('LISTED-FAULT', 0)} {extra} "
          f"lines={verdict_lines}/{pattern + nonstart} keywords={keywords}/{nonnab} "
          f"lean={lean_count}/{gate_count} time={time.time() - t0:.1f}s")
    return 1 if failed else 0


def mod_path(rel):
    return f"ClassicalLean/{rel}"


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
