"""CLOUD-MATH-3 job 1 step 1: find the full names of the constants a cut draft uses.

usage: python3 -I mkdisc3.py OUT.lean CUT.lean
Adapted from CLOUD-MATH-2's mkdiscover.py. OUT.lean is CUT.lean (the draft with the Goal list's
cuts, and its witness start if it has one) with each `example :=` turned into a
`noncomputable def disc_wN :=` (so that the constants a witness uses are in the environment), then
a `run_cmd` at its end, where the draft's own `open` lines are in force, that
  * tries to resolve every identifier of the text (comments, docstrings and string literals removed
    first, as probecheck.py does), and for a dotted identifier also each shorter dot-prefix, as a
    global constant, and prints `FULL <ident> <name>` when the longest prefix that resolves is an
    imported constant, `LOCAL <ident> <name>` when it is declared in the file, else `NONE <ident>`;
  * prints `USED <name>` for every imported constant that the type or value of a declaration of
    the file mentions (field notation such as `(hint i hi).const_mul` is resolved only there).
Nothing is probed by this file (it has no `#check` line); the probe file is written from its output
by mkprobes3.py. Refuses (exit 2) without its two arguments (rule 28).
"""
import re, sys

if len(sys.argv) != 3:
    sys.exit(2)
out_path, draft = sys.argv[1], sys.argv[2]
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from pcopy import strip, idents  # a copy of incoming/tools/probecheck.py (rule 12: copy, then import)

raw = open(draft, encoding='utf-8').read()
k = 0


def as_def(m):
    global k
    k += 1
    return f'noncomputable def disc_w{k} :='


body = re.sub(r'^example :=', as_def, raw, flags=re.M)
code = strip(raw)
names = []
for l in code.split('\n'):
    if re.match(r'^\s*(import|open|namespace|end|section)\b', l):
        continue
    for t in idents(l):
        if t not in names:
            names.append(t)


def lean_name(s):
    return '`' + '.'.join('«' + p + '»' for p in s.split('.'))


items = []
for t in names:
    parts = t.split('.')
    prefs = ['.'.join(parts[:j]) for j in range(len(parts), 0, -1)]
    items.append('    ("' + t + '", [' + ', '.join(lean_name(p) for p in prefs) + '])')
tail = ['', 'open Lean Elab Command in', 'run_cmd do', '  let env ← getEnv',
        '  let cands : List (String × List Name) := [', ',\n'.join(items), '  ]',
        '  for (s, ps) in cands do',
        '    let mut found := false',
        '    for p in ps do',
        '      unless found do',
        '        try',
        '          let n ← liftCoreM (realizeGlobalConstNoOverload (mkIdent p))',
        '          if (env.getModuleIdxFor? n).isSome then logInfo m!"FULL {s} {n}"',
        '          else logInfo m!"LOCAL {s} {n}"',
        '          found := true',
        '        catch _ => pure ()',
        '    unless found do logInfo m!"NONE {s}"',
        '  let mut used : NameSet := {}',
        '  for (_, ci) in env.constants.map₂.toList do',
        '    let cs := ci.type.getUsedConstants ++ (match ci.value? with | some v => v.getUsedConstants | none => #[])',
        '    for c in cs do',
        '      if (env.getModuleIdxFor? c).isSome then used := used.insert c',
        '  for c in used.toList do logInfo m!"USED {c}"']
open(out_path, 'w', encoding='utf-8').write(body.rstrip('\n') + '\n' + '\n'.join(tail) + '\n')
print(f'{out_path}: {len(names)} identifiers, {k} witness(es) as defs')
