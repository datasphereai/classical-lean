"""CLOUD-MATH-3: the targeted imports for a module, from its probe file (adapted from CLOUD-MATH-2's
mklocate.py).

usage: python3 -I mkimports.py OUT.lean PROBES.lean [EXTRA.txt]
OUT.lean has PROBES.lean's import lines, then a `run_cmd` that, for every `#check @Name` of
PROBES.lean (and every name in EXTRA.txt, one per line, `#` comments), prints `MODOF <name>
<module>` (the module that declares it, `env.getModuleIdxFor?`), and then `MINIMAL <module>` for
each of those modules that no other of them imports, directly or not (read from
`env.header.moduleData`'s import lists): an import set that covers every probed name. Tactics and
instances a proof uses are not names here; the import set is then tested by elaborating the cut
draft with it. Refuses (exit 2) without its arguments (rule 28).
"""
import re, sys

if len(sys.argv) not in (3, 4):
    sys.exit(2)
out, probes = sys.argv[1], sys.argv[2]
src = open(probes, encoding='utf-8').read()
imports = [l for l in src.split('\n') if l.startswith('import ')]
names = re.findall(r'^#check @(\S+)', src, re.M)
if len(sys.argv) == 4:
    for line in open(sys.argv[3], encoding='utf-8'):
        line = line.strip()
        if line and not line.startswith('#') and line not in names:
            names.append(line)


def lit(s):
    return '`' + '.'.join('«' + p + '»' for p in s.split('.'))


L = imports + ['', 'open Lean Elab Command in', 'run_cmd do', '  let env ← getEnv',
     '  let names : List Name := [' + ', '.join(lit(n) for n in names) + ']',
     '  let mut mods : Array Name := #[]',
     '  for n in names do',
     '    match env.getModuleIdxFor? n with',
     '    | some i =>',
     '      let m := env.header.moduleNames[i.toNat]!',
     '      logInfo m!"MODOF {n} {m}"',
     '      unless mods.contains m do mods := mods.push m',
     '    | none => logInfo m!"MODOF {n} (none)"',
     '  let mut idx : Std.HashMap Name Nat := {}',
     '  for h : k in [0:env.header.moduleNames.size] do',
     '    idx := idx.insert env.header.moduleNames[k] k',
     '  -- the modules each of `mods` imports, directly or not',
     '  let mut below : Array NameSet := #[]',
     '  for m in mods do',
     '    let mut seen : NameSet := {}',
     '    let mut stack : Array Name := #[m]',
     '    while !stack.isEmpty do',
     '      let a := stack.back!',
     '      stack := stack.pop',
     '      match idx[a]? with',
     '      | some k =>',
     '        for imp in env.header.moduleData[k]!.imports do',
     '          unless seen.contains imp.module do',
     '            seen := seen.insert imp.module',
     '            stack := stack.push imp.module',
     '      | none => pure ()',
     '    below := below.push seen',
     '  for m in mods do',
     '    unless below.any (·.contains m) do logInfo m!"MINIMAL {m}"']
open(out, 'w', encoding='utf-8').write('\n'.join(L) + '\n')
print(out, len(names), 'names')
