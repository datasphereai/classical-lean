"""CLOUD-MATH-2: which module declares each constant a draft uses (for targeted imports).
usage: python3 -I mklocate.py OUT.lean IMPORTS DISC.out [EXTRA.txt]
OUT.lean imports IMPORTS (comma-separated) and prints `MODOF <name> <module>` for each full name
in the discovery output (and in EXTRA.txt, one per line), via env.getModuleIdxFor?."""
import re, sys
out, imps, disc = sys.argv[1], sys.argv[2], sys.argv[3]
extra = sys.argv[4] if len(sys.argv) > 4 else None
names = []
for line in open(disc, encoding='utf-8'):
    m = re.search(r'FULL (\S+) (\S+)', line)
    if m and m.group(2) not in names:
        names.append(m.group(2))
if extra:
    for line in open(extra, encoding='utf-8'):
        line = line.strip()
        if line and not line.startswith('#') and line not in names:
            names.append(line)
def lit(s):
    return '`' + '.'.join('«' + p + '»' for p in s.split('.'))
L = [f'import {i}' for i in imps.split(',')] + ['', 'open Lean Elab Command in', 'run_cmd do',
     '  let env ← getEnv', '  for n in [' + ', '.join(lit(n) for n in names) + '] do',
     '    match env.getModuleIdxFor? n with',
     '    | some i => logInfo m!"MODOF {n} {env.header.moduleNames[i.toNat]!}"',
     '    | none => logInfo m!"MODOF {n} (none)"']
open(out, 'w', encoding='utf-8').write('\n'.join(L) + '\n')
print(out, len(names))
