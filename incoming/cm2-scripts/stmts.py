"""CLOUD-MATH-2 report: print each named declaration's statement as it stands in a module file,
from its keyword line to the `:=` that ends the statement (a definition's body is printed whole,
up to the next blank line). usage: python3 -I stmts.py MODULE.lean NAME..."""
import re, sys
lines = open(sys.argv[1], encoding='utf-8').read().split('\n')
for name in sys.argv[2:]:
    pat = re.compile(r'^(noncomputable def|theorem|def) ' + re.escape(name) + r'\b')
    hits = [i for i, l in enumerate(lines) if pat.match(l)]
    if len(hits) != 1:
        print(f'-- {name}: found {len(hits)} times'); continue
    i = hits[0]; out = []
    is_def = 'def ' in lines[i].split(name)[0]
    while i < len(lines):
        l = lines[i]
        if is_def:
            if not l.strip():
                break
            out.append(l)
        else:
            if ':= by' in l or l.rstrip().endswith(':='):
                out.append(re.sub(r'\s*:=( by)?\s*$', '', l)); break
            out.append(l)
        i += 1
    print('\n'.join(out)); print()
