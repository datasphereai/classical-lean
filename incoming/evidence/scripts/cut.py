"""CLOUD-MATH-3 job 1 step 1: a draft with the Goal list's cuts applied (the text "as it will land").

usage: python3 -I cut.py DRAFT.lean SPEC.json OUT.lean
SPEC.json: {"edits": [[line, old, new], ...], "tail": "WITNESS.lean" or null}, the same `edits`
format as assemble.py: each entry changes draft line `line` (1-based); `old` must occur in it
exactly once and is replaced by `new` (which may hold a newline); `new` = null deletes the whole
line, and then `old` must occur in it. The file named in `tail`, if any, is appended after the
draft. Prints each edit; refuses (exit 3) on any mismatch and writes nothing then. Refuses (exit 2)
without its three arguments (rule 28).
"""
import json, sys

if len(sys.argv) != 4:
    sys.exit(2)
draft, spec, out = sys.argv[1:]
D = open(draft, encoding='utf-8').read().split('\n')
sp = json.load(open(spec, encoding='utf-8'))
deleted = set()
for ln, old, new in sp.get('edits', []):
    line = D[ln - 1]
    if new is None:
        if old not in line:
            print(f'edit at {ln}: {old!r} not in {line!r}'); sys.exit(3)
        deleted.add(ln); print(f'draft {ln}: deleted {line.strip()!r}')
        continue
    if line.count(old) != 1:
        print(f'edit at {ln}: {old!r} occurs {line.count(old)} times in {line!r}'); sys.exit(3)
    D[ln - 1] = line.replace(old, new)
    print(f'draft {ln}: {old!r} -> {new!r}')
text = '\n'.join(l for k, l in enumerate(D, 1) if k not in deleted).rstrip('\n') + '\n'
if sp.get('tail'):
    text += open(sp['tail'], encoding='utf-8').read().rstrip('\n') + '\n'
open(out, 'w', encoding='utf-8').write(text)
print(f'{out}: {len(sp.get("edits", []))} edits')
