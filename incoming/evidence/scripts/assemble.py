"""CLOUD-MATH-2 job 2: assemble a module from its reviewed statement file and its draft's proofs.

usage: python3 -I assemble.py STMT.lean DRAFT.lean SPEC.json OUT.lean
SPEC.json: {"ranges": [[a, b], ...], "edits": [[line, old, new], ...], "tail": "WITNESS.lean"}.
Each `edits` entry changes draft line `line` (1-based): `old` must occur in it exactly once and is
replaced by `new`; `new` = null deletes the whole line. Then the k-th line of STMT.lean that is
exactly `  sorry` (or ends a line with `:= by sorry`, `by\\n  sorry`) is replaced by the draft's lines
`ranges[k]` (inclusive), after the edits; a range `[a, b, "term"]` is a term proof, and the
statement file's `:= by` before its hole becomes `:=`. The number of ranges must equal the number of `sorry`
lines. The file named in `tail`, if any, is appended after one blank line. Prints each edit and
refuses (exit 3) on any mismatch.
"""
import json, sys

if len(sys.argv) != 5:
    sys.exit(2)
stmt, draft, spec, out = sys.argv[1:]
S = open(stmt, encoding='utf-8').read().split('\n')
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
holes = [i for i, l in enumerate(S) if l == '  sorry']
if len(holes) != len(sp['ranges']):
    print(f'{len(holes)} sorry lines, {len(sp["ranges"])} ranges'); sys.exit(3)
for i, r in reversed(list(zip(holes, sp['ranges']))):
    a, b = r[0], r[1]
    if len(r) > 2 and r[2] == 'term':
        # the draft's proof is a term: the statement file's `:= by` before the hole becomes `:=`
        if not S[i - 1].endswith(' := by'):
            print(f'term range {r}: line before the hole is {S[i - 1]!r}'); sys.exit(3)
        S[i - 1] = S[i - 1][:-len(' by')]
        print(f'stmt {i}: `:= by` -> `:=` (term proof, draft lines {a} to {b})')
    S[i:i + 1] = [D[k - 1] for k in range(a, b + 1) if k not in deleted]
text = '\n'.join(S).rstrip('\n') + '\n'
if sp.get('tail'):
    text += '\n' + open(sp['tail'], encoding='utf-8').read().rstrip('\n') + '\n'
open(out, 'w', encoding='utf-8').write(text)
print(f'{out}: {len(holes)} proofs filled')
