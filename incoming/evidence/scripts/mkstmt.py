"""CLOUD-MATH-3 job 1 step 2: write a statement file from a draft (the inverse of assemble.py).

usage: python3 -I mkstmt.py DRAFT.lean SPEC.json OUT.lean
SPEC.json: {"head": FILE, "keep": [a, b], "drop": [line, ...], "replace": [[a, b, FILE], ...],
            "edits": [[line, old, new], ...], "proofs": [[a, b] or [a, b, "term"], ...],
            "foot": FILE}
OUT.lean = the text of `head` (licence header, imports, module docstring, `open` lines, the
`namespace` line), then draft lines a..b of `keep`, where
  * each `edits` entry first changes its draft line (`old` must occur in it exactly once);
  * a line in `drop` is left out;
  * a `replace` range [a, b] becomes the text of its FILE (a docstring written for the module);
  * a `proofs` range [a, b] (a theorem's or lemma's proof, as assemble.py fills it back) becomes
    the one line `  sorry`; for a term proof ([a, b, "term"]) the line before must end with ` :=`,
    which becomes ` := by`;
then the text of `foot` (the `end` line). Every other line is the draft's, verbatim, so every
statement and every `def` body is the draft's own text. Prints what it did; refuses (exit 3) on
any mismatch (an overlapping range, an edit or a `:=` not found) and writes nothing then; refuses
(exit 2) without its three arguments (rule 28).
"""
import json, sys

if len(sys.argv) != 4:
    sys.exit(2)
draft, spec, out = sys.argv[1:]
D = open(draft, encoding='utf-8').read().split('\n')
sp = json.load(open(spec, encoding='utf-8'))


def fail(msg):
    print(msg); sys.exit(3)


for ln, old, new in sp.get('edits', []):
    if D[ln - 1].count(old) != 1:
        fail(f'edit at {ln}: {old!r} occurs {D[ln - 1].count(old)} times in {D[ln - 1]!r}')
    D[ln - 1] = D[ln - 1].replace(old, new)
    print(f'draft {ln}: {old!r} -> {new!r}')
action = {}
for a, b, f in sp.get('replace', []):
    for k in range(a, b + 1):
        if k in action:
            fail(f'line {k} in two ranges')
        action[k] = ('skip',)
    action[a] = ('replace', open(f, encoding='utf-8').read().rstrip('\n'))
for r in sp.get('proofs', []):
    a, b = r[0], r[1]
    for k in range(a, b + 1):
        if k in action:
            fail(f'line {k} in two ranges')
        action[k] = ('skip',)
    action[a] = ('sorry', len(r) > 2 and r[2] == 'term')
for k in sp.get('drop', []):
    if k in action:
        fail(f'line {k} dropped and in a range')
    action[k] = ('skip',)
outl = open(sp['head'], encoding='utf-8').read().rstrip('\n').split('\n') + ['']  # one blank line after the head
a, b = sp['keep']
nsorry = 0
for k in range(a, b + 1):
    act = action.get(k)
    if act is None:
        outl.append(D[k - 1])
    elif act[0] == 'replace':
        outl.extend(act[1].split('\n'))
    elif act[0] == 'sorry':
        if act[1]:
            if not outl[-1].endswith(' :='):
                fail(f'term proof at {k}: line before is {outl[-1]!r}')
            outl[-1] += ' by'
        outl.append('  sorry'); nsorry += 1
print(f'{len(sp.get("drop", []))} lines dropped, {len(sp.get("replace", []))} docstrings replaced, '
      f'{nsorry} proofs as sorry')
outl.extend(open(sp['foot'], encoding='utf-8').read().rstrip('\n').split('\n'))
open(out, 'w', encoding='utf-8').write('\n'.join(outl).rstrip('\n') + '\n')
print(f'{out}: {len(outl)} lines')
