"""CLOUD-MATH-3 job 1 step 1 (rule 37): write one draft's probe file from its discovery output.

usage: python3 -I mkprobes3.py OUT.lean IMPORTS CUT.lean DISC.out [EXTRA.txt]
Adapted from CLOUD-MATH-2's mkprobes.py. OUT.lean: `import` lines for IMPORTS (comma-separated;
Mathlib whole is allowed in a probe file, which is not a module), then one `#check @Name` line for
  (a) every imported constant a `FULL <ident> <name>` line of DISC.out names, except identifiers in
      SKIP (tactic or keyword spellings that also resolve to a constant the text does not use as a
      term);
  (b) for every token of CUT.lean (an identifier with `.` or `_`, as probecheck.py reads them) that
      (a), a binder, a declaration of the text or the allowlist does not clear, each `USED <name>`
      of DISC.out that clears it the way probecheck.py does (ends in `.` + a dot-prefix of the
      token): field notation such as `(hint i hi).const_mul`;
  (c) every name in EXTRA.txt (one per line, `#` comments), written by hand;
  (d) for a token on a local (`hind.mgf_sum`, cleared by its binder), each USED name ending in
      `.` + its first field (`ProbabilityTheory.iIndepFun.mgf_sum`): the lemma field notation calls.
Sorted, each once. Prints each token still not cleared as `UNCLEARED <token>` (to be resolved by
hand in EXTRA.txt) and exits 1 if there is one; refuses (exit 2) without its arguments (rule 28).
"""
import re, sys

if len(sys.argv) not in (5, 6):
    sys.exit(2)
out, imps, cut, disc = sys.argv[1:5]
extra = sys.argv[5] if len(sys.argv) == 6 else None
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import pcopy  # a copy of incoming/tools/probecheck.py (rule 12: copy, then import)

SKIP = {'calc', 'lemma', 'positivity', 'set', 'symm', 'decide', 'congr', 'by_cases', 'by_contra',
        'norm_num', 'ext', 'trivial', 'show', 'change', 'exact', 'intro', 'rfl_lemma'}
full, used = set(), set()
for line in open(disc, encoding='utf-8'):
    m = re.search(r'\bFULL (\S+) (\S+)', line)
    if m and m.group(1).split('.')[0] not in SKIP:
        full.add(m.group(2))
    m = re.search(r'\bUSED (\S+)', line)
    if m:
        used.add(m.group(1))
names = set(full)
code, toks = pcopy.tokens(cut)
A = pcopy.allow()
B = pcopy.bound_names(code)
F = pcopy.declared(code)


def cleared(t, P):
    parts = t.split('.')
    pre = {'.'.join(parts[:k]) for k in range(1, len(parts) + 1)}
    return (pre & P or any(p.endswith('.' + q) for p in P for q in pre) or parts[0] in B or t in A
            or t in F or any(f.endswith('.' + t) for f in F)
            or any('.'.join(parts[:k]) in F for k in range(1, len(parts))))


if extra:
    for line in open(extra, encoding='utf-8'):
        line = line.strip()
        if line and not line.startswith('#'):
            names.add(line)
left = []
for t in sorted({t for _, t in toks}):
    parts = t.split('.')
    if len(parts) > 1 and parts[0] in B and parts[1]:
        # field notation on a local (`hind.mgf_sum`): cleared by the binder, but the lemma it calls
        # is a Mathlib name the proof uses, so it is probed too (every USED name it can be)
        hits = sorted(u for u in used if u.endswith('.' + parts[1]))
        if hits:
            names.update(hits)
            print(f'FIELD-LOCAL {t}: ' + ' '.join(hits))
    if cleared(t, names):
        continue
    parts = t.split('.')
    pre = ['.'.join(parts[:k]) for k in range(1, len(parts) + 1)]
    hits = sorted(u for u in used if any(u.endswith('.' + q) or u == q for q in pre))
    if hits:
        names.update(hits)
        print(f'FIELD {t}: ' + ' '.join(hits))
    else:
        left.append(t)
head = [f'import {i}' for i in imps.split(',')] + ['']
body = [f'#check @{n}' for n in sorted(names)]
open(out, 'w', encoding='utf-8').write('\n'.join(head + body) + '\n')
for t in left:
    print(f'UNCLEARED {t}')
print(f'{out}: {len(body)} probes, {len(left)} uncleared')
sys.exit(1 if left else 0)
