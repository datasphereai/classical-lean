"""CLOUD-MATH-2, job 1 step 1 (rule 37): write the one probe file.

usage: python3 -I mkprobes.py OUT.lean MANUAL.txt DISC.out...
OUT.lean: the imports that cover the five drafts' imports (Mathlib whole, for the probe only, and
the three library modules the drafts import), then one `#check @Name` line for every full name in
a `FULL <ident> <name>` line of the discovery outputs, except the names in EXCLUDE (tactic or
keyword spellings that happen to name a constant the drafts do not use as a term), and for every
name in MANUAL.txt (one per line, `#` comments: field-notation names and the Goal list's new
names, written by hand). Sorted, each once.
"""
import re, sys

if len(sys.argv) < 4:
    sys.exit('usage: python3 -I mkprobes.py OUT.lean MANUAL.txt DISC.out...')
out, manual, discs = sys.argv[1], sys.argv[2], sys.argv[3:]
# used in the drafts as a tactic, a keyword or a match pattern, not as this constant
EXCLUDE = {'Lean.calc', 'lemma', 'positivity', 'MonadStateOf.set', 'symm', 'Matrix.zero',
           'Decidable.decide', 'congr', 'by_cases', 'by_contra', 'norm_num', 'Finset.ext'}
names = set()
for d in discs:
    for line in open(d, encoding='utf-8'):
        m = re.search(r'FULL (\S+) (\S+)', line)
        if m and m.group(2) not in EXCLUDE:
            names.add(m.group(2))
for line in open(manual, encoding='utf-8'):
    line = line.strip()
    if line and not line.startswith('#'):
        names.add(line)
head = ['import Mathlib', 'import ClassicalLean.Statistics.GaussMarkov',
        'import ClassicalLean.Analysis.GradientDescent',
        'import ClassicalLean.InformationTheory.SourceCoding', '']
body = [f'#check @{n}' for n in sorted(names)]
open(out, 'w', encoding='utf-8').write('\n'.join(head + body) + '\n')
print(f'{out}: {len(body)} probes')
