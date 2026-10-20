"""CLOUD-MATH-2: fill the report template from saved outputs. usage: fillreport.py TEMPLATE OUT
Applies three wording fixes (each must occur once), then replaces {{STATEMENTS}}, {{CITECHECK}},
{{BIGFILES}}, {{MISSES}}, {{NOTRUN}} by the files' text (NOTRUN: the evidence.log lines with
rc=NOT RUN, before the notrun-count run)."""
import os, sys
E = os.environ['EVD']
t = open(sys.argv[1], encoding='utf-8').read()
fixes = [
 ('MINOR and in a docstring. End check 1', 'MINOR and in a docstring (six reviews, five confirming passes). End check 1'),
 ('`python3 -I incoming/tools/citecheck.py evidence.log REPO 4d99afd`', '`$T/ev.sh citecheck "OK for every commit" python3 -I $T/citecheck.py $EVD/evidence.log $REPO 4d99afd`'),
 ('every fix was in docstrings only, each re-elaborated and\nrebuilt (0 warnings) before its confirming pass.', 'every fix was in docstrings only, each re-elaborated (and, for a\nmodule, rebuilt with 0 warnings) before its confirming pass.'),
]
for a, b in fixes:
    if t.count(a) != 1:
        sys.exit(f'fix not found once: {a[:50]}')
    t = t.replace(a, b)
def rd(p):
    return open(os.path.join(E, p), encoding='utf-8').read().rstrip('\n')
nr = []
for l in open(os.path.join(E, 'evidence.log'), encoding='utf-8'):
    f = l.rstrip('\n').split('\t')
    if len(f) >= 5 and f[1] == 'notrun-count':
        break
    if len(f) >= 5 and f[2] == 'rc=NOT RUN':
        nr.append('\t'.join([f[0], f[1], f[4]]))
vals = {'STATEMENTS': rd('report-stmts.out').replace('\nrc=0', '').rstrip(), 'CITECHECK': rd('citecheck.out'),
        'BIGFILES': rd('big-files.out'), 'MISSES': rd('misses.txt'), 'NOTRUN': '\n'.join(nr)}
for k, v in vals.items():
    if t.count('{{' + k + '}}') != 1:
        sys.exit(f'placeholder {k} not once')
    t = t.replace('{{' + k + '}}', v)
open(sys.argv[2], 'w', encoding='utf-8').write(t)
print(sys.argv[2], 'filled;', len(nr), 'refusals')
