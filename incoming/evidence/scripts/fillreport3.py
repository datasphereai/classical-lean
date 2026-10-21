"""CLOUD-MATH-3 (adapted from CLOUD-MATH-2's fillreport.py): fill a report template's {{KEY}}
placeholders with saved outputs. usage: python3 -I fillreport3.py TEMPLATE OUT KEY=FILE...
Each {{KEY}} must occur exactly once and each KEY have a file; refuses (exit 3) otherwise, and
writes nothing then; exit 2 without its arguments (rule 28)."""
import re, sys
if len(sys.argv) < 4:
    sys.exit(2)
t = open(sys.argv[1], encoding='utf-8').read()
vals = dict(a.split('=', 1) for a in sys.argv[3:])
keys = set(re.findall(r'\{\{([A-Z_]+)\}\}', t))
if keys != set(vals):
    print('placeholders', sorted(keys), 'values', sorted(vals)); sys.exit(3)
for k, f in vals.items():
    if t.count('{{' + k + '}}') != 1:
        print(f'{k} not once'); sys.exit(3)
    t = t.replace('{{' + k + '}}', open(f, encoding='utf-8').read().rstrip('\n'))
open(sys.argv[2], 'w', encoding='utf-8').write(t)
print(sys.argv[2], 'filled:', ', '.join(sorted(vals)))
