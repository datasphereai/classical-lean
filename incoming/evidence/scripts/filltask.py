"""CLOUD-MATH-2: fill a brief template's {KEY} fields. usage: python3 -I filltask.py TEMPLATE OUT KEY=VALUE...
Refuses (exit 3) when a {KEY} of the template has no value, or a value names no {KEY} of it."""
import re, sys

if len(sys.argv) < 3:
    sys.exit(2)
t = open(sys.argv[1], encoding='utf-8').read()
vals = dict(a.split('=', 1) for a in sys.argv[3:])
keys = set(re.findall(r'\{([A-Z_]+)\}', t))
if keys - set(vals) or set(vals) - keys:
    print('missing:', sorted(keys - set(vals)), 'unused:', sorted(set(vals) - keys)); sys.exit(3)
for k, v in vals.items():
    t = t.replace('{' + k + '}', v)
open(sys.argv[2], 'w', encoding='utf-8').write(t)
print(sys.argv[2], 'filled')
