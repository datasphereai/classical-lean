"""CLOUD-MATH-3, rule 26: build a review brief from HANDOFF.md, the order's copy and a task file
(adapted from CLOUD-MATH-2's mkbrief.py).

usage: python3 -I mkbrief3.py HANDOFF.md ORDER.md TASK.md OUT.md
OUT.md = TASK.md, then
  * the order's `## Goal` section (its item table, the plan rows, and the changes it asks of each
    draft), copied verbatim from ORDER.md, from `## Goal` to the next `## ` heading;
  * the order's own rules 1, 2, 4 and 7 (statements, namespaces and imports, witnesses, reviews),
    each paragraph copied whole from ORDER.md's `## Rules of this order`;
  * the rules the order's table names for every brief (14, 17, 18, 19, 20, 22, 23, 26, 31) and
    rule 12 (the reviewer's own working rule), each line copied whole, uncut, from HANDOFF.md
    section 6's generated block.
Refuses (exit 3) when a section or rule is not found exactly once, or when a line of OUT.md holds a
clock time with no ISO date on it (the check of incoming/tools/briefcheck.py, copied inline, as
rule 36 asks of a brief builder), and writes nothing then. Refuses (exit 2) without its four
arguments (rule 28).
"""
import re, sys

if len(sys.argv) != 5:
    sys.exit(2)
handoff, order, task, out = sys.argv[1:]


def fail(msg):
    print(msg); sys.exit(3)


text = open(handoff, encoding='utf-8').read()
block = text.split('<!-- rules:begin')[1].split('<!-- rules:end -->')[0]
RULES = [12, 14, 17, 18, 19, 20, 22, 23, 26, 31]
quoted = []
for n in RULES:
    hits = [l for l in block.split('\n') if l.startswith(f'  {n}. ')]
    if len(hits) != 1:
        fail(f'rule {n}: found {len(hits)} times')
    quoted.append(hits[0].strip())
o = open(order, encoding='utf-8').read()
g = re.findall(r'^## Goal\n.*?(?=^## )', o, re.S | re.M)
if len(g) != 1:
    fail(f'Goal section found {len(g)} times')
r = re.findall(r'^## Rules of this order\n.*?(?=^## )', o, re.S | re.M)
if len(r) != 1:
    fail(f'rules section found {len(r)} times')
orules = []
for n in (1, 2, 4, 7):
    hits = [l for l in r[0].split('\n') if l.startswith(f'{n}. **')]
    if len(hits) != 1:
        fail(f'order rule {n}: found {len(hits)} times')
    orules.append(hits[0])
body = open(task, encoding='utf-8').read().rstrip('\n')
body += ('\n\n## The order\'s Goal section (quoted verbatim from the order\'s copy, '
         '`records/orders/20261021T002100Z__claude-ai__order-cloudmath3-subgradient-efron-stein-'
         'bernstein-order-statistics-bsc.md`; uncut)\n\n' + g[0].split('\n', 1)[1].strip('\n') + '\n')
body += ('\n## The order\'s rules 1, 2, 4 and 7 (quoted verbatim from the same file; each paragraph '
         'uncut)\n\n' + '\n'.join(orules) + '\n')
body += ('\n## The rules you are checked against (quoted verbatim from `HANDOFF.md` section 6, '
         'generated block; uncut)\n\n' + '\n'.join(quoted) + '\n')
TIME = re.compile(r'(?<![\d:])\d{1,2}:\d{2}(?!\d)')
DATE = re.compile(r'\d{4}-\d{2}-\d{2}')
bad = [(i, l) for i, l in enumerate(body.split('\n'), 1) if TIME.search(l) and not DATE.search(l)]
if bad:
    for i, l in bad:
        print(f'REFUSED line {i}: {l}')
    sys.exit(3)
open(out, 'w', encoding='utf-8').write(body)
print(f'{out}: {len(body.splitlines())} lines; Goal section, order rules 1, 2, 4, 7 and HANDOFF '
      f'rules {RULES} quoted')
