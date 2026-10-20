"""CLOUD-MATH-2, rule 26: build a review brief from HANDOFF.md and a task file.

usage: python3 -I mkbrief.py HANDOFF.md TASK.md OUT.md
OUT.md = TASK.md, then a section quoting verbatim, from HANDOFF.md section 6's generated block, the
rules the order's table names for every brief (14, 17, 18, 19, 20, 22, 23, 26, 31) and rule 12 (the
reviewer's own working rule), each rule line copied whole, uncut. Refuses (exit 3) when a rule is
not found exactly once, or when a line of OUT.md holds a clock time with no ISO date on it (the
check of incoming/tools/briefcheck.py, copied inline, as rule 36 asks of a brief builder), and
writes nothing then. Refuses (exit 2) without its three arguments.
"""
import re, sys

if len(sys.argv) != 4:
    sys.exit(2)
handoff, task, out = sys.argv[1:]
text = open(handoff, encoding='utf-8').read()
block = text.split('<!-- rules:begin')[1].split('<!-- rules:end -->')[0]
RULES = [12, 14, 17, 18, 19, 20, 22, 23, 26, 31]
quoted = []
for n in RULES:
    hits = [l for l in block.split('\n') if l.startswith(f'  {n}. ')]
    if len(hits) != 1:
        print(f'rule {n}: found {len(hits)} times'); sys.exit(3)
    quoted.append(hits[0].strip())
body = open(task, encoding='utf-8').read().rstrip('\n')
body += ('\n\n## The rules you are checked against (quoted verbatim from `HANDOFF.md` section 6, '
         'generated block; uncut)\n\n' + '\n'.join(quoted) + '\n')
TIME = re.compile(r'(?<![\d:])\d{1,2}:\d{2}(?!\d)')
DATE = re.compile(r'\d{4}-\d{2}-\d{2}')
bad = [(i, l) for i, l in enumerate(body.split('\n'), 1) if TIME.search(l) and not DATE.search(l)]
if bad:
    for i, l in bad:
        print(f'REFUSED line {i}: {l}')
    sys.exit(3)
open(out, 'w', encoding='utf-8').write(body)
print(f'{out}: {len(body.splitlines())} lines, rules {RULES} quoted')
