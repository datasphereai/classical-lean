r"""Order LEAN-31, rule 9: a clock time in a brief carries its ISO date on the same line.

usage: python3 -I briefcheck.py FILE...   (exit 0: every file passes; exit 3: some line refused)
A line is refused when it holds a time matched by (?<![\d:])\d{1,2}:\d{2}(?!\d) and no date
\d{4}-\d{2}-\d{2} anywhere on it. The same check is copied inline into mkbrief.py and
mkconfirm.py, which refuse to write a brief that fails it.
"""
import re, sys
TIME = re.compile(r'(?<![\d:])\d{1,2}:\d{2}(?!\d)')
DATE = re.compile(r'\d{4}-\d{2}-\d{2}')


def undated(text):
    return [(i, l) for i, l in enumerate(text.split('\n'), 1) if TIME.search(l) and not DATE.search(l)]


if __name__ == '__main__':
    bad = 0
    for f in sys.argv[1:]:
        u = undated(open(f, encoding='utf-8').read())
        for i, l in u:
            print(f'REFUSED {f}:{i}: {l}')
        print(f'{f}: {"PASS" if not u else "REFUSED, " + str(len(u)) + " undated line(s)"}')
        bad += bool(u)
    sys.exit(3 if bad else 0)
