"""CLOUD-MATH-3 (copied from CLOUD-MATH-2), rule 22: every quote in round 68's fragment is checked against its saved source.

usage: python3 -I quotecheck.py FRAGMENT MANIFEST
MANIFEST: one quote per line, `quote<TAB>source path`; `#` lines are comments. A quote may hold
`[...]`, which marks a cut: its pieces must occur in the source in order. Whitespace runs (line
breaks included) count as one space, in the fragment, the source and the quote, so a quote wrapped
over lines in the fragment still matches. For each line it prints `OK`, or `MISQUOTE` (not in the
source) or `ABSENT` (not in the fragment). It also prints `UNLISTED` for every span in straight
double quotes in the fragment that no manifest line covers. Exit 1 when any line is not OK or any
span is unlisted, else 0.
"""
import re, sys

if len(sys.argv) != 3:
    sys.exit('usage: python3 -I quotecheck.py FRAGMENT MANIFEST')


def norm(s):
    return re.sub(r'\s+', ' ', s).strip()


def occurs(pieces, text):
    pos = 0
    for p in pieces:
        k = text.find(p, pos)
        if k < 0:
            return False
        pos = k + len(p)
    return True


frag = norm(open(sys.argv[1], encoding='utf-8').read())
bad = 0
quotes = []
for raw in open(sys.argv[2], encoding='utf-8'):
    raw = raw.rstrip('\n')
    if not raw.strip() or raw.startswith('#'):
        continue
    q, src = raw.split('\t')
    q = norm(q)
    quotes.append(q)
    pieces = [norm(p) for p in q.split('[...]') if norm(p)]
    text = norm(open(src, encoding='utf-8').read())
    if not occurs(pieces, text):
        print(f'MISQUOTE {src}: {q}'); bad += 1
    elif not occurs(pieces, frag):
        print(f'ABSENT (not in the fragment): {q}'); bad += 1
    else:
        print(f'OK {src}: {q[:90]}')
for m in re.finditer(r'"([^"]+)"', frag):
    span = norm(m.group(1))
    if not any(span in q or q in span for q in quotes):
        print(f'UNLISTED "{span[:90]}"'); bad += 1
print(f'{len(quotes)} quotes, {bad} problem(s)')
sys.exit(1 if bad else 0)
