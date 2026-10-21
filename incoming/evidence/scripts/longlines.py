"""CLOUD-MATH-3: list lines longer than 100 characters (Unicode code points, as Mathlib's
`linter.style.longLine` counts them). usage: python3 -I longlines.py FILE...   exit 1 if any."""
import sys

if len(sys.argv) < 2:
    sys.exit(2)
bad = 0
for f in sys.argv[1:]:
    for i, l in enumerate(open(f, encoding='utf-8').read().split('\n'), 1):
        if len(l) > 100:
            print(f'{f}:{i}: {len(l)} characters'); bad += 1
print(f'{bad} line(s) over 100 characters')
sys.exit(1 if bad else 0)
