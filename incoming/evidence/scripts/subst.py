"""CLOUD-MATH-3: copy IN to OUT with one exact substitution. usage: python3 -I subst.py IN OUT OLDFILE NEWFILE
The text of OLDFILE must occur in IN exactly once; it is replaced by the text of NEWFILE (each file's
trailing newline is dropped first). Refuses (exit 3) otherwise and writes nothing; exit 2 without
its four arguments (rule 28)."""
import sys

if len(sys.argv) != 5:
    sys.exit(2)
src, out, of, nf = sys.argv[1:]
t = open(src, encoding='utf-8').read()
old = open(of, encoding='utf-8').read().rstrip('\n')
new = open(nf, encoding='utf-8').read().rstrip('\n')
if t.count(old) != 1:
    print(f'old text occurs {t.count(old)} times in {src}'); sys.exit(3)
open(out, 'w', encoding='utf-8').write(t.replace(old, new))
print(f'{out}: 1 substitution')
