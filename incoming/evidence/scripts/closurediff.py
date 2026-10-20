"""CLOUD-MATH-2, rule 27: modules of the new modules' import closure that the base closure lacks.
usage: python3 -I closurediff.py BASE.out NEW.out    (each holds `MOD <module>` lines)
Prints each such module, then `NEW-NOT-IN-BASE <n>`."""
import re, sys
def mods(p):
    return {m.group(1) for m in re.finditer(r'MOD (\S+)', open(p, encoding='utf-8').read())}
b, n = mods(sys.argv[1]), mods(sys.argv[2])
d = sorted(n - b)
for m in d:
    print(m)
print(f'BASE {len(b)} NEW {len(n)} NEW-NOT-IN-BASE {len(d)}')
