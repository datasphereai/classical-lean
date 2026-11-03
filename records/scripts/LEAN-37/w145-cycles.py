# Item 145 witness: every cycle (closed walk c0 -> c1 -> ... -> ck -> c0, length 1..7) of r on Fin 3.
from fractions import Fraction as F
from itertools import product
r = [[F(1), F(2), F(1, 2)], [F(1, 2), F(1), F(1, 2)], [F(1, 2), F(1, 2), F(1)]]
mx, eq1, n = F(0), set(), 0
for k in range(1, 8):
    for c in product(range(3), repeat=k):
        p = F(1)
        for a, b in zip(c, c[1:] + c[:1]):
            p *= r[a][b]
        n += 1; mx = max(mx, p)
        if p == 1:
            eq1.add(frozenset((a, b) for a, b in zip(c, c[1:] + c[:1]) if a != b))
print("cycles", n, "max product", mx)
print("off-diagonal edge sets of the cycles with product exactly 1:", sorted(map(sorted, eq1)))
