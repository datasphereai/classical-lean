"""Order LEAN-29, item 95: the four dropped-hypothesis cells at p = 1/3, checked exactly.

usage: python3 -I checks95.py
Standard library only, exact fractions. Predictions, written before the first run:
  95.mine.U        lucasU 3 2 (r = 2): U 0..3 = 0, 1, 3, 7; U 2 / U 3 = 3/7, U 1 / U 2 = 1/3.
  95.mine.copy     every step equal to the first, up with chance 1/3, (a, b) = (1, 2): the chance
                   of the event {exists n, walk n = a and walk k > -b for all k <= n} is 1/3,
                   against the formula's 3/7 (the cell of rows hX and hind; which hypothesis the
                   model breaks is by hand: the filtration that knows nothing breaks only hX, the
                   steps' own filtration breaks only hind).
  95.mine.hpm      independent steps +1 with chance 1/3 and -2 otherwise, (a, b) = (1, 2): 1/3,
                   against 3/7.
  95.mine.hp       independent fair steps, p = 1/3 stated, (a, b) = (1, 1): 1/2, against
                   U 1 / U 2 = 1/3.
Exit code 0 only if every line is a HIT.
"""
from fractions import Fraction as F
import itertools, sys

def lucasU(P, Q, n):
    u0, u1 = F(0), F(1)
    if n == 0:
        return u0
    for _ in range(n - 1):
        u0, u1 = u1, P * u1 - Q * u0
    return u1

def event(path, a, b):
    """{exists n, walk n = a and for all k <= n, -b < walk k} on a finite path of walk values"""
    for n, w in enumerate(path):
        if w <= -b:
            return False
        if w == a:
            return True
    return False

def chance_iid(steps, a, b, horizon):
    """exact chance of the event for independent steps with law `steps` (value -> chance), by
    dynamic programming over the walk's value up to `horizon` steps; mass still alive at the end
    is returned separately"""
    alive = {0: F(1)}
    hit = F(0)
    if 0 == a and 0 > -b:
        return F(1), F(0)
    if 0 <= -b:
        return F(0), F(0)
    for _ in range(horizon):
        nxt = {}
        for w, m in alive.items():
            for s, c in steps.items():
                v = w + s
                if v <= -b:
                    continue
                if v == a:
                    hit += m * c
                    continue
                nxt[v] = nxt.get(v, F(0)) + m * c
        alive = nxt
    return hit, sum(alive.values(), F(0))

res = []
def check(label, ok, msg):
    res.append(ok)
    print(('HIT ' if ok else 'MISS'), label + ':', msg)

U = [lucasU(F(3), F(2), n) for n in range(4)]
check('95.mine.U', U == [0, 1, 3, 7] and U[2] / U[3] == F(3, 7) and U[1] / U[2] == F(1, 3),
      f'lucasU 3 2: {U}, U2/U3 = {U[2] / U[3]}, U1/U2 = {U[1] / U[2]}')

# every step equal to the first: two paths, up with chance 1/3
p = F(1, 3)
c = sum((pr for x0, pr in ((1, p), (-1, 1 - p))
         if event([k * x0 for k in range(60)], 1, 2)), F(0))
check('95.mine.copy', c == F(1, 3) and c != U[2] / U[3], f'chance {c} against {U[2] / U[3]}')

h, alive = chance_iid({1: F(1, 3), -2: F(2, 3)}, 1, 2, 60)
check('95.mine.hpm', h == F(1, 3) and alive == 0 and h != U[2] / U[3],
      f'chance {h} (mass alive after 60 steps {alive}) against {U[2] / U[3]}')

# fair steps: the chance of 1 before -1 is exactly 1/2 (the walk from 0 moves to 1 or -1 at once)
h, alive = chance_iid({1: F(1, 2), -1: F(1, 2)}, 1, 1, 60)
check('95.mine.hp', h == F(1, 2) and alive == 0 and h != U[1] / U[2],
      f'chance {h} (mass alive {alive}) against {U[1] / U[2]}')

print(f'== {sum(res)} of {len(res)} checks hit')
sys.exit(0 if all(res) else 1)
