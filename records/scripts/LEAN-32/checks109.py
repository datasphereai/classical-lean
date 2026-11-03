"""Order LEAN-32, item 109: exact checks for the dropped-hypothesis rows (standard library only).

usage: python3 -I checks109.py      prints HIT/MISS per label; exit 0 only when every label hits.
The law p = (1/4, 3/4) on two letters {a, b}, so H(p) = log 4 - (3/4) log 3. Logs are not computed:
each claim "x != H(p)" is reduced by hand (written in each label's line) to a statement about
whole numbers, and that statement is checked exactly.

Predictions, written before the first run (2026-10-18): 4 labels, all HIT, exit 0.
  109.H         H(p) = -(1/4) log(1/4) - (3/4) log(3/4) = log 4 - (3/4) log 3: the coefficients of
                log 2 and log 3 in both forms agree (exact fractions).
  109.drop.law  true law q = (1, 0), p = (1/4, 3/4): the limit is -log p(a) = log 4; equal to H(p)
                only if (3/4) log 3 = 0, i.e. 3^3 = 1^4; checked 27 != 1.
  109.drop.indep X i = X 0 for every i: the average is -log p(X 0), log 4 or log(4/3) = log 4 - log 3;
                log 4 = H(p) only if 3^3 = 1, log(4/3) = H(p) only if 3^1 = 1 (since
                log 3 = (3/4) log 3 forces log 3 = 0); checked 27 != 1 and 3 != 1.
  109.drop.ident X 0 with law p, X i = b for every i >= 1 (constants, so independent; not
                identically distributed): the average tends to -log p(b) = log(4/3) != H(p), as above.
"""
from fractions import Fraction as Fr
import sys

hits = misses = 0


def report(label, ok, detail):
    global hits, misses
    if ok:
        hits += 1
        print(f'HIT {label} ({detail})')
    else:
        misses += 1
        print(f'MISS {label} ({detail})')


# logs as coefficient vectors over (log 2, log 3)
def log_of(num, den):
    """log(num/den) for num, den products of 2 and 3, as (c2, c3)"""
    def fac(n):
        c2 = c3 = 0
        while n % 2 == 0:
            n //= 2; c2 += 1
        while n % 3 == 0:
            n //= 3; c3 += 1
        assert n == 1
        return c2, c3
    a, b = fac(num), fac(den)
    return (Fr(a[0] - b[0]), Fr(a[1] - b[1]))


p = {'a': (1, 4), 'b': (3, 4)}
H = tuple(-sum(Fr(n, d) * log_of(n, d)[k] for n, d in p.values()) for k in (0, 1))
H_claim = (Fr(2), Fr(-3, 4))  # log 4 - (3/4) log 3
report('109.H', H == H_claim, f'H(p) = {H[0]} log 2 + {H[1]} log 3')

log4 = log_of(4, 1)
# log 4 = H iff the log 3 coefficients agree: 0 = -3/4, i.e. 3^(3/4) = 1, i.e. 3^3 = 1
report('109.drop.law', log4 != H and 3 ** 3 != 1, 'limit log 4 against H(p); 27 != 1')
log43 = log_of(4, 3)
report('109.drop.indep', log4 != H and log43 != H and 3 ** 3 != 1 and 3 != 1,
       'averages log 4 and log(4/3) against H(p); 27 != 1 and 3 != 1')
report('109.drop.ident', log43 != H, 'limit log(4/3) against H(p)')
print(f'{hits} of {hits + misses} checks hit')
sys.exit(0 if misses == 0 else 1)
