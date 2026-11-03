#!/usr/bin/env python3
"""Exact checks for LEAN-28 item 80b: the product form of the variance of a stationary sum.

Statement proposed (same hypotheses as `variance_sum_eq_of_stationary`: hX, hcov only):
    Var[sum X] = k * g0 * (1 + 2 * sum_{j in Ico 1 k} (1 - j/k) * (g_j / g0))
Lean conventions used: x / 0 = 0; Ico 1 k empty for k <= 1; the cast of k to R.

PREDICTIONS, written before this script first ran:
  P1  for k in 1..12 and g0 != 0 (300 random exact cases), the product form equals the
      sum form k*g0 + 2*sum (k - j) g_j exactly: 300 of 300.
  P2  k = 0 (any g): both forms are 0 under Lean's conventions: holds.
  P3  g0 = 0 with every g_j = 0 for 1 <= j < k (what a real series forces, since Var X0 = 0
      makes X0 a.e. equal to its integral, so cov(X0, Xj) = 0): both forms are 0 for k in 1..12.
  P4  g0 = 0 with some g_j != 0 (not reachable by a series): the forms DIFFER, so the identity
      alone does not give the theorem and the covariance step is needed; first failing cell in
      enumeration order is k = 2, g = (0, 1): product 0, sum 2.
  P5  dropped hX (report r80's case: X0 outside L2, X1 = Y - X0, Var Y = 1, every covariance is
      Lean's junk 0, so g = 0 meets hcov), k = 2: left side 1, product form 0: fails.
  P6  dropped hcov (X0 = X1 with Var 1, g = 0), k = 2: left side Var(2 X0) = 4, product 0: fails.
Exit code 0 only if every prediction holds.
"""
import random, sys
from fractions import Fraction as Fr

def div(a, b):
    return Fr(0) if b == 0 else Fr(a) / Fr(b)

def product_form(k, g):
    s = sum((1 - div(j, k)) * div(g[j], g[0]) for j in range(1, k))
    return Fr(k) * g[0] * (1 + 2 * s)

def sum_form(k, g):
    return Fr(k) * g[0] + 2 * sum((Fr(k) - j) * g[j] for j in range(1, k))

ok_all = True
def report(label, ok, detail):
    global ok_all
    ok_all &= bool(ok)
    print(f"{'HIT ' if ok else 'MISS'} {label}: {detail}")

random.seed(80)
n = good = 0
for _ in range(300):
    k = random.randint(1, 12)
    g = [Fr(random.randint(-9, 9), random.randint(1, 9)) for _ in range(13)]
    while g[0] == 0:
        g[0] = Fr(random.randint(-9, 9), random.randint(1, 9))
    n += 1
    good += product_form(k, g) == sum_form(k, g)
report('P1', good == 300 and n == 300, f'{good} of {n} cases equal (k in 1..12, g0 != 0)')

g = [Fr(random.randint(-9, 9), 7) for _ in range(13)]
report('P2', product_form(0, g) == 0 == sum_form(0, g), 'k = 0: both forms are 0')

p3 = all(product_form(k, [Fr(0)] * 13) == 0 == sum_form(k, [Fr(0)] * 13) for k in range(1, 13))
report('P3', p3, 'g0 = 0 and g_j = 0 for j < k: both forms 0, k in 1..12')

first = None
for k in range(1, 13):
    for j in range(1, k):
        g = [Fr(0)] * 13
        g[j] = Fr(1)
        if product_form(k, g) != sum_form(k, g):
            first = (k, j, product_form(k, g), sum_form(k, g))
            break
    if first:
        break
report('P4', first == (2, 1, Fr(0), Fr(2)), f'first cell where g0 = 0 but g_j != 0 breaks the identity: {first}')

report('P5', Fr(1) != product_form(2, [Fr(0)] * 13) == 0, 'dropped hX: left side 1, product form 0')
report('P6', Fr(4) != product_form(2, [Fr(0)] * 13) == 0, 'dropped hcov: left side 4, product form 0')

print('ALL OK' if ok_all else 'SOME MISS')
sys.exit(0 if ok_all else 1)
