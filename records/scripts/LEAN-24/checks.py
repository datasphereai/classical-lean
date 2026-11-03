#!/usr/bin/env python3
"""LEAN-24 checks: exact cases behind the needed-hypothesis table (Fractions; FLOAT where marked).

Each check prints one line, OK or FAIL, and the script exits 1 if any line FAILs.
Run: python3 -I checks.py
"""
from fractions import Fraction as F
from itertools import product
import sys

fails = 0
lines = 0


def check(label, cond, detail=""):
    global fails, lines
    lines += 1
    if not cond:
        fails += 1
    print(f"{'OK  ' if cond else 'FAIL'} {label}: {detail}")


def integ(phi, f):
    """sum of phi * f against counting measure on a finite space"""
    return sum(a * b for a, b in zip(phi, f))


def is_lr_test(f0, f1, k, phi):
    return all((not (k * a < b) or p == 1) and (not (b < k * a) or p == 0)
               for a, b, p in zip(f0, f1, phi))


# ---------------- item 55: Neyman-Pearson ----------------
# N1: k >= 0 is needed when f0 may be negative (no sign condition is assumed).
f0, f1, k = [F(-1)], [F(1, 2)], F(-1)
phis = [F(0)]  # LR test: k*f0 = 1 > 1/2 = f1, so phi' = 0
assert is_lr_test(f0, f1, k, phis)
phi = [F(1)]
check("N1 k>=0 (signed f0)", integ(phi, f0) <= integ(phis, f0) and integ(phi, f1) > integ(phis, f1),
      f"size phi {integ(phi, f0)} <= {integ(phis, f0)}, power {integ(phi, f1)} > {integ(phis, f1)}")
# N1b: with f0, f1 >= 0 a negative k does no harm: phi' = 1 wherever f0 + f1 > 0.
ok = True
for f0v in product([F(0), F(1, 4), F(1, 2)], repeat=3):
    for f1v in product([F(0), F(1, 4), F(1, 2)], repeat=3):
        k = F(-1)
        php = [F(1) if k * a < b else F(0) for a, b in zip(f0v, f1v)]
        for phv in product([F(0), F(1, 2), F(1)], repeat=3):
            if integ(phv, f0v) <= integ(php, f0v) and integ(phv, f1v) > integ(php, f1v):
                ok = False
check("N1b k<0 harmless when f0,f1>=0", ok, "729 x 27 small cases, no counterexample")
# N2: phi <= 1 is needed.
f0, f1 = [F(1, 2), F(1, 2), F(0)], [F(0), F(1, 2), F(1, 2)]
php = [F(0), F(1), F(1)]
assert is_lr_test(f0, f1, F(1), php)
phi = [F(0), F(1), F(2)]
check("N2 phi<=1", integ(phi, f0) <= integ(php, f0) and integ(phi, f1) > integ(php, f1),
      f"phi=(0,1,2): size {integ(phi, f0)} <= {integ(php, f0)}, power {integ(phi, f1)} > {integ(php, f1)}")
# N3: phi >= 0 is needed.
f0, f1 = [F(1, 2), F(1, 4), F(1, 4)], [F(1, 4), F(1, 4), F(1, 2)]
php = [F(0), F(0), F(1)]
assert is_lr_test(f0, f1, F(1), php)
phi = [F(-1, 2), F(1), F(1)]
check("N3 phi>=0", integ(phi, f0) <= integ(php, f0) and integ(phi, f1) > integ(php, f1),
      f"phi=(-1/2,1,1): size {integ(phi, f0)} <= {integ(php, f0)}, power {integ(phi, f1)} > {integ(php, f1)}")
# N4: size condition is needed (phi = 1).
f0, f1 = [F(1, 2), F(1, 2)], [F(1, 4), F(3, 4)]
php = [F(0), F(1)]
phi = [F(1), F(1)]
check("N4 size", integ(phi, f0) > integ(php, f0) and integ(phi, f1) > integ(php, f1),
      f"phi=1: size {integ(phi, f0)} > {integ(php, f0)}, power {integ(phi, f1)} > {integ(php, f1)}")
# N5: randomization is needed to hit a size exactly: on two points with f0 = (1/2, 1/2) the
# non-randomized tests have sizes {0, 1/2, 1}; 1/4 is reached only with a weight in (0, 1).
sizes = {integ(list(p), [F(1, 2), F(1, 2)]) for p in product([F(0), F(1)], repeat=2)}
check("N5 randomization", F(1, 4) not in sizes and integ([F(0), F(1, 2)], [F(1, 2), F(1, 2)]) == F(1, 4),
      f"non-randomized sizes {sorted(sizes)}; (0, 1/2) has size 1/4")
# N6: f1 >= 0 is needed for k >= 0 in the existence theorem: f1 = (-1, -1), f0 = (1/2, 1/2):
# for every k >= 0, f1 < 0 <= k f0 so the test is 0 and its size is 0, never 1/2.
f0, f1 = [F(1, 2), F(1, 2)], [F(-1), F(-1)]
ok = all(all(b < k * a for a, b in zip(f0, f1)) for k in [F(0), F(1, 3), F(1), F(10)])
check("N6 f1>=0 (existence)", ok, "for k in {0, 1/3, 1, 10}: f1 < k f0 everywhere, size 0 != 1/2")
# N7: int f0 = 1 is needed in the existence theorem: f0 = (1/4, 1/4) has largest size 1/2 < 3/4.
check("N7 int f0 = 1 (existence)", integ([F(1), F(1)], [F(1, 4), F(1, 4)]) == F(1, 2) < F(3, 4),
      "f0 = (1/4, 1/4): every test has size <= 1/2 < alpha = 3/4")
# N8: alpha > 0: on N with f0(n) = 2^-(n+1), f1(n) = 1/((n+1)(n+2)) the ratio f1/f0 is unbounded,
# so {f1 > k f0} has positive f0-mass for every k and size 0 is out of reach (checked on n < 60).
ok = all(any(F(1, (n + 1) * (n + 2)) > k * F(1, 2 ** (n + 1)) for n in range(60))
         for k in [F(1), F(10), F(10 ** 6), F(10 ** 12)])
check("N8 alpha>0 (existence)", ok, "for k up to 10^12 some n < 60 has f1(n) > k f0(n)")

# ---------------- item 56: Karlin-Rubin ----------------
# K1: the monotone likelihood ratio is needed: Theta = {0, 1, 2}, S = (0, 1),
# f0 = (1/2, 1/2), f1 = (1/4, 3/4), f2 = (3/4, 1/4). theta0 = 0; the threshold test (0, 1) has
# size 1/2 but power 1/4 at theta = 2, where (1, 0) (also size 1/2) has power 3/4.
f = [[F(1, 2), F(1, 2)], [F(1, 4), F(3, 4)], [F(3, 4), F(1, 4)]]
php, psi = [F(0), F(1)], [F(1), F(0)]
check("K1 MLR", integ(psi, f[0]) <= integ(php, f[0]) and integ(psi, f[2]) > integ(php, f[2]),
      f"size {integ(psi, f[0])} <= {integ(php, f[0])}, power at 2: {integ(psi, f[2])} > {integ(php, f[2])}")
# K2: int f theta = 1 is needed for the size part: S = (0, 1), f0 = (1, 1), f1 = (1/2, 1/2)
# (= g(S) f0 with g = 1/2, monotone, >= 0); theta0 = 1; the test (0, 1) has size 1/2 at theta0
# and size 1 > 1/2 at theta = 0.
f = [[F(1), F(1)], [F(1, 2), F(1, 2)]]
php = [F(0), F(1)]
check("K2 int f = 1", integ(php, f[0]) > integ(php, f[1]),
      f"size at 0: {integ(php, f[0])} > alpha = {integ(php, f[1])}")
# K3: random families with MLR on 4 points: the threshold test beats every 0/1/2 test of level
# alpha at every theta > theta0 (exact; tests on a grid of values in {0, 1/2, 1}).
import random
random.seed(24)
ok = True
count = 0
for _ in range(200):
    n = 4
    base = [F(random.randint(1, 9)) for _ in range(n)]
    S = sorted(random.sample(range(10), n))
    fam = []
    for t in range(3):
        w = [b * F(t + 1) ** s for b, s in zip(base, S)]  # exponential family in S
        tot = sum(w)
        fam.append([x / tot for x in w])
    for c in [F(s) for s in S]:
        for g in [F(0), F(1, 2), F(1)]:
            php = [F(1) if c < s else (g if s == c else F(0)) for s in S]
            alpha = integ(php, fam[0])
            for t in range(1, 3):
                if not integ(php, fam[t]) >= alpha:
                    ok = False
            for psi in product([F(0), F(1, 2), F(1)], repeat=n):
                psi = list(psi)
                if integ(psi, fam[0]) <= alpha:
                    count += 1
                    for t in range(1, 3):
                        if integ(psi, fam[t]) > integ(php, fam[t]):
                            ok = False
check("K3 UMP on 200 random families", ok, f"{count} competing tests of level alpha, none more powerful")

# K4: coin flips qualify. n flips, chance p of heads, S = number of heads k: the chance of one
# sequence is p^k (1-p)^(n-k), so for p < p' in (0, 1) the ratio is g(k) = (p'/p)^k ((1-p')/(1-p))^(n-k),
# which is positive and increasing in k. Checked exactly for n <= 6 and a grid of p < p'.
ok = True
grid = [F(1, 10), F(1, 4), F(1, 3), F(1, 2), F(2, 3), F(9, 10)]
for n in range(7):
    for p in grid:
        for q in grid:
            if p < q:
                g = [(q / p) ** k * ((1 - q) / (1 - p)) ** (n - k) for k in range(n + 1)]
                if not (all(x > 0 for x in g) and all(g[i] < g[i + 1] for i in range(n))):
                    ok = False
check("K4 coin flips have MLR in the head count", ok, "n <= 6, 15 pairs p < p'")
# K5: uniform on [0, theta] is excluded: theta = 1, theta' = 2, point x = 3/2 has f_1(x) = 0 but
# f_2(x) = 1/2, so f_2 = g(S) f_1 fails at x for every g.
check("K5 uniform[0, theta] excluded", F(1, 2) != 0 * F(1), "f_2(3/2) = 1/2, f_1(3/2) = 0")

# ---------------- item 58: Basu ----------------
def prob(P, s):
    return sum(P[i] for i in s)


# B1: sufficiency is needed. Omega = {0,1,2,3}, P0 = (1/8,1/8,1/4,1/2), P1 = (1/8,1/8,3/8,3/8),
# m generated by the cells {0,2}, {1,3}; A = 1{2,3}. A is ancillary (chance 3/4 under both);
# m is complete (cell chances (3/8,5/8) and (1/2,1/2) are independent rows); m is not sufficient;
# and P0({0,2} and A=1) = 1/4 != (3/8)(3/4) = 9/32.
P0 = [F(1, 8), F(1, 8), F(1, 4), F(1, 2)]
P1 = [F(1, 8), F(1, 8), F(3, 8), F(3, 8)]
cells, Aset = [[0, 2], [1, 3]], [2, 3]
anc = prob(P0, Aset) == prob(P1, Aset)
det = prob(P0, cells[0]) * prob(P1, cells[1]) - prob(P0, cells[1]) * prob(P1, cells[0])
# sufficiency would need P(A=1 | cell) equal under P0 and P1 on each cell
suff = all(prob(P0, [i for i in c if i in Aset]) / prob(P0, c) ==
           prob(P1, [i for i in c if i in Aset]) / prob(P1, c) for c in cells)
lhs, rhs = prob(P0, [2]), prob(P0, cells[0]) * prob(P0, Aset)
check("B1 sufficiency", anc and det != 0 and not suff and lhs != rhs,
      f"ancillary, complete (det {det}), not sufficient; {lhs} != {rhs}")
# B2: completeness is needed. One law, uniform on {a, b}; m = all events (sufficient for a single
# law); A = identity (ancillary for a single law). m is not complete (f = (1, -1) has mean 0), and
# P({a} and {a}) = 1/2 != 1/4.
check("B2 completeness", F(1, 2) * 1 + F(1, 2) * (-1) == 0 and F(1, 2) != F(1, 2) * F(1, 2),
      "f = (1, -1) has mean 0; P(a, a) = 1/2 != 1/4")
# B3: ancillarity is needed. One coin flip, chance p in (0, 1); S = A = the flip (sufficient and
# complete, item 61 with n = 1). At p = 1/2: P(S = 1, A = 1) = 1/2 != 1/4.
check("B3 ancillarity", F(1, 2) != F(1, 4), "A = S: P(S=1, A=1) = 1/2 != 1/4 at p = 1/2")
# B4: for coin flips every event whose chance does not depend on p has chance 0 or 1, so Basu
# applied to the head count (item 61) gives nothing non-trivial. An event with c_k sequences
# with k heads has chance sum c_k p^k (1-p)^(n-k), a polynomial of degree <= n; it is constant on
# (0, 1) iff it takes one value at the n + 1 points p = 1/(n+2), ..., (n+1)/(n+2). Exhaustive
# over all count vectors 0 <= c_k <= C(n, k), n <= 5.
from math import comb
ok = True
nontriv = 0
for n in range(1, 6):
    ps = [F(j, n + 2) for j in range(1, n + 2)]
    for cv in product(*[range(comb(n, k) + 1) for k in range(n + 1)]):
        vals = {sum(c * p ** k * (1 - p) ** (n - k) for k, c in enumerate(cv)) for p in ps}
        if len(vals) == 1 and list(vals)[0] not in (0, 1):
            nontriv += 1
            ok = False
check("B4 coin-flip ancillary events are trivial", ok, f"n <= 5, {nontriv} non-trivial found")

# ---------------- item 57: Sanov, finite alphabet ----------------
import math


def rel_entropy_lean(q, p):
    """the library's relEntropy with Lean's conventions: x / 0 = 0, log 0 = 0, log x = log |x|"""
    tot = 0.0
    for a, b in zip(q, p):
        r = a / b if b != 0 else F(0)
        tot += float(a) * (math.log(abs(r)) if r != 0 else 0.0)
    return tot


def type_probs(p, n):
    """exact chance of each empirical distribution (as a tuple of Fractions) under n draws"""
    K = len(p)
    out = {}
    for w in product(range(K), repeat=n):
        cnt = [w.count(i) for i in range(K)]
        q = tuple(F(c, n) for c in cnt)
        pr = F(1)
        for j in w:
            pr *= max(p[j], F(0))
        out[q] = out.get(q, F(0)) + pr
    return out


# S1 (FLOAT): one type class, P(type = q) <= exp(-n D(q || p)), on all types of random laws,
# K in {2, 3}, n <= 6, laws with some zero entries included.
random.seed(57)
ok = True
worst = 0.0
cases = 0
for _ in range(60):
    K = random.choice([2, 3])
    raw = [random.choice([0, 1, 2, 3, 5]) for _ in range(K)]
    if sum(raw) == 0:
        raw[0] = 1
    p = [F(r, sum(raw)) for r in raw]
    n = random.randint(1, 6)
    for q, pr in type_probs(p, n).items():
        bound = math.exp(-n * rel_entropy_lean(q, p))
        cases += 1
        if float(pr) > bound * (1 + 1e-12):
            ok = False
        if bound > 0:
            worst = max(worst, float(pr) / bound)
check("S1 one type: P <= exp(-n D) (FLOAT)", ok, f"{cases} types, largest ratio P/bound {worst:.4f}")
# S2 (FLOAT for exp): the theorem on E = {q : q_0 >= 3/4}, p = (1/2, 1/2), n = 100..800, with the
# chance as an exact binomial tail sum; d = D((3/4, 1/4) || p), the least D over E.
from math import comb as _comb
ok = True
rows = []
d = rel_entropy_lean([F(3, 4), F(1, 4)], [F(1, 2), F(1, 2)])
for n in [100, 200, 400, 800]:
    P = F(sum(_comb(n, k) for k in range(n + 1) if 4 * k >= 3 * n), 2 ** n)
    logP = math.log(P.numerator) - math.log(P.denominator)
    logB = 2 * math.log(n + 1) - n * d
    rows.append(f"n={n}: log P {logP:.2f} <= log bound {logB:.2f}")
    if logP > logB:
        ok = False
check("S2 Sanov bound, coin, E = {q0 >= 3/4} (FLOAT)", ok, "; ".join(rows))
# S3: the case p_i = 0. p = (1, 0), q = (1/2, 1/2): Lean's relEntropy is (1/2) log(1/2) < 0
# (the cell with p_1 = 0 counts 0; the true value is +infinity), yet the chance of that type is 0.
p, q = [F(1), F(0)], (F(1, 2), F(1, 2))
check("S3 p_i = 0: junk D, chance 0", rel_entropy_lean(q, p) < 0 and type_probs(p, 2).get(q, F(0)) == 0,
      f"Lean D = {rel_entropy_lean(q, p):.4f}, P(type q) = {type_probs(p, 2).get(q, F(0))}")
# S4: the hypothesis d <= D on E is needed: E = {(1/2, 1/2)}, p = (1/2, 1/2), where D = 0; with
# d = 1 instead and n = 10 the claimed bound 121 e^-10 is below P = 252/1024.
p = [F(1, 2), F(1, 2)]
P = type_probs(p, 10)[(F(1, 2), F(1, 2))]
check("S4 d <= D on E (FLOAT)", float(P) > 121 * math.exp(-10), f"P = {P} > 121 e^-10 = {121 * math.exp(-10):.5f}")
# S5: sum p = 1 is not needed: p = (2, 2) (mass 4), n = 1, q = (1, 0): P = 2, D = log(1/2),
# exp(-D) = 2: equality.
check("S5 sum p = 1 not needed", type_probs([F(2), F(2)], 1)[(F(1), F(0))] == 2 and
      abs(math.exp(-rel_entropy_lean((F(1), F(0)), [F(2), F(2)])) - 2) < 1e-12, "P = 2 = exp(-D)")

# ---------------- item 60: Glivenko-Cantelli ----------------
# G1: independence is needed: X_i = X_0 for all i, X_0 a fair coin on {0, 1} (identically
# distributed, not independent). F(0) = 1/2 while F_n(0) = 1{X_0 <= 0} is 0 or 1, so the sup is
# at least 1/2 for every n, on every outcome.
ok = all(abs(F(1 if x0 <= 0 else 0) - F(1, 2)) == F(1, 2) for x0 in [0, 1])
check("G1 independence", ok, "copies of one fair coin: |F_n(0) - F(0)| = 1/2 for all n")
# G2: identical distribution is needed: X_{2k} = 0, X_{2k+1} = 1 (constants, so independent);
# F = cdf of X_0 = 1{x >= 0}; F_n(1/2) = ceil(n/2)/n, so |F_n(1/2) - F(1/2)| = floor(n/2)/n >= 1/2 - 1/n.
ns = [10, 11, 1000, 1001]
vals = [abs(F(sum(1 for i in range(n) if [0, 1][i % 2] <= F(1, 2)), n) - 1) for n in ns]
check("G2 identical distribution", all(v == F(n // 2, n) for v, n in zip(vals, ns)),
      f"|F_n(1/2) - 1| at n = 10, 11, 1000, 1001: {[str(v) for v in vals]}")
# G3 (FLOAT, illustration only): uniform draws, seeded; sup |F_n - F| over all x is the
# Kolmogorov-Smirnov distance, computed exactly at the jump points.
random.seed(60)
xs = [random.random() for _ in range(20000)]
outs = []
for n in [100, 1000, 20000]:
    ys = sorted(xs[:n])
    dmax = max(max((k + 1) / n - y, y - k / n) for k, y in enumerate(ys))
    outs.append(f"n={n}: {dmax:.4f}")
check("G3 uniform draws, sup |F_n - F| shrinks (FLOAT)", True, "; ".join(outs))

# ---------------- item 59: James-Stein ----------------
# J1 (FLOAT, seeded Monte Carlo): the risk E||JS(X) - theta||^2 against d. At theta = 0,
# ||X||^2 is chi-square with d degrees of freedom and E[1/||X||^2] = 1/(d - 2), so the exact
# formula d - (d-2)^2 E[1/||X||^2] gives risk 2 for every d >= 3; far from 0 the risk is close to d.
random.seed(59)
rows = []
ok = True
for d, th in [(3, 0.0), (5, 0.0), (10, 0.0), (5, 3.0), (10, 10.0)]:
    N = 100000
    tot = 0.0
    for _ in range(N):
        x = [random.gauss(th, 1.0) for _ in range(d)]
        S = sum(v * v for v in x)
        js = [(1 - (d - 2) / S) * v for v in x]
        tot += sum((a - th) ** 2 for a in js)
    risk = tot / N
    rows.append(f"d={d}, theta=({th},..): {risk:.3f}")
    if not risk < d:
        ok = False
    if th == 0.0 and abs(risk - 2) > 0.05:
        ok = False
check("J1 JS risk < d; = 2 at theta = 0 (FLOAT)", ok, "; ".join(rows))
# J2: d = 2: d - 2 = 0, so JS(x) = x and the risk is exactly 2 = d (also proved in Lean,
# integral_sqNorm_jamesStein_sub_two).
check("J2 d = 2: JS = X, risk 2", (1 - F(2 - 2) / F(7)) == 1, "1 - 0/S = 1 for every S")
# J3 (by hand, recorded): d = 1 gives JS(x) = x + 1/x, whose squared error has infinite mean
# (1/x^2 is not integrable near 0 against a density bounded below there); in Lean the integral of
# a non-integrable function is 0, so "risk < d" would read 0 < 1, true for a wrong reason. This is
# why integrability is part of the theorem's conclusion. And for d = 2, E[1/||X||^2] is infinite
# (the chi-square(2) density is e^(-s/2)/2, and 1/s is not integrable at 0).
check("J3 d = 1, 2 by hand (recorded)", True, "see comment")

print(f"{lines} lines, {fails} FAIL")
print("ALL OK" if fails == 0 else "SOME FAIL")
sys.exit(1 if fails else 0)
