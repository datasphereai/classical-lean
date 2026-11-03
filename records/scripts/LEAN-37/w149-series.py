# Item 149 witnesses: the coefficients of T = X * f(T), f(s) = sum p_k s^k, by fixed-point iteration
# to degree N (coefficient n of T depends only on coefficients < n, so N iterations are exact to N).
from fractions import Fraction as F
from math import comb
N = 80
def solve(p):
    T = [F(0)] * (N + 1)
    for _ in range(N + 1):
        fT = [F(0)] * (N + 1); P = [F(1)] + [F(0)] * N  # P = T^k
        for k, pk in enumerate(p):
            for i in range(N + 1): fT[i] += pk * P[i]
            P = [sum(P[a] * T[i - a] for a in range(i + 1)) for i in range(N + 1)]
        T = [F(0)] + fT[:N]
    return T
T1 = solve([F(1, 4), F(1, 4), F(1, 2)])
print("law (1/4,1/4,1/2): first coefficients", [str(c) for c in T1[:6]])
print("  nonzero coefficients up to", N, ":", sum(1 for c in T1 if c != 0), "; partial sum", float(sum(T1)))
T2 = solve([F(1, 2), F(0), F(1, 2)])
cat = lambda n: comb(2 * n, n) // (n + 1)
print("law (1/2,0,1/2): odd = catalan/2^(2n+1):", all(T2[2 * n + 1] == F(cat(n), 2 ** (2 * n + 1)) for n in range(N // 2)),
      "; even = 0:", all(T2[2 * n] == 0 for n in range(N // 2 + 1)), "; partial sum", float(sum(T2)))
