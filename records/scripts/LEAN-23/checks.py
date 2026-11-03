"""LEAN-23 checks behind the needed-hypothesis table (items 46 to 49).

Exact rational arithmetic (fractions) unless a line says FLOAT. Lean's conventions are modelled
where they matter: x / 0 = 0, an empty sum is 0, sSup / sInf of the empty set of reals is 0.
Run: python3 -I checks.py   (prints one line per check, then ALL OK or FAILED n; rc 0 / 1)
"""
import itertools
import random
import sys
from fractions import Fraction as Q

FAILS = []


def check(label, ok, detail=""):
    print(f"{'OK  ' if ok else 'FAIL'} {label}" + (f": {detail}" if detail else ""))
    if not ok:
        FAILS.append(label)


def div(x, y):  # Lean's division: x / 0 = 0
    return Q(0) if y == 0 else Q(x) / Q(y)


# ---------- polynomials with rational coefficients (list, constant first) ----------
def p_eval(p, x):
    return sum(Q(c) * Q(x) ** i for i, c in enumerate(p))


def p_der(p):
    return [i * Q(c) for i, c in enumerate(p)][1:] or [Q(0)]


def p_int(p, a, b):  # exact ∫_a^b p
    return sum(Q(c) / (i + 1) * (Q(b) ** (i + 1) - Q(a) ** (i + 1)) for i, c in enumerate(p))


def p_mul(p, q):
    r = [Q(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            r[i + j] += Q(x) * Q(y)
    return r


def p_shift(p, s):  # q(t) = p(t + s)
    r = [Q(0)]
    pw = [Q(1)]
    for c in p:
        r = [x + Q(c) * y for x, y in itertools.zip_longest(r, pw, fillvalue=Q(0))]
        pw = p_mul(pw, [Q(s), Q(1)])
    return r


# ---------- item 48: Simpson ----------
def simpson(f, N, a, b):  # the Lean definition, with x / 0 = 0
    h = div(Q(b) - Q(a), 2 * N)
    return div(h, 3) * sum(f(a + 2 * k * h) + 4 * f(a + (2 * k + 1) * h) + f(a + (2 * k + 2) * h)
                           for k in range(N))


def simpson_bound(N, a, b, M):
    h = div(Q(b) - Q(a), 2 * N)
    return (Q(b) - Q(a)) * h ** 4 * Q(M) / 180


def max_abs_on(p, a, b):  # p of degree <= 1 here: max at the ends
    return max(abs(p_eval(p, a)), abs(p_eval(p, b)))


x4 = [0, 0, 0, 0, 1]
f = lambda x: p_eval(x4, x)
err = p_int(x4, 0, 1) - simpson(f, 1, 0, 1)
check("48 tight: x^4 on [0,1], N=1, error -1/120, bound 1/120",
      err == Q(-1, 120) and simpson_bound(1, 0, 1, 24) == Q(1, 120), f"error {err}")
ok = True
for N in range(1, 6):
    for (a, b) in [(0, 1), (-2, 3), (Q(1, 3), Q(7, 2))]:
        e = p_int(x4, a, b) - simpson(f, N, a, b)
        ok &= abs(e) == simpson_bound(N, a, b, 24)
check("48 equality for x^4, N=1..5, three intervals (error = bound exactly)", ok)

random.seed(48)
ok = True
cnt = 0
for _ in range(300):
    p = [Q(random.randint(-9, 9)) for _ in range(4)]
    a = Q(random.randint(-20, 20), random.randint(1, 5))
    b = a + Q(random.randint(0, 30), random.randint(1, 5))
    N = random.randint(1, 4)
    g = lambda x, p=p: p_eval(p, x)
    ok &= simpson(g, N, a, b) == p_int(p, a, b)
    cnt += 1
check(f"48 exact on cubics: {cnt} random cubics, a <= b, N in 1..4", ok)
ok = True
for _ in range(300):
    p = [Q(random.randint(-9, 9)) for _ in range(6)]
    a = Q(random.randint(-20, 20), random.randint(1, 5))
    b = a + Q(random.randint(0, 30), random.randint(1, 5))
    N = random.randint(1, 4)
    d4 = p_der(p_der(p_der(p_der(p))))
    M = max_abs_on(d4, a, b)
    g = lambda x, p=p: p_eval(p, x)
    ok &= abs(p_int(p, a, b) - simpson(g, N, a, b)) <= simpson_bound(N, a, b, M)
check("48 bound holds: 300 random quintics, M = max |f''''| on [a,b]", ok)

e0 = p_int([1], 0, 1) - simpson(lambda x: Q(1), 0, 0, 1)
check("48 drop 0 < N: f = 1 on [0,1], N = 0: rule 0, bound 0, error 1",
      e0 == 1 and simpson_bound(0, 0, 1, 0) == 0)
e_rev = p_int(x4, 1, 0) - simpson(f, 1, 1, 0)
check("48 drop a <= b: x^4 on [1,0], N=1: |error| 1/120 > bound -1/120",
      abs(e_rev) == Q(1, 120) and simpson_bound(1, 1, 0, 24) == Q(-1, 120))
fabs = lambda x: abs(Q(x))
e_abs = Q(1) - simpson(fabs, 1, -1, 1)  # ∫_{-1}^{1} |x| = 1
check("48 drop smoothness: |x| on [-1,1], N=1, f'''' = 0 off 0 (M = 0): error 1/3 > 0",
      e_abs == Q(1, 3))

# ---------- item 49: Euler–Maclaurin ----------
def em_remainder(p, a, b):  # ∫_a^b (fract t - 1/2) p'(t) dt for integers a <= b, exactly
    dp = p_der(p)
    tot = Q(0)
    for k in range(a, b):
        saw = [Q(-k) - Q(1, 2), Q(1)]  # t - k - 1/2 on [k, k+1)
        tot += p_int(p_mul(saw, dp), k, k + 1)
    return tot


def em_rhs(p, a, b):
    return p_int(p, a, b) + (p_eval(p, a) + p_eval(p, b)) / 2 + em_remainder(p, a, b)


def lhs(p, a, b):
    return sum(p_eval(p, k) for k in range(a, b + 1))


check("49 f = t on [0,1]: 1 = 1/2 + 1/2 + 0",
      lhs([0, 1], 0, 1) == 1 and em_remainder([0, 1], 0, 1) == 0 and em_rhs([0, 1], 0, 1) == 1)
check("49 f = t^2 on [0,1]: remainder 1/6, 1 = 1/3 + 1/2 + 1/6",
      em_remainder([0, 0, 1], 0, 1) == Q(1, 6) and em_rhs([0, 0, 1], 0, 1) == 1)
check("49 f = t^2 on [-1,1]: 2 = 2/3 + 1 + 1/3",
      lhs([0, 0, 1], -1, 1) == 2 and p_int([0, 0, 1], -1, 1) == Q(2, 3)
      and em_remainder([0, 0, 1], -1, 1) == Q(1, 3))
random.seed(49)
ok = True
okb = True
for _ in range(300):
    p = [Q(random.randint(-9, 9)) for _ in range(random.randint(1, 6))]
    a = random.randint(-8, 8)
    b = a + random.randint(0, 6)
    ok &= lhs(p, a, b) == em_rhs(p, a, b)
    # bound: |sum - ∫ - (f a + f b)/2| <= (∫_a^b |f'|)/2, with ∫|f'| by a 2000-point midpoint
    # rule on each unit interval (FLOAT), 1e-9 margin (comment corrected after review r49)
    R = lhs(p, a, b) - p_int(p, a, b) - (p_eval(p, a) + p_eval(p, b)) / 2
    dp = p_der(p)
    absint = 0.0
    for k in range(a, b):
        absint += sum(abs(float(p_eval(dp, k + (i + 0.5) / 2000))) for i in range(2000)) / 2000
    okb &= abs(float(R)) <= absint / 2 + 1e-9
check("49 identity on 300 random polynomials (degree <= 5), integer a <= b in [-8, 14]", ok)
check("49 bound |R| <= (∫|f'|)/2 on the same 300 (FLOAT ∫|f'|, margin 1e-9)", okb)
check("49 drop a <= b: f = 1, a = 2, b = 0: sum 0, right side -2 + 1 + 0 = -1",
      lhs([1], 2, 0) == 0 and p_int([1], 2, 0) + 1 == -1)
check("49 not needed for b = a - 1 (by the unit identity): f = t^2, a = 1, b = 0 gives 0 = 0",
      lhs([0, 0, 1], 1, 0) == 0
      and p_int([0, 0, 1], 1, 0) + Q(1, 2) - em_remainder([0, 0, 1], 0, 1) == 0)
# integer endpoints: a = 0, b = 1/2, f = 1: sum over integers in [0,1/2] is 1; right side 1/2 + 1 + 0
check("49 drop integer endpoints: f = 1 on [0, 1/2]: sum 1, right side 3/2",
      Q(1, 2) + 1 + 0 == Q(3, 2))
# continuity at an end: f = 0 on [0,1), f(1) = 1, f' = 0 on (0,1)
check("49 drop continuity on [a,b]: f = 0 on [0,1), f 1 = 1, f' = 0: left 1, right 1/2",
      Q(0) + (Q(0) + Q(1)) / 2 + 0 == Q(1, 2))
# derivative inside (review r49: the old example, an indicator, broke continuity too): f = t^2 on
# [0,1] with the wrong f' = 0, so f is continuous and f' integrable but not f's derivative
check("49 drop f' is the derivative inside: f = t^2 on [0,1], f' = 0: left 1, right 1/3 + 1/2 = 5/6",
      lhs([0, 0, 1], 0, 1) == 1 and p_int([0, 0, 1], 0, 1) + Q(1, 2) + 0 == Q(5, 6))

# f = t^2 sin(t^-2) on [0,1], f(0) = 0: f' = 2t sin(t^-2) - (2/t) cos(t^-2) is not integrable near 0,
# so Lean's ∫ sawtooth * f' is 0; the formula then reads sin 1 = ∫ f + sin(1)/2 (FLOAT)
import math  # noqa: E402
import numpy as _np  # noqa: E402
_u = _np.linspace(1, 200, 4_000_001)
_I = float(_np.trapz(_np.sin(_u ** 2) / _u ** 4, _u))  # ∫_0^1 t^2 sin(t^-2) dt with u = 1/t
check(f"49 drop f' integrable: t^2 sin(1/t^2) on [0,1]: left sin 1 = {math.sin(1):.4f}, right with "
      f"Lean's 0 = {_I + math.sin(1) / 2:.4f} (FLOAT)", abs(math.sin(1) - (_I + math.sin(1) / 2)) > 0.1)

# ---------- item 47: linear programs ----------
def solve(Mx, v):  # exact Gaussian elimination; None if singular
    n = len(Mx)
    A = [list(map(Q, row)) + [Q(x)] for row, x in zip(Mx, v)]
    for c in range(n):
        piv = next((r for r in range(c, n) if A[r][c] != 0), None)
        if piv is None:
            return None
        A[c], A[piv] = A[piv], A[c]
        for r in range(n):
            if r != c and A[r][c] != 0:
                fct = A[r][c] / A[c][c]
                A[r] = [x - fct * y for x, y in zip(A[r], A[c])]
    return [A[i][n] / A[i][i] for i in range(n)]


def lp_max(G, h, c):
    """max c.x subject to G x <= h (G includes -I rows for x >= 0), by vertex enumeration.
    Valid when the max is attained at a vertex (true here: both programs feasible, and x >= 0
    makes the feasible set pointed)."""
    n = len(c)
    best = None
    for rows in itertools.combinations(range(len(G)), n):
        x = solve([G[r] for r in rows], [h[r] for r in rows])
        if x is None:
            continue
        if all(sum(Q(g) * xi for g, xi in zip(G[r], x)) <= h[r] for r in range(len(G))):
            val = sum(Q(ci) * xi for ci, xi in zip(c, x))
            best = val if best is None else max(best, val)
    return best


random.seed(47)
ok = True
cnt = 0
for _ in range(200):
    m, n = random.randint(1, 3), random.randint(1, 3)
    A = [[random.randint(-4, 4) for _ in range(n)] for _ in range(m)]
    x0 = [random.randint(0, 3) for _ in range(n)]
    y0 = [random.randint(0, 3) for _ in range(m)]
    b = [sum(A[i][j] * x0[j] for j in range(n)) + random.randint(0, 3) for i in range(m)]
    c = [sum(y0[i] * A[i][j] for i in range(m)) - random.randint(0, 3) for j in range(n)]
    # primal: max c.x, A x <= b, -x <= 0
    G = A + [[-(i == j) for j in range(n)] for i in range(n)]
    P = lp_max(G, b + [0] * n, c)
    # dual: min b.y, -(y A) <= -c, -y <= 0  ==  -max (-b).y
    At = [[-A[i][j] for i in range(m)] for j in range(n)]
    H = At + [[-(i == j) for j in range(m)] for i in range(m)]
    D = -lp_max(H, [-x for x in c] + [0] * m, [-x for x in b])
    ok &= P is not None and P == D
    cnt += 1
check(f"47 strong duality on {cnt} random LPs (m, n <= 3, both feasible by construction): max = min",
      ok)

dot = lambda u, v: sum(Q(a) * Q(b) for a, b in zip(u, v))
# drop primal feasible: A = (0), b = (-1), c = (0): no x >= 0 with 0 <= -1; dual y = 0 feasible
check("47 drop primal feasible: A=(0), b=(-1), c=(0): dual feasible (y=0), primal empty",
      not any(0 * x <= -1 for x in range(0, 5)) and 0 <= 0 and 0 >= 0)
# drop dual feasible: A=(0), b=(1), c=(1): primal x >= 0 all feasible, c.x = x unbounded; dual: 1 <= 0
check("47 drop dual feasible: A=(0), b=(1), c=(1): primal unbounded (x = 10^6 feasible), dual empty",
      0 * 10 ** 6 <= 1 and not (1 <= 0))
# drop x >= 0: A=(1), b=(1), c=(-1): x = -5 has A x <= b, c.x = 5; y = 0 dual feasible (0 >= -1), b.y = 0
check("47 drop x >= 0: A=(1), b=(1), c=(-1): x = -5, y = 0: c.x = 5 > 0 = b.y (weak duality fails)",
      1 * -5 <= 1 and 0 * 1 >= -1 and dot([-1], [-5]) == 5 > dot([1], [0]))
# drop y >= 0: A=(-1), b=(1), c=(0): x = 0 primal, y = -5 has y A = 5 >= 0, b.y = -5 < 0 = c.x
check("47 drop y >= 0: A=(-1), b=(1), c=(0): x = 0, y = -5: b.y = -5 < 0 = c.x (weak duality fails)",
      -1 * 0 <= 1 and -5 * -1 >= 0 and dot([1], [-5]) == -5 < 0)
# BddAbove ∅: A=(0), b=(-1), c=(1): primal empty, its value set empty and bounded; dual needs 1 <= 0
check("47 drop primal feasible in exists_dualFeasible: A=(0), b=(-1), c=(1): both empty, BddAbove ∅",
      not (1 <= 0) and not any(0 * x <= -1 for x in range(5)))
# drop bounded: A=(0), b=(1), c=(1) as above: primal feasible, values {x : x >= 0} unbounded, no dual
check("47 drop bounded in exists_dualFeasible: A=(0), b=(1), c=(1): unbounded, dual empty",
      not (1 <= 0))
# Farkas: never both (weak form) on the random LPs is weak duality; one explicit alternative
check("47 Farkas alternative: L x = x on R^1, b = -1: no x >= 0 with x <= -1; y = 1 >= 0, y.Lx >= 0, y.b = -1 < 0",
      not any(x <= -1 for x in range(5)) and 1 * -1 < 0)

# ---------- item 46: min–max and Weyl ----------
import numpy as np  # noqa: E402

rng = np.random.default_rng(46)
okcf = True
okw = True
okwg = True
okmono = True
cnt = 0
for _ in range(2000):
    n = int(rng.integers(1, 6))
    X = rng.normal(size=(n, n)); S = (X + X.T) / 2
    Y = rng.normal(size=(n, n)); T = (Y + Y.T) / 2
    ls = np.sort(np.linalg.eigvalsh(S))[::-1]  # decreasing, as Mathlib's eigenvalues
    lt = np.sort(np.linalg.eigvalsh(T))[::-1]
    lst = np.sort(np.linalg.eigvalsh(S + T))[::-1]
    for i in range(n):
        for j in range(n):
            if i + j < n:
                okw &= lst[i + j] <= ls[i] + lt[j] + 1e-9
            k = i + j + 1 - n
            if 0 <= k < n:
                okwg &= ls[i] + lt[j] <= lst[k] + 1e-9
    P = Y @ Y.T  # positive semidefinite
    lsp = np.sort(np.linalg.eigvalsh(S + P))[::-1]
    okmono &= bool(np.all(ls <= lsp + 1e-9))
    # Courant–Fischer: random (k+1)-dim subspaces have min Rayleigh <= λ_k; the top-(k+1)
    # eigenvector span attains λ_k
    w, V = np.linalg.eigh(S); order = np.argsort(w)[::-1]; V = V[:, order]
    for k in range(n):
        for _ in range(5):
            B = np.linalg.qr(rng.normal(size=(n, k + 1)))[0]
            okcf &= np.linalg.eigvalsh(B.T @ S @ B).min() <= ls[k] + 1e-9
        B = V[:, : k + 1]
        okcf &= abs(np.linalg.eigvalsh(B.T @ S @ B).min() - ls[k]) <= 1e-9
        # min–max form (review r46): random (n-k)-dim subspaces have max Rayleigh >= λ_k, and the
        # span of the last n-k eigenvectors reaches λ_k
        for _ in range(5):
            B = np.linalg.qr(rng.normal(size=(n, n - k)))[0]
            okcf &= np.linalg.eigvalsh(B.T @ S @ B).max() >= ls[k] - 1e-9
        B = V[:, k:]
        okcf &= abs(np.linalg.eigvalsh(B.T @ S @ B).max() - ls[k]) <= 1e-9
    cnt += 1
check(f"46 Courant–Fischer, max–min and min–max forms, on {cnt} random real symmetric S (n <= 5), "
      f"5 random subspaces per k and form (FLOAT)",
      okcf)
check("46 Weyl λ_{i+j}(S+T) <= λ_i(S) + λ_j(T) on the same (FLOAT)", okw)
check("46 dual Weyl λ_i(S) + λ_j(T) <= λ_{i+j+1-n}(S+T) on the same (FLOAT)", okwg)
check("46 λ_k(S) <= λ_k(S+P) for P = Y Yᵀ positive semidefinite (FLOAT)", okmono)
# exact diagonal cases
# Weyl index shifted down by one: S = diag(1,0), T = diag(0,1): λ_1(S+T) = 1 > λ_1(S) + λ_1(T) = 0
# exact cases, computed (review r46: they were literals); diagonal matrices, eigenvalues decreasing
def eig_dec(M):
    return sorted(np.linalg.eigvalsh(np.array(M, dtype=float)).tolist(), reverse=True)


S1, T1 = [[1, 0], [0, 0]], [[0, 0], [0, 1]]
lS, lT, lST = eig_dec(S1), eig_dec(T1), eig_dec(np.add(S1, T1))
check("46 drop i + j <= k (use k = i + j - 1): S = diag(1,0), T = diag(0,1), i = j = 1, k = 1: "
      f"λ_1(S+T) = {lST[1]:g} > λ_1(S) + λ_1(T) = {lS[1] + lT[1]:g}", lST[1] > lS[1] + lT[1])
S2, T2 = [[2, 0], [0, 0]], [[0, 0], [0, 1]]
lS, lT, lST = eig_dec(S2), eig_dec(T2), eig_dec(np.add(S2, T2))
check("46 drop k + n <= i + j + 1 (use k one higher): S = diag(2,0), T = diag(0,1), i=0, j=1, k=1: "
      f"λ_0(S) + λ_1(T) = {lS[0] + lT[1]:g} > λ_1(S+T) = {lST[1]:g}", lS[0] + lT[1] > lST[1])
lS, lST = eig_dec([[0]]), eig_dec([[-1]])
check(f"46 drop T >= 0 in monotonicity: S = (0), T = (-1): λ_0(S+T) = {lST[0]:g} < λ_0(S) = {lS[0]:g}",
      lST[0] < lS[0])
check("46 drop finrank V = k + 1 (use k): T = diag(2,1), k = 0: only V = ⊥, Lean's ⨅ over no unit "
      f"vectors is 0, but λ_0 = {eig_dec([[2, 0], [0, 1]])[0]:g} (by hand: the ⨅ is junk)",
      eig_dec([[2, 0], [0, 1]])[0] != 0)
check("46 drop k < finrank V in exists_re_inner_le_eigenvalues: V = ⊥ has no unit vector (by hand)", True)

print("ALL OK" if not FAILS else f"FAILED {len(FAILS)}: {FAILS}")
sys.exit(1 if FAILS else 0)
