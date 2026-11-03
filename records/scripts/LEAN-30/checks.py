"""Exact checks for order LEAN-30 (items 96 to 100 of MATH-PLAN-library-2), by claude-ai.

Standard library only; run with `python3 -I LEAN-30-checks.py`. Each line printed is
`HIT label: what` or `MISS label: what [measured: ...]`; cases worked by hand print as `BY HAND`
lines and are not counted. The last line is `== X of Y checks hit`. rc 0 when every check hits.

Arithmetic follows Lean's conventions: `x / 0 = 0`; `Real.log 0 = 0` and `Real.log x =
Real.log |x|`; `t / k` in `ℕ` truncates and `t / 0 = 0`; `0 ^ 0 = 1`; Mathlib's covariance is
`∫ (X − ∫ X)(Y − ∫ Y) dμ` and its variance of a square-integrable `X` the same with `Y = X`, for
any finite measure (the integrals are not normalised). Fractions are exact; the lines on relative
entropy (item 97) use floating point for the logarithms and say FLOAT, with every compared gap
either at least 0.1 or a tolerance of 1e-9 stated in the line. Random cases use
`random.Random(<item number>)`, so the output is the same on every run.

PREDICTIONS, written before the first run:
- 96.hadamard: det S <= prod S_ii for 200 random rational Gram matrices, n from 1 to 5. HIT.
- 96.cov: det(covMatrix) <= prod Var for 150 random finite laws (2 to 6 points, masses summing to
  1/2, 1 or 3) and 1 to 4 variables, Mathlib's unnormalised covariance. HIT.
- 96.drop.L2: the zero-diagonal 3x3 matrix with off-diagonal entries 1 has det 2 > 0. HIT.
- 96.drop.fin: the 4x4 matrix [[0,0,1,0],[0,0,0,1],[1,0,2,0],[0,1,0,2]] has det 1 > 0. HIT.
- 97.random: FLOAT, 300 random chains (2 to 4 states, some zero entries, some with two closed
  classes), pi stationary, mu >= 0 vanishing where pi does: D(mu P || pi) <= D(mu || pi) + 1e-9. HIT.
- 97.signs: FLOAT, 100 random two-class chains with pi negative on one class: the same. HIT.
- 97.drop.hP0, 97.drop.hP, 97.drop.hmu, 97.drop.hmupi, 97.drop.hpi: each case fails the
  conclusion by at least 0.1. HIT, 5 lines.
- 98.random: 200 random V = H D H (H a rational Householder matrix, D diagonal in [m, M]),
  n from 1 to 5: (1'V1)(1'V^-1 1)/n^2 <= (m+M)^2/(4mM), exact. HIT.
- 98.equal: V = diag(m, M), n = 2: equality, for 20 pairs m < M. HIT.
- 98.drop.hm, 98.drop.hmV, 98.drop.hVM, 98.drop.nonempty: each fails, the other hypotheses
  checked to hold (a 1x1 or 2x2 symmetric matrix is positive semidefinite when its diagonal
  entries and its determinant are >= 0). HIT, 4 lines.
- 98.witness (revision 2): V = [[2, 1], [1, 3]], m = 1, M = 4 meets the hypotheses and the left
  side 21/20 lies strictly between 1 and the bound 25/16. HIT.
- 99.ml: for n <= 10, every count of wins k and p in {0, 1/10, ..., 1, 1/3, 2/3}:
  p^k (1-p)^(n-k) <= (k/n)^k (1 - k/n)^(n-k) (0^0 = 1; at n = 0 both are 1). HIT.
- 99.score: for n <= 6, every string and p in the grid with P_p{x} != 0: plug-in score <= fixed
  score (code length 0, the inequality does not depend on it). HIT.
- 99.rate: for n <= 8, p in the grid, alpha in {1, 1/2, 1/3, 1/4, 1/8}, two Kraft codes (every
  word of length n; the two-part code): P_p{plug-in score >= 1/alpha} <= alpha. HIT.
- 99.drop.hx, 99.drop.hc, 99.drop.hpf, 99.drop.halpha: each fails, with the code's words written
  out and the other hypotheses (injective, prefix-free) checked on them. HIT, 4 lines.
- 99.witness (revision 2): n = 2, p = 1/3, x = (win, loss): fixed mass 2/9 < plug-in mass 1/4,
  so the plug-in score is strictly smaller. HIT.
- 100.unique: 200 random chains with a zero entry but some power k <= 4 with every entry > 0,
  n from 2 to 4: exactly one stationary vector of total 1, and it is >= 0. HIT.
- 100.unique.neg: 100 random chains with a negative entry but some power k <= 4 with every entry
  > 0: the same (the theorem has no P >= 0). HIT.
- 100.rate: 200 random chains P >= 0 with P^k >= delta (delta the least entry of P^k, k from 1
  to 3), mu of any sign with the total of pi, t <= 12: the bound with (1 - n delta)^(t div k). HIT.
- 100.k0: the same cells with k = 0 and delta = min entry of the identity: the bound holds (t div 0
  = 0). HIT.
- 100.drop.u.hP, 100.drop.u.hpos, 100.drop.u.nonempty, 100.drop.r.hP0, 100.drop.r.hP,
  100.drop.r.hdelta, 100.drop.r.hmu, 100.drop.r.hpi: each fails, the other hypotheses checked to
  hold. HIT, 8 lines.
- BY HAND lines: 96 (hX, the measure-theoretic case), 96 (IsFiniteMeasure, the measure), 97 (pi
  >= 0 not needed), 100 (P >= 0 not needed for uniqueness; k > 0 not needed): 4 lines.
Total predicted: 36 checks, 36 hit, 4 BY HAND lines, rc 0 (revision 1, run once: 36 of 36).
Revision 2 (after cold review 1): the drop lines of items 98, 99 and 100 check the other
hypotheses too, and two witness lines are added. Predicted: 38 checks, 38 hit, 4 BY HAND, rc 0.
Revision 3 (after cold review 2): a rate case whose other hypotheses fail returns None, so its
line prints MISS instead of stopping the script. Predicted: the same output as revision 2.
"""
import math
import random
import sys
from fractions import Fraction as F
from itertools import product

RESULTS = []


def check(label, ok, what, measured=None):
    RESULTS.append(ok)
    if ok:
        print(f'HIT  {label}: {what}')
    else:
        print(f'MISS {label}: {what}  [measured: {measured}]')


def by_hand(label, what):
    print(f'BY HAND {label}: {what}')


# ---------- exact linear algebra ----------

def det(A):
    n = len(A)
    M = [list(r) for r in A]
    d = F(1)
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None:
            return F(0)
        if p != c:
            M[c], M[p] = M[p], M[c]
            d = -d
        d *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            for k in range(c, n):
                M[r][k] -= f * M[c][k]
    return d


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))]
            for i in range(len(A))]


def matpow(A, k):
    n = len(A)
    R = [[F(int(i == j)) for j in range(n)] for i in range(n)]
    for _ in range(k):
        R = matmul(R, A)
    return R


def vecmul(v, A):
    return [sum(v[i] * A[i][j] for i in range(len(v))) for j in range(len(A[0]))]


def inv(A):
    n = len(A)
    M = [list(r) + [F(int(i == j)) for j in range(n)] for i, r in enumerate(A)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        pv = M[c][c]
        M[c] = [x / pv for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [a - f * b for a, b in zip(M[r], M[c])]
    return [r[n:] for r in M]


def nullspace_left(P):
    """Vectors v with v (P - I) = 0: the null space of (P - I)^T, by exact elimination."""
    n = len(P)
    A = [[P[j][i] - (1 if i == j else 0) for j in range(n)] for i in range(n)]
    M = [list(r) for r in A]
    piv = []
    r = 0
    for c in range(n):
        p = next((i for i in range(r, n) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        pv = M[r][c]
        M[r] = [x / pv for x in M[r]]
        for i in range(n):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv.append(c)
        r += 1
    free = [c for c in range(n) if c not in piv]
    basis = []
    for fc in free:
        v = [F(0)] * n
        v[fc] = F(1)
        for i, pc in enumerate(piv):
            v[pc] = -M[i][fc]
        basis.append(v)
    return basis


def rand_frac(rng, lo, hi, den=12):
    return F(rng.randint(lo * den, hi * den), den)


# ---------- item 96 ----------

def item96():
    rng = random.Random(96)
    ok = True
    for _ in range(200):
        n = rng.randint(1, 5)
        m = rng.randint(1, 6)
        V = [[rand_frac(rng, -3, 3) for _ in range(m)] for _ in range(n)]
        S = [[sum(V[i][k] * V[j][k] for k in range(m)) for j in range(n)] for i in range(n)]
        prod_d = F(1)
        for i in range(n):
            prod_d *= S[i][i]
        ok = ok and det(S) <= prod_d
    check('96.hadamard', ok, 'det S <= prod S_ii for 200 random rational Gram matrices, n 1 to 5')
    ok = True
    for _ in range(150):
        pts = rng.randint(2, 6)
        k = rng.randint(1, 4)
        total = rng.choice([F(1, 2), F(1), F(3)])
        w = [F(rng.randint(1, 9)) for _ in range(pts)]
        s = sum(w)
        w = [x * total / s for x in w]
        X = [[rand_frac(rng, -2, 2, 6) for _ in range(pts)] for _ in range(k)]
        mean = [sum(w[a] * X[i][a] for a in range(pts)) for i in range(k)]
        C = [[sum(w[a] * (X[i][a] - mean[i]) * (X[j][a] - mean[j]) for a in range(pts))
              for j in range(k)] for i in range(k)]
        prod_v = F(1)
        for i in range(k):
            prod_v *= C[i][i]
        ok = ok and det(C) <= prod_v
    check('96.cov', ok, 'det(covMatrix) <= prod Var, 150 random finite laws of mass 1/2, 1 or 3, '
          '1 to 4 variables (Mathlib\'s unnormalised covariance)')
    C = [[F(0), F(1), F(1)], [F(1), F(0), F(1)], [F(1), F(1), F(0)]]
    check('96.drop.L2', det(C) == 2 and det(C) > 0,
          'zero diagonal, off-diagonal 1: det 2 > 0 = the product of the diagonal', det(C))
    by_hand('96.drop.L2', 'three variables on [0, 1] with Lebesgue measure, each X_k = Z_k 1_{A_k} + t W '
            '(A_k disjoint thirds, Z_k integrable but not square-integrable on A_k, W = x, t large): '
            'each X_k is integrable, not in L2, so Lean\'s cov[X_k, X_k] = 0 (the integral of a '
            'non-integrable function) and Var = 0 (evariance = infinity, toReal 0); the cross '
            'covariances are integrable and positive for large t; det = 2 c12 c13 c23 > 0')
    C = [[F(0), F(0), F(1), F(0)], [F(0), F(0), F(0), F(1)], [F(1), F(0), F(2), F(0)],
         [F(0), F(1), F(0), F(2)]]
    check('96.drop.fin', det(C) == 1, 'the 4x4 matrix of the infinite-measure case has det 1 > 0 = '
          'the product of the variances', det(C))
    by_hand('96.drop.fin', 'Lebesgue measure on R (not finite): X1 = 1_[0,1], X2 = 1_[1,2] (mean 1, '
            'so (X - 1)^2 is not integrable: cov 0, Var 0), X3 = 1_[0,1] - 1_[2,3], X4 = 1_[1,2] - '
            '1_[3,4] (mean 0); all in L2; cov(X1, X3) = cov(X2, X4) = 1, Var X3 = Var X4 = 2, the rest 0: '
            'the matrix above')


# ---------- item 97 ----------

def rlog(x):
    return 0.0 if x == 0 else math.log(abs(x))


def rel(p, q):
    s = 0.0
    for a, b in zip(p, q):
        r = 0.0 if b == 0 else a / b
        s += a * rlog(r)
    return s


def rand_stochastic(rng, n, zeros=True):
    P = []
    for _ in range(n):
        row = [F(rng.randint(0 if zeros else 1, 6)) for _ in range(n)]
        if sum(row) == 0:
            row[rng.randrange(n)] = F(1)
        s = sum(row)
        P.append([x / s for x in row])
    return P


def stationary_one(P):
    """One stationary vector of total 1 (exact), from the left null space."""
    for v in nullspace_left(P):
        s = sum(v)
        if s != 0:
            return [x / s for x in v]
    return None


def item97():
    rng = random.Random(97)
    ok = True
    worst = 0.0
    case = 0
    while case < 300:
        if case % 3 == 2:
            a, b = rng.randint(1, 2), rng.randint(1, 2)
            A, B = rand_stochastic(rng, a, False), rand_stochastic(rng, b, False)
            n = a + b
            P = [[F(0)] * n for _ in range(n)]
            for i in range(a):
                for j in range(a):
                    P[i][j] = A[i][j]
            for i in range(b):
                for j in range(b):
                    P[a + i][a + j] = B[i][j]
            pa, pb = stationary_one(A), stationary_one(B)
            c = F(rng.randint(0, 4), 4)
            pi = [c * x for x in pa] + [(1 - c) * x for x in pb]
        else:
            n = rng.randint(2, 4)
            P = rand_stochastic(rng, n)
            pi = stationary_one(P)
            if pi is None or any(x < 0 for x in pi):
                continue
        case += 1
        mu = [F(0) if pi[i] == 0 else F(rng.randint(0, 5)) for i in range(n)]
        muP = vecmul(mu, P)
        assert vecmul(pi, P) == pi
        lhs, rhs = rel([float(x) for x in muP], [float(x) for x in pi]), rel(
            [float(x) for x in mu], [float(x) for x in pi])
        worst = max(worst, lhs - rhs)
        ok = ok and lhs <= rhs + 1e-9
    check('97.random', ok, 'FLOAT: D(mu P || pi) <= D(mu || pi) + 1e-9 for 300 random chains '
          '(some zero entries, some with two closed classes)', worst)
    ok = True
    worst = 0.0
    for _ in range(100):
        a, b = rng.randint(1, 2), rng.randint(1, 2)
        A, B = rand_stochastic(rng, a, False), rand_stochastic(rng, b, False)
        n = a + b
        P = [[F(0)] * n for _ in range(n)]
        for i in range(a):
            for j in range(a):
                P[i][j] = A[i][j]
        for i in range(b):
            for j in range(b):
                P[a + i][a + j] = B[i][j]
        pa, pb = stationary_one(A), stationary_one(B)
        c = F(rng.randint(1, 3), 4)
        pi = [-c * x for x in pa] + [(1 - c) * x for x in pb]
        assert vecmul(pi, P) == pi
        mu = [F(rng.randint(0, 5)) for _ in range(n)]
        muP = vecmul(mu, P)
        lhs = rel([float(x) for x in muP], [float(x) for x in pi])
        rhs = rel([float(x) for x in mu], [float(x) for x in pi])
        worst = max(worst, lhs - rhs)
        ok = ok and lhs <= rhs + 1e-9
    check('97.signs', ok, 'FLOAT: the same for 100 two-class chains with pi negative on one class '
          '(no pi >= 0 in the statement)', worst)
    by_hand('97.signs', 'pi P = pi with P >= 0 and rows summing to 1 gives |pi| P = |pi| '
            '(|pi| P >= |pi P| entrywise, and both sides have the same total), and Lean\'s '
            'relEntropy p q depends on q only through |q| (Real.log x = Real.log |x|), so the theorem '
            'for |pi| gives it for pi')
    cases = [
        ('97.drop.hP0', [[F(3, 2), F(-1, 2)], [F(-1, 2), F(3, 2)]], [F(1, 2), F(1, 2)], [F(1), F(0)]),
        ('97.drop.hP', [[F(1), F(1)], [F(0), F(0)]], [F(1, 2), F(1, 2)], [F(1), F(0)]),
        ('97.drop.hmu', [[F(1, 2), F(1, 2)], [F(1, 2), F(1, 2)]], [F(1, 2), F(1, 2)], [F(-1), F(0)]),
        ('97.drop.hmupi', [[F(1), F(0)], [F(1), F(0)]], [F(1), F(0)], [F(1, 2), F(1, 2)]),
        ('97.drop.hpi', [[F(1), F(0)], [F(1), F(0)]], [F(1, 2), F(1, 2)], [F(1, 2), F(1, 2)]),
    ]
    for label, P, pi, mu in cases:
        hP0 = all(x >= 0 for r in P for x in r)
        hP = all(sum(r) == 1 for r in P)
        hmu = all(x >= 0 for x in mu)
        hmupi = all(mu[i] == 0 for i in range(2) if pi[i] == 0)
        hpi = vecmul(pi, P) == pi
        held = {'hP0': hP0, 'hP': hP, 'hmu': hmu, 'hmupi': hmupi, 'hpi': hpi}
        dropped = label.split('.')[-1]
        others = all(v for k, v in held.items() if k != dropped) and not held[dropped]
        muP = vecmul(mu, P)
        lhs = rel([float(x) for x in muP], [float(x) for x in pi])
        rhs = rel([float(x) for x in mu], [float(x) for x in pi])
        check(label, others and lhs - rhs >= 0.1,
              f'FLOAT: P = {[[str(x) for x in r] for r in P]}, pi = {[str(x) for x in pi]}, '
              f'mu = {[str(x) for x in mu]}: D(mu P || pi) = {lhs:.4f} > D(mu || pi) = {rhs:.4f}; '
              f'only {dropped} fails', (held, lhs, rhs))


# ---------- item 98 ----------

def householder(v):
    n = len(v)
    s = sum(x * x for x in v)
    return [[F(int(i == j)) - 2 * v[i] * v[j] / s for j in range(n)] for i in range(n)]


def eff(V):
    n = len(V)
    one = [F(1)] * n
    q1 = sum(one[i] * sum(V[i][j] for j in range(n)) for i in range(n))
    Vi = inv(V)
    q2 = sum(sum(Vi[i][j] for j in range(n)) for i in range(n))
    return F(0) if n == 0 else q1 * q2 / (n * n)


def bound(m, M):
    d = 4 * m * M
    return F(0) if d == 0 else (m + M) ** 2 / d


def item98():
    rng = random.Random(98)
    ok = True
    for _ in range(200):
        n = rng.randint(1, 5)
        m = F(rng.randint(1, 6), rng.randint(1, 3))
        M = m + F(rng.randint(0, 12), rng.randint(1, 3))
        D = [m + (M - m) * F(rng.randint(0, 10), 10) for _ in range(n)]
        v = [F(rng.randint(-4, 4)) for _ in range(n)]
        if all(x == 0 for x in v):
            v[0] = F(1)
        H = householder(v)
        V = matmul(matmul(H, [[D[i] if i == j else F(0) for j in range(n)] for i in range(n)]), H)
        ok = ok and eff(V) <= bound(m, M)
    check('98.random', ok, '(1\'V1)(1\'V^-1 1)/n^2 <= (m+M)^2/(4mM) for 200 random V = H D H, '
          'H a rational Householder matrix, D diagonal in [m, M], n 1 to 5')
    ok = True
    for _ in range(20):
        m = F(rng.randint(1, 9), rng.randint(1, 4))
        M = m + F(rng.randint(1, 9), rng.randint(1, 4))
        ok = ok and eff([[m, F(0)], [F(0), M]]) == bound(m, M)
    check('98.equal', ok, 'equality at V = diag(m, M), n = 2, for 20 pairs m < M')
    diag = lambda a, b: [[F(a), F(0)], [F(0), F(b)]]

    def psd(A):
        n = len(A)
        assert all(A[i][j] == A[j][i] for i in range(n) for j in range(n)) and n <= 2
        return all(A[i][i] >= 0 for i in range(n)) and det(A) >= 0

    def hyps(V, m, M):
        n = len(V)
        I = [[F(int(i == j)) for j in range(n)] for i in range(n)]
        return {'hm': m > 0,
                'hmV': psd([[V[i][j] - m * I[i][j] for j in range(n)] for i in range(n)]),
                'hVM': psd([[M * I[i][j] - V[i][j] for j in range(n)] for i in range(n)]),
                'nonempty': n > 0}

    def drop98(label, V, m, M, what):
        h = hyps(V, m, M)
        dropped = label.split('.')[-1]
        only = all(v for k, v in h.items() if k != dropped) and not h[dropped]
        lhs = eff(V) if V else F(0)
        check(label, only and lhs > bound(m, M), what + f'; only {dropped} fails',
              (h, lhs, bound(m, M)))
    drop98('98.drop.hm', [[F(1)]], F(0), F(1),
           'V = (1), m = 0, M = 1: left side 1 > Lean\'s 1/0 = 0')
    drop98('98.drop.hmV', diag(1, 4), F(2), F(4), 'V = diag(1, 4), m = 2, M = 4: 25/16 > 9/8')
    drop98('98.drop.hVM', diag(1, 4), F(1), F(2), 'V = diag(1, 4), m = 1, M = 2: 25/16 > 9/8')
    drop98('98.drop.nonempty', [], F(1), F(-2),
           'no index, m = 1, M = -2: left side 0 (x / 0 = 0) > (m + M)^2/(4 m M) = -1/8')
    W = [[F(2), F(1)], [F(1), F(3)]]
    h = hyps(W, F(1), F(4))
    check('98.witness', all(h.values()) and eff(W) == F(21, 20) and 1 < eff(W) < bound(F(1), F(4)),
          'V = [[2, 1], [1, 3]], m = 1, M = 4: hypotheses hold; left side 21/20, strictly between 1 '
          'and 25/16', (h, eff(W)))


# ---------- item 99 ----------

GRID = [F(i, 10) for i in range(11)] + [F(1, 3), F(2, 3)]


def mass(p, k, n):
    return p ** k * (1 - p) ** (n - k)


def phat(k, n):
    return F(0) if n == 0 else F(k, n)


def two_part_len(x):
    n, k = len(x), sum(x)
    a = math.ceil(math.log2(n + 1)) if n > 0 else 0
    b = math.ceil(math.log2(math.comb(n, k))) if math.comb(n, k) > 1 else 0
    return a + b


def false_alarm(n, p, alpha, L):
    tot = F(0)
    for x in product([0, 1], repeat=n):
        k = sum(x)
        pm = mass(phat(k, n), k, n)
        sc = F(0) if pm == 0 else F(1, 2 ** L(x)) / pm
        thr = F(0) if alpha == 0 else 1 / alpha
        if thr <= sc:
            tot += mass(p, k, n)
    return tot


def item99():
    ok = True
    for n in range(11):
        for k in range(n + 1):
            for p in GRID:
                ok = ok and mass(p, k, n) <= mass(phat(k, n), k, n)
    check('99.ml', ok, 'p^k (1-p)^(n-k) <= p^ k (1-p^)^(n-k), p^ = k/n, for n <= 10, every k, '
          'p in {0, 1/10, ..., 1, 1/3, 2/3}')
    ok = True
    for n in range(7):
        for x in product([0, 1], repeat=n):
            k = sum(x)
            for p in GRID:
                pm = mass(p, k, n)
                if pm != 0:
                    ok = ok and 1 / mass(phat(k, n), k, n) <= 1 / pm
    check('99.score', ok, 'plug-in score <= fixed score at every string with P_p{x} != 0, n <= 6')
    ok = True
    worst = None
    for n in range(9):
        for p in GRID:
            for alpha in [F(1), F(1, 2), F(1, 3), F(1, 4), F(1, 8)]:
                for L in (lambda x: len(x), two_part_len):
                    fa = false_alarm(n, p, alpha, L)
                    if fa > alpha:
                        ok = False
                        worst = (n, p, alpha, fa)
    check('99.rate', ok, 'P_p{plug-in score >= 1/alpha} <= alpha for n <= 8, p in the grid, '
          'alpha in {1, 1/2, 1/3, 1/4, 1/8}, two Kraft codes (every word of length n; the two-part '
          'code)', worst)
    # hx: n = 1, p = 0, x = (win), word length 1
    fixed = F(0)  # P_0{(win)} = 0, Lean's score 2^-1 / 0 = 0
    plug = F(1, 2) / mass(phat(1, 1), 1, 1)
    check('99.drop.hx', mass(F(0), 1, 1) == 0 and plug > fixed,
          'n = 1, p = 0, x = (win), length 1: plug-in score 1/2 > Lean\'s fixed score 2^-1/0 = 0')
    def injective(code):
        return len(set(code.values())) == len(code)

    def prefix_free(code):
        ws = set(code.values())
        return not any(a != b and b[:len(a)] == a for a in ws for b in ws)
    # hc: every string of length 2 sent to [] (length 0): fair coin, alpha = 1/4
    code = {x: () for x in product([0, 1], repeat=2)}
    fa = false_alarm(2, F(1, 2), F(1, 4), lambda x: len(code[x]))
    check('99.drop.hc', fa == F(1, 2) and not injective(code) and prefix_free(code),
          'every string of length 2 sent to []: not injective, prefix-free; scores 1, 4, 4, 1; '
          'fair coin, alpha = 1/4: chance 1/2 > 1/4', fa)
    # hpf: n = 3, injective words, not prefix-free: [] [0] [1] to the first three strings with
    # a win and a loss (lexicographic order, 0 = loss), the rest [0,0], [0,1], [1,0], [1,1], [0,0,0]
    strings = list(product([0, 1], repeat=3))
    mixed = [x for x in strings if 0 < sum(x) < 3]
    code = {mixed[0]: (), mixed[1]: (0,), mixed[2]: (1,)}
    rest = [(0, 0), (0, 1), (1, 0), (1, 1), (0, 0, 0)]
    for x in strings:
        if x not in code:
            code[x] = rest.pop(0)
    kraft = sum(F(1, 2 ** len(v)) for v in code.values())
    fa = false_alarm(3, F(1, 2), F(1, 3), lambda x: len(code[x]))
    check('99.drop.hpf', fa == F(3, 8) and kraft > 1 and injective(code) and not prefix_free(code),
          f'n = 3, words [] [0] [1] on the strings {mixed[0]}, {mixed[1]}, {mixed[2]} (Kraft sum '
          f'{kraft}): fair coin, alpha = 1/3: chance 3/8 > 1/3', (fa, kraft))
    code = {x: x for x in product([0, 1], repeat=2)}
    fa = false_alarm(2, F(1, 2), F(0), lambda x: len(code[x]))
    check('99.drop.halpha', fa == 1 and injective(code) and prefix_free(code),
          'the code writing each string of length 2 out as it is (injective, prefix-free), '
          'alpha = 0: Lean\'s 1/0 = 0 <= every score, chance 1 > 0', fa)
    fixed, plug = mass(F(1, 3), 1, 2), mass(phat(1, 2), 1, 2)
    check('99.witness', fixed == F(2, 9) and plug == F(1, 4) and fixed < plug,
          'n = 2, p = 1/3, x = (win, loss): fixed mass 2/9 < plug-in mass 1/4', (fixed, plug))


# ---------- item 100 ----------

def all_pos_power(P, kmax):
    for k in range(1, kmax + 1):
        Q = matpow(P, k)
        if all(x > 0 for r in Q for x in r):
            return k
    return None


def l1(v):
    return sum(abs(x) for x in v)


def item100():
    rng = random.Random(100)
    ok = True
    done = 0
    while done < 200:
        n = rng.randint(2, 4)
        P = rand_stochastic(rng, n)
        if all(x > 0 for r in P for x in r) or all_pos_power(P, 4) is None:
            continue
        ns = nullspace_left(P)
        pi = stationary_one(P)
        ok = ok and len(ns) == 1 and pi is not None and all(x >= 0 for x in pi)
        done += 1
    check('100.unique', ok, '200 random chains with a zero entry and some P^k > 0, k <= 4: one '
          'stationary vector of total 1, and it is >= 0')
    ok = True
    done = 0
    while done < 100:
        n = rng.randint(2, 4)
        P = []
        for _ in range(n):
            row = [F(rng.randint(-2, 8), 8) for _ in range(n)]
            row[-1] = 1 - sum(row[:-1])
            P.append(row)
        if all(x >= 0 for r in P for x in r) or all_pos_power(P, 4) is None:
            continue
        ns = nullspace_left(P)
        pi = stationary_one(P)
        ok = ok and len(ns) == 1 and pi is not None and all(x >= 0 for x in pi)
        done += 1
    check('100.unique.neg', ok, '100 random chains with a negative entry and some P^k > 0, '
          'k <= 4: the same (no P >= 0 in the uniqueness theorem)')
    by_hand('100.unique', 'P >= 0 is not needed for uniqueness: Q = P^k has rows summing to 1 and '
            'entries >= delta > 0, so the library\'s contraction (sum_abs_vecMul_le, any sign) makes '
            'Q\'s stationary vector of total 1 unique among all real vectors; pi* P is one, so '
            'pi* P = pi*. k > 0 is not needed: at k = 0, P^0 = 1 has every entry > 0 only with one '
            'state, where P = (1)')
    ok = True
    ok0 = True
    done = 0
    while done < 200:
        n = rng.randint(2, 4)
        P = rand_stochastic(rng, n)
        k = all_pos_power(P, 3)
        if k is None:
            continue
        Q = matpow(P, k)
        delta = min(x for r in Q for x in r)
        pi = stationary_one(P)
        mu = [rand_frac(rng, -2, 2, 4) for _ in range(n)]
        mu[-1] += sum(pi) - sum(mu)
        base = l1([a - b for a, b in zip(mu, pi)])
        for t in range(13):
            lhs = l1([a - b for a, b in zip(vecmul(mu, matpow(P, t)), pi)])
            ok = ok and lhs <= (1 - n * delta) ** (t // k) * base
            delta0 = min(F(int(i == j)) for i in range(n) for j in range(n))
            ok0 = ok0 and lhs <= (1 - n * delta0) ** 0 * base
        done += 1
    check('100.rate', ok, '200 random chains P >= 0 with P^k >= delta > 0 (k 1 to 3), mu of any sign '
          'with the total of pi, t <= 12: sum |mu P^t - pi| <= (1 - n delta)^(t div k) sum |mu - pi|')
    check('100.k0', ok0, 'the same cells with k = 0 (t div 0 = 0, delta <= the identity\'s entries): '
          'sum |mu P^t - pi| <= sum |mu - pi|')
    # uniqueness drops
    rows1 = lambda P: all(sum(r) == 1 for r in P)
    P = [[F(1), F(1)], [F(1), F(1)]]
    check('100.drop.u.hP', stationary_one(P) is None and all_pos_power(P, 1) == 1 and not rows1(P),
          'P all 1 (rows sum to 2), P^1 > 0: no stationary vector of total 1')
    P = [[F(1), F(0)], [F(0), F(1)]]
    check('100.drop.u.hpos', len(nullspace_left(P)) == 2 and rows1(P)
          and all_pos_power(P, 12) is None and not all(x > 0 for r in P for x in r),
          'P = 1 (2 states), rows sum to 1, no power k <= 12 (nor k = 0) has every entry > 0: '
          '(1, 0) and (0, 1) are both stationary laws')
    check('100.drop.u.nonempty', sum([]) != 1, 'no state: no vector has total 1')
    # rate drops
    def rate_case(P, k, delta, mu, pi, t, dropped):
        n = len(P)
        Q = matpow(P, k)
        h = {'hP0': all(x >= 0 for r in P for x in r), 'hP': rows1(P),
             'hdelta': all(delta <= x for r in Q for x in r), 'hmu': sum(mu) == sum(pi),
             'hpi': vecmul(pi, P) == pi}
        only = all(v for kk, v in h.items() if kk != dropped) and not h[dropped]
        lhs = l1([a - b for a, b in zip(vecmul(mu, matpow(P, t)), pi)])
        rhs = (1 - n * delta) ** (t // k if k else 0) * l1([a - b for a, b in zip(mu, pi)])
        return (lhs, rhs) if only else (None, h)
    lhs, rhs = rate_case([[F(3, 2), F(-1, 2)], [F(-1, 2), F(3, 2)]], 2, F(-3, 2),
                         [F(1), F(0)], [F(1, 2), F(1, 2)], 1, 'hP0')
    check('100.drop.r.hP0', lhs == 2 and rhs == 1,
          'P = [[3/2, -1/2], [-1/2, 3/2]], k = 2, delta = -3/2 (P^2 = [[5/2, -3/2], [-3/2, 5/2]]), '
          'mu = (1, 0), pi = (1/2, 1/2), t = 1: 2 > 1', (lhs, rhs))
    lhs, rhs = rate_case([[F(2), F(0)], [F(0), F(2)]], 1, F(0), [F(1), F(-1)], [F(0), F(0)], 1, 'hP')
    check('100.drop.r.hP', lhs == 4 and rhs == 2, 'P = 2 * 1, k = 1, delta = 0, mu = (1, -1), '
          'pi = 0, t = 1: 4 > 2', (lhs, rhs))
    lhs, rhs = rate_case([[F(1), F(0)], [F(0), F(1)]], 1, F(1, 2), [F(1), F(0)], [F(0), F(1)], 1, 'hdelta')
    check('100.drop.r.hdelta', lhs == 2 and rhs == 0, 'P = 1, k = 1, delta = 1/2, mu = (1, 0), '
          'pi = (0, 1), t = 1: 2 > 0', (lhs, rhs))
    half = [[F(1, 2), F(1, 2)], [F(1, 2), F(1, 2)]]
    lhs, rhs = rate_case(half, 1, F(1, 2), [F(0), F(0)], [F(1, 2), F(1, 2)], 1, 'hmu')
    check('100.drop.r.hmu', lhs == 1 and rhs == 0, 'P all 1/2, k = 1, delta = 1/2, mu = 0, '
          'pi = (1/2, 1/2), t = 1: 1 > 0', (lhs, rhs))
    lhs, rhs = rate_case(half, 1, F(1, 2), [F(1), F(0)], [F(1), F(0)], 1, 'hpi')
    check('100.drop.r.hpi', lhs == 1 and rhs == 0, 'P all 1/2, k = 1, delta = 1/2, '
          'mu = pi = (1, 0), not stationary, t = 1: 1 > 0', (lhs, rhs))


def main():
    print('== item 96')
    item96()
    print('== item 97')
    item97()
    print('== item 98')
    item98()
    print('== item 99')
    item99()
    print('== item 100')
    item100()
    hit = sum(RESULTS)
    print(f'== {hit} of {len(RESULTS)} checks hit' + ('' if hit == len(RESULTS) else ' -- SOME MISS'))
    return 0 if hit == len(RESULTS) else 1


if __name__ == '__main__':
    sys.exit(main())
