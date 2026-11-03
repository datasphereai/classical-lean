#!/usr/bin/env python3
"""LEAN-27 dropped-hypothesis cases, exact (fractions). Exit 0 only when every case behaves as stated.

Each case keeps the other hypotheses of its theorem and drops one; it prints the two sides and
whether the theorem's conclusion FAILS (as claimed) there. Lean's conventions are applied where
they decide the case: the inverse of a singular matrix is 0, x / 0 = 0.
"""
from fractions import Fraction as F
import sys

bad = 0


def report(label, claim_fails, lhs, rhs, holds):
    global bad
    ok = (not holds) == claim_fails
    bad += not ok
    print(f"{'OK ' if ok else 'BAD'} {label}: lhs {lhs}, rhs {rhs}, conclusion {'holds' if holds else 'FAILS'}")


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]


def mv(A, x):
    return [sum(A[i][j] * x[j] for j in range(len(x))) for i in range(len(A))]


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def det(A):
    n = len(A)
    if n == 1:
        return A[0][0]
    return sum((-1) ** j * A[0][j] * det([r[:j] + r[j + 1:] for r in A[1:]]) for j in range(n))


def inv(A):
    """Lean's inverse: 0 when singular."""
    n = len(A)
    d = det(A)
    if d == 0:
        return [[F(0)] * n for _ in range(n)]
    M = [list(map(F, r)) + [F(int(i == j)) for j in range(n)] for i, r in enumerate(A)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        pv = M[c][c]
        M[c] = [v / pv for v in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [a - f * b for a, b in zip(M[r], M[c])]
    return [r[n:] for r in M]


def ldiv(a, b):
    return F(0) if b == 0 else F(a) / F(b)


def diag(*d):
    return [[F(d[i]) if i == j else F(0) for j in range(len(d))] for i in range(len(d))]


# ---- item 82, dotProduct_mulVec_mul_inv_le: (xᵀAx)(xᵀA⁻¹x) ≤ (m+M)²/(4mM) (xᵀx)²
def kant(A, m, M, x):
    lhs = dot(x, mv(A, x)) * dot(x, mv(inv(A), x))
    rhs = ldiv((F(m) + M) ** 2, 4 * F(m) * M) * dot(x, x) ** 2
    return lhs, rhs, lhs <= rhs


x2 = [F(1), F(1)]
report("82 hm (m = 0): A = 1, m = 0, M = 1, x = (1)", True, *kant(diag(1), 0, 1, [F(1)]))
report("82 hm (m < 0): A = 1, m = -1, M = 1, x = (1)", True, *kant(diag(1), -1, 1, [F(1)]))
report("82 hmA: A = diag(1/4, 1), m = M = 1, x = (1, 1)", True, *kant(diag(F(1, 4), 1), 1, 1, x2))
report("82 hAM: A = diag(1, 4), m = M = 1, x = (1, 1)", True, *kant(diag(1, 4), 1, 1, x2))
report("82 sanity: A = diag(1, 4), m = 1, M = 4, x = (1, 1) (equality, the equal mix)", False,
       *kant(diag(1, 4), 1, 4, x2))
report("82 sanity: A = diag(1, 4), m = 1, M = 4, x = (2, 1) (strict)", False,
       *kant(diag(1, 4), 1, 4, [F(2), F(1)]))


# ---- item 82, dotProduct_mulVec_mul_inv_add_eq: equality at u + v
def kant_eq(A, m, M, u, v):
    w = [a + b for a, b in zip(u, v)]
    lhs = dot(w, mv(A, w)) * dot(w, mv(inv(A), w))
    rhs = ldiv((F(m) + M) ** 2, 4 * F(m) * M) * dot(w, w) ** 2
    return lhs, rhs, lhs == rhs


e3 = lambda i: [F(int(i == j)) for j in range(3)]
report("82eq hA: A = diag(1, 2, 0) singular, u = e0, v = e1, m = 1, M = 2", True,
       *kant_eq(diag(1, 2, 0), 1, 2, e3(0), e3(1)))
report("82eq hu: A = diag(1, 2), u = e0 with m = 5 (not its eigenvalue), v = e1, M = 2", True,
       *kant_eq(diag(1, 2), 5, 2, [F(1), F(0)], [F(0), F(1)]))
report("82eq hv: A = diag(1, 2), u = e0, m = 1, v = e1 with M = 5", True,
       *kant_eq(diag(1, 2), 1, 5, [F(1), F(0)], [F(0), F(1)]))
report("82eq huv (u·u = v·v): A = diag(1, 2), u = 2 e0, v = e1, m = 1, M = 2", True,
       *kant_eq(diag(1, 2), 1, 2, [F(2), F(0)], [F(0), F(1)]))
Anon = [[F(1), F(3, 4)], [F(0), F(2)]]
uu, vv = [F(1), F(0)], [F(3, 5), F(4, 5)]
assert mv(Anon, uu) == [F(1) * a for a in uu] and mv(Anon, vv) == [2 * a for a in vv]
report("82eq no orthogonality needed: A = [[1, 3/4], [0, 2]], u = (1, 0), v = (3/5, 4/5), u·v = 3/5",
       False, *kant_eq(Anon, 1, 2, uu, vv))
report("82eq no unit length needed: A = diag(1, 2), u = 3 e0, v = 3 e1", False,
       *kant_eq(diag(1, 2), 1, 2, [F(3), F(0)], [F(0), F(3)]))
report("82eq sanity: A = diag(1, 2), u = e0, v = e1, m = 1, M = 2", False,
       *kant_eq(diag(1, 2), 1, 2, [F(1), F(0)], [F(0), F(1)]))


# dotProduct_mulVec_eq_sum without B bᵢ = μᵢ bᵢ: B = diag(1, 2), standard basis, μ = 0, x = (1, 1)
lhs = dot(x2, mv(diag(1, 2), x2))
report("82 tool hμ: B = diag(1, 2), μ = 0, x = (1, 1)", True, lhs, F(0), lhs == F(0))


# ---- item 81, glsMatrix_ones_eq_minWeights: needs Vᵀ = V
def gls_row(V):
    n = len(V)
    Vi = inv(V)
    c = sum(Vi[i][j] for i in range(n) for j in range(n))
    row = [ldiv(1, c) * sum(Vi[i][j] for i in range(n)) for j in range(n)]   # (1ᵀV⁻¹1)⁻¹ 1ᵀV⁻¹
    mw = [ldiv(1, c) * sum(Vi[j][i] for i in range(n)) for j in range(n)]    # V⁻¹1 / (1ᵀV⁻¹1)
    return row, mw, row == mw


report("81 hV: V = [[2, 1], [0, 1]] (not symmetric)", True, *gls_row([[F(2), F(1)], [F(0), F(1)]]))
XtX = [[F(2), F(2)], [F(2), F(2)]]   # Xᵀ V⁻¹ X with X the 2x2 matrix of ones, V = 1
Xi = inv(XtX)                          # singular: Lean's inverse is 0
row0 = [sum(Xi[0][c] * 1 for c in range(2))] * 2   # (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹, first row: 0
report("81 Unique κ: κ = Fin 2, V = 1: GLS row 0 against minWeights 1 = (1/2, 1/2)", True,
       row0, [F(1, 2), F(1, 2)], row0 == [F(1, 2), F(1, 2)])
report("81 sanity: V = [[2, 1], [1, 3]] (symmetric)", False, *gls_row([[F(2), F(1)], [F(1), F(3)]]))
report("81 junk: V = [[1, 1], [1, 1]] singular, V⁻¹ = 0 in Lean, both sides 0", False,
       *gls_row([[F(1), F(1)], [F(1), F(1)]]))


# ---- item 80, variance_sum_div_eq with Lean's x / 0 = 0
def ratio(gamma, k):
    var = k * gamma[0] + 2 * sum((k - j) * gamma[j] for j in range(1, k))
    lhs = ldiv(var, k * gamma[0])
    rhs = 1 + 2 * sum((1 - ldiv(j, k)) * ldiv(gamma[j], gamma[0]) for j in range(1, k))
    return lhs, rhs, lhs == rhs


report("80 hk: k = 0 (empty sum, Var 0): 0 / 0 = 0 against 1", True, *ratio([F(1)], 0))
report("80 hγ: γ = 0 (X = 0), k = 2: 0 / 0 = 0 against 1", True, *ratio([F(0), F(0)], 2))
# hcov dropped: X 0 = X 1 with variance 1, so Var(X 0 + X 1) = 4
report("80 hcov (sum): X0 = X1, Var 1, γ = 0, k = 2: 4 against 0", True, F(4), F(0), F(4) == F(0))
lhs = ldiv(4, 2 * 1)
rhs = 1 + 2 * (1 - ldiv(1, 2)) * ldiv(0, 1)
report("80 hcov (ratio, γ 0 ≠ 0 kept): X0 = X1, Var 1, γ = (1, 0), k = 2", True, lhs, rhs, lhs == rhs)
lhs = ldiv(4, 2 * 2)
rhs = 1 + 2 * (1 - ldiv(1, 2)) * ldiv(0, 2)
report("80 note: γ = (2, 0) would hold (1 against 1), so γ 0 = 1 matters", False, lhs, rhs, lhs == rhs)
report("80 sanity: γ = (2, 1, 1/2), k = 3", False, *ratio([F(2), F(1), F(1, 2)], 3))


# variance identity itself on an MA(1) series X_t = Z_t + Z_(t-1), Z unit variance: γ0 = 2, γ1 = 1
def var_sum_ma1(k):
    # X_0 + ... + X_(k-1) = Z_(-1) + 2 (Z_0 + ... + Z_(k-2)) + Z_(k-1)
    return 1 + 4 * (k - 1) + 1 if k >= 1 else 0


for k in range(1, 7):
    g = [F(2), F(1)] + [F(0)] * k
    rhs = k * g[0] + 2 * sum((k - j) * g[j] for j in range(1, k))
    report(f"80 sanity: MA(1), k = {k}", False, var_sum_ma1(k), rhs, var_sum_ma1(k) == rhs)


# ---- item 83, sum_mul_le_sum_of_antitone; each case must break exactly the named hypothesis
def kyfan_core(lam, w, k, drop):
    hyps = {
        "hlam": all(lam[i] >= lam[i + 1] for i in range(len(lam) - 1)),
        "hw0": all(x >= 0 for x in w),
        "hw1": all(x <= 1 for x in w),
        "hk": k <= len(lam),
        "hsum": sum(w) == k,
    }
    broken = sorted(h for h, v in hyps.items() if not v)
    if broken != ([drop] if drop else []):
        raise SystemExit(f"case breaks {broken}, not only {drop}")
    lhs = sum(a * b for a, b in zip(lam, w))
    rhs = sum(lam[:k])
    return lhs, rhs, lhs <= rhs


report("83 hlam: λ = (0, 1), w = (0, 1), k = 1", True, *kyfan_core([F(0), F(1)], [F(0), F(1)], 1, "hlam"))
report("83 hw0: λ = (1, 1, 0), w = (1, 1, -1), k = 1 (r83's case)", True,
       *kyfan_core([F(1), F(1), F(0)], [F(1), F(1), F(-1)], 1, "hw0"))
report("83 hw1: λ = (1, 0, 0), w = (2, 0, 0), k = 2", True,
       *kyfan_core([F(1), F(0), F(0)], [F(2), F(0), F(0)], 2, "hw1"))
report("83 hsum: λ = (1, 1), w = (1, 1), k = 1 (Σ w = 2)", True,
       *kyfan_core([F(1), F(1)], [F(1), F(1)], 1, "hsum"))
report("83 sanity: λ = (3, 1, -2), w = (1/2, 1, 1/2), k = 2", False,
       *kyfan_core([F(3), F(1), F(-2)], [F(1, 2), F(1), F(1, 2)], 2, None))
# sum_re_inner_le_sum_eigenvalues without orthonormality, each half of it
report("83 hu (unit norm): T = id on ℝ¹, k = 1, u_0 = 2", True, F(4), F(1), F(4) <= F(1))
T = diag(1, 0)
e0 = [F(1), F(0)]
lhs = 2 * dot(e0, mv(T, e0))
report("83 hu (orthogonality): T = diag(1, 0), k = 2, u_0 = u_1 = e0", True, lhs, F(1), lhs <= F(1))

print("ALL OK" if bad == 0 else f"{bad} BAD")
sys.exit(1 if bad else 0)
