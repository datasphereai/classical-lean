#!/usr/bin/env python3
"""LEAN-25 checks: the hypothesis cases for items 62 to 66. Exact fractions unless a line says
FLOAT. Prints one line per check and ALL OK at the end; exits 1 on any failure."""
import itertools
import math
import random
import sys
from fractions import Fraction as F

fails = []
lines = []


def check(name, ok, text):
    lines.append(f"{'OK  ' if ok else 'FAIL'} {name}: {text}")
    if not ok:
        fails.append(name)


def payoff(A, x, y):
    return sum(x[i] * A[i][j] * y[j] for i in range(len(A)) for j in range(len(A[0])))


def pure(n, j):
    return [F(1) if k == j else F(0) for k in range(n)]


# ---------- item 62 ----------
A = [[F(1), F(0)], [F(0), F(1)]]
h = [F(1, 2), F(1, 2)]
ok = all(payoff(A, h, pure(2, j)) <= payoff(A, h, h) <= payoff(A, pure(2, i), h)
         for i in range(2) for j in range(2))
check("G1 item 62 sanity", ok and payoff(A, h, h) == F(1, 2),
      "A = I2: x = y = (1/2, 1/2) is a saddle point (pure deviations suffice by linearity), value 1/2")
check("G2 item 62 nonempty rows", sum([]) != 1,
      "no rows: the sum over no coordinates is 0, never 1, so the simplex is empty and no saddle point exists")

# ---------- item 66 ----------


def softmax(v):
    m = max(v)
    e = [math.exp(a - m) for a in v]
    s = sum(e)
    return [a / s for a in e]


def ew_run(A, eta, T, br):
    """Exponential weights for the row player against best responses chosen by br. FLOAT."""
    m, n = len(A), len(A[0])
    S = [0.0] * m
    xs, ys = [], []
    for t in range(T):
        x = softmax([-eta * S[i] for i in range(m)])
        j = br(A, x)
        y = [1.0 if k == j else 0.0 for k in range(n)]
        xs.append(x)
        ys.append(y)
        for i in range(m):
            S[i] += A[i][j]
    xb = [sum(x[i] for x in xs) / T for i in range(m)]
    yb = [sum(y[j] for y in ys) / T for j in range(n)]
    up = max(sum(xb[i] * A[i][j] for i in range(m)) for j in range(n))
    lo = min(sum(A[i][j] * yb[j] for j in range(n)) for i in range(m))
    return up - lo


def best_first(A, x):
    vals = [sum(x[i] * A[i][j] for i in range(len(A))) for j in range(len(A[0]))]
    best = max(vals)
    return min(j for j in range(len(vals)) if vals[j] >= best - 1e-12)


# G3: payoffs outside [0, 1]
A10 = [[F(10), F(0)], [F(0), F(10)]]
xb = [F(1, 2), F(1, 2)]                    # T = 1: softmax of zero scores
up = max(payoff(A10, xb, pure(2, j)) for j in range(2))
yb = pure(2, 0)                           # a pure best response (both columns tie)
lo = min(payoff(A10, pure(2, i), yb) for i in range(2))
bound = math.sqrt(math.log(2) / 2)
check("G3 item 66 payoffs in [0, 1]", up - lo == 5 and 5 > bound,
      f"A = 10 I2, T = 1: upper side {up}, lower side {lo}, gap {up - lo} > sqrt(log 2 / 2) = {bound:.4f} (FLOAT bound)")

# G4: eta = 0
xu = [F(1, 2), F(1, 2)]
up = max(payoff(A, xu, pure(2, j)) for j in range(2))
lo = min(payoff(A, pure(2, i), pure(2, 0)) for i in range(2))
check("G4 item 66 eta > 0", up - lo == F(1, 2),
      "eta = 0: weights stay (1/2, 1/2); best response always column 0; gap 1/2 > 0 = Lean's log 2 / (0 * T) + 0 / 8")

# G5: T = 0
check("G5 item 66 T > 0", F(0) != 1,
      "T = 0: Lean's averages are 0 / 0 = 0, whose coordinates sum to 0, not 1: not strategies")

# G6: best responses dropped (FLOAT)
T = 100
eta = math.sqrt(8 * math.log(2) / T)
gap = ew_run([[1, 0], [0, 1]], eta, T, lambda A_, x: 0)
bnd = math.sqrt(math.log(2) / (2 * T))
check("G6 item 66 best responses", gap > bnd,
      f"A = I2, T = 100, column 0 every round: gap {gap:.4f} > {bnd:.4f} (FLOAT)")

# G7: sanity (FLOAT)
random.seed(25)
worst = 0.0
count = 0
for trial in range(300):
    m = random.randint(2, 5)
    n = random.randint(1, 5)
    Ar = [[random.random() for _ in range(n)] for _ in range(m)]
    for T in (1, 5, 50, 200):
        eta = math.sqrt(8 * math.log(m) / T)
        g = ew_run(Ar, eta, T, best_first)
        b = math.sqrt(math.log(m) / (2 * T))
        worst = max(worst, g - b)
        count += 1
check("G7 item 66 sanity", worst <= 1e-9,
      f"{count} runs (random [0,1] payoffs, up to 5 x 5, T in 1, 5, 50, 200): gap <= sqrt(log m / (2T)) every time, largest excess {worst:.2e} (FLOAT)")

# ---------- item 63 ----------
# G8: 0-1 loss, two parameters, two actions, no data: minimax 1/2, largest Bayes risk 1/2.
grid = [F(k, 100) for k in range(101)]
minimax = min(max(q * 0 + (1 - q) * 1, q * 1 + (1 - q) * 0) for q in grid)
bayes = max(min(p * 0 + (1 - p) * 1, p * 1 + (1 - p) * 0) for p in grid)
check("G8 item 63 sanity", minimax == F(1, 2) and bayes == F(1, 2),
      "0-1 loss, two parameters, two actions, no data: minimax risk 1/2 = largest Bayes risk 1/2 (q = p = 1/2 on a grid of 101; both are linear, so the grid hits the optimum)")

# G9: an infinite loss: equality still holds (both sides 1)
INF = float("inf")


def risk(theta, q):  # q = chance of action a; loss(0,a)=inf, loss(0,b)=0, loss(1,a)=0, loss(1,b)=1
    if theta == 0:
        return 0 if q == 0 else INF          # 0 * inf = 0 in [0, inf]
    return (1 - q) * 1


mm = min(max(risk(0, q), risk(1, q)) for q in grid)


def bayes_p(p):
    best = INF
    for q in grid:
        v = (0 if p == 0 else p * risk(0, q)) + (1 - p) * risk(1, q)
        best = min(best, v)
    return best


bp = [bayes_p(p) for p in grid]
check("G9 item 63 finite loss", mm == 1 and max(bp) == F(99, 100) and bayes_p(F(1, 10**6)) == 1 - F(1, 10**6),
      "loss(0,a) = inf: minimax risk 1 (q = 0); Bayes risk 1 - p for p > 0 and 0 at p = 0, supremum 1 (not attained): equal, so this case does not show the hypothesis is needed")

check("G10 item 63 nonempty actions", True,
      "by hand: no parameter, one data value, no action: no prior exists, left side 0 (empty supremum); no Markov kernel exists, right side is the infimum over nothing, inf in [0, inf]: 0 != inf")


# ---------- item 64 ----------
sys.path.insert(0, "/home/dustin/lean/lean25-checks")
import tremaux_sim as TS  # noqa: E402

o = TS.main()
total, bad, treebad = o["intact"]
check("T1 item 64 intact marks", total == 186 and bad == 0 and treebad == 0,
      f"{total} runs (7 small graphs, every start, every choice the rule leaves open): every one ends at the start with every path crossed once each way and every vertex visited ({bad} not), and the first-entry tree is a Trémaux tree ({treebad} not)")
tried, found = o["erased"]
over = [f for f in found if max(f[6]) > 2]
check("T2 item 64 one stroke erased", tried == 19417 and len(found) == 9521,
      f"{tried} runs with one stroke erased (any end, any moment): {len(found)} break 'exactly twice' or the return to the start; in {len(over)} some path is crossed more than twice")
n, edges = TS.GRAPHS["triangle"]
A3 = TS.adj(n, edges)
tri = [r for r in TS.runs(A3, 0, TS.fresh(A3), 0, None, [0], (4, (1, 2))) if r[2] is True]
routes = sorted({tuple(r[0]) for r in tri})
c = TS.crossings(list(routes[0])) if routes else {}
check("T3 item 64 the triangle case", (0, 1, 2, 0, 2, 1, 2) in routes and
      c.get((1, 2), 0) + c.get((2, 1), 0) == 3 and c.get((0, 1), 0) + c.get((1, 0), 0) == 1,
      f"triangle from 0, stroke at 1's end of path 12 erased after 0-1-2-0-2: routes {routes}; path 12 crossed 3 times, path 01 once, stops at 2")
check("T4 item 64 valid chooser", True,
      "by hand: path 0-1-2 from 0, a chooser that picks 2 (offered: 1) makes step give none at once; 2 is never visited")


# ---------- item 65 ----------


def cyc_prod(r, c):
    out = F(1)
    for a, b in zip(c, c[1:] + c[:1]):
        out *= r[a][b]
    return out


def bf(w, k):
    n = len(w)
    d = [F(0)] * n
    for _ in range(k):
        d = [min(d[j], min(d[i] + w[i][j] for i in range(n))) for j in range(n)]
    return d


# A1: a zero rate: Lean reads log 0 as 0, so rate 0 counts as rate 1
r = [[F(1), F(0)], [F(2), F(1)]]
prod01 = cyc_prod(r, [0, 1])
lean_neglog_sum = -math.log(2)            # -log 0 (Lean: 0) - log 2
check("A1 item 65 r > 0 (zero rate)", prod01 == 0 and lean_neglog_sum < 0,
      f"r01 = 0, r10 = 2: cycle product {prod01} <= 1 (no gain), but Lean's -log 0 = 0 gives cycle weight -log 2 = {lean_neglog_sum:.4f} < 0: (a) holds, (c) fails (sign exact, value FLOAT)")
# A2: negative rates: prices exist but a cycle gains
r = [[F(1), F(-2)], [F(-2), F(1)]]
p = [F(1), F(1)]
prices_ok = all(r[i][j] * p[j] <= p[i] for i in range(2) for j in range(2))
check("A2 item 65 r > 0 (negative rates)", prices_ok and cyc_prod(r, [0, 1]) == 4,
      "r01 = r10 = -2: p = (1, 1) satisfies r i j p j <= p i, yet the cycle 0 -> 1 -> 0 has product 4 > 1: (b) holds, (a) fails")
# A3: n - 2 rounds are not enough
BIG = F(5)
w = [[F(0), F(-1), BIG], [BIG, F(0), F(-1)], [BIG, BIG, F(0)]]
cycles_ok = all(sum(w[a][b] for a, b in zip(c, c[1:] + c[:1])) >= 0
                for L in range(1, 4) for c in itertools.product(range(3), repeat=L))
d1, d2, d3 = bf(w, 1), bf(w, 2), bf(w, 3)
check("A3 item 65 n - 1 rounds", cycles_ok and d1 != d2 and d2 == d3,
      f"3 assets, weights w01 = w12 = -1, others 5 off the diagonal, 0 on it: no negative cycle; rounds 1, 2, 3 give {[str(x) for x in d1]}, {[str(x) for x in d2]}, {[str(x) for x in d3]}: n - 2 = 1 round is not settled, n - 1 = 2 is")
# A4: sanity (FLOAT rates, exact enumeration of cycles up to length n)
random.seed(65)
agree = 0
trials = 0
for t in range(400):
    n = random.randint(1, 4)
    rr = [[math.exp(random.uniform(-0.3, 0.3)) for _ in range(n)] for _ in range(n)]
    gain = any(math.prod(rr[a][b] for a, b in zip(c, c[1:] + c[:1])) > 1 + 1e-12
               for L in range(1, n + 1) for c in itertools.product(range(n), repeat=L))
    ww = [[-math.log(rr[i][j]) for j in range(n)] for i in range(n)]
    dd = [0.0] * n
    hist = [dd]
    for _ in range(n):
        dd = [min(dd[j], min(dd[i] + ww[i][j] for i in range(n))) for j in range(n)]
        hist.append(dd)
    stable = all(abs(a - b) < 1e-12 for a, b in zip(hist[n], hist[n - 1]))
    pr = [math.exp(x) for x in hist[n - 1]]
    prices = all(rr[i][j] * pr[j] <= pr[i] * (1 + 1e-12) for i in range(n) for j in range(n))
    trials += 1
    if (not gain) == stable and (not gain) == prices:
        agree += 1
check("A4 item 65 sanity", agree == trials,
      f"{trials} random rate tables (1 to 4 assets, rates in [e^-0.3, e^0.3]): no gain on cycles up to length n <=> Bellman-Ford stable after n - 1 rounds <=> exp(d) are prices, in {agree} of {trials} (FLOAT)")

# ---------- report ----------
for l in lines:
    print(l)
print("ALL OK" if not fails else "FAILED: " + ", ".join(fails))
sys.exit(1 if fails else 0)
