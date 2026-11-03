#!/usr/bin/env python3
"""Exact checks for order LEAN-28 (items 84 to 88 and 80b): the hypothesis rows.

Fractions throughout, with Lean's conventions where they decide a case: x / 0 = 0, 0 ^ 0 = 1,
an empty sum is 0. Every case keeps the other hypotheses of its theorem. The script sets its exit
code: 0 only if every line is a HIT.
"""
import itertools, random, sys
from fractions import Fraction as F

RESULTS = []
def check(label, ok, claim, measured=''):
    RESULTS.append(bool(ok))
    print(f"{'HIT ' if ok else 'MISS'} {label}: {claim}" + (f"  [measured: {measured}]" if measured != '' else ''))

def ldiv(a, b):
    """Lean's division on a field: x / 0 = 0."""
    return F(0) if b == 0 else F(a) / F(b)

def lpow(x, n):
    """Natural power, 0 ^ 0 = 1."""
    return F(x) ** n

# ---------------------------------------------------------------- item 84
def hit_first_iid(p, a, b, N):
    """Chance that the iid +-1 walk (up with chance p) reaches a before -b within N steps, and the
    mass not yet stopped; with the event of the Lean statement: some n with walk n = a and every
    walk k > -b for k <= n."""
    if b == 0:
        return F(0), F(0)        # -0 < walk 0 = 0 fails at k = 0
    if a == 0:
        return F(1), F(0)        # n = 0
    dist = {0: F(1)}
    hit = F(0)
    for _ in range(N):
        nd = {}
        for x, m in dist.items():
            for step, pr in ((1, p), (-1, 1 - p)):
                y = x + step
                if pr == 0:
                    continue
                if y == a:
                    hit += m * pr
                elif y == -b:
                    pass
                else:
                    nd[y] = nd.get(y, F(0)) + m * pr
        dist = nd
    return hit, sum(dist.values(), F(0))

def formula_hit(p, a, b):
    r = ldiv(1 - p, p)
    return ldiv(lpow(r, b) - 1, lpow(r, a + b) - 1)

# the formula solves the boundary problem exactly (start x, -b <= x <= a)
ok = True
for p in (F(1, 3), F(1, 5), F(2, 3), F(3, 4), F(9, 10)):
    r = (1 - p) / p
    for a in range(0, 5):
        for b in range(1, 5):
            h = lambda x: (r ** (x + b) - 1) / (r ** (a + b) - 1)
            ok &= h(-b) == 0 and h(a) == 1
            ok &= all(h(x) == p * h(x + 1) + (1 - p) * h(x - 1) for x in range(-b + 1, a))
check('84.formula', ok, 'h(x) = (r^(x+b) - 1)/(r^(a+b) - 1) solves h = p h(x+1) + q h(x-1), h(-b) = 0, h(a) = 1, p in {1/3, 1/5, 2/3, 3/4, 9/10}')

ok = True; worst = None
for p in (F(1, 3), F(2, 3), F(1, 4)):
    for a in range(0, 4):
        for b in range(0, 4):
            hit, rest = hit_first_iid(p, a, b, 120)
            f = formula_hit(p, a, b)
            good = hit <= f <= hit + rest
            ok &= good
            if not good:
                worst = (p, a, b, float(hit), float(f))
check('84.law', ok, 'stopped at step 120, the chance of a first is within the unstopped mass of the formula (a, b in 0..3, Lean conventions at a = 0 or b = 0)', worst or '')

# (b) hp0: p = 0, a = b = 1: Lean's r = 1/0 = 0, formula (0 - 1)/(0 - 1) = 1, true chance 0
hit, rest = hit_first_iid(F(0), 1, 1, 10)
check('84b.p_pos', formula_hit(F(0), 1, 1) == 1 and hit == 0 and rest == 0,
      'p = 0, a = b = 1: formula (Lean r = 1/0 = 0) is 1, the walk falls to -1 first: chance 0', (formula_hit(F(0), 1, 1), hit))
# (b) p < 1 not needed: at p = 1, r = 0, formula equals the true chance for a, b in 0..3
ok = all(formula_hit(F(1), a, b) == hit_first_iid(F(1), a, b, 10)[0] for a in range(4) for b in range(4))
check('84b.p_lt_one', ok, 'p = 1 (r = 0, Lean 0^0 = 1): formula equals the true chance for a, b in 0..3; the hypothesis is kept for the proof')
# (b) p != 1/2: r = 1, formula 0/0 = 0 against b/(a+b) = 1/2
hit, rest = hit_first_iid(F(1, 2), 1, 1, 200)
check('84b.p_ne_half', formula_hit(F(1, 2), 1, 1) == 0 and hit <= F(1, 2) <= hit + rest,
      'p = 1/2, a = b = 1: formula 0/0 = 0, true chance 1/2 (b/(a+b))', (formula_hit(F(1, 2), 1, 1), float(hit)))
# (b) hp: stated p = 1/3 but fair steps: formula (r = 2) 1/3 against 1/2
hit, rest = hit_first_iid(F(1, 2), 1, 1, 200)
check('84b.law', formula_hit(F(1, 3), 1, 1) == F(1, 3) and hit <= F(1, 2) <= hit + rest and hit > F(1, 3) + rest,
      'stated p = 1/3, fair steps, a = b = 1: formula 1/3 against chance 1/2', float(hit))
# (b) hpm: steps +1 (chance 1/3) or -2, a = 1, b = 2: hp holds with p = 1/3 (the step is 1 with
# chance 1/3); the walk reaches 1 before -2 only by a first step up: chance 1/3 against 3/7.
# (Steps never equal to 1, such as +-2, would force p = 0 through hp, against hp0: cold review r84.)
def hit_first_law(step_law, a, b, N):
    dist = {0: F(1)}; hit = F(0)
    for _ in range(N):
        nd = {}
        for x, m in dist.items():
            for st, pr in step_law:
                y = x + st
                if y == a:
                    hit += m * pr
                elif y > -b and y < a:
                    nd[y] = nd.get(y, F(0)) + m * pr
                # y <= -b: lost; y > a cannot happen from below with steps +1
        dist = nd
    return hit, sum(dist.values(), F(0))
law_b = [(1, F(1, 3)), (-2, F(2, 3))]
hit, rest = hit_first_law(law_b, 1, 2, 10)
check('84b.pm', sum(pr for st, pr in law_b if st == 1) == F(1, 3) and formula_hit(F(1, 3), 1, 2) == F(3, 7)
      and hit == F(1, 3) and rest == 0,
      'steps +1 (chance 1/3, so hp holds with p = 1/3) or -2, a = 1, b = 2: chance 1/3 against the formula 3/7', hit)
# (b) hind / hX: X n = X 0 for every n, up chance 1/3, a = 1, b = 2: chance 1/3 against 3/7
def first_hit_path(steps, a, b):
    x = 0
    for st in steps:
        x += st
        if x == a:
            return True
        if x <= -b:
            return False
    return None
chance = sum(pr for x0, pr in ((1, F(1, 3)), (-1, F(2, 3))) if first_hit_path([x0] * 10, 1, 2))
check('84b.indep', formula_hit(F(1, 3), 1, 2) == F(3, 7) and chance == F(1, 3),
      'X n = X 0 (up with chance 1/3), a = 1, b = 2: hits 1 first iff X 0 = 1, chance 1/3, formula (r = 2) 3/7; with the filtration that knows nothing, the same steps break only hX')

# (a) the four rows: the walk never leaves (-b, a), checked by a repeating state
def stays(steps_of, a, b, period, N=40):
    x = 0
    seen = set()
    for n in range(N):
        if x >= a or x <= -b:
            return False
        seen.add((x, n % period))
        x += steps_of(n)
    return x < a and x > -b
check('84a.law', stays(lambda n: 1 if n % 2 == 0 else -1, 2, 1, 2),
      'steps +1, -1, +1, ... (deterministic, so independent; each step a single law fails): walk 0, 1, 0, ... never leaves (-1, 2)')
check('84a.pm', stays(lambda n: 0, 1, 1, 1), 'steps 0 (p = 0 meets hp): the walk stays at 0, never leaves (-1, 1)')
check('84a.indep', stays(lambda n: (-1) ** n, 2, 2, 2) and stays(lambda n: -((-1) ** n), 2, 2, 2),
      'X n = (-1)^n X 0, X 0 fair (each step fair, not independent; or independent of the filtration that knows nothing, breaking hX): walk in {0, X 0}, never leaves (-2, 2)')

# (c) Ville: chance of ever reaching a, iid steps, p < q, bounded at every horizon by (p/q)^a
def reach_within(step_law, a, N):
    """Chance that the walk with iid steps (list of (step, chance)) is >= a at some n <= N."""
    if a <= 0:
        return F(1)
    dist = {0: F(1)}
    hit = F(0)
    for _ in range(N):
        nd = {}
        for x, m in dist.items():
            for s, pr in step_law:
                y = x + s
                if y >= a:
                    hit += m * pr
                else:
                    nd[y] = nd.get(y, F(0)) + m * pr
        dist = nd
    return hit
ok = True
for p in (F(1, 3), F(1, 4), F(2, 5)):
    for a in range(0, 4):
        ok &= reach_within([(1, p), (-1, 1 - p)], a, 60) <= (p / (1 - p)) ** a
check('84c.bound', ok, 'iid steps, p in {1/3, 1/4, 2/5}, a in 0..3: chance of reaching a within 60 steps <= (p/(1-p))^a')
# hp0 not needed: p = 0, the walk only falls
check('84c.p_pos', all(reach_within([(-1, F(1))], a, 20) <= lpow(ldiv(0, 1), a) for a in range(4)),
      'p = 0: chance 1 at a = 0 (bound 0^0 = 1), 0 for a >= 1 (bound 0): holds; kept for the proof (r = q/p)')
# hpq: for 1/2 <= p < 1 the bound is >= 1; p = 1: Lean's p/(1-p) = 1/0 = 0, bound 0, chance 1
ok = all(lpow(ldiv(p, 1 - p), a) >= 1 for p in (F(1, 2), F(2, 3), F(9, 10)) for a in range(5))
check('84c.p_lt_q', ok and reach_within([(1, F(1))], 1, 5) == 1 and lpow(ldiv(F(1), 0), 1) == 0,
      'dropping p < q: for 1/2 <= p < 1 the bound is at least 1 (true); at p = 1, a = 1 the bound is Lean 1/0 = 0, the chance 1')
# hp: fair steps with stated p = 1/3: chance of reaching 1 within 3 steps 5/8 > 1/2
check('84c.law', reach_within([(1, F(1, 2)), (-1, F(1, 2))], 1, 3) == F(5, 8) > F(1, 2),
      'stated p = 1/3, fair steps, a = 1: chance within 3 steps 5/8 > (1/2)^1')
# hpm: steps +1 (chance 1/3, so hp holds with p = 1/3 < 2/3) or +2: the walk reaches 1 at the first
# step: chance 1 > (1/2)^1. (Steps never equal to 1 would force p = 0 against hp0: cold review r84.)
law_c = [(1, F(1, 3)), (2, F(2, 3))]
v = reach_within(law_c, 1, 1)
check('84c.pm', sum(pr for st, pr in law_c if st == 1) == F(1, 3) and v == 1 > F(1, 2),
      'steps +1 (chance 1/3, hp holds) or +2, a = 1: chance 1 > (1/2)^1', v)
# hind / hX: three paths of mass 1/3; each step is +1 on exactly one of them
paths = {'A': [1] + [-1, -1] + [1] * 5, 'B': [-1, 1, 1] + [-1] * 5, 'C': [-1] * 8}
marg = all(sum(F(1, 3) for w in paths.values() if w[n] == 1) == F(1, 3) for n in range(8))
reach = sum(F(1, 3) for w in paths.values() if any(sum(w[:n + 1]) >= 1 for n in range(8)))
check('84c.indep', marg and reach == F(2, 3) > F(1, 2),
      'dependent steps, each +1 with chance 1/3 (paths +1-1-1+1..., -1+1+1-1..., -1-1-1...): reaches 1 with chance 2/3 > 1/2; with the filtration that knows nothing, the same steps break only hX', reach)

# ---------------------------------------------------------------- item 85
ok = True
random.seed(85)
for _ in range(200):
    rows, cols = random.randint(1, 4), random.randint(1, 4)
    A = [[F(random.randint(-9, 9), random.randint(1, 5)) for _ in range(cols)] for _ in range(rows)]
    if random.random() < 0.1:
        A = [[F(0)] * cols for _ in range(rows)]
    S = sum(abs(v) for row in A for v in row)
    m, M = -S, S
    Ap = [[ldiv(v - m, M - m) for v in row] for row in A]
    ok &= all(0 <= v <= 1 for row in Ap for v in row)
    x = [F(random.randint(0, 5)) for _ in range(rows)]; x = [v / sum(x) for v in x] if sum(x) else [F(1, rows)] * rows
    y = [F(random.randint(0, 5)) for _ in range(cols)]; y = [v / sum(y) for v in y] if sum(y) else [F(1, cols)] * cols
    pay = lambda B: sum(x[i] * B[i][j] * y[j] for i in range(rows) for j in range(cols))
    ok &= pay(A) == m + (M - m) * pay(Ap)
check('85.affine', ok, '200 random rational matrices (10% zero): entries of (A - m)/(M - m) in [0, 1] and payoff A = m + (M - m) payoff A\' on strategies, the zero matrix included (Lean 0/0 = 0)')

# ---------------------------------------------------------------- item 86
def walk_prod(r, L):
    out = F(1)
    for u, v in zip(L, L[1:]):
        out *= r[u][v]
    return out
def cycle_prod(r, c):
    return walk_prod(r, list(c) + list(c[:1]))
def cycles(n, maxlen):
    for k in range(1, maxlen + 1):
        yield from itertools.product(range(n), repeat=k)
r1 = [[F(1), F(0)], [F(2), F(1)]]
check('86.A1', all(cycle_prod(r1, c) <= 1 for c in cycles(2, 8)) and cycle_prod(r1, (0, 1)) == 0
      and all(r1[i][j] * [1, 2][j] <= [1, 2][i] for i in range(2) for j in range(2)),
      'A1, rates (1, 0; 2, 1): every cycle up to length 8 has product <= 1, prices (1, 2) hold; cycle [0, 1] has product 0 and weight -log 0 - log 2 = -log 2 < 0 with Lean\'s log 0 = 0')
r2 = [[F(1), F(-2)], [F(-2), F(1)]]
check('86.A2', all(r2[i][j] * 1 <= 1 for i in range(2) for j in range(2)) and cycle_prod(r2, (0, 1)) == 4,
      'A2, rates (1, -2; -2, 1): p = (1, 1) are prices, cycle [0, 1] has product 4 > 1')
w = [[F(0), F(-1), F(5)], [F(5), F(0), F(-1)], [F(5), F(5), F(0)]]
def bf(w, k):
    d = [F(0)] * len(w)
    for _ in range(k):
        d = [min(d[j], min(d[i] + w[i][j] for i in range(len(w)))) for j in range(len(w))]
    return d
csum = lambda c: sum(w[u][v] for u, v in zip(list(c) + list(c[:1]), (list(c) + list(c[:1]))[1:]))
check('86.A3', bf(w, 1) == [0, -1, -1] and bf(w, 2) == [0, -1, -2] and bf(w, 3) == bf(w, 2)
      and all(csum(c) >= 0 for c in cycles(3, 6)),
      'A3: rounds (0, -1, -1), (0, -1, -2), round 3 = round 2; every cycle up to length 6 has weight >= 0', (bf(w, 1), bf(w, 2)))

# ---------------------------------------------------------------- item 88
def e_num_rej(q, e):
    m = len(e)
    best = 0
    for k in range(0, m + 1):
        thr = ldiv(m, q * k)
        if k <= sum(1 for v in e if v >= thr):
            best = k
    return best
def e_false_share(q, H, e):
    m, R = len(e), e_num_rej(q, e)
    rej = {j for j in range(m) if R >= 1 and ldiv(m, q * R) <= e[j]}
    return ldiv(len(set(H) & rej), R)
def mean_share(q, H, outcomes):
    """outcomes: list of (chance, scores)."""
    return sum(pr * e_false_share(q, H, e) for pr, e in outcomes)
def score(L, mass):
    return ldiv(F(1, 2) ** L, mass)
def kraft(words):
    return sum(F(1, 2) ** len(wd) for wd in words)
strings2 = list(itertools.product((0, 1), repeat=2))
# q = 0: one string of length 0, score 1
v = mean_share(F(0), [0], [(F(1), [score(0, F(1))])])
check('88.q_pos', v == 1, 'q = 0, strings of length 0 (score 1): e-BH threshold Lean 1/(0 * 1) = 0, always rejected: mean false share 1 > 0', v)
# injective dropped: every string of length 2 -> [], fair coin, q = 1/4
v = mean_share(F(1, 4), [0], [(F(1, 4), [score(0, F(1, 4))]) for _ in strings2])
check('88.injective', v == 1 > F(1, 4) and kraft([()] * 4) == 4,
      'every string of length 2 sent to [] (prefix-free image {[]}, not injective), fair coin, q = 1/4: scores 4, always rejected, 1 > 1/4', v)
# prefix-free dropped: words [], [0], [1], [0, 0]
words = [(), (0,), (1,), (0, 0)]
v = mean_share(F(1, 2), [0], [(F(1, 4), [score(len(wd), F(1, 4))]) for wd in words])
check('88.prefix_free', v == F(3, 4) > F(1, 2) and kraft(words) == F(9, 4),
      'words [], [0], [1], [0, 0] (injective, not prefix-free, Kraft sum 9/4), fair coin, q = 1/2: scores 4, 2, 2, 1, mean false share 3/4 > 1/2', v)
# law dropped: the string is always [true], null law win rate 1/8, code x -> [x 0], q = 1/4
v = mean_share(F(1, 4), [0], [(F(1), [score(1, F(1, 8))])])
check('88.law', v == 1 > F(1, 4), 'the string is always (true), null law win rate 1/8, code x -> [x 0], q = 1/4: score (1/2)/(1/8) = 4, always rejected, 1 > 1/4', v)
# a probability measure (the expected share), needed through Lean's junk law of a string that is not
# almost everywhere measurable (a point mass, Measure.map_of_not_aemeasurable_of_ne_zero): sigma-algebra
# bot on Bool, mu = 5 * dirac true, two nulls with codes x -> [x 0] whose strings hit the point mass
# on complementary sets, so their scores are (1/2, 0) at true and (0, 1/2) at false; q = 4
v = mean_share(F(4), [0, 1], [(F(5), [F(1, 2), F(0)]), (F(0), [F(0), F(1, 2)])])
v1 = mean_share(F(4), [0, 1], [(F(1), [F(1, 2), F(0)]), (F(0), [F(0), F(1, 2)])])
check('88.prob_measure', v == 5 > F(4) * 2 / 2 and v1 == 1 <= F(4),
      'mass 5, two non-measurable nulls, scores (1/2, 0) and (0, 1/2), q = 4: one rejection, always a null: mean false share 5 > q |H| / m = q = 4; at mass 1 it is 1 <= 4', (v, v1))
# the satisfiability example: fair coin, one bit, code x -> [x 0], q = 1/2: scores 1, never rejected
v = mean_share(F(1, 2), [0], [(F(1, 2), [score(1, F(1, 2))]) for _ in range(2)])
check('88.example', v == 0, 'the example: one fair bit, code x -> [x 0], q = 1/2: every score 1, threshold 2, never rejected: 0 <= 1/2', v)
# sanity: two null tests reading the same two fair bits with a Kraft-tight code, and one non-null
code = {(0, 0): (0,), (0, 1): (1, 0), (1, 0): (1, 1, 0), (1, 1): (1, 1, 1)}
outs = [(F(1, 4), [score(len(code[s]), F(1, 4)), score(len(code[s]), F(1, 4)), F(10)]) for s in strings2]
ok = all(mean_share(q, [0, 1], outs) <= q * 2 / 3 for q in (F(1, 10), F(1, 4), F(1, 2), F(9, 10)))
check('88.sanity', ok and kraft(code.values()) == 1,
      'two null tests on the same two fair bits (code [0], [1,0], [1,1,0], [1,1,1]) and one non-null test with score 10: mean false share <= q * 2 / 3 for q in {1/10, 1/4, 1/2, 9/10}')

# ---------------------------------------------------------------- item 80b, the example
# two points of mass one, X 0 = X 1 = the indicator of `true`, gamma = 1, k = 2
mu = {True: F(1), False: F(1)}
X = {True: F(1), False: F(0)}
integ = lambda f: sum(mu[w_] * f(w_) for w_ in mu)
Ssum = lambda w_: 2 * X[w_]
mean = integ(Ssum)
var = integ(lambda w_: (Ssum(w_) - mean) ** 2)
cov = integ(lambda w_: (X[w_] - integ(lambda u: X[u])) ** 2)
prod = 2 * F(1) * (1 + 2 * sum((1 - ldiv(j, 2)) * ldiv(F(1), F(1)) for j in range(1, 2)))
check('80b.example', cov == 1 and var == 4 == prod,
      'the module\'s example (two points of mass one, X = indicator, gamma = 1, k = 2): every covariance 1, Var = 4 = 2 * 1 * (1 + 2 * (1/2) * 1)', (cov, var, prod))

hits = sum(RESULTS)
print(f'== {hits} of {len(RESULTS)} checks hit' + ('' if hits == len(RESULTS) else ' -- SOME MISS'))
print('ALL OK' if hits == len(RESULTS) else 'SOME MISS')
sys.exit(0 if hits == len(RESULTS) else 1)
