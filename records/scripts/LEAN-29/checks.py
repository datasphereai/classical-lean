#!/usr/bin/env python3
"""Exact checks for order LEAN-29 (items 91 to 95 of MATH-PLAN-library-2.md), written by
claude-ai on 2026-10-14 before its first run. Standard library only. Run with `python3 -I`.

Every check prints one line, HIT (the prediction below held) or MISS, then what it measured.
Cases worked by hand, which this script cannot compute, print one line starting BY HAND; they
are not counted. The last line counts the checks; the exit code is 0 only if every check hits.
Arithmetic is exact (fractions.Fraction) under Lean's conventions: x / 0 = 0, n / 0 = 0 and
n / r rounding down in ℕ, q ^ 0 = 1. The one exception is the exponential in item 91: `exp`
is computed with decimal.Decimal at 60 significant digits, and a comparison counts only with a
margin above 10^-40, or as an exact equality when the exponent is exactly 0 (both sides are
then 1).

Predictions, written before the first run (revision 2, after cold review 1, changed only the
lines marked r2; its prediction: 23 checks, all HIT, and BY HAND lines; the count of those was
first written as 4 and the run printed 3, 91.drop.hA, 92.drop.meas and 92.drop.fmeas, which is
right: claude-ai's miss in writing the prediction):

Item 91 (`measureReal_no_run_le_exp`, LongestRun). Grid: n = 0..10, r = 0..4, q in
{0, 1/10, 1/3, 1/2, 9/10, 1}; the chance of no run of r losses among n independent trials is
computed exactly (r = 0: the run event is everything, chance of no run 0; r > n: chance 1).
  91.grid      every cell: chance <= (1 - q^r)^(n / r) <= exp(-(n / r) q^r), 330 cells.
               (The first run predicted 396 cells, a miss of claude-ai's arithmetic:
               11 values of n, 5 of r, 6 of q make 330. The bounds held in every cell.)
  91.drop.hind the trials all one event of chance q (not independent): first failing cell, with
               n = 1..10, r = 1..4, q in (1/10, 1/3, 1/2, 9/10) in that nesting order, is
               (n, r, q) = (2, 1, 1/10): chance 9/10 against exp(-1/5) < 0.82.
  91.drop.hq   every trial's event empty while q is stated: first failing cell (1, 1, 1/10):
               chance 1 against exp(-1/10) < 1.
  91.drop.hA   BY HAND (order LEAN-28's case, not computed): Bool with the sigma-algebra
               {empty, univ}, the point mass at true, A 0 = {true}, n = r = 1, q = 1: Lean's
               P.real of the non-measurable complement is its outer measure 1, against
               exp(-1) < 0.37. Printed with exp(-1), not counted (r2).

Item 92 (`abs_covariance_le_mul_div_four`, `abs_average_mul_sub_le`, new module).
  92.prob      200 random finite laws (2 to 5 atoms, exact rational masses and values, bounds
               at or beyond the extremes): |cov| <= (M - m)(N - n)/4, every case.
  92.equal     X = Y, fair on {m, M}: cov equals the bound exactly, for 3 choices of (m, M).
  92.drop.prob a measure that is not a probability measure, one point: masses c in (0, 1/2, 2)
               with X = Y = 1. Mass 0 makes the bound hypotheses empty, so m = 1, M = 0, n = 0,
               N = 1 are allowed: cov 0 against -1/4. Masses 1/2 and 2 with m = M = n = N = 1:
               Lean's cov is c (1 - c)^2, 1/8 and 2, against 0. First failing cell: mass 0;
               all three fail.
  92.drop.bnd  X = Y fair on {-1, 1}, X's bounds claimed m = M = 0, Y's n = -1, N = 1: cov 1
               against 0.
  92.drop.meas BY HAND, not computed: Bool with {empty, univ}, the point mass at true, X = 1 at
               true and 2 at false, Y = 2 / X. Neither is a.e. measurable, so Lean's integrals of
               X and of Y are 0, while X Y = 2 is measurable: cov 2 against (1)(1)/4. Printed,
               not counted (r2). With one of X, Y measurable no case exists (cold review 1's
               argument, by hand): the two hypotheses are needed together.
  92.drop.fmeas BY HAND (r2, cold review 1): on [0, 1], f = 1 + (indicator of V), V a subset of
               (1/2, 1] that is not Lebesgue measurable, g = indicator of [0, 1/2]: Lean's
               integral of f is 0, of f g 1/2, of g 1/2; left side 1/2 against
               (2 - 1)(1 - 0)/4 = 1/4. So f's integrability is needed alone (and g's likewise).
               Printed, not counted.
  92.fun       200 random step functions f, g on random [a, b], a < b (2 to 6 equal pieces,
               bounds at or beyond the extremes): |avg(f g) - avg f avg g| <= (M - m)(N - n)/4;
               and f = g = x on [0, 1]: 1/12 <= 1/4.
  92.drop.hab  a = 1, b = 0 (the interval [1, 0] is empty, so the bound hypotheses hold for any
               m, M): f = g = 0, m = 1, M = 0, n = 0, N = 1: left side 0 against -1/4, fails.
               And a = b = 0: every interval integral over [a, a] is 0, so the left side is 0
               whatever 0⁻¹ is, and the bound is at least 0 (the hypotheses at x = a give
               m <= M, n <= N): holds (r2: the reason reworded).
  92.drop.fbnd f = g = x on [0, 1], f's bounds claimed m = M = 0, g's n = 0, N = 1: the left side,
               computed by exact integration of polynomials, is 1/3 - 1/4 = 1/12, against
               (0 - 0)(1 - 0)/4 = 0 (r2: computed, not a constant).

Item 93 (`simpson_eq_trapezoidal`, Simpson). The library's `simpson f N a b` and Mathlib's
`trapezoidal_integral f N a b`, each computed as defined (pinned Mathlib,
MeasureTheory/Integral/IntervalIntegral/TrapezoidalRule.lean line 41), with f given random values
at every node: simpson = (4 T(2N) - T(N))/3 exactly, N = 0..8, 40 random (a, b) per N including
a > b and a = b: 360 cases, every one equal.

Item 94 (`tendsto_implicitEuler`, `tendsto_explicitEuler_iff`, EulerMethod). The explicit
iterate is computed by the library's `eulerIterate` recursion with f t y = -c y and compared
with (1 - h c)^k y0 for k <= 12. A geometric sequence s0 φ^k tends to 0 exactly when s0 = 0 or
|φ| < 1 (Mathlib's `tendsto_pow_atTop_nhds_zero_iff`); that is the criterion used.
  94.closed    the closed form, every cell of c, h in (1/10, 1/2, 1, 3/2, 2, 5/2, 4), y0 in
               (-2, 1, 3), t0 in (0, 1/3).
  94.explicit  for c, h > 0 and y0 != 0 in that grid: tends to 0 iff h c < 2, every cell.
  94.implicit  for c, h > 0: the factor 1/(1 + h c) lies in (0, 1), every cell.
  94.drop.ehc  explicit, c in (-1, 0, 1/2, 1), h in (-1, 0, 1/2, 1, 3), y0 in (0, 1), c > 0
               dropped: first failing cell (c, h, y0) = (-1, 1/2, 1).
  94.drop.ehh  h > 0 dropped: first failing cell (1/2, -1, 1).
  94.drop.ey0  y0 != 0 dropped: first failing cell (1, 3, 0).
  94.drop.ihc  implicit, c in (-1, -1/2, 0, 1/2, 1), h in (1/2, 1, 2), c > 0 dropped: first
               failing cell (c, h) = (-1, 1/2) (factor 2); the cell (-1, 1) holds by Lean's
               1/0 = 0 (factor 0).
  94.drop.ihh  h in (-1, -1/2, 0, 1/2), c in (1/2, 1, 2), h > 0 dropped: first failing cell
               (h, c) = (-1, 1/2); the cell (-1, 1) holds by 1/0 = 0.

Item 95 (`measureReal_hit_eq_lucasU`, GamblersRuin). The chance that the ±1 walk from 0 with
up-chance p reaches a before -b, read as Lean's event {∃ n, walk n = a ∧ ∀ k <= n, -b < walk k}
(b = 0: empty; a = 0 < b: everything), solved exactly; U = lucasU (1 + r) r, r = (1 - p)/p.
  95.grid      p in (1/10, 1/3, 2/5, 1/2, 3/5, 3/4, 9/10), a, b = 0..5: chance = U b / U (a + b),
               every cell, p = 1/2 included (U n = n there).
  95.item84    for p != 1/2 in that grid, U b / U (a + b) equals item 84's
               (r^b - 1)/(r^(a+b) - 1), every cell; at p = 1/2 item 84's form is Lean's 0/0 = 0,
               and the first cell where it differs, a outer, is (a, b) = (0, 1).
  95.p1        p = 1 (r = 0): the formula is right in every cell (p < 1 not needed).
  95.drop.hp0  p = 0 (r = Lean's 1/0 = 0): first failing cell, a outer, (a, b) = (1, 1):
               chance 0 against U 1 / U 2 = 1.
"""
import random, sys
from decimal import Decimal, getcontext
from fractions import Fraction as Fr

getcontext().prec = 60
RESULTS = []


def show(t):
    """A cell as plain text: Fractions as a/b."""
    if isinstance(t, tuple):
        return '(' + ', '.join(show(x) for x in t) + ')'
    return str(t)


def check(label, ok, measured):
    RESULTS.append(bool(ok))
    print(f"{'HIT ' if ok else 'MISS'} {label}: {measured}")


def by_hand(label, text):
    print(f'BY HAND {label}: {text}')


def ldiv(x, y):
    """Lean's division on a field: x / 0 = 0."""
    return Fr(0) if y == 0 else Fr(x) / Fr(y)


def dexp(x):
    """exp of a Fraction, as a Decimal at 60 digits."""
    return (Decimal(x.numerator) / Decimal(x.denominator)).exp()


def dec(x):
    return Decimal(x.numerator) / Decimal(x.denominator)


MARGIN = Decimal(10) ** -40


def le_exp(lhs, expo):
    """lhs <= exp(expo) for a Fraction lhs; exact when expo == 0."""
    if expo == 0:
        return lhs <= 1
    return dec(lhs) + MARGIN < dexp(expo)


# ------------------------------------------------------------------ item 91
def no_run_chance(n, r, q):
    """Chance that n independent trials, each lost with chance q, hold no r consecutive losses."""
    if r == 0:
        return Fr(0)
    # state: current run of losses, 0..r-1
    dist = {0: Fr(1)}
    for _ in range(n):
        new = {}
        for s, pr in dist.items():
            new[0] = new.get(0, Fr(0)) + pr * (1 - q)
            if s + 1 < r:
                new[s + 1] = new.get(s + 1, Fr(0)) + pr * q
        dist = new
    return sum(dist.values(), Fr(0))


def item91():
    qs = [Fr(0), Fr(1, 10), Fr(1, 3), Fr(1, 2), Fr(9, 10), Fr(1)]
    ok, cells = True, 0
    for n in range(0, 11):
        for r in range(0, 5):
            for q in qs:
                m = n // r if r else 0
                c = no_run_chance(n, r, q)
                mid = (1 - q ** r) ** m
                cells += 1
                if not (c <= mid and le_exp(mid, -m * q ** r) and le_exp(c, -m * q ** r)):
                    ok = False
    check('91.grid', ok and cells == 330, f'{cells} cells, all within both bounds: {ok}')
    qs4 = [Fr(1, 10), Fr(1, 3), Fr(1, 2), Fr(9, 10)]
    first = None
    for n in range(1, 11):
        for r in range(1, 5):
            for q in qs4:
                c = (1 - q) if n >= r else Fr(1)
                m = n // r
                if not le_exp(c, -m * q ** r):
                    first = first or (n, r, q)
    check('91.drop.hind', first == (2, 1, Fr(1, 10)),
          f'first failing cell {show(first)}; chance 9/10 vs exp(-1/5) = {dexp(Fr(-1, 5)):.6f}')
    first = None
    for n in range(1, 11):
        for r in range(1, 5):
            for q in qs4:
                if not le_exp(Fr(1), -(n // r) * q ** r):
                    first = first or (n, r, q)
    check('91.drop.hq', first == (1, 1, Fr(1, 10)),
          f'first failing cell {show(first)}; chance 1 vs exp(-1/10) = {dexp(Fr(-1, 10)):.6f}')
    by_hand('91.drop.hA', f'chance 1 (outer measure) vs exp(-1) = {dexp(Fr(-1)):.6f}')


# ------------------------------------------------------------------ item 92
def cov(ps, xs, ys):
    ex = sum(p * x for p, x in zip(ps, xs))
    ey = sum(p * y for p, y in zip(ps, ys))
    return sum(p * (x - ex) * (y - ey) for p, x, y in zip(ps, xs, ys))


def rand_rat(rng, lo, hi, den=12):
    return Fr(rng.randint(lo * den, hi * den), den)


def item92(rng):
    ok = True
    for _ in range(200):
        k = rng.randint(2, 5)
        w = [rng.randint(1, 9) for _ in range(k)]
        ps = [Fr(x, sum(w)) for x in w]
        xs = [rand_rat(rng, -3, 3) for _ in range(k)]
        ys = [rand_rat(rng, -3, 3) for _ in range(k)]
        m, M = min(xs) - rand_rat(rng, 0, 1), max(xs) + rand_rat(rng, 0, 1)
        n, N = min(ys) - rand_rat(rng, 0, 1), max(ys) + rand_rat(rng, 0, 1)
        if abs(cov(ps, xs, ys)) > (M - m) * (N - n) / 4:
            ok = False
    check('92.prob', ok, '200 random finite laws: |cov| <= (M - m)(N - n)/4')
    eq = all(cov([Fr(1, 2)] * 2, [m, M], [m, M]) == (M - m) ** 2 / 4
             for m, M in [(Fr(0), Fr(1)), (Fr(-2), Fr(3)), (Fr(1, 3), Fr(1, 2))])
    check('92.equal', eq, 'X = Y fair on {m, M}: cov equals the bound, 3 cases')
    fails = []
    for c in [Fr(0), Fr(1, 2), Fr(2)]:
        x = y = Fr(1)
        ex, ey = c * x, c * y  # Lean's integral of a constant against mass c
        cv = c * (x - ex) * (y - ey)
        m, M, n, N = (Fr(1), Fr(0), Fr(0), Fr(1)) if c == 0 else (Fr(1),) * 4
        if abs(cv) > (M - m) * (N - n) / 4:
            fails.append((c, cv, (M - m) * (N - n) / 4))
    check('92.drop.prob', [f[0] for f in fails] == [0, Fr(1, 2), 2],
          f'failing masses (mass, cov, bound): {[(str(a), str(b), str(d)) for a, b, d in fails]}')
    cv = cov([Fr(1, 2)] * 2, [Fr(-1), Fr(1)], [Fr(-1), Fr(1)])
    check('92.drop.bnd', cv > 0, f'cov {cv} against (0 - 0)(1 - (-1))/4 = 0')
    by_hand('92.drop.meas', 'Lean cov 2 against 1/4; with one of X, Y measurable, no case')
    by_hand('92.drop.fmeas', 'f = 1 + 1_V, g = 1_[0,1/2] on [0, 1]: 1/2 against 1/4')
    ok = True
    for _ in range(200):
        a = rand_rat(rng, -3, 3)
        b = a + rand_rat(rng, 1, 4)
        k = rng.randint(2, 6)
        fv = [rand_rat(rng, -3, 3) for _ in range(k)]
        gv = [rand_rat(rng, -3, 3) for _ in range(k)]
        wid = (b - a) / k
        inv = 1 / (b - a)
        afg = inv * sum(wid * f * g for f, g in zip(fv, gv))
        af = inv * sum(wid * f for f in fv)
        ag = inv * sum(wid * g for g in gv)
        m, M = min(fv) - rand_rat(rng, 0, 1), max(fv) + rand_rat(rng, 0, 1)
        n, N = min(gv) - rand_rat(rng, 0, 1), max(gv) + rand_rat(rng, 0, 1)
        if abs(afg - af * ag) > (M - m) * (N - n) / 4:
            ok = False
    lin = Fr(1, 3) - Fr(1, 2) * Fr(1, 2)
    check('92.fun', ok and lin == Fr(1, 12) and lin <= Fr(1, 4),
          f'200 random step functions; f = g = x on [0, 1]: {lin} <= 1/4')
    # a = 1, b = 0: Lean's (b - a)⁻¹ = -1 and every interval integral of 0 is 0
    lhs = abs(ldiv(1, -1) * 0 - (ldiv(1, -1) * 0) * (ldiv(1, -1) * 0))
    bound_fail = lhs > (Fr(0) - 1) * (Fr(1) - 0) / 4
    lhs0 = abs(ldiv(1, 0) * 0 - (ldiv(1, 0) * 0) * (ldiv(1, 0) * 0))
    check('92.drop.hab', bound_fail and lhs0 == 0,
          f'a = 1, b = 0: {lhs} against -1/4 fails; a = b = 0: left side {lhs0}, holds')

    def poly_int(coeffs, a, b):
        # exact integral over [a, b] of sum coeffs[k] x^k
        return sum(c * (Fr(b) ** (k + 1) - Fr(a) ** (k + 1)) / (k + 1) for k, c in enumerate(coeffs))
    avg_fg = poly_int([0, 0, 1], 0, 1)
    avg_f = poly_int([0, 1], 0, 1)
    lhs = abs(avg_fg - avg_f * avg_f)
    bound = (Fr(0) - 0) * (Fr(1) - 0) / 4
    check('92.drop.fbnd', lhs == Fr(1, 12) and lhs > bound,
          f'f = g = x on [0, 1], m = M = 0, n = 0, N = 1: {lhs} against {bound}')


# ------------------------------------------------------------------ item 93
def simpson(f, N, a, b):
    h = ldiv(b - a, 2 * N)
    return ldiv(h, 3) * sum((f(a + 2 * k * h) + 4 * f(a + (2 * k + 1) * h) + f(a + (2 * k + 2) * h)
                             for k in range(N)), Fr(0))


def trapezoidal(f, N, a, b):
    return ldiv(b - a, N) * ((f(a) + f(b)) / 2 +
                             sum((f(a + ldiv((k + 1) * (b - a), N)) for k in range(max(N - 1, 0))),
                                 Fr(0)))


def item93(rng):
    ok, cases = True, 0
    for N in range(0, 9):
        for i in range(40):
            if i == 0:
                a = b = rand_rat(rng, -3, 3)
            else:
                a, b = rand_rat(rng, -3, 3), rand_rat(rng, -3, 3)
            vals = {}

            def f(x):
                if x not in vals:
                    vals[x] = rand_rat(rng, -5, 5)
                return vals[x]
            lhs = simpson(f, N, a, b)
            rhs = (4 * trapezoidal(f, 2 * N, a, b) - trapezoidal(f, N, a, b)) / 3
            cases += 1
            if lhs != rhs:
                ok = False
    check('93.richardson', ok and cases == 360, f'{cases} cases, simpson = (4 T(2N) - T(N))/3: {ok}')


# ------------------------------------------------------------------ item 94
def euler_iterate(f, t0, h, y0, k):
    u = y0
    for j in range(k):
        u = u + h * f(t0 + j * h, u)
    return u


def tends_geom(s0, phi):
    return s0 == 0 or abs(phi) < 1


def item94():
    grid = [Fr(1, 10), Fr(1, 2), Fr(1), Fr(3, 2), Fr(2), Fr(5, 2), Fr(4)]
    ok = True
    for c in grid:
        for h in grid:
            for y0 in [Fr(-2), Fr(1), Fr(3)]:
                for t0 in [Fr(0), Fr(1, 3)]:
                    for k in range(13):
                        if euler_iterate(lambda t, y: -c * y, t0, h, y0, k) != (1 - h * c) ** k * y0:
                            ok = False
    check('94.closed', ok, 'eulerIterate (fun _ y => -c y) t0 h y0 k = (1 - h c)^k y0, k <= 12')
    ok = all(tends_geom(y0, 1 - h * c) == (h * c < 2)
             for c in grid for h in grid for y0 in [Fr(-2), Fr(1), Fr(3)])
    check('94.explicit', ok, 'c, h > 0, y0 != 0: tends to 0 iff h c < 2')
    ok = all(0 < ldiv(1, 1 + h * c) < 1 for c in grid for h in grid)
    check('94.implicit', ok, 'c, h > 0: 0 < 1/(1 + h c) < 1')
    cs, hs = [Fr(-1), Fr(0), Fr(1, 2), Fr(1)], [Fr(-1), Fr(0), Fr(1, 2), Fr(1), Fr(3)]

    def first(pred):
        for c in cs:
            for h in hs:
                for y0 in [Fr(0), Fr(1)]:
                    if pred(c, h, y0) and tends_geom(y0, 1 - h * c) != (h * c < 2):
                        return (c, h, y0)
    r1 = first(lambda c, h, y0: h > 0 and y0 != 0)
    check('94.drop.ehc', r1 == (Fr(-1), Fr(1, 2), Fr(1)), f'c > 0 dropped: first failing {show(r1)}')
    r2 = first(lambda c, h, y0: c > 0 and y0 != 0)
    check('94.drop.ehh', r2 == (Fr(1, 2), Fr(-1), Fr(1)), f'h > 0 dropped: first failing {show(r2)}')
    r3 = first(lambda c, h, y0: c > 0 and h > 0)
    check('94.drop.ey0', r3 == (Fr(1), Fr(3), Fr(0)), f'y0 != 0 dropped: first failing {show(r3)}')
    f1 = next(((c, h) for c in [Fr(-1), Fr(-1, 2), Fr(0), Fr(1, 2), Fr(1)]
               for h in [Fr(1, 2), Fr(1), Fr(2)] if not tends_geom(1, ldiv(1, 1 + h * c))), None)
    junk1 = tends_geom(1, ldiv(1, 1 + Fr(1) * Fr(-1)))
    check('94.drop.ihc', f1 == (Fr(-1), Fr(1, 2)) and junk1,
          f'c > 0 dropped: first failing (c, h) = {show(f1)}; (c, h) = (-1, 1) holds by 1/0 = 0: {junk1}')
    f2 = next(((h, c) for h in [Fr(-1), Fr(-1, 2), Fr(0), Fr(1, 2)]
               for c in [Fr(1, 2), Fr(1), Fr(2)] if not tends_geom(1, ldiv(1, 1 + h * c))), None)
    junk2 = tends_geom(1, ldiv(1, 1 + Fr(-1) * Fr(1)))
    check('94.drop.ihh', f2 == (Fr(-1), Fr(1, 2)) and junk2,
          f'h > 0 dropped: first failing (h, c) = {show(f2)}; (h, c) = (-1, 1) holds by 1/0 = 0: {junk2}')


# ------------------------------------------------------------------ item 95
def lucasU(P, Q, n):
    u0, u1 = Fr(0), Fr(1)
    if n == 0:
        return u0
    for _ in range(n - 1):
        u0, u1 = u1, P * u1 - Q * u0
    return u1


def solve(A, rhs):
    n = len(rhs)
    M = [row[:] + [v] for row, v in zip(A, rhs)]
    for col in range(n):
        piv = next(i for i in range(col, n) if M[i][col] != 0)
        M[col], M[piv] = M[piv], M[col]
        for i in range(n):
            if i != col and M[i][col] != 0:
                fac = M[i][col] / M[col][col]
                M[i] = [x - fac * y for x, y in zip(M[i], M[col])]
    return [M[i][n] / M[i][i] for i in range(n)]


def hit_chance(p, a, b):
    """Lean's event {∃ n, walk n = a ∧ ∀ k <= n, -b < walk k}, for the walk from 0."""
    if b == 0:
        return Fr(0)
    if a == 0:
        return Fr(1)
    if p == 0:
        return Fr(0)
    if p == 1:
        return Fr(1)
    xs = list(range(-b + 1, a))  # interior states
    idx = {x: i for i, x in enumerate(xs)}
    A = [[Fr(0)] * len(xs) for _ in xs]
    rhs = [Fr(0)] * len(xs)
    for x in xs:
        i = idx[x]
        A[i][i] = Fr(1)
        for y, w in ((x + 1, p), (x - 1, 1 - p)):
            if y == a:
                rhs[i] += w
            elif y == -b:
                pass
            else:
                A[i][idx[y]] -= w
    return solve(A, rhs)[idx[0]]


def lucas_ratio(p, a, b):
    r = ldiv(1 - p, p)
    return ldiv(lucasU(1 + r, r, b), lucasU(1 + r, r, a + b))


def item84(p, a, b):
    r = ldiv(1 - p, p)
    return ldiv(r ** b - 1, r ** (a + b) - 1)


def item95():
    ps = [Fr(1, 10), Fr(1, 3), Fr(2, 5), Fr(1, 2), Fr(3, 5), Fr(3, 4), Fr(9, 10)]
    ok = all(hit_chance(p, a, b) == lucas_ratio(p, a, b)
             for p in ps for a in range(6) for b in range(6))
    check('95.grid', ok, f'{len(ps) * 36} cells: chance = U b / U (a + b), p = 1/2 included')
    ok = all(item84(p, a, b) == lucas_ratio(p, a, b)
             for p in ps if p != Fr(1, 2) for a in range(6) for b in range(6))
    d = next(((a, b) for a in range(6) for b in range(6)
              if item84(Fr(1, 2), a, b) != lucas_ratio(Fr(1, 2), a, b)), None)
    check('95.item84', ok and d == (0, 1),
          f"equal to item 84's form for p != 1/2; at p = 1/2 first differing (a, b) = {d}")
    ok = all(hit_chance(Fr(1), a, b) == lucas_ratio(Fr(1), a, b) for a in range(6) for b in range(6))
    check('95.p1', ok, 'p = 1: formula right in every cell')
    f = next(((a, b) for a in range(6) for b in range(6)
              if hit_chance(Fr(0), a, b) != lucas_ratio(Fr(0), a, b)), None)
    check('95.drop.hp0', f == (1, 1),
          f'p = 0: first failing (a, b) = {f}: chance {hit_chance(Fr(0), 1, 1)} '
          f'vs {lucas_ratio(Fr(0), 1, 1)}')


if __name__ == '__main__':
    rng = random.Random(20261014)
    item91()
    item92(rng)
    item93(rng)
    item94()
    item95()
    hits = sum(RESULTS)
    print(f'== {hits} of {len(RESULTS)} checks hit' + (' -- ALL OK' if hits == len(RESULTS) else ' -- SOME MISS'))
    sys.exit(0 if hits == len(RESULTS) else 1)
