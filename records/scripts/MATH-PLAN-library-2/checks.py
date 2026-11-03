#!/usr/bin/env python3
"""Checks for MATH-PLAN-library-2.md: every search and every number in the plan.

Run on DSMain (standard library only; Lean through lake for the --lean sections):

  mkdir mm && cd mm && git init -q && git remote add origin https://github.com/leanprover-community/mathlib4
  git fetch -q --depth 1 origin 2da3ab0a20dc0c66f56a557e37df39f7d36cb953 && git checkout -q FETCH_HEAD
  git fetch -q --depth 1 origin 5ed2965256430c3649e86755f9576b54eca72435
  cd .. && python3 -I MATH-PLAN-library-2-checks.py --repo ~/lean/classical-lean-paper-crypto --master mm --lean

Every check prints one line starting with HIT (the plan's claim holds) or MISS, then the claim and
what was measured. The last line counts them. Exit code 0 only if every check hits.
Searches are `grep -rniE --include=*.lean PATTERN DIR`, as in the last plan; a count is
"lines / files". Pinned Mathlib is <repo>/.lake/packages/mathlib (v4.34.0, 5ed2965256).
Exact checks use fractions.Fraction; a check marked FLOAT uses floats with the tolerance shown.
"""
import argparse, collections, itertools, json, math, os, random, re, subprocess, sys, tempfile
from fractions import Fraction as Fr

PINNED_REV = '5ed2965256430c3649e86755f9576b54eca72435'
MASTER_REV = '2da3ab0a20dc0c66f56a557e37df39f7d36cb953'
RESULTS = []

def check(label, ok, claim, measured=''):
    RESULTS.append(bool(ok))
    print(f"{'HIT ' if ok else 'MISS'} {label}: {claim}" + (f"  [measured: {measured}]" if measured != '' else ''))

# ---------------------------------------------------------------- grep helpers
def grep_count(pattern, d):
    """lines, files for grep -rniE --include=*.lean pattern d"""
    r = subprocess.run(['grep', '-rniEc', '--include=*.lean', pattern, d], capture_output=True, text=True)
    if r.returncode not in (0, 1):
        raise RuntimeError(f'grep failed on /{pattern}/: {r.stderr.strip()}')
    lines = files = 0
    for l in r.stdout.splitlines():
        n = int(l.rsplit(':', 1)[1])
        if n:
            lines += n; files += 1
    return lines, files

def grep_hits(pattern, d, k=3):
    r = subprocess.run(['grep', '-rniE', '--include=*.lean', pattern, d], capture_output=True, text=True)
    out = []
    for l in r.stdout.splitlines()[:k]:
        f, rest = l.split(':', 1)
        out.append(os.path.relpath(f, d) + ':' + rest.strip()[:110])
    return out

# ---------------------------------------------------------------- rows of the plan
# Each row: id, track ('G', 'L', or area number 1..10), cost (S, S-M, M, M-L, L), deps (ids this row
# rests on), and its searches: (pattern, expected pinned (lines, files), expected library lines or None).
# Master must equal pinned for every pattern unless 'master' is given (then the row is not
# "in newer Mathlib" only if the master hits are named as unrelated in the plan).
ROWS = [
 # ----- Track G (gate): searched in tools/ and by the Lean census below
 dict(id='G1', track='G', cost='S-M', deps=[], s=[]),
 dict(id='G2', track='G', cost='S', deps=[], s=[]),
 dict(id='G3', track='G', cost='S', deps=[], s=[]),
 dict(id='G4', track='G', cost='S-M', deps=[], s=[]),
 dict(id='G5', track='G', cost='S', deps=[], s=[]),
 dict(id='G6', track='G', cost='M', deps=[], s=[]),
 dict(id='G7', track='G', cost='S', deps=[], s=[]),
 dict(id='G8', track='G', cost='L', deps=[], s=[]),
 dict(id='G9', track='G', cost='M', deps=[], s=[]),
 # ----- Track L (what the 71-item plan narrowed or left)
 dict(id='L1', track='L', cost='M', deps=[], s=[('karlin|rubin|monotone likelihood', (1, 1), 13)]),
 dict(id='L2', track='L', cost='S', deps=[], s=[('affine.*(payoff|game)|payoff.*affine', (0, 0), 1)]),
 dict(id='L3', track='L', cost='S-M', deps=[], s=[('maximum.likelihood|plug-in estimate', (0, 0), 1)]),
 dict(id='L4', track='L', cost='S', deps=[], s=[]),
 dict(id='L5a', track='L', cost='M', deps=[], s=[]),
 dict(id='L5b', track='L', cost='M', deps=[], s=[]),
 dict(id='L6', track='L', cost='L', deps=[], s=[('pseudo.?inverse|moorePenrose|penrose', (35, 5), 1)]),
 dict(id='L7', track='L', cost='S-M', deps=[], s=[('perron', (6, 6), 1), ('stationary distribution|invariant distribution', (0, 0), 5)]),
 dict(id='L8', track='L', cost='L', deps=[], s=[('chi.?squared|chiSquared', (0, 0), 2)]),
 dict(id='L9', track='L', cost='S-M', deps=[], s=[('spectral density|spectralDensity', (0, 0), 0)]),
 dict(id='L11', track='L', cost='L', deps=[], s=[('\\bslater|karush|kuhn.?tucker', (2, 2), 3)]),
 dict(id='L12', track='L', cost='M', deps=[], s=[('efron', (0, 0), 0)]),
 dict(id='L13', track='L', cost='M', deps=[], s=[('sanov', (0, 0), 5)]),
 dict(id='L14', track='L', cost='S-M', deps=[], s=[('boundedly complete|bounded completeness', (0, 0), 1)]),
 dict(id='L15', track='L', cost='S', deps=[], s=[]),
 dict(id='L16', track='L', cost='S-M', deps=[], s=[]),
 dict(id='L17', track='L', cost='S-M', deps=[], s=[]),
 dict(id='L18', track='L', cost='S', deps=[], s=[]),
 dict(id='L19', track='L', cost='S', deps=[], s=[]),
 # ----- area 1, linear algebra
 dict(id='A1', track=1, cost='M', deps=[], s=[('interlac|poincar[eé] separation', (0, 0), 0)]),
 dict(id='A2', track=1, cost='M', deps=[], s=[('ky fan|kyFan', (0, 0), 0)]),
 dict(id='A3', track=1, cost='S-M', deps=[], s=[('kantorovich', (0, 0), 0)]),
 # ----- area 2, probability and statistics
 dict(id='B1', track=2, cost='M', deps=[], s=[('bernstein.?s? (inequality|bound)|bennett', (0, 0), 0)]),
 dict(id='B2', track=2, cost='M', deps=[], s=[('h[aá]jek', (0, 0), 0)]),
 dict(id='B3', track=2, cost='S-M', deps=[], s=[('\\bholm\\b|bonferroni|familywise error|family.wise error|step.?down (procedure|test)', (0, 0), 0)]),
 dict(id='B4', track=2, cost='M', deps=[], s=[('order statistic|orderStatistic|kth.?smallest', (0, 0), 0)]),
 dict(id='B5', track=2, cost='S-M', deps=[], s=[('probability integral transform', (0, 0), 0)]),
 dict(id='B6', track=2, cost='S-M', deps=[], s=[('kolmogorov.?smirnov|smirnov', (0, 0), 1)]),
 # ----- area 3, calculus
 dict(id='C1', track=3, cost='M', deps=[], s=[('fej[eé]r', (0, 0), 0)]),
 dict(id='C2', track=3, cost='S', deps=[], s=[('gr[üu]ss', (0, 0), 0), ('abs_covariance_le|covariance_le_sqrt|covariance.*sqrt.*variance', (0, 0), 0)]),
 dict(id='C3', track=3, cost='M', deps=[], s=[('euler.?maclaurin', (0, 0), 3), ('periodizedBernoulli 2|bernoulliFun 2', (1, 1), 0)]),
 # ----- area 4, differential equations
 dict(id='D1', track=4, cost='M', deps=[], s=[('variation of (constants|parameters)|duhamel', (0, 0), 0)]),
 dict(id='D2', track=4, cost='S-M', deps=[], s=[('lyapunov', (0, 0), 0)]),
 dict(id='D3', track=4, cost='M-L', deps=[], s=[('heun.?s method|runge.?kutta', (0, 0), 0)]),
 # ----- area 5, information theory
 dict(id='E1', track=5, cost='M', deps=[], s=[('channel capacity|binary symmetric', (0, 0), 0)]),
 dict(id='E2', track=5, cost='M', deps=[], s=[("han.?s inequality|shearer", (0, 0), 0)]),
 dict(id='E4', track=5, cost='S-M', deps=[], s=[('asymptotic equipartition|typical set|shannon.?mcmillan', (0, 0), 0)]),
 dict(id='E5', track=5, cost='L', deps=[], s=[('huffman', (0, 0), 0)]),
 dict(id='E6', track=5, cost='S-M', deps=[], s=[('f-divergence|fDivergence|csisz', (3, 2), 0)]),
 # ----- area 6, numerical analysis and matrices
 dict(id='F1', track=6, cost='M', deps=[], s=[('gauss.?seidel', (0, 0), 0)]),
 dict(id='F2', track=6, cost='M-L', deps=[], s=[('power (method|iteration)', (0, 0), 0)]),
 dict(id='F3', track=6, cost='M', deps=[], s=[('forward substitution|back.?substitution|triangular solve|backward (error|stab)', (0, 0), 0)]),
 dict(id='F4', track=6, cost='S', deps=[], s=[('richardson|extrapolat', (0, 0), 0)]),
 dict(id='F5', track=6, cost='S', deps=[], s=[('implicit euler|backward euler|a-stable|a-stability', (0, 0), 0)]),
 dict(id='F6', track=6, cost='S-M', deps=['A3'], s=[('steepest descent|exact line search', (0, 0), 0)]),
 # ----- area 7, convex optimization
 dict(id='H1', track=7, cost='S-M', deps=[], s=[('polyak|[lł]ojasiewicz', (0, 0), 0)]),
 dict(id='H2', track=7, cost='M', deps=[], s=[('projected gradient', (0, 0), 0)]),
 dict(id='H3', track=7, cost='S-M', deps=[], s=[('subgradient|subdifferential', (0, 0), 0)]),
 dict(id='H4', track=7, cost='M', deps=[], s=[('frank.?wolfe|conditional gradient', (0, 0), 0)]),
 dict(id='H5', track=7, cost='M', deps=[], s=[('state price|asset pricing|stiemke', (0, 0), 0), ('arbitrage', (0, 0), 1)]),
 dict(id='H6', track=7, cost='S', deps=[], s=[('convexConjugate|convex conjugate|fenchel|legendre.?(transform|fenchel)', (0, 0), 2)]),
 # ----- area 8, stochastic processes
 dict(id='K1', track=8, cost='M', deps=[], s=[('p[óo]lya.?s? urn|\\burn\\b', (0, 0), 0)]),
 dict(id='K2', track=8, cost='M', deps=[], s=[("wald", (1, 1), 11)]),
 dict(id='K3', track=8, cost='M', deps=[], s=[('reflection principle', (1, 1), 0)]),
 dict(id='K4', track=8, cost='M-L', deps=[], s=[('expected hitting|mean hitting|first.?step analysis|mean first passage', (0, 0), 0)]),
 # ----- area 9, time series
 dict(id='T1', track=9, cost='M', deps=[], s=[('durbin|partial autocorrelation', (0, 0), 0)]),
 dict(id='T2', track=9, cost='S', deps=[], s=[('variance ratio', (0, 0), 0)]),
 # ----- area 10, bridges
 dict(id='X1', track=10, cost='M', deps=[], s=[('minimax.*(linear program|duality)|linear program.*minimax', (0, 0), 0)]),
 dict(id='X2', track=10, cost='S', deps=[], s=[('generali[sz]ed least|aitken|glsMatrix', (0, 0), 36)]),
 dict(id='X3', track=10, cost='M', deps=[], s=[('gambler|ruin', (2, 2), 33), ('biased.*walk|asymmetric.*walk', (0, 0), 0)]),
 dict(id='X4', track=10, cost='S', deps=['X3'], s=[('lucas.*(ruin|walk)|ruin.*lucas', (0, 0), 0)]),
 dict(id='X5', track=10, cost='M', deps=['A2'], s=[('principal component|\\bPCA\\b', (0, 0), 0)]),
 dict(id='X6', track=10, cost='S', deps=[], s=[('det.*covMatrix|covMatrix.*det|generali[sz]ed variance', (0, 0), 0)]),
 dict(id='X7', track=10, cost='M', deps=[], s=[('no two consecutive|run.*fib|fib.*run', (0, 0), 1)]),
 dict(id='X8', track=10, cost='S', deps=[], s=[('h-theorem|entropy production', (0, 0), 0)]),
 dict(id='X9', track=10, cost='M-L', deps=[], s=[('total progeny|galton|branching process', (0, 0), 5)]),
 dict(id='X10', track=10, cost='S-M', deps=[], s=[('kalman|exponential smoothing', (0, 0), 4)]),
 dict(id='X11', track=10, cost='S-M', deps=['T2'], s=[('long.?run variance', (0, 0), 1)]),
 dict(id='X12', track=10, cost='S-M', deps=[], s=[('mirror descent|multiplicative weights|exponential weights', (0, 0), 10)]),
 dict(id='X13', track=10, cost='M', deps=[], s=[('bretagnolle|\\bhuber\\b', (0, 0), 0)]),
 dict(id='X14', track=10, cost='M', deps=[], s=[('negative cycle|bellman', (0, 0), 83)]),
 dict(id='X15', track=10, cost='S-M', deps=['H6'], s=[('logSumExp|softmax', (0, 0), 390)]),
 dict(id='X16', track=10, cost='S', deps=['A3', 'X2'], s=[('bloomfield', (0, 0), 0)]),
]
COST = {'S': 0, 'S-M': 1, 'M': 2, 'M-L': 3, 'L': 4}

def rank_rows():
    """The plan's rule: load-bearing first (another row rests on it), then absent from Mathlib (all
    rows are), then cheaper first. Ties: more dependents first, then Track L before area rows, then
    area number, then the row id in the order listed above. Track G is placed by its own rule."""
    math_rows = [r for r in ROWS if r['track'] != 'G']
    dependents = collections.Counter(d for r in math_rows for d in r['deps'])
    order = {r['id']: i for i, r in enumerate(math_rows)}
    def key(r):
        tier = 0 if dependents[r['id']] else 1
        track = 0 if r['track'] == 'L' else 1
        area = 0 if r['track'] == 'L' else r['track']
        return (tier, COST[r['cost']], -dependents[r['id']], track, area, order[r['id']])
    return sorted(math_rows, key=key), dependents

# ---------------------------------------------------------------- Lean sources (run with --lean)
LEAN_USED = r'''import ClassicalLean
open Lean
def dumpUsed : CoreM Unit := do
  let env ← getEnv
  let names := env.header.moduleNames
  let out ← IO.FS.Handle.mk "OUTFILE" .write
  for i in [0:names.size] do
    let m := names[i]!
    unless (`ClassicalLean).isPrefixOf m do continue
    let data := env.header.moduleData[i]!
    let mut seen : NameSet := {}
    for c in data.constNames do
      let some ci := env.find? c | continue
      let mut used := ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then used := used ++ v.getUsedConstants
      for u in used do
        if seen.contains u then continue
        seen := seen.insert u
        let um := match env.getModuleIdxFor? u with
          | some j => names[j.toNat]!
          | none => `none
        let kind := match env.find? u with
          | some (.thmInfo _) => "thm" | some (.defnInfo _) => "def" | some (.inductInfo _) => "ind"
          | some (.ctorInfo _) => "ctor" | some (.opaqueInfo _) => "opaque" | some (.axiomInfo _) => "ax"
          | some (.recInfo _) => "rec" | some (.quotInfo _) => "quot" | none => "none"
        let isInst := (Lean.Meta.instanceExtension.getState env).instanceNames.contains u
        out.putStrLn s!"{m}\t{u}\t{um}\t{kind}\t{isInst}"
#eval dumpUsed
'''

LEAN_CENSUS = r'''import ClassicalLean
open Lean Meta
def census : MetaM Unit := do
  let env ← getEnv
  let mut thms := 0; let mut written := 0; let mut h1 := 0; let mut h2 := 0; let mut h3 := 0
  let mut macroSc := 0; let mut helpers := 0; let mut orphan := 0; let mut deadHelpers := 0
  let mut irred : Array Name := #[]
  for (n, ci) in env.constants.toList do
    let u := privateToUserName n
    unless (`ClassicalLean).isPrefixOf u do continue
    if getReducibilityStatusCore env n == .irreducible then irred := irred.push u
    let .thmInfo ti := ci | continue
    thms := thms + 1
    if n.hasMacroScopes then macroSc := macroSc + 1
    let pos ← findDeclarationRanges? n
    match n with
    | .str p s =>
      if s.startsWith "_proof_" && pos.isNone then
        helpers := helpers + 1
        let mut used := false
        let mut q := p
        for _ in [0:4] do
          if let some pc := env.find? q then
            let mut cs := pc.type.getUsedConstants
            if let some v := pc.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
            if cs.contains n then used := true
          match q with
          | .str q' _ => q := q'
          | .num q' _ => q := q'
          | .anonymous => break
        unless used do
          orphan := orphan + 1
          let anyUse := env.constants.toList.any fun (_, mc) =>
            (mc.type.getUsedConstants ++ ((mc.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])).contains n
          unless anyUse do deadHelpers := deadHelpers + 1
    | _ => pure ()
    if pos.isNone then continue
    written := written + 1
    let k ← forallTelescopeReducing ti.type fun xs _ => do
      let mut k := 0
      for x in xs do
        let d ← x.fvarId!.getDecl
        if d.binderInfo.isInstImplicit then continue
        if ← isProp d.type then k := k + 1
      return k
    if k ≥ 1 then h1 := h1 + 1
    if k ≥ 2 then h2 := h2 + 1
    if k ≥ 3 then h3 := h3 + 1
  IO.println s!"CENSUS theorems {thms}"
  IO.println s!"CENSUS written {written}"
  IO.println s!"CENSUS hyp1 {h1}"
  IO.println s!"CENSUS hyp2 {h2}"
  IO.println s!"CENSUS hyp3 {h3}"
  IO.println s!"CENSUS macroscopes {macroSc}"
  IO.println s!"CENSUS helpers {helpers}"
  IO.println s!"CENSUS helpers_not_used_by_parent {orphan}"
  IO.println s!"CENSUS helpers_used_by_nothing {deadHelpers}"
  IO.println s!"CENSUS irreducible {irred.size} {irred.toList}"
set_option maxHeartbeats 4000000 in
#eval census
'''

LEAN_UNFOLD = r'''import Lean
open Lean Meta
def D1 (P Q : Nat → Prop) : Prop := ∀ x, P x → Q x
def D2 (P Q : Nat → Prop) : Prop := D1 P Q
def D3 (P Q : Nat → Prop) : Prop := D2 P Q
def D4 (P Q : Nat → Prop) : Prop := D3 P Q
def D5 (P Q : Nat → Prop) : Prop := D4 P Q
def D6 (P Q : Nat → Prop) : Prop := D5 P Q
-- the loop of tools/VacuityGate.lean (openLevels), maxUnfolds = 4, counting whnf calls before a binder
partial def openCount (t : Expr) (unfolds : Nat) : MetaM (Option Nat) := do
  match ← instantiateMVars t with
  | .forallE .. => return some unfolds
  | t =>
    if unfolds ≥ 4 then return none
    let t' ← whnf t
    if t'.isForall then openCount t' (unfolds + 1) else return none
#eval show MetaM Unit from do
  let pty ← mkArrow (mkConst ``Nat) (mkSort 0)
  withLocalDeclD `P pty fun P => do
  withLocalDeclD `Q pty fun Q => do
    let t := mkApp2 (mkConst ``D6) P Q
    let r ← openCount t 0
    let t' ← whnf t
    IO.println s!"UNFOLD {r.getD 99} {← ppExpr t'}"
'''

def run_lean(repo, src, tmp, name):
    path = os.path.join(tmp, name)
    with open(path, 'w') as f:
        f.write(src)
    env = dict(os.environ)
    env['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + env['PATH']
    r = subprocess.run(['nice', '-n', '19', 'lake', 'env', 'lean', path], cwd=repo, capture_output=True,
                       text=True, env=env)
    return r.returncode, r.stdout + r.stderr

# ---------------------------------------------------------------- bridge search (part 1 and 2)
def bridge_pairs(used_path, repo, maxdf=10):
    skip = re.compile(r'(\._|\.match_\d|\._proof|\.proof_\d|\.eq_\d|\.eq_def|\.rec$|\.recOn$|\.casesOn$|\.noConfusion|\.mk\.inj|\.sizeOf|^Mathlib\.Tactic|^Mathlib\.Meta|^Lean\.|^_private|\.to[A-Z][A-Za-z]*$|^inst|\.inst)')
    uses = collections.defaultdict(lambda: collections.defaultdict(set))
    for line in open(used_path, encoding='utf-8'):
        m, c, cm, kind, inst = line.rstrip('\n').split('\t')
        if not cm.startswith('Mathlib') or inst == 'true' or skip.search(c):
            continue
        k = 'obj' if kind in ('def', 'ind', 'opaque') else 'thm' if kind == 'thm' else None
        if k:
            uses[m][k].add(c)
    mods = sorted(uses)
    imp, clo = import_graph(repo)
    N = len(mods)
    df = {k: collections.Counter(c for m in mods for c in uses[m][k]) for k in ('obj', 'thm')}
    rows = []
    for i, a in enumerate(mods):
        for b in mods[i + 1:]:
            sa, sb = a.replace('ClassicalLean.', ''), b.replace('ClassicalLean.', '')
            if sa in clo.get(sb, ()) or sb in clo.get(sa, ()):
                continue
            sc = 0.0
            for k in ('obj', 'thm'):
                sc += sum(math.log(N / df[k][c]) for c in uses[a][k] & uses[b][k] if df[k][c] <= maxdf)
            if sc > 0:
                rows.append((round(sc, 1), sa, sb))
    rows.sort(key=lambda x: (-x[0], x[1], x[2]))
    return N, rows

def import_graph(repo):
    imp = {}
    root = os.path.join(repo, 'ClassicalLean')
    for dp, _, fs in os.walk(root):
        for f in fs:
            if f.endswith('.lean'):
                p = os.path.join(dp, f)
                mod = os.path.relpath(p, repo)[:-5].replace('/', '.').replace('ClassicalLean.', '')
                imp[mod] = {i.replace('ClassicalLean.', '') for i in re.findall(r'^import (ClassicalLean\S*)', open(p, encoding='utf-8').read(), re.M)}
    def clo(m, s=None):
        s = set() if s is None else s
        for d in imp.get(m, ()):
            if d not in s:
                s.add(d); clo(d, s)
        return s
    return imp, {m: clo(m) for m in imp}

SHAPES = {
 'first-order recursion': r'\(t \+ 1\) = a \* |a \* x t \+|= a \* [A-Za-z]+ (t|n|k) \+ |riccatiStep|x \(t \+ 1\)',
 'linear recurrence': r'LinearRecurrence|companionMatrix|charpoly|recDenom|lucasU|lucasV',
 'supermartingale': r'Supermartingale|Submartingale|Martingale\b',
 'Kraft-type sum': r'[0-9D] \^ \(-|\(2 : ℝ\) \^ \(-|inv_two_pow_length|Kraft',
 'quadratic form': r'⬝ᵥ [^\n]*\*ᵥ|quadForm|dotProduct_mulVec|xᵀ A x|wᵀ S w',
 'covariance': r'covMatrix|covariance|variance_sum|variance_average|categoricalCov|weightedCov',
 'relative entropy': r'relEntropy|klDiv',
 'log-sum-exp': r'logSumExp|softmax|freeEnergy',
 'stochastic matrix': r'rowStochastic|∑ j, [A-Z] i j = 1|vecMul|Channel',
 'generating function': r'PowerSeries|pgf|generating function',
 'stopping time': r'IsStoppingTime|stoppedValue|hitting|exitTime',
 'linear program': r'Farkas|farkas|duality|hyperplane_separation|PrimalFeasible|HasPrices',
 'eigenvalues': r'eigenvalues|IsHermitian|spectral',
 'binary strings': r'Fin n → Bool|List Bool|runEvent|IsPrefixFree',
}
def shape_modules(repo):
    mods = {}
    root = os.path.join(repo, 'ClassicalLean')
    for dp, _, fs in os.walk(root):
        for f in fs:
            if f.endswith('.lean'):
                p = os.path.join(dp, f)
                mods[os.path.relpath(p, repo)[:-5].replace('/', '.').replace('ClassicalLean.', '')] = open(p, encoding='utf-8').read()
    out = {}
    for name, rx in SHAPES.items():
        r = re.compile(rx)
        out[name] = {m for m, t in mods.items() if any(r.search(l) for l in t.splitlines())}
    return out

# ---------------------------------------------------------------- exact helpers
def fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a
def trib(n):  # the library's tribonacci: 0, 0, 1, 1, 2, 4, 7, ...
    t = [0, 0, 1]
    while len(t) <= n:
        t.append(t[-1] + t[-2] + t[-3])
    return t[n]
def lucasU(P, Q, n):
    u0, u1 = Fr(0), Fr(1)
    for _ in range(n):
        u0, u1 = u1, P * u1 - Q * u0
    return u0
def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
def transpose(A):
    return [list(r) for r in zip(*A)]
def inverse(A):
    n = len(A)
    M = [list(map(Fr, r)) + [Fr(int(i == j)) for j in range(n)] for i, r in enumerate(A)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        pv = M[c][c]
        M[c] = [x / pv for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [r[n:] for r in M]
def det(A):
    n = len(A); M = [list(map(Fr, r)) for r in A]; d = Fr(1)
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None:
            return Fr(0)
        if p != c:
            M[c], M[p] = M[p], M[c]; d = -d
        d *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return d
def householder(v):
    """rational orthogonal matrix I - 2 v v^T / (v^T v)"""
    n = len(v); s = sum(x * x for x in v)
    return [[Fr(int(i == j)) - Fr(2) * v[i] * v[j] / s for j in range(n)] for i in range(n)]
def quad(A, x):
    return sum(x[i] * A[i][j] * x[j] for i in range(len(x)) for j in range(len(x)))

NAMES = [
    ('L', 'HasPrices'),
    ('L', 'IsAncillary'),
    ('L', 'IsComplete'),
    ('L', 'IsTest'),
    ('L', 'NoGainCycle'),
    ('L', 'abs_prod_one_add_sub_one_le'),
    ('L', 'abs_sub_eulerIterate_le'),
    ('L', 'bernProd'),
    ('L', 'closedSimplex'),
    ('L', 'convexOn_midpoint_le_average'),
    ('L', 'covMatrix'),
    ('L', 'covariance_eq_sum'),
    ('L', 'covariance_movingAverage'),
    ('L', 'covariance_movingAverage_eq_zero_of_lt'),
    ('L', 'det_le_prod_diag'),
    ('L', 'draws'),
    ('L', 'eigenvalues_eq_iSup_iInf'),
    ('L', 'empiricalCDF'),
    ('L', 'eq_exp_smul_mulVec'),
    ('L', 'eq_of_eq_C_add_X_mul'),
    ('L', 'eq_steady_iff'),
    ('L', 'existsUnique_vecMul_eq_self'),
    ('L', 'exists_isPrefixFree_length_eq'),
    ('L', 'exitTime'),
    ('L', 'extinctionChance'),
    ('L', 'farkas'),
    ('L', 'gamma'),
    ('L', 'gibbsObjective_le'),
    ('L', 'gibbsObjective_softmax'),
    ('L', 'glsMatrix'),
    ('L', 'hasDerivAt_exp_smul_mulVec'),
    ('L', 'iSup_bayesRisk_eq_minimaxRisk_of_finite'),
    ('L', 'indep_of_isSufficient_of_isComplete_of_isAncillary'),
    ('L', 'integral_eFalseShare_le'),
    ('L', 'integral_score_le_one'),
    ('L', 'integral_stoppedValue_eq'),
    ('L', 'isMaxOn_gibbsObjective'),
    ('L', 'isMinOn_of_kkt'),
    ('L', 'isUniformlyMostPowerful_of_monotoneLikelihoodRatio'),
    ('L', 'le_add_inner_gradient_add_sq'),
    ('L', 'le_sub_of_gradientStep'),
    ('L', 'leastSquares'),
    ('L', 'lp_strong_duality'),
    ('L', 'lucasU'),
    ('L', 'lucasU_add_two'),
    ('L', 'measureReal_empirical_eq_le'),
    ('L', 'measureReal_exists_abs_ge_le'),
    ('L', 'measureReal_exists_le_of_supermartingale'),
    ('L', 'measureReal_no_run_le'),
    ('L', 'measureReal_score_bernProd_ge_le'),
    ('L', 'minWeights'),
    ('L', 'minimax_eq_of_exponentialWeights'),
    ('L', 'mutualInfo_eq_shannonEntropy_add_shannonEntropy_sub_shannonEntropy'),
    ('L', 'noGainCycle_iff_noNegativeCycle'),
    ('L', 'norm_jacobiStep_sub_le'),
    ('L', 'onesInvOnes'),
    ('L', 'payoff'),
    ('L', 'pgf'),
    ('L', 'posSemidef_covMatrix'),
    ('L', 'power_le_of_likelihoodRatioTest'),
    ('L', 'relEntropy'),
    ('L', 'relEntropy_nonneg'),
    ('L', 'relEntropy_softmax'),
    ('L', 'relEntropy_vecMul_le'),
    ('L', 'riccatiRoot'),
    ('L', 'riccati_equation_riccatiRoot'),
    ('L', 'runEvent'),
    ('L', 'shannonEntropy'),
    ('L', 'shannonEntropy_eq_add_condEntropy'),
    ('L', 'shannonEntropy_le_log_card'),
    ('L', 'shannonEntropy_le_shannonEntropy_add_shannonEntropy'),
    ('L', 'simpson'),
    ('L', 'sum_abs_vecMul_pow_sub_le'),
    ('L', 'sum_eq_integral_add'),
    ('L', 'sum_minWeights'),
    ('L', 'tendsto_sup_abs_empiricalCDF_sub'),
    ('L', 'tribonacci'),
    ('L', 'variance_average'),
    ('L', 'variance_mix'),
    ('L', 'vecMeasure'),
    ('M', 'Complex.normSq'),
    ('M', 'ConvexOn.map_sum_le'),
    ('M', 'EReal'),
    ('M', 'Finset.card_bij'),
    ('M', 'LinearMap.IsSymmetric.eigenvalues_antitone'),
    ('M', 'LinearMap.IsSymmetric.eigenvectorBasis'),
    ('M', 'Matrix.IsHermitian.spectral_theorem'),
    ('M', 'Matrix.PosDef'),
    ('M', 'Matrix.PosSemidef'),
    ('M', 'MeasureTheory.Martingale'),
    ('M', 'MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg'),
    ('M', 'MeasureTheory.measure_biUnion_finset_le'),
    ('M', 'MeasureTheory.stoppedValue'),
    ('M', 'Nat.fib'),
    ('M', 'Nat.multinomial'),
    ('M', 'ProbabilityTheory.cdf'),
    ('M', 'ProbabilityTheory.covariance'),
    ('M', 'ProbabilityTheory.covariance_self'),
    ('M', 'ProbabilityTheory.gammaPDF'),
    ('M', 'ProbabilityTheory.gaussianReal'),
    ('M', 'ProbabilityTheory.iIndepFun.mgf_sum'),
    ('M', 'ProbabilityTheory.iIndepSet'),
    ('M', 'ProbabilityTheory.measure_ge_le_exp_mul_mgf'),
    ('M', 'ProbabilityTheory.strong_law_ae'),
    ('M', 'ProbabilityTheory.variance_le_sq_of_bounded'),
    ('M', 'Real.binEntropy'),
    ('M', 'Real.one_sub_le_exp_neg'),
    ('M', 'Submartingale.ae_tendsto_limitProcess'),
    ('M', 'antitoneOn_of_deriv_nonpos'),
    ('M', 'bernoulliFun_two'),
    ('M', 'catalan'),
    ('M', 'exists_norm_eq_iInf_of_complete_convex'),
    ('M', 'geometric_hahn_banach_point_open'),
    ('M', 'iSup_le'),
    ('M', 'intervalIntegral.integral_hasDerivAt_right'),
    ('M', 'le_iSup'),
    ('M', 'norm_eq_iInf_iff_real_inner_le_zero'),
    ('M', 'norm_sub_sq_real'),
    ('M', 'periodizedBernoulli'),
    ('M', 'tendsto_pow_atTop_nhds_zero_iff'),
    ('M', 'Matrix.IsPrimitive'),
    ('M', 'trapezoidal_integral'),
]

def declared(name, d):
    """Is some suffix of the dotted name (at least its last part) declared in d? Returns the
    suffix found, longest first, or None."""
    parts = name.split('.')
    for k in range(len(parts)):
        suf = '.'.join(parts[k:])
        pat = r'^\s*(@\[[^]]*\]\s*)?((private|protected|noncomputable|nonrec|scoped) )*(theorem|lemma|def|abbrev|structure|class|inductive|instance|irreducible_def) ' + re.escape(suf) + r"([^A-Za-z0-9_'₀-₉.]|$)"
        r = subprocess.run(['grep', '-rEc', '--include=*.lean', pat, d], capture_output=True, text=True)
        if sum(int(l.rsplit(':', 1)[1]) for l in r.stdout.splitlines()):
            return suf
    return None

# ---------------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--repo', required=True)
    ap.add_argument('--master', required=True)
    ap.add_argument('--lane', default='/opt/datasphere/lane/inbox/threads/staging')
    ap.add_argument('--lean', action='store_true', help='also run the two Lean scripts (a few minutes)')
    a = ap.parse_args()
    repo = os.path.expanduser(a.repo)
    pinned = os.path.join(repo, '.lake/packages/mathlib')
    master = os.path.expanduser(a.master)
    lib = os.path.join(repo, 'ClassicalLean')
    random.seed(20261011)

    print('== 0. Setup')
    man = json.load(open(os.path.join(repo, 'lake-manifest.json')))
    rev = next(p['rev'] for p in man['packages'] if p['name'] == 'mathlib')
    check('setup.pinned', rev == PINNED_REV, f'pinned Mathlib is {PINNED_REV[:10]}', rev[:10])
    mh = subprocess.run(['git', '-C', master, 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
    if mh != MASTER_REV:
        print(f'refusing: the master clone is at {mh}, not {MASTER_REV}')
        sys.exit(2)
    check('setup.master', True, f'master clone is at {MASTER_REV[:10]}', mh[:10])
    nmod = sum(1 for dp, _, fs in os.walk(lib) for f in fs if f.endswith('.lean'))
    check('setup.modules', nmod == 120, 'the library has 120 modules', nmod)
    mtc = open(os.path.join(master, 'lean-toolchain')).read().strip()
    check('setup.master_toolchain', mtc == 'leanprover/lean4:v4.35.0-rc4', 'master builds with v4.35.0-rc4', mtc)
    head = subprocess.run(['git', '-C', repo, 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
    check('setup.worktree', head.startswith('d2cba27'), 'the worktree is at d2cba27 (VACUITY-1)', head[:7])

    print('== 1. Wanted/ and docs/1000.yaml, pinned against master')
    def wanted(root):
        r = subprocess.run(['grep', '-rnE', '--include=*.lean', r'^\s*proof_wanted\s', os.path.join(root, 'Wanted')], capture_output=True, text=True)
        names = sorted(re.sub(r'^.*?proof_wanted\s+', '', l).split()[0] for l in r.stdout.splitlines())
        return len(r.stdout.splitlines()), len({l.split(':')[0] for l in r.stdout.splitlines()}), names
    pl, pf, pn = wanted(pinned); ml, mf, mn = wanted(master)
    check('wanted.pinned', (pl, pf) == (34, 18), 'pinned Wanted/: 34 proof_wanted in 18 files', (pl, pf))
    check('wanted.master', (ml, mf) == (33, 17), 'master Wanted/: 33 in 17 files', (ml, mf))
    check('wanted.new', set(mn) - set(pn) == set(), 'master has no proof_wanted that pinned lacks', sorted(set(mn) - set(pn)))
    check('wanted.removed', set(pn) - set(mn) == {'recENNReal_neg_coe_ennreal'}, 'one removed on master: recENNReal_neg_coe_ennreal', sorted(set(pn) - set(mn)))
    def y1000(root):
        ents = {}; cur = None
        for line in open(os.path.join(root, 'docs/1000.yaml'), encoding='utf-8'):
            m = re.match(r'^(Q\d+):', line)
            if m:
                cur = m.group(1); ents[cur] = ''; continue
            if cur:
                ents[cur] += line
        return ents
    yp, ym = y1000(pinned), y1000(master)
    check('1000.count', len(yp) == len(ym) == 1179, 'docs/1000.yaml has 1179 entries in both', (len(yp), len(ym)))
    changed = sorted(q for q in ym if q not in yp or ym[q] != yp[q])
    check('1000.changed', changed == ['Q1052678'], 'only Q1052678 (Baire category theorem) differs, and it is outside the plan', changed)

    print('== 2. The search behind each row (pinned / master / library)')
    for r in ROWS:
        for pat, exp_p, exp_l in r['s']:
            cp = grep_count(pat, os.path.join(pinned, 'Mathlib'))
            cm = grep_count(pat, os.path.join(master, 'Mathlib'))
            cl = grep_count(pat, lib)[0]
            ok = cp == tuple(exp_p) and cm == cp and (exp_l is None or cl == exp_l)
            check(f"row.{r['id']}", ok, f"/{pat}/ pinned {exp_p[0]}/{exp_p[1]}, master the same, library {exp_l}",
                  f'pinned {cp[0]}/{cp[1]}, master {cm[0]}/{cm[1]}, library {cl}')
            if cp[0]:
                for h in grep_hits(pat, os.path.join(pinned, 'Mathlib')):
                    print('      pinned hit:', h)

    print('== 2b. Not candidates: Mathlib (or the library) has them')
    NOT = [
     ('Loewner order reverses inverses (C*-algebras)', r'protected lemma inv_le_inv \{a b : Aˣ\}', pinned, (1, 1)),
     ('matrices are a C*-ring (scoped instance)', r'lemma instCStarRing : CStarRing \(Matrix', pinned, (1, 1)),
     ("Sylvester's law of inertia", r"Sylvester's law of inertia", pinned, (10, 2)),
     ("Popoviciu's inequality on variances", r"Popoviciu's inequality", pinned, (1, 1)),
     ('detailed balance gives an invariant measure', r'def IsReversible|reversible Markov kernel leaves', pinned, (2, 1)),
     ('Doob decomposition (martingale part)', r'noncomputable def martingalePart', pinned, (1, 1)),
     ('martingale convergence', r'theorem Submartingale\.ae_tendsto_limitProcess ', pinned, (1, 1)),
     ('Cramér-Wold', r'Cramér-Wold theorem', pinned, (3, 1)),
     ('grid-lines lemma (gives finite Loomis-Whitney by counting measure)', r'grid-lines lemma', pinned, (8, 1)),
     ('Chebyshev sum inequality', r"Chebyshev's Sum Inequality", pinned, (11, 1)),
     ('library: entropy subadditivity', r'theorem shannonEntropy_le_shannonEntropy_add_shannonEntropy', lib, (1, 1)),
     ('library: uniform law has the most entropy', r'theorem shannonEntropy_le_log_card', lib, (1, 1)),
    ]
    for name, pat, root, exp in NOT:
        d = os.path.join(root, 'Mathlib') if root != lib else lib
        c = grep_count(pat, d)
        check('not.' + name.split()[0], c == exp, f'{name}: /{pat}/ {exp[0]}/{exp[1]}', f'{c[0]}/{c[1]}')

    print('== 2c. Every name a row rests on is declared (pinned Mathlib, or the library)')
    missing = []
    for src, n in NAMES:
        d = os.path.join(pinned, 'Mathlib') if src == 'M' else lib
        if declared(n, d) is None:
            missing.append(src + ' ' + n)
    check('names', missing == [], f'all {len(NAMES)} names cited in "rests on" cells are declared ({sum(1 for s, _ in NAMES if s == "M")} Mathlib, {sum(1 for s, _ in NAMES if s == "L")} library)', missing)

    print('== 2d. Track L: what the library says now')
    rd = lambda rel: open(os.path.join(lib, rel), encoding='utf-8').read()
    check('trackL.L4', re.search(r'^example', rd('Combinatorics/ArbitrageCycle.lean'), re.M) is None, 'ArbitrageCycle.lean has no example yet (item 86)')
    check('trackL.L15', rd('Probability/LongestRun.lean').count('(hA : ∀ i, MeasurableSet (A i))') == 2, 'both LongestRun theorems assume each A i measurable (item 87)')
    check('trackL.L16', rd('Analysis/FiniteGame.lean').count('(hℓ : ∀ θ y, ℓ θ y ≠ ∞)') == 2, 'FiniteGame assumes every loss finite (hℓ) in item 63 (item 103)')
    lr = rd('Probability/LikelihoodScore.lean'); es = rd('Probability/EffectiveSampleSize.lean')
    check('trackL.L17', '(hq0 : p₀ ≤ q) (hq1 : q < 1) (N : ℕ)' in lr and 'theorem variance_average_le_of_steady [IsProbabilityMeasure μ]' in es and 'theorem integral_residual_sq' in rd('Statistics/ResidualVariance.lean'),
          'item 5 still assumes q < 1 and item 6 a probability measure (item 104)')
    ct = rd('InformationTheory/CompressionTest.lean')
    check('trackL.L18', 'import ClassicalLean.Probability.EValueStepUp' not in ct and re.search(r'theorem \S*eFalseShare', ct) is None, 'CompressionTest neither imports EValueStepUp nor states an e-BH lemma (item 88)')
    check('trackL.L19', re.search(r'^theorem[^\n]*exp', rd('Probability/LongestRun.lean'), re.M) is None, 'LongestRun has no exp-form bound yet (item 91)')
    check('trackL.L2', 'not proved' in rd('Analysis/FiniteGame.lean').split('affine change', 1)[1][:80], "FiniteGame's docstring says the affine change is not proved (item 85)")
    for pat, exp, what in ((r'\bwold\b', (3, 1), 'Wold: 3 hits, all Cramér-Wold'), ('ljung', (0, 0), 'Ljung-Box: none'),
                           ('stochastic integral|itoIntegral', (0, 0), 'no stochastic integral')):
        cp = grep_count(pat, os.path.join(pinned, 'Mathlib')); cm = grep_count(pat, os.path.join(master, 'Mathlib'))
        check('notnow.' + what.split(':')[0].split()[0], cp == exp and cm == cp, f'/{pat}/ {exp[0]}/{exp[1]} pinned and master ({what})', f'{cp}, {cm}')

    print('== 2f. Facts behind the cold review r1 findings')
    fg = rd('Analysis/FiniteGame.lean'); gr = rd('Probability/GamblersRuin.lean')
    check('r1.minimax', re.search(r'^theorem minimax_eq_of_matrix ', fg, re.M) is not None, 'the minimax equality is already in the library (minimax_eq_of_matrix): items 85 and 141 are new proofs only')
    check('r1.wald_pm1', re.search(r'^theorem integral_stoppedValue_walk_sq ', gr, re.M) is not None, 'the ±1 case of Wald\'s second identity is in the library (integral_stoppedValue_walk_sq): item 138 is the general step law')
    c = grep_count(r'structure IsPrimitive', os.path.join(pinned, 'Mathlib/LinearAlgebra/Matrix/Irreducible'))
    check('r1.isPrimitive', c == (1, 1), 'Mathlib defines Matrix.IsPrimitive (Irreducible/Defs.lean), which item 100 should use', c)
    irr = [re.search(r'^def ' + n + r'\b[^\n]*', rd(f), re.M).group(0) for n, f in (('motzkin', 'Combinatorics/AlgebraicGeneratingFunction.lean'), ('nacciAugmented', 'NumberTheory/NacciTrace.lean'), ('euclidSteps', 'NumberTheory/EuclidSteps.lean'))]
    check('r1.irreducible_values', all(re.search(r'ℕ|ℤ', l) and 'Prop' not in l for l in irr), 'the three irreducible definitions take values in ℕ or ℤ, not Prop: item 73 changes nothing for today\'s library', irr)
    ch = rd('InformationTheory/Channel.lean')
    check('r1.dpi_support', '(hpq : ∀ i, q i = 0 → p i = 0)' in ch, 'relEntropy_vecMul_le assumes q i = 0 → p i = 0, which item 97 must carry', '')
    lp = open(os.path.join(a.lane, 'MATH-PLAN-library.md'), encoding='utf-8').read().split('## 4. The ranked list', 1)[1].split('## 5.', 1)[0]
    rows_, names_ = 0, set()
    for l in lp.splitlines():
        cc = [x.strip() for x in re.split(r'(?<!\\)\|', l)[1:-1]]
        if len(cc) >= 7 and re.match(r'^\d+$', cc[0]):
            rows_ += 1; names_ |= set(re.findall(r"`([A-Za-z][A-Za-z0-9_.']*)`", cc[3]))
    check('r1.backfill', (rows_, len(names_)) == (71, 86), 'the last plan names 86 declarations in the Lean-names column of its 71 rows (item 89\'s backfill is about 90 examples)', (rows_, len(names_)))

    print('== 2e. Pinned against master, whole Mathlib/ (the bump question)')
    st = subprocess.run(['git', '-C', master, 'diff', '--shortstat', PINNED_REV, MASTER_REV, '--', 'Mathlib'], capture_output=True, text=True)
    if st.returncode == 0 and st.stdout.strip():
        nums = list(map(int, re.findall(r'(\d+) (?:files? changed|insertions?|deletions?)', st.stdout)))
        check('diff.mathlib', nums == [6474, 55913, 44612], 'master differs from the pin in Mathlib/: 6474 files changed, 55913 insertions, 44612 deletions', nums)
    else:
        check('diff.mathlib', False, 'the master clone also holds the pinned commit (git fetch --depth 1 origin 5ed2965256...)', st.stderr.strip()[:120])
    bump = os.path.join(repo, 'records/rounds/20260923T164057Z__round-17-toolchain-v4.34.0.md')
    t = open(bump, encoding='utf-8').read()
    steps = re.findall(r'^\| v4\.\d+\.\d+ \|', t, re.M)
    sites = [int(x) for x in re.findall(r'\| (\d+) sites', t)]
    check('bump.steps', len(steps) == 6, 'the last bump (round 17) took 6 toolchain steps', len(steps))
    check('bump.sites', sum(sites) == 23, 'and changed 23 proof sites (6 + 17)', sites)
    check('bump.jobs', '3719' in t and '44 modules' in t, 'at 3719 jobs and 44 modules', '3719' in t)

    print('== 3. Track G: the gate today (tools/VacuityGate.lean at d2cba27)')
    gate = open(os.path.join(repo, 'tools/VacuityGate.lean'), encoding='utf-8').read()
    tests = open(os.path.join(repo, 'tools/VacuityGateTests.lean'), encoding='utf-8').read()
    check('gate.maxUnfolds', 'def maxUnfolds : Nat := 4' in gate, 'at most 4 unfoldings before each binder')
    check('gate.macro', 'if n.hasMacroScopes then continue' in gate, 'theorems with macro scopes are skipped')
    check('gate.helper', 'if s.startsWith "_proof_" then return (← findDeclarationRanges? n).isNone' in gate, '`_proof_` names with no source position are skipped')
    code = [l for l in gate.splitlines() if not l.strip().startswith('--') and '`' not in l]
    check('gate.metacheck', 'Meta.check' in gate and not any(re.search(r'\baddDecl\b', l) for l in code),
          'flags are checked by Meta.check; addDecl appears only in comments and docstrings')
    check('gate.heartbeats', 'set_option maxHeartbeats 2000000 in' in gate, 'per-theorem budget 2000000 heartbeats')
    for tname in ('lim_and_hyp', 'lim_false'):
        check('gate.test.' + tname, re.search(r'theorem ' + tname + r'\b', tests) is not None, f'test {tname} is in VacuityGateTests.lean')
    rl = [l for l in open(os.path.join(repo, 'tools/vacuity_reviewed.txt'), encoding='utf-8') if l.strip() and not l.startswith('#')]
    check('gate.list', rl == [], 'the reviewed list has no entries', len(rl))

    tmp = tempfile.mkdtemp(prefix='mathplan2-')
    if a.lean:
        print('== 4. Lean census (HypCensus) and the bridge search (UsedConsts)')
        rc, out = run_lean(repo, LEAN_CENSUS, tmp, 'HypCensus.lean')
        cen = dict((m.group(1), m.group(2)) for m in re.finditer(r'CENSUS (\S+) (.*)', out))
        exp = {'theorems': '3158', 'written': '1748', 'hyp1': '1068', 'hyp2': '637', 'hyp3': '400',
               'macroscopes': '0', 'helpers': '589', 'helpers_not_used_by_parent': '7', 'helpers_used_by_nothing': '3'}
        check('census.rc', rc == 0, 'the census runs', rc)
        for k, v in exp.items():
            check('census.' + k, cen.get(k) == v, f'{k} = {v}', cen.get(k))
        if all(cen.get(k) for k in ('helpers', 'helpers_not_used_by_parent', 'helpers_used_by_nothing')):
            hp, hn, hd = int(cen['helpers']), int(cen['helpers_not_used_by_parent']), int(cen['helpers_used_by_nothing'])
            check('census.derived', (hp - hn, hn - hd, hp - hd) == (582, 4, 586), '582 helpers used by their parent, 4 by something else, 586 used in all', (hp - hn, hn - hd, hp - hd))
        irr = cen.get('irreducible', '')
        check('census.irreducible', irr.startswith('3 ') and all(x in irr for x in ('motzkin', 'nacciAugmented', 'euclidSteps')),
              'three irreducible definitions: motzkin, nacciAugmented, euclidSteps', irr)
        rc, out = run_lean(repo, LEAN_UNFOLD, tmp, 'UnfoldProbe.lean')
        m = re.search(r'UNFOLD (\S+) (.*)', out)
        check('r1.unfold', rc == 0 and m is not None and m.group(1) == '1' and m.group(2).startswith('∀'), 'the gate\'s loop opens six nested definitions with one whnf call (the 4-unfolding limit never fires; item 74)', m.group(0) if m else out[-200:])
        used = os.path.join(tmp, 'used.tsv')
        rc, out = run_lean(repo, LEAN_USED.replace('OUTFILE', used), tmp, 'UsedConsts.lean')
        check('used.rc', rc == 0 and os.path.exists(used), 'UsedConsts runs and writes used.tsv', rc)
        nl = sum(1 for _ in open(used, encoding='utf-8'))
        check('used.lines', nl == 56744, 'used.tsv has 56744 (module, constant) lines', nl)
        N, pairs = bridge_pairs(used, repo)
        check('bridges.modules', N == 119, '119 modules use a kept Mathlib constant', N)
        check('bridges.pairs', len(pairs) == 2337, '2337 import-unrelated pairs share a kept constant', len(pairs))
        top = [(s, x, y) for s, x, y in pairs[:30]]
        print('      top 30 pairs:', '; '.join(f'{x} x {y} {s}' for s, x, y in top))
        want = {('Analysis.FiniteGame', 'Analysis.LinearProgram'), ('Probability.GamblersRuin', 'Probability.MaximalInequality'),
                ('Algebra.MinMax', 'Probability.CovarianceDirections')}
        found = {(x, y) for s, x, y in pairs[:60]}
        check('bridges.named', want <= found, 'FiniteGame x LinearProgram, GamblersRuin x MaximalInequality and MinMax x CovarianceDirections are in the top 60', sorted(want - found))
        rank = {(x, y): i + 1 for i, (s, x, y) in enumerate(pairs)}
        for p in sorted(want):
            print(f'      rank of {p[0]} x {p[1]}: {rank.get(p)}')
        sc = {(x, y): s for s, x, y in pairs}
        for (x, y), (rk, s_) in {('Probability.GlivenkoCantelli', 'Statistics.NeymanPearson'): (1, 188.7),
                                 ('Probability.GamblersRuin', 'Probability.MaximalInequality'): (2, 121.8),
                                 ('Analysis.FiniteGame', 'Analysis.LinearProgram'): (17, 66.1),
                                 ('Algebra.MinMax', 'Probability.CovarianceDirections'): (36, 51.4)}.items():
            check('bridges.rank', rank.get((x, y)) == rk and sc.get((x, y)) == s_, f'{x} x {y}: rank {rk}, score {s_}', (rank.get((x, y)), sc.get((x, y))))
        mq = rank.get(('Analysis.MinimumQuadraticForm', 'Statistics.GaussMarkov'))
        check('bridges.minquad', mq is not None and mq <= 60, 'MinimumQuadraticForm x GaussMarkov is in the top 60', mq)
    else:
        print('== 4. skipped (no --lean): the census and the constant-overlap search are not run')

    print('== 4b. Shape search (part 2 of the bridge search)')
    sh = shape_modules(repo)
    imp, clo = import_graph(repo)
    def unrelated(x, y):
        return x not in clo.get(y, ()) and y not in clo.get(x, ())
    SH = [('first-order recursion', 'Probability.KalmanVariance', 'Probability.FirstOrderRecursion'),
          ('generating function', 'Probability.Extinction', 'Combinatorics.AlgebraicGeneratingFunction'),
          ('covariance', 'Probability.MovingAverage', 'Probability.EffectiveSampleSize'),
          ('covariance', 'Analysis.MinimumQuadraticForm', 'Statistics.GeneralizedLeastSquares'),
          ('linear program', 'Analysis.LinearProgram', 'Combinatorics.ArbitrageCycle'),
          ('log-sum-exp', 'Analysis.ExponentialWeights', 'InformationTheory.Entropy'),
          ('eigenvalues', 'Algebra.HadamardInequality', 'Probability.CovarianceDirections'),
          ('stopping time', 'Probability.GamblersRuin', 'Probability.MaximalInequality'),
          ('linear recurrence', 'NumberTheory.LucasSequence', 'Algebra.CompanionMatrix')]
    for shape, x, y in SH:
        ok = x in sh[shape] and y in sh[shape]
        rel = 'unrelated' if unrelated(x, y) else 'import-related'
        check('shape.' + shape.split()[0], ok, f'{x} and {y} both match the shape "{shape}" ({rel})', f'{len(sh[shape])} modules match')
    for x, y in [('Probability.KalmanVariance', 'Probability.FirstOrderRecursion'), ('Probability.Extinction', 'Combinatorics.AlgebraicGeneratingFunction'),
                 ('Analysis.FiniteGame', 'Analysis.LinearProgram'), ('Analysis.LinearProgram', 'Combinatorics.ArbitrageCycle'),
                 ('Statistics.GeneralizedLeastSquares', 'Analysis.MinimumQuadraticForm'), ('Probability.GamblersRuin', 'NumberTheory.LucasSequence'),
                 ('Probability.LongestRun', 'NumberTheory.Tribonacci'), ('Analysis.ExponentialWeights', 'InformationTheory.Entropy'),
                 ('InformationTheory.Entropy', 'Statistics.NeymanPearson'), ('Probability.MovingAverage', 'Probability.EffectiveSampleSize'),
                 ('Algebra.MinMax', 'Probability.CovarianceDirections'), ('Algebra.HadamardInequality', 'Probability.CovarianceDirections'),
                 ('Simplex.LogSumExp', 'InformationTheory.Entropy')]:
        check('imports.' + x.split('.')[-1] + '_' + y.split('.')[-1], (x in imp and y in imp),
              f'{x} and {y} are modules; ' + ('no import path between them' if unrelated(x, y) else 'one imports the other'),
              'unrelated' if unrelated(x, y) else 'related')

    print('== 5. Exact checks of the plan\'s mathematical claims')
    # X3, X4: biased walk ruin chance, its Lucas form, and Ville's bound as b grows
    allok = True
    for p in (Fr(1, 3), Fr(2, 5), Fr(3, 5), Fr(3, 4)):
        q = 1 - p; r = q / p
        for a_ in range(1, 5):
            for b_ in range(1, 5):
                n = a_ + b_
                # h(x) = chance to hit a before -b from x; states x = -b..a; solve tridiagonal exactly
                N = n + 1
                M = [[Fr(0)] * N for _ in range(N)]; rhs = [Fr(0)] * N
                for i in range(N):
                    if i == 0:
                        M[i][i] = Fr(1)
                    elif i == N - 1:
                        M[i][i] = Fr(1); rhs[i] = Fr(1)
                    else:
                        M[i][i] = Fr(1); M[i][i + 1] = -p; M[i][i - 1] = -q
                inv = inverse(M)
                h0 = sum(inv[b_][j] * rhs[j] for j in range(N))
                formula = (r ** b_ - 1) / (r ** n - 1)
                lucas = lucasU(1 + r, r, b_) / lucasU(1 + r, r, n)
                allok &= (h0 == formula == lucas)
    check('X3.X4.ruin', allok, 'for p in {1/3, 2/5, 3/5, 3/4} and 1 <= a, b <= 4: P(a before -b) = (r^b - 1)/(r^(a+b) - 1) = U_b/U_(a+b), U = lucasU (1 + r) r, r = q/p')
    p = Fr(1, 3); q = 1 - p; r = q / p; a_ = 2
    vals = [(r ** b_ - 1) / (r ** (a_ + b_) - 1) for b_ in range(1, 41)]
    check('X3.ville', all(x < y for x, y in zip(vals, vals[1:])) and all(v <= (p / q) ** a_ for v in vals) and (p / q) ** a_ - vals[-1] < Fr(1, 10 ** 10),
          'p = 1/3, a = 2: the chance rises with b towards (p/q)^a = 1/4 and never passes it')
    # X7: strings with no run of r losses
    okr = all(sum(1 for s in itertools.product((0, 1), repeat=n) if '00' not in ''.join(map(str, s))) == fib(n + 2) for n in range(0, 15))
    okt = all(sum(1 for s in itertools.product((0, 1), repeat=n) if '000' not in ''.join(map(str, s))) == trib(n + 3) for n in range(0, 15))
    check('X7.runs', okr and okt, 'n <= 14: strings with no two losses in a row number fib (n + 2); with no three, tribonacci (n + 3)')
    # X10: steady Kalman gain for a = h = 1 is exponential smoothing, steady error variance = riccatiRoot
    ok = True
    for _ in range(200):
        P = Fr(random.randint(1, 60), random.randint(1, 9)); rr = Fr(random.randint(1, 60), random.randint(1, 9))
        qq = P * P / (P + rr)                     # makes P the Riccati root: P = P r/(P + r) + q
        ok &= (P == P * rr / (P + rr) + qq)
        K = P / (P + rr)
        ok &= ((qq + K * K * rr) / (1 - (1 - K) ** 2) == P)
    check('X10.kalman', ok and (Fr(2) == (1 + Fr(1, 4) * 2) / (1 - Fr(1, 4))), 'a = h = 1: (q + K^2 r)/(1 - (1 - K)^2) = P* with K = P*/(P* + r), 200 exact cases; (q, r) = (1, 2) gives P* = 2, K = 1/2')
    # X2: GLS for a common mean equals the minimum-variance weights
    ok = True
    for _ in range(50):
        n = 3
        B = [[Fr(random.randint(-5, 5)) for _ in range(n)] for _ in range(n)]
        V = [[sum(B[i][k] * B[j][k] for k in range(n)) + (Fr(1) if i == j else 0) for j in range(n)] for i in range(n)]
        Vi = inverse(V); one = [[Fr(1)] for _ in range(n)]
        XtViX = matmul(matmul(transpose(one), Vi), one)[0][0]
        gls = [x / XtViX for x in matmul(matmul(transpose(one), Vi), [[Fr(int(i == j)) for j in range(n)] for i in range(n)])[0]]
        c = sum(Vi[i][j] for i in range(n) for j in range(n))
        minw = [sum(Vi[i][j] for j in range(n)) / c for i in range(n)]
        ok &= (gls == minw) and (1 / XtViX == 1 / c)
    check('X2.gls_mean', ok, 'X = ones: the GLS row (1ᵀV⁻¹1)⁻¹1ᵀV⁻¹ equals minWeights V = V⁻¹1/(1ᵀV⁻¹1), and its variance factor is 1/(1ᵀV⁻¹1); 50 exact 3x3 cases')
    # A3, X16, F6: Kantorovich, Bloomfield-Watson for the mean, steepest descent
    okk = okb = oks = True; eq = True
    for _ in range(60):
        n = 4
        lam = sorted(Fr(random.randint(1, 30), random.randint(1, 4)) for _ in range(n))
        m_, M_ = lam[0], lam[-1]
        Q = householder([Fr(random.randint(-4, 4) or 1) for _ in range(n)])
        A = matmul(matmul(Q, [[lam[i] if i == j else Fr(0) for j in range(n)] for i in range(n)]), transpose(Q))
        Ai = inverse(A)
        bound = (m_ + M_) ** 2 / (4 * m_ * M_)
        for _ in range(5):
            x = [Fr(random.randint(-6, 6)) for _ in range(n)]
            s = sum(t * t for t in x)
            if s == 0:
                continue
            okk &= quad(A, x) * quad(Ai, x) <= bound * s * s
            g = [sum(A[i][j] * x[j] for j in range(n)) for i in range(n)]       # gradient of x^T A x / 2
            gg = sum(t * t for t in g)
            alpha = gg / quad(A, g)
            xn = [x[i] - alpha * g[i] for i in range(n)]
            oks &= quad(A, xn) <= ((M_ - m_) / (M_ + m_)) ** 2 * quad(A, x)
        one = [Fr(1)] * n
        okb &= quad(A, one) * quad(Ai, one) / (n * n) <= bound
        v = [Q[i][0] + Q[i][n - 1] for i in range(n)]                      # eigenvectors for m and M
        eq &= quad(A, v) * quad(Ai, v) == bound * sum(t * t for t in v) ** 2
    check('A3.kantorovich', okk and eq, '(xᵀAx)(xᵀA⁻¹x) <= (m + M)^2/(4mM) |x|^4 on 300 exact cases, equality at v_m + v_M')
    check('X16.efficiency', okb, '(1ᵀV1)(1ᵀV⁻¹1)/n^2 <= (m + M)^2/(4mM): OLS against GLS for a common mean, 60 exact cases')
    check('F6.steepest', oks, 'exact line search on xᵀAx/2 shrinks it by at least ((M - m)/(M + m))^2, 300 exact cases')
    # F4: Simpson = (4 T(2N) - T(N))/3
    ok = True
    for _ in range(100):
        N = random.randint(1, 6); a0 = Fr(random.randint(-5, 5)); b0 = a0 + Fr(random.randint(1, 9), random.randint(1, 3))
        vals = {}
        def f(x):
            if x not in vals:
                vals[x] = Fr(random.randint(-50, 50), random.randint(1, 7))
            return vals[x]
        h = (b0 - a0) / (2 * N)
        simp = h / 3 * sum(f(a0 + 2 * k * h) + 4 * f(a0 + (2 * k + 1) * h) + f(a0 + (2 * k + 2) * h) for k in range(N))
        def trap(m):
            return (b0 - a0) / m * ((f(a0) + f(b0)) / 2 + sum(f(a0 + (k + 1) * (b0 - a0) / m) for k in range(m - 1)))
        ok &= simp == (4 * trap(2 * N) - trap(N)) / 3
    check('F4.richardson', ok, "the library's simpson f N a b = (4 T(2N) - T(N))/3 with Mathlib's trapezoidal_integral, 100 exact cases with arbitrary values")
    # F5: stability of explicit and implicit Euler on y' = -λ y
    grid = [Fr(k, 8) for k in range(1, 40)]
    check('F5.stability', all(abs(1 / (1 + z)) < 1 for z in grid) and all((abs(1 - z) < 1) == (z < 2) for z in grid),
          'hλ in (0, 5): implicit factor 1/(1 + hλ) < 1 always; explicit |1 - hλ| < 1 exactly when hλ < 2')
    # T2 and X11: variance of a sum of a stationary series; MA(q) long-run form
    ok2 = ok11 = True
    for _ in range(80):
        q = random.randint(0, 3); th = [Fr(random.randint(-4, 4)) for _ in range(q + 1)]; v = Fr(random.randint(1, 5))
        gam = lambda k: v * sum(th[j] * th[j + k] for j in range(q + 1 - k)) if k <= q else Fr(0)
        for n in range(1, 8):
            var = sum(gam(abs(i - j)) for i in range(n) for j in range(n))
            if gam(0) != 0:
                ok2 &= var == n * gam(0) * (1 + 2 * sum((1 - Fr(j, n)) * gam(j) / gam(0) for j in range(1, n)))
            if n > q:
                ok11 &= var == n * v * sum(th) ** 2 - 2 * sum(k * gam(k) for k in range(1, q + 1))
    check('T2.variance_ratio', ok2, 'Var(X_0 + ... + X_(k-1)) = k γ0 (1 + 2 Σ_(j<k) (1 - j/k) ρ_j), exact on MA covariances')
    check('X11.long_run', ok11, 'MA(q), n > q: Var(sum of n) = n v (Σθ)^2 - 2 Σ_(k<=q) k γ(k), exact')
    # L9: MA spectral density at ω = 0 and π
    ok = True
    for _ in range(80):
        q = random.randint(0, 4); th = [Fr(random.randint(-4, 4)) for _ in range(q + 1)]; v = Fr(random.randint(1, 5))
        gam = lambda k: v * sum(th[j] * th[j + k] for j in range(q + 1 - k))
        ok &= gam(0) + 2 * sum(gam(k) for k in range(1, q + 1)) == v * sum(th) ** 2
        ok &= gam(0) + 2 * sum((-1) ** k * gam(k) for k in range(1, q + 1)) == v * sum((-1) ** j * th[j] for j in range(q + 1)) ** 2
    check('L9.spectral', ok, 'Σ_(|k|<=q) γ(k) e^(-ikω) = v |Σ θ_j e^(ijω)|^2 at ω = 0 and π, exact')
    # X6: det of a covariance matrix <= product of variances (Hadamard)
    ok = True
    for _ in range(100):
        n = random.randint(2, 4); B = [[Fr(random.randint(-4, 4)) for _ in range(n + 1)] for _ in range(n)]
        S = [[sum(B[i][k] * B[j][k] for k in range(n + 1)) for j in range(n)] for i in range(n)]
        ok &= det(S) <= math.prod(S[i][i] for i in range(n))
    check('X6.det_cov', ok, 'det S <= Π S_ii for 100 exact Gram (covariance) matrices')
    # L7: a primitive chain with a zero entry
    P = [[Fr(0), Fr(1)], [Fr(1, 2), Fr(1, 2)]]
    P2 = matmul(P, P)
    pi = [Fr(1, 3), Fr(2, 3)]
    ok = min(min(r) for r in P2) == Fr(1, 4) and matmul([pi], P)[0] == pi
    for mu in ([Fr(1), Fr(0)], [Fr(0), Fr(1)]):
        row = [mu]
        for t in range(13):
            dist = sum(abs(x - y) for x, y in zip(row[0], pi))
            ok &= dist <= 2 * Fr(1, 2) ** (t // 2)
            row = matmul(row, P)
    check('L7.primitive', ok, 'P = [[0, 1], [1/2, 1/2]] has a zero entry, P^2 >= 1/4, stationary (1/3, 2/3), Σ|μP^t - π| <= 2 (1/2)^(t div 2) for t <= 12')
    # L3: the maximum-likelihood rate gives each string at least the mass any fixed rate does
    ok = True
    for n in range(1, 9):
        for k in range(n + 1):
            ph = Fr(k, n)
            ml = ph ** k * (1 - ph) ** (n - k)
            ok &= all(ml >= Fr(j, 10) ** k * (1 - Fr(j, 10)) ** (n - k) for j in range(0, 11))
    check('L3.plugin', ok, 'n <= 8: p̂^k (1 - p̂)^(n - k) >= p^k (1 - p)^(n - k) for p in {0, 1/10, ..., 1}, p̂ = k/n')
    # X9: Catalan and the progeny equation
    deg = 21
    T = [Fr(0)] * (deg + 1)
    for _ in range(deg + 1):
        T2 = [sum(T[i] * T[j - i] for i in range(j + 1)) for j in range(deg + 1)]
        T = [Fr(0)] + [(Fr(int(j == 0)) + T2[j]) / 2 for j in range(deg)]
    cat = lambda n: math.comb(2 * n, n) // (n + 1)
    ok = all(T[2 * n + 1] == Fr(cat(n), 2 ** (2 * n + 1)) and T[2 * n] == 0 for n in range(deg // 2))
    ok2 = all(sum(Fr(cat(k), 4 ** k) for k in range(N)) == 2 - 2 * Fr(math.comb(2 * N, N), 4 ** N) for N in range(1, 31))
    check('X9.catalan', ok and ok2, 'T = X (1 + T^2)/2 has t_(2n+1) = C_n / 2^(2n+1), t_(2n) = 0 (degree <= 21); Σ_(k<N) C_k/4^k = 2 - 2 C(2N, N)/4^N (N <= 30), so Σ C_n/2^(2n+1) -> 1')
    # T1: Durbin-Levinson against a direct solve
    ok = True
    for _ in range(40):
        q = 3; th = [Fr(random.randint(-3, 3)) for _ in range(q + 1)]; th[0] = Fr(random.randint(1, 3))
        gam = lambda k: (sum(th[j] * th[j + k] for j in range(q + 1 - k)) if k <= q else Fr(0)) + (Fr(1) if k == 0 else 0)
        phi = []; vk = gam(0)
        for k in range(1, 6):
            kap = (gam(k) - sum(phi[j] * gam(k - 1 - j) for j in range(k - 1))) / vk
            phi = [phi[j] - kap * phi[k - 2 - j] for j in range(k - 1)] + [kap]
            vk = vk * (1 - kap * kap)
            G = [[gam(abs(i - j)) for j in range(k)] for i in range(k)]
            direct = [sum(inverse(G)[i][j] * gam(j + 1) for j in range(k)) for i in range(k)]
            ok &= direct == phi and vk == gam(0) - sum(phi[j] * gam(j + 1) for j in range(k)) and vk > 0
    check('T1.durbin_levinson', ok, 'the recursion gives the solution of Γ_k φ = (γ(1), ..., γ(k)) and v_k = γ(0) - φ·γ > 0, k <= 5, 40 exact cases')
    # F1: Gauss-Seidel contracts by at most ρ in the max norm
    ok = True
    for _ in range(60):
        n = 4
        A = [[Fr(random.randint(-3, 3)) for _ in range(n)] for _ in range(n)]
        for i in range(n):
            A[i][i] = sum(abs(A[i][j]) for j in range(n) if j != i) + Fr(random.randint(1, 4))
        rho = max(sum(abs(A[i][j]) for j in range(n) if j != i) / A[i][i] for i in range(n))
        e = [Fr(random.randint(-9, 9)) for _ in range(n)]
        for _ in range(4):
            new = list(e)
            for i in range(n):
                new[i] = -sum(A[i][j] * new[j] for j in range(n) if j != i) / A[i][i]
            ok &= max(map(abs, new)) <= rho * max(map(abs, e))
            e = new
    check('F1.gauss_seidel', ok, 'strictly diagonally dominant 4x4: each Gauss-Seidel sweep shrinks the error by at most ρ (max norm), 240 exact sweeps')
    # C2: Grüss for finite uniform laws
    ok = True
    for _ in range(200):
        n = random.randint(2, 6)
        X = [Fr(random.randint(-9, 9)) for _ in range(n)]; Y = [Fr(random.randint(-9, 9)) for _ in range(n)]
        mx, my = sum(X) / n, sum(Y) / n
        cov = sum((x - mx) * (y - my) for x, y in zip(X, Y)) / n
        ok &= abs(cov) <= (max(X) - min(X)) * (max(Y) - min(Y)) / 4
    check('C2.gruss', ok, '|Cov(X, Y)| <= (M - m)(N - n)/4 on 200 exact finite uniform laws')
    # K3: reflection principle
    ok = True
    for n in range(1, 15):
        walks = list(itertools.product((-1, 1), repeat=n))
        for a_ in range(1, n + 1):
            hit = sum(1 for w in walks if max(itertools.accumulate(w)) >= a_)
            end_ge = sum(1 for w in walks if sum(w) >= a_); end_gt = sum(1 for w in walks if sum(w) > a_)
            ok &= hit == end_ge + end_gt
    check('K3.reflection', ok, 'n <= 14, a >= 1: #(max_(k<=n) S_k >= a) = #(S_n >= a) + #(S_n > a)')
    # K2: Wald's second identity, exact enumeration
    ok = True
    steps = [(Fr(-2), Fr(1, 3)), (Fr(1), Fr(2, 3))]                # mean 0, variance 2
    def wald(Nmax, stop):
        es2 = et = Fr(0)
        for path in itertools.product(range(2), repeat=Nmax):
            pr = math.prod(steps[i][1] for i in path); s = Fr(0); t = 0
            for i in path:
                if stop(s, t):
                    break
                s += steps[i][0]; t += 1
            es2 += pr * s * s; et += pr * t
        return es2, et
    for Nmax in range(1, 9):
        es2, et = wald(Nmax, lambda s, t: abs(s) >= 3)
        ok &= es2 == 2 * et
    check('K2.wald2', ok, 'steps -2 (1/3) or +1 (2/3), τ = first |S| >= 3 capped at N <= 8: E[S_τ^2] = 2 E[τ] exactly')
    # B4: order statistics, exact enumeration
    ok = True
    law = [(0, Fr(1, 2)), (1, Fr(1, 3)), (2, Fr(1, 6))]
    for n in range(1, 5):
        for x in range(3):
            F = sum(pw for v, pw in law if v <= x)
            for k in range(1, n + 1):
                lhs = sum(math.prod(law[i][1] for i in tup) for tup in itertools.product(range(3), repeat=n)
                          if sorted(law[i][0] for i in tup)[k - 1] <= x)
                ok &= lhs == sum(math.comb(n, j) * F ** j * (1 - F) ** (n - j) for j in range(k, n + 1))
    check('B4.order_stat', ok, 'a law on {0, 1, 2}, n <= 4: P(k-th smallest <= x) = Σ_(j>=k) C(n, j) F^j (1 - F)^(n - j)')
    # B5: P(F(X) <= u) <= u for a law with atoms
    ok = True
    law = [(0, Fr(1, 2)), (1, Fr(1, 3)), (2, Fr(1, 6))]
    Fv = {v: sum(pw for w, pw in law if w <= v) for v, _ in law}
    for k in range(0, 49):
        u = Fr(k, 24)
        ok &= sum(pw for v, pw in law if Fv[v] <= u) <= u
    check('B5.pit', ok, 'law (1/2, 1/3, 1/6) on {0, 1, 2}: P(F(X) <= u) <= u on 49 values of u in [0, 2] (for u < 0 the left side is 0 > u, so the row says u >= 0; equality needs F continuous)')

    print('== 5b. More exact checks of row formulas')
    # C3 (item 128): Euler-Maclaurin to second order, exact for quartics on integer ranges.
    # On [k, k+1], with s = t - k: ∫ B2(s) ds = 0, ∫ s B2(s) ds = 0, ∫ s^2 B2(s) ds = 1/180, B2(s) = s^2 - s + 1/6.
    mom = [sum(Fr(1, j + 3) - Fr(1, j + 2) + Fr(1, 6 * (j + 1)) for _ in [0]) for j in range(3)]
    ok = mom == [0, 0, Fr(1, 180)]
    for _ in range(60):
        c = [Fr(random.randint(-4, 4)) for _ in range(5)]
        f = lambda x: sum(c[i] * x ** i for i in range(5))
        fp = lambda x: sum(i * c[i] * x ** (i - 1) for i in range(1, 5))
        F = lambda x: sum(c[i] * x ** (i + 1) / (i + 1) for i in range(5))
        a0 = random.randint(-4, 2); b0 = a0 + random.randint(1, 5)
        gam2 = 12 * c[4]                                  # f'' = 2 c2 + 6 c3 t + 12 c4 t^2
        rem = (b0 - a0) * gam2 / 2 * Fr(1, 180)           # ∫ B2(fract t)/2 f''(t) dt
        lhs = sum(f(Fr(k)) for k in range(a0, b0 + 1))
        rhs = F(Fr(b0)) - F(Fr(a0)) + (f(Fr(a0)) + f(Fr(b0))) / 2 + (fp(Fr(b0)) - fp(Fr(a0))) / 12 - rem
        ok &= lhs == rhs
    check('C3.em2', ok, "Σ_(k=a..b) f k = ∫ f + (f a + f b)/2 + (f'(b) - f'(a))/12 - ∫ B2(fract t)/2 f''(t) dt, exact for 60 random quartics")
    # A2, X5, A1 (items 83, 142, 123): Ky Fan and interlacing, FLOAT with Jacobi's eigenvalue method
    def eig(S):
        n = len(S); A = [r[:] for r in S]; V = [[float(i == j) for j in range(n)] for i in range(n)]
        for _ in range(100):
            off = max((abs(A[i][j]), i, j) for i in range(n) for j in range(n) if i < j)
            if off[0] < 1e-14:
                break
            _, p_, q_ = off
            th = 0.5 * math.atan2(2 * A[p_][q_], A[q_][q_] - A[p_][p_])
            c_, s_ = math.cos(th), math.sin(th)
            for k in range(n):
                akp, akq = A[k][p_], A[k][q_]
                A[k][p_], A[k][q_] = c_ * akp - s_ * akq, s_ * akp + c_ * akq
            for k in range(n):
                apk, aqk = A[p_][k], A[q_][k]
                A[p_][k], A[q_][k] = c_ * apk - s_ * aqk, s_ * apk + c_ * aqk
            for k in range(n):
                vkp, vkq = V[k][p_], V[k][q_]
                V[k][p_], V[k][q_] = c_ * vkp - s_ * vkq, s_ * vkp + c_ * vkq
        return sorted(((A[i][i], [V[k][i] for k in range(n)]) for i in range(n)), key=lambda x: -x[0])
    def gs(vs):
        out = []
        for v in vs:
            w = v[:]
            for u in out:
                d = sum(a * b for a, b in zip(w, u)); w = [a - d * b for a, b in zip(w, u)]
            nn = math.sqrt(sum(a * a for a in w)); out.append([a / nn for a in w])
        return out
    okk = oki = True
    for _ in range(200):
        n = 4; B = [[random.uniform(-2, 2) for _ in range(n)] for _ in range(n)]
        S = [[(B[i][j] + B[j][i]) / 2 for j in range(n)] for i in range(n)]
        ev = eig(S); lam = [e for e, _ in ev]
        for k in range(1, n + 1):
            top = sum(lam[:k])
            U = gs([[random.uniform(-1, 1) for _ in range(n)] for _ in range(k)])
            val = sum(sum(u[i] * S[i][j] * u[j] for i in range(n) for j in range(n)) for u in U)
            okk &= val <= top + 1e-9
            Ue = [v for _, v in ev[:k]]
            okk &= abs(sum(sum(u[i] * S[i][j] * u[j] for i in range(n) for j in range(n)) for u in Ue) - top) < 1e-9
        Sm = [r[:n - 1] for r in S[:n - 1]]; mu = [e for e, _ in eig(Sm)]
        oki &= all(lam[k] + 1e-9 >= mu[k] >= lam[k + 1] - 1e-9 for k in range(n - 1))
    check('A2.kyfan', okk, 'FLOAT: 200 random symmetric 4x4, k = 1..4: Σ over orthonormal u of uᵀSu <= sum of the k largest eigenvalues, equality at eigenvectors (also items 142)')
    check('A1.interlace', oki, 'FLOAT: deleting the last row and column: λ_k(S) >= λ_k(S\') >= λ_(k+1)(S), 200 cases')
    # H1 (item 112): Polyak-Łojasiewicz rate on f(x) = Σ a_i x_i^2 / 2 (μ = min a, L = max a), exact
    ok = True
    for _ in range(100):
        aa = [Fr(random.randint(1, 9)) for _ in range(3)]; Lc, mu = max(aa), min(aa)
        x = [Fr(random.randint(-9, 9)) for _ in range(3)]
        f = lambda y: sum(ai * yi * yi for ai, yi in zip(aa, y)) / 2
        f0 = f(x)
        for k in range(1, 6):
            x = [yi - ai * yi / Lc for ai, yi in zip(aa, x)]
            ok &= f(x) <= (1 - mu / Lc) ** k * f0
    check('H1.pl', ok, 'PL with step 1/L on positive diagonal quadratics: f(x_k) - f* <= (1 - μ/L)^k (f(x_0) - f*), exact')
    # H3 (item 113): subgradient method on f(x) = |x - c|, exact
    ok = True
    for _ in range(200):
        cc = Fr(random.randint(-20, 20), 3); x = Fr(random.randint(-30, 30)); x0 = x
        eta = Fr(random.randint(1, 8), 4); T = random.randint(1, 12); G = 1
        vals = []
        for _ in range(T):
            vals.append(abs(x - cc)); g = 1 if x > cc else (-1 if x < cc else 0); x = x - eta * g
        ok &= min(vals) - 0 <= ((x0 - cc) ** 2 + eta ** 2 * G * G * T) / (2 * eta * T)
    check('H3.subgradient', ok, 'f = |x - c|, G = 1: min_(k<T) f(x_k) - f(c) <= (|x_0 - c|^2 + η^2 G^2 T)/(2 η T), 200 exact runs')
    # L12 (item 121): Efron-Stein on {0,1}^3 with product weights, and the bounded-difference form
    ok = True
    for _ in range(200):
        pr = [Fr(random.randint(1, 9), 10) for _ in range(3)]
        pts = list(itertools.product((0, 1), repeat=3))
        w = {x: math.prod(pr[i] if x[i] else 1 - pr[i] for i in range(3)) for x in pts}
        fv = {x: Fr(random.randint(-9, 9)) for x in pts}
        mean = sum(w[x] * fv[x] for x in pts); var = sum(w[x] * (fv[x] - mean) ** 2 for x in pts)
        es = Fr(0); cs = Fr(0)
        for i in range(3):
            for x in pts:
                y = tuple(1 - x[j] if j == i else x[j] for j in range(3))
                m_i = (pr[i] * fv[x if x[i] else y] + (1 - pr[i]) * fv[y if x[i] else x])
                es += w[x] * (fv[x] - m_i) ** 2
            cs += max(abs(fv[x] - fv[tuple(1 - x[j] if j == i else x[j] for j in range(3))]) for x in pts) ** 2
        ok &= var <= es and var <= cs / 4
    check('L12.efron_stein', ok, '200 random f on {0,1}^3 with product weights: Var f <= Σ_i E[Var_i f] and Var f <= Σ c_i^2 / 4, exact')
    # B2 (item 125): Hájek-Rényi for the fair ±1 walk, exact enumeration
    ok = True
    for n in range(1, 11):
        for _ in range(5):
            cs_ = sorted((Fr(random.randint(1, 9), random.randint(1, 3)) for _ in range(n)), reverse=True)
            eps = Fr(random.randint(1, 6))
            hit = sum(1 for w_ in itertools.product((-1, 1), repeat=n) if max(cs_[k] * abs(sum(w_[:k + 1])) for k in range(n)) >= eps)
            ok &= Fr(hit, 2 ** n) <= sum(c * c for c in cs_) / (eps * eps)
    check('B2.hajek_renyi', ok, 'fair ±1 walk, n <= 10, random nonincreasing weights: P(max c_k |S_k| >= ε) <= Σ c_k^2 / ε^2, exact')
    # B3 (item 105): Holm's procedure, exact, independent and identical p-values
    ok = True
    K = 6; grid = [Fr(k, K) for k in range(1, K + 1)]          # discrete uniform: P(p <= u) <= u
    def holm(ps, q):
        m = len(ps); order = sorted(range(m), key=lambda i: ps[i]); rej = set()
        for r, i in enumerate(order):
            if ps[i] <= q / (m - r):
                rej.add(i)
            else:
                break
        return rej
    for q in (Fr(1, 10), Fr(1, 4), Fr(1, 2)):
        for m, m0 in ((2, 1), (3, 2), (3, 3), (4, 2)):
            fw = Fr(0)
            for nulls in itertools.product(grid, repeat=m0):
                ps = list(nulls) + [Fr(0)] * (m - m0)                  # false nulls: p = 0
                fw += Fr(1, K ** m0) * (1 if holm(ps, q) & set(range(m0)) else 0)
            same = sum(Fr(1, K) * (1 if holm([u] * m0 + [Fr(0)] * (m - m0), q) & set(range(m0)) else 0) for u in grid)
            ok &= fw <= q and same <= q
    check('B3.holm', ok, 'Holm at q in {1/10, 1/4, 1/2}, m <= 4: P(a true null rejected) <= q, independent and identical (fully dependent) valid p-values, exact')
    # E6 (item 110): data processing for f-divergences, FLOAT
    ok = True
    fs = [lambda x: x * math.log(x) if x > 0 else 0.0, lambda x: (x - 1) ** 2, lambda x: abs(x - 1), lambda x: -math.log(x) if x > 0 else 50.0]
    for _ in range(300):
        n_, k_ = random.randint(2, 4), random.randint(2, 4)
        pp = [random.random() for _ in range(n_)]; qq = [random.random() + 0.05 for _ in range(n_)]
        W = [[random.random() for _ in range(k_)] for _ in range(n_)]; W = [[x / sum(r) for x in r] for r in W]
        pW = [sum(pp[i] * W[i][j] for i in range(n_)) for j in range(k_)]; qW = [sum(qq[i] * W[i][j] for i in range(n_)) for j in range(k_)]
        for f in fs[:3]:
            ok &= sum(qW[j] * f(pW[j] / qW[j]) for j in range(k_)) <= sum(qq[i] * f(pp[i] / qq[i]) for i in range(n_)) + 1e-9
    check('E6.fdiv', ok, 'FLOAT: 300 random p, q > 0 and channels W, f in {x log x, (x - 1)^2, |x - 1|}: Σ_j (qW)_j f((pW)_j/(qW)_j) <= Σ_i q_i f(p_i/q_i)')
    # H4 (item 135): squared diameter of the simplex, and the Frank-Wolfe rate, FLOAT
    ok = all(max(sum((a - b) ** 2 for a, b in zip([int(i == r) for r in range(n)], [int(j == r) for r in range(n)])) for i in range(n) for j in range(n)) == 2 for n in range(2, 7))
    okfw = True
    for _ in range(100):
        n = 4; B = [[random.uniform(-1, 1) for _ in range(n)] for _ in range(n)]
        Q = [[sum(B[i][k] * B[j][k] for k in range(n)) for j in range(n)] for i in range(n)]
        Lc = sum(abs(v) for r in Q for v in r)                         # a bound on the largest eigenvalue
        bvec = [random.uniform(-1, 1) for _ in range(n)]
        f = lambda x: 0.5 * sum(x[i] * Q[i][j] * x[j] for i in range(n) for j in range(n)) + sum(b * xi for b, xi in zip(bvec, x))
        grad = lambda x: [sum(Q[i][j] * x[j] for j in range(n)) + bvec[i] for i in range(n)]
        best = min(f(gs_) for gs_ in ([random.random() for _ in range(n)] for _ in range(2000)) for gs_ in [[v / sum(gs_) for v in gs_]])
        best = min(best, min(f([float(i == j) for j in range(n)]) for i in range(n)))
        x = [1.0] + [0.0] * (n - 1)
        for k in range(30):
            g = grad(x); s = min(range(n), key=lambda i: g[i]); gam = 2 / (k + 2)
            x = [(1 - gam) * xi + gam * (1.0 if i == s else 0.0) for i, xi in enumerate(x)]
            okfw &= f(x) - best <= 4 * Lc / (k + 3) + 1e-9
    check('H4.frank_wolfe', ok and okfw, 'the simplex has squared diameter 2 (n = 2..6); FLOAT: Frank-Wolfe on 100 random convex quadratics: f(x_k) - min f <= 4L/(k + 2) (min f estimated by sampling, an upper estimate, so this check is weaker than an exact one; 30 steps)')

    print('== 5c. Last formula checks')
    # L13 (item 122): Sanov lower half, exact counting with floats for exp/log
    ok = True
    for n in range(1, 13):
        for p_ in ([0.5, 0.5], [0.2, 0.3, 0.5], [0.1, 0.9]):
            K_ = len(p_)
            for counts in itertools.product(range(n + 1), repeat=K_):
                if sum(counts) != n:
                    continue
                qv = [c / n for c in counts]
                prob = math.factorial(n) / math.prod(math.factorial(c) for c in counts) * math.prod(pi ** c for pi, c in zip(p_, counts))
                D = sum(qi * math.log(qi / pi) for qi, pi in zip(qv, p_) if qi > 0)
                ok &= prob >= (n + 1) ** (-K_) * math.exp(-n * D) * (1 - 1e-12)
    check('L13.sanov_lower', ok, 'FLOAT: every type q of n <= 12 draws from three laws: P(type = q) >= (n + 1)^(-K) exp(-n D(q || p))')
    # X15 (item 117): sup_x (p·x - logSumExp x) = Σ p log p, attained at x = log p
    ok = True
    for _ in range(200):
        k_ = random.randint(2, 5); pv = [random.random() + 0.01 for _ in range(k_)]; s = sum(pv); pv = [v / s for v in pv]
        lse = lambda x: math.log(sum(math.exp(v) for v in x))
        target = sum(v * math.log(v) for v in pv)
        at = sum(a_ * math.log(a_) for a_ in pv) - lse([math.log(v) for v in pv])
        ok &= abs(at - target) < 1e-12
        for _ in range(50):
            x = [random.uniform(-5, 5) for _ in range(k_)]
            ok &= sum(a_ * b_ for a_, b_ in zip(pv, x)) - lse(x) <= target + 1e-12
    check('X15.conjugate', ok, 'FLOAT: for p in the open simplex, p·x - logSumExp x <= Σ p log p, with equality at x = log p (200 laws, 50 points each)')
    # D1 (item 129): variation of constants, scalar case, exact for f a polynomial times nothing: x' = a x + 1
    ok = True
    for _ in range(100):
        aa_ = Fr(random.randint(-5, 5), random.randint(1, 3))
        if aa_ == 0:
            continue
        x0 = Fr(random.randint(-5, 5)); tt = random.uniform(0, 2)
        closed = math.exp(float(aa_) * tt) * float(x0) + (math.exp(float(aa_) * tt) - 1) / float(aa_)
        N = 20000; h = tt / N
        integral = sum(math.exp(float(aa_) * (tt - (i + 0.5) * h)) * h for i in range(N))
        ok &= abs(math.exp(float(aa_) * tt) * float(x0) + integral - closed) < 1e-6
    check('D1.duhamel', ok, 'FLOAT: x\' = a x + 1: exp(t a) x0 + ∫_0^t exp((t - s) a) ds equals the closed-form solution, 100 cases, midpoint rule error < 1e-6')
    # K4 (item 148): mean hitting times, exact: h = Σ_t Q^t 1 solves h = 1 + Q h
    ok = True
    for _ in range(60):
        n = 3
        P = [[Fr(random.randint(1, 6)) for _ in range(n + 1)] for _ in range(n + 1)]
        P = [[v / sum(r) for v in r] for r in P]
        Q = [r[:n] for r in P[:n]]                                     # target = last state
        h = [sum(inverse([[Fr(int(i == j)) - Q[i][j] for j in range(n)] for i in range(n)])[i][j] for j in range(n)) for i in range(n)]
        ok &= all(h[i] == 1 + sum(Q[i][j] * h[j] for j in range(n)) for i in range(n))
        part = [Fr(0)] * n; v = [Fr(1)] * n
        for _ in range(200):
            part = [part[i] + v[i] for i in range(n)]; v = [sum(Q[i][j] * v[j] for j in range(n)) for i in range(n)]
        ok &= all(abs(float(h[i] - part[i])) < 1e-6 for i in range(n))
    check('K4.hitting', ok, 'random 4-state chains, target the last state: h = (1 - Q)^(-1) 1 solves h = 1 + Q h exactly and equals Σ_(t<200) Q^t 1 to 1e-6')
    # D2 (item 108): Lyapunov decay with P = 1 and c = -(largest eigenvalue of (A + Aᵀ)/2), 2x2, FLOAT
    def expm(A, s):
        n = len(A); R = [[float(i == j) for j in range(n)] for i in range(n)]; term = [r[:] for r in R]
        for k in range(1, 60):
            term = [[sum(term[i][l] * A[l][j] * s / k for l in range(n)) for j in range(n)] for i in range(n)]
            R = [[R[i][j] + term[i][j] for j in range(n)] for i in range(n)]
        return R
    ok = True
    for _ in range(200):
        A = [[random.uniform(-3, 1), random.uniform(-2, 2)], [random.uniform(-2, 2), random.uniform(-3, 1)]]
        Sy = [[(A[i][j] + A[j][i]) / 2 for j in range(2)] for i in range(2)]
        lmax = (Sy[0][0] + Sy[1][1]) / 2 + math.sqrt(((Sy[0][0] - Sy[1][1]) / 2) ** 2 + Sy[0][1] ** 2)
        cc = -lmax                                               # A + Aᵀ + 2c·1 is negative semidefinite
        x0 = [random.uniform(-1, 1), random.uniform(-1, 1)]
        for tt in (0.1, 0.5, 1.0, 2.0):
            E = expm(A, tt); x = [E[0][0] * x0[0] + E[0][1] * x0[1], E[1][0] * x0[0] + E[1][1] * x0[1]]
            ok &= x[0] ** 2 + x[1] ** 2 <= math.exp(-2 * cc * tt) * (x0[0] ** 2 + x0[1] ** 2) * (1 + 1e-9) + 1e-12
    check('D2.lyapunov', ok, 'FLOAT: 200 random 2x2 A, P = 1, c = -λmax((A + Aᵀ)/2): |x(t)|^2 <= e^(-2ct) |x(0)|^2 at t in {0.1, 0.5, 1, 2}')
    # H2 (item 134): projected gradient descent on a box, FLOAT
    ok = True
    for _ in range(200):
        a1, a2 = random.uniform(0.2, 3), random.uniform(0.2, 3); Lc = max(a1, a2); cpt = [random.uniform(-3, 3), random.uniform(-3, 3)]
        f = lambda x: 0.5 * (a1 * (x[0] - cpt[0]) ** 2 + a2 * (x[1] - cpt[1]) ** 2)
        proj = lambda x: [min(1.0, max(-1.0, v)) for v in x]
        z = proj(cpt)                                            # the minimiser over the box (separable)
        x0 = [random.uniform(-1, 1), random.uniform(-1, 1)]; x = x0
        for k in range(1, 40):
            g = [a1 * (x[0] - cpt[0]), a2 * (x[1] - cpt[1])]
            x = proj([x[0] - g[0] / Lc, x[1] - g[1] / Lc])
            ok &= f(x) - f(z) <= Lc * ((x0[0] - z[0]) ** 2 + (x0[1] - z[1]) ** 2) / (2 * k) + 1e-12
    check('H2.projected', ok, 'FLOAT: 200 separable quadratics on the box [-1, 1]^2, step 1/L: f(x_k) - f(z) <= L |x_0 - z|^2 / (2k), z the box minimiser, k < 40')
    # L19 (item 91): (1 - q^r)^m <= exp(-m q^r)
    ok = all((1 - qq ** r) ** m <= math.exp(-m * qq ** r) + 1e-15 for qq in (0.1, 0.3, 0.5, 0.9) for r in range(1, 8) for m in range(0, 60))
    check('L19.exp', ok, 'FLOAT: (1 - q^r)^m <= exp(-m q^r) for q in {0.1, 0.3, 0.5, 0.9}, r <= 7, m < 60')

    print('== 5d. FLOAT checks (tolerance 1e-12)')
    h2 = lambda e: 0.0 if e in (0, 1) else -e * math.log(e) - (1 - e) * math.log(1 - e)
    def mi(px, W):
        P = [[px[i] * W[i][j] for j in range(2)] for i in range(2)]
        py = [P[0][j] + P[1][j] for j in range(2)]
        return sum(P[i][j] * math.log(P[i][j] / (px[i] * py[j])) for i in range(2) for j in range(2) if P[i][j] > 0)
    ok = True
    for e in (0.05, 0.1, 0.25, 0.4):
        W = [[1 - e, e], [e, 1 - e]]; cap = math.log(2) - h2(e)
        ok &= abs(mi([0.5, 0.5], W) - cap) < 1e-12 and all(mi([t / 100, 1 - t / 100], W) <= cap + 1e-12 for t in range(1, 100))
    check('E1.bsc', ok, 'FLOAT: binary symmetric channel, ε in {0.05, 0.1, 0.25, 0.4}: I <= log 2 - h(ε) on 99 inputs, equality at (1/2, 1/2)')
    ok = True
    for _ in range(300):
        k = random.randint(2, 6)
        p0 = [random.random() + 1e-3 for _ in range(k)]; s = sum(p0); p0 = [x / s for x in p0]
        p1 = [random.random() for _ in range(k)]; s = sum(p1); p1 = [x / s for x in p1]
        kl = sum(x * math.log(x / y) for x, y in zip(p1, p0) if x > 0)
        best = sum(min(x, y) for x, y in zip(p0, p1))          # least size + (1 - power) over all tests
        ok &= best >= 0.5 * math.exp(-kl) - 1e-12
    check('X13.bretagnolle_huber', ok, 'FLOAT: 300 random pairs of laws: min over tests of size + (1 - power) = Σ min(p0, p1) >= exp(-D(p1 || p0))/2')
    ok = True
    for _ in range(300):
        n = 3
        P = [[random.random() + 0.01 for _ in range(n)] for _ in range(n)]
        P = [[x / sum(r) for x in r] for r in P]
        pi = [1 / n] * n
        for _ in range(200):
            pi = [sum(pi[i] * P[i][j] for i in range(n)) for j in range(n)]
        mu = [random.random() for _ in range(n)]; s = sum(mu); mu = [x / s for x in mu]
        D = lambda a, b: sum(x * math.log(x / y) for x, y in zip(a, b) if x > 0)
        muP = [sum(mu[i] * P[i][j] for i in range(n)) for j in range(n)]
        ok &= D(muP, pi) <= D(mu, pi) + 1e-12
    check('X8.chain_kl', ok, 'FLOAT: 300 random 3-state chains: D(μP || π) <= D(μ || π)')
    ok = True
    for _ in range(200):
        P = {}
        vals = [random.random() for _ in range(8)]; s = sum(vals)
        for idx, t in enumerate(itertools.product(range(2), repeat=3)):
            P[t] = vals[idx] / s
        H = lambda d: -sum(x * math.log(x) for x in d.values() if x > 0)
        def marg(drop):
            m = collections.defaultdict(float)
            for t, x in P.items():
                m[tuple(v for i, v in enumerate(t) if i != drop)] += x
            return m
        ok &= 2 * H(P) <= sum(H(marg(i)) for i in range(3)) + 1e-12
    check('E2.han', ok, "FLOAT: 200 random laws on {0,1}^3: (n - 1) H(X) <= Σ_i H(X without i), n = 3")
    ok = True
    for n in range(5, 41):
        for pp in (0.1, 0.3, 0.5):
            for tt in range(1, n):
                tail = sum(math.comb(n, j) * pp ** j * (1 - pp) ** (n - j) for j in range(n + 1) if j - n * pp >= tt)
                ok &= tail <= math.exp(-tt * tt / (2 * (n * pp * (1 - pp) + (1 - pp) * tt / 3))) + 1e-12
    check('B1.bernstein', ok, 'FLOAT: binomial tails, n <= 40, p in {0.1, 0.3, 0.5}: P(S - np >= t) <= exp(-t^2 / (2 (np(1-p) + (1-p) t/3)))')
    ok = True
    for _ in range(200):
        k = random.randint(2, 5); eta = random.uniform(0.1, 2)
        xt = [random.random() + 0.01 for _ in range(k)]; s = sum(xt); xt = [x / s for x in xt]
        loss = [random.random() for _ in range(k)]
        w = [x * math.exp(-eta * l) for x, l in zip(xt, loss)]; s = sum(w); w = [x / s for x in w]
        obj = lambda x: eta * sum(a * b for a, b in zip(loss, x)) + sum(a * math.log(a / b) for a, b in zip(x, xt) if a > 0)
        best = obj(w)
        for _ in range(50):
            y = [random.random() for _ in range(k)]; s = sum(y); y = [v / s for v in y]
            ok &= best <= obj(y) + 1e-12
    check('X12.mirror', ok, 'FLOAT: softmax(log x_t - η ℓ) minimises η⟨ℓ, x⟩ + D(x || x_t) against 10000 random points of the simplex')

    print('== 6. The LEAN-17 and LEAN-18 dropped-hypothesis tables (Track L, rows L5a, L5b)')
    for n, exp in (('17', (29, 25)), ('18', (27, 23))):
        t = open(os.path.join(a.lane, f'LEAN-{n}-report.md'), encoding='utf-8').read()
        sec = t.split('## Which hypotheses are needed', 1)[1].split('\n## ', 1)[0]
        rows = [l for l in sec.splitlines() if re.match(r'^\| \d', l)]
        cases = [l for l in rows if not re.search(r'\| — \|', l)]
        check(f'L5.lean{n}', (len(rows), len(cases)) == exp, f'LEAN-{n}: {exp[0]} table rows, {exp[1]} of them with a case', (len(rows), len(cases)))

    print('== 6b. Numbers quoted from the reports')
    v1 = open(os.path.join(a.lane, 'VACUITY-1-report.md'), encoding='utf-8').read()
    l26 = open(os.path.join(a.lane, 'LEAN-26-report.md'), encoding='utf-8').read()
    check('quote.v1.jobs', 'rc 0, 4166 jobs, 0 warnings' in v1 and 'PASS, 3158' in v1, 'VACUITY-1: 4166 jobs, 3158 constants')
    check('quote.v1.time', 'A full\nlibrary run takes about 3 minutes' in v1 or 'library run takes about 3 minutes' in v1.replace('\n', ' '), 'VACUITY-1: a full gate run takes about 3 minutes')
    check('quote.l26.jobs', "4160 + 4 new modules + 2 new Mathlib modules = 4166" in l26.replace('\n', ' '), 'LEAN-26: 4160 + 4 + 2 = 4166 jobs')
    check('quote.l26.methodA', 'A miss by 24' in l26, "LEAN-26: Method A missed by 24")
    pf = os.path.join(a.lane, 'MATH-PLAN-library-2-prediction.txt')
    import hashlib, datetime
    h = hashlib.sha256(open(pf, 'rb').read()).hexdigest()
    mt = datetime.datetime.fromtimestamp(os.stat(pf).st_mtime, datetime.timezone.utc).strftime('%H:%M:%S')
    check('prediction.file', h == 'a3d7046cd6b57cb0650377d753c50688b691ca2ab7997eed540685b4e0e1206e' and mt == '07:33:07', 'the prediction file has sha256 a3d7046c... and was written at 07:33:07 UTC', (h[:8], mt))

    print('== 7. Prediction against found, ranking and batches')
    ranked, deps = rank_rows()
    found = collections.Counter('L' if r['track'] == 'L' else r['track'] for r in ROWS if r['track'] != 'G')
    found['G'] = sum(1 for r in ROWS if r['track'] == 'G')
    pred = {1: 4, 2: 5, 3: 2, 4: 3, 5: 4, 6: 4, 7: 4, 8: 4, 9: 3, 10: 12, 'L': 10, 'G': 6}
    expf = {1: 3, 2: 6, 3: 3, 4: 3, 5: 5, 6: 6, 7: 6, 8: 4, 9: 2, 10: 16, 'L': 19, 'G': 9}
    check('pred.total', sum(pred.values()) == 61, 'predicted 61 rows in all', sum(pred.values()))
    check('found.table', dict(found) == expf, 'found per area/track: ' + ', '.join(f'{k} {v}' for k, v in expf.items()), dict(found))
    check('found.total', sum(found.values()) == 82, 'found 82 rows in all', sum(found.values()))
    exact_hits = sorted(str(k) for k in pred if pred[k] == found[k])
    check('pred.hits', exact_hits == ['4', '8'], 'two of the twelve row counts hit: areas 4 and 8', exact_hits)
    lb = sorted(k for k, v in deps.items() if v)
    check('rank.loadbearing', lb == ['A2', 'A3', 'H6', 'T2', 'X2', 'X3'], 'load-bearing rows: A2, A3, H6, T2, X2, X3', lb)
    ids = [r['id'] for r in ranked]
    PLAN = ['H6', 'T2', 'X2', 'A3', 'A2', 'X3',
            'L2', 'L4', 'L15', 'L18', 'L19', 'C2', 'F4', 'F5', 'X4', 'X6', 'X8', 'X16',
            'L3', 'L7', 'L9', 'L14', 'L16', 'L17', 'B3', 'B5', 'B6', 'D2', 'E4', 'E6',
            'F6', 'H1', 'H3', 'X10', 'X11', 'X12', 'X15',
            'L1', 'L5a', 'L5b', 'L12', 'L13', 'A1', 'B1', 'B2', 'B4', 'C1', 'C3', 'D1', 'E1', 'E2', 'F1', 'F3',
            'H2', 'H4', 'H5', 'K1', 'K2', 'K3', 'T1', 'X1', 'X5', 'X7', 'X13', 'X14',
            'D3', 'F2', 'K4', 'X9',
            'L6', 'L8', 'L11', 'E5']
    check('rank.order', ids == PLAN, 'the plan lists the 73 math rows in the order the rule gives', ids if ids != PLAN else '')
    pos = {x: i for i, x in enumerate(ids)}
    check('rank.deps', all(pos[d] < pos[r['id']] for r in ROWS if r['track'] != 'G' for d in r['deps']), 'every row comes after the rows it rests on')
    batches = [ids[i:i + 5] for i in range(0, 30, 5)]
    check('batches', len(batches) == 6 and all(4 <= len(b) <= 6 for b in batches), 'six batches of 5 math rows, 30 rows batched', [len(b) for b in batches])
    check('cut', len(ids) - 30 == 43, '43 math rows below the cut', len(ids) - 30)
    # item numbers: VACUITY-2 (G1..G7) 72-78, LEAN-27 79-83, LEAN-28 84-88, VACUITY-3 (G8, G9) 89-90,
    # LEAN-29..32 91-110, below the cut 111-153
    item = 72; numbering = {}
    for g in ['G1', 'G2', 'G3', 'G4', 'G5', 'G6', 'G7']:
        numbering[g] = item; item += 1
    for bi, b in enumerate(batches):
        if bi == 2:
            for g in ['G8', 'G9']:
                numbering[g] = item; item += 1
        for x in b:
            numbering[x] = item; item += 1
    for x in ids[30:]:
        numbering[x] = item; item += 1
    check('items', item - 1 == 153 and len(numbering) == 82, 'items 72 to 153, one number per row', (item - 1, len(numbering)))
    check('items.batch6', numbering[ids[29]] == 110 and numbering[ids[30]] == 111, 'batch 6 ends at item 110; the first row below the cut is item 111', (numbering[ids[29]], numbering[ids[30]]))
    print('      numbering: ' + ', '.join(f'{k} {v}' for k, v in sorted(numbering.items(), key=lambda kv: kv[1])))

    hits = sum(RESULTS)
    print(f'== {hits} of {len(RESULTS)} checks hit' + ('' if hits == len(RESULTS) else ' -- SOME MISS'))
    sys.exit(0 if hits == len(RESULTS) else 1)

if __name__ == '__main__':
    main()
