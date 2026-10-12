#!/usr/bin/env python3
"""The bridge search, as a tool any order can re-run (order VACUITY-2, decision A of 2026-10-11).

A *bridge* is a theorem whose proof must use two library modules that do not import each other,
through an object they share. This script finds candidates for one, in two parts, exactly as
MATH-PLAN-library-2-checks.py does:

1. shared constants: for every pair of library modules with no import path between them, the
   Mathlib constants both use, kept by the same filters (not an instance, not a projection or
   tactic internal, used by at most 10 modules), scored by the sum of log(N / df);
2. shared shapes: the modules whose source matches each regular expression in `SHAPES`.

Usage (from the repository root, on a clean tree; it loads the whole library through Lean):

  python3 -I tools/bridge_search.py --out DIR
  python3 -I tools/bridge_search.py --diff OLD_DIR [--out DIR]

It writes into DIR (a scratch folder when --out is not given):

* `pairs.tsv`: every import-unrelated pair that shares a kept constant: rank, score, module x,
  module y, the number of shared kept constants, the constants (comma-separated);
* `shapes.tsv`: every shape candidate: shape, module x, module y, `related` or `unrelated`;
* `COMMIT`: the commit it ran on.

`--diff OLD_DIR` compares by key only: a pair by (x, y), a shape candidate by (shape, x, y),
never by the whole row, since every score and rank moves when a module is added. It prints each
key present now and absent from OLD_DIR (NEW) and each key gone (GONE). Exit 0 when there are
none, 1 when there are some: exit 1 means "candidates to review", not a failed gate. Exit 2 on
an error (Lean failed, a dirty tree, a score that does not match).

The Lean source `LEAN_USED` and the functions `run_lean`, `bridge_pairs`, `import_graph`,
`SHAPES` and `shape_modules` are copied unchanged from MATH-PLAN-library-2-checks.py (sha256
92eedbc6598361a06a50bdf3a1b4fa1698c1d1d7a3dfe783cc79dd9c1c38307e, lines 167 to 195 and 285 to
369). `shared_constants` is added: it lists, for each pair, the shared kept constants, and
asserts that their score equals the score `bridge_pairs` gave the pair.
"""
import argparse, collections, math, os, re, subprocess, sys, tempfile

# ---------------------------------------------------------------- copied unchanged from MATH-PLAN-library-2-checks.py
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
# ---------------------------------------------------------------- end of the copy


def shared_constants(used_path, repo, N, pairs, maxdf=10):
    """For each pair `(score, x, y)` of `bridge_pairs`, the shared kept constants that count toward
    its score: read with the same skip pattern, the same kind split and the same df bound as
    `bridge_pairs`. Asserts that the score recomputed from them equals the pair's score."""
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
    assert len(mods) == N, f'{len(mods)} modules here, {N} in bridge_pairs'
    df = {k: collections.Counter(c for m in mods for c in uses[m][k]) for k in ('obj', 'thm')}
    out = {}
    for s, x, y in pairs:
        a, b = 'ClassicalLean.' + x, 'ClassicalLean.' + y
        shared, sc = [], 0.0
        for k in ('obj', 'thm'):
            cs = [c for c in uses[a][k] & uses[b][k] if df[k][c] <= maxdf]
            sc += sum(math.log(N / df[k][c]) for c in cs)
            shared += cs
        assert round(sc, 1) == s, f'{x} x {y}: shared constants score {round(sc, 1)}, bridge_pairs {s}'
        out[(x, y)] = sorted(shared)
    return out


def search(repo, out_dir):
    """Run both parts on the tree at `repo` and write pairs.tsv, shapes.tsv and COMMIT."""
    dirty = subprocess.run(['git', '-C', repo, 'status', '--porcelain', '--untracked-files=no'],
                           capture_output=True, text=True).stdout.strip()
    if dirty:
        sys.exit('refusing: tracked files are changed, so no commit names this tree:\n' + dirty)
    head = subprocess.run(['git', '-C', repo, 'rev-parse', 'HEAD'], capture_output=True,
                          text=True).stdout.strip()
    tmp = tempfile.mkdtemp(prefix='bridges-')
    used = os.path.join(tmp, 'used.tsv')
    rc, log = run_lean(repo, LEAN_USED.replace('OUTFILE', used), tmp, 'UsedConsts.lean')
    if rc != 0 or not os.path.exists(used):
        sys.exit(f'refusing: UsedConsts failed (rc {rc}):\n{log[-2000:]}')
    N, pairs = bridge_pairs(used, repo)
    shared = shared_constants(used, repo, N, pairs)
    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(out_dir, 'pairs.tsv'), 'w', encoding='utf-8') as f:
        f.write(f'# {len(pairs)} import-unrelated pairs sharing a kept constant; N = {N} modules\n')
        f.write('# rank\tscore\tmodule x\tmodule y\tshared\tconstants\n')
        for i, (s, x, y) in enumerate(pairs):
            cs = shared[(x, y)]
            f.write(f'{i + 1}\t{s}\t{x}\t{y}\t{len(cs)}\t{",".join(cs)}\n')
    sh = shape_modules(repo)
    imp, clo = import_graph(repo)
    rows = []
    for name in SHAPES:
        ms = sorted(sh[name])
        for i, x in enumerate(ms):
            for y in ms[i + 1:]:
                rel = 'unrelated' if x not in clo.get(y, ()) and y not in clo.get(x, ()) else 'related'
                rows.append((name, x, y, rel))
    with open(os.path.join(out_dir, 'shapes.tsv'), 'w', encoding='utf-8') as f:
        f.write(f'# {len(rows)} shape candidates ({sum(r[3] == "unrelated" for r in rows)} unrelated)\n')
        f.write('# shape\tmodule x\tmodule y\trelation\n')
        for r in rows:
            f.write('\t'.join(r) + '\n')
    with open(os.path.join(out_dir, 'COMMIT'), 'w', encoding='utf-8') as f:
        f.write(head + '\n')
    print(f'{len(pairs)} pairs, {len(rows)} shape candidates, N = {N}, at {head[:7]}, in {out_dir}')
    return out_dir


def keys(d):
    """The keys of a result folder: ('pair', x, y) and ('shape', shape, x, y)."""
    ks = set()
    for line in open(os.path.join(d, 'pairs.tsv'), encoding='utf-8'):
        if line.startswith('#') or not line.strip():
            continue
        f = line.rstrip('\n').split('\t')
        ks.add(('pair', f[2], f[3]))
    for line in open(os.path.join(d, 'shapes.tsv'), encoding='utf-8'):
        if line.startswith('#') or not line.strip():
            continue
        f = line.rstrip('\n').split('\t')
        ks.add(('shape', f[0], f[1], f[2]))
    return ks


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--repo', default=os.getcwd())
    ap.add_argument('--out', help='folder to write into (default: a scratch folder)')
    ap.add_argument('--diff', metavar='OLD_DIR', help='compare the keys found now with OLD_DIR')
    a = ap.parse_args()
    repo = os.path.abspath(a.repo)
    if a.diff and not os.path.exists(os.path.join(a.diff, 'pairs.tsv')):
        sys.exit(f'refusing: {a.diff} has no pairs.tsv')
    out = search(repo, a.out or tempfile.mkdtemp(prefix='bridges-out-'))
    if not a.diff:
        return 0
    old, new = keys(a.diff), keys(out)
    added, gone = sorted(new - old), sorted(old - new)
    for k in added:
        print('NEW ', k[0], ' x '.join(k[1:]) if k[0] == 'pair' else f'{k[1]}: {k[2]} x {k[3]}')
    for k in gone:
        print('GONE', k[0], ' x '.join(k[1:]) if k[0] == 'pair' else f'{k[1]}: {k[2]} x {k[3]}')
    print(f'against {a.diff} (commit {open(os.path.join(a.diff, "COMMIT")).read().strip()[:7]}): '
          f'{len(added)} new, {len(gone)} gone' + (' (candidates to review)' if added or gone else ''))
    return 1 if added or gone else 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except AssertionError as e:
        print('score assertion failed:', e, file=sys.stderr)
        sys.exit(2)
