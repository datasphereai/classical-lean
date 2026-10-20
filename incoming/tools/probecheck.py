r"""Order LEAN-31, rule 10: a name is probed before the text that uses it.

usage: python3 -I probecheck.py check FILE        exit 0: every token cleared; exit 4: some not
       python3 -I probecheck.py record LABEL FILE  after a run with rc 0: print one PROBED line per
                                                   `#check` name in FILE, for evidence.log
       python3 -I probecheck.py tokens FILE        print FILE's tokens (for writing the seed file)

The text: for a file under the worktree's ClassicalLean/ (or ClassicalLean.lean), only the lines
added or changed against $BASE (`git diff -U0 $BASE -- FILE`, the new side's line numbers);
for any other file (a scratch draft), the whole file. Comments, docstrings and string literals are
removed first (over the whole file, so a changed line inside a docstring is not code). Lines
starting with `import`, `open`, `namespace`, `end`, `section`, `#check`, `#print` are not read.
The tokens: identifiers containing `.` or `_` (a lone `_` is not one).
A token is cleared when: it or a dot-prefix of it is a probed full name (a PROBED line of
evidence.log, or a line of seed.txt); some probed full name ends in `.` + the token or a dot-prefix of it (`Finset.univ` clears
`univ.filter` under `open Finset`; the rest is field notation, as for a bound local); its first
component is a name the text binds (a binder `(h : …)`, `{x y : …}`, `[i : …]` in a declaration's header or a `variable` line, a named argument
`(x := …)`, or a name after `have`, `let`, `set`, `obtain`, `rintro`, `intro`, `intros`,
`fun`, `∀`, `∃`, `∑`, `∏`, `⋃`, `⋂`, `⨆`, `⨅` (up to `∈`, `,`, `:`), `choose`, `with` (so `rcases t with p`, `cases t with p` bind only `p`, not `t`; review r101), `by_cases`, `funext`, `ext`, up to the
next `:=`, `:`, `↦`, `=>`, `using`, `from`, `;` or end of line, and for `fun`, `∀`, `∃` also `,`); it is a name the text
declares (`theorem`, `lemma`, `def`, `abbrev`, `structure`, `instance`), as written or with the
file's namespace in front, or a suffix of such a full name; or it is in allowlist.txt (one token
per line, a tab, the reason).
"""
import os, re, subprocess, sys

# Cloud port (claude-ai, 2026-10-19, order CLOUD-MATH-2): the three paths come from the environment
# (EVD the evidence directory, REPO the clone's root, BASE the branch's base commit) and the
# script refuses to run without them (rule 28); everything below is LEAN-32's d19ec3c6 unchanged.
for _v in ('EVD', 'REPO', 'BASE'):
    if not os.environ.get(_v):
        sys.exit(f'probecheck.py: set {_v}')
D = os.environ['EVD']
REPO = os.path.abspath(os.environ['REPO'])
BASE = os.environ['BASE']


def strip(text):
    """Blank out comments, docstrings and string literals, keeping every newline."""
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        two = text[i:i + 2]
        if depth:
            if two == '/-':
                depth += 1; i += 2; out.append('  ')
            elif two == '-/':
                depth -= 1; i += 2; out.append('  ')
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif two == '/-':
            depth = 1; i += 2; out.append('  ')
        elif two == '--':
            j = text.find('\n', i); j = n if j < 0 else j
            out.append(' ' * (j - i)); i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            out.append(''.join('\n' if c == '\n' else ' ' for c in text[i:j + 1])); i = j + 1
        else:
            out.append(text[i]); i += 1
    return ''.join(out)


def is_start(c):
    return c.isalpha() or c == '_'


def is_body(c):
    return c.isalnum() or c in "_'!?" or '₀' <= c <= 'ₜ'


def idents(line):
    """Identifiers with their dotted components, e.g. `Finset.sum_le_sum`, `hq0.trans_lt`."""
    res, i, n = [], 0, len(line)
    while i < n:
        c = line[i]
        if is_start(c) and (i == 0 or not is_body(line[i - 1])):
            j = i
            while True:
                while j < n and is_body(line[j]):
                    j += 1
                if j + 1 < n and line[j] == '.' and is_start(line[j + 1]):
                    j += 1
                    continue
                break
            res.append(line[i:j]); i = j
        else:
            i += 1
    return res


SKIP = re.compile(r'^\s*(import|open|namespace|end|section|#check|#print)\b')
DECL = re.compile(r'\b(?:theorem|lemma|def|abbrev|structure|instance|class|inductive)\s+([^\s(\[{:]+)')
NS = re.compile(r'^\s*namespace\s+(\S+)')
KW = ('have', 'let', 'set', 'obtain', 'rintro', 'intro', 'intros', 'fun', '∀', '∃',
      'choose', 'with', 'by_cases', 'funext', 'ext', 'λ',
      '∑', '∏', '⋃', '⋂', '⨆', '⨅')
STOP = re.compile(r':=|:|↦|=>|,|\busing\b|\bfrom\b|;')
STOP_BIG = re.compile(r'∈|,|:|\(')  # the bound name of a big operator, `∑ i ∈ s, …`, `⋃ i, …`
STOP_PAT = re.compile(r':=|:|↦|=>|\busing\b|\bfrom\b|;')  # a pattern ⟨a, b⟩ runs past commas
BINDER = re.compile(r'[(\[{⦃]\s*([^\s:()\[\]{}⦃⦄,]+(?:\s+[^\s:()\[\]{}⦃⦄,]+)*)\s*:(?!=)')
NAMED = re.compile(r'\(\s*([^\s:()]+)\s*:=')


def bound_names(code):
    names = set()
    # declaration binders only: from a declaration keyword to the first `:=` after it, so that a
    # type ascription `(c : T)` inside a proof does not count as binding `c`
    for h in re.finditer(r'\b(?:theorem|lemma|def|abbrev|instance|variable)\b(.*?)(?::=|\bwhere\b|$(?![\s\S]))',
                         code, re.S):
        for m in BINDER.finditer(h.group(1)):
            names.update(m.group(1).split())
    for m in NAMED.finditer(code):
        names.add(m.group(1))
    for line in code.split('\n'):
        for kw in KW:
            for m in re.finditer(r'(?<![\w.])' + re.escape(kw) + r'(?![\w])', line):
                rest = line[m.end():]
                s = (STOP_BIG if kw in '∑∏⋃⋂⨆⨅' else STOP if kw in ('fun', 'λ', '∀', '∃') else STOP_PAT).search(rest)
                seg = rest[:s.start()] if s else rest
                for t in idents(seg):
                    names.add(t)
    return names


def declared(code):
    full, ns = set(), []
    for line in code.split('\n'):
        m = NS.match(line)
        if m:
            ns.append(m.group(1))
        elif re.match(r'^\s*section\b', line):
            ns.append(None)
        elif re.match(r'^\s*end\b', line) and ns:
            ns.pop()
        cur = [n for n in ns if n]
        for d in DECL.finditer(line):
            full.add(d.group(1))
            if cur:
                full.add('.'.join(cur) + '.' + d.group(1))
    return full


def changed_lines(path):
    rel = os.path.relpath(os.path.abspath(path), REPO)
    out = subprocess.run(['git', '-C', REPO, 'diff', '-U0', BASE, '--', rel],
                         capture_output=True, text=True, check=True).stdout
    if not out:
        tracked = subprocess.run(['git', '-C', REPO, 'ls-files', '--error-unmatch', rel],
                                 capture_output=True).returncode == 0
        if not tracked:
            return None
    lines = set()
    for m in re.finditer(r'^@@ -\S+ \+(\d+)(?:,(\d+))? @@', out, re.M):
        a, b = int(m.group(1)), int(m.group(2) or 1)
        lines.update(range(a, a + b))
    return lines


def is_module(path):
    a = os.path.abspath(path)
    return a.startswith(REPO + '/ClassicalLean/') or a == REPO + '/ClassicalLean.lean'


def probed():
    names = set()
    log = os.path.join(D, 'evidence.log')
    if os.path.exists(log):
        for line in open(log, encoding='utf-8'):
            m = re.search(r'cmd=PROBED (\S+)', line)
            if m:
                names.add(m.group(1))
    seed = os.path.join(D, 'seed.txt')
    if os.path.exists(seed):
        names.update(l.strip() for l in open(seed, encoding='utf-8') if l.strip())
    return names


def allow():
    p = os.path.join(D, 'allowlist.txt')
    if not os.path.exists(p):
        return set()
    return {l.split('\t')[0].strip() for l in open(p, encoding='utf-8') if l.strip() and not l.startswith('#')}


def tokens(path):
    raw = open(path, encoding='utf-8').read()
    code = strip(raw)
    lines = code.split('\n')
    keep = None
    if is_module(path):
        keep = changed_lines(path)
    toks = []
    for i, l in enumerate(lines, 1):
        if keep is not None and i not in keep:
            continue
        if SKIP.match(l):
            continue
        for t in idents(l):
            if ('.' in t or '_' in t) and t.strip('_'):
                toks.append((i, t))
    return code, toks


def check(path):
    code, toks = tokens(path)
    P, A = probed(), allow()
    keep = changed_lines(path) if is_module(path) else None
    text = code if keep is None else '\n'.join(l if i in keep else '' for i, l in enumerate(code.split('\n'), 1))
    # declarations: only those in the text (for a module, its changed lines), as rule 10 says;
    # namespaces and sections are read from the whole file so full names come out right
    full_all = declared(code)
    in_text = {m.group(1) for m in DECL.finditer(text)}
    F = {f for f in full_all if any(f == d or f.endswith('.' + d) for d in in_text)}
    B = bound_names(text)
    bad = []
    for i, t in toks:
        parts = t.split('.')
        prefixes = {'.'.join(parts[:k]) for k in range(1, len(parts) + 1)}
        ok = (prefixes & P or any(p.endswith('.' + q) for p in P for q in prefixes) or parts[0] in B or t in A
              or t in F or any(f.endswith('.' + t) for f in F)
              or any('.'.join(parts[:k]) in F for k in range(1, len(parts))))
        if not ok:
            bad.append((i, t))
    return bad


if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'check':
        bad = check(sys.argv[2])
        seen = sorted({t for _, t in bad})
        if seen:
            print('NOT CLEARED: ' + ' '.join(seen))
            sys.exit(4)
        print('cleared')
    elif mode == 'record':
        label, path = sys.argv[2], sys.argv[3]
        code = strip(open(path, encoding='utf-8').read())
        for m in re.finditer(r'^\s*#check\s+@?([^\s(]+)', code, re.M):
            print(m.group(1))
    elif mode == 'tokens':
        _, toks = tokens(sys.argv[2])
        for t in sorted({t for _, t in toks}):
            print(t)
