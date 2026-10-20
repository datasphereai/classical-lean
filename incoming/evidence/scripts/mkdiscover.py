"""CLOUD-MATH-2, job 1 step 1: find the full names of the constants a draft uses.

usage: python3 -I mkdiscover.py OUT.lean DRAFT.lean
Writes OUT.lean: the draft's import lines and top-level `open` lines (each `open ... in` line kept
as a plain `open`), then a `run_cmd` that tries to resolve every identifier of the draft (comments,
docstrings and string literals removed first, as probecheck.py does) as a global constant, and for a
dotted identifier also each shorter dot-prefix. It prints `FULL <ident> <full name>` for the longest
prefix that resolves, or `NONE <ident>`. Nothing is probed by this file (it has no `#check` line);
the probe file is written from its output.
"""
import re, sys

if len(sys.argv) != 3:
    sys.exit('usage: python3 -I mkdiscover.py OUT.lean DRAFT.lean')
out_path, draft = sys.argv[1], sys.argv[2]


def strip(text):
    # the same blanking of comments, docstrings and strings as probecheck.py
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


raw = open(draft, encoding='utf-8').read()
code = strip(raw)
imports = [l for l in code.split('\n') if re.match(r'^import\s', l)]
opens = []
for l in code.split('\n'):
    m = re.match(r'^\s*open\s+(.*?)(\s+in)?\s*$', l)
    if m:
        opens.append('open ' + m.group(1))
names = []
for l in code.split('\n'):
    if re.match(r'^\s*(import|open)\b', l):
        continue
    for t in idents(l):
        if t not in names:
            names.append(t)


def lean_name(s):
    # a Name literal component by component, each in «» so that primes and subscripts are safe
    return '`' + '.'.join('«' + p + '»' for p in s.split('.'))


lines = imports + [''] + opens + ['', 'open Lean Elab Command in', 'run_cmd do']
lines.append('  let cands : List (String × List Name) := [')
items = []
for t in names:
    parts = t.split('.')
    prefs = ['.'.join(parts[:k]) for k in range(len(parts), 0, -1)]
    items.append('    ("' + t + '", [' + ', '.join(lean_name(p) for p in prefs) + '])')
lines.append(',\n'.join(items))
lines.append('  ]')
lines += [
    '  for (s, ps) in cands do',
    '    let mut found := false',
    '    for p in ps do',
    '      unless found do',
    '        try',
    '          let n ← liftCoreM (realizeGlobalConstNoOverload (mkIdent p))',
    '          logInfo m!"FULL {s} {n}"',
    '          found := true',
    '        catch _ => pure ()',
    '    unless found do logInfo m!"NONE {s}"',
]
open(out_path, 'w', encoding='utf-8').write('\n'.join(lines) + '\n')
print(f'{out_path}: {len(names)} identifiers, {len(opens)} open lines, {len(imports)} imports')
