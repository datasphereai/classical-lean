"""Order LEAN-32, rule 13: compare each commit's `Evidence:` line with evidence.log.

usage: python3 -I citecheck.py LOG REPO BASE        every commit in BASE..HEAD of REPO
       python3 -I citecheck.py LOG --message FILE HASH   one planted message, as if committed as HASH
For a commit with marker line `COMMIT <hash>` in LOG (its full or short hash), the expected range
runs from the line after the previous marker to the line before its own marker. Its message's
`Evidence: evidence.log lines N to M: L1, L2, ...` line must start at that range's first line, and
its labels must equal the labels of lines N..M exactly (every label once, none left out, none
added). Log lines after M and before the commit's own marker are reported unless their label starts
with `commit-` (the commit's own logged command). Prints one line per commit, `OK <hash>` or
`DIFF <hash>: <each difference>`, or `NO-EVIDENCE <hash>` for a message with no Evidence line,
and exits 1 when any DIFF is printed, else 0.
"""
import re, subprocess, sys

EV = re.compile(r'^Evidence: evidence\.log lines (\d+) to (\d+): (.*)$')


def labels_in(lines, n, m):
    out = []
    for line in lines[n - 1:m]:
        f = line.rstrip('\n').split('\t')
        if len(f) >= 2 and f[1] not in out:
            out.append(f[1])
    return out


def markers(lines):
    return [(i, line.split()[1]) for i, line in enumerate(lines, 1) if line.startswith('COMMIT ')]


def check(lines, msg, h):
    mk = markers(lines)
    pos = [k for k, (_, x) in enumerate(mk) if x.startswith(h) or h.startswith(x)]
    ev = [EV.match(l) for l in msg.splitlines()]
    ev = [e for e in ev if e]
    if not ev:
        return 'NO-EVIDENCE', []
    e = ev[-1]
    n, m, cited = int(e.group(1)), int(e.group(2)), [c.strip() for c in e.group(3).split(',') if c.strip()]
    diffs = []
    if not pos:
        diffs.append(f'no COMMIT marker for {h} in the log')
        start, own = None, None
    else:
        k = pos[0]
        start = mk[k - 1][0] + 1 if k > 0 else 1
        own = mk[k][0]
        if n != start:
            diffs.append(f'range starts at line {n}, the previous marker ends at line {start - 1}')
        if m >= own:
            diffs.append(f'range ends at line {m}, at or after its own marker (line {own})')
        else:
            for i in range(m + 1, own):
                f = lines[i - 1].rstrip('\n').split('\t')
                if len(f) >= 2 and not f[1].startswith('commit-'):
                    diffs.append(f'line {i} ({f[1]}) after the range and before the marker is not cited')
    actual = labels_in(lines, n, m)
    for a in actual:
        if a not in cited:
            diffs.append(f'label left out: {a}')
    for c in cited:
        if c not in actual:
            diffs.append(f'label not in lines {n} to {m}: {c}')
    return ('DIFF' if diffs else 'OK'), diffs


if __name__ == '__main__':
    log = sys.argv[1]
    lines = open(log, encoding='utf-8').readlines()
    bad = 0
    if sys.argv[2] == '--message':
        items = [(sys.argv[4], open(sys.argv[3], encoding='utf-8').read())]
    else:
        repo, base = sys.argv[2], sys.argv[3]
        hs = subprocess.run(['git', '-C', repo, 'rev-list', '--reverse', f'{base}..HEAD'],
                            capture_output=True, text=True, check=True).stdout.split()
        items = [(h, subprocess.run(['git', '-C', repo, 'log', '-1', '--format=%B', h],
                                    capture_output=True, text=True, check=True).stdout) for h in hs]
    for h, msg in items:
        verdict, diffs = check(lines, msg, h)
        bad += verdict == 'DIFF'
        print(f'{verdict} {h[:7]}' + (': ' + '; '.join(diffs) if diffs else ''))
    sys.exit(1 if bad else 0)
