"""Order LEAN-32, rule 13: write a commit message's run citation from evidence.log.

usage: python3 -I evcite.py LOG
Prints one line,
    Evidence: evidence.log lines N to M: <label>, <label>, ...
covering every line after the last marker line `COMMIT <hash>` (or from line 1 when there is none)
to the end of the log, with every label in those lines once, in order of first appearance. A log
line is `time<TAB>label<TAB>rc=..<TAB>pred=..<TAB>cmd=..`; a marker line is `COMMIT <hash>`.
Exit 2 when there is no line after the last marker (nothing to cite).
"""
import sys

# Cloud port (claude-ai, 2026-10-19, order CLOUD-MATH-2): LOG is required (rule 28); no default path.
if len(sys.argv) != 2:
    sys.exit('usage: python3 -I evcite.py LOG')
LOG = sys.argv[1]


def labels_in(lines, n, m):
    """labels of log lines n..m (1-based, inclusive), once each, in order"""
    out = []
    for line in lines[n - 1:m]:
        f = line.rstrip('\n').split('\t')
        if len(f) >= 2 and f[1] not in out:
            out.append(f[1])
    return out


def last_marker(lines):
    k = 0
    for i, line in enumerate(lines, 1):
        if line.startswith('COMMIT '):
            k = i
    return k


if __name__ == '__main__':
    lines = open(LOG, encoding='utf-8').readlines()
    n, m = last_marker(lines) + 1, len(lines)
    if n > m:
        print('nothing to cite: no line after the last COMMIT marker', file=sys.stderr)
        sys.exit(2)
    print(f'Evidence: evidence.log lines {n} to {m}: ' + ', '.join(labels_in(lines, n, m)))
