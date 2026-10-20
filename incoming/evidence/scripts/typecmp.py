"""CLOUD-MATH-2 job 1 step 3: did moving into the namespace change a meaning?

usage: python3 -I typecmp.py DRAFT.out STMT.out MAP...
DRAFT.out and STMT.out are el.sh outputs of a draft and of its statement file, each with
`set_option pp.fullNames true` and the same `#check @name` / `#print name` lines appended, in the same
order. The messages after the set_option warning are compared one by one, after three
normalisations that change no meaning: (1) whitespace runs become one space (a longer name moves
the pretty printer's line breaks); (2) universe names `u_N` are renamed in the order they first
appear in each message (`#check` names a constant's universes afresh); (3) in the draft's message
only, each MAP is applied: `OLD=NEW` replaces the whole identifier OLD by NEW, and `OLD.=NEW.`
(both ending in a dot) replaces the prefix OLD. by NEW. in front of an identifier. These are the
draft's own declarations, renamed by the move into the module's namespace. Prints `SAME` or `DIFF`
(both texts) for each message pair and a last line `TYPECMP <same>/<total>`; exit 1 when a pair
differs or the message counts differ.
"""
import re, sys

if len(sys.argv) < 3:
    sys.exit('usage: python3 -I typecmp.py DRAFT.out STMT.out MAP...')
START = re.compile(r'^(@|def |theorem |private def |private theorem |noncomputable def |opaque )')


def messages(path):
    lines = open(path, encoding='utf-8').read().split('\n')
    k = max(i for i, l in enumerate(lines) if 'linter.style.setOption false' in l)
    msgs, cur = [], None
    for l in lines[k + 1:]:
        if l.startswith('rc='):
            break
        if START.match(l):
            if cur is not None:
                msgs.append(cur)
            cur = l
        elif cur is not None:
            cur += '\n' + l
    if cur is not None:
        msgs.append(cur)
    return msgs


def norm(m):
    m = re.sub(r'\s+', ' ', m).strip()
    seen = {}
    def ren(x):
        seen.setdefault(x.group(0), f'U{len(seen) + 1}')
        return seen[x.group(0)]
    return re.sub(r'\bu_\d+\b', ren, m)


def remap(m, maps):
    for mp in maps:
        old, new = mp.split('=')
        if old.endswith('.'):
            m = re.sub(r"(?<![\w.'])" + re.escape(old) + r"(?=[\w])", new, m)
        else:
            m = re.sub(r"(?<![\w.'])" + re.escape(old) + r"(?![\w'])", new, m)
    return m


d, s = messages(sys.argv[1]), messages(sys.argv[2])
maps = sys.argv[3:]
bad = 0 if len(d) == len(s) else 1
same = 0
for i, (a, b) in enumerate(zip(d, s)):
    na, nb = norm(remap(a, maps)), norm(b)
    head = nb.split(' ')[0] if not nb.startswith(('def', 'private')) else ' '.join(nb.split(' ')[:3])
    if na == nb:
        same += 1
        print(f'SAME {i + 1}: {head}')
    else:
        bad += 1
        print(f'DIFF {i + 1}: {head}\n  draft: {na}\n  stmt:  {nb}')
print(f'TYPECMP {same}/{max(len(d), len(s))}' + ('' if len(d) == len(s) else f' (counts {len(d)} and {len(s)})'))
sys.exit(1 if bad else 0)
