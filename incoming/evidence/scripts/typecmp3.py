"""CLOUD-MATH-3 job 1 step 3 (adapted from CLOUD-MATH-2's typecmp.py): did moving into the
namespace change a meaning?

usage: python3 -I typecmp3.py DRAFT.out STMT.out DRAFT.lean STMT.lean MAP...
(`#print name` lines are read the same way, for the bodies of definitions.)
DRAFT.out and STMT.out are el.sh outputs of a draft and of its statement file, each with the same
`set_option pp.fullNames true in` / `#check @name` pairs appended, in the same order (the names
read from DRAFT.lean and STMT.lean). Each name's message is found by its first line, which starts
with `@name : ` or `name : ` (Lean writes the `@` only for a constant with implicit arguments), and
runs to the next line that starts in column 0. The two messages of each pair are compared after
three normalisations that change no meaning: (1) whitespace runs become one space (a longer name
moves the pretty printer's line breaks); (2) universe names `u_N` are renamed in the order they
first appear in each message; (3) in the draft's message only, each MAP is applied: `OLD=NEW`
replaces the whole identifier OLD by NEW, and `OLD.=NEW.` (both ending in a dot) replaces the
prefix OLD. by NEW. in front of an identifier: the draft's own declarations, renamed by the move
into the module's namespace. Prints `SAME` or `DIFF` (both texts) for each pair and a last line
`TYPECMP <same>/<total>`; exit 1 when a pair differs or a message is missing. Refuses (exit 2)
without its four file arguments (rule 28).
"""
import re, sys

if len(sys.argv) < 5:
    sys.exit(2)
dout, sout, dlean, slean = sys.argv[1:5]
maps = sys.argv[5:]


def names(lean):
    return re.findall(r'^#(?:check @|print )(\S+)\s*$', open(lean, encoding='utf-8').read(), re.M)


def is_head(l, name):
    # a `#check` message, `@name : …` or `name : …`; or a `#print` message of a definition,
    # `[private] [noncomputable] def name[.{u}] : …` (added for the bodies, CLOUD-MATH-3)
    return (l.startswith('@' + name + ' : ') or l.startswith(name + ' : ')
            or re.match(r'^(@\[[^\]]*\]\s*)?((private|noncomputable|protected) )*def '
                        + re.escape(name) + r'(\.\{[^}]*\})? : ', l) is not None)


def message(out, name, others):
    lines = open(out, encoding='utf-8').read().split('\n')
    heads = [i for i, l in enumerate(lines) if is_head(l, name)]
    if len(heads) != 1:
        return None
    i = heads[0]
    m = [lines[i]]
    body = not lines[i].startswith(('@' + name + ' : ', name + ' : '))  # a `#print` of a def
    for l in lines[i + 1:]:
        # a `#check` message ends at the next line in column 0; a `#print` message (whose body
        # starts in column 0) at the next message's head or at el.sh's `rc=` line
        if l.startswith('rc=') or any(is_head(l, o) for o in others) or (not body and not l.startswith(' ')):
            break
        m.append(l)
    return '\n'.join(m)


def norm(m):
    m = re.sub(r'\s+', ' ', m).strip()
    seen = {}

    def ren(x):
        seen.setdefault(x.group(0), f'U{len(seen) + 1}')
        return seen[x.group(0)]
    return re.sub(r'\bu_\d+\b', ren, m)


def remap(m):
    for mp in maps:
        old, new = mp.split('=')
        if old.endswith('.'):
            m = re.sub(r"(?<![\w.'])" + re.escape(old) + r"(?=[\w])", new, m)
        else:
            m = re.sub(r"(?<![\w.'])" + re.escape(old) + r"(?![\w'])", new, m)
    return m


dn, sn = names(dlean), names(slean)
bad = 0 if len(dn) == len(sn) else 1
same = 0
for a, b in zip(dn, sn):
    ma, mb = message(dout, a, dn), message(sout, b, sn)
    if ma is None or mb is None:
        bad += 1
        print(f'MISSING {a if ma is None else ""} {b if mb is None else ""}')
        continue
    na, nb = norm(remap(ma)).lstrip('@'), norm(mb).lstrip('@')
    if na == nb:
        same += 1
        print(f'SAME {b}')
    else:
        bad += 1
        print(f'DIFF {b}\n  draft: {na}\n  stmt:  {nb}')
print(f'TYPECMP {same}/{max(len(dn), len(sn))}' + ('' if len(dn) == len(sn) else f' (counts {len(dn)} and {len(sn)})'))
sys.exit(1 if bad else 0)
