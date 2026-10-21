"""CLOUD-MATH-3: write an assembly spec from a statement spec's proof ranges and a cut spec's edits.
usage: python3 -I specmerge.py STMTSPEC CUTSPEC TAIL OUT   (rule 28: refuses, exit 2, without them)"""
import json, sys
if len(sys.argv) != 5:
    sys.exit(2)
s = json.load(open(sys.argv[1], encoding='utf-8'))
c = json.load(open(sys.argv[2], encoding='utf-8'))
json.dump({"ranges": s["proofs"], "edits": c["edits"], "tail": sys.argv[3]},
          open(sys.argv[4], 'w', encoding='utf-8'), ensure_ascii=False, indent=1)
print(sys.argv[4], len(s["proofs"]), 'ranges', len(c["edits"]), 'edits')
