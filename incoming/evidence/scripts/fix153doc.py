"""CLOUD-MATH-2: tighten item 153's proof sketch (module docstring only). usage: fix153doc.py IN OUT"""
import sys
s = open(sys.argv[1], encoding='utf-8').read()
old = """lightest symbols get the two largest lengths, and then the two can be merged into one symbol of one
less length, with Kraft sum still at most `1` and cost, plus the two weights, at most the cost
before (`reduce_step`, `merge_step`); Huffman's recursion pays exactly the two weights at that step
(`cost_mergeLen`). The lengths"""
new = """lightest symbols get the two largest lengths, and then the two can be merged into one symbol whose
length is one less than the second largest, with Kraft sum still at most `1` and cost, plus the two
weights, at most the cost before (`reduce_step`, `merge_step`); Huffman's recursion pays exactly
the two weights at that step (`cost_mergeLen`), and the induction hypothesis, on the merged
weights and one symbol fewer, bounds the rest by the merged lengths' cost.
The lengths"""
if s.count(old) != 1:
    sys.exit('not found once')
open(sys.argv[2], 'w', encoding='utf-8').write(s.replace(old, new))
print('ok')
