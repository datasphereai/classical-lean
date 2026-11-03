# Item 143 witness: of the 16 sequences of four fair flips, how many have no run of 2 / 3 trues.
from itertools import product
seqs = list(product([False, True], repeat=4))
no2 = sum(1 for s in seqs if not any(s[k] and s[k + 1] for k in range(3)))
no3 = sum(1 for s in seqs if not any(s[k] and s[k + 1] and s[k + 2] for k in range(2)))
print("sequences", len(seqs), "no run of 2:", no2, "no run of 3:", no3, "windows of 2:", 3, "windows of 3:", 2)
