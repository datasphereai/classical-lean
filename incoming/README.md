# incoming/ (order CLOUD-MATH-3)

Written by claude-ai on 2026-10-20 for order CLOUD-MATH-3. Nothing here is part of the library:
`lake build`, the gates and CI read only `ClassicalLean/`, `ClassicalLean.lean` and `tools/`.
The whole folder is removed at the merge, after its report and reviews are copied to the lane.

## The five drafts

Each was written by Claude Opus 5.5 through the Anthropic Batch API (the lane's API-CREDIT-1
work). Each compiled at master 9c0639c on DSMain on 2026-10-19 (claude-ai's recheck: rc 0, 0
errors, every planned name present, axioms only propext, Classical.choice, Quot.sound), passed the
library's vacuity gate when it was drafted, and elaborates with HANDOFF rule 20's four flags at
9c0639c with rc 0 (2026-10-20; the warnings are listed in the order's Goal list).

| item | file | sha256 | last cold review |
|---|---|---|---|
| 113 | `d113-r1-s1.lean` | `f080d16b5730724ddeb21c9072790eca7e3a7d193ac9883c3430287d6e7b29c9` | API-CREDIT-1 review r1: GENERALIZED |
| 121 | `d121-r3-s1.lean` | `d4deb84ef0f4afc343ce5dbb543d93b9689bbbfb048bfe3bac58e0a03921f33b` | API-CREDIT-1 review r1: FAITHFUL |
| 124 | `d124-r4-s2.lean` | `1d4be86a973592e972562064dfb5170afa0d10a1c1356fd3ef320e4149a1f16d` | API-CREDIT-1 review r2: FAITHFUL |
| 126 | `d126-r2-s2.lean` | `ff4f22253068e56ea0a53628dd17c16a04614728dfa97f7b26a9aec5e7b5bc11` | API-CREDIT-1 review r1: FAITHFUL |
| 130 | `d130-r1-s1.lean` | `347045bfd258b0aef5a4fbe6ff62e532c247776b470992ebcd5df72d0f753dbe` | API-CREDIT-1 review r1: FAITHFUL |

## tools/

The toolkit order CLOUD-MATH-2 used (`git show 284dd5f:incoming/tools/SHA256SUMS`), with one
change: `allowlist.txt` gains `set_option` (CLOUD-MATH-2's session added it to its own copy after
five refusals). Cloud ports of order LEAN-32's helpers on DSMain, for the rules of `HANDOFF.md`
section 6 that name them: `ev.sh` and `hl.sh` (rule 23), `el.sh` with `probecheck.py` and
`allowlist.txt` (rules 20 and 37), `rootrun.sh` (rule 38), `evcite.py` and `citecheck.py`
(rule 39), `briefcheck.py` (rule 36), `census.sh` with `census-tail.lean` and
`census-all-tail.lean` (rule 27). `test_ctools.sh` holds 41 planted-fault tests; on DSMain on
2026-10-20 all 41 passed (output sha256 `3fc1b6ebabad26085aca2e48e5d356e703eba48cfcc011dc7671f973b47cc700`, byte for byte the output CLOUD-MATH-2's copy
gave). Each file's sha256 is in `tools/SHA256SUMS`.

## witness-starts/

Written by claude-ai on 2026-10-20 for the order's rule 4: one `example` block each for items 124
and 126, to place after its module's last line once the theorem's name is its full name in the
module. Each, appended to its draft, elaborated at 9c0639c on DSMain with HANDOFF rule 20's four
flags: rc 0, no message on its own lines, no `sorry`.

| item | file | sha256 |
|---|---|---|
| 124 | `witness-starts/w124-tail.lean` | 34089c00a6510a95293c9797f6e76373b7b075e596421c4581861e79bb950a83 |
| 126 | `witness-starts/w126-tail.lean` | cc216afc65e9d9e9cf8c74f1649d34661bbfe55348c3978182affe89e2fd3109 |

## cm2-scripts/

Thirteen of the scripts order CLOUD-MATH-2's session wrote, copied byte for byte from its
`incoming/evidence/scripts/` at 284dd5f (its two item-specific fixers, `fix150.py` and
`fix153doc.py`, left out). They are starting material for the scripts this order asks for: each
still names CLOUD-MATH-2's paths, rounds and items, so read and adapt it before use. Each file's
sha256 is in `cm2-scripts/SHA256SUMS`.
