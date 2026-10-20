# Review rv1c-confirm: order CLOUD-MATH-2, job 1, the confirming pass on the fix of rv1-statements finding 1

Reviewer: a fresh subagent that had not seen the session's work or the first review before this brief. Brief `/root/cm2-evidence/briefs/rv1c-confirm.md`, sha256 `4fe324bcbf46a8afe1752702ae30f3118de4476a684db5001c6c7d0f9603b279`, checked with `sha256sum` before reading: it matches, and it matches the `brief-rv1c` line of `evidence.log`. I worked in `/root/cm2-review-2` on 2026-10-20 from 19:07 to 19:13 UTC.

## Inputs, as read

I recomputed each sha256, and each one equals its `evidence.log` line:

- `reviews/rv1-statements.md`: `2a24a4c3…6b611` (label `review-rv1`).
- `stmt/Huffman.rv1-before.lean`: `8671eee9…6aae` (label `stmt-huffman-fix`). This is also the sha256 the first review gives for the `Huffman.lean` it reviewed, so the "before" file is the reviewed file.
- `stmt/Huffman.lean`: `f82b2853…4c4c` (label `stmt-huffman-fix`).
- `stmt/Huffman.rv1-fix.diff`: `27830f4a…e65e` (label `stmt-huffman-fix`).
- `stmt4-Huffman.out`: `2ba40752…c23b` (label `stmt4-Huffman`, rc 0).

The finding, read in the review's "Findings" section, item 1, is MINOR and concerns lines 17–18. The old wording, "(`Fintype.card ι` steps, each merging the two lightest", says that every step merges. In fact the last step, which has one symbol left, takes the `else` branch and merges nothing, so `Fintype.card ι` steps make `Fintype.card ι - 1` merges.

## Check 1: the diff is exactly the change the fix claims (PASS)

- I copied the two files into my folder and ran `diff Huffman.rv1-before.lean Huffman.lean`. It returned rc 1 and printed one hunk, `17,18c17,18`, and nothing else. My output is byte-identical to `Huffman.rv1-fix.diff` (`cmp` rc 0). Here is the hunk, verbatim:

```
17,18c17,18
<   `huffAux` on finite sets of symbols (`Fintype.card ι` steps, each merging the two lightest
<   symbols, which `pick` chooses).
---
>   `huffAux` on finite sets of symbols (`Fintype.card ι` steps of the recursion; each step with
>   at least two symbols left merges the two lightest, which `pick` chooses).
```

- I also compared the files line by line with my script `scripts/textcheck.py`. Both files have 214 lines (`wc -l`), and lines 17 and 18 are the only lines that differ. Both lines are inside the module docstring, which opens with `/-!` at line 9 and closes with `-/` at line 51, and both belong to the `huffmanLength` item (lines 16–18). No code line changed, no other docstring line changed, and no whitespace changed anywhere else.
- The new parenthetical is word for word the wording the first review proposed. The script finds the proposal's text as a substring of lines 16–18 joined.

## Check 2: the new wording says what the Lean says (PASS)

What the file contains:

- `huffmanLength` is `huffAux (Fintype.card ι) p Finset.univ` (line 102).
- `huffAux` is defined at lines 91–97:
  - With count `0`, it returns `fun _ => 0`.
  - With count `n + 1` on `s`, it tests `if h : 2 ≤ s.card`.
  - The `then` branch merges `(pick w s h).2` into `(pick w s h).1` (`mergeW`), recurses with count `n` on `s.erase (pick w s h).2`, and returns `mergeLen` of the result.
  - The `else` branch returns `fun _ => 0` and does not recurse.
- `pick` is `Classical.choose (exists_pair w s h)` (line 71). The statement of `exists_pair` (lines 64–66) gives two distinct members of `s`: the first has least weight in `s`, and the second has least weight among the rest.

Why the wording holds:

- Let N = `Fintype.card ι`. The recursion starts with count N and N symbols. Each merge erases one member of `s`, so the count and the number of symbols both drop by one and stay equal.
- The steps with counts N down to 2 have at least two symbols, so they merge. The step with count 1 has one symbol, takes the `else` branch, merges nothing, and ends the recursion. When N ≥ 1 the `0` clause is never reached. When N = 0 there is no step at all.
- So the recursion takes N steps (calls of the `n + 1` clause) and makes N − 1 merges, and a step merges exactly when at least two symbols are left. That is what the new wording says.
- The phrase "the two lightest, which `pick` chooses" matches `pick`'s specification: when weights tie, `pick` chooses among them. The phrase is kept from the old wording.

Fire test (my addition). `HuffmanFire.lean` is the fixed file plus one section after its last `end`. Run `rv1c-fire1` returned rc 0, with the same 23 `sorry` warnings as the file alone and no other message. The section checks four things:

- (a) `huffmanLength p = huffAux (Fintype.card ι) p Finset.univ`, by `rfl`.
- (b) A step with `s.card < 2` returns `fun _ => 0`, that is, it merges nothing. Proved by unfolding `huffAux`.
- (c) A merge step's set, `s.erase (pick w s h).2`, has `s.card - 1` members. Proved with `Finset.card_erase_of_mem` and `pick_spec`.
- (d) Two functions with `huffAux`'s own control flow (the same clauses, the same test, the same recursive arguments): `rvSteps` counts steps and `rvMerges` counts merges. On `n` symbols with count `n`, they give `n` and `n - 1`. On `Finset.univ` with count `Fintype.card ι`, they give `Fintype.card ι` steps and `Fintype.card ι - 1` merges.

Parts (c) and (d) use `pick_spec`, which is a `sorry` in the statement file. The first review found that the draft proves it with no `sorry`.

Negative control `rv1c-fire1-control` returned rc 1. It plants two false claims in a copy of the fire file:

- In (b), the hypothesis becomes `s.card = 2`, which claims that a step with two symbols merges nothing.
- In (d), the merge count becomes `Fintype.card ι`, which is the old wording's "each".

Lean reports errors at exactly those two places and nowhere else:

- Lines 246–247: the unsolved goal it shows is the `then` branch, a merge.
- Line 287: a type mismatch, because `rvMerges_eq` gives `Fintype.card ι - 1`.

## Check 3: the new wording brings no new error into the docstring (PASS, no new finding)

- Lines 16–18 now read, joined: "* `huffmanLength` — Huffman's codeword lengths for the weights `p`, defined by the recursion `huffAux` on finite sets of symbols (`Fintype.card ι` steps of the recursion; each step with at least two symbols left merges the two lightest, which `pick` chooses)."
  - The sentence is grammatical.
  - The parenthetical still closes before the item's period, as before.
  - `huffAux`, `Fintype.card ι` and `pick` are the file's own names, as before.
- The wording agrees with the rest of the module docstring. Lines 12–13 say "repeatedly merge the two lightest symbols into one", and lines 29–30 give an induction on the number of symbols. It also agrees with `pick`'s own docstring at line 69.
- Format:
  - Line 17 has 94 characters and line 18 has 75, both within 100.
  - Neither line has trailing whitespace.
  - The backticks are balanced: 4 on line 17 and 2 on line 18.
  - The only non-ASCII character is `ι`, which was already on the old line 17.
  - The file's longest line (99 characters) is not a changed line.
- The old phrases "each merging" and "symbols, which" no longer appear anywhere in the file.
- Not counted as a finding: "the two lightest" leaves ties to `pick`. That phrase is unchanged from the wording the first review read and did not flag, and "which `pick` chooses" covers it.

## Check 4: the file still elaborates (PASS)

- Run `rv1c-huffman-el1`: I ran `el.sh` on my copy of `Huffman.lean` (sha256 `f82b2853…4c4c`, the same as `stmt/Huffman.lean`). It returned rc 0 with 23 warnings, each "declaration uses `sorry`", and no other message.
- After normalizing the file path, its output is identical to `stmt4-Huffman.out` (`diff` rc 0).

## New findings

None.

## What I wrote, and the repository

Files I created:

- In `/root/cm2-review-2`:
  - copies of the three fix files;
  - `my.diff`;
  - `HuffmanFire.lean` (`e714dd05…b631d`);
  - `HuffmanFireControl.lean` (`9707be07…916e`);
  - `scripts/textcheck.py` (`5620567d…2248`);
  - `scripts/quotecheck.py`, which checks every quote, the hunk and every abbreviated sha256 in this report against its source. It reports 0 misses, and with a planted misquote added (its `control` mode) it reports 1 miss and rc 1.
- In `/root/cm2-evidence`, only this report and the outputs `el.sh` writes itself:
  - `rv1c-huffman-el1.out` (`37d2c2f1…e9d5`);
  - `rv1c-fire1.out` (`a439569a…6419`);
  - `rv1c-fire1-control.out` (`d70fa774…e5d3`);
  - their `evidence.log` lines, 776, 795 and 797.

Commands I ran:

- Before running `el.sh` on the fire file, I ran `probecheck.py check` on it directly. That command only reads, and it printed `cleared`.
- I ran no `lake build`, no gate, and no git command that writes. My only git commands were `git status --porcelain` and `git diff`.

Repository state:

- `git status --porcelain` was empty at 19:07 UTC, when I started.
- From 19:11 UTC it shows ` M ClassicalLean.lean` (one added line, `import ClassicalLean.Analysis.PowerMethod`) and `?? ClassicalLean/Analysis/PowerMethod.lean` (mtimes 19:09:03 and 19:08:55).
- I wrote neither file. They are the session's own work on item 147, which `evidence.log` records at those times (`m147-module` at 19:09:15 and `build-147` at 19:09:23). That work is outside this brief, which covers item 153's fix only.

VERDICT: CONFIRMED
