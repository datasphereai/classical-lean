VERDICT: CONFIRMED

# rv1c-confirm: confirming pass on the fix to rv1-statements item 121, finding 1

Reviewer: a fresh subagent, cold, on the fix only. Scratch folder `$HOME/cm3-review-2`; nothing written
inside `$REPO`. Started 2026-10-21T01:11:17Z, last check 2026-10-21T01:13:21Z.

Files checked (sha256):
- `$EVD/stmt/EfronStein.rv1.lean` e88ccf957a168a1a0718898b5850f5947504b8bc462b6a52d0a03e7f1eaaee0e
  (the file as reviewed)
- `$EVD/stmt/EfronStein.lean` 61ef53c91060881cf110aa227beace936fcc350f1eb92b9f22fe1a8bd4f0f5cb
  (the file as fixed)
- `$EVD/text/doc121mix.txt` 5c6b00b7b4cc337047279bc602c27de6f4d16053be28e4b124648da8c26a5f5a
- `$EVD/spec/s121.json` f76e59975a9c26a91d140484276c1bc0a1ea88ca02025bcffc25aebcf629a193
- `$EVD/scripts/mkstmt.py` 48b2211c775eabde43161aa94fcbf4e4c38d0c8f026be274c514d83c728f2bca
- `$REPO/incoming/d121-r3-s1.lean` d4deb84ef0f4afc343ce5dbb543d93b9689bbbfb048bfe3bac58e0a03921f33b
- `$EVD/reviews/rv1-statements.md` 6261731d78c743c5c0e153e2c782dafe1fc9dd7d1e7e07fa9d37dfa3b7970189

The `.rv1` file is the file the review read: its sha256 is the one `evidence.log` line 411 recorded for
`EfronStein.lean` at 2026-10-21T00:48:30Z, before the review (rv1-statements.md line 13 names lines
409 to 413 as the hashes it checked).

## 1. The new docstring resolves the finding and says exactly what `wvar_mix_le` states: YES

The finding (rv1-statements.md, item 121, finding 1): the old docstring
"Variance of a mixture of functions is at most the mixture of their variances." uses "mixture",
which in a probability module reads as a mixture of laws, for which the inequality goes the other way.

The new docstring (fixed file, lines 97 and 98):

```
/-- The variance of a weighted average of functions, `fun b => ∑ a, q a * H a b`, is at most the
weighted average `∑ a, q a * wvar r (H a)` of their variances. -/
```

The statement it documents (fixed file, lines 99 to 102, unchanged):

```
private lemma wvar_mix_le {α β : Type*} [Fintype α] [Fintype β] (q : α → ℝ) (r : β → ℝ)
    (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∑ a, q a = 1) (hr0 : ∀ b, 0 ≤ r b) (hr1 : ∑ b, r b = 1)
    (H : α → β → ℝ) :
    wvar r (fun b => ∑ a, q a * H a b) ≤ ∑ a, q a * wvar r (H a) := by
```

- The word "mixture" is gone. No line of the fixed file contains "mixture" (grep).
- The left side named in the docstring, the variance of `fun b => ∑ a, q a * H a b`, is the
  statement's `wvar r (fun b => ∑ a, q a * H a b)`; the right side, `∑ a, q a * wvar r (H a)`, is the
  statement's right side character for character; the relation "is at most" is `≤`.
- "weighted average" is what `hq0` and `hq1` make `q`: nonnegative weights summing to 1. The law of
  the variance is `r`, which the docstring names in `wvar r (H a)`; `hr0` and `hr1` make it a
  probability vector, as `wvar` means elsewhere in the module. The docstring claims nothing the
  statement does not give.
- It is the review's proposed fix: a script extracted the quoted text after "Proposed fix: replace
  the docstring with" from rv1-statements.md and found it equal to the new docstring's text, up to
  whitespace (the line break).
- The comment is well formed: one `/--` at its start, one `-/` at its end, none inside. Line lengths
  96 and 65 characters, under 100.

## 2. Nothing else changed: YES

- My own `diff` of the two files (rc 1) is byte-identical to the saved `$EVD/diff-121-fix.out`
  (`cmp` rc 0): one hunk, `97c97,98`, the old docstring line out and the two new lines in.
- A script built the expected file: the `.rv1` file's lines with line 97 replaced by the lines of
  `doc121mix.txt`. It equals the fixed file line for line (200 = 200 elements after the split).
  Lines 1 to 96 are identical, and fixed lines 99 onward equal `.rv1` lines 98 onward. No statement,
  definition, import, `open`, namespace or other docstring changed.
- The old line 97 is draft line 69 verbatim; draft line 70 is the `private lemma wvar_mix_le` line,
  kept, so the `replace` entry `[69, 69, ...]` covers the docstring line only.
- How it was made: I copied `mkstmt.py` and `s121.json` into my folder and ran the script there
  (`python3 -I`) on the draft:
  - with the spec as it stands: rc 0, "3 docstrings replaced, 18 proofs as sorry", 199 lines; the
    output is byte-identical to `$EVD/stmt/EfronStein.lean` (`cmp` rc 0, same sha256 61ef53c9...).
  - with the spec minus the one new entry `[69, 69, "/root/cm3-evidence/text/doc121mix.txt"], `:
    rc 0, "2 docstrings replaced, 18 proofs as sorry", 198 lines; the output is byte-identical to
    `EfronStein.rv1.lean` (sha256 e88ccf95...).
  - the spec minus that entry hashes to b1a60116c10b4d5ad15e3edde095abe094f944e83400d1f63a0d650f7cd3363d,
    the sha256 `evidence.log` recorded for `s121.json` at 00:48:30Z, before the review. So that entry is
    the spec's only change.
  - My run printed the same lines as the saved `$EVD/mkstmt-121-fix.out` (the two edits at draft
    lines 267 and 277, the counts, 199 lines).

## 3. The fixed file elaborates, rc 0, only the 18 `sorry` warnings: YES

- The saved `$EVD/stmt2-121.out`: 18 lines `warning: declaration uses `sorry``, then `rc=0`, nothing else.
- I re-ran it myself from `$REPO` with rule 20's four flags
  (`lake env lean -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3`)
  on `$EVD/stmt/EfronStein.lean`, output to my folder: rc 0, 18 `sorry` warnings, no other message.
  My output is byte-identical to `stmt2-121.out` (`cmp` rc 0).
- 18 is the spec's 18 `proofs` ranges. Against the pre-fix run `$EVD/stmt-121.out` (also 18), the
  warnings are the same with every line past 97 moved down by one, as the extra docstring line
  explains. The warning at line 99 is `wvar_mix_le`'s.
- `git --no-optional-locks status --porcelain` in `$REPO` was empty before and after my run, at
  HEAD 65c8797c33bec0fcb6645872d3d336eb4146fcdf.

## Observation (not a finding, not about the fix)

rv1-statements.md cites the module docstring's wording "the variance of an average is at most the
average of the variances" as line 41. It is on line 40 of both files. This is a line reference in the
earlier review, not a change in either file.

## Not checked

nothing

Tool calls used: 16 (including writing this report, hashing it and the hand-back).
