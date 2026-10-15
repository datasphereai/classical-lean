# Confirming pass on the fix for ClassicalLean/Analysis/FrankWolfe.lean (item 135, finding 1)

Brief read in full; its sha256 matches (b176c1ab…128a2e). I read the diff `/home/user/classical-lean/incoming/reviews/135-fix-r1.diff` and the current module `/home/user/classical-lean/ClassicalLean/Analysis/FrankWolfe.lean`. Everything was read-only. I ran no build and no git command that writes.

**1. Does the diff fix the finding, and is every changed sentence true? Yes.**
- **Module docstring, now lines 22-24.** It reads: "on the closed simplex, read in Euclidean space, whose squared diameter is at most `2` (exactly `2` once `ι` has two elements)". This is the reviewer's proposed wording, word for word, and it is true:
  - `closedSimplex ι = {f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1}` (`ClassicalLean/Simplex/Basic.lean:75-76`).
  - The upper bound of 2 is `norm_sub_sq_le_two` (module line 123). It proves `‖a - b‖ ^ 2 ≤ 2` from `(aᵢ - bᵢ)² ≤ aᵢ + bᵢ`.
  - If `ι` has two distinct elements i ≠ j, the vertices `e_i` and `e_j` are in the simplex, and `‖e_i - e_j‖² = 1 + 1 = 2`. So the value is exactly 2.
  - If `ι` is empty, the simplex is empty, because an empty sum is 0, not 1. If `ι` has one element, the simplex is a single point with squared diameter 0. In both cases "at most 2" still holds, and "exactly 2" is correctly limited to two or more elements.
- **`sub_le_of_frankWolfe` docstring, now lines 145-146.** It reads: "`fw_general` with `D = 2`, which bounds the squared diameter of the simplex (`norm_sub_sq_le_two`)". This is also the proposed wording, and it is true. The proof at line 163 is `fw_general (D := 2) … (fun a ha b hb => norm_sub_sq_le_two ha hb)`. `norm_sub_sq_le_two` is the module's own lemma for this bound. It is `private`, but the module docstring at line 32 already cites it by the same name.
- **No claim of "exactly 2" is left anywhere.** I searched for "diameter". The other mentions (lines 19, 40, 62, 122, 247) all say "at most".

**2. Does the diff change only docstring text? Yes.**
- The diff has two hunks:
  - `@@ -20,7 +20,8 @@` is inside the `/-! … -/` module docstring. One line is replaced by two.
  - `@@ -141,8 +142,8 @@` is inside the `/-- … -/` docstring of `sub_le_of_frankWolfe`. Two lines are replaced by two. The closing `-/` moves but stays on a docstring line.
- No statement, proof, import or declaration line is a `+` or `-` line. The `theorem sub_le_of_frankWolfe …` line is unchanged context.
- **Independent check of the lines outside the hunks.** I ran `diff -u` on the pre-fix copy (`/tmp/claude-0/-home-user-classical-lean/19408406-f39d-5a72-8f6f-124d894b525a/scratchpad/review/FrankWolfe.prefix.lean`) against the current module. The hunk bodies it produced are byte-identical to the saved diff (`cmp` reports no difference). The file grew from 320 to 321 lines, which is exactly the one extra line in the first hunk.
- One limit on that check: the module is new and not in git HEAD, so the scratchpad pre-fix copy is the only "old" version available.

**3. Is any changed line over 100 characters? No.** Counted in Unicode characters with Python:

| Line | Characters |
|---|---|
| 23 | 99 |
| 24 | 45 |
| 145 | 98 |
| 146 | 69 |

The longest line in the whole module is 99 characters. A quick awk / `wc -m` check under the POSIX locale showed 100-108 for some lines, but those are byte counts inflated by multi-byte characters such as `≤`, `ι` and `‖`. They are not character counts.

## Verdict
CONFIRMED: finding 1 fixed, no new finding
