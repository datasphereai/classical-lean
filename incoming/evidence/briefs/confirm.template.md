# Brief: the confirming pass on the fix of review `{REVIEW}`, order CLOUD-MATH-2 (review `{LABEL}`)

Written on {DATE} by the Claude Code cloud session executing order CLOUD-MATH-2. Your run ends by
{END}: have your report written before then.

You are a fresh reviewer: you have not seen this session's work, nor the review whose findings were
fixed. A cold review of a new module of the Lean library `classical-lean` found the findings below,
and the session fixed them. Your task is the fix only: is each finding fixed, and did the fix change
anything else or bring a new error?

## The findings

Read them in the review itself, `/root/cm2-evidence/reviews/{REVIEW}.md`, section "Findings":
{FINDINGS}. The review is saved with its sha256 in the session's evidence log
(`/root/cm2-evidence/evidence.log`, label `review-{REVIEW}`).

## The fix

- the module as reviewed: `{BEFORE}`;
- the module now: `{AFTER}`;
- their `diff`: `{DIFF}` (hashed in the evidence log);
- {RUNS}.

{EXTRA}

## What you check

1. The diff is exactly what the fix claims: each hunk belongs to one of the findings or to the
   change named above, and nothing else changed (recompute the diff yourself).
2. Each finding is fixed: the new text says what the Lean says.
3. The new text brings no new error, in what it says or in the build (0 warnings, rc 0).

## How you work

- Work in your own scratch folder, `/root/cm2-review-{N}` (create it). Start every Bash command with
  `. $HOME/cm2-env.sh && `. Copy any repository script into your folder before you import it.
  Write nothing in the repository, and nothing in `/root/cm2-evidence` except your report and the
  outputs that `el.sh` writes there itself.
- To elaborate a Lean file, copy it into your folder and run `$T/el.sh <label> <file>` with a label
  that starts with `{LABEL}-` and is new each time.
- Do not run `lake build`, the gates, or any git command that writes.

## Your report

Write it to `/root/cm2-evidence/reviews/{LABEL}.md`: each of the three checks with what you found;
any new finding, numbered, with a severity (BLOCKING or MINOR) and the line; as its last line
`VERDICT: CONFIRMED` if every finding is fixed and you have no new finding, else
`VERDICT: NOT CONFIRMED <reason>`. Then return only that file's sha256 (the first field `sha256sum`
prints), and nothing else.
