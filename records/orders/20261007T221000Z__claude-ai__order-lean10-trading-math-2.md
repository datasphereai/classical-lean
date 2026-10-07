<!-- Copied verbatim on 2026-10-07 from /opt/datasphere/lane/inbox/threads/staging/LEAN-10-order.md (DSMain lane; sha256 ba8af947efe8d41f6b14de930b2b7fd4eb9d9929f37dab874b4be25ba602ee81, checked before reading), per records/README.md rule 2. Copied before the work began. -->

# LEAN-10: finish LEAN-9's loose ends, then the next areas of trading math

From claude-ai (claude-ai-58), 2026-10-07 18:10 EDT. For a fresh plain Claude Code session on DSMain, as dustin, in ~/lean/classical-lean. Follows LEAN-9-report.md and LEAN-9-meanings.md; read both first. Paper only; nothing pushed.

## Part A: LEAN-9's loose ends (first)

1. The "remove a hypothesis and show it breaks" check was skipped for LEAN-9 items 3 (dependent trades) and 5 (fee drag). Do it now with exact numbers, as for items 1, 2 and 6.
2. LEAN-9's ruin bound holds only when ruinConditionOK passes for the bet. In ~/trading/paper, make the program run that check on every bet it sizes, refuse to cite the ruin bound when the check fails, and say so in its output. Extend the comparison test to cover the check (a planted wrong value must fail first, as before).

## Part B: next areas, in this order, on branch `paper-crypto-5` (worktree as before)

1. **Information theory and Kelly.** For bets on one of several outcomes with true probabilities p and fair-odds-style payouts, the best growth rate is reached by betting in proportion to p, and betting by any other belief b loses exactly the relative entropy D(p || b) in growth. Use Mathlib's entropy or KL divergence if present.
2. **Many-asset mix.** For a positive-definite covariance matrix S, the weights summing to 1 with the smallest variance are S^-1 1 / (1' S^-1 1), and that variance is 1 / (1' S^-1 1). Show positive-definiteness is needed.
3. **Mean reversion.** For x(t+1) = a * x(t) + noise with |a| < 1: the steady-state variance is s^2 / (1 - a^2), and a gap from the mean halves every log(1/2) / log(a) steps (for 0 < a < 1). Show what fails at |a| >= 1.
4. **Testing many rules, less strictly.** The Benjamini-Hochberg procedure keeps the expected share of false finds at or below q when the tests are independent. If Mathlib lacks what this needs, say how far you got and stop; do not fake it.

For each: check Mathlib v4.34.0 first and reuse it; check the statement with exact numbers first; show each hypothesis is needed; no sorry, no axiom, all six checks pass; plain-words docstrings, no trading words in names.

## Done means

1. Part A: both checks done, outputs shown; the program's ruin check runs per bet and its test passes after failing once on a planted value.
2. Part B: for each item, proved here, already in Mathlib (name it), or not reached and why. lake build 0 warnings, all six checks pass, the new constant count, `#print axioms` on each new main theorem.
3. LEAN-9-meanings.md's format continued in /opt/datasphere/lane/inbox/threads/staging/LEAN-10-meanings.md.
4. A report at /opt/datasphere/lane/inbox/threads/staging/LEAN-10-report.md with the plan first, outputs, commits, what was not reached, and the push command.
5. Close with the close-session skill (lane copy /opt/datasphere/lane/inbox/threads/SKILL-close-session.md, sha256 5f2a4671662e3142ac6b94ec40e77a4cd4aadd32341f6c67c2e1f2c6286a0d5d): the note at /opt/datasphere/lane/inbox/threads/staging/LEAN-10-CLOSE.md and its DONE file beside it.
