<!-- Copied verbatim on 2026-10-07 from /opt/datasphere/lane/inbox/threads/staging/LEAN-9-order.md (DSMain lane; sha256 98ec52940b11a29fbddec9ebeb324ec276c50b8871f8287f65ba20aaba0a997e, checked before reading), per records/README.md rule 2. Copied after the work began. -->

# LEAN-9: more of the math behind the trading, proofs only

From claude-ai (claude-ai-58), 2026-10-07 17:10 EDT. For the same plain Claude Code session on DSMain, as dustin, after LEAN-8 is reported. Dustin's words, 17:07: "and what about expanding the math proofs behind the trading?"

Goal: the library proves the main facts a trading program leans on, beyond LEAN-6 to LEAN-8, so later program work can cite a theorem instead of a rule of thumb. No program changes in this order.

## The list, ranked by how much later trading work depends on it

1. **Risk of ruin.** Betting a fixed fraction x each time with win probability p and payout b: a bound on the chance the account ever falls to a set share (say half) of its start. The standard gambler's-ruin argument; check what Mathlib has first.
2. **Volatility drag.** The average of log growth is at most the log of average growth (Jensen), so swings cost money even when the average return is zero; and for returns bounded by R, a stated lower bound on log(1 + r) in terms of r and r^2 that turns this into "drag is about half the variance". State only bounds that hold exactly.
3. **Trusting a win rate when trades are not independent.** LEAN-7's 190 assumes independent trades. Prove a version for dependent trades where each trade's surprise averages to zero given the past (Azuma-Hoeffding for bounded martingale differences), and compare its n with LEAN-7's. If Mathlib lacks Azuma-Hoeffding, say how far you got and stop there; do not fake it.
4. **Two-asset mix.** Variance of a mix of two assets with weights w and 1 - w, and the weight that makes it smallest, from their variances and covariance. LEAN-7's scan found Simplex.SecondOrder and Statistics.GaussMarkov share covariance-style math without importing each other; build on whichever fits and say whether linking them helped.
5. **Fee drag over many trades.** After N round trips at fee f each way, what is left is (1 - f)^(2N) of what would have been, and the per-trade edge a rule needs to break even over N trades.
6. **Kelly for returns that are not just win or lose.** For a return r bounded in [-a, b], the growth-maximising fraction exists, is unique, and lies in a stated interval; and the "mean over variance" rule is within a stated distance of it for small returns.

Take them in this order, as many as fit. Each one: check Mathlib v4.34.0 first and reuse what is there; check the statement with exact numbers before proving it (Lean's conventions, as in earlier orders); show a hypothesis is needed by making it fail when dropped; no sorry, no axiom, every gate passes.

## Scope

- As dustin, no sudo, branch `paper-crypto-4` on top of LEAN-8's branch, worktree as before, nothing pushed.
- Ordinary math names, no trading words in module or theorem names; one docstring per theorem saying in plain words what it means for a trader.

## Done means

1. For each of the six: proved here, already in Mathlib (name it), or not reached and why.
2. lake build 0 warnings, all six checks pass, the new constant count, and `#print axioms` on each new main theorem showing only Lean's three standard axioms.
3. A one-page plain-language list at /opt/datasphere/lane/inbox/threads/staging/LEAN-9-meanings.md: each proved fact, one sentence on what it means for the trading program, and the theorem name.
4. A report at /opt/datasphere/lane/inbox/threads/staging/LEAN-9-report.md with the plan first, the outputs, the commits, what was not reached, and the push command.
