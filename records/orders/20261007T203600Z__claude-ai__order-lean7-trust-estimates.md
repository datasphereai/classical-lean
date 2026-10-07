<!-- Copied verbatim on 2026-10-07 from /opt/datasphere/lane/inbox/threads/staging/LEAN-7-order.md (DSMain lane; sha256 9934d38b8878a57f5c8aa9e462ca4ebd3252d18b5c8701cee5e122643a6a03b4, checked before reading), per records/README.md rule 2. Copied after the work began. -->

# LEAN-7: the next proofs the trading work needs, and a pattern scan of the library aimed at it

From claude-ai (claude-ai-58), 2026-10-07 16:36 EDT. For the same plain Claude Code session on DSMain, as dustin, after LEAN-6 is reported. Dustin's words, 16:34: "the next proof additions to the library that would be beneficial to the crypto trading. Plus the check that looks for patterns across the library that would also be beneficial for the trading algos."

Why these proofs. Your own heads-up in LEAN-6 was right: the Kelly proof shows the bet-size formula is correct, not that the win rate and payout fed into it are. Those numbers come from past trades and can be wrong. So the most useful next proofs are about how far an estimate from past data can be trusted, and what happens when it is wrong.

## Part A: pattern scan (read-only; do it first, it informs Part B)

1. Build one table of every theorem constant under ClassicalLean on master, with its module and the Mathlib concepts it uses (from the declarations' types and the constants they mention; write the script, keep it in ~/trading/paper/tools/, not in the library).
2. Mark each one by whether it touches the trading math: probability and expectation, inequalities on real numbers, logarithms and exponentials, sums and limits of sequences, convexity, counting. Count by module.
3. List pairs of modules that share rare Mathlib concepts but do not import each other, as earlier library scans did.
4. Say plainly what the scan found. Predicted (claude-ai, from LEAN-1 to LEAN-3: the library is mostly number theory): few theorems touch the trading math directly. If that holds, say so; a small number is a finding, not a failure.

## Part B: proofs, in the library, on a local branch `paper-crypto-2`

Check what Mathlib v4.34.0 already has for each before proving anything; reuse it and say so. Candidates, in this order:
1. How many past trades it takes to trust a win rate: a Hoeffding-type bound for the fraction of wins among n independent trades (the chance the estimate is off by more than e is at most 2*exp(-2*n*e^2)), and the n that makes that chance below a chosen level.
2. Betting with a wrong win rate: with true win probability p but bet size computed from an estimate q > p, the expected log growth is lower than at p's own Kelly fraction, and far enough above Kelly it turns negative. claude-ai's exact check for payout 1 found growth already below 0 at twice Kelly for p = 0.6 and p = 0.51; check other payouts with exact numbers before stating any "twice Kelly" claim, and state only what holds. This is why people bet a fraction of Kelly.
3. No system beats a fair game: if each bet's expected gain is 0 given the past, then any rule for when to stop (bounded in time) has expected final value equal to the start. Mathlib has optional stopping for martingales; state the plain-language version on top of it.
4. Gains and losses combine by multiplying, so log returns add: the log of total growth over n trades is the sum of the per-trade logs, and a +r% move followed by a -r% move loses money for any r > 0.
Take as many as fit the session, in this order. No sorry, no axiom, every gate passes, statements checked with exact numbers first, as before.

## Part C: use them

Add to ~/trading/paper: the minimum number of trades from item 1 before the program will size a bet from an estimated win rate (below it, it uses a small fixed size), and a half-Kelly option from item 2. Extend the comparison test against the Lean definitions to cover both.

## Done means

1. The scan's table (counts by module and by trading-math tag), the module pairs, and the predicted-beside-measured line from Part A step 4.
2. For each Part B item: proved here, already in Mathlib (name it), or not reached; build with 0 warnings and every gate passing, outputs shown.
3. The extended test passes, after failing once on a planted wrong value.
4. The LEAN-6 backtest re-run with these rules, beside LEAN-6's numbers.
5. A report at /opt/datasphere/lane/inbox/threads/staging/LEAN-7-report.md with the plan first, the outputs, the commits, what was not tested, and the push command for when Dustin decides. Nothing is pushed.
