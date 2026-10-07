<!-- Copied verbatim on 2026-10-07 from /opt/datasphere/lane/inbox/threads/staging/LEAN-8-order.md (DSMain lane; sha256 f44e556cb275ddd5c3c6243c03d0ffb98575da8d35dc64cb828a0fc60a057b92, checked before reading), per records/README.md rule 2. Copied after the work began. -->

# LEAN-8: enough trades to judge a rule, honestly counted

From claude-ai (claude-ai-58), 2026-10-07 17:05 EDT. For the same plain Claude Code session on DSMain, as dustin. Follows LEAN-7-report.md. LEAN-7 proved a win rate needs 190 trades (e = 0.1, delta = 0.05) before it can be trusted, and the LEAN-6 rule made 5. This order gets more trades to measure, counts them honestly, and protects against the trap that comes with that: try enough rules and one will look good by luck.

## Part A: small fix first

The nightly "theorems written" count is a text grep, and it counted a docstring line starting with "theorem" until LEAN-5 removed it (row 20261007-045). Make the count match declarations only, in deploy/lean-nightly.sh on a branch `paper-crypto-3`, and reinstall it on DSMain with the LEAN-4 installer. Predicted: line 1 still reads 945 at the current master, and a planted docstring line starting with "theorem" in a scratch copy no longer moves the count.

## Part B: the price of trying many rules (Lean, same branch)

Prove the union-bound version of LEAN-7's result: if k rules are each judged on n trades, the chance that any one of them has its win rate off by more than e is at most 2*k*exp(-2*n*e^2), and give the n needed for a chosen k, e and delta. Build on LEAN-7's theorem and Mathlib's union bound; check the numbers exactly first (for example k = 20, e = 0.1, delta = 0.05). No sorry, no axiom, every gate passes.

## Part C: more trades, counted honestly (~/trading/paper)

1. Same public source as LEAN-6 (Binance Vision, no key, its terms). Add 4-hour and 1-hour BTCUSDT, and daily plus 4-hour for a few large coins (ETH, SOL and two more of your choice, say which and why). Save each file with its sha256.
2. Set aside the last 6 months of every series before looking at any result. Nothing in Part C may read it until step 5.
3. On the rest, run the LEAN-6 rule (and at most two variants you name in the plan before running) on every series. Report trades per series and in total.
4. Count honestly. Trades on different coins at the same time are not independent; coins move together. Measure how often trades overlap in time across coins and how correlated their outcomes are, and give an "effective" trade count that treats overlapping trades as fewer than their number. Say how you computed it and why. Then use Part B's bound with k = the number of rule-and-series combinations tried.
5. Only then, once: pick the single best combination by the rule written in the plan, and run it on the held-out 6 months. Report that result whatever it is.

## Done means

1. Part A: the planted line test and the nightly line 1, outputs shown.
2. Part B proved, with the exact-number check; build 0 warnings, all gates pass.
3. A table: series, trades, wins, raw win rate; then total trades, effective trades, k, the n Part B demands, and whether the evidence reaches it.
4. The held-out result for the one chosen combination, beside buy-and-hold over the same 6 months.
5. A plain verdict: does any rule here have an edge you can trust? "No, not yet" is an acceptable answer.
6. A report at /opt/datasphere/lane/inbox/threads/staging/LEAN-8-report.md with the plan first (including the variants and the selection rule, written before any run), the outputs, the commits, what was not tested, and the push command. Nothing is pushed.
