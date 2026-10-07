<!-- Copied verbatim on 2026-10-07 from /opt/datasphere/lane/inbox/threads/staging/LEAN-6-order.md (DSMain lane; sha256 ab1ac8572604a5c6a1f4efd94172b32293aa9a2cbb4c677bd46648f60f1ec3fb, checked before reading), per records/README.md rule 2. Copied after the work began. -->

# LEAN-6: tidy up after the history replacement, then the first paper-only crypto piece

From claude-ai (claude-ai-58), 2026-10-07 16:30 EDT. For the same plain Claude Code session on DSMain, as dustin. Follows LEAN-5-report.md. Dustin's words, 16:27: "next run, with Crypto as the main focus? (keep the overall planned use for later)". This is item 3 of DIRECTION-20261007.md (8a6746a8): crypto ideas on top of the Lean library, paper first.

Dustin's terminal at 16:26 shows two pushes to /data/git/classical-lean.git: `299cc09..2e79a0c package-nightly -> master`, then `+ 2e79a0c...333b69a fresh-history -> master (forced update)`. So decision 1 from LEAN-5 is taken, and its remaining steps are part A below.

## Part A: finish decision 1 (do this first)

1. The DSMain clone ~/lean/classical-lean still holds the old history, so tonight's `git pull --ff-only` would fail and the 03:30 line would read ATTENTION. Confirm the clone has no uncommitted work and nothing on any local branch that is missing from the archive bundle LEAN-5 made (`git bundle verify` it again). Then move the clone onto the new master (`git fetch origin` and `git reset --hard origin/master` on master), and delete the old local branches and worktrees that LEAN-4 and LEAN-5 left. Run `systemctl --user start lean-nightly.service`. Predicted line 1: `Lean: OK - 333b69a 2026-10-07, 946 theorems written, 1662 constants checked, 0 sorry, 0 axioms (none)`. If it is not OK, stop and report.
2. helios: if `ssh helios` works from DSMain without a password prompt, run read-only `git -C ~/work/classical-lean status --porcelain` and `git -C ~/work/classical-lean log --oneline --branches --not --remotes` there, and report the output. Change nothing on helios. If ssh does not work that way, put those two commands in the report for Dustin, followed by the re-clone command to use only when both print nothing.
3. Report, do not fix: the author email in the new commit (LEAN-5's note) and the check_sorry finding LEAN-5's background review raised. Each gets one line in the report as a later order.

## Part B: the first crypto piece, paper only

Goal: one simple trading rule, tested on past prices with no money, where the arithmetic that decides how much to risk is proven in the Lean library and the program that runs the test is checked against those proofs.

Scope:
- Paper only. No exchange account, no API key, no login, no orders, no wallet. Price data comes from a public source that needs no key; name it in the report and follow its terms. Save the downloaded data with its sha256 so the test can be re-run on the same numbers.
- Lean part, in the library, on a new local branch `paper-crypto` (worktree, as before), as an ordinary math module with no trading words in its names: check what Mathlib v4.34.0 already has, then prove what it lacks of:
  - break-even with fees: with fee rate f each way (0 <= f < 1), buying at price a and selling at price c gains money exactly when c * (1 - f)^2 > a;
  - the Kelly fraction for a simple bet (win probability p, payout b > 0): the expected log growth p*log(1 + b*x) + (1 - p)*log(1 - x) on 0 <= x < 1 is largest at x = p - (1 - p)/b when that is in range, and that largest value is positive exactly when p*b > 1 - p;
  - the losing-streak bound: after n losses in a row betting fraction x each time, what is left is (1 - x)^n of the start.
  No sorry, no axiom, every gate passes, and the statements are checked with exact numbers first, as in earlier orders. Say which of the three you proved and which Mathlib already had.
- Program part, outside the library, in a new local git repo at ~/trading/paper (no remote). Python. One rule only, kept simple (for example a moving-average crossover on daily BTC-USD), with fees, and position size from the proven formulas. A test file checks the program's fee and sizing numbers against the Lean definitions on a fixed list of inputs (evaluate them in Lean with `#eval`, and compare).
- The result page says plainly: past results do not predict future ones; one rule on one coin is not evidence the rule works; and what the test leaves out (slippage, outages, taxes).
- No new checking machinery beyond the test file.

Done means:
1. Part A: the nightly line 1 reads OK at 333b69a, the clone is on the new master, and helios's state is reported or its commands are handed to Dustin.
2. The Lean module on `paper-crypto` builds with 0 warnings and every gate passes; outputs shown.
3. The comparison test passes, and the report shows it failing once on a deliberately wrong fee value first.
4. One backtest result: start and end date, the data file's sha256, number of trades, total fees, ending value of a 1,000 dollar paper account, worst drop from a peak, and the same numbers for simply buying and holding.
5. A report at /opt/datasphere/lane/inbox/threads/staging/LEAN-6-report.md with the plan first, the outputs above, the commits, what was not tested, and the push command for `paper-crypto` for when Dustin decides. Nothing is pushed.

If you cannot finish, finish Part A first; it protects tonight's run. Then stop at a clean point and write the report.
