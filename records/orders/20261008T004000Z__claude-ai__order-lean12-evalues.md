<!-- Copied verbatim on 2026-10-07 from /opt/datasphere/lane/inbox/threads/staging/LEAN-12-order.md (DSMain lane; sha256 35544235bb967e1ac49c0687194fa74931614ce3d7ba44cbba0c943e6e732392, checked before reading), per records/README.md rule 2. Copied before the work began. -->

# LEAN-12: put the proofs to work on the paper trades, with tests that survive correlation

From claude-ai (claude-ai-61), 2026-10-07 20:40 EDT. For a fresh plain Claude Code session on DSMain, as dustin. Lean work in the worktree ~/lean/classical-lean-paper-crypto; program work in ~/trading/paper. Paper only: no account, key, order or wallet; nothing pushed. Review: cold review by a fresh-context subagent, two passes of about 40 steps each. Pass 1: READY AFTER FIXES, 3 MAJOR (a ceiling on returns cannot simply be dropped, since Mathlib's conditional expectation of a non-integrable function is 0; LEAN-11's hindsight case is not a refutation of item 1(e); line A3 refutes only (b)) and 9 MINOR, all applied. Pass 2: READY, 11 of 12 confirmed fixed, the 12th and 3 new MINOR applied after it (lines B7, B8 added; both predictions hit). Not reviewed: anything on DSMain itself.

**Why this work.** LEAN-10's and LEAN-11's reports both end "no program uses these results yet". LEAN-8 could not test average profit per trade ("a long trade's gain has no fixed ceiling"), and it found 97-98% of trades overlap across series; LEAN-10's Benjamini-Hochberg proof assumes independence (`iIndepFun`), which that overlap breaks. LEAN-11 left "q chosen from past outcomes only: not proved". Items 1 and 2 close those three gaps; item 3 runs them on LEAN-8's trades. Dustin's direction of 10-7: crypto first, paper only.

**It rests on** (lane, /opt/datasphere/lane/inbox/threads/staging/): LEAN-11-report.md d80f4d0f (axiom gate: 2001 constants), LEAN-11-CLOSE.md db86dd1d, LEAN-10-report.md 4353dc80, LEAN-8-report.md 26a60c8f; and claude-ai-61's measurements on DSMain, 2026-10-08 00:12-00:35 UTC: origin master 2c96a7a (paper-crypto-6, pushed by Dustin); the worktree clean at 2c96a7a; ~/trading/paper master 514b1d9, clean; /opt/datasphere/status/LEAN.md line 1 still naming c5f2a94 (the nightly runs at 03:30); paper/sizing.py line 17 multiplies the fee in, `w / a * (1 - f) * c * (1 - f)`. The Lean statements below were elaborated with `sorry` in the worktree's environment with rule 20's four flags: rc 0, 7 `sorry` warnings, nothing else.

## Step 0

1. Read LEAN-11-CLOSE.md. If it does not exist, stop and tell Dustin.
2. Report /opt/datasphere/status/LEAN.md line 1. Predicted: after 03:30 EDT on 10-8 it names 2c96a7a with 2001 constants checked, 0 sorry, 0 axioms; before then it still names c5f2a94.
3. Branch `paper-crypto-7` on origin/master (2c96a7a) in the worktree. Records first (order copy, index row, claim row), committed before any module.
4. Copy LEAN-12-checks.py from the lane folder above (sha256 f7d977376c7d5df09e10c8bd05b80777fa32c5c5a8fd27a73cc9c816a2a574f8) to ~/lean/lean12-checks/, run it there with `python3 -I` (standard library only, about 20 s), and diff its output with LEAN-12-checks.out (sha256 77d34a2220d936e76e064a81a1c2b71002248afd532a61efd70d0551c360f372). Lines cited below are its output lines. Line A5's first half prints "False": that is a scored miss of claude-ai-61's, noted in the script, not a failed check.

## The work, in this order

1. **A test for "no edge" whose bound uses only a floor on losses.**
   - Setting: returns `X n` adapted to a filtration `𝒢`, with `-c ≤ X n` (`0 < c`) and `X n ≤ C` for some `C`; `μ[X (n+1) | 𝒢 n] ≤ 0` almost everywhere (no edge after fees). Stakes `L n` adapted to `𝒢` (chosen from earlier returns only), `0 ≤ L n ≤ 1/c`. Wealth `wealth L X n ω = ∏ i ∈ range n, (1 + L i ω * X (i + 1) ω)`.
   - Prove: (a) it is a supermartingale; (b) the chance it reaches `1/α` (`0 < α`) within `N` trades is at most `α`; (c) `μ.real {ω | ∃ n, 1 / α ≤ wealth L X n ω} ≤ α`, from (b); (d) `∫ wealth L X N ≤ 1`, so the final wealth is an e-value.
   - (e) Corollary: LEAN-11's score with `q` replaced by `Q n`, adapted to `𝒢`, `p₀ ≤ Q n ≤ 1`: `scorePred p₀ Q W n ω = ∏ i ∈ range n, scoreFactor p₀ (Q i ω) (W (i + 1) ω)` gets (b), (c) and (d). Take `X = W - p₀`, `c = p₀`, `L = (Q - p₀)/(p₀(1 - p₀))` and `scoreFactor_eq_convex`.
   - Route: `wealth (n+1) = wealth n + wealth n * L n * X (n+1)`; pull out with `condExp_mul_of_stronglyMeasurable_left`; then `supermartingale_nat`. (b) by `measureReal_exists_le_of_supermartingale`, (c) by `measureReal_iUnion_le_of_monotone`, (d) by `Supermartingale.setIntegral_le` on the whole space.
   - About `C`: it only makes the wealth integrable; its size never enters the test. Do not simply drop it. Mathlib sets `μ[f|m] = 0` when `f` is not integrable, so without `C` (or `∀ n, Integrable (X n) μ`) the condition holds for free and (b) is false: `X 1 = -1` with chance 1/2, otherwise a heavy tail with `P(X 1 ≥ 9) = 1/2` and infinite mean, `L 0 = 1`, gives chance 1/2 > 1/10 (found by the reviewer; it needs an infinite space). Replacing `C` by integrability of each `X n` is true but optional; if not done, the report says the theorem needs a ceiling or integrable returns.
   - Expected: line A1 (0.0060 ≤ 1/10; the final wealth averages exactly 1), line A5's second half (0.0162 ≤ 1/10).
   - Needed: stakes from earlier returns only (line A2: a stake that sees the next return gives 0.310 > 1/10; for (e), line A7: `Q` that sees the next outcome gives 11/16 > 1/4). Line A6 (LEAN-11's hindsight `q`, 200 trades, 0.0939 > 1/20, LEAN-11's own figure) is why the corollary exists, not a refutation of it: it re-scores the whole history with each new `q`. `L ≤ 1/c`: line A3 for (b) (wealth can go negative: 3/4 > 1/4, made of 1/2 at the first trade and 1/4 from −2·−2), line A8 for (a) and (d) (`E[W2] = 4 > 1`). `0 ≤ L`: line A8 (`W1 = 2 > 1`). No edge: line A4 (mean 1/4 gives 0.103 > 1/10, which is the test's power). The test needs no independence between trades.

2. **Many tests at once, under any dependence (e-BH, Wang and Ramdas 2022).**
   - Setting: e-values `e i` on a finite set of `m` tests, `q > 0`. `countGE e c` = how many `e j ≥ c`. `eNumRej q e` = the largest `k ≤ m` with `k ≤ countGE e (m / (q * k))`. Test `j` is rejected when `1 ≤ eNumRej q e` and `m / (q * eNumRej q e) ≤ e j`. `eFalseShare q H e` = rejected tests in `H`, divided by `eNumRej q e`.
   - Prove: exactly `eNumRej q e` tests are rejected; for every outcome, `eFalseShare q H e ≤ q / m * ∑ i ∈ H, e i` when `e i ≥ 0` on `H` (tests outside `H` may have any sign; line B8, 2,457 cases, 0 failures); so for random e-values with `E i ≥ 0`, integrable and `∫ E i ≤ 1` on `H`, `∫ eFalseShare ≤ q * |H| / m`, with no independence anywhere. `integral_mono_of_nonneg` needs integrability of the right side only.
   - Expected: lines B1 (124,110 cases, 0 failures) and B2 (two copies of one e-value: equality at 1/2).
   - Needed: `∫ E i ≤ 1` (line B3); `e ≥ 0` on `H` (line B6); `q > 0` for the exact count (line B7: `q = −1`, `e = (−3/2, −1/2)` gives `eNumRej` 1 but 2 rejected).
   - Two Lean traps: keep `1 ≤ eNumRej` in the rejection rule, since `m / (q * 0) = 0` (line B4: one test rejected while `eNumRej` is 0, breaking the exact count; Lean's share 1/0 = 0 hides it); never build p-values as `1 / e`, since `1 / 0 = 0` rejects a zero e-value (line B5).

3. **The program** (~/trading/paper, pre-cut-off data only; the held-out months were spent by LEAN-8 and stay untouched). Write the plan, including everything below, and commit it before any run.
   (a) Item 1 in exact `Fraction`s, using each `Trade.ret` that `run_trades` already produces. The stake before a trade is `floor(1000 * min(1/2, max(0, S1/S2)))/1000`, with `S1` and `S2` the sum and sum of squares of the returns of that combination's trades closed before this trade's entry (0 when there are none or `S2 = 0`). `c = 1`: with the fee multiplied in, a round trip returns more than −1; report the smallest return to show it. Pad every combination with zero returns to the fixed horizon N = 1000 trades (report the largest trade count; if any exceeds 1000, use its wealth after trade 1000, which is still an e-value, and say so), so its final wealth is an e-value.
   (b) For each of LEAN-8's 33 combinations, in time order: final wealth, the largest wealth reached, and whether it ever reached 20. Each "ever reached 20" is a test of that one combination at α = 1/20, not a result for the family.
   (c) e-BH at q = 1/10 over the 33 final wealths (not the largest: that is not an e-value).
   (d) Computable versions over `ℚ` of the wealth and of `eNumRej`, each with a theorem equating its cast with the real definition; add their cases to tests/test_against_lean.py. Plant one wrong expected value in the Python test first and show the test fails, then restore it and show it passes, as LEAN-10 did.
   claude-ai-61's predictions, to be scored: no combination's wealth ever reaches 20; e-BH rejects 0 of 33; BTCUSDT-1h V1 (average −1.03% per trade) ends at or below 1 (exactly 1, all stakes 0, counts as a hit).

For each Lean item: check Mathlib v4.34.0 first and reuse; show each hypothesis is needed (the lines above, plus a Lean refutation where a finite space suffices); no sorry, no axiom, all six gates pass; plain-words docstrings, no trading words in names.

## Known traps (LEAN-11-CLOSE.md, section 4, and this draft)

- Warnings show under `lake build <module>`, not `lake env lean`.
- `integral_finset_sum` is deprecated: use `integral_finsetSum` (measured in the draft). Other v4.34.0 renames are in LEAN-11-CLOSE.md section 4.
- `omit [inst] in` goes before the docstring. `decide` will not evaluate on rationals: use `simp only [..., decide_eq_true_eq]; norm_num`.
- The `git add` hook refuses any command containing an asterisk; write files and `git add` in separate commands, with explicit paths.

## Done means

1. Step 0 done: the status line, and the check script's diff with rc shown.
2. Items 1 and 2: proved here, or not reached and why; each main theorem's `#print axioms`.
3. A table of dropped hypotheses: item, hypothesis, exact case, what fails, where checked. Every proved item has at least one row.
4. `lake build` 0 warnings, all six gates pass, the new constant count against 2001.
5. Item 3: the plan's commit hash before the run's; the 33-row table; the e-BH result; the three predictions scored; the red then green test logs.
6. LEAN-11-meanings.md's format continued in /opt/datasphere/lane/inbox/threads/staging/LEAN-12-meanings.md.
7. A report at /opt/datasphere/lane/inbox/threads/staging/LEAN-12-report.md: plan first, outputs, commits in both repositories, what was not reached, and the push command.
8. Close with the close-session skill (lane copy /opt/datasphere/lane/inbox/threads/SKILL-close-session.md, sha256 5f2a4671662e3142ac6b94ec40e77a4cd4aadd32341f6c67c2e1f2c6286a0d5d): the note at /opt/datasphere/lane/inbox/threads/staging/LEAN-12-CLOSE.md and its DONE file beside it.

Not in this order: any live or real-money step; the held-out data; Benjamini-Yekutieli.
