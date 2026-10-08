# Round 41 — with a real edge, a fixed stake reaches any level (order LEAN-13)

Session: Claude Code `session_01SvjhVpJp7pSW5qjW6asVks` in a cloud container (not DSMain), for
dustin, executing order `LEAN-13` (`records/orders/20261008T021400Z__claude-ai__order-lean13-edge-growth.md`),
on branch `paper-crypto-8` (on `origin/master` = `04fcd97`, which holds `paper-crypto-7` and three
later documentation commits), in `/home/user/classical-lean`. Lean and Mathlib v4.34.0 (Mathlib's
prebuilt cache). Nothing was pushed. Records were written before the modules (`a5048c4`). Item 3
of the order (the program) was not reached: the program is not in this container.

Modules added. Two counts per module: theorems written (`theorem` and `lemma` lines) and theorem
constants under the axiom gate's predicate (`.thmInfo`, user name under `ClassicalLean`, counted per
module with `env.getModuleFor?`; it adds Lean's generated constants):

* `ClassicalLean/Probability/EdgeGrowth.lean` (12 written, 13 constants), item 1: returns
  independent (`iIndepFun`), with the distribution of `X 0`, measurable, `-c ≤ X n ≤ C` with
  `0 < c`; `growth μ Y l = ∫ log (1 + l Y)`. (a) `exists_growth_pos`: a positive mean gives a stake
  `0 < l < 1/c` with positive growth. (b) `tendsto_log_wealth_div`: for `0 ≤ l < 1/c`,
  `log (wealth) / n` tends to the growth almost surely (Mathlib's `strong_law_ae_real`). (c)
  `tendsto_wealth_atTop`: positive growth gives wealth tending to infinity almost surely. (d)
  `exists_stake_measureReal_reach_eq_one`: with a positive mean, some stake in `(0, 1/c)` reaches
  `1/α` at some time with probability 1, for every `α > 0`. The wealth is `NoEdgeWealth.wealth`.
* `ClassicalLean/Probability/ScoreLookahead.lean` (14 written, 37 constants), item 2: on four fair
  coins (16 points, `Measure.pi` of the uniform law on `Bool`), with `W` the coin outcomes, `𝒢` their
  natural filtration, `p₀ = 1/2` and `Q` peeking at the next outcome, every hypothesis of
  `NoEdgeWealth.measureReal_exists_le_scorePred` holds except that `Q` is adapted, `Q` is shown not
  adapted, and the chance of reaching `4` within 4 outcomes is `11/16 > 1/4`
  (`lookahead_breaks_score_bound`). The count `11` is by `decide` over the 16 points.

Totals: 26 theorems written, 50 constants; the axiom gate counts 2091, against 2041 at `04fcd97`
(both measured in this container). `#print axioms` on the 5 main theorems gives `[propext,
Classical.choice, Quot.sound]`. `lake build` 0 warnings (per module and whole library; a planted
unused variable gave 2 warning lines, removed). Gate numbers here were taken on the working tree
holding exactly the files of this commit (one round, nothing else changed); they are re-run on the
clean tree after the commit and reported in the LEAN-13 report.

Each hypothesis of item 1 dropped: Lean refutations outside the library (independence, on two points;
a positive mean, identical distribution and `0 < c`, on one point), each with all other hypotheses
proved; planted controls fail (rc 1). Stake `l < 1/c`, `0 ≤ l` and the ceiling `C` for (b) need
infinitely many independent returns: the order's check script (line C4) and the report only.
Measurability, and `C` outside (b): not shown needed, kept for convenience. Item 2's planted control
(`Q` seeing only the previous outcome) fails (rc 1). The banned-vocabulary gate could not run here
(its term list is kept outside the repository); see the LEAN-13 report. Details are in the LEAN-13
report.

Commits: records first `a5048c4`; modules and this fragment `30715ce`. On the clean tree at
`30715ce`: `lake build` rc 0, 0 warnings; axiom gate PASS, 2091; vacuity gate PASS; check_sorry PASS
(79 files); check_records PASS (79 modules); banned_vocab_scan rc 2 (term list missing here).
