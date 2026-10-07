# Round 37 — the math behind the trading, proofs only (order LEAN-9)

Session: Claude Code `session_01KyYusMNSHJap88c9A6s6K2` on DSMain, as dustin, executing order `LEAN-9`
(`records/orders/20261007T211000Z__claude-ai__order-lean9-trading-math.md`), on branch `paper-crypto-4`
(on `paper-crypto-3`), worktree `~/lean/classical-lean-paper-crypto`. Lean and Mathlib v4.34.0.
Nothing was pushed.

Modules added (theorem constants, `env.getModuleFor?` under the axiom gate's predicate):

* `ClassicalLean/Probability/MaximalInequality.lean` (6), item 1:
  - Ville's inequality over N steps (`measureReal_exists_le_of_supermartingale`);
  - the falls-to-half bound, first with the supermartingale as a hypothesis
    (`measureReal_exists_le_half`);
  - after a side agent's note, the supermartingale **proved** from independent factors with
    E[F^(-theta)] <= 1 (`supermartingale_prod`, `measureReal_exists_le_half_of_iIndepFun`);
  - the one-bet condition as an exact rational check (`ruinConditionOK`, `ruinConditionOK_iff`).
* `ClassicalLean/Analysis/LogDrag.lean` (5), item 2:
  - Jensen for logs, and zero mean return => non-positive mean log growth;
  - r - r^2 (1/2 + R/(1-R)) <= log(1+r) <= r - r^2 (1/2 - R/(1-R)) for |r| <= R < 1, and averaged
    forms.
* `ClassicalLean/Probability/DependentSampleMean.lean` (18), item 3:
  - the conditional Hoeffding lemma, proved through `condExpKernel`
    (`hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero`);
  - two-sided Azuma-Hoeffding;
  - the plain win-rate bound for dependent trades with conditional win probability p
    (`measureReal_abs_sampleMean_sub_ge_le_of_condExp`). It gives the same 2 exp(-2ne^2), so 190.
* `ClassicalLean/Probability/TwoVariableMix.lean` (5), item 4: `variance_mix`, and the unique
  minimum-variance weight w* = (c - k)/(a + c - 2k).
* `ClassicalLean/Analysis/RepeatedFees.lean` (3), item 5: (1 - f)^(2N), and break-even exactly when
  the geometric mean of the trades' factors is >= 1/(1 - f)^2.
* `ClassicalLean/Analysis/GeneralGrowth.lean` (3), item 6, partly:
  - at most one maximising fraction;
  - mean <= 0 => no growth;
  - the fraction mu1/(mu2 c) has growth >= mu1^2/(2 mu2 c).
  - **Not reached:** existence of the maximiser in a stated interval, and its distance from
    mu1/mu2. An exact check found the maximiser at 1.55 to 6.0 times the proved fraction.

The total is 1772, against 1732 on `paper-crypto-3`. `#print axioms` on all 22 new main theorems
gives `[propext, Classical.choice, Quot.sound]`. `lake build` has 0 warnings, after fixing 4 long
lines and one `show`. Every statement was checked with exact numbers first, and a dropped
hypothesis was shown to break items 1, 2 and 6. Details are in the LEAN-9 report.
