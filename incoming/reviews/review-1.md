# Cold review 1: order CLOUD-MATH-6, statement stage (five bridges)

Reviewer: a fresh subagent (Claude Opus 5.5) doing a cold review of order CLOUD-MATH-6's statement stage.
It had not seen the work before this review.
Brief: `/root/cm6/review/brief.md`, sha256 `23a0c2a104d196ff4deb46cd069a4c405c790ced0f4ff1f4af96daaa2160ba54`.

Checks I ran myself:
- The five module copies in the brief section 6 match the untracked files under
  `ClassicalLean/Probability/` byte for byte, checked by script.
- `lake env lean` on each of the five modules gives only `sorry` warnings: UrnVille 3, RuinConditional 1,
  RuinDivisibility 1, RuinChain 2, KolmogorovSmirnov 2.
- In scratch copies under `/root/cm6/review/scratch/` I looked at the elaborated statements with
  `pp.coercions`. The `1 / ↑m` in 156 is the cast `ℕ → ℝ`. In `ruinChain`, `↑j + 1 = ↑i` is compared in
  `ℕ`.
- Lean checked by `decide` that `lucasU (3 : ℤ) 2` at `0..6` is `0, 1, 3, 7, 15, 31, 63`.
- Lean checked by `simp` some entries of `ruinChain 2 3`: `(2,1) = (2,3) = (1,0) = 1/2`, `(2,2) = 0`,
  `(0,0) = (5,5) = 1` and `(5,4) = 0`. It also checked that all six rows sum to `1`.
- I scanned the files for forbidden words, `open` lines, namespaces and declarations.
- I compared the 157 helpers with PolyaUrn's private lemmas (`PolyaUrn.lean` lines 84 and 202).
- I checked that GamblersRuin lines 977–991 are the `Monotone.measure_iUnion` step of
  `measureReal_exists_ge_le_of_biased`.

## Verdicts on the main theorems

- **157 `measureReal_exists_urnShare_ge_le`: FAITHFUL.** It has the binders and hypotheses of
  `martingale_urnShare`, plus `{c} (hc : 0 < c)`, and the conclusion is the table's to the character.
  The statement is true:
  - The share is a martingale with values in `[0, 1]`.
  - `urnShare r b X 0 = r / (r + b)`, so `E[Z 0] = r/(r+b)`.
  - Ville's inequality gives `≤ r/((r+b)c)` at each horizon `N`. The union over `N` gives "ever".

  `hrb` is not needed for the statement to be true. At `r = b = 0`, `hX_cond` forces every draw to be `0`
  almost surely, so both sides are `0`. The table names `hrb`, so it stays.
- **154 `measureReal_exists_ge_le_of_condProb`: FAITHFUL.** Binders, `hcond`, `hp0`, `hp` and the
  conclusion are the table's. The statement is true:
  - The score with `p₀ = p` and `q = 1 − p` meets every hypothesis of `measureReal_exists_le_score_ever`:
    `p < 1`, `p ≤ 1 − p` and `1 − p ≤ 1`.
  - That score is `r ^ walk`, with `r ≥ 1`.
  - Reaching `a` gives a score `≥ r^a = 1/α`.

  Item 84 follows: independence plus `P(X n = 1) = p` gives `hcond` with equality.

  `hp0` is not needed for the statement to be true. At `p = 0` every step is `−1` almost surely, so for
  `a ≥ 1` both sides are `0`, and at `a = 0` both sides are `1`. `hp` (`p ≤ 1/2`) is needed against
  `p ≥ 1`: at `p = 1`, `p/(1−p) = 0` in Lean. Both are named by the table.
- **156 `measureReal_hit_eq_inv_iff_dvd`: FAITHFUL.** Hypotheses and conclusion are the table's. The
  statement is true:
  - `U(n+1) = U n + r^n`, so `U` is positive and strictly increasing on `n ≥ 1`.
  - The chance `U b / U(a+b)` is `1/m` exactly when `U b ∣ U(a+b)`.
  - That holds exactly when `U(gcd(b, a+b)) = U b`, so exactly when `b ∣ a`.

  Both hypotheses are needed:
  - `hr`: at `r = 0` the chance is `1 = 1/1`, while `2 ∤ 1`.
  - `hb`: at `b = 0` the event is empty, because `k = 0` needs `0 < 0`. So the left side is false while
    `0 ∣ 0` is true.
- **165 `integral_exitTime_eq_meanHitting` with `ruinChain_meanHitting_iff`: FAITHFUL** (classified
  together, as the order asks).
  - Theorem 2's `↔` for every `g` says the first-step system has exactly the one solution
    `(a + b − i)·i`.
    - The inside equation checks: `1 + ((N−i+1)(i−1) + (N−i−1)(i+1))/2 = (N−i)i`.
    - The edge cases also check: `a + b = 0` and `a + b = 1`, where every index is an end.
  - Theorem 1 says `∫ τ = g b` for every solution. With theorem 2 (a solution exists) and
    `meanHitting_eq` (it is the series `h`), this is the row's `∫ = h b = a b`.
  - The statement is true for all `a b`:
    - At `a = 0` or `b = 0`, `τ = 0` and the start index is an end.
    - Otherwise `g b = (a+b−b)·b = a b`, which is `integral_exitTime_eq`.
  - No hypothesis is extra. The hypotheses are `integral_exitTime_eq`'s plus the system.
- **159 `sup_abs_empiricalCDF_sub_eq_of_continuous`: GENERALIZED.** It drops the row's pairwise
  independence, as the order directs. Otherwise it is the table's statement. The statement is true:
  - Almost surely, `X i ≤ x ↔ F(X i) ≤ F x` for all `i` and `x`. The bad set lies in the union over
    rational `q` of `{F(X i) ≤ F q} \ {X i ≤ q}`, and each such set has measure `F q − F q = 0`.
  - So the left set of values is `{|G_n(u) − u| : u ∈ range F}`, and `(0,1) ⊆ range F ⊆ [0,1]`.
  - The extra points `u = 0` and `u = 1` contribute `0` almost surely when `n ≥ 1`.
  - At `n = 0` both sides are `1`.
  - Both suprema are bounded by `1`, so `⨆` is a true supremum.

  `hlaw` is needed. Without it, a draw lying in a flat stretch of `F` breaks the identity.
- **159 `measureReal_cdf_le_eq_of_map_eq` (theorem 2): FAITHFUL.** It is item 106 at `X i`. It takes
  `hX` and `hlaw` at the one index `i`, which the table's `∀ i` forms give at once.
  - `hX` could be weakened. `hlaw` with `hF` already forces `X i` to be a.e.-measurable, because a
    non-a.e.-measurable `X i` gives `μ.map = 0`, and `cdf 0` is Mathlib's default step function, which
    is not continuous.
  - The table names `hX`, so it stays.

## Verdicts on the witnesses

- **157: PASS.**
  - It is PolyaUrn's witness at `r = b = 1` and `c = 3/4`, and it elaborates.
  - Start share `1/(1+1+0) = 1/2 < 3/4`.
  - Bound `1/((1+1)·(3/4)) = 1/(3/2) = 2/3 < 1`.
  - The event has positive chance (red, red reaches `3/4` with chance `1/2 · 2/3 = 1/3`), so neither
    side is trivial.
  - The kernel's chance is `(1 + #red)/(n+2) ∈ [1/(n+2), (n+1)/(n+2)]`.
  - The share moves at every step. With `R = urnRed` and `N = n+2`, a red draw changes it by
    `(N−R)/(N(N+1)) > 0` (since `R ≤ n+1 < N`). A blue draw changes it by `−R/(N(N+1)) < 0` (since
    `R ≥ 1`).
  - The `open … in` line opens PolyaUrn and UrnVille. `urnShare_mem_Icc` and `urnRed_stronglyMeasurable`
    resolve to UrnVille's public lemmas, because PolyaUrn's are private.
- **154: PASS.**
  - `p = 1/3 ∈ (0, 1/2)`, strictly inside, not the boundary `1/2` where `r = 1`.
  - `(X n + 1)/2` is `1` on face `0` and `0` on faces `1, 2`, so its mean is `1/3` and `hcond` holds
    with equality, via `condExp_indep_eq`.
  - Bound `((1/3)/(2/3))^2 = (1/2)^2 = 1/4 < 1`.
  - `a = 2`, and every step is `±1`, so the walk moves.
  - `Eventually.of_forall` resolves through the module's top-level `open Filter`, which rule 3 allows.
- **156: PASS.**
  - `P(coin = 0) = 1/3 = 1/(2+1)`, so `r = 2`.
  - `U = lucasU 3 2 = 0, 1, 3, 7, 15, 31, 63`, that is `U n = 2^n − 1` (checked by `decide`).
  - Chance `U 2 / U 6 = 3/63 = 1/21`.
  - `b = 2 > 1`, `a = 4 > b`, and `2 ∣ 4`.
- **165 (theorem 1): PASS.**
  - `g i = (5 − i)·i` gives `0, 4, 6, 6, 4, 0`, which is `0` at the ends.
  - The inside equations hold:
    - `i=1`: `1 + (0+6)/2 = 4`
    - `i=2`: `1 + (4+6)/2 = 6`
    - `i=3`: `1 + (6+4)/2 = 6`
    - `i=4`: `1 + (6+0)/2 = 4`
  - `g 3 = 6 = 2·3 = a b`.
  - The matrix is `6 × 6`, with four inside indices, and `a ≠ b`.
  - The fair walk moves at every step, and `τ ≥ n` has positive chance for every `n`.
  - Theorem 2 has no hypothesis, so it gets no witness. That is correct.
- **159 theorem 1: PASS.**
  - Each draw has law `N(0,1)` (`gaussianReal_map_neg`, `neg_zero`, `map_id'`).
  - `X (i+1) ω = −X i ω ≠ X i ω` except at `ω = 0`, which is null. So the process moves at every step
    with chance `1`, and it is never constant.
  - `Φ` is continuous, as in IntegralTransform's witness.
- **159 theorem 2: PASS.**
  - `i = 1`, `X 1 = −ω`, and `hlaw 1` goes through `gaussianReal_map_neg`, so it is not `rfl`.
  - `u = 1/2` is inside `[0,1]`.
  - The value is right: `P(Φ(−ω) ≤ 1/2) = P(ω ≥ 0) = 1/2`.

Form, for all six witnesses:
- `example := Full.name …`, with every chosen argument given by name and every binder before the colon
  supplied.
- Only `open … in` lines, plus the module's top-level opens.
- None of the forbidden words.
- One inline block each, placed after the module's `end`.

## Helpers (157)

`UrnVille.urnShare_mem_Icc (r b X hX01 n ω)` and `UrnVille.urnRed_stronglyMeasurable (ℱ r X hX) : ∀ n, …`
have exactly the signatures of PolyaUrn's private lemmas (`PolyaUrn.lean` lines 202 and 84). They are what
the order asks: `urnShare … ∈ Set.Icc 0 1` when every draw is `0` or `1`, and
`StronglyMeasurable[ℱ n] (urnRed r X n)`. Both are true:
- `0 ≤ urnRed ≤ r + n ≤ r + b + n`, and at `r + b + n = 0`, `0/0 = 0`.
- Measurability follows by induction, using `ℱ n ≤ ℱ (n+1)`.

Both sit inside `ClassicalLean.Probability.UrnVille`, and the witness and the coming proof use them. Their
docstrings are accurate. No `tools/vacuity_reviewed.txt` line exists yet for me to check. Neither helper
just restates a hypothesis.

## Namespaces, imports, opens, definitions

- Every declaration is inside its module's namespace.
- The imports are exactly the table's.
- The cross-module `open` lines come after the imports and before the namespace:
  - UrnVille: `PolyaUrn`
  - RuinConditional: `GamblersRuin` and `LikelihoodScore`
  - RuinDivisibility: `ClassicalLean` and `GamblersRuin`
  - RuinChain: `GamblersRuin`
- KolmogorovSmirnov needs no cross-module open: `empiricalCDF` lives in `ClassicalLean.Probability`, which
  the namespace already reaches.
- The only new definition is `ruinChain`.

## Findings

1. **MINOR (165, theorem 1 docstring).** The docstring derives the row's `∫ τ dμ = h b` "the chain's
   hypotheses being met as `ruinChain_meanHitting_iff`'s proof shows".
   - That clause describes a proof that is still `sorry`.
   - Nothing stated in the library gives `meanHitting_eq`'s hypotheses for `ruinChain` (rows sum to `1`,
     entries `≥ 0`, an end reachable from every inside index).
   - Theorem 2's `↔` could even be proved without `meanHitting_eq`, by the recurrence
     `g(i+1) = 2g(i) − g(i−1) − 2`. The clause would then be false.
   - As stated, a reader cannot get `∫ = h b`, with `h` the series, from the stated theorems without
     proving those hypotheses again.

   **Proposed fix (either one):**
   - (a) State a small helper inside the namespace, with no hypotheses (so no witness), for example
     `ruinChain_meanHitting_hyps (a b) : (∀ i, ∑ j, ruinChain a b i j = 1) ∧ (∀ i j, 0 ≤ ruinChain a b i j) ∧ ∀ i ∉ A, ∃ t, ∃ k ∈ A, 0 < (ruinChain a b ^ t) i k`.
     Have theorem 2's proof use it, and cite it in theorem 1's docstring.
   - (b) Make sure the proof of theorem 2 does go through `meanHitting_eq`, as the order's proof sketch
     says, and reword the clause to "the chain meets `meanHitting_eq`'s hypotheses (rows sum to 1,
     entries ≥ 0, an end reachable from every inside index; see the module doc)".

   Statements and witness arguments are unchanged either way.

Notes, not findings:
- `hrb` (157), `hp0` (154) and `hX` (159 theorem 2) are not needed for the statements to be true, as shown
  above. The order's table names each of them, so under the brief's rule 2 they are not extra.
- Rule 3's "saying what moves" has no process to describe in 159 theorem 2's witness, a single draw. Its
  docstring names the draw and the point `u`, which is adequate.

FINDINGS 1
