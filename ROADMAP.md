# ROADMAP

Categories to add, and the patterns that connect the ones already here.

`HANDOFF.md` says what to do next in the small. This file is the map at the level of *subject areas*,
for the standing goal in `HANDOFF.md` §3: a library that spans mathematics rather than one
corner of it.

---

## 0. The rule this file is written under

**A gap claim is a measurement, and it must name the command that made it.** Every row below
carries the search that produced its Mathlib status. Rows with no command are marked
*not researched* and are not claims.

This is not a formality. The rule was broken during the pass that produced this file, and the
break is the most useful thing in it:

> To claim Mathlib had no general Lucas sequence, the search run was
> `grep -rn 'Lucas sequence\|lucasSeq\|LucasSequence' Mathlib --include=*.lean`, which returns
> one prose line. On that basis a module docstring asserted the gap was "general `Q`".
> **The object is in Mathlib under another name.** `Polynomial.dickson k a`
> (`RingTheory/Polynomial/Dickson.lean`) is defined by `dickson k a 0 = 3 - k`,
> `dickson k a 1 = X`, `dickson k a (n+2) = X * dickson k a (n+1) - C a * dickson k a n` — which
> is `V` for `k = 1` and `U` shifted for `k = 2`, with the parameter free.
>
> The measurement was correct and the object was wrong: it searched for a *name*. What survived
> re-measurement is narrower and is what the module now claims — Mathlib has the definitions and,
> in 280 lines, proves **no** addition law, doubling identity, Cassini identity, discriminant
> relation or companion matrix at *any* parameter; every theorem past the recurrence is at
> `a = 1` or `a = 0`.

The practical form of the rule: **search for the mathematics, not the vocabulary.** Grep the
*recurrence*, the *shape of the statement*, the *value* — `3 - k`, `X * _ - C a * _`,
`x ^ n + y ^ n` — not only the word you would use for it.

It was broken a second time, in round 6, in a way the first lesson does not cover:

> `Algebra/CompanionMatrix.lean` shipped a `private theorem sum_mulVec` —
> `(∑ Aᵢ) *ᵥ v = ∑ (Aᵢ *ᵥ v)` — with a docstring saying Mathlib "has `Matrix.add_mulVec` but no
> `Finset.sum` version". The search behind that was for `Finset.sum_mulVec`. **The lemma is in
> Mathlib as `Matrix.sum_mulVec`** (`Data/Matrix/Basic.lean:943`), stated more generally — any
> `NonUnitalNonAssocSemiring`, rectangular — and with the same three-line proof.
> `grep -rn 'sum_mulVec\|mulVec_sum' Mathlib --include=*.lean` returns 7 lines and finds it
> immediately. The helper was deleted and the use site repointed; `lake build` rc 0, 0 warnings.

The first break searched for the right namespace and the wrong name. This one searched for the
right name and the **wrong namespace** — a lemma about `Matrix` lives under `Matrix`, not under
the `Finset` that appears in its statement. Added to the rule: **grep the bare name, unqualified,
before concluding a lemma is absent.**

---

## 1. Patterns across what is already here

These are the connections measured during this pass. Two are now theorems in the library; the
rest are stated with what would have to be proved.

### 1.1 Seven of the library's sequences are one object — **proved**

`NumberTheory/LucasSequence.lean` and `LucasSequenceCases.lean`. `Nat.fib`, `lucas`,
`pellNumber`, `pellHalfCompanion`, `jacobsthal`, `jacobsthalCompanion` and Mathlib's `mersenne`
are `U` or `V` of a Lucas sequence at five parameter pairs, and the even-index Fibonacci–Lucas
pair is a sixth.

The consequence that matters is not tidiness. It is that theorems proved separately in modules
sharing no import are the *same theorem*:

| proved separately | is | at |
|---|---|---|
| `lucas_mul_fib`, `jacobsthal_mul_jacobsthalCompanion` | `lucasU_two_mul` | `(1,-1)`, `(1,-2)` |
| `lucas_sq_sub_five_mul_fib_sq`, `pellHalfCompanion_sq_sub_two_mul_sq` | `lucasV_sq_sub_discr_mul_lucasU_sq` | `(1,-1)`, `(2,-1)` |
| `three_mul_jacobsthal`, `jacobsthalCompanion_eq`, `mersenne = 2^n - 1`, `coe_lucas_eq` | `lucasU_of_roots` / `lucasV_of_roots` | four root pairs, three rings |
| `lucas_two_mul` | `lucasV_two_mul` | `(1,-1)` |
| `companionMatrix_pow_trace` | `lucasCompanion_pow_succ_trace` | `(3,1)` |

The surprise inside it: **the Mersenne numbers are a Lucas sequence**, `U(3,2)`, because `2` and
`1` are the roots of `t² - 3t + 2`. That places `Mersenne.lean`, `MersenneOrder.lean` and
`MersenneFactorialPart.lean` in the same family as `Lucas.lean` and `Pell.lean`, which the
library had treated as unrelated subjects. Its discriminant is `1` — the degenerate, split case,
where the sequence is a difference of geometric progressions rather than a quadratic-irrational
one. That is *why* Mersenne arithmetic is so much more elementary than Fibonacci arithmetic, and
it is a statement, not an impression.

### 1.2 `NacciTrace` is the same theorem at order `n` — **proved, see §2.2**

`NumberTheory/NacciTrace.lean` says in its own header that `A n k` is "the `k`-th power sum of
the roots of the augmented polynomial", and ships `nacciTrace_two_eq_lucas : S 2 k = L k`.
`LucasSequence.lean` proves `lucasCompanion_pow_succ_trace : (M ^ (n+1)).trace = V (n+1)` — the
order-2 case of exactly that: the trace of the `k`-th power of a companion matrix is the `k`-th
power sum of its eigenvalues.

So `nacciTrace_two_eq_lucas` is not a coincidence between two sequences; it is the order-2
instance of a general fact the library stated in prose in one module and proved for `n = 2` in
another. What closed it: the companion matrix of a monic degree-`d` polynomial, and
`(M ^ k).trace = p_k`, the `k`-th power sum. Mathlib has Newton's identities for symmetric
polynomials (`RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean`, measured present) but
the companion-matrix trace statement is a separate thing and was **not** found —
see §2.2 for the search.

Done in `Algebra/CompanionMatrix.lean` and `NumberTheory/PowerSumCases.lean` (commits `e59dd96`,
`6a23ec8`). The unconditional statement is `nacciAugmented_eq_trace`. One caveat that §2.2
records and this section should not hide: the `k > d` half is Cayley–Hamilton and is proved for
arbitrary coefficients, but the `k ≤ d` half is proved **only** for this family, by an explicit
closed form, not in general.

### 1.3 The Chebyshev appearance in `Lucas.lean` is forced, not decorative

`lucas_two_mul_eq_chebyshev_T : (L (2n) : ℚ) = 2 * (T ℚ n).eval (3/2)` reads like a curiosity.
It is `lucasV_eq_chebyshev_C_eval` at `P = 3`, and Mathlib's own
`dickson_one_one_eq_chebyshev_C` says `Chebyshev.C = dickson 1 1`. So: *every* `Q = 1` Lucas
sequence is a Chebyshev evaluation, `L(2n)` is the `(3,1)` one, and the `3/2` is `P/2`. Three
facts the library states in three places are one fact.

### 1.4 `FactorialPart` is the precedent, and it was already the right move

`NumberTheory/FactorialPart.lean` exists because the gcd-with-a-factorial split appeared twice,
once in Mersenne material and once in Lucas material, and was about neither. That is the same
manoeuvre as §1.1, made earlier and on a smaller object. It is worth naming as the library's
house pattern: **when the same lemma is proved twice, the shared object is usually the result
worth having**, and the duplicated proofs are the evidence that it is load-bearing rather than
decorative.

### 1.5 The Simplex/Geometry corner connects to the rest through `φ` alone — and that link is thin

`Simplex/DesignConstants.lean` and `Simplex/Involution.lean` import
`GoldenRatio/Characterisations.lean`; `Geometry/Helix.lean` uses `Real.goldenRatio`. That is the
whole of the connection between the library's analysis/optimisation half and its number-theory
half. Stated honestly: the golden ratio appearing in a free-energy minimiser and in a
Fibonacci recurrence is **not** evidence of a shared mechanism, and nothing here should be
written as though it were. `DesignConstants` reaches `1/φ` by solving a transcendental
critical-point equation; `Lucas.lean` reaches `φ` as a root of `t² - t - 1`. The library should
either prove a statement that uses both facts at once, or leave them unconnected and say so.
This roadmap says so.

**Amended after the §1.6 sweep**: the direction of that dependency is the opposite of what this
section assumed. See §1.7 — `GoldenRatio/Characterisations.lean` is imported *only* by `Simplex`
modules, and no number-theory module imports it at all.

**Amended again, 2026-09-08**: the statement this section asked for — one that uses both facts at
once — now partly exists. `Simplex/Temperature.lean`'s `gibbsWeight_eq_softmaxT` identifies the
algebraic expression `criticalTemperature` is built on as a softmax weight, and
`softmaxT_levelGap_one_thresholdTemperature` restates the golden threshold in those terms. That
joins the free-energy work to `LogSumExp.lean`; it does **not** join either to the number-theory
half, which is what this section actually asked for. See §1.13.

**Dated 2026-09-24 UTC (order G-6, round 21):** pattern P4 of §1.14 would join
`Geometry/S3Quaternion` to `Simplex/FisherRao`: pulled back along the squaring map of `sqCoords`,
the Fisher–Rao metric is 4 times the Euclidean one. Geometry already reaches Simplex through
`sqCoords_mem_closedSimplex`, and neither link joins the corner to the number-theory half, which
is what this section asks for. The patterns proved in round 21 (P1–P3) join Simplex modules to
each other and Statistics to Simplex; they do not change this section's conclusion either.

**Dated 2026-09-24 UTC (order G-7, round 23), corrections, each measured with `grep` (round
23):** `Simplex/DesignConstants.lean` does not import `GoldenRatio/Characterisations.lean`, directly
or through its imports; `Simplex/FisherRao.lean` and `Simplex/Involution.lean` do. The
"amended" line above — imported *only* by `Simplex` modules, no number-theory module at all —
has been false since `abb24c7`: `NumberTheory/LucasSequenceCases.lean` imports it (line 13).
`Geometry/Helix.lean` uses `Real.goldenRatio` and, since round 23's step 6, also imports
`GoldenRatio/Characterisations.lean`, which now holds the two statements about `φ²` that
`Geometry/Helix.lean` and `Simplex/DesignConstants.lean` had each proved. Round 23's P4 (the squaring map) is proved; it joins `Geometry` to
`Simplex`, not either to the number-theory half, so this section's conclusion stands.

### 1.6 `GoldenRatio/Characterisations.lean` was a third unabsorbed copy — **now connected**

The absorptions of rounds 4 and 6 each found their target by asking "what is this a special case
of?", and each time the answer was in a neighbouring `NumberTheory` file. That question could not
see this one, because the file is filed by *subject* — the golden ratio — rather than by
*structure*. It independently develops the `(P,Q) = (1,-1)` case of the general theory:

* `fibMatrix = !![1, 1; 1, 0]` is `lucasCompanion 1 (-1)` conjugated by the swap. Proved:
  `swap_mul_lucasCompanion_mul_swap` in `LucasSequenceCases.lean`. They are not equal — the basis
  order is reversed — which is why no earlier grep for `lucasCompanion` found it.
* `fibMatrix_trace = 1` and `fibMatrix_det = -1` are `P` and `Q`; `fibMatrix_det_sub_smul` is the
  characteristic polynomial `x² - Px + Q`. All three shipped as `example`s.
* `vieta_sum` and `vieta_prod` say precisely that `φ, ψ` is the root pair at `(1,-1)`, so
  `Lucas.lean`'s `coe_lucas_eq` — Binet for the Lucas numbers, the first result of the round-3
  session — is `lucasV_of_roots` in **three lines with no induction**. Shipped as an `example`.

Nothing in that module was edited; the identifications live in `LucasSequenceCases.lean` so its
own narrative stays intact.

### 1.7 The golden ratio has two independent treatments, and the dependency runs backwards

`GoldenRatio/Characterisations.lean` is imported by exactly two modules, `Simplex/FisherRao.lean`
and `Simplex/Involution.lean`. **No `NumberTheory` module imports it.** `Lucas.lean` reaches past
it to Mathlib's `Real.goldenRatio` directly, and `Geometry/Helix.lean` does the same.

So the project's own golden-ratio theory serves the *information geometry* and not the *number
theory*, which is the reverse of what the directory layout implies. §1.6 is the first statement
proved in either direction. This is worth knowing before anyone concludes from the tree that
`GoldenRatio/` is a number-theory support module: it is not, and has never been used as one.

**Dated 2026-09-24 UTC (order G-7, round 23), corrections, each measured with `grep` (round
23):** "No `NumberTheory` module imports it" and "has never been used as one" have been false since
`abb24c7`: `NumberTheory/LucasSequenceCases.lean` imports it (line 13) and uses `vieta_sum`,
`vieta_prod` and `fibMatrix`. "Imported by exactly two modules": three at `cca6f8a`
(`Simplex/FisherRao`, `Simplex/Involution`, `NumberTheory/LucasSequenceCases`), four after
round 23's step 6, which adds `Geometry/Helix` — counting modules under `ClassicalLean/`, not
the root file `ClassicalLean.lean`, which imports every module. So `Geometry/Helix.lean` no
longer "does the same" as `Lucas.lean`, which still reaches Mathlib's `Real.goldenRatio`
directly. The golden ratio's two treatments now share two statements, `φ² + (φ²)⁻¹ = 3` and
`(φ²)⁻¹ = ψ²`, proved once in `GoldenRatio/Characterisations` (§1.15).

### 1.8 `Tribonacci.lean` was disconnected from two layers that both cover it — **now connected**

`tribonacci (n+3) = tribonacci (n+2) + tribonacci (n+1) + tribonacci n` is a constant-coefficient
linear recurrence of order 3, i.e. `companionRec ![1,1,1]`. The file contained **zero** occurrences
of `companion`, `matrix`, `trace` or `LinearRecurrence`. Both method layers reach it outright, and
now say so: `tribonacci_isSol_companionRec`, `exists_poly_mk_tribonacci` (a rational generating
function with numerator `1 - X - X² - X³`, obtained with no induction), and the order-3 instance of
`trace_companionMatrix_pow_isSol`.

This is the `NacciTrace` shape a second time. The general lesson is §1.10.

### 1.9 Cassini's identity is *not* the determinant — the gap is a factor of `Q`

The tempting statement is that trace and determinant of the companion matrix give the two classical
Lucas identities. Half of it is true: `lucasCompanion_pow_succ_trace` gives `V` on the nose.

The determinant does **not** give Cassini. Expanded on the entries
(`lucasCompanion_pow_succ_det_eq`), `det (M ^ (n+1))` is `Q · (U(n+1)² - U(n+2)·U n)`, so combining
with `lucasCompanion_pow_det` yields Cassini **multiplied by `Q`** — shipped as
`mul_lucasU_cassini`. Cancelling `Q` requires it to be a non-zero-divisor, which fails in a general
commutative ring: at `Q = 0` the determinant identity degenerates to `0 = 0` while `lucasU_cassini`
still asserts something. So the shipped induction proof is **strictly stronger** than the matrix
argument, and the two are different theorems rather than two proofs of one. Recorded because the
sloppy version of this pattern is false and is easy to write down.

### 1.10 The library is filed by subject, and that is what hides the repeated structure

§1.6 and §1.8 are the same finding twice: a module that is an instance of a shipped method layer,
invisible because it lives under a directory named for its subject rather than its structure.
`Geometry/Helix.lean` was a third, absorbed in round 6. In every case the module named the
mathematics correctly and named the *structure* nowhere.

The cheap detector, which found both of these in one pass: for each module, grep for the structural
vocabulary it would use if it knew about the layers — `companion`, `LinearRecurrence`, `trace`,
`PowerSeries`, `orderOf` — and list the modules where the count is zero but the mathematics is of
that shape. Nineteen modules are leaves that nothing imports; that list is where to look next.

### 1.11 Mathlib's junk-value convention is a cross-cutting idiom nobody has named

Six modules independently handle the same problem, in six ad-hoc ways: `sInf ∅ = 0`
(`LucasApparition`), `orderOf = 0` for elements of infinite order (`PrimitiveDivisor`,
`MersenneOrder`), `Real.log 0 = 0` (`Simplex/LogSumExp`), truncated `ℕ` subtraction
(`Mersenne`, `PrimitiveDivisor`), and the coefficient conventions in
`RecurrenceGeneratingFunction`.

This is not a candidate module — there is no shared theorem — but it is a shared *discipline*, and
it has cost real errors. In round 9 two predictions about it were wrong: that phrasing over `ℤ`
would repair the degenerate arguments (it removes one junk cell of eight), and that `p ∤ a` was the
hypothesis that excluded them (it excludes none; the failure is at `n = 0`). The recurring question
is **"which hypothesis excludes the junk?"**, the answer has been different every time, and the
only method that has worked is enumerating the junk cells numerically before stating the theorem.
That is now the rule for any new definition with a junk value.

### 1.12 The leaf sweep — three findings, two of them shipped

§1.10 named the leaf modules as where to look next.  Swept with the structural detector, 18 leaves
at the time.  Most are terminal by design — `PowerSumCases`, `PrimitiveDivisor`,
`LucasSequenceGeneratingFunction`, `AlgebraicGeneratingFunction`, `CompositumDiscriminant` sit at
the top of their chains and nothing should import them.  Three findings survived.

**(a) `Geometry/Spectral3x3.lean` had the `k ≤ d` Newton case all along — now connected.**
`Algebra/CompanionMatrix.lean` proves Newton's identity for `k > d` (Cayley–Hamilton, arbitrary
coefficients) and its header records that `k ≤ d` is proved **only** for the nacci family, by an
explicit closed form.  `Spectral3x3` has `Matrix3.trace_mul_self : (M * M).trace = M.trace ^ 2 -
2 * minorSum M` — Newton at `k = 2` for any `3 × 3` matrix — and even calls it that in its own
docstring.  It was invisible to every absorption pass because it is filed under `Geometry` and
stated for a general matrix rather than a companion one.  Specialised in `PowerSumCases.lean` as
`minorSum_companionMatrix` and `trace_companionMatrix_sq`, it closes `k = 2` at `d = 2` for
**arbitrary** coefficients — the first non-family-specific instance of that regime in the library.

**(b) Three `Geometry` modules share one object and never mention each other.**  `Hopf.lean`,
`S3Quaternion.lean` and `SU2SO3.lean` all work with the unit quaternions, `Quaternion.normSq q = 1`
— 29, 48 and 55 occurrences respectively — and **none imports another**.  `S3Quaternion` proves the
condition is closed under multiplication and star; `SU2SO3` builds a multiplicative map with
`su2_det = normSq`; `Hopf` carries the hypothesis through independently.  Same shape as §1.6: one
object, three independent developments, no shared statement.  **Not acted on** — unlike the golden
ratio case, there is no shipped general theory here for them to be instances *of*, so the honest
move is a `Geometry/UnitQuaternion.lean` that states the group structure once, and that is a new
module rather than an absorption.  Recorded, not built.

**(c) `Order/` and `Logic/` define structures nothing outside their own files used — and the
first version of this finding overstated it, twice.**  What was measured is that `Superadditive`,
`Tolerance` and `Stack`/`Admits` have **zero occurrences outside their own files**.  What was
written was that nothing instantiated them.  That is a different claim and it is false for two of
the three:

* `Order/Superadditive.lean` line 91 carries `example : Superadditive id`.
* `Order/Tolerance.lean` ships `natTolerance : Tolerance ℕ ℕ`, built from `Nat.dist`, with two
  `example`s — and its docstring says in as many words that it is there "witnessing that the
  definition is inhabited".

Both were inside the files, and the grep that produced the finding excluded exactly those files.
Only `Logic/PredicateStack.lean` genuinely had no concrete stack: `Stack` appears in its own
theorems, but no list of actual predicates is ever built.

What survives, stated at the strength it was measured: none of the three had an instance drawn from
*another* module, so their theorems said nothing about the library's own objects.

Fixed for two of the three, in the corrected sense.  `mersenne` is superadditive
(`superadditive_mersenne` in `Mersenne.lean`) — not the first instance, `id` was, but the first
**non-trivial** one and the first edge from `NumberTheory/` to `Order/`.  And `openSimplex` is a
two-predicate stack (`openSimplexStack`, `admits_openSimplexStack_iff` in `Simplex/Basic.lean`),
which is `PredicateStack`'s first concrete stack and the first edge from `Simplex/` to `Logic/`;
`Stack.admits_of_append_right` then says something about simplex membership, shipped as an
`example`.  The candidates were separated numerically first, and the property
discriminates: `mersenne` and `tribonacci` pass on `m, n < 18` with no failures, while `Nat.fib`
and `jacobsthal` **fail**, each exactly once, at `(1,1)` — `fib 1 + fib 1 = 2` against `fib 2 = 1`.
`tribonacci` is measured superadditive and **not proved**; it needs an induction that was not done.

**`Tolerance` is now settled too, and the answer was in its own header.**  That header says the
structure is "a pseudometric with the codomain and its order abstracted out" — a claim the module
asserted and never proved.  Proved, it is the bridge:
`pseudoMetricTolerance (α) [PseudoMetricSpace α] : Tolerance α ℝ≥0`, from `nndist_self` and
`nndist_comm`.  The widths are `ℝ≥0` rather than `ℝ` because they need an `OrderBot`, which is
exactly why the structure quantifies over an `OrderBot` preorder in the first place.

That single definition makes every metric object in the library an instance without further work,
and two are shipped as `example`s: the simplex's ambient `ι → ℝ`, and the quaternions that
`S3Quaternion.lean` and `SU2SO3.lean` work in.  `natTolerance` is **not** subsumed — its widths are
`ℕ`, not `ℝ≥0` — so it remains the witness that varying `E` buys something, which is the module's
own stated motivation, now with a second data point.

All three of §1.12(c)'s modules now have an instance drawn from another part of the library.

**`Tolerance` is nonetheless recorded as speculative, and round 14 overstated what it settled.**
Having an instance is not the project's bar; having a *consumer* is.  Measured:
`grep -rn 'Tolerance' ClassicalLean/ --include=*.lean` outside its own file returns **0**.  No
theorem in the library is stated in terms of it, and for a metric space every result it proves is a
one-line consequence of Mathlib's `dist` API — so the generality is currently unused.  The one
thing the abstraction buys, widths outside `ℝ≥0`, has exactly one witness (`natTolerance`) and no
consumer either.

By the project's test in `HANDOFF.md` — "porting would add names, not results" — that is a
generalisation in search
of a use case.  It is kept, not retired: the abstraction is correct and cheap, and a future module
needing graded closeness with non-real widths would want it.  But it should not be counted as
evidence the library does order theory.  The module header now says so.  What would retire the
word: a theorem whose statement genuinely needs `Tolerance` rather than `dist` — one where `E` is
not `ℝ≥0`, or where the triangle inequality is unavailable.

The same question is open, and **not** yet answered, for `Superadditive` and `PredicateStack`:
each now has a genuine instance, but neither has a theorem stated in its terms outside its own
file.  Only `Tolerance` was audited on the consumer criterion.

**Correction and answer, 2026-09-23 (round 16, order 0923).**  The paragraph above is kept as
written, and it is false as worded: `superadditive_mersenne : Superadditive mersenne`
(`Mersenne.lean:160`) and `admits_openSimplexStack_iff` (`Simplex/Basic.lean:78`) *are* theorems
stated in those modules' terms outside their own files.  What it meant is the consumer criterion,
now written out: a shipped declaration outside the defining file that uses the definition or its
lemmas to prove something not stated in its terms; an `example` creates no constant and does not
count.  Measured at the constant layer — every constant of the built library, comparing what its
type and its proof term mention:

| module | outside users | stated in its terms | consumers |
|---|---|---|---|
| `Order/Superadditive.lean` | 1 — `superadditive_mersenne` | 1 | **0** |
| `Logic/PredicateStack.lean` | 3 — `openSimplexStack`, `openSimplexStack.eq_1`, `admits_openSimplexStack_iff` | 3 | **0** |

The consumer-shaped uses exist only as `example`s (`Mersenne.lean` lines 171 and 173;
`Simplex/Basic.lean` lines 91–95).  Text layer, beside it: `grep -rn 'Superadditive' ClassicalLean/
--include=*.lean` outside its file returns 6 lines, all in `Mersenne.lean`; `grep -rn 'Stack'`
likewise returns 12, all in `Simplex/Basic.lean`.  **Verdict for both: the standing of `Tolerance`
— an instance, no consumer.  Both are kept**; retiring a module is not an audit's call.  The audit
script and its output are in round 16's fragment.

---

### 1.13 The `Simplex` order batch (G-3, G-2) — what it closed, and what it did not

Recorded late, on 2026-09-08. Both modules shipped on 2026-09-07 and neither was named in this
file until now; round 10a, in the archived history, carries the full account and
`records/README.md` carries
the mechanism that is meant to stop it recurring.

**`Simplex/Symmetry.lean` (`b525cef`) closed a loop §1.12 did not name.** `Ordered.lean` proves
the sorted simplex is a fundamental domain for the coordinate-permutation action, and `HANDOFF.md`
§2b recorded that nothing consumed it. It has a consumer now:
`exists_mem_orderedSimplex_logSumExp_eq`, reached through `logSumExp_comp_perm` and
`softmax_comp_perm`. The sharper half is negative —
`exists_mem_openSimplex_freeEnergy_comp_perm_ne` exhibits `![1/3, 2/3]` and a swap at `T = 0`,
so the free energy is **not** invariant, and `Gibbs.convexOn_barrier`'s docstring no longer has to
say that no declaration asserts it. 11 theorem constants.

**`Simplex/Temperature.lean` (`ed5b176`) found a shared object three modules were spelling out by
hand.** `levelGap n E`. `Gibbs.gibbsWeight`, `Involution.twoLevelEnergy` and the
`DesignConstants` threshold are all instances of it, and `gibbsWeight_eq_softmaxT` states the
first as an unconditional identity in `T`. 25 theorem constants, 2 definitions.

**What it did not close.** §1.5 asked for a statement using a number-theoretic fact and an
optimisation fact at once. This batch connects two *optimisation* modules to each other. The
golden ratio still appears on both sides of the library for reasons this file has no theorem
about, and §1.5's honest sentence stands.

**The detector, which is reusable.** Round 14 found `Tolerance`'s instance by reading a module
header as a specification rather than as commentary; this batch found `levelGap` the same way.
Both are cheaper than §1.10's structural grep: read what a module *says* it is for, then check
whether the library already contains the thing it names. §1.10's grep finds shared structure the
prose never mentions; this one finds structure the prose mentions and Lean never states. They fail
on different things, so run both.

### 1.14 The information-geometry corner: seven patterns, three proved (order G-6)

**Dated 2026-09-24 UTC (order G-7, round 23):** five are proved now: P4 and P5 in round 23.
**Dated 2026-09-24 UTC (order G-7, round 24):** six: P6 in round 24. P7 remains.

Measured by claude-ai on 2026-09-23 (order G-6 §0 rows 4–6 and 9) with symbolic and numeric
checks; the first three are proved in round 21 (`records/rounds/20260924T005338Z__round-21-…`).
Each entry names its hypotheses.

- **P1 — the free energy's Hessian is `T` times the Fisher–Rao metric, plus a barrier.**
  *Proved, round 21* (`Simplex/SecondOrder`): `hessian_eq_smul_fisherRaoChart_add` and
  `fisherRao_eq_fisherRaoChart`, no hypothesis (identities in the same inverses, true at
  `0⁻¹ = 0`); `fisherRaoChart_posDef` for `lam`, `kap`, `1 - lam - kap` positive.
- **P2 — the covariance of a one-hot draw inverts the Fisher–Rao metric, and is the softmax
  Jacobian.** *Proved, round 21* (`Simplex/SecondOrder`): `categoricalCov_mulVec_div` and
  `fisherRao_categoricalCov_mulVec` (no `p i` zero, tangent vector summing to `0`),
  `fisherRaoChart_mul_categoricalCov` (`lam`, `kap`, `eta` nonzero), `categoricalCov_posSemidef`
  (`0 ≤ p`, `∑ p ≤ 1`), `hasDerivAt_softmax_categoricalCov` (no hypothesis). The composite "the
  Hessian of `logSumExp` is `categoricalCov (softmax x)`" is now proved, *order LEAN-18, round 46*
  (`Simplex/SecondOrder`, `da86558`), no hypothesis: `hasFDerivAt_logSumExp` (the derivative of
  `logSumExp` is the softmax functional), `hasFDerivAt_softmax` (the derivative of `softmax` is
  `categoricalCov (softmax x)`), and `hasFDerivAt_fderiv_logSumExp_apply` (so the derivative of
  `y ↦ fderiv logSumExp y v` is `v ᵥ* categoricalCov (softmax x)`, one direction `v` at a time).
- **P3 — Gauss–Markov in weighted coordinates is Cramér–Rao on a finite outcome set.** *Proved,
  round 21* (`Statistics/CramerRao`): `posSemidef_weightedCov_sub_inv_secondMoment` (`0 ≤ p` and
  the cross-moment identity; `∑ p = 1` and `E S = 0` not needed), the equality case
  `weightedCov_eq_inv_secondMoment_iff` (every weight positive), and the categorical family in
  P1's chart attaining the bound.
- **P4 — the Fisher–Rao metric is spherical.** *Measured by claude-ai 2026-09-23, not proved*:
  for `x` with no zero coordinate, `fisherRao (x²) (2x⊙v) (2x⊙w) = 4 ⟨v, w⟩` (symbolic). It would
  join `Geometry/S3Quaternion`'s `sqCoords` to `Simplex/FisherRao` (see §1.5's dated line).
  *Proved, round 23* (order G-7): `Simplex/SecondOrder`'s `fisherRao_sq_two_mul`, with no
  hypothesis (the sum runs over the coordinates where `x ≠ 0`), and
  `fisherRao_sq_two_mul_of_ne_zero`; `Geometry/S3Quaternion`'s `fisherRao_sqCoords`.
- **P5 — the Hopf map is an orbit of the rotation action.** *Measured by claude-ai 2026-09-23, not
  proved*: `Geometry/Hopf`'s map is the `(k, j, i)` components of `q̄ * i * q`, which is
  `Geometry/SU2SO3`'s `adjoint (star q) i` (symbolic; the hypotheses on `q` were not recorded).
  *Proved, round 23* (order G-7): `Geometry/Hopf`'s `adjoint_star_eq_hopfMap` and
  `hopfMap_eq_adjoint_star`, for every `q`, no hypothesis.
- **P6 — the law of apparition `α(p) ∣ p − (D/p)`.** *Measured by claude-ai 2026-09-23, not
  proved*: 684 checks over 9 pairs `(P, Q)`, primes below 400 not dividing `2QD`, 0 failures. Its
  split case `(3, 2)`, `D = 1`, is Fermat's little theorem in `MersenneOrder`;
  `LucasApparition` says the general bound is not proved. A candidate in `HANDOFF.md` §3.
  *Proved, round 24* (order G-7): `NumberTheory/LucasApparition`'s
  `lucasApparition_dvd_sub_legendreSym` (odd `p ∤ Q`) and `prime_dvd_lucasU_sub_legendreSym`.
- **P7 — majorization.** *Measured by claude-ai 2026-09-23, not proved*: Mathlib's own TODO,
  `Analysis/Convex/Birkhoff.lean:29–30`, "`x` is majorized by `y` if and only if there is a doubly
  stochastic matrix `M` such that `M *ᵥ y = x`". The library has entropy under doubly stochastic
  matrices (`InformationTheory/Channel`), the sorted simplex as a fundamental domain
  (`Simplex/Ordered`) and permutation invariance (`Simplex/Symmetry`), and never names
  majorization. At v4.34.0 `grep -rniE 'majoriz' Mathlib --include=*.lean` gives 68 lines: the
  Birkhoff TODO, the Schur–Horn TODO at `Analysis/InnerProductSpace/Spectrum.lean:47`, and an
  unrelated asymptotics predicate `Majorized`. A candidate in `HANDOFF.md` §3.

### 1.15 Bridges between the library's islands (order G-7, round 23)

Measured with claude-ai's declaration graph (order G-7 Appendix A: a module uses another when a
constant of one names a constant of the other in its type or value). At `cca6f8a` six modules used
no other module and were used by none: `Combinatorics/AlgebraicGeneratingFunction`,
`Geometry/Hopf`, `Geometry/SU2SO3`, `NumberTheory/Catalan`, `NumberTheory/CompositumDiscriminant`,
`Order/Tolerance`. After round 23, four: `Hopf` and `SU2SO3` left the list. The four that remain are
recorded, not bridged; retiring any module is Dustin's decision.

- **P5, the Hopf map is the orbit of `i`** (step 2): joins `Geometry/Hopf` to `Geometry/SU2SO3`.
- **P4, the squaring map** (step 3): joins `Geometry/S3Quaternion` to `Simplex/SecondOrder`.
- **P8, the Fisher–Rao metric contracts under a channel** (step 4): `fisherRao_vecMul_le`, for
  `0 ≤ p` with `p i = 0 → u i = 0`, `0 ≤ W` and row sums at most `1` (each necessary), `W`
  rectangular; the second-order companion of `relEntropy_vecMul_le`. It gives
  `InformationTheory/Channel` its first user.
- **The order of `2`** (step 5): every `n` except `1` and `6` is the order of `2` modulo a prime;
  `NumberTheory/Zsigmondy` now uses `NumberTheory/MersenneOrder`, its second user.
- **The duplicates** (step 6): claude-ai's duplicate check found two statements proved twice,
  `φ² + (φ²)⁻¹ = 3` and `(φ²)⁻¹ = ψ²`, in `Geometry/Helix` and `Simplex/DesignConstants`, modules
  that do not import each other. By claude-ai's ruling (order G-7 §2; Dustin's veto open) they have
  one statement, one name and one home, `GoldenRatio/Characterisations`; the duplicate check now
  reads 5 `TWIN` lines and 0 `SWAP` lines, the five deliberate "Mathlib re-export"s.
- **Mathlib's `docs/1000.yaml`** (order G-7 §0 row 12, claude-ai's measurement at v4.34.0, not
  re-run here): of 1199 entries, 955 carry no `decl`, `decls` or `url`. Among them: Zsigmondy's
  theorem (Q8074796; its statement is for `aⁿ − bⁿ`, and the library proves `b = 1`), Gauss–Markov
  (Q428134; the library proves the matrix form, round 20), and, not in the library, the
  Frisch–Waugh–Lovell theorem (Q1059151), Cochran's theorem (Q599876), Carmichael's theorem
  (Q3889376), Lamé's theorem (Q230848), max-flow min-cut (Q608294), Menger's theorem (Q928813) and
  Rao–Blackwell (Q579515). Q7686760 "Bang's theorem" is Tarski's plank problem, not the `b = 1`
  case of Zsigmondy's theorem, so the library does not claim it. Listing anything there needs a
  public URL, and is Dustin's decision.

A caveat on the evidence: after step 4 the type dump of two unchanged theorems,
`hasDerivAt_softmax` and `hasDerivAt_softmax_categoricalCov`, differs from `cca6f8a`'s inside one
`Prop`-valued instance argument (`ContinuousSMul ℝ ℝ`), because the new import widens instance
search; the statements are definitionally equal, checked in Lean (round 23).

**Dated 2026-09-24 UTC (order G-8, rounds 25 and 26):** three islands remain,
`NumberTheory/Catalan`, `NumberTheory/CompositumDiscriminant` and `Order/Tolerance`:
`AlgebraicGeneratingFunction` now uses `RecurrenceGeneratingFunction` (J3b). The pair
`LucasApparition ~ Zsigmondy` (order G-8 §0 row 6) is an edge: `Zsigmondy` uses `LucasApparition`
(J2c), and the new module `NumberTheory/ZsigmondyPowSubPow` uses both, with `LucasSequence` and
`PrimitiveDivisor`. Appendix A on the landed tree (`after.sh j3b`): 49 modules, 1617 constants, 82
edges; `pairs.py` lists 87 pairs of modules with no edge between them that share a rare constant
(84 at `87683e3`); `DupCheck` 5 `TWIN`, 0 `SWAP`. The library now proves Q8074796's statement in
full (§2.5); listing it in `docs/1000.yaml` is Dustin's decision.

**Dated 2026-09-25 UTC (order G-9, rounds 27 and 28):** still three islands. The new module
`NumberTheory/EuclidSteps` uses `NumberTheory/Lucas` — an edge, not a fourth island — and J3 adds
no module and no use between modules. Appendix A on the landed tree (`after.sh j3`): 50 modules,
1673 constants, 83 edges; `pairs.py` lists 91 pairs of modules with no edge between them that
share a rare constant (90 after J2, 87 at `196a87d`); `DupCheck` 5 `TWIN`, 0 `SWAP`.

**Dated 2026-09-25 UTC (order G-10, rounds 29 and 30):** **two islands** remain,
`NumberTheory/CompositumDiscriminant` and `Order/Tolerance`. `NumberTheory/Catalan` left the list
(round 29: the new `NumberTheory/Wolstenholme` uses it, `succ_mul_catalan_eq_choose`, so `Catalan`
is `usedBy=1`); the new `Statistics/FrischWaughLovell` (round 30) uses `Statistics/GaussMarkov`
(`usedBy=2` — `CramerRao` and `FrischWaughLovell`) and so is no island. Appendix A on the landed
tree: 52 modules, 1782 constants, 85 edges; `pairs.py` 97 pairs (90 after J2); `DupCheck` 5 `TWIN`,
0 `SWAP`.

### 1.16 What correlated quantities are worth (order LEAN-15, round 43)

`Probability/EffectiveSampleSize` (new) proves the variance of a plain average as the average of all
covariances, Kish's design effect for unit variances, and the bound for lag correlations
`ρ ^ |i - j|`. It imported only Mathlib when order LEAN-15 added it; since order LEAN-16 it also
imports `Combinatorics/RecurrenceGeneratingFunction`, so by §1.15's measure it is no longer an
island. No module uses it yet (measured 2026-10-09 UTC: `grep -rln EffectiveSampleSize
--include=*.lean ClassicalLean ClassicalLean.lean` lists only the module and the root file). The
declaration graph of §1.15 was not re-run, so its last count, two islands (2026-09-25), is not
re-measured here.

- **The program's design effect.** LEAN-8's program uses `n / (1 + (m - 1) ρ)` without proof
  (measured 2026-10-09 UTC: `~/trading/paper/paper/many.py`, docstring line 12, "Kish design effect
  n / (1 + (m - 1) rho+)"). `variance_average_eq` proves the identity behind it: with unit
  variances the average of `k` quantities has variance `(1 + (k - 1) r) / k`, `r` the mean
  cross-covariance. The program adds two assumptions the theorem does not make: equal variances,
  and that trades which do not overlap are uncorrelated, which makes `r = (m - 1) ρ / (n - 1)`;
  and it uses one pooled correlation, floored at 0, for the mean correlation of overlapping pairs.
- **A bridge to combinatorics, proved (order LEAN-16, round 44).** The double sum
  `S(n) = ∑ i < n, ∑ j < n, ρ ^ |i - j|` of `sum_sum_pow_eq` satisfies
  `S(n + 3) = (2 + ρ) S(n + 2) - (1 + 2ρ) S(n + 1) + ρ S(n)` for every `ρ`, `ρ = 1` included, and
  `Combinatorics/RecurrenceGeneratingFunction`'s `isSolution_iff_coeff_recDenom_mul_mk` gives it the
  generating function `(x + ρ x²) / ((1 - x)² (1 - ρ x))`:
  a `LinearRecurrence ℝ` of order 3 with `coeffs = ![ρ, -(1 + 2ρ), 2 + ρ]` (`coeffs i` multiplies
  `u (n + i)`), `recDenom` `(1 - X)² (1 - ρ X)`, numerator `X + ρ X²` from `S 0, S 1, S 2`. Measured:
  order LEAN-15's check script, output line `C4 P6b recurrence: OK | order-3 recurrence, initial
  values and the generating function's coefficients all exact` (eight values of `ρ`, rerun
  2026-10-09, output identical to the lane copy). Proved in order LEAN-16:
  `EffectiveSampleSize.isSolution_sumSumPow` (the recurrence `sumSumPowRec ρ`) and
  `EffectiveSampleSize.recDenom_mul_mk_sumSumPow` (`(1 - X)² (1 - ρ X) ∑ S n Xⁿ = X + ρ X²`);
  order LEAN-16's check script, line `C7 P10 bridge: OK | seven values of rho, coefficients
  0..40`, checks the product's coefficients exactly.

### 1.17 A bridge to online learning (order LEAN-16, round 44)

`Analysis/UniversalMixture` (new) proves that running several stake rules side by side, each on an
equal share, is itself one rule (`mixStake`, `sum_prod_div_card_eq_prod_mixStake`,
`mixStake_mem_Icc`), whose stake by its definition uses only the past, and that on every sequence
with positive factors its log product is at least each rule's less `log (card s)`
(`log_prod_sub_log_card_le`; one-sided). For the `K + 1` fixed stakes `0, l/K, …, l` this gives
`le_log_mixture`: at least the log product of the best fixed stake in `[0, l]` chosen in hindsight,
less `log (K + 1) + N (l / K) D / (1 - l c)`, with no probability model. This is Cover's universal
portfolio (1991) for one stream of values and cash, in a discrete form, and the library's first
result of the online-learning kind (a regret bound). It imports only Mathlib and no module uses it
yet, so it is an island by §1.15's measure until a consumer lands. Measured: the statements are
order LEAN-16's `LEAN-16-statements.lean` (item 6), and its check script's output lines
`C6 P9 exact: OK | 2000 cases: identity, stake range, log(card) gap` and
`C6 P9 mixture bound: OK | 2000 random sequences` (rerun 2026-10-09 UTC, output identical to the lane
copy).

### 1.18 Batch 1 of the second plan (order LEAN-27, round 56)

Items 79 to 83 of MATH-PLAN-library-2, each a base that a later item of that plan rests on:

* `Analysis/ConvexConjugate` (new, item 79): the convex conjugate `f* y = ⨆ x, (y ⬝ x − f x)`
  valued in `EReal`, Fenchel–Young for real `f`, `f ≤ g ⇒ g* ≤ f*`, `f** ≤ f`, and both sides of the
  supremum (`sub_le_convexConjugate`, `convexConjugate_le_iff`) for item 117 (the conjugate of
  log-sum-exp).
* `Probability/EffectiveSampleSize` (item 80): `Var (X 0 + ⋯ + X (k − 1)) = k γ 0 +
  2 ∑_{1 ≤ j < k} (k − j) γ j` for a covariance-stationary series, the variance-ratio identity, and
  the `ℕ`-indexed form for item 115.
* `Statistics/GeneralizedLeastSquares` (item 81, a bridge): for a common mean, generalised least
  squares is `MinimumQuadraticForm.minWeights`, with variance factor `1 / (1ᵀ V⁻¹ 1)`. The two
  modules are now import-related (the bridge search's pair is gone); item 98 rests on it.
* `Algebra/Kantorovich` (new, item 82): `(xᵀ A x)(xᵀ A⁻¹ x) ≤ ((m + M)² / (4 m M)) ‖x‖⁴` for
  `m ≤ A ≤ M`, `0 < m`, and equality at an equal mix of eigenvectors; items 98 and 111 rest on it.
* `Algebra/MinMax` (item 83): Ky Fan's maximum principle, the sum of the `k` largest eigenvalues as
  the largest `∑ re ⟪T uᵢ, uᵢ⟫` over orthonormal families; item 142 rests on it (for matrices, use
  `eigenvalues₀`, the module docstring says how).

### 1.19 Batch 2 of the second plan (order LEAN-28, round 57)

Items 84 to 88 of MATH-PLAN-library-2 and item 80b, all in existing modules:

* `Probability/GamblersRuin` (item 84, a bridge to `Probability/MaximalInequality`, which it now
  imports): the biased walk leaves `(−b, a)` with chance `1`, reaches `a` first with chance
  `(r^b − 1)/(r^(a+b) − 1)`, and, when it drifts down, ever reaches `a` with chance at most
  `(p/q)^a` (Ville's inequality on `r^(walk)`); item 95 rests on it.
* `Analysis/FiniteGame` (item 85): item 66's second proof of the minimax equality, for every real
  matrix (an affine change of payoffs), without Sion's theorem.
* `Combinatorics/ArbitrageCycle` (item 86): item 65's exact counterexamples as Lean `example`s.
* `Probability/LongestRun` (item 87): item 69's open point settled: the measurability hypothesis is
  needed (a Lean `example`), and only for the trials that count.
* `InformationTheory/CompressionTest` (item 88): compression scores, each against its own null law,
  fed to e-BH (`Probability/EValueStepUp`, now imported) keep the expected false share at most `q`;
  the measure must be a probability measure (with a finite measure the statement is false, through
  Lean's value for the law of a string that is not measurable).
* `Probability/EffectiveSampleSize` (item 80b): the variance-ratio identity in the plan's product
  form, `variance_sum_eq_mul_one_add`, with no extra hypothesis (closes LEAN-27's narrowing in form).

### 1.20 Batch 3 of the second plan (order LEAN-29, round 59)

Items 91 to 95 of MATH-PLAN-library-2, one new module and four extended; narrowing: none; item 95
is wider than item 84 (no `p ≠ 1/2`):

* `Probability/LongestRun` (item 91, the lower side of item 69's `log₂ n` reading): no run of `r`
  losses has chance at most `exp (−⌊n / r⌋ q^r)` (`measureReal_no_run_le_exp`), from the
  `(1 − q^r)^⌊n / r⌋` bound and `1 − x ≤ e^(−x)`.
* `Analysis/Gruss` (new, item 92): Grüss's inequality, `|cov[X, Y]| ≤ (M − m)(N − n)/4` for
  bounded random variables, and its form for averages of functions on `[a, b]`; the covariance's
  Cauchy–Schwarz inequality is proved inside, by the discriminant argument (Mathlib v4.34.0 has
  none).
* `Analysis/Simpson` (item 93): Richardson's identity, exactly: the library's Simpson rule is
  `(4 T(2N) − T(N))/3` with Mathlib's trapezoidal rule `T`, for every `f`, `a`, `b`, `N`.
* `Analysis/EulerMethod` (item 94): for `y' = −c y`, `c > 0`, implicit Euler decays to `0` for
  every step `h > 0`, and explicit Euler from `y₀ ≠ 0` decays exactly when `h c < 2`.
* `Probability/GamblersRuin` (item 95, a bridge to `NumberTheory/LucasSequence`, which it now
  imports): the ruin chance is `U b / U (a + b)` with `U = lucasU (1 + r) r`, `r = (1 − p)/p`, for
  every `0 < p < 1`, the fair walk included (at `p = 1/2`, `U n = n`).

Also job 0: the convex conjugate's junk-value checks and the stronger form of
`exists_isPrimitiveDivisor_of_forall_prime_dvd` (`0 < a`) are now `example`s in their modules
(`Analysis/ConvexConjugate`, `NumberTheory/PrimitiveDivisor`).

### 1.21 Five items from below the plan's cut (order CLOUD-MATH-1, round 60; merged by MERGE-1, round 61)

Items 131, 135, 136, 137 and 139 of MATH-PLAN-library-2 sit below the plan's cut. Their proofs
were drafted and reviewed outside the library (`~/api-credit`); order CLOUD-MATH-1 landed them as
five new modules in a cloud session on the GitHub branch `cloud-math-1`, each with witnesses and a
cold review, and order MERGE-1 merged that branch into `master` on DSMain. Narrowing: none;
`fw_general` and `ae_mem_Icc_of_tendsto_urnShare` are wider than their plan rows:

* `InformationTheory/HanInequality` (item 131): Han's inequality,
  `(n − 1) H(X) ≤ ∑ᵢ H(X without coordinate i)` for a joint law of `n` coordinates
  (`mul_shannonEntropy_le_sum`), from strong subadditivity.
* `Analysis/FrankWolfe` (item 135): Frank–Wolfe with step `2/(k + 2)` on the closed simplex gives
  `f (x k) − f z ≤ 4 L / (k + 2)` (`sub_le_of_frankWolfe`); `fw_general` gives
  `2 L D / (k + 3)` on any convex set of squared diameter at most `D` in a real Hilbert space.
* `Analysis/StatePrices` (item 136): one-period asset pricing, finite form: no arbitrage exactly
  when there are strictly positive state prices `ψ` with `Dᵀ ψ = π`
  (`exists_pos_statePrices_iff`), from the library's Farkas lemma.
* `Probability/PolyaUrn` (item 137): the red share of Pólya's urn is a martingale
  (`martingale_urnShare`), converges almost surely (`ae_tendsto_urnShare`), and any almost-sure
  limit of it lies in `[0, 1]` (`ae_mem_Icc_of_tendsto_urnShare`).
* `Probability/Reflection` (item 139): the reflection principle for the fair `±1` walk,
  `P(max_{k ≤ n} S_k ≥ a) = P(S_n ≥ a) + P(S_n > a)` for `a ≥ 1` (`measureReal_max_ge_eq`).

### 1.22 Batch 4 of the second plan (order LEAN-30, round 62)

Items 96 to 100 of MATH-PLAN-library-2, no new module, four extended. Narrowing: none. Wider than
the plan's reading, five conditions: item 96 for any finite measure; item 97 with a stationary `π`
that need not be a law; item 100's uniqueness with no `P ≥ 0` and no `k > 0`, and its rate with no
`k > 0`. Also, as written in the order's statements, not a new change: item 97's `μ` need not sum
to `1`, and item 100's rate takes any real `δ`, `μ` of any sign and any stationary `π` with `μ`'s
total.

* `Probability/CovarianceDirections` (item 96, a bridge to `Algebra/HadamardInequality`, which it
  now imports): Hadamard's inequality for a covariance matrix, `det S ≤ ∏ i, Var(X i)`
  (`det_covMatrix_le_prod_variance`): the generalised variance is at most the product of the
  variances.
* `Probability/FiniteChain` (item 97, a bridge to `InformationTheory/Channel`): relative entropy to
  a stationary vector never increases along the chain (`relEntropy_vecMul_le_of_stationary`),
  through `|π|` and the data-processing inequality.
* `Statistics/GeneralizedLeastSquares` (item 98, a bridge to `Algebra/Kantorovich`, which it now
  imports): Bloomfield and Watson's bound for a common mean,
  `(1ᵀ V 1)(1ᵀ V⁻¹ 1)/n² ≤ (m + M)²/(4 m M)` (`onesQuad_mul_onesInvOnes_le`).
* `InformationTheory/CompressionTest` (item 99, item 68's plug-in argument in Lean): the plug-in
  score, with the string's own win rate `winRate` in the null law, is at most every fixed-rate
  score wherever the fixed rate gives the string positive mass (`score_plugIn_le`), and its
  false-alarm rate stays at most `α` under every Bernoulli law (`measureReal_score_plugIn_ge_le`;
  the strings of mass `0` are handled apart); by the weighted arithmetic–geometric mean inequality.
* `Probability/FiniteChain` (item 100): Perron–Frobenius for a primitive chain, `P ^ k` positive
  though `P` may have zeros: one stationary distribution (`existsUnique_vecMul_eq_self_of_pow`) and
  the rate `(1 − n δ) ^ (t / k)` (`sum_abs_vecMul_pow_sub_le_of_pow`). Mathlib's
  `Matrix.IsPrimitive` meets the hypothesis through `exists_pos_pow`; it is not imported.

Also job 0: five older docstring lines of `NumberTheory/PrimitiveDivisor` and `Analysis/Gruss`
are checkable from the library or say they report past runs, and PrimitiveDivisor gains one
`example` naming the two Lifting the Exponent lemmas it cites.

### 1.23 Batch 5 of the second plan (order LEAN-31, round 63)

Items 101 to 105 of MATH-PLAN-library-2, one new module, six extended. Narrowing: none. Wider than
the plan's reading, two conditions: item 105 for any finite measure, not only a probability
measure; item 104's Chernoff bound with no `p₀ < 1`. Item 104's `q ≤ 1` and `0 < p₀` are kept
though not needed. Items 103 and 104 land the carried drafts of API-credit carry list 1 (rows 103
and 104), with primed names beside the unprimed theorems, which stay.

* `Probability/MovingAverage` (item 101): the spectral density of a moving average, finite form,
  `∑_{|k| ≤ q} γ(|k|) e^(−i k φ) = v |∑ⱼ θⱼ e^(i j φ)|²` (`sum_covariance_mul_cexp_eq`), and that
  it is never negative, in real form (`zero_le_sum_covariance_mul_cos`).
* `Statistics/Sufficiency` (item 102): bounded completeness (`IsBoundedlyComplete`), that
  completeness gives it (`IsComplete.isBoundedlyComplete`), and Basu's theorem with it
  (`indep_of_isSufficient_of_isBoundedlyComplete_of_isAncillary`), wider than item 58's.
* `Analysis/FiniteGame` (item 103, item 63's open point closed): Bayes equals minimax for a finite
  decision problem with losses in `[0, ∞]` (`iSup_bayesRisk_eq_minimaxRisk_of_finite'`).
* `Statistics/ResidualVariance`, `Probability/LikelihoodScore`, `Probability/EffectiveSampleSize`
  (item 104, the generalisations LEAN-17's reviews r3, r5 and r6 proved): the residual variance for
  any measure (`integral_residual_sq'`), the relative-entropy Chernoff bound at `q = 1` and with no
  `p₀ < 1` (`measureReal_sum_ge_le_exp_neg_relEntropy'`), and the steady AR(1) average's variance
  bound with no measure instance (`variance_average_le_of_steady'`, witnessed through Mathlib's
  `Measure.infinitePi`).
* `Probability/StepDownProcedure` (item 105, new): Holm's step-down procedure (`holmRejected`)
  keeps the chance of rejecting any true null at most `q`, under any dependence and any finite
  measure (`measureReal_exists_holmRejected_true_le`), beside the Benjamini–Hochberg step-up
  procedure.

Also job 0: the Bloomfield and Watson credit in `Statistics/GeneralizedLeastSquares` is complete
and marked as checked against the journal's contents page.

### 1.24 Batch 6 of the second plan (order LEAN-32, round 64)

Items 106 to 110 of MATH-PLAN-library-2, one new module, four extended. With this batch the six
batches of MATH-PLAN-library-2 above its cut are done; what comes next (rows below the cut, a third
plan, or something else) is claude-ai's to propose and Dustin's to decide. Narrowing: none. Wider
than the plan's reading, five conditions: item 107 for any measure `ν₀`, and its first theorem with
no "`F` differs from `F₀`" hypothesis; item 108 with no positive definiteness and no symmetry of
`P`; item 109's law hypothesis; item 109 with pairwise independence only; item 110 with `q ≥ 0` and
the support condition. Item 107's second theorem is an addition.

* `Probability/IntegralTransform` (item 106, new): the probability integral transform,
  `P(F(X) ≤ u) ≤ u` for every `u ≥ 0` (`measureReal_cdf_le_le`), so a threshold test's p-value is
  valid, and `F(X)` uniform on `[0, 1]` when `F` is continuous
  (`measureReal_cdf_le_eq_of_continuous`).
* `Probability/GlivenkoCantelli` (item 107): the Kolmogorov–Smirnov test is consistent
  (`eventually_lt_sup_abs_empiricalCDF_sub`), and its test with thresholds `c n → 0` rejects
  eventually when `F` differs from `cdf ν₀` (`eventually_lt_sup_abs_empiricalCDF_sub_of_tendsto`),
  from item 60.
* `Analysis/LinearODE` (item 108): a Lyapunov bound for `x' = A x`, `x(t)ᵀ P x(t) ≤ e^(−2ct)
  x(0)ᵀ P x(0)` for `t ≥ 0` (`quadForm_le_exp_mul`).
* `InformationTheory/MethodOfTypes` (item 109): the asymptotic equipartition property,
  `−(1/n) ∑ log p(X i) → H(p)` almost surely (`tendsto_neg_log_div_shannonEntropy`), the strong law
  for `−log p(X i)`.
* `InformationTheory/Channel` (item 110): data processing for every f-divergence on finite sets
  (`sum_mul_comp_div_vecMul_le`); relative entropy is the case `f x = x log x`.

The witnesses of items 107 and 109 build independent, identically distributed draws with Mathlib's
`Measure.infinitePi` (fair coins on `ℕ → Bool`, uniform letters of `Fin 4`); item 106's equality
uses the standard normal law, Mathlib's `gaussianReal 0 1`.

## 2. Categories to add

Tiered by how much work they do inside the system that already exists, not by how interesting
they sound. Every Mathlib status is measured; the command is in the row.

### Tier 1 — finishes something already started

**2.1 Rank of apparition of a Lucas sequence** — **DONE**, see
`NumberTheory/LucasApparition.lean` (round 7, archived history)

`MersenneOrder.lean` proves that a prime divides `2^n - 1` exactly when the multiplicative order
of `2` divides `n`. Under §1.1 that is: *the rank of apparition of `U(3,2)` at `p`.* The general
statement — for `p ∤ 2QD` there is a least `α(p) > 0` with `p ∣ U_{α(p)}`, and `p ∣ U_m ↔ α(p) ∣ m`
— is HANDOFF §2 item 4 and subsumes the Mersenne case.

What shipped, and the three ways this entry was wrong before the work:

- **"Mathlib: absent"** rested on `grep -rni 'apparition'` → 0, a name search. Re-measured
  against the mathematics, `grep -rnE '… m ∣ … n ↔'` returns **exactly one line**:
  `Pell.y_dvd_iff` (`NumberTheory/PellMatiyasevic.lean:412`). `Pell.yn a1` is `lucasU (2a) 1`,
  checked by elaboration, so Mathlib **does** prove this theorem at `(P,Q) = (2a,1)`. What is
  new is general `(P,Q)`, the `ZMod N` form, and the rank itself. Mathlib does say nothing
  about `fib` modulo anything (0 hits), and has no iff form of `Nat.fib_dvd` — it cannot, since
  `fib 2 ∣ fib 3` and `¬ (2 ∣ 3)`.
- **"Does real work: `MersenneOrder.lean` becomes an instance"** was the wrong test. It closes,
  but `2^m - 1` is geometric, so the rank degenerates to a multiplicative order and the shipped
  two-rewrite proof needs none of the general theory. The instances that carry weight are
  Mathlib's `Nat.fib_dvd` and `Nat.fib_gcd`, both recovered, and the Fibonacci entry point at
  every modulus, for which Mathlib has nothing of the shape.
- **"the existence half needs the quadratic character of `D` mod `p`"** was wrong about which
  half needs it. Existence needs only that the companion matrix is a unit of a finite monoid;
  the quadratic character is needed for the *bound* `α(p) ∣ p - (D/p)`, which is **deferred**
  and remains the substantial open half, along with the sharp existence criterion, the
  repeated-root case `p ∣ D`, and the `lucasV` analogues.

The hypothesis is `IsUnit Q` alone — weaker than the classical `p ∤ 2QD`, and established by
sweeping the alternatives numerically before writing Lean (3 827 108 checks with it, 0 failures;
33 313 failures of 222 222 without).

**Dated 2026-09-24 UTC (order G-7, J3; round 24):** the bound is proved. For an odd prime `p ∤ Q`,
`α(p) ∣ p − (D/p)` (`lucasApparition_dvd_sub_legendreSym`), from the law of apparition
`p ∣ U_{p − (D/p)}` for odd `p` with `p ∣ Q → p ∣ P` (`prime_dvd_lucasU_sub_legendreSym`), which
rests on `U_p ≡ (D/p)` and `V_p ≡ P (mod p)` for every prime; the repeated-root case `p ∣ D` is
included (the index is `p`), and `V_p ≡ P` with `map_lucasV` is proved. Still open here: the sharp
existence criterion, and a `lucasV` analogue of the rank of apparition.

**Dated 2026-09-24 UTC (order G-8, rounds 25 and 26):** at `(P, Q) = (a + b, ab)` the rank of
apparition is the order of `a / b`, in any field, for `a ≠ b`
(`lucasApparition_add_mul_eq_orderOf_div`);
for a prime `p`, `0 < n` and `¬ p ∣ a − b`, `p` is a primitive divisor of `aⁿ − bⁿ` exactly when `n`
is the rank of apparition of `p` in `U(a + b, ab)` (`isPrimitiveDivisor₂_iff_lucasApparition`); and,
for distinct coprime positive integer roots, every `n` except `1`, and except `6` at
`{a, b} = {1, 2}`, is the rank of apparition of some prime
(`exists_prime_lucasApparition_add_mul_eq_iff`, `NumberTheory/ZsigmondyPowSubPow`). That is not the
classical primitive-divisor criterion for Lucas sequences, which excludes the primes of `D`; for
other `(P, Q)` the sharp existence criterion is still open. And `V_p = P ^ p` in any commutative
ring of prime characteristic `p` (`lucasV_prime_eq_pow`; round 24's `V_p ≡ P` over `ZMod p` is its
case), with `dickson 1 a p = X ^ p` in `R[X]` for every `a` (`dickson_one_eq_X_pow_of_charP`), which
Mathlib has at `a = 1`. Still open: a `lucasV` analogue of the rank of apparition.

**Dated 2026-09-25 UTC (order G-9, round 28):** the Frobenius at every index, in any commutative
ring of prime characteristic `p`: `V (p n) = V n ^ p` (`lucasV_prime_mul`) and, for odd `p`,
`U (p n) = D ^ (p / 2) U n ^ p` (`lucasU_prime_mul`); at prime powers `V (p ^ k) = P ^ (p ^ k)`
(`lucasV_prime_pow_eq_pow`) and, for odd `p`, `U (p ^ k) = D ^ (p ^ k / 2)`
(`lucasU_prime_pow_eq_lucasDiscr_pow`); `U p = D ^ (p / 2)` in every commutative ring of odd prime
characteristic (`lucasU_prime_eq_lucasDiscr_pow_of_charP`; round 24 has it over `ZMod p`, where
`p = 2` also holds); `dickson 1 a (p ^ k) = X ^ (p ^ k)` (`dickson_one_prime_pow_eq_X_pow`); and in
characteristic `2`, `V n = P U n` and `U (2 n) = P U n ^ 2`. Still open: a `lucasV` analogue of the
rank of apparition, and the `ExpChar` form a Mathlib reviewer would ask for.

**2.2 Power sums and the companion matrix at order `d`** — **DONE**, see
`Algebra/CompanionMatrix.lean` and `NumberTheory/PowerSumCases.lean`.  The gap claim below was
re-run before starting and held (still 0 hits).  `NacciTrace.lean` **is** absorbed:
`nacciAugmented_eq_trace` proves `A n k = trace (Mₙ ^ k)` unconditionally, turning that module's
own flagged-as-unformalised prose into a theorem, and `LucasCompanion.lean` is absorbed with the
`k = 0` case its own induction could not reach.  What is *not* proved is Newton's `k ≤ d`
regime for arbitrary coefficients; it is proved for the `x^(n+1) - 2x^n + 1` family, by
computing `M ^ m` on the last basis vector in closed form.

§1.2. `(M_f ^ k).trace = p_k` for `M_f` the companion matrix of a monic `f`, over a commutative
ring, plus Newton's identities relating `p_k` to the coefficients.

- Mathlib: **there is no companion matrix in Mathlib at all.**
  `grep -rn 'Matrix.companion\|companionMatrix\|companion matrix' Mathlib --include=*.lean`
  returns **0 hits**. `LinearRecurrence.charPoly` exists (`Algebra/LinearRecurrence.lean`), so
  the characteristic polynomial of a recurrence is there without the matrix that realises it.
- Mathlib, adjacent: power sums as symmetric polynomials **are** present — `MvPolynomial.psum`
  (`RingTheory/MvPolynomial/Symmetric/Defs.lean`) and Newton's identities
  (`.../Symmetric/NewtonIdentities.lean`). `grep -rn 'trace_pow\|powerSum' Mathlib
  --include=*.lean` returns 3 hits, all `FiniteField.trace_pow_card` / `ZMod.trace_pow_card`
  (a Frobenius statement, `trace (M ^ card K) = trace M ^ card K`), not `trace (M ^ k) = p_k`.
  `grep -rln 'Newton' Mathlib/LinearAlgebra/ Mathlib/RingTheory/` returns
  `JordanChevalley.lean` and `Henselian.lean` — Newton's *method* — plus `NewtonIdentities.lean`.
- Does real work: `NacciTrace.lean` and `LucasCompanion.lean` both become instances, and the
  construction is one Mathlib does not have, so it is citable outside this library.

**2.3 Generating functions of linear recurrences** — **DONE**, see
`Combinatorics/RecurrenceGeneratingFunction.lean` and
`NumberTheory/LucasSequenceGeneratingFunction.lean`.  The gap claim below was re-run before the
work started and held.  What landed: `isSolution_iff_coeff_recDenom_mul_mk` (solving a
`LinearRecurrence` ⟺ the product with the reversed characteristic polynomial is a polynomial of
degree `< order`), the two-term specialisation `lucasDenom_mul_mk_of_rec`, and the generating
functions of all seven §1.1 sequences — each one line from the master theorem, no induction.
One tooling finding came with it and is written up in `HANDOFF.md` §1: `ring` does not work in
`R⟦X⟧` without `set_option backward.isDefEq.respectTransparency false`.

`∑ U_n xⁿ = x / (1 - Px + Qx²)`, and the general `LinearRecurrence` version: a sequence
satisfies a linear recurrence iff its generating function is rational with denominator the
reversed characteristic polynomial.

- Mathlib: `PowerSeries` is extensive (19 files), and has `PowerSeries/Catalan.lean` and
  `PowerSeries/Schroder.lean` — two *specific* generating functions. The general theorem was
  **not found**: `grep -rn 'generating function\|generatingFunction' Mathlib --include=*.lean`
  returns only probability moment-generating functions; `LinearRecurrence` appears in exactly
  four files (`Algebra/LinearRecurrence.lean`, `GoldenRatio.lean`, `Chebyshev.lean`,
  `Dickson.lean`) and none of them mentions `PowerSeries`.
- Does real work: gives all seven §1.1 sequences their generating function at once, and is the
  bridge between the library's number-theory half and combinatorics.
- This is the single highest-value Tier 1 item: it is a *method*, not a fact.

### Tier 2 — new subjects, measured gaps, self-contained

**2.4 Enumerative sequences Mathlib lacks** — audited, and the answer was **build none of
them**.  What shipped instead is `Combinatorics/AlgebraicGeneratingFunction.lean`; see round 8
in the archived history.

*The five absence claims were re-run and all five hold.*  Motzkin raw 17 / residual 0, Narayana
12 / 0, Eulerian 54 / 0, Delannoy 0, Stern 4 anchored (15 unanchored) / 0 — identical to the
recorded table.  Two boundary checks the earlier entry had not made: a scan of every constant of
type `ℕ → ℕ` and `ℕ → ℕ → ℕ` in the whole environment (35 and 36 respectively, listed, with
`catalan`, `Nat.bell`, `Nat.largeSchroder`, `Nat.stirlingSecond`, `Nat.fib` recovered as a
positive control, so a sequence of that shape cannot hide) finds none of the five; and a scan of
`ℕ → R[X]` families finds no Eulerian polynomial.  Two corrections to the row text: the Stern
row's "the extra 11 being `registerName…`" is 10 `registerName*` **plus** one
`[poeschel2017siegelsternberg]` citation, and "`Algebra/ContinuedFractions` (measured present,
16 files)" is wrong — that directory holds **12** `.lean` files; 16 was a Mathlib-wide count of
mentions.

*A name hazard, recorded so a future module does not trip on it.*  `Counterexamples/Motzkin.lean`
**does exist** in the vendored tree.  It is `motzkin_polynomial_nonneg`, Motzkin's
nonnegative-but-not-a-sum-of-squares *polynomial* — a different object from the Motzkin
*numbers*.  Any absence claim about Motzkin must say which Motzkin.

*Why none of the five shipped as a module.*  The project's test, stated in `HANDOFF.md`, is "porting
would add names, not results".  Applied honestly:

| candidate | verdict |
|---|---|
| Motzkin as a fact module | **no** — its generating function would be a third hand-rolled copy of a proof Mathlib already carries twice (`Catalan.lean:48`, `Schroder.lean:95`), and the cheapest version cites `catalan` zero times, so it fails even the roadmap's own stated motive of de-isolating `Catalan.lean` |
| Narayana | **no** — its two real-work items are a shifted Vandermonde whose `d = 0` case Mathlib proves in 3 lines (`Data/Nat/Choose/Vandermonde.lean:41`), and an alternative derivation of the 4-line `catalan_pos`. Connections, not work. (`catalan_pos` *is* a real gap — `positivity` fails on it, rc 1 — but a small one.) |
| Eulerian | **defer** — real content *if* defined as a count of permutations by descents rather than by the recurrence, but it absorbs nothing, and the expensive half (the recurrence *from* the count) is unmeasured. The Coxeter route is dead: no `CoxeterSystem` is constructed anywhere in Mathlib (rc 1). |
| Delannoy | **no** — there is no object to count (`inductive … Step` returns 7 hits, the only lattice-path one being `DyckStep`, two constructors), so the recurrence would be the only available definition, which is the banned shape. Its one hook, `shiftedLegendre`, has zero consumers and nothing imports its file, so the bridge would join two leaves. |
| Stern | **fallback only** — two genuinely non-tautological theorems (consecutive coprimality; the bijection onto coprime pairs, which would be Mathlib's first explicit enumeration of `ℚ`), and a draft compiles. But "first consumer of `PowerSeries.expand`" is exercising an API, not doing work. **Unmeasured caveat**: Stern's equation is Mahler-type, `X·S = (1+X+X²)·expand 2 S`, which is *not* the `f = C c + X * q f` shape the new module's uniqueness theorem covers; whether it reaches Stern was **not** tested. |

*What was built instead, and why it is the better item.*  A uniqueness layer for algebraic
generating functions — the shape Catalan, Schröder and Motzkin actually have, and which
`RecurrenceGeneratingFunction.lean` provably cannot reach, since `LinearRecurrence` indexes
coefficients by position in a fixed window and a convolution has no such representation.  It
does work by this project's standard rather than adding names: it re-derives Mathlib's 55-line
Schröder functional equation in 15 lines, deleting both private helpers; and it states
`catalanSeries_unique` and `largeSchroderSeries_unique`, theorems about Mathlib's own constants
that Mathlib cannot state (`grep -rniE 'fixed.?point|contraction|unique.*satisf'` over
`RingTheory/PowerSeries` and `MvPowerSeries` → rc 1, 0 hits).  Motzkin ships **inside** it as an
instance, with a uniqueness statement a standalone Motzkin module would not have had.

*Still open from 2.4, in priority order*: Eulerian **as a count** (the only one of the five with
real content left in it); Stern, if a fact module is wanted, with the Mahler-shape caveat above;
and the genuine extension of the new module — uniqueness for `f = p + X ^ d * q f` — which would
make `isSolution_iff_coeff_recDenom_mul_mk` a corollary and turn the two generating-function
modules into one theory.  That last is **not** attempted and is not promised.

**Dated 2026-09-24 UTC (order G-8, J3; round 26):** the type-level remark above, that a convolution
has no `LinearRecurrence` representation, is now a theorem about the sequence:
`not_isSolution_catalan`, the Catalan numbers satisfy no linear recurrence over any nontrivial
commutative ring, and `not_isSolution_catalan_nat` over `ℕ`, in
`Combinatorics/AlgebraicGeneratingFunction`, which now imports `RecurrenceGeneratingFunction`. A
commutative semiring is not enough (in the saturating `{0, 1}` an order-1 recurrence holds). The
Mathlib citations in this entry have moved at v4.34.0: `Catalan.lean:48` is `:47`,
`Schroder.lean:95` is `:94`, and the Schröder argument is 54 lines, not 55; the module's docstring
carries the correction. The extension to `f = p + X ^ d * q f` is still not attempted.

**2.5 Primitive divisors / Zsigmondy** — **DONE in the shape described below**, see
`NumberTheory/PrimitiveDivisor.lean` and round 9 in the archived history.  Zsigmondy proper is
**deferred**, and the four open items at the end of this entry are what remains.
**(Dated 2026-09-24 UTC: Zsigmondy for `aⁿ − 1` is done, order G-6, round 22; see the dated
paragraph at the end of this entry.)**

**Re-measured 2026-09-07, and the earlier entry was wrong about the size.**  What it said:
"`grep -rn 'Zsigmondy'` → 0 hits, `grep -rni 'primitive divisor'` → 0 hits. Large."  Both
counts still hold — and both are **name** searches, which is the §0 error.  Searching the
mathematics instead shows the machinery is largely already in Mathlib, and the item is not
large in the way the entry claimed.

*The name layer, re-run and unchanged.*  `grep -rni 'Zsigmondy'` → 0, `grep -rni 'primitive
divisor'` → 0, `grep -rni 'primitiveDivisor'` → 0, `grep -rni 'Bilu'` → 0.

*[measured] The analytic bounds a Zsigmondy argument runs on are all in
`RingTheory/Polynomial/Cyclotomic/Eval.lean`*, from
`grep -n '^theorem ' Mathlib/RingTheory/Polynomial/Cyclotomic/Eval.lean`:

| lemma | line | statement |
|---|---|---|
| `sub_one_pow_totient_lt_cyclotomic_eval` | 174 | `(q-1)^φ(n) < Φₙ(q)`, for `2 ≤ n`, `1 < q` |
| `cyclotomic_eval_lt_add_one_pow_totient` | 230 | `Φₙ(q) < (q+1)^φ(n)`, for `3 ≤ n` |
| `sub_one_lt_natAbs_cyclotomic_eval` | 311 | `q - 1 < |Φₙ(q)|` over `ℤ`, for `1 < n`, `q ≠ 1` |

Their consumers, from
`grep -rln 'sub_one_pow_totient_lt_cyclotomic_eval\|cyclotomic_eval_lt_add_one_pow_totient\|sub_one_lt_natAbs_cyclotomic_eval' Mathlib --include=*.lean`:
`NumberTheory/PrimesCongruentOne.lean`, `RingTheory/LittleWedderburn.lean`, and `Eval.lean`.

*[measured] The order bridge exists too.*  `isRoot_cyclotomic_iff`
(`Cyclotomic/Roots.lean`) says `IsRoot (cyclotomic n R) μ ↔ IsPrimitiveRoot μ n` under
`[NeZero (n : R)]`; `orderOf_root_cyclotomic_dvd` (`Cyclotomic/Basic.lean:587`) gives the
`∣` half with no `NeZero`; `coprime_of_root_cyclotomic` sits just above it.

*[measured] And the whole argument is already written, inline, for another purpose.*
`Nat.exists_prime_gt_modEq_one` (`NumberTheory/PrimesCongruentOne.lean`, lines 29–60) proves
there are arbitrarily large primes `p ≡ 1 mod k` by taking `p = minFac |Φ_k(b)|` at
`b = k · n!`.  Its line 57 is

```lean
have : k = orderOf (b : ZMod p) := (isRoot_cyclotomic_iff.mp hroot).eq_orderOf
```

and `ord_p(b) = k` **is** "`p` is a primitive prime divisor of `b^k - 1`".  The choice
`b = k · n!` exists precisely to force `p ∤ k`, which is the `NeZero` side condition and, in
Zsigmondy language, the avoidance of the exceptional case `p ∣ n`.  This is the Dickson shape
and the `Matrix.sum_mulVec` shape a third time: the mathematics is present, stated for a
different purpose, and the reusable statement was never named.

*[measured] The bridge extracts in one line.*  `lake env lean` rc 0 on:

```lean
example {n p : ℕ} [Fact p.Prime] (a : ℕ)
    (hroot : IsRoot (cyclotomic n (ZMod p)) (Nat.castRingHom (ZMod p) a))
    [NeZero (n : ZMod p)] :
    orderOf ((a : ZMod p)) = n :=
  ((isRoot_cyclotomic_iff.mp hroot).eq_orderOf).symm
```

An added `hn : 0 < n` was flagged **unused** by the linter — positivity already follows from
`NeZero (n : ZMod p)`.  So this must not be shipped as though it were the content.

**What is therefore actually open**, and it is smaller and differently shaped than "large":

1. *The divisibility phrasing.*  Mathlib states this in the language of cyclotomic roots, never
   in the language of divisibility.  There is no statement of the form
   `∃ p, p.Prime ∧ p ∣ a^n - 1 ∧ ∀ m, 0 < m → m < n → ¬ p ∣ a^m - 1`.  That translation is the
   gap, and it is about `∣`, not about polynomials.
2. *Existence*, following the `PrimesCongruentOne` / `LittleWedderburn` pattern with the eval
   bounds.
3. *The exceptional cases* — `n = 1`; `n = 2` with `a + 1` a power of `2`; `n = 6`, `a = 2`.
   This is the real work, and none of it is in Mathlib.
4. *The `a^n - b^n` and Lucas-sequence generalisations*, which is where 2.1 feeds in.

**A caveat this re-measurement also puts on 2.1.**  2.1 claims its payoff is that
`MersenneOrder.lean` becomes an instance.  Read that proof
(`sed -n '61,64p' ClassicalLean/NumberTheory/MersenneOrder.lean`):

```lean
theorem dvd_mersenne_iff_orderOf_dvd {p m : ℕ} (hp : p.Prime) :
    p ∣ 2 ^ m - 1 ↔ orderOf (2 : ZMod p) ∣ m := by
  rw [dvd_mersenne_iff_pow_eq_one hp, orderOf_dvd_iff_pow_eq_one]
```

Two rewrites, through `(2 : ZMod p) ^ m = 1`, touching no Lucas sequence and no companion
matrix.  `2^m - 1` is *geometric*, so the rank of apparition degenerates to the multiplicative
order, which Mathlib handles directly; deriving this from a general `α(p)` theorem would be
**longer**, not shorter.  *[inferred, no Lean written]* the general theorem does not usefully
subsume it, and 2.1's real-work test should instead be a divisibility statement for
`pellNumber` or `jacobsthal` — reachable here through `LucasSequenceCases`, and absent from
Mathlib entirely.

**Cross-item pattern.**  2.1 and 2.5 both run through `orderOf` in `ZMod p`, and Mersenne is
the shared instance: `dvd_mersenne_iff_orderOf_dvd` is about `ord_p(2)`; a primitive divisor of
`2^n - 1` is a prime with `ord_p(2) = n`; and 2.1's `α(p)` at `(P,Q) = (3,2)` is that same
`ord_p(2)`, because `lucasU_three_two` identifies `U(3,2)` with `mersenne`.  Three names for
one object at one parameter.  *[inferred from the three statements; no Lean written.]*

**Dated 2026-09-23 (order G-5 Close, re-measured at v4.34.0 by this session; the prior-art
facts were found by its read-only researcher on the web and are attributed, not re-fetched).**
`grep -rni '<term>' Mathlib --include=*.lean` for `Zsigmondy`, `primitive divisor`, `Bilu`:
0 / 0 each, as at the pin; `docs/1000.yaml` Q8074796 still reads `# TODO: Find the code`.
**The code is found**, and none of it is in Mathlib: (1) Mantas Bakšys's Lean 3 proof, 2022,
branch `zsigmondy` of `leanprover-community/mathlib3` at `48ba6fa` ("finally proved!",
2022-12-20; no pull request; Apache-2.0), `theorem zsigmondy` for `a > b > 0` coprime integers,
`n ≥ 3`, `(a, b, n) ≠ (2, 1, 6)`, with `n = 2` separate and `n = 1` not stated; (2) a Lean 4 port,
mathlib4 pull request #28895 (Yury Kudryashov, Harmonic, opened 2025-08-25), stating the
existence in `ModEq`/`orderOf` form for `aⁿ − bⁿ` and `aⁿ + bⁿ` — **closed unmerged by its
author on 2026-09-18**, and no commit containing the file ever built green; its eight
prerequisite pull requests did merge (e.g. `Polynomial.homogenize`, in v4.34.0). Neither
states that the exceptions have no primitive divisor. **The blocker named in
`PrimitiveDivisor.lean` is stronger than a proof needs:** both prior-art proofs need
`Φₙ(a) > P(n)`, `P(n)` the largest prime factor of `n`, and for `b = 1`, `a ≥ 3` Mathlib's
`(a − 1)^φ(n)` bound already gives it; only `a = 2` needs a new inequality (the researcher's
exact sweep over `a = 2..30`, `n = 2..60` found `(2, 6)` the only failure of either bound). The
Cyclotomic/Eval line numbers in the table above moved at v4.34.0 (171, 223, 304), and the
table omits `sub_one_pow_totient_lt_natAbs_cyclotomic_eval` (`:293`). **Next, ranked first
(`HANDOFF.md` §3):** Zsigmondy for `aⁿ − 1` as an `iff` with the exact exceptional set, stated
with `IsPrimitiveDivisor`, proved here and citing the two sources as prior art.

**Dated 2026-09-24 UTC (order G-6, round 22): done.** `NumberTheory/Zsigmondy` proves
`exists_isPrimitiveDivisor_iff`: for `2 ≤ a` and every `n`, `aⁿ − 1` has a primitive divisor
exactly outside `(2, 1)`, `(2, 6)` and `n = 2` with `a + 1` a power of `2`, within the kernel
trio. The route: a prime dividing both `n` and `Φₙ(a)` is `P(n)` and, for `n ≥ 3`, divides
`Φₙ(a)` once (by a geometric sum, no Lifting the Exponent); so `|Φₙ(a)| > P(n)` gives a primitive
divisor. For `a ≥ 3` that bound is Mathlib's `(a − 1)^φ(n)`. For `a = 2` the "new inequality"
above was not needed: the expansion identities at `P(n)` and Mathlib's two existing bounds
(`sub_one_pow_totient_lt_cyclotomic_eval`, `cyclotomic_eval_lt_add_one_pow_totient`) give
`Φₙ(2) > P(n)` for `n > 1`, `n ≠ 6`, in four cases — the classical route, which both prior-art
sources also use; both were fetched for citation after the proofs were written, and nothing is
adapted. Still open, and not in this order: the two-variable form `aⁿ − bⁿ` for coprime
`a > b > 0`, which both prior-art proofs state.

**Dated 2026-09-24 UTC (order G-8, round 25): the two-variable form is done, with the sum clause.**
`NumberTheory/ZsigmondyPowSubPow` proves `exists_isPrimitiveDivisor₂_iff`: for coprime `0 < b < a`
and every `n`, `aⁿ − bⁿ` has a primitive prime divisor (`IsPrimitiveDivisor₂`, defined in
`NumberTheory/Zsigmondy`) exactly unless `n = 1` and `a = b + 1`, `n = 2` and `a + b` is a power of
`2`, or `(a, b, n) = (2, 1, 6)`; and `exists_primitive_prime_dvd_pow_add_pow_iff`: for coprime
positive `a ≠ b` and every `n`, some prime divides `aⁿ + bⁿ` and no `aᵐ + bᵐ` with `0 < m < n`,
exactly unless `n = 3` and `{a, b} = {1, 2}`. Together they are the statement of `docs/1000.yaml`'s
Q8074796 in full, within the kernel trio; listing it there needs a public URL and is Dustin's
decision. The route is round 22's, which is the prior art's, through the homogenised value
`Φₙ(a, b)`, written directly as a sum of coefficients (no `Polynomial.homogenize`); the sources of
each piece are in the module docstring and round 25. Item 4 of "What is therefore actually open"
above is done for `aⁿ − bⁿ` (the Lucas reading is §2.1's dated paragraph of order G-8); the
primitive-divisor theorem for general Lucas sequences is not.

### Tier 3 — areas the library has none of

**2.6 Order and lattice theory.** `Order/` has two isolated modules. `Order/Tolerance.lean`
explicitly does *not* assume the triangle inequality; adding it and deriving the equivalence
relation is the step the module's own header names. Smallest genuine addition in the library.

**2.7 Analysis, topology, category theory, probability, graph theory.** *Not researched this
pass.* The library has nothing in any of them and there is no reason for that except history.
No Mathlib gap is claimed here because none was measured — anyone starting one of these should
run the searches first and add the rows.

**2.8 Finite information theory** — **started, round 18 (order 0923, J4)**: see
`InformationTheory/Entropy.lean`, `InformationTheory/MutualInformation.lean` and
`InformationTheory/Channel.lean`.  The first area in this library with no number theory in it
(§3 item 3).

*What shipped.*  `shannonEntropy` (moved from `Simplex/FisherRao.lean`, same full name) and
`relEntropy`; Gibbs' inequality in unnormalised form (`sum_sub_sum_le_relEntropy`) and on
probability vectors with its equality case, zero coordinates included; the log-sum inequality;
`H ≤ log (card ι)` with equality exactly at the uniform vector; `relEntropy p (softmax x) =
crossEntropy x p - shannonEntropy p` for every `p` with `∑ p = 1`; `mutualInfo`, its
nonnegativity, its vanishing exactly at independence, `I = H(X) + H(Y) - H(X, Y)` and
subadditivity; the data-processing inequality for a finite channel; entropy nondecreasing under
a doubly stochastic matrix.  Every statement carries explicit hypotheses (`0 ≤ p i`, `∑ p = 1`,
support), not `stdSimplex`, which Mathlib deprecates at v4.34.0.

*Mathlib status — measured 2026-09-23*, `grep -rniE '<pattern>' <tree> --include=*.lean`, lines /
files, over this library (before the three modules existed), Mathlib at the pin `8f07524533`, and
Mathlib v4.34.0 (the toolchain-bump worktree):

| pattern | library | pin | v4.34.0 |
|---|---|---|---|
| `entropy` | 111 / 6 | 510 / 7 | 512 / 8 |
| `negMulLog` | 1 / 1 | 45 / 5 | 51 / 6 |
| `klFun` | 0 / 0 | 103 / 2 | 127 / 4 |
| `klDiv` | 1 / 1 | 56 / 1 | 132 / 3 |
| `mutualInfo` | 0 / 0 | 0 / 0 | 0 / 0 |
| `condEntropy` | 0 / 0 | 0 / 0 | 0 / 0 |
| `log_sum` | 1 / 1 | 6 / 1 | 6 / 1 |
| `logSum` | 92 / 5 | 0 / 0 | 0 / 0 |
| `stochastic` | 0 / 0 | 269 / 21 | 307 / 29 |
| `log \([^()]+ / [^()]+\)` (the statement shape) | 21 / 4 | 27 / 15 | 53 / 18 |
| `crossentropy\|cross_entropy` (round 10's search, re-run) | 41 / 3 | 0 / 0 | 0 / 0 |
| `relEntropy\|relativeEntropy\|relative_entropy` | 0 / 0 | 0 / 0 | 0 / 0 |
| `dataProcessing\|data_processing\|comp_right_le` | 0 / 0 | 0 / 0 | 2 / 1 |

Read beside the counts: the `entropy` files are topological entropy (`Dynamics/`), `negMulLog`
and `BinaryEntropy`; the new v4.34.0 files under `entropy` and `negMulLog` are
`Dynamics/SymbolicDynamics/Basic.lean` and `Analysis/SpecialFunctions/Log/Monotone.lean`; the
`log_sum` hits are `posLog_sum`; and a search for the *shape* of a finite entropy sum,
`grep -rnE '∑ [^,]+, [^*]+\* (Real\.)?log'` (14 lines at the pin, 23 at v4.34.0), finds Liouville,
Jensen's formula, von Mangoldt and value distribution — **no Shannon or relative entropy of a
general finite vector in either Mathlib**, only the two-point and `q`-ary cases `Real.binEntropy`
and `Real.qaryEntropy` (`Analysis/SpecialFunctions/BinaryEntropy.lean`).  What Mathlib does have is the measure-theoretic theory over `Measure α`, valued
in `ℝ≥0∞`: `InformationTheory.klDiv`, `integral_llr_add_sub_measure_univ_nonneg`,
`mul_log_le_toReal_klDiv` (log-sum), `klDiv_eq_zero_iff`, `klFun_nonneg`, and — at v4.34.0 only,
absent at the pin — the data-processing inequality `klDiv_comp_right_le` and `klDiv_map_le`
(`InformationTheory/KullbackLeibler/DataProcessing.lean`) and a chain rule
(`KullbackLeibler/ChainRule.lean`).  `Real.concaveOn_negMulLog` is there; no summed entropy bound
is.  `Matrix.rowStochastic` is square with `[DecidableEq n]`; `doublyStochastic` is root-namespace.

**Dated 2026-09-23 (order G-5, round 19) — a completion of the paragraph above, not a
reversal.**  Mathlib v4.34.0's `InformationTheory/` has **nine** files: `Coding/{Kraft,
KraftMcMillan, PrefixFree, UniquelyDecodable}`, `Hamming`, `KullbackLeibler/{Basic, ChainRule,
DataProcessing, KLFun}`; at the pin it had five (`Coding/KraftMcMillan`, `Coding/UniquelyDecodable`,
`Hamming`, `KullbackLeibler/Basic`, `KullbackLeibler/KLFun`) — `find InformationTheory -name
'*.lean' | sort` in each tree's `Mathlib/`.  The chain rule is `klDiv_compProd_eq_add`
(`ChainRule.lean:204`), a chain rule for the KL divergence of composition-products, **not** for
entropy.  `DataProcessing.lean` holds three data-processing inequalities, `klDiv_map_le` (:160,
measurable maps), `klDiv_trim_le` (:180, sub-σ-algebras) and `klDiv_comp_right_le` (:186, Markov
kernels).  `Coding/` holds the Kraft–McMillan inequality for uniquely decodable codes
(`IsUniquelyDecodable.finsetSum_one_div_card_pow_length_le_one`, `KraftMcMillan.lean:145`,
present at the pin too) and Kraft's inequality for prefix-free codes, finite and `tsum` forms
(`Kraft.lean:43`, `:71`).  None of it is a finite-vector entropy, so the conclusion above stands.

*Why the finite forms were built anyway.*  They are real-valued `Finset` sums on the same vectors
the simplex layer uses (`softmax`, `crossEntropy`, `FisherRao`), and this library has twice
declined to route a finite statement through a measure (`Simplex/LogSumExp.lean`, round 10).  The
bridge that would make the finite data-processing inequality a corollary of Mathlib's is
`(klDiv μ_p μ_q).toReal = relEntropy p q + ∑ i, q i - ∑ i, p i` under the support hypothesis —
Mathlib's `klDiv` carries the mass term `ν.real univ - μ.real univ`; it is **not** built, and is
listed in `HANDOFF.md` §3.

*Prior art outside Mathlib.*  `github.com/FujiHaruka/information-theory` (Apache-2.0, Lean
v4.31.0, pushed 2026-09-14; README read 2026-09-23, not verified) claims 4,108 theorems in
random-variable and measure form, including `entropy_le_log_card`, `mutualInfo` as the KL
divergence of the joint law from the product of the marginals, a data-processing inequality
`mutualInfo_le_of_postprocess`, Pinsker, Fano and channel coding.  Not added as a dependency.
**Dated 2026-09-23 (order G-5, round 19) — measured by claude-ai in a clone, not by the
executing session, which did not clone it.**  At `7e97b77` (2026-09-14): Apache-2.0; Lean and
Mathlib v4.31.0; 418 modules (`find InformationTheory -name '*.lean' | wc -l`); 4,055
`theorem`/`lemma` declarations (`grep -rhE '^\s*((private|protected) )?(theorem|lemma)\s'
--include=*.lean InformationTheory | wc -l`; claude-ai notes this misses `@[attr] theorem` lines,
and the README's 4,108 above is kept as the README's claim); 0 `axiom` declarations (`grep -rhE
'^\s*((private|protected|noncomputable) )*axiom\s' --include=*.lean . | wc -l`); 27 `sorry`
tokens, all in prose (`grep -rhow sorry --include=*.lean InformationTheory InformationTheory.lean |
wc -l`).  Random-variable form, `entropy μ Xs` (`Shannon/Bridge.lean:40`).  It has
`condEntropy`, `mutualInfo_chain_rule` (`Shannon/CondMutualInfo.lean:224`),
`condEntropy_pi_chain_rule`, the Markov data-processing inequality `mutualInfo_le_of_markov`
(`Shannon/CondMutualInfo.lean:366`; the README's `mutualInfo_le_of_postprocess`, linked to
`Shannon/DPI.lean`, is a different theorem), Pinsker (`tvNorm_le_sqrt_klDiv`), Fano, Kraft and
Huffman optimality.

*Subsumed here, recorded rather than removed* (those modules were read-only under order 0923):
`Gibbs.sum_mul_log_div_nonneg`, `Gibbs.sum_mul_log_div_pos_of_ne` and
`Gibbs.neg_log_card_le_sum_mul_log` are the open-simplex cases of `relEntropy_nonneg`,
`relEntropy_eq_zero_iff` and `shannonEntropy_le_log_card`; `crossEntropy_sub_entropy` is the
open-simplex case of `relEntropy_softmax`.

*Open, in order.*  The `klDiv` bridge above; conditional entropy and the chain rule
`H(X, Y) = H(X) + H(Y | X)`; data processing for mutual information along a Markov chain, which
would give `mutualInfo` its first user outside its own module (it has none today, and round 18's
fragment says why); Pinsker's inequality.

**Dated 2026-09-23 (order G-5, round 19) — declined for now.**  Information theory part 2 —
conditional entropy, the chain rule, Markov data processing, Pinsker and Fano — is not next, on
the prior-art ground Dustin asked claude-ai to apply on 2026-09-23 (claude-ai's decision on his
delegation; **his veto is open**).  All five exist, in random-variable form, in the Apache-2.0
library above, which this one does not depend on.  The finite-vector forms would still be new
here, so this is a **ranking** decision, not a finding that they add nothing.  The three finite
modules stay as they are.  `mutualInfo` keeps no consumer outside its module; round 19 says why.
The `klDiv` bridge stays listed as the first step if the finite layer is ever offered to
Mathlib.

**2.9 Statistics: the Gauss–Markov theorem** — **started, round 20 (order G-5, J3)**: see
`Statistics/GaussMarkov.lean`.  The second area in this library with no number theory in it,
after §2.8 (§3 item 3).

*What shipped.*  The least-squares matrix `leastSquares X = (Xᵀ X)⁻¹ Xᵀ` over `ℝ`, for any finite
index types.  Unbiasedness of a linear estimator `C` as `C * X = 1`, and its equivalence with
recovering every parameter from noiseless data; an unbiased linear estimator exists exactly when
`Xᵀ X` is invertible; least squares is unbiased then, its variance factor is `(Xᵀ X)⁻¹` (always,
the junk case included), it satisfies the normal equations, and it minimises the sum of squared
residuals.  **The Gauss–Markov theorem** in matrix form: for unbiased `C`,
`C Cᵀ - (Xᵀ X)⁻¹ = D Dᵀ` with `D = C - leastSquares X`, so it is positive semidefinite, with
equality exactly at least squares; the variance reading `a ⬝ᵥ ((Xᵀ X)⁻¹ *ᵥ a) ≤
a ⬝ᵥ ((C Cᵀ) *ᵥ a)`; and the Loewner form `(Xᵀ X)⁻¹ ≤ C Cᵀ` under `open scoped MatrixOrder`.
The hypotheses of the normal equations, of the least-squares theorem and of the variance reading
(and so of the Gauss–Markov theorem) cannot be dropped: each has a counterexample to the
statement without it.  Not shown necessary that way: `leastSquares_mul_self`'s (at `X = 0`,
`0 * 0 ≠ 1`), the decomposition's and the equality case's (at `X = !![1; 1]` with `C = 0`, and
with `C = !![-1/2, -1/2]`, which gives `C Cᵀ = (Xᵀ X)⁻¹` with `C ≠ leastSquares X`) — the
post-proof reviewer's witnesses, computed by hand, not stated in Lean.  A worked example (two
observations of one mean) shows the sample mean is least squares and the inequality strict.  All of it matrix algebra; no probability measure.

**Dated 2026-09-25 UTC (order G-10, J3, round 30):** `leastSquares` now underlies a full theorem
downstream — the **Frisch–Waugh–Lovell theorem** (`Statistics/FrischWaughLovell.lean`, §2.15), whose
residual maker `M₁ = 1 − X₁ · leastSquares X₁` and whose main identities are proved over it; so
`GaussMarkov` is `usedBy=2` (`CramerRao` and `FrischWaughLovell`). Cochran's theorem, the other half
of `HANDOFF.md` §3's third item, is not in order G-10.

*Mathlib status — measured 2026-09-23 at v4.34.0*, lines / files, over Mathlib and over this
library before the module existed:

| search | Mathlib v4.34.0 | library |
|---|---|---|
| `grep -rniE 'gauss.?markov\|best linear unbiased\|unbiased\|least.?squares\|leastSquares\|regression'` | 26 / 5 | 0 / 0 |
| `grep -rniE 'pseudo.?inverse\|moore.?penrose'` | 3 / 2 | 0 / 0 |
| `grep -rnE 'PosSemidef.*⁻¹'` | 3 / 1 | 0 / 0 |
| `grep -rnE '\(([A-Za-z]+)(ᴴ\|ᵀ) \* \1\)⁻¹\|\(([A-Za-z]+) \* \3(ᴴ\|ᵀ)\)⁻¹'` (the `(Xᵀ X)⁻¹` shape) | 0 / 0 | — |

Read beside the counts: all 26 hits of the first search are the word "regression" — the
`linter.tacticAnalysis.regressions.*` options (16 lines), the `linter.nightlyRegressionSet`
linter set (4 lines in `Init.lean`), four `*Regressions` definitions (three `…ToGrindRegressions`
and `omegaToLiaRegressions`) and two comments about performance regressions (`GroupTheory/OreLocalization/Basic.lean:41`,
`Topology/Algebra/Algebra.lean:109`); none is statistics.  The pseudoinverse hits are
`LinearAlgebra/Matrix/NonsingularInverse.lean:22` ("pseudoinverses which we do not consider
here") and two lines of class-design prose in `Algebra/Group/DivInvMonoid.lean`.  The
`PosSemidef.*⁻¹` hits are `PosSemidef.inv` and the two Schur-complement lemmas
`Matrix.PosDef.fromBlocks₁₁` and `Matrix.PosDef.fromBlocks₂₂` (`LinearAlgebra/Matrix/PosDef.lean`
lines 615 and 634; Mathlib's own docstring at line 34 calls the second `PosSemidef.fromBlocks₂₂`).
Mathlib's `docs/1000.yaml` entry Q428134 is the title "Gauss–Markov theorem" with no `decl`, so
no formalisation is recorded.  What Mathlib does have, and the module uses:
`Matrix.PosSemidef` (quantified over `n →₀ R`; the vector form is
`posSemidef_iff_dotProduct_mulVec`), `posSemidef_self_mul_conjTranspose`,
`Matrix.PosDef.conjTranspose_mul_self` (from injectivity of `X.mulVec`), the Loewner order
scoped to `MatrixOrder` in `Analysis/Matrix/Order.lean`, and least-squares minimisation in
geometric form (`Submodule.starProjection_minimal`).  Prior art outside Mathlib: claude-ai found
no Gauss–Markov theorem and nothing named least squares in the Apache-2.0 library of §2.8
(order G-5 §0 row 9, not re-measured here).

*Import closure* (`~/work/_bump-evidence/import_closure.py`): `Mathlib.Analysis.Matrix.Order`
adds 73 Mathlib modules, closure 3895 → 3969; `Mathlib.Probability.Kernel.Invariance`, the
module missing from Mathlib's v4.34.0 cache, is still not reached.  Controls:
`Mathlib.Analysis.Matrix.Order` and `Mathlib.Algebra.Order.Star.Real` were unreachable before
the module and are reachable after it, through it.

*Open, in order.*  Generalised least squares (`Cov ε = σ² • V`, `V` positive definite); Cochran's
theorem (`docs/1000.yaml` Q599876); the variance reading restated with
`ProbabilityTheory.covarianceBilin` (order G-5's optional second module, not started — it adds
126 modules and does not reach `Invariance`, by the order's reviewer's count, reproduced read-only
by this session's research reader); least squares for
a rank-deficient design, which needs a pseudoinverse Mathlib does not have.

**Dated 2026-09-23 (order G-5 Close), re-measured by this session at v4.34.0**, lines / files
over Mathlib: `aitken` 0 / 0; `generali[sz]ed least` 0 / 0; `cochran` 0 / 0;
`chi.?squared|chiSquared` 0 / 0; `covarianceBilin` 133 / 6 (all `grep -rniE`, `-rnE` for the
last, `--include=*.lean`); `docs/1000.yaml` Q599876 "Cochran's theorem" has no `decl`.  The
read-only researcher's reading of the ingredients: **generalised least squares is closest** —
every lemma it needs is in Mathlib and the proof follows `GaussMarkov.lean` step for step
(`glsMatrix X V = (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹`, `glsMatrix X 1 = leastSquares X` — `leastSquares`'s first
outside consumer — and Aitken's theorem `C V Cᵀ - (Xᵀ V⁻¹ X)⁻¹ = D V Dᵀ`); **Cochran's theorem
in matrix form** (`∑ A i = 1`: complete orthogonal idempotents iff the ranks add up to `card n`;
Mathlib has no statement about idempotent matrices under the ordinary product) is next; **the
distributional Cochran** needs a chi-squared law Mathlib does not have, an order of its own.

**2.10 Max-flow min-cut, and Menger's theorem** — *not started; ranked second (`HANDOFF.md`
§3).*  Combinatorics and computing, an area the library has none of (§2.7 left graph theory
unresearched).  `docs/1000.yaml` Q608294 "Max flow min cut theorem" and Q928813 "Menger's
theorem": titles only, no formalisation recorded.  *Mathlib status — measured 2026-09-23 at
v4.34.0 by this session*, `grep -rniE '<pattern>' Mathlib --include=*.lean`, lines / files:
`menger` 0 / 0; `max.?flow|min.?cut` 0 / 0; `flow network` 0 / 0;
`edgeConnect|IsEdgeConnected|IsEdgeReachable` 72 / 3;
`Nodup.*ReflTransGen|ReflTransGen.*Nodup|Nodup.*TransGen|[Cc]hain.*[Nn]odup` (`-rnE`) 0 / 0.  The
library: 0 for each.  What Mathlib has (the researcher's reading, file:line in its report):
the cut side of edge-Menger for `SimpleGraph` — `IsEdgeReachable` (`Connectivity/
EdgeConnectivity.lean:33`: every edge set of size below `k` leaves `u` and `v` reachable),
`isEdgeReachable_add_one`, the bridge characterisation — and path shortening
(`Walk.bypass`, `Walk.toPath`) for `SimpleGraph` only; nothing for a relation, a `Quiver` or a
`Digraph`, and no LP duality (`Analysis/Convex/Cone/Basic.lean` lists it as a TODO).  *First
order-sized piece:* a finite network with integer capacities, weak duality (flow value ≤ any
cut's capacity), and max-flow = min-cut with an integral maximum flow; then edge-Menger stated
against Mathlib's own `IsEdgeReachable`.  *What makes it hard:* the augmentation step needs a
duplicate-free residual path, which needs "a `ReflTransGen` witness on a finite type shortens to
at most `card α` steps" — absent from Mathlib, and shared with §2.11.  Prior art outside
Mathlib not searched (Isabelle's AFP has flow networks and Menger, by the researcher's
unverified recollection).

**2.11 Decidable acyclicity of a finite relation, and an append-only chain** — *not started;
ranked fourth, and best folded into §2.10 as its precursor.*  From Tier 3 of
`~/Cowork/lean-rebuild/20260907T231327Z__claude-ai__foundation-ranked-build-order.md`
("`Applied/Integrity.lean`": appending cannot alter a committed root, and the fact store's
second axis as a DAG with decidable acyclicity).  *Measured 2026-09-23 at v4.34.0 by this
session*, `grep -rnE`/`-rniE`, Mathlib: `TransGen.*[Dd]ecidable|[Dd]ecidable.*TransGen` 0 / 0;
`merkle` 0 / 0; `append.?only` 0 / 0.  The researcher's reading: the append-only half is
`List.foldl_append` and is thin; the acyclicity half is mostly glue over
`Finite.wellFounded_of_trans_of_irrefl` (which a search by `Fintype`/`Finite` beside
`WellFounded` misses, because the lemma's line names neither — §0's name-search trap again),
and its one real lemma is the path-shortening lemma §2.10 needs, giving
`DecidableRel (TransGen r)`.  Binding it to the actual fact store would mean modelling what the
store hashes, which lives on DSMain and is outside this library's orders.

**2.12 Statements on Mathlib's own wanted list** — *not started; ranked fifth.*  Mathlib v4.34.0
keeps them as `proof_wanted` in a separate `Wanted/` library: `grep -rnE '^\s*proof_wanted\s'
Wanted --include=*.lean` gives 34 / 18 (this session).  Within reach, per the researcher:
`Order.height_of_linearOrder` and `Order.coheight_of_linearOrder` (`Wanted/Order/
KrullDimension.lean:19`, `:22`; the `encard` API they waited for now exists; 0 new imports) and
`ProbabilityTheory.variance_of_hasLaw_binomial` (+115 modules, no `Invariance`; a route through
`bernsteinPolynomial.variance`).  `grep -rnE` for those three names over `Mathlib`: 0 / 0 (this
session).  Findings to check before anything is offered (offering is Dustin's decision):
`condVar_of_hasLaw_binomial` (`Wanted/Probability/Distributions/Binomial.lean:27`) reads as false
as stated — at `m = ⊥` its two sides are `np(1-p)` and `np(1-np)`, which differ for `n ≥ 2`,
`p > 0` (the researcher's reduction and exact check, not Lean); two semisimple-module wanted
statements look false without `[RingHomSurjective σ]` (paper counterexamples only); and
`Probability/Distributions/Binomial.lean`'s module docstring says it computes the variance, but
it computes only the expectation.

**2.13 Lamé's theorem: the number of steps of the Euclidean algorithm** — **DONE**, see
`NumberTheory/EuclidSteps.lean` (round 27, order G-9)

`euclidSteps a b` counts the division steps of the Euclidean algorithm on `(a, b)`. Proved: if it
takes `n` steps, then `F (n + 1) ≤ b` for `b ≠ 0` and `F (n + 2) ≤ a` for `b < a`; consecutive
Fibonacci and Lucas numbers take exactly `n + 1` steps; `10 ^ k < F (5 k + 2)` for `k ≠ 0`; and
Lamé's theorem, at most five steps per decimal digit of the second argument `b` (for `b ≤ a` the
classical form with the smaller entry). The constant is attained for one, two and three digits, by
`(13, 8)`, `(144, 89)` and `(1597, 987)` (the attaining pairs at `n = 4, 9, 14`), and not for four,
where the largest count is 19 (`(10946, 6765)`). Searched at v4.34.0 (order G-9 J1): `lamé` 0;
Euclid with step/iteration/count 0; `gcd` with steps/fuel/iterations 4, all docstrings. Related
prior art, weaker: Mathlib's continued-fraction bound `GenContFract.succ_nth_fib_le_of_nth_den`, one
Fibonacci index below the first bound here, with no step count. `docs/1000.yaml` lists Q230848 by
title only; listing the library's proof there is Dustin's decision.

**2.14 Wolstenholme's theorem** — **DONE**, see `NumberTheory/Wolstenholme.lean` (round 29,
order G-10)

For every prime `p ≥ 5`: the binomial form `C(2p − 1, p − 1) ≡ 1 (mod p³)`
(`choose_two_mul_sub_one_modEq_one`) and the harmonic form `p² ∣` the numerator of `H_{p−1}`
(`two_le_padicValRat_harmonic`, via `padicValRat`); the central form `C(2p, p) ≡ 2 (mod p³)` and the
same for `Nat.centralBinom`; the Catalan corollary `catalan p ≡ 2 + 2 p² − 2 p (mod p³)`; and two
half-sum identities in `ZMod p`. Route: the `j ↔ p − j` pairing in `ZMod (p³)` with `(p − 1)!` a
unit and `p⁴ = 0` collapsing the product, then a mod-`p` reduction via `ZMod.castHom`. Searched at
v4.34.0 (order G-10 §0 row 12): **0** binomial congruences modulo a prime power, and Mathlib's
`NumberTheory/Harmonic/` has the rational `harmonic` but no congruence modulo a prime — the
congruence is new and starts from Mathlib's `harmonic`. The hypothesis `p ≥ 5` is necessary: `p = 2`
and `p = 3` fail every form (order §0 row 7's cells). This is the library's first congruence modulo
a prime power, and it gives the island `Catalan` its first user (`succ_mul_catalan_eq_choose`).
`docs/1000.yaml` lists Q1724049 by title only; listing the proof there is Dustin's decision.

**2.15 The Frisch–Waugh–Lovell theorem** — **DONE**, see `Statistics/FrischWaughLovell.lean`
(round 30, order G-10)

Over round 20's `leastSquares` (`Statistics/GaussMarkov`, now `usedBy=2`). The residual maker
`residualMaker X₁ = 1 − X₁ · leastSquares X₁` (the annihilator `M₁`); `M₁` is symmetric and
idempotent with no hypothesis; `M₁ X₁ = 0`; the Gram matrices of `X₁` and of `M₁ X₂` are units when
that of `[X₁ X₂]` is. The theorem, for `X = [X₁ X₂]` with invertible Gram: the `X₂`-coefficients of
the regression of `y` on `X` equal those of the regression of `M₁ y` on `M₁ X₂`
(`leastSquares_fromCols_mulVec_inr`, and the matrix form `toRows₂_leastSquares_fromCols`); the
residuals agree; and a `Fin 2` witness that the invertibility hypothesis cannot be dropped. Route:
split the block normal equations, the `inr` block gives `(M₁X₂)ᵀ(M₁X₂) β₂ = (M₁X₂)ᵀ(M₁y)` whose Gram
is a unit by the Schur complement (`det_fromBlocks₁₁`), cancel. Searched (order G-10 §0 row 12):
**0** — no residual-maker or annihilator matrix, no `leastSquares`, no partial-regression statement
in Mathlib; the block-matrix and Schur-complement lemmas the route needs are present. A remark, not
proved here (§0 row 9, [inferred]): the theorem plausibly holds under the weaker
`IsUnit (X₁ᵀ X₁).det` alone, left for a later order. Cochran's theorem, the second half of
`HANDOFF.md` §3's third item, is not in this order. `docs/1000.yaml` lists Q1059151 by title only.

---

## 3. What would make the library *work*, as distinct from grow

Three things, in order of how much they change the character of the thing:

1. **A method module, not a fact module.** ~~2.3 is the candidate~~ — **done**.
   `Combinatorics/RecurrenceGeneratingFunction.lean` and
   `NumberTheory/LucasSequenceGeneratingFunction.lean` landed, and the test of "method" was met:
   the seven §1.1 sequences got their generating functions with **no induction anywhere**, from
   the `_add_two` lemma each module already shipped. The library now has three method modules
   (`FactorialPart.lean`, `LucasSequence.lean` and the pair above).
2. **A second unification, to test whether §1.1 was luck.** ~~2.2 is the test~~ — **done, and
   it passed.** `Algebra/CompanionMatrix.lean` absorbed `LucasCompanion.lean` outright and
   `NacciTrace.lean` completely, the latter via a family-specific computation of Newton's
   `k ≤ d` regime. The pattern in §1.1 was a method, not a coincidence about one family. The
   honest caveat: the absorption of `NacciTrace` needed a second commit of `Fin`-index work
   that the `LucasSequence` absorption did not — `git diff e59dd96 6a23ec8 --stat --
   ClassicalLean/` measures 249 insertions and 21 deletions across the two modules — so
   "method" here means *reusable*, not *cheap*.
3. **An area with no number theory in it at all.** Every module in this library is reachable
   from `ℕ` in two steps. That is a fact about its history, not about mathematics.
   **Dated 2026-09-23 (order G-5, round 20):** two such areas exist now — finite information
   theory (§2.8, round 18) and statistics (§2.9, round 20).

---

## 4. Recording rule for this file

A row here is a claim about Mathlib at the pinned toolchain (`lean-toolchain`,
`lake-manifest.json`), and Mathlib moves. When a row is acted on, the first step is to re-run
its command, not to trust it. When a row turns out to be wrong — as §0 records happening — the
correction is written into the row, not silently swapped.

**Dated 2026-09-23 (order 0923, round 17): every row above was measured at `8f07524533`**, the pin
before the toolchain moved to v4.34.0 (Mathlib `5ed2965256`), except where a row names v4.34.0 —
§2.8 measured at both. Re-measured at v4.34.0 on that date and still true: §2.2's "no companion
matrix in Mathlib" (0 hits), and the searches in the headers of `Simplex/CrossEntropy.lean`,
`Simplex/LogSumExp.lean` and `NumberTheory/CompositumDiscriminant.lean`. Everything else in §1 and
§2 — §2.1, §2.3, §2.4, §2.5 included — stands as measured at `8f07524533`.
