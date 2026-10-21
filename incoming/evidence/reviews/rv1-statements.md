VERDICT: FINDINGS 1 (BLOCKING 0, MAJOR 0, MINOR 1)

# Statement review `rv1-statements` (order CLOUD-MATH-3, job 1 step 4)

A cold review of the five statement files in `$EVD/stmt/` against the order's plan rows, the
drafts in `$REPO/incoming/`, and the evidence in `$EVD`. Written 2026-10-21, about 01:07Z. I wrote
nothing inside `$REPO` and ran no `git` command or `lake build`. My scratch folder is
`$HOME/cm3-review-1`.

How I checked:

* I read the five statement files, the five drafts and the two witness starts in full. The five
  statement files have the sha256 that `evidence.log` lines 409 to 413 record. Their mtimes
  (00:46 and 00:47) come before their elaborations `stmt-<item>.out` (00:48), so the evidence is
  about these texts.
* I wrote my own signature comparison, `$HOME/cm3-review-1/hdr.py`, which is separate from
  `typecmp3.py`. For every declaration, private ones included, it takes the text from the keyword
  to the `:=` that ends the signature, and for a `def` the whole body. It then compares the draft
  with the statement file after normalising whitespace and, for 121, the `EfronStein.` prefix.
  Result: the same declarations in the same order in all five items, and every text the same
  (113: 1/1, 121: 26/26, 124: 6/6, 126: 5/5, 130: 8/8). Negative control: I planted three changes
  in a copy of the 121 file: a hypothesis of `wvar_le_of_bdd`, the body of `marg`, and a field of
  `consEquiv'`. The script reported exactly those three as `DIFF`.
* `typecmp3.py`'s inputs: every `typecmp/tc*-{draft,stmt}.lean` and `pc*-{draft,stmt}.lean` is
  its source file, unchanged, followed only by `set_option pp.fullNames true in` / `#check @…` or
  `#print …` lines. So `typecmp2-<item>.out` and `printcmp-<item>.out` compare the real texts. All
  of them are `SAME`. The two planted controls give `DIFF`.
* Import tests: I diffed each `imports/t<item>.lean` (t121d for 121, the one that
  `imports4-121.out` ran) against its draft. The only changes are the statement file's imports in
  place of `import Mathlib`, exactly the Goal list's proof changes, and, for 124 and 126, the
  witness start appended. Each is rc 0 with no message. The earlier 121 attempts (rc 1) are
  superseded by t121d, whose imports are the statement file's six.
* `locate-<item>.out` and `locate2-121.out` name the module of each constant the proofs use. I
  checked each import against them.

## Item 113 — `ClassicalLean.Analysis.SubgradientMethod`

**`min_sub_le_of_subgradient`: GENERALIZED.** The conclusion is the row's: the least of
`f (x 0), …, f (x (T - 1))` minus `f z` is at most `(‖x 0 - z‖ ^ 2 + η ^ 2 * G ^ 2 * T) / (2 * η * T)`.
The row assumes a convex `f` with subgradients `g n`. The theorem asks only `hsub`, the
subgradient inequality at each `x n`, which is what "`g n` is a subgradient of `f` at `x n`" means
for a convex `f`. So the row's statement follows. The hypotheses:

* `hsub`, `hg` and `hstep` are the row's (subgradient, `‖g n‖ ≤ G`, the step `x n - η • g n`).
* `hη : 0 < η` is the row's step: a positive step size, which the bound's denominator needs.
* `hT : 0 < T` is regularity: "the first `T` points" are nonempty, which `Finset.inf'` needs.

None of them weakens the theorem.

* Against the draft: the text is identical (my script), and the type is `SAME` (`typecmp2-113.out`).
* Namespace: the theorem is inside `ClassicalLean.Analysis.SubgradientMethod` (lines 41 to 58).
* Imports: `Mathlib.Analysis.InnerProductSpace.Basic`, the home of `norm_sub_sq_real`,
  `real_inner_smul_right`, `inner_sub_left` and the rest (`locate-113.out`). It is targeted, and
  `imports-113.out` is rc 0.
* Docstrings: the module docstring lists the result and states it correctly, `T ≥ 1` included.
  Its GENERALIZED paragraph (lines 21 to 24) is right. The theorem's docstring names "Item 113 of
  MATH-PLAN-library-2" and spells out that "within" is one-sided ("their minimum minus `f z` is at
  most that").
* There are no private helpers, and the conclusion is an inequality of reals.

Findings: none.

## Item 121 — `ClassicalLean.Probability.EfronStein`

**`variance_le_sum_variance_coord`: FAITHFUL.** It states `variance p f ≤ ∑ i, expect p (coordVar p i f)`,
the row's `Var f ≤ ∑ᵢ E[Varᵢ f]`. `hp0` and `hp1` make each `p i` a probability vector, and with
`weight` they give the product law, which is what "independent coordinates" means. `Fintype (Ω i)`
says the sets are finite. All of these are the row's setting, not additions.

**`variance_le_sum_sq_div_four`: FAITHFUL.** `hc` is the row's bounded differences, taken at every
point `x` and every pair of values `a`, `b` of coordinate `i`. The conclusion is the row's
`Var f ≤ ∑ cᵢ² / 4`.

* Definitions (lines 56 to 79), each against its docstring, the module docstring and the row:
  * `wmean r h = ∑ a, r a * h a` is the weighted mean.
  * `wvar r h = ∑ a, r a * (h a - wmean r h) ^ 2` is the weighted variance.
  * `weight p x = ∏ i, p i (x i)` is the product weight.
  * `expect p f = wmean (weight p) f` and `variance p f = wvar (weight p) f` are the mean and the
    variance under the product law.
  * `coordVar p i f x = wvar (p i) (fun a => f (Function.update x i a))` is the variance in
    coordinate `i` alone, with the other coordinates held at those of `x`. It does not depend on
    `x i`, so `expect p (coordVar p i f)` is `E[Varᵢ f]`.
  * The private defs mean what they say. `marg` is the `p 0`-average over coordinate `0`.
    `consEquiv'` is `(a, y) ↦ Fin.cons a y` with inverse `x ↦ (x 0, Fin.tail x)`.
  * All bodies are the draft's: `printcmp-121.out` gives 6/6 for the public defs, and my script
    covers `marg` and `consEquiv'`.
* Against the draft: all 26 declarations have the draft's text up to the removed `EfronStein.`
  prefix. Both theorems and all six definitions are `SAME` (`typecmp2-121.out`, 8/8).
* Namespace: every declaration is between `namespace ClassicalLean.Probability.EfronStein` (line 54)
  and its `end` (line 198). `universe u` (line 52) is not a declaration. The draft's
  `namespace EfronStein` and its `open EfronStein` are gone, and no line opens
  `ProbabilityTheory`.
* Imports: six imports, each the home of constants the proof uses (`locate2-121.out`):
  * `Mathlib.Algebra.BigOperators.Fin` (`Fin.prod_univ_succ`, `Fin.sum_univ_succ`);
  * `Mathlib.Algebra.Order.BigOperators.Group.Finset` (`Finset.sum_le_sum`, `Finset.sum_nonneg`);
  * `Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset` (`Finset.prod_nonneg`);
  * `Mathlib.Basic.Real.Basic` (`ℝ`; `Mathlib.Data.Real.Basic` is now a `deprecated_module`
    shim to it);
  * `Mathlib.Tactic.Linarith` and `Mathlib.Tactic.Ring`.

  They are targeted, and `imports4-121.out` is rc 0.
* Private helpers: each one is true, is used by the proof that follows it, and hides no
  assumption.
  * `sum_sq_shift` (needs only `∑ r = 1`).
  * `wvar_le` (from `sum_sq_shift`).
  * `wvar_nonneg` (needs `r ≥ 0`).
  * `sq_wmean_le` (Jensen for a probability vector).
  * `wvar_mix_le`: the variance under `r` is a positive semidefinite quadratic form, hence
    convex, so the variance of a `q`-average of functions is at most the `q`-average of their
    variances.
  * `wvar_le_of_bdd` (weighted Popoviciu; `∑ r = 1` makes `α` nonempty, so `c ≥ 0` follows from
    `hc a a`).
  * `weight_nonneg`, `sum_cons`, `weight_cons` and `sum_weight_cons` (algebra over the
    `Fin.cons` split).
  * `sum_weight`, `expect_marg`, `variance_split` (total variance, needing only `∑ p 0 = 1`).
  * `expect_coordVar_zero`, `coord_succ_le` and `es_aux`.
* Docstrings: the module docstring lists all six definitions and both results and states them
  correctly. Both theorem docstrings name "Item 121 of MATH-PLAN-library-2" and state the
  theorems correctly.

Findings:

1. **MINOR** (wording). `$EVD/stmt/EfronStein.lean` line 97 (draft `d121-r3-s1.lean` line 69). The
   docstring of `wvar_mix_le` reads "Variance of a mixture of functions is at most the mixture of
   their variances." In a probability module, "mixture" reads as a mixture of laws, and for that
   the inequality goes the other way (the law of total variance). The statement is right; only
   the wording can mislead. The module docstring already words it well (line 41, "the variance of
   an average is at most the average of the variances"). Proposed fix: replace the docstring with
   "The variance of a weighted average of functions, `fun b => ∑ a, q a * H a b`, is at most the
   weighted average `∑ a, q a * wvar r (H a)` of their variances." This changes a docstring only;
   no statement or proof changes.

## Item 130 — `ClassicalLean.InformationTheory.ChannelCapacity`

**`mutualInfo_bsc_le`: FAITHFUL.** For every input law `p` (`hp0`, `hp1`) and crossover
`ε ∈ [0, 1]` (`hε0`, `hε1`, which make `ε` a probability, as "crossover" means), the mutual
information of the joint law `p a * (if a = b then 1 - ε else ε)` is at most
`Real.log 2 - Real.binEntropy ε`. That is the row's upper bound on the capacity.

**`mutualInfo_bsc_half`: FAITHFUL.** At the uniform input the mutual information equals
`log 2 - h(ε)`, which is the row's "reached by the uniform input". Together the two state that the
capacity (the supremum over input laws) is `log 2 - h(ε)` and that the uniform input attains it.
The library has no `capacity` definition, and the pair is the row's statement.

* Definitions: the private `bscJoint ε p = fun ab => p ab.1 * (if ab.1 = ab.2 then 1 - ε else ε)`
  is the joint law of input and output: output equals input with chance `1 - ε`, the other symbol
  with chance `ε`. It matches its docstring. The body is `SAME` (`printcmp-130.out`, whose planted
  control is `DIFF`). Both public statements spell the joint law out, so no public statement
  depends on the private definition.
* Library definitions behind the statements:
  * `ClassicalLean.Simplex.mutualInfo` is `relEntropy P (product of marginals)`.
  * `relEntropy p q = ∑ i, p i * Real.log (p i / q i)`, with the natural log.
  * `Real.binEntropy` uses the natural log too.

  So the module docstring's "with the natural logarithm" and "`h(ε) = -ε log ε - (1 - ε) log (1 - ε)`"
  are right.
* Against the draft: 8/8 identical texts (my script), and 8/8 `SAME` with `pp.fullNames`
  (`typecmp2-130.out`). Both sides print `ClassicalLean.Simplex.mutualInfo`, so the namespace move
  changed no name's resolution, and no name needs `ClassicalLean.Simplex.` written in full.
* Namespace: `open ClassicalLean.Simplex` stays (line 44, above the `namespace` line). `bscJoint`
  and its five private lemmas sit inside `ClassicalLean.InformationTheory.ChannelCapacity`, with
  the two theorems (lines 46 to 95).
* Imports: the draft's own two (`ClassicalLean.InformationTheory.MutualInformation`;
  `Mathlib.Analysis.SpecialFunctions.BinaryEntropy` for `Real.binEntropy`). They are targeted, and
  `imports-130.out` is rc 0.
* Private helpers: each one is true and used.
  * `bscJoint_values`.
  * `bscJoint_nonneg` (needs `ε ∈ [0, 1]` and `p ≥ 0`).
  * `mul_mul_log_mul`, which is true for all reals: if either factor is `0`, both sides are `0`;
    otherwise `Real.log_mul` holds for nonzero reals of either sign.
  * `mutualInfo_bscJoint` (`H(X, Y) = H(X) + h(ε)` when `∑ p = 1`, so `I = H(Y) - h(ε)`; it needs
    nonnegativity for the library's entropy form of `mutualInfo`).
  * `bscJoint_output_half` (true for every `ε`).
* Docstrings: the module docstring lists both results and states them correctly, and its proof
  sketch names lemmas that exist. Both theorem docstrings name "Item 130 of MATH-PLAN-library-2".

Findings: none.

## Item 124 — `ClassicalLean.Probability.BernsteinInequality`

**`measureReal_sum_ge_le_bernstein`: FAITHFUL** (its last review's verdict). The conclusion
`μ.real {ω | t ≤ ∑ i ∈ s, X i ω} ≤ Real.exp (-t ^ 2 / (2 * (v + b * t / 3)))` is the row's. It is
slightly wider in two harmless ways: the bound `X i ≤ b` is needed only almost surely, and `s` may
be any finite subset of an independent family. The hypotheses:

* `hind`, `hmean`, `hb` and `hv` are the row's.
* `hmeas` and `hint` are regularity. `hint` even follows from `hint2` on a probability space,
  since `|x| ≤ 1 + x ^ 2`.
* `hint2` is the regularity that makes `∫ ω, X i ω ^ 2 ∂μ` the row's `E[X i²]`. Without it,
  Lean's junk value `0` for a non-integrable square would let `hv` hold falsely, and the
  conclusion would fail: take a mean-`0` variable at most `1` with an infinite second moment and
  `P(X = 1) = 0.9`, at `v = 0` and `t = 1`.
* `hb0 : 0 ≤ b` adds nothing. For `s` nonempty it follows from `hmean` and `hb`
  (`0 = E[X i] ≤ b`). For `s` empty the conclusion holds anyway: at `t = 0` both sides are `1`, and
  for `t > 0` the left side is `0`.
* `ht : 0 ≤ t` is implicit in the row and is needed. At `t = -1`, `b = 0`, `v = 1` with every
  `X i = 0`, the left side is `1` and the right side is `exp (-1/2)`.

So no hypothesis weakens the theorem against the row.

* Against the draft: 6/6 identical texts (my script), and the main theorem `SAME`
  (`typecmp2-124.out`).
* Namespace: every declaration is inside `ClassicalLean.Probability.BernsteinInequality`
  (lines 45 to 92). `open MeasureTheory ProbabilityTheory` stays above the `namespace` line, as
  rule 4 asks for the witness start.
* Imports: four, each targeted (`locate-124.out`):
  * `Mathlib.Analysis.Calculus.Deriv.MeanValue` (`antitone_of_deriv_nonpos`,
    `monotoneOn_of_deriv_nonneg`);
  * `Mathlib.Analysis.SpecialFunctions.ExpDeriv` (`Real.hasDerivAt_exp`, `HasDerivAt.exp`);
  * `Mathlib.Probability.Moments.Basic` (`mgf`, `iIndepFun.mgf_sum`,
    `measure_ge_le_exp_mul_mgf`);
  * `Mathlib.Probability.Distributions.Bernoulli` (the witness start's `bernoulliMeasure` and
    lemmas).

  `imports-124.out` is rc 0 for the draft with the Goal list's changes plus `w124-tail.lean`. Every
  `first` chain is cut to the branch that fires; for `hSmeas` that is `fun_prop`.
* Private helpers: each one is true and used, with no hidden assumption.
  * `exp_le_quad_of_nonpos` (the Taylor remainder is `≤ 0` for `y ≤ 0`).
  * `exp_mul_three_sub_le`: with `g = 3 + 2y + y²/2 - e^y (3 - y)` we have `g(0) = g'(0) = g''(0) = 0`
    and `g''' = y e^y ≥ 0`.
  * `exp_le_bernstein` (`e^y - 1 - y ≤ y²/(2(1 - y/3)) ≤ y²/(2(1 - c/3))` for `0 ≤ y ≤ c < 3`, and
    the quadratic bound for `y ≤ 0`).
  * `exp_mul_le_quad` (the case `y = l x`, `c = l b`).
  * `prod_le_prod_aux` (monotonicity of a product of nonnegative factors). It duplicates Mathlib's
    `Finset.prod_le_prod`, but rule 1 keeps the draft, so this is not a finding.
* Docstrings: the module docstring states the theorem correctly, with every hypothesis. Its proof
  sketch is right: the choice `l = t / D` gives `1 - l b / 3 = v / D` and exponent `-t² / (2D)`;
  `l = t / (2D)` at `v = 0` gives `l b = 3/2 < 3`. The theorem docstring names "Item 124 of
  MATH-PLAN-library-2".

Findings: none.

## Item 126 — `ClassicalLean.Probability.OrderStatistics`

**`measureReal_orderStat_le`: FAITHFUL.** For independent `X i` (`hind`) with common
`P(X i ≤ x) = F` (`hF`) and `1 ≤ k ≤ n` (`hk`, `hkn`, the range in which a `k`-th smallest exists),
the chance that the `k`-th smallest is at most `x` is
`∑ j ∈ Finset.Icc k n, n.choose j * F ^ j * (1 - F) ^ (n - j)`: the row's sum over `j ≥ k`.
`hX` (measurability) is regularity. No hypothesis is added beyond the row's.

* `orderStat v k = v (Tuple.sort v k)`. `Tuple.sort v` is the permutation that makes `v ∘ Tuple.sort v`
  monotone (`Tuple.monotone_sort`), so `orderStat v k` is the entry at position `k`, from `0`, of
  `v` sorted increasingly. The draft's proved helper `orderStat_le_iff`
  (`orderStat v k ≤ x ↔ k.val + 1 ≤ #{i | v i ≤ x}`, for every `x`) pins it down as the
  `(k + 1)`-th smallest entry. So `orderStat v ⟨k - 1, _⟩` is the `k`-th smallest, ties included,
  as the docstrings say. The body is `SAME` (`printcmp-126.out`).
* Against the draft: 5/5 identical texts (my script), and both public names `SAME`
  (`typecmp2-126.out`).
* Namespace: every declaration is inside `ClassicalLean.Probability.OrderStatistics` (lines 40 to
  77). `open MeasureTheory ProbabilityTheory Finset` stays above the `namespace` line.
* Imports: `Mathlib.Probability.Distributions.Bernoulli` alone. It is needed by the witness start
  (`bernoulliMeasure`, `bernoulliMeasure_real_apply`), and its closure holds `Tuple.sort`,
  `iIndepFun.measure_inter_preimage_eq_mul`, `iIndepFun_pi` and `Finset.sum_powerset_apply_card`
  (`locate-126.out`). It is targeted, and `imports-126.out` is rc 0 for the draft with the Goal
  list's changes plus `w126-tail.lean`, which is the docstring's claim.
* Private helpers: each one is true and used, with no hidden assumption.
  * `orderStat_le_iff`: `⇒` because the first `k + 1` sorted entries are `≤ x`; `⇐` because if
    the entry at position `k` is `> x`, so is every later one.
  * `prod_ite_mem_eq`.
  * `sum_filter_card`: there are `C(n, j)` subsets of size `j`. It is true for every `k`, both
    sides being `0` when `k > n`.
* Docstrings: the module docstring states the result and the meaning of `orderStat` correctly.
  The theorem docstring names "Item 126 of MATH-PLAN-library-2" and gives `orderStat` at position
  `k - 1`.

Findings: none.

## All five items

* There are no declarations outside the five namespaces.
* There is no `import Mathlib`.
* No main theorem's conclusion is a recursive predicate: every conclusion is an inequality or
  equality of reals.
* Naming (HANDOFF section 5): `bernstein` and `EfronStein` are the literature's standard names,
  which section 5 asks for in new material. The library already uses such names
  (`mutualInfo_markov_le`, `lucas_two_mul_eq_chebyshev_T`, `gibbsWeight_eq_softmaxT`), and the
  order's table fixes the module names. This is not a finding.

## Not checked

Nothing. Every point of the brief's "What to check", 1 to 8, was checked for all five items.

Outside the brief, and not reviewed:

* the witness starts' content against rule 4 (only their imports were in scope);
* linter results from `lake build` (rule 20; this review may not build);
* the banned-term scan, whose list is kept outside the repository.

Tool calls used: 28. That is 25 for the review, plus writing this file, hashing it, and the
hand-back.
