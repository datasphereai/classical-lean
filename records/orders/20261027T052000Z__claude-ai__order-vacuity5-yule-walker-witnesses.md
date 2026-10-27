# VACUITY-5 order: witnesses for YuleWalker's Yule–Walker theorems (VACUITY-3 rows 31 and 32)

For a plain Claude Code session on DSMain, as dustin, in tmux `cc`. Written by claude-ai on 2026-10-27 in
Project LEAN. It is the first order written to the lighter procedure (store row 20261026-063): Lean's own
check, the machine gates, one cold review and claude-ai's push review; no per-step prediction files, no
evidence-log labels, no citecheck, no plan-approval stop.

Review: one cold pass on helios (`~/vac5-review-1/out1/review.md`,
`ee4fefbbd4563c9a1411eeb03103534c4a6b164a0bc74e1474abf6a5020d3903`): PASS WITH FINDINGS (F1 to F3 MAJOR,
F4 to F11 MINOR), all applied here. It recomputed the model and found it correct and not degenerate.

**When to start.** After the night window ends: `~/lean/vacuity4-checks/scripts/ev.sh`'s header names it
(no Lean run inside it, and a separate window for whole-library runs). Both windows apply to this order's
direct runs too. If a window comes while you work, stop at a clean point (no Lean running, the tree
committed or the change only in your scratch folder), say so, and go on when Dustin says to; time inside
a window does not count toward step 4's two hours.

**Launch check.** This session was started with `CLAUDE_CODE_DISABLE_AUTO_MEMORY=1`. Print it first; if it
is not `1`, stop and say so (the cold review below must be cold).

## Goal

`ClassicalLean/Probability/YuleWalker.lean` gains three rule-2 witnesses, one each for
`covariance_eq_sum`, `isSolution_autocovariance` and `exists_poly_mk_autocovariance_eq`, built on one
concrete stationary autoregression of order 2. No declaration changes. HANDOFF's records of these rows
are brought up to date. Every gate passes. Dustin pushes after claude-ai checks the push-review file.

VACUITY-3's rows 31 and 32 are the first two theorems (store rows 20261026-049, -050). The third has the
same hypotheses plus `hp`, so it costs one more block and closes the module.

## What is already true (measured by claude-ai, 2026-10-27, 01:07 to 01:12 EDT)

- Master is `fb8beee37b74ea369f553c41a5b1279d1cf2490b` on both remotes (LEAN-36, pushed by Dustin; CI run
  40443324601 green, 12m 54s; store row 20261027-003). The worktree `~/lean/classical-lean-paper-crypto`
  is on branch `lean-36` at `fb8beee`, clean.
- `YuleWalker.lean` at `fb8beee`: sha256 `45014b3eabec5be0f41cb9e860e207681ff19e053147e36d6087e63fca39fcf0`,
  330 lines. Imports (lines 7, 8): `ClassicalLean.Combinatorics.RecurrenceGeneratingFunction`,
  `Mathlib.Probability.Moments.Covariance`. `open MeasureTheory ProbabilityTheory` (line 81), no
  `open scoped NNReal`; `namespace ClassicalLean.Probability` (line 83) to its `end` (line 305);
  `variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]` (line 85). The
  three theorems start at lines 92, 128 and 148. One witness exists (`durbinLevinson_spec`, lines 307 to
  330). The module docstring's witness note (lines 35 to 38) says, among other things, "Nothing here says
  a stationary solution exists; it is assumed".
- HANDOFF.md section 4 (lines 1067 to 1072) lists `covariance_eq_sum` and `isSolution_autocovariance` as
  "Not witnessed … Left for a ruling", and LEAN-33's dated paragraph (line 1095) says two rows remain
  not witnessed, YuleWalker's.
- Their hypotheses: `hX : ∀ t, MemLp (X t) 2 μ`; `hrec : ∀ t, p ≤ t → ∀ ω, X t ω = ∑ i : Fin p, a i *
  X (t - 1 - i) ω + e t ω`; `hγ : ∀ s k, cov[X (s + k), X s; μ] = γ k`; `hnoise : ∀ s t, s < t →
  cov[e t, X s; μ] = 0`; then `hk : 1 ≤ k` (first), `hp : 0 < p` (second and third). Binders before the
  colon: `{Ω} {mΩ} {μ} [IsFiniteMeasure μ]` from the `variable` line, `{p} {a} {X e} {γ}`, and `{k}` in
  the first.
- The draft `d3003-r1-s1` (`/data/api-credit/20261019/carry/d3003-r1-s1.lean`, sha256
  `4c0e828c2c78a33b82ed9997c1093dfc8a043a2315bb4abebf500254f1a38cae`, read only) states the first two
  theorems' hypotheses for an AR(2) model as `∃` restatements, not in rule 2's form (its Lean run is not
  in this order's evidence). Its model and steps are the starting point: `a = ![1/2, 1/4]`, independent
  Gaussian noise with variances `48/25, 16/15, 1, 1, …`, `X 0 = e 0`, `X 1 = 2/3 · X 0 + e 1`,
  `X (t + 2) = 1/2 · X (t + 1) + 1/4 · X t + e (t + 2)`; then `cov[X t, X t] = 48/25`,
  `cov[X (t + 1), X t] = 32/25`, `cov[X (t + 2), X t] = 28/25` for every `t`, which is stationarity
  from time 0 (the review recomputed these). What must change from d3003: its noise comes from
  `exists_hasLaw_indepFun` (`Mathlib.Probability.HasLawExists`, not allowed here), so its `hWm`, `hvar`
  and `hind` are rewritten for `Measure.infinitePi` (a coordinate's law through `infinitePi_map_eval` or
  `measurePreserving_eval_infinitePi`, then `MemLp` and variance from the Gaussian lemmas; independence
  of two coordinates from `iIndepFun_infinitePi`); its goal-changing `show` lines become `change` (a
  `show` that changes the goal is a lint warning); `ℝ≥0` is written `NNReal` or behind
  `open scoped NNReal in`.
- Mathlib at this tree (claude-ai's probes in its own clone `~/api-credit/cl-354d835`, whose YuleWalker
  equals `fb8beee`'s): `/tmp/claude-ai-vac5/p1.lean` (imports YuleWalker, Gaussian.Real, ProductMeasure)
  finds `Measure.infinitePi`, `measurePreserving_eval_infinitePi`, `memLp_id_gaussianReal`,
  `variance_id_gaussianReal` and `IndepFun.covariance_eq_zero`, and the `IsProbabilityMeasure` instance
  for `Measure.infinitePi (fun _ ↦ gaussianReal 0 1)`; its one error is `iIndepFun_infinitePi` unknown
  (rc 1, `p1.out`). `/tmp/claude-ai-vac5/p3.lean` (imports YuleWalker, Gaussian.Real and
  `Mathlib.Probability.Independence.InfinitePi`, not ProductMeasure) finds `iIndepFun_infinitePi` and
  `Measure.infinitePi_map_eval` and the same instance (rc 0, `p3.out`). Neither probe tried the instance
  for the varying variances `v t`; job step 4 is the first to. `FairGame.lean` builds witnesses on
  `Measure.infinitePi` with `iIndepFun_infinitePi` (its blocks from line 226): the pattern to follow.
- In claude-ai's clone at `354d835`, a file importing `ClassicalLean` has 5729 modules, with
  `Mathlib.Probability.Distributions.Gaussian.Real`, `Mathlib.Probability.Independence.InfinitePi` and
  `Mathlib.Probability.ProductMeasure` among them (`p2.out`). LEAN-36's only import was a Mathlib file
  already in that closure, so these three are in the closure at `fb8beee` too; an import line of any of
  them in YuleWalker adds nothing to the root's closure.
- `HANDOFF.md` sha256 `87961e289177386e8e5303d387c9b14e15abf8471a7b150d3f72f93632cee3b3`;
  `records/rules.toml` `2b5fb47dc4751d93171969649f9dc4f7b7e1233cdbc36bb06713c20e23bb0359`; the last round
  is 74, so this order's is 75; `records/orders/INDEX.md` 75 lines and `records/CLAIMS.md` 67, each last
  line LEAN-36's row. At G `58339e6` LEAN-36 measured: AxiomGate 3666, type dump 4163 records (3666 thm,
  497 def), witness gate OK 179.

## The witnesses (rule 2's form)

One model for all three blocks, written inline in each (rule 2 allows no helper declaration):
- `Ω = ℕ → ℝ`, `μ = Measure.infinitePi (fun t ↦ gaussianReal 0 (v t))` with `v 0 = 48/25`,
  `v 1 = 16/15` and `v t = 1` from 2 on (as `NNReal` values);
- `e = fun t ω ↦ ω t`;
- `X` the recursion above, written as a term (d3003's `Nat.rec` on pairs is one way);
- `γ = fun k ↦ cov[X k, X 0; μ]` (a table of values is not an option: `γ` follows the recurrence for
  every `k`);
- `p = 2`, `a = ![1/2, 1/4]`; for `covariance_eq_sum`, `k = 2`.

Each block is `example := ClassicalLean.Probability.<name> (Ω := ℕ → ℝ) (μ := …) (p := 2) (a := …)
(X := …) (e := …) (γ := …) <hX> <hrec> <hγ> <hnoise> <the last argument>` (and `(k := 2)` in the first),
every binder before the colon supplied, the proofs as inline `by` blocks adapted from d3003, after the
module's last line, with the docstring "The hypotheses of `<name>` hold together: …" saying what moves.
What must move: the noise variance is positive at every time (no constant process); the two
coefficients are different and nonzero; `γ 0`, `γ 1`, `γ 2` are `48/25`, `32/25`, `28/25` (lag 2 uses
both coefficients). A witness proof may be long. Rule 2's six words may not appear: `sorry`, `admit`,
`native_decide`, `implemented_by`, `axiom`, `set_option` (so no `set_option maxHeartbeats … in`; if a
proof times out, split it into smaller `have` steps). Nor `(config :=` or any `reduceBool`-family name.

Import lines: YuleWalker may gain `Mathlib.Probability.Distributions.Gaussian.Real` and
`Mathlib.Probability.Independence.InfinitePi` (and `Mathlib.Probability.ProductMeasure` only if a block
needs it), all in the root's closure. Not `Mathlib.Probability.HasLawExists`, nor anything else.

## Scope

- Branch `vacuity-5` from `fb8beee` in `~/lean/classical-lean-paper-crypto`. Nothing pushed. No sudo.
- You may change: `ClassicalLean/Probability/YuleWalker.lean` (witness blocks after the last line, the
  import lines above, and the witness note of its module docstring, lines 35 to 38, so that it says the
  hypotheses are now witnessed); `records/`; `HANDOFF.md` section 1 (one short dated VACUITY-5 paragraph
  after LEAN-36's) and section 4 (one short dated paragraph after LEAN-33's, saying the two YuleWalker
  rows, and the third theorem, are witnessed by VACUITY-5). Nothing else; needing to is a stop.
- Your files: `~/lean/vacuity5-checks/` (scratch copies, probes, the type-dump files and their outputs,
  the expected-results file, logs). Nothing untracked in the worktree, so its tree stays clean at G.
- Lane writes: the report (`ds_file`, project `lean`, job `VACUITY-5`, kind `report`) and the push-review
  file (subdir `data`, name `VACUITY-5-push-review.txt`), through the connector. Read lane files through
  the connector too.
- Off limits as in every order: `~/lean/classical-lean` and its `master`, every earlier order's folder
  (read only), `~/api-credit/` and `/tmp/claude-ai-*` (claude-ai's; read only), `/data/api-credit/` (read
  only), Dustin's `~/.config/classical-lean/banned-terms` (never print or copy it), every GitHub branch.
- Lean runs: one at a time, under the 12 GB cap (`systemd-run --user --scope -q -p MemoryMax=12G
  -p MemorySwapMax=0`), `~/.elan/bin` on `PATH`, `pgrep -ax lean` empty before each, outside the
  windows above.

## The work

1. **Check.** Launch variable; `git fetch origin`; `git ls-remote origin master` and `git ls-remote
   github master` both `fb8beee…`; porcelain empty; the sha256s above (YuleWalker, d3003, HANDOFF,
   rules.toml); `pgrep -ax lean`. If anything differs, stop.
2. **Before.** Copy `lean/LEAN-33/scripts/TypeDumpPI.lean` (sha256
   `1fcb69f41ddbd35f84862521d2ead5946a0bd52caf5f60b6d10e966cfd9776ff`) and `g8-typediff.py`
   (`371eda9a2e5065abaa8f36bac9872d0f15e7bade72a248d5f0f88f20b4eacb71`, saved as `g8_typediff.py`) from
   the lane through the connector into `~/lean/vacuity5-checks/`, checking each hash. On a clean
   `fb8beee`, from the repository root: `lake build`, then
   `lake env lean ~/lean/vacuity5-checks/TypeDumpPI.lean > ~/lean/vacuity5-checks/td-before.out`, its
   lines starting `{` kept in `td-before.jsonl`, and `python3 -I ~/lean/vacuity5-checks/g8_typediff.py
   check td-before.jsonl`: 4163 records.
3. **Branch and records.** `git switch -c vacuity-5 fb8beee`. One records-first commit as
   `records/README.md` says: this order's copy in `records/orders/`, its INDEX and CLAIMS rows, round 75's
   fragment, and LEAN-36's push recorded in LEAN-36's INDEX and CLAIMS rows the way VACUITY-4's push is
   recorded in VACUITY-4's rows (text: `; pushed by Dustin: master fb8beee on both remotes, CI run
   40443324601 green`). check_records PASS 140.
4. **Write the witnesses** in a scratch copy first (`~/lean/vacuity5-checks/`), elaborating with
   `lake env lean` until each block is accepted with no warning, then move them into the module with the
   import lines and the docstring note. The first block is the hard one; the other two reuse its
   arguments. If after two hours of work no block is accepted, stop and report what fails. Commit the
   module alone: this commit is G.
5. **Gates on the clean tree at G.** Write the expected result of each in one file in
   `~/lean/vacuity5-checks/` first, then run: `lake build` (4193 jobs, 0 errors, 0 warnings);
   `lake env lean tools/AxiomGate.lean` (PASS, 3666, unchanged: examples add no constant);
   `python3 -I tools/check_sorry.py`; `python3 -I tools/check_records.py`;
   `lake env lean tools/VacuityGate.lean` (PASS); `python3 -I tools/banned_vocab_scan.py ClassicalLean`;
   `python3 -I tools/witness_gate.py Probability/YuleWalker.lean` (OK 4, copy-error 0), then the whole
   library, `python3 -I tools/witness_gate.py` (PASS, OK 182 = 179 + 3, about 27 minutes); the type dump
   again into `td-after.jsonl` and `python3 -I ~/lean/vacuity5-checks/g8_typediff.py diff td-before.jsonl
   td-after.jsonl` (`removed=0 added=0 changed=0 proof_only=0`: examples and import lines from the
   closure add and change nothing). Report each beside what came out. Gate 7, the bridge search and the
   report tool are not run (no theorem is added).
6. **One cold review** of the three witness blocks, by one fresh subagent that has not seen your work:
   give it the blocks, the three theorems' statements, HANDOFF section 4's "Satisfiability witnesses"
   paragraph (with rule 3's case of the moving process) and this order's "What must move". It checks each
   block against rule 2's form and rule 3 (nothing degenerate, what must move does move). Fix what it
   finds (a fix to the module reruns step 5's module gates); a second pass only if a fix changes a
   block's arguments.
7. **Documents and records.** The two HANDOFF paragraphs (sections 1 and 4) in one commit; then
   `python3 tools/compile_rules.py drift records/rules.toml HANDOFF.md` on that commit (expected PASS,
   written down first; run as earlier orders ran it). Round 75's fragment completed with the commit
   hashes and the counts from the gates' output; the CLAIMS row closed and the INDEX row set, in a
   records-only commit. check_records PASS at the final HEAD.
8. **Report** (`ds_file`, kind `report`): what each witness takes and what moves; each gate's expected
   and observed result, cited from its output; the review and its fixes; anything that missed; the push
   command as one line, not run:
   `cd ~/lean/classical-lean-paper-crypto && git push origin vacuity-5:master && git push github vacuity-5:master`.
9. **Push-review file** (`ds_file`, subdir `data`, name `VACUITY-5-push-review.txt`), one script, each
   command with its full output: `git rev-parse HEAD`; `git status --porcelain`; `git ls-remote origin
   master` and `git ls-remote github master` (both still `fb8beee`); `git log --name-status --format='== %h
   %s' fb8beee..HEAD`; `git diff --name-only fb8beee HEAD`; `git diff -U0 fb8beee HEAD -- ClassicalLean |
   grep '^[-+]import' || true`; `git diff -U0 fb8beee HEAD -- ClassicalLean | grep '^-' | grep -v '^---' ||
   true` (expected: only lines of YuleWalker's docstring witness note); the type-dump `DIFF` line; the
   whole-library `WITNESSGATE` line; `grep -rnwE
   'reduceBool|reduceNat|ofReduceBool|ofReduceNat|trustCompiler|native|plausible|slim_check|evalExpr|evalConst'
   ClassicalLean/ || true`, `grep -rn '(config *:=' ClassicalLean/ || true` and
   `grep -nE 'set_option|implemented_by|\badmit\b|\bsorry\b|\baxiom\b' ClassicalLean/Probability/YuleWalker.lean || true`
   (each expected to find nothing). Then stop: claude-ai reviews it before Dustin pushes.

## Done means

Branch `vacuity-5` from `fb8beee`, clean, nothing pushed; the three witnesses in YuleWalker, each OK in the
witness gate and passed by the cold review; no declaration changed (type dump all zeros); every gate in
step 5 and the drift check pass; the records and the two HANDOFF paragraphs committed; the report and the
push-review file in the lane, their hashes matching yours. Then tell Dustin in a few plain sentences what
was done, defining any technical term the first time, and give the two files' hashes.

## Not in this order

GATE-2; LEAN-37 (batch 7); LEAN-38 (bridges 160 to 162); TWINS-1; any push.
