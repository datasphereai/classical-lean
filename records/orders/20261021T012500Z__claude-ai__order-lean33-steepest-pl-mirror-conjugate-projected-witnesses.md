# LEAN-33 order: batch 3 of the API-credit drafts (items 111, 112, 116, 117, 134) and the witnesses of VACUITY-3 rows 7, 8, 9, 10 and 67

For a plain Claude Code session on DSMain, as dustin, in tmux `cc`. Written by claude-ai on
2026-10-20 under lean/CLOUD-LANDING-PLAN-2.md ruling 2 (batches 3 to 7 land on DSMain as LEAN-33 to
LEAN-37), after Dustin's question of 2026-10-20 20:04 EDT whether CLOUD-MATH-3 and LEAN-33 can run
at the same time; claude-ai's answer, yes, rests on the facts below, and Dustin may veto it.
Lane files named `lean/...` are under /opt/datasphere/lane/inbox/threads/staging/lean/ (ds_* tools:
root `lane`, path `inbox/threads/staging/lean/...`). This order is `lean/LEAN-33/order.md`; its
inputs are `lean/LEAN-33/scripts/` and `lean/LEAN-33/data/`.

**New lane files go through `ds_file`** (project `lean`, job `LEAN-33`): your plan is kind `plan`
(it lands as `lean/LEAN-33/plan.md`; a second becomes `plan-r2.md`, never overwriting), the report
kind `report`, the push-review file subdir `data`, name `LEAN-33-push-review.txt`. Compare each
reply's `post_sha256` with your own. Appending to the bridges file (job 5b) is `ds_write_staging`
in append mode with `expect_sha256`. **Track the order's steps with the task tools** (lane
`lean/NOTE-20261015-task-list-rule.md`).

Review: three passes on 2026-10-20 by one fresh subagent that had not seen the order being written (read-only, a read list in /tmp/claude-ai-l33/review/ on helios). Pass 1: PASS WITH FINDINGS, 0 BLOCKER, 5 MAJOR, 20 MINOR, all applied (r1). Pass 2: 22 of the 25 fixed, 3 in part, and 1 new MAJOR and 7 new MINOR, all applied (r2). A confirming pass on those: 9 of 11 fixed, 2 in part, 2 new MINOR, all applied (r3); r3 itself was not reviewed again. Not reviewed: how `ds_file` and `ds_write_staging` behave; the census tails' output form; the adapted CLOUD-MATH-2 scripts; `ev.sh`, `rootrun.sh` and `hl.sh` beyond the lines quoted here.

## What is already true (measured by claude-ai on 2026-10-20 from 20:17 to 20:26 EDT on DSMain over ssh from helios, in claude-ai's own clone `~/api-credit/cl-04e4a38` of master, its own build; outputs in `/tmp/claude-ai-l33/` on DSMain and `lean/LEAN-33/data/facts.txt`, sha256 `c052bc0001ad49a2d0d783837383737e425895231a0e7751f314b32f14ddeccc`)

- **Master.** Both remotes (`/data/git/classical-lean.git` and GitHub) are at
  `04e4a3842055026616256cf549ded9bf4bcfdd96`, MERGE-2's last commit, pushed by Dustin (the bare
  repo's master ref written 2026-10-20 19:18:05 EDT). Its GitHub CI run 39514101753: success. At
  it (claude-ai, lean/CLOUD-MATH-3/data/cut-evidence.txt a476ec39): `lake build` 4188 jobs, 0
  warnings; AxiomGate PASS 3458; VacuityGate PASS, 1 reviewed helper; check_sorry PASS 135;
  check_records PASS 135 (98 records files, 1 named exemption); `compile_rules.py drift` PASS.
- **Running beside you.** Order CLOUD-MATH-3 (lean/CLOUD-MATH-3-order.md, dfe8e5a9) runs in a
  Claude Code cloud session on GitHub branch `cloud-math-3` (`04e4a38` plus `313e9a7`). It adds
  five new modules (Analysis.SubgradientMethod, Probability.EfronStein,
  Probability.BernsteinInequality, Probability.OrderStatistics, InformationTheory.ChannelCapacity),
  writes round 68, and its records commit appends MERGE-2's push to MERGE-2's INDEX and CLAIMS
  rows. It changes no existing module. None of this order's seven modules is imported by any of
  its five drafts (113, 121, 124 and 126 `import Mathlib`; 130 imports
  `ClassicalLean.InformationTheory.MutualInformation`, which this order does not touch). This
  order's round is 69. Whichever of the two reaches master second is merged by a later order.
  CLOUD-MATH-3's final message checks that `git ls-remote origin master` is the same at its start and
  its end, so master must not move while that session runs: Dustin pushes LEAN-33 only after
  CLOUD-MATH-3's session has ended and claude-ai has said so (5f).
- **The worktree** `~/lean/classical-lean-paper-crypto` is on branch `merge-2` at `04e4a38`, clean.
  Remotes: `origin` the bare repo, `github` GitHub. The main clone `~/lean/classical-lean` is the
  nightly's.
- **Records at `04e4a38`:** the last round is 67 (MERGE-2); the latest bridge baseline is
  `records/bridges/MERGE-2/` (2877 pairs, 699 shapes, N = 134, at `0169919`, whose Lean tree is
  `04e4a38`'s); `tools/vacuity_reviewed.txt` holds 1 entry; ROADMAP.md's last section is 1.25
  (line 751); HANDOFF.md section 4's "Satisfiability witnesses" paragraph lists rows 9, 10 and 67
  as not witnessed.
- **The five drafts** (in `/data/api-credit/20261019/carry/`, read-only, whose `SHA256SUMS` is
  a2f5e552; the same bytes in `~/api-credit/drafts/`). Each imports only library modules; each
  declares at the root namespace. All five pass the API-credit pipeline's scorer at `04e4a38` (rc
  0, 0 errors, every planned name, axioms only propext, Classical.choice, Quot.sound;
  `~/api-credit/recheck-04e4a38/results/`, 2026-10-20 20:20 EDT). With rule 20's four flags, rc 0;
  the warnings are listed.

  | item | draft | sha256 | home module | main theorem | its declarations | four-flag warnings |
  |---|---|---|---|---|---|---|
  | 111 | d111-r1-s2 | `42dac059db124b9369c490c392c7b7ee32e4801922337034a99005eac34b7aad` | Algebra.Kantorovich | `quadForm_steepestStep_le` | that theorem | line 83: `field_simp <;> ring`, the `ring` never runs |
  | 112 | d112-r1-s2 | `dc03377741e21808691f3aa5dac4523fcede2d6e32123fcff5f23139cbd88022` | Analysis.GradientDescent | `sub_le_pow_mul_of_polyakLojasiewicz` | that theorem | none |
  | 116 | d1116-r1-s1 | `8ad3e6a15726367e40e1bab2bb464c638cbb574b97832c01c91303b2518b97a3` | Analysis.ExponentialWeights | `isMinOn_inner_add_relEntropy_softmax` | that theorem and the private `inner_add_relEntropy_eq_aux`; a `variable {ι : Type*} [Fintype ι]` line | none |
  | 117 | d117-r1-s2 | `ba841d5cda5e895aed81b77d1f2ac69eaba051ace6a983832aa1ee2e4ef75f9d` | Analysis.ConvexConjugate | `convexConjugate_logSumExp` | that theorem | `show` that changes the goal, lines 30 and 33 |
  | 134 | d134-r1-s1 | `252126ed11e7b7cda85b798bc1099998304a86475fcad8caf6e58e163821bef1` | Analysis.GradientDescent | `sub_le_of_projGradientStep` | that theorem and the private `projStep_aux`; a `variable {E : Type*} …` line | line 50: the hypothesis `hKc : IsClosed K` is never used |

  Their plan rows (MATH-PLAN-library-2.md section 7, lines 420 to 443): 111 steepest descent with
  exact line search shrinks `xᵀ A x / 2` by at least `((M − m)/(M + m))²` each step; 112
  Polyak–Łojasiewicz gives gradient descent with step `1/L` the rate `(1 − μ/L)^k`; 116 exponential
  weights is mirror descent (`softmax(log x − η ℓ)` is the one minimiser over the simplex of
  `η ⟨ℓ, y⟩ + D(y ‖ x)`); 117 the convex conjugate of log-sum-exp at `p` in the open simplex is
  `∑ p i log p i`; 134 projected gradient descent on a closed convex set has item 18's rate
  `L ‖x₀ − z‖²/(2k)`. Their last reviews are the API-credit pipeline's (lean/API-CREDIT-CARRY-1.md
  lists them as reviewed carries).
- **Names.** No declared name of the five drafts exists in the library, under its home namespace or
  at the root (a Lean `env.contains` check of all seven, `declnames.out`); `inner_add_relEntropy_eq_aux`
  and `projStep_aux` appear in no file under `ClassicalLean/`.
- **Two new import lines, no cycle.** ExponentialWeights gains
  `import ClassicalLean.InformationTheory.Entropy` (116's draft imports it; the plan row says so)
  and ConvexConjugate gains `import ClassicalLean.Simplex.LogSumExp` (117's draft). Neither
  ExponentialWeights nor ConvexConjugate is in the import closure of Entropy or of LogSumExp
  (`closure.out`). No module is added, so the build's job count stays 4188 (job 3 confirms it by
  rule 27's measurement). **The two lines alone,** added in claude-ai's clone (2026-10-20 20:48
  EDT, then restored): `lake build` rc 0, 4188 jobs, 0 warnings, rebuilding exactly
  ConvexConjugate, ExponentialWeights, FiniteGame and the root; the type dump against `04e4a38`'s:
  `DIFF removed=0 added=0 changed=0 proof_only=0` (facts.txt, `imp.out`, predicted beforehand).
- **The seven home modules at `04e4a38`** (sha256; namespace; last line; examples after the
  namespace):
  - `ClassicalLean/Algebra/Kantorovich.lean` `67e03d7994f2d89b441adb71f105b2406cf2525db0dad4c8b0ff33fc91964a52`; `namespace ClassicalLean.Algebra.Kantorovich` (line 81) to its `end` at line 227, the last line; its two examples sit inside the namespace (lines 210 and 219); `open Matrix` at line 79.
  - `ClassicalLean/Analysis/GradientDescent.lean` `ef34756e8539992b3fd2843e4fc5f6a179dd739d440ca348d125586fb57a642e`; `namespace ClassicalLean.Analysis` (line 93) to line 385; five witnesses after it (from line 390); 456 lines; `open Finset` and `open scoped RealInnerProductSpace NNReal` at lines 90 and 91.
  - `ClassicalLean/Analysis/ExponentialWeights.lean` `2f38e6bcbe29f20a647c9d0e6c888ed713fae62479f9ceb5a9a99e3514dcfae4`; `namespace ClassicalLean.Analysis` (line 60) to line 165; one witness after it (line 170); 172 lines; `open Finset MeasureTheory ProbabilityTheory`, `open scoped NNReal`, `open ClassicalLean.Simplex` at lines 56 to 58.
  - `ClassicalLean/Analysis/ConvexConjugate.lean` `118dfa5b93ef675ab61cee90ffdc23f105dcab1715549903afa41e08583e8a03`; `namespace ClassicalLean.Analysis.ConvexConjugate` (line 65) to line 120; eight examples, one inside the namespace (line 118) and seven after it (lines 124 to 158), six of those behind `open ClassicalLean.Analysis.ConvexConjugate in`; 158 lines; imports only Mathlib.
  - `ClassicalLean/Probability/LikelihoodScore.lean` `1c4c6af7bde57c31c37a53022d407884f4c54b6ce388d4719cd43bc2e99b51d8`; `namespace ClassicalLean.Probability.LikelihoodScore` (line 79) to line 397; three witnesses after it, each behind its own `open MeasureTheory ProbabilityTheory Filter in` (those lines are 399, 436 and 473); 557 lines.
  - `ClassicalLean/Probability/EffectiveSampleSize.lean` `56fd0a3719a408f027e0e958d1ab2bc54a8f7c79bbe027592306e1ed6bb4ccdb`; `namespace ClassicalLean.Probability.EffectiveSampleSize` (line 143) to line 662; one witness after it (from line 663, `variance_average_le_of_steady'`); 698 lines; already imports `Mathlib.Probability.HasLawExists` and `Mathlib.Probability.Distributions.Gaussian.Real`.
  - `ClassicalLean/Probability/GlivenkoCantelli.lean` `79d8c53c9c638ccb901d684778e97513c0629b228b38c0265c0831b28ee11cee`; `namespace ClassicalLean.Probability` (line 100) to line 407; two witnesses after it (from line 409); 454 lines.
  Their `variable` lines: Kantorovich line 83 `{n : Type*} [Fintype n] [DecidableEq n]`;
  GradientDescent line 95 `{E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]`,
  the same as d134's line 13; ExponentialWeights line 62 and ConvexConjugate line 67
  `{ι : Type*} [Fintype ι]`, the same as d1116's line 14.
  The three probability modules elaborate standalone with the four flags with rc 0 and no message
  (`base-*.log`); the other four were not run that way.
- **VACUITY-3 rows** (lean/VACUITY-3-report.md lines 133 to 136 and 193; HANDOFF.md section 4,
  "Satisfiability witnesses"; lean/VACUITY-3-ruling-3.md ruling 1):
  - **Rows 7 and 8**, LikelihoodScore's `measureReal_sum_ge_le_exp_neg_relEntropy` and
    `measureReal_sum_ge_le_exp_neg_sq`, are witnessed at lines 399 to 471 (line 472 is blank) with `N = 1`: one round
    of outcomes and later ones identically `0`, which ruling 1 sent to the next gate order ("at
    least two rounds, with the later outcomes not identically `0`"). Carry `d3005-r1-s2`
    (`9a5c43b4ad185e9fbb463c8cc7b83c4780e9008c5cc5df1ff49bdf0690d4170a`) holds two blocks in rule
    2's form with `N = 2` and two genuine fair coins. A copy of the module with lines 399 to 472
    replaced by the carry's lines 3 to 175 and one blank line (gather2.sh appends it after the block;
    the same text as keeping blank line 472) elaborates with the four flags: rc 0, no `sorry`, 8
    warnings, all inside the new block and the same as the carry alone gives (its lines 55 and 142:
    `norm_num` that never runs; 61 and 148: an unused simp argument `Fintype.sum_bool` and `<;>`
    where `;` suffices).
  - **Rows 9 and 10**, EffectiveSampleSize's `variance_average_eq_of_steady` and
    `variance_average_le_of_steady`, are not witnessed. LEAN-31 later witnessed the primed
    `variance_average_le_of_steady'` (line 663 on; commit `593fca1`, item 104) with `Measure.infinitePi` of Gaussian laws.
    claude-ai's two blocks `lean/LEAN-33/data/w9-10.lean`
    (`30eeb3f78d2df17b270ca40301b10197ae633fe7784edd8fdf3c3008e68dbb2e`) apply the two unprimed
    theorems to that model; appended to a copy of the module and elaborated with the four flags:
    rc 0, no message. Carry `d4001-r1-s1` (589b166e) is not used: its three examples are `∃`
    restatements, which HANDOFF.md section 4's standing rule of round 58 forbids.
  - **Row 67**, GlivenkoCantelli's `tendsto_sup_abs_empiricalCDF_sub`, is not witnessed.
    claude-ai's block `lean/LEAN-33/data/w67.lean`
    (`c0a1125ee21d5ae3bf0d579c893168798299c60602daa29f53748d91c1a05f77`) applies it to LEAN-32's
    fair coins on `ℕ → Bool` (the module's own witnesses from line 409; commit `688905c`, item 107);
    appended: rc 0, no message.
  - None of these blocks holds `sorry`, `admit`, `native_decide`, `implemented_by`, `axiom` or
    `set_option` (grep), so the older rows' exception for those words is no longer used.
- **The type dump (rule 14).** helios's `~/work/_bump-evidence/TypeDumpPI.lean` and
  `g8_typediff.py`, rule 14's pair, are copied byte for byte to `lean/LEAN-33/scripts/TypeDumpPI.lean`
  (`1fcb69f41ddbd35f84862521d2ead5946a0bd52caf5f60b6d10e966cfd9776ff`) and
  `lean/LEAN-33/scripts/g8-typediff.py` (`371eda9a2e5065abaa8f36bac9872d0f15e7bade72a248d5f0f88f20b4eacb71`;
  the lane forbids `_` in a file name; copy it back as `g8_typediff.py`). Run at `04e4a38` in
  claude-ai's clone: rc 0 in 63 s, 3930 records (3458 `thm`, 472 `def`), 35 MB; `check`: elided 0,
  missing_fields 0; the dump against itself: `DIFF removed=0 added=0 changed=0 proof_only=0`.
- **Helpers** in `~/lean/lean32-checks/scripts/` (sha256): `ev.sh` `ee1d209eaaef0a743b79cd7cc44561e266e74cd6702bd3b943d7f218d9d10efc`,
  `hl.sh` `09a418f2c2593450a22497c64753e81e4542574fa00deb3b8b2f267193564054`, `rootrun.sh`
  `4d739a45d5a49d1c041dd0f239264ddbab15dfd5c3b431c24706da90dae10131`, `el.sh`
  `18260c3e69128e8410b8117202b68ac15a7ca17b9896c9dd23448137ac731c84`, `mkcensus.sh`
  `be0ce32f8af8726580d58fffcff73f90e1cdd25692f789f1bf1069de5a42f3b5` (each with exactly one line
  `D=/home/dustin/lean/lean32-checks`), `probecheck.py`
  `d19ec3c66b5c0b93355078dafaf6fe7f8fe22e345884fb545e1aeb262ed9e207` (one line
  `D = '/home/dustin/lean/lean32-checks'`), `evcite.py`
  `11565ca5adc96a067c3b9110a3c2cd0c5cb87a86c90958dc1f59b2140745eedf` (the path in its docstring and
  in its `LOG = ` line), `mkconfirm.py` `03c4c1c927554843d1da5d54b0e01e093e3066c9c6d799555900d89193b689f4`
  (the path on 6 lines), `citecheck.py` `7e3e38f7dd8b2ce97b3da5250feac31be410a99f840272324b18b021503bc366`,
  `briefcheck.py` `aa36b5686ac507a360149c347c8f96156bbffe2abc6beca94197f727ae65d95b`, `mkbrief.py`
  `8bd502b28d276d738356024001b0aaf7562d355cb009c6c274877978094c3366` (no path); and
  `~/lean/lean32-checks/census/census-tail-lean28.lean`
  `2c950fc9d39cfea54562aae80bac14a36f2cbef9e9ec5150143ca6437eb56d6b`,
  `census-all-tail-lean28.lean` `83de4147767d603ef129cc674f0b7a2d97531072108762618b2ca01aeb06baa8`.
  Their other inputs (measured after review pass 1, facts.txt): `probecheck.py` diffs a module
  against `BASE = '8071e74'` (its line 29) and reads `$D/evidence.log`'s PROBED lines,
  `$D/seed.txt` (only if it exists: its `probed()` tests `os.path.exists`) and `$D/allowlist.txt`;
  `hl.sh` logs `sha256sum <path> :: <hash>`, the form `el.sh` line 16 greps for;
  `~/lean/lean32-checks/allowlist.txt` is
  `167e0a05e6b3e98a82051b495ccef8ea6d92abb7d67a0cf894d3f9e1309b523e` (22 lines); `el.sh` line 17
  calls `$D/hl.sh`, which does not exist (`hl.sh` is in `scripts/`), so LEAN-32's `el.sh` never
  logged the allowlist's hash; `ev.sh` and `rootrun.sh` run a command under `/usr/bin/time -v` with
  its stderr in the same output file, so a whole-library output ends with time's report.
  `mkbrief.py` and `mkconfirm.py` are LEAN-31's and predate RULES-1's renumbering of section 6
  (2026-10-19). CLOUD-MATH-2's scripts, written for the 21-rule section 6, are in git history
  (`git show 284dd5f:incoming/evidence/scripts/<name>`): `mkbrief.py`
  `f57c727f3441d1aad24d40406aef7603f46b4a1064b2f7836470aaeadba48c3a`, `filltask.py`
  `ee63913b7f100d39f1ec5432c6fb1d5b934bb5e9da250b42400906f2a1362543`, `quotecheck.py`
  `9d92f65fe14080c80708bf0e24ac9499be5361c7da0152522f261c38a1c13943`, `typecmp.py`
  `58e79d6695c3a1e89c5c19cb4abb20ea12b6baa4ddcdee73663a14a5e9abf322`, `mkprobes.py`
  `cbb38daa91968eee500dfa316cf444ba5770a79095afe2328f89d091ad9be7dd`, `mkdiscover.py`
  `a65f6d536931c7ad52dca530f7c3dc09ccdc541c9daeeb45dacc33b1957163dd` (each names CLOUD-MATH-2's
  paths; read and adapt before use).
- **MERGE-2's runs, the pattern for your gates** (`~/lean/merge2-checks/`): the vacuity tests "89
  tests, 47 flagged, 0 rule-5 run-outs, 0 mismatches"; gate 7 "ALL PASSED" at `0169919`; the
  report tool's output `report.out` (`2fdd0ca8643aa5a459edb7fe654e24a651de41d593435558072564683690856c`;
  MERGE-2's report gives 1918 theorems written); `ev.sh`'s night window is LEAN-31's, in its header.
- **The bridges file** `lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md` is
  `7cec75c22d572b7bfce8bd24e2cea6d53a34394d2478c9da770d4ac6d5e6d68e`; its last row is 162, so new
  rows start at 163. Plan 2's ruling 5 (lean/CLOUD-LANDING-PLAN-2.md) asks every bridge search to
  say how its pairs were checked.
- **Timers on DSMain** (read on 2026-10-20 with `systemctl --user list-timers` and `crontab -l`):
  memory-index at midnight; restic, ds-hygiene, the daily verify, lean-nightly and the backup bundle
  between 2 and 4 in the morning; the store sync before 6; w29-tracker and w29-sysmap every few
  minutes (they load no Lean).

## Goal

The five items proved in their home modules, each inside its module's namespace, with witnesses,
reviews and records; VACUITY-3 rows 7 and 8 re-witnessed with two genuine rounds, and rows 9, 10
and 67 witnessed for the first time; no existing declaration changed (the type dump shows it);
every gate passing, gate 7 included; the bridge search and the report tool run; HANDOFF.md and
ROADMAP.md saying what changed. Dustin pushes after claude-ai checks the push-review file.

The changes asked of each draft (from the measurements above):
- **Every item:** its declarations go inside its home module's namespace block, before that block's
  `end`, reusing the module's own `variable` line where it is the draft's (GradientDescent's
  line 95 is d134's line 13, ExponentialWeights' line 62 is d1116's line 14: drop the draft's copy);
  a draft that binds its types in its own signature (111, 112, 117) keeps them; the content of a
  draft's `/-! … -/` block (d112, d1116, d134) goes into the module docstring; the draft's `open` lines the module lacks become `open … in` on the declarations
  that need them; references the namespace makes ambiguous or wrong are written in full (job 1's
  type comparison decides); each main theorem's docstring names its item ("Item 111 of
  MATH-PLAN-library-2") and its draft; the module docstring lists the new result; a step whose
  effect is not determined is cut to what fires; every warning the four flags or `lake build`
  report is fixed in the proof only, each fix listed in round 69.
- **111:** line 83, `field_simp <;> ring` becomes `field_simp`.
- **116:** ExponentialWeights gains `import ClassicalLean.InformationTheory.Entropy`.
- **117:** ConvexConjugate gains `import ClassicalLean.Simplex.LogSumExp`; lines 30 and 33's `show`
  become `change`.
- **134:** the unused hypothesis `hKc : IsClosed K` is removed (claude-ai's ruling; Dustin may veto).
  The proof takes the nearest-point property of each step as the hypothesis `hx`, so closedness is
  never used; it is what makes such nearest points exist (Mathlib's
  `exists_norm_eq_iInf_of_complete_convex`), which the docstring says. The statement is then wider
  than the plan row: the module review's verdict is GENERALIZED, said in the docstring, round 69 and
  the report. If Dustin vetoes this ruling, keep the hypothesis as `_hKc`, leave the statement as the
  draft has it, and the verdict is FAITHFUL.

## Scope

- **Branch.** `lean-33` from `04e4a38` in `~/lean/classical-lean-paper-crypto`, made after Dustin
  approves your plan. Nothing pushed. No sudo.
- **You may change in the repository:** the seven home modules above, and in them only: new
  declarations inside the namespace block (the Goal list); the two import lines named; witnesses
  after the last line (rule 5); in LikelihoodScore, lines 399 to 471 replaced by rows 7 and 8's
  new blocks (blank line 472 kept). Also `tools/vacuity_reviewed.txt` (rule 4 only), `records/`, and `HANDOFF.md` sections
  1 and 4 and `ROADMAP.md` (job 4).
- **You may not change:** any other module, any existing declaration of the seven (the type dump
  checks it), any other import line, `ClassicalLean.lean`, anything else under `tools/`, `.github/`,
  `records/rules.toml`, the lake files, `HANDOFF.md` section 6 (its drift check hashes the text
  outside the generated block too). Needing to is a stop: report it.
- **You may write in the lane:** the plan, the report and the push-review file through `ds_file`;
  rows from 163 in the bridges file (job 5b). Nothing else.
- **Off limits:** the main clone `~/lean/classical-lean` and its `master`; `~/break-it-5`;
  `~/trading`; `~/lean/recheck` (`run-recheck.sh` is run as gate 7, not edited); Dustin's
  `~/.config/classical-lean/banned-terms` (the scanner reads it; never print or copy it); every
  GitHub branch (no push, no delete), above all `cloud-math-3`, which a cloud session is writing;
  `/data/api-credit/` (read only); `~/api-credit/` and `/tmp/claude-ai-*/` (claude-ai's).
- **The night window and the memory cap,** as LEAN-32's `ev.sh` enforces them (its header names the
  window; rule 36: name the window, do not copy its times). Before each whole-library run, log
  `pgrep -a lean` through `ev.sh --nolean` (rc 1 when none runs) and wait while another Lean process
  runs; reviewers run no
  Lean while you do. claude-ai starts no Lean run on DSMain while this session runs, unless Dustin
  says so. Start gate 7 only when it can finish
  before the midnight timer (about 21 to 22 minutes in MERGE-1 and MERGE-2). Every whole-library run under
  `ev.sh --cap` or `rootrun.sh`; never two Lean runs at once; read `crontab -l` and
  `systemctl --user list-timers` before you start; `~/.elan/bin` on `PATH`.

## Check, then read

Check these sha256s first; if any differs, stop and say which:
- this order, `lean/LEAN-33/order.md`: the value in Dustin's prompt;
- `lean/LEAN-33/scripts/TypeDumpPI.lean`, `lean/LEAN-33/scripts/g8-typediff.py`,
  `lean/LEAN-33/data/w9-10.lean`, `lean/LEAN-33/data/w67.lean`: the values above;
- `lean/MERGE-2-order.md` `81894b5bc85a6ee6858f7a1d8b065ee17ff5034f21df9ef68803cded13e4251a` (the
  DSMain pattern this order follows for setup, gates and push review);
- `lean/CLOUD-MATH-3-order.md` `dfe8e5a96158f915e30cf856620410daa9ed28bdfa8d66eccb9b73e946a44dd7`
  (the pattern for landing drafts; its rules 1 to 9);
- `lean/VACUITY-3-ruling-3.md` `aa0d17e403031b81d0e0803c3308002ed985b416d788980de0f61cc79e13a4f2`;
- `lean/CLOUD-LANDING-PLAN-2.md` `26da22cef5604286b2b4b8fdfed4ec9fd70fb5c8520cb5dbfcd7b5c8411051a5`;
- MATH-PLAN-library-2.md `6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166`;
- `lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md`: the value above;
- the six carry files in `/data/api-credit/20261019/carry/`: `d111-r1-s2.lean`, `d112-r1-s2.lean`,
  `d1116-r1-s1.lean`, `d117-r1-s2.lean`, `d134-r1-s1.lean`, `d3005-r1-s2.lean`: the values above;
- the helpers and census tails above, and the seven modules at `04e4a38` above.

Then read: in the repository `records/README.md`, `HANDOFF.md` sections 1, 4 and 6 (all 21 rules),
the seven home modules in full, round 67's fragment, and MERGE-2's and CLOUD-MATH-2's INDEX and
CLAIMS rows (the pattern for yours); in the lane the two orders named above (MERGE-2's Setup and
Job 4; CLOUD-MATH-3's rules and jobs 1 and 2), VACUITY-3-ruling-3.md, CLOUD-LANDING-PLAN-2.md
rulings 2, 3 and 5, MATH-PLAN-library-2.md section 7's rows 111, 112, 116, 117 and 134, and the
bridges file's last section; the six carry files and the two witness files in full.

## Rules of this order

1. **Statements as drafted.** Each main theorem keeps its draft's statement, apart from the Goal
   list's changes and the move into its namespace. Never weaken, restate or add a hypothesis to make
   anything easier. A statement you find false is reported with its counterexample and narrowed,
   said plainly in its docstring, round 69 and the report; never dropped silently.
2. **Namespaces and imports.** Every new declaration, private ones included, sits inside its home
   module's namespace block; the axiom gate checks only constants under `ClassicalLean`. Only the
   two import lines named in the Goal list are added; no other import line anywhere changes.
3. **No existing declaration changes** (HANDOFF rule 14). A type dump of the whole library
   (`TypeDumpPI.lean`, through `rootrun.sh`, because it imports `ClassicalLean`) at the records
   commit and again at G (rule 7), compared by `g8_typediff.py diff`, read by its `DIFF` line (its
   exit code is 0 whenever nothing is CHANGED, even with REMOVED lines): predicted `removed=0
   changed=0 proof_only=0`, and `added=` the new constants (job 3). A `REMOVED` or `CHANGED` line is a
   stop. A `PROOF-ONLY` line is listed and explained as rule 14 says, and reported as a miss of this
   prediction: claude-ai measured the two import lines alone and they give none. A difference between
   `added=` and job 3's list confined to auxiliary names is listed and explained, not a stop. A new
   warning in an existing declaration is a stop (Scope). Rows 7 and 8's swap removes two `example`
   blocks, which are not constants, so it does not show.
4. **The vacuity gate as the repository has it.** A flag or an UNCHECKED verdict on a main theorem
   makes that item not closed (rule 9). On a helper: rewrite it, remove it if Mathlib or `simp`
   already does its job, or list it in `tools/vacuity_reviewed.txt` as HELPER with a one-line reason
   its module's reviewer checks. A VACUOUS-PENDING entry makes the item not closed.
5. **Witnesses** in HANDOFF section 4's form (rule 2's form: `example := Full.name (x := …) h₁ h₂ …`,
   every chosen argument by name, optional `open … in` lines of their own and no other `open` than
   the module's top-level ones, the docstring "The hypotheses of `name` hold together: …", none of
   the six forbidden words, one inline block with no helper declarations; not degenerate as rule 3
   and VACUITY-3's ruling 3 say). Ten blocks in all:
   - five new ones, one for each item's main theorem. Hints (claude-ai's reviewer worked them out;
     check them, they are not measured): 111 in Kantorovich, a 2 × 2 matrix with `m < M` and a start
     that is not an eigenvector (Kantorovich's examples at lines 210 and 219 are `∃` forms inside the
     namespace, not rule-2 witnesses; take only their matrices); 112 in GradientDescent, `f = y²/2` on
     `ℝ` with `L = 2`, `μ = 1`, `f* = 0`, so the step `1/L` halves `x` and the factor `1 − μ/L = 1/2`
     (with `L = 1` every iterate after the first is `0`, and `μ = L` makes the factor `0`: both
     degenerate); 134 there, the same `f` with `L = 2`, `K = Icc (1/4) 1` and `x 0 = 1`, so the
     iterates are `1, 1/2, 1/4, 1/4, …` and the projection acts (a `K` holding every gradient step
     meets `hx` only because both sides are `0`); 116 in ExponentialWeights, `Fin 2` or more, `η ≠ 0`
     and losses not all equal; 117 in ConvexConjugate, a `p` in the open simplex that is not uniform;
   - rows 7 and 8: the carry's two blocks in place of lines 399 to 471, their 8 four-flag warnings
     fixed in the proof only, and their docstrings put in rule 2's form ("The hypotheses of `name`
     hold together: two genuine fair coins …"; the carry says "hold together with two genuine fair
     coins: …");
   - rows 9 and 10: `w9-10.lean`'s two blocks after EffectiveSampleSize's last line;
   - row 67: `w67.lean`'s block after GlivenkoCantelli's last line.
   Log `date +%s` through `ev.sh` when you start each of the five new witnesses; one still missing
   1800 seconds later makes its item not closed. The five supplied blocks are checked like any
   witness: they are starting material, not exempt.
6. **Records.** As `records/README.md` says. The records-first commit: this order's copy, its INDEX
   row (`| LEAN-33 |`) and CLAIMS row at the bottom, and round 69's fragment naming the seven module
   files by full path. **Do not touch MERGE-2's INDEX and CLAIMS rows:** records/README.md rule 2
   gives the next order's records commit MERGE-2's push, and CLOUD-MATH-3's records commit on its
   branch carries it, so the push is recorded once; the later merge of the two branches takes that
   side for those rows and appends LEAN-33's rows after it (both branches append rows at the bottom of
   INDEX and CLAIMS, so those files conflict anyway, as MERGE-2's trial (b) showed). Say so in round
   69, and name there and in the report the other places the later merge must handle:
   `tools/vacuity_reviewed.txt` (if a helper is listed), ROADMAP.md section 1.26, HANDOFF.md section
   1's last paragraph.
   Round 69's fragment gives each module's theorem-constant count from the census (rule 27) and gets
   its commit hashes in a follow-up edit once they exist, never predicted.
7. **Predict, then measure; the tree that counts.** As MERGE-2's rules 4 to 6: an evidence folder
   `~/lean/lean33-checks/` with `evidence.log`; every prediction file hashed into the log (`hl.sh`)
   before its run; hashes in records and the report by script, never typed; git, hash and records
   commands as `ev.sh --nolean`; every commit through `ev.sh --nolean` as `git commit -F <message
   file>` with a label starting `commit-`, then `COMMIT <hash>` appended to `evidence.log`; a helper
   you must run after generating a message's `Evidence:` line, and before its commit, takes a label
   starting `commit-`. Every gate runs on the clean tree of the last commit that touches anything
   outside `records/` (call it G); later commits touch only `records/`.
8. **Reviews.** Job 1's statement review, then five cold reviews once their text is final: (a)
   Kantorovich (111), (b) GradientDescent (112 and 134), (c) ExponentialWeights (116), (d)
   ConvexConjugate (117), (e) the witnesses of rows 7, 8, 9, 10 and 67 (three modules), each by a
   fresh subagent that has not seen your work, with a brief built by script as rule 26 says. Each
   brief caps its reviewer at 40 tool calls; at the cap it writes what it has and lists what it did
   not check, and anything listed as not checked gets a fresh reviewer for those parts only before
   the commit. A module review checks each statement against its plan row (FAITHFUL, GENERALIZED or
   WEAKER; WEAKER is a finding), every hypothesis used, each witness against rule 5, every new
   declaration in the namespace, the import lines, every private helper's statement, and no main
   theorem whose conclusion is a recursive predicate that is `True` everywhere. A review with
   findings ends with a confirming pass on the fix only, by a fresh reviewer. At most two
   fix-and-confirm rounds; an item not clean after two is not closed.
9. **Not closed.** An item not closed is undone by a new commit (never a reset): its declarations,
   witness, import line and vacuity-list entries removed, and round 69, the CLAIMS row and the report
   saying which item and why. The others go on. A witness row not clean after two rounds is undone
   the same way: rows 7 and 8 by restoring the old `N = 1` blocks, rows 9, 10 or 67 by removing their
   blocks; round 69, the section 4 line (job 4) and the report say so.
10. **Master does not move under you.** If `origin/master` or GitHub's `master` is not `04e4a38` at
    "Before approval" or when you write the push-review file, stop and report: claude-ai then writes
    the merge step. Never merge or rebase anything yourself.

## HANDOFF's rules in this session

Every rule of `HANDOFF.md` section 6 applies. How, for this order:

| rule | here |
|---|---|
| 1, 2, 3, 10, 15, 18, 19, 22, 28 | as written. Rule 19: credit each proof to its draft (the API-credit pipeline's Claude Opus 5.5 through the Anthropic Batch API, lean/API-CREDIT-CARRY-1.md), adapted by this session; rows 9, 10 and 67's blocks to claude-ai, adapted from LEAN-31's and LEAN-32's witnesses. Rule 22: every quote in round 69's fragment is checked by a script with a planted misquote (CLOUD-MATH-2's `quotecheck.py` may be adapted). |
| 12 | Reviewers work in `~/lean/lean33-checks/reviews/<label>/`, outside the repository, with `PYTHONDONTWRITEBYTECODE=1`, copy any repository script before importing it; `git status --porcelain` unchanged after each review; the tree is not touched while a reviewer runs. |
| 14 | Rule 3 above: the type dump at the records commit and at G, by the copied pair, after its controls (Setup 5). |
| 17 | Each reviewer writes its report to a file and returns only its sha256; you hash the file with `hl.sh` and compare before you open it. |
| 20 | Scratch files and modules are elaborated by `el.sh` (it carries the four flags); linter results count only from `lake build`. |
| 23 | `ev.sh` and `hl.sh`, tested in Setup 2; records files written with Write or Edit are hashed with `hl.sh` before their commit. |
| 26 | Every review brief is built by a script from `HANDOFF.md`, saved with its sha256 before it is sent, and quotes verbatim rules 14, 17, 18, 19, 20, 22, 23, 26 and 31, cut only with `[...]`; briefs (b) to (e) also quote HANDOFF section 4's "Satisfiability witnesses" paragraph verbatim. Use CLOUD-MATH-2's `mkbrief.py` (git history, above), tested in Setup 2; LEAN-31's `mkbrief.py` and `mkconfirm.py` may quote rules by their old numbers. |
| 27 | Theorem-constant counts, total and per module, from `mkcensus.sh` with the census tails on scratch copies of each final module, before any gate; the job count from `env.header.moduleNames` of a scratch file importing the seven modules, against the same at the records commit (predicted equal, so 4188 stands). |
| 31 | Job 1's statement review is in before any landing; every new declaration, private helpers included, gets its module's cold review before its commit; a review fix that touches a proof line gets its delta check (re-elaborated with `el.sh` and the module rebuilt through `ev.sh`) before its commit. |
| 36 | Briefs and predictions carry a date beside every clock time; each brief gives the dated end of its own run; `briefcheck.py` passes every brief before it is sent. Witness time limits in epoch seconds. |
| 37 | `el.sh` refuses a run while a name is not probed: one probe file per draft and one for the witness blocks, `#check @Name` lines for every Mathlib and library name in the text as it will land, run with `EL_PROBE=1`. |
| 38 | `rootrun.sh` for the type dumps, the bridge search, the report tool and any census that imports `ClassicalLean`; tested before first use (Setup 2). The gates are not wrapped. |
| 39 | Stage by path. A commit message is written after its gates ran, says only what `evidence.log` shows, names in its first paragraph any linter or option switched off or on, and ends with the line `evcite.py` prints, generated last, followed only by the session's attribution trailers. Job 5e runs `citecheck.py`. |

## Before approval (read-only in the repository)

1. `git fetch origin` in the worktree. Then, each predicted and checked: `origin/master` and
   `git ls-remote github master` both `04e4a3842055026616256cf549ded9bf4bcfdd96`; `git status
   --porcelain` empty. If not, stop (rule 10).
2. Check the hashes and read the read list.
3. Check `crontab -l`, `systemctl --user list-timers` and `free -g`.
4. Write your plan with `ds_file` (project `lean`, job `LEAN-33`, kind `plan`): the jobs in order,
   every prediction you can make now, the order of the items (a suggestion: 117 and 111, the
   shortest; then 116; then 112 and 134 together; then the witness rows), and the plan-fit check:
   for each item its plan row beside the draft's statement, every difference named (at least: 134's
   `hKc`; 112's hypothesis forms against the plan's `‖∇f‖²/2 ≥ μ (f − f*)`; 116's and 117's
   simplex conditions). Then stop and wait for Dustin's approval.

## Setup (after approval)

1. **The helpers.** Make `~/lean/lean33-checks/scripts/` and `~/lean/lean33-checks/census/`. One
   script copies the helpers and census tails above after comparing all 64 characters of each
   source hash, and changes only: the one `D=` line of `ev.sh`, `hl.sh`, `rootrun.sh`, `el.sh` and
   `mkcensus.sh`, and the one `D = ` line of `probecheck.py`, from `lean32-checks` to
   `lean33-checks`; in `probecheck.py` also the one line `BASE = '8071e74'` to
   `BASE = '04e4a38'`; in `el.sh` also the one `$D/hl.sh` to `$D/scripts/hl.sh`; in `evcite.py` the
   path on its two lines; each refused unless the file has exactly that many such lines (the comment
   lines that still name `8071e74`, `el.sh` line 5 and `probecheck.py` line 9, stay; say so in the
   plan). `citecheck.py`, `briefcheck.py`, the census tails and `allowlist.txt` (into
   `~/lean/lean33-checks/`) byte for byte. LEAN-32's `seed.txt` is not copied (your own probes seed
   the check; `probecheck.py` skips a missing seed file). You may add to `allowlist.txt` a tactic name
   `el.sh` refuses (a token that is not a constant), with a reason; `el.sh` logs the list's new hash.
   LEAN-31's `mkbrief.py` and `mkconfirm.py` are not copied: every brief, the confirming passes'
   included, is built by CLOUD-MATH-2's `mkbrief.py` and `filltask.py` from git history (above),
   adapted to this order's paths. Copy the four lane files into
   `~/lean/lean33-checks/inputs/` (`g8-typediff.py` as `g8_typediff.py`) and check their sha256.
   Log every new sha256 with `hl.sh`. Then write `pred-setup.md` and hash it.
2. **Tests before first use,** each logged and predicted: MERGE-2's Setup 2 (the empty-prediction
   refusal, exit 97; `ROOTRUN_BUILD=false rootrun.sh` refused, exit 95, the command not run; the
   real-build `rootrun.sh` test, its build line before its command line at the same head; the
   citecheck planted pair on a scratch copy of the log, plus a third case with a `commit-…` helper
   line between the `evcite.py` run and the `COMMIT` line, predicted `OK`); `el.sh` refusing a
   scratch file that uses an unprobed name (logged `NOT RUN`), then running it after its probe, and
   the allowlist's hash logged on its first run and not again on its second; `briefcheck.py` refusing a planted brief line with a
   time and no date; the brief builder printing a brief that quotes the nine rules of rule 26
   verbatim and passes `briefcheck.py`. A test that does not behave as predicted is a stop.
3. **Branch.** First, through `ev.sh --nolean setup1 …`: `git fetch origin`; `origin/master` and
   `git ls-remote github master` both `04e4a38…`; `git status --porcelain` empty (rule 10). Then
   `git switch -c lean-33 04e4a3842055026616256cf549ded9bf4bcfdd96`.
4. **Records first,** one commit, no `.lean` file (rule 6):
   `records/orders/<UTC>__claude-ai__order-lean33-steepest-pl-mirror-conjugate-projected-witnesses.md`,
   the INDEX and CLAIMS rows, and round 69's fragment
   `records/rounds/<UTC>__round-69-steepest-pl-mirror-conjugate-projected-witnesses.md`.
   check_records then: PASS 135.
5. **Before runs at the records commit,** predicted from the facts: build rc 0, 4188 jobs, 0
   warnings; AxiomGate PASS 3458; the type dump,
   `rootrun.sh td-before "<pred>" lake env lean ~/lean/lean33-checks/inputs/TypeDumpPI.lean`, whose
   `td-before.out` ends with `/usr/bin/time -v`'s report: keep its lines that start with `{` in
   `td-before.jsonl` by a script run through `ev.sh --nolean`, and check that every dropped line is
   time's report; then `g8_typediff.py check td-before.jsonl`: rc 0, 3930 records (3458 `thm`, 472
   `def`), elided 0, missing_fields 0. Then the diff tool's controls on copies of
   `td-before.jsonl`, each predicted and read by its `DIFF` line: the file against itself, all zeros,
   rc 0; one record's `ppPI` edited, `changed=1`, rc 1; only its `pp` edited, `proof_only=1`, rc 0;
   one record deleted, `removed=1`, rc 0 (the exit code does not catch it; the `DIFF` line does).

## The work

### Job 1: statements and their review

1. Probes (rule 37): one file per draft and one for the five supplied witness blocks; each new
   witness's names are probed before it is written. CLOUD-MATH-2's `mkdiscover.py` and
   `mkprobes.py` may be adapted.
2. For each draft, a scratch statement file outside the repository that imports its home module
   (and Entropy for 116, LogSumExp for 117), repeats the module's top-level `open` lines, and holds
   `namespace <home namespace>`, the draft's declarations as they will land with every theorem's and
   lemma's proof `sorry`, and `end`; the statement files for 116 and 134 keep the draft's `variable`
   line (d1116 line 14, d134 line 13), since a module's `variable` lines do not reach a file that
   imports it (only the landed module drops them). So `el.sh` reads only the new text (it reads a scratch file
   whole), and the full names are the ones the module will have. Elaborate each with `el.sh` (rc 0,
   only `sorry` warnings); hash them. Scratch files for work on a witness likewise import the module
   and hold only the block.
3. A mechanical check that the move changed no meaning: for each main theorem, its type printed
   with `set_option pp.fullNames true in #check @name` from the draft (a scratch copy with the line
   appended) and from the statement file, compared by a script (CLOUD-MATH-2's `typecmp.py` may be adapted): only the namespace prefix
   may differ, besides the Goal list's change for 134. Log the result.
4. One statement review of the five, by one fresh subagent (each statement against its plan row
   and its draft, the Goal list's changes, the namespaces, the two import lines). Its verdict is in
   before job 2.

### Job 2: land, one commit per module

In the plan's order, per module: the declarations in place (the Goal list), the import line if
any, the witness; `el.sh` on the module (rc 0); `lake build` of the module and of every module that imports it
(Kantorovich: Statistics.GeneralizedLeastSquares; GradientDescent: Analysis.FrankWolfe and
Analysis.EulerMethod; ExponentialWeights: Analysis.FiniteGame; LikelihoodScore:
Probability.NoEdgeWealth; the others none) through `ev.sh` (0 errors, 0 warnings);
`python3 -I tools/banned_vocab_scan.py ClassicalLean` (the form every earlier order used; the
credit wording as CLOUD-MATH-2's modules have it, which passed MERGE-2's scan with 0 hits); the vacuity gate and the check scripts (a copy of the vacuity gate whose only
change is its import line may run on one module while the root is not rebuilt; the real gate runs
in job 5a); the module's cold review (rule 8) with any fix and its confirming pass; one commit
staged by path, then its `COMMIT` line. Then the witness rows (7 and 8 in LikelihoodScore, 9 and 10
in EffectiveSampleSize, 67 in GlivenkoCantelli) the same way, with review (e), in one commit.

### Job 3: predictions

Once every module's text is final (after the reviews) and before job 5: a prediction file, hashed,
with the job count (rule 27's closure measurement); the theorem constants by census (base 3458 plus
the census of each final module's new constants, per module: `mkcensus.sh` on a copy of each
changed module at `04e4a38` and on its final copy, the new constants being the difference of the
two `.names` lists); the type dump's `added=` list, the difference of the two census-all lists for
the changed modules (the dump keeps only `thm` and `def` constants, so a name of another kind in
that difference is listed as an expected absence, and private names are compared by their
user-facing names, `privateToUserName`, because the census runs on copy files whose module name
differs) (rule 3); check_sorry and check_records PASS 135; the vacuity gate's verdicts and reviewed-helper
count, and its tests (MERGE-2's "89 tests, 47 flagged, 0 rule-5 run-outs, 0 mismatches");
`banned_vocab_scan.py ClassicalLean` PASS, 135 files and the root file, 0 hits; gate 7 ALL PASSED,
4188 jobs, 135 modules 0 failed, 3458 plus the census count, the three standard axioms, the planted
fault named; the drift check PASS; the bridge search's and report tool's numbers by hand from
MERGE-2's runs (say they are hand predictions); the records-file count. Until then do not run the axiom gate on
the changed modules. A miss is reported, never fixed by changing what was measured.

### Job 4: documents

- `HANDOFF.md` section 1: after MERGE-2's paragraph, a dated LEAN-33 paragraph (round 69): the five
  items by name, module and item number, one line each, 134's wider statement said; rows 7 and 8
  re-witnessed, rows 9, 10 and 67 witnessed; the counts predicted by job 3, to be re-measured by job
  5a.
- `HANDOFF.md` section 4, the "Satisfiability witnesses" paragraph: a dated line (2026-10-21 UTC or
  the day you write it) saying rows 9, 10 and 67 are now witnessed (by this order, with how), rows 7
  and 8 re-witnessed with `N = 2`, and the older rows' forbidden-word exception no longer used by
  rows 7 and 8. Change nothing else in section 4. Section 6: no change at all.
- `ROADMAP.md`: after section 1.25, a section 1.26 for items 111, 112, 116, 117 and 134 and the
  witness rows, landed from below the plan's cut by order LEAN-33, in section 1.25's form.
- One fresh cold reviewer reads the documents commit's diff alone (about 15 calls); a review with
  findings ends with a confirming pass on the fix only (rule 8).

### Job 5: the end checks, in this order

- **5a. The gates,** on the clean tree at G, each through `ev.sh` with its prediction, in MERGE-2's
  forms (its job 4a): build, AxiomGate, VacuityGate, the vacuity tests, check_sorry, check_records,
  the drift check, `banned_vocab_scan.py ClassicalLean`, and gate 7. Then the type dump at G through
  `rootrun.sh` as in Setup 5, its `{` lines kept in `td-after.jsonl` and the dropped lines checked,
  `g8_typediff.py check td-after.jsonl`, then `g8_typediff.py diff td-before.jsonl td-after.jsonl`
  (rule 3). A gate that fails
  is a stop: 5b and 5c do not run.
- **5b. The bridge search,** through `rootrun.sh`, at G:
  `python3 -I tools/bridge_search.py --diff records/bridges/MERGE-2/ --out ~/lean/lean33-checks/bridges/LEAN-33`;
  rc 1 means candidates to review. Report NEW and GONE pairs and shapes. Check each NEW import-unrelated pair and each NEW shape for
  a theorem whose proof needs both sides; a real one is appended to the bridges file from row 163,
  through `ds_write_staging` in append mode with `expect_sha256` its value above (as LEAN-32
  appended; if the write is refused, stop and report), in the file's columns. Say in the file and the report exactly
  how the pairs were checked: which were read statement by statement, and how the rest were judged
  (plan 2's ruling 5). Write the new baseline to `records/bridges/LEAN-33/`; its commit touches only
  `records/`.
- **5c. The report tool,** through `rootrun.sh`, at G, once; a report, not a gate; predicted by
  hand from MERGE-2's `report.out`. List every
  `CLOSES` line that names a theorem of this order.
- **5d. Close the records:** round 69's follow-up edit with the commit hashes and the measured
  counts, its quotes checked by script (rule 22); the CLAIMS row closed and the INDEX row's state
  set; one records-only commit. Then check_records again at the final HEAD, predicted PASS 135.
- **5e. citecheck:** every commit of this order, `git rev-list 04e4a38..HEAD`, by
  `citecheck.py ~/lean/lean33-checks/evidence.log --message <its message file> <hash>` in one loop
  (the message from `git log -1 --format=%B <hash>`; each `OK`), and the repository run `citecheck.py ~/lean/lean33-checks/evidence.log
  ~/lean/classical-lean-paper-crypto 04e4a38` (predicted rc 0, every commit `OK`).
- **5f. Report** with `ds_file` (kind `report`), laid out like MERGE-2's report: in short; setup and
  the helper tests; for each item its final statement, witness and review verdicts; the witness
  rows; the type-dump diff; predicted beside measured for every gate and count; the bridge diff and
  how it was checked; 5c's `CLOSES` lines for this order (or "none"); the commits; 5e's output;
  misses and anything not closed; and the push command as one line, not run:
  `cd ~/lean/classical-lean-paper-crypto && git push origin lean-33:master && git push github lean-33:master`.
  Say that the GitHub push starts a CI run on `master`, and that Dustin runs it only after
  CLOUD-MATH-3's cloud session has ended and claude-ai has said so (that session checks master is
  unchanged at its end).
- **5g. Push-review file** with `ds_file` (subdir `data`, name `LEAN-33-push-review.txt`), by one
  script, each command followed by its full output: `git rev-parse HEAD`, `git status --porcelain`,
  `git ls-remote origin master`, `git ls-remote github master` (both must still be `04e4a38`, rule
  10), `git merge-base --is-ancestor 04e4a38 HEAD` with its exit code, `git rev-list --count
  04e4a38..HEAD`, `git log --name-status --format='== %h %cI %s' 04e4a38..HEAD` (files under
  `records/bridges/` as a count), `git diff --stat 04e4a38 HEAD`, `git diff --name-only 04e4a38 <G> --
  ClassicalLean.lean tools .github ':(glob)lakefile*' lake-manifest.json lean-toolchain
  records/rules.toml` (predicted: only `tools/vacuity_reviewed.txt`, if a helper was listed),
  `git diff --name-only 04e4a38 <G> -- ClassicalLean` (predicted: exactly the seven modules),
  `git diff -U0 04e4a38 <G> -- ClassicalLean | grep '^[-+]import'` (predicted: exactly the two
  import lines), the type-dump `DIFF` line, `git diff --name-only <G> HEAD` (only `records/`), 5d's
  output and 5e's two outputs. Report its sha256. Then stop: claude-ai reviews it before Dustin
  pushes.

## Done means

- Branch `lean-33` from `04e4a38`, clean tree, nothing pushed; its first commit is the records
  commit and holds no `.lean` file; then one commit per module and one for the witness rows; then
  documents; then records-only commits.
- The helpers copied, their sha256s logged, their tests run before first use as predicted.
- The five items proved with no `sorry` and no new axiom, as drafted with the Goal list's changes,
  or each narrowing said plainly, or reported not closed and undone by rule 9; 134 GENERALIZED and
  said so.
- Ten witnesses in rule 2's form, each checked by its review against rule 5.
- The type-dump diff `removed=0 changed=0`, and `proof_only=0` or each PROOF-ONLY record listed and
  explained (rule 3); its `added=` list equal to the census's new
  constants, apart from differences listed and explained under rule 3 and job 3.
- Job 1's statement review and the five module reviews and the documents review saved and
  hash-checked, each ending in a confirming pass where it had findings.
- Every gate as predicted at G, or each miss reported; gate 7 ALL PASSED at G; after G only
  `records/` changed; check_records PASS at the final HEAD.
- The bridge diff reported with how it was checked; real bridges (if any) from row 163; the new
  baseline committed.
- Job 4's documents changed and named (section 6 untouched; the drift check passes).
- 5e: every commit `OK`.
- The plan and the report in `lean/LEAN-33/`, the push-review file in `lean/LEAN-33/data/`, hashes
  matching yours.

Then report in a few plain sentences: what was proved, 134's wider statement, the witnesses, the
gate results beside the predictions, any new bridge, the two files' hashes and the push command.
Dustin reads your replies carefully and is still learning to read code: plain words, and define a
technical term the first time you use it. When you need a decision from him, ask in one line with
your recommended answer first.

## Not in this order

- Merging `cloud-math-3`, or anything about CLOUD-MATH-3's session (MERGE-3, claude-ai's, later).
- VACUITY-3 rows 31, 32 and 70 (batches 4 and 6: LEAN-34 and LEAN-36); plan rows 119 and 120.
- Bridges 160 to 162 and the pair-by-pair read of MERGE-2's search (LEAN-38, plan 2 ruling 5).
- Deleting GitHub branches; any push.

## Revisions

- r1, review pass 1: MAJOR: claude-ai measured the two import lines alone (build 4188 jobs, 0 warnings; type dump all zeros), and rule 3 now reads the `DIFF` line and treats PROOF-ONLY as rule 14 does; the push waits for CLOUD-MATH-3's session to end (it checks master is unchanged); `el.sh`'s and `probecheck.py`'s other inputs measured and handled (the base commit, the missing `$D/hl.sh`, the allowlist); witness hints that avoid degenerate cases for 112 and 134; the type-dump controls moved after the before dump exists. MINOR: ConvexConjugate's example count; rows 7 and 8's range (399 to 471, blank 472 kept) and docstring form; rule 6's reason and the later merge's other spots; the scripts named with their hashes and one brief builder chosen; the bridge search's exit code and append tool; the dump's command and `/usr/bin/time -v`'s trailing report; `added=` against the census; the citecheck `commit-` case and message files; job 3's missing predictions; no before-run of the report tool; importers built and the banned scan in job 2; new witnesses probed first; rule 10 repeated before the branch; a not-closed rule for the witness rows; a fallback if Dustin vetoes 134's ruling; no overlapping Lean runs; the drafts' module docstrings and the modules' `variable` lines; the push-review path and diff; a confirming pass only after findings.
- r2, review pass 2: MAJOR: job 1's statement files import the home module and hold only the new text, so `el.sh` checks only that. MINOR: `seed.txt` (skipped when missing, measured) and the allowlist (may be extended; hash logged once); `added=` from base and final census lists; td-after filtered like td-before; Done-means follows rule 3; the measured replacement described as run; comment lines naming `8071e74`, the banned scan on `ClassicalLean`, `pgrep`'s rc 1; LEAN-31's `mkbrief.py` and `mkconfirm.py` no longer copied.
- r3, the confirming pass: the statement files for 116 and 134 keep the draft's `variable` line; private names compared by `privateToUserName`; Done-means names rule 3's and job 3's allowances; the blank line in the measured copy attributed to `gather2.sh`.
