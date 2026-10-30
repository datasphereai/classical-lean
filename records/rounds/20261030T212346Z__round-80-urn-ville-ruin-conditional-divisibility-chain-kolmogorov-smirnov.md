# Round 80 — Ville's inequality for Pólya's urn, the walk under a conditional up-chance, ruin and the divisibility of Lucas numbers, ruin by first-step analysis, the Kolmogorov–Smirnov statistic (order CLOUD-MATH-6)

Session: Claude Code cloud session `session_01HgueTbGvJvmksxSgWGMRPt`
(https://claude.ai/code/session_01HgueTbGvJvmksxSgWGMRPt), executing order `CLOUD-MATH-6`
(`records/orders/20261030T212345Z__claude-ai__order-cloudmath6-urn-ville-ruin-conditional-divisibility-chain-kolmogorov-smirnov.md`),
bridge rows 157, 154, 156, 165 and 159 of `MATH-PLAN-library-2-bridges-2.md`, in a cloud container's
clone of GitHub `datasphereai/classical-lean` on branch `cloud-math-6`, from
`8631a8d3c4316d85c78df697436b0245fa24cf1b` (checked equal to `origin/cloud-math-6` before any
change). `git ls-remote origin master` at the start: `8631a8d3c4316d85c78df697436b0245fa24cf1b`
(`$HOME/cm6/start-git.txt`). Lean and Mathlib v4.34.0 (`lake exe cache get`, 8908 files,
`$HOME/cm6/setup2-cache.txt`).

**No drafts.** Each of the five bridges is stated and proved by this session from its row's sketch
in the order; no proof comes from an earlier draft.

Evidence: `$HOME/cm6/` (outside the repository); every count below is read from a saved output
there, cited by its file name (rule 9).

First part written before any Lean file changed; completed after the work, below.

## Modules this round adds (five new modules)

* bridge 157: `ClassicalLean/Probability/UrnVille.lean` (`ClassicalLean.Probability.UrnVille`),
  importing `ClassicalLean.Probability.PolyaUrn` and `ClassicalLean.Probability.MaximalInequality`;
* bridge 154: `ClassicalLean/Probability/RuinConditional.lean`
  (`ClassicalLean.Probability.RuinConditional`), importing `ClassicalLean.Probability.GamblersRuin`
  and `ClassicalLean.Probability.LikelihoodScore`;
* bridge 156: `ClassicalLean/Probability/RuinDivisibility.lean`
  (`ClassicalLean.Probability.RuinDivisibility`), importing `ClassicalLean.Probability.GamblersRuin`
  and `ClassicalLean.NumberTheory.LucasApparition`;
* bridge 165: `ClassicalLean/Probability/RuinChain.lean` (`ClassicalLean.Probability.RuinChain`),
  importing `ClassicalLean.Probability.GamblersRuin` and `ClassicalLean.Probability.FiniteChain`;
* bridge 159: `ClassicalLean/Probability/KolmogorovSmirnov.lean`
  (`ClassicalLean.Probability.KolmogorovSmirnov`), importing
  `ClassicalLean.Probability.GlivenkoCantelli` and `ClassicalLean.Probability.IntegralTransform`;
* `ClassicalLean.lean`: five import lines, at the end of its import block, in landing order, each
  added by its module's landing commit.

No existing module changes. `tools/vacuity_reviewed.txt` changes only if a helper is listed (the
order's rule 4). Nothing else under `tools/` changes.
