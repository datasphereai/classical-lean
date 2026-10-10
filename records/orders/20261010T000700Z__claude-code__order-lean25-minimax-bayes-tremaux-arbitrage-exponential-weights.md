<!-- Written on 2026-10-10 (UTC) by Claude Code session_01Y8vMKHokSopC3taexkCYny on DSMain, from the plan /opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md (sha256 c73957af6a9f2d19aacfd3acfc1d42d9a2a124fabefae62bbfee026090422898, checked by sha256sum before this file was written; equal to the hash the order expects), as Dustin ordered in chat on 2026-10-09. Batch 9 of the plan and the order are copied verbatim below. Written before any module was changed, per records/README.md rule 2. -->

# LEAN-25: von Neumann's minimax theorem, Bayes equals minimax, Trémaux's rule, no gain around a cycle with Bellman–Ford, and the game's value by exponential weights

## Goal

Batch 9 of MATH-PLAN-library (items 62 to 66), in one order (no split): five named results on games and graphs, proved in the library with no sorry and no axiom. The item numbers are the plan's.

Re-checked against Mathlib v4.34.0 (`5ed2965256`) before this file was written, as the order asks (`grep -rliE` over Mathlib; patterns, counts and first hits in the session's evidence file `~/lean/lean25-checks/search.out`): none of the five items is in Mathlib, so none is dropped or reduced. "minimax|Minimax" 4 files: Topology/Sion.lean (Sion's theorem, `Sion.exists_isSaddlePointOn`; its docstring lists "Spell out the particular case of von Neumann theorem" as still to do), Order/SaddlePoint.lean (`IsSaddlePointOn`), Probability/Decision/Risk/Defs.lean and Risk/Basic.lean (`bayesRisk`, `minimaxRisk` and the inequality `iSup_bayesRisk_le_minimaxRisk` only). "Tr.maux|depth.first|dfs" 18 files: the `order` tactic's internal search (Tactic/Order/Graph) and unrelated words; no theorem about exploring a graph. "Bellman|negative cycle|arbitrage|shortest path" 1 file, a docstring in Combinatorics/Quiver/Arborescence.lean. "exponential weight|multiplicative weight|hedge algorithm" 0 files; the library has ExponentialWeights (`sum_inner_softmax_le`), which item 66 uses. Library: no minimax, saddle point, Trémaux, Bellman–Ford or arbitrage result.

Trémaux's rule is pinned from a source this session read: Édouard Lucas, Récréations mathématiques, tome I, second edition, Gauthier-Villars et fils, Paris, 1891 (title page), Troisième récréation "Le jeu des labyrinthes", pages 47 to 51 ("Solution de M. Trémaux"), read in the Internet Archive scan `p1rcrationsm00lucauoft`.

## Scope

### Batch 9 — games and graphs (added 2026-10-09 by claude-ai; items 62 to 64 Dustin's yes, 65 and 66 his veto open; may split)

Searched 2026-10-09 on DSMain, Mathlib v4.34.0 (`grep -rliE`, files; library in brackets): "minimax|Minimax" 4 (Topology/Sion, Order/SaddlePoint, Probability/Decision/Risk/Basic and Risk/Defs) [0]; "Nash" 137, the hits sampled are the author Oliver Nash, no game equilibrium [0]; "Tr.maux" 0 [0]; "depth.first" two lines, both inside Tactic/TFAE [0]; "Bellman|negative cycle|arbitrage" 0 [0]. Mathlib proves Sion's theorem (`Sion.exists_isSaddlePointOn`) and `iSup_bayesRisk_le_minimaxRisk`, whose docstring says equality holds "in many cases (by a so-called minimax theorem)" without proving it. Re-check each by search before building.

| # | area | the result | Lean names | module | rests on | cost |
|---|---|---|---|---|---|---|
| 62 | 7, 10 | Von Neumann's minimax theorem for finite games: for every real `m × n` matrix `A`, the minimum over mixed strategies `x` of the maximum over `y` of `xᵀ A y` equals the maximum over `y` of the minimum over `x`, and both players have optimal mixed strategies. | `minimax_eq_of_matrix`, `exists_isSaddlePoint_matrix` | new ClassicalLean.Analysis.FiniteGame | Mathlib `Sion.exists_isSaddlePointOn` on the two probability simplices (compact, convex; the payoff is bilinear and continuous), `stdSimplex` | S–M |
| 63 | 2, 10, bridge | Bayes equals minimax for a finite decision problem: with finitely many parameters and actions and randomized rules, the largest Bayes risk over priors equals the minimax risk. Mathlib proves only the inequality. Ties the statistics of batches 4 and 8 to item 62. State it with Mathlib's `bayesRisk` and `minimaxRisk` if their definitions fit the finite case; otherwise state the matrix form and say exactly how it maps to theirs. | `iSup_bayesRisk_eq_minimaxRisk_of_finite` | ClassicalLean.Analysis.FiniteGame | item 62; Mathlib `iSup_bayesRisk_le_minimaxRisk` (Probability/Decision/Risk) | M |
| 64 | 10 | Trémaux's rule: in a finite connected graph, an explorer who marks passages as Trémaux's rule says (pin the exact rule from a checked source) visits every vertex, crosses every edge exactly twice, once each way, and returns to the start; the explorer's tree is a Trémaux tree (every other edge joins a vertex to one of its ancestors). The guarantee rests on the marks: the check script shows a case where one erased mark breaks "exactly twice"; if no such case is found, say so. | `tremaux_visits_all`, `tremaux_crosses_twice`, `isTremauxTree_of_tremaux` | new ClassicalLean.Combinatorics.Tremaux | Mathlib `SimpleGraph`, `Walk`, `Connected`; Mathlib has no depth-first search | M–L |
| 65 | 7, 10, bridge | No gain around any cycle, three ways: for rates `r i j > 0` after fees between finitely many assets, (a) every cycle's product of rates is at most `1`, (b) there are positive prices `p` with `r i j · p j ≤ p i` for every pair, (c) the weights `−log r i j` have no negative cycle; and Bellman–Ford's `n − 1` rounds then settle, so a further improving step exists exactly when some cycle gains. Use: a consistency check on prices from several sources; quotes that admit no `p` are stale, wrong, or a real gap. | `forall_cycle_prod_le_one_iff_exists_prices`, `bellmanFord_stable_iff` | new ClassicalLean.Combinatorics.ArbitrageCycle | Mathlib `Finset` sums, `Real.log`; item 64's graph setting; item 47 is the general form of (a) ⇔ (b) | M–L |
| 66 | 7, 10, bridge | The game's value computed by learning: with payoffs in `[0, 1]`, the row player running the library's exponential weights for `T` rounds against best responses gets averaged strategies that are within `√(log m / (2 T))` of optimal for both players, so the upper and lower values differ by at most that for every `T`. A constructive second route to item 62 for matrices, which yields near-optimal strategies, not only their existence. Ties ExponentialWeights to games. | `abs_value_sub_le_of_exponentialWeights` | ClassicalLean.Analysis.FiniteGame | library `sum_inner_softmax_le` (ExponentialWeights); item 62 | M |

Changed or added: three new modules, ClassicalLean.Analysis.FiniteGame (items 62, 63 and 66), ClassicalLean.Combinatorics.Tremaux (item 64) and ClassicalLean.Combinatorics.ArbitrageCycle (item 65); `ClassicalLean.lean` (three import lines).

Not in scope: batch 10 of the plan; offering anything to Mathlib; anything under ~/trading; any edit under ~/lean/recheck (its script is only run, as gate 7); any push; any sudo.

## Done-means

Dustin's order, verbatim:

LEAN-25 is batch 9 of the classical-lean library plan: items 62 to 66, games and graphs, in one order (no split). It continues LEAN-24 (batch 8), which Dustin pushed; origin and github master should both be ed64909.

The item numbers are the plan's. Use them in every commit message, record row and report line:
- 62: von Neumann's minimax theorem for finite games (new module ClassicalLean.Analysis.FiniteGame)
- 63: Bayes equals minimax for a finite decision problem (same module, rests on 62)
- 64: Trémaux's rule on finite connected graphs (new module ClassicalLean.Combinatorics.Tremaux)
- 65: no gain around any cycle, three ways, with Bellman–Ford (new module ClassicalLean.Combinatorics.ArbitrageCycle)
- 66: the game's value computed by exponential weights (same module as 62, rests on 62 and the library's ExponentialWeights)
Dustin's veto is still open on items 65 and 66 and he has not used it; build them as planned.

Setup
1. Run `sha256sum` on /opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md. I expect c73957af6a9f2d19aacfd3acfc1d42d9a2a124fabefae62bbfee026090422898 (measured a minute ago; the plan has 71 items in 10 batches, and section 9 now records the narrower item 56). If it differs, say so in your report.
2. Read, in the same folder: the plan (section 4 batch 9, section 5 searches, section 9), LEAN-24-report.md, MATH-PLAN-library-HANDOFF.md, and the "Known traps" section of LEAN-16-order.md.
3. `git fetch origin`. origin/master must be ed64909 and `git ls-remote github master` must agree. If not, stop and tell me. Otherwise branch `paper-crypto-20` from it.

The work
Follow the LEAN-19/LEAN-24 method:
- Re-check each item against Mathlib (v4.34.0) by search before building. If an item is already there, drop or reduce it and say so. For item 62, Mathlib has `Sion.exists_isSaddlePointOn`; for item 63 it has `iSup_bayesRisk_le_minimaxRisk` (only the inequality).
- Records first, in one commit: the order copy (new modules in dotted form only), the INDEX row, the CLAIMS row, and the next round fragment. check_records must still pass on the three new module paths.
- Write the statements with `sorry` first and elaborate them. Those sorries are scratch only and must be gone from the library before any commit that builds it.
- State each theorem exactly. Item 63: use Mathlib's `bayesRisk` and `minimaxRisk` if their definitions fit the finite case; otherwise state the matrix form and say exactly how it maps to theirs. Item 64: pin the exact rule of Trémaux from a source you checked (give author, title and year, and say which edition or page), say what "visits every vertex, crosses every edge exactly twice, once each way, and returns to the start" means as a Lean statement, and say what a Trémaux tree is. The plan asks for a case where one erased mark breaks "exactly twice"; if the check script finds none, say so. Item 65: state (a), (b) and (c) separately and the equivalences between them, and what Bellman–Ford's n − 1 rounds settle. Item 66: say what "best responses" and "averaged strategies" mean, and where the payoffs in [0, 1] are used.
- Write a dropped-hypothesis table with exact arithmetic where you can, and mind Lean's junk values (`x / 0 = 0`, `log 0 = 0`, empty infima and suprema, the integral of a non-integrable function).
- Build one module at a time, with one cold review per module by a fresh subagent that has a read list and a limit of about 40 tool calls. Items 62, 63 and 66 share a module: review it once at the end, and once after item 62 if that is large.
- Suggested order: 62, 63, 66, 64, 65, so the two M–L items come last. If a module can't be closed, stop at a clean point and say exactly what was not reached. A tool-call limit is never a reason to cut work short, because Dustin will press continue.

Rules for this order
- Citations: for a paper or book you did not read, give author, title and year only, and say nothing about what it contains.
- Keep the constant count honest. Today it is 2854 constants, 113 modules and 4133 build jobs. Predict the new count before any gate runs, by Method B (compile scratch copies of the new modules and count what they add), and make the prediction blind as in LEAN-24: write prediction.txt before any census, vacuity probe or gate runs on a new module. For Method A model the helpers by their measured rates in LEAN-24: `eq_N` lemmas for each definition, `_proof_` lemmas inside definitions that contain `by` terms (including `jamesStein._proof_1`, which was missed), `congr_simp` lemmas for definitions used under `simp`, and `_simp_` lemmas for `field_simp`, which varied from 0 to 8 per theorem, so give a range, not a rate. Reconcile any miss name by name.
- Predict the build job count as 4133 plus one per new module plus the new Mathlib modules your imports pull in; list the import closure of the environment for the old and new import lists, as LEAN-23 and LEAN-24 did.
- Run all six gates, then gate 7 as in LEAN-24: ~/lean/recheck/run-recheck.sh with your last commit and this repo's path (take the usage from the script's own header). Nothing may be edited under ~/lean/recheck.
- Nothing under ~/trading. No push. No sudo. Do not start batch 10.

Report
Write inbox/threads/staging/LEAN-25-report.md through ds_write_staging and compare post_sha256 with your own hash. Include: each item's result in one sentence, predicted beside measured, the hypothesis table, the commits, what was not reached, and the push command as one line, not run:
cd ~/lean/classical-lean-paper-crypto && git push origin paper-crypto-20:master && git push github paper-crypto-20:master
Then stop.

Dustin is still learning to read code but reads your replies carefully. Use plain words, define a technical term the first time you use it, and ask any decision in one line with your recommended answer first.

Sent with the order, verbatim:

taskcreate <3

Sent during the session, before this file was written, verbatim:

Ruling from Dustin's helper on item 66: state it as a result about strategies, not about the gap alone. For payoffs in [0, 1], the row player runs the library's exponential weights for T rounds against the column player's best responses. The averaged strategies x̄ (row) and ȳ (column) then satisfy
(max over y of x̄ᵀ A y) − (min over x of xᵀ A ȳ) ≤ √(log m / (2 T)),
for every T, with explicit x̄ and ȳ. A statement that only bounds the two values' difference follows from item 62 at once and is not item 66's worth.
Prove it without item 62 if the library's ExponentialWeights lemma (`sum_inner_softmax_le`) allows. If it does, say in the module docstring and the report that this is a second proof of item 62 (as T grows the gap goes to zero). If it can't be done without item 62, use item 62, and say plainly in the report that it is not a second proof and that the strategies are the new content. Either way, state in the dropped-hypothesis table where payoffs in [0, 1] are used (the bound has the constant 1/2 only because of that range). Carry on with the rest of the batch.
