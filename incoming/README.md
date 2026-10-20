# incoming/ (order CLOUD-MATH-2)

Written by claude-ai on 2026-10-19 for order CLOUD-MATH-2. Nothing here is part of the library:
`lake build`, the gates and CI read only `ClassicalLean/`, `ClassicalLean.lean` and `tools/`.
The whole folder is removed at the merge, after its report and reviews are copied to the lane.

## The five drafts

Each was written by Claude Opus 5.5 through the Anthropic Batch API (the lane's API-CREDIT-1 work),
except d151-r9-s1, written by a Claude Code session on DSMain (order CC-151) from an API draft.
Each compiled at master 9c0639c on DSMain on 2026-10-19 (claude-ai's recheck: rc 0, 0 errors,
every planned name present, axioms only propext, Classical.choice, Quot.sound), passed the
library's vacuity gate when it was drafted, and passed the library's banned-vocabulary scan
on 2026-10-19 (0 hits).

| item | file | sha256 | last cold review |
|---|---|---|---|
| 147 | `d147-r1-s2.lean` | `35ad76eed4ded4b84bbc7de34bca6a83d130a35920adbc547677270571748bea` | API-CREDIT-1 review r6: GENERALIZED |
| 150 | `d150-r1-s2.lean` | `697d4d16a6ab96b4afd1c3d0f1569bfe13b93222cb32110335a7eccf10c1cf09` | API-CREDIT-1 review r6: FAITHFUL |
| 151 | `d151-r9-s1.lean` | `341440925ce176af52249312e2ac227ea38e54c27731874e265e8d8b542b2cf8` | its own review (CC-151): FAITHFUL |
| 152 | `d152-r2-s1.lean` | `7da568e73227c96fe845fd268290f2131c58349a1632a1f84766710d8deaeec2` | API-CREDIT-1 review r6: FAITHFUL |
| 153 | `d153-r1-s2.lean` | `48df737e865c3e4148e29382348154f7a60badccb199f5a62e7229e73f89af2e` | API-CREDIT-1 review r6: GENERALIZED |

`d151-r9-s1-sat.lean` (`1fe654438b2bf7f7d337c2a98cf535516dfc38446bb85f9b35ab1a733f07c8a8`) is d151-r9-s1 followed by a satisfiability example that
claude-ai wrote and compiled on 2026-10-13 (at bf9922b): the hypotheses of
`hasLaw_sum_sq_gaussian` hold for the coordinates of the product of `k` standard normal laws.
It is starting material for item 151's witness, not a witness in the library's form (its `k` is
a variable, not a concrete value).

`d147-r1-s2-witness.lean` (`6e2f7024a042fdb128b2e58175d15a49d9cc695e9e67fc6479267cf9b5c69f71`) is d147-r1-s2 followed by an `example` that claude-ai wrote
and compiled on DSMain on 2026-10-19 at 9c0639c, with the four `-D` flags of HANDOFF rule 20
(rc 0, no `sorry`, no warning on its own lines): the hypotheses of `tendsto_powerIterate` hold
together for the diagonal map with entries 2 and 1 on the plane (Mathlib orders the eigenvalues
largest first, `LinearMap.IsSymmetric.eigenvalues_antitone`), started from `(1, 1)`. It is starting
material for item 147's witness: the session moves it into the module's namespace, gives it the
docstring of HANDOFF section 4 and calls the theorem by its full name.

## tools/

Cloud ports of order LEAN-32's helpers on DSMain, for the rules of `HANDOFF.md` section 6 that
name them: `ev.sh` and `hl.sh` (rule 23), `el.sh` with `probecheck.py` and `allowlist.txt`
(rules 20 and 37), `rootrun.sh` (rule 38), `evcite.py` and `citecheck.py` (rule 39),
`briefcheck.py` (rule 36), `census.sh` with `census-tail.lean` and `census-all-tail.lean`
(rule 27). Each keeps LEAN-32's log line format; the paths come from the environment (`EVD`,
`REPO`, `BASE`) instead of DSMain's, and DSMain's night window and memory cap are left out.
Three changes beyond the paths, from the first cold review of order CLOUD-MATH-2: each tool
that runs Lean puts `~/.elan/bin` on `PATH` (as the originals do); `ev.sh`, `el.sh` and
`rootrun.sh` refuse a label already used, so no saved output is overwritten (rule 17); `census.sh`
elaborates with rule 20's four flags. `allowlist.txt` adds three tactic names the drafts use
(`all_goals`, `conv_lhs`, `push_neg`). `test_ctools.sh` holds 41 planted-fault tests; on DSMain on
2026-10-19 all 41 passed (output sha256 `3fc1b6ebabad26085aca2e48e5d356e703eba48cfcc011dc7671f973b47cc700`). Each file's sha256 is in `tools/SHA256SUMS`.
