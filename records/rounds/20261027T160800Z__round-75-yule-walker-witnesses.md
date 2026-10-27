# Round 75 — witnesses for YuleWalker's Yule–Walker theorems (order VACUITY-5)

Session: Claude Code `session_01HgueTaMGxsMGo5HLwpJJjR` on DSMain, as dustin, executing order
`VACUITY-5` (`records/orders/20261027T052000Z__claude-ai__order-vacuity5-yule-walker-witnesses.md`,
written by claude-ai, copied verbatim; lane `lean/VACUITY-5/order.md`, sha256
`02a01495e1482cfaedeeeec91cc7191a0f38b3f9b41961ee41c7dfccde9c44d2`), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `vacuity-5`, made from `fb8beee` (LEAN-36's last
commit, equal to `git ls-remote origin master` and `git ls-remote github master`, both read
2026-10-27 12:05 EDT). Lean and Mathlib v4.34.0. Nothing pushed. The order is the first written to
the lighter procedure (store row 20261026-063): Lean's own check, the machine gates, one cold review
and claude-ai's push review; no plan-approval stop. Scratch files: `~/lean/vacuity5-checks/`
(outside the repository). The launch variable `CLAUDE_CODE_DISABLE_AUTO_MEMORY` printed `1`
(2026-10-27 01:21 EDT); the session then waited out the night window and resumed at 12:05 EDT, when
step 1's checks were run again and matched.

The order's copy: its sha256 read through the connector (`ds_hash`, equal to the value above), then
the file copied byte for byte into `records/orders/` and its sha256 checked equal. The two type-dump
files (`TypeDumpPI.lean`, `g8_typediff.py`) were read through the connector and written from its
replies, each sha256 checked against the order's value.

Before the work, on the clean tree at `fb8beee`: `lake build` completed (4193 jobs); the type dump
`td-before.jsonl` checked `CHECK records=4163 thm=3666 def=497 elided=0 missing_fields=0`.

First part written before the work; completed after it, below.

## Files this round changes

Module files (no module is added):

* `ClassicalLean/Probability/YuleWalker.lean`: three `example` blocks after its last line (one each
  for `covariance_eq_sum`, `isSolution_autocovariance` and `exists_poly_mk_autocovariance_eq`), the
  Mathlib import lines the blocks need among the three the order names, and the witness note of its
  module docstring. No declaration changed.

Also changed: `records/CLAIMS.md` and `records/orders/INDEX.md` (this order's rows appended at the
bottom, and LEAN-36's push recorded in LEAN-36's two rows), this fragment, the order's copy, and
`HANDOFF.md` sections 1 and 4 (one dated paragraph each). Nothing under `tools/`, `.github/` or
`records/rules.toml`; no other `.lean` file.

## Order LEAN-36's push

By records/README.md rule 2, this round's first commit inserts into LEAN-36's INDEX row (right after
`rule 8's reading of five reviews put to claude-ai (round 74)`, before its commits cell) and its
CLAIMS row (before the final ` |`) the text
`; pushed by Dustin: master fb8beee on both remotes, CI run 40443324601 green`, as the order gives
it, by the script `~/lean/vacuity5-checks/pushnote.py`, which asserts one matching row and one
anchor in each before inserting. Re-measured before the commit: `git ls-remote origin master` and
`git ls-remote github master` both gave `fb8beee37b74ea369f553c41a5b1279d1cf2490b`. The CI run's
number and colour are the order's (store row 20261027-003), not measured here.

## Completed after the work (2026-10-27 UTC)

### What landed

| commit | what |
|---|---|
| `d42a47c` | records first (this fragment's first part, the order's copy, the INDEX and CLAIMS rows, LEAN-36's push) |
| `9bdd251` | `ClassicalLean/Probability/YuleWalker.lean`: the three witnesses after the module's last line, two import lines, the docstring's witness note (first G) |
| `cf1bde0` | the same module: the three witnesses' docstrings after the cold review, no code changed (G) |
| `331732b` | `HANDOFF.md` sections 1 and 4 (documents) |

Import lines: two of the three the order allowed, `Mathlib.Probability.Distributions.Gaussian.Real`
and `Mathlib.Probability.Independence.InfinitePi`; `Mathlib.Probability.ProductMeasure` was not
needed. The `IsProbabilityMeasure` instance for `Measure.infinitePi` of Gaussians with the varying
variances `48/25, 16/15, 1, …` is found by Lean (the order noted no probe had tried it).

The witnesses: one model in all three, `Ω = ℕ → ℝ`, `μ = Measure.infinitePi` of `N(0, 48/25)`,
`N(0, 16/15)`, `N(0, 1)`, …; `e t` the coordinates; `X` by `Nat.rec` on pairs, `X 0 = e 0`,
`X 1 = 2/3 · X 0 + e 1`, `X (t + 2) = X (t + 1)/2 + X t/4 + e (t + 2)`; `p = 2`,
`a = ![1/2, 1/4]`; `γ k = cov(X k, e 0)`; `k = 2` in the first. Each hypothesis's proof names the
measure, the noises and the process with `let`, restates its goal with `change`, proves the noises'
moments from the Gaussian laws and their independence (`iIndepFun_infinitePi`), makes the names
opaque with `clear_value`, and then follows the draft `d3003-r1-s1`'s steps. Scratch check
`~/lean/vacuity5-checks/probe/moves.lean` (sha256 `8707b954…df8d`, `lake env lean` rc 0, no
output) proves in Lean that `γ 0, γ 1, γ 2 = 48/25, 32/25, 28/25`, every noise variance is
positive, and `X (t + 1) ≠ X t` with positive probability for every `t`.

The cold review (one fresh subagent, read only; `~/lean/vacuity5-checks/review/review-1.md`): all
three PASS WITH FINDINGS. Findings 1 and 2 (an import and the third statement missing) were the
session's packet error: `theorems.lean` was cut with `fb8beee`'s line numbers from the longer module
at G; Lean settles both (build, witness gate). Finding 3 (`mΩ` left to unification) is kept, as in
the earlier `infinitePi` witnesses, and stated in the docstrings. Findings 4 to 7, docstring
wording, applied in `cf1bde0`. Finding 8 settled by the build. No block's arguments changed, so no
second pass.

### The gates, on the clean tree at G `cf1bde0` (expected in `~/lean/vacuity5-checks/expected-step5.txt`, sha256 `f9542cdf…27b0`, written before the first run)

| gate | expected | measured |
|---|---|---|
| `lake build` | 4193 jobs, 0 warnings | `Build completed successfully (4193 jobs).`, 0 warning lines |
| AxiomGate | PASS 3666 | `axiom gate PASS — 3666 theorem constant(s)`, 0 scoped exceptions |
| check_sorry | PASS | `check_sorry PASS — 140 file(s)` |
| check_records | PASS 140 | `check_records PASS — 140 module(s)`, 114 files searched |
| VacuityGate | PASS | `vacuity gate PASS`, 1 reviewed helper, 0 VACUOUS-PENDING |
| banned scan | PASS | `banned_vocab_scan PASS — 140 file(s) … 0 hits` |
| witness gate, YuleWalker | OK 4, copy-error 0 | `WITNESSGATE PASS modules=1 … OK=4 … copy-error=0` |
| witness gate, library | PASS, OK 182 | `WITNESSGATE PASS modules=140 elaborated=72 OK=182 … TYPED=205 … LISTED=1 … copy-error=0`, 1648.6 s |
| type dump | 4163 records; all zeros | `CHECK records=4163 thm=3666 def=497 elided=0 missing_fields=0`; `DIFF removed=0 added=0 changed=0 proof_only=0` |
| drift (on `331732b`) | PASS | `PASS no drift` |

At the first G `9bdd251`, the build, AxiomGate, check_sorry, check_records, VacuityGate, the banned
scan and both witness gates gave the same lines (the library witness gate `OK=182`, 1617.0 s); the
type dump was run only at `cf1bde0`; the drift check was also run once on the uncommitted HANDOFF edit before its expectation
was written (PASS), then on the commit as above. Gate 7, the bridge search and the report tool not
run (no theorem added). Theorem-constant count: unchanged, 3666 (examples add no constant).
