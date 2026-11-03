# classical-lean

classical-lean is a library of classical mathematics written in Lean, on toolchain
`leanprover/lean4:v4.34.0` and Mathlib at the manifest's `v4.34.0`. Lean is a programming language
whose compiler checks proofs, so every proof here has been checked by Lean's kernel, and the axiom
gate confirms that each theorem rests on Lean's standard axioms only. Whether a statement means what
its prose says is not something Lean checks; the witness gate and the records address that in part,
nothing fully. The library was built by its owner, named in `LICENSE` and at the end of this file,
with Claude Code and claude.ai; the records are the history of how.

## What it is not

There is no claim here beyond the theorems as stated. A statement can be vacuous, or rest on a junk
value, and still compile; that is why VacuityGate and the witness gate exist. Nothing here is advice.

## Counts, at commit `24a75a3`

- 158 modules: the `.lean` files under `ClassicalLean/`.
- 3931 theorem constants under the `ClassicalLean` namespace, as AxiomGate counts them (auxiliary
  lemmas included).
- `lake build` runs 4211 jobs (Mathlib's included).

## Areas

Each is a folder under `ClassicalLean/`, with three of its modules named here as examples; `ClassicalLean.lean` imports every module.

- Algebra: `HadamardInequality`, `MinMax`, `Kantorovich`.
- Analysis: `EulerMaclaurin`, `Simpson`, `LinearProgram`.
- Combinatorics: `ArbitrageCycle`, `Tremaux`, `RecurrenceGeneratingFunction`.
- Geometry: `Helix`, `Hopf`, `S3Quaternion`.
- GoldenRatio: `Characterisations`.
- InformationTheory: `Channel`, `ChannelCapacity`, `CompressionTest`.
- Logic: `PredicateStack`.
- NumberTheory: `Catalan`, `Wolstenholme`, `BiquadraticDiscriminant`.
- Order: `Superadditive`, `Tolerance`.
- Probability: `GamblersRuin`, `ChiSquared`, `BernsteinInequality`.
- Simplex: `Basic`, `CrossEntropy`, `DesignConstants`.
- Statistics: `Sufficiency`, `NeymanPearson`, `JamesStein`.

## How to build it

You need `elan`, the Lean version manager. It reads `lean-toolchain` and installs the right Lean
(v4.34.0).

```
lake exe cache get   # download the prebuilt Mathlib files (needs network)
lake build           # check every proof in the library
```

With the Mathlib cache, the owner's builds run under a 12 GB memory cap; without the cache, Mathlib
rebuilds from source and takes hours, and there is no measured memory figure to give for that. The
`.lake/` folder that these commands fill is not kept in git.

## How to check it

A green build is not the whole check. The gates are small programs that look for problems the
compiler accepts. Each line below is copied from `HANDOFF.md`, where the gates are explained.

```
lake build                                  # rc 0, and grep -c 'warning:' must be 0
lake env lean tools/AxiomGate.lean          # every theorem within the kernel trio
lake env lean tools/VacuityGate.lean        # no theorem asserts nothing
python3 tools/check_sorry.py ClassicalLean  # no sorry / admit / native_decide / bare axiom
python3 tools/check_records.py             # every shipped module is named in the records
python3 -I tools/witness_gate.py
python3 tools/compile_rules.py drift records/rules.toml HANDOFF.md
```

What a pass looks like: the build ends with exit code zero and no `warning:` line; AxiomGate prints
`PASS` with the count of theorems it checked; VacuityGate prints `PASS` and names any helper it was
told to accept; check_sorry prints `PASS` with the module count; check_records prints `PASS` with the
module count and its one named exemption; the witness gate, run from the repository root, prints
`WITNESSGATE PASS` with the counts of witnesses it ran (the whole library takes about 27 minutes);
the drift check prints `PASS` when `records/rules.toml` and `HANDOFF.md` agree.

`tools/banned_vocab_scan.py` reads a private word list that is not in the repository, so for anyone
else it exits with code 2 (measured), and the seventh gate, a whole-library recheck in a fresh build, runs
outside CI on the owner's machine.

## Reading the docstrings

Module docstrings cite the check scripts, witness notes and plan behind their hypotheses by the names
the orders used. Every such file is in `records/scripts/` or `records/plan/`, with a map in
`records/scripts/README.md` (one cited file is not retained, and the map says so). Some words you
will meet: "the lane" is the owner's private work-order folder, outside the repository.
"API-CREDIT-1" is the order under which proof drafts, with ids like `d127-r1-s2`, were bought from
the Anthropic Batch API in October 2026 and then adapted by the sessions the docstrings name. "Order
LEAN-NN" is a work order, kept in `records/orders/` and indexed by `INDEX.md` there. "Order CC-NN"
was an order run by a Claude Code session, named in its row. "claude-ai" is the planning chat that
wrote most orders. A "round" is one order's dated record in `records/rounds/`. A "bridge" is a
theorem that needs two modules. A "store row" is an entry in the owner's private record. A host name
is one of the owner's machines.

## Other files

- `HANDOFF.md`: how to work on the library and how to be sure a claim is true.
- `ROADMAP.md`: the subject areas to add next.
- `records/`: a record of each round of work and each order; its orders and rounds cite hosts and
  scratch paths a reader cannot reach.
- `records/scripts/`: the check scripts, outputs and witness notes the docstrings cite, with their map.
- `records/plan/`: the plan and the bridges file the docstrings cite.
- `deploy/`: a nightly check that builds the library and runs the gates.
- `tools/`: the gates `AxiomGate.lean`, `VacuityGate.lean`, `check_sorry.py`, `check_records.py`,
  `witness_gate.py`, `compile_rules.py` and `banned_vocab_scan.py`, with `UninformativeReport.lean`,
  `bridge_search.py` and `build_registry.py` as helpers; the tests `VacuityGateTests.lean`,
  `run_vacuity_tests.py`, `witness_gate_tests.py`, `test_compile_rules.py` and
  `test_breakit2_rules.py`, with their fixtures.

## License

Apache License 2.0. See `LICENSE`. Copyright 2026 Dustin Watkins.

## Contributions

Issues are welcome. Pull requests go through the owner's gates before merge.
