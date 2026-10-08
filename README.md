# classical-lean

classical-lean is a library of classical mathematics written in Lean 4. Lean is a programming
language whose compiler checks proofs, so every theorem here has been checked by a machine. The
library builds on Mathlib, the main community library of Lean mathematics.

It covers several areas: algebra, analysis, combinatorics, geometry, information theory, logic,
number theory, order, probability and statistics. Each area is a folder under `ClassicalLean/`,
and `ClassicalLean.lean` imports every module.

## How to build it

You need `elan`, the Lean version manager. It reads `lean-toolchain` and installs the right Lean
(v4.34.0).

```
lake exe cache get   # download the prebuilt Mathlib files (needs network)
lake build           # check every proof in the library
```

The first command saves hours: without it, Lean rebuilds all of Mathlib from source.
The `.lake/` folder that these commands fill is not kept in git.

## How to check it

A green build is not the whole check. The gates are small programs that look for problems the
compiler accepts:

```
lake env lean tools/AxiomGate.lean     # every theorem rests only on Lean's standard axioms
python3 -I tools/check_sorry.py        # no proof is left unfinished ("sorry")
lake env lean tools/VacuityGate.lean   # no theorem is empty, such as one that only proves True
python3 -I tools/check_records.py      # every module is named in records/
```

## Other files

- `HANDOFF.md`: how to work on the library and how to be sure a claim is true.
- `ROADMAP.md`: the subject areas to add next.
- `records/`: a record of each round of work and each order.
- `deploy/`: a nightly check that builds the library and runs the gates.

## License

Apache License 2.0. See `LICENSE`. Copyright 2026 Dustin Watkins.
