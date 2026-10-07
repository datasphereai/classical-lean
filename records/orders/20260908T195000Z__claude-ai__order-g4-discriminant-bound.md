# ORDER G-4 — narrow `disc_biquadratic_23`, and stop calling it discharge

Written 2026-09-08. Reconstructed from the G-4 session's report and revised by what that session
measured. The original G-4 was given inline and never existed as a file; this replaces it.

## Status of the original G-4

**Not discharged, and the route it assumed is closed.** Attributed to the G-4 session, recorded in
`HANDOFF.md` beside the axiom paragraph, and **not re-measured** by the session that wrote this
file — re-run the commands below before acting.

The axiom is `disc_biquadratic_23` (`|discr ℚ(√2,√3)| = 2304`) in
`NumberTheory/CompositumDiscriminant.lean`, registered in `AxiomGate.scopedExceptions` and
carrying exactly two theorems.

`HANDOFF.md` said the route was to wait, because "Mathlib moves". The pin has not moved —
`lake-manifest.json` still names `8f07524533b483cffcf3c5a50b9633c6af0defdc` — and the G-4 session
measured that even a successful cyclotomic embedding does not close it:

* `natAbs_discr_sq_dvd_of_tower` and `discr_cyclo24 = 5308416` already exist axiom-free, so
  realising `K1` inside the 24th cyclotomic field gives `|discr K1|` dividing 2304.
* Against `abs_discr_ge'`, the best lower bound this Mathlib has, that leaves **ten** surviving
  divisors of 2304 in the best case (totally real, `r₂ = 0`, bound 113.78) and 14 at `r₂ = 2`.
  The module currently uses only `abs_discr_gt_two`, which leaves 25.
* So the embedding **cannot force 2304 even if built**. The §6 argument for `ℚ(√5)` worked only
  because `125 = 5³` leaves a single square-divisor candidate.
* Closing it needs the conductor–discriminant formula, or the ring of integers of a biquadratic
  field. Neither is in this Mathlib. An independent search adding `conductor.discriminant`,
  `discr.*tower|relativeDiscr`, `ringOfIntegers.*(quadratic|biquad)` and `index.*discr` returned
  nothing beyond what the module already cites.
* **Re-run 2026-09-23 at Mathlib v4.34.0 (order 0923, J3 step 7; round 17)**, beside the old pin:
  `conductor.discriminant` 0 → 0; `ringOfIntegers.*(quadratic|biquad)` 0 → 0;
  `quadraticField|QuadraticField` 0 → 0; `Qsqrtd` 0 → 0; `discr.*tower|relativeDiscr` 1 → 2,
  `index.*discr` 15 → 17, `discr.*(Qsqrtd|quadratic|sqrt)` 16 → 33. The new files are
  `Algebra/QuadraticAlgebra/Discriminant.lean` (the algebraic `b ^ 2 + 4 * a` of an abstract
  quadratic algebra) and `NumberTheory/FundamentalDiscriminant.lean` (integer arithmetic,
  `Int.IsFundamentalDiscr`), and neither computes `NumberField.discr` of a quadratic field. Still
  no conductor–discriminant formula and no biquadratic ring of integers: **the axiom stays, and
  this order stays open.** Mathlib PRs #43490 and #43491 (quadratic fields and their
  discriminant) were open, labelled `merge-conflict`, on 2026-09-23.

## Goal

Replace an unbounded axiom with a bounded one, and write the closed route down so nobody
re-derives it. **Discharging the axiom is out of scope** — this Mathlib cannot.

## Scope

`ClassicalLean/NumberTheory/CompositumDiscriminant.lean`, plus one fragment under
`records/rounds/`. Every prior order held that module read-only; this one lifts that for the
single addition below and for nothing else.

Permitted: add `(discr ↥K1).natAbs ∣ 2304`, proved axiom-free via √2 and √3 as Gauss sums in the
24th cyclotomic field plus the existing tower lemma. Estimated ~100 lines into a ~1000-line
module, the same shape as the §6 `ℚ(√5)` argument.

Also permitted, and cheap: the module uses only `abs_discr_gt_two` where `abs_discr_ge'` is
strictly sharper. Exploiting it needs `nrComplexPlaces K1 = 0`; `IsTotallyReal` appears nowhere in
the module. Establish it or record why not.

Not permitted: removing the axiom, weakening `AxiomGate.scopedExceptions`, or editing any other
module.

## Done-means

All of the following, or a STOP report naming which failed:

1. `(discr ↥K1).natAbs ∣ 2304` is a theorem in the module, and its axiom footprint is a subset of
   `{propext, Classical.choice, Quot.sound}` — **not** resting on `disc_biquadratic_23`.
2. The module header states, as prose next to the theorem, that this narrows the axiom's content
   from one value to ten candidates and **does not discharge it**.
3. `HANDOFF.md`'s axiom paragraph is updated from "Mathlib moves" to the measured position.
4. All six gates pass on a **clean** tree, with the numbers recorded:

   ```bash
   # helios
   cd ~/work/classical-lean
   lake build                                  # rc 0, 0 warnings
   lake env lean tools/AxiomGate.lean          # exceptions still exactly 2, none new
   lake env lean tools/VacuityGate.lean
   python3 tools/check_sorry.py ClassicalLean
   python3 tools/banned_vocab_scan.py ClassicalLean
   python3 tools/check_records.py
   ```

5. A fragment under `records/rounds/` names the module in full and carries its own per-module
   constant count under the axiom gate's `.thmInfo` predicate.

## Stop conditions

STOP and report, rather than working around, if: the Gauss-sum construction needs a Mathlib
lemma that is not at the pinned revision; the `natAbs` bound turns out to rest on the axiom it is
meant to narrow; or the addition pushes the module past a clean `lake build`.
