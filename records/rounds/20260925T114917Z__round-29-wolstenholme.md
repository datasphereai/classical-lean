# Round 29 — Wolstenholme's theorem: `C(2p − 1, p − 1) ≡ 1 (mod p³)` and `p² ∣` the numerator of `H_{p−1}` (order G-10, J2)

Session: Claude Code `session_01LSEckQnr5DiDZ1uDaGnUiT` on helios, executing order `G-10`
(`records/orders/20260925T060100Z__claude-ai__order-g10-wolstenholme-fwl.md`), job J2, in
`ClassicalLean/NumberTheory/Wolstenholme.lean`. Lean and Mathlib v4.34.0. Evidence:
`~/work/_bump-evidence/g10/`. Times are UTC, from `evidence.log`. The gate numbers for J2's commit
are `land.sh check`'s, on the tree with the change in place; the clean-tree numbers after it are
recorded at the records step.

## Searches, junk cells and statements

**Searches** (rule 21; J1 item 11, `searches_row12.sh`/`searches_shape.sh` over
`.lake/packages/mathlib/Mathlib`; `item11b-row12` 08:22:06Z, `item11b-shape` 08:23:16Z):
`S1=0 S2=1 S3=6 files S4=0 S5=2 S6=16 S7=Finite/Basic.lean:311 S8=0 S9=0 S10=24 S11=3 S12=0`. Prior
art: **0 binomial congruences modulo a prime power** in Mathlib (new); Mathlib's
`NumberTheory/Harmonic/Int.lean` is the related work (a Harmonic numerator integrality, not this
congruence). The 28 `#check` probes of §0 row 8's Mathlib and library names all resolve
(`item11-elab-wolstenholme` 08:20:06Z: rc 0, 7 `sorry` warnings and nothing else). `ZMod` inverse
behaviour spot-checked (`item11c-zmodinv` 08:23:58Z): `(2 : ZMod 4)⁻¹ = 1`, `(3 : ZMod 7)⁻¹ = 5`,
and `2 * 2⁻¹ = 2 ≠ 1` in `ZMod 4` (a non-unit's junk inverse) — the reason every inverse used is
gated by `IsUnit`/`ZMod.mul_inv_of_unit`.

**Junk cells** (exact; every line predicted first; `wolstenholme_cells.py`, sha256 `04bcc32e…9531`;
`item11d-wolstenholme` 08:25:47Z, `item11d-composite-fix` 08:26:14Z): over the 166 primes
`5 ≤ p < 1000`, **0 failures** of each of (W1) `2 ≤ v_p(H(p−1))` — and `= 2` exactly at each — (W2),
(W3), (W4) and (W5); (W2) over `p < 1000`, 0 failures. Dropped-hypothesis cells at `p = 2, 3`:
`v₂(H 1) = 0`, `v₃(H 2) = 1`; `C(3,1) % 8 = 3`, `C(5,2) % 27 = 10`; `catalan 2 = 2` against `6`,
`catalan 3 = 5` against `14`; and at `p = 3` the half sums (W7), (W6) give `2`, not `0` (so `5 ≤ p`
is needed there too). **No composite `n < 2000`** has `C(2n − 1, n − 1) ≡ 1 (mod n³)`.

*An R8 correction made in J1* (`item11d-composite-fix`): the first composite scan reported the
values `1009…1999` "composite" satisfying the congruence; those are **primes** — the sieve capped at
`1000` while the scan ran to `2000`. Re-run with a `2000`-sieve, the composite list is empty. A
Wolstenholme prime (`C(2p − 1, p − 1) ≡ 1 (mod p⁴)`): `16843` True, `27011` False (claude-ai's
recalled second prime is not one; nothing here depends on it).

**Rule 21/31**: the cells ran in J1, before any J2 statement was drafted to a file
(`item12-rule31-gate` 08:30:20Z: the last cell was `item11d-fwl` 08:29:09Z; the order's statements
are fixed and were presented in the chat plan, not authored to a file, until proving began).

**Statements, reviewed before any proof** (rule 16; `reviews/stmt-j2.md`, sha256 `ee6b4b5e…5341`):

> VERDICT: ACCEPT

Every statement (W1)–(W7) and the four `example`s were accepted with no required change (the
per-statement table reads `ACCEPT | none` throughout). They elaborated under rule 20's flags with 7
`sorry` warnings and nothing else (`item11-elab-wolstenholme`). The statements are the order's §J2,
byte for byte; the names are the order's suggestions, kept.

## Proofs

**The route** (order §0 row 8, the pairing route, derived here from the cells):

- **(W7)** `sum_inv_sq_eq_zero`: `∑_{i=1}^{p−1} (i²)⁻¹ = 0` in `ZMod p`, from
  `FiniteField.sum_pow_lt_card_sub_one` at exponent `p − 3` (`(i²)⁻¹ = i^(p−3)` by Fermat,
  `ZMod.pow_card_sub_one_eq_one`), reindexing `Icc 1 (p−1) ↔ univ.erase 0` (`Finset.sum_nbij'`,
  `Finset.sum_subset`).
- **(W6)** `sum_inv_mul_sub_eq_zero`: `∑_{i=1}^{(p−1)/2} (i(p−i))⁻¹ = 0`, from (W7) by the reflection
  `i ↔ p−i` (`sum_nbij'`, `neg_sq`) folding the full sum to twice the half, and `2` a unit (`p` odd)
  to cancel; the per-term identity `(i(p−i))⁻¹ = −(i²)⁻¹` via `ZMod.natCast_self`.
- **(W2)** `choose_two_mul_sub_one_modEq_one`: in `ZMod (p³)`. `(p−1)! · C(2p−1,p−1) = ∏_{j=1}^{p−1}(p+j)`
  (`Nat.descFactorial_eq_factorial_mul_choose`, `descFactorial_eq_prod_range`, reindexed). `(p−1)!`
  and each `j` are units (`ZMod.isUnit_iff_coprime`, `.pow_right 3`). Factoring,
  `C ≡ ∏(1 + p·j⁻¹)`; pairing `j ↔ p−j` gives `∏_{k=1}^{(p−1)/2}(1 + 2p²·(k⁻¹(p−k)⁻¹))`; the private
  helper `prod_one_add_of_mul_eq_zero` collapses the product to `1 + 2p²·S`, because every pairwise
  product of the `2p²·(…)` terms carries `p⁴ = 0`; and `ZMod.castHom (p³→p) S = 0` by (W6), so
  `p ∣ S.val`, so `2p²·S = 2t·p³ = 0`.
- **(W3)** `choose_two_mul_modEq_two`: `C(2p,p) = 2·C(2p−1,p−1)` by Pascal (`Nat.choose_succ_succ'`)
  and `Nat.choose_symm`, then `×2` on (W2).
- **(W4)** `centralBinom_modEq_two`: (W3) through `Nat.centralBinom = (2p).choose p` (term-mode).
- **(W5)** `catalan_prime_modEq`: `catalan p ≡ 2 + 2p² − 2p`, from
  `ClassicalLean.succ_mul_catalan_eq_choose` (`(p+1)·catalan p = C(2p,p)`) and
  `(p+1)(2 + 2p² − 2p) = 2p³ + 2 ≡ 2`, cancelling the coprime `(p+1)`
  (`Nat.ModEq.cancel_left_of_coprime`; `p ⟂ p+1` via `Nat.gcd_add_mul_right_right`). This is the
  value-level use of a `Catalan` constant that gives the island `Catalan` its first user (Done-means 4).
- **(W1)** `two_le_padicValRat_harmonic`: the numerator `A = ∑_{k=1}^{p−1} (p−1)!/k`, with `p² ∣ A`
  by the same pairing — `k(p−k) ∣ (p−1)!` for `k` in the lower half; the per-pair identity
  `(p−1)!/k + (p−1)!/(p−k) = p·((p−1)!/(k(p−k)))`; `B = ∑ (p−1)!/(k(p−k))` casts to `0` in `ZMod p`
  by (W6), so `p ∣ B`, so `p² ∣ A`. Then `harmonic (p−1) = A / (p−1)!` (a `range ↔ Icc` bijection),
  `padicValRat.div` with `p ∤ (p−1)!` (`padicValNat.eq_zero_of_not_dvd`, `Nat.Prime.dvd_factorial`),
  and `padicValNat_dvd_iff` finish `2 ≤ v_p(A)`.

**Dependency graph as proved** (Done-means 6): (W2)←(W6)←(W7); (W3)←(W2); (W4)←(W3); (W5)←(W3);
(W1)←(W6); (W7) on nothing else in J2 — exactly as routed. The theorems are in dependency order in
the file (rule 18), reordered from the reviewed skeleton's W1…W7. Two ℕ-subtraction hazards the
proof guards: `omega` cannot see through nested `p − (p − i)` (used `Nat.sub_sub_self`), and the
half-split needs `p` odd (`hodd : p % 2 = 1`).

**The census (rule 27), as a difference** (`g10-census-j2-modthmcount`, `g10-census-j2-listthms`):
the module contributes **91 theorem constants** (`ClassicalLean.NumberTheory.Wolstenholme 91`), of
which **1 is private** (the helper `prod_one_add_of_mul_eq_zero`). Library totals: `MODULE-THM-COUNT
total 1487 → 1578` (+91), `modules 50 → 51`; `#COUNTS raw 1487 → 1578, filtered 887 → 895` (+8),
`private 208 → 209` (+1). Predicted by hand "1487 + d, d ≥ 8" (eight named declarations); the 91 is
those plus the `omega`/`ring`/`simp`/`decide` auxiliaries. Axioms: all 91 within the kernel trio
(gate 2 `AxiomGate`, fire-tested on a planted `sorry` in J1's tooling checks).

**Post-proof review** (rule 13; `reviews/post-j2.md`, sha256 `158e45f9…a12c`; dispatched to an
`adversarial-critic` subagent, its returned text saved from the hand-back and hashed):

> VERDICT: PASS

> All five headline theorems faithfully state Wolstenholme's theorem and its standard corollaries [...] there are no cheats (no axiom / native_decide / sorry / admit [...] The single finding is cosmetic. Zero BLOCKER, zero MAJOR → PASS.

The one finding (`post-j2` [1], MINOR) was cosmetic: the `catalan_prime_modEq` docstring wrote its
RHS as `2 − 2p + 2p²` — which truncates read as ℕ — against the statement's `2 + 2*p^2 - 2*p`; the
docstring was reordered to `2 + 2p² − 2p`. No statement or proof line changed, so rule 29 has
nothing to check; the module was re-elaborated after the edit (rc 0, 0 warnings). The reviews were
dispatched with the Agent tool (not a workflow); each subagent's authoritative returned text was
extracted from its hand-back to `reviews/{stmt,post}-j2.md` and hashed (rule 33, against the
returned text).

**Landing.** The landed file is the reviewed file, byte for byte (`cp` then
`sha256 4365a5b5…7ee2` = the work file; R28). One import line added to `ClassicalLean.lean`
(`import ClassicalLean.NumberTheory.Wolstenholme`, alphabetical, after `Tribonacci`). `lake build`:
rc 0, **0 warnings**, 3802 jobs (gate 1). Gate 6 fire-tested (rule 18): with the module and import
in place but before this fragment, `check_records` FAILed (`g10-firetest-records-j2`: 51 modules, 1
UNRECORDED `ClassicalLean/NumberTheory/Wolstenholme.lean`); it passes once this fragment names the
module. The Lean-side import closure (J1 item 7, `item7-catalan`): `Catalan` loaded alone reaches
`Catalan` and `Mathlib.Combinatorics.Enumerative.Catalan.Basic` (positive controls), and **not**
`Mathlib.Data.Nat.Prime.Factorial`, `Mathlib.Data.Nat.Factorial.BigOperators` or
`Mathlib.NumberTheory.Harmonic.Defs` (negative controls fire) — which is why the module imports
those three explicitly beside `Catalan` (and `Padics.PadicVal.Basic`, `FieldTheory.Finite.Basic`,
`ZMod.Basic`; `ZMod.Basic` is already in `FieldTheory.Finite.Basic`'s closure and kept, as G-9 ruled
for `Digits.Lemmas`).

**Per-module count**: `NumberTheory/Wolstenholme` 0 → 91 theorem constants (private 0 → 1;
filtered 0 → 8), from the census of the landed text.

**Commit**: `8839f14` (J2, `j2-commit`).

**After the landing** (clean tree at `8839f14`, measured before J3 landed): the six gates pass —
`lake build` rc 0, 0 warnings, 3802 jobs; `AxiomGate` PASS; `VacuityGate` PASS; `check_sorry` PASS;
`banned_vocab_scan` PASS, 0 hits; `check_records` PASS, 51 modules, 24 records files, 1 exemption.
Census `raw 1578 filtered 895 private 209`, `modules 51`. Appendix A (`g10-after-j2-*`): declgraph
1764 constants, **islands 2** (`CompositumDiscriminant`, `Tolerance`) — `Catalan` is no longer an
island, `Wolstenholme usedBy=0 uses=1` (`Catalan`), `Catalan usedBy=1 uses=0`; `pairs.py`
`modules=51 edges=84 pairs=90` (was `50/83/91`); `DupCheck: 5 TWIN, 0 SWAP`. The type dump against
J1's baseline shows only additions (the cumulative J2+J3 diff is recorded in round 30).
