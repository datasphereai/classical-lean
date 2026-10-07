# Round 31 — `|discr ℚ(√2, √3)| = 2304` proved; the library declares no axiom (order LEAN-3)

Session: Claude Code `session_01KyYusMNSHJap88c9A6s6K2` on **DSMain**, as dustin, executing order
`LEAN-3` (`records/orders/20261007T190100Z__claude-ai__order-lean3-prove-disc-biquadratic.md`), on
the local branch `prove-disc-biquadratic` of `~/lean/classical-lean` (a clone of
`/data/git/classical-lean.git` at `ea592cf`). Lean and Mathlib v4.34.0 (`5ed2965256`). Nothing was
pushed. This closes order G-4 (`records/orders/20260908T195000Z__claude-ai__order-g4-discriminant-bound.md`).

Modules added or changed:

* `ClassicalLean/NumberTheory/BiquadraticDiscriminant.lean` — new.
* `ClassicalLean/NumberTheory/CompositumDiscriminant.lean` — the axiom `disc_biquadratic_23` is
  replaced by a theorem with the same name and statement (§3); header and §11–§14 prose updated.
* `ClassicalLean.lean` — one import line.
* `tools/AxiomGate.lean` — `scopedExceptions` is empty; the PASS line says `0 scoped exceptions`.

## Route

`K1 = ℚ(θ)` for `θ = (√2 + √6) / 2 - 1`, with minimal polynomial `g = X⁴ + 4X³ + 2X² − 4X − 2`
(`θ + 1 = 2 cos(π/12)`). `BiquadraticDiscriminant` proves, for any number field `F` with a power
basis whose generator has minimal polynomial `g`:

1. `discr_powerBasis`: `Algebra.discr ℚ B.basis = 2304`, the determinant of the matrix of power
   sums `Tr θ^(i+j)` = `4, −4, 12, −28, 80, −224, 648`. The traces come from writing `θᵏ` in the
   coordinates `1, √2, √3, √6`, where `√2 = θ³ + 3θ² − 2`, `√3 = θ² + 2θ − 1` and
   `√6 = −θ³ − 3θ² + 2θ + 4` are polynomials in `θ`. Then `Tr 1 = 4`, and `Tr √d = 0` by
   `trace_eq_finrank_mul_minpoly_nextCoeff` with minimal polynomial `X² − d`.
2. `isIntegralClosure_adjoin`: `ℤ[θ] = 𝓞 F`.
   - `Algebra.discr_mul_isIntegral_mem_adjoin` gives `2304 z ∈ ℤ[θ]` for every algebraic
     integer `z`.
   - `g` is Eisenstein at 2, so `mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt`
     removes `2⁸`.
   - `three_dvd_coeffs` / `mem_adjoin_of_three_smul_mem`, used twice, remove `9`. The step at 3
     is done by hand: `g ≡ (X² − X − 1)² mod 3` with the quadratic irreducible (sympy
     `factor_list(g, modulus=3)`), so 3 has `e = 2, f = 2` and no element of `K1` is
     Eisenstein at 3.
3. `discr_eq`: `NumberField.discr F = 2304`, by the pattern of Mathlib's
   `IsCyclotomicExtension.Rat.discr_prime_pow`.

`CompositumDiscriminant` §3 checks the hypotheses for `K1`:
- `genK1` is a root of `g`;
- `√2` and `√3` are polynomials in it, so `K1 = ℚ⟮genK1⟯` (`le_antisymm`, with no degree count);
- `minpoly ℚ genK1 = g` by irreducibility, since `g` is Eisenstein, primitive and, by Gauss,
  irreducible over ℚ.

It then transports the discriminant along `IntermediateField.equivOfEq`.

Numbers checked before any Lean was written, with sympy 1.13.1 in `~/[retired term]-venv`:
- `disc(g) = 2304`;
- the trace matrix determinant is `2304`;
- the coordinate change `{1, θ, θ², θ³} → {1, √2, √3, √6}` has determinant `−8`.

Routes rejected, and why (also in the plan at the top of the LEAN-3 report):
- **Divisibility sandwich.** The quadratic-subfield towers bound `|discr K1|` below only by
  `2⁶·3²`, short of `2⁸`.
- **Compositum formula.** `gcd(8, 12) ≠ 1`.
- **Dedekind index criterion.** Mathlib's `NumberField/Ideal/KummerDedekind.lean` assumes
  `¬ p ∣ exponent θ`; `grep -rniE 'dedekind.{0,20}criterion'` finds nothing else.

## Gates

All six run on the working tree after `f42fa5d`. The tree was not clean: this fragment, `CLAIMS.md`,
`INDEX.md`, the order copy and `HANDOFF.md` were uncommitted; none of them is Lean.

```
lake build                         Build completed successfully (3805 jobs); rc=0
  (both changed modules recompiled after deleting their build outputs; grep -c 'warning:' → 0)
lake env lean tools/AxiomGate.lean axiom gate PASS — 1662 theorem constant(s) under [ClassicalLean], every one
                                   depending only on a subset of [propext, Classical.choice, Quot.sound];
                                   0 scoped exceptions
lake env lean tools/VacuityGate.lean  vacuity gate PASS — no vacuous theorems in [ClassicalLean]
python3 tools/check_sorry.py ClassicalLean   check_sorry PASS — 53 file(s) under ClassicalLean, ...
python3 tools/banned_vocab_scan.py ClassicalLean  PASS — 53 file(s) under ClassicalLean + ClassicalLean.lean,
                                   0 hits across 31 retired and 8 provenance terms
python3 tools/check_records.py     (red before this fragment: UNRECORDED NumberTheory/BiquadraticDiscriminant.lean;
                                   re-run after it, result in the commit message)
```

AxiomGate's change was shown red, then green (HANDOFF §0); both runs are in `f42fa5d`'s commit
message.
- **Red:** a planted `axiom plantedAxiom` and `theorem planted := plantedAxiom` gave
  `FAIL — 1 of 1663 … planted ← [plantedAxiom]`, rc=1.
- **Green:** after the restore (sha256 checked), the gate passed with 1662 and 0 scoped
  exceptions, rc=0.

`#print axioms` after `lake build ClassicalLean.NumberTheory.CompositumDiscriminant`:
`disc_biquadratic_23`, `K1_K2_isCoprime` and `disc_K_eq_240_pow_4` each depend on
`[propext, Classical.choice, Quot.sound]`.

## Per-module theorem-constant counts

Measured with a `ModuleThmCount`-style script (`env.getModuleFor?` under the axiom gate's
predicate: user name under `ClassicalLean`, no macro scopes, `.thmInfo`) on the working tree above:

- `NumberTheory/BiquadraticDiscriminant`: **53** (new).
- `NumberTheory/CompositumDiscriminant`: **124**.
- Total: **1662**, equal to the axiom gate's count.

Before this round the gate counted 1595 at `ea592cf` (LEAN-1, measured on DSMain). No other module
changed, so `CompositumDiscriminant` went **110 → 124** (+14: the §3 lemmas and the theorem that
replaced the axiom). The 110 is **derived** by subtraction (1595 − (1662 − 53 − 124)), not measured
at `ea592cf`.

## Commits (branch `prove-disc-biquadratic`)

- `bf9325e` — BiquadraticDiscriminant (WIP): discriminant of the power basis, and the step at 3.
- `c0b1342` — BiquadraticDiscriminant (WIP): `ℤ[θ]` is the ring of integers, and `discr F = 2304`.
- `4af1dde` — CompositumDiscriminant: `disc_biquadratic_23` is a theorem, not an axiom.
- `f42fa5d` — Docs and axiom gate after `disc_biquadratic_23` became a theorem.
- `730ccd0` — the records commit that added this fragment (hash added in this follow-up edit).
