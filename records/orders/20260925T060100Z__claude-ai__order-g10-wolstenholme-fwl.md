# ORDER G-10 — Wolstenholme's theorem; the Frisch–Waugh–Lovell theorem

Written 2026-09-25T06:01:00Z by claude-ai (Cowork, linked to helios) for one Claude Code session on
helios. Library: `~/work/classical-lean`. **Source of truth:** this file and `records/orders/INDEX.md`.
It waits in `~/Cowork/lean-orders/` until J1 files it, and starts only after order G-9 is closed.
A second agent reviewed it cold, twice, before it was placed there. The first pass found no
blocker, four major points (a brief-builder range that J2's statement review could not have
met; a false claim about `ZMod.inv`; the last draft elaboration not visible from the cloud; a
measurement range in §0 row 16 overstated from 150 to 400) and fifteen minor ones; the second
confirmed those fixes one by one and found six minor wordings, all applied without a third
review. Every number in §0 that the reviewer could re-run in the cloud, its own runs reproduced
(the four cell scripts byte for byte, every Mathlib line number and name, `docs/1000.yaml`); it
corrected one count (§0 row 12's `Lucas.lean`, 16) and supplied the import-closure reads of J1
item 7 and the middle step of §0 row 10's (S4).

It rests on three things:
- **Order G-9's close**: `HANDOFF.md` §3's ranking at that close puts Carmichael's theorem first,
  majorization second, the Frisch–Waugh–Lovell theorem (then Cochran's) third, Wolstenholme's
  theorem fourth and max-flow min-cut fifth; its "also open" list names the three islands, the 91
  pairs, the `ExpChar` form and a `lucasV` analogue of the rank of apparition. This order takes
  the fourth item (J2) and the first half of the third (J3). It does not take the first: this
  cycle measured the elementary route cell by cell (§0 row 15), which was the condition
  `HANDOFF.md` §3 set, and what the measurement found is one order's work of its own, not a job
  beside two others (Close step 1 ranks it for the next order). It does not take the second:
  nothing about majorization has been measured, and this order proposes only what it measured.
  J2's module bridges one of the three islands (`NumberTheory/Catalan`: §0 row 4, §2).
- **claude-ai's measurements of the library at `432aa26`** (§0): the declaration graph (three
  islands; `Catalan` used by nobody), the module-pair comparison, the duplicate check, exact
  checks of every statement below with each hypothesis dropped, the Mathlib searches, and both
  statement lists elaborated with `sorry` in the library's environment on helios.
- **The lessons of order G-9's run** (§1, rules 31–34). Its mathematics passed every gate. Its
  Close check made 26 findings, 18 distinct, none a wrong proof, statement or gate result: records
  corrections, three rulings, and process lapses (round 28's addendum). Its report counted its
  refusals by a `grep` (rule 30 worked), and its four asks for this order are met here (§0 row 12
  corrects order G-9 §0 row 12; rules 33 and 34; J1 item 0).

Three jobs, J1 to J3, then a close. Each has Goal / Scope / Done-means and an undo line. A STOP at a
gate is a report, not a close.

---

## 0. What claude-ai measured

Read-only, 2026-09-25 between 00:40Z and 05:25Z (a context compaction of claude-ai's own fell in
the middle; every number below was re-read from its saved output or re-run after it): the helios
tree at `432aa26`, run through the four scripts of Appendix A with `lake env lean` from the
repository root (no `lake build`, nothing written in the repository;
`GIT_OPTIONAL_LOCKS=0 git status --porcelain` empty before and after), with scratch files in
`/tmp/claude-ai-g10/`; the evidence of order G-9 under `~/work/_bump-evidence/g9/`, read-only; a
sparse clone of Mathlib v4.34.0 (`5ed2965256`, the manifest's pin); order G-9's session page, read
end to end; exact checks in Python (integers, rationals, and residues modulo `p ^ 3`). Line numbers
were read then; find each place by its text. "The reviewer" is the cold reviewer of this order;
facts it found are marked so.

| # | Fact | Value |
|---|---|---|
| 1 | Order G-9 | Closed (`INDEX.md` row `G-9` **closed** with its Close check's verdict; `CLAIMS.md` row of `session_01JcSz4wLVqhs25F7venK1Sh` **closed**). `master`, `dsmain/master` and `ls-remote dsmain master` are all `432aa26`. The push `196a87d..432aa26` is in `~/work/_bump-evidence/push.log` (`rc=0 push [G-9, Dustin's yes 2026-09-25] :: To dsmain:/data/git/classical-lean.git 196a87d..432aa26 master -> master`, followed by its `ls-remote` line, 16 lines in all) and in the `dsmain/master` reflog at 2026-09-25T04:29:35Z (`update by push`), and not yet in `HANDOFF.md` §6, by design (G-9's Close step 4; §6's last dated push line is `87683e3..196a87d`). `~/Cowork/lean-orders/` held no file before this one. |
| 2 | The library | 50 modules in 10 top-level directories; 1487 theorem constants, 208 of them private, and a filtered list of 887 (`ListTheorems.lean`: `#COUNTS raw=1487 filtered=887 private=208`; `ModuleThmCount.lean`: `total=1487 private=208 modules=50`). 17,081 lines under `ClassicalLean/` (16,655 at `196a87d`). 51 files whose line 4 is `Authors: Dustin [surname], Claude (Anthropic)`: the 50 modules and `ClassicalLean.lean`. Gate 6 searches 22 records files and passes with its one named exemption (`Simplex/Hessian.lean`); gate 5 passes, 0 hits across 31 retired and 8 provenance terms. `lean-toolchain` `v4.34.0`; the manifest's Mathlib `rev` `5ed2965256…`. |
| 3 | Six orders, measured from git and the rounds | See the table after this one. |
| 4 | Declaration graph (`DeclGraph.lean`, then `islands.py`) | 1673 constants in 50 modules. **Three islands**: `NumberTheory/Catalan`, `NumberTheory/CompositumDiscriminant`, `Order/Tolerance`. `NumberTheory/EuclidSteps` `usedBy= 0 uses= 1`; `NumberTheory/Lucas` `usedBy= 5 uses= 1`; `NumberTheory/LucasApparition` `usedBy= 2 uses= 2`; `Statistics/GaussMarkov` `usedBy= 1 uses= 0` (its one user is `Statistics/CramerRao`); `NumberTheory/Catalan` `usedBy= 0 uses= 0`. All as order G-9's final report predicted. J2's module will use `Catalan` (§2), so the islands become two; J3's will use `GaussMarkov`. |
| 5 | Duplicates (`DupCheck.lean`) | `DupCheck: 5 TWIN line(s), 0 SWAP line(s)`, the five labelled "Mathlib re-export"s of `GoldenRatio/Characterisations`. |
| 6 | Pairs that share rare concepts and no use (`pairs.py`) | First line `modules=50 edges=83 rare_df<=3 pairs_without_edge_sharing_rare=91` (round 28 predicted 90 and measured 91; this cycle 91). Highest: `S3Quaternion ~ SU2SO3` (10 shared), `Hopf ~ S3Quaternion` (6), then eight pairs at 4, four of them `CompositumDiscriminant`'s (with `SU2SO3`, `Lucas`, `Simplex/Ordered`, `LucasApparition`), and among the rest `Simplex/SecondOrder ~ Statistics/GaussMarkov` (4: `Matrix.PosSemidef`, `dotProduct`, two `AddGroup` projections) and `EuclidSteps ~ Zsigmondy` (4: `GT.gt`, `List.length`, `MulOne.toMul`, `MulOne.toOne`). `GaussMarkov` is also in three pairs at 2 (`SU2SO3`, `CompositumDiscriminant`, `Simplex/Involution`); `Catalan` is in no listed pair. J3's module uses `GaussMarkov`, an edge, not a pair; neither job joins a listed pair. |
| 7 | Wolstenholme's theorem, the statements (`wolstenholme_cells.py`, exact rationals and integers; sha256 `04bcc32e…9531`, output saved beside it) | Let `H n = ∑_{i=1}^{n} 1/i` (Mathlib's `harmonic n = ∑_{i < n} 1/(i + 1)`, `Harmonic/Defs.lean:23`). Over the 166 primes `5 ≤ p < 1000`, 0 failures of each of: **(W1)** `2 ≤ v_p (H (p − 1))` (`padicValRat`); and `v_p (H (p − 1)) = 2` exactly at every one of them; **(W2)** `C(2p − 1, p − 1) ≡ 1 [MOD p ^ 3]`; **(W3)** `C(2p, p) ≡ 2 [MOD p ^ 3]` and **(W4)** the same for `Nat.centralBinom p`; **(W5)** `catalan p ≡ 2 + 2 p ^ 2 − 2 p [MOD p ^ 3]` (in `ℕ`, `2 p ^ 2 ≥ 2 p`, so no truncation). Hypothesis `5 ≤ p` dropped: (W1) at `p = 2` is `v_2 (H 1) = v_2 1 = 0` and at `p = 3` is `v_3 (H 2) = v_3 (3/2) = 1`; (W2) at `p = 2` is `C(3, 1) = 3 ≡ 3 (mod 8)` and at `p = 3` is `C(5, 2) = 10 ≡ 10 (mod 27)`; (W5) at `p = 2` gives `catalan 2 = 2` against `6 (mod 8)` and at `p = 3` `catalan 3 = 5` against `14 (mod 27)`. Primality is needed: no composite `n < 2000` has `C(2n − 1, n − 1) ≡ 1 (mod n ^ 3)`. Two arithmetic facts behind (W5): `(p + 1)(1 − p + p ^ 2) = 1 + p ^ 3 ≡ 1 (mod p ^ 3)` for every prime, and `(p + 1) · catalan p = C(2p, p)` (the library's `succ_mul_catalan_eq_choose`). A Wolstenholme prime is one with `C(2p − 1, p − 1) ≡ 1 (mod p ^ 4)`: `16843` is one (measured); `27011`, which claude-ai recalled as the second, is not (measured: false) — a corrected recollection, recorded as one; the statements above do not depend on it. |
| 8 | Wolstenholme's theorem, the route (`wolstenholme_cells.py`, the "route" and "pairing" blocks; every identity checked exactly for the primes `5 ≤ p < 300`, and its failure at `p = 3` or `p = 2` where stated) | The pairing route, derived here (rule 19), with no elementary symmetric functions. (a) `(p − 1)! · C(2p − 1, p − 1) = (2p − 1).descFactorial (p − 1) = ∏_{i < p − 1} (2p − 1 − i) = ∏_{j = 1}^{p − 1} (p + j)` (`Nat.descFactorial_eq_factorial_mul_choose`, `Nat.descFactorial_eq_prod_range`, `Finset.prod_range_reflect`); checked as `C(2p − 1, p − 1) = ∏ (1 + p/j)` in `ℚ` for `p < 200`. (b) In `ZMod (p ^ 3)`, `(p − 1)!` is a unit (`Nat.Coprime` with `p ^ 3`, `ZMod.coe_mul_inv_eq_one`; `Nat.Prime.dvd_factorial`), so with `a_j = (j : ZMod (p ^ 3))⁻¹`, `C = ∏_{j = 1}^{p − 1} (1 + p a_j)`. (c) Pair `j` with `p − j`: `a_j + a_{p − j} = p · b_j` and `a_j · a_{p − j} = b_j` with `b_j = (j (p − j))⁻¹`, so `(1 + p a_j)(1 + p a_{p − j}) = 1 + 2 p ^ 2 b_j` in `ZMod (p ^ 3)`, and the product over `j ≤ (p − 1)/2` is `1 + 2 p ^ 2 ∑ b_j` (`p ^ 4 = 0`). (d) **(W6)** `∑_{j = 1}^{(p − 1)/2} b_j = 0` in `ZMod p`: `b_j ≡ −(j ^ 2)⁻¹ (mod p)` and the half sum of `(j ^ 2)⁻¹` is half the full one (`j ↦ p − j`), so it is enough that **(W7)** `∑_{j = 1}^{p − 1} (j ^ 2)⁻¹ = 0` in `ZMod p`, which is `∑_{x : ZMod p} x ^ (p − 3) = 0` (`x⁻² = x ^ (p − 3)` for `x ≠ 0`, `pow_card_sub_one_eq_one`; `0 ^ (p − 3) = 0` for `p ≥ 4`) — `FiniteField.sum_pow_lt_card_sub_one` at `i = p − 3 < p − 1` with `ZMod.card`; at `p = 3` the sum is `2`, and (W6)'s half sum at `p = 3` is `2`, which is where `5 ≤ p` enters. So `2 p ^ 2 ∑ b_j = 0` in `ZMod (p ^ 3)` and (W2) follows by `ZMod.natCast_eq_natCast_iff`. (e) (W3) from (W2): `C(2p, p) = C(2p − 1, p − 1) + C(2p − 1, p) = 2 C(2p − 1, p − 1)` (`Nat.choose_succ_succ'`, `Nat.choose_symm_half` at `m = p − 1`); (W4) from (W3) by `Nat.centralBinom_eq_two_mul_choose`. (f) (W5) from (W3): `(p + 1) · catalan p ≡ 2` and `(p + 1)(1 − p + p ^ 2) ≡ 1`, so `catalan p ≡ 2 (1 − p + p ^ 2)`; `catalan_eq_centralBinom_div` for the `example`. (g) (W1) from (c)–(d): `H (p − 1) = ∑_{j ≤ (p − 1)/2} (1/j + 1/(p − j)) = p · ∑_{j ≤ (p − 1)/2} 1/(j (p − j))`; with `N = ∑_j (p − 1)!/j ∈ ℕ` its numerator over `(p − 1)!`, `N = p · M` where `M = ∑_{j ≤ (p − 1)/2} (p − 1)!/(j (p − j)) ∈ ℕ` and `(M : ZMod p) = (p − 1)! · ∑ b_j = 0`, so `p ^ 2 ∣ N` (`ZMod.natCast_eq_zero_iff`, `padicValNat_dvd_iff`), and `v_p (H (p − 1)) = v_p N − v_p ((p − 1)!) = v_p N ≥ 2` (`padicValRat.div`, `padicValRat.of_nat`, `Nat.Prime.dvd_factorial`). Checked: `H_{p − 1} = p ∑ b_j` in `ZMod (p ^ 3)`, the pair identity, `b_j ≡ −j⁻² (mod p)`, the half-sum identity, `∑ x ^ 2 = 0` in `ZMod p` for `p ≥ 5` (`2` at `p = 3`, `1` at `p = 2`). The Vieta route (`e₁ ≡ 0 (mod p ^ 2)`, `e₂ ≡ 0 (mod p)`) was also checked and is not proposed. |
| 9 | The Frisch–Waugh–Lovell theorem, the statements (`fwl_cells.py`, sha256 `e442b8e6…c896`, and `fwl_side_cells.py`, sha256 `d29ac6d8…7a1b`; exact rationals under Mathlib's convention that a singular matrix's inverse is `0`; outputs saved beside them) | With `L X = (Xᵀ X)⁻¹ Xᵀ` (the library's `leastSquares`, `Statistics/GaussMarkov`) and the residual maker `M₁ = 1 − X₁ · L X₁`, for `X = [X₁ X₂]` (`Matrix.fromCols`): over 400 random exact trials with `n ≤ 7` rows and `k₁, k₂ ≤ 3` columns, the 239 with `Xᵀ X` invertible give 0 failures of each of **(F1)** `(L X *ᵥ y) ∘ Sum.inr = L (M₁ X₂) *ᵥ (M₁ *ᵥ y)`; **(F2)** the same with `y` in place of `M₁ *ᵥ y` on the right; **(F3)** the matrix form `(L X).toRows₂ = L (M₁ X₂)`; and, over 228 such trials with a fresh seed, **(F4)** `y − X *ᵥ (L X *ᵥ y) = M₁ *ᵥ y − (M₁ X₂) *ᵥ (L (M₁ X₂) *ᵥ (M₁ *ᵥ y))`. Side facts, 0 failures: **(S1)** `M₁ᵀ = M₁` and **(S2)** `M₁ * M₁ = M₁`, with no hypothesis (90 cells of `fwl_side_cells.py` over every `2 × 1` and `2 × 2` matrix with entries in `{−1, 0, 1}`, singular ones included); **(S3)** `M₁ * X₁ = 0` under `IsUnit (X₁ᵀ X₁).det`; **(S4)** `IsUnit (Xᵀ X).det → IsUnit (X₁ᵀ X₁).det` and **(S5)** `IsUnit (Xᵀ X).det → IsUnit ((M₁ X₂)ᵀ (M₁ X₂)).det` (672 cells, 0 failures). Hypotheses dropped, first failing cell in enumeration order (entries `−1, 0, 1`, lexicographic): (S3) without its hypothesis fails in 32 of 90 cells, first at `X₁ = [[−1, −1], [−1, −1]]` (singular Gram, so `M₁ = 1` and `M₁ X₁ = X₁`); (S4) without `IsUnit (Xᵀ X).det` fails in 9 of 81, first at `X₁ = 0`, `X₂ = (−1, −1)`; (S5) fails in 25 of 81, first at `X₁ = X₂ = (−1, −1)` (`M₁ X₂ = 0`; claude-ai predicted `X₁ = 0` first — a miss of enumeration order, `(−1, −1)` comes before `0`). (F1) with no hypothesis at all: the witness `X₁ = 0`, `X₂ = (1, 1)`, `y = (1, 3)` (`n = 2`, `k₁ = k₂ = 1`) gives left `[0]` (`Xᵀ X` singular, `L X = 0`) and right `[2]` (`M₁ = 1`, `L X₂ *ᵥ y = 2`). A fact the cells found that the statements do not use: when `Xᵀ X` is singular but `X₁ᵀ X₁` is a unit, both sides of (F1) are `0` in all 109 such trials (no witness in 2000 random tries) — because a dependence `X₁ u + X₂ v = 0` with `X₁` of full column rank forces `v ≠ 0` and `M₁ X₂ v = 0` [inferred, not proved]; so (F1) also holds under the weaker `IsUnit (X₁ᵀ X₁).det` alone, by a rank argument this order does not ask for. |
| 10 | The Frisch–Waugh–Lovell theorem, the route | Derived here (rule 19) from the normal equations, which the library has: `transpose_mulVec_sub_mulVec_leastSquares` (`Xᵀ (y − X (L X y)) = 0` under `IsUnit (Xᵀ X).det`) and `leastSquares_mul_self` (`L X * X = 1`). Write `β = L X *ᵥ y`, `β₁ = β ∘ Sum.inl`, `β₂ = β ∘ Sum.inr`, and split `Xᵀ X β = Xᵀ y` by `transpose_fromCols`, `fromRows_mul_fromCols`, `fromCols_fromRows_eq_fromBlocks`, `fromBlocks_mulVec` and `fromCols_mulVec_sumElim`: the `inl` row is `X₁ᵀ X₁ β₁ + X₁ᵀ X₂ β₂ = X₁ᵀ y`, so `β₁ = L X₁ *ᵥ (y − X₂ β₂)` (S4, `nonsing_inv_mul`); the `inr` row `X₂ᵀ X₁ β₁ + X₂ᵀ X₂ β₂ = X₂ᵀ y` then reads `X₂ᵀ M₁ X₂ β₂ = X₂ᵀ M₁ y`, and with (S1), (S2) this is `(M₁ X₂)ᵀ (M₁ X₂) β₂ = (M₁ X₂)ᵀ (M₁ y)`, whose Gram matrix is a unit (S5), giving (F1) by `nonsing_inv_mul`; (F2) is (F1) with `M₁ᵀ M₁ = M₁`; (F3) is (F1) at every basis vector, or directly by the same block algebra on matrices (`toRows₂`); (F4) substitutes `β₁`. (S1): `(Xᵀ X)⁻¹ᵀ = (Xᵀ X)⁻¹` (`Matrix.transpose_nonsing_inv`, unconditional). (S2): if `X₁ᵀ X₁` is a unit, `L X₁ * X₁ = 1` collapses `(X₁ L X₁) ^ 2`; if not, `L X₁ = 0` (`leastSquares_eq_zero_of_not_isUnit_det`) and `M₁ = 1`. (S3): `X₁ − X₁ (L X₁ X₁) = 0`. (S4): `Xᵀ X = fromBlocks (X₁ᵀ X₁) (X₁ᵀ X₂) (X₂ᵀ X₁) (X₂ᵀ X₂)`, and a unit block matrix has an injective `mulVec` (`mulVec_injective_iff_isUnit`, `isUnit_iff_isUnit_det`), so if `X₁ᵀ X₁ *ᵥ u = 0` then `(X₁ *ᵥ u) ⬝ᵥ (X₁ *ᵥ u) = u ⬝ᵥ (X₁ᵀ X₁ *ᵥ u) = 0` (`dotProduct_mulVec`, `mulVec_transpose`), so `X₁ *ᵥ u = 0` (`dotProduct_self_eq_zero`), so `Xᵀ X *ᵥ Sum.elim u 0 = Sum.elim (X₁ᵀ X₁ *ᵥ u) (X₂ᵀ *ᵥ (X₁ *ᵥ u)) = 0` (`fromBlocks_mulVec`) and `u = 0` (the reviewer supplied the middle step). (S5): the Schur complement of the `(1, 1)` block is `X₂ᵀ X₂ − X₂ᵀ X₁ (X₁ᵀ X₁)⁻¹ X₁ᵀ X₂ = X₂ᵀ M₁ X₂ = (M₁ X₂)ᵀ (M₁ X₂)`, and `det_fromBlocks₁₁` (with `Invertible (X₁ᵀ X₁)` from S4, `isUnit_iff_isUnit_det`, `Matrix.invertibleOfIsUnitDet`) gives `det (Xᵀ X) = det (X₁ᵀ X₁) · det (Schur)`, so the second factor is a unit (`IsUnit.mul_iff`). An alternative for (F3) alone: `invOf_fromBlocks₁₁_eq` gives `(Xᵀ X)⁻¹` in blocks and its bottom block row times `Xᵀ` is `L (M₁ X₂)`; either route is fine if the fragment names its source. The witness for the last statement (§0 row 9) is closed on `Fin 2` without `decide`: the left side by `leastSquares_eq_zero_of_not_isUnit_det` with `Matrix.det_eq_zero_of_row_eq_zero` at row `Sum.inl 0` (the Gram matrix is `Sum`-indexed, so `det_fin_two` does not apply), the right by `residualMaker 0 = 1` and `GaussMarkov`'s public `leastSquares_ones_two` (`leastSquares !![1; 1] = !![1 / 2, 1 / 2]`), then `norm_num`; the private `leastSquares_ones_two_two` is the pattern, not a tool (the reviewer's correction). |
| 11 | Both statement lists elaborated with `sorry` on helios | `/tmp/claude-ai-g10/DraftWolstenholme.lean` (sha256 `d02cc671…a940`; imports `ClassicalLean.NumberTheory.Catalan`, `Mathlib.NumberTheory.Harmonic.Defs`, `Mathlib.NumberTheory.Padics.PadicVal.Basic`, `Mathlib.FieldTheory.Finite.Basic`, `Mathlib.Data.ZMod.Basic`, `Mathlib.Data.Nat.Prime.Factorial`, `Mathlib.Data.Nat.Factorial.BigOperators`; (W1)–(W7) in `namespace ClassicalLean`, and four `example`s: `p = 3` and `p = 2` fail (W2) by `decide`, `p = 5` holds by `decide`, `catalan 5 = 42` by `rw [catalan_eq_centralBinom_div]; rfl`): `lake env lean` with rule 20's four flags, rc 0; seven `sorry` warnings and nothing else; the 28 `#check @name` probes of row 8's Mathlib and library names all resolve (`harmonic`, `harmonic_succ`, `padicValRat.div`, `.of_nat`, `.of_int`, `.mul`, `padicValInt_dvd_iff`, `padicValNat_dvd_iff`, `Nat.Prime.dvd_factorial`, `FiniteField.sum_pow_lt_card_sub_one`, `ZMod.card`, `ZMod.coe_mul_inv_eq_one`, `ZMod.mul_inv_of_unit`, `ZMod.natCast_eq_natCast_iff`, `ZMod.natCast_eq_zero_iff`, `ZMod.castHom`, `Nat.descFactorial_eq_factorial_mul_choose`, `Nat.descFactorial_eq_prod_range`, `Nat.choose_symm_half`, `Nat.centralBinom`, `Nat.succ_mul_centralBinom_succ`, `Finset.prod_range_reflect`, `Finset.sum_range_reflect`, `ClassicalLean.succ_mul_catalan_eq_choose`, `catalan_eq_centralBinom_div`, `Nat.choose_succ_succ'`, `Nat.centralBinom_eq_two_mul_choose`, `ZMod.pow_card_sub_one_eq_one`). Its first run failed on two unknown names, `Nat.Prime.dvd_factorial` and `Nat.descFactorial_eq_prod_range`, which `Catalan`'s closure does not reach: the last two imports were added for them. `/tmp/claude-ai-g10/DraftFWL.lean` (sha256 `f7b82cc2…9c41`; imports `ClassicalLean.Statistics.GaussMarkov`, `Mathlib.Data.Matrix.ColumnRowPartitioned`, `Mathlib.LinearAlgebra.Matrix.SchurComplement`; `residualMaker`, (S1)–(S5), (F1)–(F4) and the no-hypothesis witness, in `namespace ClassicalLean.Statistics` with `open Matrix` and `variable {ι κ₁ κ₂ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ₁] [Fintype κ₂] [DecidableEq κ₁] [DecidableEq κ₂]`): rc 0; ten `sorry` warnings and nothing else; the 30 `#check` probes of row 10's names all resolve (the `fromCols`/`fromRows`/`fromBlocks` lemmas, `invOf_fromBlocks₁₁_eq`, `isUnit_fromBlocks_iff_of_invertible₁₁`, `det_fromBlocks₁₁`, `mulVec_injective_iff_isUnit`, `isUnit_iff_isUnit_det`, `nonsing_inv_apply_not_isUnit`, `mul_nonsing_inv`, `nonsing_inv_mul`, `dotProduct_self_eq_zero`, `dotProduct_mulVec`, `mulVec_transpose`, `transpose_nonsing_inv`, `invertibleOfIsUnitDet`, `IsUnit.mul_iff`, `inv_def`, `det_fin_two`, and the five `GaussMarkov` names). Three earlier runs taught: `1 : Matrix ι ι ℝ` needs `[DecidableEq ι]`, which `GaussMarkov`'s `variable` line does not carry (the new module adds it); `dotProduct_self_eq_zero` is a root-namespace name, not `Matrix.`; the `unusedHypothesis`-style linter flags `[DecidableEq ι]` on (S4), whose statement has no `1` — `omit [DecidableEq ι] in` before it, and the `omit … in` line must precede the docstring, not follow it (a parse error otherwise); two statement lines over 100 characters, wrapped. Porcelain 0 after each run; the final drafts (these hashes, with three and six probes added late for row 8's (d) and (e) and row 10's names) were elaborated last at 2026-09-25T05:31Z (`DraftWolstenholme.run4.log`, `DraftFWL.run4.log` in `/tmp/claude-ai-g10/`: rc 0, 7 and 10 `sorry` warnings, nothing else; log sha256 `3a072e4c…`, 40 lines, and `d904876a…`, 94 lines). So J2's module needs `Catalan` and those six Mathlib imports (`Mathlib.Data.ZMod.Basic` is already in `FieldTheory.Finite.Basic`'s closure, by the reviewer's read of the clone's import lines; it may stay, as G-9 ruled for `Digits.Lemmas`), and J3's needs `GaussMarkov` and those two. |
| 12 | Mathlib v4.34.0 searches (commands below) | `wolstenholme` 0; harmonic numbers with a prime or modulus 1 (a docstring line of `NumberTheory/SumPrimeReciprocals.lean` matching `Primes`). **Correcting order G-9 §0 row 12** (round 28's addendum, item 13): `NumberTheory/Harmonic/` is six files, and not real-analytic throughout — `Harmonic/Defs.lean:23` defines the rational `harmonic : ℕ → ℚ`, `Harmonic/Int.lean:30` proves `padicValRat_two_harmonic` (`v_2 (harmonic n) = −log₂ n`) and `:52` `harmonic_not_int`; `Bounds`, `EulerMascheroni`, `GammaDeriv` and `ZetaAsymp` are the analytic ones. No line of the directory mentions `ZMod`, `≡` or `% p` (0), so no congruence modulo a prime: (W1) can start from Mathlib's `harmonic`, and (W1)–(W7) are new. `[MOD p ^` 2 lines in all of Mathlib, neither a binomial coefficient (`pow_pow_modEq_one`, `FieldTheory/Finite/Basic.lean:681`; `GroupTheory/Sylow.lean:614`). `Data/Nat/Choose/Lucas.lean` is Lucas's theorem modulo `p` (`choose_modEq_choose_mod_mul_choose_div` `:38`), and `padicValNat_choose` (Kummer) is `Padics/PadicVal/Basic.lean:658`: nothing modulo `p ^ 3`. Present: `FiniteField.sum_pow_lt_card_sub_one` (`Finite/Basic.lean:311`), `sum_pow_units` (`:290`), `pow_card_sub_one_eq_one` (`:218`; `ZMod.` form `:611`), `Finset.prod_range_reflect` (`BigOperators/Intervals.lean:153`; `sum_range_reflect` by `to_additive`), `Nat.descFactorial_eq_prod_range` (`Factorial/BigOperators.lean:60`), `Nat.descFactorial_eq_factorial_mul_choose` (`Choose/Basic.lean:288`), `Nat.choose_symm_half` (`:206`), `Nat.centralBinom_eq_two_mul_choose` (`Choose/Central.lean:39`), `catalan` (`Combinatorics/Enumerative/Catalan/Basic.lean:52`; `catalan_eq_centralBinom_div` `:102`, `succ_mul_catalan_eq_centralBinom` `:126`). FWL: `frisch`, `waugh`, `lovell`, partial regression 0; least squares 0; `Matrix/ColumnRowPartitioned.lean` has 24 `fromCols` lemmas (`transpose_fromCols` `:130`, `fromCols_fromRows_eq_fromBlocks` `:167`, `fromCols_mulVec_sumElim` `:205`, `fromRows_mul_fromCols` `:237`, `toRows₂_fromRows` `:83`); `Matrix/SchurComplement.lean`: `fromBlocks₁₁Invertible` `:263`, `invOf_fromBlocks₁₁_eq` `:286`, `isUnit_fromBlocks_iff_of_invertible₁₁` `:355`, `det_fromBlocks₁₁` `:370`; `Matrix/NonsingularInverse.lean`: `isUnit_iff_isUnit_det` `:127`, `nonsing_inv_apply_not_isUnit` `:175`, `mul_nonsing_inv` `:211`, `nonsing_inv_mul` `:217`, `mulVec_injective_iff_isUnit` `:360`, `inv_eq_left_inv` `:459`; `dotProduct_self_eq_zero` (`Matrix/DotProduct.lean:77`), `dotProduct_mulVec` (`Data/Matrix/Mul.lean:761`), `mulVec_transpose` (`:1099`). `Wanted/` has nothing on Wolstenholme, harmonic numbers, regression, Frisch, Waugh, Lovell or Carmichael (0). |
| 13 | `docs/1000.yaml` at v4.34.0 | 1199 entries, 955 with no `decl`, `decls` or `url` (`yaml.safe_load`). Confirmed by search, each with no `decl`, `decls` or `url`: Q1724049 Wolstenholme's theorem, Q1059151 FWL theorem, Q3889376 Carmichael's theorem, Q599876 Cochran's theorem, Q230848 Lamé’s theorem (proved by round 27, not listed), Q608294 max flow min cut, Q928813 Menger's theorem, Q8074796 Zsigmondy's theorem. If J2 lands, the library proves Q1724049's statement in both classical forms; if J3 lands, Q1059151's. Listing either needs a public URL, and is Dustin's decision. |
| 14 | Order G-9's run, from its page and evidence (UTC) | The session opened with `/effort` set to "ultracode (this session only): xhigh + dynamic workflow orchestration", then the prompt. Dustin's three messages: the prompt; `yes plan approved` at 02:43:05Z (`approval` logged 02:43:15Z); `yes` to the push (the push 04:29:35Z). J1 from 01:09Z (`0.src` 01:12:31Z); plan v1 01:45Z; four plan critics in one workflow (their reports 01:59:38Z–02:03:10Z; the page says it "took 17m 6s"); plan v2 02:13Z; the delta critic 02:13–02:29Z; plan v3 02:32:55Z; the J1 report with the plan; approval; the deferred build; the order filed; `f90f392` 02:44:32Z; the two statement reviews in one workflow (reports 03:01:28Z and 03:03:31Z; the page shows its dispatch-log step "Failed to run" — the trailing `ls` of a directory not yet made, addendum item 19); J2 proved 03:10Z, J3 03:16Z; J2's post-proof review (report 03:28:56Z) and J3's (03:37:18Z) in two workflows; `4dd8904` 03:35:10Z; `fcedf53` 03:42:07Z; the records commit `1e63d5b` 03:47:02Z; the Close `6bf3b27` 03:49:15Z; the Close check dispatched 03:50:49Z (three checkers in one workflow, reports 04:05:05Z, 04:05:49Z, 04:09:38Z); the addendum `432aa26` 04:23:27Z; the final report; the push 04:29:35Z. `evidence.log`: 617 lines, 01:12:31Z to 04:29:43Z. **Refusals on the page: 8** — one Edit-tool refusal at about 01:12:44Z (`0.land1` then measured an unedited copy: void), six Edit-tool refusals at about 02:07Z (the v2 drafts; each "File has not been read yet"), one guard refusal of a whole Bash call at about 03:39Z (a stray `python3 -`); each is logged `NOT RUN` in `evidence.log` (12 `NOT RUN` lines in all: those 8, the deferred `lake build`, the batch line, and two `T1`/`T2` test lines), and the report's `grep` counts 8 — rule 30 worked, though seven were logged late (round 27). **One context compaction**, during the Close-check wait (the page's step "Ran 3 commands, read 5 files, compacted the session", between 03:50:49Z and 04:05Z); no work was lost that the records show. Prediction misses the report lists: J2's theorem count 16 against 33 (`omega` auxiliaries), J2's first compile 3 warnings (two deprecated names, `dif_pos`/`dif_neg`, one style), J3's first compile one unsolved `1 % 2 = 1`, the declaration graph 1652 against 1653, pairs 90 against 91, and five prediction misses of addendum item 19: two trailing `ls` exit codes, two `linelen` exit codes over records lines, and four lengths off by a trailing newline. |
| 15 | Order G-9's records against its evidence files, and its report against the page | The twelve review and check files' modification times (`TZ=UTC`): `stmt-j3.md` 03:01:28Z, `stmt-j2.md` 03:03:31Z, `post-j2.md` 03:28:56Z, `post-j3.md` 03:37:18Z, `close-B.md` 04:05:05Z, `close-A.md` 04:05:49Z, `close-C.md` 04:09:38Z, and the critics `compliance.md` 01:59:38Z, `evidence.md` 02:00:23Z, `statements.md` 02:02:34Z, `routes.md` 02:03:10Z, `delta.md` 02:29:21Z — the four reviews as round 28's addendum item 4 gives them, the three Close files as its opening paragraph gives them, and the five critics inside round 27's windows (01:47–02:04Z, 02:13–02:30Z), which give no file times; each before the hash time the rounds give (the reviewer's attribution). `git rev-list --count f90f392^..432aa26` is 6; `EuclidSteps.lean` is 235 lines and `fcedf53` inserts 191 lines into `LucasApparition.lean` and removes 0; the lines under `ClassicalLean/` are 16,655 → 17,081 and the filtered list 863 → 887 — all as the report says. Two things to record: the report's order-table row gives the wall clock as "02:43–04:23", from the approval, where the table's definition (row 3) runs from the filing commit, 02:44:32Z (one minute; corrected in row 3 below); and the report's "Nothing stopped" is true this time — its eight refusals are the page's eight, one for one (checker C found the same from the transcript). Order G-9's own records had five errors the run found (round 27's "Findings that correct the order's records"), none a wrong theorem: the pairs wording (§0 row 6), the tight pairs (`(610, 987)` at 15 steps, not `(233, 377)`), the prime-power cell counts (20 and 16 with `11 ^ 3`), the `Wanted/` claim (it is in the package on helios) and the "prior art: none" claim (`GenContFract.succ_nth_fib_le_of_nth_den`); this order's row 12 keeps the `Wanted/` search and says where the clone's files are. |
| 16 | Carmichael's theorem, measured this cycle (`carmichael_measure.py`, sha256 `5a187976…221b`; exact integers, `sympy` for factoring; output saved beside it) | The elementary shape, cell by cell. With `c_n = ∏_{d ∣ n} F_d ^ μ(n/d)` (Fibonacci cyclotomic numbers): every `c_n` for `n ≤ 400` is an integer and `F_n = ∏_{d ∣ n} c_d`. **Key lemma** (a prime `p ∤ n` dividing `c_n` is primitive for `F_n`): 0 failures for `3 ≤ n ≤ 150`. `p ∣ n` and `p ∣ c_n` with `p` not the largest prime of `n`: exactly `n = 3 · 2 ^ k` with `p = 2` (`n = 6, 12, 24, 48, 96` — the cells run to `n = 150`, so `192` is untested); `p ^ 2 ∣ c_n` with `p ∣ n`: only `(6, 2)` (`n ≤ 150`; the reviewer corrected these three ranges from `400`). Writing `P(n)` for the largest prime factor of `n`: `c_n ≤ P(n)` for `n ≥ 3` only at `n = 3, 5` — but `5 = c_5 = F_5` is itself primitive for `F_5`, so stripping the possible `P(n)` factor is too crude at `n = 5`; by factoring, `F_n` has no primitive prime divisor exactly for `n ∈ {1, 2, 6, 12}` (`n ≤ 120`), the theorem's exceptions. **The size bound**: with Binet's `φ ^ (d − 2) ≤ F_d ≤ φ ^ (d − 1)` (checked `d ≤ 400`), the crude bound `c_n ≥ φ ^ (e(n))` with `e(n) ≥ φ(n) − 2 ^ ω(n)` (checked `n ≤ 400`) exceeds `P(n)` for every `15 ≤ n ≤ 400` (measured; beyond that by growth, to be proved Lean-side); it fails exactly at `n ∈ {3, 4, 5, 6, 10, 12, 14}`, so a finite check of `n ≤ 14` closes the theorem. Lean-side needs, not yet measured: Mathlib's Möbius inversion for products (`ArithmeticFunction`), a Binet lower bound on `Nat.fib` (Mathlib has `Real.coe_fib_eq`), the rank of apparition and `α(p) ≤ p + 1` (round 24), and `decide` on `F_n` for `n ≤ 14`. That is one order's J2 and J3 together, with a new module, not a job beside two others: Close step 1 ranks it first for order G-11 with this row as its measurement. |
| 17 | Order G-9's tools, for J1 item 0 | `~/work/_bump-evidence/g9/ev.sh` sha256 `04786c7f…73b2`; `g9/land.sh` `eee021d1…ebb1` (exports `LC_ALL=C`, reads each `comm`'s exit status); `g9/quotecheck.py` `e0c8a5e3…1ed9`; `g9/inlinecheck.py` (new in G-9's addendum; checks inline quotes against their sources, fire-tested on a planted misquote); `g9/brief_make3.py` (builds briefs quoting rules 16–30 from `HANDOFF.md`). Two slips round 28's addendum item 22 recorded, both measured present: `brief_make3.py` line 14's usage message names `brief_make2.py`; `land.sh` line 82 labels every fragment's quote check `$label-quotes`, so a landing with two fragments logs two lines under one label. `TypeDumpPI.lean` `1fcb69f4…76ff` with `g8_typediff.py` `371eda9a…cb71` are rule 14's pair; `ListTheorems.lean` `383b2b74…6e2d`, `ModuleThmCount.lean` `77def4ec…6af6`. |

Row 3, the six orders. "Wall clock" runs from the order's filing commit to its closing commit,
UTC; "commits" is `git rev-list --count <filing commit>^..<closing commit>`. The first five rows
are order G-9 §0's; the sixth is this cycle's, from the page and git (rows 14 and 15).

| Order | Wall clock | Commits | Modules | Lines under `ClassicalLean/` | Filtered list | Close check | Dustin's decisions |
|---|---|---|---|---|---|---|---|
| 0923 | 09-23 14:09–17:12 (includes a STOP) | 18 | 41 → 44 | 12,446 → 13,069 | → 725 (round 17) | every checkable item met, after findings | the STOP (delegated to claude-ai), the push |
| G-5 | 09-23 18:54–20:34 | 12 | 44 → 45 | → 13,619 | 725 → 746 | every checkable item met, after an evidence-log finding | the plan, the push |
| G-6 | 09-24 00:49–02:04 (J1 from 00:12) | 14 | 45 → 48 | → 14,757 | 746 → 791 | 41 held, 2 failed (records), both remedied | the plan with the credit, the push |
| G-7 | 09-24 15:40–17:42 (J1 from 14:43) | 11 | 48 → 48 | 14,757 → 15,302 | 791 → 816 | 63 held, 9 failed (one type-dump item, eight records and process), 5 pending by design | the plan with step V, the push |
| G-8 | 09-24 21:18–23:21 (J1 from 19:43, round 25's reference file; session from about 19:39) | 10 | 48 → 49 | 15,302 → 16,655 | 816 → 863 | 213 held, 21 failed (18 distinct: 13 records corrections, 2 departures ruled, 3 process lapses), 7 not checkable | the plan (v3), the push |
| G-9 | 09-25 02:44–04:23 (J1 from 01:09; approval 02:43) | 6 | 49 → 50 | 16,655 → 17,081 | 863 → 887 | 26 findings, 18 distinct, written up as 23 items (13 records corrections, 3 rulings, 7 process lapses), 5 MAJOR, 0 BLOCKER; none in a proof, statement or gate | the plan (v3), the push |

Row 12's searches, from the Mathlib clone's root (`Wanted/` and `docs/` are in the clone, and on
helios in `.lake/packages/mathlib/`, as round 27 measured):

```
grep -rniE 'wolstenholme' Mathlib --include=*.lean | wc -l                                       # 0
grep -rniE 'harmonic' Mathlib --include=*.lean | grep -ciE 'ZMod|prime|mod '                     # 1, a docstring line of NumberTheory/SumPrimeReciprocals.lean ("Primes")
ls Mathlib/NumberTheory/Harmonic/                                                                # Bounds Defs EulerMascheroni GammaDeriv Int ZetaAsymp
grep -rnE 'ZMod|≡|% p' Mathlib/NumberTheory/Harmonic/*.lean | wc -l                              # 0
grep -rnE '\[MOD p \^' Mathlib --include=*.lean | wc -l                                           # 2, neither a binomial coefficient
grep -nE '^(theorem|lemma) ' Mathlib/Data/Nat/Choose/Lucas.lean | wc -l                          # 16 (14 theorem, 2 lemma): ten congruences modulo p, six gcd lemmas about prime-power indices; none modulo p^3 (the reviewer corrected 15 to 16)
grep -rnE 'theorem sum_pow_lt_card_sub_one' Mathlib --include=*.lean                             # FieldTheory/Finite/Basic.lean:311
grep -rniE 'frisch|waugh|lovell|partialling|partial regression' Mathlib --include=*.lean | wc -l  # 0
grep -rniE 'least.?squares' Mathlib --include=*.lean | wc -l                                     # 0
grep -rnE '^(theorem|lemma) .*fromCols' Mathlib/Data/Matrix/ColumnRowPartitioned.lean | wc -l    # 24
grep -nE '^(theorem|lemma|def) (invOf_fromBlocks₁₁_eq|isUnit_fromBlocks_iff_of_invertible₁₁|det_fromBlocks₁₁)' Mathlib/LinearAlgebra/Matrix/SchurComplement.lean | wc -l   # 3
grep -rniE 'wolstenholme|frisch|waugh|lovell|regression|carmichael|harmonic' Wanted | wc -l      # 0
```

**Predict J1 from `HANDOFF.md` §1 and §6, `records/orders/INDEX.md`, `records/CLAIMS.md` and
`push.log`, not from this table** — except J1 items 6, 7, 9, 10, 11 and 12, which re-run claude-ai's
measurements and predict from rows 4–13 and 17. §6 lags the last push by design, so `push.log`
predicts item 4.

---

## 1. Rules for this session

- **`HANDOFF.md` §6 holds**: rules 1–30 and the standing answers, with §0, §3, §4 and §5, and
  README Rules 1 to 4. They are not repeated here.
- **Dustin does not read code or files.** Everything he needs goes in your chat reply. When he must
  act, give the exact command, the box, and the output you expect.
- **Predict, then measure.** Write the expected value, or "no prediction", before any command that
  prints a count, a hash or an rc. Report predicted beside actual.
- **Run every command from `~/work/classical-lean`**, or give `git -C` and absolute paths.
- **Four rules learned in order G-9's run** (§0 rows 14 and 15, round 27, round 28's addendum),
  numbered as J2's records step will file them in `HANDOFF.md` §6. In this order "rule N" means
  `HANDOFF.md` §6's rule N, 1–34; `records/README.md`'s rules are written "README Rule N".
  31. **No statement of a job is drafted until the job's last search and cell has run**, the ones a
     plan critic adds included; rule 21 says "before any of its statements is drafted", and order
     G-9's J1 ran J3's random trials, the definition reads and the critics' extra cells after
     the first drafts (round 28's addendum, item 17, a MAJOR finding; round 27). A cell that a
     review adds after a draft is run, logged, and the draft re-hashed and re-elaborated after it,
     with the times (rule 18). J1 item 12 checks it by mtime against the log.
  32. **Every write, hash and edit of an evidence or records file runs through the helper** (rule
     23), or is listed in the plan and the fragment before the commit that carries it: order G-9
     ran five such commands outside it (round 28's addendum, item 20: a `sha256sum`, a `sed`, an
     editor derivation, a `cp` of the log, a heredoc append).
  33. **A workflow returns each report's text with its sha256, and the saving command compares
     the two before the report is read** (rule 17): nothing in orders G-5 to G-9 had checked that a
     saved review was the text its agent returned, until G-9's addendum compared all twelve
     against the harness's journal (`jcmp-all`; round 28's addendum, item 23).
  34. **Every inline quote in a fragment — a phrase in quotation marks or backticks attributed
     to a document — is checked by script against its source, as block quotes are** (rule 22),
     with a planted misquote as the negative control (`g9/inlinecheck.py`; round 28's addendum,
     items 11 and 23: three inline quotes in round 28 cut or paraphrased their sources and the
     block-quote check never saw them).
- **Environment facts** (`HANDOFF.md` §6's standing answers, dated orders G-7 to G-9, and order
  G-9's run): write every commit message to a file and commit with `git commit -F <file>`; write
  scripts to files in the evidence directory and run them as `python3 <file>`; the local guard
  refuses inline `python3 -c`, chained in-place edits, and any Bash call that contains `python3 -`
  reading from stdin; helios's `BASH_ENV` switches `pipefail` on; a read-only status runs as
  `GIT_OPTIONAL_LOCKS=0 git status`; read evidence times with `TZ=UTC`; run `sort`/`comm` under
  `LC_ALL=C`. New from order G-9's run (§0 row 14): **the Edit tool refuses a file that has not
  been read in the session** ("File has not been read yet") — seven of G-9's eight refusals; read a
  file before editing it, and never run a measurement of a file in the same call as its edit
  (`0.land1` measured the unedited copy). Core deprecates `dif_pos`/`dif_neg` for
  `dite_eq_left`/`dite_eq_right` and Mathlib `Nat.digits_len` for `Nat.length_digits` (round 27).
  A workflow's journal keeps each agent's full returned text (G-9's final note). From this
  cycle's drafts (§0 row 11): `omit [inst] in` goes before a declaration's docstring; a matrix `1`
  needs `DecidableEq` on its index type.
- **Steps and commits.** Land a step as its own commit when it was proved as a step. If a module is
  proved whole before its first landing, land it in one commit and record its step structure in
  the fragment (rule 18); do not cut step commits from a finished file.
- **Gate 6.** J2 and J3 each create one module. The rules of order G-6 §1 apply to both: until a
  round fragment names the new file, write its path or bare filename into none of the files gate
  6 searches (`PROVENANCE.md`, `records/rounds/*.md`, `records/orders/*.md`, `INDEX.md` included;
  `CLAIMS.md` is not searched and does name them, as J1 step 3 says); show `check_records.py`
  FAIL on each with its import line in place; then commit it together with the fragment that
  names it. This order does not name them; the plan does (J1's Done-means).
- **Git, reviews and builds** as in order G-5 §1:
  - commit locally, never push to GitHub or add a remote, park and never delete;
  - reach DSMain only with `GIT_SSH_COMMAND='ssh -o BatchMode=yes -o ConnectTimeout=15'`; if DSMain
    is unreachable, record "unreachable" and carry on; never touch the VPN, routes or ssh
    configuration;
  - a fresh cold reviewer before and after proving; builds one at a time; subagents never run `lake`.

## 2. Standing answers — do not stop to ask these

- **Everything in `HANDOFF.md` §6's standing answers** still holds.
- **The push record.** J1 compares `HANDOFF.md` §6 with `push.log` and the `dsmain/master` reflog.
  J2's records step adds the dated line for `196a87d..432aa26` (2026-09-25T04:29:35Z, on Dustin's
  yes to order G-9's push question), taken from `push.log` and the reflog.
- **Order G-9's three rulings on Dustin's delegation stand** (round 28's addendum, items 14–16):
  a late name check stands for a skipped one when it is run and recorded; the void runs as ruled;
  and **the Close commit sets the `INDEX.md` row's State to "Close check pending" alone, and the
  addendum's commit sets the State from the verdict** (item 16, ruled for this order onward).
  His veto stays open.
- **Where the new theorems live**, pre-answered; a different home is allowed if the plan says why
  and the import closure is recorded:
  - J2, all of (W1)–(W7) and the `example`s, in one new module under `NumberTheory/`, named in
    the plan (§1's gate-6 rules), which imports `ClassicalLean.NumberTheory.Catalan` (for (W5);
    `Catalan` imports `Mathlib.Combinatorics.Enumerative.Catalan.Basic` and no library module) and
    the six Mathlib modules of §0 row 11, and no other library module; `ClassicalLean.lean` gains
    its one import line. This bridges the island `Catalan` (`usedBy= 1`); islands become two.
  - J3, `residualMaker`, (S1)–(S5), (F1)–(F4) and the witness, in one new module under
    `Statistics/`, named in the plan, which imports `ClassicalLean.Statistics.GaussMarkov`,
    `Mathlib.Data.Matrix.ColumnRowPartitioned` and `Mathlib.LinearAlgebra.Matrix.SchurComplement`,
    and no other library module (`GaussMarkov` imports `Mathlib.Analysis.Matrix.Order` and
    `Mathlib.LinearAlgebra.Matrix.Notation` and no library module); `ClassicalLean.lean` gains its
    one import line; `GaussMarkov` becomes `usedBy= 2`.
  Neither closes a cycle: both homes use no library module. J1 checks it (item 7).
- **`residualMaker`'s definition is content, its name is not.** It is `1 − X₁ * leastSquares X₁`
  (§0 row 9), over the library's `leastSquares`; the plan may name it otherwise (Mathlib has no
  such object; the statistics name is "annihilator" or "residual maker" matrix).
- **The hypothesis of (F1)–(F4) is `IsUnit ((fromCols X₁ X₂)ᵀ * fromCols X₁ X₂).det`**, the
  classical one. §0 row 9's weaker form (`IsUnit (X₁ᵀ X₁).det` alone, both sides `0` when `X` is
  singular) is not asked for; the plan may add it as a separate theorem if the rank argument is
  proved, and then says so in the fragment.
- **Names are suggestions** for the statement reviews; Mathlib's naming conventions decide.
- **Anything that needs Dustin:** ask in one line, recommended answer first, and keep working on
  whatever does not depend on it. Pushing, publishing, listing anything in Mathlib's
  `docs/1000.yaml`, offering anything to Mathlib and retiring modules are his.

---

## J1 — open and re-measure (read-only)

**Goal.** Know that order G-9 is closed and that the tree is what its records say, and record the
searches and junk cells of J2 and J3 (rules 21 and 31), before touching the tree.

**Scope.** Read-only in the repository. Write only under `~/work/_bump-evidence/`: `g10/`, and after
approval `g10-before/`. Run what plan mode allows. List the rest with predictions, marked "deferred".

**Measure, predicting each value first:**

0. **The tools first** (rule 23). Copy `g9/ev.sh`, `g9/land.sh`, `g9/quotecheck.py`,
   `g9/inlinecheck.py` and `g9/brief_make3.py` to `g10/`, byte for byte except: the one
   executable path in each shell tool becomes `g10` (`land.sh`'s `E=` line; `ev.sh`'s `EV=` line;
   their header comments may keep their `g9` text); `brief_make3.py`'s usage message names
   itself, and it quotes rules 16–34: 16–30 verbatim from `HANDOFF.md` §6 and, until J2's records
   step has filed them, 31–34 verbatim from this order's §1 (afterwards all nineteen from
   `HANDOFF.md`) — the one source outside `HANDOFF.md` that rule 26 allows here, as G-9's briefs
   did for rules 26–30; the fragment names it; it refuses a range it cannot find in either source, as the G-9 copy did, and the
   fail test asks it for rules 16–35 (the reviewer's finding: as written before, J2's statement
   review could not have quoted 31–34); `land.sh`'s quote-check label
   carries the fragment's name (`<label>-quotes-<n>` or the file's stem), so two fragments in one
   landing log two labels (§0 row 17). Record all files' sha256 before and after. Fail-test them,
   predictions first: `ev.sh`'s eleven tests of round 25; `land.sh`'s cases of rounds 25 and 27
   on a throwaway clone with stub gates, plus one landing that lists two fragments (two distinct
   quote labels); `inlinecheck.py` on a planted misquote (fails) and on round 28's addendum
   (passes); `brief_make3.py` with the wrong range (refuses). The session's own workflow scripts (the
   ones G-9's session wrote in its session directory, or fresh ones for this session; not the
   Claude Code configuration, which stays untouched) that dispatch the reviews and the Close check
   return each report's text with its sha256 (rule 33);
   the saving command compares the two and is fire-tested on a planted one-word change before
   J2's statement review is dispatched; record the scripts' paths and sha256 in `g10/`. Run every
   later command through `ev.sh`; the gate runner and the commit step call it, and a commit runs only when all six gates
   exited 0 in the same run. A guard or tool refusal is logged `NOT RUN` in the next helper call
   (rule 30).
1. `records/orders/INDEX.md` row `G-9`: its state, and what landed. `CLAIMS.md`: no open row.
2. `lean-toolchain` and `lakefile.toml` `rev`: expect v4.34.0.
3. `GIT_OPTIONAL_LOCKS=0 git -C ~/work/classical-lean status --short`: expect nothing.
4. `git -C ~/work/classical-lean rev-parse master dsmain/master`, and
   `GIT_SSH_COMMAND='ssh -o BatchMode=yes -o ConnectTimeout=15' git -C ~/work/classical-lean ls-remote dsmain master`:
   predict from `push.log`'s last push line, or record "unreachable". Compare §6's push list with
   `push.log` and the reflog, and name every push §6 lacks (expect one: G-9's).
5. The six commands in `HANDOFF.md` §1, copied from it. Predict from its snapshot. Gate 1 is
   deferred until approval, as in orders G-8 and G-9; a read-only probe stands in for it.
6. **Appendix A.** Write its four files into `~/work/_bump-evidence/g10/claude-ai/`, check each
   sha256 against the appendix, and run them as their headers say. Predict from §0 rows 4–6:
   1673 constants, 50 modules, 3 islands by name, `Catalan` with `usedBy= 0 uses= 0`,
   `GaussMarkov` with `usedBy= 1 uses= 0`; `DupCheck: 5 TWIN line(s), 0 SWAP line(s)`;
   `pairs.py`'s first line `modules=50 edges=83 rare_df<=3 pairs_without_edge_sharing_rare=91`.
7. **The import checks of §2**, Lean-side (`env.header.moduleNames`, positive and negative
   control, as `g9/ImportCheckEuclid.lean` does): `Catalan` loaded alone reaches
   `Mathlib.Combinatorics.Enumerative.Catalan.Basic` and no library module; predict from §0 row
   11's first-run failures that it does not reach `Mathlib.Data.Nat.Prime.Factorial` or
   `Mathlib.Data.Nat.Factorial.BigOperators`, and from the reviewer's read of the clone's import
   lines that it does not reach `Mathlib.NumberTheory.Harmonic.Defs` either; `GaussMarkov` loaded
   alone reaches `Mathlib.Analysis.Matrix.Order` and no library module, reaches
   `Mathlib.LinearAlgebra.Matrix.SchurComplement` (the reviewer's read: seven public imports deep
   from `Analysis.Matrix.Order`) and does not reach `Mathlib.Data.Matrix.ColumnRowPartitioned`;
   an import that adds nothing stays, as G-9 ruled for `Digits.Lemmas`, and the fragment says so.
8. The number of files under `ClassicalLean/` and `ClassicalLean.lean` whose line 4 is exactly
   `Authors: Dustin [surname], Claude (Anthropic)`: expect 51.
9. **Rule 20's flags.** Re-run order G-8's `FlexTest.lean` (`g8/FlexTest.lean`) once with plain
   `lake env lean` and once with the four options as flags: 0 warnings, then 2 `flexible`.
10. **The evidence tools.** sha256 of `~/work/_bump-evidence/TypeDumpPI.lean`, `g8_typediff.py`,
    `ListTheorems.lean`, `ModuleThmCount.lean`, `g9/ev.sh`, `g9/land.sh`, `g9/quotecheck.py`,
    `g9/inlinecheck.py`, `g9/brief_make3.py`: predict the seven §0 row 17 gives, the rest "no
    prediction", and record them for round 29.
11. **J2's and J3's searches and junk cells (rules 21 and 31)**, written under `g10/` before the
    plan drafts any statement:
    - if `/tmp/claude-ai-g10/` is still on helios, copy its two drafts and two `run4` logs into
      `g10/claude-ai/` and check their sha256 against §0 row 11; if it is not, record "not on
      helios", as round 27 did for G-9's;
    - re-run §0 row 12's commands over `.lake/packages/mathlib/` (`Mathlib`, `Wanted` and `docs`
      are all there: round 27), and add shape searches: for J2 at least `harmonic`,
      `padicValRat` with `harmonic`, `FiniteField.sum_pow_lt_card_sub_one`, `sum_pow_units`,
      `ZMod.pow_card_sub_one_eq_one`, `Finset.prod_range_reflect`, `Nat.descFactorial_eq_prod_range`,
      `Nat.choose_symm_half`, `Nat.centralBinom_eq_two_mul_choose`, `catalan_eq_centralBinom_div`,
      `succ_mul_catalan_eq_centralBinom`, `ZMod.natCast_eq_natCast_iff`, `ZMod.castHom`, and any
      Mathlib congruence of a binomial coefficient modulo a prime power (`choose` with `MOD` and
      `^`); for J3 at least every `fromCols`/`fromRows`/`toRows₂`/`fromBlocks` lemma of row 10,
      `invOf_fromBlocks₁₁_eq`, `det_fromBlocks₁₁`, `isUnit_fromBlocks_iff_of_invertible₁₁`,
      `Matrix.transpose_nonsing_inv`, `mulVec_injective_iff_isUnit`, `IsUnit.mul_iff`,
      `Matrix.invertibleOfIsUnitDet`, and any Mathlib projection or idempotent-matrix lemma
      (`IsIdempotentElem` with `Matrix`; `Projection`). Record every command and count.
    - read every Mathlib and library definition the statements use, and the theorems their routes
      rest on (rule 2): `harmonic` (and `harmonic 0 = 0`, `harmonic_succ`), `padicValRat` (and its
      value at `0`), `padicValNat`, `Nat.centralBinom`, `catalan` (Mathlib's, and the library's
      `catalan_eq_choose_div`, `succ_mul_catalan_eq_choose`), `Nat.ModEq`, `ZMod` and its `Inv`
      (`ZMod.inv` is `Nat.gcdA` of the value: `0⁻¹ = 0` (`ZMod.inv_zero`) and
      `a * a⁻¹ = Nat.gcd a.val n` (`ZMod.mul_inv_eq_gcd`), so a nonzero non-unit's inverse is not
      `0` — `(2 : ZMod 4)⁻¹ = 1`; the route inverts only units of `ZMod (p ^ 3)`, and `x⁻¹` in
      `ZMod p` for prime `p` is the field inverse; the reviewer's correction),
      `Nat.descFactorial`, `FiniteField.sum_pow_lt_card_sub_one`; `Matrix.fromCols`,
      `Matrix.toRows₂`, `Matrix.fromBlocks`, `Matrix.inv` (`nonsing_inv`, `0` at non-units),
      `Matrix.det_fromBlocks₁₁`, `Matrix.fromBlocks₁₁Invertible`, the library's `leastSquares`,
      `leastSquares_mul_self`, `leastSquares_eq_zero_of_not_isUnit_det`,
      `transpose_mulVec_sub_mulVec_leastSquares`, `isUnit_det_transpose_mul_self_of_mul_eq_one`.
    - junk cells, random plus constructed (rule 3), each script predicted first: for J2 the cells of
      §0 rows 7 and 8 (`p = 2`, `p = 3`, the composite control, the pairing identities in
      `ZMod (p ^ 3)`, the two sums in `ZMod p` at `p = 3` where they fail, the Catalan arithmetic at
      `p = 2, 3`); for J3 the cells of §0 row 9 (the singular cases under Mathlib's `0` inverse,
      `k₁ = 0` and `k₂ = 0`, `X₁ = 0`, `X₂ = X₁`, the first failing cells of (S3)–(S5), the
      no-hypothesis witness).
12. **Rule 31's gate.** Before any draft is written, log the last search and cell line; the
    drafts' `TZ=UTC` mtimes must follow it, and a cell added later is logged with the draft's
    re-hash and re-elaboration after it. The plan's J1 report says which cells, if any, ran after
    a draft (rule 18).

**If order G-9 is not closed, STOP and report.**

**Done-means.** A predicted-beside-actual table in the chat, with every miss explained. Then one plan
for J2 and J3, with their statements drafted after items 11 and 12, naming both new modules, and
wait for approval. The plan ends with Dustin's decision in one line, recommended answer first:
- "Recommended: yes — approve this plan."

**After approval, in this order:**

1. **Run the deferred commands.** STOP before J2 on any miss you cannot explain.
2. **File the order:**
   `mv -n ~/Cowork/lean-orders/20260925T060100Z__claude-ai__order-g10-wolstenholme-fwl.md ~/work/classical-lean/records/orders/ && test ! -e ~/Cowork/lean-orders/20260925T060100Z__claude-ai__order-g10-wolstenholme-fwl.md && test -f ~/work/classical-lean/records/orders/20260925T060100Z__claude-ai__order-g10-wolstenholme-fwl.md`.
3. **Add the records rows, then commit exactly three paths:** the filed order,
   `records/orders/INDEX.md` and `records/CLAIMS.md`.
   - `INDEX.md`: a row for `G-10`, naming no new file.
   - `CLAIMS.md`: a row naming the modules J2 and J3 write (both new modules by the plan's names,
     `ClassicalLean.lean` for its two import lines) and the records paths: `HANDOFF.md`,
     `ROADMAP.md`, the round 29 and 30 fragments, `CLAIMS.md` and `INDEX.md`.
4. **Take the "before" evidence on a clean tree** into `~/work/_bump-evidence/g10-before/`: the
   type dump (`TypeDumpPI.lean` with `g8_typediff.py`, rule 14 as amended), the raw and filtered
   name lists, `ModuleThmCount`, and item 6's four outputs. J2 and J3 diff against these.

**Undo:** revert J1's commit and restore the order file to `~/Cowork/lean-orders/` from git (round
27's correction of order G-9's J1 Undo line); the evidence tools live outside the repository.

---

## J2 — Wolstenholme's theorem

**Goal.** Wolstenholme's theorem (1862) in both classical forms — `C(2p − 1, p − 1) ≡ 1 (mod p³)`
and `p² ∣` the numerator of `H_{p−1}` — for every prime `p ≥ 5`, with the central form
`C(2p, p) ≡ 2 (mod p³)` and the Catalan corollary that gives the island `Catalan` its first user
(`docs/1000.yaml` Q1724049, title only, §0 row 13). It is `HANDOFF.md` §3's fourth item, and the
first congruence modulo a prime power in the library.

**Scope.**
- One new module under `NumberTheory/`, named in the plan (§1's gate-6 rules; §2's home): (W1)–(W7)
  and the `example`s, and a docstring that records the searches (§0 row 12), the prior art (none
  in Mathlib; Mathlib's `Harmonic/Int.lean` is credited as the related work; the route is the
  pairing route, derived here from the cells) and the correction to order G-9 §0 row 12. It
  imports `ClassicalLean.NumberTheory.Catalan` and §0 row 11's six Mathlib modules; the header
  with the current Authors line; one import line in `ClassicalLean.lean`; the Lean-side import
  closure with its positive and negative control (§2).
- `HANDOFF.md` §3 and §6, `ROADMAP.md` §2 (a new row, `2.14`, in the form of the `DONE` rows) and
  §1.15 (islands three → two, `Catalan` bridged by the new module), records. Round 29's fragment
  opens with the first J2 commit.

**The statements** (content fixed by §0 rows 7 and 8; `(p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p)`
throughout; the names are suggestions):

1. **(W1)** `2 ≤ padicValRat p (harmonic (p - 1))`.
2. **(W2)** `(2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]`.
3. **(W3)** `(2 * p).choose p ≡ 2 [MOD p ^ 3]`, and **(W4)** `p.centralBinom ≡ 2 [MOD p ^ 3]`.
4. **(W5)** `catalan p ≡ 2 + 2 * p ^ 2 - 2 * p [MOD p ^ 3]` — the module's use of
   `NumberTheory/Catalan` (`succ_mul_catalan_eq_choose`).
5. **(W6)** `∑ i ∈ Finset.Icc 1 ((p - 1) / 2), ((i : ZMod p) * ((p : ZMod p) - i))⁻¹ = 0`.
6. **(W7)** `∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p) ^ 2)⁻¹ = 0`.
7. The `example`s: (W2) fails at `p = 2` and `p = 3` (`decide`), holds at `p = 5` (`decide`), and
   `catalan 5 = 42`.
   State each with `5 ≤ p`; §0 row 7 records the cell at `p = 2` and `p = 3` that fails without it.
   (W6) and (W7) may be stated over `Finset.range` or as sums over `ZMod p` if the plan says why.

**Method.**

1. **Statement review before proving** (rule 16). The searches and junk cells are J1 item 11's
   (rules 21 and 31). Draft every J2 statement after J1 item 12's line, elaborate them with `sorry`
   under rule 20's flags in the module's scope, and send the list to one cold statement review
   whose brief is built by script and quotes rules 16–34 (rules 24 and 26). Its verdict is in
   before any J2 proof is written.
2. **The route** (§0 row 8): (a)–(d) for (W2), in `ZMod (p ^ 3)` with `(p − 1)!` a unit and the
   pairing `j ↔ p − j`; (W7) from `FiniteField.sum_pow_lt_card_sub_one`; (W6) from (W7) by the
   half-sum identity; (W3) from (W2) by `choose_symm_half`; (W4) from (W3); (W5) from (W3) by the `(p + 1)` unit;
   (W1) from (c)–(d) through the numerator `N = p · M` and `padicValRat.div`. (W5)'s proof names
   `ClassicalLean.succ_mul_catalan_eq_choose` (or `catalan_eq_choose_div`), not Mathlib's
   `succ_mul_catalan_eq_centralBinom`: the island is bridged by a value-level use of a `Catalan`
   constant, which Done-means 4 measures (the reviewer's finding). Another route is fine if the
   fragment names its source (the Vieta route of §0 row 8 is measured and not proposed).
3. **Land** in one commit if the module is proved whole (§1), a post-proof review of every new
   declaration before it (rule 13), quotes script-checked (rules 22 and 34). Gate 6's sequence
   (§1): the module and its import line in place, `check_records.py` shown FAIL on it, then the
   fragment section that names it, then one commit.
4. **Records** (after step 3 has landed; each line records only what landed).
   - `HANDOFF.md` §6: §1's rules 31–34, each with its date and source; the lead-in names six
     orders (0923: 1–7; G-5: 8–15; G-6: 16–19; G-7: 20–25; G-8: 26–30; G-9: 31–34). The dated
     push line of §2. A standing answer for the Edit tool's read-before-edit refusal and the
     `INDEX.md` Close-commit ruling (§1, §2).
   - `ROADMAP.md`: row `2.14`, Wolstenholme's theorem, `DONE`, with §0 row 12's searches and the
     `p = 2, 3` cells of §0 row 7; a dated line in §1.15 (the new module uses `Catalan`; islands
     two).
   - `HANDOFF.md` §3: the fourth item done, and §3's item 4 paragraph (with its dated correction)
     closed by a dated line.
   - Complete round 29's fragment (README Rule 1).

**Done-means.**
1. The six gates pass on a clean tree, with 0 warnings and 0 vocabulary hits.
2. Every new theorem is within the kernel trio. The statement review and the post-proof review are
   saved with their returned sha256 (rules 17 and 33) and quoted in round 29's fragment, every
   quote script-checked (rules 22 and 34).
3. The type dump against J1's evidence shows only additions, judged up to proof irrelevance
   (rule 25).
4. Appendix A on the landed tree: 51 modules, islands 2 (`CompositumDiscriminant`, `Tolerance`),
   the new module `uses= 1` (`Catalan`) and `Catalan` `usedBy= 1`; `DupCheck: 5 TWIN line(s),
   0 SWAP line(s)`.
5. The fragment carries the searches, the junk cells, the route with its sources, the per-module
   counts (rule 27's census beside the prediction), the rule-31 times (J1 item 12), and the
   Lean-side import closure of the new module with its two controls.
6. No `sorry` ships. A statement that did not close stays out of the file and is described in
   `HANDOFF.md` §3. As routed, (W2) depends on (W6), (W6) on (W7); (W3) on (W2); (W5) on (W3);
   (W4) on (W3); (W1) on (W6); (W7) on nothing else in J2.

**Undo:** yes — `git revert` of the one commit (it removes the module and its import line).

---

## J3 — The Frisch–Waugh–Lovell theorem

**Goal.** The Frisch–Waugh–Lovell theorem (Frisch and Waugh 1933, Lovell 1963): in the regression
of `y` on `[X₁ X₂]`, the coefficients of `X₂` are those of the regression of `M₁ y` on `M₁ X₂`,
where `M₁ = 1 − X₁ (X₁ᵀ X₁)⁻¹ X₁ᵀ` residualises on `X₁`; the residuals agree; and the matrix form.
It is the first half of `HANDOFF.md` §3's third item (Cochran's theorem is the second, not in this
order), as matrix algebra over round 20's `leastSquares`; `docs/1000.yaml` Q1059151, title only
(§0 row 13).

**Scope.**
- One new module under `Statistics/`, named in the plan (§1's gate-6 rules; §2's home):
  `residualMaker`, (S1)–(S5), (F1)–(F4), the no-hypothesis witness, and a docstring that records
  the searches (§0 row 12), the prior art (none in Mathlib; the route is derived here from the
  normal equations the library has) and the weaker-hypothesis fact of §0 row 9 as a remark, labelled inferred unless the plan proves
  it (§2). It
  imports `ClassicalLean.Statistics.GaussMarkov`, `Mathlib.Data.Matrix.ColumnRowPartitioned` and
  `Mathlib.LinearAlgebra.Matrix.SchurComplement`; the header with the current Authors line; one
  import line in `ClassicalLean.lean`; the Lean-side import closure with its controls (§2).
  `GaussMarkov` is read-only.
- `HANDOFF.md` §3 (the third item's first half done) and `ROADMAP.md` §2.9 (a dated line) and a new
  row `2.15` in the form of the `DONE` rows. Records. Round 30's fragment. Every other module is
  read-only.

**The statements** (content fixed by §0 row 9; `{ι κ₁ κ₂ : Type*} [Fintype ι] [DecidableEq ι]
[Fintype κ₁] [Fintype κ₂] [DecidableEq κ₁] [DecidableEq κ₂]`, `X₁ : Matrix ι κ₁ ℝ`,
`X₂ : Matrix ι κ₂ ℝ`, `y : ι → ℝ`, `h : IsUnit ((fromCols X₁ X₂)ᵀ * fromCols X₁ X₂).det`; the
names are suggestions):

1. **The definition.** `residualMaker X₁ : Matrix ι ι ℝ := 1 - X₁ * leastSquares X₁` (§2).
2. **(S1)** `(residualMaker X₁)ᵀ = residualMaker X₁` and **(S2)**
   `residualMaker X₁ * residualMaker X₁ = residualMaker X₁`, no hypothesis.
3. **(S3)** under `IsUnit (X₁ᵀ * X₁).det`: `residualMaker X₁ * X₁ = 0`.
4. **(S4)** under `h`: `IsUnit (X₁ᵀ * X₁).det`; **(S5)** under `h`:
   `IsUnit ((residualMaker X₁ * X₂)ᵀ * (residualMaker X₁ * X₂)).det`.
5. **(F3)** under `h`: `(leastSquares (fromCols X₁ X₂)).toRows₂ = leastSquares (residualMaker X₁ * X₂)`.
6. **(F1)** under `h`: `(leastSquares (fromCols X₁ X₂) *ᵥ y) ∘ Sum.inr = leastSquares (residualMaker X₁ * X₂) *ᵥ (residualMaker X₁ *ᵥ y)`,
   and **(F2)**, the same with `y` on the right.
7. **(F4)** under `h`: `y - fromCols X₁ X₂ *ᵥ (leastSquares (fromCols X₁ X₂) *ᵥ y) = residualMaker X₁ *ᵥ y - (residualMaker X₁ * X₂) *ᵥ (leastSquares (residualMaker X₁ * X₂) *ᵥ (residualMaker X₁ *ᵥ y))`.
8. **The witness**: `¬ ∀ (X₁ X₂ : Matrix (Fin 2) (Fin 1) ℝ) (y : Fin 2 → ℝ), (F1)'s equation`, by
   `X₁ = 0`, `X₂ = ![![1], ![1]]`, `y = ![1, 3]` (§0 row 9).
   State (S3)–(S5) and the witness with the weakest hypotheses the proof allows; (F1)–(F4) keep
   §2's hypothesis, and the weaker form, if proved, is a separate theorem (§2). §0 row 9 records
   which hypothesis each needs and the first cell that fails without it. The witness's docstring
   says that `h` cannot be dropped (at the witness both Gram matrices are singular), not that
   `IsUnit (X₁ᵀ X₁).det` cannot — the draft's wording is the reviewer's finding.

**Method.**
1. The searches and junk cells are J1 item 11's (rules 21 and 31).
2. **Statement review before proving** (rule 16), under rule 20's flags, with a brief built by
   script (rules 24 and 26).
3. **The route** (§0 row 10): the normal equations split into blocks; (S1) from
   `transpose_nonsing_inv`; (S2) by cases on `IsUnit (X₁ᵀ X₁).det`; (S4) by injectivity of
   `mulVec`; (S5) by `det_fromBlocks₁₁`; (F1) by cancelling the unit Gram matrix of `M₁ X₂`; (F2),
   (F3), (F4) from (F1) and (S1)–(S3). Another route is fine if the fragment names its source
   (`invOf_fromBlocks₁₁_eq` for (F3) is measured present).
4. Land in one commit if the module is proved whole (§1); a post-proof review before it (rule 13);
   a fix touching a proof line gets its delta check (rule 29). Gate 6's sequence as J2's.
5. **Records**: `HANDOFF.md` §3 and `ROADMAP.md` as Scope says; round 30's fragment.

**Done-means.**
1. Every landed commit passes the six gates with 0 warnings, and every theorem is within the kernel
   trio.
2. No `sorry` ships. A statement that did not close stays out of the file and is described in
   `HANDOFF.md` §3. As routed, (F1) depends on (S1)–(S5); (F2) and (F3) on (F1) and (S1)–(S2); (F4) on
   (F1), (S1)–(S2) and (S4); (S5) on (S1), (S2) and (S4); (S1), (S2), (S3), (S4) and the witness on
   nothing else in J3. The fragment records the graph as proved if it differs.
3. Both reviews are saved with their returned sha256 and quoted in round 30's fragment (rules 17,
   22, 33 and 34). The fragment carries the searches, the junk cells, the route and its source, the
   per-module count (rule 27's census beside the prediction), the rule-31 times, and the Lean-side
   import closure of the new module with its controls.
4. Appendix A on the landed tree: 52 modules, islands 2, the new module `uses= 1` (`GaussMarkov`)
   and `GaussMarkov` `usedBy= 2`; `DupCheck: 5 TWIN line(s), 0 SWAP line(s)` (if J3 lands before
   J2, rule 18: 51 modules and islands 3 at J3's landing, and J2's numbers become 52 and 2). The
   type dump against J1's evidence shows only additions, judged up to proof irrelevance (rule
   25): `GaussMarkov`'s records unchanged.

**Undo:** yes — `git revert` of the one commit (it removes the module and its import line).

---

## Close

1. **Refresh `HANDOFF.md`.**
   - §1: the snapshot from the six commands on a clean tree.
   - §3's "what next", re-ranked with this order's results. The list: Carmichael's theorem
     (Q3889376), first, now measured (this order's §0 row 16: the elementary shape — the Fibonacci
     cyclotomic numbers by Möbius product, the key lemma, the `3 · 2 ^ k` anomaly at `p = 2` (cells to
     `n = 150`), the Binet size bound (measured for `15 ≤ n ≤ 400`, to be proved in general) and
     the finite check `n ≤ 14`), proposed as order G-11's work
     once its Lean-side needs are measured; majorization (Mathlib's TODO), which no cycle has
     measured; Cochran's theorem (Q599876), the second half of the third item, over J3's module;
     max-flow min-cut and Menger (Q608294, Q928813); Mathlib's wanted list; and, not ranked, the
     two islands, the other pairs of §0 row 6, the `ExpChar` form, a `lucasV` analogue of the rank
     of apparition, and §0 row 9's weaker FWL hypothesis if the plan did not take it.
2. Close the `CLAIMS.md` row and set the `INDEX.md` row to "Close check pending" (§2's ruling);
   the addendum's commit closes it.
3. **The Close check.** Fresh subagents check every Done-means against
   `git diff <this order's first commit>^..master`, with a brief built by script that quotes rules
   16–34 verbatim (rules 24 and 26). Save their outputs first, hashed against the sha256 each
   returns (rules 17 and 33), then record the verdict, quoted and script-checked (rules 22 and 34),
   as an addendum to round 30. If it runs before step 2, say so (rule 18).
4. **Ask Dustin, in one line:** "Recommended: yes — push classical-lean master to DSMain, a
   fast-forward from 432aa26 to <new>." Push only on yes:
   `GIT_SSH_COMMAND='ssh -o BatchMode=yes -o ConnectTimeout=15' git -C ~/work/classical-lean push dsmain master`,
   fast-forward only, never `--force`. Then log the push in `push.log`. The next order records it in
   §6.
5. **The final chat report:** predicted beside actual, what landed with commit hashes, what stopped
   and why, what comes next, and:
   - the net change in theorem constants on the filtered list;
   - Appendix A's numbers before and after (islands, both new modules' uses, `TWIN` and `SWAP`
     lines, `pairs.py`'s first line);
   - this order's row for §0's order table, in the same columns, its wall clock from the filing
     commit (§0 row 15);
   - the count of refusals, as a `grep` of `evidence.log` (rule 30), and of void runs;
   - one line each on any decision made on Dustin's delegation, and on any overlap rule 18 recorded.

## Not in this order

- **G-4**: the number-theory track.
- **Publishing, listing in `docs/1000.yaml`, or offering anything to Mathlib**: Dustin's decisions.
  If J2 lands, the library proves Q1724049's statement; if J3 lands, Q1059151's. (W7) and (W6) are
  the kind of lemma Mathlib's `FieldTheory/Finite` would take; a Mathlib reviewer would ask for
  (W2) over `Nat.ModEq` as stated.
- **Retiring any module**: Dustin's decision. Two islands would remain, recorded, not bridged.
- **Carmichael's theorem** (§0 row 16, measured, ranked first at the Close), **majorization,
  Cochran, max-flow min-cut**: ranked at the Close.
- **The weaker FWL hypothesis** (§0 row 9): optional, the plan's choice.
- **The other pairs of §0 row 6**, `S3Quaternion ~ SU2SO3` among them: recorded, not bridged.
- **Any change to `tools/`** or to the banned-vocabulary list.
- **Anything in the lane on DSMain**, and the Claude Code configuration on helios.

---

## Appendix A — claude-ai's four evidence scripts

Write each into `~/work/_bump-evidence/g10/claude-ai/` byte for byte (the text between the fences,
ending with one newline), and check its sha256 before running it. All four are order G-9's
Appendix A, unchanged, their docstrings included (they still say "order G-7" and "order G-8": that
is their text).

```
a120cee455d000e78a7a60ad6cff1b93d9c1a6e15abaccf13e83a6dd95e8b3e0  DeclGraph.lean
9687c7ff6a81312c2aa9ccabbf380514ceffa479d63ade5afba2584f188c53e9  DupCheck.lean
f9aff2c78593cff456ab3e0970d3747cbaac32763aa53a03ed879c6395ec0404  islands.py
f734b8108ea1cf2c3e53c09877364891c24d71dcce74f3e3440ac4608222018a  pairs.py
```

Run, from `~/work/classical-lean`:

```
lake env lean ~/work/_bump-evidence/g10/claude-ai/DeclGraph.lean > ~/work/_bump-evidence/g10/claude-ai/declgraph.jsonl
python3 ~/work/_bump-evidence/g10/claude-ai/islands.py ~/work/_bump-evidence/g10/claude-ai/declgraph.jsonl
python3 ~/work/_bump-evidence/g10/claude-ai/pairs.py ~/work/_bump-evidence/g10/claude-ai/declgraph.jsonl
lake env lean ~/work/_bump-evidence/g10/claude-ai/DupCheck.lean
```

`DeclGraph.lean`:

```lean
import ClassicalLean
import ImportGraph.Lean.Environment

/-! Evidence script for order G-7 (claude-ai, 2026-09-24), outside the repository. Read-only.
One JSON line per `ClassicalLean` constant: its module, kind, whether private, the library
constants its type (`tyLib`) and value (`valLib`) name, and every constant its type names
(`tyAll`). Run: `lake env lean <this file> > declgraph.jsonl` from the repository root. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if n.hasMacroScopes then continue
    let u := privateToUserName n
    unless (`ClassicalLean).isPrefixOf u do continue
    let kind := match ci with
      | .thmInfo _ => "thm" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
      | .inductInfo _ => "induct" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
      | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot"
    let m := (env.getModuleFor? n).getD .anonymous
    let lib (a : Array Name) : Array Json :=
      (a.filter fun c => (`ClassicalLean).isPrefixOf (privateToUserName c)).map
        fun c => Json.str (privateToUserName c).toString
    let tyAll := ci.type.getUsedConstants
    let valAll : Array Name := match ci.value? (allowOpaque := true) with
      | some v => v.getUsedConstants | none => #[]
    let j := Json.mkObj [("raw", Json.str n.toString), ("user", Json.str u.toString),
      ("kind", Json.str kind), ("module", Json.str m.toString),
      ("private", Json.bool (isPrivateName n)),
      ("tyLib", Json.arr (lib tyAll)), ("valLib", Json.arr (lib valAll)),
      ("tyAll", Json.arr (tyAll.map fun c => Json.str c.toString))]
    IO.println j.compress
```

`DupCheck.lean`:

```lean
import ClassicalLean

/-! Evidence script for order G-7 (claude-ai, 2026-09-24), outside the repository. Read-only.
For every public `ClassicalLean` theorem, the theorems anywhere in the environment (Mathlib
included) whose type is the same `Expr` (`TWIN`), or the same with the two sides of a final `Eq`
or `Iff` swapped (`SWAP`). Run: `lake env lean <this file>` from the repository root. -/

open Lean Elab Command

partial def swapSides : Expr → Option Expr
  | .forallE n d b bi => (swapSides b).map fun b' => .forallE n d b' bi
  | e =>
    if e.isAppOfArity ``Eq 3 then
      some (mkApp3 e.appFn!.appFn!.appFn! e.appFn!.appFn!.appArg! e.appArg! e.appFn!.appArg!)
    else if e.isAppOfArity ``Iff 2 then
      some (mkApp2 e.appFn!.appFn! e.appArg! e.appFn!.appArg!)
    else none

run_cmd do
  let env ← getEnv
  let mut tbl : Std.HashMap UInt64 (Array Name) := {}
  for (n, ci) in env.constants.toList do
    if n.hasMacroScopes || n.isInternalDetail then continue
    unless ci matches .thmInfo _ do continue
    tbl := tbl.insert ci.type.hash ((tbl.getD ci.type.hash #[]).push n)
  let mut twins := 0
  let mut swaps := 0
  for (n, ci) in env.constants.toList do
    if n.hasMacroScopes || n.isInternalDetail || isPrivateName n then continue
    unless (`ClassicalLean).isPrefixOf n do continue
    unless ci matches .thmInfo _ do continue
    let same := (tbl.getD ci.type.hash #[]).filter fun m =>
      m != n && (env.find? m).any (·.type == ci.type)
    if !same.isEmpty then
      twins := twins + 1
      IO.println s!"TWIN {n} == {same}"
    if let some t' := swapSides ci.type then
      let sw := (tbl.getD t'.hash #[]).filter fun m => m != n && (env.find? m).any (·.type == t')
      if !sw.isEmpty then
        swaps := swaps + 1
        IO.println s!"SWAP {n} == symm {sw}"
  IO.println s!"DupCheck: {twins} TWIN line(s), {swaps} SWAP line(s)"
```

`islands.py`:

```python
"""Evidence script for order G-7 (claude-ai, 2026-09-24), outside the repository. Read-only.
Reads DeclGraph.lean's output and prints, per module, how many other modules use it and how many
it uses (a use: a constant of one module named in the type or value of a constant of another),
then the islands (used by none and using none). Usage: python3 islands.py declgraph.jsonl"""
import json, sys, collections
rows = [json.loads(l) for l in open(sys.argv[1])]
own = {r['user']: r['module'] for r in rows}
users, uses = collections.defaultdict(set), collections.defaultdict(set)
for r in rows:
    for c in set(r['tyLib']) | set(r['valLib']):
        m = own.get(c)
        if m and m != r['module']:
            users[m].add(r['module']); uses[r['module']].add(m)
mods = sorted(set(own.values()))
for m in mods:
    print(f"{m.removeprefix('ClassicalLean.'):46s} usedBy={len(users[m]):2d} uses={len(uses[m]):2d}")
isl = [m.removeprefix('ClassicalLean.') for m in mods if not users[m] and not uses[m]]
print(f"modules={len(mods)} constants={len(rows)} islands={len(isl)}: {', '.join(isl)}")
```

`pairs.py`:

```python
"""Evidence script for order G-8 (claude-ai, 2026-09-24), outside the repository. Read-only.
Reads DeclGraph.lean's output. For every pair of modules with no declaration-level use in either
direction, lists the rare non-library constants that the statements (types) of both modules name.
A constant is rare when the types of at most MAXDF modules name it. Usage:
python3 pairs.py declgraph.jsonl [MAXDF]"""
import json, sys, collections, itertools, math
rows = [json.loads(l) for l in open(sys.argv[1])]
MAXDF = int(sys.argv[2]) if len(sys.argv) > 2 else 3
own = {r['user']: r['module'] for r in rows}
edge = set()
for r in rows:
    for c in set(r['tyLib']) | set(r['valLib']):
        m = own.get(c)
        if m and m != r['module']:
            edge.add((r['module'], m))
conc = collections.defaultdict(set)
for r in rows:
    if r['private']:
        continue
    for c in r['tyAll']:
        if c.startswith('ClassicalLean') or c.startswith('_private'):
            continue
        conc[r['module']].add(c)
df = collections.Counter()
for m, cs in conc.items():
    for c in cs:
        df[c] += 1
mods = sorted(conc)
out = []
for a, b in itertools.combinations(mods, 2):
    if (a, b) in edge or (b, a) in edge:
        continue
    shared = sorted(c for c in conc[a] & conc[b] if df[c] <= MAXDF)
    if shared:
        score = sum(math.log(len(mods) / df[c]) for c in shared)
        out.append((score, a, b, shared))
out.sort(key=lambda t: -t[0])
print(f"modules={len(mods)} edges={len(edge)} rare_df<={MAXDF} pairs_without_edge_sharing_rare={len(out)}")
for score, a, b, shared in out[:40]:
    s = lambda m: m.removeprefix('ClassicalLean.')
    print(f"{score:6.2f} {s(a)} ~ {s(b)} :: {len(shared)} :: {', '.join(shared[:12])}")
```
