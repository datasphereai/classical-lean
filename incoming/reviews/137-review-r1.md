# Review of ClassicalLean/Probability/PolyaUrn.lean (item 137)

Reviewer: fresh cold reviewer, read-only. Brief sha256 79b4a2f8…fbf4a checked. Draft `incoming/d137-r2-s1.lean` sha256 3d4a4712…b0a6 matches `incoming/README.md:16`. Scratch work is in /tmp/claude-0/-home-user-classical-lean/19408406-f39d-5a72-8f6f-124d894b525a/scratchpad/review/cold-reviewer-137/.

I ran Lean on two scratch files, one at a time, from the repository root with the brief's flags:
- **Run 1, `Check137.lean`:** a verbatim copy of the whole module, all three witnesses included, with reviewer checks R1 to R3 added after it. Result: rc 0 in 11 s. There were no errors or warnings. The only output was the axiom lists: all three main theorems use only `[propext, Classical.choice, Quot.sound]`.
- **Run 2, `NoTraj137.lean`:** lines 1–225 of the module with the `IonescuTulcea.Traj` import removed. Result: rc 0 in 7 s, no output.

## A. Statements against the plan row and the draft
- **Plan row** (order table, `records/orders/20261015T023648Z__…polya-reflection.md:14`): "Pólya's urn: the share of red balls is a martingale and converges almost surely."
- **`martingale_urnShare`** (lines 128–133): FAITHFUL.
  - The model is the standard one. `urnRed r X n = r + Σ_{j<n} X j`, and the share is out of `r + b + n` balls.
  - Each draw `X n ∈ {0,1}` is `ℱ (n+1)`-measurable, and `μ[X n | ℱ n] = urnShare r b X n` almost everywhere. For a 0/1 variable, that conditional mean fixes the conditional law: Bernoulli(current share).
  - The conclusion is Mathlib's `Martingale`, which includes adaptedness and integrability.
- **`ae_tendsto_urnShare`** (lines 182–187): FAITHFUL. It says `∃ L, ∀ᵐ ω, Tendsto (share · ω) atTop (𝓝 (L ω))`, which is almost-sure convergence.
- **`ae_mem_Icc_of_tendsto_urnShare`** (lines 217–220), checked against the order's words "a new theorem that the limit lies in [0, 1] almost surely": GENERALIZED.
  - It says: for any `μ`, `r`, `b`, any 0/1-valued `X` and any `L` with the share tending to `L` almost surely, `L ∈ [0,1]` almost surely.
  - Combined with `ae_tendsto_urnShare`, this is exactly the requested statement for the urn. It also holds without the urn's dynamics.
  - **Its hypotheses are the right ones.**
    - None is unused: `hX01` and `hL` are both used.
    - None is missing: it compiles.
    - None is stronger than needed. It does not carry `hrb`, `IsProbabilityMeasure`, `hX_meas` or `hX_cond`, none of which the claim needs.
    - Observation, not a finding: the proof uses `hX01` only through "every share lies in [0,1]" at almost every ω. So a.e.-0/1 draws, or draws in [0,1], would also do. The pointwise 0/1 form is the module's standing model of a draw and is exactly what `ae_tendsto_urnShare` already requires, so in context it is not stronger than needed.
- **Unchanged from the draft.** `diff` of draft lines 3–160 against module lines 34–197 shows only:
  - `namespace ClassicalLean.Probability.PolyaUrn` added;
  - `show` changed to `change` at module lines 109 and 141;
  - the two docstrings expanded;
  - the dead `first | … | …` alternative removed at line 195.
  
  The signatures of `urnRed`, `urnShare`, `martingale_urnShare` and `ae_tendsto_urnShare` are character-identical to the draft's, so no statement changed in meaning.

## B. Every hypothesis used
- **`martingale_urnShare`:**
  - `hrb`: used in `urnShare_norm_le` (line 153) and in `hN` (lines 168–169, for `share_key`).
  - `hX01`: used in `hRint`, `hXint` and `hSint`.
  - `hX_meas`: used in `hRmeas`, `hXint` and `hSmeas`.
  - `hX_cond`: used at line 172.
  - `IsProbabilityMeasure`: used by `integrable_const`.
- **`ae_tendsto_urnShare`:** all four hypotheses go into `martingale_urnShare` (line 188). `hrb` and `hX01` are used again at line 194.
- **`ae_mem_Icc_of_tendsto_urnShare`:** `hL` is used at line 221 and `hX01` at line 223.
- **Observation, not a finding.** `hrb` is used but is not mathematically needed. Check R3 in run 1 proves `martingale_urnShare_noHrb`: the same statement without `hrb`, by the same proof.
  - In that proof the bound comes from `urnShare_mem_Icc`.
  - The case `r + b + n = 0` forces `r = n = 0`, so the red count is 0 and `0/0 = 0` makes the identity trivial.
  - With `r = b = 0` the hypotheses force `X = 0` almost everywhere, the empty urn.
  
  Rule 1 keeps the draft's statement, and an urn with balls is the plan's premise, so this is not a finding.

## C. Witnesses (rule 4 and HANDOFF §4)
**Form: all three witnesses comply.**
- Each is an `example := ClassicalLean.Probability.PolyaUrn.<name> …` that applies the theorem itself (lines 238, 315, 386).
- Every chosen argument is given by name: `μ`, `ℱ`, `r`, `b`, `X`, and `L` in the third. Only proofs are positional.
- Each has one `open MeasureTheory ProbabilityTheory Finset ClassicalLean.Probability.PolyaUrn in` line of its own.
- Each docstring starts "The hypotheses of `<name>` hold together: …".
- Forbidden words: `grep -nE "sorry|admit|native_decide|implemented_by|axiom|set_option"` on the file finds nothing (rc 1).
- There are no helper declarations. Local `have`s and the module's own private lemmas `urnShare_mem_Icc` and `urnRed_stronglyMeasurable` are used inline.
- Every main theorem has a hypothesis, and all three are witnessed.

**Not degenerate: each hypothesis in turn (witnesses 1 and 2 are identical apart from the theorem name).**
- **`μ`:**
  - `μ` is `Kernel.traj κ 0 (fun _ ↦ false)` on `ℕ → Bool`, a genuine Ionescu-Tulcea path measure.
  - `κ n z = ofReal s • dirac true + ofReal (1 − s) • dirac false`, where `s` is the share computed from coordinates `1..n` of `z`. So `κ n` depends on the history.
  - R1 (run 1): the red chance at step 1 is `2/3` after a red draw and `1/3` after a blue one.
  - R2 (run 1): for every `n` and `ω`, `1/(n+2) ≤ s ≤ (n+1)/(n+2)`. So `s` lies strictly inside (0,1), and neither `ofReal` truncates.
- **`r = b = 1`, `hrb : 0 < 2`:** not at a boundary.
- **`hX01`:** `X j ω = if ω (j+1) then 1 else 0` is a real 0/1 observation of the path coordinate it is about. It is not identically 0, nor 0 past some point.
- **`hX_meas`:** `ℱ = Filtration.piLE`, the natural filtration of the path. This is not a trivial σ-algebra.
- **`hX_cond`:** proved through `Kernel.condExp_traj` and `Kernel.map_traj_succ_self`, with no junk value. The share's denominator is `n + 2 > 0`.
  - The draws are genuinely random. If some `X n` were almost surely a constant `c ∈ {0,1}`, then `hX_cond`, which Lean checked, would give share = `c` almost surely. That contradicts R2, since `μ` is a probability measure.
- **Third witness: `L := Classical.choose (ae_tendsto_urnShare …)`, acceptable.**
  - `L` is the actual almost-sure limit of the same nondegenerate urn, with the same `μ` and `X`.
  - `hL` is its `choose_spec`, a real convergence fact rather than a junk value. The limit of this urn is in fact Uniform(0,1), so it is not a constant.
  - `hX01` holds as above.
- **The witness docstrings are true:**
  - "coordinate 0 plays no part" is true, since `X j` reads `ω (j+1)`;
  - the bounds `1/(n+2)` to `(n+1)/(n+2)` are verified by R2;
  - "draw n is known at time n+1" is true;
  - the Mathlib lemmas named are the ones used;
  - the third docstring describes its `L` correctly.

## D. Namespace
`namespace ClassicalLean.Probability.PolyaUrn` (line 37) to `end` (line 225) holds all 13 declarations (lines 41–223):
- `urnRed` and `urnShare`;
- the private lemmas `urnRed_zero`, `urnRed_succ`, `urnRed_bounds`, `urnShare_norm_le`, `urnRed_stronglyMeasurable`, `urnRed_integrable`, `share_key` and `urnShare_mem_Icc`;
- the three main theorems.

After line 225 there are only the three `example`s. The namespace matches the path.

## E. Imports
Line 7 imports `Mathlib.Probability.Kernel.IonescuTulcea.Traj` and line 8 imports `Mathlib.Probability.Martingale.Convergence`. Both are specific files, with no `import Mathlib`. Run 2 confirms the docstring's claim (lines 30–31) that the `Traj` import serves only the witnesses: the body compiles without it. There is precedent for an import added for the library's needs (GamblersRuin and HasLawExists, HANDOFF round 57). The module is registered at `ClassicalLean.lean:133`.

## F. No recursive-`True` conclusions
The conclusions are `Martingale …`, `∃ L, ∀ᵐ …, Tendsto …` and `∀ᵐ ω, L ω ∈ Set.Icc 0 1`. `urnRed` is recursive, but it is a real-valued function, not a predicate.

## G. Docstrings
- Each main theorem's docstring names "item 137 of MATH-PLAN-library-2" (lines 123, 179–180, 213–214).
- The module docstring names the order and the item, and lists all three results (lines 18–25).
- Every mathematical claim checked is true:
  - `(R + R/N)/(N+1) = R/N` (line 28);
  - "bounded in L¹, the martingale convergence theorem applies";
  - "Only the draws being 0 or 1 is needed" for `ae_mem_Icc_of_tendsto_urnShare` (it has no other hypothesis);
  - `urnShare_mem_Icc` "whatever r and b … Lean's 0/0 = 0";
  - the `urnRed` docstring "(i+1)-st draw", which is consistent with "draw n counting from 0";
  - the `Traj` import claim (run 2).

## H. Other
- Observation, not a finding: `urnShare_norm_le` (lines 69–82, carries `hrb`) is now subsumed by `urnShare_mem_Icc` (lines 202–211, no `hrb`). This is harmless duplication kept from the draft.
- Nothing false, misleading or mis-named found.

## Findings
None.

Observations, needing no action:
1. `hrb` is mathematically removable from `martingale_urnShare` and `ae_tendsto_urnShare` (R3). It is kept under rule 1.
2. `ae_mem_Icc_of_tendsto_urnShare` could take a.e.-0/1 draws instead of pointwise ones. The pointwise form matches the module's model.
3. `urnShare_norm_le` duplicates `urnShare_mem_Icc`.

## Verdict
VERDICT: PASS
martingale_urnShare: FAITHFUL
ae_tendsto_urnShare: FAITHFUL
ae_mem_Icc_of_tendsto_urnShare: GENERALIZED
