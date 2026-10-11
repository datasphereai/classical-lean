import ClassicalLean

/-!
# Tests for the vacuity gate

Small theorems that `tools/VacuityGate.lean` must judge correctly. This file is not part of the
library (no `lean_lib` builds it and nothing imports it); `tools/run_vacuity_tests.py` joins the
gate's test (`isVacuousType`) to these theorems and reports, for each one, whether the gate flags
it.

The first word of each name says what the gate must do:

* `vac_`: the statement proves nothing; the gate must **flag** it.
* `real_`: a real theorem; the gate must **pass** it.
* `lim_`: a known limit of the gate, stated rather than hidden. The statement is empty or close
  to it, but the gate **passes** it on purpose; the docstring says why.
* A `real_` test whose name is on `tools/vacuity_reviewed_tests.txt` must come out `LISTED`: the
  gate flags it (the old case 3, which ignores premises) and the entry lets it pass.

The two `real_..._old` theorems copy the statements of `Tremaux.anc_mem` and
`noGainCycle_of_short` as they were at `2489db4`, before order LEAN-25 reworded them to get past
the gate's case 3.
-/

namespace VacuityGateTests

open ClassicalLean.Combinatorics

variable {V : Type} {P Q R : V → Prop} {S T : Set V}

/-! ## Statements that prove nothing: the gate must flag them -/

/-- Case 1: the conclusion is `True`. -/
theorem vac_true : True := trivial

/-- Case 2: the conclusion is a hypothesis. -/
theorem vac_self (p : Prop) (h : p) : p := h

/-- Case 4: `∃ y, y = e`, true of every `e`. -/
theorem vac_exists_eq (f : ℕ → ℕ) (n : ℕ) : ∃ y, y = f n := ⟨_, rfl⟩

/-- The conclusion is an instance of a `∀` hypothesis. -/
theorem vac_forall (h : ∀ a, P a) (a : V) : P a := h a

/-- The shape the gate's docstring records from the retired corpus. -/
theorem vac_historical (f : ℕ → ℕ → ℕ → ℕ) (g : ℕ → ℕ → ℕ)
    (h : ∀ X S s, f X S s ≥ g S s) (X S s : ℕ) : f X S s ≥ g S s := h X S s

/-- A `∀` hypothesis with a premise, and the premise is another hypothesis. -/
theorem vac_forall_premise (h : ∀ a, Q a → P a) (a : V) (hq : Q a) : P a := h a hq

/-- Two premises; the first one tried for `?a ∈ S` (`hx`) is the wrong one, so the gate must
back up and try `ha`. -/
theorem vac_forall_premise_backtrack {par : V → Option V}
    (hS : ∀ a p, a ∈ S → par a = some p → p ∈ S) {x a b : V} (hx : x ∈ S) (ha : a ∈ S)
    (hp : par a = some b) : b ∈ S := hS a b ha hp

/-- The premise is a conjunction of two hypotheses. -/
theorem vac_and_premise (h : ∀ a, Q a ∧ R a → P a) (a : V) (hq : Q a) (hr : R a) : P a :=
  h a ⟨hq, hr⟩

/-- The premise is a disjunction, one side a hypothesis (review r1, finding 1). -/
theorem vac_or_premise (h : ∀ a, Q a ∨ R a → P a) (a : V) (hr : R a) : P a := h a (Or.inr hr)

/-- Five levels, each behind its own named definition (review r1, finding 3): the unfold count
starts again after each binder. -/
def W5 (P : V → Prop) : Prop := ∀ a, P a
def W4 (P : V → Prop) : Prop := ∀ _ : ℕ, W5 P
def W3 (P : V → Prop) : Prop := ∀ _ : ℕ, W4 P
def W2 (P : V → Prop) : Prop := ∀ _ : ℕ, W3 P
def W1 (P : V → Prop) : Prop := ∀ _ : ℕ, W2 P

theorem vac_nested_named (h : W1 P) (a : V) : P a := h 0 0 0 0 a

/-- The premise is an equation that holds by `rfl`. -/
theorem vac_eq_premise (F : ℕ → ℕ → Prop) (h : ∀ x y, x = y → F x y) (a : ℕ) : F a a :=
  h a a rfl

/-- The premise is a closed fact that `decide` proves. -/
theorem vac_decide_premise (F : ℕ → Prop) (h : ∀ n, 0 < n → F n) : F 1 := h 1 Nat.one_pos

/-- A variable of the hypothesis that the conclusion does not fix; any `ℕ` will do. -/
theorem vac_unused_variable (p : Prop) (h : ∀ _ : ℕ, p) : p := h 0

/-- The conclusion is a subset statement; unfolded, it is the hypothesis. -/
theorem vac_concl_subset (h : ∀ x, x ∈ S → x ∈ T) : S ⊆ T := h

/-- The hypothesis wrapped in `⊆`. The gate before VACUITY-1 cannot see inside it. -/
theorem vac_subset (h : S ⊆ T) (x : V) (hx : x ∈ S) : x ∈ T := h hx

/-- A named wrapper around a `∀` statement, used only by the tests below. -/
def Wrap (P : V → Prop) : Prop := ∀ a, P a

/-- A named wrapper around a `∀` statement with a premise. -/
def WrapImp (Q P : V → Prop) : Prop := ∀ a, Q a → P a

/-- The hypothesis wrapped in a named definition. -/
theorem vac_named (h : Wrap P) (a : V) : P a := h a

/-- The hypothesis wrapped in a named definition, and its premise is another hypothesis. -/
theorem vac_named_premise (h : WrapImp Q P) (a : V) (hq : Q a) : P a := h a hq

/-- `anc_mem`'s new hypothesis (the `⊆` form), with the conclusion one step from `a`: the premise
`b ∈ {p | ∃ a ∈ S, par a = some p}` is built from two hypotheses. -/
theorem vac_parent_subset {par : V → Option V}
    (hS : {p | ∃ a ∈ S, par a = some p} ⊆ S) {a b : V} (ha : a ∈ S) (hp : par a = some b) :
    b ∈ S := hS ⟨a, ha, hp⟩

/-- `NoShortGainCycle` (a named definition), applied to a cycle that is short enough. -/
theorem vac_short_gain {ι : Type} (r : ι → ι → ℝ) (n : ℕ) (h : NoShortGainCycle r n)
    (c : List ι) (hc : c ≠ []) (hl : c.length ≤ n) : cycleProd r c ≤ 1 := h c hc hl

/-- A Mathlib predicate (`Monotone`), applied. -/
theorem vac_monotone (f : ℕ → ℕ) (hf : Monotone f) (a b : ℕ) (hab : a ≤ b) : f a ≤ f b :=
  hf hab

/-! ## Real theorems: the gate must pass them -/

/-- `Tremaux.anc_mem` as stated at `2489db4`. The premise `par ?a = some b` cannot be met by any
hypothesis: it needs an induction along the ancestors. The fixed test passes it; the old case 3
flags it, so it is on the test list. -/
theorem real_anc_mem_old {par : V → Option V} {S : Set V}
    (hS : ∀ a p, par a = some p → a ∈ S → p ∈ S)
    {a b : V} (h : Tremaux.Anc par a b) (ha : a ∈ S) : b ∈ S :=
  Tremaux.anc_mem (fun p ⟨a, ha, hap⟩ ↦ hS a p hap ha) h ha

/-- `Tremaux.anc_mem` as stated now (after `a1a3a67`). -/
theorem real_anc_mem_new {par : V → Option V} {S : Set V}
    (hS : {p | ∃ a ∈ S, par a = some p} ⊆ S) {a b : V} (h : Tremaux.Anc par a b)
    (ha : a ∈ S) : b ∈ S :=
  Tremaux.anc_mem hS h ha

/-- `noGainCycle_of_short` as stated at `2489db4`. The premise `c.length ≤ Fintype.card ι`
cannot be met: going from short cycles to all cycles is the whole of Bellman–Ford. On the test
list, like `real_anc_mem_old`. -/
theorem real_noGainCycle_of_short_old {ι : Type} [Fintype ι] {r : ι → ι → ℝ}
    (hr : ∀ i j, 0 < r i j)
    (h : ∀ c : List ι, c ≠ [] → c.length ≤ Fintype.card ι → cycleProd r c ≤ 1) :
    NoGainCycle r :=
  noGainCycle_of_short hr h

/-- `noGainCycle_of_short` as stated now (after `a1a3a67`). -/
theorem real_noGainCycle_of_short_new {ι : Type} [Fintype ι] {r : ι → ι → ℝ}
    (hr : ∀ i j, 0 < r i j) (h : NoShortGainCycle r (Fintype.card ι)) : NoGainCycle r :=
  noGainCycle_of_short hr h

/-- The premise `0 < n` is not a hypothesis; the case `n = 0` needs `h0`. On the test list, like
`real_anc_mem_old`. -/
theorem real_premise_missing (F : ℕ → Prop) (h : ∀ n, 0 < n → F n) (h0 : F 0) (n : ℕ) : F n := by
  cases n with
  | zero => exact h0
  | succ k => exact h _ k.succ_pos

/-- The same, with the hypothesis in a named definition. -/
def WrapPos (F : ℕ → Prop) : Prop := ∀ n, 0 < n → F n

theorem real_named_premise_missing (F : ℕ → Prop) (h : WrapPos F) (h0 : F 0) (n : ℕ) : F n := by
  cases n with
  | zero => exact h0
  | succ k => exact h _ k.succ_pos

/-- The same, with the hypothesis in `⊆`: `{n | 0 < n} ⊆ {n | F n}`. -/
theorem real_subset_premise_missing (F : ℕ → Prop) (h : {n | 0 < n} ⊆ {n | F n}) (h0 : F 0)
    (n : ℕ) : F n := by
  cases n with
  | zero => exact h0
  | succ k => exact h k.succ_pos

/-- Induction: the step's conclusion `F (n + 1)` does not match `F n`. -/
theorem real_induction (F : ℕ → Prop) (h0 : F 0) (h : ∀ n, F n → F (n + 1)) (n : ℕ) : F n := by
  induction n with
  | zero => exact h0
  | succ k ih => exact h k ih

/-- A strict inequality does not give `≤` by applying it: `f a < f b` is not `f a ≤ f b`, and
`a ≤ b` may be `a = b`. -/
theorem real_strictMono_monotone (f : ℕ → ℕ) (hf : StrictMono f) : Monotone f :=
  hf.monotone

/-- A real chain: a composition of increasing maps is increasing. The fixed test passes it (the
premise `g a ≤ g b` needs `hg` applied to `hab`, a chain); the old case 3 flags it (the
conclusion of `hf` matches). It passes only through its entry on the test list. -/
theorem real_comp_increasing (f g : ℕ → ℕ) (hf : ∀ a b, a ≤ b → f a ≤ f b)
    (hg : ∀ a b, a ≤ b → g a ≤ g b) : ∀ a b, a ≤ b → f (g a) ≤ f (g b) :=
  fun a b hab ↦ hf _ _ (hg a b hab)

/-! ## Known limits: the gate passes these on purpose -/

/-- Two hypotheses chained: `h` needs `Q a`, which only `hq` applied to `hr` gives. The fixed test
meets a premise with one hypothesis, not a chain, so it passes this; the old case 3 (premises
ignored) flags it. Was `lim_chain` before the ruling that keeps the old case 3. -/
theorem vac_chain (h : ∀ a, Q a → P a) (hq : ∀ a, R a → Q a) (a : V) (hr : R a) : P a :=
  h a (hq a hr)

/-- `0 + n = n` holds for every `n` but not by `rfl` (addition recurses on the right), so the
fixed test does not meet the premise; the old case 3 (premises ignored) flags it. Was
`lim_semantic` before the ruling that keeps the old case 3. -/
theorem vac_semantic (F : ℕ → Prop) (h : ∀ n, 0 + n = n → F n) (n : ℕ) : F n :=
  h n (Nat.zero_add n)

/-- A projection of a conjunction is not an application of the hypothesis (review r1, finding 4). -/
theorem lim_and_hyp (h : ∀ a, P a ∧ Q a) (a : V) : P a := (h a).1

/-- A private test theorem is tested too (review r1, finding 8). -/
private theorem vac_private (h : ∀ a, P a) (a : V) : P a := h a

/-- A contradictory hypothesis proves anything. The gate does not look for contradictions. -/
theorem lim_false (p : Prop) (h : False) : p := h.elim

/-! ## Tactic helpers: skipped, unless written by hand -/

/-- A hand-written theorem whose name looks like a tactic helper. It has a source position, so
the gate tests it, and flags it. -/
theorem vac_named_like_helper._proof_1 (p : Prop) (h : p) : p := h

/-- A real theorem whose proof uses `omega` inside a term, which leaves `_proof_` helpers with no
source position; the gate skips those (`SKIP`) and passes the theorem. -/
theorem real_omega_user (n : ℕ) (h : 2 ≤ n) : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩

/-! ## The reviewed list (`tools/vacuity_reviewed_tests.txt` stands in for
`tools/vacuity_reviewed.txt` here) -/

/-- On the test list as a `HELPER`, under the hash of this statement: `LISTED`. -/
theorem listed_helper (f : ℕ → ℕ) (hf : Monotone f) (a b : ℕ) (hab : a ≤ b) : f a ≤ f b :=
  hf hab

/-- On the test list as `VACUOUS-PENDING`: passes, and printed. -/
theorem pending_vacuous (h : ∀ a, P a) (a : V) : P a := h a

/-- A listed statement that was changed afterwards. Its entry carries the hash of the statement
before the change (the same as `listed_helper`'s, the hash covering the statement only); the
change added the hypothesis `c`. It is flagged again. -/
theorem vac_listed_changed (f : ℕ → ℕ) (hf : Monotone f) (a b : ℕ) (hab : a ≤ b) (_c : ℕ) :
    f a ≤ f b :=
  hf hab

-- The test list also has an entry for `VacuityGateTests.stale_removed`, a theorem that does not
-- exist (renamed or deleted): the runner reports it as `STALE`, and the gate fails on such an
-- entry.

end VacuityGateTests
