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
  to it, but the gate **passes** it on purpose; the docstring says why. (None is left at
  VACUITY-2: `lim_and_hyp` and `lim_false` became `vac_and_hyp_left` and `vac_false_elim`.)
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

/-- Five levels, each behind its own named definition (review r1, finding 3). The unfold count
this tested was removed in order VACUITY-2 (one `whnf` opens every nested definition). -/
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

/-- A projection of a conjunction (review r1, finding 4). Was `lim_and_hyp` until order
VACUITY-2 (item 72), which opens `∧` hypotheses into their two halves. -/
theorem vac_and_hyp_left (h : ∀ a, P a ∧ Q a) (a : V) : P a := (h a).1

/-- A private test theorem is tested too (review r1, finding 8). -/
private theorem vac_private (h : ∀ a, P a) (a : V) : P a := h a

/-- A contradictory hypothesis proves anything. Was `lim_false` until order VACUITY-2 (item 77),
whose rule 5 looks for a proof of `False` from the hypotheses. -/
theorem vac_false_elim (p : Prop) (h : False) : p := h.elim

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

/-! ## Order VACUITY-2 (items 72 to 77) -/

/-- A conjunction hypothesis, review r1's probe, copied: the left half. The same statement as
`vac_and_hyp_left`, kept under the probe's name. -/
theorem vac_and_hyp (h : ∀ a, P a ∧ Q a) (a : V) : P a := (h a).1

/-- A conjunction hypothesis: the right half, with a premise met by another hypothesis. -/
theorem vac_and_hyp_right (h : ∀ a, Q a → P a ∧ R a) (a : V) (hq : Q a) : R a := (h a hq).2

/-- An `↔` hypothesis used forward, review r1's probe, copied. -/
theorem vac_iff_hyp (h : ∀ a, Q a ↔ P a) (a : V) (hq : Q a) : P a := (h a).mp hq

/-- An `↔` hypothesis used backward. -/
theorem vac_iff_hyp_mpr (h : ∀ a, Q a ↔ P a) (a : V) (hp : P a) : Q a := (h a).mpr hp

/-- Hypothesis in an irreducible named definition, review r1's probe, copied (item 73). -/
@[irreducible] def IWrap (P : V → Prop) : Prop := ∀ a, P a

theorem vac_irreducible (h : IWrap P) (a : V) : P a := by
  unfold IWrap at h; exact h a

/-- Six nested definitions before one binder: one `whnf` call opens them all, so the
"more than 4 unfoldings" limit never fires (item 74). Kept as a guard. -/
def E1 (P : V → Prop) : Prop := ∀ a, P a
def E2 (P : V → Prop) : Prop := E1 P
def E3 (P : V → Prop) : Prop := E2 P
def E4 (P : V → Prop) : Prop := E3 P
def E5 (P : V → Prop) : Prop := E4 P
def E6 (P : V → Prop) : Prop := E5 P

theorem vac_deep_unfold (h : E6 P) (a : V) : P a := h a

/-- Contradictory hypotheses: no natural number is below `0` (rule 5, item 77; `omega`). -/
theorem vac_false_hyp (F : ℕ → Prop) (n : ℕ) (h : n < 0) : F n := absurd h (Nat.not_lt_zero n)

/-- A deliberate "from a contradiction, anything" helper (rule 5 finds it). It is on the test list
as a `HELPER`, so it must come out `LISTED` once rule 5 exists. -/
theorem real_exfalso_helper {p : Prop} (n : ℕ) (h : n + 1 ≤ 0) : p :=
  absurd h (Nat.not_succ_le_zero n)

/-- A conclusion `≠`: unfolded, it reads `n + 1 = 0 → False`, but `n + 1 = 0` is part of the
claim, not a hypothesis; rule 5 must not refute it (the first library run of rule 5 flagged
`Simplex.single_one_ne_zero` and three more of this shape). -/
theorem real_ne_zero_concl (n : ℕ) : n + 1 ≠ 0 := Nat.succ_ne_zero n

/-- A conclusion that unfolds to a `∀` with an impossible premise (`x ∈ []`), like
`PredicateStack.admits_nil`. -/
theorem real_not_mem_nil (x : ℕ) : x ∉ ([] : List ℕ) := List.not_mem_nil

/-- A theorem whose conclusion is `False` states that its hypotheses contradict: an
impossibility result, not a vacuous one. Rule 5 does not run on it. -/
theorem real_false_concl (n : ℕ) (h : n + 1 ≤ 0) : False := Nat.not_succ_le_zero n h

/-- A conclusion written as `∀ x ∈ [], F x`: true because its premise is impossible. Rule 5
reads the binder `x ∈ []` as a hypothesis and flags it, by design: it is an empty-premise helper,
like `real_exfalso_helper`, and is on the test list (cold review r2, finding 1). -/
theorem real_forall_mem_nil (F : ℕ → Prop) : ∀ x ∈ ([] : List ℕ), F x :=
  fun _ h => absurd h List.not_mem_nil

/-- `True` behind a named definition (cold review r2, finding 4). -/
def Triv : Prop := True

theorem vac_true_named : Triv := trivial

/-- `∃ y, y = e` behind a named definition (cold review r2, finding 4). -/
def Witness (e : ℕ) : Prop := ∃ y, y = e

theorem vac_exists_named (n : ℕ) : Witness n := show ∃ y, y = n from ⟨n, rfl⟩

/-! ## Glued conclusions (Dustin's ruling of 2026-10-11, cold review r2 finding 3) -/

/-- The reviewer's example: the conclusion is the two hypotheses glued with `∧`. -/
theorem vac_glued_and (a : V) (h1 : P a) (h2 : Q a) : P a ∧ Q a := ⟨h1, h2⟩

/-- An `↔` glued from two implications that are hypotheses. -/
theorem vac_glued_iff (a : V) (h1 : P a → Q a) (h2 : Q a → P a) : P a ↔ Q a := ⟨h1, h2⟩

/-- Membership in an intersection is an `∧` once unfolded (the reviewer's `vac_mem_inter_concl`). -/
theorem vac_glued_inter (x : V) (hs : x ∈ S) (ht : x ∈ T) : x ∈ S ∩ T := ⟨hs, ht⟩

/-- Nested, and one part closed by applying a hypothesis (the fixed test) with its premise met. -/
theorem vac_glued_nested (a : V) (h1 : P a) (h2 : ∀ b, P b → Q b) (h3 : R a) :
    P a ∧ (Q a ∧ R a) := ⟨h1, h2 a h1, h3⟩

/-- One part is `True`. -/
theorem vac_glued_true (a : V) (h : P a) : P a ∧ True := ⟨h, trivial⟩

/-- A structure whose type is a proposition, other than `∧` and `↔`. -/
structure Both (p q : Prop) : Prop where
  left : p
  right : q

theorem vac_glued_struct (a : V) (h1 : P a) (h2 : Q a) : Both (P a) (Q a) := ⟨h1, h2⟩

/-- An `∧` conclusion that needs real work: neither part is a hypothesis. -/
theorem real_and_work (n : ℕ) (h : 2 ≤ n) : 1 ≤ n ∧ n ≠ 0 := ⟨by omega, by omega⟩

/-- A computed fact, closed by `decide`: never flagged. -/
theorem real_decide_fact : (3 : ℕ) < 5 ∧ 2 + 2 = 4 := by decide

/-- A hypothesis glued to a computed fact: the second part needs `rfl`/`decide`, not a
hypothesis, so the theorem passes (a stated limit of the glued rule). -/
theorem real_hyp_and_computed (a : V) (h : P a) : P a ∧ 2 + 2 = 4 := ⟨h, rfl⟩

/-- A structure whose type is a proposition and that contains itself (cold review r3, finding 1):
case 5 must end, not recurse until Lean aborts. -/
structure Loop (p : Prop) : Prop where
  rest : Loop p

structure LoopWrap (q : Prop) : Prop where
  w : q

theorem real_loop_wrap (p : Prop) (h : LoopWrap (Loop p)) : Loop p := h.w

/-- A computed fact behind a definition (cold review r3, finding 2): `Small 3` evaluates to
`True`, but only by computing, so it is not read as `True`, alone or as a part. -/
def Small (n : ℕ) : Prop := if n < 10 then True else False

theorem real_small_alone : Small 3 := by simp [Small]

theorem real_hyp_and_small (a : V) (h : P a) : P a ∧ Small 3 := ⟨h, by simp [Small]⟩

/-- `True` behind set membership, reached by unfolding instances and definitions only: flagged
(claude-ai's review of `d2503ba`, order LEAN-27, job 0). -/
theorem vac_univ_mem : (5 : ℕ) ∈ (Set.univ : Set ℕ) := trivial

/-- A computed fact behind a definition by pattern matching (order LEAN-27, job 0): `Small2 0` is
`True` only by reducing the `match`, which is computing, so it is not read as `True`. -/
def Small2 : ℕ → Prop
  | 0 => True
  | _ + 1 => False

theorem real_hyp_and_small2 (a : V) (h : P a) : P a ∧ Small2 0 := ⟨h, trivial⟩

/-- The same computed fact alone, through case 1 (job 0's review, finding 4). -/
theorem real_small2_alone : Small2 0 := trivial

/-- A computed fact behind a definition by structural recursion: a stated limit on the strict
side. Only `unfoldNamed`'s `whnfCore` runs with `iota := false`; its `unfoldDefinition?` runs
with `iota` on, and on a structural recursion its smart-unfolding path reduces the `match`, so
`Small3 0` is read as `True` and this theorem is flagged; listed in
`tools/vacuity_reviewed_tests.txt` (order LEAN-27, job 0's review, findings 1 and 4). -/
def Small3 : ℕ → Prop
  | 0 => True
  | n + 1 => Small3 n

theorem real_hyp_and_small3 (a : V) (h : P a) : P a ∧ Small3 0 := ⟨h, trivial⟩

/-- `True` behind a `match` on a pair whose one branch is `True`: nothing is computed, so it must
be flagged (Dustin's ruling of 2026-10-12 on job 0's review, finding 2). The gate at `c1b22b8`
passes it, since `whnfCore` with `iota := false` stops at the `match`. -/
def PairT : ℕ × ℕ → Prop
  | (_, _) => True

theorem vac_pair_true : ∀ x, PairT x := fun _ ↦ trivial

/-- Every branch `True`, on `ℕ`, which has no eta: the kernel cannot see `NatT n` as `True` for a
variable `n`, so no `True.intro` proof of it exists for the gate to send. A stated limit: it
passes (job 0's review of `f70aa50`, finding 2, option (c); Dustin's answer pending). -/
def NatT : ℕ → Prop
  | 0 => True
  | _ + 1 => True

theorem lim_nat_true : ∀ n, NatT n := fun n ↦ by cases n <;> trivial

/-- The same match as a glued part next to a hypothesis that closes it: flagged through that
hypothesis, as before LEAN-27 (job 0's review of `f70aa50`, finding 1). -/
theorem vac_hyp_and_nat_true (a : V) (n : ℕ) (h : P a) (hn : NatT n) : P a ∧ NatT n := ⟨h, hn⟩

-- A theorem added by meta code (`addDecl`) under a `_proof_` name, with no source position and
-- used by nothing (item 75): the statement is `p → p`.
open Lean in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ty := mkForall `p .default (mkSort 0) (mkForall `h .default (.bvar 0) (.bvar 1))
  let pf := mkLambda `p .default (mkSort 0) (mkLambda `h .default (.bvar 0) (.bvar 0))
  addDecl (.thmDecl { name := (`VacuityGateTests.vac_meta_helper).str "_proof_1",
                      levelParams := [], type := ty, value := pf })

/-- A theorem written by a local hygienic macro, so its name carries macro scopes (item 75). -/
local macro "mk_scoped_vac" : command => `(theorem vac_macro_scoped (p : Prop) (h : p) : p := h)
mk_scoped_vac

-- The test list also has an entry for `VacuityGateTests.stale_removed`, a theorem that does not
-- exist (renamed or deleted): the runner reports it as `STALE`, and the gate fails on such an
-- entry.

end VacuityGateTests
