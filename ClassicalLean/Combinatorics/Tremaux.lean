/-
Copyright (c) 2026 Dustin Watkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Watkins, Claude (Anthropic)
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-!
# Trémaux's rule for exploring a maze

A finite connected graph is a maze: vertices are crossroads, edges are paths. An explorer who
sees only the crossroads it stands at, and the marks left there, can still walk every path and
come back, by Trémaux's rule (item 64).

## The rule, as pinned from the source

Édouard Lucas, *Récréations mathématiques*, tome I, second edition, Gauthier-Villars et fils,
Paris, 1891 (title page; read in the Internet Archive scan `p1rcrationsm00lucauoft`, whose
catalogue entry says 1883), Troisième
récréation, "Le jeu des labyrinthes", pages 47 to 51, "Solution de M. Trémaux". On every crossing
of a path the explorer draws a stroke at each end, where it leaves and where it arrives (p. 47).
Then (pp. 47–49):

1. At a new crossroads, take any path ("une voie quelconque", p. 48), meaning any other than
   the one just arrived by: in Lean, one with no stroke (at a dead end, come back). Read
   literally, the arrival path would be allowed too, and on the path `0 – 1 – 2` from `0` the
   explorer could go `0 → 1 → 0` and stop, never reaching `2`.
2. Arriving at a crossroads already explored by a path never followed before, go back the
   same way.
3. Arriving at a crossroads already explored by a path already followed, take a path never
   followed if there is one, else a path followed only once.

The explorer stops when no path is allowed; Lucas shows this happens only at the start and that
then every path has been followed twice (pp. 49–50). Removing the paths where rule 2 sent the
explorer back leaves a tree (p. 51).

## The rule in Lean

`marks W u x` is the number of strokes at `u`'s end of the path `ux` after the route `W`: one
per crossing of `ux`, either way, which is what Lucas's strokes count while none is erased.
`step` applies the rule at the explorer's crossroads `v`: if some path at `v` has no stroke,
the chooser `pick` takes one; if that leads to a crossroads already on the route, rule 2 sends
the explorer straight back, and both crossings are made in the same step; if it leads to a new
crossroads the explorer enters it (rule 1). If every path at `v` has a stroke, `pick` takes one
with exactly one stroke (rule 3, and the dead end of rule 1). If none, the explorer stops.
Rules 1 and 3 thus become one choice: a path without a stroke first, else one with a single
stroke. The chooser is any function of the whole state (`Chooser.Valid`: it picks one of the
paths offered), so the theorems cover every way of making the choices the rule leaves open.
`Explorer.parent` records the crossroads each crossroads was first entered from; `step` never
reads it (a chooser is handed it, which is harmless: it follows from the route).

## Main results

For a finite connected graph, any start `s` and any valid chooser, with `tremaux G s pick` the
explorer after the run:

* `tremaux_stops`: the explorer has stopped by the rule (`step` gives `none`) and stands at `s`;
  the route is a walk from `s` back to `s`.
* `tremaux_visits_all`: every vertex is on the route.
* `tremaux_crosses_twice`: every dart (an edge with a direction) occurs exactly once in the
  route; so every edge is crossed exactly twice, once each way.
* `isTremauxTree_of_tremaux`: the first-entry parents form a **Trémaux tree** (`IsTremauxTree`):
  a tree rooted at `s` whose edges are edges of the graph, in which every edge of the graph
  joins a vertex to one of its ancestors. Its edges are the paths of rule 1.

The proof keeps one invariant (`Inv`) through the three kinds of step: no crossing is
repeated; a path with one stroke is the edge from a vertex on the current path back to `s` to
its parent; a crossroads off that path has two strokes on every path; every crossed path joins
a vertex to an ancestor. A route without repeats has at most `card V ^ 2` crossings, so the
explorer stops within that many steps.

## Hypotheses

Checked in order LEAN-25 (`~/lean/lean25-checks/checks.py`, by simulating Lucas's rule one
crossing at a time with strokes at each end and every possible choice, on seven small graphs):

* The rule itself: all 186 runs (every start, every choice) end at the start with every path
  crossed once each way, and every first-entry tree is a Trémaux tree.
* The marks. With one stroke erased, the guarantee fails: in 9,521 of 19,417 simulated runs with
  one stroke erased (any one stroke, between any two crossings; the Lean model has no erasure)
  some path is not crossed exactly twice or the explorer stops away from the start; in 9,384 of
  them some path is crossed more than twice. On the triangle `0, 1, 2` from `0`: after
  `0 → 1 → 2 → 0` and rule 2's return to `2`, erase the stroke at `1`'s end of path `12`; the
  explorer takes `2 → 1`, sees a path with one stroke arriving at an explored crossroads, so
  rule 2 sends it back to `2`, where it stops: path `12` crossed `3` times, path `01` once, and
  the explorer is not at the start.
* Connectedness: without it the vertices and edges outside the start's component are never
  reached (two vertices, no edge: the explorer stops at once at `s`), so
  `tremaux_visits_all`, `tremaux_crosses_twice` and `isTremauxTree_of_tremaux` fail;
  `tremaux_stops` does not need it.
* A valid chooser: a chooser that picks something not offered can stop the run early (on the
  path `0 – 1 – 2` from `0`, picking `2`, not a neighbour, makes `step` give `none` at once, so
  `2` is never visited; by hand).

## Mathlib at v4.34.0

Searched before this file was written (order LEAN-25, `grep -rliE`): "Tr.maux|depth.first|dfs"
18 files, all the `order` tactic's internal search or unrelated words; Mathlib has no theorem
on exploring a graph. Used: `SimpleGraph.Walk`, `Walk.concat`, `Walk.darts`, `Connected`.
Even's book and Tarry's paper are not cited here; only Lucas's text, which was read.
-/

open Finset

namespace ClassicalLean.Combinatorics

namespace Tremaux

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- The explorer: where it is, the route walked from the start `s`, and, for bookkeeping only
(`step` never reads it), the vertex each vertex was first entered from. -/
structure Explorer (G : SimpleGraph V) (s : V) where
  pos : V
  walk : G.Walk s pos
  parent : V → Option V

/-- Crossings of the path `ux` from `u` to `x`. -/
def cross {s v : V} (W : G.Walk s v) (u x : V) : ℕ := (W.darts.map fun d ↦ d.toProd).count (u, x)

/-- Strokes at `u`'s end of the path `ux`: one for each crossing of `ux`, either way (Lucas,
p. 47). -/
def marks {s v : V} (W : G.Walk s v) (u x : V) : ℕ := cross W u x + cross W x u

/-- The paths at the explorer's crossroads `v` with exactly `k` strokes at `v`'s end. -/
def passages [Fintype V] [DecidableRel G.Adj] {s v : V} (W : G.Walk s v) (k : ℕ) : Finset V :=
  univ.filter fun w ↦ G.Adj v w ∧ marks W v w = k

/-- A chooser: any rule for picking among the passages the rule allows; it may look at
everything, the whole route included. -/
def Chooser (G : SimpleGraph V) (s : V) := Explorer G s → Finset V → V

/-- A chooser is valid when it picks one of the passages it is offered. -/
def Chooser.Valid {s : V} (pick : Chooser G s) : Prop :=
  ∀ E c, c.Nonempty → pick E c ∈ c

/-- **One step of Trémaux's rule** at the crossroads `v = E.pos`, or `none` when the explorer
stops. If some path at `v` has no stroke, take one (`pick`); if it leads to a crossroads
already on the route, rule 2 sends the explorer straight back (both crossings in this step);
otherwise the new crossroads is entered (rule 1) and `v` recorded as its parent. If every path
at `v` has a stroke, take one with exactly one stroke (rule 3). Otherwise stop. -/
def step [Fintype V] [DecidableRel G.Adj] {s : V} (pick : Chooser G s) (E : Explorer G s) :
    Option (Explorer G s) :=
  if (passages E.walk 0).Nonempty then
    if h : G.Adj E.pos (pick E (passages E.walk 0)) then
      if pick E (passages E.walk 0) ∈ E.walk.support then
        some ⟨E.pos, (E.walk.concat h).concat h.symm, E.parent⟩
      else
        some ⟨_, E.walk.concat h,
          Function.update E.parent (pick E (passages E.walk 0)) (some E.pos)⟩
    else none
  else if (passages E.walk 1).Nonempty then
    if h : G.Adj E.pos (pick E (passages E.walk 1)) then
      some ⟨_, E.walk.concat h, E.parent⟩
    else none
  else none

/-- Run the rule for at most `n` steps. -/
def run [Fintype V] [DecidableRel G.Adj] {s : V} (pick : Chooser G s) :
    ℕ → Explorer G s → Explorer G s
  | 0, E => E
  | n + 1, E => match step pick E with
    | none => E
    | some E' => run pick n E'

/-- The explorer at the start, before any crossing. -/
def start (G : SimpleGraph V) (s : V) : Explorer G s := ⟨s, .nil, fun _ ↦ none⟩

/-- The explorer after the rule has been run for `card V ^ 2` steps, more than it ever needs
(`step_tremaux`). -/
def tremaux [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (pick : Chooser G s) :
    Explorer G s :=
  run pick (Fintype.card V ^ 2) (start G s)

/-- `b` is `a` or an ancestor of `a` for the parents `par`. -/
def Anc (par : V → Option V) (a b : V) : Prop :=
  Relation.ReflTransGen (fun a b ↦ par a = some b) a b

/-! ### Walk bookkeeping -/

/-- One more crossing `v → w` adds one to the count of `(v, w)`. -/
theorem cross_concat {s v w : V} (W : G.Walk s v) (h : G.Adj v w) (u x : V) :
    cross (W.concat h) u x = cross W u x + if (v, w) = (u, x) then 1 else 0 := by
  rw [cross, cross, SimpleGraph.Walk.darts_concat, List.concat_eq_append, List.map_append,
    List.count_append]
  congr 1
  simp only [List.map_cons, List.map_nil, List.count_cons, List.count_nil, zero_add]
  by_cases hh : (v, w) = (u, x) <;> simp [hh]

/-- On a route that never repeats a crossing, each crossing is counted at most once. -/
theorem cross_le_one {s v : V} {W : G.Walk s v} (hW : (W.darts.map fun d ↦ d.toProd).Nodup)
    (u x : V) : cross W u x ≤ 1 := List.nodup_iff_count_le_one.mp hW _

/-- A crossed path is an edge. -/
theorem adj_of_cross_pos {s v : V} {W : G.Walk s v} {u x : V} (h : 0 < cross W u x) :
    G.Adj u x := by
  obtain ⟨d, hd, hdx⟩ := List.mem_map.mp (List.count_pos_iff.mp h)
  have h1 : d.fst = u := congrArg Prod.fst hdx
  have h2 : d.snd = x := congrArg Prod.snd hdx
  exact h1 ▸ h2 ▸ d.adj

/-- Both ends of a crossed path are on the route. -/
theorem mem_support_of_cross_pos {s v : V} {W : G.Walk s v} {u x : V} (h : 0 < cross W u x) :
    u ∈ W.support ∧ x ∈ W.support := by
  obtain ⟨d, hd, hdx⟩ := List.mem_map.mp (List.count_pos_iff.mp h)
  have h1 := W.dart_fst_mem_support_of_mem_darts hd
  have h2 := W.dart_snd_mem_support_of_mem_darts hd
  have e1 : d.fst = u := congrArg Prod.fst hdx
  have e2 : d.snd = x := congrArg Prod.snd hdx
  exact ⟨e1 ▸ h1, e2 ▸ h2⟩

/-- Strokes at either end of a path are equal while no stroke is erased. -/
theorem marks_comm {s v : V} (W : G.Walk s v) (u x : V) : marks W u x = marks W x u :=
  Nat.add_comm _ _

/-! ### The three kinds of step -/

/-- What a step can be: rule 2 (there and back), rule 1 (to a new crossroads), rule 3 (along a
path with one stroke, when every path has a stroke). -/
theorem step_eq_some [Fintype V] [DecidableRel G.Adj] {s : V} {pick : Chooser G s}
    (hpick : pick.Valid) {E E' : Explorer G s}
    (h : step pick E = some E') :
    (∃ w, ∃ hvw : G.Adj E.pos w, marks E.walk E.pos w = 0 ∧ w ∈ E.walk.support ∧
      E' = ⟨E.pos, (E.walk.concat hvw).concat hvw.symm, E.parent⟩) ∨
    (∃ w, ∃ hvw : G.Adj E.pos w, marks E.walk E.pos w = 0 ∧ w ∉ E.walk.support ∧
      E' = ⟨w, E.walk.concat hvw, Function.update E.parent w (some E.pos)⟩) ∨
    (∃ w, ∃ hvw : G.Adj E.pos w, marks E.walk E.pos w = 1 ∧
      (∀ x, G.Adj E.pos x → marks E.walk E.pos x ≠ 0) ∧
      E' = ⟨w, E.walk.concat hvw, E.parent⟩) := by
  unfold step at h
  split_ifs at h with h0 ha hs h1 hb
  · have hm := (mem_filter.mp (hpick E _ h0)).2.2
    exact Or.inl ⟨_, ha, hm, hs, (Option.some.inj h).symm⟩
  · have hm := (mem_filter.mp (hpick E _ h0)).2.2
    exact Or.inr (Or.inl ⟨_, ha, hm, hs, (Option.some.inj h).symm⟩)
  · have hm := (mem_filter.mp (hpick E _ h1)).2.2
    refine Or.inr (Or.inr ⟨_, hb, hm, fun x hx hx0 ↦ h0 ⟨x, ?_⟩, (Option.some.inj h).symm⟩)
    exact mem_filter.mpr ⟨mem_univ _, hx, hx0⟩

/-- When the explorer stops, every path at its crossroads has at least two strokes. -/
theorem step_eq_none [Fintype V] [DecidableRel G.Adj] {s : V} {pick : Chooser G s}
    (hpick : pick.Valid) {E : Explorer G s}
    (h : step pick E = none) : ∀ x, G.Adj E.pos x → 2 ≤ marks E.walk E.pos x := by
  intro x hx
  by_contra hlt
  push Not at hlt
  unfold step at h
  by_cases h0 : (passages E.walk 0).Nonempty
  · have ha : G.Adj E.pos (pick E (passages E.walk 0)) := (mem_filter.mp (hpick E _ h0)).2.1
    simp only [h0, ha, ↓reduceIte, ↓reduceDIte] at h
    split_ifs at h
  · simp only [h0, ↓reduceIte] at h
    by_cases h1 : (passages E.walk 1).Nonempty
    · have hb : G.Adj E.pos (pick E (passages E.walk 1)) := (mem_filter.mp (hpick E _ h1)).2.1
      simp [h1, hb] at h
    · rcases (show marks E.walk E.pos x = 0 ∨ marks E.walk E.pos x = 1 by omega) with hx' | hx'
      · exact h0 ⟨x, mem_filter.mpr ⟨mem_univ _, hx, hx'⟩⟩
      · exact h1 ⟨x, mem_filter.mpr ⟨mem_univ _, hx, hx'⟩⟩

/-! ### Ancestors -/

omit [DecidableEq V] in
/-- Ancestors through the first parent. -/
theorem anc_head {par : V → Option V} {a b c : V} (hab : par a = some b) :
    Anc par a c ↔ c = a ∨ Anc par b c := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h | ⟨d, had, hdc⟩
    · exact Or.inl h.symm
    · rw [hab, Option.some.injEq] at had
      exact Or.inr (had ▸ hdc)
  · rintro (rfl | h)
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head hab h

omit [DecidableEq V] in
/-- With one parent each, a vertex on a cycle passes the cycle on to every ancestor. -/
theorem transGen_of_cycle {par : V → Option V} {a c : V} (h : Anc par a c) :
    Relation.TransGen (fun a b ↦ par a = some b) a a →
      Relation.TransGen (fun a b ↦ par a = some b) c c := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact id
  | head hab _ ih =>
    intro haa
    obtain ⟨b', hab', hb'a⟩ := Relation.TransGen.head'_iff.mp haa
    rw [hab, Option.some.injEq] at hab'
    subst hab'
    exact ih (Relation.TransGen.tail' hb'a hab)

omit [DecidableEq V] in
/-- A set closed under taking parents contains the ancestors of its members. -/
theorem anc_mem {par : V → Option V} {S : Set V} (hS : ∀ a p, par a = some p → a ∈ S → p ∈ S)
    {a b : V} (h : Anc par a b) (ha : a ∈ S) : b ∈ S := by
  induction h with
  | refl => exact ha
  | tail _ hbc ih => exact hS _ _ hbc ih

/-- Giving a parent to a vertex outside a parent-closed set does not change ancestry inside it. -/
theorem anc_update {par : V → Option V} {S : Set V} (hS : ∀ a p, par a = some p → a ∈ S → p ∈ S)
    {w v : V} (hw : w ∉ S) {a b : V} (ha : a ∈ S) :
    Anc (Function.update par w (some v)) a b ↔ Anc par a b := by
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact Relation.ReflTransGen.refl
    | @head x y hxy _ ih =>
      have hx : x ≠ w := fun e ↦ hw (e ▸ ha)
      rw [Function.update_of_ne hx] at hxy
      exact Relation.ReflTransGen.head hxy (ih (hS _ _ hxy ha))
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact Relation.ReflTransGen.refl
    | @head x y hxy _ ih =>
      have hx : x ≠ w := fun e ↦ hw (e ▸ ha)
      exact Relation.ReflTransGen.head (by rwa [Function.update_of_ne hx]) (ih (hS _ _ hxy ha))

/-! ### Marks after a crossing -/

/-- One more crossing `v → w` adds one stroke at each end of `vw`. -/
theorem marks_concat {s v w : V} (W : G.Walk s v) (h : G.Adj v w) (u x : V) :
    marks (W.concat h) u x =
      marks W u x + if (v, w) = (u, x) ∨ (v, w) = (x, u) then 1 else 0 := by
  have hvw : v ≠ w := h.ne
  unfold marks
  rw [cross_concat, cross_concat]
  by_cases h1 : (v, w) = (u, x)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    have h2 : (v, w) ≠ (w, v) := fun e ↦ hvw (Prod.mk.inj e).1
    simp only [h2, ↓reduceIte, true_or]
    omega
  · by_cases h2 : (v, w) = (x, u)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
      simp only [h1, ↓reduceIte, or_true]
      omega
    · simp only [h1, h2, ↓reduceIte, or_self]
      omega

/-- On a route that never repeats a crossing, a path has at most two strokes at an end. -/
theorem marks_le_two {s v : V} {W : G.Walk s v} (hW : (W.darts.map fun d ↦ d.toProd).Nodup)
    (u x : V) : marks W u x ≤ 2 := by
  have := cross_le_one hW u x; have := cross_le_one hW x u; unfold marks; omega

/-- A crossing counted zero times is not on the route. -/
theorem not_mem_of_cross_eq_zero {s v : V} {W : G.Walk s v} {u x : V} (h : cross W u x = 0) :
    (u, x) ∉ W.darts.map fun d ↦ d.toProd := fun hm ↦ by
  have := List.count_pos_iff.mpr hm; unfold cross at h; omega

/-! ### The invariant -/

/-- What holds after every step: `W` the route, `v` the position, `par` the first-entry
parents. -/
structure Inv {s : V} (E : Explorer G s) : Prop where
  nodup : (E.walk.darts.map fun d ↦ d.toProd).Nodup
  par_s : E.parent s = none
  par_adj : ∀ u p, E.parent u = some p → G.Adj p u ∧ p ∈ E.walk.support ∧ u ∈ E.walk.support
  anc_s : ∀ u ∈ E.walk.support, Anc E.parent u s
  once : ∀ u x, marks E.walk u x = 1 →
    (E.parent x = some u ∧ Anc E.parent E.pos x ∧ cross E.walk x u = 0) ∨
    (E.parent u = some x ∧ Anc E.parent E.pos u ∧ cross E.walk u x = 0)
  path : ∀ x, Anc E.parent E.pos x → x ≠ s → ∃ u, E.parent x = some u ∧ marks E.walk u x = 1
  finished : ∀ u ∈ E.walk.support, ¬ Anc E.parent E.pos u →
    ∀ x, G.Adj u x → marks E.walk u x = 2
  tree : ∀ u x, 0 < marks E.walk u x → Anc E.parent u x ∨ Anc E.parent x u

/-- The route is closed under taking parents. -/
theorem Inv.par_closed {s : V} {E : Explorer G s} (hE : Inv E) :
    ∀ a p, E.parent a = some p → a ∈ {x | x ∈ E.walk.support} → p ∈ {x | x ∈ E.walk.support} :=
  fun a p h _ ↦ (hE.par_adj a p h).2.1

/-- No vertex is an ancestor of its own parent: parents form no cycle. -/
theorem Inv.not_anc_of_parent {s : V} {E : Explorer G s} (hE : Inv E) {u x : V}
    (h : E.parent x = some u) : ¬ Anc E.parent u x := by
  intro hux
  have hx := (hE.par_adj x u h).2.2
  have hcyc : Relation.TransGen (fun a b ↦ E.parent a = some b) x x :=
    Relation.TransGen.head' h hux
  have hs := transGen_of_cycle (hE.anc_s x hx) hcyc
  obtain ⟨b, hb, -⟩ := Relation.TransGen.head'_iff.mp hs
  rw [hE.par_s] at hb
  simp at hb

/-- The invariant holds at the start. -/
theorem inv_start (s : V) : Inv (start G s) := by
  have hR : ∀ a b, Anc (start G s).parent a b → b = a := fun a b h ↦ by
    induction h with
    | refl => rfl
    | tail _ hbc _ => simp [start] at hbc
  have hm : ∀ u x, marks (start G s).walk u x = 0 := fun u x ↦ by simp [marks, cross, start]
  refine ⟨by simp [start], rfl, fun u p h ↦ by simp [start] at h, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    simp only [start, SimpleGraph.Walk.support_nil, List.mem_singleton] at hu
    exact hu ▸ Relation.ReflTransGen.refl
  · intro u x h; rw [hm] at h; omega
  · intro x hx hxs; exact absurd (hR _ _ hx) hxs
  · intro u hu hn
    simp only [start, SimpleGraph.Walk.support_nil, List.mem_singleton] at hu
    exact absurd (hu ▸ Relation.ReflTransGen.refl) hn
  · intro u x h; rw [hm] at h; exact absurd h (lt_irrefl 0)

/-! ### Helpers for one crossing -/

/-- `{u, x}` is the edge `{v, w}`. -/
def SameEdge (v w u x : V) : Prop := (u = v ∧ x = w) ∨ (u = w ∧ x = v)

/-- A crossing of `vw` leaves the strokes on other paths alone. -/
theorem marks_concat_of_not {s v w : V} (W : G.Walk s v) (h : G.Adj v w) {u x : V}
    (hq : ¬ SameEdge v w u x) : marks (W.concat h) u x = marks W u x := by
  rw [marks_concat]
  have : ¬ ((v, w) = (u, x) ∨ (v, w) = (x, u)) := by
    rintro (e | e) <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    · exact hq (Or.inl ⟨rfl, rfl⟩)
    · exact hq (Or.inr ⟨rfl, rfl⟩)
  simp only [this, ↓reduceIte, add_zero]

/-- A crossing of `vw` adds a stroke at `v`'s end of it. -/
theorem marks_concat_self {s v w : V} (W : G.Walk s v) (h : G.Adj v w) :
    marks (W.concat h) v w = marks W v w + 1 := by
  rw [marks_concat]; simp

/-- A crossing `v → w` leaves other crossing counts alone. -/
theorem cross_concat_of_ne {s v w : V} (W : G.Walk s v) (h : G.Adj v w) {u x : V}
    (hq : (v, w) ≠ (u, x)) : cross (W.concat h) u x = cross W u x := by
  rw [cross_concat]; simp [hq]

/-- A crossing not made before keeps the route free of repeats. -/
theorem nodup_concat {s v w : V} {W : G.Walk s v} (h : G.Adj v w)
    (hW : (W.darts.map fun d ↦ d.toProd).Nodup) (hn : cross W v w = 0) :
    ((W.concat h).darts.map fun d ↦ d.toProd).Nodup := by
  rw [SimpleGraph.Walk.darts_concat, List.map_concat]
  exact hW.concat (not_mem_of_cross_eq_zero hn)

omit [DecidableEq V] in
/-- The route after one more crossing to `w`. -/
theorem mem_support_concat {s v w : V} (W : G.Walk s v) (h : G.Adj v w) (u : V) :
    u ∈ (W.concat h).support ↔ u ∈ W.support ∨ u = w := by
  rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton]

/-- A path with no stroke at one end has none at the other. -/
theorem marks_eq_zero_of_sameEdge {s v' v w : V} {W : G.Walk s v'} (h0 : marks W v w = 0)
    {u x : V} (hq : SameEdge v w u x) : marks W u x = 0 := by
  rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h0
  · rw [marks_comm]; exact h0

/-! ### Rule 2: there and back -/

/-- Rule 2 keeps the invariant: a new path to a crossroads already on the route leads to the
current path, and going there and back gives it two strokes at each end. -/
theorem inv_rule2 {s : V} {E : Explorer G s} (hE : Inv E) {w : V} (hvw : G.Adj E.pos w)
    (h0 : marks E.walk E.pos w = 0) (hw : w ∈ E.walk.support) :
    Inv (⟨E.pos, (E.walk.concat hvw).concat hvw.symm, E.parent⟩ : Explorer G s) := by
  obtain ⟨v, W, par⟩ := E
  simp only at hvw h0 hw ⊢
  have hne : v ≠ w := hvw.ne
  have hv : v ∈ W.support := W.end_mem_support
  -- marks after the two crossings
  have hmk : ∀ u x, ¬ SameEdge v w u x →
      marks ((W.concat hvw).concat hvw.symm) u x = marks W u x := fun u x hq ↦ by
    rw [marks_concat_of_not _ _ (fun h ↦ hq (h.elim (fun h ↦ Or.inr ⟨h.1, h.2⟩)
      fun h ↦ Or.inl ⟨h.1, h.2⟩)), marks_concat_of_not _ _ hq]
  have hmvw : marks ((W.concat hvw).concat hvw.symm) v w = 2 := by
    rw [marks_comm, marks_concat_self, marks_comm, marks_concat_self, h0]
  have hmk2 : ∀ u x, SameEdge v w u x → marks ((W.concat hvw).concat hvw.symm) u x = 2 := by
    rintro u x (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hmvw
    · rw [marks_comm]; exact hmvw
  have hsupp : ∀ u, u ∈ ((W.concat hvw).concat hvw.symm).support ↔ u ∈ W.support := fun u ↦ by
    rw [mem_support_concat, mem_support_concat]
    constructor
    · rintro ((h | rfl) | rfl) <;> assumption
    · exact fun h ↦ Or.inl (Or.inl h)
  have hcw : cross W w v = 0 := by unfold marks at h0; omega
  have hcv : cross W v w = 0 := by unfold marks at h0; omega
  -- `w` is on the current path, else it would be finished
  have hanc : Anc par v w := by
    by_contra hn
    have := hE.finished w hw hn v hvw.symm
    rw [marks_comm, h0] at this
    exact absurd this (by omega)
  refine ⟨?_, hE.par_s, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine nodup_concat _ (nodup_concat _ hE.nodup hcv) ?_
    rw [cross_concat_of_ne _ _ (fun e ↦ hne (Prod.mk.inj e).1), hcw]
  · intro u p hp
    obtain ⟨h1, h2, h3⟩ := hE.par_adj u p hp
    exact ⟨h1, (hsupp p).mpr h2, (hsupp u).mpr h3⟩
  · intro u hu; exact hE.anc_s u ((hsupp u).mp hu)
  · intro u x h1
    by_cases hq : SameEdge v w u x
    · rw [hmk2 u x hq] at h1; exact absurd h1 (by omega)
    · rw [hmk u x hq] at h1
      have hq' : ¬ SameEdge v w x u := fun h ↦ hq (h.elim (fun h ↦ Or.inr ⟨h.2, h.1⟩)
        fun h ↦ Or.inl ⟨h.2, h.1⟩)
      have hc : ∀ a b, ¬ SameEdge v w a b →
          cross ((W.concat hvw).concat hvw.symm) a b = cross W a b := fun a b hab ↦ by
        rw [cross_concat_of_ne _ _ (fun e ↦ hab (Or.inr ⟨(Prod.mk.inj e).1.symm,
          (Prod.mk.inj e).2.symm⟩)), cross_concat_of_ne _ _ (fun e ↦ hab (Or.inl
          ⟨(Prod.mk.inj e).1.symm, (Prod.mk.inj e).2.symm⟩))]
      rcases hE.once u x h1 with ⟨a, b, c⟩ | ⟨a, b, c⟩
      · exact Or.inl ⟨a, b, by rw [hc x u hq']; exact c⟩
      · exact Or.inr ⟨a, b, by rw [hc u x hq]; exact c⟩
  · intro x hx hxs
    obtain ⟨u, hu, hm⟩ := hE.path x hx hxs
    refine ⟨u, hu, ?_⟩
    by_cases hq : SameEdge v w u x
    · rw [marks_eq_zero_of_sameEdge h0 hq] at hm; exact absurd hm (by omega)
    · rw [hmk u x hq]; exact hm
  · intro u hu hn x hx
    by_cases hq : SameEdge v w u x
    · exact hmk2 u x hq
    · rw [hmk u x hq]; exact hE.finished u ((hsupp u).mp hu) hn x hx
  · intro u x hpos
    by_cases hq : SameEdge v w u x
    · rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl hanc
      · exact Or.inr hanc
    · rw [hmk u x hq] at hpos; exact hE.tree u x hpos

/-- Both ends of a path with strokes are on the route. -/
theorem mem_support_of_marks_pos {s v : V} {W : G.Walk s v} {u x : V} (h : 0 < marks W u x) :
    u ∈ W.support ∧ x ∈ W.support := by
  unfold marks at h
  rcases Nat.eq_zero_or_pos (cross W u x) with h1 | h1
  · rw [h1, zero_add] at h
    exact (mem_support_of_cross_pos h).symm
  · exact mem_support_of_cross_pos h1

omit [DecidableEq V] in
/-- `SameEdge` does not depend on the order of `u` and `x`. -/
theorem sameEdge_symm {v w u x : V} (h : SameEdge v w u x) : SameEdge v w x u :=
  h.elim (fun h ↦ Or.inr ⟨h.2, h.1⟩) fun h ↦ Or.inl ⟨h.2, h.1⟩

omit [DecidableEq V] in
/-- A path other than `vw` is not the crossing `v → w`. -/
theorem ne_of_not_sameEdge {v w u x : V} (h : ¬ SameEdge v w u x) : (v, w) ≠ (u, x) :=
  fun e ↦ h (Or.inl ⟨(Prod.mk.inj e).1.symm, (Prod.mk.inj e).2.symm⟩)

/-! ### Rule 1: to a new crossroads -/

/-- Rule 1 keeps the invariant: the new crossroads joins the current path, its parent the
crossroads it was entered from. -/
theorem inv_rule1 {s : V} {E : Explorer G s} (hE : Inv E) {w : V} (hvw : G.Adj E.pos w)
    (h0 : marks E.walk E.pos w = 0) (hw : w ∉ E.walk.support) :
    Inv (⟨w, E.walk.concat hvw, Function.update E.parent w (some E.pos)⟩ : Explorer G s) := by
  have hS := hE.par_closed
  obtain ⟨v, W, par⟩ := E
  simp only at hvw h0 hw hS ⊢
  have hv : v ∈ W.support := W.end_mem_support
  have hpw : Function.update par w (some v) w = some v := Function.update_self _ _ _
  have hpar : ∀ a, a ≠ w → Function.update par w (some v) a = par a :=
    fun a ha ↦ Function.update_of_ne ha _ _
  have hupd : ∀ a b, a ∈ W.support →
      (Anc (Function.update par w (some v)) a b ↔ Anc par a b) :=
    fun a b ha ↦ anc_update (S := {x | x ∈ W.support}) hS hw ha
  have hancw : ∀ b, Anc (Function.update par w (some v)) w b ↔ b = w ∨ Anc par v b :=
    fun b ↦ by rw [anc_head hpw, hupd v b hv]
  have hmk : ∀ u x, ¬ SameEdge v w u x → marks (W.concat hvw) u x = marks W u x :=
    fun u x hq ↦ marks_concat_of_not _ _ hq
  have hm1 : ∀ u x, SameEdge v w u x → marks (W.concat hvw) u x = 1 := by
    rintro u x (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [marks_concat_self, h0]
    · rw [marks_comm, marks_concat_self, h0]
  have hcv : cross W v w = 0 := by unfold marks at h0; omega
  have hcw : cross W w v = 0 := by unfold marks at h0; omega
  have hcw' : cross (W.concat hvw) w v = 0 := by
    rw [cross_concat_of_ne _ _ (fun e ↦ hvw.ne (Prod.mk.inj e).1), hcw]
  have hsupp : ∀ u, u ∈ (W.concat hvw).support ↔ u ∈ W.support ∨ u = w :=
    mem_support_concat W hvw
  refine ⟨nodup_concat _ hE.nodup hcv, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals dsimp only
  · rw [hpar s (fun e ↦ hw (e ▸ W.start_mem_support))]; exact hE.par_s
  · intro u p hp
    by_cases hu : u = w
    · subst hu
      rw [hpw, Option.some.injEq] at hp
      subst hp
      exact ⟨hvw, (hsupp _).mpr (Or.inl hv), (hsupp _).mpr (Or.inr rfl)⟩
    · rw [hpar u hu] at hp
      obtain ⟨h1, h2, h3⟩ := hE.par_adj u p hp
      exact ⟨h1, (hsupp p).mpr (Or.inl h2), (hsupp u).mpr (Or.inl h3)⟩
  · intro u hu
    rcases (hsupp u).mp hu with hu | rfl
    · exact (hupd u s hu).mpr (hE.anc_s u hu)
    · exact (hancw s).mpr (Or.inr (hE.anc_s v hv))
  · intro u x h1
    by_cases hq : SameEdge v w u x
    · rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨hpw, Relation.ReflTransGen.refl, hcw'⟩
      · exact Or.inr ⟨hpw, Relation.ReflTransGen.refl, hcw'⟩
    · rw [hmk u x hq] at h1
      rcases hE.once u x h1 with ⟨a, b, c⟩ | ⟨a, b, c⟩
      · have hx : x ≠ w := fun e ↦ hw (e ▸ (hE.par_adj x u a).2.2)
        refine Or.inl ⟨by rw [hpar x hx]; exact a, (hancw x).mpr (Or.inr b), ?_⟩
        rw [cross_concat_of_ne _ _ (ne_of_not_sameEdge fun h ↦ hq (sameEdge_symm h))]
        exact c
      · have hu : u ≠ w := fun e ↦ hw (e ▸ (hE.par_adj u x a).2.2)
        refine Or.inr ⟨by rw [hpar u hu]; exact a, (hancw u).mpr (Or.inr b), ?_⟩
        rw [cross_concat_of_ne _ _ (ne_of_not_sameEdge hq)]
        exact c
  · intro x hx hxs
    rcases (hancw x).mp hx with rfl | hx
    · exact ⟨v, hpw, hm1 v x (Or.inl ⟨rfl, rfl⟩)⟩
    · obtain ⟨u, hu, hm⟩ := hE.path x hx hxs
      have hxS : x ∈ W.support := anc_mem (S := {x | x ∈ W.support}) hS hx hv
      have hxw : x ≠ w := fun e ↦ hw (e ▸ hxS)
      refine ⟨u, by rw [hpar x hxw]; exact hu, ?_⟩
      by_cases hq : SameEdge v w u x
      · rw [marks_eq_zero_of_sameEdge h0 hq] at hm; exact absurd hm (by omega)
      · rw [hmk u x hq]; exact hm
  · intro u hu hn x hx
    have huw : u ≠ w := fun e ↦ hn (e ▸ Relation.ReflTransGen.refl)
    have hu' : u ∈ W.support := ((hsupp u).mp hu).resolve_right huw
    have hn' : ¬ Anc par v u := fun h ↦ hn ((hancw u).mpr (Or.inr h))
    have h2 := hE.finished u hu' hn' x hx
    by_cases hq : SameEdge v w u x
    · rw [marks_eq_zero_of_sameEdge h0 hq] at h2; exact absurd h2 (by omega)
    · rw [hmk u x hq]; exact h2
  · intro u x hpos
    by_cases hq : SameEdge v w u x
    · have hwv : Anc (Function.update par w (some v)) w v :=
        Relation.ReflTransGen.head hpw Relation.ReflTransGen.refl
      rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr hwv
      · exact Or.inl hwv
    · rw [hmk u x hq] at hpos
      obtain ⟨hu, hx⟩ := mem_support_of_marks_pos hpos
      rcases hE.tree u x hpos with h | h
      · exact Or.inl ((hupd u x hu).mpr h)
      · exact Or.inr ((hupd x u hx).mpr h)

/-! ### Rule 3: back along a path followed once -/

/-- Rule 3 keeps the invariant: the one path with one stroke leads to the parent, and leaving
finishes the crossroads. -/
theorem inv_rule3 {s : V} {E : Explorer G s} (hE : Inv E) {w : V} (hvw : G.Adj E.pos w)
    (h1 : marks E.walk E.pos w = 1) (hall : ∀ x, G.Adj E.pos x → marks E.walk E.pos x ≠ 0) :
    Inv (⟨w, E.walk.concat hvw, E.parent⟩ : Explorer G s) := by
  have hnot := @Inv.not_anc_of_parent _ _ _ _ _ hE
  obtain ⟨v, W, par⟩ := E
  simp only at hvw h1 hall hnot ⊢
  have hne : v ≠ w := hvw.ne
  obtain ⟨hpv, -, hcv⟩ : par v = some w ∧ Anc par v v ∧ cross W v w = 0 := by
    rcases hE.once v w h1 with ⟨a, b, -⟩ | h
    · exact absurd b (hnot a)
    · exact h
  have hancv : ∀ b, Anc par v b ↔ b = v ∨ Anc par w b := fun b ↦ anc_head hpv
  have hnwv : ¬ Anc par w v := hnot hpv
  have hvw' : Anc par v w := Relation.ReflTransGen.head hpv Relation.ReflTransGen.refl
  have hmk : ∀ u x, ¬ SameEdge v w u x → marks (W.concat hvw) u x = marks W u x :=
    fun u x hq ↦ marks_concat_of_not _ _ hq
  have hm2 : ∀ u x, SameEdge v w u x → marks (W.concat hvw) u x = 2 := by
    rintro u x (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [marks_concat_self, h1]
    · rw [marks_comm, marks_concat_self, h1]
  have hwS : w ∈ W.support := (hE.par_adj v w hpv).2.1
  have hsupp : ∀ u, u ∈ (W.concat hvw).support ↔ u ∈ W.support := fun u ↦ by
    rw [mem_support_concat]
    exact ⟨fun h ↦ h.elim id fun e ↦ e ▸ hwS, Or.inl⟩
  refine ⟨nodup_concat _ hE.nodup hcv, hE.par_s, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals dsimp only
  · intro u p hp
    obtain ⟨a, b, c⟩ := hE.par_adj u p hp
    exact ⟨a, (hsupp p).mpr b, (hsupp u).mpr c⟩
  · intro u hu; exact hE.anc_s u ((hsupp u).mp hu)
  · intro u x h
    by_cases hq : SameEdge v w u x
    · rw [hm2 u x hq] at h; exact absurd h (by omega)
    · rw [hmk u x hq] at h
      rcases hE.once u x h with ⟨a, b, c⟩ | ⟨a, b, c⟩ <;> dsimp only at a b c
      · rcases (hancv x).mp b with rfl | b
        · rw [hpv, Option.some.injEq] at a
          exact absurd (Or.inr ⟨a.symm, rfl⟩) hq
        · refine Or.inl ⟨a, b, ?_⟩
          rw [cross_concat_of_ne _ _ (ne_of_not_sameEdge fun h ↦ hq (sameEdge_symm h))]
          exact c
      · rcases (hancv u).mp b with rfl | b
        · rw [hpv, Option.some.injEq] at a
          exact absurd (Or.inl ⟨rfl, a.symm⟩) hq
        · refine Or.inr ⟨a, b, ?_⟩
          rw [cross_concat_of_ne _ _ (ne_of_not_sameEdge hq)]
          exact c
  · intro x hx hxs
    obtain ⟨u, hu, hm⟩ := hE.path x (Relation.ReflTransGen.head hpv hx) hxs
    refine ⟨u, hu, ?_⟩
    by_cases hq : SameEdge v w u x
    · rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd hvw' (hnot hu)
      · exact absurd hx hnwv
    · rw [hmk u x hq]; exact hm
  · intro u hu hn x hx
    have hu' := (hsupp u).mp hu
    by_cases huv : u = v
    · subst huv
      by_cases hxw : x = w
      · subst hxw; exact hm2 _ _ (Or.inl ⟨rfl, rfl⟩)
      · have hq : ¬ SameEdge u w u x := by
          rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact hxw h
          · exact hne h
        rw [hmk u x hq]
        have h0 := hall x hx
        have hle := marks_le_two hE.nodup u x
        dsimp only at hle
        by_contra h2
        have hx1 : marks W u x = 1 := by omega
        rcases hE.once u x hx1 with ⟨a, b, -⟩ | ⟨a, -, -⟩ <;> dsimp only at a
        · exact hnot a b
        · rw [hpv, Option.some.injEq] at a; exact hxw a.symm
    · have hn' : ¬ Anc par v u := fun h ↦ ((hancv u).mp h).elim huv hn
      have h2 := hE.finished u hu' hn' x hx
      by_cases hq : SameEdge v w u x
      · rcases hq with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
        · exact absurd rfl huv
        · rw [marks_comm, h1] at h2; exact absurd h2 (by omega)
      · rw [hmk u x hq]; exact h2
  · intro u x hpos
    by_cases hq : SameEdge v w u x
    · rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl hvw'
      · exact Or.inr hvw'
    · rw [hmk u x hq] at hpos; exact hE.tree u x hpos

/-! ### Running the rule -/

section Run

variable [Fintype V] [DecidableRel G.Adj]

/-- Every step keeps the invariant. -/
theorem inv_step {s : V} {pick : Chooser G s} (hpick : pick.Valid) {E E' : Explorer G s}
    (hE : Inv E) (h : step pick E = some E') : Inv E' := by
  rcases step_eq_some hpick h with ⟨w, hvw, h0, hw, rfl⟩ | ⟨w, hvw, h0, hw, rfl⟩ |
    ⟨w, hvw, h1, hall, rfl⟩
  · exact inv_rule2 hE hvw h0 hw
  · exact inv_rule1 hE hvw h0 hw
  · exact inv_rule3 hE hvw h1 hall

/-- Every step crosses at least one path. -/
theorem length_lt_of_step {s : V} {pick : Chooser G s} (hpick : pick.Valid)
    {E E' : Explorer G s} (h : step pick E = some E') : E.walk.length < E'.walk.length := by
  rcases step_eq_some hpick h with ⟨w, hvw, -, -, rfl⟩ | ⟨w, hvw, -, -, rfl⟩ |
    ⟨w, hvw, -, -, rfl⟩ <;> dsimp only <;> simp only [SimpleGraph.Walk.length_concat] <;> omega

/-- Running keeps the invariant. -/
theorem inv_run {s : V} {pick : Chooser G s} (hpick : pick.Valid) :
    ∀ n (E : Explorer G s), Inv E → Inv (run pick n E)
  | 0, _, hE => hE
  | n + 1, E, hE => by
    unfold run
    cases h : step pick E with
    | none => exact hE
    | some E' => exact inv_run hpick n E' (inv_step hpick hE h)

/-- After `n` steps the explorer has stopped or crossed at least `n` more times. -/
theorem run_spec {s : V} {pick : Chooser G s} (hpick : pick.Valid) :
    ∀ n (E : Explorer G s),
      step pick (run pick n E) = none ∨ E.walk.length + n ≤ (run pick n E).walk.length
  | 0, _ => Or.inr le_rfl
  | n + 1, E => by
    cases h : step pick E with
    | none =>
      have hr : run pick (n + 1) E = E := by simp [run, h]
      rw [hr]; exact Or.inl h
    | some E' =>
      have hr : run pick (n + 1) E = run pick n E' := by simp [run, h]
      rw [hr]
      rcases run_spec hpick n E' with h' | h'
      · exact Or.inl h'
      · have := length_lt_of_step hpick h
        exact Or.inr (by omega)

omit [DecidableRel G.Adj] in
/-- A route that never repeats a crossing has at most `card V ^ 2` crossings. -/
theorem length_le_of_inv {s : V} {E : Explorer G s} (hE : Inv E) :
    E.walk.length ≤ Fintype.card V ^ 2 := by
  have h := hE.nodup.length_le_card
  rw [List.length_map, SimpleGraph.Walk.length_darts, Fintype.card_prod] at h
  rw [sq]; exact h

/-- The invariant holds for the explorer after the run. -/
theorem tremaux_inv {s : V} {pick : Chooser G s} (hpick : pick.Valid) :
    Inv (tremaux G s pick) := inv_run hpick _ _ (inv_start s)

/-- The explorer has stopped by the rule within `card V ^ 2` steps. -/
theorem step_tremaux {s : V} {pick : Chooser G s} (hpick : pick.Valid) :
    step pick (tremaux G s pick) = none := by
  rcases run_spec hpick (Fintype.card V ^ 2) (start G s) with h | h
  · exact h
  · cases h' : step pick (tremaux G s pick) with
    | none => rfl
    | some E' =>
      have h1 := length_lt_of_step hpick h'
      have h2 := length_le_of_inv (inv_step hpick (tremaux_inv hpick) h')
      have h0 : (start G s).walk.length = 0 := rfl
      rw [h0, zero_add] at h
      unfold tremaux at h1
      omega

/-- It stops at the start. -/
theorem pos_tremaux {s : V} {pick : Chooser G s} (hpick : pick.Valid) :
    (tremaux G s pick).pos = s := by
  have hE := tremaux_inv hpick
  have hstop := step_eq_none hpick (step_tremaux hpick)
  by_contra hne
  obtain ⟨u, hu, hm⟩ := hE.path _ Relation.ReflTransGen.refl hne
  have := hstop u (hE.par_adj _ u hu).1.symm
  rw [marks_comm] at this
  omega

/-- When it stops, every path at a crossroads on the route has two strokes. -/
theorem marks_tremaux {s : V} {pick : Chooser G s} (hpick : pick.Valid) {u : V}
    (hu : u ∈ (tremaux G s pick).walk.support) (x : V) (hx : G.Adj u x) :
    marks (tremaux G s pick).walk u x = 2 := by
  have hE := tremaux_inv hpick
  have hpos := pos_tremaux hpick
  by_cases hus : u = s
  · have hpu : (tremaux G s pick).pos = u := hpos.trans hus.symm
    have h1 := step_eq_none hpick (step_tremaux hpick) x (hpu ▸ hx)
    have e : marks (tremaux G s pick).walk (tremaux G s pick).pos x =
        marks (tremaux G s pick).walk u x :=
      congrArg (fun a ↦ marks (tremaux G s pick).walk a x) hpu
    have h2 := marks_le_two hE.nodup u x
    omega
  · refine hE.finished u hu (fun h ↦ hus ?_) x hx
    rw [hpos] at h
    rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hc, -⟩
    · exact h.symm
    · rw [hE.par_s] at hc; simp at hc

end Run

end Tremaux

open Tremaux

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

/-- **Trémaux's rule stops at the start (item 64).** For any valid chooser, the explorer stops
by the rule (no further step) and is back at the start `s`. -/
theorem tremaux_stops {s : V} {pick : Chooser G s} (hpick : pick.Valid) :
    step pick (tremaux G s pick) = none ∧ (tremaux G s pick).pos = s :=
  ⟨step_tremaux hpick, pos_tremaux hpick⟩

/-- **Trémaux's rule visits every vertex (item 64)** of a finite connected graph. -/
theorem tremaux_visits_all (hG : G.Connected) {s : V} {pick : Chooser G s} (hpick : pick.Valid)
    (v : V) : v ∈ (tremaux G s pick).walk.support := by
  have hclosed : ∀ a b (p : G.Walk a b), a ∈ (tremaux G s pick).walk.support →
      b ∈ (tremaux G s pick).walk.support := by
    intro a b p
    induction p with
    | nil => exact id
    | cons h _ ih =>
      intro ha
      refine ih ?_
      have := marks_tremaux hpick ha _ h
      exact (mem_support_of_marks_pos (lt_of_lt_of_eq two_pos this.symm)).2
  obtain ⟨p⟩ := hG.preconnected s v
  exact hclosed s v p (tremaux G s pick).walk.start_mem_support

/-- **Trémaux's rule crosses every edge exactly twice, once each way (item 64).** Every dart
(an edge with a direction) occurs exactly once in the route. -/
theorem tremaux_crosses_twice (hG : G.Connected) {s : V} {pick : Chooser G s}
    (hpick : pick.Valid) (d : G.Dart) : (tremaux G s pick).walk.darts.count d = 1 := by
  have hE := tremaux_inv hpick
  have hm := marks_tremaux hpick (tremaux_visits_all hG hpick d.fst) d.snd d.adj
  have h1 := cross_le_one hE.nodup d.fst d.snd
  have h2 := cross_le_one hE.nodup d.snd d.fst
  unfold marks at hm
  have h3 : cross (tremaux G s pick).walk d.fst d.snd = 1 := by omega
  unfold cross at h3
  rw [← List.count_map_of_injective _ _ SimpleGraph.Dart.toProd_injective]
  exact h3

/-- A Trémaux tree rooted at `s`, given by parents. -/
def IsTremauxTree (G : SimpleGraph V) (s : V) (parent : V → Option V) : Prop :=
  parent s = none ∧ (∀ v u, parent v = some u → G.Adj u v) ∧
  (∀ v, Relation.ReflTransGen (fun a b ↦ parent a = some b) v s) ∧
  ∀ u v, G.Adj u v → Relation.ReflTransGen (fun a b ↦ parent a = some b) u v ∨
    Relation.ReflTransGen (fun a b ↦ parent a = some b) v u

/-- **The explorer's tree is a Trémaux tree (item 64).** The first-entry parents (the paths of
rule 1; Lucas, p. 51, removes the paths of rule 2 and keeps a tree) form a Trémaux tree. -/
theorem isTremauxTree_of_tremaux (hG : G.Connected) {s : V} {pick : Chooser G s}
    (hpick : pick.Valid) : IsTremauxTree G s (tremaux G s pick).parent := by
  have hE := tremaux_inv hpick
  refine ⟨hE.par_s, fun v u h ↦ (hE.par_adj v u h).1, fun v ↦
    hE.anc_s v (tremaux_visits_all hG hpick v), fun u v huv ↦ hE.tree u v ?_⟩
  have := marks_tremaux hpick (tremaux_visits_all hG hpick u) v huv
  omega

end ClassicalLean.Combinatorics
