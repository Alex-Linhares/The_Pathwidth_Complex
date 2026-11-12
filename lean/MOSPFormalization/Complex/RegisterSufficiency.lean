/-
Copyright (c) 2026 Alexandre Linhares. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Register sufficiency (Garey & Johnson PO1) as a constrained vertex separation

Sethi, *Complete register allocation problems*, SIAM J. Comput. 4 (1975) 226–248; Garey &
Johnson (1979) p. 272, PO1 REGISTER SUFFICIENCY: a dag whose arcs run from operand to consumer,
a register is loaded when a vertex is computed, every vertex is computed exactly once, a
register may be freed at will, and the outputs (the vertices with no consumer) are kept. This
is the progressive black pebble game of `PebblingGu.lean` (`BlackMove`, `BlackPebblesWithin`,
`pb`) with a *retained set* `R` whose pebbles are never removed; `R = ∅` is Kirousis &
Papadimitriou's game, `R = outputs D` is Garey & Johnson's.

## Definitions

* `BlackMove.LegalR D R P m` — legality with retention: a pebble goes on a never-pebbled vertex
  all of whose immediate predecessors are pebbled; a pebble not on `R` may be removed.
* `BlackStepR`, `BlackPebblesWithinR D R K`, `pbR D R` — the game and its demand; the play
  ends when every vertex has been pebbled (a first draft ended at the all-`done` position,
  which no play with a retained vertex can reach; the prover of the formula found it).
* `outputs D`, `registerDemand D = pbR D (outputs D)` — Garey & Johnson's quantity.
* `IsTopological D σ` — a layout placing every operand before its consumer.
* `preBoundary D R σ i` — the vertices placed before step `i` that are retained or have a
  successor at step `i` or later: exactly the pebbles still on the board when `vᵢ` is placed,
  under the removal policy "drop a pebble as soon as all its successors are placed".
* `layoutDemand D R σ = max_i (|preBoundary D R σ i| + 1)` and
  `topologicalDemand D R = min` over topological layouts.

## The layout formula (proved in `RegisterSufficiencyFormula.lean`)

* `exists_isTopological_of_blackPebblesWithinR`: every play within `K` pebbles yields a
  topological layout (the order of placement) of demand `≤ K`, because a placed vertex with an
  unplaced successor still carries its pebble, and a retained one always does.
* `blackPebblesWithinR_of_isTopological`: placing in layout order and dropping each unretained
  pebble as soon as its last successor is placed is a play within `layoutDemand`.
* `pbR_eq_topologicalDemand`: **`pbR D R = topologicalDemand D R`** for every digraph and
  every retained set (both sides are `0` when no topological layout exists);
  `pb_eq_topologicalDemand` (`R = ∅`), `registerDemand_eq_topologicalDemand`.
* `blackPebblesWithinR_empty_iff`, `pbR_empty`: retention by `∅` is the plain game.

Brute force: `reports/scratch/ss7_register_sufficiency/pb_formula_check.py` (every labelled dag
on ≤ 6 vertices, both retention conventions, game search against the ideal-chain DP and a
brute force over topological orderings; 2,000 random dags on 9 vertices).
-/

import MOSPFormalization.Complex.PebblingGu

set_option linter.unusedSectionVars false

namespace MOSPFormalization

namespace Complex

open Finset PebblePhase

section Definitions

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Legality with a retained set `R` (G&J p. 272: the outputs are never freed). -/
def BlackMove.LegalR (D : Digraph α) (R : Finset α) (P : PebblePosition α) :
    BlackMove α → Prop
  | .place x => P x = fresh ∧ ∀ y, D.Adj y x → (P y).Pebbled
  | .remove x => P x = black ∧ x ∉ R

/-- One legal move with retained set `R`, after which at most `K` pebbles are on the graph. -/
def BlackStepR (D : Digraph α) (R : Finset α) (K : ℕ) (P Q : PebblePosition α) : Prop :=
  ∃ m : BlackMove α, m.LegalR D R P ∧ Q = m.apply P ∧ numPebbles Q ≤ K

/-- `D` can be pebbled once with at most `K` black pebbles, never freeing `R`: a play from
the empty board to a position in which every vertex has been pebbled (the retained ones
still carrying their pebble, so the end position is not `fun _ => done` unless `R = ∅`;
`blackPebblesWithinR_empty_iff` shows the two readings agree at `R = ∅`). -/
def BlackPebblesWithinR (D : Digraph α) (R : Finset α) (K : ℕ) : Prop :=
  ∃ Q : PebblePosition α,
    Relation.ReflTransGen (BlackStepR D R K) (fun _ => fresh) Q ∧ ∀ x, Q x ≠ fresh

/-- The demand with retained set `R`. -/
noncomputable def pbR (D : Digraph α) (R : Finset α) : ℕ := sInf {K | BlackPebblesWithinR D R K}

/-- Garey & Johnson's outputs: the vertices with no consumer (operand → consumer orientation). -/
def outputs (D : Digraph α) [DecidableRel D.Adj] : Finset α :=
  univ.filter fun v => ∀ u, ¬ D.Adj v u

/-- REGISTER SUFFICIENCY as Garey & Johnson state it: the outputs are kept. -/
noncomputable def registerDemand (D : Digraph α) [DecidableRel D.Adj] : ℕ :=
  pbR D (outputs D)

/-- A layout placing every operand before its consumer. -/
def IsTopological (D : Digraph α) (σ : LinearLayout α) : Prop :=
  ∀ u v, D.Adj u v → σ u < σ v

/-- The pre-placement boundary at step `i`: the vertices placed before `i` that are retained
or have a successor at `i` or later. -/
def preBoundary (D : Digraph α) [DecidableRel D.Adj] (R : Finset α) (σ : LinearLayout α)
    (i : ℕ) : Finset α :=
  univ.filter fun w => (σ w).val < i ∧ (w ∈ R ∨ ∃ u, D.Adj w u ∧ i ≤ (σ u).val)

/-- The demand of a layout: at each step the boundary plus the vertex being placed. -/
def layoutDemand (D : Digraph α) [DecidableRel D.Adj] (R : Finset α) (σ : LinearLayout α) : ℕ :=
  (univ : Finset (Fin (Fintype.card α))).sup fun i => (preBoundary D R σ i.val).card + 1

/-- The least demand over topological layouts (`0` if there is none). -/
noncomputable def topologicalDemand (D : Digraph α) [DecidableRel D.Adj] (R : Finset α) : ℕ :=
  sInf (Set.range fun σ : {σ : LinearLayout α // IsTopological D σ} => layoutDemand D R σ.1)

theorem mem_preBoundary_iff (D : Digraph α) [DecidableRel D.Adj] (R : Finset α)
    (σ : LinearLayout α) (i : ℕ) (w : α) :
    w ∈ preBoundary D R σ i ↔
      (σ w).val < i ∧ (w ∈ R ∨ ∃ u, D.Adj w u ∧ i ≤ (σ u).val) := by
  simp [preBoundary]

theorem card_preBoundary_add_one_le_layoutDemand (D : Digraph α) [DecidableRel D.Adj]
    (R : Finset α) (σ : LinearLayout α) (i : Fin (Fintype.card α)) :
    (preBoundary D R σ i.val).card + 1 ≤ layoutDemand D R σ :=
  Finset.le_sup (f := fun i : Fin (Fintype.card α) => (preBoundary D R σ i.val).card + 1)
    (mem_univ i)

theorem layoutDemand_le_iff (D : Digraph α) [DecidableRel D.Adj] (R : Finset α)
    (σ : LinearLayout α) (K : ℕ) :
    layoutDemand D R σ ≤ K ↔ ∀ i : Fin (Fintype.card α), (preBoundary D R σ i.val).card + 1 ≤ K := by
  unfold layoutDemand
  rw [Finset.sup_le_iff]
  simp

end Definitions

end Complex

end MOSPFormalization
