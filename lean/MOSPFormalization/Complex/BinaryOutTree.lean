/-
Copyright (c) 2026 Alexandre Linhares. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# The complete binary out-tree: definitions

`binaryOutTree h` is the complete binary tree of height `h` with every arc directed from a
vertex to its children (root → leaves), the family on which register sufficiency
(`RegisterSufficiency.lean`) exceeds `pw(G_u) + 1` by an unbounded amount: its one-shot black
pebble demand is `h + 1` (every topological layout has a step with `h` earlier vertices still
waiting for a successor, `BinaryOutTreeDemand.lean`), while its Lengauer graph `G_u` is the
tree itself (in-degrees are at most one, so no common-successor edge), of pathwidth
`⌈h/2⌉` (`BinaryOutTreeWidth.lean` proves `≤`).

Vertices follow `TreeBound.lean`'s `TVert`: a root, or a child index and a vertex of the tree
one level down. `binaryTree h` is the underlying undirected graph.
-/

import MOSPFormalization.Complex.RegisterSufficiency
import MOSPFormalization.TreeBound

set_option linter.unusedSectionVars false

namespace MOSPFormalization

namespace Complex

/-- The vertices of the complete binary tree of height `h`. -/
def BVert : ℕ → Type
  | 0 => Unit
  | h + 1 => Option (Fin 2 × BVert h)

instance instFintypeBVert : (h : ℕ) → Fintype (BVert h)
  | 0 => inferInstanceAs (Fintype Unit)
  | h + 1 => letI := instFintypeBVert h; inferInstanceAs (Fintype (Option (Fin 2 × BVert h)))

instance instDecidableEqBVert : (h : ℕ) → DecidableEq (BVert h)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | h + 1 => letI := instDecidableEqBVert h; inferInstanceAs (DecidableEq (Option (Fin 2 × BVert h)))

/-- The root. -/
def broot : (h : ℕ) → BVert h
  | 0 => ()
  | _ + 1 => none

/-- The arc relation of the complete binary out-tree of height `h`: the root points to the
roots of the two subtrees, and inside a subtree the arcs are those of the tree one level
down. -/
def binaryOutAdj : (h : ℕ) → BVert h → BVert h → Prop
  | 0, _, _ => False
  | h + 1, a, b =>
    match a, b with
    | none, some (_, y) => y = broot h
    | some (i, x), some (j, y) => i = j ∧ binaryOutAdj h x y
    | _, _ => False

instance instDecidableBinaryOutAdj : (h : ℕ) → DecidableRel (binaryOutAdj h)
  | 0, _, _ => inferInstanceAs (Decidable False)
  | h + 1, a, b =>
    letI := instDecidableEqBVert h
    letI := instDecidableBinaryOutAdj h
    match a, b with
    | none, some (_, y) => inferInstanceAs (Decidable (y = broot h))
    | some (i, x), some (j, y) => inferInstanceAs (Decidable (i = j ∧ binaryOutAdj h x y))
    | none, none => inferInstanceAs (Decidable False)
    | some _, none => inferInstanceAs (Decidable False)

/-- The complete binary out-tree of height `h` (root → leaves). -/
def binaryOutTree (h : ℕ) : Digraph (BVert h) where
  Adj := binaryOutAdj h

instance (h : ℕ) : DecidableRel (binaryOutTree h).Adj := instDecidableBinaryOutAdj h

/-- The underlying undirected tree. -/
def binaryTree (h : ℕ) : SimpleGraph (BVert h) where
  Adj a b := a ≠ b ∧ (binaryOutAdj h a b ∨ binaryOutAdj h b a)
  symm := by
    constructor
    intro a b ⟨hne, h⟩
    exact ⟨hne.symm, h.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (h : ℕ) : DecidableRel (binaryTree h).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem binaryOutTree_adj {h : ℕ} {a b : BVert h} :
    (binaryOutTree h).Adj a b ↔ binaryOutAdj h a b := Iff.rfl

theorem binaryOutAdj_zero (a b : BVert 0) : ¬ binaryOutAdj 0 a b := fun h => h

theorem binaryOutAdj_succ_none_some {h : ℕ} {i : Fin 2} {y : BVert h} :
    binaryOutAdj (h + 1) none (some (i, y)) ↔ y = broot h := Iff.rfl

theorem binaryOutAdj_succ_some_some {h : ℕ} {i j : Fin 2} {x y : BVert h} :
    binaryOutAdj (h + 1) (some (i, x)) (some (j, y)) ↔ i = j ∧ binaryOutAdj h x y := Iff.rfl

theorem not_binaryOutAdj_succ_some_none {h : ℕ} {a : Fin 2 × BVert h} :
    ¬ binaryOutAdj (h + 1) (some a) none := fun h => h

theorem not_binaryOutAdj_succ_none_none {h : ℕ} :
    ¬ binaryOutAdj (h + 1) (none : BVert (h + 1)) none := fun h => h

end Complex

end MOSPFormalization
