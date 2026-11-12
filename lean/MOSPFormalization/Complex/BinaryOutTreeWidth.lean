/-
Copyright (c) 2026 Alexandre Linhares. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# The complete binary out-tree: its Lengauer graph and its pathwidth

The undirected side of the register-sufficiency gap (`RegisterSufficiency.lean`,
`BinaryOutTree.lean`): the complete binary out-tree `binaryOutTree h` has Lengauer graph `G_u`
equal to the underlying tree `binaryTree h`, and that tree has pathwidth at most `⌈h/2⌉`, so
`pbw(binaryOutTree h) ≤ ⌈h/2⌉ + 1` while its one-shot black pebble demand is `h + 1`.

Brute force (`reports/scratch/ss7_register_sufficiency/binary_tree_gap.py`, 2026-11-12): the
pathwidth of the complete binary tree of height `h` is `0, 1, 1, 2, 2, 3` at `h = 0, …, 5`
(subset DP to 15 vertices, the C program `pathwidth_solver/cli/pathwidth` with a refutation at
31 and 63 vertices), i.e. `⌈h/2⌉ = (h + 1) / 2`; this file proves the `≤` half for every `h`.

## What is proved

* `card_BVert` — `|BVert h| + 1 = 2^(h+1)`.
* `binaryOutAdj_pred_unique` — in-degrees are at most one: two predecessors of a vertex are
  equal (nothing points to the root, `not_binaryOutAdj_broot`); hence
  `lengauerU_binaryOutTree : lengauerU (binaryOutTree h) = binaryTree h` — the common-successor
  clause of Lengauer's `G_u` adds no edge.
* `binaryTree_connected`, `binaryTree_isAcyclic`, `binaryTree_isTree` — connectivity from the
  root through the copy homomorphisms `copyHom`; acyclicity by the injective homomorphism
  `intoTriple` into `TreeBound.lean`'s `triple (binaryTree h) (broot h)`, which is acyclic by
  `triple_isAcyclic` (`SimpleGraph.IsAcyclic.comap`).
* `pathwidth_binaryTree_le : pathwidth (binaryTree h) ≤ (h + 1) / 2` — **the exact `⌈h/2⌉`**,
  by induction in steps of two. The step is `TreeBound.lean`'s path lemma
  (`tree_pathwidth_le_pathwidth_compl_path_add_one`) on the path `rootPath h` through the root
  and its two children of `binaryTree (h + 1)`: the complement of that path is the disjoint
  union, with no edge between, of the two rootless copies of `binaryTree h`
  (`pathwidth_binaryTree_succ_le`), and a rootless `binaryTree (h + 1)` is the disjoint union
  of two copies of `binaryTree h` (`pathwidth_induce_erase_root_le`), each copy isomorphic to
  the original through `copyIsoOn` (`pathwidth_copy_induce`); the union lemma is
  `pathwidth_induce_union_le_max`.
* `pbw_binaryOutTree_le : pbw (binaryOutTree h) ≤ (h + 1) / 2 + 1` — by
  `pbw_eq_pathwidth_lengauerU_add_one` (`PebblingGu.lean`).

Everything is `sorry`-free, with axioms `propext`, `Classical.choice`, `Quot.sound`
(`reports/scratch/ss7_register_sufficiency/binary_out_tree_width_axioms.log`). The lower
bound `⌈h/2⌉ ≤ pathwidth (binaryTree h)` is not attempted here.
-/

import MOSPFormalization.Complex.BinaryOutTree
import MOSPFormalization.Complex.PebblingGu

set_option linter.unusedSectionVars false

namespace MOSPFormalization

namespace Complex

open Finset

/-! ### Counting -/

/-- The tree of height `h` has `2^(h+1) − 1` vertices. -/
theorem card_BVert : ∀ h, Fintype.card (BVert h) + 1 = 2 ^ (h + 1)
  | 0 => by
    have : Fintype.card (BVert 0) = 1 := Fintype.card_unit
    rw [this]
    norm_num
  | h + 1 => by
    have ih := card_BVert h
    have : Fintype.card (BVert (h + 1)) = 2 * Fintype.card (BVert h) + 1 := by
      show Fintype.card (Option (Fin 2 × BVert h)) = _
      rw [Fintype.card_option, Fintype.card_prod, Fintype.card_fin]
    rw [this, pow_succ, ← ih]
    ring

/-! ### In-degrees are at most one -/

/-- Nothing points to the root. -/
theorem not_binaryOutAdj_broot : ∀ h (u : BVert h), ¬ binaryOutAdj h u (broot h)
  | 0, u => binaryOutAdj_zero u _
  | h + 1, u => by
    show ¬ binaryOutAdj (h + 1) u none
    rcases u with _ | a
    · exact not_binaryOutAdj_succ_none_none
    · exact not_binaryOutAdj_succ_some_none

/-- Two predecessors of one vertex coincide: in-degrees are at most one. -/
theorem binaryOutAdj_pred_unique :
    ∀ h {u w x : BVert h}, binaryOutAdj h u x → binaryOutAdj h w x → u = w
  | 0, u, _, x, hu, _ => absurd hu (binaryOutAdj_zero u x)
  | h + 1, u, w, x, hu, hw => by
    rcases x with _ | ⟨k, z⟩
    · exact absurd hu (not_binaryOutAdj_broot (h + 1) u)
    · rcases u with _ | ⟨i, a⟩ <;> rcases w with _ | ⟨j, b⟩
      · rfl
      · have hz : z = broot h := binaryOutAdj_succ_none_some.mp hu
        obtain ⟨-, hb⟩ := binaryOutAdj_succ_some_some.mp hw
        rw [hz] at hb
        exact absurd hb (not_binaryOutAdj_broot h b)
      · have hz : z = broot h := binaryOutAdj_succ_none_some.mp hw
        obtain ⟨-, ha⟩ := binaryOutAdj_succ_some_some.mp hu
        rw [hz] at ha
        exact absurd ha (not_binaryOutAdj_broot h a)
      · obtain ⟨hik, ha⟩ := binaryOutAdj_succ_some_some.mp hu
        obtain ⟨hjk, hb⟩ := binaryOutAdj_succ_some_some.mp hw
        have hab := binaryOutAdj_pred_unique h ha hb
        rw [hik, hjk, hab]

/-- **Lengauer's `G_u` of the binary out-tree is the tree itself**: no two distinct vertices
share a successor, so the common-successor clause adds nothing. -/
theorem lengauerU_binaryOutTree (h : ℕ) : lengauerU (binaryOutTree h) = binaryTree h := by
  ext u w
  show u ≠ w ∧ (binaryOutAdj h u w ∨ binaryOutAdj h w u ∨
      ∃ x, binaryOutAdj h u x ∧ binaryOutAdj h w x) ↔
    u ≠ w ∧ (binaryOutAdj h u w ∨ binaryOutAdj h w u)
  constructor
  · rintro ⟨hne, h1 | h1 | ⟨x, h1, h2⟩⟩
    · exact ⟨hne, Or.inl h1⟩
    · exact ⟨hne, Or.inr h1⟩
    · exact absurd (binaryOutAdj_pred_unique h h1 h2) hne
  · rintro ⟨hne, h1 | h1⟩
    · exact ⟨hne, Or.inl h1⟩
    · exact ⟨hne, Or.inr (Or.inl h1)⟩

/-! ### The two copies of the tree one level down -/

/-- The vertex `x` of the tree one level down, placed in subtree `i`. -/
def copyMap (h : ℕ) (i : Fin 2) (x : BVert h) : BVert (h + 1) := some (i, x)

theorem copyMap_injective (h : ℕ) (i : Fin 2) : Function.Injective (copyMap h i) := by
  intro x y hxy
  exact (Prod.mk.inj (Option.some.inj hxy)).2

theorem none_ne_some' {h : ℕ} (a : Fin 2 × BVert h) : (none : BVert (h + 1)) ≠ some a :=
  fun e => Option.some_ne_none a e.symm

theorem some_ne_none' {h : ℕ} (a : Fin 2 × BVert h) : (some a : BVert (h + 1)) ≠ none :=
  fun e => Option.some_ne_none a e

/-- Adjacency inside a copy is adjacency one level down. -/
theorem binaryTree_adj_copy {h : ℕ} {i : Fin 2} {x y : BVert h} :
    (binaryTree (h + 1)).Adj (some (i, x)) (some (i, y)) ↔ (binaryTree h).Adj x y := by
  show some (i, x) ≠ some (i, y) ∧
      (binaryOutAdj (h + 1) (some (i, x)) (some (i, y)) ∨
        binaryOutAdj (h + 1) (some (i, y)) (some (i, x))) ↔
    x ≠ y ∧ (binaryOutAdj h x y ∨ binaryOutAdj h y x)
  constructor
  · rintro ⟨hne, ⟨-, h1⟩ | ⟨-, h1⟩⟩
    · exact ⟨fun e => hne (by rw [e]), Or.inl h1⟩
    · exact ⟨fun e => hne (by rw [e]), Or.inr h1⟩
  · rintro ⟨hne, h1 | h1⟩
    · exact ⟨fun e => hne (Prod.mk.inj (Option.some.inj e)).2, Or.inl ⟨rfl, h1⟩⟩
    · exact ⟨fun e => hne (Prod.mk.inj (Option.some.inj e)).2, Or.inr ⟨rfl, h1⟩⟩

/-- No edge joins two different copies. -/
theorem not_binaryTree_adj_copy {h : ℕ} {i j : Fin 2} (hij : i ≠ j) (x y : BVert h) :
    ¬ (binaryTree (h + 1)).Adj (some (i, x)) (some (j, y)) := by
  rintro ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩⟩
  · exact hij h1
  · exact hij h1.symm

theorem image_copyMap_disjoint {h : ℕ} {i j : Fin 2} (hij : i ≠ j)
    (S T : Finset (BVert h)) : Disjoint (S.image (copyMap h i)) (T.image (copyMap h j)) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  obtain ⟨x, -, rfl⟩ := mem_image.mp ha
  obtain ⟨y, -, hy⟩ := mem_image.mp hb
  exact hij (Prod.mk.inj (Option.some.inj hy)).1.symm

theorem image_copyMap_not_adj {h : ℕ} {i j : Fin 2} (hij : i ≠ j) (S T : Finset (BVert h)) :
    ∀ a ∈ S.image (copyMap h i), ∀ b ∈ T.image (copyMap h j), ¬ (binaryTree (h + 1)).Adj a b := by
  intro a ha b hb
  obtain ⟨x, -, rfl⟩ := mem_image.mp ha
  obtain ⟨y, -, rfl⟩ := mem_image.mp hb
  exact not_binaryTree_adj_copy hij x y

/-- The `i`-th copy, as a homomorphism. -/
def copyHom (h : ℕ) (i : Fin 2) : binaryTree h →g binaryTree (h + 1) where
  toFun := copyMap h i
  map_rel' hxy := binaryTree_adj_copy.mpr hxy

/-- The copy of the induced subgraph on `S` is isomorphic to it. -/
noncomputable def copyIsoOn (h : ℕ) (i : Fin 2) (S : Finset (BVert h)) :
    (binaryTree h).induce (↑S : Set (BVert h)) ≃g
      (binaryTree (h + 1)).induce (↑(S.image (copyMap h i)) : Set (BVert (h + 1))) where
  toEquiv := Equiv.ofBijective
    (fun x : ↥(↑S : Set (BVert h)) =>
      (⟨copyMap h i x.1, Finset.mem_coe.mpr (mem_image_of_mem _ (Finset.mem_coe.mp x.2))⟩ :
        ↥(↑(S.image (copyMap h i)) : Set (BVert (h + 1)))))
    (by
      constructor
      · intro x y hxy
        exact Subtype.ext (copyMap_injective h i (congrArg Subtype.val hxy))
      · rintro ⟨a, ha⟩
        obtain ⟨x, hx, rfl⟩ := mem_image.mp (Finset.mem_coe.mp ha)
        exact ⟨⟨x, Finset.mem_coe.mpr hx⟩, rfl⟩)
  map_rel_iff' := by
    intro x y
    show (binaryTree (h + 1)).Adj (some (i, x.1)) (some (i, y.1)) ↔ (binaryTree h).Adj x.1 y.1
    exact binaryTree_adj_copy

theorem pathwidth_copy_induce (h : ℕ) (i : Fin 2) (S : Finset (BVert h)) :
    pathwidth ((binaryTree (h + 1)).induce (↑(S.image (copyMap h i)) : Set (BVert (h + 1)))) =
      pathwidth ((binaryTree h).induce (↑S : Set (BVert h))) :=
  (pathwidth_eq_of_iso (copyIsoOn h i S)).symm

/-! ### The tree is a tree -/

theorem binaryTree_adj_root {h : ℕ} (i : Fin 2) :
    (binaryTree (h + 1)).Adj none (some (i, broot h)) :=
  ⟨none_ne_some' _, Or.inl rfl⟩

theorem binaryTree_connected : ∀ h, (binaryTree h).Connected
  | 0 => by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    exact ⟨broot 0, fun v => by
      have : v = broot 0 := Subsingleton.elim (α := Unit) v (broot 0)
      rw [this]⟩
  | h + 1 => by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨none, ?_⟩
    rintro (_ | ⟨i, x⟩)
    · exact SimpleGraph.Reachable.refl _
    · have h1 : (binaryTree (h + 1)).Reachable none (some (i, broot h)) :=
        SimpleGraph.Adj.reachable (binaryTree_adj_root i)
      have h2 : (binaryTree (h + 1)).Reachable (some (i, broot h)) (some (i, x)) :=
        SimpleGraph.Reachable.map (copyHom h i)
          ((binaryTree_connected h).preconnected (broot h) x)
      exact h1.trans h2

/-- The underlying map of the injective homomorphism into `triple (binaryTree h) (broot h)`. -/
def intoTripleMap (h : ℕ) : BVert (h + 1) → Option (Fin 3 × BVert h)
  | none => none
  | some (i, x) => some (Fin.castSucc i, x)

theorem intoTripleMap_injective (h : ℕ) : Function.Injective (intoTripleMap h) := by
  rintro (_ | ⟨i, x⟩) (_ | ⟨j, y⟩) hab
  · rfl
  · exact absurd hab (Option.some_ne_none _).symm
  · exact absurd hab (Option.some_ne_none _)
  · have h1 := Prod.mk.inj (Option.some.inj hab)
    rw [Fin.castSucc_inj] at h1
    rw [h1.1, h1.2]

/-- `binaryTree (h + 1)` embeds in `triple (binaryTree h) (broot h)` (two of its three copies). -/
def intoTriple (h : ℕ) : binaryTree (h + 1) →g triple (binaryTree h) (broot h) where
  toFun := intoTripleMap h
  map_rel' := by
    rintro (_ | ⟨i, x⟩) (_ | ⟨j, y⟩) hab
    · exact absurd rfl hab.1
    · rcases hab with ⟨-, h1 | h1⟩
      · exact h1
      · exact absurd h1 not_binaryOutAdj_succ_some_none
    · rcases hab with ⟨-, h1 | h1⟩
      · exact absurd h1 not_binaryOutAdj_succ_some_none
      · exact h1
    · rcases hab with ⟨hne, ⟨hij, h1⟩ | ⟨hij, h1⟩⟩
      · subst hij
        exact ⟨rfl, fun e => hne (by rw [e]), Or.inl h1⟩
      · subst hij
        exact ⟨rfl, fun e => hne (by rw [e]), Or.inr h1⟩

theorem binaryTree_isAcyclic : ∀ h, (binaryTree h).IsAcyclic
  | 0 => by
    have : Subsingleton (BVert 0) := inferInstanceAs (Subsingleton Unit)
    exact SimpleGraph.IsAcyclic.of_subsingleton
  | h + 1 => SimpleGraph.IsAcyclic.comap (intoTriple h) (intoTripleMap_injective h)
      (triple_isAcyclic (binaryTree h) (broot h) (binaryTree_isAcyclic h))

theorem binaryTree_isTree (h : ℕ) : (binaryTree h).IsTree :=
  ⟨binaryTree_connected h, binaryTree_isAcyclic h⟩

/-! ### The pathwidth bound -/

/-- The path through the root of `binaryTree (h + 1)`: left child, root, right child. -/
def rootPath (h : ℕ) : Fin 3 → BVert (h + 1)
  | ⟨0, _⟩ => some (0, broot h)
  | ⟨1, _⟩ => none
  | ⟨2, _⟩ => some (1, broot h)

theorem rootPath_zero (h : ℕ) : rootPath h 0 = some (0, broot h) := rfl
theorem rootPath_one (h : ℕ) : rootPath h 1 = none := rfl
theorem rootPath_two (h : ℕ) : rootPath h 2 = some (1, broot h) := rfl

/-- A left inverse of `rootPath`. -/
def rootPathInv (h : ℕ) : BVert (h + 1) → Fin 3
  | none => 1
  | some (i, _) => if i = 0 then 0 else 2

theorem rootPathInv_rootPath (h : ℕ) : ∀ i, rootPathInv h (rootPath h i) = i := by
  intro i
  fin_cases i <;> rfl

theorem rootPath_injective (h : ℕ) : Function.Injective (rootPath h) := by
  intro i j hij
  have := congrArg (rootPathInv h) hij
  rwa [rootPathInv_rootPath, rootPathInv_rootPath] at this

/-- Every value of `rootPath` of the form `some (i, y)` has `y` the root one level down. -/
theorem eq_broot_of_rootPath_eq_some {h : ℕ} {j : Fin 3} {i : Fin 2} {y : BVert h}
    (hj : rootPath h j = some (i, y)) : y = broot h := by
  fin_cases j
  · exact (Prod.mk.inj (Option.some.inj hj)).2.symm
  · exact absurd hj (none_ne_some' _)
  · exact (Prod.mk.inj (Option.some.inj hj)).2.symm

theorem rootPath_isPathSeq (h : ℕ) : IsPathSeq (binaryTree (h + 1)) (rootPath h) := by
  refine ⟨rootPath_injective h, ?_⟩
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
  simp only at hij
  subst hij
  interval_cases i
  · exact (binaryTree_adj_root 0).symm
  · exact binaryTree_adj_root 1
  · omega

/-- The complement of the root path is the two rootless copies. -/
theorem compl_image_rootPath (h : ℕ) :
    (Finset.univ.image (rootPath h))ᶜ =
      (Finset.univ.erase (broot h)).image (copyMap h 0) ∪
        (Finset.univ.erase (broot h)).image (copyMap h 1) := by
  ext a
  rw [mem_compl, mem_union, mem_image, mem_image, mem_image]
  rcases a with _ | ⟨i, x⟩
  · constructor
    · intro hc
      exact absurd ⟨1, mem_univ _, rfl⟩ hc
    · rintro (⟨y, -, hy⟩ | ⟨y, -, hy⟩) <;> exact absurd hy (some_ne_none' _)
  · constructor
    · intro hc
      have hx : x ≠ broot h := by
        rintro rfl
        apply hc
        fin_cases i
        · exact ⟨0, mem_univ _, rfl⟩
        · exact ⟨2, mem_univ _, rfl⟩
      fin_cases i
      · exact Or.inl ⟨x, mem_erase.mpr ⟨hx, mem_univ _⟩, rfl⟩
      · exact Or.inr ⟨x, mem_erase.mpr ⟨hx, mem_univ _⟩, rfl⟩
    · rintro (⟨y, hy, hya⟩ | ⟨y, hy, hya⟩) ⟨j, -, hj⟩ <;>
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hya) <;>
        exact (mem_erase.mp hy).1 (eq_broot_of_rootPath_eq_some hj)

/-- The rootless `binaryTree (h + 1)` has no larger pathwidth than `binaryTree h`: it is the
disjoint union of two copies with no edge between them. -/
theorem pathwidth_induce_erase_root_le (h : ℕ) :
    pathwidth ((binaryTree (h + 1)).induce
        (↑(Finset.univ.erase (broot (h + 1))) : Set (BVert (h + 1)))) ≤
      pathwidth (binaryTree h) := by
  have hU : (Finset.univ.erase (broot (h + 1)) : Finset (BVert (h + 1))) =
      Finset.univ.image (copyMap h 0) ∪ Finset.univ.image (copyMap h 1) := by
    ext a
    rw [mem_union, mem_image, mem_image, mem_erase]
    rcases a with _ | ⟨i, x⟩
    · constructor
      · intro hc
        exact absurd rfl hc.1
      · rintro (⟨y, -, hy⟩ | ⟨y, -, hy⟩) <;> exact absurd hy (some_ne_none' _)
    · constructor
      · intro _
        fin_cases i
        · exact Or.inl ⟨x, mem_univ _, rfl⟩
        · exact Or.inr ⟨x, mem_univ _, rfl⟩
      · intro _
        exact ⟨some_ne_none' _, mem_univ _⟩
  rw [hU]
  refine (pathwidth_induce_union_le_max _ _ _ (image_copyMap_disjoint (by decide) _ _)
    (image_copyMap_not_adj (by decide) _ _)).trans ?_
  rw [pathwidth_copy_induce, pathwidth_copy_induce, max_self]
  exact pathwidth_le_of_injective (SimpleGraph.Embedding.induce _).toHom Subtype.val_injective

/-- **The step**: `pathwidth (binaryTree (h + 1)) ≤ pathwidth (rootless binaryTree h) + 1`,
by the path lemma on the root path, whose complement is two rootless copies. -/
theorem pathwidth_binaryTree_succ_le (h : ℕ) :
    pathwidth (binaryTree (h + 1)) ≤
      pathwidth ((binaryTree h).induce (↑(Finset.univ.erase (broot h)) : Set (BVert h))) + 1 := by
  have hP := tree_pathwidth_le_pathwidth_compl_path_add_one (binaryTree (h + 1))
    (binaryTree_isTree (h + 1)) (rootPath h) (rootPath_isPathSeq h)
  rw [compl_image_rootPath] at hP
  refine hP.trans (Nat.add_le_add_right ?_ 1)
  refine (pathwidth_induce_union_le_max _ _ _ (image_copyMap_disjoint (by decide) _ _)
    (image_copyMap_not_adj (by decide) _ _)).trans ?_
  rw [pathwidth_copy_induce, pathwidth_copy_induce, max_self]

/-- The rootless tree of height `0` is empty. -/
theorem pathwidth_induce_erase_root_zero :
    pathwidth ((binaryTree 0).induce (↑(Finset.univ.erase (broot 0)) : Set (BVert 0))) = 0 := by
  apply le_antisymm _ (Nat.zero_le _)
  have h1 := pathwidth_le_card_sub_one
    ((binaryTree 0).induce (↑(Finset.univ.erase (broot 0)) : Set (BVert 0)))
  have h0 : Fintype.card ↥(↑(Finset.univ.erase (broot 0)) : Set (BVert 0)) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun x => ?_⟩
    have hx := Finset.mem_erase.mp (Finset.mem_coe.mp x.2)
    exact hx.1 (Subsingleton.elim (α := Unit) x.1 (broot 0))
  rw [h0] at h1
  exact h1

/-- **The complete binary tree of height `h` has pathwidth at most `⌈h/2⌉ = (h + 1) / 2`.** -/
theorem pathwidth_binaryTree_le : ∀ h, pathwidth (binaryTree h) ≤ (h + 1) / 2
  | 0 => by
    have h1 := pathwidth_le_card_sub_one (binaryTree 0)
    have h2 := card_BVert 0
    omega
  | 1 => by
    have h1 := pathwidth_binaryTree_succ_le 0
    rw [pathwidth_induce_erase_root_zero] at h1
    exact h1
  | h + 2 => by
    show pathwidth (binaryTree (h + 1 + 1)) ≤ (h + 1 + 1 + 1) / 2
    have h1 := pathwidth_binaryTree_succ_le (h + 1)
    have h2 := pathwidth_induce_erase_root_le h
    have h3 := pathwidth_binaryTree_le h
    omega

/-- **Corollary**: the pebbles-within demand of the binary out-tree is at most `⌈h/2⌉ + 1`,
against its one-shot black demand of `h + 1`. -/
theorem pbw_binaryOutTree_le (h : ℕ) : pbw (binaryOutTree h) ≤ (h + 1) / 2 + 1 := by
  have : Nonempty (BVert h) := ⟨broot h⟩
  rw [pbw_eq_pathwidth_lengauerU_add_one, lengauerU_binaryOutTree]
  exact Nat.add_le_add_right (pathwidth_binaryTree_le h) 1

end Complex

end MOSPFormalization
