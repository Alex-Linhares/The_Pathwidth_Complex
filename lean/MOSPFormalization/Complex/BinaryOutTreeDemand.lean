/-
Copyright (c) 2026 Alexandre Linhares. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# The complete binary out-tree needs exactly `h + 1` pebbles

`binaryOutTree h` (`BinaryOutTree.lean`) is the complete binary tree of height `h` with every
arc directed from a vertex to its children. In the one-shot black pebble game with no retained
set (`RegisterSufficiency.lean`, `R = ∅`), its demand is `h + 1`. This file proves both
halves through the layout formula (`layoutDemand`, `topologicalDemand`):

* `exists_preBoundary_binaryOutTree`: **every topological layout `σ` of `binaryOutTree h` has a
  step `i` whose pre-placement boundary `preBoundary (binaryOutTree h) ∅ σ i` has at least `h`
  vertices** — `h` vertices placed before `i` still waiting for a successor;
* `layoutDemand_binaryOutTree_ge`: hence `h + 1 ≤ layoutDemand (binaryOutTree h) ∅ σ`;
* `exists_isTopological_layoutDemand_le`: the depth-first layout (root, subtree `0`, subtree
  `1`) has demand `≤ h + 1`;
* `topologicalDemand_binaryOutTree`: **`topologicalDemand (binaryOutTree h) ∅ = h + 1`**.

The lower bound is the one behind "register sufficiency exceeds `pw(G_u) + 1` without bound":
the Lengauer graph of the out-tree is the tree itself, of pathwidth `⌈h/2⌉`, while the demand
is `h + 1`.

## Proof idea

Everything is proved for an arbitrary *key* `f : BVert h → ℕ` that is *topological* (every arc
goes up in the key, `KeyTopological`), with the cut `keyCut h f t` = the vertices of key `< t`
having a successor of key `≥ t`; a layout is the key `x ↦ (σ x).val`, and restricting a key to
a subtree is composition with `x ↦ some (j, x)` (`subKey`), so no re-indexing of positions is
needed. The thresholds are always the key of a vertex. (`bnone`, `bsome` are the two
constructors of `BVert (h + 1)` typed as such: a bare `none` or `some (j, x)` elaborates at the
unfolded type `Option (Fin 2 × BVert h)`, which the rewriting tactics do not identify with
`BVert (h + 1)`.)

Lower bound:

* `root_lt_of_keyTopological`: the root has the least key (every vertex is reachable from it).
* `exists_adj_across` (the cut lemma): if some vertex has key `< t` and some vertex key `≥ t`,
  an arc crosses the threshold forwards — induction on `h`: the root is below `t`; take `y`
  above `t` in subtree `j`; if subtree `j`'s root is above `t` the root's arc to it crosses,
  otherwise the induction hypothesis on subtree `j` gives a crossing arc there.
* `card_keyCut_succ_ge` (the induction step): let subtree `j` be the one that *finishes* no
  later than the other, `k`. The induction hypothesis gives a vertex `v'` of subtree `j` with
  `h` vertices of subtree `j` in the cut at its key; at the same threshold in the big tree those
  `h` vertices are still in the cut (arcs inside subtree `j` are arcs of the big tree), and one
  more vertex outside subtree `j` joins them: the root (below the threshold) and the last
  vertex of subtree `k` (at or above it, since `k` finishes last) straddle the threshold, so
  the cut lemma on `{root} ∪ subtree k` — the root's arc to subtree `k`'s root, or
  `exists_adj_across` inside subtree `k` — gives a crossing arc whose tail is in the cut.
* `exists_keyCut_card_ge`: the statement for keys, by induction on `h`; the main theorem
  instantiates it with the layout's positions.

Upper bound:

* `dfsKey`: root `0`, subtree `0` shifted by `1`, subtree `1` shifted by `1 + B₀` (`B₀` a bound
  on subtree `0`'s keys); `keyCut_dfsKey_subset`: its cut at a vertex of subtree `i` is
  contained in the root together with subtree `i`'s own cut, because the two subtrees occupy
  disjoint key intervals; `exists_key_keyCut_card_le`: by induction an injective, topological,
  bounded key with every cut `≤ h`; `exists_layout_of_injective_key` (via `exists_layout_sorted`)
  and `preBoundary_eq_keyCut_of_key` turn it into a layout whose boundaries are its cuts.

Brute force: `reports/scratch/ss7_register_sufficiency/binary_tree_gap.py` (log beside it):
the one-shot black pebble demand of the binary out-tree is `h + 1` at `h = 0, …, 4` by an exact
dynamic programme over the ideals of the tree, and the out-tree recursion
`g(T) = max(g₁, g₂ + 1)`, `pb = g + 1` — the induction of this file — agrees with the exact
value on 4,200 random out-trees on 1 to 14 vertices.
-/

import MOSPFormalization.Complex.BinaryOutTree

set_option linter.unusedSectionVars false

namespace MOSPFormalization

namespace Complex

open Finset

/-! ### Keys, cuts and subtrees -/

/-- A key is topological for the out-tree of height `h` if every arc goes up in the key. -/
def KeyTopological (h : ℕ) (f : BVert h → ℕ) : Prop :=
  ∀ a b, binaryOutAdj h a b → f a < f b

/-- The vertices of key below `t` that have a successor of key at least `t`: the
pre-placement boundary of a layout, stated for an arbitrary key. -/
def keyCut (h : ℕ) (f : BVert h → ℕ) (t : ℕ) : Finset (BVert h) :=
  univ.filter fun w => f w < t ∧ ∃ u, binaryOutAdj h w u ∧ t ≤ f u

theorem mem_keyCut_iff {h : ℕ} {f : BVert h → ℕ} {t : ℕ} {w : BVert h} :
    w ∈ keyCut h f t ↔ f w < t ∧ ∃ u, binaryOutAdj h w u ∧ t ≤ f u := by
  simp [keyCut]

/-- The root of the tree of height `h + 1`, typed as such (`BVert (h + 1)` unfolds to
`Option (Fin 2 × BVert h)`, and a bare `none` elaborates at the unfolded type, which the
rewriting tactics do not identify with `BVert (h + 1)`). -/
def bnone (h : ℕ) : BVert (h + 1) := none

/-- The vertex `x` of subtree `j`, typed as a vertex of the tree of height `h + 1`. -/
def bsome {h : ℕ} (j : Fin 2) (x : BVert h) : BVert (h + 1) := some (j, x)

theorem bnone_ne_bsome {h : ℕ} (j : Fin 2) (x : BVert h) : bnone h ≠ bsome j x :=
  fun hx => (Option.some_ne_none (j, x)) (show some (j, x) = none from hx.symm)

theorem bsome_inj {h : ℕ} {i j : Fin 2} {x y : BVert h} (hxy : bsome i x = bsome j y) :
    i = j ∧ x = y :=
  Prod.mk.inj (Option.some.inj hxy)

theorem binaryOutAdj_bnone_bsome {h : ℕ} {j : Fin 2} {y : BVert h} :
    binaryOutAdj (h + 1) (bnone h) (bsome j y) ↔ y = broot h := Iff.rfl

theorem binaryOutAdj_bsome_bsome {h : ℕ} {i j : Fin 2} {x y : BVert h} :
    binaryOutAdj (h + 1) (bsome i x) (bsome j y) ↔ i = j ∧ binaryOutAdj h x y := Iff.rfl

/-- The key restricted to subtree `j`. -/
def subKey {h : ℕ} (f : BVert (h + 1) → ℕ) (j : Fin 2) : BVert h → ℕ :=
  fun x => f (bsome j x)

theorem subKey_apply {h : ℕ} (f : BVert (h + 1) → ℕ) (j : Fin 2) (x : BVert h) :
    subKey f j x = f (bsome j x) := rfl

/-- Arcs inside a subtree are arcs of the big tree, so a topological key restricts to a
topological key. -/
theorem keyTopological_subKey {h : ℕ} {f : BVert (h + 1) → ℕ} (hf : KeyTopological (h + 1) f)
    (j : Fin 2) : KeyTopological h (subKey f j) :=
  fun a b hab => hf (bsome j a) (bsome j b) (binaryOutAdj_bsome_bsome.mpr ⟨rfl, hab⟩)

/-- The injection of subtree `j` into the tree one level up. -/
theorem bsome_injective {h : ℕ} (j : Fin 2) : Function.Injective (bsome (h := h) j) :=
  fun _ _ hab => (bsome_inj hab).2

/-! ### The root has the least key -/

/-- Every vertex other than the root is reachable from the root, so the root has the least
key under any topological key. -/
theorem root_lt_of_keyTopological : ∀ (h : ℕ) (f : BVert h → ℕ), KeyTopological h f →
    ∀ x : BVert h, x ≠ broot h → f (broot h) < f x
  | 0, _, _, x, hx => by
    cases x
    exact (hx rfl).elim
  | h + 1, f, hf, x, hx => by
    rcases x with _ | ⟨i, y⟩
    · exact (hx rfl).elim
    · have h1 : f (bnone h) < f (bsome i (broot h)) :=
        hf (bnone h) (bsome i (broot h)) (binaryOutAdj_bnone_bsome.mpr rfl)
      by_cases hy : y = broot h
      · subst hy
        exact h1
      · have h2 : subKey f i (broot h) < subKey f i y :=
          root_lt_of_keyTopological h (subKey f i) (keyTopological_subKey hf i) y hy
        rw [subKey_apply, subKey_apply] at h2
        exact lt_trans h1 h2

/-! ### The cut lemma -/

/-- **The cut lemma.** If some vertex has key below `t` and some vertex key at least `t`, an
arc crosses the threshold forwards. -/
theorem exists_adj_across : ∀ (h : ℕ) (f : BVert h → ℕ) (t : ℕ), KeyTopological h f →
    (∃ x, f x < t) → (∃ y, t ≤ f y) → ∃ w u, f w < t ∧ binaryOutAdj h w u ∧ t ≤ f u
  | 0, _, _, _, ⟨x, hx⟩, ⟨y, hy⟩ => by
    cases x
    cases y
    omega
  | h + 1, f, t, hf, ⟨x, hx⟩, ⟨y, hy⟩ => by
    have hroot : f (bnone h) < t := by
      by_cases hxn : x = bnone h
      · subst hxn
        exact hx
      · exact lt_trans (root_lt_of_keyTopological (h + 1) f hf x hxn) hx
    rcases y with _ | ⟨j, y'⟩
    · exact absurd hy (not_le.mpr hroot)
    · by_cases hb : t ≤ f (bsome j (broot h))
      · exact ⟨bnone h, bsome j (broot h), hroot, binaryOutAdj_bnone_bsome.mpr rfl, hb⟩
      · obtain ⟨w', u', hw', hadj, hu'⟩ :=
          exists_adj_across h (subKey f j) t (keyTopological_subKey hf j)
            ⟨broot h, not_le.mp hb⟩ ⟨y', hy⟩
        exact ⟨bsome j w', bsome j u', hw', binaryOutAdj_bsome_bsome.mpr ⟨rfl, hadj⟩, hu'⟩

/-! ### The induction step -/

/-- The cut of subtree `j` at a threshold injects into the cut of the big tree at the same
threshold. -/
theorem image_keyCut_subKey_subset {h : ℕ} (f : BVert (h + 1) → ℕ) (j : Fin 2) (t : ℕ) :
    (keyCut h (subKey f j) t).image (bsome j) ⊆ keyCut (h + 1) f t := by
  intro w hw
  rw [mem_image] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  rw [mem_keyCut_iff] at hw' ⊢
  obtain ⟨hlt, u', hadj, hu'⟩ := hw'
  exact ⟨hlt, bsome j u', binaryOutAdj_bsome_bsome.mpr ⟨rfl, hadj⟩, hu'⟩

/-- **The induction step.** If subtree `j` has a vertex `v'` with `h` vertices of its cut at
`v'`'s key, and subtree `k ≠ j` has a vertex at or above that key (subtree `k` finishes no
earlier than subtree `j`), then the big tree's cut at that key has `h + 1` vertices. -/
theorem card_keyCut_succ_ge {h : ℕ} (f : BVert (h + 1) → ℕ) (hf : KeyTopological (h + 1) f)
    (j k : Fin 2) (hjk : j ≠ k) (v' : BVert h)
    (hv' : h ≤ (keyCut h (subKey f j) (f (bsome j v'))).card)
    (y : BVert h) (hy : f (bsome j v') ≤ f (bsome k y)) :
    h + 1 ≤ (keyCut (h + 1) f (f (bsome j v'))).card := by
  -- (a) the `h` vertices of subtree `j`
  have himage := image_keyCut_subKey_subset f j (f (bsome j v'))
  -- (b) one more vertex outside subtree `j`
  have hroot : f (bnone h) < f (bsome j v') :=
    root_lt_of_keyTopological (h + 1) f hf (bsome j v') (bnone_ne_bsome j v').symm
  obtain ⟨w₀, hw₀, hw₀j⟩ : ∃ w₀ ∈ keyCut (h + 1) f (f (bsome j v')), ∀ x', w₀ ≠ bsome j x' := by
    by_cases hb : f (bsome j v') ≤ f (bsome k (broot h))
    · refine ⟨bnone h, ?_, fun x' => bnone_ne_bsome j x'⟩
      rw [mem_keyCut_iff]
      exact ⟨hroot, bsome k (broot h), binaryOutAdj_bnone_bsome.mpr rfl, hb⟩
    · obtain ⟨w', u', hw', hadj, hu'⟩ :=
        exists_adj_across h (subKey f k) (f (bsome j v')) (keyTopological_subKey hf k)
          ⟨broot h, not_le.mp hb⟩ ⟨y, hy⟩
      refine ⟨bsome k w', ?_, fun x' hx => hjk (bsome_inj hx).1.symm⟩
      rw [mem_keyCut_iff]
      exact ⟨hw', bsome k u', binaryOutAdj_bsome_bsome.mpr ⟨rfl, hadj⟩, hu'⟩
  -- (c) count
  have hnot : w₀ ∉ (keyCut h (subKey f j) (f (bsome j v'))).image (bsome j) := by
    rw [mem_image]
    rintro ⟨x', _, hx'⟩
    exact hw₀j x' hx'.symm
  have hsub : insert w₀ ((keyCut h (subKey f j) (f (bsome j v'))).image (bsome j)) ⊆
      keyCut (h + 1) f (f (bsome j v')) :=
    insert_subset hw₀ himage
  calc h + 1 ≤ (keyCut h (subKey f j) (f (bsome j v'))).card + 1 := by omega
    _ = ((keyCut h (subKey f j) (f (bsome j v'))).image (bsome j)).card + 1 := by
        rw [card_image_of_injective _ (bsome_injective j)]
    _ = (insert w₀ ((keyCut h (subKey f j) (f (bsome j v'))).image (bsome j))).card :=
        (card_insert_of_notMem hnot).symm
    _ ≤ _ := card_le_card hsub

/-! ### The lower bound -/

/-- Every topological key of the out-tree of height `h` has a vertex whose cut has at least
`h` vertices. -/
theorem exists_keyCut_card_ge : ∀ (h : ℕ) (f : BVert h → ℕ), KeyTopological h f →
    ∃ v, h ≤ (keyCut h f (f v)).card
  | 0, _, _ => ⟨broot 0, Nat.zero_le _⟩
  | h + 1, f, hf => by
    obtain ⟨v₀, hv₀⟩ := exists_keyCut_card_ge h (subKey f 0) (keyTopological_subKey hf 0)
    obtain ⟨v₁, hv₁⟩ := exists_keyCut_card_ge h (subKey f 1) (keyTopological_subKey hf 1)
    obtain ⟨m₀, -, hm₀⟩ := exists_max_image (univ : Finset (BVert h))
      (fun x => f (bsome 0 x)) ⟨broot h, mem_univ _⟩
    obtain ⟨m₁, -, hm₁⟩ := exists_max_image (univ : Finset (BVert h))
      (fun x => f (bsome 1 x)) ⟨broot h, mem_univ _⟩
    rcases le_total (f (bsome 0 m₀)) (f (bsome 1 m₁)) with hle | hle
    · exact ⟨bsome 0 v₀, card_keyCut_succ_ge f hf 0 1 (by decide) v₀ hv₀ m₁
        (le_trans (hm₀ v₀ (mem_univ _)) hle)⟩
    · exact ⟨bsome 1 v₁, card_keyCut_succ_ge f hf 1 0 (by decide) v₁ hv₁ m₀
        (le_trans (hm₁ v₁ (mem_univ _)) hle)⟩

/-- The pre-placement boundary of a layout at the step of `v` is the cut of its position key
at `v`'s position. -/
theorem preBoundary_eq_keyCut {h : ℕ} (σ : LinearLayout (BVert h)) (v : BVert h) :
    preBoundary (binaryOutTree h) ∅ σ (σ v).val =
      keyCut h (fun x => (σ x).val) (σ v).val := by
  ext w
  rw [mem_preBoundary_iff, mem_keyCut_iff]
  simp [binaryOutTree_adj]

/-- **Main theorem.** Every topological layout of the complete binary out-tree of height `h`
has a step whose pre-placement boundary has at least `h` vertices. -/
theorem exists_preBoundary_binaryOutTree (h : ℕ) (σ : LinearLayout (BVert h))
    (hσ : IsTopological (binaryOutTree h) σ) :
    ∃ i : Fin (Fintype.card (BVert h)), h ≤ (preBoundary (binaryOutTree h) ∅ σ i.val).card := by
  obtain ⟨v, hv⟩ := exists_keyCut_card_ge h (fun x => (σ x).val)
    (fun a b hab => Fin.lt_def.mp (hσ a b hab))
  exact ⟨σ v, by rw [preBoundary_eq_keyCut]; exact hv⟩

/-- The demand of every topological layout of the binary out-tree of height `h` is at least
`h + 1`. -/
theorem layoutDemand_binaryOutTree_ge {h : ℕ} {σ : LinearLayout (BVert h)}
    (hσ : IsTopological (binaryOutTree h) σ) :
    h + 1 ≤ layoutDemand (binaryOutTree h) ∅ σ := by
  obtain ⟨i, hi⟩ := exists_preBoundary_binaryOutTree h σ hσ
  exact le_trans (Nat.add_le_add_right hi 1)
    (card_preBoundary_add_one_le_layoutDemand _ _ _ i)

/-! ### The matching upper bound: the depth-first order

Root, then subtree `0` in its own order, then subtree `1` in its own order. While subtree `0`
is being placed the root waits (one pebble) and the rest of the boundary is subtree `0`'s;
while subtree `1` is being placed the root is still waiting (its second child is unplaced)
until subtree `1`'s root goes down, after which the boundary is subtree `1`'s alone. -/

theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  revert i
  decide

/-- The depth-first key one level up: root `0`, subtree `0` shifted by `1`, subtree `1`
shifted by `1 + B₀` where `B₀` bounds the keys of subtree `0`. -/
def dfsKey {h : ℕ} (B₀ : ℕ) (f₀ f₁ : BVert h → ℕ) : BVert (h + 1) → ℕ
  | none => 0
  | some (i, x) => if i = 0 then 1 + f₀ x else 1 + B₀ + f₁ x

theorem dfsKey_bnone {h : ℕ} (B₀ : ℕ) (f₀ f₁ : BVert h → ℕ) :
    dfsKey B₀ f₀ f₁ (bnone h) = 0 := rfl

theorem dfsKey_bsome_zero {h : ℕ} (B₀ : ℕ) (f₀ f₁ : BVert h → ℕ) (x : BVert h) :
    dfsKey B₀ f₀ f₁ (bsome 0 x) = 1 + f₀ x := by
  simp [dfsKey, bsome]

theorem dfsKey_bsome_one {h : ℕ} (B₀ : ℕ) (f₀ f₁ : BVert h → ℕ) (x : BVert h) :
    dfsKey B₀ f₀ f₁ (bsome 1 x) = 1 + B₀ + f₁ x := by
  simp [dfsKey, bsome]

/-- At `h = 0` the cut is empty: there is no arc. -/
theorem keyCut_zero (f : BVert 0 → ℕ) (t : ℕ) : keyCut 0 f t = ∅ := by
  apply eq_empty_of_forall_notMem
  intro w hw
  rw [mem_keyCut_iff] at hw
  obtain ⟨_, u, hadj, _⟩ := hw
  exact binaryOutAdj_zero w u hadj

/-- The cut of the depth-first key at a vertex of subtree `i` is contained in the root
together with the cut of subtree `i` at that vertex. -/
theorem keyCut_dfsKey_subset {h : ℕ} (B₀ : ℕ) (f₀ f₁ : BVert h → ℕ) (hB₀ : ∀ x, f₀ x < B₀)
    (i : Fin 2) (v' : BVert h) :
    keyCut (h + 1) (dfsKey B₀ f₀ f₁) (dfsKey B₀ f₀ f₁ (bsome i v')) ⊆
      insert (bnone h) ((keyCut h (if i = 0 then f₀ else f₁)
        ((if i = 0 then f₀ else f₁) v')).image (bsome i)) := by
  intro w hw
  rw [mem_keyCut_iff] at hw
  obtain ⟨hlt, u, hadj, hu⟩ := hw
  rcases w with _ | ⟨i', w'⟩
  · exact mem_insert_self _ _
  · rcases u with _ | ⟨i'', u'⟩
    · exact (not_binaryOutAdj_succ_some_none hadj).elim
    · obtain ⟨rfl, hadj'⟩ := binaryOutAdj_succ_some_some.mp hadj
      apply mem_insert_of_mem
      show bsome i' w' ∈ _
      rw [mem_image]
      change dfsKey B₀ f₀ f₁ (bsome i' w') < dfsKey B₀ f₀ f₁ (bsome i v') at hlt
      change dfsKey B₀ f₀ f₁ (bsome i v') ≤ dfsKey B₀ f₀ f₁ (bsome i' u') at hu
      have hv := hB₀ v'
      have hu'' := hB₀ u'
      have hw'' := hB₀ w'
      rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases i' with rfl | rfl <;>
        simp only [dfsKey_bsome_zero, dfsKey_bsome_one] at hlt hu
      · refine ⟨w', ?_, rfl⟩
        rw [mem_keyCut_iff]
        exact ⟨by simpa using hlt, u', hadj', by simpa using hu⟩
      · omega
      · omega
      · refine ⟨w', ?_, rfl⟩
        rw [mem_keyCut_iff]
        exact ⟨by simpa using hlt, u', hadj', by simpa using hu⟩

/-- **The depth-first key.** For every `h` there is an injective topological key, bounded by
some `B`, whose every cut has at most `h` vertices. -/
theorem exists_key_keyCut_card_le : ∀ h : ℕ, ∃ (f : BVert h → ℕ) (B : ℕ),
    Function.Injective f ∧ KeyTopological h f ∧ (∀ x, f x < B) ∧
      ∀ v, (keyCut h f (f v)).card ≤ h
  | 0 => by
    refine ⟨fun _ => 0, 1, ?_, ?_, fun _ => Nat.one_pos, fun v => ?_⟩
    · intro a b _
      cases a
      cases b
      rfl
    · intro a b hab
      exact (binaryOutAdj_zero a b hab).elim
    · rw [keyCut_zero]
      exact le_rfl
  | h + 1 => by
    obtain ⟨f₀, B₀, hinj₀, htop₀, hB₀, hcut₀⟩ := exists_key_keyCut_card_le h
    obtain ⟨f₁, B₁, hinj₁, htop₁, hB₁, hcut₁⟩ := exists_key_keyCut_card_le h
    refine ⟨dfsKey B₀ f₀ f₁, 1 + B₀ + B₁, ?_, ?_, ?_, ?_⟩
    · -- injective
      intro a b hab
      rcases a with _ | ⟨i, x⟩ <;> rcases b with _ | ⟨i', y⟩
      · rfl
      · change dfsKey B₀ f₀ f₁ (bnone h) = dfsKey B₀ f₀ f₁ (bsome i' y) at hab
        rw [dfsKey_bnone] at hab
        rcases fin2_cases i' with rfl | rfl <;>
          simp only [dfsKey_bsome_zero, dfsKey_bsome_one] at hab <;> omega
      · change dfsKey B₀ f₀ f₁ (bsome i x) = dfsKey B₀ f₀ f₁ (bnone h) at hab
        rw [dfsKey_bnone] at hab
        rcases fin2_cases i with rfl | rfl <;>
          simp only [dfsKey_bsome_zero, dfsKey_bsome_one] at hab <;> omega
      · change dfsKey B₀ f₀ f₁ (bsome i x) = dfsKey B₀ f₀ f₁ (bsome i' y) at hab
        have hx := hB₀ x
        have hy := hB₀ y
        rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases i' with rfl | rfl <;>
          simp only [dfsKey_bsome_zero, dfsKey_bsome_one] at hab
        · rw [hinj₀ (by omega : f₀ x = f₀ y)]
        · omega
        · omega
        · rw [hinj₁ (by omega : f₁ x = f₁ y)]
    · -- topological
      intro a b hab
      rcases a with _ | ⟨i, x⟩ <;> rcases b with _ | ⟨i', y⟩
      · exact (not_binaryOutAdj_succ_none_none hab).elim
      · change dfsKey B₀ f₀ f₁ (bnone h) < dfsKey B₀ f₀ f₁ (bsome i' y)
        rw [dfsKey_bnone]
        rcases fin2_cases i' with rfl | rfl <;>
          simp only [dfsKey_bsome_zero, dfsKey_bsome_one] <;> omega
      · exact (not_binaryOutAdj_succ_some_none hab).elim
      · obtain ⟨rfl, hadj⟩ := binaryOutAdj_succ_some_some.mp hab
        change dfsKey B₀ f₀ f₁ (bsome i x) < dfsKey B₀ f₀ f₁ (bsome i y)
        rcases fin2_cases i with rfl | rfl <;>
          simp only [dfsKey_bsome_zero, dfsKey_bsome_one]
        · have := htop₀ x y hadj
          omega
        · have := htop₁ x y hadj
          omega
    · -- bounded
      intro x
      rcases x with _ | ⟨i, x⟩
      · change dfsKey B₀ f₀ f₁ (bnone h) < 1 + B₀ + B₁
        rw [dfsKey_bnone]
        omega
      · change dfsKey B₀ f₀ f₁ (bsome i x) < 1 + B₀ + B₁
        have hx₀ := hB₀ x
        have hx₁ := hB₁ x
        rcases fin2_cases i with rfl | rfl <;>
          simp only [dfsKey_bsome_zero, dfsKey_bsome_one] <;> omega
    · -- the cuts
      intro v
      rcases v with _ | ⟨i, v'⟩
      · change (keyCut (h + 1) (dfsKey B₀ f₀ f₁) (dfsKey B₀ f₀ f₁ (bnone h))).card ≤ h + 1
        rw [dfsKey_bnone]
        have : keyCut (h + 1) (dfsKey B₀ f₀ f₁) 0 = ∅ := by
          apply eq_empty_of_forall_notMem
          intro w hw
          rw [mem_keyCut_iff] at hw
          exact absurd hw.1 (Nat.not_lt_zero _)
        rw [this]
        exact Nat.zero_le _
      · change (keyCut (h + 1) (dfsKey B₀ f₀ f₁) (dfsKey B₀ f₀ f₁ (bsome i v'))).card ≤ h + 1
        refine le_trans (card_le_card (keyCut_dfsKey_subset B₀ f₀ f₁ hB₀ i v')) ?_
        refine le_trans (card_insert_le _ _) ?_
        rw [card_image_of_injective _ (bsome_injective i)]
        rcases fin2_cases i with rfl | rfl
        · simpa using hcut₀ v'
        · simpa using hcut₁ v'

/-- A layout sorted by an injective key has the key's order exactly. -/
theorem exists_layout_of_injective_key {h : ℕ} (f : BVert h → ℕ) (hinj : Function.Injective f) :
    ∃ σ : LinearLayout (BVert h), ∀ u v, (σ u).val < (σ v).val ↔ f u < f v := by
  obtain ⟨σ, hσ⟩ := exists_layout_sorted f
  refine ⟨σ, fun u v => ⟨fun huv => ?_, hσ u v⟩⟩
  by_contra hfuv
  rcases Nat.lt_or_ge (f v) (f u) with hvu | hvu
  · have := hσ v u hvu
    omega
  · have huv' : u = v := hinj (le_antisymm hvu (not_lt.mp hfuv))
    subst huv'
    exact lt_irrefl _ huv

/-- Under a layout with the key's order, the pre-placement boundary at the step of `v` is the
key's cut at `v`. -/
theorem preBoundary_eq_keyCut_of_key {h : ℕ} (f : BVert h → ℕ) (σ : LinearLayout (BVert h))
    (hσ : ∀ u v, (σ u).val < (σ v).val ↔ f u < f v) (v : BVert h) :
    preBoundary (binaryOutTree h) ∅ σ (σ v).val = keyCut h f (f v) := by
  ext w
  rw [mem_preBoundary_iff, mem_keyCut_iff]
  have hle : ∀ u, (σ v).val ≤ (σ u).val ↔ f v ≤ f u := by
    intro u
    rw [← not_lt, ← not_lt, hσ]
  simp only [notMem_empty, false_or, binaryOutTree_adj, hσ, hle]

/-- **The depth-first layout.** Some topological layout of the binary out-tree of height `h`
has demand at most `h + 1`. -/
theorem exists_isTopological_layoutDemand_le (h : ℕ) :
    ∃ σ : LinearLayout (BVert h),
      IsTopological (binaryOutTree h) σ ∧ layoutDemand (binaryOutTree h) ∅ σ ≤ h + 1 := by
  obtain ⟨f, _, hinj, htop, _, hcut⟩ := exists_key_keyCut_card_le h
  obtain ⟨σ, hσ⟩ := exists_layout_of_injective_key f hinj
  refine ⟨σ, fun a b hab => Fin.lt_def.mpr ((hσ a b).mpr (htop a b hab)), ?_⟩
  rw [layoutDemand_le_iff]
  intro i
  have hi : i.val = (σ (σ.symm i)).val := by rw [σ.apply_symm_apply]
  rw [hi, preBoundary_eq_keyCut_of_key f σ hσ]
  exact Nat.add_le_add_right (hcut _) 1

/-- **The demand of the binary out-tree is exactly `h + 1`**, as the least demand over
topological layouts. -/
theorem topologicalDemand_binaryOutTree (h : ℕ) :
    topologicalDemand (binaryOutTree h) ∅ = h + 1 := by
  obtain ⟨σ, hσ, hle⟩ := exists_isTopological_layoutDemand_le h
  unfold topologicalDemand
  apply le_antisymm
  · exact le_trans (csInf_le (OrderBot.bddBelow _) ⟨⟨σ, hσ⟩, rfl⟩) hle
  · refine le_csInf ⟨_, ⟨⟨σ, hσ⟩, rfl⟩⟩ ?_
    rintro k ⟨⟨τ, hτ⟩, rfl⟩
    exact layoutDemand_binaryOutTree_ge hτ

end Complex

end MOSPFormalization
