/-
Copyright (c) 2026 Alexandre Linhares. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# A compact generating class of blockages: cliques, minor pullback, branching

`Blockage.lean` proves that a blockage of order `n` (Bienstock, Robertson, Seymour &
Thomas 1991, Section 2) forces `pathwidth G ≥ n`. A blockage is a family of vertex sets,
exponential in general; this file gives three operators that build blockages from compact
data and proves, by construction and not by enumeration of separations, that their
outputs satisfy the three axioms. The class they generate is the subject of
`reports/blockage_class.md`; `learning/blockage_class.py` checked every statement below by
brute force on every graph to 6 vertices before it was written here (and the ceiling of
the class on small graphs is computed there).

**Relative blockages.** Everything is stated for a vertex set `C` of `G` (`C = univ` is
the ordinary notion), so that the sub-blockages a branch carries are blockages of `G[C_i]`
written with `Finset`s of `V` and no subtypes: `attIn G C X` is the set of vertices of
`X ⊆ C` with a neighbour in `C \ X`, `ComplementaryIn G C X₁ X₂` is a separation of
`G[C]`, and `IsBlockageIn G C n B` is the three axioms in `C`. At `C = univ` this is
`IsBlockage` (`isBlockageIn_univ_iff`).

**Frames.** Every blockage is an *avoidance family*: by axiom (ii) the sets that are not
in it are upward closed among small-attachment sets, so a blockage is
`avoid G C n big = {X ⊆ C : |attIn X| ≤ n, ¬ big X}` for an upward-closed predicate
`big`. A `Frame G C n` is such a predicate with the proof that its avoidance family is a
blockage of order `n` in `C`. The three operators:

* `Frame.clique` — a clique `K ⊆ C` with `|K| ≥ n + 1`; `big X := K ⊆ X`. A clique cannot
  be split by a separation, and lies on at most one side of a separation of order `≤ n`.
* `Frame.minor` — a minor model `T : W → Finset V` inside `C` (disjoint, nonempty,
  connected branch sets, an edge of `G` behind every edge of `H`) and a frame of order
  `n` on all of `H`; `big X := big_H {w : T w meets X}`. A separation of `G[C]` of order
  `≤ n` pulls back to a separation of `H` of order `≤ n`, because a connected branch set
  meeting both sides meets the separator (`ComplementaryIn.exists_mem_inter_of_connected`).
* `Frame.branch` — the **linked branch lemma** of `Sandwich.lean` (Fellows & Langston
  1987 Lemma 4.3, Kinnersley 1992 Corollary 4.2) as a blockage operator: three disjoint
  connected `A, B, D ⊆ C` carrying frames of order `k`, every two joined by a connected
  connector inside `C` disjoint from the third; `big X := at least two of
  big_A (X ∩ A), big_B (X ∩ B), big_D (X ∩ D)`; order `k + 1`. In a separation of order
  `≤ k + 1` either every branch sees a separator of order `≤ k`, and then each branch is
  big on exactly one side so exactly one side has two big branches; or one branch holds
  the whole separator, and then the other two branches and their connector miss it and
  lie, whole, on one side (`exactly_one_of_full`).

`Frame.pathwidth_ge` is the certificate theorem: a frame of order `n` on `univ` gives
`n ≤ pathwidth G`. `#print axioms` at the end: `propext`, `Classical.choice`,
`Quot.sound` only.
-/

import MOSPFormalization.Blockage
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option linter.unusedSectionVars false

namespace MOSPFormalization

namespace Blockage

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Attachments and separations relative to a vertex set -/

/-- The attachments of `X` inside `C`: vertices of `X` with a neighbour in `C \ X`. -/
def attIn (C X : Finset V) : Finset V := X.filter fun v => ∃ u ∈ C, u ∉ X ∧ G.Adj v u

theorem mem_attIn {C X : Finset V} {v : V} :
    v ∈ attIn G C X ↔ v ∈ X ∧ ∃ u ∈ C, u ∉ X ∧ G.Adj v u := by
  simp [attIn]

theorem attIn_subset (C X : Finset V) : attIn G C X ⊆ X := Finset.filter_subset _ _

@[simp] theorem attIn_empty (C : Finset V) : attIn G C (∅ : Finset V) = ∅ := by
  ext v; simp [mem_attIn]

@[simp] theorem attIn_self (C : Finset V) : attIn G C C = ∅ := by
  ext v
  simp only [mem_attIn, Finset.notMem_empty, iff_false, not_and, not_exists]
  intro _ u hu hu' _
  exact hu' hu

theorem attIn_univ (X : Finset V) : attIn G Finset.univ X = att G X := by
  ext v; simp [mem_attIn, mem_att]

/-- An attachment of `X ∩ D` inside `D ⊆ C` is an attachment of `X` inside `C`. -/
theorem attIn_inter_subset {C D : Finset V} (hD : D ⊆ C) (X : Finset V) :
    attIn G D (X ∩ D) ⊆ attIn G C X := by
  intro v hv
  rw [mem_attIn] at hv ⊢
  obtain ⟨hvX, u, huD, huX, hadj⟩ := hv
  exact ⟨(Finset.mem_inter.mp hvX).1, u, hD huD,
    fun h => huX (Finset.mem_inter.mpr ⟨h, huD⟩), hadj⟩

/-- A separation of `G[C]`: `X₁ ∪ X₂ = C` and the attachments of `X₁` lie in `X₂`. -/
def ComplementaryIn (C X₁ X₂ : Finset V) : Prop := X₁ ∪ X₂ = C ∧ attIn G C X₁ ⊆ X₂

theorem complementaryIn_univ_iff (X₁ X₂ : Finset V) :
    ComplementaryIn G Finset.univ X₁ X₂ ↔ Complementary G X₁ X₂ := by
  unfold ComplementaryIn Complementary
  rw [attIn_univ]

/-- A connected set with a vertex in `X` and a vertex outside `X` has an edge of `G`
leaving `X` with both ends in it (walk from one to the other; the first step out). -/
theorem exists_boundary_edge_of_connected (Z : Finset V)
    (hconn : (G.induce (↑Z : Set V)).Connected) {z z' : V} (hz : z ∈ Z) (hz' : z' ∈ Z)
    {X : Finset V} (hzX : z ∈ X) (hz'X : z' ∉ X) :
    ∃ x ∈ Z, x ∈ X ∧ ∃ u ∈ Z, u ∉ X ∧ G.Adj x u := by
  have key : ∀ (a b : (↑Z : Set V)) (_ : (G.induce (↑Z : Set V)).Walk a b),
      a.1 ∈ X → b.1 ∉ X → ∃ x ∈ Z, x ∈ X ∧ ∃ u ∈ Z, u ∉ X ∧ G.Adj x u := by
    intro a b p
    induction p with
    | nil => intro ha hb; exact absurd ha hb
    | @cons a c b hac _ ih =>
      intro ha hb
      by_cases hc : c.1 ∈ X
      · exact ih hc hb
      · exact ⟨a.1, Finset.mem_coe.mp a.2, ha, c.1, Finset.mem_coe.mp c.2, hc, hac⟩
  obtain ⟨p⟩ := hconn.preconnected ⟨z, Finset.mem_coe.mpr hz⟩ ⟨z', Finset.mem_coe.mpr hz'⟩
  exact key _ _ p hzX hz'X

namespace ComplementaryIn

variable {G} {C X₁ X₂ : Finset V}

theorem left_subset (h : ComplementaryIn G C X₁ X₂) : X₁ ⊆ C :=
  h.1 ▸ Finset.subset_union_left

theorem right_subset (h : ComplementaryIn G C X₁ X₂) : X₂ ⊆ C :=
  h.1 ▸ Finset.subset_union_right

theorem mem_left_of_not_mem_right (h : ComplementaryIn G C X₁ X₂) {v : V} (hv : v ∈ C)
    (hv₂ : v ∉ X₂) : v ∈ X₁ := by
  have : v ∈ X₁ ∪ X₂ := h.1.symm ▸ hv
  exact (Finset.mem_union.mp this).resolve_right hv₂

theorem mem_right_of_not_mem_left (h : ComplementaryIn G C X₁ X₂) {v : V} (hv : v ∈ C)
    (hv₁ : v ∉ X₁) : v ∈ X₂ := by
  have : v ∈ X₁ ∪ X₂ := h.1.symm ▸ hv
  exact (Finset.mem_union.mp this).resolve_left hv₁

theorem attIn_subset_inter (h : ComplementaryIn G C X₁ X₂) : attIn G C X₁ ⊆ X₁ ∩ X₂ :=
  fun v hv => Finset.mem_inter.mpr ⟨attIn_subset G C X₁ hv, h.2 hv⟩

/-- A separation is symmetric: no edge joins `X₁ \ X₂` to `X₂ \ X₁`. -/
theorem symm (h : ComplementaryIn G C X₁ X₂) : ComplementaryIn G C X₂ X₁ := by
  refine ⟨by rw [Finset.union_comm]; exact h.1, ?_⟩
  intro v hv
  rw [mem_attIn] at hv
  obtain ⟨hvX₂, u, huC, huX₂, hadj⟩ := hv
  have huX₁ : u ∈ X₁ := h.mem_left_of_not_mem_right huC huX₂
  by_contra hvX₁
  have : u ∈ attIn G C X₁ :=
    (mem_attIn G).mpr ⟨huX₁, v, h.right_subset hvX₂, hvX₁, hadj.symm⟩
  exact huX₂ (h.2 this)

theorem attIn_right_subset_inter (h : ComplementaryIn G C X₁ X₂) :
    attIn G C X₂ ⊆ X₁ ∩ X₂ := by
  intro v hv
  have := h.symm.attIn_subset_inter hv
  rw [Finset.inter_comm] at this
  exact this

/-- Restriction to `D ⊆ C` is a separation of `G[D]`. -/
theorem inter (h : ComplementaryIn G C X₁ X₂) {D : Finset V} (hD : D ⊆ C) :
    ComplementaryIn G D (X₁ ∩ D) (X₂ ∩ D) := by
  refine ⟨?_, ?_⟩
  · rw [← Finset.union_inter_distrib_right, h.1, Finset.inter_eq_right.mpr hD]
  · intro v hv
    have h' := attIn_inter_subset G hD X₁ hv
    exact Finset.mem_inter.mpr ⟨h.2 h', (Finset.mem_inter.mp (attIn_subset G D _ hv)).2⟩

/-- A connected set that misses the separator lies on one side, whole. -/
theorem sides (h : ComplementaryIn G C X₁ X₂) {Z : Finset V} (hZ : Z ⊆ C)
    (hconn : (G.induce (↑Z : Set V)).Connected) (hdisj : Disjoint (X₁ ∩ X₂) Z) :
    (Z ⊆ X₁ ∧ Disjoint Z X₂) ∨ (Z ⊆ X₂ ∧ Disjoint Z X₁) := by
  have hsub : Z ⊆ X₁ ∨ Z ⊆ X₂ := by
    by_contra hno
    obtain ⟨h1, h2⟩ := not_or.mp hno
    obtain ⟨z', hz'Z, hz'⟩ := Finset.not_subset.mp h1
    obtain ⟨z, hzZ, hz⟩ := Finset.not_subset.mp h2
    have hzX₁ : z ∈ X₁ := h.mem_left_of_not_mem_right (hZ hzZ) hz
    obtain ⟨x, hxZ, hxX, u, huZ, huX, hadj⟩ :=
      exists_boundary_edge_of_connected G Z hconn hzZ hz'Z hzX₁ hz'
    have hx : x ∈ attIn G C X₁ := (mem_attIn G).mpr ⟨hxX, u, hZ huZ, huX, hadj⟩
    exact Finset.disjoint_right.mp hdisj hxZ (Finset.mem_inter.mpr ⟨hxX, h.2 hx⟩)
  rcases hsub with hs | hs
  · refine Or.inl ⟨hs, Finset.disjoint_left.mpr fun v hvZ hvX₂ => ?_⟩
    exact Finset.disjoint_right.mp hdisj hvZ (Finset.mem_inter.mpr ⟨hs hvZ, hvX₂⟩)
  · refine Or.inr ⟨hs, Finset.disjoint_left.mpr fun v hvZ hvX₁ => ?_⟩
    exact Finset.disjoint_right.mp hdisj hvZ (Finset.mem_inter.mpr ⟨hvX₁, hs hvZ⟩)

/-- A connected set meeting both sides meets the separator. -/
theorem exists_mem_inter_of_connected (h : ComplementaryIn G C X₁ X₂) {Z : Finset V}
    (hZ : Z ⊆ C) (hconn : (G.induce (↑Z : Set V)).Connected)
    (h₁ : (Z ∩ X₁).Nonempty) (h₂ : (Z ∩ X₂).Nonempty) : (Z ∩ (X₁ ∩ X₂)).Nonempty := by
  by_contra hno
  have hdisj : Disjoint (X₁ ∩ X₂) Z := by
    rw [Finset.not_nonempty_iff_eq_empty] at hno
    exact (Finset.disjoint_iff_inter_eq_empty.mpr hno).symm
  rcases h.sides hZ hconn hdisj with ⟨_, hd⟩ | ⟨_, hd⟩
  · obtain ⟨v, hv⟩ := h₂
    exact Finset.disjoint_left.mp hd (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hv).2
  · obtain ⟨v, hv⟩ := h₁
    exact Finset.disjoint_left.mp hd (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hv).2

/-- Two connected sets on opposite sides of a separation, both missing the separator,
are not joined by an edge. -/
theorem not_adj_of_opposite (h : ComplementaryIn G C X₁ X₂) {Q Z : Finset V} (hZ : Z ⊆ C)
    (hQ₁ : Q ⊆ X₁) (hQ₂ : Disjoint Q X₂) (hZ₁ : Disjoint Z X₁) {q z : V} (hq : q ∈ Q)
    (hz : z ∈ Z) (hadj : G.Adj q z) : False := by
  have hzX₁ : z ∉ X₁ := Finset.disjoint_left.mp hZ₁ hz
  have : q ∈ attIn G C X₁ := (mem_attIn G).mpr ⟨hQ₁ hq, z, hZ hz, hzX₁, hadj⟩
  exact Finset.disjoint_left.mp hQ₂ hq (h.2 this)

end ComplementaryIn

/-! ### Blockages relative to a vertex set -/

/-- The blockage axioms (i)–(iii) in `C`; at `C = univ` this is `IsBlockage`. -/
structure IsBlockageIn (C : Finset V) (n : ℕ) (B : Set (Finset V)) : Prop where
  subset_of_mem : ∀ X ∈ B, X ⊆ C
  att_card_le : ∀ X ∈ B, (attIn G C X).card ≤ n
  mem_of_subset : ∀ X ∈ B, ∀ Y ⊆ X, (attIn G C Y).card ≤ n → Y ∈ B
  exactly_one : ∀ X₁ X₂, ComplementaryIn G C X₁ X₂ → (X₁ ∩ X₂).card ≤ n →
    Xor (X₁ ∈ B) (X₂ ∈ B)

theorem isBlockageIn_univ_iff {n : ℕ} {B : Set (Finset V)} :
    IsBlockageIn G Finset.univ n B ↔ IsBlockage G n B := by
  constructor
  · intro h
    exact ⟨fun X hX => by simpa [attIn_univ] using h.att_card_le X hX,
      fun X hX Y hY hYa => h.mem_of_subset X hX Y hY (by simpa [attIn_univ] using hYa),
      fun X₁ X₂ hc hcard =>
        h.exactly_one X₁ X₂ ((complementaryIn_univ_iff G X₁ X₂).mpr hc) hcard⟩
  · intro h
    exact ⟨fun X _ => Finset.subset_univ X,
      fun X hX => by simpa [attIn_univ] using h.att_card_le X hX,
      fun X hX Y hY hYa => h.mem_of_subset X hX Y hY (by simpa [attIn_univ] using hYa),
      fun X₁ X₂ hc hcard =>
        h.exactly_one X₁ X₂ ((complementaryIn_univ_iff G X₁ X₂).mp hc) hcard⟩

variable {G}

/-- `∅ ∈ 𝓑` and `C ∉ 𝓑`, from the complementary pair `(∅, C)`. -/
theorem IsBlockageIn.empty_mem_and_self_not_mem {C : Finset V} {n : ℕ} {B : Set (Finset V)}
    (hB : IsBlockageIn G C n B) : (∅ : Finset V) ∈ B ∧ C ∉ B := by
  have h := hB.exactly_one ∅ C ⟨by simp, by simp⟩ (by simp)
  rcases h with ⟨h0, hu⟩ | ⟨hu, h0⟩
  · exact ⟨h0, hu⟩
  · exact absurd (hB.mem_of_subset _ hu ∅ (Finset.empty_subset _) (by simp)) h0

/-! ### Avoidance families and frames -/

variable (G)

/-- The sets of `C` with at most `n` attachments that are not big. -/
def avoid (C : Finset V) (n : ℕ) (big : Finset V → Prop) : Set (Finset V) :=
  {X | X ⊆ C ∧ (attIn G C X).card ≤ n ∧ ¬ big X}

theorem mem_avoid_iff {C : Finset V} {n : ℕ} {big : Finset V → Prop} {X : Finset V}
    (hX : X ⊆ C) (hatt : (attIn G C X).card ≤ n) : X ∈ avoid G C n big ↔ ¬ big X := by
  simp [avoid, hX, hatt]

variable {G}

theorem IsBlockageIn.big_self {C : Finset V} {n : ℕ} {big : Finset V → Prop}
    (hB : IsBlockageIn G C n (avoid G C n big)) : big C := by
  by_contra h
  exact hB.empty_mem_and_self_not_mem.2
    ((mem_avoid_iff G (Finset.Subset.refl C) (by simp)).mpr h)

theorem IsBlockageIn.not_big_empty {C : Finset V} {n : ℕ} {big : Finset V → Prop}
    (hB : IsBlockageIn G C n (avoid G C n big)) : ¬ big ∅ :=
  (mem_avoid_iff G (Finset.empty_subset C) (by simp)).mp hB.empty_mem_and_self_not_mem.1

/-- Upward closed under inclusion. -/
def Upward (big : Finset V → Prop) : Prop := ∀ ⦃X Y : Finset V⦄, X ⊆ Y → big X → big Y

variable (G) in
/-- A frame: an upward-closed predicate whose avoidance family is a blockage of
order `n` in `C`. The compact data of a certificate is the predicate's description. -/
structure Frame (C : Finset V) (n : ℕ) where
  big : Finset V → Prop
  upward : Upward big
  blockage : IsBlockageIn G C n (avoid G C n big)

/-- **The certificate theorem**: a frame of order `n` on all of `V` forces
`pathwidth G ≥ n`. -/
theorem Frame.pathwidth_ge {n : ℕ} (F : Frame G Finset.univ n) : n ≤ pathwidth G :=
  pathwidth_ge_of_isBlockage ((isBlockageIn_univ_iff G).mp F.blockage)

/-! ### Operator 1: cliques -/

variable (G) in
/-- A clique of `n + 1` vertices in `C` is big; the sets missing one of its vertices form
a blockage of order `n` in `C`. -/
theorem isBlockageIn_clique {C K : Finset V} (hKC : K ⊆ C) (hK : G.IsClique (↑K : Set V))
    {n : ℕ} (hn : n + 1 ≤ K.card) :
    IsBlockageIn G C n (avoid G C n (fun X => K ⊆ X)) where
  subset_of_mem X hX := hX.1
  att_card_le X hX := hX.2.1
  mem_of_subset X hX Y hYX hY := ⟨hYX.trans hX.1, hY, fun h => hX.2.2 (h.trans hYX)⟩
  exactly_one X₁ X₂ hc hcard := by
    have hside : K ⊆ X₁ ∨ K ⊆ X₂ := by
      by_contra hno
      obtain ⟨h1, h2⟩ := not_or.mp hno
      obtain ⟨k₁, hk₁K, hk₁⟩ := Finset.not_subset.mp h1
      obtain ⟨k₂, hk₂K, hk₂⟩ := Finset.not_subset.mp h2
      have hk₂X₁ : k₂ ∈ X₁ := hc.mem_left_of_not_mem_right (hKC hk₂K) hk₂
      have hne : k₂ ≠ k₁ := fun h => hk₁ (h ▸ hk₂X₁)
      have hadj : G.Adj k₂ k₁ := hK (Finset.mem_coe.mpr hk₂K) (Finset.mem_coe.mpr hk₁K) hne
      have : k₂ ∈ attIn G C X₁ := (mem_attIn G).mpr ⟨hk₂X₁, k₁, hKC hk₁K, hk₁, hadj⟩
      exact hk₂ (hc.2 this)
    have hnot : ¬ (K ⊆ X₁ ∧ K ⊆ X₂) := fun ⟨h1, h2⟩ => by
      have := Finset.card_le_card (Finset.subset_inter h1 h2)
      omega
    have h1a := Finset.card_le_card hc.attIn_subset_inter
    have h2a := Finset.card_le_card hc.attIn_right_subset_inter
    rcases hside with h | h
    · exact Or.inr ⟨⟨hc.right_subset, by omega, fun h' => hnot ⟨h, h'⟩⟩, fun h' => h'.2.2 h⟩
    · exact Or.inl ⟨⟨hc.left_subset, by omega, fun h' => hnot ⟨h', h⟩⟩, fun h' => h'.2.2 h⟩

variable (G) in
/-- The clique frame. -/
def Frame.clique {C K : Finset V} (hKC : K ⊆ C) (hK : G.IsClique (↑K : Set V)) {n : ℕ}
    (hn : n + 1 ≤ K.card) : Frame G C n where
  big X := K ⊆ X
  upward _ _ hXY h := h.trans hXY
  blockage := isBlockageIn_clique G hKC hK hn

/-! ### Operator 2: pullback along a minor model -/

section Minor

variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

variable (G) in
/-- A model of `H` inside `C`: disjoint, nonempty, connected branch sets, and an edge of
`G` between the branch sets of every edge of `H`. -/
structure MinorModelIn (C : Finset V) (T : W → Finset V) : Prop where
  subset : ∀ w, T w ⊆ C
  nonempty : ∀ w, (T w).Nonempty
  connected : ∀ w, (G.induce (↑(T w) : Set V)).Connected
  disjoint : ∀ w w', w ≠ w' → Disjoint (T w) (T w')
  adj : ∀ w w', H.Adj w w' → ∃ x ∈ T w, ∃ y ∈ T w', G.Adj x y

/-- The branch sets a vertex set meets. -/
def pull (T : W → Finset V) (X : Finset V) : Finset W :=
  Finset.univ.filter fun w => (T w ∩ X).Nonempty

theorem mem_pull {T : W → Finset V} {X : Finset V} {w : W} :
    w ∈ pull T X ↔ (T w ∩ X).Nonempty := by
  simp [pull]

theorem pull_mono {T : W → Finset V} {X Y : Finset V} (hXY : X ⊆ Y) : pull T X ⊆ pull T Y := by
  intro w hw
  rw [mem_pull] at hw ⊢
  obtain ⟨x, hx⟩ := hw
  exact ⟨x, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, hXY (Finset.mem_inter.mp hx).2⟩⟩

variable {H}

/-- Branch sets are disjoint, so a set of them each meeting `A` in a vertex of its own is
no larger than `A`. -/
theorem card_le_of_forall_exists {C : Finset V} {T : W → Finset V} (hT : MinorModelIn G H C T)
    {S : Finset W} {A : Finset V} (h : ∀ w ∈ S, ∃ x ∈ T w, x ∈ A) : S.card ≤ A.card := by
  have hsub : S ⊆ A.biUnion (fun x => Finset.univ.filter fun w => x ∈ T w) := by
    intro w hw
    obtain ⟨x, hx, hxA⟩ := h w hw
    exact Finset.mem_biUnion.mpr ⟨x, hxA, by simp [hx]⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_biUnion_le_card_mul _ _ 1 fun x _ => ?_).trans (by omega)
  rw [Finset.card_le_one]
  intro w hw w' hw'
  by_contra hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
  exact Finset.disjoint_left.mp (hT.disjoint w w' hne) hw hw'

/-- The attachments of the pulled-back set are no more than those of the set: behind every
one lies an attachment inside its branch set (a boundary edge of the branch set, or the
edge of `G` behind the edge of `H`). -/
theorem card_att_pull_le {C : Finset V} {T : W → Finset V} (hT : MinorModelIn G H C T)
    (Y : Finset V) : (att H (pull T Y)).card ≤ (attIn G C Y).card := by
  apply card_le_of_forall_exists hT
  intro w hw
  rw [mem_att] at hw
  obtain ⟨hw, w', hw', hadj⟩ := hw
  rw [mem_pull] at hw hw'
  by_cases hsub : T w ⊆ Y
  · obtain ⟨x, hx, y, hy, hxy⟩ := hT.adj w w' hadj
    refine ⟨x, hx, (mem_attIn G).mpr ⟨hsub hx, y, hT.subset w' hy, ?_, hxy⟩⟩
    intro hyY
    exact hw' ⟨y, Finset.mem_inter.mpr ⟨hy, hyY⟩⟩
  · obtain ⟨z, hz⟩ := hw
    obtain ⟨z', hz'w, hz'⟩ := Finset.not_subset.mp hsub
    obtain ⟨x, hxT, hxY, u, huT, huY, hxu⟩ := exists_boundary_edge_of_connected G (T w)
      (hT.connected w) (Finset.mem_inter.mp hz).1 hz'w (Finset.mem_inter.mp hz).2 hz'
    exact ⟨x, hxT, (mem_attIn G).mpr ⟨hxY, u, hT.subset w huT, huY, hxu⟩⟩

/-- The pulled-back separation has order at most the original's. -/
theorem card_pull_inter_le {C : Finset V} {T : W → Finset V} (hT : MinorModelIn G H C T)
    {X₁ X₂ : Finset V} (hc : ComplementaryIn G C X₁ X₂) :
    (pull T X₁ ∩ pull T X₂).card ≤ (X₁ ∩ X₂).card := by
  apply card_le_of_forall_exists hT
  intro w hw
  obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hw
  rw [mem_pull] at h1 h2
  obtain ⟨x, hx⟩ := hc.exists_mem_inter_of_connected (hT.subset w) (hT.connected w) h1 h2
  exact ⟨x, (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩

/-- A separation of `G[C]` pulls back to a separation of `H`. -/
theorem complementary_pull {C : Finset V} {T : W → Finset V} (hT : MinorModelIn G H C T)
    {X₁ X₂ : Finset V} (hc : ComplementaryIn G C X₁ X₂) :
    Complementary H (pull T X₁) (pull T X₂) := by
  refine ⟨?_, ?_⟩
  · ext w
    simp only [Finset.mem_union, mem_pull, Finset.mem_univ, iff_true]
    obtain ⟨x, hx⟩ := hT.nonempty w
    have hxC : x ∈ X₁ ∪ X₂ := by rw [hc.1]; exact hT.subset w hx
    rcases Finset.mem_union.mp hxC with h | h
    · exact Or.inl ⟨x, Finset.mem_inter.mpr ⟨hx, h⟩⟩
    · exact Or.inr ⟨x, Finset.mem_inter.mpr ⟨hx, h⟩⟩
  · intro w hw
    rw [mem_att] at hw
    obtain ⟨_, w', hw', hadj⟩ := hw
    rw [mem_pull] at hw' ⊢
    obtain ⟨x, hx, y, hy, hxy⟩ := hT.adj w w' hadj
    have hyX₁ : y ∉ X₁ := fun h => hw' ⟨y, Finset.mem_inter.mpr ⟨hy, h⟩⟩
    by_cases hxX₁ : x ∈ X₁
    · have : x ∈ attIn G C X₁ := (mem_attIn G).mpr ⟨hxX₁, y, hT.subset w' hy, hyX₁, hxy⟩
      exact ⟨x, Finset.mem_inter.mpr ⟨hx, hc.2 this⟩⟩
    · exact ⟨x, Finset.mem_inter.mpr ⟨hx, hc.mem_right_of_not_mem_left (hT.subset w hx) hxX₁⟩⟩

variable (G) in
/-- **Pullback.** A blockage of order `n` on `H` pulls back along a model of `H` inside
`C` to a blockage of order `n` in `C`: `X` is big when the branch sets it meets form a
big set of `H`. -/
theorem isBlockageIn_minor {C : Finset V} {T : W → Finset V} (hT : MinorModelIn G H C T)
    {n : ℕ} {bigH : Finset W → Prop}
    (hH : IsBlockageIn H Finset.univ n (avoid H Finset.univ n bigH)) :
    IsBlockageIn G C n (avoid G C n (fun X => bigH (pull T X))) where
  subset_of_mem X hX := hX.1
  att_card_le X hX := hX.2.1
  mem_of_subset X hX Y hYX hY := by
    refine ⟨hYX.trans hX.1, hY, fun hb => ?_⟩
    have hXH : pull T X ∈ avoid H Finset.univ n bigH :=
      ⟨Finset.subset_univ _, by rw [attIn_univ]; exact (card_att_pull_le hT X).trans hX.2.1,
        hX.2.2⟩
    have hYH := hH.mem_of_subset _ hXH (pull T Y) (pull_mono hYX)
      (by rw [attIn_univ]; exact (card_att_pull_le hT Y).trans hY)
    exact hYH.2.2 hb
  exactly_one X₁ X₂ hc hcard := by
    have hx := hH.exactly_one (pull T X₁) (pull T X₂)
      ((complementaryIn_univ_iff H _ _).mpr (complementary_pull hT hc))
      ((card_pull_inter_le hT hc).trans hcard)
    have h1 : (attIn G C X₁).card ≤ n := (Finset.card_le_card hc.attIn_subset_inter).trans hcard
    have h2 : (attIn G C X₂).card ≤ n :=
      (Finset.card_le_card hc.attIn_right_subset_inter).trans hcard
    have e1 := mem_avoid_iff H (n := n) (big := bigH) (Finset.subset_univ (pull T X₁))
      (by rw [attIn_univ]; exact (card_att_pull_le hT X₁).trans h1)
    have e2 := mem_avoid_iff H (n := n) (big := bigH) (Finset.subset_univ (pull T X₂))
      (by rw [attIn_univ]; exact (card_att_pull_le hT X₂).trans h2)
    unfold Xor at hx ⊢
    rw [mem_avoid_iff G hc.left_subset h1, mem_avoid_iff G hc.right_subset h2]
    rw [e1, e2] at hx
    exact hx

variable (G) in
/-- The pulled-back frame. -/
def Frame.minor {C : Finset V} {T : W → Finset V} (hT : MinorModelIn G H C T) {n : ℕ}
    (F : Frame H Finset.univ n) : Frame G C n where
  big X := F.big (pull T X)
  upward _ _ hXY h := F.upward (pull_mono hXY) h
  blockage := isBlockageIn_minor G hT F.blockage

end Minor

/-! ### Operator 3: the linked branch lemma as a blockage operator -/

variable (G) in
/-- Three pairwise disjoint connected branches inside `C`, every two joined by a connected
connector inside `C` that misses the third branch (`Sandwich.lean`'s linked form; the
connectors may meet the branches they join). -/
structure BranchIn (C A B D : Finset V) : Prop where
  subA : A ⊆ C
  subB : B ⊆ C
  subD : D ⊆ C
  disjAB : Disjoint A B
  disjAD : Disjoint A D
  disjBD : Disjoint B D
  connA : (G.induce (↑A : Set V)).Connected
  connB : (G.induce (↑B : Set V)).Connected
  connD : (G.induce (↑D : Set V)).Connected
  linkAB : ∃ Q ⊆ C, Disjoint Q D ∧ (G.induce (↑Q : Set V)).Connected ∧
    (∃ q ∈ Q, ∃ a ∈ A, G.Adj q a) ∧ (∃ q ∈ Q, ∃ b ∈ B, G.Adj q b)
  linkAD : ∃ Q ⊆ C, Disjoint Q B ∧ (G.induce (↑Q : Set V)).Connected ∧
    (∃ q ∈ Q, ∃ a ∈ A, G.Adj q a) ∧ (∃ q ∈ Q, ∃ d ∈ D, G.Adj q d)
  linkBD : ∃ Q ⊆ C, Disjoint Q A ∧ (G.induce (↑Q : Set V)).Connected ∧
    (∃ q ∈ Q, ∃ b ∈ B, G.Adj q b) ∧ (∃ q ∈ Q, ∃ d ∈ D, G.Adj q d)

/-- At least two of the three branches are big. -/
def twoOf (bA bB bD : Finset V → Prop) (A B D X : Finset V) : Prop :=
  (bA (X ∩ A) ∧ bB (X ∩ B)) ∨ (bA (X ∩ A) ∧ bD (X ∩ D)) ∨ (bB (X ∩ B) ∧ bD (X ∩ D))

theorem twoOf_upward {bA bB bD : Finset V → Prop} (hA : Upward bA) (hB : Upward bB)
    (hD : Upward bD) (A B D : Finset V) : Upward (twoOf bA bB bD A B D) := by
  intro X Y hXY h
  have iA : X ∩ A ⊆ Y ∩ A := Finset.inter_subset_inter hXY (Finset.Subset.refl A)
  have iB : X ∩ B ⊆ Y ∩ B := Finset.inter_subset_inter hXY (Finset.Subset.refl B)
  have iD : X ∩ D ⊆ Y ∩ D := Finset.inter_subset_inter hXY (Finset.Subset.refl D)
  unfold twoOf at h ⊢
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hA iA h1, hB iB h2⟩
  · exact Or.inr (Or.inl ⟨hA iA h1, hD iD h2⟩)
  · exact Or.inr (Or.inr ⟨hB iB h1, hD iD h2⟩)

/-- A branch whose share of the separator has order `≤ k` is big on exactly one side. -/
theorem branch_xor {C Z : Finset V} (hZ : Z ⊆ C) {k : ℕ} {bigZ : Finset V → Prop}
    (hf : IsBlockageIn G Z k (avoid G Z k bigZ)) {X₁ X₂ : Finset V}
    (hc : ComplementaryIn G C X₁ X₂) (hord : (X₁ ∩ X₂ ∩ Z).card ≤ k) :
    Xor (bigZ (X₁ ∩ Z)) (bigZ (X₂ ∩ Z)) := by
  have hc' := hc.inter hZ
  have hI : (X₁ ∩ Z) ∩ (X₂ ∩ Z) = X₁ ∩ X₂ ∩ Z := by
    ext v; simp only [Finset.mem_inter]; tauto
  have hx := hf.exactly_one _ _ hc' (by rw [hI]; exact hord)
  have h1 : (attIn G Z (X₁ ∩ Z)).card ≤ k :=
    (Finset.card_le_card hc'.attIn_subset_inter).trans (by rw [hI]; exact hord)
  have h2 : (attIn G Z (X₂ ∩ Z)).card ≤ k :=
    (Finset.card_le_card hc'.attIn_right_subset_inter).trans (by rw [hI]; exact hord)
  unfold Xor at hx ⊢
  rw [mem_avoid_iff G hc'.left_subset h1, mem_avoid_iff G hc'.right_subset h2] at hx
  tauto

/-- When the separator misses two branches and their connector, the two branches lie,
whole, on the same side: each is on one side (`sides`), and the connector cannot be
opposite to a branch it is adjacent to (`not_adj_of_opposite`). -/
theorem branches_same_side {C X₁ X₂ Z Z' Q : Finset V} (hc : ComplementaryIn G C X₁ X₂)
    (hZ : Z ⊆ C) (hZ' : Z' ⊆ C) (hQ : Q ⊆ C)
    (hconnZ : (G.induce (↑Z : Set V)).Connected) (hconnZ' : (G.induce (↑Z' : Set V)).Connected)
    (hconnQ : (G.induce (↑Q : Set V)).Connected)
    (hqZ : ∃ q ∈ Q, ∃ z ∈ Z, G.Adj q z) (hqZ' : ∃ q ∈ Q, ∃ z ∈ Z', G.Adj q z)
    (hIZ : Disjoint (X₁ ∩ X₂) Z) (hIZ' : Disjoint (X₁ ∩ X₂) Z') (hIQ : Disjoint (X₁ ∩ X₂) Q) :
    (Z ⊆ X₁ ∧ Disjoint Z X₂ ∧ Z' ⊆ X₁ ∧ Disjoint Z' X₂) ∨
      (Z ⊆ X₂ ∧ Disjoint Z X₁ ∧ Z' ⊆ X₂ ∧ Disjoint Z' X₁) := by
  obtain ⟨q, hq, z, hz, hqz⟩ := hqZ
  obtain ⟨q', hq', z', hz', hqz'⟩ := hqZ'
  rcases hc.sides hQ hconnQ hIQ with ⟨hQ₁, hQ₂⟩ | ⟨hQ₂, hQ₁⟩
  · -- the connector is on side 1, so both branches are
    have hZs : Z ⊆ X₁ ∧ Disjoint Z X₂ := by
      rcases hc.sides hZ hconnZ hIZ with h | ⟨_, h⟩
      · exact h
      · exact absurd (hc.not_adj_of_opposite hZ hQ₁ hQ₂ h hq hz hqz) id
    have hZ's : Z' ⊆ X₁ ∧ Disjoint Z' X₂ := by
      rcases hc.sides hZ' hconnZ' hIZ' with h | ⟨_, h⟩
      · exact h
      · exact absurd (hc.not_adj_of_opposite hZ' hQ₁ hQ₂ h hq' hz' hqz') id
    exact Or.inl ⟨hZs.1, hZs.2, hZ's.1, hZ's.2⟩
  · have hc' := hc.symm
    have hZs : Z ⊆ X₂ ∧ Disjoint Z X₁ := by
      rcases hc.sides hZ hconnZ hIZ with ⟨_, h⟩ | h
      · exact absurd (hc'.not_adj_of_opposite hZ hQ₂ hQ₁ h hq hz hqz) id
      · exact h
    have hZ's : Z' ⊆ X₂ ∧ Disjoint Z' X₁ := by
      rcases hc.sides hZ' hconnZ' hIZ' with ⟨_, h⟩ | h
      · exact absurd (hc'.not_adj_of_opposite hZ' hQ₂ hQ₁ h hq' hz' hqz') id
      · exact h
    exact Or.inr ⟨hZs.1, hZs.2, hZ's.1, hZ's.2⟩

/-- The full-branch case: the separator of order `≤ k + 1` has `k + 1` vertices in the
branch `Z`, so it lies inside `Z` and misses the other two branches `Z'`, `Z''` and their
connector; those two are then whole on one side, where they are big (`big_self`), and
absent from the other, where they are not (`not_big_empty`). -/
theorem exactly_one_of_full {C X₁ X₂ Z Z' Z'' : Finset V} (hc : ComplementaryIn G C X₁ X₂)
    {k : ℕ} (hcard : (X₁ ∩ X₂).card ≤ k + 1)
    (hZ' : Z' ⊆ C) (hZ'' : Z'' ⊆ C) (hdZ' : Disjoint Z Z') (hdZ'' : Disjoint Z Z'')
    (hconnZ' : (G.induce (↑Z' : Set V)).Connected) (hconnZ'' : (G.induce (↑Z'' : Set V)).Connected)
    (link : ∃ Q ⊆ C, Disjoint Q Z ∧ (G.induce (↑Q : Set V)).Connected ∧
      (∃ q ∈ Q, ∃ z ∈ Z', G.Adj q z) ∧ (∃ q ∈ Q, ∃ z ∈ Z'', G.Adj q z))
    {big' big'' : Finset V → Prop}
    (hf' : IsBlockageIn G Z' k (avoid G Z' k big'))
    (hf'' : IsBlockageIn G Z'' k (avoid G Z'' k big''))
    (hfull : k + 1 ≤ (X₁ ∩ X₂ ∩ Z).card) :
    (big' (X₁ ∩ Z') ∧ big'' (X₁ ∩ Z'') ∧ ¬ big' (X₂ ∩ Z') ∧ ¬ big'' (X₂ ∩ Z'')) ∨
      (big' (X₂ ∩ Z') ∧ big'' (X₂ ∩ Z'') ∧ ¬ big' (X₁ ∩ Z') ∧ ¬ big'' (X₁ ∩ Z'')) := by
  obtain ⟨Q, hQC, hQZ, hQconn, hqZ', hqZ''⟩ := link
  -- the separator lies inside `Z`
  have hIZ : X₁ ∩ X₂ ⊆ Z := by
    have heq : X₁ ∩ X₂ ∩ Z = X₁ ∩ X₂ :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    intro v hv
    rw [← heq] at hv
    exact (Finset.mem_inter.mp hv).2
  have hIZ' : Disjoint (X₁ ∩ X₂) Z' := hdZ'.mono_left hIZ
  have hIZ'' : Disjoint (X₁ ∩ X₂) Z'' := hdZ''.mono_left hIZ
  have hIQ : Disjoint (X₁ ∩ X₂) Q := hQZ.symm.mono_left hIZ
  have bZ' := hf'.big_self
  have bZ'' := hf''.big_self
  have nZ' := hf'.not_big_empty
  have nZ'' := hf''.not_big_empty
  rcases branches_same_side hc hZ' hZ'' hQC hconnZ' hconnZ'' hQconn hqZ' hqZ'' hIZ' hIZ'' hIQ with
    ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · rw [Finset.inter_eq_right.mpr h1, Finset.inter_eq_right.mpr h3,
      Finset.disjoint_iff_inter_eq_empty.mp h2.symm, Finset.disjoint_iff_inter_eq_empty.mp h4.symm]
    exact Or.inl ⟨bZ', bZ'', nZ', nZ''⟩
  · rw [Finset.inter_eq_right.mpr h1, Finset.inter_eq_right.mpr h3,
      Finset.disjoint_iff_inter_eq_empty.mp h2.symm, Finset.disjoint_iff_inter_eq_empty.mp h4.symm]
    exact Or.inr ⟨bZ', bZ'', nZ', nZ''⟩

variable (G) in
/-- **The branch operator.** Frames of order `k` on three linked branches give a blockage
of order `k + 1` on `C`: a set is big when at least two of its branch parts are big. -/
theorem isBlockageIn_branch {C A B D : Finset V} (hb : BranchIn G C A B D) {k : ℕ}
    {bigA bigB bigD : Finset V → Prop}
    (hmA : Upward bigA) (hmB : Upward bigB) (hmD : Upward bigD)
    (hfA : IsBlockageIn G A k (avoid G A k bigA)) (hfB : IsBlockageIn G B k (avoid G B k bigB))
    (hfD : IsBlockageIn G D k (avoid G D k bigD)) :
    IsBlockageIn G C (k + 1) (avoid G C (k + 1) (twoOf bigA bigB bigD A B D)) where
  subset_of_mem X hX := hX.1
  att_card_le X hX := hX.2.1
  mem_of_subset X hX Y hYX hY :=
    ⟨hYX.trans hX.1, hY, fun h => hX.2.2 (twoOf_upward hmA hmB hmD A B D hYX h)⟩
  exactly_one X₁ X₂ hc hcard := by
    have h1 : (attIn G C X₁).card ≤ k + 1 :=
      (Finset.card_le_card hc.attIn_subset_inter).trans hcard
    have h2 : (attIn G C X₂).card ≤ k + 1 :=
      (Finset.card_le_card hc.attIn_right_subset_inter).trans hcard
    unfold Xor
    rw [mem_avoid_iff G hc.left_subset h1, mem_avoid_iff G hc.right_subset h2]
    -- the three shares of the separator are disjoint
    have hsum : (X₁ ∩ X₂ ∩ A).card + (X₁ ∩ X₂ ∩ B).card + (X₁ ∩ X₂ ∩ D).card ≤ k + 1 := by
      have dAB : Disjoint (X₁ ∩ X₂ ∩ A) (X₁ ∩ X₂ ∩ B) :=
        hb.disjAB.mono Finset.inter_subset_right Finset.inter_subset_right
      have dABD : Disjoint (X₁ ∩ X₂ ∩ A ∪ X₁ ∩ X₂ ∩ B) (X₁ ∩ X₂ ∩ D) :=
        Finset.disjoint_union_left.mpr
          ⟨hb.disjAD.mono Finset.inter_subset_right Finset.inter_subset_right,
           hb.disjBD.mono Finset.inter_subset_right Finset.inter_subset_right⟩
      have hsub : X₁ ∩ X₂ ∩ A ∪ X₁ ∩ X₂ ∩ B ∪ X₁ ∩ X₂ ∩ D ⊆ X₁ ∩ X₂ :=
        Finset.union_subset (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
          Finset.inter_subset_left
      have := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint dABD, Finset.card_union_of_disjoint dAB] at this
      omega
    by_cases hA : (X₁ ∩ X₂ ∩ A).card ≤ k <;> by_cases hB : (X₁ ∩ X₂ ∩ B).card ≤ k <;>
      by_cases hD : (X₁ ∩ X₂ ∩ D).card ≤ k
    · -- every branch sees a separator of order `≤ k`
      have xA := branch_xor hb.subA hfA hc hA
      have xB := branch_xor hb.subB hfB hc hB
      have xD := branch_xor hb.subD hfD hc hD
      unfold Xor at xA xB xD
      rcases xA with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases xB with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
        rcases xD with ⟨d1, d2⟩ | ⟨d1, d2⟩ <;> simp [twoOf, a1, a2, b1, b2, d1, d2]
    · -- `D` holds the whole separator
      have := exactly_one_of_full hc hcard hb.subA hb.subB hb.disjAD.symm hb.disjBD.symm
        hb.connA hb.connB hb.linkAB hfA hfB (by omega)
      rcases this with ⟨p1, p2, p3, p4⟩ | ⟨p1, p2, p3, p4⟩ <;> simp [twoOf, p1, p2, p3, p4]
    · -- `B` holds the whole separator
      have := exactly_one_of_full hc hcard hb.subA hb.subD hb.disjAB.symm hb.disjBD
        hb.connA hb.connD hb.linkAD hfA hfD (by omega)
      rcases this with ⟨p1, p2, p3, p4⟩ | ⟨p1, p2, p3, p4⟩ <;> simp [twoOf, p1, p2, p3, p4]
    · omega
    · -- `A` holds the whole separator
      have := exactly_one_of_full hc hcard hb.subB hb.subD hb.disjAB hb.disjAD
        hb.connB hb.connD hb.linkBD hfB hfD (by omega)
      rcases this with ⟨p1, p2, p3, p4⟩ | ⟨p1, p2, p3, p4⟩ <;> simp [twoOf, p1, p2, p3, p4]
    · omega
    · omega
    · omega

variable (G) in
/-- The branch frame. -/
def Frame.branch {C A B D : Finset V} (hb : BranchIn G C A B D) {k : ℕ}
    (FA : Frame G A k) (FB : Frame G B k) (FD : Frame G D k) : Frame G C (k + 1) where
  big := twoOf FA.big FB.big FD.big A B D
  upward := twoOf_upward FA.upward FB.upward FD.upward A B D
  blockage := isBlockageIn_branch G hb FA.upward FB.upward FD.upward
    FA.blockage FB.blockage FD.blockage

/-! ### The cut-vertex form -/

variable (G) in
theorem connected_induce_singleton (v : V) :
    (G.induce (↑({v} : Finset V) : Set V)).Connected := by
  have hmem : v ∈ (↑({v} : Finset V) : Set V) := by simp
  haveI : Nonempty (↑({v} : Finset V) : Set V) := ⟨⟨v, hmem⟩⟩
  refine ⟨fun a b => ?_⟩
  have ha : a.1 = v := by simpa using a.2
  have hb : b.1 = v := by simpa using b.2
  have : a = b := Subtype.ext (ha.trans hb.symm)
  subst this
  exact SimpleGraph.Reachable.refl _

variable (G) in
/-- A vertex `v ∈ C` outside three disjoint connected branches and adjacent to each is a
connector for every pair: Fellows & Langston's cut-vertex form. -/
theorem BranchIn.of_hub {C A B D : Finset V} (v : V) (hvC : v ∈ C)
    (hA : A ⊆ C) (hB : B ⊆ C) (hD : D ⊆ C) (hvA : v ∉ A) (hvB : v ∉ B) (hvD : v ∉ D)
    (hAB : Disjoint A B) (hAD : Disjoint A D) (hBD : Disjoint B D)
    (hconnA : (G.induce (↑A : Set V)).Connected) (hconnB : (G.induce (↑B : Set V)).Connected)
    (hconnD : (G.induce (↑D : Set V)).Connected)
    (hadjA : ∃ a ∈ A, G.Adj v a) (hadjB : ∃ b ∈ B, G.Adj v b) (hadjD : ∃ d ∈ D, G.Adj v d) :
    BranchIn G C A B D where
  subA := hA
  subB := hB
  subD := hD
  disjAB := hAB
  disjAD := hAD
  disjBD := hBD
  connA := hconnA
  connB := hconnB
  connD := hconnD
  linkAB := ⟨{v}, Finset.singleton_subset_iff.mpr hvC, Finset.disjoint_singleton_left.mpr hvD,
    connected_induce_singleton G v, ⟨v, Finset.mem_singleton_self v, hadjA⟩,
    ⟨v, Finset.mem_singleton_self v, hadjB⟩⟩
  linkAD := ⟨{v}, Finset.singleton_subset_iff.mpr hvC, Finset.disjoint_singleton_left.mpr hvB,
    connected_induce_singleton G v, ⟨v, Finset.mem_singleton_self v, hadjA⟩,
    ⟨v, Finset.mem_singleton_self v, hadjD⟩⟩
  linkBD := ⟨{v}, Finset.singleton_subset_iff.mpr hvC, Finset.disjoint_singleton_left.mpr hvA,
    connected_induce_singleton G v, ⟨v, Finset.mem_singleton_self v, hadjB⟩,
    ⟨v, Finset.mem_singleton_self v, hadjD⟩⟩

/-! ### The certificate theorems, spelled out -/

variable (G) in
/-- A clique of `n + 1` vertices forces pathwidth `≥ n` (the clique frame on `univ`). -/
theorem pathwidth_ge_of_clique_frame {K : Finset V} (hK : G.IsClique (↑K : Set V)) {n : ℕ}
    (hn : n + 1 ≤ K.card) : n ≤ pathwidth G :=
  (Frame.clique G (Finset.subset_univ K) hK hn).pathwidth_ge

variable (G) in
/-- Three linked branches carrying frames of order `k` force pathwidth `≥ k + 1`. -/
theorem pathwidth_ge_of_branch_frames {A B D : Finset V} (hb : BranchIn G Finset.univ A B D)
    {k : ℕ} (FA : Frame G A k) (FB : Frame G B k) (FD : Frame G D k) : k + 1 ≤ pathwidth G :=
  (Frame.branch G hb FA FB FD).pathwidth_ge

end Blockage

end MOSPFormalization

#print axioms MOSPFormalization.Blockage.Frame.pathwidth_ge
#print axioms MOSPFormalization.Blockage.isBlockageIn_clique
#print axioms MOSPFormalization.Blockage.isBlockageIn_minor
#print axioms MOSPFormalization.Blockage.isBlockageIn_branch
#print axioms MOSPFormalization.Blockage.pathwidth_ge_of_branch_frames
