/-
Copyright (c) 2026 Alexandre Linhares. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Blockages: the weak half of Bienstock, Robertson, Seymour & Thomas (1991), Theorem (2.1)

`literature/1991-Bienstock-Robertson-Seymour-Thomas-Quickly-Excluding-Forest-JCTB.pdf`,
Section 2. For `X ⊆ V`, `att X` is the set of vertices of `X` with a neighbour outside `X`
("attachments"), `α(X) = |att X|`. Two sets are *complementary* when `X₁ ∪ X₂ = V` and
`att X₁ ⊆ X₂` (a separation). A *blockage of order `n`* is a set `𝓑` of subsets of `V` with

* (i)   every `X ∈ 𝓑` has `α(X) ≤ n`;
* (ii)  `X ∈ 𝓑`, `Y ⊆ X`, `α(Y) ≤ n` imply `Y ∈ 𝓑`;
* (iii) for complementary `X₁, X₂` with `|X₁ ∩ X₂| ≤ n`, `𝓑` contains exactly one of them.

Theorem (2.1) says a blockage of order `n` exists iff the pathwidth is at least `n`. This
file proves the half the paper calls easy (`pathwidth_ge_of_isBlockage`): **a blockage of
order `n` forces `pathwidth G ≥ n`**, by the paper's own argument — Lemma (2.2)
(`IsBlockage.mem_of_mem`), `∅ ∈ 𝓑` and `V ∉ 𝓑` from the complementary pair `(∅, V)`, and
the prefix unions `X_i = W_0 ∪ ⋯ ∪ W_{i-1}` of a path decomposition of width `< n` climbing
from `∅` to `V` inside `𝓑` one bag at a time: `att X_i ⊆ W_i`, `X_{i+1} ∖ X_i ⊆ W_i`, so
both premises of (2.2) are bounded by `|W_i| ≤ n`. The converse (a blockage from
`pathwidth ≥ n`, via partial blockages and fractures, (2.3)–(2.5)) is not attempted.

The paper's pathwidth is `max |W_i| − 1`, as here (`PathDecomposition.width`); the paper
allows loops and multiple edges, which change nothing in Section 2, and the graphs here are
simple. Every statement was checked by brute force before it was written
(`reports/scratch/minor_tabu_lean/check_blockage.py`: both halves of (2.1) by exhaustive
enumeration of set families on every graph to 4 vertices, and the proof's set facts on
every layout of every graph to 7 vertices; zero violations).
-/

import MOSPFormalization.Minor

set_option linter.unusedSectionVars false

namespace MOSPFormalization

namespace Blockage

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The attachments of `X`: its vertices with a neighbour outside `X`. -/
def att (X : Finset V) : Finset V := X.filter fun v => ∃ u, u ∉ X ∧ G.Adj v u

theorem mem_att {X : Finset V} {v : V} : v ∈ att G X ↔ v ∈ X ∧ ∃ u, u ∉ X ∧ G.Adj v u := by
  simp [att]

theorem att_subset (X : Finset V) : att G X ⊆ X := Finset.filter_subset _ _

@[simp] theorem att_empty : att G (∅ : Finset V) = ∅ := by
  ext v; simp [mem_att]

/-- `X^c = (V ∖ X) ∪ att X`, the paper's complement. -/
def compl (X : Finset V) : Finset V := (Finset.univ \ X) ∪ att G X

/-- Complementary sets: a separation. -/
def Complementary (X₁ X₂ : Finset V) : Prop := X₁ ∪ X₂ = Finset.univ ∧ att G X₁ ⊆ X₂

/-- The blockage axioms (i)–(iii). -/
structure IsBlockage (n : ℕ) (B : Set (Finset V)) : Prop where
  att_card_le : ∀ X ∈ B, (att G X).card ≤ n
  mem_of_subset : ∀ X ∈ B, ∀ Y ⊆ X, (att G Y).card ≤ n → Y ∈ B
  exactly_one : ∀ X₁ X₂, Complementary G X₁ X₂ → (X₁ ∩ X₂).card ≤ n → Xor (X₁ ∈ B) (X₂ ∈ B)

theorem complementary_compl (X : Finset V) : Complementary G X (compl G X) := by
  refine ⟨?_, Finset.subset_union_right⟩
  ext v
  simp only [compl, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and,
    iff_true]
  tauto

theorem inter_compl (X : Finset V) : X ∩ compl G X = att G X := by
  ext v
  simp only [compl, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨hX, h | h⟩
    · exact absurd hX h
    · exact h
  · intro h
    exact ⟨att_subset G X h, Or.inr h⟩

/-- `(X ∪ Y, X^c)` is complementary. -/
theorem complementary_union_compl (X Y : Finset V) : Complementary G (X ∪ Y) (compl G X) := by
  refine ⟨?_, ?_⟩
  · ext v
    simp only [compl, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and,
      iff_true]
    tauto
  · intro v hv
    rw [mem_att] at hv
    obtain ⟨hvXY, u, hu, hadj⟩ := hv
    simp only [compl, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
    by_cases hvX : v ∈ X
    · exact Or.inr ((mem_att G).mpr ⟨hvX, u, fun h => hu (Finset.mem_union_left _ h), hadj⟩)
    · exact Or.inl hvX

theorem union_inter_compl (X Y : Finset V) : (X ∪ Y) ∩ compl G X = (Y \ X) ∪ att G X := by
  ext v
  simp only [compl, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ,
    true_and]
  have hs : v ∈ att G X → v ∈ X := fun h => att_subset G X h
  tauto

variable {G}

/-- **Lemma (2.2).** `X ∈ 𝓑`, `α(Y) ≤ n` and `|(Y ∖ X) ∪ att X| ≤ n` give `Y ∈ 𝓑`. -/
theorem IsBlockage.mem_of_mem {n : ℕ} {B : Set (Finset V)} (hB : IsBlockage G n B)
    {X Y : Finset V} (hX : X ∈ B) (hY : (att G Y).card ≤ n)
    (h : ((Y \ X) ∪ att G X).card ≤ n) : Y ∈ B := by
  -- `X^c ∉ 𝓑`, by (iii) on `(X, X^c)`
  have h1 := hB.exactly_one X (compl G X) (complementary_compl G X)
    (by rw [inter_compl]; exact hB.att_card_le X hX)
  have hXc : compl G X ∉ B := fun hc => by
    rcases h1 with ⟨_, h⟩ | ⟨_, h⟩
    · exact h hc
    · exact h hX
  -- `X ∪ Y ∈ 𝓑`, by (iii) on `(X ∪ Y, X^c)`
  have h2 := hB.exactly_one (X ∪ Y) (compl G X) (complementary_union_compl G X Y)
    (by rw [union_inter_compl]; exact h)
  have hXY : X ∪ Y ∈ B := by
    rcases h2 with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h hXc
  exact hB.mem_of_subset _ hXY Y Finset.subset_union_right hY

/-- `∅ ∈ 𝓑` and `V ∉ 𝓑`: the pair `(∅, V)` is complementary with empty intersection, and
`V ∈ 𝓑` would put `∅` in too by (ii). -/
theorem IsBlockage.empty_mem_and_univ_not_mem {n : ℕ} {B : Set (Finset V)}
    (hB : IsBlockage G n B) : (∅ : Finset V) ∈ B ∧ (Finset.univ : Finset V) ∉ B := by
  have h := hB.exactly_one ∅ Finset.univ ⟨by simp, by simp⟩ (by simp)
  rcases h with ⟨h0, hu⟩ | ⟨hu, h0⟩
  · exact ⟨h0, hu⟩
  · exact absurd (hB.mem_of_subset _ hu ∅ (Finset.empty_subset _) (by simp)) h0

/-! ### Prefix unions of a path decomposition -/

section Prefix

variable (P : PathDecomposition G)

/-- The union of the first `i` bags, `W_0 ∪ ⋯ ∪ W_{i-1}`. -/
def prefixUnion (i : ℕ) : Finset V :=
  (Finset.univ.filter fun j : Fin (P.length + 1) => j.val < i).biUnion P.bag

theorem mem_prefixUnion {i : ℕ} {v : V} :
    v ∈ prefixUnion P i ↔ ∃ j : Fin (P.length + 1), j.val < i ∧ v ∈ P.bag j := by
  simp [prefixUnion]

@[simp] theorem prefixUnion_zero : prefixUnion P 0 = ∅ := by
  ext v; simp [mem_prefixUnion]

theorem prefixUnion_last : prefixUnion P (P.length + 1) = Finset.univ := by
  ext v
  simp only [mem_prefixUnion, Finset.mem_univ, iff_true]
  obtain ⟨j, hj⟩ := P.vertex_coverage v
  exact ⟨j, j.isLt, hj⟩

/-- A vertex of `X_i` with a neighbour outside `X_i` lies in `W_i` (interval property). -/
theorem att_prefixUnion_subset {i : ℕ} (hi : i ≤ P.length) :
    att G (prefixUnion P i) ⊆ P.bag ⟨i, by omega⟩ := by
  intro v hv
  rw [mem_att, mem_prefixUnion] at hv
  obtain ⟨⟨j, hji, hvj⟩, u, hu, hadj⟩ := hv
  obtain ⟨k, hvk, huk⟩ := P.edge_coverage v u hadj
  have hik : i ≤ k.val := by
    by_contra hlt
    exact hu ((mem_prefixUnion P).mpr ⟨k, by omega, huk⟩)
  exact P.interval v j ⟨i, by omega⟩ k (by show j.val ≤ i; omega) (by show i ≤ k.val; omega)
    hvj hvk

/-- A vertex of `X_{i+1}` with a neighbour outside `X_{i+1}` lies in `W_i`. -/
theorem att_prefixUnion_succ_subset {i : ℕ} (hi : i ≤ P.length) :
    att G (prefixUnion P (i + 1)) ⊆ P.bag ⟨i, by omega⟩ := by
  intro v hv
  rw [mem_att, mem_prefixUnion] at hv
  obtain ⟨⟨j, hji, hvj⟩, u, hu, hadj⟩ := hv
  obtain ⟨k, hvk, huk⟩ := P.edge_coverage v u hadj
  have hik : i + 1 ≤ k.val := by
    by_contra hlt
    exact hu ((mem_prefixUnion P).mpr ⟨k, by omega, huk⟩)
  exact P.interval v j ⟨i, by omega⟩ k (by show j.val ≤ i; omega) (by show i ≤ k.val; omega)
    hvj hvk

/-- `X_{i+1} ∖ X_i ⊆ W_i`. -/
theorem prefixUnion_succ_sdiff_subset {i : ℕ} (hi : i ≤ P.length) :
    prefixUnion P (i + 1) \ prefixUnion P i ⊆ P.bag ⟨i, by omega⟩ := by
  intro v hv
  rw [Finset.mem_sdiff, mem_prefixUnion, mem_prefixUnion] at hv
  obtain ⟨⟨j, hji, hvj⟩, hnot⟩ := hv
  have hj : j.val = i := by
    by_contra hne
    exact hnot ⟨j, by omega, hvj⟩
  have : j = ⟨i, by omega⟩ := Fin.ext hj
  exact this ▸ hvj

end Prefix

/-! ### The theorem -/

/-- **A blockage of order `n` forces pathwidth `≥ n`** (the easy half of (2.1)). Along any
path decomposition of width `< n` the prefix unions would climb from `∅ ∈ 𝓑` to `V ∉ 𝓑`
inside `𝓑`, by Lemma (2.2) at every bag. -/
theorem pathwidth_ge_of_isBlockage {n : ℕ} {B : Set (Finset V)} (hB : IsBlockage G n B) :
    n ≤ pathwidth G := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨P, hP⟩ := exists_pathDecomposition_width_eq G
  have hbag : ∀ i : Fin (P.length + 1), (P.bag i).card ≤ n := fun i => by
    have := P.bag_card_le_width_add_one i
    omega
  obtain ⟨h0, hu⟩ := hB.empty_mem_and_univ_not_mem
  have climb : ∀ i, i ≤ P.length + 1 → prefixUnion P i ∈ B := by
    intro i
    induction i with
    | zero => intro _; simpa using h0
    | succ i ih =>
      intro hi
      have hi' : i ≤ P.length := by omega
      refine hB.mem_of_mem (ih (by omega)) ?_ ?_
      · exact (Finset.card_le_card (att_prefixUnion_succ_subset P hi')).trans (hbag _)
      · refine (Finset.card_le_card ?_).trans (hbag ⟨i, by omega⟩)
        exact Finset.union_subset (prefixUnion_succ_sdiff_subset P hi')
          (att_prefixUnion_subset P hi')
  have := climb (P.length + 1) le_rfl
  rw [prefixUnion_last] at this
  exact hu this

end Blockage

end MOSPFormalization
