/-
Copyright (c) 2026 Alexandre Linhares. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# The first moment of narrow layouts: symmetry and independence

`reports/layout_second_moment.md`.  `X_w(G)` is the number of linear layouts of
`G` with vertex separation at most `w`.  Over `G(n, p)` (the weights `gnpWeight`
of `FirstMoment.lean`) its expectation is `n!` times the probability that one fixed
layout is narrow, because relabelling the vertices carries any layout to any other
and preserves the weight.  That probability is, on paper, the value of the
open-count chain (`learning/layout_moment.py`, checked exactly against every
labelled graph to 10 vertices); its derivation uses one probabilistic fact about
`G(n, p)`, that the edges at a fixed set of pairs are independent of any event
determined by the other pairs.  Both are here:

* `layoutRelabel σ τ : V ≃ V` and the transport lemmas `prefixSet_relabel`,
  `activeSuffix_comap_relabel`, `vertexSepOfLayout_comap_relabel`: pulling `G`
  back along the relabelling turns the layout `σ` into `τ` with the same vertex
  separation at every position; `card_edges_comap`, `gnpWeight_comap`: the weight
  is preserved.
* `narrowWeight p σ w = ∑_G gnpWeight p G · 1[vs(G, σ) ≤ w]` is the same number for
  every layout (`narrowWeight_eq`), and
  **`expected_narrowLayouts`**: `∑_G gnpWeight p G · X_w(G) = n! · narrowWeight p σ₀ w`.
* **The independence lemma** `sum_gnpWeight_pattern`: for a set `F` of pairs and a
  finset `E` of graphs determined outside `F` (`DeterminedOutside E F`), the
  weight of the graphs of `E` whose edges inside `F` are exactly `Fp ⊆ F` is
  `p^|Fp| (1 − p)^(|F| − |Fp|)` times the weight of `E`.  This is the step the chain
  takes at every position: the edges from the vertex just placed to the suffix are
  fresh.  `sum_gnpWeight_emptyPairGraphs` of `FirstMoment.lean` is the case
  `E = univ`, `Fp = ∅`.
* `chainQ n p w`, the chain's value as a finite recursion, and `ChainIdentity`, the
  statement `narrowWeight p σ w = chainQ |V| p w` — **stated, not proved**: the
  proof on paper conditions on the opening times of the suffix vertices and uses
  their exchangeability; the finite-sum formalisation of that argument is more
  than a day's work and is left as the open item of the report.

No `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound` only.
-/

import MOSPFormalization.FirstMoment
import MOSPFormalization.VertexSeparation
import Mathlib.Data.Fintype.Perm

set_option linter.unusedSectionVars false

namespace MOSPFormalization

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Transport of a layout along a relabelling -/

/-- The relabelling that sends the vertex at `σ`-position `i` to the vertex at
`τ`-position `i`: `τ (layoutRelabel σ τ v) = σ v`. -/
def layoutRelabel (σ τ : LinearLayout V) : V ≃ V := σ.trans τ.symm

@[simp] theorem layoutRelabel_apply (σ τ : LinearLayout V) (v : V) : τ (layoutRelabel σ τ v) = σ v := by
  simp [layoutRelabel]

@[simp] theorem relabel_symm_apply (σ τ : LinearLayout V) (v : V) :
    σ ((layoutRelabel σ τ).symm v) = τ v := by
  simp [layoutRelabel]

theorem prefixSet_relabel (σ τ : LinearLayout V) (i : ℕ) :
    prefixSet τ i = (prefixSet σ i).map (layoutRelabel σ τ).toEmbedding := by
  ext v
  rw [mem_map_equiv, mem_prefixSet_iff, mem_prefixSet_iff, relabel_symm_apply]

theorem activeSuffix_comap_relabel (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ τ : LinearLayout V) (i : ℕ) [DecidableRel (G.comap (layoutRelabel σ τ).symm).Adj] :
    activeSuffix (G.comap (layoutRelabel σ τ).symm) τ i =
      (activeSuffix G σ i).map (layoutRelabel σ τ).toEmbedding := by
  ext v
  rw [mem_map_equiv, mem_activeSuffix_iff, mem_activeSuffix_iff, prefixSet_relabel σ τ,
    relabel_symm_apply]
  constructor
  · rintro ⟨hv, u, hu, hadj⟩
    rw [mem_map_equiv] at hu
    exact ⟨hv, (layoutRelabel σ τ).symm u, hu, hadj⟩
  · rintro ⟨hv, u, hu, hadj⟩
    refine ⟨hv, layoutRelabel σ τ u, ?_, ?_⟩
    · rw [mem_map_equiv, Equiv.symm_apply_apply]
      exact hu
    · rw [SimpleGraph.comap_adj, Equiv.symm_apply_apply]
      exact hadj

theorem vertexSepAt_comap_relabel (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ τ : LinearLayout V) (i : ℕ) [DecidableRel (G.comap (layoutRelabel σ τ).symm).Adj] :
    vertexSepAt (G.comap (layoutRelabel σ τ).symm) τ i = vertexSepAt G σ i := by
  unfold vertexSepAt
  rw [activeSuffix_comap_relabel, card_map]

/-- Pulling `G` back along `layoutRelabel σ τ` turns the layout `σ` into the layout `τ`:
the vertex separation is the same. -/
theorem vertexSepOfLayout_comap_relabel (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ τ : LinearLayout V) [DecidableRel (G.comap (layoutRelabel σ τ).symm).Adj] :
    vertexSepOfLayout (G.comap (layoutRelabel σ τ).symm) τ = vertexSepOfLayout G σ := by
  unfold vertexSepOfLayout
  split_ifs with h
  · rfl
  · exact sup'_congr _ rfl (fun (i : Fin (Fintype.card V)) _ => vertexSepAt_comap_relabel G σ τ i.val)

/-! ### The weight is preserved -/

/-- `Sym2.map` of a bijection, as a bijection of `Sym2 V`. -/
def sym2Equiv (φ : V ≃ V) : Sym2 V ≃ Sym2 V where
  toFun := Sym2.map φ
  invFun := Sym2.map φ.symm
  left_inv e := by induction e using Sym2.ind; simp
  right_inv e := by induction e using Sym2.ind; simp

theorem mem_edges_comap (G : SimpleGraph V) (φ : V ≃ V) (e : Sym2 V) :
    e ∈ edges (G.comap φ.symm) ↔ Sym2.map φ.symm e ∈ edges G := by
  induction e using Sym2.ind with
  | h u v => simp [mem_edges, SimpleGraph.mem_edgeSet]

theorem edges_comap (G : SimpleGraph V) (φ : V ≃ V) :
    edges (G.comap φ.symm) = (edges G).map (sym2Equiv φ).toEmbedding := by
  ext e
  rw [mem_map_equiv, mem_edges_comap]
  rfl

theorem card_edges_comap (G : SimpleGraph V) (φ : V ≃ V) :
    (edges (G.comap φ.symm)).card = (edges G).card := by
  rw [edges_comap, card_map]

theorem gnpWeight_comap (p : ℝ) (G : SimpleGraph V) (φ : V ≃ V) :
    gnpWeight p (G.comap φ.symm) = gnpWeight p G := by
  unfold gnpWeight
  rw [card_edges_comap]

/-- Pulling back along a bijection is a bijection of the graphs on `V`. -/
def comapEquiv (φ : V ≃ V) : SimpleGraph V ≃ SimpleGraph V where
  toFun G := G.comap φ.symm
  invFun G := G.comap φ
  left_inv G := by ext u v; simp
  right_inv G := by ext u v; simp

@[simp] theorem comapEquiv_apply (φ : V ≃ V) (G : SimpleGraph V) :
    comapEquiv φ G = G.comap φ.symm := rfl

/-! ### The symmetry: every layout is narrow with the same probability -/

open scoped Classical in
/-- `∑_G gnpWeight p G · 1[vertexSepOfLayout G σ ≤ w]`: the `G(n, p)` probability that the
fixed layout `σ` has vertex separation at most `w`. -/
noncomputable def narrowWeight (p : ℝ) (σ : LinearLayout V) (w : ℕ) : ℝ :=
  ∑ G : SimpleGraph V, if vertexSepOfLayout G σ ≤ w then gnpWeight p G else 0

open scoped Classical in
theorem narrowWeight_eq (p : ℝ) (σ τ : LinearLayout V) (w : ℕ) :
    narrowWeight p σ w = narrowWeight p τ w := by
  unfold narrowWeight
  refine Fintype.sum_equiv (comapEquiv (layoutRelabel σ τ)) _ _ (fun G => ?_)
  rw [comapEquiv_apply, vertexSepOfLayout_comap_relabel, gnpWeight_comap]

open scoped Classical in
/-- The layouts of `G` with vertex separation at most `w`. -/
noncomputable def narrowLayouts (G : SimpleGraph V) (w : ℕ) : Finset (LinearLayout V) :=
  univ.filter (fun σ => vertexSepOfLayout G σ ≤ w)

open scoped Classical in
/-- **The expected number of narrow layouts is `n!` times the probability that one fixed
layout is narrow**: `∑_G gnpWeight p G · X_w(G) = |V|! · narrowWeight p σ₀ w` for every
layout `σ₀`. -/
theorem expected_narrowLayouts (p : ℝ) (w : ℕ) (σ₀ : LinearLayout V) :
    ∑ G : SimpleGraph V, gnpWeight p G * ((narrowLayouts G w).card : ℝ) =
      ((Fintype.card V).factorial : ℝ) * narrowWeight p σ₀ w := by
  have hcard : ∀ G : SimpleGraph V, ((narrowLayouts G w).card : ℝ) =
      ∑ σ : LinearLayout V, if vertexSepOfLayout G σ ≤ w then (1 : ℝ) else 0 := by
    intro G
    unfold narrowLayouts
    rw [card_filter]
    push_cast
    rfl
  calc ∑ G : SimpleGraph V, gnpWeight p G * ((narrowLayouts G w).card : ℝ)
      = ∑ G : SimpleGraph V, ∑ σ : LinearLayout V,
          (if vertexSepOfLayout G σ ≤ w then gnpWeight p G else 0) := by
        refine sum_congr rfl (fun G _ => ?_)
        rw [hcard, mul_sum]
        refine sum_congr rfl (fun σ _ => ?_)
        split_ifs <;> simp
    _ = ∑ σ : LinearLayout V, narrowWeight p σ w := by
        rw [sum_comm]
        rfl
    _ = ∑ _σ : LinearLayout V, narrowWeight p σ₀ w :=
        sum_congr rfl (fun σ _ => narrowWeight_eq p σ σ₀ w)
    _ = _ := by
        rw [sum_const, card_univ, Fintype.card_equiv (Fintype.equivFin V), nsmul_eq_mul]

/-! ### The independence lemma -/

/-- `E` is determined outside `F`: two graphs with the same edges outside `F` are both in
`E` or both not. -/
def DeterminedOutside (E : Finset (SimpleGraph V)) (F : Finset (Sym2 V)) : Prop :=
  ∀ G H : SimpleGraph V, edges G \ F = edges H \ F → (G ∈ E ↔ H ∈ E)

/-- The graphs of `E` whose edges inside `F` are exactly `Fp`. -/
noncomputable def patternGraphs (E : Finset (SimpleGraph V)) (F Fp : Finset (Sym2 V)) :
    Finset (SimpleGraph V) := by
  classical exact E.filter (fun G => edges G ∩ F = Fp)

theorem mem_patternGraphs {E : Finset (SimpleGraph V)} {F Fp : Finset (Sym2 V)}
    {G : SimpleGraph V} : G ∈ patternGraphs E F Fp ↔ G ∈ E ∧ edges G ∩ F = Fp := by
  simp [patternGraphs]

open scoped Classical in
/-- The edge sets outside `F` whose graph lies in `E`. -/
noncomputable def freeCore (E : Finset (SimpleGraph V)) (F : Finset (Sym2 V)) :
    Finset (Finset (Sym2 V)) :=
  (edges (⊤ : SimpleGraph V) \ F).powerset.filter
    (fun S => SimpleGraph.fromEdgeSet (S : Set (Sym2 V)) ∈ E)

theorem mem_freeCore {E : Finset (SimpleGraph V)} {F S : Finset (Sym2 V)} :
    S ∈ freeCore E F ↔
      S ⊆ edges (⊤ : SimpleGraph V) \ F ∧ SimpleGraph.fromEdgeSet (S : Set (Sym2 V)) ∈ E := by
  simp [freeCore]

theorem fromEdgeSet_edges (G : SimpleGraph V) :
    SimpleGraph.fromEdgeSet ((edges G : Finset (Sym2 V)) : Set (Sym2 V)) = G := by
  ext u v
  rw [SimpleGraph.fromEdgeSet_adj, mem_coe, mem_edges, SimpleGraph.mem_edgeSet]
  exact ⟨fun h => h.1, fun h => ⟨h, G.ne_of_adj h⟩⟩

/-- The bookkeeping of a free edge set `S ⊆ edges ⊤ \ F` and `H ⊆ F ⊆ edges ⊤`. -/
theorem free_union_facts {F S H : Finset (Sym2 V)} (hF : F ⊆ edges (⊤ : SimpleGraph V))
    (hS : S ⊆ edges (⊤ : SimpleGraph V) \ F) (hH : H ⊆ F) :
    S ∪ H ⊆ edges (⊤ : SimpleGraph V) ∧ (S ∪ H) \ F = S ∧ (S ∪ H) ∩ F = H := by
  have hdisj : Disjoint S F := disjoint_of_subset_left hS sdiff_disjoint
  refine ⟨union_subset (hS.trans sdiff_subset) (hH.trans hF), ?_, ?_⟩
  · rw [union_sdiff_distrib, Finset.sdiff_eq_self_iff_disjoint.2 hdisj, sdiff_eq_empty_iff_subset.2 hH,
      union_empty]
  · rw [union_inter_distrib_right, disjoint_iff_inter_eq_empty.1 hdisj, inter_eq_left.2 hH,
      empty_union]

/-- The free part of a graph of `E` is in the core. -/
theorem sdiff_mem_freeCore {E : Finset (SimpleGraph V)} {F : Finset (Sym2 V)}
    (hE : DeterminedOutside E F) {G : SimpleGraph V} (hG : G ∈ E) :
    edges G \ F ∈ freeCore E F := by
  have hsub : edges G \ F ⊆ edges (⊤ : SimpleGraph V) \ F :=
    sdiff_subset_sdiff (edges_subset_top G) le_rfl
  refine mem_freeCore.2 ⟨hsub, (hE _ G ?_).2 hG⟩
  rw [edges_fromEdgeSet _ (hsub.trans sdiff_subset), Finset.sdiff_idem]

theorem fromEdgeSet_union_mem {E : Finset (SimpleGraph V)} {F : Finset (Sym2 V)}
    (hF : F ⊆ edges (⊤ : SimpleGraph V)) (hE : DeterminedOutside E F)
    {S H : Finset (Sym2 V)} (hS : S ∈ freeCore E F) (hH : H ⊆ F) :
    SimpleGraph.fromEdgeSet ((S ∪ H : Finset (Sym2 V)) : Set (Sym2 V)) ∈ E := by
  obtain ⟨hS', hSE⟩ := mem_freeCore.1 hS
  obtain ⟨hsub, hsd, _⟩ := free_union_facts hF hS' hH
  refine (hE _ _ ?_).1 hSE
  rw [edges_fromEdgeSet _ hsub, edges_fromEdgeSet _ (hS'.trans sdiff_subset), hsd,
    Finset.sdiff_eq_self_iff_disjoint.2 (disjoint_of_subset_left hS' sdiff_disjoint)]

/-- The weight of an edge set, `p^|S| (1 − p)^(C − |S|)`. -/
noncomputable def edgeWeight (p : ℝ) (S : Finset (Sym2 V)) : ℝ :=
  p ^ S.card * (1 - p) ^ ((Fintype.card V).choose 2 - S.card)

theorem gnpWeight_eq_edgeWeight (p : ℝ) (G : SimpleGraph V) :
    gnpWeight p G = edgeWeight p (edges G) := rfl

theorem card_free_le {F S : Finset (Sym2 V)} (hF : F ⊆ edges (⊤ : SimpleGraph V))
    (hS : S ⊆ edges (⊤ : SimpleGraph V) \ F) :
    S.card + F.card ≤ (Fintype.card V).choose 2 := by
  have h := card_le_card hS
  rw [card_sdiff_of_subset hF, card_edges_top] at h
  have h2 := card_le_card hF
  rw [card_edges_top] at h2
  omega

/-- The weight of the pattern-side graphs of `E`, through the core. -/
theorem sum_patternGraphs_eq (p : ℝ) (E : Finset (SimpleGraph V)) {F Fp : Finset (Sym2 V)}
    (hF : F ⊆ edges (⊤ : SimpleGraph V)) (hFp : Fp ⊆ F) (hE : DeterminedOutside E F) :
    ∑ G ∈ patternGraphs E F Fp, gnpWeight p G =
      ∑ S ∈ freeCore E F, edgeWeight p (S ∪ Fp) := by
  refine sum_nbij' (fun G => edges G \ F)
    (fun S => SimpleGraph.fromEdgeSet ((S ∪ Fp : Finset (Sym2 V)) : Set (Sym2 V)))
    (fun G hG => sdiff_mem_freeCore hE (mem_patternGraphs.1 hG).1)
    (fun S hS => ?_) (fun G hG => ?_) (fun S hS => ?_) (fun G hG => ?_)
  · refine mem_patternGraphs.2 ⟨fromEdgeSet_union_mem hF hE hS hFp, ?_⟩
    have hS' := (mem_freeCore.1 hS).1
    obtain ⟨hsub, _, hint⟩ := free_union_facts hF hS' hFp
    rw [edges_fromEdgeSet _ hsub, hint]
  · obtain ⟨_, hpat⟩ := mem_patternGraphs.1 hG
    rw [← hpat, sdiff_union_inter, fromEdgeSet_edges]
  · have hS' := (mem_freeCore.1 hS).1
    obtain ⟨hsub, hsd, _⟩ := free_union_facts hF hS' hFp
    rw [edges_fromEdgeSet _ hsub, hsd]
  · obtain ⟨_, hpat⟩ := mem_patternGraphs.1 hG
    rw [gnpWeight_eq_edgeWeight, ← hpat, sdiff_union_inter]

/-- The weight of `E`, through the core and the patterns inside `F`. -/
theorem sum_graphs_eq (p : ℝ) (E : Finset (SimpleGraph V)) {F : Finset (Sym2 V)}
    (hF : F ⊆ edges (⊤ : SimpleGraph V)) (hE : DeterminedOutside E F) :
    ∑ G ∈ E, gnpWeight p G =
      ∑ S ∈ freeCore E F, ∑ H ∈ F.powerset, edgeWeight p (S ∪ H) := by
  rw [← sum_product' (s := freeCore E F) (t := F.powerset) (fun S H => edgeWeight p (S ∪ H))]
  refine sum_nbij' (fun G => (edges G \ F, edges G ∩ F))
    (fun x => SimpleGraph.fromEdgeSet ((x.1 ∪ x.2 : Finset (Sym2 V)) : Set (Sym2 V)))
    (fun G hG => mem_product.2 ⟨sdiff_mem_freeCore hE hG, mem_powerset.2 inter_subset_right⟩)
    (fun x hx => ?_) (fun G hG => ?_) (fun x hx => ?_) (fun G hG => ?_)
  · obtain ⟨hS, hH⟩ := mem_product.1 hx
    exact fromEdgeSet_union_mem hF hE hS (mem_powerset.1 hH)
  · simp only
    rw [sdiff_union_inter, fromEdgeSet_edges]
  · obtain ⟨hS, hH⟩ := mem_product.1 hx
    have hS' := (mem_freeCore.1 hS).1
    obtain ⟨hsub, hsd, hint⟩ := free_union_facts hF hS' (mem_powerset.1 hH)
    rw [edges_fromEdgeSet _ hsub, hsd, hint]
  · simp only
    rw [gnpWeight_eq_edgeWeight, sdiff_union_inter]

/-- `edgeWeight p (S ∪ H)` factorises when `S` is free and `H ⊆ F`. -/
theorem edgeWeight_union {F S H : Finset (Sym2 V)} (p : ℝ) (hF : F ⊆ edges (⊤ : SimpleGraph V))
    (hS : S ⊆ edges (⊤ : SimpleGraph V) \ F) (hH : H ⊆ F) :
    edgeWeight p (S ∪ H) =
      (p ^ H.card * (1 - p) ^ (F.card - H.card)) *
        (p ^ S.card * (1 - p) ^ ((Fintype.card V).choose 2 - F.card - S.card)) := by
  have hdisj : Disjoint S H := disjoint_of_subset_right hH (disjoint_of_subset_left hS sdiff_disjoint)
  have hle := card_free_le hF hS
  have hHF := card_le_card hH
  unfold edgeWeight
  rw [card_union_of_disjoint hdisj]
  have : (Fintype.card V).choose 2 - (S.card + H.card) =
      (F.card - H.card) + ((Fintype.card V).choose 2 - F.card - S.card) := by omega
  rw [this, pow_add, pow_add]
  ring

/-- **The independence lemma.** For `F ⊆ edges ⊤`, `Fp ⊆ F` and a finset `E` of graphs
determined outside `F`, the `G(n, p)` weight of the graphs of `E` whose edges inside `F`
are exactly `Fp` is `p^|Fp| (1 − p)^(|F| − |Fp|)` times the weight of `E`: the edges at the
pairs of `F` are independent of every event determined by the other pairs. -/
theorem sum_gnpWeight_pattern (p : ℝ) (E : Finset (SimpleGraph V)) {F Fp : Finset (Sym2 V)}
    (hF : F ⊆ edges (⊤ : SimpleGraph V)) (hFp : Fp ⊆ F) (hE : DeterminedOutside E F) :
    ∑ G ∈ patternGraphs E F Fp, gnpWeight p G =
      p ^ Fp.card * (1 - p) ^ (F.card - Fp.card) * ∑ G ∈ E, gnpWeight p G := by
  rw [sum_patternGraphs_eq p E hF hFp hE, sum_graphs_eq p E hF hE, mul_sum]
  refine sum_congr rfl (fun S hS => ?_)
  have hS' := (mem_freeCore.1 hS).1
  rw [edgeWeight_union p hF hS' hFp]
  rw [sum_congr rfl (fun H hH => edgeWeight_union p hF hS' (mem_powerset.1 hH)), ← sum_mul,
    sum_pow_mul_eq_add_pow]
  simp

/-! ### The chain, stated -/

/-- `Bin(m, p)` at `j`. -/
def binomPmf {K : Type*} [Field K] (m : ℕ) (p : K) (j : ℕ) : K :=
  (m.choose j : K) * p ^ j * (1 - p) ^ (m - j)

/-- One step of the open-count chain: after `t − 1` placements with `k` open suffix vertices
(`f k` the mass of that state), the vertex placed at step `t` is open with probability
`k / (n − t + 1)`; if it is closed, `n − t − k` closed suffix vertices remain and `j` of them
open (`k' = k + j`); if it is open it leaves the suffix, `n − t + 1 − k` closed ones remain and
`k' = k − 1 + j`.  States above `w` are dropped by summing `k` over `0..w` only. -/
def chainStep {K : Type*} [Field K] (n : ℕ) (p : K) (w t : ℕ) (f : ℕ → K) :
    ℕ → K := fun k' =>
  ∑ k ∈ range (w + 1), f k *
    ((1 - (k : K) / ((n - t + 1 : ℕ) : K)) *
        (if k ≤ k' then binomPmf (n - t - k) p (k' - k) else 0) +
      ((k : K) / ((n - t + 1 : ℕ) : K)) *
        (if k ≤ k' + 1 then binomPmf (n - t + 1 - k) p (k' + 1 - k) else 0))

/-- The chain after `t` placements, from the empty prefix. -/
def chainVec {K : Type*} [Field K] (n : ℕ) (p : K) (w : ℕ) : ℕ → ℕ → K
  | 0 => fun k => if k = 0 then 1 else 0
  | t + 1 => chainStep n p w (t + 1) (chainVec n p w t)

/-- `q(n, p, w)`: the chain's mass at `k = 0` after all `n` placements. -/
def chainQ {K : Type*} [Field K] (n : ℕ) (p : K) (w : ℕ) : K :=
  chainVec n p w n 0

/-- **The chain identity, stated and not proved**: the `G(n, p)` probability that a fixed
layout has vertex separation at most `w` is the chain's value.  `learning/layout_moment.py`
checks it exactly on every labelled graph to 10 vertices; the proof on paper conditions on
the opening times of the suffix vertices (independent truncated geometrics) and uses their
exchangeability, and its finite-sum formalisation is the open item of
`reports/layout_second_moment.md`. -/
def ChainIdentity (V : Type*) [Fintype V] [DecidableEq V] (p : ℝ) : Prop :=
  ∀ (σ : LinearLayout V) (w : ℕ), narrowWeight p σ w = chainQ (Fintype.card V) p w

end MOSPFormalization
