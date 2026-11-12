/-
Copyright (c) 2026 Alexandre Linhares. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Concentration of the pathwidth of a random graph: the Lipschitz lemma

`reports/pathwidth_concentration.md` §1. Pathwidth is 1-Lipschitz under **vertex
exposure**: if two graphs on the same vertex set agree on every pair of vertices
avoiding `v` — they may differ arbitrarily in the edges at `v` — their pathwidths
differ by at most one. The construction is the obvious one: take a path
decomposition of `G'` and put `v` into every bag; every edge of `G` avoiding `v` is an
edge of `G'` and lies in a bag already, every edge at `v` lies in any bag of its other
end, the interval property of `v` is trivial, and each bag grew by at most one.

This is the deterministic input to McDiarmid's bounded-differences inequality
(McDiarmid 1989, *On the method of bounded differences*; Shamir & Spencer 1987 for the
chromatic number): exposing `G(n, p)` one vertex at a time gives `n` coordinates with
difference bound `1`, hence `P(|pw − E pw| ≥ t) ≤ 2 exp(−2t²/n)` and
`Var(pw) ≤ n/4` (Efron & Stein 1981; Steele 1986). Mathlib (at the pinned revision)
has Hoeffding's lemma and the Azuma–Hoeffding inequality in sub-Gaussian form
(`ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF`) but not McDiarmid's
inequality, and the Doob martingale of the vertex-exposure filtration is not built
here; the two probabilistic statements are therefore stated as `Prop`s
(`PathwidthConcentration`, `PathwidthVarianceBound`), with the citation, and never
asserted. No `axiom`, no `sorry`.

## Main results

* `AgreeOff G G' v` — every edge of `G` avoiding `v` is an edge of `G'`.
* `PathDecomposition.insertVertex` — the decomposition of `G` obtained from one of
  `G'` by inserting `v` into every bag; `insertVertex_width_le`: width `≤ width + 1`.
* `pathwidth_le_add_one_of_agreeOff` — `pathwidth G ≤ pathwidth G' + 1`.
* `pathwidth_lipschitz_vertex` — **the Lipschitz lemma**: if `G` and `G'` agree on all
  pairs avoiding `v` then `pathwidth G ≤ pathwidth G' + 1` and conversely;
  `abs_pathwidth_sub_le_one` is the same as `|pw G − pw G'| ≤ 1` in `ℤ`.
* `pathwidth_le_deleteIncidenceSet_add_one` / `pathwidth_deleteIncidenceSet_le` —
  removing the edges at one vertex lowers the pathwidth by at most one and never
  raises it.
* `pathwidth_le_induce_compl_add_one` — **vertex deletion** lowers the pathwidth by at
  most one: `pathwidth G ≤ pathwidth (G − v) + 1` (`pathwidth_induce_le` of
  `Minor.lean` is the other direction).
* `pathwidthMean`, `pathwidthVar` — the `G(n, p)` mean and variance of the pathwidth on
  `Fin n`, as finite weighted sums with `gnpWeight`.
* `PathwidthConcentration`, `PathwidthVarianceBound` — McDiarmid's inequality and the
  bounded-differences variance bound for `pathwidth (G(n, p))`, **stated, not proved**.

Checked before stating: every graph on at most 7 vertices, every vertex, every
replacement of its neighbourhood (`reports/scratch/pathwidth_concentration/lipschitz.log`,
`learning.pathwidth_concentration.check_lipschitz`): zero violations of either inequality.
-/

import MOSPFormalization.Minor
import MOSPFormalization.FirstMoment
import Mathlib.Analysis.SpecialFunctions.Exp

set_option linter.unusedSectionVars false

namespace MOSPFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Agreement away from a vertex -/

/-- Every edge of `G` avoiding `v` is an edge of `G'`. -/
def AgreeOff (G G' : SimpleGraph V) (v : V) : Prop :=
  ∀ u w, u ≠ v → w ≠ v → G.Adj u w → G'.Adj u w

theorem AgreeOff.of_iff {G G' : SimpleGraph V} {v : V}
    (h : ∀ u w, u ≠ v → w ≠ v → (G.Adj u w ↔ G'.Adj u w)) : AgreeOff G G' v :=
  fun u w hu hw huw => (h u w hu hw).1 huw

theorem AgreeOff.symm_of_iff {G G' : SimpleGraph V} {v : V}
    (h : ∀ u w, u ≠ v → w ≠ v → (G.Adj u w ↔ G'.Adj u w)) : AgreeOff G' G v :=
  fun u w hu hw huw => (h u w hu hw).2 huw

namespace PathDecomposition

/-- Insert `v` into every bag of a path decomposition of `G'`: a path decomposition
of any `G` whose edges avoiding `v` are edges of `G'`. -/
def insertVertex {G G' : SimpleGraph V} {v : V} (h : AgreeOff G G' v)
    (P : PathDecomposition G') : PathDecomposition G where
  length := P.length
  bag := fun i => insert v (P.bag i)
  vertex_coverage := fun w => by
    obtain ⟨i, hi⟩ := P.vertex_coverage w
    exact ⟨i, Finset.mem_insert_of_mem hi⟩
  edge_coverage := fun u w huw => by
    by_cases hu : u = v
    · obtain ⟨i, hi⟩ := P.vertex_coverage w
      refine ⟨i, ?_, Finset.mem_insert_of_mem hi⟩
      rw [hu]; exact Finset.mem_insert_self _ _
    · by_cases hw : w = v
      · obtain ⟨i, hi⟩ := P.vertex_coverage u
        refine ⟨i, Finset.mem_insert_of_mem hi, ?_⟩
        rw [hw]; exact Finset.mem_insert_self _ _
      · obtain ⟨i, hi1, hi2⟩ := P.edge_coverage u w (h u w hu hw huw)
        exact ⟨i, Finset.mem_insert_of_mem hi1, Finset.mem_insert_of_mem hi2⟩
  interval := fun w i j k hij hjk hi hk => by
    rcases Finset.mem_insert.1 hi with hw | hi'
    · rw [hw]; exact Finset.mem_insert_self _ _
    · rcases Finset.mem_insert.1 hk with hw | hk'
      · rw [hw]; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (P.interval w i j k hij hjk hi' hk')

theorem insertVertex_width_le {G G' : SimpleGraph V} {v : V} (h : AgreeOff G G' v)
    (P : PathDecomposition G') : (P.insertVertex h).width ≤ P.width + 1 :=
  width_le_of_forall_card_le _ fun i => by
    show (insert v (P.bag i)).card ≤ P.width + 1 + 1
    have h1 := P.bag_card_le_width_add_one i
    have h2 := Finset.card_insert_le v (P.bag i)
    omega

end PathDecomposition

/-! ### The Lipschitz lemma -/

theorem pathwidth_le_add_one_of_agreeOff {G G' : SimpleGraph V} {v : V}
    (h : AgreeOff G G' v) : pathwidth G ≤ pathwidth G' + 1 := by
  obtain ⟨P, hP⟩ := exists_pathDecomposition_width_eq G'
  calc pathwidth G ≤ (P.insertVertex h).width := pathwidth_le_width G _
    _ ≤ P.width + 1 := P.insertVertex_width_le h
    _ = pathwidth G' + 1 := by rw [hP]

/-- **Vertex exposure is 1-Lipschitz.** Two graphs that agree on every pair of vertices
avoiding `v` have pathwidths within one of each other. -/
theorem pathwidth_lipschitz_vertex {G G' : SimpleGraph V} (v : V)
    (h : ∀ u w, u ≠ v → w ≠ v → (G.Adj u w ↔ G'.Adj u w)) :
    pathwidth G ≤ pathwidth G' + 1 ∧ pathwidth G' ≤ pathwidth G + 1 :=
  ⟨pathwidth_le_add_one_of_agreeOff (AgreeOff.of_iff h),
   pathwidth_le_add_one_of_agreeOff (AgreeOff.symm_of_iff h)⟩

/-- The same as a distance in `ℤ`: `|pw G − pw G'| ≤ 1`. -/
theorem abs_pathwidth_sub_le_one {G G' : SimpleGraph V} (v : V)
    (h : ∀ u w, u ≠ v → w ≠ v → (G.Adj u w ↔ G'.Adj u w)) :
    |(pathwidth G : ℤ) - pathwidth G'| ≤ 1 := by
  obtain ⟨h1, h2⟩ := pathwidth_lipschitz_vertex v h
  rw [abs_le]
  constructor <;> omega

/-! ### Deleting the edges at a vertex, and deleting the vertex -/

/-- Removing every edge at `v` lowers the pathwidth by at most one. -/
theorem pathwidth_le_deleteIncidenceSet_add_one (G : SimpleGraph V) (v : V) :
    pathwidth G ≤ pathwidth (G.deleteEdges (G.incidenceSet v)) + 1 :=
  pathwidth_le_add_one_of_agreeOff (v := v) fun u w hu hw huw => by
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨huw, fun hmem => ?_⟩
    rw [SimpleGraph.mk'_mem_incidenceSet_iff] at hmem
    rcases hmem.2 with hvu | hvw
    · exact hu hvu.symm
    · exact hw hvw.symm

/-- Removing edges never raises the pathwidth. -/
theorem pathwidth_deleteIncidenceSet_le (G : SimpleGraph V) (v : V) :
    pathwidth (G.deleteEdges (G.incidenceSet v)) ≤ pathwidth G :=
  pathwidth_mono (SimpleGraph.deleteEdges_le _)

open scoped Classical in
/-- From a path decomposition of `G − v` to one of `G`: lift the bags along the
inclusion and insert `v` into every one. -/
noncomputable def PathDecomposition.ofInduceCompl (G : SimpleGraph V) (v : V)
    (P : PathDecomposition (G.induce ({v}ᶜ : Set V))) : PathDecomposition G where
  length := P.length
  bag := fun i => insert v ((P.bag i).map (Function.Embedding.subtype _))
  vertex_coverage := fun w => by
    by_cases hw : w = v
    · exact ⟨⟨0, Nat.zero_lt_succ _⟩, by rw [hw]; exact Finset.mem_insert_self _ _⟩
    · obtain ⟨i, hi⟩ := P.vertex_coverage ⟨w, Set.mem_compl_singleton_iff.2 hw⟩
      exact ⟨i, Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ hi)⟩
  edge_coverage := fun u w huw => by
    by_cases hu : u = v
    · have hw : w ≠ v := fun hw => huw.ne (hu.trans hw.symm)
      obtain ⟨i, hi⟩ := P.vertex_coverage ⟨w, Set.mem_compl_singleton_iff.2 hw⟩
      refine ⟨i, ?_, Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ hi)⟩
      rw [hu]; exact Finset.mem_insert_self _ _
    · by_cases hw : w = v
      · obtain ⟨i, hi⟩ := P.vertex_coverage ⟨u, Set.mem_compl_singleton_iff.2 hu⟩
        refine ⟨i, Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ hi), ?_⟩
        rw [hw]; exact Finset.mem_insert_self _ _
      · obtain ⟨i, hi1, hi2⟩ := P.edge_coverage ⟨u, Set.mem_compl_singleton_iff.2 hu⟩
          ⟨w, Set.mem_compl_singleton_iff.2 hw⟩ huw
        exact ⟨i, Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ hi1),
          Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ hi2)⟩
  interval := fun w i j k hij hjk hi hk => by
    rcases Finset.mem_insert.1 hi with hw | hi'
    · rw [hw]; exact Finset.mem_insert_self _ _
    · rcases Finset.mem_insert.1 hk with hw | hk'
      · rw [hw]; exact Finset.mem_insert_self _ _
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hi'
        obtain ⟨y, hy, hxy⟩ := Finset.mem_map.1 hk'
        have hyx : y = x := (Function.Embedding.subtype _).injective hxy
        subst hyx
        exact Finset.mem_insert_of_mem
          (Finset.mem_map_of_mem _ (P.interval y i j k hij hjk hx hy))

open scoped Classical in
theorem PathDecomposition.ofInduceCompl_width_le (G : SimpleGraph V) (v : V)
    (P : PathDecomposition (G.induce ({v}ᶜ : Set V))) :
    (P.ofInduceCompl G v).width ≤ P.width + 1 :=
  width_le_of_forall_card_le _ fun i => by
    show (insert v ((P.bag i).map (Function.Embedding.subtype _))).card ≤ P.width + 1 + 1
    have h1 := P.bag_card_le_width_add_one i
    have h2 := Finset.card_insert_le v ((P.bag i).map (Function.Embedding.subtype _))
    rw [Finset.card_map] at h2
    omega

open scoped Classical in
/-- **Vertex deletion lowers the pathwidth by at most one.** -/
theorem pathwidth_le_induce_compl_add_one (G : SimpleGraph V) (v : V) :
    pathwidth G ≤ pathwidth (G.induce ({v}ᶜ : Set V)) + 1 := by
  obtain ⟨P, hP⟩ := exists_pathDecomposition_width_eq (G.induce ({v}ᶜ : Set V))
  calc pathwidth G ≤ (P.ofInduceCompl G v).width := pathwidth_le_width G _
    _ ≤ P.width + 1 := P.ofInduceCompl_width_le G v
    _ = pathwidth (G.induce ({v}ᶜ : Set V)) + 1 := by rw [hP]

open scoped Classical in
/-- Deleting a vertex changes the pathwidth by at most one, in both directions. -/
theorem pathwidth_induce_compl_sandwich (G : SimpleGraph V) (v : V) :
    pathwidth (G.induce ({v}ᶜ : Set V)) ≤ pathwidth G ∧
      pathwidth G ≤ pathwidth (G.induce ({v}ᶜ : Set V)) + 1 :=
  ⟨pathwidth_induce_le G _, pathwidth_le_induce_compl_add_one G v⟩

/-! ### The probabilistic statements, on `Fin n` -/

section Gnp

open scoped Classical

/-- The `G(n, p)` mean of a real functional of the graph. -/
noncomputable def gnpMean (n : ℕ) (p : ℝ) (f : SimpleGraph (Fin n) → ℝ) : ℝ :=
  ∑ G : SimpleGraph (Fin n), gnpWeight p G * f G

/-- `E[pathwidth G(n, p)]`. -/
noncomputable def pathwidthMean (n : ℕ) (p : ℝ) : ℝ :=
  gnpMean n p fun G => (pathwidth G : ℝ)

/-- `Var(pathwidth G(n, p))`. -/
noncomputable def pathwidthVar (n : ℕ) (p : ℝ) : ℝ :=
  gnpMean n p fun G => ((pathwidth G : ℝ) - pathwidthMean n p) ^ 2

/-- **Not proved here.** The bounded-differences variance bound (Efron & Stein 1981;
Steele 1986): `n` vertex-exposure coordinates, each of difference at most one by
`pathwidth_lipschitz_vertex`, give `Var(pw) ≤ n/4`, i.e. a standard deviation at
most `√n / 2`. -/
def PathwidthVarianceBound : Prop :=
  ∀ (n : ℕ) (p : ℝ), 0 ≤ p → p ≤ 1 → pathwidthVar n p ≤ (n : ℝ) / 4

/-- **Not proved here.** McDiarmid's bounded-differences inequality (McDiarmid 1989;
the Shamir–Spencer argument for the chromatic number, 1987) applied to the
vertex-exposure martingale of `pathwidth`, whose differences are at most one by
`pathwidth_lipschitz_vertex`: `P(|pw − E pw| ≥ t) ≤ 2 exp(−2t²/n)`. -/
def PathwidthConcentration : Prop :=
  ∀ (n : ℕ) (p t : ℝ), 0 ≤ p → p ≤ 1 → 0 ≤ t →
    ∑ G ∈ (Finset.univ.filter fun G : SimpleGraph (Fin n) =>
        t ≤ |(pathwidth G : ℝ) - pathwidthMean n p|), gnpWeight p G
      ≤ 2 * Real.exp (-2 * t ^ 2 / n)

end Gnp

end MOSPFormalization
