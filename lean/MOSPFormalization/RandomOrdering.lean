/-
Copyright (c) 2026 Alexandre Linhares. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# The width of a fixed ordering of `G(n, p)`: the random-ordering upper bound

`reports/random_ordering_bound.md`.  Fix a layout `σ` of the vertex set (the identity, say)
and expose `G(n, p)`.  At position `i` the prefix `S = {v : σ v ≤ i}` has `t = i + 1`
vertices and the suffix `m = n − t`; a suffix vertex is *open* when it has an edge into
the prefix, and the open count `vertexSepAt G σ i` is the sum over the suffix of the
indicators "the `t` pairs from `v` into `S` are not all absent".  Those `t`-sets of pairs
are pairwise disjoint across the suffix, so the indicators are independent
Bernoulli(`1 − (1 − p)^t`) and the open count is `Bin(m, 1 − (1 − p)^t)`.  A union bound
over the `n` positions then bounds the probability that the layout is wider than `w`, and
since `pathwidth ≤ vertexSepOfLayout` for every layout, the same number bounds
`P(pathwidth > w)`:

* `binomTail m q w = ∑_{w < j ≤ m} C(m, j) q^j (1 − q)^(m − j)`, the upper tail of
  `Bin(m, q)`, with the generating-function (Chernoff) bound
  `binomTail_le_exp`: `binomTail m q w ≤ e^{−λ w} (1 − q + q e^{λ})^m` for `λ ≥ 0`.
* **`sum_gnpWeight_blocks`**, the independence of disjoint blocks of pairs: for pairwise
  disjoint `F j ⊆ edges ⊤` and admissible pattern sets `P j ⊆ (F j).powerset`, the weight
  of the graphs of `E` (determined outside `⋃ F j`) whose edges inside each `F j` form a
  pattern of `P j` is `∏_j (∑_{S ∈ P j} p^|S| (1 − p)^(|F j| − |S|))` times the weight of
  `E`.  It is `sum_gnpWeight_pattern` of `LayoutMoment.lean` iterated over the blocks.
* **`sum_gnpWeight_activeSuffix_eq`**: the weight of `{activeSuffix G σ i = B}` is
  `(1 − (1 − p)^t)^|B| ((1 − p)^t)^(m − |B|)` for `B ⊆ suffixSet σ i`;
  **`sum_gnpWeight_vertexSepAt_gt`**: the weight of `{vertexSepAt G σ i > w}` is exactly
  `binomTail m (1 − (1 − p)^t) w`.
* **`sum_gnpWeight_vertexSepOfLayout_gt_le`** (the union bound) and
  **`sum_gnpWeight_pathwidth_gt_le`**: for `0 ≤ p ≤ 1` and any layout `σ`,
  `P(vertexSepOfLayout G σ > w) ≤ ∑_{i < n} binomTail (n − i − 1) (1 − (1 − p)^(i + 1)) w`,
  and `P(pathwidth G > w)` is at most the same sum;
  `sum_gnpWeight_graphsOfPathwidthLe_ge`, the complementary form.

The asymptotic reading — `pw(G(n, c/n)) ≤ (β_typ(c) + ε) n` with probability `1 − o(1)`,
`β_typ(c) = max_x (1 − x)(1 − e^{−cx})` — is the Chernoff bound above with `λ` chosen and
the maximum over `t` evaluated, on paper in the report; the finite statement here is the
one the brute-force check verified (every labelled graph on `n ≤ 7` vertices, the identity
ordering, four values of `p`, every position exact and the union bound, 672 checks).

No `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound` only.
-/

import MOSPFormalization.LayoutMoment
import MOSPFormalization.LayoutToDecomposition
import Mathlib.Analysis.SpecialFunctions.Exp

set_option linter.unusedSectionVars false

namespace MOSPFormalization

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The upper tail of a binomial -/

/-- `P(Bin(m, q) > w) = ∑_{w < j ≤ m} C(m, j) q^j (1 − q)^(m − j)`. -/
noncomputable def binomTail (m : ℕ) (q : ℝ) (w : ℕ) : ℝ :=
  ∑ j ∈ (range (m + 1)).filter (fun j => w < j), (m.choose j : ℝ) * (q ^ j * (1 - q) ^ (m - j))

theorem binomTail_nonneg (m : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (w : ℕ) :
    0 ≤ binomTail m q w :=
  sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (pow_nonneg hq0 _) (pow_nonneg (sub_nonneg.2 hq1) _)))

/-- The generating-function (Chernoff) bound on the binomial tail:
`P(Bin(m, q) > w) ≤ e^{−λ w} (1 − q + q e^{λ})^m` for every `λ ≥ 0`. -/
theorem binomTail_le_exp (m : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (w : ℕ) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    binomTail m q w ≤ Real.exp (-(lam * w)) * (1 - q + q * Real.exp lam) ^ m := by
  have hterm : ∀ j : ℕ, 0 ≤ (m.choose j : ℝ) * ((q * Real.exp lam) ^ j * (1 - q) ^ (m - j)) :=
    fun j => mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (pow_nonneg (mul_nonneg hq0 (Real.exp_pos _).le) _)
        (pow_nonneg (sub_nonneg.2 hq1) _))
  calc binomTail m q w
      ≤ ∑ j ∈ (range (m + 1)).filter (fun j => w < j),
          Real.exp (-(lam * w)) * ((m.choose j : ℝ) * ((q * Real.exp lam) ^ j * (1 - q) ^ (m - j))) := by
        refine sum_le_sum (fun j hj => ?_)
        have hwj : w < j := (mem_filter.1 hj).2
        -- `exp(−λw) · (q e^λ)^j = exp(λ(j − w)) · q^j ≥ q^j`
        have h1 : (q : ℝ) ^ j ≤ Real.exp (-(lam * w)) * (q * Real.exp lam) ^ j := by
          rw [mul_pow, ← Real.exp_nat_mul, ← mul_assoc, mul_comm (Real.exp _) (q ^ j), mul_assoc,
            ← Real.exp_add]
          refine le_mul_of_one_le_right (pow_nonneg hq0 _) (Real.one_le_exp_iff.2 ?_)
          have : (w : ℝ) ≤ j := by exact_mod_cast hwj.le
          nlinarith
        calc (m.choose j : ℝ) * (q ^ j * (1 - q) ^ (m - j))
            ≤ (m.choose j : ℝ) * ((Real.exp (-(lam * w)) * (q * Real.exp lam) ^ j) * (1 - q) ^ (m - j)) := by
              refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1
                (pow_nonneg (sub_nonneg.2 hq1) _)) (Nat.cast_nonneg _)
          _ = _ := by ring
    _ ≤ ∑ j ∈ range (m + 1),
          Real.exp (-(lam * w)) * ((m.choose j : ℝ) * ((q * Real.exp lam) ^ j * (1 - q) ^ (m - j))) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun j _ _ => mul_nonneg (Real.exp_pos _).le (hterm j))
    _ = Real.exp (-(lam * w)) * (q * Real.exp lam + (1 - q)) ^ m := by
        rw [← mul_sum, add_pow]
        congr 1
        refine sum_congr rfl (fun j _ => ?_)
        ring
    _ = _ := by ring

/-! ### Independent blocks of pairs -/

theorem mem_edges_iff_of_sdiff_eq {G H : SimpleGraph V} {F : Finset (Sym2 V)}
    (hGH : edges G \ F = edges H \ F) {e : Sym2 V} (he : e ∉ F) :
    e ∈ edges G ↔ e ∈ edges H := by
  constructor
  · intro h
    have : e ∈ edges G \ F := mem_sdiff.2 ⟨h, he⟩
    rw [hGH] at this
    exact (mem_sdiff.1 this).1
  · intro h
    have : e ∈ edges H \ F := mem_sdiff.2 ⟨h, he⟩
    rw [← hGH] at this
    exact (mem_sdiff.1 this).1

/-- Being determined outside a set of pairs is inherited by subsets of that set. -/
theorem DeterminedOutside.mono {E : Finset (SimpleGraph V)} {F F' : Finset (Sym2 V)}
    (h : DeterminedOutside E F') (hFF : F ⊆ F') : DeterminedOutside E F := by
  intro G H hGH
  apply h
  ext e
  simp only [mem_sdiff]
  constructor
  · rintro ⟨he, he'⟩
    exact ⟨(mem_edges_iff_of_sdiff_eq hGH (fun h' => he' (hFF h'))).1 he, he'⟩
  · rintro ⟨he, he'⟩
    exact ⟨(mem_edges_iff_of_sdiff_eq hGH (fun h' => he' (hFF h'))).2 he, he'⟩

theorem determinedOutside_univ (F : Finset (Sym2 V)) :
    DeterminedOutside (univ : Finset (SimpleGraph V)) F :=
  fun _ _ _ => by simp

/-- **Independent blocks.** For pairwise disjoint sets of pairs `F j ⊆ edges ⊤` (`j ∈ s`),
pattern sets `P j` of subsets of `F j`, and a finset `E` of graphs determined outside
`⋃_{j ∈ s} F j`, the `G(n, p)` weight of the graphs of `E` whose edges inside every `F j` form
a pattern of `P j` is the product over `j ∈ s` of the pattern weights
`∑_{S ∈ P j} p^|S| (1 − p)^(|F j| − |S|)`, times the weight of `E`. -/
theorem sum_gnpWeight_blocks {ι : Type*} [DecidableEq ι] (p : ℝ) (E : Finset (SimpleGraph V))
    (s : Finset ι) (F : ι → Finset (Sym2 V)) (P : ι → Finset (Finset (Sym2 V)))
    (hF : ∀ j ∈ s, F j ⊆ edges (⊤ : SimpleGraph V))
    (hP : ∀ j ∈ s, ∀ S ∈ P j, S ⊆ F j)
    (hdisj : (s : Set ι).PairwiseDisjoint F)
    (hE : DeterminedOutside E (s.biUnion F)) :
    ∑ G ∈ E.filter (fun G => ∀ j ∈ s, edges G ∩ F j ∈ P j), gnpWeight p G =
      (∏ j ∈ s, ∑ S ∈ P j, p ^ S.card * (1 - p) ^ ((F j).card - S.card)) *
        ∑ G ∈ E, gnpWeight p G := by
  classical
  induction s using Finset.induction_on generalizing E with
  | empty => simp
  | insert a s has ih =>
    have hFa : F a ⊆ edges (⊤ : SimpleGraph V) := hF a (mem_insert_self a s)
    have hF' : ∀ j ∈ s, F j ⊆ edges (⊤ : SimpleGraph V) := fun j hj => hF j (mem_insert_of_mem hj)
    have hP' : ∀ j ∈ s, ∀ S ∈ P j, S ⊆ F j := fun j hj => hP j (mem_insert_of_mem hj)
    have hdisj' : (s : Set ι).PairwiseDisjoint F :=
      hdisj.subset (by intro x hx; exact mem_insert_of_mem hx)
    have hdisjA : ∀ j ∈ s, Disjoint (F a) (F j) := fun j hj =>
      hdisj (mem_insert_self a s) (mem_insert_of_mem hj) (fun h => has (h ▸ hj))
    have hE' : DeterminedOutside E (s.biUnion F) :=
      hE.mono (biUnion_subset_biUnion_of_subset_left F (subset_insert a s))
    set E' := E.filter (fun G => ∀ j ∈ s, edges G ∩ F j ∈ P j) with hE'def
    have hE'det : DeterminedOutside E' (F a) := by
      intro G H hGH
      have h1 : G ∈ E ↔ H ∈ E :=
        hE.mono (subset_biUnion_of_mem F (mem_insert_self a s)) G H hGH
      have h2 : ∀ j ∈ s, edges G ∩ F j = edges H ∩ F j := by
        intro j hj
        ext e
        simp only [mem_inter]
        constructor
        · rintro ⟨heG, hej⟩
          exact ⟨(mem_edges_iff_of_sdiff_eq hGH (disjoint_right.1 (hdisjA j hj) hej)).1 heG, hej⟩
        · rintro ⟨heH, hej⟩
          exact ⟨(mem_edges_iff_of_sdiff_eq hGH (disjoint_right.1 (hdisjA j hj) hej)).2 heH, hej⟩
      simp only [hE'def, mem_filter]
      constructor
      · rintro ⟨hGE, hGs⟩
        exact ⟨h1.1 hGE, fun j hj => (h2 j hj) ▸ hGs j hj⟩
      · rintro ⟨hHE, hHs⟩
        exact ⟨h1.2 hHE, fun j hj => (h2 j hj).symm ▸ hHs j hj⟩
    have hsplit : E.filter (fun G => ∀ j ∈ insert a s, edges G ∩ F j ∈ P j) =
        (P a).biUnion (fun Fp => patternGraphs E' (F a) Fp) := by
      ext G
      simp only [hE'def, mem_filter, mem_biUnion, mem_patternGraphs, forall_mem_insert]
      constructor
      · rintro ⟨hGE, hGa, hGs⟩
        exact ⟨edges G ∩ F a, hGa, ⟨hGE, hGs⟩, rfl⟩
      · rintro ⟨Fp, hFp, ⟨hGE, hGs⟩, rfl⟩
        exact ⟨hGE, hFp, hGs⟩
    have hpd : ((P a : Finset (Finset (Sym2 V))) : Set (Finset (Sym2 V))).PairwiseDisjoint
        (fun Fp => patternGraphs E' (F a) Fp) := by
      intro Fp _ Fq _ hne
      rw [Function.onFun, disjoint_left]
      intro G hG hG'
      exact hne ((mem_patternGraphs.1 hG).2.symm.trans (mem_patternGraphs.1 hG').2)
    rw [hsplit, sum_biUnion hpd, prod_insert has,
      sum_congr rfl (fun Fp hFp =>
        sum_gnpWeight_pattern p E' hFa (hP a (mem_insert_self a s) Fp hFp) hE'det),
      ← sum_mul, ih E hF' hP' hdisj' hE', mul_assoc]

/-! ### The open count at a position is binomial -/

/-- The pairs joining `v` to the vertices of `A`. -/
def starPairs (A : Finset V) (v : V) : Finset (Sym2 V) := A.image (fun u => s(u, v))

theorem mem_starPairs {A : Finset V} {v : V} {e : Sym2 V} :
    e ∈ starPairs A v ↔ ∃ u ∈ A, s(u, v) = e := by
  simp [starPairs]

theorem starPairs_subset_top {A : Finset V} {v : V} (hv : v ∉ A) :
    starPairs A v ⊆ edges (⊤ : SimpleGraph V) := by
  intro e he
  obtain ⟨u, hu, rfl⟩ := mem_starPairs.1 he
  rw [mem_edges_top, Sym2.mk_isDiag_iff]
  rintro rfl
  exact hv hu

theorem card_starPairs {A : Finset V} {v : V} (hv : v ∉ A) : (starPairs A v).card = A.card := by
  unfold starPairs
  rw [card_image_of_injOn]
  intro u hu u' hu' h
  rcases Sym2.eq_iff.1 h with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact h1
  · exact absurd (h1 ▸ hu) hv

theorem starPairs_disjoint {A : Finset V} {v v' : V} (hv : v ∉ A) (hne : v ≠ v') :
    Disjoint (starPairs A v) (starPairs A v') := by
  rw [disjoint_left]
  intro e he he'
  obtain ⟨u, hu, rfl⟩ := mem_starPairs.1 he
  obtain ⟨u', hu', h⟩ := mem_starPairs.1 he'
  rcases Sym2.eq_iff.1 h with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact hne h2.symm
  · exact hv (h1 ▸ hu')

/-- A suffix vertex is active iff some pair from it into the prefix is an edge. -/
theorem mem_activeSuffix_iff_inter (G : SimpleGraph V) [DecidableRel G.Adj] (σ : LinearLayout V)
    (i : ℕ) (v : V) :
    v ∈ activeSuffix G σ i ↔
      v ∈ suffixSet σ i ∧ (edges G ∩ starPairs (prefixSet σ i) v).Nonempty := by
  rw [mem_activeSuffix_iff, mem_suffixSet_iff]
  constructor
  · rintro ⟨hv, u, hu, hadj⟩
    exact ⟨hv, s(u, v), mem_inter.2 ⟨mem_edges.2 hadj, mem_starPairs.2 ⟨u, hu, rfl⟩⟩⟩
  · rintro ⟨hv, e, he⟩
    obtain ⟨heG, heS⟩ := mem_inter.1 he
    obtain ⟨u, hu, rfl⟩ := mem_starPairs.1 heS
    exact ⟨hv, u, hu, mem_edges.1 heG⟩

/-- The weight of the nonempty patterns on the pairs of `F` is `1 − (1 − p)^|F|`. -/
theorem sum_nonempty_patterns (p : ℝ) (F : Finset (Sym2 V)) :
    ∑ S ∈ F.powerset.filter (fun S => S.Nonempty), p ^ S.card * (1 - p) ^ (F.card - S.card) =
      1 - (1 - p) ^ F.card := by
  have h := sum_pow_mul_eq_add_pow p (1 - p) F
  rw [add_sub_cancel, one_pow] at h
  have hsplit := sum_filter_add_sum_filter_not F.powerset (fun S => S.Nonempty)
    (fun S => p ^ S.card * (1 - p) ^ (F.card - S.card))
  have hempty : F.powerset.filter (fun S => ¬ S.Nonempty) = {∅} := by
    ext S
    simp only [mem_filter, mem_powerset, mem_singleton, not_nonempty_iff_eq_empty]
    constructor
    · exact fun h => h.2
    · rintro rfl
      exact ⟨empty_subset _, rfl⟩
  rw [hempty, sum_singleton, h] at hsplit
  simp only [card_empty, pow_zero, one_mul, Nat.sub_zero] at hsplit
  linarith

/-- The total `G(n, p)` weight is `1`. -/
theorem sum_gnpWeight_univ (p : ℝ) : ∑ G : SimpleGraph V, gnpWeight p G = 1 := by
  have h := sum_gnpWeight_emptyPairGraphs (V := V) (A := ∅) (R := ∅) (disjoint_empty_left ∅) p
  have huniv : emptyPairGraphs (∅ : Finset V) ∅ = univ := by
    ext G
    simp [mem_emptyPairGraphs, IsEmptyPair]
  rw [huniv] at h
  simpa using h

open scoped Classical in
/-- **The law of the active suffix.** For `B ⊆ suffixSet σ i`, the weight of the graphs
whose active suffix at position `i` is exactly `B` is
`(1 − (1 − p)^t)^|B| · ((1 − p)^t)^(m − |B|)`, `t = |prefixSet σ i|`, `m = |suffixSet σ i|`. -/
theorem sum_gnpWeight_activeSuffix_eq (p : ℝ) (σ : LinearLayout V) (i : ℕ) {B : Finset V}
    (hB : B ⊆ suffixSet σ i) :
    ∑ G ∈ (univ : Finset (SimpleGraph V)).filter (fun G => activeSuffix G σ i = B),
        gnpWeight p G =
      (1 - (1 - p) ^ (prefixSet σ i).card) ^ B.card *
        ((1 - p) ^ (prefixSet σ i).card) ^ ((suffixSet σ i).card - B.card) := by
  set A := prefixSet σ i with hA
  set Sf := suffixSet σ i with hSf
  have hAS : ∀ v ∈ Sf, v ∉ A := by
    intro v hv ha
    rw [hSf, mem_suffixSet_iff] at hv
    rw [hA, mem_prefixSet_iff] at ha
    omega
  let F : V → Finset (Sym2 V) := fun v => starPairs A v
  let P : V → Finset (Finset (Sym2 V)) := fun v =>
    if v ∈ B then (F v).powerset.filter (fun S => S.Nonempty) else {∅}
  have hiff : ∀ G : SimpleGraph V,
      activeSuffix G σ i = B ↔ ∀ v ∈ Sf, edges G ∩ F v ∈ P v := by
    intro G
    constructor
    · intro hact v hv
      have key : v ∈ B ↔ (edges G ∩ F v).Nonempty := by
        rw [← hact, mem_activeSuffix_iff_inter]
        exact and_iff_right hv
      by_cases hvB : v ∈ B
      · simp only [P, hvB, ite_true, mem_filter, mem_powerset, inter_subset_right, true_and]
        exact key.1 hvB
      · simp only [P, hvB, ite_false, mem_singleton]
        exact not_nonempty_iff_eq_empty.1 (fun h => hvB (key.2 h))
    · intro h
      ext v
      rw [mem_activeSuffix_iff_inter]
      constructor
      · rintro ⟨hv, hne⟩
        have := h v hv
        by_contra hvB
        simp only [P, hvB, ite_false, mem_singleton] at this
        exact hne.ne_empty this
      · intro hvB
        have hv := hB hvB
        refine ⟨hv, ?_⟩
        have := h v hv
        simp only [P, hvB, ite_true, mem_filter] at this
        exact this.2
  have hb := sum_gnpWeight_blocks p univ Sf F P
    (fun v hv => starPairs_subset_top (hAS v hv))
    (fun v hv S hS => by
      by_cases hvB : v ∈ B
      · simp only [P, hvB, ite_true, mem_filter, mem_powerset] at hS
        exact hS.1
      · simp only [P, hvB, ite_false, mem_singleton] at hS
        rw [hS]
        exact empty_subset _)
    (fun v hv v' _ hne => starPairs_disjoint (hAS v hv) hne)
    (determinedOutside_univ _)
  rw [sum_gnpWeight_univ, mul_one] at hb
  refine Eq.trans ?_ (hb.trans ?_)
  · refine sum_congr ?_ (fun _ _ => rfl)
    ext G
    simp only [mem_filter, mem_univ, true_and]
    exact hiff G
  have hfac : ∀ v ∈ Sf, (∑ S ∈ P v, p ^ S.card * (1 - p) ^ ((F v).card - S.card)) =
      if v ∈ B then 1 - (1 - p) ^ A.card else (1 - p) ^ A.card := by
    intro v hv
    by_cases hvB : v ∈ B
    · simp only [P, hvB, ite_true]
      rw [sum_nonempty_patterns, card_starPairs (hAS v hv)]
    · simp only [P, hvB, ite_false, sum_singleton, card_empty, pow_zero, one_mul, Nat.sub_zero]
      rw [card_starPairs (hAS v hv)]
  rw [prod_congr rfl hfac, prod_ite, prod_const, prod_const]
  have h1 : Sf.filter (fun v => v ∈ B) = B := by
    rw [filter_mem_eq_inter, inter_eq_right.2 hB]
  have h2 : (Sf.filter (fun v => v ∉ B)).card = Sf.card - B.card := by
    rw [← sdiff_eq_filter, card_sdiff_of_subset hB]
  rw [h1, h2]

open scoped Classical in
/-- **The open count at a position is binomial.** The `G(n, p)` weight of the graphs whose
vertex separation at position `i` of the layout `σ` exceeds `w` is the upper tail of
`Bin(m, 1 − (1 − p)^t)` at `w`, with `t = |prefixSet σ i|` and `m = |suffixSet σ i|`. -/
theorem sum_gnpWeight_vertexSepAt_gt (p : ℝ) (σ : LinearLayout V) (i w : ℕ) :
    ∑ G : SimpleGraph V, (if w < vertexSepAt G σ i then gnpWeight p G else 0) =
      binomTail (suffixSet σ i).card (1 - (1 - p) ^ (prefixSet σ i).card) w := by
  set Sf := suffixSet σ i with hSf
  set q : ℝ := 1 - (1 - p) ^ (prefixSet σ i).card with hq
  have hq' : (1 - p) ^ (prefixSet σ i).card = 1 - q := by rw [hq]; ring
  have hmaps : ∀ G ∈ (univ : Finset (SimpleGraph V)), activeSuffix G σ i ∈ Sf.powerset :=
    fun G _ => mem_powerset.2 (activeSuffix_subset_suffixSet G σ i)
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hinner : ∀ B ∈ Sf.powerset,
      (∑ G ∈ univ.filter (fun G => activeSuffix G σ i = B),
        (if w < vertexSepAt G σ i then gnpWeight p G else 0)) =
        if w < B.card then q ^ B.card * (1 - q) ^ (Sf.card - B.card) else 0 := by
    intro B hB
    have hB' := mem_powerset.1 hB
    split_ifs with hw
    · rw [← hq', ← sum_gnpWeight_activeSuffix_eq p σ i hB']
      refine sum_congr rfl (fun G hG => ?_)
      have hGB := (mem_filter.1 hG).2
      unfold vertexSepAt
      rw [hGB]
      simp only [hw, ite_true]
    · refine sum_eq_zero (fun G hG => ?_)
      unfold vertexSepAt
      rw [(mem_filter.1 hG).2]
      simp only [hw, ite_false]
  rw [sum_congr rfl hinner,
    sum_powerset_apply_card (fun j => if w < j then q ^ j * (1 - q) ^ (Sf.card - j) else 0)]
  unfold binomTail
  rw [sum_filter]
  refine sum_congr rfl (fun j _ => ?_)
  split_ifs <;> simp [nsmul_eq_mul]

/-! ### The union bound over positions, and the pathwidth -/

open scoped Classical in
/-- **The random-ordering bound, finite form.** For `0 ≤ p ≤ 1` and any fixed layout `σ`
(the identity, say), the `G(n, p)` weight of the graphs whose vertex separation along `σ`
exceeds `w` is at most `∑_{i < n} P(Bin(n − i − 1, 1 − (1 − p)^(i + 1)) > w)`. -/
theorem sum_gnpWeight_vertexSepOfLayout_gt_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : LinearLayout V) (w : ℕ) :
    ∑ G : SimpleGraph V, (if w < vertexSepOfLayout G σ then gnpWeight p G else 0) ≤
      ∑ i ∈ range (Fintype.card V),
        binomTail (Fintype.card V - (i + 1)) (1 - (1 - p) ^ (i + 1)) w := by
  have hnn : ∀ (G : SimpleGraph V) (i : ℕ),
      0 ≤ (if w < vertexSepAt G σ i then gnpWeight p G else 0) := by
    intro G i
    split_ifs
    · exact gnpWeight_nonneg hp0 hp1 G
    · exact le_rfl
  calc ∑ G : SimpleGraph V, (if w < vertexSepOfLayout G σ then gnpWeight p G else 0)
      ≤ ∑ G : SimpleGraph V, ∑ i ∈ range (Fintype.card V),
          (if w < vertexSepAt G σ i then gnpWeight p G else 0) := by
        refine sum_le_sum (fun G _ => ?_)
        split_ifs with hw
        · obtain ⟨i, hi, hwi⟩ : ∃ i ∈ range (Fintype.card V), w < vertexSepAt G σ i := by
            unfold vertexSepOfLayout at hw
            split_ifs at hw with hn
            · omega
            · rw [lt_sup'_iff] at hw
              obtain ⟨i, _, hi⟩ := hw
              exact ⟨i.val, mem_range.2 i.isLt, hi⟩
          calc gnpWeight p G = (if w < vertexSepAt G σ i then gnpWeight p G else 0) := by
                simp only [hwi, ite_true]
            _ ≤ _ := single_le_sum (fun j _ => hnn G j) hi
        · exact sum_nonneg (fun i _ => hnn G i)
    _ = ∑ i ∈ range (Fintype.card V), ∑ G : SimpleGraph V,
          (if w < vertexSepAt G σ i then gnpWeight p G else 0) := sum_comm
    _ = _ := by
        refine sum_congr rfl (fun i hi => ?_)
        have hi' := mem_range.1 hi
        rw [sum_gnpWeight_vertexSepAt_gt, card_prefixSet σ hi']
        congr 1
        have := card_prefixSet_add_card_suffixSet σ i rfl
        rw [card_prefixSet σ hi'] at this
        omega

open scoped Classical in
/-- **The random-ordering bound on the pathwidth.** For `0 ≤ p ≤ 1`, the `G(n, p)` weight of
the graphs of pathwidth above `w` is at most
`∑_{i < n} P(Bin(n − i − 1, 1 − (1 − p)^(i + 1)) > w)`: the vertex separation of any one
layout, the identity say, bounds the pathwidth. -/
theorem sum_gnpWeight_pathwidth_gt_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (w : ℕ) :
    ∑ G ∈ (univ : Finset (SimpleGraph V)).filter (fun G => w < pathwidth G), gnpWeight p G ≤
      ∑ i ∈ range (Fintype.card V),
        binomTail (Fintype.card V - (i + 1)) (1 - (1 - p) ^ (i + 1)) w := by
  obtain ⟨σ⟩ : Nonempty (LinearLayout V) := ⟨Fintype.equivFin V⟩
  refine le_trans ?_ (sum_gnpWeight_vertexSepOfLayout_gt_le p hp0 hp1 σ w)
  rw [sum_filter]
  refine sum_le_sum (fun G _ => ?_)
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (lt_of_lt_of_le h1 (pathwidth_le_vertexSepOfLayout G σ)) h2
  · exact gnpWeight_nonneg hp0 hp1 G
  · exact le_rfl

open scoped Classical in
/-- The complementary form: `P(pathwidth ≤ w) ≥ 1 − ∑_{i < n} P(Bin(n − i − 1, 1 − (1 − p)^(i + 1)) > w)`. -/
theorem sum_gnpWeight_graphsOfPathwidthLe_ge (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (w : ℕ) :
    1 - ∑ i ∈ range (Fintype.card V),
        binomTail (Fintype.card V - (i + 1)) (1 - (1 - p) ^ (i + 1)) w ≤
      ∑ G ∈ graphsOfPathwidthLe (V := V) w, gnpWeight p G := by
  have hsplit := sum_filter_add_sum_filter_not (univ : Finset (SimpleGraph V))
    (fun G => pathwidth G ≤ w) (gnpWeight p)
  rw [sum_gnpWeight_univ] at hsplit
  have h1 : (univ : Finset (SimpleGraph V)).filter (fun G => pathwidth G ≤ w) =
      graphsOfPathwidthLe w := by
    ext G
    simp [mem_graphsOfPathwidthLe]
  have h2 : (univ : Finset (SimpleGraph V)).filter (fun G => ¬ pathwidth G ≤ w) =
      univ.filter (fun G => w < pathwidth G) := by
    ext G
    simp [not_le]
  rw [h1, h2] at hsplit
  have := sum_gnpWeight_pathwidth_gt_le (V := V) p hp0 hp1 w
  linarith

end MOSPFormalization
