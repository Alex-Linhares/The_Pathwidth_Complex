/-
Copyright (c) 2026 Alexandre Linhares. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Staircases: the layout structure of `pw ≤ n − s`, and the corner-block first moment

`reports/dense_staircase.md`. A *generalised staircase of size `s = m + 1`* in a graph
`G` is a pair of injective sequences `v, u : Fin m → V` with `u i ∉ {v j : i + j < m}`
and `u i` non-adjacent to every such `v j` (0-indexed; in the report's 1-indexed form
`u_i` is non-adjacent to `v_1, …, v_{s−i}`). A *staircase* has in addition all `2m`
vertices distinct — that is exactly the structure of a layout of *bandwidth* `≤ n − s`
(first `s − 1` and last `s − 1` positions), the object of Kuang & McDiarmid (1985).

## Main results

* `pathwidth_le_of_isGenStaircase` — a generalised staircase of size `m + 1` gives
  `pathwidth G ≤ n − (m + 1)`: lay `v` out first (`exists_layout_prefix`), then at
  any prefix of size `t ≤ m` the vertices `u 0, …, u (m − t)` are inactive suffix
  vertices (`vertexSepAt_le_of_isGenStaircase`).
* `exists_isGenStaircase_of_pathwidth_le` — the converse: a layout of width
  `≤ n − s` has at least `s − t` inactive suffix vertices at prefix size `t`, and the
  `u`'s are drawn greedily (`exists_injOn_mem`, `|C i| ≥ i + 1` suffices; the sets
  need not be nested). So **`pw ≤ n − s` iff a generalised staircase of size `s`
  exists**, both directions, no `sorry`.
* `blockCost s a b = #{(i, j) ∈ Fin b × Fin a : i + j + 1 < s}` — the forced non-edges
  of the *corner block* `v 0 … v (a−1)`, `u 0 … u (b−1)` of a staircase of size `s`;
  `forcedSet_card` — on a block cut from a generalised staircase the forced pairs are
  distinct and non-diagonal, so the block's event has `G(n, p)` weight exactly
  `(1 − p)^blockCost` (`sum_gnpWeight_patternGraphs_univ`, from the independence
  lemma `sum_gnpWeight_pattern` of `LayoutMoment.lean`).
* `weightedSum_graphsOfPathwidthLe_le_block` — **the corner-block first moment**:
  for `1 ≤ s ≤ n` and `a, b ≤ s − 1`,
  `P(pathwidth G(n, p) ≤ n − s) ≤ n^(a + b) · (1 − p)^(blockCost s a b)`;
  `weightedSum_pathwidth_le_block` is the same on `Fin n`. The report's §2 takes
  `a = b = ⌊(1 + √2) log_b n⌋` and gets `n − pw ≤ (2 + √2 + o(1)) log_b n` whp; the
  empty pair of `FirstMoment.lean` is the block `(t, t − 1)`, which only reaches `4`.
* `StaircaseUpperTail` — the matching upper half `n − pw ≥ (2 + √2 − o(1)) log_b n`
  whp, stated as a `Prop` and not proved here: on paper it is the second moment on
  staircases (`reports/dense_staircase.md` §3) or Kuang & McDiarmid's bandwidth bound
  with `pw ≤ bw`.

Checked before stating: `reports/scratch/dense_staircase/lemma_check.log` (every
labelled graph on `n ≤ 6` vertices, 32,768 at six, and samples at seven: zero
violations of either direction) and `tests/test_staircase_moment.py` (`blockCost`
against the Python `block_cost` on the values below).

No `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound` only.
-/

import MOSPFormalization.LayoutMoment
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option linter.unusedSectionVars false

namespace MOSPFormalization.Staircase

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Staircases -/

/-- A generalised staircase of size `m + 1`: `u i` avoids and is non-adjacent to every
`v j` with `i + j < m`. -/
structure IsGenStaircase (m : ℕ) (v u : Fin m → V) : Prop where
  v_inj : Function.Injective v
  u_inj : Function.Injective u
  ne : ∀ i j : Fin m, i.val + j.val < m → u i ≠ v j
  not_adj : ∀ i j : Fin m, i.val + j.val < m → ¬ G.Adj (u i) (v j)

/-- A staircase: a generalised one with all `2m` vertices distinct (the structure of
bandwidth `≤ n − (m + 1)`). -/
def IsStaircase (m : ℕ) (v u : Fin m → V) : Prop :=
  IsGenStaircase G m v u ∧ ∀ i j : Fin m, u i ≠ v j

theorem IsStaircase.isGenStaircase {m : ℕ} {v u : Fin m → V} (h : IsStaircase G m v u) :
    IsGenStaircase G m v u := h.1

/-! ### A layout with a prescribed ordered prefix -/

/-- Any injective `v : Fin m → V` is the ordered prefix of some layout: `σ (v j) = j`
and every other vertex sits at a position `≥ m`. -/
theorem exists_layout_prefix {m : ℕ} (v : Fin m → V) (hv : Function.Injective v)
    (hm : m ≤ Fintype.card V) :
    ∃ σ : LinearLayout V, (∀ j, (σ (v j)).val = j.val) ∧
      ∀ x, (∀ j, x ≠ v j) → m ≤ (σ x).val := by
  classical
  have hcard : Fintype.card (↥(Set.range v)ᶜ) = Fintype.card V - m := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective hv, Fintype.card_fin]
  let e₂ : ↥(Set.range v)ᶜ ≃ Fin (Fintype.card V - m) := Fintype.equivFinOfCardEq hcard
  let f : V → Fin (Fintype.card V) := fun x =>
    if h : x ∈ Set.range v then
      ⟨((Equiv.ofInjective v hv).symm ⟨x, h⟩).val,
        lt_of_lt_of_le ((Equiv.ofInjective v hv).symm ⟨x, h⟩).isLt hm⟩
    else ⟨m + (e₂ ⟨x, h⟩).val, by have := (e₂ ⟨x, h⟩).isLt; omega⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    by_cases hx : x ∈ Set.range v <;> by_cases hy : y ∈ Set.range v
    · simp only [f, hx, hy, dite_true, Fin.mk.injEq] at hxy
      have := (Equiv.ofInjective v hv).symm.injective (Fin.ext hxy)
      exact Subtype.ext_iff.1 this
    · simp only [f, hx, hy, dite_true, dite_false, Fin.mk.injEq] at hxy
      have := ((Equiv.ofInjective v hv).symm ⟨x, hx⟩).isLt
      omega
    · simp only [f, hx, hy, dite_true, dite_false, Fin.mk.injEq] at hxy
      have := ((Equiv.ofInjective v hv).symm ⟨y, hy⟩).isLt
      omega
    · simp only [f, hx, hy, dite_false, Fin.mk.injEq] at hxy
      have h1 : e₂ ⟨x, hx⟩ = e₂ ⟨y, hy⟩ := Fin.ext (by omega)
      exact Subtype.ext_iff.1 (e₂.injective h1)
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, by simp⟩
  refine ⟨Equiv.ofBijective f hbij, fun j => ?_, fun x hx => ?_⟩
  · have hmem : v j ∈ Set.range v := ⟨j, rfl⟩
    show (f (v j)).val = j.val
    simp only [f, hmem, dite_true]
    exact congrArg Fin.val (Equiv.ofInjective_symm_apply hv j)
  · have hx' : x ∉ Set.range v := fun ⟨j, hj⟩ => hx j hj.symm
    show m ≤ (f x).val
    simp only [f, hx', dite_false]
    exact Nat.le_add_right _ _

/-! ### A generalised staircase bounds the width of that layout -/

theorem vertexSepAt_le_of_isGenStaircase {m : ℕ} {v u : Fin m → V}
    (h : IsGenStaircase G m v u) (σ : LinearLayout V)
    (hσv : ∀ j, (σ (v j)).val = j.val) (hσ : ∀ x, (∀ j, x ≠ v j) → m ≤ (σ x).val)
    (i : ℕ) (hi : i < Fintype.card V) :
    vertexSepAt G σ i ≤ Fintype.card V - (m + 1) := by
  have hsuf := card_suffixSet σ i hi
  have hle := vertexSepAt_le_card_suffixSet G σ i
  by_cases him : i < m
  · -- the `m − i` vertices `u k`, `k < m − i`, are inactive suffix vertices
    let g : Fin (m - i) → V := fun k => u ⟨k.val, by omega⟩
    have hg : Function.Injective g := by
      intro a b hab
      have := h.u_inj hab
      exact Fin.ext (Fin.mk.inj_iff.1 this)
    have hsub : (univ : Finset (Fin (m - i))).image g ⊆ inactiveSuffix G σ i := by
      intro x hx
      obtain ⟨k, _, rfl⟩ := mem_image.1 hx
      set i₀ : Fin m := ⟨k.val, by omega⟩ with hi₀
      have hk : k.val < m - i := k.isLt
      rw [inactiveSuffix, mem_sdiff, mem_suffixSet_iff, mem_activeSuffix_iff]
      have hpos : (σ (u i₀)).val > i := by
        by_cases hr : ∃ j, u i₀ = v j
        · obtain ⟨j, hj⟩ := hr
          have hne := h.ne i₀ j
          have : ¬ (i₀.val + j.val < m) := fun hlt => hne hlt hj
          rw [hj, hσv j]
          simp only [hi₀] at this
          omega
        · have := hσ (u i₀) (fun j hj => hr ⟨j, hj⟩)
          omega
      refine ⟨hpos, fun ⟨_, x, hxp, hadj⟩ => ?_⟩
      rw [mem_prefixSet_iff] at hxp
      have hxr : ∃ j, x = v j := by
        by_contra hcon
        have := hσ x (fun j hj => hcon ⟨j, hj⟩)
        omega
      obtain ⟨j, rfl⟩ := hxr
      rw [hσv j] at hxp
      have hlt : i₀.val + j.val < m := by simp only [hi₀]; omega
      exact h.not_adj i₀ j hlt hadj.symm
    have hcardimg : ((univ : Finset (Fin (m - i))).image g).card = m - i := by
      rw [card_image_of_injective _ hg, card_univ, Fintype.card_fin]
    have h1 := card_le_card hsub
    have h2 := card_inactiveSuffix G σ i
    omega
  · omega

/-- **A generalised staircase of size `m + 1` forces `pathwidth ≤ n − (m + 1)`.** -/
theorem pathwidth_le_of_isGenStaircase {m : ℕ} {v u : Fin m → V}
    (h : IsGenStaircase G m v u) (hm : m < Fintype.card V) :
    pathwidth G ≤ Fintype.card V - (m + 1) := by
  obtain ⟨σ, hσv, hσ⟩ := exists_layout_prefix v h.v_inj hm.le
  refine (pathwidth_le_vertexSepOfLayout G σ).trans ?_
  unfold vertexSepOfLayout
  have hn : ¬ (Fintype.card V = 0) := by omega
  simp only [hn, dite_false]
  apply Finset.sup'_le
  intro i _
  exact vertexSepAt_le_of_isGenStaircase G h σ hσv hσ i.val i.isLt

theorem pathwidth_le_of_isStaircase {m : ℕ} {v u : Fin m → V}
    (h : IsStaircase G m v u) (hm : m < Fintype.card V) :
    pathwidth G ≤ Fintype.card V - (m + 1) :=
  pathwidth_le_of_isGenStaircase G h.isGenStaircase hm

/-! ### The converse: a narrow layout contains a generalised staircase -/

/-- Greedy selection: from sets `C i` with `|C i| ≥ i + 1` for `i < m`, distinct
representatives `u i ∈ C i`. -/
theorem exists_injOn_mem [Nonempty V] (C : ℕ → Finset V) (m : ℕ)
    (hC : ∀ i < m, i + 1 ≤ (C i).card) :
    ∃ u : ℕ → V, (∀ i < m, u i ∈ C i) ∧ ∀ i < m, ∀ j < m, u i = u j → i = j := by
  induction m with
  | zero =>
    obtain ⟨x⟩ := ‹Nonempty V›
    exact ⟨fun _ => x, fun i hi => absurd hi (Nat.not_lt_zero _),
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨u, hmem, hinj⟩ := ih (fun i hi => hC i (Nat.lt_succ_of_lt hi))
    have hcard : ((range m).image u).card < (C m).card := by
      have := hC m (Nat.lt_succ_self m)
      have := (card_image_le (s := range m) (f := u)).trans (by rw [card_range])
      omega
    obtain ⟨x, hxC, hx⟩ : ∃ x ∈ C m, x ∉ (range m).image u := by
      by_contra hcon
      have hsub : C m ⊆ (range m).image u := fun y hy =>
        by_contra fun hny => hcon ⟨y, hy, hny⟩
      exact absurd (card_le_card hsub) (not_le.2 hcard)
    refine ⟨fun i => if i < m then u i else x, fun i hi => ?_, fun i hi j hj hij => ?_⟩
    · by_cases him : i < m
      · simp only [him, ite_true]; exact hmem i him
      · have : i = m := by omega
        subst this
        simp only [lt_irrefl, ite_false]; exact hxC
    · by_cases him : i < m <;> by_cases hjm : j < m
      · simp only [him, hjm, ite_true] at hij
        exact hinj i him j hjm hij
      · simp only [him, hjm, ite_true, ite_false] at hij
        exact absurd (mem_image.2 ⟨i, mem_range.2 him, hij⟩) hx
      · simp only [him, hjm, ite_true, ite_false] at hij
        exact absurd (mem_image.2 ⟨j, mem_range.2 hjm, hij.symm⟩) hx
      · omega

/-- **A layout of width `≤ n − s` contains a generalised staircase of size `s`.** -/
theorem exists_isGenStaircase_of_pathwidth_le {s : ℕ} (hs : 1 ≤ s)
    (hsn : s ≤ Fintype.card V) (h : pathwidth G ≤ Fintype.card V - s) :
    ∃ v u : Fin (s - 1) → V, IsGenStaircase G (s - 1) v u := by
  classical
  have hV : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  -- an optimal layout
  have hne : (Set.range (fun σ : LinearLayout V => vertexSepOfLayout G σ)).Nonempty :=
    ⟨_, ⟨Fintype.equivFin V, rfl⟩⟩
  obtain ⟨σ, hσ⟩ := Nat.sInf_mem hne
  have hσk : vertexSepOfLayout G σ = pathwidth G := by
    rw [← vertexSeparation_eq_pathwidth]; exact hσ
  set m := s - 1 with hm
  let v : Fin m → V := fun j => σ.symm ⟨j.val, by omega⟩
  have hv : Function.Injective v := by
    intro a b hab
    have := σ.symm.injective hab
    exact Fin.ext (Fin.mk.inj_iff.1 this)
  have hσv : ∀ j : Fin m, (σ (v j)).val = j.val := by
    intro j; simp [v]
  -- the closed sets, one level per `u`
  let C : ℕ → Finset V := fun i => inactiveSuffix G σ (m - 1 - i)
  have hC : ∀ i < m, i + 1 ≤ (C i).card := by
    intro i hi
    have hpos : m - 1 - i < Fintype.card V := by omega
    have h1 := card_inactiveSuffix G σ (m - 1 - i)
    have h2 := card_suffixSet σ (m - 1 - i) hpos
    have h3 := vertexSepAt_le_vertexSepOfLayout G σ ⟨m - 1 - i, hpos⟩
    simp only at h3
    simp only [C]
    omega
  obtain ⟨u₀, hmem, hinj⟩ := exists_injOn_mem C m hC
  refine ⟨v, fun i => u₀ i.val, hv, fun a b hab => Fin.ext (hinj a.val a.isLt b.val b.isLt hab),
    fun i j hij => ?_, fun i j hij => ?_⟩
  · -- `u i` is in the suffix at position `m − 1 − i`, `v j` in its prefix
    intro heq
    have hu := hmem i.val i.isLt
    simp only [C, inactiveSuffix, mem_sdiff, mem_suffixSet_iff] at hu
    have := hσv j
    rw [← heq] at this
    omega
  · have hu := hmem i.val i.isLt
    have hvj : v j ∈ prefixSet σ (m - 1 - i.val) := by
      rw [mem_prefixSet_iff, hσv j]; omega
    exact fun hadj => not_adj_prefix_inactiveSuffix G σ (m - 1 - i.val) hvj hu hadj.symm

/-- The two directions together: `pw ≤ n − s` iff a generalised staircase of size `s`
exists (`1 ≤ s ≤ n`). -/
theorem pathwidth_le_iff_exists_isGenStaircase {s : ℕ} (hs : 1 ≤ s) (hsn : s ≤ Fintype.card V) :
    pathwidth G ≤ Fintype.card V - s ↔ ∃ v u : Fin (s - 1) → V, IsGenStaircase G (s - 1) v u := by
  refine ⟨exists_isGenStaircase_of_pathwidth_le G hs hsn, fun ⟨v, u, h⟩ => ?_⟩
  have := pathwidth_le_of_isGenStaircase G h (by omega)
  have hs' : s - 1 + 1 = s := by omega
  rwa [hs'] at this

/-! ### The corner block and its forced non-edges -/

/-- The index pairs `(i, j) ∈ Fin b × Fin a` with `i + j + 1 < s`: in 1-indexed terms,
`u_i ~/~ v_j` for `i + j ≤ s`. -/
def blockIndex (s a b : ℕ) : Finset (Fin b × Fin a) :=
  univ.filter (fun ij => ij.1.val + ij.2.val + 1 < s)

/-- `c(s, a, b)`, the number of forced non-edges of the corner block `(a, b)` —
`learning.staircase_moment.block_cost`. -/
def blockCost (s a b : ℕ) : ℕ := (blockIndex s a b).card

example : blockCost 7 4 4 = 15 := by decide
example : blockCost 5 4 2 = 7 := by decide
example : blockCost 6 5 5 = 15 := by decide
example : blockCost 3 1 1 = 1 := by decide

/-- The forced pairs `s(u i, v j)`, `(i, j) ∈ blockIndex s a b`. -/
def forcedSet {a b : ℕ} (v : Fin a → V) (u : Fin b → V) (s : ℕ) : Finset (Sym2 V) :=
  (blockIndex s a b).image (fun ij => s(u ij.1, v ij.2))

/-- The tuples whose forced set is a set of `blockCost s a b` non-diagonal pairs. -/
noncomputable def blockTuples (s a b : ℕ) : Finset ((Fin a → V) × (Fin b → V)) := by
  classical exact univ.filter (fun T =>
    forcedSet T.1 T.2 s ⊆ edges (⊤ : SimpleGraph V) ∧ (forcedSet T.1 T.2 s).card = blockCost s a b)

/-- Cutting a corner block out of a generalised staircase: `v ∘ castLE`, `u ∘ castLE`. -/
theorem isGenStaircase_restrict {m : ℕ} {v u : Fin m → V} (h : IsGenStaircase G m v u)
    {a b : ℕ} (ha : a ≤ m) (hb : b ≤ m) :
    ∀ i : Fin b, ∀ j : Fin a, i.val + j.val < m →
      u (Fin.castLE hb i) ≠ v (Fin.castLE ha j) ∧ ¬ G.Adj (u (Fin.castLE hb i)) (v (Fin.castLE ha j)) :=
  fun _ _ hij => ⟨h.ne _ _ hij, h.not_adj _ _ hij⟩

/-- On a block cut from a generalised staircase of size `s`, the map
`(i, j) ↦ s(u i, v j)` is injective on `blockIndex s a b` and lands in `edges ⊤`:
the forced set has exactly `blockCost s a b` pairs. -/
theorem forcedSet_card {m : ℕ} {v u : Fin m → V} (h : IsGenStaircase G m v u)
    {a b : ℕ} (ha : a ≤ m) (hb : b ≤ m) :
    (forcedSet (v ∘ Fin.castLE ha) (u ∘ Fin.castLE hb) (m + 1)).card = blockCost (m + 1) a b ∧
    forcedSet (v ∘ Fin.castLE ha) (u ∘ Fin.castLE hb) (m + 1) ⊆ edges (⊤ : SimpleGraph V) := by
  have hmem : ∀ ij ∈ blockIndex (m + 1) a b, ij.1.val + ij.2.val < m := by
    intro ij hij
    simp only [blockIndex, mem_filter, mem_univ, true_and] at hij
    omega
  constructor
  · unfold forcedSet blockCost
    apply card_image_of_injOn
    intro ij hij ij' hij' heq
    simp only [Function.comp] at heq
    have h1 := hmem ij hij
    have h2 := hmem ij' hij'
    rcases Sym2.eq_iff.1 heq with ⟨hu, hv⟩ | ⟨huv, hvu⟩
    · have hi := (h.u_inj.comp (Fin.castLE_injective hb)) hu
      have hj := (h.v_inj.comp (Fin.castLE_injective ha)) hv
      exact Prod.ext hi hj
    · -- `u i = v j'` and `u i' = v j` contradict `ne` unless `i + j' ≥ m` and `i' + j ≥ m`
      have hA : ¬ (ij.1.val + ij'.2.val < m) :=
        fun hlt => h.ne (Fin.castLE hb ij.1) (Fin.castLE ha ij'.2) hlt huv
      have hB : ¬ (ij'.1.val + ij.2.val < m) :=
        fun hlt => h.ne (Fin.castLE hb ij'.1) (Fin.castLE ha ij.2) hlt hvu.symm
      omega
  · intro e he
    unfold forcedSet at he
    obtain ⟨ij, hij, rfl⟩ := mem_image.1 he
    rw [mem_edges_top, Sym2.mk_isDiag_iff]
    exact h.ne _ _ (hmem ij hij)

/-- A graph of pathwidth `≤ n − s` avoids the forced set of some block tuple. -/
theorem exists_blockTuple_of_pathwidth_le {s a b : ℕ} (hs : 1 ≤ s) (hsn : s ≤ Fintype.card V)
    (ha : a ≤ s - 1) (hb : b ≤ s - 1) (h : pathwidth G ≤ Fintype.card V - s) :
    ∃ T ∈ blockTuples (V := V) s a b, G ∈ patternGraphs univ (forcedSet T.1 T.2 s) ∅ := by
  classical
  obtain ⟨v, u, hvu⟩ := exists_isGenStaircase_of_pathwidth_le G hs hsn h
  have hs' : s - 1 + 1 = s := by omega
  obtain ⟨hcard, hsub⟩ := forcedSet_card G hvu ha hb
  rw [hs'] at hcard hsub
  refine ⟨(v ∘ Fin.castLE ha, u ∘ Fin.castLE hb), ?_, ?_⟩
  · simp only [blockTuples, mem_filter, mem_univ, true_and]
    exact ⟨hsub, hcard⟩
  · rw [mem_patternGraphs]
    refine ⟨mem_univ _, eq_empty_iff_forall_notMem.2 fun e he => ?_⟩
    rw [mem_inter] at he
    obtain ⟨heG, heF⟩ := he
    unfold forcedSet at heF
    obtain ⟨ij, hij, rfl⟩ := mem_image.1 heF
    simp only [blockIndex, mem_filter, mem_univ, true_and] at hij
    rw [mem_edges, SimpleGraph.mem_edgeSet] at heG
    exact hvu.not_adj _ _ (by simp only [Fin.val_castLE]; omega) heG

/-! ### The weight of a forced set, and the union bound -/

theorem sum_gnpWeight_univ_eq_one (p : ℝ) :
    ∑ G : SimpleGraph V, gnpWeight p G = 1 := by
  have h := sum_gnpWeight_emptyPairGraphs (V := V) (A := ∅) (R := ∅) (disjoint_empty_left _) p
  have huniv : emptyPairGraphs (V := V) ∅ ∅ = univ := by
    ext G; simp [mem_emptyPairGraphs, IsEmptyPair]
  rw [huniv] at h
  simpa using h

/-- The `G(n, p)` weight of "every pair of `F` is a non-edge" is `(1 − p)^|F|` for
`F ⊆ edges ⊤`. -/
theorem sum_gnpWeight_patternGraphs_univ (p : ℝ) {F : Finset (Sym2 V)}
    (hF : F ⊆ edges (⊤ : SimpleGraph V)) :
    ∑ G ∈ patternGraphs univ F ∅, gnpWeight p G = (1 - p) ^ F.card := by
  have hdet : DeterminedOutside (univ : Finset (SimpleGraph V)) F := fun _ _ _ => by simp
  rw [sum_gnpWeight_pattern p univ hF (empty_subset _) hdet, sum_gnpWeight_univ_eq_one]
  simp

/-- **The corner-block first moment**: for `1 ≤ s ≤ n` and `a, b ≤ s − 1`,
`P(pathwidth G(n, p) ≤ n − s) ≤ n^(a + b) · (1 − p)^(blockCost s a b)`. -/
theorem weightedSum_graphsOfPathwidthLe_le_block (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {s a b : ℕ} (hs : 1 ≤ s) (hsn : s ≤ Fintype.card V) (ha : a ≤ s - 1) (hb : b ≤ s - 1) :
    ∑ G ∈ graphsOfPathwidthLe (V := V) (Fintype.card V - s), gnpWeight p G ≤
      (Fintype.card V : ℝ) ^ (a + b) * (1 - p) ^ blockCost s a b := by
  classical
  have hsub : graphsOfPathwidthLe (V := V) (Fintype.card V - s) ⊆
      (blockTuples (V := V) s a b).biUnion (fun T => patternGraphs univ (forcedSet T.1 T.2 s) ∅) := by
    intro G hG
    rw [mem_graphsOfPathwidthLe] at hG
    obtain ⟨T, hT, hGT⟩ := exists_blockTuple_of_pathwidth_le G hs hsn ha hb hG
    exact mem_biUnion.2 ⟨T, hT, hGT⟩
  have hq : 0 ≤ 1 - p := by linarith
  calc ∑ G ∈ graphsOfPathwidthLe (V := V) (Fintype.card V - s), gnpWeight p G
      ≤ ∑ G ∈ (blockTuples (V := V) s a b).biUnion
          (fun T => patternGraphs univ (forcedSet T.1 T.2 s) ∅), gnpWeight p G :=
        sum_le_sum_of_subset_of_nonneg hsub (fun G _ _ => gnpWeight_nonneg hp0 hp1 G)
    _ ≤ ∑ T ∈ blockTuples (V := V) s a b,
          ∑ G ∈ patternGraphs univ (forcedSet T.1 T.2 s) ∅, gnpWeight p G :=
        sum_biUnion_le_sum_of_nonneg _ _ _ (gnpWeight_nonneg hp0 hp1)
    _ = ∑ T ∈ blockTuples (V := V) s a b, (1 - p) ^ blockCost s a b := by
        refine sum_congr rfl (fun T hT => ?_)
        simp only [blockTuples, mem_filter, mem_univ, true_and] at hT
        rw [sum_gnpWeight_patternGraphs_univ p hT.1, hT.2]
    _ = ((blockTuples (V := V) s a b).card : ℝ) * (1 - p) ^ blockCost s a b := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card V : ℝ) ^ (a + b) * (1 - p) ^ blockCost s a b := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hq _)
        have h1 : (blockTuples (V := V) s a b).card ≤ Fintype.card V ^ (a + b) := by
          refine (card_le_univ _).trans (le_of_eq ?_)
          rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, pow_add]
        exact_mod_cast h1

/-- The same on `Fin n`: `P(pathwidth G(n, p) ≤ n − s) ≤ n^(a + b) (1 − p)^(blockCost s a b)`. -/
theorem weightedSum_pathwidth_le_block (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {s a b : ℕ} (hs : 1 ≤ s) (hsn : s ≤ n) (ha : a ≤ s - 1) (hb : b ≤ s - 1) :
    ∑ G ∈ graphsOfPathwidthLe (V := Fin n) (n - s), gnpWeight p G ≤
      (n : ℝ) ^ (a + b) * (1 - p) ^ blockCost s a b := by
  have := weightedSum_graphsOfPathwidthLe_le_block (V := Fin n) p hp0 hp1 hs
    (by simpa using hsn) ha hb
  simpa using this

/-- **Not proved here.** The matching upper half, `n − pw(G(n, p)) ≥ (2 + √2 − ε) log_b n`
with probability `→ 1` for every `ε > 0`: on paper by the second moment on staircases
(`reports/dense_staircase.md` §3) or from `pw ≤ bw` and Kuang & McDiarmid (1985). -/
def StaircaseUpperTail (p : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
    1 - ε ≤ ∑ G ∈ graphsOfPathwidthLe (V := Fin n)
      (n - ⌊(2 + Real.sqrt 2 - ε) * Real.log n / Real.log (1 / (1 - p))⌋₊), gnpWeight p G

end MOSPFormalization.Staircase
