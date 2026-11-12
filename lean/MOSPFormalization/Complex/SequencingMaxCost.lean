/-
Copyright (c) 2026 Alexandre Linhares. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Sequencing to minimize maximum cumulative cost (SS7) contains MOSP

Garey & Johnson (1979), p. 238, problem SS7, SEQUENCING TO MINIMIZE MAXIMUM
CUMULATIVE COST (Abdel-Wahab 1976; Abdel-Wahab & Kameda 1978).

## The source's definition

Instance: a set `T` of tasks, a partial order `≺` on `T`, for each task a cost
`c(t) ∈ ℤ` (positive or negative), and a bound `K ∈ ℤ`. Question: is there a
one-processor schedule `σ` for `T` that obeys the precedence constraints and
whose every prefix has cumulative cost at most `K`, i.e.
`∑ {c(t) : σ(t) ≤ i} ≤ K` for every position `i`? Garey & Johnson record it as
NP-complete "even if all `c(t) ∈ {−1, 0, 1}`" (cited, not proved here).

Formalised here without reference to stacks or pathwidth:

* `SS7Instance T` — a precedence relation `prec` (any relation; the value
  depends only on its transitive closure, `isLinearExtension_transGen_iff`,
  so a partial order is accepted and nothing more is required) and a cost
  `cost : T → ℤ`;
* `IsLinearExtension σ` — the layout `σ` obeys `prec`;
* `prefixCost σ i` — the sum of the costs of the tasks at positions `≤ i`;
* `WithinCost K` — Garey & Johnson's question for the bound `K`;
* `ss7Value` — the least natural `K` with `WithinCost K` (every instance this
  file compares with MOSP has non-negative prefix sums; a negative optimum is
  truncated to `0`, and an instance with no linear extension gets `0` too).

## MOSP is a special case: the embedding `toSS7`

A MOSP instance on customers `C` and patterns `P` becomes the SS7 instance on
the tasks `C ⊕ (C ⊕ P)`: `open c = Sum.inl c` at cost `+1`,
`close c = Sum.inr (Sum.inl c)` at cost `−1`, and each pattern
`Sum.inr (Sum.inr p)` at cost `0`. The precedence is `open c ≺ close c` for
**every** customer, and `open c ≺ p ≺ close c` whenever `c` requires `p`;
nothing else. All costs lie in `{−1, 0, 1}` (`toSS7_cost_mem`), the
restriction Garey & Johnson name.

The pair `open c ≺ close c` for a customer requiring nothing is essential:
without it such a customer could close before it opens and lower every prefix
sum by one. Measured: the equality below fails on 232 of the 673 matrices
(`ss7_embed_exhaustive.log`), every one with a customer requiring nothing.

The prefix sum of a linear extension at position `i` is the number of
customers whose open task is at or before `i` and whose close task is after
`i` (`prefixCost_toSS7`): the close task of a customer forces its open task,
and patterns cost nothing.

**Pattern order to linear extension** (`exists_linearExtension_of_layout`).
Given a pattern order `σ`, sort the tasks by the key `embedKey`: for a customer
`c` with a pattern, `open c ↦ 3·first c`, `close c ↦ 3·last c + 2`, where
`first`/`last` are the positions of its earliest and latest patterns
(`firstPos`, `lastPos`); every pattern `p ↦ 3·σ p + 1`; a customer `c` with no
pattern is parked after everything, `open c ↦ 3|P| + 3·e c`,
`close c ↦ 3|P| + 3·e c + 2`, with `e : C ≃ Fin |C|`. Keys strictly increase
along every precedence, so the sorted layout (`exists_layout_sorted`) is a
linear extension. At a task of key `K < 3|P|` every customer counted by
`prefixCost_toSS7` has a pattern and is open at step `K / 3` of `σ`, so the
prefix sum is at most `openStacksAt σ (K / 3) ≤ maxOpenStacks σ`; at a task of
key `K ≥ 3|P|` the counted customers have no pattern and a key window of width
`2` pins the customer down, so the prefix sum is at most `1`
(`card_openAt_le`). Hence `prefixCost ≤ max (maxOpenStacks σ) 1`, and with
some requirement `maxOpenStacks σ ≥ 1`.

**Linear extension to pattern order** (`exists_layout_of_linearExtension`), no
hypothesis: order the patterns by their position in the linear extension `τ`.
A customer open at step `j` of that order has a pattern at or before step `j`
and one at or after, so its open task precedes and its close task follows the
`τ`-position of the pattern at step `j`; the open stacks at `j` inject into the
set `prefixCost_toSS7` counts there.

**The equalities** (`withinCost_toSS7_iff`, `ss7Value_toSS7`,
`ss7Value_toSS7_eq_pathwidth_add_one`): when some customer requires some
pattern, `ss7Value (toSS7 M) = mospValue M = pathwidth (mospGraph M) + 1`.

## Edge cases

Without any requirement `mospValue M = 0` (`mospValue_eq_zero_of_forall_not`)
while `ss7Value (toSS7 M) = 1` when there is a customer
(`ss7Value_toSS7_eq_one_of_forall_not`: some open task is placed with its
close task later, so some prefix sum is `≥ 1`; opening and closing one
customer at a time keeps every prefix sum in `{0, 1}`), and `0` with no
customer (`ss7Value_toSS7_eq_zero_of_isEmpty`). So `hreq` is exactly the
hypothesis the equality needs, as for `mospValue_eq_pathwidth_add_one`.
Measured edge cases are tabulated in `ss7_embed_exhaustive.log`.

## Two negative results: a container, not a member of the complex

* The comparability graph and the costs do not determine the value
  (`exists_same_compGraph_cost_ne_ss7Value`). `compGraph` joins two tasks
  that are comparable; `dual` reverses the order and keeps the costs, and has
  the same comparability graph (`compGraph_dual`). On two tasks `a ≺ b` with
  costs `+1, −1` the value is `1`, on the dual it is `0`
  (`ss7Value_dualWitness`, `ss7Value_dualWitness_dual`, `ss7Value_dual_ne`).
* No graph built from pairwise-local data — the two costs and the mutual
  order of the two tasks (`Mutual`, `SS7Instance.mutualOrder`, `localGraph`) — has
  `ss7Value = pathwidth + c` for any constant `c` (`no_local_derived_graph`),
  nor within any band `c` (`no_local_derived_graph_band`). The witnesses are
  the antichains `antichain n` of `n` tasks at cost `+1` (value `n`,
  `ss7Value_antichain`) and the matched pairs `pairsInstance k`: `k` pairs
  `open_i ≺ close_i` at costs `+1, −1`, which is the embedding of `k`
  customers and no pattern relabelled onto `Fin _`, of value `1`
  (`ss7Value_pairsInstance`). An antichain of two tasks needs an edge, so
  the rule must join two `+1` tasks in mutual order `none`; then the `k`
  open tasks of the matched pairs form a clique, so the pathwidth is at
  least `k − 1` while the value is `1`.

## Brute-force checks

`reports/scratch/ss7_register_sufficiency/ss7_embed_exhaustive.py`: on every
0/1 matrix with at most 3 customers and 3 patterns and some requirement (673
matrices) `ss7Value (toSS7 M) = mospValue M = pathwidth + 1` with 0
mismatches, and the equality fails on 232 of them when the pair
`open c ≺ close c` is dropped; the 16 shapes without a requirement are listed
with both values. `ss7_witnesses.py`: the dual pair has values `1` and `0`;
`antichain k` has value `k` and the matched pairs value `1` for `k ≤ 4`.
-/

import MOSPFormalization.MOSPGraph
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin

set_option linter.unusedSectionVars false

namespace MOSPFormalization

namespace Complex

/-! ### The problem of Garey & Johnson -/

/-- An SS7 instance (Garey & Johnson 1979, p. 238): tasks `T`, a precedence
relation (G&J: a partial order; the value depends only on its transitive
closure, so any relation is accepted) and integer costs. -/
structure SS7Instance (T : Type*) where
  prec : T → T → Prop
  cost : T → ℤ

variable {T : Type*} [Fintype T] [DecidableEq T]

namespace SS7Instance

variable (I : SS7Instance T)

/-- A one-processor schedule obeying the precedence constraints. -/
def IsLinearExtension (σ : LinearLayout T) : Prop :=
  ∀ a b, I.prec a b → σ a < σ b

/-- The sum of the costs of the tasks at positions `≤ i`. -/
def prefixCost (σ : LinearLayout T) (i : ℕ) : ℤ :=
  ∑ t ∈ Finset.univ.filter (fun t => (σ t).val ≤ i), I.cost t

/-- Garey & Johnson's question: a linear extension whose every prefix sum is
at most `K`. -/
def WithinCost (K : ℤ) : Prop :=
  ∃ σ : LinearLayout T, I.IsLinearExtension σ ∧
    ∀ i : Fin (Fintype.card T), I.prefixCost σ i.val ≤ K

/-- The optimum, as a natural number: the least `K : ℕ` with `WithinCost K`
(the prefix sums of every instance this file compares with MOSP are `≥ 0`; a
negative optimum is truncated to `0`, and `sInf ∅ = 0` when no linear
extension exists). -/
noncomputable def ss7Value : ℕ :=
  sInf {K : ℕ | I.WithinCost K}

/-- The value depends only on the transitive closure of the precedence. -/
theorem isLinearExtension_transGen_iff (σ : LinearLayout T) :
    (⟨Relation.TransGen I.prec, I.cost⟩ : SS7Instance T).IsLinearExtension σ ↔
      I.IsLinearExtension σ := by
  constructor
  · intro h a b hab
    exact h a b (Relation.TransGen.single hab)
  · intro h a b hab
    induction hab with
    | single hab => exact h _ _ hab
    | tail _ hbc ih => exact lt_trans ih (h _ _ hbc)

theorem withinCost_mono {K K' : ℤ} (h : I.WithinCost K) (hKK : K ≤ K') : I.WithinCost K' := by
  obtain ⟨σ, hσ, hK⟩ := h
  exact ⟨σ, hσ, fun i => (hK i).trans hKK⟩

theorem ss7Value_le_of_withinCost {K : ℕ} (h : I.WithinCost K) : I.ss7Value ≤ K :=
  Nat.sInf_le h

theorem withinCost_ss7Value (h : ∃ K : ℕ, I.WithinCost K) : I.WithinCost I.ss7Value :=
  Nat.sInf_mem h

theorem le_ss7Value (h : ∃ K : ℕ, I.WithinCost K) {K : ℕ}
    (hK : ∀ K' : ℕ, I.WithinCost K' → K ≤ K') : K ≤ I.ss7Value :=
  le_csInf h hK

theorem ss7Value_le_iff (h : ∃ K : ℕ, I.WithinCost K) (K : ℕ) :
    I.ss7Value ≤ K ↔ I.WithinCost K :=
  ⟨fun hle => I.withinCost_mono (I.withinCost_ss7Value h) (by exact_mod_cast hle),
    I.ss7Value_le_of_withinCost⟩

/-! ### Evaluating prefix sums -/

theorem prefixCost_eq_sum_ite (σ : LinearLayout T) (i : ℕ) :
    I.prefixCost σ i = ∑ t, if (σ t).val ≤ i then I.cost t else 0 :=
  Finset.sum_filter _ _

/-- At or beyond the last position the prefix is everything. -/
theorem prefixCost_of_card_le (σ : LinearLayout T) {i : ℕ} (hi : Fintype.card T ≤ i + 1) :
    I.prefixCost σ i = ∑ t, I.cost t := by
  unfold prefixCost
  congr 1
  apply Finset.filter_true_of_mem
  intro t _
  have := (σ t).isLt
  omega

/-- At position `0` the prefix is the first task alone. -/
theorem prefixCost_zero (σ : LinearLayout T) (h : 0 < Fintype.card T) :
    I.prefixCost σ 0 = I.cost (σ.symm ⟨0, h⟩) := by
  unfold prefixCost
  have hf : Finset.univ.filter (fun t => (σ t).val ≤ 0) = {σ.symm ⟨0, h⟩} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Equiv.eq_symm_apply, Fin.ext_iff]
    omega
  rw [hf, Finset.sum_singleton]

/-- A linear extension of a sorted layout: it suffices that a key strictly
increases along every precedence. -/
theorem isLinearExtension_of_key (f : T → ℕ) (hf : ∀ a b, I.prec a b → f a < f b)
    (σ : LinearLayout T) (hσ : ∀ u v, f u < f v → (σ u).val < (σ v).val) :
    I.IsLinearExtension σ :=
  fun a b hab => Fin.lt_def.mpr (hσ a b (hf a b hab))

/-! ### Relabelling -/

/-- The same instance on the tasks renamed along `e`. -/
def relabel {T' : Type*} (e : T ≃ T') : SS7Instance T' where
  prec a b := I.prec (e.symm a) (e.symm b)
  cost a := I.cost (e.symm a)

variable {T' : Type*} [Fintype T'] [DecidableEq T']

/-- The layout of `T` induced by a layout of the renamed tasks. -/
def relabelLayout (e : T ≃ T') (σ : LinearLayout T) : LinearLayout T' :=
  e.symm.trans (σ.trans (finCongr (Fintype.card_congr e)))

theorem relabelLayout_apply (e : T ≃ T') (σ : LinearLayout T) (a : T') :
    (relabelLayout e σ a).val = (σ (e.symm a)).val := by
  simp [relabelLayout]

theorem prefixCost_relabel (e : T ≃ T') (σ : LinearLayout T) (i : ℕ) :
    (I.relabel e).prefixCost (relabelLayout e σ) i = I.prefixCost σ i := by
  unfold prefixCost
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [← Equiv.sum_comp e.symm (fun t => if (σ t).val ≤ i then I.cost t else 0)]
  apply Finset.sum_congr rfl
  intro t _
  simp only [relabelLayout_apply, relabel]

theorem withinCost_relabel_of (e : T ≃ T') {K : ℤ} (h : I.WithinCost K) :
    (I.relabel e).WithinCost K := by
  obtain ⟨σ, hσ, hK⟩ := h
  refine ⟨relabelLayout e σ, ?_, ?_⟩
  · intro a b hab
    have := Fin.lt_def.mp (hσ _ _ hab)
    rw [Fin.lt_def, relabelLayout_apply, relabelLayout_apply]
    exact this
  · intro i
    have hi : i.val < Fintype.card T := by
      have := i.isLt; rw [Fintype.card_congr e]; exact this
    rw [prefixCost_relabel]
    exact hK ⟨i.val, hi⟩

theorem relabel_relabel_symm (e : T ≃ T') : (I.relabel e).relabel e.symm = I := by
  cases I
  simp [relabel]

theorem withinCost_relabel_iff (e : T ≃ T') (K : ℤ) :
    (I.relabel e).WithinCost K ↔ I.WithinCost K := by
  refine ⟨fun h => ?_, I.withinCost_relabel_of e⟩
  have := (I.relabel e).withinCost_relabel_of e.symm h
  rwa [relabel_relabel_symm] at this

theorem ss7Value_relabel (e : T ≃ T') : (I.relabel e).ss7Value = I.ss7Value := by
  unfold ss7Value
  congr 1
  ext K
  exact I.withinCost_relabel_iff e K

/-! ### Derived graphs -/

/-- The comparability graph of the precedence. -/
def compGraph : SimpleGraph T where
  Adj a b := a ≠ b ∧ (I.prec a b ∨ I.prec b a)
  symm := ⟨fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.symm⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

/-- The dual instance: the precedence reversed, the costs kept. -/
def dual : SS7Instance T where
  prec a b := I.prec b a
  cost := I.cost

theorem compGraph_dual : I.dual.compGraph = I.compGraph := by
  ext a b
  simp only [compGraph, dual]
  constructor
  · rintro ⟨hne, h⟩; exact ⟨hne, h.symm⟩
  · rintro ⟨hne, h⟩; exact ⟨hne, h.symm⟩

end SS7Instance

/-- The mutual order of two tasks: `a ≺ b`, `b ≺ a`, or neither. -/
inductive Mutual
  | lt
  | gt
  | none
  deriving DecidableEq

namespace SS7Instance

variable (I : SS7Instance T)

open Classical in
/-- The mutual order of `a` and `b` (`lt` if `a ≺ b`, else `gt` if `b ≺ a`,
else `none`). -/
noncomputable def mutualOrder (a b : T) : Mutual :=
  if I.prec a b then Mutual.lt else if I.prec b a then Mutual.gt else Mutual.none

theorem mutualOrder_eq_none {a b : T} (h₁ : ¬ I.prec a b) (h₂ : ¬ I.prec b a) :
    I.mutualOrder a b = Mutual.none := by
  unfold mutualOrder
  simp only [h₁, h₂, ↓reduceIte]

end SS7Instance

/-- A graph built from pairwise-local data only: the two costs and the mutual
order of the two tasks, through any rule. -/
def localGraph (rule : ℤ → ℤ → Mutual → Prop) (I : SS7Instance T) : SimpleGraph T where
  Adj a b := a ≠ b ∧ (rule (I.cost a) (I.cost b) (I.mutualOrder a b) ∨
    rule (I.cost b) (I.cost a) (I.mutualOrder b a))
  symm := ⟨fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.symm⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

/-! ### The embedding of MOSP -/

variable {C P : Type*} [Fintype C] [DecidableEq C] [Fintype P] [DecidableEq P]

namespace MOSPInstance

variable (M : MOSPInstance C P)

/-- The SS7 instance of a MOSP instance: `open c = Sum.inl c` at cost `+1`,
`close c = Sum.inr (Sum.inl c)` at cost `−1`, pattern `p = Sum.inr (Sum.inr p)`
at cost `0`; `open c ≺ close c` for every customer, and `open c ≺ p ≺ close c`
whenever `c` requires `p`. -/
def toSS7 : SS7Instance (C ⊕ (C ⊕ P)) where
  prec a b := match a, b with
    | Sum.inl c, Sum.inr (Sum.inl c') => c = c'
    | Sum.inl c, Sum.inr (Sum.inr p) => M.requires c p
    | Sum.inr (Sum.inr p), Sum.inr (Sum.inl c) => M.requires c p
    | _, _ => False
  cost := fun t => match t with
    | Sum.inl _ => 1
    | Sum.inr (Sum.inl _) => -1
    | Sum.inr (Sum.inr _) => 0

theorem toSS7_prec_open_close (c : C) : (toSS7 M).prec (Sum.inl c) (Sum.inr (Sum.inl c)) := rfl

theorem toSS7_prec_open_pattern {c : C} {p : P} (h : M.requires c p) :
    (toSS7 M).prec (Sum.inl c) (Sum.inr (Sum.inr p)) := h

theorem toSS7_prec_pattern_close {c : C} {p : P} (h : M.requires c p) :
    (toSS7 M).prec (Sum.inr (Sum.inr p)) (Sum.inr (Sum.inl c)) := h

theorem toSS7_not_prec_open_open (c c' : C) : ¬ (toSS7 M).prec (Sum.inl c) (Sum.inl c') :=
  fun h => h

/-- The costs lie in the restriction Garey & Johnson record as NP-complete. -/
theorem toSS7_cost_mem (t : C ⊕ (C ⊕ P)) : (toSS7 M).cost t ∈ ({-1, 0, 1} : Set ℤ) := by
  rcases t with c | c | p <;> simp [toSS7]

/-- The customers whose open task is at or before `i` and whose close task is
after `i`. -/
def openAt (τ : LinearLayout (C ⊕ (C ⊕ P))) (i : ℕ) : Finset C :=
  Finset.univ.filter (fun c => (τ (Sum.inl c)).val ≤ i ∧ i < (τ (Sum.inr (Sum.inl c))).val)

theorem mem_openAt_iff (τ : LinearLayout (C ⊕ (C ⊕ P))) (i : ℕ) (c : C) :
    c ∈ openAt τ i ↔ (τ (Sum.inl c)).val ≤ i ∧ i < (τ (Sum.inr (Sum.inl c))).val := by
  simp [openAt]

/-- The prefix sum of a linear extension at `i` counts the customers whose
open task is placed and whose close task is not. -/
theorem prefixCost_toSS7 (τ : LinearLayout (C ⊕ (C ⊕ P))) (hτ : (toSS7 M).IsLinearExtension τ)
    (i : ℕ) :
    (toSS7 M).prefixCost τ i =
      ((Finset.univ.filter fun c : C =>
        (τ (Sum.inl c)).val ≤ i ∧ i < (τ (Sum.inr (Sum.inl c))).val).card : ℤ) := by
  rw [SS7Instance.prefixCost, Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hpat : (∑ p : P, if (τ (Sum.inr (Sum.inr p))).val ≤ i then
      (toSS7 M).cost (Sum.inr (Sum.inr p)) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    simp [toSS7]
  rw [hpat, add_zero, ← Finset.sum_add_distrib, Finset.natCast_card_filter]
  apply Finset.sum_congr rfl
  intro c _
  have hoc : (τ (Sum.inl c)).val < (τ (Sum.inr (Sum.inl c))).val :=
    Fin.lt_def.mp (hτ _ _ (toSS7_prec_open_close M c))
  simp only [toSS7]
  split_ifs <;> omega

theorem prefixCost_toSS7_eq_card_openAt (τ : LinearLayout (C ⊕ (C ⊕ P)))
    (hτ : (toSS7 M).IsLinearExtension τ) (i : ℕ) :
    (toSS7 M).prefixCost τ i = ((openAt τ i).card : ℤ) :=
  prefixCost_toSS7 M τ hτ i

variable [DecidableRel M.requires]

/-! ### Earliest and latest patterns of a customer -/

/-- The position of the earliest pattern of `c` under `σ` (`0` for a customer
with no pattern; never used in that case). -/
noncomputable def firstPos (σ : LinearLayout P) (c : C) : ℕ :=
  if h : (M.patterns c).Nonempty then
    ((M.patterns c).image (fun p => (σ p).val)).min' (h.image _)
  else 0

/-- The position of the latest pattern of `c` under `σ`. -/
noncomputable def lastPos (σ : LinearLayout P) (c : C) : ℕ :=
  if h : (M.patterns c).Nonempty then
    ((M.patterns c).image (fun p => (σ p).val)).max' (h.image _)
  else 0

theorem patterns_nonempty_of_requires {c : C} {p : P} (h : M.requires c p) :
    (M.patterns c).Nonempty :=
  ⟨p, (M.mem_patterns_iff c p).mpr h⟩

theorem firstPos_le (σ : LinearLayout P) {c : C} {p : P} (h : M.requires c p) :
    firstPos M σ c ≤ (σ p).val := by
  have hn := patterns_nonempty_of_requires M h
  unfold firstPos
  simp only [hn, ↓reduceDIte]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem (fun p => (σ p).val) ((M.mem_patterns_iff c p).mpr h))

theorem le_lastPos (σ : LinearLayout P) {c : C} {p : P} (h : M.requires c p) :
    (σ p).val ≤ lastPos M σ c := by
  have hn := patterns_nonempty_of_requires M h
  unfold lastPos
  simp only [hn, ↓reduceDIte]
  exact Finset.le_max' _ _ (Finset.mem_image_of_mem (fun p => (σ p).val) ((M.mem_patterns_iff c p).mpr h))

theorem exists_eq_firstPos (σ : LinearLayout P) {c : C} (hn : (M.patterns c).Nonempty) :
    ∃ q, M.requires c q ∧ (σ q).val = firstPos M σ c := by
  have hmem := Finset.min'_mem ((M.patterns c).image (fun p => (σ p).val)) (hn.image _)
  obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hmem
  refine ⟨q, (M.mem_patterns_iff c q).mp hq, ?_⟩
  unfold firstPos
  simp only [hn, ↓reduceDIte]
  exact heq

theorem exists_eq_lastPos (σ : LinearLayout P) {c : C} (hn : (M.patterns c).Nonempty) :
    ∃ q, M.requires c q ∧ (σ q).val = lastPos M σ c := by
  have hmem := Finset.max'_mem ((M.patterns c).image (fun p => (σ p).val)) (hn.image _)
  obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hmem
  refine ⟨q, (M.mem_patterns_iff c q).mp hq, ?_⟩
  unfold lastPos
  simp only [hn, ↓reduceDIte]
  exact heq

theorem firstPos_le_lastPos (σ : LinearLayout P) {c : C} (hn : (M.patterns c).Nonempty) :
    firstPos M σ c ≤ lastPos M σ c := by
  obtain ⟨q, hq, heq⟩ := exists_eq_firstPos M σ hn
  rw [← heq]
  exact le_lastPos M σ hq

theorem lastPos_lt_card (σ : LinearLayout P) {c : C} (hn : (M.patterns c).Nonempty) :
    lastPos M σ c < Fintype.card P := by
  obtain ⟨q, _, heq⟩ := exists_eq_lastPos M σ hn
  rw [← heq]
  exact (σ q).isLt

/-- A customer is open at every step between its earliest and latest pattern. -/
theorem isActive_of_firstPos_le_of_le_lastPos (σ : LinearLayout P) {c : C}
    (hn : (M.patterns c).Nonempty) {j : ℕ} (h₁ : firstPos M σ c ≤ j) (h₂ : j ≤ lastPos M σ c) :
    M.isActive σ c j := by
  obtain ⟨q₁, hq₁, he₁⟩ := exists_eq_firstPos M σ hn
  obtain ⟨q₂, hq₂, he₂⟩ := exists_eq_lastPos M σ hn
  exact (M.isActive_iff σ c j).mpr ⟨⟨q₁, hq₁, by omega⟩, ⟨q₂, hq₂, by omega⟩⟩

/-! ### Pattern order to linear extension -/

/-- The sorting key of the construction: a customer with a pattern opens at
`3·first` and closes at `3·last + 2`, a pattern sits at `3·σ p + 1`, and a
customer with no pattern is parked after everything at `3|P| + 3·e c` and
`3|P| + 3·e c + 2`. -/
noncomputable def embedKey (σ : LinearLayout P) (e : C ≃ Fin (Fintype.card C)) :
    C ⊕ (C ⊕ P) → ℕ
  | Sum.inl c => if (M.patterns c).Nonempty then 3 * firstPos M σ c
      else 3 * Fintype.card P + 3 * (e c).val
  | Sum.inr (Sum.inl c) => if (M.patterns c).Nonempty then 3 * lastPos M σ c + 2
      else 3 * Fintype.card P + 3 * (e c).val + 2
  | Sum.inr (Sum.inr p) => 3 * (σ p).val + 1

theorem embedKey_open (σ : LinearLayout P) (e : C ≃ Fin (Fintype.card C)) (c : C) :
    embedKey M σ e (Sum.inl c) = if (M.patterns c).Nonempty then 3 * firstPos M σ c
      else 3 * Fintype.card P + 3 * (e c).val := rfl

theorem embedKey_close (σ : LinearLayout P) (e : C ≃ Fin (Fintype.card C)) (c : C) :
    embedKey M σ e (Sum.inr (Sum.inl c)) = if (M.patterns c).Nonempty then 3 * lastPos M σ c + 2
      else 3 * Fintype.card P + 3 * (e c).val + 2 := rfl

theorem embedKey_pattern (σ : LinearLayout P) (e : C ≃ Fin (Fintype.card C)) (p : P) :
    embedKey M σ e (Sum.inr (Sum.inr p)) = 3 * (σ p).val + 1 := rfl

/-- The key strictly increases along every precedence. -/
theorem embedKey_lt_of_prec (σ : LinearLayout P) (e : C ≃ Fin (Fintype.card C))
    (a b : C ⊕ (C ⊕ P)) (h : (toSS7 M).prec a b) : embedKey M σ e a < embedKey M σ e b := by
  rcases a with c | c | p <;> rcases b with c' | c' | p'
  · exact False.elim h
  · have hcc : c = c' := h
    subst hcc
    rw [embedKey_open, embedKey_close]
    by_cases hn : (M.patterns c).Nonempty
    · simp only [hn, ↓reduceIte]
      have := firstPos_le_lastPos M σ hn
      omega
    · simp only [hn, ↓reduceIte]
      omega
  · have hreq : M.requires c p' := h
    have hn := patterns_nonempty_of_requires M hreq
    rw [embedKey_open, embedKey_pattern]
    simp only [hn, ↓reduceIte]
    have := firstPos_le M σ hreq
    omega
  · exact False.elim h
  · exact False.elim h
  · exact False.elim h
  · exact False.elim h
  · have hreq : M.requires c' p := h
    have hn := patterns_nonempty_of_requires M hreq
    rw [embedKey_pattern, embedKey_close]
    simp only [hn, ↓reduceIte]
    have := le_lastPos M σ hreq
    omega
  · exact False.elim h

theorem isLinearExtension_of_sorted (σ : LinearLayout P) (e : C ≃ Fin (Fintype.card C))
    (τ : LinearLayout (C ⊕ (C ⊕ P)))
    (hτ : ∀ u v, embedKey M σ e u < embedKey M σ e v → (τ u).val < (τ v).val) :
    (toSS7 M).IsLinearExtension τ :=
  (toSS7 M).isLinearExtension_of_key _ (embedKey_lt_of_prec M σ e) τ hτ

/-- The count of `prefixCost_toSS7` under the sorted layout is at most
`maxOpenStacks σ`, or `1` where only customers with no pattern are open. -/
theorem card_openAt_le (σ : LinearLayout P) (e : C ≃ Fin (Fintype.card C))
    (τ : LinearLayout (C ⊕ (C ⊕ P)))
    (hτ : ∀ u v, embedKey M σ e u < embedKey M σ e v → (τ u).val < (τ v).val)
    (i : Fin (Fintype.card (C ⊕ (C ⊕ P)))) :
    (openAt τ i.val).card ≤ max (M.maxOpenStacks σ) 1 := by
  -- sortedness, contrapositive
  have hle : ∀ u v, (τ u).val ≤ (τ v).val → embedKey M σ e u ≤ embedKey M σ e v := by
    intro u v huv
    by_contra hlt
    push Not at hlt
    have := hτ v u hlt
    omega
  set t := τ.symm i with ht
  have hti : (τ t).val = i.val := by simp [ht]
  set K := embedKey M σ e t with hK
  have hopen : ∀ c ∈ openAt τ i.val, embedKey M σ e (Sum.inl c) ≤ K := by
    intro c hc
    rw [mem_openAt_iff] at hc
    exact hle _ _ (by omega)
  have hclose : ∀ c ∈ openAt τ i.val, K ≤ embedKey M σ e (Sum.inr (Sum.inl c)) := by
    intro c hc
    rw [mem_openAt_iff] at hc
    exact hle _ _ (by omega)
  by_cases hKP : K < 3 * Fintype.card P
  · -- every open customer has a pattern and is active at step `K / 3`
    have hsub : openAt τ i.val ⊆ M.activeSet σ (K / 3) := by
      intro c hc
      have h₁ := hopen c hc
      have h₂ := hclose c hc
      rw [embedKey_open] at h₁
      rw [embedKey_close] at h₂
      rw [MOSPInstance.mem_activeSet_iff]
      by_cases hn : (M.patterns c).Nonempty
      · simp only [hn, ↓reduceIte] at h₁ h₂
        exact isActive_of_firstPos_le_of_le_lastPos M σ hn (by omega) (by omega)
      · simp only [hn, ↓reduceIte] at h₁
        omega
    calc (openAt τ i.val).card ≤ (M.activeSet σ (K / 3)).card := Finset.card_le_card hsub
      _ = M.openStacksAt σ (K / 3) := M.card_activeSet σ _
      _ ≤ M.maxOpenStacks σ := M.openStacksAt_le_maxOpenStacks σ (by omega)
      _ ≤ max (M.maxOpenStacks σ) 1 := le_max_left _ _
  · -- every open customer has no pattern, and the key window pins it down
    have hnone : ∀ c ∈ openAt τ i.val, ¬ (M.patterns c).Nonempty := by
      intro c hc hn
      have h₂ := hclose c hc
      rw [embedKey_close] at h₂
      simp only [hn, ↓reduceIte] at h₂
      have := lastPos_lt_card M σ hn
      omega
    refine le_trans ?_ (le_max_right _ _)
    rw [Finset.card_le_one]
    intro c hc c' hc'
    have h₁ := hopen c hc
    have h₂ := hclose c hc
    have h₁' := hopen c' hc'
    have h₂' := hclose c' hc'
    rw [embedKey_open] at h₁ h₁'
    rw [embedKey_close] at h₂ h₂'
    simp only [hnone c hc, hnone c' hc', ↓reduceIte] at h₁ h₂ h₁' h₂'
    exact e.injective (Fin.ext (by omega))

/-- **Pattern order to linear extension**: every pattern order `σ` yields a
linear extension of `toSS7 M` whose prefix sums are all at most
`maxOpenStacks σ`, when some customer requires some pattern. -/
theorem exists_linearExtension_of_layout (hreq : ∃ c p, M.requires c p) (σ : LinearLayout P) :
    ∃ τ : LinearLayout (C ⊕ (C ⊕ P)), (toSS7 M).IsLinearExtension τ ∧
      ∀ i : Fin (Fintype.card (C ⊕ (C ⊕ P))), (toSS7 M).prefixCost τ i.val ≤ M.maxOpenStacks σ := by
  obtain ⟨τ, hτ⟩ := exists_layout_sorted (embedKey M σ (Fintype.equivFin C))
  have hext := isLinearExtension_of_sorted M σ _ τ hτ
  refine ⟨τ, hext, fun i => ?_⟩
  rw [prefixCost_toSS7_eq_card_openAt M τ hext]
  have h := card_openAt_le M σ _ τ hτ i
  rw [max_eq_left (M.one_le_maxOpenStacks σ hreq)] at h
  exact_mod_cast h

/-! ### Linear extension to pattern order -/

/-- **Linear extension to pattern order**, no hypothesis: a linear extension
with prefix sums at most `K` yields a pattern order with at most `K` open
stacks at every step. -/
theorem exists_layout_of_linearExtension (τ : LinearLayout (C ⊕ (C ⊕ P)))
    (hτ : (toSS7 M).IsLinearExtension τ) (K : ℕ)
    (hK : ∀ i : Fin (Fintype.card (C ⊕ (C ⊕ P))), (toSS7 M).prefixCost τ i.val ≤ K) :
    ∃ σ : LinearLayout P, M.maxOpenStacks σ ≤ K := by
  obtain ⟨σ, hσ⟩ := exists_layout_sorted (fun p : P => (τ (Sum.inr (Sum.inr p))).val)
  have hle : ∀ p q : P, (σ p).val ≤ (σ q).val →
      (τ (Sum.inr (Sum.inr p))).val ≤ (τ (Sum.inr (Sum.inr q))).val := by
    intro p q hpq
    by_contra hlt
    push Not at hlt
    have := hσ q p hlt
    omega
  refine ⟨σ, ?_⟩
  unfold MOSPInstance.maxOpenStacks
  by_cases hn : Fintype.card P = 0
  · simp [hn]
  · simp only [dite_eq_right hn]
    apply Finset.sup'_le
    intro j _
    set pj := σ.symm j with hpj
    have hσj : (σ pj).val = j.val := by simp [hpj]
    set i := τ (Sum.inr (Sum.inr pj)) with hi
    have hsub : M.activeSet σ j.val ⊆ openAt τ i.val := by
      intro c hc
      rw [MOSPInstance.mem_activeSet_iff, MOSPInstance.isActive_iff] at hc
      obtain ⟨⟨q, hq, hqj⟩, ⟨r, hr, hjr⟩⟩ := hc
      rw [mem_openAt_iff]
      have h₁ := hle q pj (by omega)
      have h₂ := hle pj r (by omega)
      have h₃ := Fin.lt_def.mp (hτ _ _ (toSS7_prec_open_pattern M hq))
      have h₄ := Fin.lt_def.mp (hτ _ _ (toSS7_prec_pattern_close M hr))
      constructor <;> omega
    have hKi := hK i
    rw [prefixCost_toSS7_eq_card_openAt M τ hτ] at hKi
    have hcard : (openAt τ i.val).card ≤ K := by exact_mod_cast hKi
    calc M.openStacksAt σ j.val = (M.activeSet σ j.val).card := (M.card_activeSet σ j.val).symm
      _ ≤ (openAt τ i.val).card := Finset.card_le_card hsub
      _ ≤ K := hcard

/-! ### The equalities -/

/-- Garey & Johnson's question on `toSS7 M` is the MOSP decision question. -/
theorem withinCost_toSS7_iff (hreq : ∃ c p, M.requires c p) (K : ℕ) :
    (toSS7 M).WithinCost K ↔ ∃ σ : LinearLayout P, M.maxOpenStacks σ ≤ K := by
  constructor
  · rintro ⟨τ, hτ, hK⟩
    exact exists_layout_of_linearExtension M τ hτ K hK
  · rintro ⟨σ, hσ⟩
    obtain ⟨τ, hτ, hK⟩ := exists_linearExtension_of_layout M hreq σ
    exact ⟨τ, hτ, fun i => (hK i).trans (by exact_mod_cast hσ)⟩

/-- **SS7 contains MOSP**: the SS7 value of the embedded instance is the MOSP
value, whenever some customer requires some pattern. -/
theorem ss7Value_toSS7 (hreq : ∃ c p, M.requires c p) : (toSS7 M).ss7Value = M.mospValue := by
  obtain ⟨σ₀, hσ₀⟩ := M.exists_maxOpenStacks_eq_mospValue
  have hmem : (toSS7 M).WithinCost M.mospValue :=
    (withinCost_toSS7_iff M hreq _).mpr ⟨σ₀, hσ₀.le⟩
  apply le_antisymm ((toSS7 M).ss7Value_le_of_withinCost hmem)
  obtain ⟨σ, hσ⟩ := (withinCost_toSS7_iff M hreq _).mp
    ((toSS7 M).withinCost_ss7Value ⟨_, hmem⟩)
  exact (M.mospValue_le_maxOpenStacks σ).trans hσ

/-- With Yanasse's equality: the SS7 value of the embedded instance is the
pathwidth of the MOSP graph plus one. -/
theorem ss7Value_toSS7_eq_pathwidth_add_one (hreq : ∃ c p, M.requires c p) :
    (toSS7 M).ss7Value = pathwidth M.mospGraph + 1 := by
  rw [ss7Value_toSS7 M hreq]
  exact M.mospValue_eq_pathwidth_add_one hreq

/-! ### Degenerate cases -/

theorem maxOpenStacks_eq_zero_of_forall_not (σ : LinearLayout P) (h : ∀ c p, ¬ M.requires c p) :
    M.maxOpenStacks σ = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold MOSPInstance.maxOpenStacks
  by_cases hn : Fintype.card P = 0
  · simp [hn]
  · simp only [dite_eq_right hn]
    apply Finset.sup'_le
    intro i _
    unfold MOSPInstance.openStacksAt
    rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c _ hc
    obtain ⟨p, hp⟩ := M.exists_requires_of_isActive _ hc
    exact h c p hp

/-- Some linear extension of `toSS7 M` keeps every prefix sum at most `1`,
when no customer requires any pattern: open and close one customer at a time. -/
theorem withinCost_toSS7_one_of_forall_not (h : ∀ c p, ¬ M.requires c p) :
    (toSS7 M).WithinCost 1 := by
  obtain ⟨τ, hτ⟩ :=
    exists_layout_sorted (embedKey M (Fintype.equivFin P) (Fintype.equivFin C))
  have hext := isLinearExtension_of_sorted M _ _ τ hτ
  refine ⟨τ, hext, fun i => ?_⟩
  rw [prefixCost_toSS7_eq_card_openAt M τ hext]
  have hc := card_openAt_le M _ _ τ hτ i
  rw [maxOpenStacks_eq_zero_of_forall_not M _ h] at hc
  exact_mod_cast hc

/-- With a customer and no requirement the SS7 value of the embedded instance
is `1`, while `mospValue = 0`: the hypothesis of `ss7Value_toSS7` is exactly
what the equality needs. -/
theorem ss7Value_toSS7_eq_one_of_forall_not [Nonempty C] (h : ∀ c p, ¬ M.requires c p) :
    (toSS7 M).ss7Value = 1 := by
  have hup := withinCost_toSS7_one_of_forall_not M h
  apply le_antisymm ((toSS7 M).ss7Value_le_of_withinCost (by exact_mod_cast hup))
  apply (toSS7 M).le_ss7Value ⟨1, by exact_mod_cast hup⟩
  rintro K' ⟨τ, hτ, hK⟩
  obtain ⟨c⟩ := ‹Nonempty C›
  have hi := hK (τ (Sum.inl c))
  rw [prefixCost_toSS7_eq_card_openAt M τ hτ] at hi
  have hmem : c ∈ openAt τ (τ (Sum.inl c)).val := by
    rw [mem_openAt_iff]
    exact ⟨le_rfl, Fin.lt_def.mp (hτ _ _ (toSS7_prec_open_close M c))⟩
  have hpos := Finset.card_pos.mpr ⟨c, hmem⟩
  omega

/-- With no customer the SS7 value of the embedded instance is `0`. -/
theorem ss7Value_toSS7_eq_zero_of_isEmpty [IsEmpty C] : (toSS7 M).ss7Value = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply (toSS7 M).ss7Value_le_of_withinCost
  obtain ⟨τ, hτ⟩ :=
    exists_layout_sorted (embedKey M (Fintype.equivFin P) (Fintype.equivFin C))
  have hext := isLinearExtension_of_sorted M _ _ τ hτ
  refine ⟨τ, hext, fun i => ?_⟩
  rw [prefixCost_toSS7_eq_card_openAt M τ hext]
  simp [openAt, Finset.univ_eq_empty]

end MOSPInstance

/-! ### Negative result 1: the comparability graph and the costs do not determine the value -/

/-- Two tasks, `0 ≺ 1`, costs `+1, −1`. -/
def dualWitness : SS7Instance (Fin 2) :=
  ⟨fun a b => a = 0 ∧ b = 1, fun t => if t = 0 then 1 else -1⟩

/-- The identity layout of `Fin n`. -/
def idLayout (n : ℕ) : LinearLayout (Fin n) := finCongr (Fintype.card_fin n).symm

theorem idLayout_apply (n : ℕ) (a : Fin n) : (idLayout n a).val = a.val := by
  simp [idLayout]

theorem ss7Value_dualWitness : dualWitness.ss7Value = 1 := by
  have hup : dualWitness.WithinCost 1 := by
    refine ⟨idLayout 2, ?_, ?_⟩
    · rintro a b ⟨rfl, rfl⟩
      rw [Fin.lt_def, idLayout_apply, idLayout_apply]
      decide
    · intro i
      rw [SS7Instance.prefixCost_eq_sum_ite, Fin.sum_univ_two]
      simp only [idLayout_apply, dualWitness, Fin.val_zero, Fin.val_one, zero_le, ↓reduceIte,
        Fin.isValue, one_ne_zero]
      split_ifs <;> omega
  apply le_antisymm (dualWitness.ss7Value_le_of_withinCost (by exact_mod_cast hup))
  apply dualWitness.le_ss7Value ⟨1, by exact_mod_cast hup⟩
  rintro K' ⟨σ, hσ, hK⟩
  have h01 : (σ 0).val < (σ 1).val := Fin.lt_def.mp (hσ 0 1 ⟨rfl, rfl⟩)
  have hlt : (σ 1).val < 2 := lt_of_lt_of_eq (σ 1).isLt (Fintype.card_fin 2)
  have h0 : 0 < Fintype.card (Fin 2) := by simp
  have hi := hK ⟨0, h0⟩
  rw [dualWitness.prefixCost_zero σ h0] at hi
  have hs : σ.symm ⟨0, h0⟩ = 0 := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext (by simp; omega)
  rw [hs] at hi
  simp [dualWitness] at hi
  omega

theorem ss7Value_dualWitness_dual : dualWitness.dual.ss7Value = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply dualWitness.dual.ss7Value_le_of_withinCost
  refine ⟨(Equiv.swap 0 1).trans (idLayout 2), ?_, ?_⟩
  · rintro a b ⟨rfl, rfl⟩
    rw [Fin.lt_def]
    simp [idLayout]
  · intro i
    rw [SS7Instance.prefixCost_eq_sum_ite, Fin.sum_univ_two]
    have hlt : i.val < 2 := lt_of_lt_of_eq i.isLt (Fintype.card_fin 2)
    simp only [Equiv.trans_apply, Equiv.swap_apply_left, Equiv.swap_apply_right, idLayout_apply,
      dualWitness, SS7Instance.dual, Fin.val_zero, Fin.val_one, Fin.isValue, ↓reduceIte,
      one_ne_zero]
    split_ifs <;> omega

theorem ss7Value_dual_ne : dualWitness.dual.ss7Value ≠ dualWitness.ss7Value := by
  rw [ss7Value_dualWitness, ss7Value_dualWitness_dual]
  decide

/-- Two SS7 instances with the same comparability graph and the same costs
and different values: the value is not a function of that graph. -/
theorem exists_same_compGraph_cost_ne_ss7Value :
    ∃ I J : SS7Instance (Fin 2), I.compGraph = J.compGraph ∧ I.cost = J.cost ∧
      I.ss7Value ≠ J.ss7Value :=
  ⟨dualWitness, dualWitness.dual, (dualWitness.compGraph_dual).symm, rfl, ss7Value_dual_ne.symm⟩

/-! ### Negative result 2: no pairwise-local derived graph -/

/-- An edgeless graph has pathwidth `0`: one singleton bag per vertex. -/
theorem pathwidth_eq_zero_of_forall_not_adj {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (h : ∀ a b, ¬ G.Adj a b) : pathwidth G = 0 := by
  let e := Fintype.equivFin V
  let D : PathDecomposition G :=
    { length := Fintype.card V
      bag := fun i => Finset.univ.filter (fun v => (e v).val = i.val)
      vertex_coverage := fun v =>
        ⟨⟨(e v).val, by have := (e v).isLt; omega⟩, by simp⟩
      edge_coverage := fun u v huv => absurd huv (h u v)
      interval := by
        intro v i j k hij hjk hi hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hk ⊢
        have h₁ : i.val ≤ j.val := hij
        have h₂ : j.val ≤ k.val := hjk
        omega }
  apply Nat.eq_zero_of_le_zero
  calc pathwidth G ≤ D.width := pathwidth_le_width G D
    _ ≤ 0 := by
      unfold PathDecomposition.width
      have hsup : Finset.sup' Finset.univ
          (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.zero_lt_succ _⟩⟩)
          (fun i : Fin (D.length + 1) => (D.bag i).card) ≤ 1 := by
        apply Finset.sup'_le
        intro i _
        rw [Finset.card_le_one]
        intro a ha b hb
        simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        exact e.injective (Fin.ext (by omega))
      omega

/-- The antichain of `n` tasks at cost `+1`. -/
def antichain (n : ℕ) : SS7Instance (Fin n) := ⟨fun _ _ => False, fun _ => 1⟩

theorem ss7Value_antichain (n : ℕ) : (antichain n).ss7Value = n := by
  have hup : (antichain n).WithinCost n := by
    refine ⟨idLayout n, fun _ _ h => False.elim h, fun i => ?_⟩
    unfold SS7Instance.prefixCost
    simp only [antichain, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hc : (Finset.univ.filter fun t => (idLayout n t).val ≤ i.val).card ≤ n :=
      (Finset.card_le_univ _).trans (by simp)
    exact_mod_cast hc
  apply le_antisymm ((antichain n).ss7Value_le_of_withinCost hup)
  apply (antichain n).le_ss7Value ⟨n, hup⟩
  rintro K' ⟨σ, _, hK⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · omega
  · have hi := hK ⟨n - 1, by simp; omega⟩
    rw [(antichain n).prefixCost_of_card_le σ (by simp; omega)] at hi
    simp only [antichain, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ,
      Fintype.card_fin] at hi
    omega

theorem antichain_mutualOrder (n : ℕ) (a b : Fin n) : (antichain n).mutualOrder a b = Mutual.none :=
  (antichain n).mutualOrder_eq_none (fun h => h) (fun h => h)

theorem localGraph_antichain_adj_iff (rule : ℤ → ℤ → Mutual → Prop) (n : ℕ) (a b : Fin n) :
    (localGraph rule (antichain n)).Adj a b ↔ a ≠ b ∧ rule 1 1 Mutual.none := by
  show a ≠ b ∧ (rule _ _ _ ∨ rule _ _ _) ↔ _
  rw [antichain_mutualOrder, antichain_mutualOrder]
  simp [antichain]

/-- If the rule does not join two `+1` tasks in mutual order `none`, the local
graph of an antichain has no edges, hence pathwidth `0`. -/
theorem pathwidth_localGraph_antichain (rule : ℤ → ℤ → Mutual → Prop) (n : ℕ)
    (hr : ¬ rule 1 1 Mutual.none) : pathwidth (localGraph rule (antichain n)) = 0 :=
  pathwidth_eq_zero_of_forall_not_adj _ (fun a b hab =>
    hr ((localGraph_antichain_adj_iff rule n a b).mp hab).2)

/-- `k` customers and no pattern. -/
def pairsMOSP (k : ℕ) : MOSPInstance (Fin k) (Fin 0) := ⟨fun _ _ => False⟩

instance (k : ℕ) : DecidableRel (pairsMOSP k).requires := fun _ _ =>
  (inferInstance : Decidable False)

/-- The matched pairs `open_i ≺ close_i`, `i < k`, at costs `+1, −1`: the
embedding of `k` customers and no pattern, relabelled onto `Fin _`. -/
noncomputable def pairsInstance (k : ℕ) :
    SS7Instance (Fin (Fintype.card (Fin k ⊕ (Fin k ⊕ Fin 0)))) :=
  (MOSPInstance.toSS7 (pairsMOSP k)).relabel (Fintype.equivFin _)

theorem ss7Value_pairsInstance (k : ℕ) (hk : 0 < k) : (pairsInstance k).ss7Value = 1 := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  unfold pairsInstance
  rw [SS7Instance.ss7Value_relabel]
  exact MOSPInstance.ss7Value_toSS7_eq_one_of_forall_not (pairsMOSP k) (fun _ _ h => h)

/-- The open tasks of the matched pairs. -/
noncomputable def pairsOpens (k : ℕ) : Finset (Fin (Fintype.card (Fin k ⊕ (Fin k ⊕ Fin 0)))) :=
  Finset.univ.image (fun c : Fin k => Fintype.equivFin (Fin k ⊕ (Fin k ⊕ Fin 0)) (Sum.inl c))

theorem card_pairsOpens (k : ℕ) : (pairsOpens k).card = k := by
  unfold pairsOpens
  rw [Finset.card_image_of_injective _ (fun a b h =>
    Sum.inl_injective ((Fintype.equivFin _).injective h))]
  simp

theorem pairsInstance_cost_open (k : ℕ) (c : Fin k) :
    (pairsInstance k).cost (Fintype.equivFin (Fin k ⊕ (Fin k ⊕ Fin 0)) (Sum.inl c)) = 1 := by
  simp [pairsInstance, SS7Instance.relabel, MOSPInstance.toSS7]

theorem pairsInstance_mutualOrder_open (k : ℕ) (c c' : Fin k) :
    (pairsInstance k).mutualOrder (Fintype.equivFin (Fin k ⊕ (Fin k ⊕ Fin 0)) (Sum.inl c))
      (Fintype.equivFin (Fin k ⊕ (Fin k ⊕ Fin 0)) (Sum.inl c')) = Mutual.none := by
  apply SS7Instance.mutualOrder_eq_none
  · show (MOSPInstance.toSS7 (pairsMOSP k)).prec ((Fintype.equivFin _).symm ((Fintype.equivFin _) (Sum.inl c)))
      ((Fintype.equivFin _).symm ((Fintype.equivFin _) (Sum.inl c'))) → False
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact MOSPInstance.toSS7_not_prec_open_open (pairsMOSP k) c c'
  · show (MOSPInstance.toSS7 (pairsMOSP k)).prec ((Fintype.equivFin _).symm ((Fintype.equivFin _) (Sum.inl c')))
      ((Fintype.equivFin _).symm ((Fintype.equivFin _) (Sum.inl c))) → False
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact MOSPInstance.toSS7_not_prec_open_open (pairsMOSP k) c' c

/-- If the rule joins two `+1` tasks in mutual order `none`, the open tasks of
the matched pairs form a clique of the local graph. -/
theorem pairsOpens_isClique (rule : ℤ → ℤ → Mutual → Prop) (k : ℕ) (hr : rule 1 1 Mutual.none) :
    (localGraph rule (pairsInstance k)).IsClique (pairsOpens k : Set _) := by
  rw [SimpleGraph.isClique_iff]
  intro a ha b hb hab
  rw [Finset.mem_coe, pairsOpens, Finset.mem_image] at ha hb
  obtain ⟨c, _, rfl⟩ := ha
  obtain ⟨c', _, rfl⟩ := hb
  refine ⟨hab, Or.inl ?_⟩
  rw [pairsInstance_cost_open, pairsInstance_cost_open, pairsInstance_mutualOrder_open]
  exact hr

theorem le_pathwidth_localGraph_pairsInstance (rule : ℤ → ℤ → Mutual → Prop) (k : ℕ)
    (hr : rule 1 1 Mutual.none) : k ≤ pathwidth (localGraph rule (pairsInstance k)) + 1 := by
  have := card_le_pathwidth_add_one_of_isClique _ _ (pairsOpens_isClique rule k hr)
  rwa [card_pairsOpens] at this

/-- **No pairwise-local derived graph**: for no rule and no constant `c` is
`ss7Value = pathwidth (localGraph rule I) + c` on every instance. The
antichain of one task forces `c = 1`; the antichain of two tasks forces the
rule to join two `+1` tasks in mutual order `none`; then the two open tasks
of two matched pairs are adjacent, so the pathwidth is at least `1` while the
value is `1`. -/
theorem no_local_derived_graph (rule : ℤ → ℤ → Mutual → Prop) (c : ℕ) :
    ¬ ∀ (n : ℕ) (I : SS7Instance (Fin n)), I.ss7Value = pathwidth (localGraph rule I) + c := by
  intro H
  have h1 := H 1 (antichain 1)
  rw [ss7Value_antichain] at h1
  have hpw1 := pathwidth_le_card_sub_one (localGraph rule (antichain 1))
  rw [Fintype.card_fin] at hpw1
  have hc : c = 1 := by omega
  have hrule : rule 1 1 Mutual.none := by
    by_contra hr
    have h2 := H 2 (antichain 2)
    rw [ss7Value_antichain, pathwidth_localGraph_antichain rule 2 hr] at h2
    omega
  have h3 := H _ (pairsInstance 2)
  rw [ss7Value_pairsInstance 2 (by omega)] at h3
  have := le_pathwidth_localGraph_pairsInstance rule 2 hrule
  omega

/-- The band version: for no rule and no constant `c` does the pathwidth of
`localGraph rule I` stay within `c` of `ss7Value I` on every instance. The
antichain of `2c + 2` tasks forces an edge, hence the rule joins two `+1`
tasks in mutual order `none`; then the `2c + 2` open tasks of the matched
pairs form a clique, so the pathwidth is at least `2c + 1` while the value is
`1`. -/
theorem no_local_derived_graph_band (rule : ℤ → ℤ → Mutual → Prop) (c : ℕ) :
    ¬ ∀ (n : ℕ) (I : SS7Instance (Fin n)),
      pathwidth (localGraph rule I) ≤ I.ss7Value + c ∧
        I.ss7Value ≤ pathwidth (localGraph rule I) + c := by
  intro H
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    have h1 := (H 1 (antichain 1)).2
    rw [ss7Value_antichain] at h1
    have hpw1 := pathwidth_le_card_sub_one (localGraph rule (antichain 1))
    rw [Fintype.card_fin] at hpw1
    omega
  · have hrule : rule 1 1 Mutual.none := by
      by_contra hr
      have h2 := (H _ (antichain (2 * c + 2))).2
      rw [ss7Value_antichain, pathwidth_localGraph_antichain rule _ hr] at h2
      omega
    have h3 := (H _ (pairsInstance (2 * c + 2))).1
    rw [ss7Value_pairsInstance _ (by omega)] at h3
    have := le_pathwidth_localGraph_pairsInstance rule (2 * c + 2) hrule
    omega

end Complex

end MOSPFormalization
