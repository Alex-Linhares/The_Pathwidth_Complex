/-
Copyright (c) 2026 Alexandre Linhares. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# The tabu search over contraction minors: its certificates are sound

`pathwidth_solver/cli/minor_tabu.c` searches the dual side of pathwidth: its state is a
set `F` of edges of `G` (kept acyclic by the walk, a *forest*), whose connected components
are the branch sets of the minor `H = G / F` (`build_minor`), and its output is a floor on
`pathwidth G` certified by the best `H` visited. The certificate printed is the contraction
sequence `print_sequence` emits: the forest edges are walked with a union-find, and for each
edge whose ends have distinct representatives `a ≠ b` the pair `[a, b]` is printed — contract
`a` into `b`, i.e. the step `(a, some b)` of `Minor.lean` — and `a`'s block is merged into
`b`'s. The floor is either `"contraction_degeneracy"` (the MMD+ value of `H`: the largest
minimum degree over the minors a greedy contraction of `H` visits) or `"refutation"` (`w + 1`
after the engine refuted width `w` on `H`).

Every statement below was checked by brute force before it was written
(`reports/scratch/minor_tabu_lean/check.py`: every graph of the atlas to 7 vertices, random
sub-forests and arbitrary edge subsets of each, the walk in the C's order and in random
orders, pathwidth by vertex separation over all orderings; zero violations).

## The walk (`ufSeq`, `ufRep`, `quotient`)

The union-find state is a representative map `r : V → V`, idempotent (`Idem`); merging the
edge `(p, q)` sends the block of `p` to `q`'s representative (`mergeRep`). `ufSeq r es` is
the printed sequence for the edge list `es`, `ufRep r es` the final map. `quotient G r` is
`G / r` on the fixed vertex type: representatives are adjacent when distinct and some edge of
`G` joins their blocks; non-representatives are isolated. The whole theory is for an
**arbitrary** list of edges of `G` in **any** order: acyclicity is what makes each addition
shrink the minor by exactly one vertex (the C's band bookkeeping) and is not a soundness
premise, so `IsForest` is defined and never assumed.

* `applySeq_ufSeq_id` — the replayed sequence **is** the quotient: `applySeq G (ufSeq id es)
  = quotient G (ufRep id es)`; and `mem_removed_ufSeq_id` — the removed vertices are exactly
  the non-representatives. So `tabuMinor G es = minorOf G (ufSeq id es)` is `G / F` on the
  representatives, which is `build_minor`'s `H` up to its `index` relabelling
  (`tabuMinor_eq`). This is the exact identification, not the weaker form.
* `isContractionSeq_ufSeq_id` — the printed sequence is legal: every pair is an edge of the
  current graph. Hence `pathwidth_tabuMinor_le`: `pathwidth (tabuMinor G F) ≤ pathwidth G`.

## The two certificate kinds

* `floor_sound_of_refutation` — `"kind": "refutation"`: `¬ pathwidth (tabuMinor G F) ≤ w`
  gives `w + 1 ≤ pathwidth G` (`"floor" = w + 1`, `"refuted" = w`).
* `floor_sound_of_degeneracy` — `"kind": "contraction_degeneracy"`: for every legal
  contraction/deletion sequence `seq₂` on the minor and every vertex set `S`,
  `minDegreeIn (applySeq (tabuMinor G F) seq₂) S ≤ pathwidth G`. MMD+
  (`pathwidth.c::contraction_degeneracy`) reads exactly such minimum degrees — on the alive
  set after each greedy contraction or deletion of an isolated vertex — and reports their
  maximum, so each value it reports is one instance of this statement.
  `degeneracy_tabuMinor_le` is the plain-degeneracy form, which MMD+ dominates.

## The run

A run is modelled as a given floor (the `-L` flag; `0` when absent) and a list of visited
forests with the floor claimed at each (`Run`); the tabu rule, the band and the sampling
decide which forests are visited and are irrelevant to soundness. `Justified G F v` says the
claim `v` on forest `F` has one of the two certificates. `Run.output` is the maximum.

* `tabu_output_le_pathwidth` — a sound run's output is a floor on `pathwidth G`.
* `tabu_output_ge_of_visited_refutation` — a visited forest whose engine call refuted `w − 1`
  (the claim `(F, w)`) puts `w ≤ output`, whatever else the walk did.
* `exists_visited_of_le_output` — a floor reached above the given one is a visited minor of
  pathwidth at least that floor: the engine refuted `w − 1` on it, or could have.
* `reaches_iff` and `output_eq_pathwidth_iff` — the two together: for `w` above the given
  floor, `w ≤ output` exactly when some visited forest carries the claim `w`, and the output
  is the recorded width `pathwidth G` exactly when some visited minor carries that claim and
  has pathwidth equal to `pathwidth G`.

The MOSP forms are `MOSPInstance.floor_sound_of_refutation_mosp` and
`MOSPInstance.tabu_output_lt_mospValue`.
-/

import MOSPFormalization.ObstructionCertificate

set_option linter.unusedSectionVars false

namespace MOSPFormalization

namespace MinorTabu

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The union-find walk -/

/-- After merging the edge `(p, q)`: the block of `p` goes into the block of `q`
(`rep[a] = b` with `a = find(p)`, `b = find(q)` in `print_sequence`). -/
def mergeRep (r : V → V) (p q : V) : V → V := fun x => if r x = r p then r q else r x

/-- The representative map after walking the edge list. -/
def ufRep (r : V → V) : List (V × V) → V → V
  | [] => r
  | (p, q) :: es => if r p = r q then ufRep r es else ufRep (mergeRep r p q) es

/-- The contraction sequence the walk prints: for each edge whose ends have distinct
representatives `a ≠ b`, the step `(a, some b)` — contract `a` into `b` — and nothing for an
edge inside a block. -/
def ufSeq (r : V → V) : List (V × V) → List (V × Option V)
  | [] => []
  | (p, q) :: es =>
      if r p = r q then ufSeq r es else (r p, some (r q)) :: ufSeq (mergeRep r p q) es

/-- A representative map is idempotent: the representative of a representative is itself. -/
def Idem (r : V → V) : Prop := ∀ x, r (r x) = r x

theorem idem_id : Idem (id : V → V) := fun _ => rfl

theorem Idem.mergeRep {r : V → V} (hr : Idem r) (p q : V) : Idem (mergeRep r p q) := by
  intro x
  by_cases h : r x = r p
  · have hm : MinorTabu.mergeRep r p q x = r q := by simp [MinorTabu.mergeRep, h]
    show (if r (MinorTabu.mergeRep r p q x) = r p then r q else r (MinorTabu.mergeRep r p q x)) =
      MinorTabu.mergeRep r p q x
    rw [hm, hr q]
    split_ifs <;> rfl
  · have hm : MinorTabu.mergeRep r p q x = r x := by simp [MinorTabu.mergeRep, h]
    show (if r (MinorTabu.mergeRep r p q x) = r p then r q else r (MinorTabu.mergeRep r p q x)) =
      MinorTabu.mergeRep r p q x
    rw [hm, hr x]
    exact hm

theorem Idem.ufRep {r : V → V} (hr : Idem r) : ∀ es : List (V × V), Idem (ufRep r es)
  | [] => hr
  | (p, q) :: es => by
    by_cases h : r p = r q
    · simp only [MinorTabu.ufRep, ite_eq_left h]; exact hr.ufRep es
    · simp only [MinorTabu.ufRep, ite_eq_right h]; exact (hr.mergeRep p q).ufRep es

/-- A vertex that has already lost its label never gets it back. -/
theorem mergeRep_ne_self {r : V → V} (hr : Idem r) (p q : V) {x : V} (hx : r x ≠ x) :
    mergeRep r p q x ≠ x := by
  simp only [mergeRep]
  split_ifs with h
  · intro hqx
    apply hx
    rw [← hqx, hr]
  · exact hx

theorem ufRep_ne_self {r : V → V} (hr : Idem r) : ∀ (es : List (V × V)) {x : V},
    r x ≠ x → ufRep r es x ≠ x
  | [], _, hx => hx
  | (p, q) :: es, x, hx => by
    by_cases h : r p = r q
    · simp only [ufRep, ite_eq_left h]; exact ufRep_ne_self hr es hx
    · simp only [ufRep, ite_eq_right h]
      exact ufRep_ne_self (hr.mergeRep p q) es (mergeRep_ne_self hr p q hx)

/-! ### The quotient graph -/

/-- `G / r`: representatives are adjacent when distinct and some edge of `G` joins their
blocks; non-representatives are isolated. This is `build_minor`'s `H` on `G`'s own labels. -/
def quotient (G : SimpleGraph V) (r : V → V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ r x = x ∧ r y = y ∧ ∃ p q, G.Adj p q ∧ r p = x ∧ r q = y
  symm := ⟨by
    rintro x y ⟨hxy, hx, hy, p, q, hpq, hp, hq⟩
    exact ⟨hxy.symm, hy, hx, q, p, hpq.symm, hq, hp⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem quotient_adj {G : SimpleGraph V} {r : V → V} {x y : V} :
    (quotient G r).Adj x y ↔ x ≠ y ∧ r x = x ∧ r y = y ∧ ∃ p q, G.Adj p q ∧ r p = x ∧ r q = y :=
  Iff.rfl

theorem quotient_id (G : SimpleGraph V) : quotient G id = G := by
  ext x y
  rw [quotient_adj]
  constructor
  · rintro ⟨_, _, _, p, q, hpq, hp, hq⟩
    subst hp; subst hq
    exact hpq
  · intro h
    exact ⟨h.ne, rfl, rfl, x, y, h, rfl, rfl⟩

/-- The printed pair is an edge of the current quotient. -/
theorem quotient_adj_rep {G : SimpleGraph V} {r : V → V} (hr : Idem r) {p q : V}
    (hpq : G.Adj p q) (hne : r p ≠ r q) : (quotient G r).Adj (r q) (r p) :=
  ⟨hne.symm, hr q, hr p, q, p, hpq.symm, rfl, rfl⟩

/-- **One step of the walk is one contraction.** Contracting `r p` into `r q` in `G / r` is
`G / r'` for the merged map. The identity needs no edge: the edge `pq` is what makes the
step *legal* (`quotient_adj_rep`), not what it produces. -/
theorem contractEdge_quotient {G : SimpleGraph V} {r : V → V} (hr : Idem r) {p q : V}
    (hne : r p ≠ r q) :
    contractEdge (quotient G r) (r q) (r p) = quotient G (mergeRep r p q) := by
  ext x y
  simp only [contractEdge, quotient, mergeRep]
  constructor
  · rintro ⟨hxy, hxa, hya, h⟩
    rcases h with ⟨_, hx, hy, a, b, hab, ha, hb⟩ | ⟨rfl, _, _, hy, a, b, hab, ha, hb⟩ |
      ⟨rfl, _, _, hx, a, b, hab, ha, hb⟩
    · refine ⟨hxy, ?_, ?_, a, b, hab, ?_, ?_⟩
      · rw [hx, ite_eq_right hxa]
      · rw [hy, ite_eq_right hya]
      · rw [ha, ite_eq_right hxa]
      · rw [hb, ite_eq_right hya]
    · refine ⟨hxy, ?_, ?_, a, b, hab, ?_, ?_⟩
      · rw [hr, ite_eq_right hne.symm]
      · rw [hy, ite_eq_right hya]
      · rw [ha, ite_eq_left rfl]
      · rw [hb, ite_eq_right hya]
    · refine ⟨hxy, ?_, ?_, b, a, hab.symm, ?_, ?_⟩
      · rw [hx, ite_eq_right hxa]
      · rw [hr, ite_eq_right hne.symm]
      · rw [hb, ite_eq_right hxa]
      · rw [ha, ite_eq_left rfl]
  · rintro ⟨hxy, hx, hy, a, b, hab, ha, hb⟩
    -- a vertex fixed by the merged map is fixed by `r` and is not `r p`
    have fixed : ∀ z, (if r z = r p then r q else r z) = z → r z = z ∧ z ≠ r p := by
      intro z hz
      by_cases h : r z = r p
      · rw [ite_eq_left h] at hz
        exact absurd (by rw [← h, ← hz, hr]) hne
      · rw [ite_eq_right h] at hz
        exact ⟨hz, fun hzp => h (hz.trans hzp)⟩
    have hx' := fixed x hx
    have hy' := fixed y hy
    refine ⟨hxy, hx'.2, hy'.2, ?_⟩
    by_cases hap : r a = r p <;> by_cases hbp : r b = r p
    · rw [ite_eq_left hap] at ha
      rw [ite_eq_left hbp] at hb
      exact absurd (ha.symm.trans hb) hxy
    · rw [ite_eq_left hap] at ha
      rw [ite_eq_right hbp] at hb
      exact Or.inr (Or.inl ⟨ha.symm, fun h => hy'.2 h.symm, hr p, hy'.1, a, b, hab, hap, hb⟩)
    · rw [ite_eq_right hap] at ha
      rw [ite_eq_left hbp] at hb
      exact Or.inr (Or.inr ⟨hb.symm, fun h => hx'.2 h.symm, hr p, hx'.1, b, a, hab.symm, hbp, ha⟩)
    · rw [ite_eq_right hap] at ha
      rw [ite_eq_right hbp] at hb
      exact Or.inl ⟨hxy, hx'.1, hy'.1, a, b, hab, ha, hb⟩

/-! ### The printed sequence replays to the quotient -/

/-- Every element of the list is an edge of `G`: the C program's state. -/
def EdgesOf (G : SimpleGraph V) (F : List (V × V)) : Prop := ∀ e ∈ F, G.Adj e.1 e.2

theorem EdgesOf.head {G : SimpleGraph V} {p q : V} {es : List (V × V)}
    (h : EdgesOf G ((p, q) :: es)) : G.Adj p q :=
  h (p, q) (List.mem_cons_self ..)

theorem EdgesOf.tail {G : SimpleGraph V} {e : V × V} {es : List (V × V)}
    (h : EdgesOf G (e :: es)) : EdgesOf G es :=
  fun e' he' => h e' (List.mem_cons_of_mem _ he')

/-- **The replay is the quotient**, from any idempotent starting map. -/
theorem applySeq_ufSeq {G : SimpleGraph V} : ∀ (es : List (V × V)) {r : V → V}, Idem r →
    EdgesOf G es → applySeq (quotient G r) (ufSeq r es) = quotient G (ufRep r es)
  | [], _, _, _ => rfl
  | (p, q) :: es, r, hr, hes => by
    by_cases h : r p = r q
    · simp only [ufSeq, ufRep, ite_eq_left h]
      exact applySeq_ufSeq es hr hes.tail
    · simp only [ufSeq, ufRep, ite_eq_right h, applySeq, applyStep]
      rw [contractEdge_quotient hr h]
      exact applySeq_ufSeq es (hr.mergeRep p q) hes.tail

/-- **The printed sequence is legal**: every pair is an edge of the current graph. -/
theorem isContractionSeq_ufSeq {G : SimpleGraph V} : ∀ (es : List (V × V)) {r : V → V},
    Idem r → EdgesOf G es → IsContractionSeq (quotient G r) (ufSeq r es)
  | [], _, _, _ => trivial
  | (p, q) :: es, r, hr, hes => by
    by_cases h : r p = r q
    · simp only [ufSeq, ite_eq_left h]
      exact isContractionSeq_ufSeq es hr hes.tail
    · simp only [ufSeq, ite_eq_right h, IsContractionSeq, StepValid, applyStep]
      refine ⟨quotient_adj_rep hr hes.head h, ?_⟩
      rw [contractEdge_quotient hr h]
      exact isContractionSeq_ufSeq es (hr.mergeRep p q) hes.tail

/-- The removed vertices are the representatives that lost their label. -/
theorem mem_removed_ufSeq : ∀ (es : List (V × V)) {r : V → V}, Idem r → ∀ x : V,
    x ∈ removed (ufSeq r es) ↔ r x = x ∧ ufRep r es x ≠ x
  | [], r, _, x => by
    simp [removed, ufSeq, ufRep]
  | (p, q) :: es, r, hr, x => by
    by_cases h : r p = r q
    · simp only [ufSeq, ufRep, ite_eq_left h]
      exact mem_removed_ufSeq es hr x
    · simp only [ufSeq, ufRep, ite_eq_right h]
      have ih := mem_removed_ufSeq es (hr.mergeRep p q) x
      simp only [removed, List.map_cons, List.toFinset_cons, Finset.mem_insert] at ih ⊢
      rw [ih]
      constructor
      · rintro (rfl | ⟨hx, hne⟩)
        · refine ⟨hr p, ?_⟩
          apply ufRep_ne_self (hr.mergeRep p q) es
          show (if r (r p) = r p then r q else r (r p)) ≠ r p
          rw [hr p, ite_eq_left rfl]
          exact Ne.symm h
        · refine ⟨?_, hne⟩
          simp only [mergeRep] at hx
          split_ifs at hx with hxp
          · rw [← hx, hr]
          · exact hx
      · rintro ⟨hx, hne⟩
        by_cases hxp : x = r p
        · exact Or.inl hxp
        · refine Or.inr ⟨?_, hne⟩
          simp only [mergeRep, hx, ite_eq_right hxp]

/-! ### From `G` itself -/

/-- The replay of the printed sequence on `G` is the quotient by the final map. -/
theorem applySeq_ufSeq_id (G : SimpleGraph V) (es : List (V × V)) (hes : EdgesOf G es) :
    applySeq G (ufSeq id es) = quotient G (ufRep id es) := by
  have := applySeq_ufSeq es idem_id hes
  rwa [quotient_id] at this

/-- **The printed sequence is a legal contraction sequence of `G`.** -/
theorem isContractionSeq_ufSeq_id (G : SimpleGraph V) (es : List (V × V))
    (hes : EdgesOf G es) : IsContractionSeq G (ufSeq id es) := by
  have := isContractionSeq_ufSeq es idem_id hes
  rwa [quotient_id] at this

/-- The removed vertices are exactly the non-representatives. -/
theorem mem_removed_ufSeq_id (es : List (V × V)) (x : V) :
    x ∈ removed (ufSeq id es) ↔ ufRep id es x ≠ x := by
  rw [mem_removed_ufSeq es idem_id x]
  simp

/-- The survivors of the walk: the representatives. -/
abbrev Surv (es : List (V × V)) : Type _ := {x : V // x ∉ removed (ufSeq id es)}

/-- **The minor of a forest**, `G / F`: `minorOf G` of the printed sequence. -/
abbrev tabuMinor (G : SimpleGraph V) (F : List (V × V)) : SimpleGraph (Surv F) :=
  minorOf G (ufSeq id F)

/-- The exact identification: `G / F` is the quotient by the final representative map,
induced on the representatives — `build_minor`'s `H` on `G`'s labels. -/
theorem tabuMinor_eq (G : SimpleGraph V) (F : List (V × V)) (hF : EdgesOf G F) :
    tabuMinor G F = (quotient G (ufRep id F)).induce {x | x ∉ removed (ufSeq id F)} := by
  unfold tabuMinor minorOf
  rw [applySeq_ufSeq_id G F hF]

theorem removed_ufSeq_id_eq (F : List (V × V)) :
    removed (ufSeq id F) = Finset.univ.filter (fun x => ufRep id F x ≠ x) := by
  ext x
  simp [mem_removed_ufSeq_id]

/-- **Minor monotonicity for the forest's minor.** -/
theorem pathwidth_tabuMinor_le (G : SimpleGraph V) (F : List (V × V)) (hF : EdgesOf G F) :
    pathwidth (tabuMinor G F) ≤ pathwidth G :=
  pathwidth_minorOf_le G (ufSeq id F) (isContractionSeq_ufSeq_id G F hF)

/-! ### Forests

The C program keeps `F` acyclic (`forest_would_cycle`); the theorems above do not need it. -/

/-- The edge set of a list of pairs, as `Sym2` edges. -/
def edgeSet (F : List (V × V)) : Set (Sym2 V) := {e | ∃ x ∈ F, e = s(x.1, x.2)}

/-- A forest of edges of `G`: every pair an edge of `G`, and the graph they span acyclic. -/
def IsForest (G : SimpleGraph V) (F : List (V × V)) : Prop :=
  EdgesOf G F ∧ (SimpleGraph.fromEdgeSet (edgeSet F)).IsAcyclic

theorem IsForest.edgesOf {G : SimpleGraph V} {F : List (V × V)} (h : IsForest G F) :
    EdgesOf G F := h.1

theorem IsForest.isContractionSeq {G : SimpleGraph V} {F : List (V × V)} (h : IsForest G F) :
    IsContractionSeq G (ufSeq id F) :=
  isContractionSeq_ufSeq_id G F h.1

theorem IsForest.pathwidth_le {G : SimpleGraph V} {F : List (V × V)} (h : IsForest G F) :
    pathwidth (tabuMinor G F) ≤ pathwidth G :=
  pathwidth_tabuMinor_le G F h.1

/-! ### The two certificate kinds -/

section Certificates

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **`"kind": "refutation"`.** The engine refuted width `w` on the minor of the forest `F`
(`"refuted": w`), so the floor `"floor": w + 1` is a lower bound on `pathwidth G`. The
engine's graph is `build_minor`'s relabelling of `tabuMinor G F` (`tabuMinor_eq`), and
pathwidth is relabelling-invariant (`pathwidth_eq_of_iso`). -/
theorem floor_sound_of_refutation (F : List (V × V)) (hF : EdgesOf G F) {w : ℕ}
    (h : ¬ pathwidth (tabuMinor G F) ≤ w) : w + 1 ≤ pathwidth G := by
  have := pathwidth_tabuMinor_le G F hF
  omega

/-- **`"kind": "contraction_degeneracy"`.** MMD+ (`contraction_degeneracy` in
`pathwidth.c`) contracts a minimum-degree vertex into a neighbour, or drops it when
isolated, and reports the largest minimum degree it read on the alive set; every value it
reads is `minDegreeIn (applySeq (tabuMinor G F) seq₂) S` for a legal `seq₂` on the minor and
`S` the alive set, and every such value is a lower bound on `pathwidth G`. -/
theorem floor_sound_of_degeneracy (F : List (V × V)) (hF : EdgesOf G F)
    (seq₂ : List (Surv F × Option (Surv F))) (h₂ : IsContractionSeq (tabuMinor G F) seq₂)
    (S : Finset (Surv F)) :
    minDegreeIn (applySeq (tabuMinor G F) seq₂) S ≤ pathwidth G :=
  (minDegreeIn_le_degeneracy _ S).trans ((degeneracy_le_pathwidth _).trans
    ((pathwidth_applySeq_le _ seq₂ h₂).trans (pathwidth_tabuMinor_le G F hF)))

/-- The plain degeneracy of the minor (the value MMD+ dominates) is a lower bound too. -/
theorem degeneracy_tabuMinor_le (F : List (V × V)) (hF : EdgesOf G F) :
    degeneracy (tabuMinor G F) ≤ pathwidth G :=
  (degeneracy_le_pathwidth _).trans (pathwidth_tabuMinor_le G F hF)

/-- A certified floor in the C program's `"floor"` field: `v` on the forest `F`, by one of the
two kinds. The forest's edges must be edges of `G` (the state's invariant). -/
inductive Justified : List (V × V) → ℕ → Prop
  /-- `"kind": "refutation"`: the engine refuted width `w` on the minor; the floor is `w + 1`. -/
  | refutation {F : List (V × V)} (hF : EdgesOf G F) {w : ℕ}
      (h : ¬ pathwidth (tabuMinor G F) ≤ w) : Justified F (w + 1)
  /-- `"kind": "contraction_degeneracy"`: MMD+ read minimum degree `≥ v` on the alive set `S`
  after the legal sequence `seq₂` on the minor. -/
  | contractionDegeneracy {F : List (V × V)} (hF : EdgesOf G F) {v : ℕ}
      (seq₂ : List (Surv F × Option (Surv F))) (S : Finset (Surv F))
      (h₂ : IsContractionSeq (tabuMinor G F) seq₂)
      (hd : v ≤ minDegreeIn (applySeq (tabuMinor G F) seq₂) S) : Justified F v

variable {G}

theorem Justified.edgesOf {F : List (V × V)} {v : ℕ} : Justified G F v → EdgesOf G F
  | refutation hF _ => hF
  | contractionDegeneracy hF _ _ _ _ => hF

/-- Either kind of certificate puts the floor at or below the minor's pathwidth: the minor
refutes `v − 1`. -/
theorem Justified.le_pathwidth_tabuMinor {F : List (V × V)} {v : ℕ} :
    Justified G F v → v ≤ pathwidth (tabuMinor G F)
  | refutation _ h => by omega
  | contractionDegeneracy _ seq₂ S h₂ hd =>
    hd.trans ((minDegreeIn_le_degeneracy _ S).trans
      ((degeneracy_le_pathwidth _).trans (pathwidth_applySeq_le _ seq₂ h₂)))

/-- **Either kind of certificate is sound.** -/
theorem Justified.le_pathwidth {F : List (V × V)} {v : ℕ} (h : Justified G F v) :
    v ≤ pathwidth G :=
  h.le_pathwidth_tabuMinor.trans (pathwidth_tabuMinor_le G F h.edgesOf)

end Certificates

/-! ### The run -/

/-- A tabu run: the given floor (`-L`; `0` when absent) and the visited forests with the floor
claimed at each. Which forests are visited — the tabu list, the band, the sampling, the
aspiration — is irrelevant here. -/
structure Run (G : SimpleGraph V) where
  /-- The floor the run was started from (`-L`), trusted. -/
  given : ℕ
  /-- The visited forests and the floor claimed on each. -/
  claims : List (List (V × V) × ℕ)

namespace Run

variable {G : SimpleGraph V}

/-- The run's output: the largest claimed floor, or the given one. -/
def output (R : Run G) : ℕ := R.claims.foldr (fun c m => max c.2 m) R.given

/-- A sound run: the given floor is a lower bound and every claim is certified. -/
def Sound (R : Run G) [DecidableRel G.Adj] : Prop :=
  R.given ≤ pathwidth G ∧ ∀ c ∈ R.claims, Justified G c.1 c.2

theorem le_foldr_max_iff {α : Type*} (w g : ℕ) : ∀ l : List (α × ℕ),
    w ≤ l.foldr (fun c m => max c.2 m) g ↔ w ≤ g ∨ ∃ c ∈ l, w ≤ c.2
  | [] => by simp
  | c :: l => by
    simp only [List.foldr_cons, le_max_iff, le_foldr_max_iff w g l, List.mem_cons,
      exists_eq_or_imp]
    tauto

theorem foldr_max_le {α : Type*} {g b : ℕ} (hg : g ≤ b) : ∀ l : List (α × ℕ),
    (∀ c ∈ l, c.2 ≤ b) → l.foldr (fun c m => max c.2 m) g ≤ b
  | [], _ => hg
  | c :: l, hl => by
    simp only [List.foldr_cons]
    exact max_le (hl c (List.mem_cons_self ..))
      (foldr_max_le hg l fun c' hc' => hl c' (List.mem_cons_of_mem _ hc'))

/-- `w ≤ output` exactly when the given floor or some claim is at least `w`. -/
theorem le_output_iff (R : Run G) (w : ℕ) :
    w ≤ R.output ↔ w ≤ R.given ∨ ∃ c ∈ R.claims, w ≤ c.2 :=
  le_foldr_max_iff w R.given R.claims

theorem given_le_output (R : Run G) : R.given ≤ R.output :=
  (le_output_iff R _).mpr (Or.inl le_rfl)

end Run

section RunTheorems

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **The output is a floor.** Whatever the walk did, a sound run reports a lower bound on
`pathwidth G`. -/
theorem tabu_output_le_pathwidth (R : Run G) (hR : R.Sound) : R.output ≤ pathwidth G :=
  Run.foldr_max_le hR.1 R.claims fun c hc => (hR.2 c hc).le_pathwidth

/-- **A visited refutation is reported.** If the engine refuted `w − 1` on the minor of a
visited forest `F` — the claim `(F, w)` — then `w ≤ output`. -/
theorem tabu_output_ge_of_visited_refutation (R : Run G) {F : List (V × V)} {w : ℕ}
    (hc : (F, w) ∈ R.claims) : w ≤ R.output :=
  (R.le_output_iff w).mpr (Or.inr ⟨(F, w), hc, le_rfl⟩)

/-- The form with the C fields: the engine refuted `w` on `F`'s minor, the floor is `w + 1`. -/
theorem tabu_output_ge_of_refuted (R : Run G) {F : List (V × V)} {w : ℕ}
    (hc : (F, w + 1) ∈ R.claims) : w < R.output :=
  tabu_output_ge_of_visited_refutation R hc

/-- **A floor reached above the given one is a visited minor that refutes it.** If a sound run
reports `w` with `given < w`, some visited forest's minor has pathwidth at least `w` — the
engine refuted `w − 1` on it, or (degeneracy kind) could have. -/
theorem exists_visited_of_le_output (R : Run G) (hR : R.Sound) {w : ℕ} (hg : R.given < w)
    (h : w ≤ R.output) : ∃ c ∈ R.claims, w ≤ pathwidth (tabuMinor G c.1) := by
  rcases (R.le_output_iff w).mp h with h' | ⟨c, hc, hw⟩
  · omega
  · exact ⟨c, hc, hw.trans (hR.2 c hc).le_pathwidth_tabuMinor⟩

/-- **Reaching `w` is exactly a visited claim of `w`** (above the given floor). -/
theorem reaches_iff (R : Run G) {w : ℕ} (hg : R.given < w) :
    w ≤ R.output ↔ ∃ c ∈ R.claims, w ≤ c.2 := by
  rw [R.le_output_iff]
  constructor
  · rintro (h | h)
    · omega
    · exact h
  · exact Or.inr

/-- **The run reaches the recorded width exactly when a visited minor carries it.** For a sound
run started below `pathwidth G`: the output equals `pathwidth G` iff some visited forest
carries the claim `pathwidth G`, and then its minor has pathwidth exactly `pathwidth G`. -/
theorem output_eq_pathwidth_iff (R : Run G) (hR : R.Sound) (hg : R.given < pathwidth G) :
    R.output = pathwidth G ↔
      ∃ c ∈ R.claims, c.2 = pathwidth G ∧ pathwidth (tabuMinor G c.1) = pathwidth G := by
  have hle := tabu_output_le_pathwidth R hR
  constructor
  · intro h
    obtain ⟨c, hc, hw⟩ := (reaches_iff R hg).mp h.ge
    have h1 := (hR.2 c hc).le_pathwidth
    have h2 := (hR.2 c hc).le_pathwidth_tabuMinor
    have h3 := pathwidth_tabuMinor_le G c.1 (hR.2 c hc).edgesOf
    exact ⟨c, hc, le_antisymm h1 hw, le_antisymm h3 (hw.trans h2)⟩
  · rintro ⟨c, hc, hw, _⟩
    exact le_antisymm hle ((reaches_iff R hg).mpr ⟨c, hc, hw.ge⟩)

end RunTheorems

end MinorTabu

/-! ### In MOSP units -/

namespace MOSPInstance

open MinorTabu

variable {C Pt : Type*} [Fintype C] [DecidableEq C] [Fintype Pt] [DecidableEq Pt]
variable (M : MOSPInstance C Pt) [DecidableRel M.requires]

/-- **A refutation certificate on the MOSP graph**: the engine refuted width `w` on the minor
of a forest of the MOSP graph, so every pattern order opens more than `w + 1` stacks. No
hypothesis on the instance is needed. -/
theorem floor_sound_of_refutation_mosp (F : List (C × C)) (hF : EdgesOf M.mospGraph F) {w : ℕ}
    (h : ¬ pathwidth (tabuMinor M.mospGraph F) ≤ w) : w + 1 < M.mospValue :=
  M.lt_mospValue_of_minorOf (ufSeq id F) (isContractionSeq_ufSeq_id _ F hF) (Nat.lt_of_not_le h)

/-- **A sound tabu run on the MOSP graph** reports a floor below the optimum: every pattern
order opens more than `output` stacks. -/
theorem tabu_output_lt_mospValue (hreq : ∃ c p, M.requires c p) (R : Run M.mospGraph)
    (hR : R.Sound) : R.output < M.mospValue := by
  rw [M.mospValue_eq_pathwidth_add_one hreq]
  have := tabu_output_le_pathwidth R hR
  omega

end MOSPInstance

end MOSPFormalization
