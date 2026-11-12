/-
Copyright (c) 2026 Alexandre Linhares. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# The layout formula for the one-shot black pebble game with a retained set

Sethi, *Complete register allocation problems*, SIAM J. Comput. 4 (1975) 226–248; Garey &
Johnson (1979) p. 272, PO1 REGISTER SUFFICIENCY; Kirousis & Papadimitriou, *Searching and
pebbling*, TCS 47 (1986) 205–218, §3 (the progressive black game `pb` of `PebblingGu.lean`).
The game with a retained set `R` (`BlackMove.LegalR`, `BlackStepR`) and the layout quantities
(`IsTopological`, `preBoundary`, `layoutDemand`, `topologicalDemand`) are those of
`RegisterSufficiency.lean`.

## Definitions

* `BlackPebblesWithinR D R K` (`RegisterSufficiency.lean`) — the play is complete when **every
  vertex has been pebbled**: some position in which no vertex is `fresh` is reachable from the
  pebble-free start through positions with at most `K` pebbles, never removing a pebble from
  `R`. `pbR D R` is its least `K`, `registerDemand D = pbR D (outputs D)` Garey & Johnson's
  quantity. (A first draft ended the play at the all-`done` position, which `done` reached only
  by `remove`, illegal on `R`, makes unattainable for every `R ≠ ∅` on a nonempty type; the
  prover of this file found that and the definition was corrected. Garey & Johnson's play ends
  with the outputs still in registers.)
* `doneR D R σ i` — the invariant's cleared set: placed before `i`, not retained, every
  successor placed before `i`. The black set of the invariant is `preBoundary D R σ i`.

## What is proved

* `blackStepR_empty_iff`, `blackPebblesWithinR_empty_iff_reflTransGen`,
  `blackPebblesWithinR_empty_iff`, `pbR_empty`: retention by `∅` is Kirousis & Papadimitriou's
  game, whose play ends at the all-`done` position (with `R = ∅` the black pebbles of a
  completed position are removed one by one, never raising the count, `reach_done_of_black`).
* `BlackPebblesWithinR.mono`, `blackPebblesWithinR_of_subset`, `pbR_le_pbR_of_subset`: a
  smaller retained set never costs more (the inequality under the hypothesis that the larger
  set has a play, since `sInf ∅ = 0` on `ℕ`).
* `exists_isTopological_of_blackPebblesWithinR`: **every play within `K` pebbles yields a
  topological layout of demand `≤ K`**, the order of placement.
* `blackPebblesWithinR_of_isTopological`, `blackPebblesWithinR_of_isTopological_of_le`:
  **placing in layout order and dropping each unretained pebble as soon as its last successor
  is placed is a play within `layoutDemand`.**
* `pbR_eq_topologicalDemand`: **`pbR D R = topologicalDemand D R` for every digraph on a
  finite type and every retained set** (both sides `0` when no topological layout exists, i.e.
  when `D` has a cycle); `pb_eq_topologicalDemand` (`R = ∅`, Kirousis & Papadimitriou's `pb`),
  `registerDemand_eq_topologicalDemand` (Garey & Johnson's PO1).
* `pbw_le_pb_of_exists`, `pathwidth_lengauerU_add_one_le_pb`: `pw(G_u) + 1 = pbw(D) ≤ pb(D)`
  whenever the black game has a play.

## The proofs

* **Lower bound.** A black move raises the phase of its target by one and changes nothing else
  (`BlackStepR.rank_le`, `BlackStepR.eq_target`). Let `r v` be the step at which `v` stops being
  fresh; that step is the placement of `v`, so its predecessors are pebbled then
  (`BlackStepR.of_placed`), which puts them earlier: the layout sorted by `r`
  (`exists_layout_of_injective`) is topological. When `v = σ.symm i` is placed, every
  `w ∈ preBoundary D R σ i` carries a pebble: it was placed earlier, and either it is retained
  and so never removed (`seqR_retained`), or it has a successor `u` placed at or after `v`,
  whose placement needs `w` pebbled, and phases only rise. With `v` itself that is
  `|preBoundary| + 1 ≤ K` pebbles.
* **Upper bound.** The invariant after `i` placements is the position
  `gpos (doneR D R σ i) (preBoundary D R σ i) ∅` of `PebblingGu.lean`; one step
  (`rreach_step`) places `σ.symm i`, whose predecessors lie in the boundary, then removes every
  unretained pebble whose successors are all placed (`rreach_remove_set`), and the set identities
  are checked as in `breach_step`. At `i = card α` every vertex is done or black, none fresh.
* **Equality.** If a topological layout exists both infima are attained
  (`Nat.sInf_mem`, `le_csInf`); if none exists, no play exists either (a play would yield one),
  and both sides are `sInf ∅ = 0`.

Brute force: `reports/scratch/ss7_register_sufficiency/pb_formula_check.py` (every labelled dag
on ≤ 6 vertices, 33,867 of them, both retention conventions, game search against the ideal-chain
DP and a brute force over topological orderings; 2,000 random dags on 9 vertices; 0 mismatches,
`pb_formula_check.log`).
-/

import MOSPFormalization.Complex.RegisterSufficiency

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace MOSPFormalization

namespace Complex

open Finset Function PebblePhase

/-! ### The end condition, and retention by `∅` -/

section Basic

variable {α : Type*} [Fintype α] [DecidableEq α] {D : Digraph α} {R : Finset α} {K : ℕ}

theorem BlackMove.legalR_empty_iff (P : PebblePosition α) (m : BlackMove α) :
    m.LegalR D ∅ P ↔ m.Legal D P := by
  cases m <;> simp [BlackMove.LegalR, BlackMove.Legal]

theorem blackStepR_empty_iff (P Q : PebblePosition α) :
    BlackStepR D ∅ K P Q ↔ BlackStep D K P Q := by
  unfold BlackStepR BlackStep
  exact exists_congr fun m => by rw [BlackMove.legalR_empty_iff]

theorem blackStepR_empty : BlackStepR D ∅ K = BlackStep D K := by
  funext P Q; exact propext (blackStepR_empty_iff P Q)

theorem BlackStepR.numPebbles_le {P Q : PebblePosition α} (h : BlackStepR D R K P Q) :
    numPebbles Q ≤ K := by
  obtain ⟨_, _, rfl, hc⟩ := h; exact hc

theorem BlackStepR.mono {K' : ℕ} (hK : K ≤ K') {P Q : PebblePosition α}
    (h : BlackStepR D R K P Q) : BlackStepR D R K' P Q := by
  obtain ⟨m, hm, hQ, hc⟩ := h
  exact ⟨m, hm, hQ, hc.trans hK⟩

theorem BlackStepR.reflTransGen_mono {K' : ℕ} (hK : K ≤ K') {P Q : PebblePosition α}
    (h : Relation.ReflTransGen (BlackStepR D R K) P Q) :
    Relation.ReflTransGen (BlackStepR D R K') P Q := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (hs.mono hK)

theorem BlackPebblesWithinR.mono {K' : ℕ} (h : BlackPebblesWithinR D R K) (hK : K ≤ K') :
    BlackPebblesWithinR D R K' := by
  obtain ⟨Q, hQ, hf⟩ := h
  exact ⟨Q, BlackStepR.reflTransGen_mono hK hQ, hf⟩

theorem BlackMove.LegalR.of_subset {S : Finset α} (hRS : R ⊆ S) {P : PebblePosition α}
    {m : BlackMove α} (h : m.LegalR D S P) : m.LegalR D R P := by
  cases m with
  | place x => exact h
  | remove x => exact ⟨h.1, fun hx => h.2 (hRS hx)⟩

theorem BlackStepR.of_subset {S : Finset α} (hRS : R ⊆ S) {P Q : PebblePosition α}
    (h : BlackStepR D S K P Q) : BlackStepR D R K P Q := by
  obtain ⟨m, hm, hQ, hc⟩ := h
  exact ⟨m, hm.of_subset hRS, hQ, hc⟩

theorem BlackStepR.reflTransGen_of_subset {S : Finset α} (hRS : R ⊆ S) {P Q : PebblePosition α}
    (h : Relation.ReflTransGen (BlackStepR D S K) P Q) :
    Relation.ReflTransGen (BlackStepR D R K) P Q := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (hs.of_subset hRS)

/-- Retaining less never hurts. -/
theorem blackPebblesWithinR_of_subset {S : Finset α} (hRS : R ⊆ S)
    (h : BlackPebblesWithinR D S K) : BlackPebblesWithinR D R K := by
  obtain ⟨Q, hQ, hf⟩ := h
  exact ⟨Q, BlackStepR.reflTransGen_of_subset hRS hQ, hf⟩

theorem pbR_le_pbR_of_subset {S : Finset α} (hRS : R ⊆ S)
    (h : ∃ K, BlackPebblesWithinR D S K) : pbR D R ≤ pbR D S :=
  Nat.sInf_le (blackPebblesWithinR_of_subset hRS (Nat.sInf_mem h))

end Basic

/-! ### What a black move does -/

section Moves

variable {α : Type*} [Fintype α] [DecidableEq α] {D : Digraph α} {R : Finset α} {K : ℕ}

theorem PebblePhase.ne_fresh_iff_rank (p : PebblePhase) : p ≠ fresh ↔ 1 ≤ p.rank := by
  cases p <;> simp [rank]

/-- A black move never lowers a phase. -/
theorem BlackStepR.rank_le {P Q : PebblePosition α} (h : BlackStepR D R K P Q) (x : α) :
    (P x).rank ≤ (Q x).rank := by
  obtain ⟨m, hm, rfl, -⟩ := h
  cases m with
  | place z =>
    by_cases hx : x = z
    · subst hx; simp only [BlackMove.apply, Function.update_self]; rw [hm.1]; simp [rank]
    · simp [BlackMove.apply, Function.update_of_ne hx]
  | remove z =>
    by_cases hx : x = z
    · subst hx; simp only [BlackMove.apply, Function.update_self]; rw [hm.1]; simp [rank]
    · simp [BlackMove.apply, Function.update_of_ne hx]

/-- A black move changes one vertex only. -/
theorem BlackStepR.eq_target {P Q : PebblePosition α} (h : BlackStepR D R K P Q) {x y : α}
    (hx : P x ≠ Q x) (hy : P y ≠ Q y) : x = y := by
  obtain ⟨m, -, rfl, -⟩ := h
  cases m with
  | place z =>
    have h1 : x = z := by
      by_contra h; exact hx (by simp [BlackMove.apply, Function.update_of_ne h])
    have h2 : y = z := by
      by_contra h; exact hy (by simp [BlackMove.apply, Function.update_of_ne h])
    rw [h1, h2]
  | remove z =>
    have h1 : x = z := by
      by_contra h; exact hx (by simp [BlackMove.apply, Function.update_of_ne h])
    have h2 : y = z := by
      by_contra h; exact hy (by simp [BlackMove.apply, Function.update_of_ne h])
    rw [h1, h2]

/-- The only move that takes a vertex out of `fresh` is its placement: afterwards it is black,
and its immediate predecessors were pebbled before. -/
theorem BlackStepR.of_placed {P Q : PebblePosition α} (h : BlackStepR D R K P Q) {x : α}
    (hP : P x = fresh) (hQ : Q x ≠ fresh) :
    Q x = black ∧ ∀ y, D.Adj y x → (P y).Pebbled := by
  obtain ⟨m, hm, rfl, -⟩ := h
  cases m with
  | place z =>
    by_cases hx : x = z
    · subst hx; exact ⟨by simp [BlackMove.apply], hm.2⟩
    · exact absurd (by simp [BlackMove.apply, Function.update_of_ne hx, hP]) hQ
  | remove z =>
    by_cases hx : x = z
    · subst hx; rw [hm.1] at hP; exact absurd hP PebblePhase.noConfusion
    · exact absurd (by simp [BlackMove.apply, Function.update_of_ne hx, hP]) hQ

/-- A retained black pebble stays. -/
theorem BlackStepR.retained {P Q : PebblePosition α} (h : BlackStepR D R K P Q) {x : α}
    (hxR : x ∈ R) (hP : P x = black) : Q x = black := by
  obtain ⟨m, hm, rfl, -⟩ := h
  cases m with
  | place z =>
    by_cases hx : x = z
    · subst hx; rw [hm.1] at hP; exact absurd hP PebblePhase.noConfusion
    · simp [BlackMove.apply, Function.update_of_ne hx, hP]
  | remove z =>
    by_cases hx : x = z
    · subst hx; exact absurd hxR hm.2
    · simp [BlackMove.apply, Function.update_of_ne hx, hP]

/-- A retained vertex never reaches `done`. -/
theorem BlackStepR.ne_done {P Q : PebblePosition α} (h : BlackStepR D R K P Q) {x : α}
    (hxR : x ∈ R) (hP : P x ≠ done) : Q x ≠ done := by
  obtain ⟨m, hm, rfl, -⟩ := h
  cases m with
  | place z =>
    by_cases hx : x = z
    · subst hx; simp [BlackMove.apply]
    · simp [BlackMove.apply, Function.update_of_ne hx, hP]
  | remove z =>
    by_cases hx : x = z
    · subst hx; exact absurd hxR hm.2
    · simp [BlackMove.apply, Function.update_of_ne hx, hP]

/-- The black game never produces a white pebble. -/
theorem BlackStepR.ne_white {P Q : PebblePosition α} (h : BlackStepR D R K P Q)
    (hP : ∀ x, P x ≠ white) (x : α) : Q x ≠ white := by
  obtain ⟨m, -, rfl, -⟩ := h
  cases m with
  | place z =>
    by_cases hx : x = z
    · subst hx; simp [BlackMove.apply]
    · simp [BlackMove.apply, Function.update_of_ne hx, hP x]
  | remove z =>
    by_cases hx : x = z
    · subst hx; simp [BlackMove.apply]
    · simp [BlackMove.apply, Function.update_of_ne hx, hP x]

theorem reflTransGen_ne_white {Q : PebblePosition α}
    (h : Relation.ReflTransGen (BlackStepR D R K) (fun _ => fresh) Q) : ∀ x, Q x ≠ white := by
  induction h with
  | refl => exact fun _ => PebblePhase.noConfusion
  | tail _ hs ih => exact hs.ne_white ih

theorem reflTransGen_ne_done_of_mem {Q : PebblePosition α}
    (h : Relation.ReflTransGen (BlackStepR D R K) (fun _ => fresh) Q) {x : α} (hxR : x ∈ R) :
    Q x ≠ done := by
  induction h with
  | refl => exact PebblePhase.noConfusion
  | tail _ hs ih => exact hs.ne_done hxR ih

theorem reflTransGen_numPebbles_le {Q : PebblePosition α}
    (h : Relation.ReflTransGen (BlackStepR D R K) (fun _ => fresh) Q) : numPebbles Q ≤ K := by
  induction h with
  | refl => simp [numPebbles, Pebbled]
  | tail _ hs _ => exact hs.numPebbles_le

variable {T : ℕ} {P : ℕ → PebblePosition α}

theorem seqR_rank_mono (hs : ∀ i < T, BlackStepR D R K (P i) (P (i + 1))) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ T) (x : α) : (P i x).rank ≤ (P j x).rank := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (by omega)).trans ((hs j (by omega)).rank_le x)

theorem seqR_retained (hs : ∀ i < T, BlackStepR D R K (P i) (P (i + 1))) {x : α} (hxR : x ∈ R)
    {i j : ℕ} (hi : P i x = black) (hij : i ≤ j) (hj : j ≤ T) : P j x = black := by
  induction j, hij using Nat.le_induction with
  | base => exact hi
  | succ j _ ih => exact (hs j (by omega)).retained hxR (ih (by omega))

theorem seqR_numPebbles_le (hs : ∀ i < T, BlackStepR D R K (P i) (P (i + 1)))
    (h0 : P 0 = fun _ => fresh) {i : ℕ} (hi : i ≤ T) : numPebbles (P i) ≤ K := by
  rcases i with _ | i
  · rw [h0]; simp [numPebbles, Pebbled]
  · exact (hs i (by omega)).numPebbles_le

end Moves

/-! ### Retention by `∅`, under the end condition "every vertex pebbled" -/

section Empty

variable {α : Type*} [Fintype α] [DecidableEq α] {D : Digraph α} {K : ℕ}

theorem numPebbles_update_done_le (Q : PebblePosition α) (x : α) :
    numPebbles (Function.update Q x done) ≤ numPebbles Q := by
  unfold numPebbles
  apply card_le_card
  intro y hy
  simp only [mem_filter, mem_univ, true_and] at hy ⊢
  by_cases hyx : y = x
  · subst hyx; simp [Pebbled] at hy
  · rwa [Function.update_of_ne hyx] at hy

/-- With nothing retained, every black pebble can be removed, one at a time, never raising the
count. -/
theorem reach_done_of_black (B : Finset α) :
    ∀ Q : PebblePosition α, (∀ x, Q x ≠ fresh ∧ Q x ≠ white) →
      (∀ x, Q x = black → x ∈ B) → numPebbles Q ≤ K →
      Relation.ReflTransGen (BlackStepR D ∅ K) Q (fun _ => done) := by
  induction B using Finset.induction_on with
  | empty =>
    intro Q hQ hB _
    have : Q = fun _ => done := by
      funext x
      have h1 := (hQ x).1
      have h2 := (hQ x).2
      have h3 : Q x ≠ black := fun h => by simpa using hB x h
      cases h : Q x <;> simp_all
    rw [this]
  | insert x B hx ih =>
    intro Q hQ hB hK
    by_cases hQx : Q x = black
    · set Q' := Function.update Q x done with hQ'
      have hK' : numPebbles Q' ≤ K := (numPebbles_update_done_le Q x).trans hK
      refine Relation.ReflTransGen.head ⟨.remove x, ⟨hQx, notMem_empty x⟩, rfl, hK'⟩
        (ih Q' ?_ ?_ hK')
      · intro y
        by_cases hyx : y = x
        · subst hyx; simp [Q']
        · rw [hQ', Function.update_of_ne hyx]; exact hQ y
      · intro y hy
        by_cases hyx : y = x
        · subst hyx; simp [Q'] at hy
        · rw [hQ', Function.update_of_ne hyx] at hy
          exact (mem_insert.mp (hB y hy)).resolve_left hyx
    · exact ih Q hQ (fun y hy => (mem_insert.mp (hB y hy)).resolve_left
        (fun h => hQx (h ▸ hy))) hK

/-- With `R = ∅` the two end conditions agree: a position with every vertex pebbled is
completed by removing the black pebbles. -/
theorem blackPebblesWithinR_empty_iff_reflTransGen :
    BlackPebblesWithinR D ∅ K ↔
      Relation.ReflTransGen (BlackStepR D ∅ K) (fun _ => fresh) (fun _ => done) := by
  constructor
  · rintro ⟨Q, hQ, hf⟩
    refine hQ.trans (reach_done_of_black univ Q (fun x => ⟨hf x, reflTransGen_ne_white hQ x⟩)
      (fun x _ => mem_univ x) (reflTransGen_numPebbles_le hQ))
  · exact fun h => ⟨fun _ => done, h, fun _ => PebblePhase.noConfusion⟩

/-- Retention by `∅` is Kirousis & Papadimitriou's game. -/
theorem blackPebblesWithinR_empty_iff :
    BlackPebblesWithinR D ∅ K ↔ BlackPebblesWithin D K := by
  rw [blackPebblesWithinR_empty_iff_reflTransGen]
  unfold BlackPebblesWithin
  rw [blackStepR_empty]

theorem pbR_empty : pbR D ∅ = pb D := by
  unfold pbR pb
  congr 1
  ext K
  exact blackPebblesWithinR_empty_iff

end Empty

/-! ### The lower bound: the layout a play induces -/

section Lower

variable {α : Type*} [Fintype α] [DecidableEq α] {D : Digraph α} [DecidableRel D.Adj]
variable {R : Finset α} {K : ℕ}

/-- **The lower bound.** Every play within `K` pebbles yields a topological layout — the order
of placement — of demand at most `K`. -/
theorem exists_isTopological_of_blackPebblesWithinR (h : BlackPebblesWithinR D R K) :
    ∃ σ : LinearLayout α, IsTopological D σ ∧ layoutDemand D R σ ≤ K := by
  classical
  obtain ⟨Qend, hQ, hQf⟩ := h
  obtain ⟨T, P, h0, hT, hs⟩ := exists_seq_of_reflTransGen hQ
  have hmono := fun {i j} (hij : i ≤ j) (hj : j ≤ T) x => seqR_rank_mono hs (P := P) hij hj x
  have hex : ∀ v : α, ∃ t, t ≤ T ∧ P t v ≠ fresh := fun v =>
    ⟨T, le_rfl, by rw [hT]; exact hQf v⟩
  let r : α → ℕ := fun v => Nat.find (hex v)
  have hrT : ∀ v, r v ≤ T := fun v => (Nat.find_spec (hex v)).1
  have hrne : ∀ v, P (r v) v ≠ fresh := fun v => (Nat.find_spec (hex v)).2
  have hfresh : ∀ v s, s ≤ T → (P s v = fresh ↔ s < r v) := by
    intro v s hsT
    constructor
    · intro hf
      by_contra hlt
      have h1 := hmono (show r v ≤ s by omega) hsT v
      have h2 := (PebblePhase.ne_fresh_iff_rank _).mp (hrne v)
      rw [hf] at h1; simp at h1; omega
    · intro hlt
      by_contra hne
      exact Nat.find_min (hex v) hlt ⟨hsT, hne⟩
  have hpos : ∀ v, r v ≠ 0 := by
    intro v h
    have := hrne v
    rw [h, h0] at this; exact this rfl
  have hprev : ∀ v, P (r v - 1) v = fresh := fun v =>
    (hfresh v _ (by have := hrT v; omega)).mpr (by have := hpos v; omega)
  -- the step `r v - 1 → r v` is the placement of `v`
  have hplace : ∀ v, P (r v) v = black ∧ ∀ y, D.Adj y v → (P (r v - 1) y).Pebbled := by
    intro v
    obtain ⟨t, ht⟩ : ∃ t, r v = t + 1 := ⟨r v - 1, by have := hpos v; omega⟩
    have hstep := hs t (by have := hrT v; omega)
    have h1 : P t v = fresh := by have := hprev v; rwa [ht, Nat.add_sub_cancel] at this
    have h2 : P (t + 1) v ≠ fresh := by have := hrne v; rwa [ht] at this
    rw [ht, Nat.add_sub_cancel]
    exact hstep.of_placed h1 h2
  -- only `v` changes at that step
  have hother : ∀ v w, w ≠ v → P (r v) w = P (r v - 1) w := by
    intro v w hwv
    obtain ⟨t, ht⟩ : ∃ t, r v = t + 1 := ⟨r v - 1, by have := hpos v; omega⟩
    have hstep := hs t (by have := hrT v; omega)
    have h1 : P t v = fresh := by have := hprev v; rwa [ht, Nat.add_sub_cancel] at this
    have h2 : P (t + 1) v ≠ fresh := by have := hrne v; rwa [ht] at this
    rw [ht, Nat.add_sub_cancel]
    by_contra hne
    exact hwv (hstep.eq_target (x := w) (y := v) (Ne.symm hne) (by rw [h1]; exact Ne.symm h2))
  have hr : Injective r := by
    intro u v huv
    by_contra hne
    have := hother v u hne
    rw [← huv, hprev u] at this
    exact hrne u this
  obtain ⟨σ, hσ⟩ := exists_layout_of_injective hr
  have hσlt : ∀ u v, σ u < σ v ↔ r u < r v := fun u v => by rw [← not_le, hσ, not_le]
  refine ⟨σ, fun u v huv => ?_, ?_⟩
  · -- topological: `u` is pebbled when `v` is placed, so `u` left `fresh` before
    rw [hσlt]
    have hp := (hplace v).2 u huv
    have hne : P (r v - 1) u ≠ fresh := by
      intro hf; rw [hf] at hp; simp [Pebbled] at hp
    have := (hfresh u (r v - 1) (by have := hrT v; omega)).not.mp hne
    have := hpos v
    omega
  · rw [layoutDemand_le_iff]
    intro i
    set v := σ.symm i with hv
    have hσv : σ v = i := by simp [hv]
    have hpeb : ∀ w ∈ preBoundary D R σ i.val, (P (r v) w).Pebbled := by
      intro w hw
      rw [mem_preBoundary_iff] at hw
      obtain ⟨hwi, hwR⟩ := hw
      have hwv : σ w < σ v := by rw [hσv]; exact Fin.lt_def.mpr hwi
      have hrw : r w < r v := (hσlt w v).mp hwv
      have hw1 : 1 ≤ (P (r v) w).rank := by
        have := hmono hrw.le (hrT v) w
        have := (PebblePhase.ne_fresh_iff_rank _).mp (hrne w)
        omega
      rw [pebbled_iff_rank]
      refine ⟨hw1, ?_⟩
      rcases hwR with hwR | ⟨u, hwu, hiu⟩
      · have hb : P (r v) w = black :=
          seqR_retained hs hwR (hplace w).1 hrw.le (hrT v)
        rw [hb]; simp [rank]
      · -- `u` is placed at or after `v`; at its placement `w` is pebbled
        have hvu : σ v ≤ σ u := by rw [hσv]; exact Fin.le_def.mpr hiu
        have hrvu : r v ≤ r u := (hσ v u).mp hvu
        have hwu' : w ≠ u := by
          intro h; subst h
          exact absurd (lt_of_lt_of_le hwv hvu) (lt_irrefl _)
        have hp := (hplace u).2 w hwu
        have hpr : (P (r u - 1) w).rank ≤ 2 := ((pebbled_iff_rank _).mp hp).2
        have hru : (P (r u) w).rank ≤ 2 := by rw [hother u w hwu']; exact hpr
        have := hmono hrvu (hrT u) w
        omega
    have hvpeb : (P (r v) v).Pebbled := by rw [(hplace v).1]; exact Or.inr rfl
    have hsub : insert v (preBoundary D R σ i.val) ⊆
        univ.filter fun x => (P (r v) x).Pebbled := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and]
      rcases mem_insert.mp hx with rfl | hx
      · exact hvpeb
      · exact hpeb x hx
    have hvnot : v ∉ preBoundary D R σ i.val := by
      rw [mem_preBoundary_iff, hσv]
      exact fun h => lt_irrefl _ h.1
    have hcard := card_le_card hsub
    rw [card_insert_of_notMem hvnot] at hcard
    have := seqR_numPebbles_le hs h0 (hrT v)
    unfold numPebbles at this
    omega

end Lower

/-! ### The upper bound: the strategy a layout induces -/

section Upper

variable {α : Type*} [Fintype α] [DecidableEq α] {D : Digraph α} [DecidableRel D.Adj]
variable {R : Finset α} {K : ℕ} (σ : LinearLayout α)

local notation "RReach" => Relation.ReflTransGen (BlackStepR D R K)

variable (D R) in
/-- After `i` vertices of `σ` are placed: those not retained with every successor placed are
cleared. -/
def doneR (i : ℕ) : Finset α :=
  univ.filter fun w => (σ w).val < i ∧ w ∉ R ∧ ∀ u, D.Adj w u → (σ u).val < i

theorem mem_doneR_iff (i : ℕ) (w : α) :
    w ∈ doneR D R σ i ↔
      (σ w).val < i ∧ w ∉ R ∧ ∀ u, D.Adj w u → (σ u).val < i := by
  simp [doneR]

theorem rreach_place {S Bl : Finset α} {x : α} (hxS : x ∉ S) (hxB : x ∉ Bl)
    (hp : ∀ y, D.Adj y x → y ∉ S ∧ y ∈ Bl)
    (hK : ((insert x Bl ∪ ∅) \ S).card ≤ K) :
    RReach (gpos S Bl ∅) (gpos S (insert x Bl) ∅) := by
  refine Relation.ReflTransGen.single ⟨.place x, ⟨by simp [gpos, hxS, hxB], fun y hy => ?_⟩,
    ?_, (numPebbles_gpos_le _ _ _).trans hK⟩
  · obtain ⟨hyS, hyB⟩ := hp y hy; simp [gpos, hyS, hyB, Pebbled]
  · funext w
    by_cases hw : w = x
    · subst hw; simp [BlackMove.apply, gpos, hxS]
    · simp [BlackMove.apply, gpos, hw]

theorem rreach_remove_set {S Bl : Finset α} (W : Finset α) (hWS : Disjoint W S) (hWB : W ⊆ Bl)
    (hWR : Disjoint W R) (hK : ((Bl ∪ ∅) \ S).card ≤ K) :
    RReach (gpos S Bl ∅) (gpos (S ∪ W) Bl ∅) := by
  induction W using Finset.induction_on with
  | empty => simp only [union_empty]; exact .refl
  | insert x W hx ih =>
    have hxS : x ∉ S := disjoint_left.mp hWS (mem_insert_self _ _)
    have hxR : x ∉ R := disjoint_left.mp hWR (mem_insert_self _ _)
    refine (ih (disjoint_of_subset_left (subset_insert _ _) hWS)
      ((subset_insert _ _).trans hWB) (disjoint_of_subset_left (subset_insert _ _) hWR)).trans ?_
    rw [union_insert]
    have hxSW : x ∉ S ∪ W := by simp [hxS, hx]
    have hxB : x ∈ Bl := hWB (mem_insert_self _ _)
    refine Relation.ReflTransGen.single ⟨.remove x,
      by simp [BlackMove.LegalR, gpos, hxSW, hxB, hxR],
      ?_, (numPebbles_gpos_le _ _ _).trans (le_trans (card_le_card
        (sdiff_subset_sdiff le_rfl (subset_union_left.trans (subset_insert _ _)))) hK)⟩
    funext w
    by_cases hw : w = x
    · subst hw; simp [BlackMove.apply, gpos]
    · simp [BlackMove.apply, gpos, hw]

/-- One step of the strategy: place `vᵢ` (its predecessors are earlier and still carry pebbles,
having a successor at `i`), then remove every unretained pebble whose successors are all
placed. -/
theorem rreach_step (hσ : IsTopological D σ) {i : ℕ} (hi : i < Fintype.card α)
    (hK : (preBoundary D R σ i).card + 1 ≤ K) :
    RReach (gpos (doneR D R σ i) (preBoundary D R σ i) ∅)
      (gpos (doneR D R σ (i + 1)) (preBoundary D R σ (i + 1)) ∅) := by
  classical
  set v := σ.symm ⟨i, hi⟩ with hvdef
  have hv : (σ v).val = i := by simp [hvdef]
  have hσeq : ∀ w, (σ w).val = i → w = v := fun w hw => by
    rw [hvdef, Equiv.eq_symm_apply]; exact Fin.ext hw
  set S := doneR D R σ i with hSdef
  set Bl := insert v (preBoundary D R σ i) with hBldef
  have hcard : ((Bl ∪ ∅) \ S).card ≤ K := by
    refine le_trans (card_le_card (s := (Bl ∪ ∅) \ S) (t := Bl) ?_) ?_
    · rw [union_empty]; exact sdiff_subset
    · exact (card_insert_le v (preBoundary D R σ i)).trans hK
  have hvS : v ∉ S := by
    rw [hSdef, mem_doneR_iff, hv]; exact fun h => lt_irrefl _ h.1
  have hvB : v ∉ preBoundary D R σ i := by
    rw [mem_preBoundary_iff, hv]; exact fun h => lt_irrefl _ h.1
  have h1 : RReach (gpos S (preBoundary D R σ i) ∅) (gpos S Bl ∅) := by
    refine rreach_place hvS hvB ?_ hcard
    intro y hyv
    have hlt : (σ y).val < i := by rw [← hv]; exact Fin.lt_def.mp (hσ y v hyv)
    refine ⟨fun h => ?_, ?_⟩
    · rw [hSdef, mem_doneR_iff] at h
      have := h.2.2 v hyv; omega
    · rw [mem_preBoundary_iff]
      exact ⟨hlt, Or.inr ⟨v, hyv, hv.ge⟩⟩
  set W := Bl.filter fun w => w ∉ R ∧ ∀ u, D.Adj w u → (σ u).val ≤ i with hWdef
  have hWS : Disjoint W S := by
    rw [disjoint_left]
    intro w hw hwS
    rw [hWdef, mem_filter] at hw
    rw [hSdef, mem_doneR_iff] at hwS
    rcases mem_insert.mp hw.1 with rfl | hw'
    · omega
    · rw [mem_preBoundary_iff] at hw'
      rcases hw'.2 with hwR | ⟨u, hwu, hiu⟩
      · exact hwS.2.1 hwR
      · have := hwS.2.2 u hwu; omega
  have hWR : Disjoint W R := by
    rw [disjoint_left]
    intro w hw hwR
    rw [hWdef, mem_filter] at hw
    exact hw.2.1 hwR
  have h2 : RReach (gpos S Bl ∅) (gpos (S ∪ W) Bl ∅) :=
    rreach_remove_set W hWS (filter_subset _ _) hWR hcard
  have heq : gpos (S ∪ W) Bl ∅ =
      gpos (doneR D R σ (i + 1)) (preBoundary D R σ (i + 1)) ∅ := by
    have hdone : ∀ w, w ∈ S ∪ W ↔ w ∈ doneR D R σ (i + 1) := by
      intro w
      rw [mem_union, hSdef, hWdef, mem_filter, mem_doneR_iff, mem_doneR_iff, hBldef, mem_insert,
        mem_preBoundary_iff]
      constructor
      · rintro (⟨h1, h2, h3⟩ | ⟨h1 | ⟨h1, -⟩, h2, h3⟩)
        · exact ⟨by omega, h2, fun u hu => by have := h3 u hu; omega⟩
        · subst h1; exact ⟨by omega, h2, fun u hu => by have := h3 u hu; omega⟩
        · exact ⟨by omega, h2, fun u hu => by have := h3 u hu; omega⟩
      · rintro ⟨h1, h2, h3⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h1 | h1
        · by_cases hall : ∀ u, D.Adj w u → (σ u).val < i
          · exact Or.inl ⟨h1, h2, hall⟩
          · obtain ⟨u, hu, hge⟩ : ∃ u, D.Adj w u ∧ i ≤ (σ u).val := by
              by_contra hcon
              exact hall fun u hu => by
                by_contra hge
                exact hcon ⟨u, hu, by omega⟩
            exact Or.inr ⟨Or.inr ⟨h1, Or.inr ⟨u, hu, hge⟩⟩, h2,
              fun u hu => by have := h3 u hu; omega⟩
        · exact Or.inr ⟨Or.inl (hσeq w h1), h2, fun u hu => by have := h3 u hu; omega⟩
    have hblack : ∀ w, w ∉ doneR D R σ (i + 1) →
        (w ∈ Bl ↔ w ∈ preBoundary D R σ (i + 1)) := by
      intro w hwd
      rw [mem_doneR_iff] at hwd
      rw [hBldef, mem_insert, mem_preBoundary_iff, mem_preBoundary_iff]
      constructor
      · intro hw
        have hlt : (σ w).val < i + 1 := by
          rcases hw with rfl | ⟨h1, -⟩
          · omega
          · omega
        refine ⟨hlt, ?_⟩
        by_cases hwR : w ∈ R
        · exact Or.inl hwR
        · by_cases hall : ∀ u, D.Adj w u → (σ u).val < i + 1
          · exact absurd ⟨hlt, hwR, hall⟩ hwd
          · obtain ⟨u, hu, hge⟩ : ∃ u, D.Adj w u ∧ i + 1 ≤ (σ u).val := by
              by_contra hcon
              exact hall fun u hu => by
                by_contra hge
                exact hcon ⟨u, hu, by omega⟩
            exact Or.inr ⟨u, hu, hge⟩
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h1 | h1
        · refine Or.inr ⟨h1, ?_⟩
          rcases h2 with h2 | ⟨u, hu, hge⟩
          · exact Or.inl h2
          · exact Or.inr ⟨u, hu, by omega⟩
        · exact Or.inl (hσeq w h1)
    funext w
    simp only [gpos, notMem_empty, ↓reduceIte]
    by_cases hw : w ∈ doneR D R σ (i + 1)
    · have hw' := (hdone w).mpr hw
      simp only [hw, hw', ↓reduceIte]
    · have hw' : w ∉ S ∪ W := fun h => hw ((hdone w).mp h)
      simp only [hw, hw', ↓reduceIte]
      exact if_congr (hblack w hw) rfl rfl
  rw [← heq]
  exact h1.trans h2

theorem gpos_doneR_zero : gpos (doneR D R σ 0) (preBoundary D R σ 0) ∅ = fun _ => fresh := by
  funext w; simp [gpos, doneR, preBoundary]

theorem gpos_doneR_card_ne_fresh (x : α) :
    gpos (doneR D R σ (Fintype.card α)) (preBoundary D R σ (Fintype.card α)) ∅ x ≠
      fresh := by
  simp only [gpos, notMem_empty, ↓reduceIte]
  by_cases hd : x ∈ doneR D R σ (Fintype.card α)
  · simp [hd]
  · have hb : x ∈ preBoundary D R σ (Fintype.card α) := by
      rw [mem_preBoundary_iff]
      refine ⟨(σ x).isLt, Or.inl ?_⟩
      by_contra hxR
      exact hd ((mem_doneR_iff σ _ x).mpr ⟨(σ x).isLt, hxR, fun u _ => (σ u).isLt⟩)
    simp [hd, hb]

/-- **The upper bound.** Placing in the order of a topological layout `σ` and dropping each
unretained pebble as soon as its last successor is placed is a play within `K` pebbles for
every `K ≥ layoutDemand D R σ`. -/
theorem blackPebblesWithinR_of_isTopological_of_le (hσ : IsTopological D σ)
    (hK : layoutDemand D R σ ≤ K) : BlackPebblesWithinR D R K := by
  have hstep : ∀ i ≤ Fintype.card α,
      RReach (gpos (doneR D R σ 0) (preBoundary D R σ 0) ∅)
        (gpos (doneR D R σ i) (preBoundary D R σ i) ∅) := by
    intro i hi
    induction i with
    | zero => exact .refl
    | succ i ih =>
      refine (ih (by omega)).trans (rreach_step σ hσ (by omega) ?_)
      exact (card_preBoundary_add_one_le_layoutDemand D R σ ⟨i, by omega⟩).trans hK
  refine ⟨_, ?_, gpos_doneR_card_ne_fresh (D := D) (R := R) σ⟩
  have := hstep _ le_rfl
  rwa [gpos_doneR_zero (D := D) (R := R) σ] at this

theorem blackPebblesWithinR_of_isTopological (hσ : IsTopological D σ) :
    BlackPebblesWithinR D R (layoutDemand D R σ) :=
  blackPebblesWithinR_of_isTopological_of_le σ hσ le_rfl

end Upper

/-! ### The formula -/

section Formula

variable {α : Type*} [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
variable (R : Finset α)

/-- **The layout formula**: `pbR D R = topologicalDemand D R` for every digraph on a finite
type and every retained set. Both sides are `0` when `D` has no topological layout. -/
theorem pbR_eq_topologicalDemand : pbR D R = topologicalDemand D R := by
  unfold pbR topologicalDemand
  by_cases hex : ∃ σ : LinearLayout α, IsTopological D σ
  · obtain ⟨σ, hσ⟩ := hex
    have hS : {K | BlackPebblesWithinR D R K}.Nonempty :=
      ⟨_, blackPebblesWithinR_of_isTopological σ hσ⟩
    have hRg : (Set.range fun σ : {σ : LinearLayout α // IsTopological D σ} =>
        layoutDemand D R σ.1).Nonempty := ⟨_, ⟨σ, hσ⟩, rfl⟩
    apply le_antisymm
    · refine le_csInf hRg ?_
      rintro k ⟨σ', rfl⟩
      exact Nat.sInf_le (blackPebblesWithinR_of_isTopological σ'.1 σ'.2)
    · obtain ⟨σ'', hσ'', hle⟩ :=
        exists_isTopological_of_blackPebblesWithinR (Nat.sInf_mem hS)
      have hmem : layoutDemand D R σ'' ∈
          Set.range fun σ : {σ : LinearLayout α // IsTopological D σ} =>
            layoutDemand D R σ.1 :=
        ⟨⟨σ'', hσ''⟩, rfl⟩
      exact (Nat.sInf_le hmem).trans hle
  · have hS : {K | BlackPebblesWithinR D R K} = ∅ :=
      Set.eq_empty_of_forall_notMem fun K (hK : BlackPebblesWithinR D R K) =>
        hex (let ⟨σ, hσ, _⟩ := exists_isTopological_of_blackPebblesWithinR hK; ⟨σ, hσ⟩)
    have hR : Set.range (fun σ : {σ : LinearLayout α // IsTopological D σ} =>
        layoutDemand D R σ.1) = ∅ :=
      Set.eq_empty_of_forall_notMem fun k ⟨σ, _⟩ => hex ⟨σ.1, σ.2⟩
    rw [hS, hR]

/-- Kirousis & Papadimitriou's `pb` is the least layout demand with nothing retained. -/
theorem pb_eq_topologicalDemand : pb D = topologicalDemand D ∅ := by
  rw [← pbR_empty, pbR_eq_topologicalDemand]

/-- Garey & Johnson's REGISTER SUFFICIENCY is the least layout demand with the outputs
retained. -/
theorem registerDemand_eq_topologicalDemand :
    registerDemand D = topologicalDemand D (outputs D) :=
  pbR_eq_topologicalDemand D (outputs D)

end Formula

/-! ### `pbw ≤ pb` -/

section Pbw

variable {α : Type*} [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]

/-- `pbw D ≤ pb D` whenever the black game has a play (a black play is a black-white play). -/
theorem pbw_le_pb_of_exists (h : ∃ K, BlackPebblesWithin D K) : pbw D ≤ pb D := by
  have hmem : BlackPebblesWithin D (pb D) := Nat.sInf_mem h
  exact Nat.sInf_le hmem.pebblesWithin

/-- `pw(G_u) + 1 ≤ pb D` on a nonempty digraph with a play of the black game. -/
theorem pathwidth_lengauerU_add_one_le_pb [Nonempty α] (h : ∃ K, BlackPebblesWithin D K) :
    pathwidth (lengauerU D) + 1 ≤ pb D := by
  rw [← pbw_eq_pathwidth_lengauerU_add_one]
  exact pbw_le_pb_of_exists D h

end Pbw

end Complex

end MOSPFormalization
