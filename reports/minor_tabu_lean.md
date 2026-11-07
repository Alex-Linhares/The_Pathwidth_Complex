# The tabu search over contraction minors: its certificates are sound (Lean)

*2026-11-07. Files: `lean/MOSPFormalization/Search/MinorTabu.lean` (568 lines) and
`lean/MOSPFormalization/Blockage.lean` (233 lines), both imported by
`lean/MOSPFormalization.lean`; checks and logs under `reports/scratch/minor_tabu_lean/`.
No `sorry`, no `axiom`; `lake build` clean (the two new modules build with no diagnostic,
`lake_build.log`); every one of the 45 audited theorems depends on `propext`,
`Classical.choice`, `Quot.sound` and nothing else (`axiom_check.lean`, `axiom_check.log`).*

## 0. Summary

`pathwidth_solver/cli/minor_tabu.c` walks over sets `F` of edges of `G` (kept acyclic), reads
the minor `H = G / F` (`build_minor`), and reports a floor on `pathwidth G` with a certificate:
the contraction sequence `print_sequence` emits from `F` by a union-find walk, and a kind —
`"refutation"` (the engine refuted width `w` on `H`, floor `w + 1`) or
`"contraction_degeneracy"` (the MMD+ value of `H`). This note proves, in Lean 4 over Mathlib:

1. **The emitted sequence is a legal contraction sequence of `G`, and its minor *is* the
   quotient `G / F`** — the exact identification, not the weaker form. For any list of edges
   of `G` in any order (acyclicity is not needed and not assumed):
   `applySeq G (ufSeq id F) = quotient G (ufRep id F)` and
   `x ∈ removed (ufSeq id F) ↔ ufRep id F x ≠ x`, so `tabuMinor G F := minorOf G (ufSeq id F)`
   is `G / F` on the representatives, which is `build_minor`'s `H` up to its `index`
   relabelling; `IsContractionSeq G (ufSeq id F)`; `pathwidth (tabuMinor G F) ≤ pathwidth G`.
2. **Both certificate kinds are sound**: `floor_sound_of_refutation`
   (`¬ pathwidth (tabuMinor G F) ≤ w → w + 1 ≤ pathwidth G`) and `floor_sound_of_degeneracy`
   (every minimum degree MMD+ reads on any further contraction of the minor is
   `≤ pathwidth G`), plus the plain-degeneracy form.
3. **The run**: with `Run` = a given floor (`-L`) and a list of visited forests with claimed
   floors, `Justified` = the two certificate kinds, and `output` = the maximum:
   `tabu_output_le_pathwidth` (a sound run's output is a floor),
   `tabu_output_ge_of_visited_refutation` (a visited forest whose engine call refuted `w − 1`
   puts `w ≤ output`), `exists_visited_of_le_output` (a floor reached above the given one is
   a visited minor of pathwidth at least that floor), and `output_eq_pathwidth_iff` (the
   output is the recorded width exactly when a visited minor carries that claim, and then its
   pathwidth equals the graph's).
4. **Checked before stated**: `check.py` on every graph of the atlas to 7 vertices with
   random sub-forests and arbitrary edge subsets (15,024 of them, 3,382 cyclic, 68,333 emitted
   pairs, 104,390 further sequences on the minors, 3,756 simulated runs), pathwidth by vertex
   separation over all orderings: **zero violations** (`run.log`).
5. **Axiom audit**: 45 theorems, all on the three standard axioms.
6. **Optional, done**: the Bienstock–Robertson–Seymour–Thomas blockage of order `n` is
   defined exactly as in Section 2 (`att`, complementary pairs, axioms (i)–(iii)), and the
   weak half of their Theorem (2.1), **a blockage of order `n` implies `pathwidth G ≥ n`**,
   is proved `sorry`-free (`pathwidth_ge_of_isBlockage`), by the paper's own argument (Lemma
   (2.2), `∅ ∈ 𝓑`, `V ∉ 𝓑`, the prefix unions of a path decomposition). Checked first by
   `check_blockage.py`: both halves of (2.1) by exhaustive enumeration of all set families on
   every graph to 4 vertices (108 cases, 39 blockages found, consistent both ways), and the
   proof's set facts on every layout of every graph to 7 vertices (5,378,453 layouts,
   37.5 M steps, 17.8 M subset pairs): **zero violations** (`run_blockage.log`).

Nothing was solved, re-solved or certified; no binary was run; `solutions/` is untouched.

## 1. What the C program does, and what is modelled

The state is `in_forest`, a subset `F` of the edges of `G`. `build_minor` runs a union-find
over the edges of `F` in index order (`rep[a] = b` for `a = find(eu)`, `b = find(ev)`,
skipping an edge whose ends are already in one block), then makes `H` on the representatives
with `index[v] = H`-vertex of `v`'s representative and an `H`-edge between the blocks of
every `G`-edge. `print_sequence` runs the same walk and prints `[a, b]` for every edge not
skipped — contract `a` into `b`, which in `Minor.lean`'s vocabulary is the step
`(a, some b)` (`contractEdge G b a`: `b` keeps its label and gains `a`'s neighbours, `a` is
left isolated). The floor is `floor`, raised either by `decide(&H, floor + 1, …) == UNSAT`
(`best_kind = "refutation"`, `"refuted" = floor − 1`) or by `contraction_degeneracy(&H)`
(`best_kind = "contraction_degeneracy"`, MMD+ of `pathwidth.c`: contract a minimum-degree
vertex into the neighbour with fewest common neighbours, drop it when isolated, report the
largest minimum degree read on the alive set), with the starting floor `max(-L, lower_bound(G))`
where `lower_bound = max(degeneracy, contraction_degeneracy)` of `G` itself, and an exact
step on `G` itself when `n ≤ max_exact`.

In Lean (`MinorTabu` namespace):

| C | Lean |
|---|---|
| `rep` after merging edge `(p, q)` | `mergeRep r p q = fun x => if r x = r p then r q else r x` |
| the walk's final `rep` | `ufRep r es` |
| `print_sequence` | `ufSeq r es` (`(r p, some (r q))` per non-skipped edge) |
| `build_minor`'s `H` | `quotient G r` on the representatives: `x ~ y ↔ x ≠ y ∧ r x = x ∧ r y = y ∧ ∃ p q, G.Adj p q ∧ r p = x ∧ r q = y`; then `tabuMinor G F = minorOf G (ufSeq id F)` |
| `in_forest` is a forest of `G`-edges | `EdgesOf G F` (every pair an edge); `IsForest G F` adds `IsAcyclic` of the spanned subgraph — **defined, never assumed** |
| `"kind": "refutation"`, `"floor" = w + 1`, `"refuted" = w` | `Justified.refutation : ¬ pathwidth (tabuMinor G F) ≤ w → Justified G F (w + 1)` |
| `"kind": "contraction_degeneracy"`, `"floor" = v` | `Justified.contractionDegeneracy : IsContractionSeq (tabuMinor G F) seq₂ → v ≤ minDegreeIn (applySeq (tabuMinor G F) seq₂) S → Justified G F v` |
| the run; `-L`; `floor` at the end | `Run G` = `given : ℕ`, `claims : List (List (V × V) × ℕ)`; `Run.output = claims.foldr (max ∘ snd) given`; `Run.Sound` = `given ≤ pathwidth G ∧ ∀ c ∈ claims, Justified G c.1 c.2` |

The whole-graph floors (`lower_bound(G)`, the exact step on `G`) are claims on the empty
forest (`tabuMinor G [] ≅ G`); the `-L` input is `given`, trusted by hypothesis (it is an
input, not a result of the run). The tabu list, the band `[lo, hi]`, the sampling, the
aspiration rule and the seeding are not modelled: they decide *which* forests are visited,
and every theorem is for an arbitrary list of visited forests.

**On the degeneracy kind.** `ObstructionCertificate.lean` (loop0013) records that the C
program's floor on a minor is its *contraction* degeneracy (MMD+), not its minimum degree,
and that the MMD+ contractions behind it are not emitted. The soundness statement here
therefore quantifies over *every* legal sequence `seq₂` on the minor and every vertex set
`S`: whatever MMD+ contracted, each value it read is `minDegreeIn (applySeq H seq₂) S` for
the alive set `S` at that moment (a dropped isolated vertex is the step `(v, none)`), and
`floor_sound_of_degeneracy` bounds every such value by `pathwidth G`. It does not need the
sequence, so the un-emitted contractions are no gap for soundness; they would be needed only
for a *replayable* certificate of that kind, which remains the proposal of loop0013.

## 2. The theorems (one line each)

All in `MOSPFormalization.MinorTabu` unless noted; `V` finite with decidable equality,
`G : SimpleGraph V`, `[DecidableRel G.Adj]` where `minDegreeIn` appears.

**The walk.**
- `Idem r := ∀ x, r (r x) = r x`; `idem_id`; `Idem.mergeRep`; `Idem.ufRep` — representative maps stay idempotent.
- `mergeRep_ne_self`, `ufRep_ne_self` — `Idem r → r x ≠ x → ufRep r es x ≠ x`: a label once lost is never regained.
- `quotient_id : quotient G id = G`.
- `quotient_adj_rep : Idem r → G.Adj p q → r p ≠ r q → (quotient G r).Adj (r q) (r p)` — the printed pair is an edge of the current graph.
- `contractEdge_quotient : Idem r → r p ≠ r q → contractEdge (quotient G r) (r q) (r p) = quotient G (mergeRep r p q)` — **one step of the walk is one contraction** (the identity needs no edge; the edge makes the step legal).
- `applySeq_ufSeq : Idem r → EdgesOf G es → applySeq (quotient G r) (ufSeq r es) = quotient G (ufRep r es)`.
- `isContractionSeq_ufSeq : Idem r → EdgesOf G es → IsContractionSeq (quotient G r) (ufSeq r es)`.
- `mem_removed_ufSeq : Idem r → (x ∈ removed (ufSeq r es) ↔ r x = x ∧ ufRep r es x ≠ x)`.
- `applySeq_ufSeq_id : EdgesOf G es → applySeq G (ufSeq id es) = quotient G (ufRep id es)` — **the replay is the quotient**.
- `isContractionSeq_ufSeq_id : EdgesOf G es → IsContractionSeq G (ufSeq id es)` — **the printed sequence is legal** (item 1's deliverable).
- `mem_removed_ufSeq_id : x ∈ removed (ufSeq id es) ↔ ufRep id es x ≠ x`; `removed_ufSeq_id_eq` — the removed vertices are exactly the non-representatives.
- `tabuMinor_eq : EdgesOf G F → tabuMinor G F = (quotient G (ufRep id F)).induce {x | x ∉ removed (ufSeq id F)}` — **the exact identification** of `minorOf G seq` with `G / F`.
- `pathwidth_tabuMinor_le : EdgesOf G F → pathwidth (tabuMinor G F) ≤ pathwidth G`.
- `IsForest.edgesOf`, `IsForest.isContractionSeq`, `IsForest.pathwidth_le` — the same under the forest hypothesis (trivial specialisations).

**The two kinds.**
- `floor_sound_of_refutation : EdgesOf G F → ¬ pathwidth (tabuMinor G F) ≤ w → w + 1 ≤ pathwidth G`.
- `floor_sound_of_degeneracy : EdgesOf G F → IsContractionSeq (tabuMinor G F) seq₂ → minDegreeIn (applySeq (tabuMinor G F) seq₂) S ≤ pathwidth G`.
- `degeneracy_tabuMinor_le : EdgesOf G F → degeneracy (tabuMinor G F) ≤ pathwidth G`.
- `Justified.edgesOf`, `Justified.le_pathwidth_tabuMinor : Justified G F v → v ≤ pathwidth (tabuMinor G F)`, `Justified.le_pathwidth : Justified G F v → v ≤ pathwidth G`.

**The run.**
- `Run.le_output_iff : w ≤ R.output ↔ w ≤ R.given ∨ ∃ c ∈ R.claims, w ≤ c.2`; `Run.given_le_output`.
- `tabu_output_le_pathwidth : R.Sound → R.output ≤ pathwidth G`.
- `tabu_output_ge_of_visited_refutation : (F, w) ∈ R.claims → w ≤ R.output`; `tabu_output_ge_of_refuted : (F, w + 1) ∈ R.claims → w < R.output`.
- `exists_visited_of_le_output : R.Sound → R.given < w → w ≤ R.output → ∃ c ∈ R.claims, w ≤ pathwidth (tabuMinor G c.1)`.
- `reaches_iff : R.given < w → (w ≤ R.output ↔ ∃ c ∈ R.claims, w ≤ c.2)`.
- `output_eq_pathwidth_iff : R.Sound → R.given < pathwidth G → (R.output = pathwidth G ↔ ∃ c ∈ R.claims, c.2 = pathwidth G ∧ pathwidth (tabuMinor G c.1) = pathwidth G)`.

**MOSP units** (`MOSPInstance`): `floor_sound_of_refutation_mosp : EdgesOf M.mospGraph F → ¬ pathwidth (tabuMinor M.mospGraph F) ≤ w → w + 1 < M.mospValue` (no hypothesis on the instance); `tabu_output_lt_mospValue : (∃ c p, M.requires c p) → R.Sound → R.output < M.mospValue`.

**Blockages** (`MOSPFormalization.Blockage`): `att G X = X.filter (∃ u ∉ X, G.Adj v u)`; `compl G X = (univ \ X) ∪ att G X`; `Complementary G X₁ X₂ := X₁ ∪ X₂ = univ ∧ att G X₁ ⊆ X₂`; `IsBlockage G n B` = (i) `∀ X ∈ B, (att G X).card ≤ n`, (ii) `∀ X ∈ B, ∀ Y ⊆ X, (att G Y).card ≤ n → Y ∈ B`, (iii) `∀ X₁ X₂, Complementary G X₁ X₂ → (X₁ ∩ X₂).card ≤ n → Xor (X₁ ∈ B) (X₂ ∈ B)`.
- `complementary_compl`, `inter_compl : X ∩ compl G X = att G X`, `complementary_union_compl : Complementary G (X ∪ Y) (compl G X)`, `union_inter_compl : (X ∪ Y) ∩ compl G X = (Y \ X) ∪ att G X`.
- `IsBlockage.mem_of_mem` — **Lemma (2.2)**: `X ∈ B → (att G Y).card ≤ n → ((Y \ X) ∪ att G X).card ≤ n → Y ∈ B`.
- `IsBlockage.empty_mem_and_univ_not_mem : ∅ ∈ B ∧ univ ∉ B`.
- `prefixUnion P i = W_0 ∪ ⋯ ∪ W_{i−1}`; `prefixUnion_zero`, `prefixUnion_last`; `att_prefixUnion_subset : i ≤ length → att G (prefixUnion P i) ⊆ P.bag i`; `att_prefixUnion_succ_subset : att G (prefixUnion P (i+1)) ⊆ P.bag i`; `prefixUnion_succ_sdiff_subset : prefixUnion P (i+1) \ prefixUnion P i ⊆ P.bag i`.
- `pathwidth_ge_of_isBlockage : IsBlockage G n B → n ≤ pathwidth G` — **the weak half of (2.1)**.

## 3. What is proved exactly, and what is weaker

- Item 1 is proved in the **exact** form: `tabuMinor G F` is identified with the quotient
  `G / F` on the representatives (`tabuMinor_eq`, `mem_removed_ufSeq_id`), not merely shown
  to be some legal sequence. The identification is with `G / F` on `G`'s own labels; the C
  program's `index` relabelling to `0..h−1` is an isomorphism, under which pathwidth is
  invariant (`pathwidth_eq_of_iso`, `Minor.lean`); the relabelling itself is not
  constructed in Lean.
- The theory is **more general than the C's state**: any list of `G`-edges in any order,
  cyclic or not. Acyclicity is defined (`IsForest`, Mathlib's `SimpleGraph.IsAcyclic` on
  `fromEdgeSet`) and never used: it is the C's bookkeeping invariant (an addition shrinks
  the minor by exactly one vertex, so the band `[lo, hi]` is tracked by counting). The
  check measured it — on all 11,642 acyclic subsets the walk skipped no edge and the minor
  had `n − |F|` vertices; on all 3,382 cyclic ones at least one edge was skipped — but no
  Lean theorem about it was attempted, since nothing in soundness depends on it.
- "Any union-find order works" is covered because `es` is an arbitrary list: a different
  walk order is a different list, and path compression changes `rep`'s internal pointers,
  not the representative function the theorems are about.
- The degeneracy kind is stated over any further sequence on the minor and any set `S`
  (§1 above): stronger than "degeneracy ≤ pathwidth", which is included
  (`degeneracy_tabuMinor_le`), and sufficient for MMD+ without the un-emitted contractions.
- `tabu_output_ge_of_visited_refutation` is stated with the claim `(F, w) ∈ R.claims` as
  the hypothesis — the brief's "some visited forest's minor has `w ≤ pathwidth (minor)`
  (equivalently, the engine refuted `w − 1` on it)". The parenthetical is the claim; the
  mathematical property alone does not put `w` in the output, because a visited minor on
  which the engine's node budget ran out is not reported, and the check's run model
  confirms that direction cannot be strengthened. The converse — every reported floor above
  the given one is a visited minor of pathwidth at least the floor — is
  `exists_visited_of_le_output`, and `output_eq_pathwidth_iff` combines them for the
  recorded width.
- The `-L` floor is trusted by hypothesis (`R.Sound`'s first conjunct). A run started from
  an unsound `-L` reports an unsound floor; this is the flag's contract, not the search's.
- Not modelled: that the binary computes what the model says (the engine's `decide` on
  `H` is covered by `Search/`'s soundness theorems and the binary's faithfulness, as for
  every refutation in this project), and the JSON itself.
- Blockage: only the weak half of (2.1). The converse (pathwidth `≥ n` gives a blockage,
  via partial blockages and fractures, (2.3)–(2.5)) was not attempted. The paper's graphs may
  have loops and multiple edges; here they are simple, which changes nothing in Section 2.
  The paper's proof uses bags; the layout form of the check (prefixes of a layout with the
  decomposition `W_i = att(S_{i−1}) ∪ {v_i}`) is the same chain of sets.

## 4. Checks before statements

`reports/scratch/minor_tabu_lean/check.py` (`python3 -I check.py --forests 12 --seed 0`,
31.6 s, `run.log`): every graph of the networkx atlas on 1–7 vertices (1,252), per graph
twelve edge subsets alternating random sub-forests (as the C's state) and arbitrary subsets
(cyclic allowed), a quarter of them in a shuffled order; the walk replayed exactly as
`print_sequence`; (A) every emitted pair an edge of the current graph under `contractEdge`
semantics; (B) the replay equals the quotient, the removed set equals the non-representatives,
the survivors' graph equals `build_minor`'s `H`; (C) `pw(minor) ≤ pw(G)` by vertex separation
over all orderings (tight on 1,614 of 15,024); (D) MMD+ reimplemented from `pathwidth.c` on
every minor, each value it reads checked as `minDegreeIn (applySeq minor seq₂) S ≤ pw(G)`,
plus random legal sequences with random `S`; (E) simulated runs with both kinds and a given
floor: output `≤ pw(G)`, and `w ≤ output → ∃` visited minor with `pw ≥ w`, and the iff on
claims; (F) acyclicity's role. Zero violations in every column.

`check_blockage.py` (`python3 -I check_blockage.py`, 52 s, `run_blockage.log`): as in §0 item 6.

The Lean statements were written after these runs and transcribe what was checked.

## 5. Build and audit

`cd lean && lake build`: exit 0; `Built MOSPFormalization.Blockage (1.3s)`,
`Built MOSPFormalization.Search.MinorTabu (1.4s)`, no diagnostic on either
(`lake_build.log`; the warnings in the log are cached ones from untouched modules).
`lake env lean ../reports/scratch/minor_tabu_lean/axiom_check.lean`: 45 `#print axioms`
lines, each `[propext, Classical.choice, Quot.sound]`, none with `sorryAx`
(`axiom_check.log`). `grep sorry` on both files: nothing.

## 6. Lessons

- `pkill -f <pattern>` matched the session's own shell once more (the pattern was in its
  command line); the stuck Lean process was then gone, but so was the edit in the same
  command. Already in `CLAUDE.md`'s method notes; recorded again.
- A `h ▸ ?_` with an unresolved goal inside a `refine` tuple sent the elaborator into a
  twenty-minute stall with no diagnostic. Replacing it with the explicit `fun h => hy'.2 h.symm`
  compiled the file in 2.4 s.
- Inside `theorem Idem.mergeRep`, the bare name `mergeRep` resolves to the theorem being
  defined, not the function; qualify it.
- `Xor'` and `if_pos`/`if_neg`/`push_neg` are deprecated in this toolchain
  (`Xor`, `ite_eq_left`/`ite_eq_right`, `push Not`).
