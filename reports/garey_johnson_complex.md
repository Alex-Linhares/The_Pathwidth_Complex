# Garey & Johnson's list and the pathwidth complex

*2026-11-11, one session. Source: Garey & Johnson (1979), *Computers and
Intractability*, Appendix A (pp. 187–288), the Update for the current printing
(p. 339) and the subject and reference indexes, read from the scan
`literature/1979-Garey-Johnson-Computers-and-Intractability-NP-Completeness.pdf`
(two book pages per sheet, rendered with `pdftoppm` at 110–130 dpi and read as
images; the OCR text `…ocr.txt` that arrived mid-session was used only to locate
bibliography entries, and every code, page and name quoted below was read from
a rendered sheet). Page numbers are the printed ones. Sheet list in §7. Every
relation claimed below is either G&J's own comment, a cited paper, or an
argument of ours checked by brute force with the repository's exact pathwidth
(`fixed_parameter_algorithm/pathwidth.py`); the scripts are under
`reports/scratch/garey_johnson/` with a regenerate command in each header.
Nothing was solved on any instance on record; the only computation is on graphs
to 8 vertices (about 2 core-minutes). "We found no prior statement" is the
strongest attribution used.*

## 0. Summary

**Examined**: all 65 Graph Theory entries (GT1–GT65, pp. 190–205) in full; the
other categories by every entry title with the full text of each entry whose
instance is an ordering, a layout, a completion, a matrix permutation, a
pebbling or a register count — ND14, ND17, ND47 (pp. 209–218), SR2, SR5,
SR13–SR19 (pp. 226–230), SS7 (p. 238), PO1–PO6 (pp. 272–273), OPEN1–OPEN12
(pp. 285–288) and the Update (p. 339): **85 entries read in full, the rest of
the ~300 by title**. Categories A6, A7, A9 and A10 (mathematical programming,
number theory, logic, automata; pp. 245–271) were scanned in the subject index
only; none of their titles names an ordering or a width.

**Members, exact or sandwich: none.** The 1979 list contains no member of the
pathwidth complex. It has no graph-searching, interval-thickness, gate-matrix
or vertex-separation entry: the search problem (Parsons 1976) was shown
NP-complete only in Megiddo, Hakimi, Garey, Johnson & Papadimitriou (1988,
held; its §5 relates the search number to cutwidth, with the star as the
separating example), interval thickness is Kashiwabara & Fujisawa (1979), the
same year, and vertex separation is later (Lengauer 1981). Table 1 of Linhares
& Yanasse (2002), our Section 3, does not cite G&J for any member, and that is
right.

**Already in our table under another name (as relatives, not members):**

| G&J | name | our row / report | relation |
|---|---|---|---|
| GT40 (p. 200) | Bandwidth | `Sandwich.lean` `pathwidth_le_bandwidth`; `reports/complex_lb_layout.md` §0.1 | `pw ≤ bw`, gap unbounded (`K_{1,k}`: `bw = ⌈k/2⌉`, `pw = 1`; smallest gap `K_{1,3}`) |
| GT44 (p. 201) | Minimum cut linear arrangement (= cutwidth) | row 11, `Complex/EdgeSeparation.lean` `cutwidth_unbounded`, `pathwidth_le_cutwidth` | `pw ≤ cw ≤ Δ·pw`, gap unbounded on stars (smallest `K_{1,3}`) |
| GT42, GT43 (p. 200) | Optimal linear arrangement, directed | `complex_lb_layout.md` §0.1 (MinLA) | sum objective: `MinLA ≤ nΔ·pw`, no lower relation; unbounded by disjoint unions of edges |
| GT35 (p. 198) | Interval graph completion (**edges added**, not clique size) | profile = sum cut, `complex_lb_layout.md` §0.1 | `= profile(G) − |E|` (one-line proof, §3.3; checked on every graph to 6 vertices); its max-clique sibling is row 5, interval thickness `= pw + 1`, which G&J do not list |
| GT46 (p. 201), OPEN4 (p. 286) | Directed elimination ordering, chordal graph completion (fill-in) | treewidth, `Sandwich.lean` `treewidth_le_pathwidth` | fill-in is a sum; the clique-size sibling is treewidth, `tw ≤ pw`, unbounded gap |
| GT47 (p. 201) | Elimination degree sequence | `Sandwich.lean` `degeneracy_le_pathwidth` | its min–max relaxation **is the degeneracy** (checked, 1,251 graphs); `degeneracy ≤ pw`, unbounded on trees; smallest gap at 5 vertices |
| ND17 (p. 210) | Minimum cut into bounded sets (edge bisection) | Harper at `t = ⌊n/2⌋`, `EmptyPair.lean` | the *vertex* bisection is one level of Harper and `≤ vs`; the edge version is unbounded on stars |
| PO1 (p. 272) | Register sufficiency (= one-shot black pebbling, outputs retained) | row 13 (progressive pebbling, `PebblingGu.lean`) | **`pb(D) ≥ pbw(D) = pw(G_u) + 1`** is a theorem (a black play is a black-white play); strict from 5 vertices, gap 2 at 7–8; the minimum over acyclic orientations is `pw(G) + 1` (Kirousis & Papadimitriou Thm 3.1, row 13) |

**New candidates: none that is a member; two that contain the complex.**

- **SS7 Sequencing to minimize maximum cumulative cost** (p. 238; Abdel-Wahab
  1976): a linear extension of a poset with task costs in `Z` minimising the
  largest prefix sum. **It contains MOSP exactly** — tasks `open(c)` (+1),
  `close(c)` (−1), product `p` (0), `open(c) ≺ p ≺ close(c)` for `p ∈ P_c`;
  the SS7 optimum of the encoded poset equals the MOSP optimum, i.e.
  `pw(MOSP graph) + 1`, on 300 random instances (§3.1) — and **it contains
  PO1 exactly** through the encoding G&J's reference uses (checked on all
  1,099 dags to 5 vertices). G&J's own reduction chain is PO1 → SS7, so the
  1979 list already carries open stacks, as a special case, without naming
  them. SS7 itself is a common generalisation (MOSP with precedence among
  products and unpaired opens and closes); we know no derived graph on which
  it is `pw + c`, and §3.1 says what a proof or a refutation needs.
- **PO1 Register sufficiency** (Sethi 1975): the one-sided bound above. The
  black game is a *constrained vertex separation* — `pb(D) = 1 + min` over
  **topological** layouts of the left boundary just before each placement
  (checked on all 33,867 dags to 6 vertices, §3.2) — so it is pathwidth of the
  underlying graph with a precedence constraint on the layout, which white
  pebbles remove (Lengauer's theorem). Whether `pb − pbw` is bounded is open
  here; the data (0, 0, 0, 1, 1, 2, 2 at `n = 2..8`) say it grows.

**Non-members with the obstruction** (each with a brute-force witness):
GT40 and GT41 (bandwidth: stars; the directed out-star has directed bandwidth
`k` against `pw 1`), GT42/GT43/GT45/GT46/OPEN4/GT36/SR5/SR16 (sum objectives:
a disjoint union of `k` edges has `pw 1` and cost growing with `k`; SR16 on the
edge–vertex incidence matrix *is* `MinLA − |E|`, G&J's own transformation,
checked on 92 graphs), GT35 (profile: `C_n` needs `n − 3` edges at `pw 2`,
`K_n` needs 0 at `pw n − 1`), GT44 (cutwidth: stars), GT47 (degeneracy:
trees), SR2 (the intervals are given, not chosen: with unit sizes it is
interval-graph colouring, the fixed-order case of MOSP), PO2–PO6 (constrained
or sum variants of PO1), ND14/ND17 (edge cuts).

**What G&J settle that the paper's related work can cite** (§4): bandwidth
NP-complete [Papadimitriou 1976a], even for trees of maximum degree 3 [Garey,
Graham, Johnson & Knuth 1978]; cutwidth NP-complete [Stockmeyer 1974b, private
communication; Gavril 1977a]; MinLA NP-complete [Garey, Johnson & Stockmeyer
1976], polynomial on trees [Shiloach 1976; Gol'dberg & Klipker 1976]; interval
completion by edges NP-complete [Garey, Gavril & Johnson 1977, unpublished],
even on line graphs, polynomial at `K = 0` [Fulkerson & Gross 1965; Booth &
Lueker 1976]; register sufficiency NP-complete [Sethi 1975] even at out-degree
≤ 2, the recomputation variant NP-hard and "not known to be in NP" (later
PSPACE-complete, Gilbert, Lengauer & Tarjan 1980, not held); SS7 NP-complete
even with costs in {−1, 0, 1} [Abdel-Wahab 1976], polynomial on series-parallel
orders [Abdel-Wahab & Kameda 1978]; chordal completion open in 1979, NP-complete
in the Update [Yannakakis 1981]. **References to add** are proposed in §6
(fourteen entries, none in `paper1/latex/refs.bib`); **papers not held** are
appended to `literature/MISSING.md`.

## 1. Method

The problem list is pp. 187–288 (sheet `i` of the PDF holds pages `2i − 12`
and `2i − 11`; Appendix A opens on sheet 99, the GT category runs on sheets
101–109, the subject index on sheets 169–175 and the Update on sheet 175). The
subject index was read first (every problem name in capitals with its page),
then the GT category entry by entry, then every entry elsewhere whose title or
index line suggested an ordering, a layout, a matrix permutation, a completion,
a register or a pebble, then A13 and the Update. The bibliography (pp. 291–325,
sheets 151–168) was read for the entries cited by the relevant problems (sheets
151, 152, 155–157 rendered; the rest through the OCR text, each quoted entry
checked against its sheet when the OCR was doubtful).

Each relation in §2 is classified as G&J's comment (**GJ**), a cited paper
(**lit**), a Lean theorem of this repository (**Lean**), or a brute-force check
of ours (**bf**, with the script). Pathwidth is the exact subset DP of
`fixed_parameter_algorithm/pathwidth.py` throughout.

## 2. The table

Status: **member** (exact or sandwich; none found), **relative** (a proved
inequality in one direction with an unbounded gap), **contains** (the complex
is a special case), **unrelated** (no layout, width or ordering quantity; the
instance is a subgraph, a colouring, a matching, a flow, …).

### 2.1 Graph theory (A1, pp. 190–205), every entry

| code | name | p. | instance / question (as G&J state it) | relation to pathwidth, source | status |
|---|---|---|---|---|---|
| GT1 | Vertex cover | 190 | `|V'| ≤ K` covering every edge | none; (`pw ≤ n − α` is the independence bound, `IndependenceBound.lean`, but the cover is not an ordering) | unrelated |
| GT2 | Dominating set | 190 | dominating `V'`, `|V'| ≤ K` | none | unrelated |
| GT3 | Domatic number | 190 | partition into `≥ K` dominating sets | none | unrelated |
| GT4 | Graph K-colorability | 191 | proper `K`-colouring | none | unrelated |
| GT5 | Achromatic number | 191 | complete colouring with `≥ K` classes | none | unrelated |
| GT6 | Monochromatic triangle | 191 | 2-edge-colouring without monochromatic triangle | none | unrelated |
| GT7 | Feedback vertex set | 191 | `≤ K` vertices meeting every directed cycle | none | unrelated |
| GT8 | Feedback arc set | 192 | `≤ K` arcs meeting every directed cycle | none | unrelated |
| GT9 | Partial feedback edge set | 192 | `≤ K` edges meeting every cycle of length `≤ L` | none | unrelated |
| GT10 | Minimum maximal matching | 192 | maximal matching of size `≤ K` | none | unrelated |
| GT11 | Partition into triangles | 192 | `V` into triangles | none | unrelated |
| GT12 | Partition into isomorphic subgraphs | 193 | `V` into copies of `H` | none | unrelated |
| GT13 | Partition into Hamiltonian subgraphs | 193 | `V` into Hamiltonian parts | none | unrelated |
| GT14 | Partition into forests | 193 | vertex arboricity `≤ K` | none (`arboricity ≤ degeneracy ≤ pw` holds but is not the question) | unrelated |
| GT15 | Partition into cliques | 193 | clique cover number `≤ K` | none | unrelated |
| GT16 | Partition into perfect matchings | 194 | `≤ K` induced perfect matchings | none | unrelated |
| GT17 | Covering by cliques | 194 | edge clique cover `≤ K` | none; (every MOSP instance *is* an edge clique cover of its MOSP graph, `MOSPGraph.lean`, but the count of cliques is not the stack count) | unrelated |
| GT18 | Covering by complete bipartite subgraphs | 194 | bicliques covering `E` | none | unrelated |
| GT19 | Clique | 194 | `ω ≥ K` | `ω − 1 ≤ pw` is the clique bound (`_lower_bound`), unbounded gap on trees | relative (lower bound only) |
| GT20 | Independent set | 194 | `α ≥ K` | `pw ≤ n − α` (`IndependenceBound.lean`); the gap is unbounded (`K_{1,k}`: `n − α = 1 = pw`; `C_{2k}`: `n − α = k`, `pw = 2`) | relative (upper bound only) |
| GT21 | Induced subgraph with property Π | 195 | hereditary Π, `|V'| ≥ K` | none | unrelated |
| GT22 | Induced connected subgraph with property Π | 195 | as GT21, connected | none | unrelated |
| GT23 | Induced path | 196 | induced path on `≥ K` vertices | none | unrelated |
| GT24 | Balanced complete bipartite subgraph | 196 | `K_{K,K}` subgraph | none | unrelated |
| GT25 | Bipartite subgraph | 196 | `≥ K` edges bipartite | none | unrelated |
| GT26 | Degree-bounded connected subgraph | 196 | connected, degree `≤ d`, `≥ K` edges | none | unrelated |
| GT27 | Planar subgraph | 197 | planar, `≥ K` edges | none | unrelated |
| GT28 | Edge-subgraph | 197 | line-graph subgraph, `≥ K` edges | none | unrelated |
| GT29 | Transitive subgraph | 197 | transitive, `≥ K` arcs | none | unrelated |
| GT30 | Uniconnected subgraph | 197 | at most one path per pair | none | unrelated |
| GT31 | Minimum K-connected subgraph | 198 | `K`-connected, `≤ B` edges | none | unrelated |
| GT32 | Cubic subgraph | 198 | nonempty 3-regular subgraph | none | unrelated |
| GT33 | Minimum equivalent digraph | 198 | same reachability, `≤ K` arcs | none | unrelated |
| GT34 | Hamiltonian completion | 198 | `≤ K` edges added to make `G` Hamiltonian | none; a completion, not an interval or chordal one | unrelated |
| **GT35** | **Interval graph completion** | 198 | superset `E' ⊇ E`, `|E' − E| ≤ K`, `G'` interval | **`min |E' − E| = profile(G) − |E|`** (proof §3.3; **bf** `interval_profile.py`, every graph to 6 vertices, two independent evaluations at ≤ 5); profile is a sum: `C_n` needs `n − 3` at `pw 2`, `K_n` needs 0 at `pw n − 1`. The clique-size version, interval thickness `= pw + 1` (row 5), is **not** in G&J | relative (sum; unbounded both ways) |
| GT36 | Path graph completion | 199 | `≤ K` edges added to make `G` an intersection graph of paths in a tree | sum objective; tree analogue of GT35 (Gavril 1977b); unbounded by disjoint unions | relative (sum) |
| GT37 | Hamiltonian circuit | 199 | — | none | unrelated |
| GT38 | Directed Hamiltonian circuit | 199 | — | none | unrelated |
| GT39 | Hamiltonian path | 199 | — | none | unrelated |
| **GT40** | **Bandwidth** | 200 | bijection `f : V → [n]`, `|f(u) − f(v)| ≤ K` on edges | `pw ≤ bw` (**Lean** `pathwidth_le_bandwidth`); **bf** `layout_gaps.py`: 0 violations on 207 graphs to 6 vertices; gap unbounded, `bw(K_{1,k}) = ⌈k/2⌉` at `pw 1`, smallest gap `K_{1,3}` (`bw 2`, `pw 1`) | relative (lower bound only) |
| GT41 | Directed bandwidth | 200 | as GT40 with `f(u) < f(v)` on arcs | `pw(underlying) ≤ bw ≤ dbw`; out-star `K_{1,k}` directed from the centre has `dbw = k` (the centre precedes every leaf) at `pw 1` (**bf**, same script) | relative |
| **GT42** | **Optimal linear arrangement** (MinLA) | 200 | `Σ_{edges} |f(u) − f(v)| ≤ K` | sum; `MinLA ≤ n·cw ≤ nΔ·pw` (DPS 2002 Lemma 2.4, `complex_lb_layout.md`); no bound below by `pw`; **bf**: `MinLA(K_{1,k})` quadratic at `pw 1` | relative (sum) |
| GT43 | Directed optimal linear arrangement | 200 | as GT42 on a digraph, `f(u) < f(v)` on arcs | sum; as GT42 | relative (sum) |
| **GT44** | **Minimum cut linear arrangement** (cutwidth) | 201 | `|{{u,v} ∈ E : f(u) ≤ i < f(v)}| ≤ K` for all `i` | `pw ≤ cw ≤ Δ·pw` (**Lean** `pathwidth_le_cutwidth`, `cutwidth_unbounded`, row 11; upper half Bodlaender 1998 Thm 47); **bf**: 0 violations to 6 vertices, smallest gap `K_{1,3}`; Megiddo et al. 1988 §5: edge search `≤ cw`, equal on degree-3 graphs, star separates | relative (lower bound only; `= pw` within `Δ`) |
| GT45 | Rooted tree arrangement | 201 | rooted tree `T` on `V` with both ends of every edge on one root path (an elimination tree), `Σ_{edges} d_T(f(u), f(v)) ≤ K` | sum objective over an elimination tree (the tree-depth family's sum form: the min–max sibling is `≤ td − 1`); unbounded by disjoint unions | relative (sum) |
| **GT46** | **Directed elimination ordering** | 201 | elimination ordering of a digraph with fill-in `≤ K` | fill-in is a sum; G&J: the undirected case is OPEN4; the clique-size sibling is treewidth, `tw ≤ pw` (**Lean** `treewidth_le_pathwidth`), unbounded gap | relative (sum; treewidth family) |
| **GT47** | **Elimination degree sequence** | 201 | ordering with *exactly* `d_i` later neighbours at position `i` | the min–max relaxation `min_f max_v d_f(v)` **equals the degeneracy** (**bf** `gt47_degeneracy.py`, all 1,251 graphs on 2–7 vertices, 0 mismatches; the reverse of a smallest-last order attains it); `degeneracy ≤ pw` (**Lean** `degeneracy_le_pathwidth`), unbounded gap on trees; smallest gap at 5 vertices (`K_{2,3}` plus one edge on the 3-side: degeneracy 2, `pw 3`) | relative (lower bound only) |
| GT48 | Subgraph isomorphism | 202 | — | none | unrelated |
| GT49 | Largest common subgraph | 202 | — | none | unrelated |
| GT50 | Maximum subgraph matching | 202 | — | none | unrelated |
| GT51 | Graph contractability | 202 | `G` contracts to `H` | none as a problem (contraction minors are our family M, but the question here is a fixed `H`) | unrelated |
| GT52 | Graph homomorphism | 202 | — | none | unrelated |
| GT53 | Digraph D-morphism | 203 | — | none | unrelated |
| GT54 | Path with forbidden pairs | 203 | — | none | unrelated |
| GT55 | Multiple choice matching | 203 | — | none | unrelated |
| GT56 | Graph Grundy numbering | 203 | — | none | unrelated |
| GT57 | Kernel | 204 | — | none | unrelated |
| GT58 | K-closure | 204 | — | none | unrelated |
| GT59 | Intersection graph basis | 204 | intersection graph of sets over a `K`-set | none (an edge clique cover count, as GT17) | unrelated |
| GT60 | Path distinguishers | 204 | — | none | unrelated |
| GT61 | Metric dimension | 204 | — | none | unrelated |
| GT62 | Nesetril–Rödl dimension | 205 | — | none | unrelated |
| GT63 | Threshold number | 205 | `E` into `≤ K` threshold graphs | none | unrelated |
| GT64 | Oriented diameter | 205 | — | none | unrelated |
| GT65 | Weighted diameter | 205 | — | none | unrelated |

### 2.2 The other categories, the entries read in full

| code | name | p. | instance / question | relation to pathwidth, source | status |
|---|---|---|---|---|---|
| ND14 | Graph partitioning | 209 | `V` into weight-bounded parts, crossing edge length `≤ J` | edge cut; none | unrelated |
| ND17 | Minimum cut into bounded sets | 210 | `s`–`t` bisection with `|V_i| ≤ B`, edge cut `≤ K` | the vertex bisection `VB ≤ vs` is Harper's level `⌊n/2⌋` (`EmptyPair.lean`); the edge version is unbounded on stars (`⌈k/2⌉` at `pw 1`) | relative (edge form) |
| ND47 | Edge embedding on a grid | 218 | vertices on an `M × N` grid, adjacent vertices on a common line | a geometric layout, no width | unrelated |
| SR2 | Dynamic storage allocation | 226 | items with arrival, departure and size; storage `D` | the intervals are **given**; with unit sizes it is interval-graph colouring (G&J: polynomial, Gavril 1972) — the fixed-sequence case of MOSP, where the stack count is the clique number of the interval graph; the hardness is in the sizes | unrelated (fixed order) |
| SR5 | Rooted tree storage assignment | 227 | supersets `X_i' ⊇ X_i` forming directed paths of a rooted tree, `Σ|X_i' − X_i| ≤ K` | the tree analogue of SR16 (Gavril 1977a, from GT45); sum | relative (sum) |
| SR13 | Sparse matrix compression | 229 | rows stored with offsets into `m + K` cells | none | unrelated |
| SR14 | Consecutive ones submatrix | 229 | `K` columns with the consecutive-ones property | a deletion problem; G&J: `K = n` is C1P recognition (Fulkerson & Gross 1965; Tucker 1971; Booth & Lueker 1976) | unrelated |
| SR15 | Consecutive ones matrix partition | 229 | rows into two C1P matrices | none | unrelated |
| **SR16** | **Consecutive ones matrix augmentation** | 229 | change `≤ K` zeros to ones so that `A'` has C1P | with rows = customers and columns = products, `SR16(M) = min_π Σ_c span_c(π) − |M|`: the **sum** of the stack lifetimes, where MOSP is their **maximum** per column; on the edge–vertex incidence matrix it is `MinLA − |E|`, which is G&J's transformation from GT42 (**bf** `layout_gaps.py`, 92 graphs, 0 mismatches); `Z ≤ Σ span ≤ m·Z`, so unbounded by disjoint unions | relative (the sum form of MOSP) |
| SR17 | Consecutive block minimization | 230 | column permutation with `≤ K` blocks of ones | none (G&J: `K = ` number of nonzero rows is C1P recognition) | unrelated |
| SR18 | Consecutive sets | 230 | a string of length `≤ K` in which every `Σ_i` is a block | a superstring with repeats; none | unrelated |
| SR19 | 2-dimensional consecutive sets | 230 | — | none | unrelated |
| **SS7** | **Sequencing to minimize maximum cumulative cost** | 238 | poset on `T`, `c(t) ∈ Z`; a linear extension with every prefix sum `≤ K` | **contains MOSP** (encoding and **bf** `ss7_mosp.py`: 300 instances, SS7 = brute-force MOSP = `pw(MOSP graph) + 1`) **and PO1** (Abdel-Wahab's encoding, 1,099 dags, 0 mismatches); G&J: NP-complete even with `c(t) ∈ {−1, 0, 1}`, polynomial on series-parallel orders | contains |
| **PO1** | **Register sufficiency** | 272 | dag, ordering `v_1..v_n` and sets `S_0..S_n`, `|S_i| ≤ K`, `S_i − {v_i} ⊆ S_{i−1}`, operands of `v_i` in `S_{i−1}`, outputs in `S_n` | one-shot black pebbling with outputs retained; `pb(D) ≥ pbw(D) = pw(G_u) + 1` (**Lean** `pbw_eq_pathwidth_lengauerU_add_one`, `BlackPebblesWithin.pebblesWithin`); **bf** `register_sufficiency.py`: never below, strict from 5 vertices, gap 2 at 7–8; retention adds an unbounded term on multi-output dags; `pb(D) = 1 + min` over topological layouts of the pre-placement boundary (**bf** `pb_topological.py`, 33,867 dags) | relative (lower bound exact; gap open) |
| PO2 | Feasible register assignment | 272 | PO1 with a given register assignment | a constrained PO1 | unrelated |
| PO3 | Register sufficiency for loops | 272 | loop variables with cyclic lifetimes in `K` registers | circular-arc colouring with fixed arcs; polynomial for fixed `K` | unrelated (fixed order) |
| PO4 | Code generation on a one-register machine | 272 | — | none | unrelated |
| PO5 | Code generation with unlimited registers | 273 | — | none | unrelated |
| PO6 | Code generation for parallel assignments | 273 | ordering of variables with `≤ K` "needs a temporary" | a feedback-vertex count under an ordering; none | unrelated |
| OPEN4 | Chordal graph completion | 286 | `≤ K` edges added to make `G` chordal | fill-in (sum); G&J: equivalent to undirected GT46, Gaussian elimination on symmetric matrices (Rose, Tarjan & Lueker 1976); Update: NP-complete [Yannakakis 1981]; the clique-size sibling is treewidth | relative (sum; treewidth family) |

The remaining entries of A2–A5, A8, A11, A12 and A13 were read in full on their
sheets (titles and instances) and none has an ordering or width objective:
spanning trees, Steiner trees, routing, flows, sets and partitions, strings,
databases, scheduling with deadlines and machines, games (PSPACE), program
schemes, Petri nets, voting power, matrices with fixed row and column order,
fault detection, and the open problems other than OPEN4.

## 3. The two entries that contain the complex, and the three relatives checked

### 3.1 SS7, the common generalisation

**Instance** (p. 238): tasks `T`, partial order `≺`, cost `c(t) ∈ Z`, bound
`K`. **Question**: a one-processor schedule (a linear extension) such that
for every task `t`, the sum of costs of tasks scheduled at or before `t` is at
most `K`. Reference [Abdel-Wahab 1976], transformation from REGISTER
SUFFICIENCY; comment: NP-complete even for `c(t) ∈ {−1, 0, 1}`, polynomial when
`≺` is series-parallel [Abdel-Wahab & Kameda 1978; Monma & Sidney 1977].

**MOSP is the special case** of height-3 posets with the costs paired. Given
`M` (customers `c`, products `p`), take tasks `open(c)` with cost +1,
`close(c)` with cost −1, `p` with cost 0, and `open(c) ≺ p ≺ close(c)` for
every `p ∈ P_c`. In any linear extension the prefix sum after a product `p` is
`#{c : open(c) placed} − #{c : close(c) placed}`; moving every `open` as late
and every `close` as early as the order allows never raises a prefix sum, and
then the sum at `p` is the number of customers with a product at or before `p`
and one after — the open stacks of the product order. Conversely a product
order gives such an extension. So `SS7(encoding) = Z(M) = pw(G_M) + 1`.
Checked: `ss7_mosp.py`, 300 random instances with `n ≤ 5`, `m ≤ 6`, the SS7
optimum by a DP over order ideals against a brute force over all product
orders and against the exact pathwidth of the MOSP graph plus one, 0
mismatches.

**PO1 is the special case** G&J's reference uses: tasks `compute(v)` (+1) and
`free(v)` (−1), `compute(u) ≺ compute(v)` and `compute(v) ≺ free(u)` for each
arc `u → v` (`u` an operand of `v`), `compute(v) ≺ free(v)`. Checked on every
labelled dag with ≤ 5 vertices against the game DP, 0 mismatches.

**What a membership proof would need.** A derived graph `H(T, ≺, c)` with
`SS7 = pw(H) + const`. Two small facts bound the candidates. (i) The poset
`a ≺ b` with `c(a) = +1`, `c(b) = −1` has optimum 1, and the same poset with
`c(a) = −1`, `c(b) = +1` has optimum 0: the comparability graph and the cost
multiset do not determine the value, so `H` must read the orientation of
`≺` against the signs. (ii) A chain of `k` tasks all of cost +1 has optimum
`k` with nothing to close: `H` would have to carry the whole precedence chain
as a clique, and in general the +1 tasks that are forced to be simultaneously
live in *every* extension form the natural candidate graph — a membership
claim is the statement that this graph's pathwidth, plus one, is the optimum,
and we have neither proved nor refuted it. The two exact special cases
(MOSP, where the forced-live graph is the MOSP graph; PO1, where it contains
`G_u` and the data of §3.2 show the optimum above `pw(G_u) + 1`) say the
candidate cannot be exact for PO1's encoding, so a derived graph for all of
SS7 would have to be a different one. We do not pursue it: the cases the
paper cares about are already exact members, and SS7 is recorded as the
1979 list's common generalisation of MOSP and register sufficiency.

### 3.2 PO1, register sufficiency against Lengauer's `G_u`

**Instance** (p. 272): a dag `G = (V, A)` and `K`. In G&J's orientation an arc
`(v, u)` means `u` is an operand of `v`; the question asks for an ordering
`v_1, …, v_n` and register contents `S_0 = ∅, S_1, …, S_n`, `|S_i| ≤ K`, with
`S_i − {v_i} ⊆ S_{i−1}`, every operand of `v_i` in `S_{i−1}`, and every
output (in-degree 0) in `S_n`. Each vertex is computed once; a register is
freed at will; the outputs are kept. Reference [Sethi 1975]; NP-complete even
with out-degree ≤ 2; the variant with recomputation is NP-hard and "not known
to be in NP" (p. 272; Gilbert, Lengauer & Tarjan 1980 later proved it
PSPACE-complete).

This is the progressive **black** pebble game of Kirousis & Papadimitriou
(1986) with outputs retained. Row 13 of our table proves the **black-white**
progressive demand `pbw(D) = pw(G_u) + 1` for every digraph (`PebblingGu.lean`,
Lengauer 1981 Thm 2; `G_u` joins two vertices iff an arc joins them or they
share an immediate successor). Since a black play is a black-white play
(`BlackPebblesWithin.pebblesWithin`), **`pb(D) ≥ pw(G_u) + 1`** is a theorem.
It is not an equality:

| `n` | dags | `max (pb − pbw)` | smallest witness (operand → consumer) |
|---|---|---|---|
| 2–4 | all 74 | 0 | — |
| 5 | all 1,024 | 1 | `0→1, 0→2, 1→4, 2→3`: `pb = 3`, `pbw = 2` (`G_u` is the path `4–1–0–2–3`) |
| 6 | all 32,768 | 1 | the same |
| 7 | 3,000 random | 2 | `0→2, 0→5, 1→3, 1→6, 2→4, 2→5, 3→4, 3→6, 4→5, 5→6`: `pb = 6`, `pbw = 4` |
| 8 | 1,000 random | 2 | a 12-arc dag: `pb = 7`, `pbw = 5` |

(`register_sufficiency.py`; `pb < pbw` never occurred, as the theorem says.)
On the 5-vertex witness two white pebbles suffice — white on 1 and 4, turn
and clear 4, blacken 0, turn and clear 1, white on 2, turn, clear 0, black on
3 — while black needs 3, because 0 must stay until both 1 and 2 are placed
and whichever of them is placed first must stay until its own successor is.
The retention of outputs adds a further term that is unbounded on its own
(`k` sinks with one common source: `pb_GJ = k + 1`, `pbw = 2`), so the
single-output case is the one to compare; its gap equals the unretained gap in
every row above.

**What the black game is.** `pb(D) = 1 + min_σ max_i |{j < i : v_j has a
successor among v_i, …, v_n}|` over **topological** orderings `σ` — the
left vertex separation of the underlying graph taken just before each
placement, with the layout constrained to respect the arcs (`pb_topological.py`,
all 33,867 labelled dags to 6 vertices, 0 mismatches; a first draft that took
the boundary after the placement failed on a single arc). White pebbles remove
the constraint and add the common-successor edges, which is the content of
Lengauer's theorem. So PO1 is "pathwidth with a precedence constraint on the
layout", a quantity that sits above `pw(G_u) + 1` and above `pw(U(D)) + 1`;
a membership proof would need a derived graph whose pathwidth encodes the
constraint, and the data say the gap to `G_u` grows with `n`. Whether
`pb(D) ≤ f(pw(G_u))` for some function `f` is open here. The minimum of `pb`
over the acyclic orientations of a graph is exactly `pw + 1` (Kirousis &
Papadimitriou Thm 3.1, row 13), so the complex sees PO1 through its best
orientation and not through a given dag.

### 3.3 GT35 is the profile

For an ordering `f` let `last_f(v) = max_{u ∈ N[v]} f(u)`. The graph `G'_f`
with `uv ∈ E'` iff `f(u) < f(v) ≤ last_f(u)` is an interval graph (intervals
`[f(u), last_f(u)]`; `u` and `v` with `f(u) < f(v)` meet iff
`f(v) ≤ last_f(u)`), contains `E`, and has `|E'| = Σ_v (last_f(v) − f(v))`.
Conversely an interval supergraph ordered by left endpoints satisfies
`uv ∈ E'` whenever `f(u) < f(v) ≤ last_f(u)` (the interval of `u` reaches the
left end of its last neighbour and so covers every left end between), so
`G'_f ⊆` that supergraph. Hence `min_{G' interval} |E' − E| = min_f Σ_v
(last_f(v) − f(v)) − |E| = profile(G) − |E|`. We recall the identity from the
profile literature (Billionnet 1986; Lin & Yuan 1994, the latter recorded in
`literature/MISSING.md`); neither is held, so the attribution should be
checked before it is cited, and the brute-force check stands on its own:
`interval_profile.py` evaluates the formula on every atlas graph to 6 vertices
and, on every graph to 5 vertices, enumerates every supergraph and tests
intervality with Olariu's ordering characterisation (`u < v < w`, `uw ∈ E`
⇒ `uv ∈ E`), 0 mismatches. Against pathwidth: `C_n` needs `n − 3` edges (the
fan) at `pw = 2`, `K_n` needs 0 at `pw = n − 1`; the largest excess
`completion − pw` at 6 vertices is 1 (`C_6`: 3 against 2).

So the brief's question — is GT35 interval thickness under another name — has
the answer **no**: G&J's objective is the number of added edges, which is the
profile; the number of tracks (the clique number of the interval supergraph,
Kashiwabara & Fujisawa 1979) is `pw + 1` and is not in the 1979 list.

### 3.4 GT47 relaxes to the degeneracy

GT47 asks for an ordering whose forward degrees are *exactly* a given
sequence. The natural min–max relaxation, `min_f max_v d_f(v)` with
`d_f(v) = |{u ∈ N(v) : f(u) > f(v)}|`, equals the degeneracy on all 1,251
atlas graphs with 2–7 vertices (`gt47_degeneracy.py`); the proof is the usual
one (the reverse of a smallest-last ordering gives `≤ δ*`, and in any ordering
the first vertex of the `δ*`-core has `≥ δ*` later neighbours). It is
polynomial, below pathwidth (`degeneracy_le_pathwidth`), and the gap is
unbounded on trees (degeneracy 1, pathwidth `Θ(log n)`); the smallest graph
with `pw > degeneracy` has 5 vertices, `K_{2,3}` plus an edge on the 3-side
(degeneracy 2, `pw 3`), and the gap at ≤ 7 vertices is at most 1.

### 3.5 SR16 is the sum form of MOSP, and MinLA on incidence matrices

With rows as customers and columns as products, turning zeros into ones so
that every row is consecutive under a column permutation `π` costs
`Σ_c (span_c(π) − |P_c|)`; the minimum over `π` is the minimum total stack
lifetime minus the number of ones, where MOSP is the maximum over columns of
the same lifetimes. On the edge–vertex incidence matrix (rows = edges, columns
= vertices) a row's span is `|f(u) − f(v)| + 1`, so `SR16 = MinLA − |E|`:
G&J's own transformation from GT42 (p. 229, [Booth 1975], [Papadimitriou
1976a]), checked on 92 atlas graphs with 1–6 edges. The sum and the maximum
are a factor `m` apart at most (`Z ≤ Σ_c span_c ≤ m·Z`) and a disjoint union
of `k` edges separates them by `k − 1` at `pw 1`.

## 4. What G&J say about the complexity, with their references

For the paper's related work; every entry read on its sheet, the bibliography
entries on theirs or in the OCR text and checked.

| problem | status in 1979 | reference as G&J cite it | later |
|---|---|---|---|
| GT40 Bandwidth | NP-complete; trees of maximum degree 3; "corresponds to minimizing the bandwidth of a symmetric matrix by simultaneous row and column permutations" | Papadimitriou (1976a), *Computing* 16, 263–270; Garey, Graham, Johnson & Knuth (1978), *SIAM J. Appl. Math.* 34, 477–495 | caterpillars of hair length 3 (Monien 1986, not held) |
| GT41 Directed bandwidth | NP-complete for rooted directed trees of in-degree 1 and out-degree ≤ 2 | Garey, Graham, Johnson & Knuth (1978) | — |
| GT42 Optimal linear arrangement | NP-complete, also bipartite; polynomial on trees | Garey, Johnson & Stockmeyer (1976), *TCS* 1, 237–267; Even & Shiloach (1975), Technion Report 43; Shiloach (1976), Weizmann report; Gol'dberg & Klipker (1976), in Russian | — |
| GT43 Directed OLA | NP-complete; polynomial on trees even weighted | Even & Shiloach (1975); Adolphson & Hu (1973), *SIAM J. Appl. Math.* 25, 403–423 | — |
| GT44 Minimum cut linear arrangement | NP-complete, from SIMPLE MAX CUT | Stockmeyer (1974b), private communication; Gavril (1977a), *Proc. 11th Conf. Information Sciences and Systems*, Johns Hopkins, 91–95 | Megiddo et al. (1988) §5, cutwidth = search number on degree-3 graphs; trees `O(n log n)` (Yannakakis) |
| GT45 Rooted tree arrangement | NP-complete, from OLA | Gavril (1977a) | — |
| GT46 Directed elimination ordering | NP-complete; "arises in performing Gaussian elimination on sparse matrices"; the undirected case "is equivalent to CHORDAL GRAPH COMPLETION and is open" | Rose & Tarjan (1978), *SIAM J. Appl. Math.* 34, 176–197 | OPEN4 closed by Yannakakis (1981) |
| GT47 Elimination degree sequence | NP-complete, from X3C; the "exactly `d_i` neighbours" (not later neighbours) variant trivial | Garey, Johnson & Papadimitriou (1977), unpublished | — |
| GT35 Interval graph completion | NP-complete, from OLA; remains so on line graphs ("edge graphs"); polynomial for `K = 0` | Garey, Gavril & Johnson (1977), unpublished; Fulkerson & Gross (1965), *Pacific J. Math.* 15, 835–855; Booth & Lueker (1976), *JCSS* 13, 335–379 | the published proof of the NP-completeness of interval completion / profile is usually attributed to Garey & Johnson via this entry; Lin & Yuan 1994 |
| GT36 Path graph completion | NP-complete from GT35; also for directed paths in a rooted tree | Gavril (1977b), private communication | — |
| OPEN4 Chordal graph completion | open; = undirected GT46; Gaussian elimination fill-in on symmetric matrices | Rose, Tarjan & Lueker (1976), *SIAM J. Comput.* 5, 266–283; Gavril (1974b), *JCTB* 16, 47–56 | Update (p. 339): NP-complete [Yannakakis 1981] |
| SR16 Consecutive ones matrix augmentation | NP-complete, from OLA; the circular-ones variant too | Booth (1975), PhD thesis, UC Berkeley, *PQ-tree algorithms*; Papadimitriou (1976a) | — |
| SR14/SR17 (C1P recognition at the boundary) | polynomial | Fulkerson & Gross (1965); Tucker (1971); Booth & Lueker (1976) | — |
| SR2 Dynamic storage allocation | strongly NP-complete even with sizes in {1, 2}; polynomial with equal sizes "by interval graph coloring algorithms" | Stockmeyer (1976b), private communication; Gavril (1972), *SIAM J. Comput.* 1, 180–187 | — |
| SS7 Max cumulative cost | NP-complete even with `c(t) ∈ {−1, 0, 1}`, from REGISTER SUFFICIENCY; polynomial on series-parallel orders | Abdel-Wahab (1976), PhD thesis, Waterloo, *Scheduling with applications to register allocation and deadlock problems*; Abdel-Wahab & Kameda (1978), *Oper. Res.* 26, 141–158; Monma & Sidney (1977) | — |
| PO1 Register sufficiency | NP-complete even with out-degree ≤ 2; with recomputation NP-hard, not known in NP | Sethi (1975), *SIAM J. Comput.* 4, 226–248 | recomputation PSPACE-complete, Gilbert, Lengauer & Tarjan (1980) |
| PO3 Register sufficiency for loops | NP-complete; polynomial for fixed `K` | Garey, Johnson, Miller & Papadimitriou (1978), unpublished | circular-arc colouring |
| searching, pebbling (general), interval thickness, gate matrix layout, vertex separation | **absent from the 1979 list** | — | Megiddo et al. (1988, held), Kashiwabara & Fujisawa (1979), Lengauer (1981, held), Kirousis & Papadimitriou (1985, 1986, held) |

The Update (p. 339) says that of the thirteen open problems six were resolved
and refers the reader to Johnson's "NP-completeness column: an ongoing guide"
(*J. Algorithms*, from 1981); nothing in it concerns a layout problem except
chordal completion.

## 5. The open problems (A13) and the "problems in the gap"

OPEN1 graph isomorphism, OPEN2 subgraph homeomorphism for a fixed `H`, OPEN3
graph genus, **OPEN4 chordal graph completion**, OPEN5 chromatic index, OPEN6
spanning tree parity, OPEN7 partial order dimension, OPEN8 precedence
constrained 3-processor scheduling, OPEN9 linear programming, OPEN10 total
unimodularity, OPEN11 composite number, OPEN12 minimum length triangulation
(pp. 285–288). Only OPEN4 touches the complex, and as a sum objective of the
treewidth family (§2.2). None of the twelve is a layout or width problem, so
the 1979 "gap" list offers nothing to the paper beyond the citation for
fill-in.

## 6. References to add to `paper1/latex/refs.bib` (proposed, not applied)

`GareyJohnson1979` is already there. None of the following is:

```bibtex
@article{Papadimitriou1976Bandwidth,
  author  = {Papadimitriou, Christos H.},
  title   = {The {NP}-completeness of the bandwidth minimization problem},
  journal = {Computing},
  volume  = {16},
  pages   = {263--270},
  year    = {1976}
}
@article{GareyGrahamJohnsonKnuth1978,
  author  = {Garey, Michael R. and Graham, Ronald L. and Johnson, David S. and Knuth, Donald E.},
  title   = {Complexity results for bandwidth minimization},
  journal = {SIAM Journal on Applied Mathematics},
  volume  = {34},
  number  = {3},
  pages   = {477--495},
  year    = {1978}
}
@article{GareyJohnsonStockmeyer1976,
  author  = {Garey, Michael R. and Johnson, David S. and Stockmeyer, Larry},
  title   = {Some simplified {NP}-complete graph problems},
  journal = {Theoretical Computer Science},
  volume  = {1},
  number  = {3},
  pages   = {237--267},
  year    = {1976}
}
@inproceedings{Gavril1977,
  author    = {Gavril, F{\u{a}}nic{\u{a}}},
  title     = {Some {NP}-complete problems on graphs},
  booktitle = {Proceedings of the 11th Conference on Information Sciences and Systems},
  address   = {Johns Hopkins University, Baltimore},
  pages     = {91--95},
  year      = {1977}
}
@article{Sethi1975,
  author  = {Sethi, Ravi},
  title   = {Complete register allocation problems},
  journal = {SIAM Journal on Computing},
  volume  = {4},
  number  = {3},
  pages   = {226--248},
  year    = {1975}
}
@phdthesis{AbdelWahab1976,
  author = {Abdel-Wahab, Hussein M.},
  title  = {Scheduling with Applications to Register Allocation and Deadlock Problems},
  school = {Department of Electrical Engineering, University of Waterloo},
  year   = {1976}
}
@article{AbdelWahabKameda1978,
  author  = {Abdel-Wahab, Hussein M. and Kameda, Tiko},
  title   = {Scheduling to minimize maximum cumulative cost subject to series-parallel precedence constraints},
  journal = {Operations Research},
  volume  = {26},
  number  = {1},
  pages   = {141--158},
  year    = {1978}
}
@article{RoseTarjan1978,
  author  = {Rose, Donald J. and Tarjan, Robert E.},
  title   = {Algorithmic aspects of vertex elimination on directed graphs},
  journal = {SIAM Journal on Applied Mathematics},
  volume  = {34},
  number  = {1},
  pages   = {176--197},
  year    = {1978}
}
@article{RoseTarjanLueker1976,
  author  = {Rose, Donald J. and Tarjan, Robert E. and Lueker, George S.},
  title   = {Algorithmic aspects of vertex elimination on graphs},
  journal = {SIAM Journal on Computing},
  volume  = {5},
  number  = {2},
  pages   = {266--283},
  year    = {1976}
}
@article{Yannakakis1981,
  author  = {Yannakakis, Mihalis},
  title   = {Computing the minimum fill-in is {NP}-complete},
  journal = {SIAM Journal on Algebraic and Discrete Methods},
  volume  = {2},
  number  = {1},
  pages   = {77--79},
  year    = {1981}
}
@article{BoothLueker1976,
  author  = {Booth, Kellogg S. and Lueker, George S.},
  title   = {Testing for the consecutive ones property, interval graphs, and graph planarity using {PQ}-tree algorithms},
  journal = {Journal of Computer and System Sciences},
  volume  = {13},
  number  = {3},
  pages   = {335--379},
  year    = {1976}
}
@article{FulkersonGross1965,
  author  = {Fulkerson, Delbert R. and Gross, Oliver A.},
  title   = {Incidence matrices and interval graphs},
  journal = {Pacific Journal of Mathematics},
  volume  = {15},
  number  = {3},
  pages   = {835--855},
  year    = {1965}
}
@article{GilbertLengauerTarjan1980,
  author  = {Gilbert, John R. and Lengauer, Thomas and Tarjan, Robert E.},
  title   = {The pebbling problem is complete in polynomial space},
  journal = {SIAM Journal on Computing},
  volume  = {9},
  number  = {3},
  pages   = {513--524},
  year    = {1980}
}
@article{MegiddoHakimiGareyJohnsonPapadimitriou1988,
  author  = {Megiddo, Nimrod and Hakimi, S. Louis and Garey, Michael R. and Johnson, David S. and Papadimitriou, Christos H.},
  title   = {The complexity of searching a graph},
  journal = {Journal of the ACM},
  volume  = {35},
  number  = {1},
  pages   = {18--44},
  year    = {1988}
}
```

The volume and page numbers of the entries G&J cite were taken from G&J's
bibliography (read on the sheets); the Yannakakis 1981 and Gilbert–Lengauer–
Tarjan 1980 data are from memory of the papers and are to be checked against
the papers before use (neither is held). Where a result is "unpublished" or a
"private communication" in G&J (GT35, GT44 Stockmeyer, GT47, PO3), the paper
should cite G&J itself with the problem code and page.

## 7. Sheets read, scripts, regenerate commands

**Sheets rendered and read** (PDF sheet = book pages `2i − 12`, `2i − 11`):
at 110 dpi, 169–175 (subject index pp. 326–338, Update p. 339); at 130 dpi,
99–100 (pp. 186–189, the appendix's introduction), 101–109 (pp. 190–207, all
of GT and ND1–ND8), 110–118 (pp. 208–225, ND9–ND51, SP1–SP21), 119–128
(pp. 226–245, SR1–SR36, SS1–SS22, MP1–MP3), 133–135 (pp. 254–259, GP1–GP15,
LO1–LO5), 142–150 (pp. 272–288, PO1–PO20, MS1–MS19, OPEN1–OPEN12), 151, 152,
155, 156, 157 (bibliography pp. 291–293, 298–303). Rendered and not read:
153–154 and 158–168 (bibliography and indexes; consulted through the OCR text
instead). Not rendered: 1–98 (the text) and 129–132, 136–141 (pp. 246–253 and
260–271: AN, LO6 onward, AL — no layout problem in the index).

```
mkdir -p /tmp/gj
pdftoppm -r 130 -f 99 -l 168 -png literature/1979-Garey-Johnson-Computers-and-Intractability-NP-Completeness.pdf /tmp/gj/s
pdftoppm -r 110 -f 165 -l 175 -png literature/1979-Garey-Johnson-Computers-and-Intractability-NP-Completeness.pdf /tmp/gj/sheet
```

**Scripts** (`reports/scratch/garey_johnson/`, each with its log beside it;
run from the repository root; total about 2 core-minutes):

| script | checks | result |
|---|---|---|
| `register_sufficiency.py` | `pb`, `pb` with retained outputs, `pw(G_u) + 1`, `pw(U) + 1` on every labelled dag to 6 vertices and 4,000 random dags at 7–8 | `pb ≥ pbw` always; gaps 0, 0, 0, 1, 1, 2, 2 |
| `pb_topological.py` | `pb` = constrained vertex separation formula, all dags to 6 vertices | 0 mismatches on 33,867 |
| `ss7_mosp.py` | SS7 of the MOSP encoding = brute-force MOSP = `pw + 1`; SS7 of the PO1 encoding = `pb` | 0 mismatches (300 instances; 1,099 dags) |
| `interval_profile.py` | GT35 = profile − |E| (formula vs supergraph enumeration), gaps on `C_n`, `K_n` | 0 mismatches (52 and 208 graphs) |
| `gt47_degeneracy.py` | min–max forward degree = degeneracy; smallest `pw > degeneracy` | 0 mismatches (1,251 graphs); 5 vertices |
| `layout_gaps.py` | `pw ≤ bw`, `pw ≤ cw ≤ Δ·pw` to 6 vertices; stars; SR16 = MinLA − |E| on incidence matrices | 0 violations; 0 mismatches |

```
cd /home/al/dev/MOSP
for s in register_sufficiency pb_topological ss7_mosp interval_profile gt47_degeneracy layout_gaps; do
  python reports/scratch/garey_johnson/$s.py | tee reports/scratch/garey_johnson/$s.log
done
```
