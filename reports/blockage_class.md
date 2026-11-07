# A compact generating class of blockages: the first step, and its ceiling

*2026-11-07, one session. Code `learning/blockage_class.py` (11 tests in
`tests/test_blockage_class.py`), Lean `lean/MOSPFormalization/BlockageClass.lean`,
scratch `reports/scratch/blockage_class/`. Nothing under `solutions/` touched; no
instance re-solved; about 0.5 core-hours in all (the census 138 s on 8 workers, the
corpus stage 6 s on 8, the brute-force checks 71 s, the Lean build minutes).*

## §0. Summary

**The question.** Pathwidth's dual is the blockage of Bienstock, Robertson, Seymour
& Thomas (1991): a family of vertex sets, exponential in general. Every compact
lower bound on record (clique, contraction minor, Harper's prefix bound, nested
prefix chains, searched minors) is a restricted class of blockages with a measured
ceiling below the optimum on the gap instances. The owner asked for the first step
towards a richer compact class: candidates, a Lean proof that the chosen class's
members are blockages, and a brute-force measurement of its ceiling where the truth
is known. **Do not build a search.**

**The candidates** (§1). Three were weighed. (A) **Branch–minor frames**: every
blockage is an *avoidance family* — the sets it leaves out are upward closed, so a
blockage is `{X : |att X| ≤ n, ¬big X}` for an upward-closed `big` — and three
operators build such predicates from compact data: a clique of `n + 1` vertices
(`big X := K ⊆ X`); pullback along a minor model (`big X := big_H` of the branch sets
`X` meets); and the **linked branch lemma** of `Sandwich.lean` as a blockage operator
(three disjoint connected branches carrying frames of order `k`, every pair joined
by a connected connector that misses the third; `big X := at least two branch parts
big`; order `k + 1`). (B) **Connected frames with Menger**: connected generators,
pairwise `(n+1)`-inseparable, hitting number `≥ n + 1`. A blockage, but **dead by
argument**: in a tree decomposition two connected generators either share a bag or
are separated by one, so the hypotheses force `tw ≥ n` — the class can never certify
`pw > tw`, which is the whole target. (C) **BRST's partial blockages and fractures,
and the nested-prefix bands** of `reports/checkpoint_relaxation.md`: both are
statements about *all* small-step chains, as global as axiom (iii) itself; the family
a band refutation would generate is neither downward closed nor compact. Rejected as
classes. (A) was chosen; it contains every clique-minor certificate and the branch
lemma, and it is the pathwidth analogue of Bodlaender, Grigoriev & Koster's brambles
in the only sense available (a generating structure with a by-construction proof).

**The theorem** (§2). `BlockageClass.lean`, 745 lines, no `sorry`: blockages relative
to a vertex set (`attIn`, `ComplementaryIn`, `IsBlockageIn`; equal to `IsBlockage`
at `univ`), avoidance families (`avoid`), frames (`Frame`), the three operators
`Frame.clique` / `isBlockageIn_clique`, `Frame.minor` / `isBlockageIn_minor`
(`MinorModelIn`, `pull`), `Frame.branch` / `isBlockageIn_branch` (`BranchIn`,
`twoOf`, `exactly_one_of_full`), the cut-vertex form `BranchIn.of_hub`, and the
certificate theorem `Frame.pathwidth_ge : Frame G univ n → n ≤ pathwidth G` through
`pathwidth_ge_of_isBlockage`. `#print axioms` on all five named theorems:
`[propext, Classical.choice, Quot.sound]`. Every statement was checked by brute
force first: on all 208 graphs to 6 vertices the clique, minor and branch outputs
satisfy (i)–(iii) with 0 violations (4,240 linked triples), the *unlinked* control
fails on 3,486 of 4,706 triples (the linking hypothesis is load-bearing), and both
halves of the duality hold to 5 vertices.

**The ceiling** (§3). By minor monotonicity the class's best order on a graph is
`ceiling(G) = max(had(G) − 1, 1 + max{t : three pairwise disjoint, pairwise linked
connected induced subgraphs of ceiling ≥ t})`, `had` the Hadwiger number — computed
exactly by recursion over induced subgraphs with a nauty memo, and checked against an
independent enumeration over all minors on every graph to 7 vertices (1,252 graphs,
equal, never above `pw`).

| set | graphs | `ceiling = pw` | `ceiling = had − 1` | `ceiling = tw` | `ceiling > tw` | `< tw` |
|:--|--:|--:|--:|--:|--:|--:|
| every graph with `pw > tw`, ≤ 9 vertices (all have `pw = tw + 1`) | 13,937 | 47 | 13,882 | 13,881 | 47 | 1 |
| every graph with `pw − tw = 2`, 10–11 vertices | 1,038 | 0 | 1,026 | 1,026 | 12 | 0 |
| together | 14,975 | **47** | 14,916 | 14,915 | 59 | 1 |

The 47 tight graphs are the 15 trees (every tree in the set) and 32 other graphs
with three linked branches of order `pw − 1`; the 12 others where branching helps are 11-vertex
graphs with `tw = 2`, `pw = 4`, ceiling 3. On **14,915 of 14,975** the class's
ceiling is exactly the treewidth: the branch operator never fires, and a clique
minor is a treewidth certificate. The smallest graph it misses has six vertices, a
triangle with three *ears* (each ear a vertex adjacent to two triangle vertices,
graph6 `EElw`: `pw 3`, `tw 2`, no `K₄` minor, no room for three branches). The
four 10-vertex graphs with `pw − tw = 2` (§21's record) have ceiling 3 against
`pw 5`.

On the **197 corpus bound-gap instances at 20–40 customers** (every one with a
searched contraction minor tight at the optimum), with the ceiling bracketed
between the certificates the class's own operators find and a counting bound:

| verdict | instances | meaning |
|:--|--:|:--|
| tight (`ceiling = pw`) | **0** | — |
| dead (`ceiling ≤ pw − 1`, proved by counting) | **104** | 76 because three branches of pathwidth `≥ pw − 1` need `3 pw > n` vertices; 28 by the vertex-cover and edge counts |
| clique-minor only | 76 | the branch operator is excluded by counting; the class's value is `had − 1`, tight iff `G` has a `K_{pw+1}` minor (74 have `pw = tw`); whatever it is, **it adds nothing over clique minors** |
| branch open | 17 | `pw = tw + 1` (15) or `tw` (2) at `n ≥ 3 pw`: tight only if `G` packs three vertex-disjoint, pairwise linked `K_pw`-minor models; not decided (that is a packing search) |

The certificates actually found (ω, the clique numbers of the contraction-degeneracy
minors, the harness's separator branch recursion seeded by cliques, on the graph and
on its minors — all members of the class) sit **below the searched-minor value on 197
of 197**, below `max(lb_best, tw + 1)` on 182, and below the solver's own `lb_best`
on 77 (contraction degeneracy is not a clique bound and is not in the class). The
branch operator improved on the clique terms on **0 of 197**. Mean shortfall in
stacks: `pw − ceiling_lower 2.73`, `pw − ceiling_upper 0.57`, against 0.80 for the
reference and 1.86 for Harper's ceiling.

**Kill verdict — met.** The criterion was: dead if on the gap instances at ≤ 40
customers the ceiling never exceeds the searched-minor value. The searched minor is
tight on all 197, so the ceiling cannot exceed it anywhere; it is proved strictly
below on 104, shown equal on none, and on the remaining 93 the only routes left are
clique minors (76) or a packing of three clique minors (17). The class is **not
richer than minors on the gap instances**: its one ingredient beyond clique minors,
branching, needs three vertex-disjoint pieces of pathwidth `pw − 1`, and the gap
instances — dense enough to have `pw ≈ n / 3` or sparse with `pw = tw + 1` at 30–40
vertices — have no room for them. The census says the same at 6–11 vertices: the
obstruction to `pw > tw` on small graphs is almost never three branches.

**What the missed blockages look like** (§4). For the six-vertex ear graph, an
order-3 blockage is generated by three big sets `V ∖ {ear}`: it is a blockage
because every separator of ≤ 3 vertices leaves at most one non-trivial side. Such
*co-singleton frames* `{V ∖ {u} : u ∈ U}` are blockages whenever `|V| ≥ n + 3` and
every separator of size `≤ n` leaves the graph connected, or connected plus one
singleton of `U`, or exactly three singletons of `U` — a checkable condition of a
different kind (about small separators, not about disjoint pieces), but it certifies
only 1 of 1, 6 of 14, 37 of 352 and 11 of a 600-sample of the graphs the class
misses at 6, 7, 8, 9 vertices. The next class, if there is to be one, has to express
"every small separation has a trivial side" at several orders at once, which is what
the band of consecutive prefix sizes in `reports/checkpoint_relaxation.md` says in
layout vocabulary.

**What is checked and what is not.** Checked: the three operator statements by
enumeration to 6 vertices and in Lean; the ceiling formula against the minor-closure
enumeration to 7 vertices; every ceiling against the exact pathwidth (never above,
14,975 graphs); every corpus certificate against the certified optimum through the
harness's `evaluate_candidates` (never above, 197 instances; the harness's CLI stage
was not used because it appends to the committed values file). Not checked: that the
Python `linked` and the Lean `BranchIn` agree is a reading of two definitions (both
say: a connected `Q` inside `C`, missing the third branch, adjacent to both), not a
proof; the ceiling formula and the counting bounds are on paper (§3.1, §3.4); the
Hadwiger numbers that would settle the 93 undecided corpus instances were not
computed (a minor-containment search). Literature: we found no prior statement of a
blockage class used as a computed lower bound (`literature/MISSING.md`, three
entries); Groenland, Joret, Nadara & Walczak (2023) certify pathwidth by a subdivided
complete binary tree, the branching kind this class contains.

Regenerate every number:

```bash
python3 -m learning.blockage_class --stage check --max-n 6      # §2.3: 71 s; reports/scratch/blockage_class/checks.json
for n in 1 2 3 4 5 6 7 8 9; do nauty-geng -q $n | learning/_pwtw_exhaust --min-diff 1 --level 2 > reports/scratch/blockage_class/census_n$n.txt; done
nice -n 19 python3 -m learning.blockage_class --stage census --max-n 9 --workers 8   # §3.2: 138 s; census_ceiling.csv
nice -n 19 python3 -m learning.blockage_class --stage corpus --workers 8             # §3.3: 6 s; corpus_gap40.csv
python3 -m pytest tests/test_blockage_class.py -q                                    # 11 tests, 50 s
cd lean && taskset -c 16-23 lake build MOSPFormalization.BlockageClass              # §2: the five #print axioms lines
```

## §1. Candidates

### 1.1 The reformulation every candidate rests on: a blockage is an avoidance family

Fix `G`, a vertex set `C` and an order `n`. Write `attIn(C, X)` for the vertices of
`X ⊆ C` with a neighbour in `C ∖ X` ("attachments"), and call `(X₁, X₂)`
complementary in `C` when `X₁ ∪ X₂ = C` and `attIn(C, X₁) ⊆ X₂` — a separation of
`G[C]`, symmetric (`ComplementaryIn.symm`). A blockage of order `n` in `C` is a
family `𝓑` of subsets of `C` with (i) `|attIn| ≤ n` on members, (ii) downward
closed among sets with `|attIn| ≤ n`, (iii) exactly one side of every complementary
pair with `|X₁ ∩ X₂| ≤ n`. This is `Blockage.lean`'s `≤ n` reading, under which a
blockage of order `n` exists iff `pw ≥ n` (checked there to 4 vertices, here to 5,
both halves). At `C = V` it is `IsBlockage` (`isBlockageIn_univ_iff`).

Call `X` *big* when `|attIn X| ≤ n` and `X ∉ 𝓑`. By (ii), bigness is upward closed
among small-attachment sets. So `𝓑 = avoid(C, n, big) := {X ⊆ C : |attIn X| ≤ n,
¬ big X}` for any upward-closed predicate agreeing with it there, and the data of a
blockage is the predicate — in the finite case, its minimal big sets, the *frame*.
Axioms (i) and (ii) are then free; the whole content is (iii), which for a frame
`F₁, …, F_r` reads: (a) every separation of order `≤ n` has a side containing some
`F_j`, and (b) no separation of order `≤ n` has `F_i ⊆ X₁` and `F_j ⊆ X₂`. (b) is a
Menger condition, checkable pair by pair in polynomial time (`n + 1` vertex-disjoint
`F_i`–`F_j` paths, trivial paths at common vertices allowed, and `|F_i| ≥ n + 1`).
(a) is the hard half: "no separation of order `≤ n` splits every generator". A
compact class is a family of frames for which (a) follows from local, checkable
structure. BRST's own §4 says the same in the vocabulary of *stoppages*: a blockage
is a set of small cuts, one orientation per cut, such that no two chosen sides cover
`G`; strengthening "two" to "three" gives the tangle axioms, which is why blockages
are stronger than tangles and `pw ≥ tw`.

### 1.2 Candidate A — branch–minor frames (chosen)

Three operators on frames, each with (a) and (b) by construction:

* **Clique.** `K ⊆ C` a clique with `|K| ≥ n + 1`; `big X := K ⊆ X`. (a): a clique
  cannot be split by a separation (an edge from `X₁ ∖ X₂` to `X₂ ∖ X₁` would be an
  attachment of `X₁` outside `X₂`). (b): `K ⊆ X₁ ∩ X₂` would need `|X₁ ∩ X₂| ≥ n + 1`.
  Data: `n + 1` vertices.
* **Minor pullback.** A model of `H` inside `C`: branch sets `T_w ⊆ C` (`w ∈ V(H)`),
  disjoint, nonempty, connected, with an edge of `G` behind every edge of `H`; and a
  frame of order `n` on all of `H`. `big X := big_H {w : T_w ∩ X ≠ ∅}`. (iii): a
  separation of `G[C]` of order `≤ n` pulls back to a separation of `H` of order
  `≤ n` — a branch set meeting both sides meets the separator, because it is
  connected (`ComplementaryIn.exists_mem_inter_of_connected`) — and exactly one of
  its sides is big in `H`. Data: the branch sets (`≤ |C|` vertices) and `H`'s frame.
  Every clique minor, hence the Hadwiger number `had(G) − 1`, is in the class.
* **Branch** (the linked branch lemma of `Sandwich.lean`, Fellows & Langston 1987
  Lemma 4.3 / Kinnersley 1992 Corollary 4.2, as a blockage operator). Three
  pairwise disjoint connected `A, B, D ⊆ C` carrying frames of order `k`; for each
  pair a connected connector `Q ⊆ C` disjoint from the third branch and adjacent to
  both (it may meet the two it joins). `big X := at least two of big_A(X ∩ A),
  big_B(X ∩ B), big_D(X ∩ D)`; order `k + 1`. (iii): let `(X₁, X₂)` have order
  `≤ k + 1`. The three branches' shares of the separator are disjoint, so their
  orders sum to `≤ k + 1`. If all three are `≤ k`, each branch is big on exactly one
  side (its frame's axiom (iii) on the restricted separation, `branch_xor`), and of
  three such choices exactly one side receives two. Otherwise one branch holds the
  whole separator; the other two and their connector miss it, so each lies whole on
  one side (`ComplementaryIn.sides`), the connector on the same side as both (an edge
  across the separation would be an attachment, `not_adj_of_opposite`); that side
  has two whole branches, which are big (`big_self`), the other side has them empty,
  which are not (`not_big_empty`) — `exactly_one_of_full`. Data: three sets and
  three connectors, `≤ 2|C|` vertices, plus the three sub-frames. The cut-vertex
  form is the case `Q = {v}` (`BranchIn.of_hub`).

What it certifies that a clique minor cannot: the spider with three legs of two
(`pw 2`, `had 2`, three `K₂` branches at the hub), the complete ternary tree of
height 2 (`pw 2`), three `K₄` at a hub (`pw 4`, `had 4`); every tree, by Ellis,
Sudborough & Turner's characterisation, exactly. A certificate is a tree of operator
applications, and its order is downward closed in the obvious way (a clique of
`n + 1` is a clique of `n' + 1` for `n' ≤ n`; the other two operators pass the
property up by induction), so "three branches of order `≥ k`" is the right reading
of the branch operator.

### 1.3 Candidate B — connected frames with Menger ("path-brambles"), dead by argument

Generators `F_1, …, F_r`, each connected with `|F_i| ≥ n + 1`, pairwise
`(n + 1)`-inseparable (Menger), with hitting number `≥ n + 1` (no `n` vertices meet
every `F_i`). Then (a) holds — a separation that splits every `F_j` has a separator
meeting every `F_j` (a connected set split by a separation meets the separator), a
hitting set of size `≤ n` — and (b) is the Menger condition, so this is a blockage
of order `n`, checkable in polynomial time per pair plus one hitting-set
computation. It is the natural analogue of a bramble, and that is its death: take a
tree decomposition of width `w`. Each connected `F_i` lives in a subtree of the
decomposition tree. Either two subtrees are disjoint, and a bag between them
separates `F_i` from `F_j` with order `≤ w + 1`, so `w ≥ n`; or all pairwise
intersect, hence (subtrees have the Helly property) share a bag, which hits every
generator, so `w + 1 ≥ n + 1`. Either way `tw ≥ n`: **the class certifies `pw ≥ n`
only on graphs with `tw ≥ n`**, and can never see `pw > tw`, the target. Not taken
further; not formalised.

### 1.4 Candidate C — BRST's fractures, and the nested-prefix bands: not compact

BRST §2 proves existence through *partial blockages* (families with (i), (ii),
`∅ ∈ 𝓑` and no *fracture*: no chain `X_1 ⊂ … ⊂ X_m` of small-attachment sets with
small steps from a member to the complement of a member) and extends them to
blockages by (2.5). "No fracture" is a universal statement over chains, exactly as
global as axiom (iii); the paper's fractures are the tool of the existence proof,
not data. The *band* obstruction of `reports/checkpoint_relaxation.md` — UNSAT of
nested sets at consecutive sizes with small inner boundary — is the same universal
statement in layout vocabulary: the family it would generate (sets reachable by
small steps from `∅`) is a partial blockage, not downward closed as a frame and not
compact; its certificate is the refutation itself. Neither is a class in the sense
asked for.

### 1.5 The co-singleton frames seen in the data (not a candidate going in; recorded in §4)

## §2. The theorem

### 2.1 Definitions (`BlockageClass.lean`)

```
attIn G C X            vertices of X with a neighbour in C \ X
ComplementaryIn G C X₁ X₂   X₁ ∪ X₂ = C ∧ attIn G C X₁ ⊆ X₂
IsBlockageIn G C n B   (i) members ⊆ C with ≤ n attachments; (ii); (iii) with Xor
isBlockageIn_univ_iff  IsBlockageIn G univ n B ↔ IsBlockage G n B
avoid G C n big        {X | X ⊆ C ∧ |attIn G C X| ≤ n ∧ ¬ big X}
Upward big             ∀ X ⊆ Y, big X → big Y
Frame G C n            big, Upward big, IsBlockageIn G C n (avoid G C n big)
```

Relative blockages keep every set a `Finset V` of the one graph `G`, so the
sub-frames a branch carries are frames of `G[C_i]` with no subtypes and the
recursion composes. The price is that `IsBlockageIn G C n B → n ≤ pathwidth
(G.induce C)` is not stated (it is not needed: certificates are used at `C = univ`,
where `isBlockageIn_univ_iff` hands them to `pathwidth_ge_of_isBlockage`).

### 2.2 Theorems

| name | statement |
|:--|:--|
| `isBlockageIn_clique`, `Frame.clique` | `K ⊆ C` a clique, `n + 1 ≤ |K|` ⇒ `avoid G C n (K ⊆ ·)` is a blockage of order `n` in `C` |
| `MinorModelIn`, `pull`, `card_att_pull_le`, `card_pull_inter_le`, `complementary_pull` | the pullback lemmas: `|att_H (pull X)| ≤ |attIn X|`, `|pull X₁ ∩ pull X₂| ≤ |X₁ ∩ X₂|`, a separation pulls back to a separation |
| `isBlockageIn_minor`, `Frame.minor` | a blockage of order `n` on `H` pulls back along a model inside `C` |
| `BranchIn`, `twoOf`, `branch_xor`, `branches_same_side`, `exactly_one_of_full` | the branch operator's two cases |
| `isBlockageIn_branch`, `Frame.branch` | three linked branches with frames of order `k` ⇒ a frame of order `k + 1` on `C` |
| `BranchIn.of_hub`, `connected_induce_singleton` | the cut-vertex form |
| `Frame.pathwidth_ge` | `Frame G univ n → n ≤ pathwidth G` |
| `pathwidth_ge_of_clique_frame`, `pathwidth_ge_of_branch_frames` | the two spelled-out certificate theorems |

Supporting lemmas: `exists_boundary_edge_of_connected` (a connected set with a
vertex in `X` and one outside has an edge leaving `X` inside it; walk induction),
`ComplementaryIn.{symm, inter, sides, exists_mem_inter_of_connected,
not_adj_of_opposite, attIn_subset_inter, attIn_right_subset_inter}`,
`IsBlockageIn.{empty_mem_and_self_not_mem, big_self, not_big_empty}`.

The axiom audit, verbatim from the build:

```
'MOSPFormalization.Blockage.Frame.pathwidth_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'MOSPFormalization.Blockage.isBlockageIn_clique' depends on axioms: [propext, Classical.choice, Quot.sound]
'MOSPFormalization.Blockage.isBlockageIn_minor' depends on axioms: [propext, Classical.choice, Quot.sound]
'MOSPFormalization.Blockage.isBlockageIn_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'MOSPFormalization.Blockage.pathwidth_ge_of_branch_frames' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`; the whole library builds (`lake build`, exit 0,
`reports/scratch/blockage_class/lean_build_all.out`).

### 2.3 Brute force before stating (`--stage check`, `checks.json`)

On every graph of the atlas with 1–6 vertices (208 graphs), 71 s:

| check | what | result |
|:--|:--|--:|
| clique | every `C ⊆ V`, every clique `K ⊆ C`, every order `n < |K|` (to 5 vertices): `avoid(C, n, K ⊆ ·)` satisfies (i)–(iii) | 0 violations |
| branch | triples of disjoint connected sets carrying clique frames of equal order, pairwise linked, in `C = V` and three random `C ⊇ A ∪ B ∪ D`: the output satisfies (i)–(iii) at order `k + 1` | 0 violations on 4,240 triples |
| branch, control | the same with at least one pair *unlinked* | fails on 3,486 of 4,706 |
| minor | random models of 1–4 connected disjoint branch sets, every clique of the quotient, `C = V` and `C = ∪T` | 0 violations |
| duality | a blockage of order `n` exists in `V` iff `pw ≥ n`, by a backtracking search over orientations (to 5 vertices) | 0 violations |

The first design of the branch operator in this session (membership of the
restricted sets in the sub-blockage, without an upward-closed predicate) had a gap
in axiom (ii) that the frame formulation removes; the brute-force check of the
final form is what licensed the Lean statement.

## §3. The ceiling

### 3.1 The formula

Let `ceiling(G)` be the largest `n` for which some certificate tree of the three
operators gives a frame of order `n` on `V(G)`. Then

`ceiling(G) = max( had(G) − 1 , 1 + max { t : ∃ pairwise disjoint, pairwise linked, connected U₁, U₂, U₃ ⊆ V with ceiling(G[U_i]) ≥ t } )`

where "linked" is the `BranchIn` condition (for each pair a connected `Q ⊆ V` missing
the third set and adjacent to both, i.e. some component of `G − U_k` meets `N(U_i)`
and `N(U_j)`), and `had` is the Hadwiger number. Proof sketch: `≥` is the two
operators applied on `G` itself (a clique minor is a clique frame pulled back).
`≤`: a certificate is a minor model of some `H` with a clique or a branch structure
in `H` (pullback composes: a model of a model is a model); a clique in `H` is a
clique minor of `G`; a branch structure in `H` pulls back to three disjoint connected
sets of `G` (unions of branch sets) with connectors that are unions of branch sets
of connected sets, hence connected, and `H[C_i]` is a minor of `G[C_i']`, so by
minor monotonicity of the class (pullback is an operator) `ceiling(H[C_i]) ≤
ceiling(G[C_i'])`. The `max` over levels is legitimate because orders are downward
closed (§1.2). Checked: the recursive evaluation and an independent enumeration over
every minor (single-step deletions and contractions, memoised on nauty
certificates) agree on all 1,252 graphs to 7 vertices and never exceed the exact
pathwidth (`test_ceiling_matches_closure_and_is_valid`).

Implementation: `Ceiling.ceiling` recurses over every connected induced subgraph
(memo on `pynauty.certificate`); `Ceiling.hadwiger` by `max(ω, max_e had(G/e))`;
the branch term by the minimal sets of each level and a scan for a linked disjoint
triple. Feasible to 11 vertices (2,048 subsets a graph); the 1,038 graphs at 10–11
took most of the 138 s.

### 3.2 The census: every graph with `pw > tw` to 9 vertices, every `pw − tw = 2` to 11

Inputs: `learning/_pwtw_exhaust --min-diff 1` on `nauty-geng` for `n ≤ 9` (the
exhaust's own pathwidth and treewidth; `pw ≤ tw + 1` on every graph to 9, as §27
found) and `learning/data/ensemble/pwtw_found.csv` for 10–11. Every ceiling was
compared with the exact pathwidth (never above).

| n | `pw − tw` | graphs | tight | `ceiling = had − 1` | branch contributes | max shortfall |
|--:|--:|--:|--:|--:|--:|--:|
| 6 | 1 | 1 | 0 | 1 | 0 | 1 |
| 7 | 1 | 15 | 1 | 14 | 1 | 1 |
| 8 | 1 | 356 | 4 | 352 | 4 | 1 |
| 9 | 1 | 13,565 | 42 | 13,523 | 42 | 2 |
| 10 | 2 | 4 | 0 | 4 | 0 | 2 |
| 11 | 2 | 1,034 | 0 | 1,022 | 12 | 2 |

`ceiling = tw` on 14,915 of 14,975; `> tw` on 59 (the 47 tight ones and 12 at
`n = 11` with `tw 2`, `pw 4`, ceiling 3); `< tw` on one 9-vertex graph
(`HCZL]yz`, `tw 4`, `had 4`: a treewidth-4 graph with no `K₅` minor, where even
the clique-minor term is a step short of treewidth). The 15 trees in the set are all
tight; the other 32 tight graphs each carry three linked branches of order
`pw − 1` (only 6 of them at a cut vertex with three components: on 26 the certificate
needs the *linked* form's separate connectors, which the cut-vertex form of §38
cannot see). The
smallest miss: `EElw`, the triangle `{3,4,5}` with ears `0 ~ 3,4`, `1 ~ 3,5`,
`2 ~ 4,5` (`pw 3`, `tw 2`, `ω 3`, `had 3`, ceiling 2). The 10-vertex graphs of §21
(three `K₄` glued at three hubs plus a pendant each, `pw 5`, `tw 3`): ceiling 3.

Reading: on the graphs where `pw > tw`, the class's ceiling *is* the treewidth, with
59 exceptions in 14,975, all of them graphs with three disjoint branches at a hub.
Branching is not what makes `pw` exceed `tw` on small graphs.

### 3.3 The corpus: the 197 bound-gap instances at 20–40 customers

The 338 gap instances (`optimum − lb_best ≥ 2`) of `reports/obstruction_search.md`
have 197 at `n ≤ 40` (17 at 20, 133 at 30, 5 at 37–39, 42 at 40; Harvey 71,
Simonis 73, Faggioli–Bentivoglio 46, Chu & Stuckey 7). The searched contraction
minor (`04_minor/joined.csv`, `best_floor`) is tight on all 197. The exact ceiling
is out of reach at these sizes (the recursion is over `2^n` subsets), so it is
bracketed:

* **lower**: certificates the class's operators find — `ω`, the clique number of
  every minor of the contraction-degeneracy sequence (`bound_harness.contraction_minors`),
  and the harness's separator branch recursion `branch_bound(·, family_separators,
  seed_clique, ·)` seeded by cliques only (components of `H − S` as branches, the
  components of `H[S]` as connectors — a `BranchIn`), on the graph and on each of
  the first 60 minors, 20 s budget, never censored; `cand_blockage_class` returns
  optimum units and ran through `bound_harness.evaluate_candidates`;
* **upper**: `min(pw, counting_upper_bound)`: the clique term is `≤ had − 1 ≤
  tw_hi`; a branch certificate of order `t` needs three disjoint connected sets of
  pathwidth `≥ t − 1`, hence `3 · min_vertices(t − 1) ≤ n` with
  `min_vertices(s) = s + 1` for a clique minor (`s + 1 ≤ had`) and `3 ·
  min_vertices(s − 1)` otherwise, `3 (t − 1) ≤ τ(G)` (pathwidth is at most the
  vertex cover number, `IndependenceBound.lean`, and vertex cover numbers of
  disjoint induced subgraphs add up to at most `τ(G)`), and `3 · C(t, 2) ≤ |E|`
  when the three sub-certificates are clique minors.

Every lower value is `≤ pw` (checked, the run stops otherwise) and `≤ upper`.

| verdict | all | `pw − tw` = 2 | 1 | 0 | n = 20 | 30 | 37–39 | 40 |
|:--|--:|--:|--:|--:|--:|--:|--:|--:|
| tight | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| dead | 104 | 20 | 84 | 0 | 12 | 73 | 0 | 19 |
| clique-minor only | 76 | 0 | 0 | 74 (+2 with `tw_hi > pw`) | 5 | 57 | 5 | 9 |
| branch open | 17 | 0 | 15 | 2 | 0 | 3 | 0 | 14 |

(`tw` here is the invariants table's interval; 11 of the 93 undecided have
`tw_lo < tw_hi`.) The 17 "branch open" are 16 Faggioli–Bentivoglio instances and
`Warwick 1473`, at `n = 30–40`, `pw 7–10`, `ω 4–6`, 81–137 edges: a branch
certificate would need three vertex-disjoint `K_pw`-minor models in a graph whose
contraction sequence shows no clique above `pw − 1`; not excluded by counting, not
decided (a packing search, outside this step).

Against the other bounds on record, in pathwidth units:

| comparison (197 instances) | `>` | `=` | `<` |
|:--|--:|--:|--:|
| class certificates found vs searched minor (`best_floor − 1`) | 0 | 0 | 197 |
| vs reference `max(lb_best, tw + 1) − 1` | 0 | 15 | 182 |
| vs `lb_best − 1` | 1 | 119 | 77 |
| vs `ω − 1` (the trivial member of the class) | 178 | 19 | 0 |
| counting upper bound vs searched minor | 0 | 93 | 104 |

Mean shortfall `pw − value`: certificates 2.73, counting bound 0.57, reference
0.80, Harper's ceiling 1.86. The branch recursion improved on the clique terms on
0 of 197 (top level and minors alike), consistent with §38's `sep-branch`, which
with a treewidth seed beat the reference on none of the 338.

### 3.4 Why, in one line

Three branches of pathwidth `pw − 1` need `3 pw` vertices and, on sparse instances,
three disjoint certificates of order `pw − 1` that are themselves clique minors or
nested triples (`9 (pw − 2)` vertices). The gap instances at ≤ 40 customers have
`pw ≈ n / 3` or more when dense (Simonis, Harvey) and `pw = tw + 1 ≥ 6` when sparse
(Faggioli): no room either way. The census says the same with no counting: at 6–11
vertices `pw > tw` is caused by structures like the triangle with three ears, which
have no three disjoint high-pathwidth pieces.

### 3.5 Kill criterion

Stated before measuring: the class is dead if on the gap instances at ≤ 40
customers its ceiling never exceeds the searched-minor value. **Met.** The searched
minor is tight on 197 of 197, so no ceiling can exceed it; the class's ceiling is
proved strictly below on 104, equal on none, and on the 93 left the only certificates
still possible are clique minors (76) or a packing of three (17). What a search over
the generating data would have to enumerate, had the criterion not been met: minor
models (branch sets) and, inside them, triples of disjoint connected sets with
connectors, recursively — the sets of the §38 `sep-branch` family plus arbitrary
connected subsets; the counting bounds say the enumeration would find nothing on
104 and at most clique minors on 76.

## §4. What the missed blockages look like

For `EElw` the backtracking search (`check_duality`'s machinery) returns an order-3
blockage whose big sets are generated by `V ∖ {0}`, `V ∖ {1}`, `V ∖ {2}` — the
three co-ears. It is a blockage because (b) is automatic (`|X₁ ∩ X₂| ≥ |V| − 2 = 4
> 3` whenever two generators sit on opposite sides) and (a) holds because every
separator of ≤ 3 vertices leaves `G − S` connected, or connected plus one ear, or
exactly the three ears: one side of every small separation is at most one ear. In
general, `{V ∖ {u} : u ∈ U}` is a blockage of order `n` iff `|V| ≥ n + 3` and
every `S` with `|S| ≤ n` leaves `G − S` connected, connected plus a singleton of
`U`, or three singletons of `U` — a condition on small separators, nothing about
disjoint pieces, and `(n + 1)`-connectivity relaxed by ears. On the graphs the class
misses it holds for 1 of 1 (n = 6), 6 of 14 (7), 37 of 352 (8) and 11 of a random
600 (9): a second small class, not the general one. The general one must say, for a
band of consecutive orders, "every small separation has a trivial side" — which is
the band obstruction of `reports/checkpoint_relaxation.md` read from the dual side,
and the reason no single-structure class has reached it.

## §5. Decisions recorded

* The linked form of the branch operator was formalised rather than the cut-vertex
  form, because the pullback of a cut vertex is a connected hub set and the pullback
  of three connectors is three connected sets — the linked form is what minor
  pullback preserves, and `BranchIn.of_hub` recovers the cut-vertex form.
* Relative blockages (`IsBlockageIn G C`) rather than `IsBlockage (G.induce C)`: no
  subtypes in the recursion; the correspondence with the induced subgraph is by
  definition (`attIn G C X` is `att (G.induce C) X`) and is not a Lean theorem.
* The harness's CLI validity stage was not run (it appends to the committed
  `bound_harness_values.csv.gz`); its `evaluate_candidates` was called instead and
  every value compared with the certified optimum in the corpus stage, which stops on
  a violation. No value was above an optimum, on 197 instances or 14,975 graphs.
* The 93 undecided corpus instances were left undecided: deciding them is a
  clique-minor containment or packing search, and the brief said no search.
