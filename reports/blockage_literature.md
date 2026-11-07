# Three papers on the dual side of pathwidth: what they hold for the blockage work

*2026-11-07, one reading session. The three PDFs were read whole through
`pdftotext -layout` (28, 18 and 13 pages); page numbers below are the papers'
own printed page numbers. No solver was run and nothing under `solutions/`
was touched; the only computation is a 30-line enumeration of set families on
a three-vertex path (§4.1), done to check a convention before putting it in
writing. Context read first: `reports/blockage_class.md` §0 and
`paper1/latex/sec9f_appendix_dual.tex` (Appendix F).*

The three papers:

1. Diestel, R. & Oum, S. (2019). *Tangle-tree duality: in graphs, matroids and
   beyond.* Combinatorica 39, 879–910; arXiv 1701.02651v3. Cited below as **DO**.
2. Groenland, C., Joret, G., Nadara, W. & Walczak, B. (2023). *Approximating
   pathwidth for graphs of small treewidth.* ACM Trans. Algorithms 19(2);
   arXiv 2008.00779v4. Cited as **GJNW**.
3. Erde, J. (2017). *Directed path-decompositions.* arXiv 1711.00718v1. Cited
   as **Erde**.

## §0. What we can use, ranked

Honest summary first: none of the three gives a compact lower-bound certificate
for pathwidth, none says anything about computing blockages, and none moves the
ceiling measured in `reports/blockage_class.md` §3. What they do give is (1) a
proof template for the half of the BRST theorem we do not hold in Lean, (2) one
concrete family of graphs on which our generating class provably falls short,
with the reason written out, and (3) a convention check that catches an
off-by-one in Appendix F. Ranked:

1. **A route to the converse `pw ≥ n ⇒ blockage of order n` without BRST's
   fractures: Erde's Theorem 12 (pp. 7–8) specialised to symmetric digraphs,
   then DO's Theorem 7.2 (ii)→(i) (p. 19).** Erde proves, in one and a half
   pages, that for `ω ≥ k` and `|V| ≥ k` a digraph has an `S_k`-path of width
   `< ω − 1` or an `ω`-diblockage of `S_k`, never both, by induction on the
   number of unoriented separations, with one gluing step (up-shift one partial
   decomposition, down-shift the other onto a minimum-order separation between
   them; Lemmas 10–11, pp. 5–6). Replace every edge by two opposite arcs and the
   directed objects become the undirected ones: directed separations of the
   symmetric digraph are exactly the vertex separations `(A, B)` of the graph
   (p. 3, definition), directed path-decompositions are path decompositions
   (Lemma 8, p. 4; Erde uses this identification himself on p. 12), and a
   `k`-diblockage (`ω = k`, p. 7) is, clause for clause, DO's
   `F_k^{(2)}`-tangle (DO p. 18): a consistent orientation of the separations of
   order `< k`, sets of fewer than `k` vertices on the small side, and no two
   members pointing towards each other whose big sides overlap in fewer than
   `k` vertices. DO's Theorem 7.2 (ii)→(i) then turns such an orientation into a
   BRST blockage in half a page (`B := {X : (X, Y) ∈ O}`, p. 19), using only
   consistency and the auxiliary separation `{X, ∂X ∪ (V ∖ X)}` that
   `Blockage.lean` already has as `compl`. **What it is not**: it is not shorter
   than BRST's (2.3)–(2.5) in page count (BRST pp. 276–279 is about three pages;
   Erde §2–3 plus DO's half page is about four), and DO's own route goes through
   their general Theorem 3.2 (p. 8), whose proof is in a paper we do not hold
   (arXiv 1701.02509). What it is: fewer distinct lemmas, objects that are
   functions on separations and lists of nested separations rather than
   sequences normalised by "simple fractures" (BRST (2.3)), and a single hard
   lemma — Erde's Lemma 11 (p. 6), the statement that shifting a decomposition
   onto a *linked* separation does not enlarge any bag — which DO call "the only
   bit of magic now left in tree-width duality" (Lemma 6.1, p. 15) and which is
   Thomas's key lemma in Bellenbaum–Diestel's form. The identity it rests on,
   `|A,B| + |C,D| = |A∪C, B∩D| + |A∩C, B∪D|` (Erde (2.1), p. 5), is an equality
   for vertex separations, so no submodularity inequality is needed. If the
   converse is ever formalised, this is the proof to formalise; it is a few
   thousand lines of Lean, not a few hundred, and it has not been started.

2. **GJNW's tightness family (Theorem 5.1, p. 15; Claim 5.3, p. 16) is a
   family our class provably misses, and its proof says why.** `T_h^{(t)}`
   replaces each node of the complete ternary tree of height `h` by a `K_t` and
   each tree edge by a perfect matching between the two cliques. It has
   `tw = t` (Claim 5.2, p. 15) and `pw ≥ t(h + 1) − 1` (Claim 5.3). The class
   of `BlockageClass.lean` reaches `t + h − 1` on it from the obvious data
   (Hadwiger number `t + 1`, so `had − 1 = t`; the three subtrees are pairwise
   linked through the root clique and the branch operator adds one per level),
   against a pathwidth of at least `t(h + 1) − 1`: a difference of `(t − 1)h`
   between what the obvious data certify and what is true. Whether other data
   in the class do better was not computed (an upper bound on the class's
   value needs the census code), but on the smallest member, `T_1^{(2)}` (8
   vertices, `tw 2`, `pw 3`), the census has already decided it: it is one of
   the 13,882 graphs on which the class's ceiling equals the treewidth
   (`reports/blockage_class.md` §3), one below the pathwidth. The
   reason, read off Claim 5.3's proof: its induction carries not "a bag of size
   `≥ m`" but "a bag of size `≥ m` **and `t` vertex-disjoint paths from the root
   clique to that bag**", and the three branches are joined to the hub by `t`
   disjoint paths each, so the middle bag picks up `t` outside vertices per
   level instead of one. Our `branch_lemma` (`Sandwich.lean`) and
   `Frame.branch` are the case `t = 1`, where connectivity of the branch
   supplies the one path for free (that is exactly how GJNW's Lemma 2.1, p. 4,
   uses connectivity). A **candidate fourth operator** follows — stated here as
   a conjecture with a proof sketch, *not* checked by brute force, *not* in
   Lean, *not* measured, so by this project's own rule it is not yet a
   statement: for a graph `H` and a `t`-set `R ⊆ V(H)` call `ℓ_R(H) ≥ m` if
   every path decomposition of `H` has a bag `B` with `|B| ≥ m` and `t`
   vertex-disjoint `R`–`B` paths in `H`; a clique `K ⊇ R` gives `ℓ_R ≥ |K|`;
   and if `H_1, H_2, H_3` are disjoint with root sets `R_i`, `ℓ_{R_i}(H_i) ≥ m`,
   and a `t`-set `R` outside them is joined to each `R_i` by `t` disjoint paths
   whose interiors are private to `i` and avoid the other two `H_j`, then
   `ℓ_R(G[R ∪ H_1 ∪ H_2 ∪ H_3]) ≥ m + t`, hence `pw ≥ m + t − 1`. The sketch is
   Claim 5.3's argument verbatim: order the three big bags, concatenate the
   paths `B_1 → R_1 → R → R_3 → B_3`, which avoid `H_2` and are disjoint
   because each path from `R` to `R_1` and to `R_3` starts at a distinct vertex
   of `R`; each of the `t` paths meets the middle bag outside `H_2`. Two
   warnings. First, the naive generalisation "`t` disjoint paths between the
   branches avoiding the third ⇒ `+t`" is **false as a lemma** without the
   rooted invariant: the paths must start in the big bag of the branch, not
   anywhere in it, and only the invariant guarantees that. Second, the
   counting argument that killed branching on the corpus gap instances
   (`reports/blockage_class.md` §3.3: three branches of pathwidth `≥ pw − 1`
   need `3·pw > n` vertices) does not transfer: a `+t` operator needs three
   branches with `m = pw + 1 − t` each, i.e. about `3(pw + 1 − t) + t ≤ n`,
   which at `pw = 12, n = 30` is satisfiable from `t = 5`. Whether the gap
   instances contain such `t`-linked triples is a packing search nobody has
   run; in MOSP graphs a large pattern is a natural hub clique `R`. This does
   not contradict the kill verdict of `blockage_class.md` §0, which was about
   the stated class; it says where the next operator, if any, comes from.

3. **DO's Theorem 7.2 (pp. 18–19) is the citable statement that a blockage is
   an orientation**, and it settles the order convention. (B2) becomes
   consistency and (B3) becomes "exactly one orientation per separation"; the
   whole content is the two-star clause, which is BRST's stoppage condition
   (BRST §4 (4.1), p. 281: no two chosen small sides cover `G`), and the
   comparison with tangles is explicit: tangles forbid three small sides
   covering `G` (DO p. 9, Theorem 4.1; BRST p. 282), blockages forbid two. This
   is what `reports/blockage_class.md` §1.1 derived by hand as "avoidance
   families", now with a reference. Convention: DO's blockage "of order `k − 1`"
   uses `< k` (p. 18) and is dual to `pw ≥ k − 1`; Erde restates BRST with `≤ k`
   and `pw ≥ k` (pp. 1–2); BRST's own proof of (2.1) bounds bags by `|W_i| ≤ n`
   for "path-width `< n`" (p. 279) and (2.2) has `α(Y) ≤ n` (p. 276; the PDF's
   text layer renders `≤` as `<`, which is the likely origin of the slip
   below). `Blockage.lean` and `blockage_class.md` §1.1 use `≤ n`. **Appendix F
   prints `< n` in (i)–(iii) and "fewer than `n` vertices" in the proof, which
   is off by one** (§4.1 below, with the three-vertex witness).

4. **GJNW's certificate is exactly our iterated branch operator, and on our
   instances it is worth at most `⌊log₃ n⌋`.** Their `T_h`-witness (p. 4) is a
   ternary tree of vertex sets built by "three disjoint connected pieces in
   `T_{h−1}`, any two joined by a path avoiding the third" from `T_0` =
   connected graphs, and Lemma 2.1 (p. 4) is the three-bags argument of
   Fellows & Langston 1987 Lemma 4.3 that `branch_lemma_linked` formalises; as
   a frame it is `Frame.branch` iterated from the order-0 clique frame, so our
   class contains it and, being seeded by cliques and minors, dominates it.
   Every graph in `T_h` has at least `3^h` vertices (p. 4), so the certificate
   is `≤ 4` for `n ≤ 242` against widths of 10–100 on the open instances. The
   algorithm (Theorem 4.1, pp. 6–7; §4.1–4.3, pp. 7–15) is polynomial given any
   tree decomposition and we could feed it the exact elimination orderings of
   `learning/treewidth.py` (to 64 customers) or min-fill ones; it would return
   `h`, a `T_h`-witness and a path decomposition of width `≤ (t_0 + 1)h + 1`,
   none of which improves anything we hold. **Nothing beyond citation**, and
   the citation in `literature/MISSING.md` needs one correction (§4.2).

5. **Erde's Theorem 14 (pp. 10–11): every graph has a *linked* optimal path
   decomposition.** With `ω = k` on the symmetric digraph: there is a path
   decomposition of width `pw(G)` in which, for any two of its prefix
   separations, the smallest separation order between them along the
   decomposition equals the smallest order of any separation nested between
   them (definition p. 10; by Menger, the largest number of disjoint paths from
   the later bag to the earlier one). This is a dominance property of optimal
   layouts, of the kind the closing search prunes on, and it is not among the
   rules in `satisfiability/customer_search.py` or `pathwidth_solver/`. Its
   value as a pruning rule is unmeasured and, given `reports/inner_loop.md`
   (the existing rules already collapse the node before anything else is
   consulted) and `reports/checkpoint_relaxation.md` §10 (the node count at
   125 is the lattice's size), probably small; it would discard layouts, not
   closed sets. Recorded as a candidate, not proposed. Erde's appendix (p. 12)
   also shows the *lean* strengthening is false for path decompositions (a
   lean bag would be well-linked, forcing treewidth, on the doubled binary
   tree), which is worth knowing before anyone tries to add Menger
   conditions to a layout search.

6. **On computing blockages: nothing in any of the three.** DO say so
   themselves (footnote 1, p. 3): "We make no claim here as to how fast such a
   witness might be computable, only that checking it will be fast", and the
   fast-to-check witness is the *tree* (the upper-bound side, linearly many
   separations), not the tangle; "exploring the F-tangle-tree theorem from an
   algorithmic point of view is a problem we would indeed like to see
   tackled". Erde's proof of Theorem 12 is an exponential procedure (orient one
   separation at a time, backtrack through the gluing). GJNW compute their
   witness in polynomial time but it is the `log₃ n` object above.

7. **Nothing beyond citation.** DO's abstract framework (§2–3, pp. 4–8) buys
   generality — treewidth, branch-width, rank-width, matroid treewidth and a
   bounded-adhesion variant (§9, Theorem 9.3, p. 24) from one theorem — not
   compactness; a tangle is an orientation of all separations of order `< k`,
   as large as a blockage. Bowler's negative result (Theorem 11.1, p. 27): for
   `k ≥ 5` no forbidden set of *stars* makes "the orientations pointing to some
   `K_k` minor" an `F`-tangle class — a warning that concrete objects such as
   clique minors and abstract orientations do not match one-for-one, in the
   direction opposite to ours (our minor frames *are* blockages, proved). The
   two-parameter dual objects (DO `F_k^w`, Erde's `ω > k`) certify the absence
   of decompositions with *both* small width and small adhesion, which is not
   a pathwidth bound, so they do not give a cheaper certificate either.

## §1. Diestel & Oum (2019)

**What it proves.** One abstract theorem (Theorem 3.2, p. 8, proved in their
companion paper arXiv 1701.02509, not held): in a separation system `S` inside
a universe, with `F` a set of stars of separations that is "standard" and for
which `S` is "`F`-separable", exactly one of (i) an `F`-tangle of `S` exists
(a consistent orientation of `S` with no subset in `F`), (ii) an `S`-tree over
`F` exists (a tree whose edges carry separations, each node's incoming star in
`F`). The paper then chooses `S` and `F` to recover, as corollaries, the
classical dualities: Robertson–Seymour tangles against branch-width
(Theorem 4.4, p. 11), tangles in set-separation universes against rank-width,
carving-width and matroid branch-width (Theorem 5.2, p. 13), brambles against
treewidth (Theorem 6.5, pp. 17–18), **blockages against pathwidth (Theorem
7.2, pp. 18–19)**, matroid treewidth (Theorem 8.5, p. 22), bounded adhesion
(Theorem 9.3, p. 24), and the Amini–Mazoit–Nisse–Thomassé bramble duality
(Theorem 10.2, p. 26). Their claim on p. 2: "Our theorems easily imply theirs,
but not conversely."

**The separation system and the `F` for path decompositions.** For a graph
`G`, the universe is the vertex separations `(A, B)`, `A ∪ B = V`, no edge
between `A ∖ B` and `B ∖ A`, ordered by `(A, B) ≤ (C, D)` iff `A ⊆ C` and
`B ⊇ D`, with order function `|A, B| = |A ∩ B|` (p. 9); `S_k` is the
separations of order `< k`, and it is "separable" because the order function
is submodular (Lemma 3.4, p. 8). For treewidth the forbidden set is
`F_k = { stars (A_i, B_i)_{i=0..n} with |⋂ B_i| < k }` (p. 14) and an
`S_k`-tree over `F_k` is a tree decomposition of width `< k − 1`, with the bag
at a node being the intersection of the `B`-sides of its incoming star
(Lemma 6.3, p. 16). **For pathwidth** the only change is to restrict stars to
at most two elements: `F_k^{(2)} = { σ ∈ F_k : |σ| ≤ 2 }` (p. 18), because a
tree all of whose nodes have at most two incoming edges is a path.
Theorem 7.1 (p. 18): `G` has an `F_k^{(2)}`-tangle of `S_k` or an `S_k`-tree
over `F_k^{(2)}`, never both; its proof is "Apply Theorem 3.2 and Lemmas 3.3,
3.4 and 6.1" — Lemma 6.1 (pp. 15–16) being the one real lemma, that `F_k` is
closed under shifting, and shifting preserves the size of a star, so
`F_k^{(2)}` is closed too.

**How BRST's blockages sit in it.** Theorem 7.2 (p. 18) lists four
equivalents for `G ≠ ∅`, `k > 0`: (i) `G` has a blockage of order `k − 1`;
(ii) an `F_k^{(2)}`-tangle of `S_k`; (iii) no `S_k`-tree over `F_k^{(2)}`;
(iv) `pw(G) ≥ k − 1`. Their blockage (p. 18) is BRST's with `< k`: (B1)
`|∂X| < k` on members, (B2) downward closed among sets with `|∂X| < k`, (B3)
for every `{X_1, X_2} ∈ S_k` exactly one side is a member — so their "order
`k − 1`" is BRST's "order `n`" with `n = k − 1` and `≤ n`. The proof (p. 19) is
the translation both ways: from a blockage, `O = {(X, Y) ∈ S_k : X ∈ B}` is a
consistent orientation (by (B2) and (B3)), contains `(X, A)` for every `|X| < k`
(because `V ∉ B`, from `{X, V}`), and avoids every two-star
`{(A_1, B_1), (A_2, B_2)}` with `|B_1 ∩ B_2| < k` by three applications of
(B3); from an `F_k^{(2)}`-tangle `O`, `B = {X : (X, Y) ∈ O}` satisfies (B3)
because two members `X_1, X_2` of a separation would give the forbidden star
`{(X_1 ∩ Y_2, X_2), (X_2, Y_2)}`, and (B2) through the auxiliary separation
`{X, ∂X ∪ (V ∖ X)}` and consistency. That is the whole of the blockage-specific
content; the hard direction (iv)⇒(ii) is Theorem 3.2 applied through
Lemma 6.3.

**Is it a different or more usable description than axioms (i)–(iii)?**
Different in form — an orientation with two local conditions instead of a
family with a downward-closure axiom — and the same object; it is BRST's own
stoppage of §4 ((4.1), p. 281) in DO's vocabulary, with the tangle comparison
made exact (two-stars for pathwidth, three-stars for tangles; DO p. 9, BRST
p. 282). Not more compact: it orients every separation of order `< k`. The one
passage that speaks to why no vertex set is the certificate is the grid
remark on p. 14: for every low-order separation most of the grid lies on one
side, yet "every single vertex will lie on the 'wrong' side for some
low-order separation", so the tangle's location "is not represented
correctly by any one of its vertices" — the pathwidth analogue is the
"every small separation has a trivial side" obstruction of
`reports/blockage_class.md` §4.

**Does it suggest a compact certificate or an easier converse?** No compact
certificate (footnote 1, p. 3, quoted in §0 item 6). On the converse, the DO
route to `pw ≥ k − 1 ⇒` blockage is: Lemma 6.3 (p. 16, no `S_k`-tree over
`F_k^{(2)}`) → Theorem 3.2 (p. 8, the `F_k^{(2)}`-tangle; proof not in this
paper) → Theorem 7.2 (ii)⇒(i) (p. 19, the blockage). For a Lean proof of the
pathwidth case alone, Erde's Theorem 12 (§3 below) is Theorem 3.2's induction
specialised to paths and written out in full, so it is the version to follow;
DO's general theorem would pay only if the treewidth duality (Theorem 6.5)
were wanted in the same development.

**Other items noted.** The distinction on p. 1 between "concrete" highly
cohesive substructures (brambles: sets of edges that hang together) and
"abstract" ones (tangles: orientations) — a blockage is abstract; Appendix F's
sentence that the blockage "is to pathwidth what the brambles of Seymour and
Thomas are to treewidth" is loose in that sense (the exact treewidth analogue
of a blockage is the `F_k`-tangle, Theorem 6.5), and the concrete object dual
to pathwidth is not supplied by DO or, as far as these three papers go, by
anyone. Bowler's Theorem 11.1 (p. 27): for `k ≥ 5` there is a graph (the
once-subdivided `K_k`) on which no star-`F` makes "orientations pointing to an
`IK_k`" the `F`-tangles; weak stars (consistent antichains, p. 27) repair it in
their sequel. Section 11 (p. 26) lists variants of `F` for tailor-made
decompositions (forbidding `m`-sets for `m ≤ n`, trees of minimum degree `n`,
planar leaf parts); none matches a structure of MOSP instances.

## §2. Groenland, Joret, Nadara & Walczak (2023)

**What it proves.** Theorem 1.1 (p. 2): every graph with treewidth `t − 1`
has pathwidth at most `th + 1` or contains a subdivision of a complete binary
tree of height `h + 1`; the bound is tight up to a constant factor (§5). The
algorithmic form, Theorem 1.2 (p. 3) / Theorem 4.1 (pp. 6–7): given a
connected graph and a tree decomposition of width `≤ t − 1`, a polynomial-time
algorithm computes `h` with `G ∈ T_h` and `pw(G) ≤ th + 1`, a `T_h`-witness,
and a path decomposition of width `≤ th + 1`. Corollary 1.3 (p. 3): a
polynomial `O(t √log t)`-approximation for pathwidth on graphs of treewidth
`t`, the first `f(tw)`-approximation; with a tree decomposition of width `t_0`
supplied, width `≤ (t_0 + 1)·pw + 1`. The SODA 2021 version had "two serious
errors — in the proof of Theorem 3.1 and in the complexity analysis" (p. 1,
footnote); the TALG version is the corrected one and is the one held.

**The certificate and its exact statement.** `T_0` is the class of connected
graphs; `T_{h+1}` is the class of connected graphs containing three pairwise
disjoint vertex sets `V_1, V_2, V_3` with `G[V_i] ∈ T_h` such that any two of
them can be connected by a path avoiding the third (p. 2 and p. 4). A
`T_h`-witness is the ternary tree of vertex sets recording this recursion
(p. 4); it has `O(n)` nodes, and every graph in `T_h` has at least `3^h`
vertices (p. 4). **Lemma 2.1 (p. 4): `G ∈ T_h ⇒ pw(G) ≥ h`.** The proof is the
three-bags argument: restrict a path decomposition to each `V_i` to get a bag
`B_i` with `|B_i ∩ V_i| ≥ h`; if `B_2` lies between `B_1` and `B_3`, a path
from `B_1 ∩ V_1` to `B_3 ∩ V_3` avoiding `V_2` (connectivity of `G[V_1]`,
`G[V_3]` and the hypothesis) must meet `B_2`, so `|B_2| ≥ h + 1`. Lemma 2.2
(pp. 4–5): `G ∈ T_h` contains a subdivided complete binary tree of height
`h`, computable from the witness. The relation to the better-known
certificate is on p. 2: a subdivided complete binary tree of height `h`
certifies only `pw ≥ ⌈h/2⌉` (Scheffler), and "the following key concept
provides a stronger certificate" — `T_h`.

**Is it a blockage of the branch kind?** Yes, exactly. The `T_{h+1}` step is
`branch_lemma_linked` in `Sandwich.lean` (three disjoint connected branches
of pathwidth `≥ k`, each pair joined by a connected connector missing the
third, giving `k + 1`), and as a blockage it is `Frame.branch` in
`BlockageClass.lean`; the base `T_0` is the order-0 clique frame on any
vertex. So a `T_h`-witness is a frame of order `h` in our class, and the
Lean has the blockage form of what GJNW state only in layout form. Our class
is strictly richer (clique and minor seeds), so its ceiling is at least
GJNW's `h` on every graph.

**The algorithm (§4, pp. 6–15), and whether we could run it.** From the
input tree decomposition it builds a *normalized* one (§4.1, pp. 7–8): nodes
are the connected components of the sets of vertices that live only below a
node of the input tree, bags `B_α = A_α ∪ N(V(α))`, width no larger than the
input's (Lemma 4.3, p. 7). The recursive procedure `solve(G, b)` (§4.2,
pp. 9–13) with an "upper bound request" `b` and memoisation computes, for
each node, the largest `h` among proper descendants and then either (A)
keeps `h` and assembles a path decomposition along the path of the
decomposition tree through the minimal nodes achieving `h` (Lemma 2.3, p. 5,
and Claim 4.6, p. 11), or (B) finds three such nodes pairwise reachable
avoiding each other (a cycle or a degree-3 vertex in the auxiliary graph `H`,
p. 10) and returns `h + 1` with a new witness; the subtle case is "key runs"
where `H` is a path and the parent components between consecutive minimal
nodes must be handled by *secondary* calls on enlarged subgraphs `γ̂`
(pp. 12–13, Claim 4.8). The complexity argument (§4.3, pp. 13–15, Lemmas
4.9–4.10) bounds the number of distinct subproblems by `O(n log n)`. Nothing
in it needs an optimal tree decomposition — any width-`t_0` decomposition
works, with the output width `≤ (t_0 + 1)h + 1` — so the exact elimination
orderings from `learning/treewidth.py` (subset DP to 26, decision search to
64) or min-fill orderings would do as input. **What it would certify at
best**: `h ≤ ⌊log₃ n⌋` from the `3^h` count, i.e. `h ≤ 3` for `n ≤ 80` and
`h ≤ 4` for `n ≤ 242`; and from `pw ≤ (tw + 1)h + 1`, only `h ≥ (pw − 1)/(tw + 1)`,
which on instances with `pw ≤ tw + 2` is `h ≥ 1`. On the open instances
(widths 10–100, `pw` close to `tw`) the value is worthless; the measurement
already exists in substance in `reports/blockage_class.md` §3.3, where the
branch operator improved on the clique terms on 0 of 197 gap instances. The
"non-algorithmic" proof of Theorem 3.1 (pp. 5–6) uses an optimal tree
decomposition in which every `G_{x|y}` is connected (Lemma 3.2, obtained by
lexicographically minimal "fatness", after Bellenbaum–Diestel) and the Helly
property of subtrees — the same Helly tool as `MOSPGraph.lean`.

**The tightness family (§5, pp. 15–16) — the one thing here that bears on
the class's ceiling.** Theorem 5.1: for all `t, h` there is a graph with
`tw = t`, `pw ≥ t(h + 1) − 1` and no subdivided complete binary tree of
height `3·max(h + 1, ⌈log₂ t⌉)`; the graph is `T_h^{(t)}`, the complete
ternary tree of height `h` with each node replaced by `K_t` and each edge by
a perfect matching (p. 15). Claim 5.2 (`tw = t`), Claim 5.3 (`pw ≥
t(h + 1) − 1`, by the strengthened induction "a bag of size `≥ t(h + 1)` *and*
`t` vertex-disjoint paths from the root clique to it", p. 16), Claim 5.4
(the binary-tree count). The remark on p. 15 that the theorem is interesting
only for `h > log₂ t − 2`, since below that BRST's forest theorem already
gives the binary tree, is the published boundary between the two kinds of
certificate. The consequence for our class is §0 item 2: `T_h^{(t)}` is in
the census set, the class's ceiling on it is the treewidth, and Claim 5.3's
proof is the template for a `t`-linked branch operator that would reach
`t(h + 1) − 1`.

**Also in the paper, not used.** Lemma 2.3 (p. 5), the two "combining path
decompositions" lemmas (`pw(G) ≤ ℓ + t` when every component of `G − B_q`, or
of `G` minus the bags along a path of the tree, has pathwidth `≤ ℓ`), which
is the cut lemma of `DegreeBound/` in a different dress; and Conjecture 6.2
(p. 17), treedepth `O(p·ℓ)` for graphs of pathwidth `p` with no path of order
`2^ℓ`.

## §3. Erde (2017)

**What it proves.** Three theorems for directed path-decompositions (a
sequence of bags with the interval property and, for every arc `(x, y)`, `x`
in a bag no later than one containing `y`; p. 2): Theorem 4 (p. 2), the
min-max theorem `dpw(D) ≥ k − 1` iff a diblockage of order `k` exists, via
Theorem 12 (p. 7); Theorem 5 (p. 3), every digraph of directed path-width
`≥ |V(F)| − 1` contains each arborescence forest `F` as a butterfly minor
(§4, pp. 8–9), the directed analogue of BRST (1.1); Theorem 6 (p. 3), every
digraph has a *linked* directed path-decomposition of minimum width, via
Theorem 14 (p. 10), extending Kim & Seymour from semi-complete digraphs, with
a counterexample (Appendix A, p. 12) to Kintali's stronger "lean" claim. The
paper restates BRST's blockage axioms with `≤ k` and "pw `≥ k` iff a blockage
of order `≥ k`" (pp. 1–2).

**The directed blockage.** Separations are pairs `(A, B)`, `A ∪ B = V`, with
no arc from `B ∖ A` to `A ∖ B` (p. 3), ordered as in DO; `S_k` is those of
order `|A ∩ B| < k`. Because a directed separation already has a direction,
an "orientation" is a bipartition `S_k = O⁺ ∪ O⁻` (p. 6): `B` is the large side
when `(A, B) ∈ O⁺`, `A` when `(A, B) ∈ O⁻`. Consistent means `O⁺` is
down-closed and `O⁻` up-closed in `≤` (pp. 6–7). `P_ω` puts `(A, B)` in `O⁺`
when `|A| < ω` and in `O⁻` when `|B| < ω` (p. 7). An **`ω`-diblockage** of `S_k`
(p. 7) is a consistent orientation extending `P_ω` such that `(A, B) ∈ O⁺`,
`(A, B) ≤ (C, D) ∈ O⁻` imply `|B ∩ C| ≥ ω`; a diblockage of order `k` is the
case `ω = k`. On a symmetric digraph this is DO's `F_k^{(2)}`-tangle clause for
clause (the forbidden configuration is the two-star `{(A, B), (D, C)}` with
`|B ∩ C| < ω`), and through DO's Theorem 7.2 (ii)⇒(i) it is a BRST blockage
of order `k − 1` in BRST's `≤` convention.

**Is the min-max proof simpler than BRST's?** Theorem 12 (pp. 7–8): for
`ω ≥ k`, `|V| ≥ k`, exactly one of an `S_k`-path of width `< ω − 1` (a path
decomposition with bags `< ω` and adhesions `< k`) and an `ω`-diblockage of
`S_k`. The proof proves the stronger statement for every consistent partial
orientation `P`: an `(ω, P)`-admissible path (interior bags `< ω`, first
separation in `P⁺ ∪ P_ω⁺`, last in `P⁻ ∪ P_ω⁻`) or an `ω`-diblockage extending
`P`. "Both cannot happen" is six lines (p. 7): the last separation of the
path in `O⁺` is followed by one in `O⁻` with `|A_{j+1} ∩ B_j| < ω`. The
existence is an induction on the number of unoriented separations: if none
is unoriented and `P` is not a diblockage, the violating pair is itself a
two-bag admissible path; otherwise take a `≤`-minimal unoriented `(C, D)` and a
`≤`-maximal unoriented `(E, F)` above a given unoriented separation, orient
`(C, D)` into `P⁺` and `(E, F)` into `P⁻` (both consistent by minimality and
maximality), get two admissible paths by induction, choose `(X, Y)` of
minimum order between `(C, D)` and `(E, F)`, up-shift the first path onto it
and down-shift the second, and glue (p. 8). The ingredients are Lemma 7
(`∧`, `∨` of separations are separations, p. 3), Lemma 8 (an `S`-path is a
path decomposition with bags `A_i ∩ B_{i−1}`, p. 4), Lemma 9 (p. 4), the
equality (2.1) on p. 5, Lemma 10 (shifting onto a linked separation stays in
`S_k`, p. 5) and Lemma 11 (bags do not grow, p. 6). Compared with BRST's
(2.3)–(2.5) (pp. 276–279: simple fractures, the extension lemma for partial
blockages by induction on cardinality, and the assembly of a decomposition
from a simple fracture in `{∅}`), it is about the same length, has fewer
distinct objects (orientations and lists of nested separations), and needs no
normalisation step; the assessment in §0 item 1 stands. One point for a Lean
plan: the whole thing is finite and elementary — no Menger, no compactness —
and the translation lemmas (Lemmas 8–9) are the prefix-union facts
`Blockage.lean` already proves in one direction.

**Could it guide the undirected converse?** Yes, as described: symmetric
digraph, `ω = k`, then DO's half page. The restriction `|V| ≥ k` is harmless
(a graph on fewer than `k` vertices has pathwidth `< k − 1` and no blockage of
that order, since `V` itself would have to be oriented). Nothing in the
paper is specific to the directed case except the asymmetry of `O⁺`/`O⁻`,
which disappears.

**On computing blockages.** Nothing. Theorem 12's proof backtracks over
orientations. Theorem 14's proof (pp. 10–11) is a minimality argument (a
lexicographic order on decompositions by the number and components of edges
of each order, Claims 15–16), also non-constructive in the useful sense.

**Also noted.** Barát's earlier directed blockage (p. 2) gives only the easy
half, and Barát himself doubted the converse for his definition. The
"lean" counterexample (p. 12): the doubled complete binary tree of depth `n`
has `dpw = pw = (n − 1)/2`, and a lean decomposition would make its big bag
well-linked, which forces treewidth `≥ (n + 1)/6` — impossible in a tree. So
"linked" (between bags) is the most one can ask of an optimal path
decomposition; "lean" (within a bag) fails.

## §4. Contradictions and corrections

### 4.1 Appendix F prints the blockage axioms one unit too strict

`paper1/latex/sec9f_appendix_dual.tex` states (i) `α(X) < n`, (ii) `α(Y) < n`,
(iii) `|X_1 ∩ X_2| < n`, Theorem (2.1) as "a blockage of order `n` iff
`pw(G) ≥ n`", and in the proof "a path decomposition of width less than `n`,
so every bag has fewer than `n` vertices". With the paper's and the Lean's
pathwidth (`max |W_i| − 1`), width `< n` means bags of **at most** `n`
vertices, and the axioms that pair with `pw ≥ n` are the `≤ n` ones: BRST
p. 276 (text layer renders `≤` as `<`; their proof of (2.1) on p. 279 bounds
`|(X_{i+1} − X_i) ∪ att(X_i)| ≤ |W_{i+1}| ≤ n`), `Blockage.lean` (`att_card_le :
(att G X).card ≤ n`, header lines 10–14), `reports/blockage_class.md` §1.1
("the `≤ n` reading"), Erde pp. 1–2 (`≤ k`, `pw ≥ k`), DO p. 18 (`< k` for
order `k − 1`, dual to `pw ≥ k − 1`). Witness, enumerated on the path `a–b–c`
(pathwidth 1) over all `2^8` set families: under `≤ n` there are two blockages
of order 1 and none of order 2, as (2.1) says; under the strict `< n` of
Appendix F there are two "blockages of order 2", e.g.
`{∅, {a}, {b}, {c}, {a, b}}` — (i) holds since every member has at most one
attachment, (ii) holds, and the only complementary pairs with
`|X_1 ∩ X_2| < 2` are `(∅, V)`, `({a}, V)`, `({b}, V)`, `({c}, V)` and
`({a, b}, {b, c})`, each with exactly one side in the family. So the strict
reading characterises `pw ≥ n − 1`, and the appendix's displayed theorem is
false as printed while its Lean reference is right. The fix is `<` → `≤` in
(i)–(iii) and in Lemma (2.2) as quoted, and "fewer than `n`" → "at most `n`"
in the proof (the `\leanref{blockage}` then matches). The `check_blockage.py`
enumeration the appendix cites was run on the `≤` axioms (the Lean's), so it
did not see the TeX.

### 4.2 `literature/MISSING.md`'s description of GJNW's certificate

The entry says "Its certificate that `pw ≥ h` is a subdivision of a complete
binary tree of height `h`". GJNW p. 2: a subdivided complete binary tree of
height `h` certifies `pw ≥ ⌈h/2⌉`; the certificate of `pw ≥ h` is the
`T_h`-witness (Lemma 2.1, p. 4), which *implies* a subdivided binary tree of
height `h` (Lemma 2.2). The second half of the entry ("a branching
certificate, the one kind the class contains") is right. `blockage_class.md`
§0's last paragraph has the same shorthand ("certify pathwidth by a
subdivided complete binary tree"); same correction.

### 4.3 Statements in `blockage_class.md` §0 that these papers refine, not contradict

- "The branch operator never fires ... the obstruction to `pw > tw` on small
  graphs is almost never three branches": GJNW's `T_1^{(2)}` is a census graph
  where the obstruction *is* three branches, but `2`-linked ones; the `+1`
  operator cannot see it. The verdict on the stated class stands; the sentence
  "the next class ... has to express 'every small separation has a trivial
  side' at several orders at once" names one route and GJNW's Claim 5.3
  names another (rooted `t`-linkage), and the two are not the same.
- "It is the pathwidth analogue of Bodlaender, Grigoriev & Koster's brambles
  in the only sense available": DO p. 1 would call a bramble a *concrete*
  highly cohesive substructure and a blockage an *abstract* one; the phrase
  "in the only sense available" is accurate given that neither DO nor the
  other two supply a concrete dual object for pathwidth.
- "BRST's own §4 says the same in the vocabulary of stoppages": confirmed, and
  DO's Theorem 7.2 is the published form of the same translation (§1).

## §5. Not done

No Lean was written; the `t`-linked branch lemma of §0 item 2 is a conjecture
with a proof sketch and has not been checked by enumeration, which this
project requires before a statement is made. The value of the class on
`T_h^{(t)}` was taken from the obvious decomposition (`t + h − 1`), not from
the census code, so it is a lower bound on the class's ceiling and the
`(t − 1)h` of §0 item 2 is the gap of that decomposition, not a proved gap of
the class; the only exact point is `T_1^{(2)}`, where the census gives
ceiling 2 = treewidth against pathwidth 3. DO's
companion paper with the proof of Theorem 3.2 (arXiv 1701.02509) and Erde's
"A unified treatment of linked and lean tree-decompositions" (arXiv
1703.03756, cited on p. 10 for the linked definition) are not held; nothing
above depends on them. No search was run, no instance re-solved.
