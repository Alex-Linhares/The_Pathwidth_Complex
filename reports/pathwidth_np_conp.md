# Is a pathwidth lower bound short to check? Pathwidth, NP ∩ coNP, and the size of dual objects

*2026-11-07, one literature session (web search and the PDFs in `literature/`;
six more papers read in a scratch directory and not kept). No solver was run,
nothing under `solutions/` was touched. Context read first:
`reports/blockage_literature.md` §0 and `paper1/latex/sec9f_appendix_dual.tex`
(Appendix F). Page numbers are the papers' own.*

The claim under test, as the brief states it:

> "The statement 'pathwidth(G) ≥ w' is not known to be in NP; in particular, no
> polynomial-size, polynomial-time-checkable certificate of a pathwidth lower
> bound is known for general graphs, and if the blockages of Bienstock,
> Robertson, Seymour & Thomas (1991) (or any other dual object: tangle-like
> orientations, Diestel–Oum's tangle-tree duality) always had a short checkable
> form, PATHWIDTH would be in NP ∩ coNP."

## §0. Verdict: right, and understated in two places; one qualification

**The claim is right.** PATHWIDTH ("is pw(G) ≤ k?", with k part of the input)
is NP-complete; its complement "pw(G) ≥ k + 1" is therefore coNP-complete, and
a coNP-complete problem lies in NP only if NP = coNP. So "pw(G) ≥ w" is not
merely *not known* to be in NP: it is in NP **if and only if NP = coNP**, and a
short checkable form for blockages (or for any other exact dual object) would
not just put PATHWIDTH in NP ∩ coNP, it would collapse NP and coNP. Both
strengthenings are standard complexity theory applied to one NP-completeness
theorem; neither needs a pathwidth paper. The two things to cite are:

- **NP-completeness of pathwidth**: Kashiwabara & Fujisawa (1979), ISCAS,
  in interval-graph form, and Lengauer (1981), *Acta Informatica* 16, 465–475,
  Theorem 7 ("The VSG is NP-complete"), in vertex-separation form; equal to
  pathwidth by Kinnersley (1992). Arnborg, Corneil & Proskurowski (1987) is the
  treewidth theorem and is also what Fomin & Thilikos (2008) cite for
  pathwidth. Monien & Sudborough (1988) sharpen it to planar graphs of
  maximum degree 3. Every survey we hold says the same (Bodlaender 1998;
  Bodlaender 2024: "Each of these three parameters is NP-complete [3,27,41]").
- **The complexity-class consequence**: Garey & Johnson (1979), Chapter 7 (an
  NP-complete problem whose complement is in NP forces NP = co-NP). We hold
  the book only as a scan without a text layer, so the theorem number is not
  checked here.

**Who says it in print, for a width parameter.** For treewidth, Grohe & Marx
(2009, p. 1) say exactly this about brambles: "A bramble of order k + 1 is a
witness that the graph has tree width at least k. However, it is not a good
characterization of tree width in the coNP sense for two reasons: (1) The
number of subgraphs in the bramble is not necessarily polynomial in the size
of the graph and (2) it is NP-hard to determine the order of a bramble. These
problems are hardly surprising: It is NP-complete to decide whether the tree
width of a graph is at most k, thus it seems highly unlikely that tree width
has a coNP characterization." **We found no paper that says the same sentence
for pathwidth and blockages**; the three papers on the dual side of pathwidth
that we hold (Bienstock–Robertson–Seymour–Thomas 1991, Diestel–Oum 2019, Erde
2017) say nothing about the size of a blockage, and Diestel & Oum say in a
footnote that the fast-to-check object in their duality is the tree, not the
tangle.

**Understated, in the other direction, for treewidth.** Grohe & Marx prove
more than the conditional: on bounded-degree expanders every bramble of order
`n^{1/2+ε}` has size `2^{Ω(n^ε)}` — an *unconditional* exponential lower bound
on the size of the exact dual object (Theorem 8(2), p. 6; Hatzel, Komosa,
Pilipczuk & Sorge 2022 sharpen the exponent to `Ω(n^{2δ})` and show it tight).
Nothing of the kind is in print for blockages.

**The qualification: "short certificate" means exact, with k in the input.**
Three things that look like counterexamples are not:

1. *Fixed k.* For every fixed k, "pw(G) ≤ k" is decidable in linear time
   (Bodlaender 1996) and the class is minor-closed with a finite obstruction
   set (Robertson & Seymour), so a minor model of an obstruction is a
   certificate of `pw > k` of size O(n), checkable in polynomial time. This is
   not NP membership for the general problem: the obstruction sets are known
   only for k ≤ 2 (2 graphs for k = 1; 110 for k = 2, Kinnersley & Langston
   1994) and the set for k = 3 "contains at least 122 million elements"
   (Kinnersley & Langston 1994, p. 199, citing Kinnersley's 1989 thesis).
2. *Approximate bounds.* For treewidth, every graph has a polynomial-size,
   easily checked bramble of order `Ω(tw^{1/2}/log² tw)` (Grohe & Marx,
   Theorem 8(1)), and `Ω̃(tw^{1/2})` with congestion 2 (Hatzel et al.,
   Theorem 1.1). For pathwidth, Groenland, Joret, Nadara & Walczak (2023)
   give a polynomial-time computable, polynomial-size certificate of
   `pw ≥ h` whenever `pw ≥ (t_0 + 1)h + 2` for a tree decomposition of width
   `t_0` in hand, and their Theorem 1.1 with Scheffler's binary-tree theorem
   and Grohe–Marx's brambles yields (our arithmetic, §2.4 below, not a
   statement in print) a polynomial-size certificate of
   `pw ≥ Ω(pw^{1/4}/log² pw)` for every graph. So the "no short certificate"
   claim is about *exact* lower bounds, and about lower bounds within a
   constant of the optimum; it is false for polynomial approximations.
3. *The upper-bound side.* A path decomposition is the short certificate of
   `pw ≤ k`; for the search games, monotonicity (LaPaugh; Kirousis &
   Papadimitriou) is precisely what makes the searchers' strategy short and
   puts the search number in NP (Megiddo et al. 1988, p. 20 and p. 42;
   Kirousis & Papadimitriou 1986, p. 212; Fomin & Thilikos 2008). Nobody
   claims the fugitive's side is short: in BRST's (5.1) the fugitive's winning
   strategy against n searchers is, exactly, a blockage of order n, and Fomin
   & Thilikos call brambles "certificates of escaping strategies" and
   blockages their invisible-fugitive analogue, with no size statement.

**What to write in Appendix F** is in §7: the complement is coNP-complete, so
no blockage class with a polynomial-size, polynomial-time-checkable member on
every graph can exist unless NP = coNP; the exact dual object for treewidth
is provably exponential on expanders; what *is* available in polynomial size
is a root-of-the-width approximation; and the project's minor certificates
are a fixed-H instance of the obstruction principle, which Tamaki (2022)
uses in the same way for treewidth.

## §1. Item 1: NP-completeness, and the coNP side

### 1.1 The standard citations, checked

**Treewidth.** Arnborg, S., Corneil, D. G. & Proskurowski, A. (1987).
Complexity of finding embeddings in a k-tree. *SIAM Journal on Algebraic and
Discrete Methods*, 8(2), 277–284. DOI 10.1137/0608024. Not held; cited for
"Treewidth is NP-complete" by every source below, and the simple 2023 proof
(Bodlaender, Bonnet, Jaffke, Knop, Lima, Milanič, Ordyniak, Pandey & Suchý,
*Treewidth is NP-complete on cubic graphs*, IPEC 2023, arXiv 2301.10031) says
its reduction "also gives NP-completeness on co-bipartite graphs".

**Pathwidth.** Three independent proofs, under three names, all 1979–1988:

- Kashiwabara, T. & Fujisawa, T. (1979), *Proceedings of the IEEE
  International Symposium on Circuits and Systems* (ISCAS 1979). Two titles
  circulate and both appear to be real ISCAS 1979 entries: "An NP-complete
  problem on interval graphs", pp. 82–83 (as cited by Bodlaender 2024, ref.
  27) and "NP-completeness of the problem of finding a minimum-clique-number
  interval graph containing a given graph as a subgraph", pp. 657–660 (as
  cited by Kobayashi, Komuro & Tamaki 2014, ref. 12, and by the arXiv
  reference list that lists both). The interval-graph form is pathwidth:
  the least clique number of an interval supergraph is `pw + 1`. Neither is
  held; the 1979 paper we hold under Kashiwabara's name (Ohtsuki, Mori, Kuh,
  Kashiwabara & Fujisawa, *One-dimensional logic gate assignment and interval
  graphs*, IEEE Trans. Circuits and Systems) is the companion that states the
  augmentation problem and says it "turns out to be an NP-complete problem".
- Lengauer, T. (1981). Black-white pebbles and graph separation. *Acta
  Informatica*, 16, 465–475. Held. Defines the vertex separator game (VSG)
  and proves **Theorem 7, "The VSG is NP-complete"** (p. 472), by reduction
  from a modified min-cut linear arrangement; the abstract: "As an application
  of this result both games are shown to be NP-complete." VSG is vertex
  separation, which equals pathwidth (Kinnersley 1992, held).
- Monien, B. & Sudborough, I. H. (1988). Min cut is NP-complete for edge
  weighted trees. *Theoretical Computer Science*, 58(1–3), 209–229. DOI
  10.1016/0304-3975(88)90028-X. Not held. Bodlaender, Bonnet et al. (2023,
  §2) state it as "Theorem 2.4 (Monien and Sudborough [6]). Pathwidth is
  NP-complete on planar graphs with maximum degree at most 3", obtained from
  "Vertex Separation Number is NP-complete on planar graphs with maximum
  degree at most 3" and the Kinnersley equality.
- The game form: Kirousis, L. M. & Papadimitriou, C. H. (1986). Searching and
  pebbling. *Theoretical Computer Science*, 47, 205–218. Held. **Corollary
  2.6** (p. 212): "The problem of deciding, given a graph G and an integer k,
  whether ns(G) ≤ k is NP-complete", by reduction from edge searching
  (Megiddo et al.), with `ns(G) = pw(G) + 1` (their earlier note, Kirousis &
  Papadimitriou 1985, *Discrete Mathematics* 55, 181–184, is BRST's ref. 2).
  BRST (1991, p. 282) write: "It seems remarkable to us that a minimax
  formula like (2.1) for an NP-hard invariant like path-width [3] could be
  of any real use", with [3] = Kirousis & Papadimitriou 1986.

Gate matrix layout (the MOSP form) is NP-complete by Kashiwabara & Fujisawa's
interval-graph result; Kinnersley & Langston (1994, abstract) call it "a
well-known NP-complete problem".

### 1.2 The coNP side: what follows, and who states it

Nothing specific to pathwidth is needed, and nothing specific was found. The
chain is: PATHWIDTH is NP-complete; the complement of an NP-complete problem
is coNP-complete; a coNP-complete problem is in NP iff NP = coNP (and then
NP = coNP, since the classes are complementary). Garey & Johnson (1979),
Chapter 7 ("Beyond NP-completeness"), is the textbook statement; we did not
verify the theorem number against the held scan, which has no text layer.

Consequences the brief asks about, with their status:

- "Is PATHWIDTH, or its complement, in coNP / NP ∩ coNP?" — The complement
  is coNP-complete (immediate). PATHWIDTH is in coNP iff NP = coNP (immediate).
  No paper is needed, and no paper on pathwidth says it in these words that
  we could find.
- "Does any paper state explicitly that pathwidth / treewidth lower bounds
  have no short certificates unless NP = coNP?" — For treewidth, **yes**:
  Grohe & Marx (2009), quoted in §0. We found the same reasoning repeated,
  in weaker form, by Kreutzer & Tazari (2010, p. 1: "a bramble of large order
  is a witness for large treewidth"; brambles "can look quite complex") and
  by Bodlaender, Grigoriev & Koster (2008, §1: "determining the order of a
  bramble, is also NP-hard; it follows directly from the NP-hardness of the
  minimum hitting set problem [21] by taking a complete graph G and the
  collection of subsets as the bramble"). For pathwidth, **no**: not in
  BRST, Diestel–Oum, Erde, Fomin–Thilikos, Bodlaender 1998 or Bodlaender
  2024. The honest sentence is "we found no statement of it for pathwidth".

The searches also turned up the kernelization results, which are a different
question (preprocessing size, not certificate size) under a different
hypothesis (NP ⊆ coNP/poly, a collapse of the polynomial hierarchy to its
third level): Bodlaender, Jansen & Kratsch, *Preprocessing for treewidth: a
combinatorial analysis through kernelization* (SIAM J. Discrete Math. 2013,
arXiv 1104.4217) and *Kernel bounds for structural parameterizations of
pathwidth* (SWAT 2012, arXiv 1207.4900). Not to be cited for certificates.

## §2. Item 2: the size of brambles, and what exists for pathwidth

### 2.1 Grohe & Marx, exact statement

Grohe, M. & Marx, D. (2009). On tree width, bramble size, and expansion.
*Journal of Combinatorial Theory, Series B*, 99(1), 218–228. DOI
10.1016/j.jctb.2008.06.004. No arXiv version; the June 2008 preprint is open
at Marx's page (`cs.bme.hu/~dmarx/papers/grohe-marx-brambles.pdf`) and at
RWTH; page numbers below are the preprint's.

Abstract, verbatim: "We prove that every graph of tree width at least k has
a bramble of order Ω(k^{1/2}/log² k) and size polynomial in n and k, and that
for every k there is a graph G of tree width Ω(k) such that every bramble of
G of order k^{1/2+ε} has size exponential in n."

**Theorem 8** (p. 6), verbatim:

> (1) Every n-vertex graph G of tree width k has a bramble of order
> Ω(k^{1/2}/log² k) and size O(k^{3/2} · ln n).
>
> (2) There is a family (G_k)_{k≥1} of graphs such that:
> • |V(G_k)| = O(k) and |E(G_k)| = O(k) for every k ≥ 1;
> • tw(G_k) ≥ k for every k ≥ 1;
> • for every ε > 0 and k ≥ 1, every bramble of G_k of order at least
>   k^{1/2+ε} has size at least 2^{Ω(k^ε)};
> • in every bramble of G_k, the ratio of the size and the depth is O(k^{1/2}).

So the brief's recollection is right in shape and the constants are: order
`Ω(k^{1/2}/log² k)` with size `O(k^{3/2} ln n)` on the positive side; order
`k^{1/2+ε}` forces size `2^{Ω(k^ε)}` on the negative side, on bounded-degree
expanders (Lemma 16, p. 9: a bramble of order `> c·n^{1/2+ε}` in an n-vertex
graph of maximum degree d has size `≥ exp(c·n^ε/(d+1))`). Hatzel et al.
(2022, footnote (i)) note that "a slightly more careful analysis of their
calculations shows a lower bound of Ω(n^{2δ}) in the exponent".

Three sentences from the introduction matter for Appendix F:

- "It is a fairly straightforward consequence of the graph minor theorem [7]
  that there is a function f such that every graph of tree width at least k
  has a bramble of order k + 1 and cardinality f(k). We raise as an open
  question whether f can be bounded from above by an exponential function of
  k." (p. 1) — the size of an *exact* bramble depends on k alone, by
  minor-closure; what is open is the growth of f.
- "In summary, every graph with tree width at least k has a polynomial-size
  bramble that certifies in an easily verifiable way that the tree width is
  Ω(k^{1/2}/log² k), thus avoiding both problems (1) and (2) above. However,
  in general, brambles witnessing that the tree width is Ω(k^{1/2+ε}) run
  into these problems." (p. 2) — "easily verifiable" because the order is
  bounded below by size/depth, which is read off the bramble.
- "The negative results of the current paper show that brambles cannot be
  used directly in these applications." (p. 2)

### 2.2 The follow-ups

- Hatzel, M., Komosa, P., Pilipczuk, M. & Sorge, M. (2022). Constant
  congestion brambles. *Discrete Mathematics & Theoretical Computer Science*,
  24:1, #6. arXiv 2008.02133 (open). **Theorem 1.1**: "There exists a
  polynomial p(·) such that for every positive integer k and every graph G
  of treewidth at least k the graph G contains a bramble of order at least
  √k/p(log k) and congestion 2" (so size linear in the order; the order is
  at least half the size, read off directly). **Theorem 1.2**: "for every
  constant δ ∈ (0, 0.5] and every integer k, every graph G of treewidth at
  least k contains a bramble of order at least k^{0.5+δ}/p(log k) and with
  at most 2^{k^{2δ}·p(log k)} elements" — the matching upper bound to
  Grohe–Marx's exponential lower bound, "tight up to polylogarithmic
  factors".
- Kreutzer, S. & Tazari, S. (2010). On brambles, grid-like minors, and
  parameterized intractability of monadic second-order logic. SODA 2010;
  arXiv 0907.3076 (open). "We provide the first polynomial-time algorithm to
  compute a bramble that is guaranteed to have the order of the square-root
  of the treewidth, up to log-factors" (p. 2); Theorem 2.3 there restates
  Grohe–Marx as "if we are looking for a polynomial-sized bramble, the best
  order we can hope for is about the square-root of the treewidth".
- Chekuri, C. & Chuzhoy, J. (2016). Polynomial bounds for the grid-minor
  theorem. *J. ACM* 63(5), 40 (STOC 2014); arXiv 1305.6577. A grid minor of
  side `k` is a polynomial-size, polynomial-time-checkable certificate of
  `tw ≥ k`, and every graph of treewidth `k^{O(1)}` has one; this is the
  "polynomial excluded-minor approximation" that Kawarabayashi & Rossman
  (2018) name Theorem 1.1.

### 2.3 Pathwidth: blockages, tangles, and what is in print

**Blockage size: nothing.** BRST (1991) prove the min-max theorem (2.1) and
its search-game corollary (5.1) and say nothing about how many sets a
blockage contains. Diestel & Oum (2019, footnote 1, p. 3): "We make no claim
here as to how fast such a witness might be computable, only that checking
it will be fast. This is because such a check involves only linearly many
separations. Exploring the F-tangle-tree theorem from an algorithmic point of
view is a problem we would indeed like to see tackled." — and the witness
meant is the *tree* (the upper-bound side), as `reports/blockage_literature.md`
§0 item 6 already records. Erde (2017) is silent on size. **We found no
published bound, upper or lower, on the size of a blockage of order n**, and
no pathwidth analogue of Grohe–Marx.

**Tangles.** Grohe, M. & Schweitzer, P. (2016). Computing with tangles.
*SIAM J. Discrete Math.* 30(2), 1213–1247 (STOC 2015); arXiv 1503.00190
(open). Abstract: "it is unclear how to represent them, because they are
families of separations and as such may be exponentially large"; their data
structure and membership oracle run in time `n^{O(k)}` (§6, p. 36: "The
running time of all of our algorithms is n^{O(k)}, where k is the order of
the tangles"). Two later results give a tangle a *short description* without
giving it a short *check*:

- Elbracht, C., Kneip, J. & Teegen, M. (2020). Tangles are decided by
  weighted vertex sets. *Advances in Combinatorics* 2020:9; arXiv 1811.06821
  (open). (The brief's "Diestel, Elbracht & Jacobs" is a different paper;
  Diestel posed the question this one answers.) **Theorem 2**: "Let G = (V,E)
  be a finite graph and τ a k-tangle in G. Then there exists a function
  w : V → ℕ such that a separation (A,B) of G of order < k lies in τ if and
  only if w(A) < w(B)."
- Seibt, A. (2025). Witnessing and guiding sets of tangles. arXiv
  2507.04394 (open). **Theorem 1**: every k-tangle of a separation system
  with a submodular order function "has a witnessing set of size at most
  (3^k − 1)/2", improving Grohe & Schweitzer's tower-type bound; sharpness
  is discussed in its §3.3.

A weight function or a witnessing set is polynomial in size, but verifying
that the orientation it induces is a tangle still ranges over all separations
of order < k — `n^{O(k)}` of them — so these are compact *descriptions* of an
XP-checkable object, not NP-style certificates with k in the input. For
pathwidth the corresponding orientation object is Diestel & Oum's
`F_k^{(2)}`-tangle (their Theorem 7.2), with the same caveat.

**The certificate that is in print for pathwidth** is Groenland, Joret,
Nadara & Walczak (2023), TALG 19(2), art. 16; arXiv 2008.00779, held. Abstract:
"it computes in polynomial time an integer h, a certificate that G has
pathwidth at least h, and a path decomposition of G of width at most
(t_0 + 1)h + 1. The certificate is closely related to (and implies) the
existence of a subdivision of a complete binary tree of height h." The
certificate is the `T_h`-witness (their §2.2, "Witnesses for Large
Pathwidth"), a ternary tree of vertex sets with O(n) nodes; its Lemma 2.1 is
the branch lemma Appendix F already uses. And their **Theorem 1.1**: "Every
graph with treewidth t−1 has pathwidth at most th+1 or contains a subdivision
of a complete binary tree of height h+1", with "The bound th + 1 is best
possible up to a multiplicative constant". They note this "implies (with
c = 2)" Kawarabayashi & Rossman's Conjecture 8.1, the "Polynomial Grid/Tree-
Minor Theorem for Pathwidth": "There is an absolute constant c such that
every graph with pathwidth ≥ k^c has one of the following minors: the k × k
grid, the complete binary tree of height k" (Kawarabayashi & Rossman, SODA
2018, §8; journal version *J. Eur. Math. Soc.* 2022). So that conjecture is
settled, and it is a polynomial-size-certificate statement: a grid minor
model or a binary-tree subdivision has polynomial size and is checked in
polynomial time.

### 2.4 A corollary we draw (not in print as such)

Put together, for every graph with `p = pw(G)`: take `t = h = ⌊√(p − 2)⌋`
in GJNW's Theorem 1.1. Either `tw(G) ≥ t`, and Grohe–Marx (or Hatzel et al.)
give a polynomial-size, easily checked bramble of order `Ω(t^{1/2}/log² t) =
Ω(p^{1/4}/log² p)`, which bounds `pw ≥ tw` from below; or G contains a
subdivision of the complete binary tree of height `h + 1`, which certifies
`pw ≥ ⌈(h+1)/2⌉ ≈ √p/2` (the pathwidth of the complete binary tree of depth k
is ⌈k/2⌉, Scheffler, as Bodlaender 1998 Theorem 67; subgraphs do not increase
pathwidth). Hence **every graph has a polynomial-size, polynomial-time-
checkable certificate that `pw ≥ Ω(pw^{1/4}/log² pw)`**, while a certificate
of `pw ≥ pw` exactly exists for all graphs only if NP = coNP. Whether the
exponent 1/4 can be raised to 1/2 (the treewidth value) or beyond, and
whether blockages themselves must be exponential on some family in the way
brambles must, are open as far as we found. This paragraph is our
arithmetic on three published theorems; cite the theorems, not the
paragraph.

## §3. Item 3: fixed k, obstruction sets, minor certificates

- **Linear time for fixed k**: Bodlaender, H. L. (1996). A linear-time
  algorithm for finding tree-decompositions of small treewidth. *SIAM J.
  Comput.* 25(6), 1305–1317; the constructive pathwidth version is
  Bodlaender & Kloks (1996), *J. Algorithms* 21, 358–402 (held), and the
  small-width practical one is Cattell, Dinneen & Fellows (1996), IPL (held).
- **Finite obstruction sets**: Robertson & Seymour, Graph Minors XX (JCTB 92,
  2004) for finiteness; Graph Minors XIII (JCTB 63, 1995) for the `O(n^3)`
  minor test. The nonconstructive consequence for gate matrix layout is
  Fellows & Langston (1987, 1989), held.
- **What is known**: `pw ≤ 1`: two obstructions (the triangle and the
  "spoke" `S(3,2)`, the tree with three paths of length two from one
  vertex). `pw ≤ 2`: Kinnersley, N. G. & Langston, M. A. (1994). Obstruction
  set isolation for the gate matrix layout problem. *Discrete Applied
  Mathematics*, 54, 169–213 (held): "a proof that the obstruction set for
  three tracks contains exactly 110 elements" (abstract). `pw ≤ 3`:
  unknown; "the basis for parameter value four contains at least 122 million
  elements [12]", ref. [12] being Kinnersley's PhD thesis (*Obstruction set
  isolation for layout permutation problems*, Washington State University,
  1989), and the authors add that this "suggest[s] that no other bases for
  this problem are likely to be isolated in the foreseeable future" (p. 199).
  Ding, G. & Dziobiak, S. (2013). On 3-connected graphs of path-width at most
  three. *SIAM J. Discrete Math.* 27(3), 1514–1526, DOI 10.1137/100800452,
  repeat the 122 million figure and give five excluded minors for the
  3-connected case. The acyclic obstructions are known for every k:
  Takahashi, A., Ueno, S. & Kajitani, Y. (1994). Minimal acyclic forbidden
  minors for the family of graphs with bounded path-width. *Discrete
  Mathematics*, 127, 293–304. (For treewidth the picture is the same one
  step later: four obstructions for `tw ≤ 3`, Arnborg, Proskurowski &
  Corneil 1990, *Discrete Math.* 80, 1–19; `tw ≤ 4` unknown.)
- **Why this is not NP membership**: the certificate "a minor model of some
  obstruction for k" is short and checkable for each fixed k, but the
  obstruction sets are not known beyond k = 2 and their size grows at least
  like the 2 / 110 / ≥ 1.22 × 10^8 sequence, so there is no uniform,
  polynomial-time checker that takes k as input. Grohe & Marx make the same
  point for brambles (the function f(k) from the graph minor theorem, §2.1).
- **The minor-certificate principle** — any minor H with `pw(H) ≥ n` certifies
  `pw(G) ≥ n`, with the model as the proof — is used as a certificate scheme,
  in so many words, by Tamaki (2022) for treewidth: his solver "attaches a
  compact certificate to the lower bound it computes" (abstract), the
  certificate being a minor ("we record this new lower bound tw(G_{i*}/F)
  together with the minor ... of G certifying it", §5), and "The certificates
  of the lower bounds computed by our algorithm are small and easily
  verified. ... The maximum of nc(G) over these instances is 49 and the time
  for verifying each certificate is at most 400 milliseconds" (§6). Note what
  "verified" means there: an exact algorithm (Bouchitté–Todinca) is run on
  the small minor, so the check trusts a solver on ≤ 49 vertices, not a proof
  log. Bodlaender & Koster (2011, §5 "Taking minors") and Bodlaender, Wolle &
  Koster (2006, contraction degeneracy; held) are the earlier use of minors
  as treewidth lower bounds, without the word "certificate". For pathwidth,
  the tree-minor form is BRST (1.1) itself (a forest F as a minor is forced by
  `pw ≥ |V(F)| − 1`, the converse direction giving only `pw ≥ pw(F)`), and
  GJNW's binary-tree subdivision (§2.3) is the certificate they name.

## §4. Item 4: computational verification of lower bounds

- **PACE accepts only upper bounds.** Confirmed for both treewidth
  iterations. PACE 2017 (Dell, H., Komusiewicz, C., Talmon, N. & Weller, M.,
  *The PACE 2017 Parameterized Algorithms and Computational Experiments
  Challenge: The Second Iteration*, IPEC 2017, LIPIcs 89, 30:1–30:12, DOI
  10.4230/LIPIcs.IPEC.2017.30): "Exact competition: Compute a tree-
  decomposition of minimum width. You have 30 minutes per instance. Win by
  solving more instances than the other participants." (§2). The challenge
  page (`pacechallenge.org/2017/treewidth/`) says the validator "verifies that
  a given tree decomposition ... is indeed a valid tree decomposition of a
  given graph", that a submission is disqualified if it "produces a solution
  that is known to be non-optimal", and nowhere says how the minimum width of
  a secret instance was established; the repository README
  (`github.com/PACE-challenge/Treewidth`) describes `td-validate` the same
  way and an autotester over "all graphs with min-degree 3 and at most 8
  vertices". The report itself does not describe any optimality check for
  Track A. PACE 2016 (Dell, Husfeldt, Jansen, Kaski, Komusiewicz & Rosamond,
  IPEC 2016, LIPIcs 63, 30:1–30:9, DOI 10.4230/LIPIcs.IPEC.2016.30) likewise
  describes validity checking only for treewidth (and notes that the SAGE
  implementation "can produce non-optimal solutions"); the only precomputed
  optima it mentions are for the feedback-vertex-set track, by an ILP. So the
  challenge's notion of "exact" rests on agreement between solvers and
  organiser-held reference values, with no lower-bound certificate asked
  for or checked.
- **Certified lower bounds, treewidth.** Bodlaender, H. L., Grigoriev, A. &
  Koster, A. M. C. A. (2008). Treewidth lower bounds with brambles.
  *Algorithmica*, 51(1), 81–98 (ESA 2005; TR UU-CS-2005-051 held): a bramble
  is a certificate of `tw ≥ order − 1` (their Corollary 1.5), but "determining
  the order of a bramble, is also NP-hard", so the certificate is the bramble
  plus a hitting-set argument, and their constructions are for planar-like
  graphs. Bodlaender & Koster (2011), *Treewidth computations II. Lower
  bounds*, *Information and Computation* 209(7), 1103–1119 (TR UU-CS-2010-022
  held): the survey of every lower-bound family (degree-based, minors,
  spectral, MCS, improved graphs, brambles, §§3–10); each bound comes with
  the object that proves it, and no section discusses certificate size or
  proof logging. Koster, Wolle & Bodlaender (2005), *Degree-based treewidth
  lower bounds*, WEA 2005, LNCS 3503, 101–112 (TR held). Tamaki (2022), SEA
  2022, LIPIcs 233, arXiv 2202.07793: the one solver we found that *ships*
  a lower-bound certificate (§3 above). The paper the brief half-remembers
  as "Hein & Koster, an experimental evaluation of treewidth lower bounds" is
  Hein, A. & Koster, A. M. C. A. (2011), *An experimental evaluation of
  treewidth at most four reductions*, SEA 2011, LNCS 6630, 218–229, DOI
  10.1007/978-3-642-20662-7_19 — reduction rules, not lower bounds; not
  relevant.
- **LP / SDP duals.** We found no treewidth or pathwidth lower bound that is
  certified by an LP or SDP dual solution. Linear and semidefinite programs
  enter the literature on the *construction* side (Grohe & Marx use Feige,
  Hajiaghayi & Lee's LP for balanced separators to build their bramble;
  Kreutzer & Tazari likewise), and the certificate is the bramble, not the
  dual.
- **SAT with proof logging.** SAT encodings of treewidth exist (Samer, M. &
  Veith, H., *Encoding treewidth into SAT*, SAT 2009, LNCS 5584, 45–50; Berg,
  J. & Järvisalo, M., *SAT-based approaches to treewidth computation: an
  evaluation*, ICTAI 2014; Jdrasil, Bannach, Berndt & Ehlers, SEA 2017, third
  in PACE 2017's exact track) and are used to *refute* `tw ≤ k`, but **we
  found no published treewidth or pathwidth lower bound shipped with a
  DRAT (or other) proof checked by an independent checker**. The project's
  `learning/proofs.py` (DRAT refutations of `optimum − 1` checked by
  drat-trim) and `paper1/obstruction_check.py` are, as far as this search
  reaches, without a published precedent for pathwidth; say "we found no
  prior report", not "first".

## §5. Item 5: the search games and the fugitive's strategy

- **Node search number = pw + 1**: Kirousis & Papadimitriou (1985, 1986);
  BRST (5.1) (p. 282) proves from (2.1) that the following are equivalent:
  "(i) there is a successful search (X_1, ..., X_m) in G with each |X_i| ≤ n;
  (ii) there is no blockage in G of order n; (iii) G has path-width ≤ n − 1;
  (iv) there is a monotone successful search ... with each |X_i| ≤ n".
- **The searchers' side is short because of monotonicity.** Megiddo, N.,
  Hakimi, S. L., Garey, M. R., Johnson, D. S. & Papadimitriou, C. H. (1988).
  The complexity of searching a graph. *J. ACM*, 35(1), 18–44 (held), p. 20:
  "It follows from this result [LaPaugh's] that the decision problem belongs
  to NP. One need only guess the sequence in which the edges are cleared,
  from which it is straightforward to check whether or not that sequence can
  be achieved using K or fewer searchers." and p. 42: "LaPaugh [6] has proved
  that 'recontamination' does not help, and hence the problem of determining
  the search number is in NP." Kirousis & Papadimitriou (1986, p. 212): "The
  fact that node-searching is in NP follows from Theorem 2.3 since a
  recontamination-free strategy can be exhibited and proved to be a strategy
  in polynomial time." Fomin, F. V. & Thilikos, D. M. (2008). An annotated
  bibliography on guaranteed graph searching. *Theoretical Computer Science*,
  399(3), 236–245 (read in the GRASTA 2009 booklet reprint, pp. 11–12):
  "Clearly, the monotonicity property can gives us information on the
  complexity of a graph searching problem as it provides a polynomial space
  certificate for proving membership in NP (we just consider only monotone
  strategies)." LaPaugh's theorem is LaPaugh, A. S. (1993), Recontamination
  does not help to search a graph, *J. ACM* 40(2), 224–245 (1982 technical
  report).
- **The fugitive's side is never argued to be short.** Fomin & Thilikos
  (same page): Seymour & Thomas's monotonicity proof for the visible fugitive
  "was based on the introduction of screens (also known as brambles) as
  certificates of escaping strategies. The analogue of these structures for
  the invisible fugitive case was introduced in [22] (called blockages)",
  [22] = BRST 1991. That is the whole of what the bibliography says about the
  fugitive's certificate; no size is mentioned anywhere in it, in BRST, in
  Megiddo et al. (whose §5 lists open problems and does not raise it), in
  Kirousis & Papadimitriou, or in Diestel & Oum. By (5.1)(i)⇔(ii) the
  fugitive's winning strategy against n searchers *is* a blockage of order
  n, so a short fugitive strategy would be a short blockage, with the
  consequence of §0. For the visible game the escape strategy is the bramble
  (or Seymour & Thomas's haven), and Grohe & Marx's Theorem 8(2) says it can
  be forced to exponential size. We found no author who claims the
  fugitive's strategy is short, and one (Grohe & Marx) who proves it is not,
  for treewidth.

## §6. Dead ends and corrections

- The arXiv identifier 0907.3076 that a search offered for Grohe & Marx is
  Kreutzer & Tazari; Grohe & Marx has no arXiv version.
- "Diestel, Elbracht & Jacobs, Tangles are decided by weighted vertex sets"
  does not exist under those authors; the paper is Elbracht, Kneip & Teegen
  (2020). Seibt (2025) cites a different Diestel–Elbracht–Jacobs paper for
  guiding functions.
- Grohe's survey *Tangled up in blue* (arXiv 1605.06704) was not reached by
  the searches; nothing in this report depends on it.
- The held Garey & Johnson is a 175-page two-up scan without a text layer and
  no OCR tool is installed; the Chapter 7 theorem number is unchecked.
- Kashiwabara & Fujisawa (1979): two ISCAS titles are in circulation (§1.1);
  both may be real. Whichever is cited, give the page numbers with it.

## §7. What to cite in Appendix F, and the sentences we may safely write

Safe, with the citations in brackets:

1. "Deciding `pw(G) ≤ k` is NP-complete [Kashiwabara & Fujisawa 1979;
   Lengauer 1981, Theorem 7; Arnborg, Corneil & Proskurowski 1987 via
   Kinnersley 1992], so `pw(G) ≥ k + 1` is coNP-complete, and a polynomial-
   size, polynomial-time-checkable certificate of it on every graph would give
   NP = coNP [Garey & Johnson 1979, Chapter 7]."
2. "A blockage is the fugitive's winning strategy in the invisible-fugitive
   node search game [BRST 1991, (5.1)], as a bramble is the robber's in the
   visible game [Seymour & Thomas 1993; Fomin & Thilikos 2008]. Monotonicity
   makes the searchers' strategy short and puts the search number in NP
   [Megiddo et al. 1988; Kirousis & Papadimitriou 1986]; no such statement
   exists for the fugitive's side, and by (1) none can, in general, unless
   NP = coNP."
3. "For treewidth the exact dual object is provably large: on bounded-degree
   expanders every bramble of order `n^{1/2+ε}` has size `2^{Ω(n^ε)}`
   [Grohe & Marx 2009, Theorem 8(2)], while brambles of order
   `Ω(tw^{1/2}/log² tw)` and polynomial size always exist [Theorem 8(1);
   Hatzel et al. 2022, Theorem 1.1, with congestion 2]. We found no
   statement, upper or lower, about the size of a blockage; Diestel & Oum
   [2019, footnote 1] note that the fast-to-check witness in their duality
   is the tree, not the tangle."
4. "For every fixed k a minor model of an obstruction certifies `pw > k` in
   polynomial size; the obstruction sets are known for k ≤ 2 only (2 and 110
   graphs) and the set for k = 3 has at least 122 million members
   [Kinnersley & Langston 1994, p. 199]. The minor certificates of
   Section 5 and Appendix [tabu] are this principle with a chosen H; Tamaki
   [2022] ships treewidth lower bounds the same way."
5. "Polynomial-size certificates of a *polynomial approximation* exist for
   pathwidth: a grid minor or a subdivided complete binary tree [GJNW 2023,
   Theorem 1.1, settling Kawarabayashi & Rossman's Conjecture 8.1]; the
   `T_h`-witness of GJNW is one, computable in polynomial time from a tree
   decomposition."
6. "We found no published pathwidth or treewidth lower bound accompanied by
   a proof object checked by an independent tool; PACE's validators check
   decompositions only [Dell et al. 2017, 2016]."

Do not write: "pathwidth is not in coNP" (unknown, equivalent to NP ≠ coNP);
"blockages must be exponential" (not proved; the treewidth result does not
transfer); "first certificate" of anything; "the fugitive's strategy is
exponential" (not in print).

## §8. PDFs worth obtaining (open links where they exist)

Not downloaded into `literature/`. Six were read from a scratch directory
and discarded (marked *read*).

- Grohe & Marx (2009), JCTB 99(1), 218–228, DOI 10.1016/j.jctb.2008.06.004.
  Open preprint: `https://www.cs.bme.hu/~dmarx/papers/grohe-marx-brambles.pdf`.
  *Read.* The key reference.
- Hatzel, Komosa, Pilipczuk & Sorge (2022), DMTCS 24:1 #6, arXiv 2008.02133.
  *Read.*
- Kreutzer & Tazari (2010), SODA, arXiv 0907.3076. *Read.*
- Seymour & Thomas (1993), JCTB 58, 22–33, DOI 10.1006/jctb.1993.1027. Not
  open; the bramble / haven definitions and the min-max theorem.
- Chekuri & Chuzhoy (2016), J. ACM 63(5), arXiv 1305.6577.
- Kawarabayashi & Rossman (2018/2022), SODA 2018; JEMS; open at
  `https://www.math.utoronto.ca/rossman/treedepth.pdf`. *Read.*
- Tamaki (2022), SEA 2022, arXiv 2202.07793. *Read.* The shipped minor
  certificate.
- Grohe & Schweitzer (2016), SIDMA 30(2), arXiv 1503.00190. *Read.*
- Elbracht, Kneip & Teegen (2020), Advances in Combinatorics 2020:9, arXiv
  1811.06821. *Read.*
- Seibt (2025), arXiv 2507.04394. *Read.*
- Arnborg, Corneil & Proskurowski (1987), SIAM J. Alg. Disc. Meth. 8(2),
  277–284, DOI 10.1137/0608024. Not open.
- Monien & Sudborough (1988), TCS 58, 209–229, DOI
  10.1016/0304-3975(88)90028-X (Elsevier open archive).
- Kashiwabara & Fujisawa (1979), ISCAS, pp. 82–83 and/or pp. 657–660. IEEE;
  not open.
- Bodlaender, Bonnet et al. (2023), IPEC 2023, arXiv 2301.10031. *Read.*
- Ding & Dziobiak (2013), SIDMA 27(3), DOI 10.1137/100800452; open preprint
  `https://www.math.lsu.edu/~ding/pathwidth.pdf`.
- Takahashi, Ueno & Kajitani (1994), Discrete Math. 127, 293–304 (Elsevier
  open archive).
- Kinnersley (1989), PhD thesis, Washington State University (the 122 million
  count). Not located online.
- Fomin & Thilikos (2008), TCS 399(3), 236–245; open reprint in the GRASTA
  2009 booklet, `https://kam.mff.cuni.cz/kamserie/clanky/2009/s939.pdf`
  (pp. 10–13 of the booklet). *Read.*
- LaPaugh (1993), J. ACM 40(2), 224–245, DOI 10.1145/151261.151263.
- Bodlaender (1996), SIAM J. Comput. 25(6), 1305–1317, DOI
  10.1137/S0097539793251219.
- Dell, Komusiewicz, Talmon & Weller (2017), IPEC 2017, LIPIcs 89, 30, DOI
  10.4230/LIPIcs.IPEC.2017.30 (open). *Read.*
- Dell, Husfeldt, Jansen, Kaski, Komusiewicz & Rosamond (2016), IPEC 2016,
  LIPIcs 63, 30, DOI 10.4230/LIPIcs.IPEC.2016.30 (open). *Read.*
- Bodlaender, Grigoriev & Koster (2008), Algorithmica 51(1), 81–98, DOI
  10.1007/s00453-007-9056-z (the technical report is held).
- Bodlaender & Koster (2011), Information and Computation 209(7), 1103–1119,
  DOI 10.1016/j.ic.2011.04.003 (the technical report is held).
- Samer & Veith (2009), SAT 2009, LNCS 5584, 45–50, DOI
  10.1007/978-3-642-02777-2_6.
- Grohe (2016), Tangled up in blue (a survey on connectivity, decompositions,
  and tangles), arXiv 1605.06704. Not read; optional.
