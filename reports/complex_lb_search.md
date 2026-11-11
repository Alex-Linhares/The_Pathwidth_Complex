# Lower bounds in the search-game and interval members of the complex: a survey

*2026-11-11, one session. A literature survey, nothing more: no solver was run,
no instance was touched, nothing was downloaded into `literature/`. Open PDFs
were read from a scratch directory (`/tmp`) through `pdftotext`; held papers
were read from `literature/`. Page numbers are the sources' own printed pages
where the source carries them, otherwise the preprint's section or lemma
number. Sibling surveys cover the other families of the complex (gate matrix
layout, PLA folding, one-dimensional logic, split bandwidth, the layout and
LP side); this one owns the search games (node, edge, mixed, connected,
non-deterministic, zero-visibility) and the interval problems (interval
thickness, narrowness, vertex separation, proper pathwidth, linear-width),
with the structural families where those communities proved their bounds
(trees, block graphs, grids, products, outerplanar and Halin graphs, cubic
graphs and cages). Context read first: `CLAUDE.md` (Bounds),
`paper1/equivalences.md` (the master table), `reports/obstruction_search.md`
§0, `reports/blockage_class.md` §0, `reports/spectral_bound.md` §0,
`reports/chain_lp.md` §0, `paper1/latex/sec9f_appendix_dual.tex`.*

## §0. Summary (two pages)

**The question.** Every member of the pathwidth complex is a problem some
community solved for its own reasons, and a lower bound proved there is a
pathwidth lower bound whether or not it was ever called one. The families on
record here — degree / clique / degeneracy (all `≤ tw + 1`), Harper's
vertex-isoperimetric bound (one prefix size), searched contraction minors,
separator branches, the blockage class (clique / minor-pullback /
linked-branch operators), spectral and LP relaxations — have measured ceilings
below the optimum on the residual gap instances. The owner asked whether the
search-game and interval communities hold a technique we have not seen.

**The answer, in one sentence.** They do not hold one that reaches the 338
corpus bound-gap instances; every lower-bound argument in print for node,
edge, mixed, connected and non-deterministic search, interval thickness,
narrowness, vertex separation, proper pathwidth and linear-width is, once
translated through the equivalences of `paper1/equivalences.md`, a clique
argument, a degree argument, the three-branch (Parsons) lemma, minor
monotonicity, Harper's bound, or a blockage written out by hand for one graph
family (grids, tori, products) — and the literature says so itself: Fomin &
Thilikos (2008, p. 12 of the GRASTA reprint) name brambles as "certificates of
escaping strategies" for the visible fugitive and blockages as their invisible
analogue, and name nothing else. **One route is genuinely different in kind
and lives exactly on the open cages**: for graphs of maximum degree 3 the edge
search number equals the cutwidth (Makedon & Sudborough 1989; Fomin & Thilikos
2008, p. 13), so with Ellis, Sudborough & Turner's `es ≤ vs + 2` the
pathwidth of a subcubic graph is at least its cutwidth minus two, and cutwidth
has an *edge*-isoperimetric lower bound (the edge boundary of a `t`-set, up to
three times the vertex boundary on a cubic graph) that no bound on record
computes. It is stated as an experiment with a kill criterion in §4; the
arithmetic available today (one eigenvalue on the Tutte 12-cage) puts it four
below the record floor, so the expected verdict is dead, but the measurement
that decides it costs minutes. Everything else is "already covered, cite".

**The translation dictionary** (§1; all equalities are Lean theorems in
`lean/MOSPFormalization/Complex/` unless marked). A bound `b` on a member
transfers to pathwidth as follows: node search `ns = pw + 1` (K&P 1986 Thm
4.1), so `ns ≥ b ⇒ pw ≥ b − 1`; interval thickness `θ = pw + 1` and narrowness
`ν = pw + 1`, the same; vertex separation `vs = pw`; edge search
`vs ≤ es ≤ vs + 2` (EST 1994 Thm 2.1), so `es ≥ b ⇒ pw ≥ b − 2`; mixed search
`= ppw = lw ∈ {pw, pw + 1}` (Takahashi, Ueno & Kajitani 1995; Thilikos 2000
Thm 4; Fomin & Thilikos 2006 Lemma 2, held), so `pw ≥ b − 1`; connected search
`cs ≥ s`, so a lower bound on `cs` transfers **not at all**; non-deterministic
search `tw + 1 ≤ s_q ≤ pw + 1` for every `q` (Fomin, Fraigniaud & Nisse 2009),
so a lower bound on any `s_q` is a lower bound on `pw + 1`; zero-visibility
cops and robber `c_0 ≤ pw` with no lower function of `pw` (Dereniowski, Dyer,
Tifenbach & Yang 2015), so a bound on `c_0` transfers but is worth little;
cutwidth `pw ≤ cw` always (Korach & Solel 1993) and `cw = es` when `Δ ≤ 3`, so
`pw ≥ cw − 2` on subcubic graphs.

**The table.** Classification codes: **D** degree / clique / degeneracy
(`≤ tw + 1` by `ml_nature.md` §24); **H** Harper / isoperimetric at one prefix
size; **M** minor / obstruction; **B** the branch operator (three linked
branches); **G** game / blockage written for one family — inside our
clique / minor-pullback / linked-branch operators unless the row says
"consecutive orders", which is the band of `reports/checkpoint_relaxation.md`
and outside every compact class on record; **=** an equality, not a bound;
**N** genuinely different.

| # | technique (in the member's own terms) | source (page) | translation to `pw` | class | verdict |
|---|---|---|---|---|---|
| 1 | Parsons' lemma: `s(T) ≥ k + 1` iff some vertex has ≥ 3 branches of search number ≥ k (edge search, trees) | Parsons 1978; Megiddo et al. 1988 p. 21 ("Parsons' Lemma"); Peng et al. 2000 Lemma 2 | the branch lemma; `pw ≥ k + 1` from three branches of `pw ≥ k` at a vertex | B | covered: `Sandwich.lean` `branch_lemma`; the harness found no gap instance it closes (`ml_nature.md` §38) |
| 2 | Scheffler's theorem: `ns(T) ≥ k + 1` iff some vertex has three branches of `ns ≥ k`; `pw(T) ≥ p + 1` iff a vertex has three components of `pw ≥ p` | Scheffler 1990 (not held); Peng et al. 2000 Lemma 8; Coudert, Huc & Sereni 2009 Thm 5 | the same, in node-search units | B | covered, cite |
| 3 | Kornai–Tuza: `ν(T) ≥ k` iff `T` contracts to a member of `T_k`; the contraction-minimal trees have `(5·3^{k−2} − 1)/2` vertices | Kornai & Tuza 1992 Thm 4.1 (preprint pp. 4–5) | `pw(T) ≥ k − 1` iff a ternary-branching tree minor; the extremal sizes are our `treeBound` (`TreeBound.lean`: `2·treeBound k + 3 = 5·3^k`) | B + M | covered: the same extremal family, proved sorry-free on 2026-10-30; cite Kornai & Tuza beside EST |
| 4 | EST 1994: `vs(T)` characterisation and the smallest trees of each `vs`; the 2-expansion `vs(G') = s(G)`; `vs ≤ s ≤ vs + 2` | Ellis, Sudborough & Turner 1994 §§3–4, Thm 2.1 | the branch lemma and the edge-search sandwich | B, = | covered: `EdgeSearchFull.lean`, `TreeBound.lean` |
| 5 | Megiddo et al.: searching `K_M` needs `M − 1` searchers at the step the first vertex is cleared; `m` disjoint `K_M`'s | Megiddo et al. 1988 Lemmas 1–3, p. 21 | clique bound `pw ≥ ω − 1` | D | covered |
| 6 | Yang, Dyer & Alspach: sweep number vs clique number; `s(H) ≤ s(G)` for minors `H` | Yang, Dyer & Alspach 2009 (abstract; cited by Clarke & Messinger 2019 Cor. 6) | clique bound; minor monotonicity | D, M | covered |
| 7 | Alspach, Dyer, Hanson & Yang: edge-search lower bounds from minimum degree, girth, chromatic number, colouring number | ESCAPE 2007 (abstract only; not open) | degree-type (`δ`, `col = degeneracy + 1`, `χ ≤ col`) and a girth bound | D (+ girth) | covered except the girth clause, which is Chandran–Subramanian's kind (`≤ tw + 1`); to obtain |
| 8 | Kirousis–Papadimitriou: interval thickness, `ns = θ`, `ns = vs + 1`; LaPaugh monotonicity | K&P 1985, 1986 Thms 2.1–4.1 | equalities | = | covered (`NodeMonotonicity.lean`); no bound technique of its own |
| 9 | Chandran, Kavitha & Subramanian: `pw(G) ≥ b_v(s, G)` for every `s`, proved through an interval supergraph (`ω(H) ≥ b_v(s, H) + 1` on connected interval graphs) | CKS 2003 Lemma 2, Thm 3 (held, §3) | Harper's bound | H | covered: `expansion_bound.py`, `EmptyPair.lean`; its ceiling is below the optimum on 320 of the 338 (`obstruction_search.md` §0) |
| 10 | BRST blockages; Bienstock–Seymour crusades | BRST 1991 (2.1); Bienstock & Seymour 1991 | the exact dual; monotonicity | G | covered: `Blockage.lean`, Appendix F |
| 11 | Dendris, Kirousis & Thilikos: lazy invisible fugitive of unbounded speed ↔ `tw + 1`; of speed 1 ↔ **degeneracy + 1** ("width", polynomial) | DKT 1997 (abstract; Fomin & Thilikos 2008 p. 13) | the degeneracy bound is the unit-speed lazy game; every lazy-fugitive number lies in `[degeneracy + 1, tw + 1]` | D | covered; **cite** — it is the game-theoretic statement of the treewidth ceiling on the degree family |
| 12 | Mixed search = proper pathwidth = linear-width; `pw ≤ lw ≤ pw + 1`; obstruction sets for `lw ≤ 2` (57 graphs), `ppw ≤ 2`, acyclic obstructions for `pw ≤ k` and `ppw ≤ k` | Takahashi, Ueno & Kajitani 1994 (held), 1995; Thilikos 2000 Thms 3–4 (TR pp. 22–23); Fomin & Thilikos 2006 Lemma 2 (held) | `pw ≥ b − 1`; a forbidden minor for `pw ≤ k` is a minor certificate | =, M | covered by family M; the sets are known only to `k = 2` (and `k = 3` for 3-connected graphs, Ding & Dziobiak 2013) |
| 13 | Kinnersley–Langston: the 110 obstructions for three tracks (`pw ≤ 2`) | K&L 1994 (held) | minor certificates | M | covered |
| 14 | Ellis–Warren grids, cylinders, tori, orb-webs: first completely clean row / column, critical guards, `ns(h×w grid) ≥ min(h, w) + 1`, `ns(h×h torus) ≥ 2h` | Ellis & Warren 2008 Lemmas 4.2, 5.2, 6.2, 7.3 (held, pp. 548–554) | `pw` of grids `= min(h, w)`, tori `2h − 1`, exact | G, consecutive orders | covered in kind: a blockage argued step by step; equals `tw` or `tw + 1` on these families; not computable off the family |
| 15 | Clarke–Messinger products: `pw(K_2 □ K_n) ≥ n` by two cliques in two bags and the interval property; `s(P_n □ P_n) ≥ n + 1`; `s(G □ H) ≥ pw(K_{ω(G)} □ K_{ω(H)})` | Clarke & Messinger 2019 Lemmas 3, 8, Cor. 6, Lemma 7 (held, arXiv pp. 3–5) | clique-in-bag (Helly) plus counting; minor monotonicity | D + M | covered: `exists_bag_of_isClique` is the lemma; `pw(K_n □ K_n) = tw(K_n □ K_n)` (Lucena 2007), so it certifies nothing above `tw` |
| 16 | Block graphs: `ns(G) ≤ k` iff every vertex has ≤ 2 branches of `ns ≥ k` (`VC_k`) and every block has an edge `xy` with `ns({G}_{x,y}) < k` (`BC_k`) | Chou, Ko, Ho & Chen 2008 Thm 4 (held, p. 5) | exact on block graphs; the lower half is the branch lemma plus a clique-edge condition | B + D | covered in kind; a block-graph *subgraph* is a floor by monotonicity (`paper2/survey_trees_sparse.md`), never measured on the gap instances — see §5 |
| 17 | Halin: `lw(T) ≤ lw(H) ≤ 3·lw(T)`; outerplanar: `pw(G) ≤ 2·pw(G*) + 2`, lower side by the dual tree | Fomin & Thilikos 2006 Lemma 8; Bodlaender & Fomin 2000; Coudert, Huc & Sereni 2009 (all held) | lower halves are subgraph / minor monotonicity | M | covered |
| 18 | Cubic graphs: `pw ≤ (1/6 + ε) n` (upper); "0.082 n" lower via the bisection width of Ramanujan cubic graphs | Fomin & Høie 2006 §5, p. 196 (held) | `pw ≥ bw − 2` on subcubic graphs (our reading, §4) | H (edge version) | **new operator on subcubic graphs**, §4 |
| 19 | Cubic graphs: `ξ(k) ≤ (2/3)k + 10/3`; `ξ(k) ≤ k − 2` for `k ≥ 10`; the table `ξ(3..10) = 4,4,5,6,6,7,8,8` with K₃,₃, cube, Petersen, Heawood, Pappus, McGee, Tutte–Coxeter, G(10) | Bachtler & Heinrich 2023 Thms 1.1–1.3 (arXiv pp. 2–3; dissertation Thms 8.6, 8.11, pp. 121–127) | a cubic graph of girth `g ≥ 9` has `pw ≥ g + 2`; of girth `g ≥ 3`, `pw ≥ (3g − 10)/2` | N (girth; an unavoidable-set argument) | **genuinely different, dead by arithmetic on the open cages** (§4.2): 14, 13, 12, 12, 11 against record floors 20, 17, 16, 15, 16; cross-check: their five certified small values equal the dataset's |
| 20 | Girth and average degree: `tw ≥ (d̄ − 1)^{⌊(g−1)/2⌋}/(4e(g+1)) − 2` | Chandran & Subramanian 2005 (BK TR Thm 8) | `pw ≥ tw` | D | covered; below 1 on every cage |
| 21 | Connected search `cs ≤ mcs ≤ 2s + 3`; connected pathwidth `cpw ≤ 2pw + 1` | Dereniowski 2011 Thms 2, 4 (held) | no transfer downward | — | nothing to use |
| 22 | Non-deterministic search `s_q`, monotone; `tw + 1 ≤ s_q ≤ pw + 1` | Fomin, Fraigniaud & Nisse 2009; Mazoit & Nisse 2008 | any `s_q` bound is a `pw + 1` bound; none in print beyond `tw` | — | nothing to use |
| 23 | Zero-visibility cops and robber: `c_0 ≤ pw`, no lower function of `pw`; matching-number lower bounds on `c_0` | DDTY 2015; Xue, Yang & Zilles 2022 (abstracts) | transfers, but `c_0` is unboundedly below `pw` | — | nothing to use; to obtain for the record |
| 24 | Lengauer: VSG NP-complete; pebbling lower bounds for DAGs | Lengauer 1981 (held) | none for undirected `vs` | — | nothing |
| 25 | Narrowness | Kornai & Tuza 1992 Prop. 3.1 | `ν = pw + 1`; no bound of its own | = | covered (`Narrowness.lean`) |

**Ranked, what we can use.**

1. **An experiment, cheap, on the five open cubic cages only** (§4.1): the
   subcubic cutwidth route `pw ≥ cw − 2 ≥ max_t Φ_E(t) − 2`, with
   `Φ_E(t) = min_{|S|=t} e(S, V∖S)` the edge-isoperimetric profile. It is
   Harper's argument on the edge boundary, which on a cubic graph can be up to
   three times the vertex boundary, and nothing on record computes it. Kill
   criterion, before measuring: dead unless, on at least one of Foster
   (floor 15, width 20), Biggs–Smith (16, 19), Ljubljana (16, 22), Balaban
   11-cage (17, 24), Tutte 12-cage (20, 26), a *ceiling* on
   `max_t Φ_E(t)` found by local search (a `t`-set with small edge boundary at
   every `t`, minutes of compute) exceeds `floor + 2`. The 12-cage's spectral
   value `μ₂ n / 4 = 17.3` (`reports/spectral_floor_integration.md`, `μ₂ =
   3 − √6`) is already four below `floor + 2 = 22`, and Monien & Preis's
   asymptotic `bw ≤ (1/6 + o(1)) n` puts its bisection near 21, so the
   expected verdict is dead by one or two; but the ceiling is the only honest
   way to say so, and it is not on record.
2. **Citations to add** to the paper's lower-bound section and Appendix F:
   Dendris, Kirousis & Thilikos (1997) for the game reading of the treewidth
   ceiling (row 11); Fomin & Thilikos (2008, p. 12) for "brambles are
   certificates of escaping strategies, blockages their invisible analogue";
   Kornai & Tuza (1992, Thm 4.1) beside Ellis, Sudborough & Turner for the
   extremal trees of `TreeBound.lean`; Bachtler & Heinrich (2023) for the
   only girth-based pathwidth bound and for five independent exact values on
   named cubic graphs that agree with the dataset (Petersen 5, Heawood 6,
   Pappus 7, McGee 8, Tutte–Coxeter 9); Makedon & Sudborough (1989) for
   `es = cw` on `Δ ≤ 3`, which `reports/subexp_pathwidth.md` §7 attributes
   on a guess.
3. **For the 338 corpus gap instances: nothing.** Their MOSP graphs are
   unions of cliques at 20–134 customers, not subcubic, not trees, grids or
   products; every row above reduces there to a family already measured
   (D, H, M, B) and `reports/obstruction_search.md` §0 has the duality gap of
   each.
4. **Not worth building**: an interval-completion bound (the interval
   literature's lower bounds are the clique number and, on cocomparability
   graphs, `pw = tw`, Habib & Möhring 1994 — our instances have `pw > tw`);
   a zero-visibility or connected-search bound (rows 21, 23).

**What was searched and not found.** No paper states a lower-bound technique
for an invisible agile fugitive other than the blockage, the three-branch
lemma, a clique, a degree, a minor, or a hand-written case analysis on one
family; no paper computes the pathwidth, cutwidth or bisection width of the
Foster, Biggs–Smith, Ljubljana, Balaban or Tutte 12-cage graphs; no paper
states "pw ≥ cw − 2 for subcubic graphs" in that form (Fomin & Høie write
that Bezrukov et al.'s bisection result "also yields the lower bound 0.082n
for pathwidth of graphs with maximum degree three" without the route, p.
196). "We found no prior statement", never "first".

---

## §1. The dictionary: what a bound on each member says about pathwidth

The equivalences are those of `paper1/equivalences.md` (sorry-free Lean
theorems in `lean/MOSPFormalization/Complex/` except where a source is
named). `G` is finite, simple, with at least one edge where a game needs one.

| member | relation to `pw` | a lower bound `b` on the member gives | source |
|---|---|---|---|
| vertex separation `vs` | `vs = pw` | `pw ≥ b` | Kinnersley 1992 Thm 3.1; `VSEquivPW.lean` |
| node search `ns` | `ns = pw + 1` | `pw ≥ b − 1` | Kirousis & Papadimitriou 1986 Thm 4.1; `NodeMonotonicity.lean` |
| interval thickness `θ` | `θ = pw + 1` | `pw ≥ b − 1` | K&P 1985; Möhring 1990 Prop. 3.5; `IntervalThickness.lean` |
| narrowness `ν` | `ν = pw + 1` | `pw ≥ b − 1` | Kornai & Tuza 1992 Prop. 3.1; `Narrowness.lean` |
| edge search `es` | `vs ≤ es ≤ vs + 2` | `pw ≥ b − 2` | Ellis, Sudborough & Turner 1994 Thm 2.1; `EdgeSearchFull.lean` |
| mixed search `ms` = proper pathwidth `ppw` = linear-width `lw` | `pw ≤ lw ≤ pw + 1`; `ms = lw` (`= ms` of the graph without pendant vertices) | `pw ≥ b − 1` | Takahashi, Ueno & Kajitani 1995; Thilikos 2000 Thm 3(ii)–(iii), Thm 4 (TR pp. 22–23); Fomin & Thilikos 2006 Lemma 2 (held) |
| strong mixed search | `= pw` | `pw ≥ b` | Yang 2007 (via Fomin & Thilikos 2008 p. 13) |
| connected search `cs`, connected pathwidth `cpw` | `s ≤ cs ≤ 2s + 3`, `pw ≤ cpw ≤ 2pw + 1` | **nothing** (`cs ≥ s` is the wrong direction) | Dereniowski 2011 Thms 2, 4 (held) |
| non-deterministic search `s_q` | `tw + 1 = s_∞ ≤ s_q ≤ s_0 = pw + 1` | `pw ≥ b − 1` for every `q` | Fomin, Fraigniaud & Nisse 2009; monotone by Mazoit & Nisse 2008 |
| lazy invisible fugitive, speed `∞` / speed 1 | `tw + 1` / degeneracy + 1 | `pw ≥ tw ≥ b − 1` / `pw ≥ degeneracy ≥ b − 1` | Dendris, Kirousis & Thilikos 1997 (abstract; Fomin & Thilikos 2008 p. 13) |
| zero-visibility cop number `c_0` | `c_0 ≤ pw`; not bounded below by any function of `pw` | `pw ≥ b` | Dereniowski, Dyer, Tifenbach & Yang 2015 (abstract) |
| cutwidth `cw` | `pw ≤ cw` always; `cw = es` when `Δ ≤ 3` | `pw ≥ b − 2` when `Δ ≤ 3`; `pw ≥ b / Δ` in general (each crossing edge has a boundary endpoint) | Korach & Solel 1993; Makedon & Sudborough 1989 (via Fomin & Thilikos 2008 p. 13 and Ellis et al. 1994); the general inequality is folklore |

Two remarks the dictionary makes on its own. First, the only member whose
lower bounds *gain* on translation is none: every arrow loses 0, 1 or 2.
Second, the lazy-fugitive row is the game-theoretic form of the treewidth
ceiling: a fugitive who moves only when a searcher is about to land on him
is caught by a *tree* strategy, so every bound proved by letting the
fugitive wait — degree, degeneracy, clique, bramble — is a bound on
`tw + 1`, and only an *agile* invisible fugitive, who may run at every step,
needs a blockage. That is the content of `ml_nature.md` §24 said by Dendris,
Kirousis & Thilikos a decade before, and it should be cited.

## §2. The search games, paper by paper

### 2.1 Parsons (1976, 1978) and Megiddo, Hakimi, Garey, Johnson & Papadimitriou (1988) — held

The edge-search game and its first lower-bound tool. Megiddo et al. (p. 21)
restate **Parsons' Lemma**: "for any tree `T` and integer `k ≥ 1`,
`s(T) ≥ k + 1` if and only if `T` has a vertex `v` at which there are three or
more branches that have search number `≥ k`", and build the linear-time tree
algorithm on the *avenue* (Lemma 4, p. 22: either a hub whose every branch
has search number `< s`, or a unique path on which every vertex has exactly
two branches of search number `s`). For the NP-completeness reduction they
prove three clique lemmas (p. 21): in a search of `K_M`, `M ≥ 4`, at the step
the first vertex becomes cleared there are at least `M − 1` searchers on it
(Lemma 1); with `m` vertex-disjoint copies of `K_M` the cliques are cleared
one at a time (Lemma 2); an edge between a clique with a cleared vertex and
one without carries a searcher at an endpoint (Lemma 3). Translation: Lemma 1
is `es(K_M) ≥ M − 1`, i.e. `pw ≥ ω − 3` after the sandwich — weaker than the
clique bound we hold directly. Classification: the branch lemma (**B**) and
the clique bound (**D**). Nothing to add.

### 2.2 Ellis, Sudborough & Turner (1994) — held (the PDF is a scan with no text layer; the WUSTL report WUCS-87-11 is the open copy)

Theorem 2.1, `vs(G) ≤ s(G) ≤ vs(G) + 2`, with the 2-expansion `G'` (each
edge subdivided twice) satisfying `vs(G') = s(G)`; the characterisation of
trees of vertex separation `k` by the three-branch rule, and the smallest
such trees. All of it is formalised: `EdgeSearchFull.lean` has the sandwich
for the full game, `Sandwich.lean` the branch lemma (corrected on
2026-09-28 after the stated form was found false), `TreeBound.lean` the
extremal trees (`extremalTree k` with `treeBound k + 1` vertices and
pathwidth `k + 1`). Classification **B**, **=**.

### 2.3 Scheffler (1990), Kornai & Tuza (1992) — Kornai & Tuza open at SZTAKI

Scheffler's theorem (not held; quoted as Lemma 8 of Peng et al. 2000, p. 5,
and Theorem 5 of Coudert, Huc & Sereni 2009): `ns(T) ≥ k + 1` for `k ≥ 2` iff
some vertex has three branches of `ns ≥ k`. Kornai & Tuza prove the
narrowness form by contraction (Thm 4.1, preprint pp. 4–5): `ν(T) ≥ k` iff
`T` contracts to a member of `T_k`, where `T_2 = {K_2}` and `T ∈ T_{k+1}` iff a
degree-3 vertex has its three components in `T_k`; the contraction-minimal
trees have exactly `(5·3^{k−2} − 1)/2` vertices. In pathwidth units
(`ν = pw + 1`) that is `(5·3^{pw−1} − 1)/2`, which is `treeBound(pw) + 1` of
`TreeBound.lean` (`2·treeBound k + 3 = 5·3^k`): the two statements are the
same theorem, and `TreeBound.lean`'s header should cite Kornai & Tuza beside
Ellis et al. and Scheffler. The proof's device, the `p`-strong edges (both
sides of narrowness `≥ p`; Lemma 4.2: they form a connected subtree), is a
one-page proof of the branch lemma for trees. Classification **B** + **M**.
Nothing new for non-trees; the paper raises as open "the structure of graphs
with narrowness ≤ 7" (p. 5).

### 2.4 Kirousis & Papadimitriou (1985, 1986) — 1986 held

Interval thickness (1985), `ns = θ`; `ns = vs + 1` (1986 Thm 4.1), LaPaugh's
`pes = es` (Thm 2.1), `es(G) = ns(G°) − 1` through the subdivision (Thm 2.5),
and the pebbling equivalences of §3 (`mpb = ns`, Thm 3.1). Every one is in
`Complex/`, with the `K_{1,3}` repair of the Theorem 4.1 proof. The only
lower bound either paper uses is the clique (interval thickness is at least
the clique number by definition). Classification **=**.

### 2.5 Chandran, Kavitha & Subramanian (2003) — held

Section 3: `IW(G) = pw(G)` (Lemma 1); on a connected interval graph
`ω(G) ≥ b_v(s, G) + 1` for every `1 ≤ s ≤ n` (Lemma 2); hence
`pw(G) ≥ b_v(s, G)` for every `s` (Theorem 3), with `b_v(s, G)` the smallest
vertex boundary of an `s`-set. This is Harper's bound reached through the
interval member rather than the layout — the proof is three lines once the
monotonicity `b_v(s, G') ≥ b_v(s, G)` for supergraphs is noted. It is
`exists_closedNbhd_card_le` of `EmptyPair.lean` and `expansion_bound.py`;
its exact value is below the optimum on 320 of the 338 gap instances
(`obstruction_search.md` §0). Classification **H**. The same paper's
carving-width bound (Lemma 3 onward) is the edge version for a different
parameter; it is the kind of argument §4 uses, on cutwidth instead.

### 2.6 Bienstock, Robertson, Seymour & Thomas (1991); Bienstock & Seymour (1991); Bienstock (1991) — first held

Blockages are the exact dual (Appendix F, `Blockage.lean`); the crusade
argument of Bienstock & Seymour proves monotonicity of mixed search and is
the template of `nodeSearchMonotonicity`. Bienstock's DIMACS survey is not
open and not held; from its citations it reviews the equivalences, not
bounds. Classification **G**, the whole class.

### 2.7 Fomin & Thilikos (2008), the annotated bibliography — open reprint (GRASTA 2009 booklet, pp. 10–13)

Read whole. On certificates it says only this (p. 12): Seymour & Thomas's
proof for the visible fugitive "was based on the introduction of screens
(also known as brambles) as certificates of escaping strategies. The
analogue of these structures for the invisible fugitive case was introduced
in [22] (called blockages) and generalized to a general monotonicity
criterion in [64]" (Fomin & Thilikos's submodular-function paper). On
parameters (p. 13): pathwidth `= ns − 1`; strong mixed search `= pw` (Yang);
proper pathwidth `= ms` (Takahashi et al.); the visible agile fugitive
`= tw + 1`; Dendris et al.'s lazy invisible fugitive `= tw + 1`, and "the
special case of a lazy fugitive of unit speed is equivalent to the
degeneracy of a graph (that can be computed in polynomial time)"; and
"cutwidth is related to edge-searching (on graphs of vertex degree at most
3 these parameters are equal) [111]" with [111] = Makedon & Sudborough
1989. The last two sentences are rows 11 and 18 of the table. No lower-bound
technique beyond these appears in the bibliography's 170 entries.

### 2.8 Dendris, Kirousis & Thilikos (1997) — not held (listed in `MISSING.md` since 2026-10-11)

From the abstract and the bibliography above: an invisible fugitive who
moves only when a searcher is about to land on him, with speed `s`; for
unbounded speed the search number is `tw + 1`, for speed 1 it is the
polynomially computable "width", which is the degeneracy plus one; both
games are monotone; for graphs whose chordless cycles have length `≤ s`,
speed `s − 2` already gives `tw + 1`. Reading for us: the degree family of
`_lower_bound` is the family of lazy games, and its ceiling at `tw + 1` is
the unbounded-speed lazy fugitive. Nothing computational, one citation.

### 2.9 Mixed search, proper pathwidth, linear-width — Takahashi, Ueno & Kajitani (1994 held, 1995), Thilikos (2000; open TR), Fomin & Thilikos (2006, held)

Thilikos's TR (pp. 22–23) collects: a monotone mixed search exists at the
optimum (Thm 3(i), Bienstock & Seymour); `lw ≤ ms` (3(ii)); `lw = ms` when
there are no pendant vertices (3(iii)); `es(G) = ms` of the subdivision and
`ns(G) = ms` of the doubled graph (3(iv), 3(vi)); and Thm 4, `ms(G) = lw(G)`
exactly, with `lw(G) = ms` of the graph stripped of pendant vertices. Fomin &
Thilikos 2006 Lemma 2 (held): `pw ≤ lw ≤ pw + 1`. Takahashi et al. 1994
(held) determine the minimal acyclic forbidden minors for pathwidth `≤ k`
(Thm 2.5: the star-compositions) and introduce proper pathwidth; their 1995
TCS paper proves `ms = ppw`; Thilikos 2000 gives the 57 minimal forbidden
minors for `lw ≤ 2` and, through the structural link, the acyclic ones for
every `k`. Translation: a bound on any of these is `pw ≥ b − 1`; an
obstruction found as a minor is a certificate of family **M**. Since the
obstruction sets are known only to `k = 2`, and a searched contraction minor
already is "a graph of pathwidth `≥ k + 1` found as a minor", nothing is
added. Classification **=**, **M**.

### 2.10 Obstruction sets — Kinnersley & Langston (1994, held), Ding & Dziobiak (2013, open preprint), Barát et al. (2012, held)

110 obstructions for three tracks (`pw ≤ 2`), 122 million at least for four
(Kinnersley's thesis, as cited on p. 199); the 3-connected obstructions for
`pw ≤ 3` (Ding & Dziobiak). A minor-minimal obstruction for `pw ≤ k` is the
smallest possible minor certificate of `pw ≥ k + 1`, so the family is **M**
and its search is loop0013's. Not usable above `k = 3`.

### 2.11 Grids, cylinders, tori, orb-webs — Ellis & Warren (2008, held)

The method (Lemma 4.2, p. 548–549, for the `(h, w)`-grid): let `t_c`, `t_r`
be the first steps at which a column, a row is completely clean; at
`t_r − 1` no row or column is clean but one row is almost clean, so by
Observation 3.4 there are `w − 1` critical guards each on a dirty column
edge; if exactly `w − 1`, one column is guard-free and completely dirty, the
next placement must land in it and cleans nothing, so `w` critical guards,
and the criticality principle (p. 547: when every guard is critical the next
move is a placement) forces `w + 1`. Tori need the harder Lemma 7.3 (pp.
551–554): `2h + 1` unless `h = w`, where a strategy with `2h` guards exists
(Lemma 7.2) and `2h` is the floor. This is a blockage argued move by move:
"the first time a full line is clean" is a separation of a particular order,
and the argument chases the fugitive through the separations of the next
one or two orders — the consecutive-order band of
`reports/checkpoint_relaxation.md`, in prose. The authors say so (p. 546):
"the concept of a 'bramble/screen' developed in [Seymour & Thomas] could
possibly be used to obtain the other lower bounds we prove here". On the
families themselves the values are `tw` (grids) or within one of it (tori:
`pw = 2h − 1`), so even there the bound never certifies `pw > tw + 1`.
Classification **G**, consecutive orders; not computable off the family.
Warren's MSc thesis (Victoria, 2005) is the long form; not held.

### 2.12 Products — Clarke & Messinger (2019, held; Clarke, Messinger & Power)

Lemma 3 (`s(P_n □ P_n) ≥ n + 1`) is Ellis–Warren's argument in edge-search
form. Lemma 8 (`pw(K_2 □ K_n) ≥ n`, arXiv p. 5) is the clean one: the two
`n`-cliques lie in two bags `B_i`, `B_j` (Helly, Lemma 2 = our
`exists_bag_of_isClique`), `i < j`; the first bag `B_x` containing a matched
pair `v_{1,α}, v_{2,α}` lies strictly between and has room for at most `n − 2`
others, so some `v_{1,β}` is missing from `B_x` yet must meet `v_{2,β}` later —
violating the interval property. Corollary 6 is minor monotonicity of `s`
(Yang, Dyer & Alspach 2009), Lemma 7 the reduction to products of cliques,
and the main theorem `pw(K_m □ K_n) = (m/2)n + m/2 − 1` (`m` even),
`⌈m/2⌉n − 1` (`m` odd), `n ≥ m ≥ 2`, which equals Lucena's treewidth of
`K_n □ K_n`. Classification **D** + **M**: cliques, bags and the interval
property, which is our Helly lemma; and on the family where it is sharp it
is a treewidth value. `K_m □ K_n` *is* a MOSP graph (the instance whose
patterns are the `m` rows and `n` columns), so the formula is a closed-form
optimum for a two-pattern-per-customer family; a remark for paper 2's
polynomial cases, not a bound.

### 2.13 Trees, block graphs, Halin and outerplanar graphs — Peng et al. (2000), Chou et al. (2008), Coudert, Huc & Mazauric (2012), Fomin & Thilikos (2006), Bodlaender & Fomin (2000), Coudert, Huc & Sereni (2009), Markov (2004, 2007, 2008) — all held

Peng et al. (Lemmas 1–13, pp. 4–7) run Megiddo's avenue machinery for edge
and node search on trees in linear time; Coudert, Huc & Mazauric's Theorem 2
(p. 7) is Parsons' lemma again with a distributed algorithm. Chou et al.
(Thm 4, p. 5) characterise node search on block graphs: `ns ≤ k` iff `VC_k`
(no vertex has three branches of `ns ≥ k`) and `BC_k` (every block `K` has an
edge `xy` with `ns({G}_{x,y}) < k`, where `{G}_{x,y}` is `G` minus the two
branches at `x` and `y` through `K`); the lower half (proof, p. 7) is the
branch lemma plus Lemma 3(1), `os(G, u, v) ≥ ns({G}_{x,y}) + 1` for an edge on
the `u`–`v` path. Halin: `lw(T) ≤ lw(H) ≤ 3·lw(T)` (Lemma 8), the lower side
by subgraph monotonicity. Outerplanar: Bodlaender & Fomin's `pw(G) ≤ 2pw(G*)
+ 2` and Coudert–Huc–Sereni's sharpening; the lower side is again a minor
(the weak dual is a minor of a subdivision). Classification **B** + **D**
(block graphs), **M** (the rest). The one thing not yet measured: a
block-graph subgraph of a gap instance's MOSP graph is a floor through
Chou et al.'s exact formula; `paper2/survey_trees_sparse.md` records the
idea. On the 338 it cannot beat the searched contraction minor (tight on
327) and on the 11 residual dense instances a block-graph subgraph is a
tree of cliques whose node search number is near the largest clique, far
below 57–99. Dead on arithmetic; recorded in §5 so that it is not proposed
again.

### 2.14 Cubic graphs and cages — Fomin & Høie (2006, held), Makedon & Sudborough (1989, not held), Bachtler & Heinrich (2023, open), Chandran & Subramanian (2005, not held), Alspach, Dyer, Hanson & Yang (2007, not open), Yang, Dyer & Alspach (2009, not open)

Fomin & Høie, §5 (p. 196): "Lower bounds on pathwidth of cubic graphs can be
obtained by making use of Algebraic Graph Theory. In particular, Bezrukov et
al. [3] (by making use of the second smallest eigenvalues of Ramanujan
graph's Laplacian) showed that there are 3-regular graphs with the bisection
width at least 0.082n. It can be shown that the result of Bezrukov et al.
also yields the lower bound 0.082n for pathwidth of graphs with maximum
degree three. It is an interesting challenge to reduce the gap between
0.082n and 0.167n." The route is not given. Our reading (§4.1): cutwidth is
at least bisection width, equals edge search number on subcubic graphs
(Makedon & Sudborough; Fomin & Thilikos 2008 p. 13; Ellis et al. 1994 cite
it as "[Makedon 1983]"), and `es ≤ vs + 2`, so `pw ≥ bw − 2`, which is
`0.082n − 2`. (Wikipedia's "in subcubic graphs the cutwidth equals the
pathwidth plus one", citing the same paper, is false as stated — a path has
`cw = pw = 1` — and is not used.) `reports/subexp_pathwidth.md` §7 proves
`vs(G°) = cw(G)` for `Δ ≤ 3` on the degree-clique expansion and checked
`es = cw` on every subcubic atlas graph with `n + 2m ≤ 20`, attributing it
to Makedon & Sudborough on a guess; the attribution is now on two
independent secondary citations and should be made firm.

Bachtler & Heinrich (JGT 2023; arXiv 2010.08373; Bachtler's dissertation
chapter 8): with `ξ(k)` the largest girth of a cubic graph of pathwidth `k`,
**Theorem 1.1** `ξ(k) ≤ (2/3)k + 10/3` for `k ≥ 3`; **Theorem 1.2** the table
`ξ(3..10) = 4, 4, 5, 6, 6, 7, 8, 8` and `ξ(k) ≤ k − 2` for all `k ≥ 10`;
**Theorem 1.3** the unique smallest cubic graph of pathwidth `k` and girth
`ξ(k)`: K₃,₃, {cube, twisted cube}, Petersen, Heawood, Pappus, McGee,
Tutte–Coxeter, and `G(10)` (pp. 2–3). The proof of 1.1 (§4) takes a
high-degree-first path decomposition, the largest index `l ≤ k + 1` at which
the associated graph has at most one cycle, and counts degrees in the next
one; the table rests on an automated unavoidable-set test (§3) plus the
census of small cubic graphs checked in SageMath. They compare with Chandran
& Subramanian (p. 3): `k ≥ t ≥ (e(g+1))^{−1} 2^{⌊(g−1)/2⌋−2} − 2` for cubic
graphs of girth `g`, and note their linear bounds beat it "if the path-width
is less than 26". Translation for a cubic graph of girth `g`: `pw ≥
(3g − 10)/2` from 1.1, and `pw ≥ g + 2` from 1.2 when `g ≥ 9` (girth `≥ 9`
forces `k ≥ 10` by the table, then `g ≤ k − 2`). Classification **N**: a
girth argument through unavoidable configurations, in no family on record.
§4.2 does the arithmetic on the open cages: dead. The cross-check is worth
recording: the five values Theorem 1.3 certifies on graphs the dataset holds
— Petersen 5 (`pwc-16021`), Heawood 6 (`pwc-15984`), Pappus 7 (`pwc-16027`),
McGee 8 (`pwc-16010`), Tutte–Coxeter 9 (`pwc-16065`) — all agree with the
dataset's `certified:refutation` widths, by an independent program.

Alspach, Dyer, Hanson & Yang (ESCAPE 2007, LNCS 4614, 516–527): abstract
only — lower bounds on the edge search number "using minimum degree, girth,
chromatic number, and colouring number". Degree, colouring number
(`= degeneracy + 1`) and chromatic number (`≤` colouring number) are family
**D**; the girth clause is of Chandran–Subramanian's kind. Yang, Dyer &
Alspach (DM 2009): sweep number against clique number, and the minor
monotonicity Clarke & Messinger use. Both to obtain for the record; neither
can pass `tw + 1` on the cages (the 12-cage has `tw ≤ pw = 26` and
degeneracy 3).

### 2.15 Connected, non-deterministic and zero-visibility games — Dereniowski (2011, held), Fomin, Fraigniaud & Nisse (2009), Mazoit & Nisse (2008), Dereniowski, Dyer, Tifenbach & Yang (2015), Xue, Yang & Zilles (2022)

Connected search bounds the wrong way (`cs ≥ s`; Dereniowski's Thm 4 is
`cs ≤ mcs ≤ 2s + 3`, Thm 2 `cpw ≤ 2pw + 1`): a lower bound on `cs` says
nothing about `s`. Non-deterministic search `s_q` sits between `tw + 1` and
`pw + 1` and is monotone (Mazoit & Nisse), so a lower bound on any `s_q`
transfers to `pw + 1`; no such bound beyond `tw + 1` is in print.
Zero-visibility cops and robber is bounded above by `pw` and below by no
function of it (DDTY 2015, abstract), so Xue, Yang & Zilles's matching-number
lower bounds on `c_0` transfer to `pw` but are structurally far below it.
Nothing to use; the last two are listed in `MISSING.md` for completeness.

### 2.16 Lengauer (1981, held); narrowness (Kornai & Tuza 1992)

Lengauer's vertex separator game is `vs` (`EdgeSeparation.lean`, `vsg_eq_max`)
and its pebbling reductions are exact; the paper's lower bounds are for
pebbling specific DAGs (pyramids, trees), not for undirected `vs`. Kornai &
Tuza add no bound beyond `ν = pw + 1` and the tree theorem of §2.3.

## §3. Classification against the families on record

| our family | rows of the table it absorbs | why |
|---|---|---|
| D (degree, clique, degeneracy; `≤ tw + 1`) | 5, 6, 7 (three of four clauses), 11, 15 (the clique half), 16 (the block half), 20 | each is a statement about a vertex, a clique or a degree sequence that a lazy fugitive already loses to (§1, last paragraph) |
| H (Harper, one prefix size) | 9, 18 (vertex version) | CKS Thm 3 is Harper through the interval member; the edge version is §4 |
| M (minors, obstructions) | 6, 12, 13, 17 | minor monotonicity of `s`, `ns`, `ms`, `lw`, `pw`; obstruction sets known to `k = 2` or `3` |
| B (three linked branches) | 1, 2, 3, 4, 16 | Parsons, Scheffler, EST, Kornai–Tuza and Chou et al. are the same lemma in five vocabularies |
| G, inside the three operators | 10, 15 (the counting half: a frame of two cliques) | — |
| G, consecutive orders (the band) | 14, the `P_n □ P_n` half of 15 | "the first time a line is clean" is a separation of one order and the next placement one of the next: the band, by hand, on one family |
| N | 18 (edge version), 19 | §4 |

Nothing in rows 1–17 or 20–25 can exceed the searched contraction minor on
the 338 (tight on 327, `obstruction_search.md` §0), and on the 11 residual
dense instances every one of them is a `tw + 1`-type bound or a Harper-type
bound whose ceilings are measured there (`spectral_bound.md` §0: 13–42 below
the optimum).

## §4. The two "genuinely different" candidates, on the open cubic cages

The five open cubic vertex-transitive cages in the dataset (widths are the
best layouts on record, floors the certified minor or spectral floors after
loop0013's two passes and `reports/spectral_floor_integration.md`):

| record | graph | `n` | girth | width (open) | floor | `floor + 2` |
|---|---|---:|---:|---:|---:|---:|
| pwc-15968 | Foster | 90 | 10 | 20 | 15 | 17 |
| pwc-15936 | Biggs–Smith | 102 | 9 | 19 | 16 | 18 |
| pwc-16006 | Ljubljana | 112 | 10 | 22 | 16 | 18 |
| pwc-15932 | Balaban 11-cage | 112 | 11 | 24 | 17 | 19 |
| pwc-16064 | Tutte 12-cage | 126 | 12 | 26 | 20 (spectral, Thm 1) | 22 |

### 4.1 The cutwidth route: Harper on the edge boundary

**Statement.** For a graph `G` with `Δ(G) ≤ 3`,
`pw(G) = vs(G) ≥ es(G) − 2 = cw(G) − 2 ≥ max_t Φ_E(t) − 2`, where
`Φ_E(t) = min_{|S| = t} e(S, V ∖ S)` is the edge-isoperimetric profile.
Ingredients: `vs ≤ es ≤ vs + 2` (Ellis, Sudborough & Turner 1994 Thm 2.1;
`EdgeSearchFull.lean`, a theorem); `es = cw` for `Δ ≤ 3` (Makedon &
Sudborough 1989, as cited by Fomin & Thilikos 2008 p. 13 and Ellis et al.;
checked by us on every subcubic atlas graph with `n + 2m ≤ 20`,
`subexp_pathwidth.md` §7.5, not proved here); `cw ≥ max_t Φ_E(t)` (the cut
after position `t` of any layout is the boundary of a `t`-set). Worked
example: `K_{3,3}` has `pw = 3`, `cw = 5` (the layout `a_1 b_1 a_2 b_2 a_3 b_3`
cuts 4, 5, 4; no cut below 5 is possible since `Φ_E(3) = 5`), so the bound
gives `pw ≥ 3`, tight (Harper's vertex version is tight here too: every
3-set of `K_{3,3}` has all three vertices on its boundary, `Φ_V(3) = 3`);
`K_4` has `cw = 4`, `pw = 3`, so the edge bound gives 2 where the clique
bound gives 3. The vertex version is Harper's bound, `pw ≥ max_t Φ_V(t)` with
`Φ_V(t) = min |∂_in S|`; on a cubic graph every boundary vertex has one, two
or three boundary edges, so `Φ_V(t) ≤ Φ_E(t) ≤ 3 Φ_V(t)`, and the edge version
can in principle sit up to `3 Φ_V − 2` where the vertex version sits at
`Φ_V`. That is why it is of a different kind: it reads the same prefix as
Harper but counts edges, which on cubic expanders (the cages are expanders:
`μ₂ = 3 − √6` on the 12-cage) is the quantity that is large.

**Where it stands today.** The only value on record is spectral: on the
12-cage `μ₂ n / 4 = 0.5505 · 126 / 4 = 17.3`, so `bw ≥ 18`, `cw ≥ 18`,
`pw ≥ 16` — four below the record floor of 20. The spectral number is a
relaxation; the exact `max_t Φ_E(t)` is unknown on every one of the five, and
so is the exact bisection width. Against it: Monien & Preis (2006) prove
`bw ≤ (1/6 + o(1)) n` for cubic graphs, which on 126 vertices is about 21
plus the `o(n)` term, and the profile of an expander peaks near `t = n/2`, so
the route tops out near `bw − 2 ≈ 19–21` on the 12-cage against a floor of
20. On Foster (`n = 90`, spectrum `±3, ±√6, ±2, ±1, 0`, so the same `μ₂`)
the spectral value is `12.4`, bound 11, floor 15.

**Cost.** A ceiling on `max_t Φ_E(t)` — a `t`-set with small edge boundary at
every `t` — is a local search over sets, seconds per graph; an exact
`Φ_E(t)` at one `t` is a SAT or ILP question of the kind
`learning/obstruction_expansion.py` already asks for `Φ_V`, minutes to hours
at `n = 126`; the exact bisection width of a 126-vertex cubic graph is a
small ILP with a known good formulation.

**Kill criterion (written before any measurement).** Dead if, on each of the
five cages, the local-search ceiling on `max_t Φ_E(t)` is at most `floor + 2`
(17, 18, 18, 19, 22). Alive on a cage if an exactly proved `Φ_E(t) ≥ floor +
3` at some `t`, in which case the floor rises to `Φ_E(t) − 2` with a
certificate (the DRAT or ILP proof of the inner minimum, the two cited
theorems, and the `es = cw` statement, which would then need a held copy of
Makedon & Sudborough or its own proof). Expected verdict: dead by one or two
on the 12-cage, by more on the others; the ceiling that says so is the
measurement, and it is not on record.

**What it is not.** It is not a bound for the corpus (no MOSP graph with more
than one pattern per customer is subcubic), and it is not a bound for
non-cubic dataset classes without a weaker constant (`pw ≥ cw/Δ` in general,
and `cw ≤ vs(G°) ≤ cw + ⌊Δ/2⌋ − 1` on the degree-clique expansion,
`subexp_pathwidth.md` row 16, gives nothing better).

### 4.2 Bachtler–Heinrich's girth bound: dead by arithmetic

From Theorem 1.2, a cubic graph of girth `g ≥ 9` has `pw ≥ g + 2`; from
Theorem 1.1, `pw ≥ (3g − 10)/2`. On the five: Tutte 12-cage `pw ≥ 14`
(floor 20), Balaban 11-cage `≥ 13` (17), Foster and Ljubljana `≥ 12` (15,
16), Biggs–Smith `≥ 11` (16). Every value is below the floor on record, so
the family is dead on the open cages with no measurement needed; and the
bound is monotone in girth alone, so no subgraph or minor of a cage improves
it. It stays worth citing: it is the only pathwidth-specific girth bound in
print, it is tight on the Petersen, Heawood, McGee and Tutte–Coxeter graphs,
and its small-case table is an independent certification of five dataset
values (§2.14).

## §5. Closed here, so that it is not proposed again

- **Block-graph subgraphs as floors** (Chou et al. 2008 through subgraph
  monotonicity): on the 338 the searched minor is tight on 327 and a
  subgraph floor cannot exceed a minor floor; on the 11 residual dense
  instances a block subgraph of a graph with `ω ≤ 25` and optimum 57–99 has
  node search number at most about `ω + (number of branches)`, far below.
- **Interval-completion bounds**: the interval literature's lower bound is
  the clique number, and the one structural theorem — `pw = tw` on
  cocomparability graphs (Habib & Möhring 1994) — is exactly the regime our
  gap instances are not in.
- **Connected and zero-visibility games**: wrong direction, or unboundedly
  weak (§2.15).
- **Products and grids**: exact theories on their families, equal to `tw` or
  `tw + 1` there, not computable off them (§2.11, §2.12).

## §6. Literature: held, open, to obtain

Held and read in `literature/`: Megiddo et al. 1988; Ellis, Sudborough &
Turner 1994 (scan, no text layer); Kirousis & Papadimitriou 1986; BRST 1991;
Kinnersley & Langston 1994; Takahashi, Ueno & Kajitani 1994; Peng et al.
2000; Bodlaender & Fomin 2000; Chandran, Kavitha & Subramanian 2003; Fomin &
Høie 2006; Fomin & Thilikos 2006 (Halin); Chou et al. 2008; Ellis & Warren
2008; Coudert, Huc & Sereni 2009; Dereniowski 2011; Coudert, Huc & Mazauric
2012; Clarke & Messinger 2019; Kobayashi & Nakahata 2021; Lengauer 1981;
Bezrukov et al. 2004. Read from open copies in a scratch directory and not
kept: Fomin & Thilikos 2008 (GRASTA reprint); Kornai & Tuza 1992 (SZTAKI
eprint); Thilikos 2000 (Utrecht TR CS-1997-35); Bachtler & Heinrich 2023
(arXiv 2010.08373) and Bachtler's dissertation (KLUEDO); Kehagias, Hollinger
& Gelastopoulos 2009 (arXiv 0905.3359, no bounds); Bodlaender et al. 2025
(EJC, for the cutwidth citations); Ding & Dziobiak 2013 (LSU preprint). The
list of papers worth obtaining, with open links, is the new heading in
`literature/MISSING.md`, "Lower bounds: the search-game and interval members
of the complex (2026-11-11)".
