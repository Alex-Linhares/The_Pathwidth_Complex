# Lower bounds in the VLSI members of the pathwidth complex: a survey

*2026-11-11. One session, outside the loops. Scope: gate matrix layout,
one-dimensional logic (gate assignment, Weinberger arrays), PLA folding, and
interval-graph completion with minimum clique number. The search-game members
(node, edge, mixed search), narrowness, split bandwidth and the MOSP family
belong to sibling surveys and are mentioned here only where a VLSI paper
states a bound in their vocabulary. Nothing was downloaded into `literature/`;
nothing in `solutions/` or the dataset was touched; the only computation is
the toy brute force of §3 on random instances of 6–10 nets.*

Companion documents: `paper1/equivalences.md` (the dictionary used below),
`reports/obstruction_search.md` §0 (the families and their measured
ceilings), `reports/blockage_class.md` §0, `reports/spectral_bound.md` §0,
`reports/chain_lp.md` §0, `paper1/latex/sec9f_appendix_dual.tex` (the dual),
`reports/pathwidth_lower_bounds_survey.md` (the treewidth-side bounds).

## 0. Summary

**The question.** A lower bound developed in the VLSI literature of
1979–1997 for its own problem is, through the equivalences of
`paper1/equivalences.md` rows 2–5, a lower bound on pathwidth + 1 of the net
graph (the MOSP graph: nets are customers, gates are patterns, two nets are
adjacent when they share a gate). The owner asked for every such bound, its
exact statement, its translation, and its classification against the
families already measured in this project: degree/clique/degeneracy (all
`≤ tw + 1`, `Sandwich.lean`), Harper's one-prefix isoperimetric bound,
minors and obstructions, branchings, blockages, spectral, LP.

**The answer, in one paragraph.** The VLSI literature on these four problems
produced **one lower bound it computed** and **three it proved and did not
compute**. The computed one is the **maximum column sum** of the net–gate
matrix — the largest number of nets at one gate, our trivial bound `lb_p` —
stated as "self-evident" by Wing, Huang & Wang (1985, §V), as §2.1 "Lower
Bound of the Solution" by Hu & Chen (1990, p. 837), and used as the `LB`
column of every heuristic table since (Oliveira & Lorena 2002 Table I;
Linhares 2001 Tables 3.1 and 3.4, where it is `LB1`). Hu & Chen say in the
same paragraph that it "will not be optimal with the presence of cycles" and
cite a **"bottleneck hypercycle"** bound from Yu's 1986 Illinois thesis (pp.
55–57) as "the optimal lower bound", NP-complete to find and, in their
words, of no practical use; the thesis is access-restricted and we could not
read it (§2.8). The three proved-but-uncomputed bounds are all in the
graph-theoretic papers: the **clique subgraph and clique minor** bounds
(Kinnersley & Langston 1994, Lemma 5.13 and Corollary 5.14, from Fellows &
Langston 1987 Lemma 4.1), the **obstruction-set** characterisation (every
k-GML obstruction as a minor certifies k + 1 tracks; the set is known
completely only for k ≤ 3, 110 graphs), and, in Möhring's 1990 chapter, the
**split bound** (Lemma 3.11: a split whose join is `K_{a,b}` forces
`min(a, b)` searchers, p. 35) and the **branch lemma** (Lemma 3.12, p. 36,
the Fellows–Langston / Kirousis–Papadimitriou argument). Each of these is a
member of a family this project has already measured to its ceiling: the
column sum and the clique bounds are degree/clique type (`≤ tw + 1`); the
split bound is a `K_{a,b}` subgraph bound, hence `≤ tw`, and one weaker than
the subgraph statement; obstructions are family M, where the searched minor
is tight on 327 of the 338 gap instances; the branch lemma is family B,
which closes nothing. The Brazilian MOSP bounds were applied *to* the VLSI
circuits (Linhares 2001 Table 3.4, `LB5` = arc contraction = contraction
degeneracy + 1), not the other way round. **PLA folding** contributes
nothing transferable: simple folding is not pathwidth + 1 (row 4 of the
master table, false as stated), and every bound in that literature (Hu &
Kuo 1987's edge/vertex bounds on the folding size, the branch-and-bound
bounds of Lewandowski & Liu 1984, Ravi & Lloyd 1988's inapproximability) is
a bound on the size of a *simple* folding; multiple folding is gate matrix
layout under another name (Möhring Thm 3.14) and carries no bound of its
own. The **interval completion / minimum clique number** community states
the problem (Kashiwabara & Fujisawa 1979; Ohtsuki et al. 1979 §III, 1981)
and never a bound beyond `ω(G)`; the sparse-matrix profile/wavefront
literature, whose maximum wavefront is `vs + 1`, has heuristics and no lower
bound (Kumfert & Pothen 1997; Reid & Scott 1999). Díaz, Petit & Serna's
survey (2002, §9.2, p. 339) gives exactly one lower bound for `VERTSEP`, the
Mohar–Poljak spectral separator inequality, which is the family
`reports/spectral_bound.md` measured dead. **Verdict: already covered, cite;
no live candidate from this family.**

**The one candidate examined, and killed at toy scale (§3).** The VLSI
"net-cut" view suggests Harper's bound in gate vocabulary: for each `t`, the
minimum over gate sets `P` of size `t − 1` and a next gate `p` of the number
of nets open while `p` is laid out, `|cross(P) ∪ nets(p)|`, is a lower bound
on the track count (every gate order passes through such a state at every
`t`). It is a one-prefix relaxation on the gate side, valid by the same
argument as Harper's, and the natural thing a VLSI author would have
written; we found no statement of it in print. Measured by brute force on
500 random instances of 6–10 nets against `max(Harper + 1, ω, lb_p,
tw + 1)`: **above the reference on 0 of 500**, equal on 81, equal to the
optimum on 74; and the worked example of §3.2 shows it does not even
contain the trivial bound (a `K₄` gate plus a pendant path: optimum 4,
gate-cut bound 2). Kill criterion stated before measuring: dead if never
above the reference on random instances where every quantity is exact. Met.
Not proposed for the gap instances.

**A side finding for the record, not a run.** The eleven Hu & Chen circuits
the benchmark hunt holds (`paper1/benchmarks/raw/lorena_vlsi/`) are in the
dataset: ten are certified at their published best (`paper1/dataset.md` §5),
and **W4 (202 nets, 141 gates) is open at 28 against a best known of 27**,
with the literature's own floors at 18 (`LB1`) and 19 (`LB5`, Linhares 2001
Table 3.4). It is an unsolved problem of the complex and, under the owner's
rule, the kind compute goes to. Nothing was started.

### The table

Technique, source with page, statement in the problem's own terms,
translation, classification, verdict. "Tracks" is the gate matrix track
count `t(M) = pw(G_M) + 1` (master table row 2); "ns" the node search
number `= pw + 1` (row 6).

| # | technique | source | statement, in its own terms | in pathwidth terms | family | verdict |
|---|---|---|---|---|---|---|
| 1 | maximum column sum | Wing, Huang & Wang 1985 §V ("self-evident"); Hu & Chen 1990 §2.1 p. 837; Oliveira & Lorena 2002 Table I; Linhares 2001 §3.3 `LB1`, Tables 3.1, 3.4 | tracks ≥ max over gates of the number of nets at the gate; "if the layout uses no more tracks than this lower bound, the solution is optimal" | `pw + 1 ≥ max pattern size` (a clique) | clique, `≤ tw + 1` | covered: it is `lb_p` (`_lower_bound`'s trivial component); cite |
| 2 | cycle remark | Hu & Chen 1990 §2.1 pp. 837–838 | with a direct cycle a–b–c–a or an indirect cycle a–b–c–d–a, three tracks are needed even if each gate carries two nets | `K₃` and `C₄` in the net graph have pw 2 | clique / `≤ tw + 1` (tw(C₄) = 2) | covered; cite as the period's statement that column sums miss cycles |
| 3 | bottleneck hypercycle | Hu & Chen 1990 p. 838, citing Yu 1986 pp. 55–57; used on `wsn` (8 tracks, column sum 4; p. 844) | "the size of a bottleneck hypercycle is the optimal lower bound of track numbers"; "finding this theoretical optimal lower bound is a very difficult (an NP-complete) problem" | unread; a cycle of gate-cliques is a minor with known pathwidth, so provisionally minor type | minor / obstruction (provisional) | **not read**; the thesis is restricted (§2.8); `wsn = 8` is certified here by refutation, consistent with its claim |
| 4 | `K_k` subgraph | Kinnersley & Langston 1994 Lemma 5.13 p. 177, from Fellows & Langston 1987 Lemma 4.1 | if `G` contains `K_k` as a subgraph then `G` has cost at least `k`, with an optimal permutation placing the clique's edges in adjacent columns | `pw + 1 ≥ ω` | clique, `≤ tw + 1` | covered (`card_le_pathwidth_add_one_of_isClique`); cite |
| 5 | `K_k` minor | Kinnersley & Langston 1994 Corollary 5.14, 5.15 p. 177; Möhring 1990 (3.7) p. 33 | if `G` contains `K_k` as a minor then cost ≥ `k`; `K_k` is an obstruction for (k − 1)-GML; `t(H) ≤ t(G)` for `H` a minor of `G` | Hadwiger number ≤ pw + 1 | minor (clique minor), `≤ tw + 1` | covered (`pathwidth_gt_of_minorOf`, family M); cite |
| 6 | obstruction sets | Kinnersley & Langston 1994 (110 obstructions for 3 tracks, pp. 169, 199); Fellows & Langston 1987 (`K₃`, subdivided claw for 2 tracks); Govindan, Langston & Ramachandramurthi 1997 (six densest, approximate test) | `G` has cost > k iff some k-GML obstruction is a minor of `G`; Lemma 5.10: `G ∖ v` contains a (k − 1)-obstruction iff every optimal permutation has a cost-k column with a 0 in row `v` | a complete minor certificate family for fixed k; pw ≥ k + 1 iff an obstruction is a minor | minor / obstruction | covered in principle (family M is the searched version); useless at pw 20–100 (the k = 4 tree obstructions alone number 117,480, Kinnersley 1992) |
| 7 | split bound | Möhring 1990 Lemma 3.11 p. 35 | a split `V₁ ∪ V₂` whose join is `K_{A₁,A₂}` forces `ns(G) ≥ min(|A₁|, |A₂|)` | `pw ≥ min(a, b) − 1`; the subgraph `K_{a,b}` gives `tw ≥ min(a, b)`, one better | `≤ tw` | covered and dominated by the treewidth ceiling; cite only |
| 8 | branch lemma | Möhring 1990 Lemma 3.12 p. 36, Prop. 3.13 (ternary tree); Fellows & Langston 1987 Lemma 4.3; Kirousis & Papadimitriou 1986 | a degree-3 vertex whose removal leaves three components of search number `t` forces `t + 1` | `branch_lemma` and `branch_lemma_separator` (`Sandwich.lean`) | branching (family B) | covered; closes 0 of 338 (`obstruction_search.md` §6); cite |
| 9 | arc contraction on VLSI circuits | Linhares 2001 Table 3.4 p. 40 (`LB5` of Yanasse, Becceneri & Soma 1999); Hu & Chen 1990 Table II | `LB5` on `v4470, w3, w4, x0` = 7, 14, 19, 7 against layouts 9, 18, 27, 11 | contraction degeneracy + 1 | degree, `≤ tw + 1` | covered; the MOSP bounds applied to the VLSI side, not a VLSI bound |
| 10 | min-net-cut | Hwang, Fuchs & Kang 1987 (abstract); Hong, Park & Kim 1989 (cut between seeds) | a modified min-net-cut gate ordering; "an ideal min-net-cut algorithm … is at worst a log n approximation" | recursive bisection, upper side; the implicit lower bound (a balanced cut) is Harper at one level in gate vocabulary | Harper type (gate side) | upper-bound heuristics; the lower-bound reading is §3, dead |
| 11 | gate-cut prefix bound (ours, from 10) | §3 of this report; no statement found in print | `tracks ≥ max_t min_{|P| = t − 1, p ∉ P} |cross(P) ∪ nets(p)|` | a one-prefix relaxation over gate sets | Harper type (gate side) | **dead**: 0 of 500 above the reference, does not contain `lb_p` |
| 12 | expected tracks, random matrices | Das, Deo & Prasad 1989 (LNCS 405, 280–290, abstract); Prasad 1986 MS thesis | an expression for the expected number of tracks under a probabilistic model | not a bound; a first-moment-style analysis of random gate matrices | — | to obtain for Appendix E's random-cover paragraph; nothing for the floors |
| 13 | spectral separator | Díaz, Petit & Serna 2002 §9.2 Thm 9.4 p. 339 (Mohar & Poljak 1993; Alon & Milman 1985), quoted for `VERTSEP` | `|C| ≥ 4λ₂|A||B| / (Δn − λ₂|A ∪ B|)` for a separator `C` of `A`, `B` | the prefix-separator spectral floor | spectral | covered: measured dead in `reports/spectral_bound.md` |
| 14 | PLA folding size bounds | Hu & Kuo 1987 (abstract: upper and lower bounds on the folding size in edges and vertices; tight upper bound for red bipartite graphs); Lewandowski & Liu 1984; Luby et al. 1982; Ravi & Lloyd 1988 | bounds on the size `s` of a simple folding; tracks = `|V| − s` (Möhring Prop. 3.15 p. 38) | simple folding is not `pw + 1` (master table row 4, false as stated) | — | not a pathwidth bound; multiple folding (= GML) has none of its own |
| 15 | interval completion | Kashiwabara & Fujisawa 1979; Ohtsuki et al. 1979 §III p. 677, 1981; Kumfert & Pothen 1997; Reid & Scott 1999 | the minimum clique number of an interval supergraph; minimal (not minimum) augmentations; wavefront heuristics | `θ = pw + 1` (row 5) | — | no lower bound stated beyond `ω`; nothing to transfer |

**What "we found no …" covers.** Searches in English, Japanese and Chinese
(§5) on the historic names ("gate matrix layout lower bound", "net cut",
"one-dimensional logic gate assignment lower bound", "PLA folding lower
bound", "interval graph completion lower bound", "minimum clique number
interval supergraph", "bottleneck hypercycle", "maximum wavefront lower
bound"), the reference lists of the held papers (Möhring 1990, Ohtsuki et
al. 1979, Wing et al. 1985, Fellows & Langston 1987/1989, Kinnersley &
Langston 1994, Linhares 2001, Linhares & Yanasse 2002, De Giovanni et al.
2013, Karoński & Szymkowiak 2001), and the open full texts of Hu & Chen 1990
and Govindan, Langston & Ramachandramurthi 1997. Not read: Yu 1986 (the one
object of a possibly different kind), Deo, Krishnamoorthy & Langston 1987
(abstract only; its dynamic programme needs no bound), Das, Deo & Prasad
1989 (abstract only), Wing et al. 1985 beyond p. 220 (a scan with no text
layer; the §V facts are taken from `literature/MISSING.md`'s reading note),
Hwang, Fuchs & Kang 1987 and Huang & Wing 1989 (abstracts only), and every
PLA paper (abstracts only). "Hwang, Dutt & Ouyang" and "Lin & Wing" in the
brief: we found no gate matrix paper under either author list; the first is
presumably Hwang, Fuchs & Kang 1987, the second Wing's own 1982–1983 ISCAS
and ICCAD papers (Lin & Gajski 1987 is a layout expert system). "Dominating
net": no lower bound by that name; in this literature dominance is the
preprocessing rule (a net whose gates lie inside another's), Yanasse & Senne
(2010) operation 2.

## 1. The dictionary

From `paper1/equivalences.md`: tracks of a net–gate matrix `M` equal
`Z(M) = pw(G_M) + 1` (row 2, `NetGateMatrix.tracks_eq_pathwidth_add_one`);
one-dimensional logic tracks equal the interval thickness `θ(H) = pw(H) + 1`
of the connection graph (row 3); `θ = ns = pw + 1` (rows 5–6); multiple PLA
folding `= pw + 1`, simple folding is not within a constant (row 4). Möhring
1990 is the one source that states all four in one place: Theorem 3.2 (p.
29, tracks = least chromatic number of an interval augmentation), the
left-edge remark (p. 31, "the minimum number of tracks for an augmented
net-gate matrix `M^π` is equal to the maximum column sum of `M^π`"), Theorem
3.3 (p. 32, MPP ≡ IGA), Proposition 3.5 (p. 32, `pw(G) = t(G) − 1`), Theorem
3.9 (p. 34, `ns(G) = t(G)`), Theorem 3.14 (p. 36, path partitions ≡ IGA),
Proposition 3.15 (p. 38, PLA folding as a maximum folding set).

So a lower bound on tracks, on `θ`, on `ns`, or on the number of paths in a
path partition is a lower bound on `pw + 1`; a lower bound on the size of a
*simple* folding set, or on bandwidth, profile, or cutwidth, is not (the
last three sit above pathwidth, `Sandwich.lean`, `EdgeSeparation.lean`).

## 2. The sources, one by one

### 2.1 Ohtsuki, Mori, Kuh, Kashiwabara & Fujisawa (1979), held

§II, p. 676–677: for a fixed gate order the nets are intervals, "the number
of tracks required for between-gate wiring is equal to the clique number
(chromatic number) of the internal graph"; §III, p. 677: "given a graph `H`,
find a supergraph by adding a set of edges, which is an interval graph and
has the least clique number"; NP-complete by Kashiwabara & Fujisawa [11]
(p. 678). Theorem 3 (p. 678) reads a gate sequence off any ordering of the
dominant cliques of an interval augmentation; §IV gives a polynomial
algorithm for a *minimal* augmentation (Theorem 4) and its boundary-gate
form (Theorem 5); §V reports 30 random minimal augmentations per circuit on
seven 48-gate circuits (Table IV). **No lower bound is stated anywhere in
the paper**; the only inequality is `tracks ≥ ω(H)`, implicit in "clique
number of a supergraph". Classification: the dictionary itself.

### 2.2 Kashiwabara & Fujisawa (1979) and Ohtsuki, Mori, Kashiwabara & Fujisawa (1981), not held

The NP-completeness of minimum-clique-number interval augmentation (ISCAS
1979, two titles circulate, `literature/MISSING.md`), and the `O(nm')`
minimal-augmentation algorithm (JCSS 22(1), 60–97). Both are about the
problem's complexity and about minimal (inclusion-wise) completions; neither
abstract mentions a bound, and the minimal-completion literature that
followed (Heggernes, Suchan, Todinca & Villanger 2007; Crespelle & Todinca)
is about fill-in, not clique number. Nothing to transfer.

### 2.3 Wing (1982, 1983) and Wing, Huang & Wang (1985), held as a scan

The 1985 paper formulates CMOS gate matrix layout as two assignments `f`
(gates → columns) and `h` (nets → rows) with vertical diffusion constraints
(abstract, p. 220). The held file has a text layer only on p. 220; the
reading note in `literature/MISSING.md` (2026-09-27) records §V's three
"self-evident" facts, the third being **rows ≥ max nets per gate** — the
trivial bound, in the VLSI vocabulary — and Appendix A's greedy interval
graph heuristic with random restarts (Fig. 13: 90 trials on a 144-net
circuit span clique sizes 34–55). Classification: clique type. Verdict:
cite as the earliest VLSI statement of `lb_p` we hold.

### 2.4 Deo, Krishnamoorthy & Langston (1987), abstract; Das, Deo & Prasad (1989), abstract

IEEE TCAD 6(1), 79–84: a subset dynamic programme guaranteeing the optimum
(Held–Karp over net sets; no bound needed), an efficient two-track test,
unbounded-ratio families for the published heuristics, and the theorem
Möhring restates as 5.1 (p. 47): unless P = NP no polynomial algorithm is
within an additive constant of the optimum. Das, Deo & Prasad (LNCS 405,
280–290) improve the DP's time and space, report that exact solutions "take
very long even for small matrices", and "derive an expression for the
expected number of tracks" under a probabilistic model, from Prasad's 1986
Washington State MS thesis. The expectation is not a bound; it is the
period's version of the random-cover analysis of Appendix E
(`CliqueCoverMoment.lean`, `reports/random_graph_first_moment.md`) and is
worth obtaining for that paragraph's related work. Classification: none
(exact algorithm; probabilistic analysis).

### 2.5 Fellows & Langston (1987, 1989, 1991), 1987 and 1989 held

1987 Lemma 4.1 (column expansion, both directions) is the matrix form of
Yanasse's Proposition 5 and the tool behind every clique statement in this
family; Lemma 4.2 is minor-closure of "≤ k tracks"; Lemma 4.3 is the branch
construction with its proof (`literature/MISSING.md` entry). 1989 Theorem 7
is `tracks = pw + 1`. The 1991 paper (*Integration* 12(3), 321–337, not
held) is about self-reduction from decision to layout; its abstract carries
no bound. Classification: dictionary; branch lemma (family B).

### 2.6 Kinnersley & Langston (1994), held; Kinnersley (1989, 1992)

DAM 54, 169–213. The bound statements, on pp. 176–177: **Lemma 5.10** (for
`G` of cost `k` and any vertex `v`, `G` has an optimal permutation in which
every cost-`k` column has a nonzero in row `v` iff `G ∖ v` contains no
(k − 1)-GML obstruction; the proof's second half is the one-row extension
argument); **Corollary 5.11** (an obstruction has cost exactly `k + 1` and an
optimal permutation with `v` live in every full column); **Lemma 5.12**
(adding an edge raises the cost by at most one); **Lemma 5.13** (`K_k`
subgraph ⇒ cost ≥ k, with the clique's edges in adjacent columns, "follows
immediately from Lemma 4.1 of [6]"); **Corollary 5.14** (`K_k` minor ⇒ cost
≥ k); **Corollary 5.15** (`K_k` is an obstruction for (k − 1)-GML). The
paper's purpose is the 110-element obstruction set for three tracks; Lemmas
5.1–5.9 are structural exclusions (no two long pendant paths, at most three
pendant paths, no two consecutive degree-2 vertices for `k > 2`, …), which
are properties of *minimal* no-instances and not bounds. Kinnersley (1992,
held) adds the tree-obstruction recurrence and the counts 2, 10, 117,480
for k = 2, 3, 4. Classification: clique minor (5.13–5.15, `≤ tw + 1`);
obstruction minors (family M). Verdict: covered; the obstruction route is
hopeless at our widths and the clique route is in `_lower_bound`.

### 2.7 Govindan, Langston & Ramachandramurthi (1997), read from the open UTK copy

UT-CS-97-345, "Constructive algorithms based on graph minors": a linear-time
*approximate* three-track test that checks only the six smallest of the 110
obstructions (§5.1, 4 to 22 vertices), with self-reduction to produce a
layout; Tables 1–3 show it correct on all but a handful of 1,000 random
graphs per size at edge probabilities 1/2, 1/3, 1/4. The lower-bound content
is exactly "an obstruction is a minor ⇒ cost ≥ 4"; the paper's own point is
that the larger obstructions are sparser and harder to test. Classification:
minor / obstruction. Nothing new for us.

### 2.8 Hu & Chen (1990) GM-Plan, read from the open Wisconsin copy; Yu (1986), restricted

IEEE TCAD 9(8), 836–845. §2.1 "Lower Bound of the Solution" (p. 837):
"the number of tracks required must be at least equal to the largest number
of nets connecting to a single gate … If the resulting gate matrix layout
uses no more tracks than this lower bound, the solution is optimal. However,
this lower bound will not be optimal with the presence of cycles in a given
circuit topology." The two examples (p. 838): a direct cycle a–b–c–a (three
nets pairwise sharing a gate: `K₃`) and an indirect cycle a–b–c–d–a (a
"hypercycle" in the sense of [17, p. 55], Hu & Kuh's chapter): `C₄` in the
net graph; both need three tracks with two nets per gate. Then: "**Yu proved
that the size of a 'bottleneck hypercycle' is the optimal lower bound of
track numbers required in a gate matrix layout [21, p. 56]. Unfortunately,
finding this theoretical optimal lower bound is a very difficult (an
NP-complete) problem. In practice, it does not provide any guidance for
finding an optimal solution.**" On p. 844 the 8-track layout of `wsn` "is
proved to be optimal by Yu [21, p. 57] as it is the size of the 'bottleneck
hypercycle' in that circuit", against a column-sum bound of 4; the 5-track
`vw2` "is verified by hand".

[21] is Meng-Lin Yu, *Automatic random logic layout synthesis — a module
generator approach*, PhD, University of Illinois at Urbana-Champaign, 1986
(IDEALS item 69722, restricted to the Illinois community; ProQuest). We
could not read it, and the phrase "bottleneck hypercycle" occurs nowhere else
we searched. What can be said without it: a hypercycle in Hu & Kuh's sense
is a cyclic sequence of gates with consecutive gates sharing nets; its
"size" plausibly counts the nets a cut of the cycle must cross plus the nets
at the cut gate, i.e. the pathwidth + 1 of a ring of gate-cliques, which is a
contraction minor of the net graph with a closed-form width; "optimal"
likely means "the best bound of its kind", not a min–max theorem (a min–max
for pathwidth is Bienstock–Robertson–Seymour–Thomas 1991, and the sentence
"NP-complete to find" fits a maximisation over substructures, as for cliques
and minors). Our provisional classification is therefore minor type, and on
`wsn` our own record (certified at 8 by refutation, `paper1/dataset.md` §5)
agrees with Yu's value. **This is the one item of the survey that could be
of a different kind, and it cannot be settled without the thesis**; it is
recorded under the new heading in `literature/MISSING.md` with the IDEALS
link.

The rest of GM-Plan is an upper-bound method (hierarchical subgoals,
most-constraint and least-impact policies), and Table II (p. 844) is the
origin of the eleven circuits in `paper1/benchmarks/raw/lorena_vlsi/`.

### 2.9 Chen & Hu (1990) GM_Learn; Oliveira & Lorena (2002); Linhares (2001), held

All three carry the column sum as their `LB`. Linhares 2001 §3.3 (p. 35,
Table 3.1) lists 30 circuits with `LB` = "the maximum column sum of the
original matrix, A", and Table 3.4 (p. 40) adds `LB5`, "the best lower bound
presented in [Yanasse et al., 1999]" (arc contraction = contraction
degeneracy + 1; `reports/pathwidth_lower_bounds_survey.md` row 4), on the
five circuits where microcanonical optimisation beat the record:

| circuit | `LB1` | `LB5` | previous | Linhares 2001 | dataset (2026) |
|---|---:|---:|---:|---:|---|
| v4000 | 5 | 5 | 6 | 5 | 5 certified:bound |
| v4470 | 5 | 7 | 11 | 9 | 9 certified:refutation |
| w3 | 11 | 14 | 21 | 18 | 18 certified:refutation |
| w4 | 18 | 19 | 34 | 27 | **28, open** (best known 27) |
| x0 | 6 | 7 | 13 | 11 | 11 certified:refutation |

The direction of transfer in 2001 was MOSP → VLSI: the Brazilian bounds were
the best floors those circuits had, and they were 2 to 8 tracks short. Our
search closed four of the five twenty-five years later; the fifth is the
open W4. Classification: clique and degree, `≤ tw + 1`.

### 2.10 Hwang, Fuchs & Kang (1987), Huang & Wing (1989), Hong, Park & Kim (1989), Fujii et al. (1987), Nakatani et al. (1986), Asano (1982), Leong (1986), Li (1983), abstracts only

Upper-bound methods: dynamic net-lists with a modified min-net-cut ordering
and the claim that "an ideal min-net-cut algorithm for optimal gate matrix
layout with n gate signals is at worst a log n approximation algorithm"
(Hwang, Fuchs & Kang, abstract — recursive bisection, the Leighton–Rao
argument in gate vocabulary); Asano's approximate search with zone-net
assignment (Huang & Wing 1989; Asano 1982 is a branch and bound whose bound
we could not read); a seeded ordering with a cut estimate and simulated
annealing for one-dimensional logic (Hong, Park & Kim 1989, the source of
the `Fujii`–`Data VI` circuits); heuristics (Fujii, Horikawa, Kikuno &
Yoshida 1987; Nakatani, Fujii, Kikuno & Yoshida 1986; Leong 1986; Li 1983).
None of the abstracts states a lower bound; the min-net-cut view motivates
the gate-side Harper bound of §3. Su & Sarrafzadeh (1990, *Integration*
9(1), 3–23) has no abstract online and is about functional-cell chaining
(Chakravarty, He & Ravi 1990 show that part NP-hard on series-parallel
networks). Classification: none (upper side).

### 2.11 Möhring (1990), held in full

The chapter's bound statements, in order. (3.7), p. 33: `t(H) ≤ t(G)` for a
minor `H` — minor monotonicity, the basis of the obstruction approach.
**Lemma 3.11**, p. 35: for a split `V(G) = V₁ ∪ V₂` whose crossing edges
form `K_{A₁,A₂}`, every recontamination-free search has a step with all of
`A₁` or all of `A₂` guarded, "so in particular `ns(G) ≥ min{|A₁|, |A₂|}`";
the proof is the recontamination argument. In pathwidth terms `pw ≥ min(a,b)
− 1`, and since `K_{a,b}` is a subgraph, `tw ≥ min(a, b)` already, so the
lemma is one short of the subgraph bound and under the treewidth ceiling.
**Lemma 3.12**, p. 36: the branch lemma (three components of search number
`t` at a degree-3 vertex force `t + 1`), with **Proposition 3.13** (complete
ternary tree: height + 1) — family B, and `TreeBound.lean`'s
`pathwidth_ternaryTree` (`pw = h` for the complete ternary tree of height `h`,
so `ns = h + 1`) is the formal version. P. 37: "vertex separation, min
cut linear arrangement, bandwidth … while vertex separation is equivalent to
node search [KP86], the other notions define bounds on `t(G)` [KP86]
[Bo88]" — the upper-side sandwich. **Theorem 4.4**, p. 40 (Gustedt): gate
matrix layout is NP-hard on chordal graphs, by a construction in which `t(M)
≤ 2|V(G)| − k` iff `G` has a partition `V₁, V₂, V₃` with `V₂` separating `V₁`
from `V₃` and `min(|V₁|, |V₃|) ≥ k` — an exact separator formula on one
special class, not a general bound. §5, p. 47–48: Theorem 5.1 (no additive
approximation, [DKL87]); Theorems 5.2–5.3 (Ravi & Lloyd on folding
approximation, maximisation version only; "both proofs fail for the perhaps
more natural minimization of the number of tracks"); and a note that work at
TU Berlin applies **Lagrangean relaxation and subgradient methods** to
constrained block folding via the matching-with-side-constraints form of
Proposition 3.17 [Mü89] — an LP-type bound for a PLA variant that is not
pathwidth; we found no later publication of it. Classification: 3.11 `≤
tw`; 3.12 family B; 4.4 none; §5 none.

### 2.12 PLA folding: Hachtel, Newton & Sangiovanni-Vincentelli (1982); De Micheli & Sangiovanni-Vincentelli (1983); Lewandowski & Liu (1984); Luby, Vazirani, Vazirani & Sangiovanni-Vincentelli (1982); Hu & Kuo (1987); Ravi & Lloyd (1988), abstracts only

The folding literature maximises the number of folded pairs `s`; tracks
(columns after folding) are `|V| − s` (Möhring Prop. 3.15, p. 38), and for
simple folding this quantity is not `pw + 1` (`PLAFolding.lean`,
`plaTracks_idMatrix_unbounded`). Bounds found: Hu & Kuo 1987 (*Networks*
17, 19–37) give "upper and lower bounds on the size of the folding in terms
of the number of edges and vertices" and a tight upper bound for red
bipartite graphs, with Möhring's Proposition 3.16 (maximum folding =
maximum `Z_{m,m}` subgraph); the branch-and-bound papers (Lewandowski &
Liu 1984 for bipartite folding; Grass 1982) use bounds on `s` we could not
read; Ravi & Lloyd 1988 (SIAM J. Comput. 17(4), 696–710) prove the three
folding variants equivalent for approximation and that a constant-factor
algorithm for bipartite folding gives a PTAS, "strongly suggesting" none
exists; Luby et al. 1982 (ICCC, 165–170) is cited by Ravi & Lloyd for
earlier theoretical results and has no abstract online. Multiple folding
(De Micheli & Sangiovanni-Vincentelli 1983, PLEASURE) is gate matrix layout
under row 4's "multiple folding = pw + 1", and its abstract states no bound.
Classification: none transferable.

### 2.13 Interval completion and the sparse-matrix wavefront, abstracts and held reports

Interval completion with few edges (fill-in) and with smallest max-degree
(interval degree ≥ bandwidth ≥ pw(G²)) are different parameters and sit
above pathwidth. The sparse-matrix literature's *maximum wavefront* of a
symmetric ordering is `vs + 1` of the adjacency graph; Kumfert & Pothen
(1997, held) and Reid & Scott (1999, 2005) are heuristics (Sloan, hybrid
spectral) and state no lower bound on the maximum wavefront; the only bound
in that literature we found is on the 2-sum (Kumfert & Pothen p. 151, an
eigenvalue bound on a sum objective). Classification: none.

### 2.14 Díaz, Petit & Serna (2002), held; Linhares & Yanasse (2002), held; De Giovanni et al. (2013), held; Karoński & Szymkowiak (2001), held

The survey's §9 (pp. 338–340) lists three lower-bound methods — the path
method (Juvan & Mohar, for MINLA and bandwidth), spectral bounds, and
fundamental cuts (cutwidth, MINLA) — and names `VERTSEP` under exactly one,
Theorem 9.4 (Mohar & Poljak): the separator inequality `reports/spectral_bound.md`
turned into a prefix floor and measured 7.5 stacks short on the 338. Linhares
& Yanasse 2002 state the MCUT reduction (Lemmas 1–2, pp. 1761–1762) and the
GMLP–MOSP correspondence (Proposition 2, p. 1763) and give no bound; De Giovanni et al. 2013 is
the connection-cost problem with tracks as a constraint `λ`, its dual bounds
are on cost, and it certifies `λ` by Chu & Stuckey's search (pp. 639, 641);
Karoński & Szymkowiak 2001 is the randomised three-track decision problem,
with the bound `m(BT_t) ≥ d(B)` on p. 186 being a counting step in their
probabilistic argument, not a track bound. Classification: spectral (DPS);
none otherwise.

## 3. The gate-cut prefix bound: stated, checked, killed

### 3.1 Statement and validity

Let the patterns (gates) be `p₁ … p_m`, `nets(p)` the customers of `p`, and
for a set `P` of patterns let `cross(P)` be the customers with a pattern in
`P` and a pattern outside `P`. For a product order `π` the stacks open while
`π(t)` is produced are exactly `cross(π(1..t−1)) ∪ nets(π(t))`, so the
optimum satisfies, for every `t`,

    opt ≥ Ψ(t) := min { |cross(P) ∪ nets(p)| : |P| = t − 1, p ∉ P },

and `opt ≥ max_t Ψ(t)`. This is Harper's argument with the gate prefix in
place of the customer prefix; it is the lower-bound half of the "net cut"
vocabulary of §2.10 (a balanced gate cut is `Ψ` at `t = m/2` without the
`nets(p)` term). We found no statement of it in print, and it is not claimed
as new.

### 3.2 Worked examples

- One pattern `{1,2,3,4}` plus a pendant path `{4,5}, {5,6}, {6,7}`: optimum
  4, Harper (customer side) `max_s Φ(s) + 1 = 2`, trivial bound 4, `ω = 4`,
  `tw + 1 = 4`, **gate-cut bound 2**: at every level the minimiser lays the
  big gate first and ends on a path edge (`P = {p₁, p₂, p₃}`, `p = p₄`:
  `cross = {5}`, open `= {5, 6}`), so the bound never sees the clique. The
  family does not contain the trivial bound, for the same reason Harper does
  not contain the clique bound.
- `K₄` as six two-net gates plus the same path: optimum 4, Harper 2, `ω = 4`,
  gate-cut 3.
- `C₄` as four two-net gates: optimum 3, Harper 3, `ω = 2`, `tw + 1 = 3`,
  gate-cut 3.

### 3.3 Measurement

Kill criterion, written before running: dead if on random instances small
enough that every quantity is exact, `max_t Ψ(t)` never exceeds the
reference `max(Harper + 1, ω, lb_p, tw + 1)`. 500 random instances (300 at
6–9 nets and 4–8 gates, 200 at 7–10 nets and 5–10 gates, gate sizes 2–4,
connected net graph), vertex separation by subset DP, Harper's profile and
the clique number by enumeration, treewidth by elimination-order DP, the
gate-cut bound by enumeration over gate subsets; every bound checked `≤`
optimum on every instance (an assertion):

| | above reference | equal | below | equal to optimum |
|---|---:|---:|---:|---:|
| seed 1, 300 instances | 0 | 55 | 245 | 50 |
| seed 2, 200 instances | 0 | 26 | 174 | 24 |

**Verdict: dead.** It is below the reference on 84% of the instances and
above it on none. No measurement on the 64 or the 338 is proposed. The
script is in the appendix.

## 4. What we can use, ranked

1. **Cite, already covered.** The maximum column sum (Wing et al. 1985 §V;
   Hu & Chen 1990 §2.1) as the VLSI form of `lb_p`; Kinnersley & Langston
   1994 Lemma 5.13 / Corollary 5.14 as the VLSI form of the clique and
   clique-minor bounds; Möhring 1990 Lemma 3.12 beside Fellows & Langston
   1987 Lemma 4.3 as the branch lemma; Möhring Lemma 3.11 as the one bound
   nobody computed (and one short of `K_{a,b} ⊆ G ⇒ tw ≥ min(a,b)`); the
   obstruction set of Kinnersley & Langston as the complete minor certificate
   family for k ≤ 3. One sentence in Appendix F's family paragraph covers all
   of them: *every lower bound the VLSI literature states for gate matrix
   layout is a clique, a clique minor, an obstruction minor, or a branch, and
   the only one it computed is the column sum.*
2. **Obtain and read, for a possible new kind.** Yu (1986), pp. 55–57, the
   bottleneck hypercycle: if it is a ring-of-cliques minor, it joins family
   M as a closed-form member; if it is something else, it is the only
   candidate this survey leaves open. Interlibrary loan; `literature/MISSING.md`.
3. **Obtain for Appendix E's related work, not for the floors.** Das, Deo &
   Prasad (1989) and Prasad (1986): the expected track count of a random gate
   matrix, the period's version of our random-cover first moment. Also
   Karoński, Scheinerman & Singer-Cohen (1999), already listed as highest
   priority under the random-graph heading.
4. **An unsolved problem, not a bound.** W4 (202 nets) is the one Hu & Chen
   circuit the dataset has open, at 28 against 27, with literature floors 18
   and 19. Whether the 27-track layout of Linhares (2001) exists on the file
   the hunt holds, and whether 27 or 28 is optimal, is a run the owner's
   compute rule points at. Not started.
5. **Dead, with a measurement.** The gate-cut prefix bound (§3).
6. **Dead by classification.** PLA simple-folding bounds (not pathwidth);
   bandwidth/profile/cutwidth bounds (above pathwidth); DPS's spectral
   `VERTSEP` bound (measured, `reports/spectral_bound.md`); the Lagrangean
   relaxation of constrained block folding (a PLA variant, never published
   as far as we found).

## 5. What was searched and not found

Web (standard and extended modes), 2026-11-11: "gate matrix layout lower
bound tracks net", with and without "Huang Wing Lin", "net cut" /
"min-net-cut", "dominating nets", "clique net intersection graph", "linear
programming relaxation", "hypercycle" / "bottleneck hypercycle";
"one-dimensional logic gate assignment lower bound" with Ohtsuki,
Kashiwabara, Fujisawa, Asano, Hong–Park–Kim, Fujii, IEICE / Trans. IECE;
"PLA folding lower bound" with Hachtel–Newton–Sangiovanni-Vincentelli,
Lewandowski–Liu, Luby et al., De Micheli, Hu–Kuo, Ravi–Lloyd; "interval
graph completion minimum clique number lower bound", "interval thickness
lower bound", "maximum wavefront lower bound"; Deo–Krishnamoorthy–Langston,
Das–Deo–Prasad, Prasad 1986, Fellows–Langston 1991, Kinnersley 1989, Su–
Sarrafzadeh, Makedon–Sudborough; Japanese ("ゲートマトリックス レイアウト
トラック数 下界", "一次元論理ゲート配置 区間グラフ 下界") and Chinese
("门矩阵 布图 轨道数 下界", "栅矩阵 布局 门矩阵") queries. The Japanese
queries returned nothing on the problem; the Chinese ones returned two
heuristics — Li Fuyi (1989, *Acta Electronica Sinica*, a non-iterative
one-dimensional logic gate ordering) and a self-organising-map gate-array
ordering in *J. Electronics & Information Technology* — and no bound. Wu &
Chan (1987, IEEJ, "A graph-theoretic approach for one-dimensional logic gate
assignment") surfaced by title only. The Hu & Kuh chapter (1985, *VLSI
Circuit Layout: Theory and Design*, IEEE Press), the source of "hypercycle"
by Hu & Chen's citation, was not located online.

Read in full: Möhring 1990, Ohtsuki et al. 1979, Kinnersley & Langston 1994,
Fellows & Langston 1987, Linhares 2001 ch. 3, Hu & Chen 1990, Govindan,
Langston & Ramachandramurthi 1997, Díaz, Petit & Serna 2002 §9, the
reference list of Kinnersley & Langston's 1992 UTK report. Abstract only:
everything else in the table.

## Appendix: the toy script of §3

Not committed as code (this report is the deliverable); kept here so the
numbers regenerate. Run with `python3 -I toy.py <seed> <trials>`.

```python
"""Toy brute force: gate-cut prefix bound vs customer Harper, trivial, clique, tw+1, optimum.
Small random MOSP instances only; nothing from the corpus."""
import random, itertools, sys
from functools import lru_cache

def inst(n, m, lo, hi, rng):
    return [frozenset(rng.sample(range(n), rng.randint(lo, min(hi, n)))) for _ in range(m)]

def graph(n, pats):
    adj = [0] * n
    for p in pats:
        for u in p:
            for v in p:
                if u != v: adj[u] |= 1 << v
    return adj

def popcount(x): return bin(x).count('1')

def inner_boundary(adj, S, n):
    return sum(1 for u in range(n) if S >> u & 1 and adj[u] & ~S)

def vs(adj, n):
    @lru_cache(None)
    def f(S):
        if S == 0: return 0
        bS = inner_boundary(adj, S, n)
        return min(max(f(S & ~(1 << v)), bS) for v in range(n) if S >> v & 1)
    return f((1 << n) - 1)

def harper(adj, n):
    phi = {}
    for S in range(1 << n):
        s = popcount(S); phi[s] = min(phi.get(s, 10**9), inner_boundary(adj, S, n))
    return max(phi.values())

def clique(adj, n):
    best = 0
    for S in range(1 << n):
        if all((adj[u] | (1 << u)) & S == S for u in range(n) if S >> u & 1):
            best = max(best, popcount(S))
    return best

def treewidth(adj, n):
    def Q(Sp, v):
        seen = 1 << v; stack = [v]; out = 0
        while stack:
            u = stack.pop(); nb = adj[u]
            out |= nb & ~Sp & ~(1 << v)
            inner = nb & Sp & ~seen; seen |= inner; x = inner
            while x:
                w = (x & -x).bit_length() - 1; x &= x - 1; stack.append(w)
        return popcount(out)
    @lru_cache(None)
    def TW(S):
        if S == 0: return 0
        return min(max(TW(S & ~(1 << v)), Q(S & ~(1 << v), v)) for v in range(n) if S >> v & 1)
    return TW((1 << n) - 1)

def gate_cut(n, pats):
    m = len(pats); cust = [sum(1 << u for u in p) for p in pats]; best = 0
    for t in range(1, m + 1):
        mn = 10**9
        for P in itertools.combinations(range(m), t - 1):
            inP = 0
            for i in P: inP |= cust[i]
            outP = 0
            for i in range(m):
                if i not in P: outP |= cust[i]
            cross = inP & outP
            for p in range(m):
                if p not in P: mn = min(mn, popcount(cross | cust[p]))
        best = max(best, mn)
    return best

def main(seed=1, trials=300):
    rng = random.Random(seed); wins = ties = eq_opt = 0; examples = []
    for _ in range(trials):
        n = rng.randint(6, 9); m = rng.randint(4, 8)      # seed 2 used (7, 10) and (5, 10)
        pats = inst(n, m, 2, 4, rng); adj = graph(n, pats)
        if any(a == 0 for a in adj): continue
        opt = vs(adj, n) + 1; H = harper(adj, n) + 1; triv = max(map(len, pats))
        om = clique(adj, n); tw1 = treewidth(adj, n) + 1; gc = gate_cut(n, pats)
        ref = max(H, triv, om, tw1)
        assert gc <= opt and H <= opt and om <= opt and tw1 <= opt
        if gc > ref: wins += 1; examples.append((n, [sorted(p) for p in pats], opt, H, triv, om, tw1, gc))
        elif gc == ref: ties += 1
        if gc == opt: eq_opt += 1
    print("trials", trials, "gc>ref", wins, "gc==ref", ties, "gc==opt", eq_opt)
    for e in examples[:5]: print(e)

if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 1, int(sys.argv[2]) if len(sys.argv) > 2 else 300)
```
