# Papers not yet downloaded

These papers are referenced in the project but could not be downloaded due to paywalls or server issues.

## Paywalled

- ~~**Kinnersley, N.G.** (1992). The vertex separation number of a graph equals its path-width. *Information Processing Letters*, 42(6), 345-350.~~ — **OBTAINED 2026-09-27**, see below.

- ~~**Yanasse, H.H.** (1997). On a pattern sequencing problem to minimize the maximum number of open stacks. *European Journal of Operational Research*, 100(3), 454-463.~~ — **OBTAINED 2026-09-27**, see below.

- **Faggioli, E. & Bentivoglio, C.A.** (1998). Heuristic and exact methods for the cutting sequencing problem. *European Journal of Operational Research*, 110(3), 564-575. DOI: 10.1016/S0377-2217(97)00269-7 — Elsevier paywall.

- ~~**Chu, G. & Stuckey, P.J.** (2009)~~ — NOW AVAILABLE as `chu_stuckey_2009.pdf`.
- **Linhares, A.** (2001). *Industrial pattern sequencing problems: some complexity results and new local search models*. PhD thesis (Tese de Doutorado em Computação Aplicada), INPE, São José dos Campos, advisor H. H. Yanasse, defended 17 May 2001. In `literature/` as `linhares_2001_phd_thesis_industrial_pattern_sequencing.pdf`, copied from the owner's Zotero library on 2026-10-06 (116 pages, text extractable). The source for section 1 of the pathwidth complex paper (`paper1/plan.md`, remaining work item 1).
- **Chu, G.** (2011). *Improving combinatorial optimization*. PhD thesis, University of Melbourne. hdl:11343/36679 — in `literature/` as `chu_2011_phd_thesis_improving_combinatorial_optimization.pdf`, downloaded from Minerva Access on 2026-10-02. Chapter 6 restates the customer search. Theorem 6.3.6 is the CP 2009 Theorem 1 unchanged. Theorem 6.3.8 states the better move with premise `close(q, S) ≥ open(q, S ∪ {r})`. Both are false on `cexGraph`; see `paper1/prior_art_counterexample.md`.

- ~~**Yanasse, H.H. & Senne, E.L.F.** (2010)~~ — NOW AVAILABLE as `yanasse_senne_2010_properties_preprocessing.pdf`. Note the DOI recorded here previously (`10.1016/S0377-2217(09)00632-8`) was wrong; the correct one is **10.1016/j.ejor.2009.09.017**.

- ~~**Fellows, M.R. & Langston, M.A.** (1989). On search, decision, and the efficiency of polynomial-time algorithms. *Proc. 21st ACM STOC*, 501-512.~~ — **OBTAINED 2026-09-27**, see below.

- ~~**Fellows, M.R. & Langston, M.A.** (1987). Nonconstructive advances in polynomial-time complexity. *Information Processing Letters*, 26, 157-162.~~ — **OBTAINED 2026-09-27**, see below.

- **Guimaraes, G.G., Poldi, K.C. & Martin, M.** (2025). Mathematical models for the one-dimensional cutting stock problem with setups and open stacks. *Journal of Combinatorial Optimization*. DOI: 10.1007/s10878-025-01276-5 — Springer paywall.

- **Poldi, K.C. et al.** (2025). On formulations for the one-dimensional cutting stock with a limited number of open stacks problem. *International Journal of Production Research*, 64(4), 1358-1385. DOI: 10.1080/00207543.2025.2568739 — Taylor & Francis paywall.

## Highest priority — harder to obtain than they look

These were identified from the reference lists of papers we hold. *Pesquisa
Operacional* is open access on SciELO, but **only digitised from 2001 onward**,
so the two 1990s papers below are not downloadable there despite the journal
being free. Routes worth trying instead: the INPE digital library (Yanasse is at
INPE/LAC and institutional repositories often hold pre-digitisation work),
Becceneri's 1999 thesis, Becceneri et al. (2004) in *Computers & Operations
Research* which implements the same arc contraction operation, or writing to the
authors.

- ~~**Yanasse, H.H.** (1997a). A transformation for solving a pattern sequencing problem in the wood cut industry. *Pesquisa Operacional*, 17, 57-70.~~ — **OBTAINED 2026-09-27** from the author, see below. It settles the 1997c question: this is the paper.

- ~~**Yanasse, H.H., Becceneri, J.C. & Soma, N.Y.** (1999)~~ — **OBTAINED 2026-09-22**, see below.

- ~~**Yanasse, H.H.** (1997c).~~ — **SETTLED 2026-09-27: 1997c is 1997a**, *Pesquisa Operacional* 17(1), 57-70. That paper contains everything the "1997c" citations are for: the minimum-degree bound (Proposition 3: a connected graph of minimum valency n forces n + 1 open stacks), the clique bound (Corollary 2, via Proposition 2's subinstance monotonicity), and the MOSP graph itself (Proposition 5: any MOSP reduces to one with at most two panel types per pattern by replacing each pattern with a clique on its panel types, with optimal solutions corresponding both ways in polynomial time). The APORS'97 three-author paper is a different, later statement of the bounds.

## Obtained since

- **39 papers from `~/dev/pathwidth`, transferred 2026-09-30** — the literature folder of the graph pathwidth solver now in `../pathwidth_solver/` (`../pathwidth_solver/TRANSFER.md`), copied here under their original `YEAR-Author-Title-Venue.pdf` names; 11 further files there were byte-identical to papers already held and were skipped. 35 are new papers, mostly on exact and approximate pathwidth and treewidth, with reading notes in `pathwidth_solvers_README.md`; four are second copies of papers held (Yanasse & Senne 2010, the INRIA report version of Coudert, Mazauric & Nisse 2014, Kobayashi, Komuro & Tamaki 2014, Mallach 2018). Among the new ones are three entries this file listed as missing: De La Banda & Stuckey (2007), Yanasse & Limeira (2004) and Lopes & Valério de Carvalho (2015), struck through below.

- **Ding, J., Zhou, T., Lü, Z. & Yuan, Y.** (2017). A quality and distance guided metaheuristic algorithm for vertex separation problem. *IEEE Access*, 5, 19251-19261. doi:10.1109/ACCESS.2017.2740418 — in `literature/` as `ding_zhou_lu_yuan_2017_quality_distance_guided_metaheuristic_vsp_ieee_access.pdf`, obtained 2026-09-30. One of the six works citing both a MOSP paper and a graph-theory paper (`paper1/popularity.md`). Instances: VSPLIB ("http://www.optsicom.es/vsp/", now dead), 162 in total: 62 Harwell-Boeing, plus grids and trees. It improves 33 best-known values, so VSPLIB's HB values are heuristic, not optima. It quotes the HB edge range 34-3721, the same figure `paper1/benchmarks/hunt_graphs.md` found inconsistent with the files (46-7442). Resolved 2026-09-30: the page's range is wrong, and it halves the true counts at both ends; the files match the original Matrix Market matrices.

- **Devadas, S.** (1986). Topological optimization of multiple level array logic. Memorandum UCB/ERL M86/95, Electronics Research Laboratory, University of California, Berkeley, 12 December 1986. 127 pp. — in `literature/` as `devadas_1986_topological_optimization_multiple_level_array_logic_ucb_erl_m86_95.pdf`, obtained 2026-09-30. PLA / multiple-level array logic folding; appears among the relevant PLA-folding works in `paper1/data/relevance_labels.json`. Not read yet; a candidate source of PLA instances for the benchmark hunt (`paper1/plan.md` section 4). The hunt (2026-09-30) put its area-optimised array circuits out of scope (`paper1/benchmarks/README.md` §5).

- **Ellis, J.A., Sudborough, I.H. & Turner, J.S.** (1994). The vertex separation and search number of a graph. *Information and Computation*, 113(1), 50-79. doi:10.1006/inco.1994.1064 — in `literature/` as `ellis_sudborough_turner_1994_vertex_separation_search_number.pdf`, obtained 2026-09-28. Read in full. Contents: `vs(G) ≤ s(G) ≤ vs(G) + 2` for the edge search number (Theorem 2.1), `s(G) = vs(G')` for the 2-expansion (Theorem 2.2), a recursive characterization of trees with vertex separation k (Theorem 3.1), smallest trees of vertex separation k have `m(k) = ⌊5·3^k/6⌋` vertices so `vs(T) = O(log n)`, and a linear-time tree algorithm. **It has no general-graph lower bound of any kind**, so it does not anticipate the expansion bound (see *Prior art to settle* below). Its survey paragraph also records that Fellows & Langston (1989) show gate matrix layout cost = path width + 1, the same link our chain uses.

- **Coudert, D., Mazauric, D. & Nisse, N.** (2014). Experimental evaluation of a branch and bound algorithm for computing pathwidth. *SEA 2014*, LNCS 8504, 46-58. doi:10.1007/978-3-319-07959-2_5 — in `literature/` as `coudert_mazauric_nisse_2014_branch_and_bound_pathwidth_sea.pdf`, extracted from the proceedings on 2026-09-28. Prefix-layout branch and bound for vertex separation of digraphs. Two pruning rules that are the pathwidth-side counterparts of Chu & Stuckey (2009): Lemma 3, a *greedy step* that appends a vertex whose out-neighbours are already inside `S ∪ N⁺(S)` (Chu & Stuckey's definite move), and Lemma 4, a table of already-explored prefix sets (their nogood memo). Preprocessing by arc contraction and the degree-1/degree-2 rules of Bodlaender et al. No lower bound beyond the incumbent. Exact to about 60 vertices.

- **Kobayashi, Y., Komuro, K. & Tamaki, H.** (2014). Search space reduction through commitments in pathwidth computation: an experimental study. *SEA 2014*, LNCS 8504, 388-399. doi:10.1007/978-3-319-07959-2_33 — in `literature/` as `kobayashi_komuro_tamaki_2014_commitments_pathwidth_sea.pdf`, extracted 2026-09-28. Memoized backtracking over vertex-separation prefix sets with *commitments* (Tamaki): an extension `T ⊇ S` may be taken without branching when every intermediate set has border at least `d(T)`. Depth-1 commitments are extremely effective on TreewidthLIB; depth 2-10 add little. Depth-1 is again the definite-move family. The full SEA 2014 proceedings stay in `~/Downloads` and are not committed (12 MB).

- **Mallach, S.** (2018). Linear ordering based MIP formulations for the vertex separation or pathwidth problem. *Journal of Discrete Algorithms*, 52-53, 156-167. doi:10.1016/j.jda.2018.11.012 — in `literature/` as `mallach_2018_linear_ordering_mip_vertex_separation_pathwidth.pdf`, obtained 2026-09-28. Shows the earlier position- and set-assignment MIPs have LP relaxations with worst-possible (zero) lower bounds, and gives a linear-ordering MIP whose relaxation is provably nonzero; still weak on grids (constant 2 against pathwidth n) and on dense queen graphs, and the author notes combinatorial treewidth bounds are usually stronger. Relevant to item 7 only as a negative: an LP relaxation is not where a strong MOSP floor will come from. HELD (already in literature/ as `mallach_2018_linear_ordering_mip_vertex_separation_pathwidth.pdf`).

- **Grigoriev, A., Kobayashi, Y., Tamaki, H. & van der Zanden, T.C.** (2025). A polynomial delay algorithm generating all potential maximal cliques in triconnected planar graphs. arXiv:2506.12635v3 — in `literature/` as `grigoriev_kobayashi_tamaki_vanderzanden_2025_potential_maximal_cliques_planar.pdf`, obtained 2026-09-28. Treewidth of planar graphs via Bouchitté-Todinca. MOSP graphs are unions of cliques and rarely planar, so this bears only on the exact-treewidth ideas in `reports/machine_learning_todo.md`, and weakly.

- **Yanasse, H.H.** (1997b). On a pattern sequencing problem to minimize the maximum number of open stacks. *European Journal of Operational Research*, 100(3), 454-463. — in `literature/` as `yanasse_1997b_pattern_sequencing_open_stacks_ejor.pdf`, sent by the author 2026-09-27; Table 1 ref [1], the MOSP paper (received 1994, accepted 1995). What is in it. §1: the problem in the wood-cutting setting with the 6-pattern example; Conjectures 1-4 that MOSP shares an optimal solution with the order-spread (MORP), discontinuities (MDP) and tool-switching (MTSP) problems; NP-hardness "still an open question". §2: a mathematical formulation through Tang & Denardo's tool-switching model — Propositions 1-2 give `MOSP = min C such that MTSP(C) needs exactly M − C switches`. §3: **a branch and bound whose nodes are pairs `(S_o, S_u)` of open and unfinished part types and whose branching chooses the next part type to complete** — the customer-closing-order state space that Chu & Stuckey (2009) and `satisfiability/customer_search.py` search, with the observation that the patterns needed to complete a part type can be sequenced in any order without changing the open stacks at the end; bounds LB1 (largest pattern, the trivial bound), LB2 (min over successors), LB3 (from the predecessor), UB = `|S_u|`; depth-first with the greedy choice "the node with the least open stacks". §4: the matrix computations (`N_i`, the row-OR of the patterns containing type `i`; `(N_i ∨ N_ant)·e'` = stacks open after completing `i`); **dominated panel types** (`T_i ⊆ T_j`: completing `j` completes `i`) used to break ties and to fathom — the subset rule, in 1994; the sets `U^j` that avoid re-branching on a type already considered elsewhere at the same level — a memo. §4 also lists the heuristics one could build, including "next pattern ... the one that results in the least number of open stacks", the first key of the two-key rule at pattern level. So the exact method the repository runs is, in its state space and two of its rules, this paper's.

- **Ohtsuki, T., Mori, H., Kuh, E.S., Kashiwabara, T. & Fujisawa, T.** (1979). One-dimensional logic gate assignment and interval graphs. *IEEE Transactions on Circuits and Systems*, 26(9), 675-684. — in `literature/` as `ohtsuki_mori_kuh_kashiwabara_fujisawa_1979_one_dimensional_logic.pdf`, sent 2026-09-27; Table 1 ref [7]. The interval-graph route to the whole family, and the earliest paper in Table 1. Nets ↔ vertices and gates ↔ the sets `V(t)`; the **connection graph** `H` joins two nets that share a gate — the MOSP graph with nets as customers and gates as patterns (eq. 5-6). For a gate permutation the nets become intervals; tracks = chromatic number = clique number of the resulting interval graph (Fig. 3), so the problem is: find an interval supergraph `Ĥ = (V, E ∪ F)` of `H` with minimum clique number (§III), which is NP-complete by Kashiwabara & Fujisawa [11] — Table 1's ref [5], still missing, is cited here for exactly that. Theorem 1 (Fulkerson & Gross) is the consecutive-ones characterisation; Theorem 3 reads a gate sequence off an ordering of the dominant cliques; §IV gives a polynomial algorithm for a *minimal* (not minimum) augmentation, Theorem 4, extended to fixed boundary gates in Theorem 5; §V reports 30 random minimal augmentations per instance on seven 48-gate circuits (Table IV). In our terms: the optimum is `1 +` the pathwidth of the connection graph because pathwidth is one less than the least clique number of an interval supergraph — the interval-thickness link, stated here in 1979 with the MOSP graph already drawn.

- **Wing, O., Huang, S. & Wang, R.** (1985). Gate matrix layout. *IEEE Transactions on Computer-Aided Design*, 4(3), 220-231. — in `literature/` as `wing_huang_wang_1985_gate_matrix_layout.pdf`, sent 2026-09-27; Table 1 ref [8]. CMOS gate matrix layout as a two-stage problem: gate assignment `f`, then net-to-row assignment `h` with vertical diffusion runs to keep realisable. §V restates Ohtsuki's connection graph and interval graph `I(L)`, with three "self-evident" facts: `I(L) ⊇ H`, rows = largest dominant clique of `I(L)`, and **rows ≥ max nets per gate** — the trivial lower bound `lb_p`, in the VLSI literature. Appendix A is a greedy heuristic (`Algorithm Interval Graph`) that places dominant cliques left or right of the partial matrix to minimise the growth of the largest clique and the fill-in, with random restarts; Fig. 13's histogram of 90 trials on a 144-net circuit spans clique sizes 34-55, which is the spread of a constructive heuristic on one instance and a period reference point for §7's rule and §29's MCNh. Series-connected transistors are merged into one net (§IV), a domain reduction with no MOSP analogue.

- **Lengauer, T.** (1981). Black-white pebbles and graph separation. *Acta Informatica*, 16(4), 465-475. — in `literature/` as `lengauer_1981_black_white_pebbles_graph_separation.pdf`, sent 2026-09-27; Table 1 ref [14]. **Table 1 lists it under "edge separation"; its subject is the vertex separator game.** VSG (p. 467): pebble the vertices of an undirected graph in some order; the cut after each move is the set of pebble-free vertices adjacent to a pebbled one; `VSG(G)` is the least achievable maximum cut — vertex separation, with the note that in general `VSG(S) ≠ VSG(S̄)` for the reversed order (the asymmetry `reports/ml_nature.md` §8 measured on closing orders). Lengauer says explicitly (p. 468) that the *edge*-separator version of the same game is min-cut linear arrangement. Theorems 2-4 relate VSG to the progressive black-white pebble game on dags with shifts of one and two (via the graphs `G_u`, `G_d`, `G_du`); **Theorem 7 proves VSG NP-complete** by reduction from a modified min-cut linear arrangement, which is the result Kinnersley (1992) cites as [11] for VERTEX SEPARATION. So Table 1's attribution of *edge separation* to [14] is loose; the paper is the NP-completeness reference for vertex separation, and hence for pathwidth via Kinnersley.

- **Fellows, M.R. & Langston, M.A.** (1987). Nonconstructive advances in polynomial-time complexity. *Information Processing Letters*, 26, 157-162. — in `literature/` as `fellows_langston_1987_nonconstructive_advances_ipl.pdf`, obtained 2026-09-27. The letter Fellows & Langston (1989) cite as [FL1] and Kinnersley (1992) as [4]. §4 is the gate matrix layout part and carries three lemmas, all with full proofs. **Lemma 4.1**: `GML(M, k)` iff `GML(x(M), k)`, where `x(M)` expands every column with `j > 2` ones into its ⁽ʲ₂⁾ two-ones columns — proved in both directions (forward: keep the permutation, place the expanded columns adjacently; backward: for each original column take the first and last of its expanded columns, all its nets are pairwise connected and hence open across that span, so one of them can be replaced by the original column and the rest deleted without adding a track, then iterate). With the map `g` (rows → vertices, two-ones columns → edges), that is **Yanasse (1997a) Proposition 5 in matrix vocabulary, ten years earlier**: the same reduction, the same both-ways correspondence of optimal solutions. **Lemma 4.2**: the "yes" family for fixed `k` is minor-closed (deleting a column or row and contracting an edge — replacing two rows by their element-wise OR — never adds a track). **Lemma 4.3**: a planar graph of cost `> k` exists for every `k`, built by joining three copies of the previous one at a new vertex `d` adjacent to one vertex in each (Fig. 2); the proof is the **pathwidth branch rule** in full — with columns `i₁ < i₂ < i₃` from the three copies each carrying `k + 1` entries, `d` or the copy's attachment vertex spans `i₂` and forces `k + 2`. Theorem 4.4, `GML ∈ P` for fixed `k`, and the remark that GML is self-reducible (decision to construction), plus the two obstructions for `k = 2`, `K₃` and the subdivided claw.

  **This completes the chain on the literature's own proofs.** Theorem 7 of the 1989 paper sketches decomposition → layout and cites Lemma 4.1 for the expansion step, which is now in hand with its proof; the converse direction remains the elementary one written out under the 1989 entry. And the two routes from MOSP to the graph — Linhares & Yanasse (2002) through gate matrix layout, and Yanasse (1997a) through the clique-per-pattern graph — meet here: Proposition 5 and Lemma 4.1 are the same statement.

- **Fellows, M.R. & Langston, M.A.** (1989). On search, decision, and the efficiency of polynomial-time algorithms. *Proc. 21st ACM STOC*, 501-512. — in `literature/` as `fellows_langston_1989_search_decision_efficiency_stoc.pdf`, obtained 2026-09-27. Reference [15] of Linhares & Yanasse (2002) (Theorem 1 there, `GMLP ∈ FPT`, hence Corollary 1, `MOSP ∈ FPT`) and reference [6] of Kinnersley (1992). **Theorem 7** (p. 503-504): *those graphs that correspond to gate matrix layout cost k are exactly those graphs with path-width k − 1*, where a matrix is mapped to a graph by first expanding every column into two-ones columns and then reading rows as vertices and columns as edges — Yanasse (1997a) Proposition 5's clique-per-pattern construction in the VLSI vocabulary. **The paper proves one direction only**, and says so: from a path decomposition of width k − 1 it builds the matrix whose columns are the bags, expands each bag into its pairwise columns, and cites [FL1] Lemma 4.1 for the expansion preserving the cost, giving layout cost ≤ k. The converse — a layout of cost k yields a path decomposition of width ≤ k − 1 — is not written out but is elementary: take as bags the sets of rows active at each column; the consecutive-ones property makes each row's bags an interval, so the intersection condition holds, every edge (two rows sharing a column) lies in that column's bag, and no bag exceeds k rows. It is the layout-to-decomposition half of Kinnersley's Theorem 3.1 with "active at column i" in place of `V_L(i)`.

  **With this paper the MOSP–pathwidth chain closes on papers we hold**: MOSP = GML (Linhares & Yanasse 2002, Proposition 2, by definition); GML cost = pathwidth + 1 (Fellows & Langston 1989, Theorem 7, one direction sketched there and the converse elementary as above); pathwidth = vertex separation (Kinnersley 1992, Theorem 3.1, both directions); and, on the MOSP side, the graph is Yanasse (1997a) Proposition 5's. The Lean development holds the vs = pw half without gaps (`VSEquivPW.lean`); `Reduction.lean` holds `mosp ≤ pathwidth + 1` — the direction Fellows & Langston sketch — with one `sorry`, and lacks the elementary converse, which is loop0004 item 12. *(Superseded later on 2026-09-27: that `Reduction.lean` statement was over the pattern graph and false, and is deleted; `MOSPGraph.lean` proves `mospValue = pathwidth (mospGraph) + 1` in both directions, `sorry`-free.)* The 1989 paper also carries Theorem 8's table of pathwidth upper bounds for related layout problems (min cut linear arrangement k, search number k + 3) and the general nonconstructivity results (Theorems 13-16) that Linhares & Yanasse §2.2 rely on.

- **Kinnersley, N.G.** (1992). The vertex separation number of a graph equals its path-width. *Information Processing Letters*, 42(6), 345-350. — in `literature/` as `kinnersley_1992_vertex_separation_equals_pathwidth.pdf`, obtained 2026-09-27. Reference [13] of Table 1 in Linhares & Yanasse (2002). Three things in it bear on the repository. (1) **Theorem 3.1**, `vs(G) = pw(G)`, proved in both directions by exactly the two constructions the Lean development uses: from a layout `L`, the bags `X_i = V_L(i − 1) ∪ {L⁻¹(i)}` (`LayoutToDecomposition.lean`); from a path decomposition, the layout that walks the bags in order (`DecompositionToLayout.lean`). `VSEquivPW.lean` is a faithful formalisation of this proof. (2) **Corollary 3.2**: if `vs(G) = k` then gate matrix layout cost and node search number both equal `k + 1`, via Fellows & Langston's Theorem 7 and Kirousis & Papadimitriou's Theorem 4.1. With Linhares & Yanasse (2002) Proposition 2 (open stacks = GML tracks) this is the published chain behind `MOSP = pathwidth + 1`; Yanasse's clique-per-pattern graph (1997a, Proposition 5) is the other route, through the MOSP graph. (3) **Theorem 4.1** (Ellis, Sudborough & Turner) and **Corollary 4.2**: for a tree, `gml(T) > k` iff some vertex induces three or more subtrees each of cost ≥ k; and, quoted from Fellows & Langston (1987) [4], that making a new vertex adjacent to one vertex in each of three graphs of GML cost `k` gives cost at least `k + 1` (the premise of Theorem 4.3). **That is the pathwidth branch rule** `reports/ml_nature.md` §24 stated in treewidth form and loop0004 item 11 tests as its first candidate over cut vertices: it is a known lemma, to be cited, not claimed. The paper also gives the tree-obstruction recurrence `v(k) = 3v(k − 1) + 1` and the counts of tree obstructions for `k`-GML (2, 10, 117,480 for k = 2, 3, 4).

- **Yanasse, H.H.** (1997a). A transformation for solving a pattern sequencing problem in the wood cut industry. *Pesquisa Operacional*, 17(1), 57-70. — in `literature/` as `yanasse_1997a_transformation_pattern_sequencing_wood.pdf`, sent by the author 2026-09-27. **This is "Yanasse (1997c)".** Five propositions: (1) reversing a pattern sequence reverses the open-stack profile — the symmetry `reports/ml_nature.md` §8 measures, with Corollary 1 that every MOSP with more than one pattern has multiple optima; (2) adding patterns cannot lower the optimum — the subinstance bound `satisfiability/relaxation.py` uses; (3) minimum valency n forces n + 1 stacks; Corollary 2, the clique bound; (4) a clique of size n ≥ 4 forces n − 1 open stacks over four *consecutive* patterns; (5) the reduction of any MOSP to the two-panel case through the clique-per-pattern graph — the MOSP graph, with the observation (p. 68) that many different instances share one graph and hence one optimum, which §1 and §13 measure. The paper conjectures NP-hardness, later proved by Linhares & Yanasse (2002).

- **Becceneri, J.C., Yanasse, H.H. & Soma, N.Y.** (2004). A method for solving the minimization of the maximum number of open stacks problem within a cutting process. *Computers & Operations Research*, 31(14), 2315-2332. — in `literature/` as `becceneri_yanasse_soma_2004_method_mosp_cutting.pdf`, sent by the author 2026-09-27. Settles the three things it was wanted for. **The Minimal Cost Node heuristic (§4) is an arc-traversal heuristic, not a node-closing one**: it keeps `Ω(k)`, the degree of node k over arcs not yet traversed, takes the node of smallest Ω, then two adjacent nodes n₁, n₂ with Ω(n₁) = Ω(k) and the pairwise smallest Ω, traverses the arc (n₁, n₂), then greedily traverses every arc between already-open nodes; the pattern sequence is read off the arc sequence by sequencing a pattern when all its nodes are first open. That is why our node-closing `mcn` does not reproduce MCNh's numbers. **The dominance rules (§5)**: the Global dominance proposition (if `N[j] ⊆ N[i]` then some optimal sequence closes j before i, with proof) — our subset rule — and the note that using it inside their branch-and-bound *worsened* performance, so it was not used; the Equivalency proposition (`N[i] = N[j]` or `N(i) = N(j)`: sequence them consecutively, and delete one — Fig. 3's reduction 8 → 5 nodes, with the hierarchy caveat that equivalences found after a reduction must respect the earlier ones). **The arc contraction heuristic (§5)**: lb_c = max over contractions of (min degree + 1), contracting the arc whose ends have the smallest indices in the vertex set sorted by non-decreasing degree, re-sorted every iteration; O(n³); with lb_p (largest pattern) and lb_d (min degree + 1) as its floor — contraction degeneracy + 1 again, and their Fig. 7 example where lb_p = 3, lb_d = 2, lb_c = 6. Also: pattern dominance (§3, `P_j ⊆ P_i`), the tree/cycle/1-tree component pre-solve from Yanasse (1996), the exact method (branch-and-bound with the Limeira/Yanasse local dominance, MCN as incumbent, lb_c as floor, equivalent nodes deleted first), and their generator ("start with a complete graph and delete a percentage of arcs", instances `Gxyz`). Their own verdict (§6–§7): the heuristic is "quite good", the lower bound "quite poor" for small C — the degree-family verdict `reports/ml_nature.md` §6 reaches.

- **Yanasse, H.H., Becceneri, J.C. & Soma, N.Y.** (1999). Bounds for a problem of sequencing patterns. *Pesquisa Operacional*, 19(2), 249-277. — in `literature/` as `yanasse_becceneri_soma_1999_bounds_sequencing_patterns.pdf`. **The most actionable missing reference, and it settles what it was wanted for.** It gives five bounds. LB4 is degeneracy + 1 ("find an induced subgraph whose minimum degree is maximized", by repeatedly deleting the smallest-degree node). LB5, the arc contraction bound, repeatedly contracts an arc at a minimum-degree node and keeps the largest LB4 seen — **that is contraction degeneracy (MMD+) + 1, the bound `satisfiability/mosp_solver.py::_contraction_degeneracy` computes.** So the two are the same bound and no novelty may be claimed for ours; the only difference is the tie-break (their least degree sum, our least common neighbours). See `reports/lower_bounds.md` §3.

- **Yanasse, H.H., Becceneri, J.C. & Soma, N.Y.** (1997). Lower bounds for the problem of sequencing cutting patterns. APORS'97, Melbourne; also CNMAC XX, Gramado; published in the *Anais da II Oficina de Problemas de Corte & Empacotamento*, 2-6. — in `literature/` as `yanasse_becceneri_soma_1997_lower_bounds_apors.pdf`. The 1999 paper's LB1-LB3 in earlier form, with the same worked instance. **Possibly the "Yanasse (1997c)" that Yanasse & Senne (2010) cite for the MOSP graph and the clique / minimum-degree bounds** — it states the minimum-degree bound as Proposition 2 and the subgraph bound via Proposition 1, over the graph with nodes as order parts. It does *not* contain a clique bound, so if 1997c is the source of that, 1997c is a different paper still.

- **Yanasse, H.H., Becceneri, J.C. & Soma, N.Y.** (2007). Um algoritmo exato com ordenamento parcial para solução de um problema de programação da produção: experimentos computacionais. *Gestão & Produção*, 14(2), 353-361. — in `literature/` as `yanasse_becceneri_soma_2007_algoritmo_exato.pdf`. In Portuguese. States the partial-ordering rules precisely, which Yanasse & Senne only reference:
  - **Type I**: adjacent nodes i, j both of degree 2 — some optimal solution labels them consecutively.
  - **Type II**: if `A_j ⊆ A_i ∪ {i}` then i dominates j, and some optimal solution labels j before i. If `A_j = A_i`, they are equivalent, and Becceneri et al. (2004) reduce the graph keeping only one.

  Measured on our instances: the *reduction* rules essentially never fire (0 type-I pairs and 0 equivalences on SP2/SP3/SP4), but *dominance* relations are common — 28, 21 and 27 pairs respectively. Those are symmetry-breaking constraints rather than reductions, and are unexploited by our encoding.

## Also missing, newly identified

- ~~**De La Banda, M.G. & Stuckey, P.J.** (2007). Dynamic programming to minimize the maximum number of open stacks. *INFORMS Journal on Computing*, 19, 607-617. DOI: 10.1287/ijoc.1060.0205~~ — the DP that Chu & Stuckey (2009) extends. **OBTAINED 2026-09-30** with the `~/dev/pathwidth` transfer, as `2007-Garcia-de-la-Banda-Stuckey-Dynamic-Programming-Minimize-Maximum-Open-Stacks-IJOC.pdf`.

- ~~**Becceneri, J.C., Yanasse, H.H. & Soma, N.Y.** (2004). A method for solving the minimization of the maximum number of open stacks problem within a cutting process. *Computers & Operations Research*, 31(14), 2315-2332.~~ — **OBTAINED 2026-09-27** from the author, see below.

  Partially substituted by Poliquit (2008), a Master's thesis of the same title now in `literature/`, which states the MCN algorithm in full (§3) and covers arc contraction (§4.2) and a lower bound implementation (§4.4). Its statement is explicitly for instances with at most two piece types per pattern, so it does not transfer directly to the general case.

- ~~**Yanasse, H.H. & Limeira, M.S.** (2004). Refinements on an enumeration scheme for solving a pattern sequencing problem. *International Transactions in Operational Research*, 11, 277-292. DOI: 10.1111/j.1475-3995.2004.00458.x~~ — **OBTAINED 2026-09-30** with the `~/dev/pathwidth` transfer, as `2004-Yanasse-Limeira-Refinements-Enumeration-Scheme-Pattern-Sequencing-ITOR.pdf`.

## Table 1 of Linhares & Yanasse (2002) — the equivalent problems

Table 1 of `Linhares and Yanasse - 2002 - Connections between cutting-pattern
sequencing, VL.pdf` (p. 1764) asserts twelve problems equivalent up to ±1,
resting on twelve distinct references. **Eleven are held** (see
`../paper1/literature/MANIFEST.md`), including the full Möhring chapter; **one
is not**, Kashiwabara & Fujisawa [5]. When this section was written five were
held and seven were not; two of the seven, Kinnersley [13] and Yanasse [1], are
listed under **Paywalled** above, and the other five are below, four of them
since obtained:

- **Kashiwabara, T. & Fujisawa, T.** (1979). NP-completeness of the problem of finding a minimum clique number interval graph containing a given graph as a subgraph. *Proc. 1979 IEEE International Symposium on Circuits and Systems*, Tokyo, 657-660. No DOI — Table 1 ref [5], *interval thickness*. **The hardest of the twelve**: 1979 conference proceedings, not indexed by OpenAlex at all, never digitised by IEEE. Needs a library holding physical IEEE conference records.

- ~~**Möhring, R.H.** (1990). Graph problems related to gate matrix layout and PLA folding. In *Computational Graph Theory*, Computing Supplementum 7, Springer-Verlag Wien, 17-51. DOI: 10.1007/978-3-7091-9076-0_2~~ — Table 1 refs [6], *gate matrix layout* and *PLA folding*. **OBTAINED IN FULL 2026-09-27**: the 35-page chapter, extracted (pp. 20–54 of the file) from the full book PDF *Computational Graph Theory* (Tinhofer, Mayr, Noltemeier, Sysło eds., 1990) downloaded via institutional access and kept in `~/Downloads`; in `literature/` as `mohring_1990_gate_matrix_layout_pla_folding.pdf` and in `paper1/literature/` as `06_mohring_1990.pdf`. The two-page Springer preview held earlier that day was deleted. Contents: interval-graph augmentation with minimum clique size (= pathwidth + 1), node search, vertex separation, MPQ-trees / interval orders, matching problems with side constraints.

- ~~**Ohtsuki, T., Mori, H., Kuh, E.S., Kashiwabara, T. & Fujisawa, T.** (1979). One-dimensional logic gate assignment and interval graphs. *IEEE Transactions on Circuits and Systems*, 26(9), 675-684.~~ — **OBTAINED 2026-09-27**, see below.

- ~~**Wing, O., Huang, S. & Wang, R.** (1985). Gate matrix layout. *IEEE Transactions on Computer-Aided Design of Integrated Circuits and Systems*, 4(3), 220-231.~~ — **OBTAINED 2026-09-27**, see below.

- ~~**Lengauer, T.** (1981). Black-white pebbles and graph separation. *Acta Informatica*, 16(4), 465-475.~~ — **OBTAINED 2026-09-27**, see below.

Obtained since: **Kirousis, L.M. & Papadimitriou, C.H.** (1985). Interval graphs
and searching. *Discrete Mathematics*, 55(2), 181-184. DOI:
10.1016/0012-365X(85)90046-9 — Table 1 ref [9], *node search game*; the
interval-thickness = node-search-number link. Now in
`../paper1/literature/09_kirousis_papadimitriou_1985.pdf`. It was never
paywalled — Elsevier's open archive carries it free — and only ScienceDirect's
block on non-browser clients stood in the way; a browser fetched it at once.
Worth remembering for any other Elsevier open-archive item.

Sources checked for the then-missing seven and found to hold nothing: OpenAlex, Semantic
Scholar, CORE (rate-limited without an API key), Internet Archive Scholar
(`api.fatcat.wiki` unreachable throughout), the publishers, the authors' own
pages, and the Wayback Machine where an author page is dead.

## Prior art to settle (not missing — unidentified)

- ~~**The neighbourhood-expansion lower bound** of `satisfiability/expansion_bound.py`~~
  — **settled 2026-09-28: not new.** `vs(G) ≥ max_i (i − max{t : f(t) ≤ i})` with
  `f(t) = min_{|C|=t}|N[C]|` is the classical vertex-isoperimetric bound
  `vs(G) ≥ max_i Φ(i)`, `Φ(i) = min_{|S|=i} |∂_in S|`: the interior of an `i`-set
  is exactly a `C` with `N[C] ⊆ S`, so `i − M(i) = Φ(i)`. Sources to cite:
  - **Harper, L.H.** (1966). Optimal numberings and isoperimetric problems on graphs. *Journal of Combinatorial Theory*, 1(3), 385-393. doi:10.1016/S0021-9800(66)80059-5 — the method. Not held.
  - **Chandran, L.S. & Kavitha, T.** (2006). The treewidth and pathwidth of hypercubes. *Discrete Mathematics*, 306(3), 359-365. doi:10.1016/j.disc.2005.12.011 — applied to pathwidth. In `literature/` as `chandran_kavitha_2006_treewidth_pathwidth_hypercubes.pdf`, obtained 2026-09-30.
  - **Lin, L. & Lin, Y.** (2025). Discrete isoperimetric method for bandwidth, pathwidth and treewidth of hypercubes. *Discrete Applied Mathematics*, 363, 201-214. doi:10.1016/j.dam.2024.12.001 — abstract read 2026-09-28: pw(Q_d) = bw(Q_d) by Harper's method, tw(Q_d) open. Not held.
  - **Harper, L.H.** (2004). *Global Methods for Combinatorial Isoperimetric Problems*. Cambridge University Press. doi:10.1017/CBO9780511616679 — the book-length treatment. Not held.
  - **Díaz, J., Petit, J. & Serna, M.** (2002). A survey of graph layout problems. *ACM Computing Surveys*, 34(3), 313-356. doi:10.1145/568522.568523 — survey of layout lower bounds. In `literature/` as `diaz_petit_serna_2002_survey_graph_layout_problems.pdf` (44 pp.), obtained 2026-09-30.

  Read on the way and not containing it: Ellis, Sudborough & Turner (1994),
  Coudert, Mazauric & Nisse (2014), Kobayashi, Komuro & Tamaki (2014), Mallach
  (2018). What remains ours is the exact capped computation of `f` and the
  corpus measurement, not the bound.

## Server issues

- ~~**Lopes, I.C. & De Carvalho, J.M.V.** (2015). Graph properties of minimization of open stacks problems and a new integer programming model. *Pesquisa Operacional*, 35(2), 213-250. DOI: 10.1590/0101-7438.2015.035.02.0213 — SciELO open access, but server returned 502/504 errors. Retry later.~~ — **OBTAINED 2026-09-30** with the `~/dev/pathwidth` transfer, as `2015-Lopes-Valerio-de-Carvalho-Graph-Properties-Minimization-Open-Stacks-New-Integer-Programming-Model-PesqOper.pdf`.

## Random bipartite graphs, cores and random intersection graphs (item 09 of loop0004, 2026-09-28)

None of these is held; `reports/ml_nature.md` §36 cites them from memory for
the thresholds it computes itself in the configuration model, and every
citation there should be checked against the paper before it is quoted
outside this repository.

- Pittel, Spencer & Wormald (1996), "Sudden emergence of a giant k-core in a
  random graph", *J. Combin. Theory B* 67 — the k-core threshold of G(n, p).
- Molloy (2005), "Cores in random hypergraphs and Boolean formulas", *Random
  Structures & Algorithms* 27.
- Fernholz & Ramachandran (2007), "The k-core and branching processes",
  *Combin. Probab. Comput.* 16; Riordan (2008), "The k-core and branching
  processes", *Combin. Probab. Comput.* 17 — cores for general degree sequences,
  the peeling fixed point used in `learning/cover_excess.py`.
- Luby, Mitzenmacher, Shokrollahi & Spielman (2001), "Efficient erasure
  correcting codes", *IEEE Trans. Inform. Theory* 47 — the 2-core (stopping
  set) of a bipartite factor graph with given degree distributions.
- Dubois & Mandler (2002), "The 3-XORSAT threshold", *FOCS*; Mézard,
  Ricci-Tersenghi & Zecchina (2003), "Two solutions to diluted p-spin models
  and XORSAT problems", *J. Stat. Phys.* 111 — a threshold set by the 2-core of
  the factor graph having as many constraints as variables.
- Karoński, Scheinerman & Singer-Cohen (1999), "On random intersection
  graphs: the subgraph problem", *Combin. Probab. Comput.* 8; Fill, Scheinerman
  & Singer-Cohen (2000), *Random Structures & Algorithms* 16 — G(n, m, p) and
  its equivalence to G(n, p̂) only for m ≫ n⁶.
- Behrisch (2007), "Component evolution in random intersection graphs",
  *Electron. J. Combin.* 14; Lagerås & Lindholm (2008), "A note on the
  component structure in random intersection graphs with tunable
  clustering", *Electron. J. Combin.* 15 — the giant component at m = Θ(n).
- Stark (2004), "The vertex degree distribution of random intersection
  graphs", *Random Structures & Algorithms* 24; Deijfen & Kets (2009),
  *Probab. Engrg. Inform. Sci.* 23 — compound-Poisson degrees at m = Θ(n).
- Rybarczyk (2011), "Diameter, connectivity and phase transition of the
  uniform random intersection graph", *Discrete Math.* 311 — connectivity.
- Schmidt-Pruzan & Shamir (1985), *Combinatorica* 5; Karoński & Łuczak (2002),
  *J. Comput. Appl. Math.* 142 — the giant component of random hypergraphs
  (already cited in §25).

## Citers of Chu & Stuckey (2009) not read (loop0008 item 01, 2026-10-03)

The prior-art sweep (`paper1/prior_art_counterexample.md`, "Every citer, swept";
`python3 -m paper1.prior_art_sweep`) could not get a full text for these 14
works citing the CP paper. Neither the indexes nor a web search found an open
copy. They are listed in order of how likely they are to restate the definite
or better move:

- ~~**De Giovanni, L., Massi, G., Pezzella, F., Pfetsch, M.E., Rinaldi, G. & Ventura, P.** (2013). A heuristic and an exact method for the gate matrix connection cost minimization problem. *ITOR* 20(5), 627-643. doi:10.1111/itor.12025.~~ **Read 2026-10-22** (`de_giovanni_massi_pezzella_pfetsch_rinaldi_ventura_2013_gate_matrix_connection_cost_itor.pdf`, from the author): the exact method is a branch and cut for the *total* open stacks under a bound λ on the maximum (GMCCP), not for MOSP; Chu & Stuckey's algorithm is applied to certify λ as the optimal MOS on every instance (pp. 639, 641), with GAG's own MOS one above it on six instances; no rule restated, no failure reported.
- ~~**Chu, G. & Stuckey, P.J.** (2012). Inter-instance nogood learning in constraint programming. CP 2012, LNCS 7514. doi:10.1007/978-3-642-33558-7_19.~~ **Read 2026-10-19** (`chu_stuckey_2012_inter_instance_nogood_learning_cp.pdf`, the author's copy, fetched by the owner in a browser): MOSP is one of four benchmark problems for parameterised nogoods in Chuffed (35 customers, density 0.2, p. 8); the 2009 paper is cited once for the problem's definition; no rule restated or used.
- ~~**De Giovanni, L., Massi, G. & Pezzella, F.** (2013). An adaptive genetic algorithm for large-size open stack problems. *IJPR* 51(3), 682-697. doi:10.1080/00207543.2012.657256.~~ **Read 2026-10-22** (`de_giovanni_massi_pezzella_2013_adaptive_genetic_algorithm_open_stack_ijpr.pdf`, from the author): the journal form of the 2010 report; compares AGA with Chu & Stuckey's code (CS) on the literature benchmarks and on 150 new instances from their generator at 50–150 patterns × 200–250 item types, where CS proves only one optimum in 3 hours (§5.3); describes CS's rules in one sentence (p. 684); no rule restated, no failure reported. Thanks Chu, Stuckey, Mendes and Linhares for support in testing their algorithms.
- ~~**DeGiovanni, L., Massi, G. & Pezzella, F.** (2010). Preliminary computational experiments with a genetic algorithm for the open stack problem. Technical report.~~ **Read 2026-10-19** (`de_giovanni_massi_pezzella_2010_genetic_algorithm_open_stack_report.pdf`, 11 pp., the owner's download): compares their genetic algorithm against Chu & Stuckey's code ("DP+", run with Chu's and Stuckey's support) on all 200 random instances and 5,841 instances in all; DP+ proves every random instance, the largest in about 20 minutes; no rule restated, no failure reported. The fourth work to use an implementation of the rules; now cited in Appendix B.
- **Carvalho, M.A.M. & Soma, N.Y.** (2015). A breadth-first search applied to the minimization of the open stacks. *JORS* 66, 936-946. doi:10.1057/jors.2014.60.
- **Lima, J.R. & Carvalho, M.A.M.** (2017). Descent search approaches applied to the minimization of open stacks. *C&IE* 112, 175-186. doi:10.1016/j.cie.2017.08.016.
- **Santos, V.G.M. & Carvalho, M.A.M.** (2018). Adaptive large neighborhood search applied to the design of electronic circuits. *ASOC*. doi:10.1016/j.asoc.2018.08.017.
- ~~**Arbib, C., Marinelli, F. & Ventura, P.** (2016). One-dimensional cutting stock with a limited number of open stacks. *ITOR*. doi:10.1111/itor.12134.~~ **Read 2026-10-19** (`arbib_marinelli_ventura_2016_cutting_stock_limited_open_stacks_itor.pdf`, author version): cites Chu & Stuckey once, p. 2, as "a breakthrough ... a smart combinatorial lower bound ... in a branch-and-bound scheme"; no rule restated.
- ~~**Arbib, C., Marinelli, F. & Pezzella, F.** (2012). An LP-based tabu search for batch scheduling in a cutting process with finite buffers. *IJPE*. doi:10.1016/j.ijpe.2011.12.003.~~ **Read 2026-10-19** (`arbib_marinelli_pezzella_2012_lp_tabu_batch_scheduling_cutting_finite_buffers_ijpe.pdf`, author version): cites Chu & Stuckey once, in the introduction, for the problem; no rule restated.
- ~~**Visentin, A., Prestwich, S., Rossi, R. & Tarim, S.A.** (2019)~~. Modelling dynamic programming-based global constraints in constraint programming. WCGO 2019. doi:10.1007/978-3-030-21803-4_42. **Read 2026-10-19** (`visentin_2019_dp_global_constraints_wcgo.pdf`, from the CORA repository at UCC): cites Chu & Stuckey once, p. 3, for memoisation; no rule restated.
- ~~**Stivala, A.** (2010)~~. *Algorithms for the study of RNA and protein structure*. PhD thesis, University of Melbourne. **Read 2026-10-19** (`stivala_2010_phd_thesis_rna_protein.pdf`, Minerva Access): parallelises the 2007 DP for open stacks, §4.3.4; cites Chu & Stuckey once in its conclusions; nothing on the moves.
- ~~**Doulabi, S.H.H., Rousseau, L.-M. & Pesant, G.** (2016). A constraint-programming-based branch-and-price-and-cut approach for operating room planning and scheduling. *IJOC* 28(3). doi:10.1287/ijoc.2015.0686.~~ **Read 2026-10-19** (`doulabi_rousseau_pesant_2016_cp_branch_price_cut_operating_room_ijoc.pdf`, author version): cites Chu & Stuckey once, p. 10, as an example of problem-specific dominance rules; no rule restated.
- Camanho et al. (2022), *ITOR*, doi:10.1111/itor.13129, and Amirteimoori et al. (2024), *ITOR*, doi:10.1111/itor.13560. Both are probably false index links: their titles concern efficiency analysis.

Among the citers of the thesis only, one unread work could bear on the rules:
~~**Gange, G., Chu, G. & Stuckey, P.J.** (2019). Certifying optimality in
constraint programming.~~ **Read 2026-10-19** (`gange_2019_certifying_optimality_cp.pdf`,
from https://people.eng.unimelb.edu.au/pstuckey/papers/certified-cp.pdf, 39
pages): proof logging for the chuffed solver; no mention of MOSP, the customer
search or the moves; Chu's thesis is cited once as the solver's source.

**Re-check of 2026-10-19 before the arXiv posting.** Of the 14 above, ten
were obtained (the ten struck through; five by the owner in a browser, two from
De Giovanni on 2026-10-22) and none restates or doubts either move; the three
De Giovanni works used Chu & Stuckey's implementation and report no failure;
the other four stay closed (Wiley, Springer, Elsevier, IRIS and
UFOP repositories behind bot checks or authentication; the attempt log is
`fetch_attempt_2026-10-19.log`). The paper's counts become 33 of 38 CP-paper
citers and 33 of 103 thesis-only citers read in full, 66 of 141.

**Obtained in the same sweep.** Fink, C. (2012), *O problema de minimização de
pilhas abertas — novas contribuições*, PhD thesis, ICMC-USP,
doi:10.11606/t.55.2012.tde-19022013-084858. It is in `literature/` as
`fink_2012_phd_thesis_mosp_novas_contribuicoes.pdf`, from
http://www.teses.usp.br/teses/disponiveis/55/55134/tde-19022013-084858/publico/TeseRevisada.pdf
(fetched 2026-10-03). Its pp. 27–28 restate CP 2009 Theorem 1.

## IJOC papers to obtain (2026-10-04)

From the IJOC sweep, `paper1/ijoc_literature.md`, in order of importance. All are paywalled or blocked by a bot check; none was circumvented.

- Fischetti, M. & Salvagnin, D. (2010). Pruning moves. *IJOC* 22(1), 108-119. doi:10.1287/ijoc.1090.0329
- Fukasawa, R. & Poirrier, L. (2017). Numerically safe lower bounds for the capacitated vehicle routing problem. *IJOC* 29(3), 544-557. doi:10.1287/ijoc.2017.0747
- Garcia de la Banda, M., Stuckey, P.J. & Chu, G. (2011). Solving talent scheduling with dynamic programming. *IJOC* 23(1), 120-137. doi:10.1287/ijoc.1090.0378 (author copy behind a browser check: people.eng.unimelb.edu.au/pstuckey/papers/rehearsal.pdf)
- Belov, G. & Scheithauer, G. (2007). Setup and open-stacks minimization in one-dimensional stock cutting. *IJOC* 19(1), 27-35. doi:10.1287/ijoc.1050.0132
- Caprara, A. & Salazar-González, J.J. (2005). Laying out sparse graphs with provably minimum bandwidth. *IJOC* 17(3), 356-373. doi:10.1287/ijoc.1040.0083
- Halbig, K., Hümbs, L., Rösel, F., Schewe, L. & Weninger, D. (2024). Computing optimality certificates for convex mixed-integer nonlinear problems. *IJOC* 36(6), 1579-1610. doi:10.1287/ijoc.2022.0099 (Edinburgh preprint behind a browser check)
- Sewell, E.C. & Jacobson, S.H. (2012). A branch, bound, and remember algorithm for the simple assembly line balancing problem. *IJOC* 24(3), 433-442. doi:10.1287/ijoc.1110.0462
- Gmys, J. (2022). Exactly solving hard permutation flowshop scheduling problems on peta-scale GPU-accelerated supercomputers. *IJOC* 34(5), 2502-2522. doi:10.1287/ijoc.2022.1193 (HAL hal-03689608 behind a browser check)
- Hicks, I.V. (2005). Planar branch decompositions I: the ratcatcher. *IJOC* 17(4), 402-412. doi:10.1287/ijoc.1040.0075
- Hicks, I.V. (2005). Planar branch decompositions II: the cycle method. *IJOC* 17(4), 413-421. doi:10.1287/ijoc.1040.0074
- Bergman, D., Cire, A.A., van Hoeve, W.-J. & Hooker, J.N. (2016). Discrete optimization with decision diagrams. *IJOC* 28(1), 47-66. doi:10.1287/ijoc.2015.0648
- Cook, W. & Seymour, P. (2003). Tour merging via branch-decomposition. *IJOC* 15(3), 233-248. doi:10.1287/ijoc.15.3.233.16078
- Cook, W., Dash, S., Fukasawa, R. & Goycoolea, M. (2009). Numerically safe Gomory mixed-integer cuts. *IJOC* 21(4), 641-649. doi:10.1287/ijoc.1090.0324
- Malapert, A., Cambazard, H., Guéret, C., Jussien, N., Langevin, A. & Rousseau, L.-M. (2012). An optimal constraint programming approach to the open-shop problem. *IJOC* 24(2), 228-244. doi:10.1287/ijoc.1100.0446
- Barr, R.S. & Hickman, B.L. (1993). Reporting computational experiments with parallel algorithms. *ORSA J. Comput.* 5(1), 2-18. doi:10.1287/ijoc.5.1.2
- Margulies, S., Ma, J. & Hicks, I.V. (2013). The Cunningham-Geelen method in practice. *IJOC* 25(4), 599-610. doi:10.1287/ijoc.1120.0524
- Anjos, M.F. & Vannelli, A. (2008). Computing globally optimal solutions for single-row layout problems using semidefinite programming and cutting planes. *IJOC* 20(4), 611-617. doi:10.1287/ijoc.1080.0270
- Buchheim, C., Wiegele, A. & Zheng, L. (2010). Exact algorithms for the quadratic linear ordering problem. *IJOC* 22(1), 168-177. doi:10.1287/ijoc.1090.0318
- Qiu, Y., Cherniavskii, M., Goldengorin, B. & Pardalos, P.M. (2026). A computational study of the tool replacement problem. *IJOC* 38(1), 86-101. doi:10.1287/ijoc.2023.0474

## Paper 2 survey (2026-10-09)

### Products and structured classes (`paper2/survey_products_structured.md`)

Obtained 2026-10-09, all open access, each opened and checked against its citation:

- **Otachi, Y. & Suda, R.** (2011). Bandwidth and pathwidth of three-dimensional grids. *Discrete Math.* 311, doi:10.1016/j.disc.2011.02.019 — `2011-Otachi-Suda-Bandwidth-Pathwidth-Three-Dimensional-Grids-DM-arXiv.pdf` (arXiv 1101.0964). pw = bw = vbw for grids and even tori; closed form for 3D grids (Thm 4.2); 4D conjecture (Conj. 5.1).
- **Wood, D.R.** (2013). Treewidth of Cartesian products of highly connected graphs. *J. Graph Theory* 73(3), 318–321 — `2013-Wood-Treewidth-Cartesian-Products-Highly-Connected-JGT-arXiv.pdf`.
- **Harvey, D.J. & Wood, D.R.** (2014). Treewidth of the Kneser graph and the Erdős–Ko–Rado theorem. *Electron. J. Combin.* 21(1) #P1.48, doi:10.37236/3971 — `2014-Harvey-Wood-Treewidth-Kneser-Graph-Erdos-Ko-Rado-EJC.pdf`.
- **Harvey, D.J. & Wood, D.R.** (2015). Treewidth of the line graph of a complete graph. *J. Graph Theory* 79, 48–54, doi:10.1002/jgt.21813 — held as the longer arXiv version with complete multipartite graphs, `2015-Harvey-Wood-Treewidth-Line-Graph-Complete-Multipartite-JGT-arXiv.pdf` (arXiv 1210.8205v2).
- **Clarke, N.E., Messinger, M.E. & Power, G.** (2019). Bounding the search number of graph products. *Kyungpook Math. J.* 59(1), 175–190, doi:10.5666/kmj.2019.59.1.175 — `2019-Clarke-Messinger-Power-Bounding-Search-Number-Graph-Products-KMJ-arXiv.pdf`. pw(K_m □ K_n) exactly (Cor. 15).
- **Aidun, I., Dean, F., Morrison, R., Yu, T. & Yuan, J.** (2020). Treewidth and gonality of glued grid graphs. *DAM* 279, 1–11, doi:10.1016/j.dam.2019.10.024 — `2020-Aidun-Dean-Morrison-Yu-Yuan-Treewidth-Gonality-Glued-Grid-Graphs-DAM-arXiv.pdf`.
- **Liu, K., Cao, M. & Lu, M.** (2022). Treewidth of the generalized Kneser graphs. *Electron. J. Combin.* 29(1) #P1.57, doi:10.37236/10035 — `2022-Liu-Cao-Lu-Treewidth-Generalized-Kneser-Graphs-EJC.pdf`.
- **Hickingbotham, R. & Wood, D.R.** (2023). Structural properties of graph products. *J. Graph Theory*, doi:10.1002/jgt.23023 — `2023-Hickingbotham-Wood-Structural-Properties-Graph-Products-JGT-arXiv.pdf`.
- **Fabila-Monroy, R., Gómez-Galicia, S.G., Hernández-Cruz, C. & Trujillo-Negrete, A.** (2025). On the treewidth of token and Johnson graphs. *DAM*, doi:10.1016/j.dam.2025.11.042 — `2025-Fabila-Monroy-et-al-Treewidth-Token-Johnson-Graphs-DAM-arXiv.pdf`.
- **Gima, T., Morimoto, H., Okada, Y. & Otachi, Y.** (2026). Treewidth of the n × n toroidal grid. arXiv 2605.21015 — `2026-Gima-Morimoto-Okada-Otachi-Treewidth-nxn-Toroidal-Grid-arXiv.pdf`.
- **Kaul, R.** (2026). Treewidth of products of graphs with high treewidth. arXiv 2607.16778 — `2026-Kaul-Treewidth-Products-High-Treewidth-arXiv.pdf`. pw(G ⊠ H) ≥ (pw(G)+1)(pw(H)+1) − 1 (Thm 2), i.e. MOSP is supermultiplicative under the Kronecker product of instances.
- **Wang, Y., Cao, M., Lv, Z. & Lu, M.** (2026). Treewidth of generalized Hamming graph, bipartite Kneser graph and generalized Petersen graph. *Electron. J. Combin.* 33(1) #P1.7, doi:10.37236/12892 — `2026-Wang-Cao-Lv-Lu-Treewidth-Generalized-Hamming-Bipartite-Kneser-Generalized-Petersen-EJC.pdf`.

Still to obtain (ScienceDirect blocks scripted download of its open archive; nothing was circumvented):

- **Ellis, J. & Warren, R.** (2008). Lower bounds on the pathwidth of some grid-like graphs. *DAM* 156(5), 545–555. doi:10.1016/j.dam.2007.02.006 — Elsevier open archive; fetch in a browser. Source of pw(C_n □ C_n) = 2n − 1 and the grid and cylinder values.
- **Lin, L. & Lin, Y.** (2025). *DAM* 363, 201–214. doi:10.1016/j.dam.2024.12.001 — paywalled, no preprint (also listed above under prior art).
- **Kiyomi, M., Okamoto, Y. & Otachi, Y.** (2016). On the treewidth of toroidal grids. *DAM* 198, 303–306. doi:10.1016/j.dam.2015.06.027 — open archive; browser.
- **Kozawa, K., Otachi, Y. & Yamazaki, K.** (2014). Lower bounds for treewidth of product graphs. *DAM* 162, 251–258. doi:10.1016/j.dam.2013.08.005 — open archive; browser.
- **Harper, L.H.** (1966). *J. Combin. Theory* 1(3), 385–393. doi:10.1016/S0021-9800(66)80059-5 — open archive; browser (listed above as not held).
- **Harper, L.H.** (1999). On an isoperimetric problem for Hamming graphs. *DAM* 95, 285–309. doi:10.1016/S0166-218X(99)00082-7 — open archive; browser.
- **Balogh, J., Bezrukov, S.L., Harper, L.H. & Seress, Á.** (2008). On the bandwidth of 3-dimensional Hamming graphs. *TCS* 407. doi:10.1016/j.tcs.2008.07.029 — open archive; browser.
- **Djelloul, S.** (2009). Treewidth and logical definability of graph products. *TCS* 410, 696–710. doi:10.1016/j.tcs.2008.10.019 — open archive; browser.
- **Chandran, L.S., Kavitha, T. & Subramanian, C.R.** (2003). Isoperimetric inequalities and the width parameters of graphs. COCOON 2003, LNCS 2697, 385–393. doi:10.1007/3-540-45071-8_39 — paywalled.
- **Ellis, J.** (2023). Computing the pathwidth and bandwidth of solid, convex grids. SSRN, doi:10.2139/ssrn.4592858 — not fetched.
- **Xue, Y., Yang, B. & Zilles, S.** (2024). The zero-visibility cops and robber game on graph products. *TCS* 1007, 114676. doi:10.1016/j.tcs.2024.114676 — paywalled.
- **Wang, X., Wu, X. & Dumitrescu, S.** (2009). On explicit formulas for bandwidth and antibandwidth of hypercubes. *DAM* 157, 1947–1952 — DOI not looked up.
- **Bezrukov, S.L. & Leck, U.** (2009). A simple proof of the Karakhanyan–Riordan theorem on the even discrete torus. *SIAM J. Discrete Math.* 23, 1416–1421 — DOI not looked up.
- **Cao, M., Liu, K., Lu, M. & Lv, Z.** (2023). Treewidth of the q-Kneser graphs. *DAM*, doi:10.1016/j.dam.2023.09.004 — arXiv 2101.04518 is free; not downloaded.

## Paper 2 survey (2026-10-09)

Random, asymptotic and extremal pathwidth; full table and statements in
`paper2/survey_random_extremal.md`. **Obtained and verified (open access):**

- `2012-Gao-Treewidth-Erdos-Renyi-Random-Intersection-Scale-Free-Random-Graphs-DAM-arXiv.pdf` — Gao, DAM 160 (2012), arXiv 0907.5481. Thm 2: random intersection graph `G_I(n, m, p)`, `m = n^α`, `p ≥ 2/m` ⇒ treewidth linear whp, i.e. random MOSP optima are `Θ(n)`. §2.2 records that Karoński et al. introduced the model for gate matrix layout.
- `2024-Do-Erde-Kang-Note-Width-Sparse-Random-Graphs-JGT-arXiv.pdf` — tw of `G(n,(1+ε)/n)` is `Θ(ε³n)` in the weakly supercritical regime (Thm 1.6).
- `2012-Lee-Lee-Oum-Rank-Width-Random-Graphs-JGT-arXiv.pdf` — tw linear for `G(n, c/n)` iff `c > 1`.
- `2014-Perarnau-Serra-Tree-Depth-Random-Graphs-DAM-arXiv.pdf` — `td = n − O(√(n/p))` (and the same for tw) for dense `G(n,p)`, which sandwiches pw.
- `2012-Mitsche-Perarnau-Treewidth-Related-Parameters-Random-Geometric-Graphs-STACS.pdf` — tw/td/pw of random geometric graphs.
- `2014-Kolesnik-Wormald-Lower-Bounds-Isoperimetric-Numbers-Random-Regular-Graphs-SIDMA-arXiv.pdf` — vertex isoperimetric lower bounds, which give `pw(G_{n,3}) ≥ 0.0721n` a.a.s.
- `2022-Diaz-Diner-Serna-Serra-Vertex-Bisection-Width-Random-Regular-Graphs-arXiv.pdf`
- `2023-Lichev-Mitsche-Minimum-Bisection-Random-3-Regular-Graphs-EJC-arXiv.pdf`
- `2006-Fomin-Hoie-Pathwidth-Cubic-Graphs-Exact-Algorithms-IPL.pdf` — author copy; `pw ≤ (1/6+ε)n` for max degree 3; the gap to 0.082n is open.
- `2009-Fomin-Gaspers-Saurabh-Stepanov-Two-Techniques-Combining-Branching-Treewidth-Algorithmica-preprint.pdf` — pw bound by degree profile (Lemma 1).
- `2007-Behrisch-Component-Evolution-Random-Intersection-Graphs-EJC.pdf` — giant component of `G_I` for `m = n^α`, `α ≠ 1`. This corrects the §36 citation from memory, which can now be checked.
- `2011-Rybarczyk-Equivalence-Random-Intersection-Graph-Gnp-RSA-arXiv.pdf` — `G_I` ≈ `G(n, p̂)` for monotone properties when `m ≥ n³`.

**Still to obtain** (DOIs in the survey §4):

- Karoński, Scheinerman & Singer-Cohen (1999), CPC 8, 10.1017/S0963548398003459. Introduces random intersection graphs with an application to gate matrix layout, the origin of "random MOSP". Highest priority.
- Karoński & Szymkowiak (2001), Discrete Math. 236:179–189, 10.1016/S0012-365X(00)00441-6. Thresholds for randomized 3-GML (MOSP with 3 stacks). Elsevier open archive; ScienceDirect refuses curl, so a browser download is needed.
- Díaz, Petit, Serna & Trevisan (2001), Approximating layout problems on random graphs, 10.1016/S0012-365X(00)00278-8 (open archive).
- Kneis, Mölle, Richter & Rossmanith (2009), SIDMA, 10.1137/080715482.
- Takahashi, Ueno & Kajitani (1994), minimal acyclic forbidden minors for path-width; Bienstock, Robertson, Seymour & Thomas (1991), 10.1016/0095-8956(91)90068-U; Kloks & Bodlaender (1992), 10.1007/BFb0045380; Böttcher et al. (2010), 10.1016/j.ejc.2009.10.010; Lagerås & Lindholm (2008); Shang (2022), 10.3792/pjaa.98.015; Bezrukov et al. (2004); Flajolet, Raoult & Vuillemin (1979), 10.1016/0304-3975(79)90009-4; Biedl (2021), 10.1016/j.ipl.2021.106230.

## Paper 2 survey (2026-10-09)

Pathwidth on intersection and perfect-graph classes; the survey is
`paper2/survey_intersection_classes.md`, whose §6 lists everything still to
obtain, with DOIs. The most important of those are: Gustedt (1993) DAM 45,
doi:10.1016/0166-218X(93)90012-D, which is bronze OA, but the Elsevier bot check
refused it. Möhring (1996) "Triangulating graphs without asteroidal triples",
DAM 64:281–287 (AT-free ⇒ pw = tw). Habib & Möhring (1994) Order 11,
doi:10.1007/BF01462229. Kloks, Kratsch & Spinrad (1997) TCS,
doi:10.1016/S0304-3975(96)00206-X, which is OA at research.utwente.nl but a bot
check refused it. Kloks, Kratsch & Müller "Dominoes",
doi:10.1007/3-540-59071-4_41. Garbe (1995), doi:10.1007/3-540-59071-4_35.

**Obtained in this sweep** (all opened and read where cited). The Utrecht
technical reports came through the UU DSpace REST API
(`https://dspace.library.uu.nl/server/api/pid/find?id=hdl:1874/<n>`), because the
HTML front end is JavaScript-only:

- `1990-Bodlaender-Mohring-Pathwidth-Treewidth-Cographs-TR-RUU-CS-90-7.pdf` — hdl:1874/16625; TR of SIAM JDM 6 (1993) 181–188, doi:10.1137/0406014. Scanned. Thm 3.2: pw = tw on cographs. Lemma 3.4: pw of a disjoint union is the max, and **pw(G × H) = min(pw(G) + |W|, pw(H) + |V|)** for the join. O(n) algorithms from the cotree.
- `1992-Bodlaender-Kloks-Kratsch-Treewidth-Pathwidth-Permutation-Graphs-TR-UU.pdf` — hdl:1874/16673; TR of SIAM JDM 8 (1995) 606–616, doi:10.1137/S089548019223992X. pw = tw on permutation graphs, O(nk²) given the matching diagram.
- `1992-Kloks-Bodlaender-Approximating-Treewidth-Pathwidth-Perfect-Graphs-TR-RUU-CS-92-29.pdf` — hdl:1874/16672; doi:10.1007/3-540-56279-6_64 (ISAAC'92). pw ≤ 3tw + 4 on cotriangulated graphs, ≤ 2tw + 1 on convex graphs, ≤ 2tw on permutation graphs, O(tw²) on cocomparability graphs.
- `1992-Kloks-Kratsch-Treewidth-Chordal-Bipartite-Graphs-TR-RUU-CS-92-28.pdf` — hdl:1874/16671; TR of J. Algorithms (1995), doi:10.1006/jagm.1995.1037. Treewidth polynomial on chordal bipartite graphs.
- `1995-Bodlaender-Kloks-Kratsch-Muller-Treewidth-Fill-in-d-Trapezoid-Graphs-TR-UU-CS-95-34.pdf` — TU/e pure; doi:10.1142/9789812777638_0008. d-trapezoid tw = pw in O(n·tw^(d−1)), trapezoid O(n²); p. 2 lists class complexities, and Thm 2.2 (Möhring 1996) is pw = tw on AT-free.
- `1997-Bodlaender-Treewidth-Algorithmic-Techniques-Results-MFCS.pdf` — hdl:1874/18736. Treewidth is NP-complete on bipartite and cocomparability graphs (p. 2).
- `2006-Fomin-Hoie-Pathwidth-Cubic-Graphs-Exact-Algorithms-IPL.pdf` — author page; IPL 97:191–196. pw ≤ n/6 + εn for cubic graphs.
- `2007-Suchan-Todinca-Pathwidth-Circular-Arc-Graphs-WG.pdf` — author copy (univ-orleans.fr); doi:10.1007/978-3-540-74839-7_25. O(n²) pathwidth on circular-arc graphs, where pw ≠ tw.
- `2014-Adler-Kante-Kwon-Linear-Rank-Width-Distance-Hereditary-Graphs-I-arXiv.pdf` — arXiv:1403.1081. p. 2: pathwidth NP-hard on distance-hereditary graphs [Kloks, Bodlaender, Müller & Kratsch, ESA 1993].

## Paper 2 survey (2026-10-09)

### Trees and sparse classes (`paper2/survey_trees_sparse.md`)

Downloaded 2026-10-09, each opened and checked against its title page:

- **Proskurowski, A. & Telle, J.A.** (1999). Classes of graphs with restricted interval models. *DMTCS* 3, 167–176 — `1999-Proskurowski-Telle-Classes-Graphs-Restricted-Interval-Models-DMTCS.pdf` (dmtcs.episciences.org/263). Thm 6.2: k-caterpillars are the edge-maximal graphs of pathwidth k.
- **Bodlaender, H.L. & Fomin, F.V.** (2000). Approximation of pathwidth of outerplanar graphs. Tech. rep. UU-CS-2000-23; journal version *J. Algorithms* 43(2), 190–200 (2002), doi:10.1016/S0196-6774(02)00001-9 — `2000-Bodlaender-Fomin-Approximation-Pathwidth-Outerplanar-Graphs-TR-UU-CS-2000-23.pdf` (Utrecht repository, hdl:1874/18990). pw(T*) ≤ pw(G) ≤ 2pw(T*) + 2.
- **Markov, M.** (2004). *A fast practical algorithm for the vertex separation of unicyclic graphs*. MSc thesis, University of Victoria — `2004-Markov-Fast-Practical-Algorithm-Vertex-Separation-Unicyclic-Graphs-MSc-UVic.pdf` (hdl:1828/612). O(n log n), with an optimal layout. Journal version: Ellis & Markov, *Inf. Comput.* 192 (2004), not held.
- **Markov, M.** (2007). On the vertex separation of cactus graphs. *Serdica J. Computing* 1, 45–72, doi:10.55630/sjc.2007.1.45-72 — `2007-Markov-Vertex-Separation-Cactus-Graphs-SerdicaJComput.pdf`. Thm 1, p. 62: characterisation; no algorithm.
- **Markov, M.** (2008). On the vertex separation of maximal outerplanar graphs. *Serdica J. Computing* 2, 207–238, doi:10.55630/sjc.2008.2.207-238 — `2008-Markov-Vertex-Separation-Maximal-Outerplanar-Graphs-SerdicaJComput.pdf`. Thm 2, p. 233: characterisation by affixability.
- **Mihai, R. & Todinca, I.** (2009). Pathwidth is NP-hard for weighted trees. FAW 2009, LNCS 5598, 181–195, doi:10.1007/978-3-642-02270-8_20 — author copy (univ-orleans.fr/lifo/Members/todinca/PS/pwdhard.pdf), `2009-Mihai-Todinca-Pathwidth-NP-Hard-Weighted-Trees-FAW-author.pdf`. NP-hard on octopus graphs (Thm 3) and weighted trees (Thm 4); both are natural MOSP instances.
- **Barát, J., Hajnal, P., Lin, Y. & Yang, A.** (2012). On the structure of graphs with path-width at most two. arXiv:0910.4889 — `2012-Barat-Hajnal-Lin-Yang-Structure-Graphs-Path-Width-At-Most-Two-arXiv.pdf`.
- **Babu, J., Basavaraju, M., Chandran, L.S. & Rajendraprasad, D.** (2014). 2-connecting outerplanar graphs without blowing up the pathwidth. *TCS*, doi:10.1016/j.tcs.2014.04.032; arXiv:1212.6382 — `2014-Babu-Basavaraju-Chandran-Rajendraprasad-2-Connecting-Outerplanar-Graphs-Pathwidth-TCS-arXiv.pdf`.
- **Briański, M., Joret, G. & Seweryn, M.T.** (2024). Pathwidth vs cocircumference. *SIAM J. Discrete Math.*, doi:10.1137/23m158663x; arXiv:2306.03621 — `2024-Brianski-Joret-Seweryn-Pathwidth-vs-Cocircumference-SIDMA-arXiv.pdf`.

Still to obtain, mostly Elsevier open archive behind a browser check, none circumvented (full list with DOIs in the survey, §3): Skodinis 2003 (doi:10.1016/S0196-6774(02)00225-0); Scheffler 1990 (doi:10.1007/978-3-642-46908-4_70); Peng et al. 2000 (doi:10.1016/S0304-3975(99)00241-8); Chou, Ko, Ho & Chen 2008, block graphs (doi:10.1016/j.dam.2007.08.007); Ellis & Markov 2004 (doi:10.1016/j.ic.2004.03.005); Fomin & Thilikos 2006, Halin (doi:10.1016/j.jda.2005.06.004); Gustedt 1993 (doi:10.1016/0166-218X(93)90012-D); Takahashi, Ueno & Kajitani 1994 (doi:10.1016/0012-365X(94)90092-2); Megiddo et al. 1988 (doi:10.1145/42267.42268); Kneis et al. 2009 (doi:10.1137/080715482); Biedl 2022 (doi:10.1016/j.ipl.2021.106230); Coudert, Huc & Mazauric 2012 (doi:10.1007/s00453-011-9524-3); Yanasse 1996, *Pesquisa Operacional* 16(1), 1–26 (no DOI found).

### Obtained 2026-10-09 by the owner (browser downloads), copied from ~/Downloads

Each opened and identified from its first page:
- Chou, Ko, Ho & Chen (2008), Node-searching problem on block graphs, *DAM* 156:55–75 — `2008-Chou-Ko-Ho-Chen-Node-Searching-Block-Graphs-DAM.pdf`
- Ellis & Warren (2008), Lower bounds on the pathwidth of some grid-like graphs, *DAM* 156:545–555 — `2008-Ellis-Warren-Lower-Bounds-Pathwidth-Grid-Like-Graphs-DAM.pdf`
- Kozawa, Otachi & Yamazaki (2014), Lower bounds for treewidth of product graphs, *DAM* 162:251–258 — `2014-Kozawa-Otachi-Yamazaki-Lower-Bounds-Treewidth-Product-Graphs-DAM.pdf`
- Kiyomi, Okamoto & Otachi (2016), On the treewidth of toroidal grids, *DAM* 198:303–306 — `2016-Kiyomi-Okamoto-Otachi-Treewidth-Toroidal-Grids-DAM.pdf`
- Djelloul (2009), Treewidth and logical definability of graph products, *TCS* 410:696–710 — `2009-Djelloul-Treewidth-Logical-Definability-Graph-Products-TCS.pdf`
- Meister (2010), Treewidth and minimum fill-in on permutation graphs in linear time, *TCS* 411:3685–3700 — `2010-Meister-Treewidth-Fill-in-Permutation-Graphs-Linear-Time-TCS.pdf`
- Fomin & Thilikos (2006), A 3-approximation for the pathwidth of Halin graphs, *J. Discrete Algorithms* 4:499–510 — `2006-Fomin-Thilikos-3-Approximation-Pathwidth-Halin-Graphs-JDA.pdf`
- Megiddo, Hakimi, Garey, Johnson & Papadimitriou (1988), The complexity of searching a graph, *J. ACM* 35:18–44 — `1988-Megiddo-Hakimi-Garey-Johnson-Papadimitriou-Complexity-Searching-Graph-JACM.pdf`
- Coudert, Huc & Mazauric (2012), A distributed algorithm for computing the node search number in trees, *Algorithmica* 63:158–190 (HAL inria-00587819) — `2012-Coudert-Huc-Mazauric-Distributed-Algorithm-Node-Search-Number-Trees-Algorithmica-HAL.pdf`
- Olsar (2004), Updating the vertex separation of a dynamically changing tree, MMath thesis, Waterloo (hdl 10012/1163) — `2004-Olsar-Updating-Vertex-Separation-Dynamically-Changing-Tree-MMath-Waterloo.pdf`
- Cao, Liu, Lu & Lv (2023), Treewidth of the q-Kneser graphs, *DAM* (arXiv 2101.04518v2) — `2023-Cao-Liu-Lu-Lv-Treewidth-q-Kneser-Graphs-DAM-arXiv.pdf`
- Ellis (2023), Computing the pathwidth and bandwidth of solid, convex grids, SSRN 4592858 (preprint) — `2023-Ellis-Computing-Pathwidth-Bandwidth-Solid-Convex-Grids-SSRN.pdf`
- Kloks (1994), Treewidth and pathwidth of cocomparability graphs of bounded dimension, LNCS 842 ch. 12 (doi 10.1007/BFb0045387) — **2-page Springer preview only, incomplete**: `1994-Kloks-Treewidth-Pathwidth-Cocomparability-Bounded-Dimension-LNCS842-ch12-PREVIEW-2pp.pdf`. The full chapter is still to obtain.

Not obtained: Balogh, Bezrukov, Harper & Seress (2008) — only the ScienceDirect landing page (HTML) was downloaded, not the PDF.

### Obtained 2026-10-09, second batch (owner's browser downloads)

Complete papers, each identified from its first page:
- Gustedt (1993), On the pathwidth of chordal graphs, *DAM* 45:233–248 — `1993-Gustedt-Pathwidth-Chordal-Graphs-DAM.pdf`
- Kloks, Kratsch & Spinrad (1997), On treewidth and minimum fill-in of asteroidal triple-free graphs, *TCS* 175:309–335 — `1997-Kloks-Kratsch-Spinrad-Treewidth-Fill-in-AT-Free-Graphs-TCS.pdf`
- Peng, Ho, Hsu, Ko & Tang (2000), Edge and node searching problems on trees, *TCS* 240:429–446 — `2000-Peng-Ho-Hsu-Ko-Tang-Edge-Node-Searching-Trees-TCS.pdf`
- Ellis & Markov (2004), Computing the vertex separation of unicyclic graphs, *Inf. Comput.* 192:123–161 — `2004-Ellis-Markov-Computing-Vertex-Separation-Unicyclic-Graphs-IC.pdf`
- Takahashi, Ueno & Kajitani (1994), Minimal acyclic forbidden minors for the family of graphs with bounded path-width, *Discrete Math.* 127:293–304 — `1994-Takahashi-Ueno-Kajitani-...-DM.pdf`
- Bienstock, Robertson, Seymour & Thomas (1991), Quickly excluding a forest, *JCTB* 52:274–283 — `1991-Bienstock-Robertson-Seymour-Thomas-Quickly-Excluding-Forest-JCTB.pdf`
- Flajolet, Raoult & Vuillemin (1979), The number of registers required for evaluating arithmetic expressions, *TCS* 9:99–125 — `1979-Flajolet-Raoult-Vuillemin-...-TCS.pdf`
- Díaz, Petit, Serna & Trevisan (2001), Approximating layout problems on random graphs, *Discrete Math.* 235:245–253 — `2001-Diaz-Petit-Serna-Trevisan-...-DM.pdf`
- Karoński & Szymkowiak (2001), On a solution of a randomized three tracks variant of the Gate Matrix Layout problem, *Discrete Math.* 236:179–189 — `2001-Karonski-Szymkowiak-Randomized-Three-Tracks-Gate-Matrix-Layout-DM.pdf`
- Harper (1966), Optimal numberings and isoperimetric problems on graphs, *J. Combin. Theory* 1:385–393 — `1966-Harper-Optimal-Numberings-Isoperimetric-Problems-Graphs-JCT.pdf`
- Harper (1999), On an isoperimetric problem for Hamming graphs, *DAM* 95:285–309 — `1999-Harper-Isoperimetric-Problem-Hamming-Graphs-DAM.pdf`
- Broersma, Dahlhaus & Kloks (2000), A linear time algorithm for minimum fill-in and treewidth for distance hereditary graphs, *DAM* 99:367–400 — `2000-Broersma-Dahlhaus-Kloks-...-DAM.pdf`
- Böttcher, Pruessmann, Taraz & Würfl (2010), Bandwidth, expansion, treewidth, separators and universality for bounded-degree graphs, *European J. Combin.* 31:1217–1227 — `2010-Bottcher-...-EJC.pdf`
- Bezrukov, Elsässer, Monien, Preis & Tillich (2004), New spectral lower bounds on the bisection width of graphs, *TCS* 320:155–174 — `2004-Bezrukov-...-TCS.pdf`
- Nikoletseas, Raptopoulos & Spirakis (2008), Large independent sets in general random intersection graphs, *TCS* 406:215–224 — `2008-Nikoletseas-...-TCS.pdf`
- Balogh, Bezrukov, Harper & Seress (2008), On the bandwidth of 3-dimensional Hamming graphs, *TCS* 407:488–495 — `2008-Balogh-Bezrukov-Harper-Seress-Bandwidth-3D-Hamming-Graphs-TCS.pdf`
- Dereniowski (2011), From pathwidth to connected pathwidth (arXiv 1007.1269v2) — `2011-Dereniowski-From-Pathwidth-to-Connected-Pathwidth-STACS-arXiv.pdf`
- Shang (2022), On the tree-depth and tree-width in heterogeneous random graphs, *Proc. Japan Acad. A* 98:78– — `2022-Shang-...-PJA.pdf`
- Wang, Wu & Dumitrescu (2009), On explicit formulas for bandwidth and antibandwidth of hypercubes, *DAM* 157:1947–1952 — `2009-Wang-Wu-Dumitrescu-...-DAM.pdf`
- Kloks & Bodlaender (1992), Only few graphs have bounded treewidth, Utrecht tech report — `1992-Kloks-Bodlaender-Only-Few-Graphs-Bounded-Treewidth-TR-UU.pdf`
- Lagerås & Lindholm (2008), A note on the component structure in random intersection graphs with tunable clustering, *Electron. J. Combin.* 15 — `2008-Lageras-Lindholm-...-EJC.pdf`

**Springer 2-page previews only** (first pages; the full papers are still to obtain):
Gao (2006) COCOON; Chandran, Kavitha & Subramanian (2003) COCOON; Kloks, Bodlaender, Müller & Kratsch (1993) ESA; Garbe (1995) WG; Kloks, Kratsch & Müller (1995) Dominoes, WG; Peng & Yang (2007) TAMC; Krishna et al. (2010). Files end in `-PREVIEW-2pp.pdf`.

### Obtained 2026-10-09, third batch

- Coja-Oghlan, Cooley, Kang & Skubch (2017), The minimum bisection in the planted bisection model, *Theory of Computing* 13(8):1–22 — `2017-Coja-Oghlan-Cooley-Kang-Skubch-Minimum-Bisection-Planted-Bisection-Model-ToC.pdf`. Not on the to-fetch list; it was probably found while searching for Łuczak & McDiarmid (2001), *Bisecting sparse random graphs*, which is still to obtain. It is relevant to the bisection-width lower bounds of the random-graph survey (`paper2/survey_random_extremal.md`).

**The search stopped here (2026-10-09), at diminishing returns.** What is still missing is listed in `paper2/to_fetch.md` (with search links in `to_fetch.html`). Most of it is paywalled, needs a library, or is a Springer chapter of which only a 2-page preview was free. The ones that matter most for paper 2: Möhring (1996), AT-free ⇒ pw = tw; Karoński, Scheinerman & Singer-Cohen (1999), the random intersection model; Scheffler (1990), linear pathwidth of trees; Lin & Lin (2025), hypercubes.

### Obtained 2026-10-09, fourth batch

- Kumfert & Pothen (1997), Two improved algorithms for envelope and wavefront reduction, ICASE Report 97-33 / NASA CR-201714 (the technical-report version of the *BIT* 37 paper) — `1997-Kumfert-Pothen-Two-Improved-Algorithms-Envelope-Wavefront-Reduction-ICASE-97-33.pdf`. It defines the wavefront, for the candidate row "maximum wavefront = pw + 1" (`paper2/complex_members.md`, row 8).

## Pathwidth lower bounds (2026-10-11)

From the lower-bound survey `reports/pathwidth_lower_bounds_survey.md`. Downloaded into `literature/` the same day, open access, each opened and checked against its citation:

- `2010-Bodlaender-Koster-Treewidth-Computations-II-Lower-Bounds-TR-UU-CS-2010-022.pdf`: the TR of the IC 2011 survey.
- `2006-Bodlaender-Wolle-Koster-Contraction-Treewidth-Lower-Bounds-JGAA.pdf`: *JGAA* 10(1), 5–49, doi:10.7155/jgaa.00117. Tables 9 and 19 hold the myciel lower bounds (myciel6 LBP+(MD) = 29, myciel7 = 52).
- `2004-Gogate-Dechter-Complete-Anytime-Algorithm-Treewidth-UAI-arXiv.pdf`: UAI 2004, arXiv 1207.4109. Minor-min-width; Table 4 has myciel3–7.
- `2024-Gima-Hanaka-Noro-Ono-Otachi-Improved-Spectral-Lower-Bound-Treewidth-arXiv.pdf`: arXiv 2404.08520, published as *Inform. Process. Lett.* 188 (2025) 106536, doi:10.1016/j.ipl.2024.106536. tw ≥ nλ₂/(Δ+λ₂) − 1.
- `2006-Bodlaender-Fomin-Koster-Kratsch-Thilikos-Exact-Algorithms-Treewidth-TR-UU-CS-2006-032.pdf`, `2005-Bodlaender-Grigoriev-Koster-Treewidth-Lower-Bounds-Brambles-TR-UU-CS-2005-051.pdf`, `2004-Koster-Wolle-Bodlaender-Degree-Based-Treewidth-Lower-Bounds-TR-UU-CS-2004-050.pdf`, `2004-Bodlaender-Koster-Maximum-Cardinality-Search-Lower-Bound-Treewidth-TR-UU-CS-2004-053.pdf`: Utrecht technical-report versions of the journal papers listed below.

Still to obtain (or only the TR is held):

- Bodlaender, H.L. & Koster, A.M.C.A. (2011). Treewidth computations II. Lower bounds. *Information and Computation* 209(7), 1103–1119. [doi:10.1016/j.ic.2011.04.003](https://doi.org/10.1016/j.ic.2011.04.003). [Google](https://www.google.com/search?q=Bodlaender+Koster+%22Treewidth+computations+II.+Lower+bounds%22+filetype%3Apdf). The survey this sweep starts from. **The technical report is now held** (`2010-Bodlaender-Koster-Treewidth-Computations-II-Lower-Bounds-TR-UU-CS-2010-022.pdf`, UU-CS-2010-022, 29 pp.); the journal version is Elsevier open archive, browser only.
- Clautiaux, F., Carlier, J., Moukrim, A. & Nègre, S. (2003). New lower and upper bounds for graph treewidth. WEA 2003, LNCS 2647, 70–80. [doi:10.1007/3-540-44867-5_6](https://doi.org/10.1007/3-540-44867-5_6). [Google](https://www.google.com/search?q=Clautiaux+Carlier+Moukrim+Negre+%22New+lower+and+upper+bounds+for+graph+treewidth%22+filetype%3Apdf). Origin of the improved-graph method (LBN/LBP). Its common-neighbour lemma also holds for pathwidth (survey §2.1).
- Clautiaux, F., Moukrim, A., Nègre, S. & Carlier, J. (2004). Heuristic and meta-heuristic methods for computing graph treewidth. *RAIRO Oper. Res.* 38(1), 13–26. [doi:10.1051/ro:2004011](https://doi.org/10.1051/ro:2004011). [Google](https://www.google.com/search?q=Clautiaux+Moukrim+Negre+Carlier+%22Heuristic+and+meta-heuristic+methods+for+computing+graph+treewidth%22+filetype%3Apdf). Journal version of LBN/LBP.
- Bodlaender, H.L., Grigoriev, A. & Koster, A.M.C.A. (2008). Treewidth lower bounds with brambles. *Algorithmica* 51(1), 81–98. [doi:10.1007/s00453-007-9056-z](https://doi.org/10.1007/s00453-007-9056-z). [Google](https://www.google.com/search?q=Bodlaender+Grigoriev+Koster+%22Treewidth+lower+bounds+with+brambles%22+filetype%3Apdf). **TR held** (`2005-Bodlaender-Grigoriev-Koster-Treewidth-Lower-Bounds-Brambles-TR-UU-CS-2005-051.pdf`); journal version not needed.
- Lucena, B. (2003). A new lower bound for tree-width using maximum cardinality search. *SIAM J. Discrete Math.* 16(3), 345–353. [doi:10.1137/S0895480101397773](https://doi.org/10.1137/S0895480101397773). [Google](https://www.google.com/search?q=Lucena+%22A+new+lower+bound+for+tree-width+using+maximum+cardinality+search%22+filetype%3Apdf). MCSLB. Treewidth bound; the MCS TR of Bodlaender & Koster (UU-CS-2004-053) is now held and restates it.
- Ramachandramurthi, S. (1997). The structure and number of obstructions to treewidth. *SIAM J. Discrete Math.* 10(1), 146–157. [doi:10.1137/S0895480195280010](https://doi.org/10.1137/S0895480195280010). [Google](https://www.google.com/search?q=Ramachandramurthi+%22The+structure+and+number+of+obstructions+to+treewidth%22+filetype%3Apdf). The γ_R bound.
- Koster, A.M.C.A., Wolle, T. & Bodlaender, H.L. (2005). Degree-based treewidth lower bounds. WEA 2005, LNCS 3503, 101–112. [doi:10.1007/11427186_11](https://doi.org/10.1007/11427186_11). [Google](https://www.google.com/search?q=Koster+Wolle+Bodlaender+%22Degree-based+treewidth+lower+bounds%22+filetype%3Apdf). **TR held** (`2004-Koster-Wolle-Bodlaender-Degree-Based-Treewidth-Lower-Bounds-TR-UU-CS-2004-050.pdf`).
- Bodlaender, H.L. & Koster, A.M.C.A. (2007). On the maximum cardinality search lower bound for treewidth. *Discrete Appl. Math.* 155(11), 1348–1372. [doi:10.1016/j.dam.2007.02.004](https://doi.org/10.1016/j.dam.2007.02.004). [Google](https://www.google.com/search?q=Bodlaender+Koster+%22On+the+maximum+cardinality+search+lower+bound+for+treewidth%22+filetype%3Apdf). **TR held** (`2004-Bodlaender-Koster-Maximum-Cardinality-Search-Lower-Bound-Treewidth-TR-UU-CS-2004-053.pdf`).
- Chandran, L.S. & Subramanian, C.R. (2003). A spectral lower bound for the treewidth of a graph and its consequences. *Inform. Process. Lett.* 87(4), 195–200. [doi:10.1016/S0020-0190(03)00286-2](https://doi.org/10.1016/S0020-0190(03)00286-2). [Google](https://www.google.com/search?q=Chandran+Subramanian+%22A+spectral+lower+bound+for+the+treewidth+of+a+graph+and+its+consequences%22+filetype%3Apdf). Superseded in strength by Gima et al. (2025), held; Elsevier open archive.
- Chandran, L.S. & Subramanian, C.R. (2005). Girth and treewidth. *J. Combin. Theory Ser. B* 93(1), 23–32. [doi:10.1016/j.jctb.2004.05.004](https://doi.org/10.1016/j.jctb.2004.05.004). [Google](https://www.google.com/search?q=Chandran+Subramanian+%22Girth+and+treewidth%22+filetype%3Apdf). Girth/average-degree bound and the expansion bound N_min(G, s) − 1 (BK 2010 TR §10.3). Triangle-free graphs such as Mycielski's are its natural target, but the bound is tiny there.
- Mohar, B. & Poljak, S. (1993). Eigenvalues in combinatorial optimization. In *Combinatorial and Graph-Theoretical Problems in Linear Algebra*, IMA Vol. 50, 107–151. Springer. [doi:10.1007/978-1-4613-8354-3_5](https://doi.org/10.1007/978-1-4613-8354-3_5). [Google](https://www.google.com/search?q=Mohar+Poljak+%22Eigenvalues+in+combinatorial+optimization%22+filetype%3Apdf). Source of the spectral vertex-separator bound |C| ≥ 4λ₂|A||B|/(Δn − λ₂|A∪B|), quoted in Díaz–Petit–Serna (2002) Thm 9.4, p. 339 (held).
- Juvan, M. & Mohar, B. (1992). Optimal linear labelings and eigenvalues of graphs. *Discrete Appl. Math.* 36(2), 153–168. [doi:10.1016/0166-218X(92)90229-4](https://doi.org/10.1016/0166-218X(92)90229-4). [Google](https://www.google.com/search?q=Juvan+Mohar+%22Optimal+linear+labelings+and+eigenvalues+of+graphs%22+filetype%3Apdf). Spectral and path-method bounds for layout problems (DPS 2002 §9.1–9.2).
- Alon, N. & Milman, V.D. (1985). λ₁, isoperimetric inequalities for graphs, and superconcentrators. *J. Combin. Theory Ser. B* 38(1), 73–88. [doi:10.1016/0095-8956(85)90092-9](https://doi.org/10.1016/0095-8956(85)90092-9). [Google](https://www.google.com/search?q=Alon+Milman+%22isoperimetric+inequalities+for+graphs%2C+and+superconcentrators%22+filetype%3Apdf). The weaker original of the Mohar–Poljak separator bound.
- Bodlaender, H.L., Fomin, F.V., Koster, A.M.C.A., Kratsch, D. & Thilikos, D.M. (2012). On exact algorithms for treewidth. *ACM Trans. Algorithms* 9(1), 12. [doi:10.1145/2390176.2390188](https://doi.org/10.1145/2390176.2390188). [Google](https://www.google.com/search?q=Bodlaender+Fomin+Koster+Kratsch+Thilikos+%22On+exact+algorithms+for+treewidth%22+filetype%3Apdf). **TR held** (`2006-Bodlaender-Fomin-Koster-Kratsch-Thilikos-Exact-Algorithms-Treewidth-TR-UU-CS-2006-032.pdf`). Origin of 'contract to a minor, then solve it exactly' as a lower bound, the method that closes myciel6 in the survey.
- Wolle, T. (2005). *Computational aspects of treewidth: Lower bounds and network reliability.* PhD thesis, Utrecht University. no DOI. [Google](https://www.google.com/search?q=Wolle+%22Computational+aspects+of+treewidth%3A+Lower+bounds+and+network+reliability%22+filetype%3Apdf). The long form of the contraction and LBN+/LBP+ work; no open copy found.
- Bienstock, D. (1991). Graph searching, path-width, tree-width and related problems (a survey). In *Reliability of Computer and Communication Networks*, DIMACS Series 5, 33–50. [doi:10.1090/dimacs/005/02](https://doi.org/10.1090/dimacs/005/02). [Google](https://www.google.com/search?q=Bienstock+%22Graph+searching%2C+path-width%2C+tree-width+and+related+problems%22+filetype%3Apdf). Search-game view of pathwidth lower bounds.
- Fomin, F.V. & Thilikos, D.M. (2008). An annotated bibliography on guaranteed graph searching. *Theoret. Comput. Sci.* 399(3), 236–245. [doi:10.1016/j.tcs.2008.02.040](https://doi.org/10.1016/j.tcs.2008.02.040). [Google](https://www.google.com/search?q=Fomin+Thilikos+%22An+annotated+bibliography+on+guaranteed+graph+searching%22+filetype%3Apdf). Map of the search-number literature (node, edge, mixed search); Elsevier open archive.
- Dendris, N.D., Kirousis, L.M. & Thilikos, D.M. (1997). Fugitive-search games on graphs and related parameters. *Theoret. Comput. Sci.* 172(1–2), 233–254. [doi:10.1016/S0304-3975(96)00177-6](https://doi.org/10.1016/S0304-3975(96)00177-6). [Google](https://www.google.com/search?q=Dendris+Kirousis+Thilikos+%22Fugitive-search+games+on+graphs+and+related+parameters%22+filetype%3Apdf). Robber strategies as lower-bound certificates for search numbers.
- Fraire-Huacuja, H.J., Castillo-García, N., López-Locés, M.C., Martínez Flores, J.A., Pazos R., R.A., González Barbosa, J.J. & Carpio V., J.M. (2016). Integer linear programming formulation and exact algorithm for computing pathwidth. In *Nature-Inspired Design of Hybrid Intelligent Systems*, Studies in Computational Intelligence 667 (volume number not verified), 673–686. [doi:10.1007/978-3-319-47054-2_44](https://doi.org/10.1007/978-3-319-47054-2_44). [Google](https://www.google.com/search?q=Fraire-Huacuja+%22Integer+linear+programming+formulation+and+exact+algorithm+for+computing+pathwidth%22+filetype%3Apdf). Already listed in `pathwidth_solvers_README.md` §1; repeated here because its B&B may carry a lower bound.
- Solano, F. & Pióro, M. (2010). Lightpath reconfiguration in WDM networks. *J. Opt. Commun. Netw.* 2(12), 1010 (end page not verified). [doi:10.1364/JOCN.2.001010](https://doi.org/10.1364/JOCN.2.001010). [Google](https://www.google.com/search?q=Solano+Pioro+%22Lightpath+reconfiguration+in+WDM+networks%22+filetype%3Apdf). The original pathwidth B&B and MILP extended by Coudert et al.; CMN 2016 [46] says the Mycielski graphs are hard for the IP formulations.
- Mycielski, J. (1955). Sur le coloriage des graphs. *Colloq. Math.* 3, 161–162. [doi:10.4064/cm-3-2-161-162](https://doi.org/10.4064/cm-3-2-161-162). [Google](https://www.google.com/search?q=Mycielski+%22Sur+le+coloriage+des+graphs%22+filetype%3Apdf). The construction; two pages, for the citation only.
- Lin, L. & Lin, Y. (2025). Discrete isoperimetric method for bandwidth, pathwidth and treewidth of hypercubes. *Discrete Appl. Math.* 363, 201–214. [doi:10.1016/j.dam.2024.12.001](https://doi.org/10.1016/j.dam.2024.12.001). [Google](https://www.google.com/search?q=Lin+Lin+%22Discrete+isoperimetric+method+for+bandwidth%2C+pathwidth+and+treewidth+of+hypercubes%22+filetype%3Apdf). Already listed under the paper-2 survey; the most recent isoperimetric pathwidth paper.

## Talent scheduling (film shooting), 2026-10-17

For the introduction's list of MOSP's guises (`paper1/todo.md`, "The introduction").

- **Cheng, T.C.E., Diamond, J.E. & Lin, B.M.T.** (1993). Optimal scheduling in film production to minimize talent hold cost. *Journal of Optimization Theory and Applications* 79(3), 479–492. [doi:10.1007/BF00940554](https://doi.org/10.1007/BF00940554). **Obtained 2026-10-17** (the owner's download): `1993-Cheng-Diamond-Lin-Film-Production-Talent-Hold-Cost-JOTA.pdf`.
- **Garcia de la Banda, M., Stuckey, P.J. & Chu, G.** (2011). Solving talent scheduling with dynamic programming. *INFORMS Journal on Computing* 23(1), 120–137. [doi:10.1287/ijoc.1090.0378](https://doi.org/10.1287/ijoc.1090.0378). Open author copy: [people.eng.unimelb.edu.au/pstuckey/papers/rehearsal.pdf](https://people.eng.unimelb.edu.au/pstuckey/papers/rehearsal.pdf) **Obtained 2026-10-17** (the owner's download, the author's preprint in the journal's template): `2011-Garcia-de-la-Banda-Stuckey-Chu-Solving-Talent-Scheduling-Dynamic-Programming-IJOC.pdf`.

## House of Graphs, 2026-10-17 (obtained, the owner's downloads)

- **Coolsaet, K., D'hondt, S. & Goedgebeur, J.** (2022). House of Graphs 2.0: a database of interesting graphs and more. arXiv:2210.17253 (v1) — `2022-Coolsaet-Dhondt-Goedgebeur-House-of-Graphs-2.0-arXiv-2210.17253.pdf`. The journal version should be checked before citing.
- **Devillez, G., D'hondt, S. & Goedgebeur, J.** (2026). Knowledge management in House of Graphs. arXiv:2603.23070 (v2) — `2026-Devillez-Dhondt-Goedgebeur-Knowledge-Management-House-of-Graphs-arXiv-2603.23070.pdf`.

## Rihm (2012), 2026-10-18

- `2012-Rihm-Gueltige-Ungleichungen-Pfadweite-Problem-MSc-RWTH-Koster.pdf`:
  Tom Rihm, *Gültige Ungleichungen für das Pfadweite-Problem* (valid inequalities
  for the pathwidth problem), master's thesis, RWTH Aachen, January 2012,
  supervised by Arie Koster; from the owner's downloads. ILP models of pathwidth
  and their valid inequalities, with a computational study on the Mycielski
  graphs Myciel3–5 (§9). Its values agree with ours: pw(Myciel3) = 5, and its
  inequality (7.14) gives the lower bound 10 on Myciel4 (23 vertices), our exact
  value.

## Bonnet (2024), 2026-10-18

- `2024-Bonnet-Twin-Width-Contraction-Sequences-HDR-ENS-Lyon-tel-04990502.pdf`:
  Édouard Bonnet, *Twin-Width and Contraction Sequences*, habilitation thesis,
  ENS Lyon, 2024, HAL tel-04990502 (114 pp.); from the owner's downloads.
  Contraction sequences of a different kind from our minor bound's (twin-width
  contracts arbitrary vertex pairs, not edges).

## Width parameters of Mycielskians, 2026-10-18

Searched (arXiv, web, ISGCI) for pathwidth, treewidth, vertex separation,
bandwidth or cutwidth of μ(G) or of the Mycielski graphs: **no paper found**
that bounds any of them in terms of G. ISGCI (class gc_1215) lists them as
unknown. Exact values exist only as benchmark rows: Tamaki (2017/2019,
already held, `2017-Tamaki-Positive-Instance-Driven-DP-Treewidth-ESA-arXiv.pdf`)
gives tw(myciel2..6) = 2, 5, 10, 19, 35, with myciel7 open; SageMath's
`vertex_separation` documentation gives vs(MycielskiGraph(5)) = 10. Nothing
saved. Findings: `reports/mycielski_pathwidth.md`.

## Chandran, Kavitha & Subramanian (2003), full text, 2026-10-18

- `2003-Chandran-Kavitha-Subramanian-Isoperimetric-Inequalities-Width-Parameters-COCOON.pdf`
  (10 pp., from the owner's downloads) replaces the 2-page preview listed above as
  paywalled. The conference version of Chandran & Kavitha (2006): isoperimetric
  lower bounds for treewidth, pathwidth and carving width, the exact pathwidth of
  the hypercube (formalised in `lean/MOSPFormalization/Hypercube.lean`), and
  Hamming graphs.

## The separator first moment (loop0011 item 01, 2026-11-01)

Read for `reports/separator_moment.md` §1. Obtained this item, in `literature/`
with the repository's naming: Dembo, Montanari & Sen 2017 (arXiv 1503.03923;
*Ann. Probab.* 45(2), doi:10.1214/15-AOP1084), Andreis, König & Patterson 2021
(the authors' revision from WIAS; *Random Structures Algorithms* 59(4) 522–553,
doi:10.1002/rsa.21007), Puhalskii 2005 (arXiv math/0402183; *Ann. Probab.* 33(1)
337–412, doi:10.1214/009117904000000784), Díaz, Serna & Wormald 2003 (the
ALCOM-FT technical report TR-03-44, the preprint of the 2007 paper below) and
Lampis 2012 (arXiv 1211.0524, no journal version found). Not obtained:

- **O'Connell, N.** (1998). Some large deviation results for sparse random
  graphs. *Probability Theory and Related Fields*, 110, 277–285.
  doi:10.1007/s004400050149 — Springer paywall (Semantic Scholar lists a
  "bronze" PDF at the publisher, which is not served without a login). Its
  LDP for the largest component is restated, with the rate function in his
  form and the note that his Theorem 3.1 "has a misprint", by Puhalskii
  (2005), remark after Corollary 2.5; Andreis–König–Patterson §1.4 say both
  his LDPs are contractions of theirs. Cite through those.
- **Luczak, M.J. & McDiarmid, C.** (2001). Bisecting sparse random graphs.
  *Random Structures & Algorithms*, 18(1), 31–38.
  doi:10.1002/1098-2418(200101)18:1<31::AID-RSA3>3.0.CO;2-1 — Wiley paywall;
  LSE Research Online record 17554 has no full text. The `ln 4` threshold for
  a linear bisection width (the giant exceeds `n/2`) is restated by
  Lichev–Mitsche 2023 p. 2, Coja-Oghlan et al. 2017 p. 4 and
  Dembo–Montanari–Sen 2017 p. 1; its spanning-tree technique by Do–Erde–Kang
  2024 §1.3.
- **Bollobás, B.** (1988). The isoperimetric number of random regular graphs.
  *European Journal of Combinatorics*, 9(3), 241–244.
  doi:10.1016/S0195-6698(88)80014-3 — Elsevier (the direct download is
  blocked). Its first-moment bound `i_E(d) ≥ d/2 − √(d ln 2)` and its exact
  pairing-model count are re-derived in Kolesnik–Wormald 2014 §§1, 2, 7 (held)
  and Lampis 2012 §3 (held).
- **Díaz, J., Serna, M.J. & Wormald, N.C.** (2007). Bounds on the bisection
  width for random d-regular graphs. *Theoretical Computer Science*, 382(2),
  120–130. doi:10.1016/j.tcs.2007.03.003 — Elsevier, blocked; the 2003
  technical report is held and carries the same Table 1 of upper bounds, with
  an analysis it calls non-rigorous.
- **Kloks, T.** (1994). *Treewidth: Computations and Approximations*, LNCS 842,
  doi:10.1007/BFb0045375 — the chapter with the first moment over balanced
  partitions of `G(n, d/n)` (linear treewidth for `d ≥ 2.36`). The held
  two-page preview is of chapter 12 (cocomparability graphs of bounded
  dimension) and contains none of it; the result is cited only as restated by
  Do–Erde–Kang 2024 p. 1, Gao 2006 p. 226, Gao 2012 §3 and Perarnau–Serra
  2014 pp. 4, 9.

Two corrections to the loop's brief recorded here so they are not repeated:
Kolesnik & Wormald 2014 is arXiv 1311.6555 (1109.0689 is a paper on payment
systems); Díaz–Diner–Serna–Serra's vertex bisection paper is published as
*J. Comput. System Sci.* 2024, doi:10.1016/j.jcss.2024.103550.

## The OpenAI mathematics collection (loop0014 item 02, 2026-11-04)

Not missing — held locally, read-only, and recorded here because one file
of it is now copied into this development.

- **OpenAI** (2026). *The Exponential Time Hypothesis is False*, family 378
  of the OpenAI mathematics collection (`github.com/openai/math`,
  Apache-2.0), manuscript of 17 October 2026 revised 25 October 2026, 64
  pages; the Lean comparator statement
  `lean/ComparatorChallenges/SubexponentialSAT.lean` (theorem
  `exact_count_and_sat`, proved in `lean/OAI/Algorithms/SubexponentialSAT/`).
  Cloned read-only at `~/dev/untrusted/openai-math` (commit `4eaee875`,
  2026-10-29); the paper is read as a `pdftotext` extract
  (`reports/scratch/subexp_pathwidth/01_audit/eth.txt`, git-ignored) and
  the Lean files with `cat`; nothing in the clone is built or run, and
  nothing is imported from it. **Copied verbatim**, under its Apache-2.0
  header: lines 1–190 and 220 of the comparator file (the definitions —
  the CNF syntax, canonical encoding, `PrimitiveMachine` model, `Trace`,
  located configurations, `runtimeScale`, `runtimeBound`; file SHA-256
  `4183b2057cff350d66848215ff7167196dfc20e1891b598fdddea59077a76685`) into
  `lean/MOSPFormalization/SubexpPathwidth/PrimitiveMachine.lean`. The
  theorem itself is **not** copied: it is restated as the named `Prop`
  `SubexpCount` in `SubexpPathwidth/Frame.lean` and never asserted
  (`reports/subexp_pathwidth.md` §2). The verified exponent is
  `n (log log n)² / √log n`; the paper's sharper exponents are paper-only
  (§1.0).

## Pathwidth, cutwidth and edge search on bounded-degree graphs (loop0014 item 07, 2026-11-05)

The classical ties between pathwidth and cutwidth that `reports/subexp_pathwidth.md`
§3.4.3 and §7 meet, none held; attribution in §7 is "we found no prior
statement in the held papers" and nothing is claimed first against them.

- **Makedon, F. & Sudborough, I.H.** (1989). On minimizing width in linear
  layouts. *Discrete Applied Mathematics* 23(3), 243–265. Cutwidth,
  topological bandwidth and search number on graphs of maximum degree 3; the
  likely source of `cw = vs(L(G))` for `Δ ≤ 3` (§7, Theorem 7.1) and of
  `es = cw` for `Δ ≤ 3` (§7.5, checked on every subcubic atlas graph with
  `n + 2m ≤ 20`, not proved here).
- **Chung, F.R.K. & Seymour, P.D.** (1989). Graphs with small bandwidth and
  cutwidth. *Discrete Mathematics* 75, 113–119. `cw ≤ O(Δ · pw)`-type bounds.
- **Korach, E. & Solel, N.** (1993). Tree-width, path-width, and cutwidth.
  *Discrete Applied Mathematics* 43(1), 97–101. `pw ≤ cw`; `tw ≤ pw ≤ tw · log n`.
- **Monien, B. & Sudborough, I.H.** (1988). Min cut is NP-complete for edge
  weighted trees. *Theoretical Computer Science* 58, 209–229. Cutwidth and
  vertex separation NP-complete on planar graphs of maximum degree 3 (§3.1
  row 9; the construction is not held, §3.6).
- **Yannakakis, M.** (1985). A polynomial algorithm for the min-cut linear
  arrangement of trees. *J. ACM* 32(4), 950–988. Cutwidth of trees is
  polynomial (cited in §7.1 for the regime `m < 1.0888 n` where Algorithm
  7.2's base is below 2).

## Paper 3, related work (loop0015 item 08, 2026-11-05)

Cited by `paper3/latex/sec9_related.tex` and not held. The two 2001 papers
are the sources of ETH and SETH; paper 3 cites them as the manuscript of
family 378 cites them (`reports/scratch/eth_audit/paper.txt` lines
3733–3736, page 66) and states the hypotheses in the manuscript's words
(its §1.1.1), quoting nothing from the originals. The audit paper is cited
for its method only; its abstract page and arXiv API record are on disk
(`paper3/related/fetched/`), its body is not. Item 08 fetched nothing
beyond the three pages `TASK.md` allows, so no Crossref record was
consulted here; the DOIs below are the ones `refs.bib` carries from the
setup's Crossref check.

- **Impagliazzo, R. & Paturi, R.** (2001). On the complexity of k-SAT.
  *Journal of Computer and System Sciences*, 62(2), 367–375. DOI:
  10.1006/jcss.2000.1727 — Elsevier; the source of ETH (the manuscript's
  "[IP01, Theorem 1]") and of SETH ("[IP01, Open Problems, item 2]").
- **Impagliazzo, R., Paturi, R. & Zane, F.** (2001). Which problems have
  strongly exponential complexity? *Journal of Computer and System
  Sciences*, 63(4), 512–530. DOI: 10.1006/jcss.2001.1774 — Elsevier; the
  Sparsification Lemma and SETH's standard setting.
- **Sienicki, M. & Sienicki, K.** (2026). A Human Audit of OpenAI's
  AI-Generated Mathematical Proofs. arXiv:2608.14673, v3 of 9 September
  2026, 13 pages, cs.AI. Open access; only the abstract page was fetched
  (the download rule of `TASK.md`), so the PDF is not in `literature/`.
  It concerns the ten results of 1 August 2026, not family 378.
- Also cited by paper 3 and not held, listed by their items: the seven
  sources of the hypotheses' variants that Section 6 cites through the
  manuscript's reference list (Dinur 2016; Manurangsi & Raghavendra 2017;
  Chalermsook et al. 2020; Carmosino et al. 2016; Dell et al. 2014; Cygan
  et al. 2016; Williams 2016 — `refs.bib` notes, item 05) and the seven
  tool and threshold papers Section 7 cites from memory (CaDiCaL 2.0;
  PySAT 2018; Ganak 2019; ApproxMC 2013; BIRD 2019; Selman, Mitchell &
  Levesque 1996; Mertens, Mézard & Zecchina 2006 — item 06). None has a
  checked DOI (`paper3/ETH_AMBIGUOUS.MD` 05c, 06c, 08c).

## Held but not committed (copyright)

- **Garey & Johnson (1979), *Computers and Intractability: A Guide to the Theory of
  NP-Completeness*.** PDF and DjVu copied from the owner's Zotero on 2026-11-06 into
  `literature/1979-Garey-Johnson-Computers-and-Intractability-NP-Completeness.{pdf,djvu}`,
  git-ignored. The reference for every NP-completeness citation in the papers (problem
  numbers GT.., SR.., and the bandwidth / linear arrangement entries).
- **De Giovanni, Massi & Pezzella (2013, IJPR)** and **De Giovanni, Massi, Pezzella, Pfetsch,
  Rinaldi & Ventura (2013, ITOR)**, received from the author on 2026-10-22: kept in
  `literature/` under their existing names, git-ignored and removed from the index on
  2026-11-06 at the owner's request (they were in commits up to 5897970cb; the history is
  not rewritten).
- **De Giovanni, Massi & Pezzella (2010), the genetic-algorithm technical report**: treated the
  same way on 2026-11-06 (held on disk, git-ignored, removed from the index; the history is not rewritten, by the owner's decision).

## Blockages as a bound (2026-11-07, `reports/blockage_class.md`)

Looked for a published analogue, for pathwidth and blockages, of brambles built as
treewidth lower bounds (Bodlaender, Grigoriev & Koster 2005). We found no prior
statement of a blockage class used as a computed lower bound. What the search did find
(**all three obtained 2026-11-07, in `literature/`**; the third was first recorded here
under the wrong authors, "Kim, Kim & Kwon": arXiv 1711.00718 is by Joshua Erde):

- **Diestel, R. & Oum, S.** (2019). Tangle-tree duality: in graphs, matroids and beyond.
  *Combinatorica*, 39, 879–910; arXiv 1701.02651 (open). Names the blockages of
  Bienstock, Robertson, Seymour & Thomas as the tangle-like structures dual to
  path-width, inside the general duality framework. Not held; the arXiv version is
  free. Relevant to the dual side of Appendix F, not to computation. **Held**:
  `2019-Diestel-Oum-Tangle-Tree-Duality-Graphs-Matroids-Beyond-Combinatorica-arXiv1701.02651.pdf`.
- **Groenland, C., Joret, G., Nadara, W. & Walczak, B.** (2023). Approximating pathwidth
  for graphs of small treewidth. *ACM Transactions on Algorithms*, 19(2), 16 (SODA 2021).
  arXiv 2008.00779 (open). Its certificate that `pw ≥ h` is the `T_h`-witness of its Lemma 2.1, found inside
  a tree decomposition (the subdivided complete binary tree of height `h` it implies
  certifies only `⌈h/2⌉`, p. 2) — a *branching*
  certificate, the one kind the class of `BlockageClass.lean` contains, and the one
  the census shows is almost never the obstruction on graphs with `pw > tw` at ≤ 11
  vertices. **Held**:
  `2023-Groenland-Joret-Nadara-Walczak-Approximating-Pathwidth-Small-Treewidth-TALG-arXiv2008.00779.pdf`.
- **Erde, J.** (2017). Directed path-decompositions. arXiv 1711.00718 (open; the
  Hamburg preprint). Defines directed blockages and proves the directed min-max
  theorem; it is the only other place the blockage axioms are restated in print.
  **Held**: `2017-Erde-Directed-Path-Decompositions-arXiv1711.00718.pdf`.

## Pathwidth lower bounds and NP ∩ coNP (2026-11-07)

Literature session behind `reports/pathwidth_np_conp.md` (is a pathwidth lower bound
short to check?). Verdict there: `pw ≥ k+1` is coNP-complete, so a short checkable
blockage on every graph would give NP = coNP; Grohe & Marx say this for brambles and
prove brambles exponential on expanders; nothing in print bounds the size of a blockage.
Six papers were read from a scratch directory and not kept. Worth obtaining, with open
links where they exist (nothing downloaded into `literature/`):

- **Grohe, M. & Marx, D.** (2009). On tree width, bramble size, and expansion. *JCTB*,
  99(1), 218–228. DOI 10.1016/j.jctb.2008.06.004. No arXiv version; open preprint at
  `https://www.cs.bme.hu/~dmarx/papers/grohe-marx-brambles.pdf`. The key reference:
  Theorem 8 (polynomial brambles of order Ω(k^{1/2}/log² k); order k^{1/2+ε} forces size
  2^{Ω(k^ε)}) and the introduction's coNP sentence. Read, not kept.
- **Hatzel, M., Komosa, P., Pilipczuk, M. & Sorge, M.** (2022). Constant congestion
  brambles. *DMTCS* 24:1, #6. arXiv 2008.02133 (open). Theorems 1.1–1.2 sharpen
  Grohe–Marx (congestion 2; the exponential bound tight). Read, not kept.
- **Kreutzer, S. & Tazari, S.** (2010). On brambles, grid-like minors, and parameterized
  intractability of MSO. SODA 2010; arXiv 0907.3076 (open). Polynomial-time bramble
  construction at the Grohe–Marx order. Read, not kept.
- **Seymour, P. D. & Thomas, R.** (1993). Graph searching and a min-max theorem for
  tree-width. *JCTB* 58, 22–33. DOI 10.1006/jctb.1993.1027. Not open. Brambles and havens.
- **Chekuri, C. & Chuzhoy, J.** (2016). Polynomial bounds for the grid-minor theorem.
  *J. ACM* 63(5), 40. arXiv 1305.6577 (open).
- **Kawarabayashi, K. & Rossman, B.** (2018). A polynomial excluded-minor approximation
  of treedepth. SODA 2018; *J. Eur. Math. Soc.* 2022. Open at
  `https://www.math.utoronto.ca/rossman/treedepth.pdf`. Conjecture 8.1 (pathwidth) is
  settled by GJNW 2023 Theorem 1.1 (held). Read, not kept.
- **Tamaki, H.** (2022). Heuristic computation of exact treewidth. SEA 2022, LIPIcs 233;
  arXiv 2202.07793 (open). The one solver found that ships a lower-bound certificate (a
  minor of ≤ 49 vertices, verified by running an exact algorithm on it). Read, not kept.
- **Grohe, M. & Schweitzer, P.** (2016). Computing with tangles. *SIDMA* 30(2),
  1213–1247; STOC 2015; arXiv 1503.00190 (open). Tangles "may be exponentially large";
  all algorithms n^{O(k)}. Read, not kept.
- **Elbracht, C., Kneip, J. & Teegen, M.** (2020). Tangles are decided by weighted vertex
  sets. *Advances in Combinatorics* 2020:9; arXiv 1811.06821 (open). (Not
  "Diestel, Elbracht & Jacobs".) Read, not kept.
- **Seibt, A.** (2025). Witnessing and guiding sets of tangles. arXiv 2507.04394 (open).
  Witnessing sets of size ≤ (3^k − 1)/2. Read, not kept.
- **Arnborg, S., Corneil, D. G. & Proskurowski, A.** (1987). Complexity of finding
  embeddings in a k-tree. *SIAM J. Alg. Disc. Meth.* 8(2), 277–284. DOI 10.1137/0608024.
  Not open. The treewidth NP-completeness theorem, cited for pathwidth too.
- **Monien, B. & Sudborough, I. H.** (1988). Min cut is NP-complete for edge weighted
  trees. *TCS* 58, 209–229. DOI 10.1016/0304-3975(88)90028-X (Elsevier open archive).
  Vertex separation NP-complete on planar graphs of maximum degree 3.
- **Kashiwabara, T. & Fujisawa, T.** (1979). Two ISCAS 1979 titles circulate: "An
  NP-complete problem on interval graphs", pp. 82–83, and "NP-completeness of the problem
  of finding a minimum-clique-number interval graph containing a given graph as a
  subgraph", pp. 657–660. IEEE; not open. The pathwidth NP-completeness theorem in
  interval-graph form. (The held 1979 Ohtsuki–Mori–Kuh–Kashiwabara–Fujisawa paper is the
  companion, not this.)
- **Bodlaender, H. L., Bonnet, É., Jaffke, L., Knop, D., Lima, P. T., Milanič, M.,
  Ordyniak, S., Pandey, S. & Suchý, O.** (2023). Treewidth is NP-complete on cubic graphs.
  IPEC 2023; arXiv 2301.10031 (open). States Monien–Sudborough's pathwidth theorem as its
  Theorem 2.4. Read, not kept.
- **Ding, G. & Dziobiak, S.** (2013). On 3-connected graphs of path-width at most three.
  *SIDMA* 27(3), 1514–1526. DOI 10.1137/100800452; open preprint
  `https://www.math.lsu.edu/~ding/pathwidth.pdf`. Repeats the "at least 122 million"
  obstructions for pathwidth 3.
- **Takahashi, A., Ueno, S. & Kajitani, Y.** (1994). Minimal acyclic forbidden minors for
  the family of graphs with bounded path-width. *Discrete Math.* 127, 293–304 (Elsevier
  open archive).
- **Kinnersley, N. G.** (1989). Obstruction set isolation for layout permutation problems.
  PhD thesis, Washington State University. The source of the 122 million count
  (Kinnersley & Langston 1994, p. 199). Not located online.
- **Fomin, F. V. & Thilikos, D. M.** (2008). An annotated bibliography on guaranteed graph
  searching. *TCS* 399(3), 236–245. Open reprint in the GRASTA 2009 booklet,
  `https://kam.mff.cuni.cz/kamserie/clanky/2009/s939.pdf`, pp. 10–13. Monotonicity as the
  NP-membership certificate; brambles as "certificates of escaping strategies", blockages
  their invisible-fugitive analogue. Read, not kept.
- **LaPaugh, A. S.** (1993). Recontamination does not help to search a graph. *J. ACM*
  40(2), 224–245. DOI 10.1145/151261.151263.
- **Bodlaender, H. L.** (1996). A linear-time algorithm for finding tree-decompositions of
  small treewidth. *SIAM J. Comput.* 25(6), 1305–1317. DOI 10.1137/S0097539793251219.
- **Dell, H., Komusiewicz, C., Talmon, N. & Weller, M.** (2017). The PACE 2017
  Parameterized Algorithms and Computational Experiments Challenge: The Second Iteration.
  IPEC 2017, LIPIcs 89, 30. DOI 10.4230/LIPIcs.IPEC.2017.30 (open). Read, not kept.
- **Dell, H., Husfeldt, T., Jansen, B. M. P., Kaski, P., Komusiewicz, C. & Rosamond, F. A.**
  (2016). The First Parameterized Algorithms and Computational Experiments Challenge.
  IPEC 2016, LIPIcs 63, 30. DOI 10.4230/LIPIcs.IPEC.2016.30 (open). Read, not kept.
- **Bodlaender, H. L., Grigoriev, A. & Koster, A. M. C. A.** (2008). Treewidth lower bounds
  with brambles. *Algorithmica* 51(1), 81–98 (the UU-CS-2005-051 report is held).
- **Bodlaender, H. L. & Koster, A. M. C. A.** (2011). Treewidth computations II. Lower
  bounds. *Information and Computation* 209(7), 1103–1119 (the UU-CS-2010-022 report is
  held).
- **Samer, M. & Veith, H.** (2009). Encoding treewidth into SAT. SAT 2009, LNCS 5584,
  45–50. DOI 10.1007/978-3-642-02777-2_6.
- **Grohe, M.** (2016). Tangled up in blue (a survey on connectivity, decompositions, and
  tangles). arXiv 1605.06704 (open). Not read; optional.

## Spectral bounds on vertex separation (2026-11-10)

From the one-measurement test of eigenvalue lower bounds on vertex separation
(`reports/spectral_bound.md`, `learning/spectral_bound.py`). Read online and
cited, nothing downloaded into `literature/`:

- **Helmberg, C., Mohar, B., Poljak, S. & Rendl, F.** (1995). A spectral approach to HELD 2026-11-10: `1995-Helmberg-Mohar-Poljak-Rendl-Spectral-Approach-Bandwidth-Separator-Problems-LMA.pdf`.
  bandwidth and separator problems in graphs. *Linear and Multilinear Algebra* 39(1–2),
  73–90. [doi:10.1080/03081089508818381](https://doi.org/10.1080/03081089508818381).
  Open reprint: [users.fmf.uni-lj.si/mohar/Reprints/1995/BM95_LMA39_Helmberg_BandwidthandSeparatorProblems.pdf](https://users.fmf.uni-lj.si/mohar/Reprints/1995/BM95_LMA39_Helmberg_BandwidthandSeparatorProblems.pdf)
  (also at sfu.ca/~mohar). Theorem 1 (the cut bound `f(m₁, m₂)` in `λ₂, λₙ`),
  Theorem 8 (bandwidth), **Theorem 11, eq. (20)**: a separator `S₃` between `S₁, S₂`
  has `|S₃| ≥ 4 λₙ λ₂ |S₁||S₂| / (n (λₙ − λ₂)²)`; eq. (21) quotes Mohar & Poljak's
  `|S₃| ≥ 4 λ₂ |S₁||S₂| / (Δ n − λ₂ |S₁ ∪ S₂|)` and eq. (22) says when (20) beats it.
  Read in full for the measurement; worth holding (open).
- **Gu, X. & Liu, M.** (2022). A tight lower bound on the matching number of graphs via HELD 2026-11-10: `2022-Gu-Liu-Tight-Lower-Bound-Matching-Number-Laplacian-Eigenvalues-EJC.pdf`.
  Laplacian eigenvalues. *European J. Combin.* 101, 103468.
  [doi:10.1016/j.ejc.2021.103468](https://doi.org/10.1016/j.ejc.2021.103468).
  [Google](https://www.google.com/search?q=Gu+Liu+%22A+tight+lower+bound+on+the+matching+number+of+graphs+via+Laplacian+eigenvalues%22).
  Source of the separator inequality `|S| ≥ 2 λ₂ |X| / (λₙ − λ₂)` (`|X| ≤ |Y|`, no
  `X–Y` edges) that Gima et al. 2025 quote as Lemma 4.1; used here through that
  quotation and checked on every separator triple to 7 vertices. Not held.
- **Chen, Wu & Li** (2027). An improved spectral lower bound for treewidth. *Inform.
  Process. Lett.* 195, 106657. [doi:10.1016/j.ipl.2026.106657](https://doi.org/10.1016/j.ipl.2026.106657).
  [Google](https://www.google.com/search?q=%22An+improved+spectral+lower+bound+for+treewidth%22+Chen+Wu+Li).
  Found through Crossref (title, authors, venue only); the abstract was not
  readable (Elsevier 403) and no arXiv version was found, so no formula is
  recorded here. The latest step after Gima et al. 2025 (held); to obtain before
  any further spectral work.
- **Gima, T., Hanaka, T., Noro, K., Ono, H. & Otachi, Y.** (2024). On a spectral lower
  bound of treewidth. *IEICE Trans. Inf. Syst.* E107-D(3), 328–330.
  [doi:10.1587/transinf.2023FCL0002](https://doi.org/10.1587/transinf.2023FCL0002).
  The intermediate bound (`max{4Δ + 3λ₂, 3Δ + 4.5λ₂}` in the denominator),
  superseded by the held 2025 paper; for the citation only.
- Already listed above under *Pathwidth lower bounds (2026-10-11)* and still
  wanted: Mohar & Poljak (1993) (the original of eq. (21)), Juvan & Mohar (1992),
  Alon & Milman (1985), Chandran & Subramanian (2003).

What the search did not find: any published eigenvalue lower bound stated for
vertex separation or pathwidth itself. Every spectral statement found is on a
single separator (Helmberg et al.; Mohar & Poljak; Gu & Liu), on bandwidth,
cutwidth or linear arrangement (Juvan & Mohar; Helmberg et al. Thm 8), or on
treewidth through one balanced separator (Chandran & Subramanian; Gima et al.;
Chen, Wu & Li). The prefix-separator form in `learning/spectral_bound.py` is
the obvious transfer and we found no prior statement of it; it is not claimed
as new.

## LP bounds for layout problems (2026-11-10)

Precedent for `reports/chain_lp.md` (an LP relaxation of the nested-chain encoding
of vertex separation with Harper's inequalities). Found by web search; none held,
nothing downloaded.

- **Caprara, A. & Salazar-González, J.-J.** (2005). Laying out sparse graphs with
  provably minimum bandwidth. *INFORMS Journal on Computing* 17(3), 356–373.
  DOI 10.1287/ijoc.1040.0083 (`https://pubsonline.informs.org/doi/10.1287/ijoc.1040.0083`;
  Bologna record `https://cris.unibo.it/handle/11585/17058`). A new simple lower bound on
  the bandwidth, an enumerative algorithm with integer-programming relaxations (24 of 30
  literature instances under 200 nodes to proven optimality), and a method to compute the
  density lower bound. The bound is computed through layered graphs with fixed positions
  (per arXiv 1908.07584, which cites it). Not held.
- **Caprara, A., Letchford, A. N. & Salazar-González, J.-J.** (2011). Decorous lower HELD 2026-11-10: `2011-Caprara-Letchford-Salazar-Gonzalez-Decorous-Lower-Bounds-Minimum-Linear-Arrangement-IJOC.pdf`.
  bounds for minimum linear arrangement. *INFORMS Journal on Computing* 23(1), 26–40.
  DOI 10.1287/ijoc.1100.0390. LP-based lower bounds from counting inequalities; improved
  bounds on the MinLA benchmark (gd95c 443, gd96a 77,860). Open submitted version at
  Lancaster eprints `https://eprints.lancs.ac.uk/id/eprint/45449` (PDF via
  `https://core.ac.uk/download/1552183.pdf`). Not held.
- **Mallach, S.** (2018). Linear ordering based MIP formulations for the vertex HELD (since 2026-09-28, `mallach_2018_linear_ordering_mip_vertex_separation_pathwidth.pdf`; see line 58).
  separation or pathwidth problem. *Journal of Discrete Algorithms* 52–53, 156–168.
  DOI 10.1016/j.jda.2018.11.012; conference version IWOCA 2017, LNCS 10765, 327–340,
  DOI 10.1007/978-3-319-78825-8_27. **The direct prior statement**: its abstract says the
  lower bound from the LP relaxations of the existing (position-based) vertex-separation
  MIPs "is zero for any directed graph", and gives a linear-ordering-variable formulation
  whose relaxation is non-zero whenever the pathwidth is. Our chain LP is of the first
  kind and `reports/chain_lp.md` §1 proves the zero (and, with Harper cuts, exactly
  Harper). Whether its linear-ordering relaxation exceeds Harper is not stated in the
  abstract; the paper would settle it. Not held.
- **Coudert, D.** (2016). A note on Integer Linear Programming formulations for linear HELD 2026-11-10: `2016-Coudert-Note-ILP-Formulations-Linear-Ordering-Problems-Graphs-Inria-RR.pdf`.
  ordering problems on graphs. INRIA research report, HAL `hal-01271838`
  (`https://hal.archives-ouvertes.fr/hal-01271838`, open). ILP formulations for pathwidth,
  cutwidth, bandwidth, SumCut and MinLA; results for very sparse graphs on 16–24 vertices
  (as characterised by arXiv 2301.03900). Not held.

## Lower bounds: the search-game and interval members of the complex (2026-11-11)

Behind `reports/complex_lb_search.md` (the survey of lower-bound techniques for
node, edge, mixed, connected and non-deterministic search, interval thickness,
narrowness, vertex separation, proper pathwidth and linear-width, and the cubic /
cage families). Nothing was downloaded into `literature/`; open copies were read
from a scratch directory. Verdict there: everything in print reduces to clique,
degree, branch, minor, Harper or a hand-written blockage, except the subcubic
cutwidth route (`pw ≥ cw − 2` when `Δ ≤ 3`) and Bachtler–Heinrich's girth bound.
Worth obtaining, with open links where they exist:

- **Makedon, F. & Sudborough, I. H.** (1989). On minimizing width in linear layouts.
  *Discrete Applied Mathematics* 23(3), 243–265. DOI 10.1016/0166-218X(89)90016-4
  (Elsevier open archive, browser only; `sciencedirect` returns 403 to scripts).
  Conference version: Minimizing width in linear layouts, ICALP 1983, LNCS 154,
  478–490, DOI 10.1007/BFb0036931. **The load-bearing citation**: edge search number
  = cutwidth on graphs of maximum degree 3 (as cited by Fomin & Thilikos 2008 p. 13
  and by Ellis, Sudborough & Turner 1994 as "[Makedon 1983]"); with Ellis et al.'s
  `es ≤ vs + 2` it gives `pw ≥ cw − 2` on subcubic graphs (§4.1 of the report).
  Already on the 2026-11-05 list above without this role; not held.
- **Bachtler, O. & Heinrich, I.** (2023). Automated testing and interactive
  construction of unavoidable sets for graph classes of small path-width. *Journal
  of Graph Theory* (2023), DOI 10.1002/jgt.22964; arXiv 2010.08373 (open,
  `https://arxiv.org/abs/2010.08373`); author copy at TUprints
  `https://tuprints.ulb.tu-darmstadt.de/24690/1/JGT_JGT22964.pdf`. Theorems 1.1–1.3:
  `ξ(k) ≤ (2/3)k + 10/3`, `ξ(k) ≤ k − 2` for `k ≥ 10`, the table of extremal girths
  and the smallest cubic graphs (K₃,₃, cube and twisted cube, Petersen, Heawood,
  Pappus, McGee, Tutte–Coxeter, G(10)). The only girth-based pathwidth bound in
  print; five of its exact values agree with the dataset (`pwc-16021`, `-15984`,
  `-16027`, `-16010`, `-16065`). Read whole from arXiv; not held.
- **Bachtler, O.** (2023). *On algorithmic certification of graph structures.*
  Dissertation, RPTU Kaiserslautern-Landau; open at KLUEDO
  `https://kluedo.ub.rptu.de/frontdoor/deliver/index/docId/7354/file/Dissertation_Bachtler.pdf`.
  Chapter 8 is the JGT paper with Theorems 8.6 and 8.11 and the computational table
  8.1. Read; not held.
- **Alspach, B., Dyer, D., Hanson, D. & Yang, B.** (2007). Lower bounds on edge
  searching. ESCAPE 2007, LNCS 4614, 516–527. DOI 10.1007/978-3-540-74450-4_46. Not
  open. Abstract: bounds on the edge search number from minimum degree, girth,
  chromatic number and colouring number — degree-type except the girth clause.
- **Yang, B., Dyer, D. & Alspach, B.** (2009). Sweeping graphs with large clique
  number. *Discrete Mathematics* 309(18), 5770–5780. DOI 10.1016/j.disc.2008.05.033
  (Elsevier open archive, browser only); ISAAC 2004, LNCS 3341, 908–920. The clique
  lower bound on the sweep number and the minor monotonicity `s(H) ≤ s(G)` that
  Clarke & Messinger (2019, held) cite as Corollary 6.
- **Dyer, D.** (2004). *Sweeping graphs and digraphs.* PhD thesis, Simon Fraser
  University. The `core.ac.uk/download/56366685.pdf` link returns an HTML stub; the
  SFU Summit record should carry the PDF. Chapter on clique, degree, chromatic and
  girth lower bounds for the sweep number.
- **Ellis, J. A., Sudborough, I. H. & Turner, J. S.** (1994). The vertex separation
  and search number of a graph. *Information and Computation* 113(1), 50–79 (DOI not verified here). **Held as a scanned PDF with no text layer**
  (`ellis_sudborough_turner_1994_vertex_separation_search_number.pdf`: `pdftotext`
  returns nothing). The open technical report WUCS-87-11 is at
  `https://openscholarship.wustl.edu/cse_research/796` (the direct `viewcontent.cgi`
  link returned an HTML stub to a script; browser download). Worth replacing the scan
  with a text-bearing copy or OCR-ing it.
- **Scheffler, P.** (1990). A linear algorithm for the pathwidth of trees. In
  *Topics in Combinatorics and Graph Theory* (R. Bodendiek & R. Henn, eds.),
  Physica-Verlag, 613–620 (DOI not verified here). Not open. The
  three-branch characterisation in node-search / pathwidth form (quoted as Lemma 8 of
  Peng et al. 2000 and Theorem 5 of Coudert, Huc & Sereni 2009, both held).
- **Parsons, T. D.** (1978). Pursuit-evasion in a graph. In *Theory and Applications
  of Graphs*, LNM 642, Springer, 426–441 (DOI not verified here). Not open. Parsons'
  Lemma (quoted on p. 21 of Megiddo et al. 1988, held).
- **Kornai, A. & Tuza, Z.** (1992). Narrowness, pathwidth, and their application in
  natural language processing. *Discrete Applied Mathematics* 36, 87–92 (DOI not verified here). Open preprint at SZTAKI,
  `https://eprints.sztaki.hu/108/1/Kornai_159565_ny.pdf` (read whole). Proposition
  3.1 (`ν = pw + 1`), Theorem 4.1 (trees: contractible to `T_k`; the contraction-minimal
  trees have `(5·3^{k−2} − 1)/2` vertices — the extremal family of `TreeBound.lean`).
  Not held; worth holding for the citation beside Ellis et al.
- **Takahashi, A., Ueno, S. & Kajitani, Y.** (1995). Mixed searching and
  proper-path-width. *Theoretical Computer Science* 137(2), 253–268 (DOI not verified here;
  Elsevier open archive, browser only). `ms = ppw`;
  with Fomin & Thilikos 2006 Lemma 2 (held), `pw ≤ ppw ≤ pw + 1`.
- **Thilikos, D. M.** (2000). Algorithms and obstructions for linear-width and
  related search parameters. *Discrete Applied Mathematics* 105(1–3), 239–271. DOI
  10.1016/S0166-218X(00)00175-X. Open as Utrecht TR CS-1997-35,
  `https://ics-archive.science.uu.nl/research/techreps/repo/CS-1997/1997-35.pdf`
  (read: Theorems 3–4, pp. 22–23, `ms = lw`; the 57 obstructions for `lw ≤ 2`).
- **Fomin, F. V. & Thilikos, D. M.** (2008). An annotated bibliography on
  guaranteed graph searching. *TCS* 399(3), 236–245. Already listed twice above; the
  GRASTA 2009 reprint `https://kam.mff.cuni.cz/kamserie/clanky/2009/s939.pdf` is
  readable with `pdftotext` (pp. 10–13 of the booklet carry the certificate and
  parameter paragraphs quoted in the report).
- **Dendris, N. D., Kirousis, L. M. & Thilikos, D. M.** (1997). Fugitive-search
  games on graphs and related parameters. *TCS* 172(1–2), 233–254. Already listed
  (2026-10-11); its new role: the lazy fugitive of speed 1 is the degeneracy, of
  unbounded speed the treewidth — the game form of the treewidth ceiling on the
  degree family. Not open.
- **Fomin, F. V., Fraigniaud, P. & Nisse, N.** (2009). Nondeterministic graph
  searching: from pathwidth to treewidth. *Algorithmica* 53(3), 358–373. DOI
  10.1007/s00453-007-9041-6. Author copy `https://folk.uib.no/nmiff/articles/2009/2009a.pdf`
  (returned an HTML stub to a script; browser). `tw + 1 ≤ s_q ≤ pw + 1`.
- **Mazoit, F. & Nisse, N.** (2008). Monotonicity of non-deterministic graph
  searching. *TCS* 399(3), 169–178; WG 2007. HAL `hal-00351481` (open).
- **Dereniowski, D., Dyer, D., Tifenbach, R. & Yang, B.** (2015). Zero-visibility
  cops and robber and the pathwidth of a graph. *Journal of Combinatorial
  Optimization* 29 (2015) (DOI not verified here). Open author copy via
  MOST Wiedzy (`https://mostwiedzy.pl/en/publication/zero-visibility-cops-and-robber-and-the-pathwidth-of-a-graph,130501-1`).
  `c_0 ≤ pw`, no lower function of `pw`; a monotone variant within constant factors.
- **Xue, Y., Yang, B. & Zilles, S.** (2022). Lower bounds for the zero-visibility
  cops and robber game (title as indexed: a matching-number lower-bound method).
  *Journal of Combinatorial Optimization* 43(5). DOI 10.1007/s10878-021-00710-8. Not
  open. For the record only: the bound transfers to `pw` but `c_0` is unboundedly
  below it.
- **Habib, M. & Möhring, R. H.** (1994). Treewidth of cocomparability graphs and a
  new order-theoretic parameter. *Order* 11, 47–60 (DOI not verified here). TU Berlin
  TR 336-1992 abstract at
  `https://page.math.tu-berlin.de/~combi/coga-old/publications/techreports/1992/Report-336-1992.html`.
  `pw = tw` on cocomparability graphs — the interval literature's one structural
  theorem, and exactly the regime our gap instances are not in.
- **Monien, B. & Preis, R.** (2006). Upper bounds on the bisection width of 3- and
  4-regular graphs. *Journal of Discrete Algorithms* 4(3), 475–498 (DOI not verified here). `bw ≤ (1/6 + o(1)) n` for cubic graphs: the ceiling of
  the cutwidth route of the report's §4.1 on the 12-cage.
- **Clark, L. H. & Entringer, R. C.** (1988). The bisection width of cubic graphs.
  *Bull. Austral. Math. Soc.* (open at Cambridge Core; volume and pages not verified here); **Jobson, A. S.,
  Kézdy, A. E. & Lehel, J.**, Note on the bisection width of cubic graphs (`bw < n/2`
  for even `n ≥ 16`). Upper bounds on the same quantity; for the record.
- **Warren, R. B.** (2005). *Lower bounds for node search number on grid-like
  graphs.* MSc thesis, University of Victoria. The long form of Ellis & Warren 2008
  (held). Not located online.
- **Yang, B.** (2007). Strong-mixed searching and pathwidth. *Journal of
  Combinatorial Optimization* 13(1), 47–59. DOI 10.1007/s10878-006-9013-9. Not open.
  Strong mixed search number `= pw`; an equality, no bound.
- **Kirousis, L. M. & Papadimitriou, C. H.** (1985). Interval graphs and searching.
  *Discrete Mathematics* 55(2), 181–184. DOI 10.1016/0012-365X(85)90046-9 (Elsevier
  open archive, browser only). The interval-thickness paper of Table 1 row 5; not
  held (the 1986 TCS paper is).
- **Korach, E. & Solel, N.** (1993). Tree-width, path-width, and cutwidth. *DAM*
  43(1), 97–101. Already listed (2026-11-05); its role here is `pw ≤ cw`.
- **Bodlaender, H. L., Bonnet, É., Jaffke, L., Knop, D., Lima, P. T., Milanič, M.,
  Ordyniak, S., Pandey, S. & Suchý, O.** (2025). Treewidth is NP-complete on cubic
  graphs. *Electronic Journal of Combinatorics* 32(3), P3.36 (open,
  `https://www.combinatorics.org/ojs/index.php/eljc/article/view/v32i3p36`); the
  arXiv 2301.10031 version is listed above (2026-11-07). Read for its cutwidth
  citations (Theorem 6, Monien & Sudborough) and Claim 10 (`tw = pw = cw + 3n + 2` on
  the Arnborg–Corneil–Proskurowski gadget).

## Lower bounds: the VLSI members of the complex (2026-11-11)

Literature session behind `reports/complex_lb_vlsi.md` (every lower bound the gate
matrix layout, one-dimensional logic, PLA folding and interval-completion literature
states, classified against our families; verdict there: all covered — column sum,
clique, clique minor, obstruction minors, split, branch — with one object unread,
Yu's "bottleneck hypercycle"). Nothing downloaded into `literature/`; two open full
texts (Hu & Chen 1990; Govindan, Langston & Ramachandramurthi 1997) were read from a
scratch directory and not kept. Worth obtaining, with open links where they exist:

- **Yu, M.-L.** (1986). *Automatic random logic layout synthesis — a module generator
  approach*. PhD thesis, Computer Science, University of Illinois at Urbana-Champaign.
  IDEALS item `https://ideals.illinois.edu/items/69722` (restricted to the Illinois
  community; ProQuest). **The one item that could be of a different kind**: Hu & Chen
  (1990, p. 838) cite pp. 55–57 for "the size of a 'bottleneck hypercycle' is the
  optimal lower bound of track numbers required in a gate matrix layout", NP-complete to
  find, and p. 57 for the proof that `wsn` needs 8 tracks (column sum 4; our dataset
  certifies 8 by refutation). Provisionally a ring-of-cliques minor bound; cannot be
  settled without the text. Interlibrary loan.
- **Hu, Y. H. & Chen, S.-J.** (1990). GM_Plan: a gate matrix layout algorithm based on
  artificial intelligence planning techniques. *IEEE TCAD* 9(8), 836–845.
  DOI 10.1109/43.57791. Open copy (read 2026-11-11, not kept):
  `https://minds.wisconsin.edu/bitstream/handle/1793/9938/file_1.pdf?sequence=1&isAllowed=y`
  (redirects to `minds.wisc.edu`). §2.1 "Lower Bound of the Solution" (p. 837) is the
  column-sum bound with the cycle caveat; Table II (p. 844) the eleven circuits.
- **Hu, T. C. & Kuh, E. S.** (1985). Theory and concepts of circuit layout. In *VLSI
  Circuit Layout: Theory and Design* (Hu & Kuh, eds.), IEEE Press. The source of
  "hypercycle" (p. 55) by Hu & Chen's citation. Not located online.
- **Deo, N., Krishnamoorthy, M. S. & Langston, M. A.** (1987). Exact and approximate
  solutions for the gate matrix layout problem. *IEEE TCAD* 6(1), 79–84.
  [Google](https://www.google.com/search?q=Deo+Krishnamoorthy+Langston+%22Exact+and+approximate+solutions+for+the+gate+matrix+layout+problem%22).
  The subset DP, the two-track test, the no-additive-approximation theorem (Möhring 1990
  Thm 5.1). Abstract only; no bound expected.
- **Das, S. K., Deo, N. & Prasad, S.** (1989). Gate matrix layout revisited: algorithmic
  performance and probabilistic analysis. *FSTTCS 1989*, LNCS 405, 280–290.
  DOI 10.1007/3-540-52048-1_50; abstract at `https://stars.library.ucf.edu/facultybib1980/765`.
  "An expression for the expected number of tracks" under a probabilistic model — the
  period's random-gate-matrix analysis, for Appendix E's related work, not a bound.
- **Prasad, S.** (1986). *Gate matrix layout: expected-case analysis and performance of
  algorithms*. MS thesis, Computer Science, Washington State University, Pullman. The
  source of the expectation above. Not located online.
- **Hwang, D. K., Fuchs, W. K. & Kang, S. M.** (1987). An efficient approach to gate
  matrix layout. *IEEE TCAD* 6(5), 802–809. DOI 10.1109/TCAD.1987.1270323. Dynamic
  net-lists, modified min-net-cut ordering, "an ideal min-net-cut algorithm … is at
  worst a log n approximation". Abstract only. (Presumably the brief's "Hwang, Dutt &
  Ouyang", under which we found nothing.)
- **Huang, S. & Wing, O.** (1989). Improved gate matrix layout. *IEEE TCAD* 8(8),
  875–889. DOI 10.1109/43.31547. Asano's approximate search plus zone-net assignment;
  abstract only. Also **Huang & Wing** (1989), Gate matrix partitioning, *IEEE TCAD* 8,
  756–767, and **Huang & Wing** (1986), Improved gate matrix layout, *ICCAD*, 320–323.
- **Wing, O.** (1982). Automated gate matrix layout. *ISCAS 1982*, 681–685; and
  **Wing, O.** (1983). Interval-graph-based circuit layout. *ICCAD 1983*, 84–85. The
  first papers with the interval-graph augmentation view (Möhring 1990, p. 28). Not
  located online. (Presumably the brief's "Lin & Wing".)
- **Hong, Y.-S., Park, K.-H. & Kim, M.** (1989). A heuristic algorithm for ordering the
  columns in one-dimensional logic arrays. *IEEE TCAD* 8(5), 547–562.
  DOI 10.1109/43.24883. Seeded ordering with a cut estimate, simulated annealing; the
  `Fujii`–`Data VI` circuits of Linhares (2001) Table 3.1. Abstract only.
- **Fujii, T., Horikawa, H., Kikuno, T. & Yoshida, N.** (1987). A heuristic algorithm for
  gate assignment in one-dimensional array approach. *IEEE TCAD* 6(2). dblp
  `journals/tcad/FujiiHKY87`. Heuristic; abstract only.
- **Nakatani, K., Fujii, T., Kikuno, T. & Yoshida, N.** (1986). A heuristic algorithm for
  gate matrix layout. *ICCAD 1986*, 324–327. The source of `x0`. Not located online.
- **Asano, T.** (1982). An optimum gate placement algorithm for MOS one-dimensional
  arrays. *J. Digital Systems* VI(1), 1–27; and **Asano, T. & Tanaka, K.** (1978). A gate
  placement algorithm for one-dimensional arrays. *J. Inform. Proc.* 1(1), 47–52. A
  branch and bound (Hu & Chen 1990: optimal to about fifty gates in a minute); its bound
  not read. Not located online.
- **Leong, H. W.** (1986). A new algorithm for gate matrix layout. *ICCAD 1986*, 316–319;
  **Li, J. T.** (1983). Algorithms for gate matrix layout. *ISCAS 1983*, 1013–1016. Hu &
  Chen's refs [26], [11]; the sources of `v1` and `wli`. Not located online.
- **Fellows, M. R. & Langston, M. A.** (1991). Fast search algorithms for layout
  permutation problems. *Integration, the VLSI Journal* 12(3), 321–337 (dblp; a UTK
  reference list gives *Int'l J. Computer Aided VLSI Design* 3, 325–341 — check before
  citing). Self-reduction; abstract only.
- **Govindan, R., Langston, M. A. & Ramachandramurthi, S.** (1997). Constructive
  algorithms based on graph minors. UTK technical report UT-CS-97-345, open at
  `https://library.eecs.utk.edu/files/ut-cs-97-345.pdf` (read 2026-11-11, not kept).
  The approximate three-track test on the six smallest obstructions. Also
  **Kinnersley & Langston** (1991), UT-CS-91-126, open at
  `https://library.eecs.utk.edu/files/ut-cs-91-126.pdf` (the DAM 1994 version is held).
- **Oliveira, A. C. M. & Lorena, L. A. N.** (2002). A constructive genetic algorithm for
  gate matrix layout problems. *IEEE TCAD* 21(8), 969–974. DOI 10.1109/TCAD.2002.800454.
  Table I: the column-sum `LB` beside the best known tracks of the eleven circuits.
  Open copy at `http://www.lac.inpe.br/~lorena/alexandre/CGA_GMLP_2266.pdf` (host
  unreliable). **Chen, S.-J. & Hu, Y. H.** (1990), GM_Learn: an iterative learning
  algorithm for CMOS gate matrix layout (venue not verified; cited by Linhares 2001 and
  Oliveira & Lorena 2002), the same `LB`.
- **Su, C. C. & Sarrafzadeh, M.** (1990). Optimal gate-matrix layout of CMOS functional
  cells. *Integration* 9(1), 3–23. DOI 10.1016/0167-9260(90)90003-j. No abstract online;
  functional-cell chaining, probably no track bound.
- **Hu, T. C. & Kuo, Y. S.** (1987). Graph folding and programmable logic array.
  *Networks* 17(1), 19–37. DOI 10.1002/net.3230170103. Upper and lower bounds on the
  size of a *simple* folding in edges and vertices; Möhring's Prop. 3.16 (`Z_{m,m}`).
  Not a pathwidth bound. Abstract only.
- **Hachtel, G. D., Newton, A. R. & Sangiovanni-Vincentelli, A. L.** (1982). An algorithm
  for optimal PLA folding. *IEEE TCAD* 1(2), 63–77; **De Micheli, G. &
  Sangiovanni-Vincentelli, A. L.** (1983). Multiple constrained folding of programmable
  logic arrays: theory and applications. *IEEE TCAD* 2(3), 151–167,
  DOI 10.1109/TCAD.1983.1270033 (correction 10.1109/TCAD.1984.1270083); PLEASURE's
  Berkeley report `https://www2.eecs.berkeley.edu/Pubs/TechRpts/1982/9615.html`;
  **Lewandowski, J. L. & Liu, C. L.** (1984). A branch and bound algorithm for optimal
  PLA folding. *DAC 1984*, 425–433; **Luby, M., Vazirani, U., Vazirani, V. &
  Sangiovanni-Vincentelli, A.** (1982). Some theoretical results on the optimal PLA
  folding problem. *ICCC 1982*, 165–170; **Ravi, S. S. & Lloyd, E. L.** (1988). The
  complexity of near-optimal programmable logic array folding. *SIAM J. Comput.* 17(4),
  696–710, DOI 10.1137/0217045. All on simple folding (not `pw + 1`); abstracts only;
  for completeness of the PLA row.
- **Ohtsuki, T., Mori, H., Kashiwabara, T. & Fujisawa, T.** (1981). On minimal
  augmentation of a graph to obtain an interval graph. *J. Comput. System Sci.* 22(1),
  60–97. DOI 10.1016/0022-0000(81)90022-2. The `O(nm')` minimal-completion algorithm;
  no bound. (Kashiwabara & Fujisawa 1979 is listed above under *Pathwidth lower bounds
  and NP ∩ coNP*.)
- **Li, F.** (1989). A heuristic algorithm for one-dimensional logic gate layout (in
  Chinese). *Acta Electronica Sinica* (电子学报), record
  `https://www.ejournal.org.cn/en/article/34270512/`; and **Wu & Chan** (1987). A
  graph-theoretic approach for one-dimensional logic gate assignment of VLSI circuit
  layout. *IEEJ Trans.* (title only). The two non-English items the search surfaced;
  heuristics, no bound seen.

What the search did not find: any lower bound in this literature other than the column
sum, the clique and clique-minor statements, obstruction minors, Möhring's split and
branch lemmas, and Yu's unread hypercycle; no "dominating net" bound; no LP or
Lagrangean bound on tracks (the TU Berlin Lagrangean of Möhring 1990 p. 48 is for
constrained block folding and we found no publication of it); nothing in Japanese; two
Chinese heuristics. Full search list in `reports/complex_lb_vlsi.md` §5.

## Lower bounds: the linear-layout neighbours of the complex (2026-11-11)

Survey behind `reports/complex_lb_layout.md`: the lower-bound literature of cutwidth,
bandwidth and proper pathwidth, split bandwidth, MinLA and profile, treewidth,
tree-depth, linear-width and directed pathwidth, read for what transfers to pathwidth.
Verdict there: nothing transfers that is not already a treewidth or Harper argument;
the one genuinely different relaxation (an edge-lattice Harper bound through
linear-width) is measured dead to 8 vertices. Read from open copies in a scratch
directory; nothing downloaded into `literature/`. Papers already listed under other
headings (Juvan & Mohar 1992, Mohar & Poljak 1993, Caprara & Salazar-González 2005,
Clautiaux et al. 2003/2004, Korach & Solel 1993, Chung & Seymour 1989, Makedon &
Sudborough 1989, Dell et al. 2017, Lin & Lin 2025, Bodlaender & Koster 2011) are not
repeated.

**Cutwidth**

- **Bermond, J.-C., Cosnard, M., Coudert, D. & Havet, F.** (2025). New lower bounds on
  the cutwidth of graphs. *Computers & Operations Research* 182, 107130.
  [doi:10.1016/j.cor.2025.107130](https://doi.org/10.1016/j.cor.2025.107130). Open at
  HAL: [hal-05083322](https://hal.science/hal-05083322/document) (read whole). §2 surveys
  the edge-cut, `λ₂`, `Δ/2` and degeneracy bounds; §3 minimum-, average- and
  maximum-average-degree bounds by a sum-of-cuts ("grooming") argument; §4 the bound
  `C*(m, n)` from the maximum path-grooming count, `O(log n)`, dominating the average-degree
  bound; §4.2 corrects the greedy claim of Martí et al. 2013 above `C = 9`.
- **Gaar, E., Puges, D. & Wiegele, A.** (2024). Strong SDP based bounds on the cutwidth of
  a graph. *Computers & Operations Research*, 106449.
  [doi:10.1016/j.cor.2023.106449](https://doi.org/10.1016/j.cor.2023.106449);
  [arXiv:2301.03900](https://arxiv.org/abs/2301.03900) (read). The lifted linear-ordering
  SDP with 3-dicycle, triangle and LOP-lifted cuts; `n ≤ 50`; 20–63 % gaps on 16–24-vertex
  sparse graphs where Coudert's MILP solves them in seconds.
- **Kloeckner, B.** (2010). Cutwidth and degeneracy of graphs.
  [arXiv:0907.5138](https://arxiv.org/abs/0907.5138) (read). Thm 2.1 (uniform sparsity),
  Cor. 2.2 `cw ≥ δ*²/4 + δ*/2`.
- **Martí, R., Pantrigo, J. J., Duarte, A. & Pardo, E. G.** (2013). Branch and bound for
  the cutwidth minimization problem. *Computers & Operations Research* 40(1), 137–149.
  Author preprint open at
  [uv.es](https://www.uv.es/~rmarti/paper/docs/other15.pdf) (read). §2.1 the four prior
  bounds (Gomory–Hu, `λ₂`, MinLA/n, edge bisection); §3 LB1–LB4; §4 the same-set dominance
  rule.
  [Google](https://www.google.com/search?q=Mart%C3%AD+Pantrigo+Duarte+Pardo+%22Branch+and+bound+for+the+cutwidth+minimization+problem%22).
- **Bodlaender, H. L.** (1986). Classes of graphs with bounded tree-width. Technical
  Report RUU-CS-86-22, Utrecht. The source Gaar et al. cite for `cw ≥ tw`.
  [Google](https://www.google.com/search?q=Bodlaender+%22Classes+of+graphs+with+bounded+tree-width%22+RUU-CS-86-22).

**Bandwidth and proper pathwidth**

- **Chvátal, V.** (1970). A remark on a problem of Harary. *Czechoslovak Mathematical
  Journal* 20(1), 109–111. The density bound `bw ≥ max_S (|S| − 1)/diam(S)` (as attributed
  by Benadé & Hooker 2019 §7). The journal is digitised at dml.cz; the article's handle was
  not verified.
  [Google](https://www.google.com/search?q=Chv%C3%A1tal+1970+%22A+remark+on+a+problem+of+Harary%22).
- **Chinn, P. Z., Chvátalová, J., Dewdney, A. K. & Gibbs, N. E.** (1982). The bandwidth
  problem for graphs and matrices — a survey. *Journal of Graph Theory* 6(3), 223–254.
  [doi:10.1002/jgt.3190060302](https://doi.org/10.1002/jgt.3190060302). Not open.
- **Blum, A., Konjevod, G., Ravi, R. & Vempala, S.** (2000). Semi-definite relaxations
  for minimum bandwidth and other vertex-ordering problems. *Theoretical Computer
  Science* 235(1), 25–42.
  [doi:10.1016/S0304-3975(99)00181-3](https://doi.org/10.1016/S0304-3975(99)00181-3).
  The half-density ball bound `α(G)` and the first bandwidth SDP.
- **Benadé, J. G. & Hooker, J. N.** (2019). Optimization bounds from the branching dual.
  [arXiv:1908.07584](https://arxiv.org/abs/1908.07584) (read for §7–§8: the Chvátal, Blum
  et al. and Caprara–Salazar-González bounds restated as eqs (4)–(6), and the latter's
  bilevel IP (29) with fixed vertices).
- **Rendl, F., Sotirov, R. & Truden, C.** (2021). Lower bounds for the bandwidth problem.
  *Computers & Operations Research*, 105422.
  [doi:10.1016/j.cor.2021.105422](https://doi.org/10.1016/j.cor.2021.105422);
  [arXiv:1904.06715](https://arxiv.org/abs/1904.06715) (read §1–§3). The `k`-partition SDP
  (Juvan–Mohar at `k = 3`, the QAP form at `k = n`), matrices of order `n·k`, graphs to
  128 vertices; §1 states the 3-partition principle that is Harper's argument for `bw`.
- **Haemers, W. H.** (1995). Interlacing eigenvalues and graphs. *Linear Algebra and its
  Applications* 226–228, 593–616. `bw > nλ₂/λₙ` by interlacing (cited by RST 2021 and van
  Dam & Sotirov 2015).
  [Google](https://www.google.com/search?q=Haemers+1995+%22Interlacing+eigenvalues+and+graphs%22).
- **Povh, J. & Rendl, F.** (2007). A copositive programming approach to graph partitioning.
  *SIAM Journal on Optimization* 18(1), 223–241. The min-cut SDP whose value is the
  eigenvalue bound; tightened by nonnegativity.
  [Google](https://www.google.com/search?q=Povh+Rendl+%22A+copositive+programming+approach+to+graph+partitioning%22).
- **de Klerk, E., Nagy, M. & Sotirov, R.** (2013). On semidefinite programming bounds for
  graph bandwidth. *Optimization Methods and Software* 28(3), 485–500. Two QAP-SDP bounds
  dominating Blum et al.
  [Google](https://www.google.com/search?q=de+Klerk+Nagy+Sotirov+%22On+semidefinite+programming+bounds+for+graph+bandwidth%22).
- **Del Corso, G. M. & Manzini, G.** (1999). Finding exact solutions to the bandwidth
  minimization problem. *Computing* 62, 189–203.
  [doi:10.1007/s006070050002](https://doi.org/10.1007/s006070050002). The upper partial
  ordering branch and bound.
- **Martí, R., Campos, V. & Piñana, E.** (2008). A branch and bound algorithm for the
  matrix bandwidth minimization. *European Journal of Operational Research* 186(2),
  513–528. `LB2(g)`, `LB3(g)` for partial orderings. Author preprint open at
  [uv.es](https://www.uv.es/~rmarti/paper/docs/bmp3.pdf) (not read).
- **Lim, A., Rodrigues, B. & Xiao, F.** (2007). A fast bandwidth minimization algorithm.
  *International Journal of Artificial Intelligence Tools* 16(3). The level-structure
  band `|L| ≤ bw ≤ 2|L| − 1` for level layouts. Open at
  [SMU ink](https://ink.library.smu.edu.sg/lkcsb_research/609) (not read).
- **Cygan, M. & Pilipczuk, M.** (2010). Exact and approximate bandwidth. *Theoretical
  Computer Science* 411(40–42), 3701–3713.
  [doi:10.1016/j.tcs.2010.06.018](https://doi.org/10.1016/j.tcs.2010.06.018). `O(4.473ⁿ)`;
  no lower bound of its own.
- **Kaplan, H. & Shamir, R.** (1996). Pathwidth, bandwidth, and completion problems to
  proper interval graphs with small cliques. *SIAM Journal on Computing* 25(3), 540–561.
  [doi:10.1137/S0097539793258143](https://doi.org/10.1137/S0097539793258143). Proper
  pathwidth equals bandwidth.

**MinLA and profile**

- **Petit, J.** (2003). Experiments on the minimum linear arrangement problem. *ACM
  Journal of Experimental Algorithmics* 8, 2.3.
  [doi:10.1145/996546.996554](https://doi.org/10.1145/996546.996554). Preprint open at
  [aminer](https://static.aminer.org/pdf/PDF/000/979/944/experiments_on_the_minimum_linear_arrangement_problem.pdf)
  (read §2, §7): the Path, Edges, Degree, Gomory–Hu, Juvan–Mohar and Mesh methods.
- **Adolphson, D. L. & Hu, T. C.** (1973). Optimal linear ordering. *SIAM Journal on
  Applied Mathematics* 25(3), 403–423. [doi:10.1137/0125042](https://doi.org/10.1137/0125042).
  The Gomory–Hu tree bound for MinLA.
- **Lin, Y. & Yuan, J.** (1994). Profile minimization problem for matrices and graphs.
  *Acta Mathematicae Applicatae Sinica* 10(1), 107–112.
  [doi:10.1007/BF02006264](https://doi.org/10.1007/BF02006264). Profile lower bounds.

**Treewidth, tree-depth, linear-width, directed pathwidth**

- **Bodlaender, H. L. & Koster, A. M. C. A.** (2006). Safe separators for treewidth.
  *Discrete Applied Mathematics* 154(6), 806–812. The block / clique-separator
  decomposition that pathwidth lacks.
  [Google](https://www.google.com/search?q=Bodlaender+Koster+%22Safe+separators+for+treewidth%22).
- **Brokkelkamp, R., van Venetië, R., de Vries, M. & Westerdiep, J.** (2020). PACE solver
  description: tdULL. IPEC 2020, LIPIcs 180. Open at
  [CWI](https://ir.cwi.nl/pub/30347/30347.pdf) (read §2.1.1: core subgraph and
  least-common-neighbour contraction as lower bounds).
- **Korhonen, T.** (2020). SMS in PACE 2020. IPEC 2020, LIPIcs 180, 30.
  [doi:10.4230/LIPIcs.IPEC.2020.30](https://doi.org/10.4230/LIPIcs.IPEC.2020.30);
  [arXiv:2006.07302](https://arxiv.org/abs/2006.07302) (read §3.3: MMD+, long paths, and
  the isomorphism hashtable that shares lower bounds across isomorphic induced subgraphs).
- **Trimble, J.** (2020). An algorithm for the exact treedepth problem (Bute / Bute-Plus).
  SEA 2020, LIPIcs 160; [arXiv:2006.09912](https://arxiv.org/abs/2006.09912) (read §2–§3).
- **Takahashi, A., Ueno, S. & Kajitani, Y.** (1995). Mixed searching and proper-path-width.
  *Theoretical Computer Science* 137(2), 253–268. Mixed search number = 3-proper pathwidth.
  [Google](https://www.google.com/search?q=Takahashi+Ueno+Kajitani+%22Mixed+searching+and+proper-path-width%22).
- **Thomas, R.** (1996). Tree-decompositions of graphs. Lecture notes, Georgia Institute
  of Technology (unpublished). The definition of linear-width.
  [Google](https://www.google.com/search?q=Robin+Thomas+%22Tree-decompositions+of+graphs%22+lecture+notes+linear-width).
- **Yang, B. & Cao, Y.** (2008). Digraph searching, directed vertex separation and
  directed pathwidth. *Discrete Applied Mathematics* 156(10), 1822–1837. The directed
  equivalence only; no bound.
  [Google](https://www.google.com/search?q=Yang+Cao+2008+%22directed+vertex+separation+and+directed+pathwidth%22).

What the search did not find: any lower bound stated for linear-width, mixed search,
split bandwidth or directed pathwidth beyond the parameters' definitions; any
treewidth lower bound built on a matching as such (LBP's disjoint paths are the nearest);
a PACE lower-bound track before 2026 (maximum agreement forest). Every cutwidth and
bandwidth bound found is either one separator of the layout (Harper's family), a degree
or edge-count statement (under `tw`), or an LP/SDP in layout variables (under the
Lagrangian ceiling of `reports/chain_lp.md` §5).

## Random graphs: the middle regime (2026-11-11)

Survey behind `reports/random_graph_middle.md` §3: what is in print on the pathwidth,
vertex separation, treewidth or bandwidth of `G(n, p)` when `np → ∞` and `p → 0`. Read
from open copies (arXiv, ar5iv, publisher abstracts) by a search agent; nothing downloaded.
Verdict there: no published statement gives `n − pw` (or `n − tw`) the order `n ln c / c`
or a constant in that regime; the published forms are `n − O(√(n/p))` (Perarnau & Serra,
tw), `n − o(n)` (Wang et al., tw; abstract only) and `(1 − o(1)) n` (Cheung & Girardet,
vertex separation, `p ≥ n^{−1+ε}`). Papers already held under other headings (Lee, Lee &
Oum 2012; Perarnau & Serra 2014; Gao 2006/2012; Do, Erde & Kang 2024; Edwards & McDermid
2015; Díaz, Petit, Serna & Trevisan 2001) are not repeated.

- **Wang, L., Liu, Y., Cui, S. & Xu, D.** (2011). A note on treewidth in random graphs.
  *COCOA 2011*, LNCS 6831, 491–499.
  [doi:10.1007/978-3-642-22616-8_38](https://doi.org/10.1007/978-3-642-22616-8_38).
  Abstract only (paywalled, no open copy found): for `p = c/n`, `tw ≤ tn` with `t < 1`
  w.h.p.; for `p ≫ 1/n`, `tw ≥ n − o(n)`. The theorem's rate is not visible from the
  abstract. **Wanted**: the statement and proof of the `n − o(n)` bound.
- **Cheung, K. K. H. & Girardet, P.** (2017). Improved approximation of layout problems on
  random graphs. [arXiv:1710.10339](https://arxiv.org/abs/1710.10339) (read); the
  journal version is *Open J. Discrete Math.* 10(1), 13–30 (2020),
  [doi:10.4236/ojdm.2020.101003](https://doi.org/10.4236/ojdm.2020.101003), the entry
  `CheungGirardet2020` of `refs.bib`, which the agent could not reach. Lemma 7: for `p_n = Ω(n^{−c})`, `c < 1`, w.h.p. `MINVS ≥ (1 − δ)n − 1`; Theorem
  4.5 the approximation ratio for vertex separation. No rate.
- **Turner, J. S.** (1986). On the probable performance of heuristics for bandwidth
  minimization. *SIAM J. Comput.* 15(2), 561–580.
  [doi:10.1137/0215041](https://doi.org/10.1137/0215041). Held
  (`reports/scratch/first_moment/lit/turner1986.pdf`); listed here for Theorem 2.2,
  `bw ≥ (1 − ε) n` for `p ≥ c log n / n` — a bandwidth statement, which bounds nothing
  about pathwidth (`pw ≤ bw`).
- **Frieze, A. M.** (1990). On the independence number of random graphs. *Discrete
  Mathematics* 81(2), 171–175.
  [doi:10.1016/0012-365X(90)90149-C](https://doi.org/10.1016/0012-365X(90)90149-C). Not
  accessed; its statement `α(G(n, p)) = (2n/d)(ln d − ln ln d − ln 2 + 1 ± ε)` w.h.p. for
  `d = np ≥ d_ε`, `d = o(n)`, is quoted from Coja-Oghlan & Efthymiou
  ([arXiv:1007.1378](https://arxiv.org/abs/1007.1378), eq. (23)) and Bohman & van der
  Hofstad ([arXiv:2208.00117](https://arxiv.org/abs/2208.00117)). It is the upper side
  `n − pw ≥ α = (2 + o(1)) n ln c / c` of the middle-regime sandwich. **Wanted**: the
  original, for the exact range of `d`.
- **Bollobás, B. & Erdős, P.** (1976). Cliques in random graphs. *Math. Proc. Cambridge
  Philos. Soc.* 80(3), 419–427.
  [doi:10.1017/S0305004100053056](https://doi.org/10.1017/S0305004100053056); **Matula,
  D. W.** (1976). The largest clique size in a random graph. Tech. Rep. CS 7608, Southern
  Methodist University; **Grimmett, G. R. & McDiarmid, C. J. H.** (1975). On colouring
  random graphs. *Math. Proc. Cambridge Philos. Soc.* 77(2), 313–324.
  [doi:10.1017/S0305004100051124](https://doi.org/10.1017/S0305004100051124). The
  two-point concentration of `α(G(n, p))` at `(2 + o(1)) log_b n` for constant `p`, the
  upper side of the dense sandwich; not held.
- **Shang, Y.** (2022). On the tree-depth and tree-width in heterogeneous random graphs.
  *Proc. Japan Acad. Ser. A* 98(9), 78–83.
  [doi:10.3792/pjaa.98.015](https://doi.org/10.3792/pjaa.98.015). Held
  (`literature/2022-Shang-...pdf`); linear tree-depth and treewidth under density
  assumptions in `G(n, (p_ij))`, citing Perarnau & Serra for `np → ∞`; nothing sharper.
- **Mareček, J.** (2009). Some probabilistic results on width measures of graphs.
  [arXiv:0908.1772](https://arxiv.org/abs/0908.1772). `Ω(n)` lower bounds on treewidth,
  branchwidth, clique-width and rank-width at `G(n, 1/2)`; no constants.

## Second moment on layouts (2026-11-11)

Survey behind `reports/layout_second_moment.md` §5: second-moment (Paley–Zygmund)
arguments for layout and ordering parameters of random graphs, the template second
moments on random CSPs, the width of a random ordering, and pathwidth upper bounds on
`G(n, c/n)` other than Edwards & McDermid (2015). Read from abstract and landing pages by a
search agent (25 searches); nothing downloaded; one held PDF read in full (Díaz, Petit,
Serna & Trevisan 2001, `literature/2001-Diaz-Petit-Serna-Trevisan-...pdf`: Lemma 3 is the
`(1/2 − ε) n` vertex-separation floor for *every* layout of a mixing graph, a Chernoff
form of the empty-pair argument; no second moment, no variance, nothing on a random
ordering). **We found no statement** of a second moment on the number of layouts or path
decompositions of bounded width in any random graph model; of the expected vertex
separation, cutwidth or open-stack count of a uniformly random ordering of `G(n, p)`; of
the open-count chain ("the placed vertex is open with probability `k/(n − t + 1)`"); of a
cutwidth, vertex-separation or pathwidth result on random regular graphs (bisection and
treewidth only); or of a pathwidth upper bound on `G(n, c/n)` other than Edwards & McDermid.
The template papers each document the failure measured in the report (the plain second
moment exponentially above `E[X]²`) and cure it one of three ways: balanced objects,
weights that cancel the drift the conditioning induces, or a complement symmetry.
Used in the report (template and verdict), none held:

- **Achlioptas, D. & Naor, A.** (2005). The two possible values of the chromatic number
  of a random graph. *Annals of Mathematics* 162(3), 1335–1351.
  [doi:10.4007/annals.2005.162.1335](https://doi.org/10.4007/annals.2005.162.1335),
  [arXiv:0706.1725](https://arxiv.org/abs/0706.1725). Second moment of the number of
  *balanced* `k`-colourings; the pair probability depends on the `k × k` overlap matrix
  only and the sum is maximised at the flat overlap. The closest template: a count of
  combinatorial objects with an overlap-parameterised pair probability. **Wanted.**
- **Achlioptas, D. & Peres, Y.** (2004). The threshold for random `k`-SAT is
  `2^k ln 2 − O(k)`. *J. Amer. Math. Soc.* 17(4), 947–973.
  [doi:10.1090/S0894-0347-04-00464-3](https://doi.org/10.1090/S0894-0347-04-00464-3),
  [arXiv:cs/0305009](https://arxiv.org/abs/cs/0305009). §2.1 "the vanilla second moment
  method fails"; the cure is a *weighted* count, each satisfying assignment weighted by a
  product over clauses so that the weighted measure has no drift toward the majority
  assignment. The canonical lottery fix. **Wanted** for §2–3.
- **Dani, V. & Moore, C.** (2011). Independent sets in random graphs from the weighted
  second moment method. *RANDOM 2011*, LNCS 6845;
  [arXiv:1011.0180](https://arxiv.org/abs/1011.0180). "A weighted version of the second
  moment method, where we give each independent set a weight based on the total degree of
  its vertices": the plain count's second moment is exponentially larger than the squared
  expectation because a planted set makes the graph locally sparser — the exact effect
  the report measures on layouts (the planted graph is atypically sparse). The most direct
  analogue. **Wanted.**
- **Achlioptas, D. & Moore, C.** (2006). Random `k`-SAT: two moments suffice to cross a
  sharp threshold. *SIAM J. Comput.* 36(3), 740–762;
  [arXiv:cond-mat/0310227](https://arxiv.org/abs/cond-mat/0310227). The plain second
  moment works on NAE-`k`-SAT because the complement symmetry kills the drift; layouts have
  no such symmetry (reversal preserves width but not the edge count's drift).
- **Achlioptas, D. & Moore, C.** (2004). The chromatic number of random regular graphs.
  *RANDOM 2004*, LNCS 3122; [arXiv:cond-mat/0407278](https://arxiv.org/abs/cond-mat/0407278);
  **Kemkes, G., Pérez-Giménez, X. & Wormald, N.** (2010). On the chromatic number of
  random `d`-regular graphs. *Adv. Math.* 223; [arXiv:0812.2937](https://arxiv.org/abs/0812.2937).
  Balanced second moment plus small subgraph conditioning — the tool when the ratio tends
  to a constant above 1, which is not the case here (it is exponential).
- **Coja-Oghlan, A. & Efthymiou, C.** (2015). On independent sets in random graphs.
  *Random Structures & Algorithms*; [arXiv:1007.1378](https://arxiv.org/abs/1007.1378).
  States why the second moment fails for the independence number and how Frieze (1990)
  bridged the gap with Azuma / Talagrand: the bootstrapping route when the ratio is
  sub-exponential, which it is not for layouts.
- **Coja-Oghlan, A. & Zdeborová, L.** (2012). The condensation transition in random
  hypergraph 2-coloring. *SODA 2012*; [arXiv:1107.2341](https://arxiv.org/abs/1107.2341);
  **Coja-Oghlan, A. & Vilenchik, D.** (2013). Chasing the `k`-colorability threshold.
  *FOCS 2013*; [arXiv:1304.1063](https://arxiv.org/abs/1304.1063); **Bapst, V.,
  Coja-Oghlan, A., Hetterich, S., Raßmann, F. & Vilenchik, D.** (2016). The condensation
  phase transition in random graph coloring. *Comm. Math. Phys.* 341;
  [arXiv:1404.5513](https://arxiv.org/abs/1404.5513). When the lottery effect is a
  condensation transition that no weighting removes.
- **Coja-Oghlan, A. & Panagiotou, K.** (2012, 2013). Catching the `k`-NAESAT threshold,
  *STOC 2012*, [arXiv:1111.1274](https://arxiv.org/abs/1111.1274); Going after the `k`-SAT
  threshold, *STOC 2013*, [arXiv:1212.1682](https://arxiv.org/abs/1212.1682). Counting
  clusters (covers) instead of solutions: the analogue would count one representative per
  class of narrow layouts under local swaps.
- **Gerencsér, B. & Harangi, V.** (2025). Boosted second moment method in random regular
  graphs. [arXiv:2510.12600](https://arxiv.org/abs/2510.12600). The second moment's witness
  has a spatial Markov property and is improved by local modifications.
- **Bollobás, B.** (1988). The chromatic number of random graphs. *Combinatorica* 8(1),
  49–55. [doi:10.1007/BF02122551](https://doi.org/10.1007/BF02122551). The dense-regime
  template is a martingale, not a second moment on colourings.
- **Bohman, T. & van der Hofstad, R.** (2024). Two-point concentration of the independence
  number of the random graph. *Forum Math. Sigma* 12, e20 (open access). Second moment
  plus a large-deviation inequality, the modern form of Frieze's route.
- Linear extensions of finite posets, survey, [arXiv:2311.02743](https://arxiv.org/abs/2311.02743):
  the one second-moment inequality on a *count of orderings* we found (for posets, ratio
  between 1 and 2), not for graphs.
- Random regular treewidth, [arXiv:2410.20333](https://arxiv.org/abs/2410.20333), Cor. 4.34:
  `tw ≥ (1 − 6/√d) n − 1` a.a.s. for even `d` (expander mixing); Thm 4.37 an upper bound
  for `d ≥ 146`. For the dense-degree constant only.
- Unverified bandwidth leads: a 1986 *SIAM J. Comput.* bandwidth paper hosted at
  `arl.wustl.edu/~jon.turner/pubs/1986/siamjc86.pdf` (presumably Turner 1986, already
  held under the previous heading) and Erdős et al. (1989), *Annals of Discrete Math.* 41,
  117–130, which cites a McDiarmid result on the bandwidth of random graphs; the
  "bandwidth theorem in random graphs" literature (Huang–Lee–Sudakov 2012;
  Allen–Böttcher–Ehrenmüller–Schnitzer–Taraz 2022) is about embeddings, not the bandwidth
  of `G(n, p)`.
- A title "Typical Pathwidth of Random Graphs" cited by an AI-generated blog returns no
  arXiv result; treat as non-existent.

## Dense random graphs: the staircase constant (2026-11-11)

Survey behind `reports/dense_staircase.md` §5, by a search agent (about 30 searches, 20
landing pages; nothing downloaded; one open scan read through its text layer). The
question was whether `n − parameter = c · log_b n` with an exact constant is in print for
any layout parameter of `G(n, p)` at fixed `p`, and whether `2 + √2` appears anywhere.

**It does, for bandwidth, since 1985.** Erdős, Hell & Winkler (1989) state as their
Theorem 3, "proved in [13]" = Kuang & McDiarmid (1985): with probability `→ 1`, for
`G(n, ½)`, `n − (2 + √2 + o(1)) lg n < bw < n − (2 + √2 − o(1)) lg n`, and add that
"even the constant `c` is determined by the result of Kuang and McDiarmid", that before
finding [13] they "had the constant `2 + √2` in the lower bound, but not in the upper
bound", that Theorem 3 is stronger than Turner (1983/86) and de la Vega (1983) and weaker
than "the most general version of [13]" (general `p`, "easily generalized"). Read verbatim
from the text layer of the Rényi Institute scan (`static.renyi.hu/~p_erdos/1989-05.pdf`).
The strict staircase of `reports/dense_staircase.md` §1 (first `s − 1` and last `s − 1`
positions) is exactly the structure of `bw ≤ n − s` when `2s − 2 ≤ n`
(`learning.staircase_moment.check_bandwidth_lemma`), so Kuang & McDiarmid's upper bound
with `pw ≤ bw` gives the second-moment half of the pathwidth statement for free; their
lower bound says nothing about pathwidth (a bandwidth lower bound never does), and that
half — the generalised staircase with coincidences, and the corner block — is where
`reports/dense_staircase.md` §2 goes beyond the record. **We found no prior statement for
pathwidth, vertex separation, treewidth or any other member of the complex.** Füredi &
West (2001) name the structure the *halfgraph* in a Ramsey/Turán context and quote the
Kuang–McDiarmid value.

- **Kuang, Y. & McDiarmid, C.** (1985). On the bandwidth of a random graph. *Ars
  Combinatoria* 20A, 29–36. zbMATH 0606.05055; no DOI, not online (the BCC 1985
  proceedings volume; EHW cite it as "Probabilistic analysis of bandwidth problems, Proc.
  British Combinatorial Conference 1985, to appear" — the same paper, inferred). The
  primary source of `2 + √2`. **Wanted, highest priority** (library scan, or the author).
- **Erdős, P., Hell, P. & Winkler, P.** (1989). Bandwidth versus bandsize. *Annals of
  Discrete Mathematics* 41, 117–129. zbMATH 0684.05043. Open scan with text layer:
  [static.renyi.hu/~p_erdos/1989-05.pdf](https://static.renyi.hu/~p_erdos/1989-05.pdf).
  Theorem 3 as above; Theorem 4 on bandsize. **Wanted** (the scan is citable; not placed
  in `literature/`).
- **Füredi, Z. & West, D. B.** (2001). Ramsey theory and bandwidth of graphs. *Graphs and
  Combinatorics* 17(3), 463–471. [doi:10.1007/PL00013410](https://doi.org/10.1007/PL00013410).
  `bw(G) + bw(Ḡ) ≤ 2n − 4 log₂ n + o(log n)` always, against the almost-sure value from
  Kuang–McDiarmid; the halfgraph. Paywalled; abstract only.
- **Fernández de la Vega, W.** (1983). On the bandwidth of random graphs. *Annals of
  Discrete Mathematics* 17, 633–638.
  [doi:10.1016/S0304-0208(08)73443-1](https://doi.org/10.1016/S0304-0208(08)73443-1).
  Weaker than Theorem 3 per EHW; unread.
- **Turner, J. S.** (1986). *SIAM J. Comput.* 15(2), 561–580,
  [doi:10.1137/0215041](https://doi.org/10.1137/0215041) — held
  (`reports/scratch/first_moment/lit/turner1986.pdf`); constant 4, the empty pair.
- **Perarnau, G. & Serra, O.** (2014) (held) and **Lee, Lee & Oum** (2012) (held): the
  only dense-regime width results found — `td, tw = n − O(√(n/p))` and
  `rw = ⌈n/3⌉ − O(1)`; nothing of the form `n − c log n` for pathwidth or treewidth.
  Wang, Liu, Cui & Xu (2011, COCOA) give only `tw ≥ n − o(n)` (indexed abstract).
- **The second-moment template and the densest-substructure criterion.** Frieze &
  Karoński, *Introduction to Random Graphs* (CUP 2016; free PDF
  [math.cmu.edu/~af1p/BOOK.pdf](https://www.math.cmu.edu/~af1p/BOOK.pdf)): Theorem 7.3,
  `α(G(n, p)) ≈ 2 log_b n` whp (first moment at `⌈2 log_b n⌉`, second moment by Janson's
  inequality at `⌊2 log_b n − 5 log_b log n⌋`; "first proved by Matula [762]" = Matula
  1976, SMU technical report); Theorem 5.3, the subgraph threshold `n^{−1/m(H)}` with
  `m(H) = max_{K ⊆ H} d(K)` ("Erdős and Rényi proved this result for balanced graphs. The
  threshold for any graph `H` was first found by Bollobás"), both read verbatim.
  **Bollobás, B.** (1981). Threshold functions for small subgraphs. *Math. Proc. Camb.
  Phil. Soc.* 90(2), 197–206. **Bollobás, B. & Erdős, P.** (1976). Cliques in random
  graphs. *Math. Proc. Camb. Phil. Soc.* 80(3), 419–427,
  [doi:10.1017/S0305004100053056](https://doi.org/10.1017/S0305004100053056) (scan without
  text layer at `static.renyi.hu/~p_erdos/1976-05.pdf`). **Grimmett & McDiarmid** (1975),
  *Math. Proc. Camb. Phil. Soc.* 77(2), 313–324,
  [doi:10.1017/S0305004100051124](https://doi.org/10.1017/S0305004100051124). Janson,
  Łuczak & Ruciński (2000), *Random Graphs*, Ch. 3 (theorem numbers not checked in the
  book). The corner-block argument of `reports/dense_staircase.md` §2 is the
  densest-sub-configuration step applied to a pattern of *forbidden* edges (a subgraph of
  the complement, `G(n, 1 − p)`); cite it as "in the manner of Bollobás (1981)", not as an
  instance of the sparse theorem.
- Interval completion / largest induced interval subgraph of `G(n, p)`: nothing found
  (four searches); the nearest are induced trees, paths and matchings at
  `(2 + o(1)) log_q(np)` (Dutta & Subramanian, arXiv:2004.03359, 2004.02800). Since
  `pw + 1` is the least clique number of an interval supergraph (Ohtsuki et al. 1979,
  held), the pathwidth statement is itself the interval-completion one; we found no prior
  statement.

## Random graph classes (2026-11-11)

Survey behind `reports/random_graph_classes.md`: what is in print on the pathwidth (or
treewidth, vertex separation, bisection) of random regular, geometric, planar, bipartite,
preferential-attachment, interval / chordal / split graphs, hypercubes and grids, against
what our first-moment theorems give on each. Read from open copies and from held PDFs;
nothing downloaded. Papers already held under other headings (Fomin & Høie 2006; Lichev &
Mitsche 2023; Kolesnik & Wormald 2014; Díaz, Diner, Serna & Serra 2022; Mitsche &
Perarnau 2012; Gao 2012; Perarnau & Serra 2014; Lee, Lee & Oum 2012; Edwards & McDermid
2015; Chandran & Kavitha 2006; Ellis & Warren 2008; Harper 1966; Bezrukov et al. 2004)
are not repeated.

- **Gaspers, S.** (2026). Path decompositions of sparse graphs via Gaussian sweeps and
  faster exponential algorithms. [arXiv:2611.05146](https://arxiv.org/abs/2611.05146)
  (3 November 2026). **Held since 2026-11-11**:
  `2026-Gaspers-Path-Decompositions-Sparse-Graphs-Gaussian-Sweeps-arXiv.pdf` (181 pages,
  v1), read whole for `reports/gaspers_cages.md`. Theorem 1.1(a) = Theorem 8.1:
  `pw ≤ c₃ n + o(n)` for every graph of maximum degree 3, `c₃ = (3/(4π)) arccos(5/6) ≈
  0.13982`, closing the twenty-year `n/6` of Fomin & Høie; proved in Lean without
  hypotheses (Appendix B). Theorem 1.1(b) `pw ≤ F₄ n + o(n)`, `F₄ ≈ 0.24577`, at maximum
  degree 4; Theorem 1.3 per-degree weights `a₃ = 5/32, a₄ = 1/4, a₅ = 11/32, a₆ = 7/16`;
  Corollary 1.4 `pw ≤ 7m/48 + o(n)`; Theorem 3.1 the short cut sweep `pw ≤ cw ≤ c* n +
  o(n)`, `c* = (3/(2π)) arcsin(1/3) ≈ 0.16226`, with the **only explicit remainder in the
  paper**, `2.55 n / R + 4 n^{7/8}` with `R = ⌊log₂ n / 4⌋`, valid for `n ≥ 2⁴⁶`. The
  construction (Section 2): independent standard normals `Z_w`, the label `Y_v` the
  normalised sum of `2^{-dist(v,w)/2} Z_w` over the ball of radius `R` (Definition 5.2;
  base `p − 1` at maximum degree `p`; mixed arc lengths `½ ln(d(x) − 1)` at minimum degree
  3), a threshold sweep whose bags are frontiers (Lemma 4.1), the star comparison with
  the regular simplex (Section 6, Mulgund's theorem), and for degree 3 the
  *median-switched* layout (Lemma 8.4: inner frontiers below the median, outer above,
  a connector at zero ordered by Lemma 8.3). The proof of Theorem 8.1 is existential
  (Chebyshev, a grid of thresholds, a union bound: `(8K₀ + 4) 9^{R+1} < 2 √n`, so no
  parameter is admissible below `n ≈ 1.9 × 10⁷`); Section 10 makes it a Las Vegas
  `n^{1+o(1)}` and a deterministic `n^{2+o(1)}` algorithm (finite rational distribution,
  method of conditional expectations). The random-cubic lower bound `pw ≥ 0.103295 n − 2`
  a.a.s. is **not his**: it is Lichev & Mitsche's first-moment bisection bound (held,
  `2023-Lichev-Mitsche-...`) through `bw ≤ cw ≤ pw + 2` (Díaz–Petit–Serna; Makedon &
  Sudborough; Ellis, Sudborough & Turner), the cutwidth route of
  `reports/complex_lb_search.md` §4.1. Section 15: Conjecture 15.1 `pw ≤ (c₃ − 3 p_ch) n +
  o(n) ≈ 0.13225 n` for cubic graphs, `p_ch = 0.00252477819777…` the probability, on the
  ideal wave of the rooted tree `T₂` with covariance `2^{-d/2}(1 + d/3)`, that two children
  of the root both have the root as their only neighbour above zero (the "isolated helper"
  of Lichev & Mitsche, whose printed `0.002818666` the authors confirmed inaccurate). Code
  and Lean at `https://serggasp.github.io/pathwidth-site/` (not fetched). The paper's
  Table 2 and Section 1.2 record that the ETH preprints of OpenAI and Anthropic leave its
  forty-five bounds untouched. What it says about the cages: nothing — the certified floors
  of all five open cubic cages exceed `c₃ n` (`reports/gaspers_cages.md` §0).
- **Scheinerman, E. R.** (1988). Random interval graphs. *Combinatorica* 8(4), 357–371.
  [doi:10.1007/BF02189092](https://doi.org/10.1007/BF02189092). Not held; the
  chromatic number `n/2 + o_p(n)` of the uniform-endpoint model is quoted from Diaconis,
  Holmes & Janson, *Interval graph limits* ([arXiv:1102.2841](https://arxiv.org/abs/1102.2841)),
  and the clique number follows by perfection. **Wanted**: the theorem and its error term
  (the pathwidth of a random interval graph is this clique number minus one).
- **Justicz, J., Scheinerman, E. R. & Winkler, P. M.** (1990). Random intervals. *Amer.
  Math. Monthly* 97(10), 881–889. [doi:10.2307/2324324](https://doi.org/10.2307/2324324).
  Not held; cited for the maximum degree `n − 1` with probability exactly `2/3`.
- **Habib, M. & Möhring, R. H.** (1994). Treewidth of cocomparability graphs and a new
  order-theoretic parameter. *Order* 11(1), 47–60.
  [doi:10.1007/BF01462229](https://doi.org/10.1007/BF01462229). Not held; `pw = tw` on
  cocomparability graphs (hence on interval, permutation and bounded tolerance graphs);
  abstract read. **Wanted** for Section 5's "where the clique bound is exact".
- **Gustedt, J.** (1993). On the pathwidth of chordal graphs. *Discrete Applied
  Mathematics* 45(3), 233–248.
  [doi:10.1016/0166-218X(93)90012-D](https://doi.org/10.1016/0166-218X(93)90012-D). Not
  held; pathwidth is NP-complete on chordal graphs (abstract read).
- **Chapuy, G., Fusy, É., Giménez, O. & Noy, M.** (2015). On the diameter of random planar
  graphs. *Combinatorics, Probability and Computing* 24(1), 145–178.
  [doi:10.1017/S0963548314000467](https://doi.org/10.1017/S0963548314000467); arXiv
  [1203.3079](https://arxiv.org/abs/1203.3079). Not held; the diameter of a random
  connected labelled planar graph is in `(n^{1/4−ε}, n^{1/4+ε})` a.a.s. (Theorem 1.1, via
  the abstract and Noy's ICM survey item 13). With `tw ≤ 3·diam + 1` on planar graphs
  (Robertson & Seymour 1984; Eppstein 2000) this is the only upper bound on the treewidth
  of random planar graphs we found; no lower bound beyond the trivial is in print.
- **Noy, M.** (2014). Random planar graphs and beyond. *Proc. ICM 2014*, Seoul, vol. IV,
  407–430. Open copy read
  ([web.mat.upc.edu/marc.noy/uploads/2013/05/ICM-2014.pdf](https://web.mat.upc.edu/marc.noy/uploads/2013/05/ICM-2014.pdf));
  its only treewidth statement is the deterministic `O(√n)` of the separator theorem
  (reference [2], Alon, Seymour & Thomas), for minor-closed classes. **We found no
  published statement** of the order of `tw` or `pw` of a random planar graph.
- **Eppstein, D.** (2000). Diameter and treewidth in minor-closed graph families.
  *Algorithmica* 27(3), 275–291. [doi:10.1007/s004530010020](https://doi.org/10.1007/s004530010020).
  Not held; `tw ≤ 3·diam + 1` for planar graphs is cited from it (and from Robertson &
  Seymour, Graph Minors III, 1984).
- **Bender, E. A. & Canfield, E. R.** (1978). The asymptotic number of labeled graphs with
  given degree sequences. *J. Combin. Theory Ser. A* 24(3), 296–307; **Bollobás, B.**
  (1980). A probabilistic proof of an asymptotic formula for the number of labelled
  regular graphs. *European J. Combin.* 1(4), 311–316. Not held; the probability that the
  pairing model is simple, `→ exp(−(d² − 1)/4)`, is the constant behind
  `learning.random_graph_classes.simple_correction`.
- **Bollobás, B. & Leader, I.** (1991). Compressions and isoperimetric inequalities.
  *J. Combin. Theory Ser. A* 56(1), 47–62. Not held; the vertex-isoperimetric inequality
  on the grid `[k]^n`, which is why Harper's bound is exact on grids (checked by exact
  computation to `6 × 6` in the report instead).
- **Cooper, C., Frieze, A. & Uehara, R.** (2014). The height of random k-trees and related
  graphs. *Discrete Math. Theor. Comput. Sci.* 16(2), 35–48. Not held; height `~ c log n`
  for random (increasing) `k`-trees, the only shape parameter of a random chordal model we
  found; nothing on their pathwidth.
- **Castellví, J. & Stufler, B.** (2023). Limits of chordal graphs with bounded tree-width.
  [arXiv:2310.20423](https://arxiv.org/abs/2310.20423). Open; scaling and local limits of
  uniform chordal graphs of bounded treewidth; nothing on pathwidth.
- **Scale-free and small-world generators of the dataset** (`RandomBarabasiAlbert_100_2`,
  `_100_5`, `RandomHolmeKim_300_2_2`, `_700_2_2`, `RandomNewmanWattsStrogatz_100_5_3`,
  `_250_10_3`, `RandomTriangulation_800`, `RandomBoundedToleranceGraph_60`, `_80`,
  `random4reg`, `RandomGNM_*`): the PACE 2016 named instances, generated with SageMath /
  NetworkX; their seeds are not recorded with the files, so they are single draws and no
  ensemble statement rests on them.
