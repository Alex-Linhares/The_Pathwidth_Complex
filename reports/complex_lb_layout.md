# Lower bounds on the linear-layout neighbours of the pathwidth complex: what transfers, what is already ours, what is dead

*2026-11-11, one session. Scope: the lower-bound literature of the problems that
sandwich the pathwidth complex — cutwidth, bandwidth and proper pathwidth, split
bandwidth, minimum linear arrangement and profile, treewidth, tree-depth,
linear-width, directed pathwidth — read for what transfers to pathwidth and for
techniques with an unwritten pathwidth analogue. Papers were read from open
copies (HAL, arXiv, author pages) in a scratch directory outside `literature/`;
nothing was downloaded into `literature/`; the held copies cited are the ones
already there. No solver was run and nothing on record was re-solved. The one
computation made is a brute-force census on graphs to 8 vertices (§7, §9),
scripts under `reports/scratch/complex_lb_layout/` (uncommitted). Page numbers are
the printed ones where the copy has them, otherwise the preprint's line or section.
"We found no prior statement" is the strongest attribution used; nothing is
called first.*

The three reports this one is read beside, and does not repeat:
`reports/obstruction_search.md` §0 (the families searched and their duality
gaps on the 338 corpus bound-gap instances), `reports/spectral_bound.md` §0–§1
(eigenvalue bounds sit under Harper and under `tw + 1`), `reports/chain_lp.md`
§2 and §5 (every LP in the layout variables is Harper, and every relaxation of
the layout hull is at most the Lagrangian value `L(G)`), and
`reports/layout_lp_literature.md` §0 (Caprara-style counting works only on sum
objectives). `reports/pathwidth_lower_bounds_survey.md` §1 is the table of the
treewidth and pathwidth families with their values on the Mycielski graphs;
this report cites its rows rather than restating them.

## 0. Summary, in two pages

### 0.1 Directions, with the theorem each rests on

A bound transfers to pathwidth only through an inequality that puts the
neighbour *above* pathwidth by a known amount (`pw ≥ X − c` or `pw ≥ X / f`),
or that puts it *below* (then the neighbour's lower bounds are pathwidth lower
bounds at full strength, and the neighbour itself is the ceiling). The table
fixes this before any bound is weighed.

| neighbour `X` | relation | source | Lean (`lean/MOSPFormalization/`) | a lower bound `L ≤ X` gives |
|---|---|---|---|---|
| treewidth | `tw ≤ pw` | Bodlaender 1998 Thm 44ff; `tw ≤ pw` folklore | `treewidth_le_pathwidth` (`Sandwich.lean`) | `pw ≥ L` — full strength; ceiling `tw`, which is below the optimum on 142 of the 209 gap instances with exact treewidth (`ml_nature.md` §24) |
| cutwidth | `pw ≤ cw ≤ Δ·pw` | Bodlaender 1998 Thm 47 (p. 24) and the proof of Thm 49 (p. 24): a path decomposition of width `c` gives a layout of cutwidth `≤ c·Δ` | `pathwidth_le_cutwidth` (`Complex/EdgeSeparation.lean`); the upper half not formalised | `pw ≥ ⌈L / Δ⌉` — division by the maximum degree (15–64 on the residual instances) |
| bandwidth, proper pathwidth, topological bandwidth | `pw ≤ bw`, `ppw = bw` (Kaplan & Shamir 1996), `pw ≤ tbw` | Bodlaender 1998 Thms 44, 45 (p. 23); DPS 2002 Lemma 2.4 (`VS ≤ BW`) | `pathwidth_le_bandwidth` (`Sandwich.lean`) | nothing: `bw` is unbounded in `pw` (stars: `bw(K_{1,n}) = ⌈n/2⌉`, `pw = 1`) |
| split bandwidth | `pw ≤ sb ≤ pw + 1` | Fomin 1998 Thm 8 | `pathwidth_le_splitBandwidth_le_pathwidth_add_one` (`Complex/SplitBandwidth.lean`) | `pw ≥ L − 1` |
| linear-width | `pw ≤ lw ≤ pw + 1` for `lw ≥ 1` | Fomin & Thilikos 2006 Lemma 2 (held, p. 502), corrected at `K_2` by Kobayashi & Nakahata 2021 Lemma 2 (held) | — (`paper2/complex_members.md` row 17, checked on 1,233 atlas graphs) | `pw ≥ L − 1`, through the *upper* half |
| mixed search = 3-proper pathwidth | band `pw` to `pw + 1` | Takahashi, Ueno & Kajitani 1995; Bodlaender 1998 Thm 62 | — (`complex_members.md` row 18) | `pw ≥ L − 1` |
| tree-depth | `tw ≤ pw ≤ td ≤ tw·log₂ n` | Bannach & Berndt 2022 p. 4 (held, their [58]); Bodlaender 2024 Lemma 3 (held) | — | `pw ≥ L / log₂ n`: division by a logarithm; the direction the brief feared is the real one |
| minimum linear arrangement | `MinLA ≤ n·cw ≤ nΔ·pw` | DPS 2002 Lemma 2.4 (p. 317) with the cutwidth row | — | `pw ≥ L / (nΔ)` |
| profile = sum cut | `SC ≤ n·vs` (DPS Lemma 2.4); sharper, `SC(σ) = Σ_{t<n} B_σ(t) ≤ (n−1)·vs` | DPS 2002 §2 (profile and sum cut are the same problem, p. 317) | — | `pw ≥ ⌈L / (n − 1)⌉` |
| vertex bisection | `VB ≤ vs` | DPS 2002 Lemma 2.4 | Harper at `t = ⌊n/2⌋`: `exists_closedNbhd_card_le` (`EmptyPair.lean`) | `pw ≥ L` — and it *is* one level of Harper |
| directed pathwidth | `dpw(Ĝ) = pw(G)` on the symmetric digraph | Coudert, Mazauric & Nisse 2016 §1 p. 2 (held) | — | `pw ≥ L` at full strength; the literature has no bound to give (§8) |

Two consequences shape everything below. (i) **Only treewidth, vertex
bisection and directed pathwidth transfer at full strength**, and the first
two are already in the solver as `tw + 1` (proposed), contraction degeneracy
and Harper. (ii) Every bound on cutwidth, MinLA or tree-depth arrives divided
by `Δ`, `nΔ` or `log n`; on the residual instances (`Random-100-100-4`,
`Random-125-125-4/6`; optimum 50–77, `Δ` 15–64) a cutwidth bound would have to
exceed `Δ·optimum ≈ 10³` to say anything, while cutwidth itself is at most
`Δ·pw`. **No bound on a divided neighbour can be competitive there, whatever
its strength on its own problem.** So the survey is really about *techniques*:
does any neighbour's argument have a pathwidth form nobody wrote down?

### 0.2 The techniques, classified

Classification against our families: **degree** (trivial, clique, degeneracy,
contraction degeneracy, minimum degree of a minor — all `≤ tw + 1`, `ml_nature.md`
§24); **Harper** (the vertex-isoperimetric prefix bound and anything that is one
separator of a layout, `spectral_bound.md` §1(i)); **minor** (family M, tight on
327 of 338); **branch** (family B, closed); **spectral** (under Harper and under
`tw + 1`); **LP / SDP** (under the Lagrangian ceiling `L(G)`, `chain_lp.md` §5);
**blockage** (the exact dual, no algorithm); **different** (none of the above,
with the reason). "Verdict" is what this report recommends.

| # | technique | source (page) | on its problem | pathwidth analogue | class | verdict |
|---|---|---|---|---|---|---|
| 1 | `cw ≥ max_{u,v} λ(u,v)` (minimum edge cut; Gomory–Hu) | DPS 2002 Thm 9.5 p. 340; Martí et al. 2013 eq. (6); BCCH 2025 Prop. 1 | exact `O(m^{1+o(1)})` | **does not transfer as vertex connectivity**: `K_{2,t}` has `κ(a,b) = t`, `pw = 2` — a layout's prefix boundary may *contain* `v`. The valid vertex analogue is Harper. | Harper | covered; cite DPS 9.5 for the contrast |
| 2 | `cw ≥ λ₂ ⌊n/2⌋⌈n/2⌉ / n` (algebraic connectivity) | Juvan & Mohar 1992 via DPS Thm 9.2 p. 339; Martí eq. (7); BCCH Prop. 2 | one eigenvalue | the prefix-separator spectral bound, Theorems 1–4 of `spectral_bound.md` | spectral | covered, dead |
| 3 | `cw ≥ ⌈Δ/2⌉` | folklore; Bodlaender 1998 p. 24; Gaar et al. §1; BCCH Prop. 3; Martí LB1 eq. (22) | `O(n)` | `vs ≥ 1` if an edge exists; the vertex form of "half the neighbours on one side" is the trivial bound | degree | covered |
| 4 | `cw ≥ δ*(δ* + 2)/4` (degeneracy `δ*`), `cw ≥ δ(δ+2)/4` (min degree) | Kloeckner 2010 Cor. 2.2; BCCH Prop. 4–5 | linear | `degeneracy ≤ pw` (`degeneracy_le_pathwidth`); the quadratic is the edge-count of the degeneracy core, which pathwidth does not see | degree | covered |
| 5 | average / maximum average degree, by sum-of-cuts ("traffic grooming") | BCCH 2025 Prop. 6–9 (§3) | `O(1)` / one max-flow | sum over cuts of the vertex boundary: `Σ_t B_σ(t) ≥ Σ_v d⁺_σ(v) = m`, so `pw ≥ ⌈m/(n−1)⌉`; under `tw` since `m ≤ tw·n − tw(tw+1)/2`; the weighted sum is `chain_lp.md` §5's `L(G)` with uniform `μ` | LP (uniform Lagrangian) | covered by the `L(G)` theorem |
| 6 | `cw ≥ C*(m, n)`: the least cutwidth of any graph with `n` vertices and `m` edges (grooming on the path) | BCCH 2025 Prop. 10–11, Thm 1 (§4); Martí LB4 §3.4 (corrected by BCCH §4.2: greedy is right only to `C ≤ 9`) | `O(log n)` | the least pathwidth over graphs with `n, m`: the extremal graphs are path powers `P_n^k` with `kn − k(k+1)/2` edges and `pw = tw = k`, so the analogue is the treewidth edge bound | degree (edge count) | covered |
| 7 | partial-solution bounds LB2, LB3 and the dominance rule `LB2(g) ≤ LB2(h)` on the same set | Martí et al. 2013 §3.2–3.3, §4 eqs (30)–(32) | per node | LB2 is the prefix's own cost; LB3 the next vertex's forced cost; the dominance rule is the set memo of Chu & Stuckey (same set, keep the better prefix) and `commitments` of Kobayashi, Komuro & Tamaki 2014 | search rules already in `decide` | covered |
| 8 | SDP over linear-ordering variables with 3-dicycle, triangle and lifted inequalities | Gaar, Puges & Wiegele 2024 §2 | `n ≤ 50`, minutes; 20–63 % gaps on 16–24-vertex sparse graphs where MILP solves them in 3 s (§4.2.1) | an SDP in the same variables for the max boundary: **its value is at most `L(G)`** (`chain_lp.md` §5: any relaxation of the layout hull is), and `L` was bounded above but not down to Harper at 30–50 | LP / SDP | not built; a two-minute pre-test closes the route (§9.2) |
| 9 | `bw ≥ max_S (|S| − 1)/diam(S)` (density); `α(G)` and `γ(G)` from balls `N_k(v)` | Chvátal 1970; Chinn et al. 1982; Blum et al. 2000 eq. (5); Caprara & Salazar-González 2005 eq. (6), both as restated in Benadé & Hooker 2019 §7 | `O(nm)` | none: pathwidth is not a distance parameter (`K_{1,n}` again); the layered-graph *upper* bound `pw ≤ max_i(|L_i| + |L_{i+1}|) − 1` is `ForestCover.lean`'s layer lemma | — (bandwidth only) | does not transfer |
| 10 | level-structure bound `|L| ≤ bw ≤ 2|L| − 1` | Lim, Rodrigues & Xiao 2007 | — | same as 9 | — | does not transfer |
| 11 | 3-partition principle: if every `(S₁, S₂, S₃)` with `|S₂| = m₂` has an `S₁`–`S₃` edge then `bw > m₂`; eigenvalue form `bw > nλ₂/λₙ` | Juvan & Mohar 1992; Helmberg et al. 1995 Thm 8; Haemers 1995; Rendl, Sotirov & Truden 2021 §1 | one eigenvalue | **this is Harper's principle**: `(A, C, B)` with `|C| = w`, no `A`–`B` edge, is the prefix triple; the eigenvalue form is `spectral_bound.md` Thm 2 | Harper / spectral | covered |
| 12 | min-cut SDP (Povh–Rendl), QAP SDP (de Klerk et al.; van Dam & Sotirov), `k`-partition SDP (Rendl–Sotirov–Truden: matrices of order `n·k`, graphs to 128 vertices) | van Dam & Sotirov 2015 §1 p. 2, §3 eq. (4) (held); RST 2021 §1, §3–§5 | hours at 30 vertices for general graphs (vDS p. 2) | `k` checkpoints of the layout = the nested-prefix relaxation CHK of `reports/checkpoint_relaxation.md`, which with *exact* segment checks gains a quarter of a stack on fixed grids; an SDP of it is weaker than the exact CHK | LP / SDP (checkpoint) | covered, dead |
| 13 | Harper 1966: bandwidth of the cube by the vertex-isoperimetric inequality; Lin & Lin 2025 the same for `pw`, `tw` of hypercubes | Harper 1966 (held); Chandran & Kavitha 2006 (held); Lin & Lin 2025 (listed) | closed form on cubes | **it is our Harper bound** (`expansion_bound.py`; `exists_closedNbhd_card_le`) | Harper | covered; the origin of the family |
| 14 | exact bandwidth: UPO branch and bound; B&B with `LB2(g)`, `LB3(g)`; `O(4.473ⁿ)` bucket DP | Del Corso & Manzini 1999; Martí, Campos & Piñana 2008; Cygan & Pilipczuk 2010 | — | no lower bound beyond the partial layout's own cost; Cygan–Pilipczuk's buckets are an *algorithm* (positions by `b`-blocks), not a bound | search | nothing to take |
| 15 | MinLA: Path, Edges, Degree, Gomory–Hu, Mesh, `λ₂(n² − 1)/6`, decorous LP | Petit 2003 §2 (Thms 1–3); Adolphson & Hu 1973; Caprara, Letchford & Salazar-González 2011 (held) | linear in `n` except Juvan–Mohar | each arrives divided by `nΔ`; the Degree method's per-vertex count has no max-objective form (`layout_lp_literature.md` §1.4) | LP (sum objective) | covered, dead |
| 16 | profile lower bounds (interval completion) | Lin & Yuan 1994 | — | `pw ≥ ⌈profile/(n−1)⌉` is the uniform-`μ` Lagrangian, `≤ L(G)` | LP | covered |
| 17 | treewidth: `δ`, `δ₂`, `γ_R`, MMD, MMD+, MCSLB(+), LBN/LBP(+), girth, spectral, brambles, exact `tw` | Bodlaender & Koster 2011 (TR held); `pathwidth_lower_bounds_survey.md` §1 rows 1–11 | — | all `≤ tw + 1`, the ceiling of `ml_nature.md` §24; LBP's disjoint-path ("matching") lemma holds for `pw` (survey §2.1) but drives a treewidth bound | degree / tw | covered, cite |
| 18 | treewidth by safe separators and blocks (`tw = max` over blocks) | Bodlaender & Koster 2006 | linear | **false for pathwidth** (trees); the pathwidth replacement is the branch lemma of Fellows & Langston 1987 L. 4.3 / Kinnersley 1992 Cor. 4.2, family B, closed on the residual (`obstruction_search.md` §0.5) | branch | covered |
| 19 | brambles (`tw + 1 = ` max bramble order), layered brambles for planar graphs | Seymour & Thomas 1993; Bodlaender, Grigoriev & Koster 2008 (TR held) | flows | blockages (BRST 1991); the compact class of `blockage_class.md`; connected frames are blind to `pw > tw` (Appendix F, Prop. on connected frames) | blockage | covered |
| 20 | certified minor lower bounds with a *lift* step | Tamaki 2022 (held) | 30 min on PACE 2017 bonus graphs | family M, searched (`obstruction_search.md` §4–§5); the lift guidance (safe separators crossing a fill) does not transfer | minor | covered |
| 21 | PACE 2017 exact treewidth track | Dell et al. 2017 (listed) | — | there was no lower-bound track (Tracks A, B exact/heuristic treewidth, C minimum fill-in); PACE 2026 (maximum agreement forest) is the first with one | — | nothing |
| 22 | tree-depth solvers: core subgraph, min-degree contraction, MMD+ clique minors, long paths, PID DP, isomorphism-hash reuse of bounds across induced subgraphs | tdULL §2.1.1; SMS §3.3; Bute §2–3 (all 2020) | per node | core = degeneracy peeling (`spectral_bound.md`'s `peel`), contraction = family M, long paths are tree-depth-only (`pw(P_n) = 1`), PID = Bannach & Berndt 2022 (held); **isomorphism-hash sharing of refutations across states is not in our search** | search (different) | §9.3: a measurement with a kill criterion, cost hours |
| 23 | linear-width: edge-ordering isoperimetry | Thomas 1996 (definition); no lower-bound literature found | — | `pw ≥ max_s g(s) − 1` with `g(s) = min_{|F|=s} #{v : F ∋ e ∋ v, E∖F ∋ e' ∋ v}` — a Harper bound on the *edge* lattice; valid through `lw ≤ pw + 1` | different (Harper on another lattice) | **measured dead**: on every connected graph to 7 vertices it beats Harper only where `pw = tw` (8 graphs), and on all 273 connected 8-vertex graphs with `pw > tw` and `m ≤ 16` it never beats Harper, let alone `max(Harper, tw)` (§7, §9.1) |
| 24 | directed pathwidth: commitments, prefix table, no lower bound | Kitsunai et al. 2016 (held); Coudert, Mazauric & Nisse 2016 p. 19 (held) | — | CMN's own closing words ask for "lower bounds for pathwidth that are not lower bounds for treewidth" (held copy, lines 1109–1112) | — | nothing to take |

### 0.3 What we can use, ranked (honest)

1. **Nothing in the neighbours' lower-bound literature transfers a bound we do
   not already compute**, and nothing transfers at full strength except what
   is already a treewidth or Harper argument. The expected verdict "already
   covered, cite" holds for 21 of the 24 rows; two do not transfer at all
   (rows 9–10); one is measured dead (row 23).
2. **Citations the paper should carry**, each in place of a sentence that now
   stands alone: DPS 2002 Lemma 2.4 and Thm 9.5 for the directions and for why
   the Gomory–Hu bound has no vertex form; Bodlaender 1998 Thms 44–49 for
   `pw ≤ cw ≤ Δ·pw` and `pw ≤ bw`; Juvan & Mohar's 3-partition principle
   (through RST 2021 §1) as the bandwidth form of Harper's argument; Kaplan &
   Shamir 1996 so that "proper pathwidth" is read as bandwidth; BCCH 2025 §3
   as the sum-of-cuts argument whose pathwidth form is the uniform Lagrangian
   of `chain_lp.md` §5; Coudert, Mazauric & Nisse 2016 p. 19 for the open
   question our minor certificates answer.
3. **Two cheap measurements with kill criteria, proposed and not run** (§9):
   (a) the mixture upper bound on `L(G)` on the 11 residual instances —
   minutes; if `⌈U⌉ ≤` the record floor on all 11, every LP and SDP route in
   layout variables (rows 8, 12, 15, 16 and Mallach's `LP_L`) is closed on the
   residual by one theorem and one number; (b) the share of search states
   whose residual graph is isomorphic to an earlier one, on the 41–75-customer
   certificates of `learning/search_certificate.py` — hours; below 10 % the
   tree-depth solvers' isomorphism memo (row 22) is dead for us.
4. **Not worth doing, with the reason**: any cutwidth or MinLA bound (division
   by `Δ` or `nΔ`); bandwidth density and ball bounds (no pathwidth form);
   the `k`-partition SDP (the exact CHK already measured the family);
   an edge-lattice Harper search on the corpus (§9.1: dead on the census, so
   the corpus test is not warranted).

### 0.4 What this does not claim

That the census of §7 is exhaustive beyond 8 vertices and 16 edges; that the
edge-lattice bound is new (Thomas's linear-width is the parameter, and an
isoperimetric bound on edge orderings was not searched for specifically);
that any paper here was read in its journal pagination where only a preprint
was open (stated per paper); that Martí et al.'s LB4 is wrong (BCCH §4.2
corrects its greedy claim above `C = 9`, which we did not check); that the
tree-depth solvers' isomorphism memo would help (it is a measurement to make).

---

## 1. The arithmetic of transfer

For a quantity `X` with `pw ≤ X ≤ f(pw, G)`, a lower bound `L ≤ X` gives
`pw ≥ f⁻¹(L)`. The useful cases:

- **`tw ≤ pw`** (`treewidth_le_pathwidth`): any treewidth lower bound is a
  pathwidth lower bound, and its ceiling is `tw`. This is the whole of row 17
  and the reason the degree family is capped (`ml_nature.md` §24: on 131 of
  the 338 gap instances `optimum > tw_min_fill + 1`).
- **`pw ≤ cw ≤ Δ·pw`.** The lower half is Bodlaender 1998 Thm 47 (p. 24): from
  a layout of cutwidth `k`, the bags `X_i = {w : f(w) > i, ∃ v: vw ∈ E, f(v) ≤ i} ∪ {f⁻¹(i)}`
  form a path decomposition of width `≤ k`. Lean: `pathwidth_le_cutwidth`. The
  upper half is inside the proof of Thm 49 (p. 24): order the vertices by the
  first bag of a path decomposition of width `c`; an edge crossing position
  `j` has an endpoint in `X_{g(v)}`, so at most `c·Δ` edges cross. Hence
  `pw ≥ ⌈cw / Δ⌉`, and since `cw ≤ Δ·pw` the division is exactly the loss:
  a cutwidth bound reaches the pathwidth only on graphs where every vertex of
  the widest boundary has all `Δ` edges crossing the same cut.
- **`pw ≤ bw`** with no upper half: `bw(K_{1,n}) = ⌈n/2⌉` against `pw = 1`
  (Bodlaender 1998 p. 23 gives the sharpness family `G_{n,k}`). Bandwidth
  bounds do not transfer. Proper pathwidth is bandwidth (Kaplan & Shamir 1996),
  topological bandwidth is above pathwidth (Thm 45), the `q`-proper interval
  parameters of Proskurowski & Telle 1999 (held) interpolate from `bw` at
  `q = 0` to `pw` at `q = k`: a lower bound on the `q`-proper parameter
  transfers only at `q = k`, where it is pathwidth.
- **`pw ≤ sb ≤ pw + 1`, `pw ≤ lw ≤ pw + 1`, mixed search likewise.** A bound
  on the band parameter transfers with the loss of one; the transfer uses the
  *upper* inequality. Fomin & Thilikos 2006 Lemma 2 (held copy line 154:
  "for any graph `G`, `pw(G) ≤ lw(G) ≤ pw(G) + 1`") needs `lw ≥ 1`
  (Kobayashi & Nakahata 2021 Lemma 2: `lw(K_2) = 0`); `complex_members.md` row
  17 checked both ends on 1,233 atlas graphs.
- **`pw ≤ td − 1 ≤ tw·log₂ n`** (Bannach & Berndt 2022 p. 4, line 252 of the
  held copy: `tw(G) ≤ pw(G) ≤ td(G) ≤ tw(G)·log₂ n`): tree-depth lower bounds
  arrive divided by `log₂ n` (6.97 at `n = 125`). The brief's worry about the
  direction was right.
- **`MinLA ≤ n·cw`, `profile = sumcut ≤ n·vs`, `VB ≤ vs`, `EB ≤ cw`,
  `cw ≤ Δ·bw`**: DPS 2002 Lemma 2.4, p. 317, the lemma that organises the
  whole survey's bounds. The sharp form of the profile row is an identity:
  the profile of a layout *is* the sum of its `n − 1` vertex-separation cuts
  (`SC(σ) = Σ_t B_σ(t)`, DPS p. 317 on the reversed layout), so
  `pw ≥ ⌈profile / (n − 1)⌉`.
- **`dpw(Ĝ) = pw(G)`** for the symmetric digraph `Ĝ` (Coudert, Mazauric &
  Nisse 2016 §1 p. 2; `dpw = dvs` p. 4). Full-strength transfer in both
  directions, which is why §8 has nothing to report: the directed solvers
  carry no lower bound.

## 2. Cutwidth

### 2.1 Relations

`pw ≤ cw` (Bodlaender 1998 Thm 47; `pathwidth_le_cutwidth`, with the star
counterexamples `cutwidth_unbounded` and `modCutwidth_unbounded` showing no
constant in the other direction, `Complex/EdgeSeparation.lean`); `cw ≤ Δ·pw`
(Thm 49's proof); `cw ≥ tw` (Bodlaender 1986, as cited by Gaar et al. §1);
`cw ≥ ⌈Δ/2⌉` (Thm 49's proof, "the cutwidth of `G` is at least `degree(G)/2`").
On subcubic graphs `cw = es` (Makedon & Sudborough 1989, listed), hence within
`pw` to `pw + 2`; and `cw(G) = vs(L(G))` for `Δ ≤ 3` (`reports/subexp_pathwidth.md`
§7.1 Theorem 7.1, checked to 14 edges), which carries pathwidth *to* cutwidth
through the line graph and nothing back.

### 2.2 The bounds, paper by paper

**Díaz, Petit & Serna 2002** (held), §9 pp. 338–340. Thm 9.1 (Juvan & Mohar's
path method): `MinLA(G) ≥ MinLA(P_n^k)` and `bw ≥ k` for `k = ⌊c(n, m)⌋`, the
largest power of a path with at most `m` edges — an edge-count bound; the
pathwidth form is `pw ≥ k` for the same `k`, which is the treewidth edge bound
(`m ≤ tw·n − tw(tw+1)/2`). Thm 9.2: `MinLA ≥ λ₂(n² − 1)/6`,
`cw ≥ λ₂ ⌊n/2⌋⌈n/2⌉/n`, `EB ≥ λ₂ n/4`. Thm 9.3 (Helmberg et al. 1995):
`bw ≥ α` or `α + 1` with `α = ⌊nλ₂/λₙ⌋`. Thm 9.4 (Mohar & Poljak 1993): the
separator inequality `|C| ≥ 4λ₂|A||B| / (Δn − λ₂|A ∪ B|)`, which the survey
itself says gives "lower bounds for VERTSEP and BANDWIDTH" — this is Theorem 1
of `spectral_bound.md`, measured dead. Thm 9.5 (Gomory–Hu tree `T` with cut
weights `w`): `cw ≥ max_e w(e)`, `MinLA ≥ Σ_e w(e)` (Adolphson & Hu 1973),
`bw ≥ ⌈Σ_e w(e)/n⌉`. The cutwidth row is the one with no vertex form:
`cw ≥ λ(u, v)` because every cut of the layout between `u` and `v` is a
`u`–`v` edge cut; the vertex analogue would be `vs ≥ κ(u, v)`, and it is false
— in `K_{2,t}` the two-side vertices `a, b` have `κ(a, b) = t` while `pw = 2`
(the layout `a, x_1, …, x_t, b` has every prefix boundary `≤ 2`). What fails
is that a prefix boundary may contain `v` itself; the statement that survives
is the one quantified over all `t`-sets, which is Harper.

**Martí, Pantrigo, Duarte & Pardo 2013** (preprint read; journal COR 40(1),
137–149). §2.1 reviews four bounds: `LB_FF = max_{o,d} cut(o, d)` eq. (6),
`LB_LM = λ₂⌊n/2⌋⌈n/2⌉/n` eq. (7), `LB_MinLA = LA(G)/n` eq. (10), `LB_EB = EB(G)`
eq. (11), the last two from DPS Lemma 2.4. §3 proposes four: LB1
`= max_v ⌈|N(v)|/2⌉` eq. (22) (the degree bound, computed once); LB2 the
cutwidth of the labelled prefix with its edges to the unlabelled part, eq.
(23), `O(n)` incremental; LB3 the forced cost of the next position,
`CW_f(v_k) − max_{u ∈ U}(|N_S(u)| − |N_U(u)|)` eq. (26); LB4 the least cutwidth
of any graph with `n` vertices and `m` edges (§3.4, by placing edges of
length 1, then ⌊(n−1)/2⌋ of length 2, …). §3.6 shows no dominance among
LB1–LB4. §4: two partial solutions on the same vertex set are compared by
LB2, and the one with the larger value is fathomed, eqs (30)–(32); to avoid
storing `O(n!)` sets only the lexicographic representative is checked. The
pathwidth reading: LB2 is the prefix's own boundary (what `decide` prunes on),
LB3 is one step of look-ahead, the dominance rule is the set memo with a
weaker tie (same set, any order: Chu & Stuckey 2009's nogood; Coudert,
Mazauric & Nisse 2016 Lemma 4), and LB4 is the edge-count bound of row 6.
Sizes: all instances to 32 vertices and some to 158 within 30 minutes (§7).

**Bermond, Cosnard, Coudert & Havet 2025** (HAL `hal-05083322`, open; COR 182,
107130). §2 Props 1–4 restate the edge-cut, `λ₂`, `Δ/2` and degeneracy bounds
(Prop. 4 is Kloeckner's `cw ≥ δ*(δ* + 2)/4`). §3: Prop. 5 `cw ≥ (⌊δ/2⌋ + 1)⌈δ/2⌉`
from the first `⌊δ/2⌋ + 1` vertices of any layout; Prop. 6 the **sum-of-cuts
argument** — a vertex with `d⁺` forward edges loads the next `d⁺` path edges
by `d⁺, d⁺ − 1, …`, so `Σ_i load_i ≥ ½ Σ_i d⁺(v_i)(d⁺(v_i) + 1)` and
`cw ≥ load / (n − 1)`; Prop. 7 by convexity `cw ≥ ½ (m/(n−1))(m/(n−1) + 1)`
(eq. (6), `O(1)`); Props 8–9 the same on the densest subgraph (`Mad`, one
max-flow). §4: `cw ≥ C*(m, n) = min{C : m ≤ T(C, n)}` with `T(C, n)` the
maximum number of requests groomable on a path of `n` nodes at load `C`
(Props 10–11; closed form Thm 1 from their [9]; §4.2 notes that the greedy
"all shortest requests" rule, stated as a result by Martí et al. [39], holds
only to `C ≤ 9`, with a counterexample at `n = 11`, `C = 10`); §4.3 proves it
dominates `LB_Ad`, §4.4 computes it in `O(log n)`. Table 3 (`n = 20`,
Erdős–Rényi): their best bound 12–41 against the SDP bounds 14.27–38.65 of
Gaar et al., in milliseconds against a minute. Conclusion (§6): bounds "of
interest to design faster branch-and-bound algorithms".

*Pathwidth form of Prop. 6.* In a layout `σ`, a vertex `v` at position `i`
with forward neighbours at positions `j_1 < … < j_d` is counted in the
vertex separation of every cut `t` with `i ≤ t < j_d`, hence in at least `d`
cuts; so `Σ_t B_σ(t) ≥ Σ_v d⁺_σ(v) = m` and `vs ≥ ⌈m/(n−1)⌉`. That is the
uniform-weight case of the Lagrangian `L(G) = max_μ min_σ Σ_t μ(t) B_σ(t)` of
`chain_lp.md` §5, and `L ≥ Harper` already; the elementary form sits under
`tw` because a graph of treewidth `k` has at most `kn − k(k+1)/2` edges. The
convexity step has no pathwidth counterpart because the vertex count does not
grow with the forward degree: that is exactly why cutwidth is a sum-friendly
objective and vertex separation is not (`layout_lp_literature.md` §1.4).

**Kloeckner 2010** (arXiv 0907.5138): Thm 2.1 for `(ρ, λ)`-uniformly sparse
graphs, `cw ≥ ⌈ρn⌉(δ* − (⌈ρn⌉ − 1)/λ)` and, when `2nρ ≤ δ*λ − 1`,
`cw > (δ*λ + 1)²/(4λ) − 1/λ`; Cor. 2.2 `cw ≥ δ*²/4 + δ*/2`. Sharp on complete
graphs, "rather poor" on trees and hypercubes (his words). Degeneracy family.

**Gaar, Puges & Wiegele 2024** (arXiv 2301.03900 v4; COR, doi
10.1016/j.cor.2023.106449). §1: `cw ≥ ⌊(Δ + 1)/2⌋`; `cw ≥ tw` (Bodlaender 1986).
§2.1: variables `x_{ij}` (`i` before `j`) and the lifted matrix `X` of
products; `α ≥` each vertex's cut as a quadratic in `(x, X)`; `x = diag X`;
`[[1, xᵀ], [x, X]] ⪰ 0`, after Buchheim et al. 2010. §2.2: 3-dicycle equations,
triangle inequalities, Lemma 2.2's family (10) from the squared linear
ordering polytope, lifted LOP inequalities. §3: cutting planes by simulated
annealing, at most 7 rounds; the SDP point rounded to an ordering gives the
upper bound. §4: on 84 sparse graphs of 16–24 vertices gaps of 20–63 %
(mean 44 %) in a minute where Coudert's MILP solves them in 3.2 s; on dense
random graphs to 50 vertices the SDP is where MILP cannot go. *Transfer.* The
same lifting for vertex separation would put `α ≥ Σ_v s[v,t]` over a lifted
`(y, s)`; whatever the inequalities, the value is a relaxation of the layout
hull in those variables, so `≤ L(G)` by `chain_lp.md` §5. The route is not
dead by theorem — `L > Harper` on 93 % of the corpus instances at 9–20 — but
it is capped by a number we can bound from above in minutes (§9.2), and the
SDP's own scaling (order `n(n−1)/2` lifted to products, `n ≤ 50`) is two
sizes short of the residual.

**Coudert 2016** (held) and **Bansal, Katzelnick & Schwartz 2024** (held as
the FOCS arXiv): the ILP and the `log^{1+o(1)} n` approximation; BCCH's §2
remark that LP and SDP bounds "cannot be computed in a reasonable time for
graphs with more than 50 vertices" is the practical verdict.

## 3. Bandwidth and proper pathwidth

**Direction.** `pw ≤ bw`, no converse; `ppw = bw` (Kaplan & Shamir 1996, SIAM
J. Comput. 25(3)). Nothing here is a pathwidth bound; the question is only
whether a technique has a pathwidth form.

**Harper 1966** (held): the bandwidth of the `n`-cube by solving the
vertex-isoperimetric problem exactly — the first `t` vertices of a layout of
bandwidth `b` have at most `b` vertices of outer boundary, so
`bw ≥ max_t min_{|S|=t} |N(S) ∖ S|`. The same sentence with `vs` for `bw` is
our Harper bound (`exists_closedNbhd_card_le`), and `pw ≤ bw` is why the
bandwidth statement is the weaker use of it. Chandran & Kavitha 2006 (held)
and Lin & Lin 2025 (listed) apply it to pathwidth and treewidth of hypercubes.
Covered: the family is named after this paper for a reason.

**Chvátal 1970; Chinn, Chvátalová, Dewdney & Gibbs 1982.** The density bound
`bw ≥ max_S (|S| − 1)/diam(S)` (Benadé & Hooker 2019 §7 eq. (4), attributing
it to Chvátal 1970; MathWorld's `(n − 1)/diam ≤ bw ≤ n − diam` cites the 1982
survey, JGT 6(3), 223–254, not read). No pathwidth form: `K_{1,n}` has diameter
2 and pathwidth 1.

**Blum, Konjevod, Ravi & Vempala 2000**: `α(G) = max_v max_k (|N_k(v)| − 1)/(2k)`
(eq. (5) in Benadé & Hooker), a half of the density bound computable in
`O(nm)` by layered graphs; their SDP relaxation is the one Dunagan & Vempala
round. **Caprara & Salazar-González 2005** (IJOC 17(3), 356–373; not open):
`γ(G) = min_v max_k (|N_k(v)| − 1)/k` (eq. (6) there), the layered bound that
adapts to fixed positions, and the bilevel integer program (their (29),
Propositions 12 and 15, `O(m log n + n log² n)` per node) that Benadé & Hooker
§8 use as the relaxation of their branching dual; MM instances to 250 vertices,
"24 of 30 literature instances under 200 nodes" to optimality. Ball growth
again: no pathwidth form, the layer lemma being an *upper* bound for pathwidth
(`pathwidth_le_layerWidth_dist`, `ForestCover.lean`).

**Lim, Rodrigues & Xiao 2007**: given a level structure, `|L| ≤ bw ≤ 2|L| − 1`
for layouts that follow the levels — a statement about level layouts, not a
bound on `bw(G)` without the restriction. Nothing to transfer.

**Juvan & Mohar 1992; Helmberg, Mohar, Poljak & Rendl 1995 (held); Haemers
1995; Povh & Rendl 2007; de Klerk, Nagy & Sotirov 2013; van Dam & Sotirov 2015
(held); Rendl, Sotirov & Truden 2021.** RST §1 states the principle behind all
of them: "3-partitions of the vertices into blocks `S₁, S₂, S₃` of sizes
`m₁, m₂, m₃`; if all such partitions have edges joining `S₁` and `S₃`, then the
bandwidth must be bigger than `m₂`". For vertex separation the prefix triple
`(V_t, C_t, rest)` has no `V_t`–rest edge and `|C_t| ≤ vs`, so the same
principle reads: if every `(A, C, B)` with `|A| = t`, `|C| = w` has an `A`–`B`
edge then `vs > w` — Harper at level `t`, exactly. The eigenvalue relaxations
(`bw > nλ₂/λₙ`, Helmberg Thm 8; Haemers by interlacing; the min-cut SDP of
Povh–Rendl with its copositive origin; the QAP SDPs of de Klerk et al.; van
Dam & Sotirov's two-vertex fixing with symmetry reduction to 216 vertices;
RST's `k`-partition SDP in matrices of order `n·k`, graphs to 128 vertices)
are relaxations of that principle, and `spectral_bound.md` §1(i) proves every
one-separator spectral statement sits under Harper. The `k`-partition model
is worth one more sentence: with `k` blocks the layout is fixed at `k`
checkpoints, which is the CHK relaxation of `reports/checkpoint_relaxation.md`
with blocks of equal size; there the *exact* checks at 2–6 fixed sizes gained
a quarter of a stack on the 66 corpus instances where Harper fails, and only
adaptive, locally minimal checkpoint sets (a median of six, five consecutive
sizes at `0.5–0.7 n`) certified. An SDP relaxation of the same partition is
weaker than the exact check and cannot do better. Covered, dead.

**Exact solvers.** Del Corso & Manzini 1999 (Computing 62, 189–203): the
upper partial ordering and a branch and bound; Martí, Campos & Piñana 2008
(EJOR 186(2), 513–528): a single B&B tree from a GRASP incumbent with
`LB2(g)`, `LB3(g)` for partial orderings "related to the integer linear
programs of Caprara and Salazar"; Cygan & Pilipczuk 2010 (TCS 411, 3701–3713):
`O(4.473ⁿ)` and `O(n^{O(t)} 2ⁿ)` at treewidth `t` — algorithms over bucket
assignments (positions by blocks of width `b`), with no lower bound of their
own; the "bucket" vocabulary in the brief belongs to Feige's and Fürer,
Gaspers & Kasiviswanathan's approximation, not to a bound. Nothing to take.

## 4. Minimum linear arrangement, profile, sum objectives

**Petit 2003** (JEA 8, 2.3; preprint read), §2: Path method (Juvan & Mohar
Thm 1, `MinLA ≥ MinLA(P_n^k)`); Edges method (at most `n − c` edges of length
`c`); Degree method (a vertex of degree `d` contributes at least
`d²/4 + d/2`, halved over edges); Gomory–Hu (Adolphson & Hu Thm 2,
`MinLA ≥ Σ_e w(e)`); Juvan–Mohar `λ₂(n² − 1)/6` (Thm 3); Mesh method (packing
square meshes, `(4 − √2)s³/3`). §7: Juvan–Mohar best on random graphs, Mesh
on finite-element graphs, Degree on VLSI and geometric graphs; Edges always
dominates Path and Gomory–Hu. Petit 2011 (held) Table 11: on `gd96a` the best
of these is 5,155 against an upper bound of 95,263 and Caprara et al.'s
76,253. **Caprara, Letchford & Salazar-González 2011** (held; read whole in
`layout_lp_literature.md` §1): the decorous LP from counting inequalities.
**Lin & Yuan 1994**: profile lower bounds and exact values on special graphs
(`P(K_{m,n}) = mn + m(m−1)/2`).

*Transfer.* Every one of these arrives at pathwidth through `MinLA ≤ nΔ·pw` or
`profile ≤ (n − 1)·pw`; `layout_lp_literature.md` §3.3 computed the MinLA
route at below 3 on `Random-125-125-4-1_0` (optimum 57) even with the exact
MinLA. The profile route is sharper and is still the uniform-`μ` Lagrangian:
`Σ_t B_σ(t) ≥ Σ_t Φ(t)` gives `pw ≥ ⌈(1/(n−1)) Σ_t Φ(t)⌉ ≤ L(G)`. The Degree
method's per-vertex counting is the one idea without a max-objective form,
and `layout_lp_literature.md` §1.4 already says why. Covered.

## 5. Treewidth

The families are tabulated with their Mycielski values in
`pathwidth_lower_bounds_survey.md` §1 (rows 1–11, 15) from the held
Bodlaender–Koster TR; all are `≤ tw + 1` and nothing since 2011 changes that:
Gima et al. 2025 and Chen, Wu & Li 2027 (spectral, listed), Tamaki 2022
(certified minors with lift; held; our family M is the pathwidth version,
searched, and the lift's guidance by safe minimal separators does not
transfer since pathwidth has no safe separators), Harvey & Wood, Kozawa et
al., Kaul (special families, held). Three items the brief named:

- **"via matching"**: LBP / LBP+ of Clautiaux et al. 2003–2004 (listed)
  strengthens the improved-graph rule with vertex-disjoint paths found by
  max-flow; `pathwidth_lower_bounds_survey.md` §2.1 proves the common-neighbour
  lemma for pathwidth, but the bound it feeds (MMD+, MCSLB) is a treewidth
  bound. We found no treewidth lower bound built on a matching as such.
- **"via 2-connected components"**: treewidth is the maximum over blocks, and
  Bodlaender & Koster 2006 (safe separators) extend this to clique and
  almost-clique minimal separators. For pathwidth this is false already on
  trees (`pw(T)` is not the maximum over edges); the pathwidth statement is
  the branch lemma (three branches of width `k` at a cut vertex or linked
  separator force `k + 1`), family B, which closes nothing on the residual
  (`obstruction_search.md` §0.5) — the census of `blockage_class.md` §3 says
  why: branching is the obstruction on 47 of 14,975 small graphs with
  `pw > tw`.
- **Brambles** (Seymour & Thomas 1993; Bodlaender, Grigoriev & Koster 2008):
  the pathwidth dual is the blockage, Appendix F; connected frames are blind
  to `pw > tw` (proved there), and the compact class's ceiling is `tw` on
  14,915 of 14,975 census graphs.
- **PACE 2017** (Dell et al. 2017, listed): Track A exact treewidth (Larisch &
  Salfelder's `tdlib` first, Tamaki's PID), Track B heuristic, Track C minimum
  fill-in; **no lower-bound track**. PACE 2026 (maximum agreement forest) is
  the first iteration with one, on an unrelated problem. The only solver that
  ships a lower-bound certificate is Tamaki 2022 (a minor of ≤ 49 vertices,
  `pathwidth_np_conp.md` §4).

## 6. Tree-depth

**Direction.** `pw ≤ td − 1`; `td ≤ tw·log₂ n` (Bannach & Berndt 2022 p. 4).
A tree-depth lower bound `L` gives `pw ≥ L/log₂ n`: nothing usable. The PACE
2020 exact-track solvers are read for technique only.

- **tdULL** (Brokkelkamp, van Venetië, de Vries & Westerdiep 2020, §2.1.1):
  "the only sure way to find a lower bound is to recur on all possible
  separators"; minor monotonicity is the tool; the *core* (iteratively delete
  vertices of at most the minimum degree) is solved as a subgraph bound; if
  the core is empty, a contraction "of the edge between a vertex of minimal
  degree and a neighbouring vertex for which the overlap of common neighbours
  is minimal" — our `least-c` rule, the one `_contraction_degeneracy` uses.
  Classes: peel (`spectral_bound.md`'s `peel` family) and minor (M).
- **SMS** (Korhonen 2020, §3.3): bounds cached per induced subgraph `G[X]`;
  a subset-preserving hash to find `X' ⊂ X` with the best known bound; MMD+
  clique minors (Bodlaender & Koster [3]); a DFS for long paths and cycles
  (tree-depth only: `td(P_n) = ⌈log₂(n + 1)⌉` while `pw = 1`); and "a graph
  isomorphism hashtable which finds already processed induced subgraphs
  `G[X']` that are isomorphic to `G[X]` and applies the lower bounds of
  `G[X']` to `G[X]`". The last is the one idea not in our search: our memo
  stores *sets*; two closed sets whose residual graphs (with their boundary
  marked) are isomorphic are refuted separately. `ml_nature.md` §13 measured
  that relabelling moves node counts by 2–6 % at the median, which bounds
  how much tie-break symmetry there is, not how many isomorphic residuals a
  single run visits. §9.3 states the measurement.
- **Bute / Bute-Plus** (Trimble 2020): positive-instance-driven DP over sets
  that admit an elimination tree of bounded depth, with a trie and a
  domination rule; Bannach & Berndt 2022 (held) is the general PID framework
  and covers pathwidth. Not a lower-bound technique.

## 7. Linear-width, mixed search, and the edge-lattice Harper bound

**Direction.** `pw ≤ lw ≤ pw + 1` for `lw ≥ 1`; mixed search is in the same
band. No lower-bound literature specific to either was found (the searches
returned exact algorithms — Kobayashi & Nakahata 2021 `O*(2ⁿ)`, held — and
linear *rank*-width obstructions).

**The candidate.** Linear-width is the least over edge orderings of the most
vertices that are incident to a placed and to an unplaced edge. Its Harper
bound is immediate: for `g(s) = min_{|F| = s} #{v : v meets F and E ∖ F}`,
`lw ≥ max_s g(s)`, hence `pw ≥ max_s g(s) − 1`. This is a different
relaxation — a minimum over the edge lattice rather than the vertex lattice —
and the only candidate in this survey that is none of our families. Validity
rests on Fomin & Thilikos's upper half, so the loss of one is unavoidable.

**Worked example** (`reports/scratch/complex_lb_layout/ex8.py`). On the
6-vertex graph `E~a?` (a `K_4` on `{0,1,2,3}` with two pendants at `0`):
`pw = 3`, `lw = 3`, `tw = 3`. Harper's vertex bound is `1`: the hub `0` is a
cut vertex adjacent to everything, so every `t`-set that avoids it has outer
boundary `{0}`, and `Φ(t) = 1` at every level. The edge bound is `3`: at
`s = 4` every set of four edges leaves at least three vertices meeting both a
placed and an unplaced edge (four edges inside the `K_4` leave the two
untouched vertices of the `K_4` and the hub split; four edges at the hub leave
three `K_4` vertices split; a mixture leaves the hub and two more). So
`max_s g(s) − 1 = 2 > 1 = Harper`. And `tw = 3` certifies more than both: the
win is on a graph where the clique bound already closes.

**Census** (`edge_harper.py`, `census8.py`; exact `pw` by the subset DP, `lw`
by a DP over edge subsets, both Harper profiles by enumeration; no violation
of `g ≤ lw`, `Φ ≤ pw`, `pw ≤ lw` on any graph):

| graphs | count | `lw = pw + 1` | `max_s g(s) − 1 > Harper` | `… > max(Harper, tw)` |
|---|---:|---:|---:|---:|
| connected, 2–7 vertices (atlas) | 995 | 132 | 8 | 0 |
| connected, 8 vertices, `m ≤ 16`, `pw > tw` | 273 | — | **0** | **0** |

The eight wins are `K_4` or `K_5` plus pendants (`pw = tw`), listed by `ex8.py`
with their graph6 strings. On every 8-vertex graph with `pw > tw` — the only
graphs where a new bound is needed — the edge bound minus one never exceeds
the vertex bound. **Verdict: dead at the sizes where it can be computed
exactly; no corpus test is warranted.** The intuition the census confirms:
walking the edge lattice along a vertex prefix adds the edges of one vertex at
a time and can raise the split count by at most one over the prefix's
boundary, which is the `+1` of Fomin & Thilikos, and the loss of one in the
transfer gives it back. Cost of the exact bound, had it survived: a minimum
over `C(m, s)` edge sets per level, the same NP-hard inner problem as Harper's
on a lattice 3–6 times larger on MOSP graphs (`m / n` of 3–6 on the Chu &
Stuckey classes). Not searched for in the literature specifically, not claimed.

## 8. Directed pathwidth

`dpw(Ĝ) = pw(G)`. Coudert, Mazauric & Nisse 2016 (held): the branch and bound
prunes on the prefix cost and a prefix table and uses no lower bound; their
closing paragraph (lines 1109–1112 of the held copy) asks for "lower bounds for
pathwidth that are not lower bounds for treewidth", which `pathwidth_lower_bounds_survey.md`
§0 and family M answer. Kitsunai et al. 2016 (held): the `O(1.89ⁿ)` DP over
commitments, no bound. Yang & Cao 2008 (directed vertex separation = directed
pathwidth; not held) is the equivalence only. Nothing to transfer.

## 9. The genuinely different items, with kill criteria

### 9.1 Edge-lattice Harper — measured dead (§7)

Kill criterion stated before the census: dead if `max_s g(s) − 1 ≤ max(Harper, tw)`
on every graph with `pw > tw` to 8 vertices. Met: 0 of 273. Not proposed for
the corpus.

### 9.2 The `L(G)` ceiling on the residual — closes every LP/SDP route at once

`chain_lp.md` §5 proves every relaxation of the layout hull in the chain
variables, LP or SDP, has value at most `L(G) = max_μ min_σ Σ_t μ(t) B_σ(t)`,
and bounds `L` from above by the mixture LP over any pool of layouts. On the
11 residual instances (`obstruction_search.md` §0.8 item 1) the record floor is
1–4 below the optimum. **Measurement**: the mixture upper bound `U(G)` on `L`
from the witness ordering and a few hundred heuristic layouts
(`learning/chain_lp.py --stage ceiling`, minutes per instance at 100–125
customers). **Kill**: if `⌈U⌉ ≤ record floor` on all 11, rows 8, 12, 15, 16
and Mallach's `LP_L` are closed on the residual by one number each, and the
SDP of Gaar et al. need never be built for pathwidth. Expected: met, since at
30–50 the mixture bound never came down to Harper but the record floor there
is the optimum; on the residual the floor is the searched minor, far above
Harper. Not run here (the brief forbids runs; the data under
`reports/scratch/chain_lp/` would be read, not re-solved).

### 9.3 Isomorphic residual states (SMS's isomorphism hashtable)

**Statement.** In the customer search, two closed sets `S, S'` with
`G[V ∖ S] ≅ G[V ∖ S']` by an isomorphism carrying the boundary `N(S) ∖ S` onto
`N(S') ∖ S'` have the same residual problem; a refutation of one refutes the
other. Our memo keys on the set, so both are refuted.
**Measurement**: over the §32 certificates at 41–75 customers (141 verified
instances), canonicalise each visited residual graph with its boundary marked
(`learning/canonical.py`'s nauty certificates, seconds per state) and count
the share of states whose canonical form was seen earlier in the same run.
**Kill**: below 10 % of states on the median instance, the technique cannot
pay for the hash. **Expected**: met on Chu & Stuckey random instances (no
twins by construction), not met on the Harvey and Simonis families, which are
already cheap. Cost: hours, read-only.

### 9.4 Already proposed elsewhere, repeated for completeness

Mallach's `LP_L` on the 64 (`layout_lp_literature.md` §0 item 3, one
core-hour, expected dead); §9.2 would make it unnecessary.

## 10. Regenerate

    cd reports/scratch/complex_lb_layout && python3 -I edge_harper.py      # atlas census, ~2 s
    python3 -I ex8.py                                                      # the eight graphs, ~10 s
    nauty-geng -c 8 -q | python3 -I census8.py                             # 8 vertices, m ≤ 16, pw > tw, ~6 min

Needs `networkx` and `nauty-geng`. The scratch directory is not committed.

## 11. Literature used

Held in `literature/`: Harper 1966; Bodlaender 1998 (Thms 44–49, pp. 23–24);
Díaz, Petit & Serna 2002 (Lemma 2.4 p. 317; §9 pp. 338–340); Petit 2011
(Table 11); Helmberg et al. 1995; van Dam & Sotirov 2015 (§1, §3); Caprara,
Letchford & Salazar-González 2011; Coudert 2016; Coudert, Mazauric & Nisse
2016; Kitsunai et al. 2016; Kobayashi, Komuro & Tamaki 2014; Kobayashi &
Nakahata 2021; Fomin & Thilikos 2006 (Lemma 2); Bannach & Berndt 2022 (p. 4);
Bodlaender 2024 (Lemma 3); Bodlaender & Koster 2010 TR; Bodlaender, Grigoriev
& Koster 2005 TR; Tamaki 2022; Gima et al. 2025; Proskurowski & Telle 1999;
Chandran & Kavitha 2006; Bansal & Katzelnick 2023.

Read from open copies, not downloaded into `literature/` (recorded in
`literature/MISSING.md` under *Lower bounds: the linear-layout neighbours of
the complex (2026-11-11)*): Bermond, Cosnard, Coudert & Havet 2025 (HAL);
Gaar, Puges & Wiegele 2024 (arXiv); Kloeckner 2010 (arXiv); Martí, Pantrigo,
Duarte & Pardo 2013 (author preprint); Benadé & Hooker 2019 (arXiv, for the
Chvátal, Blum et al. and Caprara–Salazar-González bounds); Rendl, Sotirov &
Truden 2021 (arXiv); Petit 2003 (preprint); Brokkelkamp et al. 2020, Korhonen
2020, Trimble 2020 (LIPIcs / arXiv). Cited from abstracts or from the papers
above, not read: Chvátal 1970; Chinn et al. 1982; Blum et al. 2000; Haemers
1995; Povh & Rendl 2007; de Klerk, Nagy & Sotirov 2013; Caprara &
Salazar-González 2005; Del Corso & Manzini 1999; Martí, Campos & Piñana 2008;
Lim, Rodrigues & Xiao 2007; Cygan & Pilipczuk 2010; Lin & Yuan 1994;
Adolphson & Hu 1973; Kaplan & Shamir 1996; Takahashi, Ueno & Kajitani 1995;
Thomas 1996; Bodlaender & Koster 2006; Bodlaender 1986; Yang & Cao 2008;
Dell et al. 2017.
