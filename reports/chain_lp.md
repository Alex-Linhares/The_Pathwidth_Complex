# An LP relaxation of the nested-chain encoding, with Harper's inequalities

*2026-11-10, one session. Code: `learning/chain_lp.py` (the IP, the LP, four cut
families, the Lagrangian ceiling); tests `tests/test_chain_lp.py` (49). Data
under `reports/scratch/chain_lp/`. Nothing re-solved; `solutions/` read only
(certified optima and witness orderings); about 2.5 core-hours, nice 19, at most
8 cores. Literature: `literature/MISSING.md`, "LP bounds for layout problems".*

## 0. Summary

**The question.** Pathwidth is an integer, so a fractional lower bound of 19.1
proves 20. The nested-chain encoding of vertex separation (`reports/checkpoint_relaxation.md`:
nested prefixes `S_1 ⊂ … ⊂ S_{n−1}`, `|S_t| = t`, boundary `≤ b` at every
level) is exact and graph-only. Its LP relaxation, strengthened by Harper's
inequalities `Σ_v s[v,t] ≥ Φ(t)` (valid: every `t`-prefix has boundary at least
`Φ(t) = min_{|S|=t} |N(S) ∖ S|`), was to be measured on the 64 bound-gap
instances at 30–50 customers where Harper's exact integer bound is below the
optimum, with the kill criterion: **dead if `⌈b*⌉` never exceeds Harper on any
of the 64 for any formulation**, alive if it does.

**The verdict: dead, by a two-line proof, and the measurement confirms the
proof to 1e-14.** The point `y[v,t] = t/n`, `s[v,t] = Φ(t)/n` satisfies every
constraint of the chain LP — size, nesting, every edge inequality (both sides
equal), and every Harper cut — with `b = max_t Φ(t)`; and every feasible point
has `b ≥ Σ_v s[v,t] ≥ Φ(t)`. So the LP with Harper cuts is *exactly* Harper's
bound, and without them exactly 0 (§2). The same point satisfies the three
further cut families we could prove valid (boundary persistence across levels,
the two upper bounds on `s`, and clique inequalities; §3), so every
formulation built here returns `max_t Φ(t)`: fractional relaxation decouples
the levels completely, and nothing in `(y, s)` that the uniform point
satisfies can recouple them. Mallach (2018) states the bare fact for the
position-based vertex-separation MIPs ("the lower bound … is zero for any
directed graph"); the Harper-cut form, and that it equals Harper exactly, we
found no prior statement of.

| formulation | LP optimum (proved) | on the 64: `⌈b*⌉ > Harper` | reaches the optimum |
|---|---|---|---|
| chain LP, no cuts | 0 | 0 of 64 | 0 |
| + Harper cuts | `max_t c(t)` = Harper | 0 of 64 | 0 |
| + persistence + upper bounds | Harper | 0 of 64 | 0 |
| + clique inequalities | Harper | 0 of 64 | 0 |

(§4 has the table with the per-instance values; the LP equals the per-level
floor maximum to solver precision on every instance.)

**What is checked.** (i) The integer program's optimum is the vertex
separation: proved (§1) and checked on every graph of the networkx atlas to 7
vertices against the subset DP, **1,253 of 1,253 agree**, with and without
every cut family. (ii) Every cut family is valid: proved (§3) and checked
against every layout of every atlas graph to 6 vertices (`n!` layouts each,
the exact `(y, s)` point of each layout satisfies every row) and by the IP
with all cuts still equalling the DP on all 1,253. (iii) The uniform point is
feasible for every formulation (a test), and the LP values on the 64 equal
`max_t c(t)` to 1e-13 (§4). (iv) Every certified bound used is below the
certified optimum (`provenance` of every one of the 64 is `certified:*`;
a value above would have stopped the run).

**The ceiling of the route, which is the finding worth keeping (§5).** The
only link between `b` and the chain is per level, `b ≥ Σ_v s[v,t]`. For *any*
family of valid inequalities in `(y, s)` — up to the full integer hull
`conv{(y^σ, s^σ)}` over layouts `σ` — the LP equals
`min_λ max_t Σ_σ λ_σ B_σ(t)` over mixtures of layouts, and by LP duality

    L(G) = max_{μ ∈ Δ} min_σ Σ_t μ(t) B_σ(t),

the Lagrangian dual of `vs = min_σ max_t B_σ(t)`; `Harper ≤ L ≤ vs`. The route
can beat Harper on an instance only if `L(G) > Harper(G)` there. `L` is
computed exactly at `n ≤ 20` (cutting planes on `μ`, a subset DP as oracle)
and bounded above at any `n` by the mixture LP over a pool of layouts. **On
the atlas the ceiling is alive**: where Harper is short (516 graphs),
`L > Harper` on 489 and `⌈L⌉ = vs` on 443, `L` closing 38% of the gap on
average. **On the corpus** (§5): exact on the 1,189 corpus instances at 9–20
customers whose Harper value is below the optimum, `L > Harper` on **1,110**
(93%), `⌈L⌉ = vs` on **978** (82%), `L` closing 37% of the gap on average,
with an optimal `μ*` supported on a median of **two adjacent levels** (weights
½/½ or ⅓/⅔). At 30–50, mixtures of 500–600 heuristic layouts bound `L` from
above but never down to Harper (inconclusive on all 64), and a SAT refutation
of the **two-level sum** (`B(t_1) + B(t_2) ≤ 2H` has no nested solution) proves
`L ≥ H + ½`, hence `⌈L⌉ ≥ H + 1`, on **24 of the 64** (5 of 35 at Harper gap 1,
19 of 29 at gap ≥ 2; the refuting pairs at `0.53–0.61 n`; 200 s, no call
censored); undecided on 40. So the ceiling is above Harper on most gap
instances — but the distance between the brief's LP (Harper) and the ceiling
is the integer hull of two nested levels, and the only instrument that moves
an LP off Harper is the SAT refutation of that nested pair, which is the
checkpoint relaxation of `reports/checkpoint_relaxation.md` under another
name and already a bound proof by itself. The LP adds the rounding and
nothing else. No floor on record moves (all 64 were already certified at the
optimum by that study).

**Cost at 100–125** (§6): LP sizes and HiGHS times on two `Random-100-100-4`
instances and one `Random-125-125-4`, for the record; the value is Harper
there too.

## 1. The integer program and its exactness

Graph `G = (V, E)`, `n = |V|`, levels `t = 1 .. n − 1` (levels 0 and `n` have
empty boundary). Variables `y[v,t] ∈ {0,1}`, `s[v,t] ∈ [0,1]`, `b ≥ 0`:

    Σ_v y[v,t] = t                       (size)
    y[v,t] ≤ y[v,t+1]                    (nesting)
    s[v,t] ≥ y[u,t] − y[v,t]  ∀ uv ∈ E   (boundary; both orientations)
    Σ_v s[v,t] ≤ b                       (width)
    min b.

*Claim.* The optimum is `vs(G)`, the vertex separation (= pathwidth,
Kinnersley 1992; `MOSP = vs + 1`, `MOSPGraph.lean`).

*Proof.* Let `(y, s, b)` be feasible and integral in `y`; `S_t = {v : y[v,t] = 1}`.
Size and nesting give `S_1 ⊂ S_2 ⊂ … ⊂ S_{n−1}` with `|S_t| = t`, so each
`S_{t+1} ∖ S_t` is a single vertex and the `S_t` are the prefixes of a layout
`σ` (extend by the vertex left for position `n`). For `v ∉ S_t` with a
neighbour `u ∈ S_t`, the edge inequality gives `s[v,t] ≥ 1 − 0 = 1`, so
`Σ_v s[v,t] ≥ |N(S_t) ∖ S_t| = B_σ(t)` and `b ≥ max_t B_σ(t) = vs(σ) ≥ vs(G)`.
Conversely, for a layout `σ` with `vs(σ) = vs(G)`, set `y` to its prefix
indicators and `s[v,t] = 1[v ∉ S_t, N(v) ∩ S_t ≠ ∅]`; every edge inequality
holds (`y[u,t] − y[v,t] ≤ 1` and equals 1 only when `v` is such a boundary
vertex), and `b = vs(G)` is feasible. ∎

*Checked* (`--stage atlas`, `reports/scratch/chain_lp/atlas.csv`): every
graph of the networkx atlas (1,253 graphs on 0–7 vertices, connected or not)
through HiGHS (`scipy.optimize.milp`) against the subset DP of
`fixed_parameter_algorithm/pathwidth.py`: **0 disagreements**, with and
without the cut families of §3; 240 s on 4 cores.

## 2. The LP relaxation is Harper's bound, exactly

Relax `y ∈ [0,1]`. Let `c(t) ≤ Φ(t)` be any valid per-level floors and add
the Harper cuts `Σ_v s[v,t] ≥ c(t)`.

*Theorem.* The LP optimum is `max_t c(t)`. In particular the bare LP has
optimum 0 and the LP with exact Harper cuts has optimum `max_t Φ(t)`, Harper's
integer bound; `⌈b*⌉ = Harper` on every graph.

*Proof.* Lower bound: `b ≥ Σ_v s[v,t] ≥ c(t)` for every `t`. Upper bound: the
point `y[v,t] = t/n`, `s[v,t] = c(t)/n` for all `v`, `b = max_t c(t)` is
feasible — size `Σ_v t/n = t`; nesting `t/n ≤ (t+1)/n`; every edge inequality
reads `c(t)/n ≥ t/n − t/n = 0`; each Harper cut `Σ_v c(t)/n = c(t)`; width
`c(t) ≤ b`. ∎

The cut `Σ_v s[v,t] ≥ Φ(t)` is valid because every `t`-prefix of every layout
has boundary `≥ Φ(t)` (`EmptyPair.lean` has Harper's bound in layout form).
Where the per-level floors come from on the 64 (§4): the machinery of
`satisfiability/expansion_bound.py` — `f(k) = min_{|C|=k} |N[C]|` exact by
branch and bound to cap 12, giving the inner-boundary minimum
`Φ_in(i) = i − max{k : f(k) ≤ i}` exactly for `i < f(T+1)`, and the outer
boundary of a `t`-set is the inner boundary of its complement,
`Φ(t) = Φ_in(n − t)`; levels the cap does not reach get the trivial floor 0.
Branch and bound to cap 12 alone reaches the record's exact Harper value on
only 1 of the 64 (the record settled the deciding level by SAT with a DRAT
proof, `reports/obstruction_search.md`), and a first run with those floors
returned the floor maximum, 1–3 below Harper, exactly as the theorem says
(`reports/scratch/chain_lp/lp64_bbfloors_first_run.csv`). The floors used in
§4 join the record's settled levels (`03_sat/levels.csv`, an `unsat` row at
`(t, b)` proves `f(t) ≥ b + 1`; `record_levels`, `floors_from_levels`, with the
monotone closure filling only *below* a settled level) and reach the exact
Harper value on **64 of 64, never above it** (`floor_check.csv`). A first
draft of that merge put a floor of 17 on an instance of vertex separation 14
— it filled the levels between the cap and a settled level with the settled
value instead of the cap's — and was caught by exactly this comparison before
any LP ran on it; the test
`test_floors_from_all_exact_levels_equal_the_exact_profile` pins the corrected
rule to the exact profile.

Mallach (2018, *J. Discrete Algorithms* 52–53, abstract) states that the LP
relaxations of the position-based vertex-separation MIPs have lower bound
zero for every graph, and gives a linear-ordering-variable formulation whose
relaxation is non-zero whenever the pathwidth is; we do not hold the paper
and do not know whether that relaxation exceeds Harper anywhere
(`literature/MISSING.md`). The brief's precedents, Caprara & Salazar-González
(2005) for bandwidth and Caprara, Letchford & Salazar-González (2011) for
minimum linear arrangement, obtain their LP bounds from counting inequalities
on *position-distance* structure, which the chain has no variables for; both
are recorded as missing with links.

## 3. Four cut families, each valid, each satisfied by the uniform point

Validity means: for every layout `σ`, the exact point `(y^σ, s^σ, vs(σ))` of
§1 satisfies the inequality (so the IP's optimum is unchanged; a cut that
removed every optimal layout's point would raise it). Each family below is
proved and then checked on every layout of every atlas graph to 6 vertices
(`_all_layouts_satisfy`, all `n!` layouts) and by `IP with all cuts = DP` on
all 1,253 atlas graphs.

- **Harper** `Σ_v s[v,t] ≥ c(t)`, `c(t) ≤ Φ(t)`: §2. Uniform point: equality
  with `s = c(t)/n`.
- **Persistence** `s[v,t+1] ≥ s[v,t] − (y[v,t+1] − y[v,t])`. A boundary
  vertex at level `t` (outside `S_t`, neighbour inside) is at level `t+1`
  either the vertex that entered (`y` difference 1) or still outside with the
  same neighbour inside `S_{t+1} ⊇ S_t`, hence still boundary. Uniform point:
  `c(t+1)/n ≥ c(t)/n − 1/n`, i.e. `c(t+1) ≥ c(t) − 1`, which holds for
  `c = Φ` (remove a vertex from a `(t+1)`-set: the boundary grows by at most
  that vertex, so `Φ(t) ≤ Φ(t+1) + 1`) and for the floors used (they are
  `Φ_in` of complements, with the same property, or 0). Summed over `v` it
  gives the level coupling `Σ_v s[v,t+1] ≥ Σ_v s[v,t] − 1` the brief asked
  about; that is as far as a proof goes — the boundary can grow by `deg(w) − 1`
  in one step, and a lower bound tighter than `−1` on the drop is false
  (`K_{1,k}`: centre first, boundary `k`, then `k − 1`, …).
- **Upper bounds** `s[v,t] ≤ 1 − y[v,t]` and `s[v,t] ≤ Σ_{u ∈ N(v)} y[u,t]`:
  a boundary vertex is outside and has a neighbour inside. Uniform point:
  `c(t)/n ≤ 1 − t/n` ⇔ `c(t) ≤ n − t` (a boundary lies outside the set), and
  `c(t)/n ≤ deg(v)·t/n`, which fails only for `deg(v) = 0` at levels with
  `c(t) > 0`; then put the mass `c(t)/n` on the non-isolated vertices instead
  (`c(t) ≤ n − t − #isolated` still), and the LP value is unchanged. In the
  measurement no instance has an isolated customer.
- **Clique** for a clique `K`, `u ∈ K`: `Σ_{v ∈ K} s[v,t] ≥ |K|·y[u,t] − Σ_{v ∈ K} y[v,t]`.
  If `u ∈ S_t`, every `v ∈ K ∖ S_t` is adjacent to `u` and so a boundary
  vertex: `Σ_K s ≥ |K ∖ S_t| = |K| − Σ_K y`. If `u ∉ S_t` the right side is
  `≤ 0`. Uniform point: right side `|K| t/n − |K| t/n = 0`.

So every formulation here has LP optimum `max_t c(t)` (the theorem of §2
applies verbatim with the enlarged constraint set, the uniform point being
feasible for it). This is why the measurement of §4 is a confirmation and not
an experiment.

**Why no `(y, s)`-cut the uniform point violates would help either, in
general.** The relevant object is not the uniform point but the whole set of
fractional chains, and §5 gives the exact value of the LP under the *best
possible* `(y, s)`-cuts.

## 4. The measurement on the 64

Population: the 64 instances of `reports/scratch/checkpoint/refine/refine.csv`
(corpus, 30–50 customers, exact Harper below the certified optimum; 1 at 30,
19 at 40, 44 at 50), each with its certified optimum re-read from
`solutions/` (provenance `certified:refutation` on all 64) and the best floor
on record (`reports/scratch/obstruction_search/08_map/`: `floor0`, the
searched Harper and minor floors). Four LPs per instance through HiGHS
(`scipy.optimize.linprog`), `--stage lp64`, 4 workers.

Units: `vs` (pathwidth); the optimum is `vs + 1`. `H` is the record's exact Harper value, `harper_ref − 1`.

| n | instances | floors reach H | LP, no cuts (max) | max \|LP+Harper − H\| | max \|LP+all cuts − H\| | `⌈b*⌉ > H` (any formulation) | reaches optimum | variables | rows base / all cuts | HiGHS s, Harper / all (max) |
|---|---|---|---|---|---|---|---|---|---|---|
| 30 | 1 | 1 | 0 | 1.8e-15 | 3.6e-15 | 0 | 0 | 1741 | 8902 / 15477 | 0.2 / 1.4 (max 1) |
| 40 | 19 | 19 | 0 | 8.9e-15 | 2.7e-14 | 0 | 0 | 3121 | 10802 / 20378 | 0.5 / 2.2 (max 5) |
| 50 | 44 | 44 | 0 | 2.1e-14 | 1.4e-13 | 0 | 0 | 4901 | 17296 / 31557 | 0.8 / 3.9 (max 29) |

The Harper gap `vs − H` on the 64: 1 on 35, 2 on 22, 3 on 6, 4 on 1. The best floor on record (the searched minors of `reports/obstruction_search.md`) is above Harper on 19 of the 64 and equals the optimum on 2; the LP is below that floor wherever it is above Harper. Per-instance values: `reports/scratch/chain_lp/lp64.csv` (`lp`, `lp_harper`, `lp_harper_pu` = Harper + persistence + upper bounds, `lp_all` = + cliques, each with its seconds; the four values agree to 1e-13 on every instance). The clique family adds 27–38 maximal cliques of size ≥ 3 per instance and doubles the row count; the persistence family is the only one that changes HiGHS's path at all (it is where the seconds go), and none changes the value.

**Kill criterion, applied**: `⌈b*⌉ > Harper` on 0 of 64 for every formulation. **Dead**, as §2 proved before the run.

## 5. The ceiling of the route: the Lagrangian value

*Theorem (ceiling).* Let `P ⊇ conv{(y^σ, s^σ) : σ a layout}` be any polyhedron
cut from `[0,1]^{2n(n−1)}` by inequalities valid for the layouts' exact points,
and `LP(P) = min{b : (y, s) ∈ P, Σ_v s[v,t] ≤ b ∀t}`. Then

    LP(P) ≤ LP(conv) = min_{λ ∈ Δ(layouts)} max_t Σ_σ λ_σ B_σ(t) = max_{μ ∈ Δ(levels)} min_σ Σ_t μ(t) B_σ(t) =: L(G),

and `Harper(G) ≤ L(G) ≤ vs(G)`.

*Proof.* Minimising over a larger set gives a smaller value; on `conv`, every
point is a mixture `λ` of layouts' exact points and `Σ_v s[v,t]` is linear, so
`LP(conv)` is the mixture formula; the equality with the `max_μ min_σ` form is
LP duality for the finite zero-sum game with payoff matrix `B_σ(t)`. A point
mass `μ = δ_{t*}` gives `min_σ B_σ(t*) = Φ(t*)`, hence `L ≥ Harper`; every
`B_σ(t) ≤ vs(σ)` and the optimal layout has `vs(σ) = vs(G)`, hence `L ≤ vs`. ∎

So the route — any LP whose only link to `b` is the per-level width
constraint — certifies at most `⌈L(G)⌉`, whatever cuts are found, and the
brief's cuts certify `Harper`. `L` is the Lagrangian dual of
`vs = min_σ max_t B_σ(t)` (dualise the `n − 1` constraints `B_σ(t) ≤ b`), and
`vs − L` is its duality gap.

**Computing it.** For `μ` fixed, `min_σ Σ_t μ(t) B_σ(t)` is a shortest path
from `∅` to `V` in the subset lattice with node weight `μ(|S|)·|N(S) ∖ S|`
(`weighted_layout`, a vectorised subset DP, `n ≤ 20`, 1–5 s). `L` itself by
cutting planes on `μ`: the restricted game on a pool of layouts gives `μ` and
an upper bound `z`, the DP's best response a lower bound `v`; stop at
`z − v ≤ 1e-7` (`lagrangian_exact`; typically 2–10 iterations). Checked
against the LP over *all* `n!` profiles on a 6-vertex graph and against
brute-force enumeration of the weighted problem (tests). Above 20 vertices
only the upper bound is computed: the mixture LP over a pool of layouts
(`mixture_upper`: greedy cheapest-boundary layouts with random tie-breaks and
their reversals, each start vertex, a one-vertex-move descent on the best
`2n`, and the four layouts the certified witness ordering induces); a pool
whose mixture has `max_t` average boundary `≤ Harper` proves `L = Harper`.

**Exact, `n ≤ 20`.** Population: every corpus instance at `n ≤ 20` whose recorded Harper value (`harper12`, ledger map) is below the optimum — 1,189 instances (5 at 9, 345 at 10, 295 at 15, 532 at 20, 12 at other sizes), Harper recomputed exactly from the subset tables (below `vs` on all 1,189); plus the atlas. `L` to 1e-7 (the cutting-plane gap `z − v` closed to 2e-14 on every instance; median 1 iteration, max 69; median 0.3 s, max 35 s).

| population | instances with Harper < vs | mean gap `vs − H` | `L > H` | `⌈L⌉ = vs` | mean (L − H)/(vs − H) | median | method |
|---|---|---|---|---|---|---|---|
| atlas, all graphs to 7 vertices with Harper < vs | 516 | 1.10 | 489 | 443 | 0.38 | 0.50 | exact |
| corpus, n = 9 | 5 | 1.20 | 4 | 3 | 0.40 | 0.50 | exact |
| corpus, n = 10 | 345 | 1.08 | 328 | 304 | 0.39 | 0.50 | exact |
| corpus, n = 13 | 1 | 1.00 | 1 | 1 | 0.50 | 0.50 | exact |
| corpus, n = 14 | 3 | 1.33 | 3 | 2 | 0.27 | 0.36 | exact |
| corpus, n = 15 | 295 | 1.08 | 287 | 264 | 0.40 | 0.50 | exact |
| corpus, n = 17 | 2 | 1.50 | 2 | 1 | 0.40 | 0.40 | exact |
| corpus, n = 18 | 3 | 1.00 | 3 | 3 | 0.40 | 0.50 | exact |
| corpus, n = 19 | 3 | 1.67 | 2 | 1 | 0.30 | 0.41 | exact |
| corpus, n = 20 | 532 | 1.17 | 480 | 399 | 0.34 | 0.33 | exact |
| corpus, 9–20 together | 1189 | 1.12 | 1110 | 978 | 0.37 | 0.45 | exact |

By gap on the corpus: gap 1: L > H on 977 of 1054, L closes 0.37 of it; gap 2: L > H on 122 of 124, L closes 0.35 of it; gap 3: L > H on 10 of 10, L closes 0.37 of it; gap 4: L > H on 1 of 1, L closes 0.42 of it. On the 79 instances with `L = H` exactly, Harper is already the Lagrangian value and no `(y, s)`-cut can move the LP.

The optimal `μ*` is sparse: on a sample of 56 instances at `n = 20` with `L > H` its support is a median of **2 levels** (2–5), adjacent or two apart, with weights ½/½ or ⅓/⅔ (the `L − H` values are ½, ⅓, ¼, …), at outer-boundary sizes `0.05–0.4 n` on these dense Harvey–Simonis graphs. So where the ceiling exceeds Harper it does so by a *two-level* argument: no layout has both `B(t_1) ≤ H` and `B(t_2) ≤ H` *and* the two boundaries summing to `≤ 2H` — the nesting between two consecutive sizes, which is exactly what §5 of `reports/checkpoint_relaxation.md` found the compact certificates made of.

**At 30–50, the mixture upper bound is inconclusive on all 64.** Pools of 520–600 layouts (greedy with random tie-breaks and reversals, one-move descent, the four witness layouts; 40 of the 64 pools contain a layout of width `vs`) leave `L_upper − H` at a median of 1.00 (max 3.00); the mixture's support is 1–10 layouts. An upper bound from a heuristic pool cannot prove `L = H`; it can only do so when the pool happens to contain the equilibrium mixture, and the pools do not (`ceiling.csv`, columns `L_upper`, `L_upper_witness`, `best_single`).

**At 30–50, a lower bound on `L` by SAT: the two-level sum (`--stage pairs`).** The shape of `μ*` at `n = 20` suggests the witness: if for some pair of sizes `t_1 < t_2` no nested pair `S_{t_1} ⊂ S_{t_2}` has boundary *sum* `≤ 2H`, then with `μ = (½, ½)` on those levels every layout scores `≥ H + ½`, so `L ≥ H + ½` and `⌈L⌉ ≥ H + 1`. One CaDiCaL call per pair on the checkpoint encoding with a single totalizer over both interiors (`pair_sum_cnf`, inner-boundary units, the reversal mapping it to the outer form; checked against brute force on every pair and weight of two small graphs, and every SAT answer re-verified from the masks). Pairs `t_2 − t_1 ≤ 3` scanned from the middle (`0.6 n`) outward, at most 120 calls per instance, 10⁶ conflicts per call, first UNSAT stops; 64 instances, 200 s on 4 cores, **no call censored** (`pairs.csv`).

| Harper gap `vs − H` | instances | `L ≥ H + ½` proved | calls, median | seconds, median |
|---|---|---|---|---|
| 1 | 35 | 5 | 120 | 14.4 |
| 2 | 22 | 13 | 17 | 4.4 |
| 3 | 6 | 5 | 9 | 2.8 |
| 4 | 1 | 1 | 4 | 3.0 |

| n | instances | proved |
|---|---|---|
| 30 | 1 | 1 |
| 40 | 19 | 9 |
| 50 | 44 | 14 |

**Proved on 24 of 64; undecided on 40** (undecided means no pair in the window refuted, not that `L = H`: `μ*` may need three levels, weights ⅓/⅔, or sizes outside `t_2 − t_1 ≤ 3`). Where it is proved, the refuting pair sits at `0.53–0.61 n` (inner units; `t_2 − t_1` = 1 on 11, 2 on 8, 3 on 5) — the window where §5 of `reports/checkpoint_relaxation.md` found the compact certificates. Examples: `Warwick 1299: balanced orders, 6 orders per product` (n = 30, H = 9, vs = 11) at sizes 17, 18; `Random-40-40-2-4_0` (n = 40, H = 5, vs = 6) at sizes 21, 24; `p1540n10_0` (n = 40, H = 4, vs = 7) at sizes 21, 22; `p1540n3_0` (n = 40, H = 4, vs = 6) at sizes 23, 24; `p2040n4_0` (n = 40, H = 6, vs = 8) at sizes 20, 23; `p2040n5_0` (n = 40, H = 6, vs = 7) at sizes 23, 24. On the 5 proved gap-1 instances `⌈L⌉ = vs`; on 10 of the 24, `⌈L⌉ + 1` is above the best floor the obstruction search left on record (`08_map`), which is a statement about the ceiling, not a new floor: a two-level sum refutation is itself a certificate `vs ≥ H + 1` (both boundaries `≤ H` would sum to `≤ 2H`), i.e. a weaker-constraint form of the checkpoint pair relaxation, and every one of the 64 was already certified at its optimum by the full chain or the refinement of that study. Nothing on record moves.

**What the ceiling says.** The LP route's best conceivable value is `L`; `L > Harper` on 93% of the small gap instances and on at least 24 of the 64 at 30–50, usually by a *two-level* argument; but the only way found to move an LP off Harper is to hand it that two-level fact, and the fact is established by a SAT refutation of a nested pair — the checkpoint relaxation under another name. A cut strong enough to move the chain LP is itself a bound proof, and the LP then returns it rounded; it contributes the rounding and nothing else.

## 6. Cost at 100–125

Three residual instances (`reports/obstruction_search.md`, the dense shoulder), the LP with Harper cuts from the cap-12 floors alone (no SAT-settled levels exist at these sizes, so the floor maximum is below the record's Harper; the value is the floor maximum regardless, by §2). One core, HiGHS dual simplex, nice 19.

| instance | n | edges | optimum | max per-level floor (vs units) | LP with Harper cuts | variables | rows | seconds |
|---|---|---|---|---|---|---|---|---|
| Random-100-100-4-1_0 | 100 | 788 | 46 | 28 | 28.000 | 19,801 | 166,059 | 42 |
| Random-100-100-4-2_0 | 100 | 952 | 50 | 34 | 34.000 | 19,801 | 198,538 | 138 |
| Random-125-125-4-1_0 | 125 | 1063 | 57 | 29 | 29.000 | 31,001 | 279,285 | 126 |

The LP is affordable at 125 (31,001 variables, 279,285 rows, 2 minutes) and returns the floor maximum to 1e-13. The cost of the route at 100–125 is therefore not the LP; it is that the LP proves nothing the floors did not. Were cuts reaching the chain's integer hull ever found, the binding cost would be theirs, and §5 says what they could buy at most: `⌈L⌉`.

## 7. Verdict

- **The brief's route is dead, by proof and by measurement.** The chain LP
  with Harper cuts equals `max_t Φ(t)` on every graph (§2: the uniform point
  `y = t/n`, `s = Φ(t)/n`); bare, it is 0. Every provable cut family tried
  (persistence, the two upper bounds, cliques) is satisfied by the same point
  (§3). On the 64 gap instances at 30–50, `⌈b*⌉ > Harper` on 0 of 64 for every
  formulation, the LP values matching the per-level floor maximum to 1e-13
  (§4). The kill criterion, written before the run, is met. Mallach (2018)
  states the zero for the position-based MIPs; the Harper-cut identity we
  found no prior statement of.
- **The exact statements are checked, not trusted**: IP = vertex separation
  on all 1,253 atlas graphs, with and without cuts; no layout of any atlas
  graph to 6 vertices violates any cut; the merged Harper floors equal the
  record's exact values on 64 of 64 and exceed none; every certified optimum
  read from `solutions/` has provenance `certified:refutation`; one bug in the
  floor merge (a floor of 17 on a graph of vertex separation 14) was caught
  by the floor-against-record comparison before any LP used it (§2).
- **The ceiling is the result to keep (§5).** Any LP whose only link to `b`
  is the per-level width constraint certifies at most `⌈L(G)⌉`, `L` the
  Lagrangian value of `min_σ max_t B_σ(t)`, whatever cuts are found in
  `(y, s)`. `L` is exact at `n ≤ 20` (a subset DP as oracle, cutting planes on
  `μ`): above Harper on 1,110 of 1,189 corpus gap instances, rounding to `vs`
  on 978, by a two-level `μ*`; at 30–50 it is proved above Harper on 24 of
  the 64 by a two-level SAT refutation and undecided on 40. The ceiling is
  therefore *not* Harper — the fractional relaxation is what decouples the
  levels, not the chain — but reaching it needs the integer hull of two
  nested levels, and the instrument that establishes that hull's facts is the
  SAT call of the checkpoint relaxation, already a bound proof. An LP sits
  between a fact it cannot find and a rounding it does not need.
- **Not done, and not proposed**: cuts in `(y, s)` beyond the four families;
  a lower bound on `L` with three-level or unequal weights on the 40
  undecided instances (cheap: the same encoding with weights, `pair_sum_cnf`
  takes them); a Lean statement of the ceiling theorem (one minimax
  argument). None would change the verdict on the route: each is a SAT
  refutation of a nested sub-chain, which `reports/checkpoint_relaxation.md`
  measured already and found to be the exact problem localised.
- **Cost at 100–125** (§6): 2 minutes per LP at 125 vertices; affordable, and
  worthless there for the same reason.
