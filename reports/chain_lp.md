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
satisfies can recouple them. Mallach (2018, Theorem 4.1, p. 159) states the
bare fact for his `MIP_S`, which *is* this chain IP (nesting, size and the edge
inequality), with the uniform point `p/n` as the witness — the paper is held
(`literature/mallach_2018_...pdf`); the Harper-cut form, and that it equals Harper exactly, we
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
there too. **§7 (owner's follow-up)**: the two-level sum aimed at the floor on
the record's 11 open instances — 66 calls at `0.52–0.61 n`, all sat, none
censored, no floor rises; a high-window pass stopped after two hours with its
last calls unanswered (pysat's CaDiCaL ignores the time cap), undecided. **§8**: the mixture upper bound `U` on the ceiling is `vs` or within a unit of it on all 11 (closes nothing), and 41 two-level calls at the sizes its `μ` weights, under a 2M-conflict budget, answer 24 sat and 17 censored, 0 unsat: no floor rises.

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

Mallach (2018, *J. Discrete Algorithms* 52–53, Theorem 4.1 — the paper is held)
states that the LP relaxation of his `MIP_S`, the chain model itself, has lower
bound zero for every graph (the position model likewise), and gives a linear-ordering-variable formulation whose
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

## 7. The two-level sum on the record's 11 open instances (owner's follow-up, 2026-11-10)

*Regenerate: `nice -n 19 python -m learning.chain_lp --stage residual --workers 4` (the first window; 166 s wall on 4 cores) and `… --stage residual --window high` (the second; stopped by the coordinator after two hours, see below). Data `reports/scratch/chain_lp/residual/residual.csv`, `residual_high.csv`, `harness_validity.csv`; logs `reports/scratch/chain_lp/residual_run.out`, `residual_high_run.out`.*

**The question.** §5's two-level sum proved `L ≥ H + ½` on 24 of the 64 at 30–50 with pairs at `0.53–0.61 n`. The owner asked for the same refutation on the 11 instances `reports/obstruction_search.md` leaves open (`Random-100-100-4-1/3`, `Random-125-125-4-1..4`, `Random-125-125-6-2..5`, and the one ridge instance among them, `Random-125-125-2-2_0`; best floors 1–4 below the certified optimum), aimed at the **floor**: with `F` the best floor on record in `vs` units (optimum units minus one), a call asks for a nested pair `S_{t_1} ⊂ S_{t_2}` with inner boundaries summing to `≤ 2F` (`≤ 3F` for weights (1, 2)); UNSAT would prove every layout has a boundary `≥ F + ½` at one of the two sizes, hence `vs ≥ F + 1` and `optimum ≥ best + 1` — a floor that rises. Harper's exact value is not settled at these sizes; the table gives the record's proved floor and ceiling (`e_floor`, `e_ceiling`, optimum units; the ceiling is a found set and is below the optimum on all 11), and `2F ≥ 2(e_ceiling − 1)` on all but `4-1_0`, `4-3_0` and `2-2_0`, so a refutation here would also have been above Harper's ceiling on eight of them. Every optimum was re-read from `solutions/` (provenance `certified:refutation` on all 11); every SAT answer's two sets were re-verified from the masks (sizes, nesting, boundary sum).

**First window** (sizes `0.52–0.61 n`, the §5 band; six calls per instance: adjacent pairs at `0.55 n`, `0.58 n`, `0.52 n`, `0.61 n`, a pair two apart at `0.56 n`, and the first pair with weights (1, 2)): **66 calls, 66 sat, 0 censored, 166 s on 4 cores.** No floor rises. On the four density-6 instances the window was *vacuous or nearly so*: the inner boundary of a `t`-set is at most `t`, and with `F = 70–78` and sizes `65–77` every pair of `6-3_0` and `6-4_0` has `2F ≥ t_1 + t_2` (the constraint cannot bind), while on `6-2_0` and `6-5_0` the largest pairs ask for 2–13 interior vertices across the two sets and are satisfied at 0 conflicts; the table marks the fully vacuous two. On the seven others the calls were genuine and quick (median 1.3 s, 78 s at most on the ridge instance), each returning a nested pair with boundary sum `≤ 2F`: at those sizes the two-level relaxation admits a solution below the floor, and nothing with two levels there can raise it.

**High window** (adjacent pairs at `0.66 n`, `0.70 n`, `0.75 n`, `0.80 n` and at `F + 2`, `F + 5`, `F + 9` where higher, pairs with `t_1 + t_2 ≤ 2F` dropped; 76 calls planned): **29 finished, all sat** (the quick ones: sizes near `F` on the 100s and `4-1/4-2`, the far-right sizes `80–101`); the four calls the workers were on at 19:28 ran at full CPU for two hours with no answer, past the owner's budget, and the coordinator stopped the process; the other 43 never started. **Those 47 are undecided, not results.** The 180 s per-call cap did not bind: pysat's `interrupt()` is not honoured by CaDiCaL (the cap was tested only on a call that returned SAT in 1.6 s, which exercised nothing), and a conflict budget — which the 30–50 run used — is the only bound on work that holds; the module's docstring now says so. The first window's `0.5–0.6 n` sizes answered in seconds; the sizes around `0.7 n` on the 100- and 125-vertex instances are where the two-level formula stops being easy, which is the pattern of `reports/checkpoint_relaxation.md` §6 (dense 75-vertex instances refute in minutes to an hour, the ridge never).

| instance | n | optimum | Harper on record [floor, ceiling] | best floor on record | target total `2F` | first window: pairs (sizes; weights (1,1) unless marked) | answers | high window: pairs finished | answers | high window: not finished (undecided) |
|---|---|---|---|---|---|---|---|---|---|---|
| `Random-100-100-4-1_0` | 100 | 46 | [34, 44] | 45 | 88 | (52,53), (55,56), (55,56)×(1,2), (56,58), (58,59), (61,62) | all sat; 2 s max | (46,47), (49,50), (53,54), (80,81), (66,67), (75,76), (70,71) | all sat; 81 s max | — |
| `Random-100-100-4-3_0` | 100 | 43 | [26, 42] | 42 | 82 | (52,53), (55,56), (55,56)×(1,2), (56,58), (58,59), (61,62) | all sat; 1 s max | (43,44), (46,47), (50,51), (66,67), (75,76), (80,81), (70,71) | all sat; 95 s max | — |
| `Random-125-125-2-2_0` | 125 | 25 | [8, 23] | 24 | 46 | (65,66), (69,70), (69,70)×(1,2), (70,72), (72,73), (76,77) | all sat; 78 s max | (28,29), (25,26), (32,33), (88,89), (94,95), (100,101), (82,83) | all sat; 160 s max | — |
| `Random-125-125-4-1_0` | 125 | 57 | [37, 55] | 53 | 104 | (65,66), (69,70), (69,70)×(1,2), (70,72), (72,73), (76,77) | all sat; 9 s max | (54,55), (57,58), (61,62), (100,101) | all sat; 27 s max | (82,83), (88,89), (94,95) |
| `Random-125-125-4-2_0` | 125 | 57 | [35, 56] | 55 | 108 | (65,66), (69,70), (69,70)×(1,2), (70,72), (72,73), (76,77) | all sat; 24 s max | (56,57), (59,60), (63,64), (82,83) | all sat; 34 s max | (88,89), (94,95), (100,101) |
| `Random-125-125-4-3_0` | 125 | 54 | [34, 53] | 52 | 102 | (65,66), (69,70), (69,70)×(1,2), (70,72), (72,73), (76,77) | all sat; 64 s max | — | — | (53,54), (56,57), (60,61), (82,83), (88,89), (94,95), (100,101) |
| `Random-125-125-4-4_0` | 125 | 51 | [24, 50] | 50 | 98 | (65,66), (69,70), (69,70)×(1,2), (70,72), (72,73), (76,77) | all sat; 4 s max | — | — | (51,52), (54,55), (58,59), (82,83), (88,89), (94,95), (100,101) |
| `Random-125-125-6-2_0` | 125 | 77 | [61, 75] | 76 | 150 | (65,66), (69,70), (69,70)×(1,2), (70,72), (72,73), (76,77) | all sat; 0 s max | — | — | (77,78), (80,81), (82,83), (84,85), (88,89), (94,95), (100,101) |
| `Random-125-125-6-3_0` | 125 | 80 | [70, 79] | 79 | 156 | (65,66), (69,70), (69,70)×(1,2), (70,72), (72,73), (76,77) | all sat (vacuous: 2F ≥ t₁ + t₂); 0 s max | — | — | (80,81), (82,83), (83,84), (87,88), (88,89), (94,95), (100,101) |
| `Random-125-125-6-4_0` | 125 | 80 | [69, 79] | 78 | 154 | (65,66), (69,70), (69,70)×(1,2), (70,72), (72,73), (76,77) | all sat (vacuous: 2F ≥ t₁ + t₂); 0 s max | — | — | (79,80), (82,83), (86,87), (88,89), (94,95), (100,101) |
| `Random-125-125-6-5_0` | 125 | 74 | [59, 73] | 71 | 140 | (65,66), (69,70), (69,70)×(1,2), (70,72), (72,73), (76,77) | all sat; 0 s max | — | — | (72,73), (75,76), (79,80), (82,83), (88,89), (94,95), (100,101) |

**Harness.** `learning.bound_harness.evaluate_candidates` on the 11 with the candidate `learning.chain_lp:pair_floor_candidate` (the best value this run proved for the matrix, 0 where none): 0 on all 11, below every certified optimum (`harness_validity.csv`); there is no claimed value to validate, and none above an optimum.

**Verdict for the two-level line on the dense residual.** Dead at the sizes where it is cheap, undecided where it is not. At `0.52–0.61 n` — the band that carried every certificate at 30–50 — every one of the 11 has a nested pair below its floor, so no two-level sum there raises any floor; at `0.66–0.80 n` the few calls that returned were also sat and the rest did not return in two hours. The owner's 1–4 missing stacks on these instances are, on this evidence, not a two-level fact at any size tried: where the gap is 2–4 (`4-1_0`, `4-3_0`, `6-5_0`, `100-4-1_0`) the first-window calls were as quick and as satisfiable as where it is 1. Nothing on record moves; `solutions/` untouched; about 0.6 core-hours for the first window and 8 core-hours for the stopped second.

## 8. The 11 again: the mixture upper bound on `L`, and the pairs its `μ` points to (owner's follow-up, 2026-11-11)

*Regenerate: `nice -n 19 python -m learning.chain_lp --stage ceiling11 --workers 4 --pool 300` (327 s on 4 cores) and `… --stage residual_mu --workers 4 --conflicts 2000000` (851 s on 4 cores); data `reports/scratch/chain_lp/residual/ceiling11.csv`, `residual_mu.csv`, `harness_validity.csv`; logs `reports/scratch/chain_lp/ceiling11_run.out`, `residual_mu_run.out`. About 1.3 core-hours; nothing else of ours running.*

**(1) The mixture upper bound `U` on the ceiling `L(G)`** (§5: `L ≤ U` for the mixture LP over any pool of layouts; `⌈U⌉ ≤ F` would prove `⌈L⌉ ≤ F`, closing every LP/SDP route in layout variables on that instance by the ceiling theorem). Pool per instance: the stored witness ordering's four layouts (opening and closing orders and their reversals), each improved by the one-move descent; 300 greedy layouts with random tie-breaks and their reversals plus one per start vertex (the best dozen improved; the descent is `O(n⁴)` per round, so not all 2n as at 30–50); 812–870 distinct layouts. `F` is the best floor on record in `vs` units (optimum units minus one), as in §7.

| instance | n | vs | Harper on record [floor, ceiling] (opt. units) | best floor (opt. units) | F (vs units) | U | ⌈U⌉ | ⌈U⌉ ≤ F | layouts in the mixture | μ levels (outer size : weight) | pool | seconds |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `Random-100-100-4-1_0` | 100 | 45 | [34, 44] | 45 | 44 | 45.000 | 45 | no | 1 | 34:0.333 32:0.214 22:0.143 25:0.143 26:0.071 29:0.048 37:0.048 | 816 | 37 |
| `Random-100-100-4-3_0` | 100 | 42 | [26, 42] | 42 | 41 | 42.000 | 42 | no | 1 | 35:0.600 25:0.400 | 812 | 51 |
| `Random-125-125-2-2_0` | 125 | 24 | [8, 23] | 24 | 23 | 24.000 | 24 | no | 1 | 51:1.000 | 870 | 72 |
| `Random-125-125-4-1_0` | 125 | 56 | [37, 55] | 53 | 52 | 56.000 | 56 | no | 1 | 46:1.000 | 870 | 50 |
| `Random-125-125-4-2_0` | 125 | 56 | [35, 56] | 55 | 54 | 56.000 | 56 | no | 1 | 30:1.000 | 867 | 145 |
| `Random-125-125-4-3_0` | 125 | 53 | [34, 53] | 52 | 51 | 53.000 | 53 | no | 1 | 49:1.000 | 868 | 70 |
| `Random-125-125-4-4_0` | 125 | 50 | [24, 50] | 50 | 49 | 50.000 | 50 | no | 1 | 29:0.353 47:0.235 35:0.176 45:0.176 41:0.059 | 869 | 60 |
| `Random-125-125-6-2_0` | 125 | 76 | [61, 75] | 76 | 75 | 75.500 | 76 | no | 2 | 26:0.500 27:0.500 | 863 | 190 |
| `Random-125-125-6-3_0` | 125 | 79 | [70, 79] | 79 | 78 | 78.500 | 79 | no | 2 | 22:0.500 25:0.500 | 869 | 100 |
| `Random-125-125-6-4_0` | 125 | 79 | [69, 79] | 78 | 77 | 78.333 | 79 | no | 3 | 23:0.333 30:0.333 20:0.333 | 866 | 207 |
| `Random-125-125-6-5_0` | 125 | 73 | [59, 73] | 71 | 70 | 73.000 | 73 | no | 1 | 28:1.000 | 868 | 124 |

**`⌈U⌉ ≤ F` on 0 of 11; `U` closes nothing.** On eight the equilibrium mixture is a *single* layout — the pool's best, of width `vs` — so `U = vs` and `μ` is a point mass at that layout's peak size, carrying no information beyond "where its boundary is largest"; on the three density-6 instances `6-2_0`, `6-3_0`, `6-4_0` a mixture of 2–3 layouts flattens the profile to `vs − ½`, `vs − ½`, `vs − ⅔`, still rounding to `vs`. An upper bound from a heuristic pool proves `L ≤ F` only when the pool holds a mixture averaging below the floor, and at these sizes greedy layouts with different peaks do not combine that way: `U` is weak here, not informative. It therefore does not say that `L` cannot reach `F + 1`; it says nothing either way.

**(2) The two-level sum at `μ`'s sizes.** For each instance the two heaviest `μ` levels `t_a, t_b` (outer sizes) mapped to the encoding's inner sizes `n − t` (the inner boundary of an `i`-prefix is the outer boundary of the complementary suffix), with weights (1, 1), the integer ratio `μ` suggests where it is not 1:1 (`(2,1)` on `100-4-1_0`, `(1,2)` on `4-4_0`), and the neighbours `t ± 1`; a point-mass `μ` gets the two adjacent pairs at its level; pairs with `Σ w t ≤ F Σ w` (vacuous) dropped. Target `F·Σw`: UNSAT proves `vs ≥ F + 1`. **Conflict budget 2,000,000 per call** (the time cap of §7 does not bind on CaDiCaL; at the measured 40–150 µs per conflict a censored call took 73–311 s). 41 calls, 851 s on 4 cores: **0 unsat, 24 sat, 17 censored. No floor rises.**

| instance | F | calls (inner sizes; weights) → answer, conflicts | sat | censored |
|---|---|---|---|---|
| `Random-100-100-4-1_0` | 44 | (65,68; 1,1) sat 0.04M, (65,68; 2,1) sat 0.15M, (66,67; 1,1) sat 0.15M, (66,67; 2,1) sat 0.33M, (66,68; 1,1) sat 0.08M, (66,68; 2,1) sat 0.06M, (66,69; 1,1) sat 0.08M, (66,69; 2,1) sat 0.50M | 8 | 0 |
| `Random-100-100-4-3_0` | 41 | (64,75; 1,1) sat 1.23M, (65,74; 1,1) sat 0.21M, (65,75; 1,1) sat 0.72M, (65,76; 1,1) censored | 3 | 1 |
| `Random-125-125-2-2_0` | 23 | (73,74; 1,1) sat 0.64M, (74,75; 1,1) censored | 1 | 1 |
| `Random-125-125-4-1_0` | 52 | (78,79; 1,1) sat 0.50M, (79,80; 1,1) censored | 1 | 1 |
| `Random-125-125-4-2_0` | 54 | (94,95; 1,1) censored, (95,96; 1,1) sat 0.88M | 1 | 1 |
| `Random-125-125-4-3_0` | 51 | (75,76; 1,1) sat 0.20M, (76,77; 1,1) sat 1.43M | 2 | 0 |
| `Random-125-125-4-4_0` | 49 | (77,96; 1,1) sat 0.15M, (77,96; 1,2) censored, (78,95; 1,1) sat 0.15M, (78,95; 1,2) censored, (78,96; 1,1) sat 0.60M, (78,96; 1,2) censored, (78,97; 1,1) sat 0.63M, (78,97; 1,2) censored | 4 | 4 |
| `Random-125-125-6-2_0` | 75 | (97,99; 1,1) sat 0.63M, (98,100; 1,1) sat 0.25M, (98,99; 1,1) sat 0.50M | 3 | 0 |
| `Random-125-125-6-3_0` | 78 | (100,102; 1,1) censored, (100,103; 1,1) censored, (100,104; 1,1) censored, (99,103; 1,1) censored | 0 | 4 |
| `Random-125-125-6-4_0` | 77 | (94,102; 1,1) sat 0.20M, (95,101; 1,1) censored, (95,102; 1,1) censored, (95,103; 1,1) censored | 1 | 3 |
| `Random-125-125-6-5_0` | 70 | (96,97; 1,1) censored, (97,98; 1,1) censored | 0 | 2 |

Every sat answer's two sets were re-verified from the masks (sizes, nesting, boundary sum `≤ F·Σw`). The harness comparison (`pair_floor_candidate` reading all three residual files; `harness_validity.csv`): 0 claimed on all 11, nothing above any certified optimum.

**Verdict.** The dual's two-level form reaches the last unit on **none of the 11**. It is **not because `U` says it cannot** — `U` is `vs` or within a unit of it on every instance, an uninformative upper bound from pools whose mixtures do not average below the floor — and **not only because the calls censored**: on three instances (`100-4-1_0`, `4-3_0`, `6-2_0`) every pair `μ` pointed to answered **sat**, on `100-4-3_0` three of four did and on `4-4_0` all four (1,1) pairs did — a nested pair below the floor at exactly the sizes the mixture's dual weights, so the two-level form is refuted *there* by a witness; on `6-3_0` and `6-5_0` every call censored (undecided), and on `2-2_0`, `4-1_0`, `4-2_0`, `6-4_0` and the weighted `4-4_0` calls one pair answered sat and the others censored. Taken with §7 (66 sat at `0.52–0.61 n`, 29 sat and 47 unanswered in the high window), the two-level line on the dense residual has no refutation at any size tried and a satisfying nested pair at most of them. Whether a three-level or a full-band sum would do what two levels cannot is the checkpoint study's question (`reports/checkpoint_relaxation.md` §5–§6: at gap 2–4 the certificate is a quarter of the chain, and at 75 the ridge censors), not an LP's. Nothing on record moves; `solutions/` untouched.
