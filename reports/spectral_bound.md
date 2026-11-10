# Spectral lower bounds on vertex separation, measured on the bound-gap instances

*One session, 2026-11-10. Code `learning/spectral_bound.py` (tests
`tests/test_spectral_bound.py`, 15); data and tables under
`reports/scratch/spectral_bound/` (`values.csv.gz` is the harness run over
every certified instance, `check_small.csv.gz` the small-graph check,
`tables.md` the generated tables). Nothing here changes a solver default;
nothing is re-solved; `solutions/` is untouched. Compute: 1.7 core-hours for
the 50,949-instance harness run and about 1.4 for the 274,048-graph check,
eigenvalues only, 4 + 4 workers at `nice 19`.*

## 0. Summary and verdict

**The question.** Every lower bound the solver computes — the trivial bound,
the clique bound, contraction degeneracy + 1 — is a bound on `treewidth + 1`
and cannot see `pw > tw`, which holds on 142 of the 209 bound-gap instances
where treewidth is exact (`reports/ml_nature.md` §6, §21). Eigenvalue bounds
are not of that kind a priori, and the project had never computed one. This
is the one cheap, decisive measurement: the spectral vertex-separator
inequalities of the literature, turned into a lower bound on vertex
separation = pathwidth by the prefix-separator argument (§1, Theorem 4),
checked against exact pathwidth on every graph to 9 vertices (§2), run
through `learning/bound_harness.py` over all 50,949 certified instances (§3),
and read against every floor on record on the 338 bound-gap instances
(`optimum − lb_best ≥ 2`; `reports/obstruction_search.md`).

**Kill criterion, written before measuring** (module docstring): the family
is dead if the best spectral floor — over the graph, every induced subgraph
of the degeneracy peeling, and every minor of the contraction-degeneracy
sequence — never exceeds the best floor on record (the loop0013 result,
`reports/scratch/obstruction_search/08_map/map.csv`, column `best`) on any of
the 338 gap instances.

**Verdict: dead.** On the 338 gap instances the spectral floor is **strictly
below the best floor on record on 338 of 338** (never equal; the record is
the searched contraction minor on 327 of them). It is above `lb_best` on 9
(by one each), above the harness reference `max(lb_best, tw + 1)` on 5, above
loop0013's pre-search `floor0` on 1 (`Random-100-50-2-3_0`, 11 against 10,
optimum 15), and tight on none. Its mean shortfall to the optimum on the 338
is **7.49 stacks** (the reference's is 3.92, the record floor's 0.06); the
whole-graph value alone is short by 16.1 on average, 35% of the optimum.

| on the 338 gap instances (optimum units) | spectral above | equal | below | max excess | mean (spectral − ref) |
|---|---:|---:|---:|---:|---:|
| `lb_best` (the solver's bound) | 9 | 187 | 142 | +1 | −2.71 |
| reference `max(lb_best, tw + 1)` | 5 | 52 | 281 | +1 | −3.57 |
| `floor0` (loop0013 §1, on record before the search) | 1 | 36 | 301 | +1 | −5.16 |
| **best floor on record after loop0013** | **0** | **0** | **338** | **−1** | **−7.43** |
| Harper at cap 12 (family E's floor) | 64 | 93 | 181 | +7 | −3.50 |
| `tw + 1` (`tw_lo`, the interval's lower end) | 95 | 37 | 206 | +19 | +1.39 |

| family (on the 338) | mean optimum − value | max | tight | > `lb_best` |
|---|---:|---:|---:|---:|
| graph (Theorems 1–3 on `G`) | 16.15 | 73 | 0 | 0 |
| Theorem 1 alone on `G` | 16.54 | 73 | 0 | 0 |
| peel (best induced subgraph of the degeneracy peeling) | 10.92 | 54 | 0 | 0 |
| minor (best contraction-degeneracy minor) | 7.49 | 44 | 0 | 9 |

**On the 11 residual dense instances** (`Random-100-100-4`,
`Random-125-125-4/6`, the only gap instances whose record floor is below the
optimum, by 1–4): the spectral floor sits **13 to 42 stacks below the
optimum** (25 against 57 on `Random-125-125-4-1_0`, 38 against 77 on
`Random-125-125-6-2_0`, 13 against 25 on `Random-125-125-2-2_0`), the
whole-graph value 5 to 24. The reason is in the numbers: `μ₂` is 0.5–11 where
`Δ` is 15–64, and every one of these inequalities is, at best,
`n μ₂ / (Δ + μ₂)` (§1(ii)).

**Three things the measurement settles, each stated before it was measured.**

1. *The spectral bound is a relaxation of Harper's bound and never exceeds
   it* (§1(i), a two-line proof): on the 4,123 corpus instances at `n ≤ 22`,
   where Harper's profile is exact, the whole-graph spectral value equals
   Harper's on 2,080 (50.4%) and is short of it by 1.47 on average, 12 at
   most; on the 274,048 small graphs it never exceeds Harper, equals it on
   14.3% (13.5% of the 261,080 connected graphs on 9 vertices, where Harper
   is tight on 65.1% and the spectral value on 2.8%). On the 338 it is 14.5
   below Harper's ceiling on average and equals it on none. Since Harper's
   ceiling is below the optimum on 320 of the 338
   (`reports/obstruction_search.md` §0), no computation of the whole-graph
   spectral bound could have closed them; what was open was its value on
   subgraphs and minors, where Harper was never searched — measured above.
2. *The Theorem-1 part is a treewidth bound in disguise* (§1(ii)): its
   whole-graph value is at most `tw + 1` in pathwidth units, by the proof of
   Gima, Hanaka, Noro, Ono & Otachi (2025, Theorem 3.4) read with the
   top-degree sum in place of `Δ|S|`. Measured on the 209 gap instances with
   exact treewidth: the spectral floor exceeds `tw + 1` on **0 of 209 for
   every family**, minors included, although `pw > tw` on 142 of them. The
   95 in the table above are against `tw_lo`, the lower end of an interval,
   and say nothing about the ceiling. Spectral bounds do not escape the
   treewidth ceiling that §24 put on the degree family; they sit under it.
3. *Theorems 2 and 3 (the `λₙ` forms) add almost nothing to Theorem 1*: the
   whole-graph value is the same with or without them on 272 of the 338, on
   95.9% of the small graphs, and the cases where they add are worth one
   unit.

**Validity.** 0 of 50,949 certified instances above the optimum (corpus
6,376; campaign 37,800; upward 6,773), 0 of 274,048 small graphs above exact
pathwidth, 0 of 110,096 separator triples of the 995 connected graphs on ≤ 7
vertices violating any of the three inequalities. The bound is not wrong; it
is weak exactly where the instances are hard.

**What the bound is good for, measured.** Corpuswide it is tight on 4,160 of
6,376 (65.2%; `lb_best` 77.0%), above `lb_best` on 9 and below it on 1,375;
on the Chu & Stuckey instances it is tight on 1.5% with a mean shortfall of
13.0. It is tight on 92.8% of the connected graphs on 9 vertices through the
minor family (the whole graph alone, 2.8%): a bound for small graphs, where
nothing is needed. Median cost 0.02 s per instance, 36.5 s at most
(`Random-125-125-4-4_0`, the contraction sequence of a dense graph).

**Not done, and why.** No SDP (the Helmberg et al. diagonal-correction
`max_u μ₂(L + diag u)` is an eigenvalue optimisation and the brief excludes
it); no normalised-Laplacian form (its right-hand side needs lower bounds on
`vol(A)` and `vol(B)`, which the fringe of degree-1 customers makes
worthless); no three-part Gima trick on the prefix (the layout's prefix
components are unknown). None would change the verdict: every such bound is
an inequality on one separator and §1(i) applies to each.

---

## 1. The bounds, as theorems

Notation: `G` connected on `n` vertices, Laplacian `L = D − A` with
eigenvalues `0 = μ₁ < μ₂ ≤ … ≤ μₙ`, maximum degree `Δ`, `S(c)` the sum of the
`c` largest degrees. A **separator triple** `(C, A, B)` is a partition of `V`
with no edge between `A` and `B`, sizes `a, b, c`, `a + b + c = n`. For a
disconnected graph every value is the maximum over components, since
`pw` is and `μ₂ = 0` says nothing.

**Theorem 1** (Mohar & Poljak 1993, Thm 2.8, as quoted by Helmberg, Mohar,
Poljak & Rendl 1995 eq. (21) and Díaz, Petit & Serna 2002 Thm 9.4; here with
`S(c)` for `Δc`). For every separator triple,
`S(c) ≥ μ₂ ((a + b) − (a − b)²/n)`; with `Δc` for `S(c)` this is
`c ≥ 4 μ₂ a b / (Δ n − μ₂ (a + b))`.
*Proof.* `x = 1_A − 1_B` has `Σx = a − b`; Rayleigh on the component
orthogonal to `1` gives `xᵀLx ≥ μ₂ (xᵀx − (Σx)²/n) = μ₂((a+b) − (a−b)²/n)`;
and `xᵀLx = Σ_{uv∈E}(x_u − x_v)² = e(A,C) + e(B,C) ≤ Σ_{v∈C} deg v ≤ S(c)`.
Multiplying out with `a + b + c = n` gives the quoted form. ∎

**Theorem 2** (Helmberg, Mohar, Poljak & Rendl 1995, Theorem 11, eq. (20);
their Theorem 1 at `cut(A, B) = 0`). For every separator triple of a
non-complete graph, `c ≥ 4 μₙ μ₂ a b / (n (μₙ − μ₂)²)`.

**Theorem 3** (Gu & Liu 2022, quoted as Lemma 4.1 of Gima et al. 2025). For
every separator triple of a non-complete graph with an edge,
`c ≥ 2 μ₂ min(a, b) / (μₙ − μ₂)`.

Theorems 2 and 3 are cited, not re-proved; all three were checked on every
separator triple `(C, A, B)` with `A, B ≠ ∅` of every connected graph on 2–7
vertices before anything was built on them: 995 graphs, 110,096 triples, 0
violations (`check_inequalities`, `reports/scratch/spectral_bound/check_inequalities.csv`
empty).

**Theorem 4 (the prefix-separator bound).** Let `σ` be a layout of vertex
separation `w`, `V_t` its first `t` vertices,
`C_t = {v ∉ V_t : N(v) ∩ V_t ≠ ∅}` (so `|C_t| ≤ w` by definition),
`A_t = V_t`, `B_t = V ∖ (V_t ∪ C_t)`. Then `(C_t, A_t, B_t)` is a separator
triple with `a = t`, `b = n − t − c`. Define
`feasible(c, t)` := Theorems 1–3 all hold at `(c, t, n − t − c)`;
`c_t := min{c ∈ [0, n − t] : feasible(c, t)}` (`c = n − t` always is, by the
edge-expansion inequality `e(S, V∖S) ≥ μ₂|S|(n−|S|)/n`); and
`spec(G) := max_{1 ≤ t ≤ n−1} c_t`. Then `vs(G) = pw(G) ≥ spec(G)` and
`MOSP ≥ spec(G) + 1`.
*Proof.* `|C_t|` is feasible at `t`, so `w ≥ |C_t| ≥ c_t` for every `t`. ∎
(`vs = pw`: Kinnersley 1992, `lean/MOSPFormalization/VSEquivPW.lean`;
`MOSP = pw + 1`: `MOSPGraph.lean`.) The prefix-side convention gives the same
value because the inequalities are symmetric in `a ↔ b`. Cost `O(n²)` after
one eigendecomposition.

**Families.** `graph`: Theorem 4 on `G`. `peel`: on every induced subgraph
of the degeneracy peeling (delete a minimum-degree vertex, repeat), valid
because `pw` is subgraph-monotone. `minor`: on every minor of the
contraction-degeneracy sequence (`learning.bound_harness.contraction_minors`,
the rule of `_contraction_degeneracy`), valid because `pw` is
minor-monotone (`Minor.lean`). The harness candidate is the best of the
three plus one.

**(i) Spectral ≤ Harper.** For any `S` with `|S| = t`,
`(N(S) ∖ S, S, V ∖ N[S])` is a separator triple, so `c_t ≤ |N(S) ∖ S|` and
`c_t ≤ min_{|S|=t} |N(S) ∖ S| = f(t) − t` in the notation of
`satisfiability/expansion_bound.py`; hence `spec(G) ≤ max_t (f(t) − t)`,
which is Harper's bound (`exists_closedNbhd_card_le`, `EmptyPair.lean`). The
spectral bound lower-bounds the same minimum Harper takes exactly; it cannot
exceed the exact Harper value and the only question is the slack (§3.4).

**(ii) Theorem 1 is a treewidth bound.** For every `t`,
`c_t^{(1)} ≤ c_bal := min{c : S(c) ≥ μ₂(n − c)}`, the balanced instance of
Theorem 1 being its strongest. Gima et al. 2025 Theorem 3.4 proves
`tw + 1 ≥ |S| ≥ n μ₂/(Δ + μ₂)` from a separator `S` of size `≤ tw + 1` whose
remainder splits into three parts of at most half each, with a complex unit
test vector; the only use of `Δ` is `x*Lx ≤ Δ|S|`, which reads
`x*Lx ≤ S(|S|)` verbatim. So `tw + 1 ≥ c_bal ≥ spec₁(G)` in pathwidth units:
the Theorem-1 spectral floor is at most `tw + 2` in optimum units, one above
the treewidth ceiling of `reports/ml_nature.md` §24, and reaches `tw + 2` only
where the Gima bound is tight for treewidth (complete bipartite graphs,
their Remark 3.5). The harness confirms `Theorem-1 graph > tw + 2` on 0
instances with exact treewidth, and in fact `> tw + 1` on 0.

**Numerics.** `numpy.linalg.eigvalsh` on the dense Laplacian; `μ₂` is
lowered and `μₙ` raised by `10⁻⁷` (relative) before use. Each right-hand side
is increasing in `μ₂` and decreasing in `μₙ`, so rounding can only lose a
unit, never claim one; the complete graph, where Theorems 2–3 are not stated,
imposes no constraint from them.

## 2. Small graphs against exact pathwidth and exact Harper

`python3 -m learning.spectral_bound --stage check --workers 4`: every graph of
the atlas on 2–7 vertices (1,251), every connected graph on 8 (11,117) and 9
(261,080) vertices from `nauty-geng`, and 120 random connected graphs at each
of 10–14 vertices; exact pathwidth by the subset DP
(`fixed_parameter_algorithm/pathwidth.py`), exact Harper by enumeration of
all subsets per component. Pathwidth units.

| n | graphs | best > pw (must be 0) | graph > Harper (must be 0) | graph tight | peel tight | minor tight | Harper tight | mean pw − best | mean Harper − graph | Thm 1 alone = all |
|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| 2–5 | 51 | 0 | 0 | 0.78 | 0.98 | 1.00 | 0.86 | 0.00 | 0.08 | 0.98 |
| 6 | 156 | 0 | 0 | 0.51 | 0.90 | 0.99 | 0.74 | 0.01 | 0.30 | 0.97 |
| 7 | 1,044 | 0 | 0 | 0.27 | 0.77 | 0.99 | 0.65 | 0.01 | 0.51 | 0.97 |
| 8 | 11,117 | 0 | 0 | 0.10 | 0.57 | 0.96 | 0.62 | 0.04 | 0.83 | 0.97 |
| 9 | 261,080 | 0 | 0 | 0.03 | 0.35 | 0.93 | 0.65 | 0.07 | 1.12 | 0.96 |
| 10–14 (random) | 600 | 0 | 0 | 0.03 | 0.32 | 0.75 | 0.64 | 0.25 | 1.39 | 0.97 |

The whole-graph value falls away from the pathwidth as `n` grows (tight on
2.8% at 9 vertices against Harper's 65%); the minor family rescues it on
small graphs because the contraction sequence ends in small dense minors
where `μ₂/Δ` is large. Named cases: `K_{p,q}` is tight (`spec = min(p, q)`,
Gima's Remark 3.5 in pathwidth form), `K_n` is tight, cycles and paths are
tight, the Petersen graph gives 4 against `pw = 5 = Harper`.

## 3. The corpus

### 3.1 Validity (harness stage (a))

`python3 -m learning.spectral_bound --stage validity --workers 4`, which calls
`learning.bound_harness.run_validity` with `spectral` registered as a
candidate: 50,949 certified instances, **0 above the optimum**. The harness
table (optimum units):

| bound | rows | above optimum | tight, all | > lb_best, all | > reference, all | tight, gap | > lb_best, gap | beats reference, gap | mean shortfall, gap |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| `tw + 1` (`tw_lo`) | 50,949 | 0 | 0.779 | 0.148 | 0 | 0.198 | 0.589 | 0 | 8.88 |
| `lb_best` | 50,949 | 0 | 0.690 | 0 | 0 | 0 | 0 | 0 | 4.78 |
| reference `max(lb_best, tw + 1)` | 50,949 | 0 | 0.810 | 0.148 | 0 | 0.198 | 0.589 | 0 | 3.92 |
| **spectral** | 50,949 | **0** | 0.483 | 0.005 | 0.002 | 0 | 0.027 | 5 | 7.49 |

| source | rows | tight | > lb_best | > reference | mean optimum − spectral | max | median s | max s | core-h |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| corpus | 6,376 | 0.652 | 0.0014 | 0.0008 | 1.00 | 44 | 0.021 | 36.5 | 0.23 |
| campaign (10–40) | 37,800 | 0.528 | 0.0027 | 0.0001 | 1.29 | 10 | 0.029 | 2.8 | 0.38 |
| upward (50–100) | 6,773 | 0.071 | 0.0226 | 0.0161 | 8.92 | 24 | 0.252 | 21.9 | 1.06 |

By collection (corpus): tight on 78.2% of Simonis, 55.4% of Harvey, 33.0% of
Faggioli–Bentivoglio, 25.0% of SCOOP, 1.5% of Chu & Stuckey (mean shortfall
13.0).

### 3.2 The 338 gap instances

The tables of §0. By size band (optimum units):

| band | gap instances | mean optimum | mean spectral | mean record floor | mean `tw + 1` | spectral > record | spectral > `lb_best` | mean shortfall |
|---|--:|--:|--:|--:|--:|--:|--:|--:|
| 9–20 | 17 | 11.6 | 9.5 | 11.6 | 10.8 | 0 | 0 | 2.1 |
| 21–30 | 133 | 16.1 | 13.5 | 16.1 | 15.4 | 0 | 0 | 2.6 |
| 31–40 | 47 | 12.4 | 9.6 | 12.4 | 11.3 | 0 | 2 | 2.8 |
| 41–60 | 54 | 13.8 | 9.9 | 13.8 | 10.3 | 0 | 2 | 3.9 |
| 61–75 | 17 | 33.4 | 20.7 | 33.4 | 13.3 | 0 | 1 | 12.7 |
| 76–100 | 45 | 46.2 | 26.6 | 46.2 | 17.5 | 0 | 2 | 19.6 |
| 101–134 | 25 | 63.0 | 34.3 | 62.3 | 22.2 | 0 | 2 | 28.6 |

The shortfall grows with size: the whole-graph value is 35% of the optimum on
average over the 338 and the minor family 74%. The minor family is strictly
better than the peel on 303 of 338 and the peel strictly better than the
whole graph on 317; the best minor has 42% of the vertices on average. The
nine instances above `lb_best` (all by one; five of them above the
reference) are `Random-125-125-2-3_0` (13 against `lb_best` 12, optimum 21),
`Random-125-125-4-4_0` (25 / 24 / 51), `Random-100-50-2-3_0` (11 / 10 / 15),
`Random-100-50-6-2_0` (25 / 24 / 43), `Random-75-75-4-5_0` (20 / 19 / 32),
`Random-50-50-2-4_0` (11 / 10 / 13), `p3050n7_0` (9 / 8 / 12), `p3040n7_0`
(10 / 9 / 13), `p2040n5_0` (7 / 6 / 8); every one has a searched minor
certificate at the optimum.

### 3.3 The 11 residual dense instances

| instance | n | optimum | `lb_best` | `tw + 1` | record floor | Harper cap 12 | Harper ceiling | spectral | graph | peel | minor | `μ₂` | `Δ` | `n μ₂/(Δ+μ₂)` |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| Random-100-100-4-1_0 | 100 | 46 | 28 | 12 | 45 | 33 | 44 | 23 | 10 | 19 | 23 | 2.66 | 38 | 6.5 |
| Random-100-100-4-3_0 | 100 | 43 | 23 | 12 | 42 | 26 | 42 | 22 | 7 | 16 | 22 | 1.80 | 34 | 5.0 |
| Random-125-125-2-2_0 | 125 | 25 | 13 | 6 | 24 | 7 | 23 | 13 | 5 | 9 | 13 | 0.48 | 15 | 3.9 |
| Random-125-125-4-1_0 | 125 | 57 | 27 | 12 | 53 | 33 | 55 | 27 | 8 | 21 | 27 | 1.89 | 40 | 5.7 |
| Random-125-125-4-2_0 | 125 | 57 | 27 | 12 | 55 | 32 | 56 | 27 | 7 | 20 | 27 | 1.61 | 38 | 5.1 |
| Random-125-125-4-3_0 | 125 | 54 | 27 | 12 | 52 | 31 | 53 | 26 | 10 | 20 | 26 | 2.64 | 47 | 6.6 |
| Random-125-125-4-4_0 | 125 | 51 | 24 | 11 | 50 | 21 | 50 | 25 | 5 | 18 | 25 | 0.90 | 35 | 3.1 |
| Random-125-125-6-2_0 | 125 | 77 | 51 | 23 | 76 | 60 | 75 | 38 | 7 | 32 | 38 | 2.83 | 62 | 5.5 |
| Random-125-125-6-3_0 | 125 | 80 | 58 | 24 | 79 | 64 | 79 | 42 | 13 | 32 | 42 | 5.80 | 60 | 11.0 |
| Random-125-125-6-4_0 | 125 | 80 | 60 | 22 | 78 | 63 | 79 | 41 | 24 | 29 | 41 | 11.31 | 64 | 18.8 |
| Random-125-125-6-5_0 | 125 | 74 | 49 | 21 | 71 | 56 | 73 | 36 | 16 | 29 | 36 | 6.38 | 60 | 12.0 |

(`tw + 1` is `tw_lo + 1`; treewidth is not exact on these. Harper's cap-12
floor and ceiling from `reports/scratch/obstruction_search/`.) The
whole-graph spectral value is at or near the Gima value `n μ₂/(Δ + μ₂)` plus
what the top-degree sum buys; on a degree-dispersed graph `μ₂ ≤ δ n/(n−1)`
is pinned by the minimum degree while `Δ` is the hub degree, and the ratio
is 1/10 to 1/20. Contraction raises the minimum degree and halves the gap,
no more: 13–42 stacks short.

### 3.4 Slack to Harper, and the treewidth ceiling

*Harper.* On the 4,123 corpus instances at `n ≤ 22`, where Harper's profile
is exact (`reports/obstruction_search.md` §2), the whole-graph spectral value
equals Harper's on 2,080 (50.4%), mean slack 1.47, maximum 12; Harper is
tight on 2,933 of them, the spectral value on 1,826. On the 338 the
whole-graph value is above Harper's cap-12 floor on 1, equal on 3, below on
334, and 14.5 below Harper's ceiling on average. The spectral bound is the
cheap end of family E and not a new family.

*Treewidth.* On the 209 gap instances with exact treewidth, where
`optimum > tw + 1` on 142: `spectral > tw + 1` on **0** (every family),
`Theorem-1 graph > tw + 2` on 0 (as §1(ii) proves), maximum of
`spectral − (tw + 1)` is 0. Over all 50,949 instances the spectral value is
above `tw_lo + 1` on 1.5% — all where `tw_lo` is the lower end of an
unresolved interval. The spectral family does not see `pw > tw` on any
instance where that fact is known.

## 4. Literature

Used (open, read for this measurement; none downloaded into `literature/`,
entries in `literature/MISSING.md` under *Spectral bounds on vertex
separation (2026-11-10)*):

- Helmberg, Mohar, Poljak & Rendl (1995), *Linear and Multilinear Algebra*
  39, 73–90, doi:10.1080/03081089508818381; open reprint at Mohar's site.
  Theorem 1 (the cut bound), Theorem 8 (bandwidth; a bandwidth bound is *not*
  a pathwidth bound, `pw ≤ bw`, and was not used), **Theorem 11 eq. (20)**
  (Theorem 2 here), eq. (21) quoting Mohar & Poljak (Theorem 1 here), eq. (22)
  on when (20) beats (21).
- Gima, Hanaka, Noro, Ono & Otachi (2025), *IPL* 188, 106536 (held,
  `literature/2024-Gima-...-arXiv.pdf`): Theorem 3.4
  `tw ≥ nλ₂/(Δ+λ₂) − 1`, Lemma 4.1 (Gu & Liu; Theorem 3 here), Theorem 4.2
  `tw ≥ 2nλ₂/(3λₙ − λ₂) − 1`, Remark 3.5 (`K_{p,q}`).
- Díaz, Petit & Serna (2002), *ACM Computing Surveys* 34(3), §9.2, Theorems
  9.2–9.4 (held): Mohar–Poljak's separator bound and the Juvan–Mohar
  MINLA / cutwidth / bisection bounds (the cutwidth route
  `cw ≤ pw · Δ` with `MINLA ≥ λ₂(n² − 1)/6` gives `pw ≥ λ₂(n² − 1)/(6nΔ)`,
  weaker than Theorem 1 at the balanced prefix by a factor of about 6; not
  implemented).
- Harper (1966) for the bound the spectral one relaxes; Kinnersley (1992) for
  `vs = pw`.
- Recorded to obtain: Gu & Liu (2022), *EJC* 101, 103468; Chen, Wu & Li
  (2027), "An improved spectral lower bound for treewidth", *IPL* 195,
  106657 (title and venue from Crossref; abstract unreadable, no arXiv
  version found); Mohar & Poljak (1993); Juvan & Mohar (1992); Alon & Milman
  (1985).

The web search found no published eigenvalue bound stated for vertex
separation or pathwidth itself: every spectral statement is on one separator,
on bandwidth / cutwidth / linear arrangement, or on treewidth through one
balanced separator. The prefix form (Theorem 4) is the obvious transfer; we
found no prior statement of it and do not claim it as new.

## 5. Regenerate

    nice -n 19 python3 -m learning.spectral_bound --stage check --workers 4      # §2, ~1.4 core-h
    nice -n 19 python3 -m learning.spectral_bound --stage validity --workers 4   # §3, ~1.7 core-h
    nice -n 19 python3 -m learning.spectral_bound --stage tables                 # reports/scratch/spectral_bound/tables.md
    python3 -m pytest tests/test_spectral_bound.py -q                             # 15 tests

No solver change: nothing here reaches `satisfiability.mosp_solver._lower_bound`.
