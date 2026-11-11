# The second moment on layouts: can counting narrow orderings lower the upper end of the sandwich?

*2026-11-11, one session. Code `learning/layout_moment.py` (+ `layout_moment.c`,
`layout_moment_enum.c`), tests `tests/test_layout_moment.py` (18), Lean
`lean/MOSPFormalization/LayoutMoment.lean`, data and logs under
`reports/scratch/layout_second_moment/`, literature in `literature/MISSING.md` under
"Second moment on layouts (2026-11-11)". Every number is beside its command in §6.*

## 0. Summary

**The question.** Our sandwich on `pw(G(n, c/n))/n` has the first-moment constant `β*(c)`
below (empty pairs; `0.009, 0.171, 0.337` at `c = 3, 6, 10`, best valid floors `0.037,
0.182, 0.345` after the separator and closed-pair counts) and the degree-sequence bound of
Edwards & McDermid (2015) above (`0.183, 0.458, 0.656`), with the fitted slopes near the
middle (`0.099, 0.268, 0.415`). The owner asked whether the **second moment on the number
of narrow layouts** can lower the upper end: `X_w` = the number of vertex orderings of
width `≤ w` (every prefix `S_t` has `|N(S_t) ∖ S_t| ≤ w`), `P(pw ≤ w) ≥ E[X_w]² / E[X_w²]`,
so a bounded ratio at a width `w = β₁ n` where `E[X_w] → ∞` gives `pw ≤ β₁ n` whp.

**The chain (§1).** For a fixed ordering of `G(n, p)` the open count `k_t = |N(S_t) ∖ S_t|`
is a Markov chain in `(t, k)` and nothing else: the vertex placed at step `t` is open with
probability `k/(n − t + 1)` (given the history, which is a symmetric function of the
suffix vertices' edge vectors into the prefix, those vectors are exchangeable), and each
still-closed suffix vertex then opens with probability `p` through its fresh edge to the
placed vertex; the number of closed suffix vertices is `n − t − k`. So
`q(n, p, w) = P(a fixed ordering has width ≤ w)` is an `O(n w²)` DP and
**`E[X_w] = n! · q(n, p, w)`**, exactly. **Checked with zero discrepancies**: in exact
rational arithmetic against every labelled graph on `n ≤ 7` vertices (`2^21` graphs at
seven, the narrow orderings of each counted by a subset DP that knows nothing of the chain)
and against the isomorphism-class enumeration on `n ≤ 10` (`12,005,168` classes at ten,
`nauty-geng` + `nauty-countg --a`), every `w`, four values of `p` each.

**The first moment of layouts, as a bound (§2).** As a *lower* bound on the pathwidth
(`P(pw ≤ w) ≤ E[X_w]`) it loses to the empty pair everywhere, as expected, and by a lot: the
`n!` is `e^{n ln n}` while a narrow ordering costs only `e^{Θ(n)}` at `p = c/n` (the empty
graph alone has `E[X_0] = n! e^{−c(n−1)/2} → ∞`), so `E[X_0] ≥ 1` already at `n = 20` for
`c = 3` and `4`, at `n ≈ 60` for `c = 6`, `≈ 160` for `c = 8`, `≈ 500` for `c = 10`: **`β₁(c, n)
= 0` from there on**, and the layout count excludes `w ≤ 7` where the empty pair excludes
`w ≤ 23` (`n = 60`, `c = 10`); at `p = ½` it reaches `n − w = 29` against the empty pair's `17`
(`n = 60`). As the threshold for the *upper*-bound reading, `β₁(c, n) → 0` in the sparse
regime, so "`w = β₁ n`" is the empty graph's width and the second-moment question there is
about any fixed `β > 0`. Two by-products: the width of a *uniformly random* ordering is
`max_t (n − t)(1 − (1 − p)^t)`, hence `pw ≤ (β_typ(c) + o(1)) n` whp with
`β_typ(c) = max_x (1 − x)(1 − e^{−cx})` — `0.423, 0.586, 0.694` at `c = 3, 6, 10`, worse than
Edwards & McDermid there, but **better than it from `c = 14.42` on** (`0.808` against
`0.826` at `c = 20`, `0.903` against `0.930` at `50`): a trivial bound that beats the published
one at large `c`. And the first moment of layouts above `β_typ` is trivially `≥ 1`, which is
where the second moment "works" and says nothing.

**The second moment, sparse: dead (§3).** Exactly at `n ≤ 10`: at `w = β₁(c, n)·n` the ratio
`E[X_w²]/E[X_w]²` is `10.0, 20.3, 48.2, 124, 334, 933, 2682` at `c = 3`, `n = 4..10`
(`log ratio` against `n`: slope `0.93` per vertex, `r² > 0.999`), `161, 321, 1046, 4216` at
`c = 6`, `n = 7..10` (slope `1.1`), and `2.2 … 25,192` at `p = ½`. **The kill criterion
(exponential growth of the ratio at `w = β₁ n`) is met.** Since `n ≤ 10` is not sparse
(`p = c/n ≥ 0.3`), the same chain carrying the edge count gives a *rigorous* lower bound on
the ratio at any `n`: with `Y = e(G)`, `E[X²] ≥ Σ_e P(e) E[X | e]²` (Jensen) and
`E[X | e] = n! q_e` by symmetry, so `E[X²]/E[X]² ≥ Σ_e P(e) q_e² / (Σ_e P(e) q_e)²`, computed
exactly to `n = 100`. It is **exponential at every width below the random-ordering width**,
with rate equal (to 10–30%) to the binomial KL rate of the planted edge count — the
graph conditioned on one narrow ordering is atypically sparse, and that alone is a lottery:
at Edwards–McDermid's `β = 0.183`, `c = 3`, the bound is `≥ e^{0.175 n}` (planted edge
count `0.58` of typical); at `β = 0.458`, `c = 6`, `e^{0.028 n}`; at `β = 0.5`, `c = 10`,
`e^{0.09 n}`; the rate vanishes only as `β → β_typ(c)`. So the plain second moment on
layouts cannot prove anything below the width of a random ordering, which is the trivial
bound. The weighted cures of the literature (Achlioptas–Peres, Dani–Moore) would have to
cancel a drift of the whole open-count trajectory, not of one statistic; not attempted.

**The second moment, dense: alive but undecided (§3.4).** At `p` fixed the forced
structure is `O(log² n)` non-edges, the edge-count lottery vanishes (the Jensen bound at
`w = n − a log_b n` *decreases* with `n`: `2.4 → 0.6` for `a = 2`, `16 → 5.2` for `a = 3`,
`53 → 19.5` for `a = 4`, `n = 30 → 100`), and `pw ≤ n − s` is **exactly** the existence of a
*staircase*: distinct `v_1..v_{s−1}`, `u_1..u_{s−1}` with `u_i` non-adjacent to `v_1..v_{s−i}`
(§3.4, both directions). Its ordered count has `E = (n)_{2s−2} (1 − p)^{s(s−1)/2}`, threshold
`s = (4 − o(1)) log_b n` — Theorem B's constant, and `s₀/log₂ n = 3.96` at `n = 10⁶` — so a
second moment on staircases that works to the threshold would give
`n − pw(G(n, p)) = (4 + o(1)) log_b n`, closing the dense sandwich `[2, 4]` at `4`. The
outline is clean (an `O(log n)`-vertex structure; overlap terms `n^{−j} b^{cost(j)}` with
`cost(j) ≤ j²/8`, convex in `j`, bounded at both ends for `a < 4`), the data are consistent
(`n − pw = 11, 12, 13, 14` at `n = 30..60`, within `2–3` of the exact empty-pair floor and
above `2 log₂ n`), and the full computation is a paper-sized item, not attempted here;
it is the one place where a second moment on layouts is not dead.

**Lean (§4).** `LayoutMoment.lean`, no `sorry`, axioms `propext`, `Classical.choice`,
`Quot.sound` only: the symmetry `∑_G gnpWeight p G · X_w(G) = n! · narrowWeight p σ₀ w`
(`expected_narrowLayouts`; transport of a layout along a relabelling,
`vertexSepOfLayout_comap_relabel`, and of the weight, `gnpWeight_comap`); **the
independence lemma** `sum_gnpWeight_pattern` (the edges at a set `F` of pairs are
independent of every event determined outside `F`: the weight of the graphs of `E` with
pattern `F₊` on `F` is `p^|F₊| (1 − p)^(|F| − |F₊|)` times the weight of `E`), which is the
step the chain takes at every position and generalises `sum_gnpWeight_emptyPairGraphs`;
the chain `chainQ` as a computable recursion over any field, evaluated on rationals on all
28 pairs `(n, w)`, `n ≤ 7`, three `p` each, equal to the Python chain; and the identity
`narrowWeight p σ w = chainQ n p w` **stated as a `Prop` (`ChainIdentity`), not proved** —
the finite-sum formalisation of the exchangeability argument is more than a day.

**Literature (§5).** We found no second moment on the number of layouts or path
decompositions of bounded width in any random graph model, no expected width of a random
ordering, no prior statement of the chain, and no pathwidth upper bound on `G(n, c/n)`
other than Edwards & McDermid; the template second moments (Achlioptas–Naor,
Achlioptas–Peres, Dani–Moore, Coja-Oghlan et al.) each document the failure measured here
and cure it by balancing, weighting or symmetry. Thirteen papers recorded in `MISSING.md`.

**Nothing re-solved**; `solutions/` untouched; no pathwidth run; about 1 core-hour
(the `n = 10` enumeration 8 × 3 min, the edge-marked chain to `n = 100`).

---

## 1. The chain

Fix an ordering `v_1, …, v_n` and expose, at step `t`, the edges from `v_t` to the suffix
`v_{t+1}, …, v_n`. A suffix vertex is *open* at step `t` if it has an edge into
`S_t = {v_1..v_t}`; `k_t` is the number of open suffix vertices.

*State.* After step `t` the exposed information about a suffix vertex `v_j` is its edge
vector into `S_t`, i.i.d. across `j > t` (each coordinate Bernoulli(`p`)). The history
`(k_1, …, k_t)` is a symmetric function of these vectors (and of the vectors of the vertices
already placed, which are independent of them), so conditionally on the history the open
indicators of the suffix vertices are exchangeable with `k_t` ones: `v_{t+1}` is open with
probability `k_t / (n − t)`. Its removal leaves `k_t − O` open and `(n − t − 1) − (k_t − O)`
closed suffix vertices; each closed one opens through the fresh edge `(v_{t+1}, v_j)`,
independently with probability `p` (the edges from `v_{t+1}` to the already-open ones are
free and do not matter). So `k_{t+1} = k_t − O + Bin(n − t − 1 − k_t + O, p)` and
`(t, k)` is the whole state. The width condition truncates the chain at `k ≤ w`;
`q(n, p, w)` is the surviving mass at `t = n` (where `k_n = 0`), `E[X_w] = n! q`.

*Implementation.* `chain_log_q` (C, long double with a running scale, `O(n w²)`), the exact
rational `chain_q_exact` (Python `Fraction`), and `chainQ` in Lean (§4). The chain carrying
the edge count, `chain_edge_profile`, has state `(t, k, e)` and returns
`log P(narrow ∧ e(G) = e)`; the edges to the already-open suffix vertices are counted as
free Bernoulli(`p`) draws.

*The check.* `labelled_tables(n)` enumerates all `2^C(n,2)` labelled graphs on `n ≤ 7`
vertices and, for each, the number of orderings of width `≤ w` for every `w` by the
subset DP (paths through the subsets `S` with `|N(S) ∖ S| ≤ w`), accumulating
`T₁[e][w] = Σ_{e(G) = e} X_w(G)` and `T₂[e][w] = Σ X_w(G)²` as integers, so that
`E[X_w^j] = Σ_e p^e (1 − p)^(C − e) T_j[e][w]` is exact for rational `p`.
`learning/layout_moment_enum.c` does the same by isomorphism classes (`nauty-geng`; the
class carries `n!/|Aut|` labelled graphs, `|Aut|` from `nauty-countg -V --a`) to `n = 10`.
Results: `T₁, T₂` labelled = classes at `n = 4..7` (bit for bit); `E[X_w] = n! q` exactly
for every `w` and `p ∈ {½, 3/10, 1/7, 3/n}` at every `n = 4..10` (**0 discrepancies**; the
total `Σ_e T₁[e][n−1] = n! 2^C` at every `n`, e.g. `127,677,049,435,953,561,600` at ten).

## 2. The first moment of layouts

### 2.1 `β₁(c, n)`, the least `w/n` with `E[X_w] ≥ 1` (`beta1_sparse.csv`)

| `c` | `n = 20` | 40 | 60 | 80 | 120 | 200 | 400 | 800 | 1600 | 3200 | `β_typ(n = 3200)` |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 3 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0.423 |
| 4 | 0.050 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0.491 |
| 6 | 0.150 | 0.025 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0.586 |
| 8 | 0.250 | 0.100 | 0.067 | 0.038 | 0.008 | 0 | 0 | 0 | 0 | 0 | 0.649 |
| 10 | 0.350 | 0.175 | 0.133 | 0.100 | 0.058 | 0.025 | 0.003 | 0 | 0 | 0 | 0.694 |
| 20 | — | 0.450 | 0.383 | 0.350 | 0.292 | 0.245 | 0.190 | 0.144 | 0.105 | 0.073 | 0.808 |

`log E[X_0] = log n! + C(n,2) log(1 − c/n)`: `11.5` at `(c, n) = (3, 20)`, `2.1` at `(6, 60)`,
`−34.8 / +50.9` at `(8, 120 / 200)`, `−19.9 / +532` at `(10, 400 / 800)`. The limit of
`β₁(c, n)` is `0` for every `c`: the layout first moment carries `n!` against an `e^{Θ(n)}`
cost, so its "threshold" is the empty graph. This is the expected outcome and it is sharp:
nothing about layouts survives the factorial in the sparse regime.

### 2.2 As a lower bound: against the empty pair (`reports/random_graph_first_moment.md` §5)

| `n` | `c` | largest `w` with `E[X_w] < 1` | empty pair: largest `k` with `B < 1` |
|---|---|---|---|
| 60 | 3 / 4 / 6 / 8 / 10 | none / none / none / 3 / 7 | 1 / 5 / 11 / 17 / 23 |
| 120 | 3 / 4 / 6 / 8 / 10 | none / none / none / 0 / 6 | 1 / 9 / 21 / 33 / 43 |
| 60 | `p = ½` | 31 (`n − w = 29`) | 43 (`n − k = 17`) |
| 120 | `p = ½` | 77 (`n − w = 43`) | 101 (`n − k = 19`) |

In the dense regime `E[X_{n−s}] ≥ 1` for `s ≲ 2√(n ln n / ln b)` (`123` at `n = 800`, `p = ½`;
`beta1_dense.csv`) where the pathwidth is `n − Θ(log n)`: the layout first moment is a
lower bound on nothing useful, in either regime. It carries the same necessary condition
as the empty pair (a narrow ordering contains one) multiplied by the orderings that
realise it.

### 2.3 The width of a random ordering

`E[k_t] = (n − t)(1 − (1 − p)^t)` exactly (each suffix vertex is open independently), and
`k_t` is binomial, so `P(the identity has width ≤ max_t E[k_t] + εn) → 1` by Chernoff and a
union over `t`: **`pw(G(n, c/n)) ≤ (β_typ(c) + ε) n` whp**, `β_typ(c) = max_x (1 − x)(1 − e^{−cx})`,
attained at `x* ≈ (ln c)/c` for large `c`, `β_typ = 1 − (1 + ln c + o(1))/c`.

| `c` | 3 | 4 | 6 | 8 | 10 | 14.42 | 20 | 50 | 100 |
|---|---|---|---|---|---|---|---|---|---|
| `β_typ(c)` | 0.4227 | 0.491 | 0.5858 | 0.6487 | 0.6936 | 0.757 | **0.808** | **0.9034** | **0.9444** |
| Edwards–McDermid (Poisson) | 0.1826 | 0.2853 | 0.4575 | 0.5761 | 0.6558 | 0.757 | 0.8255 | 0.930 | 0.965 |

The uniformly random ordering beats the published degree-sequence bound from
`c = 14.42` on (`learning.edwards_mcdermid.poisson_value`; Brent on the difference). At
`p` fixed it gives `n − pw ≥ log_b n + O(1)`, half the independence bound's `2 log_b n`.
(The random ordering is the worst reasonable layout; any greedy would do better, and a
second moment at `β_typ` is trivial because `q → 1` there.)

## 3. The second moment

### 3.1 Exact, `n ≤ 10` (`exact_ratio.csv`)

`E[X_w²]/E[X_w]²` from the enumeration tables at `w₁ = β₁(c, n)·n` (the least `w` with
`E[X_w] ≥ 1`), with `E[X_{w₁}]` and the random-ordering width:

| cell | `n` | `w₁` | `E[X_{w₁}]` | ratio | `β_typ(n)` |
|---|---|---|---|---|---|
| `c = 3` | 4 / 5 / 6 / 7 / 8 / 9 / 10 | 1 | 1.2 / 2.4 / 5.1 / 11.7 / 29.5 / 81.6 / 245 | **10.0 / 20.3 / 48.2 / 124 / 334 / 933 / 2,682** | 0.56 … 0.46 |
| `c = 6` | 7 / 8 / 9 / 10 | 3 | 1.9 / 4.7 / 7.8 / 12.1 | **161 / 321 / 1,046 / 4,216** | 0.74 … 0.67 |
| `p = ½` | 4 / 5 / 6 / 7 | 1 | 7.5 / 8.0 / 5.1 / 1.9 | 2.2 / 7.6 / 48 / 581 | 0.38 … 0.54 |
| `p = ½` | 8 / 9 / 10 | 2 | 64 / 21.6 / 4.0 | 81 / 1,044 / 25,192 | 0.56 … 0.61 |

Fit of `log ratio` against `n` at `w₁`: slope `0.93` per vertex at `c = 3` (`n = 4..10`),
`1.1` at `c = 6` (`n = 7..10`); at `p = ½` with `w₁` fixed, `1.7` (`w₁ = 1`) and `2.9`
(`w₁ = 2`). **Kill criterion met: exponential.** At fixed `β = w/n` the exact ratio is
flat only above `β_typ` (`log ratio < 0.05` at `β ≥ 0.7`, `c = 3`; `≥ 0.8`, `p = ½`). The
caveat is that `n ≤ 10` with `p = c/n` is dense, which is why §3.2 goes to `n = 100`.

### 3.2 A rigorous lower bound on the ratio at any `n`, from the edge count

With `Y = e(G)`: `E[X²] = Σ_e P(e) E[X² | e] ≥ Σ_e P(e) E[X | e]²`, and conditionally on
`e` the graph is uniform on the graphs with `e` edges, a permutation-invariant law, so
`E[X | e] = n! q_e` with `q_e = P(identity narrow | e)`. Hence

    E[X_w²] / E[X_w]² ≥ R(n, p, w) := Σ_e P(e) q_e² / (Σ_e P(e) q_e)²,

and `P(e) q_e = P(narrow ∧ e(G) = e)` is what the edge-marked chain returns. (`R` is the
planted mean of `q_e` over the typical mean: `R = E_μ[q_e] / E_P[q_e]` with `μ(e) ∝ P(e) q_e`.)
Checked: `log R ≤ log` of the exact ratio on every `(n ≤ 10, p, w)`, with equality at `w = 0`
(`X_0 = n! 1[G empty]`, ratio `1/P(empty) = (1 − p)^{−C}`, a test).

| `c` | `β` | `log R` at `n = 20 / 40 / 60 / 80 / 100` | slope (n ≥ 40) | KL rate of the planted edge count | planted / typical edges (n = 100) |
|---|---|---|---|---|---|
| 3 | 0.10 | 12.7 / 21.9 / 30.6 / 39.0 / 47.3 | **0.422** | 0.368 | 0.39 |
| 3 | 0.183 (E&M) | 5.6 / 11.3 / 14.3 / 17.2 / 22.1 | **0.175** | 0.160 | 0.58 |
| 3 | 0.30 | 2.1 / 3.0 / 3.9 / 4.6 / 5.4 | 0.039 | 0.036 | 0.79 |
| 3 | 0.40 | 0.57 / 0.62 / 0.66 / 0.69 / 0.72 | 0.002 | 0.004 | 0.93 |
| 6 | 0.20 | 18.8 / 30.4 / 41.8 / 53.0 / 64.1 | **0.561** | 0.459 | 0.51 |
| 6 | 0.40 | 4.2 / 5.9 / 7.6 / 9.3 / 11.0 | 0.084 | 0.069 | 0.80 |
| 6 | 0.458 (E&M) | 2.5 / 3.4 / 4.2 / 4.2 / 5.0 | **0.028** | 0.031 | 0.86 |
| 6 | 0.55 | 0.67 / 0.68 / 0.73 / 0.79 / 0.84 | 0.004 | 0.005 | 0.95 |
| 10 | 0.35 | 18.9 / 25.9 / 34.2 / 42.4 / 50.7 | **0.432** | 0.325 | 0.68 |
| 10 | 0.415 (slope) | 13.4 / 14.4 / 19.9 / 25.4 / 28.2 | **0.237** | 0.174 | 0.76 |
| 10 | 0.50 | 5.8 / 7.0 / 8.8 / 10.6 / 12.4 | **0.090** | 0.073 | 0.84 |
| 10 | 0.60 | 1.9 / 1.9 / 2.2 / 2.6 / 2.9 | 0.016 | 0.016 | 0.92 |
| 10 | 0.656 (E&M) | 0.88 / 0.76 / 0.80 / 0.86 / 0.68 | 0.000 | 0.004 | 0.96 |

(`β_typ(n = 80) = 0.427, 0.595, 0.706`; the full grid is `jensen_sweep.csv`.) The slope
of `log R` is the KL rate `C·KL(x₁ ∥ p)/n` of the planted edge density `x₁` to within
10–30% (the finite-`n` sum has polynomial corrections), and `x₁ < p` strictly for every
`β < β_typ`: conditioning on a narrow ordering thins the graph, and the thinned graphs
carry exponentially more narrow orderings. This is the lottery effect of Achlioptas–Peres
and Dani–Moore in its simplest form, seen through one statistic; the true ratio is at
least this and (§3.1) larger. **Verdict for the sparse regime: the plain second moment on
layouts proves nothing below `β_typ(c)`, where it is trivial.**

*What a weighted count would need.* The cure in the literature is a weight that makes the
planted law typical: for `k`-SAT a factor per clause (Achlioptas–Peres), for independent
sets a factor per vertex degree (Dani–Moore). Here the planted object is the whole
trajectory `(k_t)`, not a count: the edge count is one marginal, and tilting it (a factor
`η^{e(G)}` per layout) removes only this one lottery; the next ones are the opening-time
profile and the overlap of two orderings' open sets. The clean statement is that a weight
`W(σ, G)` making `E[W X]` typical must be a function of the ordering's open-count path, and
the second moment of that is a two-chain computation (the joint law of `(k_t(σ), k_t(τ))`
over the overlap of two prefixes). Not attempted: the kill criterion was met before it.

### 3.3 Reversal and other symmetries

Reversal preserves width (the open set of a prefix is the open set of the complementary
suffix), so `X_w` counts in pairs; this does not change the ratio's growth. There is no
complement symmetry of the NAE kind: the complement of a graph of small pathwidth has
large pathwidth.

### 3.4 The dense regime: the staircase, and why the second moment is alive there

At `p` fixed and `w = n − s`, the condition `k_t ≤ n − s` reads: at least `s − t` suffix
vertices are closed at step `t`, for `t = 1..s − 1`, and nothing for `t ≥ s`. Hence

**Lemma (staircase).** `pw(G) ≤ n − s` iff there are distinct vertices `v_1..v_{s−1}` and
`u_1..u_{s−1}` with `u_i` non-adjacent to `v_1..v_{s−i}` for every `i`. (⇐: order
`v_1..v_{s−1}` first, the rest arbitrarily; at prefix `t < s` the `s − t` vertices
`u_1..u_{s−t}` are closed. ⇒: from a narrow layout pick `u_i ∈ C_{s−i}` distinct, possible
since `|C_{s−i}| ≥ i`; if some `u_i` is a later `v_j`, replace it — the all-distinct
form is the one counted and is sufficient.)

The ordered count `Y_s` of staircases has `E[Y_s] = (n)_{2s−2} (1 − p)^{s(s−1)/2}`: `2s − 2`
labelled vertices and `s(s−1)/2` forced non-edges (`Σ_i (s − i)`), so `E[Y_s] ≥ 1` iff
`s ≤ (4 − o(1)) log_b n` — Theorem B's constant, which is no accident: the empty pair of
Theorem B is the level-`s/2` slice of the staircase, with half the vertices and half the
cost. Finite thresholds at `p = ½` (`s₀` the largest `s` with `E[Y_s] ≥ 1`, beside the
exact empty-pair floor `n − k_B`, the largest `n − k` with `B < 1`, and the measured
median `n − pw` of `reports/random_graph_middle.md` §4):

| `n` | 30 | 40 | 50 | 60 | 120 | 400 | 10³ | 10⁴ | 10⁵ | 10⁶ |
|---|---|---|---|---|---|---|---|---|---|---|
| `s₀ / log₂ n` | 2.85 | 3.19 | 3.37 | 3.56 | 3.76 | 3.93 | 3.91 | 3.99 | 3.97 | 3.96 |
| `(n − k_B) / log₂ n` | 2.65 | 2.82 | 2.66 | 2.88 | 2.75 | 2.89 | 3.11 | 3.09 | 3.19 | 3.26 |
| measured `(n − pw) / log₂ n` | 2.24 | 2.25 | 2.30 | 2.37 | | | | | | |
| measured `n − pw` (median) | 11 | 12 | 13 | 14 | | | | | | |

Both ratios tend to `4` (the empty pair's `n − 4 log_b n + 4 log_b log n`-type corrections
are slow; the ordered count's `(s!)²`-type ones faster), and the measured `n − pw` sits
`2–3` below the exact floor at every `n` and *above* `2 log₂ n` (`9.8 … 11.8`): the data are
consistent with the floor being tight, i.e. with the constant `4`, and cannot settle it.

*The second moment on `Y_s`.* `E[Y_s²]/E[Y_s]² = Σ_j (terms with `j` shared vertices)`,
each `≈ n^{−j} b^{cost_shared(j)}` relative to `E[Y_s]²`, with `cost_shared(j) ≤ j²/8` (a
sub-staircase on `j` vertices has `j/2` prefix and `j/2` witness vertices and cost
`(j/2)²/2`). At `s = a log_b n`, the term is `n^{−j + j²/(8 log_b n)}`, convex in `j`, so the
sum is dominated by its ends: `j = 0` (the term `1`) and `j = 2s − 2` (the term
`1/E[Y_s] → 0` for `a < 4`); the middle terms are `n^{−j(1 − j/(8 log_b n))} ≤ n^{−j(1 − a/4)}`
and sum to `O(n^{−(1 − a/4)})`. This is the clique / biclique second moment in a
triangular pattern, and if it holds with the roles (the `v`'s are ordered, the shared
vertices may play different roles in the two staircases, and the witnesses' distinctness
constrains the overlaps) then **`pw(G(n, p)) ≤ n − (4 − ε) log_b n` whp for every `ε > 0`**,
and with Theorem B, `n − pw(G(n, p)) = (4 + o(1)) log_b n`, closing the dense sandwich of
`reports/random_graph_middle.md` at its lower end `4` (the independence bound's `2` would
then be loose by a factor two, as it is for bandwidth's lower bound of Turner). Evidence
for, not proof: the Jensen bound (§3.2) at `w = n − a log_b n` is *bounded* and
decreasing — `log R = 2.40, 2.06, 1.30, 1.04, 0.63` (`a = 2`), `16.0, 12.1, 9.2, 6.6, 5.2`
(`a = 3`), `53.0, 38.4, 31.5, 21.7, 19.5` (`a = 4`) at `n = 30, 40, 60, 80, 100` — so no
lottery through the edge count; and the structural bound `E[X | σ₀ narrow] ≥ (n − s)!`
gives `ratio ≥ n^{(a/2 − 2) s}`, uninformative for `a < 4`. What is *not* done: the
role-aware overlap sum (a paper-sized computation of the Matula / Bollobás–Erdős kind) and
its lower-order terms; the `n ≤ 10` exact tables cannot see the regime (`4 log₂ 10 > 10`).
**Proposed as the next item, with its kill criterion**: evaluate the overlap sum exactly
at `n = 10³–10⁴`, `s = (4 − ε) log_b n`; the route is dead if some middle term exceeds `1`
(then a balanced or unordered count is needed, à la Achlioptas–Naor), alive if the sum
is `1 + o(1)`, in which case the theorem follows by Paley–Zygmund, and the staircase lemma
goes to Lean first.

## 4. Lean

`lean/MOSPFormalization/LayoutMoment.lean` (imports `FirstMoment`, `VertexSeparation`;
registered in `MOSPFormalization.lean`); `lake build` passes; `#print axioms` on
`expected_narrowLayouts`, `narrowWeight_eq`, `sum_gnpWeight_pattern`,
`vertexSepOfLayout_comap_relabel`, `gnpWeight_comap`: `propext`, `Classical.choice`,
`Quot.sound` (`lean_check.log`).

| name | statement |
|---|---|
| `relabel σ τ : V ≃ V` | `τ (relabel σ τ v) = σ v` |
| `prefixSet_relabel`, `activeSuffix_comap_relabel`, `vertexSepAt_comap_relabel` | the prefix, the active suffix and the separation at every position transport along `G ↦ G.comap (relabel σ τ).symm` |
| `vertexSepOfLayout_comap_relabel` | `vs(G.comap φ.symm, τ) = vs(G, σ)` |
| `edges_comap`, `card_edges_comap`, `gnpWeight_comap` | the edge set maps by `Sym2.map φ`; the weight is preserved |
| `comapEquiv φ : SimpleGraph V ≃ SimpleGraph V` | pulling back along a bijection is a bijection of graphs |
| `narrowWeight p σ w` | `∑_G gnpWeight p G · 1[vs(G, σ) ≤ w]`; `narrowWeight_eq`: the same for every `σ` |
| **`expected_narrowLayouts`** | `∑_G gnpWeight p G · #(narrowLayouts G w) = |V|! · narrowWeight p σ₀ w` |
| `DeterminedOutside E F`, `patternGraphs E F F₊`, `freeCore E F` | events determined outside `F`; the graphs of `E` with pattern `F₊` on `F`; the free edge sets |
| `sum_patternGraphs_eq`, `sum_graphs_eq`, `edgeWeight_union` | both sides through the core, by explicit bijections (`sum_nbij'`) and the binomial theorem |
| **`sum_gnpWeight_pattern`** | `∑_{patternGraphs E F F₊} gnpWeight = p^|F₊| (1 − p)^(|F| − |F₊|) · ∑_E gnpWeight` for `F ⊆ edges ⊤`, `F₊ ⊆ F`, `E` determined outside `F` |
| `binomPmf`, `chainStep`, `chainVec`, `chainQ` | the chain over any field, computable; `#eval` on `ℚ` equals `chain_q_exact` on all 28 `(n, w)`, `n ≤ 7`, at `p = ½, 3/10, 1/7` (0 mismatches; a truncated-subtraction slip in the first draft, `n − t − k + 1` for `n − t + 1 − k`, was caught by this check) |
| `ChainIdentity V p : Prop` | `∀ σ w, narrowWeight p σ w = chainQ |V| p w` — **stated, not proved** |

The proof of `ChainIdentity` on paper: condition on the opening times `T_j` of the suffix
vertices (independent truncated geometrics of parameter `p` on the prefix positions), the
open count is `k_t = #{j > t : T_j ≤ t}`, and the chain's transition is the exchangeability
of the `T_j` given `(k_1..k_t)`; the independence lemma is the step that exposes the edges
`(v_t, v_j)`. A finite-sum formalisation needs the opening times as a function on graphs,
the exchangeability as a sum over permutations of the suffix, and an induction on `t`
carrying the joint law — more than a day, left open.

## 5. Literature

Search by an agent (25 searches, abstract pages only, nothing downloaded; the one held
PDF, Díaz, Petit, Serna & Trevisan 2001, read in full); the entries are in
`literature/MISSING.md` under "Second moment on layouts (2026-11-11)". The verdict:
**we found no statement** of a second moment on the number of layouts or path
decompositions of bounded width in any random model, of the expected width of a random
ordering, of the open-count chain, of a cutwidth / vertex-separation / pathwidth result on
random regular graphs, or of a pathwidth upper bound on `G(n, c/n)` other than Edwards &
McDermid (2015). What is in print and used here: the template second moments —
Achlioptas & Naor 2005 (balanced colourings; the overlap-matrix sum), Achlioptas & Peres
2004 ("the vanilla second moment fails"; the per-clause weight), Dani & Moore 2011 (the
degree-weighted count for independent sets, whose failure mode — the planted graph is
locally sparser — is the one measured in §3.2), Achlioptas & Moore 2006 (complement
symmetry), Kemkes–Pérez-Giménez–Wormald 2010 (small subgraph conditioning, for a ratio
tending to a constant, not our case), Coja-Oghlan & Efthymiou 2015 (why the second moment
fails for the independence number and Frieze's concentration bridge), Coja-Oghlan &
Zdeborová 2012 and Coja-Oghlan & Vilenchik 2013 (condensation: a lottery no weighting
removes), Coja-Oghlan & Panagiotou 2012/2013 (cluster counts), Gerencsér & Harangi 2025
(the boosted second moment); Díaz et al. 2001's Lemma 3 is the `(1/2 − ε) n` floor for every
layout of a mixing graph, the only statement on the cost of an arbitrary ordering we
found. The staircase of §3.4 in the dense regime is, in the complement, a triangular
biclique; the biclique second moment is classical and is the model for the proposed item.

## 6. Regenerate

```
# the chain against brute force (every labelled graph to 7) and the enumeration to 10
python -m pytest tests/test_layout_moment.py -q                      # 18 tests, < 1 s
cd reports/scratch/layout_second_moment && for n in 4 5 6 7 8 9; do nauty-geng -q $n > bin/g$n.g6; \
  nauty-countg -V --a -2 -q bin/g$n.g6 | awk '{print $4}' > bin/a$n.txt; \
  bin/layout_moment_enum $n bin/g$n.g6 bin/a$n.txt > enum_n$n.csv; done     # n = 9: 2 s
bin/run10.sh                                                         # n = 10 in 8 parts, ~3 min each at nice 19
gcc -O3 -march=native -o bin/layout_moment_enum ../../../learning/layout_moment_enum.c
# beta1, the typical width, the Jensen bound
python -m learning.layout_moment beta1    > beta1.log                 # beta1_sparse.csv, beta1_dense.csv (~1 h for n to 3200)
python -m learning.layout_moment jensen   > jensen.log                # jensen_ratio.csv
python jensen_sweep.py > jensen_sweep.log                             # jensen_sweep.csv, jensen_dense.csv (~20 min)
python jensen_dense_log.py > jensen_dense_log.log                     # jensen_dense_log.csv (~25 min)
# the exact ratio to n = 10 and the fits: the inline script of the session, output exact_ratio.csv
# Lean
cd lean && taskset -c 16-23 lake build MOSPFormalization.LayoutMoment
lake env lean ../reports/scratch/layout_second_moment/lean_check.lean > ../reports/scratch/layout_second_moment/lean_check.log
```

## 7. What remains

1. **The staircase second moment in the dense regime** (§3.4): the role-aware overlap sum
   at `s = (4 − ε) log_b n`, with its kill criterion; if it holds, `n − pw(G(n, p)) =
   (4 + o(1)) log_b n`, a sharp constant where the record has `[2, 4]`. The staircase lemma
   (both directions) is a deterministic statement for Lean first.
2. `ChainIdentity` in Lean (§4), the exchangeability argument as a finite sum.
3. The random-ordering bound `pw ≤ β_typ(c) n` whp as a Lean theorem is a Chernoff bound
   away (`FirstMomentAsymptotics` has the tools); worth it only for the paper's table,
   where it replaces Edwards & McDermid as the upper line for `c ≥ 14.42`.
4. Nothing on the sparse constants: the plain second moment on layouts is dead there, and
   a weighted one would have to tilt the whole trajectory; the separator and closed-pair
   counts of `reports/separator_moment.md` remain the best valid floors.
