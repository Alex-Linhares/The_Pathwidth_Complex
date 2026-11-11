# Gaspers' Gaussian sweep on the open cubic cages

*2026-11-11. Code `learning/gaspers_sweep.py` (65 tests, `tests/test_gaspers_sweep.py`);
runs and layouts under `reports/scratch/gaspers_cages/`; the paper is held,
`literature/2026-Gaspers-Path-Decompositions-Sparse-Graphs-Gaussian-Sweeps-arXiv.pdf`,
and its `literature/MISSING.md` entry is rewritten. Nothing under `solutions/` or
`paper1/data/dataset/` was touched.*

## 0. Summary

**The paper.** Gaspers (arXiv 2611.05146, 3 November 2026; held since today)
proves `pw ≤ c₃ n + o(n)`, `c₃ = (3/(4π)) arccos(5/6) ≈ 0.13982`, for every
graph of maximum degree 3, closing Fomin & Høie's `n/6`. The construction is a
**threshold sweep through a correlated Gaussian labelling**: independent
standard normals, one per vertex; the label of `v` is the normalised sum of
`2^{−dist(v,w)/2} Z_w` over the ball of radius `R`; the bags are the frontiers
of the sublevel sets; for degree 3 the layout keeps *inner* frontiers below
the median and *outer* frontiers above it, joined by a connector (§1.1). It is
not a projection sweep and not a greedy. The existence proof is Chebyshev plus
a union bound (§1.2); Section 10 derandomises it in `n^{2+o(1)}` (Las Vegas
`n^{1+o(1)}`). The **lower bound** `pw ≥ 0.103295 n − 2` a.a.s. for random
cubic graphs is not the paper's: it is Lichev & Mitsche's first-moment
*bisection* bound carried through `bw ≤ cw ≤ pw + 2` — the cutwidth route of
`reports/complex_lb_search.md` §4.1, now in print (§1.4).

**The bound says nothing at 90–126 vertices.** The remainder of Theorem 8.1
is not explicit; its proof's own union-bound condition admits no parameter
below `n ≈ 1.9 × 10⁷`, and the one explicit bound in the paper (Theorem 3.1,
`c* n + 2.55 n / R + 4 n^{7/8}`, `n ≥ 2⁴⁶`) first beats `n/6` at `n ≈ 10⁶⁹⁷`.
Sharper: the **certified floors of all five cages exceed `c₃ n`** (Foster
15 > 12.58, Tutte 12-cage 20 > 17.62), so the cages are lower bounds on the
paper's remainder, `ρ(n) ≥ 0.3–2.4` at these `n` (≥ 4.7–8.4 if the records
are optimal), and three floors exceed `n/6` too (§1.3). The experiment is
therefore a heuristic, as the brief anticipated.

**The experiment.** `learning/gaspers_sweep.py` builds the labels, both
plain layouts (Lemma 4.1) and the median-switched layout (Lemmas 8.3–8.5,
turned into a layout by first-bag order), with random restarts in place of
the concentration step; every width is the vertex separation of a layout,
recomputed by code that shares nothing with the construction. 65 tests; on
Petersen, Heawood, Pappus, McGee and Tutte–Coxeter the sweep never reports
below the certified value and reaches it on four of the five (§2). Two
batches of 20,000 restarts per cage (radii 1–6 then 4–8, the switch at
quantiles 0.15–0.7; about 20 min each at nice 19), then the C program from
the best layout for 600 s (§3). The median-switched layout beats both plain
sweeps on every graph by 1–2 in the minimum and 4–5 in the mean, and
switching *below* the median (quantile 0.15–0.3) beats the paper's median
by about 1 — a finite-size effect of the first-bag conversion, not a claim
about the constant.

| graph (id) | `n` | record | certified floor | `c₃ n` | best sweep (rule, `R`) | after the C program (600 s) | verified vertex separation | record moved? |
|---|---|---|---|---|---|---|---|---|
| Foster (pwc-15968) | 90 | 20 | 15 | 12.6 | **20** (switch 0.3, R 5) | 20 | 20 | no (equal) |
| Biggs–Smith (pwc-15936) | 102 | 19 | 16 | 14.3 | 20 (switch 0.15, R 6) | **19** | 19 | no (equal) |
| Ljubljana (pwc-16006) | 112 | 22 | 16 | 15.7 | 23 (switch 0.3, R 6) | **22** | 22 | no (equal) |
| Balaban 11-cage (pwc-15932) | 112 | 24 | 17 | 15.7 | 25 (switch 0.15, R 6) | **24** | 24 | no (equal) |
| Tutte 12-cage (pwc-16064) | 126 | 26 | 20 | 17.6 | 28 (switch 0.15, R 8) | **26** | 26 | no (equal) |

**No record moved.** The sweep alone reaches the record on Foster and sits
1–2 above it elsewhere (0.20–0.22 `n`, where the records are 0.19–0.22 `n`
and the paper's leading term 0.14 `n`); the C program started from each
sweep layout descends to exactly the recorded width within its first
engine calls and then spends the rest of its 600 s (7.5–8.4 × 10⁸ nodes
each) failing to refute `record − 1` — the same wall the records' own runs
hit. The sweep layouts are not a better starting point than what the C
program finds by itself; the open instances stay open. The four other named
graphs the brief lists are not subcubic (Dejter 6-regular, BubbleSort_5 and
NStar_5 4-regular, OddGraph_5 5-regular) and were skipped as instructed; the
plain sweep applies to the two 4-regular ones at `F₄ = 0.2458`, i.e. 29.5 on
120 vertices against records 23 and 28, so nothing was expected there either.

**Two findings about the record, not the paper.** The dataset's `layout`
field is a *closing order* (the C program's `-u` convention, the vertex
closed first first), not a textbook layout: on all 16 records read here its
reverse has exactly the recorded width and the field itself does not (§2).
And the C program's own `lower=` on these runs (13–16) is below the dataset's
floors (15–20), which come from searched minors and the spectral certificate;
a `-L` would not have changed the outcome, since no run reached `record − 1`.

Nothing re-solved; `solutions/` and the dataset untouched; about 2.2
core-hours in total (sweeps 1.7, C runs 0.8). Layouts of the recorded widths
are under `reports/scratch/gaspers_cages/c600/` (`<id>_c.log`, textbook
order); none improves on the record, so there is nothing for a dataset
rebuild to take.

## 1. What the paper proves, and what it gives at 90–126 vertices

**Gaspers, arXiv 2611.05146 (3 November 2026), 181 pages, read whole.**
Theorem 1.1(a) (= Theorem 8.1): every graph of maximum degree 3 has
`pw ≤ c₃ n + o(n)`, `c₃ = (3/(4π)) arccos(5/6) ≈ 0.13982`, closing Fomin &
Høie's `n/6 + o(n)` of 2006 (held). The same constant bounds bisection width
and cutwidth (Corollary 1.2, through `bw ≤ cw ≤ pw + 2` at maximum degree 3).
Theorem 1.1(b): `pw ≤ F₄ n + o(n)`, `F₄ ≈ 0.24577`, at maximum degree 4.
Theorem 1.3: per-degree weights `a₃ = 5/32, a₄ = 1/4, a₅ = 11/32, a₆ = 7/16`;
Corollary 1.4: `pw ≤ 7m/48 + o(n)` for every graph. Theorem 8.1 has a Lean
proof without hypotheses (Appendix B; the other bounds rest on Mulgund's
simplex theorem and ball-arithmetic certificates).

### 1.1 The construction is a sweep along a *correlated Gaussian labelling*, not a projection

It is neither a sweep along a random Gaussian projection of an embedding nor
a greedy over a potential. Every vertex `w` draws an independent standard
normal `Z_w`; the label of `v` is the normalised weighted sum

    X_v = Σ_{dist(v, w) ≤ R} 2^{−dist(v, w) / 2} Z_w,      Y_v = X_v / √Var X_v

(Definition 5.2, the *geometric* labels; base `p − 1` at maximum degree `p`,
and *mixed* arc lengths `½ ln(d(x) − 1)` when degrees differ). The decay
`2^{−dist/2}` is critical: on the 3-regular tree every sphere carries the same
weight, so the outer shell — the only part two neighbours' balls do not share
— carries `O(1/R)` of the variance, and every edge has label correlation at
least `r_R = (2√2/3)(1 − 1/R)` (Lemma 3.4 / 5.4; `2√2/3` is the norm of the
tree's adjacency operator over the degree, the Alon–Boppana test function).
A threshold `t` sweeps through the labels; `S_t = {v : Y_v ≤ t}`; the *outer
frontier* is the set of vertices above `t` with a neighbour at or below it,
the *inner frontier* the vertices at or below `t` with a neighbour above.
Lemma 4.1: `pw ≤ max_t |outer frontier|` and `pw ≤ max_t |inner frontier|` —
as layouts, the inner bound is the vertex separation of the label order and
the outer bound that of its reverse. The probability that one vertex lies on
a frontier is bounded by comparison with an *ideal star* (the regular simplex
minimises Gaussian orthant probabilities; Section 6), which gives the plain
sweep `F₃ n + o(n) ≈ 0.1402 n` at degree 3. The last `3.4 × 10⁻⁴` comes from
the **median switch** (Lemma 8.4): inner frontiers while `t < 0`, outer
frontiers while `t > 0`, and at `t = 0` a *connector* — the bags
`C₋₁ = U ∪ (D ∩ W)`, `C_j = D ∪ {items not yet covered} ∪ {q₁..q_j}`, with
`U`, `W` the two frontiers at zero, `D` the degree-3 vertices all of whose
neighbours lie across zero, and `q₁..q_k` an order of `W ∖ D` from a purely
combinatorial lemma (Lemma 8.3: `j − c(j) ≤ max(0, k − |P|) + 1`). The width
at zero is `max(L₀, L₀') + 1` with `L₀ = |U ∖ D| + |D|`, `L₀' = |W ∖ D| + |D|`,
and the switch lemma (Lemma 8.9) shows it adds nothing at leading order.
`c₃ = κ(r*)` is *exactly* what this layout gives on cubic graphs of large
girth (Section 15), so any improvement must change the rule at threshold
zero; Conjecture 15.1 proposes `(c₃ − 3 p_ch) n ≈ 0.13225 n` for cubic graphs,
`p_ch = 0.00252477819777…` the probability on the ideal wave that two children
of the root both have the root as their only neighbour above zero (the
"isolated helper" event of Lichev & Mitsche, whose printed `0.002818666` the
authors have confirmed was inaccurate).

### 1.2 Algorithmic, with what running time

The proof of Theorem 8.1 is **existential** (Section 8.5): for every `ε` it
picks a radius `R` with `κ(r_R) ≤ c₃ + ε/3`, a grid of `4K₀ + 1` thresholds on
`[−2, 2]`, bounds the mean of `8K₀ + 4` counts, and applies Chebyshev and a
union bound — the condition `(8K₀ + 4) · 9^{R+1} < 2√n` — to find one
realisation in which every count is within `n^{3/4}` of its mean. Section 10
(Theorem 10.1) makes it an algorithm: the Gaussians are replaced by a finite
rational distribution coupled to the normal law, and the method of
conditional expectations fixes the variables one at a time against finitely
many local counts; a Las Vegas algorithm in expected `n^{1+o(1)}` bit
operations and a deterministic one in `n^{2+o(1)}`, with the radius growing
like `(1/8) log₂ log₂ n`. The simplest form, Section 3's cut sweep, is a
randomised polynomial-time algorithm as stated: sample, sort, check the
cutwidth against the explicit bound, repeat.

What this module implements is the **random labelling and the deterministic
layout rules, with random restarts in place of the concentration step** —
the object the proof reasons about, run as a Las Vegas heuristic. It is the
"closest faithful heuristic": the derandomisation of Section 10 would output
one layout whose width is within the *proved* bound, which at these sizes is
vacuous (next subsection), so sampling many labellings and keeping the best
is strictly more useful here. The reductions of Lemma 4.5 (degree ≤ 2) are
not needed, the cages being cubic.

### 1.3 The `o(n)` at `n = 90–126`: the bound says nothing

The paper's remainder for Theorem 8.1 is a function `ρ(n) = max over graphs
of max(0, pw − c₃ n)`, defined to be `o(n)` by the uniform statement "for
every `ε` there is `N(ε)`"; it is **not explicit**. Its proof's own
parameters are explicit, and they are hopeless at any practical `n`: the
union-bound condition `(8K₀ + 4) 9^{R+1} < 2√n` with the smallest admissible
`R = 2`, `K₀ = 1` needs `n > 1.9 × 10⁷`, and at those parameters the width
it certifies is `(κ(r₂) + φ(0)/K₀ + …) n ≈ 0.81 n`; the correlation loss
alone, `κ(r_R)`, is below `1/6` only from `R ≈ 40`, which the condition
admits from `n ≈ 10⁸⁰`. The one **explicit** bound in the paper is the cut
sweep, Theorem 3.1: `pw ≤ cw ≤ c* n + 2.55 n / R + 4 n^{7/8}` with
`c* = (3/(2π)) arcsin(1/3) ≈ 0.16226` and `R = ⌊log₂ n / 4⌋`, valid for
`n ≥ 2⁴⁶`; at `n = 2⁴⁶` it reads `0.468 n`, and it first beats `n/6` at
`n = 2²³¹⁶ ≈ 10⁶⁹⁷`. Theorem 7.1(a) (degree 4) is explicit too, `F₄ n + 179
n / R + 4 n^{7/8}` with `R = ⌊log₃ n / 8⌋ ≥ 2`, i.e. `n ≥ 3¹⁶ = 4.3 × 10⁷`.

At the cages the comparison is sharper than "vacuous": the **certified floors
already exceed `c₃ n` on all five**, so the cages are lower bounds on the
paper's remainder at these sizes,

| graph | `n` | `c₃ n` | `n/6` | certified floor | record | `ρ(n) ≥` floor − `c₃ n` |
|---|---|---|---|---|---|---|
| Foster | 90 | 12.58 | 15.00 | 15 | 20 | 2.42 (7.42 if the record is optimal) |
| Biggs–Smith | 102 | 14.26 | 17.00 | 16 | 19 | 1.74 (4.74) |
| Ljubljana | 112 | 15.66 | 18.67 | 16 | 22 | 0.34 (6.34) |
| Balaban 11-cage | 112 | 15.66 | 18.67 | 17 | 24 | 1.34 (8.34) |
| Tutte 12-cage | 126 | 17.62 | 21.00 | 20 | 26 | 2.38 (8.38) |

Three of the five floors also exceed `n/6`, Fomin & Høie's leading term. So
no theorem in the paper, with or without its remainder, bears on the records;
the experiment below is a heuristic, as the brief anticipated. (The same
table is in `reports/random_graph_classes.md` §1 in a different cut.)

### 1.4 The lower bound, and how it relates to ours

The paper proves **no lower bound**. Its `pw ≥ 0.103295 n − 2` a.a.s. for
random cubic graphs is Lichev & Mitsche's (2023, held) first-moment bound on
the *bisection width* of random 3-regular graphs — a union bound over
bisections in the configuration model, with a structural analysis that
counts graphs rather than bisections (their Sections 4–5) — carried to
pathwidth through `bw ≤ cw ≤ pw + 2` (Díaz, Petit & Serna 2002 Lemma 2.4;
Makedon & Sudborough 1989 Corollary 3.3, cutwidth = search number at maximum
degree 3; Ellis, Sudborough & Turner 1994 Theorem 2.1, search number ≤
vertex separation + 2; Kinnersley 1992). This is exactly the cutwidth route
of `reports/complex_lb_search.md` §4.1, and it settles the "UNVERIFIED
factor-1 transfer" of `reports/random_graph_pathwidth_literature_2.md` §3.2:
the transfer is in print with its chain of citations. Comparison with ours
(`reports/random_graph_classes.md` §1): our empty-pair first moment under the
pairing model gives `β*₃ = 0.070`, Kolesnik & Wormald's vertex-expansion
constant `0.0729`, and the bisection route `0.1033` — the bisection witness
(a balanced cut with few crossing *edges*) is a stronger event than an
empty pair (two vertex sets of size `≈ (n − k)/2` with no edge between), so
its first moment is smaller and the floor higher; the staircase argument of
`reports/dense_staircase.md` is a dense-graph instrument and does not apply
at degree 3. The paper's own remark (Section 15) puts the cubic constant in
`[0.1032, 0.1398]`; the cages sit at `0.19–0.22 n` on the records and
`0.14–0.17 n` on the floors, above every random-cubic number, as §1 of the
random-graph-classes report already said.

## 2. The implementation

`learning/gaspers_sweep.py`:

* `weight_matrix(adj, R, kind)` — the rows `e^{−D(v,w)}` over the ball,
  normalised (padded: arc length `½ ln(p − 1)`, `R̂ = (R/2) ln(p − 1)`; mixed:
  `½ ln(d(tail) − 1)`, `R̂ = R`); labels are one matrix–vector product per
  restart. `label_correlation` lets the tests confirm Lemma 3.4's
  `Corr ≥ (2√2/3)(1 − 1/R)` on every edge of the Petersen graph at `R = 1..4`.
* `plain_sweep` — the label order and its reverse, widths by the fast
  vertex-separation routine; the tests check they equal the maximum inner and
  outer frontier sizes over all thresholds.
* `median_switched_decomposition` — the bags of Lemma 8.5 at a threshold
  (the paper: the median; `switch` as a quantile is ours), with
  `connector_order` built by Lemma 8.3's proof (components of the 2-endpoint
  items, smaller excess first, then complete an item at every step); the
  tests check inequality (8.3) on 40 random instances and that the bags are
  a path decomposition with width within Lemma 8.4's three conditions.
  `decomposition_to_layout` orders by first bag, which never widens
  (`vertex separation ≤ width`: every prefix vertex with a later neighbour
  lies in the first bag of the next vertex).
* `vertex_separation` — the textbook count from scratch, shared with nothing;
  every reported width is this number on the layout, and the tests also
  compare it with `pathwidth_solver/bench/graph_split.py::vertex_separation`.
* `sweep(adj, restarts, …)` — restarts over radii and switch quantiles; the
  best layout is rechecked before it is returned.
* `run_c` — hands a layout to `pathwidth_solver/cli/pathwidth -u` as a
  closing order (the layout reversed: the C program's `-u` file is "the
  vertex closed first first", and a closing order's prefix boundary is the
  layout's count at the mirrored position).

**A convention finding.** The dataset's `layout` field is a *closing order*,
not a textbook layout: on all 16 records read here (the five cages, seven
certified small cubic graphs, four named graphs) the stored sequence has
vertex separation above the recorded width and its *reverse* has exactly the
recorded width (Foster 21 / 20, Balaban 11-cage 31 / 24, OddGraph_5 81 / 41).
It is the C program's `-u` convention, so it can be passed to `-u` as is; a
reader computing the textbook vertex separation of the field must reverse it.

**Tests** (`tests/test_gaspers_sweep.py`, 65): the constants; the fast and
slow vertex separations against each other and against `graph_split` on
random layouts; unit variance and the edge-correlation bound; the sampled
covariance against the formula; frontier definitions; the plain-sweep widths;
Lemma 8.3 on random instances and on a path where a bad order breaks it; the
decomposition's validity; first-bag order never widening; `C₁₂` and `K₄`;
and, on Petersen (5), Heawood (6), Pappus (7), McGee (8) and Tutte–Coxeter
(9), that no width the sweep reports — best or any — is below the certified
pathwidth, with the best layout rechecked three ways. At 300 restarts the
sweep *reaches* the exact value on Petersen, Heawood, Pappus, McGee and
Coxeter, and is one above on Tutte–Coxeter (10 vs 9) and three above on the
Balaban 10-cage (18 vs 15): the sweep's typical layout is about `0.25 n` on
these graphs against the optimum's `0.21 n`.

## 3. The runs

### 3.1 Batch 1: radii 1–6, switch quantiles 0.3–0.7, 20,000 restarts per cage

`python3 -m learning.gaspers_sweep --ids <id> --restarts 20000 --seed 11 --radii 1 2 3 4 5 6 --switches 0.3 0.4 0.5 0.6 0.7`
(`reports/scratch/gaspers_cages/sweep20k/`). Minimum / mean width per rule,
over the restarts in which the rule ran (each restart draws one radius):

| graph | record | plain inner | plain outer | switch 0.3 | 0.4 | 0.5 (the paper) | 0.6 | 0.7 | best (rule, R, restart) | time |
|---|---|---|---|---|---|---|---|---|---|---|
| Foster | 20 | 21 / 28.3 | 21 / 28.3 | **20** / 25.0 | 21 / 25.3 | 21 / 26.8 | 21 / 27.9 | 21 / 28.3 | 20 (0.3, 5, #5728) | 260 s |
| Biggs–Smith | 19 | 22 / 30.6 | 22 / 30.6 | **21** / 26.7 | 21 / 27.2 | 21 / 28.9 | 21 / 30.1 | 21 / 30.5 | 21 (0.3, 4, #207) | 1,022 s |
| Ljubljana | 22 | 24 / 34.6 | 25 / 34.6 | **23** / 30.1 | 23 / 30.6 | 24 / 32.7 | 24 / 34.1 | 24 / 34.6 | 23 (0.3, 6, #10499) | 1,065 s |
| Balaban 11 | 24 | 27 / 35.1 | 26 / 35.1 | **25** / 30.7 | 26 / 31.2 | 26 / 33.3 | 26 / 34.7 | 27 / 35.1 | 25 (0.3, 6, #2231) | 1,063 s |
| Tutte 12 | 26 | 30 / 39.4 | 30 / 39.4 | **29** / 34.3 | 29 / 35.0 | 29 / 37.3 | 29 / 39.0 | 30 / 39.4 | 29 (0.3, 6, #29) | 1,182 s |

The two plain sweeps are indistinguishable (sign symmetry, as the paper
says). The median switch gains 4–5 in the mean over them and 1–2 in the
minimum. The quantile matters monotonically: 0.3 < 0.4 < 0.5 < 0.6 < 0.7 in
the mean on every graph. The best widths all come from radii 4–6 (the ball
of radius 4 has 46 vertices on a cubic graph of girth ≥ 10, radius 5 has 94:
at these radii the labels are a global component plus a local one).

### 3.2 Batch 2: radii 4–8, switch quantiles 0.15–0.35, on the three worst

`--seed 23 --radii 4 5 6 7 8 --switches 0.15 0.2 0.25 0.3 0.35`
(`reports/scratch/gaspers_cages/sweep20k_low/`):

| graph | record | plain | switch 0.15 | 0.2 | 0.25 | 0.3 | 0.35 | best | time |
|---|---|---|---|---|---|---|---|---|---|
| Biggs–Smith | 19 | 22 / 26.9 | **20** / 24.35 | 20 / 24.35 | 20 / 24.35 | 20 / 24.38 | 20 / 24.48 | 20 (0.15, R 6, #772) | 284 s |
| Balaban 11 | 24 | 26 / 32.5 | **25** / 29.21 | 25 / 29.22 | 25 / 29.24 | 25 / 29.26 | 25 / 29.30 | 25 (0.15, R 6, #1432) | 328 s |
| Tutte 12 | 26 | 30 / 36.5 | **28** / 32.82 | 28 / 32.82 | 28 / 32.83 | 28 / 32.83 | 28 / 32.85 | 28 (0.15, R 8, #18959) | 391 s |

Larger radii lower every rule's mean by 2–3 (plain 39.4 → 36.5 on the
12-cage), and below quantile 0.3 the curve is flat: the gain from moving the
switch down saturates. The sweep's best is `record + 1` on Biggs–Smith and
Balaban, `record + 2` on the 12-cage, `record` on Foster.

### 3.3 The C program from the best sweep layouts

`pathwidth -u <closing order> -t 600 -l -v` (`reports/scratch/gaspers_cages/c600/`,
`c_from_sweep.py`; the seed is the batch-1 layout reversed; five runs in
parallel at nice 19):

| graph | seed width | result | status | nodes | engine calls | own lower | rechecked |
|---|---|---|---|---|---|---|---|
| Foster | 20 | 20 | upper | 8.40 × 10⁸ | 25 | 15 | 20 |
| Biggs–Smith | 21 | 19 | upper | 7.49 × 10⁸ | 19 | 16 | 19 |
| Ljubljana | 23 | 22 | upper | 7.52 × 10⁸ | 29 | 16 | 22 |
| Balaban 11 | 25 | 24 | upper | 7.77 × 10⁸ | 12 | 13 | 24 |
| Tutte 12 | 29 | 26 | upper | 7.79 × 10⁸ | 14 | 13 | 26 |

Every run reaches the recorded width and stops there with `upper`: the
descent's satisfiable calls are cheap and the refutation of `record − 1`
does not return in 600 s, which is what the records' own runs found
(`named.csv`, 120 s, 2.2 × 10⁸ nodes; the 12-cage's 26 from a 2,400 s run).
The printed layouts were rechecked by `vertex_separation` (textbook order;
the C program checks them twice itself before printing).

### 3.4 What would be different

Nothing in the construction is specific to the cages, and the records are at
`0.19–0.22 n` against a construction whose *asymptotic* target is `0.14 n`:
the sweep's finite-size overhead on these graphs is about `0.06–0.08 n`
(the Balaban 10-cage, certified 15, gives 18 at 300 restarts; the 12-cage
gives 28 at 40,000). If anything is to move a cage record, it is a lower
one-off layout found by the complete search, not a labelling; the
derandomised Section 10 algorithm would return one layout within a bound
that is above `n/6` here, so it was not built. The one lead the data leaves
is the switch quantile: the paper's rule is symmetric by design, and a
finite-graph rule that chooses the switch where `max(L₀, L₀')` is smallest
would be a legitimate small improvement to the heuristic, not to the theorem.
