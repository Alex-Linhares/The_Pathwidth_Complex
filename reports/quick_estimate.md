# The quick estimate: pathwidth from an instance's parameters, in milliseconds, with no search

*2026-11-12, one agent session. The question (§0), the recipe as it was fixed before the
measurement (§1), the record it was tested on (§2), the results by size band and by
generator (§3), the kill criterion (§4), the bracket on random graphs (§5), the designed
sets and the graph collections, where the signed error measures distance from random
(§6), timing (§7), regenerate commands (§8), the paragraph proposed for paper 1 (§9).
Code `learning/quick_estimate.py` (18 tests in `tests/test_quick_estimate.py`); figures
`paper1/latex/figures/quick_estimate_{truth,error,bracket,designed}.py` writing
`paper1/figures/quick_estimate_*.pdf` (the LaTeX path) and `reports/figures/*.png`; the
data behind each figure `paper1/latex/data/quick_estimate_*.csv` (committed); the
per-instance table `reports/scratch/quick_estimate/estimates.csv` (22 MB, git-ignored,
sha256 committed beside it). **Nothing was solved**: every truth is a certified optimum or a
proved pathwidth already on record; `solution`-provenance records are kept, flagged, and
excluded from every accuracy figure. About 1.2 core-hours in all.*

## 0. Summary

**The question.** Given `n`, `m`, the density and the degree sequence of an instance and
nothing else, how well do the random-graph results of Appendix E estimate its pathwidth
(the MOSP optimum minus one)? Four numbers per instance — a first-moment **floor**, a
random-ordering / independence **ceiling**, min-fill treewidth as the **point estimate**,
and in the dense regime the **corner-block threshold** — then one estimate, fixed before
measuring; and a kill criterion, also fixed before measuring: if the recipe does not beat
min-fill treewidth alone on MAE *and* exact rate by size band, the answer is "use
treewidth".

**The answer: use treewidth. The kill criterion is met in every size band.** On the 57,673
certified instances from random-model generators (Chu & Stuckey, Faggioli–Bentivoglio,
Harvey, Simonis, the 44,551 generated ensembles, the 6,862 `G(n, p)` graphs), min-fill
treewidth alone has MAE 0.31 and is exact on 75.3%; the recipe has MAE 0.93 and is exact
on 50.0%. By band (recipe / treewidth): `n ≤ 20` MAE 0.35 / 0.08, exact 70% / 93%;
`21–40` 0.96 / 0.27, 43% / 75%; `41–60` 1.78 / 0.78, 29% / 43%; `61–100` 3.04 / 1.40,
15% / 26%; `101–125` 2.30 / 1.75, 30% / 30% (80 instances). Two things are responsible,
and both are measured, not guessed:

- **The bracket never binds on random-model instances.** The floor at level 0.05 is
  tight on 0.9% of them and within one of the truth on 20%; the ceiling exceeds the
  truth by 2.6 stacks on the corpus and 9.1 on `G(n, p)`. The truth lies inside
  `[floor, ceiling]` on 99.6%, so the bracket is *right*, but clipping treewidth into it
  changes the estimate on 196 of 20,077 sparse instances — all at `n ≤ 20`, all where
  the ceiling, an expectation rather than a bound, fell below a correct treewidth. The
  bracket is a statement about what the theorems bracket, not an estimator.
- **The dense rule is calibrated on `G(n, p)` at `p = ½` and fails on clique covers.**
  On the 80 dense `G(n, p)` graphs of `reports/dense_staircase.md` the block value
  `n − s_block + 1` *is* better than treewidth (MAE 0.40 against 0.93, exact 62% against
  36%), as that report found. But 65% of the random-model instances have realised density
  `p ≥ 0.3` — Harvey, Simonis and the fixed-size ensembles at `n ≤ 40` are dense clique
  covers — and there the block value overshoots by +2.1 to +2.3 at `p = 0.3–0.6` and by
  +0.8 at `p ≥ 0.6` (treewidth: +0.4 and +0.06). The block count is a statement about the
  edge-independent model; a clique cover of the same density has fewer, larger empty
  corners and a smaller pathwidth than the count predicts.

**What the recipe is good for is the other half of the question.** The floor and ceiling
are read from the parameters only, so where an instance sits far outside its bracket it
is far from random, and the sign says in which direction (§6). The designed MOSP sets and
the graph collections give exactly that: the Harwell–Boeing meshes, the PACE and
TreewidthLIB graphs and the VSPLIB grids sit **40–70 stacks below** the random
prediction (small separators the random model cannot see; Wilson's GP instances 7.7 below,
the VLSI circuits 5.9 below), the **cages sit above it** (four of the five open cubic
cages have a record width 4 above min-fill treewidth and 17–24 above the first-moment
floor: more pathwidth than a random cubic graph, as `reports/random_graph_classes.md`
said), and the Rome graphs, the control-flow graphs and the SCOOP covers sit within one
stack of it with the floor well below (the SCOOP instance `B_REVAL_145` is two stacks
below its floor, as `reports/excess_phase_diagram.md` §4 found). The sign is **proved
pathwidth minus estimate**: positive is expansion beyond random, negative is structure
random graphs lack.

**How the error grows with `n`.** Treewidth's bias is zero to `n = 30` and then grows:
+0.10 at 31–40, +0.6 at 51–60, +1.2 at 61–75, +1.0 at 101–125 on the pooled random
instances, and on the Chu & Stuckey classes alone −0.1 at 30, +0.5 at 50, +1.3 at 75,
+2.9 at 100 and **+4.3 at 125** (the +4.2 of `reports/ml_nature.md` §14). The recipe's
bias is larger at every size. On the same classes the solver's own `_lower_bound`
(trivial, clique, contraction degeneracy; `lb_best` of the record) is 0.6 below the
optimum at 30 and 14.0 below at 125, the parameter-only floor 2.8 and 7.5: **above 100
customers the first-moment floor, which never reads the graph, is closer to the truth
than the solver's graph-reading bound**, by 2.0 at 100 and 6.5 at 125 — because the
degree-based bounds saturate at the average degree (`CLAUDE.md`, the bounds section) and
the first moment does not. It is not a bound off the random model, so it cannot start a
descent; it says where the descent will end.

**Timing.** All four numbers together take 1 ms at the median over the whole record and
25–49 ms at 100–125 customers (min-fill treewidth is 80% of it); the solver's
`_lower_bound` takes 1.3–4.1 s on the same instances (§7). Measured under a load of 50 on
32 cores, so these are upper bounds.

## 1. The recipe, as fixed before the measurement

All quantities in **pathwidth units**; on a MOSP instance the optimum is the pathwidth
plus one (`lean/MOSPFormalization/MOSPGraph.lean`) and the MOSP graph has a clique per
pattern.

1. **Floor** — the first-moment floor at level 0.05, the largest `k` with
   `P(pw ≤ k) ≤ 0.05` plus one. For a MOSP instance the clique-cover inequality of
   `CliqueCoverMoment.lean` at the realised pattern sizes (`learning.first_moment.log_bound`;
   the "measured form" of `reports/random_graph_classes.md` §4, a theorem only for the
   uniform model); for a plain graph the empty-pair inequality of Theorem A at the
   realised edge density (`FirstMoment.lean`; `reports/random_graph_middle.md` §4
   evaluated it on 320 graphs). Both read `n` and the size histogram, or `n` and `p`,
   and never the graph. Recorded beside it: the solver's `_lower_bound` (`lb_best` of
   `learning/data/instances.csv` and the ensemble results; computed for the graph
   collections with a 0.2 s clique and expansion budget, no spectral term), which reads
   the graph and is a theorem.
2. **Ceiling** — the smaller of the random-ordering width
   `max_t (n − t)(1 − (1 − p)^t)` (`RandomOrdering.lean`; `reports/random_ordering_bound.md`,
   the expected open count of the identity ordering of `G(n, p)`, exact at finite `n`)
   and `n − α_greedy` (a minimum-degree greedy independent set; `pw ≤ n − α ≤ n − α_greedy`,
   `IndependenceBound.lean`, the one ceiling that is a bound). The Edwards–McDermid
   degree-histogram term `Σ_v g(d(v))` (`learning.edwards_mcdermid`) is recorded as
   `ceil_em` and the variant that includes it as `recipe_em`; it omits the corollary's
   `τ(n) + O(log n)`, the record measured it below the pathwidth on 28% of proved graphs
   (`reports/edwards_mcdermid.md`; 44% of the certified instances here), and the smoke
   test of 24 ensemble instances showed it at once (1.1 against a pathwidth of 3 at
   `n = 10`), so it was kept out of the bracket *before* the measurement.
3. **Point estimate** — min-fill treewidth (`networkx`'s `treewidth_min_fill_in`, the
   `tw_min_fill` of the record; agrees with the record's value on 99.3% of instances,
   the rest tie-breaks, same MAE to three digits).
4. **Dense regime**, `p ≥ 0.3` — the corner-block finite threshold of
   `reports/dense_staircase.md` §4: `n − s_block + 1`, `s_block` the largest `s` whose
   symmetric block count is at least one (`learning.staircase_moment.block_threshold` at
   level 1), which was the measured median `n − pw` plus one at `n = 30–60`, `p = ½`
   (`tests/test_quick_estimate.py` pins 19, 28, 37, 46).

**The estimate** (`RECIPE`): in the dense regime the block value, otherwise min-fill
treewidth, clipped into `[floor, ceiling]`; where the bracket is inverted
(`floor > ceiling`, which happens only off the random model) the rounded midpoint.

**Alternatives, all recorded**: `tw` alone (the baseline); `clip_tw` (treewidth clipped,
the recipe without the dense rule); `tw_floor = max(tw, floor)`; `midpoint`; `block`
(the dense rule wherever it applies); `recipe_em` (the recipe with the Edwards–McDermid
term in the ceiling).

**Kill criterion**: the recipe must beat `tw` alone on MAE *and* exact rate in each size
band (`≤ 20`, `21–40`, `41–60`, `61–100`, `101–125`, `> 125`) on the certified
random-model instances; otherwise "use treewidth".

## 2. The record

| source | instances | certified | truth | how the instance is rebuilt |
|---|---|---|---|---|
| MOSP corpus (`solutions/`, `learning/data/instances.csv`) | 6,376 | 6,376 | optimum − 1 | the benchmark files; provenance read from the solution file (the CSV's is stale on four 125×125 instances closed in October, `CLAUDE.md` "Stale") |
| generated ensembles `n ≤ 40` (`learning/data/ensemble/results.csv`) | 37,800 | 37,800 | optimum − 1 | regenerated from the cell seed, digest checked against the manifest |
| the 50–100 campaign (`results_upward.csv`, §16 of `ml_nature.md`) | 6,751 | 6,751 | optimum − 1 | same; the 35 uncertified rows at 100 dropped |
| `G(n, c/n)` pilot (`reports/scratch/gnp_pilot/results.csv`) | 6,542 | 6,542 | proved width | `nx.gnp_random_graph(n, c/n, seed)`, edge count checked |
| middle regime and `p = ½` (`reports/scratch/random_graph_middle/results.csv`) | 320 | 320 | proved width | graph6 stored |
| the paper's dataset, graph collections, `n ≤ 1,024` (`paper1/data/dataset/pathwidth_dataset.jsonl.gz`) | 13,131 | 12,919 | proved width | edges stored; 212 `solution` records kept as upper bounds |

70,920 instances; 70,708 with a certified truth (`certified:refutation`, `:bound`,
`:minor`, `:theorem`). The 22 graphs above 1,024 vertices are not read. Generators of
the corpus are read from the source path (`Chu_Stuckey`, `Faggioli_Bentivoglio`,
`Harvey`, `Simonis`, `Shaw`, `Wilson`, `Miller`, `SCOOP`; the 46 `Challenge` files are
the Miller–Shaw–Wilson copies and are reported as such).

## 3. Results

### 3.1 By size band, certified random-model instances (57,673)

| band | count | in bracket | floor tight | recipe MAE | recipe exact | recipe bias | tw MAE | tw exact | tw bias | `lb_best` MAE | `lb_best` exact | midpoint MAE |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| ≤ 20 | 21,483 | 0.990 | 0.014 | 0.348 | 0.703 | +0.25 | 0.075 | 0.925 | −0.05 | 0.119 | 0.883 | 0.81 |
| 21–40 | 26,226 | 1.000 | 0.007 | 0.957 | 0.427 | +0.78 | 0.267 | 0.750 | +0.04 | 0.493 | 0.616 | 1.44 |
| 41–60 | 7,215 | 1.000 | 0.001 | 1.780 | 0.289 | +1.46 | 0.779 | 0.433 | +0.45 | 2.337 | 0.315 | 3.87 |
| 61–100 | 2,669 | 1.000 | 0.002 | 3.038 | 0.154 | +2.76 | 1.401 | 0.263 | +1.11 | 4.089 | 0.263 | 5.99 |
| 101–125 | 80 | 1.000 | 0.000 | 2.300 | 0.300 | +1.50 | 1.750 | 0.300 | +1.00 | 4.550 | 0.275 | 10.3 |
| all | 57,673 | 0.996 | 0.009 | 0.931 | 0.500 | +0.76 | 0.314 | 0.753 | +0.11 | 0.757 | 0.661 | 1.73 |

`clip_tw` (treewidth clipped into the bracket, no dense rule): MAE 0.318, exact 0.749,
bias +0.105 — indistinguishable from `tw`. `tw_floor`: identical to `tw` to three digits
(the floor is never above a correct treewidth on these instances). `recipe_em`: MAE 1.55,
exact 0.188. The full table with every estimator by band, generator and
generator × band is `reports/scratch/quick_estimate/summary.md`.

### 3.2 By generator (certified)

| generator / collection | count | median `n` | recipe MAE | recipe exact | recipe bias | tw MAE | tw exact | tw bias | `lb_best` MAE | floor − truth |
|---|---|---|---|---|---|---|---|---|---|---|
| Chu & Stuckey | 200 | 50 | 3.80 | 0.055 | +3.67 | 1.75 | 0.330 | +1.59 | 5.34 | −5.6 |
| Faggioli–Bentivoglio | 300 | 30 | 0.72 | 0.397 | −0.13 | 0.54 | 0.547 | −0.35 | 1.02 | −4.2 |
| Harvey | 2,130 | 20 | 0.71 | 0.571 | +0.65 | 0.16 | 0.856 | +0.05 | 0.28 | −2.7 |
| Simonis | 3,630 | 15 | 0.81 | 0.569 | +0.80 | 0.09 | 0.917 | −0.04 | 0.18 | −2.2 |
| ensembles `n ≤ 40` | 37,800 | 25 | 0.70 | 0.538 | +0.57 | 0.18 | 0.833 | 0.00 | 0.31 | −2.6 |
| ensembles 50–100 | 6,751 | 60 | 2.71 | 0.160 | +2.46 | 1.03 | 0.354 | +0.76 | 2.66 | −5.0 |
| `G(n, c/n)` pilot | 6,542 | 40 | 0.50 | 0.593 | +0.05 | 0.47 | 0.615 | +0.10 | 1.61 | −4.5 |
| `G(n, c/n)` middle | 240 | 45 | 0.97 | 0.300 | +0.44 | 0.99 | 0.321 | +0.89 | 3.18 | −6.6 |
| `G(n, p)`, `p = ½` | 80 | 45 | **0.40** | **0.625** | −0.10 | 0.93 | 0.362 | +0.90 | 0.29 | −2.5 |
| Rome graphs | 11,199 | 47 | 0.46 | 0.549 | −0.41 | 0.46 | 0.550 | −0.41 | 1.30 | −5.3 |
| freetdi control-flow | 1,060 | 37 | 0.40 | 0.634 | −0.39 | 0.40 | 0.635 | −0.40 | 0.42 | −2.7 |
| Small (Martí et al.) | 84 | 20 | 0.33 | 0.667 | −0.33 | 0.33 | 0.667 | −0.33 | 0.36 | −2.9 |
| VSPLIB trees | 28 | 202 | 3.43 | 0.000 | −3.43 | 3.43 | 0.000 | −3.43 | 2.43 | −4.4 |

The one row where the recipe wins is the one it was calibrated on. On every sparse
collection (Rome, control-flow, Small, trees, the `G(n, c/n)` pilot) the recipe *is*
treewidth, since the bracket does not bind.

### 3.3 The dense rule, by realised density (certified random-model, `p ≥ 0.3`)

| `p` | count | block MAE | block bias | tw MAE | tw bias |
|---|---|---|---|---|---|
| 0.3–0.4 | 3,258 | 2.33 | +2.08 | 0.65 | +0.43 |
| 0.4–0.5 | 2,997 | 2.20 | +2.13 | 0.59 | +0.39 |
| 0.5–0.6 | 3,005 | 2.31 | +2.28 | 0.56 | +0.39 |
| ≥ 0.6 | 28,336 | 0.82 | +0.82 | 0.12 | +0.06 |
| `G(n, p)` only, `p ≥ 0.3` | 623 | 0.64 | — | 0.45 | — |
| `G(n, p)`, `p = ½` (the calibration cells) | 80 | 0.40 | −0.10 | 0.93 | +0.90 |

The block count is a statement about `G(n, p)`; it beats treewidth there (MAE 0.64
against 0.45 over all dense `G(n, p)`, 0.40 against 0.93 at `p = ½`) and overshoots on
clique covers of the same density by two stacks. The dense half of the random-model
record is clique covers, so the rule costs more than it buys. *Post hoc, not a new
estimator*: the rule's domain is the edge-independent model at `p ≈ ½`; nothing in this
session calibrated a block count for clique covers, and nothing is claimed for one.

## 4. The kill criterion

Met in every band (§3.1): the recipe's MAE is above treewidth's and its exact rate below
or equal in all five. The answer is **use min-fill treewidth** (plus one for the MOSP
optimum). What the measurement adds to §4 and §14 of `reports/ml_nature.md`, which
already said treewidth is the best point estimate at `n ≤ 30` and drifts to +4.2 at 125:
the random-graph floor and ceiling do not correct the drift, because the floor is 7.5
below the truth at 125 and the ceiling 30 above, and the midpoint is worse than either
end's distance. No alternative on the list (§1) beats `tw`; `clip_tw` and `tw_floor` tie
it, `midpoint`, `block` and `recipe_em` lose.

## 5. The bracket on random graphs (figure c)

`paper1/latex/data/quick_estimate_bracket.csv`: per `G(n, c/n)` cell the medians of the
floor, the ceiling, the recipe and the proved pathwidth with its min–max. At `c = 3` the
floor is zero (the excess below one, `β*(3) = 0.037`, the finite inequality never below
0.05) and the ceiling, the random-ordering width `0.42 n`, is four times the truth: the
bracket is `[0, 0.42 n]` around a truth of `0.1 n`. At `c = 6` and `c = 10` the floor
climbs to `0.68` and `0.79` of the truth and the ceiling to `2.3×` and `1.6×`; treewidth
sits on the median at every `n` to 80 and one above from 90. At `p = ½` the bracket is
2–4 stacks wide and the block estimate sits on the median at all four sizes (19, 28, 37,
46), which is where `reports/dense_staircase.md` §4 put it. The truth is inside the
bracket on 99.6% of the random-model instances; the 214 exceptions (0.4%) all have the
ceiling below the truth, and the ceiling is an expectation (random ordering) on 84% of
the `G(n, p)` graphs and 51% of the corpus, `n − α_greedy` on the rest.

## 6. Distance from random: the designed sets and the graph collections (figure d)

Signed distance **proved pathwidth − quick estimate** (mean; the table stores the
opposite sign as `recipe_bias`), with the floor's distance beside it:

| collection | count (certified) | median `n` | truth − estimate | truth − floor | floor above truth | reading |
|---|---|---|---|---|---|---|
| VSPLIB trees | 28 | 202 | **+3.4** | +4.4 | 0% | treewidth 1 on every tree; pathwidth up to 5: the one family where the estimate is below by construction |
| Foster cage (record 20, upper bound) | 1 | 90 | +1 | +18 | — | the record sits above treewidth 19 |
| SCOOP | 24 | 28 | +0.5 | +3.3 | 8% (2 of 24) | within a stack of random; `B_REVAL_145` two stacks below its floor, `B_12M18_12` one below |
| Rome, control-flow, Small, Miller | 12,344 | 20–47 | +0.3 to +0.4 | +2.7 to +5.3 | 0% | sparse planar-ish graphs: random at these densities |
| Biggs–Smith cage (19) | 1 | 102 | −1 | +17 | — | |
| Shaw | 25 | 20 | −1.2 | +0.7 | 8% | |
| freetdi named graphs | 127 | 38 | −1.3 | +5.9 | 4% | |
| Ljubljana, Balaban 11-cage, Tutte 12-cage (22, 24, 26) | 3 | 112–126 | **−4** each | +20 to +24 | — | records 4 above treewidth; the first-moment floor is 17–24 below every cage |
| VLSI gate matrix circuits | 10 | 23 | −5.9 | −3.5 | 27% | |
| Wilson (GP, NWRS) | 20 | 50 | **−7.7** | −6.1 | 75% | designed covers: below the random floor on 15 of 20 (`random_graph_classes.md` §4.4: 14 of 20 at 0.01) |
| PACE 2017 bonus | 83 | 199 | −7.3 | −4.2 | 51% | |
| VSPLIB grids | 28 | 343 | −8.9 | −3.7 | 46% | pathwidth = min side; the random model sees only the density |
| PACE 2017 heuristic | 19 | 604 | −36.6 | −35.5 | 68% | |
| PACE 2016 | 69 | 102 | −38.8 | −37.5 | 56% | |
| PACE 2017 exact | 134 | 257 | −43.9 | −43.0 | 74% | |
| VSPLIB Harwell–Boeing | 45 | 283 | −59.7 | −58.8 | 83% | finite-element meshes with `pw ≈ √n` |
| TreewidthLIB colouring | 33 | 190 | **−66.7** | −77.7 | 81% | |

Reading the sign. The floor reads `n` and the density only, so for a graph with `pw` far
below the random floor the graph has small separators that no random graph of its
density has — meshes, grids, planar and near-planar control-flow and PACE graphs, and the
designed MOSP covers of Wilson. The cages are the other direction: cubic, so their
first-moment floor is 2 and their ceiling the random-ordering width, and their record
width sits above the treewidth estimate by 4 on three of the five (above by 1 on Foster,
below by 1 on Biggs–Smith; records are upper bounds, so these distances are at most the
true ones) — expansion beyond what a random cubic graph has, the reading of
`reports/gaspers_cages.md`. The recipe's bias on these collections is the floor's: on the
designed sets the floor is above the truth on 46–83% of the instances and the bracket
inverts, so the estimate is pulled up to the floor or the midpoint (PACE 2017 exact:
treewidth alone is +1.5, the recipe +43.9). **That is the structure detector working as
`random_graph_classes.md` §4.4 described it, and it is why the recipe must not be used as
an estimator off the random model.**

## 7. Timing

`python -m learning.quick_estimate timing` (one process, nice 19, load 50 on 32 cores;
`reports/scratch/quick_estimate/timing.csv`): on the five `Random-100-100-10` and five
`Random-125-125-10` instances the four numbers take **24–28 ms at 100 and 45–49 ms at 125
customers** (floor 4–6 ms, ceiling 0.2–0.5 ms, min-fill treewidth 19–43 ms, block 1–3 ms);
the solver's `_lower_bound` with a 1 s clique budget and no spectral term takes 1.3–1.6 s
at 100 and 2.7–4.1 s at 125 on the same instances. Over the whole record (8 workers,
491 s wall for 70,920 instances, `run.log`): median 0.3 ms at `n ≤ 20`, 1.0 ms at 21–40,
1.7 ms at 41–60, 2.2 ms at 61–100, 3.1 ms at 101–125 and 26 ms above 125 (p90 0.57 s,
maximum 12.4 s on a 1,024-vertex graph, all of it min-fill). The graph-side
`_lower_bound` (clique and expansion budgets 0.2 s) is not in these figures.

## 8. Regenerate

```
nice -n 19 python3 -m learning.quick_estimate run --workers 8     # reports/scratch/quick_estimate/estimates.csv, ~8 min on 8 workers
nice -n 19 python3 -m learning.quick_estimate summarise           # summary.md and paper1/latex/data/quick_estimate_*.csv
nice -n 19 python3 -m learning.quick_estimate timing              # timing.csv
nice -n 19 python3 -m learning.quick_estimate extras              # extras.txt
for f in truth error bracket designed; do python3 paper1/latex/figures/quick_estimate_$f.py; done
python3 -m pytest tests/test_quick_estimate.py -q                 # 18 tests
sha256sum -c reports/scratch/quick_estimate/estimates.sha256
```

Every number in §0 and §3 is in `summary.md` (the band, generator, generator × band,
dense, ceiling-source, designed-set and timing tables) or in `extras.txt`
(`python3 -m learning.quick_estimate extras`: where the bracket binds, §3.3's density
rows, the floor against `lb_best`, the Chu & Stuckey classes by size, the error by
`n`).

## 9. Proposed for paper 1 (not applied), Appendix E, after "A trivial upper bound"

> **A practical recipe, tested.** The floors and ceilings of this appendix read an
> instance's parameters only — `n`, the pattern sizes or the edge density, the degree
> sequence — so they can be evaluated in a millisecond on anything. We asked how well
> they estimate the pathwidth of the 70,708 instances with a certified value on record
> (the corpus, the generated ensembles, 6,862 random graphs and the graph collections of
> Section 4), with the estimate and its kill criterion fixed before measuring: min-fill
> treewidth, clipped into the first-moment floor at level 0.05 and the smaller of the
> random-ordering width and `n − α_greedy`, replaced by the corner-block threshold
> `n − s_block + 1` where the density is at least 0.3; the recipe had to beat min-fill
> treewidth alone on both mean absolute error and exact rate in every size band. It does
> not, in any band: treewidth alone has MAE 0.31 and is exact on 75% of the 57,673
> certified random-model instances, the recipe 0.93 and 50%. The reasons are measured.
> The bracket contains the truth on 99.6% of those instances but binds on 0.3% of them —
> the floor is tight on 0.9% and the ceiling 2.6 to 9 stacks above — and the block
> threshold, which sits on the proved median at `p = ½` on `G(n, p)` (Table E.x), is two
> stacks above the optimum on clique covers of the same density, which are two thirds of
> the record. What the recipe does measure is distance from the random model, with a
> sign: the Harwell–Boeing meshes, the PACE graphs and the VSPLIB grids have pathwidth
> 9–67 below the parameter-only prediction (small separators the model cannot see), the
> SCOOP, Rome and control-flow graphs sit within half a stack of it, and the five open
> cubic cages sit 1–4 above the treewidth estimate and 17–24 above the first-moment
> floor (Figure E.y). Above 100 customers the parameter-only floor is also nearer the
> optimum than the solver's own degree-based lower bound (7.5 against 14.0 below it on
> the 125 × 125 classes), though it is not a bound and cannot start a descent. The four
> numbers cost 25–49 ms at 100–125 customers; the solver's bound costs seconds.
> (`reports/quick_estimate.md`, `learning/quick_estimate.py`.)

With figures (c) as Table/Figure E.x (the bracket on `G(n, c/n)` at `c = 3, 6, 10` and
`p = ½`) and (d) as Figure E.y (distance from random); (a) and (b) belong in the report.
