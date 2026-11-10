# The spectral floor: into the solver, and into the dataset

*One session, 2026-11-10, at the owner's approval of two things:
`reports/spectral_bound.md`'s prefix-separator eigenvalue bound as a
component of the MOSP solver's lower bound, and the nine open dataset
classes where it is the best floor on record
(`reports/layout_lp_literature.md` §8) written into the pathwidth dataset.
Code: `satisfiability/mosp_solver.py` (`_spectral_floor`, `_lower_bound`),
`learning/spectral_bound.py` (`--stage solver`),
`pathwidth_solver/bench/spectral_floor.py`, `paper1/dataset.py`,
`paper1/dataset_check.py`; tests `tests/test_lower_bounds.py` (+4),
`tests/test_spectral_floor_cli.py` (10). Data under
`reports/scratch/spectral_floor/`. Nothing re-solved; `solutions/`
untouched; the only compute is eigenvalues and the dataset rebuild, about
15 core-minutes in all.*

## 0. Summary

**What changed in the solver.** `_lower_bound` now returns
`max(trivial, clique, contraction degeneracy + 1, expansion, spectral + 1)`.
The new component is `_spectral_floor`: the best of the three families of
`learning.spectral_bound.spectral_bounds` (the whole MOSP graph, every
induced subgraph of its degeneracy peeling, every minor of its
contraction-degeneracy sequence) **plus one**, since the spectral bound is
on pathwidth and the optimum is `pathwidth + 1` (`MOSPGraph.lean`); the
unit is pinned by `test_spectral_floor_is_in_optimum_units` (complete
bipartite graphs, where the spectral bound is tight). It runs under a 10 s
budget (what a cut-short sequence saw is still a bound), on graphs to 1,500
vertices, the whole-graph family alone above 400 (the cap the contraction
degeneracy already has). `BOUND_SOURCES` gains `spectral`, and
`_lower_bound(info=...)` now reports which component attains the floor
(`degeneracy`, `expansion`, `spectral`); `solve_mosp_exact` and
`benchmarks.csearch` record it. The dependency is soft (`numpy`, which the
module already used; a failure leaves the other components in place). The
component **rests on the cited theorems and on the corpus validation, not
on Lean**: Theorems 1–3 of `spectral_bound.py` (Mohar & Poljak; Helmberg,
Mohar, Poljak & Rendl 1995 eq. (20)–(21); Gu & Liu 2022) are not
formalised, as the clique bound was not before 2026-09-27; the module
docstring, `BOUND_SOURCES` and `paper1/todo.md` say so.

**Validation** (`python3 -m learning.spectral_bound --stage solver`, every
`solutions/*.json` with a `certified:*` provenance, 8 workers, 98 s;
`reports/scratch/spectral_floor/solver_floor.csv`):

| over 6,376 certified corpus instances | old `_lower_bound` | new |
|---|---:|---:|
| above a certified optimum (**must be 0**) | 0 | **0** |
| tight | 4,909 (76.99%) | 4,909 (76.99%) |
| mean gap | 0.4305 | 0.4291 |
| max gap | 30 | 30 |
| raised above the old floor | — | **9, by one each** |
| of the 338 bound-gap instances (`optimum − lb_old ≥ 2`) | — | 9 raised, 0 closed |
| `source = spectral` | — | 9 |

The nine are exactly the nine of `reports/spectral_bound.md` §0 (`Random-100-50-2-3_0`
10 → 11, `Random-100-50-6-2_0` 24 → 25, `Random-125-125-2-3_0` 12 → 13,
`Random-125-125-4-4_0` 24 → 25, `Random-50-50-2-4_0` 10 → 11,
`Random-75-75-4-5_0` 19 → 20, `p2040n5_0` 6 → 7, `p3040n7_0` 9 → 10,
`p3050n7_0` 8 → 9); none becomes tight. The spectral value alone equals the
old floor on 4,992 instances and is below it on 1,375. **Cost per call**:
the spectral floor is **0.012 s at the median, 0.032 s at p90, 2.15 s at
most** (`Random-125-125-10-4_0`); 0.43 s median at `n ≥ 100`; 2.7 minutes
over the whole corpus. The earlier harness figure of 36 s was measured on a
loaded machine; here the dense 125-customer contraction sequence costs
0.4–2 s, so the minor family is included under the budget rather than
excluded. `_lower_bound` as a whole goes from 3.6 to 6.2 minutes over the
corpus (median 0.002 → 0.014 s; the maximum, 15–25 s, is the 5 s clique
budget plus the contraction degeneracy on dense 125×125 and is unchanged).

**The graph side.** `pathwidth_solver/bench/spectral_floor.py` computes the
floor of a benchmark graph (any format `bench/readers.py` reads, or graph6
on stdin) in pathwidth units and, with `--run`, hands it to the C program
as `-L` on the same graph6 it computed on; documented under `-L` in
`pathwidth_solver/cli/README.md`. No LAPACK in the C.
`tests/test_spectral_floor_cli.py`: the floor never exceeds the exact
pathwidth on named and random small graphs, and the program's answer with
`-L` equals its answer without.

**The nine dataset floors.** The dataset's open-run channel now carries a
`floor`: a `solution` record may hold a certified lower bound below its
width (pathwidth units), with `floor_evidence` and, where the run wrote
one, a `floor_certificate`. `paper1/dataset.py::fold` reads the open-run
files' `lower` column — written by every C run since October and read by
nothing until today, as `reports/obstruction_search.md` §7.4 proposed —
into `floors.csv`, and `write` pairs each with the stored witness. The nine
rows are `reports/scratch/spectral_floor/results_spectral.csv`
(`make_rows.py` regenerates them from the dataset's edge lists), each with
a `spectral-prefix-1` certificate: the theorem, the three inequalities,
`mu2`, `mun`, the prefix size `t` and separator size `c`, the
per-inequality values and the command. **Every value was recomputed from
the record's edge list** (`nine_recompute.json`), and the three closed-form
spectra by hand (§2): Kneser `K(9, 4)` has `μ₂ = 2`, `μₙ = 9`; the star
graph `S₅` has `μ₂ = 1`, `μₙ = 8`; the Tutte 12-cage has `μ₂ = 3 − √6`,
`μₙ = 6`.

| record | graph | n | width (open) | floor before | **spectral floor** | by | μ₂ | μₙ |
|---|---|---:|---:|---:|---:|---|---:|---:|
| pwc-16016 | NStarGraph_5 | 120 | 28 | 23 | **24** | Thm 1 | 1 | 8 |
| pwc-16023 | OddGraph_5 | 126 | 41 | 31 | **36** | Thm 1 | 2 | 9 |
| pwc-16064 | Tutte12Cage | 126 | 26 | 19 | **20** | Thm 1 | 0.5505 | 6 |
| pwc-15943 | CameronGraph | 231 | 161 | 88 | **147** | Thm 2 (eq. 20) | 21 | 33 |
| pwc-15995 | HyperStarGraph_10_5 | 252 | 62 | 18 | **42** | Thm 1 | 1 | 10 |
| pwc-17488 | he048 | 363 | 122 | 34 | **61** | Thm 2 | 4.138 | 24.80 |
| pwc-15892 | le450_5a | 450 | 245 | 63 | **110** | Thm 1 | 10.48 | 45.01 |
| pwc-15893 | le450_5b | 450 | 261 | 63 | **110** | Thm 1 | 10.31 | 44.75 |
| pwc-15944 | Cell120 | 600 | 67 | 17 | **22** | Thm 1 | 0.1459 | 6.854 |

("floor before" is the best floor on record in `layout_lp_literature.md`
§8, which includes loop0013's 600-second minor searches; the dataset itself
had recorded no floor at all.) All nine stay open (`provenance: solution`).
The independent checker replays the prefix arithmetic of each certificate
from its stated eigenvalues and the graph's own degree sequence, in the
standard library, and re-establishes **9 of 9**; it also recomputes `n`,
`m`, the degree extremes and connectedness. What it does not do is
recompute the eigenvalues (no linear algebra in the standard library): the
certificate names the command that does.

**The three closures folded in.** `BalancedTree_3_5` (pwc-15933) is now
`certified:theorem` by the branch lemma: `PROOF_PROV` knows `theorem`, the
row's `minor` column names loop0013's nested `obstruction-branch-1`
certificate (`07_open/tree_certificate.json`), and the checker's item 7
replays it on the graph — at every `branch` node the three parts must be
disjoint, connected, inside the node and off the separator, pairwise linked
through a connected `Q ⊆ S` with an edge into each, and certify `≥ k`
recursively; the root names every vertex and certifies 5 = width (a
tampered part is rejected, tested). `can_292` (pwc-04542) is
`certified:minor` at **22** (the dataset said `solution 23`): the
2026-11-09 certificate (`graph_split/can292/minor.json`, a 146-vertex
least-c minor refuting 21, verified by `obstruction_check.py`) is folded
through `results_can292.csv`, with the C program's printed layout
**reversed** into the dataset's closing-order convention (as printed it has
width 93 under that convention; the fold's width check caught it). `NY_13`
was `certified:minor` already. **Dataset after the rebuild** (`values`,
`write`, `tables`, `dataset_check.py`): 16,972 records as before;
`certified:refutation` 12,631, `certified:theorem` 41 → **42**,
`certified:minor` 439 → **440**, `certified:bound` 3,535, `solution` 326 →
**324**; **318 solution records now carry a floor** (9 with the spectral
certificate; 309 the C program's own floor, 117 of which the checker's own
degeneracy and contraction degeneracy re-establish). The checker's one
failure, `pwc-17202` ("minor certificate leaves 459 vertices, not 194"),
**predates this session** (it is in the committed `check.txt`) and is
untouched. In the paper's `tables/dataset.tex`: VSPLIB Harwell–Boeing on a
minor 5 → 6, upper bound only 28 → 27; freetdi named graphs by theorem 0 →
1, upper bound only 16 → 15; the totals 439 → 440, 41 → 42, 326 → 324.
`tables.md` moved the same six cells. `split.tex` regenerated with only its
timestamp changed and was reverted.

**Left undone.** (i) The paper's prose and Section 5's hand-written graph
table that quote open-class counts (`paper1/todo.md`, already listed).
(ii) loop0013's pass-1 search floors (`13_pass1/pass1.csv`,
`ladder_floor`/`search_floor`, e.g. the Cameron graph's 88) are not folded:
they are not in the run format and their unit convention needs pinning
first, so on the 303 other open classes the dataset's floor is the C
program's own `lower` (e.g. Cameron 43), below the record's. (iii) The
`peel` and `minor` spectral families above 200 vertices on the open
classes (proposed in `layout_lp_literature.md` §8.3; whole graph only
here). (iv) Lean: nothing — the owner's todo item stands. (v) An
observation, not a change: `_lower_bound`'s docstring says the expansion
bound is "off by default", but it is called with `time_budget=None` (no
limit) at `max_t = 8` on every call and attains the floor on 1,329 of the
6,376 corpus instances (`source = expansion`); the 77.0% tightness above is
with it on. Whoever reconciles the docstring and the code should know the
spectral measurement was taken against the code as it runs.

## 1. The solver change, in detail

`_lower_bound(instance, clique_budget=5.0, expansion_t=8, expansion_budget=None,
spectral_budget=SPECTRAL_BUDGET, info=None)`:

1. trivial (largest pattern), clique (5 s of `find_cliques`), contraction
   degeneracy + 1 — unchanged; `info["degeneracy"]`;
2. expansion (`satisfiability.expansion_bound`) — unchanged; `info["expansion"]`;
3. **spectral** — `_spectral_floor(graph, spectral_budget)`; `info["spectral"]`;
   `spectral_budget=None` or `0` disables it (the old floor, used as the
   control in the validation).

`info["source"]` is `degeneracy` unless a later component is the strict
maximum. `_spectral_floor` returns 0 on the empty graph and on graphs above
`SPECTRAL_MAX_NODES = 1500`; above `SPECTRAL_FAMILIES_MAX_NODES = 400`
only the whole-graph family runs. The deadline is passed to
`spectral_bounds`, which marks the result censored and returns what the
sequences saw — each value is a bound in its own right (an induced
subgraph's or a minor's), so censoring loses strength, never soundness.
Rounding: `μ₂` is lowered and `μₙ` raised by `TOL = 1e-7` relative before
use, which weakens every inequality (each right-hand side increases in
`μ₂` and decreases in `μₙ`).

Why `+ 1`: `spectral_bounds(...)["best"]` is `spec(G) ≤ vs(G) = pw(G)`
(Theorem 4 of the module), and `mospValue = pathwidth(mospGraph) + 1`
(`MOSPGraph.lean`). On `K_{p,q}` the spectral bound is tight at `min(p, q)`
(Gima et al. 2025 Remark 3.5), and the instance whose MOSP graph is
`K_{p,q}` (one pattern per edge) has optimum `min(p, q) + 1`; the test
checks all three equalities on `(2,3)`, `(3,4)`, `(3,6)` and the brute-force
optimum where it is affordable.

## 2. The nine, derived

Theorem 1 on a `Δ`-regular graph reads `Δ c ≥ μ₂((a + b) − (a − b)²/n)`
with `a + b = n − c`; at the balanced level it is `c (Δ + μ₂) ≥ μ₂ n`, the
Gima treewidth bound `n μ₂/(Δ + μ₂)`, and the prefix form gives the same
value on all nine (the bound is a treewidth bound in disguise,
`spectral_bound.md` §1(ii)).

- **OddGraph_5 = K(9, 4)**, `n = 126`, 5-regular. Kneser `K(n, k)` has
  adjacency eigenvalues `(−1)^i C(n − k − i, k − i)`, here `5, −4, 3, −2, 1`,
  so the Laplacian has `μ₂ = 5 − 3 = 2`, `μₙ = 5 + 4 = 9` (numerically
  `1.999999999999995`, `9.000000000000004`). `c = 35`: `175 ≥ 2(91 − (a − b)²/126)`
  needs `(a − b)² ≥ 441`, i.e. `|a − b| ≥ 21`; with `a + b = 91` that
  fails for every prefix `a ∈ [36, 55]`, so `c_t ≥ 36` there; `c = 36`:
  `180 ≥ 2(90 − …)` always. **spec = 36** (`t* = 36`). Theorems 2 and 3
  give 28.
- **NStarGraph_5 = S₅**, `n = 120`, 4-regular bipartite; the star graph
  `S_n` has algebraic connectivity 1 (Laplacian `μ₂ = 1`), and bipartite
  `Δ`-regular gives `μₙ = 2Δ = 8`. `c = 23`: `92 ≥ 97 − (a − b)²/120` needs
  `(a − b)² ≥ 600`, `|a − b| ≥ 25`; with `a + b = 97` that fails for
  `a ∈ [37, 60]`; `c = 24`: `96 ≥ 96`. **spec = 24** (`t* = 37`). Theorems 2
  and 3 give 15.
- **Tutte 12-cage**, `n = 126`, 3-regular, adjacency spectrum
  `±3, ±√6, ±√2, 0`, so `μ₂ = 3 − √6 = 0.5505`, `μₙ = 3 + 3 = 6`. Balanced:
  `c ≥ 126 · 0.5505/3.5505 = 19.54`; `c = 19`: `57 ≥ 0.5505(107 − (a − b)²/126)`
  needs `(a − b)² ≥ 436`, `|a − b| ≥ 21`, which fails for `a ∈ [44, 63]`;
  **spec = 20** (`t* = 44`). Theorems 2 and 3 give 12.
- **CameronGraph**, `srg(231, 30, 9, 3)`, `μ₂ = 21`, `μₙ = 33`. Theorem 2:
  `4 μₙ μ₂ /(n (μₙ − μ₂)²) = 2772/33264 = 1/12`, so `c ≥ ab/12`; at the
  balanced level `48 c ≥ (231 − c)²`, true at `c = 147` with equality
  (`7056 = 84²`) and false at 146 (`7008 < 85²`). **spec = 147**; Theorem 1
  gives 96.
- **HyperStarGraph_10_5** (252, 5-regular, `μ₂ = 1`, `μₙ = 10`): balanced
  `6c ≥ 252`, **42**. **Cell120** (600, 4-regular, `μ₂ = 0.1459`,
  `μₙ = 6.854`): `c ≥ 600 · 0.1459/4.1459 = 21.1`, **22**. **he048**
  (363, degrees 14–23, `μ₂ = 4.138`, `μₙ = 24.80`): Theorem 2 gives **61**,
  Theorem 1 with the top-`c` degree sum 58. **le450_5a / le450_5b** (450,
  degrees 13–42 / 12–42, `μ₂ = 10.48 / 10.31`): Theorem 1 gives **110** on
  both, Theorem 2 105 / 104.

Peel and minor families, where run (to 252 vertices), add nothing on any of
the nine: regular graphs lose `μ₂/Δ` under deletion and contraction.

## 3. The dataset mechanism

- `paper1/dataset.py`: `PROOF_PROV["theorem"]`; `BRANCH_THEOREM`;
  `FLOOR_CERTIFICATE_FORMATS`; `OPEN_RUNS` + `results_can292.csv`,
  `results_spectral.csv`; `fold` step 3 collects the best `lower` per
  record id over every open-run row (a certificate-carrying floor wins
  ties), writes `paper1/data/dataset/floors.csv` (cls, id, floor,
  evidence, certificate) for classes no row proves, and refuses a floor
  that meets or exceeds any width the class has on record; theorem rows
  load their nested certificate and check `pathwidth_proved = width`;
  `stage_write` attaches `floor`, `floor_evidence`, `floor_certificate` to
  `solution` records and a `floor` column to `classes.csv.gz`. `values.csv.gz`
  is unchanged in shape.
- `paper1/dataset_check.py`: item 7 extended to `family: branch`
  (`branch_certificate_value`, recursive; `trivial`, `clique`, `branch`
  nodes; `c` and `minor` nodes refused as resting on a search); item 9,
  floors (`spectral_prefix_bound`, the arithmetic of Theorem 4 in the
  standard library, equal to `spectral_graph_bound` on the Petersen graph,
  `K_{3,5}`, `C₉` and a random 4-regular graph; checked before use). Still
  imports nothing from the repository (`test_checker_imports_nothing_from_the_repository`).
- `paper1/dataset.md`: the `theorem` and `floor` rows of the field table.

## 4. Regenerate

```bash
cd ~/dev/MOSP
nice -n 19 python3 -m learning.spectral_bound --stage solver --workers 8      # solver_floor.csv, 98 s on 8 cores
PYTHONPATH=. python3 reports/scratch/spectral_floor/make_rows.py              # results_spectral.csv from the dataset
nice -n 19 python3 -m paper1.dataset values && nice -n 19 python3 -m paper1.dataset write
nice -n 19 python3 -m paper1.dataset tables && python3 paper1/dataset_check.py > paper1/data/dataset/check.txt
python3 -m paper1.latex.make_tables
python3 -m pytest tests/test_lower_bounds.py tests/test_spectral_floor_cli.py tests/test_dataset.py tests/test_dataset_check.py -q
python3 pathwidth_solver/bench/spectral_floor.py pathwidth_solver/bench/instances/named/gr/OddGraph_5.gr   # 36
```
