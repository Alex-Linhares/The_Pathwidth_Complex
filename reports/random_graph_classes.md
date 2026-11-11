# What the random-graph theorems say for well-studied graph classes

*2026-11-11, one session, executing the `paper1/todo.md` item of the same name.
Code `learning/random_graph_classes.py` (tests `tests/test_random_graph_classes.py`,
39, every pair probability against brute force), tables under
`reports/scratch/random_graph_classes/` (`python -m learning.random_graph_classes`,
about three minutes, nothing solved), literature in `literature/MISSING.md` under
"Random graph classes (2026-11-11)". Nothing under `solutions/` or
`paper1/data/dataset/` was touched; no pathwidth run was started; every exact
pathwidth quoted is on the record by member name.*

**The one lemma everything rests on.** `pw(G) ≤ k` forces an *empty pair*: disjoint
`A`, `R` with `|A| = t = ⌈(n − k)/2⌉`, `|R| = t − 1` and no edge between them
(`EmptyPair.lean`, `exists_empty_pair`; more generally, for every `j` a set `A` of size
`j` with `|N[A]| ≤ j + pw`, `exists_closedNbhd_card_le`, which is Harper's bound in
layout form). The union bound over the `C(n, t) C(n − t, t − 1)` pairs turns it into
`P(pw ≤ k) ≤ Σ_pairs P(pair empty)`, and **everything model-specific is the probability
that one fixed pair is empty**: `(1 − p)^{t(t−1)}` on `G(n, p)` (`FirstMoment.lean`),
`∏_j q(s_j)` on random clique covers (`CliqueCoverMoment.lean`). The lemma is
deterministic, so it holds in every model; what each class below changes is (i)
whether that probability is a product, (ii) whether it is the same for every pair, and
(iii) whether a sharper tool than the empty pair is already in print. `β*` always means
the first-moment constant on `lim pw / n` (optimum `= pw + 1` on MOSP graphs); floors
are "largest `k` with the bound below the level, plus one", in pathwidth units unless
the table says optimum units.

## 0. Summary

| # | class | model and parameter | ours (derived) | in print | measured (record) | tight family (Section 5) | verdict |
|---|---|---|---|---|---|---|---|
| 1 | random regular `G_{n,d}` | pairing model, degree `d` | exact pair probability and rate under the pairing model (§1); `β*_d = 0.070, 0.145, 0.211, 0.268, 0.357, 0.424` at `d = 3, 4, 5, 6, 8, 10`, the free split of the pair never better than the balanced one; within `0.002–0.004` of `max_u u·A_d(u)` from Kolesnik & Wormald's Table 1 (`0.0729, 0.149, 0.215, —, —, 0.425`), always a little below (they count the boundary exactly, we count its superset) | cubic: `pw ≥ 0.103295 n − 2` a.a.s. (Lichev & Mitsche 2023 bisection through `bw ≤ cw ≤ pw + 2`, stated by Gaspers, arXiv 2611.05146, 3 Nov 2026), `pw ≤ 0.13982 n + o(n)` for **every** graph of maximum degree 3 (Gaspers Thm 1.1(a), closing Fomin & Høie's `n/6`); `d ≥ 4`: KW's `u`-expansion below, Edwards & McDermid / Gaspers (`0.2458 n` at `d = 4`) above | `random4reg` (48 vertices, `pw = 13 = 0.27 n`; first-moment floor at 0.05: 8); the five open cages at `0.19–0.21 n`, record floors `0.15–0.17 n`: every random-cubic number is below them (pairing floor at 0.05: 6–10; `β*_3 n = 6–9`; `0.1033 n − 2 = 7–11`; Gaspers' asymptotic `c₃ n = 12.6–17.6`) | `random4reg`: refutation (cheap floors 6); cages: open, best floors are searched minors / spectral | **covered** for the class (KW's Corollary 9 read through Harper's layout form; our constant is theirs to `0.004`, and the cutwidth route beats both at `d = 3`); **nothing for the cages**: they sit above every random-cubic constant, including the deterministic asymptotic upper bound |
| 2 | random geometric `G(n, r)` | `n` uniform points in `[0,1]²`, radius `r` | the lemma holds; the pair probability is not a product and depends on the geometry; what survives is Harper's layout form, which *is* the method in print | `vs / (n r) → 1` a.s. for `r → 0`, `n r² / log n → ∞` (Díaz, Penrose, Petit & Serna 2001, Petit's thesis Thm 5.13; lower bound by an isoperimetric inequality on the dissection, upper by the projection layout); `tw, td, pw = Θ(r √n)` supercritical and `Θ(log n / log log n)` subcritical (Mitsche & Perarnau 2012, Thms 2–3 and Remark, held) | none: no geometric graph is on the record | — | **covered, in print**, and the only random model where `vs` has a sharp constant; nothing of ours adds to it |
| 3 | random planar, outerplanar, series-parallel | uniform labelled planar / outerplanar / SP graph on `n` vertices | nothing structural: the lemma gives no constant (the empty pair's probability is not computable in these models) and `TreeBound.lean`, the layer lemma and `ForestCover.lean` give only the deterministic `O(√n)` (planar) and `O(log n)` (treewidth ≤ 2) orders | planar: `tw ≤ 3·diam + 1` (Robertson & Seymour; Eppstein 2000) and `diam = n^{1/4 ± o(1)}` a.a.s. (Chapuy, Fusy, Giménez & Noy 2015), so **`pw ≤ n^{1/4 + o(1)} log n` a.a.s.** — we found no lower bound in print beyond the trivial, and Noy's ICM survey (read) states only the deterministic `O(√n)`; outerplanar / SP: subcritical, diameter `n^{1/2 ± ε}`, `pw = O(log n)` by `tw ≤ 2`, no constant found; random trees: `pw / log₂ n ∈ [1/4, 1/2]` (`reports/random_graph_pathwidth_literature_2.md` §3.5) | `RandomTriangulation_800` (planar, `pw ≤ 40 = 1.41 √n`, open); the 50 VSPLIB grids and `Grid2dGraph_20_40` are the planar graphs with proved widths and are not random | grids: theorem (Ellis & Warren; `Grid.lean`) | **open**: the order of `pw` of a random planar graph is not in print and our theorems say nothing; the diameter route gives `n^{1/4+o(1)}` from above |
| 4a | random bipartite `G(n, n, p)` | mean degree `c = np`, `N = 2n` | the pair probability is `(1−p)^{a₁ r₂ + a₂ r₁}` for a pair split `(a₁, a₂ ; r₁, r₂)` across the sides; the lemma's pair has a split we do not choose, so the bound sums over splits and picks the best shape: `β*_bip(c) = 0, 0.0078, 0.0604, 0.1693, 0.3346` at `c = 2, 3, 4, 6, 10` (of `N`), within `0.003` of `β*(c)` on `G(N, c/N)` (§4.1) | we found no statement on the pathwidth or treewidth of `G(n, n, p)`; the linear-width threshold at `c > 1` of Lee, Lee & Oum (2012) is for `G(n, p)` | `RandomBipartite_25_50_1/3`, `_10_50_3` on the record (`pw = 9, 23, 9`, certified) are single draws | minor (two of three) | **new statement**, small: the bipartite constant equals the Erdős–Rényi one at the same mean degree to `0.003`; nothing in print to compare with |
| 4b | Chu & Stuckey `d`-uniform covers | `m` patterns, each a uniform `d`-set of `n` customers; `d ∈ {2, 4, 6, 8, 10}` | `prob_coversOfMospValueLe_le` (`CliqueCoverMoment.lean`) evaluated at the realised sizes on all 200 instances, **the direct test of our theorem on our data**: 0 of 200 below the 0.01 floor, 0 tight; the floor sits `2.4–12.2` stacks below the optimum per class, the gap growing with `n` at fixed `d` (`4.0 → 9.2` at `d = 2`, `30 → 125`) and largest on the `100 × 50` classes (`11–12`); `opt/n − β*` is `0.08–0.19` at `d = 2`, `0.10–0.20` at `d = 4`, `0.07–0.16` at `d = 6` (§4.2) | the only random-cover statement in print is Gao's linear treewidth for random intersection graphs with `p ≥ 2/m` (held, R1 of `paper2/survey_random_extremal.md`); no constant | the 200 certified optima; `opt / n` from `0.116` (`100 × 50 × 2`) to `0.956` (`50 × 100 × 10`) | searched contraction minors tight on 189 of 200; Harper's ceiling below the optimum on the sparse classes | **covered by our own theorem**, loose by `5–12` stacks where the instances are hard: the slack is the union bound (`reports/excess_phase_diagram.md` §8.5), not the model |
| 4c | Harvey's three generators | `wbo`: patterns of fixed size `d` (the `d`-uniform cover); `wbp`: customers with exactly `r` patterns; `wbop`: both margins constant (regular bipartite incidence) | three exact pair probabilities (§4.3): the uniform cover for `wbo`; for `wbp` a sum over the size of the union of `|A|` random `r`-sets; for `wbop` the bipartite pairing model, `α! ρ! σ!/N! · [x^α y^ρ z^σ]((x+z)^d + (y+z)^d − z^d)^m`. On all 2,130 instances: **0 violations** under the matching model and under the uniform form; the `wbp` model is `1.0–2.2` stacks above the uniform floor (growing with `n`), the `wbop` pairing floor within `±0.3` of it; mean gaps `3.4`, `2.7`, `4.3` (`wbo`, `wbp`, `wbop`), tight on 8 of 2,130 | nothing on these generators in print beyond the Challenge report | the 2,130 certified optima, `opt / n = 0.70, 0.82, 0.76` | `T` (treewidth + 1) tight on 1,972 of 2,130, `D` on 1,605 | **covered** (two of the three generators needed a new pair probability, derived here; the first moment is a bound on each and loose by 3–4 stacks at 10–30 customers) |
| 4d | Faggioli–Bentivoglio, Simonis, Shaw, Wilson, SCOOP | the uniform-size form at realised sizes (`measured`, not a theorem for these generators) | FB: 0 violations on 300, tight 2, gap `4.1` (`0.15 n`); Simonis: 0 violations on 3,630, tight 9, gap `3.2`; **Shaw 2 of 25, Wilson 14 of 20, SCOOP 1 of 24 below the floor** (§4.4): the floor is not a bound off the model, and where it exceeds the optimum it measures the instance's distance from a random cover (GP1–GP8: floor 48 or 98 against optima 30–95; `B_REVAL_145`, as `excess_phase_diagram.md` §4 said) | — | — | `T` tight on 163 / 300 (FB), 3,372 / 3,630 (Simonis), 20 / 25 (Shaw), 16 / 20 (Wilson), 6 / 24 (SCOOP) | **measured**: a bound only on the random generators; a structure detector on the designed ones |
| 5 | preferential attachment, power law | Barabási–Albert `m` edges per new vertex; Holme–Kim; Newman–Watts–Strogatz | the lemma holds; what fails is the product step (`sum_gnpWeight_emptyPairGraphs`) and the symmetry over pairs — the per-pair probability depends on the ages of the vertices and must be bounded as Gao does (§5); no constant of ours | `tw(BA(n, m)) ≥ βn` a.a.s. for `m ≥ 12`, `β` implicit (Gao 2012 Thm 3, held: a first moment over balanced triples with the attachment law); nothing for `m < 12`, nothing for pathwidth, no constant | `BA_100_2`: `pw = 13` (certified by a minor) against a `G(n, p)`-matched 0.05-floor of 6; `BA_100_5`: `pw = 34`, matched floor 34; `HolmeKim_300/700`: widths 27 / 57 open, matched floors 20 / 44; `NWS_100_5_3`: 20 (minor) against 16; **`NWS_250_10_3`: width 91 against a matched "floor" of 110** — the product-law comparison is not a bound and the ring lattice shows it | M (minors) on the two certified ones | **open**: linear treewidth is in print for `m ≥ 12` only; the constant and the pathwidth are not; ours transfers nothing without redoing Gao's per-pair bound |
| 6 | random interval, chordal, split | intervals with uniform endpoints; uniform chordal / random `k`-trees; clique `K` plus independent set | interval: `pw = tw = ω − 1` (own path decomposition; the clique bound `card_le_pathwidth_add_one_of_isClique` is exact); cocomparability: `pw = tw` (Habib & Möhring 1994), so every treewidth floor is a pathwidth floor there; split: `pw ∈ {ω − 1, ω}` (bags `K ∪ {v}`; §6); chordal in general: `pw ≥ tw = ω − 1` and the gap is unbounded (trees) | random interval: `χ = ω = n/2 + o_p(n)` (Scheinerman 1988), so `pw = n/2 + o(n)`; pathwidth NP-complete on chordal graphs (Gustedt 1993); random `k`-trees: height `~ c log n` (Cooper, Frieze & Uehara 2014), nothing on their pathwidth | `RandomBoundedToleranceGraph_60/80` (cocomparability: `pw = 30, 32 = ` contraction degeneracy, `certified:bound`, `ω − 1 = 28, 30`); the 1,669 complete MOSP graphs of the corpus are the degenerate interval case | `D` (contraction degeneracy, a treewidth floor) exact by `pw = tw`; `C` on interval graphs | **covered**: deterministic identities, the random part is the clique number |
| 7 | hypercubes and grids | `Q_d`; `h × w` grid | Harper's bound `max_t (f(t) − t)` computed exactly: `= pw` on `Q_3..Q_6` (`4, 7, 13, 23`; branch and bound to `Q_4`, the simplicial order beyond, Chandran & Kavitha's formula throughout) and on every grid to `6 × 6` (`min(h, w)`, branch and bound complete); the empty pair at the balanced size is the same statement and is exact there too (§7); the `G(n, p)` counting theorem says nothing about a fixed graph | `pw(Q_d) = Σ_{m<d} C(m, ⌊m/2⌋)` (Chandran & Kavitha 2006 Thm 2, from Harper 1966); `pw(grid) = min(h, w)` (Ellis & Warren 2008; `Grid.lean` `pathwidth_grid`) | `CubeGraph_6`: `23`, certified by refutation, cheap floors 11; the 50 VSPLIB grids (`certified:theorem`) and `Grid2dGraph_20_40` (width 20 = the theorem's value, provenance still `solution`: a bookkeeping upgrade is proposed, not applied) | `E` (Harper) exact on both; `G` (theorem) on grids | **covered**: Harper's setting is where family E is exact and the degree family is far off (`Q_6`: 11 against 23) |
| 8 | Chu & Stuckey ridge classes | fixed-size covers at excess `e ≈ 2–2.4`, `m = n`: `d = 3` on the ensembles; the corpus `d = 2` (`e = 1.7–1.8`) and `d = 4` (`e = 3.2–3.4`) classes flank it | at the ridge (`n = 75`, `m = n`, `d = 3`, `e = 2.05`, median `4.6 × 10⁶` nodes): `opt/n = 0.245`, `β* = 0.140`, finite 0.01-floor `0.160 n` — gap `0.105` asymptotic, `0.085` finite; the gap **peaks on the dense shoulder**, not the ridge: `0.123` at `d = 5` (`m = n`), `0.162` at `d = 7` (`m = n/2`), `0.098` at `d = 3` (`m = 2n`) (§8) | — | the corpus `d = 2` classes: `opt/n − β* = 0.08–0.19`, finite gap `4–9` stacks; `d = 4`: `0.10–0.20`, `4–11` stacks | M on 39 / 40 (`d = 2`) and 34 / 40 (`d = 4`) | **covered by the theorem, loose where it matters**: the first moment is a floor at every excess above 1 and never within a stack of a ridge optimum; `excess_phase_diagram.md` §0.4 already said the slack is the union bound |

**Three sentences for the owner.** (i) The one class where the item mattered, the
cubic cages, is one where random-cubic theory is exhausted and irrelevant at once: our
constant reproduces Kolesnik & Wormald to `0.004`, the cutwidth route (now in print,
Gaspers 2026) beats both, and the cages' *proved floors* (`0.15–0.17 n`) already exceed
every a.a.s. constant and even the deterministic asymptotic upper bound `0.1398 n` —
they are extremal, not typical, and a bound for the class cannot reach them. (ii) The
direct test of `CliqueCoverMoment.lean` on its own generator passes on every one of 200 +
2,130 instances (and on 300 + 3,630 under the measured form) with the floor `2–12` stacks
below the optimum; where the floor exceeds an optimum (Wilson 14 / 20, Shaw 2, SCOOP 1)
the instance is not a random cover, which the floor detects. (iii) Two small statements
are ours and not in print: the pathwidth first-moment constant of `G_{n,d}` under the
pairing model (a corollary of KW Corollary 9 that they do not draw), and the bipartite
`G(n, n, p)` constant, equal to the Erdős–Rényi one to `0.003`; two of Harvey's three
generators needed pair probabilities derived here (`wbp`: a union-size sum; `wbop`:
coefficient extraction in the bipartite pairing model).

---

## 1. Random regular graphs `G_{n,d}`, cubic first

**The model.** The pairing (configuration) model: `dn` points in `n` bags of `d`, a
uniform perfect matching; the simple uniform `G_{n,d}` is this model conditioned on
simplicity, an event of probability `→ exp(−(d² − 1)/4)` (Bender & Canfield 1978;
Bollobás 1980), so `P_simple(E) ≤ P_pairing(E) · exp((d² − 1)/4)`: a constant factor that
changes no exponent and moves a finite floor by at most `(d² − 1)/4` nats
(`simple_correction`; it is asymptotic, and the tables say so where it is applied).

**The pair probability, exactly.** For a fixed pair `(A, R)`, `|A| = t`, `|R| = r`,
`S = V ∖ (A ∪ R)`, with `α = dt`, `ρ = dr`, `σ = d(n − t − r)` points, the matchings
with no `A`–`R` pair are counted by the numbers `j` of `A`–`A` and `l` of `R`–`R` pairs
(then `k = α − 2j` `A`–`S` pairs, `q = ρ − 2l` `R`–`S` pairs, `σ − k − q` even):

```
#(j, l) = C(α, 2j)(2j−1)!! · C(σ, k) k! · C(ρ, 2l)(2l−1)!! · C(σ−k, q) q! · (σ−k−q−1)!!,
P(no A–R pair) = Σ_{j,l} #(j, l) / (dn − 1)!!        (gnd_log_empty_pair)
```

checked against the enumeration of every matching on `(n, d) = (5, 2), (6, 2), (4, 3)`
to `10⁻¹⁴`. The law of the pairing model is invariant under vertex relabellings, so every
pair of given sizes has the same probability and the union bound is the pair count times
one probability: `P(pw(G_{n,d}) ≤ k) ≤ C(n, t) C(n − t, t − 1) · P(no A–R pair)`,
`t = ⌈(n − k)/2⌉` (`gnd_log_bound`).

**The exponent.** At `|A| = a n`, `|R| = r n`, `(1/n) log P → ψ_d(a, r)`, the largest
summand's exponent (`gnd_rate`: the summand at `n = 2 × 10⁵`, maximised over `(j, l)` by
grid refinement — a coordinate ascent fails on the `−∞` regions — error `O(log n / n)`;
against the exact sum at `n = 400`–`800` the agreement is `3 × 10⁻⁴`). The pair-count
exponent is `g_d(a, r) = H(a, r, 1 − a − r) + ψ_d(a, r)` and `β*_d = 1 − 2a*` at the
balanced root (`beta_star_gnd`). Harper's layout form gives a pair of sizes
`(j, n − j − pw)` for *every* `j`, so each shape is a valid bound on its own and the
best constant is `sup{β : ∃ a, g_d(a, 1 − β − a) < 0}` (`beta_star_gnd_split`): **the
free split never beats the balanced one**, on the pairing model (`d = 3, 4, 6, 10`:
identical to `10⁻⁴`) as on `G(n, p)` (`c = 4, 6, 10`: identical, the minimiser at
`a / (1 − β) = 0.500`).

| `d` | `β*_d` (pairing, balanced) | KW `A_d(1/2)/2` (`u = 1/2`) | KW `max_u u·A_d(u)` (Table 1) | `β*(c = d)` on `G(n, c/n)` |
|---:|---:|---:|---:|---:|
| 3 | 0.0699 | 0.0721 | 0.0729 (at `u = 0.45`) | 0.0087 |
| 4 | 0.1451 | 0.1448 | 0.1491 (`u = 0.40`) | 0.0613 |
| 5 | 0.2114 | 0.2043 | 0.2149 (`u = 0.40`) | 0.1175 |
| 6 | 0.2678 | 0.2510 | — | 0.1706 |
| 8 | 0.3569 | 0.3159 | — | 0.2634 |
| 10 | 0.4235 | 0.3569 | 0.425 (`u = 0.30`) | 0.3371 |

**Reading.** Kolesnik & Wormald (2014, held) define the `u`-vertex-expansion number
`I_{V,u}(d) = sup{ℓ : min_{|U| = un} |∂_V U| / (un) ≥ ℓ a.a.s.}` and prove
`I_{V,u}(d) ≥ A_d(u)` (Corollary 9) by a first moment on the pairing model that counts
sets with their boundary *exactly*; with Harper's layout form `pw ≥ min_{|U| = j} |∂_V U|`
this is `pw(G_{n,d}) ≥ (u A_d(u) − o(1)) n` a.a.s. for every fixed `u ∈ (0, 1/2]` — a
one-line corollary they do not draw, whose `u = 1/2` reading (`0.0721 n` for cubic) is
R13 of `paper2/survey_random_extremal.md` and whose `u`-optimised reading is `0.0729 n`.
Our empty-pair count is the same event counted more coarsely (the pair `(A, S ⊇ ∂A)`
instead of `(A, ∂A)`), so it must sit at or below theirs, and it does, by `0.002`–`0.004`
at every `d` where their table allows the comparison; at `d ≥ 6` it is above their
`u = 1/2` reading only because its prefix sits at `a* n` (`0.37 n` at `d = 6`), not at
`n/2`. The `G(n, c/n)` column shows why the
model matters: at mean degree 3 the Erdős–Rényi constant is `0.009`, the regular one
`0.070`, because the degree fluctuations of `G(n, p)` are where its narrow layouts live.

**What is in print beyond the first moment.** For cubic graphs the first moment is not
the best floor: Lichev & Mitsche's a.a.s. bisection `bw(G_{n,3}) ≥ 0.103295 n` transfers
with factor one through `bw ≤ cw` (Díaz, Petit & Serna 2002, Lemma 2.4), `cw = es` on
maximum degree 3 (Makedon & Sudborough 1989) and `es ≤ vs + 2` (Ellis, Sudborough &
Turner 1994; `EdgeSearchFull.lean`), which is the cutwidth route of
`reports/complex_lb_search.md` §4.1 and is now stated in print: Gaspers (arXiv
2611.05146, 3 November 2026, read through the arXiv HTML) writes
`pw ≥ 0.103295 n − 2` a.a.s. for random cubic graphs, and proves `pw ≤ c₃ n + o(n)`,
`c₃ = (3/(4π)) arccos(5/6) ≈ 0.13982`, for **every** graph of maximum degree 3
(Theorem 1.1(a)) — the constant Lichev & Mitsche had for random cubic bisections, now
deterministic, closing the twenty-year `n/6` of Fomin & Høie (2006, held, Theorem 5) and
the "`0.082 n` against `0.167 n`" gap of their concluding remark; `0.24577 n` at maximum
degree 4 (Thm 1.1(b)), `7m/48` per edge (Cor. 1.4); Conjecture 15.1 puts the cubic truth
at `≈ 0.1322 n`. This settles the "UNVERIFIED factor-1 transfer" of
`reports/random_graph_pathwidth_literature_2.md` §3.2, item 4, in the affirmative by the
cutwidth route (not by Bezrukov et al.'s level structure). So for random cubic graphs
**`0.1033 ≤ lim inf pw/n ≤ lim sup pw/n ≤ 0.1398`**, the first moment (`0.070–0.073`) is
dead there, and for `d ≥ 4` KW's `u`-optimised constant is the best floor in print
(`0.149, 0.215, …, 0.425` at `d = 4, 5, 10`) against Gaspers' `0.2458` (`d = 4`) and
Edwards & McDermid's `g(d)` above.

**The cages.** The five open cubic vertex-transitive cages of the dataset
(`reports/complex_lb_search.md` §4), with every random-cubic number evaluated at their
`n` (`cages_table`; floors in pathwidth units, the pairing floor exact, the simple
correction asymptotic):

| graph | `n` | width (record) | floor (record) | pairing floor `< 1` | `< 0.05` | `< 0.01` | simple `< 0.05` | `β*_3 n` | `0.0729 n` | `0.1033 n − 2` | `c₃ n` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Foster | 90 | 20 | 15 | 8 | 6 | 6 | 6 | 6.3 | 6.6 | 7.3 | 12.6 |
| Biggs–Smith | 102 | 19 | 16 | 8 | 8 | 8 | 8 | 7.1 | 7.4 | 8.5 | 14.3 |
| Ljubljana | 112 | 22 | 16 | 10 | 8 | 8 | 8 | 7.8 | 8.2 | 9.6 | 15.7 |
| Balaban 11-cage | 112 | 24 | 17 | 10 | 8 | 8 | 8 | 7.8 | 8.2 | 9.6 | 15.7 |
| Tutte 12-cage | 126 | 26 | 20 | 10 | 10 | 8 | 8 | 8.8 | 9.2 | 11.0 | 17.6 |

Every number a random cubic graph obeys is below the record floor by `5–12`, and the
record *widths* (`0.19–0.21 n`) are above the deterministic asymptotic ceiling
`c₃ n = 0.1398 n` (no contradiction: Gaspers' bound carries an `o(n)`, and on 126
vertices the proved floor `20 > 17.6` only says that term is at least `2.4` there). The
cages are the extremal end of the class — girth-maximal expanders — and the typical
cubic graph has pathwidth between `0.103 n` and `0.140 n`; a statement about the class
cannot certify them. The girth bound of Bachtler & Heinrich (`11–14`,
`complex_lb_search.md` §4.2) and the edge-isoperimetric route (§4.1 there, expected dead
by one or two on the 12-cage) remain the only cubic-specific tools, and neither is
random. Verdict on the row that matters: **the random-cubic theory is covered and says
nothing usable about the cages.**

## 2. Random geometric graphs

The model places `n` uniform points in the unit square and joins pairs within distance
`r`. The empty-pair lemma holds, but the probability that a fixed pair is empty is not a
product over pairs and depends on where the points fall, so neither `FirstMoment.lean`'s
weight nor a symmetry over pairs applies; what survives is Harper's layout form,
`pw ≥ min_{|U| = j} |∂_V U|`, which is exactly how the sharp lower bound in print is
proved: Díaz, Penrose, Petit & Serna (2001; Petit's thesis Theorem 5.10, via the DPS
2002 survey, held) bound the vertex boundary of every `j`-set on an `ε`-good point set
by an isoperimetric inequality on the dissection, and the projection layout (order by
`x`-coordinate; the open vertices at any cut are the points in a strip of width `r`)
matches it: `vs(G(n, r)) / (n r) → 1` a.s. for `r → 0`, `n r² / log n → ∞` (Theorem 5.13).
Mitsche & Perarnau (2012, held) give the orders on both sides of the connectivity
threshold, `Θ(r √n)` and `Θ(log n / log log n)`, for treewidth and treedepth, and their
Remark transfers them to pathwidth. There is no geometric graph on the record. Verdict:
**covered, in print**; this is the one random model where vertex separation has a limit
theorem with its constant, and our theorems add nothing to it.

## 3. Random planar, outerplanar and series-parallel graphs

Our theorems give nothing structural here, and this section says so. The empty-pair
probability is not computable under a uniform planar law; `TreeBound.lean` bounds trees,
the layer lemma `pathwidth_le_layerWidth_dist` (`ForestCover.lean`) bounds by the two
largest consecutive BFS layers, and `ForestCover.lean`'s blow-up bounds MOSP graphs of
forest incidence — none of them sees planarity. What is deterministic: `pw = O(√n)` on
planar graphs (the separator theorem) and `pw ≤ (tw + 1) log₂ n = O(log n)` on
outerplanar and series-parallel graphs (`tw ≤ 2`).

What is in print on the random side is thinner than the brief expected. We found **no
statement of the order of `tw` or `pw` of a uniform random planar graph**: Noy's ICM
survey (open copy, read) gives only the deterministic `O(√n)` of Alon, Seymour & Thomas
for minor-closed classes, and the "`Θ(√n)`" the brief asks about is not in it. From
above there is a better route: the diameter of a random connected labelled planar graph
is `n^{1/4 ± o(1)}` a.a.s. (Chapuy, Fusy, Giménez & Noy 2015, via the abstract and
Noy's item 13), and planar graphs have `tw ≤ 3·diam + 1` (Robertson & Seymour, Graph
Minors III; Eppstein 2000), so `tw = O(n^{1/4 + o(1)})` and `pw = O(n^{1/4 + o(1)} log n)`
a.a.s. — far below `√n`; we found no lower bound beyond the trivial. For outerplanar and
series-parallel graphs the diameter is `n^{1/2 ± ε}` (subcritical classes, same paper)
and `pw = O(log n)`; the constant is not in print, and the nearest result is the random
tree one, `pw / log₂ n ∈ [1/4, 1/2]` (`random_graph_pathwidth_literature_2.md` §3.5).
On the record: `RandomTriangulation_800` (`pw ≤ 40 = 1.41 √n`, provenance `solution`,
open) is the only random planar graph, and the proved planar widths are the 50 VSPLIB
grids and `Grid2dGraph_20_40`, which are not random. Verdict: **open**.

## 4. Random bipartite graphs and the MOSP generators

### 4.1 `G(n, n, p)`

Edges are independent with `p_e = p` across the sides and `0` within, a product measure
the Lean inequality is not stated for (`gnpWeight` has one `p` for every pair), so the
derivation is on paper. For a pair with `a₁ N`, `a₂ N` vertices of `A` and `r₁ N`,
`r₂ N` of `R` on the two sides (`N = 2n`, `p = c/n = 2c/N`) the empty-pair probability
is `(1 − p)^{(a₁ r₂ + a₂ r₁) N²}` and the pair count has exponent
`½ H(2a₁, 2r₁, ·) + ½ H(2a₂, 2r₂, ·)`, so the rate is
`½ H(2a₁, 2r₁, ·) + ½ H(2a₂, 2r₂, ·) − 2c(a₁ r₂ + a₂ r₁)` (`bipartite_pair_rate`). Two
things differ from `G(n, p)`: the pair the lemma produces has a split we do not choose,
so the bound at a given shape `(a, r)` must **sum over splits** (its exponent is the
maximum over `(a₁, r₁)`, `bipartite_shape_rate`); and the degenerate split with `A` and
`R` on the same side has probability one, so no shape with `a + r ≤ ½` gives a bound —
which is right, since `pw(G(n, n, p)) ≤ n = N/2` trivially. Each shape is a valid bound
on its own (Harper's layout form), so `β*_bip(c) = sup{β : min_{a + r = 1 − β} max_{split}
rate < 0}` (`beta_star_bipartite`):

| `c` | 2 | 3 | 4 | 6 | 10 |
|---|---:|---:|---:|---:|---:|
| `β*_bip(c)` (of `N = 2n`) | 0 | 0.0078 | 0.0604 | 0.1693 | 0.3346 |
| `β*(c)` on `G(N, c/N)` | 0 | 0.0087 | 0.0613 | 0.1706 | 0.3371 |

The bipartite constant equals the Erdős–Rényi one at the same mean degree to `0.003`,
the optimal shape balanced across both sides. We found no statement on the pathwidth or
treewidth of `G(n, n, p)` in print; the record's three `RandomBipartite_*` graphs are
single draws with certified widths `9, 23, 9` (two by minors). Verdict: a **new
statement**, small, with nothing in print to compare against.

### 4.2 Chu & Stuckey's `d`-uniform covers: the theorem on its own data

`prob_coversOfMospValueLe_le` (`CliqueCoverMoment.lean`) is the finite inequality for
`m` independent uniform patterns of given sizes; `learning.first_moment` evaluates it
(`log_bound`, `floors`) and `collection_rows` runs it at the realised sizes of every
instance, the optimum read from `learning/data/instances.csv` (all 200 certified; the two
`125 × 125` entries that the stale `instances.csv` still marks `solution` carry
`certified:refutation` in their `solutions/` files, read for the string only). Per class
(`chu_stuckey_cells.csv`; floors in optimum units; `β*` at the realised sizes and at the
nominal `d`; gap `= optimum − 0.01-floor`):

| `(n, m, d)` | `e` | `opt/n` | `β*` sizes | `β*` fixed | `opt` min / mean | floor `< 1` | floor `< 0.01` | gap mean |
|---|---:|---:|---:|---:|---|---:|---:|---:|
| 30, 30, 2 | 1.71 | 0.287 | 0.097 | 0 | 8 / 8.6 | 5.4 | 4.6 | 4.0 |
| 30, 30, 4 | 3.25 | 0.533 | 0.325 | 0.286 | 15 / 16.0 | 13.4 | 11.8 | 4.2 |
| 30, 30, 10 | 8.85 | 0.900 | 0.753 | 0.757 | 26 / 27.0 | 26.6 | 24.6 | 2.4 |
| 50, 50, 2 | 1.84 | 0.264 | 0.118 | 0 | 11 / 13.2 | 9.4 | 7.4 | 5.8 |
| 50, 100, 2 | 3.19 | 0.424 | 0.277 | 0.121 | 19 / 21.2 | 16.6 | 15.8 | 5.4 |
| 75, 75, 2 | 1.80 | 0.211 | 0.110 | 0 | 13 / 15.8 | 10.8 | 9.6 | 6.2 |
| 75, 75, 4 | 3.25 | 0.456 | 0.326 | 0.286 | 32 / 34.2 | 28.4 | 26.4 | 7.8 |
| 100, 50, 4 | 1.85 | 0.264 | 0.133 | 0.072 | 24 / 26.4 | 17.0 | 15.4 | 11.0 |
| 100, 50, 6 | 2.75 | 0.440 | 0.285 | 0.244 | 39 / 44.0 | 33.4 | 31.8 | 12.2 |
| 100, 100, 2 | 1.74 | 0.202 | 0.102 | 0 | 15 / 20.2 | 13.0 | 11.8 | 8.4 |
| 100, 100, 4 | 3.26 | 0.450 | 0.328 | 0.286 | 42 / 45.0 | 37.0 | 35.4 | 9.6 |
| 125, 125, 2 | 1.72 | 0.182 | 0.098 | 0 | 20 / 22.8 | 15.2 | 13.6 | 9.2 |
| 125, 125, 4 | 3.21 | 0.424 | 0.320 | 0.286 | 46 / 53.0 | 44.4 | 42.4 | 10.6 |
| 125, 125, 6 | 5.08 | 0.627 | 0.529 | 0.513 | 74 / 78.4 | 70.8 | 69.6 | 8.8 |
| 125, 125, 10 | 9.01 | 0.826 | 0.762 | 0.757 | 99 / 103.2 | 99.6 | 98.0 | 5.2 |

(all 40 classes in the CSV.) **0 of 200 optima are below the 0.01 floor and 0 are
tight.** The gap grows with `n` at fixed `d` (`4.0 → 9.2` at `d = 2` from 30 to 125
customers, `4.2 → 10.6` at `d = 4`), is largest on the `100 × 50` classes (`11–12`,
where `m < n` makes the union over pairs loosest) and smallest at `d = 10` (`2.4–5.2`,
where `β*` is within `0.07` of `opt/n`). Note that the realised sizes matter at `d = 2`:
the generator's repair (`excess_phase_diagram.md` §0.1) lifts the realised excess to
`1.7–1.8`, so `β*` at the realised sizes is `0.10–0.12` where the nominal `d = 2` gives
`0`. This is the direct test the brief asked for, and it passes with the slack
`excess_phase_diagram.md` §8.5 attributed to the union bound over clustered pairs. The
tight family on these classes is the searched contraction minor (189 of 200,
`reports/obstruction_search.md` §0); Harper's ceiling is below the optimum on the sparse
classes, so no expansion-type count, including this one, can close them.

### 4.3 Harvey's three generators

The 2,130 Harvey instances come in three families, which the file names and
descriptions state (`harvey_family`): `wbo` ("balanced orders, `d` orders per
product"): every pattern has exactly `d` customers, the `d`-uniform cover of §4.2;
`wbp` ("balanced products, `r` products per order"): every customer has exactly `r`
patterns, the patterns' sizes free; `wbop` (both): constant row and column sums, a
regular bipartite incidence graph. The fingerprint of `reports/ml_nature.md` §2 saw the
regularity; the first moment needs a pair probability per family:

- `wbo`: `prob_coversOfMospValueLe_le` as in §4.2.
- `wbp` (`rows_fixed_log_empty_pair`): each customer takes an independent uniform
  `r`-subset `Q_c` of the `m` patterns; the pair is empty iff `Q_A ∩ Q_R = ∅`. Conditioning
  on `|Q_A| = u` (the union of `|A|` random `r`-sets, whose law is a `|A|`-step
  recursion `u → u + x` with `P(x) = C(m − u, x) C(u, r − x) / C(m, r)`),
  `P(empty) = Σ_u P(|Q_A| = u) · (C(m − u, r) / C(m, r))^{|R|}`, exact.
- `wbop` (`regular_bipartite_log_empty_pair`): the bipartite pairing model (`n`
  customers of degree `r`, `m` patterns of size `d`, `nr = md = N`, a uniform bijection
  of half-edges). Label the customer half-edges `A`, `R`, `S` (`α = r|A|`, `ρ = r|R|`,
  `σ` the rest); a pattern is admissible iff its `d` slots carry no `A` and `R` together,
  so the admissible slot labellings are counted by `((x + z)^d + (y + z)^d − z^d)^m` and
  `P(empty) = α! ρ! σ! / N! · [x^α y^ρ z^σ] ((x + z)^d + (y + z)^d − z^d)^m`, computed by
  a log-space DP over the patterns (cached per `(m, d, N)`); the simple-graph conditioning
  is again a constant factor, not applied.

All three are checked against brute-force enumeration (`tests/`). Per family, floors at
0.01 in pathwidth units against the certified `pw = optimum − 1`:

| family | count | `opt/n` | violations (model) | tight | gap mean | gap max | model − uniform floor, by `n = 10 / 15 / 20 / 30` |
|---|---:|---:|---:|---:|---:|---:|---|
| `wbo` | 760 | 0.700 | 0 | 2 | 3.42 | 9 | 0 (it is the uniform model) |
| `wbp` | 760 | 0.819 | 0 | 6 | 2.66 | 11 | `+1.02 / +1.10 / +1.66 / +2.17` |
| `wbop` | 610 | 0.762 | 0 | 0 | 4.32 | 12 | `−0.33 / +0.17 / 0 / +0.17` |

**No violation under any model** (nor under the uniform form applied to all three,
`uniform_viol_0.01 = 0`), and the customers-first model is a genuinely better first
moment on `wbp` — `1–2.2` stacks above the uniform floor, growing with `n` — while the
regular-bipartite pairing floor is within a third of a stack of the uniform one. The
tight family on Harvey is `T` (treewidth + 1, 1,972 of 2,130) and `D` (1,605); the
first moment is tight on 8. Verdict: **covered**, with the two new pair probabilities
as the derivation.

### 4.4 Faggioli–Bentivoglio, Simonis, Shaw, Wilson, SCOOP

The uniform-size inequality applied at the realised sizes is a *measurement* on these
collections, a theorem only where the generator is a uniform cover
(`excess_phase_diagram.md` §4 ran it at the collection level: 0 violations on FB and
Simonis). Per collection (`collections.csv`):

| collection | count | `n` | excess median | `opt/n` | tight | **below floor** | gap mean | gap max |
|---|---:|---|---:|---:|---:|---:|---:|---:|
| Faggioli–Bentivoglio | 300 | 9–50 | 1.98 | 0.400 | 2 | 0 | 4.09 (`0.15 n`) | 8 |
| Simonis | 3,630 | 10–40 | 5.15 | 0.848 | 9 | 0 | 3.16 | 19 |
| Shaw | 25 | 20 | 5.0 | 0.684 | 6 | **2** | 0.68 | 2 |
| Wilson | 20 | 10–100 | 6.6 | 0.587 | 1 | **14** | −5.8 | 10 |
| Miller | 1 | 20 | 6.0 | 0.650 | 0 | 0 | 2 | 2 |
| SCOOP | 24 | 13–134 | 1.35 | 0.234 | 1 | **1** | 3.83 | 9 |

The 16 instances below the floor (and their 16 copies in `MOSP_Instances/Challenge`,
which reproduce them exactly) are not random covers and were never claimed to be:
Wilson's `GP1–GP8` are designed (`50 × 50` at excess `26–39`, `100 × 100` at `53–85`,
"high / medium / low path width", optima `30–95` against floors `48` and `98`), the
`NWRS` instances are the `nwrs*.txt` files of the Challenge release, and `B_REVAL_145` is the SCOOP instance
`excess_phase_diagram.md` §4 already reported two stacks below its floor. On the two
random-cover generators (FB, Simonis) and on Harvey the floor is a bound everywhere;
on the designed ones it is a detector of structure, with the sign telling which way.
Verdict: **measured**, no claim beyond the generators the theorem covers.

## 5. Preferential attachment and power-law graphs

In the Barabási–Albert model `BA(n, m)` each new vertex attaches `m` edges to earlier
vertices with probability proportional to degree. The empty-pair lemma holds for every
graph, so `P(pw ≤ k) ≤ Σ_pairs P(pair empty)` holds for every law; what fails is
everything after it: the pair probability is not a product (`sum_gnpWeight_emptyPairGraphs`
is the step that uses independence), and it is not the same for every pair (a pair whose
`A` is the oldest vertices is far less likely to be empty than one of young vertices), so
the union bound needs a per-pair upper bound on `P(no A–R edge)` that depends on the
pair's age profile. That is exactly Gao's proof (2012, Theorem 3, held, §5): a first
moment over balanced partitions with the attachment probabilities, which yields linear
treewidth a.a.s. for `m ≥ 12` with an implicit `β` — `m ≥ 12` being an artefact of the
estimate, nothing being known for `m < 12`, and nothing for pathwidth beyond `pw ≥ tw`.
We found nothing newer on pathwidth or vertex separation of preferential-attachment
graphs. Our theorems transfer nothing without redoing that per-pair bound.

What the record shows (single draws, PACE 2016's generated instances; `dataset_table`),
with the `G(n, p)` floor at the same mean degree as a *comparison* — not a bound, since
these laws are not product laws:

| graph | `n` | mean degree | width | provenance | `G(n, p)`-matched 0.05-floor | `β*(c)` |
|---|---:|---:|---:|---|---:|---:|
| `RandomBarabasiAlbert_100_2` | 100 | 3.9 | 13 | certified (minor) | 6 | 0.057 |
| `RandomBarabasiAlbert_100_5` | 100 | 9.5 | 34 | certified | 34 | 0.320 |
| `RandomHolmeKim_300_2_2` | 300 | 4.0 | 27 | open | 20 | 0.060 |
| `RandomHolmeKim_700_2_2` | 700 | 4.0 | 57 | open | 44 | 0.061 |
| `RandomNewmanWattsStrogatz_100_5_3` | 100 | 5.4 | 20 | certified (minor) | 16 | 0.138 |
| `RandomNewmanWattsStrogatz_250_10_3` | 250 | 13.1 | **91** | open | **110** | 0.425 |

The last row is the point: a Newman–Watts–Strogatz graph is a ring lattice with
shortcuts, its width `91` is well below what a `G(n, p)` of the same density must have
(`110` at level 0.05), and the "floor" is simply false for it — the product law is not a
bound on any structured model, and the comparison column is to be read as "how far from
Erdős–Rényi", nothing more. The two certified scale-free widths (`0.13 n` at mean degree
4, `0.34 n` at 9.5) happen to sit near the `G(n, p)` numbers. Verdict: **open** for the
constant and for pathwidth; in print only Gao's linear treewidth at `m ≥ 12`.

## 6. Random interval, chordal and split graphs

Deterministic facts first, each elementary. An interval graph is its own path
decomposition (the cliques at the sorted endpoints), so `pw = tw = ω − 1` and the clique
bound `card_le_pathwidth_add_one_of_isClique` is exact. Interval graphs are
cocomparability graphs, and on cocomparability graphs `pw = tw` (Habib & Möhring 1994;
not held, abstract read), so every treewidth floor — degeneracy, contraction degeneracy,
MMD+, the exact treewidth of `learning/treewidth.py` — is a pathwidth floor there and the
treewidth family `T` is exact; this is the "cocomparability fact" of
`reports/complex_lb_search.md`, which also notes that our bound-gap instances have
`pw > tw` and so are nothing of the kind. A split graph with clique `K` and independent
set `I` has the path decomposition with bags `K ∪ {v}`, `v ∈ I`, of width `|K|`, and
`pw ≥ ω − 1 ≥ |K| − 1`, so `pw ∈ {ω − 1, ω}`; `pw = |K| − 1` needs the neighbourhoods of
`I` to split into two nested chains on the two sides of the bag `K` (Helly puts `K` in
one bag), which a random split graph with independent edges fails with high probability,
so its pathwidth is `|K|` and the clique family is tight to within one. Chordal graphs in
general have `pw ≥ tw = ω − 1` with an unbounded gap (trees), and pathwidth is
NP-complete on them (Gustedt 1993).

The random part is then the clique number. For the uniform-endpoint model on `n`
intervals, Scheinerman (1988) gives `χ = n/2 + o_p(n)` (quoted from Diaconis, Holmes &
Janson), hence `ω = pw + 1 = n/2 + o(n)`: the depth of the interval arrangement at the
midpoint is `Bin(n, ½)` and the maximum over the line adds `o(n)`. For random chordal
graphs we found only shape results: the height of random (increasing) `k`-trees is
`~ c log n` (Cooper, Frieze & Uehara 2014), and the uniform chordal graphs of bounded
treewidth have scaling limits (Castellví & Stufler 2023) — nothing on pathwidth. On the
record: `RandomBoundedToleranceGraph_60` and `_80` (bounded tolerance graphs are
cocomparability graphs, Golumbic, Monma & Trotter 1984) are `certified:bound` at widths
`30` and `32`, equal to their contraction degeneracy, two above `ω − 1 = 28, 30`: the
treewidth family doing exactly what `pw = tw` says it must. The corpus's 1,669 complete
MOSP graphs are the degenerate interval case, `pw = n − 1`. Verdict: **covered**, by
identities; our theorems contribute the clique bound and nothing random.

## 7. Hypercubes and grids: the sanity check

On a fixed graph the `G(n, p)` counting theorem says nothing (its content is the number
of graphs on `n` vertices of pathwidth `≤ k`, `card_pathwidth_le_le`), and what the
random-graph theorems reduce to is the lemma itself: Harper's layout form,
`pw ≥ max_t (f(t) − t)`, `f(t) = min_{|A| = t} |N[A]|`, which is family E of Section 5,
and the empty pair at the balanced size, which is the same statement at one `t`. The
brief asked what they give on Harper's own graphs; the answer is "the exact value", and
it was computed rather than asserted (`harper_table`; `f` by the exhaustive branch and
bound of `satisfiability.expansion_bound._f_exact` where it completes, by the initial
segments of Harper's simplicial order on `Q_d` — optimal by Harper's theorem, whose
tie-break was checked against the branch and bound on `Q_3`, `Q_4`):

| graph | `n` | `pw` exact (record / theorem) | Harper, simplicial order | Harper, branch and bound |
|---|---:|---:|---:|---:|
| `Q_3` | 8 | 4 | 4 | 4 (complete) |
| `Q_4` | 16 | 7 | 7 | 7 (complete) |
| `Q_5` | 32 | 13 | 13 | — |
| `Q_6` | 64 | **23** (`CubeGraph_6`, certified by refutation) | **23** | — |
| grid `3 × 3` | 9 | 3 | — | 3 (complete) |
| grid `4 × 4` | 16 | 4 | — | 4 (complete) |
| grid `4 × 6` | 24 | 4 | — | 4 (complete) |
| grid `5 × 5` | 25 | 5 | — | 5 (complete) |
| grid `6 × 6` | 36 | 6 | — | 6 (complete) |

`pw(Q_d) = Σ_{m<d} C(m, ⌊m/2⌋)` is Chandran & Kavitha (2006, held) Theorem 2, which is
Harper's vertex-isoperimetric theorem for the cube (Harper 1966, held) read through
`pw ≥ max_s b_v(s, G)` (their Theorem 1 — our `exists_closedNbhd_card_le`) and the
matching layout; the dataset's `CubeGraph_6 = 23` is that formula's value and was
certified by the search independently of it. On grids Harper's bound equals Ellis &
Warren's `min(h, w)` (2008, held; `Grid.lean` `pathwidth_grid`) on every grid tried, the
balanced empty pair giving it exactly (on `6 × 6`: `f(16) = 22`, so no `5`-set separates `16` from `15` and
`pw ≥ 6`; the diagonal separates `15` from `15` with `6`). The degree family is far
off on both: `Q_6` has degeneracy 6, contraction degeneracy 11, `ω = 2`, against 23; the
grids have degeneracy 2 and MMD+ 4. The dataset's `Grid2dGraph_20_40` (`pw = 20`) is
certified by the theorem (`pathwidth_grid` with `h = 20, w = 40`) and still carries
provenance `solution`, as the VSPLIB grids did before they were upgraded to
`certified:theorem`; the upgrade is proposed, not applied (a dataset rebuild). Verdict:
**covered**: the random-graph lemma is Harper's bound, and Harper's bound is exact on
Harper's graphs.

## 8. The Chu & Stuckey ridge classes

The ridge is `e ≈ 2–2.4`, where refutation cost peaks (`reports/ml_nature.md` §25,
`excess_phase_diagram.md` §0.2); with `m = n` it is the fixed-size generator at `d = 3`,
and the corpus's `d = 2` (`e = 1.7–1.8`) and `d = 4` (`e = 3.2–3.4`) classes flank it.
On the certified fixed-size ensembles (`ensemble_cells`; `β*(d, μ)` at the nominal sizes,
the finite floor at the nominal sizes in optimum units over `n`, `k` instances per cell):

| `n` | `m/n` | `d` | `e` | `opt/n` | `β*` | floor `< 0.01` / `n` | `opt/n − β*` | finite gap / `n` | median nodes |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 40 | 1 | 2 | 1.13 | 0.116 | 0 | 0.025 | 0.116 | 0.091 | 319 |
| 40 | 1 | **3** | 2.05 | 0.289 | 0.140 | 0.175 | 0.149 | 0.114 | **3,255** |
| 40 | 1 | 4 | 3.02 | 0.454 | 0.286 | 0.325 | 0.168 | 0.129 | 2,147 |
| 40 | 1 | 5 | 4.00 | 0.583 | 0.411 | 0.475 | 0.172 | 0.108 | 819 |
| 40 | 1 | 10 | 9.00 | 0.889 | 0.757 | 0.825 | 0.133 | 0.064 | 13 |
| 75 | ½ | 5 | 2.04 | 0.301 | 0.154 | 0.187 | 0.147 | 0.114 | 235,461 |
| 75 | ½ | 7 | 2.99 | 0.480 | 0.319 | 0.347 | 0.162 | 0.134 | 151,131 |
| 75 | 1 | 2 | 1.13 | 0.079 | 0 | 0.013 | 0.079 | 0.066 | 12,465 |
| 75 | 1 | **3** | 2.05 | 0.245 | 0.140 | 0.160 | 0.105 | 0.085 | **4.6 × 10⁶** |
| 75 | 1 | 4 | 3.02 | 0.404 | 0.286 | 0.320 | 0.118 | 0.084 | 3.8 × 10⁶ |
| 75 | 1 | 5 | 4.00 | 0.534 | 0.411 | 0.453 | 0.123 | 0.081 | 932,000 |
| 75 | 1 | 10 | 9.00 | 0.843 | 0.757 | 0.800 | 0.086 | 0.043 | 770 |
| 75 | 2 | **2** | 2.02 | 0.204 | 0.121 | 0.133 | 0.084 | 0.071 | **6.3 × 10⁷** |
| 75 | 2 | 3 | 4.00 | 0.454 | 0.355 | 0.373 | 0.098 | 0.080 | 1.9 × 10⁷ |

(all 126 cells in `ensemble.csv`; 0 violations in every cell.) At the ridge the first
moment is a floor `0.10` below the truth asymptotically and `0.085 n` (six stacks at
`n = 75`) in finite form, and it is *not* loosest there: the gap peaks on the dense
shoulder (`d = 5` at `m = n`, `d = 7` at `m = n/2`, `d = 2–3` at `m = 2n`), exactly as
`excess_phase_diagram.md` §9 found for the floor gap. On the corpus the picture is the
same (§4.2): the `d = 2` classes have `opt/n − β* = 0.08–0.19` and a finite gap of
`4–9` stacks, the `d = 4` classes `0.10–0.20` and `4–11`. What the first moment says at
the ridge, then, is what it says everywhere above `e = 1`: a floor, never within a stack
of a ridge optimum at any size on record, and with no mechanism to get there, since the
slack is the union bound over clustered pairs (§8.5 of the phase diagram) and Harper's
ceiling is below the optimum on the sparse classes (`obstruction_search.md` §0). The
tight family on the ridge classes is the searched contraction minor (39 / 40 at `d = 2`,
34 / 40 at `d = 4`). Verdict: **covered by the theorem, loose where it matters.**

## 9. What is not done, and the record

- **Lean.** Nothing new is formalised. The statements used are `exists_empty_pair` and
  `exists_closedNbhd_card_le` (`EmptyPair.lean`), `weightedSum_graphsOfPathwidthLe_le`
  (`FirstMoment.lean`), `prob_coversOfMospValueLe_le` (`CliqueCoverMoment.lean`),
  `pathwidth_grid` (`Grid.lean`), `card_le_pathwidth_add_one_of_isClique`,
  `tree_pathwidth_le_treeBound` and `pathwidth_le_layerWidth_dist`. The pairing-model,
  rows-fixed, regular-bipartite and `G(n, n, p)` pair probabilities are on paper, each
  checked by enumeration at small sizes; a Lean statement of any of them would be a
  `gnpWeight` with a non-product law, which `LayoutMoment.lean`'s independence lemma
  does not cover.
- **Asymptotics.** `β*_d` and `β*_bip` are numerical roots (`10⁻⁵`, the rate to
  `3 × 10⁻⁴`), not closed forms; the simple-graph correction is asymptotic and never
  applied to a floor that is quoted as a bound.
- **Random geometric, planar, chordal and preferential-attachment graphs** have no
  ensemble on the record and none was generated: the brief allowed computation of our
  formulas only, and these models have no formula of ours to compute.
- **The cages** are untouched; no run was started on any open instance.
- **Proposed, not applied**: `Grid2dGraph_20_40`'s provenance to `certified:theorem`
  (§7).

Regenerate (nothing solved; about three minutes on one core, the `6 × 6` grid's branch
and bound the slowest step):

```bash
nice -n 19 python3 -m learning.random_graph_classes            # all stages -> reports/scratch/random_graph_classes/*.csv, stage_*.log
nice -n 19 python3 -m learning.random_graph_classes --stage gnd   # the beta*_d table (11 s); cages, dataset, collections, harvey, ensemble, harper likewise
python -m pytest tests/test_random_graph_classes.py -q          # 39 tests, 2 s
```
