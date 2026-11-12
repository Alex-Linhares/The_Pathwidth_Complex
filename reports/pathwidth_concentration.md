# The standard deviation of the pathwidth of a random graph

*2026-11-12, one session, outside the loops; the item "The standard deviation of the
pathwidth of a random graph" of `paper1/todo.md`. Three parts: the martingale ceiling
(proved, §1, Lean in `lean/MOSPFormalization/Concentration.lean`), the dense regime
(measured, then the second moment near its threshold, §2), the sparse regime (measured,
§3). Code `learning/pathwidth_concentration.py` (33 tests, `tests/test_pathwidth_concentration.py`); logs and
CSVs under `reports/scratch/pathwidth_concentration/`; every number is beside its
command in §6. Nothing was solved: every width is one already proved on record.*

## 0. Summary — the three answers

**1. The martingale ceiling is a theorem, and it is `√n / 2`.** Pathwidth is 1-Lipschitz
under vertex exposure: two graphs on the same vertices that agree on every pair avoiding
`v` — the edges at `v` arbitrary in both — have pathwidths within one of each other.
Proof: insert `v` into every bag of a decomposition of the other graph. Brute-forced
before stating on every graph with at most 7 vertices (1,252 graphs, every vertex, every
one of the `2^(n−1)` replacements of its neighbourhood: **500,793 pairs, 0 violations**,
the difference exactly one on 209,922 = 41.9%; the 8,475 vertex deletions: 0 violations,
the pathwidth drops on 49.5%; 310,087 distinct labelled graphs, the subset-DP oracle
`fixed_parameter_algorithm.pathwidth` against the bitmask DP of
`learning.staircase_moment` on all of them, 0 disagreements; 89 s). Proved in Lean,
`pathwidth_lipschitz_vertex` (and the vertex-deletion form
`pathwidth_le_induce_compl_add_one`), 18 declarations, no `sorry`, no `axiom`, the three
standard axioms on every one (§4). With `n` exposure coordinates of difference bound 1,
McDiarmid's inequality gives, for **every `p`**,

```
P( |pw(G(n, p)) − E pw| ≥ t ) ≤ 2 exp(−2t² / n),     Var(pw(G(n, p))) ≤ n / 4,
```

so the standard deviation is at most `√n / 2` and the median is within `√(n ln 2 / 2)`
of the mean. Mathlib (rev `1192d624`) has Hoeffding's lemma and the Azuma–Hoeffding
inequality in sub-Gaussian form (`ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF`)
but **not** McDiarmid's inequality, and the Doob martingale of the exposure filtration is
not built here, so the two probabilistic statements are `Prop`s with the citation
(`PathwidthConcentration`, `PathwidthVarianceBound`), never asserted. The observation is
in print for **treewidth**: Gao (2012, held, Lemma 3.3) applies McDiarmid's inequality
(under the name Hoeffding–Azuma) with a tuned Lipschitz constant to a tree-component
count of `G(n, m)`, and Do, Erde & Kang (2024, held, concluding remarks) remark that "rank- and
tree-width are vertex-Lipschitz functions" and hence "tightly concentrated about their
mean, for example using the Azuma–Hoeffding inequality". For pathwidth we found no
explicit statement; the content is the same one line, and no novelty is claimed.

**2. Dense regime: measured, and the transposition of Matula's argument fails at its
first step.** On the four proved `p = ½` cells (20 graphs each at `n = 30, 40, 50, 60`)
the standard deviation of `pw` is **0.70–0.91** (standard error 0.11–0.15), the two most
frequent values carry **0.75–0.95** of the mass, the spread is 2–4 values (the 4 is one
graph at `n = 30` with 186 edges, three standard deviations below the mean count, at
`pw = 16` against a median of 19); the ceiling `√n / 2 = 2.7–3.9` is three to five times
the measured value. Two-point concentration is consistent with the data and so is a
three-value window; 20 graphs per cell cannot tell them apart. On paper: the corner-block
first moment drops by a factor `n^{−(a* − 2)} = n^{−1.414}` per unit of `s` at its
threshold `s*` (measured `e^{−3.2}` to `e^{−3.8}` per step at `n = 30–60`, where
`log₂ n` is only 5–6), as polynomially as the clique count does, so the **upper tail is
sharp to one step**: `P(n − pw ≥ s* + 1) ≤ n^{−1.414 + o(1)}`. The lower tail is the
second moment on staircases, and here the transposition fails. Writing the ratio
`E[X²]/E[X]²` exactly as a sum over partial injections `τ` from the slots of a fixed
staircase to the slots of another (`ratio_from_injections`; the identity checked
against the enumerated ratio on four `(n, s)` at two values of `p`), the dangerous terms
are the bijections of the corner block onto itself, and for those the overlap lost
against the aligned placement is at least the **floored depth** `Σ_i (π(i) − max(i, F))⁺`
of either permutation, with equality when the other is the identity (the loss lemma,
brute-forced on eight blocks to 86,400 pairs, 0 violations). The generating function
`Ψ_{ℓ,F}(x) = Σ_π x^{depth_F(π)}` has a transfer matrix over the number of open
positions (`depth_gf`, checked against enumeration to `ℓ = 8`) with a finite spectral
radius, so the family's slack against `1 / E[blocks]` is **`e^{κ L}`, `L = log_b n` — a
polynomial in `n`, not `e^{Θ(L log L)}`: the kill criterion as stated is not met** — but
its rate is compared with the first moment's gain `(a* − 2) ln b` per step, and the
comparison goes the wrong way: at `p = ½`, a sub-family whose contribution is **exact**
(one permutation free, the other the identity on the sloped part) is
`≥ n^{1.82} / E_sym[B(s)]`, which at `s = s* − 1` is `≥ n^{+0.41} → ∞`; the family's
proved upper bracket is `n^{6.28} / E_sym`. So the ratio **tends to one only within
`s* − O(1)` with the `O(1)` between 3 and 6 values at `p = ½`** (between 6 and 14 at
`p = 0.3`, between 2 and 3 at `p = 0.7`), never within one step for `p ≤ ½`, and the
complete sum over all `τ` is not bounded at all. What the computation shows is *why*
cliques concentrate on two values and staircases need not: a clique has no roles and the
`k!` relabellings are divided out exactly, while a staircase has `e^{Θ(L)}` cheap
deformations — permutations of its sloped part of small depth — each a distinct forced
set of nearly the same cost, an intrinsic clustering the second moment pays for. **Neither
two-point concentration nor its failure is proved**; the standard deviation `O(1)` in the
dense regime is the expected truth, consistent with the record, and not a theorem of this
session. §2.8 says what would be needed (a second moment on clusters, or a canonical
staircase); Janson's inequality changes the rate and not the window.

**3. Sparse regime: measured; `√n` and `n^{1/2 − o(1)}` cannot be told apart, bounded
is rejected.** On the `G(n, c/n)` pilot (c fixed, 137 proved graphs per cell at
`n = 20–60`, 12–13 at `70–120`, censoring recorded) the standard deviation at
`c = 3–10` is **1.0–1.5 at `n = 20–60`**, 0.31–0.47 of the ceiling `√n / 2`, with
coefficient of variation falling from 0.26 (`c = 3`, `n = 20`) to 0.04 (`c = 10`,
`n = 60`). The weighted fit `sd ∝ n^γ` over the uncensored cells gives **`γ = 0.34–0.43
± 0.07`** at `c = 3, 4, 6, 8, 10` (`n ≤ 70–80`): `γ = 0` is rejected at every `c ≥ 2`
(`χ² = 33–56` against 2.5–12 for the free fit, 4–8 degrees of freedom), `γ = ½` is within
two standard errors at `c = 2, 4, 6, 8, 10` and 2.4 standard errors away at `c = 3`; the
data span a factor 3.5–4 in `n`, over which an `o(1)` correction to the exponent moves
`ln sd` by less than the 0.07 standard error — **`√n` and `n^{1/2 − o(1)}` are
indistinguishable here, as the brief expected**, and nothing at `n ≤ 120` can separate
them. The Bernoulli clique-cover cells of `learning/data/ensemble/` (180 cells, 150 per
cell at `n ≤ 40`, 50 at `50–75`; `pw = optimum − 1` of the MOSP graph, a random
intersection graph and **not** `G(n, p)`) are tabulated for the record; at fixed `p` they
are not a fixed-degree family (the degree grows with `n`, the graph fills up at
`p = 0.2`), so they answer no growth question.

## 1. Part 1: the martingale ceiling

### 1.1 The lemma

**Lemma (vertex exposure is 1-Lipschitz).** Let `G, G'` be graphs on the same finite
vertex set and `v` a vertex such that `G.Adj u w ↔ G'.Adj u w` for all `u, w ≠ v`. Then
`pw(G) ≤ pw(G') + 1` and `pw(G') ≤ pw(G) + 1`.

*Proof.* Take a path decomposition `P` of `G'` of width `pw(G')` and put `v` into every
bag. Every vertex is still covered. An edge `uw` of `G` with `u, w ≠ v` is an edge of
`G'` and lies in some bag of `P`, hence in the new bag; an edge `vw` lies in any bag
containing `w`. The bags containing `v` are all of them, an interval; the bags containing
any other vertex are unchanged. Every bag grew by at most one, so the width is at most
`pw(G') + 1`. The other inequality is the same with the roles exchanged. ∎

Corollaries proved the same way: removing the edges at `v` lowers the pathwidth by at
most one and never raises it (`pathwidth_le_deleteIncidenceSet_add_one`,
`pathwidth_deleteIncidenceSet_le`); deleting `v` lowers it by at most one
(`pathwidth_le_induce_compl_add_one`, the bags lifted along the inclusion and `v`
inserted; the other direction is `pathwidth_induce_le` of `Minor.lean`).

### 1.2 The brute force

`python -m learning.pathwidth_concentration lipschitz` (`lipschitz.log`): the networkx atlas, every
graph on 1–7 vertices (1,252), every vertex `v`, every subset of the other vertices as the
new neighbourhood of `v`. 500,793 `(G, v, N')` pairs, 0 with `|pw − pw'| > 1`; 290,871
with equal pathwidth and 209,922 differing by one. 8,475 deletions `(G, v)`, 0 with
`pw(G − v)` outside `{pw(G) − 1, pw(G)}`, 4,198 (49.5%) where it drops. 310,087 distinct
labelled graphs evaluated; the oracle (`compute_pathwidth`, the subset DP of
`fixed_parameter_algorithm/pathwidth.py`) agreed with the independent bitmask DP
`pathwidth_exact` on every one. 88.6 s on one core at nice 19.

### 1.3 The inequality

With the vertices exposed one at a time, `pw(G(n, p))` is a function of `n` independent
coordinates (the `i`-th coordinate is the set of edges from `v_i` to `v_1 … v_{i−1}`),
and the lemma says changing one coordinate changes the value by at most one. McDiarmid
(1989, Lemma 1.2) then gives, for every `0 ≤ p ≤ 1` and `t ≥ 0`,

```
P( pw − E pw ≥ t ) ≤ exp(−2t²/n),   P( pw − E pw ≤ −t ) ≤ exp(−2t²/n),
```

hence `P(|pw − E pw| ≥ t) ≤ 2 exp(−2t²/n)` (`mcdiarmid_tail`); and the Efron–Stein
inequality in its bounded-differences form (Efron & Stein 1981; Steele 1986; Boucheron,
Lugosi & Massart 2013, Corollary 3.2) gives `Var(pw) ≤ ¼ Σ_i c_i² = n/4`
(`variance_ceiling`). For the median: the one-sided tail is below `½` once
`t > √(n ln 2 / 2)`, so `|E pw − M| ≤ √(n ln 2 / 2) = 0.589 √n` (`median_shift`), and
`P(|pw − M| ≥ t) ≤ 2 exp(−2(t − 0.589√n)²/n)` for `t ≥ 0.589 √n`. This is the argument of
Shamir & Spencer (1987) for the chromatic number, where the same `n` coordinates give
Gaussian tails on the scale `√n` (their constant is Azuma's, `exp(−λ²/2)` at `t = λ√n`;
McDiarmid's form sharpens it to `exp(−2λ²)`). Against the record: at `n = 60`, `p = ½`, the ceiling is `sd ≤ 3.87`
and the measured `sd = 0.76`; at `n = 60`, `c = 4`, `3.87` against `1.53`. The ceiling is
never tight anywhere on record (§2.1, §3.1).

**Mathlib.** `grep` over the pinned Mathlib (`lean/.lake/packages/mathlib`, rev
`1192d624`): no `McDiarmid`, no `bounded_difference`; `Mathlib/Probability/Moments/SubGaussian.lean`
has Hoeffding's lemma (`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`) and the
Azuma–Hoeffding inequality for sums of conditionally sub-Gaussian martingale differences
(`measure_sum_ge_le_of_hasCondSubgaussianMGF`). Deriving McDiarmid from it needs the
Doob martingale `E[pw | ℱ_i]` of the exposure filtration on the finite product space, the
measurability plumbing, and Hoeffding's lemma under the conditional kernel (a difference
in an interval of length ≤ 1 is conditionally sub-Gaussian with parameter `¼`); that is a
formalisation project of its own and was not attempted. The Lean file states the two
inequalities as `Prop`s with the citation.

## 2. Part 2: the dense regime

### 2.1 The measurement

The `p = ½` cells of `reports/scratch/random_graph_middle/results.csv` (every graph proved
by the C program on 2026-11-11, 20 per cell). `s_block` is the largest `s` whose
corner-block first moment (symmetric count, `learning.staircase_moment.block_threshold`)
is at least one — the "threshold" of `reports/dense_staircase.md` §4, equal to the median
`n − pw` plus one at every size — and `s* = s_block + 1` the least `s` where it is below
one; the last column but one is `ln` of the ratio of the block bound at `s*` to that at
`s* − 1`, against its limit `−(a* − 2) ln n`.

| `n` | `L = log₂ n` | `pw` histogram | mean | sd (± se) | top-2 mass | spread | `n − pw` median | `s_block` | `s*` | ln drop/step at `s*` (limit) | `√n/2` |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 30 | 4.91 | 16:1, 19:11, 20:8 | 19.25 | 0.91 (± 0.15) | 0.95 | 4 | 11 | 12 | 13 | -3.21 (-4.81) | 2.74 |
| 40 | 5.32 | 26:1, 27:1, 28:12, 29:6 | 28.15 | 0.75 (± 0.12) | 0.90 | 3 | 12 | 13 | 14 | -3.50 (-5.22) | 3.16 |
| 50 | 5.64 | 36:3, 37:10, 38:7 | 37.20 | 0.70 (± 0.11) | 0.85 | 2 | 13 | 14 | 15 | -3.35 (-5.53) | 3.54 |
| 60 | 5.91 | 45:5, 46:9, 47:6 | 46.05 | 0.76 (± 0.12) | 0.75 | 2 | 14 | 15 | 16 | -3.82 (-5.79) | 3.87 |

The `n − pw` distributions are `{10:8, 11:11, 14:1}`, `{11:6, 12:12, 13:1, 14:1}`,
`{12:7, 13:10, 14:3}`, `{13:6, 14:9, 15:5}`: the mass sits on `s_block − 1` and
`s_block − 2`, with a few graphs at `s_block` itself (3 at `n = 50`, 5 at `n = 60`) and one
or two beyond. The spread of 2 at `n = 50, 60` and
the two-value mass of 0.85 and 0.75 are what a two-point law with `P ≈ 0.6 / 0.4` would
show at `N = 20`, and also what a three-value law would show; no decision is possible at
this sample. The martingale ceiling `√n / 2` is 3.0–5.1 times the measured standard
deviation.

### 2.2 The per-step drop of the first moment

For the block `(a, b)` at size `s`, `c(s + 1, a, b) − c(s, a, b) = a + b − s`
(`block_cost`), so the block bound drops by `q^{a + b − s}` per unit of `s`; at the
optimal block `a = b = (a* − 1) L` that is `n^{−(a* − 2)} = n^{−1.414}`, and re-optimising
`(a, b)` only helps. So `P(n − pw ≥ s* + 1) ≤ n^{−1.414 + o(1)}`: the **upper tail of
`n − pw` is sharp to one step**, exactly as the clique count's `n^{−1}` per step makes the
clique number's upper tail sharp. At the record's sizes the drop is `e^{−3.2}` to
`e^{−3.8}` per step (table), smaller than the limit `e^{−4.8}` to `e^{−5.8}` because the
optimal block at `L ≈ 5–6` is far from `(a* − 1) L` square.

### 2.3 The ratio as a sum over partial injections

Fix a staircase placement `S_0` (slots `v_1 … v_m`, `u_1 … u_m`, `m = s − 1`) with forced
pairs `F_0 = {(u_i, v_j) : i + j ≤ s}`. A placement `S'` is determined, as far as its
overlap with `S_0` goes, by the partial injection `τ` sending each `S_0`-slot whose vertex
`S'` reuses to the `S'`-slot it occupies; the vertices outside `S_0` are
`(n − 2m)_{2m − |τ|}` choices. So

```
R = E[X²]/E[X]² = Σ_τ (n − 2m)_{2m − |τ|} / (n)_{2m} · b^{ov(τ)},
ov(τ) = #{ forced S_0-pairs inside dom τ whose images are forced in S' },
```

an exact identity (`ratio_from_injections`), equal to `exact_ratio_small` of
`learning.staircase_moment` on `(n, s) = (4, 2), (5, 2), (5, 3), (6, 3)` at `q = ½, ⅓`
(rationals; `tests/test_pathwidth_concentration.py`). The weight is `n^{−|τ|}(1 + o(1))` for
`|τ| = O(log n)`, so `R ≈ Σ_τ n^{−|τ|} b^{ov(τ)}`. The aligned `τ` on the block
`[a] ∪ [b]` (same roles, same indices) gives `n^{−(a+b)} b^{c(s,a,b)} = 1 / E_ord[B(s,a,b)]`,
the reciprocal of the ordered block count — the analogue of the `j = k` term `1 / E[X_k]`
of the clique computation (Frieze & Karoński, Theorem 7.3, read verbatim on 2026-11-11).
What differs from cliques is how many `τ` sit near the aligned one at nearly the same
overlap.

### 2.4 The loss lemma

Take the bijections of the block onto itself in the same roles, `u_i ↦ u'_{π_u(i)}`,
`v_j ↦ v'_{π_v(j)}`. The forced pairs kept are `#{(i, j) : i + j ≤ s, π_u(i) + π_v(j) ≤ s}`
(`overlap_perm`). For fixed `i`, among the `r_i = min(a, s − i)` pairs `(i, j)` forced in
`S_0`, at most `s − π_u(i)` can have `π_v(j) ≤ s − π_u(i)` (injectivity of `π_v`), so at
least `(r_i − s + π_u(i))⁺ = (π_u(i) − max(i, s − a))⁺` are lost. Summing:

```
loss(π_u, π_v) ≥ max( depth_{s−a}(π_u), depth_{s−b}(π_v) ),   depth_F(π) = Σ_i (π(i) − max(i, F))⁺,
```

with **equality** `loss(π_u, id) = depth_{s−a}(π_u)`. The floor `F = s − a` is the length
of the *flat* part of the block (the `u_i` forced against every `v_j` of the block), whose
permutations cost nothing — they are the `(s − a)! (s − b)!` relabellings that the
symmetric count divides out, which is why the right first moment is `E_sym` and the
aligned term is `1 / (E_sym · (s−a)! (s−b)!)`. Brute-forced (`check_loss_lemma`,
`overlap.log`): blocks `(s, a, b) = (4,3,3), (5,3,3), (5,4,4), (6,4,4), (6,5,5), (7,5,5),
(7,5,4), (8,6,5)`, every pair of permutations (36 to 86,400 pairs), 0 violations of the
inequality, 0 of the equality.

### 2.5 The depth generating function and its rate

`depth_F(π) = Σ_{k ≥ F} e_k(π)` with `e_k = #{i ≤ k : π(i) > k}`, the number of positions
open after step `k`. Scanning `k = 1 … ℓ` with the state `e`, position `k` either takes
value `k` (`e` unchanged, 1 way), takes an open value while value `k` closes an open
position (`e − 1`, `e²` ways), takes an open value while value `k` is deferred or is
deferred while value `k` closes an open position (`e` unchanged, `e` ways each), or both
are deferred (`e + 1`, 1 way); the weight `x^e` is charged after every step `k ≥ F`. So
`Ψ_{ℓ,F}(x) = Σ_π x^{depth_F(π)}` is a product of tridiagonal transfer matrices
(`depth_gf`; `log_depth_gf` for `ℓ` in the thousands), equal to the enumeration on
`ℓ ≤ 8`, `F ∈ {1, 3}`, four values of `x` (`overlap.log`), to `1 + x` and
`1 + 2x + 3x²` at `ℓ = 2, 3`, and to `ℓ!` at `x = 1`. The entries `e² x^{e−1}` are
bounded, so the growth rate `κ₀(x) = lim (1/ℓ) ln Ψ_ℓ(x)` is the log spectral radius of
the matrix (`depth_rate`, power iteration on `e ≤ 80`, equal to the finite ratio
`ln Ψ_201 − ln Ψ_200` to `2 · 10⁻³`): `κ₀ = 0.437, 0.871, 1.474` at `x = 0.3, 0.5, 0.7`
and `0.994, 1.500, 2.137` at `x = √0.3, √0.5, √0.7`. **The slack is exponential in `ℓ`,
not in `ℓ log ℓ`.**

### 2.6 The window

At `s = a* L`, `a = b = (a* − 1) L`, the flat floor is `F = L` and the sloped length
`(a* − 2) L = 1.414 L`. The family's slack against `1 / E_sym[B]`, from §2.4:

```
lower (exact for the sub-family π_v flat-only):  Ψ_{b,L}(q) / L!
upper (loss ≥ max of the depths, q^max ≤ q^{(d_u + d_v)/2}, both roles):  2 Ψ_{b,L}(√q) Ψ_{a,L}(√q) / (L!)²
```

(`family_slack_log`; on the small blocks `(6,4,4), (7,5,5), (8,6,6)` the exact family sum
sits between them, nearer the upper: `ln = 3.40, 5.33, 7.37` against brackets
`[1.45, 4.54], [2.24, 6.84], [3.07, 9.32]` at `q = ½`, `family_exact_log`). Per unit of
`L` (slopes between `L = 160` and `320`, the asymptotic rates in brackets), against the
first moment's gain `(a* − 2) ln b` per step of `s`:

| `p` | `ln b` | gain / step | `κ_lo` | `κ_hi` | `σ_lo = κ_lo / gain` | `σ_hi` | window (values of `n − pw`) | sub-family exponent at `s* − 1` |
|---|---|---|---|---|---|---|---|---|
| 0.3 | 0.357 | 0.504 | 2.138 (2.084) | 6.232 (6.046) | 4.24 | 12.35 | 6 … 14 | `+4.58` |
| 0.5 | 0.693 | 0.980 | 1.263 (1.232) | 4.355 (4.244) | 1.29 | 4.44 | 3 … 6 | `+0.41` |
| 0.7 | 1.204 | 1.703 | 0.636 (0.618) | 2.882 (2.812) | 0.37 | 1.69 | 2 … 3 | `−0.89` |

Reading: the family's term at `s = s* − k` is between `n^{κ_lo/ln b} / E_sym(s* − k)` and
`n^{κ_hi/ln b} / E_sym(s* − k)`, and `E_sym(s* − k) ≥ n^{(a* − 2)(k − 1)}` with nothing
better guaranteed (`E_sym(s* − 1) ≥ 1` is all the definition gives), so the term vanishes
for `k > σ + 1` and the second moment certifies `n − pw ≥ s* − k` only there; choosing
the reference level as Matula does (the largest `s` with `E_sym ≥ n^{(a* − 2)(σ + ε)}`)
puts `n − pw` in a window of `⌈σ + 1⌉` consecutive values whp (`window_estimate`),
**if the family bound is the whole sum** — the sum over the other `τ` (sub-blocks, role
swaps, images outside the block, partial overlaps) is of the same mechanism and is not
bounded here. The last column is `κ_lo / ln b − (a* − 2)`: at `p = ½` the exact
sub-family alone is `≥ n^{0.41} → ∞` at `s* − 1`, so **no second moment on the ordered
staircase count tends to one at `s* − 1` for `p ≤ ½`**; at `p = 0.7` the sub-family
vanishes there and only the upper bracket (window 3) is in the way.

### 2.7 Verdict

- **Kill criterion** ("the overlap sum does not tend to one within `s* − O(1)`, the shared
  corner-block terms dominate"): **not met** in the form stated — the corner-block terms do
  dominate, but their slack is `e^{Θ(L)} = n^{Θ(1)}`, so they vanish within `s* − O(1)`
  (the `O(1)` is 3–6 steps at `p = ½`) — and **met in substance**: they do not vanish
  within `s* − 1`, which is what two-point concentration needs.
- **Two-point concentration** of `n − pw(G(n, p))`: neither proved nor refuted. The second
  moment on staircases cannot prove it for `p ≤ ½` (exact sub-family), and what it could
  prove — a window of `⌈σ_hi + 1⌉` values — rests on a bound over all `τ` that is not
  established.
- **What is proved**: the upper tail sharp to one step (§2.2, from the Lean inequality
  `weightedSum_pathwidth_le_block`); the lower tail within `o(L)` (`reports/dense_staircase.md`
  §3); `sd ≤ √n / 2` for every `p` (§1).
- **What the record says**: `sd = 0.70–0.91` at `n = 30–60`, `p = ½`, a two-value mass of
  0.75–0.95; consistent with two-point, with three-point, and four to five times below
  the proved ceiling.

### 2.8 What would be needed

The slack is the number of *distinct* forced sets within a bounded overlap distance of a
given one — the sloped permutations of small depth — and is intrinsic to the structure:
in a graph that has one staircase, the typical number of staircases is `e^{Θ(L)}` times
the number of flat relabellings. A second moment that concentrates must count *clusters*
(components of the overlap graph of staircases) or a canonical representative (the
lexicographically least staircase, the greedy one of Lemma 2 of `dense_staircase.md`),
whose second moment has no `τ` of small depth; the obstacle is that canonicity is a
condition on the whole graph, not on the placement. Janson's inequality on the ordered
count gives `P(X = 0) ≤ exp(−μ²/(2Δ))` with `Δ/μ² = R − 1`, the same sum, so it sharpens
the rate and leaves the window where it is. For `p > ½` the arithmetic of §2.6 is kinder
(window 2–3 at `p = 0.7`, the sub-family no longer in the way), so a proof of two-point
concentration for `p` near one is the easier target if one is wanted.

## 3. Part 3: the sparse regime

### 3.1 `G(n, c/n)`, `c` fixed: the pilot

`reports/scratch/gnp_pilot/results.csv` (2026-10-18; `nx.gnp_random_graph(n, c/n)`,
proved by the C program), proved widths only; a cell is *censored* when some of its graphs
were not proved (their widths are unknown and the unproved ones are the hard ones, so a
censored cell is biased); cells with fewer than 10 proved graphs are omitted
(`n = 80–120` at `c ≥ 4`).

| `c` | `n` | `N` | mean | sd (± se) | cv | min–max | top-2 mass | sd / (√n/2) |
|---|---|---|---|---|---|---|---|---|
| 0.5 | 20 | 137 | 1.03 | 0.21 (± 0.01) | 0.202 | 0–2 | 0.99 | 0.09 |
| 1 | 20 | 137 | 1.39 | 0.52 (± 0.03) | 0.373 | 1–3 | 0.99 | 0.23 |
| 1.5 | 20 | 137 | 1.86 | 0.58 (± 0.04) | 0.314 | 1–4 | 0.91 | 0.26 |
| 2 | 20 | 137 | 2.42 | 0.69 (± 0.04) | 0.287 | 1–4 | 0.88 | 0.31 |
| 3 | 20 | 137 | 3.95 | 1.01 (± 0.06) | 0.256 | 2–7 | 0.66 | 0.45 |
| 4 | 20 | 137 | 5.44 | 1.01 (± 0.06) | 0.186 | 3–8 | 0.69 | 0.45 |
| 6 | 20 | 137 | 7.87 | 0.90 (± 0.05) | 0.114 | 5–10 | 0.73 | 0.40 |
| 8 | 20 | 137 | 9.77 | 0.81 (± 0.05) | 0.083 | 7–12 | 0.80 | 0.36 |
| 10 | 20 | 137 | 11.42 | 0.79 (± 0.05) | 0.069 | 9–13 | 0.84 | 0.35 |
| 0.5 | 30 | 137 | 1.05 | 0.25 (± 0.02) | 0.240 | 0–2 | 0.99 | 0.09 |
| 1 | 30 | 137 | 1.42 | 0.54 (± 0.03) | 0.378 | 1–3 | 0.98 | 0.20 |
| 1.5 | 30 | 137 | 2.01 | 0.64 (± 0.04) | 0.318 | 1–4 | 0.85 | 0.23 |
| 2 | 30 | 137 | 2.89 | 0.84 (± 0.05) | 0.290 | 1–6 | 0.78 | 0.31 |
| 3 | 30 | 137 | 4.96 | 1.20 (± 0.07) | 0.241 | 2–8 | 0.55 | 0.44 |
| 4 | 30 | 137 | 7.09 | 1.16 (± 0.07) | 0.164 | 4–10 | 0.64 | 0.42 |
| 6 | 30 | 137 | 10.49 | 1.18 (± 0.07) | 0.113 | 6–13 | 0.61 | 0.43 |
| 8 | 30 | 137 | 13.39 | 1.02 (± 0.06) | 0.076 | 11–16 | 0.68 | 0.37 |
| 10 | 30 | 137 | 15.47 | 0.97 (± 0.06) | 0.063 | 13–18 | 0.70 | 0.35 |
| 0.5 | 40 | 137 | 1.04 | 0.19 (± 0.01) | 0.182 | 1–2 | 1.00 | 0.06 |
| 1 | 40 | 137 | 1.58 | 0.55 (± 0.03) | 0.348 | 1–3 | 0.97 | 0.17 |
| 1.5 | 40 | 137 | 2.31 | 0.71 (± 0.04) | 0.309 | 1–5 | 0.88 | 0.23 |
| 2 | 40 | 137 | 3.36 | 1.01 (± 0.06) | 0.299 | 1–6 | 0.70 | 0.32 |
| 3 | 40 | 137 | 6.03 | 1.24 (± 0.07) | 0.205 | 2–9 | 0.58 | 0.39 |
| 4 | 40 | 137 | 8.81 | 1.19 (± 0.07) | 0.135 | 5–12 | 0.58 | 0.37 |
| 6 | 40 | 137 | 13.37 | 1.17 (± 0.07) | 0.087 | 11–16 | 0.61 | 0.37 |
| 8 | 40 | 137 | 17.04 | 1.21 (± 0.07) | 0.071 | 13–20 | 0.64 | 0.38 |
| 10 | 40 | 137 | 19.72 | 1.07 (± 0.06) | 0.054 | 17–23 | 0.63 | 0.34 |
| 0.5 | 50 | 137 | 1.05 | 0.22 (± 0.01) | 0.210 | 1–2 | 1.00 | 0.06 |
| 1 | 50 | 137 | 1.58 | 0.49 (± 0.03) | 0.312 | 1–2 | 1.00 | 0.14 |
| 1.5 | 50 | 137 | 2.63 | 0.78 (± 0.05) | 0.296 | 1–5 | 0.85 | 0.22 |
| 2 | 50 | 137 | 3.68 | 1.08 (± 0.07) | 0.293 | 2–7 | 0.71 | 0.30 |
| 3 | 50 | 137 | 7.08 | 1.47 (± 0.09) | 0.208 | 4–10 | 0.46 | 0.42 |
| 4 | 50 | 137 | 10.28 | 1.44 (± 0.09) | 0.140 | 7–14 | 0.53 | 0.41 |
| 6 | 50 | 136 | 16.27 | 1.41 (± 0.09) | 0.086 | 12–19 | 0.55 | 0.40 |
| 8 | 50 | 137 | 20.37 | 1.22 (± 0.07) | 0.060 | 17–23 | 0.60 | 0.35 |
| 10 | 50 | 136 | 23.74 | 1.11 (± 0.07) | 0.047 | 21–27 | 0.67 | 0.31 |
| 0.5 | 60 | 137 | 1.06 | 0.24 (± 0.01) | 0.222 | 1–2 | 1.00 | 0.06 |
| 1 | 60 | 137 | 1.70 | 0.51 (± 0.03) | 0.297 | 1–3 | 0.98 | 0.13 |
| 1.5 | 60 | 137 | 2.71 | 0.75 (± 0.05) | 0.277 | 1–5 | 0.85 | 0.19 |
| 2 | 60 | 137 | 4.26 | 1.02 (± 0.06) | 0.238 | 2–7 | 0.66 | 0.26 |
| 3 | 60 | 136 | 8.13 | 1.48 (± 0.09) | 0.183 | 5–12 | 0.49 | 0.38 |
| 4 | 60 | 136 | 12.27 | 1.53 (± 0.09) | 0.125 | 8–17 | 0.54 | 0.40 |
| 6 | 60 | 134 | 18.78 | 1.44 (± 0.09) | 0.077 | 16–23 | 0.50 | 0.37 |
| 8 | 60 | 132 | 24.03 | 1.33 (± 0.08) | 0.055 | 20–26 | 0.54 | 0.34 |
| 10 | 60 | 133 | 27.80 | 1.20 (± 0.07) | 0.043 | 25–32 | 0.59 | 0.31 |
| 0.5 | 70 | 12 | 1.00 | 0.00 (± 0.00) | 0.000 | 1–1 | 1.00 | 0.00 |
| 1 | 70 | 12 | 1.75 | 0.62 (± 0.13) | 0.355 | 1–3 | 0.92 | 0.15 |
| 1.5 | 70 | 12 | 2.67 | 0.78 (± 0.17) | 0.292 | 2–4 | 0.83 | 0.19 |
| 2 | 70 | 12 | 5.17 | 0.94 (± 0.20) | 0.181 | 4–7 | 0.67 | 0.22 |
| 3 | 70 | 12 | 9.33 | 1.97 (± 0.42) | 0.211 | 6–13 | 0.50 | 0.47 |
| 4 | 70 | 12 | 12.92 | 1.68 (± 0.36) | 0.130 | 11–16 | 0.58 | 0.40 |
| 6 | 70 | 12 | 21.08 | 1.56 (± 0.33) | 0.074 | 18–23 | 0.50 | 0.37 |
| 8 | 70 | 12 | 27.92 | 1.16 (± 0.25) | 0.042 | 27–30 | 0.75 | 0.28 |
| 10 | 70 | 12 | 32.25 | 1.71 (± 0.37) | 0.053 | 29–35 | 0.58 | 0.41 |
| 0.5 | 80 | 12 | 1.25 | 0.45 (± 0.10) | 0.362 | 1–2 | 1.00 | 0.10 |
| 1 | 80 | 12 | 1.50 | 0.52 (± 0.11) | 0.348 | 1–2 | 1.00 | 0.12 |
| 1.5 | 80 | 12 | 3.33 | 0.89 (± 0.19) | 0.266 | 2–5 | 0.75 | 0.20 |
| 2 | 80 | 12 | 4.67 | 1.50 (± 0.32) | 0.321 | 2–6 | 0.75 | 0.33 |
| 3 | 80 | 12 | 9.42 | 1.08 (± 0.23) | 0.115 | 8–11 | 0.58 | 0.24 |
| 4 | 80 | 12 | 15.17 | 1.80 (± 0.38) | 0.119 | 13–18 | 0.58 | 0.40 |
| 0.5 | 90 | 13 | 1.15 | 0.38 (± 0.08) | 0.325 | 1–2 | 1.00 | 0.08 |
| 1 | 90 | 13 | 1.77 | 0.44 (± 0.09) | 0.248 | 1–2 | 1.00 | 0.09 |
| 1.5 | 90 | 13 | 3.00 | 0.71 (± 0.14) | 0.236 | 2–4 | 0.77 | 0.15 |
| 2 | 90 | 13 | 5.54 | 1.66 (± 0.34) | 0.300 | 3–9 | 0.62 | 0.35 |
| 3 | 90 (censored 1) | 12 | 11.17 | 1.90 (± 0.40) | 0.170 | 8–14 | 0.50 | 0.40 |
| 0.5 | 100 | 13 | 1.15 | 0.38 (± 0.08) | 0.325 | 1–2 | 1.00 | 0.08 |
| 1 | 100 | 13 | 1.85 | 0.38 (± 0.08) | 0.203 | 1–2 | 1.00 | 0.08 |
| 1.5 | 100 | 13 | 2.85 | 0.80 (± 0.16) | 0.281 | 2–4 | 0.77 | 0.16 |
| 2 | 100 | 13 | 6.08 | 1.55 (± 0.32) | 0.255 | 3–8 | 0.54 | 0.31 |
| 3 | 100 (censored 1) | 12 | 11.83 | 1.59 (± 0.34) | 0.134 | 9–14 | 0.67 | 0.32 |
| 0.5 | 120 | 13 | 1.15 | 0.38 (± 0.08) | 0.325 | 1–2 | 1.00 | 0.07 |
| 1 | 120 | 13 | 2.08 | 0.28 (± 0.06) | 0.134 | 2–3 | 1.00 | 0.05 |
| 1.5 | 120 | 13 | 4.08 | 0.95 (± 0.19) | 0.234 | 3–6 | 0.69 | 0.17 |
| 2 | 120 | 13 | 6.08 | 0.95 (± 0.19) | 0.157 | 4–7 | 0.77 | 0.17 |

### 3.2 The growth fits

`sd ∝ n^γ` by weighted least squares in `ln sd = α + γ ln n`, weights `2(N − 1)` (the
inverse variance of `ln sd` for a normal sample), uncensored cells only
(`fit_growth`, `sparse_fits`):

| `c` | cells (`n`) | γ ± se | χ² free (dof) | χ² at γ = ½ | χ² at γ = 0 | ½ within 2 se | 0 within 2 se |
|---|---|---|---|---|---|---|---|
| 0.5 | 20, 30, 40, 50, 60, 70, 80, 90, 100, 120 | 0.19 ± 0.06 | 33.1 (7) | 60.2 | 43.8 | no | no |
| 1 | 20, 30, 40, 50, 60, 70, 80, 90, 100, 120 | -0.11 ± 0.06 | 11.5 (8) | 122.3 | 15.3 | no | yes |
| 1.5 | 20, 30, 40, 50, 60, 70, 80, 90, 100, 120 | 0.24 ± 0.06 | 2.4 (8) | 21.9 | 19.5 | no | no |
| 2 | 20, 30, 40, 50, 60, 70, 80, 90, 100, 120 | 0.38 ± 0.06 | 12.0 (8) | 15.9 | 55.6 | yes | no |
| 3 | 20, 30, 40, 50, 60, 70, 80 | 0.34 ± 0.07 | 6.4 (5) | 12.0 | 32.7 | no | no |
| 4 | 20, 30, 40, 50, 60, 70, 80 | 0.38 ± 0.07 | 2.5 (5) | 5.6 | 35.5 | yes | no |
| 6 | 20, 30, 40, 50, 60, 70 | 0.42 ± 0.07 | 3.1 (4) | 4.5 | 40.2 | yes | no |
| 8 | 20, 30, 40, 50, 60, 70 | 0.43 ± 0.07 | 2.6 (4) | 3.6 | 41.5 | yes | no |
| 10 | 20, 30, 40, 50, 60, 70 | 0.38 ± 0.07 | 2.5 (4) | 5.3 | 33.5 | yes | no |

At `c ≤ 1.5` the widths are 1–3 and the standard deviation is that of a two- or
three-valued variable, not a growth law. At `c ≥ 2` the bounded hypothesis fails
(`χ²` 33–56 against 2.5–12 for the free fit, which is itself acceptable at `c ≥ 3`), the
exponent is 0.34–0.43 with a standard error of 0.06–0.07, and `γ = ½` is within two
standard errors at `c = 2, 4, 6, 8, 10`. The cells span `n = 20` to `70–80`, a factor
3.5–4; an `n^{1/2 − o(1)}` law with a slowly varying correction changes `ln sd` over that
range by less than one standard error, so the record cannot distinguish it from `√n`.
The only statement the data support is: **growing, with an exponent between a third and a
half at these sizes, below the ceiling by a factor 2.2–3.2 (`sd / (√n/2) = 0.31–0.47` at
`c ≥ 3`)**. Whether the chromatic-number phenomenon of Heckel (2021) and Heckel & Riordan
(2023) — a standard deviation of order `n^{1/2 − o(1)}` for `G(n, ½)`, against the
`√n` martingale ceiling — has a pathwidth analogue at fixed `c` is not a question these
sizes can answer.

### 3.3 The middle regime (`np → ∞`, `p → 0`)

The other three families of the 2026-11-11 run (20 proved graphs per cell), for the record:

| cell | `n` | `c` | `N` | mean | sd (± se) | cv | min–max | top-2 mass |
|---|---|---|---|---|---|---|---|---|
| 2lnn | 30 | 6.80 | 20 | 11.65 | 1.27 (± 0.21) | 0.109 | 9–13 | 0.80 |
| 2lnn | 40 | 7.38 | 20 | 15.80 | 1.15 (± 0.19) | 0.073 | 14–18 | 0.65 |
| 2lnn | 50 | 7.82 | 20 | 20.20 | 1.40 (± 0.23) | 0.069 | 17–23 | 0.60 |
| 2lnn | 60 | 8.19 | 20 | 24.30 | 1.13 (± 0.18) | 0.046 | 22–26 | 0.60 |
| dense | 30 | 15.00 | 20 | 19.25 | 0.91 (± 0.15) | 0.047 | 16–20 | 0.95 |
| dense | 40 | 20.00 | 20 | 28.15 | 0.75 (± 0.12) | 0.026 | 26–29 | 0.90 |
| dense | 50 | 25.00 | 20 | 37.20 | 0.70 (± 0.11) | 0.019 | 36–38 | 0.85 |
| dense | 60 | 30.00 | 20 | 46.05 | 0.76 (± 0.12) | 0.016 | 45–47 | 0.75 |
| n07 | 30 | 10.81 | 20 | 16.00 | 0.79 (± 0.13) | 0.050 | 15–18 | 0.80 |
| n07 | 40 | 13.23 | 20 | 23.05 | 1.10 (± 0.18) | 0.048 | 21–25 | 0.60 |
| n07 | 50 | 15.46 | 20 | 30.55 | 1.00 (± 0.16) | 0.033 | 29–33 | 0.75 |
| n07 | 60 | 17.57 | 20 | 37.60 | 0.99 (± 0.16) | 0.026 | 36–40 | 0.75 |
| sqrtn | 30 | 5.48 | 20 | 9.85 | 0.88 (± 0.14) | 0.089 | 9–11 | 0.75 |
| sqrtn | 40 | 6.32 | 20 | 13.90 | 1.29 (± 0.21) | 0.093 | 11–16 | 0.60 |
| sqrtn | 50 | 7.07 | 20 | 18.55 | 1.67 (± 0.27) | 0.090 | 16–22 | 0.45 |
| sqrtn | 60 | 7.75 | 20 | 23.45 | 1.23 (± 0.20) | 0.053 | 22–26 | 0.60 |

### 3.4 The Bernoulli clique-cover cells (not `G(n, p)`)

`learning/data/ensemble/results.csv` (n = 10–40, 150 per cell) and `results_upward.csv`
(50–75, 50 per cell), generator `bernoulli`: `n` customers, `m` products, each entry
`Bernoulli(p)`; the MOSP graph is the random intersection graph of the rows and
`pw = optimum − 1`. 180 cells in all (`sparse_cells.csv`), one censored (`n = 75`,
`m = 150`, `p = 0.025`, two of 50 unproved). The square cells at three values of `p`:

| `n` | `m` | `p` | `N` | mean pw | sd (± se) | cv | min–max |
|---|---|---|---|---|---|---|---|
| 10 | 10 | 0.05 | 150 | 1.91 | 0.73 (± 0.04) | 0.383 | 1–5 |
| 10 | 10 | 0.1 | 150 | 2.25 | 0.70 (± 0.04) | 0.313 | 1–4 |
| 10 | 10 | 0.2 | 150 | 3.38 | 1.05 (± 0.06) | 0.310 | 1–6 |
| 15 | 15 | 0.05 | 150 | 2.33 | 0.81 (± 0.05) | 0.347 | 1–6 |
| 15 | 15 | 0.1 | 150 | 3.18 | 0.92 (± 0.05) | 0.289 | 1–6 |
| 15 | 15 | 0.2 | 150 | 6.46 | 1.22 (± 0.07) | 0.189 | 4–9 |
| 20 | 20 | 0.05 | 150 | 2.89 | 0.88 (± 0.05) | 0.303 | 1–5 |
| 20 | 20 | 0.1 | 150 | 4.69 | 1.19 (± 0.07) | 0.254 | 2–8 |
| 20 | 20 | 0.2 | 150 | 10.94 | 1.49 (± 0.09) | 0.136 | 6–15 |
| 25 | 25 | 0.05 | 150 | 3.21 | 0.77 (± 0.04) | 0.241 | 2–5 |
| 25 | 25 | 0.1 | 150 | 6.65 | 1.54 (± 0.09) | 0.232 | 4–11 |
| 25 | 25 | 0.2 | 150 | 15.74 | 1.41 (± 0.08) | 0.089 | 12–20 |
| 30 | 30 | 0.05 | 150 | 4.02 | 0.97 (± 0.06) | 0.240 | 2–6 |
| 30 | 30 | 0.1 | 150 | 10.26 | 1.68 (± 0.10) | 0.164 | 5–14 |
| 30 | 30 | 0.2 | 150 | 21.11 | 1.36 (± 0.08) | 0.064 | 17–24 |
| 35 | 35 | 0.05 | 150 | 5.04 | 1.34 (± 0.08) | 0.266 | 3–9 |
| 35 | 35 | 0.1 | 150 | 13.84 | 1.80 (± 0.10) | 0.130 | 8–19 |
| 35 | 35 | 0.2 | 150 | 26.55 | 1.31 (± 0.08) | 0.049 | 23–29 |
| 40 | 40 | 0.05 | 150 | 6.57 | 1.47 (± 0.09) | 0.223 | 3–11 |
| 40 | 40 | 0.1 | 150 | 18.51 | 1.96 (± 0.11) | 0.106 | 14–24 |
| 40 | 40 | 0.2 | 150 | 31.96 | 1.07 (± 0.06) | 0.034 | 28–34 |
| 50 | 50 | 0.05 | 50 | 10.98 | 1.96 (± 0.20) | 0.179 | 8–17 |
| 50 | 50 | 0.1 | 50 | 28.98 | 1.57 (± 0.16) | 0.054 | 26–32 |
| 50 | 50 | 0.2 | 50 | 43.16 | 0.98 (± 0.10) | 0.023 | 40–45 |
| 60 | 60 | 0.05 | 50 | 17.72 | 2.63 (± 0.27) | 0.149 | 11–24 |
| 60 | 60 | 0.1 | 50 | 38.26 | 1.93 (± 0.19) | 0.050 | 34–42 |
| 60 | 60 | 0.2 | 50 | 53.72 | 0.81 (± 0.08) | 0.015 | 52–55 |
| 75 | 75 | 0.05 | 50 | 29.14 | 2.11 (± 0.21) | 0.072 | 25–36 |
| 75 | 75 | 0.1 | 50 | 55.42 | 1.30 (± 0.13) | 0.023 | 53–58 |
| 75 | 75 | 0.2 | 50 | 69.82 | 0.66 (± 0.07) | 0.009 | 68–71 |

At fixed `p` the expected degree `(n − 1)(1 − (1 − p²)^m)` grows with `n`, so these are
not fixed-degree families: at `p = 0.2` the graph fills (`pw ≈ 0.93 n` at `n = 75`) and
the standard deviation *falls* (0.66 at 75), while at `p = 0.05` it still grows (2.1–2.6
at 60–75). The fits `cover_fits.csv` are written for completeness and mean nothing about
`√n`; the relevant family would hold `p √m` fixed, which no campaign on record did.

## 4. Lean

`lean/MOSPFormalization/Concentration.lean`, imported by the root `MOSPFormalization.lean`;
`lake build MOSPFormalization.Concentration` passes (taskset 4 cores, nice 19, 0.9 s for
the file after its imports); `#print axioms` on every declaration
(`reports/scratch/pathwidth_concentration/axiom_check.lean`, log `axiom_check.log`):
**18 declarations, each on `[propext, Classical.choice, Quot.sound]`, no `sorry`, no
`axiom`.**

| declaration | statement |
|---|---|
| `AgreeOff G G' v` | every edge of `G` avoiding `v` is an edge of `G'` (`AgreeOff.of_iff`, `AgreeOff.symm_of_iff` from the iff form) |
| `PathDecomposition.insertVertex` | `v` inserted into every bag of a decomposition of `G'`, a decomposition of `G` |
| `PathDecomposition.insertVertex_width_le` | its width is at most the width plus one |
| `pathwidth_le_add_one_of_agreeOff` | `pathwidth G ≤ pathwidth G' + 1` |
| `pathwidth_lipschitz_vertex` | **the Lipschitz lemma**, both inequalities |
| `abs_pathwidth_sub_le_one` | the same as `|pw G − pw G'| ≤ 1` in `ℤ` |
| `pathwidth_le_deleteIncidenceSet_add_one`, `pathwidth_deleteIncidenceSet_le` | the edges at `v` removed: down by at most one, never up |
| `PathDecomposition.ofInduceCompl`, `ofInduceCompl_width_le` | bags of `G − v` lifted and `v` inserted |
| `pathwidth_le_induce_compl_add_one`, `pathwidth_induce_compl_sandwich` | **vertex deletion** lowers the pathwidth by at most one (with `pathwidth_induce_le`) |
| `gnpMean`, `pathwidthMean`, `pathwidthVar` | the `G(n, p)` mean and variance of the pathwidth on `Fin n` as `gnpWeight` sums |
| `PathwidthVarianceBound` | `Prop`: `Var ≤ n/4` (Efron–Stein), **stated, not proved** |
| `PathwidthConcentration` | `Prop`: `P(|pw − E pw| ≥ t) ≤ 2 exp(−2t²/n)` (McDiarmid), **stated, not proved** |

The Lean proof of the lemma is the construction of §1.1 verbatim; nothing in the file
depends on the brute force, and the brute force was run before the file was written.

## 5. Literature

Held, read for this item: Gao (2012, `literature/2012-Gao-Treewidth-…`; Lemma 3.3 is
McDiarmid's inequality quoted from McDiarmid 1989 Lemma 1.2 and Bollobás's *Random
Graphs* Theorem 1.19, applied to the treewidth of `G(n, m)` through a weighted
tree-component count; §1.1 says they "are not aware of any other application of the
Hoeffding–Azuma inequality" with weighted counts); Do, Erde & Kang (2024,
`literature/2024-Do-Erde-Kang-…`, concluding remarks: rank- and tree-width are vertex-Lipschitz,
hence concentrated by Azuma–Hoeffding, with Frieze & Karoński as the reference; they ask
whether the concentration is within `o(ε³ n)` for small `ε`); Frieze & Karoński's
Theorem 7.3 and its proof (read verbatim through the free PDF on 2026-11-11,
`literature/MISSING.md`, "Dense random graphs: the staircase constant"). Not held, cited
from the record and the standard references: McDiarmid (1989), Shamir & Spencer (1987),
Efron & Stein (1981), Steele (1986), Boucheron, Lugosi & Massart (2013), Matula (1972,
1976), Bollobás & Erdős (1976), Grimmett & McDiarmid (1975), Alon & Krivelevich (1997),
Heckel (2021), Heckel & Riordan (2023), Kuang & McDiarmid (1985). All recorded in
`literature/MISSING.md` under "Concentration of the pathwidth of a random graph
(2026-11-12)". We found no prior statement of the concentration of the *pathwidth* of
`G(n, p)`, of its standard deviation, or of a two-point law for `n − pw` at fixed `p`;
the treewidth statements above are the nearest, and the Lipschitz observation is theirs
as much as ours.

## 6. Regenerate

| number | where | command |
|---|---|---|
| 1,252 graphs, 500,793 pairs, 0 violations, 41.9% differ by one; 8,475 deletions, 0 violations, 49.5% drop; 0 oracle disagreements; 88.6 s | §0, §1.2 | `nice -n 19 python3 -m learning.pathwidth_concentration lipschitz` → `reports/scratch/pathwidth_concentration/lipschitz.log` |
| Lean build; 18 declarations on the three axioms | §4 | `cd lean && nice -n 19 taskset -c 0-3 lake build MOSPFormalization.Concentration`; `lake env lean ../reports/scratch/pathwidth_concentration/axiom_check.lean` → `axiom_check.log` |
| the dense table (sd, two-value mass, `s_block`, `s*`, the drop per step) | §2.1 | `python3 -m learning.pathwidth_concentration dense` → `dense_cells.csv` |
| the identity `R = Σ_τ`, the loss lemma, `Ψ` against enumeration, the rates, the window table, the family brackets | §2.3–§2.6 | `python3 -m learning.pathwidth_concentration overlap` → `overlap.log`; `python3 -m pytest tests/test_pathwidth_concentration.py -q` (33 tests) |
| the pilot, middle and cover tables; the fits | §3 | `python3 -m learning.pathwidth_concentration sparse` → `sparse_cells.csv`, `sparse_fits.csv`, `cover_fits.csv` |
| the markdown tables of this report | §2.1, §3 | the inline script of the session (`dense_cells`, `pilot_cells`, `middle_cells`, `ensemble_cells`, `sparse_fits`, `window_estimate`) |

Compute: under 0.1 core-hours in all (the brute force 89 s, the overlap analysis about
two minutes, the Lean build under a minute after its imports). `solutions/` untouched;
no graph solved.

## 7. Proposed text, not applied

### 7.1 Appendix E (`paper1/latex/sec9e_appendix_random.tex`), a paragraph after *The dense regime*

```latex
\paragraph{How concentrated.}
Everything above is about the location of $\mathrm{pw}(G(n,p))$; its spread
has a ceiling that costs one line. Pathwidth is $1$-Lipschitz under vertex
exposure: two graphs on the same vertices that agree on every pair avoiding
$v$ have pathwidths within one of each other, since $v$ can be put into every
bag of a decomposition of either~\leanref{concentration}. Exposing the
vertices one at a time therefore gives $n$ independent coordinates with
difference bound $1$, and the bounded-differences inequality of
\citet{McDiarmid1989}, the argument \citet{ShamirSpencer1987} used for the
chromatic number, gives for every $p$
\[
  \Pr\bigl[\,|\mathrm{pw}-\mathbb E\,\mathrm{pw}|\ge t\,\bigr]\le 2e^{-2t^{2}/n},
  \qquad \mathrm{Var}(\mathrm{pw})\le n/4 ,
\]
a standard deviation at most $\sqrt n/2$; the same observation is made for
treewidth by \citet{Gao2012} and \citet{DoErdeKang2024}. The ceiling is far
from tight. At $p=\tfrac12$, where Theorem~\ref{thm:dense} puts $n-\mathrm{pw}$
within $o(\log n)$ of $(2+\sqrt2)\log_{2}n$, the proved widths at
$n=30,40,50,60$ have standard deviations $0.91$, $0.75$, $0.70$, $0.76$
against ceilings $2.7$ to $3.9$, with $75$ to $95$ per cent of each cell on
two values. The clique number of $G(n,p)$ is concentrated on two values
\citep{Matula1976,BollobasErdos1976}, and the block first moment behind
Theorem~\ref{thm:dense} drops by $n^{-(\sqrt2+o(1))}$ per unit of $s$ as the
clique count does, so the upper tail of $n-\mathrm{pw}$ is sharp to one step;
but the second moment on staircases is not, and cannot be made so: a
staircase, unlike a clique, has $e^{\Theta(\log n)}$ cheap deformations
(permutations of its sloped part of small depth), each a distinct forced set
of nearly the same cost, and the sum over them exceeds one step of the first
moment for $p\le\tfrac12$. Whether $n-\mathrm{pw}$ is two-point concentrated is
open; what the second moment can give is a window of a bounded number of
values. At fixed $c$ the standard deviation of $\mathrm{pw}(G(n,c/n))$ on the
proved cells of Figure~\ref{fig:gnp} grows like $n^{\gamma}$ with
$\gamma=0.34$ to $0.43\pm0.07$ at $c=3$ to $10$ and $n\le80$: a bounded
spread is excluded, and $\sqrt n$ is not distinguishable from
$n^{1/2-o(1)}$ at these sizes.
```

(New references: `McDiarmid1989`, `ShamirSpencer1987`, `Gao2012`, `DoErdeKang2024`,
`Matula1976`, `BollobasErdos1976` — the last two may already be in `refs.bib` from the
dense-regime paragraph; check before adding. `fig:gnp` stands for the sparse-regime
figure's label, to be replaced by the actual one.)

### 7.2 Appendix A (`paper1/latex/sec9a_appendix_lean.tex`), one row after `staircase`

```latex
\leanentry{concentration}{The Lipschitz lemma of the paragraph \emph{How concentrated} of Appendix~\ref{app:random}: two graphs that agree on every pair avoiding $v$ have pathwidths within one (insert $v$ into every bag), hence removing the edges at a vertex, or the vertex itself, lowers the pathwidth by at most one and never raises it; the $G(n,p)$ mean and variance of the pathwidth as finite weighted sums; McDiarmid's inequality and the variance bound $n/4$ are stated propositions, not theorems} \leannames{AgreeOff, PathDecomposition.insertVertex, insertVertex_width_le, pathwidth_le_add_one_of_agreeOff, pathwidth_lipschitz_vertex, abs_pathwidth_sub_le_one, pathwidth_le_deleteIncidenceSet_add_one, pathwidth_deleteIncidenceSet_le, PathDecomposition.ofInduceCompl, pathwidth_le_induce_compl_add_one, pathwidth_induce_compl_sandwich, pathwidthMean, pathwidthVar, PathwidthVarianceBound, PathwidthConcentration} \\
```

### 7.3 The per-cell table for Appendix E

The brief asks for the sparse per-cell standard deviations "beside the means" in
Appendix E; the table of §3.1 restricted to `c ∈ {3, 4, 6, 8, 10}` and `n ≤ 60` (the
137-graph cells) is the candidate, nine columns of §3.1 reduced to `n`, `c`, mean,
`sd ± se`, `sd / (√n/2)`. Not applied.
