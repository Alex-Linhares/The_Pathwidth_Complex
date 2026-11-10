# Four layout-LP and spectral papers, read whole: what they bring beyond what is tried

*2026-11-10, one session. The four papers named in the brief were read whole
from `pdftotext -layout` dumps; Mallach (2018) was skimmed for its LP-bound
statements. No solver was run. The one computation made is eigenvalues
(`learning.spectral_bound`, seconds per graph) on open instances of the
pathwidth dataset, §8; its script and log are under
`reports/scratch/layout_lp_literature/`. Page numbers are the printed ones:
Caprara et al. pp. 26–40 (PDF page k is p. 25 + k); Coudert's HAL report
pp. 1–33 (PDF page k is report page k − 1); Helmberg et al. pp. 1–19 (PDF =
printed); Gu & Liu pp. 1–8 (PDF = printed); Mallach pp. 156–167 (PDF page k
is p. 155 + k). "The three reports" are `reports/chain_lp.md`,
`reports/spectral_bound.md` and `reports/checkpoint_relaxation.md`.*

## 0. What we can use, ranked

The honest headline: **none of the four papers brings an inequality,
construction or separation routine that could move a floor on the residual
dense MOSP instances or on the 24 open dataset classes beyond what the three
reports have already tried and killed.** Every bound in them is either a
single-separator statement (under Harper by `spectral_bound.md` §1(i)), a
bound on a sum objective (MinLA, 1-sum, bandwidth) that reaches vertex
separation only through a division by `Δ (n − 1)` or not at all, or an
ILP formulation whose LP relaxation the project has already proved to be
zero or Harper. What the reading did yield, in order of value:

1. **One floor movement, found by pointing an old bound where its
   hypothesis holds — measured here, not an idea from the papers (§8).**
   The Mohar–Poljak separator inequality that Helmberg et al. quote as their
   eq. (21) (p. 11) — Theorem 1 of `spectral_bound.md`, already implemented
   and verdict "dead" on MOSP graphs — was never evaluated on the open
   *named* graphs of the pathwidth dataset, which are regular and
   vertex-transitive: exactly where `μ₂/Δ` is large and the bound is at its
   best. On the nine smallest open named graphs (widths 19–41) it is **above
   the best floor on record on three**: `OddGraph_5` (126 vertices, width 41,
   record floor 31, spectral **36**), `NStarGraph_5` (120, width 28, floor
   23, spectral **24**), `Tutte12Cage` (126, width 26, floor 19, spectral
   **20**); below it by 2–6 on the other six. None closes. The eigenvalues
   are known in closed form (Kneser `K(9,4)`: `μ₂ = 2`, `μₙ = 9`; the star
   graph `S₅`: `μ₂ = 1`, bipartite 4-regular so `μₙ = 8`; the Tutte 12-cage:
   `μ₂ = 3 − √6`, `μₙ = 6`) and the hand computation is three lines (§8), so
   the three floors are certain. The same pass over **all 312 open classes**
   of loop0013's pass 1 (§8.2, 206 s) finds the spectral floor above the
   record on **9**, equal on none, below on 303; the other six are large and
   dense or regular, and there the gains are not marginal: the Cameron
   graph `srg(231, 30, 9, 3)` from 88 to **147** (width 161) — by
   Helmberg's own inequality (20), not Mohar–Poljak's — `le450_5a` and
   `le450_5b` from 63 to **110** (widths 245, 261), `he048` from 34 to
   **61** (width 122), `HyperStarGraph_10_5` from 18 to **42** (width 62),
   `Cell120` from 17 to **22** (width 67). Still nothing closes, and every
   one of these values is the Gima treewidth bound in disguise
   (`spectral_bound.md` §1(ii)), so the spectral verdict on the *MOSP*
   residual stands unchanged. **Proposed, not applied**: an evidence row of
   a new provenance kind (`bound:spectral`, the value reproducible from the
   edge list by `learning.spectral_bound.spectral_graph_bound`) for the nine
   classes — a dataset rebuild, which the loops forbid without the owner
   (`reports/obstruction_search.md` §7); and the `peel` and `minor` families
   on the 175 open classes above 200 vertices, where only the whole graph
   was evaluated (minutes; kill: no further class moves). Since
   `spectral ≤ Harper` (§1(i) there), Harper's exact value on `OddGraph_5` is
   at least 36 and unknown; the SAT route that settles Harper levels
   "settles almost none at 75 and beyond", so no experiment is proposed on
   it.
2. **Three citations the reports should carry, one of them a correction
   (§6).** (i) Mallach's Theorem 4.1 (p. 159) is the exact prior statement of
   `chain_lp.md` §2's "the bare LP is 0": his `MIP_S` *is* the chain IP
   (constraints (8)–(10) are nesting, size and the edge inequality) and his
   witness `b*_{v,p} = p/n` is the uniform point. `chain_lp.md` attributes
   the fact to "the position-based" MIPs and says the paper is not held;
   it is held (`literature/MISSING.md` line 58, since 2026-09-28) and the
   statement covers both models. The Harper-cut identity and the ceiling
   theorem of `chain_lp.md` §5 remain unstated in Mallach. (ii) The
   nested-chain encoding of `checkpoint_relaxation.md` is, as an ILP,
   Solano & Pióro (2010), Coudert's Formulation 2 with Formulation 4
   (`PW2`, 2016, pp. 3–7) and Mallach's `MIP_S`; Coudert's Table 4 (p. 13)
   — `PW2` solves 84 of 84 Small graphs in 1.7 s average where the
   position model `PW1` solves 78 in 56 s — is the ILP precedent of
   `checkpoint_relaxation.md` §8's chain-versus-position comparison. "What
   is new" there is the SAT form and the measurement, not the formulation.
   (iii) Caprara, Letchford & Salazar-González (2011) is the reference for
   *why* LP bounds work on a sum objective and cannot on a bottleneck one
   (§1.4): their own remark on p. 28 is the converse.
3. **One cheap measurement that would close a question the reports leave
   open, expected dead.** Mallach's linear-ordering relaxation `LP_L` is the
   only LP in the literature on exactly our problem whose value is not
   provably 0 or Harper. Run it (his (12)–(15) with (16)–(17), 3-dicycle
   rows separated lazily as on p. 161; `O(n²)` variables; his times at
   48–64 vertices are 2–37 s, p. 163) on the 64 gap instances of
   `chain_lp.md` §4 and compare with the record's exact Harper value.
   **Kill criterion: dead if `⌈LP_L⌉ ≤ Harper` on all 64.** Expected dead:
   on the complete graph `LP_L = (n − 1)/2` (Theorem 5.5, p. 162) against
   Harper `n − 1`; on the `n × n` grid `LP_L = 2` (Table 3, p. 164) against
   pathwidth `n`; and his cuts are indexed by vertex, not position (p. 157),
   so the ceiling argument of `chain_lp.md` §5 transported to his space gives
   at most `max_ν min_σ Σ_v ν(v) |S(σ, v)|`, which on `K_n` is `(n − 1)/2`
   (§5.2): his LP is already at its ceiling there, and that ceiling is half
   the vertex separation. About one core-hour.
4. **Not worth doing, with the reason.** Caprara-style rank and projected
   inequalities for vertex separation (§1.4: the max objective makes them
   minor monotonicity, which the obstruction search exhausted); the
   profile/1-sum route to vertex separation (§3.3: `vs ≥ MinLA/(Δ(n − 1))`,
   below 3 on `Random-125-125-4-1_0` even at the exact MinLA);
   Helmberg's Theorem 9 / Theorem 19 QAP bounds (§3.3: bandwidth and 1-sum
   are not pathwidth floors); maximising the separator bound (20) over edge
   weights (§3.4: still one separator, so under Harper, so under the record
   everywhere but on the regular graphs of item 1, where symmetry makes the
   uniform weights optimal); Gu & Liu's lemma as a separate inequality (§4:
   it is a consequence of Haemers' inequality, which is Helmberg's (20)
   rearranged, so Theorem 3 of `spectral_bound.md` is implied by its
   Theorem 2 — consistent with the measured "adds almost nothing").

**Contradictions with the three reports** are collected in §6: two in
`chain_lp.md` (Mallach's statement covers the chain model itself; the paper
is held), one qualification in `checkpoint_relaxation.md` ("new"), two small
ones in `spectral_bound.md` (the "diagonal-correction" attribution; Theorem 3
is not independent of Theorem 2), and one in `literature/MISSING.md`
(Mallach marked "Not held" in the 2026-11-10 LP section while line 58 has
it held). None changes a verdict.

---

## 1. Caprara, Letchford & Salazar-González (2011), *Decorous lower bounds for minimum linear arrangement*, IJOC 23(1), 26–40

### 1.1 What it proves and builds

MinLA asks for a layout minimising `Σ_{ij ∈ E} |π(i) − π(j)|` (p. 26). The
paper computes lower bounds by a cutting-plane LP in **m distance variables
`d_e`, one per edge**, with exponentially many *rank inequalities*
`Σ_{e ∈ E(G')} d_e ≥ la(G')` for subgraphs `G'` whose MinLA value is known
in closed form or computable (p. 28, §2.1), strengthened by **projecting
inequalities valid for the complete graph `K_n` onto the edge space of `G`
through paths** (p. 29, §2.3; p. 33, Proposition 12). The position-based
ILP (variables `x_ij`, vertex `i` at position `j`) is dismissed on p. 28
because its LP relaxation "admits the trivial solution `x_ij = 1/n` … and
`d_ij = 0`, yielding a lower bound of zero" — the same uniform point that
kills our chain LP. The main results: the sparse LP (1) over subgraphs of
`G` is weak (Example 1, p. 29: star inequalities give 7 on a 7-vertex graph
with `la = 8`); the dense LP (2) over all `C(n, 2)` pairs with triangle
inequalities (3) is tight but "a few orders of magnitude slower" (p. 38);
the projected LP (6) has exactly the dense LP's value (Proposition 1 and
Corollary 1, p. 30) with `m` variables, and is the one that works. Table 2
(p. 27) and Table 4 (p. 38) give the gaps.

### 1.2 The decorous inequalities, exactly

All are valid for the dominant `D(G)` of the distance polytope (p. 30), so
they lift from any subgraph to `G` (Proposition 4, p. 31):

- **star** (7), p. 31: for `i ∈ V`, `S ⊆ N(i)`: `Σ_{j ∈ S} d_ij ≥ ⌊(|S| + 1)²/4⌋`;
  facet-inducing iff `|S| ≠ 2`. Separation in `O(m log n)` by sorting the
  `d*_ij` (Proposition 13, p. 34).
- **clique** (8), p. 31: for a clique `S`: `Σ_{{i,j} ⊆ S} d_ij ≥ C(|S| + 1, 3)`;
  facet-inducing. Separation strongly NP-complete (Proposition 15, p. 34).
- **circuit** (9), p. 32: for a cycle `C`: `Σ_{e ∈ C} d_e ≥ 2|C| − 2`;
  facet-inducing; separation strongly NP-complete (Proposition 16, p. 34).
- **bipartite** (10), p. 32: for `S`, `T` completely joined, `p = |S| ≤ q = |T|`:
  `Σ_{i ∈ S, k ∈ T} d_ik ≥ r(p, q)` with `r(p, q) = ⌊p(3q² + 6pq − p² + 4)/12⌋`
  (`p + q` even) or `⌊p(3q² + 6pq − p² + 1)/12⌋` (odd), from Juvan & Mohar
  (1992); facet-inducing iff `p = 1, q = 2`, or `p = 2` and `q` even, or
  `p ≥ 3`. Separation conjectured strongly NP-complete (Conjecture 1, p. 34).
- **double star** (13), p. 33: `i, j` both joined to all of `T`, `|T| = t`
  odd `≥ 3`: `Σ_{k ∈ T} (2 d_ik + d_jk) ≥ (3t² + 4t − 1)/4`; facet-inducing;
  the only non-rank family. Separation `O(nm log n)` (Proposition 14, p. 34).
- **tree** (14), p. 33: `Σ_{e ∈ F} d_e ≥ la(T)` for a tree `T` (Shiloach's
  algorithm for the right-hand side).
- **projected** (16), p. 33, Proposition 12: from any valid
  `Σ_{ij ∈ F} α_ij d_ij ≥ β` for `D(K_n)` and any choice of paths `P_ij` in
  `G`, the inequality `Σ_ij α_ij Σ_{e ∈ P_ij} d_e ≥ β` is valid for `D(G)`
  (an edge may receive coefficient above one). Separation of the projected
  family reduces to separation over `K_n` with all-pairs shortest paths
  under `d*` (Proposition 17, p. 34); projected stars in `O(n² log n)`
  (Corollary 1, p. 34). The projected version of a facet need not even be
  face-inducing (Example 1 continued, p. 35: right-hand side 12 where 13 is
  the maximum); Proposition 18 (p. 35) gives the dominating subclass (paths
  forming a tree rooted at the centre) and Proposition 19 (p. 36) a
  sufficient condition for the right-hand side to be maximal, "almost
  always satisfied in practice".

### 1.3 The gap they achieve

Before the paper, "the best lower bounds on the optimum are generally one
order of magnitude smaller than the heuristic values" (p. 27; Table 1 gaps
42.3–94.6% on the Petit instances). With the projected LP and stars only
(Table 3, p. 38, one CPU-day limit, CPLEX 11.2, p. 36): c1y 3.7%, c2y 3.2%,
c3y 7.6%, c4y 7.0%, c5y 8.4%, gd95c 16.2%, gd96a 25.8% (18.3% with path
inequalities), gd96b 10.9%, gd96c 27.6%, gd96d 17.8%, bintree10 23.0%,
mesh33×33 37.8% (the last two with known optima and unconverged LPs). With
all families (Table 4, p. 38): the gd* instances improve to 12.5%, 18.3%,
9.5%, 22.5%, 15.5% at a cost of "a couple of orders of magnitude" in time,
bintree10 is closed by the tree inequalities, the c*y instances do not move
— the other families "give limited improvements" on MinLA instances (p. 38).
On the 44 bandwidth graphs of Caprara & Salazar-González (2005) (Table 5,
p. 39): gaps 0% (dwt_66, solved to optimality) to about 35%, "for about a
third of the instances, the gap is less than 10%", and there the extra
families help "significantly". Their final paragraph (p. 40) lists the two
limits: the time (nothing significant above 5,000 edges in a day) and that
even with integrality the model "would not be a valid formulation of MinLA"
(integer `d` need not come from a layout; recognition conjectured
NP-complete).

### 1.4 The vertex-separation analogue: what changes, precisely

The brief asks whether an analogue exists. Three things change, and each
one removes the mechanism that makes their bound strong.

1. **The objective.** MinLA is a *sum* of edge lengths, so rank inequalities
   on disjoint substructures *add*: a layout long on one star is still long
   on another. Vertex separation is a *maximum* over prefixes of a vertex
   count. The only rank-type fact is `vs(G) ≥ vs(G')` for a subgraph or
   minor `G'`, and such facts never add — the LP value over any family of
   them is their maximum. In the chain variables this is exactly the
   ceiling theorem of `chain_lp.md` §5: the LP's only coupling is a mixture
   of levels, `L = max_μ min_σ Σ_t μ(t) B_σ(t)`, and nothing in the paper's
   machinery escapes it. The paper itself says the converse on p. 28: the
   bandwidth methods "are heavily based on the fact that the objective
   function is of bottleneck type and, apparently, cannot be used in the
   MinLA context".
2. **The variable.** `d_e` is a *distance* with the metric property
   `d_ij ≤ Σ_{e ∈ P_ij} d_e`, which is what lets an inequality for `K_n` be
   projected along paths (Proposition 12). The vertex-separation quantity
   is a 0/1 event per (vertex, level): `v` is outside `S_t` and has a
   neighbour inside. It has no metric and does not propagate along paths —
   `w` outside `S_t` with neighbour `v` outside `S_t` says nothing. The
   nearest analogue of projection is minor monotonicity: a `K_s` whose
   edges are realised by disjoint paths is a topological minor and gives
   `vs ≥ s − 1`, a Hadwiger-type bound and so a treewidth bound (under the
   ceiling of `reports/ml_nature.md` §24); the general form, `vs(G) ≥ vs(H)`
   for a contraction minor `H`, is what `reports/obstruction_search.md`
   searched (tight on 327 of 338 gap instances) and what is one to four
   short on the 11 residual dense ones.
3. **The counting unit.** The star inequality counts that `q` neighbours of
   a centre occupy distinct positions, so their distances are at least
   `1, 1, 2, 2, …`, summing to `⌊(q + 1)²/4⌋`. The vertex-boundary version of
   "a vertex with `q` neighbours" at one level is `Φ(1) ≥ deg`, the trivial
   bound. The only sum-type relative of vertex separation is the profile /
   SumCut `Σ_t |N(V_t)|` (Coudert, p. 3, Table 1, `sc = pr`), for which
   genuine rank inequalities exist (the profile of `K_{1,q}` is about
   `q²/8 + q/2`); but a profile floor `P` gives only `vs ≥ P/(n − 1)`, the
   *average* boundary, which is `L` at the uniform `μ` — dominated by the
   `L` that `chain_lp.md` §5 already computes, whose optimal `μ*` is
   supported on two adjacent levels, not uniform.

So: **no analogue that is not already the Lagrangian ceiling or the minor
search.** What the paper would contribute to a write-up is the clean
statement of why.

### 1.5 The brief's four questions

(a) Counting inequalities coupling several positions: yes, all of §1.2
couple all positions of a substructure — but over *distances*, which
vertex separation lacks (§1.4). (b) Inequalities for vertex separation or
bandwidth not implied by single-prefix facts: none; the paper is MinLA
only, with bandwidth mentioned as the problem where the authors' earlier
method lives (p. 28). (c) Separation routines applicable to our encodings:
the star separation by sorting (Proposition 13) and the path projection
(Proposition 17) need distance variables; nothing transfers to `(y, s)` or
to the position encoding. (d) Spectral bounds: none in the paper.

---

## 2. Coudert (2016), *A note on ILP formulations for linear ordering problems on graphs*, Inria RR hal-01271838, 33 pp.

### 2.1 What it builds

A modelling note. Three ways to write a linear ordering in an ILP (pp. 3–5):
Formulation 1, position assignment `a^i_u` (`n²` variables, `2n`
constraints); **Formulation 2, prefix membership `x^i_u = 1` iff
`π(u) ≤ i`**, with `x^i_u ≤ x^{i+1}_u` (2a) and `Σ_u x^i_u = i` (2b) (`n²`
variables, `n²` constraints, p. 4); Formulation 3, pairwise order
`α_{u,v}` with transitivity (`O(n³)` constraints, p. 4). Formulation 2 had
been used only by Solano & Pióro for lightpath reconfiguration, "equivalent
to the Vertex Separation problem in directed graphs, and so to the
Pathwidth problem" (p. 4, lines 100–104), in an `O(n³)` variant. Pathwidth
is Formulation 4 (pp. 6–7): `y^i_u ≥ x^i_v − x^i_u` for `v ∈ N(u)` (4a),
`Σ_u y^i_u ≤ p` (4b) — **our chain IP verbatim** (`y[v,t]`, `s[v,t]`,
`chain_lp.md` §1). Table 3 (p. 6): `PW2` has `O(n²)` variables and `O(nm)`
constraints against `O(n² m)` for Duarte et al. and `O(nm)` for Biedl et
al.'s interval model. The same prefix variables give cutwidth (Formulations
6–8, pp. 8–9, including an incremental edge-cut form), bandwidth (p. 9),
SumCut/profile (p. 10) and MinLA (pp. 11–12).

### 2.2 What it measures

SageMath + CPLEX, one thread, 300 s per instance (p. 12). On the 84 Small
graphs (16–24 vertices, p. 12), Table 4 (p. 13): `PW2` solves 84 of 84 with
0.0% average gap in 1.7 s average; `PW1` 78 at 2.3% in 56 s; Solano–Pióro's
variant 83 at 0.3% in 33.6 s; Biedl et al. 17; Duarte et al. 1; the
pairwise `PW3` 1. On the 11,534 Rome graphs (Table 9, p. 14): `PW2` solves
5,615 (48.7%), the largest solved at `n + m = 142`; "almost all graphs such
that `n + m < 90`, but very few with `n + m > 120`" (p. 15). The project's C
program proves all 11,534 (`CLAUDE.md`, the pathwidth-solver entry), which
is the comparison a related-work section would make. The conclusion names
"cutset inequalities" as a way to improve the formulations (p. 15, line
438) and gives none.

### 2.3 The brief's four questions

(a)–(b) No inequality beyond the formulation's own rows; the LP relaxation
of `PW2` is zero (Mallach's Theorem 4.1 applies to it, §5). (c) No cutting
plane, no separation routine; the relations between the three variable
sets (p. 5, lines 120–133) are big-M links and fractionally weak. (d) No
spectral content. **Nothing beyond citation**: the ILP precedent of the
nested-chain encoding (§6, item 3), and its Rome numbers as a comparison.

---

## 3. Helmberg, Mohar, Poljak & Rendl (1995), *A spectral approach to bandwidth and separator problems in graphs*, Linear and Multilinear Algebra 39, 73–90 (preprint pagination 1–19)

### 3.1 What it proves

The tool is **Theorem 1 (p. 2)**: for a partition `(S₁, S₂, S₃)` of
`V(G)` with `|S_i| = m_i`,
`cut(S₁, S₂) ≥ f(m₁, m₂) := (√(m₁m₂)/2n)[(√(m₁m₂) + √((n−m₁)(n−m₂))) λ₂ + (√(m₁m₂) − √((n−m₁)(n−m₂))) λₙ]`,
proved (pp. 3–6) by Rendl–Wolkowicz's parametrisation of partition
matrices, a Hoffman–Wielandt variant (Theorem 5, p. 4) and the
Hadley–Rendl–Wolkowicz QAP projection bound (Theorem 6, p. 5), after a
diagonal shift `D` (eq. (9), p. 3) that leaves `cut` unchanged. From it:
**Theorem 8 (p. 7)**, bandwidth `σ∞(G) ≥ α` or `α + 1` with `α` the largest
integer below `nλ₂/λₙ`, via (18) `σ∞ ≥ n − m₁ − m₂ + 1` whenever
`cut(S₁, S₂) > 0` for all `(m₁, m₂)`-pairs; **Theorem 9 (p. 8)**, the
QAP-projection test: if some symmetric `B` with `b_ij = 0` for `|i − j| ≤ k`
has `Σ_i λ_{i+1}(L) λ_i(VᵗBV) < 0`, then `σ∞ > k` — a convex program in `B`
solvable by the ellipsoid method (§7.1, p. 16), containing Theorem 8; it
proves bandwidth 5 for the Petersen graph where Theorem 8 gives 3 (§7.2,
p. 16); **Theorem 11 (p. 9), eq. (20)**: a separator `S₃` between `S₁` and
`S₂` has `|S₃| ≥ 4λₙλ₂|S₁||S₂| / (n(λₙ − λ₂)²)`, tight on
`(G₁ ∪ G₂) ∗ G₃` with `m₁ = m₂` (p. 10); Corollary 12 (p. 10) its balanced
form; eq. (21) (p. 11), the Mohar–Poljak bound
`|S₃| ≥ 4λ₂|S₁||S₂| / (Δn − λ₂|S₁ ∪ S₂|)`, with (22) the exact condition
under which (20) beats it and Theorem 14 (p. 11) that (20) wins almost
surely in `G(n, p)` at fixed `p`; **Theorem 19 (p. 14)** on the 1-sum
(MinLA): `σ₁(G) ≥ −½ Σ_i λ_{i+1}(L) λ_i(VᵗBV)` with `b_ij = |i − j|`,
strictly better than Juvan–Mohar's `λ₂(n² − 1)/6` on every graph that is
neither empty nor complete (Table 2, p. 15: 2–23% on random graphs). §5
(subgraph isomorphism) and Proposition 10 (an upper bound on bandwidth) do
not concern us.

### 3.2 What the spectral report already took, and took correctly

`spectral_bound.md` Theorem 2 is eq. (20) (Theorem 11 at `cut = 0`), its
Theorem 1 is eq. (21) with the top-`c` degree sum in place of `Δc`, and its
§4 says Theorem 8 is a bandwidth bound and was not used — all as the paper
states. One attribution is off (§6, item 5): the "diagonal-correction
`max_u μ₂(L + diag u)`" that the report lists under "not done" is not this
paper's nonlinear improvement; the paper's is the optimisation over `B`
(and over edge weights, which Theorem 9 allows, p. 8) for the *bandwidth*
bound, §7.1; its only diagonal shift is the fixed `D` of eq. (9).

### 3.3 The brief's question (d): is there a spectral bound that is not one separator?

Yes, two: Theorems 9 and 19 are QAP-projection bounds that couple every
pair of positions at once through the whole spectrum and an optimised
matrix `B`, so the §1(i) argument of `spectral_bound.md` does not apply to
them. But they bound **bandwidth** and the **1-sum**, and neither reaches
pathwidth: `pw ≤ bw` (a bandwidth floor is above, not below, the
pathwidth), and the 1-sum reaches vertex separation only through the
profile — each edge `uv` with `π(u) < π(v)` has length at most
`π(v) − min_{w ∈ N[v]} π(w)`, so `MinLA ≤ Δ · profile`, and
`profile = Σ_t |N(V_t)| ≤ (n − 1) vs` (Coudert p. 3), hence
`vs ≥ MinLA/(Δ(n − 1))`. On `Random-125-125-4-1_0` (125 customers, 1,063
edges, optimum 57, i.e. `vs = 56`; `Δ ≥ 2m/n = 17`) that is at most
`MinLA/2108`; a random layout has MinLA about `m · n/3 ≈ 44,000`, the
optimum is below it, so even the *exact* MinLA would certify at most about
21 and any LP floor on it far less. The route is dead by arithmetic, as
`spectral_bound.md` §4 had already found for the Juvan–Mohar form (the
cutwidth route, "weaker by a factor of about 6"). A QAP form of vertex
separation itself does not exist: `vs ≤ k` forbids no pair of positions
from carrying an edge (that is bandwidth), and the prefix-boundary count is
not a quadratic form in the permutation matrix.

### 3.4 Couplings that Theorem 1 could give and does not

Theorem 1 with a *positive* cut couples two sets. For a layout of vertex
separation `k` and prefixes `V_s ⊂ V_t`: every vertex outside `V_t` adjacent
to `V_s` lies in `C_t`, so `cut(V_s, V ∖ V_t) ≤ cut(V_s, V ∖ V_s) = cut(V_s, C_s) ≤ Δ|C_s| ≤ Δk`,
and Theorem 1 at `m₃ = 0` gives `cut(V_s, V ∖ V_s) ≥ λ₂ s(n − s)/n`: every
two-prefix inequality of this kind is implied by the one-prefix edge
expansion `k ≥ λ₂ s(n − s)/(nΔ)`, which at `s = n/2` is `λ₂n/(4Δ)` — weaker
than (21)'s `nλ₂/(Δ + λ₂)` by about four when `λ₂ ≪ Δ`. Maximising (20) or
(21) over nonnegative edge weights (Theorem 1 is stated for weighted
graphs, p. 2) is an eigenvalue optimisation the spectral report excluded;
it stays a single-separator inequality, so `spectral_bound.md` §1(i)
applies to every weighting and it cannot exceed Harper, whose ceiling is
below the optimum on 320 of the 338 gap instances and below the recorded
width on all 24 open classes. On the regular open graphs of §8 the uniform
weighting is optimal by symmetry, so nothing is lost there either.

### 3.5 The brief's questions (a)–(c)

(a) Theorem 1 couples two sets through their sizes and the cut between them
— used at `cut = 0` it is one separator; at `cut > 0` it reduces as in §3.4.
(b) No inequality for vertex separation; Theorem 8's bandwidth inequality
(18) is "if every `(m₁, m₂)`-pair has an edge then `bw ≥ n − m₁ − m₂ + 1`",
the bandwidth analogue of an empty pair, and it is *above* pathwidth.
(c) No cutting plane.

---

## 4. Gu & Liu (2022), *A tight lower bound on the matching number of graphs via Laplacian eigenvalues*, EJC 101, 103468

### 4.1 What it proves

Theorem 1.3 (p. 2): if `μ₂ ≥ r μₙ` with `0 < r ≤ ½` then the matching
number satisfies `α' ≥ r(n − 1)`; Corollary 1.4 (p. 3):
`α' ≥ min{⌈(μ₂/μₙ)(n − 1)⌉, ⌈(n − 1)/2⌉}`, tight on `K_{s,t}` and on
`K_s ∨ tK₁` (p. 3); Theorem 1.5 (p. 3): `n` odd and `2μ₂ ≥ μₙ` give a
factor-critical graph. The engine is **Lemma 2.2 (p. 3)**: if `G − S` is
disconnected with parts `X`, `Y`, `|X| ≤ |Y|`, then
`|X| ≤ n(μₙ − μ₂)/(2μₙ)` (2.2) and `|S| ≥ 2μ₂|X|/(μₙ − μ₂)` (2.3), both
derived on p. 4 from **Haemers' separation inequality** (Theorem 2.1,
p. 3): `|X||Y|/((n − |X|)(n − |Y|)) ≤ ((μₙ − μ₂)/(μₙ + μ₂))²`. The rest
(balloons, Theorem 3.1, p. 6; even spanning subgraphs, Theorem 4.1, p. 7;
spanning trees of maximum degree `k` when `(k − 1)μ₂ ≥ μₙ`, Theorem 4.2,
p. 7) applies the same lemma through Berge–Tutte-type conditions.

### 4.2 What it means for the spectral report

(2.3) is Theorem 3 of `spectral_bound.md` (via Gima et al.'s Lemma 4.1).
Haemers' inequality is, after clearing denominators with
`n − |X| = |Y| + |S|`, exactly the inequality
`(m₁ + m₃)(m₂ + m₃)(λₙ − λ₂)² ≥ m₁m₂(λₙ + λ₂)²` from which Helmberg et al.
derive (20) on p. 9 — the two are the same constraint on the triple
`(|S|, |X|, |Y|)`. Since (2.3) is *derived* from it (p. 4), every triple
satisfying Theorem 2 satisfies Theorem 3: **Theorem 3 is implied by
Theorem 2**, and the report's measurement that "Theorems 2 and 3 add almost
nothing to Theorem 1" (272 of 338 unchanged, §0 item 3) is explained —
Theorem 3 could never add to Theorem 2. (2.2), the bound on the smaller
side irrespective of `|S|`, is likewise a consequence of (20) and is inside
the report's feasibility test. Nothing in the paper couples more than one
separator; nothing concerns pathwidth. **Nothing beyond the citation**, and
the clarification above.

---

## 5. Mallach (2018), *Linear ordering based MIP formulations for the vertex separation or pathwidth problem*, JDA 52–53, 156–167 — skimmed for its LP statements

### 5.1 The statements

- **Theorem 4.1 (p. 159)**: for every digraph, the LP relaxations of both
  the position model `MIP_P` ((1)–(7)) and the set-assignment model `MIP_S`
  ((8)–(11): `b_{v,p} ≤ b_{v,p+1}`, `Σ_v b_{v,p} = p`,
  `b_{u,p} − b_{v,p} ≤ c_{v,p}` for arcs `(u, v)`, `Σ_v c_{v,p} ≤ Z`) have an
  optimum of zero, by the points `a* = 1/n` and `b*_{v,p} = p/n`. `MIP_S` is
  the chain IP of `chain_lp.md` §1 constraint for constraint, and `b*` is
  its uniform point.
- **`MIP_L` (p. 160)**: linear-ordering variables `x_{v,w}` with
  transitivity (13), cut variables `y_{v,w}` for `w` in the separation *at
  the cut after vertex `v`* (the paper's point of view, p. 157: cuts
  "associated with a vertex rather than with a position"), forced by
  `x_{u,v} + x_{v,w} − y_{v,w} ≤ 1` for arcs `(u, w)` (14), and
  `Σ_w y_{v,w} + Σ_{(v,w) ∈ A} x_{v,w} ≤ Z` per vertex (15). **Theorem 5.4
  (p. 162)**: its LP is zero iff the digraph is acyclic. **Theorem 5.5
  (p. 162)**: on the complete digraph the LP is `(n − 1)/2` against
  `vs = n − 1`. On the `n × n` grids `LP_L = 2` against pathwidth `n`
  (Table 3, p. 164; §6.1.1); on the HB and Small graphs "about 50% on
  average, but can be considerably worse (e.g., 30% for can___96) or much
  better (even 99% for dwt___66)" (p. 164).
- **Cut implication inequalities (18), p. 161**:
  `y_{u,w} + x_{v,w} − x_{v,u} − y_{v,w} ≤ 1` for non-arcs `(u, w)`, `(v, w)`
  — if `w` is in the separation after `u` and `v` lies between `u` and `w`,
  then `w` is in the separation after `v`. Valid (Theorem 5.2), cuts an
  optimal fractional point on a 4-vertex, 2-arc digraph (Theorem 5.3,
  p. 162); their effect on bounds is not measured. The 3-dicycle
  inequalities are separated lazily, "essential" for the LP times (p. 164).
- **Verdict of the author (p. 166)**: none of the three MIPs "is yet
  competitive to the currently best combinatorial branch-and-bound
  methods", and "even the lower bounds obtained with `MIP_L` are often
  inferior to those achieved by combinatorial methods for treewidth".
  CPLEX improves the global bound better on `MIP_S` (which starts at zero)
  than on `MIP_L` (which "often stagnates early", p. 165).

### 5.2 Against the three reports

(18) is the **persistence** family of `chain_lp.md` §3 in linear-ordering
variables; in the chain space it is satisfied by the uniform point and
moves nothing. Whether `LP_L` exceeds Harper anywhere is not decidable from
the paper, and the comparable cases say no: `K_n` (half of Harper's `n − 1`)
and the grids (2 against a Harper value at the pathwidth). The ceiling
argument of `chain_lp.md` §5 transports: in Mallach's space the only link to
`Z` is per vertex, so any LP there, up to the integer hull, is at most
`max_{ν ∈ Δ(V)} min_σ Σ_v ν(v) |S(σ, v)|`; on `K_n` every layout has
`|S(σ, v)| = n − π(v)`, the adversary places heavy vertices last, the
function is symmetric and concave in `ν`, so the uniform `ν` is optimal and
the value is `Σ_i (n − i)/n = (n − 1)/2` — Theorem 5.5's number: **his LP is
at its own ceiling on `K_n`, and that ceiling is half the vertex
separation**, where the level-indexed ceiling `L` is `n − 1`. Indexing cuts
by vertex rather than by level costs the formulation a factor of two on the
complete graph. The measurement of item 3 in §0 is what would settle the
general case.

---

## 6. Contradictions and corrections to the three reports

1. **`chain_lp.md` §0 and §7** attribute Mallach's zero to "the
   position-based vertex-separation MIPs". Theorem 4.1 (p. 159) covers the
   set-assignment model `MIP_S` too, and `MIP_S` *is* the chain IP, with the
   same uniform point. The prior statement is therefore of the report's §2
   first sentence ("the bare LP has optimum 0"), not merely of a cousin's.
   The Harper-cut identity and the ceiling theorem remain unstated in the
   paper, as the report says.
2. **`chain_lp.md` §2** says "we do not hold the paper and do not know
   whether that relaxation exceeds Harper anywhere". The paper has been in
   `literature/` since 2026-09-28 (`literature/MISSING.md` line 58, which
   summarises it); the 2026-11-10 LP section of `MISSING.md` (line 839
   onward) still marks it "Not held" — an internal inconsistency to fix.
   On what the paper does say about Harper: §5.2 above.
3. **`checkpoint_relaxation.md` §0, "What is new, and what to keep"** calls
   the nested-chain encoding "a compact exact encoding of vertex
   separation". As an ILP it is Solano & Pióro (2010), Coudert's
   Formulation 2 + 4 (`PW2`, 2016, pp. 3–7, 13) and Mallach's `MIP_S`
   (2018, p. 159); Coudert's Table 4 is the precedent for §8's finding that
   the prefix form beats the position form. What is new is the SAT form,
   the DRAT proof object and the measurement at 41–75 customers.
4. **`spectral_bound.md` §0 item 3** treats Theorems 2 and 3 as separate
   inequalities that happen to add little. Theorem 3 (Gu & Liu's (2.3)) is
   derived from Haemers' inequality, which is Theorem 2 rearranged (§4.2),
   so it is implied; the measurement is explained, not contradicted.
5. **`spectral_bound.md` §0, "Not done, and why"** attributes a
   "diagonal-correction `max_u μ₂(L + diag u)`" to Helmberg et al. Their
   nonlinear improvement is the convex program over `B` for the bandwidth
   bound (Theorem 9, §7.1, pp. 8, 16), and edge-weight freedom (p. 8); the
   diagonal shift in the paper is the fixed `D` of eq. (9) (p. 3). The
   verdict ("every such bound is an inequality on one separator") stands
   for the separator bounds and does not apply to Theorem 9, which is not a
   pathwidth bound at all (§3.3).
6. **Helmberg's Theorem 14** (p. 11: (20) beats (21) almost surely in
   `G(n, p)`, fixed `p`) is not contradicted by the report's "Theorem 2 adds
   nothing on 272 of 338": the report's Theorem 1 uses the top-`c` degree
   sum, stronger than (21)'s `Δc`, and the MOSP graphs are far from `G(n, p)`
   at fixed `p` (`μ₂` 0.5–11 against `Δ` 15–64, from the fringe of
   low-degree customers, `spectral_bound.md` §0).

---

## 7. The brief's checklist, in one table

| paper | (a) several positions coupled | (b) valid inequality for vs/bw not single-prefix | (c) separation routine for our encodings | (d) spectral, not one separator | verdict |
|---|---|---|---|---|---|
| Caprara et al. 2011 | yes, over distances (§1.2) | none; MinLA only | stars by sorting, projection by APSP — need distances | none | citation only (§1.4) |
| Coudert 2016 | no | no | none ("cutset inequalities" named, p. 15) | none | citation only (ILP precedent of the chain) |
| Helmberg et al. 1995 | Theorem 1 at `cut > 0` — reduces to one prefix (§3.4) | bandwidth only, above pw | no | Theorems 9, 19 — bandwidth and 1-sum, not pw (§3.3) | citation; the old bound re-aimed (§8) |
| Gu & Liu 2022 | no | no | no | no; implied by Helmberg (20) | citation; one clarification |
| Mallach 2018 | (18) = persistence | `LP_L`, half of Harper on `K_n` | lazy 3-dicycles | no | the one measurement left (§0 item 3) |

---

## 8. The measurement made here: the spectral floor on the open named graphs

### 8.1 The nine

The spectral report evaluated Theorem 4 (the prefix form of the three
separator inequalities) on the 50,949 certified MOSP instances and 274,048
small graphs, never on the pathwidth dataset's open classes. The nine
smallest open named graphs are cages and vertex-transitive graphs (regular,
no fringe), where `μ₂/Δ` is large. Eigenvalues by `numpy` on the dataset's
edge lists (`paper1/data/dataset/pathwidth_dataset.jsonl.gz`), all three
families (`graph`, `peel`, `minor`) of `learning.spectral_bound.spectral_bounds`,
0.2–0.9 s each; the record floor is the best of `reports/scratch/dataset_open/results_quick.csv`
(`lower`, the 2026-10-12 C runs), loop0013's pass 1 (`13_pass1/pass1.csv`,
`ladder_floor` and `search_floor`, 600 s of minor search each) and
`pathwidth_solver/bench/results/repaired/named.csv`. Pathwidth units.

| graph | n | m | Δ | μ₂ | μₙ | width on record | best floor on record | spectral (all three families agree) | above the record |
|---|---|---|---|---|---|---|---|---|---|
| FosterGraph | 90 | 135 | 3 | 0.5505 | 6 | 20 | 16 | 14 | no |
| BiggsSmithGraph | 102 | 153 | 3 | 0.4384 | 5.532 | 19 | 17 | 14 | no |
| Balaban11Cage | 112 | 168 | 3 | 0.4965 | 5.856 | 24 | 18 | 16 | no |
| LjubljanaGraph | 112 | 168 | 3 | 0.4384 | 6 | 22 | 17 | 15 | no |
| DejterGraph | 112 | 336 | 6 | 1.6277 | 12 | 33 | 28 | 24 | no |
| BubbleSortGraph_5 | 120 | 240 | 4 | 0.3820 | 8 | 23 | 17 | 11 | no |
| **NStarGraph_5** | 120 | 240 | 4 | 1 | 8 | 28 | 23 | **24** | **+1** |
| **OddGraph_5** | 126 | 315 | 5 | 2 | 9 | 41 | 31 | **36** | **+5** |
| **Tutte12Cage** | 126 | 189 | 3 | 0.5505 | 6 | 26 | 19 | 20 | **+1** |
| he044 (PACE 2017, not named) | 125 | 736 | 23 | 4.127 | 25.04 | 62 | 52 | 29 (minor family) | no |

The three that move rest on Theorem 1 of `spectral_bound.md` (Mohar &
Poljak; Helmberg et al. eq. (21), p. 11) alone, with `S(c) = Δc` on a
regular graph, and the eigenvalues are exact: `OddGraph_5` is the Kneser
graph `K(9, 4)` with adjacency eigenvalues `5, −4, 3, −2, 1`, so
`μ₂ = 5 − 3 = 2` and `μₙ = 5 + 4 = 9`; `NStarGraph_5` is the star graph
`S₅`, 4-regular bipartite with algebraic connectivity 1, so `μₙ = 8`; the
Tutte 12-cage has adjacency eigenvalues `±3, ±√6, ±√2, 0`, so
`μ₂ = 3 − √6` and `μₙ = 6`. By hand on `OddGraph_5`: a separator triple
`(C, A, B)` satisfies `5|C| ≥ 2(|A| + |B| − (|A| − |B|)²/126)`; in a layout
of vertex separation `k`, the prefix of 45 vertices has `|A| = 45`,
`|B| = 81 − |C|`, and `|C| = 35` gives `175 ≥ 2(91 − 1/126) = 181.98`, false,
while `|C| = 36` gives `180 ≥ 180`; so `k ≥ 36`. For `NStarGraph_5` the
balanced level gives `4c ≥ 120 − c`, `c ≥ 24`; for the Tutte 12-cage,
`3c ≥ 0.5505 (126 − c)`, `c ≥ 19.54`, so `c ≥ 20`. The values are the Gima
treewidth bound `nμ₂/(Δ + μ₂)` of `spectral_bound.md` §1(ii), so they are
also treewidth floors (`tw(OddGraph_5) ≥ 35`) and sit under the treewidth
ceiling; what is new to the record is only that nobody had computed them
there. Since `spectral ≤ Harper`, Harper's exact value on `OddGraph_5` is at
least 36; it is not computable at 126 vertices by the routes on record.

### 8.2 All 312 open classes of loop0013's pass 1

The same computation over every open class pass 1 ran (`n` to 1,024; the
`peel` and `minor` families to 200 vertices, the whole graph alone above),
against the same record floors: script `spectral_open.py`, output
`spectral_open.csv`, log `spectral_open.log`, all under
`reports/scratch/layout_lp_literature/`; 206 s in all. **The spectral floor is
above the best floor on record on 9 of the 312 classes, equal on none and
below on 303** (median shortfall 17; the floors on record for the large
classes are pass 1's 600-second minor-search floors, which had already
raised the C program's starting floors — e.g. the Cameron graph from 43 to
88, `le450_5a` from 17 to 63). The nine are the three of §8.1 and six larger
classes, five of them regular or dense:

| class | n | m | degrees | μ₂ | μₙ | width | best floor on record | spectral (whole graph) | Thm 1 (Mohar–Poljak) | Thm 2 (Helmberg (20)) | gain |
|---|---|---|---|---|---|---|---|---|---|---|---|
| CameronGraph (srg(231, 30, 9, 3)) | 231 | 3,465 | 30-regular | 21 | 33 | 161 | 88 | **147** | 96 | **147** | +59 |
| HyperStarGraph_10_5 | 252 | 630 | 5-regular | 1 | 10 | 62 | 18 | **42** | 42 | 26 | +24 |
| he048 (PACE 2017 heuristic) | 363 | 2,992 | 14–23 | 4.14 | 24.8 | 122 | 34 | **61** | 58 | 61 | +27 |
| le450_5a (TreewidthLIB colouring) | 450 | 5,714 | 13–42 | 10.48 | 45.0 | 245 | 63 | **110** | 110 | 105 | +47 |
| le450_5b | 450 | 5,734 | 12–42 | 10.31 | 44.7 | 261 | 63 | **110** | 110 | 104 | +47 |
| Cell120 (the 120-cell) | 600 | 1,200 | 4-regular | 0.146 | 6.85 | 67 | 17 | **22** | 22 | 13 | +5 |

(Per-theorem columns from `prefix_separator_bound` with one inequality at a
time; the whole-graph value is the three together, which on these graphs is
the better of the two.) On the Cameron graph it is **Helmberg's own
inequality (20) that does the work** (147 against Mohar–Poljak's 96; by
hand, `|C| ≥ |A||B|/12` and at the balanced level `(231 − c)²/48 ≤ c`
first holds at `c = 147`, where it is an equality), as their Theorem 14
(p. 11) predicts for dense random-like graphs; on the Leighton graphs and
the 120-cell it is Mohar–Poljak with the top-`c` degree sum. The gaps left
are 14, 20, 61, 135, 151 and 45: nothing closes, and these floors are the
Gima treewidth bound in disguise (§1(ii) of `spectral_bound.md`), so they
say nothing about `pw − tw`. Above 200 vertices only the whole graph was
evaluated; the `peel` and `minor` families (which lifted `he044` from 25 to
29) are cheap there and were not run.

### 8.3 What is proposed

An evidence row of a new kind for the nine classes where the spectral value
is the best floor on record, reproducible from the edge list by
`spectral_graph_bound` — **proposed, not applied**, since writing it is a
dataset rebuild (`reports/obstruction_search.md` §7); and the `peel` and
`minor` families on the 175 open classes above 200 vertices (eigenvalues
along the contraction-degeneracy sequence; minutes per class; kill: no
further class moves). No solver run is proposed: all nine stay open, and
the family's next value would be Harper's exact profile at these sizes,
which nothing on record computes.

## 9. Regenerate

```bash
cd ~/dev/MOSP
for f in 2011-Caprara-* 2016-Coudert-Note-* 1995-Helmberg-* 2022-Gu-Liu-* mallach_2018_*; do
  pdftotext -layout "literature/$f" "/tmp/${f%.pdf}.txt"; done     # the dumps read here
PYTHONPATH=. nice -n 19 python3 reports/scratch/layout_lp_literature/spectral_open.py   # §8, eigenvalues only
```
