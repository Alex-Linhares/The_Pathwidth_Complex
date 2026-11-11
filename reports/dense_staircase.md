# Dense random graphs: the staircase, and the constant `2 + √2`

*2026-11-11, one session (the item proposed in `reports/layout_second_moment.md` §3.4 and
§7). Code `learning/staircase_moment.py`, tests `tests/test_staircase_moment.py` (751),
Lean `lean/MOSPFormalization/Staircase.lean` (15 theorems, no `sorry`, axioms `propext`,
`Classical.choice`, `Quot.sound` only — `reports/scratch/dense_staircase/axioms.log`),
data and logs under `reports/scratch/dense_staircase/`, literature in
`literature/MISSING.md` under "Dense random graphs: the staircase constant (2026-11-11)".
Every number is beside its command in §6. Nothing re-solved; `solutions/` untouched; no
pathwidth run; under one core-hour in all.*

## 0. Summary

**The conjecture was that the dense sandwich `2 ≤ (n − pw)/log_b n ≤ 4` closes at `4`.
It closes at `2 + √2 ≈ 3.414`, and both halves are now proved on paper, one of them in
Lean.** Throughout `p ∈ (0, 1)` is fixed, `q = 1 − p`, `b = 1/q`, `L = log_b n`.

**The lemma (§1; Lean, both directions).** For `1 ≤ s ≤ n`, `pw(G) ≤ n − s` **iff** `G` has
a *generalised staircase of size `s`*: sequences `v_1 … v_{s−1}` and `u_1 … u_{s−1}`,
each injective, with `u_i ∉ {v_1 … v_{s−i}}` and `u_i` non-adjacent to `v_1 … v_{s−i}` for
every `i` (`pathwidth_le_iff_exists_isGenStaircase`). A *staircase* — all `2s − 2`
vertices distinct — is sufficient (`pathwidth_le_of_isStaircase`) and is exactly the
structure of **bandwidth** `≤ n − s` when `2s − 2 ≤ n` (first `s − 1` and last `s − 1`
positions; `check_bandwidth_lemma`, zero violations on every graph to `n = 5` and on
samples at 6–7). The forward direction lays `v` out first; the converse draws the `u`'s
greedily from the inactive suffixes, which needs only `|C_i| ≥ i + 1`, not Hall. Checked
on every labelled graph with `n ≤ 6` (32,768 at six) and 300 samples at `n = 7`: zero
violations of either direction (`lemma_check.log`).

**The first moment of staircases is not the threshold (§2).** `E[X_s] = (n)_{2s−2} q^{s(s−1)/2}`
crosses `1` at `s₀ = (4 − o(1)) L` — Theorem B's constant — but a staircase contains a
denser sub-configuration: the **corner block** `v_1 … v_a`, `u_1 … u_b` with its
`c(s, a, b) = Σ_{i ≤ b} min(a, s − i)` forced non-edges. Every generalised staircase of
size `s` contains one, with the forced pairs distinct even when `u`'s coincide with later
`v`'s (`forcedSet_card`), so the union bound gives, **in Lean on `Fin n`**
(`weightedSum_pathwidth_le_block`):

```
P( pw(G(n, p)) ≤ n − s ) ≤ n^(a + b) · (1 − p)^c(s, a, b)      for all 1 ≤ s ≤ n, a, b ≤ s − 1.
```

With `s = aL` and `a' = b' = yL` the exponent is `L² ln b · [2y − y² + (2y − a)²/2 · 1[2y > a]]`,
minimised at `y = a − 1` with value `−(a²/2 − 2a + 1) L² ln b`, which is negative iff
`a > 2 + √2`. Hence **`n − pw(G(n, p)) ≤ (2 + √2 + ε) log_b n` with probability
`1 − exp(−(√2 ε + o(1)) ln² n / ln b)`**, for every `ε > 0`. The empty pair of Theorem B is
the block `(t, t − 1)` — the `y = a/2` slice, which only reaches `4`; the block at
`y = 1 + √2` is where the staircase is rarest. Numerically the block threshold `s_block/L`
is `3.397–3.432` from `n = 10³` to `10⁷` at `p = ½` and `3.408` from `10⁴` at `p = 0.3`,
with the argmin block at `(2.41–2.51) L` (`thresholds.csv`); the plain staircase threshold
goes to `3.96–4.00`. The bandwidth half of this — `bw ≥ n − (2 + √2 + o(1)) log₂ n` — is
**Kuang & McDiarmid (1985)**, quoted by Erdős, Hell & Winkler (1989) Theorem 3 (§5); a
bandwidth lower bound says nothing about pathwidth, and the generalised staircase with
its coincidences is what carries the argument across. We found no prior statement for
pathwidth.

**The second moment on staircases (§3; on paper).** By symmetry
`E[X_s²]/E[X_s]² = E_{S'}[b^{|F' ∩ F₀|}]` over a uniform ordered placement `S'` against a
fixed staircase `S₀`. Grouping `S'` by how many of `S₀`'s `v`'s and `u`'s it uses, `(a', b')`,
the overlap is at most the block cost `c(s, a', b')` (every forced pair of both lies inside
`S₀`'s pairs on the shared set, and prefix index sets maximise their number), which gives
the finite bracket `ratio_log_lower ≤ ln ratio ≤ ratio_log_upper` of two `O(s²)`-term sums,
checked against the exact ratio by enumeration at `n ≤ 7` and against every labelled graph
at `n ≤ 6`. The term with `j = xL` shared vertices is `n^{−j} b^{c}` up to `e^{O(j log L)}`,
exponent `L² ln b · h(x)`, `h(x) = −x + x²/4 − (x − a)²/2 · 1[x > a]`, concave on `[a, 2a]`
with maximum `a²/2 − 2a + 1` at `x = 2a − 2` — the same number as the block, with the
opposite sign. **So for `a < 2 + √2` every overlap term is `≤ (2m² n^{−δ(a)})^j`, the ratio is
`1 + O(log² n · n^{−δ(a)})`, and Paley–Zygmund gives `pw ≤ n − (2 + √2 − ε) log_b n` whp;
for `a > 2 + √2` the ratio is `≥ exp((a²/2 − 2a + 1 − o(1)) L² ln b)`, exponential in
`log² n`.** Measured: the rigorous lower bracket at `p = ½` is `ln ratio ≥ 29.6 → 298` for
`a = 3.9` from `n = 10²` to `10⁷` against the limit `24.6 → 302`, and `→ 0⁻` for
`a ≤ 3.3` (`ratio_brackets.csv`). The crude upper bracket carries an `e^{O(L log L)}` slack
and is useless at any feasible `n` (it is `e^{320}` at `a = 3`, `n = 10⁷`); it is the proof's
instrument, not a measurement. The §3.4 claim of the previous report — `cost(j) ≤ j²/8`,
"bounded at both ends for `a < 4`" — was wrong about the dangerous overlap: it is the
corner block with `cost = j²/4 − (j − s)²/2`, in the middle, not the sub-staircase at the
end.

**The kill criterion, as stated before computing**: dead if at every `a < 4` the ratio is
unbounded and the repairs fail; alive if some `a` near `4` works. Neither: the plain
second moment works exactly up to `2 + √2` and no repair can carry it further, because the
*first* moment on the block already excludes staircases above `2 + √2`. **The conjectured
constant `4` is refuted; the constant is `2 + √2`, and the record's sandwich `[2, 4]`
becomes an equality:**

```
n − pw(G(n, p)) = (2 + √2 + o(1)) log_b n      whp, for every fixed p ∈ (0, 1),
```

the lower half with error `e^{−Θ(ln² n)}` (block first moment; Lean finite inequality),
the upper half with error `O(log² n · n^{−δ})` (staircase second moment, on paper; or
Kuang–McDiarmid's bandwidth bound with `pw ≤ bw`). A corollary: **the pathwidth and the
bandwidth of dense `G(n, p)` agree to within `o(log n)`**, though `pw ≤ bw` in general and
the gap is `Θ(n)` on sparse graphs.

**The data (§4).** On the dense cells of `reports/random_graph_middle.md` (`p = ½`, 20
proved graphs each) the measured median `n − pw` is `11, 12, 13, 14` at `n = 30, 40, 50, 60`;
the block's `E ≥ 1` threshold is `12, 13, 14, 15` — **one above the median at every `n`** —
where the staircase first moment says `15, 17, 19, 21` and the limits `(2 + √2) L` and `4L`
say `16.7 … 20.2` and `19.6 … 23.6` (`data_vs_floors.csv`): at `L ≈ 5–6` the `o(1)` is a factor
of two and the finite block count is what to evaluate. As a 95% floor the block family
equals the empty-pair floor (`18, 26, 34, 44`) except at `n = 50` (`35` against `34`): the
block's advantage is asymptotic (`79` against `93` for `s` at `n = 10⁷`), and `2L ≈ 10–12`
sits just below the data.

**Lean (§7).** `Staircase.lean`: `IsGenStaircase`, `IsStaircase`; `exists_layout_prefix` (a
layout with any injective ordered prefix); `vertexSepAt_le_of_isGenStaircase`,
`pathwidth_le_of_isGenStaircase`, `pathwidth_le_of_isStaircase`; `exists_injOn_mem` (greedy
selection); `exists_isGenStaircase_of_pathwidth_le`; `pathwidth_le_iff_exists_isGenStaircase`;
`blockIndex`, `blockCost` (four values by `decide`, matching Python), `forcedSet`,
`blockTuples`, `forcedSet_card`, `exists_blockTuple_of_pathwidth_le`,
`sum_gnpWeight_univ_eq_one`, `sum_gnpWeight_patternGraphs_univ`,
`weightedSum_graphsOfPathwidthLe_le_block`, `weightedSum_pathwidth_le_block`;
`StaircaseUpperTail` as a `Prop`, not proved (the second moment is a page on paper but a
long finite-sum formalisation). The asymptotic optimisation (`a = b = ⌊(1 + √2) L⌋`) is on
paper.

**Literature (§5).** Kuang & McDiarmid (1985, *Ars Combinatoria* 20A) have `2 + √2` for the
bandwidth of `G(n, ½)`, two-sided; Erdős, Hell & Winkler (1989) state it and say "even the
constant is determined"; Füredi & West (2001) call the structure the halfgraph. For
pathwidth, treewidth or vertex separation of dense `G(n, p)` nothing sharper than
`n − O(√(n/p))` (Perarnau & Serra 2014) is in print. The template for the second moment is
Matula's clique number (`α ≈ 2 log_b n`, Frieze & Karoński Thm 7.3) and the densest-
subgraph threshold of Bollobás (1981). Seven papers recorded as wanted, Kuang & McDiarmid
first.

**Status: proved**, with the second-moment half on paper (§3) and both the lemma and the
first-moment half in Lean. Supersedes `reports/layout_second_moment.md` §3.4's reading of
the overlap sum and its item 1 of §7; the random-graph sandwich of
`reports/random_graph_first_moment.md` (Theorem B) and `reports/random_graph_middle.md`
("the dense sandwich `[2, 4]`") should be read with the constant `2 + √2`.

---

## 1. The staircase lemma

Fix a graph `G` on `n` vertices and `1 ≤ s ≤ n`; write `m = s − 1`. In the repository's
convention (`VertexSeparation.lean`) a layout `σ` has, at position `i` (prefix of size
`t = i + 1`), the *active suffix* — suffix vertices with a neighbour in the prefix — and
`vs(σ) = max_i |active_i|`; `pw = min_σ vs(σ)` (`vertexSeparation_eq_pathwidth`).

**Definition.** A *generalised staircase of size `s`* is a pair `v, u : Fin m → V`, each
injective, with `u_i ≠ v_j` and `u_i ≁ v_j` whenever `i + j < m` (0-indexed; in 1-indexed
terms `u_i` avoids and is non-adjacent to `v_1 … v_{s−i}`). A *staircase* has in addition
`u_i ≠ v_j` for all `i, j`.

**Lemma 1 (sufficient; `pathwidth_le_of_isGenStaircase`).** A generalised staircase of
size `s` gives `pw(G) ≤ n − s`.

*Proof.* Take a layout with `σ(v_j) = j` and every other vertex at a position `≥ m`
(`exists_layout_prefix`: `Equiv.ofBijective` of the map `x ↦ (ofInjective v)⁻¹ x` on the
range of `v` and `m + e(x)` outside, `e` any bijection of the complement with `Fin (n − m)`).
At position `i < m` the vertices `u_k`, `k < m − i`, are distinct, lie in the suffix (if
`u_k = v_j` then `k + j ≥ m` so `j > i`; otherwise its position is `≥ m > i`) and have no
prefix neighbour (a prefix vertex at position `≤ i < m` is some `v_j` with `j ≤ i`, and
`k + j < m`), so `|inactive_i| ≥ m − i` and `|active_i| ≤ (n − i − 1) − (m − i) = n − s`. At
positions `i ≥ m`, `|active_i| ≤ n − i − 1 ≤ n − s`. ∎

**Lemma 2 (necessary; `exists_isGenStaircase_of_pathwidth_le`).** If `pw(G) ≤ n − s` then
`G` has a generalised staircase of size `s`.

*Proof.* Take an optimal layout `σ`, `v_j := σ⁻¹(j)` for `j < m`, and `C_k :=` the inactive
suffix at position `m − 1 − k` for `k < m`. Then `|C_k| = (n − (m − k)) − vs_{m−1−k} ≥
(n − m + k) − (n − s) = k + 1`. Greedy selection (`exists_injOn_mem`: pick `u_k ∈ C_k`
outside `{u_0 … u_{k−1}}`, possible as `|C_k| > k`) gives injective `u` with `u_k ∈ C_k`;
`u_k` is in the suffix at position `m − 1 − k`, hence `≠ v_j` for `j ≤ m − 1 − k`, i.e. for
`k + j < m`, and non-adjacent to the prefix there, which contains those `v_j`
(`not_adj_prefix_inactiveSuffix`). ∎ The sets `C_k` happen to be nested, but the selection
does not need it.

**Corollary (`pathwidth_le_iff_exists_isGenStaircase`).** `pw(G) ≤ n − s` iff a generalised
staircase of size `s` exists.

**Bandwidth.** A layout has bandwidth `≤ n − s` iff no edge joins positions more than
`n − s` apart. Positions `i` from the front and `j` from the back are `n + 1 − i − j` apart,
more than `n − s` iff `i + j ≤ s`; two front positions are at most `s − 2` apart and a front
and a middle position at most `n − s`. So for `2s − 2 ≤ n`, **`bw(G) ≤ n − s` iff `G` has a
staircase of size `s`** (strict: the front and back vertices are distinct). Without the
size condition this fails (the empty graph on 3 vertices, `s = 3`). Checked by brute
force: `check_bandwidth_lemma`, every graph at `n ≤ 5` (`3072` pairs at five), 300 samples
at `n = 6` and 60 at `n = 7`, zero violations (`bandwidth_check.log`). This is the
structure Kuang & McDiarmid (1985) count (§5).

**The coincidences.** The generalised form differs from the strict one only in that `u_i`
may equal a *later* `v_j` (`j > s − i`). On every labelled graph at `n ≤ 6`, the strict
staircase is absent where the generalised one is present on `6,509` of `196,608`
`(graph, s)` pairs (`lemma_check.log`, `strict_gap`), so the distinction is real for
pathwidth; for the moments it costs nothing, because the forced pairs stay distinct
(§2, `forcedSet_card`).

## 2. The first moment: staircases, and the corner block

**The staircase count.** The ordered number `X_s` of (strict) staircases has
`E[X_s] = (n)_{2s−2} q^{s(s−1)/2}` (`2s − 2` labelled vertices, `Σ_{i<s} (s − i)` forced
non-edges), so `E[X_s] ≥ 1` iff `s ≤ s₀(n) = (4 − o(1)) L`: `s₀/L = 3.06, 3.19, 3.37, 3.56`
at `n = 30 … 60` and `3.91, 3.99, 3.96, 4.00` at `10³, 10⁴, 10⁶, 10⁷` (`p = ½`;
`thresholds.csv`). As a lower bound on pathwidth this is Theorem B again, since
`P(pw ≤ n − s) ≤ E[#generalised staircases]`, and the coincidence patterns are at most
`s^{s−1}` in number, each with fewer vertices at the same cost; but it is not the
threshold of the structure.

**The corner block.** For `a, b ≤ s − 1` the block `(a, b)` of a generalised staircase is
`v_1 … v_a`, `u_1 … u_b` with the forced non-edges `{u_i, v_j}`, `i ≤ b`, `j ≤ min(a, s − i)`;
their number is

```
c(s, a, b) = Σ_{i=1}^{b} min(a, s − i) = #{(i, j) ∈ Fin b × Fin a : i + j + 1 < s}   (0-indexed),
```

`= ab` for `a + b ≤ s` and `ab − (a + b − s)(a + b − s + 1)/2` for `a + b ≥ s`
(`block_cost`, closed form checked against the sum on `9³` triples and against the Lean
`blockCost` on four values by `decide`).

**Lemma 3 (`forcedSet_card`).** On a block cut from a generalised staircase the map
`(i, j) ↦ {u_i, v_j}` is injective on the index set and no pair is diagonal. *Proof.*
`u_i ≠ v_j` for `i + j < m` is the `ne` clause. If `{u_i, v_j} = {u_{i'}, v_{j'}}` with
`u_i = v_{j'}` and `u_{i'} = v_j` then `i + j' ≥ m` and `i' + j ≥ m` by `ne`, against
`i + j < m` and `i' + j' < m`. ∎

**Theorem B⁺ (`weightedSum_pathwidth_le_block`).** For `0 ≤ p ≤ 1`, `1 ≤ s ≤ n`, `a, b ≤ s − 1`:

```
P( pw(G(n, p)) ≤ n − s ) ≤ n^(a + b) · (1 − p)^c(s, a, b).
```

*Proof.* A graph of pathwidth `≤ n − s` has a generalised staircase (Lemma 2), whose
block `(a, b)` is a tuple in `(Fin a → V) × (Fin b → V)` with a forced set of exactly
`c(s, a, b)` non-diagonal pairs (Lemma 3), all non-edges. For each such tuple the `G(n, p)`
weight of "all forced pairs are non-edges" is `(1 − p)^c` (the independence lemma
`sum_gnpWeight_pattern` of `LayoutMoment.lean` with `E = univ`, `F_p = ∅`), and there are
at most `n^{a+b}` tuples. ∎ Coincidences `u_i = v_j` are tuples like any other and need no
separate accounting.

**The symmetric count (paper and Python, not Lean).** The full rows `v_1 … v_{f_v}`,
`f_v = min(a, s − b)`, and the full columns `u_1 … u_{f_u}`, `f_u = min(b, s − a)`, are
interchangeable without changing the forced set, so the number of distinct forced sets is
at most `C(n, f_v)(n − f_v)_{a−f_v} · C(n − a, f_u)(n − f_v − f_u)_{b−f_u}`
(`log_block_count`), which at `(a, b) = (t, t − 1)`, `2t − 1 ≤ s`, is the empty-pair count
`C(n, t) C(n − t, t − 1)` of `reports/random_graph_first_moment.md` (0) exactly
(`test_block_family_contains_the_empty_pair`). The block family contains Theorem B.

**The asymptotics.** Put `s = aL`, `a' = b' = yL`, `0 < y ≤ a`. Then
`c = y²L² − T((2y − a)L) · 1[2y > a]` with `T(k) = k(k+1)/2`, and

```
ln( n^{2yL} q^{c} ) = L² ln b · g_a(y) + O(L),    g_a(y) = 2y − y² + (2y − a)²/2 · 1[2y > a].
```

On `2y ≤ a`, `g_a(y) = 2y − y² > 0` for `y < 2`, and `g_a(a/2) = a − a²/4` is Theorem B's
exponent (zero at `a = 4`). On `2y > a`, `g_a(y) = y² + 2(1 − a)y + a²/2`, a convex parabola
with minimum at `y = a − 1` (inside the range iff `a > 2`) and value
`g_a(a − 1) = a²/2 − (a − 1)² = −(a²/2 − 2a + 1)`, negative iff `a > 2 + √2`. So for
`a = 2 + √2 + ε` the block `a' = b' = ⌊(a − 1)L⌋` gives

```
P( pw ≤ n − (2 + √2 + ε) log_b n ) ≤ exp( −(√2 ε − O(ε²) − o(1)) · L² ln b ) = exp( −(√2 ε + o(1)) ln² n / ln b ),
```

the derivative of `a²/2 − 2a + 1` at `2 + √2` being `√2`. **The lower half of the equality.**
Numerically (`block_threshold`, ordered count, `thresholds.csv`): the least `s` whose
block bound is below `1` has `s/L = 3.26, 3.19, 3.37, 3.39` at `n = 30 … 60`, `3.31, 3.40, 3.36,
3.41` at `100, 200, 400, 10³`, and `3.387, 3.432, 3.412, 3.397` at `10⁴ … 10⁷` (`p = ½`);
`3.408` at every `n ≥ 10⁴` for `p = 0.3`; the argmin block is square with
`a'/L = 2.41–2.54`, i.e. `1 + √2 = 2.414`. The convergence is from both sides and slow in
`1/L`, as the `O(L)` terms say.

*Why the block and not the empty pair.* The empty pair `(v_1 … v_{s/2}; u_1 … u_{s/2})` is
the slice of the staircase where every pair is forced: `s²/4` pairs on `s` vertices. The
block at `y = a − 1` has `(a − 1)²L² − (a − 2)²L²/2` pairs on `2(a − 1)L` vertices — at
`a = 2 + √2` that is `1.00 L` pairs per vertex against the empty pair's `0.85 L` — and a
structure is excluded by its densest part. This is the sub-configuration criterion of
Erdős–Rényi and Bollobás (§5), applied to a pattern of forbidden edges.

## 3. The second moment on staircases

**Setup.** `X = X_s`, `m = s − 1`, `N = m(m + 1)/2`, `F(S)` the forced pairs of a placement
`S` (an injective `2m`-tuple). `E[X²] = Σ_{S, S'} q^{|F(S) ∪ F(S')|}` and all `S` are
equivalent under relabelling, so

```
R := E[X²]/E[X]² = (1/(n)_{2m}) Σ_{S'} b^{|F(S') ∩ F(S₀)|} = E_{S' uniform}[ b^{ov(S')} ].
```

**The bracket.** Group `S'` by the number `a'` of `S₀`'s `v`-vertices and `b'` of its
`u`-vertices it uses, `j = a' + b'`. There are `C(m, a') C(m, b') (2m)_j (n − 2m)_{2m−j}` such
`S'` (choose the shared vertices, the slots they occupy, the rest outside `S₀`). Every pair
in `F(S') ∩ F(S₀)` lies in `F(S₀)` and inside the shared set, and the number of `S₀`-forced
pairs inside index sets `I ⊆ [m]` (the `v`'s) and `J ⊆ [m]` (the `u`'s) is
`#{(i ∈ J, j ∈ I) : i + j ≤ s}`, maximised by the prefixes `I = [a']`, `J = [b']` at
`c(s, a', b')`. Hence

```
R ≤ U := Σ_{a', b' ≤ m} C(m,a') C(m,b') (2m)_{a'+b'} (n − 2m)_{2m−a'−b'} / (n)_{2m} · b^{c(s, a', b')}
```

(`ratio_log_upper`), and keeping only the placements that agree with `S₀` on the prefixes
in the same roles and are disjoint elsewhere,

```
R ≥ Λ := Σ_{a', b' ≤ m} (n − 2m)_{2m−a'−b'} / (n)_{2m} · b^{c(s, a', b')}
```

(`ratio_log_lower`). Both are checked: `Λ ≤ R ≤ U` with `R` exact, by enumeration of
every `S'` at `n ≤ 7` (`exact_ratio_small`) and by enumeration of every labelled graph at
`n ≤ 6` with `E[X]` and `E[X²]` in rationals (`brute_moments`;
`test_moments_against_every_labelled_graph`). At `n = 6`, `s = 3`, `p = ½`: `R = 1.694`,
`Λ = 0.089`, `U = 3.33`.

**The exponent.** For `j = xL` shared vertices, `c(s, a', b') ≤ j²/4` if `j ≤ s` and
`≤ j²/4 − (j − s)²/2` if `j ≥ s` (the symmetric split is the largest; `(a'+b'−s)(a'+b'−s+1)/2
≥ (j − s)²/2`), while `(n − 2m)_{2m−j}/(n)_{2m} ≤ (n − 2m)^{−j}` and
`C(m,a') C(m,b') (2m)_j ≤ (2m²)^j`. So the `(a', b')` term of `U` is at most

```
( 2m² / (n − 2m) )^j · b^{c} = exp( L² ln b · h(x) + j · O(log L) ),
h(x) = −x + x²/4 − (x − a)²/2 · 1[x > a].
```

`h` is `−x(1 − x/4) < 0` on `(0, a]` for `a < 4`, and on `[a, 2a]` a concave parabola with
maximum at `x = 2a − 2`, value `a²/2 − 2a + 1` — the block exponent with the opposite sign.
For `a < 2 + √2` it is negative on `(0, 2a]`, and `h(x)/x ≤ −δ(a) < 0` uniformly (on `(0, a]`,
`−1 + a/4`; on `[a, 2a]`, `max h / (2a)`), so each term is at most `(2m² n^{−δ(a)} (1 + o(1)))^j`,
the `j = 0` term is `(n − 2m)_{2m}/(n)_{2m} ≤ 1`, and

```
1 ≤ R ≤ U ≤ 1 + O( log² n · n^{−δ(a)} ).
```

Paley–Zygmund: `P(X_s > 0) ≥ 1/R → 1`, and `X_s > 0` is a staircase, so by Lemma 1
**`pw(G(n, p)) ≤ n − (2 + √2 − ε) log_b n` with probability `1 − O(log² n · n^{−δ})`** for every
`ε > 0`. **The upper half of the equality.** For `a > 2 + √2`, the single term of `Λ` at
`a' = b' = (a − 1)L` is `exp((a²/2 − 2a + 1 − o(1)) L² ln b)`: the plain second moment is
dead there, as it must be, since there is no staircase to find.

**Measured** (`ratio_brackets.csv`, `s = round(aL)`): at `p = ½`, `ln Λ` is `−13.3, −3.6,
−0.61, −0.014, −0.002` at `a = 3` for `n = 10², 10³, 10⁴, 10⁶, 10⁷` (the ratio tends to `1`
from below in this bracket, because `Λ` keeps only the aligned placements); at `a = 3.5`
it is `4.8, 7.8, 17.6, 31.3, 28.0` (limit `3.8 → 46.9`, the discrete `T` and the rounding of
`s` still large); at `a = 3.9`, `29.6, 54.2, 95.4, 217.9, 298.2` against the limit
`24.6, 55.4, 98.5, 221.7, 301.7`. At `p = 0.3` the same picture (`a = 3.9`: `75.7 → 566.7`
against `47.9 → 586.3`). `U` is `e^{94}` to `e^{320}` at `a = 3` — the `(2m²)^j` and
`C(m, ·)²` factors are `e^{Θ(L log L)}` and overwhelm `e^{−Θ(L²)}` until `L ≫ log L`, i.e.
at no `n` one can write down; **the upper bracket proves the limit and measures
nothing**, and a sharper finite bound would need the overlap as a function of the actual
index sets and roles, a four-index-set sum not attempted here.

**On the repairs.** None applies: (i) typical staircases, (ii) Janson's inequality and
(iii) Talagrand all bound `P(X = 0)` from above, and above `2 + √2` that probability tends to
`1` by §2. Janson's inequality would give the same `δ(a)` with the exponent in place of the
polynomial — not needed.

## 4. The numbers beside the record

`reports/random_graph_middle.md` §4, `p = ½`, 20 proved graphs per cell
(`data_vs_floors.csv`; `L = log₂ n`):

| `n` | `L` | `pw` min / median / max | `n − pw` (median) | block `E ≥ 1` (`s`) | staircase `s₀` | `(2+√2)L` | `4L` | `2L` | 95% floor: empty pair / block |
|---|---|---|---|---|---|---|---|---|---|
| 30 | 4.91 | 16 / 19 / 20 | 11 | 12 | 15 | 16.7 | 19.6 | 9.8 | 18 / 18 |
| 40 | 5.32 | 26 / 28 / 29 | 12 | 13 | 17 | 18.2 | 21.3 | 10.6 | 26 / 26 |
| 50 | 5.64 | 36 / 37 / 38 | 13 | 14 | 19 | 19.3 | 22.6 | 11.3 | 34 / 35 |
| 60 | 5.91 | 45 / 46 / 47 | 14 | 15 | 21 | 20.2 | 23.6 | 11.8 | 44 / 44 |

Three readings. (i) The block's finite threshold — the least `s` at which some corner block
has expected count below one — is the measured median `n − pw` plus one at every `n`; the
staircase threshold overshoots by `4–7` and the limits `(2 + √2)L` and `4L` by `6–10`. At
`L ≈ 5–6` the `o(1)` of §2 is the size of the main term (the exponent `L² ln b` is `17–24`
and its `O(L)` corrections are of that order), so the finite count, not the constant, is
the predictor. (ii) As a 95% floor (`pw ≥ n − s + 1` where the block bound is `≤ 0.05`) the
block family adds one stack at `n = 50` and nothing elsewhere — the floor is the sharp
empty-pair inequality at these sizes, as the record said. (iii) `2L` is below every median
by `1–2`: the independence bound was never tight here, and the data were always
consistent with a constant above `2`; that it is `2 + √2` and not `4` is a statement about
`n → ∞` that the cells cannot see, and the finite block count is what they do see.

## 5. Literature

By a search agent (about 30 searches; `literature/MISSING.md`, "Dense random graphs: the
staircase constant (2026-11-11)"). **The constant `2 + √2` is in print for bandwidth**:
Kuang & McDiarmid (1985), *Ars Combinatoria* 20A, 29–36 (not online), stated by Erdős,
Hell & Winkler (1989, *Ann. Discrete Math.* 41, Theorem 3, read from the Rényi scan) as
`n − (2 + √2 + o(1)) lg n < bw(G(n, ½)) < n − (2 + √2 − o(1)) lg n`, "even the constant `c` is
determined by the result of Kuang and McDiarmid", stronger than Turner (1986) and
de la Vega (1983). The strict staircase is exactly `bw ≤ n − s` (§1), so their upper
bound with `pw ≤ bw` gives §3's half for free; their lower bound does not transfer (no
bandwidth lower bound bounds pathwidth), and §2 is the pathwidth version, through the
generalised staircase and the block. Füredi & West (2001) name the structure the
*halfgraph*. For pathwidth, treewidth or vertex separation of dense `G(n, p)` the record
is `n − O(√(n/p))` (Perarnau & Serra 2014, treedepth and treewidth) and nothing of the form
`n − c log n`; **we found no prior statement** of the pathwidth constant. The method is
Matula's (`α(G(n, p)) ≈ 2 log_b n` by first and second moment; Frieze & Karoński Thm 7.3)
and the densest-subgraph threshold of Erdős–Rényi (1960) and Bollobás (1981) (Frieze &
Karoński Thm 5.3), here applied to a pattern of forbidden edges; "in the manner of", not
an instance. Wanted: Kuang & McDiarmid 1985 (first), Erdős–Hell–Winkler 1989 (open scan),
Füredi–West 2001, de la Vega 1983, Bollobás 1981, Bollobás–Erdős 1976, Matula 1976.

## 6. Regenerate

```bash
# the tables: thresholds.csv (s0, the block threshold, the argmin block, (2+√2)L, 4L; n to 10^7, p = ½ and 0.3),
# data_vs_floors.csv (the dense cells against the floors), ratio_brackets.csv (Λ, U at s = round(aL))
nice -n 19 python -m learning.staircase_moment              # 8 s
# the lemma on every labelled graph to n = 6 and samples at 7 (lemma_check.log, 30 s); the bandwidth form (bandwidth_check.log)
nice -n 19 python -c "from learning.staircase_moment import *; print(check_lemma(6))"
nice -n 19 python -c "from learning.staircase_moment import *; print(check_bandwidth_lemma(5))"
# tests (751; the lemma to n = 5, the moments against every labelled graph to n = 6, the brackets, the exponents)
nice -n 19 python -m pytest tests/test_staircase_moment.py -q
# Lean: build and axiom audit
cd lean && taskset -c 0-7 nice -n 19 lake build MOSPFormalization.Staircase
cd lean && lake env lean ../reports/scratch/dense_staircase/axioms.lean   # axioms.log: three standard axioms, no sorry
```

## 7. Lean

`lean/MOSPFormalization/Staircase.lean`, namespace `MOSPFormalization.Staircase`,
registered in `MOSPFormalization.lean`; 15 theorems and 4 `decide` examples, no `sorry`,
axioms `propext`, `Classical.choice`, `Quot.sound` on each of the ten audited
(`axioms.log`).

| statement | Lean | status |
|---|---|---|
| a layout with any injective ordered prefix | `exists_layout_prefix` | proved |
| generalised staircase ⇒ `vs(σ) ≤ n − s` at the prefix layout | `vertexSepAt_le_of_isGenStaircase` | proved |
| generalised staircase ⇒ `pw ≤ n − s`; staircase ⇒ `pw ≤ n − s` | `pathwidth_le_of_isGenStaircase`, `pathwidth_le_of_isStaircase` | proved |
| greedy selection, `|C_i| ≥ i + 1` | `exists_injOn_mem` | proved |
| `pw ≤ n − s` ⇒ generalised staircase; the equivalence | `exists_isGenStaircase_of_pathwidth_le`, `pathwidth_le_iff_exists_isGenStaircase` | proved |
| the block's forced pairs are `c(s, a, b)` distinct non-diagonal pairs | `forcedSet_card` | proved |
| the weight of a forced set is `(1 − p)^|F|` | `sum_gnpWeight_patternGraphs_univ`, `sum_gnpWeight_univ_eq_one` | proved |
| **Theorem B⁺**, `P(pw ≤ n − s) ≤ n^{a+b}(1 − p)^{c}` | `weightedSum_graphsOfPathwidthLe_le_block`, `weightedSum_pathwidth_le_block` | proved |
| the upper half `n − pw ≥ (2 + √2 − ε) L` whp | `StaircaseUpperTail` | stated as a `Prop`; §3 on paper |
| the asymptotic optimisation, `a = b = ⌊(1 + √2) L⌋` | — | on paper (§2) |
| the strict staircase is `bw ≤ n − s` | — | brute force (§1); Mathlib has no bandwidth |

## 8. What remains

1. `StaircaseUpperTail` in Lean: the bracket `U` as a finite sum (the grouping by `(a', b')`
   and the prefix bound on the overlap are both finite combinatorics) and its limit; a
   day, not a session.
2. The asymptotic form of Theorem B⁺ in Lean, in the style of `FirstMomentAsymptotics`:
   `n^{2yL} q^{c}` with `y = ⌊(1 + √2)L⌋/L` below `exp(−κ ε ln² n)`.
3. A finite upper bracket on `R` that measures: the overlap as a function of the index sets
   and roles. Only worth it if someone wants the second-moment constant at finite `n`;
   the block count already predicts the data to one stack.
4. The paper: Appendix E's "dense sandwich `[2, 4]`" and Theorem B's "`4`" become
   `2 + √2`, with Kuang & McDiarmid cited for the bandwidth constant and the pathwidth
   equality as ours (lower half new, upper half theirs through `pw ≤ bw` or §3). Not
   applied here.
