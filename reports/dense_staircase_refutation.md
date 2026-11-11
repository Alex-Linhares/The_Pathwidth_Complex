# Dense staircases and `2 + √2`: the refuter's report

*2026-11-11, one session, by a refuter agent on `reports/dense_staircase.md` (the prover's
report), `lean/MOSPFormalization/Staircase.lean` and `learning/staircase_moment.py`. The
prover's files are untouched. My own code shares nothing with the prover's:
`reports/scratch/dense_staircase_refutation/own_check.py` (the lemma, the block bound and
the second-moment identity by brute force, with the repository's subset DP
`fixed_parameter_algorithm/pathwidth.py` as the pathwidth oracle, itself checked against
the definition on every graph to `n = 5`) and `own_numerics.py` (the thresholds, the
exponents and the bracket sums); logs beside them. No solver run; nothing downloaded into
`literature/` (the Erdős–Hell–Winkler scan was read from the Rényi Institute's open copy,
Turner 1986 from the copy already held under `reports/scratch/first_moment/lit/`).*

## 0. Verdict: CONFIRMED

Throughout `p ∈ (0, 1)` is fixed, `q = 1 − p`, `b = 1/q`, `L = log_b n`, and "whp" means
with probability `→ 1`. The claim that goes into the paper is

```
n − pw(G(n, p)) = (2 + √2 + o(1)) · log_b n      whp,
```

and it stands. The two halves, stated in terms of `n − pw` (the prover's §2 calls the
first "the lower half" and the second "the upper half", meaning the halves of a bound on
`pw`; the brief uses the opposite names; the mathematics is the same):

- **`n − pw ≤ (2 + √2 + ε) L` whp, for every `ε > 0`** — equivalently
  `pw ≥ n − (2 + √2 + ε) L`. The finite inequality
  `P(pw(G(n, p)) ≤ n − s) ≤ n^{a+b} (1 − p)^{c(s, a, b)}` for `1 ≤ s ≤ n`, `a, b ≤ s − 1` is
  **Lean** (`weightedSum_pathwidth_le_block`, no `sorry`, axioms `propext`,
  `Classical.choice`, `Quot.sound`; re-audited here from the built oleans, which `lake
  build` confirms are current). The asymptotic step — put `s = aL`, `a' = b' = (a − 1)L`,
  read off the exponent `−(a²/2 − 2a + 1) L² ln b` — is on paper; I re-derived it from
  scratch (§2) and reproduced the threshold numerics with my own code. The same finite
  inequality, with `bw ≥ pw`, is Kuang & McDiarmid's lower bound for bandwidth at every
  fixed `p`.
- **`n − pw ≥ (2 + √2 − ε) L` whp, for every `ε > 0`** — equivalently
  `pw ≤ n − (2 + √2 − ε) L`. **On paper**, by the second moment on strict staircases (the
  prover's §3); I checked the argument at the level the brief asked for (the overlap
  bound, the role of shared vertices, the falling factorials, the exponent and its
  uniform negativity; §3) and found no gap. **Citable at `p = ½`**: Kuang & McDiarmid
  (1985), stated as Theorem 3 of Erdős, Hell & Winkler (1989) and read here verbatim from
  the scan, give `bw(G(n, ½)) < n − (2 + √2 − o(1)) lg n` whp, and a layout of bandwidth
  `≤ n − s` is a strict staircase of size `s` (`2s − 2 ≤ n`), which is a layout of
  pathwidth `≤ n − s` (`pathwidth_le_of_isStaircase`, Lean); or simply `pw ≤ bw`
  (`Sandwich.lean`, `pathwidth_le_bandwidth`). For general `p` the only statement in
  print that we have read is at `p = ½`; EHW say the results "are easily generalized"
  and that their Theorem 3 is "weaker than the most general version of [13]", but the
  general-`p` form is not quoted anywhere we have seen, so at `p ≠ ½` this half rests on
  the prover's §3 (or on a K–M statement no one here has read). In Lean it is the `Prop`
  `StaircaseUpperTail p`, stated and not proved — as the prover says.

So: lemma in Lean both ways; `n − pw ≤ (2 + √2 + ε) L` in Lean up to a page of
calculus; `n − pw ≥ (2 + √2 − ε) L` on paper for every `p`, and cited for `p = ½`. The
record's bracket `[2, 4]` for the dense regime becomes the equality `2 + √2`; Theorem B's
`4` was the method's constant (the `y = a/2` slice of the block family), not the graphs'.

**Nothing was found wrong.** What I found that the paper should state precisely, none of
it an error in a theorem:

1. §4 of the prover's report uses the *symmetric* block count (full rows and columns
   unordered; `symmetric=True`, the Python default, not in Lean) for "the block's
   `E ≥ 1` threshold `12, 13, 14, 15`", while §2 and `thresholds.csv` use the *ordered*
   count (`n^{a+b}`, the Lean form) for "`s_block/L = 3.26–3.39` at `n = 30–60`"
   (`s = 16, 17, 19, 20`). Both are legitimate union bounds and I reproduce both to the
   integer, but §4 does not say which it uses, and its prose "the least `s` at which some
   corner block has expected count below one" describes `13, 14, 15, 16`; the column
   (and "median + 1") is the *largest* `s` with count `≥ 1`. Wording, off by one.
2. The §4 comparison "measured median `n − pw` + 1 = block threshold" is a finite-`n`
   coincidence of the symmetric count, which at `L ≈ 5–6` sits at `2.45–2.54 L` and
   climbs to `3.18 L` only by `n = 10⁷`; it is not evidence for the constant. The sign is
   right (§4 below), and a better finite-`n` witness of the constant is the ratio
   `(n − pw)/α(G) = 1.71–1.77` on the four cells against `(2 + √2)/2 = 1.707`.
3. EHW's running head says `117–130` and 1989; Crossref (`10.1016/S0167-5060(08)70455-2`)
   and zbMATH say `117–129`, Crossref dating the volume 1988 — cite `117–129, 1989` as
   `literature/MISSING.md` does, and know that both pairs are in print; Kuang &
   McDiarmid's title is "On the bandwidth of a random graph"
   (McDiarmid & Miller 1991 cite it so), not EHW's pre-publication "Probabilistic
   analysis of bandwidth problems"; first page 29 confirmed, last page 36 only through
   the zbMATH record `MISSING.md` quotes (zbMATH refused my fetch).

## 1. The lemma

**Statement checked.** `pw(G) ≤ n − s` iff `G` has a generalised staircase of size `s`:
injective `v_1 … v_{s−1}`, `u_1 … u_{s−1}` with `u_i ∉ {v_1 … v_{s−i}}` and `u_i ≁ v_j` for
`j ≤ s − i`.

**My derivation, from `VertexSeparation.lean`'s definition.** At position `i` the prefix
is `{x : σx ≤ i}` (size `i + 1`), the active suffix is the set of suffix vertices with a
prefix neighbour, `vs(σ) = max_i |active_i|`, `pw = min_σ vs(σ)`
(`vertexSeparation_eq_pathwidth`). Write `t = i + 1` for the prefix size and
`C_t = V ∖ N[prefix_t]` for the inactive suffix (no prefix neighbour and not in the
prefix). Then `|active_t| ≤ n − s` iff `|C_t| ≥ s − t`, since `|active_t| + |C_t| = n − t`.

- (⇐) Lay `v_1 … v_{s−1}` first in that order, the rest after. For `t ≤ s − 1` the vertices
  `u_1 … u_{s−t}` are distinct, lie outside `{v_1 … v_t}` (because `i ≤ s − t` gives
  `t ≤ s − i`, so `u_i ≠ v_j` for all `j ≤ t`) and have no neighbour among `v_1 … v_t`
  (same inequality); so `|C_t| ≥ s − t`. For `t ≥ s` the suffix itself has `n − t ≤ n − s`
  vertices. Hence `vs(σ) ≤ n − s`.
- (⇒) Take an optimal layout, `v_j := σ^{-1}(j)`, and at prefix size `t = s − i` the set
  `C_{s−i}` has `≥ i` elements. The sets `C_1 ⊆ C_2 ⊆ …` are nested, but one does not
  need that: pick `u_i ∈ C_{s−i} ∖ {u_1 … u_{i−1}}`, possible since `|C_{s−i}| ≥ i`.
  Then `u_i` is outside the prefix `{v_1 … v_{s−i}}` and non-adjacent to it. ∎

Both directions are elementary; the "Hall" question the prover mentions never arises
(the greedy choice from sets of size `≥ i` is all that is needed, and `exists_injOn_mem`
in Lean is exactly that).

**Brute force, my own code.** `own_check.py lemma`: every labelled graph on `n ≤ 6`
vertices (`32,768` at six), every `s ∈ [1, n]`, staircase existence by backtracking over
ordered `v` with the `u`'s found by augmenting-path matching (not by the nested-set
shortcut), against `compute_pathwidth` of the repository's subset DP: **zero violations**
of either direction; the DP agrees with the definition (minimum over all `n!` layouts of
the maximum active suffix) on every graph to `n = 5`. Random graphs at `n = 7` (60, at
`p ∈ {0.3, 0.5, 0.7}`) and `n = 8` (25): **zero violations**. The strict form against
brute-force bandwidth, `2s − 2 ≤ n`, every graph to `n = 5`: zero violations.

**The Lean statement.** `IsGenStaircase G m v u` with `m = s − 1`, `v u : Fin m → V`,
0-indexed `i, j`, condition `i + j < m` on both `ne` and `not_adj`. In 1-indexed terms
`i' = i + 1`, `j' = j + 1`: `i + j < m ⟺ i' + j' ≤ s ⟺ j' ≤ s − i'`, so `u_{i'}` avoids and
is non-adjacent to `v_1 … v_{s−i'}` — **exactly the statement, no off-by-one**.
`pathwidth_le_iff_exists_isGenStaircase` is `pathwidth G ≤ card V − s ↔ ∃ v u : Fin (s−1)
→ V, IsGenStaircase G (s−1) v u` under `1 ≤ s ≤ card V`, with `−` the natural
subtraction, harmless under `s ≤ n`. At the ends: `s = 1` gives empty sequences and
`pw ≤ n − 1`, both true; `s = n` forces `u_1` isolated and then `u_k = v_{n−k+1}` non-
adjacent to `v_1 … v_{n−k}`, i.e. the edgeless graph, which is `pw ≤ 0`. The axiom audit
(`reports/scratch/dense_staircase/axioms.lean`, rerun here from the built oleans): the
three standard axioms on all ten audited theorems; `lake build MOSPFormalization.Staircase`
reports nothing to rebuild.

**Verdict on item 1: confirmed.**

## 2. The block first moment

**`c(s, a, b)`.** The forced non-edges of the block `v_1 … v_a`, `u_1 … u_b` are the pairs
`{u_i, v_j}` with `i ≤ b`, `j ≤ min(a, s − i)`; their number is
`c = Σ_{i=1}^{b} min(a, s − i)`, which is `ab` when `a + b ≤ s` and
`ab − d(d + 1)/2`, `d = a + b − s`, otherwise (the `i > s − a` rows lose `a − (s − i)` each,
summing to `1 + 2 + … + d`). Checked against the sum on every `(s, a, b)` with `s < 40`:
no mismatch. The Lean `blockCost s a b = #{(i, j) ∈ Fin b × Fin a : i + j + 1 < s}` is this
in 0-indexed form (`i + j + 1 < s ⟺ i' + j' ≤ s`); its four `decide` examples
`(7,4,4) = 15, (5,4,2) = 7, (6,5,5) = 15, (3,1,1) = 1` agree with my sum.

**Distinctness.** `forcedSet_card` says the map `(i, j) ↦ {u_i, v_j}` is injective on the
index set and no pair is diagonal. The only way two forced pairs could coincide as sets
with `u_i = v_{j'}`, `u_{i'} = v_j` (a `u` equal to a later `v`) needs `i + j' ≥ s` and
`i' + j ≥ s` by the `ne` clause, while `i + j ≤ s − 1` and `i' + j' ≤ s − 1` (0-indexed
`< m`): adding, `i + i' + j + j' ≥ 2s` and `≤ 2s − 2`. Contradiction — the Lean proof
is exactly this `omega`. So the union bound counts `c` *distinct* non-edges even on the
generalised staircase, which is what carries the bandwidth argument over to pathwidth.

**The inequality at small `n`, exact.** `own_check.py lemma` also tabulates every graph
on `n ≤ 6` vertices by `(edge count, pathwidth)` and evaluates
`P(pw ≤ n − s) = Σ p^e q^{N−e}` in rationals against `n^{a+b} q^{c(s,a,b)}` for every
`s ∈ [1, n]`, every `0 ≤ a, b ≤ s − 1`, at `p ∈ {½, ⅓, ⅔, 1/10, 9/10}`: **zero violations**.

**The optimisation, from scratch.** `s = aL`, `a' = b' = yL`. If `2y ≤ a` then `c = y²L²`.
If `2y > a`: the first `(a − y)L` rows contribute `yL` each and the rest contribute
`s − i`, so `c = y(a − y)L² + Σ_{k=(a−y)L}^{yL−1} k = L²[y(a − y) + (y² − (a − y)²)/2] + O(L)
= L²[2ay − y² − a²/2] + O(L)`; the prover's `y²L² − (2y − a)²L²/2` is the same
polynomial. The term is `exp((a' + b') ln n + c ln q)`, and `ln n = L ln b`, `ln q = −ln b`,
so the exponent is `L² ln b · [2y − 2ay + y² + a²/2] + O(L)`, which is the prover's
`g_a(y) = 2y − y² + (2y − a)²/2` expanded. On `2y ≤ a` the exponent is `2y − y² > 0`
for `y < 2`, so no block with `a' + b' ≤ s` can ever give a decaying bound below `a = 4`
— the empty pair of Theorem B is `y = a/2`, zero exactly at `a = 4`. On `2y > a`,
`g' = 2 + 2y − 2a = 0` at `y = a − 1` (inside the range iff `a > 2`), and
`g_a(a − 1) = 2(a − 1) + (a − 1)² − 2a(a − 1) + a²/2 = −(a − 1)² + a²/2 = −(a²/2 − 2a + 1)`,
negative iff `a² − 4a + 2 > 0` iff `a > 2 + √2` (the other root `2 − √2` is below 2). The
derivative of `a²/2 − 2a + 1` at `2 + √2` is `√2`, so at `a = 2 + √2 + ε` the bound is
`exp(−(√2 ε − O(ε²) − o(1)) L² ln b)`. Numerically (`own_numerics.py exponent`): the
grid minimum of `g_a` is at `y = a − 1` with value `−(a²/2 − 2a + 1)` for `a = 3.5, 4`,
and `g_a > 0` on `(0, a]` for `a = 3, 3.3, 3.414`; the exact exponent
`[2 ln(n)_{yL} + c ln q] / (L² ln b)` at `n = 10⁷` is within `0.02–0.05` of `g_a(y)`, at
`n = 10³⁰⁰` within `0.0003` — the `O(L)` term is `O(1/L)` of the main term.

**Threshold numerics, my own code** (`thresholds.log`; the least `s` whose best ordered
block bound is below 1; the prover tabulates the largest `s` with bound `≥ 1`, one less):

| `p` | `n` | `L` | least `s` with bound `< 1` | `s/L` | argmin `a' = b'`, `/L` |
|---|---|---|---|---|---|
| ½ | 10³ | 9.97 | 35 | 3.512 | 25, 2.51 |
| ½ | 10⁴ | 13.29 | 46 | 3.462 | 32, 2.41 |
| ½ | 10⁵ | 16.61 | 58 | 3.492 | 41, 2.47 |
| ½ | 10⁶ | 19.93 | 69 | 3.462 | 49, 2.46 |
| ½ | 10⁷ | 23.25 | 80 | 3.440 | 56, 2.41 |
| 0.3 | 10⁴ … 10⁷ | 25.8 … 45.2 | 89 … 155 | 3.447 … 3.430 | 2.41–2.44 |

Subtracting one gives the prover's `34, 45, 57, 68, 79` and `3.397–3.432` exactly; the
argmin block is square at `(1 + √2) L = 2.414 L` as the calculus says. At `n = 30–60`:
`17, 18, 20, 21` (prover: `16, 17, 19, 20`). Reproduced.

**Verdict on item 2: confirmed.** `n − pw ≤ (2 + √2 + ε) L` whp, with the finite
inequality in Lean and the calculus on paper, re-derived here.

## 3. The other half: Kuang–McDiarmid, and the second moment

**What is in print.** Erdős, Hell & Winkler, "Bandwidth versus bandsize", *Annals of
Discrete Mathematics* 41 (1989) 117–129 (the volume *Graph Theory in Memory of G. A.
Dirac*; the running head prints 117–130), read from the Rényi scan, p. 125: "For simplicity we concentrate below on the
case `p = ½`; the results are easily generalized. […] The following theorem is proved in
[13]. **Theorem 3.** With probability approaching 1 as `n → ∞`,
`n − (2 + √2 + o(1)) · lg n < bw(G_n) < n − (2 + √2 − o(1)) · lg n`." Then: "Theorem 3 is
stronger than similar results in [20, 21] [Turner 1983, de la Vega 1983], and weaker than
the most general version of [13]. We have stated it in this way for simplicity, and also
because this was the form of the result we had before discovering [13]; we had the
constant `2 + √2` in the lower bound, but not in the upper bound." And p. 127: "We have
determined that the 'correct' value of bandwidth of `G_n` is `n − c log n`; in fact even
the constant `c` is determined by the result of Kuang and McDiarmid, as stated in Theorem
3." Reference [13] is "Y. Kuang and C. J. H. McDiarmid, Probabilistic analysis of
bandwidth problems, Proc. British Combinatorial Conference 1985. To appear." The
published form is Y. Kuang and C. McDiarmid, "On the bandwidth of a random graph", *Ars
Combinatoria* 20A (1985), 29– (first page from the reference list of McDiarmid & Miller,
"Lattice bandwidth of random graphs", *Discrete Applied Mathematics* 30 (1991), via
Crossref; last page 36 per the zbMATH record quoted in `literature/MISSING.md`, which I
could not reach). So: **two-sided, `p = ½`, base 2**, with the general-`p` form asserted
to exist but not displayed. Nobody here has read K–M itself.

**What transfers.** A layout of bandwidth `≤ n − s` with `2s − 2 ≤ n` has its first `s − 1`
and last `s − 1` vertices forming a strict staircase (checked by brute force, §1), and a
strict staircase is a generalised one, so `pathwidth_le_of_isStaircase` gives
`pw ≤ n − s`; or use `pw ≤ bw` directly (`Sandwich.lean`). Hence at `p = ½`,
**`n − pw ≥ (2 + √2 − o(1)) log₂ n` whp is a corollary of K–M's upper bound and can be
cited.** The other direction does not transfer (a bandwidth *lower* bound says nothing
about pathwidth), which is why the block first moment of §2 is needed and is new for
pathwidth. At general `p`, the citation would be to a statement we have not seen; the
honest sentence is "stated for `p = ½` by EHW, who say it generalises".

**The second moment on paper (the prover's §3), checked.** `X = X_s` counts ordered
strict staircases; `E[X] = (n)_{2m} q^{m(m+1)/2}`, `m = s − 1` — exact, confirmed by my
brute force over every labelled graph at `n ≤ 6` for `(n, s) ∈ {(4,2), (5,2), (5,3), (6,2),
(6,3), (6,4)}` at `p = ½, ⅓` (rational equality). The identity
`R = E[X²]/E[X]² = E_{S'}[b^{|F(S') ∩ F(S₀)|}]` over a uniform placement `S'` against a
fixed `S₀`: confirmed exactly on the same cases (`moment.log`). The brief's three
suspects:

- *Shared vertices in different roles* (a `v` of `S'` equal to a `u` of `S₀`): the bound
  `|F(S') ∩ F(S₀)| ≤ #{S₀-forced pairs inside the shared set}` uses only *which*
  `S₀`-vertices `S'` contains, never their roles in `S'`; every pair of the intersection
  is an `S₀`-forced pair with both ends shared. No case is missing. The count of `S'`
  with `a'` shared `v`'s and `b'` shared `u`'s, `C(m, a') C(m, b') (2m)_{a'+b'} (n − 2m)_{2m−a'−b'}`,
  sums to `(n)_{2m}` over `(a', b')` (choose the shared set, their slots, fill the rest).
- *Shared non-edges counted twice*: `|F ∪ F'| = |F| + |F'| − |F ∩ F'|` is a set identity,
  and `q^{|F ∪ F'|}` is the right weight because the forced pairs are distinct non-
  diagonal pairs and the edge indicators are independent.
- *`(n)_{2s−2}` against `n^{2s−2}`*: the exact `E[X]` has the falling factorial; the
  bound `(n − 2m)_{2m−j}/(n)_{2m} ≤ 1/(n)_j ≤ (n − 2m)^{−j}` follows from
  `(n)_{2m} = (n)_j (n − j)_{2m−j} ≥ (n)_j (n − 2m)_{2m−j}`.
- *Prefix index sets maximise the overlap*: `#{(i ∈ J, j ∈ I) : i + j ≤ s} ≤ c(s, |I|, |J|)`
  — checked on every pair of index sets for `s ≤ 8` (`21,844` pairs, zero violations).

The exponent: with `j = xL` shared vertices, `c ≤ j²/4` for `j ≤ s` and
`≤ j²/4 − (j − s)²/2` for `j ≥ s` (`a'b' ≤ j²/4`; `d(d + 1)/2 ≥ d²/2`), so the term is at
most `(2m²/(n − 2m))^j b^c = exp(L² ln b · h(x) + j · O(log L))`,
`h(x) = −x + x²/4 − (x − a)²/2 · 1[x > a]`. My grid: `h` has its maximum at `x = 2a − 2`
with value `a²/2 − 2a + 1` for `a = 3.5, 3.9` and is negative on `(0, 2a]` for
`a = 3, 3.3, 3.414`; `h(x)/x ≤ −δ(a) < 0` uniformly for `a < 2 + √2` (on `(0, a]`,
`−1 + a/4`; on `[a, 2a]`, `max h / 2a`). Each term is then `≤ (2m² n^{−δ} (1 + o(1)))^j`,
the `j = 0` term is `≤ 1`, there are `≤ m + 1` pairs per `j`, so
`1 ≤ R ≤ 1 + O(log² n · n^{−δ})` and Paley–Zygmund gives `P(X > 0) ≥ 1/R → 1`. **The
argument is correct.** Its constant is the block's with the opposite sign, which is the
right shape: the dangerous overlap is the corner block, in the middle of the staircase,
exactly where the first moment is tightest.

**The finite sums, my own implementation** (`ratio.log`; `U` and `Λ` as the prover
defines them, `p = ½`, `s = round(aL)`):

| `n` | `L` | `a` | `s` | `ln U` | `ln Λ` | `(a²/2 − 2a + 1) L² ln 2` |
|---|---|---|---|---|---|---|
| 10⁷ | 23.3 | 3.0 | 70 | +320.0 | −0.002 | −187 |
| 10⁷ | 23.3 | 3.3 | 77 | +522.4 | −0.002 | −58 |
| 10⁷ | 23.3 | 3.5 | 81 | +653.8 | +28.0 | +47 |
| 10⁷ | 23.3 | 3.9 | 91 | +1,031.9 | +298.2 | +302 |
| 10³⁰ | 99.7 | 3.0 | 299 | 0.000 | 0.000 | −3,442 |
| 10³⁰ | 99.7 | 3.3 | 329 | +2,074.4 | 0.000 | −1,067 |
| 10³⁰ | 99.7 | 3.5 | 349 | +4,277.4 | +831.5 | +861 |
| 10³⁰ | 99.7 | 3.9 | 389 | +9,519.6 | +5,522.3 | +5,542 |
| 10¹⁰⁰ | 332.2 | 3.0 | 997 | 0.000 | 0.000 | −38,245 |
| 10¹⁰⁰ | 332.2 | 3.3 | 1,096 | +316.2 | 0.000 | −11,856 |
| 10¹⁰⁰ | 332.2 | 3.5 | 1,163 | +22,973.4 | +9,503.2 | +9,561 |
| 10¹⁰⁰ | 332.2 | 3.9 | 1,296 | +77,182.3 | +61,554.2 | +61,575 |

Read honestly: **at every writable `n` the upper bracket `U` is large and positive even
below `2 + √2`** — `ln U = 320` and `522` at `n = 10⁷` for `a = 3.0` and `3.3`, still
`2,074` at `n = 10³⁰` for `a = 3.3` — so "`U → 1` for `a < 2 + √2`" is the limit and not
what the table shows at any `n` one could sample. Only the rows `(10³⁰, 3.0)`,
`(10¹⁰⁰, 3.0)` show the limit reached (`ln U = 0.000`, i.e. `R = 1` to the printed
precision); the row `(10¹⁰⁰, 3.3)` shows it on the way (`316` against `522` at `10⁷`,
falling as `L²` overtakes `L log L`); every other row below `2 + √2` shows the
`e^{Θ(L log L)}` slack of the `C(m, ·)² (2m)_j` factors, exactly as the prover's §3
says of its own bracket. Above `2 + √2` the lower bracket `Λ` tracks the predicted
exponent `(a²/2 − 2a + 1) L² ln 2` to within `0.1–1%` at `10³⁰` and `10¹⁰⁰` (the
prover's `298` at `10⁷`, `a = 3.9` reproduced to the decimal), and below it `Λ → 1`
from below, as it must (it keeps only the aligned placements). My prefactor estimate
`(2m²)^j` before running this put the crossover for `a = 3.0` above `10³⁰`; the actual
sum crosses before `10³⁰`, so the crude bound in the proof is looser than the sum it
bounds — in the safe direction. At `n ≤ 6` my `U` and `Λ` bracket the exact ratio
(`Λ = 0.089 ≤ R = 1.694 ≤ U = 3.33` at `n = 6`, `s = 3`, `p = ½`, the prover's three
numbers; `ratio_small_n.log`).

So the finite sums behave as the proof says: `Λ` grows like
`exp((a²/2 − 2a + 1) L² ln 2)` for `a > 2 + √2`, and `U` reaches `1` for `a < 2 + √2`
only once `L² ln b` dominates the `Θ(L log L)` slack — at `10³⁰` for `a = 3.0`, beyond
`10¹⁰⁰` for `a = 3.3`, and at no `n` anyone can sample. The bracket proves the limit;
it measures nothing at feasible `n`, which the prover's report also says.

**Verdict on item 3: confirmed.** The lower half of `n − pw` (upper half of `pw`) can be
*cited* at `p = ½` and is *proved on paper* for every `p`; the Lean `Prop`
`StaircaseUpperTail` is the honest status.

## 4. Consistency with the record

- **Theorem B** (`n − pw ≤ (4 + ε) L` whp) is implied, since `2 + √2 < 4`; indeed the
  empty pair `(t, t − 1)` is the block `(a', b') = (a/2 · L, a/2 · L)` and the block
  family's minimum over `(a', b')` is at most its value there.
- **Frieze's independence number** (`n − pw ≥ α = (2 − o(1)) L`) is implied by the other
  half, since `2 < 2 + √2`; the two lower ends do not conflict.
- **Turner (1986)**, *SIAM J. Comput.* 15(2), 561–580, read from the held copy: he
  defines `λ_n(c) = −ln n / ln c = log_{1/c} n` and his **Theorem 2.1** is "Let `0 < p < 1`
  be fixed. For almost all `G ∈ Γ_n(p)`, `φ(G) > n − 4 λ(1 − p)`", i.e.
  `bw > n − 4 log_{1/(1−p)} n` whp, proved from Lemma 2.1 (`bw ≤ n − 2k` forces an
  empty pair of two `k`-sets) with the count `(en/k)^{2k}` — a *lower* bound on bandwidth
  only. Kuang–McDiarmid's lower half `bw ≥ n − (2 + √2 + o(1)) L` is **stronger** than
  Turner's (`2 + √2 < 4`, and a larger subtracted term is a weaker bound), and K–M add
  the matching upper bound; EHW say so ("stronger than similar results in [20, 21]").
  Our block first moment gives `pw ≥ n − (2 + √2 + ε) L`, hence `bw ≥` the same: it
  implies Turner and reproduces K–M's lower half at every fixed `p` — which the paper's
  current sentence "our dense statement implies his and not conversely" should now say
  of K–M's lower half too. Consistent throughout.
- **The dense cells** (`reports/random_graph_middle.md` §4, `p = ½`, 20 proved graphs
  each): median `pw = 19, 28, 37, 46`, so `n − pw = 11, 12, 13, 14` at `n = 30, 40, 50, 60`,
  against `(2 + √2) L = 16.7, 18.2, 19.3, 20.2`. The measured values are **below** the
  asymptotic line, and that is the right sign: the first-moment half says only that
  `n − pw` is *at most* about `(2 + √2) L`, and every finite threshold of that family is
  an upper bound on where staircases can live, so the data must sit at or below it — the
  ordered-count threshold is `17, 18, 20, 21` here, the symmetric-count one `13, 14, 15,
  16` (the prover's `12, 13, 14, 15` is "largest `s` with count `≥ 1`"), both above the
  data. The other half is asymptotic with error `O(log² n · n^{−δ})`, and at `L ≈ 5–6`
  the `o(1)` is not small: the exponent is `L² ln 2 ≈ 17–24` and its `O(L log L)`
  corrections (the `(L!)²` of the symmetric count alone is `e^{9.6}` at `L = 5`) are of
  the same size, which is why the symmetric threshold reads `2.45–2.54 L` here and
  only `3.18 L` at `n = 10⁷` (my `thresholds.log`), converging to `3.41` from below.
  The cleanest finite-`n` check of the *constant* is a ratio in which the `1/L`
  corrections largely cancel: on the same cells the realised `α(G)` (from the record's
  `n − α` column) is `6.3, 7.0, 7.5, 7.9`, and `(n − pw)/α = 1.75, 1.71, 1.73, 1.77`
  against the asymptotic `(2 + √2)/2 = 1.707` — while `(n − pw)/L = 2.24–2.37` and
  `α/L = 1.28–1.34` are both far from their limits `3.41` and `2`. Consistent, and the
  data were never consistent with `4` or with `2` as the constant.
- **Theorem B's `4` is a method constant, as the paper already says of `4 ln 2`**; the
  same sentence structure applies here.

## 5. Edits Appendix E would need (`paper1/latex/sec9e_appendix_random.tex`)

Proposed, not applied (the prover's files and the paper are untouched by this report):

1. **Lines 164–166** ("the dense bound of this appendix, `n − (4 + ε) log_{1/(1−p)} n`
   … gives `4 log_{1/(1−p)} n + O(1)` with no `ε`, on paper"): replace `4` by `2 + √2`
   and cite the staircase: "the dense bound of this appendix,
   `n − (2 + √2 + ε) log_{1/(1−p)} n` (the corner-block first moment, Lean), which is
   sharp: `n − pw = (2 + √2 + o(1)) log_{1/(1−p)} n` whp, the other half by a second
   moment on staircases and, at `p = ½`, by Kuang and McDiarmid's bandwidth theorem with
   `pw ≤ bw`." Drop or restate the "`4 log n + O(1)` with no `ε`" clause, which is now
   dominated.
2. **Lines 169–170** ("`n − pw` lies between `2n ln c/c` and `4n ln c/c` throughout, the
   same bracket as in the dense case"): the middle regime keeps `[2, 4]` (nothing here
   touches it); change the comparison to "the bracket `[2, 4]` whose dense-regime
   counterpart closes at `2 + √2`".
3. **Line 219** ("coefficient `1` against the `[2, 4]` of the independence number and
   Theorem B"): "against `2 + √2`" (the random ordering's `1` is still below it).
4. **Lines 672–676** (Turner): keep "Turner used the same empty pair … bandwidth at least
   `n − 4 log_{1/(1−p)} n`"; replace "our dense statement implies his and not
   conversely" by "our dense statement, `pw ≥ n − (2 + √2 + ε) log_{1/(1−p)} n`, implies
   his and reproduces the lower half of Kuang and McDiarmid's two-sided
   `bw(G(n, ½)) = n − (2 + √2 + o(1)) log₂ n` [EHW Theorem 3] at every fixed `p`; the
   constant is the same because the extremal structure — a staircase, Füredi and West's
   halfgraph — is the same for both parameters, and the bandwidth upper half with
   `pw ≤ bw` gives the pathwidth one at `p = ½`."
5. **Wherever Theorem B is displayed as a theorem** (the dense form is referred to at
   164 and 219 and 672 but, as far as I can find, is not a numbered theorem in the
   appendix; `reports/random_graph_first_moment.md` and `random_graph_middle.md` carry
   it): add the staircase statement as its sharp form, with the Lean name
   `weightedSum_pathwidth_le_block` in the Appendix A table and `StaircaseUpperTail`
   marked "stated, not proved".
6. **A sentence on what is cited vs proved**: "The constant `2 + √2` is Kuang and
   McDiarmid's for bandwidth; for pathwidth we found no prior statement."

**`refs.bib` entries** (exact data as established above; `Turner1986` already exists and
is correct):

```bibtex
@article{KuangMcDiarmid1985,
  author  = {Kuang, Yi and McDiarmid, Colin},
  title   = {On the bandwidth of a random graph},
  journal = {Ars Combinatoria},
  volume  = {20A}, pages = {29--36}, year = {1985},
  note    = {Proceedings of the Tenth British Combinatorial Conference, Glasgow, 1985;
             cited by Erd{\H o}s, Hell and Winkler (1989) as ``Probabilistic analysis of
             bandwidth problems'', to appear}
}

@incollection{ErdosHellWinkler1989,
  author    = {Erd{\H o}s, Paul and Hell, Pavol and Winkler, Peter},
  title     = {Bandwidth versus bandsize},
  booktitle = {Graph Theory in Memory of {G. A. Dirac}},
  series    = {Annals of Discrete Mathematics},
  volume    = {41}, pages = {117--129}, year = {1989},
  publisher = {North-Holland}, address = {Amsterdam},
  editor    = {Andersen, L. D. and Jakobsen, I. T. and Thomassen, C. and Toft, B. and Vestergaard, P. D.},
  doi       = {10.1016/S0167-5060(08)70455-2}
}
```

The DOI, pages and authors of the EHW entry are from Crossref (which dates the volume
1988; the printed chapter says 1989). The first name "Yi" for Kuang and the editor list
are from memory, not from a page I could reach (zbMATH refused the fetch); check them
before the bibliography is compiled, or drop them. Füredi &
West (2001), *Graphs and Combinatorics* 17(3), 463–471, doi:10.1007/PL00013410, is
optional (the name "halfgraph" and the sum `bw(G) + bw(Ḡ) ≤ 2n − 4 log₂ n + o(log n)`).

## 6. Files and regenerate

```bash
# the lemma (every graph n ≤ 6, random n = 7, 8), the block bound in rationals, the bandwidth form: ~15 min
nice -n 19 python -I reports/scratch/dense_staircase_refutation/own_check.py lemma     # lemma.log
# E[X] and the ratio identity against every labelled graph at n ≤ 6: ~2 min
nice -n 19 python -I reports/scratch/dense_staircase_refutation/own_check.py moment    # moment.log
# thresholds (ordered and symmetric counts), the exponent algebra, the bracket sums
nice -n 19 python -I reports/scratch/dense_staircase_refutation/own_numerics.py thresholds   # thresholds.log
nice -n 19 python -I reports/scratch/dense_staircase_refutation/own_numerics.py exponent     # exponent.log
nice -n 19 python -I reports/scratch/dense_staircase_refutation/own_numerics.py ratio        # ratio.log (n to 10^100, ~10 min; the 10^300 rows take hours), ratio_small_n.log
# Lean axiom audit from the built oleans
cd lean && taskset -c 0-3 lake env lean ../reports/scratch/dense_staircase/axioms.lean
```

Sources read: EHW 1989 at `static.renyi.hu/~p_erdos/1989-05.pdf` (pp. 117, 125–129);
Turner 1986 at `reports/scratch/first_moment/lit/turner1986.pdf` (§2, Theorem 2.1);
Crossref record of McDiarmid & Miller 1991 (`doi:10.1016/0166-218X(91)90046-Y`) for the
K–M entry; Springer's listing of Füredi & West 2001.
